use ark_ec::{twisted_edwards::TECurveConfig, AffineRepr};
use ark_ff::PrimeField;
use ark_r1cs_std::{
    fields::fp::FpVar,
    groups::curves::twisted_edwards::AffineVar,
    prelude::{Boolean, CurveVar, EqGadget, FieldVar},
    ToBitsGadget,
};
use ark_relations::r1cs::SynthesisError;

use crate::primitives::{
    bn::{BigUintVar, BitsVar},
    poseidon::{constraints::CRHGadget, PoseidonParameters},
};

pub struct SchnorrGadget {}

impl SchnorrGadget {
    pub fn verify<const W: usize, Cfg, Fr: PrimeField, Fq: PrimeField>(
        pp: &PoseidonParameters<Fq>,
        pk: AffineVar<Cfg, FpVar<Fq>>,
        m: FpVar<Fq>,
        (s, e): (Vec<Boolean<Fq>>, Vec<Boolean<Fq>>),
    ) -> Result<(), SynthesisError>
    where
        Cfg: TECurveConfig<ScalarField = Fr, BaseField = Fq>,
    {
        let g = AffineVar::constant(Cfg::GENERATOR.into_group());
        let r = g.scalar_mul_le(s.iter())? + pk.scalar_mul_le(e.iter())?;

        let h = CRHGadget::hash(pp, r.x, r.y, m, FpVar::zero())?;
        let mut h_bits = h.to_bits_le()?;
        h_bits.truncate(Fr::MODULUS_BIT_SIZE as usize);

        BigUintVar::<Fq, W>(h_bits.chunks(W).map(BitsVar::from).collect()).enforce_lt(
            &BigUintVar::constant(Fr::MODULUS.into(), Fr::MODULUS_BIT_SIZE as usize)?,
        )?;

        Boolean::le_bits_to_fp_var(&h_bits)?.enforce_equal(&Boolean::le_bits_to_fp_var(&e)?)?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use std::time::Instant;

    use crate::primitives::schnorr::Schnorr;

    use super::*;
    use ark_bls12_381::Bls12_381;
    use ark_ed_on_bls12_381::{EdwardsAffine, Fq, Fr};
    use ark_ff::{BigInteger, UniformRand};
    use ark_groth16::{
        create_random_proof, generate_random_parameters, prepare_verifying_key, verify_proof,
    };
    use ark_r1cs_std::prelude::AllocVar;
    use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystem, ConstraintSystemRef};
    use rand::thread_rng;

    const W: usize = 32;

    #[test]
    fn test() {
        let cs = ConstraintSystem::<Fq>::new_ref();

        let rng = &mut thread_rng();
        let pp = PoseidonParameters::<Fq>::default();
        let (sk, pk) = Schnorr::key_gen::<EdwardsAffine, _>(rng);
        let m = Fq::rand(rng);
        let (s, e) = Schnorr::sign::<EdwardsAffine, _, _, _>(&pp, sk, m, rng);
        assert!(Schnorr::verify(&pp, &pk, m, (s, e)));

        let pk = AffineVar::new_witness(cs.clone(), || Ok(pk)).unwrap();
        let m = FpVar::new_witness(cs.clone(), || Ok(m)).unwrap();
        let s = Vec::new_witness(cs.clone(), || Ok(s.into_bigint().to_bits_le())).unwrap();
        let e = Vec::new_witness(cs.clone(), || Ok(e.into_bigint().to_bits_le())).unwrap();
        SchnorrGadget::verify::<W, _, _, _>(&pp, pk, m, (s, e)).unwrap();

        println!("{}", cs.num_constraints());
        assert!(cs.is_satisfied().unwrap());
    }

    struct TestCircuit {
        pp: PoseidonParameters<Fq>,
        pk: EdwardsAffine,
        m: Fq,
        s: Fr,
        e: Fr,
    }

    impl ConstraintSynthesizer<Fq> for TestCircuit {
        fn generate_constraints(
            self,
            cs: ConstraintSystemRef<Fq>,
        ) -> ark_relations::r1cs::Result<()> {
            let pk = AffineVar::new_witness(cs.clone(), || Ok(self.pk))?;
            let m = FpVar::new_witness(cs.clone(), || Ok(self.m))?;
            let s = Vec::new_witness(cs.clone(), || Ok(self.s.into_bigint().to_bits_le()))?;
            let e = Vec::new_witness(cs.clone(), || Ok(self.e.into_bigint().to_bits_le()))?;
            SchnorrGadget::verify::<W, _, _, _>(&self.pp, pk, m, (s, e)).unwrap();

            Ok(())
        }
    }

    #[test]
    fn test_circuit() {
        let rng = &mut thread_rng();
        let pp = PoseidonParameters::<Fq>::default();
        let (sk, pk) = Schnorr::key_gen::<EdwardsAffine, _>(rng);
        let m = Fq::rand(rng);
        let (s, e) = Schnorr::sign::<EdwardsAffine, _, _, _>(&pp, sk, m, rng);

        let now = Instant::now();
        let params = generate_random_parameters::<Bls12_381, _, _>(
            TestCircuit {
                pp: pp.clone(),
                pk: Default::default(),
                m: Default::default(),
                s: Default::default(),
                e: Default::default(),
            },
            rng,
        )
        .unwrap();
        println!("setup time: {:?}", now.elapsed());

        let pvk = prepare_verifying_key(&params.vk);
        let now = Instant::now();
        let proof = create_random_proof(
            TestCircuit {
                pp: pp.clone(),
                pk,
                m,
                s,
                e,
            },
            &params,
            rng,
        )
        .unwrap();
        println!("proof time: {:?}", now.elapsed());

        assert!(verify_proof(&pvk, &proof, &[]).unwrap());
    }
}
