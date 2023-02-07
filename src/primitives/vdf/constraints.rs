use ark_ff::{One, PrimeField};
use ark_r1cs_std::{
    fields::fp::FpVar,
    prelude::{Boolean, FieldVar},
    ToBitsGadget,
};
use ark_relations::r1cs::SynthesisError;
use num::BigUint;

use crate::primitives::{
    bn::{BigUintVar, BitsVar},
    poseidon::{
        config::WIDTH,
        constraints::{CRHGadget, HPrimeGadget},
        HPrime, PoseidonParameters,
    },
};

pub struct VDFGadget<const T: usize, const B: usize> {}

impl<const T: usize, const B: usize> VDFGadget<T, B> {
    fn h_prime<F: PrimeField, const W: usize>(
        pp: &PoseidonParameters<F>,
        bits: &[Boolean<F>],
        alpha: &[Vec<Boolean<F>>],
    ) -> Result<Vec<Boolean<F>>, SynthesisError> {
        let mut field_elements = bits
            .chunks(F::MODULUS_BIT_SIZE as usize - 1)
            .map(Boolean::le_bits_to_fp_var)
            .collect::<Result<Vec<_>, _>>()?;
        while field_elements.len() > 1 {
            field_elements = field_elements
                .chunks(WIDTH - 1)
                .map(|chunk| CRHGadget::hash_vec(pp, chunk.to_vec()))
                .collect::<Result<Vec<_>, _>>()?;
        }
        HPrimeGadget::to_prime::<F, W>(field_elements.pop().unwrap(), alpha)
    }

    pub fn verify<F: PrimeField, const W: usize>(
        pp: &PoseidonParameters<F>,
        n: &BigUintVar<F, W>,
        x: BigUintVar<F, W>,
        y: BigUintVar<F, W>,
        alpha: &[Vec<Boolean<F>>],
        pi: BigUintVar<F, W>,
    ) -> Result<(), SynthesisError> {
        let l = Self::h_prime::<F, W>(pp, &[x.to_bits_le()?, y.to_bits_le()?].concat(), alpha)?;
        let r = BigUintVar::<F, W>::constant(BigUint::from(B), HPrime::OUTPUT_WIDTH)?.powm(
            &FpVar::constant(F::from(T as u64)).to_bits_le()?,
            &BigUintVar(l.chunks(W).map(BitsVar::from).collect()),
            &(BigUint::one() << (HPrime::OUTPUT_WIDTH - 1)),
        )?;
        y.enforce_congruent_const(
            &x.powm_const(&r.to_bits_le()?, n)?
                .mul_no_carry(&pi.powm_const(&l, n)?)?,
            n,
        )?;
        y.enforce_lt(&n)?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use std::{error::Error, time::Instant};

    use crate::primitives::vdf::VDF;

    use super::*;
    use ark_bls12_381::{Bls12_381, Fr};
    use ark_groth16::{
        create_random_proof, generate_random_parameters, prepare_verifying_key, verify_proof,
    };
    use ark_r1cs_std::prelude::AllocVar;
    use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystem, ConstraintSystemRef};
    use num::bigint::RandBigInt;
    use rand::thread_rng;

    const W: usize = 32;
    const N: usize = 2048;

    #[test]
    fn test_vdf() {
        let cs = ConstraintSystem::<Fr>::new_ref();

        let pp = PoseidonParameters::<Fr>::default();
        let rng = &mut thread_rng();
        let vdf = VDF::<100001>::new(rng, N);
        let x = rng.gen_biguint_below(&vdf.n);
        let (y, alpha, pi) = vdf.eval(&pp, x.clone());

        assert!(vdf.verify(&pp, x.clone(), y.clone(), alpha.clone(), pi.clone()));

        let x = BigUintVar::<Fr, W>::new_witness(cs.clone(), || Ok((x, N))).unwrap();
        let y = BigUintVar::<Fr, W>::new_witness(cs.clone(), || Ok((y, N))).unwrap();
        let alpha = alpha
            .into_iter()
            .map(|a| Vec::<Boolean<Fr>>::new_witness(cs.clone(), || Ok(a)).unwrap())
            .collect::<Vec<_>>();
        let pi = BigUintVar::<Fr, W>::new_witness(cs.clone(), || Ok((pi, N))).unwrap();
        let n = BigUintVar::<Fr, W>::constant(vdf.n, N).unwrap();

        VDFGadget::<100001, 2>::verify(&pp, &n, x, y, &alpha, pi).unwrap();
        println!("{}", cs.num_constraints());
        assert!(cs.is_satisfied().unwrap());
    }

    struct TestCircuit<const T: usize, const B: usize> {
        pp: PoseidonParameters<Fr>,
        x: BigUint,
        y: BigUint,
        alpha: Vec<Vec<bool>>,
        pi: BigUint,
        n: BigUint,
    }

    impl<const T: usize, const B: usize> ConstraintSynthesizer<Fr> for TestCircuit<T, B> {
        fn generate_constraints(
            self,
            cs: ConstraintSystemRef<Fr>,
        ) -> ark_relations::r1cs::Result<()> {
            let x = BigUintVar::<Fr, W>::new_witness(cs.clone(), || Ok((self.x, N)))?;
            let y = BigUintVar::<Fr, W>::new_witness(cs.clone(), || Ok((self.y, N)))?;
            let alpha = self
                .alpha
                .into_iter()
                .map(|a| Vec::<Boolean<Fr>>::new_witness(cs.clone(), || Ok(a)))
                .collect::<Result<Vec<_>, _>>()?;
            let pi = BigUintVar::<Fr, W>::new_witness(cs.clone(), || Ok((self.pi, N)))?;
            let n = BigUintVar::<Fr, W>::constant(self.n, N)?;

            VDFGadget::<T, B>::verify(&self.pp, &n, x, y, &alpha, pi)?;
            Ok(())
        }
    }

    #[test]
    fn test() -> Result<(), Box<dyn Error>> {
        const T: usize = 1 << 22;

        let pp = PoseidonParameters::<Fr>::default();
        let rng = &mut thread_rng();
        let vdf = VDF::<T>::new(rng, N);
        let x = rng.gen_biguint_below(&vdf.n);
        let (y, alpha, pi) = vdf.eval(&pp, x.clone());

        let now = Instant::now();
        let params = generate_random_parameters::<Bls12_381, _, _>(
            TestCircuit::<{ T / 4 }, 16> {
                pp: pp.clone(),
                x: Default::default(),
                y: Default::default(),
                alpha: alpha.clone(),
                pi: Default::default(),
                n: vdf.n.clone(),
            },
            rng,
        )
        .unwrap();
        println!("setup time: {:?}", now.elapsed());

        let pvk = prepare_verifying_key(&params.vk);
        let now = Instant::now();
        let proof = create_random_proof(
            TestCircuit::<{ T / 4 }, 16> {
                pp,
                x,
                y,
                alpha,
                pi,
                n: vdf.n,
            },
            &params,
            rng,
        )
        .unwrap();
        println!("proof time: {:?}", now.elapsed());

        assert!(verify_proof(&pvk, &proof, &[]).unwrap());
        Ok(())
    }
}
