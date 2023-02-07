use ark_ec::twisted_edwards::TECurveConfig;
use ark_ff::{One, PrimeField};
use ark_r1cs_std::{
    fields::fp::FpVar,
    groups::curves::twisted_edwards::AffineVar,
    prelude::{Boolean, FieldVar},
    ToBitsGadget,
};
use ark_relations::r1cs::SynthesisError;
use num::BigUint;

use crate::primitives::{
    bn::{BigUintVar, BitsVar},
    poseidon::{config::WIDTH, constraints::CRHGadget, PoseidonParameters},
    schnorr::constraints::SchnorrGadget,
};

pub struct PDPGadget {}

impl PDPGadget {
    pub fn verify<const W: usize, Cfg, Fq: PrimeField>(
        pp: &PoseidonParameters<Fq>,
        pk: AffineVar<Cfg, FpVar<Fq>>,
        v: FpVar<Fq>,
        c: &FpVar<Fq>,
        num_blocks: BigUintVar<Fq, W>,
        block: Vec<FpVar<Fq>>,
        proof: (Vec<Boolean<Fq>>, Vec<Boolean<Fq>>),
    ) -> Result<(), SynthesisError>
    where
        Cfg: TECurveConfig<BaseField = Fq>,
    {
        let mut field_elements = block;
        while field_elements.len() > 1 {
            field_elements = field_elements
                .chunks(WIDTH - 1)
                .map(|chunk| CRHGadget::hash_vec(pp, chunk.to_vec()))
                .collect::<Result<Vec<_>, _>>()?;
        }
        let i = BigUintVar(c.to_bits_le()?.chunks(W).map(BitsVar::from).collect())
            .rem(&num_blocks, &BigUint::one())?;
        i.enforce_lt(&num_blocks)?;
        let i = Boolean::le_bits_to_fp_var(&i.to_bits_le()?)?;
        let h = CRHGadget::hash(pp, field_elements.pop().unwrap(), v, i, FpVar::zero())?;
        SchnorrGadget::verify::<W, _, _, _>(pp, pk, h, proof)
    }
}

#[cfg(test)]
mod tests {
    use std::time::Instant;

    use crate::primitives::pdp::PDP;

    use super::*;
    use ark_ed_on_bls12_381::{EdwardsAffine, Fq};
    use ark_ff::{BigInteger, UniformRand};
    use ark_r1cs_std::prelude::AllocVar;
    use ark_relations::r1cs::ConstraintSystem;
    use rand::{thread_rng, Rng};

    const NUM_BLOCKS: usize = 10;
    const BLOCK_SIZE: usize = 2048;
    const W: usize = 32;

    #[test]
    fn test() {
        let cs = ConstraintSystem::<Fq>::new_ref();

        let rng = &mut thread_rng();
        let pp = PoseidonParameters::<Fq>::default();
        let v = Fq::rand(rng);
        let now = Instant::now();
        let (sk, pk) = PDP::key_gen::<EdwardsAffine, _>(rng);
        println!("key_gen: {:.3?}", now.elapsed());
        let blocks = (0..NUM_BLOCKS)
            .into_iter()
            .map(|_| {
                (0..BLOCK_SIZE / (Fq::MODULUS_BIT_SIZE as usize))
                    .map(|_| Fq::rand(rng))
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        let now = Instant::now();
        let tags = PDP::tag_gen::<EdwardsAffine, _>(&pp, sk, v, &blocks, || thread_rng());
        println!("tag_gen: {:.3?}", now.elapsed());
        let c = rng.gen_range(0..NUM_BLOCKS);
        let now = Instant::now();
        let (block, proof) = PDP::prove::<EdwardsAffine>(&blocks, &tags, c);
        println!("prove: {:.3?}", now.elapsed());
        let now = Instant::now();
        assert!(PDP::verify(&pp, &pk, v, c, block.clone(), proof));
        println!("verify: {:.3?}", now.elapsed());

        let pk = AffineVar::new_witness(cs.clone(), || Ok(pk)).unwrap();
        let v = FpVar::new_witness(cs.clone(), || Ok(v)).unwrap();
        let c = FpVar::new_witness(cs.clone(), || Ok(Fq::from(c as u64))).unwrap();
        let num_blocks =
            BigUintVar::<_, W>::new_input(cs.clone(), || Ok((BigUint::from(NUM_BLOCKS), 64)))
                .unwrap();
        let block = Vec::new_witness(cs.clone(), || Ok(block)).unwrap();
        let proof = (
            Vec::new_witness(cs.clone(), || Ok(proof.0.into_bigint().to_bits_le())).unwrap(),
            Vec::new_witness(cs.clone(), || Ok(proof.1.into_bigint().to_bits_le())).unwrap(),
        );
        PDPGadget::verify(&pp, pk, v, &c, num_blocks, block, proof).unwrap();

        println!("{}", cs.num_constraints());
        assert!(cs.is_satisfied().unwrap());
    }
}
