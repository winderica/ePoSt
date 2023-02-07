use ark_ec::AffineRepr;
use ark_ff::PrimeField;
use rand::Rng;
use rayon::prelude::{IndexedParallelIterator, IntoParallelRefIterator, ParallelIterator};

use super::{
    poseidon::{config::WIDTH, PoseidonParameters, CRH},
    schnorr::Schnorr,
};

pub mod constraints;

pub struct PDP {}

impl PDP {
    pub fn key_gen<C: AffineRepr, R: Rng>(rng: &mut R) -> (C::ScalarField, C) {
        Schnorr::key_gen(rng)
    }

    pub fn tag_gen<C: AffineRepr, R: Rng>(
        pp: &PoseidonParameters<C::BaseField>,
        sk: C::ScalarField,
        v: C::BaseField,
        blocks: &[Vec<C::BaseField>],
        rng: fn() -> R,
    ) -> Vec<(C::ScalarField, C::ScalarField)>
    where
        C::BaseField: PrimeField,
    {
        blocks
            .par_iter()
            .enumerate()
            .map_init(rng, |rng, (i, block)| {
                let mut field_elements = block.clone();
                while field_elements.len() > 1 {
                    field_elements = field_elements
                        .chunks(WIDTH - 1)
                        .map(|chunk| CRH::hash_vec(pp, &chunk))
                        .collect::<Vec<_>>();
                }
                let h = CRH::hash(
                    pp,
                    field_elements[0],
                    v,
                    C::BaseField::from(i as u64),
                    Default::default(),
                );
                Schnorr::sign::<C, _, _, _>(pp, sk, h, rng)
            })
            .collect()
    }

    pub fn prove<C: AffineRepr>(
        blocks: &[Vec<C::BaseField>],
        tags: &[(C::ScalarField, C::ScalarField)],
        c: usize,
    ) -> (Vec<C::BaseField>, (C::ScalarField, C::ScalarField)) {
        (blocks[c].clone(), tags[c].clone())
    }

    pub fn verify<C: AffineRepr>(
        pp: &PoseidonParameters<C::BaseField>,
        pk: &C,
        v: C::BaseField,
        c: usize,
        block: Vec<C::BaseField>,
        proof: (C::ScalarField, C::ScalarField),
    ) -> bool
    where
        C::BaseField: PrimeField,
    {
        let mut field_elements = block;
        while field_elements.len() > 1 {
            field_elements = field_elements
                .chunks(WIDTH - 1)
                .map(|chunk| CRH::hash_vec(pp, &chunk))
                .collect::<Vec<_>>();
        }
        let h = CRH::hash(
            pp,
            field_elements[0],
            v,
            C::BaseField::from(c as u64),
            Default::default(),
        );
        Schnorr::verify(pp, pk, h, proof)
    }
}

#[cfg(test)]
mod tests {
    use std::time::Instant;

    use super::*;
    use ark_ed_on_bls12_381::{EdwardsAffine, Fq};
    use ark_ff::UniformRand;
    use rand::thread_rng;

    const NUM_BLOCKS: usize = 1 * 1024 * 1024 * 8 / BLOCK_SIZE;
    const BLOCK_SIZE: usize = 2048;

    #[test]
    fn test() {
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
        assert!(PDP::verify(&pp, &pk, v, c, block, proof));
        println!("verify: {:.3?}", now.elapsed());
    }
}
