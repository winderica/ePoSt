use std::marker::PhantomData;

use ark_bls12_381::Bls12_381;
use ark_ed_on_bls12_381::{EdwardsAffine, Fq, Fr, JubjubConfig};
use ark_ff::{BigInteger, PrimeField, UniformRand};
use ark_groth16::{create_random_proof, generate_random_parameters, ProvingKey};
use ark_r1cs_std::{
    eq::EqGadget,
    fields::{fp::FpVar, FieldVar},
    groups::curves::twisted_edwards::AffineVar,
    prelude::{AllocVar, Boolean},
    ToBitsGadget,
};
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
use blake2::Blake2b512;
use groth16_aggregation::{
    aggregate_proofs, setup_inner_product, tipa::SRS, verify_aggregate_proof, AggregateProof,
};
use num::{BigUint, ToPrimitive};
use primitives::{
    bn::{BigUintVar, BitsVar},
    merkle::{constraints::MerkleTreeGadget, MerklePath, MerkleTree},
    pdp::{constraints::PDPGadget, PDP},
    poseidon::{config::WIDTH, constraints::CRHGadget, HPrime, PoseidonParameters, CRH},
    vdf::{constraints::VDFGadget, VDF},
};
use rand::{thread_rng, Rng};

pub mod groth16_aggregation;
pub mod primitives;

pub struct PoST<
    const W: usize,
    const T: usize,
    const B: usize,
    const BLOCK_SIZE: usize,
    const BATCH_SIZE: usize,
    const N_SIZE: usize,
> {
    h: PoseidonParameters<Fq>,
    vdf: VDF<T>,
    groth16_srs: ProvingKey<Bls12_381>,
    ip_srs: SRS<Bls12_381>,
    __: PhantomData<(EdwardsAffine, Fr)>,
}

impl<
        const W: usize,
        const T: usize,
        const B: usize,
        const BLOCK_SIZE: usize,
        const BATCH_SIZE: usize,
        const N_SIZE: usize,
    > PoST<W, T, B, BLOCK_SIZE, BATCH_SIZE, N_SIZE>
{
    pub fn new<R: Rng>(rng: &mut R) -> Self {
        let h = PoseidonParameters::<Fq>::default();
        let vdf = VDF::<T>::new(rng, N_SIZE);
        let groth16_srs = generate_random_parameters::<Bls12_381, _, _>(
            PoSTRoundCircuit::<W, T, B, BLOCK_SIZE, N_SIZE> {
                h: &h,
                vdf: &vdf,
                pk: Default::default(),
                i: Default::default(),
                c_old: Default::default(),
                c_new: Default::default(),
                v: Default::default(),
                num_blocks: Default::default(),
                block: vec![Default::default(); BLOCK_SIZE / (Fq::MODULUS_BIT_SIZE as usize)],
                pi_pdp: Default::default(),
                y: Default::default(),
                alpha: HPrime::EXTENSIONS
                    .iter()
                    .map(|(n, _, _)| vec![false; *n])
                    .collect(),
                pi_vdf: Default::default(),
                root: Default::default(),
                pi_merkle_old: MerklePath {
                    auth_path: vec![Default::default(); BATCH_SIZE.ilog2() as usize],
                    leaf_index: Default::default(),
                },
                pi_merkle_new: MerklePath {
                    auth_path: vec![Default::default(); BATCH_SIZE.ilog2() as usize],
                    leaf_index: Default::default(),
                },
            },
            rng,
        )
        .unwrap();
        let ip_srs = setup_inner_product::<_, Blake2b512, _>(rng, BATCH_SIZE).unwrap();
        Self {
            h,
            vdf,
            groth16_srs,
            ip_srs,
            __: PhantomData,
        }
    }

    pub fn key_gen<R: Rng>(&self, rng: &mut R) -> (Fr, EdwardsAffine) {
        PDP::key_gen::<EdwardsAffine, _>(rng)
    }

    pub fn store<R: Rng>(&self, sk: Fr, blocks: &[Vec<Fq>], rng: &mut R) -> (Fq, Vec<(Fr, Fr)>) {
        let v = Fq::rand(rng);
        (
            v,
            PDP::tag_gen::<EdwardsAffine, _>(&self.h, sk, v, blocks, || thread_rng()),
        )
    }

    pub fn challenge<R: Rng>(&self, rng: &mut R) -> Fq {
        Fq::rand(rng)
    }

    fn prove_round(
        &self,
        blocks: &[Vec<Fq>],
        tags: &[(Fr, Fr)],
        c_old: Fq,
    ) -> ((Fr, Fr), BigUint, Vec<Vec<bool>>, BigUint, Fq) {
        let c_old: BigUint = c_old.into();
        let c_old = c_old % blocks.len();

        let (_, pi_pdp) = PDP::prove::<EdwardsAffine>(blocks, tags, c_old.to_usize().unwrap());

        let x = CRH::hash(
            &self.h,
            Fq::from(Into::<BigUint>::into(pi_pdp.0)),
            Fq::from(Into::<BigUint>::into(pi_pdp.1)),
            Default::default(),
            Default::default(),
        );
        let (y, alpha, pi_vdf) = self.vdf.eval_optimized(&self.h, x.into());

        let c_new = {
            let mut field_elements = [
                y.to_radix_le(2),
                vec![0; self.vdf.n_bits - y.bits() as usize],
            ]
            .concat()
            .chunks(Fq::MODULUS_BIT_SIZE as usize - 1)
            .map(|i| BigUint::from_radix_le(i, 2).map(Fq::from))
            .collect::<Option<Vec<_>>>()
            .unwrap();
            while field_elements.len() > 1 {
                field_elements = field_elements
                    .chunks(WIDTH - 1)
                    .map(|chunk| CRH::hash_vec(&self.h, chunk))
                    .collect();
            }
            field_elements.pop().unwrap()
        };

        (pi_pdp, y, alpha, pi_vdf, c_new)
    }

    pub fn prove<R: Rng>(
        &self,
        pk: EdwardsAffine,
        v: Fq,
        mut c: Fq,
        blocks: &[Vec<Fq>],
        tags: &[(Fr, Fr)],
        num_batches: usize,
        rng: &mut R,
    ) -> (
        Vec<Fq>,
        Vec<Fq>,
        Vec<MerklePath<Fq>>,
        Vec<AggregateProof<Bls12_381>>,
    ) {
        let mut roots = vec![];
        let mut proofs = vec![];
        let mut paths = vec![];
        let mut challenges = vec![];
        for _ in 0..num_batches {
            challenges.push(c);
            let mut leaves = vec![];
            let mut r = vec![];
            for _ in 0..BATCH_SIZE - 1 {
                leaves.push(c);
                let (pi_pdp, y, alpha, pi_vdf, c_new) = self.prove_round(blocks, tags, c);
                c = c_new;
                r.push((pi_pdp, y, alpha, pi_vdf));
            }
            leaves.push(c);
            let mt = MerkleTree::new(&self.h, &leaves);
            let root = mt.root();
            roots.push(root);
            paths.push(mt.generate_proof(0));

            let aggregate_proof = {
                let mut proofs = r
                    .into_iter()
                    .enumerate()
                    .zip(leaves.windows(2))
                    .map(|((i, (pi_pdp, y, alpha, pi_vdf)), c)| {
                        let c_old = c[0];
                        let c_new = c[1];
                        let block = {
                            let c_old: BigUint = c_old.into();
                            let c_old = c_old % blocks.len();
                            blocks[c_old.to_usize().unwrap()].clone()
                        };
                        let pi_merkle_old = mt.generate_proof(i);
                        let pi_merkle_new = mt.generate_proof(i + 1);
                        create_random_proof(
                            PoSTRoundCircuit::<W, T, B, BLOCK_SIZE, N_SIZE> {
                                h: &self.h,
                                vdf: &self.vdf,
                                pk,
                                i,
                                c_old,
                                c_new,
                                v,
                                num_blocks: blocks.len(),
                                block,
                                pi_pdp,
                                y,
                                alpha,
                                pi_vdf,
                                root,
                                pi_merkle_old,
                                pi_merkle_new,
                            },
                            &self.groth16_srs,
                            rng,
                        )
                        .unwrap()
                    })
                    .collect::<Vec<_>>();
                proofs.push(proofs.last().unwrap().clone());
                aggregate_proofs::<Bls12_381, Blake2b512>(&self.ip_srs, &proofs).unwrap()
            };

            proofs.push(aggregate_proof);
        }

        (roots, challenges, paths, proofs)
    }

    pub fn verify(
        &self,
        pk: EdwardsAffine,
        v: Fq,
        c0: Fq,
        roots: &[Fq],
        challenges: &[Fq],
        paths: &[MerklePath<Fq>],
        proofs: &[AggregateProof<Bls12_381>],
        num_blocks: usize,
    ) -> bool {
        if c0 != challenges[0] {
            return false;
        }
        if !roots
            .iter()
            .zip(challenges)
            .zip(paths)
            .all(|((root, c), path)| path.verify(&self.h, *root, *c))
        {
            return false;
        }
        proofs.iter().zip(roots).all(|(proof, &root)| {
            let mut statements = (0..BATCH_SIZE - 1)
                .map(|i| {
                    [
                        vec![pk.x, pk.y, v, root],
                        BigUintVar::<_, W>::inputize(&num_blocks.into(), 64),
                        BigUintVar::<_, W>::inputize(&i.into(), BATCH_SIZE.ilog2() as usize),
                    ]
                    .concat()
                })
                .collect::<Vec<_>>();
            statements.push(statements.last().unwrap().clone());
            verify_aggregate_proof::<Bls12_381, Blake2b512>(
                &self.ip_srs.get_verifier_key(),
                &self.groth16_srs.vk,
                &statements,
                proof,
            )
            .unwrap()
        })
    }
}

struct PoSTRoundGadget {}

impl PoSTRoundGadget {
    pub fn verify<const W: usize, const T: usize, const B: usize, const N_SIZE: usize>(
        pp: &PoseidonParameters<Fq>,
        n: &BigUintVar<Fq, W>,
        pk: AffineVar<JubjubConfig, FpVar<Fq>>,
        mut i: BigUintVar<Fq, W>,
        c_old: FpVar<Fq>,
        c_new: FpVar<Fq>,
        v: FpVar<Fq>,
        num_blocks: BigUintVar<Fq, W>,
        block: Vec<FpVar<Fq>>,
        pi_pdp: (Vec<Boolean<Fq>>, Vec<Boolean<Fq>>),
        y: BigUintVar<Fq, W>,
        alpha: &[Vec<Boolean<Fq>>],
        pi_vdf: BigUintVar<Fq, W>,
        root: FpVar<Fq>,
        pi_merkle_old: Vec<FpVar<Fq>>,
        pi_merkle_new: Vec<FpVar<Fq>>,
    ) -> Result<(), SynthesisError> {
        let mut x_bits = CRHGadget::hash(
            pp,
            Boolean::le_bits_to_fp_var(&pi_pdp.0)?,
            Boolean::le_bits_to_fp_var(&pi_pdp.1)?,
            FpVar::zero(),
            FpVar::zero(),
        )?
        .to_bits_le()?;
        x_bits.resize(N_SIZE, Boolean::FALSE);
        let x = BigUintVar::<_, W>(x_bits.chunks(W).map(BitsVar::from).collect());

        let mut field_elements = y
            .to_bits_le()?
            .chunks(Fq::MODULUS_BIT_SIZE as usize - 1)
            .map(Boolean::le_bits_to_fp_var)
            .collect::<Result<Vec<_>, _>>()?;
        while field_elements.len() > 1 {
            field_elements = field_elements
                .chunks(WIDTH - 1)
                .map(|chunk| CRHGadget::hash_vec(pp, chunk.to_vec()))
                .collect::<Result<Vec<_>, _>>()?;
        }
        field_elements.pop().unwrap().enforce_equal(&c_new)?;

        PDPGadget::verify(pp, pk, v, &c_old, num_blocks, block, pi_pdp)?;
        VDFGadget::<T, B>::verify(pp, n, x, y, alpha, pi_vdf)?;

        MerkleTreeGadget::verify(pp, &root, c_old, pi_merkle_old, i.to_bits_le()?)?;
        i.0[0].0 += FpVar::one();
        MerkleTreeGadget::verify(pp, &root, c_new, pi_merkle_new, i.to_bits_le()?)?;

        Ok(())
    }
}

struct PoSTRoundCircuit<
    'a,
    const W: usize,
    const T: usize,
    const B: usize,
    const BATCH_SIZE: usize,
    const N_SIZE: usize,
> {
    h: &'a PoseidonParameters<Fq>,
    vdf: &'a VDF<T>,
    pk: EdwardsAffine,
    i: usize,
    c_old: Fq,
    c_new: Fq,
    v: Fq,
    num_blocks: usize,
    block: Vec<Fq>,
    pi_pdp: (Fr, Fr),
    y: BigUint,
    alpha: Vec<Vec<bool>>,
    pi_vdf: BigUint,
    root: Fq,
    pi_merkle_old: MerklePath<Fq>,
    pi_merkle_new: MerklePath<Fq>,
}

impl<
        'a,
        const W: usize,
        const T: usize,
        const B: usize,
        const BATCH_SIZE: usize,
        const N_SIZE: usize,
    > ConstraintSynthesizer<Fq> for PoSTRoundCircuit<'a, W, T, B, BATCH_SIZE, N_SIZE>
{
    fn generate_constraints(self, cs: ConstraintSystemRef<Fq>) -> Result<(), SynthesisError> {
        let n = BigUintVar::constant(self.vdf.n.clone(), self.vdf.n_bits)?;

        let pk = AffineVar::new_input(cs.clone(), || Ok(self.pk))?;
        let v = FpVar::new_input(cs.clone(), || Ok(self.v))?;
        let root = FpVar::new_input(cs.clone(), || Ok(self.root))?;
        let num_blocks = BigUintVar::new_input(cs.clone(), || Ok((self.num_blocks.into(), 64)))?;
        let i = BigUintVar::new_input(cs.clone(), || {
            Ok((self.i.into(), BATCH_SIZE.ilog2() as usize))
        })?;

        let c_old = FpVar::new_witness(cs.clone(), || Ok(self.c_old))?;
        let c_new = FpVar::new_witness(cs.clone(), || Ok(self.c_new))?;
        let block = Vec::new_witness(cs.clone(), || Ok(self.block))?;
        let pi_pdp = (
            Vec::new_witness(cs.clone(), || Ok(self.pi_pdp.0.into_bigint().to_bits_le())).unwrap(),
            Vec::new_witness(cs.clone(), || Ok(self.pi_pdp.1.into_bigint().to_bits_le())).unwrap(),
        );
        let y = BigUintVar::new_witness(cs.clone(), || Ok((self.y, self.vdf.n_bits)))?;
        let alpha = self
            .alpha
            .into_iter()
            .map(|a| Vec::<Boolean<Fq>>::new_witness(cs.clone(), || Ok(a)))
            .collect::<Result<Vec<_>, _>>()?;
        let pi_vdf = BigUintVar::new_witness(cs.clone(), || Ok((self.pi_vdf, self.vdf.n_bits)))?;
        let pi_merkle_old =
            Vec::new_witness(cs.clone(), || Ok(self.pi_merkle_old.auth_path)).unwrap();
        let pi_merkle_new = Vec::new_witness(cs, || Ok(self.pi_merkle_new.auth_path)).unwrap();

        PoSTRoundGadget::verify::<W, T, B, N_SIZE>(
            &self.h,
            &n,
            pk,
            i,
            c_old,
            c_new,
            v,
            num_blocks,
            block,
            pi_pdp,
            y,
            &alpha,
            pi_vdf,
            root,
            pi_merkle_old,
            pi_merkle_new,
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const W: usize = 32;
    const T: usize = 1 << 24;
    const B: usize = 2;
    const NUM_BLOCKS: usize = 10;
    const BLOCK_SIZE: usize = 2048;
    const BATCH_SIZE: usize = 2;
    const NUM_BATCHES: usize = 2;
    const N_SIZE: usize = 2048;

    #[test]
    fn test() {
        let rng = &mut thread_rng();
        let post = PoST::<W, T, B, BLOCK_SIZE, BATCH_SIZE, N_SIZE>::new(rng);
        let blocks = (0..NUM_BLOCKS)
            .into_iter()
            .map(|_| {
                (0..BLOCK_SIZE / (Fq::MODULUS_BIT_SIZE as usize))
                    .map(|_| Fq::rand(rng))
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        let (sk, pk) = post.key_gen(rng);
        let (v, tags) = post.store(sk, &blocks, rng);
        let c = post.challenge(rng);
        let (roots, challenges, paths, proofs) =
            post.prove(pk, v, c, &blocks, &tags, NUM_BATCHES, rng);
        assert!(post.verify(pk, v, c, &roots, &challenges, &paths, &proofs, NUM_BLOCKS));
    }
}
