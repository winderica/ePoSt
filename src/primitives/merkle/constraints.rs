use ark_ff::PrimeField;
use ark_r1cs_std::boolean::Boolean;
use ark_r1cs_std::fields::fp::FpVar;
use ark_r1cs_std::prelude::{EqGadget, FieldVar};
use ark_relations::r1cs::SynthesisError;
use ark_std::vec::Vec;

use crate::primitives::poseidon::constraints::CRHGadget;
use crate::primitives::poseidon::PoseidonParameters;

pub struct MerkleTreeGadget;

impl MerkleTreeGadget {
    pub fn calculate_root<F: PrimeField>(
        pp: &PoseidonParameters<F>,
        leaf: FpVar<F>,
        siblings: Vec<FpVar<F>>,
        positions: Vec<Boolean<F>>,
    ) -> Result<FpVar<F>, SynthesisError> {
        let mut curr_hash = CRHGadget::hash(pp, leaf, FpVar::zero(), FpVar::zero(), FpVar::zero())?;

        for (bit, sibling) in positions.iter().zip(siblings.iter()) {
            let t = sibling + &curr_hash;
            let l = bit.select(sibling, &curr_hash)?;
            let r = t - &l;

            curr_hash = CRHGadget::hash(pp, l, r, FpVar::zero(), FpVar::zero())?;
        }

        Ok(curr_hash)
    }

    pub fn verify<F: PrimeField>(
        pp: &PoseidonParameters<F>,
        root: &FpVar<F>,
        leaf: FpVar<F>,
        siblings: Vec<FpVar<F>>,
        positions: Vec<Boolean<F>>,
    ) -> Result<(), SynthesisError> {
        Self::calculate_root(pp, leaf, siblings, positions)?.enforce_equal(root)
    }
}

#[cfg(test)]
mod tests {
    use crate::primitives::merkle::MerkleTree;

    use super::*;
    use ark_ed_on_bls12_381::Fq;
    use ark_r1cs_std::prelude::AllocVar;
    use ark_relations::r1cs::ConstraintSystem;

    fn merkle_tree_test(leaves: &[Fq]) -> () {
        let cs = ConstraintSystem::<Fq>::new_ref();
        let pp = PoseidonParameters::<Fq>::default();
        let tree = MerkleTree::new(&pp, leaves);
        let root = tree.root();
        // test merkle tree functionality without update
        for (i, &leaf) in leaves.iter().enumerate() {
            let proof = tree.generate_proof(i);
            assert!(proof.verify(&pp, root, leaf));

            let root = FpVar::new_witness(cs.clone(), || Ok(root)).unwrap();
            let leaf = FpVar::new_witness(cs.clone(), || Ok(leaf)).unwrap();
            let siblings = Vec::new_witness(cs.clone(), || Ok(proof.auth_path)).unwrap();
            let positions = Vec::new_witness(cs.clone(), || {
                Ok((0..siblings.len())
                    .map(|i| ((proof.leaf_index >> i) & 1) != 0)
                    .collect::<Vec<_>>())
            })
            .unwrap();
            assert!(MerkleTreeGadget::verify(&pp, &root, leaf, siblings, positions).is_ok());
            println!("{}", cs.num_constraints());
            assert!(cs.is_satisfied().unwrap());
        }
    }

    #[test]
    fn test_merkle_tree() {
        let leaves = vec![
            Fq::from(1u64),
            Fq::from(2u64),
            Fq::from(3u64),
            Fq::from(4u64),
            Fq::from(5u64),
            Fq::from(6u64),
            Fq::from(7u64),
            Fq::from(8u64),
        ];
        merkle_tree_test(&leaves);
    }
}
