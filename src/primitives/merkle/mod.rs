use ark_ff::PrimeField;
use ark_std::vec::Vec;

use super::poseidon::{PoseidonParameters, CRH};

pub mod constraints;

pub struct MerklePath<F: PrimeField> {
    pub auth_path: Vec<F>,
    pub leaf_index: usize,
}

impl<F: PrimeField> MerklePath<F> {
    pub fn verify(&self, pp: &PoseidonParameters<F>, root: F, leaf: F) -> bool {
        let mut index = self.leaf_index;
        let mut curr = CRH::hash(
            &pp,
            leaf,
            Default::default(),
            Default::default(),
            Default::default(),
        );

        for &node in &self.auth_path {
            curr = if index & 1 == 0 {
                CRH::hash(&pp, curr, node, Default::default(), Default::default())
            } else {
                CRH::hash(&pp, node, curr, Default::default(), Default::default())
            };
            index >>= 1;
        }

        curr == root
    }
}

pub struct MerkleTree<F: PrimeField> {
    levels: Vec<Vec<F>>,
}

impl<F: PrimeField> MerkleTree<F> {
    pub fn new(pp: &PoseidonParameters<F>, leaves: &[F]) -> Self {
        Self::new_with_leaf_digest(
            pp,
            leaves
                .iter()
                .map(|&leaf| {
                    CRH::hash(
                        pp,
                        leaf,
                        Default::default(),
                        Default::default(),
                        Default::default(),
                    )
                })
                .collect(),
        )
    }

    pub fn new_with_leaf_digest(pp: &PoseidonParameters<F>, leaves_digest: Vec<F>) -> Self {
        let mut non_leaf_nodes = vec![leaves_digest];

        loop {
            non_leaf_nodes.push(
                non_leaf_nodes
                    .last()
                    .unwrap()
                    .chunks(2)
                    .map(|c| CRH::hash(pp, c[0], c[1], Default::default(), Default::default()))
                    .collect::<Vec<_>>(),
            );
            if non_leaf_nodes.last().unwrap().len() == 1 {
                break;
            }
        }

        non_leaf_nodes.reverse();

        MerkleTree {
            levels: non_leaf_nodes,
        }
    }

    pub fn root(&self) -> F {
        self.levels[0][0]
    }

    pub fn generate_proof(&self, index: usize) -> MerklePath<F> {
        let mut j = index;
        MerklePath {
            leaf_index: index,
            auth_path: self
                .levels
                .iter()
                .skip(1)
                .rev()
                .map(|level| {
                    let sibling_index = if j & 1 == 0 { j + 1 } else { j - 1 };
                    j >>= 1;
                    level[sibling_index]
                })
                .collect(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_ed_on_bls12_381::Fq;

    fn merkle_tree_test(leaves: &[Fq]) -> () {
        let pp = PoseidonParameters::<Fq>::default();
        let tree = MerkleTree::new(&pp, leaves);
        let root = tree.root();
        for (i, &leaf) in leaves.iter().enumerate() {
            let proof = tree.generate_proof(i);
            assert!(proof.verify(&pp, root, leaf));
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
