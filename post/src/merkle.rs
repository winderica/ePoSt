use bellperson::{
    bls::{Bls12, Fr},
    Circuit, ConstraintSystem, LinearCombination, SynthesisError, Variable,
};

use crate::{poseidon::PoseidonCircuit, utils::{alloc, ZERO}};
use crate::{
    poseidon::{perm},
    utils::alloc_input,
};

pub fn merkelize(leaves: &[Fr]) -> Vec<Vec<Fr>> {
    let mut tree = vec![leaves.to_owned()];
    let height = 64 - leaves.len().leading_zeros() as usize - 1;
    for i in 0..height {
        tree.push(
            tree[i]
                .chunks(2)
                .map(|pair| perm(&[pair[0], pair[1], ZERO, ZERO, ZERO])[0])
                .collect(),
        )
    }
    tree.reverse();
    tree
}

pub struct MerkleCircuit {
    pub tree: Vec<Vec<Fr>>,
    pub index: usize,
}

impl MerkleCircuit {
    pub fn build_root<CS: ConstraintSystem<Bls12>>(
        cs: &mut CS,
        tree: &Vec<Vec<Fr>>,
        mut index: usize,
        leaf: &Fr,
        leaf_var: &Variable,
    ) -> (Fr, Variable) {
        let mut curr = *leaf;
        let mut curr_var = *leaf_var;
        for h in (1..tree.len()).rev() {
            let b = index & 1;
            let sibling = tree[h][index + 1 - b * 2];

            let (l, r) = if b == 0 { (curr, sibling) } else { (sibling, curr) };

            let sibling_var = alloc(cs, sibling);
            let l_var = alloc(cs, l);
            let r_var = alloc(cs, r);
            let b_var = alloc_input(cs, Fr::from(b as u64));

            cs.enforce(
                || "l = (1 - b) * curr + b * sibling",
                |lc| lc + b_var,
                |lc| lc + sibling_var - curr_var,
                |lc| lc + l_var - curr_var,
            );
            cs.enforce(
                || "r = b * curr + (1 - b) * sibling",
                |lc| lc + b_var,
                |lc| lc + curr_var - sibling_var,
                |lc| lc + r_var - sibling_var,
            );

            let state = [l, r, ZERO, ZERO, ZERO];
            let state_var = [l_var, r_var, alloc(cs, ZERO), alloc(cs, ZERO), alloc(cs, ZERO)];
            let (state, state_var) = PoseidonCircuit::perm(cs, &state, &state_var);
            curr = state[0];
            curr_var = state_var[0];

            index >>= 1;
        }
        (curr, curr_var)
    }
}

impl Circuit<Bls12> for MerkleCircuit {
    fn synthesize<CS: ConstraintSystem<Bls12>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
        let root = self.tree[0][0];
        let root_var = alloc_input(cs, root);

        let curr = self.tree.last().unwrap()[self.index];
        let curr_var = alloc(cs, curr);

        let (_, curr_var) = Self::build_root(cs, &self.tree, self.index, &curr, &curr_var);

        cs.enforce(|| "", |lc| lc + curr_var, |lc| lc + CS::one(), |lc| lc + root_var);

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use std::time::Instant;

    use bellperson::groth16::{create_random_proof, generate_random_parameters, prepare_verifying_key, verify_proof};
    use fff::{Field};
    use rand::{thread_rng, Rng};

    use super::*;

    #[test]
    fn test_merkelize_zk() {
        let rng = &mut thread_rng();

        for height in 1..=20 {
            println!("Height: {}", height);
            let leaves = vec![ZERO; 1 << height]
                .iter()
                .map(|_| Fr::random(rng))
                .collect::<Vec<_>>();

            let now = Instant::now();
            let tree = merkelize(&leaves);
            println!("merkelize: {:.3?}", now.elapsed());

            let root = tree[0][0];
            let index = rng.gen_range(0..1 << height);
            let index_scalar = (0..tree.len() - 1)
                .map(|h| Fr::from(((index >> h) & 1) as u64))
                .collect();

            let now = Instant::now();
            let params = generate_random_parameters(
                MerkleCircuit {
                    tree: tree.iter().map(|i| vec![ZERO; i.len()]).collect(),
                    index: 0,
                },
                rng,
            )
            .unwrap();
            println!("generate_random_parameters: {:.3?}", now.elapsed());
            println!(
                "parameters size: {} bytes",
                (params.a.len() + params.b_g1.len() + params.h.len() + params.l.len() + params.vk.ic.len() + 3) * 96
                    + (params.b_g2.len() + 3) * 192
                    + 6 * 4
            );

            let now = Instant::now();
            let pvk = prepare_verifying_key(&params.vk);
            println!("prepare_verifying_key: {:.3?}", now.elapsed());

            let now = Instant::now();
            let proof = create_random_proof(MerkleCircuit { tree, index }, &params, rng).unwrap();
            println!("create_random_proof: {:.3?}", now.elapsed());

            let now = Instant::now();
            assert!(verify_proof(&pvk, &proof, &[vec![root], index_scalar].concat()).unwrap());
            println!("verify_proof: {:.3?}", now.elapsed());
            println!();
        }
    }
}
