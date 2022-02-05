use bellperson::{
    bls::{Bls12, Fr, FrRepr},
    Circuit, ConstraintSystem, SynthesisError, Variable,
};
use fff::{Field, PrimeField};
use openssl::bn::{BigNum, BigNumContext, MsbOption};
use rand::thread_rng;

use crate::{
    bn::{bn_to_bool_arr, duplicate, generate_prime, mod_exp, mod_inv, power_of_2, rand, rand_range, rshift1},
    merkle::MerkleCircuit,
    ops::{alloc_bool_input_regs, alloc_bool_regs, alloc_u127_regs, into_regs, u127_to_scalar, Register},
    ops::{alloc_u64_regs, regs_equal, regs_mod, regs_mod_exp, regs_mod_mul},
    pdp::{Challenge, PDPCircuit, Proof, PK, SK},
    poseidon::{perm, PoseidonCircuit, WIDTH},
    utils::{alloc, alloc_input, ZERO},
    vdf2::VDFCircuit,
};

const N_BITS: usize = 2048;
const LOG_T: usize = 27;
const Λ: usize = 128;
const BATCH_SIZE: usize = 2;
const BLOCK_SIZE: i32 = N_BITS as i32 - 2 - 1 - Λ as i32;

pub struct PoSTCircuit<'a> {
    pub pk: &'a PK<Vec<u128>, Vec<bool>>,
    pub v: Fr,
    pub c: Challenge<u32>,
    pub π_pdp: &'a Proof<Vec<u128>, Vec<bool>>,
    pub y: &'a Vec<u128>,
    pub π_vdf: &'a Vec<Vec<u128>>,
    pub tree: &'a Vec<Vec<Fr>>,
    pub index: usize,
}

impl Circuit<Bls12> for PoSTCircuit<'_> {
    fn synthesize<CS: ConstraintSystem<Bls12>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
        let PoSTCircuit {
            pk,
            v,
            c,
            π_pdp,
            π_vdf,
            y,
            tree,
            index,
        } = self;

        let t = alloc_u127_regs(cs, &π_pdp.t);
        let r = alloc_bool_regs(cs, &π_pdp.r);
        let m = alloc_u127_regs(cs, &[c.m as u128]);
        let n = alloc_u127_regs(cs, &pk.n);
        let g = alloc_u127_regs(cs, &pk.g);
        let e = alloc_bool_regs(cs, &pk.e);

        let x = regs_mod_mul(cs, &t, &t, &n);
        let y = alloc_u127_regs(cs, &y);
        let π_vdf = π_vdf.iter().map(|u| alloc_u127_regs(cs, &u)).collect();

        let k1 = c.k1;
        let k2 = c.k2;
        let k1_var = alloc(cs, k1);
        let k2_var = alloc(cs, k2);
        let v_var = alloc(cs, v);

        PDPCircuit::<u128>::verify(
            cs, &n, &g, &e, &v, &v_var, &c.k1, &k1_var, &c.k2, &k2_var, &m, &r, &t, Λ,
        );

        let (kk1, kk1_var, kk2, kk2_var) = {
            let mut state = [ZERO; WIDTH];
            let mut state_var = state.map(|v| alloc(cs, v));
            VDFCircuit::hash_regs(cs, &mut state, &mut state_var, &y);
            (state[0], state_var[0], state[1], state_var[1])
        };

        VDFCircuit::verify(cs, x, y, &n, &π_vdf, LOG_T, Λ);

        let (k, k_var) = {
            let (state, state_var) = (
                [k1, k2, ZERO, ZERO, ZERO],
                [k1_var, k2_var, alloc(cs, ZERO), alloc(cs, ZERO), alloc(cs, ZERO)],
            );
            let (i, i_var) = PoseidonCircuit::perm(cs, &state, &state_var);
            (i[0], i_var[0])
        };
        let (kk, kk_var) = {
            let (state, state_var) = (
                [kk1, kk2, ZERO, ZERO, ZERO],
                [kk1_var, kk2_var, alloc(cs, ZERO), alloc(cs, ZERO), alloc(cs, ZERO)],
            );
            let (i, i_var) = PoseidonCircuit::perm(cs, &state, &state_var);
            (i[0], i_var[0])
        };

        let root = tree[0][0];
        let root_var = alloc_input(cs, root);

        for (leaf, leaf_var, i) in [(k, k_var, index), (kk, kk_var, index + 1)] {
            let (_, curr_var) = MerkleCircuit::build_root(cs, tree, i, &leaf, &leaf_var);
            cs.enforce(|| "", |lc| lc + curr_var, |lc| lc + CS::one(), |lc| lc + root_var);
        }

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use std::{env, str::FromStr, time::Instant};

    use bellperson::groth16::{
        aggregate::{aggregate_proofs, setup_fake_srs, verify_aggregate_proof},
        create_random_proof, generate_random_parameters, prepare_verifying_key, verify_proof,
    };
    use rand::{rngs::OsRng, Rng};

    use crate::{
        bn::bn_to_u127_arr,
        merkle::merkelize,
        pdp::{key_gen, prove, tag_gen, verify},
        vdf2::{VDFCircuit, VDF},
    };

    use super::*;

    #[test]
    fn test_post_setup() {
        for i in [1, 2, 4, 8, 16] {
            println!("file size: {} MB", i * 64);
            let now = Instant::now();
            let (pk, sk) = key_gen((N_BITS / 2) as i32);
            println!("key_gen: {:.3?}", now.elapsed());

            let now = Instant::now();
            VDF::new(Λ, N_BITS, Some(pk.n.to_owned().unwrap()));
            println!("setup: {:.3?}", now.elapsed());

            let block_count = i * 64 * 1024 * 1024 * 8 / BLOCK_SIZE as u64;
            let blocks = (0..block_count).into_iter().map(|_| rand(BLOCK_SIZE)).collect();
            let now = Instant::now();
            tag_gen(&pk, &sk, &blocks, 0);
            println!("tag_gen: {:.3?}", now.elapsed());
            println!();
        }
    }

    #[test]
    fn test_post_setup_multithreading() {
        let now = Instant::now();
        let (pk, sk) = key_gen((N_BITS / 2) as i32);
        println!("key_gen: {:.3?}", now.elapsed());

        let now = Instant::now();
        VDF::new(Λ, N_BITS, Some(pk.n.to_owned().unwrap()));
        println!("setup: {:.3?}", now.elapsed());

        let block_count = 64 * 1024 * 1024 * 8 / BLOCK_SIZE as u64;
        let blocks = (0..block_count).into_iter().map(|_| rand(BLOCK_SIZE)).collect();

        for i in [1, 2, 3, 4, 5, 6, 7, 8] {
            println!("threads: {}", i);
            let now = Instant::now();
            tag_gen(&pk, &sk, &blocks, i);
            println!("tag_gen: {:.3?}", now.elapsed());
        }
    }

    #[test]
    fn test_post_zk() {
        let rng = &mut thread_rng();

        let now = Instant::now();
        let (pk, sk) = key_gen((N_BITS / 2) as i32);
        println!("key_gen: {:.3?}", now.elapsed());

        let now = Instant::now();
        let mut vdf = VDF::new(Λ, N_BITS, Some(pk.n.to_owned().unwrap()));
        println!("setup: {:.3?}", now.elapsed());

        let block_count = 64 * 1024 * 1024 * 8 / BLOCK_SIZE as u32;
        let blocks = (0..block_count).into_iter().map(|_| rand(BLOCK_SIZE)).collect();
        let now = Instant::now();
        let tags = tag_gen(&pk, &sk, &blocks, 0);
        println!("tag_gen: {:.3?}", now.elapsed());

        let mut leaves = vec![];
        let mut witnesses = vec![];

        let mut c = Challenge {
            m: BigNum::from_u32(block_count).unwrap(),
            k1: Fr::random(rng),
            k2: Fr::random(rng),
        };
        leaves.push(perm(&[c.k1, c.k2, ZERO, ZERO, ZERO])[0]);
        for i in 0..BATCH_SIZE - 1 {
            let now = Instant::now();
            let π_pdp = prove(Λ.try_into().unwrap(), &pk, &blocks, &c, &tags);
            println!("prove {}: {:.3?}", i, now.elapsed());
            let x = &(&π_pdp.t * &π_pdp.t) % &pk.n;
            let now = Instant::now();
            let (y, π_vdf) = vdf.eval(&x, LOG_T);
            println!("eval {}: {:.3?}", i, now.elapsed());
            let k = vdf.hash_bn([ZERO; WIDTH], &y);
            witnesses.push((c.k1, c.k2, π_pdp, y, π_vdf));
            c.k1 = k[0];
            c.k2 = k[1];
            leaves.push(perm(&[c.k1, c.k2, ZERO, ZERO, ZERO])[0]);
        }

        let tree = &merkelize(&leaves);

        let length = N_BITS / 127 + 1;
        let now = Instant::now();
        let params = generate_random_parameters(
            PoSTCircuit {
                pk: &PK {
                    n: vec![1; length],
                    g: vec![1; length],
                    e: vec![false; N_BITS],
                },
                v: ZERO,
                c: Challenge {
                    m: 1,
                    k1: ZERO,
                    k2: ZERO,
                },
                π_pdp: &Proof {
                    r: vec![false; N_BITS],
                    t: vec![1; length],
                },
                y: &vec![1; length],
                π_vdf: &vec![vec![1; length]; LOG_T],
                tree: &tree.iter().map(|i| vec![ZERO; i.len()]).collect(),
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

        let root = tree[0][0];
        let height = tree.len() - 1;
        for index in 0..tree[height].len() - 1 {
            let next_index = index + 1;
            let (k1, k2, π_pdp, y, π_vdf) = &witnesses[index];
            let index_scalar = (0..height).map(|h| Fr::from(((index >> h) & 1) as u64)).collect();
            let next_index_scalar = (0..height).map(|h| Fr::from(((next_index >> h) & 1) as u64)).collect();
            let pk = &PK {
                n: bn_to_u127_arr(&pk.n, length),
                g: bn_to_u127_arr(&pk.g, length),
                e: bn_to_bool_arr(&pk.e, N_BITS),
            };
            let π_pdp = &Proof {
                r: bn_to_bool_arr(&π_pdp.r, N_BITS),
                t: bn_to_u127_arr(&π_pdp.t, length),
            };
            let y = &bn_to_u127_arr(&y, length);
            let π_vdf = &π_vdf.iter().map(|i| bn_to_u127_arr(&i, length)).collect();
            let now = Instant::now();
            let proof = create_random_proof(
                PoSTCircuit {
                    pk,
                    v: sk.v,
                    c: Challenge {
                        m: block_count,
                        k1: *k1,
                        k2: *k2,
                    },
                    π_pdp,
                    y,
                    π_vdf,
                    tree,
                    index,
                },
                &params,
                rng,
            )
            .unwrap();
            println!("create_random_proof {}: {:.3?}", index, now.elapsed());

            let now = Instant::now();
            assert!(verify_proof(&pvk, &proof, &[vec![root], index_scalar, next_index_scalar].concat()).unwrap());
            println!("verify_proof {}: {:.3?}", index, now.elapsed());
        }
    }

    #[test]
    fn test_post_aggregation() {
        let rng = &mut thread_rng();

        let now = Instant::now();
        let (pk, sk) = key_gen((N_BITS / 2) as i32);
        println!("key_gen: {:.3?}", now.elapsed());

        let now = Instant::now();
        let mut vdf = VDF::new(Λ, N_BITS, Some(pk.n.to_owned().unwrap()));
        println!("setup: {:.3?}", now.elapsed());

        let block_count = 64 * 1024 * 1024 * 8 / BLOCK_SIZE as u32;
        let blocks = (0..block_count).into_iter().map(|_| rand(BLOCK_SIZE)).collect();
        let now = Instant::now();
        let tags = tag_gen(&pk, &sk, &blocks, 0);
        println!("tag_gen: {:.3?}", now.elapsed());

        let mut leaves = vec![];
        let mut witnesses = vec![];

        let mut c = Challenge {
            m: BigNum::from_u32(block_count).unwrap(),
            k1: Fr::random(rng),
            k2: Fr::random(rng),
        };
        leaves.push(perm(&[c.k1, c.k2, ZERO, ZERO, ZERO])[0]);
        for i in 0..BATCH_SIZE - 1 {
            let now = Instant::now();
            let π_pdp = prove(Λ.try_into().unwrap(), &pk, &blocks, &c, &tags);
            println!("prove {}: {:.3?}", i, now.elapsed());
            let x = &(&π_pdp.t * &π_pdp.t) % &pk.n;
            let now = Instant::now();
            let (y, π_vdf) = vdf.eval(&x, LOG_T);
            println!("eval {}: {:.3?}", i, now.elapsed());
            let k = vdf.hash_bn([ZERO; WIDTH], &y);
            witnesses.push((c.k1, c.k2, π_pdp, y, π_vdf));
            c.k1 = k[0];
            c.k2 = k[1];
            leaves.push(perm(&[c.k1, c.k2, ZERO, ZERO, ZERO])[0]);
        }

        let tree = &merkelize(&leaves);

        let length = N_BITS / 127 + 1;
        let now = Instant::now();
        let params = generate_random_parameters(
            PoSTCircuit {
                pk: &PK {
                    n: vec![1; length],
                    g: vec![1; length],
                    e: vec![false; N_BITS],
                },
                v: ZERO,
                c: Challenge {
                    m: 1,
                    k1: ZERO,
                    k2: ZERO,
                },
                π_pdp: &Proof {
                    r: vec![false; N_BITS],
                    t: vec![1; length],
                },
                y: &vec![1; length],
                π_vdf: &vec![vec![1; length]; LOG_T],
                tree: &tree.iter().map(|i| vec![ZERO; i.len()]).collect(),
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

        let root = tree[0][0];
        let height = tree.len() - 1;
        for index in 0..tree[height].len() - 1 {
            let next_index = index + 1;
            let (k1, k2, π_pdp, y, π_vdf) = &witnesses[index];
            let index_scalar = (0..height)
                .map(|h| Fr::from(((index >> h) & 1) as u64))
                .collect::<Vec<_>>();
            let next_index_scalar = (0..height)
                .map(|h| Fr::from(((next_index >> h) & 1) as u64))
                .collect::<Vec<_>>();
            let pk = &PK {
                n: bn_to_u127_arr(&pk.n, length),
                g: bn_to_u127_arr(&pk.g, length),
                e: bn_to_bool_arr(&pk.e, N_BITS),
            };
            let π_pdp = &Proof {
                r: bn_to_bool_arr(&π_pdp.r, N_BITS),
                t: bn_to_u127_arr(&π_pdp.t, length),
            };
            let y = &bn_to_u127_arr(&y, length);
            let π_vdf = &π_vdf.iter().map(|i| bn_to_u127_arr(&i, length)).collect();
            let now = Instant::now();
            let proof = create_random_proof(
                PoSTCircuit {
                    pk,
                    v: sk.v,
                    c: Challenge {
                        m: block_count,
                        k1: *k1,
                        k2: *k2,
                    },
                    π_pdp,
                    y,
                    π_vdf,
                    tree,
                    index,
                },
                &params,
                rng,
            )
            .unwrap();
            println!("create_random_proof {}: {:.3?}", index, now.elapsed());

            let now = Instant::now();
            assert!(verify_proof(
                &pvk,
                &proof,
                &[vec![root], index_scalar.clone(), next_index_scalar.clone()].concat()
            )
            .unwrap());
            println!("verify_proof {}: {:.3?}", index, now.elapsed());

            for proof_count in [2048, 4096, 8192, 16384, 32768] {
                println!("Proof count: {}", proof_count);
                let statements: Vec<_> = (0..proof_count)
                    .map(|_| [vec![root], index_scalar.clone(), next_index_scalar.clone()].concat())
                    .collect();
                let proofs: Vec<_> = (0..proof_count).map(|_| proof.clone()).collect();

                let to_include = vec![]; // TODO

                let now = Instant::now();
                let (pk, vk) = setup_fake_srs(&mut thread_rng(), proof_count).specialize(proof_count);
                println!("setup_fake_srs: {:.3?}", now.elapsed());

                let now = Instant::now();
                let aggregate_proof = aggregate_proofs(&pk, &to_include, &proofs).unwrap();
                println!("aggregate_proofs: {:.3?}", now.elapsed());
                let now = Instant::now();
                assert!(
                    verify_aggregate_proof(&vk, &pvk, &mut OsRng, &statements, &aggregate_proof, &to_include).unwrap()
                );
                println!("verify_aggregate_proof: {:.3?}", now.elapsed());

                let mut v = vec![];
                aggregate_proof.write(&mut v).unwrap();
                println!("original proof size: {} bytes", (2 * 96 + 192) / 2 * proof_count);
                println!("aggregated proof size: {} bytes", v.len());

                println!();
            }
        }
    }
}
