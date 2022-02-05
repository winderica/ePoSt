use std::collections::HashSet;

use bellperson::{
    bls::{Bls12, Fr, FrRepr},
    gadgets::multipack::pack_into_inputs,
    Circuit, ConstraintSystem, SynthesisError, Variable,
};
use fff::{Field, PrimeField};
use openssl::bn::{BigNum, BigNumContext, MsbOption};
use rand::thread_rng;
use rayon::{prelude::*, ThreadPool};

use crate::{
    bn::{bn_to_bool_arr, generate_prime, mod_exp, mod_inv, power_of_2, rand, rand_range, rshift1},
    ops::{alloc_bool_input_regs, alloc_bool_regs, alloc_u127_regs, RegBool, Register},
    ops::{
        alloc_u127_input_regs, alloc_u64_input_regs, alloc_u64_regs, into_regs, regs_equal, regs_mod, regs_mod_exp,
        regs_mod_mul, Operation,
    },
    poseidon::{perm, PoseidonCircuit, WIDTH},
    utils::{alloc, alloc_input, ZERO},
};

#[derive(Debug, Clone)]
pub struct PK<N, E> {
    pub n: N,
    pub g: N,
    pub e: E,
}

#[derive(Debug, Clone)]
pub struct SK<D> {
    pub d: D,
    pub v: Fr,
}

#[derive(Debug, Clone)]
pub struct Challenge<M> {
    pub m: M,
    pub k1: Fr,
    pub k2: Fr,
}

#[derive(Debug, Clone)]
pub struct Proof<T, R> {
    pub t: T,
    pub r: R,
}

pub fn key_gen(bits: i32) -> (PK<BigNum, BigNum>, SK<BigNum>) {
    let mut ctx = BigNumContext::new().unwrap();
    let p = generate_prime(bits, true);
    let q = generate_prime(bits, true);
    let n = &p * &q;
    let g = mod_exp(&rand_range(&n), &BigNum::from_u32(2).unwrap(), &n, &mut ctx);

    let nn = &rshift1(&p) * &rshift1(&q);

    let v = Fr::random(&mut thread_rng());

    loop {
        let e = &generate_prime(bits * 2, false) % &nn;
        let d = mod_inv(&e, &nn, &mut ctx);
        if e.num_bits() == bits * 2 - 2 && d.num_bits() == bits * 2 - 2 {
            return (PK { n, g, e }, SK { d, v });
        }
    }
}

pub fn tag_gen(pk: &PK<BigNum, BigNum>, sk: &SK<BigNum>, blocks: &Vec<BigNum>, threads: usize) -> Vec<BigNum> {
    let pool = rayon::ThreadPoolBuilder::new().num_threads(threads).build().unwrap();
    let (tx, rx) = std::sync::mpsc::channel();
    for i in 0..blocks.len() {
        let block = blocks[i].to_owned().unwrap();
        let tx = tx.clone();
        let v = sk.v;
        let d = sk.d.to_owned().unwrap();
        let g = pk.g.to_owned().unwrap();
        let n = pk.n.to_owned().unwrap();
        pool.spawn(move || {
            let mut ctx = BigNumContext::new().unwrap();
            let i = Fr::from(i as u64);
            let w = perm(&[i, v, ZERO, ZERO, ZERO]);
            let tag = perm(&w)[0];
            let mut tag = BigNum::from_slice(&tag.to_bytes_be()).unwrap();
            let g = mod_exp(&g, &block, &n, &mut ctx);
            tag = &(&tag * &tag) * &g;
            tx.send(mod_exp(&tag, &d, &n, &mut ctx)).unwrap();
        });
    }
    drop(tx);
    rx.into_iter().collect()
}

pub fn prove(
    ell: i32,
    pk: &PK<BigNum, BigNum>,
    blocks: &Vec<BigNum>,
    c: &Challenge<BigNum>,
    tags: &Vec<BigNum>,
) -> Proof<BigNum, BigNum> {
    let mut ctx = BigNumContext::new().unwrap();
    let i = perm(&[c.k1, ZERO, ZERO, ZERO, ZERO])[0];
    let i = &BigNum::from_slice(&i.to_bytes_be()).unwrap() % &c.m;
    let i: usize = i.to_dec_str().unwrap().parse().unwrap();
    let a = perm(&[c.k2, ZERO, ZERO, ZERO, ZERO])[0];
    let a = &BigNum::from_slice(&a.to_bytes_be()).unwrap() % &power_of_2(ell);
    let t = mod_exp(&tags[i], &a, &pk.n, &mut ctx);
    let r = &a * &blocks[i];
    Proof { t, r }
}

pub fn verify(
    ell: i32,
    pk: &PK<BigNum, BigNum>,
    sk: &SK<BigNum>,
    c: &Challenge<BigNum>,
    proof: &Proof<BigNum, BigNum>,
) -> bool {
    let mut ctx = BigNumContext::new().unwrap();
    let mut g = mod_exp(&pk.g, &proof.r, &pk.n, &mut ctx);

    let i = perm(&[c.k1, ZERO, ZERO, ZERO, ZERO])[0];
    let i = &BigNum::from_slice(&i.to_bytes_be()).unwrap() % &c.m;
    let i = Fr::from_bytes_be(&i.to_vec_padded(32).unwrap()).unwrap();
    let a = perm(&[c.k2, ZERO, ZERO, ZERO, ZERO])[0];
    let a = &BigNum::from_slice(&a.to_bytes_be()).unwrap() % &power_of_2(ell);
    let w = perm(&[i, sk.v, ZERO, ZERO, ZERO]);
    let tag = perm(&w)[0];
    let mut tag = BigNum::from_slice(&tag.to_bytes_be()).unwrap();
    tag = &tag * &tag;
    tag = mod_exp(&tag, &a, &pk.n, &mut ctx);
    g = &(&g * &tag) % &pk.n;

    return g == mod_exp(&proof.t, &pk.e, &pk.n, &mut ctx);
}

pub struct PDPCircuit<U> {
    pub ell: usize,
    pub pk: PK<Vec<U>, Vec<bool>>,
    pub v: Fr,
    pub c: Challenge<u32>,
    pub proof: Proof<Vec<U>, Vec<bool>>,
}

impl<U> PDPCircuit<U> {
    pub fn verify<CS, Reg, T>(
        cs: &mut CS,
        n: &Vec<Reg>,
        g: &Vec<Reg>,
        e: &Vec<RegBool>,
        v: &Fr,
        v_var: &Variable,
        k1: &Fr,
        k1_var: &Variable,
        k2: &Fr,
        k2_var: &Variable,
        m: &Vec<Reg>,
        r: &Vec<RegBool>,
        t: &Vec<Reg>,
        ell: usize,
    ) where
        CS: ConstraintSystem<Bls12>,
        Reg: Register<T> + Operation,
    {
        let (i, i_var) = {
            let (scalar, var) = (
                [*k1, ZERO, ZERO, ZERO, ZERO],
                [*k1_var, alloc(cs, ZERO), alloc(cs, ZERO), alloc(cs, ZERO), alloc(cs, ZERO)],
            );
            let (scalar, var) = PoseidonCircuit::perm(cs, &scalar, &var);
            let i = into_regs(cs, &scalar[0], &var[0]);
            let i = regs_mod(cs, &i, m);
            (i[0].scalar(), i[0].variable())
        };
        let a = {
            let (scalar, var) = (
                [*k2, ZERO, ZERO, ZERO, ZERO],
                [*k2_var, alloc(cs, ZERO), alloc(cs, ZERO), alloc(cs, ZERO), alloc(cs, ZERO)],
            );
            let (a, a_var) = PoseidonCircuit::perm(cs, &scalar, &var);
            into_regs(cs, &a[0], &a_var[0])
        };
        let (w, w_var) = {
            let (scalar, var) = (
                [i, *v, ZERO, ZERO, ZERO],
                [i_var, *v_var, alloc(cs, ZERO), alloc(cs, ZERO), alloc(cs, ZERO)],
            );
            PoseidonCircuit::perm(cs, &scalar, &var)
        };
        let tag = {
            let (tag, tag_var) = PoseidonCircuit::perm(cs, &w, &w_var);
            let mut tag = into_regs(cs, &tag[0], &tag_var[0]);
            tag = regs_mod_mul(cs, &tag, &tag, n);
            regs_mod_exp(cs, &tag, &a[..ell], n)
        };
        let g = {
            let g = regs_mod_exp(cs, g, r, n);
            regs_mod_mul(cs, &g, &tag, n)
        };
        let gg = regs_mod_exp(cs, t, e, n);

        regs_equal(cs, &g, &gg);
    }
}

impl Circuit<Bls12> for PDPCircuit<u64> {
    fn synthesize<CS: ConstraintSystem<Bls12>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
        let PDPCircuit { pk, v, c, proof, ell } = self;

        let t = alloc_u64_regs(cs, &proof.t);
        let r = alloc_bool_regs(cs, &proof.r);

        let n = alloc_u64_input_regs(cs, &pk.n);
        let g = alloc_u64_input_regs(cs, &pk.g);
        let e = alloc_bool_input_regs(cs, &pk.e);
        let v_var = alloc_input(cs, v);
        let m = alloc_u64_input_regs(cs, &[c.m as u64]);
        let k1_var = alloc_input(cs, c.k1);
        let k2_var = alloc_input(cs, c.k2);

        Self::verify(
            cs, &n, &g, &e, &v, &v_var, &c.k1, &k1_var, &c.k2, &k2_var, &m, &r, &t, ell,
        );

        Ok(())
    }
}

impl Circuit<Bls12> for PDPCircuit<u128> {
    fn synthesize<CS: ConstraintSystem<Bls12>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
        let PDPCircuit { pk, v, c, proof, ell } = self;

        let t = alloc_u127_regs(cs, &proof.t);
        let r = alloc_bool_regs(cs, &proof.r);

        let n = alloc_u127_input_regs(cs, &pk.n);
        let g = alloc_u127_input_regs(cs, &pk.g);
        let e = alloc_bool_input_regs(cs, &pk.e);
        let v_var = alloc_input(cs, v);
        let m = alloc_u127_input_regs(cs, &[c.m as u128]);
        let k1_var = alloc_input(cs, c.k1);
        let k2_var = alloc_input(cs, c.k2);

        Self::verify(
            cs, &n, &g, &e, &v, &v_var, &c.k1, &k1_var, &c.k2, &k2_var, &m, &r, &t, ell,
        );

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use std::{str::FromStr, time::Instant};

    use crate::{
        bn::{bn_to_u127_arr, bn_to_u64_arr},
        ops::{bool_to_scalar, u127_to_scalar, u64_to_scalar},
    };
    use bellperson::groth16::{
        aggregate::{aggregate_proofs, setup_fake_srs, verify_aggregate_proof},
        create_random_proof, generate_random_parameters, prepare_verifying_key, verify_proof,
    };
    use rand::rngs::OsRng;

    const TOTAL_BLOCK_COUNT: u32 = 10000;

    #[test]
    fn test_pdp() {
        let length = 32;
        let ell = length * 64 / 8;
        let now = Instant::now();
        let (pk, sk) = key_gen(32 * length);
        println!("key_gen: {:.3?}", now.elapsed());
        let blocks = (0..TOTAL_BLOCK_COUNT).into_iter().map(|_| rand(32 * length)).collect();
        let now = Instant::now();
        let tags = tag_gen(&pk, &sk, &blocks, 0);
        println!("tag_gen: {:.3?}", now.elapsed());
        let c = Challenge {
            m: BigNum::from_u32(TOTAL_BLOCK_COUNT).unwrap(),
            k1: Fr::random(&mut thread_rng()),
            k2: Fr::random(&mut thread_rng()),
        };
        let now = Instant::now();
        let proof = prove(ell, &pk, &blocks, &c, &tags);
        println!("prove: {:.3?}", now.elapsed());
        let now = Instant::now();
        assert!(verify(ell, &pk, &sk, &c, &proof));
        println!("verify: {:.3?}", now.elapsed());
    }

    #[test]
    fn test_pdp_u64_zk() {
        for length in [1, 2, 4, 8 /*, 16, 32 */] {
            let ell = length * 64 / 8;
            println!("N size: {} bits", 64 * length);
            let (pk, sk) = key_gen(32 * length);
            let blocks = (0..TOTAL_BLOCK_COUNT).into_iter().map(|_| rand(32 * length)).collect();
            let tags = tag_gen(&pk, &sk, &blocks, 0);
            let c = Challenge {
                m: BigNum::from_u32(TOTAL_BLOCK_COUNT).unwrap(),
                k1: Fr::random(&mut thread_rng()),
                k2: Fr::random(&mut thread_rng()),
            };
            let proof = prove(ell, &pk, &blocks, &c, &tags);
            assert!(verify(ell, &pk, &sk, &c, &proof));

            let ell = ell as usize;
            let length = length as usize;
            let now = Instant::now();
            let params = generate_random_parameters(
                PDPCircuit::<u64> {
                    ell,
                    pk: PK {
                        n: vec![1; length],
                        g: vec![1; length],
                        e: vec![false; 64 * length],
                    },
                    v: ZERO,
                    c: Challenge {
                        m: 1,
                        k1: ZERO,
                        k2: ZERO,
                    },
                    proof: Proof {
                        r: vec![false; 64 * length],
                        t: vec![1; length],
                    },
                },
                &mut thread_rng(),
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

            let n = bn_to_u64_arr(&pk.n, length);
            let g = bn_to_u64_arr(&pk.g, length);
            let e = bn_to_bool_arr(&pk.e, 64 * length);

            let now = Instant::now();
            let proof = create_random_proof(
                PDPCircuit {
                    ell,
                    pk: PK {
                        n: n.clone(),
                        g: g.clone(),
                        e: e.clone(),
                    },
                    v: sk.v,
                    c: Challenge {
                        m: TOTAL_BLOCK_COUNT,
                        k1: c.k1,
                        k2: c.k2,
                    },
                    proof: Proof {
                        r: bn_to_bool_arr(&proof.r, 64 * length),
                        t: bn_to_u64_arr(&proof.t, length),
                    },
                },
                &params,
                &mut thread_rng(),
            )
            .unwrap();
            println!("create_random_proof: {:.3?}", now.elapsed());
            println!("proof size: {} bytes", (2 * 96 + 192) / 2);

            let now = Instant::now();
            assert!(verify_proof(
                &pvk,
                &proof,
                &[
                    n.iter().map(|&i| u64_to_scalar(i)).collect(),
                    g.iter().map(|&i| u64_to_scalar(i)).collect(),
                    e.iter().map(|&i| bool_to_scalar(i)).collect(),
                    vec![sk.v],
                    vec![u64_to_scalar(TOTAL_BLOCK_COUNT as u64)],
                    vec![c.k1],
                    vec![c.k2]
                ]
                .concat()
            )
            .unwrap());
            println!("verify_proof: {:.3?}", now.elapsed());
            println!();
        }
    }

    #[test]
    fn test_pdp_u127_zk() {
        for length in [1, 2, 4, 8 /*, 16, 32 */] {
            let n_bits = 64 * length;
            let ell = n_bits / 8;
            println!("N size: {} bits", n_bits);
            let (pk, sk) = key_gen(n_bits / 2);
            let blocks = (0..TOTAL_BLOCK_COUNT).into_iter().map(|_| rand(n_bits / 2)).collect();
            let tags = tag_gen(&pk, &sk, &blocks, 0);
            let c = Challenge {
                m: BigNum::from_u32(TOTAL_BLOCK_COUNT).unwrap(),
                k1: Fr::random(&mut thread_rng()),
                k2: Fr::random(&mut thread_rng()),
            };
            let proof = prove(ell, &pk, &blocks, &c, &tags);
            assert!(verify(ell, &pk, &sk, &c, &proof));

            let ell = ell as usize;
            let length = (length / 2 + 1) as usize;
            let n_bits = n_bits as usize;
            let now = Instant::now();
            let params = generate_random_parameters(
                PDPCircuit::<u128> {
                    ell,
                    pk: PK {
                        n: vec![1; length],
                        g: vec![1; length],
                        e: vec![false; n_bits],
                    },
                    v: ZERO,
                    c: Challenge {
                        m: 1,
                        k1: ZERO,
                        k2: ZERO,
                    },
                    proof: Proof {
                        r: vec![false; n_bits],
                        t: vec![1; length],
                    },
                },
                &mut thread_rng(),
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

            let n = bn_to_u127_arr(&pk.n, length);
            let g = bn_to_u127_arr(&pk.g, length);
            let e = bn_to_bool_arr(&pk.e, n_bits);

            let now = Instant::now();
            let proof = create_random_proof(
                PDPCircuit {
                    ell,
                    pk: PK {
                        n: n.clone(),
                        g: g.clone(),
                        e: e.clone(),
                    },
                    v: sk.v,
                    c: Challenge {
                        m: TOTAL_BLOCK_COUNT,
                        k1: c.k1,
                        k2: c.k2,
                    },
                    proof: Proof {
                        r: bn_to_bool_arr(&proof.r, n_bits),
                        t: bn_to_u127_arr(&proof.t, length),
                    },
                },
                &params,
                &mut thread_rng(),
            )
            .unwrap();
            println!("create_random_proof: {:.3?}", now.elapsed());
            println!("proof size: {} bytes", (2 * 96 + 192) / 2);

            let now = Instant::now();
            assert!(verify_proof(
                &pvk,
                &proof,
                &[
                    n.iter().map(|&i| u127_to_scalar(i)).collect(),
                    g.iter().map(|&i| u127_to_scalar(i)).collect(),
                    e.iter().map(|&i| bool_to_scalar(i)).collect(),
                    vec![sk.v],
                    vec![u127_to_scalar(TOTAL_BLOCK_COUNT as u128)],
                    vec![c.k1],
                    vec![c.k2]
                ]
                .concat()
            )
            .unwrap());
            println!("verify_proof: {:.3?}", now.elapsed());
            println!();
        }
    }

    #[test]
    fn test_groth16_aggregation() {
        let length = 2;
        let n_bits = 64 * length;
        let ell = n_bits / 8;
        let (pk, sk) = key_gen(n_bits / 2);
        let blocks = (0..TOTAL_BLOCK_COUNT).into_iter().map(|_| rand(n_bits / 2)).collect();
        let tags = tag_gen(&pk, &sk, &blocks, 0);
        let c = Challenge {
            m: BigNum::from_u32(TOTAL_BLOCK_COUNT).unwrap(),
            k1: Fr::random(&mut thread_rng()),
            k2: Fr::random(&mut thread_rng()),
        };
        let proof = prove(ell, &pk, &blocks, &c, &tags);
        assert!(verify(ell, &pk, &sk, &c, &proof));

        let ell = ell as usize;
        let length = (length / 2 + 1) as usize;
        let n_bits = n_bits as usize;
        let now = Instant::now();
        let params = generate_random_parameters(
            PDPCircuit::<u128> {
                ell,
                pk: PK {
                    n: vec![1; length],
                    g: vec![1; length],
                    e: vec![false; 64 * length],
                },
                v: ZERO,
                c: Challenge {
                    m: 1,
                    k1: ZERO,
                    k2: ZERO,
                },
                proof: Proof {
                    r: vec![false; 64 * length],
                    t: vec![1; length],
                },
            },
            &mut thread_rng(),
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

        let n = bn_to_u127_arr(&pk.n, length);
        let g = bn_to_u127_arr(&pk.g, length);
        let e = bn_to_bool_arr(&pk.e, n_bits);

        let proof = create_random_proof(
            PDPCircuit {
                ell,
                pk: PK {
                    n: n.clone(),
                    g: g.clone(),
                    e: e.clone(),
                },
                v: sk.v,
                c: Challenge {
                    m: TOTAL_BLOCK_COUNT,
                    k1: c.k1,
                    k2: c.k2,
                },
                proof: Proof {
                    r: bn_to_bool_arr(&proof.r, n_bits),
                    t: bn_to_u127_arr(&proof.t, length),
                },
            },
            &params,
            &mut thread_rng(),
        )
        .unwrap();

        for proof_count in [2048, 4096, 8192, 16384, 32768] {
            println!("Proof count: {}", proof_count);
            let statements: Vec<_> = (0..proof_count)
                .map(|_| {
                    [
                        n.iter().map(|&i| u127_to_scalar(i)).collect(),
                        g.iter().map(|&i| u127_to_scalar(i)).collect(),
                        e.iter().map(|&i| bool_to_scalar(i)).collect(),
                        vec![sk.v],
                        vec![u127_to_scalar(TOTAL_BLOCK_COUNT as u128)],
                        vec![c.k1],
                        vec![c.k2],
                    ]
                    .concat()
                })
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
            assert!(verify_aggregate_proof(&vk, &pvk, &mut OsRng, &statements, &aggregate_proof, &to_include).unwrap());
            println!("verify_aggregate_proof: {:.3?}", now.elapsed());

            let mut v = vec![];
            aggregate_proof.write(&mut v).unwrap();
            println!("original proof size: {} bytes", (2 * 96 + 192) / 2 * proof_count);
            println!("aggregated proof size: {} bytes", v.len());

            println!();
        }
    }
}
