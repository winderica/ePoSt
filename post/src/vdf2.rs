use crate::bn::{bn_to_bool_arr, bn_to_u127_arr};
use crate::ops::{alloc_u127_input_regs, RegU127, RegBool, into_regs};
use crate::poseidon::PoseidonCircuit;
use crate::utils::{alloc, ZERO};
use crate::{
    bn::{duplicate, generate_prime, mod_exp, power_of_2, rand, rand_range},
    ops::{alloc_u127_regs, alloc_u64_regs, regs_equal, regs_mod_exp, regs_mod_mul, u127_to_scalar, RegU64, Register},
    poseidon::{perm, WIDTH},
};

use bellperson::{
    bls::{Bls12, Fr, FrRepr},
    Circuit, ConstraintSystem, LinearCombination, SynthesisError, Variable,
};
use openssl::bn::{BigNum, BigNumContext};

pub struct VDF {
    λ: usize,
    n: BigNum,
    regs: usize,
    ctx: BigNumContext,
}

impl VDF {
    pub fn new(λ: usize, n_bits: usize, n: Option<BigNum>) -> Self {
        let n = match n {
            Some(n) => n,
            None => {
                let prime_bits = n_bits >> 1;
                let p = generate_prime(prime_bits as i32, true);
                let q = generate_prime(prime_bits as i32, true);
                &p * &q
            }
        };

        Self {
            λ,
            n,
            regs: n_bits / 127 + 1,
            ctx: BigNumContext::new().unwrap(),
        }
    }

    pub fn generate_challenge(&self) -> BigNum {
        let x = rand_range(&self.n);
        &(&x * &x) % &self.n
    }

    pub fn eval(&mut self, x: &BigNum, t: usize) -> (BigNum, Vec<BigNum>) {
        let mut x = duplicate(x);
        let mut y = duplicate(&x);
        let n = &self.n;
        for _ in 0..(1 << t) {
            y = &(&y * &y) % n;
        }
        let yy = duplicate(&y);
        let mut π = vec![];
        for i in 0..t {
            let mut u = duplicate(&x);
            for _ in 0..(1 << (t - i - 1)) {
                u = &(&u * &u) % n;
            }
            let r = self.hash(&[&x, &y, &u], t - i);
            x = &(&mod_exp(&x, &r, n, &mut self.ctx) * &u) % n;
            y = &(&mod_exp(&u, &r, n, &mut self.ctx) * &y) % n;
            π.push(u);
        }
        (yy, π)
    }

    pub fn verify(&mut self, x: &BigNum, y: &BigNum, π: &[BigNum], t: usize) -> bool {
        let mut x = duplicate(x);
        let mut y = duplicate(y);
        let n = &self.n;
        for i in 0..t {
            let u = &π[i];
            let r = self.hash(&[&x, &y, u], t - i);
            x = &(&mod_exp(&x, &r, &n, &mut self.ctx) * u) % n;
            y = &(&mod_exp(u, &r, &n, &mut self.ctx) * &y) % n;
        }
        y == mod_exp(&x, &power_of_2(1), n, &mut self.ctx)
    }

    pub fn hash_bn(&self, mut state: [Fr; WIDTH], i: &BigNum) -> [Fr; WIDTH] {
        for chunk in bn_to_u127_arr(&i, self.regs).chunks(4) {
            chunk.iter().enumerate().for_each(|(i, &v)| {
                state[i] += u127_to_scalar(v);
            });
            state = perm(&state);
        }
        state
    }

    pub fn hash(&self, bn: &[&BigNum], t: usize) -> BigNum {
        let mut state = [ZERO; WIDTH];
        for i in bn {
            state = self.hash_bn(state, i);
        }
        state[0] += Fr::from(1 << t);
        state = perm(&state);
        let mut state = state[0].to_bytes_le()[..(self.λ / 8)].to_vec();
        state.reverse();
        BigNum::from_slice(&state).unwrap()
    }
}

pub struct VDFCircuit {
    pub n: Vec<u128>,
    pub x: Vec<u128>,
    pub y: Vec<u128>,
    pub π: Vec<Vec<u128>>,

    pub t: usize,
    pub λ: usize,
}

impl VDFCircuit {
    pub fn add_assign<CS: ConstraintSystem<Bls12>>(
        cs: &mut CS,
        a_scalar: &mut Fr,
        a_var: &mut Variable,
        b_scalar: &Fr,
        b_var: &Variable,
    ) {
        *a_scalar += b_scalar;
        let new_var = alloc(cs, *a_scalar);
        cs.enforce(
            || "",
            |lc| lc + new_var,
            |lc| lc + CS::one(),
            |lc| lc + *a_var + *b_var,
        );
        *a_var = new_var;
    }

    pub fn hash_regs<CS: ConstraintSystem<Bls12>>(
        cs: &mut CS,
        state_scalar: &mut [Fr; WIDTH],
        state_var: &mut [Variable; WIDTH],
        regs: &Vec<RegU127>,
    ) {
        for chunk in regs.chunks(4) {
            chunk.iter().enumerate().for_each(|(i, v)| {
                Self::add_assign(cs, &mut state_scalar[i], &mut state_var[i], &v.scalar(), &v.variable());
            });
            let (scalar, var) = PoseidonCircuit::perm(cs, state_scalar, state_var);
            *state_scalar = scalar;
            *state_var = var;
        }
    }

    pub fn hash<CS: ConstraintSystem<Bls12>>(cs: &mut CS, regs: &[&Vec<RegU127>], t: usize) -> Vec<RegBool> {
        let mut state_scalar = [ZERO; WIDTH];
        let mut state_var = state_scalar.map(|v| alloc(cs, v));
        for i in regs {
            Self::hash_regs(cs, &mut state_scalar, &mut state_var, i);
        }
        let t_scalar = Fr::from(1 << t);
        let t_var = alloc(cs, t_scalar);
        Self::add_assign(cs, &mut state_scalar[0], &mut state_var[0], &t_scalar, &t_var);
        let (state_scalar, state_var) = PoseidonCircuit::perm(cs, &state_scalar, &state_var);
        into_regs(cs, &state_scalar[0], &state_var[0])
    }

    pub fn verify<CS: ConstraintSystem<Bls12>>(
        cs: &mut CS,
        mut x: Vec<RegU127>,
        mut y: Vec<RegU127>,
        n: &Vec<RegU127>,
        π: &Vec<Vec<RegU127>>,
        t: usize,
        λ: usize,
    ) {
        for i in 0..t {
            // TODO: check whether u is in QR_N
            let u = &π[i];
            let r = &Self::hash(cs, &[&x, &y, u], t - i)[..λ];
            x = regs_mod_exp(cs, &x, r, n);
            x = regs_mod_mul(cs, &x, &u, n);
            let u = regs_mod_exp(cs, u, r, n);
            y = regs_mod_mul(cs, &y, &u, n);
        }
        x = regs_mod_mul(cs, &x, &x, n);

        regs_equal(cs, &x, &y);
    }
}

impl Circuit<Bls12> for VDFCircuit {
    fn synthesize<CS: ConstraintSystem<Bls12>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
        let x = alloc_u127_input_regs(cs, &self.x);
        let y = alloc_u127_regs(cs, &self.y);
        let n = alloc_u127_input_regs(cs, &self.n);
        let π = self.π.iter().map(|u| alloc_u127_regs(cs, &u)).collect();

        Self::verify(cs, x, y, &n, &π, self.t, self.λ);

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use std::{env, str::FromStr, time::Instant};

    use bellperson::groth16::{create_random_proof, generate_random_parameters, prepare_verifying_key, verify_proof};

    use super::*;

    const Λ: usize = 128;
    const N_BITS: usize = 2048;

    #[test]
    fn test_svdf() {
        let now = Instant::now();
        let mut vdf = VDF::new(Λ, N_BITS, None);
        println!("setup: {:.3?}", now.elapsed());

        let now = Instant::now();
        let x = vdf.generate_challenge();
        println!("generate_challenge: {:.3?}", now.elapsed());

        for t in 1..26 {
            println!("t: {}", t);

            let now = Instant::now();
            let (y, π) = vdf.eval(&x, t);
            let b = now.elapsed();
            println!("eval: {:.3?}", b);

            let now = Instant::now();
            assert!(vdf.verify(&x, &y, &π, t));
            println!("verify: {:.3?}", now.elapsed());
            println!();
        }
    }

    #[test]
    fn test_svdf_zk() {
        let now = Instant::now();
        let mut vdf = VDF::new(Λ, N_BITS, None);
        println!("setup: {:.3?}", now.elapsed());

        let now = Instant::now();
        let x = vdf.generate_challenge();
        println!("generate_challenge: {:.3?}", now.elapsed());

        for t in 1..28 {
            println!("t: {}", t);

            let now = Instant::now();
            let (y, π) = vdf.eval(&x, t);
            println!("eval: {:.3?}", now.elapsed());

            let now = Instant::now();
            assert!(vdf.verify(&x, &y, &π, t));
            println!("verify: {:.3?}", now.elapsed());

            let rng = &mut rand::thread_rng();
            let now = Instant::now();
            let params = generate_random_parameters(
                VDFCircuit {
                    x: vec![1; vdf.regs],
                    y: vec![1; vdf.regs],
                    π: vec![vec![1; vdf.regs]; t],
                    n: vec![1; vdf.regs],
                    t,
                    λ: Λ,
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

            let x = bn_to_u127_arr(&x, vdf.regs);
            let y = bn_to_u127_arr(&y, vdf.regs);
            let π = π
                .iter()
                .map(|i| bn_to_u127_arr(&i, vdf.regs))
                .collect::<Vec<_>>();
            let n = bn_to_u127_arr(&vdf.n, vdf.regs);

            let now = Instant::now();
            let proof = create_random_proof(
                VDFCircuit {
                    x: x.clone(),
                    y,
                    π,
                    n: n.clone(),
                    t,
                    λ: Λ,
                },
                &params,
                rng,
            )
            .unwrap();
            println!("create_random_proof: {:.3?}", now.elapsed());

            let now = Instant::now();
            assert!(verify_proof(
                &pvk,
                &proof,
                &[x, n].concat().iter().map(|&i| u127_to_scalar(i)).collect::<Vec<_>>()
            )
            .unwrap());
            println!("verify_proof: {:.3?}", now.elapsed());
            println!();
        }
    }
}
