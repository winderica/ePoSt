use bellperson::{
    bls::{Bls12, Fr, FrRepr},
    Circuit, ConstraintSystem, SynthesisError,
};

use bellperson::groth16::{
    self, create_random_proof, create_random_proof_batch, generate_random_parameters, prepare_verifying_key,
    verify_proof, Proof,
};
use fff::{Field, PrimeField};

use std::time::{Duration, Instant};

pub const ONE_FIFTH: [u64; 4] = [0x33333332CCCCCCCD, 0x217F0E679998F199, 0xE14A56699D73F002, 0x2E5F0FBADD72321C];

pub fn minroot(mut x: Fr, mut y: Fr, rounds: usize) -> (Fr, Fr) {
    for _ in 0..rounds {
        let tmp = (x + y).pow(ONE_FIFTH);
        y = x;
        x = tmp;
    }

    (x, y)
}

#[derive(Clone)]
pub struct MinRoot {
    pub x: Fr,
    pub y: Fr,
    pub x0: Fr,
    pub y0: Fr,
    pub rounds: usize,
}

impl Circuit<Bls12> for MinRoot {
    fn synthesize<CS: ConstraintSystem<Bls12>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
        let mut x = self.x;
        let mut y = self.y;
        let mut x_var = cs.alloc(|| "x", || Ok(x))?;
        let mut y_var = cs.alloc(|| "y", || Ok(y))?;

        for i in 0..self.rounds {
            let cs = &mut cs.namespace(|| format!("round {}", i));

            let x2 = x * x;
            let x2_var = cs.alloc(|| "x^2", || Ok(x2))?;
            cs.enforce(|| "x^2 = x * x", |lc| lc + x_var, |lc| lc + x_var, |lc| lc + x2_var);

            let x4 = x2 * x2;
            let x4_var = cs.alloc(|| "x^4", || Ok(x4))?;
            cs.enforce(
                || "x^4 = x^2 * x^2",
                |lc| lc + x2_var,
                |lc| lc + x2_var,
                |lc| lc + x4_var,
            );

            let x5 = x * x4 - y;
            let x5_var = cs.alloc(|| "x^5 - y", || Ok(x5))?;
            cs.enforce(
                || "x * x^4 = x^5 - y + y",
                |lc| lc + x_var,
                |lc| lc + x4_var,
                |lc| lc + x5_var + y_var,
            );

            x = y;
            x_var = y_var;
            y = x5;
            y_var = x5_var;
        }

        let x0_var = cs.alloc_input(|| "x0", || Ok(self.x0)).unwrap();
        let y0_var = cs.alloc_input(|| "y0", || Ok(self.y0)).unwrap();

        cs.enforce(|| "x = x0", |lc| lc + x_var, |lc| lc + CS::one(), |lc| lc + x0_var);
        cs.enforce(|| "y = y0", |lc| lc + y_var, |lc| lc + CS::one(), |lc| lc + y0_var);

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use std::{str::FromStr, time::Instant};

    use super::*;

    #[test]
    fn test_minroot() {
        const MINROOT_ROUNDS: usize = 100;
        let rng = &mut rand::thread_rng();
        let xl = Fr::random(rng);
        let xr = Fr::random(rng);
        let now = Instant::now();
        minroot(xl, xr, MINROOT_ROUNDS);
        println!("minroot: {:.3?}", now.elapsed());
    }

    #[test]
    fn test_minroot_zk() {
        let rng = &mut rand::thread_rng();

        for i in 0..6 {
            let rounds = 10_usize.pow(i);
            println!("Number of rounds: {}", rounds);
            let x0 = Fr::random(rng);
            let y0 = Fr::random(rng);
            let now = Instant::now();
            let (x, y) = minroot(x0, y0, rounds);
            println!("minroot eval: {:.3?}", now.elapsed());

            let now = Instant::now();
            let params = generate_random_parameters(
                MinRoot {
                    x: Fr::random(rng),
                    y: Fr::random(rng),
                    x0: Fr::random(rng),
                    y0: Fr::random(rng),
                    rounds,
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
            let proof = create_random_proof(MinRoot { x, y, x0, y0, rounds }, &params, rng).unwrap();
            println!("create_random_proof: {:.3?}", now.elapsed());

            let now = Instant::now();
            assert!(verify_proof(&pvk, &proof, &[x0, y0]).unwrap());
            println!("verify_proof: {:.3?}", now.elapsed());
            println!();
        }
    }
}
