use ark_ff::{One, PrimeField};
use num::{BigUint, Integer, ToPrimitive};
use num_modular::{ModularPow, ModularUnaryOps};
use num_prime::RandPrime;
use rand::Rng;

use super::poseidon::{config::WIDTH, HPrime, PoseidonParameters, CRH};

pub mod constraints;

pub struct VDF<const T: usize> {
    pub n: BigUint,
    pub n_bits: usize,
}

impl<const T: usize> VDF<T> {
    fn h_prime<F: PrimeField>(
        &self,
        pp: &PoseidonParameters<F>,
        x: &BigUint,
        y: &BigUint,
        alpha: Option<Vec<Vec<bool>>>,
    ) -> (F, Vec<Vec<bool>>) {
        let mut field_elements = [
            x.to_radix_le(2),
            vec![0; self.n_bits - x.bits() as usize],
            y.to_radix_le(2),
            vec![0; self.n_bits - y.bits() as usize],
        ]
        .concat()
        .chunks(F::MODULUS_BIT_SIZE as usize - 1)
        .map(|i| BigUint::from_radix_le(i, 2).map(F::from))
        .collect::<Option<Vec<_>>>()
        .unwrap();
        while field_elements.len() >= WIDTH {
            field_elements = field_elements
                .chunks(WIDTH - 1)
                .map(|chunk| CRH::hash_vec(pp, chunk))
                .collect();
        }
        field_elements.resize(WIDTH - 1, Default::default());
        match alpha {
            Some(alpha) => (
                HPrime::hash(
                    pp,
                    field_elements[0],
                    field_elements[1],
                    field_elements[2],
                    field_elements[3],
                    &alpha,
                ),
                alpha,
            ),
            None => HPrime::find_hash(
                pp,
                field_elements[0],
                field_elements[1],
                field_elements[2],
                field_elements[3],
            ),
        }
    }

    pub fn new<R: Rng>(rng: &mut R, n_bits: usize) -> Self {
        let p: BigUint = rng.gen_prime_exact(n_bits >> 1, None);
        let q: BigUint = rng.gen_prime_exact(n_bits >> 1, None);
        Self { n: p * q, n_bits }
    }

    pub fn eval_optimized<F: PrimeField>(
        &self,
        pp: &PoseidonParameters<F>,
        x: BigUint,
    ) -> (BigUint, Vec<Vec<bool>>, BigUint) {
        let k = T.ilog2() as usize / 2;

        let mut y = x.clone();
        let mut powers = vec![];
        for i in 0..T {
            if i.is_multiple_of(&k) {
                powers.push(y.clone());
            }
            y = y.sqm(&self.n);
        }

        let (l, alpha) = self.h_prime(pp, &x, &y, None);
        let l: BigUint = l.into();

        let k1 = k / 2;
        let k0 = k - k1;

        let mut pi = BigUint::one();

        let mut ys = vec![BigUint::one(); 1 << k];
        for i in (0..T).step_by(k) {
            if i + k > T {
                continue;
            }
            let b = ((BigUint::from(2u8).powm(BigUint::from(T - i - k), &l) << k) / &l)
                .to_usize()
                .unwrap();
            ys[b] = &ys[b] * &powers[i / k] % &self.n;
        }

        for b1 in 0..1 << k1 {
            let mut z = BigUint::one();
            for b0 in 0..1 << k0 {
                z = z * &ys[(b1 << k0) + b0] % &self.n;
            }
            pi = pi * z.powm(BigUint::from(b1 << k0), &self.n) % &self.n;
        }

        for b0 in 0..1 << k0 {
            let mut z = BigUint::one();
            for b1 in 0..1 << k1 {
                z = z * &ys[(b1 << k0) + b0] % &self.n;
            }
            pi = pi * z.powm(BigUint::from(b0), &self.n) % &self.n;
        }

        (y, alpha, pi)
    }

    pub fn eval<F: PrimeField>(
        &self,
        pp: &PoseidonParameters<F>,
        x: BigUint,
    ) -> (BigUint, Vec<Vec<bool>>, BigUint) {
        let mut y = x.clone();
        for _ in 0..T {
            y = y.sqm(&self.n);
        }
        let (l, alpha) = self.h_prime(pp, &x, &y, None);
        let l: BigUint = l.into();
        let mut pi = BigUint::one();
        let mut r = BigUint::one();
        for _ in 0..T {
            let b = &r + &r >= l;
            if b {
                r = &r + &r - &l;
            } else {
                r = &r + &r;
            }
            pi = pi.sqm(&self.n);
            if b {
                pi = pi * &x % &self.n;
            }
        }
        (y, alpha, pi)
    }

    pub fn verify<F: PrimeField>(
        &self,
        pp: &PoseidonParameters<F>,
        x: BigUint,
        y: BigUint,
        alpha: Vec<Vec<bool>>,
        pi: BigUint,
    ) -> bool {
        let (l, _) = self.h_prime(pp, &x, &y, Some(alpha));
        let l: BigUint = l.into();
        let r = (BigUint::one() << T) % &l;
        y == x.powm(&r, &self.n) * pi.powm(&l, &self.n) % &self.n
    }
}

#[cfg(test)]
mod tests {
    use std::time::Instant;

    use super::*;
    use ark_bls12_381::Fr;
    use num::bigint::RandBigInt;
    use rand::thread_rng;

    #[test]
    fn test() {
        let pp = PoseidonParameters::<Fr>::default();
        let rng = &mut thread_rng();
        let vdf = VDF::<{ 1 << 23 }>::new(rng, 2048);
        let x = rng.gen_biguint_below(&vdf.n);
        let now = Instant::now();
        let r1 = vdf.eval(&pp, x.clone());
        println!("{:?}", now.elapsed());
        let now = Instant::now();
        let r2 = vdf.eval_optimized(&pp, x.clone());
        println!("{:?}", now.elapsed());
        assert_eq!(r1, r2);
        let (y, alpha, pi) = r1;
        assert!(vdf.verify(&pp, x, y, alpha, pi));
    }
}
