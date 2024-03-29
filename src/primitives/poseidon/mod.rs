use std::collections::HashSet;

use ark_ff::{PrimeField, One, BigInteger, BitIteratorLE};
use ark_std::{marker::PhantomData, vec::Vec};
use num::{BigUint, Zero, Integer};
use num_prime::nt_funcs::is_prime;

pub mod constraints;
pub mod config;

use config::{ALPHA, R_F, R_P, WIDTH};

#[derive(Clone, Debug)]
pub struct PoseidonParameters<F: PrimeField> {
    full_rounds: usize,
    partial_rounds: usize,
    alpha: u64,
    mds: Vec<Vec<F>>,
    ark: Vec<Vec<F>>,
}

impl<F: PrimeField> Default for PoseidonParameters<F> {
    fn default() -> Self {
        Self::gen(R_F, R_P, ALPHA, WIDTH)
    }
}

impl<F: PrimeField> PoseidonParameters<F> {
    pub fn gen(r_f: usize, r_p: usize, alpha: u64, width: usize) -> Self {
        const FIELD_TYPE: u16 = 1;
        const S_BOX_TYPE: u32 = 0;
        let m: BigUint = F::MODULUS.into();
        let m_bits = F::MODULUS_BIT_SIZE;

        let mut bits = format!(
            "{FIELD_TYPE:02b}{S_BOX_TYPE:04b}{m_bits:012b}{width:012b}{r_f:010b}{r_p:010b}{}",
            "1".repeat(30)
        )
        .chars()
        .map(|i| i == '1')
        .collect::<Vec<_>>();

        let mut round = || -> bool {
            let b = bits[62] ^ bits[51] ^ bits[38] ^ bits[23] ^ bits[13] ^ bits[0];
            bits.remove(0);
            bits.push(b);
            b
        };

        for _ in 0..160 {
            round();
        }

        let mut rng = || -> BigUint {
            (0..m_bits).rev().fold(BigUint::zero(), |mut v, i| loop {
                if round() {
                    v.set_bit(i.into(), round());
                    break v;
                }
                round();
            })
        };

        let round_constants = (0..r_f + r_p)
            .map(|_| {
                (0..width)
                    .map(|_| loop {
                        let r = rng();
                        if r < m {
                            return F::from(r);
                        }
                    })
                    .collect()
            })
            .collect();

        let mds_matrix = loop {
            let v = (0..width * 2).map(|_| F::from(rng())).collect::<Vec<_>>();

            if HashSet::<F>::from_iter(v.clone()).len() == width * 2 {
                let (x, y) = v.split_at(width);
                break x
                    .iter()
                    .map(|i| y.iter().map(|j| i.add(j).inverse()).collect())
                    .collect::<Option<_>>()
                    .unwrap();
            }
        };
        Self { full_rounds: r_f, partial_rounds: r_p, alpha, mds: mds_matrix, ark: round_constants }
    }
}

#[derive(Clone)]
pub struct PoseidonSponge<F: PrimeField> {
    field_phantom: PhantomData<F>,
}

impl<F: PrimeField> PoseidonSponge<F> {
    fn apply_s_box(pp: &PoseidonParameters<F>, state: &mut [F], is_full_round: bool) {
        if is_full_round {
            for elem in state {
                *elem = elem.pow([pp.alpha]);
            }
        } else {
            state[0] = state[0].pow([pp.alpha]);
        }
    }

    fn apply_ark(pp: &PoseidonParameters<F>, state: &mut [F], round_number: usize) {
        for (i, state_elem) in state.iter_mut().enumerate() {
            state_elem.add_assign(&pp.ark[round_number][i]);
        }
    }

    fn apply_mds(pp: &PoseidonParameters<F>, state: &mut [F]) {
        let mut new_state = Vec::new();
        for i in 0..state.len() {
            let mut cur = F::zero();
            for (j, state_elem) in state.iter().enumerate() {
                let term = state_elem.mul(&pp.mds[i][j]);
                cur.add_assign(&term);
            }
            new_state.push(cur);
        }
        state.clone_from_slice(&new_state[..state.len()])
    }

    fn permute(pp: &PoseidonParameters<F>, state: &mut [F]) {
        let full_rounds_over_2 = pp.full_rounds / 2;
        for i in 0..full_rounds_over_2 {
            Self::apply_ark(pp, state, i);
            Self::apply_s_box(pp, state, true);
            Self::apply_mds(pp, state);
        }
        for i in full_rounds_over_2..(full_rounds_over_2 + pp.partial_rounds) {
            Self::apply_ark(pp, state, i);
            Self::apply_s_box(pp, state, false);
            Self::apply_mds(pp, state);
        }
        for i in (full_rounds_over_2 + pp.partial_rounds)..(pp.partial_rounds + pp.full_rounds) {
            Self::apply_ark(pp, state, i);
            Self::apply_s_box(pp, state, true);
            Self::apply_mds(pp, state);
        }
    }
}

pub struct CRH<F: PrimeField> {
    field_phantom: PhantomData<F>,
}

impl<F: PrimeField> CRH<F> {
    pub fn hash(pp: &PoseidonParameters<F>, a: F, b: F, c: F, d: F) -> F {
        let mut state = [F::from(1u128 << 66), a, b, c, d];
        PoseidonSponge::permute(pp, &mut state);
        state[WIDTH - 1]
    }

    pub fn hash_vec(pp: &PoseidonParameters<F>, v: &[F]) -> F {
        assert!(v.len() < WIDTH);
        let mut state = vec![F::from(1u128 << 66)];
        state.extend_from_slice(v);
        state.resize(WIDTH, Default::default());
        PoseidonSponge::permute(pp, &mut state);
        state[WIDTH - 1]
    }
}

pub struct HPrime {
}

impl HPrime {
    pub const EXTENSIONS: [(usize, usize, usize); 3] =
        [(11, 25, 4), (11, 24, 4), (12, 34, 3)];
    pub const OUTPUT_WIDTH: usize = 128;

    fn attempt_pocklington_base(
        &(nonce_bits, random_bits, one_bits): &(usize, usize, usize),
        entropy_source: &mut Vec<bool>,
    ) -> (BigUint, u64) {
        let v = {
            let mut acc = BigUint::zero();
            for i in 0..random_bits {
                acc.set_bit(i as u64, entropy_source.pop().unwrap());
            }
            for i in 0..one_bits {
                acc.set_bit((i + random_bits) as u64, true);
            }
            acc << nonce_bits
        };
        for nonce in (1u64 << (nonce_bits - 1))..(1u64 << nonce_bits) {
            if (nonce & 0b11) == 0b11 {
                let base = &v + nonce;
                if is_prime(&base, None).probably() {
                    return (base, nonce);
                }
            }
        }
        unreachable!()
    }

    fn attempt_pocklington_extension(
        prime: &BigUint,
        &(nonce_bits, random_bits, one_bits): &(usize, usize, usize),
        entropy_source: &mut Vec<bool>,
    ) -> (BigUint, u64) {
        let v = {
            let mut acc = BigUint::zero();
            for i in 0..random_bits {
                acc.set_bit(i as u64, entropy_source.pop().unwrap());
            }
            for i in 0..one_bits {
                acc.set_bit((i + random_bits) as u64, true);
            }
            acc << nonce_bits
        };
        for nonce in (1u64 << (nonce_bits - 1))..(1u64 << nonce_bits) {
            let extension = &v + nonce;
            let number = prime * &extension + BigUint::one();
            let part = BigUint::from(2u8).modpow(&extension, &number);
            if part.modpow(prime, &number).is_one()
                && (&part - BigUint::one()).gcd(&number).is_one()
            {
                return (number, nonce);
            }
        }
        unreachable!()
    }

    pub fn find_hash<F: PrimeField>(
        pp: &PoseidonParameters<F>,
        a: F,
        b: F,
        c: F,
        d: F,
    ) -> (F, Vec<Vec<bool>>) {
        let hash = CRH::hash(pp, a, b, c, d);
        let mut entropy_source = hash.into_bigint().to_bits_le();
        entropy_source.resize(F::MODULUS_BIT_SIZE as usize, false);
        let mut nonces = vec![];
        let (base_prime, base_nonce) =
            Self::attempt_pocklington_base(&Self::EXTENSIONS[0], &mut entropy_source);
        let mut prime = base_prime;
        nonces.push(BitIteratorLE::without_trailing_zeros([base_nonce]).collect());
        for extension in &Self::EXTENSIONS[1..] {
            let ext = Self::attempt_pocklington_extension(&prime, extension, &mut entropy_source);
            prime = ext.0;
            nonces.push(BitIteratorLE::without_trailing_zeros([ext.1]).collect());
        }
        (F::from(prime), nonces)
    }

    pub fn hash<F: PrimeField>(
        pp: &PoseidonParameters<F>,
        a: F,
        b: F,
        c: F,
        d: F,
        nonces: &[Vec<bool>],
    ) -> F {
        let hash = CRH::hash(pp, a, b, c, d);
        let mut entropy_source = hash.into_bigint().to_bits_le();
        entropy_source.resize(F::MODULUS_BIT_SIZE as usize, false);
        let mut extensions =
            Self::EXTENSIONS.iter().zip(nonces).map(|(&(_, random_bits, one_bits), nonce)| {
                BigUint::from_radix_le(
                    &[
                        nonce.iter().map(|&i| i as u8).collect(),
                        entropy_source
                            .drain(entropy_source.len() - random_bits..)
                            .rev()
                            .map(|i| i as u8)
                            .collect(),
                        vec![1; one_bits],
                    ]
                    .concat(),
                    2,
                )
                .unwrap()
            });
        let mut prime = extensions.next().unwrap();
        for extension in extensions {
            assert!(extension < prime);
            prime = prime * extension + BigUint::one();
        }
        F::from(prime)
    }
}
