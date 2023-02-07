use ark_ff::{One, PrimeField};
use ark_r1cs_std::{fields::fp::FpVar, prelude::*};
use ark_relations::r1cs::SynthesisError;
use ark_std::{marker::PhantomData, vec::Vec};
use num::BigUint;

use crate::primitives::{
    bn::{BigUintVar, BitsVar},
    poseidon::config::WIDTH,
};

use super::{HPrime, PoseidonParameters};

pub struct CRHGadget<F: PrimeField> {
    field_phantom: PhantomData<F>,
}

impl<F: PrimeField> CRHGadget<F> {
    pub fn hash(
        pp: &PoseidonParameters<F>,
        a: FpVar<F>,
        b: FpVar<F>,
        c: FpVar<F>,
        d: FpVar<F>,
    ) -> Result<FpVar<F>, SynthesisError> {
        let mut state = vec![FpVar::Constant(F::from(1u128 << 66)), a, b, c, d];
        PoseidonSpongeGadget::permute(pp, &mut state)?;
        Ok(state.pop().unwrap())
    }

    pub fn hash_vec(
        pp: &PoseidonParameters<F>,
        inputs: Vec<FpVar<F>>,
    ) -> Result<FpVar<F>, SynthesisError> {
        assert!(inputs.len() < WIDTH);
        let mut state = vec![FpVar::Constant(F::from(1u128 << 66))];
        state.extend(inputs);
        state.resize(WIDTH, FpVar::zero());
        PoseidonSpongeGadget::permute(pp, &mut state)?;
        Ok(state.pop().unwrap())
    }
}

#[derive(Clone)]
pub struct PoseidonSpongeGadget<F: PrimeField> {
    field_phantom: PhantomData<F>,
}

impl<F: PrimeField> PoseidonSpongeGadget<F> {
    fn apply_s_box(
        pp: &PoseidonParameters<F>,
        state: &mut [FpVar<F>],
        is_full_round: bool,
    ) -> Result<(), SynthesisError> {
        if is_full_round {
            for state_item in state.iter_mut() {
                *state_item = state_item.pow_by_constant([pp.alpha])?;
            }
        } else {
            state[0] = state[0].pow_by_constant([pp.alpha])?;
        }

        Ok(())
    }

    fn apply_ark(pp: &PoseidonParameters<F>, state: &mut [FpVar<F>], round_number: usize) {
        for (i, state_elem) in state.iter_mut().enumerate() {
            *state_elem += pp.ark[round_number][i];
        }
    }

    fn apply_mds(pp: &PoseidonParameters<F>, state: &mut [FpVar<F>]) {
        let mut new_state = Vec::new();
        let zero = FpVar::<F>::zero();
        for i in 0..state.len() {
            let mut cur = zero.clone();
            for (j, state_elem) in state.iter().enumerate() {
                let term = state_elem * pp.mds[i][j];
                cur += &term;
            }
            new_state.push(cur);
        }
        state.clone_from_slice(&new_state[..state.len()]);
    }

    fn permute(pp: &PoseidonParameters<F>, state: &mut [FpVar<F>]) -> Result<(), SynthesisError> {
        let full_rounds_over_2 = pp.full_rounds / 2;
        for i in 0..full_rounds_over_2 {
            Self::apply_ark(pp, state, i);
            Self::apply_s_box(pp, state, true)?;
            Self::apply_mds(pp, state);
        }
        for i in full_rounds_over_2..(full_rounds_over_2 + pp.partial_rounds) {
            Self::apply_ark(pp, state, i);
            Self::apply_s_box(pp, state, false)?;
            Self::apply_mds(pp, state);
        }
        for i in (full_rounds_over_2 + pp.partial_rounds)..(pp.partial_rounds + pp.full_rounds) {
            Self::apply_ark(pp, state, i);
            Self::apply_s_box(pp, state, true)?;
            Self::apply_mds(pp, state);
        }

        Ok(())
    }
}

pub struct HPrimeGadget {}

impl HPrimeGadget {
    pub fn to_prime<F: PrimeField, const W: usize>(
        hash: FpVar<F>,
        nonces: &[Vec<Boolean<F>>],
    ) -> Result<Vec<Boolean<F>>, SynthesisError> {
        let extensions = HPrime::EXTENSIONS;
        let mut entropy_source = hash.to_bits_le()?;

        let mut prime_bits = [
            nonces[0].clone(),
            entropy_source
                .drain(entropy_source.len() - extensions[0].1..)
                .rev()
                .collect(),
            vec![Boolean::TRUE; extensions[0].2],
        ]
        .concat();
        let mut prime = BigUintVar::<F, W>(prime_bits.chunks(W).map(BitsVar::from).collect());
        prime_bits[0].enforce_equal(&Boolean::TRUE)?;
        prime_bits[1].enforce_equal(&Boolean::TRUE)?;
        for b in [2u32, 13, 23, 1662803] {
            let mut pow = BigUintVar::constant(BigUint::from(b), prime_bits.len())?.powm(
                &prime_bits[1..],
                &prime,
                &(BigUint::one() << (prime_bits.len() - 1)),
            )?;
            let mut is_one = pow.0[0].0.is_one()?;
            for i in 1..pow.0.len() {
                is_one = is_one.and(&pow.0[i].0.is_zero()?)?;
            }
            pow.0[0].0 += FpVar::one();
            let is_neg_one = prime.is_eq(&pow)?;
            is_one.or(&is_neg_one)?.enforce_equal(&Boolean::TRUE)?;
        }

        for (&(_, random_bits, one_bits), nonce) in extensions[1..].iter().zip(&nonces[1..]) {
            let extension_bits = [
                nonce.clone(),
                entropy_source
                    .drain(entropy_source.len() - random_bits..)
                    .rev()
                    .collect(),
                vec![Boolean::TRUE; one_bits],
            ]
            .concat();
            let extension = BigUintVar(extension_bits.chunks(W).map(BitsVar::from).collect());

            let n = extension
                .mul_no_carry(&prime)?
                .add_no_carry(&BigUintVar::constant(BigUint::one(), 1)?)
                .align()?;
            let base = BigUintVar::constant(BigUint::from(2u8), n.ubound().bits() as usize)?;
            let part = base.powm(
                &extension_bits,
                &n,
                &(BigUint::one() << (extension_bits.len() + prime_bits.len() - 1)),
            )?;
            part.sub_one_enforce_coprime(&n)?;

            let power = part.powm(
                &prime_bits,
                &n,
                &(BigUint::one() << (extension_bits.len() + prime_bits.len() - 1)),
            )?;
            power.0[0].0.enforce_equal(&FpVar::one())?;
            for i in 1..power.0.len() {
                power.0[i].0.enforce_equal(&FpVar::zero())?;
            }

            prime = n;
            prime_bits = prime.to_bits_le()?;
        }
        Ok(prime_bits)
    }

    pub fn hash<F: PrimeField, const W: usize>(
        pp: &PoseidonParameters<F>,
        a: FpVar<F>,
        b: FpVar<F>,
        c: FpVar<F>,
        d: FpVar<F>,
        nonces: &[Vec<Boolean<F>>],
    ) -> Result<Vec<Boolean<F>>, SynthesisError> {
        let hash = CRHGadget::hash(pp, a, b, c, d)?;
        Self::to_prime::<F, W>(hash, nonces)
    }
}

#[cfg(test)]
mod test {

    use std::{error::Error, time::Instant};

    use ark_bls12_381::{Bls12_381, Fr};
    use ark_groth16::{
        create_random_proof, generate_random_parameters, prepare_verifying_key, verify_proof,
    };
    use ark_r1cs_std::{alloc::AllocVar, R1CSVar};
    use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystem, ConstraintSystemRef};
    use ark_std::UniformRand;
    use num_prime::nt_funcs::is_prime;
    use rand::thread_rng;

    use crate::primitives::poseidon::{
        config::{ALPHA, R_F, R_P, WIDTH},
        CRH,
    };

    use super::*;

    #[test]
    fn test_hash() {
        let rng = &mut ark_std::test_rng();

        let a = Fr::rand(rng);
        let b = Fr::rand(rng);
        let c = Fr::rand(rng);
        let d = Fr::rand(rng);

        let params = PoseidonParameters::gen(R_F, R_P, ALPHA, WIDTH);

        let h = CRH::hash(&params, a, b, c, d);

        let cs = ConstraintSystem::new_ref();

        let a_var = FpVar::new_witness(cs.clone(), || Ok(a)).unwrap();
        let b_var = FpVar::new_witness(cs.clone(), || Ok(b)).unwrap();
        let c_var = FpVar::new_witness(cs.clone(), || Ok(c)).unwrap();
        let d_var = FpVar::new_witness(cs, || Ok(d)).unwrap();

        let h_var = CRHGadget::hash(&params, a_var, b_var, c_var, d_var).unwrap();

        assert_eq!(h, h_var.value().unwrap());
    }

    const W: usize = 32;

    #[test]
    fn test_h_prime() -> Result<(), Box<dyn Error>> {
        let rng = &mut thread_rng();

        let a = Fr::rand(rng);
        let b = Fr::rand(rng);
        let c = Fr::rand(rng);
        let d = Fr::rand(rng);

        let pp = PoseidonParameters::default();

        let (prime, nonces) = HPrime::find_hash(&pp, a, b, c, d);
        println!("{}", prime);
        let prime_bn: BigUint = prime.into();
        assert!(is_prime(&prime_bn, None).probably());
        assert_eq!(prime, HPrime::hash(&pp, a, b, c, d, &nonces));

        let cs = ConstraintSystem::<Fr>::new_ref();
        let a = FpVar::<Fr>::new_witness(cs.clone(), || Ok(a))?;
        let b = FpVar::<Fr>::new_witness(cs.clone(), || Ok(b))?;
        let c = FpVar::<Fr>::new_witness(cs.clone(), || Ok(c))?;
        let d = FpVar::<Fr>::new_witness(cs.clone(), || Ok(d))?;
        let nonces = nonces
            .into_iter()
            .map(|nonce| Vec::new_witness(cs.clone(), || Ok(nonce)))
            .collect::<Result<Vec<_>, _>>()?;
        let x = HPrimeGadget::hash::<Fr, W>(&pp, a, b, c, d, &nonces)?;
        println!("{}", Boolean::le_bits_to_fp_var(&x)?.value()?);
        assert!(cs.is_satisfied()?);
        println!("{}", cs.num_constraints());
        Ok(())
    }

    struct TestCircuit {
        a: Fr,
        b: Fr,
        c: Fr,
        d: Fr,
        h: Fr,
        nonces: Vec<Vec<bool>>,
    }

    impl ConstraintSynthesizer<Fr> for TestCircuit {
        fn generate_constraints(
            self,
            cs: ConstraintSystemRef<Fr>,
        ) -> ark_relations::r1cs::Result<()> {
            let a = FpVar::<Fr>::new_witness(cs.clone(), || Ok(self.a))?;
            let b = FpVar::<Fr>::new_witness(cs.clone(), || Ok(self.b))?;
            let c = FpVar::<Fr>::new_witness(cs.clone(), || Ok(self.c))?;
            let d = FpVar::<Fr>::new_witness(cs.clone(), || Ok(self.d))?;
            let nonces = self
                .nonces
                .into_iter()
                .map(|nonce| Vec::new_witness(cs.clone(), || Ok(nonce)))
                .collect::<Result<Vec<_>, _>>()?;
            Boolean::le_bits_to_fp_var(&HPrimeGadget::hash::<Fr, W>(
                &PoseidonParameters::default(),
                a,
                b,
                c,
                d,
                &nonces,
            )?)?
            .enforce_equal(&FpVar::new_input(cs, || Ok(self.h))?)?;
            Ok(())
        }
    }

    #[test]
    fn test() -> Result<(), Box<dyn Error>> {
        let rng = &mut thread_rng();
        let a = Fr::rand(rng);
        let b = Fr::rand(rng);
        let c = Fr::rand(rng);
        let d = Fr::rand(rng);

        let pp = PoseidonParameters::default();
        let (prime, nonces) = HPrime::find_hash(&pp, a, b, c, d);

        let params = generate_random_parameters::<Bls12_381, _, _>(
            TestCircuit {
                a: Default::default(),
                b: Default::default(),
                c: Default::default(),
                d: Default::default(),
                h: Default::default(),
                nonces: HPrime::EXTENSIONS
                    .iter()
                    .map(|(n, _, _)| vec![false; *n])
                    .collect(),
            },
            rng,
        )
        .unwrap();

        let pvk = prepare_verifying_key(&params.vk);
        let now = Instant::now();
        let proof = create_random_proof(
            TestCircuit {
                a,
                b,
                c,
                d,
                h: prime,
                nonces,
            },
            &params,
            rng,
        )
        .unwrap();
        println!("proof time: {:?}", now.elapsed());

        assert!(verify_proof(&pvk, &proof, &[prime]).unwrap());
        Ok(())
    }
}
