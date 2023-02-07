use ark_ff::{Field, One};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::rand::Rng;
use ark_std::{end_timer, start_timer};
use digest::Digest;
use std::{convert::TryInto, marker::PhantomData};

use super::dh_commitments::DoublyHomomorphicCommitment;
use super::inner_product::InnerProduct;
use super::{mul_helper, Error, HashMarshaller, InnerProductArgumentError};

use rayon::prelude::*;

pub struct GIPA<LMC, RMC, IPC> {
    _left_commitment: PhantomData<LMC>,
    _right_commitment: PhantomData<RMC>,
    _inner_product_commitment: PhantomData<IPC>,
}

#[derive(CanonicalSerialize, CanonicalDeserialize)]
pub struct GIPAProof<LMC, RMC, IPC>
where
    LMC: DoublyHomomorphicCommitment,
    RMC: DoublyHomomorphicCommitment<Scalar = LMC::Scalar>,
    IPC: DoublyHomomorphicCommitment<Scalar = LMC::Scalar>,
{
    pub(crate) r_commitment_steps: Vec<(
        (LMC::Output, RMC::Output, IPC::Output),
        (LMC::Output, RMC::Output, IPC::Output),
    )>,
    pub(crate) r_base: (LMC::Message, RMC::Message),
}

pub struct GIPAAux<LMC, RMC, IPC>
where
    LMC: DoublyHomomorphicCommitment,
    RMC: DoublyHomomorphicCommitment<Scalar = LMC::Scalar>,
    IPC: DoublyHomomorphicCommitment<Scalar = LMC::Scalar>,
{
    pub(crate) r_transcript: Vec<LMC::Scalar>,
    pub(crate) ck_base: (LMC::Key, RMC::Key),
    _gipa: PhantomData<GIPA<LMC, RMC, IPC>>,
}

//TODO: Can extend GIPA to support "identity commitments" in addition to "compact commitments", i.e. for SIPP

impl<LMC, RMC, IPC> GIPA<LMC, RMC, IPC>
where
    LMC: DoublyHomomorphicCommitment,
    RMC: DoublyHomomorphicCommitment<Scalar = LMC::Scalar>,
    IPC: DoublyHomomorphicCommitment<Scalar = LMC::Scalar>,
{
    pub fn setup<R: Rng>(
        rng: &mut R,
        size: usize,
    ) -> Result<(Vec<LMC::Key>, Vec<RMC::Key>, IPC::Key), Error> {
        Ok((
            LMC::setup(rng, size)?,
            RMC::setup(rng, size)?,
            IPC::setup(rng, 1)?.pop().unwrap(),
        ))
    }

    pub fn prove<
        D: Digest,
        IP: InnerProduct<
            LeftMessage = LMC::Message,
            RightMessage = RMC::Message,
            Output = IPC::Message,
        >,
    >(
        values: (&[LMC::Message], &[RMC::Message], &IPC::Message),
        ck: (&[LMC::Key], &[RMC::Key], &IPC::Key),
        com: (&LMC::Output, &RMC::Output, &IPC::Output),
    ) -> Result<GIPAProof<LMC, RMC, IPC>, Error> {
        if IP::inner_product(values.0, values.1)? != values.2.clone() {
            return Err(Box::new(InnerProductArgumentError::InnerProductInvalid));
        }
        if values.0.len().count_ones() != 1 {
            // Power of 2 length
            return Err(Box::new(InnerProductArgumentError::MessageLengthInvalid(
                values.0.len(),
                values.1.len(),
            )));
        }
        if !(LMC::verify(ck.0, values.0, com.0)?
            && RMC::verify(ck.1, values.1, com.1)?
            && IPC::verify(&vec![ck.2.clone()], &vec![values.2.clone()], com.2)?)
        {
            return Err(Box::new(InnerProductArgumentError::InnerProductInvalid));
        }

        let (proof, _) =
            Self::prove_with_aux::<D, IP>((values.0, values.1), (ck.0, ck.1, &vec![ck.2.clone()]))?;
        Ok(proof)
    }

    pub fn verify<
        D: Digest,
        IP: InnerProduct<
            LeftMessage = LMC::Message,
            RightMessage = RMC::Message,
            Output = IPC::Message,
        >,
    >(
        ck: (&[LMC::Key], &[RMC::Key], &IPC::Key),
        com: (&LMC::Output, &RMC::Output, &IPC::Output),
        proof: &GIPAProof<LMC, RMC, IPC>,
    ) -> Result<bool, Error> {
        if ck.0.len().count_ones() != 1 || ck.0.len() != ck.1.len() {
            // Power of 2 length
            return Err(Box::new(InnerProductArgumentError::MessageLengthInvalid(
                ck.0.len(),
                ck.1.len(),
            )));
        }
        // Calculate base commitment and transcript
        let (base_com, transcript) = Self::_compute_recursive_challenges::<D>(
            (com.0.clone(), com.1.clone(), com.2.clone()),
            proof,
        )?;
        // Calculate base commitment keys
        let (ck_a_base, ck_b_base) = Self::_compute_final_commitment_keys(ck, &transcript)?;
        // Verify base commitment
        Self::_verify_base_commitment::<IP>(
            (&ck_a_base, &ck_b_base, &vec![ck.2.clone()]),
            base_com,
            proof,
        )
    }

    pub fn prove_with_aux<
        D: Digest,
        IP: InnerProduct<
            LeftMessage = LMC::Message,
            RightMessage = RMC::Message,
            Output = IPC::Message,
        >,
    >(
        values: (&[LMC::Message], &[RMC::Message]),
        ck: (&[LMC::Key], &[RMC::Key], &[IPC::Key]),
    ) -> Result<(GIPAProof<LMC, RMC, IPC>, GIPAAux<LMC, RMC, IPC>), Error> {
        let (m_a, m_b) = values;
        let (ck_a, ck_b, ck_t) = ck;
        Self::_prove::<D, IP>(
            (m_a.to_vec(), m_b.to_vec()),
            (ck_a.to_vec(), ck_b.to_vec(), ck_t.to_vec()),
        )
    }

    // Returns vector of recursive commitments and transcripts in reverse order
    fn _prove<
        D: Digest,
        IP: InnerProduct<
            LeftMessage = LMC::Message,
            RightMessage = RMC::Message,
            Output = IPC::Message,
        >,
    >(
        values: (Vec<LMC::Message>, Vec<RMC::Message>),
        ck: (Vec<LMC::Key>, Vec<RMC::Key>, Vec<IPC::Key>),
    ) -> Result<(GIPAProof<LMC, RMC, IPC>, GIPAAux<LMC, RMC, IPC>), Error> {
        let (mut m_a, mut m_b) = values;
        let (mut ck_a, mut ck_b, ck_t) = ck;
        let mut r_commitment_steps = Vec::new();
        let mut r_transcript = Vec::<LMC::Scalar>::new();
        assert!(m_a.len().is_power_of_two());
        let (m_base, ck_base) = 'recurse: loop {
            if m_a.len() == 1 {
                // base case
                break 'recurse (
                    (m_a[0].clone(), m_b[0].clone()),
                    (ck_a[0].clone(), ck_b[0].clone()),
                );
            } else {
                let recurse = start_timer!(|| format!("Recurse round size {}", m_a.len()));
                // recursive step
                // Recurse with problem of half size
                let split = m_a.len() / 2;

                let m_a_1 = &m_a[split..];
                let m_a_2 = &m_a[..split];
                let ck_a_1 = &ck_a[..split];
                let ck_a_2 = &ck_a[split..];

                let m_b_1 = &m_b[..split];
                let m_b_2 = &m_b[split..];
                let ck_b_1 = &ck_b[split..];
                let ck_b_2 = &ck_b[..split];

                let cl = start_timer!(|| "Commit L");
                let com_1 = (
                    LMC::commit(ck_a_1, m_a_1)?,
                    RMC::commit(ck_b_1, m_b_1)?,
                    IPC::commit(&ck_t, &vec![IP::inner_product(m_a_1, m_b_1)?])?,
                );
                end_timer!(cl);
                let cr = start_timer!(|| "Commit R");
                let com_2 = (
                    LMC::commit(ck_a_2, m_a_2)?,
                    RMC::commit(ck_b_2, m_b_2)?,
                    IPC::commit(&ck_t, &vec![IP::inner_product(m_a_2, m_b_2)?])?,
                );
                end_timer!(cr);

                // Fiat-Shamir challenge
                let mut counter_nonce: usize = 0;
                let default_transcript = Default::default();
                let transcript = r_transcript.last().unwrap_or(&default_transcript);
                let (c, c_inv) = 'challenge: loop {
                    let mut hasher = D::new();
                    hasher.update(&counter_nonce.to_be_bytes());
                    transcript.serialize_compressed(HashMarshaller(&mut hasher))?;
                    com_1.serialize_compressed(HashMarshaller(&mut hasher))?;
                    com_2.serialize_compressed(HashMarshaller(&mut hasher))?;
                    let c: LMC::Scalar = u128::from_be_bytes(
                        hasher.finalize().as_slice()[0..16].try_into().unwrap(),
                    )
                    .into();
                    if let Some(c_inv) = c.inverse() {
                        // Optimization for multiexponentiation to rescale G2 elements with 128-bit challenge
                        // Swap 'c' and 'c_inv' since can't control bit size of c_inv
                        break 'challenge (c_inv, c);
                    }
                    counter_nonce += 1;
                };

                // Set up values for next step of recursion
                let rescale_m1 = start_timer!(|| "Rescale M1");
                m_a = m_a_1
                    .par_iter()
                    .map(|a| mul_helper(a, &c))
                    .zip(m_a_2)
                    .map(|(a_1, a_2)| a_1 + a_2.clone())
                    .collect::<Vec<LMC::Message>>();
                end_timer!(rescale_m1);

                let rescale_m2 = start_timer!(|| "Rescale M2");
                m_b = m_b_2
                    .par_iter()
                    .map(|b| mul_helper(b, &c_inv))
                    .zip(m_b_1)
                    .map(|(b_1, b_2)| b_1 + b_2.clone())
                    .collect::<Vec<RMC::Message>>();
                end_timer!(rescale_m2);

                let rescale_ck1 = start_timer!(|| "Rescale CK1");
                ck_a = ck_a_2
                    .par_iter()
                    .map(|a| mul_helper(a, &c_inv))
                    .zip(ck_a_1)
                    .map(|(a_1, a_2)| a_1 + a_2.clone())
                    .collect::<Vec<LMC::Key>>();
                end_timer!(rescale_ck1);

                let rescale_ck2 = start_timer!(|| "Rescale CK2");
                ck_b = ck_b_1
                    .par_iter()
                    .map(|b| mul_helper(b, &c))
                    .zip(ck_b_2)
                    .map(|(b_1, b_2)| b_1 + b_2.clone())
                    .collect::<Vec<RMC::Key>>();
                end_timer!(rescale_ck2);

                r_commitment_steps.push((com_1, com_2));
                r_transcript.push(c);
                end_timer!(recurse);
            }
        };
        r_transcript.reverse();
        r_commitment_steps.reverse();
        Ok((
            GIPAProof {
                r_commitment_steps,
                r_base: m_base,
            },
            GIPAAux {
                r_transcript,
                ck_base,
                _gipa: PhantomData,
            },
        ))
    }

    // Helper function used to calculate recursive challenges from proof execution (transcript in reverse)
    pub fn verify_recursive_challenge_transcript<D: Digest>(
        com: (&LMC::Output, &RMC::Output, &IPC::Output),
        proof: &GIPAProof<LMC, RMC, IPC>,
    ) -> Result<((LMC::Output, RMC::Output, IPC::Output), Vec<LMC::Scalar>), Error> {
        Self::_compute_recursive_challenges::<D>(
            (com.0.clone(), com.1.clone(), com.2.clone()),
            proof,
        )
    }

    fn _compute_recursive_challenges<D: Digest>(
        com: (LMC::Output, RMC::Output, IPC::Output),
        proof: &GIPAProof<LMC, RMC, IPC>,
    ) -> Result<((LMC::Output, RMC::Output, IPC::Output), Vec<LMC::Scalar>), Error> {
        let (mut com_a, mut com_b, mut com_t) = com;
        let mut r_transcript: Vec<LMC::Scalar> = vec![];
        for (com_1, com_2) in proof.r_commitment_steps.iter().rev() {
            // Fiat-Shamir challenge
            let mut counter_nonce: usize = 0;
            let default_transcript = Default::default();
            let transcript = r_transcript.last().unwrap_or(&default_transcript);
            let (c, c_inv) = 'challenge: loop {
                let mut hasher = D::new();
                hasher.update(&counter_nonce.to_be_bytes());
                transcript.serialize_compressed(HashMarshaller(&mut hasher))?;
                com_1.serialize_compressed(HashMarshaller(&mut hasher))?;
                com_2.serialize_compressed(HashMarshaller(&mut hasher))?;
                let c: LMC::Scalar =
                    u128::from_be_bytes(hasher.finalize().as_slice()[0..16].try_into().unwrap())
                        .into();
                if let Some(c_inv) = c.inverse() {
                    // Optimization for multiexponentiation to rescale G2 elements with 128-bit challenge
                    // Swap 'c' and 'c_inv' since can't control bit size of c_inv
                    break 'challenge (c_inv, c);
                }
                counter_nonce += 1;
            };

            com_a = mul_helper(&com_1.0, &c) + com_a.clone() + mul_helper(&com_2.0, &c_inv);
            com_b = mul_helper(&com_1.1, &c) + com_b.clone() + mul_helper(&com_2.1, &c_inv);
            com_t = mul_helper(&com_1.2, &c) + com_t.clone() + mul_helper(&com_2.2, &c_inv);

            r_transcript.push(c);
        }
        r_transcript.reverse();
        Ok(((com_a, com_b, com_t), r_transcript))
    }

    pub(crate) fn _compute_final_commitment_keys(
        ck: (&[LMC::Key], &[RMC::Key], &IPC::Key),
        transcript: &Vec<LMC::Scalar>,
    ) -> Result<(LMC::Key, RMC::Key), Error> {
        // Calculate base commitment keys
        let (ck_a, ck_b, _) = ck;
        assert!(ck_a.len().is_power_of_two());

        let mut ck_a_agg_challenge_exponents = vec![LMC::Scalar::one()];
        let mut ck_b_agg_challenge_exponents = vec![LMC::Scalar::one()];
        for (i, c) in transcript.iter().enumerate() {
            let c_inv = c.inverse().unwrap();
            for j in 0..(2_usize).pow(i as u32) {
                ck_a_agg_challenge_exponents.push(ck_a_agg_challenge_exponents[j] * &c_inv);
                ck_b_agg_challenge_exponents.push(ck_b_agg_challenge_exponents[j] * c);
            }
        }
        assert_eq!(ck_a_agg_challenge_exponents.len(), ck_a.len());
        //TODO: Optimization: Use VariableMSM multiexponentiation
        let ck_a_base_init = mul_helper(&ck_a[0], &ck_a_agg_challenge_exponents[0]);
        let ck_a_base = ck_a[1..]
            .iter()
            .zip(&ck_a_agg_challenge_exponents[1..])
            .map(|(g, x)| mul_helper(g, &x))
            .fold(ck_a_base_init, |sum, x| sum + x);
        //.reduce(|| ck_a_base_init.clone(), |sum, x| sum + x);
        let ck_b_base_init = mul_helper(&ck_b[0], &ck_b_agg_challenge_exponents[0]);
        let ck_b_base = ck_b[1..]
            .iter()
            .zip(&ck_b_agg_challenge_exponents[1..])
            .map(|(g, x)| mul_helper(g, &x))
            .fold(ck_b_base_init, |sum, x| sum + x);
        //.reduce(|| ck_b_base_init.clone(), |sum, x| sum + x);
        Ok((ck_a_base, ck_b_base))
    }

    pub(crate) fn _verify_base_commitment<
        IP: InnerProduct<
            LeftMessage = LMC::Message,
            RightMessage = RMC::Message,
            Output = IPC::Message,
        >,
    >(
        base_ck: (&LMC::Key, &RMC::Key, &Vec<IPC::Key>),
        base_com: (LMC::Output, RMC::Output, IPC::Output),
        proof: &GIPAProof<LMC, RMC, IPC>,
    ) -> Result<bool, Error> {
        let (com_a, com_b, com_t) = base_com;
        let (ck_a_base, ck_b_base, ck_t) = base_ck;
        let a_base = vec![proof.r_base.0.clone()];
        let b_base = vec![proof.r_base.1.clone()];
        let t_base = vec![IP::inner_product(&a_base, &b_base)?];

        Ok(LMC::verify(&vec![ck_a_base.clone()], &a_base, &com_a)?
            && RMC::verify(&vec![ck_b_base.clone()], &b_base, &com_b)?
            && IPC::verify(&ck_t, &t_base, &com_t)?)
    }
}

impl<LMC, RMC, IPC> Clone for GIPAProof<LMC, RMC, IPC>
where
    LMC: DoublyHomomorphicCommitment,
    RMC: DoublyHomomorphicCommitment<Scalar = LMC::Scalar>,
    IPC: DoublyHomomorphicCommitment<Scalar = LMC::Scalar>,
{
    fn clone(&self) -> Self {
        GIPAProof {
            r_commitment_steps: self.r_commitment_steps.clone(),
            r_base: self.r_base.clone(),
        }
    }
}
