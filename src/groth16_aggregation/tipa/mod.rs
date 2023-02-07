use ark_ec::pairing::Pairing;
use ark_ec::scalar_mul::fixed_base::FixedBase;
use ark_ec::{CurveGroup, Group};
use ark_ff::{Field, One, PrimeField, UniformRand};
use ark_poly::polynomial::univariate::DensePolynomial;
use ark_poly::DenseUVPolynomial;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::rand::Rng;
use ark_std::{end_timer, start_timer};
use digest::Digest;
use std::marker::PhantomData;

use super::dh_commitments::{AFGHOCommitmentG1, AFGHOCommitmentG2, DoublyHomomorphicCommitment};
use super::inner_product::{InnerProduct, MultiexponentiationInnerProduct};
use super::HashMarshaller;
use super::{
    gipa::{GIPAProof, GIPA},
    Error,
};

pub mod structured_scalar_message;

//TODO: Could generalize: Don't need TIPA over G1 and G2, would work with G1 and G1 or over different pairing s
pub trait TIPACompatibleSetup {}

impl<P: Pairing> TIPACompatibleSetup for AFGHOCommitmentG1<P> {}
impl<P: Pairing> TIPACompatibleSetup for AFGHOCommitmentG2<P> {}

//TODO: May need to add "reverse" MultiexponentiationInnerProduct to allow for MIP with G2 messages (because TIP hard-coded G1 left and G2 right)
pub struct TIPA<IP, LMC, RMC, IPC, P, D> {
    _inner_product: PhantomData<IP>,
    _left_commitment: PhantomData<LMC>,
    _right_commitment: PhantomData<RMC>,
    _inner_product_commitment: PhantomData<IPC>,
    _pair: PhantomData<P>,
    _digest: PhantomData<D>,
}

#[derive(CanonicalSerialize, CanonicalDeserialize)]
pub struct TIPAProof<LMC, RMC, IPC, P>
where
    P: Pairing,
    LMC: DoublyHomomorphicCommitment + TIPACompatibleSetup,
    RMC: DoublyHomomorphicCommitment<Scalar = LMC::Scalar> + TIPACompatibleSetup,
    IPC: DoublyHomomorphicCommitment<Scalar = LMC::Scalar>,
{
    gipa_proof: GIPAProof<LMC, RMC, IPC>,
    final_ck: (LMC::Key, RMC::Key),
    final_ck_proof: (P::G2, P::G1),
    _pair: PhantomData<P>,
}

impl<LMC, RMC, IPC, P> Clone for TIPAProof<LMC, RMC, IPC, P>
where
    P: Pairing,
    LMC: DoublyHomomorphicCommitment + TIPACompatibleSetup,
    RMC: DoublyHomomorphicCommitment<Scalar = LMC::Scalar> + TIPACompatibleSetup,
    IPC: DoublyHomomorphicCommitment<Scalar = LMC::Scalar>,
{
    fn clone(&self) -> Self {
        Self {
            gipa_proof: self.gipa_proof.clone(),
            final_ck: self.final_ck.clone(),
            final_ck_proof: self.final_ck_proof.clone(),
            _pair: PhantomData,
        }
    }
}

#[derive(Clone)]
pub struct SRS<P: Pairing> {
    pub g_alpha_powers: Vec<P::G1>,
    pub h_beta_powers: Vec<P::G2>,
    pub g_beta: P::G1,
    pub h_alpha: P::G2,
}

#[derive(Clone)]
pub struct VerifierSRS<P: Pairing> {
    pub g: P::G1,
    pub h: P::G2,
    pub g_beta: P::G1,
    pub h_alpha: P::G2,
}

//TODO: Change SRS to return reference iterator - requires changes to TIPA and GIPA signatures
impl<P: Pairing> SRS<P> {
    pub fn get_commitment_keys(&self) -> (Vec<P::G2>, Vec<P::G1>) {
        let ck_1 = self.h_beta_powers.iter().step_by(2).cloned().collect();
        let ck_2 = self.g_alpha_powers.iter().step_by(2).cloned().collect();
        (ck_1, ck_2)
    }

    pub fn get_verifier_key(&self) -> VerifierSRS<P> {
        VerifierSRS {
            g: self.g_alpha_powers[0].clone(),
            h: self.h_beta_powers[0].clone(),
            g_beta: self.g_beta.clone(),
            h_alpha: self.h_alpha.clone(),
        }
    }
}

impl<IP, LMC, RMC, IPC, P, D> TIPA<IP, LMC, RMC, IPC, P, D>
where
    D: Digest,
    P: Pairing,
    IP: InnerProduct<
        LeftMessage = LMC::Message,
        RightMessage = RMC::Message,
        Output = IPC::Message,
    >,
    LMC: DoublyHomomorphicCommitment<Scalar = P::ScalarField, Key = P::G2> + TIPACompatibleSetup,
    RMC: DoublyHomomorphicCommitment<Scalar = LMC::Scalar, Key = P::G1> + TIPACompatibleSetup,
    IPC: DoublyHomomorphicCommitment<Scalar = LMC::Scalar>,
{
    pub fn setup<R: Rng>(rng: &mut R, size: usize) -> Result<(SRS<P>, IPC::Key), Error> {
        let alpha = <P::ScalarField>::rand(rng);
        let beta = <P::ScalarField>::rand(rng);
        let g = <P::G1>::generator();
        let h = <P::G2>::generator();
        Ok((
            SRS {
                g_alpha_powers: structured_generators_scalar_power(2 * size - 1, &g, &alpha),
                h_beta_powers: structured_generators_scalar_power(2 * size - 1, &h, &beta),
                g_beta: g.mul_bigint(beta.into_bigint()),
                h_alpha: h.mul_bigint(alpha.into_bigint()),
            },
            IPC::setup(rng, 1)?.pop().unwrap(),
        ))
    }

    pub fn prove(
        srs: &SRS<P>,
        values: (&[IP::LeftMessage], &[IP::RightMessage]),
        ck: (&[LMC::Key], &[RMC::Key], &IPC::Key),
    ) -> Result<TIPAProof<LMC, RMC, IPC, P>, Error> {
        Self::prove_with_srs_shift(srs, values, ck, &<P::ScalarField>::one())
    }

    // Shifts KZG proof for left message by scalar r (used for efficient composition with aggregation protocols)
    // LMC commitment key should already be shifted before being passed as input
    pub fn prove_with_srs_shift(
        srs: &SRS<P>,
        values: (&[IP::LeftMessage], &[IP::RightMessage]),
        ck: (&[LMC::Key], &[RMC::Key], &IPC::Key),
        r_shift: &P::ScalarField,
    ) -> Result<TIPAProof<LMC, RMC, IPC, P>, Error> {
        // Run GIPA
        let (proof, aux) = <GIPA<LMC, RMC, IPC>>::prove_with_aux::<D, IP>(
            values,
            (ck.0, ck.1, &vec![ck.2.clone()]),
        )?;

        // Prove final commitment keys are wellformed
        let (ck_a_final, ck_b_final) = aux.ck_base;
        let transcript = aux.r_transcript;
        let transcript_inverse = transcript.iter().map(|x| x.inverse().unwrap()).collect();
        let r_inverse = r_shift.inverse().unwrap();

        // KZG challenge point
        let mut counter_nonce: usize = 0;
        let c = loop {
            let mut hasher = D::new();
            hasher.update(&counter_nonce.to_be_bytes());
            transcript
                .first()
                .unwrap()
                .serialize_compressed(HashMarshaller(&mut hasher))?;
            ck_a_final.serialize_compressed(HashMarshaller(&mut hasher))?;
            ck_b_final.serialize_compressed(HashMarshaller(&mut hasher))?;
            if let Some(c) = LMC::Scalar::from_random_bytes(&hasher.finalize()) {
                break c;
            };
            counter_nonce += 1;
        };

        // Complete KZG proofs
        let ck_a_kzg_opening = prove_commitment_key_kzg_opening(
            &srs.h_beta_powers,
            &transcript_inverse,
            &r_inverse,
            &c,
        )?;
        let ck_b_kzg_opening = prove_commitment_key_kzg_opening(
            &srs.g_alpha_powers,
            &transcript,
            &<P::ScalarField>::one(),
            &c,
        )?;

        Ok(TIPAProof {
            gipa_proof: proof,
            final_ck: (ck_a_final, ck_b_final),
            final_ck_proof: (ck_a_kzg_opening, ck_b_kzg_opening),
            _pair: PhantomData,
        })
    }

    pub fn verify(
        v_srs: &VerifierSRS<P>,
        ck_t: &IPC::Key,
        com: (&LMC::Output, &RMC::Output, &IPC::Output),
        proof: &TIPAProof<LMC, RMC, IPC, P>,
    ) -> Result<bool, Error> {
        Self::verify_with_srs_shift(v_srs, ck_t, com, proof, &<P::ScalarField>::one())
    }

    pub fn verify_with_srs_shift(
        v_srs: &VerifierSRS<P>,
        ck_t: &IPC::Key,
        com: (&LMC::Output, &RMC::Output, &IPC::Output),
        proof: &TIPAProof<LMC, RMC, IPC, P>,
        r_shift: &P::ScalarField,
    ) -> Result<bool, Error> {
        let (base_com, transcript) =
            GIPA::verify_recursive_challenge_transcript::<D>(com, &proof.gipa_proof)?;
        let transcript_inverse = transcript.iter().map(|x| x.inverse().unwrap()).collect();

        // Verify commitment keys wellformed
        let (ck_a_final, ck_b_final) = &proof.final_ck;
        let (ck_a_proof, ck_b_proof) = &proof.final_ck_proof;

        // KZG challenge point
        let mut counter_nonce: usize = 0;
        let c = loop {
            let mut hasher = D::new();
            hasher.update(&counter_nonce.to_be_bytes());
            transcript
                .first()
                .unwrap()
                .serialize_compressed(HashMarshaller(&mut hasher))?;
            ck_a_final.serialize_compressed(HashMarshaller(&mut hasher))?;
            ck_b_final.serialize_compressed(HashMarshaller(&mut hasher))?;
            if let Some(c) = LMC::Scalar::from_random_bytes(&hasher.finalize()) {
                break c;
            };
            counter_nonce += 1;
        };

        let ck_a_valid = verify_commitment_key_g2_kzg_opening(
            v_srs,
            &ck_a_final,
            &ck_a_proof,
            &transcript_inverse,
            &r_shift.inverse().unwrap(),
            &c,
        )?;
        let ck_b_valid = verify_commitment_key_g1_kzg_opening(
            v_srs,
            &ck_b_final,
            &ck_b_proof,
            &transcript,
            &<P::ScalarField>::one(),
            &c,
        )?;

        // Verify base inner product commitment
        let (com_a, com_b, com_t) = base_com;
        let a_base = vec![proof.gipa_proof.r_base.0.clone()];
        let b_base = vec![proof.gipa_proof.r_base.1.clone()];
        let t_base = vec![IP::inner_product(&a_base, &b_base)?];
        let base_valid = LMC::verify(&vec![ck_a_final.clone()], &a_base, &com_a)?
            && RMC::verify(&vec![ck_b_final.clone()], &b_base, &com_b)?
            && IPC::verify(&vec![ck_t.clone()], &t_base, &com_t)?;

        Ok(ck_a_valid && ck_b_valid && base_valid)
    }
}

pub fn prove_commitment_key_kzg_opening<G, F: PrimeField>(
    srs_powers: &Vec<G>,
    transcript: &Vec<F>,
    r_shift: &F,
    kzg_challenge: &F,
) -> Result<G, Error>
where
    G: CurveGroup<ScalarField = F>,
{
    let ck_polynomial = DensePolynomial::from_coefficients_slice(
        &polynomial_coefficients_from_transcript(transcript, r_shift),
    );
    assert_eq!(srs_powers.len(), ck_polynomial.coeffs.len());

    let eval = start_timer!(|| "polynomial eval");
    let ck_polynomial_c_eval =
        polynomial_evaluation_product_form_from_transcript(&transcript, kzg_challenge, &r_shift);
    end_timer!(eval);

    let quotient = start_timer!(|| "polynomial quotient");
    let quotient_polynomial = &(&ck_polynomial
        - &DensePolynomial::from_coefficients_vec(vec![ck_polynomial_c_eval]))
        / &(DensePolynomial::from_coefficients_vec(vec![-kzg_challenge.clone(), F::one()]));
    end_timer!(quotient);

    let mut quotient_polynomial_coeffs = quotient_polynomial.coeffs;
    quotient_polynomial_coeffs.resize(srs_powers.len(), F::zero());

    let mul_biginttiexp = start_timer!(|| "opening mul_biginttiexp");
    let opening =
        MultiexponentiationInnerProduct::inner_product(srs_powers, &quotient_polynomial_coeffs);
    end_timer!(mul_biginttiexp);
    opening
}

//TODO: Figure out how to avoid needing two separate methods for verification of opposite groups
pub fn verify_commitment_key_g2_kzg_opening<P: Pairing>(
    v_srs: &VerifierSRS<P>,
    ck_final: &P::G2,
    ck_opening: &P::G2,
    transcript: &Vec<P::ScalarField>,
    r_shift: &P::ScalarField,
    kzg_challenge: &P::ScalarField,
) -> Result<bool, Error> {
    let ck_polynomial_c_eval =
        polynomial_evaluation_product_form_from_transcript(transcript, kzg_challenge, r_shift);
    Ok(P::pairing(
        v_srs.g,
        *ck_final - &v_srs.h.mul_bigint(ck_polynomial_c_eval.into_bigint()),
    ) == P::pairing(
        v_srs.g_beta - &v_srs.g.mul_bigint(kzg_challenge.into_bigint()),
        *ck_opening,
    ))
}

pub fn verify_commitment_key_g1_kzg_opening<P: Pairing>(
    v_srs: &VerifierSRS<P>,
    ck_final: &P::G1,
    ck_opening: &P::G1,
    transcript: &Vec<P::ScalarField>,
    r_shift: &P::ScalarField,
    kzg_challenge: &P::ScalarField,
) -> Result<bool, Error> {
    let ck_polynomial_c_eval =
        polynomial_evaluation_product_form_from_transcript(transcript, kzg_challenge, r_shift);
    Ok(P::pairing(
        *ck_final - &v_srs.g.mul_bigint(ck_polynomial_c_eval.into_bigint()),
        v_srs.h,
    ) == P::pairing(
        *ck_opening,
        v_srs.h_alpha - &v_srs.h.mul_bigint(kzg_challenge.into_bigint()),
    ))
}

pub fn structured_generators_scalar_power<G: CurveGroup>(
    num: usize,
    g: &G,
    s: &<G as Group>::ScalarField,
) -> Vec<G> {
    assert!(num > 0);
    let mut powers_of_scalar = vec![];
    let mut pow_s = G::ScalarField::one();
    for _ in 0..num {
        powers_of_scalar.push(pow_s);
        pow_s *= s;
    }

    let window_size = FixedBase::get_mul_window_size(num);

    let scalar_bits = G::ScalarField::MODULUS_BIT_SIZE as usize;
    let g_table = FixedBase::get_window_table(scalar_bits, window_size, g.clone());
    let powers_of_g = FixedBase::msm::<G>(scalar_bits, window_size, &g_table, &powers_of_scalar);
    powers_of_g
}

fn polynomial_evaluation_product_form_from_transcript<F: Field>(
    transcript: &Vec<F>,
    z: &F,
    r_shift: &F,
) -> F {
    let mut power_2_zr = (z.clone() * z) * r_shift;
    let mut product_form = Vec::new();
    for x in transcript.iter() {
        product_form.push(F::one() + (x.clone() * &power_2_zr));
        power_2_zr *= power_2_zr;
    }
    product_form.iter().product()
}

fn polynomial_coefficients_from_transcript<F: Field>(transcript: &Vec<F>, r_shift: &F) -> Vec<F> {
    let mut coefficients = vec![F::one()];
    let mut power_2_r = r_shift.clone();
    for (i, x) in transcript.iter().enumerate() {
        for j in 0..(2_usize).pow(i as u32) {
            coefficients.push(coefficients[j] * &(x.clone() * &power_2_r));
        }
        power_2_r *= power_2_r;
    }
    // Interleave with 0 coefficients
    let mut coefficients = coefficients
        .into_iter()
        .flat_map(|i| vec![i, F::zero()])
        .collect::<Vec<_>>();
    coefficients.pop();
    coefficients
}
