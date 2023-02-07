use ark_ec::pairing::Pairing;
use ark_ff::{Field, One};
use ark_groth16::{Proof, VerifyingKey};
use ark_serialize::CanonicalSerialize;

use std::ops::{AddAssign, Mul};
use std::{
    error::Error as ErrorTrait,
    fmt::{Display, Formatter, Result as FmtResult},
    ops::MulAssign,
};

use ark_std::rand::Rng;
use digest::Digest;

mod dh_commitments;
mod gipa;
mod inner_product;
pub mod tipa;

use dh_commitments::{
    AFGHOCommitmentG1, AFGHOCommitmentG2, HomomorphicPlaceholderValue, IdentityCommitment,
    IdentityOutput,
};
use inner_product::{
    ExtensionFieldElement, InnerProduct, MultiexponentiationInnerProduct, PairingInnerProduct,
    ScalarInnerProduct,
};
use tipa::{
    structured_scalar_message::{structured_scalar_power, TIPAWithSSM, TIPAWithSSMProof},
    TIPAProof, VerifierSRS, SRS, TIPA,
};

pub type Error = Box<dyn ErrorTrait>;

//TODO: helper function for mul because relying on MulAssign
pub(crate) fn mul_helper<T: MulAssign<F> + Clone, F: Clone>(t: &T, f: &F) -> T {
    let mut clone = t.clone();
    clone.mul_assign(f.clone());
    clone
}

#[derive(Debug)]
pub enum InnerProductArgumentError {
    MessageLengthInvalid(usize, usize),
    InnerProductInvalid,
}

impl ErrorTrait for InnerProductArgumentError {
    fn source(self: &Self) -> Option<&(dyn ErrorTrait + 'static)> {
        None
    }
}

impl Display for InnerProductArgumentError {
    fn fmt(self: &Self, f: &mut Formatter<'_>) -> FmtResult {
        let msg = match self {
            InnerProductArgumentError::MessageLengthInvalid(left, right) => {
                format!("left length, right length: {}, {}", left, right)
            }
            InnerProductArgumentError::InnerProductInvalid => "inner product not sound".to_string(),
        };
        write!(f, "{}", msg)
    }
}

pub struct HashMarshaller<'a, H: Digest>(&'a mut H);

impl<'a, H: Digest> ark_std::io::Write for HashMarshaller<'a, H> {
    #[inline]
    fn write(&mut self, buf: &[u8]) -> ark_std::io::Result<usize> {
        Digest::update(self.0, buf);
        Ok(buf.len())
    }

    #[inline]
    fn flush(&mut self) -> ark_std::io::Result<()> {
        Ok(())
    }
}

type PairingInnerProductAB<P, D> = TIPA<
    PairingInnerProduct<P>,
    AFGHOCommitmentG1<P>,
    AFGHOCommitmentG2<P>,
    IdentityCommitment<ExtensionFieldElement<P>, <P as Pairing>::ScalarField>,
    P,
    D,
>;

type PairingInnerProductABProof<P> = TIPAProof<
    AFGHOCommitmentG1<P>,
    AFGHOCommitmentG2<P>,
    IdentityCommitment<ExtensionFieldElement<P>, <P as Pairing>::ScalarField>,
    P,
>;

type MultiExpInnerProductC<P, D> = TIPAWithSSM<
    MultiexponentiationInnerProduct<<P as Pairing>::G1>,
    AFGHOCommitmentG1<P>,
    IdentityCommitment<<P as Pairing>::G1, <P as Pairing>::ScalarField>,
    P,
    D,
>;

type MultiExpInnerProductCProof<P> = TIPAWithSSMProof<
    AFGHOCommitmentG1<P>,
    IdentityCommitment<<P as Pairing>::G1, <P as Pairing>::ScalarField>,
    P,
>;

pub struct AggregateProof<P: Pairing> {
    com_a: ExtensionFieldElement<P>,
    com_b: ExtensionFieldElement<P>,
    com_c: ExtensionFieldElement<P>,
    ip_ab: ExtensionFieldElement<P>,
    agg_c: P::G1,
    tipa_proof_ab: PairingInnerProductABProof<P>,
    tipa_proof_c: MultiExpInnerProductCProof<P>,
}

pub fn setup_inner_product<P, D, R: Rng>(rng: &mut R, size: usize) -> Result<SRS<P>, Error>
where
    P: Pairing,
    D: Digest,
{
    let (srs, _) = PairingInnerProductAB::<P, D>::setup(rng, size)?;
    Ok(srs)
}

pub fn aggregate_proofs<P, D>(
    ip_srs: &SRS<P>,
    proofs: &[Proof<P>],
) -> Result<AggregateProof<P>, Error>
where
    P: Pairing,
    D: Digest,
{
    let a = proofs
        .iter()
        .map(|proof| proof.a.into())
        .collect::<Vec<P::G1>>();
    let b = proofs
        .iter()
        .map(|proof| proof.b.into())
        .collect::<Vec<P::G2>>();
    let c = proofs
        .iter()
        .map(|proof| proof.c.into())
        .collect::<Vec<P::G1>>();

    let (ck_1, ck_2) = ip_srs.get_commitment_keys();

    let com_a = PairingInnerProduct::<P>::inner_product(&a, &ck_1)?;
    let com_b = PairingInnerProduct::<P>::inner_product(&ck_2, &b)?;
    let com_c = PairingInnerProduct::<P>::inner_product(&c, &ck_1)?;

    // Random linear combination of proofs
    let mut counter_nonce: usize = 0;
    let r = loop {
        let mut hasher = D::new();
        hasher.update(&counter_nonce.to_be_bytes());
        com_a.serialize_compressed(HashMarshaller(&mut hasher))?;
        com_b.serialize_compressed(HashMarshaller(&mut hasher))?;
        com_c.serialize_compressed(HashMarshaller(&mut hasher))?;
        if let Some(r) = <P::ScalarField>::from_random_bytes(&hasher.finalize()) {
            break r;
        };
        counter_nonce += 1;
    };

    let r_vec = structured_scalar_power(proofs.len(), &r);
    let a_r = a
        .iter()
        .zip(&r_vec)
        .map(|(a, r)| a.mul(r))
        .collect::<Vec<P::G1>>();
    let ip_ab = PairingInnerProduct::<P>::inner_product(&a_r, &b)?;
    let agg_c = MultiexponentiationInnerProduct::<P::G1>::inner_product(&c, &r_vec)?;

    let ck_1_r = ck_1
        .iter()
        .zip(&r_vec)
        .map(|(ck, r)| ck.mul(&r.inverse().unwrap()))
        .collect::<Vec<P::G2>>();

    assert_eq!(
        com_a,
        PairingInnerProduct::<P>::inner_product(&a_r, &ck_1_r)?
    );

    let tipa_proof_ab = PairingInnerProductAB::<P, D>::prove_with_srs_shift(
        &ip_srs,
        (&a_r, &b),
        (&ck_1_r, &ck_2, &HomomorphicPlaceholderValue),
        &r,
    )?;

    let tipa_proof_c = MultiExpInnerProductC::<P, D>::prove_with_structured_scalar_message(
        &ip_srs,
        (&c, &r_vec),
        (&ck_1, &HomomorphicPlaceholderValue),
    )?;

    Ok(AggregateProof {
        com_a,
        com_b,
        com_c,
        ip_ab,
        agg_c,
        tipa_proof_ab,
        tipa_proof_c,
    })
}

pub fn verify_aggregate_proof<P, D>(
    ip_verifier_srs: &VerifierSRS<P>,
    vk: &VerifyingKey<P>,
    public_inputs: &Vec<Vec<P::ScalarField>>, //TODO: Should use ToConstraintField instead
    proof: &AggregateProof<P>,
) -> Result<bool, Error>
where
    P: Pairing,
    D: Digest,
{
    // Random linear combination of proofs
    let mut counter_nonce: usize = 0;
    let r = loop {
        let mut hasher = D::new();
        hasher.update(&counter_nonce.to_be_bytes());
        proof
            .com_a
            .serialize_compressed(HashMarshaller(&mut hasher))?;
        proof
            .com_b
            .serialize_compressed(HashMarshaller(&mut hasher))?;
        proof
            .com_c
            .serialize_compressed(HashMarshaller(&mut hasher))?;
        if let Some(r) = <P::ScalarField>::from_random_bytes(&hasher.finalize()) {
            break r;
        };
        counter_nonce += 1;
    };

    // Check TIPA proofs
    let tipa_proof_ab_valid = PairingInnerProductAB::<P, D>::verify_with_srs_shift(
        ip_verifier_srs,
        &HomomorphicPlaceholderValue,
        (
            &proof.com_a,
            &proof.com_b,
            &IdentityOutput(vec![proof.ip_ab.clone()]),
        ),
        &proof.tipa_proof_ab,
        &r,
    )?;
    let tipa_proof_c_valid = MultiExpInnerProductC::<P, D>::verify_with_structured_scalar_message(
        ip_verifier_srs,
        &HomomorphicPlaceholderValue,
        (&proof.com_c, &IdentityOutput(vec![proof.agg_c.clone()])),
        &r,
        &proof.tipa_proof_c,
    )?;

    // Check aggregate pairing product equation

    let r_sum = (r.pow(&[public_inputs.len() as u64]) - &<P::ScalarField>::one())
        / &(r.clone() - &<P::ScalarField>::one());
    let p1 = P::pairing(vk.alpha_g1.mul(&r_sum), vk.beta_g2).0;

    assert_eq!(vk.gamma_abc_g1.len(), public_inputs[0].len() + 1);
    let r_vec = structured_scalar_power(public_inputs.len(), &r);
    let mut g_ic = vk.gamma_abc_g1[0].mul(&r_sum);
    for (i, b) in vk.gamma_abc_g1.iter().skip(1).enumerate() {
        g_ic.add_assign(
            &b.mul(&ScalarInnerProduct::inner_product(
                &public_inputs
                    .iter()
                    .map(|inputs| inputs[i].clone())
                    .collect::<Vec<P::ScalarField>>(),
                &r_vec,
            )?),
        );
    }
    let p2 = P::pairing(g_ic, vk.gamma_g2).0;
    let p3 = P::pairing(proof.agg_c, vk.delta_g2).0;

    let ppe_valid = proof.ip_ab.0 == (p1 * &p2) * &p3;

    Ok(tipa_proof_ab_valid && tipa_proof_c_valid && ppe_valid)
}

#[cfg(test)]
mod tests {
    use super::*;

    use std::time::Instant;

    use ark_bls12_381::{Bls12_381, Fr};
    use ark_ff::UniformRand;
    use ark_groth16::{create_random_proof, generate_random_parameters};
    use ark_r1cs_std::{fields::fp::FpVar, prelude::*};
    use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};

    use ark_std::rand::{rngs::StdRng, SeedableRng};
    use blake2::Blake2b512;

    #[derive(Clone)]
    struct TestCircuit {
        public_inputs: Vec<Fr>,
        witness_input: Fr,
        public_sum: Fr,
    }

    impl ConstraintSynthesizer<Fr> for TestCircuit {
        fn generate_constraints(self, cs: ConstraintSystemRef<Fr>) -> Result<(), SynthesisError> {
            let input_variables =
                Vec::<FpVar<Fr>>::new_input(cs.clone(), || Ok(self.public_inputs.clone()))?;
            let sum = FpVar::new_input(cs.clone(), || Ok(&self.public_sum))?;
            let witness = FpVar::new_witness(cs.clone(), || Ok(&self.witness_input))?;

            let mut computed_sum = witness;
            for x in &input_variables {
                computed_sum += x;
            }

            sum.enforce_equal(&computed_sum)?;

            Ok(())
        }
    }

    #[test]
    fn test() {
        const NUM_PUBLIC_INPUTS: usize = 4;
        const NUM_PROOFS_TO_AGGREGATE: usize = 1024;
        let mut rng = StdRng::seed_from_u64(0u64);

        // Generate parameters for Groth16
        let test_circuit = TestCircuit {
            public_inputs: vec![Default::default(); NUM_PUBLIC_INPUTS],
            public_sum: Default::default(),
            witness_input: Default::default(),
        };
        let parameters = generate_random_parameters(test_circuit, &mut rng).unwrap();

        // Generate parameters for inner product aggregation
        let srs =
            setup_inner_product::<_, Blake2b512, _>(&mut rng, NUM_PROOFS_TO_AGGREGATE).unwrap();

        // Generate proofs
        println!("Generating {} Groth16 proofs...", NUM_PROOFS_TO_AGGREGATE);
        let mut start = Instant::now();
        let mut proofs = Vec::new();
        let mut statements = Vec::new();
        for _ in 0..NUM_PROOFS_TO_AGGREGATE {
            // Generate random inputs to sum together
            let mut public_inputs = Vec::new();
            let mut statement = Vec::new();
            for i in 0..NUM_PUBLIC_INPUTS {
                public_inputs.push(Fr::rand(&mut rng));
                statement.push(public_inputs[i].clone());
            }
            let w = Fr::rand(&mut rng);
            let sum: Fr = w.clone() + &public_inputs.iter().sum();
            statement.push(sum.clone());
            let circuit = TestCircuit {
                public_inputs: public_inputs,
                public_sum: sum,
                witness_input: w,
            };

            let proof = create_random_proof(circuit.clone(), &parameters, &mut rng).unwrap();
            proofs.push(proof);
            statements.push(statement);

            //let result = Groth16::<Bls12_381, TestCircuit, [Fr]>::verify(&parameters.1, &statement, &proof).unwrap();
            //assert!(result);
        }
        let generation_time = start.elapsed().as_millis();

        // Aggregate proofs using inner product proofs
        start = Instant::now();
        println!("Aggregating {} Groth16 proofs...", NUM_PROOFS_TO_AGGREGATE);
        let aggregate_proof = aggregate_proofs::<Bls12_381, Blake2b512>(&srs, &proofs).unwrap();
        let prover_time = start.elapsed().as_millis();

        println!("Verifying aggregated proof...");
        start = Instant::now();
        let result = verify_aggregate_proof::<Bls12_381, Blake2b512>(
            &srs.get_verifier_key(),
            &parameters.vk,
            &statements,
            &aggregate_proof,
        )
        .unwrap();
        let verifier_time = start.elapsed().as_millis();
        assert!(result);

        println!("Proof generation time: {} ms", generation_time);
        println!("Proof aggregation time: {} ms", prover_time);
        println!("Proof verification time: {} ms", verifier_time);
    }
}
