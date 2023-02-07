use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::{fields::PrimeField, BigInteger, UniformRand};
use ark_std::rand::Rng;

use super::poseidon::{PoseidonParameters, CRH};

pub mod constraints;

pub struct Schnorr {}

impl Schnorr {
    pub fn key_gen<C: AffineRepr, R: Rng>(rng: &mut R) -> (C::ScalarField, C) {
        let sk = C::ScalarField::rand(rng);
        let pk = C::generator().mul(sk).into();

        (sk, pk)
    }

    pub fn sign<C, Fr: PrimeField, Fq: PrimeField, R: Rng>(
        pp: &PoseidonParameters<Fq>,
        sk: Fr,
        m: Fq,
        rng: &mut R,
    ) -> (Fr, Fr)
    where
        C: AffineRepr<ScalarField = Fr, BaseField = Fq>,
    {
        loop {
            let k = Fr::rand(rng);
            let (&x, &y) = C::generator().mul(k).into_affine().xy().unwrap();

            let h = CRH::hash(&pp, x, y, m, Default::default());
            let mut h_bits = h.into_bigint().to_bits_le();
            h_bits.truncate(Fr::MODULUS_BIT_SIZE as usize + 1);
            let h = Fr::BigInt::from_bits_le(&h_bits);

            if let Some(e) = Fr::from_bigint(h) {
                return (k - sk * e, e);
            };
        }
    }

    pub fn verify<C, Fr: PrimeField, Fq: PrimeField>(
        pp: &PoseidonParameters<Fq>,
        pk: &C,
        message: Fq,
        (s, e): (Fr, Fr),
    ) -> bool
    where
        C: AffineRepr<ScalarField = Fr, BaseField = Fq>,
    {
        let (&x, &y) = (C::generator().mul(s) + pk.mul(e))
            .into_affine()
            .xy()
            .unwrap();

        let h = CRH::hash(&pp, x, y, message, Default::default());
        let mut h_bits = h.into_bigint().to_bits_le();
        h_bits.truncate(Fr::MODULUS_BIT_SIZE as usize);
        let h = Fr::BigInt::from_bits_le(&h_bits);

        Fr::from_bigint(h).map_or(false, |i| i == e)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_ed_on_bls12_381::{EdwardsAffine, Fq};
    use rand::thread_rng;

    #[test]
    fn test() {
        let rng = &mut thread_rng();
        let pp = PoseidonParameters::<Fq>::default();
        let (sk, pk) = Schnorr::key_gen::<EdwardsAffine, _>(rng);
        let m = Fq::rand(rng);
        let (s, e) = Schnorr::sign::<EdwardsAffine, _, _, _>(&pp, sk, m, rng);
        assert!(Schnorr::verify(&pp, &pk, m, (s, e)));
    }
}
