//! # `blstrs`
//!
//! An implementation of the BLS12-381 pairing-friendly elliptic curve construction.

#![deny(clippy::all, clippy::perf, clippy::correctness)]
#![allow(clippy::many_single_char_names)]

#[macro_use]
mod macros;

mod fp;
mod fp12;
mod fp2;
mod fp6;
mod g1;
mod g2;
mod pairing;
mod scalar;
mod traits;

pub use fff::*;
pub use fp::{Fp, FpRepr};
pub use fp12::Fp12;
pub use fp2::Fp2;
pub use fp6::Fp6;
pub use g1::*;
pub use g2::*;
pub use pairing::*;
pub use scalar::{Scalar, ScalarRepr, S as SCALAR_S};
pub use traits::*;

mod serde_impl;

#[cfg(test)]
mod tests;

/// Bls12-381 engine
#[derive(Debug, Copy, Clone)]
pub struct Bls12;

impl fff::ScalarEngine for Bls12 {
    type Fr = Scalar;
}

impl Engine for Bls12 {
    type G1 = G1Projective;
    type G1Affine = G1Affine;
    type G2 = G2Projective;
    type G2Affine = G2Affine;
    type Fq = Fp;
    type Fqe = Fp2;
    type Fqk = Fp12;

    fn miller_loop<'a, I>(i: I) -> Self::Fqk
    where
        I: IntoIterator<
            Item = &'a (
                &'a <Self::G1Affine as PairingCurveAffine>::Prepared,
                &'a <Self::G2Affine as PairingCurveAffine>::Prepared,
            ),
        >,
    {
        use groupy::CurveAffine;

        let mut res = blst::blst_fp12::default();

        for (i, (p, q)) in i.into_iter().enumerate() {
            let mut tmp = blst::blst_fp12::default();
            if q.is_zero() || p.is_zero() {
                // Define pairing with zero as one, matching what `pairing` does.
                tmp = Fp12::one().0;
            } else {
                unsafe {
                    blst::blst_miller_loop_lines(&mut tmp, q.lines.as_ptr(), &p.0);
                }
            }
            if i == 0 {
                res = tmp;
            } else {
                unsafe {
                    blst::blst_fp12_mul(&mut res, &res, &tmp);
                }
            }
        }

        Fp12(res)
    }

    fn final_exponentiation(r: &Fp12) -> Option<Fp12> {
        let mut out = blst::blst_fp12::default();
        unsafe { blst::blst_final_exp(&mut out, &r.0) };

        // TODO: What about the None case?
        Some(out.into())
    }
}

#[test]
fn bls12_engine_tests() {
    crate::tests::engine::engine_tests::<Bls12>();
}
