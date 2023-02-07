use ark_ec::{pairing::Pairing, CurveGroup, VariableBaseMSM};
use ark_ff::{Field, PrimeField};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use rayon::prelude::IntoParallelRefIterator;
use std::{
    error::Error as ErrorTrait,
    fmt::{Display, Formatter, Result as FmtResult},
    marker::PhantomData,
    ops::{Add, Mul, MulAssign},
};

use rayon::prelude::*;

pub type Error = Box<dyn ErrorTrait>;

#[derive(Debug)]
pub enum InnerProductError {
    MessageLengthInvalid(usize, usize),
}

impl ErrorTrait for InnerProductError {
    fn source(self: &Self) -> Option<&(dyn ErrorTrait + 'static)> {
        None
    }
}

impl Display for InnerProductError {
    fn fmt(self: &Self, f: &mut Formatter<'_>) -> FmtResult {
        let msg = match self {
            InnerProductError::MessageLengthInvalid(left, right) => {
                format!("left length, right length: {}, {}", left, right)
            }
        };
        write!(f, "{}", msg)
    }
}

pub trait InnerProduct: Copy {
    type LeftMessage;
    type RightMessage;
    type Output;

    fn inner_product(
        left: &[Self::LeftMessage],
        right: &[Self::RightMessage],
    ) -> Result<Self::Output, Error>;
}

#[derive(Copy, Clone)]
pub struct PairingInnerProduct<P: Pairing> {
    _pair: PhantomData<P>,
}

impl<P: Pairing> InnerProduct for PairingInnerProduct<P> {
    type LeftMessage = P::G1;
    type RightMessage = P::G2;
    type Output = ExtensionFieldElement<P>;

    fn inner_product(
        left: &[Self::LeftMessage],
        right: &[Self::RightMessage],
    ) -> Result<Self::Output, Error> {
        if left.len() != right.len() {
            return Err(Box::new(InnerProductError::MessageLengthInvalid(
                left.len(),
                right.len(),
            )));
        };
        let aff_left = P::G1::normalize_batch(left);
        let aff_right = P::G2::normalize_batch(right);
        Ok(ExtensionFieldElement(
            P::multi_pairing(&aff_left, &aff_right).0,
        ))
    }
}

#[derive(Copy, Clone)]
pub struct MultiexponentiationInnerProduct<G: CurveGroup> {
    _projective: PhantomData<G>,
}

impl<G: CurveGroup> InnerProduct for MultiexponentiationInnerProduct<G> {
    type LeftMessage = G;
    type RightMessage = G::ScalarField;
    type Output = G;

    fn inner_product(
        left: &[Self::LeftMessage],
        right: &[Self::RightMessage],
    ) -> Result<Self::Output, Error> {
        if left.len() != right.len() {
            return Err(Box::new(InnerProductError::MessageLengthInvalid(
                left.len(),
                right.len(),
            )));
        };
        Ok(VariableBaseMSM::msm_unchecked(
            &G::normalize_batch(left),
            &right,
        ))
    }
}

#[derive(Copy, Clone)]
pub struct ScalarInnerProduct<F: Field> {
    _field: PhantomData<F>,
}

impl<F: Field> InnerProduct for ScalarInnerProduct<F> {
    type LeftMessage = F;
    type RightMessage = F;
    type Output = F;

    fn inner_product(
        left: &[Self::LeftMessage],
        right: &[Self::RightMessage],
    ) -> Result<Self::Output, Error> {
        if left.len() != right.len() {
            return Err(Box::new(InnerProductError::MessageLengthInvalid(
                left.len(),
                right.len(),
            )));
        };
        Ok(left.par_iter().zip(right).map(|(x, y)| *x * y).sum())
    }
}

// Helper wrapper type around target group commitment output in order to implement MulAssign (needed for dh_commitments)
//TODO: PairingEngine provides target group GT implementing Group for prime order P::Fr

#[derive(CanonicalSerialize, CanonicalDeserialize, Clone, Debug)]
pub struct ExtensionFieldElement<P: Pairing>(pub P::TargetField);

impl<P: Pairing> Default for ExtensionFieldElement<P> {
    fn default() -> Self {
        ExtensionFieldElement(Default::default())
    }
}

impl<P: Pairing> PartialEq for ExtensionFieldElement<P> {
    fn eq(&self, other: &Self) -> bool {
        self.0.eq(&other.0)
    }
}

impl<P: Pairing> Eq for ExtensionFieldElement<P> {}

impl<P: Pairing> MulAssign<P::ScalarField> for ExtensionFieldElement<P> {
    fn mul_assign(&mut self, rhs: P::ScalarField) {
        *self = ExtensionFieldElement(self.0.pow(rhs.into_bigint()))
    }
}

impl<P: Pairing> Add<Self> for ExtensionFieldElement<P> {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        ExtensionFieldElement(<P::TargetField as Mul>::mul(self.0, rhs.0))
    }
}
