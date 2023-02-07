use ark_ec::{pairing::Pairing, Group};
use ark_ff::fields::PrimeField;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::rand::Rng;
use std::{
    cmp::Eq,
    error::Error as ErrorTrait,
    marker::PhantomData,
    ops::{Add, MulAssign},
};

use super::inner_product::{ExtensionFieldElement, InnerProduct, PairingInnerProduct};

pub type Error = Box<dyn ErrorTrait>;

//TODO: support CanonicalSerialize
//TODO: Using MulAssign instead of Mul because Group does not support Mul

pub trait DoublyHomomorphicCommitment: Clone {
    type Scalar: PrimeField;
    type Message: CanonicalSerialize
        + CanonicalDeserialize
        + Clone
        + Default
        + Eq
        + Send
        + Sync
        + Add<Self::Message, Output = Self::Message>
        + MulAssign<Self::Scalar>;
    type Key: CanonicalSerialize
        + CanonicalDeserialize
        + Clone
        + Default
        + Eq
        + Send
        + Sync
        + Add<Self::Key, Output = Self::Key>
        + MulAssign<Self::Scalar>;
    type Output: CanonicalSerialize
        + CanonicalDeserialize
        + Clone
        + Default
        + Eq
        + Add<Self::Output, Output = Self::Output>
        + MulAssign<Self::Scalar>;

    fn setup<R: Rng>(r: &mut R, size: usize) -> Result<Vec<Self::Key>, Error>;

    fn commit(k: &[Self::Key], m: &[Self::Message]) -> Result<Self::Output, Error>;

    fn verify(k: &[Self::Key], m: &[Self::Message], com: &Self::Output) -> Result<bool, Error> {
        Ok(Self::commit(k, m)? == *com)
    }
}

// Helpers for generator commitment keys used by Pedersen and AFGHO16

pub fn random_generators<R: Rng, G: Group>(rng: &mut R, num: usize) -> Vec<G> {
    (0..num).map(|_| G::rand(rng)).collect()
}

#[derive(Clone)]
pub struct IdentityCommitment<T, F: PrimeField> {
    _t: PhantomData<T>,
    _field: PhantomData<F>,
}

#[derive(CanonicalSerialize, CanonicalDeserialize, Clone, Default, Eq, PartialEq)]
pub struct HomomorphicPlaceholderValue;

impl Add for HomomorphicPlaceholderValue {
    type Output = Self;

    fn add(self, _rhs: Self) -> Self::Output {
        HomomorphicPlaceholderValue {}
    }
}

impl<T> MulAssign<T> for HomomorphicPlaceholderValue {
    fn mul_assign(&mut self, _rhs: T) {}
}

#[derive(CanonicalSerialize, CanonicalDeserialize, Clone, Default, Eq, PartialEq)]
pub struct IdentityOutput<T>(pub Vec<T>)
where
    T: CanonicalSerialize + CanonicalDeserialize + Clone + Default + Eq;

impl<T> Add for IdentityOutput<T>
where
    T: Add<T, Output = T> + CanonicalSerialize + CanonicalDeserialize + Clone + Default + Eq,
{
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        IdentityOutput(
            self.0
                .iter()
                .zip(&rhs.0)
                .map(|(a, b)| a.clone() + b.clone())
                .collect::<Vec<T>>(),
        )
    }
}

impl<T, F> MulAssign<F> for IdentityOutput<T>
where
    T: MulAssign<F> + CanonicalSerialize + CanonicalDeserialize + Clone + Default + Eq,
    F: Clone,
{
    fn mul_assign(&mut self, rhs: F) {
        self.0.iter_mut().for_each(|a| a.mul_assign(rhs.clone()))
    }
}

impl<T, F> DoublyHomomorphicCommitment for IdentityCommitment<T, F>
where
    T: CanonicalSerialize
        + CanonicalDeserialize
        + Clone
        + Default
        + Eq
        + Add<T, Output = T>
        + MulAssign<F>
        + Send
        + Sync,
    F: PrimeField,
{
    type Scalar = F;
    type Message = T;
    type Key = HomomorphicPlaceholderValue;
    type Output = IdentityOutput<T>;

    fn setup<R: Rng>(_rng: &mut R, size: usize) -> Result<Vec<Self::Key>, Error> {
        Ok(vec![HomomorphicPlaceholderValue {}; size])
    }

    fn commit(_k: &[Self::Key], m: &[Self::Message]) -> Result<Self::Output, Error> {
        Ok(IdentityOutput(m.to_vec()))
    }
}

#[derive(Clone)]
pub struct AFGHOCommitment<P: Pairing> {
    _pair: PhantomData<P>,
}

#[derive(Clone)]
pub struct AFGHOCommitmentG1<P: Pairing>(AFGHOCommitment<P>);

#[derive(Clone)]
pub struct AFGHOCommitmentG2<P: Pairing>(AFGHOCommitment<P>);

impl<P: Pairing> DoublyHomomorphicCommitment for AFGHOCommitmentG1<P> {
    type Scalar = P::ScalarField;
    type Message = P::G1;
    type Key = P::G2;
    type Output = ExtensionFieldElement<P>;

    fn setup<R: Rng>(rng: &mut R, size: usize) -> Result<Vec<Self::Key>, Error> {
        Ok(random_generators(rng, size))
    }

    fn commit(k: &[Self::Key], m: &[Self::Message]) -> Result<Self::Output, Error> {
        PairingInnerProduct::<P>::inner_product(m, k)
    }
}

impl<P: Pairing> DoublyHomomorphicCommitment for AFGHOCommitmentG2<P> {
    type Scalar = P::ScalarField;
    type Message = P::G2;
    type Key = P::G1;
    type Output = ExtensionFieldElement<P>;

    fn setup<R: Rng>(rng: &mut R, size: usize) -> Result<Vec<Self::Key>, Error> {
        Ok(random_generators(rng, size))
    }

    fn commit(k: &[Self::Key], m: &[Self::Message]) -> Result<Self::Output, Error> {
        PairingInnerProduct::<P>::inner_product(k, m)
    }
}
