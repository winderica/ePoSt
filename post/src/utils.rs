use bellperson::{
    bls::{Bls12, Fr, FrRepr},
    gadgets::multipack::pack_into_inputs,
    Circuit, ConstraintSystem, SynthesisError, Variable,
};

pub const ZERO: Fr = Fr::zero();
pub const ONE: Fr = Fr::one();

pub fn alloc<CS>(cs: &mut CS, value: Fr) -> Variable
where
    CS: ConstraintSystem<Bls12>,
{
    cs.alloc(|| "", || Ok(value)).unwrap()
}

pub fn alloc_input<CS>(cs: &mut CS, value: Fr) -> Variable
where
    CS: ConstraintSystem<Bls12>,
{
    cs.alloc_input(|| "", || Ok(value)).unwrap()
}
