use crate::{
    bn::{div_mod, bn_to_bool_arr, duplicate, bn_to_u64_arr, bn_to_u127_arr},
    utils::{alloc, alloc_input, ONE, ZERO},
};
use bellperson::{
    bls::{Bls12, Fr},
    ConstraintSystem, LinearCombination, Variable,
};
use openssl::bn::BigNum;
use std::{cmp, fmt::Debug};

// 2^1
const R_1: Fr = Fr::from_u256([0x00000003fffffffc, 0xb1096ff400069004, 0x33189fdfd9789fea, 0x304962b3598a0adf]);
// 2^64
const R_64: Fr = Fr::from_u256([0xc98da28e0121c884, 0xe6f4f4a0c7363c67, 0xb2d6ebc4e92e7df1, 0x19ae57949d26242a]);
// 2^127
const R_127: Fr = Fr::from_u256([0x6795590d7c0fb897, 0xf31ac9ddd6045e06, 0xd6fadeb83e859487, 0x50d62b397f10dc09]);

pub fn regs_to_bn<Reg, T>(n: &[Reg]) -> BigNum
where
    Reg: Register<T>,
{
    let mut result = BigNum::new().unwrap();
    for i in n.iter().rev() {
        result = &result << Reg::bit_length();
        result = &result + &i.to_bn();
    }
    result
}

pub fn alloc_bool_regs<CS>(cs: &mut CS, x: &[bool]) -> Vec<RegBool>
where
    CS: ConstraintSystem<Bls12>,
{
    x.iter().map(|&i| RegBool::new(cs, i)).collect()
}

pub fn alloc_u64_regs<CS>(cs: &mut CS, x: &[u64]) -> Vec<RegU64>
where
    CS: ConstraintSystem<Bls12>,
{
    x.iter().map(|&i| RegU64::new(cs, i)).collect()
}

pub fn alloc_u127_regs<CS>(cs: &mut CS, x: &[u128]) -> Vec<RegU127>
where
    CS: ConstraintSystem<Bls12>,
{
    x.iter().map(|&i| RegU127::new(cs, i)).collect()
}

pub fn alloc_bool_input_regs<CS>(cs: &mut CS, x: &[bool]) -> Vec<RegBool>
where
    CS: ConstraintSystem<Bls12>,
{
    x.iter().map(|&i| RegBool::new_input(cs, i)).collect()
}

pub fn alloc_u64_input_regs<CS>(cs: &mut CS, x: &[u64]) -> Vec<RegU64>
where
    CS: ConstraintSystem<Bls12>,
{
    x.iter().map(|&i| RegU64::new_input(cs, i)).collect()
}

pub fn alloc_u127_input_regs<CS>(cs: &mut CS, x: &[u128]) -> Vec<RegU127>
where
    CS: ConstraintSystem<Bls12>,
{
    x.iter().map(|&i| RegU127::new_input(cs, i)).collect()
}

pub fn bool_to_scalar(value: bool) -> Fr {
    if value {
        ONE
    } else {
        ZERO
    }
}

pub fn u64_to_scalar(value: u64) -> Fr {
    Fr::from(value)
}

pub fn u127_to_scalar(value: u128) -> Fr {
    let mut value = value.to_le_bytes().to_vec();
    value.resize(32, 0);
    Fr::from_bytes_le(&value).unwrap()
}

pub trait Register<T>: Clone + Debug {
    fn word() -> Fr;

    fn bit_length() -> i32;

    fn zero<CS>(cs: &mut CS) -> Self
    where
        CS: ConstraintSystem<Bls12>;

    fn new<CS>(cs: &mut CS, value: T) -> Self
    where
        CS: ConstraintSystem<Bls12>;

    fn new_input<CS>(cs: &mut CS, value: T) -> Self
    where
        CS: ConstraintSystem<Bls12>;

    fn from_bn<CS>(cs: &mut CS, value: &BigNum, length: usize) -> Vec<Self>
    where
        CS: ConstraintSystem<Bls12>;

    fn from_scalar<CS>(cs: &mut CS, value: &Fr) -> Vec<Self>
    where
        CS: ConstraintSystem<Bls12>;

    fn duplicate<CS>(&self, cs: &mut CS) -> Self
    where
        CS: ConstraintSystem<Bls12>;

    fn variable(&self) -> Variable;

    fn scalar(&self) -> Fr;

    fn to_bn(&self) -> BigNum;
}

pub trait Operation {
    fn add<CS>(&self, cs: &mut CS, b: &Self, c: &Self) -> (Self, Self)
    where
        CS: ConstraintSystem<Bls12>,
        Self: Sized;

    fn mul<CS>(&self, cs: &mut CS, b: &Self, c: &Self, d: &Self) -> (Self, Self)
    where
        CS: ConstraintSystem<Bls12>,
        Self: Sized;
}

#[derive(Clone, Debug)]
pub struct RegBool {
    pub value: bool,
    pub variable: Variable,
}

impl Register<bool> for RegBool {
    fn word() -> Fr {
        R_1
    }

    fn bit_length() -> i32 {
        1
    }

    fn zero<CS>(cs: &mut CS) -> Self
    where
        CS: ConstraintSystem<Bls12>,
    {
        Self::new(cs, false)
    }

    fn new<CS>(cs: &mut CS, value: bool) -> Self
    where
        CS: ConstraintSystem<Bls12>,
    {
        Self {
            value,
            variable: alloc(cs, bool_to_scalar(value)),
        }
    }

    fn new_input<CS>(cs: &mut CS, value: bool) -> Self
    where
        CS: ConstraintSystem<Bls12>,
    {
        Self {
            value,
            variable: alloc_input(cs, bool_to_scalar(value)),
        }
    }

    fn from_bn<CS>(cs: &mut CS, value: &BigNum, length: usize) -> Vec<Self>
    where
        CS: ConstraintSystem<Bls12>,
    {
        bn_to_bool_arr(value, length).iter().map(|&i| Self::new(cs, i)).collect()
    }

    fn from_scalar<CS>(cs: &mut CS, value: &Fr) -> Vec<Self>
    where
        CS: ConstraintSystem<Bls12>,
    {
        Self::from_bn(cs, &BigNum::from_slice(&value.to_bytes_be()).unwrap(), 255)
    }

    fn duplicate<CS>(&self, cs: &mut CS) -> Self
    where
        CS: ConstraintSystem<Bls12>,
    {
        Self::new(cs, self.value)
    }

    fn variable(&self) -> Variable {
        self.variable
    }

    fn to_bn(&self) -> BigNum {
        BigNum::from_u32(self.value as u32).unwrap()
    }

    fn scalar(&self) -> Fr {
        bool_to_scalar(self.value)
    }
}

#[derive(Clone, Debug)]
pub struct RegU64 {
    pub value: u64,
    pub variable: Variable,
}

impl RegU64 {
    // a + b + c
    #[inline(always)]
    const fn adc(a: u64, b: u64, c: u64) -> (u64, u64) {
        let r = (a as u128) + (b as u128) + (c as u128);
        ((r >> 64) as u64, r as u64)
    }

    // a * b + c + d
    #[inline(always)]
    const fn mac(a: u64, b: u64, c: u64, d: u64) -> (u64, u64) {
        let r = (a as u128) * (b as u128) + (c as u128) + (d as u128);
        ((r >> 64) as u64, r as u64)
    }
}

impl Register<u64> for RegU64 {
    fn word() -> Fr {
        R_64
    }

    fn bit_length() -> i32 {
        64
    }

    fn zero<CS>(cs: &mut CS) -> Self
    where
        CS: ConstraintSystem<Bls12>,
    {
        Self::new(cs, 0)
    }

    fn new<CS>(cs: &mut CS, value: u64) -> Self
    where
        CS: ConstraintSystem<Bls12>,
    {
        Self {
            value,
            variable: alloc(cs, u64_to_scalar(value)),
        }
    }

    fn new_input<CS>(cs: &mut CS, value: u64) -> Self
    where
        CS: ConstraintSystem<Bls12>,
    {
        Self {
            value,
            variable: alloc_input(cs, u64_to_scalar(value)),
        }
    }

    fn from_bn<CS>(cs: &mut CS, value: &BigNum, length: usize) -> Vec<Self>
    where
        CS: ConstraintSystem<Bls12>,
    {
        bn_to_u64_arr(value, length).iter().map(|&i| Self::new(cs, i)).collect()
    }

    fn from_scalar<CS>(cs: &mut CS, value: &Fr) -> Vec<Self>
    where
        CS: ConstraintSystem<Bls12>,
    {
        Self::from_bn(cs, &BigNum::from_slice(&value.to_bytes_be()).unwrap(), 4)
    }

    fn duplicate<CS>(&self, cs: &mut CS) -> Self
    where
        CS: ConstraintSystem<Bls12>,
    {
        Self::new(cs, self.value)
    }

    fn variable(&self) -> Variable {
        self.variable
    }

    fn to_bn(&self) -> BigNum {
        BigNum::from_slice(&self.value.to_be_bytes()).unwrap()
    }

    fn scalar(&self) -> Fr {
        u64_to_scalar(self.value)
    }
}

impl Operation for RegU64 {
    fn add<CS>(&self, cs: &mut CS, b: &Self, c: &Self) -> (Self, Self)
    where
        CS: ConstraintSystem<Bls12>,
    {
        let a = self;
        let (q, r) = Self::adc(a.value, b.value, c.value);
        let q = Self::new(cs, q);
        let r = Self::new(cs, r);
        cs.enforce(
            || "a + b + c = q * N + r",
            |lc| lc + a.variable + b.variable + c.variable,
            |lc| lc + CS::one(),
            |lc| lc + (Self::word(), q.variable) + r.variable,
        );
        (q, r)
    }

    fn mul<CS>(&self, cs: &mut CS, b: &Self, c: &Self, d: &Self) -> (Self, Self)
    where
        CS: ConstraintSystem<Bls12>,
    {
        let a = self;
        let (q, r) = Self::mac(a.value, b.value, c.value, d.value);
        let q = Self::new(cs, q);
        let r = Self::new(cs, r);
        cs.enforce(
            || "a * b + c + d = q * N + r",
            |lc| lc + a.variable,
            |lc| lc + b.variable,
            |lc| lc + (Self::word(), q.variable) + r.variable - c.variable - d.variable,
        );
        (q, r)
    }
}

#[derive(Clone, Debug)]
pub struct RegU127 {
    pub value: u128,
    pub variable: Variable,
}

impl RegU127 {
    const W_127: u128 = 170141183460469231731687303715884105727;
    const W_64: u128 = 18446744073709551615;

    // a + b + c
    #[inline(always)]
    const fn adc(a: u128, b: u128, c: u128) -> (u128, u128) {
        let s = a + b;
        let q = s >> 127;
        let r = s & Self::W_127;
        let s = r + c;
        let q = q + (s >> 127);
        let r = s & Self::W_127;
        (q, r)
    }

    // a * b + c + d
    #[inline(always)]
    const fn mac(a: u128, b: u128, c: u128, d: u128) -> (u128, u128) {
        let x = Self::lo(a) * Self::lo(b);
        let s0 = Self::lo(x);

        let x = Self::hi(a) * Self::lo(b) + Self::hi(x);
        let s2 = Self::hi(x);

        let x = Self::lo(x) + Self::lo(a) * Self::hi(b);
        let s1 = Self::lo(x);

        let x = s2 + Self::hi(a) * Self::hi(b) + Self::hi(x);
        let s2 = Self::lo(x);
        let s3 = Self::hi(x);

        let q = s3 << 64 | s2;
        let r = s1 << 64 | s0;
        let q = q << 1 | r >> 127;
        let r = r & Self::W_127;

        let (qq, r) = Self::adc(r, c, d);
        let q = q + qq;

        (q, r)
    }

    #[inline(always)]
    const fn hi(x: u128) -> u128 {
        x >> 64
    }

    #[inline(always)]
    const fn lo(x: u128) -> u128 {
        x & Self::W_64
    }
}

impl Register<u128> for RegU127 {
    fn word() -> Fr {
        R_127
    }

    fn bit_length() -> i32 {
        127
    }

    fn zero<CS>(cs: &mut CS) -> Self
    where
        CS: ConstraintSystem<Bls12>,
    {
        Self::new(cs, 0)
    }

    fn new<CS>(cs: &mut CS, value: u128) -> Self
    where
        CS: ConstraintSystem<Bls12>,
    {
        Self {
            value,
            variable: alloc(cs, u127_to_scalar(value)),
        }
    }

    fn new_input<CS>(cs: &mut CS, value: u128) -> Self
    where
        CS: ConstraintSystem<Bls12>,
    {
        Self {
            value,
            variable: alloc_input(cs, u127_to_scalar(value)),
        }
    }

    fn from_bn<CS>(cs: &mut CS, value: &BigNum, length: usize) -> Vec<Self>
    where
        CS: ConstraintSystem<Bls12>,
    {
        bn_to_u127_arr(value, length)
            .iter()
            .map(|&i| Self::new(cs, i))
            .collect()
    }

    fn from_scalar<CS>(cs: &mut CS, value: &Fr) -> Vec<Self>
    where
        CS: ConstraintSystem<Bls12>,
    {
        Self::from_bn(cs, &BigNum::from_slice(&value.to_bytes_be()).unwrap(), 3)
    }

    fn duplicate<CS>(&self, cs: &mut CS) -> Self
    where
        CS: ConstraintSystem<Bls12>,
    {
        Self::new(cs, self.value)
    }

    fn variable(&self) -> Variable {
        self.variable
    }

    fn to_bn(&self) -> BigNum {
        BigNum::from_slice(&self.value.to_be_bytes()).unwrap()
    }

    fn scalar(&self) -> Fr {
        u127_to_scalar(self.value)
    }
}

impl Operation for RegU127 {
    fn add<CS>(&self, cs: &mut CS, b: &Self, c: &Self) -> (Self, Self)
    where
        CS: ConstraintSystem<Bls12>,
    {
        let a = self;
        let (q, r) = Self::adc(a.value, b.value, c.value);
        let q = Self::new(cs, q);
        let r = Self::new(cs, r);
        cs.enforce(
            || "a + b + c = q * N + r",
            |lc| lc + a.variable + b.variable + c.variable,
            |lc| lc + CS::one(),
            |lc| lc + (Self::word(), q.variable) + r.variable,
        );
        (q, r)
    }

    fn mul<CS>(&self, cs: &mut CS, b: &Self, c: &Self, d: &Self) -> (Self, Self)
    where
        CS: ConstraintSystem<Bls12>,
    {
        let a = self;
        let (q, r) = Self::mac(a.value, b.value, c.value, d.value);
        let q = Self::new(cs, q);
        let r = Self::new(cs, r);
        cs.enforce(
            || "a * b + c + d = q * N + r",
            |lc| lc + a.variable,
            |lc| lc + b.variable,
            |lc| lc + (Self::word(), q.variable) + r.variable - c.variable - d.variable,
        );
        (q, r)
    }
}

pub fn into_regs<CS, Reg, T>(cs: &mut CS, n: &Fr, n_var: &Variable) -> Vec<Reg>
where
    CS: ConstraintSystem<Bls12>,
    Reg: Register<T>,
{
    let r = Reg::from_scalar(cs, &n);
    let mut lc = LinearCombination::zero();
    for i in (0..r.len()).rev() {
        lc = LinearCombination::zero() + (Reg::word(), &lc) + r[i].variable();
    }
    cs.enforce(|| "n = r", |lc| lc + *n_var, |lc| lc + CS::one(), |_| lc);
    r
}

pub fn regs_equal<CS, Reg, T>(cs: &mut CS, x: &[Reg], y: &[Reg])
where
    CS: ConstraintSystem<Bls12>,
    Reg: Register<T>,
{
    let mut lhs = LinearCombination::zero();
    let mut rhs = LinearCombination::zero();
    for i in (0..x.len()).rev() {
        lhs = LinearCombination::zero() + (Reg::word(), &lhs) + x[i].variable();
    }
    for i in (0..y.len()).rev() {
        rhs = LinearCombination::zero() + (Reg::word(), &rhs) + y[i].variable();
    }
    cs.enforce(|| "lhs = rhs", |_| lhs, |lc| lc + CS::one(), |_| rhs);
}

pub fn regs_select<CS, Reg, T>(cs: &mut CS, x: &[Reg], y: &[Reg], b: &RegBool) -> Vec<Reg>
where
    CS: ConstraintSystem<Bls12>,
    Reg: Register<T>,
{
    let z = if b.value { y } else { x };
    let z: Vec<_> = z.iter().map(|i| i.duplicate(cs)).collect();

    // prove that I know `s` s.t. `(1 - b) * x + b * y = z`
    // (1 - b) * x + b * y = b * (y - x) + x = z -> b * (y - x) = z - x
    let mut lhs = LinearCombination::zero();
    let mut rhs = LinearCombination::zero();
    for i in (0..x.len()).rev() {
        lhs = LinearCombination::zero() + (Reg::word(), &lhs) + y[i].variable() - x[i].variable();
    }
    for i in (0..x.len()).rev() {
        rhs = LinearCombination::zero() + (Reg::word(), &rhs) + z[i].variable() - x[i].variable();
    }
    cs.enforce(|| "b * (y - x) = z - x", |_| lhs, |lc| lc + b.variable(), |_| rhs);
    z
}

pub fn regs_add<CS, Reg, T>(cs: &mut CS, x: &[Reg], y: &[Reg]) -> Vec<Reg>
where
    CS: ConstraintSystem<Bls12>,
    Reg: Register<T> + Operation,
{
    let length = cmp::max(x.len(), y.len());
    let mut z = vec![];
    let mut c = Reg::zero(cs);
    for i in 0..length {
        let (q, r) = if i >= x.len() {
            let a = Reg::zero(cs);
            a.add(cs, &y[i], &c)
        } else if i >= y.len() {
            let b = Reg::zero(cs);
            x[i].add(cs, &b, &c)
        } else {
            x[i].add(cs, &y[i], &c)
        };
        z.push(r);
        c = q;
    }
    z.push(c);
    z
}

pub fn regs_mul<CS, Reg, T>(cs: &mut CS, x: &[Reg], y: &[Reg]) -> Vec<Reg>
where
    CS: ConstraintSystem<Bls12>,
    Reg: Register<T> + Operation,
{
    let mut z = vec![Reg::zero(cs); x.len() + y.len()];
    for j in 0..y.len() {
        let mut c = Reg::zero(cs);
        for i in 0..x.len() {
            let (q, r) = x[i].mul(cs, &y[j], &z[i + j], &c);
            z[i + j] = r;
            c = q;
        }
        z[j + x.len()] = c;
    }
    z
}

pub fn regs_mod<CS, Reg, T>(cs: &mut CS, n: &[Reg], m: &[Reg]) -> Vec<Reg>
where
    CS: ConstraintSystem<Bls12>,
    Reg: Register<T> + Operation,
{
    let (q, r) = {
        let n = regs_to_bn(n);
        let m = regs_to_bn(m);
        div_mod(&n, &m)
    };
    let q = Reg::from_bn(cs, &q, if n.len() > m.len() { n.len() - m.len() } else { 0 } + 1);
    let r = Reg::from_bn(cs, &r, m.len());
    let qm = regs_mul(cs, &q, m);
    let nn = regs_add(cs, &qm, &r);
    regs_equal(cs, n, &nn);
    r
}

pub fn regs_mod_mul<CS, Reg, T>(cs: &mut CS, a: &[Reg], b: &[Reg], m: &[Reg]) -> Vec<Reg>
where
    CS: ConstraintSystem<Bls12>,
    Reg: Register<T> + Operation,
{
    let r = regs_mul(cs, a, b);
    regs_mod(cs, &r, m)
}

pub fn regs_mod_exp<CS, Reg, T>(cs: &mut CS, x: &[Reg], e: &[RegBool], n: &[Reg]) -> Vec<Reg>
where
    CS: ConstraintSystem<Bls12>,
    Reg: Register<T> + Operation,
{
    let mut r = Reg::from_bn(cs, &BigNum::from_u32(1).unwrap(), n.len());

    let mut x = x.to_vec();

    for i in e {
        let rr = regs_mod_mul(cs, &r, &x, n);
        r = regs_select(cs, &r, &rr, i);
        x = regs_mod_mul(cs, &x, &x, n);
    }
    r
}
