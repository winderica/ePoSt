use openssl::bn::{BigNum, BigNumContext, MsbOption};

pub fn duplicate(x: &BigNum) -> BigNum {
    &BigNum::new().unwrap() + x
}

pub fn generate_prime(bits: i32, safe: bool) -> BigNum {
    let mut r = BigNum::new().unwrap();
    r.generate_prime(bits, safe, None, None).unwrap();
    r
}

pub fn rshift1(x: &BigNum) -> BigNum {
    let mut r = BigNum::new().unwrap();
    r.rshift1(x).unwrap();
    r
}

pub fn rand(bits: i32) -> BigNum {
    let mut r = BigNum::new().unwrap();
    r.rand(bits, MsbOption::MAYBE_ZERO, false).unwrap();
    r
}

pub fn rand_range(max: &BigNum) -> BigNum {
    let mut r = BigNum::new().unwrap();
    max.rand_range(&mut r).unwrap();
    r
}

pub fn div_mod(x: &BigNum, m: &BigNum) -> (BigNum, BigNum) {
    let mut ctx = BigNumContext::new().unwrap();
    let mut q = BigNum::new().unwrap();
    let mut r = BigNum::new().unwrap();
    q.div_rem(&mut r, x, m, &mut ctx).unwrap();
    (q, r)
}

pub fn mod_inv(x: &BigNum, m: &BigNum, ctx: &mut BigNumContext) -> BigNum {
    let mut r = BigNum::new().unwrap();
    r.mod_inverse(x, m, ctx).unwrap();
    r
}

pub fn mod_exp(x: &BigNum, e: &BigNum, m: &BigNum, ctx: &mut BigNumContext) -> BigNum {
    let mut r = BigNum::new().unwrap();
    r.mod_exp(x, e, m, ctx).unwrap();
    r
}

pub fn power_of_2(i: i32) -> BigNum {
    let mut r = BigNum::new().unwrap();
    r.set_bit(i).unwrap();
    r
}

pub fn bn_to_bool_arr(x: &BigNum, length: usize) -> Vec<bool> {
    let mut r: Vec<_> = (0..x.num_bits()).map(|i| x.is_bit_set(i)).collect();
    r.resize(length, false);
    r
}

pub fn bn_to_u64_arr(n: &BigNum, length: usize) -> Vec<u64> {
    let zero = BigNum::new().unwrap();
    let mut value = duplicate(n);
    let mut n = vec![];
    while &value != &zero {
        let q = &value >> 64;
        let r = &value - &(&q << 64);
        n.push(u64::from_be_bytes(r.to_vec_padded(8).unwrap().try_into().unwrap()));
        value = q;
    }
    n.resize(length, 0);
    n
}

pub fn bn_to_u127_arr(n: &BigNum, length: usize) -> Vec<u128> {
    let zero = BigNum::new().unwrap();
    let mut value = duplicate(n);
    let mut n = vec![];
    while &value != &zero {
        let q = &value >> 127;
        let r = &value - &(&q << 127);
        n.push(u128::from_be_bytes(r.to_vec_padded(16).unwrap().try_into().unwrap()));
        value = q;
    }
    n.resize(length, 0);
    n
}
