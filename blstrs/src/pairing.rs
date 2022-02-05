use crate::{Fp12, G1Affine, G2Affine};

use blst::*;

/// Execute a complete pairing operation `(p, q)`.
pub fn pairing(p: G1Affine, q: G2Affine) -> Fp12 {
    let mut tmp = blst_fp12::default();
    unsafe { blst_miller_loop(&mut tmp, &q.0, &p.0) };

    let mut out = blst_fp12::default();
    unsafe { blst_final_exp(&mut out, &tmp) };

    out.into()
}

macro_rules! impl_pairing {
    ($name:ident, $p:ty, $q:ty, $aggregate:ident, $aggregated:ident) => {
        /// Aggregate pairings efficiently.
        #[derive(Debug)]
        pub struct $name {
            v: Box<[u64]>,
        }

        impl $name {
            pub fn new(hash_or_encode: bool, dst: &[u8]) -> Self {
                let v: Vec<u64> = vec![0; unsafe { blst_pairing_sizeof() } / 8];
                let mut obj = Self {
                    v: v.into_boxed_slice(),
                };
                obj.init(hash_or_encode, dst);
                obj
            }

            pub fn init(&mut self, hash_or_encode: bool, dst: &[u8]) {
                unsafe { blst_pairing_init(self.ctx(), hash_or_encode, dst.as_ptr(), dst.len()) }
            }

            fn ctx(&mut self) -> *mut blst_pairing {
                self.v.as_mut_ptr() as *mut blst_pairing
            }

            fn const_ctx(&self) -> *const blst_pairing {
                self.v.as_ptr() as *const blst_pairing
            }

            pub fn aggregate(
                &mut self,
                pk: &$p,
                sig: Option<&$q>,
                msg: &[u8],
                aug: &[u8],
            ) -> Result<(), BLST_ERROR> {
                let res = unsafe {
                    $aggregate(
                        self.ctx(),
                        &pk.0,
                        match sig {
                            Some(sig) => &sig.0,
                            None => std::ptr::null(),
                        },
                        msg.as_ptr(),
                        msg.len(),
                        aug.as_ptr(),
                        aug.len(),
                    )
                };
                if res == BLST_ERROR::BLST_SUCCESS {
                    Ok(())
                } else {
                    Err(res)
                }
            }

            pub fn aggregated(gtsig: &mut Fp12, sig: &$q) {
                unsafe { $aggregated(&mut gtsig.0, &sig.0) }
            }

            pub fn commit(&mut self) {
                unsafe { blst_pairing_commit(self.ctx()) }
            }

            pub fn merge(&mut self, ctx1: &Self) -> Result<(), BLST_ERROR> {
                let res = unsafe { blst_pairing_merge(self.ctx(), ctx1.const_ctx()) };
                if res == BLST_ERROR::BLST_SUCCESS {
                    Ok(())
                } else {
                    Err(res)
                }
            }

            pub fn finalverify(&self, gtsig: Option<&Fp12>) -> bool {
                unsafe {
                    blst_pairing_finalverify(
                        self.const_ctx(),
                        match gtsig {
                            Some(ref gtsig) => &gtsig.0,
                            None => std::ptr::null(),
                        },
                    )
                }
            }
        }
    };
}

impl_pairing!(
    PairingG1G2,
    G1Affine,
    G2Affine,
    blst_pairing_aggregate_pk_in_g1,
    blst_aggregated_in_g2
);
impl_pairing!(
    PairingG2G1,
    G2Affine,
    G1Affine,
    blst_pairing_aggregate_pk_in_g2,
    blst_aggregated_in_g1
);

/// Returns true if all provided messages are distinctly unique, false otherwise.
pub fn unique_messages(msgs: &[&[u8]]) -> bool {
    let n_elems = msgs.len();

    if n_elems == 1 {
        return true;
    } else if n_elems == 2 {
        return msgs[0] != msgs[1];
    }

    let mut v: Vec<u64> = vec![0; unsafe { blst_uniq_sizeof(n_elems) } / 8];
    let ctx = v.as_mut_ptr() as *mut blst_uniq;

    unsafe { blst_uniq_init(ctx) };

    for msg in msgs.iter() {
        if !unsafe { blst_uniq_test(ctx, msg.as_ptr(), msg.len()) } {
            return false;
        }
    }

    true
}
