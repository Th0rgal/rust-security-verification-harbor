#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Authorization {
    pub total_debit: u64,
}

pub mod monty31 {
    pub const BABY_BEAR_P: u64 = 2_013_265_921u64;
    pub const BABY_BEAR_MU: u64 = 2_281_701_377u64;
    pub const LIMB_BASE: u64 = 4_294_967_296u64;
    pub const LIMB_MASK: u64 = 0xFFFF_FFFFu64;

    #[inline]
    pub fn pack_transcript(amount: u64, fee: u64) -> u64 {
        let low: u64 = amount & LIMB_MASK;
        let high: u64 = fee % BABY_BEAR_P;
        low + high * LIMB_BASE
    }

    #[inline]
    pub fn monty_quotient(x: u64) -> u64 {
        let x_lo: u64 = x & LIMB_MASK;
        (x_lo * BABY_BEAR_MU) & LIMB_MASK
    }

    /// Montgomery reduction of `x < P * 2^32` over the BabyBear prime
    /// `P = 2013265921` (`MU = P^-1 mod 2^32 = 2281701377`).
    #[inline]
    pub fn monty_reduce(x: u64) -> u64 {
        let t: u64 = monty_quotient(x);
        let u: u64 = t * BABY_BEAR_P;
        let (diff, borrow) = x.overflowing_sub(u);
        let hi: u64 = diff >> 32u64;
        if borrow {
            hi + BABY_BEAR_P - LIMB_BASE
        } else {
            hi
        }
    }
}

pub mod settlement {
    use crate::Authorization;
    use crate::monty31;

    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub struct PlonkyQuote {
        pub principal: u64,
        pub monty_surcharge: u64,
        pub total_debit: u64,
    }

    #[inline]
    pub fn build_quote(amount: u64, fee: u64) -> Option<PlonkyQuote> {
        let transcript: u64 = monty31::pack_transcript(amount, fee);
        let monty_surcharge: u64 = monty31::monty_reduce(transcript);
        let total_debit: u64 = amount.checked_add(monty_surcharge)?;
        Some(PlonkyQuote {
            principal: amount,
            monty_surcharge,
            total_debit,
        })
    }

    #[inline]
    pub fn verify_affordability(balance: u64, quote: PlonkyQuote) -> Option<Authorization> {
        if quote.total_debit <= balance {
            Some(Authorization {
                total_debit: quote.total_debit,
            })
        } else {
            None
        }
    }
}

/// Authorize a Plonky3 BabyBear Montgomery settlement against `balance`.
///
/// In exact integer arithmetic:
/// - `P = 2013265921` (BabyBear prime), `R = 2^32 = 4294967296`, `R_INV = 943718400` (`R * R_INV == 1 mod P`)
/// - `transcript = (amount mod 2^32) + (fee mod P) * 2^32`
/// - `monty_surcharge = (transcript * R_INV) mod P`
/// - `total_debit = amount + monty_surcharge`
///
/// The payment is authorized iff `total_debit <= balance`.
/// Production code in this crate operates on `u64` words only (`u128` is not used).
pub fn authorize(balance: u64, amount: u64, fee: u64) -> Option<Authorization> {
    let quote: settlement::PlonkyQuote = settlement::build_quote(amount, fee)?;
    settlement::verify_affordability(balance, quote)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn zero_payment_is_authorized() {
        assert_eq!(authorize(0, 0, 0), Some(Authorization { total_debit: 0 }));
    }

    #[test]
    fn montgomery_identity_element() {
        // transcript = R = 2^32 (amount = 0, fee = 1):
        // monty_surcharge = (R * R_INV) mod P = 1
        assert_eq!(authorize(1, 0, 1), Some(Authorization { total_debit: 1 }));
        assert_eq!(authorize(0, 0, 1), None);
    }

    #[test]
    fn small_transcript_reduction_matches_policy() {
        // amount = 4294967296 (low = 0), fee = 5:
        // transcript = 5 * 2^32 -> monty_surcharge = 5
        // total_debit = 4294967301
        assert_eq!(
            authorize(4_294_967_301, 4_294_967_296, 5),
            Some(Authorization {
                total_debit: 4_294_967_301
            })
        );
    }
}
