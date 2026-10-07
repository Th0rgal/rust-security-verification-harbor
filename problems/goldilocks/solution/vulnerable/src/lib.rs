#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Authorization {
    pub total_debit: u64,
}

pub mod field {
    pub const GOLDILOCKS_MODULUS: u64 = 0xFFFF_FFFF_0000_0001u64;
    pub const GOLDILOCKS_EPSILON: u64 = 0xFFFF_FFFFu64;
    pub const LIMB_SHIFT: u64 = 32u64;

    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub struct TranscriptLimbs {
        pub low: u64,
        pub mid: u64,
        pub high: u64,
    }

    #[inline]
    pub fn split_transcript(amount: u64, fee: u64) -> TranscriptLimbs {
        TranscriptLimbs {
            low: amount,
            mid: fee & GOLDILOCKS_EPSILON,
            high: fee >> LIMB_SHIFT,
        }
    }

    /// Fold the top 32-bit limb `high * 2^96` into `low` using `2^96 == -1 (mod P)`.
    #[inline]
    pub fn fold_high_limb(low: u64, high: u64) -> u64 {
        let (low2, borrow) = low.overflowing_sub(high);
        if borrow {
            low2.wrapping_add(GOLDILOCKS_MODULUS)
        } else {
            low2
        }
    }

    /// Fold the middle 32-bit limb `mid * 2^64` using `2^64 == 2^32 - 1 (mod P)`.
    #[inline]
    pub fn fold_mid_limb(low2: u64, mid: u64) -> u64 {
        let product: u64 = mid * GOLDILOCKS_EPSILON;
        let (sum1, carry1) = low2.overflowing_add(product);
        if carry1 {
            sum1.wrapping_add(GOLDILOCKS_EPSILON)
        } else {
            sum1
        }
    }

    #[inline]
    pub fn canonicalize(folded: u64) -> u64 {
        if folded >= GOLDILOCKS_MODULUS {
            folded - GOLDILOCKS_MODULUS
        } else {
            folded
        }
    }

    /// Reduce the 128-bit integer `amount + fee * 2^64` modulo the Goldilocks
    /// prime `P = 2^64 - 2^32 + 1 = 18446744069414584321` in pure `u64`.
    #[inline]
    pub fn reduce_128(amount: u64, fee: u64) -> u64 {
        let limbs: TranscriptLimbs = split_transcript(amount, fee);
        let low2: u64 = fold_high_limb(limbs.low, limbs.high);
        let folded: u64 = fold_mid_limb(low2, limbs.mid);
        canonicalize(folded)
    }
}

pub mod settlement {
    use crate::Authorization;
    use crate::field;

    pub const PRINCIPAL_DIVISOR: u64 = 2u64;

    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub struct GoldilocksQuote {
        pub principal_share: u64,
        pub field_surcharge: u64,
        pub total_debit: u64,
    }

    #[inline]
    pub fn build_quote(amount: u64, fee: u64) -> Option<GoldilocksQuote> {
        let principal_share: u64 = amount / PRINCIPAL_DIVISOR;
        let field_surcharge: u64 = field::reduce_128(amount, fee);
        let total_debit: u64 = principal_share.checked_add(field_surcharge)?;
        Some(GoldilocksQuote {
            principal_share,
            field_surcharge,
            total_debit,
        })
    }

    #[inline]
    pub fn verify_affordability(balance: u64, quote: GoldilocksQuote) -> Option<Authorization> {
        if quote.total_debit <= balance {
            Some(Authorization {
                total_debit: quote.total_debit,
            })
        } else {
            None
        }
    }
}

/// Authorize a Goldilocks rollup settlement against `balance`.
///
/// In exact integer arithmetic:
/// - `P = 2^64 - 2^32 + 1 = 18446744069414584321` (Goldilocks prime)
/// - `principal_share = floor(amount / 2)`
/// - `field_surcharge = (amount + fee * 2^64) mod P`
/// - `total_debit = principal_share + field_surcharge`
///
/// The payment is authorized iff `total_debit <= balance`.
/// Production code in this crate operates on `u64` words only (`u128` is not used).
pub fn authorize(balance: u64, amount: u64, fee: u64) -> Option<Authorization> {
    let quote: settlement::GoldilocksQuote = settlement::build_quote(amount, fee)?;
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
    fn small_transcript_reduction_matches_policy() {
        assert_eq!(
            authorize(4_294_967_445, 100, 1),
            Some(Authorization {
                total_debit: 4_294_967_445
            })
        );
        assert_eq!(authorize(4_294_967_444, 100, 1), None);
    }

    #[test]
    fn canonicalizes_values_above_modulus() {
        assert_eq!(
            authorize(9_223_372_034_707_292_175, 18_446_744_069_414_584_331, 0),
            Some(Authorization {
                total_debit: 9_223_372_034_707_292_175
            })
        );
    }
}
