#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Authorization {
    pub total_debit: u64,
}

pub mod u128_math {
    pub const LIMB_BASE: u64 = 0x1_0000_0000u64;
    pub const LIMB_MASK: u64 = 0xFFFF_FFFFu64;
    pub const LIMB_SHIFT: u64 = 32u64;
    pub const FEE_RATE_MUL_VALUE: u64 = 1_000_000u64;

    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub struct U128Words {
        pub w0: u64,
        pub w1: u64,
        pub w2: u64,
        pub w3: u64,
    }

    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub struct DivStep {
        pub quot: u64,
        pub rem: u64,
    }

    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub struct DivResult {
        pub q0: u64,
        pub q1: u64,
        pub q2: u64,
        pub q3: u64,
        pub rem: u64,
    }

    #[inline]
    pub fn split_u128(amount: u64, fee: u64) -> U128Words {
        U128Words {
            w0: amount & LIMB_MASK,
            w1: amount >> LIMB_SHIFT,
            w2: fee & LIMB_MASK,
            w3: fee >> LIMB_SHIFT,
        }
    }

    #[inline]
    pub fn div_step(rem: u64, word: u64) -> DivStep {
        let num: u64 = rem * LIMB_BASE + word;
        DivStep {
            quot: num / FEE_RATE_MUL_VALUE,
            rem: num % FEE_RATE_MUL_VALUE,
        }
    }

    #[inline]
    pub fn div_word_chain(words: U128Words) -> DivResult {
        let step3: DivStep = div_step(0u64, words.w3);
        let step2: DivStep = div_step(step3.rem, words.w2);
        let step1: DivStep = div_step(step2.rem, words.w1);
        let step0: DivStep = div_step(step1.rem, words.w0);
        DivResult {
            q0: step0.quot,
            q1: step1.quot,
            q2: step2.quot,
            q3: step3.quot,
            rem: step0.rem,
        }
    }

    #[inline]
    pub fn round_up_quotient(div: DivResult) -> U128Words {
        let inc: u64 = if div.rem > 0u64 { 1u64 } else { 0u64 };
        let s0: u64 = div.q0 + inc;
        let r0: u64 = s0 & LIMB_MASK;
        let c0: u64 = s0 >> LIMB_SHIFT;
        let s1: u64 = div.q1 + c0;
        let r1: u64 = s1 & LIMB_MASK;
        let s2: u64 = div.q2;
        let r2: u64 = s2 & LIMB_MASK;
        let c2: u64 = s2 >> LIMB_SHIFT;
        let r3: u64 = div.q3 + c2;
        U128Words {
            w0: r0,
            w1: r1,
            w2: r2,
            w3: r3,
        }
    }

    #[inline]
    pub fn try_into_u64(words: U128Words) -> Option<u64> {
        if words.w2 != 0u64 || words.w3 != 0u64 {
            None
        } else {
            Some(words.w1 * LIMB_BASE + words.w0)
        }
    }

    #[inline]
    pub fn div_round_up_fee(amount: u64, fee: u64) -> Option<u64> {
        let words: U128Words = split_u128(amount, fee);
        let div: DivResult = div_word_chain(words);
        let rounded: U128Words = round_up_quotient(div);
        try_into_u64(rounded)
    }
}

pub mod settlement {
    use crate::Authorization;
    use crate::u128_math;

    pub const PRINCIPAL_DIVISOR: u64 = 2u64;

    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub struct WhirlpoolQuote {
        pub principal_share: u64,
        pub gross_fee: u64,
        pub total_debit: u64,
    }

    #[inline]
    pub fn build_quote(amount: u64, fee: u64) -> Option<WhirlpoolQuote> {
        let principal_share: u64 = amount / PRINCIPAL_DIVISOR;
        let gross_fee: u64 = u128_math::div_round_up_fee(amount, fee)?;
        let total_debit: u64 = principal_share.checked_add(gross_fee)?;
        Some(WhirlpoolQuote {
            principal_share,
            gross_fee,
            total_debit,
        })
    }

    #[inline]
    pub fn verify_affordability(balance: u64, quote: WhirlpoolQuote) -> Option<Authorization> {
        if quote.total_debit <= balance {
            Some(Authorization {
                total_debit: quote.total_debit,
            })
        } else {
            None
        }
    }
}

/// Authorize a concentrated-liquidity Whirlpool swap debit against `balance`.
///
/// In exact integer arithmetic:
/// - `principal_share = floor(amount / 2)`
/// - `gross_fee = ceil((amount + fee * 2^64) / 1_000_000)`
/// - `total_debit = principal_share + gross_fee`
///
/// The payment is authorized iff `total_debit <= balance`.
/// Production code in this crate operates on `u64` words only (`u128` is not used).
pub fn authorize(balance: u64, amount: u64, fee: u64) -> Option<Authorization> {
    let quote: settlement::WhirlpoolQuote = settlement::build_quote(amount, fee)?;
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
    fn rounds_up_fractional_fee() {
        // amount = 100, fee = 0:
        // principal_share = 50, gross_fee = ceil(100 / 1_000_000) = 1 -> total = 51
        assert_eq!(authorize(51, 100, 0), Some(Authorization { total_debit: 51 }));
        assert_eq!(authorize(50, 100, 0), None);
    }

    #[test]
    fn multi_word_carry_across_q0_boundary() {
        // Choose X = 1_000_000 * 0xFFFF_FFFF + 1 = 4_294_967_295_000_001 (fee = 0):
        // gross_fee = 0x1_0000_0000 = 4_294_967_296
        // principal_share = 2_147_483_647_500_000
        let amount: u64 = 4_294_967_295_000_001u64;
        let expected: u64 = (amount / 2) + 4_294_967_296u64;
        assert_eq!(
            authorize(expected, amount, 0),
            Some(Authorization {
                total_debit: expected
            })
        );
    }
}
