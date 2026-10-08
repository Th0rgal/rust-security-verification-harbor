#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Authorization {
    pub total_debit: u64,
}

pub mod mg10 {
    pub const MG10_DIVISOR: u64 = 0x8003u64;
    pub const MG10_RECIPROCAL: u64 = 0xFFF4u64;
    pub const LIMB_MASK: u64 = 0xFFFFu64;
    pub const SUB_BIAS: u64 = 0xC000_0000u64;

    /// Exact 2-by-1 normalized division for D = 32771.
    /// Given u1 < D and u0 < 65536, the dividend fits in u64.
    /// Returns floor((u1 * 65536 + u0) / D).
    #[inline]
    pub fn div_2x1_mg10(u1: u64, u0: u64) -> u64 {
        (u1 * 65536u64 + u0) / MG10_DIVISOR
    }

}

pub mod settlement {
    use crate::Authorization;
    use crate::mg10;

    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub struct RuintQuote {
        pub u1: u64,
        pub u0: u64,
        pub quotient: u64,
        pub total_debit: u64,
    }

    #[inline]
    pub fn build_quote(amount: u64, fee: u64) -> Option<RuintQuote> {
        let u1: u64 = fee % mg10::MG10_DIVISOR;
        let u0: u64 = amount & mg10::LIMB_MASK;
        let quotient: u64 = mg10::div_2x1_mg10(u1, u0);
        let total_debit: u64 = (amount >> 1u64) + quotient;
        Some(RuintQuote {
            u1,
            u0,
            quotient,
            total_debit,
        })
    }

    #[inline]
    pub fn verify_affordability(balance: u64, quote: RuintQuote) -> Option<Authorization> {
        if quote.total_debit <= balance {
            Some(Authorization {
                total_debit: quote.total_debit,
            })
        } else {
            None
        }
    }
}

/// Authorize a Ruint Möller-Granlund 2-by-1 normalized division settlement against `balance`.
///
/// In exact integer arithmetic:
/// - `D = 32771` (`0x8003`), `B = 2^16 = 65536`
/// - `u1 = fee mod D`, `u0 = amount mod B`
/// - `quotient = floor((u1 * B + u0) / D)`
/// - `total_debit = floor(amount / 2) + quotient`
///
/// The payment is authorized iff `total_debit <= balance`.
/// Production code in this crate operates on `u64` words only (`u128` is not used).
pub fn authorize(balance: u64, amount: u64, fee: u64) -> Option<Authorization> {
    let quote: settlement::RuintQuote = settlement::build_quote(amount, fee)?;
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
    fn exact_multiple_of_divisor() {
        assert_eq!(authorize(1, 0, 1), Some(Authorization { total_debit: 1 }));
        assert_eq!(authorize(0, 0, 1), None);
    }

    #[test]
    fn two_limb_dividend_matches_policy() {
        assert_eq!(
            authorize(16_405, 32_771, 10),
            Some(Authorization {
                total_debit: 16_405
            })
        );
    }

    #[test]
    fn reciprocal_underestimate_regression() {
        assert_eq!(mg10::div_2x1_mg10(16384, 65534), 32767);
        assert_eq!(authorize(65533, 65534, 16384), None);
        assert_eq!(
            authorize(65534, 65534, 16384),
            Some(Authorization { total_debit: 65534 })
        );
    }

    #[test]
    fn maximum_amount_and_limb_values() {
        // The largest two-limb dividend has quotient 65535.
        assert_eq!(mg10::div_2x1_mg10(32770, 65535), 65535);
        let amount = u64::MAX;
        let fee = 32770;
        let debit = (amount / 2) + 65535;
        assert_eq!(authorize(debit - 1, amount, fee), None);
        assert_eq!(authorize(debit, amount, fee), Some(Authorization { total_debit: debit }));
        assert_eq!(authorize(u64::MAX, amount, fee), Some(Authorization { total_debit: debit }));
    }

}
