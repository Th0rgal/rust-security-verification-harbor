#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Authorization {
    pub total_debit: u64,
}

pub mod constants {
    /// Basis-point denominator (100% = 10_000 bps).
    pub const BPS_DENOM: u64 = 10_000;
    /// Ceiling-division bias for `BPS_DENOM` (`BPS_DENOM - 1`).
    pub const BPS_MAX_REM: u64 = 9_999;
    /// Floor quotient of `2^64` by `BPS_DENOM`: `floor(2^64 / 10_000)`.
    pub const U64_MOD_BPS_QUOT: u64 = 1_844_674_407_370_955;
    /// Exact remainder of `2^64` modulo `BPS_DENOM`: `2^64 % 10_000 = 1_616`.
    pub const U64_MOD_BPS_REM: u64 = 1_616;
    /// Protocol tier rebate divisor (10% rebate on gross fee, rounded down).
    pub const REBATE_DIVISOR: u64 = 10;
    /// Reference liquidity band threshold for diagnostics.
    pub const HIGH_VALUE_THRESHOLD: u64 = 1_000_000_000_000;
}

pub mod bps_math {
    use crate::constants::*;

    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub struct SumFold {
        pub low_word: u64,
        pub wrapped_u64: bool,
    }

    /// Folds the unbounded notional sum `amount + fee` into a 64-bit low word
    /// and an explicit `2^64` carry flag without `u128` promotion.
    #[inline]
    pub fn fold_u64_sum(amount: u64, fee: u64) -> SumFold {
        let low_word = amount.wrapping_add(fee);
        let wrapped_u64 = low_word < amount;
        SumFold { low_word, wrapped_u64 }
    }

    /// Computes the floor basis-point levy `floor((amount + fee) / 10_000)`
    /// in pure `u64` arithmetic across the `2^64` boundary.
    #[inline]
    pub fn floor_div_bps_folded(fold: SumFold) -> u64 {
        if fold.wrapped_u64 {
            let rem_sum = (fold.low_word % BPS_DENOM) + U64_MOD_BPS_REM;
            U64_MOD_BPS_QUOT + (fold.low_word / BPS_DENOM) + (rem_sum / BPS_DENOM)
        } else {
            fold.low_word / BPS_DENOM
        }
    }

    /// Computes the ceiling basis-point levy `ceil((amount + fee) / 10_000)`
    /// in pure `u64` arithmetic from a folded 64-bit sum.
    #[inline]
    pub fn ceil_div_bps_folded(fold: SumFold) -> u64 {
        if fold.wrapped_u64 {
            let folded_rem = (fold.low_word % BPS_DENOM) + U64_MOD_BPS_REM;
            U64_MOD_BPS_QUOT + (fold.low_word / BPS_DENOM) + ((folded_rem + BPS_MAX_REM) / BPS_DENOM)
        } else {
            let biased = fold.low_word.wrapping_add(BPS_MAX_REM);
            if biased < fold.low_word {
                (fold.low_word / BPS_DENOM) + ((biased + U64_MOD_BPS_REM) / BPS_DENOM)
            } else {
                biased / BPS_DENOM
            }
        }
    }
}

pub mod rebate {
    use crate::constants::*;

    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub struct FeeBreakdown {
        pub gross_fee: u64,
        pub rebate: u64,
        pub net_fee: u64,
    }

    /// Computes the floor tier rebate `floor(gross_fee / 10)` in favor of the protocol.
    #[inline]
    pub fn tier_rebate_floor(gross_fee: u64) -> u64 {
        gross_fee / REBATE_DIVISOR
    }

    /// Assembles the gross fee, floor rebate, and net settlement fee `gross_fee - rebate`.
    #[inline]
    pub fn compute_fee_breakdown(gross_fee: u64) -> FeeBreakdown {
        let rebate = tier_rebate_floor(gross_fee);
        let net_fee = gross_fee - rebate;
        FeeBreakdown { gross_fee, rebate, net_fee }
    }

    /// Diagnostic helper checking whether a fee breakdown qualifies as high-volume.
    #[inline]
    pub fn is_high_volume_levy(breakdown: FeeBreakdown) -> bool {
        breakdown.gross_fee >= HIGH_VALUE_THRESHOLD
    }
}

pub mod quote {
    use crate::Authorization;
    use crate::rebate::FeeBreakdown;

    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub struct SettlementQuote {
        pub principal: u64,
        pub net_fee: u64,
        pub total_debit: u64,
    }

    /// Combines the payment principal `amount` with `breakdown.net_fee`, rejecting
    /// if the resulting settlement debit exceeds `u64::MAX`.
    #[inline]
    pub fn build_settlement_quote(amount: u64, breakdown: FeeBreakdown) -> Option<SettlementQuote> {
        let total_debit = amount.checked_add(breakdown.net_fee)?;
        Some(SettlementQuote {
            principal: amount,
            net_fee: breakdown.net_fee,
            total_debit,
        })
    }

    /// Authorizes the settlement quote iff `quote.total_debit <= balance`.
    #[inline]
    pub fn verify_affordability(balance: u64, quote: SettlementQuote) -> Option<Authorization> {
        if quote.total_debit <= balance {
            Some(Authorization { total_debit: quote.total_debit })
        } else {
            None
        }
    }
}

/// Authorize a liquidity transfer in pure `u64` arithmetic before settlement.
///
/// Policy over exact unbounded integers (`balance`, `amount`, `fee`):
/// 1. The gross protocol fee is the combined basis `amount + fee` divided by
///    `BPS_DENOM` (`10_000`), rounded up (`ceil((amount + fee) / 10_000)`).
/// 2. The tier rebate is `gross_fee` divided by `REBATE_DIVISOR` (`10`),
///    rounded down (`floor(gross_fee / 10)`).
/// 3. The net settlement debit is `amount + (gross_fee - rebate)`.
///
/// Authorize every affordable transfer (`total_debit <= balance`) and return
/// the exact net settlement debit; reject every unaffordable transfer (`None`).
/// Target word constraint: production code must use `u64` only (no `u128`).
pub fn authorize(balance: u64, amount: u64, fee: u64) -> Option<Authorization> {
    let fold = bps_math::fold_u64_sum(amount, fee);
    let gross_fee = bps_math::ceil_div_bps_folded(fold);
    let breakdown = rebate::compute_fee_breakdown(gross_fee);
    let settlement_quote = quote::build_settlement_quote(amount, breakdown)?;
    quote::verify_affordability(balance, settlement_quote)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ordinary_settlement() {
        assert_eq!(authorize(100_012, 100_000, 25_000).unwrap().total_debit, 100_012);
        assert_eq!(authorize(100_011, 100_000, 25_000), None);
    }

    #[test]
    fn ceiling_rounding_and_rebate() {
        assert_eq!(authorize(2, 1, 0).unwrap().total_debit, 2);
        assert_eq!(authorize(9, 0, 99_991).unwrap().total_debit, 9);
        assert_eq!(authorize(8, 0, 99_991), None);
    }

    #[test]
    fn wide_basis_carry_folding() {
        let expected = 1_660_206_966_643_862;
        assert_eq!(authorize(expected, 10_000, u64::MAX).unwrap().total_debit, expected);
        assert_eq!(authorize(expected - 1, 10_000, u64::MAX), None);
    }

    #[test]
    fn ceiling_bias_wrap_at_u64_max() {
        let expected = 1_660_206_966_633_861;
        assert_eq!(authorize(expected, 0, u64::MAX).unwrap().total_debit, expected);
        assert_eq!(authorize(expected - 1, 0, u64::MAX), None);
    }

    #[test]
    fn total_debit_overflow_rejected() {
        assert_eq!(authorize(u64::MAX, u64::MAX, 1), None);
        assert_eq!(authorize(u64::MAX, u64::MAX, u64::MAX), None);
    }

    #[test]
    fn floor_div_helper_matches_exact_quotient() {
        let fold = bps_math::fold_u64_sum(10_000, 18_446_744_073_709_550_000);
        assert_eq!(bps_math::floor_div_bps_folded(fold), 1_844_674_407_370_956);
    }
}
