//! Protocol basis-point settlement fee and tier rebate schedule calculator.
//!
//! Given a 65-bit combined notional `sum = add_u64_with_carry(amount, fee)`:
//! 1. The gross settlement fee is the ceiling basis-point quotient
//!    `gross_fee = ceil((amount + fee) / BPS_DENOM)` (`BPS_DENOM = 10_000`).
//! 2. The tier rebate is the floor 10% discount
//!    `rebate = floor(gross_fee / REBATE_DIVISOR)` (`REBATE_DIVISOR = 10`).
//! 3. The net protocol settlement fee is `net_fee = gross_fee - rebate`.

use crate::constants::*;
use crate::word_math::{WordSum, ceil_div_bps_u64, floor_div_bps_u64, is_institutional_notional};

/// Active protocol fee schedule parameters.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FeeSchedule {
    pub bps_denom: u64,
    pub rebate_divisor: u64,
    pub maker_cap_divisor: u64,
}

/// Complete two-stage fee quote (`gross_fee`, `rebate`, `net_fee`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FeeQuote {
    pub gross_fee: u64,
    pub rebate: u64,
    pub net_fee: u64,
}

/// Returns the canonical protocol fee schedule configuration.
#[inline]
pub fn default_schedule() -> FeeSchedule {
    FeeSchedule {
        bps_denom: BPS_DENOM,
        rebate_divisor: REBATE_DIVISOR,
        maker_cap_divisor: MAKER_REBATE_CAP_DIVISOR,
    }
}

/// Computes the 10% floor tier rebate `floor(gross_fee / REBATE_DIVISOR)`.
#[inline]
pub fn compute_tier_rebate(gross_fee: u64) -> u64 {
    gross_fee / REBATE_DIVISOR
}

/// Computes a capped passive maker rebate `min(floor(gross_fee / 10), floor(cap_basis / 5))`
/// used by order-book analytics.
#[inline]
pub fn compute_capped_maker_rebate(gross_fee: u64, cap_basis: u64) -> u64 {
    let base_rebate: u64 = gross_fee / REBATE_DIVISOR;
    let max_rebate: u64 = cap_basis / MAKER_REBATE_CAP_DIVISOR;
    if base_rebate <= max_rebate {
        base_rebate
    } else {
        max_rebate
    }
}

/// Evaluates the active clearing protocol fee quote (`gross_fee`, `rebate`, `net_fee`)
/// from a 65-bit notional sum `sum = amount + fee` using ceiling basis-point division
/// and floor tier rebate.
#[inline]
pub fn evaluate_settlement_fee(sum: WordSum) -> FeeQuote {
    let gross_fee: u64 = ceil_div_bps_u64(sum);
    let rebate: u64 = compute_tier_rebate(gross_fee);
    let net_fee: u64 = gross_fee - rebate;
    FeeQuote {
        gross_fee,
        rebate,
        net_fee,
    }
}

/// Evaluates a passive liquidity floor fee quote (`floor((amount + fee) / 10_000)`)
/// for pool reserve telemetry.
#[inline]
pub fn evaluate_passive_floor_fee(sum: WordSum) -> FeeQuote {
    let gross_fee: u64 = floor_div_bps_u64(sum);
    let rebate: u64 = compute_tier_rebate(gross_fee);
    let net_fee: u64 = gross_fee - rebate;
    FeeQuote {
        gross_fee,
        rebate,
        net_fee,
    }
}

/// Computes the rounding spread (`ceil_quote.net_fee - floor_quote.net_fee`)
/// between active ceiling settlement and passive floor settlement.
#[inline]
pub fn compute_fee_rounding_spread(sum: WordSum) -> u64 {
    let ceil_q: FeeQuote = evaluate_settlement_fee(sum);
    let floor_q: FeeQuote = evaluate_passive_floor_fee(sum);
    ceil_q.net_fee - floor_q.net_fee
}

/// Classifies the fee tier code (`0 = zero`, `1 = retail`, `2 = institutional`)
/// for batch telemetry reporting.
#[inline]
pub fn classify_settlement_tier(sum: WordSum) -> u64 {
    if !sum.high_carry && sum.low_word == 0u64 {
        0u64
    } else if is_institutional_notional(sum) {
        2u64
    } else {
        1u64
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::word_math::add_u64_with_carry;

    #[test]
    fn settlement_fee_and_rebate_rounding() {
        let s = add_u64_with_carry(100_000u64, 25_000u64);
        let q = evaluate_settlement_fee(s);
        assert_eq!(q.gross_fee, 13u64);
        assert_eq!(q.rebate, 1u64);
        assert_eq!(q.net_fee, 12u64);

        let pf = evaluate_passive_floor_fee(s);
        assert_eq!(pf.gross_fee, 12u64);
        assert_eq!(pf.rebate, 1u64);
        assert_eq!(pf.net_fee, 11u64);
        assert_eq!(compute_fee_rounding_spread(s), 1u64);
    }

    #[test]
    fn capped_maker_rebate_and_default_schedule() {
        let sched = default_schedule();
        assert_eq!(sched.bps_denom, 10_000u64);
        assert_eq!(compute_capped_maker_rebate(100u64, 30u64), 6u64);
        assert_eq!(compute_capped_maker_rebate(100u64, 100u64), 10u64);
    }

    #[test]
    fn settlement_tier_classification() {
        assert_eq!(classify_settlement_tier(add_u64_with_carry(0u64, 0u64)), 0u64);
        assert_eq!(classify_settlement_tier(add_u64_with_carry(50_000u64, 100u64)), 1u64);
        assert_eq!(classify_settlement_tier(add_u64_with_carry(INSTITUTIONAL_BAND_MIN, 0u64)), 2u64);
    }
}
