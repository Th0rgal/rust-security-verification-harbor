//! Concentrated-liquidity reserve accounting, protocol treasury split, and
//! flash-settlement repayment calculators.

use crate::constants::*;
use crate::fee_schedule::FeeQuote;
use crate::word_math::{add_u64_with_carry, ceil_div_flash_u64, floor_div_flash_u64};

/// Breakdown of protocol net fee between treasury reserve and liquidity providers.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PoolReserveQuote {
    pub treasury_cut: u64,
    pub lp_retention: u64,
}

/// Repayment receipt for an atomic flash-liquidity draw.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FlashLoanReceipt {
    pub principal: u64,
    pub flash_levy: u64,
    pub total_repayment: u64,
}

/// Splits `quote.net_fee` between the protocol treasury (`floor(net_fee / 4)`)
/// and liquidity providers (`net_fee - treasury_cut`).
#[inline]
pub fn split_pool_reserve(quote: FeeQuote) -> PoolReserveQuote {
    let treasury_cut: u64 = quote.net_fee / TREASURY_CUT_DIVISOR;
    let lp_retention: u64 = quote.net_fee - treasury_cut;
    PoolReserveQuote {
        treasury_cut,
        lp_retention,
    }
}

/// Returns the liquidity-provider retention share from a `FeeQuote`.
#[inline]
pub fn quote_lp_retention(quote: FeeQuote) -> u64 {
    let split: PoolReserveQuote = split_pool_reserve(quote);
    split.lp_retention
}

/// Computes the ceiling flash-settlement levy `ceil((principal + surcharge) / 5_000)`
/// in pure `u64` arithmetic.
#[inline]
pub fn assess_flash_fee_ceil(principal: u64, surcharge: u64) -> u64 {
    let sum = add_u64_with_carry(principal, surcharge);
    ceil_div_flash_u64(sum)
}

/// Computes the floor flash-settlement levy `floor((principal + surcharge) / 5_000)`
/// in pure `u64` arithmetic.
#[inline]
pub fn assess_flash_fee_floor(principal: u64, surcharge: u64) -> u64 {
    let sum = add_u64_with_carry(principal, surcharge);
    floor_div_flash_u64(sum)
}

/// Quotes a complete flash-loan repayment receipt if `principal + flash_levy` fits in `u64`.
#[inline]
pub fn quote_flash_repayment(principal: u64, surcharge: u64) -> Option<FlashLoanReceipt> {
    let flash_levy: u64 = assess_flash_fee_ceil(principal, surcharge);
    let total_repayment: u64 = principal.checked_add(flash_levy)?;
    Some(FlashLoanReceipt {
        principal,
        flash_levy,
        total_repayment,
    })
}

/// Verifies whether a pool reserve after crediting `lp_retention` satisfies a target
/// solvency floor `min_reserve`.
#[inline]
pub fn check_pool_reserve_solvency(current_reserve: u64, quote: FeeQuote, min_reserve: u64) -> bool {
    let lp_share: u64 = quote_lp_retention(quote);
    match current_reserve.checked_add(lp_share) {
        Some(updated) => updated >= min_reserve,
        None => true,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fee_schedule::evaluate_settlement_fee;

    #[test]
    fn reserve_split_conserves_net_fee() {
        let sum = add_u64_with_carry(500_000u64, 50_000u64);
        let q = evaluate_settlement_fee(sum);
        let split = split_pool_reserve(q);
        assert_eq!(split.treasury_cut + split.lp_retention, q.net_fee);
        assert_eq!(quote_lp_retention(q), split.lp_retention);
        assert!(check_pool_reserve_solvency(1_000u64, q, 1_030u64));
    }

    #[test]
    fn flash_repayment_receipt_and_overflow_guard() {
        let r = quote_flash_repayment(100_000u64, 1u64).unwrap();
        assert_eq!(r.flash_levy, 21u64);
        assert_eq!(r.total_repayment, 100_021u64);
        assert_eq!(assess_flash_fee_floor(100_000u64, 1u64), 20u64);
        assert_eq!(quote_flash_repayment(u64::MAX, 1u64), None);
    }
}
