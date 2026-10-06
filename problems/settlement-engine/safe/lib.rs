//! Multi-module concentrated-liquidity and flash-settlement engine.
//!
//! All production paths operate strictly in 64-bit word arithmetic (`u64`)
//! without `u128` promotion so that settlement authorization executes natively
//! on 64-bit VM word registers.

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Authorization {
    pub total_debit: u64,
}

pub mod constants {
    /// Standard basis-point denominator (100% = 10_000 bps).
    pub const BPS_DENOM: u64 = 10_000;
    /// Maximum non-zero remainder modulo `BPS_DENOM` (`BPS_DENOM - 1`).
    pub const BPS_MAX_REM: u64 = 9_999;
    /// Floor quotient of `2^64` by `BPS_DENOM`: `floor(2^64 / 10_000)`.
    pub const U64_MOD_BPS_QUOT: u64 = 1_844_674_407_370_955;
    /// Exact remainder of `2^64` modulo `BPS_DENOM`: `2^64 % 10_000 = 1_616`.
    pub const U64_MOD_BPS_REM: u64 = 1_616;
    /// Tier rebate divisor (10% rebate on gross settlement fee, rounded down).
    pub const REBATE_DIVISOR: u64 = 10;
    /// Maker rebate cap divisor (20% cap on maker rebates in order-book mode).
    pub const MAKER_REBATE_CAP_DIVISOR: u64 = 5;
    /// Protocol reserve cut divisor (25% of net pool fee retained by treasury).
    pub const TREASURY_CUT_DIVISOR: u64 = 4;
    /// Flash-loan surcharge denominator (5_000 = 2 bps per unit).
    pub const FLASH_DENOM: u64 = 5_000;
    /// Ceiling bias for `FLASH_DENOM` (`FLASH_DENOM - 1`).
    pub const FLASH_MAX_REM: u64 = 4_999;
    /// Floor quotient `floor(2^64 / 5_000)`.
    pub const U64_MOD_FLASH_QUOT: u64 = 3_689_348_814_741_910;
    /// Exact remainder `2^64 % 5_000 = 1_616`.
    pub const U64_MOD_FLASH_REM: u64 = 1_616;
    /// Institutional notional band threshold for diagnostic classification.
    pub const INSTITUTIONAL_BAND_MIN: u64 = 10_000_000_000_000;
}

pub mod word_math {
    use crate::constants::*;

    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub struct WordSum {
        pub low_word: u64,
        pub high_carry: bool,
    }

    /// Adds two `u64` words and captures the 64-bit wrap carry flag.
    #[inline]
    pub fn add_u64_with_carry(lhs: u64, rhs: u64) -> WordSum {
        let low_word = lhs.wrapping_add(rhs);
        let high_carry = low_word < lhs;
        WordSum { low_word, high_carry }
    }

    /// Checks whether a combined notional exceeds the institutional liquidity band.
    #[inline]
    pub fn is_institutional_notional(sum: WordSum) -> bool {
        if sum.high_carry {
            true
        } else {
            sum.low_word >= INSTITUTIONAL_BAND_MIN
        }
    }

    /// Exact floor division `floor((lhs + rhs) / 10_000)` in pure `u64` arithmetic.
    #[inline]
    pub fn floor_div_bps_u64(sum: WordSum) -> u64 {
        if sum.high_carry {
            let folded_rem = (sum.low_word % BPS_DENOM) + U64_MOD_BPS_REM;
            U64_MOD_BPS_QUOT + (sum.low_word / BPS_DENOM) + (folded_rem / BPS_DENOM)
        } else {
            sum.low_word / BPS_DENOM
        }
    }

    /// Ceiling division `ceil((lhs + rhs) / 10_000)` in pure `u64` arithmetic.
    #[inline]
    pub fn ceil_div_bps_u64(sum: WordSum) -> u64 {
        if sum.high_carry {
            let folded_rem = (sum.low_word % BPS_DENOM) + U64_MOD_BPS_REM;
            U64_MOD_BPS_QUOT + (sum.low_word / BPS_DENOM) + ((folded_rem + BPS_MAX_REM) / BPS_DENOM)
        } else {
            let biased = sum.low_word.wrapping_add(BPS_MAX_REM);
            if biased < sum.low_word {
                (sum.low_word / BPS_DENOM) + (((sum.low_word % BPS_DENOM) + BPS_MAX_REM) / BPS_DENOM)
            } else {
                biased / BPS_DENOM
            }
        }
    }
}

pub mod fee_tiers {
    use crate::constants::*;
    use crate::word_math::{WordSum, ceil_div_bps_u64, floor_div_bps_u64};

    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub struct FeeSchedule {
        pub bps_denom: u64,
        pub rebate_divisor: u64,
        pub maker_cap_divisor: u64,
    }

    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub struct FeeQuote {
        pub gross_fee: u64,
        pub rebate: u64,
        pub net_fee: u64,
    }

    /// Returns the default protocol fee schedule parameters.
    #[inline]
    pub fn default_schedule() -> FeeSchedule {
        FeeSchedule {
            bps_denom: BPS_DENOM,
            rebate_divisor: REBATE_DIVISOR,
            maker_cap_divisor: MAKER_REBATE_CAP_DIVISOR,
        }
    }

    /// Computes the floor 10% tier rebate `floor(gross_fee / 10)`.
    #[inline]
    pub fn compute_tier_rebate(gross_fee: u64) -> u64 {
        gross_fee / REBATE_DIVISOR
    }

    /// Computes a capped maker rebate `min(floor(gross_fee / 10), floor(limit / 5))`
    /// used by passive order-book quotes.
    #[inline]
    pub fn compute_capped_maker_rebate(gross_fee: u64, cap_basis: u64) -> u64 {
        let base_rebate = gross_fee / REBATE_DIVISOR;
        let max_rebate = cap_basis / MAKER_REBATE_CAP_DIVISOR;
        if base_rebate <= max_rebate {
            base_rebate
        } else {
            max_rebate
        }
    }

    /// Evaluates the two-stage settlement fee quote (`gross_fee`, `rebate`, `net_fee`)
    /// from a folded 64-bit notional sum.
    #[inline]
    pub fn evaluate_settlement_fee(sum: WordSum) -> FeeQuote {
        let gross_fee = ceil_div_bps_u64(sum);
        let rebate = compute_tier_rebate(gross_fee);
        let net_fee = gross_fee - rebate;
        FeeQuote {
            gross_fee,
            rebate,
            net_fee,
        }
    }

    /// Evaluates a passive liquidity floor fee quote (used by pool analytics).
    #[inline]
    pub fn evaluate_passive_floor_fee(sum: WordSum) -> FeeQuote {
        let gross_fee = floor_div_bps_u64(sum);
        let rebate = compute_tier_rebate(gross_fee);
        let net_fee = gross_fee - rebate;
        FeeQuote {
            gross_fee,
            rebate,
            net_fee,
        }
    }
}

pub mod liquidity_pool {
    use crate::constants::*;
    use crate::fee_tiers::FeeQuote;

    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub struct PoolReserveQuote {
        pub treasury_cut: u64,
        pub lp_retention: u64,
    }

    /// Splits a net fee between the protocol treasury (`floor(net_fee / 4)`)
    /// and liquidity providers (`net_fee - treasury_cut`).
    #[inline]
    pub fn split_pool_reserve(quote: FeeQuote) -> PoolReserveQuote {
        let treasury_cut = quote.net_fee / TREASURY_CUT_DIVISOR;
        let lp_retention = quote.net_fee - treasury_cut;
        PoolReserveQuote {
            treasury_cut,
            lp_retention,
        }
    }

    /// Computes the LP retention share after protocol cut for reserve accounting.
    #[inline]
    pub fn quote_lp_retention(quote: FeeQuote) -> u64 {
        let split = split_pool_reserve(quote);
        split.lp_retention
    }
}

pub mod flash_loan {
    use crate::constants::*;
    use crate::word_math::add_u64_with_carry;

    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub struct FlashLoanReceipt {
        pub principal: u64,
        pub flash_levy: u64,
        pub total_repayment: u64,
    }

    /// Computes the ceiling flash-loan levy `ceil((principal + surcharge) / 5_000)`
    /// in pure `u64` arithmetic.
    #[inline]
    pub fn assess_flash_fee_ceil(principal: u64, surcharge: u64) -> u64 {
        let sum = add_u64_with_carry(principal, surcharge);
        if sum.high_carry {
            let folded_rem = (sum.low_word % FLASH_DENOM) + U64_MOD_FLASH_REM;
            U64_MOD_FLASH_QUOT + (sum.low_word / FLASH_DENOM) + ((folded_rem + FLASH_MAX_REM) / FLASH_DENOM)
        } else {
            let biased = sum.low_word.wrapping_add(FLASH_MAX_REM);
            if biased < sum.low_word {
                (sum.low_word / FLASH_DENOM) + (((sum.low_word % FLASH_DENOM) + FLASH_MAX_REM) / FLASH_DENOM)
            } else {
                biased / FLASH_DENOM
            }
        }
    }

    /// Builds a flash-loan repayment receipt if `principal + flash_levy` fits in `u64`.
    #[inline]
    pub fn quote_flash_repayment(principal: u64, surcharge: u64) -> Option<FlashLoanReceipt> {
        let flash_levy = assess_flash_fee_ceil(principal, surcharge);
        let total_repayment = principal.checked_add(flash_levy)?;
        Some(FlashLoanReceipt {
            principal,
            flash_levy,
            total_repayment,
        })
    }
}

pub mod settlement_engine {
    use crate::Authorization;
    use crate::fee_tiers::{FeeQuote, evaluate_settlement_fee};
    use crate::word_math::add_u64_with_carry;

    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub struct SettlementTicket {
        pub principal: u64,
        pub gross_fee: u64,
        pub rebate: u64,
        pub net_fee: u64,
        pub total_debit: u64,
    }

    /// Assembles a complete settlement ticket from `amount` and `fee_quote`,
    /// returning `None` if `amount + fee_quote.net_fee` overflows `u64`.
    #[inline]
    pub fn assemble_ticket(amount: u64, fee_quote: FeeQuote) -> Option<SettlementTicket> {
        let total_debit = amount.checked_add(fee_quote.net_fee)?;
        Some(SettlementTicket {
            principal: amount,
            gross_fee: fee_quote.gross_fee,
            rebate: fee_quote.rebate,
            net_fee: fee_quote.net_fee,
            total_debit,
        })
    }

    /// Quotes the settlement ticket for `(amount, fee)` using the two-stage
    /// basis-point ceiling levy and floor tier rebate schedule.
    #[inline]
    pub fn quote_settlement_ticket(amount: u64, fee: u64) -> Option<SettlementTicket> {
        let notional_sum = add_u64_with_carry(amount, fee);
        let fee_quote = evaluate_settlement_fee(notional_sum);
        assemble_ticket(amount, fee_quote)
    }

    /// Commits a settlement ticket against `balance`, authorizing iff
    /// `ticket.total_debit <= balance`.
    #[inline]
    pub fn commit_ticket(balance: u64, ticket: SettlementTicket) -> Option<Authorization> {
        if ticket.total_debit <= balance {
            Some(Authorization {
                total_debit: ticket.total_debit,
            })
        } else {
            None
        }
    }

    /// Previews the net outflow difference between balance and ticket debit
    /// when affordable, saturating at zero for telemetry.
    #[inline]
    pub fn preview_remaining_balance(balance: u64, ticket: SettlementTicket) -> u64 {
        balance.saturating_sub(ticket.total_debit)
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
    let ticket = settlement_engine::quote_settlement_ticket(amount, fee)?;
    settlement_engine::commit_ticket(balance, ticket)
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
    fn flash_loan_ceil_levy_across_all_boundaries() {
        let fee_at_pocket = flash_loan::assess_flash_fee_ceil(0, u64::MAX - 2_500);
        assert_eq!(fee_at_pocket, 3_689_348_814_741_910);
        let receipt = flash_loan::quote_flash_repayment(100_000, 1).unwrap();
        assert_eq!(receipt.flash_levy, 21);
        assert_eq!(receipt.total_repayment, 100_021);
    }

    #[test]
    fn pool_reserve_split_and_maker_rebate_cap() {
        let sum = word_math::add_u64_with_carry(500_000, 50_000);
        let quote = fee_tiers::evaluate_passive_floor_fee(sum);
        assert_eq!(quote.gross_fee, 55);
        assert_eq!(quote.rebate, 5);
        assert_eq!(quote.net_fee, 50);
        let split = liquidity_pool::split_pool_reserve(quote);
        assert_eq!(split.treasury_cut, 12);
        assert_eq!(split.lp_retention, 38);
        assert_eq!(fee_tiers::compute_capped_maker_rebate(55, 15), 3);
    }
}
