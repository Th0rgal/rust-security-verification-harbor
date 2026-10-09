//! Multi-stage rollup batch clearing pipeline and settlement ticket gate.
//!
//! Coordinates the protocol surcharge subsystems across `word_math`, `fee_schedule`,
//! `liquidity_pool`, `reciprocal_div`, `broadword_swar`, `montgomery_field`,
//! `goldilocks_field`, and `transcript_codec` to price and authorize a batch
//! clearing request `(balance, amount, fee)`.
//!
//! The combined protocol surcharge is added to the transfer principal `amount`
//! via checked `u64` addition, and the resulting `ClearingTicket` is committed
//! if and only if `total_debit <= balance`.

use crate::Authorization;
use crate::broadword_swar::{CalldataLaneQuote, quote_calldata_lane_surcharge};
use crate::fee_schedule::{FeeQuote, evaluate_settlement_fee};
use crate::goldilocks_field::{GoldilocksQuote, quote_bridge_verifier_fee};
use crate::liquidity_pool::{PoolReserveQuote, quote_flash_lp_retention};
use crate::montgomery_field::{ProverLevyQuote, quote_prover_transcript_levy};
use crate::reciprocal_div::{BlobSlotQuote, quote_blob_gas_slots};
use crate::transcript_codec::decode_domain_tag;
use crate::word_math::{WordSum, add_u64_with_carry};

/// Itemized multi-stage surcharge breakdown for a rollup clearing operation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ClearingBreakdown {
    pub net_bps_fee: u64,
    pub flash_lp_fee: u64,
    pub blob_slot_quotient: u64,
    pub calldata_surcharge: u64,
    pub prover_levy: u64,
    pub domain_surcharge: u64,
    pub base_surcharge: u64,
    pub bridge_surcharge: u64,
}

/// Validated clearing settlement ticket ready for balance conservation check.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ClearingTicket {
    pub principal: u64,
    pub net_bps_fee: u64,
    pub flash_lp_fee: u64,
    pub blob_slot_quotient: u64,
    pub calldata_surcharge: u64,
    pub prover_levy: u64,
    pub domain_surcharge: u64,
    pub bridge_surcharge: u64,
    pub total_surcharge: u64,
    pub total_debit: u64,
}

/// Evaluates all protocol surcharge stages for `(amount, fee)` and packages them into
/// a `ClearingBreakdown`.
#[inline]
pub fn compute_clearing_breakdown(amount: u64, fee: u64) -> ClearingBreakdown {
    let notional_sum: WordSum = add_u64_with_carry(amount, fee);
    let fee_quote: FeeQuote = evaluate_settlement_fee(notional_sum);
    let flash_quote: PoolReserveQuote = quote_flash_lp_retention(amount, fee);
    let blob_quote: BlobSlotQuote = quote_blob_gas_slots(amount, fee);
    let lane_quote: CalldataLaneQuote = quote_calldata_lane_surcharge(fee);
    let levy_quote: ProverLevyQuote = quote_prover_transcript_levy(amount, fee);
    let bridge_quote: GoldilocksQuote = quote_bridge_verifier_fee(amount, fee);
    let domain_surcharge: u64 = decode_domain_tag(fee);

    let net_bps_fee: u64 = fee_quote.net_fee;
    let flash_lp_fee: u64 = flash_quote.lp_retention;
    let blob_slot_quotient: u64 = blob_quote.slot_quotient;
    let calldata_surcharge: u64 = lane_quote.surcharge;
    let prover_levy: u64 = levy_quote.prover_levy;
    let bridge_surcharge: u64 = bridge_quote.bridge_fee;

    let base_surcharge: u64 = net_bps_fee
        + flash_lp_fee
        + blob_slot_quotient
        + calldata_surcharge
        + prover_levy
        + domain_surcharge;

    ClearingBreakdown {
        net_bps_fee,
        flash_lp_fee,
        blob_slot_quotient,
        calldata_surcharge,
        prover_levy,
        domain_surcharge,
        base_surcharge,
        bridge_surcharge,
    }
}

/// Assembles a `ClearingTicket` from `amount` and `breakdown`, returning `None`
/// if `amount + breakdown.base_surcharge + breakdown.bridge_surcharge` exceeds `u64::MAX`.
#[inline]
pub fn assemble_clearing_ticket(
    amount: u64,
    breakdown: ClearingBreakdown,
) -> Option<ClearingTicket> {
    let total_surcharge: u64 = breakdown
        .base_surcharge
        .checked_add(breakdown.bridge_surcharge)?;
    let total_debit: u64 = amount.checked_add(total_surcharge)?;
    Some(ClearingTicket {
        principal: amount,
        net_bps_fee: breakdown.net_bps_fee,
        flash_lp_fee: breakdown.flash_lp_fee,
        blob_slot_quotient: breakdown.blob_slot_quotient,
        calldata_surcharge: breakdown.calldata_surcharge,
        prover_levy: breakdown.prover_levy,
        domain_surcharge: breakdown.domain_surcharge,
        bridge_surcharge: breakdown.bridge_surcharge,
        total_surcharge,
        total_debit,
    })
}

/// Quotes a complete `ClearingTicket` for `(amount, fee)`.
#[inline]
pub fn quote_clearing_ticket(amount: u64, fee: u64) -> Option<ClearingTicket> {
    let breakdown: ClearingBreakdown = compute_clearing_breakdown(amount, fee);
    assemble_clearing_ticket(amount, breakdown)
}

/// Commits a `ClearingTicket` against `balance`, authorizing iff `ticket.total_debit <= balance`.
#[inline]
pub fn commit_clearing_ticket(balance: u64, ticket: ClearingTicket) -> Option<Authorization> {
    if ticket.total_debit <= balance {
        Some(Authorization {
            total_debit: ticket.total_debit,
        })
    } else {
        None
    }
}

/// Computes the post-settlement remaining account balance for telemetry, saturating at zero.
#[inline]
pub fn preview_remaining_balance(balance: u64, ticket: ClearingTicket) -> u64 {
    balance.saturating_sub(ticket.total_debit)
}

/// Verifies internal surcharge conservation on an assembled `ClearingTicket`.
#[inline]
pub fn verify_ticket_conservation(ticket: ClearingTicket) -> bool {
    let recomputed_base: u64 = ticket.net_bps_fee
        + ticket.flash_lp_fee
        + ticket.blob_slot_quotient
        + ticket.calldata_surcharge
        + ticket.prover_levy
        + ticket.domain_surcharge;
    (recomputed_base.wrapping_add(ticket.bridge_surcharge) == ticket.total_surcharge)
        && (ticket.principal.wrapping_add(ticket.total_surcharge) == ticket.total_debit)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn zero_transfer_breakdown_carries_default_domain_tag() {
        let b = compute_clearing_breakdown(0u64, 0u64);
        assert_eq!(b.net_bps_fee, 0u64);
        assert_eq!(b.flash_lp_fee, 0u64);
        assert_eq!(b.blob_slot_quotient, 0u64);
        assert_eq!(b.calldata_surcharge, 0u64);
        assert_eq!(b.prover_levy, 0u64);
        assert_eq!(b.domain_surcharge, 90u64);
        assert_eq!(b.base_surcharge, 90u64);
        assert_eq!(b.bridge_surcharge, 0u64);
    }

    #[test]
    fn ticket_overflow_rejected_near_u64_max() {
        assert_eq!(quote_clearing_ticket(u64::MAX, 1u64), None);
        assert_eq!(quote_clearing_ticket(u64::MAX, u64::MAX), None);
    }

    #[test]
    fn remaining_balance_preview_and_ticket_conservation() {
        let t = quote_clearing_ticket(0u64, 1u64).unwrap();
        assert_eq!(t.total_debit, 4_294_967_557u64);
        assert!(verify_ticket_conservation(t));
        assert_eq!(preview_remaining_balance(4_294_967_600u64, t), 43u64);
        assert_eq!(preview_remaining_balance(200u64, t), 0u64);
    }
}
