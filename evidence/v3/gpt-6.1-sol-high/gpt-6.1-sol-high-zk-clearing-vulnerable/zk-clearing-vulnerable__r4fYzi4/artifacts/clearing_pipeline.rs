//! Multi-stage rollup batch clearing pipeline and settlement ticket gate.
//!
//! Coordinates the four protocol surcharge subsystems to price and authorize
//! a batch clearing transaction `(balance, amount, fee)`:
//! 1. `net_bps_fee`: Protocol basis-point settlement fee with 10% floor tier rebate
//!    (`fee_schedule::evaluate_settlement_fee(word_math::add_u64_with_carry(amount, fee)).net_fee`).
//! 2. `blob_slot_quotient`: L1 data-availability blob slot quotient via Möller-Granlund
//!    2-by-1 normalized reciprocal division (`reciprocal_div::quote_blob_gas_slots(amount, fee).slot_quotient`).
//! 3. `calldata_surcharge`: L1 calldata byte-lane compression surcharge via Vigna SWAR
//!    broadword operations (`broadword_swar::quote_calldata_lane_surcharge(fee).surcharge`).
//! 4. `prover_levy`: STARK BabyBear Montgomery transcript verification levy
//!    (`montgomery_field::quote_prover_transcript_levy(amount, fee).prover_levy`).
//!
//! The combined surcharge `total_surcharge = net_bps_fee + blob_slot_quotient + calldata_surcharge + prover_levy`
//! is added to the transfer principal `amount` via checked `u64` addition, and the
//! resulting `ClearingTicket` is committed iff `total_debit <= balance`.

use crate::Authorization;
use crate::broadword_swar::{CalldataLaneQuote, quote_calldata_lane_surcharge};
use crate::fee_schedule::{FeeQuote, evaluate_settlement_fee};
use crate::montgomery_field::{ProverLevyQuote, quote_prover_transcript_levy};
use crate::reciprocal_div::{BlobSlotQuote, quote_blob_gas_slots};
use crate::word_math::{WordSum, add_u64_with_carry};

/// Itemized four-stage surcharge breakdown for a rollup clearing operation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ClearingBreakdown {
    pub net_bps_fee: u64,
    pub blob_slot_quotient: u64,
    pub calldata_surcharge: u64,
    pub prover_levy: u64,
    pub total_surcharge: u64,
}

/// Validated clearing settlement ticket ready for balance conservation check.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ClearingTicket {
    pub principal: u64,
    pub net_bps_fee: u64,
    pub blob_slot_quotient: u64,
    pub calldata_surcharge: u64,
    pub prover_levy: u64,
    pub total_surcharge: u64,
    pub total_debit: u64,
}

// One byte costs its value plus a 256-unit activation charge, unless zero.
fn lane_charge(x: u64) -> u64 {
    let byte = x % 256;
    if byte == 0 { 0 } else { 256 + byte }
}

/// Evaluates all four surcharge stages for `(amount, fee)` and sums them into
/// a `ClearingBreakdown`.
#[inline]
pub fn compute_clearing_breakdown(amount: u64, fee: u64) -> ClearingBreakdown {
    // Quotient/remainder decomposition avoids overflowing amount + fee or its bias.
    let gross = amount / 10000 + fee / 10000
        + (amount % 10000 + fee % 10000 + 9999) / 10000;
    let net_bps_fee = gross - gross / 10;
    let blob_slot_quotient = ((fee % 32771) * 65536 + amount % 65536) / 32771;
    let calldata_surcharge = lane_charge(fee) + lane_charge(fee / 256)
        + lane_charge(fee / 65536) + lane_charge(fee / 16777216)
        + lane_charge(fee / 4294967296) + lane_charge(fee / 1099511627776)
        + lane_charge(fee / 281474976710656) + lane_charge(fee / 72057594037927936);
    // 943718400 is the inverse of 2^32 modulo BabyBear's prime.
    let prover_levy = (((amount % 4294967296) % 2013265921) * 943718400
        + fee % 2013265921) % 2013265921;

    let total_surcharge: u64 =
        net_bps_fee + blob_slot_quotient + calldata_surcharge + prover_levy;

    ClearingBreakdown {
        net_bps_fee,
        blob_slot_quotient,
        calldata_surcharge,
        prover_levy,
        total_surcharge,
    }
}

/// Assembles a `ClearingTicket` from `amount` and `breakdown`, returning `None`
/// if `amount + breakdown.total_surcharge` exceeds `u64::MAX`.
#[inline]
pub fn assemble_clearing_ticket(
    amount: u64,
    breakdown: ClearingBreakdown,
) -> Option<ClearingTicket> {
    let total_debit: u64 = amount.checked_add(breakdown.total_surcharge)?;
    Some(ClearingTicket {
        principal: amount,
        net_bps_fee: breakdown.net_bps_fee,
        blob_slot_quotient: breakdown.blob_slot_quotient,
        calldata_surcharge: breakdown.calldata_surcharge,
        prover_levy: breakdown.prover_levy,
        total_surcharge: breakdown.total_surcharge,
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

/// Verifies internal surcharge conservation (`net_bps_fee + blob_slot_quotient + calldata_surcharge + prover_levy == total_surcharge`)
/// on an assembled `ClearingTicket`.
#[inline]
pub fn verify_ticket_conservation(ticket: ClearingTicket) -> bool {
    let recomputed_surcharge: u64 = ticket.net_bps_fee
        + ticket.blob_slot_quotient
        + ticket.calldata_surcharge
        + ticket.prover_levy;
    (recomputed_surcharge == ticket.total_surcharge)
        && (ticket.principal.wrapping_add(ticket.total_surcharge) == ticket.total_debit)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn zero_transfer_breakdown_is_zero() {
        let b = compute_clearing_breakdown(0u64, 0u64);
        assert_eq!(b.net_bps_fee, 0u64);
        assert_eq!(b.blob_slot_quotient, 0u64);
        assert_eq!(b.calldata_surcharge, 0u64);
        assert_eq!(b.prover_levy, 0u64);
        assert_eq!(b.total_surcharge, 0u64);
    }

    #[test]
    fn ticket_overflow_rejected_near_u64_max() {
        assert_eq!(quote_clearing_ticket(u64::MAX, 1u64), None);
        assert_eq!(quote_clearing_ticket(u64::MAX, u64::MAX), None);
    }

    #[test]
    fn remaining_balance_preview_and_ticket_conservation() {
        let t = quote_clearing_ticket(0u64, 1u64).unwrap();
        assert_eq!(t.total_debit, 260u64);
        assert!(verify_ticket_conservation(t));
        assert_eq!(preview_remaining_balance(300u64, t), 40u64);
        assert_eq!(preview_remaining_balance(200u64, t), 0u64);
    }
}
