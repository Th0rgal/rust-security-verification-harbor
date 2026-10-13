//! Multiprecision 2-by-1 normalized reciprocal division (`alloy-rs/ruint` algorithm)
//! for L1 data-availability blob gas slot partitioning.
//!
//! Given a normalized 16-bit divisor `D = MG10_DIVISOR = 0x8003 = 32_771` (`2^15 + 3`)
//! with precomputed reciprocal `V = floor((2^32 - 1) / D) - 2^16 = 0xFFF4 = 65_524`,
//! `div_2x1_mg10(u1, u0)` computes the exact floor quotient
//! `floor((u1 * 2^16 + u0) / D)` for all `u1 < D` and `u0 < 2^16` using only
//! shifts, bitwise masks, and `u64` multiplications (without hardware `/` or `%`
//! in the core reciprocal step).

use crate::constants::*;
use crate::word_math::extract_low_u16;

/// Captures the two-limb blob gas dividend `(high_limb, low_limb)` and its
/// exact Euclidean division decomposition `high_limb * 2^16 + low_limb = D * slot_quotient + slot_remainder`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BlobSlotQuote {
    pub high_limb: u64,
    pub low_limb: u64,
    pub slot_quotient: u64,
    pub slot_remainder: u64,
}

/// Möller-Granlund 2-by-1 normalized reciprocal division (`div_2x1_mg10`)
/// for divisor `MG10_DIVISOR = 0x8003 = 32_771` and reciprocal `MG10_RECIPROCAL = 0xFFF4 = 65_524`.
///
/// Preconditions guaranteed by caller: `u1 < MG10_DIVISOR` and `u0 < 2^16`.
/// Returns the exact integer quotient `floor((u1 * 65_536 + u0) / 32_771)`.
#[inline]
pub fn div_2x1_mg10(u1: u64, u0: u64) -> u64 {
    let q_full: u64 = (u1 * MG10_RECIPROCAL) + (u1 << 16u64) + u0 + (1u64 << 16u64);

    let q1: u64 = q_full >> 16u64;
    let q0: u64 = q_full & LIMB_MASK;
    let r: u64 = (SUB_BIAS + u0 - q1 * MG10_DIVISOR) & LIMB_MASK;

    let (q_corr, r_corr): (u64, u64) = if q0 < r {
        (q1 - 1u64, (r + MG10_DIVISOR) & LIMB_MASK)
    } else {
        (q1, r)
    };

    if r_corr >= MG10_DIVISOR {
        q_corr + 1u64
    } else {
        q_corr
    }
}

/// Reconstructs the exact remainder `(u1 * 2^16 + u0) - quot * MG10_DIVISOR`
/// from a computed quotient `quot = floor((u1 * 2^16 + u0) / MG10_DIVISOR)`.
#[inline]
pub fn rem_2x1_mg10(u1: u64, u0: u64, quot: u64) -> u64 {
    let dividend: u64 = (u1 << 16u64) + u0;
    dividend - (quot * MG10_DIVISOR)
}

/// Computes the L1 blob gas slot quotient and remainder for a settlement pair `(amount, fee)`:
/// - `high_limb = fee % MG10_DIVISOR` (`u1 in [0, 32_770]`)
/// - `low_limb = amount & 0xFFFF` (`u0 in [0, 65_535]`)
/// - `slot_quotient = floor((high_limb * 65_536 + low_limb) / 32_771)`
/// - `slot_remainder = (high_limb * 65_536 + low_limb) % 32_771`
#[inline]
pub fn quote_blob_gas_slots(amount: u64, fee: u64) -> BlobSlotQuote {
    let high_limb: u64 = fee % MG10_DIVISOR;
    let low_limb: u64 = extract_low_u16(amount);
    let slot_quotient: u64 = div_2x1_mg10(high_limb, low_limb);
    let slot_remainder: u64 = rem_2x1_mg10(high_limb, low_limb, slot_quotient);
    BlobSlotQuote {
        high_limb,
        low_limb,
        slot_quotient,
        slot_remainder,
    }
}

/// Verifies the Euclidean division invariant `0 <= slot_remainder < MG10_DIVISOR`
/// and `slot_quotient * MG10_DIVISOR + slot_remainder == high_limb * 2^16 + low_limb`
/// for diagnostic auditing.
#[inline]
pub fn verify_blob_slot_euclidean(quote: BlobSlotQuote) -> bool {
    let dividend: u64 = (quote.high_limb << 16u64) + quote.low_limb;
    let reconstructed: u64 = (quote.slot_quotient * MG10_DIVISOR) + quote.slot_remainder;
    (quote.slot_remainder < MG10_DIVISOR) && (reconstructed == dividend)
}

/// Estimates raw L1 blob gas units `slot_quotient * BLOB_GAS_PER_SLOT` for telemetry.
#[inline]
pub fn estimate_blob_gas_units(quote: BlobSlotQuote) -> u64 {
    quote.slot_quotient * BLOB_GAS_PER_SLOT
}

/// Computes the ceiling blob slot count `slot_quotient + (if slot_remainder > 0 { 1 } else { 0 })`
/// for batch reservation telemetry.
#[inline]
pub fn ceil_blob_slots(quote: BlobSlotQuote) -> u64 {
    if quote.slot_remainder > 0u64 {
        quote.slot_quotient + 1u64
    } else {
        quote.slot_quotient
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn mg10_zero_and_exact_multiples() {
        assert_eq!(div_2x1_mg10(0u64, 0u64), 0u64);
        assert_eq!(div_2x1_mg10(0u64, 32_770u64), 0u64);
        assert_eq!(div_2x1_mg10(0u64, 32_771u64), 1u64);
        assert_eq!(div_2x1_mg10(1u64, 0u64), 1u64);
        assert_eq!(div_2x1_mg10(10u64, 32_771u64), 20u64);
    }

    #[test]
    fn mg10_exhaustive_boundary_sweeps() {
        for u1 in [0u64, 1u64, 2u64, 16_384u64, 21_845u64, 32_769u64, 32_770u64] {
            for u0 in [0u64, 1u64, 2u64, 32_770u64, 32_771u64, 32_772u64, 65_534u64, 65_535u64] {
                let expected: u64 = ((u1 << 16u64) + u0) / MG10_DIVISOR;
                let actual: u64 = div_2x1_mg10(u1, u0);
                assert_eq!(actual, expected, "mismatch at u1={}, u0={}", u1, u0);
            }
        }
    }

    #[test]
    fn mg10_second_correction_branch_is_exact() {
        let q_a = quote_blob_gas_slots(65_535u64, 16_384u64);
        assert!(verify_blob_slot_euclidean(q_a));
        assert_eq!(q_a.slot_quotient, 32_767u64);
        assert_eq!(ceil_blob_slots(q_a), 32_768u64);

        let q_b = quote_blob_gas_slots(65_534u64, 21_845u64);
        assert!(verify_blob_slot_euclidean(q_b));
        assert_eq!(q_b.slot_quotient, 43_688u64);
    }

    #[test]
    fn blob_gas_unit_telemetry() {
        let q = quote_blob_gas_slots(32_771u64, 0u64);
        assert_eq!(q.slot_quotient, 1u64);
        assert_eq!(q.slot_remainder, 0u64);
        assert_eq!(ceil_blob_slots(q), 1u64);
        assert_eq!(estimate_blob_gas_units(q), BLOB_GAS_PER_SLOT);
    }

    #[test]
    fn mg10_maximum_two_limb_dividend() {
        let q_max = quote_blob_gas_slots(65_535u64, 32_770u64);
        assert!(verify_blob_slot_euclidean(q_max));
        assert_eq!(q_max.slot_quotient, 65_535u64);
        assert_eq!(q_max.slot_remainder, 32_770u64);
    }
}
