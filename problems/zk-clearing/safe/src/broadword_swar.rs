//! Vigna (`tov/succinct-rs`) 8-lane SWAR (SIMD Within A Register) broadword byte
//! inspection and accumulation kernels for L1 calldata compression pricing.
//!
//! Zero-knowledge rollup batches compress zero bytes in transaction fee parameters
//! much more cheaply than non-zero bytes. For a 64-bit word `fee` viewed as 8 bytes
//! `b_0, b_1, ..., b_7` (`b_i = (fee >> (8 * i)) & 0xFF`):
//! - Each non-zero byte (`b_i > 0`) incurs a fixed `256`-unit activation surcharge.
//! - Each byte additionally contributes its numeric value `b_i` (`0..=255`).
//! Thus the total calldata byte-lane surcharge is:
//! `256 * |{i in 0..8 : b_i > 0}| + sum_{i=0..7} b_i`.

use crate::constants::*;

/// Breakdown of the 8-byte SWAR calldata inspection on a 64-bit parameter word.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CalldataLaneQuote {
    pub active_lanes: u64,
    pub byte_weight_sum: u64,
    pub surcharge: u64,
}

/// Vigna's broadword non-zero byte detector (`u_nz8`):
/// Sets bit 7 (`0x80`) of byte lane `i` if and only if byte `i` of `x` is non-zero (`b_i > 0`),
/// and clears all other bits in every lane.
///
/// Identity: `((((x | H8_MASK) - L8_MASK) | x) & H8_MASK)`:
/// - Setting `| H8_MASK` ensures bit 7 of each byte is `1`, blocking borrow propagation
///   between adjacent bytes when subtracting `L8_MASK` (`0x01` in each byte).
/// - If low 7 bits of byte `i` are non-zero, subtracting `1` leaves bit 7 equal to `1`.
/// - If byte `i` is `0x80` (`128`), subtracting `1` clears bit 7 to `0`, and `| x`
///   restores bit 7 to `1`.
/// - If byte `i` is `0x00`, subtracting `1` clears bit 7 to `0`, and `| x` leaves it `0`.
#[inline]
pub fn u_nz8(x: u64) -> u64 {
    (((x | H8_MASK) - L8_MASK) | x) & H8_MASK
}

/// Counts the number of non-zero bytes (`0..=8`) in a 64-bit word `x` in `O(1)`
/// register operations by shifting the `0x80` lane flags of `u_nz8(x)` down to `0x01`
/// and multiplying by `L8_MASK` to sum all 8 lanes in the top byte (`>> 56`).
#[inline]
pub fn count_nz_bytes(x: u64) -> u64 {
    ((u_nz8(x) >> 7u64) * L8_MASK) >> 56u64
}

/// Counts the number of zero bytes (`0..=8`) in a 64-bit word `x`.
#[inline]
pub fn count_zero_bytes_swar(x: u64) -> u64 {
    8u64 - count_nz_bytes(x)
}

/// Checks whether any byte lane of `x` has its most significant bit (`0x80`) set.
#[inline]
pub fn has_high_bit_byte(x: u64) -> bool {
    (x & H8_MASK) != 0u64
}

/// Computes the exact sum of all 8 bytes `b_0 + b_1 + ... + b_7` (`0..=2040`) of `x`
/// using two-lane 16-bit SWAR accumulation (`M16_MASK`) followed by `L16_MASK`
/// multiplication into the top 16-bit lane (`>> 48`).
#[inline]
pub fn sum_bytes(x: u64) -> u64 {
    let pair_sum: u64 = (x & M16_MASK) + ((x >> 8u64) & M16_MASK);
    ((pair_sum * L16_MASK) >> 48u64) & LIMB_MASK
}

/// Computes the sum of even-indexed bytes `b_0 + b_2 + b_4 + b_6` of `x`.
#[inline]
pub fn sum_even_bytes_swar(x: u64) -> u64 {
    let even_lanes: u64 = x & M16_MASK;
    ((even_lanes * L16_MASK) >> 48u64) & LIMB_MASK
}

/// Computes the sum of odd-indexed bytes `b_1 + b_3 + b_5 + b_7` of `x`.
#[inline]
pub fn sum_odd_bytes_swar(x: u64) -> u64 {
    let odd_lanes: u64 = (x >> 8u64) & M16_MASK;
    ((odd_lanes * L16_MASK) >> 48u64) & LIMB_MASK
}

/// Quotes the L1 calldata byte-lane surcharge for `fee`:
/// `surcharge = (count_nz_bytes(fee) << 8) + sum_bytes(fee)`.
#[inline]
pub fn quote_calldata_lane_surcharge(fee: u64) -> CalldataLaneQuote {
    let active_lanes: u64 = count_nz_bytes(fee);
    let byte_weight_sum: u64 = sum_bytes(fee);
    let surcharge: u64 = (active_lanes << CALLDATA_NZ_BYTE_SHIFT) + byte_weight_sum;
    CalldataLaneQuote {
        active_lanes,
        byte_weight_sum,
        surcharge,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn swar_zero_and_single_byte_lanes() {
        let q0 = quote_calldata_lane_surcharge(0u64);
        assert_eq!(q0.active_lanes, 0u64);
        assert_eq!(q0.byte_weight_sum, 0u64);
        assert_eq!(q0.surcharge, 0u64);
        assert_eq!(count_zero_bytes_swar(0u64), 8u64);

        let q1 = quote_calldata_lane_surcharge(1u64);
        assert_eq!(q1.active_lanes, 1u64);
        assert_eq!(q1.byte_weight_sum, 1u64);
        assert_eq!(q1.surcharge, 257u64);
    }

    #[test]
    fn swar_high_bit_0x80_bytes_detected_as_nonzero() {
        let single_0x80: u64 = 0x80u64;
        let q_single = quote_calldata_lane_surcharge(single_0x80);
        assert_eq!(q_single.active_lanes, 1u64);
        assert_eq!(q_single.byte_weight_sum, 128u64);
        assert_eq!(q_single.surcharge, 384u64);
        assert!(has_high_bit_byte(single_0x80));

        let all_0x80: u64 = H8_MASK;
        let q_all = quote_calldata_lane_surcharge(all_0x80);
        assert_eq!(q_all.active_lanes, 8u64);
        assert_eq!(q_all.byte_weight_sum, 1024u64);
        assert_eq!(q_all.surcharge, 3072u64);
    }

    #[test]
    fn swar_all_0xff_max_word() {
        let q_max = quote_calldata_lane_surcharge(u64::MAX);
        assert_eq!(q_max.active_lanes, 8u64);
        assert_eq!(q_max.byte_weight_sum, 2040u64);
        assert_eq!(q_max.surcharge, 4088u64);
        assert_eq!(count_zero_bytes_swar(u64::MAX), 0u64);
    }

    #[test]
    fn swar_mixed_byte_pattern_and_even_odd_partition() {
        let word: u64 = 0x0010_807F_00FF_0100u64;
        let q = quote_calldata_lane_surcharge(word);
        assert_eq!(q.active_lanes, 5u64);
        assert_eq!(q.byte_weight_sum, 527u64);
        assert_eq!(q.surcharge, 5u64 * 256u64 + 527u64);
        assert_eq!(sum_even_bytes_swar(word) + sum_odd_bytes_swar(word), q.byte_weight_sum);
    }
}
