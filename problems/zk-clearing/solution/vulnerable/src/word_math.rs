//! 64-bit word carry/borrow tracking and 128-bit carry-folded quotient kernels.
//!
//! Because two `u64` inputs `lhs` and `rhs` can sum to `[0, 2 * 2^64 - 2]`,
//! computing exact floor and ceiling quotients `floor((lhs + rhs) / D)` and
//! `ceil((lhs + rhs) / D)` without `u128` requires tracking the 1-bit carry flag
//! across the `2^64` word boundary and folding `2^64 = Q_64 * D + R_64`.

use crate::constants::*;

/// Represents the exact 65-bit sum `low_word + (high_carry as u64) * 2^64`
/// of two 64-bit unsigned words.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct WordSum {
    pub low_word: u64,
    pub high_carry: bool,
}

/// Represents the 64-bit wrapped difference `lhs.wrapping_sub(rhs)` together
/// with an explicit underflow borrow indicator (`lhs < rhs`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct WordDiff {
    pub diff_word: u64,
    pub underflow_borrow: bool,
}

/// Adds two `u64` words in 64-bit register arithmetic and captures the 64-bit
/// overflow carry flag (`low_word < lhs`).
#[inline]
pub fn add_u64_with_carry(lhs: u64, rhs: u64) -> WordSum {
    let low_word: u64 = lhs.wrapping_add(rhs);
    let high_carry: bool = low_word < lhs;
    WordSum {
        low_word,
        high_carry,
    }
}

/// Subtracts `rhs` from `lhs` in 64-bit register arithmetic and captures the
/// underflow borrow flag (`lhs < rhs`).
#[inline]
pub fn sub_u64_with_borrow(lhs: u64, rhs: u64) -> WordDiff {
    let diff_word: u64 = lhs.wrapping_sub(rhs);
    let underflow_borrow: bool = lhs < rhs;
    WordDiff {
        diff_word,
        underflow_borrow,
    }
}

/// Extracts the low 16-bit limb `word & 0xFFFF` (`word mod 2^16`).
#[inline]
pub fn extract_low_u16(word: u64) -> u64 {
    word & LIMB_MASK
}

/// Extracts the low 32-bit limb `word & 0xFFFF_FFFF` (`word mod 2^32`).
#[inline]
pub fn extract_low_u32(word: u64) -> u64 {
    word & LOW32_MASK
}

/// Extracts the high 32-bit limb `word >> 32` (`floor(word / 2^32)`).
#[inline]
pub fn extract_high_u32(word: u64) -> u64 {
    word >> 32u64
}

/// Recombines a 32-bit low limb and 32-bit high limb into a 64-bit word.
#[inline]
pub fn pack_u32_limbs(low_u32: u64, high_u32: u64) -> u64 {
    (low_u32 & LOW32_MASK) | ((high_u32 & LOW32_MASK) << 32u64)
}

/// Classifies whether a 65-bit combined notional `sum` meets or exceeds
/// `INSTITUTIONAL_BAND_MIN`.
#[inline]
pub fn is_institutional_notional(sum: WordSum) -> bool {
    if sum.high_carry {
        true
    } else {
        sum.low_word >= INSTITUTIONAL_BAND_MIN
    }
}

/// Computes the exact remainder `(lhs + rhs) mod BPS_DENOM` (`BPS_DENOM = 10_000`)
/// over the full 65-bit `WordSum` range in pure `u64` arithmetic.
#[inline]
pub fn rem_bps_u64(sum: WordSum) -> u64 {
    if sum.high_carry {
        ((sum.low_word % BPS_DENOM) + U64_MOD_BPS_REM) % BPS_DENOM
    } else {
        sum.low_word % BPS_DENOM
    }
}

/// Computes the exact floor quotient `floor((lhs + rhs) / BPS_DENOM)` (`BPS_DENOM = 10_000`)
/// over the full 65-bit `WordSum` range using pure `u64` carry folding.
#[inline]
pub fn floor_div_bps_u64(sum: WordSum) -> u64 {
    if sum.high_carry {
        let folded_rem: u64 = (sum.low_word % BPS_DENOM) + U64_MOD_BPS_REM;
        U64_MOD_BPS_QUOT + (sum.low_word / BPS_DENOM) + (folded_rem / BPS_DENOM)
    } else {
        sum.low_word / BPS_DENOM
    }
}

/// Computes the ceiling quotient `ceil((lhs + rhs) / BPS_DENOM)` (`BPS_DENOM = 10_000`),
/// equivalent in exact integer arithmetic to `floor((lhs + rhs + 9_999) / 10_000)`,
/// over the full 65-bit `WordSum` range using pure `u64` arithmetic.
#[inline]
pub fn ceil_div_bps_u64(sum: WordSum) -> u64 {
    if sum.high_carry {
        let folded_rem: u64 = (sum.low_word % BPS_DENOM) + U64_MOD_BPS_REM;
        U64_MOD_BPS_QUOT + (sum.low_word / BPS_DENOM) + ((folded_rem + BPS_MAX_REM) / BPS_DENOM)
    } else {
        let biased: u64 = sum.low_word.wrapping_add(BPS_MAX_REM);
        if biased < sum.low_word {
            (sum.low_word / BPS_DENOM) + (((sum.low_word % BPS_DENOM) + BPS_MAX_REM) / BPS_DENOM)
        } else {
            biased / BPS_DENOM
        }
    }
}

/// Computes the exact floor quotient `floor((lhs + rhs) / FLASH_DENOM)` (`FLASH_DENOM = 5_000`)
/// over the full 65-bit `WordSum` range in pure `u64` arithmetic.
#[inline]
pub fn floor_div_flash_u64(sum: WordSum) -> u64 {
    if sum.high_carry {
        let folded_rem: u64 = (sum.low_word % FLASH_DENOM) + U64_MOD_FLASH_REM;
        U64_MOD_FLASH_QUOT + (sum.low_word / FLASH_DENOM) + (folded_rem / FLASH_DENOM)
    } else {
        sum.low_word / FLASH_DENOM
    }
}

/// Computes the exact ceiling quotient `ceil((lhs + rhs) / FLASH_DENOM)` (`FLASH_DENOM = 5_000`),
/// equivalent to `floor((lhs + rhs + 4_999) / 5_000)`, in pure `u64` arithmetic.
#[inline]
pub fn ceil_div_flash_u64(sum: WordSum) -> u64 {
    if sum.high_carry {
        let folded_rem: u64 = (sum.low_word % FLASH_DENOM) + U64_MOD_FLASH_REM;
        U64_MOD_FLASH_QUOT + (sum.low_word / FLASH_DENOM) + ((folded_rem + FLASH_MAX_REM) / FLASH_DENOM)
    } else {
        let biased: u64 = sum.low_word.wrapping_add(FLASH_MAX_REM);
        if biased < sum.low_word {
            (sum.low_word / FLASH_DENOM) + (((sum.low_word % FLASH_DENOM) + FLASH_MAX_REM) / FLASH_DENOM)
        } else {
            biased / FLASH_DENOM
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn add_and_sub_carry_borrow_flags() {
        let s0 = add_u64_with_carry(100u64, 250u64);
        assert_eq!(s0.low_word, 350u64);
        assert!(!s0.high_carry);

        let s1 = add_u64_with_carry(u64::MAX, 1u64);
        assert_eq!(s1.low_word, 0u64);
        assert!(s1.high_carry);

        let d0 = sub_u64_with_borrow(500u64, 120u64);
        assert_eq!(d0.diff_word, 380u64);
        assert!(!d0.underflow_borrow);

        let d1 = sub_u64_with_borrow(10u64, 20u64);
        assert!(d1.underflow_borrow);
    }

    #[test]
    fn limb_extraction_and_packing_roundtrip() {
        let w: u64 = 0x1234_5678_9ABC_DEF0u64;
        assert_eq!(extract_low_u16(w), 0xDEF0u64);
        assert_eq!(extract_low_u32(w), 0x9ABC_DEF0u64);
        assert_eq!(extract_high_u32(w), 0x1234_5678u64);
        assert_eq!(pack_u32_limbs(extract_low_u32(w), extract_high_u32(w)), w);
    }

    #[test]
    fn bps_floor_and_ceil_at_zero_and_u64_max() {
        let z = add_u64_with_carry(0u64, 0u64);
        assert_eq!(floor_div_bps_u64(z), 0u64);
        assert_eq!(ceil_div_bps_u64(z), 0u64);
        assert_eq!(rem_bps_u64(z), 0u64);

        let one = add_u64_with_carry(1u64, 0u64);
        assert_eq!(floor_div_bps_u64(one), 0u64);
        assert_eq!(ceil_div_bps_u64(one), 1u64);
        assert_eq!(rem_bps_u64(one), 1u64);

        let at_max = add_u64_with_carry(0u64, u64::MAX);
        assert_eq!(floor_div_bps_u64(at_max), 1_844_674_407_370_955u64);
        assert_eq!(ceil_div_bps_u64(at_max), 1_844_674_407_370_956u64);
        assert_eq!(rem_bps_u64(at_max), 1_615u64);
    }

    #[test]
    fn bps_carry_folding_above_u64_max() {
        let wrapped = add_u64_with_carry(10_000u64, u64::MAX);
        assert!(wrapped.high_carry);
        assert_eq!(floor_div_bps_u64(wrapped), 1_844_674_407_370_956u64);
        assert_eq!(ceil_div_bps_u64(wrapped), 1_844_674_407_370_957u64);
        assert_eq!(rem_bps_u64(wrapped), 1_615u64);

        let double_max = add_u64_with_carry(u64::MAX, u64::MAX);
        assert_eq!(floor_div_bps_u64(double_max), 3_689_348_814_741_910u64);
        assert_eq!(ceil_div_bps_u64(double_max), 3_689_348_814_741_911u64);
    }

    #[test]
    fn flash_floor_and_ceil_across_boundaries() {
        let s = add_u64_with_carry(0u64, u64::MAX - 2_500u64);
        assert_eq!(ceil_div_flash_u64(s), 3_689_348_814_741_910u64);
        assert_eq!(floor_div_flash_u64(s), 3_689_348_814_741_909u64);

        let s_hi = add_u64_with_carry(u64::MAX, 5_000u64);
        assert!(is_institutional_notional(s_hi));
        assert_eq!(floor_div_flash_u64(s_hi), 3_689_348_814_741_911u64);
        assert_eq!(ceil_div_flash_u64(s_hi), 3_689_348_814_741_912u64);
    }
}
