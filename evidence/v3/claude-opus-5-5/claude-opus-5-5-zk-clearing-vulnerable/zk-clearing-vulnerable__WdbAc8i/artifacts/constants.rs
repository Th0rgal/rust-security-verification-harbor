//! Protocol-wide arithmetic constants, prime field moduli, reciprocal multipliers,
//! broadword SWAR bitmasks, and 64-bit word carry-folding parameters for the
//! rollup batch settlement and clearing engine.
//!
//! All arithmetic throughout the clearing crate executes natively on 64-bit machine
//! words (`u64`) without `u128` promotion so that settlement verification matches
//! single-word VM register semantics.

/// Standard protocol fee basis-point denominator (`100% = 10_000 bps`).
pub const BPS_DENOM: u64 = 10_000u64;

/// Maximum non-zero remainder modulo `BPS_DENOM` (`BPS_DENOM - 1`).
pub const BPS_MAX_REM: u64 = 9_999u64;

/// Exact floor quotient of `2^64` divided by `BPS_DENOM`:
/// `floor(18_446_744_073_709_551_616 / 10_000) = 1_844_674_407_370_955`.
pub const U64_MOD_BPS_QUOT: u64 = 1_844_674_407_370_955u64;

/// Exact positive remainder of `2^64` modulo `BPS_DENOM`:
/// `18_446_744_073_709_551_616 % 10_000 = 1_616`.
pub const U64_MOD_BPS_REM: u64 = 1_616u64;

/// Protocol tier rebate divisor (`10` corresponds to a 10% floor rebate on gross fee).
pub const REBATE_DIVISOR: u64 = 10u64;

/// Passive maker rebate cap divisor (`5` corresponds to a 20% cap on passive limit orders).
pub const MAKER_REBATE_CAP_DIVISOR: u64 = 5u64;

/// Protocol reserve treasury cut divisor (`4` corresponds to 25% of net fee retained by treasury).
pub const TREASURY_CUT_DIVISOR: u64 = 4u64;

/// Flash-settlement liquidity surcharge denominator (`5_000` = 2 bps per notional unit).
pub const FLASH_DENOM: u64 = 5_000u64;

/// Maximum non-zero remainder modulo `FLASH_DENOM` (`FLASH_DENOM - 1`).
pub const FLASH_MAX_REM: u64 = 4_999u64;

/// Exact floor quotient of `2^64` divided by `FLASH_DENOM`:
/// `floor(18_446_744_073_709_551_616 / 5_000) = 3_689_348_814_741_910`.
pub const U64_MOD_FLASH_QUOT: u64 = 3_689_348_814_741_910u64;

/// Exact positive remainder of `2^64` modulo `FLASH_DENOM`:
/// `18_446_744_073_709_551_616 % 5_000 = 1_616`.
pub const U64_MOD_FLASH_REM: u64 = 1_616u64;

/// Minimum combined notional classified as institutional settlement volume.
pub const INSTITUTIONAL_BAND_MIN: u64 = 10_000_000_000_000u64;

/// Normalized 16-bit Möller-Granlund divisor `D = 0x8003 = 32_771` (`2^15 + 3`)
/// used to partition L1 data-availability blob gas slots.
pub const MG10_DIVISOR: u64 = 0x8003u64;

/// Precomputed 16-bit Möller-Granlund reciprocal `V = floor((2^32 - 1) / D) - 2^16 = 0xFFF4 = 65_524`.
pub const MG10_RECIPROCAL: u64 = 0xFFF4u64;

/// 16-bit limb extraction mask (`2^16 - 1 = 0xFFFF = 65_535`).
pub const LIMB_MASK: u64 = 0xFFFFu64;

/// Unsigned borrow-prevention bias `0xC000_0000 = 3_221_225_472` (`49_152 * 2^16`),
/// which is an exact multiple of `2^16` exceeding `65_535 * MG10_DIVISOR`.
pub const SUB_BIAS: u64 = 0xC000_0000u64;

/// Nominal gas units allocated per L1 data-availability blob slot (`128 KiB = 131_072`).
pub const BLOB_GAS_PER_SLOT: u64 = 131_072u64;

/// SWAR 8-lane byte broadcast mask of `0x01` (`0x0101_0101_0101_0101`).
pub const L8_MASK: u64 = 0x0101_0101_0101_0101u64;

/// SWAR 8-lane byte high-bit mask of `0x80` (`0x8080_8080_8080_8080`).
pub const H8_MASK: u64 = 0x8080_8080_8080_8080u64;

/// SWAR alternating 16-bit lane mask (`0x00FF_00FF_00FF_00FF`).
pub const M16_MASK: u64 = 0x00FF_00FF_00FF_00FFu64;

/// SWAR 16-bit lane broadcast multiplier (`0x0001_0001_0001_0001`).
pub const L16_MASK: u64 = 0x0001_0001_0001_0001u64;

/// Calldata surcharge shift per active non-zero byte lane (`2^8 = 256` units per non-zero byte).
pub const CALLDATA_NZ_BYTE_SHIFT: u64 = 8u64;

/// BabyBear STARK prime modulus `P = 2^31 - 2^27 + 1 = 2_013_265_921` (`0x7800_0001`).
pub const BABYBEAR_P: u64 = 2_013_265_921u64;

/// Negative modular inverse of `BABYBEAR_P` modulo `2^32`:
/// `MU = -P^{-1} mod 2^32 = 2_281_701_377` (`0x87FF_FFFF`).
pub const BABYBEAR_MU: u64 = 2_281_701_377u64;

/// 32-bit Montgomery radix `R = 2^32 = 4_294_967_296`.
pub const LIMB_BASE: u64 = 4_294_967_296u64;

/// 32-bit low-limb mask (`2^32 - 1 = 0xFFFF_FFFF`).
pub const LOW32_MASK: u64 = 0xFFFF_FFFFu64;

/// Goldilocks 64-bit prime modulus `P_G = 2^64 - 2^32 + 1 = 0xFFFF_FFFF_0000_0001`.
pub const GOLDILOCKS_P: u64 = 0xFFFF_FFFF_0000_0001u64;

/// Goldilocks reduction epsilon `EPS = 2^32 - 1 = 0xFFFF_FFFF` (`2^64 ≡ EPS (mod P_G)`).
pub const GOLDILOCKS_EPS: u64 = 0xFFFF_FFFFu64;

/// Transcript header domain tag mask (`0xFF`).
pub const CODEC_TAG_MASK: u64 = 0xFFu64;

/// Canonical protocol version identifier (`v3 = 3`).
pub const CODEC_VERSION_V3: u64 = 3u64;

/// Default L2 batch sequencer domain tag (`0x5A = 90`).
pub const SEQUENCER_DOMAIN_TAG: u64 = 0x5Au64;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn babybear_and_goldilocks_radix_identities() {
        assert_eq!(LIMB_BASE, 1u64 << 32u64);
        assert_eq!(LOW32_MASK, LIMB_BASE - 1u64);
        assert_eq!(GOLDILOCKS_P.wrapping_add(GOLDILOCKS_EPS), 0u64);
        assert_eq!(MG10_DIVISOR, (1u64 << 15u64) + 3u64);
    }

    #[test]
    fn swar_mask_lane_alignment() {
        assert_eq!(L8_MASK * 255u64, u64::MAX);
        assert_eq!(L8_MASK << 7u64, H8_MASK);
        assert_eq!(M16_MASK | (M16_MASK << 8u64), u64::MAX);
        assert_eq!(L16_MASK * 65_535u64, u64::MAX);
    }
}
