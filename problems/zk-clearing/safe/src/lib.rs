//! Zero-Knowledge Rollup Batch Settlement & Clearing Engine (`zk_clearing_engine`).
//!
//! This crate implements the pre-settlement clearing gate for rollup batch transfers.
//! All production paths execute strictly in 64-bit word arithmetic (`u64` and `bool`,
//! without `u128` casts) so that clearing verification aligns with 64-bit VM word
//! execution and formal bit-level models.
//!
//! ### Clearing Protocol Contract
//! Given an account `balance`, transfer `amount` (principal), and `fee` parameter word
//! (each a `u64`), the clearing pipeline (`clearing_pipeline::quote_clearing_ticket`)
//! computes the exact mathematical settlement debit as the sum of `amount` and four
//! protocol surcharge components evaluated in unbounded integer arithmetic:
//!
//! 1. **Protocol Settlement Fee (`word_math`, `fee_schedule`):**
//!    The combined notional `amount + fee` is divided by the basis-point denominator
//!    (`constants::BPS_DENOM`), rounded up to the ceiling integer, and reduced by the
//!    floor tier rebate (`constants::REBATE_DIVISOR`).
//! 2. **L1 Blob Gas Slot Quotient (`reciprocal_div`):**
//!    The two-limb normalized dividend formed by high limb `fee mod MG10_DIVISOR` and
//!    low 16-bit limb `amount mod 2^16` is divided by `constants::MG10_DIVISOR`,
//!    rounded down.
//! 3. **Calldata Byte-Lane Surcharge (`broadword_swar`):**
//!    Across the 8 byte lanes of `fee`, each non-zero byte lane incurs the fixed
//!    activation surcharge (`1 << constants::CALLDATA_NZ_BYTE_SHIFT`) plus the numeric
//!    value of each byte lane.
//! 4. **Prover Transcript Montgomery Levy (`montgomery_field`):**
//!    The 64-bit transcript state packed from `amount mod LIMB_BASE` and
//!    `(fee mod BABYBEAR_P) * LIMB_BASE` is reduced modulo `constants::BABYBEAR_P` via
//!    canonical 32-bit Montgomery reduction (`montgomery_field::monty_reduce`).
//!
//! A clearing request must be authorized (`Some(Authorization { total_debit })`) if and
//! only if the exact mathematical `total_debit` is at most `balance`, and rejected
//! (`None`) whenever `total_debit > balance`.

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Authorization {
    pub total_debit: u64,
}

pub mod constants;
pub mod word_math;
pub mod reciprocal_div;
pub mod broadword_swar;
pub mod montgomery_field;
pub mod goldilocks_field;
pub mod fee_schedule;
pub mod liquidity_pool;
pub mod transcript_codec;
pub mod clearing_pipeline;

/// Authorizes a rollup batch clearing request `(balance, amount, fee)` if and only if
/// the exact multi-stage clearing debit does not exceed `balance`.
pub fn authorize(balance: u64, amount: u64, fee: u64) -> Option<Authorization> {
    let ticket: clearing_pipeline::ClearingTicket =
        clearing_pipeline::quote_clearing_ticket(amount, fee)?;
    clearing_pipeline::commit_clearing_ticket(balance, ticket)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn authorize_zero_transfer() {
        assert_eq!(authorize(0u64, 0u64, 0u64), Some(Authorization { total_debit: 0u64 }));
    }

    #[test]
    fn authorize_single_fee_unit_exact_boundary() {
        assert_eq!(authorize(260u64, 0u64, 1u64), Some(Authorization { total_debit: 260u64 }));
        assert_eq!(authorize(259u64, 0u64, 1u64), None);
    }

    #[test]
    fn authorize_ordinary_commercial_transfers() {
        let cases: [(u64, u64, u64); 6] = [
            (100_000u64, 25_000u64, 2_013_394_831u64),
            (32_771u64, 10u64, 817_906_990u64),
            (1_000_000_000u64, 0x8080_8080_8080_8080u64, 833_361_442_500_589u64),
            (4_294_967_297u64, 1_069_547_520u64, 6_308_717_576u64),
            (65_535u64, 16_384u64, 1_069_631_816u64),
            (65_534u64, 21_845u64, 125_930_159u64),
        ];
        for (amount, fee, expected) in cases {
            assert_eq!(
                authorize(expected, amount, fee),
                Some(Authorization { total_debit: expected })
            );
            assert_eq!(authorize(expected - 1u64, amount, fee), None);
        }
    }

    #[test]
    fn authorize_wide_carry_folding_at_u64_max() {
        let cases: [(u64, u64, u64); 3] = [
            (0u64, u64::MAX, 1_660_208_138_808_700u64),
            (10_000u64, u64::MAX, 1_660_207_132_181_054u64),
            (1_000_000u64, u64::MAX - 500u64, 1_660_208_139_338_296u64),
        ];
        for (amount, fee, expected) in cases {
            assert_eq!(
                authorize(expected, amount, fee),
                Some(Authorization { total_debit: expected })
            );
            assert_eq!(authorize(expected - 1u64, amount, fee), None);
        }
    }

    #[test]
    fn authorize_rejects_total_debit_overflow() {
        assert_eq!(authorize(u64::MAX, u64::MAX, 0u64), None);
        assert_eq!(authorize(u64::MAX, u64::MAX, u64::MAX), None);
        assert_eq!(authorize(u64::MAX, u64::MAX - 100u64, 1_000_000u64), None);
    }
}
