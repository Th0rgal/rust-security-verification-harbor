//! Zero-Knowledge Rollup Batch Settlement & Clearing Engine (`zk_clearing_engine`).
//!
//! This crate implements the pre-settlement clearing gate for rollup batch transfers.
//! All production paths execute strictly in 64-bit word arithmetic (`u64` and `bool`,
//! without `u128` casts) so that clearing verification aligns with 64-bit VM word
//! execution and formal bit-level models.
//!
//! ### Clearing Protocol Contract
//! Given an account `balance`, transfer `amount` (principal), and `fee` parameter word
//! (each a `u64`), the clearing pipeline (`clearing_pipeline::quote_clearing_ticket`
//! and `clearing_pipeline::commit_clearing_ticket`) evaluates all active protocol
//! surcharge stages in `clearing_pipeline::compute_clearing_breakdown(amount, fee)`
//! and adds their combined surcharge to `amount`.
//!
//! A clearing request must be authorized (`Some(Authorization { total_debit })`) if and
//! only if the exact mathematical `total_debit` across `amount` and all active stages
//! of `clearing_pipeline::compute_clearing_breakdown` is at most `balance`, and rejected
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
        assert_eq!(authorize(90u64, 0u64, 0u64), Some(Authorization { total_debit: 90u64 }));
        assert_eq!(authorize(89u64, 0u64, 0u64), None);
    }

    #[test]
    fn authorize_single_fee_unit_exact_boundary() {
        assert_eq!(
            authorize(4_294_967_557u64, 0u64, 1u64),
            Some(Authorization { total_debit: 4_294_967_557u64 })
        );
        assert_eq!(authorize(4_294_967_556u64, 0u64, 1u64), None);
    }

    #[test]
    fn authorize_ordinary_commercial_transfers() {
        let cases: [(u64, u64, u64); 6] = [
            (100_000u64, 25_000u64, 107_376_195_870_018u64),
            (32_771u64, 10u64, 43_767_612_727u64),
            (1_000_000_000u64, 0x8080_8080_8080_8080u64, 9_261_764_410_567_240_478u64),
            (4_294_967_297u64, 1_069_547_520u64, 4_593_671_629_452_848_041u64),
            (65_535u64, 16_384u64, 70_369_813_858_734u64),
            (65_534u64, 21_845u64, 93_823_686_555_067u64),
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
    fn authorize_wide_carry_folding_at_goldilocks_modulus() {
        let cases: [(u64, u64, u64); 3] = [
            (0u64, constants::GOLDILOCKS_P, 4_427_219_480_397_035u64),
            (10_000u64, constants::GOLDILOCKS_P, 4_427_220_487_045_311u64),
            (1_000_000u64, constants::GOLDILOCKS_P + 1u64, 4_427_223_776_895_826u64),
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
