//! `Plonky3` BabyBear (`P = 2_013_265_921 = 2^31 - 2^27 + 1`) 64-bit Montgomery
//! reduction and STARK prover transcript commitment levy calculator.
//!
//! For radix `R = 2^32 = 4_294_967_296` and prime `P = 2_013_265_921`:
//! - `R^{-1} mod P = 943_718_400`
//! - `MU = -P^{-1} mod R = 2_281_701_377`
//! Given a 64-bit packed transcript state `x < P * R`:
//! 1. `t = ((x mod R) * MU) mod R`
//! 2. `u = t * P` (so `x - u` is an exact multiple of `R = 2^32` in `(-P * R, P * R)`)
//! 3. If `x < u`, `(x - u) / R + P` is computed in `u64` via
//!    `P + (x.wrapping_sub(u) / R) - R`; otherwise `(x - u) / R`.
//! The result equals `(x * R^{-1}) mod P` in `[0, P - 1]`.

use crate::constants::*;

/// Captures the packed 64-bit transcript state, Montgomery quotient limb `t`,
/// and canonical BabyBear field element `prover_levy in [0, BABYBEAR_P - 1]`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ProverLevyQuote {
    pub packed_transcript: u64,
    pub monty_t: u64,
    pub prover_levy: u64,
}

/// Packs the low 32-bit limb of `amount` (`amount mod 2^32`) and the canonical
/// BabyBear residue of `fee` (`fee mod P`) into a 64-bit transcript integer
/// `x = (amount % 2^32) + (fee % P) * 2^32 < P * 2^32`.
#[inline]
pub fn pack_transcript(amount: u64, fee: u64) -> u64 {
    (amount % LIMB_BASE) + (fee % BABYBEAR_P) * LIMB_BASE
}

/// Computes the 32-bit Montgomery reduction multiplier `t = ((x mod 2^32) * MU) mod 2^32`.
#[inline]
pub fn monty_quotient(x: u64) -> u64 {
    ((x % LIMB_BASE) * BABYBEAR_MU) % LIMB_BASE
}

/// Performs 64-bit BabyBear Montgomery reduction on `x < BABYBEAR_P * 2^32`,
/// returning `(x * 943_718_400) mod 2_013_265_921` in pure `u64` arithmetic.
#[inline]
pub fn monty_reduce(x: u64) -> u64 {
    let t: u64 = monty_quotient(x);
    let u: u64 = BABYBEAR_P * t;
    let diff: u64 = x.wrapping_sub(u);
    let hi: u64 = diff / LIMB_BASE;
    if x < u {
        BABYBEAR_P + hi - LIMB_BASE
    } else {
        hi
    }
}

/// Performs Montgomery multiplication `(a * b * R^{-1}) mod BABYBEAR_P`
/// for two BabyBear field elements `a, b < BABYBEAR_P`.
#[inline]
pub fn monty_mul_babybear(a: u64, b: u64) -> u64 {
    let prod: u64 = (a % BABYBEAR_P) * (b % BABYBEAR_P);
    monty_reduce(prod)
}

/// Canonical modular addition `(a + b) mod BABYBEAR_P` for `a, b < BABYBEAR_P`.
#[inline]
pub fn canonical_add_babybear(a: u64, b: u64) -> u64 {
    let sum: u64 = a + b;
    if sum >= BABYBEAR_P {
        sum - BABYBEAR_P
    } else {
        sum
    }
}

/// Canonical modular subtraction `(a - b) mod BABYBEAR_P` for `a, b < BABYBEAR_P`.
#[inline]
pub fn canonical_sub_babybear(a: u64, b: u64) -> u64 {
    if a >= b {
        a - b
    } else {
        (a + BABYBEAR_P) - b
    }
}

/// Quotes the STARK prover transcript commitment levy for `(amount, fee)`:
/// `prover_levy = monty_reduce(pack_transcript(amount, fee))`.
#[inline]
pub fn quote_prover_transcript_levy(amount: u64, fee: u64) -> ProverLevyQuote {
    let packed_transcript: u64 = pack_transcript(amount, fee);
    let monty_t: u64 = monty_quotient(packed_transcript);
    let prover_levy: u64 = monty_reduce(packed_transcript);
    ProverLevyQuote {
        packed_transcript,
        monty_t,
        prover_levy,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn monty_reduce_zero_and_multiples_of_p() {
        assert_eq!(monty_reduce(0u64), 0u64);
        assert_eq!(monty_reduce(BABYBEAR_P), 0u64);
        assert_eq!(monty_reduce(BABYBEAR_P * 42u64), 0u64);
    }

    #[test]
    fn monty_reduce_radix_r_gives_one() {
        assert_eq!(monty_reduce(LIMB_BASE), 1u64);
        let q = quote_prover_transcript_levy(0u64, 1u64);
        assert_eq!(q.prover_levy, 1u64);
    }

    #[test]
    fn monty_reduce_underflow_branch_and_non_underflow_branch() {
        let q_under = quote_prover_transcript_levy(1u64, 0u64);
        assert_eq!(q_under.prover_levy, 943_718_400u64);

        assert_eq!(monty_reduce(BABYBEAR_P), 0u64);

        let q_high = quote_prover_transcript_levy(u64::MAX, BABYBEAR_P - 1u64);
        assert_eq!(q_high.prover_levy, 1_069_547_521u64);
    }

    #[test]
    fn canonical_babybear_ring_operations() {
        assert_eq!(canonical_add_babybear(BABYBEAR_P - 1u64, 2u64), 1u64);
        assert_eq!(canonical_sub_babybear(1u64, 2u64), BABYBEAR_P - 1u64);
        let r_mod_p: u64 = LIMB_BASE % BABYBEAR_P;
        assert_eq!(monty_mul_babybear(17u64, r_mod_p), 17u64);
    }
}
