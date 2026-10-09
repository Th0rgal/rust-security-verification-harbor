//! `recmo/goldilocks` 128-bit prime field reduction (`P_G = 2^64 - 2^32 + 1`)
//! for cross-chain L1 bridge verification fee quotes.
//!
//! Because `2^64 ≡ 2^32 - 1 = EPS (mod P_G)`, a 128-bit integer `x_lo + x_hi * 2^64`
//! is reduced modulo `P_G` in pure `u64` arithmetic by splitting `x_hi` into its
//! high 32-bit limb `x_hi_hi = x_hi >> 32` and low 32-bit limb `x_hi_lo = x_hi & EPS`:
//! 1. Subtract `x_hi_hi` from `x_lo` (compensating by `-EPS` on borrow).
//! 2. Add `x_hi_lo * EPS` (compensating by `+EPS` on 64-bit carry).
//! 3. Canonicalize into `[0, P_G - 1]` by subtracting `P_G` if `r >= P_G`.

use crate::constants::*;

/// Bridge verifier fee quote produced by Goldilocks 128-bit reduction.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct GoldilocksQuote {
    pub folded_low: u64,
    pub canonical_residue: u64,
    pub bridge_fee: u64,
}

/// Performs the first Goldilocks folding step `x_lo - (x_hi >> 32) mod 2^64`,
/// returning `(r0, borrow)`.
#[inline]
pub fn reduce_goldilocks_step1(x_lo: u64, x_hi: u64) -> (u64, bool) {
    let x_hi_hi: u64 = x_hi >> 32u64;
    x_lo.overflowing_sub(x_hi_hi)
}

/// Reduces a 128-bit value `(x_lo, x_hi)` modulo the Goldilocks prime
/// `GOLDILOCKS_P = 0xFFFF_FFFF_0000_0001` in pure `u64` arithmetic.
#[inline]
pub fn reduce_goldilocks_128(x_lo: u64, x_hi: u64) -> u64 {
    let x_hi_lo: u64 = x_hi & GOLDILOCKS_EPS;
    let (t0, borrow): (u64, bool) = reduce_goldilocks_step1(x_lo, x_hi);
    let t1: u64 = if borrow {
        t0.wrapping_sub(GOLDILOCKS_EPS)
    } else {
        t0
    };
    let prod: u64 = x_hi_lo * GOLDILOCKS_EPS;
    let (t2, carry): (u64, bool) = t1.overflowing_add(prod);
    let t3: u64 = if carry {
        t2.wrapping_add(GOLDILOCKS_EPS)
    } else {
        t2
    };
    if t3 >= GOLDILOCKS_P {
        t3 - GOLDILOCKS_P
    } else {
        t3
    }
}

/// Canonicalizes a single 64-bit word `x` modulo `GOLDILOCKS_P`.
#[inline]
pub fn canonicalize_goldilocks_u64(x: u64) -> u64 {
    if x >= GOLDILOCKS_P {
        x - GOLDILOCKS_P
    } else {
        x
    }
}

/// Canonical modular addition `(a + b) mod GOLDILOCKS_P` for `a, b < GOLDILOCKS_P`.
#[inline]
pub fn add_goldilocks_mod(a: u64, b: u64) -> u64 {
    reduce_goldilocks_128(a.wrapping_add(b), if a.wrapping_add(b) < a { 1u64 } else { 0u64 })
}

/// Canonical modular subtraction `(a - b) mod GOLDILOCKS_P` for `a, b < GOLDILOCKS_P`.
#[inline]
pub fn sub_goldilocks_mod(a: u64, b: u64) -> u64 {
    let ca: u64 = canonicalize_goldilocks_u64(a);
    let cb: u64 = canonicalize_goldilocks_u64(b);
    if ca >= cb {
        ca - cb
    } else {
        (GOLDILOCKS_P - cb) + ca
    }
}

/// Folds a 64-bit commitment word with a 32-bit challenge scalar in the Goldilocks field.
#[inline]
pub fn fold_goldilocks_challenge(commitment: u64, challenge_u32: u64) -> u64 {
    let scalar: u64 = challenge_u32 & LOW32_MASK;
    let lo_limb: u64 = commitment & LOW32_MASK;
    let hi_limb: u64 = commitment >> 32u64;
    let prod_lo: u64 = lo_limb * scalar;
    let prod_hi: u64 = hi_limb * scalar;
    let x_lo: u64 = prod_lo.wrapping_add(prod_hi << 32u64);
    let carry: u64 = if x_lo < prod_lo { 1u64 } else { 0u64 };
    let x_hi: u64 = (prod_hi >> 32u64) + carry;
    reduce_goldilocks_128(x_lo, x_hi)
}

/// Quotes a cross-chain bridge verifier fee from `(amount, fee)` in the Goldilocks field.
#[inline]
pub fn quote_bridge_verifier_fee(amount: u64, fee: u64) -> GoldilocksQuote {
    let (folded_low, _borrow): (u64, bool) = reduce_goldilocks_step1(amount, fee);
    let canonical_residue: u64 = reduce_goldilocks_128(amount, fee);
    let bridge_fee: u64 = (amount >> 32u64) + (canonical_residue & LOW32_MASK);
    GoldilocksQuote {
        folded_low,
        canonical_residue,
        bridge_fee,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn goldilocks_canonicalization_at_modulus_boundary() {
        assert_eq!(reduce_goldilocks_128(0u64, 0u64), 0u64);
        assert_eq!(reduce_goldilocks_128(GOLDILOCKS_P, 0u64), 0u64);
        assert_eq!(reduce_goldilocks_128(0u64, 1u64), GOLDILOCKS_EPS);
        assert_eq!(reduce_goldilocks_128(0u64, 4_294_967_296u64), GOLDILOCKS_P - 1u64);
        assert_eq!(reduce_goldilocks_128(1u64, 4_294_967_296u64), 0u64);
        assert_eq!(canonicalize_goldilocks_u64(GOLDILOCKS_P + 5u64), 5u64);
    }

    #[test]
    fn goldilocks_bridge_quote_and_modular_add_sub() {
        let q = quote_bridge_verifier_fee(100u64, 0u64);
        assert_eq!(q.canonical_residue, 100u64);
        assert_eq!(add_goldilocks_mod(GOLDILOCKS_P - 1u64, 1u64), 0u64);
        assert_eq!(add_goldilocks_mod(GOLDILOCKS_P - 10u64, 25u64), 15u64);
        assert_eq!(sub_goldilocks_mod(10u64, 25u64), GOLDILOCKS_P - 15u64);
    }

    #[test]
    fn goldilocks_challenge_folding_matches_128_reduction() {
        let c = fold_goldilocks_challenge(0x1_0000_0002u64, 3u64);
        assert_eq!(c, 0x3_0000_0006u64);
    }
}
