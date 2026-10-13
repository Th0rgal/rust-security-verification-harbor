#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Authorization {
    pub total_debit: u64,
}

pub mod mixed_radix {
    pub const RADIX_MASK: u64 = 0xFFFFu64;
    pub const SHIFT_16: u64 = 16u64;
    pub const SHIFT_32: u64 = 32u64;
    pub const SHIFT_48: u64 = 48u64;

    #[inline]
    pub fn clamp_digit(a: u64, b: u64) -> u64 {
        if a < b {
            a
        } else {
            b - 1u64
        }
    }

    /// Encode a 4-level mixed-radix coordinate `(d0, d1, d2, d3)` with radices
    /// `(b0, b1, b2, b3)` in `[1, 65536]` extracted from `fee` (`waugh_indexer::MixedRadix`).
    #[inline]
    pub fn encode(amount: u64, fee: u64) -> u64 {
        let b0: u64 = (fee & RADIX_MASK) + 1u64;
        let b1: u64 = ((fee >> SHIFT_16) & RADIX_MASK) + 1u64;
        let b2: u64 = ((fee >> SHIFT_32) & RADIX_MASK) + 1u64;
        let b3: u64 = ((fee >> SHIFT_48) & RADIX_MASK) + 1u64;
        let a0: u64 = amount & RADIX_MASK;
        let a1: u64 = (amount >> SHIFT_16) & RADIX_MASK;
        let a2: u64 = (amount >> SHIFT_32) & RADIX_MASK;
        let a3: u64 = (amount >> SHIFT_48) & RADIX_MASK;
        let d0: u64 = clamp_digit(a0, b0);
        let d1: u64 = clamp_digit(a1, b1);
        let d2: u64 = clamp_digit(a2, b2);
        let d3: u64 = clamp_digit(a3, b3);
        let o2: u64 = b3;
        let o1: u64 = b2 * o2;
        let o0: u64 = b1 * o1;
        let raw_idx: u64 = d0 * o0 + d1 * o1 + d2 * o2 + d3;
        let space_size: u64 = o0.wrapping_mul(b0);
        if raw_idx < space_size {
            raw_idx
        } else {
            0u64
        }
    }
}

pub mod settlement {
    use crate::Authorization;
    use crate::mixed_radix;

    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub struct OpenPqlQuote {
        pub principal_share: u64,
        pub encoded_idx: u64,
        pub index_surcharge: u64,
        pub total_debit: u64,
    }

    #[inline]
    pub fn build_quote(amount: u64, fee: u64) -> Option<OpenPqlQuote> {
        let principal_share: u64 = amount >> 1u64;
        let encoded_idx: u64 = mixed_radix::encode(amount, fee);
        let index_surcharge: u64 = encoded_idx >> 1u64;
        let total_debit: u64 = principal_share + index_surcharge;
        Some(OpenPqlQuote {
            principal_share,
            encoded_idx,
            index_surcharge,
            total_debit,
        })
    }

    #[inline]
    pub fn verify_affordability(balance: u64, quote: OpenPqlQuote) -> Option<Authorization> {
        if quote.total_debit <= balance {
            Some(Authorization {
                total_debit: quote.total_debit,
            })
        } else {
            None
        }
    }
}

/// Authorize an OpenPQL 4-level mixed-radix settlement against `balance`.
///
/// In exact integer arithmetic:
/// - For `i in {0, 1, 2, 3}`:
///   - `b_i = ((fee >> (16 * i)) & 0xFFFF) + 1` in `[1, 65536]`
///   - `a_i = (amount >> (16 * i)) & 0xFFFF` in `[0, 65535]`
///   - `d_i = min(a_i, b_i - 1)`
/// - Suffix-product offsets: `o2 = b3`, `o1 = b2 * o2`, `o0 = b1 * o1`
/// - `encoded_idx = d0 * o0 + d1 * o1 + d2 * o2 + d3`
/// - `total_debit = floor(amount / 2) + floor(encoded_idx / 2)`
///
/// The payment is authorized iff `total_debit <= balance`.
/// Production code in this crate operates on `u64` words only (`u128` is not used).
pub fn authorize(balance: u64, amount: u64, fee: u64) -> Option<Authorization> {
    let quote: settlement::OpenPqlQuote = settlement::build_quote(amount, fee)?;
    settlement::verify_affordability(balance, quote)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn zero_payment_is_authorized() {
        assert_eq!(authorize(0, 0, 0), Some(Authorization { total_debit: 0 }));
    }

    #[test]
    fn small_mixed_radix_coordinates_match_policy() {
        let fee: u64 = 0x0003_0003_0003_0003;
        let amount: u64 = 0x0001_0002_0001_0002;
        assert_eq!(
            authorize(140_741_783_355_469, amount, fee),
            Some(Authorization {
                total_debit: 140_741_783_355_469
            })
        );
        assert_eq!(authorize(140_741_783_355_468, amount, fee), None);
    }

    #[test]
    fn clamps_digits_to_radix_minus_one() {
        assert_eq!(
            authorize(50, 100, 0),
            Some(Authorization { total_debit: 50 })
        );
    }
}
