#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Authorization {
    pub total_debit: u64,
}

pub mod broadword {
    pub const L8: u64 = 0x0101_0101_0101_0101u64;
    pub const H8: u64 = 0x8080_8080_8080_8080u64;
    pub const M16: u64 = 0x00FF_00FF_00FF_00FFu64;
    pub const L16: u64 = 0x0001_0001_0001_0001u64;

    /// Vigna's SWAR broadword non-zero byte indicator (`tov/succinct-rs` `src/broadword.rs`):
    /// Sets bit `8*i + 7` iff byte `i` of `x` is non-zero.
    #[inline]
    pub fn u_nz8(x: u64) -> u64 {
        (((x | H8) - L8) | x) & H8
    }

    /// Count non-zero bytes in `x` in parallel using SWAR multiplication by `L8`.
    #[inline]
    pub fn count_nz_bytes(x: u64) -> u64 {
        ((u_nz8(x) >> 7u64).wrapping_mul(L8)) >> 56u64
    }

    /// Sum all 8 bytes of `x` in parallel using 16-bit lane folding and `L16`.
    #[inline]
    pub fn sum_bytes(x: u64) -> u64 {
        let pairs: u64 = (x & M16) + ((x >> 8u64) & M16);
        (pairs.wrapping_mul(L16) >> 48u64) & 0xFFFFu64
    }
}

pub mod settlement {
    use crate::Authorization;
    use crate::broadword;

    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub struct SuccinctQuote {
        pub principal_share: u64,
        pub active_bytes: u64,
        pub byte_sum: u64,
        pub total_debit: u64,
    }

    #[inline]
    pub fn build_quote(amount: u64, fee: u64) -> Option<SuccinctQuote> {
        let principal_share: u64 = amount >> 1u64;
        let active_bytes: u64 = broadword::count_nz_bytes(fee);
        let byte_sum: u64 = broadword::sum_bytes(fee);
        let total_debit: u64 = principal_share + (active_bytes << 8u64) + byte_sum;
        Some(SuccinctQuote {
            principal_share,
            active_bytes,
            byte_sum,
            total_debit,
        })
    }

    #[inline]
    pub fn verify_affordability(balance: u64, quote: SuccinctQuote) -> Option<Authorization> {
        if quote.total_debit <= balance {
            Some(Authorization {
                total_debit: quote.total_debit,
            })
        } else {
            None
        }
    }
}

/// Authorize a Succinct SWAR broadword byte-schedule settlement against `balance`.
///
/// In exact integer arithmetic, let the 8 bytes of `fee` be
/// `b_i = (fee >> (8 * i)) & 0xFF` for `i in {0, ..., 7}`:
/// - `active_bytes = sum_{i=0..7} (if b_i > 0 then 1 else 0)`
/// - `byte_sum = sum_{i=0..7} b_i`
/// - `total_debit = floor(amount / 2) + 256 * active_bytes + byte_sum`
///
/// The payment is authorized iff `total_debit <= balance`.
/// Production code in this crate operates on `u64` words only (`u128` is not used).
pub fn authorize(balance: u64, amount: u64, fee: u64) -> Option<Authorization> {
    let quote: settlement::SuccinctQuote = settlement::build_quote(amount, fee)?;
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
    fn low_bit_bytes_are_counted_and_summed() {
        // fee = 0x0000_0000_0000_0201 -> b0 = 1, b1 = 2 -> active = 2, sum = 3
        // total_debit = 50 + 2 * 256 + 3 = 565
        assert_eq!(
            authorize(565, 100, 0x0201),
            Some(Authorization { total_debit: 565 })
        );
        assert_eq!(authorize(564, 100, 0x0201), None);
    }

    #[test]
    fn full_low_bits_across_all_bytes() {
        // fee = L8 -> all 8 bytes = 1 -> active = 8, sum = 8 -> surcharge = 8 * 256 + 8 = 2056
        assert_eq!(
            authorize(2056, 0, broadword::L8),
            Some(Authorization { total_debit: 2056 })
        );
    }
}
