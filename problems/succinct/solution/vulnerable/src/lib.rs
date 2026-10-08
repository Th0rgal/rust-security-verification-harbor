#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Authorization {
    pub total_debit: u64,
}

pub mod broadword {
    pub const L8: u64 = 0x0101_0101_0101_0101u64;
    pub const H8: u64 = 0x8080_8080_8080_8080u64;
    pub const M16: u64 = 0x00FF_00FF_00FF_00FFu64;
    pub const L16: u64 = 0x0001_0001_0001_0001u64;

    #[inline]
    pub fn u_nz8(x: u64) -> u64 {
        (((x | H8) - L8) | x) & H8
    }

    #[inline]
    pub fn count_nz_bytes(x: u64) -> u64 {
        ((u_nz8(x) >> 7u64).wrapping_mul(L8)) >> 56u64
    }

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

pub fn authorize(balance: u64, amount: u64, fee: u64) -> Option<Authorization> {
    let quote: settlement::SuccinctQuote = settlement::build_quote(amount, fee)?;
    settlement::verify_affordability(balance, quote)
}
