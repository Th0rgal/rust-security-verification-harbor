#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Authorization {
    pub total_debit: u64,
}

pub mod mg10 {
    pub const MG10_DIVISOR: u64 = 0x8003u64;
    pub const MG10_RECIPROCAL: u64 = 0xFFF4u64;
    pub const LIMB_MASK: u64 = 0xFFFFu64;
    pub const SUB_BIAS: u64 = 0xC000_0000u64;

    #[inline]
    pub fn div_2x1_mg10(u1: u64, u0: u64) -> u64 {
        let q_full: u64 = (u1 * MG10_RECIPROCAL) + (u1 << 16u64) + u0 + (1u64 << 16u64);

        let q1: u64 = q_full >> 16u64;
        let q0: u64 = q_full & LIMB_MASK;
        let r: u64 = (SUB_BIAS + u0 - q1 * MG10_DIVISOR) & LIMB_MASK;

        let (q_corr, r_corr) = if q0 < r {
            (q1 - 1u64, (r + MG10_DIVISOR) & LIMB_MASK)
        } else {
            (q1, r)
        };

        if r_corr >= MG10_DIVISOR {
            q_corr + 1u64
        } else {
            q_corr
        }
    }
}

pub mod settlement {
    use crate::Authorization;
    use crate::mg10;

    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub struct RuintQuote {
        pub u1: u64,
        pub u0: u64,
        pub quotient: u64,
        pub total_debit: u64,
    }

    #[inline]
    pub fn build_quote(amount: u64, fee: u64) -> Option<RuintQuote> {
        let u1: u64 = fee % mg10::MG10_DIVISOR;
        let u0: u64 = amount & mg10::LIMB_MASK;
        let quotient: u64 = mg10::div_2x1_mg10(u1, u0);
        let total_debit: u64 = (amount >> 1u64) + quotient;
        Some(RuintQuote {
            u1,
            u0,
            quotient,
            total_debit,
        })
    }

    #[inline]
    pub fn verify_affordability(balance: u64, quote: RuintQuote) -> Option<Authorization> {
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
    let quote: settlement::RuintQuote = settlement::build_quote(amount, fee)?;
    settlement::verify_affordability(balance, quote)
}
