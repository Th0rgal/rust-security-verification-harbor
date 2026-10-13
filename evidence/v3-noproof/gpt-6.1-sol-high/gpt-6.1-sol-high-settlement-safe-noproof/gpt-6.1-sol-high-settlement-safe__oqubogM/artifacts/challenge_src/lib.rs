//! Word-level concentrated-liquidity fee and rebate settlement authorization.

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Authorization {
    pub total_debit: u64,
}

const BPS_DENOM: u64 = 10_000;
const BPS_MAX_REM: u64 = 9_999;
const U64_MOD_BPS_QUOT: u64 = 1_844_674_407_370_955;
const U64_MOD_BPS_REM: u64 = 1_616;
const REBATE_DIVISOR: u64 = 10;

/// Authorize a liquidity transfer in pure `u64` arithmetic before settlement.
///
/// Policy over exact unbounded integers (`balance`, `amount`, `fee`):
/// 1. The gross protocol fee is the combined basis `amount + fee` divided by
///    `BPS_DENOM` (`10_000`), rounded up (`ceil((amount + fee) / 10_000)`).
/// 2. The tier rebate is `gross_fee` divided by `REBATE_DIVISOR` (`10`),
///    rounded down (`floor(gross_fee / 10)`).
/// 3. The net settlement debit is `amount + (gross_fee - rebate)`.
///
/// Authorize every affordable transfer (`total_debit <= balance`) and return
/// the exact net settlement debit; reject every unaffordable transfer (`None`).
/// Target word constraint: production code must use `u64` only (no `u128`).
pub fn authorize(balance: u64, amount: u64, fee: u64) -> Option<Authorization> {
    let raw_sum = amount.wrapping_add(fee);
    let gross_fee = if raw_sum < amount {
        let folded_rem = (raw_sum % BPS_DENOM) + U64_MOD_BPS_REM;
        U64_MOD_BPS_QUOT + (raw_sum / BPS_DENOM) + ((folded_rem + BPS_MAX_REM) / BPS_DENOM)
    } else {
        let biased = raw_sum.wrapping_add(BPS_MAX_REM);
        if biased < raw_sum {
            (raw_sum / BPS_DENOM) + (((raw_sum % BPS_DENOM) + BPS_MAX_REM) / BPS_DENOM)
        } else {
            biased / BPS_DENOM
        }
    };
    let rebate = gross_fee / REBATE_DIVISOR;
    let net_fee = gross_fee - rebate;
    let total_debit = amount.checked_add(net_fee)?;
    (total_debit <= balance).then_some(Authorization { total_debit })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ordinary_settlement() {
        assert_eq!(authorize(100_012, 100_000, 25_000).unwrap().total_debit, 100_012);
        assert_eq!(authorize(100_011, 100_000, 25_000), None);
    }

    #[test]
    fn ceiling_rounding_and_rebate() {
        assert_eq!(authorize(2, 1, 0).unwrap().total_debit, 2);
        assert_eq!(authorize(9, 0, 99_991).unwrap().total_debit, 9);
        assert_eq!(authorize(8, 0, 99_991), None);
    }

    #[test]
    fn wide_basis_carry_folding() {
        let expected = 1_660_206_966_643_862;
        assert_eq!(authorize(expected, 10_000, u64::MAX).unwrap().total_debit, expected);
        assert_eq!(authorize(expected - 1, 10_000, u64::MAX), None);
    }

    #[test]
    fn ceiling_bias_wrap_at_u64_max() {
        let expected = 1_660_206_966_633_861;
        assert_eq!(authorize(expected, 0, u64::MAX).unwrap().total_debit, expected);
        assert_eq!(authorize(expected - 1, 0, u64::MAX), None);
    }

    #[test]
    fn total_debit_overflow_rejected() {
        assert_eq!(authorize(u64::MAX, u64::MAX, 1), None);
        assert_eq!(authorize(u64::MAX, u64::MAX, u64::MAX), None);
    }
}
