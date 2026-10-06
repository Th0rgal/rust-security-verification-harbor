//! Word-level concentrated-liquidity fee and rebate settlement authorization.

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Authorization {
    pub total_debit: u64,
}

const BPS_DENOM: u64 = 10_000;
const BPS_MAX_REM: u64 = 9_999;
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
    // amount + fee = BPS_DENOM * (qa + qf) + (ra + rf), with ra + rf <= 19_998,
    // so ceil((amount + fee) / BPS_DENOM) = qa + qf + ceil((ra + rf) / BPS_DENOM)
    // exactly, and no intermediate value can overflow u64.
    let quot_sum = (amount / BPS_DENOM) + (fee / BPS_DENOM);
    let rem_sum = (amount % BPS_DENOM) + (fee % BPS_DENOM);
    let gross_fee = quot_sum + ((rem_sum + BPS_MAX_REM) / BPS_DENOM);
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
    fn ceiling_bias_wrap_below_last_quotient() {
        // amount + fee = 2^64 - 9_999: ceil(/10_000) = 1_844_674_407_370_955.
        let fee = 18_446_744_073_709_541_617;
        let expected = 1_660_206_966_633_860;
        assert_eq!(authorize(expected, 0, fee).unwrap().total_debit, expected);
        assert_eq!(authorize(expected - 1, 0, fee), None);
    }

    #[test]
    fn total_debit_overflow_rejected() {
        assert_eq!(authorize(u64::MAX, u64::MAX, 1), None);
        assert_eq!(authorize(u64::MAX, u64::MAX, u64::MAX), None);
    }
}
