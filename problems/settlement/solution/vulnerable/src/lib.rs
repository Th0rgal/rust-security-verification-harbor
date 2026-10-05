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
