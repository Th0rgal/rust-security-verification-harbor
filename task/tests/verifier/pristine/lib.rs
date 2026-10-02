#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Authorization {
    pub total_debit: u64,
}

pub fn authorize(balance: u64, amount: u64, fee: u64) -> Option<Authorization> {
    let total = amount.wrapping_add(fee);
    (total <= balance).then_some(Authorization { total_debit: total })
}
