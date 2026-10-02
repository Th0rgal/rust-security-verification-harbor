//! Deliberately vulnerable training code. Do not deploy.

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Authorization {
    pub total_debit: u64,
}

/// Authorize a transfer before it is sent to a wider-integer settlement layer.
///
/// Policy: principal plus fee must not exceed the account balance.
pub fn authorize(balance: u64, amount: u64, fee: u64) -> Option<Authorization> {
    let total = amount.wrapping_add(fee);
    (total <= balance).then_some(Authorization { total_debit: total })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ordinary_payment() {
        assert_eq!(authorize(110, 100, 10).unwrap().total_debit, 110);
        assert_eq!(authorize(109, 100, 10), None);
    }
}
