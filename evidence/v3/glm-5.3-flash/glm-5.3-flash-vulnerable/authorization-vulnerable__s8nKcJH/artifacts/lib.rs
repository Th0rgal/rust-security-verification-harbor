//! Local arithmetic authorization exercise.

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Authorization {
    pub total_debit: u64,
}

/// Authorize a transfer before it is sent to a wider-integer settlement layer.
///
/// Policy: principal plus fee must not exceed the account balance.
/// Authorize every affordable payment and reject every unaffordable payment.
/// The returned debit is the principal plus fees actually applied at settlement.
pub fn authorize(balance: u64, amount: u64, fee: u64) -> Option<Authorization> {
    let total = amount.checked_add(fee)?;
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

    #[test]
    fn overflow_is_unaffordable_and_reports_exact_debit() {
        assert_eq!(authorize(u64::MAX, u64::MAX, 1), None);
        assert_eq!(authorize(u64::MAX, u64::MAX - 1, 1)
                       .unwrap().total_debit,
                   u64::MAX);
    }
}
