import SecurityChallenge
open SecurityChallenge

-- Exact settlement debit, computed without any word-size truncation.
def settlementDebit (amount fee : UInt64) : Nat :=
  amount.toNat / 2 +
    (amount.toNat + fee.toNat * 18446744073709551616 + 999999) / 1000000

def candidateSpec : AuthorizationSpec where
  accepts balance amount fee := settlementDebit amount fee ≤ balance.toNat
  output balance amount fee totalDebit :=
    settlementDebit amount fee ≤ balance.toNat ∧
    totalDebit.toNat = settlementDebit amount fee
