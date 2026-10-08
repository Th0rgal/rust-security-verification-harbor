import SecurityChallenge

-- Exact settlement debit, without word-size truncation.
def policyDebit (amount fee : UInt64) : Nat :=
  amount.toNat / 2 +
    (amount.toNat + fee.toNat * 18446744073709551616) % 18446744069414584321

def candidateSpec : SecurityChallenge.AuthorizationSpec where
  accepts := fun balance amount fee =>
    policyDebit amount fee ≤ balance.toNat
  output := fun balance amount fee totalDebit =>
    policyDebit amount fee ≤ balance.toNat ∧
    totalDebit.toNat = policyDebit amount fee
