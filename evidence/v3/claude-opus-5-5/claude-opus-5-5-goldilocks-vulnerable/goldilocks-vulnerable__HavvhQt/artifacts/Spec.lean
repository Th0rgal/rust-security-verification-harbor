import SecurityChallenge
open SecurityChallenge

-- Exact policy debit: floor(amount/2) + (amount + fee * 2^64) mod P, with P = 2^64 - 2^32 + 1.
def policyDebit (amount fee : UInt64) : Nat :=
  amount.toNat / 2 + (amount.toNat + fee.toNat * 18446744073709551616) % 18446744069414584321

def candidateSpec : AuthorizationSpec where
  accepts := fun balance amount fee => policyDebit amount fee ≤ balance.toNat
  output := fun _balance amount fee totalDebit => totalDebit.toNat = policyDebit amount fee
