import SecurityChallenge
open SecurityChallenge

-- Exact intended debit: floor(amount/2) + ceil((amount + fee*2^64)/1000000), computed in Nat.
def intendedTotal (amount fee : UInt64) : Nat :=
  amount.toNat / 2 + (amount.toNat + fee.toNat * 2 ^ 64 + 999999) / 1000000

def candidateSpec : SecurityChallenge.AuthorizationSpec where
  accepts := fun balance amount fee => intendedTotal amount fee ≤ balance.toNat
  output := fun _balance amount fee totalDebit => totalDebit.toNat = intendedTotal amount fee
