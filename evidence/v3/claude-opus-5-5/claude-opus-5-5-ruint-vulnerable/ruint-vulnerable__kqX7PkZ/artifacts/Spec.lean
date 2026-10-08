import SecurityChallenge
open SecurityChallenge

def intendedDebit (amount fee : UInt64) : Nat :=
  amount.toNat / 2 + ((fee.toNat % 32771) * 65536 + amount.toNat % 65536) / 32771

def candidateSpec : SecurityChallenge.AuthorizationSpec where
  accepts := fun balance amount fee => intendedDebit amount fee ≤ balance.toNat
  output := fun _balance amount fee total => total.toNat = intendedDebit amount fee
