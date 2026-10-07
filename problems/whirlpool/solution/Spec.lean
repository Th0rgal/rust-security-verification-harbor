import SecurityChallenge
open SecurityChallenge

def whirlpoolDebit (amount fee : UInt64) : Nat :=
  (amount.toNat / 2) + ((amount.toNat + fee.toNat * 18446744073709551616 + 999999) / 1000000)

def candidateSpec : AuthorizationSpec where
  accepts := fun balance amount fee =>
    whirlpoolDebit amount fee ≤ balance.toNat
  output := fun _balance amount fee total =>
    total.toNat = whirlpoolDebit amount fee
