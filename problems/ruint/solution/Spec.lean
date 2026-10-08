import SecurityChallenge

open SecurityChallenge

def ruintDebit (amount fee : UInt64) : Nat :=
  let u1 := fee.toNat % 32771
  let u0 := amount.toNat % 65536
  let dividend := u1 * 65536 + u0
  let q := dividend / 32771
  (amount.toNat / 2) + q

def candidateSpec : AuthorizationSpec where
  accepts := fun balance amount fee =>
    ruintDebit amount fee ≤ balance.toNat
  output := fun _balance amount fee total =>
    total.toNat = ruintDebit amount fee
