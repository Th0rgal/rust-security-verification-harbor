import SecurityChallenge
open SecurityChallenge

def goldilocksDebit (amount fee : UInt64) : Nat :=
  (amount.toNat / 2) + ((amount.toNat + 18446744073709551616 * fee.toNat) % 18446744069414584321)

def candidateSpec : AuthorizationSpec where
  accepts := fun balance amount fee =>
    goldilocksDebit amount fee ≤ balance.toNat
  output := fun _balance amount fee total =>
    total.toNat = goldilocksDebit amount fee
