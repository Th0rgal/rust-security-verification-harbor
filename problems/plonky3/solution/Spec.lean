import SecurityChallenge
open SecurityChallenge

def plonky3Debit (amount fee : UInt64) : Nat :=
  amount.toNat + ((((amount.toNat % 4294967296) + (fee.toNat % 2013265921) * 4294967296) * 943718400) % 2013265921)

def candidateSpec : AuthorizationSpec where
  accepts := fun balance amount fee =>
    plonky3Debit amount fee ≤ balance.toNat
  output := fun _balance amount fee total =>
    total.toNat = plonky3Debit amount fee
