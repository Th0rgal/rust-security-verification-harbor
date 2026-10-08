import SecurityChallenge
open SecurityChallenge

def settlementDebit (amount fee : UInt64) : Nat :=
  amount.toNat / 2 + ((fee.toNat % 32771) * 65536 + amount.toNat % 65536) / 32771

def candidateSpec : AuthorizationSpec where
  accepts balance amount fee := settlementDebit amount fee ≤ balance.toNat
  output _ amount fee totalDebit := totalDebit.toNat = settlementDebit amount fee
