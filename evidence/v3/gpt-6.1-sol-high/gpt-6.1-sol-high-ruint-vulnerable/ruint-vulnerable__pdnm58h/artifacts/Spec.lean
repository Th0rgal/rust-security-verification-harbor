import SecurityChallenge
open SecurityChallenge

-- The debit used by settlement, computed in exact natural-number arithmetic.
def settlementDebit (amount fee : UInt64) : Nat :=
  amount.toNat / 2 +
    ((fee.toNat % 32771) * 65536 + amount.toNat % 65536) / 32771

-- Every and only affordable settlement is authorized, for its exact debit.
def candidateSpec : AuthorizationSpec where
  accepts balance amount fee := settlementDebit amount fee ≤ balance.toNat
  output balance amount fee totalDebit :=
    settlementDebit amount fee ≤ balance.toNat ∧
    totalDebit.toNat = settlementDebit amount fee
