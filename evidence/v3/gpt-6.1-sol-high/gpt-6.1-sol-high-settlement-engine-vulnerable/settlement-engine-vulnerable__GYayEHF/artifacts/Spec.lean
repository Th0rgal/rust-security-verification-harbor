import SecurityChallenge

open SecurityChallenge

/-- Exact mathematical debit: ceiling basis-point levy minus floor tier rebate. -/
def settlementDebit (amount fee : UInt64) : Nat :=
  let gross := (amount.toNat + fee.toNat + 9999) / 10000
  amount.toNat + (gross - gross / 10)

/-- Affordability and exact settlement output, without word-arithmetic wrapping. -/
def candidateSpec : AuthorizationSpec where
  accepts := fun balance amount fee => settlementDebit amount fee ≤ balance.toNat
  output := fun _balance amount fee totalDebit =>
    totalDebit.toNat = settlementDebit amount fee
