import SecurityChallenge

-- Exact unbounded settlement arithmetic, including the ceiling fee and floor rebate.
def grossFeeNat (amount fee : UInt64) : Nat :=
  (amount.toNat + fee.toNat + 9999) / 10000

def settlementDebitNat (amount fee : UInt64) : Nat :=
  amount.toNat + (grossFeeNat amount fee - grossFeeNat amount fee / 10)

def candidateSpec : SecurityChallenge.AuthorizationSpec where
  accepts balance amount fee := settlementDebitNat amount fee ≤ balance.toNat
  output balance amount fee totalDebit :=
    settlementDebitNat amount fee ≤ balance.toNat ∧
    totalDebit.toNat = settlementDebitNat amount fee
