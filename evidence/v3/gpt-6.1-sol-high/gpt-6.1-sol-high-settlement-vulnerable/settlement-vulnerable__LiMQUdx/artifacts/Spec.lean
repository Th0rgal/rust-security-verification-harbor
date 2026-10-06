import SecurityChallenge

-- Settlement arithmetic is unbounded, even though all API words are UInt64.
def settlementGrossFee (amount fee : UInt64) : Nat :=
  (amount.toNat + fee.toNat + 9999) / 10000

def settlementDebit (amount fee : UInt64) : Nat :=
  amount.toNat + (settlementGrossFee amount fee - settlementGrossFee amount fee / 10)

def candidateSpec : SecurityChallenge.AuthorizationSpec where
  accepts balance amount fee := settlementDebit amount fee ≤ balance.toNat
  output balance amount fee totalDebit :=
    settlementDebit amount fee ≤ balance.toNat ∧
    totalDebit.toNat = settlementDebit amount fee
