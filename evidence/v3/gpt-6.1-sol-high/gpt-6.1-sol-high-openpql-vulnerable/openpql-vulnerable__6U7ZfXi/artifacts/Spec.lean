import SecurityChallenge

-- All arithmetic below is exact natural-number arithmetic.
def policyDigit (word : Nat) (position : Nat) : Nat :=
  (word / (65536 ^ position)) % 65536

def policyClamp (a limit : Nat) : Nat :=
  if a < limit then a else limit

def policyIndex (amount fee : UInt64) : Nat :=
  let f0 := policyDigit fee.toNat 0
  let f1 := policyDigit fee.toNat 1
  let f2 := policyDigit fee.toNat 2
  let f3 := policyDigit fee.toNat 3
  let d0 := policyClamp (policyDigit amount.toNat 0) f0
  let d1 := policyClamp (policyDigit amount.toNat 1) f1
  let d2 := policyClamp (policyDigit amount.toNat 2) f2
  let d3 := policyClamp (policyDigit amount.toNat 3) f3
  d0 * ((f1 + 1) * ((f2 + 1) * (f3 + 1))) +
    d1 * ((f2 + 1) * (f3 + 1)) + d2 * (f3 + 1) + d3

def policyDebit (amount fee : UInt64) : Nat :=
  amount.toNat / 2 + policyIndex amount fee / 2

def candidateSpec : SecurityChallenge.AuthorizationSpec where
  accepts := fun balance amount fee => policyDebit amount fee ≤ balance.toNat
  output := fun balance amount fee totalDebit =>
    policyDebit amount fee ≤ balance.toNat ∧
    totalDebit.toNat = policyDebit amount fee
