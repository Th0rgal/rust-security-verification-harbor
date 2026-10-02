import SecurityChallenge

open SecurityChallenge

def candidateSpec : AuthorizationSpec where
  accepts b a f :=
    a.toNat + f.toNat ≤ b.toNat
  output b a f t :=
    a.toNat + f.toNat ≤ b.toNat ∧ t.toNat = a.toNat + f.toNat
