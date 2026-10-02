import SecurityChallenge

-- The exact contract is expressed in wider natural-number arithmetic.
-- Affordability is `amount + fee <= balance`; any accepted settlement debit
-- is exactly that mathematical total.
def candidateSpec : SecurityChallenge.AuthorizationSpec where
  accepts b a f := a.toNat + f.toNat ≤ b.toNat
  output b a f total :=
    a.toNat + f.toNat ≤ b.toNat ∧ total.toNat = a.toNat + f.toNat
