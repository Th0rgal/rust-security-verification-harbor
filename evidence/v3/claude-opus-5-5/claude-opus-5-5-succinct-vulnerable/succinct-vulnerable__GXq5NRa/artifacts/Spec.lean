import SecurityChallenge
open SecurityChallenge

namespace CandidateSpecDefs

def byteAt (f : Nat) (i : Nat) : Nat := (f >>> (8 * i)) % 256

def nz (v : Nat) : Nat := if 0 < v then 1 else 0

def activeBytes (f : Nat) : Nat :=
  nz (byteAt f 0) + nz (byteAt f 1) + nz (byteAt f 2) + nz (byteAt f 3) +
  nz (byteAt f 4) + nz (byteAt f 5) + nz (byteAt f 6) + nz (byteAt f 7)

def byteSum (f : Nat) : Nat :=
  byteAt f 0 + byteAt f 1 + byteAt f 2 + byteAt f 3 +
  byteAt f 4 + byteAt f 5 + byteAt f 6 + byteAt f 7

def debit (amount fee : UInt64) : Nat :=
  amount.toNat / 2 + 256 * activeBytes fee.toNat + byteSum fee.toNat

end CandidateSpecDefs

open CandidateSpecDefs in
def candidateSpec : SecurityChallenge.AuthorizationSpec where
  accepts := fun balance amount fee => debit amount fee ≤ balance.toNat
  output := fun balance amount fee total =>
    debit amount fee ≤ balance.toNat ∧ total.toNat = debit amount fee
