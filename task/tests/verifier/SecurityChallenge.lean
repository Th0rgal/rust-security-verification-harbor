import Mathlib.Tactic

namespace SecurityChallenge

def u64Max : Nat := 18446744073709551615

def repairedAuthorize (balance amount fee : Nat) : Option Nat :=
  if amount + fee ≤ u64Max ∧ amount + fee ≤ balance then
    some (amount + fee)
  else
    none

end SecurityChallenge
