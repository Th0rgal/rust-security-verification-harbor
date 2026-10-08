import SecurityChallenge
import Mathlib.Tactic
open SecurityChallenge

def component (n divisor : Nat) : Nat := (n / divisor) % 65536

def policyDigit (a b : Nat) : Nat := if a < b then a else b - 1

def policyIndex (amount fee : Nat) : Nat :=
  let b0 := component fee 1 + 1
  let b1 := component fee 65536 + 1
  let b2 := component fee 4294967296 + 1
  let b3 := component fee 281474976710656 + 1
  let d0 := policyDigit (component amount 1) b0
  let d1 := policyDigit (component amount 65536) b1
  let d2 := policyDigit (component amount 4294967296) b2
  let d3 := policyDigit (component amount 281474976710656) b3
  d0 * (b1 * (b2 * b3)) + d1 * (b2 * b3) + d2 * b3 + d3

def policyDebit (amount fee : Nat) : Nat :=
  amount / 2 + policyIndex amount fee / 2

def candidateSpec : AuthorizationSpec where
  accepts balance amount fee := policyDebit amount.toNat fee.toNat ≤ balance.toNat
  output balance amount fee totalDebit :=
    policyDebit amount.toNat fee.toNat ≤ balance.toNat ∧
    totalDebit.toNat = policyDebit amount.toNat fee.toNat
