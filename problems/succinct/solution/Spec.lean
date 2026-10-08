import SecurityChallenge

open SecurityChallenge

def isNz (b : Nat) : Nat := if 0 < b then 1 else 0

def succinctDebit (amount fee : UInt64) : Nat :=
  let f := fee.toNat
  let b0 := f % 256
  let b1 := (f / 256) % 256
  let b2 := (f / 65536) % 256
  let b3 := (f / 16777216) % 256
  let b4 := (f / 4294967296) % 256
  let b5 := (f / 1099511627776) % 256
  let b6 := (f / 281474976710656) % 256
  let b7 := (f / 72057594037927936) % 256
  let active := isNz b0 + isNz b1 + isNz b2 + isNz b3 + isNz b4 + isNz b5 + isNz b6 + isNz b7
  let bsum := b0 + b1 + b2 + b3 + b4 + b5 + b6 + b7
  (amount.toNat / 2) + active * 256 + bsum

def candidateSpec : AuthorizationSpec where
  accepts := fun balance amount fee =>
    succinctDebit amount fee ≤ balance.toNat
  output := fun _balance amount fee total =>
    total.toNat = succinctDebit amount fee
