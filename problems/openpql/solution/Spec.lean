import SecurityChallenge
open SecurityChallenge

def openpqlDebit (amount fee : UInt64) : Nat :=
  let f := fee.toNat
  let a := amount.toNat
  let b0 := (f % 65536) + 1
  let b1 := ((f / 65536) % 65536) + 1
  let b2 := ((f / 4294967296) % 65536) + 1
  let b3 := ((f / 281474976710656) % 65536) + 1
  let a0 := a % 65536
  let a1 := (a / 65536) % 65536
  let a2 := (a / 4294967296) % 65536
  let a3 := (a / 281474976710656) % 65536
  let d0 := if a0 < b0 then a0 else b0 - 1
  let d1 := if a1 < b1 then a1 else b1 - 1
  let d2 := if a2 < b2 then a2 else b2 - 1
  let d3 := if a3 < b3 then a3 else b3 - 1
  let o2 := b3
  let o1 := b2 * o2
  let o0 := b1 * o1
  let idx := d0 * o0 + d1 * o1 + d2 * o2 + d3
  (a / 2) + (idx / 2)

def candidateSpec : AuthorizationSpec where
  accepts := fun balance amount fee =>
    openpqlDebit amount fee ≤ balance.toNat
  output := fun _balance amount fee total =>
    total.toNat = openpqlDebit amount fee
