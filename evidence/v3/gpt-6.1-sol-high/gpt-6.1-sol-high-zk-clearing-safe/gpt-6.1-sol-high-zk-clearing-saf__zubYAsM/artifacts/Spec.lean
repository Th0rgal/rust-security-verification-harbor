import SecurityChallenge

/- The parameter `fee` is a protocol word, not a standalone debit.  All
   active stage charges are assessed, then added WITHOUT reduction modulo
   2^64.  Thus a mathematical debit above the balance is always rejected.
   The following word reductions describe the protocol's limb encodings
   and canonical field-folding procedures, not the settlement addition. -/
namespace Policy
abbrev R : Nat := 18446744073709551616
abbrev P : Nat := 18446744069414584321
abbrev E : Nat := 4294967295
abbrev B : Nat := 4294967296
abbrev Q : Nat := 2013265921

def add (x y : Nat) := (x + y) % R
def sub (x y : Nat) := (R - y + x) % R
def mul (x y : Nat) := (x * y) % R
def left (x k : Nat) := (x <<< (k % 64)) % R
def right (x k : Nat) := x >>> (k % 64)

-- Carry-preserving ceiling assessment of a two-word notional.
def ceilCharge (a f d remBias carryQuot carryRem : Nat) : Nat :=
  let low := add a f
  if low < a then
    let folded := add (low % d) carryRem
    add (add carryQuot (low / d)) (add folded remBias / d)
  else
    let biased := add low remBias
    if biased < low then
      add (low / d) (add (low % d) remBias / d)
    else biased / d

def netFee (a f : Nat) : Nat :=
  let gross := ceilCharge a f 10000 9999 1844674407370955 1616
  sub gross (gross / 10)
def flashRetention (a f : Nat) : Nat :=
  let gross := ceilCharge a f 5000 4999 3689348814741910 1616
  sub gross (gross / 4)

-- Euclidean two-limb blob-slot assessment with reciprocal corrections.
def blob (a f : Nat) : Nat :=
  let h := f % 32771
  let l := a &&& 65535
  let full := add (add (add (mul h 65524) (left h 16)) l) (left 1 16)
  let q := right full 16
  let low := full &&& 65535
  let r := sub (add 3221225472 l) (mul q 32771) &&& 65535
  let qc := if low < r then sub q 1 else q
  let rc := if low < r then add r 32771 &&& 65535 else r
  if 32771 ≤ rc then add qc 1 else qc

-- Each nonzero calldata byte costs 256, plus its unsigned byte weight.
def lanes (f : Nat) : Nat :=
  let nz := (sub (f ||| 9259542123273814144) 72340172838076673 ||| f) &&& 9259542123273814144
  right (mul (right nz 7) 72340172838076673) 56
def weights (f : Nat) : Nat :=
  let pairs := add (f &&& 71777214294589695) (right f 8 &&& 71777214294589695)
  right (mul pairs 281479271743489) 48 &&& 65535
def calldata (f : Nat) : Nat := add (left (lanes f) 8) (weights f)

-- Canonical BabyBear Montgomery transcript levy.
def prover (a f : Nat) : Nat :=
  let x := add (a % B) (mul (f % Q) B)
  let t := mul (x % B) 2281701377 % B
  let u := mul Q t
  let hi := sub x u / B
  if x < u then sub (add Q hi) B else hi

-- Canonical Goldilocks residue of the 128-bit bridge challenge.
def bridge (a f : Nat) : Nat :=
  let h := right f 32
  let t0 := sub a h
  let t1 := if a < h then add t0 P else t0
  let prod := mul (f &&& E) E
  let t2 := add t1 prod
  let t3 := if t2 < t1 then add t2 E else t2
  if P ≤ t3 then sub t3 P else t3

def domain (f : Nat) : Nat :=
  let tag := f &&& 255
  if tag = 0 then 90 else tag

def base (a f : Nat) : Nat :=
  netFee a f + flashRetention a f + blob a f + calldata f + prover a f + domain f

def debit (a f : Nat) : Nat := a + (base a f + bridge a f)
end Policy

def candidateSpec : SecurityChallenge.AuthorizationSpec where
  accepts b a f := Policy.debit a.toNat f.toNat ≤ b.toNat
  output b a f totalDebit :=
    Policy.debit a.toNat f.toNat ≤ b.toNat ∧
    totalDebit.toNat = Policy.debit a.toNat f.toNat
