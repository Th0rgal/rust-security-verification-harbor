import SecurityChallenge
open SecurityChallenge

-- Unbounded mathematical pricing. Decomposition computes ceil((a+f)/10000)
-- without imposing any machine-word bound on a+f.
def grossNat (a f : Nat) : Nat :=
  a / 10000 + f / 10000 + (a % 10000 + f % 10000 + 9999) / 10000

def laneNat (x : Nat) : Nat :=
  if x % 256 = 0 then 0 else 256 + x % 256

def calldataNat (f : Nat) : Nat :=
  laneNat f + laneNat (f / 256) + laneNat (f / 65536)
  + laneNat (f / 16777216) + laneNat (f / 4294967296)
  + laneNat (f / 1099511627776) + laneNat (f / 281474976710656)
  + laneNat (f / 72057594037927936)

def blobNat (a f : Nat) : Nat :=
  ((f % 32771) * 65536 + a % 65536) / 32771

-- Canonical Montgomery reduction: inverse of 2^32 modulo p is 943718400.
-- Reducing before multiplying is mathematically equivalent to reducing
-- the packed transcript multiplied by this inverse.
def levyNat (a f : Nat) : Nat :=
  (((a % 4294967296) % 2013265921) * 943718400 + f % 2013265921) % 2013265921

def surchargeNat (a f : Nat) : Nat :=
  let g := grossNat a f
  (g - g / 10) + blobNat a f + calldataNat f + levyNat a f

def debitNat (a f : Nat) : Nat := a + surchargeNat a f

def candidateSpec : AuthorizationSpec where
  accepts b a f := debitNat a.toNat f.toNat ≤ b.toNat
  output b a f total := debitNat a.toNat f.toNat ≤ b.toNat ∧
    total.toNat = debitNat a.toNat f.toNat
