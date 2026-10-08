import SecurityChallenge
import Std.Tactic.BVDecide
open SecurityChallenge

def feeByte (fee : UInt64) (i : Nat) : Nat :=
  (fee.toNat / 2 ^ (8 * i)) % 256

def byteCharge (b : Nat) : Nat := (if b = 0 then 0 else 256) + b

def exactDebit (amount fee : UInt64) : Nat :=
  amount.toNat / 2 +
  byteCharge (feeByte fee 0) + byteCharge (feeByte fee 1) +
  byteCharge (feeByte fee 2) + byteCharge (feeByte fee 3) +
  byteCharge (feeByte fee 4) + byteCharge (feeByte fee 5) +
  byteCharge (feeByte fee 6) + byteCharge (feeByte fee 7)

def candidateSpec : AuthorizationSpec where
  accepts := fun balance amount fee => exactDebit amount fee ≤ balance.toNat
  output := fun balance amount fee totalDebit =>
    exactDebit amount fee ≤ balance.toNat ∧ totalDebit.toNat = exactDebit amount fee

set_option maxRecDepth 4096
set_option maxHeartbeats 0

def ub (f : UInt64) (i : UInt64) : UInt64 := (f >>> i) &&& 255
def nz (x : UInt64) : UInt64 := if x = 0 then 0 else 1

theorem count_correct (f : UInt64) : countNzBytes f =
  nz (ub f 0) + nz (ub f 8) + nz (ub f 16) + nz (ub f 24) +
  nz (ub f 32) + nz (ub f 40) + nz (ub f 48) + nz (ub f 56) := by
  unfold countNzBytes uNz8 l8Mask h8Mask ub nz
  bv_decide

theorem sum_correct (f : UInt64) : sumBytes f =
  ub f 0 + ub f 8 + ub f 16 + ub f 24 +
  ub f 32 + ub f 40 + ub f 48 + ub f 56 := by
  unfold sumBytes m16Mask l16Mask ub
  bv_decide

def wc (x : UInt64) : UInt64 := (if x = 0 then 0 else 256) + x

theorem shift_mul (x : UInt64) : x <<< 8 = x * 256 := by bv_decide

theorem half_shift (x : UInt64) : x >>> 1 = x / 2 := by bv_decide

theorem nz_scaled (x : UInt64) : nz x * 256 = (if x = 0 then 0 else 256) := by
  unfold nz
  split <;> decide +revert

theorem debit_word (a f : UInt64) :
  (a >>> 1) + (countNzBytes f <<< 8) + sumBytes f =
  a / 2 + wc (ub f 0) + wc (ub f 8) + wc (ub f 16) + wc (ub f 24) +
  wc (ub f 32) + wc (ub f 40) + wc (ub f 48) + wc (ub f 56) := by
  rw [count_correct, sum_correct]
  rw [half_shift, shift_mul]
  simp only [UInt64.add_mul, nz_scaled, wc]
  ac_rfl

theorem ub_as_mod (f : UInt64) :
  ub f 0 = (f / 1) % 256 ∧ ub f 8 = (f / 256) % 256 ∧
  ub f 16 = (f / 65536) % 256 ∧ ub f 24 = (f / 16777216) % 256 ∧
  ub f 32 = (f / 4294967296) % 256 ∧ ub f 40 = (f / 1099511627776) % 256 ∧
  ub f 48 = (f / 281474976710656) % 256 ∧ ub f 56 = (f / 72057594037927936) % 256 := by
  unfold ub
  bv_decide

 theorem byte_nat (f : UInt64) :
  (ub f 0).toNat = feeByte f 0 ∧ (ub f 8).toNat = feeByte f 1 ∧
  (ub f 16).toNat = feeByte f 2 ∧ (ub f 24).toNat = feeByte f 3 ∧
  (ub f 32).toNat = feeByte f 4 ∧ (ub f 40).toNat = feeByte f 5 ∧
  (ub f 48).toNat = feeByte f 6 ∧ (ub f 56).toNat = feeByte f 7 := by
  rcases ub_as_mod f with ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩
  simp [h0,h1,h2,h3,h4,h5,h6,h7,feeByte]

 theorem charge_nat (x : UInt64) (h : x.toNat < 256) :
  (wc x).toNat = byteCharge x.toNat := by
  by_cases hx : x = 0
  · simp [wc, byteCharge, hx]
  · have hn : x.toNat ≠ 0 := by
      intro hn
      apply hx
      apply UInt64.toNat.inj
      simpa using hn
    simp [wc, byteCharge, hx, hn, UInt64.toNat_add]
    omega

 theorem charge_bound (f : UInt64) (i : Nat) : byteCharge (feeByte f i) ≤ 511 := by
  have hb : feeByte f i < 256 := Nat.mod_lt _ (by decide)
  unfold byteCharge
  split <;> omega

 theorem debit_nat (a f : UInt64) :
  ((a >>> 1) + (countNzBytes f <<< 8) + sumBytes f).toNat = exactDebit a f := by
  rw [debit_word]
  rcases byte_nat f with ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩
  have hb (i : Nat) : feeByte f i < 256 := Nat.mod_lt _ (by decide)
  have c0 := charge_nat (ub f 0) (by rw [h0]; exact hb 0)
  have c1 := charge_nat (ub f 8) (by rw [h1]; exact hb 1)
  have c2 := charge_nat (ub f 16) (by rw [h2]; exact hb 2)
  have c3 := charge_nat (ub f 24) (by rw [h3]; exact hb 3)
  have c4 := charge_nat (ub f 32) (by rw [h4]; exact hb 4)
  have c5 := charge_nat (ub f 40) (by rw [h5]; exact hb 5)
  have c6 := charge_nat (ub f 48) (by rw [h6]; exact hb 6)
  have c7 := charge_nat (ub f 56) (by rw [h7]; exact hb 7)
  have b0 := charge_bound f 0
  have b1 := charge_bound f 1
  have b2 := charge_bound f 2
  have b3 := charge_bound f 3
  have b4 := charge_bound f 4
  have b5 := charge_bound f 5
  have b6 := charge_bound f 6
  have b7 := charge_bound f 7
  have ha := a.toNat_lt
  simp only [UInt64.toNat_add, UInt64.toNat_div, c0,c1,c2,c3,c4,c5,c6,c7,
    h0,h1,h2,h3,h4,h5,h6,h7]
  change ((((((((a.toNat / 2 + byteCharge (feeByte f 0)) % 2^64 +
    byteCharge (feeByte f 1)) % 2^64 + byteCharge (feeByte f 2)) % 2^64 +
    byteCharge (feeByte f 3)) % 2^64 + byteCharge (feeByte f 4)) % 2^64 +
    byteCharge (feeByte f 5)) % 2^64 + byteCharge (feeByte f 6)) % 2^64 +
    byteCharge (feeByte f 7)) % 2^64 = exactDebit a f
  unfold exactDebit
  omega

theorem universal_conformance : Conforms candidateSpec challengeAuthorize := by
  constructor
  · intro b a f
    have hd := debit_nat a f
    simp only [challengeAuthorize, buildQuote, verifyAffordability]
    change (∃ total, (if (a >>> 1) + (countNzBytes f <<< 8) + sumBytes f ≤ b then
      some ((a >>> 1) + (countNzBytes f <<< 8) + sumBytes f) else none) = some total) ↔
      exactDebit a f ≤ b.toNat
    rw [← hd, ← UInt64.le_iff_toNat_le]
    split <;> simp_all
  · intro b a f total h
    have hd := debit_nat a f
    simp only [challengeAuthorize, buildQuote, verifyAffordability] at h
    change (if (a >>> 1) + (countNzBytes f <<< 8) + sumBytes f ≤ b then
      some ((a >>> 1) + (countNzBytes f <<< 8) + sumBytes f) else none) = some total at h
    split at h
    · rename_i hb
      have ht := Option.some.inj h
      change exactDebit a f ≤ b.toNat ∧ total.toNat = exactDebit a f
      constructor
      · rw [← hd]
        exact UInt64.le_iff_toNat_le.mp hb
      · rw [← ht]
        exact hd
    · contradiction

