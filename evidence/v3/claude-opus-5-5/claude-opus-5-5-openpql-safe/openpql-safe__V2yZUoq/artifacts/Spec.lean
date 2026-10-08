import SecurityChallenge
import Mathlib
open SecurityChallenge

/-! Intended policy, stated in exact (unbounded) natural-number arithmetic. -/

def radB0 (f : Nat) : Nat := f % 65536 + 1
def radB1 (f : Nat) : Nat := f / 65536 % 65536 + 1
def radB2 (f : Nat) : Nat := f / 4294967296 % 65536 + 1
def radB3 (f : Nat) : Nat := f / 281474976710656 % 65536 + 1
def digA0 (a : Nat) : Nat := a % 65536
def digA1 (a : Nat) : Nat := a / 65536 % 65536
def digA2 (a : Nat) : Nat := a / 4294967296 % 65536
def digA3 (a : Nat) : Nat := a / 281474976710656 % 65536

/- clamp: min a (b - 1) for b at least 1 -/
def clampN (a b : Nat) : Nat := if a < b then a else b - 1

def encN (a f : Nat) : Nat :=
  clampN (digA0 a) (radB0 f) * (radB1 f * (radB2 f * radB3 f))
  + clampN (digA1 a) (radB1 f) * (radB2 f * radB3 f)
  + clampN (digA2 a) (radB2 f) * radB3 f
  + clampN (digA3 a) (radB3 f)

def debitN (a f : Nat) : Nat := a / 2 + encN a f / 2

def candidateSpec : AuthorizationSpec where
  accepts := fun b a f => debitN a.toNat f.toNat ≤ b.toNat
  output := fun _b a f t => t.toNat = debitN a.toNat f.toNat

/-! Proof that the model computes the policy without overflow. -/

theorem two64 : (2:Nat)^64 = 18446744073709551616 := by norm_num

theorem mul_toNat_of_lt (x y : UInt64) (h : x.toNat * y.toNat < 18446744073709551616) :
    (x * y).toNat = x.toNat * y.toNat := by
  rw [UInt64.toNat_mul, two64, Nat.mod_eq_of_lt h]

theorem add_toNat_of_lt (x y : UInt64) (h : x.toNat + y.toNat < 18446744073709551616) :
    (x + y).toNat = x.toNat + y.toNat := by
  rw [UInt64.toNat_add, two64, Nat.mod_eq_of_lt h]

theorem key_lt {d b x B : Nat} (hd : d < b) (hx : x < B) : d * B + x < b * B := by
  have : (d + 1) * B ≤ b * B := Nat.mul_le_mul_right B hd
  rw [Nat.add_mul, Nat.one_mul] at this
  omega

theorem enc_core (b0 b1 b2 b3 d0 d1 d2 d3 : UInt64)
    (hb0 : b0.toNat ≤ 65536) (hb1 : b1.toNat ≤ 65536) (hb2 : b2.toNat ≤ 65536)
    (hb3 : b3.toNat ≤ 65536)
    (hd0 : d0.toNat < b0.toNat) (hd1 : d1.toNat < b1.toNat) (hd2 : d2.toNat < b2.toNat)
    (hd3 : d3.toNat < b3.toNat) :
    (d0 * (b1 * (b2 * b3)) + d1 * (b2 * b3) + d2 * b3 + d3).toNat =
      d0.toNat * (b1.toNat * (b2.toNat * b3.toNat)) + d1.toNat * (b2.toNat * b3.toNat)
        + d2.toNat * b3.toNat + d3.toNat := by
  have h23 : b2.toNat * b3.toNat ≤ 65536 * 65536 := Nat.mul_le_mul hb2 hb3
  have p23 : (b2 * b3).toNat = b2.toNat * b3.toNat := mul_toNat_of_lt _ _ (by omega)
  have h123 : b1.toNat * (b2.toNat * b3.toNat) ≤ 65536 * (65536 * 65536) :=
    Nat.mul_le_mul hb1 h23
  have p123 : (b1 * (b2 * b3)).toNat = b1.toNat * (b2.toNat * b3.toNat) := by
    rw [mul_toNat_of_lt _ _ (by rw [p23]; omega), p23]
  have hall : b0.toNat * (b1.toNat * (b2.toNat * b3.toNat)) ≤ 65536 * (65536 * (65536 * 65536)) :=
    Nat.mul_le_mul hb0 h123
  have s3 := key_lt hd2 hd3
  have s2 := key_lt hd1 s3
  have s1 := key_lt hd0 s2
  have q0 : (d0 * (b1 * (b2 * b3))).toNat = d0.toNat * (b1.toNat * (b2.toNat * b3.toNat)) := by
    rw [mul_toNat_of_lt _ _ (by rw [p123]; omega), p123]
  have q1 : (d1 * (b2 * b3)).toNat = d1.toNat * (b2.toNat * b3.toNat) := by
    rw [mul_toNat_of_lt _ _ (by rw [p23]; omega), p23]
  have q2 : (d2 * b3).toNat = d2.toNat * b3.toNat := mul_toNat_of_lt _ _ (by omega)
  rw [add_toNat_of_lt, add_toNat_of_lt, add_toNat_of_lt, q0, q1, q2]
  · rw [q0, q1]; omega
  · rw [add_toNat_of_lt, q0, q1] <;> (try rw [q0, q1]) <;> omega
  · rw [add_toNat_of_lt, add_toNat_of_lt, q0, q1, q2] <;> (try rw [q0, q1]) <;>
      (try rw [add_toNat_of_lt, q0, q1, q2]) <;> (try rw [q0, q1]) <;> omega

theorem clamp_toNat (a b : UInt64) (hb : 1 ≤ b.toNat) :
    (clampDigit a b).toNat = clampN a.toNat b.toNat := by
  unfold clampDigit clampN
  by_cases h : a < b
  · have h' : a.toNat < b.toNat := UInt64.lt_iff_toNat_lt.mp h
    simp [h, h']
  · have h' : ¬ a.toNat < b.toNat := fun x => h (UInt64.lt_iff_toNat_lt.mpr x)
    simp only [h, h', if_false]
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simpa using hb))]
    simp

theorem encode_toNat (a f : UInt64) :
    (encodeMixedRadix a f).toNat = encN a.toNat f.toNat := by
  have hr : radixBase.toNat = 65536 := rfl
  have h16 : shift16.toNat = 65536 := rfl
  have h32 : shift32.toNat = 4294967296 := rfl
  have h48 : shift48.toNat = 281474976710656 := rfl
  have one : (1 : UInt64).toNat = 1 := rfl
  have B0 : ((f % radixBase) + 1).toNat = radB0 f.toNat := by
    rw [add_toNat_of_lt, UInt64.toNat_mod, hr, one] <;> simp only [UInt64.toNat_mod, hr, one, radB0] <;> omega
  have B1 : (((f / shift16) % radixBase) + 1).toNat = radB1 f.toNat := by
    rw [add_toNat_of_lt, UInt64.toNat_mod, UInt64.toNat_div, hr, h16, one] <;>
      simp only [UInt64.toNat_mod, UInt64.toNat_div, hr, h16, one, radB1] <;> omega
  have B2 : (((f / shift32) % radixBase) + 1).toNat = radB2 f.toNat := by
    rw [add_toNat_of_lt, UInt64.toNat_mod, UInt64.toNat_div, hr, h32, one] <;>
      simp only [UInt64.toNat_mod, UInt64.toNat_div, hr, h32, one, radB2] <;> omega
  have B3 : (((f / shift48) % radixBase) + 1).toNat = radB3 f.toNat := by
    rw [add_toNat_of_lt, UInt64.toNat_mod, UInt64.toNat_div, hr, h48, one] <;>
      simp only [UInt64.toNat_mod, UInt64.toNat_div, hr, h48, one, radB3] <;> omega
  have A0 : (a % radixBase).toNat = digA0 a.toNat := by
    simp only [UInt64.toNat_mod, hr, digA0]
  have A1 : ((a / shift16) % radixBase).toNat = digA1 a.toNat := by
    simp only [UInt64.toNat_mod, UInt64.toNat_div, hr, h16, digA1]
  have A2 : ((a / shift32) % radixBase).toNat = digA2 a.toNat := by
    simp only [UInt64.toNat_mod, UInt64.toNat_div, hr, h32, digA2]
  have A3 : ((a / shift48) % radixBase).toNat = digA3 a.toNat := by
    simp only [UInt64.toNat_mod, UInt64.toNat_div, hr, h48, digA3]
  have rb0 : 1 ≤ radB0 f.toNat ∧ radB0 f.toNat ≤ 65536 := by unfold radB0; omega
  have rb1 : 1 ≤ radB1 f.toNat ∧ radB1 f.toNat ≤ 65536 := by unfold radB1; omega
  have rb2 : 1 ≤ radB2 f.toNat ∧ radB2 f.toNat ≤ 65536 := by unfold radB2; omega
  have rb3 : 1 ≤ radB3 f.toNat ∧ radB3 f.toNat ≤ 65536 := by unfold radB3; omega
  have cl : ∀ x y : Nat, 1 ≤ y → clampN x y < y := by
    intro x y hy; unfold clampN; split <;> omega
  unfold encodeMixedRadix
  simp only []
  have D0 := clamp_toNat (a % radixBase) ((f % radixBase) + 1) (by rw [B0]; exact rb0.1)
  have D1 := clamp_toNat ((a / shift16) % radixBase) (((f / shift16) % radixBase) + 1) (by rw [B1]; exact rb1.1)
  have D2 := clamp_toNat ((a / shift32) % radixBase) (((f / shift32) % radixBase) + 1) (by rw [B2]; exact rb2.1)
  have D3 := clamp_toNat ((a / shift48) % radixBase) (((f / shift48) % radixBase) + 1) (by rw [B3]; exact rb3.1)
  rw [B0, A0] at D0
  rw [B1, A1] at D1
  rw [B2, A2] at D2
  rw [B3, A3] at D3
  rw [enc_core _ _ _ _ _ _ _ _ (by rw [B0]; exact rb0.2) (by rw [B1]; exact rb1.2)
    (by rw [B2]; exact rb2.2) (by rw [B3]; exact rb3.2)
    (by rw [D0, B0]; exact cl _ _ rb0.1) (by rw [D1, B1]; exact cl _ _ rb1.1)
    (by rw [D2, B2]; exact cl _ _ rb2.1) (by rw [D3, B3]; exact cl _ _ rb3.1)]
  rw [D0, D1, D2, D3, B1, B2, B3]
  rfl

def quoteDebit (a f : UInt64) : UInt64 :=
  a / halfDivisor + encodeMixedRadix a f / halfDivisor

theorem auth_eq (b a f : UInt64) :
    challengeAuthorize b a f = if quoteDebit a f ≤ b then some (quoteDebit a f) else none := rfl

theorem debit_toNat (a f : UInt64) : (quoteDebit a f).toNat = debitN a.toNat f.toNat := by
  have h2 : halfDivisor.toNat = 2 := rfl
  have ha := a.toNat_lt
  have he := (encodeMixedRadix a f).toNat_lt
  rw [two64] at ha he
  unfold quoteDebit debitN
  rw [add_toNat_of_lt, UInt64.toNat_div, UInt64.toNat_div, h2, encode_toNat]
  rw [UInt64.toNat_div, UInt64.toNat_div, h2]
  omega

theorem candidate_conforms : Conforms candidateSpec challengeAuthorize := by
  constructor
  · intro b a f
    show (∃ total, challengeAuthorize b a f = some total) ↔ debitN a.toNat f.toNat ≤ b.toNat
    rw [auth_eq]
    constructor
    · rintro ⟨t, ht⟩
      split at ht
      · rename_i h
        rw [← debit_toNat]; exact UInt64.le_iff_toNat_le.mp h
      · cases ht
    · intro h
      refine ⟨quoteDebit a f, ?_⟩
      rw [if_pos (UInt64.le_iff_toNat_le.mpr (by rw [debit_toNat]; exact h))]
  · intro b a f t ht
    show t.toNat = debitN a.toNat f.toNat
    rw [auth_eq] at ht
    split at ht
    · cases ht; exact debit_toNat a f
    · cases ht
