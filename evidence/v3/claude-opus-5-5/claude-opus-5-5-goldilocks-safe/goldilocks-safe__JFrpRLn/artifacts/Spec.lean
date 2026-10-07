import SecurityChallenge
open SecurityChallenge

namespace GoldilocksAudit

def policyTotal (amount fee : Nat) : Nat :=
  amount / 2 + (amount + fee * 18446744073709551616) % 18446744069414584321

end GoldilocksAudit

def candidateSpec : SecurityChallenge.AuthorizationSpec where
  accepts balance amount fee :=
    GoldilocksAudit.policyTotal amount.toNat fee.toNat ≤ balance.toNat
  output _balance amount fee totalDebit :=
    totalDebit.toNat = GoldilocksAudit.policyTotal amount.toNat fee.toNat

namespace GoldilocksAudit

theorem eP : goldilocksModulus.toNat = 18446744069414584321 := rfl
theorem eE : goldilocksEpsilon.toNat = 4294967295 := rfl
theorem eL : limbBase.toNat = 4294967296 := rfl
theorem eM : u64Max.toNat = 18446744073709551615 := rfl
theorem eD : principalDivisor.toNat = 2 := rfl

theorem lt64 (x : UInt64) : x.toNat < 18446744073709551616 := by
  have h := x.toNat_lt
  simp only [Nat.reducePow] at h
  exact h

theorem add_n (x y : UInt64) :
    (x + y).toNat = (x.toNat + y.toNat) % 18446744073709551616 := by
  simp only [UInt64.toNat_add, Nat.reducePow]

theorem sub_n (x y : UInt64) :
    (x - y).toNat = (18446744073709551616 - y.toNat + x.toNat) % 18446744073709551616 := by
  simp only [UInt64.toNat_sub, Nat.reducePow]

theorem mul_n (x y : UInt64) :
    (x * y).toNat = (x.toNat * y.toNat) % 18446744073709551616 := by
  simp only [UInt64.toNat_mul, Nat.reducePow]

theorem foldHigh_n (l h : UInt64) (hh : h.toNat < 4294967296) :
    (foldHighLimb l h).toNat =
      if l.toNat < h.toNat then l.toNat + 18446744069414584321 - h.toNat
      else l.toNat - h.toNat := by
  have hl := lt64 l
  dsimp only [foldHighLimb]
  by_cases c : l.toNat < h.toNat
  · rw [if_pos (UInt64.lt_iff_toNat_lt.mpr c), if_pos c, add_n, sub_n, eP]
    omega
  · rw [if_neg (fun h' => c (UInt64.lt_iff_toNat_lt.mp h')), if_neg c, sub_n]
    omega

theorem foldMid_n (x m : UInt64) (hm : m.toNat < 4294967296) :
    (foldMidLimb x m).toNat =
      if 18446744073709551616 ≤ x.toNat + 4294967295 * m.toNat then
        x.toNat + 4294967295 * m.toNat - 18446744073709551616 + 4294967295
      else x.toNat + 4294967295 * m.toNat := by
  have hx := lt64 x
  have hs : (x + goldilocksEpsilon * m).toNat =
      (x.toNat + 4294967295 * m.toNat) % 18446744073709551616 := by
    rw [add_n, mul_n, eE]
    omega
  dsimp only [foldMidLimb]
  by_cases c : x + goldilocksEpsilon * m < x
  · have c' := UInt64.lt_iff_toNat_lt.mp c
    rw [hs] at c'
    rw [if_pos c, add_n, hs, eE]
    by_cases d : 18446744073709551616 ≤ x.toNat + 4294967295 * m.toNat
    · rw [if_pos d]; omega
    · rw [if_neg d]; omega
  · have c' : ¬ (x + goldilocksEpsilon * m).toNat < x.toNat :=
      fun h' => c (UInt64.lt_iff_toNat_lt.mpr h')
    rw [hs] at c'
    rw [if_neg c, hs]
    by_cases d : 18446744073709551616 ≤ x.toNat + 4294967295 * m.toNat
    · rw [if_pos d]; omega
    · rw [if_neg d]; omega

theorem canon_n (x : UInt64) :
    (canonicalize x).toNat =
      if 18446744069414584321 ≤ x.toNat then x.toNat - 18446744069414584321
      else x.toNat := by
  dsimp only [canonicalize]
  by_cases c : goldilocksModulus ≤ x
  · have c' := UInt64.le_iff_toNat_le.mp c
    rw [eP] at c'
    rw [if_pos c, if_pos c', UInt64.toNat_sub_of_le _ _ c, eP]
  · have c' : ¬ 18446744069414584321 ≤ x.toNat :=
      fun h => c (UInt64.le_iff_toNat_le.mpr (by rw [eP]; exact h))
    rw [if_neg c, if_neg c']

theorem reduce_n (a f : UInt64) :
    (reduce128 a f).toNat =
      (a.toNat + f.toNat * 18446744073709551616) % 18446744069414584321 := by
  have ha := lt64 a
  have hf := lt64 f
  have hh : (f / limbBase).toNat = f.toNat / 4294967296 := by rw [UInt64.toNat_div, eL]
  have hm : (f % limbBase).toNat = f.toNat % 4294967296 := by rw [UInt64.toNat_mod, eL]
  have hh' : (f / limbBase).toNat < 4294967296 := by rw [hh]; omega
  have hm' : (f % limbBase).toNat < 4294967296 := by rw [hm]; omega
  have r1 := foldHigh_n a (f / limbBase) hh'
  have r2 := foldMid_n (foldHighLimb a (f / limbBase)) (f % limbBase) hm'
  have r3 := canon_n (foldMidLimb (foldHighLimb a (f / limbBase)) (f % limbBase))
  have r0 : reduce128 a f =
      canonicalize (foldMidLimb (foldHighLimb a (f / limbBase)) (f % limbBase)) := rfl
  rw [r0]
  rw [hh] at r1
  rw [hm] at r2
  generalize (canonicalize (foldMidLimb (foldHighLimb a (f / limbBase)) (f % limbBase))).toNat = Z at r3 ⊢
  generalize (foldMidLimb (foldHighLimb a (f / limbBase)) (f % limbBase)).toNat = Y at r2 r3
  generalize (foldHighLimb a (f / limbBase)).toNat = X at r1 r2
  generalize a.toNat = A at *
  generalize f.toNat = F at *
  split at r1 <;> split at r2 <;> split at r3 <;> omega

theorem div2_n (a : UInt64) : (a / principalDivisor).toNat = a.toNat / 2 := by
  rw [UInt64.toNat_div, eD]

theorem total_n (b a f : UInt64) (h : policyTotal a.toNat f.toNat ≤ b.toNat) :
    (a / principalDivisor + reduce128 a f).toNat = policyTotal a.toNat f.toNat := by
  have hb := lt64 b
  rw [add_n, div2_n, reduce_n]
  unfold policyTotal at h ⊢
  omega

theorem authorize_eq (b a f : UInt64) :
    challengeAuthorize b a f =
      if policyTotal a.toNat f.toNat ≤ b.toNat
      then some (a / principalDivisor + reduce128 a f) else none := by
  have hr := reduce_n a f
  have hb := lt64 b
  have ha := lt64 a
  have hd := div2_n a
  unfold challengeAuthorize buildQuote
  by_cases h1 : reduce128 a f ≤ u64Max - a / principalDivisor
  · have h1' := UInt64.le_iff_toNat_le.mp h1
    rw [sub_n, hd, hr, eM] at h1'
    simp only [h1, ↓reduceIte, verifyAffordability]
    by_cases h2 : a / principalDivisor + reduce128 a f ≤ b
    · have h2' := UInt64.le_iff_toNat_le.mp h2
      rw [add_n, hd, hr] at h2'
      rw [if_pos h2, if_pos (show policyTotal a.toNat f.toNat ≤ b.toNat by unfold policyTotal; omega)]
    · have h2' : ¬ (a / principalDivisor + reduce128 a f).toNat ≤ b.toNat :=
        fun h => h2 (UInt64.le_iff_toNat_le.mpr h)
      rw [add_n, hd, hr] at h2'
      rw [if_neg h2, if_neg (show ¬ policyTotal a.toNat f.toNat ≤ b.toNat by unfold policyTotal; omega)]
  · have h1' : ¬ (reduce128 a f).toNat ≤ (u64Max - a / principalDivisor).toNat :=
      fun h => h1 (UInt64.le_iff_toNat_le.mpr h)
    rw [sub_n, hd, hr, eM] at h1'
    simp only [h1, ↓reduceIte]
    rw [if_neg (show ¬ policyTotal a.toNat f.toNat ≤ b.toNat by unfold policyTotal; omega)]

end GoldilocksAudit
