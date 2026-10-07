import SecurityChallenge
open SecurityChallenge

-- Exact gross fee: ceil((amount + fee * 2^64) / 1_000_000).
def grossFeeNat (a f : UInt64) : Nat :=
  (a.toNat + f.toNat * 18446744073709551616 + 999999) / 1000000

-- Exact total debit: floor(amount / 2) + gross fee.
def totalDebitNat (a f : UInt64) : Nat :=
  a.toNat / 2 + grossFeeNat a f

def candidateSpec : AuthorizationSpec where
  accepts b a f := totalDebitNat a f ≤ b.toNat
  output _ a f t := t.toNat = totalDebitNat a f

namespace CandidateAux

theorem lb : limbBase.toNat = 4294967296 := rfl

theorem toNat_add_lt {x y : UInt64} (h : x.toNat + y.toNat < 18446744073709551616) :
    (x + y).toNat = x.toNat + y.toNat := by
  rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt h

theorem toNat_mul_lt {x y : UInt64} (h : x.toNat * y.toNat < 18446744073709551616) :
    (x * y).toNat = x.toNat * y.toNat := by
  rw [UInt64.toNat_mul]; exact Nat.mod_eq_of_lt h

theorem divStep_spec (r w : UInt64) (hr : r.toNat < 1000000) (hw : w.toNat < 4294967296) :
    (divStep r w).quot.toNat = (4294967296 * r.toNat + w.toNat) / 1000000 ∧
    (divStep r w).rem.toNat = (4294967296 * r.toNat + w.toNat) % 1000000 := by
  have h1 : (4294967296 : UInt64).toNat = 4294967296 := rfl
  have h2 : (1000000 : UInt64).toNat = 1000000 := rfl
  have hlt1 : 4294967296 * r.toNat < 2^64 := by omega
  have hlt2 : 4294967296 * r.toNat + w.toNat < 2^64 := by omega
  simp only [divStep, limbBase, feeRateMulValue, UInt64.toNat_div, UInt64.toNat_mod,
    UInt64.toNat_add, UInt64.toNat_mul, h1, h2, Nat.mod_eq_of_lt hlt1, Nat.mod_eq_of_lt hlt2]
  exact ⟨trivial, trivial⟩

theorem chain_spec (w : U128Words) (h0 : w.w0.toNat < 4294967296) (h1 : w.w1.toNat < 4294967296)
    (h2 : w.w2.toNat < 4294967296) (h3 : w.w3.toNat < 4294967296) :
    (divWordChain w).q0.toNat < 4294967296 ∧ (divWordChain w).q1.toNat < 4294967296 ∧
    (divWordChain w).q2.toNat < 4294967296 ∧ (divWordChain w).q3.toNat < 4294967296 ∧
    (divWordChain w).rem.toNat < 1000000 ∧
    (79228162514264337593543950336 * (divWordChain w).q3.toNat
      + 18446744073709551616 * (divWordChain w).q2.toNat
      + 4294967296 * (divWordChain w).q1.toNat + (divWordChain w).q0.toNat) * 1000000
      + (divWordChain w).rem.toNat
      = 79228162514264337593543950336 * w.w3.toNat + 18446744073709551616 * w.w2.toNat
        + 4294967296 * w.w1.toNat + w.w0.toNat := by
  have z : (0 : UInt64).toNat = 0 := rfl
  have s3 := divStep_spec 0 w.w3 (by decide) h3
  have s2 := divStep_spec (divStep 0 w.w3).rem w.w2 (by rw [s3.2]; omega) h2
  have s1 := divStep_spec (divStep (divStep 0 w.w3).rem w.w2).rem w.w1 (by rw [s2.2]; omega) h1
  have s0 := divStep_spec (divStep (divStep (divStep 0 w.w3).rem w.w2).rem w.w1).rem w.w0
    (by rw [s1.2]; omega) h0
  obtain ⟨e3q, e3r⟩ := s3
  obtain ⟨e2q, e2r⟩ := s2
  obtain ⟨e1q, e1r⟩ := s1
  obtain ⟨e0q, e0r⟩ := s0
  simp only [divWordChain]
  omega

theorem roundUp_spec (D : DivResult) (h0 : D.q0.toNat < 4294967296) (h1 : D.q1.toNat < 4294967296)
    (h2 : D.q2.toNat < 4294967296) (h3 : D.q3.toNat < 4294967296) :
    (roundUpQuotient D).w0.toNat < 4294967296 ∧ (roundUpQuotient D).w1.toNat < 4294967296 ∧
    (roundUpQuotient D).w2.toNat < 4294967296 ∧
    (0 < D.rem.toNat →
      79228162514264337593543950336 * (roundUpQuotient D).w3.toNat
      + 18446744073709551616 * (roundUpQuotient D).w2.toNat
      + 4294967296 * (roundUpQuotient D).w1.toNat + (roundUpQuotient D).w0.toNat
      = 79228162514264337593543950336 * D.q3.toNat + 18446744073709551616 * D.q2.toNat
        + 4294967296 * D.q1.toNat + D.q0.toNat + 1) ∧
    (D.rem.toNat = 0 →
      79228162514264337593543950336 * (roundUpQuotient D).w3.toNat
      + 18446744073709551616 * (roundUpQuotient D).w2.toNat
      + 4294967296 * (roundUpQuotient D).w1.toNat + (roundUpQuotient D).w0.toNat
      = 79228162514264337593543950336 * D.q3.toNat + 18446744073709551616 * D.q2.toNat
        + 4294967296 * D.q1.toNat + D.q0.toNat) := by
  obtain ⟨q0, q1, q2, q3, rem⟩ := D
  dsimp only at h0 h1 h2 h3 ⊢
  simp only [roundUpQuotient]
  generalize hI : (if 0 < rem then (1 : UInt64) else 0) = inc
  have hi1 : 0 < rem.toNat → inc.toNat = 1 := by
    intro h
    have hp : (0 : UInt64) < rem := UInt64.lt_iff_toNat_lt.mpr (by show 0 < rem.toNat; exact h)
    rw [← hI, if_pos hp]; rfl
  have hi0 : rem.toNat = 0 → inc.toNat = 0 := by
    intro h
    have hn : ¬ (0 : UInt64) < rem := by
      rw [UInt64.lt_iff_toNat_lt]; show ¬ 0 < rem.toNat; omega
    rw [← hI, if_neg hn]; rfl
  have hi : inc.toNat ≤ 1 := by
    by_cases h : rem.toNat = 0
    · have := hi0 h; omega
    · have := hi1 (by omega); omega
  have e0 := toNat_add_lt (x := inc) (y := q0) (by omega)
  generalize inc + q0 = s0 at *
  have e1 := toNat_add_lt (x := s0 / limbBase) (y := q1) (by rw [UInt64.toNat_div, lb]; omega)
  rw [UInt64.toNat_div, lb] at e1
  generalize s0 / limbBase + q1 = s1 at *
  have e2 := toNat_add_lt (x := s1 / limbBase) (y := q2) (by rw [UInt64.toNat_div, lb]; omega)
  rw [UInt64.toNat_div, lb] at e2
  generalize s1 / limbBase + q2 = s2 at *
  have e3 := toNat_add_lt (x := s2 / limbBase) (y := q3) (by rw [UInt64.toNat_div, lb]; omega)
  rw [UInt64.toNat_div, lb] at e3
  generalize s2 / limbBase + q3 = s3 at *
  simp only [UInt64.toNat_div, UInt64.toNat_mod, lb] at *
  omega

theorem divRound_spec (a f : UInt64) :
    (∀ g, divRoundUpFee a f = some g → g.toNat = grossFeeNat a f) ∧
    (divRoundUpFee a f = none → 18446744073709551616 ≤ grossFeeNat a f) := by
  have hW0 : (splitU128 a f).w0.toNat = a.toNat % 4294967296 := by
    simp only [splitU128, UInt64.toNat_mod, lb]
  have hW1 : (splitU128 a f).w1.toNat = a.toNat / 4294967296 := by
    simp only [splitU128, UInt64.toNat_div, lb]
  have hW2 : (splitU128 a f).w2.toNat = f.toNat % 4294967296 := by
    simp only [splitU128, UInt64.toNat_mod, lb]
  have hW3 : (splitU128 a f).w3.toNat = f.toNat / 4294967296 := by
    simp only [splitU128, UInt64.toNat_div, lb]
  have ha := UInt64.toNat_lt a
  have hf := UInt64.toNat_lt f
  obtain ⟨a0, a1, a2, a3, ar, aeq⟩ := chain_spec (splitU128 a f) (by rw [hW0]; omega)
    (by rw [hW1]; omega) (by rw [hW2]; omega) (by rw [hW3]; omega)
  obtain ⟨b0, b1, b2, bpos, bzero⟩ := roundUp_spec (divWordChain (splitU128 a f)) a0 a1 a2 a3
  simp only [divRoundUpFee]
  generalize roundUpQuotient (divWordChain (splitU128 a f)) = R at *
  generalize divWordChain (splitU128 a f) = D at *
  generalize splitU128 a f = W at *
  have hR : 79228162514264337593543950336 * R.w3.toNat + 18446744073709551616 * R.w2.toNat
      + 4294967296 * R.w1.toNat + R.w0.toNat
      = (a.toNat + f.toNat * 18446744073709551616 + 999999) / 1000000 := by
    by_cases h : D.rem.toNat = 0
    · have := bzero h; omega
    · have := bpos (by omega); omega
  unfold grossFeeNat
  unfold tryIntoU64
  by_cases hc : R.w2 = 0 ∧ R.w3 = 0
  · rw [if_pos hc]
    have z2 : R.w2.toNat = 0 := by rw [hc.1]; rfl
    have z3 : R.w3.toNat = 0 := by rw [hc.2]; rfl
    have hm : (limbBase * R.w1).toNat = 4294967296 * R.w1.toNat := by
      rw [toNat_mul_lt (by rw [lb]; omega), lb]
    have hs : (limbBase * R.w1 + R.w0).toNat = 4294967296 * R.w1.toNat + R.w0.toNat := by
      rw [toNat_add_lt (by rw [hm]; omega), hm]
    refine ⟨fun g hg => ?_, fun h => by simp at h⟩
    injection hg with hg
    subst hg
    rw [hs]; omega
  · rw [if_neg hc]
    refine ⟨fun g hg => by simp at hg, fun _ => ?_⟩
    by_cases x : R.w2.toNat = 0
    · by_cases y : R.w3.toNat = 0
      · exact absurd ⟨UInt64.toNat_inj.mp x, UInt64.toNat_inj.mp y⟩ hc
      · omega
    · omega

theorem key (b a f : UInt64) :
    (∀ t, challengeAuthorize b a f = some t → t.toNat = totalDebitNat a f ∧ totalDebitNat a f ≤ b.toNat) ∧
    (challengeAuthorize b a f = none → ¬ totalDebitNat a f ≤ b.toNat) := by
  obtain ⟨hs, hn⟩ := divRound_spec a f
  have hP : (a / principalDivisor).toNat = a.toNat / 2 := by rw [UInt64.toNat_div]; rfl
  have hM : u64Max.toNat = 18446744073709551615 := rfl
  have hb := UInt64.toNat_lt b
  have ha := UInt64.toNat_lt a
  unfold totalDebitNat
  simp only [challengeAuthorize, buildQuote]
  cases h : divRoundUpFee a f with
  | none =>
    have := hn h
    refine ⟨fun t ht => by simp at ht, fun _ => by omega⟩
  | some g =>
    have hg := hs g h
    have hgt := UInt64.toNat_lt g
    have hsub : (u64Max - a / principalDivisor).toNat = 18446744073709551615 - a.toNat / 2 := by
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, hP, hM]; omega), hP, hM]
    dsimp only
    by_cases hc : g ≤ u64Max - a / principalDivisor
    · rw [if_pos hc]
      have hc' := UInt64.le_iff_toNat_le.mp hc
      rw [hsub] at hc'
      have hadd : (a / principalDivisor + g).toNat = a.toNat / 2 + g.toNat := by
        rw [toNat_add_lt (by rw [hP]; omega), hP]
      simp only [verifyAffordability]
      by_cases hv : a / principalDivisor + g ≤ b
      · rw [if_pos hv]
        have hv' := UInt64.le_iff_toNat_le.mp hv
        rw [hadd] at hv'
        refine ⟨fun t ht => ?_, fun ht => by simp at ht⟩
        injection ht with ht
        subst ht
        rw [hadd]; omega
      · rw [if_neg hv]
        have hv' : ¬ (a / principalDivisor + g).toNat ≤ b.toNat := fun x => hv (UInt64.le_iff_toNat_le.mpr x)
        rw [hadd] at hv'
        refine ⟨fun t ht => by simp at ht, fun _ => by omega⟩
    · rw [if_neg hc]
      have hc' : ¬ g.toNat ≤ (u64Max - a / principalDivisor).toNat := fun x => hc (UInt64.le_iff_toNat_le.mpr x)
      rw [hsub] at hc'
      refine ⟨fun t ht => by simp at ht, fun _ => by omega⟩

theorem conforms : Conforms candidateSpec challengeAuthorize := by
  refine ⟨fun b a f => ?_, fun b a f t ht => ((key b a f).1 t ht).1⟩
  constructor
  · rintro ⟨t, ht⟩
    exact ((key b a f).1 t ht).2
  · intro h
    cases hc : challengeAuthorize b a f with
    | none => exact absurd h ((key b a f).2 hc)
    | some t => exact ⟨t, rfl⟩

end CandidateAux
