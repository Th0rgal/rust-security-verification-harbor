import SecurityChallenge
open SecurityChallenge

-- Intended policy (exact unbounded integers):
--   gross  = ceil((amount + fee) / 10000)
--   rebate = floor(gross / 10)
--   total  = amount + (gross - rebate)
-- Accept iff total <= balance; the reported debit equals total exactly.

def grossFeeNat (a f : UInt64) : Nat := (a.toNat + f.toNat + 9999) / 10000
def netDebitNat (a f : UInt64) : Nat := a.toNat + (grossFeeNat a f - grossFeeNat a f / 10)

def candidateSpec : AuthorizationSpec where
  accepts b a f := netDebitNat a f ≤ b.toNat
  output _b a f t := t.toNat = netDebitNat a f

theorem gross_eq (a f : UInt64) :
    (ceilDivBpsFolded (foldU64Sum a f)).toNat = (a.toNat + f.toNat + 9999) / 10000 := by
  have ha := a.toNat_lt
  have hf := f.toNat_lt
  simp only [ceilDivBpsFolded, foldU64Sum, bpsDenom, u64ModBpsQuot, u64ModBpsRem, bpsMaxRem]
  split <;> rename_i h
  · simp only [decide_eq_true_eq, UInt64.lt_iff_toNat_lt, UInt64.toNat_add] at h
    simp only [UInt64.toNat_add, UInt64.toNat_div, UInt64.toNat_mod, UInt64.reduceToNat]
    omega
  · simp only [decide_eq_true_eq, UInt64.lt_iff_toNat_lt, UInt64.toNat_add] at h
    split <;> rename_i h2
    · simp only [UInt64.lt_iff_toNat_lt, UInt64.toNat_add, UInt64.reduceToNat] at h2
      simp only [UInt64.toNat_add, UInt64.toNat_div, UInt64.toNat_mod, UInt64.reduceToNat]
      omega
    · simp only [UInt64.lt_iff_toNat_lt, UInt64.toNat_add, UInt64.reduceToNat] at h2
      simp only [UInt64.toNat_add, UInt64.toNat_div, UInt64.reduceToNat]
      omega

theorem net_eq (a f : UInt64) :
    (computeFeeBreakdown (ceilDivBpsFolded (foldU64Sum a f))).netFee.toNat
      = grossFeeNat a f - grossFeeNat a f / 10 := by
  have hg := gross_eq a f
  simp only [computeFeeBreakdown, tierRebateFloor, rebateDivisor, grossFeeNat]
  generalize ceilDivBpsFolded (foldU64Sum a f) = g at hg
  have hgl := g.toNat_lt
  rw [UInt64.toNat_sub_of_le]
  · simp only [UInt64.toNat_div, UInt64.reduceToNat]; omega
  · rw [UInt64.le_iff_toNat_le]; simp only [UInt64.toNat_div, UInt64.reduceToNat]; omega

theorem auth_iff (b a f t : UInt64) :
    challengeAuthorize b a f = some t ↔ (netDebitNat a f ≤ b.toNat ∧ t.toNat = netDebitNat a f) := by
  have hn := net_eq a f
  have ha := a.toNat_lt
  have hb := b.toNat_lt
  simp only [challengeAuthorize, buildSettlementQuote, verifyAffordability, netDebitNat]
  generalize computeFeeBreakdown (ceilDivBpsFolded (foldU64Sum a f)) = br at hn
  generalize grossFeeNat a f - grossFeeNat a f / 10 = n at hn
  have hnl := br.netFee.toNat_lt
  have hsub : (u64Max - a).toNat = 18446744073709551615 - a.toNat := by
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp [u64Max]; omega)]
    simp [u64Max]
  by_cases h1 : br.netFee ≤ u64Max - a
  · rw [if_pos h1]
    have h1' := UInt64.le_iff_toNat_le.mp h1
    rw [hsub] at h1'
    have hs : (a + br.netFee).toNat = a.toNat + br.netFee.toNat := by
      rw [UInt64.toNat_add]; omega
    simp only
    by_cases h2 : a + br.netFee ≤ b
    · rw [if_pos h2]
      have h2' := UInt64.le_iff_toNat_le.mp h2
      rw [hs] at h2'
      constructor
      · intro h; cases h; omega
      · intro ⟨_, h⟩; first | exact congrArg some (UInt64.eq_of_toNat_eq (by omega)) | exact congrArg some (UInt64.toNat_inj.mp (by omega))
    · rw [if_neg h2]
      have h2' : ¬ (a + br.netFee).toNat ≤ b.toNat := fun h => h2 (UInt64.le_iff_toNat_le.mpr h)
      rw [hs] at h2'
      simp only [reduceCtorEq, false_iff]; omega
  · rw [if_neg h1]
    have h1' : ¬ br.netFee.toNat ≤ (u64Max - a).toNat := fun h => h1 (UInt64.le_iff_toNat_le.mpr h)
    rw [hsub] at h1'
    simp only [reduceCtorEq, false_iff]; omega

theorem ofNat_toNat_small (n : Nat) (h : n < 2 ^ 64) : (UInt64.ofNat n).toNat = n := by
  first
  | (rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt h)
  | (simp only [UInt64.toNat_ofNat_of_lt' h])
  | (show n % 2 ^ 64 = n; exact Nat.mod_eq_of_lt h)
  | (simp; omega)

theorem spec_conforms : Conforms candidateSpec challengeAuthorize := by
  refine ⟨fun b a f => ?_, fun b a f t h => ((auth_iff b a f t).mp h).2⟩
  show (∃ t, challengeAuthorize b a f = some t) ↔ netDebitNat a f ≤ b.toNat
  constructor
  · rintro ⟨t, h⟩; exact ((auth_iff b a f t).mp h).1
  · intro h
    refine ⟨UInt64.ofNat (netDebitNat a f), (auth_iff _ _ _ _).mpr ⟨h, ?_⟩⟩
    have := b.toNat_lt
    exact ofNat_toNat_small _ (by omega)
