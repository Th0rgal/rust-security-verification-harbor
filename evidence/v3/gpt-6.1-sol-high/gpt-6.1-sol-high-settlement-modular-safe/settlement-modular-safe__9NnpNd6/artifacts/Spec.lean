import SecurityChallenge
import Lean.Elab.Tactic.Omega

-- Settlement arithmetic is unbounded; no intermediate sum is reduced modulo 2^64.
def grossFee (amount fee : UInt64) : Nat :=
  (amount.toNat + fee.toNat + 9999) / 10000

def settlementDebit (amount fee : UInt64) : Nat :=
  amount.toNat + (grossFee amount fee - grossFee amount fee / 10)

def candidateSpec : SecurityChallenge.AuthorizationSpec where
  accepts balance amount fee := settlementDebit amount fee ≤ balance.toNat
  output balance amount fee totalDebit :=
    settlementDebit amount fee ≤ balance.toNat ∧
    totalDebit.toNat = settlementDebit amount fee

open SecurityChallenge
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem ceil_correct (a f : UInt64) :
    (ceilDivBpsFolded (foldU64Sum a f)).toNat = grossFee a f := by
  have ha := a.toNat_lt
  have hf := f.toNat_lt
  unfold ceilDivBpsFolded foldU64Sum grossFee
  simp only [Bool.decide_eq_true, Bool.decide_eq_false]
  split
  · simp only [UInt64.toNat_add, UInt64.toNat_div, UInt64.toNat_mod,
      UInt64.toNat_ofNat, bpsDenom, bpsMaxRem, u64ModBpsQuot, u64ModBpsRem,
      UInt64.lt_iff_toNat_lt] at *
    simp only [Nat.reducePow, Nat.reduceMod, decide_eq_true_eq, decide_eq_false_iff_not] at *
    simp (disch := omega) only [Nat.mod_eq_of_lt]
    all_goals omega
  · split
    · simp only [UInt64.toNat_add, UInt64.toNat_div, UInt64.toNat_mod,
        UInt64.toNat_ofNat, bpsDenom, bpsMaxRem, u64ModBpsQuot, u64ModBpsRem,
        UInt64.lt_iff_toNat_lt] at *
      simp only [Nat.reducePow, Nat.reduceMod, decide_eq_true_eq, decide_eq_false_iff_not] at *
      simp (disch := omega) only [Nat.mod_eq_of_lt]
      all_goals omega
    · simp only [UInt64.toNat_add, UInt64.toNat_div, UInt64.toNat_mod,
        UInt64.toNat_ofNat, bpsDenom, bpsMaxRem, u64ModBpsQuot, u64ModBpsRem,
        UInt64.lt_iff_toNat_lt] at *
      simp only [Nat.reducePow, Nat.reduceMod, decide_eq_true_eq, decide_eq_false_iff_not] at *
      simp (disch := omega) only [Nat.mod_eq_of_lt]
      all_goals omega

theorem net_correct (a f : UInt64) :
    (computeFeeBreakdown (ceilDivBpsFolded (foldU64Sum a f))).netFee.toNat =
      grossFee a f - grossFee a f / 10 := by
  have h (g : UInt64) : tierRebateFloor g ≤ g := by
    simp only [tierRebateFloor, rebateDivisor, UInt64.le_iff_toNat_le,
      UInt64.toNat_div, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    omega
  change (ceilDivBpsFolded (foldU64Sum a f) -
    tierRebateFloor (ceilDivBpsFolded (foldU64Sum a f))).toNat = _
  rw [UInt64.toNat_sub_of_le _ _ (h _)]
  simp only [tierRebateFloor, rebateDivisor, UInt64.toNat_div,
    UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, ceil_correct]

theorem authorize_iff (b a f t : UInt64) :
    challengeAuthorize b a f = some t ↔
      settlementDebit a f ≤ b.toNat ∧ t.toNat = settlementDebit a f := by
  have ha := a.toNat_lt
  have hb := b.toNat_lt
  have hn := net_correct a f
  have hmax : a ≤ u64Max := by
    simp only [u64Max, UInt64.le_iff_toNat_le, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    omega
  have hsub : (u64Max - a).toNat = 18446744073709551615 - a.toNat := by
    rw [UInt64.toNat_sub_of_le _ _ hmax]
    rfl
  unfold challengeAuthorize buildSettlementQuote
  dsimp only
  by_cases hfit : (computeFeeBreakdown (ceilDivBpsFolded (foldU64Sum a f))).netFee ≤ u64Max - a
  · simp only [hfit, if_pos, Option.some.injEq]
    have hfitNat := UInt64.le_iff_toNat_le.mp hfit
    rw [hsub, hn] at hfitNat
    have htotal : (a + (computeFeeBreakdown (ceilDivBpsFolded (foldU64Sum a f))).netFee).toNat =
        settlementDebit a f := by
      simp only [UInt64.toNat_add, hn, settlementDebit]
      apply Nat.mod_eq_of_lt
      omega
    simp only [verifyAffordability]
    split
    · rename_i haff
      have haffNat := UInt64.le_iff_toNat_le.mp haff
      rw [htotal] at haffNat
      simp only [Option.some.injEq, ← UInt64.toNat_inj, htotal]
      exact ⟨fun h => ⟨haffNat, h.symm⟩, fun h => h.2.symm⟩
    · rename_i haff
      have haffNat : ¬ settlementDebit a f ≤ b.toNat := by
        simpa only [UInt64.le_iff_toNat_le, htotal] using haff
      try simp only [reduceCtorEq, false_iff]
      exact fun h => haffNat h.1
  · simp only [hfit, if_neg]
    have hfitNat : ¬ (grossFee a f - grossFee a f / 10) ≤ 18446744073709551615 - a.toNat := by
      simpa only [UInt64.le_iff_toNat_le, hsub, hn] using hfit
    have hnot : ¬ settlementDebit a f ≤ b.toNat := by
      unfold settlementDebit
      omega
    simp [hnot]
