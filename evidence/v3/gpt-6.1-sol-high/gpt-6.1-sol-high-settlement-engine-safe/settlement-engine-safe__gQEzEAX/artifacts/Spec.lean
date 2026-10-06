import SecurityChallenge
import Lean.Elab.Tactic.Omega
open SecurityChallenge

/-- The gross fee is the ceiling of the exact combined basis / 10,000. -/
def policyGross (amount fee : UInt64) : Nat :=
  (amount.toNat + fee.toNat + 9999) / 10000

/-- Principal plus the gross fee less the floor ten-percent rebate. -/
def policyDebit (amount fee : UInt64) : Nat :=
  amount.toNat + (policyGross amount fee - policyGross amount fee / 10)

/-- Affordability is exact-integer affordability; output is the exact debit. -/
def candidateSpec : AuthorizationSpec := {
  accepts := fun balance amount fee => policyDebit amount fee ≤ balance.toNat
  output := fun _ amount fee totalDebit => totalDebit.toNat = policyDebit amount fee
}

-- Universal correctness evidence for the carry-aware word implementation.
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem gross_correct (a f : UInt64) :
  (ceilDivBpsU64 (addU64WithCarry a f)).toNat = policyGross a f := by
  have ha := a.toNat_lt
  have hf := f.toNat_lt
  unfold ceilDivBpsU64 addU64WithCarry
  dsimp only
  split
  · simp [UInt64.toNat_add, UInt64.toNat_div, UInt64.toNat_mod,
      bpsDenom, bpsMaxRem, u64ModBpsQuot, u64ModBpsRem,
      UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat, policyGross] at *
    omega
  · split
    · simp [UInt64.toNat_add, UInt64.toNat_div, UInt64.toNat_mod,
        bpsDenom, bpsMaxRem, UInt64.lt_iff_toNat_lt,
        UInt64.toNat_ofNat, policyGross] at *
      omega
    · simp [UInt64.toNat_add, UInt64.toNat_div,
        bpsDenom, bpsMaxRem, UInt64.lt_iff_toNat_lt,
        UInt64.toNat_ofNat, policyGross] at *
      omega

theorem net_correct (a f : UInt64) :
  (evaluateSettlementFee (addU64WithCarry a f)).netFee.toNat =
    policyGross a f - policyGross a f / 10 := by
  have hg := gross_correct a f
  have hr : computeTierRebate (ceilDivBpsU64 (addU64WithCarry a f)) ≤
      ceilDivBpsU64 (addU64WithCarry a f) := by
    simp [computeTierRebate, rebateDivisor, UInt64.le_iff_toNat_le,
      UInt64.toNat_div]
    omega
  simp only [evaluateSettlementFee, UInt64.toNat_sub_of_le _ _ hr]
  simp [computeTierRebate, rebateDivisor, UInt64.toNat_div, hg]

theorem authorize_correct (b a f t : UInt64) :
    challengeAuthorize b a f = some t ↔
    policyDebit a f ≤ b.toNat ∧ t.toNat = policyDebit a f := by
  have hb := b.toNat_lt
  have ha := a.toNat_lt
  have hn := net_correct a f
  have hm : (u64Max - a).toNat = 18446744073709551615 - a.toNat := by
    rw [UInt64.toNat_sub_of_le]
    · rfl
    · simp [u64Max, UInt64.le_iff_toNat_le]
      omega
  let n := (evaluateSettlementFee (addU64WithCarry a f)).netFee
  change n.toNat = policyGross a f - policyGross a f / 10 at hn
  have hexpr : challengeAuthorize b a f =
      if n ≤ u64Max - a then
        (if a + n ≤ b then some (a + n) else none)
      else none := by
    unfold challengeAuthorize quoteSettlementTicket assembleTicket
    dsimp only
    by_cases h : n ≤ u64Max - a
    · simp [n, h, commitTicket] at *
    · simp [n, h, commitTicket] at *
  rw [hexpr]
  by_cases h : n ≤ u64Max - a
  · rw [if_pos h]
    by_cases hbal : a + n ≤ b
    · rw [if_pos hbal]
      simp only [Option.some.injEq, ← UInt64.toNat_inj]
      simp [UInt64.le_iff_toNat_le, UInt64.toNat_add, hm] at h hbal ⊢
      unfold policyDebit
      omega
    · rw [if_neg hbal]
      simp only [reduceCtorEq, false_iff]
      simp [UInt64.le_iff_toNat_le, UInt64.toNat_add, hm] at h hbal
      unfold policyDebit
      omega
  · rw [if_neg h]
    simp only [reduceCtorEq, false_iff]
    simp [UInt64.le_iff_toNat_le, hm] at h
    unfold policyDebit
    omega

theorem conforms_correct : Conforms candidateSpec challengeAuthorize := by
  constructor
  · intro b a f
    change (∃ t, challengeAuthorize b a f = some t) ↔ policyDebit a f ≤ b.toNat
    constructor
    · rintro ⟨t, ht⟩
      exact ((authorize_correct b a f t).mp ht).1
    · intro h
      have hb := b.toNat_lt
      have ht : (UInt64.ofNat (policyDebit a f)).toNat = policyDebit a f := by
        simp only [UInt64.toNat_ofNat']
        apply Nat.mod_eq_of_lt
        omega
      exact ⟨UInt64.ofNat (policyDebit a f),
        (authorize_correct b a f _).mpr ⟨h, ht⟩⟩
  · intro b a f t ht
    exact ((authorize_correct b a f t).mp ht).2
