import SecurityChallenge
import Mathlib.Tactic
open SecurityChallenge

/- Exact settlement debit, without machine-word truncation. -/
def exactDebit (amount fee : UInt64) : Nat :=
  amount.toNat / 2 +
    (amount.toNat + fee.toNat * 18446744073709551616) % 18446744069414584321

def candidateSpec : AuthorizationSpec where
  accepts balance amount fee := exactDebit amount fee ≤ balance.toNat
  output balance amount fee totalDebit :=
    exactDebit amount fee ≤ balance.toNat ∧ totalDebit.toNat = exactDebit amount fee

private theorem high_correct (a h : UInt64) (hh : h.toNat < 4294967296) :
    (foldHighLimb a h).toNat =
      if a.toNat < h.toNat then a.toNat + 18446744069414584321 - h.toNat
      else a.toNat - h.toNat := by
  have ha := a.toNat_lt
  unfold foldHighLimb
  split <;> rename_i hc
  · simp only [UInt64.lt_iff_toNat_lt] at hc
    simp only [UInt64.toNat_add, UInt64.toNat_sub, goldilocksModulus,
      UInt64.toNat_ofNat]
    norm_num
    rw [if_pos hc]
    omega
  · have hn : ¬ a.toNat < h.toNat := hc
    rw [if_neg hn, UInt64.toNat_sub_of_le a h (by rw [UInt64.le_iff_toNat_le]; omega)]

private theorem mid_correct (a m : UInt64) (hm : m.toNat < 4294967296) :
    (foldMidLimb a m).toNat =
      if a.toNat + 4294967295 * m.toNat < 18446744073709551616
      then a.toNat + 4294967295 * m.toNat
      else a.toNat + 4294967295 * m.toNat - 18446744069414584321 := by
  have ha := a.toNat_lt
  have hp : 4294967295 * m.toNat < 18446744073709551616 := by omega
  unfold foldMidLimb
  simp only [UInt64.lt_iff_toNat_lt, UInt64.toNat_add, UInt64.toNat_mul,
    goldilocksEpsilon, UInt64.toNat_ofNat]
  norm_num
  split_ifs <;> simp only [UInt64.toNat_add, UInt64.toNat_mul,
    goldilocksEpsilon, UInt64.toNat_ofNat] <;> norm_num <;> omega

private theorem canonical_correct (a : UInt64) :
    (canonicalize a).toNat = a.toNat % 18446744069414584321 := by
  have ha := a.toNat_lt
  unfold canonicalize
  split <;> rename_i hc
  · rw [UInt64.toNat_sub_of_le _ _ hc]
    simp only [goldilocksModulus, UInt64.toNat_ofNat] at *
    norm_num at *
    change 18446744069414584321 ≤ a.toNat at hc
    omega
  · change ¬18446744069414584321 ≤ a.toNat at hc
    omega

theorem reduction_correct (a f : UInt64) :
    (reduce128 a f).toNat =
      (a.toNat + f.toNat * 18446744073709551616) % 18446744069414584321 := by
  let h := f / limbBase
  let m := f % limbBase
  let l := foldHighLimb a h
  have hf := f.toNat_lt
  have hh : h.toNat < 4294967296 := by
    dsimp [h, limbBase]
    simp only [UInt64.toNat_div, UInt64.toNat_ofNat]
    norm_num
    omega
  have hm : m.toNat < 4294967296 := by
    dsimp [m, limbBase]
    simp only [UInt64.toNat_mod, UInt64.toNat_ofNat]
    norm_num
    omega
  have decomp : f.toNat = m.toNat + 4294967296 * h.toNat := by
    dsimp [m, h, limbBase]
    simp only [UInt64.toNat_mod, UInt64.toNat_div, UInt64.toNat_ofNat]
    norm_num
    omega
  have hl := high_correct a h hh
  have identity :
      a.toNat + f.toNat * 18446744073709551616 + 18446744069414584321 =
      (l.toNat + 4294967295 * m.toNat) +
      (m.toNat + 4294967297 * h.toNat +
        (if a.toNat < h.toNat then 0 else 1)) * 18446744069414584321 := by
    change l.toNat = _ at hl
    split_ifs at hl ⊢ <;> omega
  have cong := congrArg (fun n : Nat => n % 18446744069414584321) identity
  simp only [Nat.add_mod_right, Nat.add_mul_mod_self_right] at cong
  unfold reduce128 splitTranscript
  change (canonicalize (foldMidLimb l m)).toNat = _
  rw [canonical_correct, mid_correct l m hm]
  rw [cong]
  split_ifs <;> omega

theorem authorization_correct (b a f t : UInt64) :
    challengeAuthorize b a f = some t ↔
      exactDebit a f ≤ b.toNat ∧ t.toNat = exactDebit a f := by
  have hb := b.toNat_lt
  have ha := a.toNat_lt
  have ht := t.toNat_lt
  have hs := (reduce128 a f).toNat_lt
  have hp : (a / principalDivisor).toNat = a.toNat / 2 := by
    simp [principalDivisor, UInt64.toNat_div, UInt64.toNat_ofNat]
  have hr := reduction_correct a f
  unfold challengeAuthorize buildQuote
  dsimp only
  split_ifs with hc
  all_goals try dsimp only
  · have hsum : (a / principalDivisor + reduce128 a f).toNat = exactDebit a f := by
      rw [UInt64.toNat_add, hp, hr]
      unfold exactDebit
      have hc' := hc
      rw [UInt64.le_iff_toNat_le, UInt64.toNat_sub_of_le] at hc'
      · change (reduce128 a f).toNat ≤ 18446744073709551615 - a.toNat / 2 at hc'
        rw [hr] at hc'
        omega
      · rw [UInt64.le_iff_toNat_le, hp]
        change a.toNat / 2 ≤ 18446744073709551615
        omega
    simp only [verifyAffordability]
    split <;> rename_i hbal
    · simp only [Option.some.injEq, ← UInt64.toNat_inj]
      rw [hsum]
      rw [UInt64.le_iff_toNat_le, hsum] at hbal
      omega
    · simp only [reduceCtorEq, false_iff, not_and]
      rw [UInt64.le_iff_toNat_le, hsum] at hbal
      omega
  · simp only [reduceCtorEq, false_iff, not_and]
    have hsub : (u64Max - a / principalDivisor).toNat =
        18446744073709551615 - a.toNat / 2 := by
      rw [UInt64.toNat_sub_of_le, hp]
      · rfl
      · rw [UInt64.le_iff_toNat_le, hp]
        change a.toNat / 2 ≤ 18446744073709551615
        omega
    rw [UInt64.le_iff_toNat_le, hsub, hr] at hc
    unfold exactDebit
    omega
