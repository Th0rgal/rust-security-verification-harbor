import SecurityChallenge
import Lean.Elab.Tactic.Omega

open SecurityChallenge

/-- Exact gross fee, rounded up, without word-sized intermediate arithmetic. -/
def policyGross (amount fee : UInt64) : Nat :=
  (amount.toNat + fee.toNat + 9999) / 10000

/-- Exact principal plus the gross fee less its ten-percent tier rebate. -/
def policyDebit (amount fee : UInt64) : Nat :=
  amount.toNat + (policyGross amount fee - policyGross amount fee / 10)

def candidateSpec : AuthorizationSpec where
  accepts balance amount fee := policyDebit amount fee ≤ balance.toNat
  output balance amount fee totalDebit :=
    policyDebit amount fee ≤ balance.toNat ∧ totalDebit.toNat = policyDebit amount fee

-- Word-level helper used only in the correctness proof, not in the policy.
def wordGross (amount fee : UInt64) : UInt64 :=
  let rawSum := amount + fee
  if rawSum < amount then
    let foldedRem := (rawSum % bpsDenom) + u64ModBpsRem
    u64ModBpsQuot + (rawSum / bpsDenom) + ((foldedRem + bpsMaxRem) / bpsDenom)
  else
    let biased := rawSum + bpsMaxRem
    if biased < rawSum then
      (rawSum / bpsDenom) + (((rawSum % bpsDenom) + bpsMaxRem) / bpsDenom)
    else
      biased / bpsDenom

theorem gross_correct (amount fee : UInt64) :
    (wordGross amount fee).toNat = policyGross amount fee := by
  have ha := amount.toNat_lt
  have hf := fee.toNat_lt
  unfold wordGross policyGross
  dsimp only
  split
  · rename_i h
    simp only [UInt64.lt_iff_toNat_lt, UInt64.toNat_add] at h
    simp only [UInt64.toNat_add, UInt64.toNat_div, UInt64.toNat_mod,
      bpsDenom, bpsMaxRem, u64ModBpsQuot, u64ModBpsRem]
    simp only [UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at *
    omega
  · rename_i h
    split
    · rename_i hb
      simp only [UInt64.lt_iff_toNat_lt, UInt64.toNat_add, bpsMaxRem,
        UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at h hb
      simp only [UInt64.toNat_add, UInt64.toNat_div, UInt64.toNat_mod,
        bpsDenom, bpsMaxRem, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
      omega
    · rename_i hb
      simp only [UInt64.lt_iff_toNat_lt, UInt64.toNat_add, bpsMaxRem,
        UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at h hb
      simp only [UInt64.toNat_add, UInt64.toNat_div,
        bpsDenom, bpsMaxRem, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
      omega

def wordNet (amount fee : UInt64) : UInt64 :=
  wordGross amount fee - wordGross amount fee / rebateDivisor

theorem net_correct (amount fee : UInt64) :
    (wordNet amount fee).toNat = policyGross amount fee - policyGross amount fee / 10 := by
  have h : wordGross amount fee / rebateDivisor ≤ wordGross amount fee := by
    rw [UInt64.le_iff_toNat_le, UInt64.toNat_div]
    exact Nat.div_le_self _ _
  unfold wordNet
  rw [UInt64.toNat_sub_of_le _ _ h, UInt64.toNat_div, gross_correct]
  rfl

theorem guard_correct (_balance amount fee : UInt64) :
    wordNet amount fee ≤ u64Max - amount ↔
      amount.toNat + (wordNet amount fee).toNat < 18446744073709551616 := by
  have ha := amount.toNat_lt
  have hamax : amount ≤ u64Max := by
    rw [UInt64.le_iff_toNat_le]
    change amount.toNat ≤ 18446744073709551615
    omega
  rw [UInt64.le_iff_toNat_le, UInt64.toNat_sub_of_le _ _ hamax]
  change (wordNet amount fee).toNat ≤ 18446744073709551615 - amount.toNat ↔ _
  omega

theorem debit_correct (amount fee : UInt64)
    (h : wordNet amount fee ≤ u64Max - amount) :
    (amount + wordNet amount fee).toNat = policyDebit amount fee := by
  have hg := (guard_correct 0 amount fee).mp h
  rw [UInt64.toNat_add, Nat.mod_eq_of_lt hg]
  unfold policyDebit
  rw [net_correct]
