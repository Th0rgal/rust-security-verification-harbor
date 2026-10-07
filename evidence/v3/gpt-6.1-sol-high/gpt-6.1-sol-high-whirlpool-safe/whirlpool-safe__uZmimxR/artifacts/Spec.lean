import SecurityChallenge

def settlementDebit (amount fee : UInt64) : Nat :=
  amount.toNat / 2 +
    (amount.toNat + fee.toNat * 18446744073709551616 + 999999) / 1000000

def candidateSpec : SecurityChallenge.AuthorizationSpec where
  accepts balance amount fee := settlementDebit amount fee ≤ balance.toNat
  output balance amount fee totalDebit :=
    settlementDebit amount fee ≤ balance.toNat ∧
    totalDebit.toNat = settlementDebit amount fee

open SecurityChallenge

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

theorem division_step_invariant (r w : UInt64)
    (hr : r.toNat < 1000000) (hw : w.toNat < 4294967296) :
    (divStep r w).quot.toNat < 4294967296 ∧
    (divStep r w).rem.toNat < 1000000 ∧
    4294967296 * r.toNat + w.toNat =
      1000000 * (divStep r w).quot.toNat + (divStep r w).rem.toNat := by
  have hn : 4294967296 * r.toNat + w.toNat < 18446744073709551616 := by omega
  simp [divStep, limbBase, feeRateMulValue, Nat.mod_eq_of_lt hn]
  omega

theorem rounding_invariant (d : DivResult)
    (h0 : d.q0.toNat < 4294967296) (h1 : d.q1.toNat < 4294967296)
    (h2 : d.q2.toNat < 4294967296) (h3 : d.q3.toNat < 4294967296) :
    let w := roundUpQuotient d
    w.w0.toNat < 4294967296 ∧ w.w1.toNat < 4294967296 ∧
    w.w0.toNat + 4294967296 * w.w1.toNat +
      18446744073709551616 * w.w2.toNat +
      79228162514264337593543950336 * w.w3.toNat =
    d.q0.toNat + 4294967296 * d.q1.toNat +
      18446744073709551616 * d.q2.toNat +
      79228162514264337593543950336 * d.q3.toNat +
      (if 0 < d.rem.toNat then 1 else 0) := by
  simp only [roundUpQuotient, limbBase, UInt64.lt_iff_toNat_lt]
  split <;> simp_all <;> omega

theorem chain_invariant (a f : UInt64) :
    let w := roundUpQuotient (divWordChain (splitU128 a f))
    w.w0.toNat < 4294967296 ∧ w.w1.toNat < 4294967296 ∧
    w.w0.toNat + 4294967296 * w.w1.toNat +
      18446744073709551616 * w.w2.toNat +
      79228162514264337593543950336 * w.w3.toNat =
      (a.toNat + f.toNat * 18446744073709551616 + 999999) / 1000000 := by
  have ha := a.toNat_lt
  have hf := f.toNat_lt
  have hw : (splitU128 a f).w0.toNat < 4294967296 ∧
      (splitU128 a f).w1.toNat < 4294967296 ∧
      (splitU128 a f).w2.toNat < 4294967296 ∧
      (splitU128 a f).w3.toNat < 4294967296 := by
    simp [splitU128, limbBase]
    omega
  let s3 := divStep 0 (splitU128 a f).w3
  let s2 := divStep s3.rem (splitU128 a f).w2
  let s1 := divStep s2.rem (splitU128 a f).w1
  let s0 := divStep s1.rem (splitU128 a f).w0
  have h3 := division_step_invariant 0 (splitU128 a f).w3 (by decide) hw.2.2.2
  have h2 := division_step_invariant s3.rem (splitU128 a f).w2 h3.2.1 hw.2.2.1
  have h1 := division_step_invariant s2.rem (splitU128 a f).w1 h2.2.1 hw.2.1
  have h0 := division_step_invariant s1.rem (splitU128 a f).w0 h1.2.1 hw.1
  have hr := rounding_invariant (divWordChain (splitU128 a f)) h0.1 h1.1 h2.1 h3.1
  refine ⟨hr.1, hr.2.1, ?_⟩
  rw [hr.2.2]
  change s0.quot.toNat + 4294967296 * s1.quot.toNat +
    18446744073709551616 * s2.quot.toNat +
    79228162514264337593543950336 * s3.quot.toNat +
    (if 0 < s0.rem.toNat then 1 else 0) = _
  have e3 := h3.2.2
  have e2 := h2.2.2
  have e1 := h1.2.2
  have e0 := h0.2.2
  change 4294967296 * s3.rem.toNat + (splitU128 a f).w2.toNat =
    1000000 * s2.quot.toNat + s2.rem.toNat at e2
  change 4294967296 * s2.rem.toNat + (splitU128 a f).w1.toNat =
    1000000 * s1.quot.toNat + s1.rem.toNat at e1
  change 4294967296 * s1.rem.toNat + (splitU128 a f).w0.toNat =
    1000000 * s0.quot.toNat + s0.rem.toNat at e0
  change 4294967296 * (0 : UInt64).toNat + (splitU128 a f).w3.toNat =
    1000000 * s3.quot.toNat + s3.rem.toNat at e3
  simp only [splitU128, limbBase, UInt64.toNat_mod, UInt64.toNat_div,
    UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.zero_mul, Nat.zero_add] at e0 e1 e2 e3
  have hrem : s0.rem.toNat < 1000000 := h0.2.1
  split <;> omega

theorem fee_correct (a f : UInt64) :
    (∀ g, divRoundUpFee a f = some g →
      g.toNat = (a.toNat + f.toNat * 18446744073709551616 + 999999) / 1000000) ∧
    (divRoundUpFee a f = none →
      18446744073709551616 ≤
      (a.toNat + f.toNat * 18446744073709551616 + 999999) / 1000000) := by
  have hc := chain_invariant a f
  let w := roundUpQuotient (divWordChain (splitU128 a f))
  change w.w0.toNat < 4294967296 ∧ w.w1.toNat < 4294967296 ∧
    w.w0.toNat + 4294967296 * w.w1.toNat +
      18446744073709551616 * w.w2.toNat +
      79228162514264337593543950336 * w.w3.toNat = _ at hc
  change (∀ g, tryIntoU64 w = some g → _) ∧ (tryIntoU64 w = none → _)
  unfold tryIntoU64
  by_cases hz : w.w2 = 0 ∧ w.w3 = 0
  · simp only [hz, ↓reduceIte, Option.some.injEq, reduceCtorEq, false_implies, and_true]
    intro g hg
    subst g
    have he := hc.2.2
    simp only [hz.1, hz.2, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
      Nat.mul_zero, Nat.add_zero] at he
    have hn : 4294967296 * w.w1.toNat + w.w0.toNat < 18446744073709551616 := by omega
    simp [limbBase, Nat.mod_eq_of_lt hn]
    omega
  · simp only [hz, ↓reduceIte, reduceCtorEq, false_implies, forall_const,
      true_and, true_implies]
    have hz' : ¬(w.w2.toNat = 0 ∧ w.w3.toNat = 0) := by
      simpa only [← UInt64.toNat_inj, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod] using hz
    omega


theorem authorize_some_iff (b a f t : UInt64) :
    challengeAuthorize b a f = some t ↔
    settlementDebit a f ≤ b.toNat ∧ t.toNat = settlementDebit a f := by
  have hc := fee_correct a f
  have hb := b.toNat_lt
  have ha := a.toNat_lt
  have ht := t.toNat_lt
  unfold challengeAuthorize buildQuote
  cases he : divRoundUpFee a f with
  | none =>
    have hn := hc.2 he
    simp only
    unfold settlementDebit
    simp only [reduceCtorEq, false_iff, not_and]
    omega
  | some g =>
    have hg := hc.1 g he
    have hp : a / principalDivisor ≤ u64Max := by
      simp [UInt64.le_iff_toNat_le, principalDivisor, u64Max]
      omega
    have hsub := UInt64.toNat_sub_of_le u64Max (a / principalDivisor) hp
    by_cases hs : g ≤ u64Max - a / principalDivisor
    · simp only [hs, ↓reduceIte]
      simp only [verifyAffordability]
      have hsn := hs
      simp only [UInt64.le_iff_toNat_le] at hsn
      rw [hsub] at hsn
      simp only [
        u64Max, principalDivisor, UInt64.toNat_div, UInt64.toNat_ofNat,
        Nat.reducePow, Nat.reduceMod] at hsn
      have hn : a.toNat / 2 + g.toNat < 18446744073709551616 := by omega
      simp only [UInt64.le_iff_toNat_le, UInt64.toNat_add, principalDivisor,
        UInt64.toNat_div, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
        Nat.mod_eq_of_lt hn, Option.some.injEq, ← UInt64.toNat_inj]
      unfold settlementDebit
      split <;> simp_all [← UInt64.toNat_inj, UInt64.toNat_add,
        UInt64.toNat_div, principalDivisor, Nat.mod_eq_of_lt hn] <;> omega
    · simp only [hs, ↓reduceIte, reduceCtorEq, false_iff, not_and]
      have hsn := hs
      simp only [UInt64.le_iff_toNat_le] at hsn
      rw [hsub] at hsn
      simp only [
        u64Max, principalDivisor, UInt64.toNat_div, UInt64.toNat_ofNat,
        Nat.reducePow, Nat.reduceMod] at hsn
      unfold settlementDebit
      omega

theorem authorize_correct (b a f : UInt64) :
    (∃ t, challengeAuthorize b a f = some t) ↔ settlementDebit a f ≤ b.toNat := by
  constructor
  · rintro ⟨t, ht⟩
    exact ((authorize_some_iff b a f t).mp ht).1
  · intro h
    have hn : settlementDebit a f < UInt64.size := by
      have hb := b.toNat_lt
      change settlementDebit a f < 18446744073709551616
      omega
    refine ⟨UInt64.ofNat (settlementDebit a f), ?_⟩
    apply (authorize_some_iff b a f _).mpr
    exact ⟨h, UInt64.toNat_ofNat_of_lt' hn⟩

theorem authorize_output (b a f t : UInt64)
    (h : challengeAuthorize b a f = some t) :
    settlementDebit a f ≤ b.toNat ∧ t.toNat = settlementDebit a f :=
  (authorize_some_iff b a f t).mp h
