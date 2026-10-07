by
  change Conforms candidateSpec challengeAuthorize
  have hp : babyBearP.toNat = 2013265921 := rfl
  have hmu : babyBearMu.toNat = 2281701377 := rfl
  have hbase : limbBase.toNat = 4294967296 := rfl
  have hmax : u64Max.toNat = 18446744073709551615 := rfl
  have h_pack : ∀ (amount fee : UInt64),
      (packTranscript amount fee).toNat =
        (amount.toNat % 4294967296) + (fee.toNat % 2013265921) * 4294967296 ∧
      (packTranscript amount fee).toNat < 4294967296 * 2013265921 := by
    intro amount fee
    dsimp only [packTranscript]
    simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_mod, hp, hbase]
    omega
  have h_quot : ∀ (x : UInt64),
      (montyQuotient x).toNat = (2281701377 * (x.toNat % 4294967296)) % 4294967296 ∧
      (montyQuotient x).toNat < 4294967296 := by
    intro x
    dsimp only [montyQuotient]
    simp only [UInt64.toNat_mul, UInt64.toNat_mod, hmu, hbase]
    omega
  have h_red : ∀ (x : UInt64),
      x.toNat < 4294967296 * 2013265921 →
      (montyReduce x).toNat = (x.toNat * 943718400) % 2013265921 := by
    intro x hx
    have ⟨ht_eq, ht_lt⟩ := h_quot x
    dsimp only [montyReduce]
    generalize montyQuotient x = t at ht_eq ht_lt ⊢
    have hu_eq : (babyBearP * t).toNat = 2013265921 * t.toNat := by
      simp only [UInt64.toNat_mul, hp]
      omega
    split
    · next hlt =>
      rw [UInt64.lt_iff_toNat_lt, hu_eq] at hlt
      have hdiff : (x - babyBearP * t).toNat = 18446744073709551616 + x.toNat - 2013265921 * t.toNat := by
        rw [UInt64.toNat_sub, hu_eq]
        omega
      have hhi : ((x - babyBearP * t) / limbBase).toNat =
          (18446744073709551616 + x.toNat - 2013265921 * t.toNat) / 4294967296 := by
        rw [UInt64.toNat_div, hdiff, hbase]
      have h_res : (babyBearP + (x - babyBearP * t) / limbBase - limbBase).toNat =
          2013265921 + (18446744073709551616 + x.toNat - 2013265921 * t.toNat) / 4294967296 - 4294967296 := by
        rw [UInt64.toNat_sub, UInt64.toNat_add, hp, hbase, hhi]
        omega
      rw [h_res]
      omega
    · next hlt =>
      rw [UInt64.lt_iff_toNat_lt, hu_eq] at hlt
      have hdiff : (x - babyBearP * t).toNat = x.toNat - 2013265921 * t.toNat := by
        rw [UInt64.toNat_sub, hu_eq]
        omega
      rw [UInt64.toNat_div, hdiff, hbase]
      omega
  have h_monty : ∀ (amount fee : UInt64),
      (montyReduce (packTranscript amount fee)).toNat =
        ((((amount.toNat % 4294967296) + (fee.toNat % 2013265921) * 4294967296) * 943718400) % 2013265921) := by
    intro amount fee
    have ⟨hx_eq, hx_lt⟩ := h_pack amount fee
    rw [h_red (packTranscript amount fee) hx_lt, hx_eq]
  have h_sub_max : ∀ (a : UInt64), (u64Max - a).toNat = 18446744073709551615 - a.toNat := by
    intro a
    have ha : a.toNat < 18446744073709551616 := a.toNat_lt_size
    have h_le : a ≤ u64Max := by
      rw [UInt64.le_iff_toNat_le, hmax]
      omega
    rw [UInt64.toNat_sub_of_le _ _ h_le, hmax]
  constructor
  · intro balance amount fee
    have hb : balance.toNat < 18446744073709551616 := balance.toNat_lt_size
    have ha : amount.toNat < 18446744073709551616 := amount.toNat_lt_size
    have hm := h_monty amount fee
    dsimp only [challengeAuthorize] at hm ⊢
    dsimp only [verifyAffordability, buildQuote, candidateSpec, plonky3Debit]
    generalize montyReduce (packTranscript amount fee) = M at hm ⊢
    constructor
    · rintro ⟨total, hcall⟩
      split at hcall
      · next quote hquote =>
        split at hquote
        · next hfit =>
          injection hquote with hq
          subst hq
          split at hcall
          · next hbal =>
            dsimp at hbal
            rw [UInt64.le_iff_toNat_le, h_sub_max, hm] at hfit
            rw [UInt64.le_iff_toNat_le, UInt64.toNat_add, hm] at hbal
            omega
          · cases hcall
        · cases hquote
      · cases hcall
    · intro hbal_nat
      have hfit : M ≤ u64Max - amount := by
        rw [UInt64.le_iff_toNat_le, h_sub_max, hm]
        omega
      have hbal_u64 : amount + M ≤ balance := by
        rw [UInt64.le_iff_toNat_le, UInt64.toNat_add, hm]
        omega
      exact ⟨amount + M, by simp [hfit, hbal_u64]⟩
  · intro balance amount fee total hcall
    have ha : amount.toNat < 18446744073709551616 := amount.toNat_lt_size
    have hm := h_monty amount fee
    dsimp only [challengeAuthorize] at hm hcall
    dsimp only [verifyAffordability, buildQuote] at hcall
    dsimp only [candidateSpec, plonky3Debit]
    generalize montyReduce (packTranscript amount fee) = M at hm hcall
    split at hcall
    · next quote hquote =>
      split at hquote
      · next hfit =>
        injection hquote with hq
        subst hq
        split at hcall
        · next hbal =>
          injection hcall with htot
          subst htot
          dsimp
          rw [UInt64.le_iff_toNat_le, h_sub_max, hm] at hfit
          rw [UInt64.toNat_add, hm]
          omega
        · cases hcall
      · cases hquote
    · cases hcall
