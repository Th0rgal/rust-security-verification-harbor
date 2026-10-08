by
  change Conforms candidateSpec challengeAuthorize
  have hbase : limbBase.toNat = 4294967296 := rfl
  have hfee_mul : feeRateMulValue.toNat = 1000000 := rfl
  have hdiv : principalDivisor.toNat = 2 := rfl
  have hmax : u64Max.toNat = 18446744073709551615 := rfl
  have hpow : (2 : Nat) ^ 64 = 18446744073709551616 := rfl
  have h0 : (0 : UInt64).toNat = 0 := rfl
  have h1 : (1 : UInt64).toNat = 1 := rfl
  have h_step : ∀ (rem word : UInt64),
      rem.toNat < 1000000 → word.toNat < 4294967296 →
      (divStep rem word).quot.toNat = (4294967296 * rem.toNat + word.toNat) / 1000000 ∧
      (divStep rem word).rem.toNat = (4294967296 * rem.toNat + word.toNat) % 1000000 ∧
      (divStep rem word).quot.toNat < 4294967296 ∧
      (divStep rem word).rem.toNat < 1000000 := by
    intro rem word hrem hword
    dsimp only [divStep]
    have hmul : (limbBase * rem).toNat = 4294967296 * rem.toNat := by
      simp only [UInt64.toNat_mul, hbase, hpow]; omega
    have hnum : (limbBase * rem + word).toNat = 4294967296 * rem.toNat + word.toNat := by
      simp only [UInt64.toNat_add, hmul, hpow]; omega
    rw [UInt64.toNat_div, UInt64.toNat_mod, hnum, hfee_mul]
    omega
  have h_chain : ∀ (amount fee : UInt64),
      let d := divWordChain (splitU128 amount fee)
      d.q0.toNat + d.q1.toNat * 4294967296 + d.q2.toNat * 18446744073709551616 + d.q3.toNat * 79228162514264337593543950336 =
        (amount.toNat + fee.toNat * 18446744073709551616) / 1000000 ∧
      d.rem.toNat = (amount.toNat + fee.toNat * 18446744073709551616) % 1000000 ∧
      d.q0.toNat < 4294967296 ∧ d.q1.toNat < 4294967296 ∧ d.q2.toNat < 4294967296 ∧ d.q3.toNat < 4294967296 ∧ d.rem.toNat < 1000000 := by
    intro amount fee
    have ha : amount.toNat < 18446744073709551616 := amount.toNat_lt_size
    have hf : fee.toNat < 18446744073709551616 := fee.toNat_lt_size
    dsimp only [divWordChain, splitU128]
    have hw0 : (amount % limbBase).toNat < 4294967296 := by rw [UInt64.toNat_mod, hbase]; omega
    have hw1 : (amount / limbBase).toNat < 4294967296 := by rw [UInt64.toNat_div, hbase]; omega
    have hw2 : (fee % limbBase).toNat < 4294967296 := by rw [UInt64.toNat_mod, hbase]; omega
    have hw3 : (fee / limbBase).toNat < 4294967296 := by rw [UInt64.toNat_div, hbase]; omega
    have h0_lt : (0 : UInt64).toNat < 1000000 := by decide
    have hs3 := h_step 0 (fee / limbBase) h0_lt hw3
    have hs2 := h_step (divStep 0 (fee / limbBase)).rem (fee % limbBase) hs3.2.2.2 hw2
    have hs1 := h_step (divStep (divStep 0 (fee / limbBase)).rem (fee % limbBase)).rem (amount / limbBase) hs2.2.2.2 hw1
    have hs0 := h_step (divStep (divStep (divStep 0 (fee / limbBase)).rem (fee % limbBase)).rem (amount / limbBase)).rem (amount % limbBase) hs1.2.2.2 hw0
    rw [UInt64.toNat_mod, hbase] at hs0
    rw [UInt64.toNat_div, hbase] at hs1
    rw [UInt64.toNat_mod, hbase] at hs2
    rw [UInt64.toNat_div, hbase] at hs3
    rw [h0] at hs3
    omega
  have h_round : ∀ (d : DivResult),
      d.q0.toNat < 4294967296 → d.q1.toNat < 4294967296 → d.q2.toNat < 4294967296 → d.q3.toNat < 4294967296 → d.rem.toNat < 1000000 →
      let r := roundUpQuotient d
      r.w0.toNat + r.w1.toNat * 4294967296 + r.w2.toNat * 18446744073709551616 + r.w3.toNat * 79228162514264337593543950336 =
        d.q0.toNat + d.q1.toNat * 4294967296 + d.q2.toNat * 18446744073709551616 + d.q3.toNat * 79228162514264337593543950336 +
        (if 0 < d.rem.toNat then 1 else 0) ∧
      r.w0.toNat < 4294967296 ∧ r.w1.toNat < 4294967296 := by
    intro d hq0 hq1 hq2 hq3 hrem
    dsimp only [roundUpQuotient]
    split <;> next hgt =>
      rw [UInt64.lt_iff_toNat_lt, h0] at hgt
      simp only [hgt, ↓reduceIte, UInt64.toNat_add, UInt64.toNat_div, UInt64.toNat_mod, hbase, h0, h1, hpow]
      omega
  have h_try : ∀ (w : U128Words),
      w.w0.toNat < 4294967296 → w.w1.toNat < 4294967296 →
      ((∃ g, tryIntoU64 w = some g) ↔ w.w2.toNat = 0 ∧ w.w3.toNat = 0) ∧
      (∀ g, tryIntoU64 w = some g → w.w2.toNat = 0 ∧ w.w3.toNat = 0 ∧ g.toNat = w.w0.toNat + w.w1.toNat * 4294967296) := by
    intro w hw0 hw1
    dsimp only [tryIntoU64]
    have hw2_iff : (w.w2 = 0) ↔ w.w2.toNat = 0 := ⟨fun h => by rw [h, h0], fun h => UInt64.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq h)⟩
    have hw3_iff : (w.w3 = 0) ↔ w.w3.toNat = 0 := ⟨fun h => by rw [h, h0], fun h => UInt64.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq h)⟩
    constructor
    · split
      · next h23 =>
        rw [hw2_iff, hw3_iff] at h23
        exact Iff.intro (fun _ => h23) (fun _ => ⟨_, rfl⟩)
      · next h23 =>
        rw [hw2_iff, hw3_iff] at h23
        exact Iff.intro (fun ⟨_, h⟩ => by cases h) (fun h => absurd h h23)
    · intro g hg
      split at hg
      · next h23 =>
        injection hg with hg'
        subst hg'
        rw [hw2_iff, hw3_iff] at h23
        refine ⟨h23.1, h23.2, ?_⟩
        simp only [UInt64.toNat_add, UInt64.toNat_mul, hbase, hpow]
        omega
      · next h23 =>
        cases hg
  have h_div_fee : ∀ (amount fee : UInt64),
      let grossNat := (amount.toNat + fee.toNat * 18446744073709551616 + 999999) / 1000000
      ((∃ g, divRoundUpFee amount fee = some g) ↔ grossNat < 18446744073709551616) ∧
      (∀ g, divRoundUpFee amount fee = some g → g.toNat = grossNat) := by
    intro amount fee
    dsimp only [divRoundUpFee]
    have ⟨hq_eq, hrem_eq, hq0, hq1, hq2, hq3, hrem⟩ := h_chain amount fee
    generalize divWordChain (splitU128 amount fee) = d at hq_eq hrem_eq hq0 hq1 hq2 hq3 hrem ⊢
    have ⟨hr_eq, hr0, hr1⟩ := h_round d hq0 hq1 hq2 hq3 hrem
    generalize roundUpQuotient d = r at hr_eq hr0 hr1 ⊢
    have ⟨htry_iff, htry_val⟩ := h_try r hr0 hr1
    constructor
    · rw [htry_iff]
      split at hr_eq <;> omega
    · intro g hg
      have ⟨hw2, hw3, hg_val⟩ := htry_val g hg
      split at hr_eq <;> omega
  have h_sub_max : ∀ (a : UInt64), (u64Max - a / principalDivisor).toNat = 18446744073709551615 - a.toNat / 2 := by
    intro a
    have ha : a.toNat < 18446744073709551616 := a.toNat_lt_size
    have h_le : a / principalDivisor ≤ u64Max := by
      rw [UInt64.le_iff_toNat_le, UInt64.toNat_div, hdiv, hmax]
      omega
    rw [UInt64.toNat_sub_of_le _ _ h_le, UInt64.toNat_div, hdiv, hmax]
  constructor
  · intro balance amount fee
    have hb : balance.toNat < 18446744073709551616 := balance.toNat_lt_size
    have ha : amount.toNat < 18446744073709551616 := amount.toNat_lt_size
    have ⟨hfee_iff, hfee_val⟩ := h_div_fee amount fee
    dsimp only [challengeAuthorize, buildQuote, verifyAffordability, candidateSpec, whirlpoolDebit]
    constructor
    · rintro ⟨total, hcall⟩
      cases h_df : divRoundUpFee amount fee with
      | none =>
        rw [h_df] at hcall
        cases hcall
      | some grossFee =>
        rw [h_df] at hcall
        dsimp only at hcall
        have hg_eq := hfee_val grossFee h_df
        split at hcall
        · next quote hquote =>
          split at hquote
          · next hfit =>
            injection hquote with hq
            subst hq
            split at hcall
            · next hbal =>
              dsimp at hbal
              rw [UInt64.le_iff_toNat_le, h_sub_max] at hfit
              rw [UInt64.le_iff_toNat_le, UInt64.toNat_add, UInt64.toNat_div, hdiv] at hbal
              omega
            · cases hcall
          · cases hquote
        · cases hcall
    · intro hbal_nat
      have h_gross_lt : (amount.toNat + fee.toNat * 18446744073709551616 + 999999) / 1000000 < 18446744073709551616 := by
        omega
      obtain ⟨grossFee, h_df⟩ := hfee_iff.mpr h_gross_lt
      have hg_eq := hfee_val grossFee h_df
      rw [h_df]
      dsimp only
      have hfit : grossFee ≤ u64Max - amount / principalDivisor := by
        rw [UInt64.le_iff_toNat_le, h_sub_max]
        omega
      have hbal_u64 : amount / principalDivisor + grossFee ≤ balance := by
        rw [UInt64.le_iff_toNat_le, UInt64.toNat_add, UInt64.toNat_div, hdiv]
        omega
      exact ⟨amount / principalDivisor + grossFee, by simp [hfit, hbal_u64]⟩
  · intro balance amount fee total hcall
    have hb : balance.toNat < 18446744073709551616 := balance.toNat_lt_size
    have ha : amount.toNat < 18446744073709551616 := amount.toNat_lt_size
    have ⟨_, hfee_val⟩ := h_div_fee amount fee
    dsimp only [challengeAuthorize, buildQuote, verifyAffordability] at hcall
    dsimp only [candidateSpec, whirlpoolDebit]
    cases h_df : divRoundUpFee amount fee with
    | none =>
      rw [h_df] at hcall
      cases hcall
    | some grossFee =>
      rw [h_df] at hcall
      dsimp only at hcall
      have hg_eq := hfee_val grossFee h_df
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
            rw [UInt64.le_iff_toNat_le, h_sub_max] at hfit
            rw [UInt64.toNat_add, UInt64.toNat_div, hdiv]
            omega
          · cases hcall
        · cases hquote
      · cases hcall
