by
  change Conforms candidateSpec challengeAuthorize
  have hmod : goldilocksModulus.toNat = 18446744069414584321 := rfl
  have heps : goldilocksEpsilon.toNat = 4294967295 := rfl
  have hbase : limbBase.toNat = 4294967296 := rfl
  have hdiv : principalDivisor.toNat = 2 := rfl
  have hmax : u64Max.toNat = 18446744073709551615 := rfl
  have hpow : (2 : Nat) ^ 64 = 18446744073709551616 := rfl
  have h_high : ∀ (low high : UInt64),
      high.toNat < 4294967296 →
      ((foldHighLimb low high).toNat + high.toNat = 18446744069414584321 + low.toNat ∨
       (foldHighLimb low high).toNat + high.toNat = low.toNat) := by
    intro low high hhi
    have hlo : low.toNat < 18446744073709551616 := low.toNat_lt_size
    dsimp only [foldHighLimb]
    split
    · next hlt =>
      left
      rw [UInt64.lt_iff_toNat_lt] at hlt
      simp only [UInt64.toNat_add, UInt64.toNat_sub, hmod, hpow]
      omega
    · next hlt =>
      right
      rw [UInt64.lt_iff_toNat_lt] at hlt
      have hle : high ≤ low := by rw [UInt64.le_iff_toNat_le]; omega
      rw [UInt64.toNat_sub_of_le _ _ hle]
      omega
  have h_mid : ∀ (low2 mid : UInt64),
      mid.toNat < 4294967296 →
      ((foldMidLimb low2 mid).toNat = low2.toNat + 4294967295 * mid.toNat ∨
       (foldMidLimb low2 mid).toNat + 18446744069414584321 = low2.toNat + 4294967295 * mid.toNat) := by
    intro low2 mid hmid
    have hlo2 : low2.toNat < 18446744073709551616 := low2.toNat_lt_size
    dsimp only [foldMidLimb]
    have hprod : (goldilocksEpsilon * mid).toNat = 4294967295 * mid.toNat := by
      simp only [UInt64.toNat_mul, heps, hpow]
      omega
    split
    · next hlt =>
      right
      rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add, hprod, hpow] at hlt
      simp only [UInt64.toNat_add, hprod, heps, hpow]
      omega
    · next hlt =>
      left
      rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add, hprod, hpow] at hlt
      simp only [UInt64.toNat_add, hprod, hpow]
      omega
  have h_canon : ∀ (folded : UInt64),
      (canonicalize folded).toNat < 18446744069414584321 ∧
      ((canonicalize folded).toNat = folded.toNat ∨
       (canonicalize folded).toNat + 18446744069414584321 = folded.toNat) := by
    intro folded
    have hf : folded.toNat < 18446744073709551616 := folded.toNat_lt_size
    dsimp only [canonicalize]
    split
    · next hle =>
      rw [UInt64.toNat_sub_of_le _ _ hle, hmod]
      rw [UInt64.le_iff_toNat_le, hmod] at hle
      omega
    · next hle =>
      rw [UInt64.le_iff_toNat_le, hmod] at hle
      omega
  have h_red : ∀ (amount fee : UInt64),
      (reduce128 amount fee).toNat =
        (amount.toNat + 18446744073709551616 * fee.toNat) % 18446744069414584321 := by
    intro amount fee
    have ha : amount.toNat < 18446744073709551616 := amount.toNat_lt_size
    have hf : fee.toNat < 18446744073709551616 := fee.toNat_lt_size
    dsimp only [reduce128, splitTranscript]
    have hhi_lt : (fee / limbBase).toNat < 4294967296 := by rw [UInt64.toNat_div, hbase]; omega
    have hmid_lt : (fee % limbBase).toNat < 4294967296 := by rw [UInt64.toNat_mod, hbase]; omega
    have hh := h_high amount (fee / limbBase) hhi_lt
    rw [UInt64.toNat_div, hbase] at hh
    generalize foldHighLimb amount (fee / limbBase) = low2 at hh ⊢
    have hlo2_lt : low2.toNat < 18446744073709551616 := low2.toNat_lt_size
    have hm := h_mid low2 (fee % limbBase) hmid_lt
    rw [UInt64.toNat_mod, hbase] at hm
    generalize foldMidLimb low2 (fee % limbBase) = folded at hm ⊢
    have hfold_lt : folded.toNat < 18446744073709551616 := folded.toNat_lt_size
    have ⟨hc_lt, hc_eq⟩ := h_canon folded
    generalize canonicalize folded = res at hc_lt hc_eq ⊢
    rcases hh with hh | hh <;> rcases hm with hm | hm <;> rcases hc_eq with hc_eq | hc_eq <;> omega
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
    have hr := h_red amount fee
    dsimp only [challengeAuthorize] at hr ⊢
    dsimp only [verifyAffordability, buildQuote, candidateSpec, goldilocksDebit]
    generalize reduce128 amount fee = R at hr ⊢
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
            rw [UInt64.le_iff_toNat_le, h_sub_max, hr] at hfit
            rw [UInt64.le_iff_toNat_le, UInt64.toNat_add, UInt64.toNat_div, hdiv, hr] at hbal
            omega
          · cases hcall
        · cases hquote
      · cases hcall
    · intro hbal_nat
      have hfit : R ≤ u64Max - amount / principalDivisor := by
        rw [UInt64.le_iff_toNat_le, h_sub_max, hr]
        omega
      have hbal_u64 : amount / principalDivisor + R ≤ balance := by
        rw [UInt64.le_iff_toNat_le, UInt64.toNat_add, UInt64.toNat_div, hdiv, hr]
        omega
      exact ⟨amount / principalDivisor + R, by simp [hfit, hbal_u64]⟩
  · intro balance amount fee total hcall
    have ha : amount.toNat < 18446744073709551616 := amount.toNat_lt_size
    have hr := h_red amount fee
    dsimp only [challengeAuthorize] at hr hcall
    dsimp only [verifyAffordability, buildQuote] at hcall
    dsimp only [candidateSpec, goldilocksDebit]
    generalize reduce128 amount fee = R at hr hcall
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
          rw [UInt64.le_iff_toNat_le, h_sub_max, hr] at hfit
          rw [UInt64.toNat_add, UInt64.toNat_div, hdiv, hr]
          omega
        · cases hcall
      · cases hquote
    · cases hcall
