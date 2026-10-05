by
  change Conforms candidateSpec challengeAuthorize
  have hbps : bpsDenom.toNat = 10000 := rfl
  have hmaxrem : bpsMaxRem.toNat = 9999 := rfl
  have hq64 : u64ModBpsQuot.toNat = 1844674407370955 := rfl
  have hr64 : u64ModBpsRem.toNat = 1616 := rfl
  have hreb : rebateDivisor.toNat = 10 := rfl
  have hmax : u64Max.toNat = 18446744073709551615 := rfl
  have hsize : UInt64.size = 18446744073709551616 := rfl
  have h_net_eq : ∀ (amount fee : UInt64),
      let rawSum := amount + fee
      let grossFee :=
        if rawSum < amount then
          let foldedRem := (rawSum % bpsDenom) + u64ModBpsRem
          u64ModBpsQuot + (rawSum / bpsDenom) + ((foldedRem + bpsMaxRem) / bpsDenom)
        else
          let biased := rawSum + bpsMaxRem
          if biased < rawSum then
            (rawSum / bpsDenom) + (((rawSum % bpsDenom) + bpsMaxRem) / bpsDenom)
          else
            biased / bpsDenom
      (grossFee - grossFee / rebateDivisor).toNat =
        (amount.toNat + fee.toNat + 9999) / 10000 - (amount.toNat + fee.toNat + 9999) / 10000 / 10 := by
    intro amount fee
    have ha := amount.toNat_lt_size
    have hf := fee.toNat_lt_size
    dsimp only
    have h_gross :
        (if amount + fee < amount then
          u64ModBpsQuot + (amount + fee) / bpsDenom +
            (((amount + fee) % bpsDenom + u64ModBpsRem + bpsMaxRem) / bpsDenom)
        else
          if (amount + fee) + bpsMaxRem < amount + fee then
            (amount + fee) / bpsDenom + (((amount + fee) % bpsDenom + bpsMaxRem) / bpsDenom)
          else
            ((amount + fee) + bpsMaxRem) / bpsDenom).toNat =
        (amount.toNat + fee.toNat + 9999) / 10000 := by
      split
      · next hwrap =>
        rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add] at hwrap
        simp only [UInt64.toNat_add, UInt64.toNat_div, UInt64.toNat_mod, hbps, hmaxrem, hq64, hr64]
        omega
      · next hnowrap =>
        rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add] at hnowrap
        split
        · next hbias =>
          rw [UInt64.lt_iff_toNat_lt] at hbias
          simp only [UInt64.toNat_add, UInt64.toNat_div, UInt64.toNat_mod, hbps, hmaxrem] at hbias ⊢
          omega
        · next hnobias =>
          rw [UInt64.lt_iff_toNat_lt] at hnobias
          simp only [UInt64.toNat_add, UInt64.toNat_div, hbps, hmaxrem] at hnobias ⊢
          omega
    generalize
      (if amount + fee < amount then
        u64ModBpsQuot + (amount + fee) / bpsDenom +
          (((amount + fee) % bpsDenom + u64ModBpsRem + bpsMaxRem) / bpsDenom)
      else
        if (amount + fee) + bpsMaxRem < amount + fee then
          (amount + fee) / bpsDenom + (((amount + fee) % bpsDenom + bpsMaxRem) / bpsDenom)
        else
          ((amount + fee) + bpsMaxRem) / bpsDenom) = G at h_gross ⊢
    have h_rebate_le : G / rebateDivisor ≤ G := by
      rw [UInt64.le_iff_toNat_le, UInt64.toNat_div, hreb]
      omega
    rw [UInt64.toNat_sub_of_le _ _ h_rebate_le, UInt64.toNat_div, hreb, h_gross]
  constructor
  · intro balance amount fee
    have hb := balance.toNat_lt_size
    have ha := amount.toNat_lt_size
    have h_net := h_net_eq amount fee
    dsimp [challengeAuthorize, candidateSpec] at h_net ⊢
    generalize
      (if amount + fee < amount then
        u64ModBpsQuot + (amount + fee) / bpsDenom +
          (((amount + fee) % bpsDenom + u64ModBpsRem + bpsMaxRem) / bpsDenom)
      else
        if (amount + fee) + bpsMaxRem < amount + fee then
          (amount + fee) / bpsDenom + (((amount + fee) % bpsDenom + bpsMaxRem) / bpsDenom)
        else
          ((amount + fee) + bpsMaxRem) / bpsDenom) = G at h_net ⊢
    have h_amt_le_max : amount ≤ u64Max := by
      rw [UInt64.le_iff_toNat_le, hmax]
      omega
    constructor
    · rintro ⟨total, hcall⟩
      split at hcall
      · next hfit =>
        split at hcall
        · next hbal =>
          rw [UInt64.le_iff_toNat_le, UInt64.toNat_sub_of_le _ _ h_amt_le_max, h_net, hmax] at hfit
          rw [UInt64.le_iff_toNat_le, UInt64.toNat_add, h_net] at hbal
          omega
        · cases hcall
      · cases hcall
    · intro hbal_nat
      have hfit : G - G / rebateDivisor ≤ u64Max - amount := by
        rw [UInt64.le_iff_toNat_le, UInt64.toNat_sub_of_le _ _ h_amt_le_max, h_net, hmax]
        omega
      have hbal_u64 : amount + (G - G / rebateDivisor) ≤ balance := by
        rw [UInt64.le_iff_toNat_le, UInt64.toNat_add, h_net]
        omega
      exact ⟨amount + (G - G / rebateDivisor), by simp [hfit, hbal_u64]⟩
  · intro balance amount fee total hcall
    have ha := amount.toNat_lt_size
    have h_net := h_net_eq amount fee
    dsimp [challengeAuthorize, candidateSpec] at h_net hcall ⊢
    generalize
      (if amount + fee < amount then
        u64ModBpsQuot + (amount + fee) / bpsDenom +
          (((amount + fee) % bpsDenom + u64ModBpsRem + bpsMaxRem) / bpsDenom)
      else
        if (amount + fee) + bpsMaxRem < amount + fee then
          (amount + fee) / bpsDenom + (((amount + fee) % bpsDenom + bpsMaxRem) / bpsDenom)
        else
          ((amount + fee) + bpsMaxRem) / bpsDenom) = G at h_net hcall
    have h_amt_le_max : amount ≤ u64Max := by
      rw [UInt64.le_iff_toNat_le, hmax]
      omega
    split at hcall
    · next hfit =>
      split at hcall
      · next hbal =>
        injection hcall with htot
        subst htot
        rw [UInt64.le_iff_toNat_le, UInt64.toNat_sub_of_le _ _ h_amt_le_max, h_net, hmax] at hfit
        rw [UInt64.toNat_add, h_net]
        omega
      · cases hcall
    · cases hcall
