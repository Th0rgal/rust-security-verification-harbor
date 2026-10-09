by
  have hg (a f : UInt64) :
      (LeanModel.ClearingPipeline.protocolGross a f).toNat = grossNat a.toNat f.toNat := by
    have ha := a.toNat_lt
    have hf := f.toNat_lt
    simp only [LeanModel.ClearingPipeline.protocolGross, grossNat,
      UInt64.toNat_add, UInt64.toNat_div, UInt64.toNat_mod, UInt64.toNat_ofNat]
    omega
  have hb (a f : UInt64) :
      (LeanModel.ClearingPipeline.blobCharge a f).toNat = blobNat a.toNat f.toNat := by
    simp only [LeanModel.ClearingPipeline.blobCharge, blobNat,
      UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_div, UInt64.toNat_mod, UInt64.toNat_ofNat]
    omega
  have hl (a f : UInt64) :
      (LeanModel.ClearingPipeline.levyCharge a f).toNat = levyNat a.toNat f.toNat := by
    simp only [LeanModel.ClearingPipeline.levyCharge, levyNat,
      UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_mod, UInt64.toNat_ofNat]
    omega
  have hn (x : UInt64) :
      (LeanModel.ClearingPipeline.laneCharge x).toNat = laneNat x.toNat := by
    simp only [LeanModel.ClearingPipeline.laneCharge, laneNat]
    split <;> simp_all only [UInt64.eq_iff_toNat_eq, UInt64.toNat_mod,
      UInt64.toNat_add, UInt64.toNat_ofNat, UInt64.toNat_zero]
    all_goals omega
  have hnBound (x : Nat) : laneNat x ≤ 511 := by
    unfold laneNat
    split <;> omega
  have hc (f : UInt64) :
      (LeanModel.ClearingPipeline.calldataCharge f).toNat = calldataNat f.toNat := by
    have h0 := hnBound f.toNat
    have h1 := hnBound (f.toNat / 256)
    have h2 := hnBound (f.toNat / 65536)
    have h3 := hnBound (f.toNat / 16777216)
    have h4 := hnBound (f.toNat / 4294967296)
    have h5 := hnBound (f.toNat / 1099511627776)
    have h6 := hnBound (f.toNat / 281474976710656)
    have h7 := hnBound (f.toNat / 72057594037927936)
    simp only [LeanModel.ClearingPipeline.calldataCharge, calldataNat,
      UInt64.toNat_add, hn, UInt64.toNat_div, UInt64.toNat_ofNat]
    omega
  have hs (a f : UInt64) :
      (LeanModel.ClearingPipeline.computeClearingBreakdown a f).totalSurcharge.toNat =
        surchargeNat a.toNat f.toNat := by
    have ha := a.toNat_lt
    have hf := f.toNat_lt
    have gbound : grossNat a.toNat f.toNat ≤ 3689348814741911 := by
      unfold grossNat
      omega
    have bbound : blobNat a.toNat f.toNat ≤ 65535 := by
      unfold blobNat
      omega
    have lbound : levyNat a.toNat f.toNat < 2013265921 := by
      unfold levyNat
      omega
    have cbound : calldataNat f.toNat ≤ 4088 := by
      unfold calldataNat
      have h0 := hnBound f.toNat
      have h1 := hnBound (f.toNat / 256)
      have h2 := hnBound (f.toNat / 65536)
      have h3 := hnBound (f.toNat / 16777216)
      have h4 := hnBound (f.toNat / 4294967296)
      have h5 := hnBound (f.toNat / 1099511627776)
      have h6 := hnBound (f.toNat / 281474976710656)
      have h7 := hnBound (f.toNat / 72057594037927936)
      omega
    have hsub : LeanModel.ClearingPipeline.protocolGross a f / 10 ≤
        LeanModel.ClearingPipeline.protocolGross a f := by
      simp only [UInt64.le_iff_toNat_le, UInt64.toNat_div, UInt64.toNat_ofNat]
      omega
    simp only [LeanModel.ClearingPipeline.computeClearingBreakdown, surchargeNat,
      UInt64.toNat_add, UInt64.toNat_sub_of_le _ _ hsub, UInt64.toNat_div,
      UInt64.toNat_ofNat, hg, hb, hc, hl]
    omega
  change Conforms candidateSpec LeanModel.ClearingPipeline.challengeAuthorize
  constructor
  · intro b a f
    have ha := a.toNat_lt
    have hb := b.toNat_lt
    have hs' := hs a f
    simp only [LeanModel.ClearingPipeline.challengeAuthorize,
      LeanModel.ClearingPipeline.authorizeBreakdown, LeanModel.Constants.u64Max]
    simp only [candidateSpec, debitNat]
    split
    · rename_i hfit
      have hfit' : (LeanModel.ClearingPipeline.computeClearingBreakdown a f).totalSurcharge.toNat ≤
          18446744073709551615 - a.toNat := by
        simpa only [UInt64.le_iff_toNat_le, UInt64.toNat_sub_of_le _ _ (by simp only [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat]; omega),
          UInt64.toNat_ofNat] using hfit
      split
      · rename_i hbal
        have hbal' := UInt64.le_iff_toNat_le.mp hbal
        simp only [UInt64.toNat_add] at hbal'
        constructor
        · intro _; omega
        · intro _; exact ⟨_, rfl⟩
      · rename_i hbal
        have hbal' : ¬ (a + (LeanModel.ClearingPipeline.computeClearingBreakdown a f).totalSurcharge).toNat ≤ b.toNat :=
          fun h => hbal (UInt64.le_iff_toNat_le.mpr h)
        simp only [UInt64.toNat_add] at hbal'
        constructor
        · rintro ⟨_, h⟩; cases h
        · intro h; omega
    · rename_i hfit
      have hmax : a ≤ (18446744073709551615 : UInt64) := by
        simp only [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat]
        omega
      have hfit' := hfit
      simp only [UInt64.le_iff_toNat_le, UInt64.toNat_sub_of_le _ _ hmax,
        UInt64.toNat_ofNat] at hfit'
      constructor
      · rintro ⟨_, h⟩; cases h
      · intro h; omega
  · intro b a f total h
    have ha := a.toNat_lt
    have hs' := hs a f
    simp only [LeanModel.ClearingPipeline.challengeAuthorize,
      LeanModel.ClearingPipeline.authorizeBreakdown, LeanModel.Constants.u64Max] at h
    split at h
    · rename_i hfit
      have hmax : a ≤ (18446744073709551615 : UInt64) := by
        simp only [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat]
        omega
      have hfit' := hfit
      simp only [UInt64.le_iff_toNat_le, UInt64.toNat_sub_of_le _ _ hmax,
        UInt64.toNat_ofNat] at hfit'
      split at h
      · rename_i hbal
        cases h
        have hbal' := UInt64.le_iff_toNat_le.mp hbal
        simp only [UInt64.toNat_add] at hbal'
        simp only [candidateSpec, debitNat, UInt64.toNat_add]
        constructor <;> omega
      · cases h
    · cases h
