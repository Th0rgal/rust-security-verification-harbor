by
  change Conforms candidateSpec challengeAuthorize
  have hbps : bpsDenom.toNat = 10000 := rfl
  have hmaxrem : bpsMaxRem.toNat = 9999 := rfl
  have hq64 : u64ModBpsQuot.toNat = 1844674407370955 := rfl
  have hr64 : u64ModBpsRem.toNat = 1616 := rfl
  have hreb : rebateDivisor.toNat = 10 := rfl
  have hmax : u64Max.toNat = 18446744073709551615 := rfl
  have hsize : UInt64.size = 18446744073709551616 := rfl
  -- Stage 1: 128-bit carry-folded basis-point ceiling division and floor tier rebate
  have h_net_eq : ∀ (amount fee : UInt64),
      (evaluateSettlementFee (addU64WithCarry amount fee)).netFee.toNat =
        (amount.toNat + fee.toNat + 9999) / 10000 - (amount.toNat + fee.toNat + 9999) / 10000 / 10 := by
    intro amount fee
    have ha := amount.toNat_lt_size
    have hf := fee.toNat_lt_size
    dsimp only [evaluateSettlementFee, computeTierRebate, ceilDivBpsU64, addU64WithCarry]
    simp only [decide_eq_true_eq]
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
  -- Stage 2: Moller-Granlund 2-by-1 normalized reciprocal division
  have h_blob_eq : ∀ (amount fee : UInt64),
      (quoteBlobGasSlots amount fee).slotQuotient.toNat =
        ((fee.toNat % 32771) * 65536 + (amount.toNat % 65536)) / 32771 := by
    have mg10_core : ∀ (u1 u0 qFull q1 q0 r : Nat),
        u1 < 32771 →
        u0 < 65536 →
        qFull = u1 * 65524 + u1 * 65536 + u0 + 65536 →
        q1 = qFull / 65536 →
        q0 = qFull % 65536 →
        r = (3221225472 + u0 - q1 * 32771) % 65536 →
        let qCorr := if q0 < r then q1 - 1 else q1
        let rCorr := if q0 < r then (r + 32771) % 65536 else r
        let qFinal := if 32771 ≤ rCorr then qCorr + 1 else qCorr
        qFinal = (u1 * 65536 + u0) / 32771 ∧
        q1 ≥ 1 ∧
        q1 ≤ 65535 := by
      intro u1 u0 qFull q1 q0 r hu1 hu0 hqf hq1 hq0 hr
      clear hbps hmaxrem hq64 hr64 hreb hmax hsize h_net_eq
      dsimp only
      have h_u_div : u1 * 65536 + u0 = 32771 * ((u1 * 65536 + u0) / 32771) + ((u1 * 65536 + u0) % 32771) ∧
          (u1 * 65536 + u0) % 32771 < 32771 := by omega
      have h_qf_div : qFull = 65536 * q1 + q0 ∧ q0 < 65536 ∧ q1 ≥ 1 ∧ q1 ≤ 65535 := by omega
      generalize (u1 * 65536 + u0) / 32771 = q_true at h_u_div ⊢
      generalize (u1 * 65536 + u0) % 32771 = r_true at h_u_div
      clear hq1 hq0
      have h_cases :
          (q1 = q_true + 1 ∧ q0 < 65536 - 32771 + r_true) ∨
          (q1 = q_true ∧ (q0 < r_true → r_true + 32771 < 65536)) ∨
          (q1 + 1 = q_true ∧ r_true + 32771 ≤ q0 ∧ r_true + 32771 < 65536) := by
        have h_lo : 65536 * r_true + 65536 * 32771 * (q_true + 1) ≥
            65536 * 32771 * q1 + q0 * 32771 := by
          clear hr; omega
        have h_hi : 65536 * r_true + 65536 * 32771 * (q_true + 1) ≤
            65536 * 32771 * q1 + q0 * 32771 + 32770 * 36 + 65535 * 32765 := by
          clear hr h_lo; omega
        have h_rd : r_true < 32771 := h_u_div.2
        have h_q0 : q0 < 65536 := h_qf_div.2.1
        clear hr h_u_div h_qf_div hqf hu1 hu0
        omega
      have h_rd_65 : r_true < 65536 := by clear hr h_qf_div hqf h_cases; omega
      rcases h_cases with ⟨hc1, hc2⟩ | ⟨hc1, hc2⟩ | ⟨hc1, hc2, hc3⟩
      · have hr_val : r = 65536 - 32771 + r_true := by
          have h_eq : 3221225472 + u0 - q1 * 32771 = 65536 * (49151 - u1) + (65536 - 32771 + r_true) := by
            clear hr h_qf_div hqf; omega
          have h_lt : 65536 - 32771 + r_true < 65536 := by
            clear hr h_qf_div hqf h_eq; omega
          rw [hr, h_eq, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt h_lt]
        have h_rc : (r + 32771) % 65536 = r_true := by
          have h_eq : r + 32771 = 65536 * 1 + r_true := by
            clear hr h_qf_div hqf; omega
          rw [h_eq, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt h_rd_65]
        have hq_ge : q1 ≥ 1 := h_qf_div.2.2.1
        have hq_le : q1 ≤ 65535 := h_qf_div.2.2.2
        have h_rd : r_true < 32771 := h_u_div.2
        clear hr h_u_div h_qf_div hqf hu1 hu0
        rw [h_rc]
        split <;> (try split) <;> omega
      · have hr_val : r = r_true := by
          have h_eq : 3221225472 + u0 - q1 * 32771 = 65536 * (49152 - u1) + r_true := by
            clear hr h_qf_div hqf; omega
          rw [hr, h_eq, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt h_rd_65]
        have hq_ge : q1 ≥ 1 := h_qf_div.2.2.1
        have hq_le : q1 ≤ 65535 := h_qf_div.2.2.2
        have h_rd : r_true < 32771 := h_u_div.2
        clear hr h_u_div h_qf_div hqf hu1 hu0
        split
        · next h_lt_r =>
          have h_rc : (r + 32771) % 65536 = r_true + 32771 := by
            have h_lt2 : r + 32771 < 65536 := by omega
            rw [Nat.mod_eq_of_lt h_lt2, hr_val]
          rw [h_rc]
          split <;> omega
        · split <;> omega
      · have hr_val : r = r_true + 32771 := by
          have h_eq : 3221225472 + u0 - q1 * 32771 = 65536 * (49152 - u1) + (r_true + 32771) := by
            clear hr h_qf_div hqf; omega
          rw [hr, h_eq, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hc3]
        have hq_ge : q1 ≥ 1 := h_qf_div.2.2.1
        have hq_le : q1 ≤ 65535 := h_qf_div.2.2.2
        have h_rd : r_true < 32771 := h_u_div.2
        clear hr h_u_div h_qf_div hqf hu1 hu0
        split <;> (try split) <;> omega
    have div2x1Mg10_spec : ∀ (u1 u0 : UInt64),
        u1.toNat < 32771 →
        u0.toNat < 65536 →
        (div2x1Mg10 u1 u0).toNat = (u1.toNat * 65536 + u0.toNat) / 32771 := by
      intro u1 u0 hu1 hu0
      clear hbps hmaxrem hq64 hr64 hreb hmax hsize h_net_eq
      have hD : mg10Divisor.toNat = 32771 := rfl
      have hV : mg10Reciprocal.toNat = 65524 := rfl
      have hB : subBias.toNat = 3221225472 := rfl
      have h_and16 : ∀ (n : UInt64), (n &&& limbMask).toNat = n.toNat % 65536 := by
        intro n
        simp only [UInt64.toNat_and]
        exact Nat.and_two_pow_sub_one_eq_mod n.toNat 16
      have h_shr16 : ∀ (n : UInt64), (n >>> 16).toNat = n.toNat / 65536 := by
        intro n
        simp only [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
        rfl
      let qFull : UInt64 := (u1 * mg10Reciprocal) + (u1 <<< 16) + u0 + ((1 : UInt64) <<< 16)
      let q1 : UInt64 := qFull >>> 16
      let q0 : UInt64 := qFull &&& limbMask
      let r : UInt64 := (subBias + u0 - q1 * mg10Divisor) &&& limbMask
      have hqf_nat : qFull.toNat =
          u1.toNat * 65524 + u1.toNat * 65536 + u0.toNat + 65536 := by
        dsimp only [qFull]
        simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_shiftLeft, hV, Nat.shiftLeft_eq]
        change ((((u1.toNat * 65524) % 18446744073709551616 +
            (u1.toNat * 65536) % 18446744073709551616) % 18446744073709551616 + u0.toNat) % 18446744073709551616 + 65536) % 18446744073709551616 =
          u1.toNat * 65524 + u1.toNat * 65536 + u0.toNat + 65536
        clear mg10_core h_and16 h_shr16
        omega
      have hq1_nat : q1.toNat = qFull.toNat / 65536 := h_shr16 qFull
      have hq0_nat : q0.toNat = qFull.toNat % 65536 := h_and16 qFull
      have hq1_bounds : q1.toNat ≥ 1 ∧ q1.toNat ≤ 65535 := by
        clear mg10_core h_and16 h_shr16 hq0_nat
        omega
      have hr_nat : r.toNat = (3221225472 + u0.toNat - q1.toNat * 32771) % 65536 := by
        dsimp only [r]
        rw [h_and16]
        have h_lhs_nat : (q1 * mg10Divisor).toNat = q1.toNat * 32771 := by
          simp only [UInt64.toNat_mul, hD]
          apply Nat.mod_eq_of_lt
          clear mg10_core h_and16 h_shr16 hqf_nat hq1_nat hq0_nat
          omega
        have h_rhs_nat : (subBias + u0).toNat = 3221225472 + u0.toNat := by
          simp only [UInt64.toNat_add, hB]
          apply Nat.mod_eq_of_lt
          clear mg10_core h_and16 h_shr16 hqf_nat hq1_nat hq0_nat h_lhs_nat
          omega
        have h_le : q1 * mg10Divisor ≤ subBias + u0 := by
          rw [UInt64.le_iff_toNat_le, h_lhs_nat, h_rhs_nat]
          clear mg10_core h_and16 h_shr16 hqf_nat hq1_nat hq0_nat h_lhs_nat h_rhs_nat
          omega
        rw [UInt64.toNat_sub_of_le _ _ h_le, h_lhs_nat, h_rhs_nat]
      have h_core := mg10_core u1.toNat u0.toNat qFull.toNat q1.toNat q0.toNat r.toNat
        hu1 hu0 hqf_nat hq1_nat hq0_nat hr_nat
      dsimp only at h_core
      have hr_lt : r.toNat < 65536 := by
        rw [hr_nat]; clear mg10_core h_and16 h_shr16 hqf_nat hq1_nat hq0_nat h_core; omega
      dsimp only [div2x1Mg10]
      change (let (qCorr, rCorr) := if q0 < r then (q1 - 1, (r + mg10Divisor) &&& limbMask) else (q1, r)
              if mg10Divisor ≤ rCorr then qCorr + 1 else qCorr).toNat = _
      have h_q1_sub : (q1 - 1).toNat = q1.toNat - 1 := by
        have h1 : (1 : UInt64) ≤ q1 := by rw [UInt64.le_iff_toNat_le]; exact hq1_bounds.1
        rw [UInt64.toNat_sub_of_le _ _ h1]; rfl
      have h_r_add : ((r + mg10Divisor) &&& limbMask).toNat = (r.toNat + 32771) % 65536 := by
        rw [h_and16]
        simp only [UInt64.toNat_add, hD]
        have h_no_ovf : r.toNat + 32771 < 18446744073709551616 := by
          clear mg10_core h_and16 h_shr16 hqf_nat hq1_nat hq0_nat hr_nat h_core; omega
        rw [Nat.mod_eq_of_lt h_no_ovf]
      clear mg10_core h_and16 h_shr16 hqf_nat hq1_nat hq0_nat hr_nat
      by_cases h_cmp1 : q0 < r
      · have h_cmp1_nat : q0.toNat < r.toNat := UInt64.lt_iff_toNat_lt.mp h_cmp1
        simp only [h_cmp1, ite_true, h_cmp1_nat] at h_core ⊢
        by_cases h_cmp2 : mg10Divisor ≤ (r + mg10Divisor) &&& limbMask
        · have h_cmp2_nat : 32771 ≤ (r.toNat + 32771) % 65536 := by
            have h := UInt64.le_iff_toNat_le.mp h_cmp2
            rwa [hD, h_r_add] at h
          simp only [h_cmp2, ite_true, h_cmp2_nat] at h_core ⊢
          have h_add_1 : (q1 - 1 + 1).toNat = q1.toNat - 1 + 1 := by
            simp only [UInt64.toNat_add, h_q1_sub]
            change (q1.toNat - 1 + 1) % 18446744073709551616 = q1.toNat - 1 + 1
            clear h_core h_r_add; omega
          rw [h_add_1]
          exact h_core.1
        · have h_cmp2_nat : ¬ (32771 ≤ (r.toNat + 32771) % 65536) := by
            intro h_le_nat
            apply h_cmp2
            rw [UInt64.le_iff_toNat_le, hD, h_r_add]
            exact h_le_nat
          simp only [h_cmp2, ite_false, h_cmp2_nat] at h_core ⊢
          rw [h_q1_sub]
          exact h_core.1
      · have h_cmp1_nat : ¬ (q0.toNat < r.toNat) := by
          intro h_lt_nat
          exact h_cmp1 (UInt64.lt_iff_toNat_lt.mpr h_lt_nat)
        simp only [h_cmp1, ite_false, h_cmp1_nat] at h_core ⊢
        by_cases h_cmp2 : mg10Divisor ≤ r
        · have h_cmp2_nat : 32771 ≤ r.toNat := by
            have h := UInt64.le_iff_toNat_le.mp h_cmp2
            rwa [hD] at h
          simp only [h_cmp2, ite_true, h_cmp2_nat] at h_core ⊢
          have h_add_1 : (q1 + 1).toNat = q1.toNat + 1 := by
            simp only [UInt64.toNat_add]
            change (q1.toNat + 1) % 18446744073709551616 = q1.toNat + 1
            clear h_core h_r_add; omega
          rw [h_add_1]
          exact h_core.1
        · have h_cmp2_nat : ¬ (32771 ≤ r.toNat) := by
            intro h_le_nat
            apply h_cmp2
            rw [UInt64.le_iff_toNat_le, hD]
            exact h_le_nat
          simp only [h_cmp2, ite_false, h_cmp2_nat] at h_core ⊢
          exact h_core.1
    intro amount fee
    clear mg10_core hbps hmaxrem hq64 hr64 hreb hmax hsize h_net_eq
    have hD : mg10Divisor.toNat = 32771 := rfl
    have hu1_nat : (fee % mg10Divisor).toNat = fee.toNat % 32771 := by
      simp only [UInt64.toNat_mod, hD]
    have hu0_nat : (extractLowU16 amount).toNat = amount.toNat % 65536 := by
      dsimp only [extractLowU16]
      simp only [UInt64.toNat_and]
      exact Nat.and_two_pow_sub_one_eq_mod amount.toNat 16
    have hu1_lt : (fee % mg10Divisor).toNat < 32771 := by
      rw [hu1_nat]; clear div2x1Mg10_spec; omega
    have hu0_lt : (extractLowU16 amount).toNat < 65536 := by
      rw [hu0_nat]; clear div2x1Mg10_spec; omega
    dsimp only [quoteBlobGasSlots]
    rw [div2x1Mg10_spec (fee % mg10Divisor) (extractLowU16 amount) hu1_lt hu0_lt, hu1_nat, hu0_nat]
  -- Stage 3: Vigna SWAR 8-lane broadword calldata byte-lane surcharge
  have h_swar_eq : ∀ (fee : UInt64),
      let f := fee.toNat
      let b0 := f % 256
      let b1 := (f / 256) % 256
      let b2 := (f / 65536) % 256
      let b3 := (f / 16777216) % 256
      let b4 := (f / 4294967296) % 256
      let b5 := (f / 1099511627776) % 256
      let b6 := (f / 281474976710656) % 256
      let b7 := (f / 72057594037927936) % 256
      (quoteCalldataLaneSurcharge fee).surcharge.toNat =
        (isNz b0 + isNz b1 + isNz b2 + isNz b3 + isNz b4 + isNz b5 + isNz b6 + isNz b7) * 256 +
          (b0 + b1 + b2 + b3 + b4 + b5 + b6 + b7) ∧
      (quoteCalldataLaneSurcharge fee).surcharge.toNat ≤ 4088 := by
    clear hbps hmaxrem hq64 hr64 hreb hmax hsize h_net_eq h_blob_eq
    have h256 : (256 : Nat) = 2 ^ 8 := rfl
    have h256_pos : (0 : Nat) < 256 := by decide
    have h_bt_lt : ∀ x i, byteAt x i < 256 := fun x i => Nat.mod_lt _ h256_pos
    have h_isNz_le : ∀ b, (if 0 < b then 1 else 0) ≤ 1 := by
      intro b; split <;> decide
    have h_top_zero_lem : ∀ y < 18446744073709551616, byteAt y 8 = 0 := by
      intro y hy; dsimp only [byteAt]; rw [Nat.shiftRight_eq_div_pow]; omega
    have h_cnt_bound_lem : ∀ (b0 b1 b2 b3 b4 b5 b6 b7 : Nat),
        isNz b0 + isNz b1 + isNz b2 + isNz b3 + isNz b4 + isNz b5 + isNz b6 + isNz b7 ≤ 8 := by
      intro b0 b1 b2 b3 b4 b5 b6 b7
      dsimp only [isNz]
      have h0 := h_isNz_le b0
      have h1 := h_isNz_le b1
      have h2 := h_isNz_le b2
      have h3 := h_isNz_le b3
      have h4 := h_isNz_le b4
      have h5 := h_isNz_le b5
      have h6 := h_isNz_le b6
      have h7 := h_isNz_le b7
      clear h_bt_lt h_isNz_le h_top_zero_lem
      omega
    have h_sum_bound_lem : ∀ (b0 b1 b2 b3 b4 b5 b6 b7 : Nat),
        b0 < 256 → b1 < 256 → b2 < 256 → b3 < 256 → b4 < 256 → b5 < 256 → b6 < 256 → b7 < 256 →
        b0 + b1 + b2 + b3 + b4 + b5 + b6 + b7 ≤ 2040 := by
      intros
      clear h_bt_lt h_isNz_le h_top_zero_lem h_cnt_bound_lem
      omega
    have h_bt_and : ∀ (x y i : Nat), byteAt (x &&& y) i = byteAt x i &&& byteAt y i := by
      intro x y i; dsimp only [byteAt]; rw [h256, Nat.shiftRight_and_distrib, Nat.and_mod_two_pow]
    have h_bt_or : ∀ (x y i : Nat), byteAt (x ||| y) i = byteAt x i ||| byteAt y i := by
      intro x y i; dsimp only [byteAt]; rw [h256, Nat.shiftRight_or_distrib, Nat.or_mod_two_pow]
    have h_shr8_bt : ∀ (x i : Nat), byteAt (x >>> (UInt64.toNat 8 % 64)) i = byteAt x (i + 1) := by
      intro x i; dsimp only [byteAt]
      change ((x >>> 8) >>> (8 * i)) % 256 = (x >>> (8 * (i + 1))) % 256
      have h_sh : 8 + 8 * i = 8 * (i + 1) := by
        clear h_bt_lt h_isNz_le h_top_zero_lem h_cnt_bound_lem h_sum_bound_lem h_bt_and h_bt_or
        omega
      rw [← Nat.shiftRight_add, h_sh]
    have h_byte_facts :
        (∀ b < 256, 128 ≤ (b ||| 128) ∧ (b ||| 128) < 256) ∧
        (∀ b < 256, ((((b ||| 128) - 1) ||| b) &&& 128) = 128 * (if 0 < b then 1 else 0)) ∧
        (∀ b < 256, (b &&& 255) = b) ∧
        (∀ b < 256, (b &&& 0) = 0) := by
      decide +kernel
    have h_H8_bt :
        byteAt 9259542123273814144 0 = 128 ∧
        byteAt 9259542123273814144 1 = 128 ∧
        byteAt 9259542123273814144 2 = 128 ∧
        byteAt 9259542123273814144 3 = 128 ∧
        byteAt 9259542123273814144 4 = 128 ∧
        byteAt 9259542123273814144 5 = 128 ∧
        byteAt 9259542123273814144 6 = 128 ∧
        byteAt 9259542123273814144 7 = 128 := by
      decide
    have h_M16_bt :
        byteAt 71777214294589695 0 = 255 ∧
        byteAt 71777214294589695 1 = 0 ∧
        byteAt 71777214294589695 2 = 255 ∧
        byteAt 71777214294589695 3 = 0 ∧
        byteAt 71777214294589695 4 = 255 ∧
        byteAt 71777214294589695 5 = 0 ∧
        byteAt 71777214294589695 6 = 255 ∧
        byteAt 71777214294589695 7 = 0 := by
      decide
    have h_decomp : ∀ (y : Nat), y < 18446744073709551616 →
        y = byteAt y 0 +
            256 * byteAt y 1 +
            65536 * byteAt y 2 +
            16777216 * byteAt y 3 +
            4294967296 * byteAt y 4 +
            1099511627776 * byteAt y 5 +
            281474976710656 * byteAt y 6 +
            72057594037927936 * byteAt y 7 := by
      intro y hy
      dsimp only [byteAt]
      simp only [Nat.shiftRight_eq_div_pow]
      clear h_bt_lt h_isNz_le h_top_zero_lem h_cnt_bound_lem h_sum_bound_lem h_bt_and h_bt_or h_shr8_bt h_byte_facts h_H8_bt h_M16_bt
      omega
    have h_sub_l8_bytes : ∀ (m0 m1 m2 m3 m4 m5 m6 m7 s : Nat),
        128 ≤ m0 ∧ m0 < 256 → 128 ≤ m1 ∧ m1 < 256 → 128 ≤ m2 ∧ m2 < 256 → 128 ≤ m3 ∧ m3 < 256 →
        128 ≤ m4 ∧ m4 < 256 → 128 ≤ m5 ∧ m5 < 256 → 128 ≤ m6 ∧ m6 < 256 → 128 ≤ m7 ∧ m7 < 256 →
        s = (m0 + 256 * m1 + 65536 * m2 + 16777216 * m3 + 4294967296 * m4 + 1099511627776 * m5 + 281474976710656 * m6 + 72057594037927936 * m7) - 72340172838076673 →
        byteAt s 0 = m0 - 1 ∧
        byteAt s 1 = m1 - 1 ∧
        byteAt s 2 = m2 - 1 ∧
        byteAt s 3 = m3 - 1 ∧
        byteAt s 4 = m4 - 1 ∧
        byteAt s 5 = m5 - 1 ∧
        byteAt s 6 = m6 - 1 ∧
        byteAt s 7 = m7 - 1 := by
      clear h_bt_lt h_isNz_le h_top_zero_lem h_cnt_bound_lem h_sum_bound_lem h_bt_and h_bt_or h_shr8_bt h_byte_facts h_H8_bt h_M16_bt h_decomp
      intro m0 m1 m2 m3 m4 m5 m6 m7 s hm0 hm1 hm2 hm3 hm4 hm5 hm6 hm7 hs
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> {
        dsimp only [byteAt]
        rw [Nat.shiftRight_eq_div_pow, hs]
        omega
      }
    have h_l8_top : ∀ (c0 c1 c2 c3 c4 c5 c6 c7 : Nat),
        c0 ≤ 1 → c1 ≤ 1 → c2 ≤ 1 → c3 ≤ 1 → c4 ≤ 1 → c5 ≤ 1 → c6 ≤ 1 → c7 ≤ 1 →
        ((((128 * c0 + 256 * (128 * c1) + 65536 * (128 * c2) + 16777216 * (128 * c3) +
            4294967296 * (128 * c4) + 1099511627776 * (128 * c5) + 281474976710656 * (128 * c6) +
            72057594037927936 * (128 * c7)) / 128) * 72340172838076673) % 18446744073709551616) / 72057594037927936 =
        c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 := by
      intro c0 c1 c2 c3 c4 c5 c6 c7 h0 h1 h2 h3 h4 h5 h6 h7
      clear h_bt_lt h_isNz_le h_top_zero_lem h_cnt_bound_lem h_sum_bound_lem h_bt_and h_bt_or h_shr8_bt h_byte_facts h_H8_bt h_M16_bt h_decomp h_sub_l8_bytes
      have h_div :
          (c0 + 256 * (c0 + c1) + 65536 * (c0 + c1 + c2) + 16777216 * (c0 + c1 + c2 + c3) +
            4294967296 * (c0 + c1 + c2 + c3 + c4) + 1099511627776 * (c0 + c1 + c2 + c3 + c4 + c5) +
            281474976710656 * (c0 + c1 + c2 + c3 + c4 + c5 + c6) +
            72057594037927936 * (c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7)) / 72057594037927936 =
          c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 := by omega
      have h_lt :
          (c0 + 256 * (c0 + c1) + 65536 * (c0 + c1 + c2) + 16777216 * (c0 + c1 + c2 + c3) +
            4294967296 * (c0 + c1 + c2 + c3 + c4) + 1099511627776 * (c0 + c1 + c2 + c3 + c4 + c5) +
            281474976710656 * (c0 + c1 + c2 + c3 + c4 + c5 + c6) +
            72057594037927936 * (c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7)) < 18446744073709551616 := by clear h_div; omega
      have h_prod :
          ((128 * c0 + 256 * (128 * c1) + 65536 * (128 * c2) + 16777216 * (128 * c3) +
            4294967296 * (128 * c4) + 1099511627776 * (128 * c5) + 281474976710656 * (128 * c6) +
            72057594037927936 * (128 * c7)) / 128) * 72340172838076673 =
          18446744073709551616 * ((c1 + c2 + c3 + c4 + c5 + c6 + c7) + 256 * (c2 + c3 + c4 + c5 + c6 + c7) +
            65536 * (c3 + c4 + c5 + c6 + c7) + 16777216 * (c4 + c5 + c6 + c7) + 4294967296 * (c5 + c6 + c7) +
            1099511627776 * (c6 + c7) + 281474976710656 * c7) +
          (c0 + 256 * (c0 + c1) + 65536 * (c0 + c1 + c2) + 16777216 * (c0 + c1 + c2 + c3) +
            4294967296 * (c0 + c1 + c2 + c3 + c4) + 1099511627776 * (c0 + c1 + c2 + c3 + c4 + c5) +
            281474976710656 * (c0 + c1 + c2 + c3 + c4 + c5 + c6) +
            72057594037927936 * (c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7)) := by clear h_div h_lt; omega
      generalize ((128 * c0 + 256 * (128 * c1) + 65536 * (128 * c2) + 16777216 * (128 * c3) +
            4294967296 * (128 * c4) + 1099511627776 * (128 * c5) + 281474976710656 * (128 * c6) +
            72057594037927936 * (128 * c7)) / 128) * 72340172838076673 = P at h_prod ⊢
      generalize (c1 + c2 + c3 + c4 + c5 + c6 + c7) + 256 * (c2 + c3 + c4 + c5 + c6 + c7) +
            65536 * (c3 + c4 + c5 + c6 + c7) + 16777216 * (c4 + c5 + c6 + c7) + 4294967296 * (c5 + c6 + c7) +
            1099511627776 * (c6 + c7) + 281474976710656 * c7 = Q at h_prod
      generalize c0 + 256 * (c0 + c1) + 65536 * (c0 + c1 + c2) + 16777216 * (c0 + c1 + c2 + c3) +
            4294967296 * (c0 + c1 + c2 + c3 + c4) + 1099511627776 * (c0 + c1 + c2 + c3 + c4 + c5) +
            281474976710656 * (c0 + c1 + c2 + c3 + c4 + c5 + c6) +
            72057594037927936 * (c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7) = R at h_prod h_lt h_div
      subst h_prod
      have h_mod : (18446744073709551616 * Q + R) % 18446744073709551616 = R := by
        rw [Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt h_lt]
      generalize (18446744073709551616 * Q + R) % 18446744073709551616 = M at h_mod ⊢
      subst h_mod
      exact h_div
    have h_l16_top : ∀ (b0 b1 b2 b3 b4 b5 b6 b7 : Nat),
        b0 < 256 → b1 < 256 → b2 < 256 → b3 < 256 → b4 < 256 → b5 < 256 → b6 < 256 → b7 < 256 →
        ((((((b0 + 256 * 0 + 65536 * b2 + 16777216 * 0 + 4294967296 * b4 + 1099511627776 * 0 + 281474976710656 * b6 + 72057594037927936 * 0) +
             (b1 + 256 * 0 + 65536 * b3 + 16777216 * 0 + 4294967296 * b5 + 1099511627776 * 0 + 281474976710656 * b7 + 72057594037927936 * 0)) % 18446744073709551616) * 281479271743489) % 18446744073709551616) / 281474976710656) % 65536 =
        b0 + b1 + b2 + b3 + b4 + b5 + b6 + b7 := by
      intro b0 b1 b2 b3 b4 b5 b6 b7 h0 h1 h2 h3 h4 h5 h6 h7
      clear h_bt_lt h_isNz_le h_top_zero_lem h_cnt_bound_lem h_sum_bound_lem h_bt_and h_bt_or h_shr8_bt h_byte_facts h_H8_bt h_M16_bt h_decomp h_sub_l8_bytes h_l8_top
      have h_sum_lt :
          (b0 + 256 * 0 + 65536 * b2 + 16777216 * 0 + 4294967296 * b4 + 1099511627776 * 0 + 281474976710656 * b6 + 72057594037927936 * 0) +
          (b1 + 256 * 0 + 65536 * b3 + 16777216 * 0 + 4294967296 * b5 + 1099511627776 * 0 + 281474976710656 * b7 + 72057594037927936 * 0) < 18446744073709551616 := by omega
      have h_sum_mod := Nat.mod_eq_of_lt h_sum_lt
      have h_div :
          ((b0 + b1) + 65536 * (b0 + b1 + b2 + b3) + 4294967296 * (b0 + b1 + b2 + b3 + b4 + b5) +
            281474976710656 * (b0 + b1 + b2 + b3 + b4 + b5 + b6 + b7)) / 281474976710656 =
          b0 + b1 + b2 + b3 + b4 + b5 + b6 + b7 := by clear h_sum_lt h_sum_mod; omega
      have h_mod65536 :
          (b0 + b1 + b2 + b3 + b4 + b5 + b6 + b7) % 65536 =
          b0 + b1 + b2 + b3 + b4 + b5 + b6 + b7 := by clear h_sum_lt h_sum_mod h_div; omega
      have h_lt :
          ((b0 + b1) + 65536 * (b0 + b1 + b2 + b3) + 4294967296 * (b0 + b1 + b2 + b3 + b4 + b5) +
            281474976710656 * (b0 + b1 + b2 + b3 + b4 + b5 + b6 + b7)) < 18446744073709551616 := by
        clear h_sum_lt h_sum_mod h_div h_mod65536; omega
      have h_prod :
          ((b0 + 256 * 0 + 65536 * b2 + 16777216 * 0 + 4294967296 * b4 + 1099511627776 * 0 + 281474976710656 * b6 + 72057594037927936 * 0) +
           (b1 + 256 * 0 + 65536 * b3 + 16777216 * 0 + 4294967296 * b5 + 1099511627776 * 0 + 281474976710656 * b7 + 72057594037927936 * 0)) * 281479271743489 =
          18446744073709551616 * ((b2 + b3 + b4 + b5 + b6 + b7) + 65536 * (b4 + b5 + b6 + b7) + 4294967296 * (b6 + b7)) +
          ((b0 + b1) + 65536 * (b0 + b1 + b2 + b3) + 4294967296 * (b0 + b1 + b2 + b3 + b4 + b5) +
            281474976710656 * (b0 + b1 + b2 + b3 + b4 + b5 + b6 + b7)) := by
        clear h_sum_lt h_sum_mod h_div h_mod65536 h_lt; omega
      generalize ((b0 + 256 * 0 + 65536 * b2 + 16777216 * 0 + 4294967296 * b4 + 1099511627776 * 0 + 281474976710656 * b6 + 72057594037927936 * 0) +
             (b1 + 256 * 0 + 65536 * b3 + 16777216 * 0 + 4294967296 * b5 + 1099511627776 * 0 + 281474976710656 * b7 + 72057594037927936 * 0)) % 18446744073709551616 = S at h_sum_mod ⊢
      subst h_sum_mod
      generalize ((b0 + 256 * 0 + 65536 * b2 + 16777216 * 0 + 4294967296 * b4 + 1099511627776 * 0 + 281474976710656 * b6 + 72057594037927936 * 0) +
           (b1 + 256 * 0 + 65536 * b3 + 16777216 * 0 + 4294967296 * b5 + 1099511627776 * 0 + 281474976710656 * b7 + 72057594037927936 * 0)) * 281479271743489 = P at h_prod ⊢
      generalize (b2 + b3 + b4 + b5 + b6 + b7) + 65536 * (b4 + b5 + b6 + b7) + 4294967296 * (b6 + b7) = Q at h_prod
      generalize (b0 + b1) + 65536 * (b0 + b1 + b2 + b3) + 4294967296 * (b0 + b1 + b2 + b3 + b4 + b5) +
            281474976710656 * (b0 + b1 + b2 + b3 + b4 + b5 + b6 + b7) = R at h_prod h_lt h_div
      subst h_prod
      have h_mod : (18446744073709551616 * Q + R) % 18446744073709551616 = R := by
        rw [Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt h_lt]
      generalize (18446744073709551616 * Q + R) % 18446744073709551616 = M at h_mod ⊢
      subst h_mod
      rw [h_div]
      exact h_mod65536
    intro x
    have h_L8 : l8Mask.toNat = 72340172838076673 := rfl
    have h_H8 : h8Mask.toNat = 9259542123273814144 := rfl
    have h_M16 : m16Mask.toNat = 71777214294589695 := rfl
    have h_L16 : l16Mask.toNat = 281479271743489 := rfl
    have hx_lt : x.toNat < 18446744073709551616 := x.toNat_lt_size
    have hor_lt : (x ||| h8Mask).toNat < 18446744073709551616 := (x ||| h8Mask).toNat_lt_size
    have hunz_lt : (uNz8 x).toNat < 18446744073709551616 := (uNz8 x).toNat_lt_size
    have hlo_lt : (x &&& m16Mask).toNat < 18446744073709551616 := (x &&& m16Mask).toNat_lt_size
    have hhi_lt : ((x >>> 8) &&& m16Mask).toNat < 18446744073709551616 := ((x >>> 8) &&& m16Mask).toNat_lt_size
    have hor_decomp := h_decomp (x ||| h8Mask).toNat hor_lt
    simp only [UInt64.toNat_or, h_H8, h_bt_or] at hor_decomp
    rw [h_H8_bt.1, h_H8_bt.2.1, h_H8_bt.2.2.1, h_H8_bt.2.2.2.1,
        h_H8_bt.2.2.2.2.1, h_H8_bt.2.2.2.2.2.1, h_H8_bt.2.2.2.2.2.2.1, h_H8_bt.2.2.2.2.2.2.2] at hor_decomp
    have hb0 := h_byte_facts.1 (byteAt x.toNat 0) (h_bt_lt _ _)
    have hb1 := h_byte_facts.1 (byteAt x.toNat 1) (h_bt_lt _ _)
    have hb2 := h_byte_facts.1 (byteAt x.toNat 2) (h_bt_lt _ _)
    have hb3 := h_byte_facts.1 (byteAt x.toNat 3) (h_bt_lt _ _)
    have hb4 := h_byte_facts.1 (byteAt x.toNat 4) (h_bt_lt _ _)
    have hb5 := h_byte_facts.1 (byteAt x.toNat 5) (h_bt_lt _ _)
    have hb6 := h_byte_facts.1 (byteAt x.toNat 6) (h_bt_lt _ _)
    have hb7 := h_byte_facts.1 (byteAt x.toNat 7) (h_bt_lt _ _)
    have h_or_ge : 72340172838076673 ≤ x.toNat ||| 9259542123273814144 := by
      rw [hor_decomp]
      clear h_bt_lt h_isNz_le h_top_zero_lem h_cnt_bound_lem h_sum_bound_lem h_bt_and h_bt_or h_shr8_bt h_byte_facts h_H8_bt h_M16_bt h_decomp h_sub_l8_bytes h_l8_top h_l16_top hor_decomp
      omega
    have h_sub_le : l8Mask ≤ x ||| h8Mask := by
      rw [UInt64.le_iff_toNat_le, UInt64.toNat_or, h_L8, h_H8]
      exact h_or_ge
    have h_sub_eq : ((x ||| h8Mask) - l8Mask).toNat =
        ((byteAt x.toNat 0 ||| 128) +
         256 * (byteAt x.toNat 1 ||| 128) +
         65536 * (byteAt x.toNat 2 ||| 128) +
         16777216 * (byteAt x.toNat 3 ||| 128) +
         4294967296 * (byteAt x.toNat 4 ||| 128) +
         1099511627776 * (byteAt x.toNat 5 ||| 128) +
         281474976710656 * (byteAt x.toNat 6 ||| 128) +
         72057594037927936 * (byteAt x.toNat 7 ||| 128)) - 72340172838076673 := by
      rw [UInt64.toNat_sub_of_le _ _ h_sub_le, UInt64.toNat_or, h_L8, h_H8, hor_decomp]
    have h_sub_all := h_sub_l8_bytes
      (byteAt x.toNat 0 ||| 128)
      (byteAt x.toNat 1 ||| 128)
      (byteAt x.toNat 2 ||| 128)
      (byteAt x.toNat 3 ||| 128)
      (byteAt x.toNat 4 ||| 128)
      (byteAt x.toNat 5 ||| 128)
      (byteAt x.toNat 6 ||| 128)
      (byteAt x.toNat 7 ||| 128)
      ((x ||| h8Mask) - l8Mask).toNat
      hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 h_sub_eq
    have hunz_decomp := h_decomp (uNz8 x).toNat hunz_lt
    dsimp only [uNz8] at hunz_decomp
    simp only [UInt64.toNat_and, UInt64.toNat_or, h_H8, h_bt_and, h_bt_or] at hunz_decomp
    rw [h_H8_bt.1, h_H8_bt.2.1, h_H8_bt.2.2.1, h_H8_bt.2.2.2.1,
        h_H8_bt.2.2.2.2.1, h_H8_bt.2.2.2.2.2.1, h_H8_bt.2.2.2.2.2.2.1, h_H8_bt.2.2.2.2.2.2.2,
        h_sub_all.1, h_sub_all.2.1, h_sub_all.2.2.1, h_sub_all.2.2.2.1,
        h_sub_all.2.2.2.2.1, h_sub_all.2.2.2.2.2.1, h_sub_all.2.2.2.2.2.2.1, h_sub_all.2.2.2.2.2.2.2,
        h_byte_facts.2.1 (byteAt x.toNat 0) (h_bt_lt _ _),
        h_byte_facts.2.1 (byteAt x.toNat 1) (h_bt_lt _ _),
        h_byte_facts.2.1 (byteAt x.toNat 2) (h_bt_lt _ _),
        h_byte_facts.2.1 (byteAt x.toNat 3) (h_bt_lt _ _),
        h_byte_facts.2.1 (byteAt x.toNat 4) (h_bt_lt _ _),
        h_byte_facts.2.1 (byteAt x.toNat 5) (h_bt_lt _ _),
        h_byte_facts.2.1 (byteAt x.toNat 6) (h_bt_lt _ _),
        h_byte_facts.2.1 (byteAt x.toNat 7) (h_bt_lt _ _)] at hunz_decomp
    have hlo_decomp := h_decomp (x &&& m16Mask).toNat hlo_lt
    simp only [UInt64.toNat_and, h_M16, h_bt_and] at hlo_decomp
    rw [h_M16_bt.1, h_M16_bt.2.1, h_M16_bt.2.2.1, h_M16_bt.2.2.2.1,
        h_M16_bt.2.2.2.2.1, h_M16_bt.2.2.2.2.2.1, h_M16_bt.2.2.2.2.2.2.1, h_M16_bt.2.2.2.2.2.2.2,
        h_byte_facts.2.2.1 (byteAt x.toNat 0) (h_bt_lt _ _),
        h_byte_facts.2.2.2 (byteAt x.toNat 1) (h_bt_lt _ _),
        h_byte_facts.2.2.1 (byteAt x.toNat 2) (h_bt_lt _ _),
        h_byte_facts.2.2.2 (byteAt x.toNat 3) (h_bt_lt _ _),
        h_byte_facts.2.2.1 (byteAt x.toNat 4) (h_bt_lt _ _),
        h_byte_facts.2.2.2 (byteAt x.toNat 5) (h_bt_lt _ _),
        h_byte_facts.2.2.1 (byteAt x.toNat 6) (h_bt_lt _ _),
        h_byte_facts.2.2.2 (byteAt x.toNat 7) (h_bt_lt _ _)] at hlo_decomp
    have hhi_decomp := h_decomp ((x >>> 8) &&& m16Mask).toNat hhi_lt
    simp only [UInt64.toNat_and, UInt64.toNat_shiftRight, h_M16, h_bt_and, h_shr8_bt] at hhi_decomp
    have h_top_zero : byteAt x.toNat 8 = 0 := h_top_zero_lem x.toNat hx_lt
    rw [h_M16_bt.1, h_M16_bt.2.1, h_M16_bt.2.2.1, h_M16_bt.2.2.2.1,
        h_M16_bt.2.2.2.2.1, h_M16_bt.2.2.2.2.2.1, h_M16_bt.2.2.2.2.2.2.1, h_M16_bt.2.2.2.2.2.2.2,
        h_top_zero,
        h_byte_facts.2.2.1 (byteAt x.toNat 1) (h_bt_lt _ _),
        h_byte_facts.2.2.2 (byteAt x.toNat 2) (h_bt_lt _ _),
        h_byte_facts.2.2.1 (byteAt x.toNat 3) (h_bt_lt _ _),
        h_byte_facts.2.2.2 (byteAt x.toNat 4) (h_bt_lt _ _),
        h_byte_facts.2.2.1 (byteAt x.toNat 5) (h_bt_lt _ _),
        h_byte_facts.2.2.2 (byteAt x.toNat 6) (h_bt_lt _ _),
        h_byte_facts.2.2.1 (byteAt x.toNat 7) (h_bt_lt _ _),
        h_byte_facts.2.2.2 0 h256_pos] at hhi_decomp
    have hc_def : (countNzBytes x).toNat = ((((uNz8 x).toNat / 128) * 72340172838076673) % 18446744073709551616) / 72057594037927936 := by
      dsimp only [countNzBytes]
      simp only [UInt64.toNat_shiftRight, UInt64.toNat_mul, h_L8, Nat.shiftRight_eq_div_pow]
      rfl
    have hs_def : (sumBytes x).toNat =
        ((((((x &&& m16Mask).toNat + ((x >>> 8) &&& m16Mask).toNat) % 18446744073709551616) * 281479271743489) % 18446744073709551616) / 281474976710656) % 65536 := by
      dsimp only [sumBytes]
      simp only [UInt64.toNat_and, UInt64.toNat_shiftRight, UInt64.toNat_mul, UInt64.toNat_add, h_L16, Nat.shiftRight_eq_div_pow]
      exact Nat.and_two_pow_sub_one_eq_mod _ 16
    have hc_eq : (countNzBytes x).toNat =
        isNz (byteAt x.toNat 0) +
        isNz (byteAt x.toNat 1) +
        isNz (byteAt x.toNat 2) +
        isNz (byteAt x.toNat 3) +
        isNz (byteAt x.toNat 4) +
        isNz (byteAt x.toNat 5) +
        isNz (byteAt x.toNat 6) +
        isNz (byteAt x.toNat 7) := by
      have hunz_lhs : (uNz8 x).toNat = (((x ||| h8Mask) - l8Mask).toNat ||| x.toNat) &&& 9259542123273814144 := by
        dsimp only [uNz8]; simp only [UInt64.toNat_and, UInt64.toNat_or, h_H8]
      rw [← hunz_lhs] at hunz_decomp
      generalize (uNz8 x).toNat = u at hc_def hunz_decomp
      subst hunz_decomp
      rw [hc_def]
      exact h_l8_top
        (if 0 < byteAt x.toNat 0 then 1 else 0)
        (if 0 < byteAt x.toNat 1 then 1 else 0)
        (if 0 < byteAt x.toNat 2 then 1 else 0)
        (if 0 < byteAt x.toNat 3 then 1 else 0)
        (if 0 < byteAt x.toNat 4 then 1 else 0)
        (if 0 < byteAt x.toNat 5 then 1 else 0)
        (if 0 < byteAt x.toNat 6 then 1 else 0)
        (if 0 < byteAt x.toNat 7 then 1 else 0)
        (h_isNz_le _) (h_isNz_le _) (h_isNz_le _) (h_isNz_le _) (h_isNz_le _) (h_isNz_le _) (h_isNz_le _) (h_isNz_le _)
    have hs_eq : (sumBytes x).toNat =
        byteAt x.toNat 0 +
        byteAt x.toNat 1 +
        byteAt x.toNat 2 +
        byteAt x.toNat 3 +
        byteAt x.toNat 4 +
        byteAt x.toNat 5 +
        byteAt x.toNat 6 +
        byteAt x.toNat 7 := by
      have hlo_lhs : (x &&& m16Mask).toNat = x.toNat &&& 71777214294589695 := by
        simp only [UInt64.toNat_and, h_M16]
      have hhi_lhs : ((x >>> 8) &&& m16Mask).toNat = x.toNat >>> (UInt64.toNat 8 % 64) &&& 71777214294589695 := by
        simp only [UInt64.toNat_and, UInt64.toNat_shiftRight, h_M16]
      rw [← hlo_lhs] at hlo_decomp
      rw [← hhi_lhs] at hhi_decomp
      generalize (x &&& m16Mask).toNat = lo at hs_def hlo_decomp
      generalize ((x >>> 8) &&& m16Mask).toNat = hi at hs_def hhi_decomp
      subst hlo_decomp
      subst hhi_decomp
      rw [hs_def]
      exact h_l16_top
        (byteAt x.toNat 0)
        (byteAt x.toNat 1)
        (byteAt x.toNat 2)
        (byteAt x.toNat 3)
        (byteAt x.toNat 4)
        (byteAt x.toNat 5)
        (byteAt x.toNat 6)
        (byteAt x.toNat 7)
        (h_bt_lt _ _) (h_bt_lt _ _) (h_bt_lt _ _) (h_bt_lt _ _) (h_bt_lt _ _) (h_bt_lt _ _) (h_bt_lt _ _) (h_bt_lt _ _)
    have hc_le : (countNzBytes x).toNat ≤ 8 := by
      rw [hc_eq]
      exact h_cnt_bound_lem _ _ _ _ _ _ _ _
    have hs_le : (sumBytes x).toNat ≤ 2040 := by
      rw [hs_eq]
      exact h_sum_bound_lem _ _ _ _ _ _ _ _
        (h_bt_lt _ _) (h_bt_lt _ _) (h_bt_lt _ _) (h_bt_lt _ _) (h_bt_lt _ _) (h_bt_lt _ _) (h_bt_lt _ _) (h_bt_lt _ _)
    have h_sur_nat : (quoteCalldataLaneSurcharge x).surcharge.toNat =
        (countNzBytes x).toNat * 256 + (sumBytes x).toNat := by
      dsimp only [quoteCalldataLaneSurcharge]
      have hsh : calldataNzByteShift = 8 := rfl
      rw [hsh]
      simp only [UInt64.toNat_add, UInt64.toNat_shiftLeft, Nat.shiftLeft_eq]
      generalize (countNzBytes x).toNat = c at hc_le ⊢
      generalize (sumBytes x).toNat = s at hs_le ⊢
      clear h_bt_lt h_isNz_le h_top_zero_lem h_cnt_bound_lem h_sum_bound_lem h_bt_and h_bt_or h_shr8_bt h_byte_facts h_H8_bt h_M16_bt h_decomp h_sub_l8_bytes h_l8_top h_l16_top hc_def hs_def hc_eq hs_eq hor_decomp h_or_ge h_sub_le h_sub_eq h_sub_all hunz_decomp hlo_decomp hhi_decomp h_top_zero hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7
      change ((c * 256) % 18446744073709551616 + s) % 18446744073709551616 = c * 256 + s
      omega
    have h_sur_le : (quoteCalldataLaneSurcharge x).surcharge.toNat ≤ 4088 := by
      rw [h_sur_nat]
      generalize (countNzBytes x).toNat = c at hc_le ⊢
      generalize (sumBytes x).toNat = s at hs_le ⊢
      clear h_bt_lt h_isNz_le h_top_zero_lem h_cnt_bound_lem h_sum_bound_lem h_bt_and h_bt_or h_shr8_bt h_byte_facts h_H8_bt h_M16_bt h_decomp h_sub_l8_bytes h_l8_top h_l16_top hc_def hs_def hc_eq hs_eq hor_decomp h_or_ge h_sub_le h_sub_eq h_sub_all hunz_decomp hlo_decomp hhi_decomp h_top_zero hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 h_sur_nat
      omega
    refine ⟨?_, h_sur_le⟩
    rw [h_sur_nat, hc_eq, hs_eq]
    dsimp only [byteAt]
    simp only [Nat.shiftRight_eq_div_pow, Nat.mul_zero, Nat.pow_zero, Nat.div_one]
  -- Stage 4: BabyBear STARK Montgomery reduction
  have h_monty_eq : ∀ (amount fee : UInt64),
      (quoteProverTranscriptLevy amount fee).proverLevy.toNat =
        ((((amount.toNat % 4294967296) + (fee.toNat % 2013265921) * 4294967296) * 943718400) % 2013265921) := by
    clear hbps hmaxrem hq64 hr64 hreb hmax hsize h_net_eq h_blob_eq h_swar_eq
    have hp : babyBearP.toNat = 2013265921 := rfl
    have hmu : babyBearMu.toNat = 2281701377 := rfl
    have hbase : limbBase.toNat = 4294967296 := rfl
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
    intro amount fee
    have ⟨hx_eq, hx_lt⟩ := h_pack amount fee
    dsimp only [quoteProverTranscriptLevy]
    rw [h_red (packTranscript amount fee) hx_lt, hx_eq]
  -- Stage 5: Flash-settlement LP reserve retention (WordMath + LiquidityPool)
  have h_flash_eq : ∀ (amount fee : UInt64),
      (quoteFlashLpRetention amount fee).lpRetention.toNat =
        (amount.toNat + fee.toNat + 4999) / 5000 - (amount.toNat + fee.toNat + 4999) / 5000 / 4 := by
    clear hbps hmaxrem hq64 hr64 hreb hmax h_net_eq h_blob_eq h_swar_eq h_monty_eq
    have hfl : flashDenom.toNat = 5000 := rfl
    have hflmax : flashMaxRem.toNat = 4999 := rfl
    have hflq64 : u64ModFlashQuot.toNat = 3689348814741910 := rfl
    have hflr64 : u64ModFlashRem.toNat = 1616 := rfl
    have htr : treasuryCutDivisor.toNat = 4 := rfl
    intro amount fee
    have ha := amount.toNat_lt_size
    have hf := fee.toNat_lt_size
    have h_levy :
        (assessFlashFeeCeil amount fee).toNat =
        (amount.toNat + fee.toNat + 4999) / 5000 := by
      dsimp only [assessFlashFeeCeil, ceilDivFlashU64, addU64WithCarry]
      simp only [decide_eq_true_eq]
      split
      · next hwrap =>
        rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add] at hwrap
        simp only [UInt64.toNat_add, UInt64.toNat_div, UInt64.toNat_mod, hfl, hflmax, hflq64, hflr64]
        omega
      · next hnowrap =>
        rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add] at hnowrap
        split
        · next hbias =>
          rw [UInt64.lt_iff_toNat_lt] at hbias
          simp only [UInt64.toNat_add, UInt64.toNat_div, UInt64.toNat_mod, hfl, hflmax] at hbias ⊢
          omega
        · next hnobias =>
          rw [UInt64.lt_iff_toNat_lt] at hnobias
          simp only [UInt64.toNat_add, UInt64.toNat_div, hfl, hflmax] at hnobias ⊢
          omega
    dsimp only [quoteFlashLpRetention]
    generalize assessFlashFeeCeil amount fee = L at h_levy ⊢
    have h_cut_le : L / treasuryCutDivisor ≤ L := by
      rw [UInt64.le_iff_toNat_le, UInt64.toNat_div, htr]
      omega
    rw [UInt64.toNat_sub_of_le _ _ h_cut_le, UInt64.toNat_div, htr, h_levy]
  -- Stage 6: Sequencer transcript domain tag decoding (TranscriptCodec)
  have h_dom_eq : ∀ (fee : UInt64),
      (decodeDomainTag fee).toNat = (if fee.toNat % 256 = 0 then 90 else fee.toNat % 256) ∧
      (decodeDomainTag fee).toNat ≤ 255 := by
    clear hbps hmaxrem hq64 hr64 hreb hmax hsize h_net_eq h_blob_eq h_swar_eq h_monty_eq h_flash_eq
    have hseq : sequencerDomainTag.toNat = 90 := rfl
    have h_and8 : ∀ (n : UInt64), (n &&& codecTagMask).toNat = n.toNat % 256 := by
      intro n
      simp only [UInt64.toNat_and]
      exact Nat.and_two_pow_sub_one_eq_mod n.toNat 8
    intro fee
    dsimp only [decodeDomainTag]
    have hr := h_and8 fee
    by_cases h0 : fee &&& codecTagMask = 0
    · have h0_nat : fee.toNat % 256 = 0 := by
        have h := congrArg UInt64.toNat h0
        rwa [hr] at h
      rw [if_pos h0, if_pos h0_nat, hseq]
      omega
    · have h0_nat : ¬ (fee.toNat % 256 = 0) := by
        intro h_eq
        apply h0
        have h_toNat : (fee &&& codecTagMask).toNat = 0 := by omega
        exact UInt64.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq h_toNat)
      rw [if_neg h0, if_neg h0_nat, hr]
      omega
  -- Stage 7: Goldilocks 128-bit prime field reduction (GoldilocksField)
  have h_gl_eq : ∀ (amount fee : UInt64),
      (quoteBridgeVerifierFee amount fee).bridgeFee.toNat =
        (amount.toNat + 18446744073709551616 * fee.toNat) % 18446744069414584321 := by
    clear hbps hmaxrem hq64 hr64 hreb hmax hsize h_net_eq h_blob_eq h_swar_eq h_monty_eq h_flash_eq h_dom_eq
    have hmod : goldilocksP.toNat = 18446744069414584321 := rfl
    have heps : goldilocksEps.toNat = 4294967295 := rfl
    have hpow : (2 : Nat) ^ 64 = 18446744073709551616 := rfl
    have h_shr32 : ∀ (n : UInt64), (n >>> 32).toNat = n.toNat / 4294967296 := by
      intro n
      simp only [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
      rfl
    have h_and32 : ∀ (n : UInt64), (n &&& goldilocksEps).toNat = n.toNat % 4294967296 := by
      intro n
      simp only [UInt64.toNat_and]
      exact Nat.and_two_pow_sub_one_eq_mod n.toNat 32
    let foldHigh (low high : UInt64) : UInt64 :=
      if decide (low < high) then (low - high) + goldilocksP else low - high
    let foldMid (low2 mid : UInt64) : UInt64 :=
      let prod : UInt64 := mid * goldilocksEps
      let t2 : UInt64 := low2 + prod
      if decide (t2 < low2) then t2 + goldilocksEps else t2
    let canonGl (t3 : UInt64) : UInt64 :=
      if goldilocksP ≤ t3 then t3 - goldilocksP else t3
    have h_high : ∀ (low high : UInt64),
        high.toNat < 4294967296 →
        ((foldHigh low high).toNat + high.toNat = 18446744069414584321 + low.toNat ∨
         (foldHigh low high).toNat + high.toNat = low.toNat) := by
      intro low high hhi
      have hlo : low.toNat < 18446744073709551616 := low.toNat_lt_size
      dsimp only [foldHigh]
      simp only [decide_eq_true_eq]
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
        ((foldMid low2 mid).toNat = low2.toNat + 4294967295 * mid.toNat ∨
         (foldMid low2 mid).toNat + 18446744069414584321 = low2.toNat + 4294967295 * mid.toNat) := by
      intro low2 mid hmid
      have hlo2 : low2.toNat < 18446744073709551616 := low2.toNat_lt_size
      dsimp only [foldMid]
      simp only [decide_eq_true_eq]
      have hprod : (mid * goldilocksEps).toNat = 4294967295 * mid.toNat := by
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
        (canonGl folded).toNat < 18446744069414584321 ∧
        ((canonGl folded).toNat = folded.toNat ∨
         (canonGl folded).toNat + 18446744069414584321 = folded.toNat) := by
      intro folded
      have hf : folded.toNat < 18446744073709551616 := folded.toNat_lt_size
      dsimp only [canonGl]
      split
      · next hle =>
        rw [UInt64.toNat_sub_of_le _ _ hle, hmod]
        rw [UInt64.le_iff_toNat_le, hmod] at hle
        omega
      · next hle =>
        rw [UInt64.le_iff_toNat_le, hmod] at hle
        omega
    intro amount fee
    have ha : amount.toNat < 18446744073709551616 := amount.toNat_lt_size
    have hf : fee.toNat < 18446744073709551616 := fee.toNat_lt_size
    change (canonGl (foldMid (foldHigh amount (fee >>> 32)) (fee &&& goldilocksEps))).toNat =
      (amount.toNat + 18446744073709551616 * fee.toNat) % 18446744069414584321
    have hhi_lt : (fee >>> 32).toNat < 4294967296 := by rw [h_shr32]; omega
    have hmid_lt : (fee &&& goldilocksEps).toNat < 4294967296 := by rw [h_and32]; omega
    have hh := h_high amount (fee >>> 32) hhi_lt
    rw [h_shr32] at hh
    generalize foldHigh amount (fee >>> 32) = low2 at hh ⊢
    have hlo2_lt : low2.toNat < 18446744073709551616 := low2.toNat_lt_size
    have hm := h_mid low2 (fee &&& goldilocksEps) hmid_lt
    rw [h_and32] at hm
    generalize foldMid low2 (fee &&& goldilocksEps) = folded at hm ⊢
    have hfold_lt : folded.toNat < 18446744073709551616 := folded.toNat_lt_size
    have ⟨hc_lt, hc_eq⟩ := h_canon folded
    generalize canonGl folded = res at hc_lt hc_eq ⊢
    rcases hh with hh | hh <;> rcases hm with hm | hm <;> rcases hc_eq with hc_eq | hc_eq <;> omega
  -- Cross-module pipeline composition: baseSurcharge + bridgeSurcharge and ticket conservation
  have h_surcharge_eq : ∀ (amount fee : UInt64),
      amount.toNat +
        (computeClearingBreakdown amount fee).baseSurcharge.toNat +
        (computeClearingBreakdown amount fee).bridgeSurcharge.toNat =
          zkClearingDebit amount fee := by
    intro amount fee
    have ha := amount.toNat_lt_size
    have hf := fee.toNat_lt_size
    have h1 := h_net_eq amount fee
    have h2 := h_flash_eq amount fee
    have h3 := h_blob_eq amount fee
    have ⟨h4, h4_le⟩ := h_swar_eq fee
    have h5 := h_monty_eq amount fee
    have ⟨h6, h6_le⟩ := h_dom_eq fee
    have h7 := h_gl_eq amount fee
    clear h_net_eq h_flash_eq h_blob_eq h_swar_eq h_monty_eq h_dom_eq h_gl_eq
    dsimp only [computeClearingBreakdown]
    generalize (evaluateSettlementFee (addU64WithCarry amount fee)).netFee = S1 at h1 ⊢
    generalize (quoteFlashLpRetention amount fee).lpRetention = S2 at h2 ⊢
    generalize (quoteBlobGasSlots amount fee).slotQuotient = S3 at h3 ⊢
    generalize (quoteCalldataLaneSurcharge fee).surcharge = S4 at h4 h4_le ⊢
    generalize (quoteProverTranscriptLevy amount fee).proverLevy = S5 at h5 ⊢
    generalize decodeDomainTag fee = S6 at h6 h6_le ⊢
    generalize (quoteBridgeVerifierFee amount fee).bridgeFee = S7 at h7 ⊢
    have h_sum6 : (S1 + S2 + S3 + S4 + S5 + S6).toNat =
        S1.toNat + S2.toNat + S3.toNat + S4.toNat + S5.toNat + S6.toNat := by
      have h1_le : S1.toNat ≤ 3689348814741911 := by
        clear h2 h3 h4 h4_le h5 h6 h6_le h7; omega
      have h2_le : S2.toNat ≤ 7378697629483821 := by
        clear h1 h3 h4 h4_le h5 h6 h6_le h7 h1_le; omega
      have h3_le : S3.toNat ≤ 65535 := by
        clear h1 h2 h4 h4_le h5 h6 h6_le h7 h1_le h2_le; omega
      have h5_le : S5.toNat ≤ 2013265920 := by
        clear h1 h2 h3 h4 h4_le h6 h6_le h7 h1_le h2_le h3_le; omega
      clear h1 h2 h3 h4 h5 h6 h7
      simp only [UInt64.toNat_add]
      omega
    have h_assoc : amount.toNat + (S1.toNat + S2.toNat + S3.toNat + S4.toNat + S5.toNat + S6.toNat) + S7.toNat =
        amount.toNat + S1.toNat + S2.toNat + S3.toNat + S4.toNat + S5.toNat + S6.toNat + S7.toNat := by
      clear h1 h2 h3 h4 h4_le h5 h6 h6_le h7 h_sum6
      omega
    rw [h_sum6, h_assoc, h1, h2, h3, h4, h5, h6, h7]
    rfl
  have h_sub_max : ∀ (a : UInt64), (u64Max - a).toNat = 18446744073709551615 - a.toNat := by
    intro a
    have ha : a.toNat < 18446744073709551616 := a.toNat_lt_size
    have h_le : a ≤ u64Max := by
      rw [UInt64.le_iff_toNat_le, hmax]
      clear h_surcharge_eq
      omega
    rw [UInt64.toNat_sub_of_le _ _ h_le, hmax]
  clear h_net_eq h_flash_eq h_blob_eq h_swar_eq h_monty_eq h_dom_eq h_gl_eq
  constructor
  · intro balance amount fee
    change (∃ total, challengeAuthorize balance amount fee = some total) ↔ zkClearingDebit amount fee ≤ balance.toNat
    have hb : balance.toNat < 18446744073709551616 := balance.toNat_lt_size
    have ha : amount.toNat < 18446744073709551616 := amount.toNat_lt_size
    have hs := h_surcharge_eq amount fee
    dsimp only [challengeAuthorize, authorizeBreakdown]
    clear hbps hmaxrem hq64 hr64 hreb hmax hsize h_surcharge_eq
    generalize (computeClearingBreakdown amount fee).baseSurcharge = B_base at hs ⊢
    generalize (computeClearingBreakdown amount fee).bridgeSurcharge = B_gl at hs ⊢
    generalize zkClearingDebit amount fee = D at hs ⊢
    have hB_base : B_base.toNat < 18446744073709551616 := B_base.toNat_lt_size
    have hB_gl : B_gl.toNat < 18446744073709551616 := B_gl.toNat_lt_size
    by_cases hfit1 : B_gl ≤ u64Max - B_base
    · rw [if_pos hfit1]
      have hfit1_nat : B_gl.toNat ≤ 18446744073709551615 - B_base.toNat := by
        have h := UInt64.le_iff_toNat_le.mp hfit1
        rwa [h_sub_max] at h
      have h_tot_sur : (B_base + B_gl).toNat = B_base.toNat + B_gl.toNat := by
        rw [UInt64.toNat_add]
        clear h_sub_max hfit1
        omega
      by_cases hfit2 : B_base + B_gl ≤ u64Max - amount
      · rw [if_pos hfit2]
        have hfit2_nat : (B_base + B_gl).toNat ≤ 18446744073709551615 - amount.toNat := by
          have h := UInt64.le_iff_toNat_le.mp hfit2
          rwa [h_sub_max] at h
        by_cases hbal : amount + (B_base + B_gl) ≤ balance
        · rw [if_pos hbal]
          constructor
          · intro _
            have hbal_nat : (amount + (B_base + B_gl)).toNat ≤ balance.toNat := UInt64.le_iff_toNat_le.mp hbal
            rw [UInt64.toNat_add, h_tot_sur] at hbal_nat
            clear h_sub_max hfit1 hfit2 hbal
            omega
          · intro _
            exact ⟨amount + (B_base + B_gl), rfl⟩
        · rw [if_neg hbal]
          constructor
          · rintro ⟨_, hcall⟩
            cases hcall
          · intro h_le_d
            exfalso
            apply hbal
            rw [UInt64.le_iff_toNat_le, UInt64.toNat_add, h_tot_sur]
            clear h_sub_max hfit1 hfit2
            omega
      · rw [if_neg hfit2]
        constructor
        · rintro ⟨_, hcall⟩
          cases hcall
        · intro h_le_d
          exfalso
          apply hfit2
          rw [UInt64.le_iff_toNat_le, h_sub_max, h_tot_sur]
          clear h_sub_max hfit1
          omega
    · rw [if_neg hfit1]
      constructor
      · rintro ⟨_, hcall⟩
        cases hcall
      · intro h_le_d
        exfalso
        apply hfit1
        rw [UInt64.le_iff_toNat_le, h_sub_max]
        clear h_sub_max
        omega
  · intro balance amount fee total hcall
    change total.toNat = zkClearingDebit amount fee
    have ha : amount.toNat < 18446744073709551616 := amount.toNat_lt_size
    have hs := h_surcharge_eq amount fee
    dsimp only [challengeAuthorize, authorizeBreakdown] at hcall
    clear hbps hmaxrem hq64 hr64 hreb hmax hsize h_surcharge_eq
    generalize (computeClearingBreakdown amount fee).baseSurcharge = B_base at hs hcall
    generalize (computeClearingBreakdown amount fee).bridgeSurcharge = B_gl at hs hcall
    generalize zkClearingDebit amount fee = D at hs ⊢
    have hB_base : B_base.toNat < 18446744073709551616 := B_base.toNat_lt_size
    have hB_gl : B_gl.toNat < 18446744073709551616 := B_gl.toNat_lt_size
    by_cases hfit1 : B_gl ≤ u64Max - B_base
    · rw [if_pos hfit1] at hcall
      have hfit1_nat : B_gl.toNat ≤ 18446744073709551615 - B_base.toNat := by
        have h := UInt64.le_iff_toNat_le.mp hfit1
        rwa [h_sub_max] at h
      have h_tot_sur : (B_base + B_gl).toNat = B_base.toNat + B_gl.toNat := by
        rw [UInt64.toNat_add]
        clear h_sub_max hfit1
        omega
      by_cases hfit2 : B_base + B_gl ≤ u64Max - amount
      · rw [if_pos hfit2] at hcall
        have hfit2_nat : (B_base + B_gl).toNat ≤ 18446744073709551615 - amount.toNat := by
          have h := UInt64.le_iff_toNat_le.mp hfit2
          rwa [h_sub_max] at h
        by_cases hbal : amount + (B_base + B_gl) ≤ balance
        · rw [if_pos hbal] at hcall
          injection hcall with htot
          subst htot
          rw [UInt64.toNat_add, h_tot_sur]
          clear h_sub_max hfit1 hfit2 hbal
          omega
        · rw [if_neg hbal] at hcall
          cases hcall
      · rw [if_neg hfit2] at hcall
        cases hcall
    · rw [if_neg hfit1] at hcall
      cases hcall
