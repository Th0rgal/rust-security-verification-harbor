by
  dsimp [AuditClaim, verdict, Conforms]
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
  clear mg10_core
  have h_tot : ∀ (amount fee : UInt64),
      ((amount >>> 1) + div2x1Mg10 (fee % mg10Divisor) (amount &&& limbMask)).toNat = ruintDebit amount fee := by
    intro amount fee
    have hD : mg10Divisor.toNat = 32771 := rfl
    have hu1_nat : (fee % mg10Divisor).toNat = fee.toNat % 32771 := by
      simp only [UInt64.toNat_mod, hD]
    have hu0_nat : (amount &&& limbMask).toNat = amount.toNat % 65536 := by
      simp only [UInt64.toNat_and]
      exact Nat.and_two_pow_sub_one_eq_mod amount.toNat 16
    have hu1_lt : (fee % mg10Divisor).toNat < 32771 := by
      rw [hu1_nat]; clear div2x1Mg10_spec; omega
    have hu0_lt : (amount &&& limbMask).toNat < 65536 := by
      rw [hu0_nat]; clear div2x1Mg10_spec; omega
    have hq := div2x1Mg10_spec (fee % mg10Divisor) (amount &&& limbMask) hu1_lt hu0_lt
    let q := div2x1Mg10 (fee % mg10Divisor) (amount &&& limbMask)
    have hq_bound : q.toNat < 65536 := by
      dsimp [q]; rw [hq]; clear div2x1Mg10_spec; omega
    have ha_lt : amount.toNat < 18446744073709551616 := amount.toNat_lt_size
    have h_princ : (amount >>> 1).toNat = amount.toNat / 2 := by
      simp only [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]; rfl
    have h_add_nat : ((amount >>> 1) + q).toNat = amount.toNat / 2 + q.toNat := by
      simp only [UInt64.toNat_add, h_princ]
      generalize q.toNat = qv at hq_bound ⊢
      clear div2x1Mg10_spec hq hu1_nat hu0_nat
      omega
    dsimp [ruintDebit]
    rw [h_add_nat]
    dsimp [q]
    rw [hq, hu1_nat, hu0_nat]
  constructor
  · intro balance amount fee
    have htot := h_tot amount fee
    dsimp only [challengeAuthorize, verifyAffordability, buildQuote, candidateSpec]
    generalize (amount >>> 1) + div2x1Mg10 (fee % mg10Divisor) (amount &&& limbMask) = T at htot ⊢
    constructor
    · rintro ⟨total, hcall⟩
      split at hcall
      · next hbal =>
        rw [UInt64.le_iff_toNat_le, htot] at hbal
        exact hbal
      · cases hcall
    · intro hbal_nat
      have hbal_u64 : T ≤ balance := by
        rw [UInt64.le_iff_toNat_le, htot]
        exact hbal_nat
      exact ⟨T, by simp [hbal_u64]⟩
  · intro balance amount fee total hcall
    have htot := h_tot amount fee
    dsimp only [challengeAuthorize, verifyAffordability, buildQuote, candidateSpec] at hcall ⊢
    generalize (amount >>> 1) + div2x1Mg10 (fee % mg10Divisor) (amount &&& limbMask) = T at htot hcall ⊢
    split at hcall
    · next hbal =>
      injection hcall with htot_eq
      subst htot_eq
      exact htot
    · cases hcall
