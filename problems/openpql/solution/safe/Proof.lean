by
  dsimp [AuditClaim, verdict, Conforms]
  have hbase : radixBase.toNat = 65536 := rfl
  have hs16 : shift16.toNat = 65536 := rfl
  have hs32 : shift32.toNat = 4294967296 := rfl
  have hs48 : shift48.toNat = 281474976710656 := rfl
  have hhalf : halfDivisor.toNat = 2 := rfl
  have hone : (1 : UInt64).toNat = 1 := rfl
  have h_clamp : ∀ (a b : UInt64), 1 ≤ b.toNat → b.toNat ≤ 65536 →
      (clampDigit a b).toNat = (if a.toNat < b.toNat then a.toNat else b.toNat - 1) ∧
      (clampDigit a b).toNat + 1 ≤ b.toNat := by
    intro a b hb1 hb2
    dsimp [clampDigit]
    split
    · next hlt =>
      rw [UInt64.lt_iff_toNat_lt] at hlt
      rw [if_pos hlt]
      omega
    · next hlt =>
      rw [UInt64.lt_iff_toNat_lt] at hlt
      rw [if_neg hlt]
      have h1 : (1 : UInt64) ≤ b := by
        rw [UInt64.le_iff_toNat_le, hone]
        exact hb1
      rw [UInt64.toNat_sub_of_le _ _ h1, hone]
      omega
  have h_mr : ∀ (b0 b1 b2 b3 d0 d1 d2 d3 : Nat),
      b0 ≤ 65536 → b1 ≤ 65536 → b2 ≤ 65536 → b3 ≤ 65536 →
      d0 + 1 ≤ b0 → d1 + 1 ≤ b1 → d2 + 1 ≤ b2 → d3 + 1 ≤ b3 →
      b2 * b3 ≤ 4294967296 ∧
      b1 * (b2 * b3) ≤ 281474976710656 ∧
      b0 * (b1 * (b2 * b3)) ≤ 18446744073709551616 ∧
      d0 * (b1 * (b2 * b3)) + d1 * (b2 * b3) + d2 * b3 + d3 < 18446744073709551616 := by
    intro b0 b1 b2 b3 d0 d1 d2 d3 hb0 hb1 hb2 hb3 hd0 hd1 hd2 hd3
    have p23 : b2 * b3 ≤ 65536 * 65536 := Nat.mul_le_mul hb2 hb3
    have p123 : b1 * (b2 * b3) ≤ 65536 * (65536 * 65536) := Nat.mul_le_mul hb1 p23
    have p0123 : b0 * (b1 * (b2 * b3)) ≤ 65536 * (65536 * (65536 * 65536)) := Nat.mul_le_mul hb0 p123
    have e2 : (d2 + 1) * b3 ≤ b2 * b3 := Nat.mul_le_mul_right b3 hd2
    have e1 : (d1 + 1) * (b2 * b3) ≤ b1 * (b2 * b3) := Nat.mul_le_mul_right (b2 * b3) hd1
    have e0 : (d0 + 1) * (b1 * (b2 * b3)) ≤ b0 * (b1 * (b2 * b3)) := Nat.mul_le_mul_right (b1 * (b2 * b3)) hd0
    rw [Nat.add_mul, Nat.one_mul] at e2 e1 e0
    omega
  have h_enc : ∀ (amount fee : UInt64),
      ((amount / halfDivisor) + ((encodeMixedRadix amount fee) / halfDivisor)).toNat = openpqlDebit amount fee := by
    intro amount fee
    have ha : amount.toNat < 18446744073709551616 := amount.toNat_lt_size
    have hidx_size : (encodeMixedRadix amount fee).toNat < 18446744073709551616 := (encodeMixedRadix amount fee).toNat_lt_size
    have h_add_div : ((amount / halfDivisor) + ((encodeMixedRadix amount fee) / halfDivisor)).toNat =
        amount.toNat / 2 + (encodeMixedRadix amount fee).toNat / 2 := by
      simp only [UInt64.toNat_add, UInt64.toNat_div, hhalf]
      omega
    rw [h_add_div]
    dsimp only [encodeMixedRadix, openpqlDebit]
    have hb0 : ((fee % radixBase) + 1).toNat = (fee.toNat % 65536) + 1 ∧
        1 ≤ ((fee % radixBase) + 1).toNat ∧ ((fee % radixBase) + 1).toNat ≤ 65536 := by
      simp only [UInt64.toNat_add, UInt64.toNat_mod, hbase, hone]; omega
    have hb1 : (((fee / shift16) % radixBase) + 1).toNat = ((fee.toNat / 65536) % 65536) + 1 ∧
        1 ≤ (((fee / shift16) % radixBase) + 1).toNat ∧ (((fee / shift16) % radixBase) + 1).toNat ≤ 65536 := by
      simp only [UInt64.toNat_add, UInt64.toNat_mod, UInt64.toNat_div, hbase, hs16, hone]; omega
    have hb2 : (((fee / shift32) % radixBase) + 1).toNat = ((fee.toNat / 4294967296) % 65536) + 1 ∧
        1 ≤ (((fee / shift32) % radixBase) + 1).toNat ∧ (((fee / shift32) % radixBase) + 1).toNat ≤ 65536 := by
      simp only [UInt64.toNat_add, UInt64.toNat_mod, UInt64.toNat_div, hbase, hs32, hone]; omega
    have hb3 : (((fee / shift48) % radixBase) + 1).toNat = ((fee.toNat / 281474976710656) % 65536) + 1 ∧
        1 ≤ (((fee / shift48) % radixBase) + 1).toNat ∧ (((fee / shift48) % radixBase) + 1).toNat ≤ 65536 := by
      simp only [UInt64.toNat_add, UInt64.toNat_mod, UInt64.toNat_div, hbase, hs48, hone]; omega
    have ha0 : (amount % radixBase).toNat = amount.toNat % 65536 := by
      simp only [UInt64.toNat_mod, hbase]
    have ha1 : ((amount / shift16) % radixBase).toNat = (amount.toNat / 65536) % 65536 := by
      simp only [UInt64.toNat_mod, UInt64.toNat_div, hbase, hs16]
    have ha2 : ((amount / shift32) % radixBase).toNat = (amount.toNat / 4294967296) % 65536 := by
      simp only [UInt64.toNat_mod, UInt64.toNat_div, hbase, hs32]
    have ha3 : ((amount / shift48) % radixBase).toNat = (amount.toNat / 281474976710656) % 65536 := by
      simp only [UInt64.toNat_mod, UInt64.toNat_div, hbase, hs48]
    have ⟨hd0_eq, hd0_le⟩ := h_clamp (amount % radixBase) ((fee % radixBase) + 1) hb0.2.1 hb0.2.2
    have ⟨hd1_eq, hd1_le⟩ := h_clamp ((amount / shift16) % radixBase) (((fee / shift16) % radixBase) + 1) hb1.2.1 hb1.2.2
    have ⟨hd2_eq, hd2_le⟩ := h_clamp ((amount / shift32) % radixBase) (((fee / shift32) % radixBase) + 1) hb2.2.1 hb2.2.2
    have ⟨hd3_eq, hd3_le⟩ := h_clamp ((amount / shift48) % radixBase) (((fee / shift48) % radixBase) + 1) hb3.2.1 hb3.2.2
    generalize (fee % radixBase) + 1 = B0 at hb0 hd0_eq hd0_le ⊢
    generalize ((fee / shift16) % radixBase) + 1 = B1 at hb1 hd1_eq hd1_le ⊢
    generalize ((fee / shift32) % radixBase) + 1 = B2 at hb2 hd2_eq hd2_le ⊢
    generalize ((fee / shift48) % radixBase) + 1 = B3 at hb3 hd3_eq hd3_le ⊢
    generalize clampDigit (amount % radixBase) B0 = D0 at hd0_eq hd0_le ⊢
    generalize clampDigit ((amount / shift16) % radixBase) B1 = D1 at hd1_eq hd1_le ⊢
    generalize clampDigit ((amount / shift32) % radixBase) B2 = D2 at hd2_eq hd2_le ⊢
    generalize clampDigit ((amount / shift48) % radixBase) B3 = D3 at hd3_eq hd3_le ⊢
    rw [ha0] at hd0_eq
    rw [ha1] at hd1_eq
    rw [ha2] at hd2_eq
    rw [ha3] at hd3_eq
    have ⟨ho1_le, ho0_le, _, hidx_lt⟩ := h_mr B0.toNat B1.toNat B2.toNat B3.toNat D0.toNat D1.toNat D2.toNat D3.toNat
      hb0.2.2 hb1.2.2 hb2.2.2 hb3.2.2 hd0_le hd1_le hd2_le hd3_le
    have ho1_nat : (B2 * B3).toNat = B2.toNat * B3.toNat := by
      rw [UInt64.toNat_mul]; omega
    have ho0_nat : (B1 * (B2 * B3)).toNat = B1.toNat * (B2.toNat * B3.toNat) := by
      rw [UInt64.toNat_mul, ho1_nat]; omega
    have ht0_nat : (D0 * (B1 * (B2 * B3))).toNat = D0.toNat * (B1.toNat * (B2.toNat * B3.toNat)) := by
      rw [UInt64.toNat_mul, ho0_nat]; omega
    have ht1_nat : (D1 * (B2 * B3)).toNat = D1.toNat * (B2.toNat * B3.toNat) := by
      rw [UInt64.toNat_mul, ho1_nat]; omega
    have ht2_nat : (D2 * B3).toNat = D2.toNat * B3.toNat := by
      rw [UInt64.toNat_mul]; omega
    have hidx_nat : (D0 * (B1 * (B2 * B3)) + D1 * (B2 * B3) + D2 * B3 + D3).toNat =
        D0.toNat * (B1.toNat * (B2.toNat * B3.toNat)) + D1.toNat * (B2.toNat * B3.toNat) + D2.toNat * B3.toNat + D3.toNat := by
      simp only [UInt64.toNat_add, ht0_nat, ht1_nat, ht2_nat]
      omega
    rw [hidx_nat, hd0_eq, hd1_eq, hd2_eq, hd3_eq, hb0.1, hb1.1, hb2.1, hb3.1]
  constructor
  · intro balance amount fee
    have htot := h_enc amount fee
    dsimp only [challengeAuthorize, verifyAffordability, buildQuote, candidateSpec]
    generalize (amount / halfDivisor) + ((encodeMixedRadix amount fee) / halfDivisor) = T at htot ⊢
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
    have htot := h_enc amount fee
    dsimp only [challengeAuthorize, verifyAffordability, buildQuote, candidateSpec] at hcall ⊢
    generalize (amount / halfDivisor) + ((encodeMixedRadix amount fee) / halfDivisor) = T at htot hcall ⊢
    split at hcall
    · next hbal =>
      injection hcall with htot_eq
      subst htot_eq
      exact htot
    · cases hcall
