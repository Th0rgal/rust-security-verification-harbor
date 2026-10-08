by
  dsimp [AuditClaim, verdict, Conforms]
  let byteAt (x i : Nat) : Nat := (x >>> (8 * i)) % 256
  have h256 : (256 : Nat) = 2 ^ 8 := rfl
  have h256_pos : (0 : Nat) < 256 := by decide
  have h_bt_lt : ∀ x i, byteAt x i < 256 := fun x i => Nat.mod_lt _ h256_pos
  have h_isNz_le : ∀ b, (if 0 < b then 1 else 0) ≤ 1 := by
    intro b; split <;> decide
  have h_top_zero_lem : ∀ y < 18446744073709551616, byteAt y 8 = 0 := by
    intro y hy; dsimp [byteAt]; rw [Nat.shiftRight_eq_div_pow]; omega
  have h_cnt_bound_lem : ∀ (b0 b1 b2 b3 b4 b5 b6 b7 : Nat),
      isNz b0 + isNz b1 + isNz b2 + isNz b3 + isNz b4 + isNz b5 + isNz b6 + isNz b7 ≤ 8 := by
    intro b0 b1 b2 b3 b4 b5 b6 b7
    dsimp [isNz]
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
    intro x y i; dsimp [byteAt]; rw [h256, Nat.shiftRight_and_distrib, Nat.and_mod_two_pow]
  have h_bt_or : ∀ (x y i : Nat), byteAt (x ||| y) i = byteAt x i ||| byteAt y i := by
    intro x y i; dsimp [byteAt]; rw [h256, Nat.shiftRight_or_distrib, Nat.or_mod_two_pow]
  have h_shr8_bt : ∀ (x i : Nat), byteAt (x >>> (UInt64.toNat 8 % 64)) i = byteAt x (i + 1) := by
    intro x i; dsimp [byteAt]
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
    decide +kernel
  have h_M16_bt :
      byteAt 71777214294589695 0 = 255 ∧
      byteAt 71777214294589695 1 = 0 ∧
      byteAt 71777214294589695 2 = 255 ∧
      byteAt 71777214294589695 3 = 0 ∧
      byteAt 71777214294589695 4 = 255 ∧
      byteAt 71777214294589695 5 = 0 ∧
      byteAt 71777214294589695 6 = 255 ∧
      byteAt 71777214294589695 7 = 0 := by
    decide +kernel
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
    dsimp [byteAt]
    simp only [Nat.shiftRight_eq_div_pow]
    clear h_bt_lt h_isNz_le h_top_zero_lem h_cnt_bound_lem h_sum_bound_lem h_bt_and h_bt_or h_shr8_bt h_byte_facts h_H8_bt h_M16_bt byteAt
    omega
  have h_sub_l8_bytes : ∀ (m0 m1 m2 m3 m4 m5 m6 m7 : Nat),
      128 ≤ m0 ∧ m0 < 256 → 128 ≤ m1 ∧ m1 < 256 → 128 ≤ m2 ∧ m2 < 256 → 128 ≤ m3 ∧ m3 < 256 →
      128 ≤ m4 ∧ m4 < 256 → 128 ≤ m5 ∧ m5 < 256 → 128 ≤ m6 ∧ m6 < 256 → 128 ≤ m7 ∧ m7 < 256 →
      let s := (m0 + 256 * m1 + 65536 * m2 + 16777216 * m3 + 4294967296 * m4 + 1099511627776 * m5 + 281474976710656 * m6 + 72057594037927936 * m7) - 72340172838076673
      72340172838076673 ≤ m0 + 256 * m1 + 65536 * m2 + 16777216 * m3 + 4294967296 * m4 + 1099511627776 * m5 + 281474976710656 * m6 + 72057594037927936 * m7 ∧
      byteAt s 0 = m0 - 1 ∧
      byteAt s 1 = m1 - 1 ∧
      byteAt s 2 = m2 - 1 ∧
      byteAt s 3 = m3 - 1 ∧
      byteAt s 4 = m4 - 1 ∧
      byteAt s 5 = m5 - 1 ∧
      byteAt s 6 = m6 - 1 ∧
      byteAt s 7 = m7 - 1 := by
    intros
    dsimp only [byteAt]
    simp only [Nat.shiftRight_eq_div_pow]
    clear h_bt_lt h_isNz_le h_top_zero_lem h_cnt_bound_lem h_sum_bound_lem h_bt_and h_bt_or h_shr8_bt h_byte_facts h_H8_bt h_M16_bt h_decomp byteAt
    refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
  have h_l8_top : ∀ (c0 c1 c2 c3 c4 c5 c6 c7 : Nat),
      c0 ≤ 1 → c1 ≤ 1 → c2 ≤ 1 → c3 ≤ 1 → c4 ≤ 1 → c5 ≤ 1 → c6 ≤ 1 → c7 ≤ 1 →
      ((((128 * c0 + 256 * (128 * c1) + 65536 * (128 * c2) + 16777216 * (128 * c3) +
          4294967296 * (128 * c4) + 1099511627776 * (128 * c5) + 281474976710656 * (128 * c6) +
          72057594037927936 * (128 * c7)) / 128) * 72340172838076673) % 18446744073709551616) / 72057594037927936 =
      c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 := by
    intro c0 c1 c2 c3 c4 c5 c6 c7 h0 h1 h2 h3 h4 h5 h6 h7
    clear h_bt_lt h_isNz_le h_top_zero_lem h_cnt_bound_lem h_sum_bound_lem h_bt_and h_bt_or h_shr8_bt h_byte_facts h_H8_bt h_M16_bt h_decomp h_sub_l8_bytes byteAt
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
    clear h_bt_lt h_isNz_le h_top_zero_lem h_cnt_bound_lem h_sum_bound_lem h_bt_and h_bt_or h_shr8_bt h_byte_facts h_H8_bt h_M16_bt h_decomp h_sub_l8_bytes h_l8_top byteAt
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
  have h_cnt_sum : ∀ (x : UInt64),
      (countNzBytes x).toNat =
        isNz (byteAt x.toNat 0) +
        isNz (byteAt x.toNat 1) +
        isNz (byteAt x.toNat 2) +
        isNz (byteAt x.toNat 3) +
        isNz (byteAt x.toNat 4) +
        isNz (byteAt x.toNat 5) +
        isNz (byteAt x.toNat 6) +
        isNz (byteAt x.toNat 7) ∧
      (sumBytes x).toNat =
        byteAt x.toNat 0 +
        byteAt x.toNat 1 +
        byteAt x.toNat 2 +
        byteAt x.toNat 3 +
        byteAt x.toNat 4 +
        byteAt x.toNat 5 +
        byteAt x.toNat 6 +
        byteAt x.toNat 7 ∧
      (countNzBytes x).toNat ≤ 8 ∧
      (sumBytes x).toNat ≤ 2040 := by
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
    have h_sub_all := h_sub_l8_bytes
      (byteAt x.toNat 0 ||| 128)
      (byteAt x.toNat 1 ||| 128)
      (byteAt x.toNat 2 ||| 128)
      (byteAt x.toNat 3 ||| 128)
      (byteAt x.toNat 4 ||| 128)
      (byteAt x.toNat 5 ||| 128)
      (byteAt x.toNat 6 ||| 128)
      (byteAt x.toNat 7 ||| 128)
      hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7
    dsimp only at h_sub_all
    rw [← hor_decomp] at h_sub_all
    have h_sub_le : l8Mask ≤ x ||| h8Mask := by
      rw [UInt64.le_iff_toNat_le, UInt64.toNat_or, h_L8, h_H8]
      exact h_sub_all.1
    have h_sub_nat : ((x ||| h8Mask) - l8Mask).toNat = (x.toNat ||| 9259542123273814144) - 72340172838076673 := by
      rw [UInt64.toNat_sub_of_le _ _ h_sub_le, UInt64.toNat_or, h_L8, h_H8]
    rw [← h_sub_nat] at h_sub_all
    have hunz_decomp := h_decomp (uNz8 x).toNat hunz_lt
    dsimp only [uNz8] at hunz_decomp
    simp only [UInt64.toNat_and, UInt64.toNat_or, h_H8, h_bt_and, h_bt_or] at hunz_decomp
    rw [h_H8_bt.1, h_H8_bt.2.1, h_H8_bt.2.2.1, h_H8_bt.2.2.2.1,
        h_H8_bt.2.2.2.2.1, h_H8_bt.2.2.2.2.2.1, h_H8_bt.2.2.2.2.2.2.1, h_H8_bt.2.2.2.2.2.2.2,
        h_sub_all.2.1, h_sub_all.2.2.1, h_sub_all.2.2.2.1, h_sub_all.2.2.2.2.1,
        h_sub_all.2.2.2.2.2.1, h_sub_all.2.2.2.2.2.2.1, h_sub_all.2.2.2.2.2.2.2.1, h_sub_all.2.2.2.2.2.2.2.2,
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
    exact ⟨hc_eq, hs_eq, hc_le, hs_le⟩
  have h_tot : ∀ (amount fee : UInt64),
      ((amount >>> 1) + ((countNzBytes fee) <<< 8) + sumBytes fee).toNat = succinctDebit amount fee := by
    intro amount fee
    have ha : amount.toNat < 18446744073709551616 := amount.toNat_lt_size
    have ⟨hc, hs, hc_le, hs_le⟩ := h_cnt_sum fee
    have h_add_nat : ((amount >>> 1) + ((countNzBytes fee) <<< 8) + sumBytes fee).toNat =
        amount.toNat / 2 + (countNzBytes fee).toNat * 256 + (sumBytes fee).toNat := by
      simp only [UInt64.toNat_add, UInt64.toNat_shiftRight, UInt64.toNat_shiftLeft,
                 Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
      generalize (countNzBytes fee).toNat = c at hc_le ⊢
      generalize (sumBytes fee).toNat = s at hs_le ⊢
      clear h_bt_lt h_isNz_le h_top_zero_lem h_cnt_bound_lem h_sum_bound_lem h_bt_and h_bt_or h_shr8_bt h_byte_facts h_H8_bt h_M16_bt h_decomp h_sub_l8_bytes h_l8_top h_l16_top h_cnt_sum hc hs byteAt
      change ((amount.toNat / 2 + (c * 256) % 18446744073709551616) % 18446744073709551616 + s) % 18446744073709551616 =
        amount.toNat / 2 + c * 256 + s
      omega
    rw [h_add_nat, hc, hs]
    dsimp [succinctDebit, byteAt]
    simp only [Nat.shiftRight_eq_div_pow]
  constructor
  · intro balance amount fee
    have htot := h_tot amount fee
    dsimp only [challengeAuthorize, verifyAffordability, buildQuote, candidateSpec]
    generalize (amount >>> 1) + ((countNzBytes fee) <<< 8) + sumBytes fee = T at htot ⊢
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
    generalize (amount >>> 1) + ((countNzBytes fee) <<< 8) + sumBytes fee = T at htot hcall ⊢
    split at hcall
    · next hbal =>
      injection hcall with htot_eq
      subst htot_eq
      exact htot
    · cases hcall
