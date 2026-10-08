import SecurityChallenge
open SecurityChallenge

namespace SCSpec

def nz (x : Nat) : Nat := if x = 0 then 0 else 1
def b0 (f : UInt64) : Nat := f.toNat % 256
def b1 (f : UInt64) : Nat := f.toNat / 256 % 256
def b2 (f : UInt64) : Nat := f.toNat / 65536 % 256
def b3 (f : UInt64) : Nat := f.toNat / 16777216 % 256
def b4 (f : UInt64) : Nat := f.toNat / 4294967296 % 256
def b5 (f : UInt64) : Nat := f.toNat / 1099511627776 % 256
def b6 (f : UInt64) : Nat := f.toNat / 281474976710656 % 256
def b7 (f : UInt64) : Nat := f.toNat / 72057594037927936 % 256
def activeBytes (f : UInt64) : Nat :=
  nz (b0 f) + nz (b1 f) + nz (b2 f) + nz (b3 f) + nz (b4 f) + nz (b5 f) + nz (b6 f) + nz (b7 f)
def byteSum (f : UInt64) : Nat :=
  b0 f + b1 f + b2 f + b3 f + b4 f + b5 f + b6 f + b7 f
def totalDebit (a f : UInt64) : Nat := a.toNat / 2 + 256 * activeBytes f + byteSum f

def pk (a0 a1 a2 a3 a4 a5 a6 a7 : Nat) : Nat :=
  a0 + 256*(a1 + 256*(a2 + 256*(a3 + 256*(a4 + 256*(a5 + 256*(a6 + 256*a7))))))

theorem or_split (a b c d : Nat) (ha : a < 256) (hc : c < 256) :
    (a + 256*b) ||| (c + 256*d) = (a ||| c) + 256*(b ||| d) := by
  have h1 : ((a + 256*b) ||| (c + 256*d)) % 2^8 = a ||| c := by
    rw [Nat.or_mod_two_pow]; congr 1 <;> omega
  have h2 : ((a + 256*b) ||| (c + 256*d)) / 2^8 = b ||| d := by
    rw [← Nat.shiftRight_eq_div_pow, Nat.shiftRight_or_distrib, Nat.shiftRight_eq_div_pow,
      Nat.shiftRight_eq_div_pow]; congr 1 <;> omega
  have := Nat.mod_add_div ((a + 256*b) ||| (c + 256*d)) (2^8)
  rw [h1, h2] at this
  omega

theorem and_split (a b c d : Nat) (ha : a < 256) (hc : c < 256) :
    (a + 256*b) &&& (c + 256*d) = (a &&& c) + 256*(b &&& d) := by
  have h1 : ((a + 256*b) &&& (c + 256*d)) % 2^8 = a &&& c := by
    rw [Nat.and_mod_two_pow]; congr 1 <;> omega
  have h2 : ((a + 256*b) &&& (c + 256*d)) / 2^8 = b &&& d := by
    rw [← Nat.shiftRight_eq_div_pow, Nat.shiftRight_and_distrib, Nat.shiftRight_eq_div_pow,
      Nat.shiftRight_eq_div_pow]; congr 1 <;> omega
  have := Nat.mod_add_div ((a + 256*b) &&& (c + 256*d)) (2^8)
  rw [h1, h2] at this
  omega

theorem or_pk (a0 a1 a2 a3 a4 a5 a6 a7 c0 c1 c2 c3 c4 c5 c6 c7 : Nat)
    (ha0 : a0 < 256) (ha1 : a1 < 256) (ha2 : a2 < 256) (ha3 : a3 < 256)
    (ha4 : a4 < 256) (ha5 : a5 < 256) (ha6 : a6 < 256)
    (hc0 : c0 < 256) (hc1 : c1 < 256) (hc2 : c2 < 256) (hc3 : c3 < 256)
    (hc4 : c4 < 256) (hc5 : c5 < 256) (hc6 : c6 < 256) :
    pk a0 a1 a2 a3 a4 a5 a6 a7 ||| pk c0 c1 c2 c3 c4 c5 c6 c7 =
      pk (a0 ||| c0) (a1 ||| c1) (a2 ||| c2) (a3 ||| c3) (a4 ||| c4) (a5 ||| c5)
        (a6 ||| c6) (a7 ||| c7) := by
  unfold pk
  rw [or_split a0 _ c0 _ ha0 hc0, or_split a1 _ c1 _ ha1 hc1, or_split a2 _ c2 _ ha2 hc2,
    or_split a3 _ c3 _ ha3 hc3, or_split a4 _ c4 _ ha4 hc4, or_split a5 _ c5 _ ha5 hc5,
    or_split a6 _ c6 _ ha6 hc6]

theorem and_pk (a0 a1 a2 a3 a4 a5 a6 a7 c0 c1 c2 c3 c4 c5 c6 c7 : Nat)
    (ha0 : a0 < 256) (ha1 : a1 < 256) (ha2 : a2 < 256) (ha3 : a3 < 256)
    (ha4 : a4 < 256) (ha5 : a5 < 256) (ha6 : a6 < 256)
    (hc0 : c0 < 256) (hc1 : c1 < 256) (hc2 : c2 < 256) (hc3 : c3 < 256)
    (hc4 : c4 < 256) (hc5 : c5 < 256) (hc6 : c6 < 256) :
    pk a0 a1 a2 a3 a4 a5 a6 a7 &&& pk c0 c1 c2 c3 c4 c5 c6 c7 =
      pk (a0 &&& c0) (a1 &&& c1) (a2 &&& c2) (a3 &&& c3) (a4 &&& c4) (a5 &&& c5)
        (a6 &&& c6) (a7 &&& c7) := by
  unfold pk
  rw [and_split a0 _ c0 _ ha0 hc0, and_split a1 _ c1 _ ha1 hc1, and_split a2 _ c2 _ ha2 hc2,
    and_split a3 _ c3 _ ha3 hc3, and_split a4 _ c4 _ ha4 hc4, and_split a5 _ c5 _ ha5 hc5,
    and_split a6 _ c6 _ ha6 hc6]

set_option maxRecDepth 100000 in
theorem byte_nz : ∀ x < 256, (((x ||| 128) - 1) ||| x) &&& 128 = 128 * nz x := by
  unfold nz; decide

set_option maxRecDepth 100000 in
theorem byte_or128 : ∀ x < 256, 128 ≤ x ||| 128 ∧ x ||| 128 < 256 := by decide

set_option maxRecDepth 100000 in
theorem byte_and255 : ∀ x < 256, x &&& 255 = x := by decide

theorem or256 {x y : Nat} (hx : x < 256) (hy : y < 256) : x ||| y < 256 :=
  Nat.or_lt_two_pow (n := 8) hx hy

theorem nz_le (x : Nat) : nz x ≤ 1 := by unfold nz; split <;> omega

theorem lane (low c Q K : Nat) (hK : 0 < K) (hlow : low < K) (hfit : low + K*c < 2^64) :
    (low + K*c + 2^64*Q) % 2^64 / K = c := by
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hfit, Nat.add_mul_div_left _ _ hK,
    Nat.div_eq_of_lt hlow]
  all_goals omega

theorem unz_nat (x0 x1 x2 x3 x4 x5 x6 x7 : Nat)
    (h0 : x0 < 256) (h1 : x1 < 256) (h2 : x2 < 256) (h3 : x3 < 256)
    (h4 : x4 < 256) (h5 : x5 < 256) (h6 : x6 < 256) (h7 : x7 < 256) :
    (((pk x0 x1 x2 x3 x4 x5 x6 x7 ||| pk 128 128 128 128 128 128 128 128)
        - pk 1 1 1 1 1 1 1 1) ||| pk x0 x1 x2 x3 x4 x5 x6 x7) &&& pk 128 128 128 128 128 128 128 128
      = pk (128 * nz x0) (128 * nz x1) (128 * nz x2) (128 * nz x3) (128 * nz x4)
          (128 * nz x5) (128 * nz x6) (128 * nz x7) := by
  have k : (128:Nat) < 256 := by decide
  obtain ⟨l0, u0⟩ := byte_or128 x0 h0
  obtain ⟨l1, u1⟩ := byte_or128 x1 h1
  obtain ⟨l2, u2⟩ := byte_or128 x2 h2
  obtain ⟨l3, u3⟩ := byte_or128 x3 h3
  obtain ⟨l4, u4⟩ := byte_or128 x4 h4
  obtain ⟨l5, u5⟩ := byte_or128 x5 h5
  obtain ⟨l6, u6⟩ := byte_or128 x6 h6
  obtain ⟨l7, u7⟩ := byte_or128 x7 h7
  rw [or_pk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h0 h1 h2 h3 h4 h5 h6 k k k k k k k]
  rw [show pk (x0 ||| 128) (x1 ||| 128) (x2 ||| 128) (x3 ||| 128) (x4 ||| 128) (x5 ||| 128)
        (x6 ||| 128) (x7 ||| 128) - pk 1 1 1 1 1 1 1 1
      = pk ((x0 ||| 128) - 1) ((x1 ||| 128) - 1) ((x2 ||| 128) - 1) ((x3 ||| 128) - 1)
          ((x4 ||| 128) - 1) ((x5 ||| 128) - 1) ((x6 ||| 128) - 1) ((x7 ||| 128) - 1) by
    unfold pk; omega]
  rw [or_pk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) h0 h1 h2 h3 h4 h5 h6]
  rw [and_pk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (or256 (by omega) h0) (or256 (by omega) h1) (or256 (by omega) h2) (or256 (by omega) h3)
    (or256 (by omega) h4) (or256 (by omega) h5) (or256 (by omega) h6) k k k k k k k]
  rw [byte_nz x0 h0, byte_nz x1 h1, byte_nz x2 h2, byte_nz x3 h3, byte_nz x4 h4,
    byte_nz x5 h5, byte_nz x6 h6, byte_nz x7 h7]

theorem cnt_nat (z0 z1 z2 z3 z4 z5 z6 z7 : Nat)
    (h0 : z0 ≤ 1) (h1 : z1 ≤ 1) (h2 : z2 ≤ 1) (h3 : z3 ≤ 1)
    (h4 : z4 ≤ 1) (h5 : z5 ≤ 1) (h6 : z6 ≤ 1) (h7 : z7 ≤ 1) :
    pk z0 z1 z2 z3 z4 z5 z6 z7 * 72340172838076673 % 2^64 / 2^56
      = z0 + z1 + z2 + z3 + z4 + z5 + z6 + z7 := by
  have e : pk z0 z1 z2 z3 z4 z5 z6 z7 * 72340172838076673 =
      (z0 + 256*(z0+z1) + 65536*(z0+z1+z2) + 16777216*(z0+z1+z2+z3)
        + 4294967296*(z0+z1+z2+z3+z4) + 1099511627776*(z0+z1+z2+z3+z4+z5)
        + 281474976710656*(z0+z1+z2+z3+z4+z5+z6))
      + 2^56 * (z0 + z1 + z2 + z3 + z4 + z5 + z6 + z7)
      + 2^64 * ((z1+z2+z3+z4+z5+z6+z7) + 256*(z2+z3+z4+z5+z6+z7) + 65536*(z3+z4+z5+z6+z7)
        + 16777216*(z4+z5+z6+z7) + 4294967296*(z5+z6+z7) + 1099511627776*(z6+z7)
        + 281474976710656*z7) := by
    unfold pk; omega
  rw [e, lane _ _ _ _ (by decide) (by omega) (by omega)]

theorem sum_nat (x0 x1 x2 x3 x4 x5 x6 x7 : Nat)
    (h0 : x0 < 256) (h1 : x1 < 256) (h2 : x2 < 256) (h3 : x3 < 256)
    (h4 : x4 < 256) (h5 : x5 < 256) (h6 : x6 < 256) (h7 : x7 < 256) :
    ((pk x0 0 x2 0 x4 0 x6 0 + pk x1 0 x3 0 x5 0 x7 0) * 281479271743489 % 2^64 / 2^48)
      = x0 + x1 + x2 + x3 + x4 + x5 + x6 + x7 := by
  have e : (pk x0 0 x2 0 x4 0 x6 0 + pk x1 0 x3 0 x5 0 x7 0) * 281479271743489 =
      ((x0+x1) + 65536*(x0+x1+x2+x3) + 4294967296*(x0+x1+x2+x3+x4+x5))
      + 2^48 * (x0 + x1 + x2 + x3 + x4 + x5 + x6 + x7)
      + 2^64 * ((x2+x3+x4+x5+x6+x7) + 65536*(x4+x5+x6+x7) + 4294967296*(x6+x7)) := by
    unfold pk; omega
  rw [e, lane _ _ _ _ (by decide) (by omega) (by omega)]

theorem decomp (f : UInt64) :
    f.toNat = pk (b0 f) (b1 f) (b2 f) (b3 f) (b4 f) (b5 f) (b6 f) (b7 f) := by
  have := UInt64.toNat_lt f
  unfold pk b0 b1 b2 b3 b4 b5 b6 b7
  omega

theorem bytes_lt (f : UInt64) : b0 f < 256 ∧ b1 f < 256 ∧ b2 f < 256 ∧ b3 f < 256 ∧
    b4 f < 256 ∧ b5 f < 256 ∧ b6 f < 256 ∧ b7 f < 256 := by
  unfold b0 b1 b2 b3 b4 b5 b6 b7
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> exact Nat.mod_lt _ (by decide)

theorem count_eq (f : UInt64) : (countNzBytes f).toNat = activeBytes f := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := bytes_lt f
  have hH : h8Mask.toNat = pk 128 128 128 128 128 128 128 128 := by decide
  have hL : l8Mask.toNat = pk 1 1 1 1 1 1 1 1 := by decide
  have hL' : l8Mask.toNat = 72340172838076673 := by decide
  have hx := decomp f
  have hor : (f ||| h8Mask).toNat = pk (b0 f ||| 128) (b1 f ||| 128) (b2 f ||| 128)
      (b3 f ||| 128) (b4 f ||| 128) (b5 f ||| 128) (b6 f ||| 128) (b7 f ||| 128) := by
    rw [UInt64.toNat_or, hx, hH]
    exact or_pk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h0 h1 h2 h3 h4 h5 h6
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hle : l8Mask ≤ f ||| h8Mask := by
    rw [UInt64.le_iff_toNat_le, hor, hL]
    have := (byte_or128 _ h0).1; have := (byte_or128 _ h1).1; have := (byte_or128 _ h2).1
    have := (byte_or128 _ h3).1; have := (byte_or128 _ h4).1; have := (byte_or128 _ h5).1
    have := (byte_or128 _ h6).1; have := (byte_or128 _ h7).1
    unfold pk; omega
  have hu : (uNz8 f).toNat = pk (128 * nz (b0 f)) (128 * nz (b1 f)) (128 * nz (b2 f))
      (128 * nz (b3 f)) (128 * nz (b4 f)) (128 * nz (b5 f)) (128 * nz (b6 f))
      (128 * nz (b7 f)) := by
    unfold uNz8
    rw [UInt64.toNat_and, UInt64.toNat_or, UInt64.toNat_sub_of_le _ _ hle, UInt64.toNat_or,
      hx, hH, hL]
    exact unz_nat _ _ _ _ _ _ _ _ h0 h1 h2 h3 h4 h5 h6 h7
  have e7 : (7 : UInt64).toNat % 64 = 7 := by decide
  have e56 : (56 : UInt64).toNat % 64 = 56 := by decide
  have hdiv : pk (128 * nz (b0 f)) (128 * nz (b1 f)) (128 * nz (b2 f))
      (128 * nz (b3 f)) (128 * nz (b4 f)) (128 * nz (b5 f)) (128 * nz (b6 f))
      (128 * nz (b7 f)) / 2^7 = pk (nz (b0 f)) (nz (b1 f)) (nz (b2 f)) (nz (b3 f))
      (nz (b4 f)) (nz (b5 f)) (nz (b6 f)) (nz (b7 f)) := by
    unfold pk; omega
  unfold countNzBytes
  rw [UInt64.toNat_shiftRight, UInt64.toNat_mul, UInt64.toNat_shiftRight, hu, e7, e56, hL',
    Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, hdiv,
    cnt_nat _ _ _ _ _ _ _ _ (nz_le _) (nz_le _) (nz_le _) (nz_le _) (nz_le _) (nz_le _)
      (nz_le _) (nz_le _)]
  rfl

theorem sum_eq (f : UInt64) : (sumBytes f).toNat = byteSum f := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := bytes_lt f
  have hM : m16Mask.toNat = pk 255 0 255 0 255 0 255 0 := by decide
  have hL : l16Mask.toNat = 281479271743489 := by decide
  have hF : (0xFFFF : UInt64).toNat = 2^16 - 1 := by decide
  have e8 : (8 : UInt64).toNat % 64 = 8 := by decide
  have e48 : (48 : UInt64).toNat % 64 = 48 := by decide
  have hx := decomp f
  have k : (255:Nat) < 256 := by decide
  have z : (0:Nat) < 256 := by decide
  have hlo : (f &&& m16Mask).toNat = pk (b0 f) 0 (b2 f) 0 (b4 f) 0 (b6 f) 0 := by
    rw [UInt64.toNat_and, hx, hM,
      and_pk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h0 h1 h2 h3 h4 h5 h6 k z k z k z k,
      byte_and255 _ h0, byte_and255 _ h2, byte_and255 _ h4, byte_and255 _ h6]
    simp only [Nat.and_zero]
  have hsh : (f >>> 8).toNat = pk (b1 f) (b2 f) (b3 f) (b4 f) (b5 f) (b6 f) (b7 f) 0 := by
    rw [UInt64.toNat_shiftRight, e8, Nat.shiftRight_eq_div_pow, hx]
    unfold pk; omega
  have hhi : ((f >>> 8) &&& m16Mask).toNat = pk (b1 f) 0 (b3 f) 0 (b5 f) 0 (b7 f) 0 := by
    rw [UInt64.toNat_and, hsh, hM,
      and_pk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 k z k z k z k,
      byte_and255 _ h1, byte_and255 _ h3, byte_and255 _ h5, byte_and255 _ h7]
    simp only [Nat.and_zero]
  have hadd : ((f &&& m16Mask) + ((f >>> 8) &&& m16Mask)).toNat
      = pk (b0 f) 0 (b2 f) 0 (b4 f) 0 (b6 f) 0 + pk (b1 f) 0 (b3 f) 0 (b5 f) 0 (b7 f) 0 := by
    rw [UInt64.toNat_add, hlo, hhi]
    apply Nat.mod_eq_of_lt
    unfold pk; omega
  have hlt : b0 f + b1 f + b2 f + b3 f + b4 f + b5 f + b6 f + b7 f < 2^16 := by omega
  simp only [sumBytes]
  rw [UInt64.toNat_and, UInt64.toNat_shiftRight, UInt64.toNat_mul, hadd, hL, hF, e48,
    Nat.shiftRight_eq_div_pow, sum_nat _ _ _ _ _ _ _ _ h0 h1 h2 h3 h4 h5 h6 h7,
    Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hlt]
  rfl

def qT (a f : UInt64) : UInt64 := (a >>> 1) + (countNzBytes f <<< 8) + sumBytes f

theorem qT_eq (a f : UInt64) : (qT a f).toNat = totalDebit a f := by
  have e1 : (1 : UInt64).toNat % 64 = 1 := by decide
  have e8 : (8 : UInt64).toNat % 64 = 8 := by decide
  have ha := UInt64.toNat_lt a
  have hc := count_eq f
  have hs := sum_eq f
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := bytes_lt f
  have := nz_le (b0 f); have := nz_le (b1 f); have := nz_le (b2 f); have := nz_le (b3 f)
  have := nz_le (b4 f); have := nz_le (b5 f); have := nz_le (b6 f); have := nz_le (b7 f)
  unfold qT totalDebit
  rw [UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_shiftRight, UInt64.toNat_shiftLeft,
    hc, hs, e1, e8, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  unfold activeBytes byteSum
  omega

theorem auth_eq (b a f : UInt64) :
    challengeAuthorize b a f = if qT a f ≤ b then some (qT a f) else none := rfl

end SCSpec

def candidateSpec : AuthorizationSpec where
  accepts b a f := SCSpec.totalDebit a f ≤ b.toNat
  output b a f t := t.toNat = SCSpec.totalDebit a f

namespace SCSpec

theorem conforms : Conforms candidateSpec challengeAuthorize := by
  constructor
  · intro b a f
    rw [auth_eq]
    show _ ↔ totalDebit a f ≤ b.toNat
    rw [← qT_eq, ← UInt64.le_iff_toNat_le]
    by_cases h : qT a f ≤ b <;> simp [h]
  · intro b a f t h
    rw [auth_eq] at h
    show t.toNat = totalDebit a f
    by_cases hq : qT a f ≤ b
    · rw [if_pos hq] at h
      cases h
      exact qT_eq a f
    · rw [if_neg hq] at h
      cases h

end SCSpec
