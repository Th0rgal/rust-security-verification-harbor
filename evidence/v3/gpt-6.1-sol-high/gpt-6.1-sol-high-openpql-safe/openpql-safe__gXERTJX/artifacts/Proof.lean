by
  have component_bound (n k : Nat) : component n k < 65536 := by
    unfold component
    exact Nat.mod_lt _ (by decide)
  have radix_nat (x : UInt64) : ((x % radixBase) + 1).toNat = x.toNat % 65536 + 1 := by
    have h := Nat.mod_lt x.toNat (show 0 < 65536 by decide)
    have hb : x.toNat % 65536 + 1 < 2^64 := by norm_num; omega
    simp only [UInt64.toNat_add, UInt64.toNat_mod, radixBase, UInt64.toNat_ofNat]
    exact Nat.mod_eq_of_lt hb
  have clamp_nat (x y : UInt64) (hy : 0 < y.toNat) :
      (clampDigit x y).toNat = policyDigit x.toNat y.toNat := by
    unfold clampDigit policyDigit
    simp only [UInt64.lt_iff_toNat_lt]
    split
    · rfl
    · rw [UInt64.toNat_sub_of_le]
      · simp
      · change 1 ≤ y.toNat
        omega
  have pack_bound (x p y q : Nat) (hx : x < p) (hy : y < q) : x*q+y < p*q := by
    nlinarith
  have digit_bound (a b : Nat) (hb : 0 < b) : policyDigit a b < b := by
    unfold policyDigit
    split <;> omega
  have index_bound (a f : Nat) : policyIndex a f < 2^64 := by
    let b0 := component f 1 + 1
    let b1 := component f 65536 + 1
    let b2 := component f 4294967296 + 1
    let b3 := component f 281474976710656 + 1
    let d0 := policyDigit (component a 1) b0
    let d1 := policyDigit (component a 65536) b1
    let d2 := policyDigit (component a 4294967296) b2
    let d3 := policyDigit (component a 281474976710656) b3
    have hb0 : b0 ≤ 65536 := by dsimp [b0]; have := component_bound f 1; omega
    have hb1 : b1 ≤ 65536 := by dsimp [b1]; have := component_bound f 65536; omega
    have hb2 : b2 ≤ 65536 := by dsimp [b2]; have := component_bound f 4294967296; omega
    have hb3 : b3 ≤ 65536 := by dsimp [b3]; have := component_bound f 281474976710656; omega
    have hd0 : d0 < b0 := digit_bound _ _ (by dsimp [b0]; omega)
    have hd1 : d1 < b1 := digit_bound _ _ (by dsimp [b1]; omega)
    have hd2 : d2 < b2 := digit_bound _ _ (by dsimp [b2]; omega)
    have hd3 : d3 < b3 := digit_bound _ _ (by dsimp [b3]; omega)
    have h01 := pack_bound d0 b0 d1 b1 hd0 hd1
    have h012 := pack_bound _ _ d2 b2 h01 hd2
    have h0123 := pack_bound _ _ d3 b3 h012 hd3
    have hp : b0*b1*b2*b3 ≤ 2^64 := by
      calc
        b0*b1*b2*b3 ≤ 65536*65536*65536*65536 :=
          Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hb0 hb1) hb2) hb3
        _ = 2^64 := by norm_num
    have he : policyIndex a f = ((d0*b1+d1)*b2+d2)*b3+d3 := by
      change d0*(b1*(b2*b3))+d1*(b2*b3)+d2*b3+d3 = _
      ring
    rw [he]
    omega
  have index_nat (a f : UInt64) : (encodeMixedRadix a f).toNat = policyIndex a.toNat f.toNat := by
    have clamp_radix (x y : UInt64) :
        (clampDigit x ((y % radixBase) + 1)).toNat =
          policyDigit x.toNat (y.toNat % 65536 + 1) := by
      rw [clamp_nat, radix_nat]
      rw [radix_nat]
      omega
    have hm : (encodeMixedRadix a f).toNat = policyIndex a.toNat f.toNat % 2^64 := by
      simp only [encodeMixedRadix, UInt64.toNat_add, UInt64.toNat_mul,
        clamp_radix, radix_nat, UInt64.toNat_div, UInt64.toNat_mod]
      simp only [radixBase, shift16, shift32, shift48, UInt64.toNat_ofNat,
        Nat.mod_add_mod, Nat.add_mod_mod, Nat.mul_mod_mod]
      norm_num [policyIndex, component]
    rw [hm, Nat.mod_eq_of_lt (index_bound a.toNat f.toNat)]
  have debit_nat (a f : UInt64) :
      (a / halfDivisor + encodeMixedRadix a f / halfDivisor).toNat = policyDebit a.toNat f.toNat := by
    have ha := a.toNat_lt_size
    have hi := index_bound a.toNat f.toNat
    have hsum : a.toNat / 2 + policyIndex a.toNat f.toNat / 2 < 2^64 := by
      change a.toNat < 2^64 at ha
      omega
    simp only [UInt64.toNat_add, UInt64.toNat_div, halfDivisor, UInt64.toNat_ofNat,
      index_nat, policyDebit]
    exact Nat.mod_eq_of_lt hsum
  change Conforms candidateSpec challengeAuthorize
  constructor
  · intro b a f
    simp [challengeAuthorize, buildQuote, verifyAffordability, candidateSpec,
      UInt64.le_iff_toNat_le, debit_nat]
  · intro b a f total h
    simp only [challengeAuthorize, buildQuote, verifyAffordability] at h
    split at h
    · rename_i affordable
      cases h
      exact ⟨by simpa only [UInt64.le_iff_toNat_le, debit_nat] using affordable, debit_nat a f⟩
    · contradiction
