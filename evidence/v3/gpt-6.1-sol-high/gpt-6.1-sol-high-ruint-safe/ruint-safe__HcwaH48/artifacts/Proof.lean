import Mathlib.Tactic.NormNum
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
by
  have maskNat (x : UInt64) : (x &&& (65535 : UInt64)).toNat = x.toNat % 65536 := by
    change (x.toBitVec &&& (65535 : UInt64).toBitVec).toNat = _
    rw [BitVec.toNat_and]
    change x.toNat &&& (2^16 - 1) = _
    rw [Nat.and_two_pow_sub_one_eq_mod]
  have shrNat (x : UInt64) (n : UInt64) :
      (x >>> n).toNat = x.toNat / 2^(n.toNat % 64) := by
    change (x.toBitVec >>> (n.toNat % 64)).toNat = _
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    rfl
  have shlNat (x : UInt64) (n : UInt64) :
      (x <<< n).toNat = (x.toNat * 2^(n.toNat % 64)) % 2^64 := by
    change (x.toBitVec <<< (n.toNat % 64)).toNat = _
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    rfl
  have addExact (x y : UInt64) (h : x.toNat + y.toNat < 2^64) :
      (x+y).toNat = x.toNat + y.toNat := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt h]
  have mulExact (x y : UInt64) (h : x.toNat * y.toNat < 2^64) :
      (x*y).toNat = x.toNat * y.toNat := by
    rw [UInt64.toNat_mul, Nat.mod_eq_of_lt h]
  have divCorrect (u1 u0 : UInt64) (h1 : u1.toNat < 32771) (h0 : u0.toNat < 65536) :
      (div2x1Mg10 u1 u0).toNat = (u1.toNat * 65536 + u0.toNat) / 32771 := by
    let p := u1.toNat * 65524 + u1.toNat * 65536 + u0.toNat + 65536
    let qFull : UInt64 := (u1 * mg10Reciprocal) + (u1 <<< 16) + u0 + ((1 : UInt64) <<< 16)
    have hm : (u1 * mg10Reciprocal).toNat = u1.toNat * 65524 := by
      rw [UInt64.toNat_mul]
      change (u1.toNat * 65524) % 18446744073709551616 = _
      apply Nat.mod_eq_of_lt; omega
    have hs : (u1 <<< 16).toNat = u1.toNat * 65536 := by
      rw [shlNat]
      change (u1.toNat * 65536) % 18446744073709551616 = _
      apply Nat.mod_eq_of_lt; omega
    have hc : ((1 : UInt64) <<< 16).toNat = 65536 := by decide
    have hab : ((u1 * mg10Reciprocal) + (u1 <<< 16)).toNat = u1.toNat * 65524 + u1.toNat * 65536 := by
      rw [addExact _ _ (by rw [hm, hs]; norm_num; omega), hm, hs]
    have habc : ((u1 * mg10Reciprocal) + (u1 <<< 16) + u0).toNat = u1.toNat * 65524 + u1.toNat * 65536 + u0.toNat := by
      rw [addExact _ _ (by rw [hab]; norm_num; omega), hab]
    have hp : qFull.toNat = p := by
      dsimp [qFull]
      rw [addExact _ _ (by rw [habc, hc]; norm_num; omega), habc, hc]
    let q1 := qFull >>> (16 : UInt64)
    have hq1 : q1.toNat = p / 65536 := by
      dsimp [q1]; rw [shrNat, hp]; rfl
    have hqBound : 1 ≤ q1.toNat ∧ q1.toNat ≤ 65535 := by
      rw [hq1]; dsimp [p]; omega
    have hqProd : (q1 * mg10Divisor).toNat = q1.toNat * 32771 := by
      rw [UInt64.toNat_mul]
      change (q1.toNat * 32771) % 18446744073709551616 = _
      apply Nat.mod_eq_of_lt; omega
    have hb : (subBias + u0).toNat = 3221225472 + u0.toNat := by
      rw [UInt64.toNat_add]
      change (3221225472 + u0.toNat) % 18446744073709551616 = _
      apply Nat.mod_eq_of_lt; omega
    have hrSub : (subBias + u0 - q1 * mg10Divisor).toNat = 3221225472 + u0.toNat - q1.toNat * 32771 := by
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, hb, hqProd]; omega), hb, hqProd]
    change (let q0 := qFull &&& limbMask
            let r := (subBias + u0 - q1 * mg10Divisor) &&& limbMask
            let (qc, rc) := if q0 < r then (q1 - 1, (r + mg10Divisor) &&& limbMask) else (q1, r)
            if mg10Divisor ≤ rc then qc + 1 else qc).toNat = _
    dsimp only
    split <;> split
    all_goals simp only [limbMask, maskNat, UInt64.lt_iff_toNat_lt, UInt64.le_iff_toNat_le, hp, hrSub, hq1] at *
    all_goals simp only [UInt64.lt_iff_toNat_lt, UInt64.le_iff_toNat_le,
      UInt64.toNat_add, UInt64.toNat_sub, hp, hq1, hrSub, mg10Divisor,
      UInt64.toNat_ofNat, Nat.reduceMod, Nat.reducePow] at *
    all_goals dsimp [p] at *
    all_goals omega
  exact False.elim (by contradiction)
