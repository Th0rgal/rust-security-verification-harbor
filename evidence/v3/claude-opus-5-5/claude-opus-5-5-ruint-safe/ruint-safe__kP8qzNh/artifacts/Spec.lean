import SecurityChallenge
open SecurityChallenge

def debitNat (amount fee : UInt64) : Nat :=
  amount.toNat / 2 + ((fee.toNat % 32771) * 65536 + amount.toNat % 65536) / 32771

def candidateSpec : SecurityChallenge.AuthorizationSpec where
  accepts := fun balance amount fee => debitNat amount fee ≤ balance.toNat
  output := fun _balance amount fee totalDebit => totalDebit.toNat = debitNat amount fee

namespace SpecAux

theorem land_65535 (x : Nat) : x &&& 65535 = x % 65536 := by
  have h : (65535 : Nat) = 2^16 - 1 := rfl
  rw [h, Nat.and_two_pow_sub_one_eq_mod]

theorem mask_toNat (x : UInt64) : (x &&& limbMask).toNat = x.toNat % 65536 := by
  rw [UInt64.toNat_and]
  have h : limbMask.toNat = 65535 := rfl
  rw [h, land_65535]

theorem nat_core (a b : Nat) (ha : a < 32771) (hb : b < 65536) :
    (let qf := 131060*a + b + 65536
     let q1 := qf / 65536
     let q0 := qf % 65536
     let r := (3221225472 + b - q1*32771) % 65536
     let qc := if q0 < r then q1 - 1 else q1
     let rc := if q0 < r then (r + 32771) % 65536 else r
     if 32771 ≤ rc then qc + 1 else qc) = (a*65536 + b) / 32771 := by
  dsimp only
  generalize hQ : (a*65536 + b) / 32771 = q
  generalize hq1 : (131060 * a + b + 65536) / 65536 = q1
  have hq0 : (131060 * a + b + 65536) % 65536 = 131060*a + b + 65536 - 65536*q1 := by omega
  rw [hq0]
  have hQ1 : q*32771 ≤ a*65536+b ∧ a*65536+b < q*32771+32771 := by omega
  have hB1 : 65536*q1 ≤ 131060*a+b+65536 ∧ 131060*a+b+65536 < 65536*q1 + 65536 := by omega
  clear hQ hq1 hq0
  by_cases ht : q1*32771 ≤ a*65536 + b
  · have hr : (3221225472 + b - q1*32771) % 65536 = a*65536 + b - q1*32771 := by omega
    rw [hr]
    by_cases hc : 131060*a + b + 65536 - 65536*q1 < a*65536 + b - q1*32771
    · simp only [if_pos hc]
      have hrc : (a*65536 + b - q1*32771 + 32771) % 65536 = a*65536 + b - q1*32771 + 32771 := by omega
      rw [hrc]
      split <;> omega
    · simp only [if_neg hc]
      split <;> omega
  · have hr : (3221225472 + b - q1*32771) % 65536 = a*65536 + b + 65536 - q1*32771 := by omega
    rw [hr]
    have hc : 131060*a + b + 65536 - 65536*q1 < a*65536 + b + 65536 - q1*32771 := by omega
    simp only [if_pos hc]
    have hrc : (a*65536 + b + 65536 - q1*32771 + 32771) % 65536 = a*65536 + b + 32771 - q1*32771 := by omega
    rw [hrc]
    split <;> omega

theorem div_correct (u1 u0 : UInt64) (h1 : u1.toNat < 32771) (h0 : u0.toNat < 65536) :
    (div2x1Mg10 u1 u0).toNat = (u1.toNat * 65536 + u0.toNat) / 32771 := by
  have hD : mg10Divisor.toNat = 32771 := rfl
  have hqf : ((u1 * mg10Reciprocal) + (u1 <<< 16) + u0 + ((1 : UInt64) <<< 16)).toNat = 131060 * u1.toNat + u0.toNat + 65536 := by
    simp [mg10Reciprocal, UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_shiftLeft, Nat.shiftLeft_eq]
    omega
  have hN := nat_core u1.toNat u0.toNat h1 h0
  dsimp only at hN
  rw [← hN]
  unfold div2x1Mg10
  dsimp only
  generalize ((u1 * mg10Reciprocal) + (u1 <<< 16) + u0 + ((1 : UInt64) <<< 16)) = X at hqf ⊢
  rw [← hqf]
  have hq1 : (X >>> 16).toNat = X.toNat / 65536 := by
    simp [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
  have hq0 := mask_toNat X
  rw [← hq1, ← hq0]
  generalize X >>> 16 = Q1 at hq1 ⊢
  generalize X &&& limbMask = Q0 at hq0 ⊢
  have hQ1b : Q1.toNat ≤ 65536 := by omega
  have hm : (Q1 * mg10Divisor).toNat = Q1.toNat * 32771 := by
    rw [UInt64.toNat_mul, hD]; omega
  have hs : (subBias + u0).toNat = 3221225472 + u0.toNat := by
    rw [UInt64.toNat_add]; have : subBias.toNat = 3221225472 := rfl
    rw [this]; omega
  have hsub : (subBias + u0 - Q1 * mg10Divisor).toNat = 3221225472 + u0.toNat - Q1.toNat * 32771 := by
    rw [UInt64.toNat_sub, hs, hm]; omega
  have hr := mask_toNat (subBias + u0 - Q1 * mg10Divisor)
  rw [hsub] at hr
  rw [← hr]
  generalize (subBias + u0 - Q1 * mg10Divisor &&& limbMask) = R at hr ⊢
  have hRb : R.toNat < 65536 := by omega
  by_cases hc : Q0 < R
  · have hcN : Q0.toNat < R.toNat := UInt64.lt_iff_toNat_lt.mp hc
    simp only [if_pos hc, if_pos hcN]
    have hrc := mask_toNat (R + mg10Divisor)
    have hadd : (R + mg10Divisor).toNat = R.toNat + 32771 := by
      rw [UInt64.toNat_add, hD]; omega
    rw [hadd] at hrc
    rw [← hrc]
    have hq1m : (Q1 - 1).toNat = Q1.toNat - 1 := by
      rw [UInt64.toNat_sub]; have : (1:UInt64).toNat = 1 := rfl
      rw [this]; omega
    by_cases ho : mg10Divisor ≤ (R + mg10Divisor &&& limbMask)
    · have hoN := UInt64.le_iff_toNat_le.mp ho
      rw [hD] at hoN
      simp only [if_pos ho, if_pos hoN]
      rw [UInt64.toNat_add, hq1m]; have : (1:UInt64).toNat = 1 := rfl
      rw [this]; omega
    · have hoN : ¬ (32771 ≤ (R + mg10Divisor &&& limbMask).toNat) := fun h => ho (UInt64.le_iff_toNat_le.mpr (by rw [hD]; exact h))
      simp only [if_neg ho, if_neg hoN]
      exact hq1m
  · have hcN : ¬ (Q0.toNat < R.toNat) := fun h => hc (UInt64.lt_iff_toNat_lt.mpr h)
    simp only [if_neg hc, if_neg hcN]
    by_cases ho : mg10Divisor ≤ R
    · have hoN := UInt64.le_iff_toNat_le.mp ho
      rw [hD] at hoN
      simp only [if_pos ho, if_pos hoN]
      rw [UInt64.toNat_add]; have : (1:UInt64).toNat = 1 := rfl
      rw [this]; omega
    · have hoN : ¬ (32771 ≤ R.toNat) := fun h => ho (UInt64.le_iff_toNat_le.mpr (by rw [hD]; exact h))
      simp only [if_neg ho, if_neg hoN]

theorem total_toNat (a f : UInt64) :
    ((a >>> 1) + div2x1Mg10 (f % mg10Divisor) (a &&& limbMask)).toNat = debitNat a f := by
  have hu1 : (f % mg10Divisor).toNat = f.toNat % 32771 := by
    rw [UInt64.toNat_mod]; rfl
  have hu0 := mask_toNat a
  have h1 : (f % mg10Divisor).toNat < 32771 := by rw [hu1]; omega
  have h0 : (a &&& limbMask).toNat < 65536 := by rw [hu0]; omega
  have hq := div_correct _ _ h1 h0
  have hsh : (a >>> 1).toNat = a.toNat / 2 := by
    simp [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
  have ha : a.toNat < 18446744073709551616 := a.toNat_lt
  rw [UInt64.toNat_add, hq, hu1, hu0, hsh]
  unfold debitNat
  omega

theorem auth_eq (b a f : UInt64) :
    challengeAuthorize b a f =
      if debitNat a f ≤ b.toNat then some ((a >>> 1) + div2x1Mg10 (f % mg10Divisor) (a &&& limbMask)) else none := by
  simp only [challengeAuthorize, buildQuote, verifyAffordability]
  by_cases h : debitNat a f ≤ b.toNat
  · have h' : (a >>> 1) + div2x1Mg10 (f % mg10Divisor) (a &&& limbMask) ≤ b := by
      rw [UInt64.le_iff_toNat_le, total_toNat]; exact h
    rw [if_pos h', if_pos h]
  · have h' : ¬ ((a >>> 1) + div2x1Mg10 (f % mg10Divisor) (a &&& limbMask) ≤ b) := by
      rw [UInt64.le_iff_toNat_le, total_toNat]; exact h
    rw [if_neg h', if_neg h]

theorem conforms_thm : Conforms candidateSpec challengeAuthorize := by
  refine ⟨fun b a f => ?_, fun b a f t => ?_⟩
  · show (∃ t, challengeAuthorize b a f = some t) ↔ debitNat a f ≤ b.toNat
    rw [auth_eq]
    by_cases h : debitNat a f ≤ b.toNat
    · rw [if_pos h]; exact ⟨fun _ => h, fun _ => ⟨_, rfl⟩⟩
    · rw [if_neg h]; exact ⟨fun ⟨_, ht⟩ => (by cases ht), fun hh => absurd hh h⟩
  · show challengeAuthorize b a f = some t → t.toNat = debitNat a f
    rw [auth_eq]
    by_cases h : debitNat a f ≤ b.toNat
    · rw [if_pos h]; intro ht; injection ht with ht; rw [← ht]; exact total_toNat a f
    · rw [if_neg h]; intro ht; cases ht

end SpecAux
