import SecurityChallenge
open SecurityChallenge

-- Intended policy (from the documented contract of `authorize`), in exact integer arithmetic:
--   P = 2013265921, R = 2^32, R_INV = 943718400 (R * R_INV = 1 mod P)
--   transcript      = (amount mod 2^32) + (fee mod P) * 2^32
--   monty_surcharge = (transcript * R_INV) mod P
--   total_debit     = amount + monty_surcharge          (exact, unbounded)
-- The payment is authorized iff total_debit <= balance, and the reported debit is exactly
-- total_debit.

-- Documented Montgomery surcharge, computed in exact Nat arithmetic.
def surcharge (a f : UInt64) : Nat :=
  ((a.toNat % 4294967296 + (f.toNat % 2013265921) * 4294967296) * 943718400) % 2013265921

def candidateSpec : AuthorizationSpec where
  accepts b a f := a.toNat + surcharge a f ≤ b.toNat
  output b a f total := total.toNat = a.toNat + surcharge a f

theorem surcharge_lt (a f : UInt64) : surcharge a f < 2013265921 := Nat.mod_lt _ (by decide)

theorem tq (x : UInt64) : (montyQuotient x).toNat = 2281701377 * (x.toNat % 4294967296) % 4294967296 := by
  unfold montyQuotient babyBearMu limbBase
  simp only [UInt64.toNat_mod, UInt64.toNat_mul]
  simp

theorem tp (a f : UInt64) : (packTranscript a f).toNat = a.toNat % 4294967296 + (f.toNat % 2013265921) * 4294967296 := by
  have ha := a.toNat_lt
  have hf := f.toNat_lt
  simp only [packTranscript, limbBase, babyBearP, UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_mod]
  simp
  omega

theorem modP (Y q K : Nat) (h : Y = q + 2013265921 * K) (hq : q < 2013265921) : Y % 2013265921 = q := by
  subst h; rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hq]

theorem modP2 (Y m K : Nat) (h : Y + m = 2013265921 * K) (h0 : 0 < m) (h1 : m < 2013265921) :
    Y % 2013265921 = 2013265921 - m := by
  have hY : Y = (2013265921 - m) + 2013265921 * (K - 1) := by omega
  exact modP _ _ _ hY (by omega)

theorem keyAB (X T lo h s : Nat) (e1 : X = lo + 4294967296 * h)
    (e2 : 2281701377 * lo = 4294967296 * s + T) :
    X + 4294967296 * (1069547521 * lo) = 2013265921 * T + 4294967296 * (2013265921 * s + h) := by
  omega

theorem borrowM (X T A B : Nat) (hAB : X + 4294967296 * A = 2013265921 * T + 4294967296 * B)
    (hc : X < 2013265921 * T) : X + 4294967296 * (A - B) = 2013265921 * T := by omega

theorem nbQ (X T A B : Nat) (hAB : X + 4294967296 * A = 2013265921 * T + 4294967296 * B)
    (hc : 2013265921 * T ≤ X) : X = 2013265921 * T + 4294967296 * (B - A) := by omega

theorem borrowRes (X T m : Nat) (h : X + 4294967296 * m = 2013265921 * T) (hc : X < 2013265921 * T)
    (hT : T < 4294967296) :
    (18446744073709551616 - 2013265921 * T + X) % 18446744073709551616 = 18446744073709551616 - 4294967296 * m ∧
    0 < m ∧ m < 2013265921 ∧ X * 943718400 % 2013265921 = 2013265921 - m := by
  have hm0 : 0 < m := by omega
  have hmP : m < 2013265921 := by omega
  have hK : X * 943718400 + 2013265921 * (2013265919 * m) + m = 2013265921 * (943718400 * T) := by omega
  have hr : (X * 943718400 + 2013265921 * (2013265919 * m)) % 2013265921 = 2013265921 - m := modP2 _ _ _ hK hm0 hmP
  rw [Nat.add_mul_mod_self_left] at hr
  have hd : (18446744073709551616 - 2013265921 * T + X) % 18446744073709551616 = 18446744073709551616 - 4294967296 * m := by omega
  exact ⟨hd, hm0, hmP, hr⟩

theorem nbRes (X T q : Nat) (h : X = 2013265921 * T + 4294967296 * q) (hX : X < 2013265921 * 4294967296) :
    (18446744073709551616 - 2013265921 * T + X) % 18446744073709551616 = 4294967296 * q ∧
    q < 2013265921 ∧ X * 943718400 % 2013265921 = q := by
  have hqP : q < 2013265921 := by omega
  have hK : X * 943718400 = q + 2013265921 * (943718400 * T + 2013265919 * q) := by omega
  have hd : (18446744073709551616 - 2013265921 * T + X) % 18446744073709551616 = 4294967296 * q := by omega
  exact ⟨hd, hqP, modP _ _ _ hK hqP⟩

-- Montgomery reduction is correct (canonical, exact) on its documented domain `x < P * 2^32`.
theorem mr (x : UInt64) (hx : x.toNat < 2013265921 * 4294967296) :
    (montyReduce x).toNat = x.toNat * 943718400 % 2013265921 := by
  unfold montyReduce
  have h1 := tq x
  generalize montyQuotient x = t at *
  dsimp only
  have htl : t.toNat < 4294967296 := by omega
  have hPT : 2013265921 * t.toNat % 18446744073709551616 = 2013265921 * t.toNat := Nat.mod_eq_of_lt (by omega)
  have hAB := keyAB x.toNat t.toNat (x.toNat % 4294967296) (x.toNat / 4294967296) (2281701377 * (x.toNat % 4294967296) / 4294967296) (by omega) (by omega)
  generalize 1069547521 * (x.toNat % 4294967296) = A at hAB
  generalize 2013265921 * (2281701377 * (x.toNat % 4294967296) / 4294967296) + x.toNat / 4294967296 = B at hAB
  clear h1
  split <;> rename_i hc <;>
    simp only [babyBearP, limbBase, UInt64.lt_iff_toNat_lt, UInt64.toNat_sub, UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_div, UInt64.toNat_ofNat] at hc ⊢ <;>
    simp at hc ⊢ <;> rw [hPT] at hc ⊢
  · obtain ⟨hd, hm0, hmP, hr⟩ := borrowRes _ _ _ (borrowM _ _ _ _ hAB hc) hc htl
    rw [hd, hr]
    generalize A - B = m at *
    clear hAB hd hr hPT hx hc htl
    omega
  · obtain ⟨hd, hqP, hr⟩ := nbRes _ _ _ (nbQ _ _ _ _ hAB hc) hx
    rw [hd, hr]
    generalize B - A = q at *
    clear hAB hd hr hPT hx hc htl
    omega

theorem auth_iff (b a f t : UInt64) : challengeAuthorize b a f = some t ↔
    (a.toNat + surcharge a f ≤ b.toNat ∧ t.toNat = a.toNat + surcharge a f) := by
  have hx : (packTranscript a f).toNat < 2013265921 * 4294967296 := by
    rw [tp]; have := f.toNat_lt; omega
  have hm := mr _ hx
  rw [tp] at hm
  have hs := surcharge_lt a f
  unfold surcharge at *
  unfold challengeAuthorize buildQuote verifyAffordability
  try dsimp only
  generalize montyReduce (packTranscript a f) = s at *
  generalize ((a.toNat % 4294967296 + (f.toNat % 2013265921) * 4294967296) * 943718400) % 2013265921 = S at *
  subst hm
  have ha := a.toNat_lt
  have hb := b.toNat_lt
  have ht := t.toNat_lt
  by_cases h1 : s ≤ u64Max - a
  · rw [if_pos h1]
    try dsimp only
    have h1' := h1
    simp only [UInt64.le_iff_toNat_le, UInt64.toNat_sub, u64Max] at h1'
    simp at h1'
    have hsum : (a + s).toNat = a.toNat + s.toNat := by simp; omega
    by_cases h2 : a + s ≤ b
    · rw [if_pos h2]
      rw [UInt64.le_iff_toNat_le, hsum] at h2
      simp only [Option.some.injEq]
      constructor
      · intro h; subst h; omega
      · intro h; apply UInt64.toNat_inj.mp; omega
    · rw [if_neg h2]
      rw [UInt64.le_iff_toNat_le, hsum] at h2
      simp; omega
  · rw [if_neg h1]
    simp only [UInt64.le_iff_toNat_le, UInt64.toNat_sub, u64Max] at h1
    simp at h1
    simp
    omega

theorem candidateSpec_conforms : Conforms candidateSpec challengeAuthorize := by
  refine ⟨fun b a f => ⟨?_, ?_⟩, fun b a f t h => ((auth_iff b a f t).mp h).2⟩
  · rintro ⟨t, h⟩; exact ((auth_iff b a f t).mp h).1
  · intro h
    change a.toNat + surcharge a f ≤ b.toNat at h
    have hb := b.toNat_lt
    have hn : a.toNat + surcharge a f < 2 ^ 64 := by omega
    refine ⟨UInt64.ofNat (a.toNat + surcharge a f), (auth_iff _ _ _ _).mpr ⟨h, ?_⟩⟩
    first
      | exact UInt64.toNat_ofNat_of_lt' hn
      | (simp <;> omega)
      | (rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt hn)
      | simp [Nat.mod_eq_of_lt hn]
