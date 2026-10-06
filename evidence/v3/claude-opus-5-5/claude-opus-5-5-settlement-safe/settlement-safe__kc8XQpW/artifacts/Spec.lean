import SecurityChallenge
open SecurityChallenge

/-- Intended gross fee: ceil((amount + fee) / 10000), exact over Nat. -/
def specGross (a f : Nat) : Nat := (a + f + 9999) / 10000
/-- Intended net debit: amount + (gross - floor(gross / 10)). -/
def specDebit (a f : Nat) : Nat := a + (specGross a f - specGross a f / 10)

def candidateSpec : SecurityChallenge.AuthorizationSpec where
  accepts := fun b a f => specDebit a.toNat f.toNat ≤ b.toNat
  output := fun _b a f t => t.toNat = specDebit a.toNat f.toNat

namespace CandidateProofs

def gfee (amount fee : UInt64) : UInt64 :=
  let rawSum := amount + fee
  if rawSum < amount then
    let foldedRem := (rawSum % bpsDenom) + u64ModBpsRem
    u64ModBpsQuot + (rawSum / bpsDenom) + ((foldedRem + bpsMaxRem) / bpsDenom)
  else
    let biased := rawSum + bpsMaxRem
    if biased < rawSum then
      (rawSum / bpsDenom) + (((rawSum % bpsDenom) + bpsMaxRem) / bpsDenom)
    else
      biased / bpsDenom

def tailFn (balance amount grossFee : UInt64) : Option UInt64 :=
  let rebate := grossFee / rebateDivisor
  let netFee := grossFee - rebate
  if netFee ≤ u64Max - amount then
    let total := amount + netFee
    if total ≤ balance then some total else none
  else none

theorem model_eq (b a f : UInt64) :
    challengeAuthorize b a f = tailFn b a (gfee a f) := rfl

theorem gfee_toNat (a f : UInt64) :
    (gfee a f).toNat = (a.toNat + f.toNat + 9999) / 10000 := by
  have ha := a.toNat_lt
  have hf := f.toNat_lt
  have hD : bpsDenom.toNat = 10000 := rfl
  have hR : bpsMaxRem.toNat = 9999 := rfl
  have hQ : u64ModBpsQuot.toNat = 1844674407370955 := rfl
  have hM : u64ModBpsRem.toNat = 1616 := rfl
  dsimp only [gfee]
  split
  next h1 =>
    rw [UInt64.lt_iff_toNat_lt] at h1
    simp only [UInt64.toNat_add, UInt64.toNat_div, UInt64.toNat_mod, hD, hR, hQ, hM] at h1 ⊢
    omega
  next h1 =>
    rw [UInt64.lt_iff_toNat_lt] at h1
    split
    next h2 =>
      rw [UInt64.lt_iff_toNat_lt] at h2
      simp only [UInt64.toNat_add, UInt64.toNat_div, UInt64.toNat_mod, hD, hR] at h1 h2 ⊢
      omega
    next h2 =>
      rw [UInt64.lt_iff_toNat_lt] at h2
      simp only [UInt64.toNat_add, UInt64.toNat_div, UInt64.toNat_mod, hD, hR] at h1 h2 ⊢
      omega

theorem tail_iff (b a g t : UInt64) :
    tailFn b a g = some t ↔
      (a.toNat + (g.toNat - g.toNat / 10) ≤ b.toNat ∧
        t.toNat = a.toNat + (g.toNat - g.toNat / 10)) := by
  have ha := a.toNat_lt
  have hb := b.toNat_lt
  have hg := g.toNat_lt
  have ht := t.toNat_lt
  have h10 : (g / rebateDivisor).toNat = g.toNat / 10 := by
    rw [UInt64.toNat_div]; rfl
  have hs : (g - g / rebateDivisor).toNat = g.toNat - g.toNat / 10 := by
    rw [UInt64.toNat_sub, h10]; omega
  have hmx : u64Max.toNat = 18446744073709551615 := rfl
  have hm : (u64Max - a).toNat = 18446744073709551615 - a.toNat := by
    rw [UInt64.toNat_sub, hmx]; omega
  have hsum : (a + (g - g / rebateDivisor)).toNat =
      (a.toNat + (g.toNat - g.toNat / 10)) % 2 ^ 64 := by
    rw [UInt64.toNat_add, hs]
  dsimp only [tailFn]
  split
  next h1 =>
    rw [UInt64.le_iff_toNat_le, hs, hm] at h1
    split
    next h2 =>
      rw [UInt64.le_iff_toNat_le, hsum] at h2
      constructor
      · intro h
        have h' := Option.some.inj h
        subst h'
        exact ⟨by omega, by rw [hsum]; omega⟩
      · intro h
        have key : a + (g - g / rebateDivisor) = t :=
          UInt64.toNat_inj.mp (by rw [hsum]; omega)
        rw [key]
    next h2 =>
      rw [UInt64.le_iff_toNat_le, hsum] at h2
      constructor
      · intro h; cases h
      · intro h; exfalso; omega
  next h1 =>
    rw [UInt64.le_iff_toNat_le, hs, hm] at h1
    constructor
    · intro h; cases h
    · intro h; exfalso; omega

theorem auth_iff (b a f t : UInt64) :
    challengeAuthorize b a f = some t ↔
      (specDebit a.toNat f.toNat ≤ b.toNat ∧ t.toNat = specDebit a.toNat f.toNat) := by
  rw [model_eq, tail_iff, gfee_toNat]
  rfl

theorem conforms : Conforms candidateSpec challengeAuthorize := by
  constructor
  · intro b a f
    show (∃ total, challengeAuthorize b a f = some total) ↔ specDebit a.toNat f.toNat ≤ b.toNat
    constructor
    · rintro ⟨t, h⟩
      exact ((auth_iff b a f t).mp h).1
    · intro h
      have hb := b.toNat_lt
      refine ⟨UInt64.ofNat (specDebit a.toNat f.toNat), (auth_iff _ _ _ _).mpr ⟨h, ?_⟩⟩
      rw [UInt64.toNat_ofNat']
      omega
  · intro b a f t h
    exact ((auth_iff b a f t).mp h).2

end CandidateProofs
