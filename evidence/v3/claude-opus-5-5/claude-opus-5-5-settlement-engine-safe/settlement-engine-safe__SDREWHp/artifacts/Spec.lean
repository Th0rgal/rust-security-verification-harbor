import SecurityChallenge
open SecurityChallenge

def specGrossFee (amount fee : UInt64) : Nat :=
  (amount.toNat + fee.toNat + 9999) / 10000
def specRebate (amount fee : UInt64) : Nat :=
  specGrossFee amount fee / 10
def specTotalDebit (amount fee : UInt64) : Nat :=
  amount.toNat + (specGrossFee amount fee - specRebate amount fee)
def candidateSpec : AuthorizationSpec where
  accepts := fun balance amount fee => specTotalDebit amount fee ≤ balance.toNat
  output := fun _balance amount fee totalDebit => totalDebit.toNat = specTotalDebit amount fee

theorem ceilDiv_toNat (a f : UInt64) : (ceilDivBpsU64 (addU64WithCarry a f)).toNat = (a.toNat + f.toNat + 9999) / 10000 := by
  have ha := a.toNat_lt
  have hf := f.toNat_lt
  simp only [ceilDivBpsU64, addU64WithCarry, bpsDenom, bpsMaxRem, u64ModBpsQuot, u64ModBpsRem]
  split <;> (try split) <;> simp_all [UInt64.lt_iff_toNat_lt, UInt64.toNat_add, UInt64.toNat_div, UInt64.toNat_mod] <;> omega

theorem conform_parts (b a f : UInt64) :
    ((∃ t, challengeAuthorize b a f = some t) ↔ specTotalDebit a f ≤ b.toNat) ∧
    (∀ t, challengeAuthorize b a f = some t → t.toNat = specTotalDebit a f) := by
  have hG := ceilDiv_toNat a f
  have ha := a.toNat_lt
  have hb := b.toNat_lt
  simp only [challengeAuthorize, quoteSettlementTicket, evaluateSettlementFee, assembleTicket,
    commitTicket, computeTierRebate, specTotalDebit, specRebate, specGrossFee, rebateDivisor]
  generalize ceilDivBpsU64 (addU64WithCarry a f) = G at hG ⊢
  have hsub : (G - G / 10).toNat = G.toNat - G.toNat / 10 := by
    rw [UInt64.toNat_sub_of_le, UInt64.toNat_div]
    · rfl
    · rw [UInt64.le_iff_toNat_le, UInt64.toNat_div]; exact Nat.div_le_self _ _
  have hm : u64Max.toNat = 18446744073709551615 := rfl
  have hmax : (u64Max - a).toNat = 18446744073709551615 - a.toNat := by
    rw [UInt64.toNat_sub_of_le, hm]
    rw [UInt64.le_iff_toNat_le, hm]; omega
  have hadd : (a + (G - G / 10)).toNat = (a.toNat + (G.toNat - G.toNat / 10)) % 2 ^ 64 := by
    rw [UInt64.toNat_add, hsub]
  rw [← hG]
  by_cases h1 : G - G / 10 ≤ u64Max - a
  · have h1' := UInt64.le_iff_toNat_le.mp h1
    rw [hsub, hmax] at h1'
    have hadd' : (a + (G - G / 10)).toNat = a.toNat + (G.toNat - G.toNat / 10) := by
      rw [hadd]; exact Nat.mod_eq_of_lt (by omega)
    rw [if_pos h1]
    by_cases h2 : a + (G - G / 10) ≤ b
    · have h2' := UInt64.le_iff_toNat_le.mp h2
      rw [hadd'] at h2'
      simp only [if_pos h2]
      refine ⟨⟨fun _ => h2', fun _ => ⟨_, rfl⟩⟩, fun t ht => ?_⟩
      cases ht
      exact hadd'
    · have h2' : ¬ (a + (G - G / 10)).toNat ≤ b.toNat := fun h => h2 (UInt64.le_iff_toNat_le.mpr h)
      rw [hadd'] at h2'
      simp only [if_neg h2]
      refine ⟨⟨fun ⟨t, ht⟩ => (by cases ht), fun h => absurd h h2'⟩, fun t ht => (by cases ht)⟩
  · have h1' : ¬ (G - G / 10).toNat ≤ (u64Max - a).toNat := fun h => h1 (UInt64.le_iff_toNat_le.mpr h)
    rw [hsub, hmax] at h1'
    rw [if_neg h1]
    refine ⟨⟨fun ⟨t, ht⟩ => (by cases ht), fun h => by omega⟩, fun t ht => (by cases ht)⟩

