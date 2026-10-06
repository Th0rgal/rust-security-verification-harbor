by
  change Conforms candidateSpec challengeAuthorize
  have model (b a f : UInt64) : challengeAuthorize b a f =
      (if wordNet a f ≤ u64Max - a then
        if a + wordNet a f ≤ b then some (a + wordNet a f) else none
      else none) := by rfl
  constructor
  · intro b a f
    rw [model]
    change (∃ t, (if wordNet a f ≤ u64Max - a then
      if a + wordNet a f ≤ b then some (a + wordNet a f) else none
      else none) = some t) ↔ policyDebit a f ≤ b.toNat
    by_cases h : wordNet a f ≤ u64Max - a
    · have ht := debit_correct a f h
      simp only [h, if_true]
      simp only [UInt64.le_iff_toNat_le, ht]
      by_cases hb : policyDebit a f ≤ b.toNat <;> simp [hb]
    · have hg : ¬ a.toNat + (wordNet a f).toNat < 18446744073709551616 :=
        fun hn => h ((guard_correct b a f).mpr hn)
      have hn := net_correct a f
      have hb := b.toNat_lt
      have bad : ¬ policyDebit a f ≤ b.toNat := by
        unfold policyDebit
        omega
      simp [h, bad]
  · intro b a f t ht
    rw [model] at ht
    change policyDebit a f ≤ b.toNat ∧ t.toNat = policyDebit a f
    by_cases h : wordNet a f ≤ u64Max - a
    · simp only [h, if_true] at ht
      by_cases hb : a + wordNet a f ≤ b
      · simp only [hb, if_true, Option.some.injEq] at ht
        have hd := debit_correct a f h
        have hbn := UInt64.le_iff_toNat_le.mp hb
        constructor
        · omega
        · rw [← ht, hd]
      · simp [hb] at ht
    · simp [h] at ht
