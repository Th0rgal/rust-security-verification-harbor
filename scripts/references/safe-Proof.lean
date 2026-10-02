by
  change Conforms candidateSpec challengeAuthorize
  constructor
  · intro b a f
    change (∃ total, (if a.toNat + f.toNat < 2^64 ∧ a.toNat + f.toNat ≤ b.toNat then some (UInt64.ofNat (a.toNat + f.toNat)) else none) = some total) ↔ a.toNat + f.toNat ≤ b.toNat
    have bound := b.toNat_lt_size
    by_cases allowed : a.toNat + f.toNat < 2^64 ∧ a.toNat + f.toNat ≤ b.toNat
    · simp only [if_pos allowed]
      constructor
      · intro _; exact allowed.2
      · intro _; exact ⟨_, rfl⟩
    · simp only [if_neg allowed]
      constructor
      · rintro ⟨t, ht⟩; cases ht
      · intro h
        exact False.elim (allowed ⟨Nat.lt_of_le_of_lt h bound, h⟩)
  · intro b a f total h
    change (if a.toNat + f.toNat < 2^64 ∧ a.toNat + f.toNat ≤ b.toNat then some (UInt64.ofNat (a.toNat + f.toNat)) else none) = some total at h
    by_cases allowed : a.toNat + f.toNat < 2^64 ∧ a.toNat + f.toNat ≤ b.toNat
    · simp only [if_pos allowed, Option.some.injEq] at h
      subst total
      exact UInt64.toNat_ofNat_of_lt' allowed.1
    · simp only [if_neg allowed] at h
      cases h
