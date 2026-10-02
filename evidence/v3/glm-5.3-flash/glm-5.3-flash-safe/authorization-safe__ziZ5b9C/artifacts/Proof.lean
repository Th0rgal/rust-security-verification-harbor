by
  constructor
  · intro b a f
    have hb : b.toNat < 2 ^ 64 := b.toNat_lt_size
    have hsize : UInt64.size = 2 ^ 64 := rfl
    simp [challengeAuthorize, candidateSpec, hsize]
    omega
  · intro b a f total h
    simp only [challengeAuthorize] at h
    split at h
    · rename_i hcond
      refine ⟨hcond.2, ?_⟩
      cases h
      simpa using hcond.1
    · exact absurd h (by simp)
