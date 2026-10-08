by
  intro h
  have h1 : challengeAuthorize 1744830467 1744830467 0 = some 1744830467 := by decide
  have h2 := (h.1 1744830467 1744830467 0).mp ⟨_, h1⟩
  change specTotal 1744830467 0 ≤ (1744830467 : UInt64).toNat at h2
  exact absurd h2 (by decide)
