fun h => by
  have hacc : (∃ total, challengeAuthorize 1660206966633859 0 18446744073709541617 = some total) :=
    ⟨1660206966633859, by decide⟩
  have h1 := (h.1 1660206966633859 0 18446744073709541617).mp hacc
  have h2 : ¬ (specTotal 0 18446744073709541617 ≤ (1660206966633859 : UInt64).toNat) := by
    decide
  exact h2 h1
