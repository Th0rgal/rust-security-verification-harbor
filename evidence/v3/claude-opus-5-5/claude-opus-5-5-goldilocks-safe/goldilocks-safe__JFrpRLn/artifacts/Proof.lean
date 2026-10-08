by
  show Conforms candidateSpec challengeAuthorize
  constructor
  · intro b a f
    rw [GoldilocksAudit.authorize_eq]
    by_cases h : GoldilocksAudit.policyTotal a.toNat f.toNat ≤ b.toNat
    · rw [if_pos h]
      exact ⟨fun _ => h, fun _ => ⟨_, rfl⟩⟩
    · rw [if_neg h]
      constructor
      · intro ⟨_, ht⟩
        cases ht
      · intro h'
        exact absurd h' h
  · intro b a f t
    rw [GoldilocksAudit.authorize_eq]
    by_cases h : GoldilocksAudit.policyTotal a.toNat f.toNat ≤ b.toNat
    · rw [if_pos h]
      intro ht
      cases ht
      exact GoldilocksAudit.total_n b a f h
    · rw [if_neg h]
      intro ht
      cases ht
