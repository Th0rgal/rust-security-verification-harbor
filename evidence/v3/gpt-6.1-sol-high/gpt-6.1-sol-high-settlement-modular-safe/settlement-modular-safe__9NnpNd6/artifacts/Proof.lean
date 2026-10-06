by
  change Conforms candidateSpec challengeAuthorize
  constructor
  · intro b a f
    change (∃ t, challengeAuthorize b a f = some t) ↔ settlementDebit a f ≤ b.toNat
    constructor
    · rintro ⟨t, ht⟩
      exact ((authorize_iff b a f t).mp ht).1
    · intro haff
      have hb := b.toNat_lt
      have hbound : settlementDebit a f < UInt64.size := by
        exact Nat.lt_of_le_of_lt haff hb
      refine ⟨UInt64.ofNat (settlementDebit a f), ?_⟩
      apply (authorize_iff b a f _).mpr
      exact ⟨haff, UInt64.toNat_ofNat_of_lt' hbound⟩
  · intro b a f t ht
    exact (authorize_iff b a f t).mp ht
