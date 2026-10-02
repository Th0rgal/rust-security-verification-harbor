by
  unfold repairedAuthorize at h
  split at h
  · rename_i accepted
    simp only [Option.some.injEq] at h
    obtain ⟨_, within_balance⟩ := accepted
    omega
  · simp at h
