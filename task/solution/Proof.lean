by
  obtain ⟨hTotal, _, hBalance⟩ :=
    (repairedAuthorize_success balance amount fee total).mp h
  subst total
  exact ⟨rfl, hBalance⟩
