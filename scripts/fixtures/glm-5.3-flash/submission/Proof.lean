by
  try intro balance amount fee total h
  try simp_all [authorize]
  first
    | omega
    | cases h <;> omega
    | split at * <;> simp_all [authorize] <;> omega
