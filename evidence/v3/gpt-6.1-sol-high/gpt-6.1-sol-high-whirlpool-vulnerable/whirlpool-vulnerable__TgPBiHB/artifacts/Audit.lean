import SecurityChallenge
open SecurityChallenge

-- Rounding discards the carry out of the second 32-bit limb.
def verdict : AuditVerdict := .vulnerable
