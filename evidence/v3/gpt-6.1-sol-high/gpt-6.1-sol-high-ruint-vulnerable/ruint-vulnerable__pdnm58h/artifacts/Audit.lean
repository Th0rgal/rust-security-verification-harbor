import SecurityChallenge
open SecurityChallenge

-- The reciprocal routine can underestimate the quotient by one.
def verdict : AuditVerdict := .vulnerable
