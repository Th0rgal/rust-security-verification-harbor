import SecurityChallenge

/-- Carry folding and overflow rejection implement the exact settlement policy. -/
def verdict : SecurityChallenge.AuditVerdict := .safe
