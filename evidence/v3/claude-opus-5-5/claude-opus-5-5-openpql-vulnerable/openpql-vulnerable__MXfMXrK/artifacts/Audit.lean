import SecurityChallenge
open SecurityChallenge

/- fee = u64::MAX makes space_size = 65536^4 wrap to 0, zeroing the index. -/
def verdict : SecurityChallenge.AuditVerdict := .vulnerable
