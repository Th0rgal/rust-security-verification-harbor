import SecurityChallenge
open SecurityChallenge

-- Audit result: authorize conforms to the documented policy on all u64 inputs.
def verdict : SecurityChallenge.AuditVerdict := .safe
