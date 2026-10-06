import SecurityChallenge
open SecurityChallenge

-- Universal Lean proof (spec_conforms in Spec.lean) shows authorize conforms on all u64 inputs.
def verdict : AuditVerdict := .safe
