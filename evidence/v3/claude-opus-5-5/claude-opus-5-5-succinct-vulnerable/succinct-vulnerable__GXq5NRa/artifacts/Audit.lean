import SecurityChallenge
open SecurityChallenge

-- u_nz8 omits the `| x` term of Vigna's indicator, so a byte equal to 0x80
-- is treated as zero: fee = 0x80 yields debit 128 instead of 384.
def verdict : SecurityChallenge.AuditVerdict := .vulnerable
