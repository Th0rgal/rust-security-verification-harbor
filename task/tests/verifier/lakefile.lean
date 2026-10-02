import Lake
open Lake DSL

package SecurityVerifier where
  version := v!"1.0.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.31.0"

@[default_target]
lean_lib SecurityChallenge
