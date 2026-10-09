import Lake
open Lake DSL
package SecurityVerifier where
  version := v!"3.0.0"

lean_lib LeanModel where
  globs := #[.submodules `LeanModel]

@[default_target]
lean_lib SecurityChallenge

@[default_target]
lean_lib SpecAudit
