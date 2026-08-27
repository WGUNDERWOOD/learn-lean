import Lake
open Lake DSL

require "leanprover-community" / "mathlib4" @ git "v4.29.1"

package LearnLean

@[default_target]
lean_lib LearnLean where
  globs := #[.submodules `LearnLean]
