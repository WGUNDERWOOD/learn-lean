import Lake
open Lake DSL

require aesop from git
  "https://github.com/leanprover-community/aesop.git" @ "v4.29.0"

package LearnLean

@[default_target]
lean_lib LearnLean
