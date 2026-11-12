import Lake
open Lake DSL

package xhl

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.33.1"

lean_lib Xhl where
  globs := #[.submodules `Xhl]

lean_lib XhlLogic where
  globs := #[.submodules `Xhl.Measures, .submodules `Xhl.Language,
    .submodules `Xhl.Divergence, .submodules `Xhl.Logic]

lean_lib XhlExamples where
  globs := #[.submodules `Xhl.Examples]


