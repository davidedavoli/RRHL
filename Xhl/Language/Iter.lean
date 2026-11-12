import Xhl.Language.Semantics

open Continuous

/-!
# Counted iteration of a command

`iterCmd c n` is `c` sequenced with itself `n` times: the loop-free form of a `while`
with a known iteration count (`osemA_while_eq_iterCmd`, `Logic/Equiv/Unroll.lean`).
-/

open MeasureTheory

variable {ident : Type} {M : MemType ident}

namespace Continuous

/-- `n`-fold sequential repetition of a command. -/
def iterCmd (c : Cmd ident M) : ℕ → Cmd ident M
  | 0 => Cmd.skip
  | n + 1 => Cmd.seq c (iterCmd c n)

end Continuous
