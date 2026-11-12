import Xhl.Logic.Equiv.Local

open Continuous

/-!
# Blocks with several local variables

`locs xs c` is the block `local x₁, …, xₙ in c`, namely `loc x₁ (… (loc xₙ c))`.

* `preR xs`, `postR xs` — the resets of the variables, in the two orders in which the
  nested blocks apply them.

**[Local]** for such blocks is `TDeriv.locs` (`Xhl/Logic/Rrhl/Deriv.lean`).
-/

open MeasureTheory ProbabilityTheory ENNReal Cmd

variable {ident : Type} {M : MemType ident}

namespace Continuous

/-- A variable of any type. -/
abbrev AVar (ident : Type) := Σ t : Ty, Vars ident t

/-- `local x₁, …, xₙ in c`. -/
noncomputable def locs : List (AVar ident) → Cmd ident M → Cmd ident M
  | [], c => c
  | ⟨_, x⟩ :: xs, c => loc x (locs xs c)

/-- The resets on entry: `x₁` first, `xₙ` last. -/
def preR : List (AVar ident) → St M → St M
  | [] => id
  | ⟨_, x⟩ :: xs => fun s => preR xs (resetV x s)

/-- The resets on exit: `xₙ` first, `x₁` last. -/
def postR : List (AVar ident) → St M → St M
  | [] => id
  | ⟨_, x⟩ :: xs => fun s => resetV x (postR xs s)

end Continuous
