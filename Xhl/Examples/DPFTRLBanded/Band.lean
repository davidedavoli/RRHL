import Xhl.Examples.DPFTRLBanded.Params

open Continuous

/-!
# The banded record step: a Bernoulli coin per eligible record

Record `i` is eligible at round `t` when `elig(i, t)` holds, and an eligible record takes
part with probability `q`, tossing its own coin (the block Pois of Fig. 8):

    while i < n do
      if elig(i, t) then local u in (u ←$ Bern(q) ; acc := acc + u·clip_Γ(∇ℓ(x, D[i])))
      else skip ;
      i := i + 1
    od

This file defines the eligibility test `eligE` and the freshness conditions `UOK` of the
coin variable; the step itself is `recBT` (`Program.lean`), which adds straight into the
history slot `H[t]` instead of `acc`.
-/


open MeasureTheory ProbabilityTheory ENNReal
open scoped NNReal

variable {ident : Type} {M : MemType ident}

namespace DPFTRL.Band

open Continuous

variable {d e n T R : ℕ} {τ : Ty} [NeZero T] [NeZero R]

/-! ## The banded record step -/

section BandProgram

variable (p : TParams d e n T R τ) (v : TVars ident d T R τ) (tv : Vars ident .nat)
  (q : ℝ≥0) (elig : ℕ → ℕ → Bool) (uv : Vars ident .bool) (bw : ℕ)

/-- `elig(i, t)`. -/
def eligE : BExpr M :=
  ⟨fun m => elig (M.get m .nat v.i.name) (M.get m .nat tv.name),
    (measurable_of_countable (fun q : ℕ × ℕ => elig q.1 q.2)).comp
      ((M.get_measurable .nat v.i.name).prodMk (M.get_measurable .nat tv.name))⟩
end BandProgram

variable {p : TParams d e n T R τ} {v : TVars ident d T R τ} {tv rv : Vars ident .nat}
  {q : ℝ≥0} {elig : ℕ → ℕ → Bool} {uv : Vars ident .bool} {bw : ℕ}

/-- The coin is a variable of its own. -/
structure UOK (v : TVars ident d T R τ) (tv rv : Vars ident .nat) (uv : Vars ident .bool) :
    Prop where
  ux : uv.name ≠ v.x.name
  uacc : uv.name ≠ v.acc.name
  uz : uv.name ≠ v.z.name
  ui : uv.name ≠ v.i.name
  uD : uv.name ≠ v.D.name
  uH : uv.name ≠ v.H.name
  uY : uv.name ≠ v.Y.name
  ut : uv.name ≠ tv.name
  ur : uv.name ≠ rv.name

end DPFTRL.Band
