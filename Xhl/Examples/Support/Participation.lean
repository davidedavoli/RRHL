import Xhl.Language.Semantics

open Continuous

/-!
# The per-pattern norm of a matrix-mechanism encoder

`patNormSq C pat = ‖C·u(pat)‖² = ∑_j (∑_{t ∈ pat} C_{j,t})²`, with `u(pat)` the indicator of
the participation pattern `pat`: the multi-epoch sensitivity of Choquette-Choo et al.  For `0/1`
participation on `pat` and `CᵀC ≥ 0` entrywise it equals `sens_j/Γ²` (`sensSq_eq_patNormSq`,
`DPFTRLMatrix/Potential.lean`).
-/

open Finset MeasureTheory ProbabilityTheory ENNReal Real
open scoped NNReal ENNReal

namespace Continuous

variable {T : ℕ} {ι : Type} [Fintype ι]

/-- `‖C u(pat)‖² = ∑_j (∑_{t∈pat} C_{j,t})²`, the published per-pattern sensitivity. -/
def patNormSq (C : ι → Fin T → ℝ) (pat : Finset (Fin T)) : ℝ := ∑ j, (∑ t ∈ pat, C j t) ^ 2

end Continuous
