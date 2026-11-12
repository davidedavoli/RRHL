import Xhl.Examples.DPSGD.Shared.ReleasePrograms
import Xhl.Examples.DPSGD.Shared.Round

/-!
# The sampling block, with its hidden variables local

The block `local b, B, j, g in (Pois_q ; g ← Σ_{i∈B} clip_Γ(∇ℓ(θ, D[i])) ; g̃ ←$ 𝒩(g, v))`
is derived by [Equiv] (fusing it into `fusedLoc`, `Equiv/BlockCEquiv.lean`) and [Local]
(`TDeriv.locs`).  `preR_hidden`/`postR_hidden`: the entry and exit resets of the block are
both `rSt` (i.e. `obsPaper`).
-/

open MeasureTheory ProbabilityTheory Continuous
open scoped NNReal ENNReal

namespace DPSGDPaper

/-! ## The block -/

section Block

variable (N dx d : ℕ)
  (grad : EuclideanSpace ℝ (Fin dx) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
  (C : ℝ≥0)
  (v : ℝ≥0) (q : ℝ≥0)

/-- The resets on entry are the reset `obsPaper`. -/
lemma preR_hidden : preR (M := PMem) (hidden N d) = rSt N d := rfl

/-- The resets on exit are the reset `obsPaper`. -/
lemma postR_hidden : postR (M := PMem) (hidden N d) = rSt N d := by
  funext s
  show (PMem.set (PMem.set (PMem.set (PMem.set s.1 (.vec d) (gV d).name 0) .nat jv.name 0)
      (.finset (N + 1)) (bchV N).name ∅) .bool bv.name false, s.2)
    = (PMem.set (PMem.set (PMem.set (PMem.set s.1 .bool bv.name false) (.finset (N + 1))
      (bchV N).name ∅) .nat jv.name 0) (.vec d) (gV d).name 0, s.2)
  congr 1
  rw [MemType.set_set_comm (M := PMem) (.finset (N + 1)) .bool
      (PMem.set (PMem.set s.1 (.vec d) (gV d).name 0) .nat jv.name 0) (bchV N).name bv.name
      (by slot_ne) ∅ false,
    MemType.set_set_comm (M := PMem) .nat .bool (PMem.set s.1 (.vec d) (gV d).name 0) jv.name
      bv.name (by slot_ne) 0 false,
    MemType.set_set_comm (M := PMem) (.vec d) .bool s.1 (gV d).name bv.name (by slot_ne) 0 false,
    MemType.set_set_comm (M := PMem) (.vec d) .nat (PMem.set s.1 .bool bv.name false) (gV d).name
      jv.name (by slot_ne) 0 0,
    MemType.set_set_comm (M := PMem) (.vec d) (.finset (N + 1))
      (PMem.set (PMem.set s.1 .bool bv.name false) .nat jv.name 0) (gV d).name (bchV N).name
      (by slot_ne) 0 ∅,
    MemType.set_set_comm (M := PMem) .nat (.finset (N + 1)) (PMem.set s.1 .bool bv.name false)
      jv.name (bchV N).name (by slot_ne) 0 ∅]

/-- The block after the fusion. -/
noncomputable def fusedLoc (hm : MeasOK dx d grad) : Cmd String PMem :=
  locs (hidden N d) (Cmd.random (gtV d) (fusedK N dx d grad C v q hm))

end Block

end DPSGDPaper
