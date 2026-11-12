import Xhl.Language.Syntax

open Continuous

/-!
# The Bernoulli sampler

The coin of the Poisson subsampling loops, typed at `Ty.bool` and memory-independent.
`bernoulliMeasure p` is by definition the two-point mixture
`(1 − p) • dirac false + min p 1 • dirac true`, so binds over it unfold to mixtures.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {ident : Type} {M : MemType ident}

namespace Continuous

private instance : MeasurableSpace M.heap := M.heapMeas

end Continuous

namespace Continuous

instance Ty.standardBorel_bool : StandardBorelSpace (Ty.interp .bool) :=
  (inferInstance : StandardBorelSpace Bool)

/-- The Bernoulli measure on `Bool`: `true` with probability `p`, `false` with
probability `1 - p`.  The parameter is read as `min p 1`, so this is a probability
measure for every `p`; for `p ≤ 1` it is the usual Bernoulli (`bernoulliMeasure_of_le`). -/
noncomputable def bernoulliMeasure (p : ℝ≥0) : Measure Bool :=
  (1 - (p : ℝ≥0∞)) • Measure.dirac false + ((min p 1 : ℝ≥0) : ℝ≥0∞) • Measure.dirac true

lemma bernoulliMeasure_of_le {p : ℝ≥0} (hp : p ≤ 1) :
    bernoulliMeasure p = (1 - (p : ℝ≥0∞)) • Measure.dirac false + (p : ℝ≥0∞) • Measure.dirac true := by
  rw [bernoulliMeasure, min_eq_left hp]

instance isProb_bernoulliMeasure (p : ℝ≥0) : IsProbabilityMeasure (bernoulliMeasure p) := by
  constructor
  simp only [bernoulliMeasure, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, measure_univ, mul_one]
  rcases le_total p 1 with hp | hp
  · rw [min_eq_left hp]; exact tsub_add_cancel_of_le (by exact_mod_cast hp)
  · rw [min_eq_right hp, ENNReal.coe_one, tsub_eq_zero_of_le (by exact_mod_cast hp), zero_add]

/-- The Bernoulli(`p`) sampling kernel, memory-independent. -/
noncomputable def bernoulliKernel (p : ℝ≥0) :
    @ProbabilityTheory.Kernel M.heap Bool M.heapMeas (Ty.measurableSpace .bool) :=
  Kernel.const _ (bernoulliMeasure p)

@[simp] lemma bernoulliKernel_apply (p : ℝ≥0) (m : M.heap) :
    bernoulliKernel (M := M) p m = bernoulliMeasure p := rfl

instance isMarkov_bernoulliKernel (p : ℝ≥0) : IsMarkovKernel (bernoulliKernel (M := M) p) := by
  rw [bernoulliKernel]; infer_instance

end Continuous
