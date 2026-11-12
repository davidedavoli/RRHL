import Xhl.Divergence.GaussianPiEuclidean
import Xhl.Language.Semantics

open Continuous

/-!
# The isotropic ℝ^d Gaussian mechanism

The Gaussian sampling kernel `gaussKernelE` (mean map `heap → ℝ^d`, noise `σ²I`), its
centred instance `noiseKernelE`, and the translation identity `gaussE_map_add_const`.  This
is the only Gaussian primitive of the language; the scalar case is `d = 1`.
-/

open MeasureTheory ProbabilityTheory ENNReal Real
open scoped NNReal

variable {ident : Type} {M : MemType ident} {d : ℕ}

namespace Continuous

/-- The **isotropic ℝ^d Gaussian mechanism kernel** (noise `σ²I`): sample the new vector from
    `𝒩(g m, σ²I_d)`.  Measurable via `gaussE_measurable`. -/
noncomputable def gaussKernelE (g : M.heap → EuclideanSpace ℝ (Fin d)) (hg : Measurable g)
    (σ2 : ℝ≥0) :
    @ProbabilityTheory.Kernel M.heap (EuclideanSpace ℝ (Fin d)) M.heapMeas
      (Ty.measurableSpace (.vec d)) where
  toFun m := gaussE (g m) σ2
  measurable' := gaussE_measurable.comp hg

@[simp] lemma gaussKernelE_apply (g : M.heap → EuclideanSpace ℝ (Fin d)) (hg : Measurable g)
    (σ2 : ℝ≥0) (m : M.heap) : gaussKernelE g hg σ2 m = gaussE (g m) σ2 := rfl

instance (g : M.heap → EuclideanSpace ℝ (Fin d)) (hg : Measurable g) (σ2 : ℝ≥0) :
    IsMarkovKernel (gaussKernelE g hg σ2) :=
  ⟨fun _ => by rw [gaussKernelE_apply]; infer_instance⟩

/-- Translating an isotropic Gaussian shifts its mean. -/
lemma gaussE_map_add_const {σ2 : ℝ≥0} (μ y : EuclideanSpace ℝ (Fin d)) :
    (gaussE μ σ2).map (fun w => w + y) = gaussE (μ + y) σ2 := by
  rw [← gaussE_noise (σ2 := σ2) μ, ← gaussE_noise (σ2 := σ2) (μ + y),
    Measure.map_map (measurable_add_const y) (measurable_const_add μ)]
  congr 1
  funext z
  simp only [Function.comp_apply]
  abel

/-- The centred isotropic Gaussian noise kernel `𝒩(0, σ²I_d)`. -/
noncomputable def noiseKernelE (σ2 : ℝ≥0) :
    @ProbabilityTheory.Kernel M.heap (EuclideanSpace ℝ (Fin d)) M.heapMeas
      (Ty.measurableSpace (.vec d)) :=
  gaussKernelE (fun _ => (0 : EuclideanSpace ℝ (Fin d))) measurable_const σ2

instance (σ2 : ℝ≥0) : IsMarkovKernel (noiseKernelE (M := M) (d := d) σ2) := by
  unfold noiseKernelE; infer_instance

end Continuous
