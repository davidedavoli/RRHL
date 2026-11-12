import Xhl.Examples.DPFTRLBanded.Band
import Xhl.Divergence.SubsamplingMixBudget

/-!
# Isotropic Gaussians by blocks

`K` independent isotropic Gaussians in dimension `d`, concatenated, form the isotropic Gaussian in
dimension `K·d` whose mean is the concatenation of the means.  The blocks are those of `blk`.
-/

open MeasureTheory ProbabilityTheory ENNReal Set
open scoped NNReal

namespace DPFTRL.Band

open Continuous

variable {K d : ℕ}

/-- The concatenation of `K` vectors of dimension `d`, block `k` being the `k`-th vector. -/
noncomputable def concatE (Z : Fin K → EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin (K * d)) :=
  WithLp.toLp 2 (fun q => Z (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2)

lemma concatE_apply (Z : Fin K → EuclideanSpace ℝ (Fin d)) (q : Fin (K * d)) :
    concatE Z q = Z (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2 := rfl

lemma blk_concatE (Z : Fin K → EuclideanSpace ℝ (Fin d)) (k : Fin K) : blk (concatE Z) k = Z k := by
  ext i
  show concatE Z (finProdFinEquiv (k, i)) = Z k i
  rw [concatE_apply, Equiv.symm_apply_apply]

lemma norm_concatE_sq (Z : Fin K → EuclideanSpace ℝ (Fin d)) :
    ‖concatE Z‖ ^ 2 = ∑ k, ‖Z k‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp_rw [EuclideanSpace.norm_sq_eq]
  rw [← Fintype.sum_prod_type', ← (finProdFinEquiv (m := K) (n := d)).sum_comp]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Real.norm_eq_abs, sq_abs, Real.norm_eq_abs, sq_abs]
  show (concatE Z (finProdFinEquiv q)) ^ 2 = (Z q.1 q.2) ^ 2
  rw [concatE_apply, Equiv.symm_apply_apply]

lemma measurable_concatE : Measurable (concatE (K := K) (d := d)) := by
  refine (MeasurableEquiv.toLp 2 (Fin (K * d) → ℝ)).measurable.comp ?_
  refine measurable_pi_lambda _ fun q => ?_
  exact (measurable_pi_apply _).comp ((PiLp.continuous_ofLp 2 _).measurable.comp
    (measurable_pi_apply (finProdFinEquiv.symm q).1))

/-- **Blocks of an isotropic Gaussian.** -/
theorem pi_gaussE_map_concatE (c : Fin K → EuclideanSpace ℝ (Fin d)) (σ2 : ℝ≥0) :
    (Measure.pi (fun k => gaussE (c k) σ2)).map concatE = gaussE (concatE c) σ2 := by
  set e := (finProdFinEquiv (m := K) (n := d)) with he
  set Φ : (Fin K → EuclideanSpace ℝ (Fin d)) → (Fin (K * d) → ℝ) :=
    fun Z q => Z (e.symm q).1 (e.symm q).2 with hΦ
  have hΦm : Measurable Φ := by
    refine measurable_pi_lambda _ fun q => ?_
    exact (measurable_pi_apply _).comp ((PiLp.continuous_ofLp 2 _).measurable.comp
      (measurable_pi_apply (e.symm q).1))
  have hconc : concatE (K := K) (d := d) = (MeasurableEquiv.toLp 2 (Fin (K * d) → ℝ)) ∘ Φ := rfl
  haveI : ∀ k, IsProbabilityMeasure (gaussE (c k) σ2) := fun k => by
    unfold gaussE; exact Measure.isProbabilityMeasure_map (by fun_prop)
  rw [hconc, ← Measure.map_map (MeasurableEquiv.toLp 2 (Fin (K * d) → ℝ)).measurable hΦm, gaussE]
  congr 1
  refine (Measure.pi_eq fun s hs => ?_).symm
  rw [Measure.map_apply hΦm (MeasurableSet.univ_pi hs)]
  have hpre : Φ ⁻¹' (univ.pi s) = univ.pi (fun k => {z : EuclideanSpace ℝ (Fin d) |
      ∀ i, z i ∈ s (e (k, i))}) := by
    ext Z
    simp only [mem_preimage, mem_univ_pi, mem_setOf_eq, hΦ]
    constructor
    · intro h k i
      have := h (e (k, i))
      simpa using this
    · intro h q
      have := h (e.symm q).1 (e.symm q).2
      simpa using this
  rw [hpre, Measure.pi_pi]
  have hk : ∀ k, gaussE (c k) σ2 {z : EuclideanSpace ℝ (Fin d) | ∀ i, z i ∈ s (e (k, i))}
      = ∏ i, gaussianReal (c k i) σ2 (s (e (k, i))) := by
    intro k
    rw [gaussE, Measure.map_apply (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurable]
    · have : (MeasurableEquiv.toLp 2 (Fin d → ℝ)) ⁻¹'
          {z : EuclideanSpace ℝ (Fin d) | ∀ i, z i ∈ s (e (k, i))} = univ.pi (fun i => s (e (k, i))) := by
        ext x; simp
      rw [this, Measure.pi_pi]
    · have : {z : EuclideanSpace ℝ (Fin d) | ∀ i, z i ∈ s (e (k, i))}
          = (MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm ⁻¹' univ.pi (fun i => s (e (k, i))) := by
        ext x; simp
      rw [this]
      exact (MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm.measurable (MeasurableSet.univ_pi fun i => hs _)
  simp_rw [hk]
  rw [← Fintype.prod_prod_type', ← e.prod_comp]
  refine Finset.prod_congr rfl fun q _ => ?_
  show gaussianReal (c q.1 q.2) σ2 (s (e q)) = gaussianReal (concatE c (e q)) σ2 (s (e q))
  rw [concatE_apply, he, Equiv.symm_apply_apply]

end DPFTRL.Band

