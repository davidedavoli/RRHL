import Xhl.Divergence.Gaussian
import Xhl.Divergence.Tensor

/-!
# The isotropic Gaussian Hellinger integral on `Fin d → ℝ`

For `𝒩(μ, vI_d)` as the product `Measure.pi` of `d` scalar Gaussians, tensorization
(`hellingerIntegral_pi`) and `hellingerIntegral_gaussianReal` give
`exp(r(r-1)‖μ₁ − μ₂‖²/(2v))` (Proposition A.25, item 1).
-/

open MeasureTheory ProbabilityTheory ENNReal Real
open scoped NNReal

namespace Continuous

/-- **The isotropic Gaussian Hellinger integral** on `Fin d → ℝ`, at order `r > 1`. -/
theorem hellingerIntegral_gaussianReal_pi {r : ℝ} {d : ℕ} (hr : 1 < r) (μ₁ μ₂ : Fin d → ℝ)
    {v : ℝ≥0} (hv : v ≠ 0) :
    hellingerIntegral r (Measure.pi (fun i => gaussianReal (μ₁ i) v))
        (Measure.pi (fun i => gaussianReal (μ₂ i) v))
      = ENNReal.ofReal
          (Real.exp (r * (r - 1) * (∑ i, (μ₁ i - μ₂ i) ^ 2) / (2 * (v : ℝ)))) := by
  rw [hellingerIntegral_pi hr d _ _ (fun i => inferInstance) (fun i => inferInstance)
      (fun i => (gaussianReal_absolutelyContinuous (μ₁ i) hv).trans
        (gaussianReal_absolutelyContinuous' (μ₂ i) hv)),
    Finset.prod_congr rfl (fun i _ => hellingerIntegral_gaussianReal hr (μ₁ i) (μ₂ i) hv),
    ← ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le), ← Real.exp_sum]
  congr 2
  rw [← Finset.sum_div, ← Finset.mul_sum]

end Continuous
