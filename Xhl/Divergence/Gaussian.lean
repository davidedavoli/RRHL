import Mathlib.Probability.Distributions.Gaussian.Real
import Xhl.Divergence.HellingerIntegral

/-!
# The scalar Gaussian Hellinger integral

  `hellingerIntegral α (𝒩 μ₁ v) (𝒩 μ₂ v) = exp(α(α-1)(μ₁-μ₂)²/(2v))`

(Proposition A.25, item 1, in dimension one), from the density identity
`pdf₁^α·pdf₂^{1-α} = exp(α(α-1)Δ²/2v)·pdf_{αμ₁+(1-α)μ₂}`.
-/

open MeasureTheory ProbabilityTheory ENNReal Real
open scoped NNReal

namespace Continuous

/-- **The Gaussian Hellinger integral** (`α > 1`, variance `v ≠ 0`) of two same-variance
    Gaussians. -/
theorem hellingerIntegral_gaussianReal {α : ℝ} (hα : 1 < α) (μ₁ μ₂ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    hellingerIntegral α (gaussianReal μ₁ v) (gaussianReal μ₂ v)
      = ENNReal.ofReal (Real.exp (α * (α - 1) * (μ₁ - μ₂) ^ 2 / (2 * (v : ℝ)))) := by
  have hα0 : (0 : ℝ) < α := by linarith
  have hvR : (0 : ℝ) < (v : ℝ) := by exact_mod_cast hv.bot_lt
  set N₁ := gaussianReal μ₁ v with hN1
  set N₂ := gaussianReal μ₂ v with hN2
  have h1vol : N₁ ≪ volume := gaussianReal_absolutelyContinuous μ₁ hv
  have h2vol : N₂ ≪ volume := gaussianReal_absolutelyContinuous μ₂ hv
  have hvol2 : volume ≪ N₂ := gaussianReal_absolutelyContinuous' μ₂ hv
  have h12 : N₁ ≪ N₂ := h1vol.trans hvol2
  set K : ℝ := Real.exp (α * (α - 1) * (μ₁ - μ₂) ^ 2 / (2 * (v : ℝ))) with hK
  set m' : ℝ := α * μ₁ + (1 - α) * μ₂ with hm'
  set C : ℝ := (√(2 * π * (v : ℝ)))⁻¹ with hC
  have hCpos : (0 : ℝ) < C := by rw [hC]; positivity
  have hKnn : (0 : ℝ) ≤ K := by rw [hK]; positivity
  have hexppow : ∀ (a y : ℝ), (Real.exp a) ^ y = Real.exp (a * y) := fun a y => by
    rw [Real.rpow_def_of_pos (Real.exp_pos a), Real.log_exp]
  have hptwise : ∀ x : ℝ,
      gaussianPDFReal μ₁ v x ^ α * gaussianPDFReal μ₂ v x ^ (1 - α)
        = K * gaussianPDFReal m' v x := by
    intro x
    simp only [gaussianPDFReal_def, ← hC]
    rw [Real.mul_rpow hCpos.le (Real.exp_pos _).le,
        Real.mul_rpow hCpos.le (Real.exp_pos _).le,
        Real.rpow_def_of_pos hCpos α, Real.rpow_def_of_pos hCpos (1 - α),
        hexppow, hexppow, hK, ← Real.exp_log hCpos]
    simp only [← Real.exp_add]
    rw [Real.exp_eq_exp, hm']
    simp only [Real.log_exp]
    field_simp
    ring
  -- evaluate against Lebesgue measure
  rw [← hRen_ref_indep hα N₁ N₂ volume h12 h2vol, hRen]
  have hrn1 := rnDeriv_gaussianReal μ₁ v
  have hrn2 := rnDeriv_gaussianReal μ₂ v
  have hintegrand : (fun x => (N₁.rnDeriv volume x) ^ α * (N₂.rnDeriv volume x) ^ (1 - α))
      =ᵐ[volume] fun x => ENNReal.ofReal (K * gaussianPDFReal m' v x) := by
    filter_upwards [hrn1, hrn2] with x hx1 hx2
    rw [hx1, hx2]
    simp only [gaussianPDF]
    rw [ENNReal.ofReal_rpow_of_pos (gaussianPDFReal_pos μ₁ v x hv),
        ENNReal.ofReal_rpow_of_pos (gaussianPDFReal_pos μ₂ v x hv),
        ← ENNReal.ofReal_mul (Real.rpow_nonneg (gaussianPDFReal_nonneg _ _ _) _), hptwise x]
  rw [lintegral_congr_ae hintegrand,
      ← ofReal_integral_eq_lintegral_ofReal
        ((integrable_gaussianPDFReal m' v).const_mul K)
        (Filter.Eventually.of_forall fun x => mul_nonneg hKnn (gaussianPDFReal_nonneg _ _ _))]
  rw [integral_const_mul, integral_gaussianPDFReal_eq_one m' hv, mul_one]

end Continuous
