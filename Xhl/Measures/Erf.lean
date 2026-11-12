/-
  The error function `erf`/`erfc` (absent from Mathlib) and the Gaussian half-line masses

      𝒩(m, v)(−∞, z) = ½·erfc((m − z)/√(2v))      (`gaussianReal_real_Iio`)
      𝒩(m, v)(z, ∞)  = ½·erfc((z − m)/√(2v))      (`gaussianReal_real_Ioi`)

  used to turn `mixBudgetR_eq_phiForm` into the erfc form evaluated by deployed
  accountants (`mixBudgetR_eq_erfcForm`, Proposition D.2).
-/
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Probability.Distributions.Gaussian.Real

open MeasureTheory ProbabilityTheory Set Real
open scoped NNReal

namespace Continuous

/-- **The error function**, `erf x = (2/√π)·∫ t in 0..x, exp (−t²)`. -/
noncomputable def erf (x : ℝ) : ℝ :=
  (2 / Real.sqrt π) * ∫ t in (0:ℝ)..x, Real.exp (-(t ^ 2))

/-- **The complementary error function**, `erfc x = 1 − erf x`. -/
noncomputable def erfc (x : ℝ) : ℝ := 1 - erf x

lemma integrable_exp_neg_sq : Integrable fun t : ℝ => Real.exp (-(t ^ 2)) := by
  simpa [neg_mul] using integrable_exp_neg_mul_sq (one_pos (α := ℝ))

/-- `erf` is odd. -/
lemma erf_neg (x : ℝ) : erf (-x) = -erf x := by
  unfold erf
  have h : ∫ t in (0:ℝ)..(-x), Real.exp (-(t ^ 2))
      = ∫ t in (0:ℝ)..(-x), Real.exp (-((-t) ^ 2)) := by simp
  rw [h, intervalIntegral.integral_comp_neg (fun t => Real.exp (-(t ^ 2))),
    neg_zero, intervalIntegral.integral_symm, mul_neg, neg_neg]

/-- The right Gaussian half-mass: `∫ t in Ioi 0, exp (−t²) = √π/2`. -/
lemma integral_exp_neg_sq_Ioi :
    ∫ t in Ioi (0:ℝ), Real.exp (-(t ^ 2)) = Real.sqrt π / 2 := by
  simpa [neg_mul] using integral_gaussian_Ioi 1

/-- The left Gaussian half-mass, by reflection. -/
lemma integral_exp_neg_sq_Iio_zero :
    ∫ t in Iio (0:ℝ), Real.exp (-(t ^ 2)) = Real.sqrt π / 2 := by
  rw [← integral_Iic_eq_integral_Iio]
  have h : ∫ t in Iic (0:ℝ), Real.exp (-(t ^ 2))
      = ∫ t in Iic (0:ℝ), Real.exp (-((-t) ^ 2)) := by simp
  rw [h, integral_comp_neg_Iic 0 (fun t => Real.exp (-(t ^ 2))), neg_zero,
    integral_exp_neg_sq_Ioi]

/-- **The Gaussian integral over a lower half-line**, in `erfc` form. -/
lemma setIntegral_exp_neg_sq_Iio (y : ℝ) :
    ∫ t in Iio y, Real.exp (-(t ^ 2)) = Real.sqrt π / 2 * erfc (-y) := by
  have hπ : (0:ℝ) < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
  have hsplit := intervalIntegral.integral_Iio_sub_Iio'
    (f := fun t => Real.exp (-(t ^ 2))) (μ := volume) (a := 0) (b := y)
    integrable_exp_neg_sq.integrableOn integrable_exp_neg_sq.integrableOn
  rw [integral_exp_neg_sq_Iio_zero] at hsplit
  have hI : ∫ t in (0:ℝ)..y, Real.exp (-(t ^ 2)) = Real.sqrt π / 2 * erf y := by
    rw [erf]; field_simp
  rw [hI] at hsplit
  have : ∫ t in Iio y, Real.exp (-(t ^ 2))
      = Real.sqrt π / 2 * erf y + Real.sqrt π / 2 := by linarith
  rw [this, erfc, erf_neg]
  ring

/-- The lower tail of the centred Gaussian at variance `2⁻¹`, whose density is the erf
    integrand. -/
lemma gaussianReal_half_real_Iio (y : ℝ) :
    (gaussianReal 0 (2⁻¹ : ℝ≥0)).real (Iio y) = 2⁻¹ * erfc (-y) := by
  have hπ : (0:ℝ) < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
  have hv : (2⁻¹ : ℝ≥0) ≠ 0 := by norm_num
  have hpdf : ∀ x : ℝ, gaussianPDFReal 0 (2⁻¹ : ℝ≥0) x
      = (Real.sqrt π)⁻¹ * Real.exp (-(x ^ 2)) := by
    intro x
    simp only [gaussianPDFReal_def]
    have h1 : ((2⁻¹ : ℝ≥0) : ℝ) = 2⁻¹ := by norm_num
    rw [h1, show 2 * π * (2:ℝ)⁻¹ = π by ring, show 2 * (2:ℝ)⁻¹ = 1 by norm_num,
      sub_zero, div_one]
  rw [measureReal_def, gaussianReal_apply_eq_integral 0 hv,
    ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_Iio
      fun x _ => gaussianPDFReal_nonneg 0 _ x)]
  simp only [hpdf]
  rw [MeasureTheory.integral_const_mul, setIntegral_exp_neg_sq_Iio]
  rw [show (Real.sqrt π)⁻¹ * (Real.sqrt π / 2 * erfc (-y)) = 2⁻¹ * erfc (-y) by
    field_simp]

/-- `gaussianReal 0 v` is the `√(2v)`-dilation of the variance-`2⁻¹` Gaussian. -/
lemma gaussianReal_zero_eq_map_half {v : ℝ≥0} (hv : v ≠ 0) :
    (gaussianReal 0 (2⁻¹ : ℝ≥0)).map (Real.sqrt (2 * v) * ·) = gaussianReal 0 v := by
  rw [gaussianReal_map_const_mul]
  congr 1
  · ring
  · refine NNReal.coe_injective ?_
    push_cast
    rw [Real.sq_sqrt (by positivity)]
    ring

/-- **The Gaussian CDF in `erfc` form**: `𝒩(m,v)(−∞,z) = ½·erfc((m−z)/√(2v))`. -/
theorem gaussianReal_real_Iio (m z : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    (gaussianReal m v).real (Iio z)
      = 2⁻¹ * erfc ((m - z) / Real.sqrt (2 * v)) := by
  have hs : (0:ℝ) < Real.sqrt (2 * v) :=
    Real.sqrt_pos.mpr (by positivity)
  have hmap : gaussianReal m v
      = ((gaussianReal 0 (2⁻¹ : ℝ≥0)).map (Real.sqrt (2 * v) * ·)).map (· + m) := by
    rw [gaussianReal_zero_eq_map_half hv, gaussianReal_map_add_const, zero_add]
  rw [hmap, map_measureReal_apply (measurable_add_const m) measurableSet_Iio]
  have hpre1 : (· + m) ⁻¹' Iio z = Iio (z - m) := by
    ext x; simp [lt_sub_iff_add_lt]
  rw [hpre1, map_measureReal_apply (measurable_const_mul _) measurableSet_Iio,
    Set.preimage_const_mul_Iio₀ _ hs, gaussianReal_half_real_Iio, ← neg_div, neg_sub]

/-- **The Gaussian tail in `erfc` form**: `𝒩(m,v)(z,∞) = ½·erfc((z−m)/√(2v))`. -/
theorem gaussianReal_real_Ioi (m z : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    (gaussianReal m v).real (Ioi z)
      = 2⁻¹ * erfc ((z - m) / Real.sqrt (2 * v)) := by
  have hmap : gaussianReal m v = (gaussianReal (-m) v).map (fun x => -x) := by
    rw [gaussianReal_map_neg, neg_neg]
  have hpre : (fun x : ℝ => -x) ⁻¹' Ioi z = Iio (-z) := by
    ext x; simp
  rw [hmap, map_measureReal_apply measurable_neg measurableSet_Ioi, hpre,
    gaussianReal_real_Iio _ _ hv]
  congr 2
  ring

end Continuous
