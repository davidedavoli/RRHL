import Xhl.Divergence.SubsamplingRealOrderE
import Xhl.Measures.Erf

/-!
# The subsampled-Gaussian budget `Υ_α`

`mixBudgetR q s v α = Υ_α(q, s, v)` (paper eq. (3)), defined as a Hellinger integral and
monotone in `s` for every `q ≤ 1`. On `0 < q < 1`, `0 < s` it is evaluated in closed form
(`mixBudgetR_eq_closedForm`, `mixBudgetR_eq_phiForm`, `mixBudgetR_eq_erfcForm`;
Proposition E.2).
-/

open MeasureTheory ProbabilityTheory ENNReal Set
open scoped NNReal

namespace Continuous

variable {d : ℕ}

/-! ## The budget, for every `q ≤ 1` -/

/-- **`Υ_α(q, s, v)`** (paper eq. (3)): the Hellinger integral of
    `(1−q)·𝒩(0,v) + q·𝒩(s,v)` against `𝒩(0,v)`. -/
noncomputable def mixBudgetR (q : ℝ≥0) (s : ℝ) (v : ℝ≥0) (α : ℝ) : ℝ≥0∞ :=
  hellingerIntegral α ((1 - (q : ℝ≥0∞)) • gaussianReal (0 : ℝ) v + (q : ℝ≥0∞) • gaussianReal s v)
    (gaussianReal (0 : ℝ) v)

/-- At sensitivity `0` the mixture is the base Gaussian: the budget is `1`. -/
lemma mixBudgetR_zero {α : ℝ} (hα : 1 < α) (v : ℝ≥0) {q : ℝ≥0} (hq : (q : ℝ) ≤ 1) :
    mixBudgetR q 0 v α = 1 := by
  have hqE : (q : ℝ≥0∞) ≤ 1 := by exact_mod_cast hq
  rw [mixBudgetR, ← add_smul, tsub_add_cancel_of_le hqE, one_smul, hellingerIntegral_self_prob]

/-- **Monotonicity of `Υ_α` in the sensitivity**, for every `q ≤ 1`
    (Proposition A.24, item 2). -/
theorem mixBudgetR_mono {α : ℝ} (hα : 1 < α) {v : ℝ≥0} (hv : v ≠ 0) {q : ℝ≥0}
    (hq : (q : ℝ) ≤ 1) {s t : ℝ} (hst : |s| ≤ |t|) :
    mixBudgetR q s v α ≤ mixBudgetR q t v α := by
  have hαle : (1 : ℝ) ≤ α := hα.le
  have hqNN : q ≤ 1 := by exact_mod_cast hq
  have hvR : (0 : ℝ) < (v : ℝ) := by exact_mod_cast hv.bot_lt
  set β1 : ℝ≥0 := ⟨s ^ 2 / (v : ℝ), by positivity⟩ with hβ1def
  set β2 : ℝ≥0 := ⟨t ^ 2 / (v : ℝ), by positivity⟩ with hβ2def
  have hβ1R : (β1 : ℝ) = s ^ 2 / v := rfl
  have hβ2R : (β2 : ℝ) = t ^ 2 / v := rfl
  have hsq : s ^ 2 ≤ t ^ 2 := by
    rw [← sq_abs s, ← sq_abs t]; exact pow_le_pow_left₀ (abs_nonneg _) hst 2
  have hββ : β1 ≤ β2 := by
    rw [← NNReal.coe_le_coe, hβ1R, hβ2R]; exact div_le_div_of_nonneg_right hsq hvR.le
  have hgoal : ∫ x, mixturePow α q (gaussLR 0 s v x) ∂gaussianReal 0 v
      ≤ ∫ x, mixturePow α q (gaussLR 0 t v x) ∂gaussianReal 0 v := by
    rw [integral_mixturePow_gaussLR_eq_expShift hαle hq hv β1 hβ1R,
      integral_mixturePow_gaussLR_eq_expShift hαle hq hv β2 hβ2R]
    exact mixturePow_integral_mono_variance hαle hq hββ
  have h1 := hellingerIntegral_sgMixture_real (μ₀ := (0 : ℝ)) (Δ := s) hα hv q hqNN
  have h2 := hellingerIntegral_sgMixture_real (μ₀ := (0 : ℝ)) (Δ := t) hα hv q hqNN
  rw [zero_add] at h1 h2
  rw [mixBudgetR, mixBudgetR, h1, h2]
  exact ENNReal.ofReal_le_ofReal (by simpa [mixturePow] using hgoal)

/-- The budget is at least `1`, for every `q ≤ 1` and every sensitivity. -/
lemma one_le_mixBudgetR {α : ℝ} (hα : 1 < α) {v : ℝ≥0} (hv : v ≠ 0) {q : ℝ≥0}
    (hq : (q : ℝ) ≤ 1) (s : ℝ) : 1 ≤ mixBudgetR q s v α := by
  rw [← mixBudgetR_zero hα v hq]
  exact mixBudgetR_mono hα hv hq (by simp [abs_nonneg s])

lemma mixBudgetR_ne_top {α : ℝ} (hα : 1 < α) (q : ℝ≥0) (s : ℝ) {v : ℝ≥0} (hv : v ≠ 0)
    (hq : (q : ℝ) ≤ 1) : mixBudgetR q s v α ≠ ⊤ := by
  have hqNN : q ≤ 1 := by exact_mod_cast hq
  have h := hellingerIntegral_sgMixture_real (μ₀ := (0 : ℝ)) (Δ := s) hα hv q hqNN
  rw [zero_add] at h
  rw [mixBudgetR, h]
  exact ENNReal.ofReal_ne_top

/-- **The vector subsampled Gaussian at the budget**: on `EuclideanSpace ℝ (Fin d)`, at a
    displacement of norm at most `s`, the Hellinger integral is at most `Υ_α(q, s, v)`. -/
theorem hellingerIntegral_sgMixtureE_le_mixBudgetR {α : ℝ} (hα : 1 < α) (u Δ : EuclideanSpace ℝ (Fin d))
    (v : ℝ≥0) (hv : v ≠ 0) (q : ℝ≥0) (hq : q ≤ 1) {s : ℝ} (hΔ : ‖Δ‖ ≤ s) :
    hellingerIntegral α ((1 - (q : ℝ≥0∞)) • gaussE u v + (q : ℝ≥0∞) • gaussE (u + Δ) v) (gaussE u v)
      ≤ mixBudgetR q s v α := by
  have hqR : (q : ℝ) ≤ 1 := by exact_mod_cast hq
  have hqE : (q : ℝ≥0∞) ≤ 1 := by exact_mod_cast hq
  have hs : 0 ≤ s := le_trans (norm_nonneg Δ) hΔ
  rcases eq_or_ne Δ 0 with rfl | hΔ0
  · rw [add_zero, ← add_smul, tsub_add_cancel_of_le hqE, one_smul, hellingerIntegral_self_prob]
    exact one_le_mixBudgetR hα hv hqR s
  · rw [hellingerIntegral_sgMixtureE_eq_scalar hα u Δ hΔ0 v hv q]
    exact mixBudgetR_mono hα hv hqR
      (by rw [abs_of_nonneg (norm_nonneg Δ), abs_of_nonneg hs]; exact hΔ)

/-! ## Evaluating the budget: the closed form (Proposition E.2) -/

/-- **The budget in closed form**, for `0 < q < 1` and `0 < s`: the two binomial series
    of Mironov et al.'s §3.3 accountant, split at `z₁`. -/
theorem mixBudgetR_eq_closedForm {α : ℝ} (hα : 1 < α) {q : ℝ≥0} (hq0 : 0 < q)
    (hq1 : (q : ℝ) < 1) {s : ℝ} (hs : 0 < s) {v : ℝ≥0} (hv : v ≠ 0) :
    mixBudgetR q s v α
      = ENNReal.ofReal
          ((∑' n : ℕ, Ring.choose α n * (1 - (q : ℝ)) ^ (α - n) * (q : ℝ) ^ n
              * ∫ z in Set.Iio (z₁ (0:ℝ) s v q), gaussLR (0:ℝ) s v z ^ n ∂(gaussianReal (0:ℝ) v))
            + ∑' n : ℕ, Ring.choose α n * (1 - (q : ℝ)) ^ n * (q : ℝ) ^ (α - n)
              * ∫ z in Set.Ioi (z₁ (0:ℝ) s v q), gaussLR (0:ℝ) s v z ^ (α - (n : ℝ))
                ∂(gaussianReal (0:ℝ) v)) := by
  rw [mixBudgetR]
  simpa using hellingerIntegral_sgMixture_real_closedForm_unconditional (μ₀ := 0) hα hs hv hq0 hq1

/-- **The budget, `Φ` form** (Proposition E.2): each truncated likelihood-ratio moment of
`mixBudgetR_eq_closedForm` as `exp(β(β−1)s²/2v)` times the Gaussian measure of a half-line. -/
theorem mixBudgetR_eq_phiForm {α : ℝ} (hα : 1 < α) {q : ℝ≥0} (hq0 : 0 < q)
    (hq1 : (q : ℝ) < 1) {s : ℝ} (hs : 0 < s) {v : ℝ≥0} (hv : v ≠ 0) :
    mixBudgetR q s v α
      = ENNReal.ofReal
          ((∑' n : ℕ, Ring.choose α n * (1 - (q : ℝ)) ^ (α - n) * (q : ℝ) ^ n
              * (Real.exp ((n : ℝ) * ((n : ℝ) - 1) * s ^ 2 / (2 * (v : ℝ)))
                  * (gaussianReal ((n : ℝ) * s) v).real (Set.Iio (z₁ (0:ℝ) s v q))))
            + ∑' n : ℕ, Ring.choose α n * (1 - (q : ℝ)) ^ n * (q : ℝ) ^ (α - n)
              * (Real.exp ((α - (n : ℝ)) * ((α - (n : ℝ)) - 1) * s ^ 2 / (2 * (v : ℝ)))
                  * (gaussianReal ((α - (n : ℝ)) * s) v).real (Set.Ioi (z₁ (0:ℝ) s v q)))) := by
  rw [mixBudgetR_eq_closedForm hα hq0 hq1 hs hv]
  congr 1
  congr 1
  · exact tsum_congr fun n => by
      rw [integral_gaussLR_pow_eq hv n measurableSet_Iio, zero_add]
  · exact tsum_congr fun n => by
      rw [integral_gaussLR_rpow_eq hv (α - (n : ℝ)) measurableSet_Ioi, zero_add]

/-- **The budget, `erfc` form** (Proposition E.2): `mixBudgetR_eq_phiForm` with each
Gaussian half-line mass written via `erfc`, as evaluated by deployed accountants. -/
theorem mixBudgetR_eq_erfcForm {α : ℝ} (hα : 1 < α) {q : ℝ≥0} (hq0 : 0 < q)
    (hq1 : (q : ℝ) < 1) {s : ℝ} (hs : 0 < s) {v : ℝ≥0} (hv : v ≠ 0) :
    mixBudgetR q s v α
      = ENNReal.ofReal
          ((∑' n : ℕ, Ring.choose α n * (1 - (q : ℝ)) ^ (α - n) * (q : ℝ) ^ n
              * (Real.exp ((n : ℝ) * ((n : ℝ) - 1) * s ^ 2 / (2 * (v : ℝ)))
                  * (2⁻¹ * erfc (((n : ℝ) * s - z₁ (0:ℝ) s v q) / Real.sqrt (2 * v)))))
            + ∑' n : ℕ, Ring.choose α n * (1 - (q : ℝ)) ^ n * (q : ℝ) ^ (α - n)
              * (Real.exp ((α - (n : ℝ)) * ((α - (n : ℝ)) - 1) * s ^ 2 / (2 * (v : ℝ)))
                  * (2⁻¹ * erfc ((z₁ (0:ℝ) s v q - (α - (n : ℝ)) * s) / Real.sqrt (2 * v))))) := by
  rw [mixBudgetR_eq_phiForm hα hq0 hq1 hs hv]
  congr 1
  congr 1
  · exact tsum_congr fun n => by rw [gaussianReal_real_Iio _ _ hv]
  · exact tsum_congr fun n => by rw [gaussianReal_real_Ioi _ _ hv]

end Continuous
