import Xhl.Divergence.SubsamplingDomination

/-!
# A weak triangle inequality for the Hellinger integral

For finite measures with `R ≠ 0` (paper eq. (22)):

    H_α(P ‖ Q) ≤ ( H_{2α}(P ‖ R) · H_{2α−1}(R ‖ Q) )^{1/2}        (`hellingerIntegral_le_sqrt_mul`),

by Cauchy–Schwarz in `L²(Q)` on `(dP/dQ)^α = [(dP/dR)^α (dR/dQ)^{1/2}] · (dR/dQ)^{α−1/2}`.
Used for the replace-one last-iterate bound (`Examples/DPSGD/LastIterate/Replace.lean`).
-/

open MeasureTheory ProbabilityTheory ENNReal
open scoped NNReal

namespace Continuous

/-- The zero measure has Hellinger integral `0` against anything, for `α > 0`. -/
lemma hellingerIntegral_zero_left {Ω : Type*} [MeasurableSpace Ω] {α : ℝ} (hα : 0 < α)
    (Q : Measure Ω) : hellingerIntegral α 0 Q = 0 := by
  rw [hellingerIntegral_eq_lintegral_rnDeriv _ _ (Measure.AbsolutelyContinuous.zero Q)]
  have h0 : (fun x => (Measure.rnDeriv 0 Q x) ^ α) =ᵐ[Q] fun _ => 0 :=
    (Measure.rnDeriv_zero Q).mono fun x hx => by
      simp only [hx, Pi.zero_apply, ENNReal.zero_rpow_of_pos hα]
  rw [lintegral_congr_ae h0, lintegral_zero]

/-- A nonzero measure has nonzero Hellinger integral against anything, for `α > 0`. -/
lemma hellingerIntegral_ne_zero {Ω : Type*} [MeasurableSpace Ω] {α : ℝ} (hα : 0 < α)
    {μ : Measure Ω} (ν : Measure Ω) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμ : μ ≠ 0) :
    hellingerIntegral α μ ν ≠ 0 := by
  by_cases hac : μ ≪ ν
  · rw [hellingerIntegral_eq_lintegral_rnDeriv _ _ hac]
    intro h
    rw [lintegral_eq_zero_iff ((Measure.measurable_rnDeriv _ _).pow_const _)] at h
    refine hμ ?_
    have h0 : μ.rnDeriv ν =ᵐ[ν] 0 := h.mono fun x hx => by
      simpa [ENNReal.rpow_eq_zero_iff, hα, hα.not_gt] using hx
    rw [← Measure.withDensity_rnDeriv_eq μ ν hac, withDensity_congr_ae h0, withDensity_zero]
  · rw [hellingerIntegral_eq_top_of_not_ac _ _ hac]; exact top_ne_zero

/-- The Cauchy–Schwarz step, under `P ≪ R ≪ Q`. -/
private theorem hellingerIntegral_le_sqrt_mul_of_ac {Ω : Type*} [MeasurableSpace Ω] {α : ℝ} (hα : 1 < α)
    (P R Q : Measure Ω) [IsFiniteMeasure P] [IsFiniteMeasure R] [IsFiniteMeasure Q]
    (hPR : P ≪ R) (hRQ : R ≪ Q) :
    hellingerIntegral α P Q
      ≤ (hellingerIntegral (2 * α) P R * hellingerIntegral (2 * α - 1) R Q) ^ (1 / 2 : ℝ) := by
  have hα0 : (0 : ℝ) ≤ α := by linarith
  have hα2 : (0 : ℝ) ≤ α - 1 / 2 := by linarith
  set pr := P.rnDeriv R with hpr
  set rq := R.rnDeriv Q with hrq
  have hpr_m : Measurable pr := Measure.measurable_rnDeriv _ _
  have hrq_m : Measurable rq := Measure.measurable_rnDeriv _ _
  rw [hellingerIntegral_eq_lintegral_rnDeriv _ _ (hPR.trans hRQ),
    hellingerIntegral_eq_lintegral_rnDeriv _ _ hPR,
    hellingerIntegral_eq_lintegral_rnDeriv _ _ hRQ]
  have hchain : ∫⁻ x, (P.rnDeriv Q x) ^ α ∂Q
      = ∫⁻ x, ((pr x ^ α * rq x ^ (1 / 2 : ℝ)) * rq x ^ (α - 1 / 2)) ∂Q := by
    refine lintegral_congr_ae ?_
    filter_upwards [Measure.rnDeriv_mul_rnDeriv (κ := Q) hPR] with x hx
    rw [← hx, Pi.mul_apply, ENNReal.mul_rpow_of_nonneg _ _ hα0, mul_assoc,
      ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) hα2]
    congr 2; ring
  rw [hchain]
  have hCS := ENNReal.lintegral_mul_le_Lp_mul_Lq Q Real.HolderConjugate.two_two
    (f := fun x => pr x ^ α * rq x ^ (1 / 2 : ℝ)) (g := fun x => rq x ^ (α - 1 / 2))
    ((hpr_m.pow_const _).mul (hrq_m.pow_const _)).aemeasurable
    (hrq_m.pow_const _).aemeasurable
  have hf2 : ∫⁻ x, (pr x ^ α * rq x ^ (1 / 2 : ℝ)) ^ (2 : ℝ) ∂Q = ∫⁻ x, pr x ^ (2 * α) ∂R := by
    rw [← lintegral_rnDeriv_mul hRQ (hpr_m.pow_const _).aemeasurable]
    refine lintegral_congr fun x => ?_
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
      show (1 / 2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one, mul_comm α 2, mul_comm]
  have hg2 : ∫⁻ x, (rq x ^ (α - 1 / 2)) ^ (2 : ℝ) ∂Q = ∫⁻ x, rq x ^ (2 * α - 1) ∂Q := by
    refine lintegral_congr fun x => ?_
    rw [← ENNReal.rpow_mul]; congr 1; ring
  simp only [Pi.mul_apply, hf2, hg2] at hCS
  refine hCS.trans (le_of_eq ?_)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]

/-- **The weak triangle inequality** (paper eq. (22)): for finite measures with `R ≠ 0`
    and `α > 1`, `H_α(P‖Q) ≤ (H_{2α}(P‖R) · H_{2α−1}(R‖Q))^{1/2}`. -/
theorem hellingerIntegral_le_sqrt_mul {Ω : Type*} [MeasurableSpace Ω] {α : ℝ} (hα : 1 < α)
    (P R Q : Measure Ω) [IsFiniteMeasure P] [IsFiniteMeasure R] [IsFiniteMeasure Q]
    (hR : R ≠ 0) :
    hellingerIntegral α P Q
      ≤ (hellingerIntegral (2 * α) P R * hellingerIntegral (2 * α - 1) R Q) ^ (1 / 2 : ℝ) := by
  by_cases hP : P = 0
  · subst hP; rw [hellingerIntegral_zero_left (by linarith)]; exact bot_le
  have h₁ : hellingerIntegral (2 * α) P R ≠ 0 := hellingerIntegral_ne_zero (by linarith) R hP
  have h₂ : hellingerIntegral (2 * α - 1) R Q ≠ 0 := hellingerIntegral_ne_zero (by linarith) Q hR
  by_cases hPR : P ≪ R
  · by_cases hRQ : R ≪ Q
    · exact hellingerIntegral_le_sqrt_mul_of_ac hα P R Q hPR hRQ
    · rw [hellingerIntegral_eq_top_of_not_ac (α := 2 * α - 1) R Q hRQ, ENNReal.mul_top h₁,
        ENNReal.top_rpow_of_pos (by norm_num)]
      exact le_top
  · rw [hellingerIntegral_eq_top_of_not_ac (α := 2 * α) P R hPR, ENNReal.top_mul h₂,
      ENNReal.top_rpow_of_pos (by norm_num)]
    exact le_top

end Continuous
