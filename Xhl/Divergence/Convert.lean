/-
  The Rényi → (ε,δ) conversion of Balle et al. (AISTATS 2020, Theorem 21; paper
  Proposition 3.5), `ε = ρ + log((α−1)/α) − (log δ + log α)/(α−1)`, the one used by
  deployed accountants. From the power form `μ A ≤ H^{1/α} · ν(A)^{(α−1)/α}`
  (`hellingerIntegral_pr_le`, Hölder), a single weighted AM–GM step at the optimal split
  point (`root_to_add_improved`) gives `hellingerIntegral_to_dp_balle`.
-/
import Mathlib.Analysis.MeanInequalities
import Xhl.Divergence.HellingerIntegral

open Real

namespace Continuous

/-- **The conversion, scalar form.** From `a ≤ H^{1/α} b^{(α−1)/α}` and any `K > 0`,
    `a ≤ K·b + H·K^{1−α}(α−1)^{α−1}/α^α`. -/
theorem root_to_add_improved {α H K a b : ℝ} (hα : 1 < α)
    (hH : 0 ≤ H) (hK : 0 < K) (_ha : 0 ≤ a) (hb : 0 ≤ b)
    (hroot : a ≤ H ^ (1 / α) * b ^ ((α - 1) / α)) :
    a ≤ K * b + H * K ^ (1 - α) * ((α - 1) ^ (α - 1) / α ^ α) := by
  have hα0 : (0 : ℝ) < α := by linarith
  have hα1 : (0 : ℝ) < α - 1 := by linarith
  set c : ℝ := (α - 1) / (α * K) with hc
  set d : ℝ := α * K / (α - 1) with hd
  have hc0 : (0:ℝ) < c := by rw [hc]; positivity
  have hd0 : (0:ℝ) < d := by rw [hd]; positivity
  have hcd : c * d = 1 := by rw [hc, hd]; field_simp
  set p₁ : ℝ := H * c ^ (α - 1) with hp₁
  set p₂ : ℝ := d * b with hp₂
  have hp₁0 : 0 ≤ p₁ := by rw [hp₁]; positivity
  have hp₂0 : 0 ≤ p₂ := by rw [hp₂]; positivity
  have hw : 1 / α + (α - 1) / α = 1 := by field_simp; ring
  have hgm := Real.geom_mean_le_arith_mean2_weighted
    (by positivity : (0:ℝ) ≤ 1 / α) (by positivity : (0:ℝ) ≤ (α - 1) / α) hp₁0 hp₂0 hw
  have e1 : p₁ ^ (1 / α) = H ^ (1 / α) * c ^ ((α - 1) / α) := by
    rw [hp₁, Real.mul_rpow hH (Real.rpow_nonneg hc0.le _), ← Real.rpow_mul hc0.le,
      mul_one_div]
  have e2 : p₂ ^ ((α - 1) / α) = d ^ ((α - 1) / α) * b ^ ((α - 1) / α) := by
    rw [hp₂, Real.mul_rpow hd0.le hb]
  have hgeo : p₁ ^ (1 / α) * p₂ ^ ((α - 1) / α) = H ^ (1 / α) * b ^ ((α - 1) / α) := by
    rw [e1, e2]
    rw [show H ^ (1 / α) * c ^ ((α - 1) / α) * (d ^ ((α - 1) / α) * b ^ ((α - 1) / α))
        = H ^ (1 / α) * b ^ ((α - 1) / α) * (c ^ ((α - 1) / α) * d ^ ((α - 1) / α)) by ring,
      ← Real.mul_rpow hc0.le hd0.le, hcd, Real.one_rpow, mul_one]
  have hterm2 : (α - 1) / α * p₂ = K * b := by rw [hp₂, hd]; field_simp
  have hαα : α ^ α = α * α ^ (α - 1) := by
    have h := Real.rpow_add hα0 1 (α - 1)
    rwa [show (1:ℝ) + (α - 1) = α by ring, Real.rpow_one] at h
  have hterm1 : 1 / α * p₁ = H * K ^ (1 - α) * ((α - 1) ^ (α - 1) / α ^ α) := by
    rw [hp₁, hc, Real.div_rpow (by linarith) (by positivity),
      Real.mul_rpow hα0.le hK.le,
      show (1:ℝ) - α = -(α - 1) by ring, Real.rpow_neg hK.le, hαα]
    have hK1 : (0:ℝ) < K ^ (α - 1) := Real.rpow_pos_of_pos hK _
    have hA1 : (0:ℝ) < α ^ (α - 1) := Real.rpow_pos_of_pos hα0 _
    field_simp
  calc a ≤ H ^ (1 / α) * b ^ ((α - 1) / α) := hroot
    _ = p₁ ^ (1 / α) * p₂ ^ ((α - 1) / α) := hgeo.symm
    _ ≤ 1 / α * p₁ + (α - 1) / α * p₂ := hgm
    _ = K * b + H * K ^ (1 - α) * ((α - 1) ^ (α - 1) / α ^ α) := by
        rw [hterm1, hterm2]; ring

end Continuous

namespace Continuous

open MeasureTheory ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Hölder: `μ A ≤ H_α(μ‖ν)^{1/α} · ν(A)^{(α−1)/α}`. -/
theorem hellingerIntegral_pr_le {α : ℝ} (hα : 1 < α) (μ ν : Measure Ω)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμν : μ ≪ ν)
    {A : Set Ω} (hA : MeasurableSet A) :
    μ A ≤ (hellingerIntegral α μ ν) ^ (1 / α) * (ν A) ^ ((α - 1) / α) := by
  have hα0 : (0 : ℝ) < α := by linarith
  set q : ℝ := α / (α - 1) with hq
  have hqpos : 0 < q := div_pos hα0 (by linarith)
  have hpq : α.HolderConjugate q := by
    rw [Real.holderConjugate_iff]; exact ⟨hα, by rw [hq, inv_div]; field_simp; ring⟩
  set f : Ω → ℝ≥0∞ := μ.rnDeriv ν with hf
  set g : Ω → ℝ≥0∞ := A.indicator 1 with hg
  have hfm : AEMeasurable f ν := (Measure.measurable_rnDeriv μ ν).aemeasurable
  have hgm : AEMeasurable g ν := (measurable_const.indicator hA).aemeasurable
  have hμA : μ A = ∫⁻ x, f x * g x ∂ν := by
    rw [← Measure.setLIntegral_rnDeriv hμν A, ← lintegral_indicator hA]
    refine lintegral_congr fun x => ?_
    simp only [hf, hg]
    by_cases hx : x ∈ A <;> simp [hx]
  have hfα : ∫⁻ x, f x ^ α ∂ν = hellingerIntegral α μ ν := (hellingerIntegral_eq_lintegral_rnDeriv μ ν hμν).symm
  have hgq : ∫⁻ x, g x ^ q ∂ν = ν A := by
    have hpow : (fun x => g x ^ q) = A.indicator 1 := by
      funext x
      simp only [hg, Set.indicator, Pi.one_apply]
      by_cases hx : x ∈ A <;>
        simp [hx, ENNReal.zero_rpow_of_pos hqpos, ENNReal.one_rpow]
    rw [hpow, lintegral_indicator hA]; simp
  have hHold := ENNReal.lintegral_mul_le_Lp_mul_Lq ν hpq hfm hgm
  rw [hfα, hgq, show (1 : ℝ) / q = (α - 1) / α by rw [hq, one_div_div]] at hHold
  rw [hμA]
  exact hHold

/-- **(ε,δ) from a Hellinger bound.** If `H_α(μ‖ν) ≤ e^{(α−1)ρ}`, then for every `δ > 0`
    and every event the `(ε,δ)` inequality holds at Balle et al.'s `ε`. -/
theorem hellingerIntegral_to_dp_balle {α ρ δ : ℝ} (hα : 1 < α) (hδ0 : 0 < δ)
    (μ ν : Measure Ω) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμν : μ ≪ ν)
    (hH : hellingerIntegral α μ ν ≤ ENNReal.ofReal (Real.exp ((α - 1) * ρ)))
    {A : Set Ω} (hA : MeasurableSet A) :
    (μ A).toReal
      ≤ Real.exp (ρ + Real.log ((α - 1) / α)
          - (Real.log δ + Real.log α) / (α - 1)) * (ν A).toReal + δ := by
  have hα0 : (0:ℝ) < α := by linarith
  have hα1 : (0:ℝ) < α - 1 := by linarith
  set ε : ℝ := ρ + Real.log ((α - 1) / α) - (Real.log δ + Real.log α) / (α - 1) with hε
  have hK : (0:ℝ) < Real.exp ε := Real.exp_pos _
  have hpr := hellingerIntegral_pr_le hα μ ν hμν hA
  have hroot : (μ A).toReal
      ≤ Real.exp ((α - 1) * ρ) ^ (1 / α) * ((ν A).toReal) ^ ((α - 1) / α) := by
    have hmono : hellingerIntegral α μ ν ^ (1 / α) * (ν A) ^ ((α - 1) / α)
        ≤ ENNReal.ofReal (Real.exp ((α - 1) * ρ)) ^ (1 / α) * (ν A) ^ ((α - 1) / α) :=
      mul_le_mul' (ENNReal.rpow_le_rpow hH (by positivity)) le_rfl
    have hle := hpr.trans hmono
    have hfin : ENNReal.ofReal (Real.exp ((α - 1) * ρ)) ^ (1 / α) * (ν A) ^ ((α - 1) / α)
        ≠ ⊤ :=
      ENNReal.mul_ne_top
        (ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top)
        (ENNReal.rpow_ne_top_of_nonneg (by positivity) (measure_ne_top ν A))
    have h := (ENNReal.toReal_le_toReal (measure_ne_top μ A) hfin).mpr hle
    simpa [ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
      ENNReal.toReal_ofReal (Real.exp_pos _).le] using h
  have key := root_to_add_improved (α := α) (H := Real.exp ((α - 1) * ρ))
    (K := Real.exp ε) hα (Real.exp_pos _).le hK ENNReal.toReal_nonneg
    ENNReal.toReal_nonneg hroot
  have hslack : Real.exp ((α - 1) * ρ) * Real.exp ε ^ (1 - α)
      * ((α - 1) ^ (α - 1) / α ^ α) = δ := by
    rw [Real.rpow_def_of_pos hK, Real.log_exp,
      Real.rpow_def_of_pos hα1, Real.rpow_def_of_pos hα0,
      ← Real.exp_sub, ← Real.exp_add, ← Real.exp_add]
    rw [show (α - 1) * ρ + ε * (1 - α)
          + (Real.log (α - 1) * (α - 1) - Real.log α * α) = Real.log δ by
      rw [hε, Real.log_div hα1.ne' hα0.ne']; field_simp; ring]
    exact Real.exp_log hδ0
  rwa [hslack] at key

end Continuous
