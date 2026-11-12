import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-!
# Reverse-Hölder superadditivity and the reference-form Hellinger integral

`lintegral_rpow_mul_rpow_le`: for `α > 1`,

    (∫ f)^α · (∫ g)^{1-α}  ≤  ∫ f^α · g^{1-α},

by Hölder's inequality at the conjugate pair `(α, α/(α-1))`; it underlies data processing.
`hRen α ρ μ ν` is the Hellinger integral computed against a reference measure `ρ`.
-/

open MeasureTheory ENNReal NNReal

namespace Continuous

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

private lemma rpow_ne_zero_of_ne_zero {x : ℝ≥0∞} (hx : x ≠ 0) {y : ℝ}
    (hy : 0 < y) : x ^ y ≠ 0 := by
  rw [Ne, ENNReal.rpow_eq_zero_iff]; push Not
  exact ⟨fun h => absurd h hx, fun _ => by linarith⟩

private lemma rpow_ne_zero_of_ne_zero_ne_top {x : ℝ≥0∞} (hx0 : x ≠ 0)
    (hxt : x ≠ ⊤) (y : ℝ) : x ^ y ≠ 0 := by
  rw [Ne, ENNReal.rpow_eq_zero_iff]; push Not
  exact ⟨fun h => absurd h hx0, fun h => absurd h hxt⟩

private lemma rpow_ne_top_of_ne_zero_ne_top {x : ℝ≥0∞} (hx0 : x ≠ 0)
    (hxt : x ≠ ⊤) (y : ℝ) : x ^ y ≠ ⊤ := by
  rw [Ne, ENNReal.rpow_eq_top_iff]; push Not
  exact ⟨fun h => absurd h hx0, fun h => absurd h hxt⟩

/-- **Reverse-Hölder superadditivity** (`α > 1`):
    `(∫ f)^α · (∫ g)^{1-α} ≤ ∫ f^α · g^{1-α}`. -/
theorem lintegral_rpow_mul_rpow_le (f g : Ω → ℝ≥0∞) {α : ℝ} (hα : 1 < α)
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    (∫⁻ x, f x ∂μ) ^ α * (∫⁻ x, g x ∂μ) ^ (1 - α)
      ≤ ∫⁻ x, f x ^ α * g x ^ (1 - α) ∂μ := by
  have hα0 : (0 : ℝ) < α := lt_trans one_pos hα
  have hprodm : AEMeasurable (fun x => f x ^ α * g x ^ (1 - α)) μ :=
    (hf.pow_const _).mul (hg.pow_const _)
  set R := ∫⁻ x, f x ^ α * g x ^ (1 - α) ∂μ with hR
  set Sf := ∫⁻ x, f x ∂μ with hSf
  set Sg := ∫⁻ x, g x ∂μ with hSg
  rcases eq_or_ne R ⊤ with hRtop | hRtop
  · rw [hRtop]; exact le_top
  rcases eq_or_ne Sg ⊤ with hSgtop | hSgtop
  · rw [hSgtop, ENNReal.top_rpow_of_neg (by linarith), mul_zero]; exact zero_le
  -- Case ∫g = 0: then `f = 0` a.e. (else the integrand is ⊤ on a positive set,
  -- forcing `R = ⊤`), so the left side is 0.
  rcases eq_or_ne Sg 0 with hSg0 | hSg0
  · rcases eq_or_ne Sf 0 with hSf0 | hSf0
    · rw [hSf0, ENNReal.zero_rpow_of_pos hα0, zero_mul]; exact zero_le
    · exfalso; apply hRtop
      have hgae : g =ᵐ[μ] 0 := (lintegral_eq_zero_iff' hg).mp hSg0
      have hfpos : μ {x | f x ≠ 0} ≠ 0 := fun h =>
        hSf0 (hSf ▸ (lintegral_eq_zero_iff' hf).mpr (ae_iff.mpr (by simpa using h)))
      refine lintegral_eq_top_of_measure_eq_top_ne_zero hprodm ?_
      -- `{f ≠ 0} ⊆ᵐ {integrand = ⊤}` (as `g = 0` a.e.), and `{f ≠ 0}` is nonnull.
      have hsub : ∀ᵐ x ∂μ, x ∈ {x | f x ≠ 0} →
          x ∈ {x | f x ^ α * g x ^ (1 - α) = ⊤} := by
        filter_upwards [hgae] with x hx0 hxne
        rw [hx0, Pi.zero_apply, ENNReal.zero_rpow_of_neg (by linarith)]
        exact ENNReal.mul_top (rpow_ne_zero_of_ne_zero hxne hα0)
      exact fun h => hfpos (measure_mono_null_ae hsub h)
  -- From here `0 < ∫g < ⊤`.
  set q : ℝ := α / (α - 1) with hq
  have hqpos : 0 < q := div_pos hα0 (by linarith)
  have hpq : α.HolderConjugate q := by
    rw [Real.holderConjugate_iff]; exact ⟨hα, by rw [hq, inv_div]; field_simp; ring⟩
  have hgtop : ∀ᵐ x ∂μ, g x ≠ ⊤ := by
    filter_upwards [ae_lt_top' hg hSgtop] with x hx using hx.ne
  have hIntfin : ∀ᵐ x ∂μ, f x ^ α * g x ^ (1 - α) ≠ ⊤ := by
    filter_upwards [ae_lt_top' hprodm hRtop] with x hx using hx.ne
  -- The a.e. Hölder-substitution identity.
  have hae : (fun x => (f x ^ α * g x ^ (1 - α)) ^ (1 / α) * g x ^ (1 / q))
      =ᵐ[μ] f := by
    filter_upwards [hgtop, hIntfin] with x hgt hInt
    by_cases hg0 : g x = 0
    · -- `g x = 0` forces `f x = 0` (else integrand is ⊤).
      have hf0 : f x = 0 := by
        by_contra hfne
        exact hInt (by
          rw [hg0, ENNReal.zero_rpow_of_neg (by linarith)]
          exact ENNReal.mul_top (rpow_ne_zero_of_ne_zero hfne hα0))
      rw [hf0, hg0, ENNReal.zero_rpow_of_pos hα0, zero_mul,
        ENNReal.zero_rpow_of_pos (one_div_pos.mpr hα0), zero_mul]
    · -- `0 < g x < ⊤` forces `f x ≠ ⊤`, and the algebra collapses.
      have hfnetop : f x ≠ ⊤ := by
        by_contra hft
        exact hInt (by
          rw [hft, ENNReal.top_rpow_of_pos hα0]
          exact ENNReal.top_mul (rpow_ne_zero_of_ne_zero_ne_top hg0 hgt _))
      rw [ENNReal.mul_rpow_of_ne_top
            (ENNReal.rpow_ne_top_of_nonneg hα0.le hfnetop)
            (rpow_ne_top_of_ne_zero_ne_top hg0 hgt _),
        ← ENNReal.rpow_mul (f x), ← ENNReal.rpow_mul (g x),
        mul_one_div_cancel hα0.ne', ENNReal.rpow_one, mul_assoc,
        ← ENNReal.rpow_add _ _ hg0 hgt,
        show (1 - α) * (1 / α) + 1 / q = 0 by
          rw [hq, one_div, one_div, inv_div]; field_simp; ring,
        ENNReal.rpow_zero, mul_one]
  set F := fun x => (f x ^ α * g x ^ (1 - α)) ^ (1 / α) with hF
  set G := fun x => g x ^ (1 / q) with hG
  have hFm : AEMeasurable F μ := (hprodm).pow_const _
  have hGm : AEMeasurable G μ := hg.pow_const _
  have hFpow : (∫⁻ x, F x ^ α ∂μ) = R := by
    rw [hR]; refine lintegral_congr fun x => ?_
    rw [hF, ← ENNReal.rpow_mul, one_div_mul_cancel hα0.ne', ENNReal.rpow_one]
  have hGpow : (∫⁻ x, G x ^ q ∂μ) = Sg := by
    rw [hSg]; refine lintegral_congr fun x => ?_
    rw [hG, ← ENNReal.rpow_mul, one_div_mul_cancel hqpos.ne', ENNReal.rpow_one]
  have hFG : (∫⁻ x, (F * G) x ∂μ) = Sf :=
    (lintegral_congr_ae (by filter_upwards [hae] with x hx using hx)).trans hSf.symm
  have hHold := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq hFm hGm
  rw [hFG, hFpow, hGpow] at hHold
  -- Raise to `α`, cancel the `Sg` powers.
  have hkey : Sf ^ α ≤ R * Sg ^ (α - 1) :=
    calc Sf ^ α ≤ (R ^ (1 / α) * Sg ^ (1 / q)) ^ α := ENNReal.rpow_le_rpow hHold hα0.le
      _ = R * Sg ^ (α - 1) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hα0.le, ← ENNReal.rpow_mul,
            ← ENNReal.rpow_mul, one_div_mul_cancel hα0.ne', ENNReal.rpow_one]
          congr 1
          rw [hq, one_div, inv_div]; field_simp
  calc Sf ^ α * Sg ^ (1 - α)
      ≤ R * Sg ^ (α - 1) * Sg ^ (1 - α) := _root_.mul_le_mul_left hkey _
    _ = R := by
        rw [mul_assoc, ← ENNReal.rpow_add _ _ hSg0 hSgtop,
          show (α - 1) + (1 - α) = 0 by ring, ENNReal.rpow_zero, mul_one]

/-- The Hellinger integral relative to a reference measure `ρ`:
    `∫ (dμ/dρ)^α (dν/dρ)^{1-α} dρ`. It equals `hellingerIntegral α μ ν` for `μ ≪ ν ≪ ρ`
    (`hRen_ref_indep`). -/
noncomputable def hRen (α : ℝ) (ρ μ ν : Measure Ω) : ℝ≥0∞ :=
  ∫⁻ x, (μ.rnDeriv ρ x) ^ α * (ν.rnDeriv ρ x) ^ (1 - α) ∂ρ

end Continuous
