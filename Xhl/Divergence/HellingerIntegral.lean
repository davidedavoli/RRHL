import Xhl.Divergence.HRen

/-!
# The weighted Hellinger integral and the budget `hellingerIntegral`

Definition 3.1 of the paper:

    weightedHellingerIntegral α w μ ν = ∫ (dμ/dν)^α · w dν   if μ ≪ ν,   and ⊤ otherwise.

`hellingerIntegral α μ ν` (the paper's `H_α`) is its instance at `w ≡ 1`. The `⊤` case is
needed for weak duality (Proposition 4.2) when the weight vanishes.
`hRen_ref_indep` relates it to the reference form `hRen α ρ μ ν` of `HRen.lean`, used to
evaluate the Gaussian closed form against Lebesgue measure.
-/

open MeasureTheory ENNReal

namespace Continuous

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The weighted Hellinger integral** (Definition 3.1): `∫ (dμ/dν)^α · w dν` when
    `μ ≪ ν`, and `⊤` otherwise. -/
noncomputable def weightedHellingerIntegral (α : ℝ) (w : Ω → ℝ≥0∞) (μ ν : Measure Ω) :
    ℝ≥0∞ := by
  classical
  exact if μ ≪ ν then ∫⁻ x, (μ.rnDeriv ν x) ^ α * w x ∂ν else ⊤

lemma weightedHellingerIntegral_of_ac {α : ℝ} (w : Ω → ℝ≥0∞) {μ ν : Measure Ω} (h : μ ≪ ν) :
    weightedHellingerIntegral α w μ ν = ∫⁻ x, (μ.rnDeriv ν x) ^ α * w x ∂ν := by
  classical
  simp [weightedHellingerIntegral, h]

lemma weightedHellingerIntegral_of_not_ac {α : ℝ} (w : Ω → ℝ≥0∞) {μ ν : Measure Ω}
    (h : ¬ μ ≪ ν) : weightedHellingerIntegral α w μ ν = ⊤ := by
  classical
  simp [weightedHellingerIntegral, h]

/-- **The Hellinger integral** `H_α`, the judgment budget: the weighted integral at
    weight `1`. -/
noncomputable def hellingerIntegral (α : ℝ) (μ ν : Measure Ω) : ℝ≥0∞ :=
  weightedHellingerIntegral α (fun _ => 1) μ ν

/-- At weight `1` the weighted integral is the Hellinger integral. -/
theorem weightedHellingerIntegral_one {α : ℝ} (μ ν : Measure Ω) :
    weightedHellingerIntegral α (fun _ => 1) μ ν = hellingerIntegral α μ ν := rfl

/-- `hellingerIntegral` is the ν-based integral `∫ (dμ/dν)^α ∂ν` when `μ ≪ ν`. -/
theorem hellingerIntegral_eq_lintegral_rnDeriv {α : ℝ} (μ ν : Measure Ω) (hμν : μ ≪ ν) :
    hellingerIntegral α μ ν = ∫⁻ x, (μ.rnDeriv ν x) ^ α ∂ν := by
  rw [hellingerIntegral, weightedHellingerIntegral_of_ac _ hμν]
  simp only [mul_one]

/-- If `¬ μ ≪ ν` then `hellingerIntegral α μ ν = ⊤`. -/
theorem hellingerIntegral_eq_top_of_not_ac {α : ℝ} (μ ν : Measure Ω) (hnac : ¬ μ ≪ ν) :
    hellingerIntegral α μ ν = ⊤ :=
  weightedHellingerIntegral_of_not_ac _ hnac

/-- The Hellinger integral of a measure against itself is its total mass. -/
lemma hellingerIntegral_self {α : ℝ} (μ : Measure Ω) [SigmaFinite μ] : hellingerIntegral α μ μ = μ Set.univ := by
  rw [hellingerIntegral_eq_lintegral_rnDeriv μ μ Measure.AbsolutelyContinuous.rfl,
    lintegral_congr_ae (μ.rnDeriv_self.mono (fun x hx => by rw [hx, ENNReal.one_rpow])),
    lintegral_one]

/-- The Hellinger integral of a probability measure against itself is `1`. -/
lemma hellingerIntegral_self_prob {α : ℝ} (μ : Measure Ω) [IsProbabilityMeasure μ] : hellingerIntegral α μ μ = 1 := by
  rw [hellingerIntegral_self, measure_univ]

/-- For `μ ≪ ν ≪ ρ`, the reference form equals `∫ (dμ/dν)^α ∂ν`. -/
theorem hRen_eq_lintegral_rnDeriv {α : ℝ} (hα : 1 < α)
    (μ ν ρ : Measure Ω) [SigmaFinite μ] [SigmaFinite ν] [SigmaFinite ρ]
    (hμν : μ ≪ ν) (hνρ : ν ≪ ρ) :
    hRen α ρ μ ν = ∫⁻ x, (μ.rnDeriv ν x) ^ α ∂ν := by
  have hα0 : (0 : ℝ) < α := by linarith
  rw [hRen]
  have hpt : (fun x => (μ.rnDeriv ρ x) ^ α * (ν.rnDeriv ρ x) ^ (1 - α))
      =ᵐ[ρ] (fun x => ν.rnDeriv ρ x * (μ.rnDeriv ν x) ^ α) := by
    filter_upwards [Measure.rnDeriv_mul_rnDeriv (κ := ρ) hμν,
      μ.rnDeriv_lt_top ρ, ν.rnDeriv_lt_top ρ] with x hchain hμfin hνfin
    simp only [Pi.mul_apply] at hchain
    rcases eq_or_ne (ν.rnDeriv ρ x) 0 with h0 | h0
    · have hμ0 : μ.rnDeriv ρ x = 0 := by rw [← hchain, h0, mul_zero]
      rw [hμ0, h0, ENNReal.zero_rpow_of_pos hα0, zero_mul, zero_mul]
    · have hμνfin : μ.rnDeriv ν x ≠ ⊤ := by
        intro htop
        rw [htop] at hchain
        rw [ENNReal.top_mul h0] at hchain
        exact (hchain ▸ hμfin).ne rfl
      rw [← hchain,
        ENNReal.mul_rpow_of_ne_top hμνfin hνfin.ne,
        mul_assoc, ← ENNReal.rpow_add _ _ h0 hνfin.ne,
        show α + (1 - α) = 1 by ring, ENNReal.rpow_one, mul_comm]
  rw [lintegral_congr_ae hpt,
    lintegral_rnDeriv_mul hνρ ((Measure.measurable_rnDeriv μ ν).pow_const α).aemeasurable]

/-- **Reference independence** of `hRen`: for `μ ≪ ν ≪ ρ` it is `hellingerIntegral α μ ν`. -/
theorem hRen_ref_indep {α : ℝ} (hα : 1 < α)
    (μ ν ρ : Measure Ω) [SigmaFinite μ] [SigmaFinite ν] [SigmaFinite ρ]
    (hμν : μ ≪ ν) (hνρ : ν ≪ ρ) :
    hRen α ρ μ ν = hellingerIntegral α μ ν := by
  rw [hRen_eq_lintegral_rnDeriv hα μ ν ρ hμν hνρ, ← hellingerIntegral_eq_lintegral_rnDeriv μ ν hμν]

end Continuous
