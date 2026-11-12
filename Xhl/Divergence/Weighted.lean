import Xhl.Divergence.MapLe

/-!
# The weighted Hellinger integral — weights and data processing

A constant factor in the weight comes out (`weightedHellingerIntegral_const_mul`), and
data processing holds for a weight on the image (`weightedHellingerIntegral_map_le`).
The chain rule is `weightedHellingerIntegral_bind_le` (`ChainUncond.lean`).
-/

open MeasureTheory ProbabilityTheory ENNReal

namespace Continuous

section Def

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A constant factor in the weight comes out. -/
lemma weightedHellingerIntegral_const_mul {α : ℝ} (c : ℝ≥0∞) (hc : c ≠ 0) (w : Ω → ℝ≥0∞) (hw : Measurable w)
    (μ ν : Measure Ω) : weightedHellingerIntegral α (fun x => c * w x) μ ν = c * weightedHellingerIntegral α w μ ν := by
  by_cases h : μ ≪ ν
  · rw [weightedHellingerIntegral_of_ac _ h, weightedHellingerIntegral_of_ac _ h,
      ← lintegral_const_mul (f := fun x => (μ.rnDeriv ν x) ^ α * w x) c
        (((Measure.measurable_rnDeriv μ ν).pow_const α).mul hw)]
    congr 1; funext x; ring
  · rw [weightedHellingerIntegral_of_not_ac _ h, weightedHellingerIntegral_of_not_ac _ h, ENNReal.mul_top hc]

end Def

section Map

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']

/-- A measurable weight, positive and finite at each point (no uniform bound). -/
structure GoodWeight (w : Ω → ℝ≥0∞) : Prop where
  meas : Measurable w
  ne_zero : ∀ x, w x ≠ 0
  ne_top : ∀ x, w x ≠ ⊤

lemma GoodWeight.comp {w : Ω' → ℝ≥0∞} (hw : GoodWeight w) {f : Ω → Ω'} (hf : Measurable f) :
    GoodWeight (w ∘ f) :=
  ⟨hw.meas.comp hf, fun x => hw.ne_zero (f x), fun x => hw.ne_top (f x)⟩

lemma GoodWeight.one : GoodWeight (fun _ : Ω => (1 : ℝ≥0∞)) :=
  ⟨measurable_const, fun _ => one_ne_zero, fun _ => one_ne_top⟩

/-- A bounded weight reweights a finite measure to a finite one. -/
lemma isFiniteMeasure_withDensity_of_bdd {w : Ω → ℝ≥0∞}
    (hbdd : ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ x, w x ≤ C) (μ : Measure Ω) [IsFiniteMeasure μ] :
    IsFiniteMeasure (μ.withDensity w) := by
  obtain ⟨C, hC, hle⟩ := hbdd
  refine isFiniteMeasure_withDensity ?_
  refine ne_top_of_le_ne_top (ENNReal.mul_ne_top hC (measure_ne_top μ Set.univ)) ?_
  calc ∫⁻ x, w x ∂μ ≤ ∫⁻ _, C ∂μ := lintegral_mono hle
    _ = C * μ Set.univ := lintegral_const C

/-- A pointwise-finite weight reweights a σ-finite measure to a σ-finite one. -/
lemma sigmaFinite_withDensity_of_good {w : Ω → ℝ≥0∞} (hw : GoodWeight w)
    (μ : Measure Ω) [SigmaFinite μ] : SigmaFinite (μ.withDensity w) :=
  SigmaFinite.withDensity_of_ne_top' hw.ne_top

lemma ac_withDensity_iff {w : Ω → ℝ≥0∞} (hw : GoodWeight w) (μ ν : Measure Ω) :
    μ.withDensity w ≪ ν.withDensity w ↔ μ ≪ ν := by
  have h1 : ∀ ρ : Measure Ω, ρ ≪ ρ.withDensity w := fun ρ =>
    withDensity_absolutelyContinuous' hw.meas.aemeasurable (ae_of_all _ hw.ne_zero)
  constructor
  · intro h; exact (h1 μ).trans (h.trans (withDensity_absolutelyContinuous ν w))
  · intro h; exact (withDensity_absolutelyContinuous μ w).trans (h.trans (h1 ν))

/-- Under `μ ≪ ν`, the weighted integral is the Hellinger integral of the reweighted
    measures. -/
theorem weightedHellingerIntegral_eq_hellingerIntegral_withDensity {α : ℝ} (hα : 1 < α) {w : Ω → ℝ≥0∞} (hw : GoodWeight w)
    (μ ν : Measure Ω) [SigmaFinite μ] [SigmaFinite ν] (h : μ ≪ ν) :
    weightedHellingerIntegral α w μ ν = hellingerIntegral α (μ.withDensity w) (ν.withDensity w) := by
  have := sigmaFinite_withDensity_of_good hw μ
  have := sigmaFinite_withDensity_of_good hw ν
  · have hac : μ.withDensity w ≪ ν.withDensity w := (ac_withDensity_iff hw μ ν).mpr h
    rw [weightedHellingerIntegral_of_ac _ h, hellingerIntegral_eq_lintegral_rnDeriv _ _ hac,
      lintegral_withDensity_eq_lintegral_mul _ hw.meas
        ((Measure.measurable_rnDeriv _ _).pow_const α)]
    refine lintegral_congr_ae ?_
    have hl := Measure.rnDeriv_withDensity_left (μ := μ) (ν := ν) hw.meas.aemeasurable
      (ae_of_all _ hw.ne_top)
    have hr := Measure.rnDeriv_withDensity_right (μ.withDensity w) ν hw.meas.aemeasurable
      (ae_of_all _ hw.ne_zero) (ae_of_all _ hw.ne_top)
    filter_upwards [hl, hr] with x hlx hrx
    simp only [Pi.mul_apply]
    rw [hrx, hlx, ← mul_assoc, ENNReal.inv_mul_cancel (hw.ne_zero x) (hw.ne_top x), one_mul,
      mul_comm]

lemma map_withDensity_comp {w : Ω' → ℝ≥0∞} (hw : Measurable w) {f : Ω → Ω'} (hf : Measurable f)
    (μ : Measure Ω) : (μ.withDensity (w ∘ f)).map f = (μ.map f).withDensity w := by
  ext s hs
  rw [Measure.map_apply hf hs, withDensity_apply _ (hf hs), withDensity_apply _ hs,
    setLIntegral_map hs hw hf]
  rfl

/-- **Weighted data processing** under a measurable map, for a weight on the image. -/
theorem weightedHellingerIntegral_map_le {α : ℝ} (hα : 1 < α) {w : Ω' → ℝ≥0∞} (hw : GoodWeight w)
    (hbdd : ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ x, w x ≤ C)
    {f : Ω → Ω'} (hf : Measurable f) (μ ν : Measure Ω) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    weightedHellingerIntegral α w (μ.map f) (ν.map f) ≤ weightedHellingerIntegral α (w ∘ f) μ ν := by
  by_cases h : μ ≪ ν
  swap
  · rw [weightedHellingerIntegral_of_not_ac _ h]; exact le_top
  have hwf := hw.comp hf
  have hbddf : ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ x, (w ∘ f) x ≤ C :=
    let ⟨C, hC, hle⟩ := hbdd; ⟨C, hC, fun x => hle (f x)⟩
  have := isFiniteMeasure_withDensity_of_bdd hbddf μ
  have := isFiniteMeasure_withDensity_of_bdd hbddf ν
  rw [weightedHellingerIntegral_eq_hellingerIntegral_withDensity hα hw _ _ (h.map hf),
    weightedHellingerIntegral_eq_hellingerIntegral_withDensity hα hwf _ _ h,
    ← map_withDensity_comp hw.meas hf, ← map_withDensity_comp hw.meas hf]
  exact hellingerIntegral_map_le hα hf _ _ ((ac_withDensity_iff hwf μ ν).mpr h)

end Map

end Continuous
