import Mathlib.MeasureTheory.Function.ConditionalExpectation.RadonNikodym
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Xhl.Divergence.HellingerIntegral

/-!
# Data processing under a measurable map

`hellingerIntegral_map_le : hellingerIntegral α (μ.map f) (ν.map f) ≤ hellingerIntegral α μ ν`
for any measurable `f` and `μ ≪ ν` (Proposition A.20, item 2). Proof by conditional Jensen:
the pushforward density is a conditional expectation of `dμ/dν` (`toReal_rnDeriv_map`), and
`x ↦ x^α` is convex.
-/

open MeasureTheory ENNReal Set

namespace Continuous

variable {𝓧 𝓨 : Type*} [m𝓧 : MeasurableSpace 𝓧] [m𝓨 : MeasurableSpace 𝓨]

/-- **Data processing under a measurable map**, for `μ ≪ ν`. -/
theorem hellingerIntegral_map_le {α : ℝ} (hα : 1 < α)
    {f : 𝓧 → 𝓨} (hf : Measurable f) (μ ν : Measure 𝓧)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμν : μ ≪ ν) :
    hellingerIntegral α (μ.map f) (ν.map f) ≤ hellingerIntegral α μ ν := by
  have hα0 : (0 : ℝ) < α := by linarith
  have : IsFiniteMeasure (μ.map f) := μ.isFiniteMeasure_map f
  have : IsFiniteMeasure (ν.map f) := ν.isFiniteMeasure_map f
  have hmapac : μ.map f ≪ ν.map f := hμν.map hf
  have hm'le : MeasurableSpace.comap f m𝓨 ≤ m𝓧 := hf.comap_le
  have : IsFiniteMeasure (ν.trim hm'le) :=
    ⟨by rw [trim_measurableSet_eq hm'le MeasurableSet.univ]; exact measure_lt_top ν _⟩
  have hqmeas : Measurable (fun x => (μ.rnDeriv ν x).toReal) :=
    (Measure.measurable_rnDeriv _ _).ennreal_toReal
  rw [hellingerIntegral_eq_lintegral_rnDeriv (μ.map f) (ν.map f) hmapac,
    hellingerIntegral_eq_lintegral_rnDeriv μ ν hμν,
    lintegral_map ((Measure.measurable_rnDeriv _ _).pow_const α) hf]
  rcases eq_or_ne (∫⁻ x, (μ.rnDeriv ν x) ^ α ∂ν) ⊤ with hRtop | hRfin
  · rw [hRtop]; exact le_top
  have hR_pt : (fun x => (μ.rnDeriv ν x) ^ α)
      =ᵐ[ν] fun x => ENNReal.ofReal ((μ.rnDeriv ν x).toReal ^ α) := by
    filter_upwards [μ.rnDeriv_lt_top ν] with x hx
    rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hα0.le, ENNReal.ofReal_toReal hx.ne]
  have hL_pt : (fun x => ((μ.map f).rnDeriv (ν.map f) (f x)) ^ α)
      =ᵐ[ν] fun x => ENNReal.ofReal (((μ.map f).rnDeriv (ν.map f) (f x)).toReal ^ α) := by
    have hfin : ∀ᵐ x ∂ν, (μ.map f).rnDeriv (ν.map f) (f x) ≠ ⊤ :=
      (ae_map_iff hf.aemeasurable
        (measurableSet_lt (Measure.measurable_rnDeriv _ _) measurable_const)).mp
        (by filter_upwards [(μ.map f).rnDeriv_lt_top (ν.map f)] with y hy using hy) |>.mono
        fun x hx => hx.ne
    filter_upwards [hfin] with x hx
    rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hα0.le, ENNReal.ofReal_toReal hx]
  have hqα_int : Integrable (fun x => (μ.rnDeriv ν x).toReal ^ α) ν := by
    refine (lintegral_ofReal_ne_top_iff_integrable ((hqmeas.pow_const α).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => by positivity)).mp ?_
    rw [← lintegral_congr_ae hR_pt]; exact hRfin
  have hq_int : Integrable (fun x => (μ.rnDeriv ν x).toReal) ν :=
    Measure.integrable_toReal_rnDeriv
  -- conditional Jensen
  have hcontrpow : Continuous (fun x : ℝ => x ^ α) :=
    continuous_iff_continuousAt.mpr fun x => Real.continuousAt_rpow_const x α (Or.inr hα0.le)
  have hjensen := (convexOn_rpow hα.le).map_condExp_le (μ := ν)
    (f := fun x => (μ.rnDeriv ν x).toReal) (φ := fun x => x ^ α) hm'le
    (hcontrpow.lowerSemicontinuous.lowerSemicontinuousOn (Ici 0))
    (Filter.Eventually.of_forall fun x => Set.mem_Ici.mpr ENNReal.toReal_nonneg)
    isClosed_Ici hq_int hqα_int
  have hcn : 0 ≤ᵐ[ν] (ν[fun y => (μ.rnDeriv ν y).toReal | MeasurableSpace.comap f m𝓨]) :=
    condExp_nonneg (Filter.Eventually.of_forall fun x => ENNReal.toReal_nonneg)
  have hcondint : Integrable
      (fun x => (ν[fun y => (μ.rnDeriv ν y).toReal | MeasurableSpace.comap f m𝓨] x) ^ α) ν := by
    have hg : Integrable
        (ν[fun y => (μ.rnDeriv ν y).toReal ^ α | MeasurableSpace.comap f m𝓨]) ν :=
      integrable_condExp
    refine hg.mono' (hcontrpow.comp_aestronglyMeasurable
        (stronglyMeasurable_condExp.mono hm'le).aestronglyMeasurable) ?_
    filter_upwards [hjensen, hcn] with x hx hcnx using by
      rw [Real.norm_of_nonneg (Real.rpow_nonneg hcnx α)]; exact hx
  rw [lintegral_congr_ae hL_pt, lintegral_congr_ae hR_pt,
    ← ofReal_integral_eq_lintegral_ofReal hqα_int
      (Filter.Eventually.of_forall fun x => Real.rpow_nonneg ENNReal.toReal_nonneg α)]
  have hLeq : (fun x => ((μ.map f).rnDeriv (ν.map f) (f x)).toReal ^ α)
      =ᵐ[ν] fun x => (ν[fun y => (μ.rnDeriv ν y).toReal | MeasurableSpace.comap f m𝓨] x) ^ α := by
    filter_upwards [MeasureTheory.toReal_rnDeriv_map hμν hf] with x hx; rw [hx]
  rw [← ofReal_integral_eq_lintegral_ofReal (hcondint.congr hLeq.symm)
    (Filter.Eventually.of_forall fun x => Real.rpow_nonneg ENNReal.toReal_nonneg α)]
  refine ofReal_le_ofReal ?_
  calc ∫ x, ((μ.map f).rnDeriv (ν.map f) (f x)).toReal ^ α ∂ν
      = ∫ x, (ν[fun y => (μ.rnDeriv ν y).toReal | MeasurableSpace.comap f m𝓨] x) ^ α ∂ν :=
        integral_congr_ae hLeq
    _ ≤ ∫ x, (ν[fun y => (μ.rnDeriv ν y).toReal ^ α | MeasurableSpace.comap f m𝓨] x) ∂ν :=
        integral_mono_ae hcondint integrable_condExp hjensen
    _ = ∫ x, (μ.rnDeriv ν x).toReal ^ α ∂ν := integral_condExp hm'le

end Continuous
