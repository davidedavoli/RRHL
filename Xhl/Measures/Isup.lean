import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Data.ENNReal.Operations

/-!
# Scott-continuity of measure evaluation

For a monotone sequence of measures, evaluating the supremum at a measurable set
commutes with taking the supremum of the values.
-/

open MeasureTheory

namespace Continuous

/-- Evaluation at a measurable set commutes with suprema of monotone sequences. -/
lemma iSup_measure_apply {α : Type*} [MeasurableSpace α]
    {μ : ℕ → Measure α} (hmon : Monotone μ)
    {s : Set α} (hs : MeasurableSet s) :
    (⨆ n, μ n) s = ⨆ n, μ n s := by
  apply le_antisymm
  · -- Build an auxiliary measure ν₀ = (⨆ n, (μ n).toOuterMeasure).toMeasure hcar
    -- such that ⨆ n, μ n ≤ ν₀ and ν₀ s = ⨆ n, μ n s.
    have hcar : ‹MeasurableSpace α› ≤ (⨆ n, (μ n).toOuterMeasure).caratheodory := by
      intro t ht r
      simp only [OuterMeasure.iSup_apply, Measure.coe_toOuterMeasure]
      have each : ∀ k, μ k r = μ k (r ∩ t) + μ k (r \ t) :=
        fun k => (measure_inter_add_sdiff r ht (μ := μ k)).symm
      simp_rw [each]
      exact (ENNReal.iSup_add_iSup_of_monotone
        (fun a b hab => Measure.le_iff'.mp (hmon hab) (r ∩ t))
        (fun a b hab => Measure.le_iff'.mp (hmon hab) (r \ t))).symm
    have hdom : ∀ k, μ k ≤ (⨆ n, (μ n).toOuterMeasure).toMeasure hcar :=
      fun k => Measure.le_iff'.mpr fun t => by
        simp only [← Measure.coe_toOuterMeasure (μ k)]
        exact ((le_iSup (fun n => (μ n).toOuterMeasure) k) t).trans
          (le_toMeasure_apply _ hcar t)
    calc (⨆ n, μ n) s
        ≤ (⨆ n, (μ n).toOuterMeasure).toMeasure hcar s :=
            Measure.le_iff'.mp (iSup_le hdom) s
      _ = (⨆ n, (μ n).toOuterMeasure) s := toMeasure_apply _ hcar hs
      _ = ⨆ n, (μ n).toOuterMeasure s := OuterMeasure.iSup_apply _ _
      _ = ⨆ n, μ n s := by simp only [Measure.coe_toOuterMeasure]
  · exact iSup_le fun n => Measure.le_iff'.mp (le_iSup μ n) s

end Continuous
