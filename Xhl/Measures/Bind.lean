import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Kernel.Composition.MeasureComp

/-!
# Bind identities

Facts about the Giry bind used by the equivalence soundness proofs and the banded DP-FTRL
window identity:

* `bind_map_eq` — binding over an image measure;
* `prod_bind_eq` — binding over a product measure, one coordinate at a time;
* `pi_fin_succ_eq_map_cons`, `measurable_fin_cons` — `m + 1` independent draws as the
  first draw and the `m` others.
-/

open MeasureTheory ProbabilityTheory

namespace Continuous

variable {Θ Ω : Type*} [MeasurableSpace Θ] [MeasurableSpace Ω]

/-- Binding over an image measure. -/
lemma bind_map_eq {X : Type*} [MeasurableSpace X] {ν : Measure Ω} {φ : Ω → Θ} (hφ : Measurable φ)
    {κ : Θ → Measure X} (hκ : Measurable κ) : (ν.map φ).bind κ = ν.bind (fun ω => κ (φ ω)) := by
  ext A hA
  have hκφ : Measurable (fun ω => κ (φ ω)) := hκ.comp hφ
  rw [Measure.bind_apply hA hκ.aemeasurable, Measure.bind_apply hA hκφ.aemeasurable,
    lintegral_map (f := fun a => κ a A) ((Measure.measurable_coe hA).comp hκ) hφ]

/-- Binding over a product measure, one coordinate at a time. -/
lemma prod_bind_eq {X : Type*} [MeasurableSpace X] (μ : Measure Θ) (ν : Measure Ω) [SFinite ν]
    {f : Θ × Ω → Measure X} (hf : Measurable f) :
    (μ.prod ν).bind f = μ.bind (fun a => ν.bind (fun b => f (a, b))) := by
  have hfa : ∀ a, Measurable (fun b => f (a, b)) := fun a => hf.comp measurable_prodMk_left
  have hA : Measurable (fun a => ν.bind (fun b => f (a, b))) := by
    refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
    simp_rw [Measure.bind_apply hs (hfa _).aemeasurable]
    exact (Measure.measurable_coe hs |>.comp hf).lintegral_prod_right'
  ext s hs
  rw [Measure.bind_apply hs hf.aemeasurable, Measure.bind_apply hs hA.aemeasurable,
    lintegral_prod (fun z => f z s) ((Measure.measurable_coe hs).comp hf).aemeasurable]
  simp_rw [Measure.bind_apply hs (hfa _).aemeasurable]

/-- `m + 1` independent draws: the first, then the `m` others. -/
lemma pi_fin_succ_eq_map_cons {E : Type*} [MeasurableSpace E] (μ : Measure E) [SigmaFinite μ]
    (m : ℕ) :
    Measure.pi (fun _ : Fin (m + 1) => μ)
      = (μ.prod (Measure.pi (fun _ : Fin m => μ))).map (fun p => Fin.cons p.1 p.2) := by
  have h := (measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => μ) 0).symm
  rw [← h.map_eq]
  congr 1
  funext p
  exact Fin.insertNth_zero' p.1 p.2

lemma measurable_fin_cons {E : Type*} [MeasurableSpace E] (m : ℕ) :
    Measurable (fun p : E × (Fin m → E) => (Fin.cons p.1 p.2 : Fin (m + 1) → E)) := by
  refine measurable_pi_lambda _ fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using measurable_fst
  · simp only [Fin.cons_succ]; exact (measurable_pi_apply j).comp measurable_snd

end Continuous
