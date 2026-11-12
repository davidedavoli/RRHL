import Xhl.Divergence.ChainUncond
import Xhl.Divergence.Tensor

/-!
# Mixtures along a common mixing measure

* `add_bind'`, `smul_bind'` — `bind` is linear
  in the mixing measure.
* `hellingerIntegral_bind_le_const` — two mixtures of Markov kernels along the same probability
  measure have Hellinger integral at most any common bound `C ≠ 0` on the components
  (Proposition A.20, item 3).
-/

open MeasureTheory ProbabilityTheory ENNReal

namespace Continuous

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

lemma add_bind' (μ₁ μ₂ : Measure A) {f : A → Measure B} (hf : Measurable f) :
    (μ₁ + μ₂).bind f = μ₁.bind f + μ₂.bind f := by
  ext s hs
  rw [Measure.add_apply, Measure.bind_apply hs hf.aemeasurable,
    Measure.bind_apply hs hf.aemeasurable, Measure.bind_apply hs hf.aemeasurable,
    lintegral_add_measure]

lemma smul_bind' (c : ℝ≥0∞) (μ : Measure A) {f : A → Measure B} (hf : Measurable f) :
    (c • μ).bind f = c • μ.bind f := by
  ext s hs
  rw [Measure.smul_apply, Measure.bind_apply hs hf.aemeasurable,
    Measure.bind_apply hs hf.aemeasurable, lintegral_smul_measure]

lemma bind_isProb (ρ : Measure A) [IsProbabilityMeasure ρ] (K : Kernel A B) [IsMarkovKernel K] :
    IsProbabilityMeasure (ρ.bind K) := by
  refine ⟨?_⟩
  rw [Measure.bind_apply MeasurableSet.univ K.measurable.aemeasurable]
  simp

/-- Mixtures along a common probability measure: a common bound `C ≠ 0` on
    `H_α(K a ‖ L a)` bounds `H_α(ρ.bind K ‖ ρ.bind L)`. -/
theorem hellingerIntegral_bind_le_const {α : ℝ} (hα : 1 < α) (ρ : Measure A) [IsProbabilityMeasure ρ]
    (K L : Kernel A B) [IsMarkovKernel K] [IsMarkovKernel L] {C : ℝ≥0∞} (hC : C ≠ 0)
    (h : ∀ a, hellingerIntegral α (K a) (L a) ≤ C) :
    hellingerIntegral α (ρ.bind K) (ρ.bind L) ≤ C := by
  have := bind_isProb ρ K
  have := bind_isProb ρ L
  have hstep : ∀ a, weightedHellingerIntegral α (fun _ => (1 : ℝ≥0∞)) (K a) (L a) ≤ C := fun a => by
    rw [weightedHellingerIntegral_one]; exact h a
  have hb := weightedHellingerIntegral_bind_le hα ρ ρ K L GoodWeight.one
    (fun _ => C) hstep
  rw [weightedHellingerIntegral_one] at hb
  have hc : weightedHellingerIntegral α (fun _ : A => C) ρ ρ = C := by
    have := weightedHellingerIntegral_const_mul (α := α) C hC (fun _ : A => (1 : ℝ≥0∞)) measurable_const ρ ρ
    simp only [mul_one] at this
    rw [this, weightedHellingerIntegral_one, hellingerIntegral_self_prob, mul_one]
  exact hb.trans (le_of_eq hc)

section BindHelpers

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

/-- A product measure pushed forward along a two-variable map is a `bind`. -/
lemma prod_map_eq_bind {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] (ρ : Measure A) (ν : Measure B) [SFinite ν] [SFinite ρ]
    (g : A × B → C) (hg : Measurable g) :
    (ρ.prod ν).map g = ρ.bind (fun z => ν.map (fun ξ => g (z, ξ))) := by
  set K : Kernel A C :=
    Kernel.map ((Kernel.id : Kernel A A) ×ₖ Kernel.const A ν) g with hK
  have hKapp : ∀ z, K z = ν.map (fun ξ => g (z, ξ)) := by
    intro z
    rw [hK, Kernel.map_apply _ hg, Kernel.prod_apply, Kernel.id_apply, Kernel.const_apply,
      Measure.dirac_prod, Measure.map_map hg measurable_prodMk_left]
    rfl
  ext s hs
  rw [Measure.map_apply hg hs, Measure.prod_apply (hg hs),
    show (fun z => ν.map (fun ξ => g (z, ξ))) = ⇑K from funext fun z => (hKapp z).symm,
    Measure.bind_apply hs K.aemeasurable]
  refine lintegral_congr (fun z => ?_)
  have hmk : Measurable (fun ξ : B => g (z, ξ)) := hg.comp measurable_prodMk_left
  rw [hKapp z, Measure.map_apply hmk hs]
  rfl

end BindHelpers

end Continuous
