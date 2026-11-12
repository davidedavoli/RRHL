import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.MeasurableLIntegral
import Xhl.Divergence.WeightedDual
import Xhl.Divergence.MapLe

/-!
# The chain rule of the Hellinger integral, by duality

`weightedHellingerIntegral_bind_le` (Theorem 3.3): the weighted chain rule over `bind`,
for arbitrary measurable spaces. Proof by duality (`WeightedDual.lean`, Theorem 3.2): an
admissible pair of tests `(k₁, k₂)` on `B` is integrated through the kernels,
`k₁' a = ∫ k₁ dM(a)`, `k₂' a = ∫ k₂ dN(a)`, which by weak duality on each fibre is admissible
for the weight `w'` on `A`.

`hellingerIntegral_compProd_le` is the unweighted bound over a composition-product, with the
supremum of the fibre integrals.
-/

open MeasureTheory ProbabilityTheory ENNReal

namespace Continuous

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

/-- **Weighted chain rule for `bind`** (Theorem 3.3): if every fibre has weighted Hellinger
    integral at most `w' a`, the composition has weighted integral at most the
    `w'`-weighted integral of the first component. -/
theorem weightedHellingerIntegral_bind_le {α : ℝ} (hα : 1 < α)
    (μ ν : Measure A) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (M N : Kernel A B) [IsFiniteKernel M] [IsFiniteKernel N]
    {w : B → ℝ≥0∞} (hw : GoodWeight w)
    (w' : A → ℝ≥0∞)
    (hstep : ∀ a, weightedHellingerIntegral α w (M a) (N a) ≤ w' a) :
    weightedHellingerIntegral α w (μ.bind M) (ν.bind N) ≤ weightedHellingerIntegral α w' μ ν := by
  have : IsFiniteMeasure (μ.bind M) := inferInstanceAs (IsFiniteMeasure (M ∘ₘ μ))
  have : IsFiniteMeasure (ν.bind N) := inferInstanceAs (IsFiniteMeasure (N ∘ₘ ν))
  rw [weightedHellingerIntegral_eq_testSupW hα hw]
  refine iSup_le fun k₁ => iSup_le fun k₂ => iSup_le fun h₁ => iSup_le fun h₂ =>
    iSup_le fun hadm => ?_
  rw [Measure.lintegral_bind M.measurable.aemeasurable h₁.aemeasurable,
    Measure.lintegral_bind N.measurable.aemeasurable h₂.aemeasurable]
  refine (le_testSupW h₁.lintegral_kernel h₂.lintegral_kernel fun a => ?_).trans
    (testSupW_le_weightedHellingerIntegral hα w' μ ν)
  calc (∫⁻ b, k₁ b ∂(M a)) ^ α * (∫⁻ b, k₂ b ∂(N a)) ^ (1 - α)
      ≤ testSupW α w (M a) (N a) := le_testSupW h₁ h₂ hadm
    _ ≤ weightedHellingerIntegral α w (M a) (N a) := testSupW_le_weightedHellingerIntegral hα _ _ _
    _ ≤ w' a := hstep a

/-- Unweighted chain bound on the composition-product, with the supremum of the fibre
    integrals. -/
theorem hellingerIntegral_compProd_le {α : ℝ} (hα : 1 < α)
    (μ ν : Measure A) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (M N : Kernel A B) [IsFiniteKernel M] [IsFiniteKernel N] (hμν : μ ≪ ν) :
    hellingerIntegral α (μ ⊗ₘ M) (ν ⊗ₘ N) ≤ hellingerIntegral α μ ν * ⨆ a, hellingerIntegral α (M a) (N a) := by
  set S : ℝ≥0∞ := ⨆ a, hellingerIntegral α (M a) (N a) with hS
  have hfib : ∀ (K : Kernel A B) [IsFiniteKernel K] (a : A),
      (Kernel.id ×ₖ K) a = (K a).map (Prod.mk a) := fun K _ a => by
    ext s hs
    rw [Kernel.id_prod_apply' _ _ hs, Measure.map_apply measurable_prodMk_left hs]
  have hbdd1 : ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ _ : A × B, (1 : ℝ≥0∞) ≤ C := ⟨1, one_ne_top, fun _ => le_rfl⟩
  have hstep : ∀ a, weightedHellingerIntegral α (fun _ : A × B => (1 : ℝ≥0∞))
      ((Kernel.id ×ₖ M) a) ((Kernel.id ×ₖ N) a) ≤ (fun _ => S) a := fun a => by
    rw [hfib M, hfib N]
    have h := weightedHellingerIntegral_map_le hα GoodWeight.one hbdd1
      (measurable_prodMk_left (x := a)) (M a) (N a)
    simp only [Function.comp_def, weightedHellingerIntegral_one] at h ⊢
    exact h.trans (le_iSup (fun a => hellingerIntegral α (M a) (N a)) a)
  have h := weightedHellingerIntegral_bind_le hα μ ν (Kernel.id ×ₖ M) (Kernel.id ×ₖ N)
    GoodWeight.one (fun _ => S) hstep
  rw [weightedHellingerIntegral_one] at h
  rw [Measure.compProd_eq_comp_prod, Measure.compProd_eq_comp_prod]
  refine h.trans ?_
  rcases eq_or_ne S 0 with h0 | h0
  · rw [h0, weightedHellingerIntegral_of_ac _ hμν]
    simp
  · have := weightedHellingerIntegral_const_mul (α := α) S h0 (fun _ : A => (1 : ℝ≥0∞)) measurable_const μ ν
    simp only [mul_one] at this
    rw [this, weightedHellingerIntegral_one, mul_comm]

end Continuous
