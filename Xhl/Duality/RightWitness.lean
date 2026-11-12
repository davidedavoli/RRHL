import Xhl.Duality.WitnessFreeLift
import Xhl.Divergence.ChainUncond
import Xhl.Divergence.MapLe
import Mathlib.Probability.Kernel.Disintegration.StandardBorel

/-!
# The right witness from a single measure (reduced form of the lifting)

Used by the strong duality theorem (Theorem C.1).  The two-witness lifting is
determined by its left witness alone: if a finite measure `w` on `A × B` has left
marginal `μ₁`, is supported on `R`, and its right marginal `ν` satisfies
`hellingerIntegral α ν μ₂ ≤ η`, then a right witness exists completing it to a
pair of witnesses for `(μ₁, μ₂)` at budget `η` (`exists_witnesses_of_reduced`).

The right witness is built by disintegration.  Swap `w` and disintegrate along
`B`: `w.swap = ν ⊗ₘ K'` with `K'` the conditional kernel (`A` standard Borel).
`K'` is arbitrary off a `ν`-null set, where `μ₂` may still put mass, so it is
replaced there by the Dirac kernel of a measurable partner selector `s : B → A`.
The switch is the measurable set `G` of targets whose conditional law already
charges only `R`; it has full `ν`-measure, so the left witness is unchanged.
The right witness is `(μ₂ ⊗ₘ K'').swap`.  Its Hellinger integral against the
left witness is at most `hellingerIntegral α ν μ₂` by data processing (the swap) and the
chain bound over `compProd` (`hellingerIntegral_compProd_le`), with equal fibers.

The selector is a hypothesis; `wrhl_of_rrhl_polish` supplies it by
`exists_measurable_partner_ae`.

`exists_witnesses_top` is the infinite-budget case, which needs only the two selectors.
-/


open MeasureTheory ProbabilityTheory ENNReal

namespace Continuous

section Top

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

/-- **Infinite budget**: with measurable partner selectors on both sides, the
    two witnesses exist at budget `⊤`. -/
theorem exists_witnesses_top {α : ℝ} {R : A → B → Prop} (hRm : MeasurableSet {p : A × B | R p.1 p.2})
    {μ₁ : Measure A} {μ₂ : Measure B} [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂]
    (s₁ : A → B) (hs₁ : Measurable s₁) (h₁ : ∀ᵐ a ∂μ₁, R a (s₁ a))
    (s₂ : B → A) (hs₂ : Measurable s₂) (h₂ : ∀ᵐ b ∂μ₂, R (s₂ b) b) :
    ∃ w₁ w₂ : Measure (A × B), IsFiniteMeasure w₁ ∧ IsFiniteMeasure w₂ ∧
      w₁.map Prod.fst = μ₁ ∧ w₂.map Prod.snd = μ₂ ∧
      (∀ᵐ p ∂w₁, R p.1 p.2) ∧ (∀ᵐ p ∂w₂, R p.1 p.2) ∧ hellingerIntegral α w₁ w₂ ≤ ⊤ := by
  have hm₁ : Measurable fun a => (a, s₁ a) := measurable_id.prodMk hs₁
  have hm₂ : Measurable fun b => (s₂ b, b) := hs₂.prodMk measurable_id
  refine ⟨μ₁.map fun a => (a, s₁ a), μ₂.map fun b => (s₂ b, b), inferInstance, inferInstance,
    ?_, ?_, ?_, ?_, le_top⟩
  · rw [Measure.map_map measurable_fst hm₁]; exact Measure.map_id
  · rw [Measure.map_map measurable_snd hm₂]; exact Measure.map_id
  · exact (ae_map_iff hm₁.aemeasurable hRm).mpr h₁
  · exact (ae_map_iff hm₂.aemeasurable hRm).mpr h₂

end Top

section Reduced

variable {A B : Type*} [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]
  [MeasurableSpace B]

/-- **Reduced form of the lifting**: a single finite measure with left marginal
    `μ₁`, supported on `R`, whose right marginal has Hellinger integral at most `η`
    against `μ₂`, yields two witnesses at budget `η`, given a measurable selector of
    `R`-partners for `μ₂`-almost every target. -/
theorem exists_witnesses_of_reduced {α : ℝ} (hα : 1 < α) {R : A → B → Prop} {η : ℝ≥0∞}
    (hRm : MeasurableSet {p : A × B | R p.1 p.2})
    {μ₁ : Measure A} {μ₂ : Measure B} [IsFiniteMeasure μ₂]
    (w : Measure (A × B)) [IsFiniteMeasure w] (hw₁ : w.map Prod.fst = μ₁)
    (hwR : ∀ᵐ p ∂w, R p.1 p.2) (hJ : hellingerIntegral α (w.map Prod.snd) μ₂ ≤ η)
    (s : B → A) (hs : Measurable s) (hsR : ∀ᵐ b ∂μ₂, R (s b) b) :
    ∃ w₁ w₂ : Measure (A × B), IsFiniteMeasure w₁ ∧ IsFiniteMeasure w₂ ∧
      w₁.map Prod.fst = μ₁ ∧ w₂.map Prod.snd = μ₂ ∧
      (∀ᵐ p ∂w₁, R p.1 p.2) ∧ (∀ᵐ p ∂w₂, R p.1 p.2) ∧ hellingerIntegral α w₁ w₂ ≤ η := by
  -- disintegrate the swapped witness along `B`
  set ρ : Measure (B × A) := w.map Prod.swap with hρ
  set ν : Measure B := w.map Prod.snd with hν
  have hρν : ρ.fst = ν := by rw [hρ, Measure.fst_map_swap]; rfl
  set K' : Kernel B A := ρ.condKernel with hK'
  have hdis : ν ⊗ₘ K' = ρ := by rw [← hρν]; exact ρ.disintegrate ρ.condKernel
  -- the good targets: those whose conditional law charges only `R`
  set T : Set (B × A) := {q | ¬ R q.2 q.1} with hT
  have hTm : MeasurableSet T :=
    (measurable_swap hRm).compl
  have hsec : ∀ b, Prod.mk b ⁻¹' T = {a | ¬ R a b} := fun b => rfl
  set G : Set B := {b | K' b (Prod.mk b ⁻¹' T) = 0} with hG
  have hGm : MeasurableSet G :=
    (Kernel.measurable_kernel_prodMk_left hTm) (measurableSet_singleton 0)
  -- `ρ`-almost every pair is related
  have hρR : ∀ᵐ q ∂ρ, R q.2 q.1 :=
    (ae_map_iff measurable_swap.aemeasurable (measurable_swap hRm)).mpr hwR
  have hνG : ∀ᵐ b ∂ν, b ∈ G := by
    rw [← hdis] at hρR
    filter_upwards [Measure.ae_ae_of_ae_compProd hρR] with b hb
    show K' b (Prod.mk b ⁻¹' T) = 0
    rw [hsec]
    exact ae_iff.mp hb
  -- the corrected kernel
  set K'' : Kernel B A := Kernel.piecewise hGm K' (Kernel.deterministic s hs) with hK''
  have hK''mk : IsMarkovKernel K'' := by
    refine ⟨fun b => ?_⟩
    rw [hK'', Kernel.piecewise_apply]
    split_ifs
    · infer_instance
    · rw [Kernel.deterministic_apply]; infer_instance
  have hK''eq : ⇑K' =ᵐ[ν] ⇑K'' := by
    filter_upwards [hνG] with b hb
    rw [hK'', Kernel.piecewise_apply, if_pos hb]
  have hwX : w = (ν ⊗ₘ K'').map Prod.swap := by
    rw [← Measure.compProd_congr hK''eq, hdis, hρ, Measure.map_map measurable_swap measurable_swap]
    simp [Function.comp_def, Measure.map_id']
  -- the right witness
  set w₂ : Measure (A × B) := (μ₂ ⊗ₘ K'').map Prod.swap with hw₂
  have hw₂snd : w₂.map Prod.snd = μ₂ := by
    rw [hw₂, Measure.map_map measurable_snd measurable_swap]
    show (μ₂ ⊗ₘ K'').map Prod.fst = μ₂
    exact Measure.fst_compProd μ₂ K''
  have hw₂R : ∀ᵐ p ∂w₂, R p.1 p.2 := by
    refine (ae_map_iff measurable_swap.aemeasurable hRm).mpr ?_
    refine (Measure.ae_compProd_iff (measurable_swap hRm)).mpr ?_
    filter_upwards [hsR] with b hb
    rw [hK'', Kernel.piecewise_apply]
    split_ifs with hbG
    · have h0 : K' b {a | ¬ R a b} = 0 := by rw [← hsec]; exact hbG
      exact ae_iff.mpr h0
    · rw [Kernel.deterministic_apply]
      exact (ae_dirac_iff (measurable_prodMk_right hRm)).mpr hb
  -- the budget
  have hbudget : hellingerIntegral α w w₂ ≤ η := by
    by_cases hac : ν ≪ μ₂
    · have hXY : ν ⊗ₘ K'' ≪ μ₂ ⊗ₘ K'' := hac.compProd_left K''
      have hsup : (⨆ b, hellingerIntegral α (K'' b) (K'' b)) ≤ 1 :=
        iSup_le fun b => (hellingerIntegral_self_prob (K'' b)).le
      calc hellingerIntegral α w w₂ = hellingerIntegral α ((ν ⊗ₘ K'').map Prod.swap) ((μ₂ ⊗ₘ K'').map Prod.swap) := by
            rw [← hwX]
        _ ≤ hellingerIntegral α (ν ⊗ₘ K'') (μ₂ ⊗ₘ K'') := hellingerIntegral_map_le hα measurable_swap _ _ hXY
        _ ≤ hellingerIntegral α ν μ₂ * ⨆ b, hellingerIntegral α (K'' b) (K'' b) :=
            hellingerIntegral_compProd_le hα ν μ₂ K'' K'' hac
        _ ≤ hellingerIntegral α ν μ₂ * 1 := mul_le_mul' le_rfl hsup
        _ = hellingerIntegral α ν μ₂ := mul_one _
        _ ≤ η := hJ
    · have htop : hellingerIntegral α ν μ₂ = ⊤ := hellingerIntegral_eq_top_of_not_ac ν μ₂ hac
      rw [htop, top_le_iff] at hJ
      rw [hJ]; exact le_top
  exact ⟨w, w₂, inferInstance, inferInstance, hw₁, hw₂snd, hwR, hw₂R, hbudget⟩

end Reduced

end Continuous
