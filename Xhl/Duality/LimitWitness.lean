import Xhl.Duality.HellingerIntegralLsc
import Xhl.Divergence.Convert
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Tight
import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# A limit of approximate left witnesses

Used by the strong duality theorem (Theorem C.1).  Let `W i` be finite measures
on `A × B` (Polish spaces), indexed along a non-trivial filter, all with left
marginal `μ₁` and right-marginal budget `hellingerIntegral α ((W i).map snd) μ₂ ≤ η < ⊤`,
and eventually vanishing outside each member of a sequence of closed sets whose
intersection lies in `R`.  Then some finite measure `w` has left marginal `μ₁`,
is supported on `R`, and keeps the budget (`exists_limit_witness`).  Together
with `exists_witnesses_of_reduced` it gives the two witnesses.

* **Tightness** (`exists_compact_compl_le`): the left marginals are the single
  measure `μ₁`, tight on a Polish space; the right marginals obey the uniform
  bound `ν(S) ≤ η^{1/α} μ₂(S)^{(α−1)/α}` (`hellingerIntegral_pr_le`), so they inherit the
  tightness of `μ₂`; a product of compacts controls both.
* **Compactness**: Prokhorov's theorem for finite measures of fixed mass
  (`isCompact_setOfPred_finiteMeasure_mass_eq_compl_isCompact_le`); the limit is
  taken along an ultrafilter finer than the index filter.
* **Passing to the limit**: the left marginal by continuity of pushforward; the
  support by the closed-set portmanteau inequality and the fixed total mass; the
  budget by lower semicontinuity of the Hellinger integral (`hellingerIntegral_lsc`).
-/

open MeasureTheory ENNReal Filter Topology
open scoped NNReal

namespace Continuous

variable {A B : Type*}
  [MetricSpace A] [CompleteSpace A] [SecondCountableTopology A] [MeasurableSpace A] [BorelSpace A]
  [MetricSpace B] [CompleteSpace B] [SecondCountableTopology B] [MeasurableSpace B] [BorelSpace B]

/-- **Uniform tightness** of a family with fixed left marginal and bounded
    right-marginal Hellinger integral. -/
lemma exists_compact_compl_le {α : ℝ} (hα : 1 < α) {η : ℝ≥0∞} (hη : η ≠ ⊤)
    {μ₁ : Measure A} {μ₂ : Measure B} [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂]
    {ι : Type*} (W : ι → Measure (A × B)) [∀ i, IsFiniteMeasure (W i)]
    (hW₁ : ∀ i, (W i).map Prod.fst = μ₁) (hWJ : ∀ i, hellingerIntegral α ((W i).map Prod.snd) μ₂ ≤ η)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ K : Set (A × B), IsCompact K ∧ ∀ i, W i Kᶜ ≤ ε := by
  have hα0 : (0 : ℝ) < α := by linarith
  have hq : (0 : ℝ) < (α - 1) / α := div_pos (by linarith) hα0
  have hε2 : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  obtain ⟨K₁, hK₁c, hK₁⟩ := isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp
    (isTightMeasureSet_singleton (μ := μ₁)) (ε / 2) hε2
  -- the right marginals: a uniform bound in terms of `μ₂`
  have hg : Tendsto (fun δ : ℝ≥0∞ => η ^ (1 / α) * δ ^ ((α - 1) / α)) (𝓝 0) (𝓝 0) := by
    have h1 : Tendsto (fun δ : ℝ≥0∞ => δ ^ ((α - 1) / α)) (𝓝 0) (𝓝 0) := by
      have := (ENNReal.continuous_rpow_const (y := (α - 1) / α)).tendsto 0
      rwa [ENNReal.zero_rpow_of_pos hq] at this
    have := ENNReal.Tendsto.const_mul h1
      (Or.inr (ENNReal.rpow_ne_top_of_nonneg (one_div_pos.mpr hα0).le hη))
    rwa [mul_zero] at this
  obtain ⟨δ, hδg, hδpos⟩ := ((hg.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))).eventually
    (gt_mem_nhds hε2)).and self_mem_nhdsWithin |>.exists
  obtain ⟨K₂, hK₂c, hK₂⟩ := isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp
    (isTightMeasureSet_singleton (μ := μ₂)) δ hδpos
  refine ⟨K₁ ×ˢ K₂, hK₁c.prod hK₂c, fun i => ?_⟩
  have h1 : W i (Prod.fst ⁻¹' K₁ᶜ) ≤ ε / 2 := by
    rw [← Measure.map_apply measurable_fst hK₁c.isClosed.measurableSet.compl, hW₁ i]
    exact hK₁ μ₁ rfl
  have h2 : W i (Prod.snd ⁻¹' K₂ᶜ) ≤ ε / 2 := by
    rw [← Measure.map_apply measurable_snd hK₂c.isClosed.measurableSet.compl]
    have hac : (W i).map Prod.snd ≪ μ₂ := by
      by_contra h
      have htop : hellingerIntegral α ((W i).map Prod.snd) μ₂ = ⊤ := hellingerIntegral_eq_top_of_not_ac _ _ h
      exact hη (top_le_iff.mp (htop ▸ hWJ i))
    calc (W i).map Prod.snd K₂ᶜ
        ≤ (hellingerIntegral α ((W i).map Prod.snd) μ₂) ^ (1 / α) * (μ₂ K₂ᶜ) ^ ((α - 1) / α) :=
          hellingerIntegral_pr_le hα _ μ₂ hac hK₂c.isClosed.measurableSet.compl
      _ ≤ η ^ (1 / α) * δ ^ ((α - 1) / α) :=
          mul_le_mul' (ENNReal.rpow_le_rpow (hWJ i) (one_div_pos.mpr hα0).le)
            (ENNReal.rpow_le_rpow (hK₂ μ₂ rfl) hq.le)
      _ ≤ ε / 2 := hδg.le
  calc W i (K₁ ×ˢ K₂)ᶜ = W i (Prod.fst ⁻¹' K₁ᶜ ∪ Prod.snd ⁻¹' K₂ᶜ) := by
        rw [Set.compl_prod_eq_union, Set.prod_univ, Set.univ_prod]
    _ ≤ W i (Prod.fst ⁻¹' K₁ᶜ) + W i (Prod.snd ⁻¹' K₂ᶜ) := measure_union_le _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add h1 h2
    _ = ε := ENNReal.add_halves ε

/-- **A limit of approximate left witnesses.** -/
theorem exists_limit_witness {α : ℝ} (hα : 1 < α) {R : A → B → Prop} {η : ℝ≥0∞} (hη : η ≠ ⊤)
    {μ₁ : Measure A} {μ₂ : Measure B} [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂]
    (F : ℕ → Set (A × B)) (hFc : ∀ k, IsClosed (F k)) (hFR : ∀ p, (∀ k, p ∈ F k) → R p.1 p.2)
    {ι : Type*} {l : Filter ι} [l.NeBot] (W : ι → Measure (A × B)) [∀ i, IsFiniteMeasure (W i)]
    (hW₁ : ∀ i, (W i).map Prod.fst = μ₁) (hWJ : ∀ i, hellingerIntegral α ((W i).map Prod.snd) μ₂ ≤ η)
    (hWF : ∀ k, ∀ᶠ i in l, W i (F k)ᶜ = 0) :
    ∃ w : Measure (A × B), IsFiniteMeasure w ∧ w.map Prod.fst = μ₁ ∧
      (∀ᵐ p ∂w, R p.1 p.2) ∧ hellingerIntegral α (w.map Prod.snd) μ₂ ≤ η := by
  -- uniform tightness along a sequence of compacts
  obtain ⟨u, -, upos, ulim⟩ : ∃ u : ℕ → ℝ≥0, StrictAnti u ∧ (∀ n, 0 < u n) ∧
      Tendsto u atTop (𝓝 0) := exists_seq_strictAnti_tendsto 0
  have hK : ∀ n, ∃ K : Set (A × B), IsCompact K ∧ ∀ i, W i Kᶜ ≤ u n := fun n =>
    exists_compact_compl_le hα hη W hW₁ hWJ (ENNReal.coe_pos.mpr (upos n))
  choose K hKc hKb using hK
  -- the family as finite measures, all in one compact set
  set Wf : ι → FiniteMeasure (A × B) := fun i => ⟨W i, inferInstance⟩ with hWf
  have hWuniv : ∀ i, W i Set.univ = μ₁ Set.univ := fun i => by
    rw [← hW₁ i, Measure.map_apply measurable_fst MeasurableSet.univ, Set.preimage_univ]
  set C : ℝ≥0 := (μ₁ Set.univ).toNNReal with hC
  have hmass : ∀ i, (Wf i).mass = C := fun i => by
    apply ENNReal.coe_injective
    rw [FiniteMeasure.ennreal_mass, hC, ENNReal.coe_toNNReal (measure_ne_top μ₁ _)]
    exact hWuniv i
  set S := {μ : FiniteMeasure (A × B) | μ.mass = C ∧ ∀ n, μ (K n)ᶜ ≤ u n} with hSdef
  have hS : IsCompact S :=
    isCompact_setOfPred_finiteMeasure_mass_eq_compl_isCompact_le C ulim hKc (Or.inl inferInstance)
  have hWS : ∀ i, Wf i ∈ S := fun i => ⟨hmass i, fun n => by
    rw [← ENNReal.coe_le_coe, FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
    exact hKb n i⟩
  -- a limit along an ultrafilter finer than `l`
  set 𝒰 : Ultrafilter ι := Ultrafilter.of l with h𝒰
  obtain ⟨wL, -, hlim⟩ := hS.ultrafilter_le_nhds (𝒰.map Wf)
    (by rw [Ultrafilter.coe_map]
        exact le_principal_iff.mpr (Filter.mem_map.mpr (Filter.univ_mem' hWS)))
  have hT : Tendsto Wf 𝒰 (𝓝 wL) := by rw [Tendsto, ← Ultrafilter.coe_map]; exact hlim
  set w : Measure (A × B) := (wL : Measure (A × B)) with hw
  -- left marginal
  set μ₁f : FiniteMeasure A := ⟨μ₁, inferInstance⟩ with hμ₁f
  have hfst : Tendsto (fun i => (Wf i).map Prod.fst) 𝒰 (𝓝 (wL.map Prod.fst)) :=
    ((FiniteMeasure.continuous_map continuous_fst).tendsto wL).comp hT
  have hconst : ∀ i, (Wf i).map Prod.fst = μ₁f := fun i =>
    FiniteMeasure.toMeasure_injective (by rw [FiniteMeasure.toMeasure_map]; exact hW₁ i)
  have h1 : wL.map Prod.fst = μ₁f :=
    tendsto_nhds_unique hfst (by simp only [hconst]; exact tendsto_const_nhds)
  have hw₁ : w.map Prod.fst = μ₁ := by
    have := congrArg (fun ν : FiniteMeasure A => (ν : Measure A)) h1
    simp only [FiniteMeasure.toMeasure_map] at this
    exact this
  -- support
  have hwuniv : w Set.univ = μ₁ Set.univ := by
    rw [← hw₁, Measure.map_apply measurable_fst MeasurableSet.univ, Set.preimage_univ]
  have hFk : ∀ k, w (F k)ᶜ = 0 := by
    intro k
    have hls := FiniteMeasure.limsup_measure_closed_le_of_tendsto hT (hFc k)
    have hev : ∀ᶠ i in (𝒰 : Filter ι), (Wf i : Measure (A × B)) (F k) = μ₁ Set.univ := by
      filter_upwards [(hWF k).filter_mono (Ultrafilter.of_le l)] with i hi
      have hsplit := measure_add_measure_compl (μ := W i) (hFc k).measurableSet
      rw [hi, add_zero, hWuniv i] at hsplit
      exact hsplit
    rw [limsup_congr hev, limsup_const] at hls
    rw [measure_compl (hFc k).measurableSet (measure_ne_top _ _), hwuniv]
    exact tsub_eq_zero_of_le hls
  have hR : ∀ᵐ p ∂w, R p.1 p.2 := by
    rw [ae_iff]
    refine measure_mono_null (fun p hp => ?_) (measure_iUnion_null hFk)
    simp only [Set.mem_ofPred_eq] at hp
    by_contra hcon
    simp only [Set.mem_iUnion, Set.mem_compl_iff, not_exists, not_not] at hcon
    exact hp (hFR p hcon)
  -- budget
  have hsnd : Tendsto (fun i => (Wf i).map Prod.snd) 𝒰 (𝓝 (wL.map Prod.snd)) :=
    ((FiniteMeasure.continuous_map continuous_snd).tendsto wL).comp hT
  have hJ : hellingerIntegral α (w.map Prod.snd) μ₂ ≤ η := by
    by_contra hcon
    push Not at hcon
    have hl := hellingerIntegral_lsc hα μ₂ (wL.map Prod.snd) η (by
      show η < hellingerIntegral α ((wL.map Prod.snd : FiniteMeasure B) : Measure B) μ₂
      rw [FiniteMeasure.toMeasure_map]; exact hcon)
    obtain ⟨i, hi⟩ := (hsnd.eventually hl).exists
    change η < hellingerIntegral α (((Wf i).map Prod.snd : FiniteMeasure B) : Measure B) μ₂ at hi
    rw [FiniteMeasure.toMeasure_map] at hi
    exact absurd (hWJ i) (not_le.mpr hi)
  exact ⟨w, inferInstance, hw₁, hR, hJ⟩

end Continuous
