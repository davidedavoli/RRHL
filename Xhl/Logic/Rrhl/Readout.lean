import Xhl.Logic.Rrhl.Rrhl
import Xhl.Language.SubMarkov
import Xhl.Divergence.Privacy

open Continuous

/-!
# From a judgment to a Rényi bound (§4.4)

* `hellingerIntegral_le_of_tests` — strong duality for the equality relation, on any measurable
  space: if every pair of tests with pointwise Hellinger term at most `1` has value at
  most `η`, then the Hellinger integral is at most `η`.  The tests are explicit
  (truncated powers of the likelihood ratio), so no topology is needed.
* `rrhl_tr_hellingerIntegral_le` — a valid judgment whose postcondition equates the transcripts
  bounds the Hellinger integral between the laws of the transcripts.
* `rrhl_renyiDP` / `rrhl_indivRenyiDP` — Proposition 4.4: such a judgment, from adjacent
  memories with equal transcripts, makes the program's transcript `(α, log η/(α−1))`-RDP,
  and a family of them, one per individual, makes it individually RDP.
-/

open MeasureTheory ProbabilityTheory ENNReal Cmd

namespace Continuous

section Equality

variable {Ω : Type*} [MeasurableSpace Ω]

private lemma trunc_adm {α : ℝ} (hα : 1 < α) {y : ℝ≥0∞} (hy : y ≠ ⊤) :
    (y ^ (α - 1)) ^ α * (y ^ α) ^ (1 - α) ≤ 1 := by
  have hα0 : (0 : ℝ) < α := by linarith
  rcases eq_or_ne y 0 with h0 | h0
  · rw [h0, ENNReal.zero_rpow_of_pos (by linarith : (0 : ℝ) < α - 1),
      ENNReal.zero_rpow_of_pos hα0, zero_mul]
    exact zero_le
  · rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul, ← ENNReal.rpow_add _ _ h0 hy]
    have : (α - 1) * α + α * (1 - α) = 0 := by ring
    rw [this, ENNReal.rpow_zero]

private lemma mul_rpow_pred {α : ℝ} (hα : 1 < α) {y : ℝ≥0∞} (hy : y ≠ ⊤) :
    y * y ^ (α - 1) = y ^ α := by
  have hα0 : (0 : ℝ) < α := by linarith
  rcases eq_or_ne y 0 with h0 | h0
  · rw [h0, zero_mul, ENNReal.zero_rpow_of_pos hα0]
  · nth_rewrite 1 [← ENNReal.rpow_one y]
    rw [← ENNReal.rpow_add _ _ h0 hy]
    congr 1; ring

/-- **Strong duality for equality.** -/
theorem hellingerIntegral_le_of_tests {α : ℝ} (hα : 1 < α) (μ ν : Measure Ω) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] {η : ℝ≥0∞}
    (h : ∀ g₁ g₂ : Ω → ℝ≥0∞, Measurable g₁ → Measurable g₂ →
      (∀ x, g₁ x ^ α * g₂ x ^ (1 - α) ≤ 1) →
      (∫⁻ x, g₁ x ∂μ) ^ α * (∫⁻ x, g₂ x ∂ν) ^ (1 - α) ≤ η) :
    hellingerIntegral α μ ν ≤ η := by
  have hα0 : (0 : ℝ) < α := by linarith
  have h1α : (1 : ℝ) - α < 0 := by linarith
  by_cases hac : μ ≪ ν
  · set L := μ.rnDeriv ν with hL
    have hLm : Measurable L := Measure.measurable_rnDeriv μ ν
    set T : ℕ → Ω → ℝ≥0∞ := fun n x => min (L x) n with hT
    have hTm : ∀ n, Measurable (T n) := fun n => hLm.min measurable_const
    have hTt : ∀ n x, T n x ≠ ⊤ := fun n x =>
      ne_top_of_le_ne_top (ENNReal.natCast_ne_top n) (min_le_right _ _)
    have hI : ∀ n, ∫⁻ x, T n x ^ α ∂ν ≤ η := by
      intro n
      set I := ∫⁻ x, T n x ^ α ∂ν with hIdef
      set A := ∫⁻ x, T n x ^ (α - 1) ∂μ with hAdef
      have hIA : I ≤ A := by
        rw [hAdef, ← lintegral_rnDeriv_mul hac ((hTm n).pow_const _).aemeasurable]
        refine lintegral_mono fun x => ?_
        calc T n x ^ α = T n x * T n x ^ (α - 1) := (mul_rpow_pred hα (hTt n x)).symm
          _ ≤ L x * T n x ^ (α - 1) := mul_le_mul' (min_le_left _ _) le_rfl
      have hIt : I ≠ ⊤ := by
        refine ne_top_of_le_ne_top
          (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hα0.le (ENNReal.natCast_ne_top n))
            (measure_ne_top ν Set.univ)) ?_
        calc I ≤ ∫⁻ _, (n : ℝ≥0∞) ^ α ∂ν :=
              lintegral_mono fun x => ENNReal.rpow_le_rpow (min_le_right _ _) hα0.le
          _ = (n : ℝ≥0∞) ^ α * ν Set.univ := lintegral_const _
      have hv := h (fun x => T n x ^ (α - 1)) (fun x => T n x ^ α) ((hTm n).pow_const _)
        ((hTm n).pow_const _) (fun x => trunc_adm hα (hTt n x))
      rcases eq_or_ne I 0 with hI0 | hI0
      · rw [hI0]; exact zero_le
      calc I = I ^ α * I ^ (1 - α) := by
            rw [← ENNReal.rpow_add _ _ hI0 hIt, add_sub_cancel, ENNReal.rpow_one]
        _ ≤ A ^ α * I ^ (1 - α) := mul_le_mul' (ENNReal.rpow_le_rpow hIA hα0.le) le_rfl
        _ ≤ η := hv
    rw [hellingerIntegral_eq_lintegral_rnDeriv μ ν hac]
    calc ∫⁻ x, L x ^ α ∂ν ≤ ∫⁻ x, ⨆ n, T n x ^ α ∂ν := by
          refine lintegral_mono_ae ?_
          filter_upwards [Measure.rnDeriv_lt_top μ ν] with x hx
          obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hx.ne
          refine le_iSup_of_le n ?_
          show L x ^ α ≤ (min (L x) n) ^ α
          rw [min_eq_left hn.le]
      _ = ⨆ n, ∫⁻ x, T n x ^ α ∂ν := by
          refine lintegral_iSup (fun n => (hTm n).pow_const _) ?_
          intro n m hnm x
          exact ENNReal.rpow_le_rpow (min_le_min le_rfl (by exact_mod_cast hnm)) hα0.le
      _ ≤ η := iSup_le hI
  · obtain ⟨s, hνs, hμs⟩ : ∃ s, ν s = 0 ∧ μ s ≠ 0 := by
      by_contra hne
      push Not at hne
      exact hac (fun s hs => hne s hs)
    set N := toMeasurable ν s with hN
    have hNm : MeasurableSet N := measurableSet_toMeasurable ν s
    have hνN : ν N = 0 := by rw [hN, measure_toMeasurable]; exact hνs
    have hμN : μ N ≠ 0 := fun h0 =>
      hμs (measure_mono_null (subset_toMeasurable ν s) h0)
    have hv := h (N.indicator 1) (N.indicator 1) (measurable_one.indicator hNm)
      (measurable_one.indicator hNm) (fun x => by
        by_cases hx : x ∈ N
        · simp [Set.indicator_of_mem hx]
        · simp [Set.indicator_of_notMem hx, ENNReal.zero_rpow_of_pos hα0])
    rw [lintegral_indicator_one hNm, lintegral_indicator_one hNm, hνN,
      ENNReal.zero_rpow_of_neg h1α,
      ENNReal.mul_top (ENNReal.rpow_pos (pos_iff_ne_zero.mpr hμN) (measure_ne_top μ N)).ne']
      at hv
    rw [top_le_iff.mp hv]; exact le_top

end Equality

variable {ident : Type} {M : MemType ident}


/-- The observational semantics of a command is a finite measure. -/
lemma isFiniteMeasure_osemA (c : Cmd ident M) (s : St M) :
    IsFiniteMeasure (osemA c s) := by
  refine ⟨?_⟩
  exact lt_of_le_of_lt (osemA_univ_le_one c s) ENNReal.one_lt_top

/-- **What the adversary sees.**  A valid judgment whose postcondition equates the
    transcripts bounds the Hellinger integral between the laws of the transcripts. -/
theorem rrhl_tr_hellingerIntegral_le {α : ℝ} (hα : 1 < α) {η : ℝ≥0∞} {P : St M × St M → Prop}
    {c₁ c₂ : Cmd ident M} 
    (h : RRhl α P (fun _ => η) c₁ c₂ (fun q => q.1.2 = q.2.2) (fun _ => 1))
    (s : St M × St M) (hs : P s) :
    hellingerIntegral α ((osemA c₁ s.1).map Prod.snd) ((osemA c₂ s.2).map Prod.snd) ≤ η := by
  have := isFiniteMeasure_osemA c₁ s.1
  have := isFiniteMeasure_osemA c₂ s.2
  refine hellingerIntegral_le_of_tests hα _ _ fun g₁ g₂ hg₁ hg₂ hadm => ?_
  rw [lintegral_map hg₁ measurable_snd, lintegral_map hg₂ measurable_snd]
  refine h s hs (fun x => g₁ x.2) (fun x => g₂ x.2) (hg₁.comp measurable_snd)
    (hg₂.comp measurable_snd) fun p hp => ?_
  show g₁ p.1.2 ^ α * g₂ p.2.2 ^ (1 - α) ≤ 1
  rw [hp]; exact hadm _

/-- The budget `η` of a judgment as an RDP level: `η ≤ exp((α−1) · log η/(α−1))`.  (At
    `η = 0`, `Real.log 0 = 0` and the right-hand side is `1`.) -/
lemma le_exp_renyiLevel {α : ℝ} (hα : 1 < α) {η : ℝ≥0∞} (hη : η ≠ ⊤) :
    η ≤ ENNReal.ofReal (Real.exp ((α - 1) * (Real.log η.toReal / (α - 1)))) := by
  rw [mul_div_cancel₀ _ (by linarith : (α - 1) ≠ 0)]
  rcases eq_or_ne η 0 with h0 | h0
  · rw [h0]; exact zero_le
  · rw [Real.exp_log (ENNReal.toReal_pos h0 hη), ENNReal.ofReal_toReal hη]

/-- **Proposition 4.4, the RDP readout.**  A valid judgment of `c` against itself, from
    `Adj`-related memories with equal transcripts to equal transcripts at budget `η`,
    makes the law of `c`'s transcript `(α, log η/(α−1))`-Rényi differentially private on
    `Adj`-related inputs.  The run starts from the empty transcript, so the equal-transcript
    half of the precondition holds initially. -/
theorem rrhl_renyiDP {α : ℝ} (hα : 1 < α) {η : ℝ≥0∞} (hη : η ≠ ⊤)
    {Adj : M.heap → M.heap → Prop} {c : Cmd ident M}
    (h : RRhl α (fun s => Adj s.1.1 s.2.1 ∧ s.1.2 = s.2.2) (fun _ => η) c c
      (fun q => q.1.2 = q.2.2) (fun _ => 1)) :
    RenyiDP α (Real.log η.toReal / (α - 1)) Adj (fun m => (osem c m).map Prod.snd) :=
  fun m₁ m₂ hadj => (renyiDiv_le_coe_iff hα _ _).2 <|
    (rrhl_tr_hellingerIntegral_le hα h ((m₁, Tr.nil), (m₂, Tr.nil)) ⟨hadj, rfl⟩).trans
      (le_exp_renyiLevel hα hη)

/-- **Proposition 4.4, individual form.**  One such judgment per individual `k`, at the
    individual adjacency `Adj k` and budget `η k`, makes the transcript
    `(α, (log η k/(α−1))ₖ)`-individually RDP for the family `Adj`. -/
theorem rrhl_indivRenyiDP {ι : Type*} {α : ℝ} (hα : 1 < α) {η : ι → ℝ≥0∞}
    (hη : ∀ k, η k ≠ ⊤) {Adj : ι → M.heap → M.heap → Prop} {c : Cmd ident M}
    (h : ∀ k, RRhl α (fun s => Adj k s.1.1 s.2.1 ∧ s.1.2 = s.2.2) (fun _ => η k) c c
      (fun q => q.1.2 = q.2.2) (fun _ => 1)) :
    IndivRenyiDP α (fun k => Real.log (η k).toReal / (α - 1)) Adj
      (fun m => (osem c m).map Prod.snd) :=
  fun k => rrhl_renyiDP hα (hη k) (h k)

end Continuous
