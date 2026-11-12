import Xhl.Logic.Rrhl.Rrhl

open Continuous

/-!
# Validity of the sampling rules and of [Scale]

* `rrhl_rnd_fwdK_ae` — **[Samp-Dec]** (Figure 9): the right sampler decomposes as
  `dlet v ← ν in F v` with `F` Markov; postcondition asked almost everywhere.
  `rrhl_rnd_fwdK` is the everywhere instance.
* `rrhl_rnd` — **[Samp]**: the instance at the identity kernel.
* `rrhl_rnd_gap` — **[Samp-Gap]**: the instance at the translation `v ↦ v − δ`.
* `rrhl_scale` — **[Scale]**.
-/

open MeasureTheory ProbabilityTheory ENNReal Cmd

variable {ident : Type} {M : MemType ident}

namespace Continuous

/-- The pair of states after writing `v.1` on the left and `v.2` on the right. -/
def updPair {t₁ t₂ : Ty} (x₁ : Vars ident t₁) (x₂ : Vars ident t₂) (s : St M × St M)
    (v : t₁.interp × t₂.interp) : St M × St M :=
  ((M.set s.1.1 t₁ x₁.name v.1, s.1.2), (M.set s.2.1 t₂ x₂.name v.2, s.2.2))

/-- **[Samp-Dec]** (Figure 9): if `ν.bind F = κ₂` with `F` Markov, the postcondition holds
    for `ν`-a.e. `v` and `F v`-a.e. `w`, and the weighted Hellinger integral of `κ₁`
    against `ν`, with the weight averaged under `F`, is at most `φ`, the sampling
    judgment is valid. -/
theorem rrhl_rnd_fwdK_ae {α : ℝ} (hα : 1 < α) {t₁ t₂ : Ty}
    (x₁ : Vars ident t₁) (x₂ : Vars ident t₂)
    (κ₁ : @ProbabilityTheory.Kernel M.heap t₁.interp M.heapMeas (Ty.measurableSpace t₁))
    [IsSubMarkovKernel κ₁]
    (κ₂ : @ProbabilityTheory.Kernel M.heap t₂.interp M.heapMeas (Ty.measurableSpace t₂))
    [IsSubMarkovKernel κ₂]
    (P Q : St M × St M → Prop) (φ ψ : St M × St M → ℝ≥0∞)
    (hdiv : ∀ s, P s →
      ∃ (F : @ProbabilityTheory.Kernel t₁.interp t₂.interp
          (Ty.measurableSpace t₁) (Ty.measurableSpace t₂)) (ν : Measure t₁.interp),
        IsMarkovKernel F ∧ IsFiniteMeasure ν ∧
        ν.bind (fun v => F v) = κ₂ s.2.1 ∧
        (∀ᵐ v ∂ν, ∀ᵐ w ∂(F v), Q (updPair x₁ x₂ s (v, w))) ∧
        weightedHellingerIntegral α (fun v => ∫⁻ w, ψ (updPair x₁ x₂ s (v, w)) ∂(F v))
          (κ₁ s.1.1) ν ≤ φ s) :
    RRhl α P φ (Cmd.random x₁ κ₁) (Cmd.random x₂ κ₂) Q ψ := by
  intro s hs k₁ k₂ hk₁ hk₂ hk
  obtain ⟨F, ν, hF, hν, hbind, hQae, hb⟩ := hdiv s hs
  haveI := hF
  haveI := hν
  have hu₁ : Measurable (fun v : t₁.interp => ((M.set s.1.1 t₁ x₁.name v, s.1.2) : St M)) :=
    ((M.set_measurable x₁.name).comp measurable_prodMk_left).prodMk measurable_const
  have hu₂ : Measurable (fun v : t₂.interp => ((M.set s.2.1 t₂ x₂.name v, s.2.2) : St M)) :=
    ((M.set_measurable x₂.name).comp measurable_prodMk_left).prodMk measurable_const
  have e₁ := ewp_random hk₁ x₁ κ₁ s.1
  have e₂ := ewp_random hk₂ x₂ κ₂ s.2
  unfold ewp at e₁ e₂
  have hg₂ : Measurable (fun w : t₂.interp => k₂ (M.set s.2.1 t₂ x₂.name w, s.2.2)) :=
    hk₂.comp hu₂
  -- the right integral, read through the witness and the kernel
  have hr : ∫⁻ w, k₂ (M.set s.2.1 t₂ x₂.name w, s.2.2) ∂(κ₂ s.2.1)
      = ∫⁻ v, ∫⁻ w, k₂ (M.set s.2.1 t₂ x₂.name w, s.2.2) ∂(F v) ∂ν := by
    rw [← hbind]
    exact Measure.lintegral_bind (F.measurable.aemeasurable) hg₂.aemeasurable
  set K₂ : t₁.interp → ℝ≥0∞ :=
    fun v => ∫⁻ w, k₂ (M.set s.2.1 t₂ x₂.name w, s.2.2) ∂(F v) with hK₂def
  have hK₂ : Measurable K₂ :=
    (hg₂.comp (measurable_snd (α := t₁.interp))).lintegral_kernel_prod_right'
  -- pointwise admissibility against the `F`-averaged weight: reverse Hölder under `F v`
  have hadm : ∀ᵐ v ∂ν, (k₁ (M.set s.1.1 t₁ x₁.name v, s.1.2)) ^ α * (K₂ v) ^ (1 - α)
      ≤ ∫⁻ w, ψ (updPair x₁ x₂ s (v, w)) ∂(F v) := by
    filter_upwards [hQae] with v hQv
    have hconst : k₁ (M.set s.1.1 t₁ x₁.name v, s.1.2)
        = ∫⁻ _w, k₁ (M.set s.1.1 t₁ x₁.name v, s.1.2) ∂(F v) := by
      rw [lintegral_const, measure_univ, mul_one]
    calc (k₁ (M.set s.1.1 t₁ x₁.name v, s.1.2)) ^ α * (K₂ v) ^ (1 - α)
        = (∫⁻ _w, k₁ (M.set s.1.1 t₁ x₁.name v, s.1.2) ∂(F v)) ^ α
            * (∫⁻ w, k₂ (M.set s.2.1 t₂ x₂.name w, s.2.2) ∂(F v)) ^ (1 - α) := by
          rw [← hconst]
      _ ≤ ∫⁻ w, (k₁ (M.set s.1.1 t₁ x₁.name v, s.1.2)) ^ α
            * (k₂ (M.set s.2.1 t₂ x₂.name w, s.2.2)) ^ (1 - α) ∂(F v) :=
          lintegral_rpow_mul_rpow_le _ _ hα measurable_const.aemeasurable hg₂.aemeasurable
      _ ≤ ∫⁻ w, ψ (updPair x₁ x₂ s (v, w)) ∂(F v) :=
          lintegral_mono_ae (hQv.mono fun w hw => hk _ hw)
  rw [testValC, e₁, e₂, hr]
  exact le_trans (testVal_le_weightedHellingerIntegral_same hα (hk₁.comp hu₁) hK₂ (κ₁ s.1.1) ν
    hadm) hb

/-- **[Samp-Dec]** with the postcondition asked everywhere. -/
theorem rrhl_rnd_fwdK {α : ℝ} (hα : 1 < α) {t₁ t₂ : Ty}
    (x₁ : Vars ident t₁) (x₂ : Vars ident t₂)
    (κ₁ : @ProbabilityTheory.Kernel M.heap t₁.interp M.heapMeas (Ty.measurableSpace t₁))
    [IsSubMarkovKernel κ₁]
    (κ₂ : @ProbabilityTheory.Kernel M.heap t₂.interp M.heapMeas (Ty.measurableSpace t₂))
    [IsSubMarkovKernel κ₂]
    (P Q : St M × St M → Prop) (φ ψ : St M × St M → ℝ≥0∞)
    (hdiv : ∀ s, P s →
      ∃ (F : @ProbabilityTheory.Kernel t₁.interp t₂.interp
          (Ty.measurableSpace t₁) (Ty.measurableSpace t₂)) (ν : Measure t₁.interp),
        IsMarkovKernel F ∧ IsFiniteMeasure ν ∧
        ν.bind (fun v => F v) = κ₂ s.2.1 ∧
        (∀ v, ∀ᵐ w ∂(F v), Q (updPair x₁ x₂ s (v, w))) ∧
        weightedHellingerIntegral α (fun v => ∫⁻ w, ψ (updPair x₁ x₂ s (v, w)) ∂(F v))
          (κ₁ s.1.1) ν ≤ φ s) :
    RRhl α P φ (Cmd.random x₁ κ₁) (Cmd.random x₂ κ₂) Q ψ :=
  rrhl_rnd_fwdK_ae hα x₁ x₂ κ₁ κ₂ P Q φ ψ fun s hs => by
    obtain ⟨F, ν, hF, hν, hbind, hQ, hb⟩ := hdiv s hs
    exact ⟨F, ν, hF, hν, hbind, Filter.Eventually.of_forall hQ, hb⟩

/-- **[Samp]**: both sides write the same sampled value; the postcondition is asked
    `κ₂`-a.e.  [Samp-Dec] at the identity kernel with `ν = κ₂`. -/
theorem rrhl_rnd {α : ℝ} (hα : 1 < α) {t : Ty} (x₁ x₂ : Vars ident t)
    (κ₁ κ₂ : @ProbabilityTheory.Kernel M.heap t.interp M.heapMeas (Ty.measurableSpace t))
    [IsSubMarkovKernel κ₁] [IsSubMarkovKernel κ₂]
    (P Q : St M × St M → Prop)
    (φ ψ : St M × St M → ℝ≥0∞)
    (hQhold : ∀ s, P s → ∀ᵐ v ∂(κ₂ s.2.1), Q (updPair x₁ x₂ s (v, v)))
    (hdiv : ∀ s, P s →
      weightedHellingerIntegral α (fun v => ψ (updPair x₁ x₂ s (v, v))) (κ₁ s.1.1) (κ₂ s.2.1) ≤ φ s) :
    RRhl α P φ (Cmd.random x₁ κ₁) (Cmd.random x₂ κ₂) Q ψ := by
  refine rrhl_rnd_fwdK_ae hα x₁ x₂ κ₁ κ₂ P Q φ ψ fun s hs => ?_
  refine ⟨Kernel.deterministic id measurable_id, κ₂ s.2.1,
    inferInstance, inferInstance, ?_, ?_, ?_⟩
  · simp only [Kernel.deterministic_apply, id_eq]
    exact Measure.bind_dirac
  · filter_upwards [hQhold s hs] with v hv
    rw [Kernel.deterministic_apply, ae_dirac_eq]
    exact Filter.eventually_pure.mpr hv
  · have h : ∀ v, (∫⁻ w, ψ (updPair x₁ x₂ s (v, w))
        ∂(Kernel.deterministic (id : t.interp → t.interp) measurable_id v))
        = ψ (updPair x₁ x₂ s (v, v)) := fun v => by
      rw [Kernel.deterministic_apply, lintegral_dirac, id_eq]
    simpa only [h] using hdiv s hs

/-- **[Samp-Gap]**: the right value is the left value translated by `−δ`; the
    postcondition is asked a.e.  [Samp-Dec] at the kernel `v ↦ dirac (v − δ s)` with `ν`
    the translated right sampler. -/
theorem rrhl_rnd_gap {α : ℝ} (hα : 1 < α) {d : ℕ} (x₁ x₂ : Vars ident (.vec d))
    (κ₁ κ₂ : @ProbabilityTheory.Kernel M.heap (EuclideanSpace ℝ (Fin d)) M.heapMeas
      (Ty.measurableSpace (.vec d)))
    [IsSubMarkovKernel κ₁] [IsSubMarkovKernel κ₂]
    (δ : St M × St M → EuclideanSpace ℝ (Fin d))
    (P Q : St M × St M → Prop) (φ ψ : St M × St M → ℝ≥0∞)
    (hQhold : ∀ s, P s → ∀ᵐ v ∂((κ₂ s.2.1).map (fun w => w + δ s)),
      Q (updPair x₁ x₂ s (v, v - δ s)))
    (hdiv : ∀ s, P s → weightedHellingerIntegral α (fun v => ψ (updPair x₁ x₂ s (v, v - δ s)))
      (κ₁ s.1.1) ((κ₂ s.2.1).map (fun w => w + δ s)) ≤ φ s) :
    RRhl α P φ (Cmd.random x₁ κ₁) (Cmd.random x₂ κ₂) Q ψ := by
  refine rrhl_rnd_fwdK_ae hα x₁ x₂ κ₁ κ₂ P Q φ ψ fun s hs => ?_
  have hsub : Measurable (fun v : EuclideanSpace ℝ (Fin d) => v - δ s) :=
    measurable_id.sub_const _
  have hadd : Measurable (fun w : EuclideanSpace ℝ (Fin d) => w + δ s) :=
    measurable_id.add_const _
  refine ⟨Kernel.deterministic (fun v => v - δ s) hsub,
    (κ₂ s.2.1).map (fun w => w + δ s),
    inferInstance, Measure.isFiniteMeasure_map _ _, ?_, ?_, ?_⟩
  · simp only [Kernel.deterministic_apply]
    rw [Measure.bind_dirac_eq_map _ hsub, Measure.map_map hsub hadd]
    have hco : ((fun v => v - δ s) ∘ fun w => w + δ s) = id :=
      funext fun w => add_sub_cancel_right w (δ s)
    rw [hco, Measure.map_id]
  · filter_upwards [hQhold s hs] with v hv
    rw [Kernel.deterministic_apply, ae_dirac_eq]
    exact Filter.eventually_pure.mpr hv
  · have h : ∀ v, (∫⁻ w, ψ (updPair x₁ x₂ s (v, w))
        ∂(Kernel.deterministic (fun v => v - δ s) hsub v))
        = ψ (updPair x₁ x₂ s (v, v - δ s)) := fun v => by
      rw [Kernel.deterministic_apply, lintegral_dirac]
    simpa only [h] using hdiv s hs

/-- **[Scale]**: the pre-budget and the post-weight may be multiplied by a positive finite
    constant. -/
theorem rrhl_scale {α : ℝ} (hα : 1 < α) {c : ℝ≥0∞} (hc0 : c ≠ 0) (hct : c ≠ ⊤)
    {P Q : St M × St M → Prop} {φ ψ : St M × St M → ℝ≥0∞} {c₁ c₂ : Cmd ident M}
    (h : RRhl α P φ c₁ c₂ Q ψ) :
    RRhl α P (fun s => c * φ s) c₁ c₂ Q (fun s => c * ψ s) := by
  intro s hs k₁ k₂ hk₁ hk₂ hk
  have hα0 : (0 : ℝ) < α := by linarith
  set d := c⁻¹ ^ (1 / α) with hd
  have hdα : d ^ α = c⁻¹ := by
    rw [hd, ← ENNReal.rpow_mul, one_div_mul_cancel hα0.ne', ENNReal.rpow_one]
  have hadm : TestAdmW α Q ψ (fun x => k₁ x * d) k₂ := by
    intro p hp
    show (k₁ p.1 * d) ^ α * k₂ p.2 ^ (1 - α) ≤ ψ p
    rw [ENNReal.mul_rpow_of_nonneg _ _ hα0.le, hdα]
    calc k₁ p.1 ^ α * c⁻¹ * k₂ p.2 ^ (1 - α)
        = c⁻¹ * (k₁ p.1 ^ α * k₂ p.2 ^ (1 - α)) := by ring
      _ ≤ c⁻¹ * (c * ψ p) := mul_le_mul' le_rfl (hk p hp)
      _ = ψ p := by rw [← mul_assoc, ENNReal.inv_mul_cancel hc0 hct, one_mul]
  have hv := h s hs (fun x => k₁ x * d) k₂ (hk₁.mul_const d) hk₂ hadm
  rw [testValC, lintegral_mul_const _ hk₁, ENNReal.mul_rpow_of_nonneg _ _ hα0.le, hdα] at hv
  rw [testValC]
  calc (∫⁻ a, k₁ a ∂osemA c₁ s.1) ^ α * (∫⁻ b, k₂ b ∂osemA c₂ s.2) ^ (1 - α)
      = c * (c⁻¹ * ((∫⁻ a, k₁ a ∂osemA c₁ s.1) ^ α * (∫⁻ b, k₂ b ∂osemA c₂ s.2) ^ (1 - α))) := by
        rw [← mul_assoc, ENNReal.mul_inv_cancel hc0 hct, one_mul]
    _ ≤ c * φ s := by
        refine mul_le_mul' le_rfl ?_
        calc c⁻¹ * ((∫⁻ a, k₁ a ∂osemA c₁ s.1) ^ α * (∫⁻ b, k₂ b ∂osemA c₂ s.2) ^ (1 - α))
            = (∫⁻ a, k₁ a ∂osemA c₁ s.1) ^ α * c⁻¹ * (∫⁻ b, k₂ b ∂osemA c₂ s.2) ^ (1 - α) := by
              ring
          _ ≤ φ s := hv

end Continuous
