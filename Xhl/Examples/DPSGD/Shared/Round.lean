import Xhl.Examples.DPSGD.Shared.Paper
import Xhl.Divergence.MixtureBind
import Xhl.Divergence.SubsamplingFlip
import Xhl.Divergence.SubsamplingDomination
import Xhl.Logic.Equiv.Local
import Xhl.Logic.Rrhl.Readout

/-!
# One round of Figure 1, semantically

The semantic facts the DP-SGD derivations use about a round of the programs of
`ReleasePrograms.lean`:

* the round's kernel: `noisyG` (the Gaussian at the clipped batch sum) and `fusedK` (the
  batch draw fused with it), its mixture forms `fusedK_mix_erase`/`fusedK_mix` over the
  shared draw `νb`, and the leaf bounds `hellingerIntegral_fusedK_le{,_flip,_sym}`;
* the invariants `DInv`/`DPost`/`LInv` and their invariance under the reset `rSt`;
* the per-round budgets `subDispBudgetSym` (`max(Υ, Λ)`) and `subDispBudget` (`Υ`), equal
  by `subDispBudgetSym_eq`, and the step bounds.
-/

open MeasureTheory ProbabilityTheory Continuous
open scoped NNReal ENNReal

namespace Continuous

section Generic

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

/-- The `q`-mixture `(1−q)·w₀ + q·w₁` of two kernels, with `q` read as `min q 1`. -/
noncomputable def mixKernel (q : ℝ≥0∞) (w₀ w₁ : Kernel A B) : Kernel A B where
  toFun a := (1 - q) • w₀ a + min q 1 • w₁ a
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
    simp only [Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact ((Kernel.measurable_coe w₀ hs).const_mul _).add ((Kernel.measurable_coe w₁ hs).const_mul _)

lemma mixKernel_apply (q : ℝ≥0∞) (w₀ w₁ : Kernel A B) (a : A) :
    mixKernel q w₀ w₁ a = (1 - q) • w₀ a + min q 1 • w₁ a := rfl

@[simp] lemma mixKernel_apply_of_le {q : ℝ≥0∞} (hq : q ≤ 1) (w₀ w₁ : Kernel A B) (a : A) :
    mixKernel q w₀ w₁ a = (1 - q) • w₀ a + q • w₁ a := by
  rw [mixKernel_apply, min_eq_left hq]

instance mixKernel_isMarkov (q : ℝ≥0∞) (K₀ K₁ : Kernel A B) [IsMarkovKernel K₀]
    [IsMarkovKernel K₁] : IsMarkovKernel (mixKernel q K₀ K₁) := by
  refine ⟨fun a => ⟨?_⟩⟩
  simp only [mixKernel_apply, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, measure_univ, mul_one]
  rcases le_total q 1 with hq | hq
  · rw [min_eq_left hq]; exact tsub_add_cancel_of_le hq
  · rw [min_eq_right hq, tsub_eq_zero_of_le hq, zero_add]

/-- The Hellinger integral of two measures of mass `1` is at least `1`. -/
lemma one_le_hellingerIntegral {α : ℝ} (hα : 1 < α) (μ ν : Measure A) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (hμ : μ Set.univ = 1) (hν : ν Set.univ = 1) : 1 ≤ hellingerIntegral α μ ν := by
  have h := testVal_le_hellingerIntegral_same hα (K₁ := fun _ => (1 : ℝ≥0∞)) (K₂ := fun _ => 1)
    measurable_const measurable_const μ ν (Filter.Eventually.of_forall fun _ => by simp)
  simpa [hμ, hν] using h

end Generic

section FuseMarkov

variable {ident : Type} {M : MemType ident} {tb : Ty}


instance fuseK_isMarkov {t : Ty} (b : Vars ident tb)
    (κ : @ProbabilityTheory.Kernel M.heap tb.interp M.heapMeas (Ty.measurableSpace tb))
    [IsMarkovKernel κ]
    (S : @ProbabilityTheory.Kernel M.heap t.interp M.heapMeas (Ty.measurableSpace t))
    [IsMarkovKernel S] : IsMarkovKernel (fuseK b κ S) := by
  refine ⟨fun m => ?_⟩
  rw [fuseK_apply]
  have hset : Measurable (fun B : tb.interp => M.set m tb b.name B) :=
    (M.set_measurable b.name).comp measurable_prodMk_left
  have hm : Measurable (fun B : tb.interp => S (M.set m tb b.name B)) :=
    S.measurable.comp hset
  refine ⟨?_⟩
  rw [Measure.bind_apply MeasurableSet.univ hm.aemeasurable]
  simp

end FuseMarkov

/-- **The budget of a round that spends `a` of the displacement**:
    `Υ_α(q, s, σ₂) · exp(α(α−1)(a/|γ|)²/(2σ₁))`, with `σ₁, σ₂` variances and
    `Υ_α = mixBudgetR` the subsampled-Gaussian budget. -/
noncomputable def subDispBudget (q : ℝ≥0) (s : ℝ) (σ1 σ2 : ℝ≥0) (γ a α : ℝ) : ℝ≥0∞ :=
  mixBudgetR q s σ2 α * ENNReal.ofReal (Real.exp (α * (α - 1) * (a / |γ|) ^ 2 / (2 * (σ1 : ℝ))))

/-- The same budget at symmetric adjacency: `max(Υ_α, Λ_α)` (`Λ_α = mixFlipBudgetE`, the
    record absent on the left) times the same displacement factor. -/
noncomputable def subDispBudgetSym (q : ℝ≥0) (s : ℝ) (σ1 σ2 : ℝ≥0) (γ a α : ℝ) : ℝ≥0∞ :=
  max (mixBudgetR q s σ2 α) (mixFlipBudgetE q s σ2 α) * ENNReal.ofReal (Real.exp (α * (α - 1) * (a / |γ|) ^ 2 / (2 * (σ1 : ℝ))))

/-- `Λ_α ≤ Υ_α` (Mironov–Talwar–Zhang), so the symmetric budget is `subDispBudget`. -/
lemma subDispBudgetSym_eq {α : ℝ} (hα : 1 < α) {q : ℝ≥0} (hq : (q : ℝ) ≤ 1)
    {σ1 σ2 : ℝ≥0} (hσ2 : σ2 ≠ 0) {s γ a : ℝ} :
    subDispBudgetSym q s σ1 σ2 γ a α = subDispBudget q s σ1 σ2 γ a α := by
  unfold subDispBudgetSym subDispBudget
  rw [max_mixBudgetR_mixFlipBudgetE hα hq hσ2 s]

lemma subDispBudget_ne_top {α : ℝ} (hα : 1 < α) {q : ℝ≥0} (hq : (q : ℝ) ≤ 1)
    {σ1 σ2 : ℝ≥0} (hσ2 : σ2 ≠ 0) (s γ a : ℝ) :
    subDispBudget q s σ1 σ2 γ a α ≠ ⊤ :=
  ENNReal.mul_ne_top (mixBudgetR_ne_top hα _ _ hσ2 hq) ENNReal.ofReal_ne_top

lemma subDispBudgetSym_ne_top {α : ℝ} (hα : 1 < α) {q : ℝ≥0} (hq : (q : ℝ) ≤ 1)
    {σ1 σ2 : ℝ≥0} (hσ2 : σ2 ≠ 0) (s γ a : ℝ) :
    subDispBudgetSym q s σ1 σ2 γ a α ≠ ⊤ := by
  rw [subDispBudgetSym_eq hα hq hσ2]; exact subDispBudget_ne_top hα hq hσ2 s γ a

lemma subDispBudgetSym_ne_zero {α : ℝ} (hα : 1 < α) {q : ℝ≥0} (hq : (q : ℝ) ≤ 1)
    {σ1 σ2 : ℝ≥0} (hσ2 : σ2 ≠ 0) {s γ a : ℝ} :
    subDispBudgetSym q s σ1 σ2 γ a α ≠ 0 :=
  mul_ne_zero
    (ne_of_gt (lt_of_lt_of_le zero_lt_one ((one_le_mixBudgetR hα hσ2 hq s).trans (le_max_left _ _))))
    (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'

end Continuous

namespace DPSGDPaper

/-! ## The round's kernel -/

section Kernel

variable (N dx d : ℕ)
  (grad : EuclideanSpace ℝ (Fin dx) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
  (C : ℝ≥0)
  (v q : ℝ≥0) (i : Fin (N + 1))

/-- The clipped batch sum as a function of the batch, read in a memory. -/
noncomputable def cbs (m : PMem.heap) (B : Finset (Fin (N + 1))) : EuclideanSpace ℝ (Fin d) :=
  clippedBatchSumD (N := N) grad C B (getR N dx m) (getTh d m)

/-- The Gaussian of the clipped sum of the batch held in memory, at variance `v`. -/
noncomputable def noisyG (hm : MeasOK dx d grad) :
    @ProbabilityTheory.Kernel PMem.heap (EuclideanSpace ℝ (Fin d)) PMem.heapMeas
      (Ty.measurableSpace (.vec d)) :=
  gaussKernelE (esem (batchSumPaperE N dx d grad C hm))
    (batchSumPaperE N dx d grad C hm).measurable v

@[simp] lemma noisyG_apply (hm : MeasOK dx d grad) (h : PMem.heap) :
    noisyG N dx d grad C v hm h
      = gaussE (esem (batchSumPaperE N dx d grad C hm) h) v := rfl

/-- `noisyG` is Markov (stated directly: the generic `gaussKernelE` instance is keyed on a
    different measurable-space instance). -/
instance isMarkov_noisyG (hm : MeasOK dx d grad) :
    IsMarkovKernel (noisyG N dx d grad C v hm) :=
  ⟨fun h => by rw [noisyG_apply]; infer_instance⟩

/-- **The fused sampler**: the Poisson batch draw fused with `noisyG`. -/
noncomputable def fusedK (hm : MeasOK dx d grad) :
    @ProbabilityTheory.Kernel PMem.heap (EuclideanSpace ℝ (Fin d)) PMem.heapMeas
      (Ty.measurableSpace (.vec d)) :=
  fuseK (t := .vec d) (bchV N) (poissonBatchKernel N q) (noisyG N dx d grad C v hm)

instance isMarkov_fusedK (hm : MeasOK dx d grad) :
    IsMarkovKernel (fusedK N dx d grad C v q hm) :=
  fuseK_isMarkov (t := .vec d) (bchV N) (poissonBatchKernel N q) _

lemma fusedK_apply (hm : MeasOK dx d grad) (x : PMem.heap) :
    fusedK N dx d grad C v q hm x
      = (batchFrom N q (N + 1) 0 ∅).bind (fun B => gaussE (cbs N dx d grad C x B) v) := by
  rw [fusedK, fuseK_apply, poissonBatchKernel_apply]
  congr 1
  funext B
  show gaussE (cbs N dx d grad C (PMem.set x (.finset (N + 1)) (bchV N).name B)
      (getBatch N (PMem.set x (.finset (N + 1)) (bchV N).name B))) v = _
  unfold cbs getBatch getTh
  have hB : (bchV N).name = "B" := rfl
  rw [hB, PMem.get_set_eq,
    getR_set N dx _ (t := .finset (N + 1)) _ _ (Or.inl (fun h => Ty.noConfusion h)),
    PMem.get_set_ne _ _ _ _ _ _ (Or.inl (by intro h; cases h))]

/-- The batch law with record `i` erased: the draw both datasets share. -/
noncomputable def νb : Measure (Finset (Fin (N + 1))) :=
  (batchFrom N q (N + 1) 0 ∅).map (fun S => S.erase i)

instance isProb_νb : IsProbabilityMeasure (νb N q i) := by
  have := isProb_batchFrom N q (N + 1) 0 ∅
  exact Measure.isProbabilityMeasure_map Measurable.of_discrete.aemeasurable

/-- **The fused sampler as a mixture**: record `i` left out with probability `1 − q` and
    put in with probability `q`, over the Poisson draw of the others. -/
lemma fusedK_mix_erase (hm : MeasOK dx d grad) (hq : q ≤ 1) (x : PMem.heap) :
    fusedK N dx d grad C v q hm x
      = (νb N q i).bind (fun S =>
          (1 - (q : ℝ≥0∞)) • gaussE (cbs N dx d grad C x (S.erase i)) v
          + (q : ℝ≥0∞) • gaussE (cbs N dx d grad C x (insert i S)) v) := by
  have hG : Measurable (fun B : Finset (Fin (N + 1)) => gaussE (cbs N dx d grad C x B) v) :=
    Measurable.of_discrete
  have hK : Measurable (fun S : Finset (Fin (N + 1)) =>
      (1 - (q : ℝ≥0∞)) • Measure.dirac (S.erase i) +
        (q : ℝ≥0∞) • Measure.dirac (insert i S)) := Measurable.of_discrete
  have hν : (batchFrom N q (N + 1) 0 ∅).map (fun S => S.erase i) = νb N q i := rfl
  rw [fusedK_apply N dx d grad C v q hm, batchFrom_eq_mix_erase N hq i, hν,
    Measure.bind_bind hK.aemeasurable hG.aemeasurable]
  congr 1
  funext S
  rw [add_bind' _ _ hG, smul_bind' _ _ hG, smul_bind' _ _ hG, Measure.dirac_bind hG,
    Measure.dirac_bind hG]

/-- **The fused sampler as a mixture over the common draw `νb`.** -/
lemma fusedK_mix (hm : MeasOK dx d grad) (hq : q ≤ 1) (x : PMem.heap) :
    fusedK N dx d grad C v q hm x
      = (νb N q i).bind (fun B =>
          (1 - (q : ℝ≥0∞)) • gaussE (cbs N dx d grad C x B) v
          + (q : ℝ≥0∞) • gaussE (cbs N dx d grad C x (insert i B)) v) := by
  rw [fusedK_mix_erase N dx d grad C v q i hm hq, νb,
    ← bind_comp_eq _ Measurable.of_discrete Measurable.of_discrete,
    ← bind_comp_eq _ Measurable.of_discrete Measurable.of_discrete]
  congr 1
  funext S
  beta_reduce
  rw [Finset.erase_idem]

/-- The Gaussian at the clipped sum of a batch with record `i` erased. -/
noncomputable def offK (m : PMem.heap) :
    Kernel (Finset (Fin (N + 1))) (EuclideanSpace ℝ (Fin d)) :=
  ⟨fun S => gaussE (cbs N dx d grad C m (S.erase i)) v, Measurable.of_discrete⟩

/-- The Gaussian at the clipped sum of a batch with record `i` inserted. -/
noncomputable def onK (m : PMem.heap) :
    Kernel (Finset (Fin (N + 1))) (EuclideanSpace ℝ (Fin d)) :=
  ⟨fun S => gaussE (cbs N dx d grad C m (insert i S)) v, Measurable.of_discrete⟩

instance (m : PMem.heap) : IsMarkovKernel (offK N dx d grad C v i m) :=
  ⟨fun _ => by show IsProbabilityMeasure (gaussE _ _); infer_instance⟩

instance (m : PMem.heap) : IsMarkovKernel (onK N dx d grad C v i m) :=
  ⟨fun _ => by show IsProbabilityMeasure (gaussE _ _); infer_instance⟩

/-- At adjacent datasets and equal models, the sampler of the dataset holding record `i`
    is, batch by batch, the `q`-mixture of `offK` and `onK`. -/
lemma fusedK_eq_mix_of_adj (hm : MeasOK dx d grad) (hq : q ≤ 1) {m₁ m₂ : PMem.heap}
    (hadj : AdjAt (getR N dx) i m₁ m₂) (hth : getTh d m₁ = getTh d m₂) :
    fusedK N dx d grad C v q hm m₁ = (νb N q i).bind
      (mixKernel (q : ℝ≥0∞) (offK N dx d grad C v i m₂) (onK N dx d grad C v i m₁)) := by
  have hqE : (q : ℝ≥0∞) ≤ 1 := by exact_mod_cast hq
  rw [fusedK_mix_erase N dx d grad C v q i hm hq]
  refine congrArg (Measure.bind _) (funext fun S => ?_)
  rw [mixKernel_apply_of_le hqE]
  show (1 - (q : ℝ≥0∞)) • gaussE (cbs N dx d grad C m₁ (S.erase i)) v
      + (q : ℝ≥0∞) • gaussE (cbs N dx d grad C m₁ (insert i S)) v
    = (1 - (q : ℝ≥0∞)) • gaussE (cbs N dx d grad C m₂ (S.erase i)) v
      + (q : ℝ≥0∞) • gaussE (cbs N dx d grad C m₁ (insert i S)) v
  unfold cbs
  rw [clippedBatchSumD_eq_of_adj N dx d grad C i hadj, hth]

/-- The sampler of the dataset missing record `i` is, batch by batch, `offK`. -/
lemma fusedK_eq_off_of_adj (hm : MeasOK dx d grad) (hq : q ≤ 1) {m₁ m₂ : PMem.heap}
    (hadj : AdjAt (getR N dx) i m₁ m₂) :
    fusedK N dx d grad C v q hm m₂ = (νb N q i).bind (offK N dx d grad C v i m₂) := by
  have hqE : (q : ℝ≥0∞) ≤ 1 := by exact_mod_cast hq
  rw [fusedK_mix_erase N dx d grad C v q i hm hq]
  congr 1
  funext S
  show (1 - (q : ℝ≥0∞)) • gaussE (cbs N dx d grad C m₂ (S.erase i)) v
      + (q : ℝ≥0∞) • gaussE (cbs N dx d grad C m₂ (insert i S)) v
    = gaussE (cbs N dx d grad C m₂ (S.erase i)) v
  unfold cbs
  rw [clippedBatchSumD_insert_eq_erase_of_adj N dx d grad C i hadj,
    ← add_smul, tsub_add_cancel_of_le hqE, one_smul]

/-- The inserted-record Gaussian is the erased one translated by `shiftPaper`, of norm at
    most `C`. -/
lemma cbs_add_shiftPaper_of_adj {m₁ m₂ : PMem.heap}
    (hadj : AdjAt (getR N dx) i m₁ m₂) (hth : getTh d m₁ = getTh d m₂)
    (S : Finset (Fin (N + 1))) :
    cbs N dx d grad C m₂ (S.erase i) + shiftPaper N dx d grad C i m₁ S
      = cbs N dx d grad C m₁ (insert i S) := by
  unfold shiftPaper cbs
  rw [clippedBatchSumD_eq_of_adj N dx d grad C i hadj, hth, add_sub_cancel]

/-- Leaf bound of the fused samplers at adjacent datasets and equal models, record `i`
    absent on the right: `Υ_α`. -/
theorem hellingerIntegral_fusedK_le {α : ℝ} (hα : 1 < α) (hm : MeasOK dx d grad)
    (hq1 : (q : ℝ) ≤ 1) (hv : v ≠ 0)
    {m₁ m₂ : PMem.heap} (hadj : AdjAt (getR N dx) i m₁ m₂)
    (hth : getTh d m₁ = getTh d m₂) :
    hellingerIntegral α (fusedK N dx d grad C v q hm m₁) (fusedK N dx d grad C v q hm m₂)
      ≤ mixBudgetR q (C : ℝ) v α := by
  have hqE : (q : ℝ≥0∞) ≤ 1 := by exact_mod_cast hq1
  have hν : IsProbabilityMeasure (νb N q i) := isProb_νb N q i
  rw [fusedK_eq_mix_of_adj N dx d grad C v q i hm hq1 hadj hth,
    fusedK_eq_off_of_adj N dx d grad C v q i hm hq1 hadj]
  refine hellingerIntegral_bind_le_const hα _ _ _
    (ne_of_gt (lt_of_lt_of_le zero_lt_one (one_le_mixBudgetR hα hv hq1 _)))
    fun S => ?_
  have hleaf := hellingerIntegral_sgMixtureE_le_mixBudgetR hα
    (cbs N dx d grad C m₂ (S.erase i)) (shiftPaper N dx d grad C i m₁ S)
    v hv q (by exact_mod_cast hq1) (norm_shiftPaper_le N dx d grad C i m₁ S)
  rw [cbs_add_shiftPaper_of_adj N dx d grad C i hadj hth] at hleaf
  rw [mixKernel_apply_of_le hqE]
  exact hleaf

/-- The mirror case, record `i` absent on the left: `Λ_α = mixFlipBudgetE`. -/
theorem hellingerIntegral_fusedK_le_flip {α : ℝ} (hα : 1 < α) (hm : MeasOK dx d grad)
    (hC : 0 < (C : ℝ)) (hq1 : (q : ℝ) < 1) (hv : v ≠ 0)
    {m₁ m₂ : PMem.heap} (hadj : AdjAt (getR N dx) i m₂ m₁)
    (hth : getTh d m₁ = getTh d m₂) :
    hellingerIntegral α (fusedK N dx d grad C v q hm m₁) (fusedK N dx d grad C v q hm m₂)
      ≤ mixFlipBudgetE q (C : ℝ) v α := by
  have hqE : (q : ℝ≥0∞) ≤ 1 := by exact_mod_cast hq1.le
  have hν : IsProbabilityMeasure (νb N q i) := isProb_νb N q i
  rw [fusedK_eq_off_of_adj N dx d grad C v q i hm hq1.le hadj,
    fusedK_eq_mix_of_adj N dx d grad C v q i hm hq1.le hadj hth.symm]
  refine hellingerIntegral_bind_le_const hα _ _ _ (mixFlipBudgetE_ne_zero hα hq1 hv hC.le)
    fun S => ?_
  have hleaf := hellingerIntegral_flip_sgMixtureE_le_budget_of_le hα
    (cbs N dx d grad C m₁ (S.erase i)) (shiftPaper N dx d grad C i m₂ S)
    v hv hq1 (norm_shiftPaper_le N dx d grad C i m₂ S)
  rw [cbs_add_shiftPaper_of_adj N dx d grad C i hadj hth.symm] at hleaf
  rw [mixKernel_apply_of_le hqE]
  exact hleaf

/-- The leaf bound at symmetric adjacency: `max(Υ_α, Λ_α)`. -/
theorem hellingerIntegral_fusedK_le_sym {α : ℝ} (hα : 1 < α) (hm : MeasOK dx d grad)
    (hC : 0 < (C : ℝ)) (hq1 : (q : ℝ) < 1) (hv : v ≠ 0)
    {m₁ m₂ : PMem.heap} (hadj : AdjAtSym (recBotN N dx) i (getDS N dx m₁) (getDS N dx m₂))
    (hth : getTh d m₁ = getTh d m₂) :
    hellingerIntegral α (fusedK N dx d grad C v q hm m₁) (fusedK N dx d grad C v q hm m₂)
      ≤ max (mixBudgetR q (C : ℝ) v α) (mixFlipBudgetE q (C : ℝ) v α) := by
  have hadj' : AdjAtSym (getR N dx) i m₁ m₂ := (adjAtSym_recBotN_iff N dx).1 hadj
  rcases hadj' with h | h
  · exact (hellingerIntegral_fusedK_le N dx d grad C v q i hα hm hq1.le hv h
      hth).trans (le_max_left _ _)
  · exact (hellingerIntegral_fusedK_le_flip N dx d grad C v q i hα hm hC hq1 hv h
      hth).trans (le_max_right _ _)

end Kernel

/-! ## The invariants -/

section Invariants

variable (N dx d : ℕ) (i : Fin (N + 1))

/-- The invariant of the rounds: adjacent datasets, models at distance at most `z`, equal
    transcripts. -/
def DInv (z : ℝ) (st : St PMem × St PMem) : Prop :=
  AdjAtSym (recBotN N dx) i (PMem.get st.1.1 (.prod (.vec ((N + 1) * dx)) (.finset (N + 1))) (dsV N dx).name)
      (PMem.get st.2.1 (.prod (.vec ((N + 1) * dx)) (.finset (N + 1))) (dsV N dx).name) ∧
    ‖PMem.get st.1.1 (.vec d) (thV d).name - PMem.get st.2.1 (.vec d) (thV d).name‖ ≤ z ∧
    st.1.2 = st.2.2

/-- The postcondition of the block: the values `θ − γ·g̃` are at distance at most `z'`. -/
def DPost (γ z' : ℝ) (st : St PMem × St PMem) : Prop :=
  ‖(PMem.get st.1.1 (.vec d) (thV d).name - γ • PMem.get st.1.1 (.vec d) (gtV d).name)
      - (PMem.get st.2.1 (.vec d) (thV d).name - γ • PMem.get st.2.1 (.vec d) (gtV d).name)‖
      ≤ z' ∧
    AdjAtSym (recBotN N dx) i (PMem.get st.1.1 (.prod (.vec ((N + 1) * dx)) (.finset (N + 1))) (dsV N dx).name)
      (PMem.get st.2.1 (.prod (.vec ((N + 1) * dx)) (.finset (N + 1))) (dsV N dx).name) ∧ st.1.2 = st.2.2

/-- The invariant family of the loop: `DInv` with the counter pinned on both sides. -/
def LInv (z : ℕ → ℝ) (k : ℕ) (s : St PMem × St PMem) : Prop :=
  DInv N dx d i (z k) s ∧ getCnt s.1.1 = k ∧ getCnt s.2.1 = k

/-- The reset of the hidden variables on states. -/
noncomputable def rSt (s : St PMem) : St PMem := (obsPaper N d s.1, s.2)

lemma DInv_rSt (z : ℝ) (s : St PMem × St PMem) :
    DInv N dx d i z (rSt N d s.1, rSt N d s.2) ↔ DInv N dx d i z s := by
  unfold DInv rSt
  show AdjAtSym (recBotN N dx) i (getDS N dx (obsPaper N d s.1.1)) (getDS N dx (obsPaper N d s.2.1)) ∧
      ‖getTh d (obsPaper N d s.1.1) - getTh d (obsPaper N d s.2.1)‖ ≤ z ∧ s.1.2 = s.2.2 ↔
    AdjAtSym (recBotN N dx) i (getDS N dx s.1.1) (getDS N dx s.2.1) ∧ ‖getTh d s.1.1 - getTh d s.2.1‖ ≤ z ∧ s.1.2 = s.2.2
  rw [getDS_obsPaper, getDS_obsPaper, getTh_obsPaper, getTh_obsPaper]

lemma DPost_rSt (γ z' : ℝ) (s : St PMem × St PMem) :
    DPost N dx d i γ z' (rSt N d s.1, rSt N d s.2) ↔ DPost N dx d i γ z' s := by
  unfold DPost rSt
  show ‖(getTh d (obsPaper N d s.1.1) - γ • getGt d (obsPaper N d s.1.1))
      - (getTh d (obsPaper N d s.2.1) - γ • getGt d (obsPaper N d s.2.1))‖ ≤ z' ∧
      AdjAtSym (recBotN N dx) i (getDS N dx (obsPaper N d s.1.1)) (getDS N dx (obsPaper N d s.2.1)) ∧ s.1.2 = s.2.2 ↔
    ‖(getTh d s.1.1 - γ • getGt d s.1.1) - (getTh d s.2.1 - γ • getGt d s.2.1)‖ ≤ z' ∧
      AdjAtSym (recBotN N dx) i (getDS N dx s.1.1) (getDS N dx s.2.1) ∧ s.1.2 = s.2.2
  rw [getDS_obsPaper, getDS_obsPaper, getTh_obsPaper, getTh_obsPaper, getGt_obsPaper, getGt_obsPaper]

end Invariants

/-! ## The step bounds -/

section Steps

variable (N dx d : ℕ)
  (grad : EuclideanSpace ℝ (Fin dx) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
  (C : ℝ≥0) (i : Fin (N + 1))

/-- The clipped sum of a batch has norm at most `(N+1)·C`. -/
lemma norm_cbs_le (m : PMem.heap)
    (B : Finset (Fin (N + 1))) : ‖cbs N dx d grad C m B‖ ≤ (N + 1) * C := by
  unfold cbs clippedBatchSumD
  refine (norm_sum_le _ _).trans ?_
  calc ∑ j ∈ B, ‖clipV C (gradBot grad (getR N dx m j) (getTh d m))‖ ≤ ∑ _j ∈ B, (C : ℝ) :=
        Finset.sum_le_sum fun j _ => norm_clipV_le C.2 _
    _ = B.card * C := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (N + 1) * C := by
        refine mul_le_mul_of_nonneg_right ?_ (by exact_mod_cast C.2)
        have := Finset.card_le_univ B
        rw [Fintype.card_fin] at this
        exact_mod_cast this

/-- Without a hypothesis on the loss, one gradient step moves two models apart by at most
    `2·|γ|·(N+1)·C`. -/
lemma step_le_any (γ : ℝ) (x y : PMem.heap)
    (B : Finset (Fin (N + 1))) {z : ℝ} (hz : ‖getTh d x - getTh d y‖ ≤ z) :
    ‖(getTh d x - γ • cbs N dx d grad C x B) - (getTh d y - γ • cbs N dx d grad C y B)‖
      ≤ z + 2 * |γ| * ((N + 1) * C) := by
  have e : (getTh d x - γ • cbs N dx d grad C x B) - (getTh d y - γ • cbs N dx d grad C y B)
      = (getTh d x - getTh d y) - γ • cbs N dx d grad C x B + γ • cbs N dx d grad C y B := by
    abel
  rw [e]
  have h1 : ‖γ • cbs N dx d grad C x B‖ ≤ |γ| * ((N + 1) * C) := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (norm_cbs_le N dx d grad C x B) (abs_nonneg γ)
  have h2 : ‖γ • cbs N dx d grad C y B‖ ≤ |γ| * ((N + 1) * C) := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (norm_cbs_le N dx d grad C y B) (abs_nonneg γ)
  calc ‖(getTh d x - getTh d y) - γ • cbs N dx d grad C x B + γ • cbs N dx d grad C y B‖
      ≤ ‖(getTh d x - getTh d y) - γ • cbs N dx d grad C x B‖
        + ‖γ • cbs N dx d grad C y B‖ := norm_add_le _ _
    _ ≤ (‖getTh d x - getTh d y‖ + ‖γ • cbs N dx d grad C x B‖)
        + ‖γ • cbs N dx d grad C y B‖ := add_le_add (norm_sub_le _ _) le_rfl
    _ ≤ z + 2 * |γ| * ((N + 1) * C) := by linarith

/-- On a common batch without record `i`, the two clipped sums agree. -/
lemma cbs_eq_of_adj {x y : PMem.heap} (hadj : AdjAt (getR N dx) i x y)
    (B : Finset (Fin (N + 1))) (hB : i ∉ B) (u : EuclideanSpace ℝ (Fin d)) :
    clippedBatchSumD (N := N) grad C B (getR N dx x) u
      = clippedBatchSumD (N := N) grad C B (getR N dx y) u := by
  have := clippedBatchSumD_eq_of_adj N dx d grad C i hadj u B
  rwa [Finset.erase_eq_of_notMem hB] at this

/-- `cbs_eq_of_adj` at symmetric adjacency. -/
lemma cbs_eq_of_adjS {x y : PMem.heap} (hadj : AdjAtSym (recBotN N dx) i (getDS N dx x) (getDS N dx y))
    (B : Finset (Fin (N + 1))) (hB : i ∉ B) (u : EuclideanSpace ℝ (Fin d)) :
    clippedBatchSumD (N := N) grad C B (getR N dx x) u
      = clippedBatchSumD (N := N) grad C B (getR N dx y) u :=
  ((adjAtSym_recBotN_iff N dx).1 hadj : AdjAtSym (getR N dx) i x y).elim
    (fun h => cbs_eq_of_adj N dx d grad C i h B hB u)
    (fun h => (cbs_eq_of_adj N dx d grad C i h B hB u).symm)

end Steps

end DPSGDPaper
