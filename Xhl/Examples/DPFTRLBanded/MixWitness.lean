import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Xhl.Examples.DPFTRLBanded.GaussBlocks

/-!
# The [Samp-Dec] witnesses for a subsampled Gaussian (Appendix D.5)

Both runs draw `w ~ Bern(q) ⊗ 𝒩(0, σ²I)` (the draw (45)), and the postcondition asks for
one run's noise to be the other's shifted by its coin times `Δ`.  For **[Samp-Dec]**
(Fig. 9) the right value is drawn from a kernel `F` given the left one, and the witness
`ν` satisfies `ν.bind F = Bern(q) ⊗ 𝒩(0, σ²I)`.  `sampFwdK_mix_witness` prices the
left-coin orientation at the mixture `Υ_α`; `sampFwdK_flip_witness` the right-coin one at
the reversed leaf `Λ_α`. -/

open MeasureTheory ProbabilityTheory ENNReal Set
open scoped NNReal

namespace DPFTRL.Band

open Continuous

variable {K : ℕ}

/-- The forward kernel at the block draw: a fresh right coin, and the right noises equal
    to the left ones shifted by `u·Δ` when the left coin `u` came up. -/
noncomputable def fwdShiftK (q : ℝ≥0) (Δ : EuclideanSpace ℝ (Fin K)) :
    ProbabilityTheory.Kernel (Bool × EuclideanSpace ℝ (Fin K))
      (Bool × EuclideanSpace ℝ (Fin K)) :=
  (ProbabilityTheory.Kernel.const _ (bernoulliMeasure q)).prod
    (ProbabilityTheory.Kernel.deterministic
      (fun v : Bool × EuclideanSpace ℝ (Fin K) => v.2 + if v.1 then Δ else 0)
      (measurable_snd.add
        ((measurable_of_countable (fun b : Bool => if b then Δ else 0)).comp
          measurable_fst)))

instance isMarkov_fwdShiftK (q : ℝ≥0) (Δ : EuclideanSpace ℝ (Fin K)) :
    IsMarkovKernel (fwdShiftK (K := K) q Δ) := by
  unfold fwdShiftK
  infer_instance

lemma fwdShiftK_apply (q : ℝ≥0) (Δ : EuclideanSpace ℝ (Fin K))
    (v : Bool × EuclideanSpace ℝ (Fin K)) :
    fwdShiftK (K := K) q Δ v
      = (bernoulliMeasure q).prod (Measure.dirac (v.2 + if v.1 then Δ else 0)) := by
  unfold fwdShiftK
  rw [ProbabilityTheory.Kernel.prod_apply, ProbabilityTheory.Kernel.const_apply,
    ProbabilityTheory.Kernel.deterministic_apply]

/-- The forward kernel almost surely realizes the shift. -/
lemma fwdShiftK_ae (q : ℝ≥0) (Δ : EuclideanSpace ℝ (Fin K))
    (v : Bool × EuclideanSpace ℝ (Fin K)) :
    ∀ᵐ w ∂(fwdShiftK (K := K) q Δ v), w.2 = v.2 + if v.1 then Δ else 0 := by
  rw [fwdShiftK_apply, ae_iff]
  have he : {w : Bool × EuclideanSpace ℝ (Fin K) |
      ¬ w.2 = v.2 + if v.1 then Δ else 0}
      = Set.univ ×ˢ ({v.2 + if v.1 then Δ else 0}ᶜ) := by
    ext w
    simp [Set.mem_prod]
  rw [he, Measure.prod_prod, Measure.dirac_apply' _ (measurableSet_singleton _).compl]
  simp

/-- The shift of the noises by the coin: `Δ` if the coin came up, `0` otherwise. -/
noncomputable def shB (Δ : EuclideanSpace ℝ (Fin K)) (b : Bool) : EuclideanSpace ℝ (Fin K) :=
  if b then Δ else 0

lemma measurable_shB (Δ : EuclideanSpace ℝ (Fin K)) : Measurable (shB Δ) :=
  measurable_of_countable _

/-- **The joint law of the shifted noise and the coin**: a coin `u ~ Bern(q)` and a noise
    `z ~ 𝒩(0, σ²I)`, recorded as `(z + u·Δ, u)`.  Its first marginal is the mixture
    (`mixJoint_fst`), and undoing the shift recovers the draw (`mixJoint_map_unshift`). -/
noncomputable def mixJoint (q σ2 : ℝ≥0) (Δ : EuclideanSpace ℝ (Fin K)) :
    Measure (EuclideanSpace ℝ (Fin K) × Bool) :=
  ((bernoulliMeasure q).prod (gaussE 0 σ2)).map (fun p => (p.2 + shB Δ p.1, p.1))

lemma measurable_shiftPair (Δ : EuclideanSpace ℝ (Fin K)) :
    Measurable (fun p : Bool × EuclideanSpace ℝ (Fin K) => (p.2 + shB Δ p.1, p.1)) :=
  (measurable_snd.add ((measurable_shB Δ).comp measurable_fst)).prodMk measurable_fst

lemma measurable_unshiftPair (Δ : EuclideanSpace ℝ (Fin K)) :
    Measurable (fun p : EuclideanSpace ℝ (Fin K) × Bool => (p.2, p.1 - shB Δ p.2)) :=
  measurable_snd.prodMk (measurable_fst.sub ((measurable_shB Δ).comp measurable_snd))

instance (q σ2 : ℝ≥0) (Δ : EuclideanSpace ℝ (Fin K)) : IsProbabilityMeasure (mixJoint q σ2 Δ) := by
  haveI : IsProbabilityMeasure (bernoulliMeasure q) := isProb_bernoulliMeasure q
  haveI : IsProbabilityMeasure (gaussE (0 : EuclideanSpace ℝ (Fin K)) σ2) := by
    unfold gaussE; exact Measure.isProbabilityMeasure_map (by fun_prop)
  exact Measure.isProbabilityMeasure_map (measurable_shiftPair Δ).aemeasurable

/-- The first marginal of the joint law is the mixture. -/
lemma mixJoint_fst {q : ℝ≥0} (hq : q ≤ 1) (σ2 : ℝ≥0) (Δ : EuclideanSpace ℝ (Fin K)) :
    (mixJoint q σ2 Δ).fst = (1 - (q : ℝ≥0∞)) • gaussE 0 σ2 + (q : ℝ≥0∞) • gaussE Δ σ2 := by
  have hφ := measurable_shiftPair (K := K) Δ
  rw [Measure.fst, mixJoint, Measure.map_map measurable_fst hφ]
  ext A hA
  have hpre : MeasurableSet ((Prod.fst ∘ fun p : Bool × EuclideanSpace ℝ (Fin K) =>
      (p.2 + shB Δ p.1, p.1)) ⁻¹' A) := (measurable_fst.comp hφ) hA
  have hsh := gaussE_map_add_const (σ2 := σ2) (0 : EuclideanSpace ℝ (Fin K)) Δ
  rw [zero_add] at hsh
  rw [Measure.map_apply (measurable_fst.comp hφ) hA, Measure.prod_apply hpre,
    bernoulliMeasure_of_le hq, lintegral_add_measure, lintegral_smul_measure,
    lintegral_smul_measure, lintegral_dirac, lintegral_dirac, Measure.add_apply,
    Measure.smul_apply, Measure.smul_apply, ← hsh,
    Measure.map_apply (measurable_add_const Δ) hA, smul_eq_mul, smul_eq_mul]
  congr 2
  · congr 1; ext z; simp [shB]

/-- Undoing the shift recovers the draw. -/
lemma mixJoint_map_unshift (q σ2 : ℝ≥0) (Δ : EuclideanSpace ℝ (Fin K)) :
    (mixJoint q σ2 Δ).map (fun p => (p.2, p.1 - shB Δ p.2))
      = (bernoulliMeasure q).prod (gaussE 0 σ2) := by
  rw [mixJoint, Measure.map_map (measurable_unshiftPair Δ) (measurable_shiftPair Δ)]
  have hid : ((fun p : EuclideanSpace ℝ (Fin K) × Bool => (p.2, p.1 - shB Δ p.2)) ∘
      fun p : Bool × EuclideanSpace ℝ (Fin K) => (p.2 + shB Δ p.1, p.1)) = id := by
    funext p; simp
  rw [hid, Measure.map_id]

/-- **The witness of [Samp-Dec] at the block draw**: the posterior coupling, pushed to
    the left value space.  The kernel recovers the right sampler from it, and the
    Hellinger integral of the left sampler against it is that of the mixture. -/
theorem sampFwdK_mix_witness {α : ℝ} (hα : 1 < α) (σ2 : ℝ≥0) (hσ : σ2 ≠ 0) (q : ℝ≥0)
    (hq : q ≤ 1) (Δ : EuclideanSpace ℝ (Fin K)) :
    ∃ ν : Measure (Bool × EuclideanSpace ℝ (Fin K)), IsFiniteMeasure ν ∧
      ν.bind (fun v => fwdShiftK (K := K) q Δ v)
        = (bernoulliMeasure q).prod (gaussE 0 σ2) ∧
      hellingerIntegral α ((bernoulliMeasure q).prod (gaussE 0 σ2)) ν
        ≤ hellingerIntegral α ((1 - (q : ℝ≥0∞)) • gaussE 0 σ2 + (q : ℝ≥0∞) • gaussE Δ σ2)
            (gaussE 0 σ2) := by
  set Bn := bernoulliMeasure q with hBn
  haveI : IsProbabilityMeasure Bn := isProb_bernoulliMeasure q
  have hgP : ∀ c : EuclideanSpace ℝ (Fin K), IsProbabilityMeasure (gaussE c σ2) := fun c => by
    unfold gaussE; exact Measure.isProbabilityMeasure_map (by fun_prop)
  set N0 : Measure (EuclideanSpace ℝ (Fin K)) := gaussE 0 σ2 with hN0
  haveI : IsProbabilityMeasure N0 := hgP 0
  set Mix := (1 - (q : ℝ≥0∞)) • N0 + (q : ℝ≥0∞) • gaussE Δ σ2 with hMix
  haveI : IsFiniteMeasure Mix := ⟨by
    rw [hMix, Measure.add_apply, Measure.smul_apply, Measure.smul_apply, measure_univ,
      measure_univ, smul_eq_mul, smul_eq_mul, mul_one, mul_one]
    exact ENNReal.add_lt_top.mpr ⟨lt_of_le_of_lt tsub_le_self ENNReal.one_lt_top,
      ENNReal.coe_lt_top⟩⟩
  set ρ := mixJoint q σ2 Δ with hρ
  have hfst : ρ.fst = Mix := mixJoint_fst hq σ2 Δ
  set κ := ρ.condKernel with hκ
  have hdis : Mix ⊗ₘ κ = ρ := by rw [← hfst]; exact ρ.disintegrate ρ.condKernel
  set ψ : EuclideanSpace ℝ (Fin K) × Bool → Bool × EuclideanSpace ℝ (Fin K) :=
    fun p => (p.2, p.1 - shB Δ p.2) with hψdef
  have hψ : Measurable ψ := measurable_unshiftPair Δ
  -- the left sampler is `ρ` pushed along `ψ`
  have hρψ : ρ.map ψ = Bn.prod N0 := mixJoint_map_unshift q σ2 Δ
  set ν := (N0 ⊗ₘ κ).map ψ with hνdef
  haveI : IsFiniteMeasure ν := Measure.isFiniteMeasure_map _ _
  refine ⟨ν, inferInstance, ?_, ?_⟩
  · -- the kernel recovers the right sampler: `ν.bind F = Bn.prod N0`
    have hFψ : ∀ p : EuclideanSpace ℝ (Fin K) × Bool,
        fwdShiftK (K := K) q Δ (ψ p) = Bn.prod (Measure.dirac p.1) := by
      intro p
      rw [fwdShiftK_apply]
      have harg : ((ψ p).2 + if (ψ p).1 then Δ else 0) = p.1 := by
        show p.1 - shB Δ p.2 + (if p.2 then Δ else 0) = p.1
        rw [show (if p.2 then Δ else 0) = shB Δ p.2 from rfl, sub_add_cancel]
      rw [harg]
    refine Measure.ext fun s hs => ?_
    rw [Measure.bind_apply hs (fwdShiftK (K := K) q Δ).measurable.aemeasurable, hνdef,
      lintegral_map ((fwdShiftK (K := K) q Δ).measurable_coe hs) hψ]
    have hpt : ∀ p : EuclideanSpace ℝ (Fin K) × Bool,
        fwdShiftK (K := K) q Δ (ψ p) s
          = ∫⁻ u, Measure.dirac p.1 (Prod.mk u ⁻¹' s) ∂Bn := by
      intro p
      rw [hFψ p, Measure.prod_apply hs]
    simp only [hpt]
    -- the integrand depends on the noise only; integrate the conditional coin out
    have hinner : Measurable (fun W : EuclideanSpace ℝ (Fin K) =>
        ∫⁻ u, Measure.dirac W (Prod.mk u ⁻¹' s) ∂Bn) := by
      have hjm : Measurable (fun z : EuclideanSpace ℝ (Fin K) × Bool =>
          Set.indicator s (fun _ => (1 : ℝ≥0∞)) (z.2, z.1)) :=
        (measurable_one.indicator hs).comp (measurable_snd.prodMk measurable_fst)
      have : (fun W : EuclideanSpace ℝ (Fin K) =>
          ∫⁻ u, Measure.dirac W (Prod.mk u ⁻¹' s) ∂Bn)
          = fun W => ∫⁻ u, Set.indicator s (fun _ => (1 : ℝ≥0∞)) (u, W) ∂Bn := by
        funext W
        refine lintegral_congr fun u => ?_
        rw [Measure.dirac_apply' _ (measurable_prodMk_left hs)]
        rfl
      rw [this]
      exact hjm.lintegral_prod_right'
    rw [Measure.lintegral_compProd
      (f := fun p : EuclideanSpace ℝ (Fin K) × Bool =>
        ∫⁻ u, Measure.dirac p.1 (Prod.mk u ⁻¹' s) ∂Bn)
      (hinner.comp measurable_fst)]
    have hconst : ∀ W : EuclideanSpace ℝ (Fin K),
        ∫⁻ _u : Bool, (∫⁻ u, Measure.dirac W (Prod.mk u ⁻¹' s) ∂Bn) ∂(κ W)
          = ∫⁻ u, Measure.dirac W (Prod.mk u ⁻¹' s) ∂Bn := by
      intro W
      haveI : IsProbabilityMeasure (κ W) := inferInstance
      rw [lintegral_const, measure_univ, mul_one]
    simp only [hconst]
    -- Tonelli, then the dirac collapses to the sliced Gaussian
    have hswap : ∫⁻ W, ∫⁻ u, Measure.dirac W (Prod.mk u ⁻¹' s) ∂Bn ∂N0
        = ∫⁻ u, ∫⁻ W, Measure.dirac W (Prod.mk u ⁻¹' s) ∂N0 ∂Bn := by
      have hjm : Measurable (Function.uncurry fun (W : EuclideanSpace ℝ (Fin K)) (u : Bool) =>
          Measure.dirac W (Prod.mk u ⁻¹' s)) := by
        have : (Function.uncurry fun (W : EuclideanSpace ℝ (Fin K)) (u : Bool) =>
            Measure.dirac W (Prod.mk u ⁻¹' s))
            = fun z : EuclideanSpace ℝ (Fin K) × Bool =>
                Set.indicator s (fun _ => (1 : ℝ≥0∞)) (z.2, z.1) := by
          funext z
          rw [Function.uncurry]
          rw [Measure.dirac_apply' _ (measurable_prodMk_left hs)]
          rfl
        rw [this]
        exact (measurable_one.indicator hs).comp (measurable_snd.prodMk measurable_fst)
      exact lintegral_lintegral_swap hjm.aemeasurable
    rw [hswap, Measure.prod_apply hs]
    refine lintegral_congr fun u => ?_
    have : ∀ W : EuclideanSpace ℝ (Fin K), Measure.dirac W (Prod.mk u ⁻¹' s)
        = Set.indicator (Prod.mk u ⁻¹' s) (fun _ => (1 : ℝ≥0∞)) W := fun W => by
      rw [Measure.dirac_apply' _ (measurable_prodMk_left hs)]
      rfl
    simp only [this]
    rw [lintegral_indicator (measurable_prodMk_left hs)]
    simp
  · -- the budget: the two sides share the conditional law of the coin
    have hMixac : Mix ≪ N0 := by
      intro A hA
      rw [hMix, Measure.add_apply, Measure.smul_apply, Measure.smul_apply, hA,
        gaussE_ac hσ Δ 0 hA]
      simp
    have hρac : ρ ≪ N0 ⊗ₘ κ := by
      rw [← hdis]
      exact hMixac.compProd (Filter.Eventually.of_forall fun a =>
        Measure.AbsolutelyContinuous.rfl)
    haveI : IsFiniteMeasure (N0 ⊗ₘ κ) := inferInstance
    calc hellingerIntegral α (Bn.prod N0) ν
        = hellingerIntegral α (ρ.map ψ) ((N0 ⊗ₘ κ).map ψ) := by rw [hρψ, hνdef]
      _ ≤ hellingerIntegral α ρ (N0 ⊗ₘ κ) := hellingerIntegral_map_le hα hψ _ _ hρac
      _ = hellingerIntegral α (Mix ⊗ₘ κ) (N0 ⊗ₘ κ) := by rw [hdis]
      _ ≤ hellingerIntegral α Mix N0 * ⨆ a, hellingerIntegral α (κ a) (κ a) :=
          hellingerIntegral_compProd_le hα Mix N0 κ κ hMixac
      _ = hellingerIntegral α Mix N0 := by
          have hone : ∀ a, hellingerIntegral α (κ a) (κ a) = 1 := fun a => hellingerIntegral_self_prob _
          simp only [hone, ciSup_const, mul_one]

/-- **The witness of [Samp-Dec] in the mirrored orientation**: now the *right* coin carries
    the shift, `left noise = right noise + u'·Δ`.  The forward kernel reads the left noise,
    draws the right coin from its posterior given that noise under the joint law
    `mixJoint`, and un-shifts.  The witness is the left coin with the noise drawn from the
    mixture, so the price is the Hellinger integral of the plain Gaussian against the
    mixture — the reversed leaf. -/
theorem sampFwdK_flip_witness {α : ℝ} (hα : 1 < α) (σ2 : ℝ≥0) (q : ℝ≥0)
    (hq : q ≤ 1) (Δ : EuclideanSpace ℝ (Fin K)) :
    ∃ (F : ProbabilityTheory.Kernel (Bool × EuclideanSpace ℝ (Fin K))
        (Bool × EuclideanSpace ℝ (Fin K)))
      (ν : Measure (Bool × EuclideanSpace ℝ (Fin K))), IsMarkovKernel F ∧ IsFiniteMeasure ν ∧
      ν.bind (fun v => F v) = (bernoulliMeasure q).prod (gaussE 0 σ2) ∧
      (∀ v, ∀ᵐ w ∂(F v), v.2 = w.2 + if w.1 then Δ else 0) ∧
      hellingerIntegral α ((bernoulliMeasure q).prod (gaussE 0 σ2)) ν
        ≤ hellingerIntegral α (gaussE 0 σ2)
            ((1 - (q : ℝ≥0∞)) • gaussE 0 σ2 + (q : ℝ≥0∞) • gaussE Δ σ2) := by
  haveI : IsProbabilityMeasure (bernoulliMeasure q) := isProb_bernoulliMeasure q
  haveI : IsProbabilityMeasure (gaussE (0 : EuclideanSpace ℝ (Fin K)) σ2) := by
    unfold gaussE; exact Measure.isProbabilityMeasure_map (by fun_prop)
  have hfst := mixJoint_fst (K := K) hq σ2 Δ
  haveI : IsProbabilityMeasure
      ((1 - (q : ℝ≥0∞)) • gaussE (0 : EuclideanSpace ℝ (Fin K)) σ2
        + (q : ℝ≥0∞) • gaussE Δ σ2) := by
    rw [← hfst]; infer_instance
  have hdis : ((1 - (q : ℝ≥0∞)) • gaussE (0 : EuclideanSpace ℝ (Fin K)) σ2
      + (q : ℝ≥0∞) • gaussE Δ σ2) ⊗ₘ (mixJoint q σ2 Δ).condKernel = mixJoint q σ2 Δ := by
    rw [← hfst]; exact (mixJoint q σ2 Δ).disintegrate _
  have hψ := measurable_unshiftPair (K := K) Δ
  haveI : IsMarkovKernel ((ProbabilityTheory.Kernel.id ×ₖ (mixJoint q σ2 Δ).condKernel).map
      (fun p : EuclideanSpace ℝ (Fin K) × Bool => (p.2, p.1 - shB Δ p.2))) :=
    ProbabilityTheory.Kernel.IsMarkovKernel.map _ hψ
  refine ⟨(ProbabilityTheory.Kernel.id ×ₖ (mixJoint q σ2 Δ).condKernel).map
      (fun p : EuclideanSpace ℝ (Fin K) × Bool => (p.2, p.1 - shB Δ p.2))
      ∘ₖ ProbabilityTheory.Kernel.deterministic Prod.snd measurable_snd,
    (bernoulliMeasure q).prod
      ((1 - (q : ℝ≥0∞)) • gaussE 0 σ2 + (q : ℝ≥0∞) • gaussE Δ σ2),
    inferInstance, inferInstance, ?_, fun w => ?_, ?_⟩
  · -- `ν.bind F` reads the noise of `ν`, a mixture draw, and un-shifts it
    show _ ∘ₘ _ = _
    rw [← Measure.comp_assoc, Measure.deterministic_comp_eq_map, Measure.map_snd_prod,
      measure_univ, one_smul, ← Measure.map_comp _ _ hψ, ← Measure.compProd_eq_comp_prod, hdis]
    exact mixJoint_map_unshift q σ2 Δ
  · -- the kernel un-shifts the left noise by the right coin
    have hS : MeasurableSet {x : Bool × EuclideanSpace ℝ (Fin K) |
        w.2 = x.2 + if x.1 then Δ else 0} :=
      measurableSet_eq_fun measurable_const
        (measurable_snd.add ((measurable_shB Δ).comp measurable_fst))
    rw [ProbabilityTheory.Kernel.comp_deterministic_eq_comap,
      ProbabilityTheory.Kernel.comap_apply, ProbabilityTheory.Kernel.map_apply _ hψ,
      ae_map_iff hψ.aemeasurable hS, ProbabilityTheory.Kernel.prod_apply,
      ProbabilityTheory.Kernel.id_apply, Measure.dirac_prod]
    refine (ae_map_iff measurable_prodMk_left.aemeasurable (hψ hS)).2 (ae_of_all _ fun u => ?_)
    show w.2 = w.2 - shB Δ u + shB Δ u
    rw [sub_add_cancel]
  · -- the budget: the coins agree, so only the noises pay
    rw [← Measure.compProd_const, ← Measure.compProd_const]
    refine (hellingerIntegral_compProd_le hα _ _ _ _ Measure.AbsolutelyContinuous.rfl).trans ?_
    simp only [ProbabilityTheory.Kernel.const_apply, ciSup_const]
    rw [hellingerIntegral_self_prob, one_mul]

end DPFTRL.Band
