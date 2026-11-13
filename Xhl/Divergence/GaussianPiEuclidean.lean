import Mathlib.Probability.Distributions.Gaussian.Real
import Xhl.Divergence.MixtureBind
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Xhl.Divergence.GaussianPi
import Xhl.Divergence.ChainUncond

open MeasureTheory ProbabilityTheory ENNReal Real
open scoped NNReal

/-!
# The isotropic `ℝ^d` Gaussian

`gaussE m σ2 = 𝒩(m, σ²I_d)` on `EuclideanSpace ℝ (Fin d)`: the product of scalar Gaussians
transported along `MeasurableEquiv.toLp` (Definition A.22).

* `gaussE_measurable` — measurable in the mean; `gaussE_noise` — translate of the centred one;
* `gaussE_leaf` — `hellingerIntegral α (gaussE a σ²) (gaussE b σ²) ≤ exp(α(α−1)‖a − b‖²/2σ²)`
  (Proposition A.24, item 1); `gaussE_ac` — mutual absolute continuity;
* `gaussE_conv`, `gaussE_split_shift` — convolution of Gaussians adds variances
  (Proposition A.23, item 2), in product and bind form.
-/

namespace Continuous

variable {d : ℕ} {σ2 : ℝ≥0}

/-- Translation covariance of the product (isotropic) Gaussian on `Fin d → ℝ`. -/
lemma gaussianPi_translation (u : Fin d → ℝ) :
    (Measure.pi (fun _ : Fin d => gaussianReal 0 σ2)).map (fun x => x + u)
      = Measure.pi (fun i => gaussianReal (u i) σ2) := by
  have : ∀ i, SigmaFinite ((gaussianReal (0 : ℝ) σ2).map (fun x => x + u i)) := by
    intro i; rw [gaussianReal_map_add_const, zero_add]; infer_instance
  rw [show (fun x : Fin d → ℝ => x + u) = (fun x i => x i + u i) from rfl,
      Measure.pi_map_pi (fun i => (measurable_add_const (u i)).aemeasurable)]
  refine congrArg Measure.pi (funext fun i => ?_)
  rw [gaussianReal_map_add_const, zero_add]

/-- The mean-parameterized product Gaussian is measurable in its mean vector. -/
lemma measurable_piGauss :
    Measurable (fun v : Fin d → ℝ => Measure.pi (fun i => gaussianReal (v i) σ2)) := by
  set ν0 : Measure (Fin d → ℝ) := Measure.pi (fun _ : Fin d => gaussianReal 0 σ2) with hν0
  have hmk : Measurable (fun p : (Fin d → ℝ) × (Fin d → ℝ) => p.2 + p.1) :=
    measurable_snd.add measurable_fst
  set K : Kernel (Fin d → ℝ) (Fin d → ℝ) :=
    Kernel.map ((Kernel.id : Kernel (Fin d → ℝ) (Fin d → ℝ)) ×ₖ Kernel.const _ ν0)
      (fun p => p.2 + p.1) with hK
  have hKapp : ∀ v, K v = ν0.map (fun x => x + v) := by
    intro v
    rw [hK, Kernel.map_apply _ hmk, Kernel.prod_apply, Kernel.id_apply, Kernel.const_apply,
        Measure.dirac_prod, Measure.map_map hmk measurable_prodMk_left]
    rfl
  have hfun : (fun v : Fin d → ℝ => Measure.pi (fun i => gaussianReal (v i) σ2)) = ⇑K := by
    funext v; rw [hKapp, hν0, gaussianPi_translation]
  rw [hfun]; exact K.measurable

/-- The isotropic (`σ²I`) Gaussian on `EuclideanSpace ℝ (Fin d)` with mean `m`. -/
noncomputable def gaussE (m : EuclideanSpace ℝ (Fin d)) (σ2 : ℝ≥0) :
    Measure (EuclideanSpace ℝ (Fin d)) :=
  (Measure.pi (fun i => gaussianReal (m i) σ2)).map (MeasurableEquiv.toLp 2 (Fin d → ℝ))

lemma gaussE_measurable :
    Measurable (fun m : EuclideanSpace ℝ (Fin d) => gaussE m σ2) :=
  (Measure.measurable_map _ (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurable).comp
    (measurable_piGauss.comp (WithLp.measurable_ofLp 2 (Fin d → ℝ)))

instance gaussE_isProb (m : EuclideanSpace ℝ (Fin d)) : IsProbabilityMeasure (gaussE m σ2) := by
  rw [gaussE]
  exact Measure.isProbabilityMeasure_map (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurable.aemeasurable

lemma gaussE_noise (w : EuclideanSpace ℝ (Fin d)) :
    (gaussE (0 : EuclideanSpace ℝ (Fin d)) σ2).map (fun z => w + z) = gaussE w σ2 := by
  set e := MeasurableEquiv.toLp 2 (Fin d → ℝ) with he
  have h0 : gaussE (0 : EuclideanSpace ℝ (Fin d)) σ2
      = (Measure.pi (fun _ : Fin d => gaussianReal 0 σ2)).map e := by
    rw [gaussE]; rfl
  have hw : gaussE w σ2
      = (Measure.pi (fun _ : Fin d => gaussianReal 0 σ2)).map (fun x => e (x + WithLp.ofLp w)) := by
    rw [gaussE, ← gaussianPi_translation (WithLp.ofLp w),
        Measure.map_map e.measurable (measurable_add_const _)]
    rfl
  have hwmeas : Measurable (fun z : EuclideanSpace ℝ (Fin d) => w + z) :=
    measurable_const.add measurable_id
  rw [h0, hw, Measure.map_map hwmeas e.measurable]
  refine Measure.map_congr (ae_of_all _ (fun x => ?_))
  show w + e x = e (x + WithLp.ofLp w)
  rw [he, MeasurableEquiv.coe_toLp, WithLp.toLp_add, WithLp.toLp_ofLp, add_comm]

lemma gaussE_leaf {α : ℝ} (hα : 1 < α) (hσ : σ2 ≠ 0) (a b : EuclideanSpace ℝ (Fin d)) :
    hellingerIntegral α (gaussE a σ2) (gaussE b σ2)
      ≤ ENNReal.ofReal (Real.exp (α * (α - 1) * ‖a - b‖ ^ 2 / (2 * (σ2 : ℝ)))) := by
  set e := MeasurableEquiv.toLp 2 (Fin d → ℝ) with he
  have hac : Measure.pi (fun i => gaussianReal (a i) σ2) ≪ Measure.pi (fun i => gaussianReal (b i) σ2) :=
    pi_ac_fin _ _ _ (fun i => inferInstance) (fun i => inferInstance)
      (fun i => (gaussianReal_absolutelyContinuous (a i) hσ).trans
        (gaussianReal_absolutelyContinuous' (b i) hσ))
  have hsum : (∑ i, (a i - b i) ^ 2) = ‖a - b‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    exact Finset.sum_congr rfl (fun i _ => by rw [WithLp.ofLp_sub]; rfl)
  refine le_of_eq ?_
  rw [gaussE, gaussE, hellingerIntegral_map_equiv hα e _ _ hac,
      hellingerIntegral_gaussianReal_pi hα (fun i => a i) (fun i => b i) hσ, hsum]

/-! ## Convolution: lifted coordinatewise from `gaussianReal_conv_gaussianReal` -/

lemma gaussianReal_prod_add (a b : ℝ) (v₁ v₂ : ℝ≥0) :
    ((gaussianReal a v₁).prod (gaussianReal b v₂)).map (fun q : ℝ × ℝ => q.1 + q.2)
      = gaussianReal (a + b) (v₁ + v₂) :=
  gaussianReal_conv_gaussianReal

lemma gaussianPi_conv (a b : Fin d → ℝ) (v₁ v₂ : ℝ≥0) :
    ((Measure.pi (fun i => gaussianReal (a i) v₁)).prod
      (Measure.pi (fun i => gaussianReal (b i) v₂))).map
        (fun p : (Fin d → ℝ) × (Fin d → ℝ) => p.1 + p.2)
      = Measure.pi (fun i => gaussianReal (a i + b i) (v₁ + v₂)) := by
  have hadd : Measurable (fun p : (Fin d → ℝ) × (Fin d → ℝ) => p.1 + p.2) :=
    measurable_fst.add measurable_snd
  have hmp := measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin d)
    (fun i => gaussianReal (a i) v₁) (fun i => gaussianReal (b i) v₂)
  rw [← hmp.map_eq, Measure.map_map hadd
    (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin d)).measurable,
    show (fun p : (Fin d → ℝ) × (Fin d → ℝ) => p.1 + p.2)
        ∘ (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin d))
      = (fun (w : Fin d → ℝ × ℝ) (i : Fin d) => (w i).1 + (w i).2) from rfl,
    Measure.pi_map_pi (f := fun (_ : Fin d) (p : ℝ × ℝ) => p.1 + p.2)
      (fun _ => (measurable_fst.add measurable_snd).aemeasurable)]
  exact congrArg Measure.pi (funext fun i => gaussianReal_prod_add _ _ _ _)

/-- **The isotropic Gaussian on `EuclideanSpace` is closed under convolution.** -/
lemma gaussE_conv (a b : EuclideanSpace ℝ (Fin d)) (v₁ v₂ : ℝ≥0) :
    ((gaussE a v₁).prod (gaussE b v₂)).map
        (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => p.1 + p.2)
      = gaussE (a + b) (v₁ + v₂) := by
  set e := MeasurableEquiv.toLp 2 (Fin d → ℝ) with he
  have hadd : Measurable
      (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => p.1 + p.2) :=
    measurable_fst.add measurable_snd
  have haddp : Measurable (fun p : (Fin d → ℝ) × (Fin d → ℝ) => p.1 + p.2) :=
    measurable_fst.add measurable_snd
  have hmap : Measurable (Prod.map (e : (Fin d → ℝ) → EuclideanSpace ℝ (Fin d)) e) :=
    e.measurable.prodMap e.measurable
  rw [gaussE, gaussE, Measure.map_prod_map _ _ e.measurable e.measurable,
    Measure.map_map hadd hmap,
    show (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => p.1 + p.2)
        ∘ (Prod.map (e : (Fin d → ℝ) → EuclideanSpace ℝ (Fin d)) e)
      = (e : (Fin d → ℝ) → EuclideanSpace ℝ (Fin d))
        ∘ (fun p : (Fin d → ℝ) × (Fin d → ℝ) => p.1 + p.2) from
      funext fun p => by
        show WithLp.toLp 2 p.1 + WithLp.toLp 2 p.2 = WithLp.toLp 2 (p.1 + p.2)
        rw [WithLp.toLp_add],
    ← Measure.map_map e.measurable haddp, gaussianPi_conv, gaussE]
  rfl

/-- Isotropic Gaussians on `ℝ^d` are mutually absolutely continuous (transport of `pi_ac_fin`). -/
lemma gaussE_ac {d : ℕ} {σ2 : ℝ≥0} (hσ : σ2 ≠ 0) (a b : EuclideanSpace ℝ (Fin d)) :
    gaussE a σ2 ≪ gaussE b σ2 := by
  rw [gaussE, gaussE]
  exact (pi_ac_fin _ _ _ (fun i => inferInstance) (fun i => inferInstance)
    (fun i => (gaussianReal_absolutelyContinuous (a i) hσ).trans
      (gaussianReal_absolutelyContinuous' (b i) hσ))).map (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurable

/-- **The variance split** (Proposition A.23, item 2): a `𝒩(c, σ₂²)`
    draw followed by a `𝒩(· + p, σ₁²)` draw is a `𝒩(c + p, σ₂² + σ₁²)` draw. -/
lemma gaussE_split_shift {d : ℕ} (c p : EuclideanSpace ℝ (Fin d)) (σ1 σ2 : ℝ≥0) :
    (gaussE c σ2).bind (fun z => gaussE (z + p) σ1) = gaussE (c + p) (σ2 + σ1) := by
  have h := gaussE_conv c p σ2 σ1
  rw [← h, prod_map_eq_bind _ _
    (g := fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => p.1 + p.2)
    (measurable_fst.add measurable_snd)]
  refine Measure.bind_congr_right (Filter.Eventually.of_forall (fun z => ?_))
  show gaussE (z + p) σ1 = (gaussE p σ1).map (fun ξ => z + ξ)
  rw [← gaussE_noise (σ2 := σ1) p,
    Measure.map_map (measurable_const_add z) (measurable_const_add p),
    ← gaussE_noise (σ2 := σ1) (z + p)]
  exact congrArg (fun f => Measure.map f (gaussE (0 : EuclideanSpace ℝ (Fin d)) σ1))
    (funext fun ξ => by show z + p + ξ = z + (p + ξ); abel)

end Continuous
