import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Xhl.Divergence.SubsamplingRealOrder
import Xhl.Divergence.GaussianPiEuclidean

/-!
# The subsampled Gaussian on `EuclideanSpace ℝ (Fin d)`

`hellingerIntegral_sgMixtureE_eq_scalar`: the vector subsampled-Gaussian mixture at `gaussE`
has the Hellinger integral of the scalar one at sensitivity `‖Δ‖`. In an orthonormal basis with
`b 0 = Δ/‖Δ‖` (`gaussE_eq_pi_map_basis`), both measures factor as a scalar part on coordinate `0`
times a common product on the others, which `hellingerIntegral_prod` cancels.
-/

open MeasureTheory ProbabilityTheory ENNReal Real
open scoped NNReal

namespace Continuous

variable {d : ℕ}

/-- `gaussE 0 v` is the pushforward of Mathlib's standard Gaussian by scaling by `√v`. -/
theorem gaussE_eq_map_stdGaussian (v : ℝ≥0) :
    gaussE (0 : EuclideanSpace ℝ (Fin d)) v
      = (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin d))).map
          (fun x => (Real.sqrt v) • x) := by
  set c := Real.sqrt v with hc
  have hgr : gaussianReal (0:ℝ) v = (gaussianReal 0 1).map (c * ·) := by
    rw [gaussianReal_map_const_mul]
    congr 1
    · ring
    · exact NNReal.coe_injective (by
        push_cast; rw [hc, Real.sq_sqrt (NNReal.coe_nonneg v), mul_one])
  have hpi : Measure.pi (fun _ : Fin d => gaussianReal (0:ℝ) v)
      = (Measure.pi (fun _ : Fin d => gaussianReal (0:ℝ) 1)).map (fun x i => c * x i) := by
    simp_rw [hgr]
    rw [Measure.pi_map_pi (fun i => (measurable_const_mul c).aemeasurable)]
  have hpi2 : (fun (x : Fin d → ℝ) (i : Fin d) => c * x i) = (fun x : Fin d → ℝ => c • x) := by
    funext x i; simp [Pi.smul_apply]
  rw [hpi2] at hpi
  have hzero : ∀ i : Fin d, (0 : EuclideanSpace ℝ (Fin d)) i = 0 := fun i => rfl
  unfold gaussE
  simp only [hzero]
  rw [hpi, Measure.map_map (by fun_prop) (by fun_prop),
    show (MeasurableEquiv.toLp 2 (Fin d → ℝ)) ∘ (fun x : Fin d → ℝ => c • x)
        = (fun x : EuclideanSpace ℝ (Fin d) => c • x) ∘ (MeasurableEquiv.toLp 2 (Fin d → ℝ))
      from by
        funext x
        show (MeasurableEquiv.toLp 2 (Fin d → ℝ)) (c • x)
            = c • (MeasurableEquiv.toLp 2 (Fin d → ℝ)) x
        rw [MeasurableEquiv.coe_toLp, WithLp.toLp_smul],
    ← Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  exact map_pi_eq_stdGaussian

open scoped RealInnerProductSpace in
/-- **`gaussE` in an orthonormal basis**: the pushforward, along `x ↦ ∑ i, x i • b i`, of the
    product of scalar Gaussians at the `b`-coordinates of the mean. -/
theorem gaussE_eq_pi_map_basis (v : ℝ≥0) (m : EuclideanSpace ℝ (Fin d))
    (b : OrthonormalBasis (Fin d) ℝ (EuclideanSpace ℝ (Fin d))) :
    gaussE m v
      = (Measure.pi (fun i : Fin d => gaussianReal ⟪b i, m⟫ v)).map (fun x => ∑ i, x i • b i) := by
  set ψ : (Fin d → ℝ) → EuclideanSpace ℝ (Fin d) := fun x => ∑ i, x i • b i with hψ
  have hψmeas : Measurable ψ := by fun_prop
  set c := Real.sqrt v with hc
  have hgr : gaussianReal (0:ℝ) v = (gaussianReal 0 1).map (c * ·) := by
    rw [gaussianReal_map_const_mul]
    congr 1
    · ring
    · exact NNReal.coe_injective (by
        push_cast; rw [hc, Real.sq_sqrt (NNReal.coe_nonneg v), mul_one])
  have hscale : Measure.pi (fun _ : Fin d => gaussianReal (0:ℝ) v)
      = (Measure.pi (fun _ : Fin d => gaussianReal (0:ℝ) 1)).map (fun x i => c * x i) := by
    simp_rw [hgr]
    rw [Measure.pi_map_pi (fun i => (measurable_const_mul c).aemeasurable)]
  have hscale2 : (fun (x : Fin d → ℝ) (i : Fin d) => c * x i) = (fun x : Fin d → ℝ => c • x) := by
    funext x i; simp [Pi.smul_apply]
  rw [hscale2] at hscale
  have hg0 : gaussE (0 : EuclideanSpace ℝ (Fin d)) v
      = (Measure.pi (fun _ : Fin d => gaussianReal 0 v)).map ψ := by
    rw [gaussE_eq_map_stdGaussian, stdGaussian_eq_map_pi_orthonormalBasis b,
      Measure.map_map (by fun_prop) (by fun_prop)]
    have heq : (fun x : EuclideanSpace ℝ (Fin d) => c • x) ∘ ψ
        = ψ ∘ (fun x : Fin d → ℝ => c • x) := by
      funext x
      show c • (∑ i, x i • b i) = ∑ i, (c • x) i • b i
      rw [Finset.smul_sum]
      congr 1; funext i; rw [smul_smul]; rfl
    rw [heq, ← Measure.map_map hψmeas (by fun_prop), hscale]
  have hmrepr : m = ψ (fun i => ⟪b i, m⟫) := (b.sum_repr' m).symm
  have step1 : gaussE m v = (gaussE 0 v).map (ψ (fun i => ⟪b i, m⟫) + ·) := by
    conv_lhs => rw [hmrepr]
    exact (gaussE_noise _).symm
  have step2 : (gaussE (0 : EuclideanSpace ℝ (Fin d)) v).map (ψ (fun i => ⟪b i, m⟫) + ·)
      = (Measure.pi (fun i : Fin d => gaussianReal ⟪b i, m⟫ v)).map ψ := by
    rw [hg0, Measure.map_map (by fun_prop) hψmeas]
    have heq2 : (fun z => ψ (fun i => ⟪b i, m⟫) + z) ∘ ψ
        = ψ ∘ (fun x => (fun i => ⟪b i, m⟫) + x) := by
      funext x
      show ψ (fun i => ⟪b i, m⟫) + ψ x = ψ ((fun i => ⟪b i, m⟫) + x)
      rw [hψ]
      simp only [Pi.add_apply]
      rw [← Finset.sum_add_distrib]
      congr 1; funext i; rw [add_smul]
    rw [heq2, ← Measure.map_map hψmeas (by fun_prop)]
    congr 1
    have hshift : (fun x : Fin d → ℝ => (fun i => ⟪b i, m⟫) + x)
        = (fun x i => (⟪b i, m⟫ : ℝ) + x i) := by
      funext x i; simp [Pi.add_apply]
    rw [hshift, Measure.pi_map_pi (fun i => (measurable_const_add (⟪b i, m⟫ : ℝ)).aemeasurable)]
    refine congrArg Measure.pi (funext fun i => ?_)
    rw [gaussianReal_map_const_add, zero_add]
  rw [step1, step2]

/-- **Translation invariance** of the scalar subsampled-mixture Hellinger integral in the base
    point `μ₀`. -/
theorem hellingerIntegral_sgMixture_real_translation_invariant {α : ℝ} (hα : 1 < α) {μ₀ μ₀' Δ : ℝ}
    {v : ℝ≥0} (hv : v ≠ 0) (q : ℝ≥0) :
    hellingerIntegral α ((1 - (q:ℝ≥0∞)) • gaussianReal μ₀ v + (q:ℝ≥0∞) • gaussianReal (μ₀ + Δ) v)
        (gaussianReal μ₀ v)
      = hellingerIntegral α ((1 - (q:ℝ≥0∞)) • gaussianReal μ₀' v + (q:ℝ≥0∞) • gaussianReal (μ₀' + Δ) v)
        (gaussianReal μ₀' v) := by
  set e : ℝ ≃ᵐ ℝ := (Homeomorph.addRight (μ₀' - μ₀)).toMeasurableEquiv with he
  have hac0 : gaussianReal (μ₀ + Δ) v ≪ gaussianReal μ₀ v :=
    (gaussianReal_absolutelyContinuous _ hv).trans (gaussianReal_absolutelyContinuous' _ hv)
  have hac1 : (1 - (q:ℝ≥0∞)) • gaussianReal μ₀ v ≪ gaussianReal μ₀ v := by
    intro s hs; simp [Measure.smul_apply, hs]
  have hac2 : (q:ℝ≥0∞) • gaussianReal (μ₀ + Δ) v ≪ gaussianReal μ₀ v := by
    intro s hs; simp [Measure.smul_apply, hac0 hs]
  have hac : (1 - (q:ℝ≥0∞)) • gaussianReal μ₀ v + (q:ℝ≥0∞) • gaussianReal (μ₀ + Δ) v
      ≪ gaussianReal μ₀ v := hac1.add_left hac2
  haveI : IsFiniteMeasure
      ((1 - (q:ℝ≥0∞)) • gaussianReal μ₀ v + (q:ℝ≥0∞) • gaussianReal (μ₀ + Δ) v) := by
    constructor
    simp only [Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      measure_univ, mul_one]
    exact ENNReal.add_lt_top.2 ⟨lt_of_le_of_lt tsub_le_self one_lt_top, ENNReal.coe_lt_top⟩
  rw [← hellingerIntegral_map_equiv hα e _ _ hac]
  have h1 : (gaussianReal μ₀ v).map e = gaussianReal μ₀' v := by
    show (gaussianReal μ₀ v).map (· + (μ₀' - μ₀)) = gaussianReal μ₀' v
    rw [gaussianReal_map_add_const]; ring_nf
  have h2 : (gaussianReal (μ₀ + Δ) v).map e = gaussianReal (μ₀' + Δ) v := by
    show (gaussianReal (μ₀ + Δ) v).map (· + (μ₀' - μ₀)) = gaussianReal (μ₀' + Δ) v
    rw [gaussianReal_map_add_const]; ring_nf
  rw [Measure.map_add _ _ e.measurable, Measure.map_smul, Measure.map_smul, h1, h2]

open scoped RealInnerProductSpace in
set_option maxHeartbeats 4000000 in
/-- **Dimension reduction**: the vector subsampled-mixture Hellinger integral equals the scalar
    one at sensitivity `‖Δ‖`. -/
theorem hellingerIntegral_sgMixtureE_eq_scalar {α : ℝ} (hα : 1 < α) (u Δ : EuclideanSpace ℝ (Fin d))
    (hΔ : Δ ≠ 0) (v : ℝ≥0) (hv : v ≠ 0) (q : ℝ≥0) :
    hellingerIntegral α ((1 - (q:ℝ≥0∞)) • gaussE u v + (q:ℝ≥0∞) • gaussE (u + Δ) v) (gaussE u v)
      = hellingerIntegral α ((1 - (q:ℝ≥0∞)) • gaussianReal (0:ℝ) v + (q:ℝ≥0∞) • gaussianReal (‖Δ‖:ℝ) v)
          (gaussianReal (0:ℝ) v) := by
  have hd0 : d ≠ 0 := by
    intro hd0
    apply hΔ
    subst hd0
    exact Subsingleton.elim Δ 0
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd0
  have hΔnorm : ‖Δ‖ ≠ 0 := norm_ne_zero_iff.mpr hΔ
  have hw : ‖(‖Δ‖⁻¹ : ℝ) • Δ‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg Δ),
      inv_mul_cancel₀ hΔnorm]
  obtain ⟨b, hb0⟩ :
      ∃ b : OrthonormalBasis (Fin (n+1)) ℝ (EuclideanSpace ℝ (Fin (n+1))),
        b 0 = (‖Δ‖⁻¹ : ℝ) • Δ := by
    have hcard : Module.finrank ℝ (EuclideanSpace ℝ (Fin (n+1))) = Fintype.card (Fin (n+1)) := by
      rw [finrank_euclideanSpace_fin, Fintype.card_fin]
    have hv' : Orthonormal ℝ
        (({(0:Fin (n+1))} : Set (Fin (n+1))).domRestrict (fun _ => (‖Δ‖⁻¹ : ℝ) • Δ)) := by
      rw [orthonormal_iff_ite]
      intro i j
      have hi : i.1 = 0 := i.2
      have hj : j.1 = 0 := j.2
      have hij : i = j := Subtype.ext (hi.trans hj.symm)
      subst hij
      simp [hw, Set.domRestrict_apply]
    obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq hcard hv'
    exact ⟨b, hb 0 (by simp)⟩
  have hΔeq : Δ = ‖Δ‖ • b 0 := by
    rw [hb0, smul_smul, mul_inv_cancel₀ hΔnorm, one_smul]
  have hinner0 : ⟪b 0, Δ⟫ = ‖Δ‖ := by
    rw [hb0, real_inner_smul_left, real_inner_self_eq_norm_sq]; field_simp
  have hinnerne : ∀ i : Fin (n+1), i ≠ 0 → ⟪b i, Δ⟫ = 0 := by
    intro i hi
    rw [hΔeq, inner_smul_right, real_inner_comm]
    rw [b.orthonormal.2 (Ne.symm hi)]; ring
  set coeffs : Fin (n+1) → ℝ := fun i => ⟪b i, u⟫ with hcoeffs
  have hcoeffsΔ : ∀ i : Fin (n+1), ⟪b i, u + Δ⟫ = Function.update coeffs 0 (coeffs 0 + ‖Δ‖) i := by
    intro i
    rw [inner_add_right]
    rcases eq_or_ne i 0 with rfl | hi
    · rw [Function.update_self, hinner0]
    · rw [Function.update_of_ne hi, hinnerne i hi, add_zero]
  -- `ψ` as a measurable equivalence
  set T : EuclideanSpace ℝ (Fin (n+1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n+1)) :=
    (EuclideanSpace.basisFun (Fin (n+1)) ℝ).equiv b (Equiv.refl (Fin (n+1))) with hT
  set ψe : (Fin (n+1) → ℝ) ≃ᵐ EuclideanSpace ℝ (Fin (n+1)) :=
    (MeasurableEquiv.toLp 2 (Fin (n+1) → ℝ)).trans T.toHomeomorph.toMeasurableEquiv with hψe
  have hψecoe : (ψe : (Fin (n+1) → ℝ) → EuclideanSpace ℝ (Fin (n+1)))
      = fun x => ∑ i, x i • b i := by
    funext x
    show T (MeasurableEquiv.toLp 2 (Fin (n+1) → ℝ) x) = ∑ i, x i • b i
    rw [MeasurableEquiv.coe_toLp, hT, OrthonormalBasis.equiv_apply]
    simp [EuclideanSpace.basisFun_repr]
  -- `gaussE` at `u` and `u+Δ` via the basis
  have hgu : gaussE u v = (Measure.pi (fun i => gaussianReal (coeffs i) v)).map ψe := by
    rw [gaussE_eq_pi_map_basis v u b, ← hψecoe]
  have hguΔ : gaussE (u + Δ) v
      = (Measure.pi (fun i => gaussianReal (Function.update coeffs 0 (coeffs 0 + ‖Δ‖) i) v)).map
          ψe := by
    rw [gaussE_eq_pi_map_basis v (u + Δ) b, ← hψecoe]
    congr 1
    exact congrArg Measure.pi (funext fun i => by rw [hcoeffsΔ])
  set coeffsΔ : Fin (n+1) → ℝ := Function.update coeffs 0 (coeffs 0 + ‖Δ‖) with hcoeffsΔdef
  -- absolute continuity, pointwise then tensorized
  have hacpt : ∀ i : Fin (n+1), gaussianReal (coeffsΔ i) v ≪ gaussianReal (coeffs i) v := by
    intro i
    rcases eq_or_ne i 0 with rfl | hi
    · exact (gaussianReal_absolutelyContinuous _ hv).trans (gaussianReal_absolutelyContinuous' _ hv)
    · rw [hcoeffsΔdef, Function.update_of_ne hi]
  have hacPi : Measure.pi (fun i => gaussianReal (coeffsΔ i) v)
      ≪ Measure.pi (fun i => gaussianReal (coeffs i) v) :=
    pi_ac_fin _ _ _ (fun i => inferInstance) (fun i => inferInstance) hacpt
  have hac1 : (1 - (q:ℝ≥0∞)) • Measure.pi (fun i => gaussianReal (coeffs i) v)
      ≪ Measure.pi (fun i => gaussianReal (coeffs i) v) := by
    intro s hs; simp [Measure.smul_apply, hs]
  have hac2 : (q:ℝ≥0∞) • Measure.pi (fun i => gaussianReal (coeffsΔ i) v)
      ≪ Measure.pi (fun i => gaussianReal (coeffs i) v) := by
    intro s hs; simp [Measure.smul_apply, hacPi hs]
  have hac : (1 - (q:ℝ≥0∞)) • Measure.pi (fun i => gaussianReal (coeffs i) v)
      + (q:ℝ≥0∞) • Measure.pi (fun i => gaussianReal (coeffsΔ i) v)
      ≪ Measure.pi (fun i => gaussianReal (coeffs i) v) := hac1.add_left hac2
  haveI : IsFiniteMeasure ((1 - (q:ℝ≥0∞)) • Measure.pi (fun i => gaussianReal (coeffs i) v)
      + (q:ℝ≥0∞) • Measure.pi (fun i => gaussianReal (coeffsΔ i) v)) := by
    constructor
    simp only [Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      measure_univ, mul_one]
    exact ENNReal.add_lt_top.2 ⟨lt_of_le_of_lt tsub_le_self one_lt_top, ENNReal.coe_lt_top⟩
  rw [hgu, hguΔ, ← Measure.map_smul, ← Measure.map_smul, ← Measure.map_add _ _ ψe.measurable,
    hellingerIntegral_map_equiv hα ψe _ _ hac]
  -- peel off coordinate 0
  set e0 : (Fin (n+1) → ℝ) ≃ᵐ (ℝ × (Fin n → ℝ)) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0 with he0
  have hmpU := measurePreserving_piFinSuccAbove (fun i : Fin (n+1) => gaussianReal (coeffs i) v) 0
  have hmpUΔ := measurePreserving_piFinSuccAbove (fun i : Fin (n+1) => gaussianReal (coeffsΔ i) v) 0
  have htail : (fun j : Fin n => gaussianReal (coeffsΔ ((0 : Fin (n+1)).succAbove j)) v)
      = (fun j : Fin n => gaussianReal (coeffs ((0 : Fin (n+1)).succAbove j)) v) := by
    funext j
    rw [hcoeffsΔdef, Function.update_of_ne (Fin.succAbove_ne 0 j)]
  rw [← hellingerIntegral_map_equiv hα e0 _ _ hac, Measure.map_add _ _ e0.measurable,
    Measure.map_smul, Measure.map_smul, hmpU.map_eq, hmpUΔ.map_eq, htail,
    ← Measure.prod_smul_left, ← Measure.prod_smul_left, ← Measure.add_prod]
  have hcoeffsΔ0 : coeffsΔ 0 = coeffs 0 + ‖Δ‖ := Function.update_self ..
  have hac1' : (1 - (q:ℝ≥0∞)) • gaussianReal (coeffs 0) v ≪ gaussianReal (coeffs 0) v := by
    intro s hs; simp [Measure.smul_apply, hs]
  have hac2' : (q:ℝ≥0∞) • gaussianReal (coeffsΔ 0) v ≪ gaussianReal (coeffs 0) v := by
    intro s hs; simp [Measure.smul_apply, hacpt 0 hs]
  haveI : IsFiniteMeasure ((1 - (q:ℝ≥0∞)) • gaussianReal (coeffs 0) v
      + (q:ℝ≥0∞) • gaussianReal (coeffsΔ 0) v) := by
    constructor
    simp only [Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      measure_univ, mul_one]
    exact ENNReal.add_lt_top.2 ⟨lt_of_le_of_lt tsub_le_self one_lt_top, ENNReal.coe_lt_top⟩
  rw [hellingerIntegral_prod hα _ _ _ _ (hac1'.add_left hac2') Measure.AbsolutelyContinuous.rfl,
    hellingerIntegral_self_prob, mul_one, hcoeffsΔ0]
  simpa using
    hellingerIntegral_sgMixture_real_translation_invariant (μ₀ := coeffs 0) (μ₀' := 0) (Δ := ‖Δ‖) hα hv q

end Continuous
