import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Xhl.Divergence.SubsamplingFlip
import Xhl.Divergence.SubsamplingMixBudget

/-!
# Domination of the reversed order (Lemma E.1)

`mixFlipBudgetE_le_forward`: for every real `α > 1` and `q ≤ 1`,

  `Λ_α(q, s, v) = H_α(𝒩(0,v) ‖ (1-q)·𝒩(0,v) + q·𝒩(s,v))  ≤  Υ_α(q, s, v)`

(Mironov et al.), so a bound at the symmetric adjacency, `max(Υ_α, Λ_α)`, is `Υ_α`
(`max_mixBudgetR_mixFlipBudgetE`). With `L` the likelihood ratio, both sides are `𝒩(0,v)`-integrals
of a function of `L`; the reflection `z ↦ s - z` inverts `L` (`lintegral_reflect_gaussLR`), which
reduces the claim to the pointwise `A^{1-α} + x·W^{1-α} ≤ A^α + x·W^α` (`mixture_rpow_symm_le`),
proved via the monotonicity of `sinh(βσ)/sinh σ` (`sinh_mul_ratio_mono`).
-/

open MeasureTheory ProbabilityTheory ENNReal Real
open scoped NNReal

namespace Continuous

/-! ## The ratio `sinh(βσ)/sinh σ` is monotone -/

/-- `β cosh(βs) sinh s - sinh(βs) cosh s ≥ 0` for `s ≥ 0`, `β ≥ 1`: it vanishes at `0` and
    its derivative is `(β²-1) sinh(βs) sinh s ≥ 0`. -/
lemma sinh_mul_numerator_nonneg {β : ℝ} (hβ : 1 ≤ β) {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ β * Real.cosh (β * s) * Real.sinh s - Real.sinh (β * s) * Real.cosh s := by
  set N : ℝ → ℝ := fun s => β * Real.cosh (β * s) * Real.sinh s - Real.sinh (β * s) * Real.cosh s
    with hN
  have hderiv : ∀ x, HasDerivAt N ((β ^ 2 - 1) * Real.sinh (β * x) * Real.sinh x) x := by
    intro x
    have h1 : HasDerivAt (fun x => β * x) β x := by
      simpa using (hasDerivAt_id x).const_mul β
    have := ((h1.cosh.const_mul β).mul (Real.hasDerivAt_sinh x)).sub
      (h1.sinh.mul (Real.hasDerivAt_cosh x))
    exact this.congr_deriv (by ring)
  have hmono : MonotoneOn N (Set.Ici 0) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      (fun x _ => (hderiv x).continuousAt.continuousWithinAt)
      (fun x _ => (hderiv x).hasDerivWithinAt) ?_
    intro x hx
    rw [interior_Ici] at hx
    have hx0 : (0:ℝ) < x := hx
    have h1 : 0 ≤ β ^ 2 - 1 := by nlinarith
    have h2 : 0 ≤ Real.sinh (β * x) :=
      Real.sinh_nonneg_iff.2 (mul_nonneg (by linarith) hx0.le)
    have h3 : 0 ≤ Real.sinh x := Real.sinh_nonneg_iff.2 hx0.le
    exact mul_nonneg (mul_nonneg h1 h2) h3
  have h0 : N 0 = 0 := by simp [hN]
  have := hmono (Set.mem_Ici.2 le_rfl) hs hs
  rw [h0] at this
  exact this

/-- **`sinh(βσ)/sinh σ` is nondecreasing on `σ ≥ 0`** for `β ≥ 1`, cross-multiplied so that
    `τ = 0` needs no special statement. -/
lemma sinh_mul_ratio_mono {β : ℝ} (hβ : 1 ≤ β) {τ σ : ℝ} (hτ : 0 ≤ τ) (hτσ : τ ≤ σ) :
    Real.sinh (β * τ) * Real.sinh σ ≤ Real.sinh (β * σ) * Real.sinh τ := by
  rcases hτ.eq_or_lt with rfl | hτ0
  · simp
  set g : ℝ → ℝ := fun s => Real.sinh (β * s) / Real.sinh s with hg
  have hderiv : ∀ x, 0 < x → HasDerivAt g
      ((β * Real.cosh (β * x) * Real.sinh x - Real.sinh (β * x) * Real.cosh x)
        / Real.sinh x ^ 2) x := by
    intro x hx
    have h1 : HasDerivAt (fun x => β * x) β x := by
      simpa using (hasDerivAt_id x).const_mul β
    have := h1.sinh.div (Real.hasDerivAt_sinh x) (Real.sinh_pos_iff.2 hx).ne'
    exact this.congr_deriv (by ring)
  have hmono : MonotoneOn g (Set.Ioi 0) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioi 0)
      (f' := fun x => (β * Real.cosh (β * x) * Real.sinh x - Real.sinh (β * x) * Real.cosh x)
        / Real.sinh x ^ 2)
      (fun x hx => (hderiv x hx).continuousAt.continuousWithinAt) ?_ ?_
    · intro x hx
      rw [interior_Ioi] at hx
      exact (hderiv x hx).hasDerivWithinAt
    · intro x hx
      rw [interior_Ioi] at hx
      exact div_nonneg (sinh_mul_numerator_nonneg hβ (le_of_lt hx)) (sq_nonneg _)
  have hσ0 : 0 < σ := hτ0.trans_le hτσ
  have key := hmono hτ0 hσ0 hτσ
  simp only [hg] at key
  rwa [div_le_div_iff₀ (Real.sinh_pos_iff.2 hτ0) (Real.sinh_pos_iff.2 hσ0)] at key

/-- **The two-point inequality.**  If the weighted `sinh σᵢ` balance, `c₁ sinh σ₁ + c₂ sinh σ₂ = 0`,
    and the positive exponent dominates, `σ₁ + σ₂ ≥ 0`, then for `β ≥ 1` the weighted
    `sinh(βσᵢ)` sum is nonnegative. -/
lemma two_point_sinh_nonneg {β : ℝ} (hβ : 1 ≤ β) {c₁ c₂ σ₁ σ₂ : ℝ} (hc₁ : 0 ≤ c₁)
    (hc₂ : 0 ≤ c₂) (hsum : 0 ≤ σ₁ + σ₂)
    (hbal : c₁ * Real.sinh σ₁ + c₂ * Real.sinh σ₂ = 0) :
    0 ≤ c₁ * Real.sinh (β * σ₁) + c₂ * Real.sinh (β * σ₂) := by
  wlog h : σ₂ ≤ σ₁ generalizing c₁ c₂ σ₁ σ₂
  · have := this hc₂ hc₁ (by linarith) (by linarith) (le_of_not_ge h)
    linarith
  have hσ₁ : 0 ≤ σ₁ := by linarith
  rcases le_or_gt 0 σ₂ with hσ₂ | hσ₂
  · exact add_nonneg
      (mul_nonneg hc₁ (Real.sinh_nonneg_iff.2 (mul_nonneg (by linarith) hσ₁)))
      (mul_nonneg hc₂ (Real.sinh_nonneg_iff.2 (mul_nonneg (by linarith) hσ₂)))
  · have hτ0 : 0 < -σ₂ := by linarith
    have hτσ : -σ₂ ≤ σ₁ := by linarith
    have key := sinh_mul_ratio_mono hβ hτ0.le hτσ
    have e1 : Real.sinh (β * σ₂) = - Real.sinh (β * -σ₂) := by
      rw [show β * -σ₂ = -(β * σ₂) by ring, Real.sinh_neg, neg_neg]
    have e2 : Real.sinh σ₂ = - Real.sinh (-σ₂) := by rw [Real.sinh_neg, neg_neg]
    rw [e2] at hbal
    rw [e1]
    have hsσ₁ : 0 < Real.sinh σ₁ := Real.sinh_pos_iff.2 (by linarith)
    have hmul : c₂ * Real.sinh (β * -σ₂) * Real.sinh σ₁
        ≤ c₁ * Real.sinh (β * σ₁) * Real.sinh σ₁ := by
      calc c₂ * Real.sinh (β * -σ₂) * Real.sinh σ₁
          = c₂ * (Real.sinh (β * -σ₂) * Real.sinh σ₁) := by ring
        _ ≤ c₂ * (Real.sinh (β * σ₁) * Real.sinh (-σ₂)) := mul_le_mul_of_nonneg_left key hc₂
        _ = Real.sinh (β * σ₁) * (c₁ * Real.sinh σ₁) := by
          linear_combination (-Real.sinh (β * σ₁)) * hbal
        _ = c₁ * Real.sinh (β * σ₁) * Real.sinh σ₁ := by ring
    have := le_of_mul_le_mul_right hmul hsσ₁
    linarith

/-! ## The pointwise inequality -/

/-- `r^α - r^{1-α} = 2 e^σ sinh((2α-1)σ)` with `σ = ½ log r`. -/
lemma rpow_sub_rpow_one_sub_eq_sinh {r : ℝ} (hr : 0 < r) (α : ℝ) :
    r ^ α - r ^ (1 - α)
      = 2 * Real.exp (Real.log r / 2) * Real.sinh ((2 * α - 1) * (Real.log r / 2)) := by
  rw [Real.rpow_def_of_pos hr, Real.rpow_def_of_pos hr, Real.sinh_eq]
  have e1 : Real.log r * α = Real.log r / 2 + (2 * α - 1) * (Real.log r / 2) := by ring
  have e2 : Real.log r * (1 - α) = Real.log r / 2 + -((2 * α - 1) * (Real.log r / 2)) := by ring
  rw [e1, e2, Real.exp_add, Real.exp_add]
  ring

/-- `r - 1 = 2 e^σ sinh σ` with `σ = ½ log r`. -/
lemma sub_one_eq_sinh {r : ℝ} (hr : 0 < r) :
    r - 1 = 2 * Real.exp (Real.log r / 2) * Real.sinh (Real.log r / 2) := by
  have h1 : r = Real.exp (Real.log r / 2) * Real.exp (Real.log r / 2) := by
    rw [← Real.exp_add, add_halves, Real.exp_log hr]
  have h2 : Real.exp (Real.log r / 2) * Real.exp (-(Real.log r / 2)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  rw [Real.sinh_eq]
  linear_combination h1 + h2

lemma mixture_base_pos {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) {x : ℝ} (hx : 0 < x) :
    0 < 1 - q + q * x := by
  rcases hq0.eq_or_lt with h | h
  · rw [← h]; norm_num
  · nlinarith [mul_pos h hx]

/-- **The symmetrized pointwise inequality.**  For `x > 0`, `q ∈ [0,1]`, `α ≥ 1`,
    with `A = (1-q)+qx` and `W = (1-q)+q/x`: `A^{1-α} + x·W^{1-α} ≤ A^α + x·W^α`. -/
theorem mixture_rpow_symm_le {α : ℝ} (hα : 1 ≤ α) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    {x : ℝ} (hx : 0 < x) :
    (1 - q + q * x) ^ (1 - α) + x * (1 - q + q * x⁻¹) ^ (1 - α)
      ≤ (1 - q + q * x) ^ α + x * (1 - q + q * x⁻¹) ^ α := by
  have hxi : 0 < x⁻¹ := inv_pos.2 hx
  have hxx : x * x⁻¹ = 1 := mul_inv_cancel₀ hx.ne'
  set A := 1 - q + q * x with hAdef
  set W := 1 - q + q * x⁻¹ with hWdef
  have hA : 0 < A := mixture_base_pos hq0 hq1 hx
  have hW : 0 < W := mixture_base_pos hq0 hq1 hxi
  have hAW : A * W - 1 = q * (1 - q) * (x⁻¹ * (x - 1) ^ 2) := by
    rw [hAdef, hWdef]
    linear_combination (q ^ 2 + q * (1 - q) * (2 - x)) * hxx
  have hAW1 : 1 ≤ A * W := by
    have : 0 ≤ q * (1 - q) * (x⁻¹ * (x - 1) ^ 2) :=
      mul_nonneg (mul_nonneg hq0 (by linarith)) (mul_nonneg hxi.le (sq_nonneg _))
    linarith
  have hsum : 0 ≤ Real.log A / 2 + Real.log W / 2 := by
    have := Real.log_nonneg hAW1
    rw [Real.log_mul hA.ne' hW.ne'] at this
    linarith
  have hbal : (2 * Real.exp (Real.log A / 2)) * Real.sinh (Real.log A / 2)
      + (x * (2 * Real.exp (Real.log W / 2))) * Real.sinh (Real.log W / 2) = 0 := by
    have h1 := sub_one_eq_sinh hA
    have h2 := sub_one_eq_sinh hW
    have h3 : (A - 1) + x * (W - 1) = 0 := by
      rw [hAdef, hWdef]; linear_combination q * hxx
    linear_combination h3 - h1 - x * h2
  have key := two_point_sinh_nonneg (β := 2 * α - 1) (by linarith)
    (by positivity : (0:ℝ) ≤ 2 * Real.exp (Real.log A / 2))
    (mul_nonneg hx.le (by positivity : (0:ℝ) ≤ 2 * Real.exp (Real.log W / 2))) hsum hbal
  have hdiff : (A ^ α - A ^ (1 - α)) + x * (W ^ α - W ^ (1 - α))
      = (2 * Real.exp (Real.log A / 2)) * Real.sinh ((2 * α - 1) * (Real.log A / 2))
        + (x * (2 * Real.exp (Real.log W / 2))) * Real.sinh ((2 * α - 1) * (Real.log W / 2)) := by
    rw [rpow_sub_rpow_one_sub_eq_sinh hA α, rpow_sub_rpow_one_sub_eq_sinh hW α]
    ring
  linarith

/-! ## Reflection of the Gaussian pair -/

/-- The Gaussian likelihood ratio is inverted by the reflection `z ↦ s - z`. -/
lemma gaussLR_reflect (s : ℝ) (v : ℝ≥0) (z : ℝ) :
    gaussLR 0 s v (s - z) = (gaussLR 0 s v z)⁻¹ := by
  simp only [gaussLR]
  rw [← Real.exp_neg]
  congr 1
  ring

/-- **Reflection.**  `z ↦ s - z` carries `𝒩(s,v)` onto `𝒩(0,v)`, so for every measurable
    `g ≥ 0`, `∫ g d𝒩(0,v) = ∫ L(z)·g(s-z) d𝒩(0,v)` with `L` the likelihood ratio. -/
lemma lintegral_reflect_gaussLR {v : ℝ≥0} (hv : v ≠ 0) (s : ℝ) {g : ℝ → ℝ≥0∞}
    (hg : Measurable g) :
    ∫⁻ z, g z ∂(gaussianReal (0:ℝ) v)
      = ∫⁻ z, ENNReal.ofReal (gaussLR 0 s v z) * g (s - z) ∂(gaussianReal (0:ℝ) v) := by
  have hac : gaussianReal s v ≪ gaussianReal (0:ℝ) v :=
    (gaussianReal_absolutelyContinuous _ hv).trans (gaussianReal_absolutelyContinuous' _ hv)
  have hrn : (gaussianReal s v).rnDeriv (gaussianReal (0:ℝ) v)
      =ᵐ[gaussianReal (0:ℝ) v] fun x => ENNReal.ofReal (gaussLR 0 s v x) := by
    have := gaussianReal_rnDeriv_eq_gaussLR (μ₀ := 0) (Δ := s) hv
    rwa [zero_add] at this
  have hgs : Measurable (fun z => g (s - z)) := hg.comp (measurable_const.sub measurable_id)
  calc ∫⁻ z, g z ∂(gaussianReal (0:ℝ) v)
      = ∫⁻ z, g z ∂((gaussianReal s v).map (fun z => s - z)) := by
        rw [gaussianReal_map_const_sub, sub_self]
    _ = ∫⁻ z, g (s - z) ∂(gaussianReal s v) := lintegral_map hg (by fun_prop)
    _ = ∫⁻ z, (gaussianReal s v).rnDeriv (gaussianReal (0:ℝ) v) z * g (s - z)
          ∂(gaussianReal (0:ℝ) v) := (lintegral_rnDeriv_mul hac hgs.aemeasurable).symm
    _ = _ := lintegral_congr_ae (hrn.mono fun x hx => by simp only [hx])

/-! ## The domination -/

lemma mixture_rpow_ofReal {q : ℝ≥0} (hq : (q:ℝ) ≤ 1) {y : ℝ} (hy : 0 < y) (p : ℝ) :
    ((1 - (q:ℝ≥0∞)) + (q:ℝ≥0∞) * ENNReal.ofReal y) ^ p
      = ENNReal.ofReal ((1 - (q:ℝ) + q * y) ^ p) := by
  have hqR : (0:ℝ) ≤ q := q.coe_nonneg
  have e1 : ENNReal.ofReal (1 - (q:ℝ)) = 1 - (q:ℝ≥0∞) := by
    rw [ENNReal.ofReal_sub _ hqR, ENNReal.ofReal_one, ENNReal.ofReal_coe_nnreal]
  have e2 : ENNReal.ofReal ((q:ℝ) * y) = (q:ℝ≥0∞) * ENNReal.ofReal y := by
    rw [ENNReal.ofReal_mul hqR, ENNReal.ofReal_coe_nnreal]
  rw [← e1, ← e2, ← ENNReal.ofReal_add (by linarith) (mul_nonneg hqR hy.le),
    ENNReal.ofReal_rpow_of_pos (mixture_base_pos hqR hq hy)]

/-- **Domination of the reversed order** (Lemma E.1; Mironov et al., Corollary 7): `Λ_α ≤ Υ_α`, at every
    real `α > 1` and `q ≤ 1`. -/
theorem mixFlipBudgetE_le_forward {α : ℝ} (hα : 1 < α) {q : ℝ≥0} (hq : (q:ℝ) ≤ 1) {v : ℝ≥0}
    (hv : v ≠ 0) (s : ℝ) :
    mixFlipBudgetE q s v α ≤ mixBudgetR q s v α := by
  rw [mixBudgetR]
  rcases hq.lt_or_eq with hq1 | hq1
  swap
  · -- `q = 1`: both sides are the Gaussian closed form, with `(0-s)² = (s-0)²`.
    have : q = 1 := NNReal.coe_eq_one.1 hq1
    subst this
    simp only [mixFlipBudgetE, ENNReal.coe_one, tsub_self, zero_smul, zero_add, one_smul]
    rw [hellingerIntegral_gaussianReal hα _ _ hv, hellingerIntegral_gaussianReal hα _ _ hv,
      show ((0:ℝ) - s) ^ 2 = (s - 0) ^ 2 by ring]
  set μ₀ := gaussianReal (0:ℝ) v with hμ₀
  set L : ℝ → ℝ := gaussLR 0 s v with hL
  have hac : gaussianReal s v ≪ μ₀ :=
    (gaussianReal_absolutelyContinuous _ hv).trans (gaussianReal_absolutelyContinuous' _ hv)
  have hrn : (gaussianReal s v).rnDeriv μ₀ =ᵐ[μ₀] fun x => ENNReal.ofReal (L x) := by
    have := gaussianReal_rnDeriv_eq_gaussLR (μ₀ := 0) (Δ := s) hv
    rwa [zero_add] at this
  have hqE : (q:ℝ≥0∞) < 1 := by
    rw [show (1 : ℝ≥0∞) = ((1 : ℝ≥0) : ℝ≥0∞) from rfl, ENNReal.coe_lt_coe]
    exact_mod_cast hq1
  set F : ℝ → ℝ≥0∞ := fun z => ((1 - (q:ℝ≥0∞)) + (q:ℝ≥0∞) * ENNReal.ofReal (L z)) ^ (1 - α)
    with hF
  set G : ℝ → ℝ≥0∞ := fun z => ((1 - (q:ℝ≥0∞)) + (q:ℝ≥0∞) * ENNReal.ofReal (L z)) ^ α
    with hG
  have hLm : Measurable (fun z => ENNReal.ofReal (L z)) := measurable_gaussLR.ennreal_ofReal
  have hFm : Measurable F := (measurable_const.add (measurable_const.mul hLm)).pow_const _
  have hGm : Measurable G := (measurable_const.add (measurable_const.mul hLm)).pow_const _
  have hΛ : mixFlipBudgetE q s v α = ∫⁻ z, F z ∂μ₀ := by
    rw [mixFlipBudgetE, hellingerIntegral_flip_mixture_real_lintegral hα hqE _ _ hac]
    exact lintegral_congr_ae (hrn.mono fun x hx => by rw [hF]; dsimp only; rw [hx])
  have hΥ : hellingerIntegral α ((1 - (q:ℝ≥0∞)) • μ₀ + (q:ℝ≥0∞) • gaussianReal s v) μ₀
      = ∫⁻ z, G z ∂μ₀ := by
    rw [hellingerIntegral_mixture_real_lintegral hα _ ENNReal.coe_ne_top _ _ hac]
    exact lintegral_congr_ae (hrn.mono fun x hx => by rw [hG]; dsimp only; rw [hx])
  have hpt : ∀ z, F z + ENNReal.ofReal (L z) * F (s - z)
      ≤ G z + ENNReal.ofReal (L z) * G (s - z) := by
    intro z
    have hx : 0 < L z := Real.exp_pos _
    have hxi : 0 < (L z)⁻¹ := inv_pos.2 hx
    have hqR : (0:ℝ) ≤ q := q.coe_nonneg
    simp only [hF, hG, hL, gaussLR_reflect]
    rw [mixture_rpow_ofReal hq hx, mixture_rpow_ofReal hq hxi, mixture_rpow_ofReal hq hx,
      mixture_rpow_ofReal hq hxi, ← ENNReal.ofReal_mul hx.le, ← ENNReal.ofReal_mul hx.le,
      ← ENNReal.ofReal_add (Real.rpow_nonneg (mixture_base_pos hqR hq hx).le _)
        (mul_nonneg hx.le (Real.rpow_nonneg (mixture_base_pos hqR hq hxi).le _)),
      ← ENNReal.ofReal_add (Real.rpow_nonneg (mixture_base_pos hqR hq hx).le _)
        (mul_nonneg hx.le (Real.rpow_nonneg (mixture_base_pos hqR hq hxi).le _))]
    exact ENNReal.ofReal_le_ofReal (mixture_rpow_symm_le hα.le hqR hq hx)
  have h2 : ∫⁻ z, F z ∂μ₀ + ∫⁻ z, F z ∂μ₀ ≤ ∫⁻ z, G z ∂μ₀ + ∫⁻ z, G z ∂μ₀ := by
    calc ∫⁻ z, F z ∂μ₀ + ∫⁻ z, F z ∂μ₀
        = ∫⁻ z, F z ∂μ₀ + ∫⁻ z, ENNReal.ofReal (L z) * F (s - z) ∂μ₀ := by
          rw [← lintegral_reflect_gaussLR hv s hFm]
      _ = ∫⁻ z, (F z + ENNReal.ofReal (L z) * F (s - z)) ∂μ₀ := (lintegral_add_left hFm _).symm
      _ ≤ ∫⁻ z, (G z + ENNReal.ofReal (L z) * G (s - z)) ∂μ₀ := lintegral_mono hpt
      _ = ∫⁻ z, G z ∂μ₀ + ∫⁻ z, ENNReal.ofReal (L z) * G (s - z) ∂μ₀ :=
          lintegral_add_left hGm _
      _ = ∫⁻ z, G z ∂μ₀ + ∫⁻ z, G z ∂μ₀ := by
          rw [← lintegral_reflect_gaussLR hv s hGm]
  rw [hΛ, hΥ]
  by_contra hlt
  exact absurd h2 (not_le.2 (ENNReal.add_lt_add (not_le.1 hlt) (not_le.1 hlt)))

/-- The reversed vector subsampled Gaussian, at a displacement of norm at most `s`, is within
    `Λ_α(q, s, v)`, at every `q ≤ 1`. -/
theorem hellingerIntegral_flip_sgMixtureE_le_budget_of_le_one {d : ℕ} {α : ℝ} (hα : 1 < α)
    (u Δ : EuclideanSpace ℝ (Fin d)) (v : ℝ≥0) (hv : v ≠ 0) {q : ℝ≥0} (hq : (q:ℝ) ≤ 1)
    {s : ℝ} (hΔ : ‖Δ‖ ≤ s) :
    hellingerIntegral α (gaussE u v) ((1 - (q:ℝ≥0∞)) • gaussE u v + (q:ℝ≥0∞) • gaussE (u + Δ) v)
      ≤ mixFlipBudgetE q s v α := by
  rcases hq.lt_or_eq with hq1 | hq1
  · exact hellingerIntegral_flip_sgMixtureE_le_budget_of_le hα u Δ v hv hq1 hΔ
  have : q = 1 := NNReal.coe_eq_one.1 hq1
  subst this
  simp only [mixFlipBudgetE, ENNReal.coe_one, tsub_self, zero_smul, zero_add, one_smul]
  rw [hellingerIntegral_gaussianReal hα _ _ hv]
  refine (gaussE_leaf hα hv u (u + Δ)).trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_))
  have hs : 0 ≤ s := (norm_nonneg Δ).trans hΔ
  have hvR : (0:ℝ) < v := by exact_mod_cast pos_iff_ne_zero.2 hv
  have hα' : 0 ≤ α * (α - 1) := by nlinarith
  rw [show u - (u + Δ) = -Δ by abel, norm_neg, zero_sub, neg_sq]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg Δ) hΔ 2) hα'

/-- `max(Υ_α, Λ_α) = Υ_α`, at every `q ≤ 1`. -/
theorem max_mixBudgetR_mixFlipBudgetE {α : ℝ} (hα : 1 < α) {q : ℝ≥0} (hq : (q:ℝ) ≤ 1)
    {v : ℝ≥0} (hv : v ≠ 0) (s : ℝ) :
    max (mixBudgetR q s v α) (mixFlipBudgetE q s v α) = mixBudgetR q s v α :=
  max_eq_left (mixFlipBudgetE_le_forward hα hq hv s)

end Continuous
