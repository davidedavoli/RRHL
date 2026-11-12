import Xhl.Examples.DPSGD.Shared.Paper
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Algebra.Order.Chebyshev

/-!
# Altschuler–Talwar's hypotheses on the loss

Altschuler and Talwar assume the per-record losses convex, `β`-smooth and `C`-Lipschitz.
Under these hypotheses the update of the last-iterate program is non-expansive on every
batch, provided the step is small enough (`hstep_of_ATLoss`), which is the hypothesis
`hstep` of the last-iterate theorems.

* A `C`-Lipschitz loss has gradients of norm at most `C`, so clipping at `C` is the
  identity (`clipV_grad_of_ATLoss`).
* A convex function with `β`-Lipschitz gradient is *cocoercive*,
  `‖∇f x − ∇f y‖² ≤ β ⟪∇f x − ∇f y, x − y⟫` (`cocoercive`), by the descent lemma and the
  first-order condition of convexity.
* A sum of `|B|` such gradients is cocoercive with constant `|B| β`, so the step
  `u ↦ u − γ ∑ᵢ ∇ℓᵢ u` is non-expansive when `γ |B| β ≤ 2`.  The batch may hold every record,
  so with `γ = η / (q (N + 1))` the step condition is `η β ≤ 2 q`.
-/

open MeasureTheory
open scoped NNReal RealInnerProductSpace

namespace SmoothConvex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {f : E → ℝ} {g : E → E}

lemma hasDerivAt_comp_lineMap (hf : ∀ z, HasGradientAt f (g z) z) (x y : E) (t : ℝ) :
    HasDerivAt (fun t : ℝ => f (AffineMap.lineMap x y t))
      ⟪g (AffineMap.lineMap x y t), y - x⟫ t :=
  (hasGradientAt_iff_hasFDerivAt.mp (hf _)).comp_hasDerivAt t AffineMap.hasDerivAt_lineMap

/-- First-order condition of convexity. -/
lemma convex_first_order (hf : ∀ z, HasGradientAt f (g z) z) (hc : ConvexOn ℝ Set.univ f)
    (x y : E) : f x + ⟪g x, y - x⟫ ≤ f y := by
  have hc' : ConvexOn ℝ Set.univ (fun t : ℝ => f (AffineMap.lineMap x y t)) :=
    hc.comp_affineMap (AffineMap.lineMap x y)
  have h := hc'.le_slope_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1) zero_lt_one
    (hasDerivAt_comp_lineMap hf x y 0)
  simp only [slope_def_field, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one,
    sub_zero, div_one] at h
  linarith

/-- The gradient of a convex function is monotone. -/
lemma inner_grad_sub_nonneg (hf : ∀ z, HasGradientAt f (g z) z) (hc : ConvexOn ℝ Set.univ f)
    (x y : E) : 0 ≤ ⟪g x - g y, x - y⟫ := by
  have h1 := convex_first_order hf hc x y
  have h2 := convex_first_order hf hc y x
  have e : ⟪g x - g y, x - y⟫ = -⟪g x, y - x⟫ - ⟪g y, x - y⟫ := by
    rw [inner_sub_left, ← neg_sub x y, inner_neg_right]; ring
  linarith

/-- The descent lemma: a function with `β`-Lipschitz gradient lies below its tangent
    paraboloid. -/
lemma descent (hf : ∀ z, HasGradientAt f (g z) z) {β : ℝ≥0} (hg : LipschitzWith β g)
    (x y : E) : f y ≤ f x + ⟪g x, y - x⟫ + β / 2 * ‖y - x‖ ^ 2 := by
  set v := y - x
  let φ : ℝ → ℝ := fun t => f (AffineMap.lineMap x y t) - t * ⟪g x, v⟫ - β / 2 * t ^ 2 * ‖v‖ ^ 2
  have hφ : ∀ t, HasDerivAt φ (⟪g (AffineMap.lineMap x y t), v⟫ - ⟪g x, v⟫
      - β / 2 * (2 * t) * ‖v‖ ^ 2) t := fun t => by
    have h2 : HasDerivAt (fun t : ℝ => t ^ 2) (2 * t) t := by
      simpa using hasDerivAt_pow 2 t
    exact (((hasDerivAt_comp_lineMap hf x y t).sub
      ((hasDerivAt_id t).mul_const ⟪g x, v⟫ |>.congr_deriv (one_mul _))).sub
      ((h2.const_mul (β / 2 : ℝ)).mul_const (‖v‖ ^ 2)))
  have hanti : AntitoneOn φ (Set.Ici 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici 0)
      (fun t _ => (hφ t).continuousAt.continuousWithinAt)
      (fun t _ => (hφ t).differentiableAt.differentiableWithinAt) fun t ht => ?_
    rw [interior_Ici] at ht
    have ht0 : 0 ≤ t := le_of_lt ht
    rw [(hφ t).deriv]
    have hl : AffineMap.lineMap x y t - x = t • v := by
      rw [AffineMap.lineMap_apply_module']; abel
    have hcs : ⟪g (AffineMap.lineMap x y t) - g x, v⟫ ≤ β * t * ‖v‖ ^ 2 := by
      calc ⟪g (AffineMap.lineMap x y t) - g x, v⟫
          ≤ ‖g (AffineMap.lineMap x y t) - g x‖ * ‖v‖ := real_inner_le_norm _ _
        _ ≤ (β * ‖AffineMap.lineMap x y t - x‖) * ‖v‖ := by
            gcongr; exact hg.norm_sub_le _ _
        _ = β * t * ‖v‖ ^ 2 := by
            rw [hl, norm_smul, Real.norm_of_nonneg ht0]; ring
    rw [inner_sub_left] at hcs
    nlinarith
  have h := hanti (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 zero_le_one) zero_le_one
  simp only [φ, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one] at h
  linarith

/-- **Cocoercivity** (Baillon–Haddad, the convex smooth case):
    `‖∇f x − ∇f y‖² ≤ β ⟪∇f x − ∇f y, x − y⟫`. -/
lemma cocoercive (hf : ∀ z, HasGradientAt f (g z) z) (hc : ConvexOn ℝ Set.univ f)
    {β : ℝ≥0} (hg : LipschitzWith β g) (x y : E) :
    ‖g x - g y‖ ^ 2 ≤ β * ⟪g x - g y, x - y⟫ := by
  rcases eq_or_ne β 0 with hβ | hβ
  · have : g x - g y = 0 := by
      have := hg.norm_sub_le x y; rw [hβ] at this; simp at this; simp [this]
    simp [this]
  -- `f y ≥ f x + ⟪∇f x, y − x⟫ + ‖∇f y − ∇f x‖² / (2β)`, by the descent lemma at the
  -- minimiser `x` of `z ↦ f z − ⟪∇f x, z⟫`
  have key : ∀ x y : E, f x + ⟪g x, y - x⟫ + ‖g y - g x‖ ^ 2 / (2 * β) ≤ f y := by
    intro x y
    have hβ0 : (0 : ℝ) < β := lt_of_le_of_ne (NNReal.coe_nonneg β) (by exact_mod_cast hβ.symm)
    set w := y - (1 / (β : ℝ)) • (g y - g x)
    have h1 := convex_first_order hf hc x w
    have h2 := descent hf hg y w
    have hw : w - y = -((1 / (β : ℝ)) • (g y - g x)) := by simp [w]
    rw [hw, inner_neg_right, norm_neg, inner_smul_right, norm_smul, Real.norm_of_nonneg
      (by positivity)] at h2
    have hwx : w - x = (y - x) - (1 / (β : ℝ)) • (g y - g x) := by simp [w]; abel
    rw [hwx, inner_sub_right, inner_smul_right] at h1
    have e : ⟪g y, g y - g x⟫ - ⟪g x, g y - g x⟫ = ‖g y - g x‖ ^ 2 := by
      rw [← inner_sub_left, real_inner_self_eq_norm_sq]
    have e2 : β / 2 * (1 / β * ‖g y - g x‖) ^ 2 = ‖g y - g x‖ ^ 2 / (2 * β) := by
      field_simp
    have e3 : 1 / (β : ℝ) * ‖g y - g x‖ ^ 2 = 2 * (‖g y - g x‖ ^ 2 / (2 * β)) := by
      field_simp
    have e' : 1 / (β : ℝ) * ⟪g y, g y - g x⟫ - 1 / (β : ℝ) * ⟪g x, g y - g x⟫
        = 1 / (β : ℝ) * ‖g y - g x‖ ^ 2 := by rw [← mul_sub, e]
    linarith [e2, e3, e']
  have hβ0 : (0 : ℝ) < β := lt_of_le_of_ne (NNReal.coe_nonneg β) (by exact_mod_cast hβ.symm)
  have k1 := key x y
  have k2 := key y x
  have hn : ‖g x - g y‖ = ‖g y - g x‖ := norm_sub_rev _ _
  have e : ⟪g x - g y, x - y⟫ = -⟪g x, y - x⟫ - ⟪g y, x - y⟫ := by
    rw [inner_sub_left, ← neg_sub x y, inner_neg_right]; ring
  have hsum : ‖g x - g y‖ ^ 2 / β ≤ ⟪g x - g y, x - y⟫ := by
    have : ‖g x - g y‖ ^ 2 / β = ‖g y - g x‖ ^ 2 / (2 * β) + ‖g x - g y‖ ^ 2 / (2 * β) := by
      rw [hn]; field_simp; ring
    rw [this]; rw [hn] at k2 ⊢; linarith
  rwa [div_le_iff₀ hβ0, mul_comm] at hsum

omit [CompleteSpace E] in
/-- A gradient step on a sum of `|B|` cocoercive gradients is non-expansive when
    `γ |B| β ≤ 2`. -/
lemma step_nonexpansive {ι : Type*} (B : Finset ι) (G : ι → E → E) {β : ℝ≥0}
    (hmono : ∀ j ∈ B, ∀ x y, 0 ≤ ⟪G j x - G j y, x - y⟫)
    (hcoc : ∀ j ∈ B, ∀ x y, ‖G j x - G j y‖ ^ 2 ≤ β * ⟪G j x - G j y, x - y⟫)
    {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ : γ * B.card * β ≤ 2) (u₁ u₂ : E) :
    ‖(u₁ - γ • ∑ j ∈ B, G j u₁) - (u₂ - γ • ∑ j ∈ B, G j u₂)‖ ≤ ‖u₁ - u₂‖ := by
  set a : ι → E := fun j => G j u₁ - G j u₂
  set A := ∑ j ∈ B, a j
  set Δ := u₁ - u₂
  have hA : (∑ j ∈ B, G j u₁) - ∑ j ∈ B, G j u₂ = A := by
    simp only [A, a, Finset.sum_sub_distrib]
  have hrw : (u₁ - γ • ∑ j ∈ B, G j u₁) - (u₂ - γ • ∑ j ∈ B, G j u₂) = Δ - γ • A := by
    rw [← hA, smul_sub]; simp only [Δ]; abel
  have hinner : ⟪A, Δ⟫ = ∑ j ∈ B, ⟪a j, Δ⟫ := by simp only [A, sum_inner]
  have hpos : 0 ≤ ⟪A, Δ⟫ := by
    rw [hinner]; exact Finset.sum_nonneg fun j hj => hmono j hj u₁ u₂
  have hnormA : ‖A‖ ^ 2 ≤ B.card * β * ⟪A, Δ⟫ := by
    calc ‖A‖ ^ 2 ≤ (∑ j ∈ B, ‖a j‖) ^ 2 := by
          gcongr; exact norm_sum_le _ _
      _ ≤ B.card * ∑ j ∈ B, ‖a j‖ ^ 2 := sq_sum_le_card_mul_sum_sq
      _ ≤ B.card * ∑ j ∈ B, β * ⟪a j, Δ⟫ := by
          gcongr with j hj; exact hcoc j hj u₁ u₂
      _ = B.card * β * ⟪A, Δ⟫ := by rw [← Finset.mul_sum, hinner]; ring
  rw [hrw]
  have hsq : ‖Δ - γ • A‖ ^ 2 ≤ ‖Δ‖ ^ 2 := by
    rw [norm_sub_sq_real, inner_smul_right, norm_smul, Real.norm_of_nonneg hγ0]
    have : γ ^ 2 * ‖A‖ ^ 2 ≤ γ * 2 * ⟪Δ, A⟫ := by
      rw [real_inner_comm]
      calc γ ^ 2 * ‖A‖ ^ 2 ≤ γ ^ 2 * (B.card * β * ⟪A, Δ⟫) := by gcongr
        _ = γ * (γ * B.card * β) * ⟪A, Δ⟫ := by ring
        _ ≤ γ * 2 * ⟪A, Δ⟫ := by gcongr
    nlinarith
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 hsq

end SmoothConvex

namespace DPSGDPaper

variable {N dx d : ℕ}

/-- **Altschuler–Talwar's hypotheses on the loss**: for every record `x`, the loss `ℓ x` is
    differentiable with gradient `grad x`, convex, `β`-smooth (its gradient is
    `β`-Lipschitz) and `C`-Lipschitz. -/
structure ATLoss
    (ℓ : EuclideanSpace ℝ (Fin dx) → EuclideanSpace ℝ (Fin d) → ℝ)
    (grad : EuclideanSpace ℝ (Fin dx) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (β C : ℝ≥0) : Prop where
  hasGradient : ∀ x θ, HasGradientAt (ℓ x) (grad x θ) θ
  convex : ∀ x, ConvexOn ℝ Set.univ (ℓ x)
  smooth : ∀ x, LipschitzWith β (grad x)
  lipschitz : ∀ x, LipschitzWith C (ℓ x)

/-- A `C`-Lipschitz loss has gradients of norm at most `C`, so clipping at `C` is the
    identity. -/
lemma clipV_grad_of_ATLoss {ℓ : EuclideanSpace ℝ (Fin dx) → EuclideanSpace ℝ (Fin d) → ℝ}
    {grad : EuclideanSpace ℝ (Fin dx) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    {β C : ℝ≥0} (h : ATLoss ℓ grad β C) (x : EuclideanSpace ℝ (Fin dx))
    (θ : EuclideanSpace ℝ (Fin d)) : Continuous.clipV C (grad x θ) = grad x θ := by
  have hfd := (hasGradientAt_iff_hasFDerivAt.mp (h.hasGradient x θ)).fderiv
  have hn := norm_fderiv_le_of_lipschitz ℝ (x₀ := θ) (h.lipschitz x)
  rw [hfd, LinearIsometryEquiv.norm_map] at hn
  unfold Continuous.clipV; rw [if_pos hn]

/-- Clipping at `C` is the identity on the gradients of `ℝ^dx_⊥` records: `⊥` has gradient `0`. -/
lemma clipV_gradBot_of_ATLoss {ℓ : EuclideanSpace ℝ (Fin dx) → EuclideanSpace ℝ (Fin d) → ℝ}
    {grad : EuclideanSpace ℝ (Fin dx) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    {β C : ℝ≥0} (h : ATLoss ℓ grad β C) (r : Option (EuclideanSpace ℝ (Fin dx)))
    (θ : EuclideanSpace ℝ (Fin d)) : Continuous.clipV C (gradBot grad r θ) = gradBot grad r θ := by
  cases r with
  | none => unfold Continuous.clipV; simp
  | some x => exact clipV_grad_of_ATLoss h x θ

/-- **Altschuler–Talwar's hypotheses give the non-expansive update** (the hypothesis `hstep`
    of the last-iterate theorems; §5.1.3), at every step `0 ≤ η` with `η β ≤ 2 q`. -/
theorem hstep_of_ATLoss
    {ℓ : EuclideanSpace ℝ (Fin dx) → EuclideanSpace ℝ (Fin d) → ℝ}
    {grad : EuclideanSpace ℝ (Fin dx) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    {β C : ℝ≥0} (h : ATLoss ℓ grad β C) {η : ℝ} {q : ℝ≥0} (hη0 : 0 ≤ η)
    (hηβ : η * β ≤ 2 * q) :
    ∀ (B : Finset (Fin (N + 1))) (Dv : Fin (N + 1) → Option (EuclideanSpace ℝ (Fin dx))) (u₁ u₂),
      ‖(u₁ - γv N η q • clippedBatchSumD (N := N) grad C B Dv u₁)
        - (u₂ - γv N η q • clippedBatchSumD (N := N) grad C B Dv u₂)‖ ≤ ‖u₁ - u₂‖ := by
  intro B Dv u₁ u₂
  simp only [clippedBatchSumD, clipV_gradBot_of_ATLoss h]
  have hγ0 : 0 ≤ γv N η q := by unfold γv; positivity
  have hγ : γv N η q * B.card * β ≤ 2 := by
    have hcard : (B.card : ℝ) ≤ N + 1 := by
      have := B.card_le_univ; rw [Fintype.card_fin] at this; exact_mod_cast this
    calc γv N η q * B.card * β ≤ γv N η q * (N + 1) * β := by gcongr
      _ ≤ 2 := by
        unfold γv
        rcases eq_or_ne (q : ℝ) 0 with hq | hq
        · simp [hq]
        · have hq0 : (0 : ℝ) < q := lt_of_le_of_ne q.2 (Ne.symm hq)
          rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
          nlinarith
  refine SmoothConvex.step_nonexpansive B (fun j => gradBot grad (Dv j)) (fun j _ x y => ?_)
    (fun j _ x y => ?_) hγ0 hγ u₁ u₂
  · cases hj : Dv j with
    | none => simp
    | some r => exact SmoothConvex.inner_grad_sub_nonneg (h.hasGradient r) (h.convex r) x y
  · cases hj : Dv j with
    | none => simp
    | some r => exact SmoothConvex.cocoercive (h.hasGradient r) (h.convex r) (h.smooth r) x y

end DPSGDPaper
