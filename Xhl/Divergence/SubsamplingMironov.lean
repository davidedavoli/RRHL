import Mathlib.Analysis.Complex.ExponentialBounds
import Xhl.Divergence.SubsamplingMixBudget

/-!
# Mironov, Talwar and Zhang's bound on the subsampled-Gaussian budget

`mixBudgetR_le_mironov`: Theorem 11 of Mironov, Talwar, Zhang 2019 ("Rényi Differential Privacy
of the Sampled Gaussian Mechanism", arXiv:1908.10530), at real order, used by Proposition D.4.
The proof follows the source's Lemmas 8–10 as a pointwise domination of the integrand by moments
of the likelihood ratio `t = gaussLR 0 s v`, split at `t = r₀ = 1 + 1/(q(α−1))`:

1. `one_add_rpow_le_quadratic` — `(1+w)^α ≤ 1 + αw + α(α−1)w²` (Bun et al.);
2. `mixture_rpow_le_mironov` — the pointwise bound on the mixture bracket;
3. `mixBudgetR_le_mironov_moments` — its integral against `𝒩(0,v)` (Lemmas 9 and 10);
4. `mironov_tail_le` — the arithmetic of Lemma 10 (cases I, IIa, IIb);
5. `exp_inv_sq_sub_one_le` — `e^{1/σ²} − 1 ≤ 1.1/σ²` for `σ ≥ 4`.
-/

open MeasureTheory ProbabilityTheory ENNReal
open scoped NNReal

namespace Continuous

/-- **Bun et al.'s quadratic bound on `(1+w)^α`** (Bun, Dwork, Rothblum, Steinke 2018,
    Lemma 15, the input of Mironov et al.'s Lemma 8), for real `α > 1` on
    `−1/2 ≤ w ≤ 1/(α−1)`: `(1+w)^α ≤ 1 + αw + α(α−1)w²`.  The difference
    `g(u) = 1 + αu + α(α−1)u² − (1+u)^α` vanishes at `0` and has derivative
    `α(1 + 2(α−1)u − (1+u)^{α−1})`, nonnegative on `[0, 1/(α−1)]`
    (`(1+u)^{α−1} ≤ e^{(α−1)u} ≤ 1 + 2(α−1)u`) and nonpositive on `[−1/2, 0]`
    (`(1+u)^{α−1} ≥ 1 + (α−1)log(1+u) ≥ 1 + 2(α−1)u`). -/
lemma one_add_rpow_le_quadratic {α w : ℝ} (hα : 1 < α) (hw0 : -1 / 2 ≤ w)
    (hw1 : w ≤ 1 / (α - 1)) :
    (1 + w) ^ α ≤ 1 + α * w + α * (α - 1) * w ^ 2 := by
  set g : ℝ → ℝ := fun u => 1 + α * u + α * (α - 1) * u ^ 2 - (1 + u) ^ α with hgdef
  have hg : ∀ u, HasDerivAt g (α * (1 + 2 * (α - 1) * u - (1 + u) ^ (α - 1))) u := by
    intro u
    have h1 : HasDerivAt (fun u : ℝ => (1 + u) ^ α) (α * (1 + u) ^ (α - 1)) u := by
      have h2 : HasDerivAt (fun u : ℝ => 1 + u) 1 u := (hasDerivAt_id u).const_add 1
      simpa using h2.rpow_const (Or.inr hα.le)
    have h3 : HasDerivAt (fun u : ℝ => u ^ 2) (2 * u) u := by
      simpa using hasDerivAt_pow 2 u
    have h := ((((hasDerivAt_id u).const_mul α).const_add 1).add
      (h3.const_mul (α * (α - 1)))).sub h1
    refine h.congr_deriv ?_
    ring
  have hcont : ∀ D : Set ℝ, ContinuousOn g D := fun D u _ =>
    (hg u).continuousAt.continuousWithinAt
  have hdiff : ∀ D : Set ℝ, DifferentiableOn ℝ g D := fun D u _ =>
    (hg u).differentiableAt.differentiableWithinAt
  have hg0 : g 0 = 0 := by simp [hgdef]
  have hα0 : 0 < α := by linarith
  have hα1 : 0 < α - 1 := by linarith
  suffices h : 0 ≤ g w by simp only [hgdef] at h; linarith
  rcases le_total 0 w with hw | hw
  · have hmono : MonotoneOn g (Set.Icc 0 (1 / (α - 1))) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) (hcont _) (hdiff _) ?_
      intro u hu
      rw [interior_Icc] at hu
      rw [(hg u).deriv]
      have hu0 : 0 < 1 + u := by linarith [hu.1]
      have hy1 : (α - 1) * u ≤ 1 := by
        have := mul_le_mul_of_nonneg_left hu.2.le hα1.le
        rwa [mul_one_div_cancel hα1.ne'] at this
      have hy0 : 0 ≤ (α - 1) * u := mul_nonneg hα1.le hu.1.le
      have hp : (1 + u) ^ (α - 1) ≤ Real.exp ((α - 1) * u) := by
        rw [Real.rpow_def_of_pos hu0]
        apply Real.exp_le_exp.2
        have := Real.log_le_sub_one_of_pos hu0
        nlinarith
      have he : Real.exp ((α - 1) * u) ≤ 1 + 2 * ((α - 1) * u) := by
        have h := Real.abs_exp_sub_one_sub_id_le (x := (α - 1) * u)
          (by rw [abs_of_nonneg hy0]; exact hy1)
        have h' := (abs_le.1 h).2
        nlinarith
      exact mul_nonneg hα0.le (by linarith)
    rw [← hg0]
    exact hmono ⟨le_rfl, by positivity⟩ ⟨hw, hw1⟩ hw
  · have hanti : AntitoneOn g (Set.Icc (-1 / 2) 0) := by
      refine antitoneOn_of_deriv_nonpos (convex_Icc _ _) (hcont _) (hdiff _) ?_
      intro u hu
      rw [interior_Icc] at hu
      rw [(hg u).deriv]
      have hu0 : 0 < 1 + u := by linarith [hu.1]
      have hlog : 2 * u ≤ Real.log (1 + u) := by
        have h := Real.one_sub_inv_le_log_of_pos hu0
        have e : 1 - (1 + u)⁻¹ = u / (1 + u) := by field_simp; ring
        have h2 : 2 * u ≤ u / (1 + u) := by
          rw [le_div_iff₀ hu0]; nlinarith [hu.1, hu.2]
        linarith
      have hp : 1 + (α - 1) * Real.log (1 + u) ≤ (1 + u) ^ (α - 1) := by
        rw [Real.rpow_def_of_pos hu0]
        have := Real.add_one_le_exp (Real.log (1 + u) * (α - 1))
        linarith
      have : 1 + 2 * (α - 1) * u ≤ (1 + u) ^ (α - 1) := by nlinarith
      exact mul_nonpos_of_nonneg_of_nonpos hα0.le (by linarith)
    rw [← hg0]
    exact hanti ⟨hw0, hw⟩ ⟨by norm_num, le_rfl⟩ hw

/-- **The mixture bracket against moments of the likelihood ratio** (Mironov et al.'s
    Lemmas 8 and 10, pointwise).  For `α > 1`, `0 < q ≤ 1/2`, `β ≥ α` and `t > 0`, with
    `r₀ = 1 + 1/(q(α−1))`,
    `(1−q+qt)^α ≤ 1 + αq(t−1) + α(α−1)q²(t−1)² + (qα)^α·r₀^{α−β}·t^β`.
    For `t ≤ r₀` drop the last term and apply `one_add_rpow_le_quadratic` at `w = q(t−1)`;
    for `t > r₀`, `1 − q + qt ≤ qαt` and `t^α ≤ r₀^{α−β}t^β`, and the first three terms are
    nonnegative. -/
lemma mixture_rpow_le_mironov {α q β t : ℝ} (hα : 1 < α) (hq0 : 0 < q) (hq : q ≤ 1 / 2)
    (hβ : α ≤ β) (ht : 0 < t) :
    (1 - q + q * t) ^ α ≤ 1 + α * q * (t - 1) + α * (α - 1) * q ^ 2 * (t - 1) ^ 2
      + (q * α) ^ α * (1 + 1 / (q * (α - 1))) ^ (α - β) * t ^ β := by
  set r := 1 + 1 / (q * (α - 1)) with hr
  have hα1 : 0 < α - 1 := by linarith
  have hx : 0 < q * (α - 1) := mul_pos hq0 hα1
  have hr1 : 1 < r := by have := one_div_pos.2 hx; linarith
  have hxr : q * (α - 1) * r = q * (α - 1) + 1 := by
    rw [hr]; field_simp
  have hqα : 0 < q * α := mul_pos hq0 (by linarith)
  have hK : 0 ≤ (q * α) ^ α * r ^ (α - β) * t ^ β := by positivity
  rcases le_or_gt t r with htr | htr
  · have hw0 : -1 / 2 ≤ q * (t - 1) := by nlinarith
    have hw1 : q * (t - 1) ≤ 1 / (α - 1) := by
      have h1 : q * (t - 1) ≤ q * (r - 1) := mul_le_mul_of_nonneg_left (by linarith) hq0.le
      have e : q * (r - 1) = 1 / (α - 1) := by rw [hr]; field_simp; ring
      linarith
    have h := one_add_rpow_le_quadratic hα hw0 hw1
    have e : 1 - q + q * t = 1 + q * (t - 1) := by ring
    rw [e]
    nlinarith [h]
  · have hlin : 1 - q + q * t ≤ q * α * t := by
      have := mul_lt_mul_of_pos_left htr hx
      nlinarith
    have h0 : 0 ≤ 1 - q + q * t := by nlinarith
    have h1 : (1 - q + q * t) ^ α ≤ (q * α * t) ^ α :=
      Real.rpow_le_rpow h0 hlin (by linarith)
    rw [Real.mul_rpow hqα.le ht.le] at h1
    have h2 : t ^ α = t ^ (α - β) * t ^ β := by
      rw [← Real.rpow_add ht]; congr 1; ring
    have h3 : t ^ (α - β) ≤ r ^ (α - β) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) htr.le (by linarith)
    have h4 : (q * α) ^ α * t ^ α ≤ (q * α) ^ α * r ^ (α - β) * t ^ β := by
      rw [h2, ← mul_assoc]
      have : 0 ≤ (q * α) ^ α := by positivity
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 this) (by positivity)
    have h5 : 0 ≤ 1 + α * q * (t - 1) := by nlinarith
    have h6 : 0 ≤ α * (α - 1) * q ^ 2 * (t - 1) ^ 2 := by positivity
    linarith

/-- **The budget against moments** (Mironov et al.'s Lemmas 9 and 10 before their
    arithmetic).  For `α > 1`, `0 < q ≤ 1/2`, `v ≠ 0` and any `β ≥ α`, with
    `r₀ = 1 + 1/(q(α−1))`,
    `Υ_α ≤ 1 + α(α−1)q²(e^{s²/v} − 1) + (qα)^α·r₀^{α−β}·e^{β(β−1)s²/2v}`.
    `mixture_rpow_le_mironov` integrated against `𝒩(0,v)`, each moment by
    `integral_gaussLR_rpow_eq` (`∫ t = 1`, `∫ t² = e^{s²/v}`). -/
lemma mixBudgetR_le_mironov_moments {α : ℝ} (hα : 1 < α) {q : ℝ≥0} (hq0 : 0 < (q : ℝ))
    (hq : (q : ℝ) ≤ 1 / 2) {v : ℝ≥0} (hv : v ≠ 0) (s : ℝ) {β : ℝ} (hβ : α ≤ β) :
    mixBudgetR q s v α ≤ ENNReal.ofReal (1 + α * (α - 1) * (q : ℝ) ^ 2 * (Real.exp (s ^ 2 / v) - 1)
      + ((q : ℝ) * α) ^ α * (1 + 1 / ((q : ℝ) * (α - 1))) ^ (α - β)
        * Real.exp (β * (β - 1) * s ^ 2 / (2 * v))) := by
  have hqNN : q ≤ 1 := by
    have : (q : ℝ) ≤ 1 := by linarith
    exact_mod_cast this
  have h := hellingerIntegral_sgMixture_real (μ₀ := (0 : ℝ)) (Δ := s) hα hv q hqNN
  rw [zero_add] at h
  rw [mixBudgetR, h]
  apply ENNReal.ofReal_le_ofReal
  set μ := gaussianReal (0 : ℝ) v with hμ
  set T : ℝ → ℝ → ℝ := fun γ x => gaussLR 0 s v x ^ γ with hT
  have hTint : ∀ γ, Integrable (T γ) μ := fun γ =>
    integrableOn_univ.mp (integrable_gaussLR_rpow hv γ MeasurableSet.univ)
  have hTE : ∀ γ, ∫ x, T γ x ∂μ = Real.exp (γ * (γ - 1) * s ^ 2 / (2 * v)) := by
    intro γ
    have := integral_gaussLR_rpow_eq (μ₀ := 0) (Δ := s) hv γ MeasurableSet.univ
    rw [setIntegral_univ] at this
    rw [hT, hμ, this]
    simp
  set qr : ℝ := (q : ℝ) with hqr
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = α * (α - 1) * qr ^ 2 := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = (qr * α) ^ α * (1 + 1 / (qr * (α - 1))) ^ (α - β) := ⟨_, rfl⟩
  obtain ⟨c0, hc0⟩ : ∃ c0 : ℝ, c0 = 1 - α * qr + c := ⟨_, rfl⟩
  have hpt : ∀ x, (1 - qr + qr * gaussLR 0 s v x) ^ α ≤
      c0 + ((α * qr - 2 * c) * T 1 x + (c * T 2 x + K * T β x)) := by
    intro x
    have ht : 0 < gaussLR 0 s v x := Real.exp_pos _
    have := mixture_rpow_le_mironov hα hq0 hq hβ ht
    simp only [hT, Real.rpow_one, Real.rpow_two]
    calc _ ≤ _ := this
      _ = _ := by rw [hc0, hK, hc]; ring
  have hint : Integrable (fun x => c0 + ((α * qr - 2 * c) * T 1 x
      + (c * T 2 x + K * T β x))) μ :=
    (integrable_const _).add (((hTint 1).const_mul _).add
      (((hTint 2).const_mul _).add ((hTint β).const_mul _)))
  refine (integral_mono (integrable_mixture_pow hα hv hqNN) hint hpt).trans (le_of_eq ?_)
  have hadd : ∀ {f g : ℝ → ℝ}, Integrable f μ → Integrable g μ →
      ∫ x, f x + g x ∂μ = ∫ x, f x ∂μ + ∫ x, g x ∂μ := fun hf hg => integral_add hf hg
  have hI : ∀ {f g : ℝ → ℝ}, Integrable f μ → Integrable g μ →
      Integrable (fun x => f x + g x) μ := fun hf hg => hf.add hg
  rw [hadd, hadd, hadd]
  rotate_left
  all_goals repeat' (first | exact integrable_const _ | exact (hTint _).const_mul _ | apply hI)
  rw [integral_const, integral_const_mul, integral_const_mul, integral_const_mul,
    hTE, hTE, hTE]
  have e1 : Real.exp (1 * (1 - 1) * s ^ 2 / (2 * v)) = 1 := by simp
  have e2 : Real.exp (2 * (2 - 1) * s ^ 2 / (2 * v)) = Real.exp (s ^ 2 / v) := by
    congr 1; field_simp; ring
  rw [e1, e2, probReal_univ, one_smul, hc0, hK, hc]
  ring

/-- **Mironov et al.'s Lemma 10, the arithmetic.**  Under Theorem 11's hypotheses
    (`0 < q ≤ 1/5`, `σ ≥ 4`, `1 < α ≤ σ²L/2 − 2 log σ` and
    `α ≤ (σ²L²/2 − log 5 − 2 log σ)/(L + log(qα) + 1/(2σ²))`, `L = log r₀`,
    `r₀ = 1 + 1/(q(α−1))`), the split point `z₀ = 1/2 + σ²L` is at least `α`, and the last
    term of `mixBudgetR_le_mironov_moments` at `β = z₀` (sensitivity `1`, variance `σ²`),
    `exp(E)`, `E = α log(qα) + (α − z₀)L + z₀(z₀−1)/(2σ²)`, is at most `0.9·q²α(α−1)/σ²`.
    `E` is the source's exponent `α log(qα) − z₀(z₀−2α)/(2σ²) − α/(2σ²)` (its eq. (6));
    cases I (`α < 2`), IIa (`α ≥ 2`, `q(α−1) < 1/3`) go through its
    `E ≤ α log(qα) − 2L log σ`, case IIb (`q(α−1) ≥ 1/3`) through the second condition. -/
lemma mironov_tail_le {q α σ L : ℝ} (hq0 : 0 < q) (hq : q ≤ 1 / 5) (hσ : 4 ≤ σ) (hα : 1 < α)
    (hL : L = Real.log (1 + 1 / (q * (α - 1))))
    (h₁ : α ≤ σ ^ 2 * L / 2 - 2 * Real.log σ)
    (h₂ : α ≤ (σ ^ 2 * L ^ 2 / 2 - Real.log 5 - 2 * Real.log σ)
      / (L + Real.log (q * α) + 1 / (2 * σ ^ 2))) :
    α ≤ 1 / 2 + σ ^ 2 * L ∧
    (q * α) ^ α * (1 + 1 / (q * (α - 1))) ^ (α - (1 / 2 + σ ^ 2 * L))
      * Real.exp ((1 / 2 + σ ^ 2 * L) * (1 / 2 + σ ^ 2 * L - 1) / (2 * σ ^ 2))
      ≤ 9 / 10 * q ^ 2 * α * (α - 1) / σ ^ 2 := by
  set x := q * (α - 1) with hxdef
  set r := 1 + 1 / x with hrdef
  have hα1 : 0 < α - 1 := by linarith
  have hα0 : 0 < α := by linarith
  have hx : 0 < x := mul_pos hq0 hα1
  have hr1 : 1 < r := by have := one_div_pos.2 hx; linarith
  have hr0 : 0 < r := by linarith
  have hLr : L = Real.log r := hL
  have hLpos : 0 < L := by rw [hLr]; exact Real.log_pos hr1
  have hσ0 : 0 < σ := by linarith
  have hS0 : 0 < σ ^ 2 := by positivity
  have hqα : 0 < q * α := mul_pos hq0 hα0
  -- numerics
  have hl2 := Real.log_two_gt_d9
  have hl4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hℓ : 2 * Real.log 2 ≤ Real.log σ := by
    rw [← hl4]; exact Real.log_le_log (by norm_num) hσ
  have hl910 : -(1 / 9) ≤ Real.log (9 / 10) := by
    have := Real.one_sub_inv_le_log_of_pos (x := 9 / 10) (by norm_num)
    norm_num at this ⊢; linarith
  -- the logarithms of `qα` and `x = q(α−1)`
  have hlqα : Real.log (q * α) = Real.log q + Real.log α := Real.log_mul hq0.ne' hα0.ne'
  have hlx : Real.log x = Real.log q + Real.log (α - 1) := Real.log_mul hq0.ne' hα1.ne'
  have hxr : x * r = x + 1 := by rw [hrdef]; field_simp
  have hLx : Real.log x + L = Real.log (x + 1) := by
    rw [hLr, ← Real.log_mul hx.ne' hr0.ne', hxr]
  have hlx1 : 0 ≤ Real.log (x + 1) := Real.log_nonneg (by linarith)
  -- the split point `z₀ = 1/2 + σ²L`: `z₀ − 2α ≥ 4 log σ` (the source's eq. (8))
  have hz : 2 * α + 4 * Real.log σ ≤ σ ^ 2 * L := by linarith
  refine ⟨by linarith, ?_⟩
  -- the left side is `exp E`
  rw [Real.rpow_def_of_pos hqα, Real.rpow_def_of_pos hr0, ← hLr, ← Real.exp_add,
    ← Real.exp_add]
  have hRpos : 0 < 9 / 10 * q ^ 2 * α * (α - 1) / σ ^ 2 := by positivity
  rw [← Real.exp_log hRpos]
  apply Real.exp_le_exp.2
  have hlogR : Real.log (9 / 10 * q ^ 2 * α * (α - 1) / σ ^ 2)
      = Real.log (9 / 10) + 2 * Real.log q + Real.log α + Real.log (α - 1)
        - 2 * Real.log σ := by
    rw [Real.log_div (by positivity) hS0.ne', Real.log_mul (by positivity) hα1.ne',
      Real.log_mul (by positivity) hα0.ne', Real.log_mul (by norm_num) (by positivity),
      Real.log_pow, Real.log_pow]
    push_cast; ring
  rw [hlogR]
  -- the source's form of the exponent (its eq. (6))
  have hE : Real.log (q * α) * α + L * (α - (1 / 2 + σ ^ 2 * L))
      + (1 / 2 + σ ^ 2 * L) * (1 / 2 + σ ^ 2 * L - 1) / (2 * σ ^ 2)
      = α * Real.log (q * α) - (1 / 2 + σ ^ 2 * L) * (1 / 2 + σ ^ 2 * L - 2 * α) / (2 * σ ^ 2)
        - α / (2 * σ ^ 2) := by
    field_simp; ring
  rw [hE]
  have hα2S : 0 ≤ α / (2 * σ ^ 2) := by positivity
  -- the source's `z₀(z₀−2α)/(2σ²) ≥ 2L log σ`, from `z₀ − 2α ≥ 4 log σ` and `z₀ ≥ σ²L`
  have hgen : 2 * L * Real.log σ
      ≤ (1 / 2 + σ ^ 2 * L) * (1 / 2 + σ ^ 2 * L - 2 * α) / (2 * σ ^ 2) := by
    rw [le_div_iff₀ (by positivity)]
    have a1 : σ ^ 2 * L ≤ 1 / 2 + σ ^ 2 * L := by linarith
    have a2 : 4 * Real.log σ ≤ 1 / 2 + σ ^ 2 * L - 2 * α := by linarith
    have a3 : 0 ≤ 4 * Real.log σ := by linarith
    have a4 : 0 ≤ 1 / 2 + σ ^ 2 * L := by positivity
    have h1 := mul_le_mul a1 a2 a3 a4
    have e : 2 * L * Real.log σ * (2 * σ ^ 2) = σ ^ 2 * L * (4 * Real.log σ) := by ring
    rw [e]; exact h1
  have hl2a : 6931 / 10000 < Real.log 2 := by
    have := Real.log_two_gt_d9; norm_num at this ⊢; linarith
  have hl2b : Real.log 2 < 6932 / 10000 := by
    have := Real.log_two_lt_d9; norm_num at this ⊢; linarith
  have hl2sq : 6931 / 10000 * (6931 / 10000) ≤ Real.log 2 * Real.log 2 :=
    mul_le_mul hl2a.le hl2a.le (by norm_num) (by linarith)
  rcases lt_or_ge α 2 with hα2 | hα2
  · -- Case I: `α < 2`
    have hxq : x < q := by
      have := mul_lt_mul_of_pos_left (by linarith : α - 1 < 1) hq0
      rw [hxdef]; linarith
    have hr6 : 6 ≤ r := by
      have : 5 ≤ 1 / x := (le_div_iff₀ hx).2 (by linarith)
      linarith
    have hL6 : 2 * Real.log 2 + 1 / 3 ≤ L := by
      have h6 : Real.log 6 = Real.log 4 + Real.log (3 / 2) := by
        rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
      have h32 := Real.one_sub_inv_le_log_of_pos (x := 3 / 2) (by norm_num)
      have := Real.log_le_log (by norm_num) hr6
      rw [hLr]; norm_num at h32; linarith
    have hqαle : Real.log (q * α) ≤ 0 := by
      refine Real.log_nonpos hqα.le ?_
      have := mul_lt_mul_of_pos_left hα2 hq0
      linarith
    have hp1 : 0 ≤ (α - 1) * (-(Real.log q + Real.log α)) :=
      mul_nonneg hα1.le (by linarith)
    have hp2 : (2 * Real.log 2 + 1 / 3 - 1) * (2 * (2 * Real.log 2) - 1)
        ≤ (L - 1) * (2 * Real.log σ - 1) := by
      have b1 : 2 * Real.log 2 + 1 / 3 - 1 ≤ L - 1 := by linarith
      have b2 : 2 * (2 * Real.log 2) - 1 ≤ 2 * Real.log σ - 1 := by linarith
      have b3 : 0 ≤ 2 * (2 * Real.log 2) - 1 := by linarith
      have b4 : 0 ≤ L - 1 := by linarith
      exact mul_le_mul b1 b2 b3 b4
    have hnum : 6 / 5 ≤ (2 * Real.log 2 + 1 / 3 - 1) * (2 * (2 * Real.log 2) - 1) := by
      linarith
    rw [hlqα]
    linarith
  rcases lt_or_ge x (1 / 3) with hx3 | hx3
  · -- Case IIa: `α ≥ 2`, `q(α−1) < 1/3`
    have hr4 : 4 ≤ r := by
      have : 3 ≤ 1 / x := (le_div_iff₀ hx).2 (by linarith)
      linarith
    have hL4 : 2 * Real.log 2 ≤ L := by
      rw [hLr, ← hl4]; exact Real.log_le_log (by norm_num) hr4
    have hqαle : Real.log (q * α) ≤ 0 := by
      refine Real.log_nonpos hqα.le ?_
      have := mul_nonneg hq0.le (by linarith : (0 : ℝ) ≤ α - 2)
      have e : x = q * α - q := by rw [hxdef]; ring
      linarith
    have hlα : Real.log α ≤ Real.log 2 + Real.log (α - 1) := by
      rw [← Real.log_mul (by norm_num) hα1.ne']
      exact Real.log_le_log hα0 (by linarith)
    have hp1 : 0 ≤ (α - 2) * (-(Real.log q + Real.log α)) :=
      mul_nonneg (by linarith) (by linarith)
    have hp2 : (2 * Real.log 2 - 1) * (2 * Real.log 2) ≤ (L - 1) * Real.log σ := by
      have c1 : 2 * Real.log 2 - 1 ≤ L - 1 := by linarith
      have c3 : 0 ≤ 2 * Real.log 2 := by linarith
      have c4 : 0 ≤ L - 1 := by linarith
      exact mul_le_mul c1 hℓ c3 c4
    have hnum : 1 / 9 + Real.log 2 ≤ 2 * ((2 * Real.log 2 - 1) * (2 * Real.log 2)) := by
      linarith
    rw [hlqα]
    linarith
  · -- Case IIb: `α ≥ 2`, `q(α−1) ≥ 1/3`: the second condition
    have hqr : q * α * r = q * α + α / (α - 1) := by
      rw [hrdef, hxdef]; field_simp
    have hαα : 1 ≤ α / (α - 1) := by rw [le_div_iff₀ hα1]; linarith
    have hD0 : 0 ≤ Real.log (q * α) + L := by
      rw [hLr, ← Real.log_mul hqα.ne' hr0.ne']
      refine Real.log_nonneg ?_
      rw [hqr]; linarith
    have hS2 : 0 < 1 / (2 * σ ^ 2) := by positivity
    have hD : 0 < L + Real.log (q * α) + 1 / (2 * σ ^ 2) := by linarith
    have h₂' := (le_div_iff₀ hD).1 h₂
    have hE2 : α * Real.log (q * α) - (1 / 2 + σ ^ 2 * L) * (1 / 2 + σ ^ 2 * L - 2 * α)
          / (2 * σ ^ 2) - α / (2 * σ ^ 2)
        = α * (L + Real.log (q * α) + 1 / (2 * σ ^ 2)) - α / (2 * σ ^ 2)
          - L / 2 - σ ^ 2 * L ^ 2 / 2 - 1 / (8 * σ ^ 2) := by
      field_simp; ring
    rw [hE2]
    have h8 : 0 ≤ 1 / (8 * σ ^ 2) := by positivity
    -- `L + 2 log(3x/2) ≥ 0`, as `r·(3x/2)² = 9x(x+1)/4 ≥ 1`
    have hx32 : 0 < 3 * x / 2 := by linarith
    have hF : 0 ≤ L + 2 * Real.log (3 * x / 2) := by
      have e : r * (3 * x / 2) ^ 2 = 9 / 4 * (x * (x + 1)) := by
        rw [show r * (3 * x / 2) ^ 2 = 9 / 4 * x * (x * r) by ring, hxr]; ring
      have h0 : 1 / 3 * (1 / 3 + 1) ≤ x * (x + 1) :=
        mul_le_mul hx3 (by linarith) (by norm_num) hx.le
      have h1 : 1 ≤ r * (3 * x / 2) ^ 2 := by rw [e]; linarith
      have h2 := Real.log_nonneg h1
      rw [Real.log_mul hr0.ne' (pow_pos hx32 2).ne', Real.log_pow] at h2
      rw [hLr]; push_cast at h2; linarith
    -- `log(3x/2) − log 5 = log(3x/10) ≤ log(0.9·qα·x)`, as `qα ≥ x ≥ 1/3`
    have hG : Real.log (3 * x / 2) - Real.log 5
        ≤ Real.log (9 / 10) + Real.log (q * α) + Real.log x := by
      rw [← Real.log_div hx32.ne' (by norm_num), ← Real.log_mul (by norm_num) hqα.ne',
        ← Real.log_mul (by positivity) hx.ne']
      refine Real.log_le_log (by linarith) ?_
      have hxqα : x ≤ q * α := by
        have e : x = q * α - q := by rw [hxdef]; ring
        linarith
      have : x * (1 / 3) ≤ x * (q * α) := mul_le_mul_of_nonneg_left (by linarith) hx.le
      linarith
    rw [hlqα, hlx] at hG
    linarith

/-- `e^{1/σ²} − 1 ≤ 1.1/σ²` for `σ ≥ 4` (the last step of Mironov et al.'s proof of
    Theorem 11), from `e^y ≤ 1 + y + y²` at `y = 1/σ² ≤ 1/16`. -/
lemma exp_inv_sq_sub_one_le {σ : ℝ} (hσ : 4 ≤ σ) :
    Real.exp (1 / σ ^ 2) - 1 ≤ 11 / 10 * (1 / σ ^ 2) := by
  have hy0 : 0 ≤ 1 / σ ^ 2 := by positivity
  have hy16 : 1 / σ ^ 2 ≤ 1 / 16 :=
    one_div_le_one_div_of_le (by norm_num) (by nlinarith)
  have h := Real.abs_exp_sub_one_sub_id_le (x := 1 / σ ^ 2)
    (by rw [abs_of_nonneg hy0]; linarith)
  have h' := (abs_le.1 h).2
  have h2 : (1 / σ ^ 2) ^ 2 ≤ 1 / σ ^ 2 * (1 / 16) := by
    rw [sq]; exact mul_le_mul_of_nonneg_left hy16 hy0
  linarith

/-- **Mironov, Talwar, Zhang 2019, Theorem 11**: if `q ≤ 1/5`, `σ ≥ 4` and the real order
    `α > 1` satisfies `α ≤ σ²L/2 − 2 log σ` and
    `α ≤ (σ²L²/2 − log 5 − 2 log σ)/(L + log(qα) + 1/(2σ²))`, `L = log(1 + 1/(q(α−1)))`, then
    `Υ_α ≤ exp((α−1)·2q²αs²/v)`. The source's `σ` is the noise standard deviation over the
    sensitivity, `σ²s² = v`. -/
theorem mixBudgetR_le_mironov {α : ℝ} (hα : 1 < α) {q : ℝ≥0} (hq : (q : ℝ) ≤ 1 / 5)
    {s : ℝ} {v : ℝ≥0} {σ : ℝ} (hσv : σ ^ 2 * s ^ 2 = v) (hσ : 4 ≤ σ)
    (h₁ : α ≤ σ ^ 2 * Real.log (1 + 1 / ((q : ℝ) * (α - 1))) / 2 - 2 * Real.log σ)
    (h₂ : α ≤ (σ ^ 2 * Real.log (1 + 1 / ((q : ℝ) * (α - 1))) ^ 2 / 2 - Real.log 5
        - 2 * Real.log σ)
      / (Real.log (1 + 1 / ((q : ℝ) * (α - 1))) + Real.log ((q : ℝ) * α) + 1 / (2 * σ ^ 2))) :
    mixBudgetR q s v α
      ≤ ENNReal.ofReal (Real.exp ((α - 1) * (2 * (q : ℝ) ^ 2 * α * s ^ 2 / v))) := by
  have hσ0 : 0 < σ := by linarith
  have hlσ : 0 < Real.log σ := Real.log_pos (by linarith)
  have hq0 : 0 < (q : ℝ) := by
    rcases (NNReal.coe_nonneg q).eq_or_lt with h | h
    · exfalso; rw [← h] at h₁; simp at h₁; linarith
    · exact h
  rcases eq_or_ne s 0 with rfl | hs
  · rw [mixBudgetR_zero hα v (by linarith)]; simp
  have hvpos : (0 : ℝ) < v := by rw [← hσv]; positivity
  have hv : v ≠ 0 := by intro h; rw [h] at hvpos; simp at hvpos
  set L := Real.log (1 + 1 / ((q : ℝ) * (α - 1))) with hL
  obtain ⟨hzα, htail⟩ := mironov_tail_le hq0 hq hσ hα hL h₁ h₂
  refine (mixBudgetR_le_mironov_moments hα hq0 (by linarith) hv s hzα).trans ?_
  apply ENNReal.ofReal_le_ofReal
  have hsv : s ^ 2 / v = 1 / σ ^ 2 := by rw [← hσv]; field_simp
  have hsv2 : (1 / 2 + σ ^ 2 * L) * (1 / 2 + σ ^ 2 * L - 1) * s ^ 2 / (2 * v)
      = (1 / 2 + σ ^ 2 * L) * (1 / 2 + σ ^ 2 * L - 1) / (2 * σ ^ 2) := by
    rw [← hσv]; field_simp
  rw [hsv, hsv2]
  have hc : 0 ≤ α * (α - 1) * (q : ℝ) ^ 2 :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) (sq_nonneg _)
  have hexp := mul_le_mul_of_nonneg_left (exp_inv_sq_sub_one_le hσ) hc
  have hε : 2 * (q : ℝ) ^ 2 * α * (α - 1) / σ ^ 2 + 1
      ≤ Real.exp ((α - 1) * (2 * (q : ℝ) ^ 2 * α * s ^ 2 / v)) := by
    have e : (α - 1) * (2 * (q : ℝ) ^ 2 * α * s ^ 2 / v)
        = 2 * (q : ℝ) ^ 2 * α * (α - 1) / σ ^ 2 := by
      rw [show 2 * (q : ℝ) ^ 2 * α * s ^ 2 / v = 2 * (q : ℝ) ^ 2 * α * (s ^ 2 / v) by ring, hsv]
      ring
    rw [e]; exact Real.add_one_le_exp _
  have e2 : α * (α - 1) * (q : ℝ) ^ 2 * (11 / 10 * (1 / σ ^ 2))
      + 9 / 10 * (q : ℝ) ^ 2 * α * (α - 1) / σ ^ 2
      = 2 * (q : ℝ) ^ 2 * α * (α - 1) / σ ^ 2 := by
    field_simp; ring
  linarith

end Continuous
