import Xhl.Divergence.SubsamplingRealOrderE

/-!
# The subsampled Gaussian in the reversed order

  `Λ_α(q, s, v) = H_α(𝒩(0,v) ‖ (1-q)·𝒩(0,v) + q·𝒩(s,v))`   (`mixFlipBudgetE`),

the cost of a subsampled Gaussian step when the differing record is absent on the left
(§5.1.1, Appendix E.1). As for `Υ_α`: the mixture identity
(`hellingerIntegral_flip_mixture_real_lintegral`, integrand `((1-q)+q·L)^{1-α}`, bounded by
`(1-q)^{1-α}`), monotonicity in `|Δ|` by convex order (`hellingerIntegral_flip_sgMixture_real_mono`),
and the reduction of the vector case to the scalar one
(`hellingerIntegral_flip_sgMixtureE_le_budget_of_le`). Lemma E.1 bounds it by `Υ_α`
(`SubsamplingDomination.lean`).
-/

open MeasureTheory ProbabilityTheory ENNReal Real
open scoped NNReal

namespace Continuous

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## A negative power is convex on a positive half-line -/

/-- `x ↦ x^p` is convex on `Ici c` for `c > 0` and `p ≤ 0`. -/
lemma convexOn_rpow_nonpos {p c : ℝ} (hp : p ≤ 0) (hc : 0 < c) :
    ConvexOn ℝ (Set.Ici c) (fun x : ℝ => x ^ p) := by
  have hpos : ∀ x ∈ Set.Ici c, (0:ℝ) < x := fun x hx => lt_of_lt_of_le hc hx
  have hposi : ∀ x ∈ interior (Set.Ici c), (0:ℝ) < x := by
    intro x hx
    rw [interior_Ici] at hx
    exact hc.trans hx
  refine convexOn_of_deriv2_nonneg (convex_Ici c) ?_ ?_ ?_ ?_
  · exact ContinuousOn.rpow_const continuousOn_id (fun x hx => Or.inl (hpos x hx).ne')
  · exact fun x hx =>
      (Real.differentiableAt_rpow_const_of_ne p (hposi x hx).ne').differentiableWithinAt
  · rw [Real.deriv_rpow_const' p]
    exact fun x hx =>
      ((Real.differentiableAt_rpow_const_of_ne (p - 1)
        (hposi x hx).ne').const_mul p).differentiableWithinAt
  · intro x hx
    have hxpos := hposi x hx
    have hd : deriv^[2] (fun x : ℝ => x ^ p) x = p * ((p - 1) * x ^ (p - 1 - 1)) := by
      have hone : (deriv fun x : ℝ => x ^ p) = fun x : ℝ => p * x ^ (p - 1) :=
        Real.deriv_rpow_const' p
      have h2 : deriv^[2] (fun x : ℝ => x ^ p) x
          = deriv (deriv fun x : ℝ => x ^ p) x := by
        simp [Function.iterate_succ_apply']
      rw [h2, hone,
        deriv_const_mul _ (Real.differentiableAt_rpow_const_of_ne (p - 1) hxpos.ne'),
        Real.deriv_rpow_const]
    rw [hd]
    have h3 : (0:ℝ) ≤ p * (p - 1) := by nlinarith
    have h4 : (0:ℝ) < x ^ (p - 1 - 1) := Real.rpow_pos_of_pos hxpos _
    nlinarith

/-! ## The reversed mixture identity -/

/-- `ν` is absolutely continuous with respect to any `q`-mixture `(1-q)·ν + q·ν'` with `q < 1`:
    the mixture dominates `(1-q)·ν`. -/
lemma ac_mixture_base {q : ℝ≥0∞} (hq1 : q < 1) (ν ν' : Measure Ω) :
    ν ≪ (1 - q) • ν + q • ν' := by
  intro s hs
  have hne : (1 - q) ≠ 0 := by
    simp only [ne_eq, tsub_eq_zero_iff_le]
    exact fun h => absurd (lt_of_lt_of_le hq1 h) (lt_irrefl _)
  have h0 : ((1 - q) • ν + q • ν') s = 0 := hs
  simp only [Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h0
  have := (add_eq_zero.mp h0).1
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h hne
  · exact h

/-- **The reversed mixture identity**: `H_α(ν ‖ (1-q)ν + qν') = ∫ ((1-q)+q·L)^{1-α} dν`,
    `L` the likelihood ratio. -/
theorem hellingerIntegral_flip_mixture_real_lintegral {α : ℝ} (hα : 1 < α) {q : ℝ≥0∞} (hq1 : q < 1)
    (ν ν' : Measure Ω) [IsFiniteMeasure ν] [IsFiniteMeasure ν'] (hac : ν' ≪ ν) :
    hellingerIntegral α ν ((1 - q) • ν + q • ν')
      = ∫⁻ x, ((1 - q) + q * ν'.rnDeriv ν x) ^ (1 - α) ∂ν := by
  have hqtop : q ≠ ⊤ := hq1.ne_top
  set L : Ω → ℝ≥0∞ := ν'.rnDeriv ν with hLdef
  have hL : Measurable L := Measure.measurable_rnDeriv _ _
  have hf : Measurable (fun x => (1 - q) + q * L x) :=
    measurable_const.add (measurable_const.mul hL)
  have hmixwd : (1 - q) • ν + q • ν' = ν.withDensity (fun x => (1 - q) + q * L x) := by
    have e2 : q • ν' = ν.withDensity (fun x => q * L x) := by
      rw [show (fun x : Ω => q * L x) = q • L from rfl, withDensity_smul _ hL]
      congr 1
      rw [hLdef]; exact (Measure.withDensity_rnDeriv_eq _ _ hac).symm
    rw [(withDensity_const (1 - q)).symm, e2, ← withDensity_add_left measurable_const]
    rfl
  have : IsFiniteMeasure (ν.withDensity (fun x => (1 - q) + q * L x)) := by
    refine isFiniteMeasure_withDensity ?_
    rw [lintegral_add_left measurable_const, lintegral_const, lintegral_const_mul _ hL, hLdef,
      Measure.lintegral_rnDeriv hac]
    refine ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ?_ (measure_ne_top ν _),
      ENNReal.mul_ne_top hqtop (measure_ne_top ν' _)⟩
    exact (tsub_le_self.trans_lt one_lt_top).ne
  have : IsFiniteMeasure ((1 - q) • ν + q • ν') := by rw [hmixwd]; infer_instance
  have hmixac : (1 - q) • ν + q • ν' ≪ ν := by
    rw [hmixwd]; exact withDensity_absolutelyContinuous _ _
  have hmixrn : ((1 - q) • ν + q • ν').rnDeriv ν
      =ᵐ[ν] fun x => (1 - q) + q * L x := by
    rw [hmixwd]; exact Measure.rnDeriv_withDensity _ hf
  have hbase : ν ≪ (1 - q) • ν + q • ν' := ac_mixture_base hq1 ν ν'
  rw [← hRen_ref_indep hα ν ((1 - q) • ν + q • ν') ν hbase hmixac, hRen]
  refine lintegral_congr_ae ?_
  filter_upwards [ν.rnDeriv_self, hmixrn] with x hx hmx
  rw [hx, hmx, ENNReal.one_rpow, one_mul]

/-! ## The reversed scalar integrand -/

/-- The reversed mixture integrand, for the convex-order argument: `t ↦ ((1-q)+q·t)^{1-α}`. -/
noncomputable def mixturePowF (α : ℝ) (q : ℝ≥0) (t : ℝ) : ℝ :=
  ((1 - (q:ℝ)) + (q:ℝ) * t) ^ (1 - α)

lemma mixturePowF_base_pos {q : ℝ≥0} (hq1 : (q:ℝ) < 1) {t : ℝ} (ht : 0 ≤ t) :
    (0:ℝ) < (1 - (q:ℝ)) + (q:ℝ) * t := by
  have hqnn : (0:ℝ) ≤ (q:ℝ) := q.coe_nonneg
  nlinarith

lemma mixturePowF_nonneg {α : ℝ} {q : ℝ≥0} (hq1 : (q:ℝ) < 1) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ mixturePowF α q t :=
  Real.rpow_nonneg (mixturePowF_base_pos hq1 ht).le _

/-- On `t ≥ 0` the reversed integrand is at most `(1-q)^{1-α}`. -/
lemma mixturePowF_le {α : ℝ} (hα : 1 ≤ α) {q : ℝ≥0} (hq1 : (q:ℝ) < 1) {t : ℝ} (ht : 0 ≤ t) :
    mixturePowF α q t ≤ (1 - (q:ℝ)) ^ (1 - α) := by
  have hqnn : (0:ℝ) ≤ (q:ℝ) := q.coe_nonneg
  have h1 : (0:ℝ) < 1 - (q:ℝ) := by linarith
  have h2 : (1 - (q:ℝ)) ≤ (1 - (q:ℝ)) + (q:ℝ) * t := by nlinarith
  exact Real.rpow_le_rpow_of_nonpos h1 h2 (by linarith)

/-- `mixturePowF α q` is convex on `t ≥ 0`. -/
lemma convexOn_mixturePowF {α : ℝ} (hα : 1 ≤ α) {q : ℝ≥0} (hq1 : (q:ℝ) < 1) :
    ConvexOn ℝ (Set.Ici (0:ℝ)) (mixturePowF α q) := by
  have hqnn : (0:ℝ) ≤ (q:ℝ) := q.coe_nonneg
  have h1 : (0:ℝ) < 1 - (q:ℝ) := by linarith
  have hbase := convexOn_rpow_nonpos (p := 1 - α) (c := 1 - (q:ℝ)) (by linarith) h1
  refine ⟨convex_Ici 0, fun x hx y hy a b ha hb hab => ?_⟩
  simp only [smul_eq_mul] at hab ⊢
  have hxnn : (0:ℝ) ≤ x := hx
  have hynn : (0:ℝ) ≤ y := hy
  set u := (1 - (q:ℝ)) + (q:ℝ) * x with hu
  set w := (1 - (q:ℝ)) + (q:ℝ) * y with hw
  have hune : u ∈ Set.Ici (1 - (q:ℝ)) := by rw [hu, Set.mem_Ici]; nlinarith
  have hwne : w ∈ Set.Ici (1 - (q:ℝ)) := by rw [hw, Set.mem_Ici]; nlinarith
  have hkey := hbase.2 hune hwne ha hb hab
  simp only [smul_eq_mul] at hkey
  have heq : (1 - (q:ℝ)) + (q:ℝ) * (a * x + b * y) = a * u + b * w := by
    rw [hu, hw]; nlinarith [hab]
  show mixturePowF α q (a * x + b * y) ≤ a * mixturePowF α q x + b * mixturePowF α q y
  unfold mixturePowF
  rw [heq]
  exact hkey

lemma continuousOn_mixturePowF {α : ℝ} {q : ℝ≥0} (hq1 : (q:ℝ) < 1) :
    ContinuousOn (mixturePowF α q) (Set.Ici (0:ℝ)) := by
  unfold mixturePowF
  exact ContinuousOn.rpow_const (by fun_prop)
    (fun t ht => Or.inl (mixturePowF_base_pos hq1 ht).ne')

lemma continuous_mixturePowF_comp {α : ℝ} {q : ℝ≥0} (hq1 : (q:ℝ) < 1)
    {f : ℝ → ℝ} (hf : Continuous f) (hfnn : ∀ x, 0 ≤ f x) :
    Continuous fun x => mixturePowF α q (f x) := by
  unfold mixturePowF
  exact Continuous.rpow_const (by fun_prop)
    (fun x => Or.inl (mixturePowF_base_pos hq1 (hfnn x)).ne')

lemma integrable_mixturePowF_comp {α : ℝ} (hα : 1 ≤ α) {q : ℝ≥0} (hq1 : (q:ℝ) < 1)
    {f : ℝ → ℝ} (hf : Continuous f) (hfnn : ∀ x, 0 ≤ f x)
    {μ : Measure ℝ} [IsFiniteMeasure μ] :
    Integrable (fun x => mixturePowF α q (f x)) μ := by
  refine Integrable.mono' (integrable_const ((1 - (q:ℝ)) ^ (1 - α)))
    (continuous_mixturePowF_comp hq1 hf hfnn).aestronglyMeasurable (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (mixturePowF_nonneg (α := α) hq1 (hfnn x))]
  exact mixturePowF_le hα hq1 (hfnn x)

/-- **The convex-order step, reversed**: `β ↦ E_{y∼𝒩(0,β)}[mixturePowF α q (exp(y-β/2))]` is
    monotone. -/
theorem mixturePowF_integral_mono_variance {α : ℝ} (hα : 1 ≤ α) {q : ℝ≥0} (hq1 : (q:ℝ) < 1)
    {β1 β2 : ℝ≥0} (hβ : β1 ≤ β2) :
    ∫ y, mixturePowF α q (Real.exp (y - (β1:ℝ)/2)) ∂(gaussianReal 0 β1)
      ≤ ∫ y, mixturePowF α q (Real.exp (y - (β2:ℝ)/2)) ∂(gaussianReal 0 β2) := by
  set τ : ℝ≥0 := β2 - β1 with hτdef
  have hτ : β1 + τ = β2 := add_tsub_cancel_of_le hβ
  have hconv : gaussianReal (0:ℝ) β1 ∗ gaussianReal (0:ℝ) τ = gaussianReal 0 β2 := by
    rw [gaussianReal_conv_gaussianReal, hτ, add_zero]
  have hconvdef : gaussianReal (0:ℝ) β1 ∗ gaussianReal (0:ℝ) τ
      = Measure.map (fun p : ℝ × ℝ => p.1 + p.2)
          ((gaussianReal (0:ℝ) β1).prod (gaussianReal (0:ℝ) τ)) := rfl
  have hmap2 : Measure.map (fun p : ℝ × ℝ => p.1 + p.2)
      ((gaussianReal (0:ℝ) β1).prod (gaussianReal (0:ℝ) τ)) = gaussianReal 0 β2 := by
    rw [← hconvdef, hconv]
  have hg2int : Integrable (fun y => mixturePowF α q (Real.exp (y - (β2:ℝ)/2)))
      (gaussianReal 0 β2) :=
    integrable_mixturePowF_comp hα hq1 (by fun_prop) (fun y => (Real.exp_pos _).le)
  have hg2int' : Integrable (fun w => mixturePowF α q (Real.exp (w - (β2:ℝ)/2)))
      (Measure.map (fun p : ℝ × ℝ => p.1 + p.2)
        ((gaussianReal (0:ℝ) β1).prod (gaussianReal (0:ℝ) τ))) := by
    rw [hmap2]; exact hg2int
  have hjoint' : Integrable (fun p : ℝ × ℝ => mixturePowF α q (Real.exp (p.1 + p.2 - (β2:ℝ)/2)))
      ((gaussianReal (0:ℝ) β1).prod (gaussianReal (0:ℝ) τ)) :=
    hg2int'.comp_measurable (by fun_prop)
  have hFubini : ∫ p, mixturePowF α q (Real.exp (p.1 + p.2 - (β2:ℝ)/2))
        ∂((gaussianReal (0:ℝ) β1).prod (gaussianReal (0:ℝ) τ))
      = ∫ y, ∫ z, mixturePowF α q (Real.exp (y + z - (β2:ℝ)/2))
          ∂(gaussianReal 0 τ) ∂(gaussianReal 0 β1) :=
    integral_prod _ hjoint'
  have hF2eq : ∫ y, mixturePowF α q (Real.exp (y - (β2:ℝ)/2)) ∂(gaussianReal 0 β2)
      = ∫ p, mixturePowF α q (Real.exp (p.1 + p.2 - (β2:ℝ)/2))
          ∂((gaussianReal (0:ℝ) β1).prod (gaussianReal (0:ℝ) τ)) := by
    rw [← hmap2, integral_map (by fun_prop) hg2int'.aestronglyMeasurable]
  have hpointwise : ∀ᵐ y ∂(gaussianReal (0:ℝ) β1),
      mixturePowF α q (Real.exp (y - (β1:ℝ)/2))
        ≤ ∫ z, mixturePowF α q (Real.exp (y + z - (β2:ℝ)/2)) ∂(gaussianReal 0 τ) := by
    filter_upwards with y
    set m : ℝ := Real.exp (y - (β1:ℝ)/2) with hmdef
    have hmpos : 0 < m := Real.exp_pos _
    have halg : ∀ z : ℝ, y + z - (β2:ℝ)/2 = (y - (β1:ℝ)/2) + (z - (τ:ℝ)/2) := by
      intro z
      have hβ2 : (β2:ℝ) = (β1:ℝ) + (τ:ℝ) := by exact_mod_cast hτ.symm
      rw [hβ2]; ring
    have hexpsplit : ∀ z : ℝ, Real.exp (y + z - (β2:ℝ)/2) = m * Real.exp (z - (τ:ℝ)/2) := by
      intro z; rw [halg z, Real.exp_add, hmdef]
    have hz' : Integrable (fun z => mixturePowF α q (m * Real.exp (z - (τ:ℝ)/2)))
        (gaussianReal 0 τ) :=
      integrable_mixturePowF_comp hα hq1 (by fun_prop)
        (fun z => by positivity)
    have hfint : Integrable (fun z => m * Real.exp (z - (τ:ℝ)/2)) (gaussianReal 0 τ) := by
      have heq2 : ∀ z : ℝ, m * Real.exp (z - (τ:ℝ)/2)
          = Real.exp (y - (β1:ℝ)/2 - (τ:ℝ)/2) * Real.exp (1 * z) := by
        intro z
        rw [hmdef, one_mul]
        simp only [← Real.exp_add]
        ring_nf
      simp_rw [heq2]
      exact (integrable_exp_mul_gaussianReal 1).const_mul _
    have hfmem : ∀ᵐ z ∂(gaussianReal (0:ℝ) τ), m * Real.exp (z - (τ:ℝ)/2) ∈ Set.Ici (0:ℝ) :=
      ae_of_all _ fun z => by rw [Set.mem_Ici]; positivity
    have hjensen := (convexOn_mixturePowF hα hq1).map_integral_le
      (f := fun z => m * Real.exp (z - (τ:ℝ)/2))
      (continuousOn_mixturePowF hq1) isClosed_Ici hfmem hfint hz'
    have hintm : ∫ z, m * Real.exp (z - (τ:ℝ)/2) ∂(gaussianReal (0:ℝ) τ) = m := by
      rw [integral_const_mul, integral_exp_sub_half_gaussianReal τ, mul_one]
    rw [hintm] at hjensen
    calc mixturePowF α q m
        ≤ ∫ z, mixturePowF α q (m * Real.exp (z - (τ:ℝ)/2)) ∂(gaussianReal 0 τ) := hjensen
      _ = ∫ z, mixturePowF α q (Real.exp (y + z - (β2:ℝ)/2)) ∂(gaussianReal 0 τ) := by
          apply integral_congr_ae; filter_upwards with z; rw [hexpsplit]
  have hmono := integral_mono_ae
    (integrable_mixturePowF_comp (μ := gaussianReal 0 β1) hα hq1 (by fun_prop)
      (fun y => (Real.exp_pos _).le))
    (hjoint'.integral_prod_left) hpointwise
  rw [hF2eq, hFubini]
  exact hmono

/-- **Change of variables** for the reversed integrand: the `Δ`-dependence is through
    `β = Δ²/v`. -/
lemma integral_mixturePowF_gaussLR_eq_expShift {α : ℝ} (hα : 1 ≤ α) {q : ℝ≥0}
    (hq1 : (q:ℝ) < 1) {μ₀ Δ : ℝ} {v : ℝ≥0} (hv : v ≠ 0) (β : ℝ≥0) (hβR : (β:ℝ) = Δ^2/v) :
    ∫ x, mixturePowF α q (gaussLR μ₀ Δ v x) ∂(gaussianReal μ₀ v)
      = ∫ y, mixturePowF α q (Real.exp (y - (β:ℝ)/2)) ∂(gaussianReal 0 β) := by
  have hvR : (v:ℝ) ≠ 0 := by exact_mod_cast hv
  set c : ℝ := Δ / v with hc
  have hβeq : (⟨c^2, sq_nonneg _⟩ * v : ℝ≥0) = β := by
    have hcoe : ((⟨c^2, sq_nonneg _⟩ * v : ℝ≥0) : ℝ) = c^2 * v := rfl
    apply NNReal.coe_injective
    rw [hcoe, hβR, hc]
    field_simp
  have hmap1 : (gaussianReal μ₀ v).map (· + (-μ₀)) = gaussianReal 0 v := by
    rw [gaussianReal_map_add_const]; ring_nf
  have hmap2 : (gaussianReal (0:ℝ) v).map (c * ·) = gaussianReal 0 β := by
    rw [gaussianReal_map_const_mul, mul_zero]
    exact congrArg (gaussianReal 0) hβeq
  have hmapfull : (gaussianReal μ₀ v).map ((c * ·) ∘ (· + (-μ₀))) = gaussianReal 0 β := by
    rw [← Measure.map_map (by fun_prop) (by fun_prop), hmap1, hmap2]
  have hfun : ((c * ·) ∘ (fun x : ℝ => x + (-μ₀))) = (fun x : ℝ => c * (x - μ₀)) := by
    funext x; show c * (x + (-μ₀)) = c * (x - μ₀); ring
  rw [hfun] at hmapfull
  have hg : ∀ x : ℝ, c * (x - μ₀) - (β:ℝ)/2 = Δ * (x - μ₀) / v - Δ ^ 2 / (2 * v) := by
    intro x
    rw [hβR, hc]
    field_simp
  have hmeasg : AEStronglyMeasurable
      (fun y => mixturePowF α q (Real.exp (y - (β:ℝ)/2)))
      ((gaussianReal μ₀ v).map (fun x => c * (x - μ₀))) := by
    rw [hmapfull]
    exact (integrable_mixturePowF_comp (μ := gaussianReal 0 β) hα hq1 (by fun_prop)
      (fun y => (Real.exp_pos _).le)).aestronglyMeasurable
  rw [← hmapfull, integral_map (by fun_prop) hmeasg]
  apply integral_congr_ae
  filter_upwards with x
  congr 2
  unfold gaussLR
  rw [← hg x]

/-! ## The reversed scalar case -/

/-- `H_α(𝒩(μ₀,v) ‖ (1-q)𝒩(μ₀,v) + q𝒩(μ₀+Δ,v)) = E_{ν₀}[((1-q)+q·L)^{1-α}]`. -/
theorem hellingerIntegral_flip_sgMixture_real {α : ℝ} (hα : 1 < α) {μ₀ Δ : ℝ} {v : ℝ≥0} (hv : v ≠ 0)
    {q : ℝ≥0} (hq1 : (q:ℝ) < 1) :
    hellingerIntegral α (gaussianReal μ₀ v)
        ((1 - (q : ℝ≥0∞)) • gaussianReal μ₀ v + (q : ℝ≥0∞) • gaussianReal (μ₀ + Δ) v)
      = ENNReal.ofReal
          (∫ x, mixturePowF α q (gaussLR μ₀ Δ v x) ∂(gaussianReal μ₀ v)) := by
  have hac : gaussianReal (μ₀ + Δ) v ≪ gaussianReal μ₀ v :=
    (gaussianReal_absolutelyContinuous _ hv).trans (gaussianReal_absolutelyContinuous' _ hv)
  have hqE : (q : ℝ≥0∞) < 1 := by
    rw [show (1 : ℝ≥0∞) = ((1 : ℝ≥0) : ℝ≥0∞) from rfl, ENNReal.coe_lt_coe]
    exact_mod_cast hq1
  rw [hellingerIntegral_flip_mixture_real_lintegral hα hqE _ _ hac,
    lintegral_congr_ae (gaussianReal_rnDeriv_eq_gaussLR hv |>.mono fun x hx => by rw [hx])]
  have hqR : (0:ℝ) ≤ (q:ℝ) := NNReal.coe_nonneg q
  have hpt : ∀ x, ((1 - (q : ℝ≥0∞)) + (q : ℝ≥0∞) * ENNReal.ofReal (gaussLR μ₀ Δ v x)) ^ (1 - α)
      = ENNReal.ofReal (mixturePowF α q (gaussLR μ₀ Δ v x)) := by
    intro x
    have hLpos : (0:ℝ) < gaussLR μ₀ Δ v x := Real.exp_pos _
    have e1 : ENNReal.ofReal (1 - (q:ℝ)) = 1 - (q:ℝ≥0∞) := by
      rw [ENNReal.ofReal_sub _ hqR, ENNReal.ofReal_one, ENNReal.ofReal_coe_nnreal]
    have e2 : ENNReal.ofReal ((q:ℝ) * gaussLR μ₀ Δ v x)
        = (q:ℝ≥0∞) * ENNReal.ofReal (gaussLR μ₀ Δ v x) := by
      rw [ENNReal.ofReal_mul hqR, ENNReal.ofReal_coe_nnreal]
    have e3 : ENNReal.ofReal ((1 - (q:ℝ)) + (q:ℝ) * gaussLR μ₀ Δ v x)
        = (1 - (q:ℝ≥0∞)) + (q:ℝ≥0∞) * ENNReal.ofReal (gaussLR μ₀ Δ v x) := by
      rw [ENNReal.ofReal_add (by linarith) (mul_nonneg hqR hLpos.le), e1, e2]
    rw [← e3, ENNReal.ofReal_rpow_of_pos (mixturePowF_base_pos hq1 hLpos.le)]
    rfl
  simp_rw [hpt]
  have hintfun : Integrable (fun x => mixturePowF α q (gaussLR μ₀ Δ v x)) (gaussianReal μ₀ v) :=
    integrable_mixturePowF_comp hα.le hq1 (by fun_prop)
      (fun x => (Real.exp_pos _).le)
  have hnn' : 0 ≤ᵐ[gaussianReal μ₀ v] fun x => mixturePowF α q (gaussLR μ₀ Δ v x) :=
    ae_of_all _ fun x => mixturePowF_nonneg hq1 (Real.exp_pos _).le
  exact (ofReal_integral_eq_lintegral_ofReal hintfun hnn').symm

/-- **Monotonicity in the sensitivity** `|Δ|`, reversed order. -/
theorem hellingerIntegral_flip_sgMixture_real_mono {α : ℝ} (hα : 1 < α) {μ₀ : ℝ} {v : ℝ≥0} (hv : v ≠ 0)
    {q : ℝ≥0} (hq1 : (q:ℝ) < 1) {Δ1 Δ2 : ℝ} (hΔ : |Δ1| ≤ |Δ2|) :
    hellingerIntegral α (gaussianReal μ₀ v)
        ((1 - (q:ℝ≥0∞)) • gaussianReal μ₀ v + (q:ℝ≥0∞) • gaussianReal (μ₀ + Δ1) v)
      ≤ hellingerIntegral α (gaussianReal μ₀ v)
        ((1 - (q:ℝ≥0∞)) • gaussianReal μ₀ v + (q:ℝ≥0∞) • gaussianReal (μ₀ + Δ2) v) := by
  have hvR : (0:ℝ) < (v:ℝ) := by exact_mod_cast hv.bot_lt
  set β1 : ℝ≥0 := ⟨Δ1^2/(v:ℝ), by positivity⟩ with hβ1def
  set β2 : ℝ≥0 := ⟨Δ2^2/(v:ℝ), by positivity⟩ with hβ2def
  have hβ1R : (β1:ℝ) = Δ1^2/v := rfl
  have hβ2R : (β2:ℝ) = Δ2^2/v := rfl
  have hsq : Δ1^2 ≤ Δ2^2 := by
    rw [← sq_abs Δ1, ← sq_abs Δ2]
    exact pow_le_pow_left₀ (abs_nonneg _) hΔ 2
  have hββ : β1 ≤ β2 := by
    rw [← NNReal.coe_le_coe, hβ1R, hβ2R]
    exact div_le_div_of_nonneg_right hsq hvR.le
  rw [hellingerIntegral_flip_sgMixture_real hα hv hq1, hellingerIntegral_flip_sgMixture_real hα hv hq1,
    integral_mixturePowF_gaussLR_eq_expShift hα.le hq1 hv β1 hβ1R,
    integral_mixturePowF_gaussLR_eq_expShift hα.le hq1 hv β2 hβ2R]
  exact ENNReal.ofReal_le_ofReal (mixturePowF_integral_mono_variance hα.le hq1 hββ)

/-! ## Translation invariance and the vector reduction -/

/-- **Translation invariance** in the base point `μ₀`, reversed order. -/
theorem hellingerIntegral_flip_sgMixture_real_translation_invariant {α : ℝ} (hα : 1 < α) {μ₀ μ₀' Δ : ℝ}
    {v : ℝ≥0} {q : ℝ≥0} (hq1 : (q:ℝ) < 1) :
    hellingerIntegral α (gaussianReal μ₀ v)
        ((1 - (q:ℝ≥0∞)) • gaussianReal μ₀ v + (q:ℝ≥0∞) • gaussianReal (μ₀ + Δ) v)
      = hellingerIntegral α (gaussianReal μ₀' v)
        ((1 - (q:ℝ≥0∞)) • gaussianReal μ₀' v + (q:ℝ≥0∞) • gaussianReal (μ₀' + Δ) v) := by
  have hqE : (q : ℝ≥0∞) < 1 := by
    rw [show (1 : ℝ≥0∞) = ((1 : ℝ≥0) : ℝ≥0∞) from rfl, ENNReal.coe_lt_coe]
    exact_mod_cast hq1
  set e : ℝ ≃ᵐ ℝ := (Homeomorph.addRight (μ₀' - μ₀)).toMeasurableEquiv with he
  have hac : gaussianReal μ₀ v
      ≪ (1 - (q:ℝ≥0∞)) • gaussianReal μ₀ v + (q:ℝ≥0∞) • gaussianReal (μ₀ + Δ) v :=
    ac_mixture_base hqE _ _
  have : IsFiniteMeasure
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

variable {d : ℕ}

open scoped RealInnerProductSpace in
set_option maxHeartbeats 4000000 in
/-- **Dimension reduction, reversed**: the vector Hellinger integral equals the scalar one at
    sensitivity `‖Δ‖`. -/
theorem hellingerIntegral_flip_sgMixtureE_eq_scalar {α : ℝ} (hα : 1 < α) (u Δ : EuclideanSpace ℝ (Fin d))
    (hΔ : Δ ≠ 0) (v : ℝ≥0) (hv : v ≠ 0) {q : ℝ≥0} (hq1 : (q:ℝ) < 1) :
    hellingerIntegral α (gaussE u v) ((1 - (q:ℝ≥0∞)) • gaussE u v + (q:ℝ≥0∞) • gaussE (u + Δ) v)
      = hellingerIntegral α (gaussianReal (0:ℝ) v)
          ((1 - (q:ℝ≥0∞)) • gaussianReal (0:ℝ) v + (q:ℝ≥0∞) • gaussianReal (‖Δ‖:ℝ) v) := by
  have hqE : (q : ℝ≥0∞) < 1 := by
    rw [show (1 : ℝ≥0∞) = ((1 : ℝ≥0) : ℝ≥0∞) from rfl, ENNReal.coe_lt_coe]
    exact_mod_cast hq1
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
  -- the pure measure is dominated by the mixture, coordinatewise and tensorized
  have hacpt : ∀ i : Fin (n+1), gaussianReal (coeffsΔ i) v ≪ gaussianReal (coeffs i) v := by
    intro i
    rcases eq_or_ne i 0 with rfl | hi
    · exact (gaussianReal_absolutelyContinuous _ hv).trans (gaussianReal_absolutelyContinuous' _ hv)
    · rw [hcoeffsΔdef, Function.update_of_ne hi]
  have hac : Measure.pi (fun i => gaussianReal (coeffs i) v)
      ≪ (1 - (q:ℝ≥0∞)) • Measure.pi (fun i => gaussianReal (coeffs i) v)
        + (q:ℝ≥0∞) • Measure.pi (fun i => gaussianReal (coeffsΔ i) v) :=
    ac_mixture_base hqE _ _
  have : IsFiniteMeasure ((1 - (q:ℝ≥0∞)) • Measure.pi (fun i => gaussianReal (coeffs i) v)
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
  have hac0 : gaussianReal (coeffs 0) v
      ≪ (1 - (q:ℝ≥0∞)) • gaussianReal (coeffs 0) v + (q:ℝ≥0∞) • gaussianReal (coeffsΔ 0) v :=
    ac_mixture_base hqE _ _
  have : IsFiniteMeasure ((1 - (q:ℝ≥0∞)) • gaussianReal (coeffs 0) v
      + (q:ℝ≥0∞) • gaussianReal (coeffsΔ 0) v) := by
    constructor
    simp only [Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      measure_univ, mul_one]
    exact ENNReal.add_lt_top.2 ⟨lt_of_le_of_lt tsub_le_self one_lt_top, ENNReal.coe_lt_top⟩
  rw [hellingerIntegral_prod hα _ _ _ _ hac0 Measure.AbsolutelyContinuous.rfl,
    hellingerIntegral_self_prob, mul_one, hcoeffsΔ0]
  simpa using
    hellingerIntegral_flip_sgMixture_real_translation_invariant (μ₀ := coeffs 0) (μ₀' := 0) (Δ := ‖Δ‖)
      hα hq1

/-! ## The budget -/

/-- **`Λ_α(q, s, v)`**: the Hellinger integral of `𝒩(0,v)` against
    `(1-q)·𝒩(0,v) + q·𝒩(s,v)`. -/
noncomputable def mixFlipBudgetE (q : ℝ≥0) (s : ℝ) (v : ℝ≥0) (α : ℝ) : ℝ≥0∞ :=
  hellingerIntegral α (gaussianReal (0:ℝ) v)
    ((1 - (q:ℝ≥0∞)) • gaussianReal (0:ℝ) v + (q:ℝ≥0∞) • gaussianReal s v)

/-- `Λ_α` is finite: the reversed integrand is bounded by `(1-q)^{1-α}`. -/
lemma mixFlipBudgetE_ne_top {α : ℝ} (hα : 1 < α) {q : ℝ≥0} (hq1 : (q:ℝ) < 1) {v : ℝ≥0}
    (hv : v ≠ 0) (s : ℝ) : mixFlipBudgetE q s v α ≠ ⊤ := by
  rw [mixFlipBudgetE, show s = 0 + s by rw [zero_add], hellingerIntegral_flip_sgMixture_real hα hv hq1]
  exact ENNReal.ofReal_ne_top

/-- **The reversed vector subsampled Gaussian at the budget**: at a displacement of norm at
    most `s`, the Hellinger integral is at most `Λ_α(q, s, v)`, for `q < 1`. -/
theorem hellingerIntegral_flip_sgMixtureE_le_budget_of_le {α : ℝ} (hα : 1 < α)
    (u Δ : EuclideanSpace ℝ (Fin d)) (v : ℝ≥0) (hv : v ≠ 0) {q : ℝ≥0} (hq1 : (q:ℝ) < 1)
    {s : ℝ} (hΔ : ‖Δ‖ ≤ s) :
    hellingerIntegral α (gaussE u v) ((1 - (q:ℝ≥0∞)) • gaussE u v + (q:ℝ≥0∞) • gaussE (u + Δ) v)
      ≤ mixFlipBudgetE q s v α := by
  have hs : 0 ≤ s := le_trans (norm_nonneg Δ) hΔ
  have hq1ENN : (q:ℝ≥0∞) ≤ 1 := by exact_mod_cast hq1.le
  have hbudget : mixFlipBudgetE q s v α
      = hellingerIntegral α (gaussianReal (0:ℝ) v)
        ((1 - (q:ℝ≥0∞)) • gaussianReal (0:ℝ) v + (q:ℝ≥0∞) • gaussianReal (0 + s) v) := by
    rw [mixFlipBudgetE, zero_add]
  rcases eq_or_ne Δ 0 with rfl | hΔ0
  · rw [add_zero]
    have h1 : (1 - (q:ℝ≥0∞)) • gaussE u v + (q:ℝ≥0∞) • gaussE u v = gaussE u v := by
      rw [← add_smul, tsub_add_cancel_of_le hq1ENN, one_smul]
    rw [h1, hellingerIntegral_self_prob, hbudget]
    calc (1:ℝ≥0∞)
        = hellingerIntegral α (gaussianReal (0:ℝ) v)
            ((1 - (q:ℝ≥0∞)) • gaussianReal (0:ℝ) v + (q:ℝ≥0∞) • gaussianReal (0 + 0) v) := by
          rw [add_zero, ← add_smul, tsub_add_cancel_of_le hq1ENN, one_smul, hellingerIntegral_self_prob]
      _ ≤ hellingerIntegral α (gaussianReal (0:ℝ) v)
            ((1 - (q:ℝ≥0∞)) • gaussianReal (0:ℝ) v + (q:ℝ≥0∞) • gaussianReal (0 + s) v) :=
          hellingerIntegral_flip_sgMixture_real_mono hα hv hq1 (by rw [abs_zero]; exact abs_nonneg s)
  · rw [hellingerIntegral_flip_sgMixtureE_eq_scalar hα u Δ hΔ0 v hv hq1, hbudget]
    have := hellingerIntegral_flip_sgMixture_real_mono (μ₀ := (0:ℝ)) hα hv hq1 (Δ1 := ‖Δ‖) (Δ2 := s)
      (by rw [abs_of_nonneg (norm_nonneg Δ), abs_of_nonneg hs]; exact hΔ)
    simpa using this

/-- `1 ≤ Λ_α`. -/
lemma one_le_mixFlipBudgetE {α : ℝ} (hα : 1 < α) {q : ℝ≥0} (hq1 : (q:ℝ) < 1) {v : ℝ≥0}
    (hv : v ≠ 0) {s : ℝ} (hs : 0 ≤ s) : 1 ≤ mixFlipBudgetE q s v α := by
  have h0 := hellingerIntegral_flip_sgMixtureE_le_budget_of_le (d := 1) hα 0 0 v hv hq1
    (s := s) (by simpa using hs)
  have hq1ENN : (q:ℝ≥0∞) ≤ 1 := by exact_mod_cast hq1.le
  rw [add_zero, ← add_smul, tsub_add_cancel_of_le hq1ENN, one_smul, hellingerIntegral_self_prob] at h0
  exact h0

/-- `Λ_α ≠ 0`. -/
lemma mixFlipBudgetE_ne_zero {α : ℝ} (hα : 1 < α) {q : ℝ≥0} (hq1 : (q:ℝ) < 1) {v : ℝ≥0}
    (hv : v ≠ 0) {s : ℝ} (hs : 0 ≤ s) : mixFlipBudgetE q s v α ≠ 0 :=
  ne_of_gt (lt_of_lt_of_le zero_lt_one (one_le_mixFlipBudgetE hα hq1 hv hs))

end Continuous
