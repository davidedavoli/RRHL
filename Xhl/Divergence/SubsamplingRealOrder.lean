import Mathlib.Analysis.Analytic.Binomial
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Probability.Moments.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.Group.Convolution
import Xhl.Divergence.Gaussian
import Xhl.Divergence.RingChooseSummable

/-!
# The subsampled Gaussian at every real order

The Hellinger integral of the `q`-subsampled Gaussian mixture `(1−q)·𝒩(μ₀,v) + q·𝒩(μ₀+Δ,v)`
against `𝒩(μ₀,v)`, at every real `α > 1`:

1. `hellingerIntegral_sgMixture_real` — it is `E_{ν₀}[((1−q)+q·L)^α]`, `L` the likelihood ratio;
2. `hellingerIntegral_sgMixture_real_closedForm_unconditional` — split at `z₁`, where
   `(1−q)·ν₀ = q·ν₁`, and expanded below and above `z₁` as generalized binomial series whose
   terms are `exp(β(β−1)Δ²/2v) · 𝒩(μ₀+βΔ, v)(half-line)` (Mironov et al., §3.3);
3. `hellingerIntegral_sgMixture_real_mono` — monotone in `|Δ|`, by a convex-order argument
   (Proposition A.25, item 2).

`SubsamplingRealOrderE.lean` lifts the result to the isotropic vector Gaussian.
-/

open MeasureTheory ProbabilityTheory ENNReal Real
open scoped NNReal

namespace Continuous

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The Hellinger integral of a `q`-mixture is the `ν`-integral of `((1-q)+q·L)^α`, `L` the
    likelihood ratio, at any real `α > 1`. -/
theorem hellingerIntegral_mixture_real_lintegral {α : ℝ} (hα : 1 < α) (q : ℝ≥0∞) (hqtop : q ≠ ⊤)
    (ν ν' : Measure Ω) [IsFiniteMeasure ν] [IsFiniteMeasure ν'] (hac : ν' ≪ ν) :
    hellingerIntegral α ((1 - q) • ν + q • ν') ν
      = ∫⁻ x, ((1 - q) + q * ν'.rnDeriv ν x) ^ α ∂ν := by
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
  haveI : IsFiniteMeasure (ν.withDensity (fun x => (1 - q) + q * L x)) := by
    refine isFiniteMeasure_withDensity ?_
    rw [lintegral_add_left measurable_const, lintegral_const, lintegral_const_mul _ hL, hLdef,
      Measure.lintegral_rnDeriv hac]
    refine ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ?_ (measure_ne_top ν _),
      ENNReal.mul_ne_top hqtop (measure_ne_top ν' _)⟩
    exact (tsub_le_self.trans_lt one_lt_top).ne
  haveI : IsFiniteMeasure ((1 - q) • ν + q • ν') := by rw [hmixwd]; infer_instance
  have hmixac : (1 - q) • ν + q • ν' ≪ ν := by
    rw [hmixwd]; exact withDensity_absolutelyContinuous _ _
  have hmixrn : ((1 - q) • ν + q • ν').rnDeriv ν
      =ᵐ[ν] fun x => (1 - q) + q * L x := by
    rw [hmixwd]; exact Measure.rnDeriv_withDensity _ hf
  rw [hellingerIntegral_eq_lintegral_rnDeriv _ _ hmixac,
    lintegral_congr_ae (hmixrn.mono fun x hx => by rw [hx])]

/-- The Gaussian likelihood ratio `L(x) = pdf(μ₀+Δ,v)(x) / pdf(μ₀,v)(x)`, in closed form. -/
noncomputable def gaussLR (μ₀ Δ : ℝ) (v : ℝ≥0) (x : ℝ) : ℝ :=
  Real.exp (Δ * (x - μ₀) / v - Δ ^ 2 / (2 * v))

lemma gaussLR_eq_pdf_ratio {μ₀ Δ : ℝ} {v : ℝ≥0} (hv : v ≠ 0) (x : ℝ) :
    gaussLR μ₀ Δ v x = gaussianPDFReal (μ₀ + Δ) v x / gaussianPDFReal μ₀ v x := by
  have hvR : (0 : ℝ) < (v : ℝ) := by exact_mod_cast hv.bot_lt
  rw [gaussianPDFReal_def, gaussianPDFReal_def, gaussLR,
    mul_div_mul_left _ _ (by positivity : (√(2 * π * (v : ℝ)))⁻¹ ≠ 0), ← Real.exp_sub]
  congr 1
  field_simp
  ring

lemma measurable_gaussLR {μ₀ Δ : ℝ} {v : ℝ≥0} : Measurable (gaussLR μ₀ Δ v) := by
  unfold gaussLR; fun_prop

/-- The Gaussian likelihood ratio `rnDeriv` is `gaussLR`, a.e. against the base Gaussian. -/
lemma gaussianReal_rnDeriv_eq_gaussLR {μ₀ Δ : ℝ} {v : ℝ≥0} (hv : v ≠ 0) :
    (gaussianReal (μ₀ + Δ) v).rnDeriv (gaussianReal μ₀ v)
      =ᵐ[gaussianReal μ₀ v] fun x => ENNReal.ofReal (gaussLR μ₀ Δ v x) := by
  have hac : gaussianReal (μ₀ + Δ) v ≪ gaussianReal μ₀ v :=
    (gaussianReal_absolutelyContinuous _ hv).trans (gaussianReal_absolutelyContinuous' _ hv)
  have hν₀vol : gaussianReal μ₀ v ≪ volume := gaussianReal_absolutelyContinuous μ₀ hv
  have hchain : (gaussianReal (μ₀ + Δ) v).rnDeriv (gaussianReal μ₀ v)
      * (gaussianReal μ₀ v).rnDeriv volume
      =ᵐ[volume] (gaussianReal (μ₀ + Δ) v).rnDeriv volume :=
    Measure.rnDeriv_mul_rnDeriv (κ := volume) hac
  have hrn0 : (gaussianReal μ₀ v).rnDeriv volume =ᵐ[volume] gaussianPDF μ₀ v :=
    rnDeriv_gaussianReal μ₀ v
  have hrn1 : (gaussianReal (μ₀ + Δ) v).rnDeriv volume =ᵐ[volume] gaussianPDF (μ₀ + Δ) v :=
    rnDeriv_gaussianReal (μ₀ + Δ) v
  have hcombined : ∀ᵐ x ∂volume,
      (gaussianReal (μ₀ + Δ) v).rnDeriv (gaussianReal μ₀ v) x
        = ENNReal.ofReal (gaussLR μ₀ Δ v x) := by
    filter_upwards [hchain, hrn0, hrn1] with x hx h0 h1
    simp only [Pi.mul_apply] at hx
    have hp0pos : 0 < gaussianPDFReal μ₀ v x := gaussianPDFReal_pos μ₀ v x hv
    have hp0ne : gaussianPDF μ₀ v x ≠ 0 := (ENNReal.ofReal_pos.mpr hp0pos).ne'
    have hp0top : gaussianPDF μ₀ v x ≠ ⊤ := ENNReal.ofReal_ne_top
    rw [h0] at hx; rw [h1] at hx
    have : (gaussianReal (μ₀ + Δ) v).rnDeriv (gaussianReal μ₀ v) x
        = gaussianPDF (μ₀ + Δ) v x / gaussianPDF μ₀ v x := by
      rw [ENNReal.eq_div_iff hp0ne hp0top, mul_comm]; exact hx
    rw [this, gaussianPDF, gaussianPDF, gaussLR_eq_pdf_ratio hv x,
      ENNReal.ofReal_div_of_pos hp0pos]
  exact hν₀vol.ae_eq hcombined

/-- **The mixture density is integrable against `ν₀`**, dominated by `2^α·(1+L^α)`. -/
lemma integrable_mixture_pow {α : ℝ} (hα : 1 < α) {μ₀ Δ : ℝ} {v : ℝ≥0} (hv : v ≠ 0)
    {q : ℝ≥0} (hq : q ≤ 1) :
    Integrable (fun x => ((1 - (q : ℝ)) + (q : ℝ) * gaussLR μ₀ Δ v x) ^ α)
      (gaussianReal μ₀ v) := by
  have hac : gaussianReal (μ₀ + Δ) v ≪ gaussianReal μ₀ v :=
    (gaussianReal_absolutelyContinuous _ hv).trans (gaussianReal_absolutelyContinuous' _ hv)
  have hα0 : (0 : ℝ) < α := lt_trans one_pos hα
  have hnonneg : ∀ x, 0 ≤ (1 - (q : ℝ)) + (q : ℝ) * gaussLR μ₀ Δ v x := fun x => by
    have hq1 : (q : ℝ) ≤ 1 := by exact_mod_cast hq
    have : (0:ℝ) ≤ gaussLR μ₀ Δ v x := le_of_lt (Real.exp_pos _)
    nlinarith [NNReal.coe_nonneg q]
  have hLpos : ∀ x, 0 < gaussLR μ₀ Δ v x := fun x => Real.exp_pos _
  have hgnonneg : 0 ≤ᵐ[gaussianReal μ₀ v] fun x => (gaussLR μ₀ Δ v x) ^ α :=
    ae_of_all _ fun x => Real.rpow_nonneg (hLpos x).le α
  have hgmeas : AEStronglyMeasurable (fun x => (gaussLR μ₀ Δ v x) ^ α) (gaussianReal μ₀ v) :=
    ((continuous_rpow_const hα0.le).measurable.comp measurable_gaussLR).aestronglyMeasurable
  have hgint : Integrable (fun x => (gaussLR μ₀ Δ v x) ^ α) (gaussianReal μ₀ v) := by
    refine ⟨hgmeas, (hasFiniteIntegral_iff_ofReal hgnonneg).2 ?_⟩
    have heq2 : (∫⁻ x, ENNReal.ofReal ((gaussLR μ₀ Δ v x) ^ α) ∂gaussianReal μ₀ v)
        = hellingerIntegral α (gaussianReal (μ₀ + Δ) v) (gaussianReal μ₀ v) := by
      rw [hellingerIntegral_eq_lintegral_rnDeriv _ _ hac]
      apply lintegral_congr_ae
      filter_upwards [gaussianReal_rnDeriv_eq_gaussLR hv] with x hx
      rw [hx, ENNReal.ofReal_rpow_of_pos (hLpos x)]
    rw [heq2, hellingerIntegral_gaussianReal hα (μ₀ + Δ) μ₀ hv]
    exact ENNReal.ofReal_lt_top
  have hdom : ∀ x, ((1 - (q : ℝ)) + (q : ℝ) * gaussLR μ₀ Δ v x) ^ α
      ≤ (2:ℝ) ^ α * (1 + (gaussLR μ₀ Δ v x) ^ α) := by
    intro x
    set L := gaussLR μ₀ Δ v x with hLval
    have hq1 : (q : ℝ) ≤ 1 := by exact_mod_cast hq
    have hLnn : (0:ℝ) ≤ L := (hLpos x).le
    have h1 : (1 - (q:ℝ)) + (q:ℝ) * L ≤ 1 + L := by nlinarith [NNReal.coe_nonneg q]
    have h2 : (1:ℝ) + L ≤ 2 * max 1 L := by
      rcases le_total 1 L with h | h <;> [rw [max_eq_right h]; rw [max_eq_left h]] <;> linarith
    have h3 : max 1 L ^ α ≤ 1 + L ^ α := by
      rcases le_total 1 L with h | h
      · rw [max_eq_right h]; linarith [Real.one_le_rpow h hα0.le]
      · rw [max_eq_left h, Real.one_rpow]
        have : L ^ α ≤ 1 := Real.rpow_le_one hLnn h hα0.le
        linarith [Real.rpow_nonneg hLnn α]
    have hbase1 : (0:ℝ) ≤ 1 - (q:ℝ) + (q:ℝ) * L := by nlinarith [NNReal.coe_nonneg q]
    have hbase2 : (0:ℝ) ≤ 1 + L := by linarith
    calc ((1 - (q:ℝ)) + (q:ℝ) * L) ^ α ≤ (1 + L) ^ α :=
          Real.rpow_le_rpow hbase1 h1 hα0.le
      _ ≤ (2 * max 1 L) ^ α := Real.rpow_le_rpow hbase2 h2 hα0.le
      _ = 2 ^ α * max 1 L ^ α := Real.mul_rpow (by norm_num) (le_trans zero_le_one (le_max_left _ _))
      _ ≤ 2 ^ α * (1 + L ^ α) :=
          mul_le_mul_of_nonneg_left h3 (Real.rpow_nonneg (by norm_num) α)
  have hdomint : Integrable (fun x => (2:ℝ) ^ α * (1 + (gaussLR μ₀ Δ v x) ^ α))
      (gaussianReal μ₀ v) := ((integrable_const 1).add hgint).const_mul _
  have hmeasf : AEStronglyMeasurable
      (fun x => ((1 - (q : ℝ)) + (q : ℝ) * gaussLR μ₀ Δ v x) ^ α) (gaussianReal μ₀ v) :=
    ((continuous_rpow_const hα0.le).measurable.comp
        (measurable_const.add (measurable_const.mul measurable_gaussLR))).aestronglyMeasurable
  refine Integrable.mono' hdomint hmeasf (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hnonneg x) α)]
  exact hdom x


/-- The Hellinger integral of the subsampled Gaussian mixture against the base Gaussian, at any
    real `α > 1`, as the Bochner integral `E_{ν₀}[((1-q)+q·L)^α]`. -/
theorem hellingerIntegral_sgMixture_real {α : ℝ} (hα : 1 < α) {μ₀ Δ : ℝ} {v : ℝ≥0} (hv : v ≠ 0)
    (q : ℝ≥0) (hq : q ≤ 1) :
    hellingerIntegral α ((1 - (q : ℝ≥0∞)) • gaussianReal μ₀ v + (q : ℝ≥0∞) • gaussianReal (μ₀ + Δ) v)
        (gaussianReal μ₀ v)
      = ENNReal.ofReal
          (∫ x, ((1 - (q : ℝ)) + (q : ℝ) * gaussLR μ₀ Δ v x) ^ α ∂(gaussianReal μ₀ v)) := by
  have hac : gaussianReal (μ₀ + Δ) v ≪ gaussianReal μ₀ v :=
    (gaussianReal_absolutelyContinuous _ hv).trans (gaussianReal_absolutelyContinuous' _ hv)
  have hqtop : (q : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  rw [hellingerIntegral_mixture_real_lintegral hα (q : ℝ≥0∞) hqtop _ _ hac,
    lintegral_congr_ae (gaussianReal_rnDeriv_eq_gaussLR hv |>.mono fun x hx => by rw [hx])]
  have hα0 : (0:ℝ) < α := lt_trans one_pos hα
  have hnonneg : ∀ x, 0 ≤ (1 - (q : ℝ)) + (q : ℝ) * gaussLR μ₀ Δ v x := fun x => by
    have hq1 : (q : ℝ) ≤ 1 := by exact_mod_cast hq
    have : (0:ℝ) ≤ gaussLR μ₀ Δ v x := le_of_lt (Real.exp_pos _)
    nlinarith [NNReal.coe_nonneg q]
  have hpt : ∀ x, ((1 - (q : ℝ≥0∞)) + (q : ℝ≥0∞) * ENNReal.ofReal (gaussLR μ₀ Δ v x)) ^ α
      = ENNReal.ofReal (((1 - (q : ℝ)) + (q : ℝ) * gaussLR μ₀ Δ v x) ^ α) := by
    intro x
    have hqR : (0:ℝ) ≤ (q:ℝ) := NNReal.coe_nonneg q
    have hq1R : (q:ℝ) ≤ 1 := by exact_mod_cast hq
    have e1 : ENNReal.ofReal (1 - (q:ℝ)) = 1 - (q:ℝ≥0∞) := by
      rw [ENNReal.ofReal_sub _ hqR, ENNReal.ofReal_one, ENNReal.ofReal_coe_nnreal]
    have e2 : ENNReal.ofReal ((q:ℝ) * gaussLR μ₀ Δ v x)
        = (q:ℝ≥0∞) * ENNReal.ofReal (gaussLR μ₀ Δ v x) := by
      rw [ENNReal.ofReal_mul hqR, ENNReal.ofReal_coe_nnreal]
    have hLnn0 : (0:ℝ) ≤ gaussLR μ₀ Δ v x := (Real.exp_pos _).le
    have e3 : ENNReal.ofReal ((1 - (q:ℝ)) + (q:ℝ) * gaussLR μ₀ Δ v x)
        = (1 - (q:ℝ≥0∞)) + (q:ℝ≥0∞) * ENNReal.ofReal (gaussLR μ₀ Δ v x) := by
      rw [ENNReal.ofReal_add (by linarith) (mul_nonneg hqR hLnn0), e1, e2]
    rw [← e3, ENNReal.ofReal_rpow_of_nonneg (hnonneg x) hα0.le]
  simp_rw [hpt]
  have hintfun := integrable_mixture_pow (μ₀ := μ₀) (Δ := Δ) hα hv hq
  have hnn' : 0 ≤ᵐ[gaussianReal μ₀ v]
      fun x => ((1 - (q : ℝ)) + (q : ℝ) * gaussLR μ₀ Δ v x) ^ α :=
    ae_of_all _ fun x => Real.rpow_nonneg (hnonneg x) α
  exact (ofReal_integral_eq_lintegral_ofReal hintfun hnn').symm

/-! ## The `z₁` split

Below `z₁` the binomial series in `qL/(1-q)` converges, above it the series in `(1-q)/(qL)`. -/

/-- The split point: `gaussLR μ₀ Δ v z₁ = (1-q)/q`, i.e. `(1-q)·ν₀(z₁) = q·ν₁(z₁)`. -/
noncomputable def z₁ (μ₀ Δ : ℝ) (v : ℝ≥0) (q : ℝ≥0) : ℝ :=
  μ₀ + Δ / 2 + (v : ℝ) / Δ * Real.log ((1 - (q : ℝ)) / q)

lemma gaussLR_z₁ {μ₀ Δ : ℝ} (hΔ : Δ ≠ 0) {v : ℝ≥0} (hv : v ≠ 0) {q : ℝ≥0}
    (hq0 : 0 < q) (hq1 : (q : ℝ) < 1) :
    gaussLR μ₀ Δ v (z₁ μ₀ Δ v q) = (1 - (q : ℝ)) / q := by
  have hvR : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  have hqR : (0 : ℝ) < (q : ℝ) := hq0
  have hpos : (0 : ℝ) < (1 - (q : ℝ)) / q := div_pos (by linarith) hqR
  unfold gaussLR z₁
  rw [show Δ * (μ₀ + Δ / 2 + (v : ℝ) / Δ * Real.log ((1 - (q : ℝ)) / q) - μ₀) / v - Δ ^ 2 / (2 * v)
      = Real.log ((1 - (q : ℝ)) / q) from by field_simp; ring]
  exact Real.exp_log hpos

/-- `gaussLR` is strictly increasing in `x` when the sensitivity `Δ` is positive. -/
lemma gaussLR_strictMono {μ₀ Δ : ℝ} (hΔ : 0 < Δ) {v : ℝ≥0} (hv : v ≠ 0) :
    StrictMono (gaussLR μ₀ Δ v) := by
  have hvR : (0 : ℝ) < (v : ℝ) := by exact_mod_cast hv.bot_lt
  intro x y hxy
  unfold gaussLR
  refine Real.exp_lt_exp.mpr ?_
  have h1 : Δ * (x - μ₀) < Δ * (y - μ₀) := by nlinarith
  have h2 : Δ * (x - μ₀) / v < Δ * (y - μ₀) / v :=
    (div_lt_div_iff_of_pos_right hvR).mpr h1
  linarith

/-- Below `z₁`: `x = qL(z)/(1-q)` satisfies `|x| < 1`. -/
lemma abs_frac_lt_one_of_lt_z₁ {μ₀ Δ : ℝ} (hΔ : 0 < Δ) {v : ℝ≥0} (hv : v ≠ 0) {q : ℝ≥0}
    (hq0 : 0 < q) (hq1 : (q : ℝ) < 1) {z : ℝ} (hz : z < z₁ μ₀ Δ v q) :
    |(q : ℝ) * gaussLR μ₀ Δ v z / (1 - (q : ℝ))| < 1 := by
  have hqR : (0 : ℝ) < (q : ℝ) := hq0
  have hL : gaussLR μ₀ Δ v z < (1 - (q : ℝ)) / q := by
    rw [← gaussLR_z₁ hΔ.ne' hv hq0 hq1]; exact gaussLR_strictMono hΔ hv hz
  have hLpos : (0 : ℝ) < gaussLR μ₀ Δ v z := Real.exp_pos _
  have h1q : (0 : ℝ) < 1 - (q : ℝ) := by linarith
  rw [abs_of_nonneg (div_nonneg (mul_nonneg hqR.le hLpos.le) h1q.le)]
  rw [div_lt_one h1q]
  calc (q : ℝ) * gaussLR μ₀ Δ v z < q * ((1 - (q : ℝ)) / q) :=
        mul_lt_mul_of_pos_left hL hqR
    _ = 1 - (q : ℝ) := by field_simp

/-- Above `z₁`: the reciprocal `y = (1-q)/(qL(z))` satisfies `|y| < 1`. -/
lemma abs_recip_lt_one_of_gt_z₁ {μ₀ Δ : ℝ} (hΔ : 0 < Δ) {v : ℝ≥0} (hv : v ≠ 0) {q : ℝ≥0}
    (hq0 : 0 < q) (hq1 : (q : ℝ) < 1) {z : ℝ} (hz : z₁ μ₀ Δ v q < z) :
    |(1 - (q : ℝ)) / ((q : ℝ) * gaussLR μ₀ Δ v z)| < 1 := by
  have hqR : (0 : ℝ) < (q : ℝ) := hq0
  have hL : (1 - (q : ℝ)) / q < gaussLR μ₀ Δ v z := by
    rw [← gaussLR_z₁ hΔ.ne' hv hq0 hq1]; exact gaussLR_strictMono hΔ hv hz
  have hLpos : (0 : ℝ) < gaussLR μ₀ Δ v z := Real.exp_pos _
  have hqLpos : (0 : ℝ) < (q : ℝ) * gaussLR μ₀ Δ v z := mul_pos hqR hLpos
  rw [abs_of_nonneg (div_nonneg (by linarith) hqLpos.le)]
  rw [div_lt_one hqLpos]
  calc (1 - (q : ℝ)) = q * ((1 - (q : ℝ)) / q) := by field_simp
    _ < q * gaussLR μ₀ Δ v z := mul_lt_mul_of_pos_left hL hqR

/-- The real-exponent binomial series, specialized to a single real point `y` with `|y| < 1`. -/
lemma hasSum_one_add_rpow {a : ℝ} {y : ℝ} (hy : |y| < 1) :
    HasSum (fun n : ℕ => Ring.choose a n * y ^ n) ((1 + y) ^ a) := by
  have hmem : y ∈ Metric.eball (0 : ℝ) 1 := by
    rw [Metric.mem_eball, edist_dist, Real.dist_eq, sub_zero,
      show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from (ENNReal.ofReal_one).symm,
      ENNReal.ofReal_lt_ofReal_iff (by norm_num)]
    exact hy
  have h := (Real.one_add_rpow_hasFPowerSeriesOnBall_zero (a := a)).hasSum hmem
  simp only [binomialSeries, smul_eq_mul] at h
  simpa [mul_comm] using h

/-- **Below `z₁`**: the pointwise binomial-series expansion of `((1-q)+qL(z))^α`. -/
lemma hasSum_pow_below_z₁ {α : ℝ} {μ₀ Δ : ℝ} (hΔ : 0 < Δ) {v : ℝ≥0} (hv : v ≠ 0) {q : ℝ≥0}
    (hq0 : 0 < q) (hq1 : (q : ℝ) < 1) {z : ℝ} (hz : z < z₁ μ₀ Δ v q) :
    HasSum (fun n : ℕ => Ring.choose α n * (1 - (q : ℝ)) ^ (α - n) * (q : ℝ) ^ n
        * gaussLR μ₀ Δ v z ^ n)
      (((1 - (q : ℝ)) + (q : ℝ) * gaussLR μ₀ Δ v z) ^ α) := by
  set x := (q : ℝ) * gaussLR μ₀ Δ v z / (1 - (q : ℝ)) with hxdef
  have hx1 : |x| < 1 := abs_frac_lt_one_of_lt_z₁ hΔ hv hq0 hq1 hz
  have h1q : (0 : ℝ) < 1 - (q : ℝ) := by linarith
  have hLnn : (0 : ℝ) ≤ gaussLR μ₀ Δ v z := (Real.exp_pos _).le
  have hnum : (0 : ℝ) ≤ (1 - (q : ℝ)) + (q : ℝ) * gaussLR μ₀ Δ v z := by positivity
  have hsum := hasSum_one_add_rpow (a := α) hx1
  have heq : (1 + x) ^ α = ((1 - (q : ℝ)) + (q : ℝ) * gaussLR μ₀ Δ v z) ^ α
      / (1 - (q : ℝ)) ^ α := by
    rw [← Real.div_rpow hnum h1q.le]
    congr 1
    rw [hxdef]; field_simp
  rw [heq] at hsum
  have hsum2 := hsum.mul_right ((1 - (q : ℝ)) ^ α)
  rw [div_mul_cancel₀ _ (by positivity : (1 - (q : ℝ)) ^ α ≠ 0)] at hsum2
  have hterm : (fun n : ℕ => Ring.choose α n * x ^ n * (1 - (q : ℝ)) ^ α)
      = fun n : ℕ => Ring.choose α n * (1 - (q : ℝ)) ^ (α - n) * (q : ℝ) ^ n
        * gaussLR μ₀ Δ v z ^ n := by
    funext n
    rw [hxdef, div_pow, Real.rpow_sub h1q, Real.rpow_natCast]
    field_simp; ring
  rwa [hterm] at hsum2

/-- **Above `z₁`**: the pointwise binomial-series expansion of `((1-q)+qL(z))^α`, in powers
    `α-k`. -/
lemma hasSum_pow_above_z₁ {α : ℝ} {μ₀ Δ : ℝ} (hΔ : 0 < Δ) {v : ℝ≥0} (hv : v ≠ 0) {q : ℝ≥0}
    (hq0 : 0 < q) (hq1 : (q : ℝ) < 1) {z : ℝ} (hz : z₁ μ₀ Δ v q < z) :
    HasSum (fun n : ℕ => Ring.choose α n * (1 - (q : ℝ)) ^ n * (q : ℝ) ^ (α - n)
        * gaussLR μ₀ Δ v z ^ (α - n))
      (((1 - (q : ℝ)) + (q : ℝ) * gaussLR μ₀ Δ v z) ^ α) := by
  set y := (1 - (q : ℝ)) / ((q : ℝ) * gaussLR μ₀ Δ v z) with hydef
  have hy1 : |y| < 1 := abs_recip_lt_one_of_gt_z₁ hΔ hv hq0 hq1 hz
  have hqR : (0 : ℝ) < (q : ℝ) := hq0
  have hLpos : (0 : ℝ) < gaussLR μ₀ Δ v z := Real.exp_pos _
  have hqLpos : (0 : ℝ) < (q : ℝ) * gaussLR μ₀ Δ v z := mul_pos hqR hLpos
  have hnum : (0 : ℝ) ≤ (1 - (q : ℝ)) + (q : ℝ) * gaussLR μ₀ Δ v z :=
    add_nonneg (by linarith) (mul_nonneg hqR.le hLpos.le)
  have hsum := hasSum_one_add_rpow (a := α) hy1
  have heq : (1 + y) ^ α = ((1 - (q : ℝ)) + (q : ℝ) * gaussLR μ₀ Δ v z) ^ α
      / ((q : ℝ) * gaussLR μ₀ Δ v z) ^ α := by
    rw [← Real.div_rpow hnum hqLpos.le]
    congr 1
    rw [hydef]; field_simp; ring
  rw [heq] at hsum
  have hsum2 := hsum.mul_right (((q : ℝ) * gaussLR μ₀ Δ v z) ^ α)
  rw [div_mul_cancel₀ _ (by positivity : ((q : ℝ) * gaussLR μ₀ Δ v z) ^ α ≠ 0)] at hsum2
  have hterm : (fun n : ℕ => Ring.choose α n * y ^ n * ((q : ℝ) * gaussLR μ₀ Δ v z) ^ α)
      = fun n : ℕ => Ring.choose α n * (1 - (q : ℝ)) ^ n * (q : ℝ) ^ (α - n)
        * gaussLR μ₀ Δ v z ^ (α - n) := by
    funext n
    have e1 : ((q : ℝ) * gaussLR μ₀ Δ v z) ^ n = (q : ℝ) ^ n * gaussLR μ₀ Δ v z ^ n := mul_pow _ _ n
    have e2 : ((q : ℝ) * gaussLR μ₀ Δ v z) ^ α = (q : ℝ) ^ α * gaussLR μ₀ Δ v z ^ α :=
      Real.mul_rpow hqR.le hLpos.le
    have hqn : (q : ℝ) ^ α / (q : ℝ) ^ n = (q : ℝ) ^ (α - n) := by
      rw [Real.rpow_sub hqR, Real.rpow_natCast]
    have hLn : gaussLR μ₀ Δ v z ^ α / gaussLR μ₀ Δ v z ^ n = gaussLR μ₀ Δ v z ^ (α - n) := by
      rw [Real.rpow_sub hLpos, Real.rpow_natCast]
    rw [hydef, div_pow, e1, e2, ← hqn, ← hLn]
    ring
  rwa [hterm] at hsum2

/-! ## Incomplete moments

`ν₀(z)·L(z)^β` is a constant multiple of a shifted Gaussian density, for any real `β`, so the
incomplete moments are `exp(β(β-1)Δ²/2v)` times the Gaussian measure of a half-line. -/

/-- Completing the square: `pdf₀(x)·L(x)^β = exp(β(β-1)Δ²/2v)·pdf_{μ₀+βΔ}(x)`, for any real `β`. -/
lemma gaussianPDFReal_mul_gaussLR_rpow {μ₀ Δ : ℝ} {v : ℝ≥0} (hv : v ≠ 0) (β : ℝ) (x : ℝ) :
    gaussianPDFReal μ₀ v x * gaussLR μ₀ Δ v x ^ β
      = Real.exp (β * (β - 1) * Δ ^ 2 / (2 * (v : ℝ))) * gaussianPDFReal (μ₀ + β * Δ) v x := by
  have hvR : (0 : ℝ) < (v : ℝ) := by exact_mod_cast hv.bot_lt
  have hexppow : gaussLR μ₀ Δ v x ^ β = Real.exp (β * (Δ * (x - μ₀) / v - Δ ^ 2 / (2 * v))) := by
    unfold gaussLR
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, mul_comm]
  have key : -(x - μ₀) ^ 2 / (2 * (v : ℝ)) + β * (Δ * (x - μ₀) / v - Δ ^ 2 / (2 * v))
      = β * (β - 1) * Δ ^ 2 / (2 * (v : ℝ)) + -(x - (μ₀ + β * Δ)) ^ 2 / (2 * (v : ℝ)) := by
    field_simp; ring
  simp only [gaussianPDFReal_def, hexppow]
  rw [mul_assoc, ← Real.exp_add, key, Real.exp_add]
  ring

/-- **The incomplete moment over `s`**: `∫_s ν₀(x)·L(x)^β dx = exp(β(β-1)Δ²/2v) · 𝒩(μ₀+βΔ,v)(s)`. -/
lemma lintegral_gaussianPDF_mul_gaussLR_rpow {μ₀ Δ : ℝ} {v : ℝ≥0} (hv : v ≠ 0)
    (β : ℝ) (s : Set ℝ) :
    ∫⁻ x in s, ENNReal.ofReal (gaussianPDFReal μ₀ v x * gaussLR μ₀ Δ v x ^ β) ∂volume
      = ENNReal.ofReal (Real.exp (β * (β - 1) * Δ ^ 2 / (2 * (v : ℝ))))
        * gaussianReal (μ₀ + β * Δ) v s := by
  have hK : (0 : ℝ) ≤ Real.exp (β * (β - 1) * Δ ^ 2 / (2 * (v : ℝ))) := (Real.exp_pos _).le
  have hpt : ∀ x, gaussianPDFReal μ₀ v x * gaussLR μ₀ Δ v x ^ β
      = Real.exp (β * (β - 1) * Δ ^ 2 / (2 * (v : ℝ))) * gaussianPDFReal (μ₀ + β * Δ) v x :=
    fun x => gaussianPDFReal_mul_gaussLR_rpow hv β x
  simp_rw [hpt, ENNReal.ofReal_mul hK]
  rw [lintegral_const_mul _ ((measurable_gaussianPDFReal (μ₀ + β * Δ) v).ennreal_ofReal)]
  congr 1
  exact (gaussianReal_apply (μ₀ + β * Δ) hv s).symm

/-! ## Gaussian tail bounds (Chernoff), for the domination of the series -/

/-- **Gaussian right-tail (Chernoff) bound**: for `Z ~ 𝒩(m,v)` and `ε ≥ m`,
`P(Z ≥ ε) ≤ exp(-(ε-m)²/2v)`. -/
lemma gaussianReal_measure_ge_le {m : ℝ} {v : ℝ≥0} (hv : v ≠ 0) {ε : ℝ} (hε : m ≤ ε) :
    (gaussianReal m v).real {x : ℝ | ε ≤ x} ≤ Real.exp (-(ε - m) ^ 2 / (2 * (v : ℝ))) := by
  have hvR : (0 : ℝ) < (v : ℝ) := by exact_mod_cast hv.bot_lt
  set t := (ε - m) / (v : ℝ) with htdef
  have ht0 : 0 ≤ t := div_nonneg (by linarith) hvR.le
  have hle := measure_ge_le_exp_mul_mgf (μ := gaussianReal m v) (X := id) (t := t) ε ht0
    (integrable_exp_mul_gaussianReal t)
  rw [show {ω : ℝ | ε ≤ id ω} = {x : ℝ | ε ≤ x} from rfl, mgf_id_gaussianReal] at hle
  have heq : Real.exp (-t * ε) * Real.exp (m * t + (v : ℝ) * t ^ 2 / 2)
      = Real.exp (-(ε - m) ^ 2 / (2 * (v : ℝ))) := by
    rw [← Real.exp_add]
    congr 1
    rw [htdef]
    field_simp
    ring
  rwa [heq] at hle

/-- **Gaussian left-tail (Chernoff) bound**: for `Z ~ 𝒩(m,v)` and `ε ≤ m`,
`P(Z ≤ ε) ≤ exp(-(m-ε)²/2v)`. -/
lemma gaussianReal_measure_le_le {m : ℝ} {v : ℝ≥0} (hv : v ≠ 0) {ε : ℝ} (hε : ε ≤ m) :
    (gaussianReal m v).real {x : ℝ | x ≤ ε} ≤ Real.exp (-(m - ε) ^ 2 / (2 * (v : ℝ))) := by
  have hvR : (0 : ℝ) < (v : ℝ) := by exact_mod_cast hv.bot_lt
  set t := (ε - m) / (v : ℝ) with htdef
  have ht0 : t ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hvR.le
  have hle := measure_le_le_exp_mul_mgf (μ := gaussianReal m v) (X := id) (t := t) ε ht0
    (integrable_exp_mul_gaussianReal t)
  rw [show {ω : ℝ | id ω ≤ ε} = {x : ℝ | x ≤ ε} from rfl, mgf_id_gaussianReal] at hle
  have heq : Real.exp (-t * ε) * Real.exp (m * t + (v : ℝ) * t ^ 2 / 2)
      = Real.exp (-(m - ε) ^ 2 / (2 * (v : ℝ))) := by
    rw [← Real.exp_add]
    congr 1
    rw [htdef]
    field_simp
    ring
  rwa [heq] at hle

/-! ## Per-term domination

Past the index where `μ₀+nΔ ≥ z₁`, the moment prefactor `exp(n(n-1)Δ²/2v)` and the Chernoff tail
combine, by the defining property of `z₁`, into `exp(-(μ₀-z₁)²/2v)·((1-q)/q)^n`; with the
coefficient `(1-q)^{α-n} q^n` the terms are then bounded by a constant times `|Ring.choose α n|`. -/

lemma measure_le_ofReal_of_real_le {m : ℝ} {v : ℝ≥0} {s : Set ℝ} {c : ℝ}
    (h : (gaussianReal m v).real s ≤ c) :
    gaussianReal m v s ≤ ENNReal.ofReal c := by
  rw [measureReal_def] at h
  calc gaussianReal m v s = ENNReal.ofReal ((gaussianReal m v s).toReal) :=
        (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    _ ≤ ENNReal.ofReal c := ENNReal.ofReal_le_ofReal h

/-- **Moment/tail bound below `z₁`**: for `μ₀+nΔ ≥ z₁`, the `n`-th incomplete moment is at most
`exp(-(μ₀-z₁)²/2v)·((1-q)/q)^n`. -/
lemma incomplete_moment_below_bound {μ₀ Δ : ℝ} (hΔ : 0 < Δ) {v : ℝ≥0} (hv : v ≠ 0) {q : ℝ≥0}
    (hq0 : 0 < q) (hq1 : (q : ℝ) < 1) (n : ℕ) (hn : z₁ μ₀ Δ v q ≤ μ₀ + (n : ℝ) * Δ) :
    ENNReal.ofReal (Real.exp ((n : ℝ) * ((n : ℝ) - 1) * Δ ^ 2 / (2 * (v : ℝ))))
        * gaussianReal (μ₀ + (n : ℝ) * Δ) v (Set.Iic (z₁ μ₀ Δ v q))
      ≤ ENNReal.ofReal (Real.exp (-(μ₀ - z₁ μ₀ Δ v q) ^ 2 / (2 * (v : ℝ)))
          * ((1 - (q : ℝ)) / q) ^ n) := by
  have hvR : (0 : ℝ) < (v : ℝ) := by exact_mod_cast hv.bot_lt
  have hqR : (0 : ℝ) < (q : ℝ) := hq0
  have hrpos : (0 : ℝ) < (1 - (q : ℝ)) / q := div_pos (by linarith) hqR
  have htail := gaussianReal_measure_le_le (m := μ₀ + (n : ℝ) * Δ) hv
    (ε := z₁ μ₀ Δ v q) hn
  have hmeasle : gaussianReal (μ₀ + (n : ℝ) * Δ) v (Set.Iic (z₁ μ₀ Δ v q))
      ≤ ENNReal.ofReal
          (Real.exp (-((μ₀ + (n : ℝ) * Δ) - z₁ μ₀ Δ v q) ^ 2 / (2 * (v : ℝ)))) :=
    measure_le_ofReal_of_real_le htail
  have hpow : ((1 - (q : ℝ)) / q) ^ n
      = Real.exp ((n : ℝ) * Real.log ((1 - (q : ℝ)) / q)) := by
    rw [Real.exp_nat_mul, Real.exp_log hrpos]
  have key : (n : ℝ) * ((n : ℝ) - 1) * Δ ^ 2 / (2 * (v : ℝ))
      + -((μ₀ + (n : ℝ) * Δ) - z₁ μ₀ Δ v q) ^ 2 / (2 * (v : ℝ))
      = -(μ₀ - z₁ μ₀ Δ v q) ^ 2 / (2 * (v : ℝ))
        + (n : ℝ) * Real.log ((1 - (q : ℝ)) / q) := by
    unfold z₁
    field_simp
    ring
  calc ENNReal.ofReal (Real.exp ((n : ℝ) * ((n : ℝ) - 1) * Δ ^ 2 / (2 * (v : ℝ))))
      * gaussianReal (μ₀ + (n : ℝ) * Δ) v (Set.Iic (z₁ μ₀ Δ v q))
      ≤ ENNReal.ofReal (Real.exp ((n : ℝ) * ((n : ℝ) - 1) * Δ ^ 2 / (2 * (v : ℝ))))
          * ENNReal.ofReal
            (Real.exp (-((μ₀ + (n : ℝ) * Δ) - z₁ μ₀ Δ v q) ^ 2 / (2 * (v : ℝ)))) :=
        mul_le_mul_right hmeasle _
    _ = ENNReal.ofReal (Real.exp ((n : ℝ) * ((n : ℝ) - 1) * Δ ^ 2 / (2 * (v : ℝ)))
          * Real.exp (-((μ₀ + (n : ℝ) * Δ) - z₁ μ₀ Δ v q) ^ 2 / (2 * (v : ℝ)))) :=
        (ENNReal.ofReal_mul (Real.exp_pos _).le).symm
    _ = ENNReal.ofReal (Real.exp (-(μ₀ - z₁ μ₀ Δ v q) ^ 2 / (2 * (v : ℝ)))
          * ((1 - (q : ℝ)) / q) ^ n) := by
        rw [← Real.exp_add, key, Real.exp_add, hpow]

/-! ## Incomplete moments as Bochner integrals against `gaussianReal μ₀ v`, at real `β` -/

/-- `gaussLR x ^ β = exp(β · affine(x))`, for any real `β`. -/
lemma gaussLR_rpow_eq_exp (μ₀ Δ : ℝ) (v : ℝ≥0) (β x : ℝ) :
    gaussLR μ₀ Δ v x ^ β = Real.exp (β * (Δ * (x - μ₀) / v - Δ ^ 2 / (2 * v))) := by
  unfold gaussLR
  rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, mul_comm]

lemma measurable_gaussLR_rpow (μ₀ Δ : ℝ) (v : ℝ≥0) (β : ℝ) :
    Measurable (fun x => gaussLR μ₀ Δ v x ^ β) := by
  simp_rw [gaussLR_rpow_eq_exp]
  fun_prop

/-- The incomplete moment `∫_s L^β dν₀` of the likelihood ratio, at every real `β`. -/
lemma lintegral_gaussLR_rpow_eq_gaussianReal {μ₀ Δ : ℝ} {v : ℝ≥0} (hv : v ≠ 0) (β : ℝ)
    {s : Set ℝ} (hs : MeasurableSet s) :
    ∫⁻ x in s, ENNReal.ofReal (gaussLR μ₀ Δ v x ^ β) ∂(gaussianReal μ₀ v)
      = ENNReal.ofReal (Real.exp (β * (β - 1) * Δ ^ 2 / (2 * (v : ℝ))))
        * gaussianReal (μ₀ + β * Δ) v s := by
  have hgmeas : Measurable (fun x => ENNReal.ofReal (gaussLR μ₀ Δ v x ^ β)) :=
    (measurable_gaussLR_rpow μ₀ Δ v β).ennreal_ofReal
  rw [gaussianReal_of_var_ne_zero μ₀ hv,
    setLIntegral_withDensity_eq_setLIntegral_mul _ (measurable_gaussianPDF μ₀ v) hgmeas hs]
  have heq : ∀ x, (gaussianPDF μ₀ v * fun x => ENNReal.ofReal (gaussLR μ₀ Δ v x ^ β)) x
      = ENNReal.ofReal (gaussianPDFReal μ₀ v x * gaussLR μ₀ Δ v x ^ β) := by
    intro x
    simp only [Pi.mul_apply, gaussianPDF]
    rw [← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _)]
  simp_rw [heq]
  exact lintegral_gaussianPDF_mul_gaussLR_rpow hv β s

lemma integrable_gaussLR_rpow {μ₀ Δ : ℝ} {v : ℝ≥0} (hv : v ≠ 0) (β : ℝ) {s : Set ℝ}
    (hs : MeasurableSet s) :
    IntegrableOn (fun x => gaussLR μ₀ Δ v x ^ β) s (gaussianReal μ₀ v) := by
  have hgLRnn : ∀ x, (0 : ℝ) ≤ gaussLR μ₀ Δ v x ^ β := fun x =>
    Real.rpow_nonneg (Real.exp_pos _).le β
  constructor
  · exact (measurable_gaussLR_rpow μ₀ Δ v β).aestronglyMeasurable.restrict
  · rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ hgLRnn),
      lintegral_gaussLR_rpow_eq_gaussianReal hv β hs]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)

/-- The incomplete moment `∫_s L^β dν₀` as a Bochner integral, at every real `β`. -/
lemma integral_gaussLR_rpow_eq {μ₀ Δ : ℝ} {v : ℝ≥0} (hv : v ≠ 0) (β : ℝ) {s : Set ℝ}
    (hs : MeasurableSet s) :
    ∫ x in s, gaussLR μ₀ Δ v x ^ β ∂(gaussianReal μ₀ v)
      = Real.exp (β * (β - 1) * Δ ^ 2 / (2 * (v : ℝ))) * (gaussianReal (μ₀ + β * Δ) v).real s := by
  have hgLRnn : ∀ x, (0 : ℝ) ≤ gaussLR μ₀ Δ v x ^ β := fun x =>
    Real.rpow_nonneg (Real.exp_pos _).le β
  have hnn : 0 ≤ᵐ[(gaussianReal μ₀ v).restrict s] fun x => gaussLR μ₀ Δ v x ^ β :=
    ae_of_all _ hgLRnn
  have hint := integrable_gaussLR_rpow (μ₀ := μ₀) (Δ := Δ) hv β hs
  have hlhs_nn : (0 : ℝ) ≤ ∫ x in s, gaussLR μ₀ Δ v x ^ β ∂(gaussianReal μ₀ v) :=
    setIntegral_nonneg hs (fun x _ => hgLRnn x)
  have hrhs_nn : (0 : ℝ) ≤ Real.exp (β * (β - 1) * Δ ^ 2 / (2 * (v : ℝ)))
      * (gaussianReal (μ₀ + β * Δ) v).real s :=
    mul_nonneg (Real.exp_pos _).le (by rw [measureReal_def]; positivity)
  rw [← ENNReal.ofReal_eq_ofReal_iff hlhs_nn hrhs_nn, ofReal_integral_eq_lintegral_ofReal hint hnn,
    lintegral_gaussLR_rpow_eq_gaussianReal hv β hs, ENNReal.ofReal_mul (Real.exp_pos _).le,
    measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]

lemma integrable_gaussLR_pow {μ₀ Δ : ℝ} {v : ℝ≥0} (hv : v ≠ 0) (n : ℕ) {s : Set ℝ}
    (hs : MeasurableSet s) :
    IntegrableOn (fun x => gaussLR μ₀ Δ v x ^ n) s (gaussianReal μ₀ v) := by
  simp_rw [fun x => (Real.rpow_natCast (gaussLR μ₀ Δ v x) n).symm]
  exact integrable_gaussLR_rpow hv (n : ℝ) hs

/-- The incomplete moment `∫_s L^n dν₀` as a Bochner integral. -/
lemma integral_gaussLR_pow_eq {μ₀ Δ : ℝ} {v : ℝ≥0} (hv : v ≠ 0) (n : ℕ) {s : Set ℝ}
    (hs : MeasurableSet s) :
    ∫ x in s, gaussLR μ₀ Δ v x ^ n ∂(gaussianReal μ₀ v)
      = Real.exp ((n : ℝ) * ((n : ℝ) - 1) * Δ ^ 2 / (2 * (v : ℝ)))
        * (gaussianReal (μ₀ + (n : ℝ) * Δ) v).real s := by
  simp_rw [fun x => (Real.rpow_natCast (gaussLR μ₀ Δ v x) n).symm]
  exact integral_gaussLR_rpow_eq hv (n : ℝ) hs
/-! ## Term-by-term integration, below `z₁`, under a summability hypothesis -/

/-- Term-by-term integration below `z₁`, given absolute summability of the series of
incomplete moments (discharged by `hsum_below_always`). -/
theorem setIntegral_pow_below_z₁ {α μ₀ Δ : ℝ} (hΔ : 0 < Δ) {v : ℝ≥0} (hv : v ≠ 0)
    {q : ℝ≥0} (hq0 : 0 < q) (hq1 : (q : ℝ) < 1)
    (hsummable : Summable (fun n : ℕ => |Ring.choose α n| * (1 - (q : ℝ)) ^ (α - n) * (q : ℝ) ^ n
      * ∫ z in Set.Iio (z₁ μ₀ Δ v q), gaussLR μ₀ Δ v z ^ n ∂(gaussianReal μ₀ v))) :
    ∫ z in Set.Iio (z₁ μ₀ Δ v q), ((1 - (q : ℝ)) + (q : ℝ) * gaussLR μ₀ Δ v z) ^ α
        ∂(gaussianReal μ₀ v)
      = ∑' n : ℕ, Ring.choose α n * (1 - (q : ℝ)) ^ (α - n) * (q : ℝ) ^ n
          * ∫ z in Set.Iio (z₁ μ₀ Δ v q), gaussLR μ₀ Δ v z ^ n ∂(gaussianReal μ₀ v) := by
  set s := Set.Iio (z₁ μ₀ Δ v q) with hsdef
  set μ := (gaussianReal μ₀ v).restrict s with hμdef
  have hs : MeasurableSet s := measurableSet_Iio
  set g := fun n : ℕ => |Ring.choose α n| * (1 - (q : ℝ)) ^ (α - n) * (q : ℝ) ^ n
    * ∫ z in s, gaussLR μ₀ Δ v z ^ n ∂(gaussianReal μ₀ v) with hgdef
  set f := fun (n : ℕ) (z : ℝ) => Ring.choose α n * (1 - (q : ℝ)) ^ (α - n) * (q : ℝ) ^ n
    * gaussLR μ₀ Δ v z ^ n with hfdef
  have hintcongr : ∫ z in s, ((1 - (q : ℝ)) + (q : ℝ) * gaussLR μ₀ Δ v z) ^ α
      ∂(gaussianReal μ₀ v) = ∫ z, ∑' n : ℕ, f n z ∂μ := by
    apply setIntegral_congr_fun hs
    intro z hz
    exact ((hasSum_pow_below_z₁ hΔ hv hq0 hq1 hz).tsum_eq).symm
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable (f n) μ := fun n =>
    ((measurable_gaussLR.pow_const n).const_mul _).aestronglyMeasurable
  have h1q : (0 : ℝ) ≤ 1 - (q : ℝ) := by linarith
  have hLnn : ∀ z, (0 : ℝ) ≤ gaussLR μ₀ Δ v z := fun z => (Real.exp_pos _).le
  have hcoefnn : ∀ n : ℕ, (0:ℝ) ≤ |Ring.choose α n| * ((1 - (q:ℝ)) ^ (α - n) * (q:ℝ) ^ n) :=
    fun n => mul_nonneg (abs_nonneg _) (mul_nonneg (Real.rpow_nonneg h1q _) (by positivity))
  have hgnn : ∀ n, (0 : ℝ) ≤ g n := fun n => by
    rw [hgdef]
    exact mul_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg h1q _))
      (by positivity)) (setIntegral_nonneg hs (fun z _ => pow_nonneg (hLnn z) n))
  have hfin : ∑' n : ℕ, ∫⁻ z, ‖f n z‖ₑ ∂μ ≠ ⊤ := by
    have hterm : ∀ n : ℕ, ∫⁻ z, ‖f n z‖ₑ ∂μ = ENNReal.ofReal (g n) := by
      intro n
      have habs : ∀ z, ‖f n z‖ₑ = ENNReal.ofReal
            (|Ring.choose α n| * ((1 - (q:ℝ)) ^ (α - n) * (q:ℝ) ^ n))
          * ENNReal.ofReal (gaussLR μ₀ Δ v z ^ n) := by
        intro z
        rw [hfdef, Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_mul (hcoefnn n)]
        congr 1
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg h1q (α - (n:ℝ))),
          abs_of_nonneg (by positivity : (0:ℝ) ≤ (q:ℝ) ^ n),
          abs_of_nonneg (pow_nonneg (hLnn z) n)]
        ring
      simp_rw [habs]
      rw [lintegral_const_mul _ (measurable_gaussLR.pow_const n).ennreal_ofReal,
        ← ofReal_integral_eq_lintegral_ofReal
          (integrable_gaussLR_pow (μ₀ := μ₀) (Δ := Δ) hv n hs)
          (ae_of_all _ fun z => pow_nonneg (hLnn z) n),
        ← ENNReal.ofReal_mul (hcoefnn n), hgdef]
      congr 1
      ring
    simp_rw [hterm]
    rw [← ENNReal.ofReal_tsum_of_nonneg hgnn hsummable]
    exact ENNReal.ofReal_ne_top
  rw [hintcongr, integral_tsum hmeas hfin]
  simp only [hfdef, hμdef]
  exact tsum_congr fun n => integral_const_mul _ _

/-! ## The same, above `z₁` (exponents `α - n`, negative for `n > α`) -/


/-- Term-by-term integration above `z₁`, given absolute summability (discharged by
`hsum_above_always`). -/
theorem setIntegral_pow_above_z₁ {α μ₀ Δ : ℝ} (hΔ : 0 < Δ) {v : ℝ≥0} (hv : v ≠ 0)
    {q : ℝ≥0} (hq0 : 0 < q) (hq1 : (q : ℝ) < 1)
    (hsummable : Summable (fun n : ℕ => |Ring.choose α n| * (1 - (q : ℝ)) ^ n
      * (q : ℝ) ^ (α - n)
      * ∫ z in Set.Ioi (z₁ μ₀ Δ v q), gaussLR μ₀ Δ v z ^ (α - (n : ℝ)) ∂(gaussianReal μ₀ v))) :
    ∫ z in Set.Ioi (z₁ μ₀ Δ v q), ((1 - (q : ℝ)) + (q : ℝ) * gaussLR μ₀ Δ v z) ^ α
        ∂(gaussianReal μ₀ v)
      = ∑' n : ℕ, Ring.choose α n * (1 - (q : ℝ)) ^ n * (q : ℝ) ^ (α - n)
          * ∫ z in Set.Ioi (z₁ μ₀ Δ v q), gaussLR μ₀ Δ v z ^ (α - (n : ℝ))
            ∂(gaussianReal μ₀ v) := by
  set s := Set.Ioi (z₁ μ₀ Δ v q) with hsdef
  set μ := (gaussianReal μ₀ v).restrict s with hμdef
  have hs : MeasurableSet s := measurableSet_Ioi
  set g := fun n : ℕ => |Ring.choose α n| * (1 - (q : ℝ)) ^ n * (q : ℝ) ^ (α - n)
    * ∫ z in s, gaussLR μ₀ Δ v z ^ (α - (n : ℝ)) ∂(gaussianReal μ₀ v) with hgdef
  set f := fun (n : ℕ) (z : ℝ) => Ring.choose α n * (1 - (q : ℝ)) ^ n * (q : ℝ) ^ (α - n)
    * gaussLR μ₀ Δ v z ^ (α - (n : ℝ)) with hfdef
  have hintcongr : ∫ z in s, ((1 - (q : ℝ)) + (q : ℝ) * gaussLR μ₀ Δ v z) ^ α
      ∂(gaussianReal μ₀ v) = ∫ z, ∑' n : ℕ, f n z ∂μ := by
    apply setIntegral_congr_fun hs
    intro z hz
    exact ((hasSum_pow_above_z₁ hΔ hv hq0 hq1 hz).tsum_eq).symm
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable (f n) μ := fun n =>
    ((measurable_gaussLR_rpow μ₀ Δ v (α - n)).const_mul _).aestronglyMeasurable
  have h1q : (0 : ℝ) ≤ 1 - (q : ℝ) := by linarith
  have hqR : (0 : ℝ) < (q : ℝ) := hq0
  have hLnn : ∀ z, (0 : ℝ) ≤ gaussLR μ₀ Δ v z := fun z => (Real.exp_pos _).le
  have hcoefnn : ∀ n : ℕ, (0 : ℝ) ≤ |Ring.choose α n| * ((1 - (q:ℝ)) ^ n * (q:ℝ) ^ (α - n)) :=
    fun n => mul_nonneg (abs_nonneg _) (mul_nonneg (pow_nonneg h1q n)
      (Real.rpow_nonneg hqR.le _))
  have hgnn : ∀ n, (0 : ℝ) ≤ g n := fun n => by
    rw [hgdef]
    exact mul_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) (pow_nonneg h1q n))
      (Real.rpow_nonneg hqR.le _))
      (setIntegral_nonneg hs (fun z _ => Real.rpow_nonneg (hLnn z) _))
  have hfin : ∑' n : ℕ, ∫⁻ z, ‖f n z‖ₑ ∂μ ≠ ⊤ := by
    have hterm : ∀ n : ℕ, ∫⁻ z, ‖f n z‖ₑ ∂μ = ENNReal.ofReal (g n) := by
      intro n
      have habs : ∀ z, ‖f n z‖ₑ = ENNReal.ofReal
            (|Ring.choose α n| * ((1 - (q:ℝ)) ^ n * (q:ℝ) ^ (α - n)))
          * ENNReal.ofReal (gaussLR μ₀ Δ v z ^ (α - (n:ℝ))) := by
        intro z
        rw [hfdef, Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_mul (hcoefnn n)]
        congr 1
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (pow_nonneg h1q n),
          abs_of_nonneg (Real.rpow_nonneg hqR.le (α - (n:ℝ))),
          abs_of_nonneg (Real.rpow_nonneg (hLnn z) (α - (n:ℝ)))]
        ring
      simp_rw [habs]
      rw [lintegral_const_mul _ (measurable_gaussLR_rpow μ₀ Δ v (α - n)).ennreal_ofReal,
        ← ofReal_integral_eq_lintegral_ofReal
          (integrable_gaussLR_rpow (μ₀ := μ₀) (Δ := Δ) hv (α - n) hs)
          (ae_of_all _ fun z => Real.rpow_nonneg (hLnn z) (α - (n:ℝ))),
        ← ENNReal.ofReal_mul (hcoefnn n), hgdef]
      congr 1
      ring
    simp_rw [hterm]
    rw [← ENNReal.ofReal_tsum_of_nonneg hgnn hsummable]
    exact ENNReal.ofReal_ne_top
  rw [hintcongr, integral_tsum hmeas hfin]
  simp only [hfdef, hμdef]
  exact tsum_congr fun n => integral_const_mul _ _


/-- **The closed form at real order**, given the two summability hypotheses `hsum_below`,
`hsum_above`. -/
theorem hellingerIntegral_sgMixture_real_closedForm {α μ₀ Δ : ℝ} (hα : 1 < α) (hΔ : 0 < Δ) {v : ℝ≥0}
    (hv : v ≠ 0) {q : ℝ≥0} (hq0 : 0 < q) (hq1 : (q : ℝ) < 1)
    (hsum_below : Summable (fun n : ℕ => |Ring.choose α n| * (1 - (q : ℝ)) ^ (α - n) * (q : ℝ) ^ n
      * ∫ z in Set.Iio (z₁ μ₀ Δ v q), gaussLR μ₀ Δ v z ^ n ∂(gaussianReal μ₀ v)))
    (hsum_above : Summable (fun n : ℕ => |Ring.choose α n| * (1 - (q : ℝ)) ^ n * (q : ℝ) ^ (α - n)
      * ∫ z in Set.Ioi (z₁ μ₀ Δ v q), gaussLR μ₀ Δ v z ^ (α - (n : ℝ))
        ∂(gaussianReal μ₀ v))) :
    hellingerIntegral α ((1 - (q : ℝ≥0∞)) • gaussianReal μ₀ v + (q : ℝ≥0∞) • gaussianReal (μ₀ + Δ) v)
        (gaussianReal μ₀ v)
      = ENNReal.ofReal
          ((∑' n : ℕ, Ring.choose α n * (1 - (q : ℝ)) ^ (α - n) * (q : ℝ) ^ n
              * ∫ z in Set.Iio (z₁ μ₀ Δ v q), gaussLR μ₀ Δ v z ^ n ∂(gaussianReal μ₀ v))
            + ∑' n : ℕ, Ring.choose α n * (1 - (q : ℝ)) ^ n * (q : ℝ) ^ (α - n)
              * ∫ z in Set.Ioi (z₁ μ₀ Δ v q), gaussLR μ₀ Δ v z ^ (α - (n : ℝ))
                ∂(gaussianReal μ₀ v)) := by
  have hq : q ≤ 1 := hq1.le
  haveI : NullSingletonClass (gaussianReal μ₀ v) := noAtoms_gaussianReal hv
  have hintfun := integrable_mixture_pow (μ₀ := μ₀) (Δ := Δ) hα hv hq
  have hsplit : ∫ x, ((1 - (q : ℝ)) + (q : ℝ) * gaussLR μ₀ Δ v x) ^ α ∂(gaussianReal μ₀ v)
      = ∫ x in Set.Iio (z₁ μ₀ Δ v q), ((1 - (q : ℝ)) + (q : ℝ) * gaussLR μ₀ Δ v x) ^ α
          ∂(gaussianReal μ₀ v)
        + ∫ x in Set.Ioi (z₁ μ₀ Δ v q), ((1 - (q : ℝ)) + (q : ℝ) * gaussLR μ₀ Δ v x) ^ α
          ∂(gaussianReal μ₀ v) := by
    have hcompl : ∫ x in (Set.Iio (z₁ μ₀ Δ v q))ᶜ,
        ((1 - (q : ℝ)) + (q : ℝ) * gaussLR μ₀ Δ v x) ^ α ∂(gaussianReal μ₀ v)
        = ∫ x in Set.Ioi (z₁ μ₀ Δ v q), ((1 - (q : ℝ)) + (q : ℝ) * gaussLR μ₀ Δ v x) ^ α
          ∂(gaussianReal μ₀ v) := by
      rw [Set.compl_Iio, ← restrict_Ioi_eq_restrict_Ici]
    have hadd := (integral_add_compl (measurableSet_Iio (a := z₁ μ₀ Δ v q)) hintfun).symm
    rwa [hcompl] at hadd
  rw [hellingerIntegral_sgMixture_real hα hv q hq, hsplit,
    setIntegral_pow_below_z₁ hΔ hv hq0 hq1 hsum_below,
    setIntegral_pow_above_z₁ hΔ hv hq0 hq1 hsum_above]

/-! ## Discharging the summability hypotheses

From `summable_abs_ringChoose` (`RingChooseSummable.lean`). -/

/-- Once `Ring.choose a` vanishes at some index, it vanishes at every later index. -/
lemma ringChoose_eq_zero_forall_ge (a : ℝ) {N : ℕ} (h : Ring.choose a N = 0) :
    ∀ n ≥ N, Ring.choose a n = 0 := by
  have hstep : ∀ k : ℕ, Ring.choose a (N + k) = 0 := by
    intro k
    induction k with
    | zero => simpa using h
    | succ k ih =>
      have heq : N + (k + 1) = (N + k) + 1 := by ring
      rw [heq, RingChooseSummable.choose_succ_eq, ih]
      ring
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  exact hstep k

/-- **`Ring.choose a n` is absolutely summable for every real `a > 0`.** -/
lemma summable_abs_ringChoose_always (a : ℝ) (ha : 0 < a) :
    Summable (fun n : ℕ => |Ring.choose a n|) := by
  set N := ⌈2 * (|a| + 1)⌉₊ + 1 with hNdef
  have hN1 : 1 ≤ N := by omega
  have hNbd : 2 * (|a| + 1) ≤ (N : ℝ) := by
    have h1 : 2 * (|a| + 1) ≤ (⌈2 * (|a| + 1)⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈2 * (|a| + 1)⌉₊ : ℝ) ≤ (N : ℝ) := by rw [hNdef]; push_cast; linarith
    linarith
  by_cases hc : Ring.choose a N = 0
  · apply summable_of_ne_finset_zero (s := Finset.range N)
    intro n hn
    rw [Finset.mem_range, not_lt] at hn
    rw [ringChoose_eq_zero_forall_ge a hc n hn]
    simp
  · exact RingChooseSummable.summable_abs_ringChoose a ha N hN1 hNbd hc

/-- **Moment/tail bound above `z₁`**, at real exponent `β`: the same bound as
`incomplete_moment_below_bound`. -/
lemma incomplete_moment_above_bound {μ₀ Δ : ℝ} (hΔ : 0 < Δ) {v : ℝ≥0} (hv : v ≠ 0) {q : ℝ≥0}
    (hq0 : 0 < q) (hq1 : (q : ℝ) < 1) (β : ℝ) (hβ : μ₀ + β * Δ ≤ z₁ μ₀ Δ v q) :
    ENNReal.ofReal (Real.exp (β * (β - 1) * Δ ^ 2 / (2 * (v : ℝ))))
        * gaussianReal (μ₀ + β * Δ) v (Set.Ici (z₁ μ₀ Δ v q))
      ≤ ENNReal.ofReal (Real.exp (-(μ₀ - z₁ μ₀ Δ v q) ^ 2 / (2 * (v : ℝ)))
          * ((1 - (q : ℝ)) / q) ^ β) := by
  have hqR : (0 : ℝ) < (q : ℝ) := hq0
  have hrpos : (0 : ℝ) < (1 - (q : ℝ)) / q := div_pos (by linarith) hqR
  have htail := gaussianReal_measure_ge_le (m := μ₀ + β * Δ) hv (ε := z₁ μ₀ Δ v q) hβ
  have hmeasle : gaussianReal (μ₀ + β * Δ) v (Set.Ici (z₁ μ₀ Δ v q))
      ≤ ENNReal.ofReal
          (Real.exp (-(z₁ μ₀ Δ v q - (μ₀ + β * Δ)) ^ 2 / (2 * (v : ℝ)))) :=
    measure_le_ofReal_of_real_le htail
  have hpow : ((1 - (q : ℝ)) / q) ^ β
      = Real.exp (β * Real.log ((1 - (q : ℝ)) / q)) := by
    rw [Real.rpow_def_of_pos hrpos, mul_comm]
  have key : β * (β - 1) * Δ ^ 2 / (2 * (v : ℝ))
      + -(z₁ μ₀ Δ v q - (μ₀ + β * Δ)) ^ 2 / (2 * (v : ℝ))
      = -(μ₀ - z₁ μ₀ Δ v q) ^ 2 / (2 * (v : ℝ))
        + β * Real.log ((1 - (q : ℝ)) / q) := by
    unfold z₁
    field_simp
    ring
  calc ENNReal.ofReal (Real.exp (β * (β - 1) * Δ ^ 2 / (2 * (v : ℝ))))
      * gaussianReal (μ₀ + β * Δ) v (Set.Ici (z₁ μ₀ Δ v q))
      ≤ ENNReal.ofReal (Real.exp (β * (β - 1) * Δ ^ 2 / (2 * (v : ℝ))))
          * ENNReal.ofReal
            (Real.exp (-(z₁ μ₀ Δ v q - (μ₀ + β * Δ)) ^ 2 / (2 * (v : ℝ)))) :=
        mul_le_mul_right hmeasle _
    _ = ENNReal.ofReal (Real.exp (β * (β - 1) * Δ ^ 2 / (2 * (v : ℝ)))
          * Real.exp (-(z₁ μ₀ Δ v q - (μ₀ + β * Δ)) ^ 2 / (2 * (v : ℝ)))) :=
        (ENNReal.ofReal_mul (Real.exp_pos _).le).symm
    _ = ENNReal.ofReal (Real.exp (-(μ₀ - z₁ μ₀ Δ v q) ^ 2 / (2 * (v : ℝ)))
          * ((1 - (q : ℝ)) / q) ^ β) := by
        rw [← Real.exp_add, key, Real.exp_add, hpow]

lemma integral_gaussLR_pow_below_eventual_bound {μ₀ Δ : ℝ} (hΔ : 0 < Δ) {v : ℝ≥0} (hv : v ≠ 0)
    {q : ℝ≥0} (hq0 : 0 < q) (hq1 : (q : ℝ) < 1) (n : ℕ)
    (hn : z₁ μ₀ Δ v q ≤ μ₀ + (n : ℝ) * Δ) :
    ∫ z in Set.Iio (z₁ μ₀ Δ v q), gaussLR μ₀ Δ v z ^ n ∂(gaussianReal μ₀ v)
      ≤ Real.exp (-(μ₀ - z₁ μ₀ Δ v q) ^ 2 / (2 * (v : ℝ))) * ((1 - (q : ℝ)) / q) ^ n := by
  haveI : NullSingletonClass (gaussianReal μ₀ v) := noAtoms_gaussianReal hv
  have hre : (∫ z in Set.Iio (z₁ μ₀ Δ v q), gaussLR μ₀ Δ v z ^ n ∂(gaussianReal μ₀ v))
      = ∫ z in Set.Iic (z₁ μ₀ Δ v q), gaussLR μ₀ Δ v z ^ n ∂(gaussianReal μ₀ v) := by
    rw [restrict_Iio_eq_restrict_Iic]
  rw [hre, integral_gaussLR_pow_eq hv n measurableSet_Iic]
  have hb := incomplete_moment_below_bound hΔ hv hq0 hq1 n hn
  have heq1 : ENNReal.ofReal (Real.exp ((n : ℝ) * ((n : ℝ) - 1) * Δ ^ 2 / (2 * (v : ℝ)))
      * (gaussianReal (μ₀ + (n : ℝ) * Δ) v).real (Set.Iic (z₁ μ₀ Δ v q)))
      = ENNReal.ofReal (Real.exp ((n : ℝ) * ((n : ℝ) - 1) * Δ ^ 2 / (2 * (v : ℝ))))
        * gaussianReal (μ₀ + (n : ℝ) * Δ) v (Set.Iic (z₁ μ₀ Δ v q)) := by
    rw [ENNReal.ofReal_mul (Real.exp_pos _).le, measureReal_def,
      ENNReal.ofReal_toReal (measure_ne_top _ _)]
  have hle : ENNReal.ofReal (Real.exp ((n : ℝ) * ((n : ℝ) - 1) * Δ ^ 2 / (2 * (v : ℝ)))
      * (gaussianReal (μ₀ + (n : ℝ) * Δ) v).real (Set.Iic (z₁ μ₀ Δ v q)))
      ≤ ENNReal.ofReal (Real.exp (-(μ₀ - z₁ μ₀ Δ v q) ^ 2 / (2 * (v : ℝ)))
          * ((1 - (q : ℝ)) / q) ^ n) := by
    rw [heq1]; exact hb
  have h1qnn : (0 : ℝ) ≤ 1 - (q : ℝ) := by linarith
  have hrhsnn : (0 : ℝ) ≤ Real.exp (-(μ₀ - z₁ μ₀ Δ v q) ^ 2 / (2 * (v : ℝ)))
      * ((1 - (q : ℝ)) / q) ^ n :=
    mul_nonneg (Real.exp_pos _).le (pow_nonneg (div_nonneg h1qnn hq0.le) n)
  exact (ENNReal.ofReal_le_ofReal_iff hrhsnn).mp hle

lemma integral_gaussLR_rpow_above_eventual_bound {μ₀ Δ : ℝ} (hΔ : 0 < Δ) {v : ℝ≥0} (hv : v ≠ 0)
    {q : ℝ≥0} (hq0 : 0 < q) (hq1 : (q : ℝ) < 1) (β : ℝ) (hβ : μ₀ + β * Δ ≤ z₁ μ₀ Δ v q) :
    ∫ z in Set.Ioi (z₁ μ₀ Δ v q), gaussLR μ₀ Δ v z ^ β ∂(gaussianReal μ₀ v)
      ≤ Real.exp (-(μ₀ - z₁ μ₀ Δ v q) ^ 2 / (2 * (v : ℝ))) * ((1 - (q : ℝ)) / q) ^ β := by
  haveI : NullSingletonClass (gaussianReal μ₀ v) := noAtoms_gaussianReal hv
  have hre : (∫ z in Set.Ioi (z₁ μ₀ Δ v q), gaussLR μ₀ Δ v z ^ β ∂(gaussianReal μ₀ v))
      = ∫ z in Set.Ici (z₁ μ₀ Δ v q), gaussLR μ₀ Δ v z ^ β ∂(gaussianReal μ₀ v) := by
    rw [restrict_Ioi_eq_restrict_Ici]
  rw [hre, integral_gaussLR_rpow_eq hv β measurableSet_Ici]
  have hb := incomplete_moment_above_bound hΔ hv hq0 hq1 β hβ
  have heq1 : ENNReal.ofReal (Real.exp (β * (β - 1) * Δ ^ 2 / (2 * (v : ℝ)))
      * (gaussianReal (μ₀ + β * Δ) v).real (Set.Ici (z₁ μ₀ Δ v q)))
      = ENNReal.ofReal (Real.exp (β * (β - 1) * Δ ^ 2 / (2 * (v : ℝ))))
        * gaussianReal (μ₀ + β * Δ) v (Set.Ici (z₁ μ₀ Δ v q)) := by
    rw [ENNReal.ofReal_mul (Real.exp_pos _).le, measureReal_def,
      ENNReal.ofReal_toReal (measure_ne_top _ _)]
  have hle : ENNReal.ofReal (Real.exp (β * (β - 1) * Δ ^ 2 / (2 * (v : ℝ)))
      * (gaussianReal (μ₀ + β * Δ) v).real (Set.Ici (z₁ μ₀ Δ v q)))
      ≤ ENNReal.ofReal (Real.exp (-(μ₀ - z₁ μ₀ Δ v q) ^ 2 / (2 * (v : ℝ)))
          * ((1 - (q : ℝ)) / q) ^ β) := by
    rw [heq1]; exact hb
  have hrhsnn : (0 : ℝ) ≤ Real.exp (-(μ₀ - z₁ μ₀ Δ v q) ^ 2 / (2 * (v : ℝ)))
      * ((1 - (q : ℝ)) / q) ^ β :=
    mul_nonneg (Real.exp_pos _).le
      (Real.rpow_nonneg (div_nonneg (by linarith) hq0.le) β)
  exact (ENNReal.ofReal_le_ofReal_iff hrhsnn).mp hle

/-- The below-`z₁` series' `n`-th term, without the `|choose|` factor, is eventually bounded by
`(1-q)^α·exp(-(μ₀-z₁)²/2v)`. -/
lemma below_term_eventual_bound {α μ₀ Δ : ℝ} (hΔ : 0 < Δ) {v : ℝ≥0} (hv : v ≠ 0) {q : ℝ≥0}
    (hq0 : 0 < q) (hq1 : (q : ℝ) < 1) (n : ℕ) (hn : z₁ μ₀ Δ v q ≤ μ₀ + (n : ℝ) * Δ) :
    (1 - (q : ℝ)) ^ (α - n) * (q : ℝ) ^ n
        * ∫ z in Set.Iio (z₁ μ₀ Δ v q), gaussLR μ₀ Δ v z ^ n ∂(gaussianReal μ₀ v)
      ≤ (1 - (q : ℝ)) ^ α * Real.exp (-(μ₀ - z₁ μ₀ Δ v q) ^ 2 / (2 * (v : ℝ))) := by
  have h1q : (0 : ℝ) < 1 - (q : ℝ) := by linarith
  have hqR : (0 : ℝ) < (q : ℝ) := hq0
  have hqn : (q : ℝ) ^ n ≠ 0 := pow_ne_zero n hqR.ne'
  have hbound := integral_gaussLR_pow_below_eventual_bound hΔ hv hq0 hq1 n hn
  have hcoefnn : (0 : ℝ) ≤ (1 - (q : ℝ)) ^ (α - n) * (q : ℝ) ^ n :=
    mul_nonneg (Real.rpow_nonneg h1q.le _) (by positivity)
  calc (1 - (q : ℝ)) ^ (α - n) * (q : ℝ) ^ n
        * ∫ z in Set.Iio (z₁ μ₀ Δ v q), gaussLR μ₀ Δ v z ^ n ∂(gaussianReal μ₀ v)
      ≤ (1 - (q : ℝ)) ^ (α - n) * (q : ℝ) ^ n
          * (Real.exp (-(μ₀ - z₁ μ₀ Δ v q) ^ 2 / (2 * (v : ℝ))) * ((1 - (q : ℝ)) / q) ^ n) :=
        mul_le_mul_of_nonneg_left hbound hcoefnn
    _ = (1 - (q : ℝ)) ^ α * Real.exp (-(μ₀ - z₁ μ₀ Δ v q) ^ 2 / (2 * (v : ℝ))) := by
        rw [div_pow,
          show (1 - (q : ℝ)) ^ (α - (n : ℝ)) * (q : ℝ) ^ n
              * (Real.exp (-(μ₀ - z₁ μ₀ Δ v q) ^ 2 / (2 * (v : ℝ)))
                * ((1 - (q : ℝ)) ^ n / (q : ℝ) ^ n))
            = (1 - (q : ℝ)) ^ (α - (n : ℝ)) * (1 - (q : ℝ)) ^ n
              * Real.exp (-(μ₀ - z₁ μ₀ Δ v q) ^ 2 / (2 * (v : ℝ)))
              * ((q : ℝ) ^ n / (q : ℝ) ^ n) from by ring,
          div_self hqn, mul_one, ← Real.rpow_natCast (1 - (q : ℝ)) n, ← Real.rpow_add h1q,
          show α - (n : ℝ) + (n : ℝ) = α from by ring]

/-- The same bound for the above-`z₁` series. -/
lemma above_term_eventual_bound {α μ₀ Δ : ℝ} (hΔ : 0 < Δ) {v : ℝ≥0} (hv : v ≠ 0) {q : ℝ≥0}
    (hq0 : 0 < q) (hq1 : (q : ℝ) < 1) (n : ℕ) (hn : μ₀ + (α - (n : ℝ)) * Δ ≤ z₁ μ₀ Δ v q) :
    (1 - (q : ℝ)) ^ n * (q : ℝ) ^ (α - n)
        * ∫ z in Set.Ioi (z₁ μ₀ Δ v q), gaussLR μ₀ Δ v z ^ (α - (n : ℝ)) ∂(gaussianReal μ₀ v)
      ≤ (1 - (q : ℝ)) ^ α * Real.exp (-(μ₀ - z₁ μ₀ Δ v q) ^ 2 / (2 * (v : ℝ))) := by
  have h1q : (0 : ℝ) < 1 - (q : ℝ) := by linarith
  have hqR : (0 : ℝ) < (q : ℝ) := hq0
  have hqan : (q : ℝ) ^ (α - (n : ℝ)) ≠ 0 := (Real.rpow_pos_of_pos hqR _).ne'
  have hbound := integral_gaussLR_rpow_above_eventual_bound hΔ hv hq0 hq1 (α - n) hn
  have hcoefnn : (0 : ℝ) ≤ (1 - (q : ℝ)) ^ n * (q : ℝ) ^ (α - n) :=
    mul_nonneg (by positivity) (Real.rpow_nonneg hqR.le _)
  calc (1 - (q : ℝ)) ^ n * (q : ℝ) ^ (α - n)
        * ∫ z in Set.Ioi (z₁ μ₀ Δ v q), gaussLR μ₀ Δ v z ^ (α - (n : ℝ)) ∂(gaussianReal μ₀ v)
      ≤ (1 - (q : ℝ)) ^ n * (q : ℝ) ^ (α - n)
          * (Real.exp (-(μ₀ - z₁ μ₀ Δ v q) ^ 2 / (2 * (v : ℝ))) * ((1 - (q : ℝ)) / q) ^ (α - n)) :=
        mul_le_mul_of_nonneg_left hbound hcoefnn
    _ = (1 - (q : ℝ)) ^ α * Real.exp (-(μ₀ - z₁ μ₀ Δ v q) ^ 2 / (2 * (v : ℝ))) := by
        rw [Real.div_rpow h1q.le hqR.le,
          show (1 - (q : ℝ)) ^ n * (q : ℝ) ^ (α - (n : ℝ))
              * (Real.exp (-(μ₀ - z₁ μ₀ Δ v q) ^ 2 / (2 * (v : ℝ)))
                * ((1 - (q : ℝ)) ^ (α - (n : ℝ)) / (q : ℝ) ^ (α - (n : ℝ))))
            = (1 - (q : ℝ)) ^ n * (1 - (q : ℝ)) ^ (α - (n : ℝ))
              * Real.exp (-(μ₀ - z₁ μ₀ Δ v q) ^ 2 / (2 * (v : ℝ)))
              * ((q : ℝ) ^ (α - (n : ℝ)) / (q : ℝ) ^ (α - (n : ℝ))) from by ring,
          div_self hqan, mul_one, ← Real.rpow_natCast (1 - (q : ℝ)) n, ← Real.rpow_add h1q,
          show (n : ℝ) + (α - (n : ℝ)) = α from by ring]

/-- An eventually bounded nonnegative sequence times `|Ring.choose a ·|` is summable. -/
lemma summable_choose_mul_of_eventually_le {a : ℝ} (ha : 0 < a) (g : ℕ → ℝ)
    (hgnn : ∀ n, 0 ≤ g n) {N₀ : ℕ} {K : ℝ} (hbound : ∀ n ≥ N₀, g n ≤ K) :
    Summable (fun n : ℕ => |Ring.choose a n| * g n) := by
  rw [← summable_nat_add_iff N₀]
  have hshift : Summable (fun n : ℕ => |Ring.choose a (n + N₀)|) :=
    (summable_nat_add_iff N₀).mpr (summable_abs_ringChoose_always a ha)
  have hdom : Summable (fun n : ℕ => K * |Ring.choose a (n + N₀)|) := hshift.mul_left K
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (abs_nonneg _) (hgnn _))
    (fun n => ?_) hdom
  calc |Ring.choose a (n + N₀)| * g (n + N₀)
      ≤ |Ring.choose a (n + N₀)| * K :=
        mul_le_mul_of_nonneg_left (hbound (n + N₀) (Nat.le_add_left N₀ n)) (abs_nonneg _)
    _ = K * |Ring.choose a (n + N₀)| := mul_comm _ _

lemma hsum_below_always {α μ₀ Δ : ℝ} (hα : 1 < α) (hΔ : 0 < Δ) {v : ℝ≥0} (hv : v ≠ 0) {q : ℝ≥0}
    (hq0 : 0 < q) (hq1 : (q : ℝ) < 1) :
    Summable (fun n : ℕ => |Ring.choose α n| * (1 - (q : ℝ)) ^ (α - n) * (q : ℝ) ^ n
      * ∫ z in Set.Iio (z₁ μ₀ Δ v q), gaussLR μ₀ Δ v z ^ n ∂(gaussianReal μ₀ v)) := by
  set N₀ : ℕ := ⌈(z₁ μ₀ Δ v q - μ₀) / Δ⌉₊ with hN₀def
  have hN₀ : ∀ n : ℕ, N₀ ≤ n → z₁ μ₀ Δ v q ≤ μ₀ + (n : ℝ) * Δ := by
    intro n hn
    have h1 : (z₁ μ₀ Δ v q - μ₀) / Δ ≤ (N₀ : ℝ) := Nat.le_ceil _
    have h2 : (N₀ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have h3 : (z₁ μ₀ Δ v q - μ₀) / Δ ≤ (n : ℝ) := h1.trans h2
    rw [div_le_iff₀ hΔ] at h3
    linarith
  have hg : ∀ n : ℕ, (fun n : ℕ => |Ring.choose α n| * (1 - (q : ℝ)) ^ (α - n) * (q : ℝ) ^ n
      * ∫ z in Set.Iio (z₁ μ₀ Δ v q), gaussLR μ₀ Δ v z ^ n ∂(gaussianReal μ₀ v)) n
      = |Ring.choose α n| * ((1 - (q : ℝ)) ^ (α - n) * (q : ℝ) ^ n
        * ∫ z in Set.Iio (z₁ μ₀ Δ v q), gaussLR μ₀ Δ v z ^ n ∂(gaussianReal μ₀ v)) := by
    intro n; ring
  simp_rw [hg]
  have h1q : (0 : ℝ) < 1 - (q : ℝ) := by linarith
  refine summable_choose_mul_of_eventually_le (lt_trans one_pos hα) _ (fun n => ?_)
    (K := (1 - (q : ℝ)) ^ α * Real.exp (-(μ₀ - z₁ μ₀ Δ v q) ^ 2 / (2 * (v : ℝ))))
    (fun n hn => below_term_eventual_bound hΔ hv hq0 hq1 n (hN₀ n hn))
  exact mul_nonneg (mul_nonneg (Real.rpow_nonneg h1q.le _) (by positivity))
    (setIntegral_nonneg measurableSet_Iio (fun z _ => pow_nonneg (Real.exp_pos _).le n))

lemma hsum_above_always {α μ₀ Δ : ℝ} (hα : 1 < α) (hΔ : 0 < Δ) {v : ℝ≥0} (hv : v ≠ 0) {q : ℝ≥0}
    (hq0 : 0 < q) (hq1 : (q : ℝ) < 1) :
    Summable (fun n : ℕ => |Ring.choose α n| * (1 - (q : ℝ)) ^ n * (q : ℝ) ^ (α - n)
      * ∫ z in Set.Ioi (z₁ μ₀ Δ v q), gaussLR μ₀ Δ v z ^ (α - (n : ℝ))
        ∂(gaussianReal μ₀ v)) := by
  set N₁ : ℕ := ⌈α - (z₁ μ₀ Δ v q - μ₀) / Δ⌉₊ with hN₁def
  have hN₁ : ∀ n : ℕ, N₁ ≤ n → μ₀ + (α - (n : ℝ)) * Δ ≤ z₁ μ₀ Δ v q := by
    intro n hn
    have h1 : α - (z₁ μ₀ Δ v q - μ₀) / Δ ≤ (N₁ : ℝ) := Nat.le_ceil _
    have h2 : (N₁ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have h3 : α - (z₁ μ₀ Δ v q - μ₀) / Δ ≤ (n : ℝ) := h1.trans h2
    have h4 : α - (n : ℝ) ≤ (z₁ μ₀ Δ v q - μ₀) / Δ := by linarith
    rw [le_div_iff₀ hΔ] at h4
    linarith
  have hg : ∀ n : ℕ, (fun n : ℕ => |Ring.choose α n| * (1 - (q : ℝ)) ^ n * (q : ℝ) ^ (α - n)
      * ∫ z in Set.Ioi (z₁ μ₀ Δ v q), gaussLR μ₀ Δ v z ^ (α - (n : ℝ))
        ∂(gaussianReal μ₀ v)) n
      = |Ring.choose α n| * ((1 - (q : ℝ)) ^ n * (q : ℝ) ^ (α - n)
        * ∫ z in Set.Ioi (z₁ μ₀ Δ v q), gaussLR μ₀ Δ v z ^ (α - (n : ℝ))
          ∂(gaussianReal μ₀ v)) := by
    intro n; ring
  simp_rw [hg]
  have h1q : (0 : ℝ) < 1 - (q : ℝ) := by linarith
  refine summable_choose_mul_of_eventually_le (lt_trans one_pos hα) _ (fun n => ?_)
    (K := (1 - (q : ℝ)) ^ α * Real.exp (-(μ₀ - z₁ μ₀ Δ v q) ^ 2 / (2 * (v : ℝ))))
    (fun n hn => above_term_eventual_bound hΔ hv hq0 hq1 n (hN₁ n hn))
  exact mul_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg hq0.le _))
    (setIntegral_nonneg measurableSet_Ioi
      (fun z _ => Real.rpow_nonneg (Real.exp_pos _).le _))

/-- **The subsampled Gaussian in closed form, at every real order `α > 1`**: the two binomial
series of Mironov et al. (§3.3), split at `z₁`. -/
theorem hellingerIntegral_sgMixture_real_closedForm_unconditional {α μ₀ Δ : ℝ} (hα : 1 < α) (hΔ : 0 < Δ)
    {v : ℝ≥0} (hv : v ≠ 0) {q : ℝ≥0} (hq0 : 0 < q) (hq1 : (q : ℝ) < 1) :
    hellingerIntegral α ((1 - (q : ℝ≥0∞)) • gaussianReal μ₀ v + (q : ℝ≥0∞) • gaussianReal (μ₀ + Δ) v)
        (gaussianReal μ₀ v)
      = ENNReal.ofReal
          ((∑' n : ℕ, Ring.choose α n * (1 - (q : ℝ)) ^ (α - n) * (q : ℝ) ^ n
              * ∫ z in Set.Iio (z₁ μ₀ Δ v q), gaussLR μ₀ Δ v z ^ n ∂(gaussianReal μ₀ v))
            + ∑' n : ℕ, Ring.choose α n * (1 - (q : ℝ)) ^ n * (q : ℝ) ^ (α - n)
              * ∫ z in Set.Ioi (z₁ μ₀ Δ v q), gaussLR μ₀ Δ v z ^ (α - (n : ℝ))
                ∂(gaussianReal μ₀ v)) :=
  hellingerIntegral_sgMixture_real_closedForm hα hΔ hv hq0 hq1
    (hsum_below_always hα hΔ hv hq0 hq1) (hsum_above_always hα hΔ hv hq0 hq1)

/-! ## Monotonicity in the sensitivity

`hellingerIntegral α (mixture Δ) ν₀ = E_{z∼ν₀}[((1-q)+q·L_Δ(z))^α]` depends on `Δ` only through
`β = Δ²/v` (`integral_mixturePow_gaussLR_eq_expShift`): `L_Δ(z)` is distributed as `exp(Y − β/2)`,
`Y ∼ 𝒩(0,β)`. It is monotone in `β` (`mixturePow_integral_mono_variance`): splitting
`𝒩(0,β₁+τ) = 𝒩(0,β₁) ∗ 𝒩(0,τ)` adds a mean-one independent factor, and Jensen applies to the
convex `t ↦ ((1-q)+q·t)^α`. -/

/-- The mixture integrand as a standalone function, for the convex-order argument. -/
noncomputable def mixturePow (α : ℝ) (q : ℝ≥0) (t : ℝ) : ℝ := ((1 - (q:ℝ)) + (q:ℝ) * t) ^ α

/-- `mixturePow α q` is convex on `t ≥ 0`, for `α ≥ 1` and `q ≤ 1`. -/
lemma convexOn_mixturePow {α : ℝ} (hα : 1 ≤ α) {q : ℝ≥0} (hq1 : (q:ℝ) ≤ 1) :
    ConvexOn ℝ (Set.Ici (0:ℝ)) (mixturePow α q) := by
  have hbase := convexOn_rpow hα
  refine ⟨convex_Ici 0, fun x hx y hy a b ha hb hab => ?_⟩
  simp only [smul_eq_mul] at hab ⊢
  have hqnn : (0:ℝ) ≤ (q:ℝ) := q.coe_nonneg
  have hq1' : (0:ℝ) ≤ 1 - (q:ℝ) := by linarith
  have hxnn : (0:ℝ) ≤ x := hx
  have hynn : (0:ℝ) ≤ y := hy
  set u := (1 - (q:ℝ)) + (q:ℝ)*x with hu
  set w := (1 - (q:ℝ)) + (q:ℝ)*y with hw
  have hune : u ∈ Set.Ici (0:ℝ) := by rw [hu, Set.mem_Ici]; positivity
  have hwne : w ∈ Set.Ici (0:ℝ) := by rw [hw, Set.mem_Ici]; positivity
  have hkey := hbase.2 hune hwne ha hb hab
  simp only [smul_eq_mul] at hkey
  have heq : (1 - (q:ℝ)) + (q:ℝ)*(a*x+b*y) = a*u + b*w := by rw [hu, hw]; nlinarith [hab]
  show mixturePow α q (a * x + b * y) ≤ a * mixturePow α q x + b * mixturePow α q y
  unfold mixturePow
  rw [heq]
  exact hkey

lemma continuous_mixturePow {α : ℝ} (hα0 : 0 ≤ α) {q : ℝ≥0} : Continuous (mixturePow α q) := by
  unfold mixturePow
  exact (continuous_rpow_const hα0).comp (by fun_prop)

/-- The Gaussian mean-`1` fact underlying the convex-order step: `E_{z∼𝒩(0,β)}[exp(z-β/2)] = 1`. -/
lemma integral_exp_sub_half_gaussianReal (β : ℝ≥0) :
    ∫ x, Real.exp (x - (β:ℝ)/2) ∂(gaussianReal 0 β) = 1 := by
  have hval : mgf id (gaussianReal 0 β) 1 = Real.exp ((β:ℝ)/2) := by
    rw [mgf_id_gaussianReal (μ := (0:ℝ)) (v := β)]; norm_num
  have hunfold : mgf id (gaussianReal 0 β) 1 = ∫ x, Real.exp (1 * x) ∂(gaussianReal 0 β) := rfl
  rw [hunfold] at hval
  simp only [one_mul] at hval
  have heq : ∀ x : ℝ, Real.exp (x - (β:ℝ)/2) = Real.exp x * Real.exp (-((β:ℝ)/2)) := by
    intro x; rw [← Real.exp_add]; ring_nf
  simp_rw [heq]
  rw [integral_mul_const, hval, ← Real.exp_add]
  simp

lemma integrable_mixturePow_expShift {α : ℝ} (hα : 1 ≤ α) {q : ℝ≥0} (hq1 : (q:ℝ) ≤ 1)
    (β : ℝ≥0) :
    Integrable (fun y => mixturePow α q (Real.exp (y - (β:ℝ)/2))) (gaussianReal 0 β) := by
  have hα0 : (0:ℝ) < α := lt_of_lt_of_le one_pos hα
  simp only [mixturePow]
  set L : ℝ → ℝ := fun y => Real.exp (y - (β:ℝ)/2) with hLdef
  have hLpos : ∀ y, 0 < L y := fun y => Real.exp_pos _
  have hnonneg : ∀ y, 0 ≤ (1 - (q:ℝ)) + (q:ℝ) * L y := fun y => by
    have hqnn : (0:ℝ) ≤ (q:ℝ) := q.coe_nonneg
    have : (0:ℝ) ≤ L y := (hLpos y).le
    nlinarith [hqnn, hq1]
  have hLmeas : Measurable L := by rw [hLdef]; fun_prop
  have hgnonneg : 0 ≤ᵐ[gaussianReal 0 β] fun y => (L y) ^ α :=
    ae_of_all _ fun y => Real.rpow_nonneg (hLpos y).le α
  have hgmeas : AEStronglyMeasurable (fun y => (L y) ^ α) (gaussianReal 0 β) :=
    ((continuous_rpow_const hα0.le).measurable.comp hLmeas).aestronglyMeasurable
  have hgint : Integrable (fun y => (L y) ^ α) (gaussianReal 0 β) := by
    refine ⟨hgmeas, (hasFiniteIntegral_iff_ofReal hgnonneg).2 ?_⟩
    have heq : ∀ y, (L y) ^ α = Real.exp (α * (y - (β:ℝ)/2)) := by
      intro y
      rw [hLdef, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, mul_comm]
    have hLexpint : Integrable (fun y => Real.exp (α * (y - (β:ℝ)/2))) (gaussianReal 0 β) := by
      have heq2 : ∀ y : ℝ,
          Real.exp (α * (y - (β:ℝ)/2)) = Real.exp (-(α * (β:ℝ)/2)) * Real.exp (α * y) := by
        intro y; rw [← Real.exp_add]; ring_nf
      simp_rw [heq2]
      exact (integrable_exp_mul_gaussianReal α).const_mul _
    have heqlint : ∫⁻ y, ENNReal.ofReal ((L y)^α) ∂gaussianReal 0 β
        = ∫⁻ y, ENNReal.ofReal (Real.exp (α * (y - (β:ℝ)/2))) ∂gaussianReal 0 β := by
      apply lintegral_congr_ae; filter_upwards with y; rw [heq y]
    rw [heqlint]
    have := hLexpint.2
    rwa [hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun y => (Real.exp_pos _).le))] at this
  have hdom : ∀ y, ((1 - (q:ℝ)) + (q:ℝ) * L y) ^ α ≤ (2:ℝ) ^ α * (1 + (L y) ^ α) := by
    intro y
    have hq1' : (q : ℝ) ≤ 1 := hq1
    have hLnn : (0:ℝ) ≤ L y := (hLpos y).le
    have h1 : (1 - (q:ℝ)) + (q:ℝ) * L y ≤ 1 + L y := by nlinarith [NNReal.coe_nonneg q]
    have h2 : (1:ℝ) + L y ≤ 2 * max 1 (L y) := by
      rcases le_total 1 (L y) with h | h <;> [rw [max_eq_right h]; rw [max_eq_left h]] <;> linarith
    have h3 : max 1 (L y) ^ α ≤ 1 + (L y) ^ α := by
      rcases le_total 1 (L y) with h | h
      · rw [max_eq_right h]; linarith [Real.one_le_rpow h hα0.le]
      · rw [max_eq_left h, Real.one_rpow]
        have : (L y) ^ α ≤ 1 := Real.rpow_le_one hLnn h hα0.le
        linarith [Real.rpow_nonneg hLnn α]
    have hbase1 : (0:ℝ) ≤ 1 - (q:ℝ) + (q:ℝ) * L y := by nlinarith [NNReal.coe_nonneg q]
    have hbase2 : (0:ℝ) ≤ 1 + L y := by linarith
    calc ((1 - (q:ℝ)) + (q:ℝ) * L y) ^ α ≤ (1 + L y) ^ α :=
          Real.rpow_le_rpow hbase1 h1 hα0.le
      _ ≤ (2 * max 1 (L y)) ^ α := Real.rpow_le_rpow hbase2 h2 hα0.le
      _ = 2 ^ α * max 1 (L y) ^ α := Real.mul_rpow (by norm_num) (le_trans zero_le_one (le_max_left _ _))
      _ ≤ 2 ^ α * (1 + (L y) ^ α) := mul_le_mul_of_nonneg_left h3 (Real.rpow_nonneg (by norm_num) α)
  have hdomint : Integrable (fun y => (2:ℝ) ^ α * (1 + (L y) ^ α)) (gaussianReal 0 β) :=
    ((integrable_const 1).add hgint).const_mul _
  have hmeasf : AEStronglyMeasurable
      (fun y => ((1 - (q : ℝ)) + (q : ℝ) * L y) ^ α) (gaussianReal 0 β) :=
    ((continuous_rpow_const hα0.le).measurable.comp
        (measurable_const.add (measurable_const.mul hLmeas))).aestronglyMeasurable
  refine Integrable.mono' hdomint hmeasf (ae_of_all _ fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hnonneg y) α)]
  exact hdom y

/-- **The convex-order step**: `β ↦ E_{y∼𝒩(0,β)}[mixturePow α q (exp(y-β/2))]` is monotone. -/
theorem mixturePow_integral_mono_variance {α : ℝ} (hα : 1 ≤ α) {q : ℝ≥0} (hq1 : (q:ℝ) ≤ 1)
    {β1 β2 : ℝ≥0} (hβ : β1 ≤ β2) :
    ∫ y, mixturePow α q (Real.exp (y - (β1:ℝ)/2)) ∂(gaussianReal 0 β1)
      ≤ ∫ y, mixturePow α q (Real.exp (y - (β2:ℝ)/2)) ∂(gaussianReal 0 β2) := by
  have hα0 : (0:ℝ) < α := lt_of_lt_of_le one_pos hα
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
  have hg2int := integrable_mixturePow_expShift hα hq1 β2
  have hg2int' : Integrable (fun w => mixturePow α q (Real.exp (w - (β2:ℝ)/2)))
      (Measure.map (fun p : ℝ × ℝ => p.1 + p.2)
        ((gaussianReal (0:ℝ) β1).prod (gaussianReal (0:ℝ) τ))) := by
    rw [hmap2]; exact hg2int
  have hjoint' : Integrable (fun p : ℝ × ℝ => mixturePow α q (Real.exp (p.1 + p.2 - (β2:ℝ)/2)))
      ((gaussianReal (0:ℝ) β1).prod (gaussianReal (0:ℝ) τ)) :=
    hg2int'.comp_measurable (by fun_prop)
  have hFubini : ∫ p, mixturePow α q (Real.exp (p.1 + p.2 - (β2:ℝ)/2))
        ∂((gaussianReal (0:ℝ) β1).prod (gaussianReal (0:ℝ) τ))
      = ∫ y, ∫ z, mixturePow α q (Real.exp (y + z - (β2:ℝ)/2))
          ∂(gaussianReal 0 τ) ∂(gaussianReal 0 β1) :=
    integral_prod _ hjoint'
  have hF2eq : ∫ y, mixturePow α q (Real.exp (y - (β2:ℝ)/2)) ∂(gaussianReal 0 β2)
      = ∫ p, mixturePow α q (Real.exp (p.1 + p.2 - (β2:ℝ)/2))
          ∂((gaussianReal (0:ℝ) β1).prod (gaussianReal (0:ℝ) τ)) := by
    rw [← hmap2, integral_map (by fun_prop) hg2int'.aestronglyMeasurable]
  have hae_int := hjoint'.prod_right_ae
  have hpointwise : ∀ᵐ y ∂(gaussianReal (0:ℝ) β1),
      mixturePow α q (Real.exp (y - (β1:ℝ)/2))
        ≤ ∫ z, mixturePow α q (Real.exp (y + z - (β2:ℝ)/2)) ∂(gaussianReal 0 τ) := by
    filter_upwards [hae_int] with y hz
    set m : ℝ := Real.exp (y - (β1:ℝ)/2) with hmdef
    have halg : ∀ z : ℝ, y + z - (β2:ℝ)/2 = (y - (β1:ℝ)/2) + (z - (τ:ℝ)/2) := by
      intro z
      have hβ2 : (β2:ℝ) = (β1:ℝ) + (τ:ℝ) := by exact_mod_cast hτ.symm
      rw [hβ2]; ring
    have hexpsplit : ∀ z : ℝ, Real.exp (y + z - (β2:ℝ)/2) = m * Real.exp (z - (τ:ℝ)/2) := by
      intro z; rw [halg z, Real.exp_add, hmdef]
    have hz' : Integrable (fun z => mixturePow α q (m * Real.exp (z - (τ:ℝ)/2)))
        (gaussianReal 0 τ) := by simpa [hexpsplit] using hz
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
    have hjensen := (convexOn_mixturePow hα hq1).map_integral_le
      (f := fun z => m * Real.exp (z - (τ:ℝ)/2))
      (continuous_mixturePow hα0.le).continuousOn isClosed_Ici hfmem hfint hz'
    have hintm : ∫ z, m * Real.exp (z - (τ:ℝ)/2) ∂(gaussianReal (0:ℝ) τ) = m := by
      rw [integral_const_mul, integral_exp_sub_half_gaussianReal τ, mul_one]
    rw [hintm] at hjensen
    calc mixturePow α q m
        ≤ ∫ z, mixturePow α q (m * Real.exp (z - (τ:ℝ)/2)) ∂(gaussianReal 0 τ) := hjensen
      _ = ∫ z, mixturePow α q (Real.exp (y + z - (β2:ℝ)/2)) ∂(gaussianReal 0 τ) := by
          apply integral_congr_ae; filter_upwards with z; rw [hexpsplit]
  have hmono := integral_mono_ae (integrable_mixturePow_expShift hα hq1 β1)
    (hjoint'.integral_prod_left) hpointwise
  rw [hF2eq, hFubini]
  exact hmono

/-- **Change of variables**: the mixture integrand against `𝒩(μ₀,v)` at displacement `Δ` is the
`β`-indexed integrand against `𝒩(0,β)`, `β := Δ²/v`. -/
lemma integral_mixturePow_gaussLR_eq_expShift {α : ℝ} (hα : 1 ≤ α) {q : ℝ≥0} (hq1 : (q:ℝ) ≤ 1)
    {μ₀ Δ : ℝ} {v : ℝ≥0} (hv : v ≠ 0) (β : ℝ≥0) (hβR : (β:ℝ) = Δ^2/v) :
    ∫ x, mixturePow α q (gaussLR μ₀ Δ v x) ∂(gaussianReal μ₀ v)
      = ∫ y, mixturePow α q (Real.exp (y - (β:ℝ)/2)) ∂(gaussianReal 0 β) := by
  have hα0 : (0:ℝ) < α := lt_of_lt_of_le one_pos hα
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
      (fun y => mixturePow α q (Real.exp (y - (β:ℝ)/2)))
      ((gaussianReal μ₀ v).map (fun x => c * (x - μ₀))) := by
    rw [hmapfull]
    exact (integrable_mixturePow_expShift hα hq1 β).aestronglyMeasurable
  rw [← hmapfull, integral_map (by fun_prop) hmeasg]
  apply integral_congr_ae
  filter_upwards with x
  congr 2
  unfold gaussLR
  rw [← hg x]

/-- **Monotonicity of the subsampled Gaussian in the sensitivity** `|Δ|` (Proposition A.25,
item 2). -/
theorem hellingerIntegral_sgMixture_real_mono {α : ℝ} (hα : 1 < α) {μ₀ : ℝ} {v : ℝ≥0} (hv : v ≠ 0)
    {q : ℝ≥0} (hq1 : (q:ℝ) < 1) {Δ1 Δ2 : ℝ} (hΔ : |Δ1| ≤ |Δ2|) :
    hellingerIntegral α ((1 - (q:ℝ≥0∞)) • gaussianReal μ₀ v + (q:ℝ≥0∞) • gaussianReal (μ₀ + Δ1) v)
        (gaussianReal μ₀ v)
      ≤ hellingerIntegral α ((1 - (q:ℝ≥0∞)) • gaussianReal μ₀ v + (q:ℝ≥0∞) • gaussianReal (μ₀ + Δ2) v)
        (gaussianReal μ₀ v) := by
  have hαle : (1:ℝ) ≤ α := hα.le
  have hqle1 : (q:ℝ) ≤ 1 := hq1.le
  have hqNNle1 : q ≤ 1 := by exact_mod_cast hqle1
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
  have hgoal : ∫ x, mixturePow α q (gaussLR μ₀ Δ1 v x) ∂gaussianReal μ₀ v
      ≤ ∫ x, mixturePow α q (gaussLR μ₀ Δ2 v x) ∂gaussianReal μ₀ v := by
    rw [integral_mixturePow_gaussLR_eq_expShift hαle hqle1 hv β1 hβ1R,
      integral_mixturePow_gaussLR_eq_expShift hαle hqle1 hv β2 hβ2R]
    exact mixturePow_integral_mono_variance hαle hqle1 hββ
  rw [hellingerIntegral_sgMixture_real hα hv q hqNNle1, hellingerIntegral_sgMixture_real hα hv q hqNNle1]
  exact ENNReal.ofReal_le_ofReal (by simpa [mixturePow] using hgoal)
