import Xhl.Divergence.HellingerIntegral
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Weak lower semicontinuity of the Hellinger integral

For a finite Borel measure `μ₂` on a (pseudo)metric space, the map
`ν ↦ hellingerIntegral α ν μ₂` on finite measures is lower semicontinuous for the weak
topology (`hellingerIntegral_lsc`).  It carries the budget of approximate witnesses to
their limit in the strong duality theorem (Theorem C.1).

The proof uses one bounded continuous test per point, not a supremum.

* **Tangent bound** (`tangent_bound`): for every `g ≥ 0`,
  `α ∫ g^{α−1} dν ≤ hellingerIntegral α ν μ₂ + (α−1) ∫ g^α dμ₂`.  It is Young's inequality
  `α x t^{α−1} ≤ x^α + (α−1) t^α` (`young_rpow`) applied to `x = dν/dμ₂`,
  `t = g`, and trivial when `ν` is not absolutely continuous (the value is `⊤`).
* **A strict test at each point**: if `y < hellingerIntegral α ν₀ μ₂`, some
  bounded continuous `g` satisfies `y + (α−1) ∫ g^α dμ₂ < α ∫ g^{α−1} dν₀`.
  When `ν₀ ≪ μ₂`, truncate the density at `N`, approximate the truncation by
  bounded continuous functions in `L¹(μ₂)` (Mathlib's density theorem stands in
  for Lusin's), pass to an a.e. convergent subsequence, clip to `[0, N]`, and
  conclude by dominated convergence (`exists_test_ac`).  Otherwise take a closed
  set of positive `ν₀`-mass and zero `μ₂`-mass, and a tall, narrow bump on it
  (`exists_test_sing`).
* Since `ν ↦ ∫ g^{α−1} dν` is weakly continuous (`continuous_lintegral_rpow`),
  the strict inequality persists near `ν₀`, and the tangent bound turns it into
  `y < hellingerIntegral α ν μ₂`.
-/

open MeasureTheory ENNReal Filter Topology
open scoped NNReal

namespace Continuous

/-!
## Young's inequality and the tangent bound
-/

/-- Young's inequality in the form `α x t^{α−1} ≤ x^α + (α−1) t^α`, for finite
    `x, t ∈ ℝ≥0∞`. -/
lemma young_rpow {α : ℝ} (hα : 1 < α) {x t : ℝ≥0∞} (hx : x ≠ ⊤) (ht : t ≠ ⊤) :
    ENNReal.ofReal α * (x * t ^ (α - 1)) ≤ x ^ α + ENNReal.ofReal (α - 1) * t ^ α := by
  have hα0 : 0 < α := by linarith
  have hα1 : 0 < α - 1 := by linarith
  obtain ⟨a, ha, rfl⟩ : ∃ a, 0 ≤ a ∧ x = ENNReal.ofReal a :=
    ⟨x.toReal, ENNReal.toReal_nonneg, (ENNReal.ofReal_toReal hx).symm⟩
  obtain ⟨s, hs, rfl⟩ : ∃ s, 0 ≤ s ∧ t = ENNReal.ofReal s :=
    ⟨t.toReal, ENNReal.toReal_nonneg, (ENNReal.ofReal_toReal ht).symm⟩
  have hpq : α.HolderConjugate (α / (α - 1)) := by
    rw [Real.holderConjugate_iff]
    refine ⟨hα, ?_⟩
    rw [inv_div]
    field_simp
    ring
  have hy := Real.young_inequality_of_nonneg ha (Real.rpow_nonneg hs (α - 1)) hpq
  have hpow : (s ^ (α - 1)) ^ (α / (α - 1)) = s ^ α := by
    rw [← Real.rpow_mul hs]
    congr 1
    field_simp
  rw [hpow] at hy
  have hreal : α * (a * s ^ (α - 1)) ≤ a ^ α + (α - 1) * s ^ α := by
    calc α * (a * s ^ (α - 1)) ≤ α * (a ^ α / α + s ^ α / (α / (α - 1))) :=
          mul_le_mul_of_nonneg_left hy hα0.le
      _ = a ^ α + (α - 1) * s ^ α := by field_simp
  rw [ENNReal.ofReal_rpow_of_nonneg hs hα1.le, ENNReal.ofReal_rpow_of_nonneg ha hα0.le,
    ENNReal.ofReal_rpow_of_nonneg hs hα0.le, ← ENNReal.ofReal_mul ha, ← ENNReal.ofReal_mul hα0.le,
    ← ENNReal.ofReal_mul hα1.le, ← ENNReal.ofReal_add (Real.rpow_nonneg ha α)
      (mul_nonneg hα1.le (Real.rpow_nonneg hs α))]
  exact ENNReal.ofReal_le_ofReal hreal

variable {B : Type*} [MeasurableSpace B]

/-- **Tangent bound**: for every measurable `g ≥ 0`,
    `α ∫ g^{α−1} dν ≤ hellingerIntegral α ν μ₂ + (α−1) ∫ g^α dμ₂`. -/
theorem tangent_bound {α : ℝ} (hα : 1 < α) (ν μ₂ : Measure B) [IsFiniteMeasure ν]
    [IsFiniteMeasure μ₂] (g : B → ℝ≥0) (hg : Measurable g) :
    ENNReal.ofReal α * ∫⁻ x, (g x : ℝ≥0∞) ^ (α - 1) ∂ν
      ≤ hellingerIntegral α ν μ₂ + ENNReal.ofReal (α - 1) * ∫⁻ x, (g x : ℝ≥0∞) ^ α ∂μ₂ := by
  by_cases hac : ν ≪ μ₂
  · have hgm : Measurable fun x => (g x : ℝ≥0∞) := measurable_coe_nnreal_ennreal.comp hg
    have hφ : Measurable fun x => (g x : ℝ≥0∞) ^ (α - 1) := hgm.pow_const _
    have hψ : Measurable fun x => (g x : ℝ≥0∞) ^ α := hgm.pow_const _
    have hr : Measurable fun x => ν.rnDeriv μ₂ x ^ α := (Measure.measurable_rnDeriv ν μ₂).pow_const _
    have hrφ : Measurable fun x => ν.rnDeriv μ₂ x * (g x : ℝ≥0∞) ^ (α - 1) :=
      (Measure.measurable_rnDeriv ν μ₂).mul hφ
    rw [hellingerIntegral_eq_lintegral_rnDeriv ν μ₂ hac, ← lintegral_rnDeriv_mul hac hφ.aemeasurable,
      ← lintegral_const_mul (ENNReal.ofReal α) hrφ,
      ← lintegral_const_mul (ENNReal.ofReal (α - 1)) hψ, ← lintegral_add_left hr]
    refine lintegral_mono_ae ?_
    filter_upwards [Measure.rnDeriv_lt_top ν μ₂] with x hx
    exact young_rpow hα hx.ne ENNReal.coe_ne_top
  · rw [hellingerIntegral_eq_top_of_not_ac ν μ₂ hac, top_add]
    exact le_top

/-- The integral of a power of a bounded function against a finite measure is finite. -/
lemma lintegral_rpow_ne_top {β : ℝ} (hβ : 0 ≤ β) (μ : Measure B) [IsFiniteMeasure μ]
    (g : B → ℝ≥0) (N : ℝ≥0) (hgN : ∀ x, g x ≤ N) :
    ∫⁻ x, (g x : ℝ≥0∞) ^ β ∂μ ≠ ⊤ := by
  refine ne_top_of_le_ne_top (b := ∫⁻ _, (N : ℝ≥0∞) ^ β ∂μ) ?_
    (lintegral_mono fun x => ENNReal.rpow_le_rpow (ENNReal.coe_le_coe.mpr (hgN x)) hβ)
  rw [lintegral_const]
  exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hβ ENNReal.coe_ne_top)
    (measure_ne_top μ _)

/-!
## Weak continuity of test integrals
-/

/-- For `g` bounded continuous and `β ≥ 0`, `ν ↦ ∫ g^β dν` is weakly continuous. -/
lemma continuous_lintegral_rpow [TopologicalSpace B] [OpensMeasurableSpace B] {β : ℝ}
    (hβ : 0 ≤ β) (g : B → ℝ≥0) (hg : Continuous g) (N : ℝ≥0) (hgN : ∀ x, g x ≤ N) :
    Continuous fun ν : FiniteMeasure B => ∫⁻ x, (g x : ℝ≥0∞) ^ β ∂(ν : Measure B) := by
  have hc : Continuous fun x => g x ^ β := (NNReal.continuous_rpow_const hβ).comp hg
  have hb : ∀ x, g x ^ β ≤ N ^ β := fun x => NNReal.rpow_le_rpow (hgN x) hβ
  let φ : BoundedContinuousFunction B ℝ≥0 :=
    BoundedContinuousFunction.mkOfBound ⟨fun x => g x ^ β, hc⟩ ((N ^ β : ℝ≥0) : ℝ)
      (fun x y => by
        rw [NNReal.dist_eq]
        change |((g x ^ β : ℝ≥0) : ℝ) - ((g y ^ β : ℝ≥0) : ℝ)| ≤ ((N ^ β : ℝ≥0) : ℝ)
        have h1 := hb x
        have h2 := hb y
        have h1' : ((g x ^ β : ℝ≥0) : ℝ) ≤ ((N ^ β : ℝ≥0) : ℝ) := by exact_mod_cast h1
        have h2' : ((g y ^ β : ℝ≥0) : ℝ) ≤ ((N ^ β : ℝ≥0) : ℝ) := by exact_mod_cast h2
        have h3 : (0 : ℝ) ≤ ((g x ^ β : ℝ≥0) : ℝ) := NNReal.coe_nonneg _
        have h4 : (0 : ℝ) ≤ ((g y ^ β : ℝ≥0) : ℝ) := NNReal.coe_nonneg _
        rw [abs_sub_le_iff]
        constructor <;> linarith)
  have heq : ∀ ν : FiniteMeasure B,
      ∫⁻ x, (g x : ℝ≥0∞) ^ β ∂(ν : Measure B) = (ν.testAgainstNN φ : ℝ≥0∞) := by
    intro ν
    rw [FiniteMeasure.testAgainstNN_coe_eq]
    refine lintegral_congr fun x => ?_
    show (g x : ℝ≥0∞) ^ β = ((g x ^ β : ℝ≥0) : ℝ≥0∞)
    rw [ENNReal.coe_rpow_of_nonneg _ hβ]
  simp_rw [heq]
  exact ENNReal.continuous_coe.comp (FiniteMeasure.continuous_testAgainstNN_eval φ)

/-!
## A strict test at each point
-/

/-- `x * x ^ (α - 1) = x ^ α` in `ℝ≥0∞`, for finite `x` (also at `0`). -/
lemma mul_rpow_sub_one' {α : ℝ} (hα : 1 < α) {x : ℝ≥0∞} (hx : x ≠ ⊤) :
    x ^ (α - 1) * x = x ^ α := by
  rcases eq_or_ne x 0 with h0 | h0
  · rw [h0, mul_zero, ENNReal.zero_rpow_of_pos (by linarith)]
  · calc x ^ (α - 1) * x = x ^ (α - 1) * x ^ (1 : ℝ) := by rw [ENNReal.rpow_one]
      _ = x ^ (α - 1 + 1) := (ENNReal.rpow_add _ _ h0 hx).symm
      _ = x ^ α := by rw [show α - 1 + 1 = α by ring]

/-- **The absolutely continuous case.** -/
theorem exists_test_ac [TopologicalSpace B] [NormalSpace B] [BorelSpace B] {α : ℝ} (hα : 1 < α)
    (μ₂ ν₀ : Measure B) [IsFiniteMeasure μ₂] [IsFiniteMeasure ν₀] [μ₂.WeaklyRegular]
    (hac : ν₀ ≪ μ₂) {y : ℝ≥0∞} (hy : y < hellingerIntegral α ν₀ μ₂) :
    ∃ g : B → ℝ≥0, ∃ N : ℝ≥0, Continuous g ∧ (∀ x, g x ≤ N) ∧
      y + ENNReal.ofReal (α - 1) * ∫⁻ x, (g x : ℝ≥0∞) ^ α ∂μ₂
        < ENNReal.ofReal α * ∫⁻ x, (g x : ℝ≥0∞) ^ (α - 1) ∂ν₀ := by
  have hα0 : 0 < α := by linarith
  have hα1 : 0 < α - 1 := by linarith
  set r := ν₀.rnDeriv μ₂ with hrdef
  have hrm : Measurable r := Measure.measurable_rnDeriv ν₀ μ₂
  -- truncation
  have hsup : ∫⁻ x, r x ^ α ∂μ₂ = ⨆ n : ℕ, ∫⁻ x, (min (r x) (n : ℝ≥0∞)) ^ α ∂μ₂ := by
    rw [← lintegral_iSup (fun n => (hrm.min measurable_const).pow_const α)
      (fun n m hnm x => ENNReal.rpow_le_rpow (min_le_min le_rfl (Nat.cast_le.mpr hnm)) hα0.le)]
    refine lintegral_congr fun x => ?_
    have h1 : r x = ⨆ n : ℕ, min (r x) (n : ℝ≥0∞) := by
      rw [show (⨆ n : ℕ, min (r x) (n : ℝ≥0∞)) = ⨆ n : ℕ, r x ⊓ (n : ℝ≥0∞) from rfl,
        ← inf_iSup_eq, ENNReal.iSup_natCast, inf_top_eq]
    conv_lhs => rw [h1]
    exact Monotone.map_iSup_of_continuousAt ENNReal.continuous_rpow_const.continuousAt
      (fun a b hab => ENNReal.rpow_le_rpow hab hα0.le) (ENNReal.zero_rpow_of_pos hα0)
  rw [hellingerIntegral_eq_lintegral_rnDeriv ν₀ μ₂ hac, hsup] at hy
  obtain ⟨n, hn⟩ := lt_iSup_iff.mp hy
  set N : ℝ≥0 := (n : ℝ≥0) with hNdef
  set s : B → ℝ≥0∞ := fun x => min (r x) (n : ℝ≥0∞) with hsdef
  have hsm : Measurable s := hrm.min measurable_const
  have hsN : ∀ x, s x ≤ N := fun x => by
    simp only [hsdef, hNdef]; exact min_le_right _ _
  have hstop : ∀ x, s x ≠ ⊤ := fun x => ne_top_of_le_ne_top ENNReal.coe_ne_top (hsN x)
  have hsr : ∀ x, s x ≤ r x := fun x => min_le_left _ _
  set S := ∫⁻ x, s x ^ α ∂μ₂ with hSdef
  have hSy : y < S := hn
  have hStop : S ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := ∫⁻ _, (N : ℝ≥0∞) ^ α ∂μ₂) ?_
      (lintegral_mono fun x => ENNReal.rpow_le_rpow (hsN x) hα0.le)
    rw [lintegral_const]
    exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hα0.le ENNReal.coe_ne_top)
      (measure_ne_top μ₂ _)
  -- continuous approximations of `s`, converging a.e.
  set sr : B → ℝ := fun x => (s x).toReal with hsrdef
  have hsrm : Measurable sr := hsm.ennreal_toReal
  have hsrL : MemLp sr 1 μ₂ := MemLp.of_bound hsrm.aestronglyMeasurable (N : ℝ)
    (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
      exact ENNReal.toReal_le_of_le_ofReal N.coe_nonneg
        (by rw [ENNReal.ofReal_coe_nnreal]; exact hsN x))
  have happrox : ∀ k : ℕ, ∃ G : BoundedContinuousFunction B ℝ,
      eLpNorm (sr - ⇑G) 1 μ₂ ≤ ENNReal.ofReal (1 / ((k : ℝ) + 1)) ∧ MemLp (⇑G) 1 μ₂ :=
    fun k => hsrL.exists_boundedContinuous_eLpNorm_sub_le ENNReal.one_ne_top
      (by rw [Ne, ENNReal.ofReal_eq_zero, not_le]; positivity)
  choose G hG using happrox
  have hlimL : Tendsto (fun k => eLpNorm ((G k : B → ℝ) - sr) 1 μ₂) atTop (𝓝 0) := by
    have h0 : Tendsto (fun k : ℕ => ENNReal.ofReal (1 / ((k : ℝ) + 1))) atTop (𝓝 0) := by
      rw [← ENNReal.ofReal_zero]
      exact ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0
      (fun k => zero_le) (fun k => ?_)
    rw [eLpNorm_sub_comm]
    exact (hG k).1
  have htim : TendstoInMeasure μ₂ (fun k => (G k : B → ℝ)) atTop sr :=
    tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero
      (fun k => (G k).continuous.aestronglyMeasurable) hsrm.aestronglyMeasurable hlimL
  obtain ⟨ns, -, hae⟩ := htim.exists_seq_tendsto_ae
  set h : ℕ → B → ℝ≥0 := fun i x => Real.toNNReal (min (G (ns i) x) (N : ℝ)) with hhdef
  have hcont : ∀ i, Continuous (h i) := fun i =>
    continuous_real_toNNReal.comp ((G (ns i)).continuous.min continuous_const)
  have hhm : ∀ i, Measurable (h i) := fun i => (hcont i).measurable
  have hle : ∀ i x, h i x ≤ N := fun i x => by
    simp only [hhdef]
    calc Real.toNNReal (min (G (ns i) x) (N : ℝ)) ≤ Real.toNNReal (N : ℝ) :=
          Real.toNNReal_le_toNNReal (min_le_right _ _)
      _ = N := Real.toNNReal_coe
  have hconv : ∀ᵐ x ∂μ₂, Tendsto (fun i => (h i x : ℝ≥0∞)) atTop (𝓝 (s x)) := by
    filter_upwards [hae] with x hx
    have h1 : Tendsto (fun i => ENNReal.ofReal (min (G (ns i) x) (N : ℝ))) atTop
        (𝓝 (ENNReal.ofReal (min (sr x) (N : ℝ)))) :=
      (ENNReal.continuous_ofReal.tendsto _).comp (hx.min tendsto_const_nhds)
    have h2 : ENNReal.ofReal (min (sr x) (N : ℝ)) = s x := by
      have hle' : sr x ≤ (N : ℝ) :=
        ENNReal.toReal_le_of_le_ofReal N.coe_nonneg
          (by rw [ENNReal.ofReal_coe_nnreal]; exact hsN x)
      rw [min_eq_left hle', hsrdef, ENNReal.ofReal_toReal (hstop x)]
    rw [h2] at h1
    exact h1
  -- limits of the two sides
  have hbd1 : ∫⁻ _, (N : ℝ≥0∞) ^ (α - 1) * (N : ℝ≥0∞) ∂μ₂ ≠ ⊤ := by
    rw [lintegral_const]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_nonneg hα1.le ENNReal.coe_ne_top) ENNReal.coe_ne_top)
      (measure_ne_top μ₂ _)
  have hbd2 : ∫⁻ _, (N : ℝ≥0∞) ^ α ∂μ₂ ≠ ⊤ := by
    rw [lintegral_const]
    exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hα0.le ENNReal.coe_ne_top)
      (measure_ne_top μ₂ _)
  have hL : Tendsto (fun i => ∫⁻ x, (h i x : ℝ≥0∞) ^ (α - 1) * s x ∂μ₂) atTop (𝓝 S) := by
    have := tendsto_lintegral_of_dominated_convergence (μ := μ₂)
      (fun _ => (N : ℝ≥0∞) ^ (α - 1) * (N : ℝ≥0∞))
      (fun i => ((measurable_coe_nnreal_ennreal.comp (hhm i)).pow_const _).mul hsm)
      (fun i => ae_of_all _ fun x => mul_le_mul'
        (ENNReal.rpow_le_rpow (ENNReal.coe_le_coe.mpr (hle i x)) hα1.le) (hsN x))
      hbd1
      (by
        filter_upwards [hconv] with x hx
        exact ENNReal.Tendsto.mul_const
          ((ENNReal.continuous_rpow_const.tendsto (s x)).comp hx) (Or.inr (hstop x)))
    have hlim_eq : ∫⁻ x, s x ^ (α - 1) * s x ∂μ₂ = S :=
      lintegral_congr fun x => mul_rpow_sub_one' hα (hstop x)
    rwa [hlim_eq] at this
  have hC : Tendsto (fun i => ∫⁻ x, (h i x : ℝ≥0∞) ^ α ∂μ₂) atTop (𝓝 S) :=
    tendsto_lintegral_of_dominated_convergence (μ := μ₂) (fun _ => (N : ℝ≥0∞) ^ α)
      (fun i => (measurable_coe_nnreal_ennreal.comp (hhm i)).pow_const _)
      (fun i => ae_of_all _ fun x =>
        ENNReal.rpow_le_rpow (ENNReal.coe_le_coe.mpr (hle i x)) hα0.le)
      hbd2
      (by
        filter_upwards [hconv] with x hx
        exact (ENNReal.continuous_rpow_const.tendsto (s x)).comp hx)
  have hlimR : Tendsto (fun i => ENNReal.ofReal α * ∫⁻ x, (h i x : ℝ≥0∞) ^ (α - 1) * s x ∂μ₂)
      atTop (𝓝 (ENNReal.ofReal α * S)) :=
    ENNReal.Tendsto.const_mul hL (Or.inr ENNReal.ofReal_ne_top)
  have hlimLft : Tendsto (fun i => y + ENNReal.ofReal (α - 1) * ∫⁻ x, (h i x : ℝ≥0∞) ^ α ∂μ₂)
      atTop (𝓝 (y + ENNReal.ofReal (α - 1) * S)) :=
    tendsto_const_nhds.add (ENNReal.Tendsto.const_mul hC (Or.inr ENNReal.ofReal_ne_top))
  have hstrict : y + ENNReal.ofReal (α - 1) * S < ENNReal.ofReal α * S := by
    have hsplit : ENNReal.ofReal α * S = S + ENNReal.ofReal (α - 1) * S := by
      rw [show α = 1 + (α - 1) by ring, ENNReal.ofReal_add zero_le_one hα1.le,
        ENNReal.ofReal_one, add_mul, one_mul, show 1 + (α - 1) - 1 = α - 1 by ring]
    rw [hsplit]
    exact ENNReal.add_lt_add_right (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hStop) hSy
  obtain ⟨i, hi⟩ := (hlimLft.eventually_lt hlimR hstrict).exists
  refine ⟨h i, N, hcont i, hle i, lt_of_lt_of_le hi ?_⟩
  refine mul_le_mul' le_rfl ?_
  have hφ : Measurable fun x => (h i x : ℝ≥0∞) ^ (α - 1) :=
    (measurable_coe_nnreal_ennreal.comp (hhm i)).pow_const _
  rw [← lintegral_rnDeriv_mul hac hφ.aemeasurable]
  exact lintegral_mono fun x => by
    rw [mul_comm (r x)]
    exact mul_le_mul' le_rfl (hsr x)

/-- **The singular case.** -/
theorem exists_test_sing [PseudoMetricSpace B] [BorelSpace B] {α : ℝ} (hα : 1 < α)
    (μ₂ ν₀ : Measure B) [IsFiniteMeasure μ₂] [IsFiniteMeasure ν₀]
    (hac : ¬ ν₀ ≪ μ₂) {y : ℝ≥0∞} (hy : y ≠ ⊤) :
    ∃ g : B → ℝ≥0, ∃ N : ℝ≥0, Continuous g ∧ (∀ x, g x ≤ N) ∧
      y + ENNReal.ofReal (α - 1) * ∫⁻ x, (g x : ℝ≥0∞) ^ α ∂μ₂
        < ENNReal.ofReal α * ∫⁻ x, (g x : ℝ≥0∞) ^ (α - 1) ∂ν₀ := by
  have hα0 : 0 < α := by linarith
  have hα1 : 0 < α - 1 := by linarith
  -- a closed set of positive `ν₀`-mass and zero `μ₂`-mass
  obtain ⟨S, hSm, hS2, hS1⟩ : ∃ S, MeasurableSet S ∧ μ₂ S = 0 ∧ ν₀ S ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hac (Measure.AbsolutelyContinuous.mk fun S hS h0 => hcon S hS h0)
  obtain ⟨F, hFS, hFc, hFlt⟩ := hSm.exists_isClosed_lt_add (μ := ν₀) (measure_ne_top ν₀ S) hS1
  have hF1 : ν₀ F ≠ 0 := by
    intro h0
    rw [h0, zero_add] at hFlt
    exact lt_irrefl _ hFlt
  have hF2 : μ₂ F = 0 := measure_mono_null hFS hS2
  have hFne : F.Nonempty := Set.nonempty_iff_ne_empty.mpr fun h => hF1 (by rw [h, measure_empty])
  have hFm : MeasurableSet F := hFc.measurableSet
  -- the height of the bump
  set a := ENNReal.ofReal α * ν₀ F with hadef
  have ha0 : a ≠ 0 := mul_ne_zero (by rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact hα0) hF1
  have hatop : a ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top ν₀ F)
  set Y := y + 1 with hYdef
  have hYtop : Y ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨hy, ENNReal.one_ne_top⟩
  set T : ℝ≥0∞ := Y / a + 1 with hTdef
  have hTtop : T ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.div_ne_top hYtop ha0, ENNReal.one_ne_top⟩
  set t : ℝ≥0 := T.toNNReal ^ (1 / (α - 1)) with htdef
  have ht : (t : ℝ≥0∞) ^ (α - 1) = T := by
    rw [htdef, ENNReal.coe_rpow_of_nonneg _ (one_div_pos.mpr hα1).le, ← ENNReal.rpow_mul,
      one_div_mul_cancel hα1.ne', ENNReal.rpow_one, ENNReal.coe_toNNReal hTtop]
  have hYlt : Y < T * a := by
    rw [hTdef, add_mul, one_mul, ENNReal.div_mul_cancel ha0 hatop]
    exact ENNReal.lt_add_right hYtop ha0
  -- the width of the bump
  set K := ENNReal.ofReal (α - 1) * (t : ℝ≥0∞) ^ α with hKdef
  have hKtop : K ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.rpow_ne_top_of_nonneg hα0.le ENNReal.coe_ne_top)
  have hthick : Tendsto (fun δ => μ₂ (Metric.cthickening δ F)) (𝓝 0) (𝓝 0) := by
    have := tendsto_measure_cthickening_of_isClosed (μ := μ₂)
      ⟨1, one_pos, measure_ne_top μ₂ _⟩ hFc
    rwa [hF2] at this
  have hK0 : Tendsto (fun δ => K * μ₂ (Metric.cthickening δ F)) (𝓝 0) (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul hthick (Or.inr hKtop)
    rwa [mul_zero] at this
  obtain ⟨δ, hδK, hδpos⟩ := ((hK0.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))).eventually
    (gt_mem_nhds (zero_lt_one : (0 : ℝ≥0∞) < 1))).and self_mem_nhdsWithin |>.exists
  have hδ : (0 : ℝ) < δ := hδpos
  -- the bump
  set g : B → ℝ≥0 := fun x => Real.toNNReal ((t : ℝ) * (1 - Metric.infDist x F / δ)) with hgdef
  have hgc : Continuous g :=
    continuous_real_toNNReal.comp (continuous_const.mul
      (continuous_const.sub ((Metric.continuous_infDist_pt F).div_const δ)))
  have hgt : ∀ x, g x ≤ t := fun x => by
    simp only [hgdef]
    calc Real.toNNReal ((t : ℝ) * (1 - Metric.infDist x F / δ)) ≤ Real.toNNReal (t : ℝ) := by
          refine Real.toNNReal_le_toNNReal ?_
          have : 0 ≤ Metric.infDist x F / δ := div_nonneg Metric.infDist_nonneg hδ.le
          nlinarith [t.coe_nonneg]
      _ = t := Real.toNNReal_coe
  have hgF : ∀ x ∈ F, g x = t := fun x hx => by
    simp only [hgdef, Metric.infDist_zero_of_mem hx, zero_div, sub_zero, mul_one,
      Real.toNNReal_coe]
  have hg0 : ∀ x ∉ Metric.cthickening δ F, g x = 0 := by
    intro x hx
    by_contra hne
    apply hx
    have hpos : 0 < (t : ℝ) * (1 - Metric.infDist x F / δ) := by
      by_contra hle
      exact hne (Real.toNNReal_eq_zero.mpr (not_lt.mp hle))
    have h1 : Metric.infDist x F < δ := by
      have h2 : 0 < 1 - Metric.infDist x F / δ := pos_of_mul_pos_right hpos t.coe_nonneg
      rw [sub_pos, div_lt_one hδ] at h2
      exact h2
    obtain ⟨z, hz, hdz⟩ := (Metric.infDist_lt_iff hFne).mp h1
    exact Metric.mem_cthickening_of_dist_le x z δ F hz hdz.le
  -- the two integrals
  have hlow : (t : ℝ≥0∞) ^ (α - 1) * ν₀ F ≤ ∫⁻ x, (g x : ℝ≥0∞) ^ (α - 1) ∂ν₀ := by
    rw [← lintegral_indicator_const hFm]
    refine lintegral_mono fun x => ?_
    by_cases hx : x ∈ F
    · rw [Set.indicator_of_mem hx, hgF x hx]
    · rw [Set.indicator_of_notMem hx]; exact zero_le
  have hupp : ∫⁻ x, (g x : ℝ≥0∞) ^ α ∂μ₂
      ≤ (t : ℝ≥0∞) ^ α * μ₂ (Metric.cthickening δ F) := by
    rw [← lintegral_indicator_const Metric.isClosed_cthickening.measurableSet]
    refine lintegral_mono fun x => ?_
    by_cases hx : x ∈ Metric.cthickening δ F
    · rw [Set.indicator_of_mem hx]
      exact ENNReal.rpow_le_rpow (ENNReal.coe_le_coe.mpr (hgt x)) hα0.le
    · rw [Set.indicator_of_notMem hx, hg0 x hx, ENNReal.coe_zero,
        ENNReal.zero_rpow_of_pos hα0]
  refine ⟨g, t, hgc, hgt, ?_⟩
  calc y + ENNReal.ofReal (α - 1) * ∫⁻ x, (g x : ℝ≥0∞) ^ α ∂μ₂
      ≤ y + K * μ₂ (Metric.cthickening δ F) := by
        rw [hKdef, mul_assoc]
        exact add_le_add le_rfl (mul_le_mul' le_rfl hupp)
    _ < Y := ENNReal.add_lt_add_left hy hδK
    _ < T * a := hYlt
    _ = ENNReal.ofReal α * ((t : ℝ≥0∞) ^ (α - 1) * ν₀ F) := by
        rw [← ht, hadef]; ring
    _ ≤ ENNReal.ofReal α * ∫⁻ x, (g x : ℝ≥0∞) ^ (α - 1) ∂ν₀ := mul_le_mul' le_rfl hlow

/-!
## Lower semicontinuity
-/

/-- **Weak lower semicontinuity of the Hellinger integral**: for a finite Borel
    measure `μ₂` on a pseudometric space, `ν ↦ hellingerIntegral α ν μ₂` is lower
    semicontinuous on finite measures with the weak topology. -/
theorem hellingerIntegral_lsc [PseudoMetricSpace B] [BorelSpace B] {α : ℝ} (hα : 1 < α)
    (μ₂ : Measure B) [IsFiniteMeasure μ₂] :
    LowerSemicontinuous fun ν : FiniteMeasure B => hellingerIntegral α (ν : Measure B) μ₂ := by
  have hα1 : (0 : ℝ) ≤ α - 1 := by linarith
  intro ν₀ y hy
  obtain ⟨g, N, hgc, hgN, hstrict⟩ : ∃ g : B → ℝ≥0, ∃ N : ℝ≥0, Continuous g ∧ (∀ x, g x ≤ N) ∧
      y + ENNReal.ofReal (α - 1) * ∫⁻ x, (g x : ℝ≥0∞) ^ α ∂μ₂
        < ENNReal.ofReal α * ∫⁻ x, (g x : ℝ≥0∞) ^ (α - 1) ∂(ν₀ : Measure B) := by
    by_cases hac : (ν₀ : Measure B) ≪ μ₂
    · exact exists_test_ac hα μ₂ ν₀ hac hy
    · exact exists_test_sing hα μ₂ ν₀ hac (ne_top_of_lt hy)
  have hcont : Continuous fun ν : FiniteMeasure B =>
      ENNReal.ofReal α * ∫⁻ x, (g x : ℝ≥0∞) ^ (α - 1) ∂(ν : Measure B) :=
    (ENNReal.continuous_const_mul ENNReal.ofReal_ne_top).comp
      (continuous_lintegral_rpow hα1 g hgc N hgN)
  have hCtop : ENNReal.ofReal (α - 1) * ∫⁻ x, (g x : ℝ≥0∞) ^ α ∂μ₂ ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (lintegral_rpow_ne_top (by linarith) μ₂ g N hgN)
  filter_upwards [(hcont.tendsto ν₀).eventually (lt_mem_nhds hstrict)] with ν hν
  exact (ENNReal.add_lt_add_iff_right hCtop).mp
    (lt_of_lt_of_le hν (tangent_bound hα (ν : Measure B) μ₂ g hgc.measurable))

end Continuous
