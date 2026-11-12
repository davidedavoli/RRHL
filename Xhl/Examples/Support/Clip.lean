import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Clipping, spending part of a displacement, and splitting on presence

* `clipV C v`: `v` clipped to norm `C` (`norm_clipV_le`).
* `pullv v a`: the part of a displacement `v` a step spends, of norm `min a ‖v‖`; the
  residual `v − pullv v a` is bounded by `norm_sub_pullv_le`.
* `apply_option_split`: a function of a `⊥`-extended record as a branch on presence, the
  form in which the case studies state measurability without a measurable structure on
  the option type.
-/

open MeasureTheory

namespace Continuous

/-! ## Clipping to a norm bound -/

/-- Clipping to norm `C`. -/
noncomputable def clipV {d : ℕ} (C : ℝ) (v : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  if ‖v‖ ≤ C then v else (C / ‖v‖) • v

lemma norm_clipV_le {d : ℕ} {C : ℝ} (hC : 0 ≤ C) (v : EuclideanSpace ℝ (Fin d)) :
    ‖clipV C v‖ ≤ C := by
  unfold clipV
  split_ifs with h
  · exact h
  · rw [not_le] at h
    have hv : 0 < ‖v‖ := lt_of_le_of_lt hC h
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hC hv.le), div_mul_cancel₀ _ hv.ne']

/-- Clipping the zero vector gives the zero vector, at any radius. -/
@[simp] lemma clipV_zero {d : ℕ} (C : ℝ) : clipV (d := d) C 0 = 0 := by
  unfold clipV; split_ifs <;> simp

lemma measurable_clipV {d : ℕ} (C : ℝ) : Measurable (clipV (d := d) C) :=
  Measurable.ite (measurableSet_le measurable_norm measurable_const) measurable_id
    ((measurable_const.div measurable_norm).smul measurable_id)

/-! ## Spending part of a displacement -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The capped pull vector: move distance `min a ‖v‖` along `v`. -/
noncomputable def pullv (v : E) (a : ℝ) : E := (min a ‖v‖ / ‖v‖) • v

@[simp] lemma pullv_zero (a : ℝ) : pullv (0 : E) a = 0 := by simp [pullv]

lemma norm_pullv_le {v : E} {a : ℝ} (ha : 0 ≤ a) : ‖pullv v a‖ ≤ a := by
  rcases eq_or_ne v 0 with rfl | hv
  · simpa using ha
  · have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hcoef : 0 ≤ min a ‖v‖ / ‖v‖ := div_nonneg (le_min ha hvpos.le) hvpos.le
    rw [pullv, norm_smul, Real.norm_eq_abs, abs_of_nonneg hcoef, div_mul_cancel₀ _ hvpos.ne']
    exact min_le_left a ‖v‖

lemma norm_sub_pullv {v : E} {a : ℝ} (ha : 0 ≤ a) : ‖v - pullv v a‖ = ‖v‖ - min a ‖v‖ := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp [min_eq_right ha]
  · have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hle1 : min a ‖v‖ / ‖v‖ ≤ 1 := by rw [div_le_one hvpos]; exact min_le_right a ‖v‖
    have hcoef : 0 ≤ min a ‖v‖ / ‖v‖ := div_nonneg (le_min ha hvpos.le) hvpos.le
    have h : v - pullv v a = (1 - min a ‖v‖ / ‖v‖) • v := by rw [pullv, sub_smul, one_smul]
    rw [h, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith), sub_mul, one_mul,
      div_mul_cancel₀ _ hvpos.ne']

/-- **The residual bound, as the sampling rule uses it.**  If the displacement to be spent
    on has norm at most `zc` and the step spends `a`, the residual fits in any `z'` above
    both `zc − a` and `0`. -/
lemma norm_sub_pullv_le {v : E} {a zc z' : ℝ} (ha : 0 ≤ a) (hv : ‖v‖ ≤ zc)
    (hz' : zc - a ≤ z') (hz'0 : 0 ≤ z') : ‖v - pullv v a‖ ≤ z' := by
  rw [norm_sub_pullv ha]
  rcases le_total a ‖v‖ with h | h
  · rw [min_eq_left h]; linarith
  · rw [min_eq_right h]; simpa using hz'0

/-! ## Splitting a `⊥`-extended record on presence -/

/-- **A `⊥`-extended record, split on presence.**  If `g none = 0` then
    `g o = if o.isSome then g (some (o.getD 0)) else 0`, which mentions the option only
    through `isSome` and `getD 0`. -/
lemma apply_option_split {β γ : Type*} [Zero β] [Zero γ] {g : Option β → γ}
    (hbot : g none = 0) (o : Option β) :
    g o = if o.isSome then g (some (o.getD 0)) else 0 := by
  cases o with
  | none => simpa using hbot
  | some y => simp

end Continuous
