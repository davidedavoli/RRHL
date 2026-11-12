import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Analysis.Convex.Continuous
import Xhl.Duality.Discrete.Distr
import Xhl.Duality.Discrete.MaxCoupling
import Xhl.Duality.Discrete.Total
import Mathlib.InformationTheory.KullbackLeibler.KLFun
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Xhl.Duality.Discrete.Coupling
import Xhl.Duality.Discrete.Range

open ENNReal Classical

namespace DStd

/-!
# The discrete Hellinger integral and the two-witness Rényi lifting

* `hRen α μ ν = ∑' x, μ(x)^α · ν(x)^{1−α}` — the Hellinger integral of two discrete
  sub-distributions;
* `tsum_rpow_mul_rpow_le` — superadditivity of `a^α b^{1−α}` over countable sums, with no
  mass hypothesis (Hölder against the counting measure);
* `FMulWitness`, `FLiftMul` — the two-witness lifting, at budget `η`.
-/

open ENNReal Classical Distr Range

namespace Distr

variable {A B C D : Type}

/-!
## Superadditivity of the convex perspective
-/

/-- The counting-measure Hölder inequality for `tsum`s in `ℝ≥0∞`, general
    conjugate exponents. -/
private lemma tsum_holder {ι : Type} (u v : ι → ℝ≥0∞) {p q : ℝ}
    (hpq : p.HolderConjugate q) :
    ∑' i, u i * v i
      ≤ (∑' i, u i ^ p) ^ (1 / p) * (∑' i, v i ^ q) ^ (1 / q) := by
  let : MeasurableSpace ι := ⊤
  have hmeas : ∀ h : ι → ℝ≥0∞, Measurable h :=
    fun h _ _ => MeasurableSpace.measurableSet_top
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq (MeasureTheory.Measure.count (α := ι))
    hpq (hmeas u).aemeasurable (hmeas v).aemeasurable
  rwa [MeasureTheory.lintegral_count' (hmeas _),
    MeasureTheory.lintegral_count' (hmeas _),
    MeasureTheory.lintegral_count' (hmeas _)] at hH

private lemma rpow_ne_zero_of_ne_zero {x : ℝ≥0∞} (hx : x ≠ 0) {y : ℝ}
    (hy : 0 < y) : x ^ y ≠ 0 := by
  rw [Ne, ENNReal.rpow_eq_zero_iff]
  push Not
  exact ⟨fun h => absurd h hx, fun _ => by linarith⟩

private lemma rpow_ne_zero_of_ne_zero_ne_top {x : ℝ≥0∞} (hx0 : x ≠ 0)
    (hxt : x ≠ ⊤) (y : ℝ) : x ^ y ≠ 0 := by
  rw [Ne, ENNReal.rpow_eq_zero_iff]
  push Not
  exact ⟨fun h => absurd h hx0, fun h => absurd h hxt⟩

private lemma rpow_ne_top_of_ne_zero_ne_top {x : ℝ≥0∞} (hx0 : x ≠ 0)
    (hxt : x ≠ ⊤) (y : ℝ) : x ^ y ≠ ⊤ := by
  rw [Ne, ENNReal.rpow_eq_top_iff]
  push Not
  exact ⟨fun h => absurd h hx0, fun h => absurd h hxt⟩

/-- **Superadditivity of `a^α b^{1−α}`** (`α > 1`), countable form: the grouping
    inequality behind data processing.  No support or mass hypotheses. -/
lemma tsum_rpow_mul_rpow_le {ι : Type} (a b : ι → ℝ≥0∞) {α : ℝ} (hα : 1 < α) :
    (∑' i, a i) ^ α * (∑' i, b i) ^ (1 - α)
      ≤ ∑' i, a i ^ α * b i ^ (1 - α) := by
  have hα0 : (0 : ℝ) < α := lt_trans one_pos hα
  set R := ∑' i, a i ^ α * b i ^ (1 - α) with hR
  by_cases hbad : ∃ i, b i = 0 ∧ a i ≠ 0
  · obtain ⟨i₀, hb0, ha0⟩ := hbad
    have hterm : a i₀ ^ α * b i₀ ^ (1 - α) = ⊤ := by
      rw [hb0, ENNReal.zero_rpow_of_neg (by linarith)]
      exact ENNReal.mul_top (rpow_ne_zero_of_ne_zero ha0 hα0)
    have hRtop : R = ⊤ := le_antisymm le_top (hR ▸ hterm ▸ ENNReal.le_tsum i₀)
    rw [hRtop]; exact le_top
  push Not at hbad
  set S := ∑' i, b i with hS
  rcases eq_or_ne S 0 with hS0 | hSne
  · have ha0 : ∀ i, a i = 0 := fun i => hbad i (ENNReal.tsum_eq_zero.mp hS0 i)
    rw [ENNReal.tsum_eq_zero.mpr ha0, ENNReal.zero_rpow_of_pos hα0, zero_mul]
    exact zero_le
  rcases eq_or_ne S ⊤ with hStop | hStop
  · rw [hStop, ENNReal.top_rpow_of_neg (by linarith), mul_zero]
    exact zero_le
  have hbtop : ∀ i, b i ≠ ⊤ := fun i h =>
    hStop (le_antisymm le_top (h ▸ ENNReal.le_tsum i))
  by_cases hatop : ∃ i, a i = ⊤
  · obtain ⟨i₀, hai⟩ := hatop
    have hbi0 : b i₀ ≠ 0 := by
      intro h
      have hz := hbad i₀ h
      rw [hai] at hz
      exact ENNReal.top_ne_zero hz
    have hterm : a i₀ ^ α * b i₀ ^ (1 - α) = ⊤ := by
      rw [hai, ENNReal.top_rpow_of_pos hα0,
        ENNReal.top_mul (rpow_ne_zero_of_ne_zero_ne_top hbi0 (hbtop i₀) _)]
    have hRtop : R = ⊤ := le_antisymm le_top (hR ▸ hterm ▸ ENNReal.le_tsum i₀)
    rw [hRtop]; exact le_top
  push Not at hatop
  set q : ℝ := α / (α - 1) with hq
  have hqpos : 0 < q := by rw [hq]; exact div_pos hα0 (by linarith)
  have hαne : α ≠ 0 := hα0.ne'
  have hαm1ne : α - 1 ≠ 0 := by linarith
  have hpq : α.HolderConjugate q := by
    rw [Real.holderConjugate_iff]
    refine ⟨hα, ?_⟩
    rw [hq, inv_div]
    field_simp
    ring
  have huv : ∀ i, (a i ^ α * b i ^ (1 - α)) ^ (1 / α) * b i ^ (1 / q) = a i := by
    intro i
    by_cases hb0 : b i = 0
    · rw [hb0, hbad i hb0, ENNReal.zero_rpow_of_pos hα0, zero_mul,
        ENNReal.zero_rpow_of_pos (one_div_pos.mpr hα0), zero_mul]
    · rw [ENNReal.mul_rpow_of_ne_top
          (ENNReal.rpow_ne_top_of_nonneg hα0.le (hatop i))
          (rpow_ne_top_of_ne_zero_ne_top hb0 (hbtop i) _),
        ← ENNReal.rpow_mul (a i), ← ENNReal.rpow_mul (b i),
        mul_one_div_cancel hα0.ne', ENNReal.rpow_one, mul_assoc,
        ← ENNReal.rpow_add _ _ hb0 (hbtop i),
        show (1 - α) * (1 / α) + 1 / q = 0 by
          rw [hq, one_div, one_div, inv_div]; field_simp; ring,
        ENNReal.rpow_zero, mul_one]
  have hup : ∀ i, ((a i ^ α * b i ^ (1 - α)) ^ (1 / α)) ^ α
      = a i ^ α * b i ^ (1 - α) := by
    intro i
    rw [← ENNReal.rpow_mul, one_div_mul_cancel hα0.ne', ENNReal.rpow_one]
  have hvq : ∀ i, (b i ^ (1 / q)) ^ q = b i := by
    intro i
    rw [← ENNReal.rpow_mul, one_div_mul_cancel hqpos.ne', ENNReal.rpow_one]
  have hHold := tsum_holder (fun i => (a i ^ α * b i ^ (1 - α)) ^ (1 / α))
    (fun i => b i ^ (1 / q)) hpq
  simp only [huv, hup, hvq] at hHold
  rw [← hR, ← hS] at hHold
  have hkey : (∑' i, a i) ^ α ≤ R * S ^ (α - 1) := by
    calc (∑' i, a i) ^ α
        ≤ (R ^ (1 / α) * S ^ (1 / q)) ^ α :=
          ENNReal.rpow_le_rpow hHold hα0.le
      _ = R * S ^ (α - 1) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hα0.le, ← ENNReal.rpow_mul,
            ← ENNReal.rpow_mul, one_div_mul_cancel hα0.ne', ENNReal.rpow_one]
          congr 1
          rw [hq, one_div, inv_div]
          field_simp
  calc (∑' i, a i) ^ α * S ^ (1 - α)
      ≤ R * S ^ (α - 1) * S ^ (1 - α) := _root_.mul_le_mul_left hkey _
    _ = R := by
        rw [mul_assoc, ← ENNReal.rpow_add _ _ hSne hStop,
          show (α - 1) + (1 - α) = 0 by ring, ENNReal.rpow_zero, mul_one]

/-!
## The Hellinger integral
-/

/-- The **Hellinger integral** `hRen α μ ν = ∑' x, μ(x)^α ν(x)^{1−α}` of discrete
    sub-distributions. -/
noncomputable def hRen (α : ℝ) (μ ν : Distr A) : ℝ≥0∞ :=
  ∑' x, μ.mass x ^ α * ν.mass x ^ (1 - α)

/-!
## The two-witness lifting
-/

/-- Witness pair for the two-witness Rényi lifting: marginals, support, and the budget
    `hRen α w.1 w.2 ≤ η`. -/
def FMulWitness (α : ℝ) (R : A → B → Prop) (η : ℝ≥0∞)
    (μ₁ : Distr A) (μ₂ : Distr B) (w : Distr (A × B) × Distr (A × B)) : Prop :=
  w.1.fst = μ₁ ∧ w.2.snd = μ₂ ∧
  range (fun p => R p.1 p.2) w.1 ∧ range (fun p => R p.1 p.2) w.2 ∧
  hRen α w.1 w.2 ≤ η

/-- The two-witness Rényi lifting. -/
def FLiftMul (α : ℝ) (R : A → B → Prop) (η : ℝ≥0∞)
    (μ₁ : Distr A) (μ₂ : Distr B) : Prop :=
  ∃ w, FMulWitness α R η μ₁ μ₂ w

end Distr

end DStd
