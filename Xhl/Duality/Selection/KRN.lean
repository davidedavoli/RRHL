import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Polish

/-!
# The Kuratowski–Ryll-Nardzewski measurable selection theorem

Let `α` be a measurable space and `β` a complete separable metric space with its Borel
σ-algebra.  A correspondence `F : α → Set β` is *weakly measurable* if for every open `U`
the set of `x` such that `F x` meets `U` is measurable.

`exists_measurable_selection`: a weakly measurable correspondence with closed non-empty
values has a measurable selector.

The proof is the classical one.  Fix a dense sequence `u`.  Measurable maps `g n : α → ℕ`
are built so that the ball of radius `2⁻ⁿ` around `u (g n x)` meets `F x`, and so that
consecutive centres are at distance less than `2⁻ⁿ + 2⁻⁽ⁿ⁺¹⁾`.  The centres converge, the
limit lies in `F x` because `F x` is closed, and it is measurable as a pointwise limit.
-/

open Set Filter Topology Metric TopologicalSpace

namespace Continuous

variable {α β : Type*} [MeasurableSpace α] [MetricSpace β] [SecondCountableTopology β]
  [MeasurableSpace β] [BorelSpace β]

/-- A correspondence is weakly measurable if the set of points whose value meets a given
    open set is measurable. -/
def WeaklyMeasurable (F : α → Set β) : Prop :=
  ∀ U : Set β, IsOpen U → MeasurableSet {x | (F x ∩ U).Nonempty}

section Step

variable [Nonempty β] {F : α → Set β}

open Classical in
/-- The first approximation. -/
lemma krn_base (hF : WeaklyMeasurable F) (hne : ∀ x, (F x).Nonempty) {r : ℝ} (hr : 0 < r) :
    ∃ g : α → ℕ, Measurable g ∧ ∀ x, (F x ∩ ball (denseSeq β (g x)) r).Nonempty := by
  have hp : ∀ x, ∃ k, (F x ∩ ball (denseSeq β k) r).Nonempty := by
    intro x
    obtain ⟨y, hy⟩ := hne x
    obtain ⟨k, hk⟩ := (denseRange_denseSeq β).exists_dist_lt y hr
    exact ⟨k, y, hy, mem_ball.mpr hk⟩
  refine ⟨fun x => Nat.find (hp x), measurable_find hp fun k => hF _ isOpen_ball, fun x => ?_⟩
  exact Nat.find_spec (hp x)

open Classical in
/-- The refinement step. -/
lemma krn_step (hF : WeaklyMeasurable F) {r r' : ℝ} (hr' : 0 < r') (g : α → ℕ)
    (hg : Measurable g) (hgF : ∀ x, (F x ∩ ball (denseSeq β (g x)) r).Nonempty) :
    ∃ g' : α → ℕ, Measurable g' ∧ (∀ x, (F x ∩ ball (denseSeq β (g' x)) r').Nonempty) ∧
      ∀ x, dist (denseSeq β (g x)) (denseSeq β (g' x)) < r + r' := by
  have hp : ∀ x, ∃ k,
      (F x ∩ (ball (denseSeq β (g x)) r ∩ ball (denseSeq β k) r')).Nonempty := by
    intro x
    obtain ⟨y, hyF, hyb⟩ := hgF x
    obtain ⟨k, hk⟩ := (denseRange_denseSeq β).exists_dist_lt y hr'
    exact ⟨k, y, hyF, hyb, mem_ball.mpr hk⟩
  have hm : ∀ k, MeasurableSet
      {x | (F x ∩ (ball (denseSeq β (g x)) r ∩ ball (denseSeq β k) r')).Nonempty} := by
    intro k
    have : {x | (F x ∩ (ball (denseSeq β (g x)) r ∩ ball (denseSeq β k) r')).Nonempty}
        = ⋃ m, (g ⁻¹' {m}) ∩
            {x | (F x ∩ (ball (denseSeq β m) r ∩ ball (denseSeq β k) r')).Nonempty} := by
      ext x
      simp only [mem_setOf_eq, mem_iUnion, mem_inter_iff, mem_preimage, mem_singleton_iff]
      constructor
      · intro h; exact ⟨g x, rfl, h⟩
      · rintro ⟨m, hm, h⟩; rw [hm]; exact h
    rw [this]
    exact MeasurableSet.iUnion fun m =>
      (hg (measurableSet_singleton m)).inter (hF _ (isOpen_ball.inter isOpen_ball))
  refine ⟨fun x => Nat.find (hp x), measurable_find hp hm, fun x => ?_, fun x => ?_⟩
  · obtain ⟨y, hyF, -, hy2⟩ := Nat.find_spec (hp x)
    exact ⟨y, hyF, hy2⟩
  · obtain ⟨y, -, hy1, hy2⟩ := Nat.find_spec (hp x)
    calc dist (denseSeq β (g x)) (denseSeq β (Nat.find (hp x)))
        ≤ dist (denseSeq β (g x)) y + dist y (denseSeq β (Nat.find (hp x))) := dist_triangle _ _ _
      _ < r + r' := add_lt_add (by rw [dist_comm]; exact mem_ball.mp hy1) (mem_ball.mp hy2)

end Step

/-- **Kuratowski–Ryll-Nardzewski.**  A weakly measurable correspondence with closed
    non-empty values in a complete separable metric space has a measurable selector. -/
theorem exists_measurable_selection [CompleteSpace β] (F : α → Set β)
    (hc : ∀ x, IsClosed (F x)) (hne : ∀ x, (F x).Nonempty) (hF : WeaklyMeasurable F) :
    ∃ f : α → β, Measurable f ∧ ∀ x, f x ∈ F x := by
  rcases isEmpty_or_nonempty α with hα | hα
  · exact ⟨fun x => isEmptyElim x, measurable_of_empty _, fun x => isEmptyElim x⟩
  haveI : Nonempty β := let ⟨x⟩ := hα; (hne x).to_subtype.map Subtype.val
  have hpos : ∀ n : ℕ, (0 : ℝ) < (1 / 2) ^ n := fun n => by positivity
  -- the sequence of approximations
  let S : ℕ → Type _ := fun n =>
    {g : α → ℕ // Measurable g ∧ ∀ x, (F x ∩ ball (denseSeq β (g x)) ((1 / 2 : ℝ) ^ n)).Nonempty}
  let base : S 0 :=
    ⟨Classical.choose (krn_base hF hne (hpos 0)), Classical.choose_spec (krn_base hF hne (hpos 0))⟩
  let step : ∀ n, S n → S (n + 1) := fun n g =>
    ⟨Classical.choose (krn_step hF (hpos (n + 1)) g.1 g.2.1 g.2.2),
      (Classical.choose_spec (krn_step hF (hpos (n + 1)) g.1 g.2.1 g.2.2)).1,
      (Classical.choose_spec (krn_step hF (hpos (n + 1)) g.1 g.2.1 g.2.2)).2.1⟩
  let seq : ∀ n, S n := fun n => Nat.rec base step n
  have hclose : ∀ n x, dist (denseSeq β ((seq n).1 x)) (denseSeq β ((seq (n + 1)).1 x))
      < (1 / 2 : ℝ) ^ n + (1 / 2 : ℝ) ^ (n + 1) := fun n x =>
    (Classical.choose_spec
      (krn_step hF (hpos (n + 1)) (seq n).1 (seq n).2.1 (seq n).2.2)).2.2 x
  set v : ℕ → α → β := fun n x => denseSeq β ((seq n).1 x) with hv
  have hvm : ∀ n, Measurable (v n) := fun n => (measurable_from_nat).comp (seq n).2.1
  have hcauchy : ∀ x, CauchySeq (fun n => v n x) := by
    intro x
    refine cauchySeq_of_le_geometric (1 / 2 : ℝ) 2 (by norm_num) fun n => ?_
    have h := (hclose n x).le
    have h2 : (1 / 2 : ℝ) ^ n + (1 / 2 : ℝ) ^ (n + 1) ≤ 2 * (1 / 2 : ℝ) ^ n := by
      rw [pow_succ]; nlinarith [hpos n]
    exact h.trans h2
  choose f hf using fun x => cauchySeq_tendsto_of_complete (hcauchy x)
  refine ⟨f, measurable_of_tendsto_metrizable hvm (tendsto_pi_nhds.mpr hf), fun x => ?_⟩
  -- the limit is in the closed set `F x`
  choose y hyF hyb using fun n => (seq n).2.2 x
  have hylim : Tendsto y atTop (𝓝 (f x)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    have hsum : Tendsto (fun n => (1 / 2 : ℝ) ^ n + dist (v n x) (f x)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
      have h2 := tendsto_iff_dist_tendsto_zero.mp (hf x)
      simpa using h1.add h2
    refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_) hsum
    calc dist (y n) (f x) ≤ dist (y n) (v n x) + dist (v n x) (f x) := dist_triangle _ _ _
      _ ≤ (1 / 2 : ℝ) ^ n + dist (v n x) (f x) := by
          have := (mem_ball.mp (hyb n)).le
          linarith
  exact (hc x).mem_of_tendsto hylim (Filter.Eventually.of_forall hyF)

end Continuous
