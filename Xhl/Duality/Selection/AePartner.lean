import Xhl.Duality.Selection.PartnerSelection
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Measurable partners almost everywhere

`exists_measurable_partner_ae`: let `S` be a closed subset of `A × B`, with `A` and `B`
Polish, and let `λ` be a finite measure on `B` such that `λ`-almost every `b` has a
partner `a` with `(a, b) ∈ S`.  Then a partner can be chosen measurably, for
`λ`-almost every `b`.  No compactness is assumed.

The proof is a capacitability argument.  `S` is Polish, hence the continuous image
`g(ℕ → ℕ)`; write `h` for the second coordinate of `g`.  Bounding the coordinates of
`ℕ → ℕ` one at a time, continuity of `λ` from below on increasing (not necessarily
measurable) sets keeps `λ(h(·))` above a threshold `t < λ(B)` (`exists_box`); the box
`C` of all sequences below the chosen bounds is compact, and `h(C)` is the
intersection of the closures of the partial images (`mem_image_boxAll_of_mem_closure`),
so `λ(h(C)) ≥ t`.  On the compact set `h(C)` every target has a partner in the compact
set `g₁(C)`, so the Kuratowski–Ryll-Nardzewski theorem (`exists_measurable_partner`)
gives a measurable partner there.  Taking `t = λ(B) − 1/j` and gluing over `j` gives
the selector off a null set.
-/

open Set Filter Topology TopologicalSpace MeasureTheory ENNReal

namespace Continuous

section Boxes

/-- Sequences bounded by `n` on the first `k` coordinates. -/
def boxPre (n : ℕ → ℕ) (k : ℕ) : Set (ℕ → ℕ) := {y | ∀ i < k, y i ≤ n i}

/-- Sequences bounded by `n` everywhere. -/
def boxAll (n : ℕ → ℕ) : Set (ℕ → ℕ) := {y | ∀ i, y i ≤ n i}

lemma isCompact_boxAll (n : ℕ → ℕ) : IsCompact (boxAll n) := by
  have : boxAll n = Set.pi univ (fun i => Iic (n i)) := by
    ext y; simp only [boxAll, mem_setOf_eq, Set.mem_pi, mem_univ, mem_Iic, forall_const]
  rw [this]
  exact isCompact_univ_pi fun i => (Set.finite_Iic (n i)).isCompact

lemma boxPre_antitone (n : ℕ → ℕ) : Antitone (boxPre n) :=
  fun _ _ hkl _ hy i hi => hy i (lt_of_lt_of_le hi hkl)

/-- A box is contained in an open set as soon as one of its finite-prefix
    approximations is (a tube lemma for `ℕ → ℕ`). -/
lemma exists_boxPre_subset {n : ℕ → ℕ} {U : Set (ℕ → ℕ)} (hU : IsOpen U)
    (hC : boxAll n ⊆ U) : ∃ m, boxPre n m ⊆ U := by
  classical
  have hcyl : ∀ c ∈ boxAll n, ∃ k, PiNat.cylinder c k ⊆ U := by
    intro c hc
    obtain ⟨_, ⟨x, k, rfl⟩, hcx, hsub⟩ :=
      (PiNat.isTopologicalBasis_cylinders (fun _ : ℕ => ℕ)).exists_subset_of_mem_open (hC hc) hU
    refine ⟨k, ?_⟩
    rwa [PiNat.mem_cylinder_iff_eq.mp hcx]
  choose! k hk using hcyl
  obtain ⟨t, htC, hcover⟩ := (isCompact_boxAll n).elim_nhds_subcover
    (fun c => PiNat.cylinder c (k c))
    (fun c _ => (PiNat.isOpen_cylinder _ c (k c)).mem_nhds (PiNat.self_mem_cylinder c (k c)))
  refine ⟨t.sup k, fun y hy => ?_⟩
  set c' : ℕ → ℕ := fun i => if i < t.sup k then y i else 0 with hc'
  have hc'C : c' ∈ boxAll n := by
    intro i
    simp only [hc']
    split_ifs with hi
    · exact hy i hi
    · exact Nat.zero_le _
  obtain ⟨c, hct, hc'c⟩ := mem_iUnion₂.mp (hcover hc'C)
  refine hk c (htC c hct) (PiNat.mem_cylinder_iff.mpr fun i hi => ?_)
  have him : i < t.sup k := lt_of_lt_of_le hi (Finset.le_sup hct)
  have := PiNat.mem_cylinder_iff.mp hc'c i hi
  simp only [hc', if_pos him] at this
  exact this

variable {B : Type*} [MetricSpace B]

/-- The image of the box is the intersection of the closures of the images of its
    finite-prefix approximations. -/
lemma mem_image_boxAll_of_mem_closure {h : (ℕ → ℕ) → B} (hh : Continuous h) {n : ℕ → ℕ}
    {x : B} (hx : ∀ k, x ∈ closure (h '' boxPre n k)) : x ∈ h '' boxAll n := by
  by_contra hxC
  have hcl : IsClosed (h '' boxAll n) := ((isCompact_boxAll n).image hh).isClosed
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hcl.isOpen_compl x hxC
  set U : Set (ℕ → ℕ) := h ⁻¹' (Metric.closedBall x (r / 2))ᶜ with hUdef
  have hU : IsOpen U := Metric.isClosed_closedBall.isOpen_compl.preimage hh
  have hCU : boxAll n ⊆ U := by
    intro c hc hcb
    exact hball (Metric.closedBall_subset_ball (by linarith) hcb) ⟨c, hc, rfl⟩
  obtain ⟨m, hm⟩ := exists_boxPre_subset hU hCU
  obtain ⟨b, ⟨y, hy, rfl⟩, hd⟩ := Metric.mem_closure_iff.mp (hx m) (r / 2) (by linarith)
  exact hm hy (Metric.mem_closedBall.mpr (by rw [dist_comm]; linarith))

variable [MeasurableSpace B] [OpensMeasurableSpace B]

/-- **Capacitability** of a continuous image of `ℕ → ℕ`: below its outer measure, the
    image contains the image of a compact box of at least that measure. -/
lemma exists_box {h : (ℕ → ℕ) → B} (hh : Continuous h) (μ : Measure B) [IsFiniteMeasure μ]
    {t : ℝ≥0∞} (ht : t < μ (range h)) : ∃ n, t ≤ μ (h '' boxAll n) := by
  classical
  have step : ∀ (k : ℕ) (n : ℕ → ℕ), t < μ (h '' boxPre n k) →
      ∃ m, t < μ (h '' boxPre (Function.update n k m) (k + 1)) := by
    intro k n hn
    set s : ℕ → Set B := fun m => h '' boxPre (Function.update n k m) (k + 1) with hs
    have hmono : Monotone s := by
      intro m m' hmm' _ ⟨y, hy, hyb⟩
      refine ⟨y, fun i hi => ?_, hyb⟩
      have := hy i hi
      rcases eq_or_ne i k with rfl | hik
      · simp only [Function.update_self] at this ⊢; omega
      · simpa [Function.update_of_ne hik] using this
    have hU : (⋃ m, s m) = h '' boxPre n k := by
      ext b
      simp only [hs, mem_iUnion, mem_image]
      constructor
      · rintro ⟨m, y, hy, rfl⟩
        refine ⟨y, fun i hi => ?_, rfl⟩
        have := hy i (Nat.lt_succ_of_lt hi)
        rwa [Function.update_of_ne (Nat.ne_of_lt hi)] at this
      · rintro ⟨y, hy, rfl⟩
        refine ⟨y k, y, fun i hi => ?_, rfl⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
        · rw [Function.update_of_ne (Nat.ne_of_lt hi)]; exact hy i hi
        · simp
    rw [← hU, hmono.measure_iUnion] at hn
    exact lt_iSup_iff.mp hn
  let N : ℕ → (ℕ → ℕ) := fun k => Nat.rec (fun _ => 0)
    (fun k nk => if hk : t < μ (h '' boxPre nk k) then
      Function.update nk k (Classical.choose (step k nk hk)) else nk) k
  have hNsucc : ∀ k, N (k + 1) = if hk : t < μ (h '' boxPre (N k) k) then
      Function.update (N k) k (Classical.choose (step k (N k) hk)) else N k := fun _ => rfl
  have hN : ∀ k, t < μ (h '' boxPre (N k) k) := by
    intro k
    induction k with
    | zero =>
      have : boxPre (N 0) 0 = univ := by ext y; simp [boxPre]
      rw [this, image_univ]; exact ht
    | succ k ih =>
      rw [hNsucc, dif_pos ih]
      exact Classical.choose_spec (step k (N k) ih)
  have hagree : ∀ k j, j < k → N (k + 1) j = N k j := by
    intro k j hj
    rw [hNsucc]
    split_ifs
    · exact Function.update_of_ne (Nat.ne_of_lt hj) _ _
    · rfl
  have hstab : ∀ k i, i < k → N k i = N (i + 1) i := by
    intro k i hi
    induction k with
    | zero => omega
    | succ k ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · rw [hagree k i hi, ih hi]
      · rfl
  set n : ℕ → ℕ := fun i => N (i + 1) i with hn
  have hbox : ∀ k, boxPre (N k) k = boxPre n k := by
    intro k; ext y
    simp only [boxPre, mem_setOf_eq]
    exact forall₂_congr fun i hi => by rw [hstab k i hi]
  refine ⟨n, ?_⟩
  have hsub : (⋂ k, closure (h '' boxPre n k)) ⊆ h '' boxAll n :=
    fun x hx => mem_image_boxAll_of_mem_closure hh (mem_iInter.mp hx)
  have hanti : Antitone fun k => closure (h '' boxPre n k) :=
    fun _ _ hkl => closure_mono (image_mono (boxPre_antitone n hkl))
  calc t ≤ ⨅ k, μ (closure (h '' boxPre n k)) := by
        refine le_iInf fun k => ?_
        rw [← hbox k]
        exact (hN k).le.trans (measure_mono subset_closure)
    _ = μ (⋂ k, closure (h '' boxPre n k)) :=
        (hanti.measure_iInter (fun _ => isClosed_closure.measurableSet.nullMeasurableSet)
          ⟨0, measure_ne_top _ _⟩).symm
    _ ≤ μ (h '' boxAll n) := measure_mono hsub

end Boxes

section Partner

variable {A B : Type*}
  [MetricSpace A] [CompleteSpace A] [SecondCountableTopology A] [MeasurableSpace A]
  [BorelSpace A] [Nonempty A]
  [MetricSpace B] [CompleteSpace B] [SecondCountableTopology B] [MeasurableSpace B]
  [BorelSpace B]

/-- **Measurable partners almost everywhere**, with no compactness assumption. -/
theorem exists_measurable_partner_ae (S : Set (A × B)) (hS : IsClosed S)
    (μ : Measure B) [IsFiniteMeasure μ] (hp : ∀ᵐ b ∂μ, ∃ a, (a, b) ∈ S) :
    ∃ f : B → A, Measurable f ∧ ∀ᵐ b ∂μ, (f b, b) ∈ S := by
  classical
  obtain ⟨a₀⟩ := ‹Nonempty A›
  by_cases hS0 : S.Nonempty
  swap
  · refine ⟨fun _ => a₀, measurable_const, ?_⟩
    filter_upwards [hp] with b ⟨a, ha⟩
    exact (hS0 ⟨_, ha⟩).elim
  by_cases hμ0 : μ univ = 0
  · refine ⟨fun _ => a₀, measurable_const, ?_⟩
    rw [Measure.measure_univ_eq_zero.mp hμ0]; simp
  have : PolishSpace S := hS.polishSpace
  have : Nonempty S := hS0.to_subtype
  obtain ⟨g, hg, hgs⟩ := PolishSpace.exists_nat_nat_continuous_surjective S
  set h : (ℕ → ℕ) → B := fun y => (g y : A × B).2 with hhdef
  set g₁ : (ℕ → ℕ) → A := fun y => (g y : A × B).1 with hg₁def
  have hh : Continuous h := continuous_snd.comp (continuous_subtype_val.comp hg)
  have hg₁ : Continuous g₁ := continuous_fst.comp (continuous_subtype_val.comp hg)
  -- the image of `h` has full measure
  have hnull : μ (range h)ᶜ = 0 := by
    refine measure_mono_null (fun b hb => ?_) (ae_iff.mp hp)
    rintro ⟨a, ha⟩
    obtain ⟨y, hy⟩ := hgs ⟨(a, b), ha⟩
    exact hb ⟨y, by simp [hhdef, hy]⟩
  have hrange : μ (range h) = μ univ := by
    refine le_antisymm (measure_mono (subset_univ _)) ?_
    calc μ univ = μ (range h ∪ (range h)ᶜ) := by rw [union_compl_self]
      _ ≤ μ (range h) + μ (range h)ᶜ := measure_union_le _ _
      _ = μ (range h) := by rw [hnull, add_zero]
  -- compact boxes of almost full measure
  have hbox : ∀ j : ℕ, ∃ n : ℕ → ℕ, μ univ - (j : ℝ≥0∞)⁻¹ ≤ μ (h '' boxAll n) := by
    intro j
    refine exists_box hh μ ?_
    rw [hrange]
    exact ENNReal.sub_lt_self (measure_ne_top _ _) hμ0 (ENNReal.inv_ne_zero.mpr (natCast_ne_top j))
  choose n hn using hbox
  set K : ℕ → Set B := fun j => h '' boxAll (n j) with hK
  set L : ℕ → Set A := fun j => g₁ '' boxAll (n j) with hL
  have hKc : ∀ j, IsCompact (K j) := fun j => (isCompact_boxAll _).image hh
  have hLc : ∀ j, IsCompact (L j) := fun j => (isCompact_boxAll _).image hg₁
  have hKm : ∀ j, MeasurableSet (K j) := fun j => (hKc j).isClosed.measurableSet
  -- a measurable partner on each compact piece
  have hsel : ∀ j, ∃ F : B → A, Measurable F ∧ ∀ b ∈ K j, (F b, b) ∈ S := by
    intro j
    set Q : Set (K j × A) := {p | (p.2, (p.1 : B)) ∈ S ∧ p.2 ∈ L j} with hQ
    have hQc : IsClosed Q :=
      (hS.preimage (continuous_snd.prodMk (continuous_subtype_val.comp continuous_fst))).inter
        ((hLc j).isClosed.preimage continuous_snd)
    have hne : ∀ b : K j, ∃ a, (b, a) ∈ Q := by
      rintro ⟨b, y, hy, rfl⟩
      exact ⟨g₁ y, (g y).2, ⟨y, hy, rfl⟩⟩
    obtain ⟨φ, hφm, hφ⟩ := exists_measurable_partner Q hQc (fun _ => L j) (fun _ => hLc j)
      (fun p hp => ⟨0, hp.2⟩) hne
    refine ⟨fun b => if hb : b ∈ K j then φ ⟨b, hb⟩ else a₀,
      Measurable.dite hφm measurable_const (hKm j), fun b hb => ?_⟩
    simp only [dif_pos hb]
    exact (hφ ⟨b, hb⟩).1
  choose F hFm hF using hsel
  -- glue the pieces
  set p : ℕ → B → Prop := fun j b => b ∈ K j ∨ b ∉ ⋃ i, K i with hp'
  have hex : ∀ b, ∃ j, p j b := by
    intro b
    by_cases hb : b ∈ ⋃ i, K i
    · obtain ⟨j, hj⟩ := mem_iUnion.mp hb; exact ⟨j, Or.inl hj⟩
    · exact ⟨0, Or.inr hb⟩
  have hpm : ∀ j, MeasurableSet {b | p j b} := fun j =>
    (hKm j).union (MeasurableSet.iUnion hKm).compl
  refine ⟨fun b => F (Nat.find (hex b)) b, Measurable.find hFm hpm hex, ?_⟩
  -- the pieces cover almost everything
  have hcov : μ (⋃ i, K i)ᶜ = 0 := by
    refine le_antisymm (ge_of_tendsto' ENNReal.tendsto_inv_nat_nhds_zero fun j => ?_) zero_le'
    calc μ (⋃ i, K i)ᶜ ≤ μ (K j)ᶜ := measure_mono (compl_subset_compl.mpr (subset_iUnion K j))
      _ = μ univ - μ (K j) := measure_compl (hKm j) (measure_ne_top _ _)
      _ ≤ μ univ - (μ univ - (j : ℝ≥0∞)⁻¹) := tsub_le_tsub_left (hn j) _
      _ ≤ (j : ℝ≥0∞)⁻¹ := tsub_le_iff_right.mpr le_add_tsub
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hcov] with b hb
  have hb' : b ∈ ⋃ i, K i := not_not.mp hb
  have hspec := Nat.find_spec (hex b)
  rcases hspec with hk | hk
  · exact hF _ b hk
  · exact (hk hb').elim

omit [Nonempty A] in
/-- The left-hand version: partners chosen measurably for almost every source. -/
theorem exists_measurable_partner_ae_left [Nonempty B] (S : Set (A × B)) (hS : IsClosed S)
    (μ : Measure A) [IsFiniteMeasure μ] (hp : ∀ᵐ a ∂μ, ∃ b, (a, b) ∈ S) :
    ∃ f : A → B, Measurable f ∧ ∀ᵐ a ∂μ, (a, f a) ∈ S :=
  exists_measurable_partner_ae (A := B) (B := A) (Prod.swap ⁻¹' S)
    (hS.preimage continuous_swap) μ hp

end Partner

end Continuous
