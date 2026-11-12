import Xhl.Duality.Selection.KRN

/-!
# Measurable partners in a closed relation

`exists_measurable_partner`: let `Q` be a closed relation between a measurable space `X`
with a topology whose open sets are measurable and a complete separable metric space `Y`,
such that every `a` has a partner `b` with `(a, b) ∈ Q`.  If the partners lie in countably
many compact subsets of `Y`, then a partner can be chosen measurably.  It is applied, on
compact pieces of almost full measure, in `AePartner.lean`.

Proof: the sections of `Q` are closed, and `Q` meets `X × C`, for `C` closed, in a
countable union of closed sets with compact second projection, whose first projections
are closed; so the correspondence is weakly measurable and the Kuratowski–Ryll-Nardzewski
theorem applies.
-/

open Set Filter Topology TopologicalSpace

namespace Continuous

variable {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  [MetricSpace Y] [CompleteSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y]
  [BorelSpace Y]

/-- The first projection of a closed set contained in `X × K`, `K` compact, is closed. -/
lemma isClosed_image_fst_of_subset_compact {S : Set (X × Y)} (hS : IsClosed S) {K : Set Y}
    (hK : IsCompact K) (hSK : ∀ p ∈ S, p.2 ∈ K) : IsClosed (Prod.fst '' S) := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have hS' : IsClosed {p : X × K | (p.1, (p.2 : Y)) ∈ S} :=
    hS.preimage (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have := isClosedMap_fst_of_compactSpace (X := X) (Y := K) _ hS'
  convert this using 1
  ext a
  constructor
  · rintro ⟨⟨a', b⟩, hp, rfl⟩
    exact ⟨(a', ⟨b, hSK _ hp⟩), hp, rfl⟩
  · rintro ⟨⟨a', b⟩, hp, rfl⟩
    exact ⟨(a', b), hp, rfl⟩

/-- **Measurable partners.** -/
theorem exists_measurable_partner (Q : Set (X × Y)) (hQ : IsClosed Q)
    (K : ℕ → Set Y) (hK : ∀ n, IsCompact (K n)) (hQK : ∀ p ∈ Q, ∃ n, p.2 ∈ K n)
    (hne : ∀ a, ∃ b, (a, b) ∈ Q) :
    ∃ f : X → Y, Measurable f ∧ ∀ a, (a, f a) ∈ Q := by
  set F : X → Set Y := fun a => {b | (a, b) ∈ Q} with hF
  have hFc : ∀ a, IsClosed (F a) := fun a =>
    hQ.preimage (continuous_const.prodMk continuous_id)
  have hFC : ∀ C : Set Y, IsClosed C → MeasurableSet {a | (F a ∩ C).Nonempty} := by
    intro C hC
    have : {a | (F a ∩ C).Nonempty}
        = ⋃ n, Prod.fst '' (Q ∩ (Set.univ ×ˢ (C ∩ K n))) := by
      ext a
      simp only [mem_setOf_eq, mem_iUnion, mem_image, mem_inter_iff, mem_prod, mem_univ,
        true_and, Prod.exists, exists_and_right, exists_eq_right, hF]
      constructor
      · rintro ⟨b, hb, hbC⟩
        obtain ⟨n, hn⟩ := hQK (a, b) hb
        exact ⟨n, b, hb, hbC, hn⟩
      · rintro ⟨n, b, hb, hbC, -⟩
        exact ⟨b, hb, hbC⟩
    rw [this]
    refine MeasurableSet.iUnion fun n => ?_
    refine (isClosed_image_fst_of_subset_compact (hQ.inter (isClosed_univ.prod (hC.inter
      (hK n).isClosed))) (hK n) fun p hp => hp.2.2.2).measurableSet
  have hFm : WeaklyMeasurable F := by
    intro U hU
    obtain ⟨C, hCc, -, hCU, -⟩ := hU.exists_iUnion_isClosed
    have : {a | (F a ∩ U).Nonempty} = ⋃ n, {a | (F a ∩ C n).Nonempty} := by
      ext a
      simp only [mem_setOf_eq, mem_iUnion]
      constructor
      · rintro ⟨b, hb, hbU⟩
        rw [← hCU] at hbU
        obtain ⟨n, hn⟩ := mem_iUnion.1 hbU
        exact ⟨n, b, hb, hn⟩
      · rintro ⟨n, b, hb, hn⟩
        exact ⟨b, hb, by rw [← hCU]; exact mem_iUnion.2 ⟨n, hn⟩⟩
    rw [this]
    exact MeasurableSet.iUnion fun n => hFC _ (hCc n)
  obtain ⟨f, hfm, hf⟩ := exists_measurable_selection F hFc (fun a => hne a) hFm
  exact ⟨f, hfm, hf⟩

end Continuous
