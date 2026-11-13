import Xhl.Duality.LimitWitness
import Xhl.Duality.RightWitness
import Xhl.Duality.Discrete.RenyiDualityGen

/-!
# Strong duality for the continuous Rényi lifting

The core of Theorem D.1.  For sub-probability measures on Polish spaces and a closed relation with measurable
partner selectors, the witness-free lifting implies the two-witness one
(`exists_witnesses_of_codLift`).

* **Cells**: the cell of a point is the index of the first point of a dense
  sequence within `ε/2` of it (`cell`); cells are measurable and two points of
  one cell are within `ε`.
* **The quotient problem**: pushing `μ₁`, `μ₂` along the cell maps gives
  sub-distributions on `ℕ` (`quotD`), related when some pair of their cells
  meets `R`.  Step functions are measurable tests, so the witness-free bound
  transfers with equal test values, and the partner conditions transfer.  The
  discrete duality `DStd.Distr.flift_mul_iff_codLift_gen` gives discrete witnesses at
  budget `η`.
* **The lift**: the left discrete witness `w` becomes the density
  `w(i,j) / (μ₁(Cᵢ) μ₂(Dⱼ))` on product cells against `μ₁ ⊗ μ₂`.  Tonelli gives
  the left marginal `μ₁` and a right marginal with density constant on cells,
  whose Hellinger integral against `μ₂` is the discrete one of the right
  marginals, hence at most `η`; the density vanishes off the closed
  `ε`-thickening of `R` (`exists_approx_witness`).
* **Assembly**: mesh `1/(n+1)`, the limit `exists_limit_witness`, and the
  right witness `exists_witnesses_of_reduced`; `exists_witnesses_top` when `η = ⊤`.
-/

open MeasureTheory ENNReal Filter Topology Classical
open scoped NNReal

open DStd

namespace Continuous.StdDual

/-!
## Cells of small diameter
-/

section Cells

variable (X : Type*) [MetricSpace X] [SecondCountableTopology X] [Nonempty X]

lemma exists_denseSeq_near (ε : ℝ) (hε : 0 < ε) (x : X) :
    ∃ i, dist x (TopologicalSpace.denseSeq X i) < ε / 2 :=
  Metric.denseRange_iff.mp (TopologicalSpace.denseRange_denseSeq X) x (ε / 2) (half_pos hε)

/-- The cell of a point: the first index of the dense sequence within `ε/2`. -/
noncomputable def cell (ε : ℝ) (hε : 0 < ε) (x : X) : ℕ :=
  Nat.find (exists_denseSeq_near X ε hε x)

variable {X}

lemma cell_spec {ε : ℝ} (hε : 0 < ε) (x : X) :
    dist x (TopologicalSpace.denseSeq X (cell X ε hε x)) < ε / 2 :=
  Nat.find_spec (exists_denseSeq_near X ε hε x)

lemma dist_lt_of_cell_eq {ε : ℝ} (hε : 0 < ε) {x y : X} (h : cell X ε hε x = cell X ε hε y) :
    dist x y < ε := by
  have hx := cell_spec hε x
  have hy := cell_spec hε y
  rw [h] at hx
  calc dist x y ≤ dist x (TopologicalSpace.denseSeq X (cell X ε hε y))
        + dist (TopologicalSpace.denseSeq X (cell X ε hε y)) y := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := by rw [dist_comm _ y]; exact add_lt_add hx hy
    _ = ε := add_halves ε

lemma measurable_cell [MeasurableSpace X] [BorelSpace X] {ε : ℝ} (hε : 0 < ε) :
    Measurable (cell X ε hε) := by
  refine measurable_to_countable' fun i => ?_
  have h : cell X ε hε ⁻¹' {i} = {x | dist x (TopologicalSpace.denseSeq X i) < ε / 2} ∩
      ⋂ j, ⋂ (_ : j < i), {x | ¬ dist x (TopologicalSpace.denseSeq X j) < ε / 2} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_iInter]
    exact Nat.find_eq_iff _
  rw [h]
  refine MeasurableSet.inter (measurableSet_lt (measurable_id.dist measurable_const)
    measurable_const) (MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => ?_)
  exact (measurableSet_lt (measurable_id.dist measurable_const) measurable_const).compl

end Cells

/-!
## Quotient sub-distributions
-/

section Quot

variable {X : Type*} [MeasurableSpace X]

/-- The push of a sub-probability measure along a measurable map to `ℕ`. -/
noncomputable def quotD (μ : Measure X) (hμ : μ Set.univ ≤ 1) (q : X → ℕ) (hq : Measurable q) :
    Distr ℕ where
  mass i := μ.map q {i}
  le_one := by
    have h := lintegral_countable' (μ := μ.map q) (fun _ => (1 : ℝ≥0∞))
    simp only [one_mul, lintegral_const, Measure.map_apply hq MeasurableSet.univ,
      Set.preimage_univ] at h
    rw [← h]
    exact hμ

lemma quotD_mass {μ : Measure X} {hμ : μ Set.univ ≤ 1} {q : X → ℕ} {hq : Measurable q} (i : ℕ) :
    (quotD μ hμ q hq).mass i = μ (q ⁻¹' {i}) :=
  Measure.map_apply hq (measurableSet_singleton i)

lemma lintegral_quotD {μ : Measure X} {hμ : μ Set.univ ≤ 1} {q : X → ℕ} {hq : Measurable q}
    (k : ℕ → ℝ≥0∞) : ∫⁻ x, k (q x) ∂μ = ∑' i, k i * (quotD μ hμ q hq).mass i := by
  rw [← lintegral_map measurable_from_nat hq, lintegral_countable']
  rfl

end Quot

/-- Data processing to the second coordinate, for sub-distributions. -/
lemma Distr.hRen_snd_le {I J : Type} {α : ℝ} (hα : 1 < α) (w₁ w₂ : Distr (I × J)) :
    Distr.hRen α w₁.snd w₂.snd ≤ Distr.hRen α w₁ w₂ := by
  unfold Distr.hRen
  simp_rw [Distr.snd_mass]
  calc ∑' j, (∑' i, w₁.mass (i, j)) ^ α * (∑' i, w₂.mass (i, j)) ^ (1 - α)
      ≤ ∑' j, ∑' i, w₁.mass (i, j) ^ α * w₂.mass (i, j) ^ (1 - α) :=
        ENNReal.tsum_le_tsum fun j => Distr.tsum_rpow_mul_rpow_le _ _ hα
    _ = ∑' p : I × J, w₁.mass p ^ α * w₂.mass p ^ (1 - α) := by
        rw [ENNReal.tsum_comm]
        exact (ENNReal.tsum_prod' (f := fun p : I × J => w₁.mass p ^ α * w₂.mass p ^ (1 - α))).symm

/-!
## Approximate witnesses
-/

variable {A B : Type*}
  [MetricSpace A] [SecondCountableTopology A] [MeasurableSpace A] [BorelSpace A] [Nonempty A]
  [MetricSpace B] [SecondCountableTopology B] [MeasurableSpace B] [BorelSpace B] [Nonempty B]

/-- **Approximate left witnesses** from the witness-free bound: left marginal
    `μ₁`, right-marginal budget `η`, no mass off the closed `ε`-thickening of `R`. -/
theorem exists_approx_witness {α : ℝ} (hα : 1 < α) {R : A → B → Prop} {η : ℝ≥0∞} (hη : η ≠ ⊤)
    {μ₁ : Measure A} {μ₂ : Measure B} [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂]
    (hμ₁ : μ₁ Set.univ ≤ 1) (hμ₂ : μ₂ Set.univ ≤ 1)
    (hp₁ : ∀ᵐ a ∂μ₁, ∃ b, R a b) (hp₂ : ∀ᵐ b ∂μ₂, ∃ a, R a b)
    (h : CodLiftMulC α R η μ₁ μ₂) {ε : ℝ} (hε : 0 < ε) :
    ∃ W : Measure (A × B), IsFiniteMeasure W ∧ W.map Prod.fst = μ₁ ∧
      hellingerIntegral α (W.map Prod.snd) μ₂ ≤ η ∧
      W (Metric.cthickening ε {p : A × B | R p.1 p.2})ᶜ = 0 := by
  have hα0 : (0 : ℝ) < α := by linarith
  set q₁ := cell A ε hε with hq₁def
  set q₂ := cell B ε hε with hq₂def
  have hq₁ : Measurable q₁ := measurable_cell hε
  have hq₂ : Measurable q₂ := measurable_cell hε
  set m₁ : Distr ℕ := quotD μ₁ hμ₁ q₁ hq₁ with hm₁def
  set m₂ : Distr ℕ := quotD μ₂ hμ₂ q₂ hq₂ with hm₂def
  set Rq : ℕ → ℕ → Prop := fun i j => ∃ a b, q₁ a = i ∧ q₂ b = j ∧ R a b with hRq
  -- the witness-free bound on the quotient
  have hcod : Distr.CodLiftMul α Rq η m₁ m₂ := by
    intro k₁ k₂ hk
    have hadm : TestAdmC α R (fun a => k₁ (q₁ a)) (fun b => k₂ (q₂ b)) :=
      fun a b hab => hk _ _ ⟨a, b, rfl, rfl, hab⟩
    have := h (fun a => k₁ (q₁ a)) (fun b => k₂ (q₂ b)) (measurable_from_nat.comp hq₁)
      (measurable_from_nat.comp hq₂) hadm
    unfold testValC at this
    unfold Distr.testVal
    rwa [lintegral_quotD (hμ := hμ₁) (hq := hq₁), lintegral_quotD (hμ := hμ₂) (hq := hq₂)] at this
  -- partner conditions on the quotient
  have hp₁q : ∀ i, m₁.mass i ≠ 0 → ∃ j, Rq i j := by
    intro i hi
    rw [quotD_mass] at hi
    by_contra hcon
    push Not at hcon
    apply hi
    refine measure_mono_null (fun a ha => ?_) (ae_iff.mp hp₁)
    rintro ⟨b, hb⟩
    exact hcon (q₂ b) ⟨a, b, ha, rfl, hb⟩
  have hp₂q : ∀ j, m₂.mass j ≠ 0 → ∃ i, Rq i j := by
    intro j hj
    rw [quotD_mass] at hj
    by_contra hcon
    push Not at hcon
    apply hj
    refine measure_mono_null (fun b hb => ?_) (ae_iff.mp hp₂)
    rintro ⟨a, ha⟩
    exact hcon (q₁ a) ⟨a, b, rfl, hb, ha⟩
  -- discrete witnesses
  obtain ⟨⟨wL, wR⟩, hfst, hsnd, hrL, hrR, hH⟩ :=
    (Distr.flift_mul_iff_codLift_gen hα hp₁q hp₂q).mpr hcod
  have hm₁top : ∀ i, m₁.mass i ≠ ⊤ := fun i => Distr.mass_ne_top m₁ i
  have hm₂top : ∀ j, m₂.mass j ≠ ⊤ := fun j => Distr.mass_ne_top m₂ j
  have hwL1 : ∀ i j, wL.mass (i, j) ≠ 0 → m₁.mass i ≠ 0 := by
    intro i j hw h0
    apply hw
    have hle : wL.mass (i, j) ≤ m₁.mass i := by
      rw [← hfst, Distr.fst_mass]; exact ENNReal.le_tsum j
    exact le_antisymm (h0 ▸ hle) zero_le
  have hwL2 : ∀ i j, wL.mass (i, j) ≠ 0 → m₂.mass j ≠ 0 := by
    intro i j hw h0
    have hwR : wR.mass (i, j) ≠ 0 := by
      intro hR0
      have hterm : wL.mass (i, j) ^ α * wR.mass (i, j) ^ (1 - α) = ⊤ := by
        rw [hR0, ENNReal.zero_rpow_of_neg (by linarith)]
        exact ENNReal.mul_top (Distr.rpow_ne_zero_of_ne_zero_of_ne_top hw (Distr.mass_ne_top wL _) _)
      have : Distr.hRen α wL wR = ⊤ := top_le_iff.mp (hterm ▸ ENNReal.le_tsum (i, j))
      exact hη (top_le_iff.mp (this ▸ hH))
    apply hwR
    have hle : wR.mass (i, j) ≤ m₂.mass j := by
      rw [← hsnd, Distr.snd_mass]; exact ENNReal.le_tsum i
    exact le_antisymm (h0 ▸ hle) zero_le
  -- the density on product cells
  set H : ℕ → ℕ → ℝ≥0∞ := fun i j => wL.mass (i, j) / (m₁.mass i * m₂.mass j) with hHdef
  set Hq : A × B → ℝ≥0∞ := fun p => H (q₁ p.1) (q₂ p.2) with hHqdef
  have hHqm : Measurable Hq :=
    (measurable_of_countable (fun ij : ℕ × ℕ => H ij.1 ij.2)).comp
      ((hq₁.comp measurable_fst).prodMk (hq₂.comp measurable_snd))
  have hHzero : ∀ i j, H i j ≠ 0 → wL.mass (i, j) ≠ 0 := fun i j hne h0 => by
    apply hne; rw [hHdef]; simp only [h0, ENNReal.zero_div]
  set W : Measure (A × B) := (μ₁.prod μ₂).withDensity Hq with hWdef
  -- inner integrals
  have hI1 : ∀ i, m₁.mass i ≠ 0 → ∫⁻ b, H i (q₂ b) ∂μ₂ = 1 := by
    intro i hi
    rw [lintegral_quotD (hμ := hμ₂) (hq := hq₂) (fun j => H i j)]
    calc ∑' j, H i j * m₂.mass j = ∑' j, wL.mass (i, j) * (m₁.mass i)⁻¹ := by
          refine tsum_congr fun j => ?_
          by_cases hw : wL.mass (i, j) = 0
          · rw [hHdef]; simp only [hw, ENNReal.zero_div, zero_mul]
          · have hj := hwL2 i j hw
            rw [hHdef]
            simp only
            rw [div_eq_mul_inv, ENNReal.mul_inv (Or.inl hi) (Or.inl (hm₁top i)), mul_assoc,
              mul_assoc, ENNReal.inv_mul_cancel hj (hm₂top j), mul_one]
      _ = (∑' j, wL.mass (i, j)) * (m₁.mass i)⁻¹ := ENNReal.tsum_mul_right
      _ = 1 := by
          rw [← Distr.fst_mass, hfst, ENNReal.mul_inv_cancel hi (hm₁top i)]
  have hI2 : ∀ j, ∫⁻ a, H (q₁ a) j ∂μ₁ = wL.snd.mass j * (m₂.mass j)⁻¹ := by
    intro j
    rw [lintegral_quotD (hμ := hμ₁) (hq := hq₁) (fun i => H i j)]
    calc ∑' i, H i j * m₁.mass i = ∑' i, wL.mass (i, j) * (m₂.mass j)⁻¹ := by
          refine tsum_congr fun i => ?_
          by_cases hw : wL.mass (i, j) = 0
          · rw [hHdef]; simp only [hw, ENNReal.zero_div, zero_mul]
          · have hi := hwL1 i j hw
            have hj := hwL2 i j hw
            rw [hHdef]
            simp only
            rw [div_eq_mul_inv, ENNReal.mul_inv (Or.inl hi) (Or.inl (hm₁top i)), mul_assoc,
              mul_comm (m₁.mass i)⁻¹, mul_assoc, ENNReal.inv_mul_cancel hi (hm₁top i), mul_one]
      _ = (∑' i, wL.mass (i, j)) * (m₂.mass j)⁻¹ := ENNReal.tsum_mul_right
      _ = wL.snd.mass j * (m₂.mass j)⁻¹ := by rw [Distr.snd_mass]
  -- left marginal
  have hnull : ∀ᵐ a ∂μ₁, m₁.mass (q₁ a) ≠ 0 := by
    rw [ae_iff]
    refine measure_mono_null (fun a ha => ?_)
      (measure_iUnion_null fun i : {i : ℕ // m₁.mass i = 0} =>
        (show μ₁ (q₁ ⁻¹' {i.1}) = 0 by rw [← quotD_mass (hμ := hμ₁) (hq := hq₁)]; exact i.2))
    simp only [Set.mem_ofPred_eq, not_not] at ha
    exact Set.mem_iUnion.mpr ⟨⟨q₁ a, ha⟩, rfl⟩
  have hW1 : W.map Prod.fst = μ₁ := by
    ext s hs
    rw [Measure.map_apply measurable_fst hs, hWdef, withDensity_apply _ (measurable_fst hs),
      show Prod.fst ⁻¹' s = s ×ˢ (Set.univ : Set B) from Set.prod_univ.symm,
      ← Measure.prod_restrict, Measure.restrict_univ, lintegral_prod _ hHqm.aemeasurable]
    have hae : ∀ᵐ a ∂μ₁, ∫⁻ b, Hq (a, b) ∂μ₂ = 1 := by
      filter_upwards [hnull] with a ha
      exact hI1 (q₁ a) ha
    rw [lintegral_congr_ae (ae_restrict_of_ae hae), lintegral_one, Measure.restrict_apply_univ]
  have hWfin : IsFiniteMeasure W := by
    refine ⟨?_⟩
    have : W Set.univ = μ₁ Set.univ := by
      rw [← hW1, Measure.map_apply measurable_fst MeasurableSet.univ, Set.preimage_univ]
    rw [this]; exact measure_lt_top μ₁ _
  -- right marginal
  set g : ℕ → ℝ≥0∞ := fun j => wL.snd.mass j * (m₂.mass j)⁻¹ with hgdef
  set f : B → ℝ≥0∞ := fun b => g (q₂ b) with hfdef
  have hfm : Measurable f := (measurable_from_nat (f := g)).comp hq₂
  have hW2 : W.map Prod.snd = μ₂.withDensity f := by
    ext t ht
    rw [Measure.map_apply measurable_snd ht, hWdef, withDensity_apply _ (measurable_snd ht),
      withDensity_apply _ ht,
      show Prod.snd ⁻¹' t = (Set.univ : Set A) ×ˢ t from Set.univ_prod.symm,
      ← Measure.prod_restrict, Measure.restrict_univ, lintegral_prod_symm _ hHqm.aemeasurable]
    exact lintegral_congr fun b => hI2 (q₂ b)
  -- budget
  have hbudget : hellingerIntegral α (W.map Prod.snd) μ₂ ≤ η := by
    have hac : W.map Prod.snd ≪ μ₂ := hW2 ▸ withDensity_absolutelyContinuous μ₂ f
    have hrn : (W.map Prod.snd).rnDeriv μ₂ =ᵐ[μ₂] f := hW2 ▸ Measure.rnDeriv_withDensity μ₂ hfm
    rw [hellingerIntegral_eq_lintegral_rnDeriv _ μ₂ hac,
      lintegral_congr_ae (hrn.mono fun b hb => by rw [hb]),
      lintegral_quotD (hμ := hμ₂) (hq := hq₂) (fun j => g j ^ α)]
    have hsndz : ∀ j, m₂.mass j = 0 → wL.snd.mass j = 0 := fun j hj => by
      rw [Distr.snd_mass]
      exact ENNReal.tsum_eq_zero.mpr fun i => by
        by_contra hw; exact hwL2 i j hw hj
    calc ∑' j, g j ^ α * m₂.mass j
        = ∑' j, wL.snd.mass j ^ α * m₂.mass j ^ (1 - α) := by
          refine tsum_congr fun j => ?_
          rw [hgdef]
          simp only
          by_cases hj : m₂.mass j = 0
          · rw [hj, hsndz j hj, zero_mul, ENNReal.zero_rpow_of_pos hα0, zero_mul, zero_mul]
          · rw [ENNReal.mul_rpow_of_nonneg _ _ hα0.le, ENNReal.inv_rpow, ← ENNReal.rpow_neg,
              mul_assoc]
            congr 1
            calc m₂.mass j ^ (-α) * m₂.mass j = m₂.mass j ^ (-α) * m₂.mass j ^ (1 : ℝ) := by
                  rw [ENNReal.rpow_one]
              _ = m₂.mass j ^ (-α + 1) := (ENNReal.rpow_add _ _ hj (hm₂top j)).symm
              _ = m₂.mass j ^ (1 - α) := by rw [show -α + 1 = 1 - α by ring]
      _ = Distr.hRen α wL.snd m₂ := rfl
      _ = Distr.hRen α wL.snd wR.snd := by rw [hsnd]
      _ ≤ Distr.hRen α wL wR := Distr.hRen_snd_le hα wL wR
      _ ≤ η := hH
  -- support
  have hRset : ∀ p : A × B, p ∉ Metric.cthickening ε {p : A × B | R p.1 p.2} → Hq p = 0 := by
    rintro ⟨a, b⟩ hp
    by_contra hne
    apply hp
    obtain ⟨a', b', ha', hb', hR⟩ := hrL (q₁ a, q₂ b) (hHzero _ _ hne)
    have hda : dist a a' < ε := dist_lt_of_cell_eq hε ha'.symm
    have hdb : dist b b' < ε := dist_lt_of_cell_eq hε hb'.symm
    refine Metric.mem_cthickening_of_dist_le (a, b) (a', b') ε _ hR ?_
    rw [Prod.dist_eq]
    exact (max_lt hda hdb).le
  have hsupp : W (Metric.cthickening ε {p : A × B | R p.1 p.2})ᶜ = 0 := by
    have hm : MeasurableSet (Metric.cthickening ε {p : A × B | R p.1 p.2})ᶜ :=
      Metric.isClosed_cthickening.measurableSet.compl
    rw [hWdef, withDensity_apply _ hm,
      setLIntegral_congr_fun hm (g := fun _ => 0) (fun p hp => hRset p hp), lintegral_zero]
  exact ⟨W, hWfin, hW1, hbudget, hsupp⟩

/-!
## Strong duality
-/

variable [CompleteSpace A] [CompleteSpace B]

/-- **Strong duality** for the continuous lifting: under the partner selectors, the
    witness-free lifting gives two finite witnesses, concentrated on `R`, with
    marginals `μ₁`, `μ₂` and Hellinger integral at most `η`. -/
theorem exists_witnesses_of_codLift {α : ℝ} (hα : 1 < α) {R : A → B → Prop} {η : ℝ≥0∞}
    (hRc : IsClosed {p : A × B | R p.1 p.2})
    {μ₁ : Measure A} {μ₂ : Measure B} [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂]
    (hμ₁ : μ₁ Set.univ ≤ 1) (hμ₂ : μ₂ Set.univ ≤ 1)
    (s₁ : A → B) (hs₁ : Measurable s₁) (h₁ : ∀ᵐ a ∂μ₁, R a (s₁ a))
    (s₂ : B → A) (hs₂ : Measurable s₂) (h₂ : ∀ᵐ b ∂μ₂, R (s₂ b) b)
    (h : CodLiftMulC α R η μ₁ μ₂) :
    ∃ w₁ w₂ : Measure (A × B), IsFiniteMeasure w₁ ∧ IsFiniteMeasure w₂ ∧
      w₁.map Prod.fst = μ₁ ∧ w₂.map Prod.snd = μ₂ ∧
      (∀ᵐ p ∂w₁, R p.1 p.2) ∧ (∀ᵐ p ∂w₂, R p.1 p.2) ∧ hellingerIntegral α w₁ w₂ ≤ η := by
  by_cases hη : η = ⊤
  · rw [hη]; exact exists_witnesses_top hRc.measurableSet s₁ hs₁ h₁ s₂ hs₂ h₂
  have hp₁ : ∀ᵐ a ∂μ₁, ∃ b, R a b := h₁.mono fun a ha => ⟨s₁ a, ha⟩
  have hp₂ : ∀ᵐ b ∂μ₂, ∃ a, R a b := h₂.mono fun b hb => ⟨s₂ b, hb⟩
  have happ : ∀ n : ℕ, ∃ W : Measure (A × B), IsFiniteMeasure W ∧ W.map Prod.fst = μ₁ ∧
      hellingerIntegral α (W.map Prod.snd) μ₂ ≤ η ∧
      W (Metric.cthickening (1 / ((n : ℝ) + 1)) {p : A × B | R p.1 p.2})ᶜ = 0 :=
    fun n => exists_approx_witness hα hη hμ₁ hμ₂ hp₁ hp₂ h Nat.one_div_pos_of_nat
  choose W hWfin hW₁ hWJ hWF using happ
  have : ∀ n, IsFiniteMeasure (W n) := hWfin
  set F : ℕ → Set (A × B) :=
    fun k => Metric.cthickening (1 / ((k : ℝ) + 1)) {p : A × B | R p.1 p.2} with hFdef
  have hFc : ∀ k, IsClosed (F k) := fun k => Metric.isClosed_cthickening
  have hFR : ∀ p, (∀ k, p ∈ F k) → R p.1 p.2 := by
    intro p hp
    have hcl : p ∈ closure {p : A × B | R p.1 p.2} := by
      rw [Metric.closure_eq_iInter_cthickening]
      simp only [Set.mem_iInter]
      intro δ hδ
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt hδ
      exact Metric.cthickening_mono hk.le _ (hp k)
    rw [hRc.closure_eq] at hcl
    exact hcl
  have hWFk : ∀ k, ∀ᶠ n in atTop, W n (F k)ᶜ = 0 := fun k =>
    (eventually_ge_atTop k).mono fun n hn => by
      refine measure_mono_null (Set.compl_subset_compl.mpr (Metric.cthickening_mono ?_ _)) (hWF n)
      exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hn 1)
  obtain ⟨w, hwfin, hw₁, hwR, hwJ⟩ := exists_limit_witness hα hη F hFc hFR W hW₁ hWJ hWFk
  have := hwfin
  exact exists_witnesses_of_reduced hα hRc.measurableSet w hw₁ hwR hwJ s₂ hs₂ h₂

end Continuous.StdDual
