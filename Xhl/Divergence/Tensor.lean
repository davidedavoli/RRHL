import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Algebra.BigOperators.Fin
import Xhl.Divergence.MapLe

/-!
# Tensorization of the Hellinger integral

The Hellinger integral is multiplicative over products: `hellingerIntegral_prod` (binary) and
`hellingerIntegral_pi` (`Measure.pi` on `Fin n`); Proposition A.20, item 4.
-/

open MeasureTheory ProbabilityTheory ENNReal Real
open scoped NNReal

namespace Continuous

variable {r : ℝ}

/-- **Tensorization**: for finite measures with `μᵢ ≪ νᵢ`,
    `H(μ₁ ⊗ μ₂ ‖ ν₁ ⊗ ν₂) = H(μ₁‖ν₁) · H(μ₂‖ν₂)`. -/
theorem hellingerIntegral_prod {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (hr : 1 < r) (μ₁ ν₁ : Measure X) (μ₂ ν₂ : Measure Y)
    [IsFiniteMeasure μ₁] [IsFiniteMeasure ν₁] [IsFiniteMeasure μ₂] [IsFiniteMeasure ν₂]
    (h1 : μ₁ ≪ ν₁) (h2 : μ₂ ≪ ν₂) :
    hellingerIntegral r (μ₁.prod μ₂) (ν₁.prod ν₂) = hellingerIntegral r μ₁ ν₁ * hellingerIntegral r μ₂ ν₂ := by
  have hr0 : (0 : ℝ) ≤ r := le_of_lt (lt_trans one_pos hr)
  set f₁ := μ₁.rnDeriv ν₁ with hf₁def
  set f₂ := μ₂.rnDeriv ν₂ with hf₂def
  have hf₁ : Measurable f₁ := Measure.measurable_rnDeriv _ _
  have hf₂ : Measurable f₂ := Measure.measurable_rnDeriv _ _
  have hac : μ₁.prod μ₂ ≪ ν₁.prod ν₂ := h1.prod h2
  have hprodwd : μ₁.prod μ₂ = (ν₁.prod ν₂).withDensity (fun z => f₁ z.1 * f₂ z.2) := by
    conv_lhs =>
      rw [← Measure.withDensity_rnDeriv_eq μ₁ ν₁ h1, ← Measure.withDensity_rnDeriv_eq μ₂ ν₂ h2]
    exact prod_withDensity₀ hf₁.aemeasurable hf₂.aemeasurable
  have hrn : (μ₁.prod μ₂).rnDeriv (ν₁.prod ν₂) =ᵐ[ν₁.prod ν₂] fun z => f₁ z.1 * f₂ z.2 := by
    rw [hprodwd]
    exact Measure.rnDeriv_withDensity _ ((hf₁.comp measurable_fst).mul (hf₂.comp measurable_snd))
  rw [hellingerIntegral_eq_lintegral_rnDeriv _ _ hac,
      lintegral_congr_ae (hrn.mono (fun z hz => by rw [hz]))]
  simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hr0]
  rw [lintegral_prod_mul (f := fun x => f₁ x ^ r) (g := fun y => f₂ y ^ r)
        (by fun_prop) (by fun_prop),
      ← hellingerIntegral_eq_lintegral_rnDeriv μ₁ ν₁ h1, ← hellingerIntegral_eq_lintegral_rnDeriv μ₂ ν₂ h2]

/-- Invariance of the Hellinger integral under a measurable equivalence. -/
lemma hellingerIntegral_map_equiv {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (hr : 1 < r)
    (e : X ≃ᵐ Y) (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμν : μ ≪ ν) :
    hellingerIntegral r (μ.map e) (ν.map e) = hellingerIntegral r μ ν := by
  have := μ.isFiniteMeasure_map e
  have := ν.isFiniteMeasure_map e
  refine le_antisymm (hellingerIntegral_map_le hr e.measurable μ ν hμν) ?_
  have hle2 := hellingerIntegral_map_le hr e.symm.measurable (μ.map e) (ν.map e) (hμν.map e.measurable)
  rwa [Measure.map_map e.symm.measurable e.measurable,
       Measure.map_map e.symm.measurable e.measurable,
       e.symm_comp_self, Measure.map_id, Measure.map_id] at hle2

/-- Absolute continuity tensorizes over `Measure.pi` on `Fin n`. -/
lemma pi_ac_fin {X : Type*} [MeasurableSpace X] :
    ∀ (n : ℕ) (P Q : Fin n → Measure X), (∀ i, IsFiniteMeasure (P i)) →
      (∀ i, IsFiniteMeasure (Q i)) → (∀ i, P i ≪ Q i) → Measure.pi P ≪ Measure.pi Q := by
  intro n
  induction n with
  | zero =>
      intro P Q _ _ _
      rw [Measure.pi_of_empty P, Measure.pi_of_empty Q]
  | succ n ih =>
      intro P Q hPf hQf hac
      have : ∀ i, IsFiniteMeasure (P i) := hPf
      have : ∀ i, IsFiniteMeasure (Q i) := hQf
      set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => X) 0 with hedef
      have hmpP := measurePreserving_piFinSuccAbove P 0
      have hmpQ := measurePreserving_piFinSuccAbove Q 0
      have htail : Measure.pi (fun j => P ((0 : Fin (n + 1)).succAbove j))
          ≪ Measure.pi (fun j => Q ((0 : Fin (n + 1)).succAbove j)) :=
        ih _ _ (fun j => hPf _) (fun j => hQf _) (fun j => hac _)
      have hprodac : (P 0).prod (Measure.pi (fun j => P ((0 : Fin (n + 1)).succAbove j)))
          ≪ (Q 0).prod (Measure.pi (fun j => Q ((0 : Fin (n + 1)).succAbove j))) :=
        (hac 0).prod htail
      have hPeq : Measure.pi P = (Measure.map e (Measure.pi P)).map e.symm := by
        rw [Measure.map_map e.symm.measurable e.measurable, e.symm_comp_self, Measure.map_id]
      have hQeq : Measure.pi Q = (Measure.map e (Measure.pi Q)).map e.symm := by
        rw [Measure.map_map e.symm.measurable e.measurable, e.symm_comp_self, Measure.map_id]
      rw [hPeq, hQeq, hmpP.map_eq, hmpQ.map_eq]
      exact hprodac.map e.symm.measurable

/-- **Tensorization over `Measure.pi` on `Fin n`**, for finite measures with `Pᵢ ≪ Qᵢ`. -/
theorem hellingerIntegral_pi {X : Type*} [MeasurableSpace X] (hr : 1 < r) :
    ∀ (n : ℕ) (P Q : Fin n → Measure X), (∀ i, IsFiniteMeasure (P i)) →
      (∀ i, IsFiniteMeasure (Q i)) → (∀ i, P i ≪ Q i) →
      hellingerIntegral r (Measure.pi P) (Measure.pi Q) = ∏ i, hellingerIntegral r (P i) (Q i) := by
  intro n
  induction n with
  | zero =>
      intro P Q _ _ _
      rw [Measure.pi_of_empty P, Measure.pi_of_empty Q, Finset.univ_eq_empty, Finset.prod_empty,
          hellingerIntegral_self_prob]
  | succ n ih =>
      intro P Q hPf hQf hac
      have : ∀ i, IsFiniteMeasure (P i) := hPf
      have : ∀ i, IsFiniteMeasure (Q i) := hQf
      set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => X) 0 with hedef
      have hmpP := measurePreserving_piFinSuccAbove P 0
      have hmpQ := measurePreserving_piFinSuccAbove Q 0
      have hpiac : Measure.pi P ≪ Measure.pi Q := pi_ac_fin _ P Q hPf hQf hac
      have htailac : Measure.pi (fun j => P ((0 : Fin (n + 1)).succAbove j))
          ≪ Measure.pi (fun j => Q ((0 : Fin (n + 1)).succAbove j)) :=
        pi_ac_fin _ _ _ (fun j => hPf _) (fun j => hQf _) (fun j => hac _)
      rw [← hellingerIntegral_map_equiv hr e (Measure.pi P) (Measure.pi Q) hpiac,
          hmpP.map_eq, hmpQ.map_eq,
          hellingerIntegral_prod hr _ _ _ _ (hac 0) htailac,
          ih _ _ (fun j => hPf _) (fun j => hQf _) (fun j => hac _),
          ← Fin.prod_univ_succAbove (fun i => hellingerIntegral r (P i) (Q i)) 0]

end Continuous
