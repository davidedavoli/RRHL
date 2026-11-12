import Xhl.Logic.Rrhl.Readout
import Xhl.Duality.DualityContStd
import Xhl.Duality.Selection.AePartner

open Continuous

/-!
# Witness-based validity and duality (Proposition 4.2, Appendix C)

`WRhl α P φ c₁ c₂ Q ψ` is the two-witness reading of a judgment: from every pair of
states satisfying `P` there are two finite witnesses on `St M × St M`, both
concentrated on `Q`, whose first (resp. second) marginal is the semantics of `c₁`
(resp. `c₂`), and whose weighted Hellinger integral is at most the pre-budget.

* `rrhl_of_wrhl` — **Proposition 4.2 (weak duality)**: witnesses give validity, for every
  post-weight `ψ`.
* `wrhl_of_rrhl_polish`, `rrhl_iff_wrhl_polish` — **Theorem C.1 (strong duality)** at
  post-weight `1`: on a Polish state space and for a closed postcondition, validity gives
  witnesses as soon as almost every final state of each program has a partner.  The
  partners are chosen measurably a.e. (`Xhl/Duality/Selection/AePartner.lean`).
-/

open MeasureTheory ProbabilityTheory ENNReal

namespace Continuous

variable {ident : Type} {M : MemType ident}


/-- **Witness-based validity**: two finite witnesses on pairs of states, concentrated
    on the postcondition, with the two program semantics as marginals and weighted
    Hellinger integral at most the pre-budget. -/
def WRhl (α : ℝ) (P : St M × St M → Prop) (φ : St M × St M → ℝ≥0∞) (c₁ c₂ : Cmd ident M)
    (Q : St M × St M → Prop) (ψ : St M × St M → ℝ≥0∞) : Prop :=
  ∀ s, P s → ∃ w₁ w₂ : Measure (St M × St M), IsFiniteMeasure w₁ ∧ IsFiniteMeasure w₂ ∧
    w₁.map Prod.fst = osemA c₁ s.1 ∧ w₂.map Prod.snd = osemA c₂ s.2 ∧
    (∀ᵐ p ∂w₁, Q p) ∧ (∀ᵐ p ∂w₂, Q p) ∧ weightedHellingerIntegral α ψ w₁ w₂ ≤ φ s

/-- **Proposition 4.2 (weak duality)**: witness-based validity implies validity, for every
    post-weight. -/
theorem rrhl_of_wrhl {α : ℝ} (hα : 1 < α) {P : St M × St M → Prop}
    {φ : St M × St M → ℝ≥0∞} {c₁ c₂ : Cmd ident M} {Q : St M × St M → Prop}
    {ψ : St M × St M → ℝ≥0∞} (h : WRhl α P φ c₁ c₂ Q ψ) : RRhl α P φ c₁ c₂ Q ψ := by
  intro s hs k₁ k₂ hk₁ hk₂ hk
  obtain ⟨w₁, w₂, hf₁, hf₂, h1, h2, -, hQ₂, hb⟩ := h s hs
  have hK₁ : Measurable fun p : St M × St M => k₁ p.1 := hk₁.comp measurable_fst
  have hK₂ : Measurable fun p : St M × St M => k₂ p.2 := hk₂.comp measurable_snd
  have hpt : ∀ᵐ p ∂w₂, k₁ p.1 ^ α * k₂ p.2 ^ (1 - α) ≤ ψ p :=
    hQ₂.mono fun p hp => hk p hp
  have key := testVal_le_weightedHellingerIntegral_same hα hK₁ hK₂ w₁ w₂ hpt
  rw [testValC, ← h1, ← h2, lintegral_map hk₁ measurable_fst,
    lintegral_map hk₂ measurable_snd]
  exact key.trans hb

section Strong

variable [MetricSpace (St M)] [SecondCountableTopology (St M)] [BorelSpace (St M)]
  [CompleteSpace (St M)] [Nonempty (St M)]

/-- **Theorem C.1 (strong duality)** at post-weight `1`: on a Polish state space and for a
    closed postcondition, validity implies witness-based validity as soon as almost every
    final state of each program has a partner in the postcondition. -/
theorem wrhl_of_rrhl_polish {α : ℝ} (hα : 1 < α)
    {P : St M × St M → Prop} {φ : St M × St M → ℝ≥0∞} {c₁ c₂ : Cmd ident M}
    {Q : St M × St M → Prop} 
    (hQ : IsClosed {p : St M × St M | Q p})
    (hp₁ : ∀ s, P s → ∀ᵐ a ∂(osemA c₁ s.1), ∃ b, Q (a, b))
    (hp₂ : ∀ s, P s → ∀ᵐ b ∂(osemA c₂ s.2), ∃ a, Q (a, b))
    (h : RRhl α P φ c₁ c₂ Q (fun _ => 1)) : WRhl α P φ c₁ c₂ Q (fun _ => 1) := by
  intro s hs
  have := isFiniteMeasure_osemA c₁ s.1
  have := isFiniteMeasure_osemA c₂ s.2
  obtain ⟨f₁, hf₁, hq₁⟩ := exists_measurable_partner_ae_left {p : St M × St M | Q p} hQ
    (osemA c₁ s.1) (hp₁ s hs)
  obtain ⟨f₂, hf₂, hq₂⟩ := exists_measurable_partner_ae {p : St M × St M | Q p} hQ
    (osemA c₂ s.2) (hp₂ s hs)
  have hcod : CodLiftMulC α (fun a b => Q (a, b)) (φ s) (osemA c₁ s.1) (osemA c₂ s.2) :=
    fun k₁ k₂ hk₁ hk₂ hk => h s hs k₁ k₂ hk₁ hk₂ fun p hp => hk p.1 p.2 hp
  obtain ⟨w₁, w₂, hw₁, hw₂, h1, h2, hQ₁', hQ₂', hb⟩ :=
    StdDual.exists_witnesses_of_codLift hα (R := fun a b => Q (a, b)) hQ
      (osemA_univ_le_one c₁ s.1) (osemA_univ_le_one c₂ s.2)
      f₁ hf₁ hq₁ f₂ hf₂ hq₂ hcod
  exact ⟨w₁, w₂, hw₁, hw₂, h1, h2, hQ₁', hQ₂', by rwa [weightedHellingerIntegral_one]⟩

/-- **Theorem C.1**, both directions, under the hypotheses of `wrhl_of_rrhl_polish`. -/
theorem rrhl_iff_wrhl_polish {α : ℝ} (hα : 1 < α)
    {P : St M × St M → Prop} {φ : St M × St M → ℝ≥0∞} {c₁ c₂ : Cmd ident M}
    {Q : St M × St M → Prop} 
    (hQ : IsClosed {p : St M × St M | Q p})
    (hp₁ : ∀ s, P s → ∀ᵐ a ∂(osemA c₁ s.1), ∃ b, Q (a, b))
    (hp₂ : ∀ s, P s → ∀ᵐ b ∂(osemA c₂ s.2), ∃ a, Q (a, b)) :
    RRhl α P φ c₁ c₂ Q (fun _ => 1) ↔ WRhl α P φ c₁ c₂ Q (fun _ => 1) :=
  ⟨wrhl_of_rrhl_polish hα   hQ hp₁ hp₂, rrhl_of_wrhl hα⟩

end Strong

end Continuous
