import Xhl.Examples.DPSGD.Transcript.Deriv
import Xhl.Divergence.Privacy

/-!
# RDP and (ε,δ) guarantees for DP-SGD in the transcript model (Corollary E.3)

From `dpsgdTranscript_deriv`: individual RDP (Proposition 4.4), RDP at the union of the
adjacencies (Lemma 3.7), and `(ε,δ)`-DP (Proposition 3.5) at

    ε = T·log Υ/(α−1) + log((α−1)/α) − (log δ + log α)/(α−1).
-/

open MeasureTheory ProbabilityTheory Continuous
open scoped NNReal ENNReal

namespace DPSGDPaper

section RelDP

variable (N dx d T : ℕ)
  (grad : EuclideanSpace ℝ (Fin dx) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
  (C : ℝ≥0)
  (η : ℝ) (σ q : ℝ≥0) (i : Fin (N + 1))

/-- **The transcript mechanism is individually RDP** (Def 3.6) for the family
    `AdjAtSym (recBotN N dx) j`, at level `T·log Υ_α/(α−1)`: Proposition 4.4
    (`rrhl_indivRenyiDP`) on `dpsgdTranscript_deriv`, with `max(Υ_α, Λ_α) = Υ_α` by
    Lemma E.1. -/
theorem dpsgdTranscript_IndivRDP {α : ℝ} (hα : 1 < α)
    (θ₀ : EuclideanSpace ℝ (Fin d)) (hm : MeasOK dx d grad)
    (hC : 0 < (C : ℝ))
    (hq1 : (q : ℝ) < 1) (hσC : (σ * C) ^ 2 ≠ 0) :
    Continuous.IndivRenyiDP α
      (fun _ : Fin (N + 1) => ((T : ℝ) * Real.log ((mixBudgetR q (C : ℝ) ((σ * C) ^ 2) α).toReal) / (α - 1)))
      (fun (j : Fin (N + 1)) (m₁ m₂ : PMem.heap) =>
        AdjAtSym (recBotN N dx) j (getDS N dx m₁) (getDS N dx m₂))
      (fun m => (osem (dpsgdTranscript N dx d T grad C η σ q hm θ₀) m).map Prod.snd) := by
  have hΥtop : mixBudgetR q (C : ℝ) ((σ * C) ^ 2) α ≠ ⊤ := by
    exact mixBudgetR_ne_top hα _ _ hσC hq1.le
  have h := rrhl_indivRenyiDP hα
    (η := fun _ : Fin (N + 1) => mixBudgetR q (C : ℝ) ((σ * C) ^ 2) α ^ T)
    (fun _ => ENNReal.pow_ne_top hΥtop)
    (Adj := fun (j : Fin (N + 1)) (m₁ m₂ : PMem.heap) =>
      AdjAtSym (recBotN N dx) j (getDS N dx m₁) (getDS N dx m₂))
    (c := dpsgdTranscript N dx d T grad C η σ q hm θ₀) fun j => by
      have hd := (dpsgdTranscript_deriv N dx d T grad C η σ q j hα θ₀ hm hC hq1
          hσC).sound hα
      rwa [max_mixBudgetR_mixFlipBudgetE hα hq1.le hσC] at hd
  simpa only [ENNReal.toReal_pow, Real.log_pow] using h

/-- **The transcript mechanism is `(α, T·log Υ_α/(α−1))`-RDP** (Def 3.4) at the union
    `⋃ j, AdjAtSym (recBotN N dx) j`: Lemma 3.7 (`IndivRenyiDP.renyiDP_iSup`) on
    `dpsgdTranscript_IndivRDP`. -/
theorem dpsgdTranscript_RDP {α : ℝ} (hα : 1 < α)
    (θ₀ : EuclideanSpace ℝ (Fin d)) (hm : MeasOK dx d grad)
    (hC : 0 < (C : ℝ))
    (hq1 : (q : ℝ) < 1) (hσC : (σ * C) ^ 2 ≠ 0) :
    Continuous.RenyiDP α
      ((T : ℝ) * Real.log ((mixBudgetR q (C : ℝ) ((σ * C) ^ 2) α).toReal) / (α - 1))
      (fun m₁ m₂ => ∃ j : Fin (N + 1), AdjAtSym (recBotN N dx) j (getDS N dx m₁) (getDS N dx m₂))
      (fun m => (osem (dpsgdTranscript N dx d T grad C η σ q hm θ₀) m).map Prod.snd) := by
  simpa only [ciSup_const] using
    (dpsgdTranscript_IndivRDP N dx d T grad C η σ q hα θ₀ hm hC hq1
      hσC).renyiDP_iSup (Set.finite_range _).bddAbove

/-- **Corollary E.3**: the transcript mechanism is `(ε,δ)`-DP at the union of the
    adjacencies, by Proposition 3.5 (`RenyiDP.epsilonDeltaDP`) on `dpsgdTranscript_RDP`. -/
theorem dpsgdTranscript_DP {α : ℝ} (hα : 1 < α)
    (θ₀ : EuclideanSpace ℝ (Fin d)) (hm : MeasOK dx d grad)
    (hC : 0 < (C : ℝ))
    (hq1 : (q : ℝ) < 1) (hσC : (σ * C) ^ 2 ≠ 0) {δ : ℝ} (hδ0 : 0 < δ) :
    Continuous.EpsilonDeltaDP
      ((T : ℝ) * Real.log ((mixBudgetR q (C : ℝ) ((σ * C) ^ 2) α).toReal) / (α - 1)
        + Real.log ((α - 1) / α) - (Real.log δ + Real.log α) / (α - 1)) δ
      (fun m₁ m₂ => ∃ j : Fin (N + 1), AdjAtSym (recBotN N dx) j (getDS N dx m₁) (getDS N dx m₂))
      (fun m => (osem (dpsgdTranscript N dx d T grad C η σ q hm θ₀) m).map Prod.snd) := by
  have hfin : ∀ m : PMem.heap, IsFiniteMeasure
      ((osem (dpsgdTranscript N dx d T grad C η σ q hm θ₀) m).map Prod.snd) := fun m =>
    @Measure.isFiniteMeasure_map _ _ _ _ _ (isFiniteMeasure_osemA _ (m, Tr.nil)) _
  exact @Continuous.RenyiDP.epsilonDeltaDP _ _ _ _ _ _ hα hδ0 _ _ hfin
    (dpsgdTranscript_RDP N dx d T grad C η σ q hα θ₀
      hm hC hq1 hσC)

end RelDP

end DPSGDPaper
