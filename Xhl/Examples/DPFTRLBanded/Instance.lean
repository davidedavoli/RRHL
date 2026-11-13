import Xhl.Examples.DPFTRLBanded.Cyclic

open Continuous

/-!
# Amplified banded DP-FTRL on `PMem` (Appendix E.5)

`dpftrlBanded` is `dpftrlBandedGen` at the matrix study's fixed variables `tVarsP`, round
counter `t` and coin `u`, on the dataset model of `DPSGD/Shared/Paper.lean`, with the
cyclic eligibility `eligCyc`.  The readouts `dpftrlBanded_Hellinger`,
`dpftrlBanded_IndivRDP` and `dpftrlBanded_uniform_IndivRDP` keep only the parameters'
domains and the bandedness of the encoder as hypotheses.
-/

open MeasureTheory ProbabilityTheory ENNReal
open scoped NNReal

namespace DPFTRL.Band

open DPSGDPaper

variable (N dx d T : ℕ) [NeZero T]
  (grad : EuclideanSpace ℝ (Fin dx) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
  (Cl : ℝ) (σ2 : ℝ≥0) (C : Fin T → Fin T → ℝ) (B : Fin T → Fin T → ℝ) (lam : ℝ)
  (q : ℝ≥0) (m : ℕ)

/-! ## The program -/

/-- The coin. -/
def uvBP : Vars String .bool := ⟨"u"⟩

/-- **Amplified banded DP-FTRL on `PMem`** (Fig. 10): `dpftrlBandedGen` at the matrix study's
    parameters and variables, with the cyclic eligibility `eligCyc m`. -/
noncomputable def dpftrlBanded
    (hgrad : Measurable (fun p : EuclideanSpace ℝ (Fin dx) × EuclideanSpace ℝ (Fin d) =>
      grad p.1 p.2)) : Cmd String PMem :=
  dpftrlBandedGen (tParamsP N dx d T T grad Cl σ2 C B lam (fun _ _ => 0)) (tVarsP N dx d T T) tvMP q
    (eligCyc m) uvBP (tOKP N dx d T T grad Cl σ2 C B lam (fun _ _ => 0) hgrad)

/-! ## The side conditions, at fixed names -/

omit [NeZero T] in
lemma tCntOKBP : TCntOK (tVarsP N dx d T T) tvMP where
  tx := show "t" ≠ "th" by decide
  tacc := show "t" ≠ "acc" by decide
  tz := show "t" ≠ "z" by decide
  ti := show "t" ≠ "i" by decide
  tD := show "t" ≠ "D" by decide
  tH := show "t" ≠ "H" by decide
  tY := show "t" ≠ "Y" by decide

omit [NeZero T] in
lemma uOKBP : UOK (tVarsP N dx d T T) tvMP tvMP uvBP where
  ux := show "u" ≠ "th" by decide
  uacc := show "u" ≠ "acc" by decide
  uz := show "u" ≠ "z" by decide
  ui := show "u" ≠ "i" by decide
  uD := show "u" ≠ "D" by decide
  uH := show "u" ≠ "H" by decide
  uY := show "u" ≠ "Y" by decide
  ut := show "u" ≠ "t" by decide
  ur := show "u" ≠ "t" by decide

/-! ## The readout -/

/-- **Amplified banded DP-FTRL on `PMem`, from the derivation**: for datasets adjacent at
    record `i`, in either order, the Hellinger integral of the transcripts is at most one
    factor `Υ_α(q, Γ·c_t, σ²)` per round `t ∈ P_i`, `c_t² = colSq C t m`. -/
theorem dpftrlBanded_Hellinger {α : ℝ} (hα : 1 < α)
    (hgrad : Measurable (fun p : EuclideanSpace ℝ (Fin dx) × EuclideanSpace ℝ (Fin d) =>
      grad p.1 p.2)) (hq : q ≤ 1) (hσ : σ2 ≠ 0) (hCl : 0 ≤ Cl)
    (hband : ∀ r s : Fin T, C r s ≠ 0 → (r : ℕ) ≤ s + m) (i : Fin (N + 1))
    (m₁ m₂ : PMem.heap) (hadj : AdjAtSym (recBotN N dx) i (getDS N dx m₁) (getDS N dx m₂)) :
    hellingerIntegral α
      ((osem (dpftrlBanded N dx d T grad Cl σ2 C B lam q m hgrad) m₁).map Prod.snd)
      ((osem (dpftrlBanded N dx d T grad Cl σ2 C B lam q m hgrad) m₂).map Prod.snd)
      ≤ ∏ t ∈ partRounds (eligCyc m) T i,
          mixBudgetR q (Cl * Real.sqrt (colSq C t m)) σ2 α :=
  dpftrlBanded_gen_cyclic_Hellinger hα (tOKP N dx d T T grad Cl σ2 C B lam (fun _ _ => 0) hgrad)
    (tCntOKBP N dx d T) (uOKBP N dx d T) hq hσ hCl hband
    i.isLt m₁ m₂ hadj

/-- **`dpftrlBanded` is individually RDP**: for every record `i`, at the adjacency
    `AdjAtSym (recBotN N dx) i` (record `i` removed from either dataset), the law of the transcript is
    `(α, ∑_{t∈P_i} log Υ_α(q, Γ·c_t, σ²)/(α−1))`-RDP.  An instance of
    `dpftrlBanded_gen_IndivRDP`. -/
theorem dpftrlBanded_IndivRDP {α : ℝ} (hα : 1 < α)
    (hgrad : Measurable (fun p : EuclideanSpace ℝ (Fin dx) × EuclideanSpace ℝ (Fin d) =>
      grad p.1 p.2)) (hq : q ≤ 1) (hσ : σ2 ≠ 0) (hCl : 0 ≤ Cl)
    (hband : ∀ r s : Fin T, C r s ≠ 0 → (r : ℕ) ≤ s + m) :
    IndivRenyiDP α
      (fun i : Fin (N + 1) => (∑ t ∈ partRounds (eligCyc m) T i,
        Real.log (mixBudgetR q (Cl * Real.sqrt (colSq C t m)) σ2 α).toReal) / (α - 1))
      (fun (i : Fin (N + 1)) (m₁ m₂ : PMem.heap) => AdjAtSym (recBotN N dx) i (getDS N dx m₁) (getDS N dx m₂))
      (fun μ => (osem (dpftrlBanded N dx d T grad Cl σ2 C B lam q m hgrad) μ).map Prod.snd) :=
  fun i m₁ m₂ hadj => dpftrlBanded_gen_IndivRDP hα
    (tOKP N dx d T T grad Cl σ2 C B lam (fun _ _ => 0) hgrad) (tCntOKBP N dx d T)
    (uOKBP N dx d T) hq hσ hCl (eligCyc_bandElig m T) hband i m₁ m₂
    hadj

/-- **The paper's uniform budget on `PMem`** (Appendix E.5): with every restricted column
    norm at most `c`, `dpftrlBanded` is `(α, k·log Υ_α(q, Γ·c, σ²)/(α−1))`-individually RDP
    at `k = ⌈T/(m+1)⌉ = (T + m)/(m + 1)` (`card_partRounds_eligCyc`). -/
theorem dpftrlBanded_uniform_IndivRDP {α : ℝ} (hα : 1 < α)
    (hgrad : Measurable (fun p : EuclideanSpace ℝ (Fin dx) × EuclideanSpace ℝ (Fin d) =>
      grad p.1 p.2)) (hq : q ≤ 1) (hσ : σ2 ≠ 0) (hCl : 0 ≤ Cl)
    (hband : ∀ r s : Fin T, C r s ≠ 0 → (r : ℕ) ≤ s + m)
    {c : ℝ} (hc : ∀ t, t < T → Real.sqrt (colSq C t m) ≤ c) :
    IndivRenyiDP α
      (fun _ : Fin (N + 1) =>
        (((T + m) / (m + 1) : ℕ) : ℝ) * Real.log (mixBudgetR q (Cl * c) σ2 α).toReal / (α - 1))
      (fun (i : Fin (N + 1)) (m₁ m₂ : PMem.heap) => AdjAtSym (recBotN N dx) i (getDS N dx m₁) (getDS N dx m₂))
      (fun μ => (osem (dpftrlBanded N dx d T grad Cl σ2 C B lam q m hgrad) μ).map Prod.snd) :=
  fun i m₁ m₂ hadj => dpftrlBanded_gen_uniform_IndivRDP hα
    (tOKP N dx d T T grad Cl σ2 C B lam (fun _ _ => 0) hgrad) (tCntOKBP N dx d T)
    (uOKBP N dx d T) hq hσ hCl (eligCyc_bandElig m T) hband hc
    (fun j _ => card_partRounds_eligCyc m T j) i m₁ m₂
    hadj

end DPFTRL.Band
