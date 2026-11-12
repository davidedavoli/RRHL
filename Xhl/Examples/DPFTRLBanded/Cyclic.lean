import Xhl.Examples.DPFTRLBanded.DerivT

open Continuous

/-!
# The cyclic schedule (Appendix D.5)

As in Algorithm 2 of Choquette-Choo et al., the records are split into `m + 1` residue
groups and round `t` samples only the group `t % (m+1)` (`eligCyc`, the test
`i mod b = t mod b` of Fig. 8 at `b = m + 1`); within the group each record tosses its own
Poisson coin at rate `q`, where they draw a fixed-size batch.  The schedule is banded
(`eligCyc_bandElig`) and allows at most `⌈T/(m+1)⌉` participations
(`card_partRounds_eligCyc`), the truncated last window included.  So
`dpftrlBanded_gen_cyclic_Hellinger` keeps only the encoder's bandedness
`C[r,s] ≠ 0 → r ≤ s + m` as a hypothesis.
-/

open MeasureTheory ProbabilityTheory ENNReal
open scoped NNReal


variable {ident : Type} {M : MemType ident}

namespace DPFTRL.Band

open Continuous

variable {d e n T : ℕ} {τ : Ty} [NeZero T]

variable {p : TParams d e n T T τ} {v : TVars ident d T T τ} {tv : Vars ident .nat}
  {q : ℝ≥0} {uv : Vars ident .bool} {m : ℕ}
  {wv : Vars ident (.prod .bool (.vec ((m + 1) * d)))}

/-! ## The cyclic schedule -/

/-- **Algorithm-2 eligibility**: record `j` is due at round `t` iff `t ≡ j [MOD m+1]`. -/
def eligCyc (m : ℕ) : ℕ → ℕ → Bool := fun j t =>
  decide (t % (m + 1) = j % (m + 1))

/-- **The cyclic schedule is banded**: rounds of one residue class are `m + 1` apart. -/
lemma eligCyc_bandElig (m T j : ℕ) : BandElig (eligCyc m) m T j where
  sep t t' htt' _ ht ht' := by
    simp only [eligCyc, decide_eq_true_eq] at ht ht'
    have hdvd : m + 1 ∣ t' - t :=
      (Nat.modEq_iff_dvd' htt'.le).mp (ht.trans ht'.symm)
    have := Nat.le_of_dvd (by omega) hdvd
    omega

/-- **At most `⌈T/(m+1)⌉ = (T + m)/(m + 1)` participations** under the cyclic schedule: a
    round `t < T` of `P_j` is determined by its quotient by `m + 1`, which is below
    `(T + m)/(m + 1)`. -/
lemma card_partRounds_eligCyc (m T j : ℕ) :
    (partRounds (eligCyc m) T j).card ≤ (T + m) / (m + 1) := by
  classical
  calc (partRounds (eligCyc m) T j).card ≤ (Finset.range ((T + m) / (m + 1))).card := by
        refine Finset.card_le_card_of_injOn (fun t => t / (m + 1)) ?_ ?_
        · intro t ht
          simp only [Finset.mem_coe, partRounds, eligCyc, Finset.mem_filter, Finset.mem_range,
            decide_eq_true_eq] at ht ⊢
          have h1 := Nat.div_le_div_right (c := m + 1) (show t + (m + 1) ≤ T + m by omega)
          rw [Nat.add_div_right t (show 0 < m + 1 by omega)] at h1
          omega
        · intro t ht t' ht' h
          have h : t / (m + 1) = t' / (m + 1) := h
          simp only [Finset.mem_coe, partRounds, eligCyc, Finset.mem_filter, Finset.mem_range,
            decide_eq_true_eq] at ht ht'
          have e1 := Nat.div_add_mod t (m + 1)
          have e2 := Nat.div_add_mod t' (m + 1)
          rw [ht.2, h] at e1
          rw [ht'.2] at e2
          exact e1.symm.trans e2
    _ = (T + m) / (m + 1) := Finset.card_range _

/-! ## The derivation, hypotheses discharged -/

/-- **The readout under the cyclic schedule**: the Hellinger integral of the transcripts
    from two memories whose datasets are adjacent at `j` (either order) is at most one
    factor `Υ_α(q, Γ·c_t, σ²)` per round `t ∈ P_j`; the only hypothesis on the
    encoder is its bandedness. -/
theorem dpftrlBanded_gen_cyclic_Hellinger [Infinite ident] {α : ℝ} (hα : 1 < α)
    (hok : TOK p v) (hct : TCntOK v tv) (hu : UOK v tv tv uv) (hq : q ≤ 1) (hv : p.σ2 ≠ 0) (hC : 0 ≤ p.Cl)
    (hband : ∀ r s : Fin T, p.C r s ≠ 0 → (r : ℕ) ≤ s + m) {j : ℕ} (hj : j < n)
    (m₁ m₂ : M.heap) (hadj : AdjAtSym p.record j (tD v m₁) (tD v m₂)) :
    hellingerIntegral α ((osem (dpftrlBandedGen p v tv q (eligCyc m) uv hok) m₁).map Prod.snd)
        ((osem (dpftrlBandedGen p v tv q (eligCyc m) uv hok) m₂).map Prod.snd)
      ≤ ∏ t ∈ partRounds (eligCyc m) T j, mixBudgetR q (p.Cl * Real.sqrt (colSq p.C t m)) p.σ2 α :=
  dpftrlBanded_gen_Hellinger hα hok hct hu hq hv hC hj
    (eligCyc_bandElig m T j) hband m₁ m₂ hadj
