import Xhl.Examples.DPSGD.LastIterate.Horizon
import Xhl.Divergence.WeakTriangle
import Xhl.Divergence.SubsamplingMironov

/-!
# The last iterate at replace-one adjacency (Appendix E.2, Proposition E.4)

* `ReplF`, `dropRec` — replace-one adjacency at record `j`, and the dataset with record `j`
  set to `⊥`, add/remove-adjacent to both sides of a replace pair;
* `dpsgdLastIter_full_Hellinger` — the schedule at `R = T`: both runs start at `θ₀`, so
  there is no distance to close and `H_α ≤ Υ_α^T`;
* `liL_le_mironov` — the per-round level by Mironov et al. [Theorem 11];
* `dpsgdLastIter_AT_addRemove` — at add/remove adjacency, level
  `(5/2)·β·q²C²/v · min{T, T̄}` with `T̄ = atTbar`;
* `dpsgdLastIter_AT_replace` — **Proposition E.4**, by group privacy through `dropRec j`
  (`hellinger_group_le`) and Lemma 3.7.
-/

open MeasureTheory ProbabilityTheory Continuous
open scoped NNReal ENNReal

namespace DPSGDPaper

/-! ## Replace-one adjacency -/

section Replace

variable {N dx : ℕ}

/-- **Replace-one adjacency at record `i`**: the datasets agree on every record but `i`. -/
def ReplF (N dx : ℕ) (i : Fin (N + 1))
    (DP₁ DP₂ : EuclideanSpace ℝ (Fin ((N + 1) * dx)) × Finset (Fin (N + 1))) : Prop :=
  ∀ j : Fin (N + 1), j ≠ i → recBot dx DP₁.1 DP₁.2 j = recBot dx DP₂.1 DP₂.2 j

/-- The dataset `(D, P)` with record `i` set to `⊥`. -/
def dropRec (i : Fin (N + 1))
    (DP : EuclideanSpace ℝ (Fin ((N + 1) * dx)) × Finset (Fin (N + 1))) :
    EuclideanSpace ℝ (Fin ((N + 1) * dx)) × Finset (Fin (N + 1)) :=
  (DP.1, DP.2.erase i)

/-- Dropping record `i` gives a dataset adjacent at `i` to the original. -/
lemma adjAtSym_dropRec_left (i : Fin (N + 1))
    (DP : EuclideanSpace ℝ (Fin ((N + 1) * dx)) × Finset (Fin (N + 1))) :
    AdjAtSym (recBotN N dx) i DP (dropRec i DP) :=
  (adjAtSym_recBotN_iff N dx).2 (Or.inl ⟨fun j hj => by
      show recBot dx DP.1 DP.2 j = recBot dx DP.1 (DP.2.erase i) j
      rw [recBot_erase, if_neg hj],
    by show recBot dx DP.1 (DP.2.erase i) i = none; rw [recBot_erase, if_pos rfl]⟩)

/-- Dropping record `i` from one side of a replace pair gives a dataset adjacent at `i` to
    the other side. -/
lemma adjAtSym_dropRec_right {i : Fin (N + 1)}
    {DP₁ DP₂ : EuclideanSpace ℝ (Fin ((N + 1) * dx)) × Finset (Fin (N + 1))}
    (h : ReplF N dx i DP₁ DP₂) : AdjAtSym (recBotN N dx) i (dropRec i DP₁) DP₂ :=
  (adjAtSym_recBotN_iff N dx).2 (Or.inr ⟨fun j hj => by
      show recBot dx DP₂.1 DP₂.2 j = recBot dx DP₁.1 (DP₁.2.erase i) j
      rw [recBot_erase, if_neg hj]; exact (h j hj).symm,
    by show recBot dx DP₁.1 (DP₁.2.erase i) i = none; rw [recBot_erase, if_pos rfl]⟩)

end Replace

/-! ## The leaf by Mironov et al.'s Theorem 11 -/

/-- **The per-round level by Mironov et al.'s Theorem 11**: under its hypotheses at order
    `β`, with `σ̄²C² = σ₂` (`σ₂` a variance), `L_β = log Υ_β/(β−1) ≤ 2βq²C²/σ₂`. -/
lemma liL_le_mironov {β : ℝ} (hβ : 1 < β) {q : ℝ≥0} (hq : (q : ℝ) ≤ 1 / 5) {C : ℝ}
    {σ2 : ℝ≥0} {σ : ℝ} (hσv : σ ^ 2 * C ^ 2 = σ2) (hσ : 4 ≤ σ)
    (h₁ : β ≤ σ ^ 2 * Real.log (1 + 1 / ((q : ℝ) * (β - 1))) / 2 - 2 * Real.log σ)
    (h₂ : β ≤ (σ ^ 2 * Real.log (1 + 1 / ((q : ℝ) * (β - 1))) ^ 2 / 2 - Real.log 5
        - 2 * Real.log σ)
      / (Real.log (1 + 1 / ((q : ℝ) * (β - 1))) + Real.log ((q : ℝ) * β) + 1 / (2 * σ ^ 2))) :
    liL q C σ2 β ≤ 2 * β * ((q : ℝ) ^ 2 * C ^ 2 / σ2) := by
  have hle := ENNReal.toReal_le_of_le_ofReal (Real.exp_pos _).le
    (mixBudgetR_le_mironov hβ hq hσv hσ h₁ h₂)
  have hβ0 : 0 ≤ β := by linarith
  have hx : 0 ≤ (β - 1) * (2 * (q : ℝ) ^ 2 * β * C ^ 2 / σ2) :=
    mul_nonneg (by linarith) (by positivity)
  have hlog : Real.log (mixBudgetR q C σ2 β).toReal
      ≤ (β - 1) * (2 * (q : ℝ) ^ 2 * β * C ^ 2 / σ2) := by
    rcases (ENNReal.toReal_nonneg (a := mixBudgetR q C σ2 β)).eq_or_lt with h0 | hpos
    · rw [← h0, Real.log_zero]; exact hx
    · exact (Real.log_le_log hpos hle).trans (le_of_eq (Real.log_exp _))
  rw [liL, div_le_iff₀ (by linarith)]
  calc _ ≤ _ := hlog
    _ = _ := by ring


/-! ## The shifted schedule at `R = T`: the gap is `0` -/

section Full

variable (N dx d T : ℕ)
  (grad : EuclideanSpace ℝ (Fin dx) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
  (C : ℝ≥0)
  (proj : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
  (η : ℝ) (q : ℝ≥0) (i : Fin (N + 1))

/-- **The loop at `R = T`**: both runs start at `θ₀`, every round keeps the models equal
    and pays only the subsampled leaf. -/
theorem tderiv_dpsgdLastIterLoc_full {α : ℝ} (hα : 1 < α) {σ1 σ2 : ℝ≥0} (hσ1 : σ1 ≠ 0)
    (hσ2 : σ2 ≠ 0)
    (θ₀ : EuclideanSpace ℝ (Fin d)) (hm : MeasOK dx d grad)
    (hpm : Measurable proj)
    (hq1 : (q : ℝ) < 1) (hC : 0 < (C : ℝ))
    (hne : ∀ x y, ‖proj x - proj y‖ ≤ ‖x - y‖)
    {Dm : ℝ} (hdiam : ∀ x y, ‖proj x - proj y‖ ≤ Dm) (hη : γv N η q ≠ 0)
    (hstep : ∀ (B : Finset (Fin (N + 1))) (Dv : Fin (N + 1) → Option (EuclideanSpace ℝ (Fin dx))) (u₁ u₂),
      ‖(u₁ - γv N η q • clippedBatchSumD (N := N) grad C B Dv u₁)
        - (u₂ - γv N η q • clippedBatchSumD (N := N) grad C B Dv u₂)‖ ≤ ‖u₁ - u₂‖) :
    TDeriv (M := PMem) α
      (fun s => AdjAtSym (recBotN N dx) i (PMem.get s.1.1 (.prod (.vec ((N + 1) * dx)) (.finset (N + 1))) (dsV N dx).name)
        (PMem.get s.2.1 (.prod (.vec ((N + 1) * dx)) (.finset (N + 1))) (dsV N dx).name) ∧ s.1.2 = s.2.2)
      (fun _ => subDispBudgetSym q (C : ℝ) σ1 σ2 (γv N η q) 0 α ^ T)
      (dpsgdLastIterLoc N dx d T grad C proj η q hm hpm (σ2 + σ1) θ₀)
      (dpsgdLastIterLoc N dx d T grad C proj η q hm hpm (σ2 + σ1) θ₀)
      (fun s => getTh d s.1.1 = getTh d s.2.1 ∧ s.1.2 = s.2.2) (fun _ => 1) := by
  set c := bodyLocLI N dx d grad C proj η q hm hpm (σ2 + σ1) with hcdef
  set z : ℕ → ℝ := fun _ => 0 with hz
  set F : ℕ → ℝ≥0∞ := fun _ => subDispBudgetSym q (C : ℝ) σ1 σ2 (γv N η q) 0 α with hF
  have hround : ∀ k, k < T → TDeriv (M := PMem) α (LInv N dx d i z k) (fun _ => F k)
      c c (LInv N dx d i z (k + 1)) (fun _ => 1) := by
    intro k _
    show TDeriv (M := PMem) α
      (fun s => DInv N dx d i (z k) s ∧ getCnt s.1.1 = k ∧ getCnt s.2.1 = k) (fun _ => F k) c c
      (fun s => DInv N dx d i (z (k + 1)) s ∧ getCnt s.1.1 = k + 1 ∧ getCnt s.2.1 = k + 1)
      (fun _ => 1)
    refine tderiv_bodyLocLI_spend N dx d grad C proj η q i hα hσ1 hσ2 hm hpm
      hq1 hC hne hdiam hη k (a := 0) (zc := 0) le_rfl le_rfl ?_ ?_
    · show min ((0 : ℝ) - 0) Dm ≤ 0
      rw [sub_self]; exact min_le_left _ _
    · intro x y hA hxy B hB
      unfold cbs
      rw [cbs_eq_of_adjS N dx d grad C i hA B hB]
      exact (hstep B (getR N dx y) _ _).trans hxy
  have hloop := tderiv_loopCnt N dx d T i hα c z F
    (fun _ => subDispBudgetSym_ne_zero hα hq1.le hσ2)
    (fun _ => subDispBudgetSym_ne_top hα hq1.le hσ2 _ _ _) hround
  have hprod : (∏ k ∈ Finset.range T, F k)
      = subDispBudgetSym q (C : ℝ) σ1 σ2 (γv N η q) 0 α ^ T := by
    rw [Finset.prod_const, Finset.card_range]
  refine TDeriv.conseq (fun _ h => h) (fun _ _ => le_of_eq hprod) (fun s h => ?_)
    (fun _ _ => le_rfl) (TDeriv.seq ?_ hloop)
  · obtain ⟨_, h2, h3⟩ := h
    exact ⟨sub_eq_zero.mp (norm_le_zero_iff.mp h2), h3⟩
  · refine TDeriv.conseq (fun s hs => ?_) (fun _ _ => le_rfl) (fun _ h => h) (fun _ _ => le_rfl)
      (tderiv_initR d θ₀ (LInv N dx d i z 0) (fun _ => ∏ k ∈ Finset.range T, F k))
    exact LInv_initR N dx d i θ₀ z le_rfl s hs.1 hs.2

/-- `dpsgdLastIter` at `R = T`, including the final `release θ`. -/
theorem dpsgdLastIter_full_deriv {α : ℝ} (hα : 1 < α) {σ1 σ2 : ℝ≥0} (hσ1 : σ1 ≠ 0)
    (hσ2 : σ2 ≠ 0)
    (θ₀ : EuclideanSpace ℝ (Fin d)) (hm : MeasOK dx d grad)
    (hpm : Measurable proj)
    (hq1 : (q : ℝ) < 1) (hC : 0 < (C : ℝ))
    (hne : ∀ x y, ‖proj x - proj y‖ ≤ ‖x - y‖)
    {Dm : ℝ} (hdiam : ∀ x y, ‖proj x - proj y‖ ≤ Dm) (hη : γv N η q ≠ 0)
    (hstep : ∀ (B : Finset (Fin (N + 1))) (Dv : Fin (N + 1) → Option (EuclideanSpace ℝ (Fin dx))) (u₁ u₂),
      ‖(u₁ - γv N η q • clippedBatchSumD (N := N) grad C B Dv u₁)
        - (u₂ - γv N η q • clippedBatchSumD (N := N) grad C B Dv u₂)‖ ≤ ‖u₁ - u₂‖) :
    TDeriv (M := PMem) α
      (fun s => AdjAtSym (recBotN N dx) i (PMem.get s.1.1 (.prod (.vec ((N + 1) * dx)) (.finset (N + 1))) (dsV N dx).name)
        (PMem.get s.2.1 (.prod (.vec ((N + 1) * dx)) (.finset (N + 1))) (dsV N dx).name) ∧ s.1.2 = s.2.2)
      (fun _ => subDispBudgetSym q (C : ℝ) σ1 σ2 (γv N η q) 0 α ^ T)
      (dpsgdLastIter N dx d T grad C proj η q hm hpm (σ2 + σ1) θ₀)
      (dpsgdLastIter N dx d T grad C proj η q hm hpm (σ2 + σ1) θ₀)
      (fun s => s.1.2 = s.2.2) (fun _ => 1) := by
  refine TDeriv.seq
    (Q := liftP (M := PMem) (fun p => getTh d p.1 = getTh d p.2)) (ψ := fun _ => 1) ?_ ?_
  · exact tderiv_dpsgdLastIterLoc_full N dx d T grad C proj η q i hα hσ1 hσ2 θ₀ hm hpm
      hq1 hC hne hdiam hη hstep
  · exact TDeriv.conseq
      (fun s hs => ⟨hs.1, by
        show s.1.2.snoc ⟨_, _⟩ = s.2.2.snoc ⟨_, _⟩
        rw [hs.2]; exact congrArg (fun x => s.2.2.snoc ⟨_, x⟩) hs.1⟩)
      (fun _ _ => le_rfl) (fun _ h => h.2) (fun _ _ => le_rfl)
      (TDeriv.release (M := PMem) (Expr.var (thV d)) (Expr.var (thV d))
        (liftP (fun p => getTh d p.1 = getTh d p.2)) (fun _ => 1))

/-- **The bound at `R = T`**: `H_α ≤ Υ_α^T` on the transcript law. -/
theorem dpsgdLastIter_full_Hellinger {α : ℝ} (hα : 1 < α) {σ1 σ2 : ℝ≥0} (hσ1 : σ1 ≠ 0)
    (hσ2 : σ2 ≠ 0)
    (θ₀ : EuclideanSpace ℝ (Fin d)) (hm : MeasOK dx d grad)
    (hpm : Measurable proj)
    (hq1 : (q : ℝ) < 1) (hC : 0 < (C : ℝ))
    (hne : ∀ x y, ‖proj x - proj y‖ ≤ ‖x - y‖)
    {Dm : ℝ} (hdiam : ∀ x y, ‖proj x - proj y‖ ≤ Dm) (hη : γv N η q ≠ 0)
    (hstep : ∀ (B : Finset (Fin (N + 1))) (Dv : Fin (N + 1) → Option (EuclideanSpace ℝ (Fin dx))) (u₁ u₂),
      ‖(u₁ - γv N η q • clippedBatchSumD (N := N) grad C B Dv u₁)
        - (u₂ - γv N η q • clippedBatchSumD (N := N) grad C B Dv u₂)‖ ≤ ‖u₁ - u₂‖)
    (s₁ s₂ : St PMem)
    (hadj : AdjAtSym (recBotN N dx) i (getDS N dx s₁.1)
      (getDS N dx s₂.1)) (htau : s₁.2 = s₂.2) :
    hellingerIntegral α
      ((osemA (dpsgdLastIter N dx d T grad C proj η q hm hpm (σ2 + σ1) θ₀) s₁).map
        Prod.snd)
      ((osemA (dpsgdLastIter N dx d T grad C proj η q hm hpm (σ2 + σ1) θ₀) s₂).map
        Prod.snd)
      ≤ mixBudgetR q (C : ℝ) σ2 α ^ T := by
  have hd := (dpsgdLastIter_full_deriv N dx d T grad C proj η q i hα hσ1 hσ2 θ₀ hm hpm
      hq1 hC hne hdiam hη hstep).sound hα
  rw [subDispBudgetSym_eq hα hq1.le hσ2] at hd
  refine (rrhl_tr_hellingerIntegral_le hα hd (s₁, s₂) ⟨hadj, htau⟩).trans (le_of_eq ?_)
  simp [subDispBudget]

end Full

/-! ## The add/remove bound in Altschuler–Talwar's shape -/

/-- The horizon `T̄ = max 1 ⌈Δ/(|γ|qC)⌉` of Proposition E.4. -/
noncomputable def atTbar (N : ℕ) (η : ℝ) (q C : ℝ≥0) (Dm : ℝ) : ℕ :=
  max 1 ⌈Dm / (|γv N η q| * q * C)⌉₊

/-- **Group privacy for Hellinger levels**: order-`2α` level `ρ₁` from `P` to `R` and
    order-`(2α−1)` level `ρ₂` from `R` to `Q` give order-`α` level
    `((2α−1)ρ₁ + (2α−2)ρ₂)/(2(α−1))` from `P` to `Q`. -/
lemma hellinger_group_le {Ω : Type*} [MeasurableSpace Ω] {α : ℝ} (hα : 1 < α)
    (P R Q : Measure Ω) [IsFiniteMeasure P] [IsFiniteMeasure R] [IsFiniteMeasure Q]
    {ρ₁ ρ₂ : ℝ}
    (h₁ : hellingerIntegral (2 * α) P R ≤ ENNReal.ofReal (Real.exp ((2 * α - 1) * ρ₁)))
    (h₂ : hellingerIntegral (2 * α - 1) R Q
      ≤ ENNReal.ofReal (Real.exp ((2 * α - 1 - 1) * ρ₂))) :
    hellingerIntegral α P Q ≤ ENNReal.ofReal (Real.exp ((α - 1) *
      (((2 * α - 1) * ρ₁ + (2 * α - 2) * ρ₂) / (2 * (α - 1))))) := by
  by_cases hR : R = 0
  · -- a finite first leg forces `P ≪ R = 0`, so `P = 0` and the left side vanishes
    have hPR : P ≪ R := not_not.1 fun h =>
      ENNReal.ofReal_ne_top (top_le_iff.1 (hellingerIntegral_eq_top_of_not_ac (α := 2 * α) P R h ▸ h₁))
    rw [hR, Measure.absolutelyContinuous_zero_iff] at hPR
    rw [hPR, hellingerIntegral_zero_left (by linarith)]; exact bot_le
  refine (hellingerIntegral_le_sqrt_mul hα P R Q hR).trans ?_
  refine (ENNReal.rpow_le_rpow (mul_le_mul' h₁ h₂) (by norm_num)).trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add,
    ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le (by norm_num), ← Real.exp_mul]
  congr 2
  have : α - 1 ≠ 0 := by linarith
  field_simp
  ring

section ATShape

variable (N dx d T : ℕ)
  (grad : EuclideanSpace ℝ (Fin dx) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
  (C : ℝ≥0)
  (proj : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
  (η : ℝ) (q : ℝ≥0) (i : Fin (N + 1))

/-- **The add/remove bound**: with both noise halves of variance `v = σ̄²C²` and Mironov et
    al.'s Theorem 11 hypotheses at order `β`, the order-`β` level of `dpsgdLastIter` is at
    most `(5/2)·β·q²C²/v · min{T, T̄}` (schedule at `R = min{T, T̄}`). -/
theorem dpsgdLastIter_AT_addRemove {β : ℝ} (hβ : 1 < β) {v : ℝ≥0}
    (θ₀ : EuclideanSpace ℝ (Fin d)) (hm : MeasOK dx d grad)
    (hpm : Measurable proj)
    (hq : (q : ℝ) ≤ 1 / 5) (hC : 0 < (C : ℝ))
    (hne : ∀ x y, ‖proj x - proj y‖ ≤ ‖x - y‖)
    {Dm : ℝ} (hDm : 0 ≤ Dm) (hdiam : ∀ x y, ‖proj x - proj y‖ ≤ Dm) (hη : γv N η q ≠ 0)
    (hstep : ∀ (B : Finset (Fin (N + 1))) (Dv : Fin (N + 1) → Option (EuclideanSpace ℝ (Fin dx))) (u₁ u₂),
      ‖(u₁ - γv N η q • clippedBatchSumD (N := N) grad C B Dv u₁)
        - (u₂ - γv N η q • clippedBatchSumD (N := N) grad C B Dv u₂)‖ ≤ ‖u₁ - u₂‖)
    {σ : ℝ} (hσv : σ ^ 2 * (C : ℝ) ^ 2 = v) (hσ : 4 ≤ σ)
    (h₁ : β ≤ σ ^ 2 * Real.log (1 + 1 / ((q : ℝ) * (β - 1))) / 2 - 2 * Real.log σ)
    (h₂ : β ≤ (σ ^ 2 * Real.log (1 + 1 / ((q : ℝ) * (β - 1))) ^ 2 / 2 - Real.log 5
        - 2 * Real.log σ)
      / (Real.log (1 + 1 / ((q : ℝ) * (β - 1))) + Real.log ((q : ℝ) * β) + 1 / (2 * σ ^ 2)))
    (s₁ s₂ : St PMem)
    (hadj : AdjAtSym (recBotN N dx) i (getDS N dx s₁.1)
      (getDS N dx s₂.1)) (htau : s₁.2 = s₂.2) :
    hellingerIntegral β
      ((osemA (dpsgdLastIter N dx d T grad C proj η q hm hpm (v + v) θ₀) s₁).map
        Prod.snd)
      ((osemA (dpsgdLastIter N dx d T grad C proj η q hm hpm (v + v) θ₀) s₂).map
        Prod.snd)
      ≤ ENNReal.ofReal (Real.exp ((β - 1) * (5 / 2 * β * ((q : ℝ) ^ 2 * (C : ℝ) ^ 2 / v)
          * min (T : ℝ) (atTbar N η q C Dm)))) := by
  have hβ1 : 1 < β := hβ
  have hβ0 : 0 ≤ β := by linarith
  have hq1 : (q : ℝ) < 1 := by linarith
  have hvpos : (0 : ℝ) < v := by
    rw [← hσv]; have : 0 < σ := by linarith
    positivity
  have hv : v ≠ 0 := by intro h; rw [h] at hvpos; simp at hvpos
  set γ := γv N η q with hγ
  have hq0 : (0 : ℝ) < q := by
    rcases (NNReal.coe_nonneg q).eq_or_lt with h | h
    · exfalso; apply hη; rw [hγ, γv, ← h, zero_mul, div_zero]
    · exact h
  set X : ℝ := (q : ℝ) ^ 2 * (C : ℝ) ^ 2 / v with hX
  have hX0 : 0 ≤ X := by positivity
  -- the leaf, by Mironov et al.'s Theorem 11
  have hL : liL q (C : ℝ) v β ≤ 2 * β * X := liL_le_mironov hβ hq hσv hσ h₁ h₂
  have hmono : ∀ ρ ρ' : ℝ, ρ ≤ ρ' → ENNReal.ofReal (Real.exp ((β - 1) * ρ))
      ≤ ENNReal.ofReal (Real.exp ((β - 1) * ρ')) := fun ρ ρ' h =>
    ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left h (by linarith)))
  set Tb := atTbar N η q C Dm with hTb
  rcases le_or_gt T Tb with hT | hT
  · -- `T ≤ T̄`: the schedule at `R = T`, gap `0`
    have h := dpsgdLastIter_full_Hellinger N dx d T grad C proj η q i hβ1 hv hv θ₀ hm hpm
      hq1 hC hne hdiam hη hstep s₁ s₂ hadj htau
    have hΥ : mixBudgetR q (C : ℝ) v β ^ T ≠ ⊤ :=
      ENNReal.pow_ne_top (mixBudgetR_ne_top hβ1 _ _ hv hq1.le)
    refine h.trans ((le_exp_renyiLevel hβ1 hΥ).trans (hmono _ _ ?_))
    rw [ENNReal.toReal_pow, Real.log_pow, mul_div_assoc, ← liL,
      min_eq_left (by exact_mod_cast hT : (T : ℝ) ≤ Tb)]
    have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg _
    have := mul_le_mul_of_nonneg_left hL hT0
    nlinarith [mul_nonneg (mul_nonneg hβ0 hX0) hT0]
  · -- `T̄ < T`: Altschuler–Talwar's schedule with `R = T̄` spending rounds
    have hR1 : 1 ≤ Tb := le_max_left _ _
    have hRpos : (0 : ℝ) < Tb := by exact_mod_cast hR1
    have h := dpsgdLastIter_Hellinger N dx d T grad C proj η q i hβ1 hv hv θ₀ hm hpm
      hq1 hC hne hDm hdiam hη hstep s₁ s₂ hadj htau
    refine h.trans ((iInf_le _ ⟨Tb, Finset.mem_Icc.mpr ⟨hR1, hT.le⟩⟩).trans ?_)
    have hΩtop : subDispBudget q (C : ℝ) v v γ (Dm / Tb) β ^ Tb ≠ ⊤ :=
      ENNReal.pow_ne_top (subDispBudget_ne_top hβ1 hq1.le hv _ _ _)
    refine (le_exp_renyiLevel hβ1 hΩtop).trans (hmono _ _ ?_)
    rw [log_subDispBudget_pow hβ1 hq1 hv hv hη Dm hR1,
      min_eq_right (by exact_mod_cast hT.le : (Tb : ℝ) ≤ T)]
    have hγ0 : 0 < |γ| := abs_pos.2 hη
    have hden : 0 < |γ| * q * C := by positivity
    -- `Dm ≤ T̄·|γ|qC`, from the ceiling
    have hDmR : Dm ≤ Tb * (|γ| * q * C) := by
      have h1 : Dm / (|γ| * q * C) ≤ Tb := by
        refine (Nat.le_ceil _).trans ?_
        exact_mod_cast le_max_right _ _
      exact (div_le_iff₀ hden).1 h1
    -- the shift cost: `K/T̄ ≤ β·T̄·X/2`
    have hK : liK v γ Dm β / Tb ≤ β * Tb * X / 2 := by
      have key : β * Dm ^ 2 ≤ β * (Tb * (|γ| * q * C)) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hDm hDmR 2) hβ0
      have hγ2 : 0 < γ ^ 2 := by positivity
      unfold liK
      rw [div_div, div_le_iff₀ (by positivity)]
      calc β * Dm ^ 2 ≤ β * (Tb * (|γ| * q * C)) ^ 2 := key
        _ = β * Tb * X / 2 * (2 * γ ^ 2 * v * Tb) := by
          rw [hX, mul_pow, mul_pow, mul_pow, sq_abs]
          field_simp
    have := mul_le_mul_of_nonneg_left hL hRpos.le
    nlinarith [mul_nonneg (mul_nonneg hβ0 hX0) hRpos.le]

/-- **Proposition E.4 (last iterate at replace-one adjacency)**: for `α ≥ 3/2`, `q ≤ 1/5`,
    `σ ≥ 4C` and Mironov et al.'s Theorem 11 conditions at `2α` and `2α − 1` (`hord`),
    `dpsgdLastIter` with noise variance `σ² + σ²` is `(α, 20·α·q²C²/σ² · min{T, T̄})`-RDP at
    `⋃ j, ReplF N dx j`.  The paper's hypotheses on the losses and `η` enter only through
    the non-expansive step `hstep`, assumed here directly. -/
theorem dpsgdLastIter_AT_replace {α : ℝ} (hα : 3 / 2 ≤ α) {σ : ℝ≥0}
    (θ₀ : EuclideanSpace ℝ (Fin d)) (hm : MeasOK dx d grad)
    (hpm : Measurable proj)
    (hq : (q : ℝ) ≤ 1 / 5) (hC : 0 < (C : ℝ)) (hσ : 4 * (C : ℝ) ≤ σ)
    (hne : ∀ x y, ‖proj x - proj y‖ ≤ ‖x - y‖)
    {Dm : ℝ} (hDm : 0 ≤ Dm) (hdiam : ∀ x y, ‖proj x - proj y‖ ≤ Dm) (hη : γv N η q ≠ 0)
    (hstep : ∀ (B : Finset (Fin (N + 1))) (Dv : Fin (N + 1) → Option (EuclideanSpace ℝ (Fin dx))) (u₁ u₂),
      ‖(u₁ - γv N η q • clippedBatchSumD (N := N) grad C B Dv u₁)
        - (u₂ - γv N η q • clippedBatchSumD (N := N) grad C B Dv u₂)‖ ≤ ‖u₁ - u₂‖)
    (hord : ∀ α' ∈ ({2 * α, 2 * α - 1} : Set ℝ),
      α' ≤ ((σ : ℝ) / C) ^ 2 * Real.log (1 + 1 / ((q : ℝ) * (α' - 1))) / 2
          - 2 * Real.log ((σ : ℝ) / C) ∧
      α' ≤ (((σ : ℝ) / C) ^ 2 * Real.log (1 + 1 / ((q : ℝ) * (α' - 1))) ^ 2 / 2
          - Real.log 5 - 2 * Real.log ((σ : ℝ) / C))
        / (Real.log (1 + 1 / ((q : ℝ) * (α' - 1))) + Real.log ((q : ℝ) * α')
          + 1 / (2 * ((σ : ℝ) / C) ^ 2))) :
    RenyiDP α
      (20 * α * ((q : ℝ) ^ 2 * (C : ℝ) ^ 2 / (σ : ℝ) ^ 2) * min (T : ℝ) (atTbar N η q C Dm))
      (fun m₁ m₂ : PMem.heap => ∃ j : Fin (N + 1),
        ReplF N dx j (getDS N dx m₁)
          (getDS N dx m₂))
      (fun m => (osem (dpsgdLastIter N dx d T grad C proj η q hm hpm (σ ^ 2 + σ ^ 2) θ₀)
        m).map Prod.snd) := by
  have hα1 : 1 < α := by linarith
  obtain ⟨v, hvdef⟩ : ∃ v : ℝ≥0, v = σ ^ 2 := ⟨_, rfl⟩
  have hvR : (v : ℝ) = (σ : ℝ) ^ 2 := by rw [hvdef]; push_cast; rfl
  have hσv : ((σ : ℝ) / C) ^ 2 * (C : ℝ) ^ 2 = v := by rw [hvR]; field_simp
  have hσ4 : 4 ≤ (σ : ℝ) / C := by rw [le_div_iff₀ hC]; linarith
  obtain ⟨h₁a, h₂a⟩ := hord (2 * α) (by simp)
  obtain ⟨h₁b, h₂b⟩ := hord (2 * α - 1) (by simp)
  rw [← hvdef]
  set c := dpsgdLastIter N dx d T grad C proj η q hm hpm (v + v) θ₀
  -- individually at each replace-one adjacency `ReplF N dx j`
  have hind : IndivRenyiDP α
      (fun _ : Fin (N + 1) =>
        20 * α * ((q : ℝ) ^ 2 * (C : ℝ) ^ 2 / (σ : ℝ) ^ 2) * min (T : ℝ) (atTbar N η q C Dm))
      (fun (j : Fin (N + 1)) (m₁ m₂ : PMem.heap) =>
        ReplF N dx j (getDS N dx m₁) (getDS N dx m₂))
      (fun m => (osem c m).map Prod.snd) := by
    intro j
    refine fun m₁ m₂ hadj => (renyiDiv_le_coe_iff hα1 _ _).2 <| ?_
    set D₁ := PMem.get m₁ (.prod (.vec ((N + 1) * dx)) (.finset (N + 1))) (dsV N dx).name
    let s₀ : St PMem := (PMem.set m₁ (.prod (.vec ((N + 1) * dx)) (.finset (N + 1)))
      (dsV N dx).name (dropRec j D₁), Tr.nil)
    have hD₀ : getDS N dx s₀.1 = dropRec j D₁ :=
      PMem.get_set_eq _ _ _ _
    have hfin : ∀ s : St PMem, IsFiniteMeasure ((osemA c s).map Prod.snd) := fun s =>
      @Measure.isFiniteMeasure_map _ _ _ _ _ (isFiniteMeasure_osemA _ s) _
    have h₁ := dpsgdLastIter_AT_addRemove N dx d T grad C proj η q j
      (by linarith : (1 : ℝ) < 2 * α) θ₀ hm hpm hq hC hne hDm hdiam hη hstep hσv hσ4 h₁a h₂a
      (m₁, Tr.nil) s₀ (by rw [hD₀]; exact adjAtSym_dropRec_left j D₁) rfl
    have h₂ := dpsgdLastIter_AT_addRemove N dx d T grad C proj η q j
      (by linarith : (1 : ℝ) < 2 * α - 1) θ₀ hm hpm hq hC hne hDm hdiam hη hstep hσv hσ4
      h₁b h₂b s₀ (m₂, Tr.nil) (by rw [hD₀]; exact adjAtSym_dropRec_right hadj) rfl
    have := hfin (m₁, Tr.nil); have := hfin s₀; have := hfin (m₂, Tr.nil)
    refine (hellinger_group_le hα1 _ ((osemA c s₀).map Prod.snd) _ h₁ h₂).trans ?_
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2
      (mul_le_mul_of_nonneg_left ?_ (by linarith)))
    -- `((2α−1)·(5/2)(2α)Y + (2α−2)·(5/2)(2α−1)Y)/(2(α−1)) = 5(2α−1)²Y/(2(α−1)) ≤ 20αY`
    set Y : ℝ := (q : ℝ) ^ 2 * (C : ℝ) ^ 2 / v * min (T : ℝ) (atTbar N η q C Dm) with hY
    have hY0 : 0 ≤ Y := mul_nonneg (by positivity)
      (le_min (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    have hpoly : 0 ≤ 4 * α ^ 2 - 4 * α - 1 := by nlinarith
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < 2 * (α - 1))]
    have e₁ : 5 / 2 * (2 * α) * ((q : ℝ) ^ 2 * (C : ℝ) ^ 2 / v)
        * min (T : ℝ) (atTbar N η q C Dm) = 5 / 2 * (2 * α) * Y := by rw [hY]; ring
    have e₂ : 5 / 2 * (2 * α - 1) * ((q : ℝ) ^ 2 * (C : ℝ) ^ 2 / v)
        * min (T : ℝ) (atTbar N η q C Dm) = 5 / 2 * (2 * α - 1) * Y := by rw [hY]; ring
    have e₃ : 20 * α * ((q : ℝ) ^ 2 * (C : ℝ) ^ 2 / (σ : ℝ) ^ 2)
        * min (T : ℝ) (atTbar N η q C Dm) = 20 * α * Y := by rw [hY, hvR]; ring
    rw [e₁, e₂, e₃]
    nlinarith [mul_nonneg hY0 hpoly]
  -- at their union, by Lemma 3.7
  simpa only [ciSup_const] using hind.renyiDP_iSup (Set.finite_range _).bddAbove


end ATShape

end DPSGDPaper
