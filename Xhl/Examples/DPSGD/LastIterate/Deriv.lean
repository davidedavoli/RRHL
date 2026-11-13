import Xhl.Examples.DPSGD.LastIterate.SpendRound
import Xhl.Examples.DPSGD.LastIterate.BurnRound
import Xhl.Examples.DPSGD.Shared.LocalSupport
import Xhl.Logic.Rrhl.Deriv

/-!
# DP-SGD in the last-iterate model (§5.1.3, Appendix E.2)

`dpsgdLastIter_deriv` derives judgment (8) for `dpsgdLastIter`, for each record `i` at
symmetric adjacency and each `1 ≤ R ≤ T`: `T − R` burning rounds (`tderiv_bodyLocLI_burn`,
no cost, distance kept below `Δ` by the projection) followed by `R` spending rounds
(`tderiv_bodyLocLI_spend`, each closing `Δ/R` of the distance), then the final
`release θ`.  The budget is `subDispBudgetSym^R`, which equals `subDispBudget^R` (the
paper's `Ω_α(R)`, with `Δ` in place of `Δ_R`) by Lemma E.1.  `dpsgdLastIter_Hellinger`
reads the bound off on the transcript law and minimizes over `R` outside the logic.
-/

open MeasureTheory ProbabilityTheory Continuous
open scoped NNReal ENNReal

namespace DPSGDPaper

/-! ## The last iterate: the loop, with no trace variable -/

section LastIterRel

variable (N dx d T : ℕ)
  (grad : EuclideanSpace ℝ (Fin dx) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
  (C : ℝ≥0)
  (proj : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
  (η : ℝ) (q : ℝ≥0) (i : Fin (N + 1))

/-- The initialization establishes the loop invariant at `k = 0`. -/
lemma LInv_initR (θ₀ : EuclideanSpace ℝ (Fin d)) (z : ℕ → ℝ) (hz0 : 0 ≤ z 0)
    (s : St PMem × St PMem)
    (hadj : AdjAtSym (recBotN N dx) i (PMem.get s.1.1 (.prod (.vec ((N + 1) * dx)) (.finset (N + 1))) (dsV N dx).name)
      (PMem.get s.2.1 (.prod (.vec ((N + 1) * dx)) (.finset (N + 1))) (dsV N dx).name)) (htau : s.1.2 = s.2.2) :
    LInv N dx d i z 0 (initFR d θ₀ s.1, initFR d θ₀ s.2) := by
  refine ⟨⟨?_, ?_, htau⟩, ?_, ?_⟩
  · show AdjAtSym (recBotN N dx) i
      (PMem.get (PMem.set (PMem.set s.1.1 (.vec d) (thV d).name θ₀) .nat cnt.name 0)
        (.prod (.vec ((N + 1) * dx)) (.finset (N + 1))) (dsV N dx).name)
      (PMem.get (PMem.set (PMem.set s.2.1 (.vec d) (thV d).name θ₀) .nat cnt.name 0)
        (.prod (.vec ((N + 1) * dx)) (.finset (N + 1))) (dsV N dx).name)
    rw [PMem.get_set_ne _ _ _ _ _ _ (by slot_ne), PMem.get_set_ne _ _ _ _ _ _ (by slot_ne),
      PMem.get_set_ne _ _ _ _ _ _ (by slot_ne), PMem.get_set_ne _ _ _ _ _ _ (by slot_ne)]
    exact hadj
  · show ‖PMem.get (PMem.set (PMem.set s.1.1 (.vec d) (thV d).name θ₀) .nat cnt.name 0)
        (.vec d) (thV d).name
      - PMem.get (PMem.set (PMem.set s.2.1 (.vec d) (thV d).name θ₀) .nat cnt.name 0)
        (.vec d) (thV d).name‖ ≤ z 0
    rw [PMem.get_set_ne _ _ _ _ _ _ (by slot_ne), PMem.get_set_eq,
      PMem.get_set_ne _ _ _ _ _ _ (by slot_ne), PMem.get_set_eq, sub_self, norm_zero]
    exact hz0
  · show getCnt (PMem.set (PMem.set s.1.1 (.vec d) (thV d).name θ₀) .nat cnt.name 0) = 0
    unfold getCnt; rw [PMem.get_set_eq]
  · show getCnt (PMem.set (PMem.set s.2.1 (.vec d) (thV d).name θ₀) .nat cnt.name 0) = 0
    unfold getCnt; rw [PMem.get_set_eq]

/-- One round of the last-iterate program, from a derivation of its block; the counter is
    pinned at `k` before and `k + 1` after. -/
theorem tderiv_roundLI {α : ℝ} (hpm : Measurable proj)
    (hne : ∀ x y, ‖proj x - proj y‖ ≤ ‖x - y‖)
    {Dm : ℝ} (hdiam : ∀ x y, ‖proj x - proj y‖ ≤ Dm)
    {z z₁ z'' : ℝ} (hz : min z₁ Dm ≤ z'') {Fb : ℝ≥0∞} (k : ℕ)
    (c : Cmd String PMem)
    (hpre : TDeriv (M := PMem) α
      (fun s => DInv N dx d i z s ∧ getCnt s.1.1 = k ∧ getCnt s.2.1 = k) (fun _ => Fb) c c
      (fun s => DPost N dx d i (γv N η q) z₁ s ∧ getCnt s.1.1 = k ∧ getCnt s.2.1 = k)
      (fun _ => 1)) :
    TDeriv (M := PMem) α
      (fun s => DInv N dx d i z s ∧ getCnt s.1.1 = k ∧ getCnt s.2.1 = k) (fun _ => Fb)
      (Cmd.seq (Cmd.seq c (Cmd.assign (thV d) (modelUpdProjE d proj hpm (γv N η q))))
        (Cmd.assign cnt (incW cnt)))
      (Cmd.seq (Cmd.seq c (Cmd.assign (thV d) (modelUpdProjE d proj hpm (γv N η q))))
        (Cmd.assign cnt (incW cnt)))
      (fun s => DInv N dx d i z'' s ∧ getCnt s.1.1 = k + 1 ∧ getCnt s.2.1 = k + 1)
      (fun _ => 1) := by
  set γ := γv N η q with hγ
  have hupd : TDeriv (M := PMem) α
      (fun s => DPost N dx d i γ z₁ s ∧ getCnt s.1.1 = k ∧ getCnt s.2.1 = k) (fun _ => 1)
      (Cmd.assign (thV d) (modelUpdProjE d proj hpm γ)) (Cmd.assign (thV d) (modelUpdProjE d proj hpm γ))
      (fun s => DInv N dx d i z'' s ∧ getCnt s.1.1 = k ∧ getCnt s.2.1 = k) (fun _ => 1) := by
    refine TDeriv.conseq (fun st h => ?_) (fun _ _ => le_rfl) (fun _ h => h) (fun _ _ => le_rfl)
      (TDeriv.assign (M := PMem) (α := α) (thV d) (modelUpdProjE d proj hpm γ) (thV d)
        (modelUpdProjE d proj hpm γ)
        (fun s => DInv N dx d i z'' s ∧ getCnt s.1.1 = k ∧ getCnt s.2.1 = k) (fun _ => 1))
    obtain ⟨⟨h1, h2, h3⟩, hk1, hk2⟩ := h
    refine ⟨⟨?_, ?_, h3⟩, ?_, ?_⟩
    · show AdjAtSym (recBotN N dx) i (PMem.get (PMem.set st.1.1 (.vec d) (thV d).name _) (.prod (.vec ((N + 1) * dx)) (.finset (N + 1)))
          (dsV N dx).name)
        (PMem.get (PMem.set st.2.1 (.vec d) (thV d).name _) (.prod (.vec ((N + 1) * dx)) (.finset (N + 1))) (dsV N dx).name)
      rw [PMem.get_set_ne _ _ _ _ _ _ (by slot_ne), PMem.get_set_ne _ _ _ _ _ _ (by slot_ne)]
      exact h2
    · show ‖PMem.get (PMem.set st.1.1 (.vec d) (thV d).name _) (.vec d) (thV d).name
        - PMem.get (PMem.set st.2.1 (.vec d) (thV d).name _) (.vec d) (thV d).name‖ ≤ z''
      rw [PMem.get_set_eq, PMem.get_set_eq, esem_modelUpdProjE, esem_modelUpdProjE]
      exact (le_min ((hne _ _).trans h1) (hdiam _ _)).trans hz
    · show getCnt (PMem.set st.1.1 (.vec d) (thV d).name _) = k
      rw [getCnt_set_th]; exact hk1
    · show getCnt (PMem.set st.2.1 (.vec d) (thV d).name _) = k
      rw [getCnt_set_th]; exact hk2
  have hcnt : TDeriv (M := PMem) α
      (fun s => DInv N dx d i z'' s ∧ getCnt s.1.1 = k ∧ getCnt s.2.1 = k) (fun _ => 1)
      (Cmd.assign cnt (incW cnt))
      (Cmd.assign cnt (incW cnt))
      (fun s => DInv N dx d i z'' s ∧ getCnt s.1.1 = k + 1 ∧ getCnt s.2.1 = k + 1)
      (fun _ => 1) := by
    refine TDeriv.conseq (fun st h => ?_) (fun _ _ => le_rfl) (fun _ h => h) (fun _ _ => le_rfl)
      (TDeriv.assign (M := PMem) (α := α) cnt (incW cnt)
        cnt (incW cnt)
        (fun s => DInv N dx d i z'' s ∧ getCnt s.1.1 = k + 1 ∧ getCnt s.2.1 = k + 1) (fun _ => 1))
    obtain ⟨⟨h1, h2, h3⟩, hk1, hk2⟩ := h
    refine ⟨⟨?_, ?_, h3⟩, ?_, ?_⟩
    · show AdjAtSym (recBotN N dx) i (PMem.get (PMem.set st.1.1 .nat cnt.name _) (.prod (.vec ((N + 1) * dx)) (.finset (N + 1)))
          (dsV N dx).name)
        (PMem.get (PMem.set st.2.1 .nat cnt.name _) (.prod (.vec ((N + 1) * dx)) (.finset (N + 1))) (dsV N dx).name)
      rw [PMem.get_set_ne _ _ _ _ _ _ (by slot_ne), PMem.get_set_ne _ _ _ _ _ _ (by slot_ne)]
      exact h1
    · show ‖PMem.get (PMem.set st.1.1 .nat cnt.name _) (.vec d) (thV d).name
        - PMem.get (PMem.set st.2.1 .nat cnt.name _) (.vec d) (thV d).name‖ ≤ z''
      rw [PMem.get_set_ne _ _ _ _ _ _ (by slot_ne), PMem.get_set_ne _ _ _ _ _ _ (by slot_ne)]
      exact h2
    · show getCnt (PMem.set st.1.1 .nat cnt.name (getCnt st.1.1 + 1)) = k + 1
      unfold getCnt; rw [PMem.get_set_eq]
      exact congrArg (· + 1) hk1
    · show getCnt (PMem.set st.2.1 .nat cnt.name (getCnt st.2.1 + 1)) = k + 1
      unfold getCnt; rw [PMem.get_set_eq]
      exact congrArg (· + 1) hk2
  exact TDeriv.seq (TDeriv.seq hpre hupd) hcnt

end LastIterRel

/-! ## The last iterate: the two round forms -/

section LastIterRelBody

variable (N dx d T : ℕ)
  (grad : EuclideanSpace ℝ (Fin dx) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
  (C : ℝ≥0)
  (proj : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
  (η : ℝ) (q : ℝ≥0) (i : Fin (N + 1))

/-- A round that **spends**: the distance after the step, `zc`, is reduced by `a`, at cost
    `subDispBudgetSym(…, a)`. -/
theorem tderiv_bodyLocLI_spend {α : ℝ} (hα : 1 < α) {σ1 σ2 : ℝ≥0} (hσ1 : σ1 ≠ 0) (hσ2 : σ2 ≠ 0)
    (hm : MeasOK dx d grad) (hpm : Measurable proj)
    (hq1 : (q : ℝ) < 1) (hC : 0 < (C : ℝ))
    (hne : ∀ x y, ‖proj x - proj y‖ ≤ ‖x - y‖)
    {Dm : ℝ} (hdiam : ∀ x y, ‖proj x - proj y‖ ≤ Dm) (hη : γv N η q ≠ 0) (k : ℕ)
    {a z zc z'' : ℝ} (ha : 0 ≤ a) (hza : a ≤ zc) (hz : min (zc - a) Dm ≤ z'')
    (hcontr : ∀ x y : PMem.heap, AdjAtSym (recBotN N dx) i (getDS N dx x) (getDS N dx y) →
      ‖getTh d x - getTh d y‖ ≤ z → ∀ B : Finset (Fin (N + 1)), i ∉ B →
        ‖(getTh d x - γv N η q • cbs N dx d grad C x B)
          - (getTh d y - γv N η q • cbs N dx d grad C y B)‖ ≤ zc) :
    TDeriv (M := PMem) α
      (fun s => DInv N dx d i z s ∧ getCnt s.1.1 = k ∧ getCnt s.2.1 = k)
      (fun _ => subDispBudgetSym q (C : ℝ) σ1 σ2 (γv N η q) a α)
      (bodyLocLI N dx d grad C proj η q hm hpm (σ2 + σ1))
      (bodyLocLI N dx d grad C proj η q hm hpm (σ2 + σ1))
      (fun s => DInv N dx d i z'' s ∧ getCnt s.1.1 = k + 1 ∧ getCnt s.2.1 = k + 1)
      (fun _ => 1) :=
  tderiv_roundLI N dx d proj η q i hpm hne hdiam hz k _
    (tderiv_blockLoc_of_split N dx d grad C q σ1 σ2 i hm hq1.le
      (fun s hs => ⟨(DInv_rSt N dx d i z s).2 hs.1,
        by show getCnt (obsPaper N d s.1.1) = k; rw [getCnt_obsPaper]; exact hs.2.1,
        by show getCnt (obsPaper N d s.2.1) = k; rw [getCnt_obsPaper]; exact hs.2.2⟩)
      (fun s hs => ⟨(DPost_rSt N dx d i _ _ s).2 hs.1,
        by show getCnt (obsPaper N d s.1.1) = k; rw [getCnt_obsPaper]; exact hs.2.1,
        by show getCnt (obsPaper N d s.2.1) = k; rw [getCnt_obsPaper]; exact hs.2.2⟩)
      (tderiv_splitSamp N dx d grad C q σ1 σ2 i hα hm hσ1 hσ2 hq1 hC
        hη ha le_rfl (sub_nonneg.2 hza) hcontr
        (fun s => getCnt s.1.1 = k ∧ getCnt s.2.1 = k)
        (fun st w hA =>
          ⟨by show getCnt (PMem.set st.1.1 (.finset (N + 1)) (bchV N).name w.1) = k
              rw [getCnt_set_bch]; exact hA.1,
           by show getCnt (PMem.set st.2.1 (.finset (N + 1)) (bchV N).name w.2) = k
              rw [getCnt_set_bch]; exact hA.2⟩)
        (fun st w hA =>
          ⟨by show getCnt (PMem.set st.1.1 (.vec d) (gV d).name w.1) = k
              rw [getCnt_set_gV]; exact hA.1,
           by show getCnt (PMem.set st.2.1 (.vec d) (gV d).name w.2) = k
              rw [getCnt_set_gV]; exact hA.2⟩)
        (fun st w hA =>
          ⟨by show getCnt (PMem.set st.1.1 (.vec d) (gtV d).name w.1) = k
              rw [getCnt_set_gt]; exact hA.1,
           by show getCnt (PMem.set st.2.1 (.vec d) (gtV d).name w.2) = k
              rw [getCnt_set_gt]; exact hA.2⟩)))

/-- A round that **burns**: no cost; the distance after the step grows by at most
    `|γ|·C`, capped by the projection's diameter. -/
theorem tderiv_bodyLocLI_burn {α : ℝ} (hα : 1 < α) (v : ℝ≥0)
    (hm : MeasOK dx d grad) (hpm : Measurable proj)
    (hne : ∀ x y, ‖proj x - proj y‖ ≤ ‖x - y‖)
    {Dm : ℝ} (hdiam : ∀ x y, ‖proj x - proj y‖ ≤ Dm) (k : ℕ)
    {z zc z'' : ℝ} (hz : min (zc + |γv N η q| * C) Dm ≤ z'')
    (hcontr : ∀ x y : PMem.heap, AdjAtSym (recBotN N dx) i (getDS N dx x) (getDS N dx y) →
      ‖getTh d x - getTh d y‖ ≤ z → ∀ B : Finset (Fin (N + 1)), i ∉ B →
        ‖(getTh d x - γv N η q • cbs N dx d grad C x B)
          - (getTh d y - γv N η q • cbs N dx d grad C y B)‖ ≤ zc) :
    TDeriv (M := PMem) α
      (fun s => DInv N dx d i z s ∧ getCnt s.1.1 = k ∧ getCnt s.2.1 = k) (fun _ => 1)
      (bodyLocLI N dx d grad C proj η q hm hpm v)
      (bodyLocLI N dx d grad C proj η q hm hpm v)
      (fun s => DInv N dx d i z'' s ∧ getCnt s.1.1 = k + 1 ∧ getCnt s.2.1 = k + 1)
      (fun _ => 1) :=
  tderiv_roundLI N dx d proj η q i hpm hne hdiam hz k _
    (tderiv_blockLoc_of_prefix N dx d grad C q v hm
      (fun s hs => ⟨(DInv_rSt N dx d i z s).2 hs.1,
        by show getCnt (obsPaper N d s.1.1) = k; rw [getCnt_obsPaper]; exact hs.2.1,
        by show getCnt (obsPaper N d s.2.1) = k; rw [getCnt_obsPaper]; exact hs.2.2⟩)
      (fun s hs => ⟨(DPost_rSt N dx d i _ _ s).2 hs.1,
        by show getCnt (obsPaper N d s.1.1) = k; rw [getCnt_obsPaper]; exact hs.2.1,
        by show getCnt (obsPaper N d s.2.1) = k; rw [getCnt_obsPaper]; exact hs.2.2⟩)
      (tderiv_prefixLI_burn N dx d grad C q i hα v hm le_rfl
        hcontr (fun s => getCnt s.1.1 = k ∧ getCnt s.2.1 = k)
        (fun st w hA =>
          ⟨by show getCnt (PMem.set st.1.1 (.finset (N + 1)) (bchV N).name w.1) = k
              rw [getCnt_set_bch]; exact hA.1,
           by show getCnt (PMem.set st.2.1 (.finset (N + 1)) (bchV N).name w.2) = k
              rw [getCnt_set_bch]; exact hA.2⟩)
        (fun st w hA =>
          ⟨by show getCnt (PMem.set st.1.1 .bool bv.name w.1) = k
              rw [getCnt_set_bv]; exact hA.1,
           by show getCnt (PMem.set st.2.1 .bool bv.name w.2) = k
              rw [getCnt_set_bv]; exact hA.2⟩)
        (fun st w hA =>
          ⟨by show getCnt (PMem.set st.1.1 .nat jv.name w.1) = k
              rw [getCnt_set_jv]; exact hA.1,
           by show getCnt (PMem.set st.2.1 .nat jv.name w.2) = k
              rw [getCnt_set_jv]; exact hA.2⟩)
        (fun st w hA =>
          ⟨by show getCnt (PMem.set st.1.1 (.vec d) (gV d).name w.1) = k
              rw [getCnt_set_gV]; exact hA.1,
           by show getCnt (PMem.set st.2.1 (.vec d) (gV d).name w.2) = k
              rw [getCnt_set_gV]; exact hA.2⟩)
        (fun st w hA =>
          ⟨by show getCnt (PMem.set st.1.1 (.vec d) (gtV d).name w.1) = k
              rw [getCnt_set_gt]; exact hA.1,
           by show getCnt (PMem.set st.2.1 (.vec d) (gtV d).name w.2) = k
              rw [getCnt_set_gt]; exact hA.2⟩)))

end LastIterRelBody

/-! ## The last iterate: the schedule, the release, and the transcript bound -/

section LastIterRelAT

variable (N dx d T : ℕ)
  (grad : EuclideanSpace ℝ (Fin dx) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
  (C : ℝ≥0)
  (proj : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
  (η : ℝ) (q : ℝ≥0) (i : Fin (N + 1))

/-- The loop of the last-iterate program: `T − R` burning rounds, then `R` spending
    rounds, ending at equal models. -/
theorem tderiv_dpsgdLastIterLoc_AT {α : ℝ} (hα : 1 < α) {σ1 σ2 : ℝ≥0} (hσ1 : σ1 ≠ 0)
    (hσ2 : σ2 ≠ 0)
    (θ₀ : EuclideanSpace ℝ (Fin d)) (hm : MeasOK dx d grad)
    (hpm : Measurable proj)
    (hq1 : (q : ℝ) < 1) (hC : 0 < (C : ℝ))
    (hne : ∀ x y, ‖proj x - proj y‖ ≤ ‖x - y‖)
    {Dm : ℝ} (hDm : 0 ≤ Dm) (hdiam : ∀ x y, ‖proj x - proj y‖ ≤ Dm) (hη : γv N η q ≠ 0)
    (hstep : ∀ (B : Finset (Fin (N + 1))) (Dv : Fin (N + 1) → Option (EuclideanSpace ℝ (Fin dx))) (u₁ u₂),
      ‖(u₁ - γv N η q • clippedBatchSumD (N := N) grad C B Dv u₁)
        - (u₂ - γv N η q • clippedBatchSumD (N := N) grad C B Dv u₂)‖ ≤ ‖u₁ - u₂‖)
    (R : ℕ) (hR1 : 1 ≤ R) (hRT : R ≤ T) :
    TDeriv (M := PMem) α
      (fun s => AdjAtSym (recBotN N dx) i (PMem.get s.1.1 (.prod (.vec ((N + 1) * dx)) (.finset (N + 1))) (dsV N dx).name)
        (PMem.get s.2.1 (.prod (.vec ((N + 1) * dx)) (.finset (N + 1))) (dsV N dx).name) ∧ s.1.2 = s.2.2)
      (fun _ => subDispBudgetSym q (C : ℝ) σ1 σ2 (γv N η q) (Dm / R) α ^ R)
      (dpsgdLastIterLoc N dx d T grad C proj η q hm hpm (σ2 + σ1) θ₀)
      (dpsgdLastIterLoc N dx d T grad C proj η q hm hpm (σ2 + σ1) θ₀)
      (fun s => getTh d s.1.1 = getTh d s.2.1 ∧ s.1.2 = s.2.2) (fun _ => 1) := by
  set c := bodyLocLI N dx d grad C proj η q hm hpm (σ2 + σ1) with hcdef
  set γ := γv N η q with hγ
  have hRpos : (0 : ℝ) < (R : ℝ) := by exact_mod_cast hR1
  set z : ℕ → ℝ := fun k => Dm * ((min (T - k) R : ℕ) : ℝ) / R with hz
  have hz0 : z 0 = Dm := by
    simp only [hz, Nat.sub_zero, min_eq_right hRT]
    field_simp
  have hzT : z T ≤ 0 := by simp [hz]
  have hspend : ∀ k, k < T → T - R ≤ k → z (k + 1) = z k - Dm / R := by
    intro k hk hs
    have h1 : min (T - k) R = T - k := min_eq_left (by omega)
    have h2 : min (T - (k + 1)) R = T - (k + 1) := min_eq_left (by omega)
    have h3 : ((T - k : ℕ) : ℝ) = ((T - (k + 1) : ℕ) : ℝ) + 1 := by
      have : T - k = (T - (k + 1)) + 1 := by omega
      rw [this]; push_cast; ring
    simp only [hz, h1, h2, h3]
    field_simp
    ring
  set F : ℕ → ℝ≥0∞ := fun k => if T - R ≤ k then subDispBudgetSym q (C : ℝ) σ1 σ2 γ (Dm / R) α
    else 1 with hF
  have hF0 : ∀ k, F k ≠ 0 := fun k => by
    by_cases h : T - R ≤ k
    · simp only [hF, h, if_true]
      exact subDispBudgetSym_ne_zero hα hq1.le hσ2
    · simp only [hF, h, if_false]; exact one_ne_zero
  have hFt : ∀ k, F k ≠ ⊤ := fun k => by
    by_cases h : T - R ≤ k
    · simp only [hF, h, if_true]; exact subDispBudgetSym_ne_top hα hq1.le hσ2 (C : ℝ) γ (Dm / R)
    · simp only [hF, h, if_false]; exact ENNReal.one_ne_top
  have hround : ∀ k, k < T → TDeriv (M := PMem) α (LInv N dx d i z k) (fun _ => F k)
      c c
      (LInv N dx d i z (k + 1)) (fun _ => 1) := by
    intro k hk
    show TDeriv (M := PMem) α
      (fun s => DInv N dx d i (z k) s ∧ getCnt s.1.1 = k ∧ getCnt s.2.1 = k) (fun _ => F k) c c
      (fun s => DInv N dx d i (z (k + 1)) s ∧ getCnt s.1.1 = k + 1 ∧ getCnt s.2.1 = k + 1)
      (fun _ => 1)
    by_cases hs : T - R ≤ k
    · -- a round that spends
      simp only [hF, hs, if_true]
      refine tderiv_bodyLocLI_spend N dx d grad C proj η q i hα hσ1 hσ2 hm hpm
        hq1 hC hne hdiam hη k (a := Dm / R) (zc := z k)
        (div_nonneg hDm hRpos.le) ?_ ?_ ?_
      · have h1 : min (T - k) R = T - k := min_eq_left (by omega)
        have h2 : (1 : ℝ) ≤ ((T - k : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ T - k)
        simp only [hz, h1]
        rw [mul_div_assoc]
        calc Dm / R = Dm * (1 / R) := by ring
          _ ≤ Dm * (((T - k : ℕ) : ℝ) / R) :=
            mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right h2 hRpos.le) hDm
      · rw [hspend k hk hs]; exact min_le_left _ _
      · intro x y hA hxy B hB
        unfold cbs
        rw [cbs_eq_of_adjS N dx d grad C i hA B hB]
        exact (hstep B (getR N dx y) _ _).trans hxy
    · -- a round that does not spend
      simp only [hF, hs, if_false]
      have h2 : min (T - (k + 1)) R = R := min_eq_right (by omega)
      have hz1 : z (k + 1) = Dm := by simp only [hz, h2]; field_simp
      exact tderiv_bodyLocLI_burn N dx d grad C proj η q i hα (σ2 + σ1) hm hpm hne hdiam k (zc := z k + 2 * |γ| * ((N + 1) * C))
        (by rw [hz1]; exact min_le_right _ _)
        (fun x y _ hxy B _ => step_le_any N dx d grad C γ x y B hxy)
  have hloop := tderiv_loopCnt N dx d T i hα c z F hF0 hFt hround
  have hprod : (∏ k ∈ Finset.range T, F k) = subDispBudgetSym q (C : ℝ) σ1 σ2 γ (Dm / R) α ^ R := by
    rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
    have hcard : (Finset.filter (fun k => T - R ≤ k) (Finset.range T)).card = R := by
      have : Finset.filter (fun k => T - R ≤ k) (Finset.range T) = Finset.Ico (T - R) T := by
        ext k; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
      rw [this, Nat.card_Ico]; omega
    rw [hcard]
  refine TDeriv.conseq (fun _ h => h) (fun _ _ => le_of_eq hprod) (fun s h => ?_)
    (fun _ _ => le_rfl) (TDeriv.seq ?_ hloop)
  · obtain ⟨_, h2, h3⟩ := h
    exact ⟨sub_eq_zero.mp (norm_le_zero_iff.mp (h2.trans hzT)), h3⟩
  · refine TDeriv.conseq (fun s hs => ?_) (fun _ _ => le_rfl) (fun _ h => h) (fun _ _ => le_rfl)
      (tderiv_initR d θ₀ (LInv N dx d i z 0) (fun _ => ∏ k ∈ Finset.range T, F k))
    exact LInv_initR N dx d i θ₀ z (hz0 ▸ hDm) s hs.1 hs.2

/-- **Judgment (9) of §5.1.3**, at `R` spending rounds: adjacent datasets and equal
    transcripts to equal transcripts, at budget `subDispBudgetSym(…, Δ/R)^R`; the final
    `release θ` is free since the two models are equal. -/
theorem dpsgdLastIter_deriv {α : ℝ} (hα : 1 < α) {σ1 σ2 : ℝ≥0} (hσ1 : σ1 ≠ 0)
    (hσ2 : σ2 ≠ 0)
    (θ₀ : EuclideanSpace ℝ (Fin d)) (hm : MeasOK dx d grad)
    (hpm : Measurable proj)
    (hq1 : (q : ℝ) < 1) (hC : 0 < (C : ℝ))
    (hne : ∀ x y, ‖proj x - proj y‖ ≤ ‖x - y‖)
    {Dm : ℝ} (hDm : 0 ≤ Dm) (hdiam : ∀ x y, ‖proj x - proj y‖ ≤ Dm) (hη : γv N η q ≠ 0)
    (hstep : ∀ (B : Finset (Fin (N + 1))) (Dv : Fin (N + 1) → Option (EuclideanSpace ℝ (Fin dx))) (u₁ u₂),
      ‖(u₁ - γv N η q • clippedBatchSumD (N := N) grad C B Dv u₁)
        - (u₂ - γv N η q • clippedBatchSumD (N := N) grad C B Dv u₂)‖ ≤ ‖u₁ - u₂‖)
    (R : ℕ) (hR1 : 1 ≤ R) (hRT : R ≤ T) :
    TDeriv (M := PMem) α
      (fun s => AdjAtSym (recBotN N dx) i (PMem.get s.1.1 (.prod (.vec ((N + 1) * dx)) (.finset (N + 1))) (dsV N dx).name)
        (PMem.get s.2.1 (.prod (.vec ((N + 1) * dx)) (.finset (N + 1))) (dsV N dx).name) ∧ s.1.2 = s.2.2)
      (fun _ => subDispBudgetSym q (C : ℝ) σ1 σ2 (γv N η q) (Dm / R) α ^ R)
      (dpsgdLastIter N dx d T grad C proj η q hm hpm (σ2 + σ1) θ₀)
      (dpsgdLastIter N dx d T grad C proj η q hm hpm (σ2 + σ1) θ₀)
      (fun s => s.1.2 = s.2.2) (fun _ => 1) := by
  refine TDeriv.seq
    (Q := liftP (M := PMem) (fun p => getTh d p.1 = getTh d p.2)) (ψ := fun _ => 1) ?_ ?_
  · exact tderiv_dpsgdLastIterLoc_AT N dx d T grad C proj η q i hα hσ1 hσ2 θ₀ hm hpm
      hq1 hC hne hDm hdiam hη hstep R hR1 hRT
  · exact TDeriv.conseq
      (fun s hs => ⟨hs.1, by
        show s.1.2.snoc ⟨_, _⟩ = s.2.2.snoc ⟨_, _⟩
        rw [hs.2]; exact congrArg (fun x => s.2.2.snoc ⟨_, x⟩) hs.1⟩)
      (fun _ _ => le_rfl) (fun _ h => h.2) (fun _ _ => le_rfl)
      (TDeriv.release (M := PMem) (Expr.var (thV d)) (Expr.var (thV d))
        (liftP (fun p => getTh d p.1 = getTh d p.2)) (fun _ => 1))

/-- **The last-iterate bound**: the Hellinger integral of the two transcript laws is at
    most `min_{1 ≤ R ≤ T} subDispBudget(…, Δ/R)^R`, from `dpsgdLastIter_deriv` (one per
    `R`) by `TDeriv.sound` and `rrhl_tr_hellingerIntegral_le`. -/
theorem dpsgdLastIter_Hellinger {α : ℝ} (hα : 1 < α) {σ1 σ2 : ℝ≥0} (hσ1 : σ1 ≠ 0)
    (hσ2 : σ2 ≠ 0)
    (θ₀ : EuclideanSpace ℝ (Fin d)) (hm : MeasOK dx d grad)
    (hpm : Measurable proj)
    (hq1 : (q : ℝ) < 1) (hC : 0 < (C : ℝ))
    (hne : ∀ x y, ‖proj x - proj y‖ ≤ ‖x - y‖)
    {Dm : ℝ} (hDm : 0 ≤ Dm) (hdiam : ∀ x y, ‖proj x - proj y‖ ≤ Dm) (hη : γv N η q ≠ 0)
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
      ≤ ⨅ R : Finset.Icc 1 T,
        subDispBudget q (C : ℝ) σ1 σ2 (γv N η q) (Dm / (R : ℕ)) α ^ (R : ℕ) := by
  refine le_iInf fun R => ?_
  have hd := (dpsgdLastIter_deriv N dx d T grad C proj η q i hα hσ1 hσ2 θ₀ hm hpm
      hq1 hC hne hDm hdiam hη hstep (R : ℕ)
      (Finset.mem_Icc.mp R.2).1 (Finset.mem_Icc.mp R.2).2).sound hα
  rw [subDispBudgetSym_eq hα hq1.le hσ2] at hd
  exact rrhl_tr_hellingerIntegral_le hα hd (s₁, s₂) ⟨hadj, htau⟩

end LastIterRelAT

end DPSGDPaper
