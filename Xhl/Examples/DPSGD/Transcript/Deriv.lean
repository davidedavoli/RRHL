import Xhl.Examples.DPSGD.Shared.DerivLeaves
import Xhl.Divergence.SubsamplingDomination
import Xhl.Examples.DPSGD.Shared.LocalSupport
import Xhl.Logic.Rrhl.Deriv

/-!
# DP-SGD in the transcript model (§5.1.1, Appendix D.1)

`dpsgdTranscript_deriv` derives the judgment of §5.1.1 for `dpsgdTranscript`, for each
record `i`, at symmetric adjacency `AdjAtSym (recBotN N dx) i`, with postcondition
`τ⟨1⟩ = τ⟨2⟩` and budget `max(Υ, Λ)^T`, which equals `Υ^T` by Lemma D.1
(`max_mixBudgetR_mixFlipBudgetE`).  `dpsgdTranscript_Hellinger` reads
the bound off on the law of the transcript.  The RDP and `(ε,δ)` corollaries are in
`Transcript/DP.lean`.
-/

open MeasureTheory ProbabilityTheory Continuous
open scoped NNReal ENNReal

namespace DPSGDPaper

/-! ## The transcript model: `dpsgdTranscript` -/

section Transcript

variable (N dx d T : ℕ)
  (grad : EuclideanSpace ℝ (Fin dx) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
  (C : ℝ≥0)
  (η : ℝ) (σ q : ℝ≥0) (i : Fin (N + 1))

/-- The memory part of the invariant: adjacent datasets, equal models, counters pinned
    at `k`. -/
def RMem (k : ℕ) (p : PMem.heap × PMem.heap) : Prop :=
  AdjAtSym (recBotN N dx) i (getDS N dx p.1) (getDS N dx p.2) ∧ getTh d p.1 = getTh d p.2 ∧
    getCnt p.1 = getCnt p.2 ∧ getCnt p.1 = k

/-- The memory part after the sampling: `RMem` and equal noisy gradients. -/
def RGtM (k : ℕ) (p : PMem.heap × PMem.heap) : Prop :=
  RMem N dx d i k p ∧ getGt d p.1 = getGt d p.2

/-- The invariant between rounds: the memory part, and equal transcripts. -/
def RInv (k : ℕ) : St PMem × St PMem → Prop := liftP (RMem N dx d i k)

/-- The postcondition of the sampling. -/
def RGt (k : ℕ) : St PMem × St PMem → Prop := liftP (RGtM N dx d i k)

lemma RMem_obsPaper (k : ℕ) (p : PMem.heap × PMem.heap) (h : RMem N dx d i k p) :
    RMem N dx d i k (obsPaper N d p.1, obsPaper N d p.2) := by
  obtain ⟨hadj, hth, hcnteq, hk⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · show AdjAtSym (recBotN N dx) i (getDS N dx (obsPaper N d p.1)) (getDS N dx (obsPaper N d p.2))
    rw [getDS_obsPaper, getDS_obsPaper]; exact hadj
  · show getTh d (obsPaper N d p.1) = getTh d (obsPaper N d p.2)
    rw [getTh_obsPaper, getTh_obsPaper]; exact hth
  · show getCnt (obsPaper N d p.1) = getCnt (obsPaper N d p.2)
    rw [getCnt_obsPaper, getCnt_obsPaper]; exact hcnteq
  · show getCnt (obsPaper N d p.1) = k
    rw [getCnt_obsPaper]; exact hk

lemma RInv_rSt (k : ℕ) (s : St PMem × St PMem) (h : RInv N dx d i k s) :
    RInv N dx d i k (rSt N d s.1, rSt N d s.2) := by
  obtain ⟨hmem, htau⟩ := h
  refine ⟨?_, ?_⟩
  · show RMem N dx d i k (obsPaper N d s.1.1, obsPaper N d s.2.1)
    exact RMem_obsPaper N dx d i k (s.1.1, s.2.1) hmem
  · show s.1.2 = s.2.2
    exact htau

lemma RGt_rSt (k : ℕ) (s : St PMem × St PMem) (h : RGt N dx d i k s) :
    RGt N dx d i k (rSt N d s.1, rSt N d s.2) := by
  obtain ⟨⟨hmem, hgt⟩, htau⟩ := h
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · show RMem N dx d i k (obsPaper N d s.1.1, obsPaper N d s.2.1)
    exact RMem_obsPaper N dx d i k (s.1.1, s.2.1) hmem
  · show getGt d (obsPaper N d s.1.1) = getGt d (obsPaper N d s.2.1)
    rw [getGt_obsPaper, getGt_obsPaper]; exact hgt
  · show s.1.2 = s.2.2
    exact htau

/-- The fused sampling of a round, by **[Samp]**, at budget `max(Υ_α, Λ_α)` with
    clipping radius `C` and variance `(σC)²`. -/
theorem tderiv_sampRel {α : ℝ} (hα : 1 < α) (hm : MeasOK dx d grad)
    (hC : 0 < (C : ℝ))
    (hq1 : (q : ℝ) < 1) (hσC : (σ * C) ^ 2 ≠ 0) (k : ℕ) :
    TDeriv (M := PMem) α (RInv N dx d i k)
      (fun _ => max (mixBudgetR q (C : ℝ) ((σ * C) ^ 2) α) (mixFlipBudgetE q (C : ℝ) ((σ * C) ^ 2) α))
      (Cmd.random (gtV d) (fusedK N dx d grad C ((σ * C) ^ 2) q hm))
      (Cmd.random (gtV d) (fusedK N dx d grad C ((σ * C) ^ 2) q hm))
      (RGt N dx d i k) (fun _ => 1) := by
  refine TDeriv.rnd hα (gtV d) (gtV d) _ _ _ _ _ _ (fun s hs => Filter.Eventually.of_forall fun v => ?_) (fun s hs => ?_)
  · obtain ⟨⟨hadj, hth, hcnteq, hk⟩, htau⟩ := hs
    refine ⟨⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩, htau⟩
    · show AdjAtSym (recBotN N dx) i (getDS N dx (PMem.set s.1.1 (.vec d) (gtV d).name v))
        (getDS N dx (PMem.set s.2.1 (.vec d) (gtV d).name v))
      rw [getDS_set_gt, getDS_set_gt]; exact hadj
    · show getTh d (PMem.set s.1.1 (.vec d) (gtV d).name v)
        = getTh d (PMem.set s.2.1 (.vec d) (gtV d).name v)
      rw [getTh_set_gt, getTh_set_gt]; exact hth
    · show getCnt (PMem.set s.1.1 (.vec d) (gtV d).name v)
        = getCnt (PMem.set s.2.1 (.vec d) (gtV d).name v)
      rw [getCnt_set_gt, getCnt_set_gt]; exact hcnteq
    · show getCnt (PMem.set s.1.1 (.vec d) (gtV d).name v) = k
      rw [getCnt_set_gt]; exact hk
    · show PMem.get (PMem.set s.1.1 (.vec d) (gtV d).name v) (.vec d) (gtV d).name
        = PMem.get (PMem.set s.2.1 (.vec d) (gtV d).name v) (.vec d) (gtV d).name
      rw [PMem.get_set_eq, PMem.get_set_eq]
  · rw [weightedHellingerIntegral_one]
    exact hellingerIntegral_fusedK_le_sym N dx d grad C ((σ * C) ^ 2) q i hα hm hC
      hq1 hσC hs.1.1 hs.1.2.1

/-- The sampling block of a round: `tderiv_blockLoc_of_samp` around `tderiv_sampRel`. -/
theorem tderiv_blockRel {α : ℝ} (hα : 1 < α) (hm : MeasOK dx d grad)
    (hC : 0 < (C : ℝ))
    (hq1 : (q : ℝ) < 1) (hσC : (σ * C) ^ 2 ≠ 0) (k : ℕ) :
    TDeriv (M := PMem) α (RInv N dx d i k)
      (fun _ => max (mixBudgetR q (C : ℝ) ((σ * C) ^ 2) α) (mixFlipBudgetE q (C : ℝ) ((σ * C) ^ 2) α))
      (blockLoc N dx d grad C ((σ * C) ^ 2) q hm)
      (blockLoc N dx d grad C ((σ * C) ^ 2) q hm)
      (RGt N dx d i k) (fun _ => 1) :=
  tderiv_blockLoc_of_samp N dx d grad C _ q hm (RInv_rSt N dx d i k) (RGt_rSt N dx d i k)
    (tderiv_sampRel N dx d grad C σ q i hα hm hC hq1 hσC k)

/-- The round of `dpsgdTranscript`: the block, the update, the release of the noisy gradient,
    the counter. -/
theorem tderiv_bodyRel {α : ℝ} (hα : 1 < α) (hm : MeasOK dx d grad)
    (hC : 0 < (C : ℝ))
    (hq1 : (q : ℝ) < 1) (hσC : (σ * C) ^ 2 ≠ 0) (k : ℕ) :
    TDeriv (M := PMem) α (RInv N dx d i k)
      (fun _ => max (mixBudgetR q (C : ℝ) ((σ * C) ^ 2) α) (mixFlipBudgetE q (C : ℝ) ((σ * C) ^ 2) α))
      (bodyRel N dx d grad C η σ q hm) (bodyRel N dx d grad C η σ q hm)
      (RInv N dx d i (k + 1)) (fun _ => 1) := by
  -- the update: the two models stay equal, because the two noisy gradients are equal
  have hupd : TDeriv (M := PMem) α (RGt N dx d i k) (fun _ => 1)
      (Cmd.assign (thV d) (modelUpdE d (γv N η q)))
      (Cmd.assign (thV d) (modelUpdE d (γv N η q)))
      (RGt N dx d i k) (fun _ => 1) := by
    refine TDeriv.conseq (fun st h => ?_) (fun _ _ => le_rfl) (fun _ h => h) (fun _ _ => le_rfl)
      (TDeriv.assign (M := PMem) (α := α) (thV d) (modelUpdE d (γv N η q)) (thV d)
        (modelUpdE d (γv N η q)) (RGt N dx d i k) (fun _ => 1))
    obtain ⟨⟨⟨hadj, hth, hcnteq, hk⟩, hgt⟩, htau⟩ := h
    refine ⟨⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩, htau⟩
    · show AdjAtSym (recBotN N dx) i (getDS N dx (PMem.set st.1.1 (.vec d) (thV d).name _))
        (getDS N dx (PMem.set st.2.1 (.vec d) (thV d).name _))
      rw [getDS_set_th, getDS_set_th]; exact hadj
    · show getTh d (PMem.set st.1.1 (.vec d) (thV d).name
          (esem (modelUpdE d (γv N η q)) st.1.1))
        = getTh d (PMem.set st.2.1 (.vec d) (thV d).name
          (esem (modelUpdE d (γv N η q)) st.2.1))
      unfold getTh
      have hn : (thV d).name = "th" := rfl
      rw [hn, PMem.get_set_eq, PMem.get_set_eq, esem_modelUpdE, esem_modelUpdE, hth]
      exact congrArg _ (congrArg _ hgt)
    · show getCnt (PMem.set st.1.1 (.vec d) (thV d).name _)
        = getCnt (PMem.set st.2.1 (.vec d) (thV d).name _)
      rw [getCnt_set_th, getCnt_set_th]; exact hcnteq
    · show getCnt (PMem.set st.1.1 (.vec d) (thV d).name _) = k
      rw [getCnt_set_th]; exact hk
    · show getGt d (PMem.set st.1.1 (.vec d) (thV d).name _)
        = getGt d (PMem.set st.2.1 (.vec d) (thV d).name _)
      rw [getGt_set_th, getGt_set_th]; exact hgt
  -- the counter
  have hcnt : TDeriv (M := PMem) α (RGt N dx d i k) (fun _ => 1)
      (Cmd.assign cnt (incW cnt))
      (Cmd.assign cnt (incW cnt))
      (RInv N dx d i (k + 1)) (fun _ => 1) := by
    refine TDeriv.conseq (fun st h => ?_) (fun _ _ => le_rfl) (fun _ h => h) (fun _ _ => le_rfl)
      (TDeriv.assign (M := PMem) (α := α) cnt _ cnt _ (RInv N dx d i (k + 1)) (fun _ => 1))
    obtain ⟨⟨⟨hadj, hth, hcnteq, hk⟩, _⟩, htau⟩ := h
    refine ⟨⟨?_, ?_, ?_, ?_⟩, htau⟩
    · show AdjAtSym (recBotN N dx) i (getDS N dx (PMem.set st.1.1 .nat cnt.name _))
        (getDS N dx (PMem.set st.2.1 .nat cnt.name _))
      rw [getDS_set_cnt, getDS_set_cnt]; exact hadj
    · show getTh d (PMem.set st.1.1 .nat cnt.name _) = getTh d (PMem.set st.2.1 .nat cnt.name _)
      rw [getTh_set_cnt, getTh_set_cnt]; exact hth
    · show getCnt (PMem.set st.1.1 .nat cnt.name (getCnt st.1.1 + 1))
        = getCnt (PMem.set st.2.1 .nat cnt.name (getCnt st.2.1 + 1))
      unfold getCnt at hcnteq ⊢; rw [PMem.get_set_eq, PMem.get_set_eq, hcnteq]
    · show getCnt (PMem.set st.1.1 .nat cnt.name (getCnt st.1.1 + 1)) = k + 1
      unfold getCnt; rw [PMem.get_set_eq]
      exact congrArg (· + 1) hk
  exact TDeriv.seq
    (tderiv_blockRel N dx d grad C σ q i hα hm hC hq1 hσC k)
    (TDeriv.seq hupd
      (TDeriv.seq
        (TDeriv.conseq
          (fun s hs => ⟨hs.1, by
            show s.1.2.snoc ⟨_, _⟩ = s.2.2.snoc ⟨_, _⟩
            rw [hs.2]; exact congrArg (fun x => s.2.2.snoc ⟨_, x⟩) hs.1.2⟩)
          (fun _ _ => le_rfl) (fun _ h => h) (fun _ _ => le_rfl)
          (TDeriv.release (M := PMem) (α := α) (Expr.var (gtV d)) (Expr.var (gtV d))
            (liftP (RGtM N dx d i k)) (fun _ => 1)))
        hcnt))

/-- The loop of `dpsgdTranscript`, by **[While-Prod]**: `T` rounds at `max(Υ, Λ)` each. -/
theorem tderiv_loopRel {α : ℝ} (hα : 1 < α) (hm : MeasOK dx d grad)
    (hC : 0 < (C : ℝ))
    (hq1 : (q : ℝ) < 1) (hσC : (σ * C) ^ 2 ≠ 0) :
    TDeriv (M := PMem) α (RInv N dx d i 0)
      (fun _ => max (mixBudgetR q (C : ℝ) ((σ * C) ^ 2) α) (mixFlipBudgetE q (C : ℝ) ((σ * C) ^ 2) α) ^ T)
      (Cmd.while (guardE T) (bodyRel N dx d grad C η σ q hm))
      (Cmd.while (guardE T) (bodyRel N dx d grad C η σ q hm))
      (RInv N dx d i T) (fun _ => 1) := by
  set Υ := max (mixBudgetR q (C : ℝ) ((σ * C) ^ 2) α) (mixFlipBudgetE q (C : ℝ) ((σ * C) ^ 2) α) with hΥ
  have hΥ0 : Υ ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one
    ((one_le_mixBudgetR hα hσC hq1.le _).trans (le_max_left _ _)))
  have hΥt : Υ ≠ ⊤ := by
    rw [hΥ]
    refine ne_of_lt (max_lt ?_ (lt_top_iff_ne_top.2 (mixFlipBudgetE_ne_top hα hq1 hσC _)))
    exact lt_top_iff_ne_top.2 (mixBudgetR_ne_top hα _ _ hσC hq1.le)
  have h := tderiv_while_prod (α := α) (e := guardE T) T (RInv N dx d i)
    (fun _ => Υ) (fun _ => hΥ0) (fun _ => hΥt)
    (fun k _ => tderiv_bodyRel N dx d grad C η σ q i hα hm hC
      hq1 hσC k)
    (fun k s hs hk => by
      have e1 : cntN s.1.1 = k := hs.1.2.2.2
      have e12 : cntN s.1.1 = cntN s.2.1 := hs.1.2.2.1
      constructor <;> rw [esem_guardE, decide_eq_true_iff]
      · show cntN s.1.1 < T
        omega
      · show cntN s.2.1 < T
        omega)
    (fun s hs => by
      have e1 : cntN s.1.1 = T := hs.1.2.2.2
      have e12 : cntN s.1.1 = cntN s.2.1 := hs.1.2.2.1
      constructor <;> rw [esem_guardE, decide_eq_false_iff_not]
      · show ¬ (cntN s.1.1 < T)
        omega
      · show ¬ (cntN s.2.1 < T)
        omega)
  refine TDeriv.conseq (fun _ h => h) (fun _ _ => le_of_eq ?_) (fun _ h => h)
    (fun _ _ => le_rfl) h
  rw [Finset.prod_const, Finset.card_range]

lemma RInv_initFR (θ₀ : EuclideanSpace ℝ (Fin d)) (s : St PMem × St PMem)
    (hadj : AdjAtSym (recBotN N dx) i (getDS N dx s.1.1) (getDS N dx s.2.1)) (htau : s.1.2 = s.2.2) :
    RInv N dx d i 0 (initFR d θ₀ s.1, initFR d θ₀ s.2) := by
  have hD : ∀ t : St PMem, getDS N dx (initFR d θ₀ t).1 = getDS N dx t.1 := fun t => by
    simp only [initFR]; rw [getDS_set_cnt, getDS_set_th]
  have hth : ∀ t : St PMem, getTh d (initFR d θ₀ t).1 = θ₀ := fun t => by
    simp only [initFR]; rw [getTh_set_cnt]; unfold getTh
    have hn : (thV d).name = "th" := rfl
    rw [hn, PMem.get_set_eq]
  have hcn : ∀ t : St PMem, getCnt (initFR d θ₀ t).1 = 0 := fun t => by
    simp only [initFR]; unfold getCnt; rw [PMem.get_set_eq]
  refine ⟨⟨?_, ?_, ?_, hcn s.1⟩, htau⟩
  · show AdjAtSym (recBotN N dx) i (getDS N dx (initFR d θ₀ s.1).1) (getDS N dx (initFR d θ₀ s.2).1)
    rw [hD, hD]; exact hadj
  · show getTh d (initFR d θ₀ s.1).1 = getTh d (initFR d θ₀ s.2).1
    rw [hth, hth]
  · show getCnt (initFR d θ₀ s.1).1 = getCnt (initFR d θ₀ s.2).1
    rw [hcn, hcn]

/-- **The transcript derivation (§5.1.1)**: adjacent datasets and equal transcripts to
    equal transcripts, at budget `max(Υ_α, Λ_α)^T`. -/
theorem dpsgdTranscript_deriv {α : ℝ} (hα : 1 < α) (θ₀ : EuclideanSpace ℝ (Fin d))
    (hm : MeasOK dx d grad)
    (hC : 0 < (C : ℝ))
    (hq1 : (q : ℝ) < 1) (hσC : (σ * C) ^ 2 ≠ 0) :
    TDeriv (M := PMem) α
      (fun s => AdjAtSym (recBotN N dx) i (getDS N dx s.1.1) (getDS N dx s.2.1) ∧ s.1.2 = s.2.2)
      (fun _ => max (mixBudgetR q (C : ℝ) ((σ * C) ^ 2) α) (mixFlipBudgetE q (C : ℝ) ((σ * C) ^ 2) α) ^ T)
      (dpsgdTranscript N dx d T grad C η σ q hm θ₀)
      (dpsgdTranscript N dx d T grad C η σ q hm θ₀)
      (fun s => s.1.2 = s.2.2) (fun _ => 1) := by
  set Υ := max (mixBudgetR q (C : ℝ) ((σ * C) ^ 2) α) (mixFlipBudgetE q (C : ℝ) ((σ * C) ^ 2) α) with hΥ
  have hinit : TDeriv (M := PMem) α
      (fun s => AdjAtSym (recBotN N dx) i (getDS N dx s.1.1) (getDS N dx s.2.1) ∧ s.1.2 = s.2.2) (fun _ => Υ ^ T)
      (Cmd.seq (Cmd.assign (thV d) (Expr.cst θ₀)) (Cmd.assign cnt (Expr.cst (0 : ℕ))))
      (Cmd.seq (Cmd.assign (thV d) (Expr.cst θ₀)) (Cmd.assign cnt (Expr.cst (0 : ℕ))))
      (RInv N dx d i 0) (fun _ => Υ ^ T) :=
    TDeriv.conseq (fun s hs => RInv_initFR N dx d i θ₀ s hs.1 hs.2) (fun _ _ => le_rfl)
      (fun _ h => h) (fun _ _ => le_rfl)
      (tderiv_initR d θ₀ (RInv N dx d i 0) (fun _ => Υ ^ T))
  have hloop := tderiv_loopRel N dx d T grad C η σ q i hα hm hC
    hq1 hσC
  exact TDeriv.conseq (fun _ h => h) (fun _ _ => le_rfl) (fun s h => h.2) (fun _ _ => le_rfl)
    (TDeriv.seq hinit hloop)

/-- **The transcript bound**: the Hellinger integral of the two transcript laws is at most
    `Υ_α^T`, by `TDeriv.sound` and `rrhl_tr_hellingerIntegral_le`. -/
theorem dpsgdTranscript_Hellinger {α : ℝ} (hα : 1 < α) (θ₀ : EuclideanSpace ℝ (Fin d))
    (hm : MeasOK dx d grad)
    (hC : 0 < (C : ℝ))
    (hq1 : (q : ℝ) < 1) (hσC : (σ * C) ^ 2 ≠ 0)
    (m₁ m₂ : PMem.heap) (hadj : AdjAtSym (recBotN N dx) i (getDS N dx m₁) (getDS N dx m₂)) :
    hellingerIntegral α
      ((osem (dpsgdTranscript N dx d T grad C η σ q hm θ₀) m₁).map Prod.snd)
      ((osem (dpsgdTranscript N dx d T grad C η σ q hm θ₀) m₂).map Prod.snd)
      ≤ mixBudgetR q (C : ℝ) ((σ * C) ^ 2) α ^ T := by
  have h := rrhl_tr_hellingerIntegral_le hα
    ((dpsgdTranscript_deriv N dx d T grad C η σ q i hα θ₀ hm hC hq1
      hσC).sound hα)
    ((m₁, Tr.nil), (m₂, Tr.nil)) ⟨hadj, rfl⟩
  rwa [max_mixBudgetR_mixFlipBudgetE hα hq1.le hσC] at h

end Transcript

end DPSGDPaper
