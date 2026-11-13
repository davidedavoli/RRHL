import Xhl.Examples.DPSGD.Shared.Equiv.SplitLeaves
import Xhl.Examples.DPSGD.Shared.DerivLeaves
import Xhl.Examples.DPSGD.LastIterate.BurnRound
import Xhl.Examples.Support.Clip

/-!
# The spending round of the last-iterate study (§5.1.3, Appendix E.2)

* `tderiv_splitSamp` — the split program of `Equiv/SplitLeaves.lean`, derived by
  [Samp] (batch), [Samp] (mixture, at `max(Υ, Λ)`) and [Samp-Gap] (noisy sum, spending `a`
  of the distance at `exp(α(α−1)(a/|γ|)²/(2σ₁))`), for a total of `subDispBudgetSym`;
* `tderiv_blockLoc_of_split` — the round's block, by [Equiv]
  (`cequiv_blockLoc_splitLoc`) and [Local].
-/

open MeasureTheory ProbabilityTheory ENNReal Continuous
open scoped NNReal

namespace DPSGDPaper

section Split

variable (N dx d : ℕ)
  (grad : EuclideanSpace ℝ (Fin dx) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
  (C : ℝ≥0)
  (q : ℝ≥0) (σ1 σ2 : ℝ≥0) (i : Fin (N + 1))

/-- **The split program, derived**: [Samp] on the batch, [Samp] on the mixture at
    `max(Υ_α, Λ_α)`, and [Samp-Gap] on the noisy sum, spending `a` of the distance (through
    `pullv`) at `exp(α(α−1)(a/|γ|)²/(2σ₁))` (`σ₁` a variance); total `subDispBudgetSym`. -/
theorem tderiv_splitSamp {α : ℝ} (hα : 1 < α) (hm : MeasOK dx d grad)
    (hσ1 : σ1 ≠ 0) (hσ2 : σ2 ≠ 0) (hq1 : (q : ℝ) < 1) (hC : 0 < (C : ℝ))
    {γ a z zc z' : ℝ} (hγ : γ ≠ 0) (ha : 0 ≤ a) (hz' : zc - a ≤ z') (hz'0 : 0 ≤ z')
    (hcontr : ∀ x y : PMem.heap, AdjAtSym (recBotN N dx) i (getDS N dx x) (getDS N dx y) →
      ‖getTh d x - getTh d y‖ ≤ z → ∀ B : Finset (Fin (N + 1)), i ∉ B →
        ‖(getTh d x - γ • cbs N dx d grad C x B)
          - (getTh d y - γ • cbs N dx d grad C y B)‖ ≤ zc)
    (A : St PMem × St PMem → Prop)
    (hAb : FrameB N A)
    (hAg : ∀ (st : St PMem × St PMem)
        (w : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)),
      A st → A ((PMem.set st.1.1 (.vec d) (gV d).name w.1, st.1.2),
                (PMem.set st.2.1 (.vec d) (gV d).name w.2, st.2.2)))
    (hAw : ∀ (st : St PMem × St PMem)
        (w : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)),
      A st → A ((PMem.set st.1.1 (.vec d) (gtV d).name w.1, st.1.2),
                (PMem.set st.2.1 (.vec d) (gtV d).name w.2, st.2.2))) :
    TDeriv (M := PMem) α (fun st => DInv N dx d i z st ∧ A st)
      (fun _ => subDispBudgetSym q (C : ℝ) σ1 σ2 γ a α)
      (splitPrefix N dx d grad C q σ1 σ2 i hm)
      (splitPrefix N dx d grad C q σ1 σ2 i hm)
      (fun st => DPost N dx d i γ z' st ∧ A st) (fun _ => 1) := by
  have hq : q ≤ 1 := hq1.le
  have hΛE_ne : subDispBudgetSym q (C : ℝ) σ1 σ2 γ a α ≠ 0 :=
    subDispBudgetSym_ne_zero hα hq1.le hσ2
  have hE_ne : ENNReal.ofReal (Real.exp (α * (α - 1) * (a / |γ|) ^ 2 / (2 * (σ1 : ℝ)))) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  unfold splitPrefix
  refine TDeriv.seq
    (Q := fun st => ((DInv N dx d i z st ∧ A st) ∧ getBatch N st.1.1 = getBatch N st.2.1) ∧
      getG d st.1.1 = getG d st.2.1)
    (ψ := fun _ => ENNReal.ofReal (Real.exp (α * (α - 1) * (a / |γ|) ^ 2 / (2 * (σ1 : ℝ)))))
    (TDeriv.seq
      (Q := fun st => (DInv N dx d i z st ∧ A st) ∧ getBatch N st.1.1 = getBatch N st.2.1)
      (ψ := fun _ => subDispBudgetSym q (C : ℝ) σ1 σ2 γ a α) ?_ ?_) ?_
  -- [Samp] on the batch, at the carried budget
  · refine TDeriv.rnd (M := PMem) hα (bchV N) (bchV N) _ _ _ _ _ _
      (fun st hst => Filter.Eventually.of_forall fun v => ?_) (fun st hst => ?_)
    · refine ⟨⟨DInv_set N dx d i (bchV N).name (by show ("B" : String) ≠ "D"; decide)
        (by show ("B" : String) ≠ "th"; decide) st v v hst.1, hAb st (v, v) hst.2⟩, ?_⟩
      simp [updPair, getBatch, bchV, PMem.get_set_eq]
    · show weightedHellingerIntegral α (fun _ : Finset (Fin (N + 1)) => subDispBudgetSym q (C : ℝ) σ1 σ2 γ a α)
        (νb N q i) (νb N q i) ≤ subDispBudgetSym q (C : ℝ) σ1 σ2 γ a α
      have h1 : (fun _ : Finset (Fin (N + 1)) => subDispBudgetSym q (C : ℝ) σ1 σ2 γ a α)
          = fun v : Finset (Fin (N + 1)) => subDispBudgetSym q (C : ℝ) σ1 σ2 γ a α
              * (fun _ : Finset (Fin (N + 1)) => (1 : ℝ≥0∞)) v := by
        funext v; rw [mul_one]
      rw [h1, weightedHellingerIntegral_const_mul _ hΛE_ne _ measurable_const, weightedHellingerIntegral_one,
        hellingerIntegral_self_prob, mul_one]
  -- [Samp] on the mixture draw, at the subsampling budget
  · refine TDeriv.rnd (M := PMem) hα (gV d) (gV d) _ _ _ _ _ _
      (fun st hst => Filter.Eventually.of_forall fun v => ?_) (fun st hst => ?_)
    · refine ⟨⟨⟨DInv_set N dx d i (gV d).name (by show ("g" : String) ≠ "D"; decide)
        (by show ("g" : String) ≠ "th"; decide) st v v hst.1.1,
        hAg st (v, v) hst.1.2⟩, ?_⟩, ?_⟩
      · simpa [updPair, getBatch, bchV, gV, get_set_other] using hst.2
      · simp [updPair, getG, gV, PMem.get_set_eq]
    · have hadj : AdjAtSym (getR N dx) i st.1.1 st.2.1 := (adjAtSym_recBotN_iff N dx).1
        (show AdjAtSym (recBotN N dx) i (getDS N dx st.1.1) (getDS N dx st.2.1) from hst.1.1.1)
      have hqE : (q : ℝ≥0∞) ≤ 1 := by exact_mod_cast hq
      have hcol : (1 - (q : ℝ≥0∞)) • gaussE (0 : EuclideanSpace ℝ (Fin d)) σ2
          + (q : ℝ≥0∞) • gaussE (0 : EuclideanSpace ℝ (Fin d)) σ2
          = gaussE (0 : EuclideanSpace ℝ (Fin d)) σ2 := by
        rw [← add_smul, tsub_add_cancel_of_le hqE, one_smul]
      have hfin : ∀ u : EuclideanSpace ℝ (Fin d), IsFiniteMeasure
          ((1 - (q : ℝ≥0∞)) • gaussE (0 : EuclideanSpace ℝ (Fin d)) σ2
            + (q : ℝ≥0∞) • gaussE u σ2) := fun u => by
        refine ⟨?_⟩
        simp only [Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
          smul_eq_mul, measure_univ, mul_one]
        exact ENNReal.add_lt_top.2
          ⟨lt_of_le_of_lt tsub_le_self ENNReal.one_lt_top, ENNReal.coe_lt_top⟩
      haveI := hfin (uRec N dx d grad C i st.1.1)
      haveI := hfin (uRec N dx d grad C i st.2.1)
      have h1 : (fun _ : EuclideanSpace ℝ (Fin d) =>
          ENNReal.ofReal (Real.exp (α * (α - 1) * (a / |γ|) ^ 2 / (2 * (σ1 : ℝ)))))
          = fun v : EuclideanSpace ℝ (Fin d) =>
              ENNReal.ofReal (Real.exp (α * (α - 1) * (a / |γ|) ^ 2 / (2 * (σ1 : ℝ))))
                * (fun _ : EuclideanSpace ℝ (Fin d) => (1 : ℝ≥0∞)) v := by
        funext v; rw [mul_one]
      rw [mixZK_apply (hq := hq), mixZK_apply (hq := hq), h1,
        weightedHellingerIntegral_const_mul _ hE_ne _ measurable_const,
        weightedHellingerIntegral_one]
      show ENNReal.ofReal (Real.exp (α * (α - 1) * (a / |γ|) ^ 2 / (2 * (σ1 : ℝ))))
          * hellingerIntegral α
            ((1 - (q : ℝ≥0∞)) • gaussE (0 : EuclideanSpace ℝ (Fin d)) σ2
              + (q : ℝ≥0∞) • gaussE (uRec N dx d grad C i st.1.1) σ2)
            ((1 - (q : ℝ≥0∞)) • gaussE (0 : EuclideanSpace ℝ (Fin d)) σ2
              + (q : ℝ≥0∞) • gaussE (uRec N dx d grad C i st.2.1) σ2)
          ≤ max (mixBudgetR q (C : ℝ) σ2 α) (mixFlipBudgetE q (C : ℝ) σ2 α)
            * ENNReal.ofReal (Real.exp (α * (α - 1) * (a / |γ|) ^ 2 / (2 * (σ1 : ℝ))))
      rw [mul_comm]
      refine mul_le_mul' ?_ le_rfl
      rcases hadj with hA | hA
      · -- the *right* dataset misses the record, so the right mixture collapses to the
        -- plain Gaussian: the forward leaf `Υ`
        have hu2 : uRec N dx d grad C i st.2.1 = 0 := by
          unfold uRec
          rw [hA.2, gradBot_none, clipV_zero]
        rw [hu2, hcol]
        have hb := hellingerIntegral_sgMixtureE_le_mixBudgetR hα (0 : EuclideanSpace ℝ (Fin d))
          (uRec N dx d grad C i st.1.1) σ2 hσ2 q hq (norm_uRec_le N dx d grad C i st.1.1)
        rw [zero_add] at hb
        exact hb.trans (le_max_left _ _)
      · -- the *left* dataset misses the record, so the left mixture collapses: the
        -- reversed leaf `Λ`
        have hu1 : uRec N dx d grad C i st.1.1 = 0 := by
          unfold uRec
          rw [hA.2, gradBot_none, clipV_zero]
        rw [hu1, hcol]
        have hb := hellingerIntegral_flip_sgMixtureE_le_budget_of_le hα
          (0 : EuclideanSpace ℝ (Fin d)) (uRec N dx d grad C i st.2.1) σ2 hσ2 hq1
          (norm_uRec_le N dx d grad C i st.2.1)
        rw [zero_add] at hb
        exact hb.trans (le_max_right _ _)
  -- [Samp-Gap] on the noisy sum: spend `a` of the displacement
  · set δf : St PMem × St PMem → EuclideanSpace ℝ (Fin d) := fun st =>
      (cbs N dx d grad C st.1.1 ((getBatch N st.1.1).erase i)
        - cbs N dx d grad C st.2.1 ((getBatch N st.2.1).erase i))
      + γ⁻¹ • pullv
          ((getTh d st.1.1
              - γ • cbs N dx d grad C st.1.1 ((getBatch N st.1.1).erase i))
            - (getTh d st.2.1
              - γ • cbs N dx d grad C st.2.1 ((getBatch N st.2.1).erase i))) a
      with hδf
    refine TDeriv.rndGap (M := PMem) hα (gtV d) (gtV d) _ _ δf _ _ _ _
      (fun st hst => Filter.Eventually.of_forall fun v => ?_) (fun st hst => ?_)
    · obtain ⟨⟨⟨hDI, hA⟩, hBeq⟩, hGeq⟩ := hst
      have hadj : AdjAtSym (recBotN N dx) i (getDS N dx st.1.1) (getDS N dx st.2.1) := hDI.1
      have hB2 : (getBatch N st.2.1).erase i = (getBatch N st.1.1).erase i := by rw [hBeq]
      have hDd := hcontr st.1.1 st.2.1 hadj hDI.2.1 ((getBatch N st.1.1).erase i)
        (Finset.notMem_erase i _)
      have hnorm : ‖(getTh d st.1.1 - γ • v) - (getTh d st.2.1 - γ • (v - δf st))‖ ≤ z' := by
        have e : (getTh d st.1.1 - γ • v) - (getTh d st.2.1 - γ • (v - δf st))
            = ((getTh d st.1.1
                  - γ • cbs N dx d grad C st.1.1 ((getBatch N st.1.1).erase i))
                - (getTh d st.2.1
                  - γ • cbs N dx d grad C st.2.1 ((getBatch N st.1.1).erase i)))
              - pullv ((getTh d st.1.1
                  - γ • cbs N dx d grad C st.1.1 ((getBatch N st.1.1).erase i))
                - (getTh d st.2.1
                  - γ • cbs N dx d grad C st.2.1 ((getBatch N st.1.1).erase i))) a := by
          rw [hδf]
          simp only [hB2, smul_sub, smul_add, smul_smul, mul_inv_cancel₀ hγ, one_smul]
          abel
        rw [e]
        exact norm_sub_pullv_le ha hDd hz' hz'0
      refine ⟨⟨?_, ?_, hDI.2.2⟩, hAw st (v, v - δf st) hA⟩
      · simpa [updPair, getTh, getGt, thV, gtV, get_set_other, PMem.get_set_eq]
          using hnorm
      · simpa [updPair, dsV, gtV, get_set_other, PMem.get_set_eq] using hDI.1
    · obtain ⟨⟨⟨hDI, _hA⟩, hBeq⟩, hGeq⟩ := hst
      show weightedHellingerIntegral α (fun _ : EuclideanSpace ℝ (Fin d) => (1 : ℝ≥0∞))
          (gaussE (splitCtr N dx d grad C i st.1.1) σ1)
          ((gaussE (splitCtr N dx d grad C i st.2.1) σ1).map (fun w => w + δf st))
          ≤ ENNReal.ofReal (Real.exp (α * (α - 1) * (a / |γ|) ^ 2 / (2 * (σ1 : ℝ))))
      have : IsFiniteMeasure
          ((gaussE (splitCtr N dx d grad C i st.2.1) σ1).map (fun w => w + δf st)) :=
        Measure.isFiniteMeasure_map _ _
      rw [weightedHellingerIntegral_one]
      have hmap : (gaussE (splitCtr N dx d grad C i st.2.1) σ1).map (fun w => w + δf st)
          = gaussE (splitCtr N dx d grad C i st.2.1 + δf st) σ1 := by
        rw [gaussE_map_add_const]
      rw [hmap]
      refine le_trans (gaussE_leaf hα hσ1 _ _) ?_
      have hgap : ‖splitCtr N dx d grad C i st.1.1
          - (splitCtr N dx d grad C i st.2.1 + δf st)‖ ≤ a / |γ| := by
        have e : splitCtr N dx d grad C i st.1.1
            - (splitCtr N dx d grad C i st.2.1 + δf st)
            = -(γ⁻¹ • pullv
                ((getTh d st.1.1
                    - γ • cbs N dx d grad C st.1.1 ((getBatch N st.1.1).erase i))
                  - (getTh d st.2.1
                    - γ • cbs N dx d grad C st.2.1 ((getBatch N st.2.1).erase i))) a) := by
          rw [hδf]
          simp only []
          unfold splitCtr
          rw [hGeq]
          generalize cbs N dx d grad C st.1.1 ((getBatch N st.1.1).erase i) = c1
          generalize cbs N dx d grad C st.2.1 ((getBatch N st.2.1).erase i) = c2
          generalize γ⁻¹ • pullv ((getTh d st.1.1 - γ • c1) - (getTh d st.2.1 - γ • c2)) a = P
          abel
        rw [e, norm_neg, norm_smul, norm_inv, Real.norm_eq_abs, div_eq_inv_mul]
        exact mul_le_mul_of_nonneg_left (norm_pullv_le ha) (inv_nonneg.mpr (abs_nonneg γ))
      refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
      have hσR : (0 : ℝ) < (σ1 : ℝ) := by exact_mod_cast hσ1.bot_lt
      have hα0 : (0 : ℝ) ≤ α * (α - 1) := by nlinarith
      have hsq : ‖splitCtr N dx d grad C i st.1.1
          - (splitCtr N dx d grad C i st.2.1 + δf st)‖ ^ 2 ≤ (a / |γ|) ^ 2 := by
        have h0 : (0 : ℝ) ≤ a / |γ| := div_nonneg ha (abs_nonneg γ)
        nlinarith [norm_nonneg (splitCtr N dx d grad C i st.1.1
          - (splitCtr N dx d grad C i st.2.1 + δf st)), hgap]
      gcongr

/-- **[Equiv] and [Local] for a spending round**: a derivation of the split program gives
    one of the block. -/
theorem tderiv_blockLoc_of_split {α : ℝ} (hm : MeasOK dx d grad) (hq : q ≤ 1)
    {P Q : St PMem × St PMem → Prop} {Fb : ℝ≥0∞}
    (hP : ∀ s, P s → P (rSt N d s.1, rSt N d s.2))
    (hQ : ∀ s, Q s → Q (rSt N d s.1, rSt N d s.2))
    (hsamp : TDeriv (M := PMem) α P (fun _ => Fb)
      (splitPrefix N dx d grad C q σ1 σ2 i hm)
      (splitPrefix N dx d grad C q σ1 σ2 i hm) Q (fun _ => 1)) :
    TDeriv (M := PMem) α P (fun _ => Fb)
      (blockLoc N dx d grad C (σ2 + σ1) q hm) (blockLoc N dx d grad C (σ2 + σ1) q hm)
      Q (fun _ => 1) := by
  refine TDeriv.equiv
    (cequiv_blockLoc_splitLoc N dx d grad C q σ1 σ2 i hm hq (fun _ => True))
    (cequiv_blockLoc_splitLoc N dx d grad C q σ1 σ2 i hm hq (fun _ => True))
    (fun _ _ => ⟨trivial, trivial⟩) ?_
  have h := TDeriv.locs (α := α) (hidden N d)
    (P := P) (Q := Q) (φ := fun _ => Fb) (ψ := fun _ => 1)
    (TDeriv.conseq (fun _ h => h) (fun _ _ => le_rfl)
      (fun s hs => by rw [postR_hidden]; exact hQ s hs) (fun _ _ => le_rfl) hsamp)
  exact TDeriv.conseq (fun s hs => by rw [preR_hidden]; exact hP s hs)
    (fun _ _ => le_rfl) (fun _ h => h) (fun _ _ => le_rfl) h

end Split

end DPSGDPaper
