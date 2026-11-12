import Xhl.Examples.DPSGD.Shared.DerivLeaves

/-!
# The burning round of the last-iterate study (§5.1.3, Appendix D.2)

A burning round costs nothing and is derived on the block as written, without [Equiv]:

* `tderiv_poissonSample_sync` — the Poisson loop, each coin coupled to itself by [Samp]
  at budget `1`, so both runs draw the same batch;
* `tderiv_prefixLI_burn` — the block body: the noise draw is [Samp-Gap] at the gap
  `g⟨1⟩ − g⟨2⟩` between the two means, which leaves no residual, so the cost is `1`;
* `tderiv_blockLoc_of_prefix` — the block, by [Local].
-/

open MeasureTheory ProbabilityTheory Continuous
open scoped NNReal ENNReal

namespace DPSGDPaper

/-! ## The Poisson sub-loop, synchronized -/

section PoissonSync

variable (N : ℕ) (q : ℝ≥0)

/-- The Poisson loop's invariant: the caller's frame, equal batches, equal indices `l`. -/
def PoisInv (A : St PMem × St PMem → Prop) (l : ℕ) (st : St PMem × St PMem) : Prop :=
  A st ∧ getBatch N st.1.1 = getBatch N st.2.1 ∧ getJv st.1.1 = l ∧ getJv st.2.1 = l

variable (A : St PMem × St PMem → Prop)

/-- The frame is closed under a write to the batch. -/
abbrev FrameB : Prop :=
  ∀ (st : St PMem × St PMem) (w : Finset (Fin (N + 1)) × Finset (Fin (N + 1))),
    A st → A ((PMem.set st.1.1 (.finset (N + 1)) (bchV N).name w.1, st.1.2),
              (PMem.set st.2.1 (.finset (N + 1)) (bchV N).name w.2, st.2.2))

/-- The frame is closed under a write to the coin. -/
abbrev FrameC : Prop :=
  ∀ (st : St PMem × St PMem) (w : Bool × Bool),
    A st → A ((PMem.set st.1.1 .bool bv.name w.1, st.1.2),
              (PMem.set st.2.1 .bool bv.name w.2, st.2.2))

/-- The frame is closed under a write to the index. -/
abbrev FrameJ : Prop :=
  ∀ (st : St PMem × St PMem) (w : ℕ × ℕ),
    A st → A ((PMem.set st.1.1 .nat jv.name w.1, st.1.2),
              (PMem.set st.2.1 .nat jv.name w.2, st.2.2))

/-- One iteration of the Poisson loop at budget `1`: **[Samp]** on the coin, **[If]**,
    **[Assn]**. -/
theorem tderiv_poissonLoopBody_sync {α : ℝ} (hα : 1 < α)
    (hAb : FrameB N A) (hAc : FrameC A) (hAj : FrameJ A) (l : ℕ) :
    TDeriv (M := PMem) α (PoisInv N A l) (fun _ => 1)
      (poissonLoopBody N q) (poissonLoopBody N q) (PoisInv N A (l + 1)) (fun _ => 1) := by
  refine TDeriv.seq (Q := PoisInv N A l) (ψ := fun _ => 1)
    (TDeriv.seq (Q := fun st => PoisInv N A l st ∧ getBv st.1.1 = getBv st.2.1)
      (ψ := fun _ => 1) ?_ ?_) ?_
  -- [Samp] on the coin
  · refine TDeriv.rnd (M := PMem) hα bv bv _ _ _
      (fun st => PoisInv N A l st ∧ getBv st.1.1 = getBv st.2.1) (fun _ => 1) (fun _ => 1)
      (fun st hst => Filter.Eventually.of_forall fun w => ?_) (fun st hst => ?_)
    · refine ⟨⟨hAc st (w, w) hst.1, ?_, ?_, ?_⟩, ?_⟩
      · simpa [updPair, getBatch, bchV, bv, get_set_other] using hst.2.1
      · simpa [updPair, getJv, bv, get_set_other] using hst.2.2.1
      · simpa [updPair, getJv, bv, get_set_other] using hst.2.2.2
      · simp [updPair, getBv, PMem.get_set_eq]
    · rw [bernoulliKernel_apply, bernoulliKernel_apply, weightedHellingerIntegral_one, hellingerIntegral_self_prob]
  -- [If] at the synchronized coin
  · refine TDeriv.if_ (fun st hst => ?_) ?_ ?_
    · show getBv st.1.1 = getBv st.2.1
      exact hst.2
    · refine TDeriv.conseq (fun st hst => ?_) (fun _ _ => le_rfl) (fun _ h => h)
        (fun _ _ => le_rfl)
        (TDeriv.assign (M := PMem) (α := α) (bchV N) (insertJE N) (bchV N) (insertJE N)
          (PoisInv N A l) (fun _ => 1))
      refine ⟨hAb st (insertIdx N (getJv st.1.1) (getBatch N st.1.1),
        insertIdx N (getJv st.2.1) (getBatch N st.2.1)) hst.1.1.1, ?_, ?_, ?_⟩
      · have hB : PMem.get st.1.1 (Ty.finset (N + 1)) "B"
            = PMem.get st.2.1 (Ty.finset (N + 1)) "B" := hst.1.1.2.1
        simp only [getBatch, bchV, PMem.get_set_eq, esem_insertJE, hB,
          hst.1.1.2.2.1, hst.1.1.2.2.2]
      · simpa [getJv, bchV, get_set_other] using hst.1.1.2.2.1
      · simpa [getJv, bchV, get_set_other] using hst.1.1.2.2.2
    · exact TDeriv.conseq (fun _ hst => hst.1.1) (fun _ _ => le_rfl) (fun _ h => h)
        (fun _ _ => le_rfl) (TDeriv.skip (PoisInv N A l) (fun _ => 1))
  -- [Assn] on the index
  · refine TDeriv.conseq (fun st hst => ?_) (fun _ _ => le_rfl) (fun _ h => h)
      (fun _ _ => le_rfl)
      (TDeriv.assign (M := PMem) (α := α) jv (incW jv)
        jv (incW jv) (PoisInv N A (l + 1))
        (fun _ => 1))
    refine ⟨hAj st (getJv st.1.1 + 1, getJv st.2.1 + 1) hst.1, ?_, ?_, ?_⟩
    · simpa [getBatch, bchV, jv, get_set_other] using hst.2.1
    · show getJv st.1.1 + 1 = l + 1
      rw [hst.2.2.1]
    · show getJv st.2.1 + 1 = l + 1
      rw [hst.2.2.2]

/-- The Poisson loop at budget `1`, ending in equal batches (by **[While-Prod]**). -/
theorem tderiv_poissonSample_sync {α : ℝ} (hα : 1 < α)
    (hAb : FrameB N A) (hAc : FrameC A) (hAj : FrameJ A) :
    TDeriv (M := PMem) α A (fun _ => 1) (poissonSample N q) (poissonSample N q)
      (fun st => A st ∧ getBatch N st.1.1 = getBatch N st.2.1) (fun _ => 1) := by
  have hloop : TDeriv (M := PMem) α (PoisInv N A 0) (fun _ => 1)
      (Cmd.while (poissonGuard N) (poissonLoopBody N q))
      (Cmd.while (poissonGuard N) (poissonLoopBody N q)) (PoisInv N A (N + 1))
      (fun _ => 1) := by
    have h := tderiv_while_prod (M := PMem) (α := α) (e := poissonGuard N)
      (c := poissonLoopBody N q) (N + 1) (PoisInv N A)
      (fun _ => 1) (fun _ => one_ne_zero) (fun _ => ENNReal.one_ne_top)
      (fun l _ => tderiv_poissonLoopBody_sync N q A hα hAb hAc hAj l)
      (fun l st hst hl => ⟨by show decide (getJv st.1.1 < N + 1) = true
                              rw [hst.2.2.1]; exact decide_eq_true hl,
                           by show decide (getJv st.2.1 < N + 1) = true
                              rw [hst.2.2.2]; exact decide_eq_true hl⟩)
      (fun st hst => ⟨by show decide (getJv st.1.1 < N + 1) = false
                         rw [hst.2.2.1]; simp,
                      by show decide (getJv st.2.1 < N + 1) = false
                         rw [hst.2.2.2]; simp⟩)
    simpa using h
  rw [poissonSample_eq]
  refine TDeriv.seq (Q := PoisInv N A 0) (ψ := fun _ => 1) ?_
    (TDeriv.conseq (fun _ h => h) (fun _ _ => le_rfl) (fun _ h => ⟨h.1, h.2.1⟩)
      (fun _ _ => le_rfl) hloop)
  refine TDeriv.seq (Q := fun st => A st ∧ getBatch N st.1.1 = getBatch N st.2.1)
    (ψ := fun _ => 1) ?_ ?_
  · refine TDeriv.conseq (fun st hst => ?_) (fun _ _ => le_rfl) (fun _ h => h)
      (fun _ _ => le_rfl)
      (TDeriv.assign (M := PMem) (α := α) (bchV N) (Expr.cst ∅) (bchV N) (Expr.cst ∅)
        (fun st => A st ∧ getBatch N st.1.1 = getBatch N st.2.1) (fun _ => 1))
    exact ⟨hAb st (∅, ∅) hst, by simp only [getBatch, bchV, PMem.get_set_eq]; rfl⟩
  · refine TDeriv.conseq (fun st hst => ?_) (fun _ _ => le_rfl) (fun _ h => h)
      (fun _ _ => le_rfl)
      (TDeriv.assign (M := PMem) (α := α) jv (Expr.cst 0) jv (Expr.cst 0)
        (PoisInv N A 0) (fun _ => 1))
    refine ⟨hAj st (0, 0) hst.1, ?_, ?_, ?_⟩
    · simpa [getBatch, bchV, jv, get_set_other] using hst.2
    · simp only [getJv, PMem.get_set_eq]; rfl
    · simp only [getJv, PMem.get_set_eq]; rfl

end PoissonSync


/-! ## The block body of a burning round -/

section BurnLeaf

variable (N dx d : ℕ)
  (grad : EuclideanSpace ℝ (Fin dx) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
  (C : ℝ≥0)
  (q : ℝ≥0) (i : Fin (N + 1))

@[simp] lemma getCnt_set_bch (x : PMem.heap) (B : Finset (Fin (N + 1))) :
    getCnt (PMem.set x (.finset (N + 1)) (bchV N).name B) = getCnt x :=
  PMem.get_set_ne _ _ _ _ _ _ (Or.inl (fun h => Ty.noConfusion h))

@[simp] lemma getCnt_set_gV (x : PMem.heap) (w : EuclideanSpace ℝ (Fin d)) :
    getCnt (PMem.set x (.vec d) (gV d).name w) = getCnt x :=
  PMem.get_set_ne _ _ _ _ _ _ (Or.inl (fun h => Ty.noConfusion h))

@[simp] lemma getCnt_set_bv (x : PMem.heap) (b : Bool) :
    getCnt (PMem.set x .bool bv.name b) = getCnt x :=
  PMem.get_set_ne _ _ _ _ _ _ (Or.inr (show bv.name ≠ cnt.name by
    show ("bv" : String) ≠ "cnt"; decide))

@[simp] lemma getCnt_set_jv (x : PMem.heap) (j : ℕ) :
    getCnt (PMem.set x .nat jv.name j) = getCnt x :=
  PMem.get_set_ne _ _ _ _ _ _ (Or.inr (show jv.name ≠ cnt.name by
    show ("jv" : String) ≠ "cnt"; decide))

/-- `DInv` survives a write to any slot other than the dataset and the model. -/
lemma DInv_set {z : ℝ} {t : Ty} (n : String)
    (hD : n ≠ (dsV N dx).name) (hth : n ≠ (thV d).name) (st : St PMem × St PMem)
    (w₁ w₂ : t.interp) (h : DInv N dx d i z st) :
    DInv N dx d i z
      ((PMem.set st.1.1 t n w₁, st.1.2), (PMem.set st.2.1 t n w₂, st.2.2)) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, h3⟩
  · show AdjAtSym (recBotN N dx) i (PMem.get (PMem.set st.1.1 t n w₁) (.prod (.vec ((N + 1) * dx)) (.finset (N + 1))) (dsV N dx).name)
      (PMem.get (PMem.set st.2.1 t n w₂) (.prod (.vec ((N + 1) * dx)) (.finset (N + 1))) (dsV N dx).name)
    rwa [get_set_other (M := PMem) _ _ hD, get_set_other (M := PMem) _ _ hD]
  · show ‖PMem.get (PMem.set st.1.1 t n w₁) (.vec d) (thV d).name
      - PMem.get (PMem.set st.2.1 t n w₂) (.vec d) (thV d).name‖ ≤ z
    rwa [get_set_other (M := PMem) _ _ hth, get_set_other (M := PMem) _ _ hth]

/-- After the assignment of line 6, `g` holds the clipped batch sum. -/
lemma getG_assign_batchSum (hm : MeasOK dx d grad) (m : PMem.heap) :
    getG d (PMem.set m (.vec d) (gV d).name (esem (batchSumPaperE N dx d grad C hm) m))
      = cbs N dx d grad C
          (PMem.set m (.vec d) (gV d).name (esem (batchSumPaperE N dx d grad C hm) m))
          (getBatch N (PMem.set m (.vec d) (gV d).name
            (esem (batchSumPaperE N dx d grad C hm) m))) := by
  have hD : getR N dx (PMem.set m (.vec d) (gV d).name
      (esem (batchSumPaperE N dx d grad C hm) m)) = getR N dx m := by
    exact getR_set N dx m (t := .vec d) _ _ (Or.inl (fun h => Ty.noConfusion h))
  have hth : getTh d (PMem.set m (.vec d) (gV d).name
      (esem (batchSumPaperE N dx d grad C hm) m)) = getTh d m := by
    unfold getTh
    rw [get_set_other (M := PMem) (a := (gV d).name) (y := "th") _ _ (by show ("g" : String) ≠ "th"; decide)]
  have hB : getBatch N (PMem.set m (.vec d) (gV d).name
      (esem (batchSumPaperE N dx d grad C hm) m)) = getBatch N m := by
    unfold getBatch
    rw [get_set_other (M := PMem) (a := (gV d).name) (y := "B") _ _ (by show ("g" : String) ≠ "B"; decide)]
  unfold getG cbs
  rw [hD, hth, hB]
  exact PMem.get_set_eq _ _ _ _

/-- The invariant before the noise draw: `DInv`, the caller's frame, equal batches, and
    `g` holding each side's clipped batch sum. -/
def MidInv (A : St PMem × St PMem → Prop) (z : ℝ) (st : St PMem × St PMem) : Prop :=
  (DInv N dx d i z st ∧ A st) ∧ getBatch N st.1.1 = getBatch N st.2.1 ∧
    getG d st.1.1 = cbs N dx d grad C st.1.1 (getBatch N st.1.1) ∧
    getG d st.2.1 = cbs N dx d grad C st.2.1 (getBatch N st.2.1)

/-- **The block body of a burning round, at budget `1`**: the synchronized Poisson loop,
    **[Assn]** for the clipped sum, and **[Samp-Gap]** at the gap between the two means. -/
theorem tderiv_prefixLI_burn {α : ℝ} (hα : 1 < α) (v : ℝ≥0) (hm : MeasOK dx d grad)
    {γ z zc z' : ℝ} (hz' : zc + |γ| * C ≤ z')
    (hcontr : ∀ x y : PMem.heap, AdjAtSym (recBotN N dx) i (getDS N dx x) (getDS N dx y) →
      ‖getTh d x - getTh d y‖ ≤ z → ∀ B : Finset (Fin (N + 1)), i ∉ B →
        ‖(getTh d x - γ • cbs N dx d grad C x B)
          - (getTh d y - γ • cbs N dx d grad C y B)‖ ≤ zc)
    (A : St PMem × St PMem → Prop)
    (hAb : FrameB N A) (hAc : FrameC A) (hAj : FrameJ A)
    (hAg : ∀ (st : St PMem × St PMem)
        (w : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)),
      A st → A ((PMem.set st.1.1 (.vec d) (gV d).name w.1, st.1.2),
                (PMem.set st.2.1 (.vec d) (gV d).name w.2, st.2.2)))
    (hAw : ∀ (st : St PMem × St PMem)
        (w : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)),
      A st → A ((PMem.set st.1.1 (.vec d) (gtV d).name w.1, st.1.2),
                (PMem.set st.2.1 (.vec d) (gtV d).name w.2, st.2.2))) :
    TDeriv (M := PMem) α (fun st => DInv N dx d i z st ∧ A st) (fun _ => 1)
      (prefixLI N dx d grad C v q hm) (prefixLI N dx d grad C v q hm)
      (fun st => DPost N dx d i γ z' st ∧ A st) (fun _ => 1) := by
  have hBb : FrameB N (fun st => DInv N dx d i z st ∧ A st) := fun st w h =>
    ⟨DInv_set N dx d i (bchV N).name (by show ("B" : String) ≠ "D"; decide)
      (by show ("B" : String) ≠ "th"; decide) st w.1 w.2 h.1, hAb st w h.2⟩
  have hBc : FrameC (fun st => DInv N dx d i z st ∧ A st) := fun st w h =>
    ⟨DInv_set N dx d i bv.name (by show ("bv" : String) ≠ "D"; decide)
      (by show ("bv" : String) ≠ "th"; decide) st w.1 w.2 h.1, hAc st w h.2⟩
  have hBj : FrameJ (fun st => DInv N dx d i z st ∧ A st) := fun st w h =>
    ⟨DInv_set N dx d i jv.name (by show ("jv" : String) ≠ "D"; decide)
      (by show ("jv" : String) ≠ "th"; decide) st w.1 w.2 h.1, hAj st w h.2⟩
  refine TDeriv.seq (Q := MidInv N dx d grad C i A z) (ψ := fun _ => 1)
    (TDeriv.seq
      (Q := fun st => (DInv N dx d i z st ∧ A st) ∧
        getBatch N st.1.1 = getBatch N st.2.1) (ψ := fun _ => 1)
      (tderiv_poissonSample_sync N q _ hα hBb hBc hBj) ?_) ?_
  -- [Assn] on the clipped sum
  · refine TDeriv.conseq (fun st hst => ?_) (fun _ _ => le_rfl) (fun _ h => h)
      (fun _ _ => le_rfl)
      (TDeriv.assign (M := PMem) (α := α) (gV d) (batchSumPaperE N dx d grad C hm)
        (gV d) (batchSumPaperE N dx d grad C hm)
        (MidInv N dx d grad C i A z) (fun _ => 1))
    refine ⟨⟨DInv_set N dx d i (gV d).name (by show ("g" : String) ≠ "D"; decide)
      (by show ("g" : String) ≠ "th"; decide) st _ _ hst.1.1,
      hAg st (esem (batchSumPaperE N dx d grad C hm) st.1.1,
        esem (batchSumPaperE N dx d grad C hm) st.2.1) hst.1.2⟩, ?_, ?_, ?_⟩
    · simpa [getBatch, bchV, gV, get_set_other] using hst.2
    · exact getG_assign_batchSum N dx d grad C hm st.1.1
    · exact getG_assign_batchSum N dx d grad C hm st.2.1
  -- [Samp-Gap] on the noise: the gap is the difference of the two means, so nothing is
  -- left to charge
  · refine TDeriv.rndGap (M := PMem) hα (gtV d) (gtV d) _ _
      (fun st => getG d st.1.1 - getG d st.2.1) (MidInv N dx d grad C i A z)
      (fun st => DPost N dx d i γ z' st ∧ A st) (fun _ => 1) (fun _ => 1)
      (fun st hst => Filter.Eventually.of_forall fun u => ?_) (fun st hst => ?_)
    · have hadj : AdjAtSym (recBotN N dx) i (getDS N dx st.1.1) (getDS N dx st.2.1) := hst.1.1.1
      have hB : getBatch N st.1.1 = getBatch N st.2.1 := hst.2.1
      have hγC : (0 : ℝ) ≤ |γ| * C := mul_nonneg (abs_nonneg γ) C.2
      have hbase := hcontr st.1.1 st.2.1 hadj hst.1.1.2.1 ((getBatch N st.1.1).erase i)
        (Finset.notMem_erase i _)
      unfold cbs at hbase
      have hnorm : ‖(getTh d st.1.1 - γ • getG d st.1.1)
          - (getTh d st.2.1 - γ • getG d st.2.1)‖ ≤ z' := by
        rw [hst.2.2.1, hst.2.2.2, ← hB]
        unfold cbs
        by_cases h0 : i ∈ getBatch N st.1.1
        · have hins : insert i (getBatch N st.1.1) = getBatch N st.1.1 :=
            Finset.insert_eq_self.mpr h0
          have hadjR : AdjAtSym (getR N dx) i st.1.1 st.2.1 := (adjAtSym_recBotN_iff N dx).1 hadj
          rcases hadjR with hA | hA
          · -- the *right* dataset misses the record, so the right sum collapses to the batch
            -- with `i` erased and the residual term, bounded by the clipping constant, sits
            -- on the left
            have hcol := clippedBatchSumD_insert_eq_erase_of_adj N dx d grad C i
              hA (getTh d st.2.1) (getBatch N st.1.1)
            have hres := norm_clippedBatchSumD_insert_sub_erase_le N dx d grad C i
              (getR N dx st.1.1) (getTh d st.1.1) (getBatch N st.1.1)
            rw [hins] at hcol hres
            rw [hcol]
            have hsplit : (getTh d st.1.1 - γ • clippedBatchSumD (N := N) grad C
                    (getBatch N st.1.1) (getR N dx st.1.1) (getTh d st.1.1))
                  - (getTh d st.2.1 - γ • clippedBatchSumD (N := N) grad C
                    ((getBatch N st.1.1).erase i) (getR N dx st.2.1) (getTh d st.2.1))
                = ((getTh d st.1.1 - γ • clippedBatchSumD (N := N) grad C
                      ((getBatch N st.1.1).erase i) (getR N dx st.1.1) (getTh d st.1.1))
                    - (getTh d st.2.1 - γ • clippedBatchSumD (N := N) grad C
                      ((getBatch N st.1.1).erase i) (getR N dx st.2.1) (getTh d st.2.1)))
                  - γ • (clippedBatchSumD (N := N) grad C (getBatch N st.1.1)
                        (getR N dx st.1.1) (getTh d st.1.1)
                      - clippedBatchSumD (N := N) grad C ((getBatch N st.1.1).erase i)
                        (getR N dx st.1.1) (getTh d st.1.1)) := by
              rw [smul_sub]; abel
            rw [hsplit]
            refine le_trans (norm_sub_le _ _) (le_trans (add_le_add hbase ?_) hz')
            rw [norm_smul, Real.norm_eq_abs]
            exact mul_le_mul_of_nonneg_left hres (abs_nonneg γ)
          · -- the *left* dataset misses the record, so the left sum collapses to the batch
            -- with `i` erased and the residual term, bounded by the clipping constant, sits
            -- on the right
            have hcol := clippedBatchSumD_insert_eq_erase_of_adj N dx d grad C i
              hA (getTh d st.1.1) (getBatch N st.1.1)
            have hres := norm_clippedBatchSumD_insert_sub_erase_le N dx d grad C i
              (getR N dx st.2.1) (getTh d st.2.1) (getBatch N st.1.1)
            rw [hins] at hcol hres
            rw [hcol]
            have hsplit : (getTh d st.1.1 - γ • clippedBatchSumD (N := N) grad C
                    ((getBatch N st.1.1).erase i) (getR N dx st.1.1) (getTh d st.1.1))
                  - (getTh d st.2.1 - γ • clippedBatchSumD (N := N) grad C
                    (getBatch N st.1.1) (getR N dx st.2.1) (getTh d st.2.1))
                = ((getTh d st.1.1 - γ • clippedBatchSumD (N := N) grad C
                      ((getBatch N st.1.1).erase i) (getR N dx st.1.1) (getTh d st.1.1))
                    - (getTh d st.2.1 - γ • clippedBatchSumD (N := N) grad C
                      ((getBatch N st.1.1).erase i) (getR N dx st.2.1) (getTh d st.2.1)))
                  + γ • (clippedBatchSumD (N := N) grad C (getBatch N st.1.1)
                        (getR N dx st.2.1) (getTh d st.2.1)
                      - clippedBatchSumD (N := N) grad C ((getBatch N st.1.1).erase i)
                        (getR N dx st.2.1) (getTh d st.2.1)) := by
              rw [smul_sub]; abel
            rw [hsplit]
            refine le_trans (norm_add_le _ _) (le_trans (add_le_add hbase ?_) hz')
            rw [norm_smul, Real.norm_eq_abs]
            exact mul_le_mul_of_nonneg_left hres (abs_nonneg γ)
        · rw [Finset.erase_eq_of_notMem h0] at hbase
          exact le_trans hbase (le_trans (le_add_of_nonneg_right hγC) hz')
      refine ⟨⟨?_, ?_, hst.1.1.2.2⟩, hAw st (u, u - (getG d st.1.1 - getG d st.2.1)) hst.1.2⟩
      · have he : (getTh d st.1.1 - γ • u)
            - (getTh d st.2.1 - γ • (u - (getG d st.1.1 - getG d st.2.1)))
            = (getTh d st.1.1 - γ • getG d st.1.1)
              - (getTh d st.2.1 - γ • getG d st.2.1) := by
          simp only [smul_sub]; abel
        have hb := he ▸ hnorm
        simpa [updPair, getTh, getGt, thV, gtV, get_set_other, PMem.get_set_eq] using hb
      · simpa [updPair, dsV, gtV, get_set_other, PMem.get_set_eq] using hst.1.1.1
    · have hfin : IsFiniteMeasure (((gaussKernelE (M := PMem) (getG d) (measurable_getG d) v)
          st.2.1).map (fun w => w + (getG d st.1.1 - getG d st.2.1))) :=
        Measure.isFiniteMeasure_map _ _
      rw [weightedHellingerIntegral_one, gaussKernelE_apply, gaussKernelE_apply]
      have hmap : ((gaussE (getG d st.2.1) v).map
            (fun w => w + (getG d st.1.1 - getG d st.2.1)))
          = gaussE (getG d st.1.1) v := by
        rw [gaussE_map_add_const]
        congr 1
        abel
      rw [hmap, hellingerIntegral_self_prob]

/-- **[Local]** on the block: a derivation of `prefixLI` gives one of `blockLoc`. -/
theorem tderiv_blockLoc_of_prefix {α : ℝ} (v : ℝ≥0)
    (hm : MeasOK dx d grad)
    {P Q : St PMem × St PMem → Prop} {Fb : ℝ≥0∞}
    (hP : ∀ s, P s → P (rSt N d s.1, rSt N d s.2))
    (hQ : ∀ s, Q s → Q (rSt N d s.1, rSt N d s.2))
    (hbody : TDeriv (M := PMem) α P (fun _ => Fb)
      (prefixLI N dx d grad C v q hm) (prefixLI N dx d grad C v q hm) Q
      (fun _ => 1)) :
    TDeriv (M := PMem) α P (fun _ => Fb)
      (blockLoc N dx d grad C v q hm) (blockLoc N dx d grad C v q hm) Q
      (fun _ => 1) := by
  have h := TDeriv.locs (α := α) (hidden N d) (P := P) (Q := Q) (φ := fun _ => Fb)
    (ψ := fun _ => 1)
    (TDeriv.conseq (fun _ h => h) (fun _ _ => le_rfl)
      (fun s hs => by rw [postR_hidden]; exact hQ s hs) (fun _ _ => le_rfl) hbody)
  exact TDeriv.conseq (fun s hs => by rw [preR_hidden]; exact hP s hs)
    (fun _ _ => le_rfl) (fun _ h => h) (fun _ _ => le_rfl) h

end BurnLeaf

end DPSGDPaper
