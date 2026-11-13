import Xhl.Logic.Equiv.CEquiv
import Xhl.Examples.DPSGD.Shared.LocalSupport

/-!
# The DP-SGD sampling block, by the equivalence calculus

`cequiv_blockLoc_fusedLoc`: the block of lines 4–7 of Figure 1 is equivalent to the single
fused sampling `fusedLoc` (§5.1.1), as a `CEquiv` derivation (Appendix C).  The Poisson
loop is unrolled by **[E-Count]** and its `N + 1` iterations are merged into one batch
draw (`poissonBatchKernel`); the clipped sum is then pushed into the Gaussian's mean and
the batch draw merged with the Gaussian (**[E-Merge]**).
-/

open MeasureTheory ProbabilityTheory Continuous Cmd
open scoped NNReal ENNReal

namespace DPSGDPaper

/-- **[E-Count]** on the Poisson loop: `poissonSample` is its two initial stores followed
    by `N + 1` iterations of the body (**[E-Seq-A]** carries `jv = 0` to the loop). -/
theorem cequiv_poissonSample_iterCmd (N : ℕ) (q : ℝ≥0) (R : St PMem → Prop) :
    CEquiv R (poissonSample N q)
      (Cmd.seq (Cmd.seq (Cmd.assign (bchV N) (Expr.cst (∅ : Finset (Fin (N + 1)))))
          (Cmd.assign jv (Expr.cst (0 : ℕ))))
        (iterCmd (poissonLoopBody N q) (N + 1))) := by
  rw [poissonSample_eq]
  refine (CEquiv.seqAssoc).trans (CEquiv.trans ?_ (CEquiv.seqAssoc).symm)
  refine CEquiv.congrSeqDet (bchV N) (Expr.cst (∅ : Finset (Fin (N + 1))))
    (R' := fun _ => True) (fun _ _ => trivial) ?_
  refine CEquiv.congrSeqDet jv (Expr.cst (0 : ℕ))
    (R' := fun s => PMem.get s.1 .nat jv.name + (N + 1) = N + 1) ?_
    (CEquiv.count jv (N + 1) (c := poissonLoopBody N q) ⟨⟨show bv.name ≠ jv.name by decide, show (bchV N).name ≠ jv.name from fun h => by simp [bchV, jv] at h, trivial⟩,
      Or.inl rfl⟩ (N + 1))
  intro s _
  show PMem.get (PMem.set s.1 .nat jv.name 0) .nat jv.name + (N + 1) = N + 1
  rw [PMem.get_set_eq]
  exact Nat.zero_add _

/-! ## Collapsing the iterations

With the coin reset `bv ≔ default` floated next to it (**[E-Frame]**), one iteration
`bv ←$ Bern(q) ; B ≔ (if bv then B ∪ {jv} else B) ; bv ≔ default` is the single draw
`B ←$ batchK N q 1 id` (`CEquiv.drawAssignReset`).  Consecutive iterations are merged by
**[E-Comm]**, **[E-SS]** (along `batchFrom_one_bind`) and **[E-AA]**. -/

/-- The law of deciding `k` further indices from `f jv` on, over the batch in memory. -/
noncomputable def batchK (N : ℕ) (q : ℝ≥0) (k : ℕ) (f : ℕ → ℕ) :
    @ProbabilityTheory.Kernel PMem.heap (Finset (Fin (N + 1))) PMem.heapMeas
      (Ty.measurableSpace (.finset (N + 1))) where
  toFun m := batchFrom N q k (f (getJv m)) (getBatch N m)
  measurable' :=
    (Measurable.of_discrete (f := fun p : ℕ × Finset (Fin (N + 1)) =>
      batchFrom N q k (f p.1) p.2)).comp (measurable_getJv.prodMk (measurable_getBatch N))

instance isMarkov_batchK (N : ℕ) (q : ℝ≥0) (k : ℕ) (f : ℕ → ℕ) :
    IsMarkovKernel (batchK N q k f) :=
  ⟨fun m => isProb_batchFrom N q k (f (getJv m)) (getBatch N m)⟩

/-- One coin at index `j`, then `k` more from `j + 1`, is `k + 1` coins from `j`. -/
lemma batchFrom_one_bind (N : ℕ) (q : ℝ≥0) (k j : ℕ) (S₀ : Finset (Fin (N + 1))) :
    (batchFrom N q 1 j S₀).bind (fun S => batchFrom N q k (j + 1) S)
      = batchFrom N q (k + 1) j S₀ := by
  have hF : Measurable (fun S : Finset (Fin (N + 1)) => batchFrom N q k (j + 1) S) :=
    Measurable.of_discrete
  have hD : Measurable (fun b : Bool => batchFrom N q 0 (j + 1)
      (if b then insert (Fin.ofNat (N + 1) j) S₀ else S₀)) := Measurable.of_discrete
  show ((Continuous.bernoulliMeasure q).bind (fun b => batchFrom N q 0 (j + 1)
      (if b then insert (Fin.ofNat (N + 1) j) S₀ else S₀))).bind
      (fun S => batchFrom N q k (j + 1) S) = _
  rw [Measure.bind_bind hD.aemeasurable hF.aemeasurable]
  show (Continuous.bernoulliMeasure q).bind (fun b =>
      (Measure.dirac (if b then insert (Fin.ofNat (N + 1) j) S₀ else S₀)).bind
        (fun S => batchFrom N q k (j + 1) S)) = _
  refine congrArg _ (funext fun b => ?_)
  rw [Measure.dirac_bind hF]

/-! ### The pieces of one iteration, named -/

/-- The coin draw. -/
noncomputable def coinD (q : ℝ≥0) : Cmd String PMem := Cmd.random bv (bernoulliKernel q)

/-- The batch store, after **[E-Cond-W]** has turned the guarded write into an assignment. -/
noncomputable def batchA (N : ℕ) : Cmd String PMem :=
  Cmd.assign (bchV N) (Expr.ite (Expr.var bv) (insertJE N) (Expr.var (bchV N)))

/-- The reset of the coin. -/
noncomputable def bvZ : Cmd String PMem := Cmd.assign bv (Expr.cst (default : Bool))

/-- The counter jump's expression, `jv + n`; at `n = 1` it is the loop's own `incW jv`. -/
noncomputable def jvAddE (n : ℕ) : Expr PMem .nat :=
  ⟨fun m => getJv m + n,
    (measurable_from_top : Measurable (fun j : ℕ => j + n)).comp measurable_getJv⟩

/-- The counter jump by `n`. -/
noncomputable def jvAdd (n : ℕ) : Cmd String PMem := Cmd.assign jv (jvAddE n)

/-- `n` iterations, collapsed: one reset of the coin, one batch draw, one counter jump. -/
noncomputable def collapsed (N : ℕ) (q : ℝ≥0) (n : ℕ) : Cmd String PMem :=
  Cmd.seq bvZ (Cmd.seq (Cmd.random (bchV N) (batchK N q n id)) (jvAdd n))

/-! ### Slot distinctness, in the form the rules ask for -/

/-- Closes a goal `x.name ≠ y.name` between two concrete slots. -/
macro "vname_ne" : tactic =>
  `(tactic| (simp only [gV, thV, gtV, bchV, dsV, jv, bv, cnt]; decide))

lemma name_bchV_ne_bv (N : ℕ) : (bchV N).name ≠ bv.name := by
  show ("B" : String) ≠ "bv"; decide

lemma name_jv_ne_bv : jv.name ≠ bv.name := by show ("jv" : String) ≠ "bv"; decide

lemma name_jv_ne_bchV (N : ℕ) : jv.name ≠ (bchV N).name := by
  show ("jv" : String) ≠ "B"; decide

/-! ### The frame facts of the three slots, in `get`/`set` form -/

@[simp] lemma getJv_setJv (h : PMem.heap) (v : ℕ) :
    getJv (PMem.set h .nat jv.name v) = v := PMem.get_set_eq .nat h jv.name v

@[simp] lemma getBatch_setB (N : ℕ) (h : PMem.heap) (S : Finset (Fin (N + 1))) :
    getBatch N (PMem.set h (.finset (N + 1)) (bchV N).name S) = S :=
  PMem.get_set_eq (.finset (N + 1)) h (bchV N).name S

@[simp] lemma getJv_setB (N : ℕ) (h : PMem.heap) (S : Finset (Fin (N + 1))) :
    getJv (PMem.set h (.finset (N + 1)) (bchV N).name S) = getJv h :=
  PMem.get_set_ne (.finset (N + 1)) .nat h (bchV N).name jv.name S
    (Or.inr (fun hc => name_jv_ne_bchV N hc.symm))

@[simp] lemma getBatch_setJv (N : ℕ) (h : PMem.heap) (v : ℕ) :
    getBatch N (PMem.set h .nat jv.name v) = getBatch N h :=
  PMem.get_set_ne .nat (.finset (N + 1)) h jv.name (bchV N).name v
    (Or.inr (name_jv_ne_bchV N))

/-- The counter jump ignores the coin. -/
lemma indepY_bv_jvAdd (n : ℕ) : IndepY (M := PMem) bv (jvAdd n) :=
  ⟨name_jv_ne_bv, fun h w => by
    show getJv (PMem.set h .bool bv.name w) + n = getJv h + n
    rw [show getJv (PMem.set h .bool bv.name w) = getJv h from
      PMem.get_set_ne .bool .nat h bv.name jv.name w (Or.inr name_jv_ne_bv.symm)]⟩

/-- **[E-Cond-W]** on the loop body: a draw, a store and a counter jump. -/
lemma cequiv_body_eq (N : ℕ) (q : ℝ≥0) (R : St PMem → Prop) :
    CEquiv R (poissonLoopBody N q) (Cmd.seq (Cmd.seq (coinD q) (batchA N)) (jvAdd 1)) :=
  CEquiv.congrHead (CEquiv.congrTail
    (CEquiv.condAssignExpr (bchV N) (Expr.var bv) (insertJE N)))

/-! ### The collapse of one round -/

/-- **One iteration, collapsed** (`CEquiv.drawAssignReset`). -/
lemma cequiv_round_one (N : ℕ) (q : ℝ≥0) (R : St PMem → Prop) :
    CEquiv R (Cmd.seq (Cmd.seq (coinD q) (batchA N)) bvZ)
      (Cmd.seq bvZ (Cmd.random (bchV N) (batchK N q 1 id))) := by
  refine CEquiv.drawAssignReset bv (bchV N) (name_bchV_ne_bv N) (bernoulliKernel q)
    (fun _ _ => rfl) _ (batchK N q 1 id) (fun h => ?_)
  have hmap : Measurable (fun b : Bool =>
      if b then insert (Fin.ofNat (N + 1) (getJv h)) (getBatch N h) else getBatch N h) :=
    Measurable.of_discrete
  have hfun : (fun v : Bool => esem (Expr.ite (Expr.var bv) (insertJE N) (Expr.var (bchV N)))
        (PMem.set h .bool bv.name v))
      = (fun b : Bool => if b then insert (Fin.ofNat (N + 1) (getJv h)) (getBatch N h)
          else getBatch N h) := by
    funext v
    show (if getBv (PMem.set h .bool bv.name v) = true then
        insertIdx N (getJv (PMem.set h .bool bv.name v))
          (getBatch N (PMem.set h .bool bv.name v))
      else getBatch N (PMem.set h .bool bv.name v)) = _
    rw [show getBv (PMem.set h .bool bv.name v) = v from PMem.get_set_eq .bool h bv.name v,
      show getJv (PMem.set h .bool bv.name v) = getJv h from
        PMem.get_set_ne .bool .nat h bv.name jv.name v (Or.inr name_jv_ne_bv.symm),
      show getBatch N (PMem.set h .bool bv.name v) = getBatch N h from
        PMem.get_set_ne .bool (.finset (N + 1)) h bv.name (bchV N).name v
          (Or.inr (name_bchV_ne_bv N).symm)]
    rfl
  show batchFrom N q 1 (getJv h) (getBatch N h)
    = (bernoulliKernel (M := PMem) q h).map
        (fun v => esem (Expr.ite (Expr.var bv) (insertJE N) (Expr.var (bchV N)))
          (PMem.set h .bool bv.name v))
  rw [hfun, bernoulliKernel_apply]
  show (Continuous.bernoulliMeasure q).bind (fun b => Measure.dirac
      (if b then insert (Fin.ofNat (N + 1) (getJv h)) (getBatch N h) else getBatch N h)) = _
  exact Measure.bind_dirac_eq_map _ hmap

/-! ### Merging the collapsed iterations -/

/-- **[E-Comm]**: the counter jump floats past the batch draw, which then reads one index on. -/
lemma cequiv_swap_jv_batch (N : ℕ) (q : ℝ≥0) (n : ℕ) (R : St PMem → Prop) :
    CEquiv R (Cmd.seq (jvAdd 1) (Cmd.random (bchV N) (batchK N q n id)))
      (Cmd.seq (Cmd.random (bchV N) (batchK N q n (· + 1))) (jvAdd 1)) := by
  refine CEquiv.swap jv (bchV N) (name_jv_ne_bchV N) (jvAddE 1)
    (fun h w => ?_) (batchK N q n id) (batchK N q n (· + 1)) (fun h => ?_)
  · show getJv (PMem.set h (.finset (N + 1)) (bchV N).name w) + 1 = getJv h + 1
    rw [getJv_setB]
  · show batchFrom N q n (getJv h + 1) (getBatch N h)
      = batchFrom N q n (getJv (PMem.set h .nat jv.name (getJv h + 1)))
          (getBatch N (PMem.set h .nat jv.name (getJv h + 1)))
    rw [getJv_setJv, getBatch_setJv]

/-- **[E-SS]**: one coin then `n` more is `n + 1` coins. -/
lemma cequiv_merge_batch (N : ℕ) (q : ℝ≥0) (n : ℕ) (R : St PMem → Prop) :
    CEquiv R (Cmd.seq (Cmd.random (bchV N) (batchK N q 1 id))
        (Cmd.random (bchV N) (batchK N q n (· + 1))))
      (Cmd.random (bchV N) (batchK N q (n + 1) id)) := by
  refine CEquiv.drawComp (bchV N) (batchK N q 1 id) (batchK N q n (· + 1)) (batchK N q (n + 1) id)
    (fun h => ?_)
  show batchFrom N q (n + 1) (getJv h) (getBatch N h)
    = (batchFrom N q 1 (getJv h) (getBatch N h)).bind
        (fun S => batchFrom N q n (getJv (PMem.set h (.finset (N + 1)) (bchV N).name S) + 1)
          (getBatch N (PMem.set h (.finset (N + 1)) (bchV N).name S)))
  simp only [getJv_setB, getBatch_setB]
  exact (batchFrom_one_bind N q n (getJv h) (getBatch N h)).symm

/-- **[E-AA]**: the two counter jumps are one. -/
lemma cequiv_merge_jv (n : ℕ) (R : St PMem → Prop) :
    CEquiv R (Cmd.seq (jvAdd 1) (jvAdd n)) (jvAdd (n + 1)) := by
  refine CEquiv.assignComp jv (jvAddE 1) (jvAddE n) (jvAddE (n + 1)) (fun m => ?_)
  show getJv m + (n + 1) = getJv (PMem.set m .nat jv.name (getJv m + 1)) + n
  rw [getJv_setJv, Nat.add_assoc, Nat.add_comm 1 n]

/-! ### The induction -/

/-- An iteration in front of `n + 1` collapsed iterations is `n + 2` collapsed ones. -/
lemma cequiv_round_step (N : ℕ) (q : ℝ≥0) (n : ℕ) (R : St PMem → Prop) :
    CEquiv R (Cmd.seq (poissonLoopBody N q) (collapsed N q (n + 1)))
      (collapsed N q (n + 1 + 1)) := by
  refine (CEquiv.congrHead (cequiv_body_eq N q R)).trans ?_
  refine (CEquiv.seqAssoc).trans ?_
  -- the coin reset floats next to the coin draw, and the iteration collapses
  refine (CEquiv.congrTail (CEquiv.frameRight bv (indepY_bv_jvAdd 1) default)).trans ?_
  refine (CEquiv.seqAssoc').trans ?_
  refine (CEquiv.congrHead (cequiv_round_one N q R)).trans ?_
  refine (CEquiv.seqAssoc).trans (CEquiv.congrTail ?_)
  -- the counter jump floats past the next draw, then both pairs merge
  refine (CEquiv.congrTail (CEquiv.seqAssoc')).trans ?_
  refine (CEquiv.congrTail (CEquiv.congrHead
    (cequiv_swap_jv_batch N q (n + 1) (fun _ => True)))).trans ?_
  refine (CEquiv.congrTail (CEquiv.seqAssoc)).trans ?_
  refine (CEquiv.congrTail (CEquiv.congrTail (cequiv_merge_jv (n + 1) (fun _ => True)))).trans ?_
  refine (CEquiv.seqAssoc').trans ?_
  exact CEquiv.congrHead (cequiv_merge_batch N q (n + 1) (fun _ => True))

/-- `n + 1` iterations followed by the coin reset are one reset, one batch draw and one
    counter jump. -/
lemma cequiv_iter_collapsed (N : ℕ) (q : ℝ≥0) :
    ∀ (n : ℕ) (R : St PMem → Prop),
      CEquiv R (Cmd.seq (iterCmd (poissonLoopBody N q) (n + 1)) bvZ) (collapsed N q (n + 1))
  | 0, R => by
      show CEquiv R (Cmd.seq (Cmd.seq (poissonLoopBody N q) Cmd.skip) bvZ) _
      refine (CEquiv.congrHead (CEquiv.seqSkip (poissonLoopBody N q))).trans ?_
      refine (CEquiv.congrHead (cequiv_body_eq N q R)).trans ?_
      refine (CEquiv.seqAssoc).trans ?_
      refine (CEquiv.congrTail (CEquiv.assignFrame bv (indepY_bv_jvAdd 1) default).symm).trans ?_
      refine (CEquiv.seqAssoc').trans ?_
      refine (CEquiv.congrHead (cequiv_round_one N q R)).trans ?_
      exact CEquiv.seqAssoc
  | n + 1, R => by
      show CEquiv R (Cmd.seq (Cmd.seq (poissonLoopBody N q)
        (iterCmd (poissonLoopBody N q) (n + 1))) bvZ) _
      refine (CEquiv.seqAssoc).trans ?_
      refine (CEquiv.congrTail (cequiv_iter_collapsed N q n (fun _ => True))).trans ?_
      exact cequiv_round_step N q n R

/-! ## From the collapsed loop to the single batch draw `poissonBatchKernel` -/

/-- The counter, set outright. -/
noncomputable def jvSet (n : ℕ) : Cmd String PMem := Cmd.assign jv (Expr.cst n)

/-- `B ≔ ∅`. -/
noncomputable def bchEmpty (N : ℕ) : Cmd String PMem :=
  Cmd.assign (bchV N) (Expr.cst (∅ : Finset (Fin (N + 1))))

lemma indepY_bv_jvSet (n : ℕ) : IndepY (M := PMem) bv (jvSet n) :=
  ⟨name_jv_ne_bv, fun _ _ => rfl⟩

lemma indepY_bv_bchEmpty (N : ℕ) : IndepY (M := PMem) bv (bchEmpty N) :=
  ⟨name_bchV_ne_bv N, fun _ _ => rfl⟩

/-- **[E-Comm]**: `jv ≔ 0` floats past the batch draw, which then reads the counter at `0`. -/
lemma cequiv_swap_jv0_batch (N : ℕ) (q : ℝ≥0) (R : St PMem → Prop) :
    CEquiv R (Cmd.seq (jvSet 0) (Cmd.random (bchV N) (batchK N q (N + 1) id)))
      (Cmd.seq (Cmd.random (bchV N) (batchK N q (N + 1) (fun _ => 0))) (jvSet 0)) := by
  refine CEquiv.swap jv (bchV N) (name_jv_ne_bchV N) (Expr.cst (0 : ℕ))
    (fun _ _ => rfl) (batchK N q (N + 1) id) (batchK N q (N + 1) (fun _ => 0)) (fun h => ?_)
  show batchFrom N q (N + 1) 0 (getBatch N h)
    = batchFrom N q (N + 1) (getJv (PMem.set h .nat jv.name 0))
        (getBatch N (PMem.set h .nat jv.name 0))
  rw [getJv_setJv, getBatch_setJv]

/-- **[E-AA]**: `jv ≔ 0 ; jv ≔ jv + (N + 1)` is `jv ≔ N + 1`. -/
lemma cequiv_jv0_jvAdd (N : ℕ) (R : St PMem → Prop) :
    CEquiv R (Cmd.seq (jvSet 0) (jvAdd (N + 1))) (jvSet (N + 1)) := by
  refine CEquiv.assignComp jv (Expr.cst (0 : ℕ)) (jvAddE (N + 1)) (Expr.cst (N + 1))
    (fun m => ?_)
  show (N + 1 : ℕ) = getJv (PMem.set m .nat jv.name 0) + (N + 1)
  rw [getJv_setJv, Nat.zero_add]

/-- **[E-AS]**: `B ≔ ∅` is absorbed by the batch draw, giving `poissonBatchKernel`. -/
lemma cequiv_bchEmpty_batch (N : ℕ) (q : ℝ≥0) (R : St PMem → Prop) :
    CEquiv R (Cmd.seq (bchEmpty N) (Cmd.random (bchV N) (batchK N q (N + 1) (fun _ => 0))))
      (Cmd.random (bchV N) (poissonBatchKernel N q)) := by
  refine CEquiv.drawAfterAssign (bchV N) (Expr.cst (∅ : Finset (Fin (N + 1))))
    (batchK N q (N + 1) (fun _ => 0)) (poissonBatchKernel N q) (fun h => ?_)
  show batchFrom N q (N + 1) 0 ∅
    = batchFrom N q (N + 1) 0 (getBatch N (PMem.set h (.finset (N + 1)) (bchV N).name ∅))
  rw [getBatch_setB]

/-- `poissonSample ; bv ≔ default` is the coin reset, one batch draw and one counter store. -/
lemma cequiv_poissonSample_bvZ (N : ℕ) (q : ℝ≥0) (R : St PMem → Prop) :
    CEquiv R (Cmd.seq (poissonSample N q) bvZ)
      (Cmd.seq bvZ (Cmd.seq (Cmd.random (bchV N) (poissonBatchKernel N q)) (jvSet (N + 1)))) := by
  refine (CEquiv.congrHead (cequiv_poissonSample_iterCmd N q R)).trans ?_
  refine (CEquiv.seqAssoc).trans ?_
  refine (CEquiv.congrTail (cequiv_iter_collapsed N q N (fun _ => True))).trans ?_
  refine (CEquiv.seqAssoc).trans ?_
  refine (CEquiv.congrTail (CEquiv.frameRight bv (indepY_bv_jvSet 0) default)).trans ?_
  refine (CEquiv.frameRight bv (indepY_bv_bchEmpty N) default).trans
    (CEquiv.congrTail ?_)
  refine (CEquiv.congrTail (CEquiv.seqAssoc')).trans ?_
  refine (CEquiv.congrTail (CEquiv.congrHead
    (cequiv_swap_jv0_batch N q (fun _ => True)))).trans ?_
  refine (CEquiv.congrTail (CEquiv.seqAssoc)).trans ?_
  refine (CEquiv.congrTail (CEquiv.congrTail (cequiv_jv0_jvAdd N (fun _ => True)))).trans ?_
  refine (CEquiv.seqAssoc').trans ?_
  exact CEquiv.congrHead (cequiv_bchEmpty_batch N q (fun _ => True))

/-- The Poisson loop under the coin's block. -/
lemma cequiv_loc_poissonSample (N : ℕ) (q : ℝ≥0) (R : St PMem → Prop) :
    CEquiv R (Cmd.loc bv (poissonSample N q))
      (Cmd.seq bvZ (Cmd.seq (Cmd.random (bchV N) (poissonBatchKernel N q)) (jvSet (N + 1)))) := by
  refine (CEquiv.locDesugar bv).trans ?_
  refine (CEquiv.congrTail (cequiv_poissonSample_bvZ N q (fun _ => True))).trans ?_
  refine (CEquiv.seqAssoc').trans ?_
  exact CEquiv.congrHead (CEquiv.resetTwice bv)

/-! ## The rest of the block

**[E-Comm]** pushes the clipped batch sum into the Gaussian's mean (giving `noisyG`), the
stores to `g` and `jv` are dead in their blocks, and **[E-Merge]** fuses the batch draw
with `noisyG` into `fusedK`. -/

section Outer

variable (N dx d : ℕ)
  (grad : EuclideanSpace ℝ (Fin dx) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
  (C : ℝ≥0)
  (v : ℝ≥0) (q : ℝ≥0)

/-- The store of the clipped batch sum into `g`. -/
noncomputable def gAssign (hm : MeasOK dx d grad) : Cmd String PMem :=
  Cmd.assign (gV d) (batchSumPaperE N dx d grad C hm)

/-- The Gaussian draw of the program, reading `g`. -/
noncomputable def gtDraw : Cmd String PMem :=
  Cmd.random (gtV d) (gaussKernelE (M := PMem) (getG d) (measurable_getG d) v)

/-! ### Frame facts for the slots `B`, `D`, `th` the noisy draw reads -/

/-- `batchSumPaperE` reads only `B`, `D` and `th`. -/
lemma esem_bsE_frame (hm : MeasOK dx d grad) {t : Ty} (y : String)
    (hB : t ≠ Ty.finset (N + 1) ∨ y ≠ "B")
    (hD : t ≠ Ty.prod (.vec ((N + 1) * dx)) (.finset (N + 1)) ∨ y ≠ "D")
    (hT : t ≠ Ty.vec d ∨ y ≠ "th")
    (h : PMem.heap) (w : t.interp) :
    esem (batchSumPaperE N dx d grad C hm) (PMem.set h t y w)
      = esem (batchSumPaperE N dx d grad C hm) h := by
  show clippedBatchSumD (N := N) grad C
      (PMem.get (PMem.set h t y w) (.finset (N + 1)) "B")
      (getR N dx (PMem.set h t y w))
      (PMem.get (PMem.set h t y w) (.vec d) "th")
    = clippedBatchSumD (N := N) grad C (PMem.get h (.finset (N + 1)) "B")
      (getR N dx h)
      (PMem.get h (.vec d) "th")
  rw [PMem.get_set_ne t (.finset (N + 1)) h y "B" w hB,
    getR_set N dx h y w hD,
    PMem.get_set_ne t (.vec d) h y "th" w hT]

/-- `noisyG` reads only `B`, `D` and `th`. -/
lemma noisyG_frame (hm : MeasOK dx d grad) {t : Ty} (y : String)
    (hB : t ≠ Ty.finset (N + 1) ∨ y ≠ "B")
    (hD : t ≠ Ty.prod (.vec ((N + 1) * dx)) (.finset (N + 1)) ∨ y ≠ "D")
    (hT : t ≠ Ty.vec d ∨ y ≠ "th")
    (h : PMem.heap) (w : t.interp) :
    noisyG N dx d grad C v hm (PMem.set h t y w)
      = noisyG N dx d grad C v hm h := by
  rw [noisyG_apply, noisyG_apply, esem_bsE_frame N dx d grad C hm y hB hD hT h w]

/-- `fusedK` ignores writes to slots other than `D` and `th` (a write to `B` is
    overwritten by its own draw). -/
lemma fusedK_frame (hm : MeasOK dx d grad) {t : Ty} (y : String)
    (hD : t ≠ Ty.prod (.vec ((N + 1) * dx)) (.finset (N + 1)) ∨ y ≠ "D")
    (hT : t ≠ Ty.vec d ∨ y ≠ "th")
    (h : PMem.heap) (w : t.interp) :
    fusedK N dx d grad C v q hm (PMem.set h t y w)
      = fusedK N dx d grad C v q hm h := by
  rw [fusedK,
    fuseK_apply (t := .vec d) (bchV N) (poissonBatchKernel N q) _ (PMem.set h t y w),
    fuseK_apply (t := .vec d) (bchV N) (poissonBatchKernel N q) _ h,
    poissonBatchKernel_apply, poissonBatchKernel_apply]
  refine congrArg _ (funext fun B => ?_)
  by_cases hsame : t = Ty.finset (N + 1) ∧ y = "B"
  · -- the write is to `B` itself, and the fused draw overwrites it
    obtain ⟨rfl, rfl⟩ := hsame
    rw [show PMem.set (PMem.set h (.finset (N + 1)) "B" w) (.finset (N + 1)) (bchV N).name B
        = PMem.set h (.finset (N + 1)) (bchV N).name B from set_set_same h "B" w B]
  · -- a different slot: it commutes with the draw's store and the readers ignore it
    have hne : t ≠ Ty.finset (N + 1) ∨ y ≠ "B" := by
      by_cases ht : t = Ty.finset (N + 1)
      · exact Or.inr (fun hy => hsame ⟨ht, hy⟩)
      · exact Or.inl ht
    rw [show PMem.set (PMem.set h t y w) (.finset (N + 1)) (bchV N).name B
        = PMem.set (PMem.set h (.finset (N + 1)) (bchV N).name B) t y w from
      MemType.set_set_comm (M := PMem) t (.finset (N + 1)) h y (bchV N).name hne w B]
    exact noisyG_frame N dx d grad C v hm y hne hD hT _ w

/-! ### The resets of the four hidden variables, and what ignores them -/

/-- The reset of `g`, as `locDesugar` produces it. -/
noncomputable def gZ : Cmd String PMem :=
  Cmd.assign (gV d) (Expr.cst (default : EuclideanSpace ℝ (Fin d)))

/-- The reset of `jv`. -/
noncomputable def jvZ : Cmd String PMem := Cmd.assign jv (Expr.cst (default : ℕ))

/-- The reset of `B`. -/
noncomputable def bchZ : Cmd String PMem :=
  Cmd.assign (bchV N) (Expr.cst (default : Finset (Fin (N + 1))))

/-- The Poisson draw, named. -/
noncomputable def poisDraw : Cmd String PMem :=
  Cmd.random (bchV N) (poissonBatchKernel N q)

/-- The fused draw, named. -/
noncomputable def fusedDraw (hm : MeasOK dx d grad) : Cmd String PMem :=
  Cmd.random (gtV d) (fusedK N dx d grad C v q hm)

/-- The noisy draw after **[E-Comm]**, named. -/
noncomputable def noisyDraw (hm : MeasOK dx d grad) : Cmd String PMem :=
  Cmd.random (gtV d) (noisyG N dx d grad C v hm)

lemma indepY_bv_gAssign (hm : MeasOK dx d grad) :
    IndepY (M := PMem) bv (gAssign N dx d grad C hm) :=
  ⟨by vname_ne, fun h w =>
    esem_bsE_frame N dx d grad C hm "bv" (Or.inr (by decide)) (Or.inr (by decide))
      (Or.inr (by decide)) h w⟩

lemma indepY_bv_gtDraw : IndepY (M := PMem) bv (gtDraw d v) :=
  ⟨by vname_ne, fun h w => by
    show gaussKernelE (M := PMem) (getG d) (measurable_getG d) v (PMem.set h .bool bv.name w) = _
    rw [gaussKernelE_apply, gaussKernelE_apply,
      show getG d (PMem.set h .bool bv.name w) = getG d h from
        get_set_other h w (show ("bv" : String) ≠ "g" by decide)]⟩

lemma indepY_gV_bvZ : IndepY (M := PMem) (gV d) bvZ := ⟨by vname_ne, fun _ _ => rfl⟩
lemma indepY_gV_jvSet (n : ℕ) : IndepY (M := PMem) (gV d) (jvSet n) :=
  ⟨by vname_ne, fun _ _ => rfl⟩
lemma indepY_gV_poisDraw : IndepY (M := PMem) (gV d) (poisDraw N q) :=
  ⟨by vname_ne, fun _ _ => rfl⟩
lemma indepY_gV_noisyDraw (hm : MeasOK dx d grad) :
    IndepY (M := PMem) (gV d) (noisyDraw N dx d grad C v hm) :=
  ⟨by vname_ne, fun h w =>
    noisyG_frame N dx d grad C v hm "g" (Or.inr (by decide)) (Or.inr (by decide))
      (Or.inr (by decide)) h w⟩
lemma indepY_gV_fusedDraw (hm : MeasOK dx d grad) :
    IndepY (M := PMem) (gV d) (fusedDraw N dx d grad C v q hm) :=
  ⟨by vname_ne, fun h w =>
    fusedK_frame N dx d grad C v q hm "g" (Or.inr (by decide))
      (Or.inr (by decide)) h w⟩

lemma indepY_jv_bvZ : IndepY (M := PMem) jv bvZ := ⟨name_jv_ne_bv.symm, fun _ _ => rfl⟩
lemma indepY_jv_gZ : IndepY (M := PMem) jv (gZ d) := ⟨by vname_ne, fun _ _ => rfl⟩
lemma indepY_jv_poisDraw : IndepY (M := PMem) jv (poisDraw N q) :=
  ⟨fun hc => name_jv_ne_bchV N hc.symm, fun _ _ => rfl⟩
lemma indepY_jv_noisyDraw (hm : MeasOK dx d grad) :
    IndepY (M := PMem) jv (noisyDraw N dx d grad C v hm) :=
  ⟨by vname_ne, fun h w =>
    noisyG_frame N dx d grad C v hm "jv" (Or.inr (by decide)) (Or.inr (by decide))
      (Or.inr (by decide)) h w⟩
lemma indepY_jv_fusedDraw (hm : MeasOK dx d grad) :
    IndepY (M := PMem) jv (fusedDraw N dx d grad C v q hm) :=
  ⟨by vname_ne, fun h w =>
    fusedK_frame N dx d grad C v q hm "jv" (Or.inr (by decide))
      (Or.inr (by decide)) h w⟩

lemma indepY_bch_bvZ : IndepY (M := PMem) (bchV N) bvZ :=
  ⟨(name_bchV_ne_bv N).symm, fun _ _ => rfl⟩
lemma indepY_bch_jvZ : IndepY (M := PMem) (bchV N) jvZ :=
  ⟨name_jv_ne_bchV N, fun _ _ => rfl⟩
lemma indepY_bch_gZ : IndepY (M := PMem) (bchV N) (gZ d) :=
  ⟨by vname_ne, fun _ _ => rfl⟩
lemma indepY_bch_fusedDraw (hm : MeasOK dx d grad) :
    IndepY (M := PMem) (bchV N) (fusedDraw N dx d grad C v q hm) :=
  ⟨by vname_ne, fun h w =>
    fusedK_frame N dx d grad C v q hm "B" (Or.inr (by decide))
      (Or.inr (by decide)) h w⟩

lemma indepY_bv_gZ : IndepY (M := PMem) bv (gZ d) := ⟨by vname_ne, fun _ _ => rfl⟩
lemma indepY_bv_jvZ : IndepY (M := PMem) bv jvZ := ⟨name_jv_ne_bv, fun _ _ => rfl⟩
lemma indepY_bv_bchZ : IndepY (M := PMem) bv (bchZ N) :=
  ⟨name_bchV_ne_bv N, fun _ _ => rfl⟩
lemma indepY_bv_fusedDraw (hm : MeasOK dx d grad) :
    IndepY (M := PMem) bv (fusedDraw N dx d grad C v q hm) :=
  ⟨by vname_ne, fun h w =>
    fusedK_frame N dx d grad C v q hm "bv" (Or.inr (by decide))
      (Or.inr (by decide)) h w⟩

/-- **[E-Comm]** at `g`: the store to `g` floats past the Gaussian draw, whose kernel then
    reads the clipped batch sum directly. -/
lemma cequiv_swap_g (hm : MeasOK dx d grad) (R : St PMem → Prop) :
    CEquiv R (Cmd.seq (gAssign N dx d grad C hm) (gtDraw d v))
      (Cmd.seq (noisyDraw N dx d grad C v hm) (gAssign N dx d grad C hm)) := by
  have := isMarkov_noisyG N dx d grad C v hm
  refine CEquiv.swap (gV d) (gtV d) (by vname_ne) (batchSumPaperE N dx d grad C hm)
    (fun h w => ?_)
    (gaussKernelE (M := PMem) (getG d) (measurable_getG d) v)
    (noisyG N dx d grad C v hm) (fun h => ?_)
  · exact esem_bsE_frame N dx d grad C hm "gt" (Or.inr (by decide)) (Or.inr (by decide))
      (Or.inr (by decide)) h w
  · show gaussE (esem (batchSumPaperE N dx d grad C hm) h) v
      = gaussE (getG d (PMem.set h (.vec d) (gV d).name
          (esem (batchSumPaperE N dx d grad C hm) h))) v
    rw [show getG d (PMem.set h (.vec d) (gV d).name
        (esem (batchSumPaperE N dx d grad C hm) h))
        = esem (batchSumPaperE N dx d grad C hm) h from
      PMem.get_set_eq (.vec d) h (gV d).name _]

/-! ### The assembly: `blockLoc` and `fusedLoc` reduce to the normal form `blockNF` -/

/-- The common normal form: the four resets, then the fused draw. -/
noncomputable def blockNF (hm : MeasOK dx d grad) : Cmd String PMem :=
  Cmd.seq bvZ (Cmd.seq jvZ (Cmd.seq (gZ d)
    (Cmd.seq (bchZ N) (fusedDraw N dx d grad C v q hm))))

/-- The body of the `g`-block, with the store to `g` moved last. -/
lemma cequiv_locbv_body (hm : MeasOK dx d grad) (R : St PMem → Prop) :
    CEquiv R (Cmd.loc bv (prefixLI N dx d grad C v q hm))
      (Cmd.seq (Cmd.seq (Cmd.seq bvZ (Cmd.seq (poisDraw N q) (jvSet (N + 1))))
        (noisyDraw N dx d grad C v hm)) (gAssign N dx d grad C hm)) := by
  show CEquiv R (Cmd.loc bv (Cmd.seq (Cmd.seq (poissonSample N q)
    (gAssign N dx d grad C hm)) (gtDraw d v))) _
  refine (CEquiv.congrLocT bv (CEquiv.seqAssoc)).trans ?_
  refine (CEquiv.locNarrowRight bv
    (c₁ := Cmd.seq (gAssign N dx d grad C hm) (gtDraw d v))
    ⟨indepY_bv_gAssign N dx d grad C hm, indepY_bv_gtDraw d v⟩).trans ?_
  refine (CEquiv.congrHead (cequiv_loc_poissonSample N q R)).trans ?_
  refine (CEquiv.congrTail (cequiv_swap_g N dx d grad C v hm (fun _ => True))).trans ?_
  exact CEquiv.seqAssoc'

/-- **The `g`-block**: the final store to `g` is dead (`locDeadStore`). -/
lemma cequiv_locg_locbv (hm : MeasOK dx d grad) (R : St PMem → Prop) :
    CEquiv R (Cmd.loc (gV d) (Cmd.loc bv (prefixLI N dx d grad C v q hm)))
      (Cmd.seq (gZ d) (Cmd.seq (Cmd.seq bvZ (Cmd.seq (poisDraw N q) (jvSet (N + 1))))
        (noisyDraw N dx d grad C v hm))) :=
  (CEquiv.congrLocT (gV d)
      (cequiv_locbv_body N dx d grad C v q hm (fun _ => True))).trans <|
    (CEquiv.locDeadStore (gV d)).trans
      (CEquiv.locDead (gV d)
        (c := Cmd.seq (Cmd.seq bvZ (Cmd.seq (poisDraw N q) (jvSet (N + 1))))
          (noisyDraw N dx d grad C v hm))
        ⟨⟨indepY_gV_bvZ d, indepY_gV_poisDraw N d q, indepY_gV_jvSet d (N + 1)⟩,
          indepY_gV_noisyDraw N dx d grad C v hm⟩)

/-- The body of the `jv`-block, with the counter store moved last (**[E-Frame]**). -/
lemma cequiv_locjv_body (hm : MeasOK dx d grad) (R : St PMem → Prop) :
    CEquiv R (Cmd.seq (gZ d) (Cmd.seq (Cmd.seq bvZ (Cmd.seq (poisDraw N q)
        (jvSet (N + 1)))) (noisyDraw N dx d grad C v hm)))
      (Cmd.seq (Cmd.seq (gZ d) (Cmd.seq bvZ (Cmd.seq (poisDraw N q)
        (noisyDraw N dx d grad C v hm)))) (jvSet (N + 1))) := by
  refine (CEquiv.congrTail (CEquiv.seqAssoc)).trans ?_
  refine (CEquiv.congrTail (CEquiv.congrTail (CEquiv.seqAssoc))).trans ?_
  refine (CEquiv.congrTail (CEquiv.congrTail (CEquiv.congrTail
    (CEquiv.assignFrame jv
      (indepY_jv_noisyDraw N dx d grad C v hm) (N + 1))))).trans ?_
  refine (CEquiv.congrTail (CEquiv.congrTail (CEquiv.seqAssoc'))).trans ?_
  refine (CEquiv.congrTail (CEquiv.seqAssoc')).trans ?_
  exact CEquiv.seqAssoc'

/-- **The `jv`-block**: the final counter store is dead. -/
lemma cequiv_locjv (hm : MeasOK dx d grad) (R : St PMem → Prop) :
    CEquiv R (Cmd.loc jv (Cmd.seq (gZ d) (Cmd.seq (Cmd.seq bvZ (Cmd.seq (poisDraw N q)
        (jvSet (N + 1)))) (noisyDraw N dx d grad C v hm))))
      (Cmd.seq jvZ (Cmd.seq (gZ d) (Cmd.seq bvZ (Cmd.seq (poisDraw N q)
        (noisyDraw N dx d grad C v hm))))) :=
  (CEquiv.congrLocT jv
      (cequiv_locjv_body N dx d grad C v q hm (fun _ => True))).trans <|
    (CEquiv.locDeadStore jv).trans
      (CEquiv.locDead jv
        (c := Cmd.seq (gZ d) (Cmd.seq bvZ (Cmd.seq (poisDraw N q)
          (noisyDraw N dx d grad C v hm))))
        ⟨indepY_jv_gZ d, indepY_jv_bvZ, indepY_jv_poisDraw N q,
          indepY_jv_noisyDraw N dx d grad C v hm⟩)

/-- **The `B`-block**: the resets move out of the block (`locNarrow`), and **[E-Merge]**
    fuses the batch draw with the noisy draw into `fusedK`. -/
lemma cequiv_locB (hm : MeasOK dx d grad) (R : St PMem → Prop) :
    CEquiv R (Cmd.loc (bchV N) (Cmd.seq jvZ (Cmd.seq (gZ d) (Cmd.seq bvZ
        (Cmd.seq (poisDraw N q) (noisyDraw N dx d grad C v hm))))))
      (blockNF N dx d grad C v q hm) := by
  have := isMarkov_noisyG N dx d grad C v hm
  refine (CEquiv.locNarrow (bchV N) (indepY_bch_jvZ N)).trans ?_
  refine (CEquiv.congrTail (CEquiv.locNarrow (bchV N) (indepY_bch_gZ N d))).trans ?_
  refine (CEquiv.congrTail (CEquiv.congrTail
    (CEquiv.locNarrow (bchV N) (indepY_bch_bvZ N)))).trans ?_
  refine (CEquiv.congrTail (CEquiv.congrTail (CEquiv.congrTail
    (CEquiv.fuseGen (bchV N) (gtV d) (by vname_ne) (poissonBatchKernel N q)
      (noisyG N dx d grad C v hm))))).trans ?_
  refine (CEquiv.congrTail (CEquiv.frameRight bv (indepY_bv_gZ d) default)).trans ?_
  exact CEquiv.frameRight bv indepY_bv_jvZ default

/-- **The block, reduced.**  `blockLoc` is the normal form. -/
lemma cequiv_blockLoc_nf (hm : MeasOK dx d grad) (R : St PMem → Prop) :
    CEquiv R (blockLoc N dx d grad C v q hm) (blockNF N dx d grad C v q hm) := by
  show CEquiv R (Cmd.loc bv (Cmd.loc (bchV N) (Cmd.loc jv (Cmd.loc (gV d)
    (prefixLI N dx d grad C v q hm))))) _
  -- the coin's block moves innermost
  refine (CEquiv.locComm bv (bchV N) (by vname_ne)
    (Cmd.loc jv (Cmd.loc (gV d) (prefixLI N dx d grad C v q hm)))).trans ?_
  refine (CEquiv.congrLocT (bchV N) (CEquiv.locComm bv jv (by vname_ne)
    (Cmd.loc (gV d) (prefixLI N dx d grad C v q hm)))).trans ?_
  refine (CEquiv.congrLocT (bchV N) (CEquiv.congrLocT jv
    (CEquiv.locComm bv (gV d) (by vname_ne)
      (prefixLI N dx d grad C v q hm)))).trans ?_
  -- then the three blocks, from the inside out
  refine (CEquiv.congrLocT (bchV N) (CEquiv.congrLocT jv
    (cequiv_locg_locbv N dx d grad C v q hm (fun _ => True)))).trans ?_
  refine (CEquiv.congrLocT (bchV N)
    (cequiv_locjv N dx d grad C v q hm (fun _ => True))).trans ?_
  exact cequiv_locB N dx d grad C v q hm R

/-- **The fused block, reduced**: `fusedLoc` is `blockNF`. -/
lemma cequiv_fusedLoc_nf (hm : MeasOK dx d grad) (R : St PMem → Prop) :
    CEquiv R (fusedLoc N dx d grad C v q hm) (blockNF N dx d grad C v q hm) := by
  show CEquiv R (Cmd.loc bv (Cmd.loc (bchV N) (Cmd.loc jv (Cmd.loc (gV d)
    (fusedDraw N dx d grad C v q hm))))) _
  refine (CEquiv.congrLocT bv (CEquiv.congrLocT (bchV N) (CEquiv.congrLocT jv
    (CEquiv.locDead (gV d)
      (indepY_gV_fusedDraw N dx d grad C v q hm))))).trans ?_
  refine (CEquiv.congrLocT bv (CEquiv.congrLocT (bchV N)
    (CEquiv.locDead jv (c := Cmd.seq (gZ d) (fusedDraw N dx d grad C v q hm))
      ⟨indepY_jv_gZ d, indepY_jv_fusedDraw N dx d grad C v q hm⟩))).trans ?_
  refine (CEquiv.congrLocT bv (CEquiv.locNarrow (bchV N) (indepY_bch_jvZ N))).trans ?_
  refine (CEquiv.congrLocT bv (CEquiv.congrTail
    (CEquiv.locNarrow (bchV N) (indepY_bch_gZ N d)))).trans ?_
  refine (CEquiv.congrLocT bv (CEquiv.congrTail (CEquiv.congrTail
    (CEquiv.locDead (bchV N)
      (indepY_bch_fusedDraw N dx d grad C v q hm))))).trans ?_
  exact CEquiv.locDead bv
    (c := Cmd.seq jvZ (Cmd.seq (gZ d) (Cmd.seq (bchZ N) (fusedDraw N dx d grad C v q hm))))
    ⟨indepY_bv_jvZ, indepY_bv_gZ d, indepY_bv_bchZ N,
      indepY_bv_fusedDraw N dx d grad C v q hm⟩

/-- **The fusion of §5.1.1**: the sampling block of a DP-SGD round is equivalent to the
    fused sampling `fusedLoc`. -/
theorem cequiv_blockLoc_fusedLoc (hm : MeasOK dx d grad) (R : St PMem → Prop) :
    CEquiv R (blockLoc N dx d grad C v q hm) (fusedLoc N dx d grad C v q hm) :=
  (cequiv_blockLoc_nf N dx d grad C v q hm R).trans
    (cequiv_fusedLoc_nf N dx d grad C v q hm R).symm

end Outer

end DPSGDPaper
