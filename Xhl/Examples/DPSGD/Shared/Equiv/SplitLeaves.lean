import Xhl.Examples.DPSGD.Shared.Equiv.BlockCEquiv

/-!
# The split program of a paying round (last-iterate model)

A paying round of the last-iterate study (§5.1.3, Appendix D.2) is derived by **[Equiv]**
onto the split program `splitPrefix` (variances `σ₁`, `σ₂`, block variance `σ₂ + σ₁`)

    B ←$ ν_B ;  z ←$ (1−q)·𝒩(0, σ₂) + q·𝒩(u, σ₂) ;  g̃ ←$ 𝒩(g(B ∖ {i}) + z, σ₁)

with `ν_B = νb` the batch law with record `i` erased and `u = uRec` record `i`'s clipped
gradient.  `cequiv_blockLoc_splitLoc` is the [Equiv] premise; the three draws are discharged
by [Samp], [Samp], [Samp-Gap] in `LastIterate/SpendRound.lean`.
-/

open MeasureTheory ProbabilityTheory ENNReal Continuous
open scoped NNReal

namespace DPSGDPaper

section Split

variable (N dx d : ℕ)
  (grad : EuclideanSpace ℝ (Fin dx) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
  (C : ℝ≥0)
  (q : ℝ≥0) (σ1 σ2 : ℝ≥0) (i : Fin (N + 1))

/-! ## The three samplers of the split program -/

/-- Record `i`'s clipped gradient (`0` when the record is absent). -/
noncomputable def uRec (m : PMem.heap) : EuclideanSpace ℝ (Fin d) :=
  clipV C (gradBot grad (getR N dx m i) (getTh d m))

lemma measurable_uRec (hm : MeasOK dx d grad) :
    Measurable (uRec N dx d grad C i) := by
  have h := measurable_clippedBatchSumD_at (N := N) (dx := dx) grad hm C {i}
  unfold uRec
  simpa only [clippedBatchSumD, Finset.sum_singleton] using h

lemma norm_uRec_le (m : PMem.heap) :
    ‖uRec N dx d grad C i m‖ ≤ (C : ℝ) := norm_clipV_le C.2 _

/-- The mixture draw: the noise, plus the record's gradient if its coin comes up. -/
noncomputable def mixZK (hm : MeasOK dx d grad) :
    @ProbabilityTheory.Kernel PMem.heap (EuclideanSpace ℝ (Fin d)) PMem.heapMeas
      (Ty.measurableSpace (.vec d)) :=
  mixKernel (q : ℝ≥0∞)
    (gaussKernelE (M := PMem) (fun _ => 0) measurable_const σ2)
    (gaussKernelE (M := PMem) (uRec N dx d grad C i)
      (measurable_uRec N dx d grad C i hm) σ2)

lemma mixZK_apply' (hm : MeasOK dx d grad) (x : PMem.heap) :
    mixZK N dx d grad C q σ2 i hm x
      = (1 - (q : ℝ≥0∞)) • gaussE (0 : EuclideanSpace ℝ (Fin d)) σ2
        + (min (q : ℝ≥0∞) 1) • gaussE (uRec N dx d grad C i x) σ2 := by
  rw [mixZK, mixKernel_apply]; rfl

@[simp] lemma mixZK_apply (hm : MeasOK dx d grad) (hq : q ≤ 1) (x : PMem.heap) :
    mixZK N dx d grad C q σ2 i hm x
      = (1 - (q : ℝ≥0∞)) • gaussE (0 : EuclideanSpace ℝ (Fin d)) σ2
        + (q : ℝ≥0∞) • gaussE (uRec N dx d grad C i x) σ2 := by
  rw [mixZK, mixKernel_apply_of_le (by exact_mod_cast hq)]; rfl

instance isMarkov_mixZK (hm : MeasOK dx d grad) :
    IsMarkovKernel (mixZK N dx d grad C q σ2 i hm) := by
  unfold mixZK; infer_instance

/-- The centre of the last draw: the clipped sum over the batch without record `i`, plus
    `z` (stored in `g`). -/
noncomputable def splitCtr (m : PMem.heap) : EuclideanSpace ℝ (Fin d) :=
  cbs N dx d grad C m ((getBatch N m).erase i) + getG d m

lemma measurable_splitCtr (hm : MeasOK dx d grad) :
    Measurable (splitCtr N dx d grad C i) := by
  have hF : Measurable (fun p : Finset (Fin (N + 1)) × PMem.heap =>
      cbs N dx d grad C p.2 p.1) := by
    refine measurable_from_prod_countable_right fun B => ?_
    exact measurable_clippedBatchSumD_at grad hm C B
  have hc : Measurable (fun m : PMem.heap =>
      cbs N dx d grad C m ((getBatch N m).erase i)) :=
    Measurable.comp (g := fun p : Finset (Fin (N + 1)) × PMem.heap => cbs N dx d grad C p.2 p.1)
      (f := fun m : PMem.heap => ((getBatch N m).erase i, m)) hF
      (((Measurable.of_discrete (f := fun S : Finset (Fin (N + 1)) => S.erase i)).comp
        (measurable_getBatch N)).prodMk measurable_id)
  exact hc.add (measurable_getG d)

/-- The split program: the batch, the mixture, the noisy sum. -/
noncomputable def splitPrefix (hm : MeasOK dx d grad) : Cmd String PMem :=
  Cmd.seq (Cmd.seq
    (Cmd.random (bchV N) (Kernel.const _ (νb N q i)))
    (Cmd.random (gV d) (mixZK N dx d grad C q σ2 i hm)))
    (Cmd.random (gtV d) (gaussKernelE (M := PMem) (splitCtr N dx d grad C i)
      (measurable_splitCtr N dx d grad C i hm) σ1))

/-! ## Reading through the split program's writes -/

lemma uRec_set_bch (m : PMem.heap) (B : Finset (Fin (N + 1))) :
    uRec N dx d grad C i (PMem.set m (.finset (N + 1)) (bchV N).name B)
      = uRec N dx d grad C i m := by
  unfold uRec getTh
  rw [getR_set N dx m (t := .finset (N + 1)) _ B (Or.inl (fun h => Ty.noConfusion h)),
    get_set_other (M := PMem) _ _ (by show ("B" : String) ≠ "th"; decide)]

lemma mixZK_set_bch (hm : MeasOK dx d grad) (m : PMem.heap)
    (B : Finset (Fin (N + 1))) :
    mixZK N dx d grad C q σ2 i hm (PMem.set m (.finset (N + 1)) (bchV N).name B)
      = mixZK N dx d grad C q σ2 i hm m := by
  rw [mixZK_apply', mixZK_apply', uRec_set_bch]

lemma splitCtr_set (m : PMem.heap) (B : Finset (Fin (N + 1)))
    (z : EuclideanSpace ℝ (Fin d)) :
    splitCtr N dx d grad C i
        (PMem.set (PMem.set m (.finset (N + 1)) (bchV N).name B) (.vec d) (gV d).name z)
      = cbs N dx d grad C m (B.erase i) + z := by
  unfold splitCtr
  have hB : getBatch N
      (PMem.set (PMem.set m (.finset (N + 1)) (bchV N).name B) (.vec d) (gV d).name z) = B := by
    unfold getBatch
    rw [get_set_other (M := PMem) _ _ (by show ("g" : String) ≠ "B"; decide)]
    exact PMem.get_set_eq _ _ _ _
  have hG : getG d
      (PMem.set (PMem.set m (.finset (N + 1)) (bchV N).name B) (.vec d) (gV d).name z) = z :=
    PMem.get_set_eq _ _ _ _
  have hcbs : cbs N dx d grad C
      (PMem.set (PMem.set m (.finset (N + 1)) (bchV N).name B) (.vec d) (gV d).name z)
      (B.erase i) = cbs N dx d grad C m (B.erase i) := by
    unfold cbs getTh
    rw [getR_set N dx _ (t := .vec d) _ z (Or.inl (fun h => Ty.noConfusion h)),
      getR_set N dx m (t := .finset (N + 1)) _ B (Or.inl (fun h => Ty.noConfusion h)),
      get_set_other (M := PMem) _ _ (by show ("g" : String) ≠ "th"; decide),
      get_set_other (M := PMem) _ _ (by show ("B" : String) ≠ "th"; decide)]
  rw [hB, hG, hcbs]

/-! ## The split program's binds compose to the fused kernel -/

/-- `νb`-almost every batch misses record `i`. -/
lemma ae_notMem_νb : ∀ᵐ B ∂(νb N q i), i ∉ B := by
  unfold νb
  rw [ae_map_iff (p := fun B : Finset (Fin (N + 1)) => i ∉ B)
    Measurable.of_discrete.aemeasurable MeasurableSet.of_discrete]
  exact Filter.Eventually.of_forall fun S => Finset.notMem_erase i S

/-- The mixture at variance `σ₂` followed by the noisy sum at `σ₁`, under the batch draw,
    is the fused sampler at `σ₂ + σ₁`. -/
lemma split_bind_eq_fusedK (hm : MeasOK dx d grad) (hq : q ≤ 1) (x : PMem.heap) :
    (νb N q i).bind (fun B =>
        (mixZK N dx d grad C q σ2 i hm x).bind (fun z =>
          gaussE (cbs N dx d grad C x (B.erase i) + z) σ1))
      = fusedK N dx d grad C (σ2 + σ1) q hm x := by
  rw [fusedK_mix N dx d grad C (σ2 + σ1) q i hm hq]
  refine Measure.bind_congr_right ?_
  filter_upwards [ae_notMem_νb N q i] with B hB
  have hBe : B.erase i = B := Finset.erase_eq_of_notMem hB
  rw [hBe, mixZK_apply (hq := hq)]
  set c := cbs N dx d grad C x B with hc
  have hK : Measurable (fun z : EuclideanSpace ℝ (Fin d) => gaussE (c + z) σ1) :=
    gaussE_measurable.comp (measurable_const_add c)
  rw [add_bind' _ _ hK, smul_bind' _ _ hK, smul_bind' _ _ hK]
  have hcomm : (fun z : EuclideanSpace ℝ (Fin d) => gaussE (c + z) σ1)
      = fun z => gaussE (z + c) σ1 := funext fun z => by rw [add_comm]
  rw [hcomm, gaussE_split_shift, gaussE_split_shift, zero_add]
  have hins : cbs N dx d grad C x (insert i B)
      = uRec N dx d grad C i x + c := by
    show clippedBatchSumD (N := N) grad C (insert i B) (getR N dx x) (getTh d x) = _
    rw [clippedBatchSumD_insert_erase, hBe]
    rfl
  rw [hins]

/-- The split block: the split program with the hidden variables local. -/
noncomputable def splitLoc (hm : MeasOK dx d grad) : Cmd String PMem :=
  locs (hidden N d) (splitPrefix N dx d grad C q σ1 σ2 i hm)

/-! ## The split identity

Both blocks reduce to `blockNF` at variance `σ₂ + σ₁`: on the split side **[E-Merge]**
fires twice and **[E-Leaf-S]** exchanges the composite kernel for `fusedK`
(`fuse_splitFK_eq_fusedK`). -/

/-- The batch draw of the split program, named. -/
noncomputable def bchDraw : Cmd String PMem :=
  Cmd.random (bchV N) (Kernel.const _ (νb N q i))

/-- The mixture draw, named. -/
noncomputable def mixDraw (hm : MeasOK dx d grad) : Cmd String PMem :=
  Cmd.random (gV d) (mixZK N dx d grad C q σ2 i hm)

/-- The noisy-sum draw, named. -/
noncomputable def splitDraw (hm : MeasOK dx d grad) : Cmd String PMem :=
  Cmd.random (gtV d) (gaussKernelE (M := PMem) (splitCtr N dx d grad C i)
    (measurable_splitCtr N dx d grad C i hm) σ1)

/-- The mixture fused into the noisy sum (first **[E-Merge]**). -/
noncomputable def splitFK (hm : MeasOK dx d grad) :
    @ProbabilityTheory.Kernel PMem.heap (EuclideanSpace ℝ (Fin d)) PMem.heapMeas
      (Ty.measurableSpace (.vec d)) :=
  fuseK (t := .vec d) (gV d) (mixZK N dx d grad C q σ2 i hm)
    (gaussKernelE (M := PMem) (splitCtr N dx d grad C i)
      (measurable_splitCtr N dx d grad C i hm) σ1)

instance isSubMarkov_splitFK (hm : MeasOK dx d grad) :
    IsSubMarkovKernel (splitFK N dx d grad C q σ1 σ2 i hm) :=
  fuseK_isSubMarkov (t := .vec d) (gV d) (mixZK N dx d grad C q σ2 i hm)
    (gaussKernelE (M := PMem) (splitCtr N dx d grad C i)
      (measurable_splitCtr N dx d grad C i hm) σ1)

/-- The two fusions compose to the fused sampler, at every heap. -/
lemma fuse_splitFK_eq_fusedK (hm : MeasOK dx d grad) (hq : q ≤ 1)
    (x : PMem.heap) :
    fuseK (t := .vec d) (bchV N) (Kernel.const _ (νb N q i))
        (splitFK N dx d grad C q σ1 σ2 i hm) x
      = fusedK N dx d grad C (σ2 + σ1) q hm x := by
  rw [fuseK_apply, Kernel.const_apply,
    ← split_bind_eq_fusedK N dx d grad C q σ1 σ2 i hm hq x]
  refine Measure.bind_congr_right (Filter.Eventually.of_forall fun B => ?_)
  beta_reduce
  unfold splitFK
  rw [fuseK_apply, mixZK_set_bch]
  refine Measure.bind_congr_right (Filter.Eventually.of_forall fun z => ?_)
  beta_reduce
  rw [gaussKernelE_apply, splitCtr_set]

lemma indepY_gV_bchDraw : IndepY (M := PMem) (gV d) (bchDraw N q i) :=
  ⟨by vname_ne, fun _ _ => rfl⟩

lemma indepY_jv_bchZ : IndepY (M := PMem) jv (bchZ N) :=
  ⟨fun hc => name_jv_ne_bchV N hc.symm, fun _ _ => rfl⟩

/-- **The split block, reduced** to `blockNF` at variance `σ₂ + σ₁`. -/
lemma cequiv_splitLoc_nf (hm : MeasOK dx d grad) (hq : q ≤ 1)
    (R : St PMem → Prop) :
    CEquiv R (splitLoc N dx d grad C q σ1 σ2 i hm)
      (blockNF N dx d grad C (σ2 + σ1) q hm) := by
  have : IsSubMarkovKernel (fuseK (t := .vec d) (bchV N) (Kernel.const PMem.heap (νb N q i))
      (splitFK N dx d grad C q σ1 σ2 i hm)) :=
    fuseK_isSubMarkov (t := .vec d) (bchV N) _ _
  show CEquiv R (Cmd.loc bv (Cmd.loc (bchV N) (Cmd.loc jv (Cmd.loc (gV d)
    (Cmd.seq (Cmd.seq (bchDraw N q i) (mixDraw N dx d grad C q σ2 i hm))
      (splitDraw N dx d grad C σ1 i hm)))))) _
  -- `jv`'s block moves outside `B`'s
  refine (CEquiv.congrLocT bv (CEquiv.locComm (bchV N) jv (by vname_ne)
    (Cmd.loc (gV d) (Cmd.seq (Cmd.seq (bchDraw N q i) (mixDraw N dx d grad C q σ2 i hm))
      (splitDraw N dx d grad C σ1 i hm))))).trans ?_
  -- the `g`-block: narrow past the batch draw, then [E-Merge]
  refine (CEquiv.congrLocT bv (CEquiv.congrLocT jv (CEquiv.congrLocT (bchV N)
    ((CEquiv.congrLocT (gV d) (CEquiv.seqAssoc)).trans
      ((CEquiv.locNarrow (gV d) (indepY_gV_bchDraw N d q i)).trans
        (CEquiv.congrTail (CEquiv.fuseGen (gV d) (gtV d) (by vname_ne)
          (mixZK N dx d grad C q σ2 i hm)
          (gaussKernelE (M := PMem) (splitCtr N dx d grad C i)
            (measurable_splitCtr N dx d grad C i hm) σ1)))))))).trans ?_
  -- the `B`-block: float `g`'s reset to the front, narrow, [E-Merge], [E-Leaf-S]
  refine (CEquiv.congrLocT bv (CEquiv.congrLocT jv ((CEquiv.congrLocT (bchV N)
    ((CEquiv.seqAssoc').trans
      ((CEquiv.congrHead (CEquiv.assignFrame (gV d)
          (indepY_gV_bchDraw N d q i) default).symm).trans
        (CEquiv.seqAssoc)))).trans
    ((CEquiv.locNarrow (bchV N) (indepY_bch_gZ N d)).trans
      (CEquiv.congrTail ((CEquiv.fuseGen (bchV N) (gtV d) (by vname_ne)
          (Kernel.const PMem.heap (νb N q i)) (splitFK N dx d grad C q σ1 σ2 i hm)).trans
        (CEquiv.congrTail (CEquiv.leafDraw (gtV d) _ _ (fun s _ =>
          (fuse_splitFK_eq_fusedK N dx d grad C q σ1 σ2 i hm hq s.1).symm))))))))).trans ?_
  -- the dead blocks: `jv` and `bv` are never read
  refine (CEquiv.congrLocT bv (CEquiv.locDead jv
    (c := Cmd.seq (gZ d) (Cmd.seq (bchZ N) (fusedDraw N dx d grad C (σ2 + σ1) q hm)))
    ⟨indepY_jv_gZ d, indepY_jv_bchZ N,
      indepY_jv_fusedDraw N dx d grad C (σ2 + σ1) q hm⟩)).trans ?_
  exact CEquiv.locDead bv
    (c := Cmd.seq jvZ (Cmd.seq (gZ d) (Cmd.seq (bchZ N)
      (fusedDraw N dx d grad C (σ2 + σ1) q hm))))
    ⟨indepY_bv_jvZ, indepY_bv_gZ d, indepY_bv_bchZ N,
      indepY_bv_fusedDraw N dx d grad C (σ2 + σ1) q hm⟩

/-- **The split identity**: the block at variance `σ₂ + σ₁` is equivalent to the split
    block. -/
theorem cequiv_blockLoc_splitLoc (hm : MeasOK dx d grad) (hq : q ≤ 1)
    (R : St PMem → Prop) :
    CEquiv R (blockLoc N dx d grad C (σ2 + σ1) q hm)
      (splitLoc N dx d grad C q σ1 σ2 i hm) :=
  (cequiv_blockLoc_nf N dx d grad C (σ2 + σ1) q hm R).trans
    (cequiv_splitLoc_nf N dx d grad C q σ1 σ2 i hm hq R).symm

end Split

end DPSGDPaper
