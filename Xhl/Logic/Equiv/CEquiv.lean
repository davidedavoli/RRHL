import Xhl.Logic.Equiv.CEquivSound

open Continuous

/-!
# `CEquiv` — derivable program equivalence

The program equivalence calculus of Appendix E (Figures 10–11).  `CEquiv R c c'` is the
judgment `⊢ c ≡_R c'`: one constructor per equation of Figure 10 and per closure rule of
Figure 11.  `CEquiv.sound` (Theorem E.1) turns it into the semantic equality
`∀ s, R s → osemA c s = osemA c' s` that **[Equiv]** (`TDeriv.equiv`) consumes.

The index `R` is the restriction (the states the precondition allows); [E-If-F], [E-Idle],
[E-Ghost], [E-Count] and [E-Defer-C] hold only on restricted states.  No constructor takes
a semantic equality of programs as a premise; distribution-specific facts enter only as
kernel parameters.  The rest of the file derives the forms the case studies use.
-/

open MeasureTheory ProbabilityTheory ENNReal Cmd

variable {ident : Type} {M : MemType ident}

namespace Continuous

/-- **Derivable program equivalence.**  One constructor per equivalence axiom, plus
    congruence, restriction and the equivalence-relation rules. -/
inductive CEquiv : (St M → Prop) → Cmd ident M → Cmd ident M → Prop where
  -- Equivalence and restriction: [E-Refl], [E-Sym], [E-Trans], [E-Restr]
  | refl {R : St M → Prop} (c : Cmd ident M) : CEquiv R c c
  | symm {R : St M → Prop} {c c' : Cmd ident M} (h : CEquiv R c c') : CEquiv R c' c
  | trans {R : St M → Prop} {c d c' : Cmd ident M}
      (h : CEquiv R c d) (h' : CEquiv R d c') : CEquiv R c c'
  /-- **[E-Restr]**: an equivalence valid on `R'` is valid on any smaller `R`. -/
  | weaken {R R' : St M → Prop} {c c' : Cmd ident M}
      (hR : ∀ s, R s → R' s) (h : CEquiv R' c c') : CEquiv R c c'

  /-- **[E-Seq]**.  The tail premise is unrestricted. -/
  | congrSeq {R : St M → Prop} {c₁ c₁' c₂ c₂' : Cmd ident M}
      (h₁ : CEquiv R c₁ c₁') (h₂ : CEquiv (fun _ => True) c₂ c₂') :
      CEquiv R (Cmd.seq c₁ c₂) (Cmd.seq c₁' c₂')
  /-- **[E-Seq-A]**: congruence for `seq` under an assignment head, which carries the
      restriction forward. -/
  | congrSeqDet {t : Ty} (x : Vars ident t) (e : Expr M t)
      {R R' : St M → Prop} {c c' : Cmd ident M} 
      (hR : ∀ s, R s → R' ((M.set s.1 t x.name (esem e s.1), s.2) : St M))
      (h : CEquiv R' c c') :
      CEquiv R (Cmd.seq (Cmd.assign x e) c) (Cmd.seq (Cmd.assign x e) c')
  /-- **[E-If]**: each branch may assume the guard. -/
  | congrCond {R : St M → Prop} {e : BExpr M} {c₁ c₁' c₂ c₂' : Cmd ident M}
      (h₁ : CEquiv (fun s => R s ∧ esem e s.1 = true) c₁ c₁')
      (h₂ : CEquiv (fun s => R s ∧ esem e s.1 = false) c₂ c₂') :
      CEquiv R (Cmd.cond e c₁ c₂) (Cmd.cond e c₁' c₂')
  /-- **[E-Loc]**: the body may assume any `R'` holding at `resetV x s`. -/
  | congrLoc {t : Ty} (x : Vars ident t) {R R' : St M → Prop} {c c' : Cmd ident M}
      (hR : ∀ s, R s → R' (resetV x s)) (h : CEquiv R' c c') :
      CEquiv R (Cmd.loc x c) (Cmd.loc x c')

  /-- **[E-Ghost]**: a variable neither program mentions may be assumed to hold its
      default, provided the restriction does not read it (`hR`). -/
  | ghost {t : Ty} (y : Vars ident t) {R : St M → Prop} {c c' : Cmd ident M}
      (hic : IndepY y c) (hic' : IndepY y c')
      (hR : ∀ s : St M, R s → R (resetV y s))
      (h : CEquiv (fun s => R s ∧ M.get s.1 t y.name = default) c c') :
      CEquiv R c c'

  /-- **[E-Leaf-A]**: replace an assignment's expression by one that agrees with it on
      the restriction. -/
  | leafAssign {t : Ty} (x : Vars ident t) {R : St M → Prop} (e e' : Expr M t)
      (he : ∀ s : St M, R s → esem e' s.1 = esem e s.1) :
      CEquiv R (Cmd.assign x e) (Cmd.assign x e')
  /-- **[E-Leaf-S]**: likewise for a sampling and its kernel. -/
  | leafDraw {t : Ty} (x : Vars ident t) {R : St M → Prop}
      (κ κ' : @ProbabilityTheory.Kernel M.heap t.interp M.heapMeas (Ty.measurableSpace t))
      [IsSubMarkovKernel κ] [IsSubMarkovKernel κ']
      (hκ : ∀ s : St M, R s → κ' s.1 = κ s.1) :
      CEquiv R (Cmd.random x κ) (Cmd.random x κ')
  /-- **[E-Seq-V]**: a restriction determined by the values of the variables `ys` is
      transported past a head that writes none of them (`NoWrite`, syntactic). -/
  | seqVals {R : St M → Prop} {c₁ c₂ c₂' : Cmd ident M}
      (ys : List ((t : Ty) × Vars ident t))
      (hR : ∀ s s' : St M,
        (∀ z ∈ ys, M.get s.1 z.1 z.2.name = M.get s'.1 z.1 z.2.name) → R s → R s')
      (hnw : ∀ z ∈ ys, NoWrite z.2.name c₁)
      (h₂ : CEquiv R c₂ c₂') :
      CEquiv R (Cmd.seq c₁ c₂) (Cmd.seq c₁ c₂')

  /-- **[E-If-F]**: a conditional whose guard is false on the restriction is its
      else-branch. -/
  | ifFalse {R : St M → Prop} (e : BExpr M) (c₁ c₂ : Cmd ident M)
      (hR : ∀ s, R s → esem e s.1 = false) :
      CEquiv R (Cmd.cond e c₁ c₂) c₂
  /-- **[E-Idle]**: storing the default into a variable that already holds it is `skip`. -/
  | idleReset {t : Ty} (x : Vars ident t) {R : St M → Prop}
      (hR : ∀ s, R s → M.get s.1 t x.name = default) :
      CEquiv R (Cmd.assign x (Expr.cst default)) Cmd.skip

  /-- **[E-Unroll]**. -/
  | unroll {R : St M → Prop} {e : BExpr M} {c : Cmd ident M} :
      CEquiv R (Cmd.while e c) (Cmd.cond e (Cmd.seq c (Cmd.while e c)) Cmd.skip)
  /-- **[E-Count]**: a counted loop `while x < n do c`, whose body ends with `x := x + 1`
      and writes `x` nowhere else (`IncLast`, syntactic), is its `k`-fold unrolling on the
      states with `x + k = n`. -/
  | count (x : Vars ident .nat) (n : ℕ) {c : Cmd ident M} (hc : IncLast x c) (k : ℕ) :
      CEquiv (fun s => M.get s.1 .nat x.name + k = n) (Cmd.while (ltW x n) c) (iterCmd c k)

  -- [E-SeqSkip], [E-SkipSeq], [E-Assoc]
  | seqSkip {R : St M → Prop} (c : Cmd ident M) : CEquiv R (Cmd.seq c Cmd.skip) c
  | skipSeq {R : St M → Prop} {c : Cmd ident M} :
      CEquiv R (Cmd.seq Cmd.skip c) c
  | seqAssoc {R : St M → Prop} {c₁ c₂ c₃ : Cmd ident M} :
      CEquiv R (Cmd.seq (Cmd.seq c₁ c₂) c₃) (Cmd.seq c₁ (Cmd.seq c₂ c₃))

  /-- **[E-Loc-D]**: a block is its body between two resets. -/
  | locDesugar {t : Ty} (x : Vars ident t) {R : St M → Prop} {c : Cmd ident M}
      : CEquiv R (loc x c) (locReset x c)

  /-- **[E-Frame]**: a store of a constant commutes with a command that ignores the
      variable. -/
  | assignFrame {t₀ : Ty} (y : Vars ident t₀) {R : St M → Prop}
      {c : Cmd ident M} (hind : IndepY y c) (w : t₀.interp) :
      CEquiv R (Cmd.seq (Cmd.assign y (Expr.cst w)) c) (Cmd.seq c (Cmd.assign y (Expr.cst w)))

  /-- **[E-Defer]**. -/
  | defer {t₀ : Ty} (y : Vars ident t₀) {R : St M → Prop}
      {κ : @ProbabilityTheory.Kernel M.heap t₀.interp M.heapMeas (Ty.measurableSpace t₀)}
      [IsSubMarkovKernel κ]
      {μ : Measure t₀.interp} (hκ : ∀ h, κ h = μ)
      {c : Cmd ident M} (hind : IndepY y c) :
      CEquiv R (Cmd.seq c (Cmd.random y κ)) (Cmd.seq (Cmd.random y κ) c)

  /-- **[E-Defer-C]**: a mass-one draw of a block-local variable hoists out of a
      conditional whose guard does not read it and whose else-branch does not mention it,
      on states where the variable holds its default.  Needs `κ` of total mass one. -/
  | deferCond {t : Ty} (y : Vars ident t) {e : BExpr M}
      {c₁ c₂ : Cmd ident M}
      (κ : @ProbabilityTheory.Kernel M.heap t.interp M.heapMeas (Ty.measurableSpace t))
      [IsMarkovKernel κ] 
      (hind : IndepY y c₂)
      (heb : ∀ (h : M.heap) (w : t.interp), esem e (M.set h t y.name w) = esem e h) :
      CEquiv (fun s => resetV y s = s)
        (Cmd.cond e (Cmd.loc y (Cmd.seq (Cmd.random y κ) c₁)) c₂)
        (Cmd.loc y (Cmd.seq (Cmd.random y κ) (Cmd.cond e c₁ c₂)))

  /-- **[E-Merge]**. -/
  | fuseGen {tb t : Ty} (b : Vars ident tb) (x : Vars ident t)
      {R : St M → Prop} (hxb : x.name ≠ b.name)
      (κ : @ProbabilityTheory.Kernel M.heap tb.interp M.heapMeas (Ty.measurableSpace tb))
      [IsSubMarkovKernel κ]
      (S : @ProbabilityTheory.Kernel M.heap t.interp M.heapMeas (Ty.measurableSpace t))
      [IsSubMarkovKernel S] :
      CEquiv R
        (Cmd.loc b (Cmd.seq (Cmd.random b κ) (Cmd.random x S)))
        (Cmd.seq (Cmd.assign b (Expr.cst default)) (Cmd.random x (fuseK b κ S)))

  /-- **[E-Push]**. -/
  | pushGen {tb t : Ty} (b : Vars ident tb) (x : Vars ident t)
      {R : St M → Prop} (hxb : x.name ≠ b.name)
      (κ : @ProbabilityTheory.Kernel M.heap tb.interp M.heapMeas (Ty.measurableSpace tb))
      [IsSubMarkovKernel κ]
      (e : Expr M t)
      (κ' : @ProbabilityTheory.Kernel M.heap t.interp M.heapMeas (Ty.measurableSpace t))
      [IsSubMarkovKernel κ']
      (hκ' : ∀ h, κ' h = (κ h).map (fun v => esem e (M.set h tb b.name v))) :
      CEquiv R
        (Cmd.loc b (Cmd.seq (Cmd.random b κ) (Cmd.assign x e)))
        (Cmd.seq (Cmd.assign b (Expr.cst default)) (Cmd.random x κ'))

  /-- **[E-Comm]**. -/
  | swap {t u : Ty} (x : Vars ident t) (y : Vars ident u)
      {R : St M → Prop} (hxy : x.name ≠ y.name)
      (e : Expr M t)
      (hey : ∀ h w, esem e (M.set h u y.name w) = esem e h)
      (κ κ' : @ProbabilityTheory.Kernel M.heap u.interp M.heapMeas (Ty.measurableSpace u))
      [IsSubMarkovKernel κ] [IsSubMarkovKernel κ']
      (hκ' : ∀ h, κ' h = κ (M.set h t x.name (esem e h))) :
      CEquiv R (Cmd.seq (Cmd.assign x e) (Cmd.random y κ))
               (Cmd.seq (Cmd.random y κ') (Cmd.assign x e))

  /-- **[E-Cond-W]**, with the conditional expression as a parameter `e'`. -/
  | condAssign {t : Ty} (x : Vars ident t) {R : St M → Prop} (b : BExpr M)
      (e e' : Expr M t)
      (he' : ∀ m, esem e' m = if esem b m = true then esem e m else M.get m t x.name) :
      CEquiv R (Cmd.cond b (Cmd.assign x e) Cmd.skip) (Cmd.assign x e')

  /-- **[E-AA]**. -/
  | assignComp {t : Ty} (x : Vars ident t) {R : St M → Prop}
      (e₁ e₂ e₂' : Expr M t) 
      (he₂' : ∀ m, esem e₂' m = esem e₂ (M.set m t x.name (esem e₁ m))) :
      CEquiv R (Cmd.seq (Cmd.assign x e₁) (Cmd.assign x e₂)) (Cmd.assign x e₂')

  /-- **[E-AS]**: `x ≔ E ; x ←$ S  ≡  x ←$ S[E/x]`. -/
  | drawAfterAssign {t : Ty} (x : Vars ident t) {R : St M → Prop}
      (e : Expr M t)
      (κ κ' : @ProbabilityTheory.Kernel M.heap t.interp M.heapMeas (Ty.measurableSpace t))
      [IsSubMarkovKernel κ']
      [IsSubMarkovKernel κ]
      (hκ' : ∀ h, κ' h = κ (M.set h t x.name (esem e h))) :
      CEquiv R (Cmd.seq (Cmd.assign x e) (Cmd.random x κ)) (Cmd.random x κ')
  /-- **[E-SA]**: `x ←$ κ ; x ≔ E  ≡  x ←$ κ[E]`. -/
  | assignAfterDraw {t : Ty} (x : Vars ident t) {R : St M → Prop}
      (κ : @ProbabilityTheory.Kernel M.heap t.interp M.heapMeas (Ty.measurableSpace t))
      [IsSubMarkovKernel κ]
      (e : Expr M t)
      (κ' : @ProbabilityTheory.Kernel M.heap t.interp M.heapMeas (Ty.measurableSpace t))
      [IsSubMarkovKernel κ']
      (hκ' : ∀ h, κ' h = (κ h).map (fun v => esem e (M.set h t x.name v))) :
      CEquiv R (Cmd.seq (Cmd.random x κ) (Cmd.assign x e)) (Cmd.random x κ')
  /-- **[E-SS]**: `x ←$ κ₁ ; x ←$ κ₂  ≡  x ←$ (dlet v ← κ₁ in κ₂[v/x])`. -/
  | drawComp {t : Ty} (x : Vars ident t) {R : St M → Prop}
      (κ₁ κ₂ κ' : @ProbabilityTheory.Kernel M.heap t.interp M.heapMeas (Ty.measurableSpace t))
      [IsSubMarkovKernel κ']
      [IsSubMarkovKernel κ₁] [IsSubMarkovKernel κ₂]
      (hκ' : ∀ h, κ' h = (κ₁ h).bind (fun v => κ₂ (M.set h t x.name v))) :
      CEquiv R (Cmd.seq (Cmd.random x κ₁) (Cmd.random x κ₂)) (Cmd.random x κ')

@[inherit_doc CEquiv]
scoped notation:40 c " ≋{" R "} " c' => CEquiv R c c'

/-- **Theorem E.1 (soundness of the equivalence calculus)**: a derivable equivalence is an
    equality of the two programs' semantics on the states its restriction allows. -/
theorem CEquiv.sound {R : St M → Prop} {c c' : Cmd ident M} (h : CEquiv R c c') :
    ∀ s : St M, R s → osemA c s = osemA c' s := by
  induction h with
  | refl c => exact fun _ _ => rfl
  | symm _ ih => exact fun s hs => (ih s hs).symm
  | trans _ _ ih ih' => exact fun s hs => (ih s hs).trans (ih' s hs)
  | weaken hR _ ih => exact fun s hs => ih s (hR s hs)
  | congrSeq _ _ ih₁ ih₂ =>
      intro s hs
      show (osemA _ s).bind (osemA _) = (osemA _ s).bind (osemA _)
      rw [ih₁ s hs]
      exact Measure.bind_congr_right (Filter.Eventually.of_forall fun y => ih₂ y trivial)
  | congrSeqDet x e hR _ ih =>
      intro s hs
      show (osemA (Cmd.assign x e) s).bind (osemA _) = (osemA (Cmd.assign x e) s).bind (osemA _)
      rw [show osemA (Cmd.assign x e) s
            = Measure.dirac ((M.set s.1 _ x.name (esem e s.1), s.2) : St M) from rfl,
        Measure.dirac_bind (osemA_measurable _), Measure.dirac_bind (osemA_measurable _)]
      exact ih _ (hR s hs)
  | @congrCond R e c₁ c₁' c₂ c₂' _ _ ih₁ ih₂ =>
      intro s hs
      show (if esem e s.1 = true then osemA c₁ s else osemA c₂ s)
        = (if esem e s.1 = true then osemA c₁' s else osemA c₂' s)
      by_cases hg : esem e s.1 = true
      · rw [if_pos hg, if_pos hg]; exact ih₁ s ⟨hs, hg⟩
      · rw [if_neg hg, if_neg hg]
        exact ih₂ s ⟨hs, by simpa using hg⟩
  | congrLoc x hR _ ih =>
      intro s hs
      rw [osemA_loc x s, osemA_loc x s, ih (resetV x s) (hR s hs)]
  | ifFalse e c₁ c₂ hR =>
      intro s hs
      show (if esem e s.1 = true then osemA c₁ s else osemA c₂ s) = osemA c₂ s
      rw [if_neg (by simp [hR s hs])]
  | idleReset x hR =>
      intro s hs
      show Measure.dirac ((M.set s.1 _ x.name default, s.2) : St M) = Measure.dirac s
      rw [← hR s hs, M.set_get_eq]
  | unroll => exact fun s _ => osemA_while_unroll s
  | @count x n c hc k =>
      refine fun s hs => osemA_while_eq_iterCmd (ltW x n)
        (fun r a => M.get a .nat x.name + r = n) ?_ ?_ ?_ k s hs
      · intro a ha
        have ha' : (M.get a .nat x.name : ℕ) = n := ha
        show decide ((M.get a .nat x.name : ℕ) < n) = false
        simp [ha']
      · intro r a ha
        have ha' : (M.get a .nat x.name : ℕ) + (r + 1) = n := ha
        show decide ((M.get a .nat x.name : ℕ) < n) = true
        simp only [decide_eq_true_eq]
        exact ha' ▸ Nat.lt_add_of_pos_right (Nat.succ_pos r)
      · intro r s₀ hs₀
        refine (range_incLast x c hc s₀ _ rfl).mono fun s' h => ?_
        have h' : (M.get s'.1 .nat x.name : ℕ) = M.get s₀.1 .nat x.name + 1 := h
        have hs₀' : (M.get s₀.1 .nat x.name : ℕ) + (r + 1) = n := hs₀
        show (M.get s'.1 .nat x.name : ℕ) + r = n
        rw [h', ← hs₀', Nat.add_assoc, Nat.add_comm 1 r]
  | seqSkip c => exact fun s _ => osemA_seq_skip s
  | skipSeq => exact fun s _ => osemA_skip_seq s
  | seqAssoc => exact fun s _ => osemA_seq_assoc s
  | locDesugar x => exact fun s _ => osemA_loc_eq_reset x s
  | assignFrame y hind w => exact fun s _ => osemA_assign_frame y hind w s
  | defer y hκ hind => exact fun s _ => osemA_defer y hκ hind s
  | deferCond y κ hind heb =>
      exact fun s hs => osemA_defer_cond y κ hind heb s hs
  | fuseGen b x hxb κ S =>
      exact fun s _ => osemA_fuse_gen b x hxb κ S s
  | pushGen b x hxb κ e κ' hκ' =>
      exact fun s _ => osemA_push_gen b x hxb κ e κ' hκ' s
  | swap x y hxy e hey κ κ' hκ' =>
      exact fun s _ => osemA_swap x y hxy e hey κ κ' hκ' s
  | ghost y hic hic' hR _ ih =>
      exact fun s hs => osemA_ghost y hic hic' s
        (ih (resetV y s) ⟨hR s hs, M.get_set_eq _ _ _ _⟩)
  | leafAssign x e e' he => exact fun s hs => osemA_leaf_assign x e e' s (he s hs)
  | leafDraw x κ κ' hκ => exact fun s hs => osemA_leaf_random x κ κ' s (hκ s hs)
  | seqVals ys hR hnw _ ih =>
      exact fun s hs => osemA_seq_vals ys hR hnw ih s hs
  | condAssign x b e e' he' => exact fun s _ => osemA_cond_assign x b e e' he' s
  | assignComp x e₁ e₂ e₂' he₂' =>
      exact fun s _ => osemA_assign_comp x e₁ e₂ e₂' he₂' s
  | drawAfterAssign x e κ κ' hκ' => exact fun s _ => osemA_draw_after_assign x e κ κ' hκ' s
  | assignAfterDraw x κ e κ' hκ' =>
      exact fun s _ => osemA_assign_after_draw x κ e κ' hκ' s
  | drawComp x κ₁ κ₂ κ' hκ' => exact fun s _ => osemA_draw_comp x κ₁ κ₂ κ' hκ' s

/-! ### Sequencing helpers -/

/-- Congruence on the head of a sequence. -/
theorem CEquiv.congrHead {R : St M → Prop} {c₁ c₁' c₂ : Cmd ident M} (h : CEquiv R c₁ c₁') :
    CEquiv R (Cmd.seq c₁ c₂) (Cmd.seq c₁' c₂) :=
  CEquiv.congrSeq h (CEquiv.refl _)

/-- [E-Seq-V] at one variable. -/
theorem CEquiv.seqVal {t : Ty} (y : Vars ident t) {R : St M → Prop}
    {c₁ c₂ c₂' : Cmd ident M}
    (hR : ∀ s s' : St M, M.get s.1 t y.name = M.get s'.1 t y.name → R s → R s')
    (hnw : NoWrite y.name c₁) (h₂ : CEquiv R c₂ c₂') :
    CEquiv R (Cmd.seq c₁ c₂) (Cmd.seq c₁ c₂') :=
  CEquiv.seqVals [⟨t, y⟩]
    (fun s s' h hs => hR s s' (h ⟨t, y⟩ (by simp)) hs) 
    (fun z hz => by rw [List.mem_singleton] at hz; subst hz; exact hnw) h₂

/-- Congruence on the tail of a sequence. -/
theorem CEquiv.congrTail {R : St M → Prop} {c₁ c₂ c₂' : Cmd ident M}
    (h : CEquiv (fun _ => True) c₂ c₂') :
    CEquiv R (Cmd.seq c₁ c₂) (Cmd.seq c₁ c₂') :=
  CEquiv.congrSeq (CEquiv.refl _) h

/-- Congruence for `loc` with an unrestricted body premise. -/
theorem CEquiv.congrLocT {t : Ty} (x : Vars ident t) {R : St M → Prop} {c c' : Cmd ident M}
    (h : CEquiv (fun _ => True) c c') : CEquiv R (Cmd.loc x c) (Cmd.loc x c') :=
  CEquiv.congrLoc x (R' := fun _ => True) (fun _ _ => trivial) h

/-- [E-Assoc] read right to left. -/
theorem CEquiv.seqAssoc' {R : St M → Prop} {c₁ c₂ c₃ : Cmd ident M}
    :
    CEquiv R (Cmd.seq c₁ (Cmd.seq c₂ c₃)) (Cmd.seq (Cmd.seq c₁ c₂) c₃) :=
  (CEquiv.seqAssoc).symm

/-- [E-Frame] one statement deep: a constant store behind a command that ignores its
    variable floats to the front. -/
theorem CEquiv.frameRight {t₀ : Ty} (y : Vars ident t₀) {R : St M → Prop}
    {c c₃ : Cmd ident M} (hind : IndepY y c) (w : t₀.interp)
    :
    CEquiv R (Cmd.seq c (Cmd.seq (Cmd.assign y (Expr.cst w)) c₃))
      (Cmd.seq (Cmd.assign y (Expr.cst w)) (Cmd.seq c c₃)) :=
  (CEquiv.seqAssoc').trans <|
    (CEquiv.congrHead (CEquiv.assignFrame y hind w).symm).trans
      (CEquiv.seqAssoc)

/-! ### Block laws for a variable the body does not touch -/

/-- Two resets of one variable are one ([E-AA]). -/
theorem CEquiv.resetTwice {t : Ty} (x : Vars ident t) {R : St M → Prop} :
    CEquiv R (Cmd.seq (Cmd.assign x (Expr.cst (default : t.interp)))
        (Cmd.assign x (Expr.cst (default : t.interp))))
      (Cmd.assign x (Expr.cst (default : t.interp))) :=
  CEquiv.assignComp x _ _ _ (fun _ => rfl)

/-- **A block around a command that ignores its variable is the entry reset.** -/
theorem CEquiv.locDead {t : Ty} (x : Vars ident t) {R : St M → Prop}
    {c : Cmd ident M} (hind : IndepY x c) :
    CEquiv R (Cmd.loc x c) (Cmd.seq (Cmd.assign x (Expr.cst (default : t.interp))) c) :=
  (CEquiv.locDesugar x ).trans <|
    (CEquiv.congrTail (CEquiv.assignFrame x hind default).symm).trans <|
    (CEquiv.seqAssoc').trans (CEquiv.congrHead (CEquiv.resetTwice x))

/-- **Narrowing a block past a suffix** that ignores its variable. -/
theorem CEquiv.locNarrowRight {t : Ty} (x : Vars ident t) {R : St M → Prop}
    {c c₁ : Cmd ident M} (hind : IndepY x c₁) :
    CEquiv R (Cmd.loc x (Cmd.seq c c₁)) (Cmd.seq (Cmd.loc x c) c₁) :=
  (CEquiv.locDesugar x).trans <|
    (CEquiv.congrTail (CEquiv.seqAssoc)).trans <|
    (CEquiv.congrTail (CEquiv.congrTail
      (CEquiv.assignFrame x hind default).symm)).trans <|
    (CEquiv.congrTail (CEquiv.seqAssoc')).trans <|
    (CEquiv.seqAssoc' ).trans
      (CEquiv.congrHead (CEquiv.locDesugar x ).symm)

/-! ## Derived forms

### Scoping a reused draw variable

A block around a draw is the draw followed by one reset, the leading reset being absorbed
by the draw ([E-Loc-D], [E-AS]):

    local b in (b ←$ κ ; x ≔ e)   ≡   b ←$ κ ; x ≔ e ; b ≔ d_b

so a draw into a variable reused across iterations can be treated as block-local. -/

/-- **A block around a draw is the draw followed by one reset.** -/
theorem CEquiv.locDrawTail {tb : Ty} (b : Vars ident tb) {R : St M → Prop}
    (κ : @ProbabilityTheory.Kernel M.heap tb.interp M.heapMeas (Ty.measurableSpace tb))
    [IsSubMarkovKernel κ]
    (hκb : ∀ h w, κ (M.set h tb b.name w) = κ h)
    {c : Cmd ident M} :
    CEquiv R (Cmd.loc b (Cmd.seq (Cmd.random b κ) c))
      (Cmd.seq (Cmd.seq (Cmd.random b κ) c) (Cmd.assign b (Expr.cst default))) := by
  refine (CEquiv.locDesugar b (R := R)).trans ?_
  refine (CEquiv.congrTail (CEquiv.seqAssoc)).trans ?_
  refine (CEquiv.seqAssoc' (c₁ := Cmd.assign b (Expr.cst default)) (c₂ := Cmd.random b κ)
    (c₃ := Cmd.seq c (Cmd.assign b (Expr.cst default))) ).trans ?_
  -- [E-AS]: the leading reset is absorbed by the draw
  refine (CEquiv.congrHead (CEquiv.drawAfterAssign b (Expr.cst default) κ κ
    (fun h => (hκb h default).symm))).trans ?_
  exact (CEquiv.seqAssoc).symm

/-- A block around a draw-and-assign is the draw-and-assign followed by one reset. -/
theorem CEquiv.locDrawAssign {tb t : Ty} (b : Vars ident tb)
    (x : Vars ident t) {R : St M → Prop}
    (κ : @ProbabilityTheory.Kernel M.heap tb.interp M.heapMeas (Ty.measurableSpace tb))
    [IsSubMarkovKernel κ]
    (hκb : ∀ h w, κ (M.set h tb b.name w) = κ h)
    (e : Expr M t) :
    CEquiv R (Cmd.loc b (Cmd.seq (Cmd.random b κ) (Cmd.assign x e)))
      (Cmd.seq (Cmd.seq (Cmd.random b κ) (Cmd.assign x e))
        (Cmd.assign b (Expr.cst default))) :=
  CEquiv.locDrawTail b κ hκb

/-- A draw into a reused `b`, an assignment to `x` reading it, and a reset of `b` become a
    single draw into `x` ([E-Push] without a per-iteration block). -/
theorem CEquiv.drawAssignReset {tb t : Ty} (b : Vars ident tb)
    (x : Vars ident t) {R : St M → Prop} (hxb : x.name ≠ b.name)
    (κ : @ProbabilityTheory.Kernel M.heap tb.interp M.heapMeas (Ty.measurableSpace tb))
    [IsSubMarkovKernel κ]
    (hκb : ∀ h w, κ (M.set h tb b.name w) = κ h)
    (e : Expr M t)
    (κ' : @ProbabilityTheory.Kernel M.heap t.interp M.heapMeas (Ty.measurableSpace t))
    [IsSubMarkovKernel κ']
    (hκ' : ∀ h, κ' h = (κ h).map (fun v => esem e (M.set h tb b.name v))) :
    CEquiv R
      (Cmd.seq (Cmd.seq (Cmd.random b κ) (Cmd.assign x e)) (Cmd.assign b (Expr.cst default)))
      (Cmd.seq (Cmd.assign b (Expr.cst default)) (Cmd.random x κ')) :=
  (CEquiv.locDrawAssign b x κ hκb e).symm.trans
    (CEquiv.pushGen b x hxb κ e κ' hκ')

/-- **[E-Cond-W]** as displayed in Figure 10, with the expression `if b then e else x`. -/
theorem CEquiv.condAssignExpr {t : Ty} (x : Vars ident t) {R : St M → Prop}
    (b : BExpr M) (e : Expr M t) :
    CEquiv R (Cmd.cond b (Cmd.assign x e) Cmd.skip)
      (Cmd.assign x (Expr.ite b e (Expr.var x))) :=
  CEquiv.condAssign x b e (Expr.ite b e (Expr.var x)) (fun _ => rfl)

/-- `iterCmd c (a + b) ≡ iterCmd c a ; iterCmd c b`. -/
theorem CEquiv.iterCmd_add {c : Cmd ident M} :
    ∀ (a b : ℕ) (R : St M → Prop),
      CEquiv R (iterCmd c (a + b)) (Cmd.seq (iterCmd c a) (iterCmd c b))
  | 0, b, _ => by
      rw [Nat.zero_add]
      exact (CEquiv.skipSeq (c := iterCmd c b)).symm
  | a + 1, b, R => by
      rw [show a + 1 + b = (a + b) + 1 from by omega]
      show CEquiv R (Cmd.seq c (iterCmd c (a + b)))
        (Cmd.seq (Cmd.seq c (iterCmd c a)) (iterCmd c b))
      exact (CEquiv.congrSeq (CEquiv.refl c)
          (CEquiv.iterCmd_add a b (fun _ => True))).trans
        (CEquiv.seqAssoc).symm

/-- The three-way split of an unrolled loop. -/
theorem CEquiv.iterCmd_split {c : Cmd ident M} (a b d : ℕ)
    (R : St M → Prop) :
    CEquiv R (iterCmd c (a + (b + d)))
      (Cmd.seq (iterCmd c a) (Cmd.seq (iterCmd c b) (iterCmd c d))) :=
  (CEquiv.iterCmd_add a (b + d) R).trans
    (CEquiv.congrSeq (CEquiv.refl _) (CEquiv.iterCmd_add b d (fun _ => True)))

/-! ## Scope laws

Derived from [E-Loc-D], [E-Assoc], [E-Frame] and [E-AA] by flattening both sides into
reset-flanked sequences. -/

/-- **Narrowing**: a block narrows past a prefix that ignores its variable. -/
theorem CEquiv.locNarrow {t₀ : Ty} (y : Vars ident t₀) {R : St M → Prop}
    {c₀ c : Cmd ident M} (hind : IndepY y c₀) :
    CEquiv R (Cmd.loc y (Cmd.seq c₀ c)) (Cmd.seq c₀ (Cmd.loc y c)) :=
  (CEquiv.locDesugar y).trans <|
    (CEquiv.congrTail (CEquiv.seqAssoc)).trans <|
    (CEquiv.seqAssoc').trans <|
    (CEquiv.congrHead (CEquiv.assignFrame y hind default)).trans <|
    (CEquiv.seqAssoc).trans
      (CEquiv.congrTail (CEquiv.locDesugar y ).symm)

/-- **Dead final store**: the block's exit reset absorbs it ([E-AA]). -/
theorem CEquiv.locDeadStore {t : Ty} (x : Vars ident t) {R : St M → Prop}
    {c : Cmd ident M} {e : Expr M t} 
    :
    CEquiv R (Cmd.loc x (Cmd.seq c (Cmd.assign x e))) (Cmd.loc x c) :=
  (CEquiv.locDesugar x).trans <|
    (CEquiv.congrTail (CEquiv.seqAssoc)).trans <|
    (CEquiv.congrTail (CEquiv.congrTail
      (CEquiv.assignComp x e (Expr.cst default) (Expr.cst default)  (fun _ => rfl)))).trans
      (CEquiv.locDesugar x ).symm

/-- **Permutation of two blocks**: both sides flatten to the same statements, the resets
    commuting by [E-Frame]. -/
theorem CEquiv.locComm {t u : Ty} (x : Vars ident t)
    (z : Vars ident u) {R : St M → Prop} (hxz : x.name ≠ z.name) (c : Cmd ident M)
    :
    CEquiv R (Cmd.loc x (Cmd.loc z c)) (Cmd.loc z (Cmd.loc x c)) := by
  have hiZ : IndepY (M := M) z (Cmd.assign x (Expr.cst (default : t.interp))) :=
    ⟨hxz, fun _ _ => rfl⟩
  have hL : CEquiv R (Cmd.loc x (Cmd.loc z c))
      (Cmd.seq (Cmd.assign x (Expr.cst default))
        (Cmd.seq (Cmd.seq (Cmd.assign z (Expr.cst default))
          (Cmd.seq c (Cmd.assign z (Expr.cst default))))
          (Cmd.assign x (Expr.cst default)))) :=
    (CEquiv.locDesugar x).trans
      (CEquiv.congrTail (CEquiv.congrHead (CEquiv.locDesugar z )))
  have hRr : CEquiv R (Cmd.loc z (Cmd.loc x c))
      (Cmd.seq (Cmd.assign z (Expr.cst default))
        (Cmd.seq (Cmd.seq (Cmd.assign x (Expr.cst default))
          (Cmd.seq c (Cmd.assign x (Expr.cst default))))
          (Cmd.assign z (Expr.cst default)))) :=
    (CEquiv.locDesugar z).trans
      (CEquiv.congrTail (CEquiv.congrHead (CEquiv.locDesugar x )))
  refine hL.trans (CEquiv.trans ?_ hRr.symm)
  refine (CEquiv.congrTail (CEquiv.seqAssoc)).trans ?_
  refine (CEquiv.congrTail (CEquiv.congrTail (CEquiv.seqAssoc))).trans ?_
  refine (CEquiv.congrTail (CEquiv.congrTail (CEquiv.congrTail
    (CEquiv.assignFrame z hiZ default)))).trans ?_
  refine (CEquiv.frameRight z hiZ default ).trans ?_
  refine (CEquiv.congrTail (CEquiv.congrTail (CEquiv.seqAssoc'))).trans ?_
  exact CEquiv.congrTail (CEquiv.seqAssoc')

/-! ## Hoisting helpers -/

/-- **A vacuous block deletes**, where its variable holds its default. -/
theorem CEquiv.locVacuous {t : Ty} (x : Vars ident t) {R : St M → Prop}
    (hR : ∀ s, R s → M.get s.1 t x.name = default)
    (hRdet : ∀ s s' : St M, M.get s.1 t x.name = M.get s'.1 t x.name → R s → R s')
    {c : Cmd ident M} (hind : IndepY x c) :
    CEquiv R (Cmd.loc x c) c :=
  (CEquiv.locDesugar x ).trans <|
    (CEquiv.congrHead (CEquiv.idleReset x hR)).trans <|
    (CEquiv.skipSeq).trans <|
    (CEquiv.seqVals (M := M) [⟨t, x⟩]
      (fun s s' h hs => hRdet s s' (h ⟨t, x⟩ (by simp)) hs) 
      (fun z hz => by rw [List.mem_singleton] at hz; subst hz; exact noWrite_of_indepY x hind)
      (CEquiv.idleReset x hR)).trans (CEquiv.seqSkip c)

/-- **A constant-law draw floats to the front of its block** past an independent prefix. -/
theorem CEquiv.drawToFront {t : Ty} (b : Vars ident t) {R : St M → Prop}
    {κ : @ProbabilityTheory.Kernel M.heap t.interp M.heapMeas (Ty.measurableSpace t)}
    [IsSubMarkovKernel κ] {μ : Measure t.interp} (hκ : ∀ h, κ h = μ)
    {c₀ c : Cmd ident M} (hind : IndepY b c₀) :
    CEquiv R (Cmd.loc b (Cmd.seq c₀ (Cmd.seq (Cmd.random b κ) c)))
      (Cmd.loc b (Cmd.seq (Cmd.random b κ) (Cmd.seq c₀ c))) :=
  CEquiv.congrLocT b <|
    (CEquiv.seqAssoc').trans <|
    (CEquiv.congrHead (CEquiv.defer b hκ hind)).trans (CEquiv.seqAssoc)

/-- **A draw-headed block grows over an independent prefix**, keeping its draw first. -/
theorem CEquiv.hoistDraw {t : Ty} (b : Vars ident t) {R : St M → Prop}
    {κ : @ProbabilityTheory.Kernel M.heap t.interp M.heapMeas (Ty.measurableSpace t)}
    [IsSubMarkovKernel κ] {μ : Measure t.interp} (hκ : ∀ h, κ h = μ)
    {c₀ c : Cmd ident M} (hind : IndepY b c₀) :
    CEquiv R (Cmd.seq c₀ (Cmd.loc b (Cmd.seq (Cmd.random b κ) c)))
      (Cmd.loc b (Cmd.seq (Cmd.random b κ) (Cmd.seq c₀ c))) :=
  (CEquiv.locNarrow b hind).symm.trans
    (CEquiv.drawToFront b hκ hind )

/-- **A draw-headed block grows over an independent suffix.** -/
theorem CEquiv.extendBlockDraw {t : Ty} (b : Vars ident t) {R : St M → Prop}
    {κ : @ProbabilityTheory.Kernel M.heap t.interp M.heapMeas (Ty.measurableSpace t)}
    [IsSubMarkovKernel κ]
    {c c₁ : Cmd ident M} (hind : IndepY b c₁) :
    CEquiv R (Cmd.seq (Cmd.loc b (Cmd.seq (Cmd.random b κ) c)) c₁)
      (Cmd.loc b (Cmd.seq (Cmd.random b κ) (Cmd.seq c c₁))) :=
  (CEquiv.locNarrowRight b hind).symm.trans
    (CEquiv.congrLocT b (CEquiv.seqAssoc))

/-! ## Nested draw blocks

`nestDraws κ K gs body` is

    local g₀ in (g₀ ←$ κ ; local g₁ in (g₁ ←$ κ ; … ; body))

with `K` blocks drawing from the same constant-law kernel. -/

/-- `K` nested scratch blocks, each drawing before the next, `body` innermost. -/
def nestDraws {t : Ty}
    (κ : @ProbabilityTheory.Kernel M.heap t.interp M.heapMeas (Ty.measurableSpace t))
    [IsSubMarkovKernel κ] :
    (K : ℕ) → (Fin K → Vars ident t) → Cmd ident M → Cmd ident M
  | 0, _, body => body
  | K + 1, gs, body =>
      Cmd.loc (gs 0) (Cmd.seq (Cmd.random (gs 0) κ) (nestDraws κ K (Fin.tail gs) body))

/-- A nest of draws from a kernel blind to `y`, around a body independent of `y`, is
    independent of `y`. -/
lemma indepY_nestDraws {t ty : Ty} (y : Vars ident ty)
    {κ : @ProbabilityTheory.Kernel M.heap t.interp M.heapMeas (Ty.measurableSpace t)}
    [IsSubMarkovKernel κ]
    (hκy : ∀ (h : M.heap) (w : ty.interp), κ (M.set h ty y.name w) = κ h)
    {body : Cmd ident M} (hbody : IndepY y body) :
    ∀ (K : ℕ) (gs : Fin K → Vars ident t), (∀ l, (gs l).name ≠ y.name) →
      IndepY y (nestDraws κ K gs body)
  | 0, _, _ => hbody
  | K + 1, gs, hgy =>
    ⟨hgy 0, ⟨hgy 0, hκy⟩, indepY_nestDraws y hκy hbody K (Fin.tail gs) (fun l => hgy l.succ)⟩

/-- **A nest grows over an independent prefix**, draws staying in front. -/
theorem CEquiv.nestIn {t : Ty} {R : St M → Prop}
    {κ : @ProbabilityTheory.Kernel M.heap t.interp M.heapMeas (Ty.measurableSpace t)}
    [IsSubMarkovKernel κ] {μ : Measure t.interp} (hκ : ∀ h, κ h = μ)
    {c₀ body : Cmd ident M} :
    ∀ (K : ℕ) (gs : Fin K → Vars ident t), (∀ l, IndepY (gs l) c₀) →
      CEquiv R (Cmd.seq c₀ (nestDraws κ K gs body)) (nestDraws κ K gs (Cmd.seq c₀ body))
  | 0, _, _ => CEquiv.refl _
  | K + 1, gs, hind =>
      (CEquiv.hoistDraw (gs 0) hκ  (hind 0)).trans <|
        CEquiv.congrLocT (gs 0) <| CEquiv.congrTail <|
          CEquiv.nestIn hκ   K (Fin.tail gs) (fun l => hind l.succ)

/-- **A nest grows over an independent suffix.** -/
theorem CEquiv.nestOut {t : Ty} {R : St M → Prop}
    {κ : @ProbabilityTheory.Kernel M.heap t.interp M.heapMeas (Ty.measurableSpace t)}
    [IsSubMarkovKernel κ]
    {body c₁ : Cmd ident M} :
    ∀ (K : ℕ) (gs : Fin K → Vars ident t), (∀ l, IndepY (gs l) c₁) →
      CEquiv R (Cmd.seq (nestDraws κ K gs body) c₁) (nestDraws κ K gs (Cmd.seq body c₁))
  | 0, _, _ => CEquiv.refl _
  | K + 1, gs, hind =>
      (CEquiv.extendBlockDraw (gs 0) 
          (hind 0)).trans <|
        CEquiv.congrLocT (gs 0) <| CEquiv.congrTail <|
          CEquiv.nestOut   K (Fin.tail gs) (fun l => hind l.succ)

/-- **Congruence through a nest**, for a body rewrite valid at a restriction determined by
    variables the nest does not touch. -/
theorem CEquiv.congrNestDraws {t : Ty} {R : St M → Prop}
    {κ : @ProbabilityTheory.Kernel M.heap t.interp M.heapMeas (Ty.measurableSpace t)}
    [IsSubMarkovKernel κ]
    (ys : List ((t' : Ty) × Vars ident t'))
    (hR : ∀ s s' : St M,
      (∀ z ∈ ys, M.get s.1 z.1 z.2.name = M.get s'.1 z.1 z.2.name) → R s → R s')
    {body body' : Cmd ident M} (h : CEquiv R body body') :
    ∀ (K : ℕ) (gs : Fin K → Vars ident t),
      (∀ (l : Fin K), ∀ z ∈ ys, (gs l).name ≠ z.2.name) →
      CEquiv R (nestDraws κ K gs body) (nestDraws κ K gs body')
  | 0, _, _ => h
  | K + 1, gs, hfr => by
    refine CEquiv.congrLoc (gs 0) (R' := R) (fun s hs => ?_) ?_
    · exact hR s _ (fun z hz =>
        (M.get_set_ne t z.1 s.1 (gs 0).name z.2.name default
          (Or.inr (hfr 0 z hz))).symm) hs
    · exact CEquiv.seqVals ys hR
        (fun z hz => hfr 0 z hz)
        (CEquiv.congrNestDraws ys hR h K (Fin.tail gs) (fun l => hfr l.succ))

/-- **A block commutes out of a nest** that does not mention its variable. -/
theorem CEquiv.pullLocNest {t ty : Ty} {R : St M → Prop}
    {κ : @ProbabilityTheory.Kernel M.heap t.interp M.heapMeas (Ty.measurableSpace t)}
    [IsSubMarkovKernel κ] (y : Vars ident ty)
    (hκy : ∀ (h : M.heap) (w : ty.interp), κ (M.set h ty y.name w) = κ h)
    {body : Cmd ident M} :
    ∀ (K : ℕ) (gs : Fin K → Vars ident t), (∀ l, (gs l).name ≠ y.name) →
      CEquiv R (nestDraws κ K gs (Cmd.loc y body)) (Cmd.loc y (nestDraws κ K gs body))
  | 0, _, _ => CEquiv.refl _
  | K + 1, gs, hgy => by
    have hindY : IndepY y (Cmd.random (M := M) (gs 0) κ) :=
      ⟨hgy 0, hκy⟩
    refine (CEquiv.congrLocT (gs 0) (CEquiv.congrTail
      (CEquiv.pullLocNest y hκy K (Fin.tail gs) (fun l => hgy l.succ)))).trans ?_
    refine (CEquiv.congrLocT (gs 0)
      (CEquiv.locNarrow y hindY ).symm).trans ?_
    exact CEquiv.locComm (gs 0) y (hgy 0)
      (Cmd.seq (Cmd.random (gs 0) κ) (nestDraws κ K (Fin.tail gs) body))

/-- **Iterated [E-Ghost]** over a list of pairwise-distinct variables. -/
theorem CEquiv.ghosts {R : St M → Prop} {c c' : Cmd ident M}
    :
    ∀ (ys : List ((t : Ty) × Vars ident t)),
      ys.Pairwise (fun a b => a.2.name ≠ b.2.name) →
      (∀ z ∈ ys, IndepY z.2 c) → (∀ z ∈ ys, IndepY z.2 c') →
      (∀ z ∈ ys, ∀ s : St M, R s → R (resetV z.2 s)) →
      CEquiv (fun s => R s ∧ ∀ z ∈ ys, M.get s.1 z.1 z.2.name = default) c c' →
      CEquiv R c c'
  | [], _, _, _, _, h =>
      CEquiv.weaken (fun s hs => ⟨hs, fun z hz => absurd hz List.not_mem_nil⟩) h
  | z :: zs, hpw, hic, hic', hhR, h => by
    refine CEquiv.ghost z.2   (hic z List.mem_cons_self)
      (hic' z List.mem_cons_self) (hhR z List.mem_cons_self) ?_
    refine CEquiv.ghosts zs
      ((List.pairwise_cons.mp hpw).2)
      (fun z' hz' => hic z' (List.mem_cons_of_mem _ hz'))
      (fun z' hz' => hic' z' (List.mem_cons_of_mem _ hz'))
      (fun z' hz' s hs => ⟨hhR z' (List.mem_cons_of_mem _ hz') s hs.1, by
        show M.get (M.set s.1 z'.1 z'.2.name default) z.1 z.2.name = default
        rw [M.get_set_ne z'.1 z.1 s.1 z'.2.name z.2.name default
          (Or.inr ((List.pairwise_cons.mp hpw).1 z' hz').symm)]
        exact hs.2⟩) ?_
    exact CEquiv.weaken (fun s hs => ⟨hs.1.1, fun z'' hz'' => by
      rcases List.mem_cons.mp hz'' with rfl | hz''
      · exact hs.1.2
      · exact hs.2 z'' hz''⟩) h

/-! ## Dead leading store and naming a draw -/

/-- **A leading store to a block's own variable is dead** when the body does not mention
    the variable: `local x in (x ≔ E ; C) ≡ local x in C`. -/
theorem CEquiv.locStoreHead {t : Ty} (x : Vars ident t) {R : St M → Prop}
    {c : Cmd ident M} {e : Expr M t}
    (hind : IndepY x c) 
    (hex : ∀ m : M.heap, esem e (M.set m t x.name default) = esem e m) :
    CEquiv R (Cmd.loc x (Cmd.seq (Cmd.assign x e) c)) (Cmd.loc x c) := by
  refine ((CEquiv.locDesugar x ).trans ?_).trans (CEquiv.locDead x hind).symm
  refine (CEquiv.congrTail (CEquiv.seqAssoc)).trans ?_
  refine (CEquiv.seqAssoc').trans ?_
  refine (CEquiv.congrHead (CEquiv.assignComp x (Expr.cst default) e e 
    (fun m => (hex m).symm))).trans ?_
  refine (CEquiv.congrTail (CEquiv.assignFrame x hind default).symm).trans ?_
  refine (CEquiv.seqAssoc').trans ?_
  exact CEquiv.congrHead (CEquiv.assignComp x e (Expr.cst default) (Expr.cst default) 
    (fun _ => rfl))

/-- **Naming a draw**: `x ←$ κ ≡ local b in (b ←$ κ ; x ≔ b)` on the states where `b`
    holds its default ([E-Push] at the identity expression). -/
theorem CEquiv.nameDraw {t : Ty} (b x : Vars ident t) {R : St M → Prop}
    (hxb : x.name ≠ b.name)
    (κ : @ProbabilityTheory.Kernel M.heap t.interp M.heapMeas (Ty.measurableSpace t))
    [IsSubMarkovKernel κ] (hR : ∀ s : St M, R s → M.get s.1 t b.name = default) :
    CEquiv R (Cmd.loc b (Cmd.seq (Cmd.random b κ) (Cmd.assign x (Expr.var b))))
      (Cmd.random x κ) :=
  (CEquiv.pushGen b x hxb κ (Expr.var b) κ
      (fun h => by
        show κ h = (κ h).map (fun v => M.get (M.set h t b.name v) t b.name)
        rw [show (fun v : t.interp => M.get (M.set h t b.name v) t b.name) = id from
          funext fun v => M.get_set_eq t h b.name v, Measure.map_id])).trans <|
    (CEquiv.congrHead (CEquiv.idleReset b hR)).trans (CEquiv.skipSeq )

end Continuous
