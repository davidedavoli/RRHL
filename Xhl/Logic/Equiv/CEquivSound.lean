import Xhl.Language.SubMarkov
import Xhl.Logic.Equiv.Defer
import Xhl.Logic.Equiv.Local
import Xhl.Measures.Bind
import Xhl.Logic.Equiv.Unroll

open Continuous

/-!
# Semantic lemmas behind the equivalence calculus

The side-condition vocabulary of `CEquiv` (`setY`, `ExprIndep`, `IndepY`, `NoWriteL`) and
one `osemA` identity per equation and closure rule of Appendix C, which `CEquiv.sound`
(Theorem C.1, `Xhl/Logic/Equiv/CEquiv.lean`) assembles.  The frame law `osemA_setY` is the
basic independence fact; [E-Defer] (`osemA_defer`) and [E-Defer-C] (`osemA_defer_cond`) are
the identities with probabilistic content.
-/

open MeasureTheory ProbabilityTheory ENNReal Cmd

variable {ident : Type} {M : MemType ident}

namespace Continuous

variable {t₀ : Ty} (y : Vars ident t₀)

/-- Writing `y` on a memory with a transcript. -/
def setY (w : t₀.interp) (s : St M) : St M := (M.set s.1 t₀ y.name w, s.2)

lemma measurable_setY (w : t₀.interp) : Measurable (setY (M := M) y w) :=
  ((M.set_measurable y.name).comp (measurable_fst.prodMk measurable_const)).prodMk measurable_snd

lemma measurable_setY_right (s : St M) :
    Measurable (fun w : t₀.interp => setY (M := M) y w s) :=
  ((M.set_measurable y.name).comp (measurable_const.prodMk measurable_id)).prodMk
    measurable_const

/-! ## Memory laws -/

lemma set_set_same {t : Ty} (h : M.heap) (x : ident) (v w : t.interp) :
    M.set (M.set h t x v) t x w = M.set h t x w :=
  MemType.set_set_absorb M t h x v w

lemma set_comm_ne {t u : Ty} (h : M.heap) {x z : ident} (hxz : x ≠ z)
    (v : t.interp) (w : u.interp) :
    M.set (M.set h t x v) u z w = M.set (M.set h u z w) t x v :=
  MemType.set_set_comm M t u h x z (Or.inr hxz) v w

/-! ## Independence -/

/-- `e` does not read `y`: its value is unchanged by writing `y`. -/
def ExprIndep {t : Ty} (e : Expr M t) : Prop :=
  ∀ (h : M.heap) (w : t₀.interp), esem e (M.set h t₀ y.name w) = esem e h

lemma ExprIndep.var {t : Ty} (x : Vars ident t) (hx : x.name ≠ y.name) :
    ExprIndep y (Expr.var x : Expr M t) :=
  fun h w => M.get_set_ne _ _ h y.name x.name w (Or.inr (Ne.symm hx))

lemma ExprIndep.cst {t : Ty} (c : t.interp) : ExprIndep y (Expr.cst c : Expr M t) :=
  fun _ _ => rfl

/-- `c` neither reads nor writes `y`. -/
def IndepY : Cmd ident M → Prop
  | .abort => True
  | .skip => True
  | @Cmd.assign _ _ _ x e => x.name ≠ y.name ∧
      ∀ h w, esem e (M.set h t₀ y.name w) = esem e h
  | @Cmd.random _ _ _ x κ _ => x.name ≠ y.name ∧ ∀ h w, κ (M.set h t₀ y.name w) = κ h
  | .cond e c₁ c₂ => (∀ h w, esem e (M.set h t₀ y.name w) = esem e h) ∧ IndepY c₁ ∧ IndepY c₂
  | .seq c₁ c₂ => IndepY c₁ ∧ IndepY c₂
  | .while e c => (∀ h w, esem e (M.set h t₀ y.name w) = esem e h) ∧ IndepY c
  | .release e => ∀ h w, esem e (M.set h t₀ y.name w) = esem e h
  | @Cmd.loc _ _ _ x c => x.name ≠ y.name ∧ IndepY c

/-- Independence is stronger than not writing: `IndepY` forbids reads as well. -/
lemma noWrite_of_indepY : ∀ {c : Cmd ident M}, IndepY y c → NoWrite y.name c
  | .abort, _ => trivial
  | .skip, _ => trivial
  | .assign _ _, h => h.1
  | @Cmd.random _ _ _ _ _ _, h => h.1
  | .cond _ _ _, h => ⟨noWrite_of_indepY h.2.1, noWrite_of_indepY h.2.2⟩
  | .seq _ _, h => ⟨noWrite_of_indepY h.1, noWrite_of_indepY h.2⟩
  | .while _ b, h => noWrite_of_indepY (c := b) h.2
  | .release _, _ => trivial
  | .loc _ _, h => ⟨h.1, noWrite_of_indepY h.2⟩

/-- The image of a bind. -/
lemma map_bind_eqY {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure α) {f : α → Measure β} (hf : Measurable f) {g : β → γ} (hg : Measurable g) :
    (μ.bind f).map g = μ.bind (fun a => (f a).map g) := by
  ext A hA
  have hfg : Measurable (fun a => (f a).map g) := (Measure.measurable_map g hg).comp hf
  rw [Measure.map_apply hg hA, Measure.bind_apply (hg hA) hf.aemeasurable,
    Measure.bind_apply hA hfg.aemeasurable]
  refine lintegral_congr fun a => ?_
  rw [Measure.map_apply hg hA]

/-- **Frame**: a command independent of `y` commutes with writing `y`. -/
theorem osemA_setY : ∀ {c : Cmd ident M}, IndepY y c → ∀ (w : t₀.interp) (s : St M),
    osemA c (setY y w s) = (osemA c s).map (setY y w)
  | .abort, _, w, s => by
      show (0 : Measure (St M)) = (0 : Measure (St M)).map _
      rw [Measure.map_zero]
  | .skip, _, w, s => by
      show Measure.dirac (setY y w s) = (Measure.dirac s).map (setY y w)
      exact (Measure.map_dirac' (measurable_setY y w) s).symm
  | @Cmd.loc _ _ t x c, hy, w, s => by
      obtain ⟨hxy, hcy⟩ : x.name ≠ y.name ∧ IndepY y c := hy
      have hcomm : ∀ s' : St M, resetV x (setY y w s') = setY y w (resetV x s') := fun s' => by
        show ((M.set (M.set s'.1 t₀ y.name w) t x.name default, s'.2) : St M)
          = (M.set (M.set s'.1 t x.name default) t₀ y.name w, s'.2)
        rw [set_comm_ne _ (Ne.symm hxy)]
      show (osemA c (resetV x (setY y w s))).map (resetV x)
        = ((osemA c (resetV x s)).map (resetV x)).map (setY y w)
      rw [hcomm s, osemA_setY (c := c) hcy w (resetV x s),
        Measure.map_map (measurable_resetV x) (measurable_setY y w),
        Measure.map_map (measurable_setY y w) (measurable_resetV x),
        show ((resetV x) ∘ (setY y w) : St M → St M) = (setY y w) ∘ (resetV x) from
          funext hcomm]
  | @Cmd.assign _ _ t x e, hy, w, s => by
      obtain ⟨hxy, he⟩ : x.name ≠ y.name ∧ ∀ h w, esem e (M.set h t₀ y.name w) = esem e h := hy
      show Measure.dirac ((M.set (M.set s.1 t₀ y.name w) t x.name
          (esem e (M.set s.1 t₀ y.name w)), s.2) : St M)
        = (Measure.dirac ((M.set s.1 t x.name (esem e s.1), s.2) : St M)).map (setY y w)
      rw [Measure.map_dirac' (measurable_setY y w), he, set_comm_ne _ (Ne.symm hxy)]
      rfl
  | @Cmd.random _ _ t x κ _, hy, w, s => by
      obtain ⟨hxy, hκ⟩ : x.name ≠ y.name ∧ ∀ h w, κ (M.set h t₀ y.name w) = κ h := hy
      have hd : Measurable (fun v : t.interp => Measure.dirac ((M.set s.1 t x.name v, s.2) : St M)) :=
        Measure.measurable_dirac.comp (((M.set_measurable x.name).comp
          (measurable_const.prodMk measurable_id)).prodMk measurable_const)
      show (κ (M.set s.1 t₀ y.name w)).bind (fun v => Measure.dirac _)
        = ((κ s.1).bind (fun v => Measure.dirac ((M.set s.1 t x.name v, s.2) : St M))).map _
      rw [hκ, map_bind_eqY _ hd (measurable_setY y w)]
      congr 1; funext v
      show Measure.dirac ((M.set (M.set s.1 t₀ y.name w) t x.name v, s.2) : St M)
        = (Measure.dirac ((M.set s.1 t x.name v, s.2) : St M)).map (setY y w)
      rw [Measure.map_dirac' (measurable_setY y w), set_comm_ne _ (Ne.symm hxy)]
      rfl
  | .cond e c₁ c₂, hy, w, s => by
      obtain ⟨he, h₁, h₂⟩ : (∀ h w, esem e (M.set h t₀ y.name w) = esem e h) ∧ IndepY y c₁ ∧ IndepY y c₂ := hy
      show (if esem e (M.set s.1 t₀ y.name w) = true then osemA c₁ (setY y w s)
          else osemA c₂ (setY y w s))
        = (if esem e s.1 = true then osemA c₁ s else osemA c₂ s).map (setY y w)
      rw [he]
      split
      · exact osemA_setY h₁ w s
      · exact osemA_setY h₂ w s
  | .seq c₁ c₂, hy, w, s => by
      obtain ⟨h₁, h₂⟩ : IndepY y c₁ ∧ IndepY y c₂ := hy
      have hm₂ := osemA_measurable c₂
      show (osemA c₁ (setY y w s)).bind (osemA c₂) = ((osemA c₁ s).bind (osemA c₂)).map _
      rw [osemA_setY h₁ w s, bind_map_eq (measurable_setY y w) hm₂,
        map_bind_eqY _ hm₂ (measurable_setY y w)]
      congr 1; funext s'
      exact osemA_setY h₂ w s'
  | .while e c, hy, w, s => by
      obtain ⟨he, hb⟩ : (∀ h w, esem e (M.set h t₀ y.name w) = esem e h) ∧ IndepY y c := hy
      have hm := osemA_measurable c
      have hg : Measurable (esem e) := e.measurable
      have happ : ∀ n (s : St M), oubn (osemA c) (esem e) n (setY y w s)
          = (oubn (osemA c) (esem e) n s).map (setY y w) := by
        intro n
        induction n with
        | zero => intro s; simp [oubn]
        | succ n ih =>
          intro s
          show (if esem e (M.set s.1 t₀ y.name w) = true then
            (osemA c (setY y w s)).bind (oubn (osemA c) (esem e) n) else Measure.dirac (setY y w s))
          = (if esem e s.1 = true then (osemA c s).bind (oubn (osemA c) (esem e) n)
            else Measure.dirac s).map (setY y w)
          rw [he]
          split
          · rw [osemA_setY hb w s, bind_map_eq (measurable_setY y w) (oubn_measurable hm hg n),
              map_bind_eqY _ (oubn_measurable hm hg n) (measurable_setY y w)]
            congr 1; funext s'; exact ih s'
          · show Measure.dirac (setY y w s) = (Measure.dirac s).map (setY y w)
            exact (Measure.map_dirac' (measurable_setY y w) s).symm
      show (⨆ n, oubn (osemA c) (esem e) n (setY y w s))
        = (⨆ n, oubn (osemA c) (esem e) n s).map (setY y w)
      simp_rw [happ]
      have hmon : Monotone fun n => oubn (osemA c) (esem e) n s := oubn_monotone hm hg s
      have hmon' : Monotone fun n => (oubn (osemA c) (esem e) n s).map (setY y w) :=
        fun a b hab => Measure.map_mono (hmon hab) (measurable_setY y w)
      ext A hA
      rw [iSup_measure_apply hmon' hA, Measure.map_apply (measurable_setY y w) hA,
        iSup_measure_apply hmon (measurable_setY y w hA)]
      refine iSup_congr fun n => ?_
      rw [Measure.map_apply (measurable_setY y w) hA]
  | @Cmd.release _ _ t e, he, w, s => by
      show Measure.dirac
          ((M.set s.1 t₀ y.name w, s.2.snoc ⟨t, esem e (M.set s.1 t₀ y.name w)⟩) : St M)
        = (Measure.dirac ((s.1, s.2.snoc ⟨t, esem e s.1⟩) : St M)).map (setY y w)
      rw [Measure.map_dirac' (measurable_setY y w), he]
      rfl

/-- **[E-Frame]**: storing a constant into `y` commutes with any command that neither
    reads nor writes `y`. -/
theorem osemA_assign_frame {c : Cmd ident M} (hy : IndepY y c)
    (w : t₀.interp) (s : St M) :
    osemA (Cmd.seq (Cmd.assign y (Expr.cst w)) c) s
      = osemA (Cmd.seq c (Cmd.assign y (Expr.cst w))) s := by
  have hm := osemA_measurable c
  show (Measure.dirac (setY y w s)).bind (osemA c)
    = (osemA c s).bind (fun s' => Measure.dirac (setY y w s'))
  rw [Measure.dirac_bind hm, Measure.bind_dirac_eq_map _ (measurable_setY y w)]
  exact osemA_setY y hy w s

variable {Θ : Type*}

/-! ## Sequencing -/

/-- **[E-SeqSkip]**. -/
lemma osemA_seq_skip {c : Cmd ident M} (s : St M) :
    osemA (Cmd.seq c Cmd.skip) s = osemA c s := by
  show (osemA c s).bind Measure.dirac = osemA c s
  exact Measure.bind_dirac

/-- **[E-SkipSeq]**. -/
lemma osemA_skip_seq {c : Cmd ident M} (s : St M) :
    osemA (Cmd.seq Cmd.skip c) s = osemA c s := by
  show (Measure.dirac s).bind (osemA c) = osemA c s
  exact Measure.dirac_bind (osemA_measurable _) s

/-- **[E-Assoc]**. -/
lemma osemA_seq_assoc {c₁ c₂ c₃ : Cmd ident M} (s : St M) :
    osemA (Cmd.seq (Cmd.seq c₁ c₂) c₃) s = osemA (Cmd.seq c₁ (Cmd.seq c₂ c₃)) s := by
  show ((osemA c₁ s).bind (osemA c₂)).bind (osemA c₃)
    = (osemA c₁ s).bind (fun y => (osemA c₂ y).bind (osemA c₃))
  exact Measure.bind_bind (osemA_measurable _).aemeasurable
    (osemA_measurable _).aemeasurable

/-- **[E-Defer]**: a draw from a state-independent kernel commutes with a command that
    neither reads nor writes its target. -/
theorem osemA_defer {t₀ : Ty} (y : Vars ident t₀)
    {κ : @ProbabilityTheory.Kernel M.heap t₀.interp M.heapMeas (Ty.measurableSpace t₀)}
    [IsSubMarkovKernel κ]
    {μ : Measure t₀.interp} (hκ : ∀ h, κ h = μ)
    {c : Cmd ident M} (hind : IndepY y c) (s : St M) :
    osemA (Cmd.seq c (Cmd.random y κ)) s = osemA (Cmd.seq (Cmd.random y κ) c) s := by
  haveI : IsFiniteMeasure (osemA c s) := isFiniteMeasure_osemA _ s
  -- the law is the kernel's at the current memory, hence finite (κ is sub-Markov)
  haveI : IsFiniteMeasure μ := hκ s.1 ▸ inferInstance
  have hrnd : ∀ x : St M, osemA (Cmd.random y κ) x = μ.bind (fun v => Measure.dirac (setY y v x)) := by
    intro x
    show (κ x.1).bind (fun v => Measure.dirac ((M.set x.1 t₀ y.name v, x.2) : St M)) = _
    rw [hκ]
    rfl
  have hdm : Measurable (fun p : St M × t₀.interp => Measure.dirac (setY (M := M) y p.2 p.1)) :=
    Measure.measurable_dirac.comp (((M.set_measurable y.name).comp
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).prodMk
      (measurable_snd.comp measurable_fst))
  show (osemA c s).bind (osemA (Cmd.random y κ)) = (osemA (Cmd.random y κ) s).bind (osemA c)
  calc (osemA c s).bind (osemA (Cmd.random y κ))
      = (osemA c s).bind (fun x => μ.bind (fun v => Measure.dirac (setY y v x))) := by
        exact Measure.bind_congr_right (Filter.Eventually.of_forall fun x => hrnd x)
    _ = μ.bind (fun v => (osemA c s).bind (fun x => Measure.dirac (setY y v x))) :=
        Continuous.bind_comm_of_sFinite (osemA c s) μ
          (fun p : St M × t₀.interp => Measure.dirac (setY y p.2 p.1)) hdm
    _ = μ.bind (fun v => (osemA c s).map (setY y v)) := by
        refine congrArg _ (funext fun v => ?_)
        exact Measure.bind_dirac_eq_map _ (measurable_setY y v)
    _ = μ.bind (fun v => osemA c (setY y v s)) := by
        refine congrArg _ (funext fun v => ?_)
        exact (osemA_setY y hind v s).symm
    _ = (μ.bind (fun v => Measure.dirac (setY y v s))).bind (osemA c) := by
        have hm1 : Measurable (fun v : t₀.interp => Measure.dirac (setY (M := M) y v s)) :=
          Measure.measurable_dirac.comp (((M.set_measurable y.name).comp
            (measurable_const.prodMk measurable_id)).prodMk measurable_const)
        rw [Measure.bind_bind hm1.aemeasurable (osemA_measurable _).aemeasurable]
        refine congrArg _ (funext fun v => ?_)
        exact (Measure.dirac_bind (osemA_measurable _) _).symm
    _ = (osemA (Cmd.random y κ) s).bind (osemA c) := by rw [hrnd s]

/-- **[E-Merge]**, at states where `b` holds its default: two adjacent draws, the second
    kernel possibly reading the first's result, are one draw from `fuseK`. -/
theorem osemA_fuse {tb t : Ty} (b : Vars ident tb) (x : Vars ident t)
    (hxb : x.name ≠ b.name)
    (κ : @ProbabilityTheory.Kernel M.heap tb.interp M.heapMeas (Ty.measurableSpace tb))
    [IsSubMarkovKernel κ]
    (S : @ProbabilityTheory.Kernel M.heap t.interp M.heapMeas (Ty.measurableSpace t))
    [IsSubMarkovKernel S]
    (s : St M) (hs : M.set s.1 tb b.name default = s.1) :
    osemA (Cmd.loc b (Cmd.seq (Cmd.random b κ) (Cmd.random x S))) s
      = osemA (Cmd.random x (fuseK b κ S)) s := by
  have hres : resetV b s = s := Prod.ext hs rfl
  have hkey : ∀ (B : tb.interp) (v : t.interp),
      M.set (M.set (M.set s.1 tb b.name B) t x.name v) tb b.name default
        = M.set s.1 t x.name v := by
    intro B v
    rw [set_comm_ne _ hxb, set_set_same, hs]
  have hS := osemA_measurable (M := M) (Cmd.random x S)
  have hsetb : Measurable (fun B : tb.interp => ((M.set s.1 tb b.name B, s.2) : St M)) :=
    ((M.set_measurable b.name).comp (measurable_const.prodMk measurable_id)).prodMk
      measurable_const
  have hdb : Measurable (fun B : tb.interp =>
      Measure.dirac ((M.set s.1 tb b.name B, s.2) : St M)) :=
    Measure.measurable_dirac.comp hsetb
  have hdx : Measurable (fun v : t.interp =>
      Measure.dirac ((M.set s.1 t x.name v, s.2) : St M)) :=
    Measure.measurable_dirac.comp (((M.set_measurable x.name).comp
      (measurable_const.prodMk measurable_id)).prodMk measurable_const)
  rw [osemA_loc b s, hres]
  show ((osemA (Cmd.random b κ) s).bind (osemA (Cmd.random x S))).map (resetV b)
    = (fuseK b κ S s.1).bind (fun v => Measure.dirac ((M.set s.1 t x.name v, s.2) : St M))
  have h2 : (osemA (Cmd.random b κ) s).bind (osemA (Cmd.random x S))
      = (κ s.1).bind (fun B => osemA (Cmd.random x S) ((M.set s.1 tb b.name B, s.2) : St M)) := by
    show ((κ s.1).bind (fun B =>
        Measure.dirac ((M.set s.1 tb b.name B, s.2) : St M))).bind (osemA (Cmd.random x S)) = _
    rw [Measure.bind_bind hdb.aemeasurable hS.aemeasurable]
    exact congrArg _ (funext fun B => Measure.dirac_bind hS _)
  rw [h2, map_bind_eqY (f := fun B : tb.interp =>
      osemA (Cmd.random x S) ((M.set s.1 tb b.name B, s.2) : St M)) _
    (hS.comp hsetb) (measurable_resetV b), fuseK_apply b κ S s.1,
    Measure.bind_bind (f := fun B : tb.interp => S (M.set s.1 tb b.name B))
      (g := fun v : t.interp => Measure.dirac ((M.set s.1 t x.name v, s.2) : St M))
      ((Kernel.measurable S).comp ((M.set_measurable b.name).comp
        (measurable_const.prodMk measurable_id))).aemeasurable hdx.aemeasurable]
  refine congrArg _ (funext fun B => ?_)
  show (osemA (Cmd.random x S) ((M.set s.1 tb b.name B, s.2) : St M)).map (resetV b)
    = (S (M.set s.1 tb b.name B)).bind (fun v => Measure.dirac ((M.set s.1 t x.name v, s.2) : St M))
  have hdxB : Measurable (fun v : t.interp =>
      Measure.dirac ((M.set (M.set s.1 tb b.name B) t x.name v, s.2) : St M)) :=
    Measure.measurable_dirac.comp (((M.set_measurable x.name).comp
      (measurable_const.prodMk measurable_id)).prodMk measurable_const)
  show ((S (M.set s.1 tb b.name B)).bind (fun v =>
      Measure.dirac ((M.set (M.set s.1 tb b.name B) t x.name v, s.2) : St M))).map (resetV b) = _
  rw [map_bind_eqY _ hdxB (measurable_resetV b)]
  refine congrArg _ (funext fun v => ?_)
  rw [Measure.map_dirac' (measurable_resetV b)]
  show Measure.dirac ((M.set (M.set (M.set s.1 tb b.name B) t x.name v) tb b.name default,
      s.2) : St M) = _
  rw [hkey B v]

/-- **[E-Push]**, at states where `b` holds its default: a draw followed by a deterministic
    post-processing is a draw from the image kernel. -/
theorem osemA_push {tb t : Ty} (b : Vars ident tb) (x : Vars ident t)
    (hxb : x.name ≠ b.name)
    (κ : @ProbabilityTheory.Kernel M.heap tb.interp M.heapMeas (Ty.measurableSpace tb))
    [IsSubMarkovKernel κ]
    (e : Expr M t)
    (κ' : @ProbabilityTheory.Kernel M.heap t.interp M.heapMeas (Ty.measurableSpace t))
    [IsSubMarkovKernel κ']
    (hκ' : ∀ h, κ' h = (κ h).map (fun v => esem e (M.set h tb b.name v)))
    (s : St M) (hs : M.set s.1 tb b.name default = s.1) :
    osemA (Cmd.loc b (Cmd.seq (Cmd.random b κ) (Cmd.assign x e))) s
      = osemA (Cmd.random x κ') s := by
  have he : Measurable (esem e) := e.measurable
  have hres : resetV b s = s := Prod.ext hs rfl
  have hkey : ∀ (B : tb.interp),
      M.set (M.set (M.set s.1 tb b.name B) t x.name (esem e (M.set s.1 tb b.name B)))
        tb b.name default = M.set s.1 t x.name (esem e (M.set s.1 tb b.name B)) := by
    intro B
    rw [set_comm_ne _ hxb, set_set_same, hs]
  have hsetb : Measurable (fun B : tb.interp => ((M.set s.1 tb b.name B, s.2) : St M)) :=
    ((M.set_measurable b.name).comp (measurable_const.prodMk measurable_id)).prodMk
      measurable_const
  have hdb : Measurable (fun B : tb.interp =>
      Measure.dirac ((M.set s.1 tb b.name B, s.2) : St M)) :=
    Measure.measurable_dirac.comp hsetb
  have hA := osemA_measurable (M := M) (Cmd.assign x e)
  have hf : Measurable (fun B : tb.interp => esem e (M.set s.1 tb b.name B)) :=
    he.comp ((M.set_measurable b.name).comp (measurable_const.prodMk measurable_id))
  have hdx : Measurable (fun v : t.interp =>
      Measure.dirac ((M.set s.1 t x.name v, s.2) : St M)) :=
    Measure.measurable_dirac.comp (((M.set_measurable x.name).comp
      (measurable_const.prodMk measurable_id)).prodMk measurable_const)
  rw [osemA_loc b s, hres]
  have h2 : (osemA (Cmd.random b κ) s).bind (osemA (Cmd.assign x e))
      = (κ s.1).bind (fun B => osemA (Cmd.assign x e) ((M.set s.1 tb b.name B, s.2) : St M)) := by
    show ((κ s.1).bind (fun B =>
        Measure.dirac ((M.set s.1 tb b.name B, s.2) : St M))).bind (osemA (Cmd.assign x e)) = _
    rw [Measure.bind_bind hdb.aemeasurable hA.aemeasurable]
    exact congrArg _ (funext fun B => Measure.dirac_bind hA _)
  show ((osemA (Cmd.random b κ) s).bind (osemA (Cmd.assign x e))).map (resetV b)
    = (κ' s.1).bind (fun v => Measure.dirac ((M.set s.1 t x.name v, s.2) : St M))
  rw [h2, map_bind_eqY (f := fun B : tb.interp =>
      osemA (Cmd.assign x e) ((M.set s.1 tb b.name B, s.2) : St M)) _
    (hA.comp hsetb) (measurable_resetV b), hκ' s.1, bind_map_eq hf hdx]
  refine congrArg _ (funext fun B => ?_)
  show (Measure.dirac ((M.set (M.set s.1 tb b.name B) t x.name
      (esem e (M.set s.1 tb b.name B)), s.2) : St M)).map (resetV b) = _
  rw [Measure.map_dirac' (measurable_resetV b)]
  show Measure.dirac ((M.set (M.set (M.set s.1 tb b.name B) t x.name
      (esem e (M.set s.1 tb b.name B))) tb b.name default, s.2) : St M) = _
  rw [hkey B]

/-- **[E-Merge]** at every state:
    `local b in (b ←$ κ ; x ←$ S)  ≡  b := d_b ; x ←$ fuseK b κ S`, for `x ≠ b`. -/
theorem osemA_fuse_gen {tb t : Ty} (b : Vars ident tb) (x : Vars ident t)
    (hxb : x.name ≠ b.name)
    (κ : @ProbabilityTheory.Kernel M.heap tb.interp M.heapMeas (Ty.measurableSpace tb))
    [IsSubMarkovKernel κ]
    (S : @ProbabilityTheory.Kernel M.heap t.interp M.heapMeas (Ty.measurableSpace t))
    [IsSubMarkovKernel S]
    (s : St M) :
    osemA (Cmd.loc b (Cmd.seq (Cmd.random b κ) (Cmd.random x S))) s
      = osemA (Cmd.seq (Cmd.assign b (Expr.cst default))
          (Cmd.random x (fuseK b κ S))) s := by
  have hidem : resetV b (resetV b s) = resetV b s :=
    Prod.ext (set_set_same s.1 b.name default default) rfl
  have key := osemA_fuse b x hxb κ S (resetV b s) (congrArg Prod.fst hidem)
  rw [osemA_loc b (resetV b s), hidem] at key
  rw [osemA_loc b s, key]
  show _ = (Measure.dirac (resetV b s)).bind (osemA (Cmd.random x (fuseK b κ S)))
  rw [Measure.dirac_bind (osemA_measurable _)]

/-- **[E-Push]** at every state, the block's entry reset kept on the right. -/
theorem osemA_push_gen {tb t : Ty} (b : Vars ident tb) (x : Vars ident t)
    (hxb : x.name ≠ b.name)
    (κ : @ProbabilityTheory.Kernel M.heap tb.interp M.heapMeas (Ty.measurableSpace tb))
    [IsSubMarkovKernel κ]
    (e : Expr M t)
    (κ' : @ProbabilityTheory.Kernel M.heap t.interp M.heapMeas (Ty.measurableSpace t))
    [IsSubMarkovKernel κ']
    (hκ' : ∀ h, κ' h = (κ h).map (fun v => esem e (M.set h tb b.name v)))
    (s : St M) :
    osemA (Cmd.loc b (Cmd.seq (Cmd.random b κ) (Cmd.assign x e))) s
      = osemA (Cmd.seq (Cmd.assign b (Expr.cst default)) (Cmd.random x κ')) s := by
  have he : Measurable (esem e) := e.measurable
  have hidem : resetV b (resetV b s) = resetV b s :=
    Prod.ext (set_set_same s.1 b.name default default) rfl
  have key := osemA_push b x hxb κ e κ' hκ' (resetV b s) (congrArg Prod.fst hidem)
  rw [osemA_loc b (resetV b s), hidem] at key
  rw [osemA_loc b s, key]
  show _ = (Measure.dirac (resetV b s)).bind (osemA (Cmd.random x κ'))
  rw [Measure.dirac_bind (osemA_measurable _)]

/-- **[E-Comm]**: an assignment commutes with a draw whose kernel may read the assigned
    variable, by substituting the expression into the kernel. -/
theorem osemA_swap {t u : Ty} (x : Vars ident t) (y : Vars ident u)
    (hxy : x.name ≠ y.name) (e : Expr M t)
    (hey : ∀ h w, esem e (M.set h u y.name w) = esem e h)
    (κ κ' : @ProbabilityTheory.Kernel M.heap u.interp M.heapMeas (Ty.measurableSpace u))
    [IsSubMarkovKernel κ] [IsSubMarkovKernel κ']
    (hκ' : ∀ h, κ' h = κ (M.set h t x.name (esem e h))) (s : St M) :
    osemA (Cmd.seq (Cmd.assign x e) (Cmd.random y κ)) s
      = osemA (Cmd.seq (Cmd.random y κ') (Cmd.assign x e)) s := by
  have he : Measurable (esem e) := e.measurable
  have hkey : ∀ w : u.interp,
      M.set (M.set s.1 u y.name w) t x.name (esem e (M.set s.1 u y.name w))
        = M.set (M.set s.1 t x.name (esem e s.1)) u y.name w := by
    intro w
    rw [hey s.1 w, ← set_comm_ne _ hxy]
  have hR := osemA_measurable (M := M) (Cmd.random y κ)
  have hA := osemA_measurable (M := M) (Cmd.assign x e)
  have hdy : Measurable (fun w : u.interp =>
      Measure.dirac ((M.set s.1 u y.name w, s.2) : St M)) :=
    Measure.measurable_dirac.comp (((M.set_measurable y.name).comp
      (measurable_const.prodMk measurable_id)).prodMk measurable_const)
  show (osemA (Cmd.assign x e) s).bind (osemA (Cmd.random y κ))
    = (osemA (Cmd.random y κ') s).bind (osemA (Cmd.assign x e))
  have h1 : (osemA (Cmd.assign x e) s).bind (osemA (Cmd.random y κ))
      = osemA (Cmd.random y κ) ((M.set s.1 t x.name (esem e s.1), s.2) : St M) := by
    show (Measure.dirac ((M.set s.1 t x.name (esem e s.1), s.2) : St M)).bind
      (osemA (Cmd.random y κ)) = _
    exact Measure.dirac_bind hR _
  have h2 : (osemA (Cmd.random y κ') s).bind (osemA (Cmd.assign x e))
      = (κ' s.1).bind (fun w =>
          osemA (Cmd.assign x e) ((M.set s.1 u y.name w, s.2) : St M)) := by
    show ((κ' s.1).bind (fun w =>
        Measure.dirac ((M.set s.1 u y.name w, s.2) : St M))).bind (osemA (Cmd.assign x e)) = _
    rw [Measure.bind_bind hdy.aemeasurable hA.aemeasurable]
    exact congrArg _ (funext fun w => Measure.dirac_bind hA _)
  rw [h1, h2, hκ' s.1]
  show (κ (M.set s.1 t x.name (esem e s.1))).bind (fun w =>
      Measure.dirac ((M.set (M.set s.1 t x.name (esem e s.1)) u y.name w, s.2) : St M))
    = (κ (M.set s.1 t x.name (esem e s.1))).bind (fun w =>
      Measure.dirac ((M.set (M.set s.1 u y.name w) t x.name
        (esem e (M.set s.1 u y.name w)), s.2) : St M))
  exact congrArg _ (funext fun w => by rw [hkey w])

/-! ## Writes to one variable -/

/-- **[E-Cond-W]**: a conditional write is the write of a conditional expression, given by
    its defining equation `he'`. -/
theorem osemA_cond_assign {t : Ty} (x : Vars ident t) (b : BExpr M)
    (e e' : Expr M t)
    (he' : ∀ m, esem e' m = if esem b m = true then esem e m else M.get m t x.name)
    (s : St M) :
    osemA (Cmd.cond b (Cmd.assign x e) Cmd.skip) s = osemA (Cmd.assign x e') s := by
  show (if esem b s.1 = true then osemA (Cmd.assign x e) s else osemA Cmd.skip s)
    = Measure.dirac ((M.set s.1 t x.name (esem e' s.1), s.2) : St M)
  rw [he' s.1]
  by_cases hb : esem b s.1 = true
  · rw [if_pos hb, if_pos hb]
    rfl
  · rw [if_neg hb, if_neg hb, M.set_get_eq]
    rfl

/-- **[E-AA]**: `x ≔ E₁ ; x ≔ E₂  ≡  x ≔ E₂[E₁/x]`, the composed expression given by its
    defining equation. -/
theorem osemA_assign_comp {t : Ty} (x : Vars ident t)
    (e₁ e₂ e₂' : Expr M t)

    (he₂' : ∀ m, esem e₂' m = esem e₂ (M.set m t x.name (esem e₁ m)))
    (s : St M) :
    osemA (Cmd.seq (Cmd.assign x e₁) (Cmd.assign x e₂)) s = osemA (Cmd.assign x e₂') s := by
  show (osemA (Cmd.assign x e₁) s).bind (osemA (Cmd.assign x e₂)) = _
  rw [show osemA (Cmd.assign x e₁) s
        = Measure.dirac ((M.set s.1 t x.name (esem e₁ s.1), s.2) : St M) from rfl,
    Measure.dirac_bind (osemA_measurable _)]
  show Measure.dirac ((M.set (M.set s.1 t x.name (esem e₁ s.1)) t x.name
      (esem e₂ (M.set s.1 t x.name (esem e₁ s.1))), s.2) : St M) = _
  rw [set_set_same, ← he₂' s.1]
  rfl

/-- **[E-AS]**: `x ≔ E ; x ←$ S  ≡  x ←$ S[E/x]`. -/
theorem osemA_draw_after_assign {t : Ty} (x : Vars ident t)
    (e : Expr M t)
    (κ κ' : @ProbabilityTheory.Kernel M.heap t.interp M.heapMeas (Ty.measurableSpace t))
    [IsSubMarkovKernel κ']
    [IsSubMarkovKernel κ]
    (hκ' : ∀ h, κ' h = κ (M.set h t x.name (esem e h)))
    (s : St M) :
    osemA (Cmd.seq (Cmd.assign x e) (Cmd.random x κ)) s = osemA (Cmd.random x κ') s := by
  show (osemA (Cmd.assign x e) s).bind (osemA (Cmd.random x κ)) = _
  rw [show osemA (Cmd.assign x e) s
        = Measure.dirac ((M.set s.1 t x.name (esem e s.1), s.2) : St M) from rfl,
    Measure.dirac_bind (osemA_measurable _)]
  show (κ (M.set s.1 t x.name (esem e s.1))).bind
      (fun v => Measure.dirac ((M.set (M.set s.1 t x.name (esem e s.1)) t x.name v, s.2) : St M))
    = (κ' s.1).bind (fun v => Measure.dirac ((M.set s.1 t x.name v, s.2) : St M))
  rw [hκ' s.1]
  exact congrArg _ (funext fun v => by rw [set_set_same])

/-- **[E-SA]**: `x ←$ κ ; x ≔ E  ≡  x ←$ κ[E]`. -/
theorem osemA_assign_after_draw {t : Ty} (x : Vars ident t)
    (κ : @ProbabilityTheory.Kernel M.heap t.interp M.heapMeas (Ty.measurableSpace t))
    [IsSubMarkovKernel κ]
    (e : Expr M t)
    (κ' : @ProbabilityTheory.Kernel M.heap t.interp M.heapMeas (Ty.measurableSpace t))
    [IsSubMarkovKernel κ']
    (hκ' : ∀ h, κ' h = (κ h).map (fun v => esem e (M.set h t x.name v)))
    (s : St M) :
    osemA (Cmd.seq (Cmd.random x κ) (Cmd.assign x e)) s = osemA (Cmd.random x κ') s := by
  have he : Measurable (esem e) := e.measurable
  have hset : Measurable (fun v : t.interp => ((M.set s.1 t x.name v, s.2) : St M)) :=
    ((M.set_measurable x.name).comp (measurable_const.prodMk measurable_id)).prodMk
      measurable_const
  have hf : Measurable (fun v : t.interp => esem e (M.set s.1 t x.name v)) :=
    he.comp ((M.set_measurable x.name).comp (measurable_const.prodMk measurable_id))
  have hdir : Measurable (fun v : t.interp =>
      Measure.dirac ((M.set s.1 t x.name v, s.2) : St M)) :=
    Measure.measurable_dirac.comp hset
  show ((κ s.1).bind (fun v => Measure.dirac ((M.set s.1 t x.name v, s.2) : St M))).bind
      (osemA (Cmd.assign x e))
    = (κ' s.1).bind (fun v => Measure.dirac ((M.set s.1 t x.name v, s.2) : St M))
  rw [hκ' s.1, bind_map_eq hf hdir,
    Measure.bind_bind hdir.aemeasurable (osemA_measurable _).aemeasurable]
  refine congrArg _ (funext fun v => ?_)
  rw [Measure.dirac_bind (osemA_measurable _)]
  show Measure.dirac ((M.set (M.set s.1 t x.name v) t x.name
    (esem e (M.set s.1 t x.name v)), s.2) : St M) = _
  rw [set_set_same]

/-- **[E-SS]**: `x ←$ κ₁ ; x ←$ κ₂  ≡  x ←$ (dlet v ← κ₁ in κ₂[v/x])`. -/
theorem osemA_draw_comp {t : Ty} (x : Vars ident t)
    (κ₁ κ₂ κ' : @ProbabilityTheory.Kernel M.heap t.interp M.heapMeas (Ty.measurableSpace t))
    [IsSubMarkovKernel κ']
    [IsSubMarkovKernel κ₁] [IsSubMarkovKernel κ₂]
    (hκ' : ∀ h, κ' h = (κ₁ h).bind (fun v => κ₂ (M.set h t x.name v)))
    (s : St M) :
    osemA (Cmd.seq (Cmd.random x κ₁) (Cmd.random x κ₂)) s = osemA (Cmd.random x κ') s := by
  have hset : Measurable (fun v : t.interp => ((M.set s.1 t x.name v, s.2) : St M)) :=
    ((M.set_measurable x.name).comp (measurable_const.prodMk measurable_id)).prodMk
      measurable_const
  have hk₂ : Measurable (fun v : t.interp => κ₂ (M.set s.1 t x.name v)) :=
    κ₂.measurable.comp ((M.set_measurable x.name).comp (measurable_const.prodMk measurable_id))
  have hdir : Measurable (fun v : t.interp =>
      Measure.dirac ((M.set s.1 t x.name v, s.2) : St M)) :=
    Measure.measurable_dirac.comp hset
  show ((κ₁ s.1).bind (fun v => Measure.dirac ((M.set s.1 t x.name v, s.2) : St M))).bind
      (osemA (Cmd.random x κ₂))
    = (κ' s.1).bind (fun u => Measure.dirac ((M.set s.1 t x.name u, s.2) : St M))
  rw [hκ' s.1, Measure.bind_bind hdir.aemeasurable (osemA_measurable _).aemeasurable,
    Measure.bind_bind hk₂.aemeasurable hdir.aemeasurable]
  refine congrArg _ (funext fun v => ?_)
  rw [Measure.dirac_bind (osemA_measurable _)]
  show (κ₂ (M.set s.1 t x.name v)).bind
      (fun u => Measure.dirac ((M.set (M.set s.1 t x.name v) t x.name u, s.2) : St M)) = _
  exact congrArg _ (funext fun u => by rw [set_set_same])

/-! ## [E-Defer-C]

On the branch that would not have drawn, the right-hand side draws and discards; the two
laws agree because the kernel has total mass one. -/

/-- A draw followed by a command, as a bind over the kernel. -/
lemma osemA_random_seq_bind {t : Ty} (z : Vars ident t)
    (κ : @ProbabilityTheory.Kernel M.heap t.interp M.heapMeas (Ty.measurableSpace t))
    [IsSubMarkovKernel κ]
    {Q : Cmd ident M} (x : St M) :
    osemA (Cmd.seq (Cmd.random z κ) Q) x
      = (κ x.1).bind (fun w => osemA Q ((M.set x.1 t z.name w, x.2) : St M)) := by
  have hQm : Measurable (osemA Q) := osemA_measurable _
  have hd : Measurable (fun w : t.interp => ((M.set x.1 t z.name w, x.2) : St M)) :=
    ((M.set_measurable z.name).comp (measurable_const.prodMk measurable_id)).prodMk
      measurable_const
  show ((κ x.1).bind (fun w => Measure.dirac ((M.set x.1 t z.name w, x.2) : St M))).bind
      (osemA Q) = _
  rw [Measure.bind_dirac_eq_map _ hd, bind_map_eq hd hQm]

/-- **[E-Defer-C]**: a mass-one draw of a block-local variable hoists out of a conditional
    whose guard does not read it and whose else-branch does not mention it, on the states
    where the variable holds its default. -/
theorem osemA_defer_cond {e : BExpr M} {c₁ c₂ : Cmd ident M}
    (κ : @ProbabilityTheory.Kernel M.heap t₀.interp M.heapMeas (Ty.measurableSpace t₀))
    [IsMarkovKernel κ] 
    (hind : IndepY y c₂)
    (heb : ∀ (h : M.heap) (w : t₀.interp), esem e (M.set h t₀ y.name w) = esem e h)
    (s : St M) (hs : resetV y s = s) :
    osemA (Cmd.cond e (Cmd.loc y (Cmd.seq (Cmd.random y κ) c₁)) c₂) s
      = osemA (Cmd.loc y (Cmd.seq (Cmd.random y κ) (Cmd.cond e c₁ c₂))) s := by
  have he : Measurable (esem e) := e.measurable
  have hres : (setY y (default : t₀.interp) : St M → St M) = resetV y := rfl
  -- the guard is blind to `y`, so it reads the same at every drawn value
  have hgw : ∀ w : t₀.interp, esem e (setY y w s).1 = esem e s.1 := fun w => heb s.1 w
  -- the right-hand side, with the entry reset absorbed by `hs`
  have hrhs : osemA (Cmd.loc y (Cmd.seq (Cmd.random y κ) (Cmd.cond e c₁ c₂))) s
      = ((κ s.1).bind (fun w => osemA (Cmd.cond e c₁ c₂) (setY y w s))).map (resetV y) := by
    show (osemA (Cmd.seq (Cmd.random y κ) (Cmd.cond e c₁ c₂)) (resetV y s)).map
      (resetV y) = _
    rw [hs, osemA_random_seq_bind y κ s]
    rfl
  by_cases hg : esem e s.1 = true
  · -- the guard is true: both sides commit to `c₁` at every drawn value
    have hlhs : osemA (Cmd.cond e (Cmd.loc y (Cmd.seq (Cmd.random y κ) c₁)) c₂) s
        = ((κ s.1).bind (fun w => osemA c₁ (setY y w s))).map (resetV y) := by
      show (if esem e s.1 = true then
        osemA (Cmd.loc y (Cmd.seq (Cmd.random y κ) c₁)) s else osemA c₂ s) = _
      rw [if_pos hg]
      show (osemA (Cmd.seq (Cmd.random y κ) c₁) (resetV y s)).map (resetV y) = _
      rw [hs, osemA_random_seq_bind y κ s]
      rfl
    rw [hlhs, hrhs]
    refine congrArg _ (congrArg _ (funext fun w => ?_))
    show osemA c₁ (setY y w s) = if esem e (setY y w s).1 = true then _ else _
    rw [hgw w, if_pos hg]
  · -- the guard is false: the right-hand side draws and discards
    have hgf : esem e s.1 = false := by
      cases h : esem e s.1 with
      | false => rfl
      | true => exact absurd h hg
    have hlhs : osemA (Cmd.cond e (Cmd.loc y (Cmd.seq (Cmd.random y κ) c₁)) c₂) s
        = osemA c₂ s := by
      show (if esem e s.1 = true then
        osemA (Cmd.loc y (Cmd.seq (Cmd.random y κ) c₁)) s else osemA c₂ s) = _
      rw [hgf]; rfl
    -- `c₂` is blind to `y`, so resetting `y` after it changes nothing
    have hkeep : (osemA c₂ s).map (resetV y) = osemA c₂ s := by
      rw [← hres, ← osemA_setY y hind default s, hres, hs]
    have hinner : ∀ w : t₀.interp,
        (osemA (Cmd.cond e c₁ c₂) (setY y w s)).map (resetV y) = osemA c₂ s := by
      intro w
      have h1 : osemA (Cmd.cond e c₁ c₂) (setY y w s) = osemA c₂ (setY y w s) := by
        show (if esem e (setY y w s).1 = true then _ else _) = _
        simp only [hgw w, hgf, Bool.false_eq_true, if_false]
      rw [h1, osemA_setY y hind w s,
        Measure.map_map (measurable_resetV y) (measurable_setY y w),
        show (resetV (M := M) y ∘ setY y w) = resetV y from
          funext fun s' => Prod.ext (set_set_same _ _ _ _) rfl,
        hkeep]
    have hf : Measurable (fun w : t₀.interp => osemA (Cmd.cond e c₁ c₂) (setY y w s)) :=
      (osemA_measurable _).comp (measurable_setY_right y s)
    rw [hlhs, hrhs, map_bind_eqY (κ s.1) hf (measurable_resetV y),
      show (fun w : t₀.interp => (osemA (Cmd.cond e c₁ c₂) (setY y w s)).map (resetV y))
        = (fun _ : t₀.interp => osemA c₂ s) from funext hinner,
      Measure.bind_const, measure_univ, one_smul]

/-- **[E-Ghost]**: if two programs not mentioning `y` agree from the state with `y` reset,
    they agree from the original state (by the frame law `osemA_setY`). -/
theorem osemA_ghost {t : Ty} (y : Vars ident t) {c c' : Cmd ident M}
    (hic : IndepY y c) (hic' : IndepY y c')
    (s : St M) (h0 : osemA c (resetV y s) = osemA c' (resetV y s)) :
    osemA c s = osemA c' s := by
  have hset : setY (M := M) y (M.get s.1 t y.name) (resetV y s) = s := by
    refine Prod.ext ?_ rfl
    show M.set (M.set s.1 t y.name default) t y.name (M.get s.1 t y.name) = s.1
    rw [set_set_same, M.set_get_eq]
  calc osemA c s
      = osemA c (setY y (M.get s.1 t y.name) (resetV y s)) := by rw [hset]
    _ = (osemA c (resetV y s)).map (setY y (M.get s.1 t y.name)) :=
        osemA_setY y hic _ _
    _ = (osemA c' (resetV y s)).map (setY y (M.get s.1 t y.name)) := by rw [h0]
    _ = osemA c' (setY y (M.get s.1 t y.name) (resetV y s)) :=
        (osemA_setY y hic' _ _).symm
    _ = osemA c' s := by rw [hset]

/-! ## Leaves and restriction transport -/

/-- **[E-Leaf-A]**: only the value of the expression at `s` matters. -/
theorem osemA_leaf_assign {t : Ty} (x : Vars ident t) (e e' : Expr M t) (s : St M)
    (he : esem e' s.1 = esem e s.1) :
    osemA (Cmd.assign x e : Cmd ident M) s = osemA (Cmd.assign x e') s := by
  show Measure.dirac ((M.set s.1 t x.name (esem e s.1), s.2) : St M)
    = Measure.dirac ((M.set s.1 t x.name (esem e' s.1), s.2) : St M)
  rw [he]

/-- **[E-Leaf-S]**: only the measure the kernel takes at `s` matters. -/
theorem osemA_leaf_random {t : Ty} (x : Vars ident t)
    (κ κ' : @ProbabilityTheory.Kernel M.heap t.interp M.heapMeas (Ty.measurableSpace t))
    [IsSubMarkovKernel κ] [IsSubMarkovKernel κ']
    (s : St M) (hκ : κ' s.1 = κ s.1) :
    osemA (Cmd.random x κ : Cmd ident M) s = osemA (Cmd.random x κ') s := by
  show (κ s.1).bind (fun v => Measure.dirac ((M.set s.1 t x.name v, s.2) : St M))
    = (κ' s.1).bind (fun v => Measure.dirac ((M.set s.1 t x.name v, s.2) : St M))
  rw [hκ]

/-- `NoWrite` for every variable in a list — the side condition of `seqVals`. -/
def NoWriteL (ys : List ((t : Ty) × Vars ident t)) (c : Cmd ident M) : Prop :=
  ∀ z ∈ ys, NoWrite z.2.name c

/-- A command that does not write `z` keeps its value, almost surely. -/
lemma keepGet {t : Ty} (z : Vars ident t)
    {c : Cmd ident M} (hnw : NoWrite z.name c) (s : St M) :
    ∀ᵐ s' ∂(osemA c s), M.get s'.1 t z.name = M.get s.1 t z.name := by
  have h := range_frame (M := M) (t := t) z.name {M.get s.1 t z.name}
    ((M.get_measurable _ z.name) (measurableSet_singleton _)) c hnw s rfl
  rwa [range] at h

/-- The same for a finite list of variables: finitely many almost-sure facts intersect. -/
lemma keepGets (ys : List ((t : Ty) × Vars ident t))
    {c : Cmd ident M} (hnw : ∀ z ∈ ys, NoWrite z.2.name c) (s : St M) :
    ∀ᵐ s' ∂(osemA c s), ∀ z ∈ ys, M.get s'.1 z.1 z.2.name = M.get s.1 z.1 z.2.name := by
  induction ys with
  | nil => filter_upwards with s'; simp
  | cons z zs ih =>
      have h1 := keepGet z.2 (hnw z (by simp)) s
      have h2 := ih (fun w hw => hnw w (by simp [hw]))
      filter_upwards [h1, h2] with s' e1 e2 w hw
      rcases List.mem_cons.mp hw with rfl | hw'
      · exact e1
      · exact e2 w hw'

/-- **[E-Seq-V]**: a head that writes none of the variables `ys` the restriction depends
    on (`hR`) leaves it standing, so the tail may be replaced at `R`.  The head may read
    them. -/
theorem osemA_seq_vals {R : St M → Prop} (ys : List ((t : Ty) × Vars ident t))
    (hR : ∀ s s' : St M, (∀ z ∈ ys, M.get s.1 z.1 z.2.name = M.get s'.1 z.1 z.2.name) →
      R s → R s')
    {c₁ c₂ c₂' : Cmd ident M} (hnw : ∀ z ∈ ys, NoWrite z.2.name c₁)
    (h₂ : ∀ s' : St M, R s' → osemA c₂ s' = osemA c₂' s')
    (s : St M) (hs : R s) :
    osemA (Cmd.seq c₁ c₂) s = osemA (Cmd.seq c₁ c₂') s := by
  show (osemA c₁ s).bind (osemA c₂) = (osemA c₁ s).bind (osemA c₂')
  refine Measure.bind_congr_right ?_
  filter_upwards [keepGets ys hnw s] with s' hs'
  exact h₂ s' (hR s s' (fun z hz => (hs' z hz).symm) hs)

