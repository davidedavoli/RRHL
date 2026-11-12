import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.Probability.Kernel.MeasurableLIntegral
import Mathlib.Probability.Kernel.Composition.MapComap
import Xhl.Language.Syntax
import Xhl.Measures.Isup

/-!
# Semantics of expressions and commands

`esem` evaluates expressions. A transcript `Tr = ℕ × (ℕ → Val)` is the list of released
values, each tagged with its type (`Val = Σ t, t.interp`). The semantics `osemA` (paper
§4.1) sends a state `St M = M.heap × Tr` to a sub-probability measure on states, appending
released values to the transcript; `osem c m = osemA c (m, Tr.nil)`. `osemA_measurable`:
it is a measurable kernel. Loop laws are in `Xhl/Logic/Equiv/Unroll.lean`.
-/

namespace Continuous

open Classical MeasureTheory ProbabilityTheory Cmd

variable {ident : Type} {M : MemType ident}

private instance : MeasurableSpace M.heap := M.heapMeas

/-!
## Expression evaluation
-/

/-- Evaluate an expression in a given memory. -/
def esem {t : Ty} (e : Expr M t) (m : M.heap) : t.interp := e.toFun m

/-- `MemType.get_measurable` as a `fun_prop` lemma, for the quoter `e⟪…⟫`. -/
@[fun_prop]
lemma measurable_get (t : Ty) (x : ident) : Measurable (fun m : M.heap => M.get m t x) :=
  M.get_measurable t x

@[simp] lemma esem_mk {t : Ty} (f : M.heap → t.interp) (hf) (m : M.heap) :
    esem (⟨f, hf⟩ : Expr M t) m = f m := rfl

/-!
## Measurability of the memory operations
-/

/-- The heap update `M.set` is jointly measurable in (state, value). -/
lemma M_set_measurable {t : Ty} (x : ident) :
    Measurable (fun mv : M.heap × t.interp => M.set mv.1 t x mv.2) :=
  M.set_measurable x

/-- Writing a measurable value into a fixed variable is a measurable state
    transformation. -/
lemma measurable_set_var {t : Ty} (y : Vars ident t) {f : M.heap → t.interp}
    (hf : Measurable f) : Measurable (fun m : M.heap => M.set m t y.name (f m)) :=
  (M.set_measurable (t := t) y.name).comp (measurable_id.prodMk hf)

/-- The counter increment `x + 1`. -/
def incW (x : Vars ident .nat) : Expr M .nat :=
  ⟨fun m => M.get m .nat x.name + 1,
   (measurable_of_countable (fun a : ℕ => a + 1)).comp (M.get_measurable _ _)⟩

/-- The counter guard `x < K`, the guard of every counted loop. -/
def ltW (x : Vars ident .nat) (K : ℕ) : BExpr M :=
  ⟨fun m => decide (M.get m .nat x.name < K),
   (measurable_of_countable (fun a : ℕ => decide (a < K))).comp (M.get_measurable _ _)⟩

/-! ## Syntactic unrolling -/

/-- Syntactic `k`-fold unrolling of a while loop: the loop replaced by `k` nested
    conditionals, with `abort` past the last one.  Its semantics is the `k`-th approximant
    of the loop (`osemA_unrollWhile`). -/
def unrollWhile (e : BExpr M) (c : Cmd ident M) : ℕ → Cmd ident M
  | 0 => Cmd.abort
  | k + 1 => Cmd.cond e (Cmd.seq c (unrollWhile e c k)) Cmd.skip

/-! ## Transcripts -/

/-- A released value: a type of the language with a value of it (the paper's `Val`),
    under the sum σ-algebra. -/
def Val : Type := Σ t : Ty, t.interp

instance : MeasurableSpace Val := Sigma.instMeasurableSpace
instance : Inhabited Val := ⟨⟨.nat, 0⟩⟩

/-- Tagging a value with its type is measurable. -/
lemma measurable_sigmaMk (t : Ty) : Measurable (fun v : t.interp => (⟨t, v⟩ : Val)) :=
  fun s hs => @iInf_le (MeasurableSpace Val) Ty _
    (fun t => (Ty.measurableSpace t).map (Sigma.mk t)) t s hs

/-- Transcripts: a length and the released values. -/
abbrev Tr : Type := ℕ × (ℕ → Val)

/-- The empty transcript. -/
def Tr.nil : Tr := (0, fun _ => default)

/-- Append one released value. -/
def Tr.snoc (s : Tr) (v : Val) : Tr := (s.1 + 1, fun i => if i = s.1 then v else s.2 i)

/-- States of the semantics: a memory and the transcript so far. -/
abbrev St (M : MemType ident) : Type := M.heap × Tr

lemma measurable_snoc : Measurable (fun p : Tr × Val => Tr.snoc p.1 p.2) := by
  refine Measurable.prodMk ((measurable_of_countable (fun n : ℕ => n + 1)).comp
    (measurable_fst.comp measurable_fst)) (measurable_pi_lambda _ fun i => ?_)
  exact Measurable.ite
    (measurableSet_eq_fun measurable_const (measurable_fst.comp measurable_fst))
    measurable_snd ((measurable_pi_apply i).comp (measurable_snd.comp measurable_fst))

/-- Resetting a variable to the default value of its type, on states with a transcript. -/
lemma measurable_resetS {u : Ty} (x : Vars ident u) :
    Measurable (fun s : M.heap × Tr => (M.set s.1 u x.name default, s.2)) :=
  ((M.set_measurable x.name).comp (measurable_fst.prodMk measurable_const)).prodMk measurable_snd

/-! ## The semantics -/

/-- `n`-step approximants of a loop, on memories with transcripts. -/
noncomputable def oubn (f : M.heap × Tr → Measure (M.heap × Tr)) (g : M.heap → Bool) :
    ℕ → M.heap × Tr → Measure (M.heap × Tr)
  | 0, _ => 0
  | n + 1, s => if g s.1 then (f s).bind (oubn f g n) else Measure.dirac s

/-- The semantics of commands, from a memory and the transcript so far:

    - `abort`   → the zero measure (diverge / probability 0)
    - `skip`    → Dirac delta at the input state
    - `assign`  → Dirac delta at the updated state
    - `random`  → sample from kernel κ, update the memory
    - `cond`    → conditional on the Boolean expression
    - `seq`     → monadic bind (sequential composition)
    - `while`   → supremum of the n-step approximants
    - `release` → append the released value, tagged with its type, to the transcript
    - `loc`     → run with the variable reset, reset it again on exit -/
noncomputable def osemA (c : Cmd ident M) (s : M.heap × Tr) : Measure (M.heap × Tr) :=
  match c with
  | .abort => 0
  | .skip => Measure.dirac s
  | .assign x e => Measure.dirac (M.set s.1 _ x.name (esem e s.1), s.2)
  | @Cmd.random _ _ _ x κ _ => (κ s.1).bind (fun v => Measure.dirac (M.set s.1 _ x.name v, s.2))
  | .cond e c1 c2 => if esem e s.1 then osemA c1 s else osemA c2 s
  | .seq c1 c2 => (osemA c1 s).bind (osemA c2)
  | .while e c => ⨆ n, oubn (osemA c) (esem e) n s
  | @Cmd.release _ _ t e => Measure.dirac (s.1, s.2.snoc ⟨t, esem e s.1⟩)
  | @Cmd.loc _ _ u x c =>
      (osemA c (M.set s.1 u x.name default, s.2)).map (fun s' => (M.set s'.1 u x.name default, s'.2))

/-- The semantics from the empty transcript. -/
noncomputable def osem (c : Cmd ident M) (m : M.heap) : Measure (M.heap × Tr) :=
  osemA c (m, Tr.nil)

/-! ## Unfolding lemmas -/

lemma osemA_abort (s : St M) :
    osemA (M := M) .abort s = 0 := rfl

lemma osemA_skip (s : St M) :
    osemA (M := M) .skip s = Measure.dirac s := rfl

lemma osemA_assign {t : Ty} (x : Vars ident t) (e : Expr M t)
    (s : St M) :
    osemA (.assign x e) s = Measure.dirac (M.set s.1 t x.name (esem e s.1), s.2) := rfl

lemma osemA_random {t : Ty} (x : Vars ident t)
    (κ : @ProbabilityTheory.Kernel M.heap t.interp M.heapMeas (Ty.measurableSpace t))
    [IsSubMarkovKernel κ] (s : St M) :
    osemA (.random x κ) s =
      (κ s.1).bind (fun v => Measure.dirac (M.set s.1 t x.name v, s.2)) := rfl

lemma osemA_cond (e : BExpr M) (c1 c2 : Cmd ident M) (s : St M) :
    osemA (.cond e c1 c2) s = if esem e s.1 then osemA c1 s else osemA c2 s := rfl

lemma osemA_seq (c1 c2 : Cmd ident M) (s : St M) :
    osemA (.seq c1 c2) s = (osemA c1 s).bind (osemA c2) := rfl

lemma osemA_while (e : BExpr M) (c : Cmd ident M) (s : St M) :
    osemA (.while e c) s = ⨆ n, oubn (osemA c) (esem e) n s := rfl

lemma osemA_release {t : Ty} (e : Expr M t) (s : St M) :
    osemA (.release e) s = Measure.dirac (s.1, s.2.snoc ⟨t, esem e s.1⟩) := rfl

/-! ## Measurability -/

section Meas

variable {f : M.heap × Tr → Measure (M.heap × Tr)} {g : M.heap → Bool}

lemma oubn_measurable (hf : Measurable f) (hg : Measurable g) (n : ℕ) :
    Measurable (oubn f g n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    simp only [oubn]
    exact Measurable.ite ((hg.comp measurable_fst)
      (show MeasurableSet ({true} : Set Bool) from MeasurableSet.of_discrete))
      ((Measure.measurable_bind' ih).comp hf) Measure.measurable_dirac

lemma oubn_mono (hf : Measurable f) (hg : Measurable g) (s : M.heap × Tr) (n : ℕ) :
    oubn f g n s ≤ oubn f g (n + 1) s := by
  induction n generalizing s with
  | zero => exact bot_le
  | succ n ih =>
    simp only [oubn]
    split_ifs with h
    · show (f s).bind (oubn f g n) ≤ (f s).bind (oubn f g (n + 1))
      rw [Measure.le_iff]
      intro A hA
      rw [Measure.bind_apply hA (oubn_measurable hf hg n).aemeasurable,
        Measure.bind_apply hA (oubn_measurable hf hg (n + 1)).aemeasurable]
      exact lintegral_mono fun b => ih b A
    · exact le_refl _

lemma oubn_monotone (hf : Measurable f) (hg : Measurable g) (s : M.heap × Tr) :
    Monotone (fun n => oubn f g n s) :=
  monotone_nat_of_le_succ (oubn_mono hf hg s)

end Meas

theorem osemA_measurable (c : Cmd ident M) : Measurable (osemA c) := by
  induction c with
  | abort => exact measurable_const
  | skip => exact Measure.measurable_dirac
  | assign x e =>
    exact Measure.measurable_dirac.comp
      (((measurable_set_var x e.measurable).comp measurable_fst).prodMk measurable_snd)
  | @random t x κ _ =>
    apply Measure.measurable_of_measurable_coe
    intro A hA
    have hG : Measurable (fun q : (M.heap × Tr) × t.interp => (M.set q.1.1 t x.name q.2, q.1.2)) :=
      ((M.set_measurable x.name).comp ((measurable_fst.comp measurable_fst).prodMk
        measurable_snd)).prodMk (measurable_snd.comp measurable_fst)
    have key : ∀ s : M.heap × Tr, osemA (.random x κ) s A
        = ∫⁻ v, Measure.dirac (M.set s.1 _ x.name v, s.2) A ∂(κ s.1) := fun s => by
      show ((κ s.1).bind (fun v => Measure.dirac (M.set s.1 _ x.name v, s.2))) A = _
      exact Measure.bind_apply hA
        (Measure.measurable_dirac.comp (hG.comp measurable_prodMk_left)).aemeasurable
    simp_rw [key]
    exact Measurable.lintegral_kernel_prod_right (κ := κ.comap Prod.fst measurable_fst)
      ((Measure.measurable_coe hA).comp (Measure.measurable_dirac.comp hG))
  | cond e c1 c2 ih1 ih2 =>
    exact Measurable.ite ((e.measurable.comp measurable_fst)
      (show MeasurableSet ({true} : Set Bool) from MeasurableSet.of_discrete)) ih1 ih2
  | seq c1 c2 ih1 ih2 => exact (Measure.measurable_bind' ih2).comp ih1
  | «while» e c ih =>
    apply Measure.measurable_of_measurable_coe
    intro A hA
    have key : ∀ s, osemA (.while e c) s A = ⨆ n, oubn (osemA c) (esem e) n s A := fun s =>
      iSup_measure_apply (oubn_monotone ih e.measurable s) hA
    simp_rw [key]
    exact Measurable.iSup fun n =>
      (Measure.measurable_coe hA).comp (oubn_measurable ih e.measurable n)
  | @release t e =>
    exact Measure.measurable_dirac.comp (measurable_fst.prodMk
      (measurable_snoc.comp (measurable_snd.prodMk ((measurable_sigmaMk t).comp
        (e.measurable.comp measurable_fst)))))
  | @loc u x c ih =>
    exact (Measure.measurable_map _ (measurable_resetS x)).comp
      (ih.comp (measurable_resetS x))

/-! ## Generic facts about `map` and `bind` -/

section Marginal

variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

lemma map_bind_eq (μ : Measure α) {K : α → Measure β} (hK : Measurable K) {f : β → γ}
    (hf : Measurable f) : (μ.bind K).map f = μ.bind (fun a => (K a).map f) := by
  ext A hA
  rw [Measure.map_apply hf hA, Measure.bind_apply (hf hA) hK.aemeasurable,
    Measure.bind_apply hA (show AEMeasurable (fun a => (K a).map f) μ from
      ((Measure.measurable_map f hf).comp hK).aemeasurable)]
  refine lintegral_congr fun a => ?_
  rw [Measure.map_apply hf hA]

lemma bind_comp_eq (μ : Measure α) {f : α → β} (hf : Measurable f) {g : β → Measure γ}
    (hg : Measurable g) : μ.bind (fun a => g (f a)) = (μ.map f).bind g := by
  ext A hA
  rw [Measure.bind_apply hA (show AEMeasurable (fun a => g (f a)) μ from
      (hg.comp hf).aemeasurable), Measure.bind_apply hA hg.aemeasurable]
  exact (lintegral_map (f := fun b => g b A) ((Measure.measurable_coe hA).comp hg) hf).symm

end Marginal

end Continuous
