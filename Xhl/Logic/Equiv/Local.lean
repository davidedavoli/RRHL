import Xhl.Logic.Rrhl.Equiv
import Xhl.Language.MemLaws

open Continuous

/-!
# Local variables

`loc x c` is `local x in c` (`Cmd.loc`): run `c` with `x` set to the default of its type,
and reset `x` to that default on exit.

* `osemA_loc` — the semantics of a block (the primitive clause of `osemA`).
* `locReset`, `osemA_loc_eq_reset` — the desugaring `x := dₓ ; (c ; x := dₓ)` and its
  equality with the block ([E-Loc-D]); **[Local]** (`TDeriv.loc`) is derived from it.
* `fuseK` — the kernel of [E-Merge]: a draw into `b` followed by a sampling that reads it.
-/

open MeasureTheory ProbabilityTheory ENNReal Cmd

variable {ident : Type} {M : MemType ident}

namespace Continuous

/-- `local x in c` — the primitive block statement of the language. -/
abbrev loc {t : Ty} (x : Vars ident t) (c : Cmd ident M) : Cmd ident M := Cmd.loc x c

/-- The desugaring of a block: reset `x`, run `c`, reset `x` again. -/
noncomputable def locReset {t : Ty} (x : Vars ident t) (c : Cmd ident M) : Cmd ident M :=
  Cmd.seq (Cmd.assign x (Expr.cst default)) (Cmd.seq c (Cmd.assign x (Expr.cst default)))

/-- Reset a variable to the default value of its type. -/
def resetV {t : Ty} (x : Vars ident t) (s : St M) : St M :=
  (M.set s.1 t x.name default, s.2)

lemma measurable_resetV {t : Ty} (x : Vars ident t) : Measurable (resetV (M := M) x) :=
  ((M.set_measurable x.name).comp (measurable_fst.prodMk measurable_const)).prodMk
    measurable_snd

/-- **The semantics of a block**: the primitive clause, with no side condition. -/
lemma osemA_loc {t : Ty} (x : Vars ident t) {c : Cmd ident M} (s : St M) :
    osemA (loc x c) s = (osemA c (resetV x s)).map (resetV x) := rfl

/-- The semantics of the desugaring. -/
lemma osemA_locReset {t : Ty} (x : Vars ident t) {c : Cmd ident M} 
    (s : St M) : osemA (locReset x c) s = (osemA c (resetV x s)).map (resetV x) := by
  have hd : Measurable (fun b : St M => Measure.dirac (resetV x b)) :=
    Measure.measurable_dirac.comp (measurable_resetV x)
  show (Measure.dirac (resetV x s)).bind
      (fun a => (osemA c a).bind (fun b => Measure.dirac (resetV x b))) = _
  have hm : Measurable (fun a : St M =>
      (osemA c a).bind (fun b => Measure.dirac (resetV x b))) :=
    (Measure.measurable_bind' hd).comp (osemA_measurable _)
  rw [Measure.dirac_bind hm, Measure.bind_dirac_eq_map _ (measurable_resetV x)]

/-- **[E-Loc-D]**: the block and its desugaring have the same semantics. -/
lemma osemA_loc_eq_reset {t : Ty} (x : Vars ident t) {c : Cmd ident M} 
    (s : St M) : osemA (loc x c) s = osemA (locReset x c) s := by
  rw [osemA_loc x s, osemA_locReset x s]

/-! ## Fusion -/

/-- The sampler obtained by fusing a draw into `b` with a sampler that reads `b`. -/
noncomputable def fuseK {tb t : Ty} (b : Vars ident tb)
    (κ : @ProbabilityTheory.Kernel M.heap tb.interp M.heapMeas (Ty.measurableSpace tb))
    (S : @ProbabilityTheory.Kernel M.heap t.interp M.heapMeas (Ty.measurableSpace t)) :
    @ProbabilityTheory.Kernel M.heap t.interp M.heapMeas (Ty.measurableSpace t) :=
  S ∘ₖ (Kernel.map (Kernel.id ×ₖ κ) (fun p : M.heap × tb.interp => M.set p.1 tb b.name p.2))

lemma fuseK_apply {tb t : Ty} (b : Vars ident tb)
    (κ : @ProbabilityTheory.Kernel M.heap tb.interp M.heapMeas (Ty.measurableSpace tb))
    [IsSFiniteKernel κ]
    (S : @ProbabilityTheory.Kernel M.heap t.interp M.heapMeas (Ty.measurableSpace t))
    (m : M.heap) :
    fuseK b κ S m = (κ m).bind (fun B => S (M.set m tb b.name B)) := by
  have hset : Measurable (fun B : tb.interp => M.set m tb b.name B) :=
    (M.set_measurable b.name).comp measurable_prodMk_left
  rw [fuseK, Kernel.comp_apply, Kernel.map_apply _ (M.set_measurable b.name),
    Kernel.prod_apply, Kernel.id_apply, Measure.dirac_prod,
    Measure.map_map (M.set_measurable b.name) measurable_prodMk_left]
  exact (bind_comp_eq (κ m) hset S.measurable).symm

/-- `fuseK` is sub-Markov.  Instance resolution finds this only at a generic `t`
    (`Ty.interp` is an `abbrev`); at a concrete type supply it by hand,
    `haveI := fuseK_isSubMarkov (t := .vec d) b _ _`. -/
instance fuseK_isSubMarkov {tb t : Ty} (b : Vars ident tb)
    (κ : @ProbabilityTheory.Kernel M.heap tb.interp M.heapMeas (Ty.measurableSpace tb))
    [IsSubMarkovKernel κ]
    (S : @ProbabilityTheory.Kernel M.heap t.interp M.heapMeas (Ty.measurableSpace t))
    [IsSubMarkovKernel S] : IsSubMarkovKernel (fuseK b κ S) := by
  refine ⟨fun m => ?_⟩
  rw [fuseK_apply]
  have hSm : Measurable (fun B : tb.interp => S (M.set m tb b.name B)) :=
    S.measurable.comp ((M.set_measurable b.name).comp measurable_prodMk_left)
  rw [Measure.bind_apply MeasurableSet.univ hSm.aemeasurable]
  calc ∫⁻ B, S (M.set m tb b.name B) Set.univ ∂(κ m)
      ≤ ∫⁻ _, 1 ∂(κ m) :=
        lintegral_mono fun B => IsSubMarkovKernel.measure_univ_le_one _
    _ = κ m Set.univ := lintegral_one
    _ ≤ 1 := IsSubMarkovKernel.measure_univ_le_one m

end Continuous
