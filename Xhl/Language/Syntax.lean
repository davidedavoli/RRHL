import Mathlib.Data.Int.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Probability.Kernel.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Tactic.DeriveCountable

/-!
# Syntax of the probabilistic imperative language

Types `Ty` with their measurable spaces, memories `MemType`, expressions `Expr`, and
commands `Cmd` (paper §4.1).
-/

open Classical MeasureTheory ProbabilityTheory

namespace Continuous

/-!
## Small universe of types
-/

/-- The types of the language.

    `finset n` is `Finset (Fin n)`; `fin n` is `Fin (n + 1)` (one more than its
    parameter, so that every type is inhabited). -/
inductive Ty : Type where
  | bool    : Ty
  | nat     : Ty
  | int     : Ty
  | real    : Ty
  | prod    : Ty → Ty → Ty
  | vec     : ℕ → Ty
  | finset  : ℕ → Ty
  | fin     : ℕ → Ty
  deriving DecidableEq, Repr, Countable

/-- Interpretation of `Ty` as Lean types. -/
abbrev Ty.interp : Ty → Type
  | .bool      => Bool
  | .nat       => Nat
  | .int       => Int
  | .real      => ℝ
  | .prod s t  => s.interp × t.interp
  | .vec d     => EuclideanSpace ℝ (Fin d)
  | .finset d  => Finset (Fin d)
  | .fin n     => Fin (n + 1)

/-- Every language type is inhabited -/
@[reducible] def Ty.inhabited : (t : Ty) → Inhabited t.interp
  | .bool     => ⟨false⟩
  | .nat      => show Inhabited Nat from inferInstance
  | .int      => show Inhabited Int from inferInstance
  | .real     => show Inhabited ℝ  from inferInstance
  | .prod s t => ⟨(s.inhabited.default, t.inhabited.default)⟩
  | .vec d    => show Inhabited (EuclideanSpace ℝ (Fin d)) from inferInstance
  | .finset d => show Inhabited (Finset (Fin d)) from inferInstance
  | .fin n    => show Inhabited (Fin (n + 1)) from inferInstance

instance (t : Ty) : Inhabited t.interp := t.inhabited

/-!
## Measurability of types
-/

/-- Every language type carries a measurable space structure -/
instance Ty.measurableSpace : (t : Ty) → MeasurableSpace t.interp
  | .bool     => inferInstance
  | .nat      => inferInstance
  | .int      => inferInstance
  | .real     => inferInstance
  | .prod s t => @Prod.instMeasurableSpace _ _ s.measurableSpace t.measurableSpace
  | .vec _d   => inferInstance
  | .finset _d => inferInstance
  | .fin _n   => inferInstance

/-- Every language type has measurable singletons. -/
instance Ty.measurableSingletonClass : (t : Ty) → MeasurableSingletonClass t.interp
  | .bool     => inferInstance
  | .nat      => inferInstance
  | .int      => inferInstance
  | .real     => inferInstance
  | .prod s t => @Prod.instMeasurableSingletonClass _ _ s.measurableSpace t.measurableSpace
      s.measurableSingletonClass t.measurableSingletonClass
  | .vec _d   => inferInstance
  | .finset _d => inferInstance
  | .fin _n   => inferInstance

/-!
## Memory Types
-/

/-- Abstract memory type: a heap with typed get/set operations. -/
structure MemType (ident : Type) where
  /-- The heap type -/
  heap : Type
  /-- The heap carries a measurable space -/
  heapMeas : MeasurableSpace heap
  /-- Read the value of type `t` at identifier `x`. -/
  get : heap → (t : Ty) → ident → t.interp
  /-- Write the value of type `t` at identifier `x`. -/
  set : heap → (t : Ty) → ident → t.interp → heap
  /-- Reading back a freshly written value gives the written value. -/
  get_set_eq : ∀ (t : Ty) (m : heap) (x : ident) (v : t.interp),
    get (set m t x v) t x = v
  /-- Reading a different location or type is unaffected by a write -/
  get_set_ne : ∀ (t u : Ty) (m : heap) (x y : ident) (v : t.interp),
    (t ≠ u ∨ x ≠ y) → get (set m t x v) u y = get m u y
  /-- Writing back the value just read leaves the memory unchanged -/
  set_get_eq : ∀ (t : Ty) (m : heap) (x : ident), set m t x (get m t x) = m
  /-- Extensionality: a memory is determined by the values of its variables -/
  ext : ∀ (m m' : heap), (∀ (t : Ty) (x : ident), get m t x = get m' t x) → m = m'
  /-- Reading a variable is measurable, for every type and identifier. -/
  get_measurable : ∀ (t : Ty) (x : ident),
    @Measurable heap t.interp heapMeas (Ty.measurableSpace t) (fun m => get m t x)
  /-- The update `set` is jointly measurable in (state, value) for every type and identifier. -/
  set_measurable : ∀ {t : Ty} (x : ident),
    @Measurable (heap × t.interp) heap
      (@Prod.instMeasurableSpace heap t.interp heapMeas (Ty.measurableSpace t))
      heapMeas
      (fun mv => set mv.1 t x mv.2)

/-!
## Variables
-/

/-- A typed variable over an identifier type. -/
structure Vars (ident : Type) (t : Ty) where
  name : ident

/-!
## Expressions

An expression of type `t` is a measurable function of the memory (shallow embedding).
The quoter `e⟪…⟫` (`Examples/Support/GameSyntax.lean`) builds expressions and discharges
their measurability.
-/

/-- Expressions over the memory type `M`, indexed by `Ty`: a function of the memory
    together with its measurability. -/
@[ext] structure Expr {ident : Type} (M : MemType ident) (t : Ty) where
  /-- The value of the expression in a memory. -/
  toFun : M.heap → t.interp
  /-- Expressions are measurable, by type. -/
  measurable : @Measurable M.heap t.interp M.heapMeas (Ty.measurableSpace t) toFun

/-- Boolean expression -/
abbrev BExpr {ident : Type} (M : MemType ident) := Expr M .bool

namespace Expr

variable {ident : Type} {M : MemType ident}


/-- Variable reference. -/
def var {t : Ty} (x : Vars ident t) : Expr M t :=
  ⟨fun m => M.get m t x.name, M.get_measurable t x.name⟩

/-- Constant. -/
def cst {t : Ty} (c : t.interp) : Expr M t := ⟨fun _ => c, measurable_const⟩

/-- Conditional expression `if b then e₁ else e₂`. -/
def ite {t : Ty} (b : BExpr M) (e₁ e₂ : Expr M t) : Expr M t :=
  ⟨fun m => if b.toFun m = true then e₁.toFun m else e₂.toFun m,
   Measurable.ite (p := fun m => b.toFun m = true) (b.measurable (measurableSet_singleton true))
     e₁.measurable e₂.measurable⟩

end Expr

/-!
## Commands
-/

/-- A **sub-Markov kernel**: every state's law is a sub-probability measure. The class
    of the sampling primitives; command denotations are again sub-Markov
    (`osemA_univ_le_one`). -/
class IsSubMarkovKernel {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (κ : ProbabilityTheory.Kernel α β) : Prop where
  measure_univ_le_one : ∀ a, κ a Set.univ ≤ 1

instance {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (κ : ProbabilityTheory.Kernel α β) [IsMarkovKernel κ] : IsSubMarkovKernel κ :=
  ⟨fun a => (measure_univ (μ := κ a)).le⟩

instance {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (κ : ProbabilityTheory.Kernel α β) [IsSubMarkovKernel κ] : IsFiniteKernel κ :=
  ⟨1, ENNReal.one_lt_top, IsSubMarkovKernel.measure_univ_le_one⟩

/-- Commands of the language (paper §4.1). `random` takes a sub-Markov kernel from the
    memory. -/
inductive Cmd (ident : Type) (M : MemType ident) : Type where
  /-- Abort (diverge / zero measure) -/
  | abort : Cmd ident M
  /-- Skip (identity) -/
  | skip : Cmd ident M
  /-- Deterministic assignment: x := e -/
  | assign : Vars ident t → Expr M t → Cmd ident M
  /-- Random assignment: x ← κ(m), where κ is a sub-Markov kernel -/
  | random : Vars ident t → (κ : @ProbabilityTheory.Kernel M.heap t.interp M.heapMeas t.measurableSpace) →
      [@IsSubMarkovKernel M.heap t.interp M.heapMeas t.measurableSpace κ] → Cmd ident M
  /-- Conditional: if e then c1 else c2 -/
  | cond : BExpr M → Cmd ident M → Cmd ident M → Cmd ident M
  /-- While loop: while e do c -/
  | while : BExpr M → Cmd ident M → Cmd ident M
  /-- Sequential composition: c1 ; c2 -/
  | seq : Cmd ident M → Cmd ident M → Cmd ident M
  /-- Release: the value of `e` is appended to the transcript; the memory is unchanged -/
  | release {t : Ty} : Expr M t → Cmd ident M
  /-- Local block: `local x in c` runs `c` with `x` initialised to the default value of
      its type and resets `x` to that default on exit. -/
  | loc : Vars ident t → Cmd ident M → Cmd ident M

namespace Cmd
infixl:74 " ;; " => Cmd.seq
end Cmd

open Cmd

/-!
## Concrete memory
-/

/-- Concrete memory: a function from typed identifiers to values. -/
structure CoreMem (ident : Type) where
  get : (t : Ty) → ident → t.interp

namespace CoreMem

variable {ident : Type} [DecidableEq ident]

/-- Set a value in the memory. -/
noncomputable def set (m : CoreMem ident) (t : Ty) (x : ident) (v : t.interp) :
    CoreMem ident where
  get u y :=
    if h : t = u then
      if x = y then h ▸ v else m.get u y
    else m.get u y

lemma get_set_eq (m : CoreMem ident) (t : Ty) (x : ident) (v : t.interp) :
    (m.set t x v).get t x = v := by simp [set]

lemma get_set_ne (m : CoreMem ident) (t u : Ty) (x y : ident) (v : t.interp)
    (h : t ≠ u ∨ x ≠ y) : (m.set t x v).get u y = m.get u y := by
  simp only [set]
  rcases h with htu | hxy
  · exact dif_neg htu
  · by_cases heqtu : t = u
    · subst heqtu; simp [hxy]
    · exact dif_neg heqtu

lemma set_get_eq (m : CoreMem ident) (t : Ty) (x : ident) : m.set t x (m.get t x) = m := by
  cases m with
  | mk g =>
    simp only [set, mk.injEq]
    funext u y
    by_cases h : t = u
    · subst h
      by_cases hxy : x = y
      · subst hxy; simp
      · simp [hxy]
    · simp [h]

end CoreMem

end Continuous
