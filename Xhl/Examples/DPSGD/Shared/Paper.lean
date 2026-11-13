import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Xhl.Examples.Support.GameSyntax
import Xhl.Examples.Support.Clip
import Xhl.Examples.Support.Adjacency
import Xhl.Divergence.SubsamplingRealOrderE
import Xhl.Language.PlainMem
import Xhl.Language.Semantics

/-!
# The DP-SGD model of Figure 1

The concrete model the DP-SGD case studies (§5.1, Appendix E.1–E.2) run on: the memory
`PMem`, the program variables and their readers and frame lemmas, the expressions of
Figure 1 (the clipped batch sum `clippedBatchSumD`, the model updates `modelUpdE` /
`modelUpdProjE` with step size `γv`, the guard `guardE`), the Poisson loop `poissonSample`
with its batch law `batchFrom`, and the observable `obsPaper`.  The programs are assembled
in `ReleasePrograms.lean`.

Records live in `ℝ^dx_⊥`: the dataset slot `dsV` holds the record values with the set of
present indices, read as records by `recBot`/`getR`; `∇ℓ(θ, ⊥) = 0` is the definition of
`gradBot`.  The batch `B` holds record indices, and the record is looked up in line 6
(`clippedBatchSumD`).  `Ty.fin N` interprets as `Fin (N + 1)`, so the paper's `|D|` is
`N + 1` here.  Slots whose type depends on a dimension (`D`, `θ`, `g`, `w`, `B`) are
parametrised `Vars` functions rather than `pvar`s, and the lines that read them are built
from `Expr` directly and spliced into `⟪…⟫` with `~`.
-/

open MeasureTheory ProbabilityTheory Continuous
open scoped NNReal ENNReal

namespace Continuous

section BindLinearity

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

/-- `bind` is additive in the (function-valued) kernel. -/
lemma bind_add_measure_fun (μ : Measure A) {f g : A → Measure B}
    (hf : Measurable f) (hg : Measurable g) :
    μ.bind f + μ.bind g = μ.bind (fun a => f a + g a) := by
  have hfg : Measurable (fun a => f a + g a) := by
    refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
    exact (Kernel.measurable_coe ⟨f, hf⟩ hs).add (Kernel.measurable_coe ⟨g, hg⟩ hs)
  ext s hs
  rw [Measure.add_apply, Measure.bind_apply hs hf.aemeasurable,
    Measure.bind_apply hs hg.aemeasurable, Measure.bind_apply hs hfg.aemeasurable]
  have hm : Measurable (fun a => (f a) s) := Kernel.measurable_coe ⟨f, hf⟩ hs
  rw [← lintegral_add_left hm]
  rfl

/-- `bind` commutes with scalar multiplication of the (function-valued) kernel. -/
lemma bind_smul_measure_fun (c : ℝ≥0∞) (μ : Measure A) {f : A → Measure B} (hf : Measurable f) :
    c • μ.bind f = μ.bind (fun a => c • f a) := by
  have hcf : Measurable (fun a => c • f a) := by
    refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
    simpa using (Kernel.measurable_coe ⟨f, hf⟩ hs).const_mul c
  ext s hs
  rw [Measure.smul_apply, Measure.bind_apply hs hf.aemeasurable,
    Measure.bind_apply hs hcf.aemeasurable]
  have hm : Measurable (fun a => (f a) s) := Kernel.measurable_coe ⟨f, hf⟩ hs
  rw [smul_eq_mul, ← lintegral_const_mul c hm]
  rfl

end BindLinearity

end Continuous

namespace DPSGDPaper

variable {m : ℕ}

theorem measurable_euclCoord {n : ℕ} (i : Fin n) :
    Measurable (fun x : EuclideanSpace ℝ (Fin n) => x i) :=
  (continuous_apply i).measurable.comp (EuclideanSpace.equiv (Fin n) ℝ).continuous.measurable

/-- The flat index of record `i`'s coordinate `j`. -/
def blockIdx (dx : ℕ) (i : Fin (m + 1)) (j : Fin dx) : Fin ((m + 1) * dx) :=
  finProdFinEquiv (i, j)

/-- Record `i`'s `dx` coordinates, read out of the flattened dataset. -/
noncomputable def blockRead (dx : ℕ) (D : EuclideanSpace ℝ (Fin ((m + 1) * dx)))
    (i : Fin (m + 1)) : EuclideanSpace ℝ (Fin dx) :=
  (EuclideanSpace.equiv (Fin dx) ℝ).symm (fun j => D (blockIdx dx i j))

theorem measurable_blockRead (dx : ℕ) (i : Fin (m + 1)) :
    Measurable (fun D : EuclideanSpace ℝ (Fin ((m + 1) * dx)) => blockRead dx D i) :=
  (EuclideanSpace.equiv (Fin dx) ℝ).symm.continuous.measurable.comp
    (measurable_pi_lambda _ (fun j => measurable_euclCoord (blockIdx dx i j)))

/-! ## The dataset over `ℝ^dx_⊥`

A dataset of `m + 1` records is the pair of the flattened record values `D` and the set `P`
of present indices; the value at an absent index is never read. -/

/-- Record `i` of the dataset `(D, P)`, in `ℝ^dx_⊥`: `⊥` (`none`) when `i ∉ P`. -/
noncomputable def recBot (dx : ℕ) (D : EuclideanSpace ℝ (Fin ((m + 1) * dx)))
    (P : Finset (Fin (m + 1))) (i : Fin (m + 1)) : Option (EuclideanSpace ℝ (Fin dx)) :=
  if i ∈ P then some (blockRead dx D i) else none

/-- Erasing `i` from the present indices sets record `i` to `⊥` and leaves the others. -/
lemma recBot_erase (dx : ℕ) (D : EuclideanSpace ℝ (Fin ((m + 1) * dx)))
    (P : Finset (Fin (m + 1))) (i j : Fin (m + 1)) :
    recBot dx D (P.erase i) j = if j = i then none else recBot dx D P j := by
  unfold recBot
  by_cases hj : j = i
  · subst hj; simp
  · simp [hj, Finset.mem_erase]

/-- The gradient on `ℝ^dx_⊥`: `∇ℓ(θ, ⊥) = 0` and `∇ℓ(θ, x) = grad x θ`. -/
noncomputable def gradBot {dx d : ℕ}
    (grad : EuclideanSpace ℝ (Fin dx) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) :
    Option (EuclideanSpace ℝ (Fin dx)) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)
  | none, _ => 0
  | some x, θ => grad x θ

@[simp] lemma gradBot_none {dx d : ℕ}
    (grad : EuclideanSpace ℝ (Fin dx) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (θ : EuclideanSpace ℝ (Fin d)) : gradBot grad none θ = 0 := rfl

@[simp] lemma gradBot_some {dx d : ℕ}
    (grad : EuclideanSpace ℝ (Fin dx) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (x : EuclideanSpace ℝ (Fin dx)) (θ : EuclideanSpace ℝ (Fin d)) :
    gradBot grad (some x) θ = grad x θ := rfl


/-! ## Variables and record readers shared by the case studies -/

/-- The sampled node `z`. -/
def zV (d : ℕ) : Vars String (.vec d) := ⟨"z"⟩

/-- The gradient accumulator `acc`. -/
def accV (d : ℕ) : Vars String (.vec d) := ⟨"acc"⟩

/-- The dataset `(D, P)` as an `ℕ`-indexed array over `ℝ^dx_⊥`: record `i` below `N + 1`,
    `⊥` beyond.  The record reader on which every case study states adjacency. -/
noncomputable def recBotN (N dx : ℕ)
    (DP : EuclideanSpace ℝ (Fin ((N + 1) * dx)) × Finset (Fin (N + 1))) (i : ℕ) :
    Option (EuclideanSpace ℝ (Fin dx)) :=
  if h : i < N + 1 then recBot dx DP.1 DP.2 ⟨i, h⟩ else none

lemma recBotN_fin (N dx : ℕ) (DP : EuclideanSpace ℝ (Fin ((N + 1) * dx)) × Finset (Fin (N + 1)))
    (i : Fin (N + 1)) : recBotN N dx DP i = recBot dx DP.1 DP.2 i := by
  simp only [recBotN, dif_pos i.isLt, Fin.eta]

/-- Adjacency at record `i` on the `ℕ`-indexed reader `recBotN` is adjacency of the
    `Fin (N + 1)`-indexed record arrays `recBot` (read by `getR`). -/
theorem adjAtSym_recBotN_iff (N dx : ℕ) {i : Fin (N + 1)}
    {DP₁ DP₂ : EuclideanSpace ℝ (Fin ((N + 1) * dx)) × Finset (Fin (N + 1))} :
    AdjAtSym (recBotN N dx) (i : ℕ) DP₁ DP₂ ↔
      AdjAtSym (fun DP (j : Fin (N + 1)) => recBot dx DP.1 DP.2 j) i DP₁ DP₂ := by
  have key : ∀ DP₁ DP₂ : EuclideanSpace ℝ (Fin ((N + 1) * dx)) × Finset (Fin (N + 1)),
      AdjAt (recBotN N dx) (i : ℕ) DP₁ DP₂ ↔
        AdjAt (fun DP (j : Fin (N + 1)) => recBot dx DP.1 DP.2 j) i DP₁ DP₂ := by
    intro DP₁ DP₂
    constructor
    · rintro ⟨hoff, hi⟩
      refine ⟨fun j hj => ?_, ?_⟩
      · have h := hoff j (fun e => hj (Fin.ext e))
        rwa [recBotN_fin, recBotN_fin] at h
      · rwa [recBotN_fin] at hi
    · rintro ⟨hoff, hi⟩
      refine ⟨fun t ht => ?_, ?_⟩
      · unfold recBotN
        split_ifs with hlt
        · exact hoff ⟨t, hlt⟩ (fun e => ht (by simp [← e]))
        · rfl
      · rw [recBotN_fin]
        exact hi
  exact or_congr (key DP₁ DP₂) (key DP₂ DP₁)

/-- Whether record `i` is present is a measurable function of the dataset. -/
lemma measurableSet_recBotN_isSome (N dx i : ℕ) :
    MeasurableSet {DP : EuclideanSpace ℝ (Fin ((N + 1) * dx)) × Finset (Fin (N + 1)) |
      (recBotN N dx DP i).isSome} := by
  by_cases h : i < N + 1
  · have hset : {DP : EuclideanSpace ℝ (Fin ((N + 1) * dx)) × Finset (Fin (N + 1)) |
        (recBotN N dx DP i).isSome}
          = Prod.snd ⁻¹' {P : Finset (Fin (N + 1)) | (⟨i, h⟩ : Fin (N + 1)) ∈ P} := by
      ext DP
      simp only [recBotN, dif_pos h, recBot, Set.mem_ofPred_eq, Set.mem_preimage]
      by_cases hP : (⟨i, h⟩ : Fin (N + 1)) ∈ DP.2 <;> simp [hP]
    rw [hset]
    exact measurable_snd (Set.toFinite _).measurableSet
  · simp only [recBotN, dif_neg h, Option.isSome_none, Bool.false_eq_true, Set.ofPred_false,
      MeasurableSet.empty]

/-- Record `i`, read with `⊥ ↦ 0`, is a measurable function of the dataset. -/
lemma measurable_recBotN_getD (N dx i : ℕ) :
    Measurable (fun DP : EuclideanSpace ℝ (Fin ((N + 1) * dx)) × Finset (Fin (N + 1)) =>
      (recBotN N dx DP i).getD 0) := by
  by_cases h : i < N + 1
  · have hS : MeasurableSet {DP : EuclideanSpace ℝ (Fin ((N + 1) * dx)) × Finset (Fin (N + 1)) |
        (⟨i, h⟩ : Fin (N + 1)) ∈ DP.2} :=
      measurable_snd
        (Set.toFinite {P : Finset (Fin (N + 1)) | (⟨i, h⟩ : Fin (N + 1)) ∈ P}).measurableSet
    have hfun : (fun DP : EuclideanSpace ℝ (Fin ((N + 1) * dx)) × Finset (Fin (N + 1)) =>
        (recBotN N dx DP i).getD 0)
          = fun DP => if (⟨i, h⟩ : Fin (N + 1)) ∈ DP.2 then blockRead dx DP.1 ⟨i, h⟩ else 0 := by
      funext DP
      simp only [recBotN, dif_pos h, recBot]
      split_ifs <;> rfl
    rw [hfun]
    exact Measurable.ite hS ((measurable_blockRead dx _).comp measurable_fst) measurable_const
  · simp only [recBotN, dif_neg h, Option.getD_none]
    exact measurable_const

end DPSGDPaper

namespace DPSGDPaper

/-! ## The memory

`PMem` is `plainMemType String`: every slot projection is measurable
(`CoreMem.measurable_get`).  The dataset is one slot `dsV` holding the flattened record
values (a Euclidean space, so with its Borel structure) and the discrete set of present
indices. -/

noncomputable def PMem : MemType String := plainMemType String

noncomputable instance : MeasurableSpace PMem.heap := PMem.heapMeas

/-! ## Program variables

`cnt` (the paper's `t`), `jv` (the Poisson loop's index) and `bv` (its coin) are `pvar`s;
the dimension-dependent slots are `dsV`/`thV`/`gV`/`gtV`/`bchV`. -/

pvar PMem cnt : .nat
pvar PMem jv : .nat
pvar PMem bv : .bool

/-- `D` — the dataset: `N + 1` records in `ℝ^dx_⊥`, as (record values, present indices). -/
def dsV (N dx : ℕ) : Vars String (.prod (.vec ((N + 1) * dx)) (.finset (N + 1))) := ⟨"D"⟩
/-- `θ` — the model. -/
def thV (d : ℕ) : Vars String (.vec d) := ⟨"th"⟩
/-- `g` — the clipped batch sum. -/
def gV (d : ℕ) : Vars String (.vec d) := ⟨"g"⟩
/-- `w` — the noised gradient (the per-round release of the transcript model). -/
def gtV (d : ℕ) : Vars String (.vec d) := ⟨"gt"⟩
/-- `B` — the Poisson batch, a set of record indices. -/
def bchV (N : ℕ) : Vars String (.finset (N + 1)) := ⟨"B"⟩

/-! ### Readers, and their measurability -/

/-- The dataset slot: the record values and the present indices. -/
noncomputable def getDS (N dx : ℕ) (m : PMem.heap) :
    EuclideanSpace ℝ (Fin ((N + 1) * dx)) × Finset (Fin (N + 1)) :=
  PMem.get m (.prod (.vec ((N + 1) * dx)) (.finset (N + 1))) "D"
/-- The dataset as its record array over `ℝ^dx_⊥`. -/
noncomputable def getR (N dx : ℕ) (m : PMem.heap) : Fin (N + 1) → Option (EuclideanSpace ℝ (Fin dx)) :=
  fun j => recBot dx (getDS N dx m).1 (getDS N dx m).2 j
noncomputable def getTh (d : ℕ) (m : PMem.heap) : EuclideanSpace ℝ (Fin d) :=
  PMem.get m (.vec d) "th"
noncomputable def getG (d : ℕ) (m : PMem.heap) : EuclideanSpace ℝ (Fin d) :=
  PMem.get m (.vec d) "g"
noncomputable def getGt (d : ℕ) (m : PMem.heap) : EuclideanSpace ℝ (Fin d) :=
  PMem.get m (.vec d) "gt"
noncomputable def getBatch (N : ℕ) (m : PMem.heap) : Finset (Fin (N + 1)) :=
  PMem.get m (.finset (N + 1)) "B"

lemma measurable_getDS (N dx : ℕ) : Measurable (getDS N dx) :=
  CoreMem.measurable_get (.prod (.vec ((N + 1) * dx)) (.finset (N + 1))) "D"
lemma measurable_getTh (d : ℕ) : Measurable (getTh d) := CoreMem.measurable_get (.vec d) "th"
lemma measurable_getG (d : ℕ) : Measurable (getG d) := CoreMem.measurable_get (.vec d) "g"
lemma measurable_getGt (d : ℕ) : Measurable (getGt d) := CoreMem.measurable_get (.vec d) "gt"
lemma measurable_getBatch (N : ℕ) : Measurable (getBatch N) :=
  CoreMem.measurable_get (.finset (N + 1)) "B"
lemma measurable_getCnt : Measurable getCnt := CoreMem.measurable_get .nat "cnt"
lemma measurable_getJv : Measurable getJv := CoreMem.measurable_get .nat "jv"
/-! ## Line 6: the clipped batch sum -/

section Params
variable {N dx d : ℕ}

/-- Line 6 of Figure 1: `Σ_{j∈B} clip_Γ(∇ℓ(θ, R j))` over the record array
    `R : Fin (N+1) → ℝ^dx_⊥`. -/
noncomputable def clippedBatchSumD
    (grad : EuclideanSpace ℝ (Fin dx) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (C : ℝ≥0)
    (B : Finset (Fin (N + 1))) (R : Fin (N + 1) → Option (EuclideanSpace ℝ (Fin dx)))
    (θ : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  ∑ j ∈ B, clipV C (gradBot grad (R j) θ)

/-- At a fixed batch, the clipped batch sum is measurable in the dataset and the model
    (split on the countably many present-index sets). -/
lemma measurable_clippedBatchSumD_at
    (grad : EuclideanSpace ℝ (Fin dx) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hgrad : Measurable (fun p : EuclideanSpace ℝ (Fin dx) × EuclideanSpace ℝ (Fin d) =>
      grad p.1 p.2))
    (C : ℝ≥0) (B : Finset (Fin (N + 1))) :
    Measurable (fun m : PMem.heap =>
      clippedBatchSumD (N := N) grad C B (getR N dx m) (getTh d m)) := by
  have hP : ∀ P : Finset (Fin (N + 1)),
      Measurable (fun p : EuclideanSpace ℝ (Fin ((N + 1) * dx)) × EuclideanSpace ℝ (Fin d) =>
        clippedBatchSumD (N := N) grad C B (fun j => recBot dx p.1 P j) p.2) := by
    intro P
    refine Finset.measurable_sum B fun j _ => ?_
    by_cases hj : j ∈ P
    · simp only [recBot, if_pos hj, gradBot_some]
      exact (measurable_clipV (C : ℝ)).comp (hgrad.comp
        (((measurable_blockRead dx j).comp measurable_fst).prodMk measurable_snd))
    · simp only [recBot, if_neg hj, gradBot_none]
      exact measurable_const
  have hjoint : Measurable (fun p : Finset (Fin (N + 1)) ×
      (EuclideanSpace ℝ (Fin ((N + 1) * dx)) × EuclideanSpace ℝ (Fin d)) =>
      clippedBatchSumD (N := N) grad C B (fun j => recBot dx p.2.1 p.1 j) p.2.2) :=
    measurable_from_prod_countable_right hP
  exact Measurable.comp (g := fun p : Finset (Fin (N + 1)) ×
      (EuclideanSpace ℝ (Fin ((N + 1) * dx)) × EuclideanSpace ℝ (Fin d)) =>
      clippedBatchSumD (N := N) grad C B (fun j => recBot dx p.2.1 p.1 j) p.2.2)
    (f := fun m : PMem.heap => ((getDS N dx m).2, (getDS N dx m).1, getTh d m)) hjoint
    ((measurable_snd.comp (measurable_getDS N dx)).prodMk
      ((measurable_fst.comp (measurable_getDS N dx)).prodMk (measurable_getTh d)))

/-- Joint measurability of `clippedBatchSumD` in `(B, D, θ)`. -/
lemma measurable_clippedBatchSumD
    (grad : EuclideanSpace ℝ (Fin dx) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hgrad : Measurable (fun p : EuclideanSpace ℝ (Fin dx) × EuclideanSpace ℝ (Fin d) =>
      grad p.1 p.2))
    (C : ℝ≥0) :
    Measurable (fun m : PMem.heap =>
      clippedBatchSumD (N := N) grad C (getBatch N m) (getR N dx m) (getTh d m)) := by
  have hjoint : Measurable (fun p : Finset (Fin (N + 1)) × PMem.heap =>
      clippedBatchSumD (N := N) grad C p.1 (getR N dx p.2) (getTh d p.2)) :=
    measurable_from_prod_countable_right fun B => measurable_clippedBatchSumD_at grad hgrad C B
  exact Measurable.comp (g := fun p : Finset (Fin (N + 1)) × PMem.heap =>
      clippedBatchSumD (N := N) grad C p.1 (getR N dx p.2) (getTh d p.2))
    (f := fun m : PMem.heap => (getBatch N m, m)) hjoint
    ((measurable_getBatch N).prodMk measurable_id)

end Params

/-- Joint measurability of the gradient, the one side condition of the round's expressions. -/
abbrev MeasOK (dx d : ℕ)
    (grad : EuclideanSpace ℝ (Fin dx) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) :
    Prop :=
  Measurable (fun p : EuclideanSpace ℝ (Fin dx) × EuclideanSpace ℝ (Fin d) => grad p.1 p.2)

/-- Line 6's expression, reading `B`, `D` and `θ`. -/
noncomputable def batchSumPaperE (N dx d : ℕ)
    (grad : EuclideanSpace ℝ (Fin dx) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (C : ℝ≥0)
    (hm : MeasOK dx d grad) : Expr PMem (.vec d) :=
  ⟨fun m => clippedBatchSumD (N := N) grad C (getBatch N m) (getR N dx m) (getTh d m),
    measurable_clippedBatchSumD grad hm C⟩


/-- Insert the index `j` into the batch (`Fin.ofNat`, total in `j`). -/
noncomputable def insertIdx (N : ℕ) (j : ℕ) (S : Finset (Fin (N + 1))) : Finset (Fin (N + 1)) :=
  insert (Fin.ofNat (N + 1) j) S

/-- `B ∪ {j}`, as the expression (measurable since both arguments are discrete). -/
noncomputable def insertJE (N : ℕ) : Expr PMem (.finset (N + 1)) :=
  ⟨fun m => insertIdx N (getJv m) (getBatch N m),
    (Measurable.of_discrete (f := fun p : ℕ × Finset (Fin (N + 1)) => insertIdx N p.1 p.2)).comp
      (measurable_getJv.prodMk (measurable_getBatch N))⟩

@[simp] lemma esem_insertJE (N : ℕ) (m : PMem.heap) :
    esem (insertJE N) m = insertIdx N (getJv m) (getBatch N m) := rfl

/-! ## Line 8: the model update `θ ← Π(θ − γ·w)`, with `γ = γv N η q` -/

noncomputable def modelUpdE (d : ℕ) (γ : ℝ) : Expr PMem (.vec d) :=
  ⟨fun m => getTh d m - γ • getGt d m, (measurable_getTh d).sub ((measurable_getGt d).const_smul γ)⟩

@[simp] lemma esem_modelUpdE (d : ℕ) (γ : ℝ) (m : PMem.heap) :
    esem (modelUpdE d γ) m = getTh d m - γ • getGt d m := rfl

/-- The step size `η / (q·|D|)` with `|D| = N + 1`. -/
noncomputable def γv (N : ℕ) (η : ℝ) (q : ℝ≥0) : ℝ := η / ((q : ℝ) * ((N : ℝ) + 1))

/-- The projected update `θ ← Π(θ − γ·w)`. -/
noncomputable def modelUpdProjE (d : ℕ) (proj : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hpm : Measurable proj) (γ : ℝ) : Expr PMem (.vec d) :=
  ⟨fun m => proj (getTh d m - γ • getGt d m),
    hpm.comp ((measurable_getTh d).sub ((measurable_getGt d).const_smul γ))⟩

@[simp] lemma esem_modelUpdProjE (d : ℕ) (proj : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hpm : Measurable proj) (γ : ℝ) (m : PMem.heap) :
    esem (modelUpdProjE d proj hpm γ) m = proj (getTh d m - γ • getGt d m) := rfl

/-! ## The Poisson loop `Pois_q` of Figure 1, over the indices `0, …, N` -/

noncomputable def poissonSample (N : ℕ) (q : ℝ≥0) : Cmd String PMem :=
  ⟪ (bchV N) ← (∅ : Finset (Fin (N + 1))) ;
    jv ← (0 : ℕ) ;
    while jv < N + 1 do
      bv ←$ Bern(q) ;
      if bv then
        ~(Cmd.assign (bchV N) (insertJE N))
      else
        skip
      fi ;
      jv ← jv + (1 : ℕ)
    od ⟫

/-! ## One step of the Poisson loop

The loop's guard and body, and the body's one-step semantics (`osemA_poissonLoopBody`). -/

private lemma ty_bool_ne_nat : (Ty.bool : Ty) ≠ Ty.nat := fun h => Ty.noConfusion h

private lemma ty_finset_ne_nat (n : ℕ) : (Ty.finset n : Ty) ≠ Ty.nat := fun h => Ty.noConfusion h
private lemma ty_bool_ne_finset (n : ℕ) : (Ty.bool : Ty) ≠ Ty.finset n := fun h => Ty.noConfusion h

noncomputable def poissonGuard (N : ℕ) : BExpr PMem := ltW jv (N + 1)

noncomputable def poissonLoopBody (N : ℕ) (q : ℝ≥0) : Cmd String PMem :=
  Cmd.seq
    (Cmd.seq (Cmd.random bv (bernoulliKernel q))
      (Cmd.cond (Expr.var bv) (Cmd.assign (bchV N) (insertJE N)) Cmd.skip))
    (Cmd.assign jv (incW jv))

lemma poissonSample_eq (N : ℕ) (q : ℝ≥0) :
    poissonSample N q =
      Cmd.seq (Cmd.seq (Cmd.assign (bchV N) (Expr.cst ∅)) (Cmd.assign jv (Expr.cst 0)))
        (Cmd.while (poissonGuard N) (poissonLoopBody N q)) := rfl

/-- One iteration's post-state given the coin `b`: insert `jv` into `B` iff `b`, then
    advance `jv`. -/
noncomputable def poissonStep (N : ℕ) (m : PMem.heap) (b : Bool) : PMem.heap :=
  PMem.set
    (if b then
      PMem.set (PMem.set m .bool bv.name b) (.finset (N + 1)) (bchV N).name
        (insertIdx N (getJv m) (getBatch N m))
     else
      PMem.set m .bool bv.name b)
    .nat jv.name (getJv m + 1)

lemma getJv_poissonStep (N : ℕ) (m : PMem.heap) (b : Bool) :
    getJv (poissonStep N m b) = getJv m + 1 := by
  unfold poissonStep getJv
  exact PMem.get_set_eq _ _ jv.name _

private lemma getJv_poissonStep_branch (N : ℕ) (m : PMem.heap) (v : Bool) :
    getJv (if v then
        PMem.set (PMem.set m .bool bv.name v) (.finset (N + 1)) (bchV N).name
          (insertIdx N (getJv m) (getBatch N m))
      else PMem.set m .bool bv.name v) = getJv m := by
  unfold getJv
  cases v with
  | true =>
    simp only [↓reduceIte]
    rw [PMem.get_set_ne _ _ _ _ _ _ (Or.inl (ty_finset_ne_nat _)),
      PMem.get_set_ne _ _ _ _ _ _ (Or.inl ty_bool_ne_nat)]
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact PMem.get_set_ne _ _ _ _ _ _ (Or.inl ty_bool_ne_nat)

/-- One iteration of the loop body: a `Bernoulli(q)` coin followed by `poissonStep`; the
    transcript is untouched. -/
lemma osemA_poissonLoopBody (N : ℕ) (q : ℝ≥0) (s : St PMem) :
    osemA (poissonLoopBody N q) s =
      (Continuous.bernoulliMeasure q).bind
        (fun b => Measure.dirac ((poissonStep N s.1 b, s.2) : St PMem)) := by
  have hcondMeas : Measurable
      (osemA (Cmd.cond (Expr.var bv) (Cmd.assign (bchV N) (insertJE N)) (Cmd.skip (M := PMem)))) :=
    osemA_measurable _
  have hdiracSetBvMeas : Measurable (fun v : Bool =>
      Measure.dirac ((PMem.set s.1 .bool bv.name v, s.2) : St PMem)) :=
    Measurable.of_discrete
  show osemA (Cmd.seq (Cmd.seq (Cmd.random bv (bernoulliKernel q))
      (Cmd.cond (Expr.var bv) (Cmd.assign (bchV N) (insertJE N)) Cmd.skip))
      (Cmd.assign jv (incW jv))) s = _
  rw [osemA_seq, osemA_seq, osemA_random, bernoulliKernel_apply,
    Measure.bind_bind hdiracSetBvMeas.aemeasurable hcondMeas.aemeasurable]
  simp_rw [Measure.dirac_bind hcondMeas]
  have hstep : ∀ v : Bool, osemA (Cmd.cond (Expr.var bv) (Cmd.assign (bchV N) (insertJE N))
      (Cmd.skip (M := PMem))) ((PMem.set s.1 .bool bv.name v, s.2) : St PMem) =
      Measure.dirac ((if v then
          PMem.set (PMem.set s.1 .bool bv.name v) (.finset (N + 1)) (bchV N).name
            (insertIdx N (getJv s.1) (getBatch N s.1))
         else PMem.set s.1 .bool bv.name v, s.2) : St PMem) := by
    intro v
    have hguard : esem (Expr.var bv) (PMem.set s.1 .bool bv.name v) = v := by
      show getBv (PMem.set s.1 .bool bv.name v) = v
      unfold getBv
      exact PMem.get_set_eq _ _ bv.name _
    rw [osemA_cond]
    show (if esem (Expr.var bv) (PMem.set s.1 .bool bv.name v) = true then _ else _) = _
    rw [hguard]
    cases v with
    | true =>
      simp only [↓reduceIte]
      rw [osemA_assign]
      show Measure.dirac ((_, s.2) : St PMem) = _
      rw [show esem (insertJE N) (PMem.set s.1 .bool bv.name true)
            = insertIdx N (getJv (PMem.set s.1 .bool bv.name true))
                (getBatch N (PMem.set s.1 .bool bv.name true)) from rfl,
        show getJv (PMem.set s.1 .bool bv.name true) = getJv s.1 from
          PMem.get_set_ne _ _ _ _ _ _ (Or.inl ty_bool_ne_nat),
        show getBatch N (PMem.set s.1 .bool bv.name true) = getBatch N s.1 from
          PMem.get_set_ne _ _ _ _ _ _ (Or.inl (ty_bool_ne_finset _))]
    | false => simp only [Bool.false_eq_true, ↓reduceIte, osemA_skip]
  simp_rw [hstep]
  have hdiracNextMeas : Measurable (fun v : Bool => Measure.dirac ((if v then
      PMem.set (PMem.set s.1 .bool bv.name v) (.finset (N + 1)) (bchV N).name
        (insertIdx N (getJv s.1) (getBatch N s.1))
      else PMem.set s.1 .bool bv.name v, s.2) : St PMem)) := Measurable.of_discrete
  have hosemAssignMeas : Measurable (osemA (Cmd.assign jv (incW jv) : Cmd String PMem)) :=
    osemA_measurable _
  rw [Measure.bind_bind hdiracNextMeas.aemeasurable hosemAssignMeas.aemeasurable]
  refine congrArg (Measure.bind (Continuous.bernoulliMeasure q)) (funext fun v => ?_)
  rw [Measure.dirac_bind hosemAssignMeas, osemA_assign]
  show Measure.dirac ((PMem.set _ .nat jv.name (getJv _ + 1), s.2) : St PMem)
    = Measure.dirac ((poissonStep N s.1 v, s.2) : St PMem)
  rw [getJv_poissonStep_branch N s.1 v]
  rfl

/-- The law of deciding indices `j, …, j + k - 1` by independent `Bernoulli(q)` coins on
    top of the batch `S₀`; the Poisson batch law is `batchFrom N q (N + 1) 0 ∅`. -/
noncomputable def batchFrom (N : ℕ) (q : ℝ≥0) :
    ℕ → ℕ → Finset (Fin (N + 1)) → Measure (Finset (Fin (N + 1)))
  | 0,     _, S₀ => Measure.dirac S₀
  | k + 1, j, S₀ => (Continuous.bernoulliMeasure q).bind (fun b =>
      batchFrom N q k (j + 1) (if b then insert (Fin.ofNat (N + 1) j) S₀ else S₀))

/-! ## The Poisson batch law -/

private lemma ty_ne_or_name_ne {ty : Ty} {nm : String} {T : Ty} {Nm : String}
    (h : ¬ (ty = T ∧ nm = Nm)) : T ≠ ty ∨ Nm ≠ nm := by
  by_cases hty : ty = T
  · exact Or.inr (fun hnm => h ⟨hty, hnm.symm⟩)
  · exact Or.inl (fun he => hty he.symm)

/-- `m` with `jv`/`bv`/`B` overwritten to `j`/`b`/`S`. -/
noncomputable def setPoissonState (N : ℕ) (m : PMem.heap) (j : ℕ) (b : Bool)
    (S : Finset (Fin (N + 1))) : PMem.heap :=
  PMem.set (PMem.set (PMem.set m .bool bv.name b) (.finset (N + 1)) (bchV N).name S)
    .nat jv.name j

/-- The Poisson batch law as a constant kernel (codomain instance given explicitly, to
    match the one `Cmd.random` expects). -/
noncomputable def poissonBatchKernel (N : ℕ) (q : ℝ≥0) :
    @ProbabilityTheory.Kernel PMem.heap (Finset (Fin (N + 1))) PMem.heapMeas
      (Ty.measurableSpace (.finset (N + 1))) :=
  Kernel.const _ (batchFrom N q (N + 1) 0 ∅)

@[simp] lemma poissonBatchKernel_apply (N : ℕ) (q : ℝ≥0) (m : PMem.heap) :
    poissonBatchKernel N q m = batchFrom N q (N + 1) 0 ∅ := rfl

lemma isProb_batchFrom (N : ℕ) (q : ℝ≥0) :
    ∀ (k j : ℕ) (S₀ : Finset (Fin (N + 1))), IsProbabilityMeasure (batchFrom N q k j S₀) := by
  intro k
  induction k with
  | zero => intro j S₀; exact (inferInstance : IsProbabilityMeasure (Measure.dirac S₀))
  | succ k ih =>
    intro j S₀
    have hF : Measurable (fun b : Bool => batchFrom N q k (j + 1)
        (if b then insert (Fin.ofNat (N + 1) j) S₀ else S₀)) := Measurable.of_discrete
    have hall : ∀ᵐ b ∂ (Continuous.bernoulliMeasure q), IsProbabilityMeasure (batchFrom N q k
        (j + 1) (if b then insert (Fin.ofNat (N + 1) j) S₀ else S₀)) :=
      Filter.Eventually.of_forall (fun b => by cases b <;> exact ih _ _)
    exact isProbabilityMeasure_bind hF.aemeasurable hall

instance isMarkov_poissonBatchKernel (N : ℕ) (q : ℝ≥0) :
    IsMarkovKernel (poissonBatchKernel N q) := by
  haveI := isProb_batchFrom N q (N + 1) 0 ∅
  rw [poissonBatchKernel]; infer_instance

/-! ## The batch law as a two-point mixture at record `i`

`batchFrom_eq_mix_erase` writes the batch law as
`ω.bind (fun S => (1 - q) • dirac (S.erase i) + q • dirac (insert i S))`, with `ω` the
law with record `i` erased; used by the split leaf in `Equiv/SplitLeaves.lean`. -/

/-- Starting from `insert i S₀` is drawing from `S₀` and inserting `i` afterwards. -/
theorem batchFrom_insert (N : ℕ) (q : ℝ≥0) (i : Fin (N + 1)) :
    ∀ (k j : ℕ) (S₀ : Finset (Fin (N + 1))),
      batchFrom N q k j (insert i S₀) = (batchFrom N q k j S₀).map (insert i) := by
  intro k
  induction k with
  | zero =>
    intro j S₀
    show Measure.dirac (insert i S₀) = (Measure.dirac S₀).map (insert i)
    rw [Measure.map_dirac' Measurable.of_discrete]
  | succ k ih =>
    intro j S₀
    have hF : Measurable (fun b : Bool => batchFrom N q k (j + 1)
        (if b then insert (Fin.ofNat (N + 1) j) S₀ else S₀)) := Measurable.of_discrete
    have hins : Measurable (insert i : Finset (Fin (N + 1)) → Finset (Fin (N + 1))) :=
      Measurable.of_discrete
    have hbatchUnfold : batchFrom N q (k + 1) j (insert i S₀) = (Continuous.bernoulliMeasure q).bind
        (fun b => batchFrom N q k (j + 1)
          (insert i (if b then insert (Fin.ofNat (N + 1) j) S₀ else S₀))) := by
      show (Continuous.bernoulliMeasure q).bind (fun b => batchFrom N q k (j + 1)
          (if b then insert (Fin.ofNat (N + 1) j) (insert i S₀) else insert i S₀)) = _
      congr 1
      funext b
      cases b with
      | true => simp only [↓reduceIte]; rw [Finset.insert_comm]
      | false => simp only [Bool.false_eq_true, ↓reduceIte]
    have hRHSUnfold : batchFrom N q (k + 1) j S₀ = (Continuous.bernoulliMeasure q).bind
        (fun b => batchFrom N q k (j + 1) (if b then insert (Fin.ofNat (N + 1) j) S₀ else S₀)) :=
      rfl
    have hstep : ∀ b : Bool, batchFrom N q k (j + 1)
        (insert i (if b then insert (Fin.ofNat (N + 1) j) S₀ else S₀))
        = (batchFrom N q k (j + 1) (if b then insert (Fin.ofNat (N + 1) j) S₀ else S₀)).map
            (insert i) := fun b => ih (j + 1) _
    rw [hbatchUnfold, hRHSUnfold, map_bind_eq _ hF hins]
    exact congrArg (Measure.bind _) (funext hstep)

/-- Erasing an index `i` that is not in `S₀` and below the active range leaves the law
    unchanged. -/
theorem batchFrom_erase_self (N : ℕ) (q : ℝ≥0) (i : Fin (N + 1)) :
    ∀ (k j : ℕ) (S₀ : Finset (Fin (N + 1))), i.val < j → j + k ≤ N + 1 → i ∉ S₀ →
      (batchFrom N q k j S₀).map (fun S => S.erase i) = batchFrom N q k j S₀ := by
  intro k
  induction k with
  | zero =>
    intro j S₀ _ _ hiS₀
    show (Measure.dirac S₀).map (fun S => S.erase i) = Measure.dirac S₀
    rw [Measure.map_dirac' Measurable.of_discrete, Finset.erase_eq_self.mpr hiS₀]
  | succ k ih =>
    intro j S₀ hij hjk hiS₀
    have hF : Measurable (fun b : Bool => batchFrom N q k (j + 1)
        (if b then insert (Fin.ofNat (N + 1) j) S₀ else S₀)) := Measurable.of_discrete
    have herase : Measurable (fun S : Finset (Fin (N + 1)) => S.erase i) := Measurable.of_discrete
    have hbatchUnfold : batchFrom N q (k + 1) j S₀ = (Continuous.bernoulliMeasure q).bind
        (fun b => batchFrom N q k (j + 1) (if b then insert (Fin.ofNat (N + 1) j) S₀ else S₀)) :=
      rfl
    have hjlt : j < N + 1 := by omega
    have hjval : (Fin.ofNat (N + 1) j).val = j := by
      rw [Fin.ofNat_eq_cast, Fin.val_cast_of_lt hjlt]
    have hine : i ≠ Fin.ofNat (N + 1) j := by
      intro h; rw [h, hjval] at hij; exact absurd hij (lt_irrefl _)
    rw [hbatchUnfold, map_bind_eq _ hF herase]
    refine congrArg (Measure.bind _) (funext fun b => ?_)
    cases b with
    | true =>
      simp only [↓reduceIte]
      exact ih (j + 1) (insert (Fin.ofNat (N + 1) j) S₀) (by omega) (by omega)
        (fun h => (Finset.mem_insert.mp h).elim hine hiS₀)
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact ih (j + 1) S₀ (by omega) (by omega) hiS₀

/-- A bind over `bernoulliMeasure` is the two-point mixture of the continuation. -/
private lemma bernoulliMeasure_bind {Y : Type*} [MeasurableSpace Y] {q : ℝ≥0} (hq : q ≤ 1)
    (F : Bool → Measure Y) (hF : Measurable F) :
    (Continuous.bernoulliMeasure q).bind F
      = (1 - (q : ℝ≥0∞)) • F false + (q : ℝ≥0∞) • F true := by
  rw [Continuous.bernoulliMeasure_of_le hq]
  ext s hs
  rw [Measure.bind_apply hs hF.aemeasurable, Measure.add_apply, Measure.smul_apply,
    Measure.smul_apply, lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure,
    lintegral_dirac, lintegral_dirac]

/-- The two-point mixture at record `i`, from coin `j` on, while `j ≤ i < j + k` and
    `i ∉ S₀`; by induction on `k`. -/
theorem batchFrom_eq_mixAt (N : ℕ) {q : ℝ≥0} (hq : q ≤ 1) (i : Fin (N + 1)) :
    ∀ (k j : ℕ) (S₀ : Finset (Fin (N + 1))), j ≤ i.val → i.val < j + k → j + k ≤ N + 1 →
      i ∉ S₀ →
      batchFrom N q k j S₀ = ((batchFrom N q k j S₀).map (fun S => S.erase i)).bind
        (fun S => (1 - (q : ℝ≥0∞)) • Measure.dirac (S.erase i) +
          (q : ℝ≥0∞) • Measure.dirac (insert i S)) := by
  have herase : Measurable (fun S : Finset (Fin (N + 1)) => S.erase i) := Measurable.of_discrete
  have hins : Measurable (insert i : Finset (Fin (N + 1)) → Finset (Fin (N + 1))) :=
    Measurable.of_discrete
  have hK : Measurable (fun S : Finset (Fin (N + 1)) => (1 - (q : ℝ≥0∞)) •
      Measure.dirac (S.erase i) + (q : ℝ≥0∞) • Measure.dirac (insert i S)) :=
    Measurable.of_discrete
  intro k
  induction k with
  | zero => intro j S₀ hj hi _ _; omega
  | succ k ih =>
    intro j S₀ hj hi hk hiS₀
    have hF : Measurable (fun b : Bool => batchFrom N q k (j + 1)
        (if b then insert (Fin.ofNat (N + 1) j) S₀ else S₀)) := Measurable.of_discrete
    have hbatchUnfold : batchFrom N q (k + 1) j S₀ = (Continuous.bernoulliMeasure q).bind
        (fun b => batchFrom N q k (j + 1) (if b then insert (Fin.ofNat (N + 1) j) S₀ else S₀)) :=
      rfl
    have hjlt : j < N + 1 := by omega
    have hjval : (Fin.ofNat (N + 1) j).val = j := by
      rw [Fin.ofNat_eq_cast, Fin.val_cast_of_lt hjlt]
    rcases Nat.lt_or_ge j i.val with hji | hji
    · -- the coin at `j` is not record `i`'s: both sides recurse under the same bind
      have hine : i ≠ Fin.ofNat (N + 1) j := by
        intro h; rw [h, hjval] at hji; exact lt_irrefl _ hji
      have hG : Measurable (fun b : Bool => (batchFrom N q k (j + 1)
          (if b then insert (Fin.ofNat (N + 1) j) S₀ else S₀)).map (fun S => S.erase i)) :=
        Measurable.of_discrete
      rw [hbatchUnfold, map_bind_eq _ hF herase,
        Measure.bind_bind hG.aemeasurable hK.aemeasurable]
      refine congrArg (Measure.bind _) (funext fun b => ?_)
      cases b with
      | true =>
        simp only [↓reduceIte]
        exact ih (j + 1) (insert (Fin.ofNat (N + 1) j) S₀) (by omega) (by omega) (by omega)
          (fun h => (Finset.mem_insert.mp h).elim hine hiS₀)
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact ih (j + 1) S₀ (by omega) (by omega) (by omega) hiS₀
    · -- the coin at `j` is record `i`'s: it is the completion coin
      have hofi : Fin.ofNat (N + 1) j = i := Fin.ext (by rw [hjval]; omega)
      have hBe : (batchFrom N q k (j + 1) S₀).map (fun S => S.erase i)
          = batchFrom N q k (j + 1) S₀ :=
        batchFrom_erase_self N q i k (j + 1) S₀ (by omega) (by omega) hiS₀
      have hcoin : (fun b : Bool => batchFrom N q k (j + 1)
          (if b then insert (Fin.ofNat (N + 1) j) S₀ else S₀))
          = fun b => if b then (batchFrom N q k (j + 1) S₀).map (insert i)
              else batchFrom N q k (j + 1) S₀ := by
        funext b
        cases b with
        | true => simp only [↓reduceIte]; rw [hofi]; exact batchFrom_insert N q i k (j + 1) S₀
        | false => simp only [Bool.false_eq_true, ↓reduceIte]
      have hF' : Measurable (fun b : Bool => if b then
          (batchFrom N q k (j + 1) S₀).map (insert i) else batchFrom N q k (j + 1) S₀) :=
        Measurable.of_discrete
      have hLaw : batchFrom N q (k + 1) j S₀
          = (1 - (q : ℝ≥0∞)) • batchFrom N q k (j + 1) S₀
            + (q : ℝ≥0∞) • (batchFrom N q k (j + 1) S₀).map (insert i) := by
        rw [hbatchUnfold, hcoin, bernoulliMeasure_bind hq _ hF']
        simp only [↓reduceIte, Bool.false_eq_true]
      have hMarg : (batchFrom N q (k + 1) j S₀).map (fun S => S.erase i)
          = batchFrom N q k (j + 1) S₀ := by
        have hqE : (q : ℝ≥0∞) ≤ 1 := by exact_mod_cast hq
        rw [hLaw, Measure.map_add _ _ herase, Measure.map_smul, Measure.map_smul,
          Measure.map_map herase hins, hBe]
        have hei : (fun S : Finset (Fin (N + 1)) => S.erase i) ∘ insert i
            = fun S => S.erase i := funext fun S => Finset.erase_insert_eq_erase S i
        rw [hei, hBe, ← add_smul, tsub_add_cancel_of_le hqE, one_smul]
      rw [hMarg]
      have h1 : Measurable (fun S : Finset (Fin (N + 1)) =>
          (1 - (q : ℝ≥0∞)) • Measure.dirac (S.erase i)) := Measurable.of_discrete
      have h2 : Measurable (fun S : Finset (Fin (N + 1)) =>
          (q : ℝ≥0∞) • Measure.dirac (insert i S)) := Measurable.of_discrete
      have hd1 : Measurable (fun S : Finset (Fin (N + 1)) => Measure.dirac (S.erase i)) :=
        Measurable.of_discrete
      have hd2 : Measurable (fun S : Finset (Fin (N + 1)) => Measure.dirac (insert i S)) :=
        Measurable.of_discrete
      rw [← bind_add_measure_fun _ h1 h2, ← bind_smul_measure_fun _ _ hd1,
        ← bind_smul_measure_fun _ _ hd2, Measure.bind_dirac_eq_map _ herase,
        Measure.bind_dirac_eq_map _ hins, hBe]
      exact hLaw

/-- The Poisson batch law is its `i`-erased marginal completed by a fresh `Bernoulli q`
    coin for record `i`. -/
theorem batchFrom_eq_mix_erase (N : ℕ) {q : ℝ≥0} (hq : q ≤ 1) (i : Fin (N + 1)) :
    batchFrom N q (N + 1) 0 ∅ = ((batchFrom N q (N + 1) 0 ∅).map (fun S => S.erase i)).bind
      (fun S => (1 - (q : ℝ≥0∞)) • Measure.dirac (S.erase i) +
        (q : ℝ≥0∞) • Measure.dirac (insert i S)) :=
  batchFrom_eq_mixAt N hq i (N + 1) 0 ∅ (Nat.zero_le _) (by rw [zero_add]; exact i.isLt)
    (by rw [zero_add]) (Finset.notMem_empty _)

/-! ## Sensitivity of `clippedBatchSumD`

For datasets adjacent at record `i` (`AdjAt`, record `i` of the second is `⊥`), stated at
the two branches `insert i S` and `S.erase i` of `batchFrom_eq_mix_erase`, for every `S`. -/

/-- Peeling record `i` off `clippedBatchSumD (insert i S)`. -/
lemma clippedBatchSumD_insert_erase (N dx d : ℕ)
    (grad : EuclideanSpace ℝ (Fin dx) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (C : ℝ≥0) (i : Fin (N + 1))
    (R : Fin (N + 1) → Option (EuclideanSpace ℝ (Fin dx))) (θ : EuclideanSpace ℝ (Fin d))
    (S : Finset (Fin (N + 1))) :
    clippedBatchSumD (N := N) grad C (insert i S) R θ
      = clipV C (gradBot grad (R i) θ)
        + clippedBatchSumD (N := N) grad C (S.erase i) R θ := by
  have hins : insert i S = insert i (S.erase i) := by
    by_cases h0 : i ∈ S
    · rw [Finset.insert_eq_self.mpr h0, Finset.insert_erase h0]
    · rw [Finset.erase_eq_self.mpr h0]
  rw [hins]
  unfold clippedBatchSumD
  rw [Finset.sum_insert (Finset.notMem_erase _ _)]

/-- On `S.erase i` the clipped batch sums of datasets adjacent at `i` agree. -/
lemma clippedBatchSumD_eq_of_adj (N dx d : ℕ)
    (grad : EuclideanSpace ℝ (Fin dx) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (C : ℝ≥0) (i : Fin (N + 1))
    {τ : Type*} {rec : τ → Fin (N + 1) → Option (EuclideanSpace ℝ (Fin dx))} {D₁ D₂ : τ}
    (hadj : AdjAt rec i D₁ D₂) (θ : EuclideanSpace ℝ (Fin d)) (S : Finset (Fin (N + 1))) :
    clippedBatchSumD (N := N) grad C (S.erase i) (rec D₁) θ
      = clippedBatchSumD (N := N) grad C (S.erase i) (rec D₂) θ := by
  unfold clippedBatchSumD
  exact Finset.sum_congr rfl (fun j hj => by rw [hadj.1 j (Finset.ne_of_mem_erase hj)])

/-- On the side where record `i` is `⊥`, inserting `i` does not change the sum. -/
lemma clippedBatchSumD_insert_eq_erase_of_adj (N dx d : ℕ)
    (grad : EuclideanSpace ℝ (Fin dx) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (C : ℝ≥0) (i : Fin (N + 1))
    {τ : Type*} {rec : τ → Fin (N + 1) → Option (EuclideanSpace ℝ (Fin dx))} {D₁ D₂ : τ}
    (hadj : AdjAt rec i D₁ D₂) (θ : EuclideanSpace ℝ (Fin d)) (S : Finset (Fin (N + 1))) :
    clippedBatchSumD (N := N) grad C (insert i S) (rec D₂) θ
      = clippedBatchSumD (N := N) grad C (S.erase i) (rec D₂) θ := by
  rw [clippedBatchSumD_insert_erase, hadj.2, gradBot_none, clipV_zero, zero_add]

/-- Inserting the differing record moves the sum by at most the clipping radius. -/
lemma norm_clippedBatchSumD_insert_sub_erase_le (N dx d : ℕ)
    (grad : EuclideanSpace ℝ (Fin dx) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (C : ℝ≥0) (i : Fin (N + 1))
    (R : Fin (N + 1) → Option (EuclideanSpace ℝ (Fin dx))) (θ : EuclideanSpace ℝ (Fin d))
    (S : Finset (Fin (N + 1))) :
    ‖clippedBatchSumD (N := N) grad C (insert i S) R θ
      - clippedBatchSumD (N := N) grad C (S.erase i) R θ‖ ≤ (C : ℝ) := by
  rw [clippedBatchSumD_insert_erase, add_sub_cancel_right]
  exact norm_clipV_le C.2 _

/-! ## The observable `obsPaper`

`obsPaper` resets the round's local slots `jv`/`bv`/`B`/`g` to fixed values and leaves
every other slot unchanged. -/

noncomputable def obsPaper (N d : ℕ) (m : PMem.heap) : PMem.heap :=
  PMem.set (setPoissonState N m 0 false ∅) (.vec d) (gV d).name 0

/-- Slot-name disequalities for the `d`-parametrised names, proved without `decide` on an
    open term. -/
private lemma gName_ne_thName (d : ℕ) : (gV d).name ≠ "th" := by
  show ("g" : String) ≠ "th"; decide

private lemma cntName_ne_jvName : cnt.name ≠ jv.name := by
  show ("cnt" : String) ≠ "jv"; decide

private lemma gName_ne_gtName (d : ℕ) : (gV d).name ≠ (gtV d).name := by
  show ("g" : String) ≠ "gt"; decide

/-- `obsPaper` preserves every slot other than `bv`/`B`/`jv`/`g`. -/
lemma getOther_obsPaper (N d : ℕ) (m : PMem.heap) {ty : Ty} {nm : String}
    (h1 : ¬ (ty = .bool ∧ nm = bv.name)) (h2 : ¬ (ty = .finset (N + 1) ∧ nm = (bchV N).name))
    (h3 : ¬ (ty = .nat ∧ nm = jv.name)) (h4 : ¬ (ty = .vec d ∧ nm = (gV d).name)) :
    PMem.get (obsPaper N d m) ty nm = PMem.get m ty nm := by
  have h1' := ty_ne_or_name_ne h1
  have h2' := ty_ne_or_name_ne h2
  have h3' := ty_ne_or_name_ne h3
  have h4' := ty_ne_or_name_ne h4
  unfold obsPaper setPoissonState
  rw [PMem.get_set_ne _ _ _ _ _ _ h4', PMem.get_set_ne _ _ _ _ _ _ h3',
    PMem.get_set_ne _ _ _ _ _ _ h2', PMem.get_set_ne _ _ _ _ _ _ h1']

lemma getGt_obsPaper (N d : ℕ) (m : PMem.heap) :
    getGt d (obsPaper N d m) = getGt d m :=
  getOther_obsPaper N d m
    (fun h => Ty.noConfusion h.1) (fun h => Ty.noConfusion h.1) (fun h => Ty.noConfusion h.1)
    (fun h => (gName_ne_gtName d).symm h.2)

lemma getCnt_obsPaper (N d : ℕ) (m : PMem.heap) :
    getCnt (obsPaper N d m) = getCnt m :=
  getOther_obsPaper N d m
    (fun h => Ty.noConfusion h.1) (fun h => Ty.noConfusion h.1) (fun h => cntName_ne_jvName h.2)
    (fun h => Ty.noConfusion h.1)

private lemma thName_ne_gtName (d : ℕ) : (thV d).name ≠ (gtV d).name := by
  show ("th" : String) ≠ "gt"; decide

lemma getDS_set (N dx : ℕ) (m : PMem.heap) {t : Ty} (n : String) (u : t.interp)
    (h : t ≠ .prod (.vec ((N + 1) * dx)) (.finset (N + 1)) ∨ n ≠ "D") :
    getDS N dx (PMem.set m t n u) = getDS N dx m := by
  unfold getDS
  rw [PMem.get_set_ne _ _ _ _ _ _ h]

lemma getR_set (N dx : ℕ) (m : PMem.heap) {t : Ty} (n : String) (u : t.interp)
    (h : t ≠ .prod (.vec ((N + 1) * dx)) (.finset (N + 1)) ∨ n ≠ "D") :
    getR N dx (PMem.set m t n u) = getR N dx m := by
  unfold getR
  rw [getDS_set N dx m n u h]

lemma getDS_obsPaper (N dx d : ℕ) (m : PMem.heap) :
    getDS N dx (obsPaper N d m) = getDS N dx m := by
  unfold obsPaper setPoissonState
  rw [getDS_set _ _ _ _ _ (Or.inl (fun h => Ty.noConfusion h)),
    getDS_set _ _ _ _ _ (Or.inl (fun h => Ty.noConfusion h)),
    getDS_set _ _ _ _ _ (Or.inl (fun h => Ty.noConfusion h)),
    getDS_set _ _ _ _ _ (Or.inl (fun h => Ty.noConfusion h))]

lemma getTh_obsPaper (N d : ℕ) (m : PMem.heap) :
    getTh d (obsPaper N d m) = getTh d m := by
  unfold obsPaper setPoissonState getTh
  rw [PMem.get_set_ne _ _ _ _ _ _ (Or.inr (gName_ne_thName d)),
    PMem.get_set_ne _ _ _ _ _ _ (Or.inl (fun h => Ty.noConfusion h)),
    PMem.get_set_ne _ _ _ _ _ _ (Or.inl (fun h => Ty.noConfusion h)),
    PMem.get_set_ne _ _ _ _ _ _ (Or.inl (fun h => Ty.noConfusion h))]

lemma getDS_set_gt (N dx d : ℕ) (m : PMem.heap) (u : EuclideanSpace ℝ (Fin d)) :
    getDS N dx (PMem.set m (.vec d) (gtV d).name u) = getDS N dx m :=
  getDS_set N dx m (t := .vec d) _ u (Or.inl (fun h => Ty.noConfusion h))

lemma getTh_set_gt (d : ℕ) (m : PMem.heap) (u : EuclideanSpace ℝ (Fin d)) :
    getTh d (PMem.set m (.vec d) (gtV d).name u) = getTh d m := by
  unfold getTh
  exact PMem.get_set_ne _ _ _ _ _ _ (Or.inr (thName_ne_gtName d).symm)

lemma getDS_set_th (N dx d : ℕ) (m : PMem.heap) (u : EuclideanSpace ℝ (Fin d)) :
    getDS N dx (PMem.set m (.vec d) (thV d).name u) = getDS N dx m :=
  getDS_set N dx m (t := .vec d) _ u (Or.inl (fun h => Ty.noConfusion h))

lemma getDS_set_cnt (N dx : ℕ) (m : PMem.heap) (u : ℕ) :
    getDS N dx (PMem.set m .nat cnt.name u) = getDS N dx m :=
  getDS_set N dx m (t := .nat) _ u (Or.inl (fun h => Ty.noConfusion h))

lemma getTh_set_cnt (d : ℕ) (m : PMem.heap) (u : ℕ) :
    getTh d (PMem.set m .nat cnt.name u) = getTh d m := by
  unfold getTh
  exact PMem.get_set_ne _ _ _ _ _ _ (Or.inl (fun h => Ty.noConfusion h))

lemma getCnt_set_gt (d : ℕ) (m : PMem.heap) (u : EuclideanSpace ℝ (Fin d)) :
    getCnt (PMem.set m (.vec d) (gtV d).name u) = getCnt m := by
  unfold getCnt
  exact PMem.get_set_ne _ _ _ _ _ _ (Or.inl (fun h => Ty.noConfusion h))

lemma getGt_set_th (d : ℕ) (m : PMem.heap) (u : EuclideanSpace ℝ (Fin d)) :
    getGt d (PMem.set m (.vec d) (thV d).name u) = getGt d m := by
  unfold getGt
  exact PMem.get_set_ne _ _ _ _ _ _ (Or.inr (thName_ne_gtName d))

lemma getCnt_set_th (d : ℕ) (m : PMem.heap) (u : EuclideanSpace ℝ (Fin d)) :
    getCnt (PMem.set m (.vec d) (thV d).name u) = getCnt m := by
  unfold getCnt
  exact PMem.get_set_ne _ _ _ _ _ _ (Or.inl (fun h => Ty.noConfusion h))

/-- The shift between the two Gaussian means when record `i` is in the batch vs not. -/
noncomputable def shiftPaper (N dx d : ℕ)
    (grad : EuclideanSpace ℝ (Fin dx) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (C : ℝ≥0) (i : Fin (N + 1))
    (m : PMem.heap) (S : Finset (Fin (N + 1))) : EuclideanSpace ℝ (Fin d) :=
  clippedBatchSumD (N := N) grad C (insert i S) (getR N dx m) (getTh d m)
    - clippedBatchSumD (N := N) grad C (S.erase i) (getR N dx m) (getTh d m)

/-- `shiftPaper` is bounded by the clipping radius. -/
lemma norm_shiftPaper_le (N dx d : ℕ)
    (grad : EuclideanSpace ℝ (Fin dx) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (C : ℝ≥0) (i : Fin (N + 1))
    (m : PMem.heap) (S : Finset (Fin (N + 1))) :
    ‖shiftPaper N dx d grad C i m S‖ ≤ (C : ℝ) :=
  norm_clippedBatchSumD_insert_sub_erase_le N dx d grad C i (getR N dx m)
    (getTh d m) S

lemma measurable_guard_cnt (T : ℕ) : Measurable (fun m : PMem.heap => decide (getCnt m < T)) :=
  (measurable_from_top : Measurable (fun n : ℕ => decide (n < T))).comp measurable_getCnt

/-- The guard of the round loop, `cnt < T`, as the expression the derivations name. -/
noncomputable def guardE (T : ℕ) : BExpr PMem :=
  ⟨fun m => decide (getCnt m < T), measurable_guard_cnt T⟩

lemma esem_guardE (T : ℕ) (m : PMem.heap) : esem (guardE T) m = decide (getCnt m < T) := rfl

/-- Closes a goal `t ≠ u ∨ x ≠ y` between two slots whose names are literals. -/
macro "slot_ne" : tactic =>
  `(tactic| first
    | (apply Or.inl; intro h; cases h; done)
    | (apply Or.inr; decide)
    | (apply Or.inr; simp only [gV, thV, gtV, bchV, dsV, cnt, jv, bv]; decide))

end DPSGDPaper
