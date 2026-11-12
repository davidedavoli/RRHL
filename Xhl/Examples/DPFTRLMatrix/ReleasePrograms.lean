import Xhl.Logic.Equiv.Frame
import Xhl.Examples.DPFTRLMatrix.Program
import Xhl.Examples.DPSGD.Shared.Paper

open Continuous

/-!
# DP-FTRL with a matrix mechanism: the program

The program of Figure 6 (§5.3): matrix-mechanism DP-FTRL with multiple participation.  The
round releases the model alone; the aggregates `Y[r]` are internal state.  Tree aggregation
with single participation is an instance of the same program (the tree encoder, `Deriv.lean`).

`dpftrlGen` is the program over the generic parameters `TParams`/`TVars`; `tParamsP`,
`tVarsP`, `tOKP`, `mCntOKP` instantiate it on the memory model of `DPSGD/Shared/Paper.lean`;
`dpftrl` is the same program written with the `⟪…⟫` quoter of `GameSyntax.lean`, equal to
`dpftrlGen` by `rfl` (`dpftrl_eq`).
-/

open MeasureTheory ProbabilityTheory ENNReal
open scoped NNReal

variable {ident : Type} {M : MemType ident}

namespace DPFTRL

open Continuous

variable {d e n T R : ℕ} {τ : Ty} [NeZero T] [NeZero R]

/-! ## The program -/

section Program

variable (p : TParams d e n T R τ) (v : TVars ident d T R τ) (tv rv : Vars ident .nat)

/-- `H[t] := Σ_{i<n} part(i,t)·clip_Γ(∇ℓ(θ,D[i]))`: the round's gradient sum (line 4 of
    Figure 6).  Its measurability rests on the well-formedness `hok`. -/
noncomputable def batchEM (hok : TOK p v) : Expr M (.vec (T * d)) :=
  ⟨fun h => setBlk (M.get h (.vec (T * d)) v.H.name) (Fin.ofNat T (M.get h .nat tv.name))
      (batchStep p (M.get h .nat tv.name) (M.get h τ v.D.name) (M.get h (.vec d) v.x.name)), by
    set Φ : (EuclideanSpace ℝ (Fin (T * d)) × τ.interp × EuclideanSpace ℝ (Fin d)) × ℕ →
        EuclideanSpace ℝ (Fin (T * d)) :=
      fun ((H, D, θ), t) => setBlk H (Fin.ofNat T t) (batchStep p t D θ)
    have hΦ : Measurable Φ := by
      refine measurable_from_prod_countable_left (fun tt => ?_)
      exact (continuous_setBlk (Fin.ofNat T tt)).measurable.comp (measurable_fst.prodMk
        ((measurable_batchStep hok.grad hok.present hok.recVal tt).comp measurable_snd))
    exact hΦ.comp (((M.get_measurable (.vec (T * d)) v.H.name).prodMk
      ((M.get_measurable τ v.D.name).prodMk (M.get_measurable (.vec d) v.x.name))).prodMk
      (M.get_measurable .nat tv.name))⟩

/-- `Y[r] := (C · H)_r + z`.  It reads only the encoder `C`, so the banded study
    (`DPFTRL.Band`) reuses it. -/
noncomputable def relEM (C : Fin R → Fin T → ℝ) (v : TVars ident d T R τ)
    (rv : Vars ident .nat) : Expr M (.vec (R * d)) :=
  ⟨fun h => setBlk (M.get h (.vec (R * d)) v.Y.name) (Fin.ofNat R (M.get h .nat rv.name))
      (rowMean C (Fin.ofNat R (M.get h .nat rv.name)) (M.get h (.vec (T * d)) v.H.name)
        + M.get h (.vec d) v.z.name), by
    set Φ : (EuclideanSpace ℝ (Fin (R * d)) × EuclideanSpace ℝ (Fin (T * d)) ×
        EuclideanSpace ℝ (Fin d)) × ℕ → EuclideanSpace ℝ (Fin (R * d)) :=
      fun ((Y, H, z), r) => setBlk Y (Fin.ofNat R r) (rowMean C (Fin.ofNat R r) H + z)
    have hΦ : Measurable Φ := measurable_from_prod_countable_left fun rr =>
      (continuous_setBlk (Fin.ofNat R rr)).measurable.comp (measurable_fst.prodMk
        (((continuous_rowMean (Fin.ofNat R rr)).measurable.comp
          (measurable_fst.comp measurable_snd)).add (measurable_snd.comp measurable_snd)))
    exact hΦ.comp (((M.get_measurable (.vec (R * d)) v.Y.name).prodMk
      ((M.get_measurable (.vec (T * d)) v.H.name).prodMk (M.get_measurable (.vec d) v.z.name))).prodMk
      (M.get_measurable .nat rv.name))⟩

/-- `ŝ := (B·Y)_t`: the private prefix sum of the round, kept in `acc`. -/
noncomputable def sumEM : Expr M (.vec d) :=
  ⟨fun h => rowDec p (M.get h .nat tv.name) (M.get h (.vec (R * d)) v.Y.name), by
    set Φ : EuclideanSpace ℝ (Fin (R * d)) × ℕ → EuclideanSpace ℝ (Fin d) :=
      fun q => rowDec p q.2 q.1
    have hΦ : Measurable Φ := measurable_from_prod_countable_left fun tt =>
      (continuous_rowDec (p := p) tt).measurable
    exact hΦ.comp ((M.get_measurable (.vec (R * d)) v.Y.name).prodMk
      (M.get_measurable .nat tv.name))⟩

/-- `θ := −(1/lam)·ŝ`: the regularized-leader step. -/
noncomputable def modelEM : Expr M (.vec d) :=
  ⟨fun h => (-(1 / p.lam)) • M.get h (.vec d) v.acc.name,
    (M.get_measurable (.vec d) v.acc.name).const_smul (-(1 / p.lam))⟩

/-- `done(r) = t`: release `r` is made at the round at which its row completes. -/
noncomputable def dueE : BExpr M :=
  ⟨fun h => decide (doneN p (Fin.ofNat R (M.get h .nat rv.name)) = M.get h .nat tv.name),
    (measurable_of_countable (fun q : ℕ × ℕ => decide (doneN p (Fin.ofNat R q.1) = q.2))).comp
      ((M.get_measurable .nat rv.name).prodMk (M.get_measurable .nat tv.name))⟩

/-- `k < K` on a counter. -/
def ltCE (x : Vars ident .nat) (K : ℕ) : BExpr M := ltW x K

/-- The aggregate due at `r`, if any: sample the noise and write the row.  Nothing is
    released here. -/
noncomputable def relStepM : Cmd ident M :=
  Cmd.seq (Cmd.cond (dueE p tv rv)
    (Cmd.seq (Cmd.random v.z (noiseKernelE p.σ2)) (Cmd.assign v.Y (relEM p.C v rv))) Cmd.skip)
    (Cmd.assign rv (incW rv))

/-- One round (the body of the outer loop of Figure 6). -/
noncomputable def roundM (hok : TOK p v) : Cmd ident M :=
  Cmd.seq (Cmd.assign v.H (batchEM p v tv hok))
    (Cmd.seq (Cmd.assign rv (Expr.cst (t := .nat) 0))
      (Cmd.seq (Cmd.while (ltCE rv R) (relStepM p v tv rv))
        (Cmd.seq (Cmd.assign v.acc (sumEM p v tv))
          (Cmd.seq (Cmd.assign v.x (modelEM p v))
            (Cmd.seq (Cmd.release (Expr.var v.x)) (Cmd.assign tv (incW tv)))))))

/-- The program: the model, the history and the releases start at zero, then `T` rounds. -/
noncomputable def dpftrlGen (hok : TOK p v) : Cmd ident M :=
  Cmd.seq (Cmd.assign v.x (Expr.cst (t := .vec d) 0))
    (Cmd.seq (Cmd.assign v.H (Expr.cst (t := .vec (T * d)) 0))
      (Cmd.seq (Cmd.assign v.Y (Expr.cst (t := .vec (R * d)) 0))
        (Cmd.seq (Cmd.assign tv (Expr.cst (t := .nat) 0))
          (Cmd.while (ltCE tv T) (roundM p v tv rv hok)))))

end Program

variable {p : TParams d e n T R τ} {v : TVars ident d T R τ} {tv rv : Vars ident .nat}

/-- The counters are variables of their own. -/
structure MCntOK (v : TVars ident d T R τ) (tv rv : Vars ident .nat) : Prop where
  tx : tv.name ≠ v.x.name
  tacc : tv.name ≠ v.acc.name
  tz : tv.name ≠ v.z.name
  ti : tv.name ≠ v.i.name
  tD : tv.name ≠ v.D.name
  tH : tv.name ≠ v.H.name
  tY : tv.name ≠ v.Y.name
  rx : rv.name ≠ v.x.name
  racc : rv.name ≠ v.acc.name
  rz : rv.name ≠ v.z.name
  ri : rv.name ≠ v.i.name
  rD : rv.name ≠ v.D.name
  rH : rv.name ≠ v.H.name
  rY : rv.name ≠ v.Y.name
  tr : tv.name ≠ rv.name

abbrev tT (tv : Vars ident .nat) (h : M.heap) : ℕ := M.get h .nat tv.name
abbrev tIN (v : TVars ident d T R τ) (h : M.heap) : ℕ := M.get h .nat v.i.name


end DPFTRL

/-! ## The instance on the memory model of `DPSGD/Shared/Paper.lean` -/

namespace DPFTRL

open Continuous DPSGDPaper

/-- The history `H`, as a ground `Vars` constant for the quoter's splices. -/
def hMV (T d : ℕ) : Vars String (.vec (T * d)) := ⟨"H"⟩

/-- The release vector `Y`. -/
def yMV (R d : ℕ) : Vars String (.vec (R * d)) := ⟨"Y"⟩

variable (N dx d T R : ℕ) [NeZero T] [NeZero R]
  (grad : EuclideanSpace ℝ (Fin dx) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
  (Cl : ℝ) (σ2 : ℝ≥0) (C : Fin R → Fin T → ℝ) (B : Fin T → Fin R → ℝ) (lam : ℝ)
  (part : ℕ → ℕ → ℝ)

/-- The variables, on `PMem`. -/
def tVarsP : TVars String d T R (.prod (.vec ((N + 1) * dx)) (.finset (N + 1))) where
  x := ⟨"th"⟩
  acc := ⟨"acc"⟩
  z := ⟨"z"⟩
  i := ⟨"i"⟩
  D := ⟨"D"⟩
  H := ⟨"H"⟩
  Y := ⟨"Y"⟩
  distinct := by simp [List.nodup_cons]

def tvMP : Vars String .nat := ⟨"t"⟩
def rvMP : Vars String .nat := ⟨"r"⟩

/-- The parameters, on the dataset of `DPSGD/Shared/Paper.lean`. -/
noncomputable def tParamsP :
    TParams d dx (N + 1) T R (.prod (.vec ((N + 1) * dx)) (.finset (N + 1))) where
  Cl := Cl
  σ2 := σ2
  C := C
  B := B
  lam := lam
  part := part
  grad := fun θ r => r.elim 0 (fun x => grad x θ)
  grad_bot := fun _ => rfl
  record := fun D i => recBotN N dx D i

lemma tOKP (hgrad : Measurable (fun p : EuclideanSpace ℝ (Fin dx) × EuclideanSpace ℝ (Fin d) =>
      grad p.1 p.2)) :
    TOK (tParamsP N dx d T R grad Cl σ2 C B lam part) (tVarsP N dx d T R) where
  grad := by
    show Measurable (fun q : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin dx) =>
      grad q.2 q.1)
    exact hgrad.comp measurable_swap
  present := measurableSet_recBotN_isSome N dx
  recVal := measurable_recBotN_getD N dx

lemma mCntOKP : MCntOK (tVarsP N dx d T R) tvMP rvMP where
  tx := show "t" ≠ "th" by decide
  tacc := show "t" ≠ "acc" by decide
  tz := show "t" ≠ "z" by decide
  ti := show "t" ≠ "i" by decide
  tD := show "t" ≠ "D" by decide
  tH := show "t" ≠ "H" by decide
  tY := show "t" ≠ "Y" by decide
  rx := show "r" ≠ "th" by decide
  racc := show "r" ≠ "acc" by decide
  rz := show "r" ≠ "z" by decide
  ri := show "r" ≠ "i" by decide
  rD := show "r" ≠ "D" by decide
  rH := show "r" ≠ "H" by decide
  rY := show "r" ≠ "Y" by decide
  tr := show "t" ≠ "r" by decide

/-! ## The program, with the high-level syntax -/

/-- The matrix-mechanism DP-FTRL program on `PMem`, written with the quoter (Figure 6). -/
noncomputable def dpftrl
    (hgrad : Measurable (fun p : EuclideanSpace ℝ (Fin dx) × EuclideanSpace ℝ (Fin d) =>
      grad p.1 p.2)) : Cmd String PMem :=
  ⟪ (thV d) ← (0 : EuclideanSpace ℝ (Fin d)) ;
    ( (hMV T d) ← (0 : EuclideanSpace ℝ (Fin (T * d))) ;
    ( (yMV R d) ← (0 : EuclideanSpace ℝ (Fin (R * d))) ;
    ( tvMP ← (0 : ℕ) ;
    while tvMP < T do
      ( ~(Cmd.assign (hMV T d) (batchEM (tParamsP N dx d T R grad Cl σ2 C B lam part) (tVarsP N dx d T R) tvMP
            (tOKP N dx d T R grad Cl σ2 C B lam part hgrad))) ;
        ( rvMP ← (0 : ℕ) ;
          ( while rvMP < R do
              ( if doneN (tParamsP N dx d T R grad Cl σ2 C B lam part) (Fin.ofNat R rvMP) = tvMP then
                  ( (zV d) ←$ 𝒩(fun _ => (0 : EuclideanSpace ℝ (Fin d)), measurable_const, σ2) ;
                    ~(Cmd.assign (yMV R d) (relEM C (tVarsP N dx d T R) rvMP)) )
                else skip fi ;
                rvMP ← rvMP + (1 : ℕ) )
            od ;
            ( ~(Cmd.assign (accV d) (sumEM (tParamsP N dx d T R grad Cl σ2 C B lam part) (tVarsP N dx d T R) tvMP)) ;
              ( ~(Cmd.assign (thV d) (modelEM (tParamsP N dx d T R grad Cl σ2 C B lam part) (tVarsP N dx d T R))) ;
                ( release (thV d) ;
                  tvMP ← tvMP + (1 : ℕ) ) ) ) ) ) )
    od ) ) ) ⟫

/-- The quoted program is the generic program at the instance, by `rfl`. -/
lemma dpftrl_eq
    (hgrad : Measurable (fun p : EuclideanSpace ℝ (Fin dx) × EuclideanSpace ℝ (Fin d) =>
      grad p.1 p.2)) :
    dpftrl N dx d T R grad Cl σ2 C B lam part hgrad
      = dpftrlGen (tParamsP N dx d T R grad Cl σ2 C B lam part) (tVarsP N dx d T R) tvMP rvMP
          (tOKP N dx d T R grad Cl σ2 C B lam part hgrad) := rfl

/-! ## The program again, in the paper's notation

`dpftrl` restated with the paper-style notation of `GameSyntax.lean` and checked equal by
`rfl`.  The local notations only rename program variables, dataset records (`D⁅i⁆`, `⊥` for
an absent record) and fixed functions (`∇ℓ` extended to `⊥` by `0`, `clip`); derived
quantities such as the row `∑ s, C r s • blk H s` are spelled out, and `done` is a
function of `C`, not a parameter.
-/

section PaperSyntax

variable (hgrad : Measurable (fun p : EuclideanSpace ℝ (Fin dx) × EuclideanSpace ℝ (Fin d) =>
  grad p.1 p.2))

local notation:max "dpftrl!" => dpftrl N dx d T R grad Cl σ2 C B lam part hgrad
local notation:max "p!" => tParamsP N dx d T R grad Cl σ2 C B lam part
local notation:max "v!" => tVarsP N dx d T R

/-- Measurability of the three quoted expressions that rest on `hgrad`. -/
local macro_rules
  | `(tactic| xhl_measurable) =>
    `(tactic| first
      | exact (batchEM p! v! tvMP (tOKP N dx d T R grad Cl σ2 C B lam part hgrad)).measurable
      | exact (relEM C v! rvMP).measurable
      | exact (sumEM p! v! tvMP).measurable)

local notation:max "θ" => ⌞thV d⌟
local notation:max "ŝ" => ⌞accV d⌟
local notation:max "z" => ⌞zV d⌟
local notation:max "H" => ⌞hMV T d⌟
local notation:max "Y" => ⌞yMV R d⌟
local notation:max "t" => ⌞tvMP⌟
local notation:max "r" => ⌞rvMP⌟
local notation:max "done" =>
  DPFTRL.doneN (tParamsP N dx d T R grad Cl σ2 C B lam part)
set_option quotPrecheck false in
local notation:max "D⁅" x "⁆" => recBotN N dx (⌞dsV N dx⌟) x
local notation:max "∇ℓ" => (fun θ' r' => Option.elim r' 0 (fun x' => grad x' θ'))
local notation:max "clip" => Continuous.clipV

/-- Matrix-mechanism DP-FTRL as Figure 6 displays it. -/
example :
    dpftrl! =
    ⟪ θ := (0 : EuclideanSpace ℝ (Fin d)) ;
      ( H := (0 : EuclideanSpace ℝ (Fin (T * d))) ;
      ( Y := (0 : EuclideanSpace ℝ (Fin (R * d))) ;
      ( t := 0 ;
      while t < T do
        ( H := setBlk H (Fin.ofNat T t)
                 (∑ i ∈ Finset.range (N + 1),
                   part i t • clip Cl (∇ℓ θ D⁅i⁆)) ;
          ( r := 0 ;
            ( while r < R do
                ( if done (Fin.ofNat R r) = t then
                    ( z ∼ 𝒩(0, σ2) ;
                      Y := setBlk Y (Fin.ofNat R r)
                        ((∑ s, C (Fin.ofNat R r) s • blk H s) + z) )
                  else skip fi ;
                  r := r + 1 )
              od ;
              ( ŝ := ∑ ρ, B (Fin.ofNat T t) ρ • blk Y ρ ;
                ( θ := (-(1 / lam)) • ŝ ;
                  ( release θ ;
                    t := t + 1 ) ) ) ) ) )
      od ) ) ) ⟫ := rfl

end PaperSyntax

end DPFTRL
