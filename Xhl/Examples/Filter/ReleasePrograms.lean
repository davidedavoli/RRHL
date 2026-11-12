import Xhl.Examples.DPSGD.Shared.Paper
import Xhl.Examples.Filter.FilterGD

open Continuous

/-!
# Noisy gradient descent with per-record Rényi filters: the program

The program of Figure 5 (§5.2), after Feldman–Zrnic's Algorithm 3: `filterGen` over the
generic parameters of `FilterGD.lean`, its instance on the memory model of
`DPSGD/Shared/Paper.lean`, and the quoted program `filter` (equal by `rfl`, `filter_eq`).

The program carries no Rényi order: the meter `s[i]` accumulates squared norms, and the
filter is the clipping radius `min{Γ, √max(0, B − s[i])}`.  The order `α` appears only in
the budgets of the derivation.
-/

open MeasureTheory ProbabilityTheory ENNReal
open scoped NNReal

variable {ident : Type} {M : MemType ident}

namespace RenyiFilter

open Continuous

variable {d e n : ℕ} {τ : Ty}

/-! ## The program -/

section Program

variable (p : TapParams d e n τ) (v : TapVars ident d n τ) (tv : Vars ident .nat)

/-- The guard of the record loop: `i < n`. -/
def guardIT : BExpr M :=
  ⟨fun h => decide (M.get h .nat v.i.name < n),
    (measurable_from_top : Measurable (fun k : ℕ => decide (k < n))).comp
      (M.get_measurable .nat v.i.name)⟩

/-- The guard of the rounds: `t < T`. -/
def guardTT (T : ℕ) : BExpr M :=
  ⟨fun h => decide (M.get h .nat tv.name < T),
    (measurable_from_top : Measurable (fun k : ℕ => decide (k < T))).comp
      (M.get_measurable .nat tv.name)⟩

/-- One round: the record loop, the noise, the update, the release, the counter. -/
noncomputable def roundT (hok : TapOK p v) : Cmd ident M :=
  Cmd.seq (initT v) (Cmd.seq (Cmd.while (guardIT v) (bodyT p v hok))
    (Cmd.seq (Cmd.random v.z (noiseKernelE p.nvar)) (Cmd.seq (Cmd.assign v.x (updET p v tv))
      (Cmd.seq (Cmd.release (Expr.var v.x)) (Cmd.assign tv (incW tv))))))

/-- The rounds: `T` of them, each releasing the model. -/
noncomputable def roundsT (hok : TapOK p v) (T : ℕ) : Cmd ident M :=
  Cmd.seq (Cmd.assign tv (Expr.cst (t := .nat) 0))
    (Cmd.while (guardTT tv T) (roundT p v tv hok))

/-- The program: the initialization, then the rounds. -/
noncomputable def filterGen (hok : TapOK p v) (T : ℕ) : Cmd ident M :=
  Cmd.seq (initGDT v) (roundsT p v tv hok T)

end Program

variable {p : TapParams d e n τ} {v : TapVars ident d n τ} {tv : Vars ident .nat}

/-- The round counter is a variable of its own. -/
structure TvOKT (v : TapVars ident d n τ) (tv : Vars ident .nat) : Prop where
  x : tv.name ≠ v.x.name
  acc : tv.name ≠ v.acc.name
  z : tv.name ≠ v.z.name
  s : tv.name ≠ v.s.name
  i : tv.name ≠ v.i.name
  D : tv.name ≠ v.D.name

/-- The round counter, as a natural number. -/
abbrev fT (tv : Vars ident .nat) (h : M.heap) : ℕ := M.get h .nat tv.name

end RenyiFilter

/-! ## The instance on the memory model of `DPSGD/Shared/Paper.lean` -/

namespace RenyiFilter

open Continuous DPSGDPaper

/-- The record index `i`, as a ground `Vars` constant for the quoter's guards. -/
def iV : Vars String .nat := ⟨"i"⟩

/-- The round counter `t`. -/
def tvP : Vars String .nat := ⟨"t"⟩

/-- The per-record meters `s`, accumulating squared norms. -/
def sV (N : ℕ) : Vars String (.vec (N + 1)) := ⟨"s"⟩

variable (N dx d : ℕ)
  (grad : EuclideanSpace ℝ (Fin dx) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
  (C : ℝ) (nvar : ℝ≥0) (Bnorm : ℝ) (η : ℕ → ℝ)

/-- The variables, on `PMem`: the model `th`, the accumulator `acc`, the noise `z`, the
    meters `s`, the record index `i`, the dataset `D`; the round counter is `t`. -/
def fzVarsP : TapVars String d (N + 1) (.prod (.vec ((N + 1) * dx)) (.finset (N + 1))) where
  x := ⟨"th"⟩
  acc := ⟨"acc"⟩
  z := ⟨"z"⟩
  s := ⟨"s"⟩
  i := ⟨"i"⟩
  D := ⟨"D"⟩
  distinct := by simp [List.nodup_cons]

/-- The parameters, on the dataset of `DPSGD/Shared/Paper.lean`.  **No Rényi order.** -/
noncomputable def fzParamsP :
    TapParams d dx (N + 1) (.prod (.vec ((N + 1) * dx)) (.finset (N + 1))) where
  Cl := C
  nvar := nvar
  Bnorm := Bnorm
  η := η
  grad := fun θ r => r.elim 0 (fun x => grad x θ)
  grad_bot := fun _ => rfl
  record := fun D i => recBotN N dx D i

lemma fzOKP (hgrad : Measurable (fun p : EuclideanSpace ℝ (Fin dx) × EuclideanSpace ℝ (Fin d) =>
      grad p.1 p.2)) :
    TapOK (fzParamsP N dx d grad C nvar Bnorm η) (fzVarsP N dx d) where
  grad := by
    show Measurable (fun q : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin dx) =>
      grad q.2 q.1)
    exact hgrad.comp measurable_swap
  present := measurableSet_recBotN_isSome N dx
  recVal := measurable_recBotN_getD N dx

lemma fzTvOKP : TvOKT (fzVarsP N dx d) tvP where
  x := show "t" ≠ "th" by decide
  acc := show "t" ≠ "acc" by decide
  z := show "t" ≠ "z" by decide
  s := show "t" ≠ "s" by decide
  i := show "t" ≠ "i" by decide
  D := show "t" ≠ "D" by decide

/-! ## The program, with the high-level syntax -/

/-- The filtered noisy gradient descent of Figure 5 on `PMem`, written with the quoter. -/
noncomputable def filter
    (hgrad : Measurable (fun p : EuclideanSpace ℝ (Fin dx) × EuclideanSpace ℝ (Fin d) =>
      grad p.1 p.2)) (T : ℕ) : Cmd String PMem :=
  ⟪ ( (sV N) ← (0 : EuclideanSpace ℝ (Fin (N + 1))) ;
      (thV d) ← (0 : EuclideanSpace ℝ (Fin d)) ) ;
    ( tvP ← (0 : ℕ) ;
    while tvP < T do
      ( ( iV ← (0 : ℕ) ; (accV d) ← (0 : EuclideanSpace ℝ (Fin d)) ) ;
        ( while iV < N + 1 do
            ( ~(Cmd.assign (accV d) (accET (fzParamsP N dx d grad C nvar Bnorm η) (fzVarsP N dx d)
                  (fzOKP N dx d grad C nvar Bnorm η hgrad))) ;
              ( ~(Cmd.assign (sV N) (sET (fzParamsP N dx d grad C nvar Bnorm η) (fzVarsP N dx d)
                  (fzOKP N dx d grad C nvar Bnorm η hgrad))) ;
                iV ← iV + (1 : ℕ) ) )
          od ;
          ( (zV d) ←$ 𝒩(fun _ => (0 : EuclideanSpace ℝ (Fin d)), measurable_const, nvar) ;
            ( ~(Cmd.assign (thV d)
                  (updET (fzParamsP N dx d grad C nvar Bnorm η) (fzVarsP N dx d) tvP)) ;
              ( release (thV d) ;
                tvP ← tvP + (1 : ℕ) ) ) ) ) )
    od ) ⟫

/-- The quoted program is the generic program at the instance, by `rfl`. -/
lemma filter_eq
    (hgrad : Measurable (fun p : EuclideanSpace ℝ (Fin dx) × EuclideanSpace ℝ (Fin d) =>
      grad p.1 p.2)) (T : ℕ) :
    filter N dx d grad C nvar Bnorm η hgrad T
      = filterGen (fzParamsP N dx d grad C nvar Bnorm η) (fzVarsP N dx d) tvP
          (fzOKP N dx d grad C nvar Bnorm η hgrad) T := rfl

/-! ## The program again, in the paper's notation

`filter` restated with the paper-style notation of `GameSyntax.lean` and checked equal by
`rfl`.  The local notations only rename program variables, dataset records (`D⁅i⁆`, `⊥` for
an absent record) and fixed functions (`∇ℓ` extended to `⊥` by `0`, `clip`); the radius
`min{Γ, √max(0, B − s[i])}` is spelled out.  `clipV r g = g` when `‖g‖ ≤ r`, so this is
Feldman–Zrnic's `(g/‖g‖)·min{‖g‖, Γ, √(B − s[i])}`.
-/

section PaperSyntax

variable (hgrad : Measurable (fun p : EuclideanSpace ℝ (Fin dx) × EuclideanSpace ℝ (Fin d) =>
  grad p.1 p.2))

local notation:max "p!" => fzParamsP N dx d grad C nvar Bnorm η
local notation:max "v!" => fzVarsP N dx d

/-- Measurability of the three quoted expressions automation does not prove. -/
local macro_rules
  | `(tactic| xhl_measurable) =>
    `(tactic| first
      | exact (accET p! v! (fzOKP N dx d grad C nvar Bnorm η hgrad)).measurable
      | exact (sET p! v! (fzOKP N dx d grad C nvar Bnorm η hgrad)).measurable
      | exact (updET p! v! tvP).measurable)

local notation:max "θ" => ⌞thV d⌟
local notation:max "acc" => ⌞accV d⌟
local notation:max "z" => ⌞zV d⌟
local notation:max "s" => ⌞sV N⌟
local notation:max "i" => ⌞iV⌟
local notation:max "t" => ⌞tvP⌟
set_option quotPrecheck false in
local notation:max "D⁅" x "⁆" => recBotN N dx (⌞dsV N dx⌟) x
local notation:max "∇ℓ" => (fun θ' r' => Option.elim r' 0 (fun x' => grad x' θ'))
local notation:max "clip" => Continuous.clipV

/-- Noisy gradient descent with filtering, as Figure 5 displays it. -/
example (T : ℕ) :
    filter N dx d grad C nvar Bnorm η hgrad T =
    ⟪ ( s := 0 ; θ := 0 ) ;
      ( t := 0 ;
      while t < T do
        ( ( i := 0 ; acc := 0 ) ;
          ( while i < N + 1 do
              ( acc := acc +
                  clip (min C (Real.sqrt (max 0 (Bnorm - remAt s i)))) (∇ℓ θ D⁅i⁆) ;
                ( s := s +
                    ‖clip (min C (Real.sqrt (max 0 (Bnorm - remAt s i)))) (∇ℓ θ D⁅i⁆)‖ ^ 2
                      • eAt (N + 1) i ;
                  i := i + 1 ) )
            od ;
            ( z ∼ 𝒩(0, nvar) ;
              ( θ := θ - (η t / ((N + 1 : ℕ) : ℝ)) • (acc + z) ;
                ( release θ ;
                  t := t + 1 ) ) ) ) )
      od ) ⟫ := rfl

end PaperSyntax

end RenyiFilter

