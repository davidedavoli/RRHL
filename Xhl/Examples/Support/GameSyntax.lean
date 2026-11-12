import Xhl.Examples.Support.Samplers
import Xhl.Examples.Support.GaussVec

/-!
# Surface syntax for the paper's programs: `pvar`, `e⟪…⟫`, `⟪…⟫`

Quoters that let a case study write its program as the paper prints it, then check by
`rfl` that the quoted text is the intended `Cmd`/`Expr` term.

* `pvar M x : t` declares a ground program variable and its reader.
* `e⟪…⟫` quotes an expression: the program variables are replaced by reads of the memory,
  and the measurability proof is found by automation, so `esem` of a quoted expression
  reduces by `rfl`.
* `⟪…⟫` quotes a command.  Its sampling forms are exactly `x ←$ Bern(p)` and
  `x ←$ 𝒩(μ, hμ, v)` (with the alias `x ∼ 𝒩(c, v)`); there is no form taking an arbitrary
  kernel, so "the program samples only from these primitives" is a syntactic property.
  The quoter sits in `Examples/Support` because those kernels are defined here.

The aliases `:=`, `∼ 𝒩(c, v)`, `release e` and the escape `⌞…⌟` are used by the
`example … = ⟪ paper text ⟫ := rfl` blocks next to each quoted program (e.g.
`Filter/ReleasePrograms.lean`).
-/

open Lean Meta Elab Term
open Continuous

namespace Continuous

variable {ident : Type} {M : MemType ident}

/-! ## `pvar`: declaring program variables -/

abbrev MemType.Var (_M : MemType ident) (t : Ty) : Type := Vars ident t

syntax (name := cpvarCmd) "pvar " term:max ident " : " term : command

macro_rules
  | `(pvar $M $x : $ty) => do
      let nameStr := x.getId.eraseMacroScopes.getString!
      let lit := Syntax.mkStrLit nameStr
      let readerName := "get" ++ nameStr.capitalize
      let g := mkIdentFrom x (Name.mkSimple readerName)
      `(abbrev $x : ($M).Var $ty := ⟨$lit⟩
        noncomputable def $g (m : ($M).heap) : Ty.interp $ty :=
          ($M).get m $ty (Vars.name $x))

/-!
## `⌞…⌟`: program-variable escapes

A bare identifier can only name a ground program variable (a global constant of type
`Vars ident t`).  Inside `e⟪…⟫`, `⌞v⌟` reads the program variable denoted by an arbitrary
term `v : Vars ident t`, e.g. `⌞thV d⌟`; outside the quoter it elaborates to `v`.

The variables are abstracted in order of first textual occurrence, escapes before bare
identifiers, so a paper listing matches a hand-built `Expr` by `rfl` only if its
first-occurrence order agrees with the expression's argument order. -/

syntax:max (name := pvarEscape) "⌞" term "⌟" : term

open Lean Elab Term in
@[term_elab Continuous.pvarEscape] def elabPVarEscape : TermElab := fun stx ty? => do
  match stx with
  | `(⌞$v⌟) => elabTerm v ty?
  | _ => throwUnsupportedSyntax

open Lean Elab Term Quotation in
/-- Let `local notation "θ" => ⌞thV d⌟`-style shorthands pass the notation
    quotation precheck: an escape is checked exactly like its inner term. -/
@[quot_precheck Continuous.pvarEscape] def precheckPVarEscape : Precheck
  | `(⌞$v⌟) => precheck v
  | _ => throwUnsupportedSyntax

/-!
## Expression quotation `e⟪…⟫`

The program variables occurring in the body are replaced by the reads `M.get m τ x.name`.
The measurability proof is tried by `measurable_of_countable`, `fun_prop`, `measurability`,
and finally the extensible tactic `xhl_measurable`, which a file extends with
`local macro_rules` for expressions whose proof rests on hypotheses.  The proof is
irrelevant to equality, so a quoted listing is `rfl`-equal to the program whichever proof
closes it.  A bare variable quotes to `Expr.var x`, a variable-free body to `Expr.cst`. -/

/-- The quoter's measurability fallback, extended by `local macro_rules`; by default it fails. -/
syntax "xhl_measurable" : tactic
macro_rules
  | `(tactic| xhl_measurable) =>
    `(tactic| fail "e⟪…⟫: no measurability proof found; add a `local macro_rules | `(tactic| xhl_measurable) => `(tactic| exact …)` clause, or name the expression")

open Lean Meta Elab Term in
/-- One `⌞v⌟` escape inside `e⟪…⟫`: elaborate `v` against `Vars ident _` and
    mint (or reuse — keyed on the *elaborated value*, so notation expansions of
    the same variable coincide despite fresh hygiene scopes) the local standing
    for its read. -/
def rewriteEscape (identE : Lean.Expr) (v : Term) (orig : Syntax)
    (acc : Array (Name × Lean.Expr × Lean.Expr)) :
    TermElabM (Syntax × Array (Name × Lean.Expr × Lean.Expr)) := do
  let vE ← elabTerm v none
  synthesizeSyntheticMVarsNoPostponing
  let vE ← instantiateMVars vE
  if let some e := acc.find? fun (_, w, _) => w == vE then
    return (mkIdent e.1, acc)
  let vty ← whnfR (← inferType vE)
  unless vty.getAppFn.isConstOf ``Vars && vty.getAppArgs.size == 2 do
    throwErrorAt orig "⌞…⌟: expected a term of type `Vars _ _`, got{indentExpr vty}"
  unless ← isDefEq vty.getAppArgs[0]! identE do
    throwErrorAt orig "⌞…⌟: program variable over the wrong identifier type{indentExpr vty}"
  let nm := Name.mkSimple s!"pv✝{acc.size}"
  return (mkIdent nm, acc.push (nm, vE, vty.getAppArgs[1]!))

open Lean Meta Elab Term in
/-- Rewrite every `⌞v⌟` into the ident of its minted local, in textual order,
    recursing into every other node unchanged. -/
partial def rewriteEscapes (identE : Lean.Expr) (s : Syntax)
    (acc : Array (Name × Lean.Expr × Lean.Expr)) :
    TermElabM (Syntax × Array (Name × Lean.Expr × Lean.Expr)) := do
  match s with
  | `(⌞$v⌟) => rewriteEscape identE v s acc
  | _ =>
    match s with
    | .node info kind args => do
      let mut args' := args
      let mut acc' := acc
      for i in [0:args.size] do
        let (a, acc'') ← rewriteEscapes identE args[i]! acc'
        args' := args'.set! i a
        acc' := acc''
      return (.node info kind args', acc')
    | _ => return (s, acc)

open Lean Meta Elab Term in
elab "e⟪ " t:term " ⟫" : term <= expectedType => do
  let expT ← instantiateMVars expectedType
  -- wait for the expected type: in `prog = ⟪…⟫` the right-hand side is elaborated first
  tryPostponeIfMVar expT
  let expT ← whnfR expT
  let f := expT.getAppFn
  unless f.isConstOf ``Continuous.Expr do
    throwError "e⟪…⟫: expected type must be an `Expr`, got{indentExpr expT}"
  let args := expT.getAppArgs
  unless args.size == 3 do
    throwError "e⟪…⟫: under-applied `Expr` expected type{indentExpr expT}"
  let identE := args[0]!; let ME := args[1]!; let tyE := args[2]!
  if identE.hasExprMVar || ME.hasExprMVar || tyE.hasExprMVar then tryPostpone
  -- expand macros, so `local notation` shorthands for `⌞…⌟` escapes reach the scans
  let traw ← liftMacroM <| expandMacros t.raw
  -- rewrite the `⌞…⌟` escapes, collecting their variables in textual order
  let (traw, escs) ← rewriteEscapes identE traw #[]
  -- collect candidate bare-ident program variables, appended after the escapes:
  -- idents resolving to `Vars`-typed constants
  let mut cands : Array (Name × Lean.Expr × Lean.Expr) := escs  -- (localName, varValue, Ty)
  let mut candNames : Std.HashSet Name := {}
  for stx in traw.topDown do
    if let .ident _ _ nm _ := stx then
      -- macro-generated idents are never program variables; a notation for a program
      -- variable must expand to a `⌞…⌟` escape
      if nm.hasMacroScopes then continue
      let comps := nm.components
      for k in [1:comps.length+1] do
        let pre := comps.take k |>.foldl (fun a c => a ++ c) Name.anonymous
        if candNames.contains pre then break
        if (← getLCtx).findFromUserName? pre |>.isSome then continue
        let some cst ← try pure (some (← resolveGlobalConstNoOverload (mkIdent pre)))
                       catch _ => pure none | continue
        let cinfo ← getConstInfo cst
        let cty ← whnfR cinfo.type
        if cty.getAppFn.isConstOf ``Vars then
          let cargs := cty.getAppArgs   -- Vars (ident) (t)
          if cargs.size == 2 then
            if ← isDefEq cargs[0]! identE then
              cands := cands.push (pre, mkConst cst, cargs[1]!)
              candNames := candNames.insert pre
              break
  -- elaborate the body with locals for the candidates
  let rec withCands (i : Nat) (fvars : Array (Name × Lean.Expr × Lean.Expr × Lean.Expr))
      (k : Array (Name × Lean.Expr × Lean.Expr × Lean.Expr) → TermElabM Lean.Expr) : TermElabM Lean.Expr := do
    if h : i < cands.size then
      let (nm, vE, tyv) := cands[i]
      withLocalDeclD nm (mkApp (mkConst ``Ty.interp) tyv) fun fv =>
        withCands (i + 1) (fvars.push (nm, vE, tyv, fv)) k
    else
      k fvars
  withCands 0 #[] fun fvars => do
    let interpTy := mkApp (mkConst ``Ty.interp) tyE
    let isBool ← isDefEq tyE (mkConst ``Ty.bool)
    let body ← do
      if isBool then
        match ← observing? (elabTermEnsuringType traw interpTy) with
        | some b => pure b
        | none =>
          let p ← elabTermEnsuringType traw (mkSort .zero)
          synthesizeSyntheticMVarsNoPostponing
          let inst ← synthInstance (mkApp (mkConst ``Decidable) (← instantiateMVars p))
          if (← instantiateMVars inst).getUsedConstants.contains ``Classical.propDecidable then
            throwError "e⟪…⟫: the guard is not effectively decidable (Classical instance)"
          pure (mkApp2 (mkConst ``Decidable.decide) p inst)
      else
        elabTermEnsuringType traw interpTy
    synthesizeSyntheticMVarsNoPostponing
    let body ← instantiateMVars body
    if body.hasSorry then throwError "e⟪…⟫: elaboration produced sorry"
    -- occurring program variables
    let occ := fvars.filter fun (_, _, _, fv) => body.containsFVar fv.fvarId!
    -- a bare variable is `Expr.var`, a variable-free body is `Expr.cst`
    if h : occ.size = 1 then
      let (_, vE, tyv, fv) := occ[0]
      if body == fv then
        return mkAppN (mkConst ``Continuous.Expr.var) #[identE, ME, tyv, vE]
    if occ.isEmpty then
      return mkAppN (mkConst ``Continuous.Expr.cst) #[identE, ME, tyE, body]
    -- the lambda over the memory, every variable read off it
    let heapTy := mkApp2 (mkConst ``Continuous.MemType.heap) identE ME
    let core ← withLocalDeclD `m heapTy fun m => do
      let vals := occ.map fun (_, vE, tyv, _) =>
        mkAppN (mkConst ``Continuous.MemType.get) #[identE, ME, m, tyv,
          mkAppN (mkConst ``Continuous.Vars.name) #[identE, tyv, vE]]
      mkLambdaFVars #[m] (body.replaceFVars (occ.map fun (_, _, _, fv) => fv) vals)
    -- measurability: the reads are measurable, and the body as a function of the read
    -- values is handed to automation
    let measTy := mkAppN (mkConst ``Measurable [Level.zero, Level.zero])
      #[heapTy, interpTy, mkApp2 (mkConst ``Continuous.MemType.heapMeas) identE ME,
        mkApp (mkConst ``Continuous.Ty.measurableSpace) tyE, core]
    let pf ← do
        let tys := occ.map fun (_, _, tyv, _) => mkApp (mkConst ``Ty.interp) tyv
        -- the value tuple `τ₁ × (τ₂ × … τₖ)`, its reads, and its projections
        let rec tupleTy : List Lean.Expr → Lean.Expr
          | [] => mkConst ``Unit
          | [a] => a
          | a :: rest => mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) a (tupleTy rest)
        let rec tuple : List (Lean.Expr × Lean.Expr) → Lean.Expr
          | [] => mkConst ``Unit.unit
          | [(_, v)] => v
          | (a, v) :: rest => mkAppN (mkConst ``Prod.mk [Level.zero, Level.zero])
              #[a, tupleTy (rest.map (·.1)), v, tuple rest]
        let rec projs (p : Lean.Expr) : List Lean.Expr → List Lean.Expr
          | [] => []
          | [_] => [p]
          | _ :: rest => mkProj ``Prod 0 p :: projs (mkProj ``Prod 1 p) rest
        let tysL := tys.toList
        let reads ← withLocalDeclD `m heapTy fun m => do
          let vals := (occ.map fun (_, vE, tyv, _) =>
            mkAppN (mkConst ``Continuous.MemType.get) #[identE, ME, m, tyv,
              mkAppN (mkConst ``Continuous.Vars.name) #[identE, tyv, vE]]).toList
          mkLambdaFVars #[m] (tuple (tysL.zip vals))
        let Fun ← withLocalDeclD `p (tupleTy tysL) fun pv => do
          mkLambdaFVars #[pv] (body.replaceFVars (occ.map fun (_, _, _, fv) => fv)
            (projs pv tysL).toArray)
        let rec hreads : Nat → TermElabM Term
          | 0 => `($(mkIdent ``Continuous.measurable_get) _ _)
          | n + 1 => do
            let rest ← hreads n
            `(Measurable.prodMk ($(mkIdent ``Continuous.measurable_get) _ _) $rest)
        let hr ← hreads (occ.size - 1)
        let FunStx ← exprToSyntax Fun
        let readsStx ← exprToSyntax reads
        elabTermEnsuringType
          (← `(by first
                | exact Measurable.comp (g := $FunStx) (f := $readsStx)
                    (by first | exact measurable_of_countable _ | fun_prop | measurability) $hr
                | fun_prop
                | xhl_measurable))
          measTy
    synthesizeSyntheticMVarsNoPostponing
    return mkAppN (mkConst ``Continuous.Expr.mk) #[identE, ME, tyE, core, ← instantiateMVars pf]

/-!
## Command quotation `⟪…⟫`

The sampling forms are restricted to the Bernoulli and Gaussian kernels.  The statements:

* `skip`;
* `x ← e`, or `x := e` — assignment;
* `x ←$ Bern(p)` — Bernoulli draw;
* `x ←$ 𝒩(μ, hμ, v)` — Gaussian draw with a memory-dependent
  mean `μ` and its measurability `hμ`;
* `x ∼ 𝒩(c, v)` — Gaussian draw centred at a constant: the mean map is `fun _ => c`,
  its measurability `measurable_const` (proof-irrelevant, so definitionally the
  three-argument form);
* `release x` — release the variable `x`, of any type: `Cmd.release (Expr.var x)`;
* `~c` — splice an already-built `Cmd`;
* `(c)`, `c₁ ; c₂`, `if g then c₁ else c₂ fi`, `while g do c od` — grouping, sequence and
  the two control forms. -/

declare_syntax_cat ccmd

syntax:60 "skip" : ccmd
syntax:60 term:max " ← " term : ccmd
syntax:60 term:max " := " term : ccmd
syntax:60 term:max " ←$ " "Bern(" term ")" : ccmd
syntax:60 term:max " ←$ " "𝒩(" term ", " term ", " term ")" : ccmd
syntax:60 term:max " ∼ " "𝒩(" term ", " term ")" : ccmd
syntax:60 "release " term:max : ccmd
syntax:60 "~" term:max : ccmd
syntax "(" ccmd ")" : ccmd
syntax:50 ccmd:50 " ; " ccmd:51 : ccmd
syntax:60 "if " termBeforeDo " then " ccmd " else " ccmd " fi" : ccmd
syntax:60 "while " termBeforeDo " do " ccmd " od" : ccmd

syntax "⟪ " ccmd " ⟫" : term

macro_rules
  | `(⟪ skip ⟫)                           => `(Cmd.skip)
  | `(⟪ $x:term ← $e ⟫)                   => `(Cmd.assign $x (e⟪ $e ⟫))
  | `(⟪ $x:term := $e ⟫)                  => `(Cmd.assign $x (e⟪ $e ⟫))
  | `(⟪ $x:term ←$ Bern($p) ⟫)            => `(Cmd.random $x (bernoulliKernel $p))
  | `(⟪ $x:term ←$ 𝒩($μ, $hμ, $v) ⟫)      => `(Cmd.random $x (gaussKernelE $μ $hμ $v))
  | `(⟪ $x:term ∼ 𝒩($c, $v) ⟫)            =>
      `(Cmd.random $x (gaussKernelE (fun _ => $c) measurable_const $v))
  | `(⟪ release $x ⟫)                     => `(Cmd.release (Expr.var $x))
  | `(⟪ ~$t ⟫)                            => `($t)
  | `(⟪ ($c) ⟫)                           => `(⟪ $c ⟫)
  | `(⟪ $a ; $b ⟫)                        => `(⟪ $a ⟫ ;; ⟪ $b ⟫)
  | `(⟪ if $g then $a else $b fi ⟫)       => `(Cmd.cond (e⟪ $g ⟫) ⟪ $a ⟫ ⟪ $b ⟫)
  | `(⟪ while $g do $c od ⟫)              => `(Cmd.while (e⟪ $g ⟫) ⟪ $c ⟫)

end Continuous
