import Xhl.Examples.DPFTRLBanded.Sched

open Continuous

/-!
# Amplified banded DP-FTRL, one release per round — the program (Fig. 10)

`R = T`: row `t` is released at round `t`.  One round is

    i := 0 ;
    while i < n do
      if elig(i,t) then local u in ( u ←$ Bern(q) ; H[t] := H[t] + u·clip_Γ(∇ℓ(x, D[i])) ) ;
      i := i + 1
    od ;
    z ←$ 𝒩(0, σ²·I_d) ;  Y[t] := (C·H)_t + z ;
    ŝ := (B·Y)_t ;  θ := −(1/λ)·ŝ ;  release θ ;  t := t + 1

and `dpftrlBandedGen` is `θ := 0 ; H := 0 ; Y := 0 ; t := 0 ; while t < T do round od`.
The record loop accumulates straight into the slot `H[t]`, and the prefix sum `ŝ` is held
in `acc`.  Parameters, geometry (`rowMean`, `blk`/`setBlk`) and round tail (`relEM`,
`sumEM`, `modelEM`) are the matrix-mechanism study's at `R := T`.  `histE` carries its
measurability proof, which needs `hok : TOK p v`, so every program built from it takes
`hok`.
-/

open MeasureTheory ProbabilityTheory ENNReal
open Cmd hiding loc
open scoped NNReal

variable {ident : Type} {M : MemType ident}

namespace DPFTRL.Band

open Continuous

variable {d e n T : ℕ} {τ : Ty} [NeZero T]

section TProgram

variable (p : TParams d e n T T τ) (v : TVars ident d T T τ) (tv : Vars ident .nat)
  (q : ℝ≥0) (elig : ℕ → ℕ → Bool) (uv : Vars ident .bool) (hok : TOK p v)

/-! ## The record step, writing the history directly -/

/-- The contribution of record `i` with coin `u`, written straight into slot `t`. -/
noncomputable def histStepT (HH : EuclideanSpace ℝ (Fin (T * d))) (u : Bool) (tt ii : ℕ)
    (xx : EuclideanSpace ℝ (Fin d)) (DD : τ.interp) : EuclideanSpace ℝ (Fin (T * d)) :=
  setBlk HH (Fin.ofNat T tt)
    (blk HH (Fin.ofNat T tt) + (if u then (1 : ℝ) else 0) • clipV p.Cl (p.grad xx (p.record DD ii)))

/-- `H[t] := H[t] + u·clip_Γ(∇ℓ(x, D[i]))`. -/
noncomputable def histE : Expr M (.vec (T * d)) :=
  ⟨fun h => histStepT p (M.get h (.vec (T * d)) v.H.name) (M.get h .bool uv.name)
      (M.get h .nat tv.name) (M.get h .nat v.i.name) (M.get h (.vec d) v.x.name)
      (M.get h τ v.D.name), by
    set Φ : ((EuclideanSpace ℝ (Fin (T * d)) × EuclideanSpace ℝ (Fin d) × τ.interp)
        × (Bool × ℕ × ℕ)) → EuclideanSpace ℝ (Fin (T * d)) :=
      fun ((H, θ, D), (u, t, i)) => histStepT p H u t i θ D
    have hΦ : Measurable Φ := by
      refine measurable_from_prod_countable_left (fun uti => ?_)
      obtain ⟨u, tt, ii⟩ := uti
      have hg : Measurable (fun ((_, θ, D) : EuclideanSpace ℝ (Fin (T * d)) × EuclideanSpace ℝ (Fin d)
          × τ.interp) => clipV p.Cl (p.grad θ (p.record D ii))) := by
        refine (measurable_clipV p.Cl).comp ?_
        simp only [grad_record_split]
        exact Measurable.ite ((measurable_snd.comp measurable_snd) (hok.present ii))
          (hok.grad.comp ((measurable_fst.comp measurable_snd).prodMk
            ((hok.recVal ii).comp (measurable_snd.comp measurable_snd))))
          measurable_const
      show Measurable (fun ((H, θ, D) : EuclideanSpace ℝ (Fin (T * d)) × EuclideanSpace ℝ (Fin d)
          × τ.interp) => setBlk H (Fin.ofNat T tt)
            (blk H (Fin.ofNat T tt) + (if u then (1 : ℝ) else 0)
              • clipV p.Cl (p.grad θ (p.record D ii))))
      exact (continuous_setBlk (Fin.ofNat T tt)).measurable.comp (measurable_fst.prodMk
        (((continuous_blk (Fin.ofNat T tt)).measurable.comp measurable_fst).add
          (hg.const_smul (if u then (1 : ℝ) else 0))))
    exact hΦ.comp (((M.get_measurable (.vec (T * d)) v.H.name).prodMk
      ((M.get_measurable (.vec d) v.x.name).prodMk (M.get_measurable τ v.D.name))).prodMk
      ((M.get_measurable .bool uv.name).prodMk ((M.get_measurable .nat tv.name).prodMk
        (M.get_measurable .nat v.i.name))))⟩

/-- The record step: coin and direct history write, then `i := i + 1`. -/
noncomputable def recBT : Cmd ident M :=
  Cmd.seq (Cmd.cond (eligE v tv elig)
      (loc uv (Cmd.seq (Cmd.random uv (bernoulliKernel q))
        (Cmd.assign v.H (histE p v tv uv hok)))) Cmd.skip)
    (Cmd.assign v.i (incW v.i))

/-! ## The round and the program -/

/-- The tail of a round after the record loop: one noise, the row `Y[t]`, the prefix sum
    `ŝ := (B·Y)_t`, the model `θ := −(1/λ)·ŝ` and its release, `t++`. -/
noncomputable def postT : Cmd ident M :=
  Cmd.seq (Cmd.random v.z (noiseKernelE p.σ2))
    (Cmd.seq (Cmd.assign v.Y (relEM p.C v tv))
      (Cmd.seq (Cmd.assign v.acc (sumEM p v tv))
        (Cmd.seq (Cmd.assign v.x (modelEM p v))
          (Cmd.seq (Cmd.release (Expr.var v.x)) (Cmd.assign tv (incW tv))))))

/-- One round. -/
noncomputable def roundT : Cmd ident M :=
  Cmd.seq (Cmd.assign v.i (Expr.cst (t := .nat) 0))
    (Cmd.seq (Cmd.while (ltCE v.i n) (recBT p v tv q elig uv hok)) (postT p v tv))

/-- **Amplified banded DP-FTRL, one release per round**: `θ := 0 ; H := 0 ; Y := 0 ;
    t := 0 ; while t < T do round od`. -/
noncomputable def dpftrlBandedGen : Cmd ident M :=
  Cmd.seq (Cmd.assign v.x (Expr.cst (t := .vec d) 0))
    (Cmd.seq (Cmd.assign v.H (Expr.cst (t := .vec (T * d)) 0))
      (Cmd.seq (Cmd.assign v.Y (Expr.cst (t := .vec (T * d)) 0))
        (Cmd.seq (Cmd.assign tv (Expr.cst (t := .nat) 0))
          (Cmd.while (ltCE tv T) (roundT p v tv q elig uv hok)))))

end TProgram

/-! ## Side conditions -/

variable {p : TParams d e n T T τ} {v : TVars ident d T T τ} {tv : Vars ident .nat}
  {q : ℝ≥0} {elig : ℕ → ℕ → Bool} {uv : Vars ident .bool}

section Meas

/-- **The round counter is a variable of its own.** -/
structure TCntOK (v : TVars ident d T T τ) (tv : Vars ident .nat) : Prop where
  tx : tv.name ≠ v.x.name
  tacc : tv.name ≠ v.acc.name
  tz : tv.name ≠ v.z.name
  ti : tv.name ≠ v.i.name
  tD : tv.name ≠ v.D.name
  tH : tv.name ≠ v.H.name
  tY : tv.name ≠ v.Y.name

end Meas

end DPFTRL.Band
