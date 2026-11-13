import Xhl.Examples.DPFTRLBanded.Program
import Xhl.Examples.DPFTRLBanded.MixWitness
import Xhl.Logic.Equiv.CEquivSound

open Continuous

/-!
# The window of `dpftrlBandedGen`, presampled into one variable

A window (the paper's block, Appendix E.5) is `L + 1 ≤ m + 1` rounds: fewer than `m + 1`
when the end of the run truncates it.  The amplified bound needs the coin of record `j`
at the window's first round and the window's noises in one joint draw `w` (the draw (45)),
held in the state.  This file defines

* `windowW`, the window reading its coin and noises from `w` (`coinWT`/`noiseWT`; a
  truncated window reads the first `L + 1` of the `m + 1` noise blocks), and its
  rewriting into `windowE` by the equivalence rules (`cequivW_windowE`);
* `windowS = local w in (w ←$ lawWT ; windowW)`, the presampled window.  The identity
  `iterCmd roundT (L + 1) ≡ windowS` is `cequiv_windowT_windowS_rules` (`PresampleT.lean`).
-/

open MeasureTheory ProbabilityTheory ENNReal
open Cmd hiding loc
open scoped NNReal

variable {ident : Type} {M : MemType ident}

namespace DPFTRL.Band

open Continuous

variable {d e n T : ℕ} {τ : Ty} [NeZero T]

/-! ## The programs, with the randomness given by expressions -/

section Program

variable (p : TParams d e n T T τ) (v : TVars ident d T T τ) (tv : Vars ident .nat)
  (q : ℝ≥0) (elig : ℕ → ℕ → Bool) (uv : Vars ident .bool) (hok : TOK p v)

/-- The round tail with the noise given by an expression. -/
noncomputable def postTE (ez : Expr M (.vec d)) : Cmd ident M :=
  Cmd.seq (Cmd.assign v.z ez)
    (Cmd.seq (Cmd.assign v.Y (relEM p.C v tv))
      (Cmd.seq (Cmd.assign v.acc (sumEM p v tv))
        (Cmd.seq (Cmd.assign v.x (modelEM p v))
          (Cmd.seq (Cmd.release (Expr.var v.x)) (Cmd.assign tv (incW tv))))))

/-- A round with the noise `ez`. -/
noncomputable def roundTE (ez : Expr M (.vec d)) : Cmd ident M :=
  Cmd.seq (Cmd.assign v.i (Expr.cst (t := .nat) 0))
    (Cmd.seq (Cmd.while (ltCE v.i n) (recBT p v tv q elig uv hok)) (postTE p v tv ez))

/-- The step of a record whose coin is given by an expression. -/
noncomputable def recJTE (eb : Expr M .bool) : Cmd ident M :=
  Cmd.seq (Cmd.cond (eligE v tv elig)
      (loc uv (Cmd.seq (Cmd.assign uv eb) (Cmd.assign v.H (histE p v tv uv hok))))
      Cmd.skip)
    (Cmd.assign v.i (incW v.i))

/-- The round in which record `j`'s coin is `eb`, with the noise `ez`. -/
noncomputable def roundITE (j : ℕ) (eb : Expr M .bool)
    (ez : Expr M (.vec d)) : Cmd ident M :=
  Cmd.seq (Cmd.assign v.i (Expr.cst (t := .nat) 0))
    (Cmd.seq (iterCmd (recBT p v tv q elig uv hok) j)
      (Cmd.seq (recJTE p v tv elig uv hok eb)
        (Cmd.seq (iterCmd (recBT p v tv q elig uv hok) (n - j - 1)) (postTE p v tv ez))))

/-- `m` rounds with the noises `ez`. -/
noncomputable def iterTE : (m : ℕ) → (Fin m → Expr M (.vec d)) → Cmd ident M
  | 0, _ => Cmd.skip
  | m + 1, ez => Cmd.seq (roundTE p v tv q elig uv hok (ez 0)) (iterTE m (Fin.tail ez))

/-- **The window with the coin and the noises given by expressions.** -/
noncomputable def windowE (j m : ℕ) (eb : Expr M .bool)
    (ez : Fin (m + 1) → Expr M (.vec d)) : Cmd ident M :=
  Cmd.seq (roundITE p v tv q elig uv hok j eb (ez 0))
    (iterTE p v tv q elig uv hok m (Fin.tail ez))

end Program

/-! ## The variable that holds the window's randomness -/

section W

variable (p : TParams d e n T T τ) (v : TVars ident d T T τ) (tv : Vars ident .nat)
  (q : ℝ≥0) (elig : ℕ → ℕ → Bool) (uv : Vars ident .bool) (hok : TOK p v) {m : ℕ}
  (wv : Vars ident (.prod .bool (.vec ((m + 1) * d))))

/-- The coin of record `j`, read from `w`. -/
def coinWT : Expr M .bool :=
  ⟨fun h => (M.get h (.prod .bool (.vec ((m + 1) * d))) wv.name).1,
    measurable_fst.comp (M.get_measurable (.prod .bool (.vec ((m + 1) * d))) wv.name)⟩

/-- The noise of the round `l` of the window, read from `w`. -/
noncomputable def noiseWT (l : Fin (m + 1)) : Expr M (.vec d) :=
  ⟨fun h => blk (M.get h (.prod .bool (.vec ((m + 1) * d))) wv.name).2 l,
    ((continuous_blk l).measurable.comp measurable_snd).comp
      (M.get_measurable (.prod .bool (.vec ((m + 1) * d))) wv.name)⟩

/-- The window of `L + 1 ≤ m + 1` rounds reading its coin and noises from `w`: round `l`
    reads the noise block `l` of `w`. -/
noncomputable def windowW (j L : ℕ) (hL : L ≤ m) : Cmd ident M :=
  windowE p v tv q elig uv hok j L (coinWT wv)
    (fun l => noiseWT wv (Fin.castLE (Nat.succ_le_succ hL) l))

/-- **The law of `w`**: the coin of record `j` at the window's first round, and the noises
    of the whole window, concatenated. -/
noncomputable def lawWT (q σ2 : ℝ≥0) :
    Measure (Ty.interp (.prod .bool (.vec ((m + 1) * d)))) :=
  (bernoulliMeasure q).prod (gaussE (0 : EuclideanSpace ℝ (Fin ((m + 1) * d))) σ2)

instance isProb_lawWT {σ2 : ℝ≥0} :
    IsProbabilityMeasure (lawWT (d := d) (m := m) q σ2) := by
  haveI : IsProbabilityMeasure (gaussE (0 : EuclideanSpace ℝ (Fin ((m + 1) * d))) σ2) := by
    unfold gaussE; exact Measure.isProbabilityMeasure_map (by fun_prop)
  unfold lawWT; infer_instance

/-- **The window of `L + 1` rounds with its randomness presampled into `w`.** -/
noncomputable def windowS (j L : ℕ) (hL : L ≤ m) : Cmd ident M :=
  loc wv (Cmd.seq (Cmd.random wv (Kernel.const _ (lawWT (m := m) (d := d) q p.σ2)))
    (windowW p v tv q elig uv hok wv j L hL))

end W

/-! ## Side conditions -/

variable {p : TParams d e n T T τ} {v : TVars ident d T T τ} {tv : Vars ident .nat}
  {q : ℝ≥0} {elig : ℕ → ℕ → Bool} {uv : Vars ident .bool} {hok : TOK p v} {m : ℕ}
  {wv : Vars ident (.prod .bool (.vec ((m + 1) * d)))}

/-- `w` is a variable of its own. -/
structure WOKT (v : TVars ident d T T τ) (tv : Vars ident .nat) (uv : Vars ident .bool)
    (wv : Vars ident (.prod .bool (.vec ((m + 1) * d)))) : Prop where
  wx : wv.name ≠ v.x.name
  wz : wv.name ≠ v.z.name
  wi : wv.name ≠ v.i.name
  wD : wv.name ≠ v.D.name
  wH : wv.name ≠ v.H.name
  wY : wv.name ≠ v.Y.name
  wt : wv.name ≠ tv.name
  wu : wv.name ≠ uv.name
  wacc : wv.name ≠ v.acc.name

/-- The draw held in `w`. -/
abbrev tWT (wv : Vars ident (.prod .bool (.vec ((m + 1) * d)))) (h : M.heap) :=
  M.get h (.prod .bool (.vec ((m + 1) * d))) wv.name

/-- The reads of `w` are independent of every other variable. -/
lemma exprIndep_coinWT {t : Ty} (y : Vars ident t) (hy : y.name ≠ wv.name) :
    ExprIndep y (coinWT (M := M) wv) := fun h w => by
  simp only [coinWT, esem_mk]
  rw [get_set_other _ _ hy]

lemma exprIndep_noiseWT {t : Ty} (y : Vars ident t) (hy : y.name ≠ wv.name) (l : Fin (m + 1)) :
    ExprIndep y (noiseWT (M := M) wv l) := fun h w => by
  simp only [noiseWT, esem_mk]
  rw [get_set_other _ _ hy]

/-! ## The names of the program are not `w` -/

/-- The variables the window mentions, none of which is `w`. -/
structure WNamesT (v : TVars ident d T T τ) (tv : Vars ident .nat) (uv : Vars ident .bool)
    (wv : Vars ident (.prod .bool (.vec ((m + 1) * d)))) : Prop where
  x : v.x.name ≠ wv.name
  z : v.z.name ≠ wv.name
  i : v.i.name ≠ wv.name
  D : v.D.name ≠ wv.name
  H : v.H.name ≠ wv.name
  Y : v.Y.name ≠ wv.name
  t : tv.name ≠ wv.name
  u : uv.name ≠ wv.name
  acc : v.acc.name ≠ wv.name

lemma wnamesT (hw : WOKT v tv uv wv) : WNamesT v tv uv wv :=
  ⟨Ne.symm hw.wx, Ne.symm hw.wz, Ne.symm hw.wi, Ne.symm hw.wD, Ne.symm hw.wH, Ne.symm hw.wY,
    Ne.symm hw.wt, Ne.symm hw.wu, Ne.symm hw.wacc⟩

/-! ## The program does not write `w` -/

section NoWriteW

variable (hn : WNamesT v tv uv wv)

include hn

lemma noWriteT_recBT : NoWrite wv.name (recBT (M := M) p v tv q elig uv hok) :=
  ⟨⟨⟨hn.u, hn.u, hn.H⟩, trivial⟩, hn.i⟩

lemma noWriteT_iterCmd {c : Cmd ident M} (h : NoWrite wv.name c) :
    ∀ l, NoWrite wv.name (iterCmd c l)
  | 0 => trivial
  | l + 1 => ⟨h, noWriteT_iterCmd h l⟩

lemma noWriteT_postTE (ez : Expr M (.vec d)) :
    NoWrite wv.name (postTE (M := M) p v tv ez) :=
  ⟨hn.z, hn.Y, hn.acc, hn.x, trivial, hn.t⟩

lemma noWriteT_roundTE (ez : Expr M (.vec d)) :
    NoWrite wv.name (roundTE (M := M) p v tv q elig uv hok ez) :=
  ⟨hn.i, noWriteT_recBT hn, noWriteT_postTE hn ez⟩

lemma noWriteT_recJTE (eb : Expr M .bool) :
    NoWrite wv.name (recJTE (M := M) p v tv elig uv hok eb) :=
  ⟨⟨⟨hn.u, hn.u, hn.H⟩, trivial⟩, hn.i⟩

lemma noWriteT_roundITE (j : ℕ) (eb : Expr M .bool)
    (ez : Expr M (.vec d)) :
    NoWrite wv.name (roundITE (M := M) p v tv q elig uv hok j eb ez) :=
  ⟨hn.i, noWriteT_iterCmd hn (noWriteT_recBT hn) j, noWriteT_recJTE hn eb,
    noWriteT_iterCmd hn (noWriteT_recBT hn) _, noWriteT_postTE hn ez⟩

lemma noWriteT_iterTE : ∀ (K : ℕ) (ez : Fin K → Expr M (.vec d)),
    NoWrite wv.name (iterTE (M := M) p v tv q elig uv hok K ez)
  | 0, _ => trivial
  | K + 1, ez => ⟨noWriteT_roundTE hn (ez 0), noWriteT_iterTE K (Fin.tail ez)⟩

lemma noWriteT_windowE (j K : ℕ) (eb : Expr M .bool)
    (ez : Fin (K + 1) → Expr M (.vec d)) :
    NoWrite wv.name (windowE (M := M) p v tv q elig uv hok j K eb ez) :=
  ⟨noWriteT_roundITE hn j eb (ez 0), noWriteT_iterTE hn K (Fin.tail ez)⟩

end NoWriteW

/-! ## Rewriting the window's randomness, by the equivalence rules

[E-Leaf-S]/[E-Leaf-A] fire at the coin and at each noise, [E-Seq-V] (`CEquiv.seqVals`)
transports the restriction past every head, and [E-If]/[E-Loc] carry it underneath.  The
restriction `R` is any predicate determined by the values of the variables `ys`. -/

section CEquivW

variable {R : St M → Prop} (ys : List ((t : Ty) × Vars ident t))
  (hR : ∀ s s' : St M,
    (∀ z ∈ ys, M.get s.1 z.1 z.2.name = M.get s'.1 z.1 z.2.name) → R s → R s')

include hR

/-- Sequencing: the head is rewritten by `CEquiv.congrHead`, the tail at the restriction
    after the head, which `CEquiv.seqVals` supplies since the head writes none of `ys`. -/
lemma cequivW_seq {c₁ c₂ c₁' c₂' : Cmd ident M}
    (hnw' : NoWriteL (M := M) ys c₁')
    (h₁ : CEquiv R c₁ c₁') (h₂ : CEquiv R c₂ c₂') :
    CEquiv R (Cmd.seq c₁ c₂) (Cmd.seq c₁' c₂') :=
  (CEquiv.congrHead h₁).trans (CEquiv.seqVals ys hR hnw' h₂)

/-- The round tail: the noise is a leaf. -/
lemma cequivW_postTE
    {ez ez' : Expr M (.vec d)}
    (hnw' : NoWriteL (M := M) ys (postTE (M := M) p v tv ez'))
    (hE : ∀ s : St M, R s → esem ez' s.1 = esem ez s.1) :
    CEquiv R (postTE (M := M) p v tv ez) (postTE p v tv ez') :=
  cequivW_seq ys hR
    (fun z hz => (hnw' z hz).1) (CEquiv.leafAssign v.z ez ez' hE) (CEquiv.refl _)

/-- A round. -/
lemma cequivW_roundTE (hok : TOK p v)
    {ez ez' : Expr M (.vec d)}
    (hnw' : NoWriteL (M := M) ys (roundTE (M := M) p v tv q elig uv hok ez'))
    (hE : ∀ s : St M, R s → esem ez' s.1 = esem ez s.1) :
    CEquiv R (roundTE (M := M) p v tv q elig uv hok ez) (roundTE p v tv q elig uv hok ez') := by
  refine cequivW_seq ys hR (fun z hz => (hnw' z hz).1) (CEquiv.refl _) ?_
  exact cequivW_seq ys hR
    (fun z hz => (hnw' z hz).2.1) (CEquiv.refl _)
    (cequivW_postTE ys hR (fun z hz => (hnw' z hz).2.2) hE)

/-- The step of the distinguished record: the coin is a leaf under a `cond` and a `loc`,
    and both congruences carry the restriction to it. -/
lemma cequivW_recJTE (hok : TOK p v)
    {eb eb' : Expr M .bool}
    (hnw' : NoWriteL (M := M) ys (recJTE (M := M) p v tv elig uv hok eb'))
    (huy : ∀ z ∈ ys, uv.name ≠ z.2.name)
    (hEb : ∀ s : St M, R s → esem eb' s.1 = esem eb s.1) :
    CEquiv R (recJTE (M := M) p v tv elig uv hok eb) (recJTE p v tv elig uv hok eb') := by
  refine cequivW_seq ys hR (fun z hz => (hnw' z hz).1) ?_ (CEquiv.refl _)
  refine CEquiv.congrCond (CEquiv.weaken (fun _ hs => hs.1) ?_) (CEquiv.refl _)
  refine CEquiv.congrLoc uv (R' := R) (fun s hs => hR s _ (fun z hz => ?_) hs) ?_
  · exact (M.get_set_ne _ _ s.1 uv.name z.2.name default (Or.inr (huy z hz))).symm
  · exact cequivW_seq ys hR (fun z hz => (hnw' z hz).1.1.2.1)
      (CEquiv.leafAssign uv eb eb' hEb) (CEquiv.refl _)

/-- The window's first round. -/
lemma cequivW_roundITE (hok : TOK p v) (j : ℕ)
    {eb eb' : Expr M .bool}
    {ez ez' : Expr M (.vec d)}
    (hnw' : NoWriteL (M := M) ys (roundITE (M := M) p v tv q elig uv hok j eb' ez'))
    (huy : ∀ z ∈ ys, uv.name ≠ z.2.name)
    (hEb : ∀ s : St M, R s → esem eb' s.1 = esem eb s.1)
    (hE : ∀ s : St M, R s → esem ez' s.1 = esem ez s.1) :
    CEquiv R (roundITE (M := M) p v tv q elig uv hok j eb ez)
      (roundITE p v tv q elig uv hok j eb' ez') := by
  refine cequivW_seq ys hR (fun z hz => (hnw' z hz).1) (CEquiv.refl _) ?_
  refine cequivW_seq ys hR (fun z hz => (hnw' z hz).2.1) (CEquiv.refl _) ?_
  refine cequivW_seq ys hR (fun z hz => (hnw' z hz).2.2.1)
    (cequivW_recJTE ys hR hok (fun z hz => (hnw' z hz).2.2.1) huy hEb) ?_
  exact cequivW_seq ys hR (fun z hz => (hnw' z hz).2.2.2.1) (CEquiv.refl _)
    (cequivW_postTE ys hR (fun z hz => (hnw' z hz).2.2.2.2) hE)

/-- `K` rounds. -/
lemma cequivW_iterTE (hok : TOK p v) :
    ∀ (K : ℕ) (ez ez' : Fin K → Expr M (.vec d)),
    NoWriteL (M := M) ys (iterTE (M := M) p v tv q elig uv hok K ez') →
    (∀ (l : Fin K) (s : St M), R s → esem (ez' l) s.1 = esem (ez l) s.1) →
    CEquiv R (iterTE (M := M) p v tv q elig uv hok K ez)
      (iterTE p v tv q elig uv hok K ez')
  | 0, _, _, _, _ => CEquiv.refl _
  | K + 1, ez, ez', hnw', hE =>
    cequivW_seq ys hR (fun z hz => (hnw' z hz).1)
      (cequivW_roundTE ys hR hok (fun z hz => (hnw' z hz).1) (hE 0))
      (cequivW_iterTE hok K (Fin.tail ez) (Fin.tail ez')
        (fun z hz => (hnw' z hz).2) (fun l s => hE l.succ s))

/-- The window. -/
lemma cequivW_windowE (hok : TOK p v) (j K : ℕ)
    {eb eb' : Expr M .bool}
    {ez ez' : Fin (K + 1) → Expr M (.vec d)}
    (hnw' : NoWriteL (M := M) ys (windowE (M := M) p v tv q elig uv hok j K eb' ez'))
    (huy : ∀ z ∈ ys, uv.name ≠ z.2.name)
    (hEb : ∀ s : St M, R s → esem eb' s.1 = esem eb s.1)
    (hE : ∀ (l : Fin (K + 1)) (s : St M), R s → esem (ez' l) s.1 = esem (ez l) s.1) :
    CEquiv R (windowE (M := M) p v tv q elig uv hok j K eb ez)
      (windowE p v tv q elig uv hok j K eb' ez') :=
  cequivW_seq ys hR (fun z hz => (hnw' z hz).1)
    (cequivW_roundITE ys hR hok j (fun z hz => (hnw' z hz).1) huy hEb (hE 0))
    (cequivW_iterTE ys hR hok K (Fin.tail ez) (Fin.tail ez')
      (fun z hz => (hnw' z hz).2) (fun l s => hE l.succ s))

end CEquivW

/-! ## The law of `w` -/

lemma lawWT_eq_map (σ2 : ℝ≥0) :
    lawWT (m := m) (d := d) q σ2
      = ((bernoulliMeasure q).prod (Measure.pi fun _ : Fin (m + 1) =>
          gaussE (0 : EuclideanSpace ℝ (Fin d)) σ2)).map
        (fun θ => (θ.1, concatE θ.2)) := by
  have h0 : concatE (fun _ : Fin (m + 1) => (0 : EuclideanSpace ℝ (Fin d))) = 0 := by
    ext k; simp [concatE]
  have hmap : ((bernoulliMeasure q).prod (Measure.pi fun _ : Fin (m + 1) =>
      gaussE (0 : EuclideanSpace ℝ (Fin d)) σ2)).map (Prod.map id concatE)
      = ((bernoulliMeasure q).map id).prod ((Measure.pi fun _ : Fin (m + 1) =>
          gaussE (0 : EuclideanSpace ℝ (Fin d)) σ2).map concatE) :=
    (Measure.map_prod_map _ _ measurable_id measurable_concatE).symm
  rw [Measure.map_id, pi_gaussE_map_concatE, h0] at hmap
  exact hmap.symm

end DPFTRL.Band
