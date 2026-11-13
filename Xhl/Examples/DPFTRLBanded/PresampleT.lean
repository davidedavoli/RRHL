import Xhl.Examples.DPFTRLBanded.Window

open Continuous

/-!
# The window identity, in the equivalence calculus (Appendix E.5, Appendix C)

`cequiv_windowT_windowS_rules`: a window of `L + 1 ≤ m + 1` rounds of `dpftrlBandedGen` is
its presampled form `windowS` (the lazy-vs-eager identity behind (45)), as a `CEquiv`
derivation.  The window's draws are named into fresh scratch blocks ([E-Push]), the
distinguished coin leaves its eligibility conditional ([E-Defer-C]), every block grows to
the window's front (scope laws), and the draws merge into the single joint draw of `w`
([E-Merge], [E-Push]), whose reads [E-Leaf-S]/[E-Leaf-A] rewrite.  A truncated window
(`L < m`) takes the `m − L` unused scratches as dead draws (`cequiv_deadDraw`).  The
scratches (one Boolean, `m + 1` vectors) appear only inside the derivation and are
discharged by [E-Ghost].

`FNamesT` is `WNamesT` at an arbitrary name, so one lemma serves the scratches and `w`. -/

open MeasureTheory ProbabilityTheory ENNReal
open Cmd hiding loc
open scoped NNReal

variable {ident : Type} {M : MemType ident}

namespace DPFTRL.Band

open Continuous

variable {d e n T : ℕ} {τ : Ty} [NeZero T]
variable {p : TParams d e n T T τ} {v : TVars ident d T T τ} {tv : Vars ident .nat}
  {q : ℝ≥0} {elig : ℕ → ℕ → Bool} {uv : Vars ident .bool} {hok : TOK p v}

/-! ## Independence of an arbitrary fresh name -/

/-- The program's variables all avoid the name `f` — `WNamesT` at an arbitrary name. -/
structure FNamesT (v : TVars ident d T T τ) (tv : Vars ident .nat) (uv : Vars ident .bool)
    (f : ident) : Prop where
  x : v.x.name ≠ f
  z : v.z.name ≠ f
  i : v.i.name ≠ f
  D : v.D.name ≠ f
  H : v.H.name ≠ f
  Y : v.Y.name ≠ f
  t : tv.name ≠ f
  u : uv.name ≠ f
  acc : v.acc.name ≠ f

section FreshVar

variable {tf : Ty} (fv : Vars ident tf)

lemma exprIndepF_incW (x : Vars ident .nat) (hx : x.name ≠ fv.name) :
    ExprIndep fv (incW (M := M) x) := fun h w => by
  simp only [incW, esem_mk]
  rw [get_set_other _ _ hx.symm]

lemma exprIndepF_ltCE (x : Vars ident .nat) (hx : x.name ≠ fv.name) (K : ℕ) :
    ExprIndep fv (ltCE (M := M) x K) := fun h w => by
  simp only [ltCE, ltW, esem_mk]
  rw [get_set_other _ _ hx.symm]

lemma indepF_assign {t : Ty} (x : Vars ident t) (e : Expr M t)
    (hx : x.name ≠ fv.name) (he : ExprIndep fv e) : IndepY fv (Cmd.assign (M := M) x e) :=
  ⟨hx, he⟩

/-- The constant Bernoulli kernel is blind to every write. -/
lemma bern_blind (h : M.heap) (w : tf.interp) :
    bernoulliKernel (M := M) q (M.set h tf fv.name w) = bernoulliKernel q h := rfl

/-- The noise kernel is the constant Gaussian, so it too is blind to every write. -/
lemma noiseK_blind (σ2 : ℝ≥0) (h : M.heap) (w : tf.interp) :
    noiseKernelE (M := M) (d := d) σ2 (M.set h tf fv.name w)
      = noiseKernelE (M := M) (d := d) σ2 h := by
  show gaussKernelE (M := M) (fun _ => (0 : EuclideanSpace ℝ (Fin d)))
      measurable_const σ2 _ = gaussKernelE (M := M) _ measurable_const σ2 h
  rw [gaussKernelE_apply, gaussKernelE_apply]

lemma indepF_iterCmd {c : Cmd ident M} (h : IndepY fv c) : ∀ l, IndepY fv (iterCmd c l)
  | 0 => trivial
  | l + 1 => ⟨h, indepF_iterCmd h l⟩

variable (hn : FNamesT v tv uv fv.name)

include hn

lemma exprIndepF_histE : ExprIndep fv (histE (M := M) p v tv uv hok) := fun h w => by
  simp only [histE, esem_mk]
  rw [get_set_other _ _ hn.H.symm, get_set_other _ _ hn.u.symm, get_set_other _ _ hn.t.symm,
    get_set_other _ _ hn.i.symm, get_set_other _ _ hn.x.symm, get_set_other _ _ hn.D.symm]

lemma exprIndepF_relEM : ExprIndep fv (relEM (M := M) p.C v tv) := fun h w => by
  simp only [relEM, esem_mk]
  rw [get_set_other _ _ hn.Y.symm, get_set_other _ _ hn.t.symm, get_set_other _ _ hn.H.symm,
    get_set_other _ _ hn.z.symm]

lemma exprIndepF_sumEM : ExprIndep fv (sumEM (M := M) p v tv) := fun h w => by
  simp only [sumEM, esem_mk]
  rw [get_set_other _ _ hn.t.symm, get_set_other _ _ hn.Y.symm]

omit [NeZero T] in
lemma exprIndepF_modelEM : ExprIndep fv (modelEM (M := M) p v) := fun h w => by
  simp only [modelEM, esem_mk]
  rw [get_set_other _ _ hn.acc.symm]

lemma exprIndepF_eligE : ExprIndep fv (eligE (M := M) v tv elig) := fun h w => by
  simp only [eligE, esem_mk]
  rw [get_set_other _ _ hn.i.symm, get_set_other _ _ hn.t.symm]

omit [NeZero T] in
lemma indepF_releaseX : IndepY fv (Cmd.release (M := M) (Expr.var v.x)) :=
  ExprIndep.var fv v.x hn.x

lemma indepF_recBT : IndepY fv (recBT (M := M) p v tv q elig uv hok) :=
  ⟨⟨exprIndepF_eligE fv hn,
      ⟨hn.u, ⟨hn.u, bern_blind fv⟩,
        indepF_assign fv v.H _ hn.H (exprIndepF_histE fv hn)⟩, trivial⟩,
    indepF_assign fv v.i _ hn.i (exprIndepF_incW fv v.i hn.i)⟩

lemma indepF_postT : IndepY fv (postT (M := M) p v tv) :=
  ⟨⟨hn.z, noiseK_blind fv p.σ2⟩,
    indepF_assign fv v.Y _ hn.Y (exprIndepF_relEM fv hn),
    indepF_assign fv v.acc _ hn.acc (exprIndepF_sumEM fv hn),
    indepF_assign fv v.x _ hn.x (exprIndepF_modelEM fv hn),
    indepF_releaseX fv hn,
    indepF_assign fv tv _ hn.t (exprIndepF_incW fv tv hn.t)⟩

lemma indepF_roundT : IndepY fv (roundT (M := M) p v tv q elig uv hok) :=
  ⟨indepF_assign fv v.i _ hn.i (ExprIndep.cst fv _),
    ⟨exprIndepF_ltCE fv v.i hn.i n, indepF_recBT fv hn⟩,
    indepF_postT fv hn⟩

/-! The target-side fragments, parametric in their expressions. -/

lemma indepF_postTE {ez : Expr M (.vec d)} (hez : ExprIndep fv ez) :
    IndepY fv (postTE (M := M) p v tv ez) :=
  ⟨indepF_assign fv v.z _ hn.z hez,
    indepF_assign fv v.Y _ hn.Y (exprIndepF_relEM fv hn),
    indepF_assign fv v.acc _ hn.acc (exprIndepF_sumEM fv hn),
    indepF_assign fv v.x _ hn.x (exprIndepF_modelEM fv hn),
    indepF_releaseX fv hn,
    indepF_assign fv tv _ hn.t (exprIndepF_incW fv tv hn.t)⟩

lemma indepF_roundTE {ez : Expr M (.vec d)} (hez : ExprIndep fv ez) :
    IndepY fv (roundTE (M := M) p v tv q elig uv hok ez) :=
  ⟨indepF_assign fv v.i _ hn.i (ExprIndep.cst fv _),
    ⟨exprIndepF_ltCE fv v.i hn.i n, indepF_recBT fv hn⟩,
    indepF_postTE fv hn hez⟩

lemma indepF_recJTE {eb : Expr M .bool} (heb : ExprIndep fv eb) :
    IndepY fv (recJTE (M := M) p v tv elig uv hok eb) :=
  ⟨⟨exprIndepF_eligE fv hn,
      ⟨hn.u, indepF_assign fv uv _ hn.u heb,
        indepF_assign fv v.H _ hn.H (exprIndepF_histE fv hn)⟩, trivial⟩,
    indepF_assign fv v.i _ hn.i (exprIndepF_incW fv v.i hn.i)⟩

lemma indepF_roundITE (j : ℕ) {eb : Expr M .bool} (heb : ExprIndep fv eb)
    {ez : Expr M (.vec d)} (hez : ExprIndep fv ez) :
    IndepY fv (roundITE (M := M) p v tv q elig uv hok j eb ez) :=
  ⟨indepF_assign fv v.i _ hn.i (ExprIndep.cst fv _),
    indepF_iterCmd fv (indepF_recBT fv hn) j,
    indepF_recJTE fv hn heb,
    indepF_iterCmd fv (indepF_recBT fv hn) _,
    indepF_postTE fv hn hez⟩

lemma indepF_iterTE : ∀ (K : ℕ) (ez : Fin K → Expr M (.vec d)),
    (∀ l, ExprIndep fv (ez l)) → IndepY fv (iterTE (M := M) p v tv q elig uv hok K ez)
  | 0, _, _ => trivial
  | K + 1, ez, hez => ⟨indepF_roundTE fv hn (hez 0),
      indepF_iterTE K (Fin.tail ez) (fun l => hez l.succ)⟩

end FreshVar

/-! ## The noise of a round, presampled

The round's Gaussian is named into a fresh scratch block (`CEquiv.nameDraw`), and the
block grows over the round's head, leaving the draw first. -/

/-! ### The transport package

The variables the restriction is determined by, the determinedness itself, and each
one's freshness: what [E-Seq-V] (`CEquiv.seqVals`) needs to carry the restriction past
program fragments. -/

section Transport

variable {R : St M → Prop} (ys : List ((t : Ty) × Vars ident t))

/-- Everything `CEquiv.seqVals` and the freshness lemmas need of the restriction's
    variables. -/
structure TransportT (v : TVars ident d T T τ) (tv : Vars ident .nat)
    (uv : Vars ident .bool) (ys : List ((t : Ty) × Vars ident t)) (R : St M → Prop) :
    Prop where
  det : ∀ s s' : St M,
    (∀ z ∈ ys, M.get s.1 z.1 z.2.name = M.get s'.1 z.1 z.2.name) → R s → R s'
  fn : ∀ z ∈ ys, FNamesT v tv uv z.2.name

variable {ys} (ht : TransportT (M := M) v tv uv ys R)

include ht

/-- Transport past a head that writes none of the package's variables. -/
lemma TransportT.seq {c₁ c₂ c₂' : Cmd ident M}
    (hnw : ∀ z ∈ ys, NoWrite z.2.name c₁) (h : CEquiv R c₂ c₂') :
    CEquiv R (Cmd.seq c₁ c₂) (Cmd.seq c₁ c₂') :=
  CEquiv.seqVals ys ht.det hnw h

lemma TransportT.nw_while :
    ∀ z ∈ ys, NoWrite z.2.name
      (Cmd.while (ltCE (M := M) v.i n) (recBT p v tv q elig uv hok)) :=
  fun z hz =>
    noWrite_of_indepY z.2
      ⟨exprIndepF_ltCE z.2 v.i (ht.fn z hz).i n, indepF_recBT z.2 (ht.fn z hz)⟩

lemma TransportT.nw_iterJ (j : ℕ) :
    ∀ z ∈ ys, NoWrite z.2.name (iterCmd (recBT (M := M) p v tv q elig uv hok) j) :=
  fun z hz =>
    noWrite_of_indepY z.2 (indepF_iterCmd z.2 (indepF_recBT z.2 (ht.fn z hz)) j)

lemma TransportT.nw_i0 :
    ∀ z ∈ ys, NoWrite z.2.name (Cmd.assign (M := M) v.i (Expr.cst (t := .nat) 0)) :=
  fun z hz =>
    noWrite_of_indepY z.2 (indepF_assign z.2 v.i _ (ht.fn z hz).i (ExprIndep.cst z.2 _))

/-- The restriction survives setting the loop counter, since the counter is none of the
    package's variables. -/
lemma TransportT.det_set_i (s : St M) (hs : R s) (w : ℕ) :
    R ((M.set s.1 .nat v.i.name w, s.2) : St M) :=
  ht.det s _ (fun z hz =>
    (M.get_set_ne .nat z.1 s.1 v.i.name z.2.name w (Or.inr (ht.fn z hz).i)).symm) hs

end Transport

section NoiseStep

variable {m : ℕ} (g : Vars ident (.vec d)) {R : St M → Prop}
  (hgd : ∀ s : St M, R s → M.get s.1 (.vec d) g.name = default)
  (hn : FNamesT v tv uv g.name)

/-- The noise kernel is constant. -/
lemma noiseK_const (σ2 : ℝ≥0) (h : M.heap) :
    noiseKernelE (M := M) (d := d) σ2 h = gaussE (0 : EuclideanSpace ℝ (Fin d)) σ2 := by
  show gaussKernelE (M := M) (fun _ => (0 : EuclideanSpace ℝ (Fin d)))
      measurable_const σ2 h = _
  rw [gaussKernelE_apply]

include hgd hn

/-- **The round tail, its Gaussian named**: `postT ≡ local g in (g ←$ 𝒩 ; postTE g)`. -/
lemma cequiv_postT_name :
    CEquiv R (postT (M := M) p v tv)
      (Cmd.loc g (Cmd.seq (Cmd.random g (noiseKernelE p.σ2))
        (postTE p v tv (Expr.var g)))) :=
  have hiTail : IndepY g (Cmd.seq (Cmd.assign (M := M) v.Y (relEM p.C v tv))
      (Cmd.seq (Cmd.assign v.acc (sumEM p v tv))
        (Cmd.seq (Cmd.assign v.x (modelEM p v))
          (Cmd.seq (Cmd.release (Expr.var v.x)) (Cmd.assign tv (incW tv)))))) :=
    ⟨indepF_assign g v.Y _ hn.Y (exprIndepF_relEM g hn),
      indepF_assign g v.acc _ hn.acc (exprIndepF_sumEM g hn),
      indepF_assign g v.x _ hn.x (exprIndepF_modelEM g hn),
      indepF_releaseX g hn,
      indepF_assign g tv _ hn.t (exprIndepF_incW g tv hn.t)⟩
  (CEquiv.congrHead
      (CEquiv.nameDraw g v.z hn.z (noiseKernelE p.σ2) hgd).symm).trans
    (CEquiv.extendBlockDraw g hiTail)

/-- **A round, its Gaussian named**: `roundT ≡ local g in (g ←$ 𝒩 ; roundTE g)`.
    The restriction travels past the round's head with the transport package. -/
lemma cequiv_roundT_name {ys : List ((t : Ty) × Vars ident t)}
    (ht : TransportT (M := M) v tv uv ys R) (hok : TOK p v) :
    CEquiv R (roundT (M := M) p v tv q elig uv hok)
      (Cmd.loc g (Cmd.seq (Cmd.random g (noiseKernelE p.σ2))
        (roundTE p v tv q elig uv hok (Expr.var g)))) := by
  have hiW : IndepY g (Cmd.while (ltCE (M := M) v.i n) (recBT p v tv q elig uv hok)) :=
    ⟨exprIndepF_ltCE g v.i hn.i n, indepF_recBT g hn⟩
  have hκ : ∀ h : M.heap, noiseKernelE (M := M) (d := d) p.σ2 h
      = gaussE (0 : EuclideanSpace ℝ (Fin d)) p.σ2 := noiseK_const p.σ2
  -- reach `postT` with the restriction intact, then hoist the block over the two heads
  have h1 : CEquiv R (Cmd.seq (Cmd.while (ltCE (M := M) v.i n) (recBT p v tv q elig uv hok))
        (postT p v tv))
      (Cmd.seq (Cmd.while (ltCE (M := M) v.i n) (recBT p v tv q elig uv hok))
        (Cmd.loc g (Cmd.seq (Cmd.random g (noiseKernelE p.σ2))
          (postTE p v tv (Expr.var g))))) :=
    ht.seq ht.nw_while (cequiv_postT_name g hgd hn)
  have h2 : CEquiv R (roundT (M := M) p v tv q elig uv hok)
      (Cmd.seq (Cmd.assign v.i (Expr.cst (t := .nat) 0))
        (Cmd.seq (Cmd.while (ltCE (M := M) v.i n) (recBT p v tv q elig uv hok))
          (Cmd.loc g (Cmd.seq (Cmd.random g (noiseKernelE p.σ2))
            (postTE p v tv (Expr.var g)))))) :=
    ht.seq ht.nw_i0 h1
  refine h2.trans ?_
  refine (CEquiv.congrTail (CEquiv.hoistDraw g hκ hiW)).trans ?_
  exact CEquiv.hoistDraw g hκ (indepF_assign g v.i _ hn.i (ExprIndep.cst g _))

end NoiseStep

/-! ## The coin of the distinguished record, presampled

The coin is drawn inside `if eligible then … else skip`, into `uv`.  The derivation names
it into a fresh scratch Boolean inside the branch (`CEquiv.nameDraw`), narrows `uv`'s block
off the new draw (`CEquiv.locNarrow`), and then applies [E-Defer-C] to the fresh variable,
whose default the ambient restriction supplies. -/

section CoinStep

variable (bb : Vars ident .bool) {R : St M → Prop}
  (hbd : ∀ s : St M, R s → M.get s.1 .bool bb.name = default)
  (hn : FNamesT v tv uv bb.name)

include hbd hn

/-- **The distinguished record, its coin named and lifted out of the conditional**:
    `recBT ≡ local bb in (bb ←$ Bern q ; recJTE bb)`. -/
lemma cequiv_recBT_coin (hok : TOK p v) :
    CEquiv R (recBT (M := M) p v tv q elig uv hok)
      (Cmd.loc bb (Cmd.seq (Cmd.random bb (bernoulliKernel q))
        (recJTE p v tv elig uv hok (Expr.var bb)))) := by
  have hiA : IndepY bb (Cmd.assign (M := M) v.H (histE p v tv uv hok)) :=
    indepF_assign bb v.H _ hn.H (exprIndepF_histE bb hn)
  -- the branch: name the coin, grow the scratch block over the history store,
  -- and narrow `uv`'s block off the fresh draw
  have hbranch : CEquiv (fun s : St M => M.get s.1 .bool bb.name = default)
      (Cmd.loc uv (Cmd.seq (Cmd.random uv (bernoulliKernel q))
        (Cmd.assign v.H (histE p v tv uv hok))))
      (Cmd.loc bb (Cmd.seq (Cmd.random bb (bernoulliKernel q))
        (Cmd.loc uv (Cmd.seq (Cmd.assign uv (Expr.var bb))
          (Cmd.assign v.H (histE p v tv uv hok)))))) := by
    have hinner : CEquiv (fun s : St M => M.get s.1 .bool bb.name = default)
        (Cmd.seq (Cmd.random (M := M) uv (bernoulliKernel q))
          (Cmd.assign v.H (histE p v tv uv hok)))
        (Cmd.loc bb (Cmd.seq (Cmd.random bb (bernoulliKernel q))
          (Cmd.seq (Cmd.assign uv (Expr.var bb))
            (Cmd.assign v.H (histE p v tv uv hok))))) :=
      (CEquiv.congrHead
          (CEquiv.nameDraw bb uv hn.u (bernoulliKernel q) (fun s hs => hs)).symm).trans
        (CEquiv.extendBlockDraw bb hiA)
    have houter : CEquiv (fun s : St M => M.get s.1 .bool bb.name = default)
        (Cmd.loc uv (Cmd.loc bb (Cmd.seq (Cmd.random (M := M) bb (bernoulliKernel q))
          (Cmd.seq (Cmd.assign uv (Expr.var bb))
            (Cmd.assign v.H (histE p v tv uv hok))))))
        (Cmd.loc bb (Cmd.seq (Cmd.random bb (bernoulliKernel q))
          (Cmd.loc uv (Cmd.seq (Cmd.assign uv (Expr.var bb))
            (Cmd.assign v.H (histE p v tv uv hok)))))) :=
      (CEquiv.locComm uv bb hn.u _).trans
        (CEquiv.congrLocT bb (CEquiv.locNarrow uv ⟨hn.u.symm, bern_blind uv⟩))
    refine CEquiv.trans (CEquiv.congrLoc uv
      (R' := fun s : St M => M.get s.1 .bool bb.name = default)
      (fun s hs => ?_) hinner) houter
    show M.get (M.set s.1 .bool uv.name default) .bool bb.name = default
    rw [M.get_set_ne _ _ s.1 uv.name bb.name default (Or.inr hn.u)]; exact hs
  -- the conditional: the fresh scratch's block leaves it, by the conditional defer
  have hcond : CEquiv R
      (Cmd.cond (eligE (M := M) v tv elig)
        (Cmd.loc uv (Cmd.seq (Cmd.random uv (bernoulliKernel q))
          (Cmd.assign v.H (histE p v tv uv hok)))) Cmd.skip)
      (Cmd.loc bb (Cmd.seq (Cmd.random bb (bernoulliKernel q))
        (Cmd.cond (eligE v tv elig)
          (Cmd.loc uv (Cmd.seq (Cmd.assign uv (Expr.var bb))
            (Cmd.assign v.H (histE p v tv uv hok)))) Cmd.skip))) := by
    refine (CEquiv.congrCond (CEquiv.weaken (fun s hs => hbd s hs.1) hbranch)
      (CEquiv.refl _)).trans ?_
    refine CEquiv.weaken (R' := fun s : St M => resetV bb s = s) (fun s hs => ?_) ?_
    · exact Prod.ext
        (show M.set s.1 .bool bb.name default = s.1 by
          rw [← hbd s hs]; exact M.set_get_eq _ _ _) rfl
    · exact CEquiv.deferCond bb (bernoulliKernel q) trivial (exprIndepF_eligE bb hn)
  -- the record: the block grows over the index increment
  refine (CEquiv.congrHead hcond).trans ?_
  exact CEquiv.extendBlockDraw bb
    (indepF_assign bb v.i _ hn.i (exprIndepF_incW bb v.i hn.i))

end CoinStep

/-! ## The distinguished round, presampled

The record loop is unrolled by its counter ([E-Count]), record `j`'s coin leaves its
conditional (`cequiv_recBT_coin`), the Gaussian is named (`cequiv_postT_name`), and both
scratch blocks grow to the round's front, around `roundITE j` reading the scratches. -/

section RoundStep

variable (bb : Vars ident .bool) (g : Vars ident (.vec d)) {R : St M → Prop}
  (hbg : bb.name ≠ g.name)
  (hbd : ∀ s : St M, R s → M.get s.1 .bool bb.name = default)
  (hgd : ∀ s : St M, R s → M.get s.1 (.vec d) g.name = default)
  (hnb : FNamesT v tv uv bb.name) (hng : FNamesT v tv uv g.name)

include hbg hbd hgd hnb hng

/-- **The distinguished round named**:
    `roundT ≡ local bb in (bb ←$ Bern q ; local g in (g ←$ 𝒩 ; roundITE j bb g))`. -/
lemma cequiv_roundIT_name {ys : List ((t : Ty) × Vars ident t)}
    (ht : TransportT (M := M) v tv uv ys R)
    (hok : TOK p v) (hu : UOK v tv tv uv) {j : ℕ} (hj : j < n) :
    CEquiv R (roundT (M := M) p v tv q elig uv hok)
      (Cmd.loc bb (Cmd.seq (Cmd.random bb (bernoulliKernel q))
        (Cmd.loc g (Cmd.seq (Cmd.random g (noiseKernelE p.σ2))
          (roundITE p v tv q elig uv hok j (Expr.var bb) (Expr.var g)))))) := by
  have hκb : ∀ h : M.heap, bernoulliKernel (M := M) q h = bernoulliMeasure q := fun _ => rfl
  have hκg : ∀ h : M.heap, noiseKernelE (M := M) (d := d) p.σ2 h
      = gaussE (0 : EuclideanSpace ℝ (Fin d)) p.σ2 := noiseK_const p.σ2
  -- the independence facts
  have hiBJ : IndepY bb (iterCmd (recBT (M := M) p v tv q elig uv hok) j) :=
    indepF_iterCmd bb (indepF_recBT bb hnb) j
  have hiBJ' : IndepY bb (iterCmd (recBT (M := M) p v tv q elig uv hok) (n - j - 1)) :=
    indepF_iterCmd bb (indepF_recBT bb hnb) _
  have hiBP : IndepY bb (postT (M := M) p v tv) := indepF_postT bb hnb
  have hiBA : IndepY bb (Cmd.assign (M := M) v.i (Expr.cst (t := .nat) 0)) :=
    indepF_assign bb v.i _ hnb.i (ExprIndep.cst bb _)
  have hiGJ : IndepY g (iterCmd (recBT (M := M) p v tv q elig uv hok) j) :=
    indepF_iterCmd g (indepF_recBT g hng) j
  have hiGJ' : IndepY g (iterCmd (recBT (M := M) p v tv q elig uv hok) (n - j - 1)) :=
    indepF_iterCmd g (indepF_recBT g hng) _
  have hiGR : IndepY g (recJTE (M := M) p v tv elig uv hok (Expr.var bb)) :=
    indepF_recJTE g hng (ExprIndep.var g bb hbg)
  have hiGA : IndepY g (Cmd.assign (M := M) v.i (Expr.cst (t := .nat) 0)) :=
    indepF_assign g v.i _ hng.i (ExprIndep.cst g _)
  have hiGB : IndepY g (Cmd.random (M := M) bb (bernoulliKernel q)) :=
    ⟨hbg, bern_blind g⟩
  -- Phase 1a: unroll the record loop by its counter, at the head `i ≔ 0`
  have hunroll : CEquiv (fun s : St M => tIN v s.1 + n = n)
      (Cmd.while (ltCE (M := M) v.i n) (recBT p v tv q elig uv hok))
      (iterCmd (recBT p v tv q elig uv hok) n) := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h17, -⟩ := v.ne
    exact CEquiv.count v.i n (c := recBT p v tv q elig uv hok)
      ⟨⟨⟨hu.ui, hu.ui, Ne.symm h17⟩, trivial⟩, Or.inl rfl⟩ n
  -- Phase 1b: split the unrolled loop around record `j`
  have hsplit : ∀ R' : St M → Prop, CEquiv R'
      (iterCmd (recBT (M := M) p v tv q elig uv hok) n)
      (Cmd.seq (iterCmd (recBT p v tv q elig uv hok) j)
        (Cmd.seq (iterCmd (recBT p v tv q elig uv hok) 1)
          (iterCmd (recBT p v tv q elig uv hok) (n - j - 1)))) := by
    intro R'
    have hcount : iterCmd (recBT (M := M) p v tv q elig uv hok) n
        = iterCmd (recBT p v tv q elig uv hok) (j + (1 + (n - j - 1))) :=
      congrArg _ (by omega)
    rw [hcount]
    exact CEquiv.iterCmd_split _ _ _ R'
  -- Phase 1c: at the ambient restriction, replace record `j` and the tail noise
  have hcoin : CEquiv R
      (Cmd.seq (recBT (M := M) p v tv q elig uv hok)
        (Cmd.seq (iterCmd (recBT p v tv q elig uv hok) (n - j - 1)) (postT p v tv)))
      (Cmd.loc bb (Cmd.seq (Cmd.random bb (bernoulliKernel q))
        (Cmd.seq (recJTE p v tv elig uv hok (Expr.var bb))
          (Cmd.seq (iterCmd (recBT p v tv q elig uv hok) (n - j - 1)) (postT p v tv))))) :=
    (CEquiv.congrHead (cequiv_recBT_coin bb hbd hnb hok)).trans
      (CEquiv.extendBlockDraw bb ⟨hiBJ', hiBP⟩)
  have hnoise : CEquiv R
      (Cmd.loc bb (Cmd.seq (Cmd.random (M := M) bb (bernoulliKernel q))
        (Cmd.seq (recJTE p v tv elig uv hok (Expr.var bb))
          (Cmd.seq (iterCmd (recBT p v tv q elig uv hok) (n - j - 1)) (postT p v tv)))))
      (Cmd.loc bb (Cmd.seq (Cmd.random bb (bernoulliKernel q))
        (Cmd.seq (recJTE p v tv elig uv hok (Expr.var bb))
          (Cmd.seq (iterCmd (recBT p v tv q elig uv hok) (n - j - 1))
            (Cmd.loc g (Cmd.seq (Cmd.random g (noiseKernelE p.σ2))
              (postTE p v tv (Expr.var g)))))))) := by
    refine CEquiv.congrLoc bb (R' := fun s : St M => M.get s.1 (.vec d) g.name = default)
      (fun s hs => ?_) ?_
    · show M.get (M.set s.1 .bool bb.name default) (.vec d) g.name = default
      rw [M.get_set_ne _ _ s.1 bb.name g.name default (Or.inr hbg)]; exact hgd s hs
    · refine CEquiv.seqVal g (fun s s' h hs => h.symm.trans hs)
        (noWrite_of_indepY g hiGB) ?_
      refine CEquiv.seqVal g (fun s s' h hs => h.symm.trans hs)
        (noWrite_of_indepY g hiGR) ?_
      exact CEquiv.seqVal g (fun s s' h hs => h.symm.trans hs)
        (noWrite_of_indepY g hiGJ')
        (cequiv_postT_name g (fun _ hs => hs) hng)
  -- the Gaussian's block to the front of the inner content
  have hgfront : CEquiv R
      (Cmd.loc bb (Cmd.seq (Cmd.random (M := M) bb (bernoulliKernel q))
        (Cmd.seq (recJTE p v tv elig uv hok (Expr.var bb))
          (Cmd.seq (iterCmd (recBT p v tv q elig uv hok) (n - j - 1))
            (Cmd.loc g (Cmd.seq (Cmd.random g (noiseKernelE p.σ2))
              (postTE p v tv (Expr.var g))))))))
      (Cmd.loc bb (Cmd.seq (Cmd.random bb (bernoulliKernel q))
        (Cmd.loc g (Cmd.seq (Cmd.random g (noiseKernelE p.σ2))
          (Cmd.seq (recJTE p v tv elig uv hok (Expr.var bb))
            (Cmd.seq (iterCmd (recBT p v tv q elig uv hok) (n - j - 1))
              (postTE p v tv (Expr.var g)))))))) :=
    CEquiv.congrLocT bb <| CEquiv.congrTail <|
      (CEquiv.congrTail (CEquiv.hoistDraw g hκg hiGJ')).trans
        (CEquiv.hoistDraw g hκg hiGR)
  -- Phase 1: everything under the heads `i ≔ 0` and the first `j` records
  have hphase1 : CEquiv R (roundT (M := M) p v tv q elig uv hok)
      (Cmd.seq (Cmd.assign v.i (Expr.cst (t := .nat) 0))
        (Cmd.seq (iterCmd (recBT p v tv q elig uv hok) j)
          (Cmd.loc bb (Cmd.seq (Cmd.random bb (bernoulliKernel q))
            (Cmd.loc g (Cmd.seq (Cmd.random g (noiseKernelE p.σ2))
              (Cmd.seq (recJTE p v tv elig uv hok (Expr.var bb))
                (Cmd.seq (iterCmd (recBT p v tv q elig uv hok) (n - j - 1))
                  (postTE p v tv (Expr.var g)))))))))) := by
    refine CEquiv.congrSeqDet v.i (Expr.cst (t := .nat) 0)
      (R' := fun s : St M => (tIN v s.1 + n = n) ∧ R s)
      (fun s hs => ?_) ?_
    · refine ⟨?_, ?_⟩
      · show M.get (M.set s.1 .nat v.i.name 0) .nat v.i.name + n = n
        rw [M.get_set_eq]
        exact Nat.zero_add n
      · exact ht.det_set_i s hs 0
    · -- the loop body, at `tIN = 0 ∧ scratch defaults`
      refine (CEquiv.congrHead (CEquiv.weaken (fun s hs => hs.1) hunroll)).trans ?_
      refine CEquiv.weaken (R' := R) (fun s hs => hs.2) ?_
      refine (CEquiv.congrHead (hsplit R)).trans ?_
      refine (CEquiv.seqAssoc).trans ?_
      refine (CEquiv.congrTail (CEquiv.seqAssoc)).trans ?_
      refine (CEquiv.congrTail (CEquiv.congrHead (CEquiv.seqSkip _))).trans ?_
      exact ht.seq (ht.nw_iterJ j) (hcoin.trans (hnoise.trans hgfront))
  -- Phase 2: both blocks over the heads, draws staying first
  refine hphase1.trans ?_
  refine (CEquiv.congrTail ((CEquiv.hoistDraw bb hκb hiBJ).trans
    (CEquiv.congrLocT bb (CEquiv.congrTail
      (CEquiv.hoistDraw g hκg hiGJ))))).trans ?_
  refine (CEquiv.hoistDraw bb hκb hiBA).trans ?_
  exact CEquiv.congrLocT bb (CEquiv.congrTail (CEquiv.hoistDraw g hκg hiGA))

end RoundStep

/-! ## The window, presampled

By induction over rounds: each round's Gaussian is named into its own scratch block
(`cequiv_roundT_name`) and the blocks nest with their draws in front.  The tail of the
induction runs at the defaults of the remaining scratches only (`CEquiv.weaken`,
`CEquiv.seqVals`). -/

section WindowStep

/-- The transport package of a family of scratch vectors. -/
lemma transportT_ofFn {K : ℕ} (gs : Fin K → Vars ident (.vec d))
    (hfn : ∀ l, FNamesT (ident := ident) v tv uv (gs l).name) :
    TransportT (M := M) v tv uv (List.ofFn fun l => ⟨.vec d, gs l⟩)
      (fun s : St M => ∀ l, M.get s.1 (.vec d) (gs l).name = default) where
  det s s' h hs l :=
    (h ⟨.vec d, gs l⟩ (List.mem_ofFn.mpr ⟨l, rfl⟩)).symm.trans (hs l)
  fn z hz := by
    obtain ⟨l, rfl⟩ := List.mem_ofFn.mp hz
    exact hfn l

/-- **The plain rounds, presampled**: `K` rounds of `roundT` are `K` nested scratch
    blocks, draws first, around `iterTE` reading the scratches. -/
lemma cequiv_iterT_name (hok : TOK p v) :
    ∀ (K : ℕ) (gs : Fin K → Vars ident (.vec d)),
      (∀ l, FNamesT (ident := ident) v tv uv (gs l).name) →
      (∀ l l' : Fin K, l ≠ l' → (gs l).name ≠ (gs l').name) →
      CEquiv (fun s : St M => ∀ l, M.get s.1 (.vec d) (gs l).name = default)
        (iterCmd (roundT (M := M) p v tv q elig uv hok) K)
        (nestDraws (noiseKernelE p.σ2) K gs
          (iterTE p v tv q elig uv hok K (fun l => Expr.var (gs l))))
  | 0, _, _, _ => CEquiv.refl _
  | K + 1, gs, hfn, hgg => by
    have hκg : ∀ h : M.heap, noiseKernelE (M := M) (d := d) p.σ2 h
        = gaussE (0 : EuclideanSpace ℝ (Fin d)) p.σ2 := noiseK_const p.σ2
    have hiTailRTE : ∀ l : Fin K, IndepY (Fin.tail gs l)
        (roundTE (M := M) p v tv q elig uv hok (Expr.var (gs 0))) := fun l =>
      indepF_roundTE (Fin.tail gs l) (hfn l.succ)
        (ExprIndep.var (Fin.tail gs l) (gs 0) (hgg 0 l.succ (Fin.succ_ne_zero l).symm))
    have hi0nest : IndepY (gs 0)
        (nestDraws (M := M) (noiseKernelE p.σ2) K (Fin.tail gs)
          (iterTE p v tv q elig uv hok K (fun l => Expr.var (Fin.tail gs l)))) :=
      indepY_nestDraws (gs 0) (noiseK_blind (gs 0) p.σ2)
        (indepF_iterTE (gs 0) (hfn 0) K (fun l => Expr.var (Fin.tail gs l)) (fun l =>
          ExprIndep.var (gs 0) (Fin.tail gs l) (hgg l.succ 0 (Fin.succ_ne_zero l))))
        K (Fin.tail gs) (fun l => hgg l.succ 0 (Fin.succ_ne_zero l))
    -- the head round named, at the full restriction
    refine (CEquiv.congrHead (cequiv_roundT_name (gs 0) (fun s hs => hs 0) (hfn 0)
      (transportT_ofFn gs hfn) hok)).trans ?_
    -- the remaining rounds, at the tail's restriction
    have htail : CEquiv
        (fun s : St M => ∀ l : Fin K, M.get s.1 (.vec d) (Fin.tail gs l).name = default)
        (iterCmd (roundT (M := M) p v tv q elig uv hok) K)
        (nestDraws (noiseKernelE p.σ2) K (Fin.tail gs)
          (iterTE p v tv q elig uv hok K (fun l => Expr.var (Fin.tail gs l)))) :=
      cequiv_iterT_name hok K (Fin.tail gs) (fun l => hfn l.succ)
        (fun l l' hll => hgg l.succ l'.succ (by
          intro hcon; exact hll (Fin.succ_injective _ hcon)))
    have hnwHead : ∀ z ∈ (List.ofFn fun l => (⟨.vec d, Fin.tail gs l⟩ :
        (t : Ty) × Vars ident t)), NoWrite z.2.name (Cmd.loc (gs 0)
        (Cmd.seq (Cmd.random (M := M) (gs 0) (noiseKernelE p.σ2))
          (roundTE p v tv q elig uv hok (Expr.var (gs 0))))) := by
      intro z hz
      obtain ⟨l, rfl⟩ := List.mem_ofFn.mp hz
      refine ⟨fun hcon => hgg 0 l.succ (Fin.succ_ne_zero l).symm hcon, ?_, ?_⟩
      · exact fun hcon => hgg 0 l.succ (Fin.succ_ne_zero l).symm hcon
      · exact noWrite_of_indepY (Fin.tail gs l) (hiTailRTE l)
    have hmid : CEquiv
        (fun s : St M => ∀ l : Fin K, M.get s.1 (.vec d) (Fin.tail gs l).name = default)
        (Cmd.seq (Cmd.loc (gs 0)
          (Cmd.seq (Cmd.random (gs 0) (noiseKernelE p.σ2))
            (roundTE p v tv q elig uv hok (Expr.var (gs 0)))))
          (iterCmd (roundT (M := M) p v tv q elig uv hok) K))
        (Cmd.seq (Cmd.loc (gs 0)
          (Cmd.seq (Cmd.random (gs 0) (noiseKernelE p.σ2))
            (roundTE p v tv q elig uv hok (Expr.var (gs 0)))))
          (nestDraws (noiseKernelE p.σ2) K (Fin.tail gs)
            (iterTE p v tv q elig uv hok K (fun l => Expr.var (Fin.tail gs l))))) :=
      (transportT_ofFn (Fin.tail gs) (fun l => hfn l.succ)).seq hnwHead htail
    refine (CEquiv.weaken (fun s hs (l : Fin K) => hs l.succ) hmid).trans ?_
    -- assemble: the head block over the nest, the head round into the nest
    refine (CEquiv.extendBlockDraw (gs 0) hi0nest).trans ?_
    exact CEquiv.congrLocT (gs 0) (CEquiv.congrTail
      (CEquiv.nestIn hκg K (Fin.tail gs) hiTailRTE))

end WindowStep

/-! ## The whole window, presampled -/

section WindowAll

variable {m : ℕ} (bb : Vars ident .bool) (gs : Fin (m + 1) → Vars ident (.vec d))

/-- The window's scratch-default restriction: the coin's scratch and every round's. -/
def ScrD (bb : Vars ident .bool) (gs : Fin (m + 1) → Vars ident (.vec d))
    (s : St M) : Prop :=
  M.get s.1 .bool bb.name = default ∧
    ∀ l, M.get s.1 (.vec d) (gs l).name = default

variable
  (hbg : ∀ l, bb.name ≠ (gs l).name)
  (hgg : ∀ l l' : Fin (m + 1), l ≠ l' → (gs l).name ≠ (gs l').name)
  (hnb : FNamesT (ident := ident) v tv uv bb.name)
  (hng : ∀ l, FNamesT (ident := ident) v tv uv (gs l).name)

include hbg hgg hnb hng

omit hbg hgg in
/-- The transport package of the coin's scratch and the rounds'. -/
lemma transportT_scr : TransportT (M := M) v tv uv
    (⟨.bool, bb⟩ :: List.ofFn fun l => ⟨.vec d, gs l⟩) (ScrD bb gs) where
  det s s' h hs := by
    refine ⟨(h ⟨.bool, bb⟩ (List.mem_cons_self ..)).symm.trans hs.1, fun l => ?_⟩
    exact (h ⟨.vec d, gs l⟩ (List.mem_cons_of_mem _
      (List.mem_ofFn.mpr ⟨l, rfl⟩))).symm.trans (hs.2 l)
  fn z hz := by
    rcases List.mem_cons.mp hz with rfl | hz
    · exact hnb
    · obtain ⟨l, rfl⟩ := List.mem_ofFn.mp hz
      exact hng l

/-- **The window named**: `m + 1` rounds of `dpftrlBandedGen` are the coin's scratch block and
    `m + 1` nested noise blocks, all draws in front, around `windowE` reading the
    scratches. -/
theorem cequiv_windowT_name (hok : TOK p v) (hu : UOK v tv tv uv) {j : ℕ} (hj : j < n) :
    CEquiv (ScrD (M := M) bb gs)
      (iterCmd (roundT (M := M) p v tv q elig uv hok) (m + 1))
      (Cmd.loc bb (Cmd.seq (Cmd.random bb (bernoulliKernel q))
        (nestDraws (noiseKernelE p.σ2) (m + 1) gs
          (windowE p v tv q elig uv hok j m (Expr.var bb)
            (fun l => Expr.var (gs l)))))) := by
  have hκg : ∀ h : M.heap, noiseKernelE (M := M) (d := d) p.σ2 h
      = gaussE (0 : EuclideanSpace ℝ (Fin d)) p.σ2 := noiseK_const p.σ2
  -- the independence facts
  have hiTailRIT : ∀ l : Fin m, IndepY (Fin.tail gs l)
      (roundITE (M := M) p v tv q elig uv hok j (Expr.var bb) (Expr.var (gs 0))) := fun l =>
    indepF_roundITE (Fin.tail gs l) (hng l.succ) j
      (ExprIndep.var (Fin.tail gs l) bb (hbg l.succ))
      (ExprIndep.var (Fin.tail gs l) (gs 0) (hgg 0 l.succ (Fin.succ_ne_zero l).symm))
  have hi0nest : IndepY (gs 0)
      (nestDraws (M := M) (noiseKernelE p.σ2) m (Fin.tail gs)
        (iterTE p v tv q elig uv hok m (fun l => Expr.var (Fin.tail gs l)))) :=
    indepY_nestDraws (gs 0) (noiseK_blind (gs 0) p.σ2)
      (indepF_iterTE (gs 0) (hng 0) m (fun l => Expr.var (Fin.tail gs l)) (fun l =>
        ExprIndep.var (gs 0) (Fin.tail gs l) (hgg l.succ 0 (Fin.succ_ne_zero l))))
      m (Fin.tail gs) (fun l => hgg l.succ 0 (Fin.succ_ne_zero l))
  have hibnest : IndepY bb
      (nestDraws (M := M) (noiseKernelE p.σ2) m (Fin.tail gs)
        (iterTE p v tv q elig uv hok m (fun l => Expr.var (Fin.tail gs l)))) :=
    indepY_nestDraws bb (noiseK_blind bb p.σ2)
      (indepF_iterTE bb hnb m (fun l => Expr.var (Fin.tail gs l)) (fun l =>
        ExprIndep.var bb (Fin.tail gs l) (hbg l.succ).symm))
      m (Fin.tail gs) (fun l => (hbg l.succ).symm)
  -- the head round, distinguished; the tail rounds by the induction
  have hhead : CEquiv (ScrD (M := M) bb gs)
      (roundT (M := M) p v tv q elig uv hok)
      (Cmd.loc bb (Cmd.seq (Cmd.random bb (bernoulliKernel q))
        (Cmd.loc (gs 0) (Cmd.seq (Cmd.random (gs 0) (noiseKernelE p.σ2))
          (roundITE p v tv q elig uv hok j (Expr.var bb) (Expr.var (gs 0))))))) :=
    cequiv_roundIT_name bb (gs 0) (hbg 0) (fun s hs => hs.1)
      (fun s hs => hs.2 0) hnb (hng 0)
      (transportT_scr bb gs hnb hng) hok hu hj
  have htail : CEquiv
      (fun s : St M => ∀ l : Fin m, M.get s.1 (.vec d) (Fin.tail gs l).name = default)
      (iterCmd (roundT (M := M) p v tv q elig uv hok) m)
      (nestDraws (noiseKernelE p.σ2) m (Fin.tail gs)
        (iterTE p v tv q elig uv hok m (fun l => Expr.var (Fin.tail gs l)))) :=
    cequiv_iterT_name hok m (Fin.tail gs) (fun l => hng l.succ)
      (fun l l' hll => hgg l.succ l'.succ (by
        intro hcon; exact hll (Fin.succ_injective _ hcon)))
  have hnwHead : ∀ z ∈ (List.ofFn fun l => (⟨.vec d, Fin.tail gs l⟩ :
      (t : Ty) × Vars ident t)), NoWrite z.2.name
      (Cmd.loc bb (Cmd.seq (Cmd.random (M := M) bb (bernoulliKernel q))
        (Cmd.loc (gs 0) (Cmd.seq (Cmd.random (gs 0) (noiseKernelE p.σ2))
          (roundITE p v tv q elig uv hok j (Expr.var bb) (Expr.var (gs 0))))))) := by
    intro z hz
    obtain ⟨l, rfl⟩ := List.mem_ofFn.mp hz
    exact ⟨fun hcon => hbg l.succ hcon, fun hcon => hbg l.succ hcon,
      fun hcon => hgg 0 l.succ (Fin.succ_ne_zero l).symm hcon,
      fun hcon => hgg 0 l.succ (Fin.succ_ne_zero l).symm hcon,
      noWrite_of_indepY (Fin.tail gs l) (hiTailRIT l)⟩
  have hmid : CEquiv
      (fun s : St M => ∀ l : Fin m, M.get s.1 (.vec d) (Fin.tail gs l).name = default)
      (Cmd.seq (Cmd.loc bb (Cmd.seq (Cmd.random bb (bernoulliKernel q))
          (Cmd.loc (gs 0) (Cmd.seq (Cmd.random (gs 0) (noiseKernelE p.σ2))
            (roundITE p v tv q elig uv hok j (Expr.var bb) (Expr.var (gs 0)))))))
        (iterCmd (roundT (M := M) p v tv q elig uv hok) m))
      (Cmd.seq (Cmd.loc bb (Cmd.seq (Cmd.random bb (bernoulliKernel q))
          (Cmd.loc (gs 0) (Cmd.seq (Cmd.random (gs 0) (noiseKernelE p.σ2))
            (roundITE p v tv q elig uv hok j (Expr.var bb) (Expr.var (gs 0)))))))
        (nestDraws (noiseKernelE p.σ2) m (Fin.tail gs)
          (iterTE p v tv q elig uv hok m (fun l => Expr.var (Fin.tail gs l))))) :=
    (transportT_ofFn (Fin.tail gs) (fun l => hng l.succ)).seq hnwHead htail
  -- assemble
  refine (CEquiv.congrHead hhead).trans ?_
  refine (CEquiv.weaken (fun s hs (l : Fin m) => hs.2 l.succ) hmid).trans ?_
  refine (CEquiv.extendBlockDraw bb hibnest).trans ?_
  refine CEquiv.congrLocT bb (CEquiv.congrTail ?_)
  refine (CEquiv.extendBlockDraw (gs 0) hi0nest).trans ?_
  exact CEquiv.congrLocT (gs 0) (CEquiv.congrTail
    (CEquiv.nestIn hκg m (Fin.tail gs) hiTailRIT))

end WindowAll

/-! ## The pack kernel

`packK Φ` draws `K` Gaussians and maps them through `Φ h` — the kernel every stage of the
packing produces, with `Φ` carrying how the already-materialized reads enter. -/

section PackK

variable {m K : ℕ}

/-- Draw `K` Gaussians, then map them through `Φ h`. -/
noncomputable def packK (σ2 : ℝ≥0) {A : Ty}
    (Φ : M.heap → (Fin K → EuclideanSpace ℝ (Fin d)) → A.interp) :
    @ProbabilityTheory.Kernel M.heap A.interp M.heapMeas (Ty.measurableSpace A) :=
  Kernel.map
    ((Kernel.id : @ProbabilityTheory.Kernel M.heap M.heap M.heapMeas M.heapMeas) ×ₖ
      Kernel.const _ (Measure.pi fun _ : Fin K =>
        gaussE (0 : EuclideanSpace ℝ (Fin d)) σ2))
    (Function.uncurry Φ)

lemma packK_apply (σ2 : ℝ≥0) {A : Ty}
    {Φ : M.heap → (Fin K → EuclideanSpace ℝ (Fin d)) → A.interp}
    (hΦ : Measurable (Function.uncurry Φ)) (h : M.heap) :
    packK (M := M) σ2 Φ h
      = (Measure.pi fun _ : Fin K =>
          gaussE (0 : EuclideanSpace ℝ (Fin d)) σ2).map (Φ h) := by
  rw [packK, Kernel.map_apply _ hΦ, Kernel.prod_apply, Kernel.id_apply, Kernel.const_apply,
    Measure.dirac_prod, Measure.map_map hΦ measurable_prodMk_left]
  rfl

lemma isMarkov_packK (σ2 : ℝ≥0) {A : Ty}
    {Φ : M.heap → (Fin K → EuclideanSpace ℝ (Fin d)) → A.interp}
    (hΦ : Measurable (Function.uncurry Φ)) :
    IsMarkovKernel (packK (M := M) σ2 Φ) := by
  haveI : IsProbabilityMeasure (gaussE (0 : EuclideanSpace ℝ (Fin d)) σ2) := by
    unfold gaussE; exact Measure.isProbabilityMeasure_map (by fun_prop)
  haveI : IsProbabilityMeasure (Measure.pi fun _ : Fin K =>
      gaussE (0 : EuclideanSpace ℝ (Fin d)) σ2) := inferInstance
  refine ⟨fun h => ?_⟩
  rw [packK_apply σ2 hΦ h]
  refine ⟨?_⟩
  rw [Measure.map_apply (show Measurable (Φ h) from hΦ.comp measurable_prodMk_left)
    MeasurableSet.univ, Set.preimage_univ, measure_univ]

/-- `packK` is sub-Markov for every `Φ`: `Kernel.map` is the zero kernel when the map is
    not measurable, and the Markov kernel `isMarkov_packK` otherwise. -/
instance isSubMarkov_packK (σ2 : ℝ≥0) {A : Ty}
    (Φ : M.heap → (Fin K → EuclideanSpace ℝ (Fin d)) → A.interp) :
    IsSubMarkovKernel (packK (M := M) σ2 Φ) := by
  by_cases hΦ : Measurable (Function.uncurry Φ)
  · haveI := isMarkov_packK (M := M) σ2 hΦ; infer_instance
  · refine ⟨fun h => ?_⟩
    rw [packK, Kernel.map_of_not_measurable _ hΦ]
    simp

end PackK

/-! ## The packing induction

`K + 1` nested scratch blocks around the assignment that reads them collapse into the
single joint draw `packK`: [E-Push] at the innermost block, [E-Merge] at each outer one,
with the measure identity `packK_fuse` entering [E-Leaf-S] (`CEquiv.leafDraw`). -/

section NestPack

variable {σ2 : ℝ≥0}

/-- A map over a product measure, one coordinate at a time. -/
lemma prod_map_eq_bind_map {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace Z] (μ : Measure X) (ν : Measure Y) [SFinite ν]
    {G : X × Y → Z} (hG : Measurable G) :
    (μ.prod ν).map G = μ.bind (fun a => ν.map (fun b => G (a, b))) := by
  rw [← Measure.bind_dirac_eq_map _ hG,
    prod_bind_eq μ ν (f := fun z => Measure.dirac (G z))
      (Measure.measurable_dirac.comp hG)]
  exact Measure.bind_congr_right (Filter.Eventually.of_forall fun a =>
    Measure.bind_dirac_eq_map _ (hG.comp measurable_prodMk_left))

/-- **The fuse of one more Gaussian into a pack is the pack one longer** — the measure
    identity behind the packing induction's step. -/
lemma packK_fuse {J : ℕ} {A : Ty} (g0 : Vars ident (.vec d))
    {Φ : M.heap → (Fin (J + 1) → EuclideanSpace ℝ (Fin d)) → A.interp}
    (hΦm : Measurable (Function.uncurry Φ))
    (hΦb : ∀ (h : M.heap) (w : EuclideanSpace ℝ (Fin d)) ws,
      Φ (M.set h (.vec d) g0.name w) ws = Φ h ws) (h : M.heap) :
    fuseK g0 (noiseKernelE (M := M) (d := d) σ2)
      (packK σ2 (fun h' ws => Φ h' (Fin.cons (M.get h' (.vec d) g0.name) ws))) h
      = packK (M := M) σ2 Φ h := by
  have : IsProbabilityMeasure (gaussE (0 : EuclideanSpace ℝ (Fin d)) σ2) := by
    unfold gaussE; exact Measure.isProbabilityMeasure_map (by fun_prop)
  have hΦh : Measurable (Φ h) := hΦm.comp measurable_prodMk_left
  have hΦ'm : Measurable (Function.uncurry (fun h' ws =>
      Φ h' (Fin.cons (M.get h' (.vec d) g0.name) ws)
        : M.heap → (Fin J → EuclideanSpace ℝ (Fin d)) → A.interp)) :=
    hΦm.comp (measurable_fst.prodMk ((measurable_fin_cons J).comp
      (((M.get_measurable (.vec d) g0.name).comp measurable_fst).prodMk measurable_snd)))
  rw [fuseK_apply, noiseK_const σ2 h, packK_apply σ2 hΦm h]
  have hb : ∀ w : EuclideanSpace ℝ (Fin d),
      packK (M := M) σ2 (fun h' ws => Φ h' (Fin.cons (M.get h' (.vec d) g0.name) ws))
          (M.set h (.vec d) g0.name w)
        = (Measure.pi fun _ : Fin J =>
            gaussE (0 : EuclideanSpace ℝ (Fin d)) σ2).map
              (fun ws => Φ h (Fin.cons w ws)) := by
    intro w
    rw [packK_apply σ2 hΦ'm _]
    congr 1
    funext ws
    show Φ (M.set h (.vec d) g0.name w)
        (Fin.cons (M.get (M.set h (.vec d) g0.name w) (.vec d) g0.name) ws)
        = Φ h (Fin.cons w ws)
    rw [M.get_set_eq]
    exact hΦb h w (Fin.cons w ws)
  rw [Measure.bind_congr_right (Filter.Eventually.of_forall hb),
    pi_fin_succ_eq_map_cons (gaussE (0 : EuclideanSpace ℝ (Fin d)) σ2) J,
    Measure.map_map hΦh (measurable_fin_cons J)]
  exact (prod_map_eq_bind_map _ _ (hΦh.comp (measurable_fin_cons J))).symm

/-- **The packing induction**: `K + 1` nested scratch blocks around the assignment that
    reads them collapse into the single joint draw `packK σ2 Φ`, at the scratches'
    defaults. -/
lemma cequiv_nestPack {A : Ty} (xv : Vars ident A) :
    ∀ (K : ℕ) (gsK : Fin (K + 1) → Vars ident (.vec d))
      (hgg : ∀ l l' : Fin (K + 1), l ≠ l' → (gsK l).name ≠ (gsK l').name)
      (hxg : ∀ l, xv.name ≠ (gsK l).name)
      (e : Expr M A)
      (Φ : M.heap → (Fin (K + 1) → EuclideanSpace ℝ (Fin d)) → A.interp)
      (hΦm : Measurable (Function.uncurry Φ))
      (he : ∀ h : M.heap, esem e h = Φ h (fun l => M.get h (.vec d) (gsK l).name))
      (hΦb : ∀ (l : Fin (K + 1)) (h : M.heap) (w : EuclideanSpace ℝ (Fin d)) ws,
        Φ (M.set h (.vec d) (gsK l).name w) ws = Φ h ws),
      CEquiv (fun s : St M => ∀ l, M.get s.1 (.vec d) (gsK l).name = default)
        (nestDraws (t := Ty.vec d) (noiseKernelE (M := M) (d := d) σ2) (K + 1) gsK (Cmd.assign xv e))
        (Cmd.random xv (packK σ2 Φ))
  | 0, gsK, hgg, hxg, e, Φ, hΦm, he, hΦb => by
    have : IsProbabilityMeasure (gaussE (0 : EuclideanSpace ℝ (Fin d)) σ2) := by
      unfold gaussE; exact Measure.isProbabilityMeasure_map (by fun_prop)
    have hΦh : ∀ h : M.heap, Measurable (Φ h) := fun h => hΦm.comp measurable_prodMk_left
    -- the one-draw pack is the pushforward of the one Gaussian
    have hone : (Measure.pi fun _ : Fin 1 => gaussE (0 : EuclideanSpace ℝ (Fin d)) σ2)
        = (gaussE (0 : EuclideanSpace ℝ (Fin d)) σ2).map
            (fun w => Fin.cons w (isEmptyElim : Fin 0 → EuclideanSpace ℝ (Fin d))) := by
      rw [pi_fin_succ_eq_map_cons (gaussE (0 : EuclideanSpace ℝ (Fin d)) σ2) 0,
        Measure.pi_of_empty _ isEmptyElim, Measure.prod_dirac,
        Measure.map_map (measurable_fin_cons 0)
          (show Measurable (fun x : EuclideanSpace ℝ (Fin d) =>
              (x, fun a : Fin 0 => (isEmptyElim a : EuclideanSpace ℝ (Fin d)))) from
            measurable_id.prodMk measurable_const)]
      rfl
    have hκ' : ∀ h : M.heap, packK (M := M) σ2 Φ h
        = (noiseKernelE (M := M) (d := d) σ2 h).map
            (fun w => esem e (M.set h (.vec d) (gsK 0).name w)) := by
      intro h
      rw [noiseK_const σ2 h, packK_apply σ2 hΦm h, hone,
        Measure.map_map (hΦh h)
          (show Measurable (fun w : EuclideanSpace ℝ (Fin d) =>
              (Fin.cons w (fun a : Fin 0 => (isEmptyElim a : EuclideanSpace ℝ (Fin d)))
                : Fin 1 → EuclideanSpace ℝ (Fin d))) from
            (measurable_fin_cons 0).comp (measurable_id.prodMk measurable_const))]
      refine congrArg (fun f => Measure.map f
        (gaussE (0 : EuclideanSpace ℝ (Fin d)) σ2)) (funext fun w => ?_)
      show Φ h (Fin.cons w isEmptyElim) = esem e (M.set h (.vec d) (gsK 0).name w)
      rw [he (M.set h (.vec d) (gsK 0).name w), hΦb 0]
      refine congrArg (Φ h) (funext fun l => ?_)
      rw [show l = 0 from Fin.ext (Nat.lt_one_iff.mp l.isLt), Fin.cons_zero, M.get_set_eq]
    refine (CEquiv.pushGen (gsK 0) xv (hxg 0) (noiseKernelE (M := M) (d := d) σ2) e
      (packK σ2 Φ) hκ').trans ?_
    exact (CEquiv.congrHead (CEquiv.idleReset (gsK 0) (fun s hs => hs 0))).trans
      CEquiv.skipSeq
  | K + 1, gsK, hgg, hxg, e, Φ, hΦm, he, hΦb => by
    have : IsProbabilityMeasure (gaussE (0 : EuclideanSpace ℝ (Fin d)) σ2) := by
      unfold gaussE; exact Measure.isProbabilityMeasure_map (by fun_prop)
    have h0l : ∀ l : Fin (K + 1), (gsK 0).name ≠ (gsK l.succ).name :=
      fun l => hgg 0 l.succ (Fin.succ_ne_zero l).symm
    have hΦ'm : Measurable (Function.uncurry (fun h' ws =>
        Φ h' (Fin.cons (M.get h' (.vec d) (gsK 0).name) ws)
          : M.heap → (Fin (K + 1) → EuclideanSpace ℝ (Fin d)) → A.interp)) :=
      hΦm.comp (measurable_fst.prodMk ((measurable_fin_cons (K + 1)).comp
        (((M.get_measurable (.vec d) (gsK 0).name).comp measurable_fst).prodMk measurable_snd)))
    -- the tail's pack, one scratch shorter (the induction)
    have hIH : CEquiv (fun s : St M => ∀ l : Fin (K + 1),
        M.get s.1 (.vec d) (Fin.tail gsK l).name = default)
        (nestDraws (t := Ty.vec d) (noiseKernelE (M := M) (d := d) σ2) (K + 1) (Fin.tail gsK)
          (Cmd.assign xv e))
        (Cmd.random xv (packK σ2 (fun h' ws =>
          Φ h' (Fin.cons (M.get h' (.vec d) (gsK 0).name) ws)))) :=
      cequiv_nestPack xv K (Fin.tail gsK)
        (fun l l' hll => hgg l.succ l'.succ
          (fun hcon => hll (Fin.succ_injective _ hcon)))
        (fun l => hxg l.succ) e _ hΦ'm
        (fun h => by
          rw [he h]
          exact congrArg (Φ h)
            (Fin.cons_self_tail (fun l => M.get h (.vec d) (gsK l).name)).symm)
        (fun l h w ws => by
          show Φ (M.set h (.vec d) (Fin.tail gsK l).name w)
              (Fin.cons (M.get (M.set h (.vec d) (Fin.tail gsK l).name w)
                (.vec d) (gsK 0).name) ws)
              = Φ h (Fin.cons (M.get h (.vec d) (gsK 0).name) ws)
          rw [M.get_set_ne (.vec d) (.vec d) h (Fin.tail gsK l).name (gsK 0).name w
            (Or.inr (hgg l.succ 0 (Fin.succ_ne_zero l)))]
          exact hΦb l.succ h w _)
    -- inside the head's block: the tail packs, at the tail's defaults
    have hmid : CEquiv (fun s : St M => ∀ l : Fin (K + 2),
        M.get s.1 (.vec d) (gsK l).name = default)
        (Cmd.loc (gsK 0) (Cmd.seq (Cmd.random (gsK 0) (noiseKernelE (M := M) (d := d) σ2))
          (nestDraws (t := Ty.vec d) (noiseKernelE (M := M) (d := d) σ2) (K + 1) (Fin.tail gsK)
            (Cmd.assign xv e))))
        (Cmd.loc (gsK 0) (Cmd.seq (Cmd.random (gsK 0) (noiseKernelE (M := M) (d := d) σ2))
          (Cmd.random xv (packK σ2 (fun h' ws =>
            Φ h' (Fin.cons (M.get h' (.vec d) (gsK 0).name) ws)))))) := by
      refine CEquiv.congrLoc (gsK 0)
        (R' := fun s : St M => ∀ l : Fin (K + 1),
          M.get s.1 (.vec d) (Fin.tail gsK l).name = default)
        (fun s hs l => ?_) ?_
      · show M.get (M.set s.1 (.vec d) (gsK 0).name default) (.vec d)
            (Fin.tail gsK l).name = default
        rw [M.get_set_ne (.vec d) (.vec d) s.1 (gsK 0).name (Fin.tail gsK l).name default
          (Or.inr (h0l l))]
        exact hs l.succ
      · refine CEquiv.seqVals
          (List.ofFn fun l : Fin (K + 1) => ⟨.vec d, Fin.tail gsK l⟩) ?_ ?_ hIH
        · intro s s' hzz hs l
          exact (hzz ⟨.vec d, Fin.tail gsK l⟩
            (List.mem_ofFn.mpr ⟨l, rfl⟩)).symm.trans (hs l)
        · intro z hz
          obtain ⟨l, rfl⟩ := List.mem_ofFn.mp hz
          exact show (gsK 0).name ≠ (Fin.tail gsK l).name from h0l l
    refine hmid.trans ?_
    -- the head's block fuses into the pack, its reset dying at the head's default
    refine (CEquiv.fuseGen (gsK 0) xv (hxg 0) (noiseKernelE (M := M) (d := d) σ2)
      (packK σ2 (fun h' ws =>
        Φ h' (Fin.cons (M.get h' (.vec d) (gsK 0).name) ws)))).trans ?_
    refine (CEquiv.congrHead (CEquiv.idleReset (gsK 0) (fun s hs => hs 0))).trans ?_
    refine CEquiv.skipSeq.trans ?_
    exact CEquiv.leafDraw xv _ _
      (fun s _ => (packK_fuse (gsK 0) hΦm (hΦb 0) s.1).symm)

end NestPack

/-! ## Dead draws

A window truncated by the end of the run has fewer rounds than `w` has noise blocks: the
scratches of the rounds never run are drawn and never read.  Their blocks are inserted by
[E-Defer-C] at a false guard, so that the packing of all `m + 1` scratches is unchanged. -/

section DeadDraw

/-- **A dead draw**: a mass-one draw of a block-local variable the body never mentions is
    the body — [E-Defer-C] at the guard `false`, collapsed on both sides by [E-If-F]. -/
theorem cequiv_deadDraw {t : Ty} (y : Vars ident t)
    (κ : @ProbabilityTheory.Kernel M.heap t.interp M.heapMeas (Ty.measurableSpace t))
    [IsMarkovKernel κ] {c : Cmd ident M} (hind : IndepY y c) :
    CEquiv (fun s : St M => resetV y s = s) c (Cmd.loc y (Cmd.seq (Cmd.random y κ) c)) :=
  (CEquiv.ifFalse (Expr.cst (t := .bool) false)
      (Cmd.loc y (Cmd.seq (Cmd.random y κ) c)) c (fun _ _ => rfl)).symm.trans
    ((CEquiv.deferCond y κ hind (fun _ _ => rfl)).trans
      (CEquiv.congrLocT y (CEquiv.congrTail
        (CEquiv.ifFalse (Expr.cst (t := .bool) false) c c (fun _ _ => rfl)))))

/-- **A nest grows by dead draws**: a nest of `L` scratch blocks around a body that
    mentions none of the further scratches is the nest of all `K ≥ L` of them, at the
    scratches' defaults — the dead blocks sit innermost, one `cequiv_deadDraw` each. -/
theorem cequiv_nestDraws_trunc {t : Ty}
    (κ : @ProbabilityTheory.Kernel M.heap t.interp M.heapMeas (Ty.measurableSpace t))
    [IsMarkovKernel κ] {body : Cmd ident M} :
    ∀ (K L : ℕ) (hL : L ≤ K) (gs : Fin K → Vars ident t) (gs' : Fin L → Vars ident t),
      (∀ l : Fin L, gs' l = gs ⟨l, lt_of_lt_of_le l.isLt hL⟩) →
      (∀ l l' : Fin K, l ≠ l' → (gs l).name ≠ (gs l').name) →
      (∀ l : Fin K, L ≤ (l : ℕ) → IndepY (gs l) body) →
      CEquiv (fun s : St M => ∀ l, M.get s.1 t (gs l).name = default)
        (nestDraws κ K gs body) (nestDraws κ L gs' body)
  | 0, L, hL, _, _, _, _, _ => by
    obtain rfl : L = 0 := Nat.le_zero.mp hL
    exact CEquiv.refl _
  | K + 1, 0, _, gs, gs', _, hgg, hind => by
    have hIH := cequiv_nestDraws_trunc κ K 0 (Nat.zero_le K) (Fin.tail gs) gs'
      (fun l => l.elim0)
      (fun l l' hll => hgg l.succ l'.succ (fun h => hll (Fin.succ_injective _ h)))
      (fun l _ => hind l.succ (Nat.zero_le _))
    show CEquiv _ (Cmd.loc (gs 0) (Cmd.seq (Cmd.random (gs 0) κ)
      (nestDraws κ K (Fin.tail gs) body))) body
    refine CEquiv.trans ?_ (CEquiv.weaken (fun s hs => ?_)
      (cequiv_deadDraw (gs 0) κ (hind 0 (Nat.zero_le _))).symm)
    · refine CEquiv.congrLoc (gs 0)
        (R' := fun s : St M => ∀ l : Fin K, M.get s.1 t (Fin.tail gs l).name = default)
        (fun s hs l => ?_) ?_
      · show M.get (M.set s.1 t (gs 0).name default) t (Fin.tail gs l).name = default
        rw [M.get_set_ne t t s.1 (gs 0).name (Fin.tail gs l).name default
          (Or.inr (hgg 0 l.succ (Fin.succ_ne_zero l).symm))]
        exact hs l.succ
      · refine CEquiv.seqVals (List.ofFn fun l : Fin K => ⟨t, Fin.tail gs l⟩)
          (fun s s' hzz hs l =>
            (hzz ⟨t, Fin.tail gs l⟩ (List.mem_ofFn.mpr ⟨l, rfl⟩)).symm.trans (hs l))
          (fun z hz => ?_) hIH
        obtain ⟨l, rfl⟩ := List.mem_ofFn.mp hz
        exact show (gs 0).name ≠ (Fin.tail gs l).name from hgg 0 l.succ (Fin.succ_ne_zero l).symm
    · exact Prod.ext
        (show M.set s.1 t (gs 0).name default = s.1 by rw [← hs 0]; exact M.set_get_eq _ _ _) rfl
  | K + 1, L + 1, hL, gs, gs', hgs, hgg, hind => by
    have h0 : gs' 0 = gs 0 := (hgs 0).trans (congrArg gs (Fin.ext (by simp)))
    have hIH := cequiv_nestDraws_trunc κ K L (Nat.le_of_succ_le_succ hL) (Fin.tail gs)
      (Fin.tail gs')
      (fun l => by
        show gs' l.succ = gs (Fin.succ ⟨(l : ℕ), _⟩)
        rw [hgs l.succ]
        exact congrArg gs (Fin.ext (by simp)))
      (fun l l' hll => hgg l.succ l'.succ (fun h => hll (Fin.succ_injective _ h)))
      (fun l hl => hind l.succ (by rw [Fin.val_succ]; omega))
    show CEquiv _ (Cmd.loc (gs 0) (Cmd.seq (Cmd.random (gs 0) κ)
        (nestDraws κ K (Fin.tail gs) body)))
      (Cmd.loc (gs' 0) (Cmd.seq (Cmd.random (gs' 0) κ) (nestDraws κ L (Fin.tail gs') body)))
    rw [h0]
    refine CEquiv.congrLoc (gs 0)
      (R' := fun s : St M => ∀ l : Fin K, M.get s.1 t (Fin.tail gs l).name = default)
      (fun s hs l => ?_) ?_
    · show M.get (M.set s.1 t (gs 0).name default) t (Fin.tail gs l).name = default
      rw [M.get_set_ne t t s.1 (gs 0).name (Fin.tail gs l).name default
        (Or.inr (hgg 0 l.succ (Fin.succ_ne_zero l).symm))]
      exact hs l.succ
    · refine CEquiv.seqVals (List.ofFn fun l : Fin K => ⟨t, Fin.tail gs l⟩)
        (fun s s' hzz hs l =>
          (hzz ⟨t, Fin.tail gs l⟩ (List.mem_ofFn.mpr ⟨l, rfl⟩)).symm.trans (hs l))
        (fun z hz => ?_) hIH
      obtain ⟨l, rfl⟩ := List.mem_ofFn.mp hz
      exact show (gs 0).name ≠ (Fin.tail gs l).name from hgg 0 l.succ (Fin.succ_ne_zero l).symm

end DeadDraw

/-! ## The whole derivation

Name every draw of the window's `L + 1` rounds (`cequiv_windowT_name`), grow the nest to
all `m + 1` scratches by dead draws (`cequiv_nestDraws_trunc`), insert the packed
variable's block and rewrite the leaves to read the pack (`cequiv_windowE_pack`), commute
the block out, collapse the nest and the pack store into the single pack draw
(`cequiv_nestPack`), fuse the coin (`bernFuse_packK`), and discharge the scratches
(`CEquiv.ghosts`). -/

section WindowRules

variable {m : ℕ} (bb : Vars ident .bool) (gs : Fin (m + 1) → Vars ident (.vec d))
  {wv : Vars ident (.prod .bool (.vec ((m + 1) * d)))}

/-- The packing expression: read the scratches, pair the coin with the concatenated
    noises. -/
noncomputable def packWE : Expr M (.prod .bool (.vec ((m + 1) * d))) :=
  ⟨fun h => ((M.get h .bool bb.name, concatE fun l => M.get h (.vec d) (gs l).name) :
      Ty.interp (.prod .bool (.vec ((m + 1) * d)))),
    (M.get_measurable .bool bb.name).prodMk (measurable_concatE.comp
      (measurable_pi_lambda _ fun l => M.get_measurable (.vec d) (gs l).name))⟩

lemma esem_packWE (h : M.heap) :
    esem (packWE (M := M) bb gs) h
      = ((M.get h .bool bb.name,
          concatE fun l => M.get h (.vec d) (gs l).name) :
          Ty.interp (.prod .bool (.vec ((m + 1) * d)))) := rfl

/-- **The coin's fuse with the pack is the window's joint law** — the second measure
    identity of the packing, entering `leafDraw` as a kernel parameter. -/
lemma bernFuse_packK (σ2 : ℝ≥0) (h : M.heap) :
    fuseK bb (bernoulliKernel q)
      (packK (A := .prod .bool (.vec ((m + 1) * d))) σ2
        (fun h' ws => (M.get h' .bool bb.name, concatE ws))) h
      = Kernel.const M.heap (lawWT (d := d) (m := m) q σ2) h := by
  have : IsProbabilityMeasure (gaussE (0 : EuclideanSpace ℝ (Fin d)) σ2) := by
    unfold gaussE; exact Measure.isProbabilityMeasure_map (by fun_prop)
  have hΦm : Measurable (Function.uncurry (fun h' ws =>
      (M.get h' .bool bb.name, concatE ws)
      : M.heap → (Fin (m + 1) → EuclideanSpace ℝ (Fin d)) →
        Ty.interp (.prod .bool (.vec ((m + 1) * d))))) :=
    ((M.get_measurable .bool bb.name).comp measurable_fst).prodMk
      (measurable_concatE.comp measurable_snd)
  rw [fuseK_apply, Kernel.const_apply, lawWT_eq_map σ2,
    show bernoulliKernel (M := M) q h = bernoulliMeasure q from rfl]
  have hbind : ∀ b : Bool,
      packK (M := M) (A := .prod .bool (.vec ((m + 1) * d))) σ2
          (fun h' ws => (M.get h' .bool bb.name, concatE ws))
          (M.set h .bool bb.name b)
        = (Measure.pi fun _ : Fin (m + 1) =>
            gaussE (0 : EuclideanSpace ℝ (Fin d)) σ2).map
            (fun ws => ((b, concatE ws) :
              Ty.interp (.prod .bool (.vec ((m + 1) * d))))) := by
    intro b
    rw [packK_apply σ2 hΦm _]
    congr 1
    funext ws
    show ((M.get (M.set h .bool bb.name b) .bool bb.name, concatE ws) :
        Ty.interp (.prod .bool (.vec ((m + 1) * d))))
      = ((b, concatE ws) : Ty.interp (.prod .bool (.vec ((m + 1) * d))))
    rw [M.get_set_eq]
  rw [Measure.bind_congr_right (Filter.Eventually.of_forall hbind)]
  exact (prod_map_eq_bind_map (bernoulliMeasure q)
    (Measure.pi fun _ : Fin (m + 1) => gaussE (0 : EuclideanSpace ℝ (Fin d)) σ2)
    (measurable_fst.prodMk (measurable_concatE.comp measurable_snd))).symm

omit [NeZero T] in
/-- `WNamesT` at a dummy variable carrying an arbitrary fresh name — lets the
    `noWriteT_*` family serve the scratches. -/
lemma wnamesF {f : ident} (hf : FNamesT (ident := ident) v tv uv f) :
    WNamesT v tv uv
      (⟨f⟩ : Vars ident (.prod .bool (.vec ((m + 1) * d)))) :=
  ⟨hf.x, hf.z, hf.i, hf.D, hf.H, hf.Y, hf.t, hf.u, hf.acc⟩

variable
  (hbg : ∀ l, bb.name ≠ (gs l).name)
  (hgg : ∀ l l' : Fin (m + 1), l ≠ l' → (gs l).name ≠ (gs l').name)
  (hnb : FNamesT (ident := ident) v tv uv bb.name)
  (hng : ∀ l, FNamesT (ident := ident) v tv uv (gs l).name)
  (hwb : wv.name ≠ bb.name) (hwg : ∀ l, wv.name ≠ (gs l).name)

include hbg hgg hnb hng hwb hwg

/-- **The window reading its scratches is the packed-variable block**: open the block,
    store the pack, and rewrite every leaf to read the pack instead of the scratches —
    at `w = default`, which the enclosing structure supplies.  The window has `L + 1`
    rounds, reading the first `L + 1` scratches; the pack stores all `m + 1`. -/
lemma cequiv_windowE_pack (hok : TOK p v) (hw : WOKT v tv uv wv) (j L : ℕ) (hL : L ≤ m) :
    CEquiv (fun s : St M =>
        M.get s.1 (.prod .bool (.vec ((m + 1) * d))) wv.name = default)
      (windowE (M := M) p v tv q elig uv hok j L (Expr.var bb)
        (fun l => Expr.var (gs (Fin.castLE (Nat.succ_le_succ hL) l))))
      (Cmd.loc wv (Cmd.seq (Cmd.assign wv (packWE bb gs))
        (windowW p v tv q elig uv hok wv j L hL))) := by
  have hn := wnamesT hw
  have fnW : FNamesT (ident := ident) v tv uv wv.name :=
    ⟨hn.x, hn.z, hn.i, hn.D, hn.H, hn.Y, hn.t, hn.u, hn.acc⟩
  have hiEw : IndepY wv (windowE (M := M) p v tv q elig uv hok j L (Expr.var bb)
      (fun l => Expr.var (gs (Fin.castLE (Nat.succ_le_succ hL) l)))) :=
    ⟨indepF_roundITE wv fnW j (ExprIndep.var wv bb hwb.symm)
        (ExprIndep.var wv (gs _) (hwg _).symm),
      indepF_iterTE wv fnW L
        (Fin.tail fun l => Expr.var (gs (Fin.castLE (Nat.succ_le_succ hL) l)))
        (fun l => ExprIndep.var wv (gs _) (hwg _).symm)⟩
  -- the packed window with the pack stored is the scratch-read window
  have hstored : CEquiv (fun _ : St M => True)
      (Cmd.seq (Cmd.assign wv (packWE bb gs)) (windowW p v tv q elig uv hok wv j L hL))
      (Cmd.seq (Cmd.assign wv (packWE bb gs))
        (windowE (M := M) p v tv q elig uv hok j L (Expr.var bb)
          (fun l => Expr.var (gs (Fin.castLE (Nat.succ_le_succ hL) l))))) := by
    refine CEquiv.congrSeqDet wv (packWE bb gs)
      (R' := fun s : St M =>
        tWT wv s.1 = (M.get s.1 .bool bb.name,
          concatE fun l => M.get s.1 (.vec d) (gs l).name))
      (fun s _ => ?_) ?_
    · -- after the store, `w` holds the pack of the scratches
      show M.get (M.set s.1 (.prod .bool (.vec ((m + 1) * d))) wv.name
          (esem (packWE bb gs) s.1)) (.prod .bool (.vec ((m + 1) * d))) wv.name = _
      rw [M.get_set_eq, esem_packWE]
      refine Prod.ext ?_ ?_
      · exact (M.get_set_ne (.prod .bool (.vec ((m + 1) * d))) .bool s.1
          wv.name bb.name _ (Or.inr hwb)).symm
      · exact congrArg concatE (funext fun l =>
          (M.get_set_ne (.prod .bool (.vec ((m + 1) * d))) (.vec d) s.1
            wv.name (gs l).name _ (Or.inr (hwg l))).symm)
    · -- the leaf rewrite at "`w` holds the pack"
      refine cequivW_windowE
        (⟨.prod .bool (.vec ((m + 1) * d)), wv⟩ :: ⟨.bool, bb⟩ ::
          List.ofFn fun l => (⟨.vec d, gs l⟩ : (t : Ty) × Vars ident t))
        (fun s s' hv hs => ?_)
        hok j L (eb := coinWT (M := M) wv) (eb' := Expr.var bb)
        (ez := fun l => noiseWT (M := M) wv (Fin.castLE (Nat.succ_le_succ hL) l))
        (ez' := fun l => Expr.var (gs (Fin.castLE (Nat.succ_le_succ hL) l)))
        (fun z hz => ?_) (fun z hz => ?_)
        (fun s hs => ?_) (fun l s hs => ?_)
      · -- the restriction is determined by the values of `w`, the coin and the noises
        have hvw : M.get s.1 (.prod .bool (.vec ((m + 1) * d))) wv.name
            = M.get s'.1 (.prod .bool (.vec ((m + 1) * d))) wv.name :=
          hv ⟨.prod .bool (.vec ((m + 1) * d)), wv⟩ List.mem_cons_self
        have hvb : M.get s.1 .bool bb.name = M.get s'.1 .bool bb.name :=
          hv ⟨.bool, bb⟩ (List.mem_cons_of_mem _ List.mem_cons_self)
        have hvg : ∀ l, M.get s.1 (.vec d) (gs l).name
            = M.get s'.1 (.vec d) (gs l).name := fun l =>
          hv ⟨.vec d, gs l⟩ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
            (List.mem_ofFn.mpr ⟨l, rfl⟩)))
        have hs' : M.get s.1 (.prod .bool (.vec ((m + 1) * d))) wv.name
            = (M.get s.1 .bool bb.name,
              concatE fun l => M.get s.1 (.vec d) (gs l).name) := hs
        show M.get s'.1 (.prod .bool (.vec ((m + 1) * d))) wv.name = _
        rw [← hvw, hs']
        exact Prod.ext hvb (congrArg concatE (funext hvg))
      · -- the scratch-read window writes none of the restriction's variables
        rcases List.mem_cons.mp hz with rfl | hz
        · exact noWriteT_windowE hn j L _ _
        rcases List.mem_cons.mp hz with rfl | hz
        · exact noWriteT_windowE (wnamesF (m := m) hnb) j L _ _
        · obtain ⟨l, rfl⟩ := List.mem_ofFn.mp hz
          exact noWriteT_windowE (wnamesF (m := m) (hng l)) j L _ _
      · -- none of them is `u`
        rcases List.mem_cons.mp hz with rfl | hz
        · exact hn.u
        rcases List.mem_cons.mp hz with rfl | hz
        · exact hnb.u
        · obtain ⟨l, rfl⟩ := List.mem_ofFn.mp hz
          exact (hng l).u
      · -- the coin leaf
        show M.get s.1 .bool bb.name = (tWT wv s.1).1
        rw [hs]
      · -- the noise leaves
        show M.get s.1 (.vec d) (gs (Fin.castLE (Nat.succ_le_succ hL) l)).name
          = blk (tWT wv s.1).2 (Fin.castLE (Nat.succ_le_succ hL) l)
        rw [hs]
        exact (blk_concatE (fun l => M.get s.1 (.vec d) (gs l).name) _).symm
  refine CEquiv.symm ?_
  refine (CEquiv.congrLocT wv hstored).trans ?_
  refine (CEquiv.locStoreHead wv hiEw (fun hp => ?_)).trans
    (CEquiv.locVacuous wv (fun _ hs => hs)
      (fun s s' hv hs => hv ▸ hs) hiEw)
  -- the pack reads only the scratches, so the block's entry reset does not disturb it
  rw [esem_packWE, esem_packWE]
  refine Prod.ext ?_ ?_
  · exact M.get_set_ne (.prod .bool (.vec ((m + 1) * d))) .bool hp
      wv.name bb.name default (Or.inr hwb)
  · exact congrArg concatE (funext fun l =>
      M.get_set_ne (.prod .bool (.vec ((m + 1) * d))) (.vec d) hp
        wv.name (gs l).name default (Or.inr (hwg l)))

/-- **The window identity**: on states where `w` holds its default, a window of
    `L + 1 ≤ m + 1` rounds of `dpftrlBandedGen` is its presampled form `windowS`, as a
    `CEquiv` derivation.  The scratches (one Boolean, `m + 1` vectors, fresh for the
    program, for `w` and for each other) are discharged by [E-Ghost]. -/
theorem cequiv_windowT_windowS_rules (hok : TOK p v) (hu : UOK v tv tv uv)
    (hw : WOKT v tv uv wv) {j : ℕ} (hj : j < n) (L : ℕ) (hL : L ≤ m) :
    CEquiv (fun s : St M => resetV wv s = s)
      (iterCmd (roundT (M := M) p v tv q elig uv hok) (L + 1))
      (windowS p v tv q elig uv hok wv j L hL) := by
  have hL1 : L + 1 ≤ m + 1 := Nat.succ_le_succ hL
  have hΦm : Measurable (Function.uncurry (fun h' ws =>
      (M.get h' .bool bb.name, concatE ws)
      : M.heap → (Fin (m + 1) → EuclideanSpace ℝ (Fin d)) →
        Ty.interp (.prod .bool (.vec ((m + 1) * d))))) :=
    ((M.get_measurable .bool bb.name).comp measurable_fst).prodMk
      (measurable_concatE.comp measurable_snd)
  haveI hSMbern : IsSubMarkovKernel (bernoulliKernel (M := M) q) := inferInstance
  haveI hSMpk : IsSubMarkovKernel
      (packK (M := M) (A := .prod .bool (.vec ((m + 1) * d))) p.σ2
        (fun h' ws => (M.get h' .bool bb.name, concatE ws))) :=
    isSubMarkov_packK (M := M) (A := .prod .bool (.vec ((m + 1) * d))) p.σ2 _
  haveI hSMfuse : IsSubMarkovKernel (fuseK bb (bernoulliKernel (M := M) q)
      (packK (A := .prod .bool (.vec ((m + 1) * d))) p.σ2
        (fun h' ws => (M.get h' .bool bb.name, concatE ws)))) :=
    fuseK_isSubMarkov bb _ _
  -- the scratches are ghosts of both programs
  have hiWb : IndepY bb (windowW (M := M) p v tv q elig uv hok wv j L hL) :=
    ⟨indepF_roundITE bb hnb j (exprIndep_coinWT bb hwb.symm) (exprIndep_noiseWT bb hwb.symm _),
      indepF_iterTE bb hnb L (Fin.tail fun l => noiseWT (M := M) wv (Fin.castLE hL1 l))
        (fun l => exprIndep_noiseWT bb hwb.symm _)⟩
  have hiWg : ∀ l : Fin (m + 1),
      IndepY (gs l) (windowW (M := M) p v tv q elig uv hok wv j L hL) := fun l =>
    ⟨indepF_roundITE (gs l) (hng l) j (exprIndep_coinWT (gs l) (hwg l).symm)
        (exprIndep_noiseWT (gs l) (hwg l).symm _),
      indepF_iterTE (gs l) (hng l) L (Fin.tail fun l => noiseWT (M := M) wv (Fin.castLE hL1 l))
        (fun l' => exprIndep_noiseWT (gs l) (hwg l).symm _)⟩
  -- the pieces of the master restriction
  set Rall : St M → Prop := fun s => (resetV (M := M) wv s = s) ∧
    ∀ z ∈ (⟨.bool, bb⟩ :: List.ofFn fun l => (⟨.vec d, gs l⟩ : (t : Ty) × Vars ident t)),
      M.get s.1 z.1 z.2.name = default with hRallDef
  have hRb : ∀ s : St M, Rall s → M.get s.1 .bool bb.name = default :=
    fun s hs => hs.2 _ List.mem_cons_self
  have hRg : ∀ s : St M, Rall s → ∀ l, M.get s.1 (.vec d) (gs l).name = default :=
    fun s hs l => hs.2 _ (List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨l, rfl⟩))
  have hRw : ∀ s : St M, Rall s →
      M.get s.1 (.prod .bool (.vec ((m + 1) * d))) wv.name = default := by
    intro s hs
    have h1 : M.set s.1 (.prod .bool (.vec ((m + 1) * d))) wv.name default = s.1 :=
      congrArg Prod.fst hs.1
    conv_lhs => rw [← h1]
    exact M.get_set_eq _ s.1 wv.name default
  -- Step 1: every draw of the `L + 1` rounds named, the remaining scratches drawn dead
  have hS1 : CEquiv Rall
      (iterCmd (roundT (M := M) p v tv q elig uv hok) (L + 1))
      (Cmd.loc bb (Cmd.seq (Cmd.random bb (bernoulliKernel q))
        (nestDraws (noiseKernelE p.σ2) (m + 1) gs
          (windowE p v tv q elig uv hok j L (Expr.var bb)
            (fun l => Expr.var (gs (Fin.castLE hL1 l))))))) := by
    -- the window's rounds named into the first `L + 1` scratches
    have hname := cequiv_windowT_name (M := M) (q := q) (elig := elig) bb
      (fun l => gs (Fin.castLE hL1 l))
      (fun l => hbg _) (fun l l' hll => hgg _ _ (fun h => hll (Fin.ext
        (show ((Fin.castLE hL1 l : Fin (m + 1)) : ℕ) = Fin.castLE hL1 l' from congrArg Fin.val h))))
      hnb (fun l => hng _) hok hu hj
    refine (CEquiv.weaken (fun s hs => ⟨hRb s hs, fun l => hRg s hs _⟩) hname).trans ?_
    -- the window never mentions the scratches of the rounds past its end
    have hindX : ∀ l : Fin (m + 1), L + 1 ≤ (l : ℕ) → IndepY (gs l)
        (windowE (M := M) p v tv q elig uv hok j L (Expr.var bb)
          (fun l' => Expr.var (gs (Fin.castLE hL1 l')))) := fun l hl =>
      ⟨indepF_roundITE (gs l) (hng l) j (ExprIndep.var (gs l) bb (hbg l))
          (ExprIndep.var (gs l) (gs (Fin.castLE hL1 0)) (hgg _ _ (fun h => by
            have := congrArg Fin.val h; simp at this; omega))),
        indepF_iterTE (gs l) (hng l) L (Fin.tail fun l' => Expr.var (gs (Fin.castLE hL1 l')))
          (fun l' => ExprIndep.var (gs l) (gs (Fin.castLE hL1 l'.succ)) (hgg _ _ (fun h => by
            have h1 : ((Fin.castLE hL1 l'.succ : Fin (m + 1)) : ℕ) = (l' : ℕ) + 1 := rfl
            have h2 := congrArg Fin.val h
            have := l'.isLt
            omega)))⟩
    refine CEquiv.congrLoc bb
      (R' := fun s : St M => ∀ l, M.get s.1 (.vec d) (gs l).name = default)
      (fun s hs l => ?_) ?_
    · show M.get (M.set s.1 .bool bb.name default) (.vec d) (gs l).name = default
      rw [M.get_set_ne .bool (.vec d) s.1 bb.name (gs l).name default (Or.inr (hbg l))]
      exact hRg s hs l
    · refine CEquiv.seqVals (List.ofFn fun l => (⟨.vec d, gs l⟩ : (t : Ty) × Vars ident t))
        (fun s s' hv hs l =>
          (hv ⟨.vec d, gs l⟩ (List.mem_ofFn.mpr ⟨l, rfl⟩)).symm.trans (hs l))
        (fun z hz => by
          obtain ⟨l, rfl⟩ := List.mem_ofFn.mp hz
          exact show bb.name ≠ (gs l).name from hbg l) ?_
      exact (cequiv_nestDraws_trunc (noiseKernelE p.σ2) (m + 1) (L + 1) hL1 gs
        (fun l => gs (Fin.castLE hL1 l)) (fun _ => rfl) hgg hindX).symm
  -- Step 2: the leaves read the pack, through the nest
  have hS2 : CEquiv Rall
      (Cmd.loc bb (Cmd.seq (Cmd.random bb (bernoulliKernel q))
        (nestDraws (noiseKernelE p.σ2) (m + 1) gs
          (windowE p v tv q elig uv hok j L (Expr.var bb)
            (fun l => Expr.var (gs (Fin.castLE hL1 l)))))))
      (Cmd.loc bb (Cmd.seq (Cmd.random bb (bernoulliKernel q))
        (nestDraws (noiseKernelE p.σ2) (m + 1) gs
          (Cmd.loc wv (Cmd.seq (Cmd.assign wv (packWE bb gs))
            (windowW p v tv q elig uv hok wv j L hL)))))) := by
    refine CEquiv.congrLoc bb
      (R' := fun s : St M =>
        M.get s.1 (.prod .bool (.vec ((m + 1) * d))) wv.name = default)
      (fun s hs => ?_) ?_
    · show M.get (M.set s.1 .bool bb.name default)
          (.prod .bool (.vec ((m + 1) * d))) wv.name = default
      rw [M.get_set_ne .bool (.prod .bool (.vec ((m + 1) * d))) s.1
        bb.name wv.name default (Or.inr hwb.symm)]
      exact hRw s hs
    · refine CEquiv.seqVal wv (fun s s' hv hs => hv ▸ hs)
        (show bb.name ≠ wv.name from hwb.symm) ?_
      refine CEquiv.congrNestDraws
        [⟨.prod .bool (.vec ((m + 1) * d)), wv⟩]
        (fun s s' hv hs =>
          (hv _ (List.mem_singleton.mpr rfl)).symm.trans hs)
        (cequiv_windowE_pack bb gs hbg hgg hnb hng hwb hwg hok hw j L hL)
        (m + 1) gs (fun l z hz => by
          rw [List.mem_singleton] at hz; subst hz; exact (hwg l).symm)
  -- Step 3: the packed block commutes out of the nest
  have hS3 : CEquiv Rall
      (Cmd.loc bb (Cmd.seq (Cmd.random bb (bernoulliKernel q))
        (nestDraws (noiseKernelE p.σ2) (m + 1) gs
          (Cmd.loc wv (Cmd.seq (Cmd.assign wv (packWE bb gs))
            (windowW p v tv q elig uv hok wv j L hL))))))
      (Cmd.loc bb (Cmd.seq (Cmd.random bb (bernoulliKernel q))
        (Cmd.loc wv (nestDraws (noiseKernelE p.σ2) (m + 1) gs
          (Cmd.seq (Cmd.assign wv (packWE bb gs))
            (windowW p v tv q elig uv hok wv j L hL)))))) :=
    CEquiv.congrLocT bb (CEquiv.congrTail
      (CEquiv.pullLocNest wv (noiseK_blind wv p.σ2) (m + 1) gs
        (fun l => (hwg l).symm)))
  -- Step 4: the window leaves the nest
  have hS4 : CEquiv Rall
      (Cmd.loc bb (Cmd.seq (Cmd.random bb (bernoulliKernel q))
        (Cmd.loc wv (nestDraws (noiseKernelE p.σ2) (m + 1) gs
          (Cmd.seq (Cmd.assign wv (packWE bb gs))
            (windowW p v tv q elig uv hok wv j L hL))))))
      (Cmd.loc bb (Cmd.seq (Cmd.random bb (bernoulliKernel q))
        (Cmd.loc wv (Cmd.seq
          (nestDraws (noiseKernelE p.σ2) (m + 1) gs
            (Cmd.assign wv (packWE bb gs)))
          (windowW p v tv q elig uv hok wv j L hL))))) :=
    CEquiv.congrLocT bb (CEquiv.congrTail (CEquiv.congrLocT wv
      (CEquiv.nestOut (m + 1) gs (fun l => hiWg l)).symm))
  -- Step 5: the nest and the store collapse into the pack draw
  have hS5 : CEquiv Rall
      (Cmd.loc bb (Cmd.seq (Cmd.random bb (bernoulliKernel q))
        (Cmd.loc wv (Cmd.seq
          (nestDraws (noiseKernelE p.σ2) (m + 1) gs
            (Cmd.assign wv (packWE bb gs)))
          (windowW p v tv q elig uv hok wv j L hL)))))
      (Cmd.loc bb (Cmd.seq (Cmd.random bb (bernoulliKernel q))
        (Cmd.loc wv (Cmd.seq
          (Cmd.random wv (packK (A := .prod .bool (.vec ((m + 1) * d))) p.σ2
            (fun h' ws => (M.get h' .bool bb.name, concatE ws))))
          (windowW p v tv q elig uv hok wv j L hL))))) := by
    refine CEquiv.congrLoc bb
      (R' := fun s : St M => ∀ l, M.get s.1 (.vec d) (gs l).name = default)
      (fun s hs l => ?_) ?_
    · show M.get (M.set s.1 .bool bb.name default) (.vec d) (gs l).name = default
      rw [M.get_set_ne .bool (.vec d) s.1 bb.name (gs l).name default
        (Or.inr (hbg l))]
      exact hRg s hs l
    · refine CEquiv.seqVals (List.ofFn fun l => (⟨.vec d, gs l⟩ : (t : Ty) × Vars ident t))
        (fun s s' hv hs l =>
          (hv ⟨.vec d, gs l⟩ (List.mem_ofFn.mpr ⟨l, rfl⟩)).symm.trans (hs l))
        (fun z hz => by
          obtain ⟨l, rfl⟩ := List.mem_ofFn.mp hz
          exact show bb.name ≠ (gs l).name from hbg l) ?_
      refine CEquiv.congrLoc wv
        (R' := fun s : St M => ∀ l, M.get s.1 (.vec d) (gs l).name = default)
        (fun s hs l => ?_) ?_
      · show M.get (M.set s.1 (.prod .bool (.vec ((m + 1) * d))) wv.name default)
            (.vec d) (gs l).name = default
        rw [M.get_set_ne (.prod .bool (.vec ((m + 1) * d))) (.vec d) s.1
          wv.name (gs l).name default (Or.inr (hwg l))]
        exact hs l
      · refine CEquiv.congrHead ?_
        refine cequiv_nestPack wv m gs hgg hwg (packWE bb gs) _ hΦm
          (fun h => esem_packWE bb gs h) ?_
        intro l h w ws
        show ((M.get (M.set h (.vec d) (gs l).name w) .bool bb.name, concatE ws) :
            Ty.interp (.prod .bool (.vec ((m + 1) * d))))
          = ((M.get h .bool bb.name, concatE ws) :
            Ty.interp (.prod .bool (.vec ((m + 1) * d))))
        rw [M.get_set_ne (.vec d) .bool h (gs l).name bb.name w
          (Or.inr (hbg l).symm)]
  -- Step 6: the packed block commutes out of the coin's block
  have hS6 : CEquiv Rall
      (Cmd.loc bb (Cmd.seq (Cmd.random bb (bernoulliKernel q))
        (Cmd.loc wv (Cmd.seq
          (Cmd.random wv (packK (A := .prod .bool (.vec ((m + 1) * d))) p.σ2
            (fun h' ws => (M.get h' .bool bb.name, concatE ws))))
          (windowW p v tv q elig uv hok wv j L hL)))))
      (Cmd.loc wv (Cmd.loc bb (Cmd.seq (Cmd.random bb (bernoulliKernel q))
        (Cmd.seq
          (Cmd.random wv (packK (A := .prod .bool (.vec ((m + 1) * d))) p.σ2
            (fun h' ws => (M.get h' .bool bb.name, concatE ws))))
          (windowW p v tv q elig uv hok wv j L hL))))) := by
    refine (CEquiv.congrLocT bb (CEquiv.locNarrow wv
      (show IndepY wv (Cmd.random (M := M) bb (bernoulliKernel q)) from
        ⟨hwb.symm, fun _ _ => rfl⟩)).symm).trans ?_
    exact CEquiv.locComm bb wv hwb.symm _
  -- Step 7: the coin fuses into the pack, which is the window's law
  have hS7 : CEquiv Rall
      (Cmd.loc wv (Cmd.loc bb (Cmd.seq (Cmd.random bb (bernoulliKernel q))
        (Cmd.seq
          (Cmd.random wv (packK (A := .prod .bool (.vec ((m + 1) * d))) p.σ2
            (fun h' ws => (M.get h' .bool bb.name, concatE ws))))
          (windowW p v tv q elig uv hok wv j L hL)))))
      (windowS p v tv q elig uv hok wv j L hL) := by
    refine CEquiv.congrLoc wv
      (R' := fun s : St M => M.get s.1 .bool bb.name = default)
      (fun s hs => ?_) ?_
    · show M.get (M.set s.1 (.prod .bool (.vec ((m + 1) * d))) wv.name default)
          .bool bb.name = default
      rw [M.get_set_ne (.prod .bool (.vec ((m + 1) * d))) .bool s.1
        wv.name bb.name default (Or.inr hwb)]
      exact hRb s hs
    · refine (CEquiv.congrLocT bb CEquiv.seqAssoc').trans ?_
      refine (CEquiv.locNarrowRight bb hiWb).trans ?_
      refine (CEquiv.congrHead (CEquiv.fuseGen bb wv hwb (bernoulliKernel q)
        (packK (A := .prod .bool (.vec ((m + 1) * d))) p.σ2
          (fun h' ws => (M.get h' .bool bb.name, concatE ws))))).trans ?_
      refine (CEquiv.congrHead ((CEquiv.congrHead
        (CEquiv.idleReset bb (fun _ hs => hs))).trans CEquiv.skipSeq)).trans ?_
      exact CEquiv.congrHead (CEquiv.leafDraw wv _ _
        (fun s _ => (bernFuse_packK bb p.σ2 s.1).symm))
  -- assemble, and discharge the scratches
  refine CEquiv.ghosts
    (⟨.bool, bb⟩ :: List.ofFn fun l => (⟨.vec d, gs l⟩ : (t : Ty) × Vars ident t))
    ?_ (fun z hz => ?_) (fun z hz => ?_) (fun z hz s hs => ?_) ?_
  · -- pairwise-distinct names
    refine List.pairwise_cons.mpr ⟨fun z hz => ?_, ?_⟩
    · obtain ⟨l, rfl⟩ := List.mem_ofFn.mp hz
      exact hbg l
    · refine List.pairwise_ofFn.mpr ?_
      intro l l' hll
      exact hgg l l' (Fin.ne_of_lt hll)
  · -- ghosts of the window
    rcases List.mem_cons.mp hz with rfl | hz
    · exact indepF_iterCmd bb (indepF_roundT bb hnb) (L + 1)
    · obtain ⟨l, rfl⟩ := List.mem_ofFn.mp hz
      exact indepF_iterCmd (gs l) (indepF_roundT (gs l) (hng l)) (L + 1)
  · -- ghosts of the presampled window
    rcases List.mem_cons.mp hz with rfl | hz
    · exact ⟨hwb, ⟨hwb, fun _ _ => rfl⟩, hiWb⟩
    · obtain ⟨l, rfl⟩ := List.mem_ofFn.mp hz
      exact ⟨hwg l, ⟨hwg l, fun _ _ => rfl⟩, hiWg l⟩
  · -- the restriction ignores the ghosts
    rcases List.mem_cons.mp hz with rfl | hz
    · show resetV (M := M) wv (resetV bb s) = resetV bb s
      have h1 : M.set s.1 (.prod .bool (.vec ((m + 1) * d))) wv.name default = s.1 :=
        congrArg Prod.fst hs
      show (M.set (M.set s.1 .bool bb.name default)
          (.prod .bool (.vec ((m + 1) * d))) wv.name default, s.2)
        = (M.set s.1 .bool bb.name default, s.2)
      rw [M.set_set_comm .bool (.prod .bool (.vec ((m + 1) * d))) s.1
        bb.name wv.name (Or.inr hwb.symm) default default, h1]
    · obtain ⟨l, rfl⟩ := List.mem_ofFn.mp hz
      show resetV (M := M) wv (resetV (gs l) s) = resetV (gs l) s
      have h1 : M.set s.1 (.prod .bool (.vec ((m + 1) * d))) wv.name default = s.1 :=
        congrArg Prod.fst hs
      show (M.set (M.set s.1 (.vec d) (gs l).name default)
          (.prod .bool (.vec ((m + 1) * d))) wv.name default, s.2)
        = (M.set s.1 (.vec d) (gs l).name default, s.2)
      rw [M.set_set_comm (.vec d) (.prod .bool (.vec ((m + 1) * d))) s.1
        (gs l).name wv.name (Or.inr (hwg l).symm) default default, h1]
  · -- the chain itself, at the master restriction
    exact hS1.trans (hS2.trans (hS3.trans (hS4.trans (hS5.trans
      (hS6.trans hS7)))))

end WindowRules

/-- **A scratch supply for the window derivation**: one Boolean and `m + 1` vectors,
    with their mutual freshness, freshness for the program's variables and freshness
    for `w`. -/
structure WScratchT (v : TVars ident d T T τ) (tv : Vars ident .nat)
    (uv : Vars ident .bool) {m : ℕ}
    (wv : Vars ident (.prod .bool (.vec ((m + 1) * d)))) where
  bb : Vars ident .bool
  gs : Fin (m + 1) → Vars ident (.vec d)
  hbg : ∀ l, bb.name ≠ (gs l).name
  hgg : ∀ l l' : Fin (m + 1), l ≠ l' → (gs l).name ≠ (gs l').name
  hnb : FNamesT (ident := ident) v tv uv bb.name
  hng : ∀ l, FNamesT (ident := ident) v tv uv (gs l).name
  hwb : wv.name ≠ bb.name
  hwg : ∀ l, wv.name ≠ (gs l).name

/-- `cequiv_windowT_windowS_rules`, on a packaged scratch supply. -/
theorem cequiv_windowT_windowS_scr {m : ℕ}
    {wv : Vars ident (.prod .bool (.vec ((m + 1) * d)))}
    (sc : WScratchT (ident := ident) v tv uv wv)
    (hok : TOK p v) (hu : UOK v tv tv uv) (hw : WOKT v tv uv wv)
    {j : ℕ} (hj : j < n) (L : ℕ) (hL : L ≤ m) :
    CEquiv (fun s : St M => resetV wv s = s)
      (iterCmd (roundT (M := M) p v tv q elig uv hok) (L + 1))
      (windowS p v tv q elig uv hok wv j L hL) :=
  cequiv_windowT_windowS_rules sc.bb sc.gs sc.hbg sc.hgg sc.hnb sc.hng
    sc.hwb sc.hwg hok hu hw hj L hL

end DPFTRL.Band
