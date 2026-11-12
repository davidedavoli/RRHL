import Xhl.Logic.Rrhl.Sampling
import Xhl.Logic.Rrhl.OneSided
import Xhl.Logic.Equiv.LocalList
import Xhl.Logic.Rrhl.Lift
import Xhl.Logic.Equiv.CEquiv

open Continuous

/-!
# The deductive system of RRHL

`TDeriv α P φ c₁ c₂ Q ψ` is derivability in RRHL (§4.3, Figure 3): one constructor per core
rule, plus the one-sided rules of Appendix B (Figure 7), whose validity lemmas are in
`OneSided.lean`.  `TDeriv.sound` is Theorem 4.3.

* Constructors carry no measurability or well-formedness side conditions (expressions are
  measurable and kernels sub-Markov by type), and none carries `1 < α`: `TDeriv.sound`
  takes it once.
* **[Samp-Lift]** (`TDeriv.rndLift`) is the only two-sided sampling constructor; its
  premise is validity of the sampling judgment.  **[Samp]**, **[Samp-Gap]** and
  **[Samp-Dec]** (`TDeriv.rnd`, `TDeriv.rndGap`, `TDeriv.rndFwdK`) are derived from it.
* **[Local]** (`TDeriv.loc`, `TDeriv.locs`) is derived from [Equiv], [Assn] and [Seq];
  **[While-Prod]** (`tderiv_while_prod`) from [While] and [Scale].
-/

open MeasureTheory ProbabilityTheory ENNReal Cmd

variable {ident : Type} {M : MemType ident}

namespace Continuous

/-- **Derivability in RRHL** (Figure 3, and the one-sided rules of Figure 7). -/
inductive TDeriv (α : ℝ) :
    (St M × St M → Prop) → (St M × St M → ℝ≥0∞) → Cmd ident M → Cmd ident M →
    (St M × St M → Prop) → (St M × St M → ℝ≥0∞) → Prop where
  /-- **[Skip]** (`rrhl_skip`). -/
  | skip (Q : St M × St M → Prop) (ψ : St M × St M → ℝ≥0∞) :
      TDeriv α Q ψ Cmd.skip Cmd.skip Q ψ
  /-- **[Assn]** (`rrhl_assign`). -/
  | assign {t₁ t₂ : Ty} (x₁ : Vars ident t₁) (e₁ : Expr M t₁)
      (x₂ : Vars ident t₂) (e₂ : Expr M t₂)
      (Q : St M × St M → Prop) (ψ : St M × St M → ℝ≥0∞) :
      TDeriv α
        (fun s => Q ((M.set s.1.1 t₁ x₁.name (esem e₁ s.1.1), s.1.2),
                     (M.set s.2.1 t₂ x₂.name (esem e₂ s.2.1), s.2.2)))
        (fun s => ψ ((M.set s.1.1 t₁ x₁.name (esem e₁ s.1.1), s.1.2),
                     (M.set s.2.1 t₂ x₂.name (esem e₂ s.2.1), s.2.2)))
        (Cmd.assign x₁ e₁) (Cmd.assign x₂ e₂) Q ψ
  /-- **[Release]** (`rrhl_release`). -/
  | release {t : Ty} (e₁ e₂ : Expr M t)
      (Q : St M × St M → Prop) (ψ : St M × St M → ℝ≥0∞) :
      TDeriv α
        (fun s => Q ((s.1.1, s.1.2.snoc ⟨t, esem e₁ s.1.1⟩),
                     (s.2.1, s.2.2.snoc ⟨t, esem e₂ s.2.1⟩)))
        (fun s => ψ ((s.1.1, s.1.2.snoc ⟨t, esem e₁ s.1.1⟩),
                     (s.2.1, s.2.2.snoc ⟨t, esem e₂ s.2.1⟩)))
        (Cmd.release e₁) (Cmd.release e₂) Q ψ
  /-- **[Conseq]** (`rrhl_conseq`). -/
  | conseq {P P₀ Q Q₀ : St M × St M → Prop} {φ φ₀ ψ ψ₀ : St M × St M → ℝ≥0∞}
      {c₁ c₂ : Cmd ident M}
      (hP : ∀ s, P s → P₀ s) (hφ : ∀ s, P s → φ₀ s ≤ φ s) (hQ : ∀ s, Q₀ s → Q s)
      (hψ : ∀ s, Q₀ s → ψ s ≤ ψ₀ s) (d : TDeriv α P₀ φ₀ c₁ c₂ Q₀ ψ₀) :
      TDeriv α P φ c₁ c₂ Q ψ
  /-- **[Seq]** (`rrhl_seq`): no side conditions. -/
  | seq {P Q R : St M × St M → Prop} {φ ψ χ : St M × St M → ℝ≥0∞}
      {c₁ c₂ c₁' c₂' : Cmd ident M}
      (d : TDeriv α P φ c₁ c₂ Q ψ) (d' : TDeriv α Q ψ c₁' c₂' R χ) :
      TDeriv α P φ (Cmd.seq c₁ c₁') (Cmd.seq c₂ c₂') R χ
  /-- **[If]** (`rrhl_if`, synchronized guards). -/
  | if_ {P Q : St M × St M → Prop} {φ ψ : St M × St M → ℝ≥0∞}
      {e₁ e₂ : BExpr M} {c1t c2t c1e c2e : Cmd ident M}
      (hsync : ∀ s, P s → esem e₁ s.1.1 = esem e₂ s.2.1)
      (dthen : TDeriv α (fun s => P s ∧ esem e₁ s.1.1 = true) φ c1t c2t Q ψ)
      (delse : TDeriv α (fun s => P s ∧ esem e₁ s.1.1 = false) φ c1e c2e Q ψ) :
      TDeriv α P φ (Cmd.cond e₁ c1t c1e) (Cmd.cond e₂ c2t c2e) Q ψ
  /-- **[While]** (`rrhl_while_gen`): an invariant family indexed by the number of completed
      rounds, the exit data read wherever the loops stop.  The round premise is asked only
      at levels where a round can be taken (`∃ s, …`). -/
  | while_ {e₁ e₂ : BExpr M} {c₁ c₂ : Cmd ident M}
      (P : ℕ → St M × St M → Prop) (φ : ℕ → St M × St M → ℝ≥0∞)
      (E : St M × St M → Prop) (ψ : St M × St M → ℝ≥0∞)
      (dstep : ∀ k, (∃ s, P k s ∧ esem e₁ s.1.1 = true ∧ esem e₂ s.2.1 = true) → TDeriv α
        (fun s => P k s ∧ esem e₁ s.1.1 = true ∧ esem e₂ s.2.1 = true) (φ k)
        c₁ c₂ (P (k + 1)) (φ (k + 1)))
      (hsync : ∀ k s, P k s → esem e₁ s.1.1 = esem e₂ s.2.1)
      (hexit : ∀ k s, P k s → esem e₁ s.1.1 = false → E s ∧ ψ s ≤ φ k s) :
      TDeriv α (P 0) (φ 0) (Cmd.while e₁ c₁) (Cmd.while e₂ c₂)
        (fun s => E s ∧ esem e₁ s.1.1 = false ∧ esem e₂ s.2.1 = false) ψ
  /-- **[Assn-L]** (`rrhl_assign_l`): an assignment on the left against `skip`. -/
  | assignL {t : Ty} (x : Vars ident t) (e : Expr M t)
      (Q : St M × St M → Prop) (ψ : St M × St M → ℝ≥0∞) :
      TDeriv α
        (fun s => Q ((M.set s.1.1 t x.name (esem e s.1.1), s.1.2), s.2))
        (fun s => ψ ((M.set s.1.1 t x.name (esem e s.1.1), s.1.2), s.2))
        (Cmd.assign x e) Cmd.skip Q ψ
  /-- **[Release-L]** (`rrhl_release_l`): a release on the left against `skip`. -/
  | releaseL {t : Ty} (e : Expr M t)
      (Q : St M × St M → Prop) (ψ : St M × St M → ℝ≥0∞) :
      TDeriv α
        (fun s => Q ((s.1.1, s.1.2.snoc ⟨t, esem e s.1.1⟩), s.2))
        (fun s => ψ ((s.1.1, s.1.2.snoc ⟨t, esem e s.1.1⟩), s.2))
        (Cmd.release e) Cmd.skip Q ψ
  /-- **[If-L]** (`rrhl_if_l`): a case split on the left guard; the right statement is
      arbitrary. -/
  | ifL {P Q : St M × St M → Prop} {φ ψ : St M × St M → ℝ≥0∞}
      {e₁ : BExpr M} {c1t c1e c₂ : Cmd ident M}
      (dthen : TDeriv α (fun s => P s ∧ esem e₁ s.1.1 = true) φ c1t c₂ Q ψ)
      (delse : TDeriv α (fun s => P s ∧ esem e₁ s.1.1 = false) φ c1e c₂ Q ψ) :
      TDeriv α P φ (Cmd.cond e₁ c1t c1e) c₂ Q ψ
  /-- **[Samp-L]** (`rrhl_rnd_l`): sampling on the left against `skip`, from any sub-Markov
      kernel, at the expected post-budget. -/
  | rndL {t : Ty} (x : Vars ident t)
      (κ : @ProbabilityTheory.Kernel M.heap t.interp M.heapMeas (Ty.measurableSpace t))
      [IsSubMarkovKernel κ]
      (P Q : St M × St M → Prop) (φ ψ : St M × St M → ℝ≥0∞)
      (hQ : ∀ s, P s → ∀ᵐ v ∂(κ s.1.1), Q ((M.set s.1.1 t x.name v, s.1.2), s.2))
      (hφ : ∀ s, P s → ∫⁻ v, ψ ((M.set s.1.1 t x.name v, s.1.2), s.2) ∂(κ s.1.1) ≤ φ s) :
      TDeriv α P φ (Cmd.random x κ) Cmd.skip Q ψ
  /-- **[Samp-R]** (`rrhl_rnd_r`): sampling on the right against `skip`, from a Markov
      kernel, at the expected post-budget. -/
  | rndR {t : Ty} (x : Vars ident t)
      (κ : @ProbabilityTheory.Kernel M.heap t.interp M.heapMeas (Ty.measurableSpace t))
      [IsMarkovKernel κ]
      (P Q : St M × St M → Prop) (φ ψ : St M × St M → ℝ≥0∞)
      (hQ : ∀ s, P s → ∀ᵐ v ∂(κ s.2.1), Q (s.1, (M.set s.2.1 t x.name v, s.2.2)))
      (hφ : ∀ s, P s → ∫⁻ v, ψ (s.1, (M.set s.2.1 t x.name v, s.2.2)) ∂(κ s.2.1) ≤ φ s) :
      TDeriv α P φ Cmd.skip (Cmd.random x κ) Q ψ
  /-- **[While-L]** (`rrhl_while_l`): a loop on the left against `skip`, with an invariant
      family over all of `ℕ` and no termination requirement. -/
  | whileL {e₁ : BExpr M} {c₁ : Cmd ident M}
      (P : ℕ → St M × St M → Prop) (φ : ℕ → St M × St M → ℝ≥0∞)
      (E : St M × St M → Prop) (ψ : St M × St M → ℝ≥0∞)
      (dstep : ∀ k, TDeriv α (fun s => P k s ∧ esem e₁ s.1.1 = true) (φ k)
        c₁ Cmd.skip (P (k + 1)) (φ (k + 1)))
      (hexit : ∀ k s, P k s → esem e₁ s.1.1 = false → E s ∧ ψ s ≤ φ k s) :
      TDeriv α (P 0) (φ 0) (Cmd.while e₁ c₁) Cmd.skip
        (fun s => E s ∧ esem e₁ s.1.1 = false) ψ
  /-- **[While-R]** (`rrhl_while_r`): a loop on the right against `skip`, which must stop
      within `n` rounds (`P n` forces the guard false). -/
  | whileR {e₂ : BExpr M} {c₂ : Cmd ident M} (n : ℕ)
      (P : ℕ → St M × St M → Prop) (φ : ℕ → St M × St M → ℝ≥0∞)
      (E : St M × St M → Prop) (ψ : St M × St M → ℝ≥0∞)
      (dstep : ∀ k, k < n → TDeriv α (fun s => P k s ∧ esem e₂ s.2.1 = true) (φ k)
        Cmd.skip c₂ (P (k + 1)) (φ (k + 1)))
      (hstop : ∀ s, P n s → esem e₂ s.2.1 = false)
      (hexit : ∀ k, k ≤ n → ∀ s, P k s → esem e₂ s.2.1 = false → E s ∧ ψ s ≤ φ k s) :
      TDeriv α (P 0) (φ 0) Cmd.skip (Cmd.while e₂ c₂)
        (fun s => E s ∧ esem e₂ s.2.1 = false) ψ
  /-- **[Samp-Lift]**: any valid judgment between two sampling statements is derivable. -/
  | rndLift {t₁ t₂ : Ty} (x₁ : Vars ident t₁) (x₂ : Vars ident t₂)
      (κ₁ : @ProbabilityTheory.Kernel M.heap t₁.interp M.heapMeas (Ty.measurableSpace t₁))
      [IsSubMarkovKernel κ₁]
      (κ₂ : @ProbabilityTheory.Kernel M.heap t₂.interp M.heapMeas (Ty.measurableSpace t₂))
      [IsSubMarkovKernel κ₂]
      (P Q : St M × St M → Prop) (φ ψ : St M × St M → ℝ≥0∞)
      (h : RRhl α P φ (Cmd.random x₁ κ₁) (Cmd.random x₂ κ₂) Q ψ) :
      TDeriv α P φ (Cmd.random x₁ κ₁) (Cmd.random x₂ κ₂) Q ψ
  /-- **[Scale]** (`rrhl_scale`): both the budget and the weight scale. -/
  | scale {c : ℝ≥0∞} (hc0 : c ≠ 0) (hct : c ≠ ⊤)
      {P Q : St M × St M → Prop} {φ ψ : St M × St M → ℝ≥0∞} {c₁ c₂ : Cmd ident M}
      (d : TDeriv α P φ c₁ c₂ Q ψ) :
      TDeriv α P (fun s => c * φ s) c₁ c₂ Q (fun s => c * ψ s)
  /-- **[Equiv]** (`rrhl_equiv`): programs derivably equivalent (`CEquiv`, Appendix E) on
      restrictions `R₁`, `R₂` that the precondition entails (`hP`) are interchangeable. -/
  | equiv {P Q : St M × St M → Prop} {φ ψ : St M × St M → ℝ≥0∞}
      {c₁ c₂ c₁' c₂' : Cmd ident M} {R₁ R₂ : St M → Prop}

      (h₁ : CEquiv R₁ c₁ c₁') (h₂ : CEquiv R₂ c₂ c₂')
      (hP : ∀ s, P s → R₁ s.1 ∧ R₂ s.2)
      (d : TDeriv α P φ c₁' c₂' Q ψ) :
      TDeriv α P φ c₁ c₂ Q ψ

@[inherit_doc TDeriv]
scoped notation:40 "⊢ₜ{" P ", " φ "} " c₁:max " ∼{" α "} " c₂:max " {" Q ", " ψ "}" =>
  TDeriv α P φ c₁ c₂ Q ψ

example {α : ℝ} (Q : St M × St M → Prop) (ψ : St M × St M → ℝ≥0∞) :
    (⊢ₜ{Q, ψ} Cmd.skip ∼{α} Cmd.skip {Q, ψ}) = TDeriv (M := M) α Q ψ Cmd.skip Cmd.skip Q ψ :=
  rfl

/-- **[While] with a descending budget chain of length `n`**, derived from [While]: a round
    moves `P (k+1)` to `P k`, and `P 0` forces the guard false. -/
theorem TDeriv.whileInv {α : ℝ} {e₁ e₂ : BExpr M} {c₁ c₂ : Cmd ident M}
    (n : ℕ)
    (P : ℕ → St M × St M → Prop) (φ : ℕ → St M × St M → ℝ≥0∞)
    (E : St M × St M → Prop) (ψ : St M × St M → ℝ≥0∞)
    (dstep : ∀ k, k < n → TDeriv α
      (fun s => P (k + 1) s ∧ esem e₁ s.1.1 = true ∧ esem e₂ s.2.1 = true) (φ (k + 1))
      c₁ c₂ (P k) (φ k))
    (hsync : ∀ k s, P k s → esem e₁ s.1.1 = esem e₂ s.2.1)
    (hstop0 : ∀ s, P 0 s → esem e₁ s.1.1 = false)
    (hexit : ∀ k, k ≤ n → ∀ s, P k s → esem e₁ s.1.1 = false → E s ∧ ψ s ≤ φ k s) :
    TDeriv α (P n) (φ n) (Cmd.while e₁ c₁) (Cmd.while e₂ c₂)
      (fun s => E s ∧ esem e₁ s.1.1 = false ∧ esem e₂ s.2.1 = false) ψ := by
  have h := TDeriv.while_ (fun k => P (n - k)) (fun k => φ (n - k)) E ψ
    (fun k hlive => by
      rcases Nat.lt_or_ge k n with hk | hk
      · have e : n - k = n - (k + 1) + 1 := by omega
        simpa only [e] using dstep (n - (k + 1)) (by omega)
      · exfalso
        obtain ⟨s, hs, h1, -⟩ := hlive
        rw [show n - k = 0 by omega] at hs
        rw [hstop0 s hs] at h1
        exact Bool.noConfusion h1)
    (fun k s hs => hsync _ s hs)
    (fun k s hs hf => hexit (n - k) (by omega) s hs hf)
  simpa only [Nat.sub_zero] using h

/-- **Theorem 4.3 (soundness)**: every derivable judgment is valid, for `1 < α`. -/
theorem TDeriv.sound {α : ℝ} (hα : 1 < α) {P Q : St M × St M → Prop}
    {φ ψ : St M × St M → ℝ≥0∞} {c₁ c₂ : Cmd ident M}
    (d : TDeriv α P φ c₁ c₂ Q ψ) :
    RRhl α P φ c₁ c₂ Q ψ := by
  induction d with
  | skip Q ψ => exact rrhl_skip Q ψ
  | assign x₁ e₁ x₂ e₂ Q ψ => exact rrhl_assign x₁ e₁ x₂ e₂ Q ψ
  | release e₁ e₂ Q ψ => exact rrhl_release e₁ e₂ Q ψ
  | conseq hP hφ hQ hψ _ ih => exact rrhl_conseq hP hφ hQ hψ ih
  | seq _ _ ih ih' => exact rrhl_seq ih ih'
  | if_ hsync _ _ iht ihe => exact rrhl_if hsync iht ihe
  | @while_ e₁ e₂ c₁ c₂ P φ E ψ _ hsync hexit ih =>
      refine rrhl_while_gen hα P φ E ψ (fun k => ?_) hsync hexit
      by_cases hlive : ∃ s, P k s ∧ esem e₁ s.1.1 = true ∧ esem e₂ s.2.1 = true
      · exact ih k hlive
      · exact rrhl_bot fun s hs => hlive ⟨s, hs⟩
  | assignL x e Q ψ => exact rrhl_assign_l x e Q ψ
  | releaseL e Q ψ => exact rrhl_release_l e Q ψ
  | ifL _ _ iht ihe => exact rrhl_if_l iht ihe
  | rndL x κ P Q φ ψ hQ hφ => exact rrhl_rnd_l hα x κ P Q φ ψ hQ hφ
  | rndR x κ P Q φ ψ hQ hφ => exact rrhl_rnd_r hα x κ P Q φ ψ hQ hφ
  | whileL P φ E ψ _ hexit ih => exact rrhl_while_l hα P φ E ψ ih hexit
  | whileR n P φ E ψ _ hstop hexit ih =>
      exact rrhl_while_r n P φ E ψ (fun k hk => ih k hk) hstop hexit
  | rndLift x₁ x₂ κ₁ κ₂ P Q φ ψ h => exact h
  | scale hc0 hct _ ih => exact rrhl_scale hα hc0 hct ih
  | equiv h₁ h₂ hP _ ih =>
      exact rrhl_equiv (fun s hs => h₁.sound s.1 (hP s hs).1)
        (fun s hs => h₂.sound s.2 (hP s hs).2) ih

/-! ## [Local], derived

[Equiv] onto the desugaring `x := dₓ ; (c ; x := dₓ)` ([E-Loc-D], `CEquiv.locDesugar`),
then [Assn] and [Seq]. -/

/-- **[Local]**, derived. -/
theorem TDeriv.loc {α : ℝ} {t₁ t₂ : Ty} (x₁ : Vars ident t₁) (x₂ : Vars ident t₂)
    {c₁ c₂ : Cmd ident M} 
    {P Q : St M × St M → Prop} {φ ψ : St M × St M → ℝ≥0∞}
    (d : TDeriv α P φ c₁ c₂ (fun s => Q (resetV x₁ s.1, resetV x₂ s.2))
      (fun s => ψ (resetV x₁ s.1, resetV x₂ s.2))) :
    TDeriv α (fun s => P (resetV x₁ s.1, resetV x₂ s.2))
      (fun s => φ (resetV x₁ s.1, resetV x₂ s.2)) (loc x₁ c₁) (loc x₂ c₂) Q ψ := by
  refine TDeriv.equiv
    (CEquiv.locDesugar (R := fun _ => True) x₁ )
    (CEquiv.locDesugar (R := fun _ => True) x₂ )
    (fun _ _ => ⟨trivial, trivial⟩) ?_
  exact TDeriv.seq
    (TDeriv.assign x₁ (Expr.cst default) x₂ (Expr.cst default) P φ)
    (TDeriv.seq d
      (TDeriv.assign x₁ (Expr.cst default) x₂ (Expr.cst default) Q ψ))

/-- **[Local]** for a block with several variables, derived. -/
theorem TDeriv.locs {α : ℝ} : ∀ (xs : List (AVar ident)) {c₁ c₂ : Cmd ident M},
    ∀ {P Q : St M × St M → Prop} {φ ψ : St M × St M → ℝ≥0∞},
    TDeriv α P φ c₁ c₂ (fun s => Q (postR xs s.1, postR xs s.2))
      (fun s => ψ (postR xs s.1, postR xs s.2)) →
    TDeriv α (fun s => P (preR xs s.1, preR xs s.2)) (fun s => φ (preR xs s.1, preR xs s.2))
      (locs xs c₁) (locs xs c₂) Q ψ
  | [], _, _, _, _, _, _, h => h
  | ⟨_, x⟩ :: xs, _, _, _, Q, _, ψ, h =>
    TDeriv.loc x x
      (TDeriv.locs xs (Q := fun s => Q (resetV x s.1, resetV x s.2))
        (ψ := fun s => ψ (resetV x s.1, resetV x s.2)) h)

/-! ## Derived sampling rules

Each is [Samp-Lift] applied to the matching validity lemma of `Sampling.lean`; the
postcondition is asked almost everywhere. -/

/-- **[Samp]** (`rrhl_rnd`): both sides write the same sampled value, and the pre-budget
    pays the weighted Hellinger integral of the two kernels. -/
theorem TDeriv.rnd {α : ℝ} (hα : 1 < α) {t : Ty} (x₁ x₂ : Vars ident t)
    (κ₁ κ₂ : @ProbabilityTheory.Kernel M.heap t.interp M.heapMeas (Ty.measurableSpace t))
    [IsSubMarkovKernel κ₁] [IsSubMarkovKernel κ₂]
    (P Q : St M × St M → Prop)
    (φ ψ : St M × St M → ℝ≥0∞)
    (hQhold : ∀ s, P s → ∀ᵐ v ∂(κ₂ s.2.1), Q (updPair x₁ x₂ s (v, v)))
    (hdiv : ∀ s, P s →
      weightedHellingerIntegral α (fun v => ψ (updPair x₁ x₂ s (v, v))) (κ₁ s.1.1) (κ₂ s.2.1) ≤ φ s) :
    TDeriv α P φ (Cmd.random x₁ κ₁) (Cmd.random x₂ κ₂) Q ψ :=
  TDeriv.rndLift x₁ x₂ κ₁ κ₂ P Q φ ψ
    (rrhl_rnd hα x₁ x₂ κ₁ κ₂ P Q φ ψ hQhold hdiv)

/-- **[Samp-Gap]** (`rrhl_rnd_gap`): the right value is the left value translated by `−δ`. -/
theorem TDeriv.rndGap {α : ℝ} (hα : 1 < α) {d : ℕ} (x₁ x₂ : Vars ident (.vec d))
    (κ₁ κ₂ : @ProbabilityTheory.Kernel M.heap (EuclideanSpace ℝ (Fin d)) M.heapMeas
      (Ty.measurableSpace (.vec d)))
    [IsSubMarkovKernel κ₁] [IsSubMarkovKernel κ₂]
    (δ : St M × St M → EuclideanSpace ℝ (Fin d))
    (P Q : St M × St M → Prop)
    (φ ψ : St M × St M → ℝ≥0∞)
    (hQhold : ∀ s, P s → ∀ᵐ v ∂((κ₂ s.2.1).map (fun w => w + δ s)),
      Q (updPair x₁ x₂ s (v, v - δ s)))
    (hdiv : ∀ s, P s → weightedHellingerIntegral α (fun v => ψ (updPair x₁ x₂ s (v, v - δ s)))
      (κ₁ s.1.1) ((κ₂ s.2.1).map (fun w => w + δ s)) ≤ φ s) :
    TDeriv α P φ (Cmd.random x₁ κ₁) (Cmd.random x₂ κ₂) Q ψ :=
  TDeriv.rndLift x₁ x₂ κ₁ κ₂ P Q φ ψ
    (rrhl_rnd_gap hα x₁ x₂ κ₁ κ₂ δ P Q φ ψ hQhold hdiv)

/-- **[Samp-Dec]** (`rrhl_rnd_fwdK_ae`, Figure 9): the right sampler decomposes as
    `dlet v ← ν in F v` with `F` Markov; the pre-budget pays the weighted Hellinger
    integral between the left sampler and `ν`. -/
theorem TDeriv.rndFwdK {α : ℝ} (hα : 1 < α) {t₁ t₂ : Ty}
    (x₁ : Vars ident t₁) (x₂ : Vars ident t₂)
    (κ₁ : @ProbabilityTheory.Kernel M.heap t₁.interp M.heapMeas (Ty.measurableSpace t₁))
    [IsSubMarkovKernel κ₁]
    (κ₂ : @ProbabilityTheory.Kernel M.heap t₂.interp M.heapMeas (Ty.measurableSpace t₂))
    [IsSubMarkovKernel κ₂]
    (P Q : St M × St M → Prop) (φ ψ : St M × St M → ℝ≥0∞)
    (hdiv : ∀ s, P s →
      ∃ (F : @ProbabilityTheory.Kernel t₁.interp t₂.interp
          (Ty.measurableSpace t₁) (Ty.measurableSpace t₂)) (ν : Measure t₁.interp),
        IsMarkovKernel F ∧ IsFiniteMeasure ν ∧
        ν.bind (fun v => F v) = κ₂ s.2.1 ∧
        (∀ᵐ v ∂ν, ∀ᵐ w ∂(F v), Q (updPair x₁ x₂ s (v, w))) ∧
        weightedHellingerIntegral α (fun v => ∫⁻ w, ψ (updPair x₁ x₂ s (v, w)) ∂(F v))
          (κ₁ s.1.1) ν ≤ φ s) :
    TDeriv α P φ (Cmd.random x₁ κ₁) (Cmd.random x₂ κ₂) Q ψ :=
  TDeriv.rndLift x₁ x₂ κ₁ κ₂ P Q φ ψ
    (rrhl_rnd_fwdK_ae hα x₁ x₂ κ₁ κ₂ P Q φ ψ hdiv)

/-! ## [While-Prod], derived -/

/-- **[While-Prod]**, derived from [While] and [Scale]: a counted loop with constant
    per-round budgets `η l` has budget `∏ l < N, η l`.  The invariant decides the guard:
    true below `N`, false at `N`. -/
theorem tderiv_while_prod {α : ℝ} {e : BExpr M} {c : Cmd ident M}
    (N : ℕ) (I : ℕ → St M × St M → Prop)
    (η : ℕ → ℝ≥0∞) (hη0 : ∀ l, η l ≠ 0) (hηt : ∀ l, η l ≠ ⊤)
    (hstep : ∀ l, l < N → TDeriv α (I l) (fun _ => η l) c c (I (l + 1)) (fun _ => 1))
    (hIg : ∀ l s, I l s → l < N → esem e s.1.1 = true ∧ esem e s.2.1 = true)
    (hIN : ∀ s, I N s → esem e s.1.1 = false ∧ esem e s.2.1 = false) :
    TDeriv α (I 0) (fun _ => ∏ l ∈ Finset.range N, η l) (Cmd.while e c) (Cmd.while e c)
      (I N) (fun _ => 1) := by
  have key : ∀ k, N - k < N ∨ (N - k = N ∧ (k = 0 ∨ N = 0)) := fun k => by omega
  have hd : ∀ k, k < N → TDeriv α
      (fun s => I (N - (k + 1)) s ∧ esem e s.1.1 = true ∧ esem e s.2.1 = true)
      (fun _ => ∏ j ∈ Finset.Ico (N - (k + 1)) N, η j) c c (I (N - k))
      (fun _ => ∏ j ∈ Finset.Ico (N - k) N, η j) := by
    intro k hk
    have hl : N - (k + 1) < N := by omega
    have hsucc : N - (k + 1) + 1 = N - k := by omega
    have hc0 : (∏ j ∈ Finset.Ico (N - k) N, η j) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun j _ => hη0 j
    have hct : (∏ j ∈ Finset.Ico (N - k) N, η j) ≠ ⊤ := ENNReal.prod_ne_top fun j _ => hηt j
    refine TDeriv.conseq (fun s hs => hs.1) (fun _ _ => ?_)
      (fun s h => by rwa [hsucc] at h) (fun _ _ => ?_)
      (TDeriv.scale hc0 hct (hstep _ hl))
    · show (∏ j ∈ Finset.Ico (N - k) N, η j) * η (N - (k + 1))
        ≤ ∏ j ∈ Finset.Ico (N - (k + 1)) N, η j
      rw [Finset.prod_eq_prod_Ico_succ_bot hl, hsucc, mul_comm]
    · show (∏ j ∈ Finset.Ico (N - k) N, η j) ≤ (∏ j ∈ Finset.Ico (N - k) N, η j) * 1
      rw [mul_one]
  have h := TDeriv.whileInv (e₁ := e) (e₂ := e) N (fun k => I (N - k))
    (fun k _ => ∏ j ∈ Finset.Ico (N - k) N, η j) (I N) (fun _ => 1) hd
    (fun k s hs => by
      rcases key k with hlt | ⟨heq, -⟩
      · rw [(hIg _ s hs hlt).1, (hIg _ s hs hlt).2]
      · rw [heq] at hs; rw [(hIN s hs).1, (hIN s hs).2])
    (fun s hs => (hIN s (by rwa [Nat.sub_zero] at hs)).1)
    (fun k hk s hs hfalse => by
      rcases key k with hlt | ⟨heq, -⟩
      · rw [(hIg _ s hs hlt).1] at hfalse; cases hfalse
      · rw [heq] at hs
        exact ⟨hs, by rw [heq, Finset.Ico_self, Finset.prod_empty]⟩)
  refine TDeriv.conseq (fun s hs => by rwa [Nat.sub_self]) (fun _ _ => ?_)
    (fun s h => h.1) (fun _ _ => le_rfl) h
  show (∏ j ∈ Finset.Ico (N - N) N, η j) ≤ ∏ l ∈ Finset.range N, η l
  rw [Nat.sub_self, Finset.range_eq_Ico]

end Continuous
