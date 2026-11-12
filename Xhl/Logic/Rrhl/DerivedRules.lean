import Xhl.Logic.Rrhl.Deriv

open Continuous

/-!
# Derived rules used by the case studies

`TDeriv` lemmas proved from the constructors:

* `tderiv_assign_same`, `tderiv_assign_sameW` — **[Assn]** with the postcondition (and
  weights) read on the updated memories;
* `tderiv_iterCmd_family` — an invariant family chained along `iterCmd`;
* `tderiv_while_count` — **[While]** for a loop run exactly `N` times;
* `tderiv_of_false` — a judgment with an unsatisfiable precondition, by induction on the
  program.
-/
open MeasureTheory ProbabilityTheory ENNReal

variable {ident : Type} {M : MemType ident}

namespace Continuous

variable {d : ℕ}

/-- **[Assn]** as a derivation, with the postcondition checked on the updated memories. -/
lemma tderiv_assign_same {α : ℝ} {ty : Ty} (x : Vars ident ty) (e : Expr M ty)
    (η : ℝ≥0∞) (P Q : M.heap × M.heap → Prop)
    (h : ∀ m, P m → Q (M.set m.1 ty x.name (esem e m.1), M.set m.2 ty x.name (esem e m.2))) :
    TDeriv (M := M) α (liftP P) (fun _ => η) (Cmd.assign x e) (Cmd.assign x e) (liftP Q)
      (fun _ => η) :=
  TDeriv.conseq (fun _ hs => ⟨h _ hs.1, hs.2⟩) (fun _ _ => le_rfl) (fun _ h => h)
    (fun _ _ => le_rfl) (TDeriv.assign x e x e (liftP Q) (fun _ => η))

/-- **[Assn]** as a derivation with memory weights: the post-weight, read on the updated
    memories, is at most the pre-weight. -/
lemma tderiv_assign_sameW {α : ℝ} {ty : Ty} (x : Vars ident ty) (e : Expr M ty)
    (w w' : M.heap × M.heap → ℝ≥0∞) (P Q : M.heap × M.heap → Prop)
    (h : ∀ m, P m → Q (M.set m.1 ty x.name (esem e m.1), M.set m.2 ty x.name (esem e m.2)))
    (hw : ∀ m, P m →
      w' (M.set m.1 ty x.name (esem e m.1), M.set m.2 ty x.name (esem e m.2)) ≤ w m) :
    TDeriv (M := M) α (liftP P) (liftW w) (Cmd.assign x e) (Cmd.assign x e) (liftP Q)
      (liftW w') :=
  TDeriv.conseq (fun _ hs => ⟨h _ hs.1, hs.2⟩) (fun _ hs => hw _ hs.1) (fun _ h => h)
    (fun _ _ => le_rfl) (TDeriv.assign x e x e (liftP Q) (liftW w'))

/-- Indexed iteration as a derivation: the weights are chained. -/
lemma tderiv_iterCmd_family {α : ℝ} {c₁ c₂ : Cmd ident M}
    (P : ℕ → St M × St M → Prop) (φ : ℕ → St M × St M → ℝ≥0∞) (N : ℕ)
    (hstep : ∀ k, k < N → TDeriv α (P k) (φ k) c₁ c₂ (P (k + 1)) (φ (k + 1))) :
    ∀ n k, k + n ≤ N →
      TDeriv α (P k) (φ k) (iterCmd c₁ n) (iterCmd c₂ n) (P (k + n)) (φ (k + n)) := by
  intro n
  induction n with
  | zero => intro k _; exact TDeriv.skip (P k) (φ k)
  | succ n ih =>
    intro k hk
    rw [show k + (n + 1) = k + 1 + n by omega]
    exact TDeriv.seq (hstep k (by omega)) (ih (k + 1) (by omega))

/-- `c` contains no `abort` (which has no proof rule). -/
def AbortFree : Cmd ident M → Prop
  | .abort => False
  | .cond _ c1 c2 => AbortFree c1 ∧ AbortFree c2
  | .seq c1 c2 => AbortFree c1 ∧ AbortFree c2
  | .while _ c => AbortFree c
  | .loc _ c => AbortFree c
  | _ => True

/-- **A judgment `c ∼ c` with an unsatisfiable precondition is derivable**, by structural
    induction on the `abort`-free program, each case being its own rule at the assertion
    `False` closed by [Conseq]. -/
theorem tderiv_of_false {α : ℝ} (c : Cmd ident M) :
    AbortFree c →
    ∀ {P Q : St M × St M → Prop} {φ ψ : St M × St M → ℝ≥0∞}, (∀ s, ¬ P s) →
    TDeriv α P φ c c Q ψ := by
  induction c with
  | abort => exact fun haf => (haf : False).elim
  | skip =>
      intro _ _ _ _ _ h
      exact TDeriv.conseq (fun s hs => absurd hs (h s)) (fun s hs => absurd hs (h s))
        (fun _ hq => hq.elim) (fun _ hq => hq.elim)
        (TDeriv.skip (fun _ => False) (fun _ => 1))
  | assign x e =>
      intro _ _ _ _ _ h
      exact TDeriv.conseq (fun s hs => absurd hs (h s)) (fun s hs => absurd hs (h s))
        (fun _ hq => hq.elim) (fun _ hq => hq.elim)
        (TDeriv.assign x e x e (fun _ => False) (fun _ => 1))
  | @random _ x κ _ =>
      intro _ _ _ _ _ h
      exact TDeriv.rndLift x x κ κ _ _ _ _ (rrhl_bot h)
  | cond e c1 c2 ih1 ih2 =>
      intro haf _ _ _ _ h
      have haf' : AbortFree c1 ∧ AbortFree c2 := haf
      exact TDeriv.if_ (fun s hs => absurd hs (h s))
        (ih1 haf'.1 (fun s hs => h s hs.1))
        (ih2 haf'.2 (fun s hs => h s hs.1))
  | «while» e c _ih =>
      intro _ P _ φ ψ h
      refine TDeriv.conseq (fun s hs => hs) (fun _ _ => le_rfl)
        (fun _ hq => hq.1.elim) (fun _ hq => hq.1.elim)
        (TDeriv.whileInv 0 (fun _ => P) (fun _ => φ) (fun _ => False) ψ
          (fun k hk => absurd hk (Nat.not_lt_zero k))
          (fun _ s hs => absurd hs (h s))
          (fun s hs => absurd hs (h s))
          (fun _ _ s hs _ => absurd hs (h s)))
  | seq c1 c2 ih1 ih2 =>
      intro haf _ _ _ _ h
      have haf' : AbortFree c1 ∧ AbortFree c2 := haf
      exact TDeriv.seq (Q := fun _ => False) (ψ := fun _ => 1)
        (ih1 haf'.1 h) (ih2 haf'.2 (fun _ hs => hs))
  | release e =>
      intro _ _ _ _ _ h
      exact TDeriv.conseq (fun s hs => absurd hs (h s)) (fun s hs => absurd hs (h s))
        (fun _ hq => hq.elim) (fun _ hq => hq.elim)
        (TDeriv.release e e (fun _ => False) (fun _ => 1))
  | loc x c ih =>
      intro haf _ _ _ _ h
      exact TDeriv.conseq (fun s hs => absurd hs (h s)) (fun s hs => absurd hs (h s))
        (fun _ hq => hq) (fun _ _ => le_rfl)
        (TDeriv.loc x x (c₁ := c) (c₂ := c) (P := fun _ => False) (φ := fun _ => 1)
          (ih haf (fun _ hs => hs)))

/-- **[While] for a loop run `N` times**: the invariant `P k` holds after `k` iterations,
    the guards are true below `N` (`hIg`) and false at `N` (`hIN`).  `TDeriv.whileInv` at
    the reversed index `N − k`. -/
theorem tderiv_while_count {α : ℝ} {e₁ e₂ : BExpr M} {c₁ c₂ : Cmd ident M}
    (N : ℕ) (P : ℕ → St M × St M → Prop) (φ : ℕ → St M × St M → ℝ≥0∞)
    (hstep : ∀ k, k < N → TDeriv α (P k) (φ k) c₁ c₂ (P (k + 1)) (φ (k + 1)))
    (hIg : ∀ k s, P k s → k < N → esem e₁ s.1.1 = true ∧ esem e₂ s.2.1 = true)
    (hIN : ∀ s, P N s → esem e₁ s.1.1 = false ∧ esem e₂ s.2.1 = false) :
    TDeriv α (P 0) (φ 0) (Cmd.while e₁ c₁) (Cmd.while e₂ c₂) (P N) (φ N) := by
  have hrev : ∀ k, k < N → N - (k + 1) + 1 = N - k := fun k hk => by omega
  -- synchronization: the index decides the guard, so both sides agree on it
  have hsync : ∀ k s, P (N - k) s → esem e₁ s.1.1 = esem e₂ s.2.1 := by
    intro k s hs
    rcases Nat.lt_or_ge (N - k) N with hlt | hge
    · obtain ⟨h1, h2⟩ := hIg _ s hs hlt; rw [h1, h2]
    · obtain ⟨h1, h2⟩ := hIN s (by rw [show N = N - k from by omega]; exact hs)
      rw [h1, h2]
  -- one iteration, at the reversed index; the guard conjuncts are simply dropped
  have hstep' : ∀ k, k < N → TDeriv α
      (fun s => P (N - (k + 1)) s ∧ esem e₁ s.1.1 = true ∧ esem e₂ s.2.1 = true)
      (φ (N - (k + 1))) c₁ c₂ (P (N - k)) (φ (N - k)) := by
    intro k hk
    have h := hstep (N - (k + 1)) (by omega)
    rw [hrev k hk] at h
    exact TDeriv.conseq (fun _ hs => hs.1) (fun _ _ => le_rfl) (fun _ h => h)
      (fun _ _ => le_rfl) h
  -- an early exit is vacuous: strictly below `N` the guard is true
  have hexit : ∀ k, k ≤ N → ∀ s, P (N - k) s → esem e₁ s.1.1 = false →
      P N s ∧ φ N s ≤ φ (N - k) s := by
    intro k hk s hs hfalse
    have hk0 : k = 0 := by
      by_contra hne
      have hlt : N - k < N := by omega
      rw [(hIg _ s hs hlt).1] at hfalse
      exact Bool.noConfusion hfalse
    subst hk0
    simp only [Nat.sub_zero] at hs ⊢
    exact ⟨hs, le_rfl⟩
  have hw := TDeriv.whileInv (e₁ := e₁) (e₂ := e₂) (c₁ := c₁) (c₂ := c₂) N
    (fun k => P (N - k)) (fun k => φ (N - k)) (P N) (φ N) hstep' hsync
    (fun s hs => (hIN s (by simpa using hs)).1) hexit
  simp only [Nat.sub_self, Nat.sub_zero] at hw
  exact TDeriv.conseq (fun _ h => h) (fun _ _ => le_rfl) (fun _ hs => hs.1)
    (fun _ _ => le_rfl) hw

end Continuous
