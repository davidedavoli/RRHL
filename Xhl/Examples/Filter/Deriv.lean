import Xhl.Logic.Rrhl.Readout
import Xhl.Logic.Rrhl.Deriv
import Xhl.Examples.Filter.Support

open Continuous

/-!
# Noisy gradient descent with per-record Rényi filters: the derivation (§5.2, Appendix E.3)

`filter_gen_deriv` derives judgment (10) for `filterGen` in `TDeriv`: **[Assn]** for the
assignments, **[While]** (as the budget chain `TDeriv.whileInv`) for the record loop at the
weight `wMidT` and for the rounds at the weight `wEndT` (premise (11) is `tderiv_roundT`),
**[Samp-Gap]** (`TDeriv.rndGap`) for the noise, **[Release]**, **[Seq]** and **[Conseq]**.
The adjacency is `AdjAtSym p.record j`; the record step is the same argument in either
orientation (`step_preservesT`).

* `filter_gen_deriv` — the derivation, at budget `exp((α − 1)·α·B/2v)`.
* `filter_gen_IndivRDP` — `(α, αB/2v)`-individual RDP, by Proposition 4.4.
* `filter_IndivRDP` — the result on the quoted program `filter`.
-/

open MeasureTheory ProbabilityTheory ENNReal
open scoped NNReal

variable {ident : Type} {M : MemType ident}

namespace RenyiFilter

open Continuous

variable {d e n : ℕ} {τ : Ty}

/-! ## Rules in the form used by the derivation -/

section Rules

/-- A deterministic assignment, with the postcondition and the weight checked on the
    updated memories: **[Assn]** followed by **[Conseq]**. -/
lemma tderiv_assign_mem {α : ℝ} {ty : Ty} (x : Vars ident ty) (e : Expr M ty)
    (A Q : M.heap × M.heap → Prop) (φ ψ : M.heap × M.heap → ℝ≥0∞)
    (hQ : ∀ m, A m → Q (M.set m.1 ty x.name (esem e m.1), M.set m.2 ty x.name (esem e m.2)))
    (hw : ∀ m, A m → ψ (M.set m.1 ty x.name (esem e m.1), M.set m.2 ty x.name (esem e m.2))
      ≤ φ m) :
    TDeriv (M := M) α (liftP A) (liftW φ) (Cmd.assign x e) (Cmd.assign x e) (liftP Q)
      (liftW ψ) :=
  TDeriv.conseq (fun _ hs => ⟨hQ _ hs.1, hs.2⟩) (fun _ hs => hw _ hs.1) (fun _ h => h)
    (fun _ _ => le_rfl) (TDeriv.assign x e x e (liftP Q) (liftW ψ))

/-- The same for two assignments in sequence. -/
lemma tderiv_assign2_mem {α : ℝ} {t₁ t₂ : Ty} (x₁ : Vars ident t₁) (e₁ : Expr M t₁)
    (x₂ : Vars ident t₂) (e₂ : Expr M t₂)
    (A Q : M.heap × M.heap → Prop) (φ ψ : M.heap × M.heap → ℝ≥0∞)
    (hQ : ∀ m, A m → Q (M.set (M.set m.1 t₁ x₁.name (esem e₁ m.1)) t₂ x₂.name
        (esem e₂ (M.set m.1 t₁ x₁.name (esem e₁ m.1))),
      M.set (M.set m.2 t₁ x₁.name (esem e₁ m.2)) t₂ x₂.name
        (esem e₂ (M.set m.2 t₁ x₁.name (esem e₁ m.2)))))
    (hw : ∀ m, A m → ψ (M.set (M.set m.1 t₁ x₁.name (esem e₁ m.1)) t₂ x₂.name
        (esem e₂ (M.set m.1 t₁ x₁.name (esem e₁ m.1))),
      M.set (M.set m.2 t₁ x₁.name (esem e₁ m.2)) t₂ x₂.name
        (esem e₂ (M.set m.2 t₁ x₁.name (esem e₁ m.2)))) ≤ φ m) :
    TDeriv (M := M) α (liftP A) (liftW φ) (Cmd.seq (Cmd.assign x₁ e₁) (Cmd.assign x₂ e₂))
      (Cmd.seq (Cmd.assign x₁ e₁) (Cmd.assign x₂ e₂)) (liftP Q) (liftW ψ) :=
  TDeriv.conseq (fun _ hs => ⟨hQ _ hs.1, hs.2⟩) (fun _ hs => hw _ hs.1) (fun _ h => h)
    (fun _ _ => le_rfl)
    (TDeriv.seq
      (TDeriv.assign x₁ e₁ x₁ e₁
        (fun s => liftP Q ((M.set s.1.1 t₂ x₂.name (esem e₂ s.1.1), s.1.2),
          (M.set s.2.1 t₂ x₂.name (esem e₂ s.2.1), s.2.2)))
        (fun s => liftW ψ ((M.set s.1.1 t₂ x₂.name (esem e₂ s.1.1), s.1.2),
          (M.set s.2.1 t₂ x₂.name (esem e₂ s.2.1), s.2.2))))
      (TDeriv.assign x₂ e₂ x₂ e₂ (liftP Q) (liftW ψ)))

end Rules

/-! ## The record step -/

section Step

variable {p : TapParams d e n τ} {v : TapVars ident d n τ} {tv : Vars ident .nat}

/-- The record step — three **[Assn]** and two **[Seq]** — with the postcondition and the
    weight checked on the stepped memories. -/
lemma tderiv_bodyT_mem {α : ℝ} (hok : TapOK p v)
    (A Q : M.heap × M.heap → Prop) (φ ψ : M.heap × M.heap → ℝ≥0∞)
    (hQ : ∀ m, A m → Q (stepMapT p v m.1, stepMapT p v m.2))
    (hw : ∀ m, A m → ψ (stepMapT p v m.1, stepMapT p v m.2) ≤ φ m) :
    TDeriv (M := M) α (liftP A) (liftW φ) (bodyT p v hok) (bodyT p v hok) (liftP Q)
      (liftW ψ) := by
  unfold bodyT
  have h := TDeriv.seq
    (TDeriv.assign (M := M) (α := α) v.acc (accET p v hok) v.acc (accET p v hok) _ _)
    (TDeriv.seq
      (TDeriv.assign v.s (sET p v hok) v.s (sET p v hok) _ _)
      (TDeriv.assign v.i (incW v.i) v.i (incW v.i) (liftP Q) (liftW ψ)))
  exact TDeriv.conseq (fun _ hs => ⟨hQ _ hs.1, hs.2⟩) (fun _ hs => hw _ hs.1) (fun _ h => h)
    (fun _ _ => le_rfl) h

end Step

/-! ## The round -/

section Round

variable {p : TapParams d e n τ} {v : TapVars ident d n τ} {tv : Vars ident .nat}

/-- The initialization: from the round precondition to the loop invariant at `0`. -/
lemma tderiv_initT {α : ℝ} (_hα : 1 < α) (htv : TvOKT v tv) {j : ℕ} (k : ℕ) :
    TDeriv (M := M) α (liftP (withT tv (PreT p v j) k)) (liftW (wEndT p v α j)) (initT v)
      (initT v) (liftP (withT tv (JT p v j 0) k)) (liftW (wMidT p v α j)) := by
  have ht : ∀ h : M.heap,
      fT tv (M.set (M.set h .nat v.i.name 0) (.vec d) v.acc.name 0) = fT tv h :=
    fun h => by
      unfold fT
      rw [get_set_other _ _ (Ne.symm htv.acc), get_set_other _ _ (Ne.symm htv.i)]
  refine tderiv_assign2_mem v.i (Expr.cst (t := .nat) 0) v.acc (Expr.cst (t := .vec d) 0)
    _ _ _ _ (fun m hm => ?_) (fun m hm => ?_)
  · obtain ⟨⟨hadj, hx, hsk, ⟨hq1, hq2⟩, hr0, hrB⟩, ht1, ht2⟩ := hm
    obtain ⟨x1, d1, s1, i1, a1⟩ := initT_get (v := v) m.1
    obtain ⟨x2, d2, s2, i2, a2⟩ := initT_get (v := v) m.2
    have hr : remP p v j (M.set (M.set m.1 .nat v.i.name 0) (.vec d) v.acc.name 0,
        M.set (M.set m.2 .nat v.i.name 0) (.vec d) v.acc.name 0) = remP p v j m :=
      remP_congr s1 s2
    show withT tv (JT p v j 0) k (M.set (M.set m.1 .nat v.i.name 0) (.vec d) v.acc.name 0,
      M.set (M.set m.2 .nat v.i.name 0) (.vec d) v.acc.name 0)
    refine ⟨⟨?_, ?_, i1, i2, ?_, fun _ => by
      show tapA v _ = tapA v _; rw [a1, a2], ⟨fun hn => ?_, fun hn => ?_⟩,
      by rw [hr]; exact hr0, ?_⟩,
      by rw [ht]; exact ht1, by rw [ht]; exact ht2⟩
    · show AdjAtSym p.record j (tapD v _) (tapD v _); rw [d1, d2]; exact hadj
    · show tapX v _ = tapX v _; rw [x1, x2]; exact hx
    · intro k hk; show tapS v _ k = tapS v _ k; rw [s1, s2]; exact hsk k hk
    · show remAt (tapS v _) j = 0; rw [s1]; exact hq1 (by rw [← d1]; exact hn)
    · show remAt (tapS v _) j = 0; rw [s2]; exact hq2 (by rw [← d2]; exact hn)
    · rw [hr]
      show remP p v j m + ‖tapA v _ - tapA v _‖ ^ 2 ≤ p.Bnorm
      rw [a1, a2, sub_self, norm_zero]
      simpa using hrB
  · obtain ⟨x1, d1, s1, i1, a1⟩ := initT_get (v := v) m.1
    obtain ⟨x2, d2, s2, i2, a2⟩ := initT_get (v := v) m.2
    show wMidT p v α j (M.set (M.set m.1 .nat v.i.name 0) (.vec d) v.acc.name 0,
      M.set (M.set m.2 .nat v.i.name 0) (.vec d) v.acc.name 0) ≤ wEndT p v α j m
    simp only [wMidT, wEndT, expW]
    rw [remP_congr s1 s2, a1, a2, sub_self, norm_zero]
    simp

/-- **The record loop**, by **[While]** (`TDeriv.whileInv`) at the weight `wMidT`, which the
    record step conserves exactly. -/
lemma tderiv_loopT {α : ℝ} (_hα : 1 < α) (hC : 0 ≤ p.Cl) (hok : TapOK p v)
    (htv : TvOKT v tv) {j : ℕ} (hj : j < n) (k : ℕ) :
    TDeriv (M := M) α (liftP (withT tv (JT p v j 0) k)) (liftW (wMidT p v α j))
      (Cmd.while (guardIT v) (bodyT p v hok)) (Cmd.while (guardIT v) (bodyT p v hok))
      (liftP (withT tv (JT p v j n) k)) (liftW (wMidT p v α j)) := by
  have hstep : ∀ t, t < n → TDeriv (M := M) α (liftP (withT tv (JT p v j t) k))
      (liftW (wMidT p v α j)) (bodyT p v hok) (bodyT p v hok)
      (liftP (withT tv (JT p v j (t + 1)) k))
      (liftW (wMidT p v α j)) := by
    intro t _
    refine tderiv_bodyT_mem hok _ _ _ _
      (fun m hm => ⟨(step_preservesT hC hj t m hm.1).1, by rw [fT_stepMapT htv]; exact hm.2.1,
        by rw [fT_stepMapT htv]; exact hm.2.2⟩)
      (fun m hm => le_of_eq ?_)
    show ENNReal.ofReal (Real.exp ((α - 1) *
        (cT p α * remP p v j (stepMapT p v m.1, stepMapT p v m.2)
          + cT p α * ‖tapA v (stepMapT p v m.1) - tapA v (stepMapT p v m.2)‖ ^ 2)))
      = ENNReal.ofReal (Real.exp ((α - 1) *
        (cT p α * remP p v j m + cT p α * ‖tapA v m.1 - tapA v m.2‖ ^ 2)))
    rw [← mul_add, ← mul_add, (step_preservesT hC hj t m hm.1).2]
  have hesem : ∀ a : M.heap, esem (guardIT (M := M) v) a = decide (tapI v a < n) := fun a => rfl
  have h := TDeriv.whileInv (α := α) (e₁ := guardIT v) (e₂ := guardIT v)
    (c₁ := bodyT p v hok) (c₂ := bodyT p v hok) n
    (fun i => liftP (withT tv (JT p v j (n - i)) k))
    (fun _ => liftW (wMidT p v α j))
    (liftP (withT tv (JT p v j n) k)) (liftW (wMidT p v α j))
    (fun i hi => by
      have e : n - (i + 1) + 1 = n - i := by omega
      have h := hstep (n - (i + 1)) (by omega)
      rw [e] at h
      exact TDeriv.conseq (fun s hs => hs.1) (fun _ _ => le_rfl) (fun _ h => h)
        (fun _ _ => le_rfl) h)
    (fun i s hs => by
      have e1 : tapI v s.1.1 = n - i := hs.1.1.2.2.1
      have e2 : tapI v s.2.1 = n - i := hs.1.1.2.2.2.1
      rw [hesem, hesem, e1, e2])
    (fun s hs => by
      have e1 : tapI v s.1.1 = n - 0 := hs.1.1.2.2.1
      rw [hesem, decide_eq_false_iff_not]; omega)
    (fun i hi s hs hfalse => by
      have e1 : tapI v s.1.1 = n - i := hs.1.1.2.2.1
      rw [hesem, decide_eq_false_iff_not] at hfalse
      rw [show n - i = n by omega] at hs
      exact ⟨hs, le_rfl⟩)
  refine TDeriv.conseq (fun s hs => ?_) (fun _ _ => le_rfl) (fun s h => h.1)
    (fun _ _ => le_rfl) h
  rw [Nat.sub_self]
  exact hs

/-- **The noise**, by **[Samp-Gap]** at the gap of the two sums: the noisy sums agree, and the
    Gaussian cost `exp(α(α−1)‖g‖²/2v)` is paid out of `wMidT`, leaving `wEndT`. -/
lemma tderiv_noiseT {α : ℝ} (hα : 1 < α) (htv : TvOKT v tv)
    (hnv : p.nvar ≠ 0) {j : ℕ} (k : ℕ) :
    TDeriv (M := M) α (liftP (withT tv (JT p v j n) k)) (liftW (wMidT p v α j))
      (Cmd.random v.z (noiseKernelE p.nvar)) (Cmd.random v.z (noiseKernelE p.nvar))
      (liftP (withT tv (Q2T p v j) k)) (liftW (wEndT p v α j)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := v.ne
  have hnv' : (0 : ℝ) < p.nvar := by exact_mod_cast hnv.bot_lt
  have hgs : ∀ (h : M.heap) (w : EuclideanSpace ℝ (Fin d)),
      tapS v (M.set h (.vec d) v.z.name w) = tapS v h := fun h w => get_set_other _ _ h10
  have hgx : ∀ (h : M.heap) (w : EuclideanSpace ℝ (Fin d)),
      tapX v (M.set h (.vec d) v.z.name w) = tapX v h := fun h w => get_set_other _ _ (Ne.symm h2)
  have hgd : ∀ (h : M.heap) (w : EuclideanSpace ℝ (Fin d)),
      tapD v (M.set h (.vec d) v.z.name w) = tapD v h := fun h w => get_set_other _ _ h12
  have hga : ∀ (h : M.heap) (w : EuclideanSpace ℝ (Fin d)),
      tapA v (M.set h (.vec d) v.z.name w) = tapA v h := fun h w => get_set_other _ _ (Ne.symm h6)
  have hgz : ∀ (h : M.heap) (w : EuclideanSpace ℝ (Fin d)),
      tapZ v (M.set h (.vec d) v.z.name w) = w := fun h w => M.get_set_eq _ _ _ _
  have hgt : ∀ (h : M.heap) (w : EuclideanSpace ℝ (Fin d)),
      fT tv (M.set h (.vec d) v.z.name w) = fT tv h :=
    fun h w => get_set_other _ _ (Ne.symm htv.z)
  have hnoise : ∀ (h : M.heap), noiseKernelE (M := M) (d := d) p.nvar h = gaussE 0 p.nvar :=
    fun h => rfl
  have hwE := goodWeight_wEndT (M := M) (p := p) (v := v) (α := α) j
  refine TDeriv.rndGap hα v.z v.z _ _ (fun s => tapA v s.2.1 - tapA v s.1.1) _ _ _ _
    (fun s hs => Filter.Eventually.of_forall fun w => ?_) (fun s hs => ?_)
  · obtain ⟨⟨⟨hadj, hx, -, -, hsk, -, ⟨hq1, hq2⟩, hr0, hrB⟩, ht1, ht2⟩, htr⟩ := hs
    simp only [updPair, liftP, withT]
    refine ⟨⟨⟨⟨?_, ?_, ?_, ⟨fun hn => ?_, fun hn => ?_⟩, ?_, ?_⟩, ?_⟩,
      by rw [hgt]; exact ht1, by rw [hgt]; exact ht2⟩, htr⟩
    · show AdjAtSym p.record j (tapD v _) (tapD v _); rw [hgd, hgd]; exact hadj
    · show tapX v _ = tapX v _; rw [hgx, hgx]; exact hx
    · intro k hk; show tapS v _ k = tapS v _ k; rw [hgs, hgs]; exact hsk k hk
    · show remAt (tapS v _) j = 0; rw [hgs]; exact hq1 (by rw [← hgd s.1.1 w]; exact hn)
    · show remAt (tapS v _) j = 0; rw [hgs]
      exact hq2 (by rw [← hgd s.2.1 (w - (tapA v s.2.1 - tapA v s.1.1))]; exact hn)
    · rw [remP_congr (hgs _ _) (hgs _ _)]; exact hr0
    · rw [remP_congr (hgs _ _) (hgs _ _)]
      have hrB' : remP p v j (s.1.1, s.2.1)
          + ‖tapA v s.1.1 - tapA v s.2.1‖ ^ 2 ≤ p.Bnorm := hrB
      linarith [sq_nonneg ‖tapA v s.1.1 - tapA v s.2.1‖]
    · show tapA v _ + tapZ v _ = tapA v _ + tapZ v _
      rw [hga, hga, hgz, hgz]; abel
  · obtain ⟨⟨⟨-, -, -, -, -, -, hr0, hrB⟩, -, -⟩, -⟩ := hs
    -- the weight after the sampling does not depend on the sample
    have hconst : (fun w : EuclideanSpace ℝ (Fin d) => liftW (wEndT p v α j)
        (updPair v.z v.z s (w, w - (tapA v s.2.1 - tapA v s.1.1))))
        = fun _ => wEndT p v α j (s.1.1, s.2.1) * 1 := by
      funext w
      rw [mul_one]
      simp only [updPair, liftW, wEndT, expW]
      rw [remP_congr (hgs _ _) (hgs _ _)]
    rw [hconst, weightedHellingerIntegral_const_mul _ (hwE.ne_zero _) _ measurable_const, weightedHellingerIntegral_one, hnoise,
      hnoise, gaussE_map_add_const]
    set g := tapA v s.1.1 - tapA v s.2.1 with hg
    have hleaf := gaussE_leaf hα hnv (0 : EuclideanSpace ℝ (Fin d))
      (0 + (tapA v s.2.1 - tapA v s.1.1))
    have hn : ‖(0 : EuclideanSpace ℝ (Fin d)) - (0 + (tapA v s.2.1 - tapA v s.1.1))‖ = ‖g‖ := by
      rw [zero_add, zero_sub, norm_neg, hg, norm_sub_rev]
    rw [hn] at hleaf
    calc wEndT p v α j (s.1.1, s.2.1)
          * hellingerIntegral α (gaussE 0 p.nvar) (gaussE (0 + (tapA v s.2.1 - tapA v s.1.1)) p.nvar)
        ≤ wEndT p v α j (s.1.1, s.2.1) * ENNReal.ofReal
            (Real.exp (α * (α - 1) * ‖g‖ ^ 2 / (2 * (p.nvar : ℝ)))) :=
          mul_le_mul' le_rfl hleaf
      _ ≤ liftW (wMidT p v α j) s := by
          have hcancel : (cT p α * remP p v j (s.1.1, s.2.1) + cT p α * ‖g‖ ^ 2)
              - cT p α * ‖g‖ ^ 2 = cT p α * remP p v j (s.1.1, s.2.1) := add_sub_cancel_right _ _
          have hcharge := expW_charge_le hα
            (bv := cT p α * remP p v j (s.1.1, s.2.1) + cT p α * ‖g‖ ^ 2)
            (ρ := cT p α * ‖g‖ ^ 2) (D := ‖g‖) (σ2 := (p.nvar : ℝ))
            (le_of_eq (by unfold cT; ring))
          rw [hcancel] at hcharge
          simp only [liftW, wEndT, wMidT, expW]
          exact hcharge

/-- The update keeps the precondition of the next round and the filter weight.  The two
    runs read the same round counter, so they apply the same learning rate. -/
lemma tderiv_updT {α : ℝ} (_hα : 1 < α) (htv : TvOKT v tv)
    {j : ℕ} (k : ℕ) :
    TDeriv (M := M) α (liftP (withT tv (Q2T p v j) k)) (liftW (wEndT p v α j))
      (Cmd.assign v.x (updET p v tv)) (Cmd.assign v.x (updET p v tv))
      (liftP (withT tv (PreT p v j) k)) (liftW (wEndT p v α j)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := v.ne
  have hgs : ∀ (h : M.heap) (w : EuclideanSpace ℝ (Fin d)),
      tapS v (M.set h (.vec d) v.x.name w) = tapS v h := fun h w => get_set_other _ _ h3
  have hgd : ∀ (h : M.heap) (w : EuclideanSpace ℝ (Fin d)),
      tapD v (M.set h (.vec d) v.x.name w) = tapD v h := fun h w => get_set_other _ _ h5
  have hgt : ∀ (h : M.heap) (w : EuclideanSpace ℝ (Fin d)),
      fT tv (M.set h (.vec d) v.x.name w) = fT tv h :=
    fun h w => get_set_other _ _ (Ne.symm htv.x)
  refine tderiv_assign_mem v.x (updET p v tv) _ _ _ _ (fun m hm => ?_) (fun m hm => ?_)
  · obtain ⟨⟨⟨hadj, hx, hsk, ⟨hq1, hq2⟩, hr0, hrB⟩, hsum⟩, ht1, ht2⟩ := hm
    refine ⟨⟨?_, ?_, ?_, ⟨fun hn => ?_, fun hn => ?_⟩, ?_, ?_⟩,
      by rw [hgt]; exact ht1, by rw [hgt]; exact ht2⟩
    · show AdjAtSym p.record j (tapD v _) (tapD v _); rw [hgd, hgd]; exact hadj
    · show tapX v _ = tapX v _
      rw [tapX, tapX, M.get_set_eq, M.get_set_eq]
      show updStepTap p.η n (fT tv m.1) (tapX v m.1) (tapA v m.1) (tapZ v m.1)
        = updStepTap p.η n (fT tv m.2) (tapX v m.2) (tapA v m.2) (tapZ v m.2)
      unfold updStepTap
      rw [hx, ht1, ht2, hsum]
    · intro k hk; show tapS v _ k = tapS v _ k; rw [hgs, hgs]; exact hsk k hk
    · show remAt (tapS v _) j = 0; rw [hgs]; exact hq1 (by rw [← hgd m.1 (esem (updET p v tv) m.1)]; exact hn)
    · show remAt (tapS v _) j = 0; rw [hgs]; exact hq2 (by rw [← hgd m.2 (esem (updET p v tv) m.2)]; exact hn)
    · rw [remP_congr (hgs _ _) (hgs _ _)]; exact hr0
    · rw [remP_congr (hgs _ _) (hgs _ _)]; exact hrB
  · simp only [wEndT, expW]; rw [remP_congr (hgs _ _) (hgs _ _)]

/-- The counter. -/
lemma tderiv_incTT {α : ℝ} (_hα : 1 < α) (htv : TvOKT v tv) {j : ℕ} (k : ℕ) :
    TDeriv (M := M) α (liftP (withT tv (PreT p v j) k)) (liftW (wEndT p v α j))
      (Cmd.assign tv (incW tv)) (Cmd.assign tv (incW tv))
      (liftP (withT tv (PreT p v j) (k + 1))) (liftW (wEndT p v α j)) := by
  refine tderiv_assign_mem tv (incW tv) _ _ _ _ (fun m hm => ?_) (fun m hm => ?_)
  · obtain ⟨hpre, ht1, ht2⟩ := hm
    refine ⟨PreT_set_t htv m hpre _ _, ?_, ?_⟩
    · show M.get (M.set m.1 .nat tv.name (fT tv m.1 + 1)) .nat tv.name = k + 1
      rw [M.get_set_eq, ht1]
    · show M.get (M.set m.2 .nat tv.name (fT tv m.2 + 1)) .nat tv.name = k + 1
      rw [M.get_set_eq, ht2]
  · exact le_of_eq (wEndT_set_t htv m _ _)

/-- **One round** keeps the filter weight of record `j` and advances the counter. -/
theorem tderiv_roundT {α : ℝ} (hα : 1 < α) (hC : 0 ≤ p.Cl) (hok : TapOK p v)
    (htv : TvOKT v tv) (hnv : p.nvar ≠ 0) {j : ℕ} (hj : j < n) (k : ℕ) :
    TDeriv (M := M) α (liftP (withT tv (PreT p v j) k)) (liftW (wEndT p v α j))
      (roundT p v tv hok) (roundT p v tv hok) (liftP (withT tv (PreT p v j) (k + 1)))
      (liftW (wEndT p v α j)) := by
  unfold roundT
  refine TDeriv.seq (tderiv_initT hα htv k) (TDeriv.seq (tderiv_loopT hα hC hok htv hj k)
    (TDeriv.seq (tderiv_noiseT hα htv hnv k) (TDeriv.seq (tderiv_updT hα htv k)
      (TDeriv.seq ?_ (tderiv_incTT hα htv k)))))
  refine TDeriv.conseq ?_ (fun _ _ => le_rfl) (fun _ h => h) (fun _ _ => le_rfl)
    (TDeriv.release (Expr.var v.x) (Expr.var v.x) _ (liftW (wEndT p v α j)))
  intro s hs
  refine ⟨hs.1, ?_⟩
  show s.1.2.snoc ⟨_, _⟩ = s.2.2.snoc ⟨_, _⟩
  rw [hs.2]; exact congrArg (fun x => s.2.2.snoc ⟨_, x⟩) hs.1.1.2.1

end Round

/-! ## The rounds -/

section Rounds

variable {p : TapParams d e n τ} {v : TapVars ident d n τ} {tv : Vars ident .nat}

/-- **The rounds, as a derivation**: from the invariant `PreT`, the `T` rounds keep the
    transcripts equal at budget `exp((α − 1)·α·B/2v)`, independent of `T`. -/
theorem tderiv_roundsT {α : ℝ} (hα : 1 < α) (hC : 0 ≤ p.Cl) (hok : TapOK p v)
    (htv : TvOKT v tv) (hnv : p.nvar ≠ 0) {j : ℕ} (hj : j < n) (hB : 0 ≤ p.Bnorm)
    (T : ℕ) :
    TDeriv (M := M) α (liftP (PreT p v j))
      (fun _ => ENNReal.ofReal (Real.exp ((α - 1) * (α * p.Bnorm / (2 * (p.nvar : ℝ))))))
      (roundsT p v tv hok T) (roundsT p v tv hok T) (liftP (PreT p v j)) (fun _ => 1) := by
  have hcB : 0 ≤ cT p α * p.Bnorm := mul_nonneg (cT_nonneg hα) hB
  have hesem : ∀ a : M.heap, esem (guardTT (M := M) tv T) a = decide (fT tv a < T) := fun a => rfl
  have hloop' := TDeriv.whileInv (α := α) (e₁ := guardTT tv T) (e₂ := guardTT tv T)
    (c₁ := roundT p v tv hok) (c₂ := roundT p v tv hok) T
    (fun i => liftP (withT tv (PreT p v j) (T - i)))
    (fun _ => liftW (wEndT p v α j))
    (liftP (withT tv (PreT p v j) T)) (liftW (wEndT p v α j))
    (fun i hi => by
      have e : T - (i + 1) + 1 = T - i := by omega
      have h := tderiv_roundT (M := M) hα hC hok htv hnv hj (T - (i + 1))
      rw [e] at h
      exact TDeriv.conseq (fun s hs => hs.1) (fun _ _ => le_rfl) (fun _ h => h)
        (fun _ _ => le_rfl) h)
    (fun i s hs => by rw [hesem, hesem, hs.1.2.1, hs.1.2.2])
    (fun s hs => by
      have e1 : fT tv s.1.1 = T - 0 := hs.1.2.1
      rw [hesem, decide_eq_false_iff_not]; omega)
    (fun i hi s hs hfalse => by
      have e1 : fT tv s.1.1 = T - i := hs.1.2.1
      rw [hesem, decide_eq_false_iff_not] at hfalse
      rw [show T - i = T by omega] at hs
      exact ⟨hs, le_rfl⟩)
  have hloop : TDeriv (M := M) α (liftP (withT tv (PreT p v j) 0)) (liftW (wEndT p v α j))
      (Cmd.while (guardTT tv T) (roundT p v tv hok))
      (Cmd.while (guardTT tv T) (roundT p v tv hok))
      (liftP (withT tv (PreT p v j) T)) (liftW (wEndT p v α j)) := by
    refine TDeriv.conseq (fun s hs => ?_) (fun _ _ => le_rfl) (fun s h => h.1)
      (fun _ _ => le_rfl) hloop'
    rw [Nat.sub_self]
    exact hs
  have hinit : TDeriv (M := M) α (liftP (PreT p v j)) (liftW (wEndT p v α j))
      (Cmd.assign tv (Expr.cst (t := .nat) 0)) (Cmd.assign tv (Expr.cst (t := .nat) 0))
      (liftP (withT tv (PreT p v j) 0)) (liftW (wEndT p v α j)) :=
    tderiv_assign_mem tv (Expr.cst (t := .nat) 0) _ _ _ _
      (fun m hm => ⟨PreT_set_t htv m hm 0 0, M.get_set_eq _ _ _ _, M.get_set_eq _ _ _ _⟩)
      (fun m _ => le_of_eq (wEndT_set_t htv m 0 0))
  have hbudget : cT p α * p.Bnorm = α * p.Bnorm / (2 * (p.nvar : ℝ)) := by unfold cT; ring
  -- [Conseq]: `ω ≤ exp((α−1)·cT·B)` and `1 ≤ ω`, both from the invariant
  have hwle : ∀ s : St M × St M, liftP (PreT p v j) s → liftW (wEndT (M := M) p v α j) s
      ≤ ENNReal.ofReal (Real.exp ((α - 1) * (α * p.Bnorm / (2 * (p.nvar : ℝ))))) := by
    intro s hs
    rw [← hbudget]
    show expW α (fun m => cT p α * remP p v j m) (s.1.1, s.2.1)
      ≤ ENNReal.ofReal (Real.exp ((α - 1) * (cT p α * p.Bnorm)))
    exact expW_le_of_le hα (mul_le_mul_of_nonneg_left hs.1.2.2.2.2.2 (cT_nonneg hα))
  have hone : ∀ s : St M × St M, liftP (withT tv (PreT p v j) T) s
      → (1 : ℝ≥0∞) ≤ liftW (wEndT (M := M) p v α j) s := by
    intro s hs
    show (1 : ℝ≥0∞) ≤ expW α (fun m => cT p α * remP p v j m) (s.1.1, s.2.1)
    exact one_le_expW hα (mul_nonneg (cT_nonneg hα) hs.1.1.2.2.2.2.1)
  unfold roundsT
  exact TDeriv.conseq (fun _ h => h) (fun s h => hwle s h)
    (fun s h => ⟨h.1.1, h.2⟩) (fun s h => hone s h)
    (TDeriv.seq hinit hloop)

/-- **The filter, as a derivation** (judgment (10)): from datasets adjacent at `j` and equal
    transcripts, to equal models and transcripts, at budget `exp((α − 1)·α·B/2v)`. -/
theorem filter_gen_deriv {α : ℝ} (hα : 1 < α) (hC : 0 ≤ p.Cl) (hok : TapOK p v)
    (htv : TvOKT v tv) (hnv : p.nvar ≠ 0) {j : ℕ} (hj : j < n) (hB : 0 ≤ p.Bnorm)
    (T : ℕ) :
    TDeriv (M := M) α (liftP (fun m => AdjAtSym p.record j (tapD v m.1) (tapD v m.2)))
      (fun _ => ENNReal.ofReal (Real.exp ((α - 1) * (α * p.Bnorm / (2 * (p.nvar : ℝ))))))
      (filterGen p v tv hok T) (filterGen p v tv hok T)
      (liftP (fun m => tapX v m.1 = tapX v m.2)) (fun _ => 1) := by
  have hinit : TDeriv (M := M) α (liftP (fun m => AdjAtSym p.record j (tapD v m.1) (tapD v m.2)))
      (liftW (fun _ =>
        ENNReal.ofReal (Real.exp ((α - 1) * (α * p.Bnorm / (2 * (p.nvar : ℝ)))))))
      (initGDT v) (initGDT v) (liftP (PreT p v j))
      (liftW (fun _ =>
        ENNReal.ofReal (Real.exp ((α - 1) * (α * p.Bnorm / (2 * (p.nvar : ℝ))))))) := by
    refine tderiv_assign2_mem v.s (Expr.cst (t := .vec n) 0) v.x (Expr.cst (t := .vec d) 0)
      _ _ _ _ (fun m hm => ?_) (fun _ _ => le_rfl)
    obtain ⟨d1, x1, s1⟩ := initGDT_get (v := v) m.1
    obtain ⟨d2, x2, s2⟩ := initGDT_get (v := v) m.2
    show PreT p v j
      (M.set (M.set m.1 (.vec n) v.s.name 0) (.vec d) v.x.name 0,
        M.set (M.set m.2 (.vec n) v.s.name 0) (.vec d) v.x.name 0)
    have hr : remP p v j (M.set (M.set m.1 (.vec n) v.s.name 0) (.vec d) v.x.name 0,
        M.set (M.set m.2 (.vec n) v.s.name 0) (.vec d) v.x.name 0) = p.Bnorm := by
      show (p.Bnorm - remAt (tapS v _) j) + (p.Bnorm - remAt (tapS v _) j) - p.Bnorm = p.Bnorm
      rw [s1, s2, remAt_zero]; ring
    refine ⟨?_, ?_, ?_, ⟨fun _ => ?_, fun _ => ?_⟩, by rw [hr]; exact hB, by rw [hr]⟩
    · show AdjAtSym p.record j (tapD v _) (tapD v _); rw [d1, d2]; exact hm
    · show tapX v _ = tapX v _; rw [x1, x2]
    · intro k hk; show tapS v _ k = tapS v _ k; rw [s1, s2]
    · show remAt (tapS v _) j = 0; rw [s1, remAt_zero]
    · show remAt (tapS v _) j = 0; rw [s2, remAt_zero]
  exact TDeriv.conseq (fun _ h => h) (fun _ _ => le_rfl) (fun _ h => ⟨h.1.2.1, h.2⟩)
    (fun _ _ => le_rfl) (TDeriv.seq hinit (tderiv_roundsT hα hC hok htv hnv hj hB T))

/-- **The filter is `(α, αB/2v)`-individually RDP** (§5.2, Definition 3.6) at the adjacency
    `AdjAtSym p.record j`: `filter_gen_deriv` read out by Proposition 4.4
    (`rrhl_indivRenyiDP`). -/
theorem filter_gen_IndivRDP {α : ℝ} (hα : 1 < α) (hC : 0 ≤ p.Cl)
    (hok : TapOK p v) (htv : TvOKT v tv) (hnv : p.nvar ≠ 0) (hB : 0 ≤ p.Bnorm) (T : ℕ) :
    IndivRenyiDP α (fun _ => α * p.Bnorm / (2 * (p.nvar : ℝ)))
      (fun (j : Fin n) (m₁ m₂ : M.heap) => AdjAtSym p.record j (tapD v m₁) (tapD v m₂))
      (fun (m : M.heap) => (osem (filterGen p v tv hok T) m).map Prod.snd) := by
  have hlev : Real.log (ENNReal.ofReal
      (Real.exp ((α - 1) * (α * p.Bnorm / (2 * (p.nvar : ℝ)))))).toReal
      / (α - 1) = α * p.Bnorm / (2 * (p.nvar : ℝ)) := by
    rw [ENNReal.toReal_ofReal (Real.exp_pos _).le, Real.log_exp,
      mul_div_cancel_left₀ _ (sub_pos.2 hα).ne']
  have h := rrhl_indivRenyiDP (M := M) hα (fun _ => ENNReal.ofReal_ne_top)
    (Adj := fun (j : Fin n) m₁ m₂ => AdjAtSym p.record j (tapD v m₁) (tapD v m₂))
    (fun j => rrhl_conseq (fun _ h => h) (fun _ _ => le_rfl) (fun _ h => h.2) (fun _ _ => le_rfl)
      ((filter_gen_deriv hα hC hok htv hnv j.isLt hB T).sound hα))
  simpa only [hlev] using h

end Rounds

end RenyiFilter

/-! ## The instance on the quoted program `filter` -/

namespace RenyiFilter

open Continuous DPSGDPaper

variable (N dx d : ℕ)
  (grad : EuclideanSpace ℝ (Fin dx) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
  (C : ℝ) (nvar : ℝ≥0) (Bnorm : ℝ) (η : ℕ → ℝ)

/-- **The program of Figure 5 is `(α, αB/2v)`-individually RDP** (§5.2): for every record
    `j`, at `AdjAtSym (recBotN N dx) j`, for every `α > 1` and every number of rounds `T`. -/
theorem filter_IndivRDP {α : ℝ} (hα : 1 < α) (hC : 0 ≤ C)
    (hgrad : Measurable (fun q : EuclideanSpace ℝ (Fin dx) × EuclideanSpace ℝ (Fin d) =>
      grad q.1 q.2)) (hnv : nvar ≠ 0) (hB : 0 ≤ Bnorm) (T : ℕ) :
    IndivRenyiDP α (fun _ : Fin (N + 1) => α * Bnorm / (2 * (nvar : ℝ)))
      (fun (j : Fin (N + 1)) (m₁ m₂ : PMem.heap) =>
        AdjAtSym (recBotN N dx) j (getDS N dx m₁) (getDS N dx m₂))
      (fun m => (osem (filter N dx d grad C nvar Bnorm η hgrad T) m).map Prod.snd) := by
  rw [filter_eq]
  exact filter_gen_IndivRDP (p := fzParamsP N dx d grad C nvar Bnorm η) hα hC
    (fzOKP N dx d grad C nvar Bnorm η hgrad) (fzTvOKP N dx d) hnv hB T

end RenyiFilter
