import Xhl.Logic.Rrhl.Deriv
import Xhl.Examples.DPFTRLMatrix.ReleasePrograms

open Continuous

/-!
# Amplified banded DP-FTRL (Appendix D.5): shared facts

The banded study reuses the matrix-mechanism study's parameters `DPFTRL.TParams`, side
conditions `DPFTRL.TOK` and round tail (`Y[t] := (C·H)_t + z`, `θ := −(1/λ)·(B·Y)_t`,
release `θ`, as in Fig. 8), at the symmetric adjacency `AdjAtSym`.  The schedule field
`part` of the record is not read: the coins decide participation.

Contents: the `⊥`-record fact `clipV_grad_none`, the linear-algebra core
`rowMean_of_blk_agree`, and the release of the model `tderiv_releaseX`.
-/

open MeasureTheory ProbabilityTheory ENNReal
open scoped NNReal

variable {ident : Type} {M : MemType ident}

namespace DPFTRL.Band

open Continuous

variable {d e n T R : ℕ} {τ : Ty} [NeZero T] [NeZero R]

/-- **A missing record contributes nothing**: `∇ℓ(θ,⊥) = 0` and `clip_Γ(0) = 0`. -/
@[simp] lemma clipV_grad_none (p : TParams d e n T R τ) (xx : EuclideanSpace ℝ (Fin d)) :
    clipV p.Cl (p.grad xx none) = 0 := by
  rw [p.grad_bot, clipV_zero]

/-- **Only the distinguished slot reaches a release.**  If two histories agree at every
    slot that release `r` actually reads — every `s ≠ c` with a nonzero coefficient — then
    the two means `r` forms differ by exactly the slot-`c` difference, scaled by `C r c`. -/
lemma rowMean_of_blk_agree {p : TParams d e n T R τ} {r : Fin R} {c : Fin T}
    {H₁ H₂ : EuclideanSpace ℝ (Fin (T * d))}
    (hagr : ∀ s : Fin T, p.C r s ≠ 0 → s ≠ c → blk H₁ s = blk H₂ s) :
    rowMean p.C r H₁ = rowMean p.C r H₂ + p.C r c • (blk H₁ c - blk H₂ c) := by
  classical
  unfold rowMean
  have hterm : ∀ s : Fin T, p.C r s • blk H₁ s
      = p.C r s • blk H₂ s + p.C r s • (if s = c then blk H₁ c - blk H₂ c else 0) := by
    intro s
    by_cases hsc : s = c
    · rw [if_pos hsc, hsc, smul_sub]; abel
    · rw [if_neg hsc, smul_zero, add_zero]
      by_cases hC : p.C r s = 0
      · rw [hC, zero_smul, zero_smul]
      · rw [hagr s hC hsc]
  rw [Finset.sum_congr rfl fun s _ => hterm s, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single c (fun s _ hs => by rw [if_neg hs, smul_zero])
    (fun hc => absurd (Finset.mem_univ c) hc), if_pos rfl]

/-! ## [Release] of an equal model -/

variable {v : TVars ident d T R τ}

omit [NeZero T] [NeZero R] in
/-- **[Release]** of the model `θ`, when the invariant forces it equal on both sides. -/
lemma tderiv_releaseX {α : ℝ} (A : M.heap × M.heap → Prop)
    (heq : ∀ m, A m → tX v m.1 = tX v m.2) :
    TDeriv (M := M) α (liftP A) (fun _ => 1) (Cmd.release (Expr.var v.x))
      (Cmd.release (Expr.var v.x)) (liftP A) (fun _ => 1) :=
  TDeriv.conseq
    (fun s hs => ⟨hs.1, by
      show s.1.2.snoc ⟨_, _⟩ = s.2.2.snoc ⟨_, _⟩
      rw [hs.2]; exact congrArg (fun x => s.2.2.snoc ⟨_, x⟩) (heq _ hs.1)⟩)
    (fun _ _ => le_rfl) (fun _ h => h) (fun _ _ => le_rfl)
    (TDeriv.release (Expr.var v.x) (Expr.var v.x) (liftP A) (fun _ => 1))

end DPFTRL.Band
