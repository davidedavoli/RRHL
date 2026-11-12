import Xhl.Examples.Support.GaussVec
import Xhl.Divergence.SubsamplingRealOrderE
import Xhl.Logic.Rrhl.Deriv
import Xhl.Examples.DPSGD.Shared.Equiv.BlockCEquiv

open Continuous

/-!
# Derivation steps shared by the DP-SGD studies

* `tderiv_blockLoc_of_samp` — the sampling block, by **[Equiv]** and **[Local]**;
* `tderiv_loopCnt` — the counted loop, for any body that increments the counter;
* `tderiv_initR` — the initialization `θ ← θ₀ ; t ← 0`.
-/

open MeasureTheory ProbabilityTheory ENNReal Cmd
open scoped NNReal

namespace DPSGDPaper

open Continuous


/-! ## The block and the transcript round's sampling -/

section Block

variable (N dx d : ℕ)
  (grad : EuclideanSpace ℝ (Fin dx) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
  (C : ℝ≥0)
  (v q : ℝ≥0)

/-- The sampling block: **[Equiv]** (by `cequiv_blockLoc_fusedLoc`) and **[Local]** once
    per hidden variable, from a judgment on the fused sampling. -/
theorem tderiv_blockLoc_of_samp {α : ℝ} (hm : MeasOK dx d grad)
    {P Q : St PMem × St PMem → Prop} {Fb : ℝ≥0∞}
    (hP : ∀ s, P s → P (rSt N d s.1, rSt N d s.2)) (hQ : ∀ s, Q s → Q (rSt N d s.1, rSt N d s.2))
    (hsamp : TDeriv (M := PMem) α P (fun _ => Fb)
      (Cmd.random (gtV d) (fusedK N dx d grad C v q hm))
      (Cmd.random (gtV d) (fusedK N dx d grad C v q hm)) Q (fun _ => 1)) :
    TDeriv (M := PMem) α P (fun _ => Fb)
      (blockLoc N dx d grad C v q hm) (blockLoc N dx d grad C v q hm) Q
      (fun _ => 1) := by
  refine TDeriv.equiv
    (cequiv_blockLoc_fusedLoc N dx d grad C v q hm (fun _ => True))
    (cequiv_blockLoc_fusedLoc N dx d grad C v q hm (fun _ => True))
    (fun _ _ => ⟨trivial, trivial⟩) ?_
  have h := TDeriv.locs (α := α) (hidden N d) (P := P) (Q := Q) (φ := fun _ => Fb)
    (ψ := fun _ => 1)
    (TDeriv.conseq (fun _ h => h) (fun _ _ => le_rfl)
      (fun s hs => by rw [postR_hidden]; exact hQ s hs) (fun _ _ => le_rfl) hsamp)
  exact TDeriv.conseq (fun s hs => by rw [preR_hidden]; exact hP s hs)
    (fun _ _ => le_rfl) (fun _ h => h) (fun _ _ => le_rfl) h

end Block

/-! ## The loop -/

section LoopCnt

variable (N dx d T : ℕ) (i : Fin (N + 1))

/-- `getCnt` at the type `ℕ`: the `pvar` reader returns `Ty.nat.interp`, whose atoms
    `omega` does not recognize. -/
noncomputable def cntN (a : PMem.heap) : ℕ := getCnt a

/-- The loop, for a body taking `LInv k` to `LInv (k + 1)` at budget `F k`: the counted
    loop `tderiv_while_prod` (budget `∏ F k`) and **[Conseq]**. -/
theorem tderiv_loopCnt {α : ℝ} (_hα : 1 < α) (c : Cmd String PMem)
    (z : ℕ → ℝ) (F : ℕ → ℝ≥0∞) (hF0 : ∀ k, F k ≠ 0) (hFt : ∀ k, F k ≠ ⊤)
    (hround : ∀ k, k < T → TDeriv (M := PMem) α (LInv N dx d i z k) (fun _ => F k)
      c c (LInv N dx d i z (k + 1)) (fun _ => 1)) :
    TDeriv (M := PMem) α (LInv N dx d i z 0) (fun _ => ∏ k ∈ Finset.range T, F k)
      (Cmd.while (guardE T) c) (Cmd.while (guardE T) c)
      (DInv N dx d i (z T)) (fun _ => 1) := by
  have h := tderiv_while_prod (α := α) (e := guardE T) T (LInv N dx d i z) F hF0 hFt hround
    (fun k s hs hk => by
      have e1 : cntN s.1.1 = k := hs.2.1
      have e2 : cntN s.2.1 = k := hs.2.2
      constructor <;> rw [esem_guardE, decide_eq_true_iff]
      · show cntN s.1.1 < T
        omega
      · show cntN s.2.1 < T
        omega)
    (fun s hs => by
      have e1 : cntN s.1.1 = T := hs.2.1
      have e2 : cntN s.2.1 = T := hs.2.2
      constructor <;> rw [esem_guardE, decide_eq_false_iff_not]
      · show ¬ (cntN s.1.1 < T)
        omega
      · show ¬ (cntN s.2.1 < T)
        omega)
  exact TDeriv.conseq (fun _ h => h) (fun _ _ => le_rfl)
    (fun s (h : LInv N dx d i z T s) => h.1) (fun _ _ => le_rfl) h

end LoopCnt

/-! ## The initialization of the released programs -/

section InitR

variable (d : ℕ)

/-- The initialization `θ ← θ₀ ; t ← 0`, as a function on states. -/
noncomputable def initFR (θ₀ : EuclideanSpace ℝ (Fin d)) (s : St PMem) : St PMem :=
  (PMem.set (PMem.set s.1 (.vec d) (thV d).name θ₀) .nat cnt.name 0, s.2)

/-- The initialization block, derived by two **[Assn]** and one **[Seq]**. -/
theorem tderiv_initR {α : ℝ} (θ₀ : EuclideanSpace ℝ (Fin d))
    (Q : St PMem × St PMem → Prop) (ψ : St PMem × St PMem → ℝ≥0∞) :
    TDeriv (M := PMem) α
      (fun s => Q (initFR d θ₀ s.1, initFR d θ₀ s.2))
      (fun s => ψ (initFR d θ₀ s.1, initFR d θ₀ s.2))
      (Cmd.seq (Cmd.assign (thV d) (Expr.cst θ₀)) (Cmd.assign cnt (Expr.cst (0 : ℕ))))
      (Cmd.seq (Cmd.assign (thV d) (Expr.cst θ₀)) (Cmd.assign cnt (Expr.cst (0 : ℕ))))
      Q ψ :=
  TDeriv.seq
    (TDeriv.assign (thV d) (Expr.cst θ₀) (thV d) (Expr.cst θ₀)
      (fun s => Q ((PMem.set s.1.1 .nat cnt.name 0, s.1.2),
                   (PMem.set s.2.1 .nat cnt.name 0, s.2.2)))
      (fun s => ψ ((PMem.set s.1.1 .nat cnt.name 0, s.1.2),
                   (PMem.set s.2.1 .nat cnt.name 0, s.2.2))))
    (TDeriv.assign cnt (Expr.cst (0 : ℕ)) cnt (Expr.cst (0 : ℕ)) Q ψ)

end InitR

end DPSGDPaper
