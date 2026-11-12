import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Order.OmegaCompletePartialOrder

open ENNReal OmegaCompletePartialOrder Classical

namespace DStd

/-!
# Discrete sub-probability distributions

`Distr α`: a mass function `α → ℝ≥0∞` with sum at most 1, and its marginals.  The discrete
development in namespace `DStd` supports the discrete duality theorem
(`Xhl/Duality/Discrete/RenyiDualityGen.lean`), the first step of Theorem C.1.
-/

open ENNReal OmegaCompletePartialOrder Classical

/-- A sub-probability distribution over a type `α`. -/
@[ext]
structure Distr (α : Type) where
  /-- The mass of each element. -/
  mass : α → ℝ≥0∞
  /-- Total mass is at most 1. -/
  le_one : ∑' x, mass x ≤ 1

namespace Distr

variable {α β γ : Type}

/-- The image of a distribution under a function. -/
noncomputable def margin [DecidableEq β] (f : α → β) (d : Distr α) : Distr β where
  mass b := ∑' a, if f a = b then d.mass a else 0
  le_one := by
    have h : ∑' b, ∑' a, (if f a = b then d.mass a else 0) = ∑' a, d.mass a := by
      rw [ENNReal.tsum_comm]
      apply tsum_congr
      intro a
      rw [tsum_eq_single (f a) (fun b hb => by simp [Ne.symm hb])]
      simp
    rw [h]
    exact d.le_one

/-- First marginal. -/
noncomputable def fst (d : Distr (α × β)) : Distr α := d.margin Prod.fst

/-- Second marginal. -/
noncomputable def snd (d : Distr (α × β)) : Distr β := d.margin Prod.snd

end Distr

end DStd
