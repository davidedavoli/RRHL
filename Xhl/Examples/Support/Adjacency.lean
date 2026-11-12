import Mathlib.Logic.Basic

/-!
# Add/remove adjacency

The adjacency of every case study (§5.1.1): `D ≃_j D'` when the datasets agree off record
`j` and record `j` is `⊥` in one of them.  A dataset is read through `rec : τ → ι → Option X`,
with `none` for `⊥`.  `AdjAt` fixes the order (record `j` is `⊥` in `D₂`); `AdjAtSym`, the
relation the headline theorems take, allows either order.
-/

namespace Continuous

universe u v w

variable {τ : Type u} {ι : Type v} {X : Type w}

/-- **Add/remove adjacency at record `j`**: the datasets agree off `j`, and record `j` is
    `⊥` in `D₂`. -/
def AdjAt (rec : τ → ι → Option X) (j : ι) (D₁ D₂ : τ) : Prop :=
  (∀ t, t ≠ j → rec D₁ t = rec D₂ t) ∧ rec D₂ j = none

/-- **Add/remove adjacency at record `j`, in either order**: the datasets agree off `j`,
    and record `j` is `⊥` in one of them. -/
def AdjAtSym (rec : τ → ι → Option X) (j : ι) (D₁ D₂ : τ) : Prop :=
  AdjAt rec j D₁ D₂ ∨ AdjAt rec j D₂ D₁

variable {rec : τ → ι → Option X} {j : ι} {D₁ D₂ : τ}

lemma AdjAtSym.symm (h : AdjAtSym rec j D₁ D₂) : AdjAtSym rec j D₂ D₁ :=
  Or.symm h

/-- Datasets adjacent at `j`, in either order, agree off `j`. -/
lemma AdjAtSym.agree (h : AdjAtSym rec j D₁ D₂) (t : ι) (ht : t ≠ j) :
    rec D₁ t = rec D₂ t :=
  h.elim (fun h => h.1 t ht) (fun h => (h.1 t ht).symm)

end Continuous
