import Xhl.Examples.Support.GaussVec

open Continuous

/-!
# Tree aggregation: the path count

The binary-tree mechanism (Kairouz et al.) releases one Gaussian per node of the depth-`k`
tree, centred at the gradient sum over the node's dyadic interval.  A leaf lies in exactly
`k + 1` node intervals (`tree_path_count`), which gives the column norm of the tree encoder
(`colNormSq_tree`, `Support.lean`) used in the comparison of Appendix D.4.

Node `(ℓ, j)`, with `ℓ ≤ k` and `j < 2^{k−ℓ}`, covers `[j·2^ℓ, (j+1)·2^ℓ)`.
-/

open Finset MeasureTheory ProbabilityTheory ENNReal Real
open scoped NNReal ENNReal

namespace DPFTRL

open Continuous

variable {k : ℕ}

/-- A node of the depth-`k` complete binary tree: level `ℓ ≤ k` and position `j < 2^{k−ℓ}`. -/
abbrev TNode (k : ℕ) : Type := Σ ℓ : Fin (k + 1), Fin (2 ^ (k - (ℓ : ℕ)))

/-- Node `(ℓ, j)` (dyadic interval `[j·2^ℓ, (j+1)·2^ℓ)`) contains leaf `t` iff `j = t / 2^ℓ`. -/
def tcontains (t : ℕ) (p : TNode k) : Prop := (p.2 : ℕ) = t / 2 ^ (p.1 : ℕ)

instance (t : ℕ) (p : TNode k) : Decidable (tcontains t p) := by
  unfold tcontains; infer_instance

/-- For a leaf `t < 2^k`, its containing position at level `ℓ` is in range. -/
lemma tstar_div_lt {k t : ℕ} (ht : t < 2 ^ k) (ℓ : Fin (k + 1)) :
    t / 2 ^ (ℓ : ℕ) < 2 ^ (k - (ℓ : ℕ)) := by
  have hle : (ℓ : ℕ) ≤ k := Nat.lt_succ_iff.mp ℓ.2
  rw [Nat.div_lt_iff_lt_mul (by positivity : 0 < 2 ^ (ℓ : ℕ))]
  calc t < 2 ^ k := ht
    _ = 2 ^ (k - (ℓ : ℕ)) * 2 ^ (ℓ : ℕ) := by rw [← pow_add, Nat.sub_add_cancel hle]

/-- The number of tree nodes whose interval contains a fixed leaf `t < 2^k` is `k + 1`: one
    per level, on the root-to-leaf path. -/
theorem tree_path_count (k t : ℕ) (ht : t < 2 ^ k) :
    ((Finset.univ : Finset (TNode k)).filter (tcontains t)).card = k + 1 := by
  -- the containing nodes are the image of the injective `ℓ ↦ (ℓ, t/2^ℓ)`
  classical
  set φ : Fin (k + 1) → TNode k :=
    fun ℓ => ⟨ℓ, ⟨t / 2 ^ (ℓ : ℕ), tstar_div_lt ht ℓ⟩⟩ with hφ
  have hφinj : Function.Injective φ := by
    intro a b hab
    have h1 : (φ a).1 = (φ b).1 := by rw [hab]
    simpa [hφ] using h1
  have hset : (Finset.univ : Finset (TNode k)).filter (tcontains t)
      = (Finset.univ : Finset (Fin (k + 1))).image φ := by
    ext p
    simp only [mem_filter, mem_univ, true_and, mem_image]
    constructor
    · intro hp
      refine ⟨p.1, ?_⟩
      obtain ⟨ℓ, j⟩ := p
      simp only [tcontains] at hp
      exact Sigma.ext rfl (heq_of_eq (Fin.ext hp.symm))
    · rintro ⟨ℓ, rfl⟩
      rfl
  rw [hset, Finset.card_image_of_injective _ hφinj]
  exact Finset.card_fin (k + 1)

end DPFTRL
