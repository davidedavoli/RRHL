import Xhl.Examples.Filter.Support
import Xhl.Examples.DPFTRLMatrix.ReleasePrograms
import Xhl.Examples.DPFTRLMatrix.Tree
import Xhl.Logic.Rrhl.Deriv

open Continuous

/-!
# DP-FTRL with a matrix mechanism: counter invariants and the tree encoder

Support for the derivation of `dpftrlGen` (`ReleasePrograms.lean`): the invariants with the
round and release counters (`ITc`, `RLc`, `RAc`), the frame fact `IT_set_cnt`, and the tree
encoder `treeC` (row `r` sums the dyadic interval of node `r`) with its column norm
`colNormSq_tree = k + 1`, by which tree aggregation is an instance of the same program.
-/

open MeasureTheory ProbabilityTheory ENNReal
open scoped NNReal

variable {ident : Type} {M : MemType ident}

namespace DPFTRL

open Continuous

variable {d e n T R : ℕ} {τ : Ty} [NeZero T] [NeZero R]

variable {p : TParams d e n T R τ} {v : TVars ident d T R τ} {tv rv : Vars ident .nat}

/-! ## Invariants with the counters -/

/-- Between rounds, at round `k`. -/
def ITc (p : TParams d e n T R τ) (v : TVars ident d T R τ) (tv : Vars ident .nat) (j k : ℕ)
    (m : M.heap × M.heap) : Prop :=
  IT p v j m ∧ tT tv m.1 = k ∧ tT tv m.2 = k

/-- In the release loop of round `k`, before release `ρ`. -/
def RLc (p : TParams d e n T R τ) (v : TVars ident d T R τ) (tv rv : Vars ident .nat) (j k ρ : ℕ)
    (m : M.heap × M.heap) : Prop :=
  IT p v j m ∧ tT tv m.1 = k ∧ tT tv m.2 = k ∧ tT rv m.1 = ρ ∧ tT rv m.2 = ρ

/-- After `acc := (B · Y)_t` in round `k`: the invariant, and the two accumulators agree. -/
def RAc (p : TParams d e n T R τ) (v : TVars ident d T R τ) (tv rv : Vars ident .nat) (j k : ℕ)
    (m : M.heap × M.heap) : Prop :=
  RLc p v tv rv j k R m ∧ tA v m.1 = tA v m.2

/-- `IT` does not read the counters. -/
lemma IT_set_cnt {j : ℕ} {x : Vars ident .nat} (hx : x.name ≠ v.x.name) (hD : x.name ≠ v.D.name)
    (hH : x.name ≠ v.H.name) (hY : x.name ≠ v.Y.name) (m : M.heap × M.heap) (hm : IT p v j m)
    (a b : ℕ) : IT p v j (M.set m.1 .nat x.name a, M.set m.2 .nat x.name b) := by
  obtain ⟨hadj, hxe, hy, hHb⟩ := hm
  refine ⟨?_, ?_, ?_, fun s => ?_⟩
  · show AdjAtSym p.record j (tD v _) (tD v _); rw [tD, tD, get_set_other _ _ hD, get_set_other _ _ hD]; exact hadj
  · show tX v _ = tX v _; rw [tX, tX, get_set_other _ _ hx, get_set_other _ _ hx]; exact hxe
  · show tY v _ = tY v _; rw [tY, tY, get_set_other _ _ hY, get_set_other _ _ hY]; exact hy
  · show ‖blk (tH v _) s - blk (tH v _) s‖ ≤ _
    rw [tH, tH, get_set_other _ _ hH, get_set_other _ _ hH]; exact hHb s

/-! ## The tree encoder: tree aggregation as an instance -/

section Tree

variable (k : ℕ)

instance : NeZero (2 ^ k) := ⟨(pow_pos two_pos k).ne'⟩

instance : Nonempty (TNode k) := ⟨⟨0, ⟨0, pow_pos two_pos _⟩⟩⟩

/-- The number of nodes of the depth-`k` binary tree. -/
abbrev nNodes : ℕ := Fintype.card (TNode k)

instance : NeZero (nNodes k) := ⟨Fintype.card_ne_zero⟩

/-- Aggregate `r` is the node `node k r`. -/
noncomputable def node (r : Fin (nNodes k)) : TNode k := (Fintype.equivFin (TNode k)).symm r

/-- The tree encoder: row `r` sums the rounds of the dyadic interval of node `r`. -/
noncomputable def treeC (r : Fin (nNodes k)) (s : Fin (2 ^ k)) : ℝ :=
  if tcontains (s : ℕ) (node k r) then 1 else 0

/-- **The column norm of the tree encoder**: column `s₀` has one entry `1` per node on the
    path from the leaf `s₀` to the root, so `‖C_{·,s₀}‖² = k + 1`. -/
lemma colNormSq_tree (s₀ : Fin (2 ^ k)) : ∑ r, treeC k r s₀ ^ 2 = k + 1 := by
  have hsq : ∀ r, (treeC k r s₀) ^ 2 = if tcontains (s₀ : ℕ) (node k r) then 1 else 0 := by
    intro r; unfold treeC; split_ifs <;> norm_num
  simp_rw [hsq]
  rw [Finset.sum_boole]
  have hcard : ((Finset.univ : Finset (Fin (nNodes k))).filter
      (fun r => tcontains (s₀ : ℕ) (node k r))).card = k + 1 := by
    rw [← tree_path_count k s₀ s₀.2]
    refine Finset.card_equiv (Fintype.equivFin (TNode k)).symm (fun r => ?_)
    rw [Finset.mem_filter, Finset.mem_filter]
    exact ⟨fun h => ⟨Finset.mem_univ _, h.2⟩, fun h => ⟨Finset.mem_univ _, h.2⟩⟩
  rw [hcard]; push_cast; ring

end Tree

end DPFTRL
