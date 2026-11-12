import Xhl.Logic.Equiv.Frame
import Xhl.Logic.Rrhl.Rrhl
import Xhl.Examples.Filter.ReleasePrograms

open Continuous

/-!
# Rényi filters: round-counter frame lemmas

The round counter `t` is untouched by the record step and preserves the invariant and the
budget of the derivation (`Deriv.lean`) across its own updates.
-/

open MeasureTheory ProbabilityTheory ENNReal
open scoped NNReal

variable {ident : Type} {M : MemType ident}

namespace RenyiFilter

open Continuous

variable {d e n : ℕ} {τ : Ty}

/-- A predicate on memories, with the round counter at `k` on both sides. -/
def withT (tv : Vars ident .nat) (A : M.heap × M.heap → Prop) (k : ℕ) (m : M.heap × M.heap) :
    Prop :=
  A m ∧ fT tv m.1 = k ∧ fT tv m.2 = k
variable {p : TapParams d e n τ} {v : TapVars ident d n τ} {tv : Vars ident .nat}

/-! ## The round counter -/

lemma PreT_set_t (htv : TvOKT v tv) {j : ℕ} (m : M.heap × M.heap)
    (hm : PreT p v j m) (a b : ℕ) :
    PreT p v j (M.set m.1 .nat tv.name a, M.set m.2 .nat tv.name b) := by
  obtain ⟨hadj, hx, hs, ⟨hq1, hq2⟩, hr0, hrB⟩ := hm
  have gs : ∀ (h : M.heap) (w : ℕ), tapS v (M.set h .nat tv.name w) = tapS v h :=
    fun h w => get_set_other _ _ htv.s
  have gx : ∀ (h : M.heap) (w : ℕ), tapX v (M.set h .nat tv.name w) = tapX v h :=
    fun h w => get_set_other _ _ htv.x
  have gd : ∀ (h : M.heap) (w : ℕ), tapD v (M.set h .nat tv.name w) = tapD v h :=
    fun h w => get_set_other _ _ htv.D
  have hr : remP p v j (M.set m.1 .nat tv.name a, M.set m.2 .nat tv.name b) = remP p v j m :=
    remP_congr (gs _ _) (gs _ _)
  refine ⟨?_, ?_, ?_, ⟨fun hn => ?_, fun hn => ?_⟩, by rw [hr]; exact hr0, by rw [hr]; exact hrB⟩
  · show AdjAtSym p.record j (tapD v _) (tapD v _); rw [gd, gd]; exact hadj
  · show tapX v _ = tapX v _; rw [gx, gx]; exact hx
  · intro k hk; show tapS v _ k = tapS v _ k; rw [gs, gs]; exact hs k hk
  · show remAt (tapS v _) j = 0; rw [gs]; exact hq1 (by rw [← gd m.1 a]; exact hn)
  · show remAt (tapS v _) j = 0; rw [gs]; exact hq2 (by rw [← gd m.2 b]; exact hn)

lemma wEndT_set_t (htv : TvOKT v tv) {α : ℝ} {j : ℕ} (m : M.heap × M.heap) (a b : ℕ) :
    wEndT p v α j (M.set m.1 .nat tv.name a, M.set m.2 .nat tv.name b) = wEndT p v α j m := by
  have gs : ∀ (h : M.heap) (w : ℕ), tapS v (M.set h .nat tv.name w) = tapS v h :=
    fun h w => get_set_other _ _ htv.s
  show ENNReal.ofReal (Real.exp ((α - 1) *
      (cT p α * remP p v j (M.set m.1 .nat tv.name a, M.set m.2 .nat tv.name b))))
    = ENNReal.ofReal (Real.exp ((α - 1) * (cT p α * remP p v j m)))
  rw [remP_congr (gs _ _) (gs _ _)]

lemma fT_stepMapT (htv : TvOKT v tv) (a : M.heap) :
    fT tv (stepMapT p v a) = fT tv a := by
  unfold stepMapT fT
  simp only
  rw [get_set_other _ _ (Ne.symm htv.i), get_set_other _ _ (Ne.symm htv.s),
    get_set_other _ _ (Ne.symm htv.acc)]

end RenyiFilter
