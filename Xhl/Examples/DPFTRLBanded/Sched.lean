import Xhl.Examples.DPFTRLBanded.GaussBlocks
import Xhl.Divergence.SubsamplingDomination

open Continuous

/-!
# Slot lifetimes and block budgets of amplified banded DP-FTRL

* `lastB C s` — the last row reading slot `s` (row `r` is released at round `r`);
* `colSq C s m = ∑_{k<m+1, s+k<T} C[s+k, s]²` — the paper's `c_s²` (Appendix D.5) at
  `b = m + 1`, truncated at the end of the run;
* `blockSymBudgetM` — the block budget `max(Υ, Λ)` of the symmetric adjacency, equal to
  `Υ` by `blockSymBudgetM_eq`;
* `gLx` — the clipped per-record gradient.
-/

open MeasureTheory ProbabilityTheory ENNReal
open scoped NNReal


variable {ident : Type} {M : MemType ident}

namespace DPFTRL.Band

open Continuous

variable {d e n T R : ℕ} {τ : Ty} [NeZero T] [NeZero R]

/-! ## Slot lifetimes -/

open scoped Classical in
/-- **The round after which slot `s` of the history is dead**: the last row of the encoder
    reading it — row `r` is released at round `r`. -/
noncomputable def lastB (C : Fin R → Fin T → ℝ) (s : Fin T) : ℕ :=
  Finset.univ.sup fun r : Fin R => if C r s = 0 then 0 else (r : ℕ)

open scoped Classical in
/-- Every row reading slot `s` is released by round `lastB C s`. -/
lemma le_lastB {C : Fin R → Fin T → ℝ} {r : Fin R} {s : Fin T} (h : C r s ≠ 0) :
    (r : ℕ) ≤ lastB C s := by
  have := Finset.le_sup (f := fun r : Fin R => if C r s = 0 then 0 else (r : ℕ))
    (Finset.mem_univ r)
  rwa [if_neg h] at this

omit [NeZero T] in
open scoped Classical in
/-- **Every slot is dead by the end of the run**: the rows are the rounds `0, …, R − 1`. -/
lemma lastB_lt (C : Fin R → Fin T → ℝ) (s : Fin T) : lastB C s < R := by
  rw [lastB, Finset.sup_lt_iff (show (⊥ : ℕ) < R from Nat.pos_of_ne_zero (NeZero.ne R))]
  intro r _
  split_ifs
  · exact Nat.pos_of_ne_zero (NeZero.ne R)
  · exact r.isLt

omit [NeZero T] [NeZero R] in
open scoped Classical in
/-- A bound on the rows reading slot `s` bounds its lifetime. -/
lemma lastB_le {C : Fin R → Fin T → ℝ} {s : Fin T} {b : ℕ}
    (h : ∀ r : Fin R, C r s ≠ 0 → (r : ℕ) ≤ b) : lastB C s ≤ b :=
  Finset.sup_le fun r _ => by
    by_cases hr : C r s = 0
    · rw [if_pos hr]; exact Nat.zero_le _
    · rw [if_neg hr]; exact h r hr

/-! ## Blocks supported on one slot -/

lemma blk_zeroA {K : ℕ} (s : Fin K) : blk (0 : EuclideanSpace ℝ (Fin (K * d))) s = 0 := by
  ext k; simp [blk]

lemma blk_addA {K : ℕ} (H E : EuclideanSpace ℝ (Fin (K * d))) (s : Fin K) :
    blk (H + E) s = blk H s + blk E s := by
  ext k; simp [blk]


/-! ## The block's sensitivity -/

/-- **The block's squared column norm**, the paper's `c_s² = ∑_{k<min(b, T−s)} C_{s+k,s}²`
    at `b = m + 1`: rows past the end of the run (`s + k ≥ T`) read as `0`. -/
noncomputable def colSq (C : Fin T → Fin T → ℝ) (s m : ℕ) : ℝ :=
  ∑ k : Fin (m + 1),
    (if s + (k : ℕ) < T then C (Fin.ofNat T (s + (k : ℕ))) (Fin.ofNat T s) else 0) ^ 2

lemma colSq_nonneg (C : Fin T → Fin T → ℝ) (s m : ℕ) : 0 ≤ colSq C s m :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _


/-! ## The block budget and the clipped gradient -/

section Shared

variable {d e n T R : ℕ} {τ : Ty} [NeZero T] [NeZero R] {q : ℝ≥0}

/-- **The block budget of the symmetric adjacency**: the larger of the two orientations at
    the block's sensitivity `Γ·√(colSq)` — the forward leaf `Υ_α = mixBudgetR` when record
    `j` is absent from the right dataset, the reversed leaf `Λ_α = mixFlipBudgetE` when it is
    absent from the *left* one. -/
noncomputable def blockSymBudgetM (p : TParams d e n T T τ) (q : ℝ≥0) (α : ℝ) (m s : ℕ) :
    ℝ≥0∞ :=
  max (mixBudgetR q (p.Cl * Real.sqrt (colSq p.C s m)) p.σ2 α)
    (mixFlipBudgetE q (p.Cl * Real.sqrt (colSq p.C s m)) p.σ2 α)

/-- **Mironov–Talwar–Zhang** (Lemma D.1): the reversed leaf is dominated by the forward
    one, so the symmetric block budget is `Υ_α`, at every `q ≤ 1`. -/
theorem blockSymBudgetM_eq {α : ℝ} (hα : 1 < α) {p : TParams d e n T T τ} (hσ : p.σ2 ≠ 0)
    (hq : q ≤ 1) (m s : ℕ) :
    blockSymBudgetM p q α m s = mixBudgetR q (p.Cl * Real.sqrt (colSq p.C s m)) p.σ2 α :=
  max_mixBudgetR_mixFlipBudgetE hα (by exact_mod_cast hq) hσ _

/-- The clipped gradient of record `j`, read off a model `x` and a dataset `D`. -/
noncomputable def gLx (p : TParams d e n T R τ) (j : ℕ) (x : EuclideanSpace ℝ (Fin d))
    (D : τ.interp) : EuclideanSpace ℝ (Fin d) :=
  clipV p.Cl (p.grad x (p.record D j))

lemma norm_gLx_le {p : TParams d e n T R τ} (hC : 0 ≤ p.Cl) (j : ℕ)
    (x : EuclideanSpace ℝ (Fin d)) (D : τ.interp) : ‖gLx p j x D‖ ≤ p.Cl := norm_clipV_le hC _

end Shared

end DPFTRL.Band
