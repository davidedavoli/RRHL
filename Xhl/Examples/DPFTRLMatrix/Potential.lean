import Xhl.Examples.DPFTRLMatrix.Support

/-!
# DP-FTRL: the state-dependent budget of the matrix mechanism

The quantitative invariant `Φ_k` of §5.3, as the potential `potW P f`: the largest Gaussian
cost of the pending aggregates `P`, over the history differences that respect the per-slot
slack of record `j` and agree with the written history on the first `f` slots.  It starts at
`sensW` (`potW_start`), only shrinks when a slot is written (`potW_setH_le`), splits exactly
at a release into the release's cost and the rest (`potW_release`), and ends at `1`
(`one_le_potW_empty`).

The sensitivity `sens_j = sup_{U ∈ 𝒰_j} ∑_r ‖(C·U)_r‖²` is `sensSq`, and
`sensW = exp(α(α−1)·sens_j/2σ²)` (`sensW_eq_gaussB_sensSq`).  It is bounded by the row gaps
(`sensSq_le_relGap`), and equals `Γ²‖∑_{t ∈ P_j} C_{·,t}‖²` for `0/1` participation when
`CᵀC ≥ 0` entrywise (`sensSq_eq_patNormSq`).
-/

open Continuous MeasureTheory ProbabilityTheory ENNReal
open scoped NNReal

variable {ident : Type} {M : MemType ident}

namespace DPFTRL

open Continuous

variable {d e n T R : ℕ} {τ : Ty}

/-- The Gaussian budget of a squared shift. -/
noncomputable def gaussB (α : ℝ) (σ2 : ℝ≥0) (x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (α * (α - 1) * x / (2 * (σ2 : ℝ))))

lemma gaussB_add (α : ℝ) (σ2 : ℝ≥0) (x y : ℝ) :
    gaussB α σ2 (x + y) = gaussB α σ2 x * gaussB α σ2 y := by
  unfold gaussB
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 2; ring

lemma gaussB_zero (α : ℝ) (σ2 : ℝ≥0) : gaussB α σ2 0 = 1 := by simp [gaussB]

lemma gaussB_ne_zero (α : ℝ) (σ2 : ℝ≥0) (x : ℝ) : gaussB α σ2 x ≠ 0 :=
  ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))

lemma gaussB_mono {α : ℝ} (hα : 1 < α) (σ2 : ℝ≥0) {x y : ℝ} (h : x ≤ y) :
    gaussB α σ2 x ≤ gaussB α σ2 y :=
  ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left h (mul_nonneg (by linarith) (by linarith))) (by positivity)))

/-- The squared shifts `∑_{r ∈ P} ‖(C·D)_r‖²` of the rows `P` under history differences `D`. -/
noncomputable def shiftSq (C : Fin R → Fin T → ℝ) (P : Finset (Fin R))
    (D : Fin T → EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∑ r ∈ P, ‖∑ s, C r s • D s‖ ^ 2

/-- **Admissible history differences**: within the per-slot slack `|part(j,s)|·Γ` of the
    differing record `j`, and equal to `Δ` on the first `f` slots. -/
def AdmD (p : TParams d e n T R τ) (j f : ℕ) (Δ D : Fin T → EuclideanSpace ℝ (Fin d)) : Prop :=
  (∀ s, ‖D s‖ ≤ |p.part j s| * p.Cl) ∧ ∀ s : Fin T, (s : ℕ) < f → D s = Δ s

/-- The aggregates still to release at step `ρ` of round `k`: those completed later, and
    those of round `k` from `ρ` on. -/
noncomputable def pend (p : TParams d e n T R τ) (k ρ : ℕ) : Finset (Fin R) :=
  Finset.univ.filter fun r => k < doneN p r ∨ (doneN p r = k ∧ ρ ≤ (r : ℕ))

/-- The history differences `H₂ − H₁` of a pair of memories, slot by slot. -/
noncomputable def hDiff (v : TVars ident d T R τ) (m : M.heap × M.heap) :
    Fin T → EuclideanSpace ℝ (Fin d) :=
  fun s => blk (tH v m.2) s - blk (tH v m.1) s

/-- **The potential**: the largest Gaussian cost of the rows `P`, over every admissible
    completion of the history written on the first `f` slots. -/
noncomputable def potW (p : TParams d e n T R τ) (α : ℝ) (j : ℕ) (P : Finset (Fin R)) (f : ℕ)
    (v : TVars ident d T R τ) (m : M.heap × M.heap) : ℝ≥0∞ :=
  ⨆ (D : Fin T → EuclideanSpace ℝ (Fin d)) (_ : AdmD p j f (hDiff v m) D),
    gaussB α p.σ2 (shiftSq p.C P D)

/-- **The budget of the whole run**: the supremum of `exp(α(α−1)‖C·D‖²_F/2σ²)` over the
    history differences `D` within the slack of record `j`. -/
noncomputable def sensW (p : TParams d e n T R τ) (α : ℝ) (j : ℕ) : ℝ≥0∞ :=
  ⨆ (D : Fin T → EuclideanSpace ℝ (Fin d)) (_ : ∀ s, ‖D s‖ ≤ |p.part j s| * p.Cl),
    gaussB α p.σ2 (shiftSq p.C Finset.univ D)

variable {p : TParams d e n T R τ} {v : TVars ident d T R τ}

/-! ## The potential reads the history alone -/

lemma potW_congr {α : ℝ} {j : ℕ} {P : Finset (Fin R)} {f : ℕ} {m m' : M.heap × M.heap}
    (h : hDiff v m' = hDiff v m) : potW p α j P f v m' = potW p α j P f v m := by
  unfold potW; rw [h]

/-- An assignment to another variable than the history leaves the potential unchanged. -/
lemma potW_set_other {α : ℝ} {j : ℕ} {P : Finset (Fin R)} {f : ℕ} {ty : Ty} {x : ident}
    (hx : x ≠ v.H.name) (m : M.heap × M.heap) (a b : ty.interp) :
    potW p α j P f v (M.set m.1 ty x a, M.set m.2 ty x b) = potW p α j P f v m := by
  refine potW_congr (funext fun s => ?_)
  simp only [hDiff, tH, get_set_other _ _ hx]

/-- With nothing written, the potential does not depend on the memories. -/
lemma potW_zero {α : ℝ} {j : ℕ} (P : Finset (Fin R)) (m : M.heap × M.heap) :
    potW p α j P 0 v m
      = ⨆ (D : Fin T → EuclideanSpace ℝ (Fin d)) (_ : ∀ s, ‖D s‖ ≤ |p.part j s| * p.Cl),
          gaussB α p.σ2 (shiftSq p.C P D) := by
  unfold potW AdmD
  refine iSup_congr fun D => ?_
  exact iSup_congr_Prop ⟨fun h => h.1, fun h => ⟨h, fun s hs => absurd hs (Nat.not_lt_zero _)⟩⟩
    fun _ => rfl

/-! ## Writing a slot -/

/-- **Writing slot `k` only shrinks the admissible set**: if the first `k` slots are
    unchanged, the potential with `k + 1` slots written is at most the one with `k`. -/
lemma potW_setH_le {α : ℝ} {j : ℕ} {P : Finset (Fin R)} {k : ℕ} {m m' : M.heap × M.heap}
    (h : ∀ s : Fin T, (s : ℕ) < k → hDiff v m' s = hDiff v m s) :
    potW p α j P (k + 1) v m' ≤ potW p α j P k v m :=
  iSup₂_le fun D hD => le_iSup₂_of_le (f := fun D (_ : AdmD p j k (hDiff v m) D) =>
    gaussB α p.σ2 (shiftSq p.C P D)) D
    ⟨hD.1, fun s hs => (hD.2 s (Nat.lt_succ_of_lt hs)).trans (h s hs)⟩ le_rfl

/-! ## A release -/

/-- A row reads only the slots up to its completion round. -/
lemma le_doneN {r : Fin R} {s : Fin T} (hC : p.C r s ≠ 0) : (s : ℕ) ≤ doneN p r := by
  classical
  have h := Finset.le_sup (f := fun s : Fin T => if p.C r s = 0 then 0 else (s : ℕ))
    (Finset.mem_univ s)
  simp only [if_neg hC] at h
  exact h

/-- **A release splits the potential exactly**: if row `r` is the one released at step
    `ρ = r` of its completion round `k`, all the slots it reads are written, so its shift is
    the actual `(C·(H₂ − H₁))_r`, paid now, and the rest is the potential of the other rows. -/
lemma potW_release {α : ℝ} {j k : ℕ} {r : Fin R} (hdone : doneN p r = k)
    (m : M.heap × M.heap) :
    gaussB α p.σ2 (‖∑ s, p.C r s • hDiff v m s‖ ^ 2) * potW p α j (pend p k (r + 1)) (k + 1) v m
      ≤ potW p α j (pend p k r) (k + 1) v m := by
  have hins : pend p k r = insert r (pend p k (r + 1)) := by
    ext r'
    simp only [pend, Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro (h | ⟨h1, h2⟩)
      · exact Or.inr (Or.inl h)
      · rcases eq_or_ne r' r with rfl | hne
        · exact Or.inl rfl
        · exact Or.inr (Or.inr ⟨h1, by
            have : (r' : ℕ) ≠ r := fun h => hne (Fin.ext h)
            omega⟩)
    · rintro (rfl | h | ⟨h1, h2⟩)
      · exact Or.inr ⟨hdone, le_rfl⟩
      · exact Or.inl h
      · exact Or.inr ⟨h1, by omega⟩
  have hnot : r ∉ pend p k (r + 1) := by
    simp only [pend, Finset.mem_filter, Finset.mem_univ, true_and, not_or, not_and]
    exact ⟨by omega, fun _ => by omega⟩
  unfold potW
  rw [ENNReal.mul_iSup]
  refine iSup_mono fun D => ?_
  rw [ENNReal.mul_iSup]
  refine iSup_mono fun hD => le_of_eq ?_
  have hrow : ∑ s, p.C r s • D s = ∑ s, p.C r s • hDiff v m s := by
    refine Finset.sum_congr rfl fun s _ => ?_
    by_cases hC : p.C r s = 0
    · simp [hC]
    · rw [hD.2 s (by have := le_doneN hC; omega)]
  rw [← gaussB_add, hins]
  unfold shiftSq
  rw [Finset.sum_insert hnot, hrow]

/-- A step `ρ` that releases nothing leaves the pending rows unchanged. -/
lemma pend_succ_of_not_due {k ρ : ℕ} (h : ∀ r : Fin R, (r : ℕ) = ρ → doneN p r ≠ k) :
    pend p k (ρ + 1) = pend p k ρ := by
  ext r
  simp only [pend, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (h1 | ⟨h1, h2⟩)
    · exact Or.inl h1
    · exact Or.inr ⟨h1, by omega⟩
  · rintro (h1 | ⟨h1, h2⟩)
    · exact Or.inl h1
    · refine Or.inr ⟨h1, ?_⟩
      rcases Nat.lt_or_ge ρ r with hlt | hge
      · omega
      · exact absurd h1 (h r (by omega))

/-- The rows pending after the last step of round `k` are those pending at round `k + 1`. -/
lemma pend_round (k : ℕ) : pend p k R = pend p (k + 1) 0 := by
  ext r
  simp only [pend, Finset.mem_filter, Finset.mem_univ, true_and]
  have := r.2
  omega

lemma pend_zero : pend p 0 0 = Finset.univ := by
  ext r; simp only [pend, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]; omega

lemma pend_end [NeZero T] : pend p T 0 = ∅ := by
  ext r
  simp only [pend, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
    iff_false, not_or, not_and]
  have := doneN_lt (p := p) r
  exact ⟨by omega, fun h => by omega⟩

/-! ## The end of the run, and the start -/

/-- The actual history difference is admissible when it meets the slack. -/
lemma admD_hDiff {j f : ℕ} {m : M.heap × M.heap}
    (h : ∀ s, ‖blk (tH v m.1) s - blk (tH v m.2) s‖ ≤ |p.part j s| * p.Cl) :
    AdmD p j f (hDiff v m) (hDiff v m) :=
  ⟨fun s => by rw [hDiff, norm_sub_rev]; exact h s, fun _ _ => rfl⟩

/-- With no row pending, and the actual history within the slack, the potential is at
    least `1`. -/
lemma one_le_potW_empty {α : ℝ} {j f : ℕ} {m : M.heap × M.heap}
    (h : ∀ s, ‖blk (tH v m.1) s - blk (tH v m.2) s‖ ≤ |p.part j s| * p.Cl) :
    1 ≤ potW p α j ∅ f v m :=
  le_iSup₂_of_le (f := fun D (_ : AdmD p j f (hDiff v m) D) =>
    gaussB α p.σ2 (shiftSq p.C ∅ D)) (hDiff v m) (admD_hDiff h)
    (by simp [shiftSq, gaussB_zero])

/-- Within the slack, the potential is not `0`. -/
lemma potW_ne_zero {α : ℝ} {j f : ℕ} {P : Finset (Fin R)} {m : M.heap × M.heap}
    (h : ∀ s, ‖blk (tH v m.1) s - blk (tH v m.2) s‖ ≤ |p.part j s| * p.Cl) :
    potW p α j P f v m ≠ 0 :=
  ne_of_gt (lt_of_lt_of_le (pos_iff_ne_zero.mpr (gaussB_ne_zero α p.σ2 _))
    (le_iSup₂_of_le (f := fun D (_ : AdmD p j f (hDiff v m) D) =>
      gaussB α p.σ2 (shiftSq p.C P D)) (hDiff v m) (admD_hDiff h) le_rfl))

/-- At the start of the run, the potential is the budget `sensW`. -/
lemma potW_start {α : ℝ} {j : ℕ} (m : M.heap × M.heap) :
    potW p α j (pend p 0 0) 0 v m = sensW p α j := by
  rw [potW_zero, pend_zero]; rfl

/-! ## The row-by-row triangle inequality -/

/-- The row-by-row triangle inequality: within the slack, `‖C·D‖²_F ≤ ∑_r gap_r²`. -/
lemma shiftSq_le_relGap {j : ℕ} {D : Fin T → EuclideanSpace ℝ (Fin d)}
    (hD : ∀ s, ‖D s‖ ≤ |p.part j s| * p.Cl) :
    shiftSq p.C Finset.univ D ≤ ∑ r, relGap p j r ^ 2 := by
  refine Finset.sum_le_sum fun r _ => ?_
  refine pow_le_pow_left₀ (norm_nonneg _) ((norm_sum_le _ _).trans
    (Finset.sum_le_sum fun s _ => ?_)) 2
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (hD s) (abs_nonneg _)

/-! ## The sensitivity `sens_j`, and the budget as its Gaussian cost -/

/-- **The sensitivity of record `j`** (§5.3): `sens_j = sup_D ∑_r ‖(C·D)_r‖²` over the history
    differences with `‖D_s‖ ≤ |part(j,s)|·Γ`.  A supremum in `ℝ`, bounded by
    `shiftSq_le_relGap`. -/
noncomputable def sensSq (p : TParams d e n T R τ) (j : ℕ) : ℝ :=
  ⨆ D : {D : Fin T → EuclideanSpace ℝ (Fin d) // ∀ s, ‖D s‖ ≤ |p.part j s| * p.Cl},
    shiftSq p.C Finset.univ D.1

lemma sensSq_bddAbove (j : ℕ) :
    BddAbove (Set.range fun D : {D : Fin T → EuclideanSpace ℝ (Fin d) //
      ∀ s, ‖D s‖ ≤ |p.part j s| * p.Cl} => shiftSq p.C Finset.univ D.1) :=
  ⟨_, Set.forall_mem_range.2 fun D => shiftSq_le_relGap D.2⟩

lemma sensSq_nonempty (hC : 0 ≤ p.Cl) (j : ℕ) :
    Nonempty {D : Fin T → EuclideanSpace ℝ (Fin d) // ∀ s, ‖D s‖ ≤ |p.part j s| * p.Cl} :=
  ⟨⟨0, fun s => by rw [Pi.zero_apply, norm_zero]; exact mul_nonneg (abs_nonneg _) hC⟩⟩

/-- Every admissible history difference shifts by at most the sensitivity. -/
lemma shiftSq_le_sensSq {j : ℕ} {D : Fin T → EuclideanSpace ℝ (Fin d)}
    (hD : ∀ s, ‖D s‖ ≤ |p.part j s| * p.Cl) : shiftSq p.C Finset.univ D ≤ sensSq p j :=
  le_ciSup (f := fun D : {D : Fin T → EuclideanSpace ℝ (Fin d) //
    ∀ s, ‖D s‖ ≤ |p.part j s| * p.Cl} => shiftSq p.C Finset.univ D.1)
    (sensSq_bddAbove j) ⟨D, hD⟩

/-- **The triangle bound on the sensitivity**: `sens_j ≤ ∑_r gap_{j,r}²`, the bound that
    Proposition D.5 evaluates. -/
lemma sensSq_le_relGap (j : ℕ) : sensSq p j ≤ ∑ r, relGap p j r ^ 2 :=
  Real.iSup_le (fun D => shiftSq_le_relGap D.2) (Finset.sum_nonneg fun _ _ => sq_nonneg _)

lemma continuous_gaussB (α : ℝ) (σ2 : ℝ≥0) : Continuous (gaussB α σ2) :=
  ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp
    ((continuous_const.mul continuous_id).div_const _))

/-- **The budget is the Gaussian cost of the sensitivity**: `sensW = exp(α(α−1)·sens_j/2σ²)`.
    The supremum passes through `x ↦ exp(α(α−1)x/2σ²)`, which is monotone and continuous. -/
theorem sensW_eq_gaussB_sensSq {α : ℝ} (hα : 1 < α) (hC : 0 ≤ p.Cl) (j : ℕ) :
    sensW p α j = gaussB α p.σ2 (sensSq p j) := by
  have := sensSq_nonempty (p := p) hC j
  rw [sensSq, Monotone.map_ciSup_of_continuousAt (continuous_gaussB α p.σ2).continuousAt
    (fun _ _ h => gaussB_mono hα _ h) (sensSq_bddAbove j), sensW, iSup_subtype']

/-- The Gram sensitivity of record `j`: `∑_{s,s'} |(CᵀC)_{s,s'}|·|part(j,s)|Γ·|part(j,s')|Γ`. -/
noncomputable def gramSq (p : TParams d e n T R τ) (j : ℕ) : ℝ :=
  ∑ s, ∑ s', |∑ r, p.C r s * p.C r s'| * (|p.part j s| * p.Cl * (|p.part j s'| * p.Cl))

/-- **The Gram bound**: `‖C·D‖²_F = ∑_{s,s'} (CᵀC)_{s,s'} ⟨D_s, D_{s'}⟩`, so with
    `‖D_s‖ ≤ b_s` it is at most `∑_{s,s'} |(CᵀC)_{s,s'}| b_s b_{s'}`. -/
lemma shiftSq_le_gram (C : Fin R → Fin T → ℝ) (D : Fin T → EuclideanSpace ℝ (Fin d))
    (b : Fin T → ℝ) (hb : ∀ s, ‖D s‖ ≤ b s) :
    shiftSq C Finset.univ D ≤ ∑ s, ∑ s', |∑ r, C r s * C r s'| * (b s * b s') := by
  have hexp : ∀ r, ‖∑ s, C r s • D s‖ ^ 2
      = ∑ s, ∑ s', C r s * C r s' * inner ℝ (D s) (D s') := by
    intro r
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [inner_sum]
    refine Finset.sum_congr rfl fun s' _ => ?_
    rw [inner_smul_left, inner_smul_right]
    simp only [conj_trivial]; ring
  unfold shiftSq
  simp_rw [hexp]
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun s _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun s' _ => ?_
  rw [← Finset.sum_mul]
  have hb0 : ∀ s, 0 ≤ b s := fun s => (norm_nonneg _).trans (hb s)
  calc (∑ r, C r s * C r s') * inner ℝ (D s) (D s')
      ≤ |∑ r, C r s * C r s'| * |inner ℝ (D s) (D s')| := by
        rw [← abs_mul]; exact le_abs_self _
    _ ≤ |∑ r, C r s * C r s'| * (‖D s‖ * ‖D s'‖) :=
        mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (abs_nonneg _)
    _ ≤ |∑ r, C r s * C r s'| * (b s * b s') :=
        mul_le_mul_of_nonneg_left (mul_le_mul (hb s) (hb s') (norm_nonneg _) (hb0 s))
          (abs_nonneg _)

/-- Aligned differences `D_s = b_s·e` along one unit vector shift row `r` by `(C·b)_r·e`:
    `‖C·D‖²_F = ‖C·b‖²`. -/
lemma shiftSq_aligned_rows (C : Fin R → Fin T → ℝ) (b : Fin T → ℝ)
    (e : EuclideanSpace ℝ (Fin d)) (he : ‖e‖ = 1) :
    shiftSq C Finset.univ (fun s => b s • e) = ∑ r, (∑ s, C r s * b s) ^ 2 := by
  refine Finset.sum_congr rfl fun r _ => ?_
  have : ∑ s, C r s • (b s • e) = (∑ s, C r s * b s) • e := by
    rw [Finset.sum_smul]; exact Finset.sum_congr rfl fun s _ => by rw [smul_smul]
  rw [this, norm_smul, he, mul_one, Real.norm_eq_abs, sq_abs]

/-- Aligned differences `D_s = b_s·e` along one unit vector reach the Gram form exactly:
    `‖C·D‖²_F = ∑_{s,s'} (CᵀC)_{s,s'} b_s b_{s'}`. -/
lemma shiftSq_aligned (C : Fin R → Fin T → ℝ) (b : Fin T → ℝ)
    (e : EuclideanSpace ℝ (Fin d)) (he : ‖e‖ = 1) :
    shiftSq C Finset.univ (fun s => b s • e)
      = ∑ s, ∑ s', (∑ r, C r s * C r s') * (b s * b s') := by
  rw [shiftSq_aligned_rows C b e he]
  simp_rw [sq, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s' _ => ?_
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun r _ => by ring

/-- **The Gram bound on the sensitivity**: `sens_j ≤ ∑_{s,s'} |(CᵀC)_{s,s'}| π_s π_{s'} Γ²`,
    with `π_s = |part(j,s)|`, for every encoder and participation schedule. -/
lemma sensSq_le_gram (hCl : 0 ≤ p.Cl) (j : ℕ) : sensSq p j ≤ gramSq p j := by
  have := sensSq_nonempty (p := p) hCl j
  exact ciSup_le fun D => shiftSq_le_gram p.C D.1 _ D.2

/-- Aligned differences `D_s = π_sΓ·e` are admissible: they meet the slack exactly. -/
lemma aligned_adm (hCl : 0 ≤ p.Cl) (j : ℕ) {e : EuclideanSpace ℝ (Fin d)} (he : ‖e‖ = 1)
    (s : Fin T) : ‖(|p.part j s| * p.Cl) • e‖ ≤ |p.part j s| * p.Cl := by
  rw [norm_smul, he, mul_one, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (abs_nonneg _) hCl)]

/-- Under a nonnegative Gram matrix the Gram form is the shift of the aligned differences. -/
lemma gramSq_eq_aligned (hG : ∀ s s', 0 ≤ ∑ r, p.C r s * p.C r s') (j : ℕ)
    {e : EuclideanSpace ℝ (Fin d)} (he : ‖e‖ = 1) :
    gramSq p j = shiftSq p.C Finset.univ (fun s => (|p.part j s| * p.Cl) • e) := by
  rw [shiftSq_aligned p.C _ e he]
  unfold gramSq
  exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun s' _ => by
    rw [abs_of_nonneg (hG s s')]

/-- For `0/1` participation on `pat`, the aligned differences shift by
    `Γ²‖∑_{t ∈ pat} C_{·,t}‖²`. -/
lemma shiftSq_aligned_pat {j : ℕ} (pat : Finset (Fin T))
    (hpart : ∀ s : Fin T, p.part j s = if s ∈ pat then 1 else 0)
    {e : EuclideanSpace ℝ (Fin d)} (he : ‖e‖ = 1) :
    shiftSq p.C Finset.univ (fun s => (|p.part j s| * p.Cl) • e)
      = patNormSq p.C pat * p.Cl ^ 2 := by
  rw [shiftSq_aligned_rows p.C _ e he, patNormSq, Finset.sum_mul]
  refine Finset.sum_congr rfl fun r _ => ?_
  have hrow : ∑ s, p.C r s * (|p.part j s| * p.Cl) = (∑ s ∈ pat, p.C r s) * p.Cl := by
    rw [Finset.sum_mul, ← Fintype.sum_ite_mem pat]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [hpart s]
    split_ifs <;> simp
  rw [hrow, mul_pow]

/-- **`sens_j` under a nonnegative Gram matrix**: when `CᵀC ≥ 0` entrywise (and the model
    has a coordinate), `sens_j = ∑_{s,s'} (CᵀC)_{s,s'} π_s π_{s'} Γ² = Γ²‖C·π‖²`, with
    `π_s = |part(j,s)|`; the supremum is attained by aligning every round's difference along
    one direction. -/
theorem sensSq_eq_gram (hd : 0 < d) (hCl : 0 ≤ p.Cl)
    (hG : ∀ s s', 0 ≤ ∑ r, p.C r s * p.C r s') (j : ℕ) :
    sensSq p j = gramSq p j := by
  set e : EuclideanSpace ℝ (Fin d) := EuclideanSpace.single ⟨0, hd⟩ 1
  have he : ‖e‖ = 1 := by simp [e]
  exact le_antisymm (sensSq_le_gram hCl j)
    ((gramSq_eq_aligned hG j he).trans_le (shiftSq_le_sensSq (aligned_adm hCl j he)))

/-- **Multi-epoch participation, `0/1` on a pattern `P_j`**: when `CᵀC ≥ 0` entrywise,
    `sens_j = Γ²·‖∑_{t ∈ P_j} C_{·,t}‖²` (`patNormSq`), as used in the comparison with
    Choquette-Choo et al. (Appendix D.4). -/
theorem sensSq_eq_patNormSq (hd : 0 < d) (hCl : 0 ≤ p.Cl)
    (hG : ∀ s s', 0 ≤ ∑ r, p.C r s * p.C r s') {j : ℕ} (pat : Finset (Fin T))
    (hpart : ∀ s : Fin T, p.part j s = if s ∈ pat then 1 else 0) :
    sensSq p j = patNormSq p.C pat * p.Cl ^ 2 := by
  set e : EuclideanSpace ℝ (Fin d) := EuclideanSpace.single ⟨0, hd⟩ 1
  have he : ‖e‖ = 1 := by simp [e]
  rw [sensSq_eq_gram hd hCl hG j, gramSq_eq_aligned hG j he, shiftSq_aligned_pat pat hpart he]

end DPFTRL
