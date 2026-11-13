import Xhl.Examples.Support.Clip
import Xhl.Examples.Support.Adjacency
import Xhl.Examples.Support.Participation

open Continuous

/-!
# DP-FTRL with a matrix mechanism: parameters, expressions, invariants

The ingredients of the program of Figure 6 (§5.3): the parameters `TParams` (encoder `C`,
decoder `B`, public participation schedule `part`, clipping norm, noise, regularization),
the variables `TVars`, the round's gradient sum `batchStep`, the aggregate mean `rowMean`,
the decoder `rowDec`, the release schedule `doneN` (a function of `C`), and the relational
invariant `IT`.

The row gaps `relGap p j r = ∑_s |C_{r,s}|·|part(j,s)|·Γ` bound the sensitivity `sens_j`
(`sensSq_le_relGap`, `Potential.lean`); their closed forms for single participation
(`sum_relGap_sq_singleton`) and banded encoders on separated patterns (`sum_relGap_sq_banded`)
are the two claims of Proposition E.5.
-/

open MeasureTheory ProbabilityTheory ENNReal Real
open scoped NNReal

variable {ident : Type} {M : MemType ident}

namespace DPFTRL

open Continuous

/-! ## Blocks -/

section Blocks

/-- `Fin.ofNat` on a value in range. -/
lemma ofNat_eq_of_lt {K : ℕ} [NeZero K] {k : ℕ} (hk : k < K) : Fin.ofNat K k = ⟨k, hk⟩ :=
  Fin.ext (by simp [Fin.val_ofNat, Nat.mod_eq_of_lt hk])


variable {K d : ℕ}

/-- Block `s` of a vector made of `K` blocks of size `d`. -/
noncomputable def blk (H : EuclideanSpace ℝ (Fin (K * d))) (s : Fin K) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun k : Fin d => H (finProdFinEquiv (s, k)))

/-- Replace block `s`. -/
noncomputable def setBlk (H : EuclideanSpace ℝ (Fin (K * d))) (s : Fin K)
    (w : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin (K * d)) :=
  WithLp.toLp 2 (fun q : Fin (K * d) =>
    if (finProdFinEquiv.symm q).1 = s then w (finProdFinEquiv.symm q).2 else H q)

@[simp] lemma blk_zero (s : Fin K) : blk (0 : EuclideanSpace ℝ (Fin (K * d))) s = 0 := by
  ext k; simp [blk]

lemma blk_setBlk (H : EuclideanSpace ℝ (Fin (K * d))) (s s' : Fin K) (w) :
    blk (setBlk H s w) s' = if s' = s then w else blk H s' := by
  ext k
  simp only [blk, setBlk, PiLp.toLp_apply, Equiv.symm_apply_apply]
  by_cases h : s' = s
  · subst h; simp
  · simp [h]

lemma continuous_blk (s : Fin K) : Continuous (fun H : EuclideanSpace ℝ (Fin (K * d)) => blk H s) :=
  (PiLp.continuous_toLp 2 _).comp (continuous_pi fun _ => PiLp.continuous_apply 2 _ _)

lemma continuous_setBlk (s : Fin K) :
    Continuous (fun p : EuclideanSpace ℝ (Fin (K * d)) × EuclideanSpace ℝ (Fin d) =>
      setBlk p.1 s p.2) := by
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun q => ?_)
  split_ifs
  · exact (PiLp.continuous_apply 2 _ _).comp continuous_snd
  · exact (PiLp.continuous_apply 2 _ _).comp continuous_fst

end Blocks

variable {d e n T R : ℕ} {τ : Ty}

/-- Parameters of DP-FTRL. -/
structure TParams (d e n T R : ℕ) (τ : Ty) where
  /-- clipping norm -/
  Cl : ℝ
  /-- noise variance -/
  σ2 : ℝ≥0
  /-- the encoder of the matrix mechanism -/
  C : Fin R → Fin T → ℝ
  /-- the decoder of the matrix mechanism; the workload is `A = B · C` -/
  B : Fin T → Fin R → ℝ
  /-- the regularization parameter of the regularized-leader step -/
  lam : ℝ
  /-- the participation schedule: weight of record `i` at round `t` -/
  part : ℕ → ℕ → ℝ
  /-- per-example gradient, on records extended with `⊥`:
      `∇ℓ : ℝ^d → ℝ^e_⊥ → ℝ^d`, as in the DP-SGD and filter case studies -/
  grad : EuclideanSpace ℝ (Fin d) → Option (EuclideanSpace ℝ (Fin e)) →
    EuclideanSpace ℝ (Fin d)
  /-- `∇ℓ(θ, ⊥) = 0`: a missing record contributes nothing to the round's gradient sum -/
  grad_bot : ∀ xx, grad xx none = 0
  /-- the `i`-th record of the dataset, `⊥` (`none`) if that slot is missing -/
  record : τ.interp → ℕ → Option (EuclideanSpace ℝ (Fin e))

/-- Program variables. -/
structure TVars (ident : Type) (d T R : ℕ) (τ : Ty) where
  x : Vars ident (.vec d)
  acc : Vars ident (.vec d)
  z : Vars ident (.vec d)
  i : Vars ident .nat
  D : Vars ident τ
  H : Vars ident (.vec (T * d))
  Y : Vars ident (.vec (R * d))
  distinct : [x.name, acc.name, z.name, i.name, D.name, H.name, Y.name].Nodup

lemma TVars.ne (v : TVars ident d T R τ) :
    v.x.name ≠ v.acc.name ∧ v.x.name ≠ v.z.name ∧ v.x.name ≠ v.i.name ∧ v.x.name ≠ v.D.name ∧
    v.x.name ≠ v.H.name ∧ v.x.name ≠ v.Y.name ∧
    v.acc.name ≠ v.z.name ∧ v.acc.name ≠ v.i.name ∧ v.acc.name ≠ v.D.name ∧
    v.acc.name ≠ v.H.name ∧ v.acc.name ≠ v.Y.name ∧
    v.z.name ≠ v.i.name ∧ v.z.name ≠ v.D.name ∧ v.z.name ≠ v.H.name ∧ v.z.name ≠ v.Y.name ∧
    v.i.name ≠ v.D.name ∧ v.i.name ≠ v.H.name ∧ v.i.name ≠ v.Y.name ∧
    v.D.name ≠ v.H.name ∧ v.D.name ≠ v.Y.name ∧ v.H.name ≠ v.Y.name := by
  have h := v.distinct
  simp only [List.nodup_cons, List.mem_cons, not_or, List.nodup_nil, and_true,
    List.not_mem_nil, not_false_eq_true] at h
  obtain ⟨⟨h1, h2, h3, h4, h5, h6⟩, ⟨h7, h8, h9, h10, h11⟩, ⟨h12, h13, h14, h15⟩,
    ⟨h16, h17, h18⟩, ⟨h19, h20⟩, h21⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21⟩

variable (p : TParams d e n T R τ)

/-- The round's gradient sum `Σ_{i<n} part(i,t)·clip_Γ(∇ℓ(θ,D[i]))` (line 4 of Figure 6).
    A missing record adds `clip_Γ(∇ℓ(θ, ⊥)) = 0`. -/
noncomputable def batchStep (t : ℕ) (DD : τ.interp) (xx : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) :=
  ∑ i ∈ Finset.range n, p.part i t • clipV p.Cl (p.grad xx (p.record DD i))

/-- The mean of release `r`: `(C · H)_r`. -/
noncomputable def rowMean (C : Fin R → Fin T → ℝ) (r : Fin R)
    (HH : EuclideanSpace ℝ (Fin (T * d))) : EuclideanSpace ℝ (Fin d) :=
  ∑ s, C r s • blk HH s

/-- The private prefix sum of round `t`: `(B · Y)_t`.  The model is `−(1/lam)` times this. -/
noncomputable def rowDec [NeZero T] (t : ℕ) (YY : EuclideanSpace ℝ (Fin (R * d))) :
    EuclideanSpace ℝ (Fin d) :=
  ∑ r, p.B (Fin.ofNat T t) r • blk YY r

open scoped Classical in
/-- `done(r) = sup{s : C_{r,s} ≠ 0}`: the round at which aggregate `r` is computed, the last
    round its row of the encoder reads. -/
noncomputable def doneN (r : Fin R) : ℕ :=
  Finset.univ.sup fun s : Fin T => if p.C r s = 0 then 0 else (s : ℕ)

/-! ## Side conditions -/

/-- Measurability side conditions. -/
structure TOK (p : TParams d e n T R τ) (v : TVars ident d T R τ) : Prop where
  grad : Measurable (fun q : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin e) =>
    p.grad q.1 (some q.2))
  present : ∀ k, MeasurableSet {D : τ.interp | (p.record D k).isSome}
  recVal : ∀ k, Measurable (fun D : τ.interp => (p.record D k).getD 0)

section Meas

variable {p} {v : TVars ident d T R τ}

lemma continuous_rowMean {C : Fin R → Fin T → ℝ} (r : Fin R) :
    Continuous (rowMean (d := d) C r) :=
  continuous_finsetSum _ fun s _ =>
    ((continuous_blk s).const_smul (C r s) :
      Continuous fun HH : EuclideanSpace ℝ (Fin (T * d)) => C r s • blk HH s)

lemma continuous_rowDec [NeZero T] (t : ℕ) : Continuous (rowDec (d := d) (T := T) p t) :=
  continuous_finsetSum _ fun r _ =>
    ((continuous_blk r).const_smul (p.B (Fin.ofNat T t) r) :
      Continuous fun YY : EuclideanSpace ℝ (Fin (R * d)) => p.B (Fin.ofNat T t) r • blk YY r)

/-- `∇ℓ` at a slot, split on the slot's presence: the form `TOK` is stated in. -/
lemma grad_record_split (i : ℕ) (xx : EuclideanSpace ℝ (Fin d)) (DD : τ.interp) :
    p.grad xx (p.record DD i)
      = if (p.record DD i).isSome then p.grad xx (some ((p.record DD i).getD 0)) else 0 :=
  apply_option_split (g := p.grad xx) (p.grad_bot xx) _

lemma measurable_batchStep
    (hgrad : Measurable (fun q : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin e) =>
      p.grad q.1 (some q.2)))
    (hpresent : ∀ k, MeasurableSet {D : τ.interp | (p.record D k).isSome})
    (hrecVal : ∀ k, Measurable (fun D : τ.interp => (p.record D k).getD 0)) (t : ℕ) :
    Measurable (fun q : τ.interp × EuclideanSpace ℝ (Fin d) => batchStep p t q.1 q.2) := by
  refine Finset.measurable_sum _ fun i _ => ?_
  have hg : Measurable (fun q : τ.interp × EuclideanSpace ℝ (Fin d) =>
      p.grad q.2 (p.record q.1 i)) := by
    simp only [grad_record_split]
    exact Measurable.ite (measurable_fst (hpresent i))
      (hgrad.comp (measurable_snd.prodMk ((hrecVal i).comp measurable_fst)))
      measurable_const
  exact ((measurable_clipV p.Cl).comp hg).const_smul (p.part i t)

end Meas

/-! ## Readings and invariants -/

section Inv

variable {p} {v : TVars ident d T R τ}

abbrev tX (v : TVars ident d T R τ) (h : M.heap) := M.get h (.vec d) v.x.name
abbrev tA (v : TVars ident d T R τ) (h : M.heap) := M.get h (.vec d) v.acc.name
abbrev tZ (v : TVars ident d T R τ) (h : M.heap) := M.get h (.vec d) v.z.name
abbrev tD (v : TVars ident d T R τ) (h : M.heap) := M.get h τ v.D.name
abbrev tH (v : TVars ident d T R τ) (h : M.heap) := M.get h (.vec (T * d)) v.H.name
abbrev tY (v : TVars ident d T R τ) (h : M.heap) := M.get h (.vec (R * d)) v.Y.name

/-- The differing record moves the round's gradient sum by at most `|part(j,t)|·Γ`: the two
    sums agree termwise off `j`, and at `j` the right run contributes `clip_Γ(∇ℓ(θ, ⊥)) = 0`. -/
private lemma norm_batchStep_sub_le_of_adjAt {j : ℕ} {D₁ D₂ : τ.interp} (hadj : AdjAt p.record j D₁ D₂)
    (hC : 0 ≤ p.Cl) (t : ℕ) (xx : EuclideanSpace ℝ (Fin d)) :
    ‖batchStep p t D₁ xx - batchStep p t D₂ xx‖ ≤ |p.part j t| * p.Cl := by
  obtain ⟨hoff, hjbot⟩ := hadj
  have hterm : ∀ i ∈ Finset.range n, i ≠ j →
      p.part i t • clipV p.Cl (p.grad xx (p.record D₁ i)) -
      p.part i t • clipV p.Cl (p.grad xx (p.record D₂ i)) = 0 := by
    intro i _ hij
    rw [hoff i hij, sub_self]
  unfold batchStep
  rw [← Finset.sum_sub_distrib]
  by_cases hjn : j < n
  · rw [Finset.sum_eq_single j hterm (fun h => absurd (Finset.mem_range.mpr hjn) h),
      hjbot, p.grad_bot, clipV_zero, smul_zero, sub_zero, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (norm_clipV_le hC _) (abs_nonneg _)
  · rw [Finset.sum_congr rfl (fun i hi => hterm i hi (fun h => hjn (h ▸ Finset.mem_range.mp hi))),
      Finset.sum_const_zero, norm_zero]
    exact mul_nonneg (abs_nonneg _) hC

/-- `norm_batchStep_sub_le_of_adjAt` in either order. -/
lemma norm_batchStep_sub_le {j : ℕ} {D₁ D₂ : τ.interp} (hadj : AdjAtSym p.record j D₁ D₂)
    (hC : 0 ≤ p.Cl) (t : ℕ) (xx : EuclideanSpace ℝ (Fin d)) :
    ‖batchStep p t D₁ xx - batchStep p t D₂ xx‖ ≤ |p.part j t| * p.Cl := by
  rcases hadj with h | h
  · exact norm_batchStep_sub_le_of_adjAt h hC t xx
  · rw [norm_sub_rev]; exact norm_batchStep_sub_le_of_adjAt h hC t xx

open scoped Classical in
/-- Every release happens during the run: a row is complete by the last round. -/
lemma doneN_lt [NeZero T] (r : Fin R) : doneN p r < T := by
  rw [doneN, Finset.sup_lt_iff (by exact Nat.pos_of_neZero T)]
  intro s _
  split_ifs
  · exact Nat.pos_of_neZero T
  · exact s.2

/-- The invariant between rounds and between releases. -/
def IT (p : TParams d e n T R τ) (v : TVars ident d T R τ) (j : ℕ) (m : M.heap × M.heap) :
    Prop :=
  AdjAtSym p.record j (tD v m.1) (tD v m.2) ∧ tX v m.1 = tX v m.2 ∧ tY v m.1 = tY v m.2 ∧
    ∀ s : Fin T, ‖blk (tH v m.1) s - blk (tH v m.2) s‖ ≤ |p.part j s| * p.Cl

/-- The precondition of the program: the datasets are adjacent at `j`.  The initialization
    establishes the rest of `IT`, through `ITpre1` and `ITpre2`. -/
def ITpre (p : TParams d e n T R τ) (v : TVars ident d T R τ) (j : ℕ)
    (m : M.heap × M.heap) : Prop :=
  AdjAtSym p.record j (tD v m.1) (tD v m.2)

/-- After `θ := 0`: the two models agree. -/
def ITpre1 (p : TParams d e n T R τ) (v : TVars ident d T R τ) (j : ℕ)
    (m : M.heap × M.heap) : Prop :=
  AdjAtSym p.record j (tD v m.1) (tD v m.2) ∧ tX v m.1 = tX v m.2

/-- After `H := 0`: the history blocks agree, hence meet their slack. -/
def ITpre2 (p : TParams d e n T R τ) (v : TVars ident d T R τ) (j : ℕ)
    (m : M.heap × M.heap) : Prop :=
  AdjAtSym p.record j (tD v m.1) (tD v m.2) ∧ tX v m.1 = tX v m.2 ∧
    ∀ s : Fin T, ‖blk (tH v m.1) s - blk (tH v m.2) s‖ ≤ |p.part j s| * p.Cl

end Inv

/-! ## Row gaps -/

/-- The gap bound of aggregate `r`: `∑_s |C_{r,s}|·|part(j,s)|·Γ`. -/
noncomputable def relGap (p : TParams d e n T R τ) (j : ℕ) (r : Fin R) : ℝ :=
  ∑ s, |p.C r s| * (|p.part j s| * p.Cl)

section Rel

variable {p} {v : TVars ident d T R τ}

/-- With a `0/1` participation pattern the gap of aggregate `r` is the `ℓ₁` norm of row `r`
    of the encoder over the pattern, times the clipping norm. -/
lemma relGap_eq_sum_abs {j : ℕ} (pat : Finset (Fin T))
    (hpart : ∀ s : Fin T, p.part j s = if s ∈ pat then 1 else 0) (r : Fin R) :
    relGap p j r = (∑ s ∈ pat, |p.C r s|) * p.Cl := by
  classical
  unfold relGap
  rw [Finset.sum_mul, ← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ pat)]
  have h1 : ∑ s ∈ Finset.univ.filter (· ∈ pat), |p.C r s| * (|p.part j s| * p.Cl)
      = ∑ s ∈ pat, |p.C r s| * p.Cl := by
    rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [hpart s, if_pos hs, abs_one, one_mul]
  have h2 : ∑ s ∈ Finset.univ.filter (fun s => ¬ s ∈ pat), |p.C r s| * (|p.part j s| * p.Cl)
      = 0 := Finset.sum_eq_zero fun s hs => by
        rw [Finset.mem_filter] at hs; rw [hpart s, if_neg hs.2]; simp
  rw [h1, h2, add_zero]

/-- **Proposition E.5 (1)**: for a single participation at `s₀` the squared gaps sum to
    `Γ²‖C_{·,s₀}‖²`, for every encoder `C` (no sign condition). -/
theorem sum_relGap_sq_singleton {j : ℕ} (s₀ : Fin T)
    (hpart : ∀ s : Fin T, p.part j s = if s = s₀ then 1 else 0) :
    ∑ r, relGap p j r ^ 2 = (∑ r, p.C r s₀ ^ 2) * p.Cl ^ 2 := by
  have hg : ∀ r, relGap p j r = |p.C r s₀| * p.Cl := by
    intro r
    unfold relGap
    rw [Finset.sum_eq_single s₀ (fun s _ hs => by rw [hpart s, if_neg hs]; simp)
      (fun h => absurd (Finset.mem_univ s₀) h), hpart s₀, if_pos rfl, abs_one, one_mul]
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun r _ => by rw [hg, mul_pow, sq_abs]

/-- **A row-banded encoder**: every row of `C` has its nonzero entries inside a window of
    fewer than `b` consecutive columns.  A lower-triangular `b`-banded matrix satisfies
    this: its row `r` is supported on the columns `s` with `r - b < s ≤ r`. -/
def RowBanded (C : Fin R → Fin T → ℝ) (b : ℕ) : Prop :=
  ∀ (r : Fin R) (s s' : Fin T), C r s ≠ 0 → C r s' ≠ 0 →
    |((s : ℕ) : ℤ) - ((s' : ℕ) : ℤ)| < (b : ℤ)

/-- **Proposition E.5 (2)**: for a row-banded encoder and a `b`-separated participation
    pattern the squared gaps sum to `Γ² ∑_{s ∈ pat} ‖C_{·,s}‖²`, with no sign condition on `C`
    (each row meets the pattern in at most one column). -/
theorem sum_relGap_sq_banded {j b : ℕ} (pat : Finset (Fin T))
    (hpart : ∀ s : Fin T, p.part j s = if s ∈ pat then 1 else 0)
    (hband : RowBanded p.C b)
    (hsep : ∀ s ∈ pat, ∀ s' ∈ pat, s ≠ s' →
      (b : ℤ) ≤ |((s : ℕ) : ℤ) - ((s' : ℕ) : ℤ)|) :
    ∑ r, relGap p j r ^ 2 = (∑ s ∈ pat, ∑ r, p.C r s ^ 2) * p.Cl ^ 2 := by
  classical
  have hg : ∀ r, relGap p j r = (∑ s ∈ pat, |p.C r s|) * p.Cl :=
    fun r => relGap_eq_sum_abs pat hpart r
  -- each row meets the pattern in at most one column
  have hsq : ∀ r, (∑ s ∈ pat, |p.C r s|) ^ 2 = ∑ s ∈ pat, p.C r s ^ 2 := by
    intro r
    have hcard : (pat.filter (fun s => p.C r s ≠ 0)).card ≤ 1 := by
      refine Finset.card_le_one.mpr fun x hx y hy => ?_
      by_contra hxy
      rw [Finset.mem_filter] at hx hy
      exact absurd (hband r x y hx.2 hy.2) (not_lt.mpr (hsep x hx.1 y hy.1 hxy))
    have hL : ∑ s ∈ pat.filter (fun s => p.C r s ≠ 0), |p.C r s| = ∑ s ∈ pat, |p.C r s| :=
      Finset.sum_subset (Finset.filter_subset _ _) fun s hs hns => by
        rw [Finset.mem_filter] at hns
        rw [not_not.mp (fun h => hns ⟨hs, h⟩), abs_zero]
    have hR : ∑ s ∈ pat.filter (fun s => p.C r s ≠ 0), p.C r s ^ 2 = ∑ s ∈ pat, p.C r s ^ 2 :=
      Finset.sum_subset (Finset.filter_subset _ _) fun s hs hns => by
        rw [Finset.mem_filter] at hns
        rw [not_not.mp (fun h => hns ⟨hs, h⟩)]; ring
    rw [← hL, ← hR]
    rcases (pat.filter (fun s => p.C r s ≠ 0)).eq_empty_or_nonempty with hE | ⟨s₀, hs₀⟩
    · rw [hE]; simp
    · have hFs : pat.filter (fun s => p.C r s ≠ 0) = {s₀} :=
        Finset.eq_singleton_iff_unique_mem.mpr
          ⟨hs₀, fun x hx => Finset.card_le_one.mp hcard x hx s₀ hs₀⟩
      rw [hFs, Finset.sum_singleton, Finset.sum_singleton, sq_abs]
  have step : ∑ r, relGap p j r ^ 2 = (∑ r, ∑ s ∈ pat, p.C r s ^ 2) * p.Cl ^ 2 := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun r _ => by rw [hg r, mul_pow, hsq r]
  rw [step, Finset.sum_comm]

end Rel

end DPFTRL
