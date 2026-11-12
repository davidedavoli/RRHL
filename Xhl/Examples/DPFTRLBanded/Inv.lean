import Xhl.Examples.DPFTRLBanded.Window

open Continuous

/-!
# The invariants of `dpftrlBandedGen` (Appendix D.5)

Every quantity is read off the two states.

* `HAgrT C k c`: every history slot alive at `k` or not yet written (index `≥ k`) agrees,
  except possibly `c` — the record step adds to the current slot, so its prior value must
  agree; `HAgrK` is the exception-free form, between windows.
* The relation between the draws (the paper's conjunct `W`, (59)) is `YGT` before record
  `j`'s step (shift read off the model) and `YHT` after it (shift read off the slot-`s`
  difference of the histories).
* `shiftT`, the window's total shift, is bounded by `Γ·√(colSq)` (`norm_shiftT_le`); the
  rounds of a truncated window past `T` are shifted by nothing.
-/

open MeasureTheory ProbabilityTheory ENNReal
open Cmd hiding loc
open scoped NNReal


variable {ident : Type} {M : MemType ident}

namespace DPFTRL.Band

open Continuous

variable {d e n T : ℕ} {τ : Ty} [NeZero T]

/-- The value held in `w`: a coin and the noises of the window's `m + 1` rounds. -/
abbrev WValT (m d : ℕ) := Ty.interp (Ty.prod .bool (.vec ((m + 1) * d)))

/-! ## The agreement predicates -/

/-- **The two histories agree wherever it can still matter**: every slot alive at `k` (some
    release reading it is still due) or not yet written at `k` (its round is still to come)
    holds the same value on both sides, except possibly the distinguished slot `c`. -/
def HAgrT (C : Fin T → Fin T → ℝ) (k : ℕ) (c : Fin T)
    (H₁ H₂ : EuclideanSpace ℝ (Fin (T * d))) : Prop :=
  ∀ s : Fin T, (k ≤ lastB C s ∨ k ≤ (s : ℕ)) → s ≠ c → blk H₁ s = blk H₂ s

/-- The exception-free form, between windows. -/
def HAgrK (C : Fin T → Fin T → ℝ) (k : ℕ) (H₁ H₂ : EuclideanSpace ℝ (Fin (T * d))) : Prop :=
  ∀ s : Fin T, (k ≤ lastB C s ∨ k ≤ (s : ℕ)) → blk H₁ s = blk H₂ s

variable {C : Fin T → Fin T → ℝ} {k k' : ℕ} {c c' : Fin T}
  {H₁ H₂ : EuclideanSpace ℝ (Fin (T * d))}

lemma hAgrK_of_eq (h : H₁ = H₂) (k : ℕ) : HAgrK (d := d) C k H₁ H₂ := fun _ _ => by rw [h]

lemma HAgrK.mono (h : HAgrK (d := d) C k H₁ H₂) (hk : k ≤ k') : HAgrK C k' H₁ H₂ :=
  fun s hs => h s (hs.imp (le_trans hk) (le_trans hk))

lemma hAgrT_of_hAgrK (h : HAgrK (d := d) C k H₁ H₂) (c : Fin T) : HAgrT C k c H₁ H₂ :=
  fun s hs _ => h s hs

lemma blk_eq_of_hAgrT (h : HAgrT (d := d) C k c H₁ H₂) {s : Fin T}
    (hs : k ≤ lastB C s ∨ k ≤ (s : ℕ)) (hsc : s ≠ c) : blk H₁ s = blk H₂ s := h s hs hsc

lemma blk_eq_of_hAgrK (h : HAgrK (d := d) C k H₁ H₂) {s : Fin T}
    (hs : k ≤ lastB C s ∨ k ≤ (s : ℕ)) : blk H₁ s = blk H₂ s := h s hs

/-- A write keeps the agreement, provided the two values agree whenever the slot written is
    tracked and is not the exception. -/
lemma hAgrT_write (h : HAgrT (d := d) C k c H₁ H₂) (t : Fin T)
    {a₁ a₂ : EuclideanSpace ℝ (Fin d)}
    (ha : (k ≤ lastB C t ∨ k ≤ (t : ℕ)) → t ≠ c → a₁ = a₂) :
    HAgrT C k c (setBlk H₁ t a₁) (setBlk H₂ t a₂) := fun s hs hsc => by
  by_cases hst : s = t
  · rw [blk_setBlk, blk_setBlk, if_pos hst, if_pos hst,
      ha (by rw [← hst]; exact hs) (by rw [← hst]; exact hsc)]
  · rw [blk_setBlk, blk_setBlk, if_neg hst, if_neg hst]
    exact h s hs hsc

lemma hAgrK_write (h : HAgrK (d := d) C k H₁ H₂) (t : Fin T)
    {a₁ a₂ : EuclideanSpace ℝ (Fin d)}
    (ha : (k ≤ lastB C t ∨ k ≤ (t : ℕ)) → a₁ = a₂) :
    HAgrK C k (setBlk H₁ t a₁) (setBlk H₂ t a₂) := fun s hs => by
  by_cases hst : s = t
  · rw [blk_setBlk, blk_setBlk, if_pos hst, if_pos hst, ha (by rw [← hst]; exact hs)]
  · rw [blk_setBlk, blk_setBlk, if_neg hst, if_neg hst]
    exact h s hs

/-- **Leaving a window**: the slot it wrote is dead and its round is past, so the exception
    is vacuous and the agreement holds with no exception at all. -/
lemma hAgrK_of_hAgrT_dead (h : HAgrT (d := d) C k c H₁ H₂) (hk : k ≤ k')
    (hlast : lastB C c < k') (hcv : (c : ℕ) < k') : HAgrK C k' H₁ H₂ := fun s hs => by
  have hsc : s ≠ c := fun e => by subst e; rcases hs with hs | hs <;> omega
  exact h s (hs.imp (le_trans hk) (le_trans hk)) hsc

/-- **Only the distinguished slot reaches a row**: a row `r` computed no earlier than `k`
    reads only slots alive at `k`, so the two means it forms differ by exactly the slot-`c`
    difference, scaled by `C r c`. -/
lemma rowMean_of_hAgrT {p : TParams d e n T T τ} (h : HAgrT (d := d) p.C k c H₁ H₂)
    (r : Fin T) (hr : k ≤ (r : ℕ)) :
    rowMean p.C r H₁ = rowMean p.C r H₂ + p.C r c • (blk H₁ c - blk H₂ c) :=
  rowMean_of_blk_agree fun s hC hsc => h s (Or.inl (le_trans hr (le_lastB hC))) hsc

/-- A row released no earlier than `k` reads only alive slots, which all agree: the two means
    are equal. -/
lemma rowMean_eq_of_hAgrK {p : TParams d e n T T τ} (h : HAgrK (d := d) p.C k H₁ H₂)
    (r : Fin T) (hr : k ≤ (r : ℕ)) : rowMean p.C r H₁ = rowMean p.C r H₂ := by
  unfold rowMean
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases hC : p.C r s = 0
  · rw [hC, zero_smul, zero_smul]
  · rw [h s (Or.inl (le_trans hr (le_lastB hC)))]

/-! ## The window's shift and its norm -/

/-- **The shift of the window's noises** for a slot-`s` difference `g`: round `s + l`
    reads slot `s` with coefficient `C[s+l, s]`; a round past the end of the run
    (`s + l ≥ T`) is shifted by nothing. -/
noncomputable def shiftT (p : TParams d e n T T τ) (s m : ℕ) (g : EuclideanSpace ℝ (Fin d)) :
    Fin (m + 1) → EuclideanSpace ℝ (Fin d) :=
  fun l => (if s + (l : ℕ) < T then p.C (Fin.ofNat T (s + (l : ℕ))) (Fin.ofNat T s) else 0) • g

/-- **The shift of a window is bounded by the block's column norm** `Γ·c_s`: round `s + l`
    shifts its noise by `C[s+l, s]·g`, the `l`-th summand of `colSq`. -/
lemma norm_shiftT_le {p : TParams d e n T T τ} (hC : 0 ≤ p.Cl) {s m : ℕ}
    {g : EuclideanSpace ℝ (Fin d)} (hg : ‖g‖ ≤ p.Cl) :
    ‖concatE (shiftT p s m g)‖ ≤ p.Cl * Real.sqrt (colSq p.C s m) := by
  have hsq : ‖concatE (shiftT p s m g)‖ ^ 2 ≤ (p.Cl * Real.sqrt (colSq p.C s m)) ^ 2 := by
    rw [norm_concatE_sq, mul_pow, Real.sq_sqrt (colSq_nonneg p.C s m), colSq, Finset.mul_sum]
    refine Finset.sum_le_sum fun l _ => ?_
    rw [shiftT, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, mul_comm]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hg 2) (sq_nonneg _)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hC (Real.sqrt_nonneg _))
    two_ne_zero).mp hsq

/-! ## Observations -/

/-- The variables that the invariants read. -/
structure ObsT (d T : ℕ) (τ : Ty) where
  D : τ.interp
  x : EuclideanSpace ℝ (Fin d)
  Y : EuclideanSpace ℝ (Fin (T * d))
  H : EuclideanSpace ℝ (Fin (T * d))
  i : ℕ
  t : ℕ

/-- The observation of a memory. -/
def obsT (v : TVars ident d T T τ) (tv : Vars ident .nat) (h : M.heap) : ObsT d T τ :=
  ⟨tD v h, tX v h, tY v h, tH v h, tIN v h, tT tv h⟩

variable {p : TParams d e n T T τ} {v : TVars ident d T T τ} {tv : Vars ident .nat}
  {q : ℝ≥0} {elig : ℕ → ℕ → Bool} {uv : Vars ident .bool} {m : ℕ}
  {wv : Vars ident (.prod .bool (.vec ((m + 1) * d)))}

section ObsSet

variable (h : M.heap)

lemma obsT_set_u (hu : UOK v tv tv uv) (w : Bool) :
    obsT v tv (M.set h .bool uv.name w) = obsT v tv h := by
  simp only [obsT, tD, tX, tY, tH, tIN, tT, get_set_other _ _ hu.uD, get_set_other _ _ hu.ux,
    get_set_other _ _ hu.uY, get_set_other _ _ hu.uH, get_set_other _ _ hu.ui,
    get_set_other _ _ hu.ut]

lemma obsT_set_z (hct : TCntOK v tv) (w : EuclideanSpace ℝ (Fin d)) :
    obsT v tv (M.set h (.vec d) v.z.name w) = obsT v tv h := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21⟩ := v.ne
  simp only [obsT, tD, tX, tY, tH, tIN, tT, get_set_other _ _ h13,
    get_set_other _ _ (Ne.symm h2), get_set_other _ _ h15, get_set_other _ _ h14,
    get_set_other _ _ h12, get_set_other _ _ (Ne.symm hct.tz)]

lemma obsT_set_i (hct : TCntOK v tv) (w : ℕ) :
    obsT v tv (M.set h .nat v.i.name w) = { obsT v tv h with i := w } := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21⟩ := v.ne
  simp only [obsT, tD, tX, tY, tH, tIN, tT, get_set_other _ _ h16,
    get_set_other _ _ (Ne.symm h3), get_set_other _ _ h18, get_set_other _ _ h17,
    M.get_set_eq, get_set_other _ _ (Ne.symm hct.ti)]

lemma obsT_set_H (hct : TCntOK v tv) (w : EuclideanSpace ℝ (Fin (T * d))) :
    obsT v tv (M.set h (.vec (T * d)) v.H.name w) = { obsT v tv h with H := w } := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21⟩ := v.ne
  simp only [obsT, tD, tX, tY, tH, tIN, tT, get_set_other _ _ (Ne.symm h19),
    get_set_other _ _ (Ne.symm h5), get_set_other _ _ h21, M.get_set_eq,
    get_set_other _ _ (Ne.symm h17), get_set_other _ _ (Ne.symm hct.tH)]

lemma obsT_set_Y (hct : TCntOK v tv) (w : EuclideanSpace ℝ (Fin (T * d))) :
    obsT v tv (M.set h (.vec (T * d)) v.Y.name w) = { obsT v tv h with Y := w } := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21⟩ := v.ne
  simp only [obsT, tD, tX, tY, tH, tIN, tT, get_set_other _ _ (Ne.symm h20),
    get_set_other _ _ (Ne.symm h6), M.get_set_eq, get_set_other _ _ (Ne.symm h21),
    get_set_other _ _ (Ne.symm h18), get_set_other _ _ (Ne.symm hct.tY)]

omit [NeZero T] in
lemma obsT_set_acc (hct : TCntOK v tv) (w : EuclideanSpace ℝ (Fin d)) :
    obsT v tv (M.set h (.vec d) v.acc.name w) = obsT v tv h := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21⟩ := v.ne
  simp only [obsT, tD, tX, tY, tH, tIN, tT, get_set_other _ _ h9,
    get_set_other _ _ (Ne.symm h1), get_set_other _ _ h11, get_set_other _ _ h10,
    get_set_other _ _ h8, get_set_other _ _ (Ne.symm hct.tacc)]

lemma obsT_set_x (hct : TCntOK v tv) (w : EuclideanSpace ℝ (Fin d)) :
    obsT v tv (M.set h (.vec d) v.x.name w) = { obsT v tv h with x := w } := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21⟩ := v.ne
  simp only [obsT, tD, tX, tY, tH, tIN, tT, get_set_other _ _ h4, M.get_set_eq,
    get_set_other _ _ h6, get_set_other _ _ h5, get_set_other _ _ h3,
    get_set_other _ _ (Ne.symm hct.tx)]

lemma obsT_set_t (hct : TCntOK v tv) (w : ℕ) :
    obsT v tv (M.set h .nat tv.name w) = { obsT v tv h with t := w } := by
  simp only [obsT, tD, tX, tY, tH, tIN, tT, get_set_other _ _ hct.tD,
    get_set_other _ _ hct.tx, get_set_other _ _ hct.tY, get_set_other _ _ hct.tH,
    get_set_other _ _ hct.ti, M.get_set_eq]

end ObsSet

lemma obsT_set_w (hw : WOKT v tv uv wv) (h : M.heap) (θ : WValT m d) :
    obsT v tv (M.set h (.prod .bool (.vec ((m + 1) * d))) wv.name θ) = obsT v tv h := by
  simp only [obsT, tD, tX, tY, tH, tIN, tT, get_set_other _ _ hw.wD,
    get_set_other _ _ hw.wx, get_set_other _ _ hw.wY, get_set_other _ _ hw.wH,
    get_set_other _ _ hw.wi, get_set_other _ _ hw.wt]

/-! ## The reads of `w` survive the writes of the program -/

lemma tWT_set_u (hw : WOKT v tv uv wv) (h : M.heap) (b : Bool) :
    tWT wv (M.set h .bool uv.name b) = tWT wv h := get_set_other _ _ (Ne.symm hw.wu)

lemma tWT_set_z (hw : WOKT v tv uv wv) (h : M.heap) (z : EuclideanSpace ℝ (Fin d)) :
    tWT wv (M.set h (.vec d) v.z.name z) = tWT wv h := get_set_other _ _ (Ne.symm hw.wz)

omit [NeZero T] in
lemma tWT_set_acc (hw : WOKT v tv uv wv) (h : M.heap) (a : EuclideanSpace ℝ (Fin d)) :
    tWT wv (M.set h (.vec d) v.acc.name a) = tWT wv h := get_set_other _ _ (Ne.symm hw.wacc)

lemma tWT_set_x (hw : WOKT v tv uv wv) (h : M.heap) (x : EuclideanSpace ℝ (Fin d)) :
    tWT wv (M.set h (.vec d) v.x.name x) = tWT wv h := get_set_other _ _ (Ne.symm hw.wx)

lemma tWT_set_i (hw : WOKT v tv uv wv) (h : M.heap) (i : ℕ) :
    tWT wv (M.set h .nat v.i.name i) = tWT wv h := get_set_other _ _ (Ne.symm hw.wi)

lemma tWT_set_t (hw : WOKT v tv uv wv) (h : M.heap) (k : ℕ) :
    tWT wv (M.set h .nat tv.name k) = tWT wv h := get_set_other _ _ (Ne.symm hw.wt)

lemma tWT_set_H (hw : WOKT v tv uv wv) (h : M.heap)
    (H : EuclideanSpace ℝ (Fin (T * d))) :
    tWT wv (M.set h (.vec (T * d)) v.H.name H) = tWT wv h := get_set_other _ _ (Ne.symm hw.wH)

lemma tWT_set_Y (hw : WOKT v tv uv wv) (h : M.heap)
    (Y : EuclideanSpace ℝ (Fin (T * d))) :
    tWT wv (M.set h (.vec (T * d)) v.Y.name Y) = tWT wv h := get_set_other _ _ (Ne.symm hw.wY)

/-! ## The invariants -/

/-- The shape of a relation between the two runs' draws: it may read the left model, the
    two datasets, the two histories, and the two draws. -/
abbrev NRelT (d T m : ℕ) (τ : Ty) :=
  EuclideanSpace ℝ (Fin d) → τ.interp → τ.interp → EuclideanSpace ℝ (Fin (T * d)) →
    EuclideanSpace ℝ (Fin (T * d)) → WValT m d → WValT m d → Prop

section Inv

variable (p : TParams d e n T T τ) (j s m : ℕ)

/-- **What holds everywhere in the window**: adjacency at `j` (in either order), equal
    models and aggregates `Y`, and the two histories agree on every slot that still
    matters, except possibly the slot `s` the window writes. -/
def YBT (o₁ o₂ : ObsT d T τ) : Prop :=
  AdjAtSym p.record j o₁.D o₂.D ∧ o₁.x = o₂.x ∧ o₁.Y = o₂.Y ∧
    HAgrT p.C s (Fin.ofNat T s) o₁.H o₂.H

/-- **How the two draws are shifted, before record `j`'s step**, in the orientation of the
    adjacency: if record `j` is absent on the right, the right noises are the left ones
    shifted by what record `j`'s gradient would put on the window's releases, if the left
    coin came up; if it is absent on the left, the mirror image, with the right coin. -/
def YShT (x : EuclideanSpace ℝ (Fin d)) (D₁ D₂ : τ.interp) (θ₁ θ₂ : WValT m d) : Prop :=
  (p.record D₂ j = none ∧
      θ₂.2 = θ₁.2 + (if θ₁.1 then concatE (shiftT p s m (gLx p j x D₁)) else 0)) ∨
    (p.record D₁ j = none ∧
      θ₁.2 = θ₂.2 + (if θ₂.1 then concatE (shiftT p s m (gLx p j x D₂)) else 0))

/-- **The draws, before record `j`'s step**: the slot the window writes still agrees, and
    the draws are shifted as `YShT` says. -/
def YGT : NRelT d T m τ := fun x D₁ D₂ H₁ H₂ θ₁ θ₂ =>
  blk H₁ (Fin.ofNat T s) = blk H₂ (Fin.ofNat T s) ∧ YShT p j s m x D₁ D₂ θ₁ θ₂

/-- **The draws, from record `j`'s step on**: round `s + l`'s noise is shifted by its row's
    read of the slot-`s` difference of the two histories (by nothing past the end of the
    run). -/
def YHT : NRelT d T m τ := fun _ _ _ H₁ H₂ θ₁ θ₂ =>
  ∀ l : Fin (m + 1), blk θ₂.2 l = blk θ₁.2 l
    + (if s + (l : ℕ) < T then p.C (Fin.ofNat T (s + (l : ℕ))) (Fin.ofNat T s) else 0)
        • (blk H₁ (Fin.ofNat T s) - blk H₂ (Fin.ofNat T s))

/-- In the record loop of round `k`, before record `i`. -/
def YRT (k i : ℕ) (NR : NRelT d T m τ) (o₁ o₂ : ObsT d T τ) (θ₁ θ₂ : WValT m d) : Prop :=
  YBT p j s o₁ o₂ ∧ o₁.i = i ∧ o₂.i = i ∧ o₁.t = k ∧ o₂.t = k ∧
    NR o₁.x o₁.D o₂.D o₁.H o₂.H θ₁ θ₂

/-- At a round boundary of the window. -/
def YQT (k : ℕ) (NR : NRelT d T m τ) (o₁ o₂ : ObsT d T τ) (θ₁ θ₂ : WValT m d) : Prop :=
  YBT p j s o₁ o₂ ∧ o₁.t = k ∧ o₂.t = k ∧ NR o₁.x o₁.D o₂.D o₁.H o₂.H θ₁ θ₂

end Inv

/-- **Between windows**: the histories agree on everything that still matters, with no
    exception at all, and the counters stand at `k`.  Nothing is said about the draw. -/
def YKT (p : TParams d e n T T τ) (j k : ℕ) (o₁ o₂ : ObsT d T τ) : Prop :=
  AdjAtSym p.record j o₁.D o₂.D ∧ o₁.x = o₂.x ∧ o₁.Y = o₂.Y ∧ HAgrK p.C k o₁.H o₂.H ∧
    o₁.t = k ∧ o₂.t = k

section Mem

variable (p : TParams d e n T T τ) (v : TVars ident d T T τ) (tv : Vars ident .nat) {m : ℕ}
  (wv : Vars ident (.prod .bool (.vec ((m + 1) * d)))) (j s : ℕ)

/-- `YRT` on memories. -/
def YRTm (k i : ℕ) (NR : NRelT d T m τ) (mm : M.heap × M.heap) : Prop :=
  YRT p j s m k i NR (obsT v tv mm.1) (obsT v tv mm.2) (tWT wv mm.1) (tWT wv mm.2)

/-- `YQT` on memories. -/
def YQTm (k : ℕ) (NR : NRelT d T m τ) (mm : M.heap × M.heap) : Prop :=
  YQT p j s m k NR (obsT v tv mm.1) (obsT v tv mm.2) (tWT wv mm.1) (tWT wv mm.2)

/-- `YKT` on memories. -/
def YKTm (k : ℕ) (mm : M.heap × M.heap) : Prop :=
  YKT p j k (obsT v tv mm.1) (obsT v tv mm.2)

/-- **The composable between-windows invariant**: `YKT`, and the window-local variable `w`
    at its default value on both sides. -/
def ZKTm (k : ℕ) (σ : St M × St M) : Prop :=
  liftP (YKTm p v tv j k) σ ∧ tWT wv σ.1.1 = default ∧ tWT wv σ.2.1 = default

end Mem

variable {j s : ℕ}

/-- **Leaving a window**: the slot it wrote is dead (`hlast`) and past, so the agreement
    holds with no exception. -/
lemma yKTm_of_yQTm {k : ℕ} (hk : s ≤ k) (hsk : s < k)
    (hlast : lastB p.C (Fin.ofNat T s) < k) (hsT : s < T) {mm : M.heap × M.heap}
    (h : YQTm p v tv wv j s k (YHT p s m) mm) : YKTm p v tv j k mm := by
  obtain ⟨⟨hadj, hx, hy, hHagr⟩, ht1, ht2, -⟩ := h
  refine ⟨hadj, hx, hy, ?_, ht1, ht2⟩
  refine hAgrK_of_hAgrT_dead hHagr hk hlast ?_
  rw [ofNat_eq_of_lt hsT]
  exact hsk

/-- **Entering a window**: the exception-free agreement is weakened to the re-centred one,
    the window's slot still agrees, and the relation between the two draws is whatever the
    sampling leaf has just established. -/
lemma yQTm_of_yKTm {mm : M.heap × M.heap} (hsT : s < T) (h : YKTm p v tv j s mm)
    (hθ : YShT p j s m (tX v mm.1) (tD v mm.1) (tD v mm.2) (tWT wv mm.1) (tWT wv mm.2)) :
    YQTm p v tv wv j s s (YGT p j s m) mm := by
  obtain ⟨hadj, hx, hy, hHagr, ht1, ht2⟩ := h
  refine ⟨⟨hadj, hx, hy, hAgrT_of_hAgrK hHagr _⟩, ht1, ht2, ?_, hθ⟩
  exact blk_eq_of_hAgrK hHagr (Or.inr (by rw [ofNat_eq_of_lt hsT]))

end DPFTRL.Band
