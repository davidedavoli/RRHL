import Xhl.Examples.DPFTRLMatrix.Potential
import Xhl.Logic.Rrhl.DerivedRules

open Continuous

/-!
# DP-FTRL with a matrix mechanism: the derivation (§5.3, Appendix D.4)

`dpftrl_gen_deriv` derives judgment (13) for `dpftrlGen` in `TDeriv`: **[Assn]** for the
assignments, the counted loop `tderiv_while_count` for both loops (premise (14) is
`tderiv_roundM`), **[If]** on the release schedule, **[Samp-Gap]** (`TDeriv.rndGap`) for the
noise of each aggregate, **[Release]**, **[Seq]** and **[Conseq]**.  Budgets are the
state-dependent potential `potW` of `Potential.lean`; each aggregate is charged the Gaussian
cost of its actual shift.

Everything else is read out of this one derivation in the metalogic: the transcript bound
`dpftrl_gen_Hellinger`, individual RDP at `α·sens_j/2σ²` (`dpftrl_gen_IndivRDP`), and the
comparisons of Appendix D.4 (`dpftrl_gen_denisov_RDP`, `dpftrl_gen_tree_RDP`,
`dpftrl_gen_multiEpoch_IndivRDP`, `dpftrl_gen_multiEpoch_RDP`).  `dpftrl_IndivRDP` is the
result on the quoted program `dpftrl`.
-/

open MeasureTheory ProbabilityTheory ENNReal
open scoped NNReal

variable {ident : Type} {M : MemType ident}

namespace DPFTRL

open Continuous

variable {d e n T R : ℕ} {τ : Ty} [NeZero T] [NeZero R]

variable {p : TParams d e n T R τ} {v : TVars ident d T R τ} {tv rv : Vars ident .nat}

/-! ## The budget of a state -/

omit [NeZero T] [NeZero R] in
/-- **[Assn]** for a variable other than the history, at the weight of a potential. -/
lemma tderiv_assign_potW {α : ℝ} {ty : Ty} (x : Vars ident ty) (ex : Expr M ty)
    (hxH : x.name ≠ v.H.name) (j : ℕ) (P' : Finset (Fin R)) (f : ℕ)
    (P Q : M.heap × M.heap → Prop)
    (h : ∀ m, P m → Q (M.set m.1 ty x.name (esem ex m.1), M.set m.2 ty x.name (esem ex m.2))) :
    TDeriv (M := M) α (liftP P) (liftW (potW p α j P' f v)) (Cmd.assign x ex) (Cmd.assign x ex)
      (liftP Q) (liftW (potW p α j P' f v)) :=
  tderiv_assign_sameW x ex _ _ P Q h fun m _ => le_of_eq (potW_set_other hxH m _ _)

/-! ## The round's gradient sum -/

omit [NeZero R] in
/-- `H[t] := Σ_{i<n} part(i,t)·clip_Γ(∇ℓ(θ, D[i]))` by **[Assn]**: the slot differs by at
    most `|part(j,k)|·Γ`, and the potential shrinks (`potW_setH_le`). -/
lemma tderiv_batchM {α : ℝ} (hok : TOK p v) (hc : MCntOK v tv rv) (hC : 0 ≤ p.Cl) (j : ℕ)
    (P' : Finset (Fin R)) {k : ℕ} (hk : k < T) :
    TDeriv (M := M) α (liftP (ITc p v tv j k)) (liftW (potW p α j P' k v))
      (Cmd.assign v.H (batchEM p v tv hok)) (Cmd.assign v.H (batchEM p v tv hok))
      (liftP (ITc p v tv j k)) (liftW (potW p α j P' (k + 1) v)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21⟩ := v.ne
  have hE : ∀ h : M.heap, esem (batchEM (M := M) p v tv hok) h
      = setBlk (tH v h) (Fin.ofNat T (tT tv h)) (batchStep p (tT tv h) (tD v h) (tX v h)) :=
    fun h => rfl
  refine tderiv_assign_sameW v.H (batchEM p v tv hok) _ _ _ _ (fun m hm => ?_)
    (fun m hm => potW_setH_le fun s hs => ?_)
  · obtain ⟨⟨hadj, hx, hy, hH⟩, ht1, ht2⟩ := hm
    refine ⟨⟨?_, ?_, ?_, fun s => ?_⟩, ?_, ?_⟩
    · show AdjAtSym p.record j (tD v _) (tD v _)
      rw [tD, tD, get_set_other _ _ (Ne.symm h19), get_set_other _ _ (Ne.symm h19)]; exact hadj
    · show tX v _ = tX v _
      rw [tX, tX, get_set_other _ _ (Ne.symm h5), get_set_other _ _ (Ne.symm h5)]; exact hx
    · show tY v _ = tY v _
      rw [tY, tY, get_set_other _ _ h21, get_set_other _ _ h21]; exact hy
    · show ‖blk (tH v _) s - blk (tH v _) s‖ ≤ _
      rw [tH, tH, M.get_set_eq, M.get_set_eq, hE, hE, ht1, ht2, blk_setBlk, blk_setBlk]
      by_cases hst : s = Fin.ofNat T k
      · rw [if_pos hst, if_pos hst, hst, ofNat_eq_of_lt hk, hx]
        exact norm_batchStep_sub_le hadj hC k _
      · rw [if_neg hst, if_neg hst]; exact hH s
    · show tT tv _ = k; rw [tT, get_set_other _ _ (Ne.symm hc.tH)]; exact ht1
    · show tT tv _ = k; rw [tT, get_set_other _ _ (Ne.symm hc.tH)]; exact ht2
  · obtain ⟨-, ht1, ht2⟩ := hm
    have hne : s ≠ Fin.ofNat T k := fun h => by
      rw [h, ofNat_eq_of_lt hk] at hs; exact lt_irrefl _ hs
    show blk (tH v (M.set m.2 (.vec (T * d)) v.H.name (esem (batchEM p v tv hok) m.2))) s
        - blk (tH v (M.set m.1 (.vec (T * d)) v.H.name (esem (batchEM p v tv hok) m.1))) s
        = blk (tH v m.2) s - blk (tH v m.1) s
    rw [tH, tH, M.get_set_eq, M.get_set_eq, hE, hE, ht1, ht2, blk_setBlk, blk_setBlk, if_neg hne,
      if_neg hne]

/-- `r := 0`, as a derivation: one **[Assn]**. -/
lemma tderiv_rInitM {α : ℝ} (hc : MCntOK v tv rv) (j k : ℕ) (P' : Finset (Fin R)) (f : ℕ) :
    TDeriv (M := M) α (liftP (ITc p v tv j k)) (liftW (potW p α j P' f v))
      (Cmd.assign rv (Expr.cst (t := .nat) 0)) (Cmd.assign rv (Expr.cst (t := .nat) 0))
      (liftP (RLc p v tv rv j k 0)) (liftW (potW p α j P' f v)) := by
  refine tderiv_assign_potW rv _ hc.rH j P' f _ _ (fun m hm => ?_)
  obtain ⟨hI, ht1, ht2⟩ := hm
  refine ⟨IT_set_cnt hc.rx hc.rD hc.rH hc.rY m hI 0 0, ?_, ?_, M.get_set_eq _ _ _ _,
    M.get_set_eq _ _ _ _⟩
  · show tT tv _ = k; rw [tT, get_set_other _ _ (Ne.symm hc.tr)]; exact ht1
  · show tT tv _ = k; rw [tT, get_set_other _ _ (Ne.symm hc.tr)]; exact ht2

/-! ## The releases of a round -/

omit [NeZero T] in
/-- A due aggregate: **[Samp-Gap]** (`TDeriv.rndGap`) closes the actual shift of the row, paid
    out of the potential (`potW_release`), and the two rows coincide. -/
lemma tderiv_relDueM {α : ℝ} (hα : 1 < α) (hc : MCntOK v tv rv)
    (hσ : p.σ2 ≠ 0) (j k ρ : ℕ) (hρ : ρ < R) (hdue : doneN p (Fin.ofNat R ρ) = k) :
    TDeriv (M := M) α (liftP (RLc p v tv rv j k ρ))
      (liftW (potW p α j (pend p k ρ) (k + 1) v))
      (Cmd.seq (Cmd.random v.z (noiseKernelE p.σ2)) (Cmd.assign v.Y (relEM p.C v rv)))
      (Cmd.seq (Cmd.random v.z (noiseKernelE p.σ2)) (Cmd.assign v.Y (relEM p.C v rv)))
      (liftP (RLc p v tv rv j k ρ)) (liftW (potW p α j (pend p k (ρ + 1)) (k + 1) v)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21⟩ := v.ne
  set r : Fin R := Fin.ofNat R ρ with hr
  have hrρ : (r : ℕ) = ρ := by rw [hr, ofNat_eq_of_lt hρ]
  set Q' : M.heap × M.heap → Prop := fun m => RLc p v tv rv j k ρ m ∧
    rowMean p.C r (tH v m.1) + tZ v m.1 = rowMean p.C r (tH v m.2) + tZ v m.2 with hQ'
  have hnoise : ∀ (h : M.heap), noiseKernelE (M := M) (d := d) p.σ2 h = gaussE 0 p.σ2 :=
    fun h => rfl
  set δ : M.heap × M.heap → EuclideanSpace ℝ (Fin d) :=
    fun m => rowMean p.C r (tH v m.2) - rowMean p.C r (tH v m.1) with hδ
  have hδeq : ∀ m, δ m = ∑ s, p.C r s • hDiff v m s := by
    intro m
    show rowMean p.C r (tH v m.2) - rowMean p.C r (tH v m.1) = _
    unfold rowMean hDiff
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun s _ => (smul_sub _ _ _).symm
  -- the noise
  have hz : TDeriv (M := M) α (liftP (RLc p v tv rv j k ρ))
      (liftW (potW p α j (pend p k ρ) (k + 1) v))
      (Cmd.random v.z (noiseKernelE p.σ2)) (Cmd.random v.z (noiseKernelE p.σ2)) (liftP Q')
      (liftW (potW p α j (pend p k (ρ + 1)) (k + 1) v)) := by
    refine TDeriv.rndGap hα v.z v.z _ _ (fun s => δ (s.1.1, s.2.1)) _ _ _ _
      (fun s hs => Filter.Eventually.of_forall fun w => ?_) (fun s hs => ?_)
    · obtain ⟨⟨⟨hadj, hx, hy, hH⟩, ht1, ht2, hr1, hr2⟩, htr⟩ := hs
      simp only [updPair, liftP]
      refine ⟨⟨⟨⟨?_, ?_, ?_, fun s => ?_⟩, ?_, ?_, ?_, ?_⟩, ?_⟩, htr⟩
      · show AdjAtSym p.record j (tD v _) (tD v _)
        rw [tD, tD, get_set_other _ _ h13, get_set_other _ _ h13]; exact hadj
      · show tX v _ = tX v _
        rw [tX, tX, get_set_other _ _ (Ne.symm h2), get_set_other _ _ (Ne.symm h2)]; exact hx
      · show tY v _ = tY v _
        rw [tY, tY, get_set_other _ _ h15, get_set_other _ _ h15]; exact hy
      · show ‖blk (tH v _) s - blk (tH v _) s‖ ≤ _
        rw [tH, tH, get_set_other _ _ h14, get_set_other _ _ h14]; exact hH s
      · show tT tv _ = k; rw [tT, get_set_other _ _ (Ne.symm hc.tz)]; exact ht1
      · show tT tv _ = k; rw [tT, get_set_other _ _ (Ne.symm hc.tz)]; exact ht2
      · show tT rv _ = ρ; rw [tT, get_set_other _ _ (Ne.symm hc.rz)]; exact hr1
      · show tT rv _ = ρ; rw [tT, get_set_other _ _ (Ne.symm hc.rz)]; exact hr2
      · show rowMean p.C r (tH v _) + tZ v _ = rowMean p.C r (tH v _) + tZ v _
        rw [tH, tH, get_set_other _ _ h14, get_set_other _ _ h14, tZ, tZ, M.get_set_eq,
          M.get_set_eq]
        have key : ∀ a b u : EuclideanSpace ℝ (Fin d), a + u = b + (u - (b - a)) :=
          fun a b u => by abel
        exact key _ _ _
    · -- the weight after the draw is the potential of the other rows, a constant
      set c := potW p α j (pend p k (ρ + 1)) (k + 1) v (s.1.1, s.2.1) with hcdef
      have hconst : (fun w : EuclideanSpace ℝ (Fin d) =>
          liftW (potW p α j (pend p k (ρ + 1)) (k + 1) v)
            (updPair v.z v.z s (w, w - δ (s.1.1, s.2.1)))) = fun _ => c * 1 := by
        funext w; rw [mul_one]
        exact potW_set_other h14 (s.1.1, s.2.1) _ _
      have hc0 : c ≠ 0 := potW_ne_zero hs.1.1.2.2.2
      rw [hconst, weightedHellingerIntegral_const_mul c hc0 _ measurable_const,
        weightedHellingerIntegral_one, hnoise, hnoise, gaussE_map_add_const]
      have hleaf : hellingerIntegral α (gaussE (0 : EuclideanSpace ℝ (Fin d)) p.σ2)
          (gaussE (0 + δ (s.1.1, s.2.1)) p.σ2)
          ≤ gaussB α p.σ2 (‖∑ s', p.C r s' • hDiff v (s.1.1, s.2.1) s'‖ ^ 2) := by
        refine (gaussE_leaf hα hσ _ _).trans (le_of_eq ?_)
        rw [zero_add, zero_sub, norm_neg, hδeq]; rfl
      refine (mul_le_mul' le_rfl hleaf).trans ?_
      rw [mul_comm]
      have hrel := potW_release (p := p) (v := v) (α := α) (j := j) (k := k) (r := r)
        (by rw [hr]; exact hdue) (s.1.1, s.2.1)
      rw [hrρ] at hrel
      exact hrel
  -- the write of the row
  have hY : TDeriv (M := M) α (liftP Q') (liftW (potW p α j (pend p k (ρ + 1)) (k + 1) v))
      (Cmd.assign v.Y (relEM p.C v rv)) (Cmd.assign v.Y (relEM p.C v rv))
      (liftP (RLc p v tv rv j k ρ)) (liftW (potW p α j (pend p k (ρ + 1)) (k + 1) v)) := by
    refine tderiv_assign_potW v.Y (relEM p.C v rv) (Ne.symm h21) j _ _ _ _ (fun m hm => ?_)
    obtain ⟨⟨⟨hadj, hx, hy, hH⟩, ht1, ht2, hr1, hr2⟩, hsum⟩ := hm
    have hE : ∀ h : M.heap, esem (relEM (M := M) p.C v rv) h
        = setBlk (tY v h) (Fin.ofNat R (tT rv h))
            (rowMean p.C (Fin.ofNat R (tT rv h)) (tH v h) + tZ v h) :=
      fun h => rfl
    refine ⟨⟨?_, ?_, ?_, fun s => ?_⟩, ?_, ?_, ?_, ?_⟩
    · show AdjAtSym p.record j (tD v _) (tD v _)
      rw [tD, tD, get_set_other _ _ (Ne.symm h20), get_set_other _ _ (Ne.symm h20)]; exact hadj
    · show tX v _ = tX v _
      rw [tX, tX, get_set_other _ _ (Ne.symm h6), get_set_other _ _ (Ne.symm h6)]; exact hx
    · show tY v _ = tY v _
      rw [tY, tY, M.get_set_eq, M.get_set_eq, hE, hE, hr1, hr2, hy, ← hr, hsum]
    · show ‖blk (tH v _) s - blk (tH v _) s‖ ≤ _
      rw [tH, tH, get_set_other _ _ (Ne.symm h21), get_set_other _ _ (Ne.symm h21)]; exact hH s
    · show tT tv _ = k; rw [tT, get_set_other _ _ (Ne.symm hc.tY)]; exact ht1
    · show tT tv _ = k; rw [tT, get_set_other _ _ (Ne.symm hc.tY)]; exact ht2
    · show tT rv _ = ρ; rw [tT, get_set_other _ _ (Ne.symm hc.rY)]; exact hr1
    · show tT rv _ = ρ; rw [tT, get_set_other _ _ (Ne.symm hc.rY)]; exact hr2
  exact TDeriv.seq hz hY

/-- `r := r + 1`, as a derivation: one **[Assn]**. -/
lemma tderiv_rIncM {α : ℝ} (hc : MCntOK v tv rv) (j k ρ : ℕ) (P' : Finset (Fin R)) (f : ℕ) :
    TDeriv (M := M) α (liftP (RLc p v tv rv j k ρ)) (liftW (potW p α j P' f v))
      (Cmd.assign rv (incW rv)) (Cmd.assign rv (incW rv)) (liftP (RLc p v tv rv j k (ρ + 1)))
      (liftW (potW p α j P' f v)) := by
  refine tderiv_assign_potW rv (incW rv) hc.rH j P' f _ _ (fun m hm => ?_)
  obtain ⟨hI, ht1, ht2, hr1, hr2⟩ := hm
  refine ⟨IT_set_cnt hc.rx hc.rD hc.rH hc.rY m hI _ _, ?_, ?_, ?_, ?_⟩
  · show tT tv _ = k; rw [tT, get_set_other _ _ (Ne.symm hc.tr)]; exact ht1
  · show tT tv _ = k; rw [tT, get_set_other _ _ (Ne.symm hc.tr)]; exact ht2
  · show M.get (M.set m.1 .nat rv.name (tT rv m.1 + 1)) .nat rv.name = ρ + 1
    rw [M.get_set_eq, hr1]
  · show M.get (M.set m.2 .nat rv.name (tT rv m.2 + 1)) .nat rv.name = ρ + 1
    rw [M.get_set_eq, hr2]

/-- **One step of the aggregate loop**, by **[If]**: the schedule test agrees on both sides. -/
lemma tderiv_relStepM {α : ℝ} (hα : 1 < α) (hc : MCntOK v tv rv)
    (hσ : p.σ2 ≠ 0) (j k ρ : ℕ) (hρ : ρ < R) :
    TDeriv (M := M) α (liftP (RLc p v tv rv j k ρ))
      (liftW (potW p α j (pend p k ρ) (k + 1) v))
      (relStepM p v tv rv) (relStepM p v tv rv) (liftP (RLc p v tv rv j k (ρ + 1)))
      (liftW (potW p α j (pend p k (ρ + 1)) (k + 1) v)) := by
  have hesem : ∀ a : M.heap, esem (dueE (M := M) p tv rv) a
      = decide (doneN p (Fin.ofNat R (tT rv a)) = tT tv a) := fun a => rfl
  unfold relStepM
  refine TDeriv.seq ?_ (tderiv_rIncM hc j k ρ _ _)
  refine TDeriv.if_ (fun s hs => ?_) ?_ ?_
  · obtain ⟨⟨-, ht1, ht2, hr1, hr2⟩, -⟩ := hs
    rw [hesem, hesem, ht1, ht2, hr1, hr2]
  · -- due: sample the noise and write the row; nothing is released here
    by_cases hdue : doneN p (Fin.ofNat R ρ) = k
    · exact TDeriv.conseq (fun s hs => hs.1) (fun _ _ => le_rfl) (fun _ h => h)
        (fun _ _ => le_rfl) (tderiv_relDueM hα hc hσ j k ρ hρ hdue)
    · refine tderiv_of_false (Cmd.seq (Cmd.random v.z (noiseKernelE p.σ2))
        (Cmd.assign v.Y (relEM p.C v rv))) ⟨trivial, trivial⟩ fun s hs => hdue ?_
      obtain ⟨⟨⟨-, ht1, -, hr1, -⟩, -⟩, hd⟩ := hs
      rw [hesem, ht1, hr1, decide_eq_true_iff] at hd
      exact hd
  · -- not due: the pending rows are unchanged
    refine TDeriv.conseq (fun s hs => hs.1) (fun s hs => le_of_eq ?_) (fun _ h => h)
      (fun _ _ => le_rfl) (TDeriv.skip _ _)
    obtain ⟨⟨⟨-, ht1, -, hr1, -⟩, -⟩, hnd⟩ := hs
    rw [hesem, ht1, hr1, decide_eq_false_iff_not] at hnd
    rw [pend_succ_of_not_due fun r hr => ?_]
    have e : Fin.ofNat R ρ = r :=
      Fin.ext (by rw [ofNat_eq_of_lt (show ρ < R from hr ▸ r.2)]; exact hr.symm)
    rwa [← e]

/-- **The aggregate loop of round `k`**, by `tderiv_while_count` over the counter `r`. -/
lemma tderiv_relLoopM {α : ℝ} (hα : 1 < α) (hc : MCntOK v tv rv)
    (hσ : p.σ2 ≠ 0) (j k : ℕ) :
    TDeriv (M := M) α (liftP (RLc p v tv rv j k 0)) (liftW (potW p α j (pend p k 0) (k + 1) v))
      (Cmd.while (ltCE rv R) (relStepM p v tv rv)) (Cmd.while (ltCE rv R) (relStepM p v tv rv))
      (liftP (RLc p v tv rv j k R)) (liftW (potW p α j (pend p k R) (k + 1) v)) := by
  have hesem : ∀ a : M.heap, esem (ltCE (M := M) rv R) a = decide (tT rv a < R) := fun a => rfl
  exact tderiv_while_count R
    (fun ρ => liftP (RLc p v tv rv j k ρ)) (fun ρ => liftW (potW p α j (pend p k ρ) (k + 1) v))
    (fun ρ hρ => tderiv_relStepM hα hc hσ j k ρ hρ)
    (fun ρ s hs hρ => by
      have e1 : tT rv s.1.1 = ρ := hs.1.2.2.2.1
      have e2 : tT rv s.2.1 = ρ := hs.1.2.2.2.2
      constructor <;> rw [hesem, decide_eq_true_iff] <;> omega)
    (fun s hs => by
      have e1 : tT rv s.1.1 = R := hs.1.2.2.2.1
      have e2 : tT rv s.2.1 = R := hs.1.2.2.2.2
      constructor <;> rw [hesem, decide_eq_false_iff_not] <;> omega)

/-! ## The round and the rounds -/

omit [NeZero R] in
/-- `acc := (B · Y)_t` by **[Assn]**: the aggregates agree, so the accumulators do. -/
lemma tderiv_sumM {α : ℝ} (hc : MCntOK v tv rv) (j k : ℕ) (P' : Finset (Fin R)) (f : ℕ) :
    TDeriv (M := M) α (liftP (RLc p v tv rv j k R)) (liftW (potW p α j P' f v))
      (Cmd.assign v.acc (sumEM p v tv)) (Cmd.assign v.acc (sumEM p v tv))
      (liftP (RAc p v tv rv j k)) (liftW (potW p α j P' f v)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21⟩ := v.ne
  refine tderiv_assign_potW v.acc (sumEM p v tv) h10 j P' f _ _ (fun m hm => ?_)
  obtain ⟨⟨hadj, hx, hy, hH⟩, ht1, ht2, hr1, hr2⟩ := hm
  have hE : ∀ h : M.heap, esem (sumEM (M := M) p v tv) h = rowDec p (tT tv h) (tY v h) :=
    fun h => rfl
  refine ⟨⟨⟨?_, ?_, ?_, fun s => ?_⟩, ?_, ?_, ?_, ?_⟩, ?_⟩
  · show AdjAtSym p.record j (tD v _) (tD v _)
    rw [tD, tD, get_set_other _ _ h9, get_set_other _ _ h9]; exact hadj
  · show tX v _ = tX v _
    rw [tX, tX, get_set_other _ _ (Ne.symm h1), get_set_other _ _ (Ne.symm h1)]; exact hx
  · show tY v _ = tY v _
    rw [tY, tY, get_set_other _ _ h11, get_set_other _ _ h11]; exact hy
  · show ‖blk (tH v _) s - blk (tH v _) s‖ ≤ _
    rw [tH, tH, get_set_other _ _ h10, get_set_other _ _ h10]; exact hH s
  · show tT tv _ = k; rw [tT, get_set_other _ _ (Ne.symm hc.tacc)]; exact ht1
  · show tT tv _ = k; rw [tT, get_set_other _ _ (Ne.symm hc.tacc)]; exact ht2
  · show tT rv _ = R; rw [tT, get_set_other _ _ (Ne.symm hc.racc)]; exact hr1
  · show tT rv _ = R; rw [tT, get_set_other _ _ (Ne.symm hc.racc)]; exact hr2
  · show tA v _ = tA v _
    rw [tA, tA, M.get_set_eq, M.get_set_eq, hE, hE, hy, ht1, ht2]

omit [NeZero T] [NeZero R] in
/-- `θ := −(1/λ)·acc` by **[Assn]**. -/
lemma tderiv_modelM {α : ℝ} (hc : MCntOK v tv rv) (j k : ℕ) (P' : Finset (Fin R)) (f : ℕ) :
    TDeriv (M := M) α (liftP (RAc p v tv rv j k)) (liftW (potW p α j P' f v))
      (Cmd.assign v.x (modelEM p v)) (Cmd.assign v.x (modelEM p v))
      (liftP (ITc p v tv j k)) (liftW (potW p α j P' f v)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21⟩ := v.ne
  refine tderiv_assign_potW v.x (modelEM p v) h5 j P' f _ _ (fun m hm => ?_)
  obtain ⟨⟨⟨hadj, hx, hy, hH⟩, ht1, ht2, -, -⟩, hacc⟩ := hm
  have hE : ∀ h : M.heap, esem (modelEM (M := M) p v) h = (-(1 / p.lam)) • tA v h :=
    fun h => rfl
  refine ⟨⟨?_, ?_, ?_, fun s => ?_⟩, ?_, ?_⟩
  · show AdjAtSym p.record j (tD v _) (tD v _)
    rw [tD, tD, get_set_other _ _ h4, get_set_other _ _ h4]; exact hadj
  · show tX v _ = tX v _
    rw [tX, tX, M.get_set_eq, M.get_set_eq, hE, hE, hacc]
  · show tY v _ = tY v _
    rw [tY, tY, get_set_other _ _ h6, get_set_other _ _ h6]; exact hy
  · show ‖blk (tH v _) s - blk (tH v _) s‖ ≤ _
    rw [tH, tH, get_set_other _ _ h5, get_set_other _ _ h5]; exact hH s
  · show tT tv _ = k; rw [tT, get_set_other _ _ (Ne.symm hc.tx)]; exact ht1
  · show tT tv _ = k; rw [tT, get_set_other _ _ (Ne.symm hc.tx)]; exact ht2

/-- `t := t + 1`, as a derivation: one **[Assn]**. -/
lemma tderiv_tIncM {α : ℝ} (hc : MCntOK v tv rv) (j k : ℕ) (P' : Finset (Fin R)) (f : ℕ) :
    TDeriv (M := M) α (liftP (ITc p v tv j k)) (liftW (potW p α j P' f v))
      (Cmd.assign tv (incW tv)) (Cmd.assign tv (incW tv)) (liftP (ITc p v tv j (k + 1)))
      (liftW (potW p α j P' f v)) := by
  refine tderiv_assign_potW tv (incW tv) hc.tH j P' f _ _ (fun m hm => ?_)
  obtain ⟨hI, ht1, ht2⟩ := hm
  refine ⟨IT_set_cnt hc.tx hc.tD hc.tH hc.tY m hI _ _, ?_, ?_⟩
  · show M.get (M.set m.1 .nat tv.name (tT tv m.1 + 1)) .nat tv.name = k + 1
    rw [M.get_set_eq, ht1]
  · show M.get (M.set m.2 .nat tv.name (tT tv m.2 + 1)) .nat tv.name = k + 1
    rw [M.get_set_eq, ht2]

/-- **One round**: the [While] premise (14), at the potential. -/
theorem tderiv_roundM {α : ℝ} (hα : 1 < α) (hok : TOK p v) (hc : MCntOK v tv rv)
    (hσ : p.σ2 ≠ 0) (hC : 0 ≤ p.Cl) (j : ℕ) {k : ℕ} (hk : k < T) :
    TDeriv (M := M) α (liftP (ITc p v tv j k)) (liftW (potW p α j (pend p k 0) k v))
      (roundM p v tv rv hok) (roundM p v tv rv hok) (liftP (ITc p v tv j (k + 1)))
      (liftW (potW p α j (pend p (k + 1) 0) (k + 1) v)) := by
  have hrel : TDeriv (M := M) α (liftP (ITc p v tv j k))
      (liftW (potW p α j (pend p k R) (k + 1) v))
      (Cmd.release (Expr.var v.x)) (Cmd.release (Expr.var v.x))
      (liftP (ITc p v tv j k)) (liftW (potW p α j (pend p k R) (k + 1) v)) :=
    TDeriv.conseq
      (fun s hs => ⟨hs.1, by
        show s.1.2.snoc ⟨_, _⟩ = s.2.2.snoc ⟨_, _⟩
        rw [hs.2]; exact congrArg (fun x => s.2.2.snoc ⟨_, x⟩) hs.1.1.2.1⟩)
      (fun _ _ => le_rfl) (fun _ h => h) (fun _ _ => le_rfl)
      (TDeriv.release (Expr.var v.x) (Expr.var v.x) (liftP (ITc p v tv j k))
        (liftW (potW p α j (pend p k R) (k + 1) v)))
  rw [← pend_round]
  unfold roundM
  exact TDeriv.seq (tderiv_batchM hok hc hC j _ hk)
    (TDeriv.seq (tderiv_rInitM hc j k _ _)
      (TDeriv.seq (tderiv_relLoopM hα hc hσ j k)
        (TDeriv.seq (tderiv_sumM hc j k _ _)
          (TDeriv.seq (tderiv_modelM hc j k _ _)
            (TDeriv.seq hrel (tderiv_tIncM hc j k _ _))))))

/-- **DP-FTRL with the matrix mechanism, as a derivation** (judgment (13)): from datasets
    adjacent at `j` and equal transcripts, the program keeps the transcripts equal at budget
    `sensW = exp(α(α−1)·sens_j/2σ²)`. -/
theorem dpftrl_gen_deriv {α : ℝ} (hα : 1 < α) (hok : TOK p v) (hc : MCntOK v tv rv)
    (hσ : p.σ2 ≠ 0) (hC : 0 ≤ p.Cl) (j : ℕ) :
    TDeriv (M := M) α (liftP (ITpre p v j)) (fun _ => sensW p α j)
      (dpftrlGen p v tv rv hok) (dpftrlGen p v tv rv hok) (liftP (IT p v j)) (fun _ => 1) := by
  have hesem : ∀ a : M.heap, esem (ltCE (M := M) tv T) a = decide (tT tv a < T) := fun a => rfl
  have hloop := tderiv_while_count (α := α) T
    (fun k => liftP (ITc p v tv j k)) (fun k => liftW (potW p α j (pend p k 0) k v))
    (fun k hk => tderiv_roundM hα hok hc hσ hC j hk)
    (fun k s hs hk => by
      have e1 : tT tv s.1.1 = k := hs.1.2.1
      have e2 : tT tv s.2.1 = k := hs.1.2.2
      constructor <;> rw [hesem, decide_eq_true_iff] <;> omega)
    (fun s hs => by
      have e1 : tT tv s.1.1 = T := hs.1.2.1
      have e2 : tT tv s.2.1 = T := hs.1.2.2
      constructor <;> rw [hesem, decide_eq_false_iff_not] <;> omega)
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21⟩ := v.ne
  -- before any slot is written the potential does not read the memories
  set W : M.heap × M.heap → ℝ≥0∞ := potW p α j (pend p 0 0) 0 v with hW
  have hW0 : ∀ m m' : M.heap × M.heap, W m' ≤ W m := fun m m' =>
    le_of_eq (by rw [hW, potW_zero, potW_zero])
  have hzv : ∀ {K : ℕ} (h : M.heap) (c : EuclideanSpace ℝ (Fin K)),
      esem (M := M) (Expr.cst (t := .vec K) c) h = c := fun _ _ => rfl
  -- `θ := 0`
  have hx0 : TDeriv (M := M) α (liftP (ITpre p v j)) (liftW W)
      (Cmd.assign v.x (Expr.cst (t := .vec d) 0)) (Cmd.assign v.x (Expr.cst (t := .vec d) 0))
      (liftP (ITpre1 p v j)) (liftW W) :=
    tderiv_assign_sameW v.x _ _ _ _ _ (fun m hadj => by
      refine ⟨?_, ?_⟩
      · show AdjAtSym p.record j (tD v _) (tD v _)
        rw [tD, tD, get_set_other _ _ h4, get_set_other _ _ h4]; exact hadj
      · show tX v _ = tX v _; rw [tX, tX, M.get_set_eq, M.get_set_eq, hzv, hzv])
      (fun m _ => hW0 _ _)
  -- `H := 0`
  have hH0 : TDeriv (M := M) α (liftP (ITpre1 p v j)) (liftW W)
      (Cmd.assign v.H (Expr.cst (t := .vec (T * d)) 0))
      (Cmd.assign v.H (Expr.cst (t := .vec (T * d)) 0))
      (liftP (ITpre2 p v j)) (liftW W) :=
    tderiv_assign_sameW v.H _ _ _ _ _ (fun m hm => by
      obtain ⟨hadj, hx⟩ := hm
      refine ⟨?_, ?_, fun s => ?_⟩
      · show AdjAtSym p.record j (tD v _) (tD v _)
        rw [tD, tD, get_set_other _ _ (Ne.symm h19), get_set_other _ _ (Ne.symm h19)]; exact hadj
      · show tX v _ = tX v _
        rw [tX, tX, get_set_other _ _ (Ne.symm h5), get_set_other _ _ (Ne.symm h5)]; exact hx
      · show ‖blk (tH v _) s - blk (tH v _) s‖ ≤ _
        rw [tH, tH, M.get_set_eq, M.get_set_eq, hzv, hzv, blk_zero, sub_self, norm_zero]
        exact mul_nonneg (abs_nonneg _) hC)
      (fun m _ => hW0 _ _)
  -- `Y := 0`
  have hY0 : TDeriv (M := M) α (liftP (ITpre2 p v j)) (liftW W)
      (Cmd.assign v.Y (Expr.cst (t := .vec (R * d)) 0))
      (Cmd.assign v.Y (Expr.cst (t := .vec (R * d)) 0))
      (liftP (IT p v j)) (liftW W) :=
    tderiv_assign_sameW v.Y _ _ _ _ _ (fun m hm => by
      obtain ⟨hadj, hx, hH⟩ := hm
      refine ⟨?_, ?_, ?_, fun s => ?_⟩
      · show AdjAtSym p.record j (tD v _) (tD v _)
        rw [tD, tD, get_set_other _ _ (Ne.symm h20), get_set_other _ _ (Ne.symm h20)]; exact hadj
      · show tX v _ = tX v _
        rw [tX, tX, get_set_other _ _ (Ne.symm h6), get_set_other _ _ (Ne.symm h6)]; exact hx
      · show tY v _ = tY v _; rw [tY, tY, M.get_set_eq, M.get_set_eq, hzv, hzv]
      · show ‖blk (tH v _) s - blk (tH v _) s‖ ≤ _
        rw [tH, tH, get_set_other _ _ (Ne.symm h21), get_set_other _ _ (Ne.symm h21)]
        exact hH s)
      (fun m _ => hW0 _ _)
  have ht0 : TDeriv (M := M) α (liftP (IT p v j)) (liftW W)
      (Cmd.assign tv (Expr.cst (t := .nat) 0)) (Cmd.assign tv (Expr.cst (t := .nat) 0))
      (liftP (ITc p v tv j 0)) (liftW W) :=
    tderiv_assign_sameW tv _ _ _ _ _
      (fun m hm => ⟨IT_set_cnt hc.tx hc.tD hc.tH hc.tY m hm 0 0, M.get_set_eq _ _ _ _,
        M.get_set_eq _ _ _ _⟩)
      (fun m _ => hW0 _ _)
  unfold dpftrlGen
  refine TDeriv.conseq (fun _ h => h) (fun s _ => le_of_eq (potW_start _))
    (fun s h => ⟨h.1.1, h.2⟩) (fun s h => ?_)
    (TDeriv.seq hx0 (TDeriv.seq hH0 (TDeriv.seq hY0 (TDeriv.seq ht0 hloop))))
  show (1 : ℝ≥0∞) ≤ potW p α j (pend p T 0) T v (s.1.1, s.2.1)
  rw [pend_end]
  exact one_le_potW_empty h.1.1.2.2.2

/-! ## The readout: the laws of the transcripts, and individual RDP
-/

/-- **The laws of the transcripts**: judgment (13) read out by soundness and Proposition 4.4.
    On datasets adjacent at `j` the transcript laws have `α`-Hellinger integral at most
    `exp(α(α−1)·sens_j/2σ²)`. -/
theorem dpftrl_gen_Hellinger {α : ℝ} (hα : 1 < α) (hok : TOK p v)
    (hc : MCntOK v tv rv) (hσ : p.σ2 ≠ 0) (hC : 0 ≤ p.Cl) {j : ℕ}
    (m₀ : M.heap × M.heap) (hm₀ : ITpre p v j m₀) :
    hellingerIntegral α ((osem (dpftrlGen p v tv rv hok) m₀.1).map Prod.snd)
        ((osem (dpftrlGen p v tv rv hok) m₀.2).map Prod.snd)
      ≤ ENNReal.ofReal (Real.exp (α * (α - 1) * sensSq p j / (2 * (p.σ2 : ℝ)))) :=
  (rrhl_tr_hellingerIntegral_le hα
    (rrhl_conseq (fun _ h => h) (fun _ _ => le_rfl) (fun _ h => h.2) (fun _ _ => le_rfl)
      ((dpftrl_gen_deriv hα hok hc hσ hC j).sound hα))
    ((m₀.1, Tr.nil), (m₀.2, Tr.nil)) ⟨hm₀, rfl⟩).trans_eq (sensW_eq_gaussB_sensSq hα hC j)

/-- **DP-FTRL is `(α, α·sens_j/2σ²)`-individually RDP** (§5.3, Definition 3.6), at the
    adjacency `AdjAtSym p.record j`. -/
theorem dpftrl_gen_IndivRDP {α : ℝ} (hα : 1 < α) (hok : TOK p v)
    (hc : MCntOK v tv rv) (hσ : p.σ2 ≠ 0) (hC : 0 ≤ p.Cl) :
    IndivRenyiDP α (fun j : Fin n => α * sensSq p j / (2 * (p.σ2 : ℝ)))
      (fun (j : Fin n) (m₁ m₂ : M.heap) => AdjAtSym p.record j (tD v m₁) (tD v m₂))
      (fun (m : M.heap) => (osem (dpftrlGen p v tv rv hok) m).map Prod.snd) :=
  fun j => fun m₁ m₂ hadj => (renyiDiv_le_coe_iff hα _ _).2 <|
    (dpftrl_gen_Hellinger hα hok hc hσ hC (m₁, m₂) hadj).trans_eq (by congr 2; ring)

/-- **Any bound on the sensitivity is an RDP level**: if `sens_j ≤ S_j` for every record
    `j < n`, DP-FTRL is `(α, α·S_j/2σ²)`-individually RDP. -/
theorem dpftrl_gen_IndivRDP_of_le {α : ℝ} (hα : 1 < α) (hok : TOK p v)
    (hc : MCntOK v tv rv) (hσ : p.σ2 ≠ 0) (hC : 0 ≤ p.Cl) (S : ℕ → ℝ)
    (hS : ∀ j, j < n → sensSq p j ≤ S j) :
    IndivRenyiDP α (fun j : Fin n => α * S j / (2 * (p.σ2 : ℝ)))
      (fun (j : Fin n) (m₁ m₂ : M.heap) => AdjAtSym p.record j (tD v m₁) (tD v m₂))
      (fun (m : M.heap) => (osem (dpftrlGen p v tv rv hok) m).map Prod.snd) :=
  fun j => fun m₁ m₂ hadj => (renyiDiv_le_coe_iff hα _ _).2 <|
    ((dpftrl_gen_Hellinger hα hok hc hσ hC (m₁, m₂) hadj).trans
      (gaussB_mono hα p.σ2 (hS j j.isLt))).trans_eq (by unfold gaussB; congr 2; ring)

/-! ## The comparisons with previous bounds, in the metalogic -/

/-- **Single participation** (comparison with Denisov et al., Theorem 4.1): if every record
    `j` takes part in round `s₀ j` alone, DP-FTRL is `(α, α·Γ²·max_s ‖C_{·,s}‖²/2σ²)`-RDP, for
    any encoder.  By Proposition D.5 (1) and Lemma 3.7. -/
theorem dpftrl_gen_denisov_RDP {α : ℝ} (hα : 1 < α) (hok : TOK p v)
    (hc : MCntOK v tv rv) (hσ : p.σ2 ≠ 0) (hC : 0 ≤ p.Cl) (s₀ : ℕ → Fin T)
    (hpart : ∀ j, j < n → ∀ s : Fin T, p.part j s = if s = s₀ j then 1 else 0) :
    RenyiDP α (α * ((⨆ s, ∑ r, p.C r s ^ 2) * p.Cl ^ 2) / (2 * (p.σ2 : ℝ)))
      (fun (m₁ m₂ : M.heap) => ∃ j : Fin n, AdjAtSym p.record j (tD v m₁) (tD v m₂))
      (fun (m : M.heap) => (osem (dpftrlGen p v tv rv hok) m).map Prod.snd) :=
  (dpftrl_gen_IndivRDP_of_le hα hok hc hσ hC (fun _ => (⨆ s, ∑ r, p.C r s ^ 2) * p.Cl ^ 2)
    fun j hj => (sensSq_le_relGap j).trans <|
      (sum_relGap_sq_singleton (s₀ j) (hpart j hj)).trans_le <|
        mul_le_mul_of_nonneg_right
          (le_ciSup (Set.finite_range fun s => ∑ r, p.C r s ^ 2).bddAbove (s₀ j))
          (sq_nonneg _)).renyiDP_of_le fun _ => le_rfl

/-- **Multi-epoch participation** (comparison with Choquette-Choo et al.): if `CᵀC ≥ 0`
    entrywise and record `j` participates on the pattern `pat j`, DP-FTRL is
    `(α, α·Γ²‖∑_{t ∈ pat j} C_{·,t}‖²/2σ²)`-individually RDP (`sensSq_eq_patNormSq`). -/
theorem dpftrl_gen_multiEpoch_IndivRDP {α : ℝ} (hα : 1 < α) (hok : TOK p v)
    (hc : MCntOK v tv rv) (hσ : p.σ2 ≠ 0) (hC : 0 ≤ p.Cl) (hd : 0 < d)
    (hG : ∀ s s', 0 ≤ ∑ r, p.C r s * p.C r s') (pat : ℕ → Finset (Fin T))
    (hpart : ∀ j, j < n → ∀ s : Fin T, p.part j s = if s ∈ pat j then 1 else 0) :
    IndivRenyiDP α (fun j : Fin n => α * (patNormSq p.C (pat j) * p.Cl ^ 2) / (2 * (p.σ2 : ℝ)))
      (fun (j : Fin n) (m₁ m₂ : M.heap) => AdjAtSym p.record j (tD v m₁) (tD v m₂))
      (fun (m : M.heap) => (osem (dpftrlGen p v tv rv hok) m).map Prod.snd) :=
  dpftrl_gen_IndivRDP_of_le hα hok hc hσ hC (fun j => patNormSq p.C (pat j) * p.Cl ^ 2)
    fun j hj => (sensSq_eq_patNormSq hd hC hG (pat j) (hpart j hj)).le

/-- **Multi-epoch participation, global form** (Lemma 3.7): DP-FTRL is
    `(α, maxⱼ α·Γ²‖∑_{t ∈ pat j} C_{·,t}‖²/2σ²)`-RDP, the bound of Choquette-Choo et al. -/
theorem dpftrl_gen_multiEpoch_RDP {α : ℝ} (hα : 1 < α) (hok : TOK p v)
    (hc : MCntOK v tv rv) (hσ : p.σ2 ≠ 0) (hC : 0 ≤ p.Cl) (hd : 0 < d) (hn : 0 < n)
    (hG : ∀ s s', 0 ≤ ∑ r, p.C r s * p.C r s') (pat : ℕ → Finset (Fin T))
    (hpart : ∀ j, j < n → ∀ s : Fin T, p.part j s = if s ∈ pat j then 1 else 0) :
    RenyiDP α (⨆ j : Fin n, α * (patNormSq p.C (pat j) * p.Cl ^ 2) / (2 * (p.σ2 : ℝ)))
      (fun (m₁ m₂ : M.heap) => ∃ j : Fin n, AdjAtSym p.record j (tD v m₁) (tD v m₂))
      (fun (m : M.heap) => (osem (dpftrlGen p v tv rv hok) m).map Prod.snd) :=
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  (dpftrl_gen_multiEpoch_IndivRDP hα hok hc hσ hC hd hG pat hpart).renyiDP_iSup
    (Set.finite_range _).bddAbove

section Tree

variable (k : ℕ)

variable {d e n : ℕ} {τ : Ty} {v : TVars ident d (2 ^ k) (nNodes k) τ} {tv rv : Vars ident .nat}

/-- **Tree aggregation with single participation** (comparison with Kairouz et al.,
    Theorem 4.1): with the tree encoder DP-FTRL is `(α, α·(k+1)Γ²/2σ²)`-RDP.
    `dpftrl_gen_denisov_RDP` at the tree, whose columns have squared norm `k + 1`. -/
theorem dpftrl_gen_tree_RDP {α : ℝ} (hα : 1 < α)
    {p : TParams d e n (2 ^ k) (nNodes k) τ}
    (hok : TOK p v) (hc : MCntOK v tv rv) (hσ : p.σ2 ≠ 0) (hC : 0 ≤ p.Cl)
    (henc : p.C = treeC k) (s₀ : ℕ → Fin (2 ^ k))
    (hpart : ∀ j, j < n → ∀ s : Fin (2 ^ k), p.part j s = if s = s₀ j then 1 else 0) :
    RenyiDP α (α * ((k + 1) * p.Cl ^ 2) / (2 * (p.σ2 : ℝ)))
      (fun (m₁ m₂ : M.heap) => ∃ j : Fin n, AdjAtSym p.record j (tD v m₁) (tD v m₂))
      (fun (m : M.heap) => (osem (dpftrlGen p v tv rv hok) m).map Prod.snd) := by
  have h := dpftrl_gen_denisov_RDP (M := M) hα hok hc hσ hC s₀ hpart
  have hcol : (⨆ s, ∑ r, p.C r s ^ 2) = (k + 1 : ℝ) := by
    simp only [henc, colNormSq_tree, ciSup_const]
  rwa [hcol] at h

end Tree

end DPFTRL

/-! ## The instance on the quoted program `dpftrl` -/

namespace DPFTRL

open Continuous DPSGDPaper

variable (N dx d T R : ℕ) [NeZero T] [NeZero R]
  (grad : EuclideanSpace ℝ (Fin dx) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
  (Cl : ℝ) (σ2 : ℝ≥0) (C : Fin R → Fin T → ℝ) (B : Fin T → Fin R → ℝ) (lam : ℝ)
  (part : ℕ → ℕ → ℝ)

/-- **`dpftrl` is individually RDP at the sensitivity** (§5.3): for every record `i`, at
    `AdjAtSym (recBotN N dx) i`, the transcript is `(α, α·sens_i/2σ²)`-RDP, with
    `sens_i = sup_U ∑_r ‖(C·U)_r‖²` over `‖U_s‖ ≤ |part(i,s)|·Cl` written out. -/
theorem dpftrl_IndivRDP {α : ℝ} (hα : 1 < α)
    (hgrad : Measurable (fun p : EuclideanSpace ℝ (Fin dx) × EuclideanSpace ℝ (Fin d) =>
      grad p.1 p.2)) (hσ : σ2 ≠ 0) (hCl : 0 ≤ Cl) :
    IndivRenyiDP α
      (fun i : Fin (N + 1) => α * (⨆ U : {U : Fin T → EuclideanSpace ℝ (Fin d) //
          ∀ s, ‖U s‖ ≤ |part i s| * Cl}, ∑ r, ‖∑ s, C r s • U.1 s‖ ^ 2) / (2 * (σ2 : ℝ)))
      (fun (i : Fin (N + 1)) (m₁ m₂ : PMem.heap) => AdjAtSym (recBotN N dx) i (getDS N dx m₁) (getDS N dx m₂))
      (fun m => (osem (dpftrl N dx d T R grad Cl σ2 C B lam part hgrad) m).map Prod.snd) :=
  fun i m₁ m₂ hadj => by
    rw [dpftrl_eq]
    exact dpftrl_gen_IndivRDP hα
      (tOKP N dx d T R grad Cl σ2 C B lam part hgrad) (mCntOKP N dx d T R) hσ hCl i m₁ m₂
      hadj

end DPFTRL
