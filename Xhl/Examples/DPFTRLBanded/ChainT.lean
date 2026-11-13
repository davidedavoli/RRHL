import Xhl.Examples.DPFTRLBanded.Inv
import Xhl.Logic.Rrhl.DerivedRules

open Continuous

/-!
# The window of `dpftrlBandedGen` as a derivation, statement by statement

The body of the block judgment (57) of Appendix E.5, at budget `1` with the draw `w` in
the state, by [Assn], [If], [Samp] with equal coins, [Local], [Seq], [While] and [Conseq].

* the record step adds to the history slot, so the noise relation `NR` must survive an
  equal-increment write (`NRWriteStable`, satisfied by `YGT` and `YHT`);
* at the distinguished record's step (`tderiv_recJTY`) `YGT` becomes `YHT`;
* the round tail reads only the slots alive at `t` (`rowMean_of_hAgrT`), so the rows
  coincide (the paper's (56)).
-/

open MeasureTheory ProbabilityTheory ENNReal
open Cmd hiding loc
open scoped NNReal


variable {ident : Type} {M : MemType ident}

namespace DPFTRL.Band

open Continuous

variable {d e n T : ℕ} {τ : Ty} [NeZero T]

variable {p : TParams d e n T T τ} {v : TVars ident d T T τ} {tv : Vars ident .nat}
  {q : ℝ≥0} {elig : ℕ → ℕ → Bool} {uv : Vars ident .bool} {hok : TOK p v} {m : ℕ}
  {wv : Vars ident (.prod .bool (.vec ((m + 1) * d)))}

/-! ## The noise relations survive the record loop's history writes -/

/-- A noise relation that survives an equal-increment write to any slot.  This is what the
    record loop demands of `NR`: a record step adds the *same* vector to the same slot on
    both sides. -/
def NRWriteStable (NR : NRelT d T m τ) : Prop :=
  ∀ (x : EuclideanSpace ℝ (Fin d)) (D₁ D₂ : τ.interp)
    (H₁ H₂ : EuclideanSpace ℝ (Fin (T * d))) (θ₁ θ₂ : WValT m d) (t : Fin T)
    (a : EuclideanSpace ℝ (Fin d)),
    NR x D₁ D₂ H₁ H₂ θ₁ θ₂ →
      NR x D₁ D₂ (setBlk H₁ t (blk H₁ t + a)) (setBlk H₂ t (blk H₂ t + a)) θ₁ θ₂

lemma nrws_YGT {j s : ℕ} : NRWriteStable (d := d) (T := T) (m := m) (τ := τ) (YGT p j s m) := by
  rintro x D₁ D₂ H₁ H₂ θ₁ θ₂ t a ⟨hδ, hθ⟩
  refine ⟨?_, hθ⟩
  rw [blk_setBlk, blk_setBlk]
  split_ifs with hts
  · rw [← hts, hδ]
  · exact hδ

lemma nrws_YHT {s : ℕ} : NRWriteStable (d := d) (T := T) (m := m) (τ := τ) (YHT p s m) := by
  intro x D₁ D₂ H₁ H₂ θ₁ θ₂ t a h l
  have hl := h l
  rw [blk_setBlk, blk_setBlk]
  by_cases hts : Fin.ofNat T s = t
  · rw [if_pos hts, if_pos hts, add_sub_add_right_eq_sub, ← hts]; exact hl
  · rw [if_neg hts, if_neg hts]; exact hl

/-! ## `i := i + 1` -/

lemma tderiv_incTY {α : ℝ} (hok : TOK p v) (hct : TCntOK v tv)
    (hw : WOKT v tv uv wv) {j s : ℕ} (k i : ℕ) (NR : NRelT d T m τ) :
    TDeriv (M := M) α (liftP (YRTm p v tv wv j s k i NR)) (fun _ => 1)
      (Cmd.assign v.i (incW v.i)) (Cmd.assign v.i (incW v.i))
      (liftP (YRTm p v tv wv j s k (i + 1) NR)) (fun _ => 1) := by
  refine tderiv_assign_same (α := α) v.i (incW v.i) 1 _ _ (fun mm hmm => ?_)
  obtain ⟨hB, hi1, hi2, ht1, ht2, hG⟩ := hmm
  have e1 : tIN v mm.1 = i := hi1
  have e2 : tIN v mm.2 = i := hi2
  show YRT p j s m k (i + 1) NR (obsT v tv (M.set mm.1 .nat v.i.name (tIN v mm.1 + 1)))
    (obsT v tv (M.set mm.2 .nat v.i.name (tIN v mm.2 + 1)))
    (tWT wv (M.set mm.1 .nat v.i.name (tIN v mm.1 + 1)))
    (tWT wv (M.set mm.2 .nat v.i.name (tIN v mm.2 + 1)))
  rw [obsT_set_i (hct := hct), obsT_set_i (hct := hct), tWT_set_i hw, tWT_set_i hw, e1, e2]
  exact ⟨hB, rfl, rfl, ht1, ht2, hG⟩

/-- Resetting the coin disturbs nothing the invariants read. -/
lemma YRTm_set_u (hu : UOK v tv tv uv) (hw : WOKT v tv uv wv) {j s : ℕ}
    {k i : ℕ} {NR : NRelT d T m τ} (mm : M.heap × M.heap) (b₁ b₂ : Bool) :
    YRTm p v tv wv j s k i NR (M.set mm.1 .bool uv.name b₁, M.set mm.2 .bool uv.name b₂)
      ↔ YRTm p v tv wv j s k i NR mm := by
  show YRT p j s m k i NR (obsT v tv (M.set mm.1 .bool uv.name b₁))
      (obsT v tv (M.set mm.2 .bool uv.name b₂))
      (tWT wv (M.set mm.1 .bool uv.name b₁)) (tWT wv (M.set mm.2 .bool uv.name b₂))
    ↔ _
  rw [obsT_set_u (hu := hu), obsT_set_u (hu := hu), tWT_set_u hw, tWT_set_u hw]
  exact Iff.rfl

/-! ## The record loop -/

/-- The semantics of the history step, split off once. -/
lemma esem_histE_eq (h : M.heap) :
    esem (histE (M := M) p v tv uv hok) h
      = setBlk (tH v h) (Fin.ofNat T (tT tv h))
          (blk (tH v h) (Fin.ofNat T (tT tv h)) + (if M.get h .bool uv.name then (1 : ℝ) else 0)
            • clipV p.Cl (p.grad (tX v h) (p.record (tD v h) (tIN v h)))) := rfl

/-- **A record step that adds the same contribution on both sides.**  [If] on the
    eligibility, [Local] for the coin, [Samp] with *equal* coins, [Assn] for the history
    write — whose increments agree because the record is not the distinguished one (or is,
    but is not eligible this round, `hij`) — then [Assn] for the index. -/
lemma tderiv_recTY {α : ℝ} (hα : 1 < α) (hok : TOK p v) (hct : TCntOK v tv)
    (hu : UOK v tv tv uv) (hw : WOKT v tv uv wv) {j s : ℕ}
    (k i : ℕ) (NR : NRelT d T m τ) (hNR : NRWriteStable NR)
    (hij : i = j → elig j k = false) :
    TDeriv (M := M) α (liftP (YRTm p v tv wv j s k i NR)) (fun _ => 1)
      (recBT p v tv q elig uv hok) (recBT p v tv q elig uv hok)
      (liftP (YRTm p v tv wv j s k (i + 1) NR)) (fun _ => 1) := by
  have hesem : ∀ a : M.heap, esem (eligE (M := M) v tv elig) a = elig (tIN v a) (tT tv a) :=
    fun _ => rfl
  set P := YRTm p v tv wv j s k i NR with hP
  unfold recBT
  refine TDeriv.seq ?_ (tderiv_incTY hok hct hw k i NR)
  refine TDeriv.if_ (fun σ hσ => ?_) ?_ ?_
  · obtain ⟨⟨-, hi1, hi2, ht1, ht2, -⟩, -⟩ := hσ
    have e1 : tIN v σ.1.1 = i := hi1
    have e2 : tIN v σ.2.1 = i := hi2
    have e3 : tT tv σ.1.1 = k := ht1
    have e4 : tT tv σ.2.1 = k := ht2
    rw [hesem, hesem, e1, e2, e3, e4]
  · by_cases hel : elig i k = true
    · have hij' : i ≠ j := fun h => by subst h; rw [hij rfl] at hel; exact Bool.false_ne_true hel
      -- the coin, drawn at equal values
      have hcoin : TDeriv (M := M) α (liftP P) (fun _ => 1)
          (Cmd.random uv (bernoulliKernel q)) (Cmd.random uv (bernoulliKernel q))
          (liftP (fun mm => P mm ∧ M.get mm.1 .bool uv.name = M.get mm.2 .bool uv.name))
          (fun _ => 1) := by
        refine TDeriv.rnd hα uv uv _ _ _ _ _ (fun _ => 1) (fun σ hσ => Filter.Eventually.of_forall fun b => ?_) (fun σ hσ => ?_)
        · refine ⟨⟨(YRTm_set_u hu hw _ b b).mpr hσ.1, ?_⟩, hσ.2⟩
          show M.get (M.set σ.1.1 .bool uv.name b) .bool uv.name
            = M.get (M.set σ.2.1 .bool uv.name b) .bool uv.name
          rw [M.get_set_eq, M.get_set_eq]
        · rw [weightedHellingerIntegral_one, bernoulliKernel_apply, bernoulliKernel_apply, hellingerIntegral_self_prob]
      -- the history write: the same record, the same model, the same coin
      have hhist : TDeriv (M := M) α
          (liftP (fun mm => P mm ∧ M.get mm.1 .bool uv.name = M.get mm.2 .bool uv.name))
          (fun _ => 1) (Cmd.assign v.H (histE p v tv uv hok)) (Cmd.assign v.H (histE p v tv uv hok))
          (liftP (fun mm => P (M.set mm.1 .bool uv.name default,
            M.set mm.2 .bool uv.name default))) (fun _ => 1) := by
        refine tderiv_assign_same (α := α) v.H (histE p v tv uv hok) 1 _ _ (fun mm hmm => ?_)
        obtain ⟨⟨hB, hi1, hi2, ht1, ht2, hG⟩, hcn⟩ := hmm
        obtain ⟨hadj, hx, hy, hHagr⟩ := hB
        refine (YRTm_set_u hu hw (M.set mm.1 (.vec (T * d)) v.H.name _,
          M.set mm.2 (.vec (T * d)) v.H.name _) default default).mpr ?_
        show YRT p j s m k i NR (obsT v tv (M.set mm.1 (.vec (T * d)) v.H.name _))
          (obsT v tv (M.set mm.2 (.vec (T * d)) v.H.name _))
          (tWT wv (M.set mm.1 (.vec (T * d)) v.H.name _))
          (tWT wv (M.set mm.2 (.vec (T * d)) v.H.name _))
        rw [obsT_set_H (hct := hct), obsT_set_H (hct := hct), tWT_set_H hw, tWT_set_H hw]
        have e1 : tIN v mm.1 = i := hi1
        have e2 : tIN v mm.2 = i := hi2
        have e3 : tT tv mm.1 = k := ht1
        have e4 : tT tv mm.2 = k := ht2
        have hxe : tX v mm.1 = tX v mm.2 := hx
        have hadj' : ∀ t', t' ≠ j → p.record (tD v mm.1) t' = p.record (tD v mm.2) t' :=
          hadj.agree
        have hHagr' : HAgrT p.C s (Fin.ofNat T s) (tH v mm.1) (tH v mm.2) := hHagr
        have hG' : NR (tX v mm.1) (tD v mm.1) (tD v mm.2) (tH v mm.1) (tH v mm.2)
            (tWT wv mm.1) (tWT wv mm.2) := hG
        -- the two increments agree: equal coins, equal models, the same record
        have hinc : (if M.get mm.2 .bool uv.name then (1 : ℝ) else 0)
              • clipV p.Cl (p.grad (tX v mm.2) (p.record (tD v mm.2) (tIN v mm.2)))
            = (if M.get mm.1 .bool uv.name then (1 : ℝ) else 0)
              • clipV p.Cl (p.grad (tX v mm.1) (p.record (tD v mm.1) (tIN v mm.1))) := by
          rw [hcn, hxe, e1, e2, hadj' i hij']
        rw [esem_histE_eq, esem_histE_eq, e3, e4, hinc]
        refine ⟨⟨hadj, hx, hy, ?_⟩, hi1, hi2, ht1, ht2, ?_⟩
        · refine hAgrT_write hHagr' (Fin.ofNat T k) (fun htr hne => ?_)
          rw [blk_eq_of_hAgrT hHagr' htr hne]
        · exact hNR (tX v mm.1) (tD v mm.1) (tD v mm.2) (tH v mm.1) (tH v mm.2)
            (tWT wv mm.1) (tWT wv mm.2) (Fin.ofNat T k)
            ((if M.get mm.1 .bool uv.name then (1 : ℝ) else 0)
              • clipV p.Cl (p.grad (tX v mm.1) (p.record (tD v mm.1) (tIN v mm.1)))) hG'
      -- [Local] around the two of them
      have hbody : TDeriv (M := M) α (liftP P) (fun _ => 1)
          (Cmd.seq (Cmd.random uv (bernoulliKernel q)) (Cmd.assign v.H (histE p v tv uv hok)))
          (Cmd.seq (Cmd.random uv (bernoulliKernel q)) (Cmd.assign v.H (histE p v tv uv hok)))
          (fun σ => liftP P (resetV uv σ.1, resetV uv σ.2)) (fun _ => 1) :=
        TDeriv.conseq (fun _ h => h) (fun _ _ => le_rfl) (fun _ h => h) (fun _ _ => le_rfl)
          (TDeriv.seq hcoin hhist)
      have hl := TDeriv.loc (α := α) uv uv
        (c₁ := Cmd.seq (Cmd.random uv (bernoulliKernel q)) (Cmd.assign v.H (histE p v tv uv hok)))
        (c₂ := Cmd.seq (Cmd.random uv (bernoulliKernel q)) (Cmd.assign v.H (histE p v tv uv hok)))
        (P := liftP P) (Q := liftP P) (φ := fun _ => 1) (ψ := fun _ => 1) hbody
      refine TDeriv.conseq (fun σ hσ => ⟨?_, hσ.1.2⟩) (fun _ _ => le_rfl) (fun _ h => h)
        (fun _ _ => le_rfl) hl
      have hP1 := hσ.1.1
      rw [hP] at hP1 ⊢
      exact (YRTm_set_u hu hw (σ.1.1, σ.2.1) default default).mpr hP1
    · refine tderiv_of_false _ ?_ (fun σ hσ => hel ?_)
      · exact ⟨trivial, trivial⟩
      · obtain ⟨⟨⟨-, hi1, -, ht1, -, -⟩, -⟩, hg⟩ := hσ
        have e1 : tIN v σ.1.1 = i := hi1
        have e3 : tT tv σ.1.1 = k := ht1
        rw [hesem, e1, e3] at hg; exact hg
  · exact TDeriv.conseq (fun σ hσ => hσ.1) (fun _ _ => le_rfl) (fun _ h => h) (fun _ _ => le_rfl)
      (TDeriv.skip _ _)

/-- The difference the distinguished record's step leaves in the slot: its clipped gradient
    if the coin held in `w` came up, and nothing otherwise. -/
noncomputable def adJT (p : TParams d e n T T τ) (j : ℕ) {m : ℕ}
    (x : EuclideanSpace ℝ (Fin d)) (D : τ.interp) (θ : WValT m d) :
    EuclideanSpace ℝ (Fin d) :=
  if θ.1 then gLx p j x D else 0

/-- **The step of the distinguished record, with its coin read from `w` — where `YGT`
    becomes `YHT`.**  The run holding record `j` gains `gLx p j x D` in its slot if its
    coin came up; the other gains nothing whatever its coin, its dataset having no slot `j`.
    In either orientation (`YShT`) the slot-`s` difference becomes exactly what the
    window's noises were shifted by — with the sign of the orientation — so the relation
    carried forward reads it off the two histories. -/
lemma tderiv_recJTY {α : ℝ} (hok : TOK p v) (hct : TCntOK v tv)
    (hu : UOK v tv tv uv) (hw : WOKT v tv uv wv) {j s : ℕ}
    (hel : elig j s = true) :
    TDeriv (M := M) α (liftP (YRTm p v tv wv j s s j (YGT p j s m))) (fun _ => 1)
      (recJTE p v tv elig uv hok (coinWT wv)) (recJTE p v tv elig uv hok (coinWT wv))
      (liftP (YRTm p v tv wv j s s (j + 1) (YHT p s m))) (fun _ => 1) := by
  have hesem : ∀ a : M.heap, esem (eligE (M := M) v tv elig) a = elig (tIN v a) (tT tv a) :=
    fun _ => rfl
  have hcoinE : ∀ a : M.heap, esem (coinWT (M := M) wv) a = (tWT wv a).1 := fun _ => rfl
  set P := YRTm p v tv wv j s s j (YGT p j s m) with hP
  set P' := YRTm p v tv wv j s s j (YHT p s m) with hP'
  unfold recJTE
  refine TDeriv.seq ?_ (tderiv_incTY hok hct hw s j (YHT p s m))
  refine TDeriv.if_ (fun σ hσ => ?_) ?_ ?_
  · obtain ⟨⟨-, hi1, hi2, ht1, ht2, -⟩, -⟩ := hσ
    have e1 : tIN v σ.1.1 = j := hi1
    have e2 : tIN v σ.2.1 = j := hi2
    have e3 : tT tv σ.1.1 = s := ht1
    have e4 : tT tv σ.2.1 = s := ht2
    rw [hesem, hesem, e1, e2, e3, e4]
  · -- the coin, read from `w` on each side
    have hset : TDeriv (M := M) α (liftP P) (fun _ => 1)
        (Cmd.assign uv (coinWT wv)) (Cmd.assign uv (coinWT wv))
        (liftP (fun mm => P mm ∧ M.get mm.1 .bool uv.name = (tWT wv mm.1).1 ∧
          M.get mm.2 .bool uv.name = (tWT wv mm.2).1)) (fun _ => 1) := by
      refine tderiv_assign_same (α := α) uv (coinWT wv) 1 _ _ (fun mm hmm => ?_)
      refine ⟨(YRTm_set_u hu hw mm _ _).mpr hmm, ?_, ?_⟩
      · rw [M.get_set_eq, tWT_set_u hw, hcoinE]
      · rw [M.get_set_eq, tWT_set_u hw, hcoinE]
    -- the history write: the left slot gains the coin's worth, the right nothing
    have hhist : TDeriv (M := M) α
        (liftP (fun mm => P mm ∧ M.get mm.1 .bool uv.name = (tWT wv mm.1).1 ∧
          M.get mm.2 .bool uv.name = (tWT wv mm.2).1)) (fun _ => 1)
        (Cmd.assign v.H (histE p v tv uv hok)) (Cmd.assign v.H (histE p v tv uv hok))
        (liftP (fun mm => P' (M.set mm.1 .bool uv.name default,
          M.set mm.2 .bool uv.name default))) (fun _ => 1) := by
      refine tderiv_assign_same (α := α) v.H (histE p v tv uv hok) 1 _ _ (fun mm hmm => ?_)
      obtain ⟨⟨hB, hi1, hi2, ht1, ht2, hδ0, hθ⟩, hb1, hb2⟩ := hmm
      obtain ⟨hadj, hx, hy, hHagr⟩ := hB
      have hHagr' : HAgrT p.C s (Fin.ofNat T s) (tH v mm.1) (tH v mm.2) := hHagr
      have hδ0' : blk (tH v mm.1) (Fin.ofNat T s) = blk (tH v mm.2) (Fin.ofNat T s) := hδ0
      have hθs : YShT p j s m (tX v mm.1) (tD v mm.1) (tD v mm.2) (tWT wv mm.1) (tWT wv mm.2) :=
        hθ
      refine (YRTm_set_u hu hw (M.set mm.1 (.vec (T * d)) v.H.name _,
        M.set mm.2 (.vec (T * d)) v.H.name _) default default).mpr ?_
      show YRT p j s m s j (YHT p s m)
        (obsT v tv (M.set mm.1 (.vec (T * d)) v.H.name _))
        (obsT v tv (M.set mm.2 (.vec (T * d)) v.H.name _))
        (tWT wv (M.set mm.1 (.vec (T * d)) v.H.name _))
        (tWT wv (M.set mm.2 (.vec (T * d)) v.H.name _))
      rw [obsT_set_H (hct := hct), obsT_set_H (hct := hct), tWT_set_H hw, tWT_set_H hw]
      have e1 : tIN v mm.1 = j := hi1
      have e2 : tIN v mm.2 = j := hi2
      have e3 : tT tv mm.1 = s := ht1
      have e4 : tT tv mm.2 = s := ht2
      rcases hθs with ⟨hrec2, hθ'⟩ | ⟨hrec1, hθ'⟩
      · -- record `j` absent on the right: the left slot gains the left coin's worth
        -- the two written values
        have hwrite1 : esem (histE (M := M) p v tv uv hok) mm.1
            = setBlk (tH v mm.1) (Fin.ofNat T s)
                (blk (tH v mm.1) (Fin.ofNat T s)
                  + (if (tWT wv mm.1).1 then (1 : ℝ) else 0) • gLx p j (tX v mm.1) (tD v mm.1)) := by
          rw [esem_histE_eq, e3, e1, hb1]; rfl
        have hwrite2 : esem (histE (M := M) p v tv uv hok) mm.2
            = setBlk (tH v mm.2) (Fin.ofNat T s) (blk (tH v mm.2) (Fin.ofNat T s) + 0) := by
          rw [esem_histE_eq, e4, e2, hrec2, clipV_grad_none, smul_zero]
        -- the coin-weighted gradient is `adJT`
        have hcoinG : (if (tWT wv mm.1).1 then (1 : ℝ) else 0) • gLx p j (tX v mm.1) (tD v mm.1)
            = adJT p j (tX v mm.1) (tD v mm.1) (tWT wv mm.1) := by
          unfold adJT
          cases h : (tWT wv mm.1).1
          · rw [if_neg (by simp [h]), if_neg (by simp [h]), zero_smul]
          · rw [if_pos (by simp [h]), if_pos (by simp [h]), one_smul]
        rw [hwrite1, hwrite2, hcoinG]
        refine ⟨⟨hadj, hx, hy, ?_⟩, hi1, hi2, ht1, ht2, ?_⟩
        · exact hAgrT_write hHagr (Fin.ofNat T s) (fun _ hne => absurd rfl hne)
        · -- `YHT` from `YGT`: the slot difference is now exactly the window's shift source
          intro l
          have hb1' : blk (setBlk (tH v mm.1) (Fin.ofNat T s)
                (blk (tH v mm.1) (Fin.ofNat T s)
                  + adJT p j (tX v mm.1) (tD v mm.1) (tWT wv mm.1))) (Fin.ofNat T s)
              = blk (tH v mm.1) (Fin.ofNat T s)
                  + adJT p j (tX v mm.1) (tD v mm.1) (tWT wv mm.1) := by
            rw [blk_setBlk, if_pos rfl]
          have hb2' : blk (setBlk (tH v mm.2) (Fin.ofNat T s)
                (blk (tH v mm.2) (Fin.ofNat T s) + 0)) (Fin.ofNat T s)
              = blk (tH v mm.2) (Fin.ofNat T s) := by
            rw [blk_setBlk, if_pos rfl, add_zero]
          rw [hb1', hb2']
          -- the difference collapses to `adJT`
          have hδ : blk (tH v mm.1) (Fin.ofNat T s)
                + adJT p j (tX v mm.1) (tD v mm.1) (tWT wv mm.1)
                - blk (tH v mm.2) (Fin.ofNat T s)
              = adJT p j (tX v mm.1) (tD v mm.1) (tWT wv mm.1) := by
            rw [hδ0']; abel
          rw [hδ]
          -- and `YGT`'s shift is blockwise exactly `C[s+l, s] • adJT`
          have hθl : blk (tWT wv mm.2).2 l = blk (tWT wv mm.1).2 l
              + blk (if (tWT wv mm.1).1 then
                  concatE (shiftT p s m (gLx p j (tX v mm.1) (tD v mm.1))) else 0) l := by
            rw [hθ', blk_addA]
          rw [hθl]
          congr 1
          unfold adJT
          cases h : (tWT wv mm.1).1
          · rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true, smul_zero, blk_zeroA]
          · rw [if_pos (rfl : true = true), if_pos (rfl : true = true), blk_concatE]
            rfl
      · -- record `j` absent on the left: the mirror image, the right slot gains the right
        -- coin's worth, and the slot difference is `−adJT`
        have hxe : tX v mm.2 = tX v mm.1 := hx.symm
        have hwrite1 : esem (histE (M := M) p v tv uv hok) mm.1
            = setBlk (tH v mm.1) (Fin.ofNat T s) (blk (tH v mm.1) (Fin.ofNat T s) + 0) := by
          rw [esem_histE_eq, e3, e1, hrec1, clipV_grad_none, smul_zero]
        have hwrite2 : esem (histE (M := M) p v tv uv hok) mm.2
            = setBlk (tH v mm.2) (Fin.ofNat T s)
                (blk (tH v mm.2) (Fin.ofNat T s)
                  + (if (tWT wv mm.2).1 then (1 : ℝ) else 0) • gLx p j (tX v mm.1) (tD v mm.2)) := by
          rw [esem_histE_eq, e4, e2, hb2, hxe]; rfl
        have hcoinG : (if (tWT wv mm.2).1 then (1 : ℝ) else 0) • gLx p j (tX v mm.1) (tD v mm.2)
            = adJT p j (tX v mm.1) (tD v mm.2) (tWT wv mm.2) := by
          unfold adJT
          cases h : (tWT wv mm.2).1
          · rw [if_neg (by simp [h]), if_neg (by simp [h]), zero_smul]
          · rw [if_pos (by simp [h]), if_pos (by simp [h]), one_smul]
        rw [hwrite1, hwrite2, hcoinG]
        refine ⟨⟨hadj, hx, hy, ?_⟩, hi1, hi2, ht1, ht2, ?_⟩
        · exact hAgrT_write hHagr (Fin.ofNat T s) (fun _ hne => absurd rfl hne)
        · intro l
          have hb1' : blk (setBlk (tH v mm.1) (Fin.ofNat T s)
                (blk (tH v mm.1) (Fin.ofNat T s) + 0)) (Fin.ofNat T s)
              = blk (tH v mm.1) (Fin.ofNat T s) := by
            rw [blk_setBlk, if_pos rfl, add_zero]
          have hb2' : blk (setBlk (tH v mm.2) (Fin.ofNat T s)
                (blk (tH v mm.2) (Fin.ofNat T s)
                  + adJT p j (tX v mm.1) (tD v mm.2) (tWT wv mm.2))) (Fin.ofNat T s)
              = blk (tH v mm.2) (Fin.ofNat T s)
                  + adJT p j (tX v mm.1) (tD v mm.2) (tWT wv mm.2) := by
            rw [blk_setBlk, if_pos rfl]
          rw [hb1', hb2']
          have hδ : blk (tH v mm.1) (Fin.ofNat T s)
                - (blk (tH v mm.2) (Fin.ofNat T s)
                  + adJT p j (tX v mm.1) (tD v mm.2) (tWT wv mm.2))
              = -adJT p j (tX v mm.1) (tD v mm.2) (tWT wv mm.2) := by
            rw [hδ0']; abel
          rw [hδ]
          have hθl : blk (tWT wv mm.1).2 l = blk (tWT wv mm.2).2 l
              + blk (if (tWT wv mm.2).1 then
                  concatE (shiftT p s m (gLx p j (tX v mm.1) (tD v mm.2))) else 0) l := by
            rw [hθ', blk_addA]
          have hk : blk (if (tWT wv mm.2).1 then
                concatE (shiftT p s m (gLx p j (tX v mm.1) (tD v mm.2))) else 0) l
              = (if s + (l : ℕ) < T then p.C (Fin.ofNat T (s + (l : ℕ))) (Fin.ofNat T s) else 0)
                  • adJT p j (tX v mm.1) (tD v mm.2) (tWT wv mm.2) := by
            unfold adJT
            cases h : (tWT wv mm.2).1
            · rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true, smul_zero, blk_zeroA]
            · rw [if_pos (rfl : true = true), if_pos (rfl : true = true), blk_concatE]
              rfl
          rw [hθl, hk, smul_neg, add_neg_cancel_right]
    -- [Local]
    have hbody : TDeriv (M := M) α (liftP P) (fun _ => 1)
        (Cmd.seq (Cmd.assign uv (coinWT wv)) (Cmd.assign v.H (histE p v tv uv hok)))
        (Cmd.seq (Cmd.assign uv (coinWT wv)) (Cmd.assign v.H (histE p v tv uv hok)))
        (fun σ => liftP P' (resetV uv σ.1, resetV uv σ.2)) (fun _ => 1) :=
      TDeriv.conseq (fun _ h => h) (fun _ _ => le_rfl) (fun _ h => h) (fun _ _ => le_rfl)
        (TDeriv.seq hset hhist)
    have hl := TDeriv.loc (α := α) uv uv
      (c₁ := Cmd.seq (Cmd.assign uv (coinWT wv)) (Cmd.assign v.H (histE p v tv uv hok)))
      (c₂ := Cmd.seq (Cmd.assign uv (coinWT wv)) (Cmd.assign v.H (histE p v tv uv hok)))
      (P := liftP P) (Q := liftP P')
      (φ := fun _ => 1) (ψ := fun _ => 1) hbody
    refine TDeriv.conseq (fun σ hσ => ⟨?_, hσ.1.2⟩) (fun _ _ => le_rfl) (fun _ h => h)
      (fun _ _ => le_rfl) hl
    have hP1 := hσ.1.1
    rw [hP] at hP1 ⊢
    exact (YRTm_set_u hu hw (σ.1.1, σ.2.1) default default).mpr hP1
  · refine tderiv_of_false _ ?_ (fun σ hσ => ?_)
    · trivial
    · obtain ⟨⟨⟨-, hi1, -, ht1, -, -⟩, -⟩, hg⟩ := hσ
      have e1 : tIN v σ.1.1 = j := hi1
      have e3 : tT tv σ.1.1 = s := ht1
      rw [hesem, e1, e3, hel] at hg
      exact absurd hg (by decide)

/-- **The record loop as a loop**, by the counted [While]. -/
lemma tderiv_loopTY {α : ℝ} (hα : 1 < α) (hok : TOK p v) (hct : TCntOK v tv)
    (hu : UOK v tv tv uv) (hw : WOKT v tv uv wv) {j s : ℕ}
    (k : ℕ) (NR : NRelT d T m τ) (hNR : NRWriteStable NR)
    (hne : elig j k = false) :
    TDeriv (M := M) α (liftP (YRTm p v tv wv j s k 0 NR)) (fun _ => 1)
      (Cmd.while (ltCE v.i n) (recBT p v tv q elig uv hok))
      (Cmd.while (ltCE v.i n) (recBT p v tv q elig uv hok))
      (liftP (YRTm p v tv wv j s k n NR)) (fun _ => 1) := by
  have hesem : ∀ a : M.heap, esem (ltCE (M := M) v.i n) a = decide (tIN v a < n) :=
    fun _ => rfl
  refine tderiv_while_count (α := α) n (fun i => liftP (YRTm p v tv wv j s k i NR))
    (fun _ _ => 1)
    (fun i _ => tderiv_recTY hα hok hct hu hw k i NR hNR (fun _ => hne))
    (fun i σ hσ hi => ?_) (fun σ hσ => ?_)
  · obtain ⟨⟨-, hi1, hi2, -, -, -⟩, -⟩ := hσ
    have e1 : tIN v σ.1.1 = i := hi1
    have e2 : tIN v σ.2.1 = i := hi2
    exact ⟨by rw [hesem, e1, decide_eq_true_iff]; omega,
      by rw [hesem, e2, decide_eq_true_iff]; omega⟩
  · obtain ⟨⟨-, hi1, hi2, -, -, -⟩, -⟩ := hσ
    have e1 : tIN v σ.1.1 = n := hi1
    have e2 : tIN v σ.2.1 = n := hi2
    refine ⟨?_, ?_⟩
    · rw [hesem, e1, decide_eq_false_iff_not]; exact lt_irrefl n
    · rw [hesem, e2, decide_eq_false_iff_not]; exact lt_irrefl n

/-- A stretch of records, none of which is the distinguished one at an eligible round. -/
lemma tderiv_iterRecTY {α : ℝ} (hα : 1 < α) (hok : TOK p v)
    (hct : TCntOK v tv) (hu : UOK v tv tv uv)
    (hw : WOKT v tv uv wv) {j s : ℕ} (k : ℕ)
    (i₀ L : ℕ) (NR : NRelT d T m τ) (hNR : NRWriteStable NR)
    (hij : ∀ i, i₀ ≤ i → i < i₀ + L → i = j → elig j k = false) :
    TDeriv (M := M) α (liftP (YRTm p v tv wv j s k i₀ NR)) (fun _ => 1)
      (iterCmd (recBT p v tv q elig uv hok) L) (iterCmd (recBT p v tv q elig uv hok) L)
      (liftP (YRTm p v tv wv j s k (i₀ + L) NR)) (fun _ => 1) := by
  have h := tderiv_iterCmd_family (M := M) (α := α)
    (fun r => liftP (YRTm p v tv wv j s k (i₀ + r) NR)) (fun _ _ => 1) L
    (fun r hr => tderiv_recTY (M := M) (q := q) hα hok hct hu hw k (i₀ + r) NR hNR
      (hij _ (by omega) (by omega))) L 0 (by omega)
  simpa using h

/-- `i := 0` enters the record loop's invariant. -/
lemma tderiv_iInitTY {α : ℝ} (hok : TOK p v) (hct : TCntOK v tv)
    (hw : WOKT v tv uv wv) {j s : ℕ} (k : ℕ) (NR : NRelT d T m τ) :
    TDeriv (M := M) α (liftP (YQTm p v tv wv j s k NR)) (fun _ => 1)
      (Cmd.assign v.i (Expr.cst (t := .nat) 0)) (Cmd.assign v.i (Expr.cst (t := .nat) 0))
      (liftP (YRTm p v tv wv j s k 0 NR)) (fun _ => 1) := by
  refine tderiv_assign_same (α := α) v.i (Expr.cst (t := .nat) 0) 1 _ _ (fun mm hmm => ?_)
  obtain ⟨hB, ht1, ht2, hNRh⟩ := hmm
  show YRT p j s m k 0 NR (obsT v tv (M.set mm.1 .nat v.i.name _))
    (obsT v tv (M.set mm.2 .nat v.i.name _))
    (tWT wv (M.set mm.1 .nat v.i.name _)) (tWT wv (M.set mm.2 .nat v.i.name _))
  rw [obsT_set_i (hct := hct), obsT_set_i (hct := hct), tWT_set_i hw, tWT_set_i hw]
  exact ⟨hB, rfl, rfl, ht1, ht2, hNRh⟩

/-! ## The round tail: one noise, one row, the model and its release -/

/-- **The tail of a round of the window.**  The noise is read from `w`; by `YHT` the right
    one exceeds the left one by what the slot difference puts on the row due now, and by
    `rowMean_of_hAgrT` the two means differ by exactly the same amount, so the two rows
    coincide; so do the prefix sums `(B·Y)_t` and the models released, at budget `1`. -/
lemma tderiv_postTY {α : ℝ} (hct : TCntOK v tv)
    (hw : WOKT v tv uv wv)
    {j s : ℕ} (l : Fin (m + 1))
    (hkT : s + (l : ℕ) < T) :
    TDeriv (M := M) α (liftP (YQTm p v tv wv j s (s + (l : ℕ)) (YHT p s m))) (fun _ => 1)
      (postTE p v tv (noiseWT wv l)) (postTE p v tv (noiseWT wv l))
      (liftP (YQTm p v tv wv j s (s + (l : ℕ) + 1) (YHT p s m))) (fun _ => 1) := by
  have hnz : ∀ a : M.heap, esem (noiseWT (M := M) wv l) a = blk (tWT wv a).2 l := fun _ => rfl
  set P := YQTm p v tv wv j s (s + (l : ℕ)) (YHT p s m) with hP
  -- the noise, read from `w` on each side
  have hz : TDeriv (M := M) α (liftP P) (fun _ => 1)
      (Cmd.assign v.z (noiseWT wv l)) (Cmd.assign v.z (noiseWT wv l))
      (liftP (fun mm => P mm ∧ tZ v mm.1 = blk (tWT wv mm.1).2 l ∧
        tZ v mm.2 = blk (tWT wv mm.2).2 l)) (fun _ => 1) := by
    refine tderiv_assign_same (α := α) v.z _ 1 _ _ (fun mm hmm => ?_)
    refine ⟨?_, ?_, ?_⟩
    · show YQT p j s m (s + (l : ℕ)) (YHT p s m)
        (obsT v tv (M.set mm.1 (.vec d) v.z.name _)) (obsT v tv (M.set mm.2 (.vec d) v.z.name _))
        (tWT wv (M.set mm.1 (.vec d) v.z.name _)) (tWT wv (M.set mm.2 (.vec d) v.z.name _))
      rw [obsT_set_z (hct := hct), obsT_set_z (hct := hct), tWT_set_z hw, tWT_set_z hw]
      exact hmm
    · simpa only [tWT_set_z hw, M.get_set_eq] using hnz mm.1
    · simpa only [tWT_set_z hw, M.get_set_eq] using hnz mm.2
  -- the row: the mean shift and the noise shift cancel
  have hY : TDeriv (M := M) α
      (liftP (fun mm => P mm ∧ tZ v mm.1 = blk (tWT wv mm.1).2 l ∧
        tZ v mm.2 = blk (tWT wv mm.2).2 l)) (fun _ => 1)
      (Cmd.assign v.Y (relEM p.C v tv)) (Cmd.assign v.Y (relEM p.C v tv))
      (liftP P) (fun _ => 1) := by
    refine tderiv_assign_same (α := α) v.Y (relEM p.C v tv) 1 _ _ (fun mm hmm => ?_)
    obtain ⟨⟨⟨hadj, hx, hy, hHagr⟩, ht1, ht2, hH⟩, hz1, hz2⟩ := hmm
    show YQT p j s m (s + (l : ℕ)) (YHT p s m)
      (obsT v tv (M.set mm.1 (.vec (T * d)) v.Y.name _))
      (obsT v tv (M.set mm.2 (.vec (T * d)) v.Y.name _))
      (tWT wv (M.set mm.1 (.vec (T * d)) v.Y.name _))
      (tWT wv (M.set mm.2 (.vec (T * d)) v.Y.name _))
    rw [obsT_set_Y (hct := hct), obsT_set_Y (hct := hct), tWT_set_Y hw, tWT_set_Y hw]
    refine ⟨⟨hadj, hx, ?_, hHagr⟩, ht1, ht2, hH⟩
    have hYe : tY v mm.1 = tY v mm.2 := hy
    have e1 : tT tv mm.1 = s + (l : ℕ) := ht1
    have e2 : tT tv mm.2 = s + (l : ℕ) := ht2
    have hmean : rowMean p.C (Fin.ofNat T (s + (l : ℕ))) (tH v mm.1)
        = rowMean p.C (Fin.ofNat T (s + (l : ℕ))) (tH v mm.2)
          + p.C (Fin.ofNat T (s + (l : ℕ))) (Fin.ofNat T s)
            • (blk (tH v mm.1) (Fin.ofNat T s) - blk (tH v mm.2) (Fin.ofNat T s)) :=
      rowMean_of_hAgrT (p := p) hHagr (Fin.ofNat T (s + (l : ℕ)))
        (by simp only [Fin.val_ofNat, Nat.mod_eq_of_lt hkT]; omega)
    have hHl : blk (tWT wv mm.2).2 l = blk (tWT wv mm.1).2 l
        + p.C (Fin.ofNat T (s + (l : ℕ))) (Fin.ofNat T s)
          • (blk (tH v mm.1) (Fin.ofNat T s) - blk (tH v mm.2) (Fin.ofNat T s)) := by
      have h := hH l
      rwa [if_pos hkT] at h
    show setBlk (tY v mm.1) (Fin.ofNat T (tT tv mm.1))
        (rowMean p.C (Fin.ofNat T (tT tv mm.1)) (tH v mm.1) + tZ v mm.1)
      = setBlk (tY v mm.2) (Fin.ofNat T (tT tv mm.2))
        (rowMean p.C (Fin.ofNat T (tT tv mm.2)) (tH v mm.2) + tZ v mm.2)
    rw [hYe, e1, e2, hz1, hz2, hmean, hHl]
    congr 1
    abel
  -- `ŝ := (B·Y)_t`: equal rows, equal prefix sums
  have hacc : TDeriv (M := M) α (liftP P) (fun _ => 1)
      (Cmd.assign v.acc (sumEM p v tv)) (Cmd.assign v.acc (sumEM p v tv))
      (liftP (fun mm => P mm ∧ tA v mm.1 = tA v mm.2)) (fun _ => 1) := by
    refine tderiv_assign_same (α := α) v.acc (sumEM p v tv) 1 _ _ (fun mm hmm => ?_)
    refine ⟨?_, ?_⟩
    · show YQT p j s m (s + (l : ℕ)) (YHT p s m)
        (obsT v tv (M.set mm.1 (.vec d) v.acc.name _))
        (obsT v tv (M.set mm.2 (.vec d) v.acc.name _))
        (tWT wv (M.set mm.1 (.vec d) v.acc.name _)) (tWT wv (M.set mm.2 (.vec d) v.acc.name _))
      rw [obsT_set_acc (hct := hct), obsT_set_acc (hct := hct), tWT_set_acc hw, tWT_set_acc hw]
      exact hmm
    · obtain ⟨⟨-, -, hy, -⟩, ht1, ht2, -⟩ := hmm
      have hYe : tY v mm.1 = tY v mm.2 := hy
      have e1 : tT tv mm.1 = s + (l : ℕ) := ht1
      have e2 : tT tv mm.2 = s + (l : ℕ) := ht2
      show M.get (M.set mm.1 (.vec d) v.acc.name (esem (sumEM p v tv) mm.1)) (.vec d) v.acc.name
        = M.get (M.set mm.2 (.vec d) v.acc.name (esem (sumEM p v tv) mm.2)) (.vec d) v.acc.name
      rw [M.get_set_eq, M.get_set_eq]
      show rowDec p (tT tv mm.1) (tY v mm.1) = rowDec p (tT tv mm.2) (tY v mm.2)
      rw [hYe, e1, e2]
  -- `θ := −(1/λ)·ŝ`: equal prefix sums, equal models
  have hmod : TDeriv (M := M) α (liftP (fun mm => P mm ∧ tA v mm.1 = tA v mm.2)) (fun _ => 1)
      (Cmd.assign v.x (modelEM p v)) (Cmd.assign v.x (modelEM p v))
      (liftP P) (fun _ => 1) := by
    refine tderiv_assign_same (α := α) v.x (modelEM p v) 1 _ _ (fun mm hmm => ?_)
    obtain ⟨⟨⟨hadj, hx, hy, hHagr⟩, ht1, ht2, hH⟩, hA⟩ := hmm
    show YQT p j s m (s + (l : ℕ)) (YHT p s m)
      (obsT v tv (M.set mm.1 (.vec d) v.x.name _)) (obsT v tv (M.set mm.2 (.vec d) v.x.name _))
      (tWT wv (M.set mm.1 (.vec d) v.x.name _)) (tWT wv (M.set mm.2 (.vec d) v.x.name _))
    rw [obsT_set_x (hct := hct), obsT_set_x (hct := hct), tWT_set_x hw, tWT_set_x hw]
    refine ⟨⟨hadj, ?_, hy, hHagr⟩, ht1, ht2, hH⟩
    show (-(1 / p.lam)) • tA v mm.1 = (-(1 / p.lam)) • tA v mm.2
    rw [hA]
  -- the release of the model: equal models
  have hrel : TDeriv (M := M) α (liftP P) (fun _ => 1)
      (Cmd.release (Expr.var v.x)) (Cmd.release (Expr.var v.x)) (liftP P) (fun _ => 1) :=
    tderiv_releaseX _ fun _ hmm => hmm.1.2.1
  -- `t := t + 1`
  have htinc : TDeriv (M := M) α (liftP P) (fun _ => 1)
      (Cmd.assign tv (incW tv)) (Cmd.assign tv (incW tv))
      (liftP (YQTm p v tv wv j s (s + (l : ℕ) + 1) (YHT p s m))) (fun _ => 1) := by
    refine tderiv_assign_same (α := α) tv (incW tv) 1 _ _ (fun mm hmm => ?_)
    obtain ⟨hB, ht1, ht2, hH⟩ := hmm
    have e1 : tT tv mm.1 = s + (l : ℕ) := ht1
    have e2 : tT tv mm.2 = s + (l : ℕ) := ht2
    show YQT p j s m (s + (l : ℕ) + 1) (YHT p s m)
      (obsT v tv (M.set mm.1 .nat tv.name (tT tv mm.1 + 1)))
      (obsT v tv (M.set mm.2 .nat tv.name (tT tv mm.2 + 1)))
      (tWT wv (M.set mm.1 .nat tv.name (tT tv mm.1 + 1)))
      (tWT wv (M.set mm.2 .nat tv.name (tT tv mm.2 + 1)))
    rw [obsT_set_t (hct := hct), obsT_set_t (hct := hct), tWT_set_t hw, tWT_set_t hw, e1, e2]
    exact ⟨hB, rfl, rfl, hH⟩
  unfold postTE
  exact TDeriv.seq hz (TDeriv.seq hY (TDeriv.seq hacc (TDeriv.seq hmod (TDeriv.seq hrel htinc))))

/-! ## Rounds -/

/-- **A later round of the window**: the distinguished record is not eligible, so the record
    loop adds equal contributions and the round is exact at budget `1`. -/
lemma tderiv_roundTY {α : ℝ} (hα : 1 < α) (hok : TOK p v)
    (hct : TCntOK v tv) (hu : UOK v tv tv uv)
    (hw : WOKT v tv uv wv)
    {j s : ℕ}
    (l : Fin (m + 1)) (hkT : s + (l : ℕ) < T) (hne : elig j (s + (l : ℕ)) = false) :
    TDeriv (M := M) α (liftP (YQTm p v tv wv j s (s + (l : ℕ)) (YHT p s m))) (fun _ => 1)
      (roundTE p v tv q elig uv hok (noiseWT wv l)) (roundTE p v tv q elig uv hok (noiseWT wv l))
      (liftP (YQTm p v tv wv j s (s + (l : ℕ) + 1) (YHT p s m))) (fun _ => 1) := by
  unfold roundTE
  refine TDeriv.seq (tderiv_iInitTY hok hct hw (s + (l : ℕ)) (YHT p s m)) ?_
  refine TDeriv.seq (tderiv_loopTY hα hok hct hu hw (s + (l : ℕ)) (YHT p s m)
    nrws_YHT hne) ?_
  refine TDeriv.conseq (fun σ hσ => ?_) (fun _ _ => le_rfl) (fun _ h => h) (fun _ _ => le_rfl)
    (tderiv_postTY hct hw l hkT)
  obtain ⟨⟨hB, -, -, ht1, ht2, hH⟩, htr⟩ := hσ
  exact ⟨⟨hB, ht1, ht2, hH⟩, htr⟩

/-- **The window's first round**, at which the distinguished record participates. -/
lemma tderiv_roundITY {α : ℝ} (hα : 1 < α) (hok : TOK p v)
    (hct : TCntOK v tv) (hu : UOK v tv tv uv)
    (hw : WOKT v tv uv wv)
    {j s : ℕ} (hsT : s < T)
    (hj : j < n) (hel : elig j s = true) :
    TDeriv (M := M) α (liftP (YQTm p v tv wv j s s (YGT p j s m))) (fun _ => 1)
      (roundITE p v tv q elig uv hok j (coinWT wv) (noiseWT wv 0))
      (roundITE p v tv q elig uv hok j (coinWT wv) (noiseWT wv 0))
      (liftP (YQTm p v tv wv j s (s + 1) (YHT p s m))) (fun _ => 1) := by
  have h1 := tderiv_iterRecTY (M := M) (α := α) (q := q) hα hok hct hu hw (j := j) (s := s)
    (elig := elig) s 0 j (YGT p j s m) nrws_YGT (fun i _ hi h => absurd h (by omega))
  have h2 := tderiv_recJTY (M := M) (α := α) hok hct hu hw (s := s) hel
  have h3 := tderiv_iterRecTY (M := M) (α := α) (q := q) hα hok hct hu hw (j := j) (s := s)
    (elig := elig) s (j + 1) (n - j - 1) (YHT p s m) nrws_YHT (fun i hi _ h => absurd h (by omega))
  rw [zero_add] at h1
  rw [show j + 1 + (n - j - 1) = n from by omega] at h3
  have hpost := tderiv_postTY (M := M) (α := α) (p := p) (j := j) (s := s) hct hw (0 : Fin (m + 1))
    (by simpa using hsT)
  simp only [Fin.val_zero, Nat.add_zero] at hpost
  unfold roundITE
  refine TDeriv.seq (tderiv_iInitTY hok hct hw s (YGT p j s m)) ?_
  refine TDeriv.seq h1 ?_
  refine TDeriv.seq h2 ?_
  refine TDeriv.seq h3 ?_
  refine TDeriv.conseq (fun σ hσ => ?_) (fun _ _ => le_rfl) (fun _ h => h) (fun _ _ => le_rfl)
    hpost
  obtain ⟨⟨hB, -, -, ht1, ht2, hH⟩, htr⟩ := hσ
  exact ⟨⟨hB, ht1, ht2, hH⟩, htr⟩

/-- `m` rounds, as a family. -/
lemma tderiv_iterTE_family {α : ℝ} :
    ∀ (K : ℕ) (F : ℕ → St M × St M → Prop) (ez : Fin K → Expr M (.vec d)),
      (∀ l : Fin K, TDeriv (M := M) α (F (l : ℕ)) (fun _ => 1)
        (roundTE p v tv q elig uv hok (ez l)) (roundTE p v tv q elig uv hok (ez l))
        (F ((l : ℕ) + 1)) (fun _ => 1)) →
      TDeriv (M := M) α (F 0) (fun _ => 1) (iterTE p v tv q elig uv hok K ez)
        (iterTE p v tv q elig uv hok K ez) (F K) (fun _ => 1)
  | 0, F, _, _ => TDeriv.skip _ _
  | K + 1, F, ez, h => by
    have ih := tderiv_iterTE_family (α := α) K (fun r => F (r + 1)) (Fin.tail ez) (fun l => by
      have := h l.succ
      simpa [Fin.tail, Fin.val_succ] using this)
    exact TDeriv.seq (by simpa using h 0) (by simpa using ih)

/-! ## The window -/

/-- **The whole window, at budget `1`, with the draw in the state.**  The window has
    `L + 1 ≤ m + 1` rounds, all inside the run, and reads the first `L + 1` noise blocks
    of `w`; the precondition `YGT` on the draws is paid for by the sampling leaf. -/
theorem tderiv_windowWY {α : ℝ} (hα : 1 < α) (hok : TOK p v)
    (hct : TCntOK v tv) (hu : UOK v tv tv uv)
    (hw : WOKT v tv uv wv)
    {j : ℕ} (hj : j < n) (s L : ℕ) (hL : L ≤ m)
    (hsT : s + L < T) (hel : elig j s = true)
    (hne : ∀ l, 1 ≤ l → l ≤ L → elig j (s + l) = false) :
    TDeriv (M := M) α (liftP (YQTm p v tv wv j s s (YGT p j s m))) (fun _ => 1)
      (windowE p v tv q elig uv hok j L (coinWT wv)
        (fun l => noiseWT wv (Fin.castLE (Nat.succ_le_succ hL) l)))
      (windowE p v tv q elig uv hok j L (coinWT wv)
        (fun l => noiseWT wv (Fin.castLE (Nat.succ_le_succ hL) l)))
      (liftP (YQTm p v tv wv j s (s + L + 1) (YHT p s m))) (fun _ => 1) := by
  have hrest := tderiv_iterTE_family (α := α) (p := p) (v := v) (tv := tv) (q := q)
    (elig := elig) (uv := uv) L
    (fun r => liftP (YQTm p v tv wv j s (s + 1 + r) (YHT p s m)))
    (Fin.tail fun l : Fin (L + 1) => noiseWT wv (Fin.castLE (Nat.succ_le_succ hL) l))
    (fun l => by
      have hl := l.isLt
      have hval : ((Fin.castLE (Nat.succ_le_succ hL) l.succ : Fin (m + 1)) : ℕ)
          = (l : ℕ) + 1 := rfl
      have h := tderiv_roundTY (M := M) (α := α) (q := q) (j := j) (s := s) hα hok hct hu hw
        (Fin.castLE (Nat.succ_le_succ hL) l.succ) (by rw [hval]; omega)
        (by rw [hval]; exact hne ((l : ℕ) + 1) (by omega) (by omega))
      rw [hval, show s + ((l : ℕ) + 1) = s + 1 + (l : ℕ) from by omega] at h
      exact h)
  rw [show s + L + 1 = s + 1 + L from by omega]
  unfold windowE
  refine TDeriv.seq ?_ (by simpa using hrest)
  have h0 := tderiv_roundITY (M := M) (α := α) (q := q) (elig := elig) (uv := uv) (wv := wv)
    hα hok hct hu hw (by omega) hj hel
  rwa [show (noiseWT (M := M) wv (0 : Fin (m + 1)))
    = noiseWT wv (Fin.castLE (Nat.succ_le_succ hL) (0 : Fin (L + 1))) from rfl] at h0

end DPFTRL.Band
