import Xhl.Examples.DPFTRLBanded.SampT
import Xhl.Logic.Rrhl.DerivedRules

open Continuous

/-!
# The rounds outside every window (Appendix E.5, (52), (54))

Between windows the histories differ on dead slots but agree on every slot alive or still
to be written (`HAgrK`).  So the record loop adds equal contributions, the release reads
only alive slots, and a round of `roundT` costs `1`, with coins and noise by [Samp] at
equal values.  `w` stays at its default (`roundT` never mentions it).
-/

open MeasureTheory ProbabilityTheory ENNReal
open Cmd hiding loc
open scoped NNReal


variable {ident : Type} {M : MemType ident}

namespace DPFTRL.Band

open Continuous

variable {d e n T : ℕ} {τ : Ty} [NeZero T]

section Mem

variable (p : TParams d e n T T τ) (v : TVars ident d T T τ) (tv : Vars ident .nat) {m : ℕ}
  (wv : Vars ident (.prod .bool (.vec ((m + 1) * d)))) (j : ℕ)

/-- **Outside a window**: the between-windows invariant, with the window-local variable at
    its default value on both sides. -/
def PQTm (k : ℕ) (mm : M.heap × M.heap) : Prop :=
  YKTm p v tv j k mm ∧ tWT wv mm.1 = default ∧ tWT wv mm.2 = default

/-- In the record loop of a round outside a window. -/
def PRTm (k i : ℕ) (mm : M.heap × M.heap) : Prop :=
  PQTm p v tv wv j k mm ∧ tIN v mm.1 = i ∧ tIN v mm.2 = i

end Mem

variable {p : TParams d e n T T τ} {v : TVars ident d T T τ} {tv : Vars ident .nat}
  {q : ℝ≥0} {elig : ℕ → ℕ → Bool} {uv : Vars ident .bool} {hok : TOK p v} {m : ℕ}
  {wv : Vars ident (.prod .bool (.vec ((m + 1) * d)))}

/-- The composable invariant of `SampT.lean` is the plain-round invariant, lifted. -/
lemma zKTm_iff_liftP_pQTm {j k : ℕ} (σ : St M × St M) :
    ZKTm p v tv wv j k σ ↔ liftP (PQTm p v tv wv j k) σ :=
  ⟨fun ⟨⟨h1, h2⟩, h3, h4⟩ => ⟨⟨h1, h3, h4⟩, h2⟩, fun ⟨⟨h1, h3, h4⟩, h2⟩ => ⟨⟨h1, h2⟩, h3, h4⟩⟩

/-! ## The record step -/

/-- `i := i + 1`. -/
lemma tderiv_incT_plain {α : ℝ} (hok : TOK p v) (hct : TCntOK v tv)
    (hw : WOKT v tv uv wv) {j : ℕ} (k i : ℕ) :
    TDeriv (M := M) α (liftP (PRTm p v tv wv j k i)) (fun _ => 1)
      (Cmd.assign v.i (incW v.i)) (Cmd.assign v.i (incW v.i))
      (liftP (PRTm p v tv wv j k (i + 1))) (fun _ => 1) := by
  refine tderiv_assign_same (α := α) v.i (incW v.i) 1 _ _ (fun mm hmm => ?_)
  obtain ⟨⟨hK, hw1, hw2⟩, hi1, hi2⟩ := hmm
  have e1 : tIN v mm.1 = i := hi1
  have e2 : tIN v mm.2 = i := hi2
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · show YKT p j k (obsT v tv (M.set mm.1 .nat v.i.name _))
      (obsT v tv (M.set mm.2 .nat v.i.name _))
    rw [obsT_set_i (hct := hct), obsT_set_i (hct := hct)]
    exact hK
  · show tWT wv (M.set mm.1 .nat v.i.name (esem (incW v.i) mm.1)) = default
    rw [tWT_set_i hw]; exact hw1
  · show tWT wv (M.set mm.2 .nat v.i.name (esem (incW v.i) mm.2)) = default
    rw [tWT_set_i hw]; exact hw2
  · show M.get (M.set mm.1 .nat v.i.name (esem (incW v.i) mm.1)) .nat v.i.name = i + 1
    rw [M.get_set_eq]
    show tIN v mm.1 + 1 = i + 1
    rw [e1]
  · show M.get (M.set mm.2 .nat v.i.name (esem (incW v.i) mm.2)) .nat v.i.name = i + 1
    rw [M.get_set_eq]
    show tIN v mm.2 + 1 = i + 1
    rw [e2]

/-- Resetting the coin disturbs nothing the plain invariant reads. -/
lemma PRTm_set_u (hu : UOK v tv tv uv) (hw : WOKT v tv uv wv) {j : ℕ}
    {k i : ℕ} (mm : M.heap × M.heap) (b₁ b₂ : Bool) :
    PRTm p v tv wv j k i (M.set mm.1 .bool uv.name b₁, M.set mm.2 .bool uv.name b₂)
      ↔ PRTm p v tv wv j k i mm := by
  unfold PRTm PQTm YKTm
  rw [obsT_set_u (hu := hu), obsT_set_u (hu := hu), tWT_set_u hw, tWT_set_u hw]
  show _ ∧ tIN v (M.set mm.1 .bool uv.name b₁) = i ∧ tIN v (M.set mm.2 .bool uv.name b₂) = i
    ↔ _
  rw [show tIN v (M.set mm.1 .bool uv.name b₁) = tIN v mm.1 from
      get_set_other _ _ hu.ui,
    show tIN v (M.set mm.2 .bool uv.name b₂) = tIN v mm.2 from
      get_set_other _ _ hu.ui]

/-- **A record step outside a window**: equal coins, equal priors, equal contributions. -/
lemma tderiv_recT_plain {α : ℝ} (hα : 1 < α) (hok : TOK p v)
    (hct : TCntOK v tv) (hu : UOK v tv tv uv)
    (hw : WOKT v tv uv wv) {j : ℕ} (k i : ℕ)
    (hij : i = j → elig j k = false) :
    TDeriv (M := M) α (liftP (PRTm p v tv wv j k i)) (fun _ => 1)
      (recBT p v tv q elig uv hok) (recBT p v tv q elig uv hok)
      (liftP (PRTm p v tv wv j k (i + 1))) (fun _ => 1) := by
  have hesem : ∀ a : M.heap, esem (eligE (M := M) v tv elig) a = elig (tIN v a) (tT tv a) :=
    fun _ => rfl
  set P := PRTm p v tv wv j k i with hP
  unfold recBT
  refine TDeriv.seq ?_ (tderiv_incT_plain hok hct hw k i)
  refine TDeriv.if_ (fun σ hσ => ?_) ?_ ?_
  · obtain ⟨⟨⟨hK, -, -⟩, hi1, hi2⟩, -⟩ := hσ
    have e1 : tIN v σ.1.1 = i := hi1
    have e2 : tIN v σ.2.1 = i := hi2
    have e3 : tT tv σ.1.1 = k := hK.2.2.2.2.1
    have e4 : tT tv σ.2.1 = k := hK.2.2.2.2.2
    rw [hesem, hesem, e1, e2, e3, e4]
  · by_cases hel : elig i k = true
    · have hij' : i ≠ j := fun h => by subst h; rw [hij rfl] at hel; exact Bool.false_ne_true hel
      have hcoin : TDeriv (M := M) α (liftP P) (fun _ => 1)
          (Cmd.random uv (bernoulliKernel q)) (Cmd.random uv (bernoulliKernel q))
          (liftP (fun mm => P mm ∧ M.get mm.1 .bool uv.name = M.get mm.2 .bool uv.name))
          (fun _ => 1) := by
        refine TDeriv.rnd hα uv uv _ _ _ _ _ (fun _ => 1) (fun σ hσ => Filter.Eventually.of_forall fun b => ?_) (fun σ hσ => ?_)
        · refine ⟨⟨(PRTm_set_u hu hw _ b b).mpr hσ.1, ?_⟩, hσ.2⟩
          show M.get (M.set σ.1.1 .bool uv.name b) .bool uv.name
            = M.get (M.set σ.2.1 .bool uv.name b) .bool uv.name
          rw [M.get_set_eq, M.get_set_eq]
        · rw [weightedHellingerIntegral_one, bernoulliKernel_apply, bernoulliKernel_apply, hellingerIntegral_self_prob]
      have hhist : TDeriv (M := M) α
          (liftP (fun mm => P mm ∧ M.get mm.1 .bool uv.name = M.get mm.2 .bool uv.name))
          (fun _ => 1) (Cmd.assign v.H (histE p v tv uv hok)) (Cmd.assign v.H (histE p v tv uv hok))
          (liftP (fun mm => P (M.set mm.1 .bool uv.name default,
            M.set mm.2 .bool uv.name default))) (fun _ => 1) := by
        refine tderiv_assign_same (α := α) v.H (histE p v tv uv hok) 1 _ _ (fun mm hmm => ?_)
        obtain ⟨⟨⟨hK, hw1, hw2⟩, hi1, hi2⟩, hcn⟩ := hmm
        obtain ⟨hadj, hx, hy, hHagr, ht1, ht2⟩ := hK
        refine (PRTm_set_u hu hw (M.set mm.1 (.vec (T * d)) v.H.name _,
          M.set mm.2 (.vec (T * d)) v.H.name _) default default).mpr ?_
        have e1 : tIN v mm.1 = i := hi1
        have e2 : tIN v mm.2 = i := hi2
        have e3 : tT tv mm.1 = k := ht1
        have e4 : tT tv mm.2 = k := ht2
        have hxe : tX v mm.1 = tX v mm.2 := hx
        have hadj' : ∀ t', t' ≠ j → p.record (tD v mm.1) t' = p.record (tD v mm.2) t' :=
          hadj.agree
        have hHagr' : HAgrK p.C k (tH v mm.1) (tH v mm.2) := hHagr
        -- the two increments agree
        have hinc : (if M.get mm.2 .bool uv.name then (1 : ℝ) else 0)
              • clipV p.Cl (p.grad (tX v mm.2) (p.record (tD v mm.2) (tIN v mm.2)))
            = (if M.get mm.1 .bool uv.name then (1 : ℝ) else 0)
              • clipV p.Cl (p.grad (tX v mm.1) (p.record (tD v mm.1) (tIN v mm.1))) := by
          rw [hcn, hxe, e1, e2, hadj' i hij']
        refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
        · show YKT p j k (obsT v tv (M.set mm.1 (.vec (T * d)) v.H.name _))
            (obsT v tv (M.set mm.2 (.vec (T * d)) v.H.name _))
          rw [obsT_set_H (hct := hct), obsT_set_H (hct := hct)]
          refine ⟨hadj, hx, hy, ?_, ht1, ht2⟩
          rw [esem_histE_eq, esem_histE_eq, e3, e4, hinc]
          refine hAgrK_write hHagr' (Fin.ofNat T k) (fun htr => ?_)
          rw [blk_eq_of_hAgrK hHagr' htr]
        · show tWT wv (M.set mm.1 (.vec (T * d)) v.H.name (esem (histE p v tv uv hok) mm.1))
            = default
          rw [tWT_set_H hw]; exact hw1
        · show tWT wv (M.set mm.2 (.vec (T * d)) v.H.name (esem (histE p v tv uv hok) mm.2))
            = default
          rw [tWT_set_H hw]; exact hw2
        · show tIN v (M.set mm.1 (.vec (T * d)) v.H.name (esem (histE p v tv uv hok) mm.1)) = i
          obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17,
            h18, h19, h20, h21⟩ := v.ne
          simp only [get_set_other _ _ (Ne.symm h17)]
          exact hi1
        · show tIN v (M.set mm.2 (.vec (T * d)) v.H.name (esem (histE p v tv uv hok) mm.2)) = i
          obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17,
            h18, h19, h20, h21⟩ := v.ne
          simp only [get_set_other _ _ (Ne.symm h17)]
          exact hi2
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
      exact (PRTm_set_u hu hw (σ.1.1, σ.2.1) default default).mpr hP1
    · refine tderiv_of_false _ ?_ (fun σ hσ => hel ?_)
      · exact ⟨trivial, trivial⟩
      · obtain ⟨⟨⟨⟨hK, -, -⟩, hi1, -⟩, -⟩, hg⟩ := hσ
        have e1 : tIN v σ.1.1 = i := hi1
        have e3 : tT tv σ.1.1 = k := hK.2.2.2.2.1
        rw [hesem, e1, e3] at hg; exact hg
  · exact TDeriv.conseq (fun σ hσ => hσ.1) (fun _ _ => le_rfl) (fun _ h => h) (fun _ _ => le_rfl)
      (TDeriv.skip _ _)

/-! ## The round -/

/-- `i := 0`. -/
lemma tderiv_iInitT_plain {α : ℝ} (hct : TCntOK v tv)
    (hw : WOKT v tv uv wv) {j : ℕ} (k : ℕ) :
    TDeriv (M := M) α (liftP (PQTm p v tv wv j k)) (fun _ => 1)
      (Cmd.assign v.i (Expr.cst (t := .nat) 0)) (Cmd.assign v.i (Expr.cst (t := .nat) 0))
      (liftP (PRTm p v tv wv j k 0)) (fun _ => 1) := by
  refine tderiv_assign_same (α := α) v.i (Expr.cst (t := .nat) 0) 1 _ _ (fun mm hmm => ?_)
  obtain ⟨hK, hw1, hw2⟩ := hmm
  refine ⟨⟨?_, ?_, ?_⟩, M.get_set_eq _ _ _ _, M.get_set_eq _ _ _ _⟩
  · show YKT p j k (obsT v tv (M.set mm.1 .nat v.i.name _))
      (obsT v tv (M.set mm.2 .nat v.i.name _))
    rw [obsT_set_i (hct := hct), obsT_set_i (hct := hct)]
    exact hK
  · show tWT wv (M.set mm.1 .nat v.i.name (esem (Expr.cst (t := Ty.nat) 0) mm.1)) = default
    rw [tWT_set_i hw]; exact hw1
  · show tWT wv (M.set mm.2 .nat v.i.name (esem (Expr.cst (t := Ty.nat) 0) mm.2)) = default
    rw [tWT_set_i hw]; exact hw2

/-- The record loop. -/
lemma tderiv_loopT_plain {α : ℝ} (hα : 1 < α) (hok : TOK p v)
    (hct : TCntOK v tv) (hu : UOK v tv tv uv)
    (hw : WOKT v tv uv wv) {j : ℕ} (k : ℕ)
    (hne : elig j k = false) :
    TDeriv (M := M) α (liftP (PRTm p v tv wv j k 0)) (fun _ => 1)
      (Cmd.while (ltCE v.i n) (recBT p v tv q elig uv hok))
      (Cmd.while (ltCE v.i n) (recBT p v tv q elig uv hok))
      (liftP (PRTm p v tv wv j k n)) (fun _ => 1) := by
  have hesem : ∀ a : M.heap, esem (ltCE (M := M) v.i n) a = decide (tIN v a < n) :=
    fun _ => rfl
  refine tderiv_while_count (α := α) n (fun i => liftP (PRTm p v tv wv j k i))
    (fun _ _ => 1) (fun i _ => tderiv_recT_plain hα hok hct hu hw k i (fun _ => hne))
    (fun i σ hσ hi => ?_) (fun σ hσ => ?_)
  · obtain ⟨⟨-, hi1, hi2⟩, -⟩ := hσ
    have e1 : tIN v σ.1.1 = i := hi1
    have e2 : tIN v σ.2.1 = i := hi2
    exact ⟨by rw [hesem, e1, decide_eq_true_iff]; omega,
      by rw [hesem, e2, decide_eq_true_iff]; omega⟩
  · obtain ⟨⟨-, hi1, hi2⟩, -⟩ := hσ
    have e1 : tIN v σ.1.1 = n := hi1
    have e2 : tIN v σ.2.1 = n := hi2
    refine ⟨?_, ?_⟩
    · rw [hesem, e1, decide_eq_false_iff_not]; exact lt_irrefl n
    · rw [hesem, e2, decide_eq_false_iff_not]; exact lt_irrefl n

/-- **A round outside every window**, at budget `1`, on the program's own round. -/
theorem tderiv_roundT_plain {α : ℝ} (hα : 1 < α) (hok : TOK p v)
    (hct : TCntOK v tv) (hu : UOK v tv tv uv)
    (hw : WOKT v tv uv wv)
    {j : ℕ} (k : ℕ) (hkT : k < T)
    (hne : elig j k = false) :
    TDeriv (M := M) α (liftP (PQTm p v tv wv j k)) (fun _ => 1)
      (roundT p v tv q elig uv hok) (roundT p v tv q elig uv hok)
      (liftP (PQTm p v tv wv j (k + 1))) (fun _ => 1) := by
  -- the noise, drawn at equal values
  have hz : TDeriv (M := M) α (liftP (PRTm p v tv wv j k n)) (fun _ => 1)
      (Cmd.random v.z (noiseKernelE p.σ2)) (Cmd.random v.z (noiseKernelE p.σ2))
      (liftP (fun mm => PQTm p v tv wv j k mm ∧ tZ v mm.1 = tZ v mm.2)) (fun _ => 1) := by
    refine TDeriv.rnd hα v.z v.z _ _ _ _ _ (fun _ => 1) (fun σ hσ => Filter.Eventually.of_forall fun z => ?_) (fun σ hσ => ?_)
    · obtain ⟨⟨⟨hK, hw1, hw2⟩, -, -⟩, htr⟩ := hσ
      refine ⟨⟨⟨?_, ?_, ?_⟩, ?_⟩, htr⟩
      · show YKT p j k (obsT v tv (M.set σ.1.1 (.vec d) v.z.name z))
          (obsT v tv (M.set σ.2.1 (.vec d) v.z.name z))
        rw [obsT_set_z (hct := hct), obsT_set_z (hct := hct)]
        exact hK
      · show tWT wv (M.set σ.1.1 (.vec d) v.z.name z) = default
        rw [tWT_set_z hw]; exact hw1
      · show tWT wv (M.set σ.2.1 (.vec d) v.z.name z) = default
        rw [tWT_set_z hw]; exact hw2
      · show tZ v (M.set σ.1.1 (.vec d) v.z.name z) = tZ v (M.set σ.2.1 (.vec d) v.z.name z)
        simp only [M.get_set_eq]
    · rw [weightedHellingerIntegral_one]
      simp only [noiseKernelE, gaussKernelE_apply]
      rw [hellingerIntegral_self_prob]
  -- the row: equal means, equal noises
  have hY : TDeriv (M := M) α
      (liftP (fun mm => PQTm p v tv wv j k mm ∧ tZ v mm.1 = tZ v mm.2)) (fun _ => 1)
      (Cmd.assign v.Y (relEM p.C v tv)) (Cmd.assign v.Y (relEM p.C v tv))
      (liftP (PQTm p v tv wv j k)) (fun _ => 1) := by
    refine tderiv_assign_same (α := α) v.Y (relEM p.C v tv) 1 _ _ (fun mm hmm => ?_)
    obtain ⟨⟨⟨hadj, hx, hy, hHagr, ht1, ht2⟩, hw1, hw2⟩, hze⟩ := hmm
    have hHagr' : HAgrK p.C k (tH v mm.1) (tH v mm.2) := hHagr
    have hYe : tY v mm.1 = tY v mm.2 := hy
    have e1 : tT tv mm.1 = k := ht1
    have e2 : tT tv mm.2 = k := ht2
    refine ⟨?_, ?_, ?_⟩
    · show YKT p j k (obsT v tv (M.set mm.1 (.vec (T * d)) v.Y.name _))
        (obsT v tv (M.set mm.2 (.vec (T * d)) v.Y.name _))
      rw [obsT_set_Y (hct := hct), obsT_set_Y (hct := hct)]
      refine ⟨hadj, hx, ?_, hHagr, ht1, ht2⟩
      have hmean : rowMean p.C (Fin.ofNat T k) (tH v mm.1)
          = rowMean p.C (Fin.ofNat T k) (tH v mm.2) :=
        rowMean_eq_of_hAgrK (p := p) hHagr' (Fin.ofNat T k) (by simp [Nat.mod_eq_of_lt hkT])
      show setBlk (tY v mm.1) (Fin.ofNat T (tT tv mm.1))
          (rowMean p.C (Fin.ofNat T (tT tv mm.1)) (tH v mm.1) + tZ v mm.1)
        = setBlk (tY v mm.2) (Fin.ofNat T (tT tv mm.2))
          (rowMean p.C (Fin.ofNat T (tT tv mm.2)) (tH v mm.2) + tZ v mm.2)
      rw [hYe, e1, e2, hze, hmean]
    · show tWT wv (M.set mm.1 (.vec (T * d)) v.Y.name (esem (relEM p.C v tv) mm.1)) = default
      rw [tWT_set_Y hw]; exact hw1
    · show tWT wv (M.set mm.2 (.vec (T * d)) v.Y.name (esem (relEM p.C v tv) mm.2)) = default
      rw [tWT_set_Y hw]; exact hw2
  -- `ŝ := (B·Y)_t`: equal rows, equal prefix sums
  have hacc : TDeriv (M := M) α (liftP (PQTm p v tv wv j k)) (fun _ => 1)
      (Cmd.assign v.acc (sumEM p v tv)) (Cmd.assign v.acc (sumEM p v tv))
      (liftP (fun mm => PQTm p v tv wv j k mm ∧ tA v mm.1 = tA v mm.2)) (fun _ => 1) := by
    refine tderiv_assign_same (α := α) v.acc (sumEM p v tv) 1 _ _ (fun mm hmm => ?_)
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · show YKT p j k (obsT v tv (M.set mm.1 (.vec d) v.acc.name _))
        (obsT v tv (M.set mm.2 (.vec d) v.acc.name _))
      rw [obsT_set_acc (hct := hct), obsT_set_acc (hct := hct)]
      exact hmm.1
    · show tWT wv (M.set mm.1 (.vec d) v.acc.name (esem (sumEM p v tv) mm.1)) = default
      rw [tWT_set_acc hw]; exact hmm.2.1
    · show tWT wv (M.set mm.2 (.vec d) v.acc.name (esem (sumEM p v tv) mm.2)) = default
      rw [tWT_set_acc hw]; exact hmm.2.2
    · obtain ⟨⟨-, -, hy, -, ht1, ht2⟩, -, -⟩ := hmm
      have hYe : tY v mm.1 = tY v mm.2 := hy
      have e1 : tT tv mm.1 = k := ht1
      have e2 : tT tv mm.2 = k := ht2
      show M.get (M.set mm.1 (.vec d) v.acc.name (esem (sumEM p v tv) mm.1)) (.vec d) v.acc.name
        = M.get (M.set mm.2 (.vec d) v.acc.name (esem (sumEM p v tv) mm.2)) (.vec d) v.acc.name
      rw [M.get_set_eq, M.get_set_eq]
      show rowDec p (tT tv mm.1) (tY v mm.1) = rowDec p (tT tv mm.2) (tY v mm.2)
      rw [hYe, e1, e2]
  -- `θ := −(1/λ)·ŝ`: equal prefix sums, equal models
  have hmod : TDeriv (M := M) α
      (liftP (fun mm => PQTm p v tv wv j k mm ∧ tA v mm.1 = tA v mm.2)) (fun _ => 1)
      (Cmd.assign v.x (modelEM p v)) (Cmd.assign v.x (modelEM p v))
      (liftP (PQTm p v tv wv j k)) (fun _ => 1) := by
    refine tderiv_assign_same (α := α) v.x (modelEM p v) 1 _ _ (fun mm hmm => ?_)
    obtain ⟨⟨⟨hadj, hx, hy, hHagr, ht1, ht2⟩, hw1, hw2⟩, hA⟩ := hmm
    refine ⟨?_, ?_, ?_⟩
    · show YKT p j k (obsT v tv (M.set mm.1 (.vec d) v.x.name _))
        (obsT v tv (M.set mm.2 (.vec d) v.x.name _))
      rw [obsT_set_x (hct := hct), obsT_set_x (hct := hct)]
      refine ⟨hadj, ?_, hy, hHagr, ht1, ht2⟩
      show (-(1 / p.lam)) • tA v mm.1 = (-(1 / p.lam)) • tA v mm.2
      rw [hA]
    · show tWT wv (M.set mm.1 (.vec d) v.x.name (esem (modelEM p v) mm.1)) = default
      rw [tWT_set_x hw]; exact hw1
    · show tWT wv (M.set mm.2 (.vec d) v.x.name (esem (modelEM p v) mm.2)) = default
      rw [tWT_set_x hw]; exact hw2
  -- the release of the model: equal models
  have hrel : TDeriv (M := M) α (liftP (PQTm p v tv wv j k)) (fun _ => 1)
      (Cmd.release (Expr.var v.x)) (Cmd.release (Expr.var v.x))
      (liftP (PQTm p v tv wv j k)) (fun _ => 1) :=
    tderiv_releaseX _ fun _ hmm => hmm.1.2.1
  -- `t := t + 1`
  have htinc : TDeriv (M := M) α (liftP (PQTm p v tv wv j k)) (fun _ => 1)
      (Cmd.assign tv (incW tv)) (Cmd.assign tv (incW tv))
      (liftP (PQTm p v tv wv j (k + 1))) (fun _ => 1) := by
    refine tderiv_assign_same (α := α) tv (incW tv) 1 _ _ (fun mm hmm => ?_)
    obtain ⟨⟨hadj, hx, hy, hHagr, ht1, ht2⟩, hw1, hw2⟩ := hmm
    have hHagr' : HAgrK p.C k (tH v mm.1) (tH v mm.2) := hHagr
    have e1 : tT tv mm.1 = k := ht1
    have e2 : tT tv mm.2 = k := ht2
    refine ⟨?_, ?_, ?_⟩
    · show YKT p j (k + 1) (obsT v tv (M.set mm.1 .nat tv.name (tT tv mm.1 + 1)))
        (obsT v tv (M.set mm.2 .nat tv.name (tT tv mm.2 + 1)))
      rw [obsT_set_t (hct := hct), obsT_set_t (hct := hct), e1, e2]
      exact ⟨hadj, hx, hy, hHagr'.mono (by omega), rfl, rfl⟩
    · show tWT wv (M.set mm.1 .nat tv.name (esem (incW tv) mm.1)) = default
      rw [tWT_set_t hw]; exact hw1
    · show tWT wv (M.set mm.2 .nat tv.name (esem (incW tv) mm.2)) = default
      rw [tWT_set_t hw]; exact hw2
  unfold roundT postT
  refine TDeriv.seq (tderiv_iInitT_plain hct hw k) ?_
  refine TDeriv.seq (tderiv_loopT_plain hα hok hct hu hw k hne) ?_
  refine TDeriv.seq (TDeriv.conseq (fun σ hσ => hσ) (fun _ _ => le_rfl) (fun _ h => h)
    (fun _ _ => le_rfl) hz) ?_
  exact TDeriv.seq hY (TDeriv.seq hacc (TDeriv.seq hmod (TDeriv.seq hrel htinc)))

end DPFTRL.Band
