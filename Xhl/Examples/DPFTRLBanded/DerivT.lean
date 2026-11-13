import Xhl.Examples.DPFTRLBanded.PlainT
import Xhl.Logic.Rrhl.DerivedRules
import Xhl.Divergence.Privacy

open Continuous

/-!
# Amplified banded DP-FTRL, as a derivation (Appendix E.5)

`dpftrlBandedGen` (Fig. 10) derived in `TDeriv`, the judgment (44), for any banded
eligibility (`BandElig`): the rounds `P_j = {t < T | elig j t}` of record `j` are
`(m+1)`-min-separated, so the windows of `m + 1` rounds they open do not overlap; the last
may be truncated by the end of the run.

* a round outside every window costs `1` (`tderiv_roundT_plain`, (52));
* the window at `ts l` costs `Υ_α(q, Γ·√(colSq (ts l)), σ²)` (`tderiv_windowT_rules`, (53));
* [Equiv] unrolls the `while` to `T` rounds ([E-Count]) and splits them into plain
  stretches and windows; the budgets multiply by [Seq].

`dpftrlBanded_gen_list_deriv` derives it over an enumeration `ts 0 < … < ts (K−1)` of
`P_j`, `dpftrlBanded_gen_deriv` on `elig` itself; `dpftrlBanded_gen_Hellinger` reads the
bound out by soundness on arbitrary adjacent memories (`tr_osem_eq_resetW`), and
`dpftrlBanded_gen_IndivRDP`/`dpftrlBanded_gen_uniform_IndivRDP` convert it (Prop. 4.4).
-/

open MeasureTheory ProbabilityTheory ENNReal
open scoped NNReal


variable {ident : Type} {M : MemType ident}

namespace DPFTRL.Band

open Continuous

variable {d e n T : ℕ} {τ : Ty} [NeZero T]

variable {p : TParams d e n T T τ} {v : TVars ident d T T τ} {tv : Vars ident .nat}
  {q : ℝ≥0} {elig : ℕ → ℕ → Bool} {uv : Vars ident .bool} {hok : TOK p v} {m : ℕ}
  {wv : Vars ident (.prod .bool (.vec ((m + 1) * d)))}

/-! ## The initial state -/

/-- **The entry condition**: the datasets are adjacent at `j`, and the window-local
    variable is at its default value.  Everything else is established by the initialization
    `θ := 0 ; H := 0 ; Y := 0`. -/
def XAWT (p : TParams d e n T T τ) (v : TVars ident d T T τ)
    (wv : Vars ident (.prod .bool (.vec ((m + 1) * d)))) (j : ℕ)
    (mm : M.heap × M.heap) : Prop :=
  AdjAtSym p.record j (tD v mm.1) (tD v mm.2) ∧ tWT wv mm.1 = default ∧ tWT wv mm.2 = default

/-- **After the initialization**: the datasets are adjacent at `j` (in either order), the
    models, aggregates and histories are equal, and the window-local variable is at its
    default value. -/
def XEWT (p : TParams d e n T T τ) (v : TVars ident d T T τ)
    (wv : Vars ident (.prod .bool (.vec ((m + 1) * d)))) (j : ℕ)
    (mm : M.heap × M.heap) : Prop :=
  AdjAtSym p.record j (tD v mm.1) (tD v mm.2) ∧ tX v mm.1 = tX v mm.2 ∧ tY v mm.1 = tY v mm.2 ∧
    tH v mm.1 = tH v mm.2 ∧ tWT wv mm.1 = default ∧ tWT wv mm.2 = default

/-- `t := 0` enters the between-windows invariant: equal histories agree everywhere. -/
lemma tderiv_initT {α : ℝ} (hct : TCntOK v tv)
    (hw : WOKT v tv uv wv) (j : ℕ) (η : ℝ≥0∞) :
    TDeriv (M := M) α (liftP (XEWT p v wv j)) (fun _ => η)
      (Cmd.assign tv (Expr.cst (t := .nat) 0)) (Cmd.assign tv (Expr.cst (t := .nat) 0))
      (ZKTm p v tv wv j 0) (fun _ => η) := by
  refine TDeriv.conseq (fun _ h => h) (fun _ _ => le_rfl)
    (fun σ hσ => (zKTm_iff_liftP_pQTm σ).mpr hσ) (fun _ _ => le_rfl) ?_
  refine tderiv_assign_same (α := α) tv (Expr.cst (t := .nat) 0) η _ _ (fun mm hmm => ?_)
  obtain ⟨hadj, hx, hy, hH, hw1, hw2⟩ := hmm
  refine ⟨?_, ?_, ?_⟩
  · show YKT p j 0 (obsT v tv (M.set mm.1 .nat tv.name _))
      (obsT v tv (M.set mm.2 .nat tv.name _))
    rw [obsT_set_t (hct := hct), obsT_set_t (hct := hct)]
    exact ⟨hadj, hx, hy, hAgrK_of_eq hH 0, rfl, rfl⟩
  · show tWT wv (M.set mm.1 .nat tv.name (esem (Expr.cst (t := Ty.nat) 0) mm.1)) = default
    rw [tWT_set_t hw]; exact hw1
  · show tWT wv (M.set mm.2 .nat tv.name (esem (Expr.cst (t := Ty.nat) 0) mm.2)) = default
    rw [tWT_set_t hw]; exact hw2

/-! ## The program, derived -/

/-- **The program, derived, over an enumeration of the participations.**  Record `j` is
    eligible exactly at the rounds of a `(m+1)`-separated list `ts 0 < … < ts (K−1)`
    inside the run, and every row reading the slot `ts l` is due within `m` rounds
    (`hlast`).  The budget is one factor `blockSymBudgetM = max(Υ, Λ)` per window. -/
theorem dpftrlBanded_gen_list_deriv {α : ℝ} (hα : 1 < α) (hok : TOK p v)
    (hct : TCntOK v tv) (hu : UOK v tv tv uv)
    (hw : WOKT v tv uv wv) (sc : WScratchT v tv uv wv) (hq : q ≤ 1) (hv : p.σ2 ≠ 0) (hC : 0 ≤ p.Cl)
    {j : ℕ} (hj : j < n)
    (ts : ℕ → ℕ) (K : ℕ)
    (hsep : ∀ l, l + 1 < K → ts l + m + 1 ≤ ts (l + 1))
    (hlt : ∀ l, l < K → ts l < T)
    (hstart : ∀ l, l < K → elig j (ts l) = true)
    (hmid : ∀ l, l < K → ∀ r, 1 ≤ r → r ≤ m → ts l + r < T → elig j (ts l + r) = false)
    (hoff : ∀ k, k < T → (∀ l, l < K → k < ts l ∨ ts l + m < k) → elig j k = false)
    (hlast : ∀ l, l < K → lastB p.C (Fin.ofNat T (ts l)) ≤ ts l + m) :
    TDeriv (M := M) α (liftP (XAWT p v wv j))
      (fun _ => ∏ l ∈ Finset.range K, blockSymBudgetM p q α m (ts l))
      (dpftrlBandedGen p v tv q elig uv hok) (dpftrlBandedGen p v tv q elig uv hok)
      (ZKTm p v tv wv j T) (fun _ => 1) := by
  have hqR : (q : ℝ) ≤ 1 := by exact_mod_cast hq
  set Υ : ℕ → ℝ≥0∞ := fun l => blockSymBudgetM p q α m (ts l) with hΥ
  have hΥ0 : ∀ l, Υ l ≠ 0 :=
    fun l => ne_of_gt (lt_of_lt_of_le zero_lt_one
      ((one_le_mixBudgetR hα hv hqR _).trans (le_max_left _ _)))
  have hΥt : ∀ l, Υ l ≠ ⊤ := fun l => by
    simp only [hΥ, blockSymBudgetM_eq hα hv hq]; exact mixBudgetR_ne_top hα _ _ hv hqR
  set B : ℕ → ℝ≥0∞ := fun l => ∏ i ∈ Finset.Ico l K, Υ i with hB
  have hB0 : ∀ l, B l ≠ 0 := fun l => Finset.prod_ne_zero_iff.mpr fun i _ => hΥ0 i
  have hBt : ∀ l, B l ≠ ⊤ := fun l => ENNReal.prod_ne_top fun i _ => hΥt i
  -- the list is monotone
  have hmono : ∀ a b, a ≤ b → b < K → ts a ≤ ts b := by
    intro a b hab hbK
    obtain ⟨c, rfl⟩ : ∃ c, b = a + c := ⟨b - a, by omega⟩
    clear hab
    revert hbK
    induction c with
    | zero => intro _; exact le_rfl
    | succ c ih =>
      intro hbK
      have h1 := ih (by omega)
      have h2 := hsep (a + c) (by omega)
      show ts a ≤ ts ((a + c) + 1)
      omega
  -- a stretch of rounds outside every window, at budget `1`
  have hplainSeg : ∀ s len : ℕ, s + len ≤ T → (∀ i, i < len → elig j (s + i) = false) →
      TDeriv (M := M) α (ZKTm p v tv wv j s) (fun _ => (1 : ℝ≥0∞))
        (iterCmd (roundT p v tv q elig uv hok) len) (iterCmd (roundT p v tv q elig uv hok) len)
        (ZKTm p v tv wv j (s + len)) (fun _ => 1) := by
    intro s len hsl hoffi
    have h := tderiv_iterCmd_family (M := M) (α := α)
      (fun k => liftP (PQTm p v tv wv j (s + k))) (fun _ _ => 1) len
      (fun k hk => tderiv_roundT_plain (M := M) (q := q) hα hok hct hu hw (s + k) (by omega)
        (hoffi k hk)) len 0 (by omega)
    simp only [zero_add] at h
    exact TDeriv.conseq (fun σ hσ => (zKTm_iff_liftP_pQTm σ).mp hσ) (fun _ _ => le_rfl)
      (fun σ hσ => (zKTm_iff_liftP_pQTm σ).mpr hσ) (fun _ _ => le_rfl) h
  -- the suffix from any between-windows position, by induction on the remaining windows
  have aux : ∀ fuel l, l ≤ K → K - l = fuel → ∀ s, s ≤ T →
      (∀ l', l' < l → ts l' + m + 1 ≤ s ∨ T ≤ s) → (l < K → s ≤ ts l) →
      TDeriv (M := M) α (ZKTm p v tv wv j s) (fun _ => B l)
        (iterCmd (roundT p v tv q elig uv hok) (T - s))
        (iterCmd (roundT p v tv q elig uv hok) (T - s))
        (ZKTm p v tv wv j T) (fun _ => 1) := by
    intro fuel
    induction fuel with
    | zero =>
      intro l hlK hf s hsT' hpast _
      have hlK' : l = K := by omega
      subst hlK'
      have hpl := hplainSeg s (T - s) (by omega)
        (fun i hi => hoff (s + i) (by omega)
          (fun l' hl' => Or.inr (by have := hpast l' hl'; omega)))
      rw [show s + (T - s) = T by omega] at hpl
      refine TDeriv.conseq (fun _ h => h) (fun _ _ => le_of_eq ?_) (fun _ h => h)
        (fun _ _ => le_rfl) hpl
      simp [hB]
    | succ f ih =>
      intro l hlK hf s hsT' hpast hnext
      have hlK' : l < K := by omega
      have hts_l : s ≤ ts l := hnext hlK'
      have hlt_l : ts l < T := hlt l hlK'
      -- the window has `L + 1` rounds: `m + 1`, or fewer when the run ends first
      obtain ⟨L, hLm, hLT, hLfull, hLtr⟩ : ∃ L, L ≤ m ∧ ts l + L < T ∧
          (ts l + m + 1 ≤ T → L = m) ∧ (T < ts l + m + 1 → ts l + L + 1 = T) := by
        rcases Nat.lt_or_ge T (ts l + m + 1) with h | h
        · exact ⟨T - ts l - 1, by omega, by omega, fun h' => absurd h' (Nat.not_le.mpr h),
            fun _ => by omega⟩
        · exact ⟨m, le_rfl, by omega, fun _ => rfl, fun h' => absurd h' (by omega)⟩
      -- the plain stretch up to the window
      have hpl := hplainSeg s (ts l - s) (by omega)
        (fun i hi => hoff (s + i) (by omega)
          (fun l' hl' => by
            rcases Nat.lt_or_ge l' l with h' | h'
            · exact Or.inr (by have := hpast l' h'; omega)
            · exact Or.inl (by have := hmono l l' h' hl'; omega)))
      rw [show s + (ts l - s) = ts l by omega] at hpl
      have hplS := TDeriv.scale (hB0 l) (hBt l) hpl
      -- the window: its slot is dead by its end — by the band when it is whole, by the
      -- end of the run when it is truncated
      have hlast' : lastB p.C (Fin.ofNat T (ts l)) < ts l + L + 1 := by
        have h1 := hlast l hlK'
        have h2 := lastB_lt p.C (Fin.ofNat T (ts l))
        rcases Nat.lt_or_ge T (ts l + m + 1) with h | h
        · have := hLtr h; omega
        · have := hLfull h; omega
      have hwin := tderiv_windowT_rules (M := M) hα hok hct hu hw sc hq hv hC hj (ts l) L hLm
        hLT (hstart l hlK') (fun r hr1 hr2 => hmid l hlK' r hr1 (by omega) (by omega)) hlast'
      have hwinS := TDeriv.scale (hB0 (l + 1)) (hBt (l + 1)) hwin
      -- the rest
      have hih := ih (l + 1) (by omega) (by omega) (ts l + L + 1) (by omega)
        (fun l' hl' => by
          rcases Nat.lt_or_ge l' l with h' | h'
          · rcases hpast l' h' with h'' | h'' <;> omega
          · obtain rfl : l' = l := by omega
            rcases Nat.lt_or_ge T (ts l' + m + 1) with h | h
            · have := hLtr h; omega
            · have := hLfull h; omega)
        (fun h1K => by have := hsep l h1K; omega)
      have hBl : B l = Υ l * B (l + 1) := by
        simp only [hB]; exact Finset.prod_eq_prod_Ico_succ_bot hlK' _
      -- [Equiv]: the suffix is the stretch, the window, and the rest
      have hsplit : ∀ R : St M → Prop, CEquiv R
          (iterCmd (roundT (M := M) p v tv q elig uv hok) (T - s))
          (Cmd.seq (iterCmd (roundT p v tv q elig uv hok) (ts l - s))
            (Cmd.seq (iterCmd (roundT p v tv q elig uv hok) (L + 1))
              (iterCmd (roundT p v tv q elig uv hok) (T - (ts l + L + 1))))) := by
        intro R
        rw [show T - s = (ts l - s) + ((L + 1) + (T - (ts l + L + 1))) by omega]
        exact CEquiv.iterCmd_split _ _ _ R
      refine TDeriv.equiv (hsplit (fun _ => True)) (hsplit (fun _ => True))
        (fun _ _ => ⟨trivial, trivial⟩) ?_
      refine TDeriv.seq (TDeriv.conseq (fun _ h => h) (fun _ _ => le_of_eq (mul_one _))
        (fun _ h => h) (fun _ _ => le_of_eq (mul_one _).symm) hplS) ?_
      refine TDeriv.seq (TDeriv.conseq (fun _ h => h) (fun _ _ => le_of_eq ?_)
        (fun _ h => h) (fun _ _ => le_of_eq (mul_one _).symm) hwinS) hih
      rw [hBl, mul_comm]
  -- [Equiv]: the `while` is `T` rounds
  have hloop : TDeriv (M := M) α (ZKTm p v tv wv j 0) (fun _ => B 0)
      (Cmd.while (ltCE tv T) (roundT p v tv q elig uv hok))
      (Cmd.while (ltCE tv T) (roundT p v tv q elig uv hok))
      (ZKTm p v tv wv j T) (fun _ => 1) := by
    have hcount : IncLast tv (roundT (M := M) p v tv q elig uv hok) :=
      ⟨Ne.symm hct.ti, Or.inr ⟨⟨⟨⟨hu.ut, hu.ut, Ne.symm hct.tH⟩, trivial⟩, Ne.symm hct.ti⟩,
        Or.inr ⟨Ne.symm hct.tz, Or.inr ⟨Ne.symm hct.tY, Or.inr ⟨Ne.symm hct.tacc,
          Or.inr ⟨Ne.symm hct.tx, Or.inr ⟨trivial, Or.inl rfl⟩⟩⟩⟩⟩⟩⟩
    -- **[E-Count]**: the loop's own counter bounds the unrolling
    have hunroll : ∀ R : St M → Prop, (∀ y : St M, R y → tT tv y.1 = 0) →
        CEquiv R (Cmd.while (ltCE tv T) (roundT p v tv q elig uv hok))
          (iterCmd (roundT p v tv q elig uv hok) T) := fun R hR =>
      CEquiv.weaken (fun y hy => by show tT tv y.1 + T = T; rw [hR y hy]; omega)
        (CEquiv.count tv T hcount T)
    refine TDeriv.equiv
      (hunroll (fun y => tT tv y.1 = 0) (fun _ h => h))
      (hunroll (fun y => tT tv y.1 = 0) (fun _ h => h))
      (fun _ hσ => ⟨hσ.1.1.2.2.2.2.1, hσ.1.1.2.2.2.2.2⟩) ?_
    exact aux (K - 0) 0 (Nat.zero_le K) rfl 0 (Nat.zero_le T)
      (fun l' hl' => absurd hl' (Nat.not_lt_zero l')) (fun _ => Nat.zero_le _)
  have hB0' : B 0 = ∏ l ∈ Finset.range K, blockSymBudgetM p q α m (ts l) := by
    simp only [hB, hΥ]; rw [Finset.range_eq_Ico]
  -- the initialization `θ := 0 ; H := 0 ; Y := 0`
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21⟩ := v.ne
  have hx0 : TDeriv (M := M) α (liftP (XAWT p v wv j)) (fun _ => B 0)
      (Cmd.assign v.x (Expr.cst (t := .vec d) 0)) (Cmd.assign v.x (Expr.cst (t := .vec d) 0))
      (liftP (fun mm => AdjAtSym p.record j (tD v mm.1) (tD v mm.2) ∧ tX v mm.1 = tX v mm.2 ∧
        tWT wv mm.1 = default ∧ tWT wv mm.2 = default)) (fun _ => B 0) :=
    tderiv_assign_same v.x _ _ _ _ (fun mm hmm => by
      obtain ⟨hadj, hw1, hw2⟩ := hmm
      refine ⟨?_, ?_, ?_, ?_⟩
      · show AdjAtSym p.record j (M.get (M.set mm.1 (.vec d) v.x.name 0) τ v.D.name)
          (M.get (M.set mm.2 (.vec d) v.x.name 0) τ v.D.name)
        rw [get_set_other _ _ h4, get_set_other _ _ h4]; exact hadj
      · show M.get (M.set mm.1 (.vec d) v.x.name 0) (.vec d) v.x.name
          = M.get (M.set mm.2 (.vec d) v.x.name 0) (.vec d) v.x.name
        rw [M.get_set_eq, M.get_set_eq]
      · show tWT wv (M.set mm.1 (.vec d) v.x.name 0) = default
        rw [tWT_set_x hw]; exact hw1
      · show tWT wv (M.set mm.2 (.vec d) v.x.name 0) = default
        rw [tWT_set_x hw]; exact hw2)
  have hH0 : TDeriv (M := M) α
      (liftP (fun mm => AdjAtSym p.record j (tD v mm.1) (tD v mm.2) ∧ tX v mm.1 = tX v mm.2 ∧
        tWT wv mm.1 = default ∧ tWT wv mm.2 = default)) (fun _ => B 0)
      (Cmd.assign v.H (Expr.cst (t := .vec (T * d)) 0))
      (Cmd.assign v.H (Expr.cst (t := .vec (T * d)) 0))
      (liftP (fun mm => AdjAtSym p.record j (tD v mm.1) (tD v mm.2) ∧ tX v mm.1 = tX v mm.2 ∧
        tH v mm.1 = tH v mm.2 ∧ tWT wv mm.1 = default ∧ tWT wv mm.2 = default))
      (fun _ => B 0) :=
    tderiv_assign_same v.H _ _ _ _ (fun mm hmm => by
      obtain ⟨hadj, hx, hw1, hw2⟩ := hmm
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · show AdjAtSym p.record j (M.get (M.set mm.1 (.vec (T * d)) v.H.name 0) τ v.D.name)
          (M.get (M.set mm.2 (.vec (T * d)) v.H.name 0) τ v.D.name)
        rw [get_set_other _ _ (Ne.symm h19), get_set_other _ _ (Ne.symm h19)]; exact hadj
      · show M.get (M.set mm.1 (.vec (T * d)) v.H.name 0) (.vec d) v.x.name
          = M.get (M.set mm.2 (.vec (T * d)) v.H.name 0) (.vec d) v.x.name
        rw [get_set_other _ _ (Ne.symm h5), get_set_other _ _ (Ne.symm h5)]; exact hx
      · show M.get (M.set mm.1 (.vec (T * d)) v.H.name 0) (.vec (T * d)) v.H.name
          = M.get (M.set mm.2 (.vec (T * d)) v.H.name 0) (.vec (T * d)) v.H.name
        rw [M.get_set_eq, M.get_set_eq]
      · show tWT wv (M.set mm.1 (.vec (T * d)) v.H.name 0) = default
        rw [tWT_set_H hw]; exact hw1
      · show tWT wv (M.set mm.2 (.vec (T * d)) v.H.name 0) = default
        rw [tWT_set_H hw]; exact hw2)
  have hY0 : TDeriv (M := M) α
      (liftP (fun mm => AdjAtSym p.record j (tD v mm.1) (tD v mm.2) ∧ tX v mm.1 = tX v mm.2 ∧
        tH v mm.1 = tH v mm.2 ∧ tWT wv mm.1 = default ∧ tWT wv mm.2 = default))
      (fun _ => B 0)
      (Cmd.assign v.Y (Expr.cst (t := .vec (T * d)) 0))
      (Cmd.assign v.Y (Expr.cst (t := .vec (T * d)) 0))
      (liftP (XEWT p v wv j)) (fun _ => B 0) :=
    tderiv_assign_same v.Y _ _ _ _ (fun mm hmm => by
      obtain ⟨hadj, hx, hH, hw1, hw2⟩ := hmm
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · show AdjAtSym p.record j (M.get (M.set mm.1 (.vec (T * d)) v.Y.name 0) τ v.D.name)
          (M.get (M.set mm.2 (.vec (T * d)) v.Y.name 0) τ v.D.name)
        rw [get_set_other _ _ (Ne.symm h20), get_set_other _ _ (Ne.symm h20)]; exact hadj
      · show M.get (M.set mm.1 (.vec (T * d)) v.Y.name 0) (.vec d) v.x.name
          = M.get (M.set mm.2 (.vec (T * d)) v.Y.name 0) (.vec d) v.x.name
        rw [get_set_other _ _ (Ne.symm h6), get_set_other _ _ (Ne.symm h6)]; exact hx
      · show M.get (M.set mm.1 (.vec (T * d)) v.Y.name 0) (.vec (T * d)) v.Y.name
          = M.get (M.set mm.2 (.vec (T * d)) v.Y.name 0) (.vec (T * d)) v.Y.name
        rw [M.get_set_eq, M.get_set_eq]
      · show M.get (M.set mm.1 (.vec (T * d)) v.Y.name 0) (.vec (T * d)) v.H.name
          = M.get (M.set mm.2 (.vec (T * d)) v.Y.name 0) (.vec (T * d)) v.H.name
        rw [get_set_other _ _ (Ne.symm h21), get_set_other _ _ (Ne.symm h21)]; exact hH
      · show tWT wv (M.set mm.1 (.vec (T * d)) v.Y.name 0) = default
        rw [tWT_set_Y hw]; exact hw1
      · show tWT wv (M.set mm.2 (.vec (T * d)) v.Y.name 0) = default
        rw [tWT_set_Y hw]; exact hw2)
  unfold dpftrlBandedGen
  rw [← hB0']
  exact TDeriv.seq hx0 (TDeriv.seq hH0 (TDeriv.seq hY0
    (TDeriv.seq (tderiv_initT hct hw j (B 0)) hloop)))

/-! ## Banded eligibility -/

/-- The rounds at which record `j` is eligible, `P_j = {t < T | elig j t}`. -/
def partRounds (elig : ℕ → ℕ → Bool) (T j : ℕ) : Finset ℕ :=
  (Finset.range T).filter fun t => elig j t = true

/-- **Banded eligibility** of record `j`: its eligible rounds are `(m+1)`-min-separated.
    The last window may run past `T`. -/
structure BandElig (elig : ℕ → ℕ → Bool) (m T j : ℕ) : Prop where
  sep : ∀ t t', t < t' → t' < T → elig j t = true → elig j t' = true → t + m < t'

/-- **A finite set of rounds, in increasing order**: an enumeration `ts 0 < … < ts (K−1)`
    of `S` with `K = |S|`, along which products over `S` are taken. -/
lemma exists_enum (S : Finset ℕ) :
    ∃ ts : ℕ → ℕ, (∀ a b, a < b → b < S.card → ts a < ts b) ∧ (∀ l, l < S.card → ts l ∈ S) ∧
      (∀ t ∈ S, ∃ l, l < S.card ∧ ts l = t) ∧
      ∀ f : ℕ → ℝ≥0∞, ∏ t ∈ S, f t = ∏ l ∈ Finset.range S.card, f (ts l) := by
  classical
  set e := S.orderEmbOfFin rfl
  set ts : ℕ → ℕ := fun l => if h : l < S.card then e ⟨l, h⟩ else 0 with hts
  have hmono : ∀ a b, a < b → b < S.card → ts a < ts b := fun a b hab hb => by
    simp only [hts, dif_pos (lt_trans hab hb), dif_pos hb]
    exact e.strictMono (Fin.mk_lt_mk.mpr hab)
  have hmem : ∀ l, l < S.card → ts l ∈ S := fun l hl => by
    simp only [hts, dif_pos hl]; exact S.orderEmbOfFin_mem rfl _
  have hsurj : ∀ t ∈ S, ∃ l, l < S.card ∧ ts l = t := fun t ht => by
    have : t ∈ Set.range e := by rw [Finset.range_orderEmbOfFin]; exact ht
    obtain ⟨⟨l, hl⟩, rfl⟩ := this
    exact ⟨l, hl, by simp only [hts, dif_pos hl]⟩
  refine ⟨ts, hmono, hmem, hsurj, fun f => ?_⟩
  have hS : S = (Finset.range S.card).image ts := by
    ext t
    simp only [Finset.mem_image, Finset.mem_range]
    exact ⟨hsurj t, fun ⟨l, hl, he⟩ => he ▸ hmem l hl⟩
  conv_lhs => rw [hS]
  refine Finset.prod_image fun a ha b hb hab => ?_
  simp only [Finset.coe_range, Set.mem_Iio] at ha hb
  rcases Nat.lt_trichotomy a b with h | h | h
  · exact absurd hab (ne_of_lt (hmono a b h hb))
  · exact h
  · exact absurd hab (ne_of_gt (hmono b a h ha))

/-- **The program, derived** (the judgment (44) of Appendix E.5).  Record `j`'s
    eligibility is banded (`BandElig`) and the encoder is banded (`C[r,s] ≠ 0 → r ≤ s + m`);
    from datasets adjacent at `j` in either order, the budget is one factor
    `blockSymBudgetM` per round of `P_j`. -/
theorem dpftrlBanded_gen_deriv {α : ℝ} (hα : 1 < α) (hok : TOK p v)
    (hct : TCntOK v tv) (hu : UOK v tv tv uv)
    (hw : WOKT v tv uv wv) (sc : WScratchT v tv uv wv) (hq : q ≤ 1) (hv : p.σ2 ≠ 0) (hC : 0 ≤ p.Cl)
    {j : ℕ} (hj : j < n)
    (he : BandElig elig m T j) (hband : ∀ r s : Fin T, p.C r s ≠ 0 → (r : ℕ) ≤ s + m) :
    TDeriv (M := M) α (liftP (XAWT p v wv j))
      (fun _ => ∏ t ∈ partRounds elig T j, blockSymBudgetM p q α m t)
      (dpftrlBandedGen p v tv q elig uv hok) (dpftrlBandedGen p v tv q elig uv hok)
      (ZKTm p v tv wv j T) (fun _ => 1) := by
  obtain ⟨ts, hmono, hmem, hsurj, hprod⟩ := exists_enum (partRounds elig T j)
  have hmem' : ∀ l, l < (partRounds elig T j).card → ts l < T ∧ elig j (ts l) = true :=
    fun l hl => by simpa [partRounds] using hmem l hl
  rw [hprod]
  refine dpftrlBanded_gen_list_deriv hα hok hct hu hw sc hq hv hC hj ts _
    (fun l hl => by
      have h1 := hmem' l (by omega); have h2 := hmem' (l + 1) hl
      have := he.sep _ _ (hmono l (l + 1) (by omega) hl) h2.1 h1.2 h2.2; omega)
    (fun l hl => (hmem' l hl).1)
    (fun l hl => (hmem' l hl).2)
    (fun l hl r h1 h2 hrT => by
      have hl' := hmem' l hl
      cases hr : elig j (ts l + r) with
      | false => rfl
      | true => have := he.sep _ _ (by omega) hrT hl'.2 hr; omega)
    (fun k hk hout => by
      cases hr : elig j k with
      | false => rfl
      | true =>
        obtain ⟨l, hl, rfl⟩ := hsurj k (by simp [partRounds, hk, hr])
        rcases hout l hl with h | h <;> omega)
    (fun l hl => by
      have hlt := (hmem' l hl).1
      have hval : ((Fin.ofNat T (ts l) : Fin T) : ℕ) = ts l := by
        simp [Nat.mod_eq_of_lt hlt]
      calc lastB p.C (Fin.ofNat T (ts l))
          ≤ ((Fin.ofNat T (ts l) : Fin T) : ℕ) + m := lastB_le fun r hr => hband r _ hr
        _ = ts l + m := by rw [hval])

/-! ## The readout

The program never mentions the buffer `w` (`indepY_dpftrlBandedGen`), so its transcript law
is unchanged when `w` is reset (`tr_osem_eq_resetW`), and the readouts hold on arbitrary
adjacent memories.  The buffer and scratch names are picked among the names the program
does not use (`exists_wScratch`), hence `[Infinite ident]`. -/

omit [NeZero T] in
/-- The window's buffer is a name the program does not use. -/
lemma fnamesT_of_wokt (hw : WOKT v tv uv wv) : FNamesT v tv uv wv.name :=
  ⟨hw.wx.symm, hw.wz.symm, hw.wi.symm, hw.wD.symm, hw.wH.symm, hw.wY.symm, hw.wt.symm,
    hw.wu.symm, hw.wacc.symm⟩

/-- **The program neither reads nor writes the window's buffer.** -/
lemma indepY_dpftrlBandedGen (hw : WOKT v tv uv wv) :
    IndepY wv (dpftrlBandedGen (M := M) p v tv q elig uv hok) :=
  have hn := fnamesT_of_wokt hw
  ⟨indepF_assign wv v.x _ hn.x (ExprIndep.cst wv _),
    indepF_assign wv v.H _ hn.H (ExprIndep.cst wv _),
    indepF_assign wv v.Y _ hn.Y (ExprIndep.cst wv _),
    indepF_assign wv tv _ hn.t (ExprIndep.cst wv _),
    exprIndepF_ltCE wv tv hn.t T, indepF_roundT wv hn⟩

/-- **The transcript does not see the window's buffer**: the law of the transcript of
    `dpftrlBandedGen` from `m₀` is its law from `m₀` with `w` reset. -/
lemma tr_osem_eq_resetW (hw : WOKT v tv uv wv) (m₀ : M.heap) :
    (osem (dpftrlBandedGen (M := M) p v tv q elig uv hok) m₀).map Prod.snd
      = (osemA (dpftrlBandedGen p v tv q elig uv hok) (setY wv default (m₀, Tr.nil))).map Prod.snd := by
  rw [osemA_setY wv (indepY_dpftrlBandedGen hw) default (m₀, Tr.nil),
    Measure.map_map measurable_snd (measurable_setY wv default)]
  rfl

omit [NeZero T] in
/-- Adjacent memories, with the buffer reset, meet the derivation's entry condition. -/
lemma xawt_resetW (hw : WOKT v tv uv wv) {j : ℕ} {m₁ m₂ : M.heap}
    (hadj : AdjAtSym p.record j (tD v m₁) (tD v m₂)) :
    liftP (XAWT p v wv j) (setY wv default (m₁, Tr.nil), setY wv default (m₂, Tr.nil)) := by
  refine ⟨⟨?_, M.get_set_eq _ _ _ _, M.get_set_eq _ _ _ _⟩, rfl⟩
  show AdjAtSym p.record j (M.get (M.set m₁ _ wv.name default) τ v.D.name)
    (M.get (M.set m₂ _ wv.name default) τ v.D.name)
  rw [get_set_other _ _ hw.wD, get_set_other _ _ hw.wD]
  exact hadj

omit [NeZero T] in
/-- **Fresh names exist when names are infinite**: a presampling buffer `w` and a scratch
    supply avoiding the program's finitely many variables (and each other). -/
lemma exists_wScratch [Infinite ident] (v : TVars ident d T T τ) (tv : Vars ident .nat)
    (uv : Vars ident .bool) (m : ℕ) :
    ∃ wv : Vars ident (.prod .bool (.vec ((m + 1) * d))),
      WOKT v tv uv wv ∧ Nonempty (WScratchT v tv uv wv) := by
  classical
  set F : Finset ident := {v.x.name, v.z.name, v.i.name, v.D.name, v.H.name, v.Y.name,
    tv.name, uv.name, v.acc.name} with hF
  have hinf : (↑F : Set ident)ᶜ.Infinite := F.finite_toSet.infinite_compl
  set g : ℕ → ident := fun k => (hinf.natEmbedding _ k : ident) with hg
  have hginj : ∀ a b, a ≠ b → g a ≠ g b := fun a b hab h =>
    hab ((hinf.natEmbedding _).injective (Subtype.ext h))
  have hfn : ∀ k, FNamesT (ident := ident) v tv uv (g k) := fun k => by
    have hk : g k ∉ F := (hinf.natEmbedding _ k).2
    simp only [hF, Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hk
    exact ⟨Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4, Ne.symm h5, Ne.symm h6,
      Ne.symm h7, Ne.symm h8, Ne.symm h9⟩
  refine ⟨⟨g 0⟩, ⟨(hfn 0).x.symm, (hfn 0).z.symm, (hfn 0).i.symm, (hfn 0).D.symm,
    (hfn 0).H.symm, (hfn 0).Y.symm, (hfn 0).t.symm, (hfn 0).u.symm, (hfn 0).acc.symm⟩, ⟨?_⟩⟩
  exact
    { bb := ⟨g 1⟩
      gs := fun l => ⟨g (l + 2)⟩
      hbg := fun l => hginj _ _ (by omega)
      hgg := fun l l' h => hginj _ _ fun e => h (Fin.ext (by omega))
      hnb := hfn 1
      hng := fun l => hfn _
      hwb := hginj _ _ (by omega)
      hwg := fun l => hginj _ _ (by omega) }

/-- **The readout**: the Hellinger integral of the transcripts of `dpftrlBandedGen`, on
    datasets adjacent at `j` in either order, under banded eligibility and a banded encoder,
    is at most `∏_{t∈P_j} Υ_α(q, Γ·c_t, σ²)`; the per-window `max(Υ, Λ)` is `Υ` by
    Mironov–Talwar–Zhang (`blockSymBudgetM_eq`). -/
theorem dpftrlBanded_gen_Hellinger [Infinite ident] {α : ℝ} (hα : 1 < α)
    (hok : TOK p v) (hct : TCntOK v tv) (hu : UOK v tv tv uv) (hq : q ≤ 1) (hv : p.σ2 ≠ 0) (hC : 0 ≤ p.Cl)
    {j : ℕ} (hj : j < n)
    (he : BandElig elig m T j) (hband : ∀ r s : Fin T, p.C r s ≠ 0 → (r : ℕ) ≤ s + m)
    (m₁ m₂ : M.heap) (hadj : AdjAtSym p.record j (tD v m₁) (tD v m₂)) :
    hellingerIntegral α ((osem (dpftrlBandedGen p v tv q elig uv hok) m₁).map Prod.snd)
        ((osem (dpftrlBandedGen p v tv q elig uv hok) m₂).map Prod.snd)
      ≤ ∏ t ∈ partRounds elig T j, mixBudgetR q (p.Cl * Real.sqrt (colSq p.C t m)) p.σ2 α := by
  obtain ⟨wv, hw, ⟨sc⟩⟩ := exists_wScratch v tv uv m
  rw [tr_osem_eq_resetW hw m₁, tr_osem_eq_resetW hw m₂]
  have hd := dpftrlBanded_gen_deriv (M := M) hα hok hct hu hw sc hq hv hC hj he hband
  simp only [blockSymBudgetM_eq hα hv hq] at hd
  refine rrhl_tr_hellingerIntegral_le hα (rrhl_conseq (fun _ h => h) (fun _ _ => le_rfl)
    (fun _ h => h.1.2) (fun _ _ => le_rfl) (TDeriv.sound hα hd))
    (setY wv default (m₁, Tr.nil), setY wv default (m₂, Tr.nil)) (xawt_resetW hw hadj)

/-! ## Individual RDP -/

/-- **A product of finite nonzero budgets is an RDP level**: `∏_{t∈S} Υ_t` is the Hellinger
    bound `exp((α−1)ρ)` at `ρ = ∑_{t∈S} log Υ_t/(α−1)`. -/
lemma ofReal_exp_sum_log_div {α : ℝ} (hα : 1 < α) (S : Finset ℕ) (f : ℕ → ℝ≥0∞)
    (h0 : ∀ t, f t ≠ 0) (ht : ∀ t, f t ≠ ⊤) :
    ENNReal.ofReal (Real.exp ((α - 1) * ((∑ t ∈ S, Real.log (f t).toReal) / (α - 1))))
      = ∏ t ∈ S, f t := by
  have hα1 : α - 1 ≠ 0 := by linarith
  rw [show (α - 1) * ((∑ t ∈ S, Real.log (f t).toReal) / (α - 1))
      = ∑ t ∈ S, Real.log (f t).toReal by field_simp, Real.exp_sum,
    ENNReal.ofReal_prod_of_nonneg (fun _ _ => Real.exp_nonneg _)]
  refine Finset.prod_congr rfl fun t _ => ?_
  rw [Real.exp_log (ENNReal.toReal_pos (h0 t) (ht t)), ENNReal.ofReal_toReal (ht t)]

/-- **At most `k` factors, each at most the largest shift's**: the subsampled-Gaussian
    budgets of shifts bounded by `|s₀|`, over at most `k` rounds, are within the RDP level
    `k·log Υ_α(q, s₀, σ²)/(α−1)`. -/
lemma prod_mixBudgetR_le_uniform {α : ℝ} (hα : 1 < α) {q : ℝ≥0} (hq : (q : ℝ) ≤ 1)
    {v : ℝ≥0} (hv : v ≠ 0) (S : Finset ℕ) (s : ℕ → ℝ) (s₀ : ℝ) (hs : ∀ t ∈ S, |s t| ≤ |s₀|)
    {k : ℕ} (hk : S.card ≤ k) :
    ∏ t ∈ S, mixBudgetR q (s t) v α
      ≤ ENNReal.ofReal (Real.exp ((α - 1) *
          (k * Real.log (mixBudgetR q s₀ v α).toReal / (α - 1)))) := by
  have hΥ1 := one_le_mixBudgetR hα hv hq s₀
  have hρ := ofReal_exp_sum_log_div hα (Finset.range k) (fun _ => mixBudgetR q s₀ v α)
    (fun _ => (lt_of_lt_of_le zero_lt_one hΥ1).ne') (fun _ => mixBudgetR_ne_top hα _ _ hv hq)
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Finset.prod_const] at hρ
  rw [hρ]
  calc ∏ t ∈ S, mixBudgetR q (s t) v α ≤ ∏ _t ∈ S, mixBudgetR q s₀ v α :=
        Finset.prod_le_prod' fun t ht => mixBudgetR_mono hα hv hq (hs t ht)
    _ = mixBudgetR q s₀ v α ^ S.card := Finset.prod_const _
    _ ≤ mixBudgetR q s₀ v α ^ k := pow_le_pow_right₀ hΥ1 hk

/-- **Amplified banded DP-FTRL is individually RDP**: for every record `j`, at the symmetric
    adjacency `AdjAtSym p.record j` (record `j` removed from either dataset), the law of the
    transcript is `(α, ∑_{t∈P_j} log Υ_α(q, Γ·c_t, σ²)/(α−1))`-RDP. -/
theorem dpftrlBanded_gen_IndivRDP [Infinite ident] {α : ℝ} (hα : 1 < α) (hok : TOK p v)
    (hct : TCntOK v tv) (hu : UOK v tv tv uv) (hq : q ≤ 1) (hv : p.σ2 ≠ 0) (hC : 0 ≤ p.Cl)
    (he : ∀ j, BandElig elig m T j) (hband : ∀ r s : Fin T, p.C r s ≠ 0 → (r : ℕ) ≤ s + m) :
    IndivRenyiDP α
      (fun j : Fin n => (∑ t ∈ partRounds elig T j,
        Real.log (mixBudgetR q (p.Cl * Real.sqrt (colSq p.C t m)) p.σ2 α).toReal) / (α - 1))
      (fun (j : Fin n) (m₁ m₂ : M.heap) => AdjAtSym p.record j (tD v m₁) (tD v m₂))
      (fun (m : M.heap) => (osem (dpftrlBandedGen p v tv q elig uv hok) m).map Prod.snd) := by
  have hqR : (q : ℝ) ≤ 1 := by exact_mod_cast hq
  exact fun j => fun m₁ m₂ hadj => (renyiDiv_le_coe_iff hα _ _).2 <|
    (dpftrlBanded_gen_Hellinger hα hok hct hu hq hv hC j.isLt (he j) hband
      m₁ m₂ hadj).trans_eq
      (ofReal_exp_sum_log_div hα _ _
        (fun _ => (lt_of_lt_of_le zero_lt_one (one_le_mixBudgetR hα hv hqR _)).ne')
        (fun _ => mixBudgetR_ne_top hα _ _ hv hqR)).symm

/-- **The paper's uniform budget**: if every restricted column norm is at most `c`
    (`c_t ≤ c`) and every record is eligible at most `k` times (`|P_j| ≤ k`), amplified
    banded DP-FTRL is `(α, k·log Υ_α(q, Γ·c, σ²)/(α−1))`-individually RDP. -/
theorem dpftrlBanded_gen_uniform_IndivRDP [Infinite ident] {α : ℝ} (hα : 1 < α) (hok : TOK p v)
    (hct : TCntOK v tv) (hu : UOK v tv tv uv) (hq : q ≤ 1) (hv : p.σ2 ≠ 0) (hC : 0 ≤ p.Cl)
    (he : ∀ j, BandElig elig m T j) (hband : ∀ r s : Fin T, p.C r s ≠ 0 → (r : ℕ) ≤ s + m)
    {c : ℝ} (hc : ∀ t, t < T → Real.sqrt (colSq p.C t m) ≤ c)
    {k : ℕ} (hk : ∀ j, j < n → (partRounds elig T j).card ≤ k) :
    IndivRenyiDP α
      (fun _ : Fin n => k * Real.log (mixBudgetR q (p.Cl * c) p.σ2 α).toReal / (α - 1))
      (fun (j : Fin n) (m₁ m₂ : M.heap) => AdjAtSym p.record j (tD v m₁) (tD v m₂))
      (fun (m : M.heap) => (osem (dpftrlBandedGen p v tv q elig uv hok) m).map Prod.snd) := by
  have hqR : (q : ℝ) ≤ 1 := by exact_mod_cast hq
  have hc0 : 0 ≤ c := (Real.sqrt_nonneg _).trans (hc 0 (Nat.pos_of_ne_zero (NeZero.ne T)))
  refine fun j => fun m₁ m₂ hadj => (renyiDiv_le_coe_iff hα _ _).2 <|
    (dpftrlBanded_gen_Hellinger hα hok hct hu hq hv hC j.isLt (he j) hband
      m₁ m₂ hadj).trans
      (prod_mixBudgetR_le_uniform hα hqR hv _ _ _ (fun t ht => ?_) (hk j j.isLt))
  have htT : t < T := Finset.mem_range.mp (Finset.mem_filter.mp ht).1
  rw [abs_of_nonneg (mul_nonneg hC (Real.sqrt_nonneg _)), abs_of_nonneg (mul_nonneg hC hc0)]
  exact mul_le_mul_of_nonneg_left (hc t htT) hC

end DPFTRL.Band
