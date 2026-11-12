import Xhl.Examples.DPFTRLBanded.ChainT
import Xhl.Examples.DPFTRLBanded.PresampleT

open Continuous

/-!
# The paying leaf, the presampled window, and [Equiv] (Appendix D.5, (53)–(58))

* **[Samp-Dec]** (`tderiv_sampWT`) on the draw `w ←$ Bern(q) ⊗ 𝒩(0, σ²I)^{m+1}`, with the
  witnesses `sampFwdK_mix_witness` (record `j` absent on the right, price `Υ_α`) and
  `sampFwdK_flip_witness` (absent on the left, price `Λ_α`): budget `blockSymBudgetM`;
* **[Local]** and **[Seq]** assemble the presampled window `windowS` at that budget,
  between the invariant `ZKTm` (`tderiv_windowSY`);
* **[Equiv]** (`tderiv_windowT_rules`) moves the derivation onto the program's window
  `iterCmd roundT (L+1)` through `cequiv_windowT_windowS_scr`.
-/

open MeasureTheory ProbabilityTheory ENNReal
open Cmd hiding loc
open scoped NNReal


variable {ident : Type} {M : MemType ident}

namespace DPFTRL.Band

open Continuous

variable {d e n T : ℕ} {τ : Ty} [NeZero T]

variable {p : TParams d e n T T τ} {v : TVars ident d T T τ} {tv : Vars ident .nat}
  {q : ℝ≥0} {elig : ℕ → ℕ → Bool} {uv : Vars ident .bool} {m : ℕ}
  {wv : Vars ident (.prod .bool (.vec ((m + 1) * d)))}

/-- The between-windows invariant does not read `w`. -/
lemma YKTm_set_w (hw : WOKT v tv uv wv) {j k : ℕ} (mm : M.heap × M.heap)
    (θ₁ θ₂ : WValT m d) :
    YKTm p v tv j k (M.set mm.1 (.prod .bool (.vec ((m + 1) * d))) wv.name θ₁,
        M.set mm.2 (.prod .bool (.vec ((m + 1) * d))) wv.name θ₂)
      ↔ YKTm p v tv j k mm := by
  show YKT p j k (obsT v tv (M.set mm.1 _ wv.name θ₁))
      (obsT v tv (M.set mm.2 _ wv.name θ₂)) ↔ _
  rw [obsT_set_w hw, obsT_set_w hw]
  exact Iff.rfl

/-! ## [Samp-Dec] on the presampled coin and noises -/

/-- **The paying step**, by **[Samp-Dec]**, in either orientation of the adjacency: the
    kernel and the witness are chosen per state, at price `Υ` when record `j` is absent on
    the right and `Λ` when it is absent on the left, so `max(Υ, Λ)` (`blockSymBudgetM`). -/
theorem tderiv_sampWT {α : ℝ} (hα : 1 < α) (hw : WOKT v tv uv wv) (hq : q ≤ 1)
    (hσ : p.σ2 ≠ 0) (hC : 0 ≤ p.Cl)
    {j s : ℕ} (hsT : s < T) :
    TDeriv (M := M) α (liftP (YKTm p v tv j s)) (fun _ => blockSymBudgetM p q α m s)
      (Cmd.random wv (Kernel.const _ (lawWT (m := m) (d := d) q p.σ2)))
      (Cmd.random wv (Kernel.const _ (lawWT (m := m) (d := d) q p.σ2)))
      (liftP (YQTm p v tv wv j s s (YGT p j s m))) (fun _ => 1) := by
  refine TDeriv.rndFwdK hα wv wv _ _ _ _ _ _ (fun σ hσ' => ?_)
  have hadj : AdjAtSym p.record j (tD v σ.1.1) (tD v σ.2.1) := hσ'.1.1
  -- each pair of draws shifted as `YShT` says satisfies the postcondition
  have hpost : ∀ w w' : WValT m d,
      YShT p j s m (tX v σ.1.1) (tD v σ.1.1) (tD v σ.2.1) w w' →
      liftP (YQTm p v tv wv j s s (YGT p j s m)) (updPair wv wv σ (w, w')) := by
    intro w w' hθ
    set m1 := M.set σ.1.1 (.prod .bool (.vec ((m + 1) * d))) wv.name w with hm1
    set m2 := M.set σ.2.1 (.prod .bool (.vec ((m + 1) * d))) wv.name w' with hm2
    have e1 : obsT v tv m1 = obsT v tv σ.1.1 := by rw [hm1]; exact obsT_set_w hw _ _
    have e2 : obsT v tv m2 = obsT v tv σ.2.1 := by rw [hm2]; exact obsT_set_w hw _ _
    have hK : YKTm p v tv j s (m1, m2) := by
      show YKT p j s (obsT v tv m1) (obsT v tv m2)
      rw [e1, e2]; exact hσ'.1
    have hx : tX v m1 = tX v σ.1.1 := congrArg ObsT.x e1
    have hD1 : tD v m1 = tD v σ.1.1 := congrArg ObsT.D e1
    have hD2 : tD v m2 = tD v σ.2.1 := congrArg ObsT.D e2
    have g1 : tWT wv m1 = w := by rw [hm1]; exact M.get_set_eq _ _ _ _
    have g2 : tWT wv m2 = w' := by rw [hm2]; exact M.get_set_eq _ _ _ _
    refine ⟨yQTm_of_yKTm hsT hK ?_, hσ'.2⟩
    show YShT p j s m (tX v m1) (tD v m1) (tD v m2) (tWT wv m1) (tWT wv m2)
    rw [hx, hD1, hD2, g1, g2]
    exact hθ
  -- constant post-weight: the kernel-averaged weight is `1`
  have hone : ∀ (F : ProbabilityTheory.Kernel (WValT m d) (WValT m d)) [IsMarkovKernel F],
      (fun w => ∫⁻ w', (fun _ : St M × St M => (1 : ℝ≥0∞))
        (updPair wv wv σ (w, w')) ∂(F w)) = fun _ => 1 := by
    intro F _
    funext w
    rw [lintegral_one, measure_univ]
  rcases hadj with hA | hA
  · -- record `j` absent on the right: the forward leaf
    set Δ := concatE (shiftT p s m (gLx p j (tX v σ.1.1) (tD v σ.1.1))) with hΔ
    obtain ⟨ν, hν, hbind, hH⟩ := sampFwdK_mix_witness hα p.σ2 hσ q hq Δ
    refine ⟨fwdShiftK q Δ, ν, isMarkov_fwdShiftK q Δ, hν, hbind,
      Filter.Eventually.of_forall fun w => (fwdShiftK_ae q Δ w).mono fun w' hw' => hpost w w' (Or.inl ⟨hA.2, hw'⟩), ?_⟩
    rw [hone, weightedHellingerIntegral_one]
    refine hH.trans (le_trans ?_ (le_max_left _ _))
    have hb := hellingerIntegral_sgMixtureE_le_mixBudgetR hα 0 Δ p.σ2 hσ q hq
      (s := p.Cl * Real.sqrt (colSq p.C s m))
      (by rw [hΔ]; exact norm_shiftT_le hC (norm_gLx_le hC j _ _))
    rw [zero_add] at hb
    exact hb
  · -- record `j` absent on the left: the reversed leaf
    set Δ := concatE (shiftT p s m (gLx p j (tX v σ.1.1) (tD v σ.2.1))) with hΔ
    obtain ⟨F, ν, hF, hν, hbind, hae, hH⟩ := sampFwdK_flip_witness hα p.σ2 q hq Δ
    refine ⟨F, ν, hF, hν, hbind,
      Filter.Eventually.of_forall fun w => (hae w).mono fun w' hw' => hpost w w' (Or.inr ⟨hA.2, hw'⟩), ?_⟩
    rw [hone, weightedHellingerIntegral_one]
    refine hH.trans (le_trans ?_ (le_max_right _ _))
    have hb := hellingerIntegral_flip_sgMixtureE_le_budget_of_le_one hα 0 Δ p.σ2 hσ
      (q := q) (by exact_mod_cast hq) (s := p.Cl * Real.sqrt (colSq p.C s m))
      (by rw [hΔ]; exact norm_shiftT_le hC (norm_gLx_le hC j _ _))
    rw [zero_add] at hb
    exact hb

/-! ## [Local]: the presampled window -/

/-- **The presampled window, by the rules, at the amplified budget.**  [Local] for `w`,
    [Seq], the paying leaf `tderiv_sampWT`, and `tderiv_windowWY`; pre- and postcondition
    are the between-windows invariant.  The window has `L + 1 ≤ m + 1` rounds, all inside
    the run, and its slot is dead by its end (`hlast`). -/
theorem tderiv_windowSY {α : ℝ} (hα : 1 < α) (hok : TOK p v)
    (hct : TCntOK v tv) (hu : UOK v tv tv uv)
    (hw : WOKT v tv uv wv) (hq : q ≤ 1) (hσ : p.σ2 ≠ 0) (hC : 0 ≤ p.Cl)
    {j : ℕ} (hj : j < n) (s L : ℕ) (hL : L ≤ m)
    (hsT : s + L < T) (hel : elig j s = true)
    (hne : ∀ l, 1 ≤ l → l ≤ L → elig j (s + l) = false)
    (hlast : lastB p.C (Fin.ofNat T s) < s + L + 1) :
    TDeriv (M := M) α (ZKTm p v tv wv j s) (fun _ => blockSymBudgetM p q α m s)
      (windowS p v tv q elig uv hok wv j L hL) (windowS p v tv q elig uv hok wv j L hL)
      (ZKTm p v tv wv j (s + L + 1)) (fun _ => 1) := by
  -- the window, with its postcondition read after the reset of `w`
  have hwin : TDeriv (M := M) α (liftP (YQTm p v tv wv j s s (YGT p j s m))) (fun _ => 1)
      (windowW p v tv q elig uv hok wv j L hL) (windowW p v tv q elig uv hok wv j L hL)
      (fun σ => ZKTm p v tv wv j (s + L + 1) (resetV wv σ.1, resetV wv σ.2))
      (fun _ => 1) := by
    refine TDeriv.conseq (fun _ h => h) (fun _ _ => le_rfl) (fun σ hσ' => ⟨⟨?_, hσ'.2⟩, ?_, ?_⟩)
      (fun _ _ => le_rfl)
      (tderiv_windowWY hα hok hct hu hw hj s L hL hsT hel hne)
    · show YKT p j (s + L + 1)
        (obsT v tv (M.set σ.1.1 (.prod .bool (.vec ((m + 1) * d))) wv.name default))
        (obsT v tv (M.set σ.2.1 (.prod .bool (.vec ((m + 1) * d))) wv.name default))
      rw [obsT_set_w hw, obsT_set_w hw]
      exact yKTm_of_yQTm (by omega) (by omega) hlast (by omega) hσ'.1
    · exact M.get_set_eq _ _ _ _
    · exact M.get_set_eq _ _ _ _
  have hseq := TDeriv.seq (tderiv_sampWT (M := M) hα hw hq hσ hC (by omega : s < T)) hwin
  have hl := TDeriv.loc (α := α) wv wv
    (c₁ := Cmd.seq (Cmd.random wv (Kernel.const _ (lawWT (m := m) (d := d) q p.σ2)))
      (windowW p v tv q elig uv hok wv j L hL))
    (c₂ := Cmd.seq (Cmd.random wv (Kernel.const _ (lawWT (m := m) (d := d) q p.σ2)))
      (windowW p v tv q elig uv hok wv j L hL))
    (Q := ZKTm p v tv wv j (s + L + 1)) (ψ := fun _ => 1) hseq
  refine TDeriv.conseq (fun σ hσ' => ?_) (fun _ _ => le_rfl) (fun _ h => h)
    (fun _ _ => le_rfl) hl
  exact ⟨(YKTm_set_w hw (σ.1.1, σ.2.1) default default).mpr hσ'.1.1, hσ'.1.2⟩

/-! ## [Equiv]: the program's window is the presampled window -/

/-- **A window of the program, by the rules, at the amplified budget**: the rounds
    `s, …, s + L` (`L ≤ m`, inside the run), by [Equiv] onto the presampled window
    (`cequiv_windowT_windowS_scr`) and `tderiv_windowSY`. -/
theorem tderiv_windowT_rules {α : ℝ} (hα : 1 < α) (hok : TOK p v)
    (hct : TCntOK v tv) (hu : UOK v tv tv uv)
    (hw : WOKT v tv uv wv) (sc : WScratchT v tv uv wv) (hq : q ≤ 1) (hσ : p.σ2 ≠ 0) (hC : 0 ≤ p.Cl)
    {j : ℕ} (hj : j < n) (s L : ℕ) (hL : L ≤ m)
    (hsT : s + L < T) (hel : elig j s = true)
    (hne : ∀ l, 1 ≤ l → l ≤ L → elig j (s + l) = false)
    (hlast : lastB p.C (Fin.ofNat T s) < s + L + 1) :
    TDeriv (M := M) α (ZKTm p v tv wv j s) (fun _ => blockSymBudgetM p q α m s)
      (iterCmd (roundT p v tv q elig uv hok) (L + 1)) (iterCmd (roundT p v tv q elig uv hok) (L + 1))
      (ZKTm p v tv wv j (s + L + 1)) (fun _ => 1) :=
  have hres : ∀ (y : St M), tWT wv y.1 = default → resetV wv y = y := fun y hy =>
    Prod.ext
      (show M.set y.1 (.prod .bool (.vec ((m + 1) * d))) wv.name default = y.1 by
        rw [← hy]; exact M.set_get_eq _ _ _)
      rfl
  TDeriv.equiv
    (cequiv_windowT_windowS_scr sc hok hu hw hj L hL)
    (cequiv_windowT_windowS_scr sc hok hu hw hj L hL)
    (fun y hy => ⟨hres y.1 hy.2.1, hres y.2 hy.2.2⟩)
    (tderiv_windowSY hα hok hct hu hw hq hσ hC hj s L hL hsT hel hne hlast)

end DPFTRL.Band
