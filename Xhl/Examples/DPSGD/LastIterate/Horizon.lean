import Xhl.Examples.DPSGD.LastIterate.Deriv
import Xhl.Divergence.Privacy

/-!
# The horizon-free last-iterate bound (§5.1.3, end)

`dpsgdLastIter_Hellinger` bounds the transcript by `min_{1 ≤ R ≤ T} Ω_α(R)` with
`Ω_α(R) = subDispBudget q C σ₁ σ₂ γ (Δ/R) α ^ R` (`σ₁`, `σ₂` variances).  With
`L = liL = log Υ_α(q, C, σ₂)/(α−1)` and `K = liK = αΔ²/(2γ²σ₁)`, the level of `Ω_α(R)` is
`R·L + K/R` (`log_subDispBudget_pow`), and for `L > 0` and `T ≥ max 1 ⌈√(K/L)⌉` some `R`
gives `2√(KL) + L` (`exists_mul_add_div_le`).  Hence `dpsgdLastIter_horizonFree_RDP`:
the released model is `(α, 2√(KL) + L)`-RDP, independently of `T`.
-/

open MeasureTheory ProbabilityTheory Continuous
open scoped NNReal ENNReal

namespace DPSGDPaper

/-! ## The two constants and the level of `Ω_α(R)` -/

section Constants

/-- `L = log Υ_α(q, C, σ₂)/(α−1)` (cf. Altschuler–Talwar eq. (3.4)). -/
noncomputable def liL (q : ℝ≥0) (C : ℝ) (σ2 : ℝ≥0) (α : ℝ) : ℝ :=
  Real.log (mixBudgetR q C σ2 α).toReal / (α - 1)

/-- `K = αΔ²/(2γ²σ₁)`, `σ₁` a variance (cf. Altschuler–Talwar eq. (3.5)). -/
noncomputable def liK (σ1 : ℝ≥0) (γ Dm α : ℝ) : ℝ :=
  α * Dm ^ 2 / (2 * γ ^ 2 * (σ1 : ℝ))

/-- **The level of the last `R` rounds' budget**: `log Ω_α(R)/(α−1) = R·L + K/R`. -/
theorem log_subDispBudget_pow {α : ℝ} (hα : 1 < α) {q : ℝ≥0} (hq1 : (q : ℝ) < 1)
    {σ1 σ2 : ℝ≥0} (hσ1 : σ1 ≠ 0) (hσ2 : σ2 ≠ 0) {C : ℝ} {γ : ℝ} (hγ : γ ≠ 0)
    (Dm : ℝ) {R : ℕ} (hR : 1 ≤ R) :
    Real.log ((subDispBudget q C σ1 σ2 γ (Dm / R) α ^ R).toReal) / (α - 1)
      = R * liL q C σ2 α + liK σ1 γ Dm α / R := by
  have hα1 : α - 1 ≠ 0 := by linarith
  have hΛpos : 0 < (mixBudgetR q C σ2 α).toReal :=
    ENNReal.toReal_pos
      (ne_of_gt (lt_of_lt_of_le zero_lt_one (one_le_mixBudgetR hα hσ2 hq1.le C)))
      (mixBudgetR_ne_top hα _ _ hσ2 hq1.le)
  have hRpos : (0 : ℝ) < R := by exact_mod_cast hR
  have hσR : (0 : ℝ) < (σ1 : ℝ) := by exact_mod_cast pos_iff_ne_zero.mpr hσ1
  unfold subDispBudget liL liK
  rw [ENNReal.toReal_pow, Real.log_pow, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.exp_pos _).le,
    Real.log_mul hΛpos.ne' (Real.exp_pos _).ne', Real.log_exp, div_pow, div_pow, sq_abs]
  field_simp

end Constants

/-! ## The minimization over `R` -/

/-- **The minimization over integer `R`** (cf. Altschuler–Talwar eq. (3.6)): with `L > 0`,
    `K ≥ 0` and `T ≥ max 1 ⌈√(K/L)⌉`, `R = max 1 ⌈√(K/L)⌉ ∈ [1, T]` has
    `R·L + K/R ≤ 2√(KL) + L`. -/
theorem exists_mul_add_div_le {L K : ℝ} (hL : 0 < L) (hK : 0 ≤ K) {T : ℕ}
    (hT : max 1 ⌈Real.sqrt (K / L)⌉₊ ≤ T) :
    ∃ R : ℕ, 1 ≤ R ∧ R ≤ T ∧ R * L + K / R ≤ 2 * Real.sqrt (K * L) + L := by
  set x := Real.sqrt (K / L) with hx
  have hx0 : 0 ≤ x := Real.sqrt_nonneg _
  refine ⟨max 1 ⌈x⌉₊, le_max_left _ _, hT, ?_⟩
  set R := max 1 ⌈x⌉₊ with hRdef
  have hR1 : (1 : ℝ) ≤ R := by exact_mod_cast le_max_left 1 ⌈x⌉₊
  have hRpos : (0 : ℝ) < R := lt_of_lt_of_le one_pos hR1
  -- `R ≤ x + 1`
  have hRle : (R : ℝ) ≤ x + 1 := by
    rw [hRdef, Nat.cast_max, Nat.cast_one]
    exact max_le (by linarith) (Nat.ceil_lt_add_one hx0).le
  -- `R ≥ x`
  have hRge : x ≤ R := by
    rw [hRdef, Nat.cast_max]
    exact le_trans (Nat.le_ceil x) (le_max_right _ _)
  -- `x·L = √(KL)` and `x·√(KL) = K`
  have hxL : x * L = Real.sqrt (K * L) := by
    rw [hx, show K * L = (K / L) * L ^ 2 by field_simp, Real.sqrt_mul' _ (sq_nonneg L),
      Real.sqrt_sq hL.le]
  have hKL0 : 0 ≤ K * L := mul_nonneg hK hL.le
  have hxs : x * Real.sqrt (K * L) = K := by
    rw [hx, ← Real.sqrt_mul' _ hKL0, show K / L * (K * L) = K ^ 2 by field_simp,
      Real.sqrt_sq hK]
  have h1 : R * L ≤ Real.sqrt (K * L) + L := by
    rw [← hxL]; nlinarith
  have h2 : K / R ≤ Real.sqrt (K * L) := by
    rw [div_le_iff₀ hRpos]
    calc K = x * Real.sqrt (K * L) := hxs.symm
      _ ≤ R * Real.sqrt (K * L) := mul_le_mul_of_nonneg_right hRge (Real.sqrt_nonneg _)
      _ = Real.sqrt (K * L) * R := mul_comm _ _
  linarith

/-! ## The horizon-free guarantee -/

section HorizonFree

variable (N dx d T : ℕ)
  (grad : EuclideanSpace ℝ (Fin dx) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
  (C : ℝ≥0)
  (proj : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
  (η : ℝ) (q : ℝ≥0) (i : Fin (N + 1))

/-- **The last-iterate bound, independent of `T`**: under the hypotheses of
    `dpsgdLastIter_Hellinger`, with `L > 0` and `T ≥ max 1 ⌈√(K/L)⌉`, the Hellinger integral
    of the two transcript laws is at most `exp((α−1)·(2√(KL) + L))`. -/
theorem dpsgdLastIter_horizonFree_Hellinger {α : ℝ} (hα : 1 < α)
    {σ1 σ2 : ℝ≥0} (hσ1 : σ1 ≠ 0) (hσ2 : σ2 ≠ 0)
    (θ₀ : EuclideanSpace ℝ (Fin d)) (hm : MeasOK dx d grad)
    (hpm : Measurable proj)
    (hq1 : (q : ℝ) < 1) (hC : 0 < (C : ℝ))
    (hne : ∀ x y, ‖proj x - proj y‖ ≤ ‖x - y‖)
    {Dm : ℝ} (hDm : 0 ≤ Dm) (hdiam : ∀ x y, ‖proj x - proj y‖ ≤ Dm) (hη : γv N η q ≠ 0)
    (hstep : ∀ (B : Finset (Fin (N + 1))) (Dv : Fin (N + 1) → Option (EuclideanSpace ℝ (Fin dx))) (u₁ u₂),
      ‖(u₁ - γv N η q • clippedBatchSumD (N := N) grad C B Dv u₁)
        - (u₂ - γv N η q • clippedBatchSumD (N := N) grad C B Dv u₂)‖ ≤ ‖u₁ - u₂‖)
    (hL : 0 < liL q (C : ℝ) σ2 α)
    (hT : max 1 ⌈Real.sqrt (liK σ1 (γv N η q) Dm α / liL q (C : ℝ) σ2 α)⌉₊ ≤ T)
    (s₁ s₂ : St PMem)
    (hadj : AdjAtSym (recBotN N dx) i (getDS N dx s₁.1)
      (getDS N dx s₂.1)) (htau : s₁.2 = s₂.2) :
    hellingerIntegral α
      ((osemA (dpsgdLastIter N dx d T grad C proj η q hm hpm (σ2 + σ1) θ₀) s₁).map
        Prod.snd)
      ((osemA (dpsgdLastIter N dx d T grad C proj η q hm hpm (σ2 + σ1) θ₀) s₂).map
        Prod.snd)
      ≤ ENNReal.ofReal (Real.exp ((α - 1) *
          (2 * Real.sqrt (liK σ1 (γv N η q) Dm α * liL q (C : ℝ) σ2 α)
            + liL q (C : ℝ) σ2 α))) := by
  have hK : 0 ≤ liK σ1 (γv N η q) Dm α := by
    unfold liK
    have : (0 : ℝ) ≤ (σ1 : ℝ) := σ1.2
    positivity
  obtain ⟨R, hR1, hRT, hRle⟩ := exists_mul_add_div_le hL hK hT
  have h := dpsgdLastIter_Hellinger N dx d T grad C proj η q i hα hσ1
    hσ2 θ₀ hm hpm hq1 hC hne hDm hdiam hη hstep s₁ s₂ hadj htau
  refine h.trans ((iInf_le _ ⟨R, Finset.mem_Icc.mpr ⟨hR1, hRT⟩⟩).trans ?_)
  have hΩtop : subDispBudget q (C : ℝ) σ1 σ2 (γv N η q) (Dm / R) α ^ R ≠ ⊤ :=
    ENNReal.pow_ne_top (subDispBudget_ne_top hα hq1.le hσ2 _ _ _)
  refine (le_exp_renyiLevel hα hΩtop).trans ?_
  rw [log_subDispBudget_pow hα hq1 hσ1 hσ2 hη Dm hR1]
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
  exact mul_le_mul_of_nonneg_left hRle (by linarith)

/-- **Individual `(α, 2√(KL) + L)`-RDP** (Def 3.6) for the family `AdjAtSym (recBotN N dx) j`,
    for every `T ≥ max 1 ⌈√(K/L)⌉`. -/
theorem dpsgdLastIter_horizonFree_IndivRDP {α : ℝ} (hα : 1 < α)
    {σ1 σ2 : ℝ≥0} (hσ1 : σ1 ≠ 0) (hσ2 : σ2 ≠ 0)
    (θ₀ : EuclideanSpace ℝ (Fin d)) (hm : MeasOK dx d grad)
    (hpm : Measurable proj)
    (hq1 : (q : ℝ) < 1) (hC : 0 < (C : ℝ))
    (hne : ∀ x y, ‖proj x - proj y‖ ≤ ‖x - y‖)
    {Dm : ℝ} (hDm : 0 ≤ Dm) (hdiam : ∀ x y, ‖proj x - proj y‖ ≤ Dm) (hη : γv N η q ≠ 0)
    (hstep : ∀ (B : Finset (Fin (N + 1))) (Dv : Fin (N + 1) → Option (EuclideanSpace ℝ (Fin dx))) (u₁ u₂),
      ‖(u₁ - γv N η q • clippedBatchSumD (N := N) grad C B Dv u₁)
        - (u₂ - γv N η q • clippedBatchSumD (N := N) grad C B Dv u₂)‖ ≤ ‖u₁ - u₂‖)
    (hL : 0 < liL q (C : ℝ) σ2 α)
    (hT : max 1 ⌈Real.sqrt (liK σ1 (γv N η q) Dm α / liL q (C : ℝ) σ2 α)⌉₊ ≤ T) :
    IndivRenyiDP α
      (fun _ : Fin (N + 1) =>
        2 * Real.sqrt (liK σ1 (γv N η q) Dm α * liL q (C : ℝ) σ2 α) + liL q (C : ℝ) σ2 α)
      (fun (j : Fin (N + 1)) (m₁ m₂ : PMem.heap) =>
        AdjAtSym (recBotN N dx) j (getDS N dx m₁)
          (getDS N dx m₂))
      (fun m => (osem (dpsgdLastIter N dx d T grad C proj η q hm hpm (σ2 + σ1) θ₀)
        m).map Prod.snd) :=
  fun j => fun m₁ m₂ hadj => (renyiDiv_le_coe_iff hα _ _).2 <|
    dpsgdLastIter_horizonFree_Hellinger N dx d T grad C proj η q j hα hσ1
      hσ2 θ₀ hm hpm hq1 hC hne hDm hdiam hη hstep hL hT
      (m₁, Tr.nil) (m₂, Tr.nil) hadj rfl

/-- **The last-iterate model is `(α, 2√(KL) + L)`-RDP for every `T ≥ max 1 ⌈√(K/L)⌉`**
    (§5.1.3) at the union `⋃ j, AdjAtSym (recBotN N dx) j`: Lemma 3.7 on
    `dpsgdLastIter_horizonFree_IndivRDP`. -/
theorem dpsgdLastIter_horizonFree_RDP {α : ℝ} (hα : 1 < α)
    {σ1 σ2 : ℝ≥0} (hσ1 : σ1 ≠ 0) (hσ2 : σ2 ≠ 0)
    (θ₀ : EuclideanSpace ℝ (Fin d)) (hm : MeasOK dx d grad)
    (hpm : Measurable proj)
    (hq1 : (q : ℝ) < 1) (hC : 0 < (C : ℝ))
    (hne : ∀ x y, ‖proj x - proj y‖ ≤ ‖x - y‖)
    {Dm : ℝ} (hDm : 0 ≤ Dm) (hdiam : ∀ x y, ‖proj x - proj y‖ ≤ Dm) (hη : γv N η q ≠ 0)
    (hstep : ∀ (B : Finset (Fin (N + 1))) (Dv : Fin (N + 1) → Option (EuclideanSpace ℝ (Fin dx))) (u₁ u₂),
      ‖(u₁ - γv N η q • clippedBatchSumD (N := N) grad C B Dv u₁)
        - (u₂ - γv N η q • clippedBatchSumD (N := N) grad C B Dv u₂)‖ ≤ ‖u₁ - u₂‖)
    (hL : 0 < liL q (C : ℝ) σ2 α)
    (hT : max 1 ⌈Real.sqrt (liK σ1 (γv N η q) Dm α / liL q (C : ℝ) σ2 α)⌉₊ ≤ T) :
    RenyiDP α
      (2 * Real.sqrt (liK σ1 (γv N η q) Dm α * liL q (C : ℝ) σ2 α) + liL q (C : ℝ) σ2 α)
      (fun m₁ m₂ : PMem.heap => ∃ j : Fin (N + 1),
        AdjAtSym (recBotN N dx) j (getDS N dx m₁)
          (getDS N dx m₂))
      (fun m => (osem (dpsgdLastIter N dx d T grad C proj η q hm hpm (σ2 + σ1) θ₀)
        m).map Prod.snd) := by
  simpa only [ciSup_const] using
    (dpsgdLastIter_horizonFree_IndivRDP N dx d T grad C proj η q hα hσ1 hσ2 θ₀ hm hpm hq1 hC hne hDm hdiam hη hstep hL hT).renyiDP_iSup (Set.finite_range _).bddAbove

end HorizonFree

end DPSGDPaper
