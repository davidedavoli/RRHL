import Xhl.Logic.Rrhl.Sampling
import Xhl.Logic.Equiv.Unroll

/-!
# One-sided rules

Validity of the one-sided rules of Appendix B (Figure 7), which relate a statement to
`skip`.  Sampling and loops are not symmetric, because the test value
`E[k₁] ^ α * E[k₂] ^ (1 - α)` is increasing in the left expectation and decreasing in the
right one: **[Samp-L]** holds for any sub-Markov kernel, **[Samp-R]** needs a Markov kernel;
**[While-L]** needs no termination, **[While-R]** asks the right loop to stop within `n`
rounds.
-/

namespace Continuous

open MeasureTheory ProbabilityTheory ENNReal Cmd

variable {ident : Type} {M : MemType ident}

/-- Validity only sees the semantics: statements with equal denotations on the states of
    the precondition can be exchanged. -/
theorem rrhl_congr {α : ℝ} {P Q : St M × St M → Prop} {φ ψ : St M × St M → ℝ≥0∞}
    {c₁ c₂ c₁' c₂' : Cmd ident M}
    (h₁ : ∀ s, P s → osemA c₁ s.1 = osemA c₁' s.1)
    (h₂ : ∀ s, P s → osemA c₂ s.2 = osemA c₂' s.2)
    (h : RRhl α P φ c₁' c₂' Q ψ) : RRhl α P φ c₁ c₂ Q ψ := by
  intro s hs k₁ k₂ hk₁ hk₂ hk
  show testValC α (osemA c₁ s.1) (osemA c₂ s.2) k₁ k₂ ≤ φ s
  rw [h₁ s hs, h₂ s hs]
  exact h s hs k₁ k₂ hk₁ hk₂ hk

lemma osemA_skip_seq_skip (s : St M) :
    osemA (Cmd.seq (Cmd.skip : Cmd ident M) Cmd.skip) s = osemA Cmd.skip s := by
  rw [osemA_seq, osemA_skip, Measure.dirac_bind (osemA_measurable _), osemA_skip]

/-! ## Deterministic statements -/

/-- **[Assn-L]**. -/
theorem rrhl_assign_l {α : ℝ} {t : Ty} (x : Vars ident t) (e : Expr M t)
    (Q : St M × St M → Prop) (ψ : St M × St M → ℝ≥0∞) :
    RRhl α
      (fun s => Q ((M.set s.1.1 t x.name (esem e s.1.1), s.1.2), s.2))
      (fun s => ψ ((M.set s.1.1 t x.name (esem e s.1.1), s.1.2), s.2))
      (Cmd.assign x e) Cmd.skip Q ψ :=
  rrhl_det (g₁ := fun s => (M.set s.1 t x.name (esem e s.1), s.2)) (g₂ := id)
    (fun _ => rfl) (fun _ => rfl) Q ψ

/-- **[Release-L]**. -/
theorem rrhl_release_l {α : ℝ} {t : Ty} (e : Expr M t)
    (Q : St M × St M → Prop) (ψ : St M × St M → ℝ≥0∞) :
    RRhl α
      (fun s => Q ((s.1.1, s.1.2.snoc ⟨t, esem e s.1.1⟩), s.2))
      (fun s => ψ ((s.1.1, s.1.2.snoc ⟨t, esem e s.1.1⟩), s.2))
      (Cmd.release e) Cmd.skip Q ψ :=
  rrhl_det (g₁ := fun s => (s.1, s.2.snoc ⟨t, esem e s.1⟩)) (g₂ := id)
    (fun _ => rfl) (fun _ => rfl) Q ψ

/-- **[If-L]**: a case split on the left guard alone; the right statement is arbitrary. -/
theorem rrhl_if_l {α : ℝ} {P Q : St M × St M → Prop} {φ ψ : St M × St M → ℝ≥0∞}
    {e₁ : BExpr M} {c1t c1e c₂ : Cmd ident M}
    (hthen : RRhl α (fun s => P s ∧ esem e₁ s.1.1 = true) φ c1t c₂ Q ψ)
    (helse : RRhl α (fun s => P s ∧ esem e₁ s.1.1 = false) φ c1e c₂ Q ψ) :
    RRhl α P φ (Cmd.cond e₁ c1t c1e) c₂ Q ψ := by
  intro s hs k₁ k₂ hk₁ hk₂ hk
  show testValC α (if esem e₁ s.1.1 then osemA c1t s.1 else osemA c1e s.1)
    (osemA c₂ s.2) k₁ k₂ ≤ φ s
  cases hg : esem e₁ s.1.1 with
  | true => simpa using hthen s ⟨hs, hg⟩ k₁ k₂ hk₁ hk₂ hk
  | false => simpa using helse s ⟨hs, hg⟩ k₁ k₂ hk₁ hk₂ hk

/-- The mirror image of **[If-L]**, used for **[While-R]**. -/
theorem rrhl_if_r {α : ℝ} {P Q : St M × St M → Prop} {φ ψ : St M × St M → ℝ≥0∞}
    {e₂ : BExpr M} {c₁ c2t c2e : Cmd ident M}
    (hthen : RRhl α (fun s => P s ∧ esem e₂ s.2.1 = true) φ c₁ c2t Q ψ)
    (helse : RRhl α (fun s => P s ∧ esem e₂ s.2.1 = false) φ c₁ c2e Q ψ) :
    RRhl α P φ c₁ (Cmd.cond e₂ c2t c2e) Q ψ := by
  intro s hs k₁ k₂ hk₁ hk₂ hk
  show testValC α (osemA c₁ s.1)
    (if esem e₂ s.2.1 then osemA c2t s.2 else osemA c2e s.2) k₁ k₂ ≤ φ s
  cases hg : esem e₂ s.2.1 with
  | true => simpa using hthen s ⟨hs, hg⟩ k₁ k₂ hk₁ hk₂ hk
  | false => simpa using helse s ⟨hs, hg⟩ k₁ k₂ hk₁ hk₂ hk

/-! ## Sampling -/

/-- The weighted Hellinger integral of a finite measure against itself is the integral of
    the weight. -/
lemma weightedHellingerIntegral_self {Ω : Type*} [MeasurableSpace Ω] {α : ℝ}
    (w : Ω → ℝ≥0∞) (μ : Measure Ω) [SigmaFinite μ] :
    weightedHellingerIntegral α w μ μ = ∫⁻ x, w x ∂μ := by
  rw [weightedHellingerIntegral_of_ac _ (Measure.AbsolutelyContinuous.refl μ)]
  refine lintegral_congr_ae ?_
  filter_upwards [Measure.rnDeriv_self μ] with x hx
  rw [hx, ENNReal.one_rpow, one_mul]

/-- **[Samp-L]**: sampling on the left against `skip`, for any sub-Markov kernel.  The
    pre-budget bounds the expected post-budget; the postcondition is needed for almost
    every sampled value only. -/
theorem rrhl_rnd_l {α : ℝ} (hα : 1 < α) {t : Ty} (x : Vars ident t)
    (κ : @ProbabilityTheory.Kernel M.heap t.interp M.heapMeas (Ty.measurableSpace t))
    [IsSubMarkovKernel κ]
    (P Q : St M × St M → Prop) (φ ψ : St M × St M → ℝ≥0∞)
    (hQ : ∀ s, P s → ∀ᵐ v ∂(κ s.1.1), Q ((M.set s.1.1 t x.name v, s.1.2), s.2))
    (hφ : ∀ s, P s → ∫⁻ v, ψ ((M.set s.1.1 t x.name v, s.1.2), s.2) ∂(κ s.1.1) ≤ φ s) :
    RRhl α P φ (Cmd.random x κ) Cmd.skip Q ψ := by
  intro s hs k₁ k₂ hk₁ hk₂ hk
  have hu : Measurable (fun v : t.interp => ((M.set s.1.1 t x.name v, s.1.2) : St M)) :=
    ((M.set_measurable x.name).comp measurable_prodMk_left).prodMk measurable_const
  have e₁ := ewp_random hk₁ x κ s.1
  unfold ewp at e₁
  rw [testValC, e₁, osemA_skip, lintegral_dirac' _ hk₂]
  set μ := κ s.1.1
  have hcore := testVal_le_weightedHellingerIntegral_same hα (hk₁.comp hu)
    (measurable_const (a := k₂ s.2)) μ μ
    (w := fun v => ψ ((M.set s.1.1 t x.name v, s.1.2), s.2))
    (by filter_upwards [hQ s hs] with v hv using hk _ hv)
  rw [weightedHellingerIntegral_self, lintegral_const] at hcore
  refine le_trans ?_ (hcore.trans (hφ s hs))
  refine mul_le_mul' le_rfl (rpow_antitone_of_nonpos ?_ (by linarith))
  calc k₂ s.2 * μ Set.univ ≤ k₂ s.2 * 1 :=
        mul_le_mul' le_rfl (IsSubMarkovKernel.measure_univ_le_one _)
    _ = k₂ s.2 := mul_one _

/-- **[Samp-R]**: sampling on the right against `skip`, for a Markov kernel.  A loss of
    mass on the right would *raise* the test value, hence the total-mass requirement. -/
theorem rrhl_rnd_r {α : ℝ} (hα : 1 < α) {t : Ty} (x : Vars ident t)
    (κ : @ProbabilityTheory.Kernel M.heap t.interp M.heapMeas (Ty.measurableSpace t))
    [IsMarkovKernel κ]
    (P Q : St M × St M → Prop) (φ ψ : St M × St M → ℝ≥0∞)
    (hQ : ∀ s, P s → ∀ᵐ v ∂(κ s.2.1), Q (s.1, (M.set s.2.1 t x.name v, s.2.2)))
    (hφ : ∀ s, P s → ∫⁻ v, ψ (s.1, (M.set s.2.1 t x.name v, s.2.2)) ∂(κ s.2.1) ≤ φ s) :
    RRhl α P φ Cmd.skip (Cmd.random x κ) Q ψ := by
  intro s hs k₁ k₂ hk₁ hk₂ hk
  have hu : Measurable (fun v : t.interp => ((M.set s.2.1 t x.name v, s.2.2) : St M)) :=
    ((M.set_measurable x.name).comp measurable_prodMk_left).prodMk measurable_const
  have e₂ := ewp_random hk₂ x κ s.2
  unfold ewp at e₂
  rw [testValC, e₂, osemA_skip, lintegral_dirac' _ hk₁]
  set μ := κ s.2.1
  have hcore := testVal_le_weightedHellingerIntegral_same hα
    (measurable_const (a := k₁ s.1)) (hk₂.comp hu) μ μ
    (w := fun v => ψ (s.1, (M.set s.2.1 t x.name v, s.2.2)))
    (by filter_upwards [hQ s hs] with v hv using hk _ hv)
  rw [weightedHellingerIntegral_self, lintegral_const, measure_univ, mul_one] at hcore
  exact hcore.trans (hφ s hs)

/-! ## Loops -/

/-- **[While-L]**: a loop on the left against `skip`, with an invariant family indexed by
    the completed rounds and no termination condition. -/
theorem rrhl_while_l {α : ℝ} (hα : 1 < α) {e₁ : BExpr M} {c₁ : Cmd ident M}
    (P : ℕ → St M × St M → Prop) (φ : ℕ → St M × St M → ℝ≥0∞)
    (E : St M × St M → Prop) (ψ : St M × St M → ℝ≥0∞)
    (dstep : ∀ k, RRhl α (fun s => P k s ∧ esem e₁ s.1.1 = true) (φ k)
      c₁ Cmd.skip (P (k + 1)) (φ (k + 1)))
    (hexit : ∀ k s, P k s → esem e₁ s.1.1 = false → E s ∧ ψ s ≤ φ k s) :
    RRhl α (P 0) (φ 0) (Cmd.while e₁ c₁) Cmd.skip
      (fun s => E s ∧ esem e₁ s.1.1 = false) ψ := by
  have hiter : ∀ j k, RRhl α (P k) (φ k) (unrollWhile e₁ c₁ j) Cmd.skip
      (fun s => E s ∧ esem e₁ s.1.1 = false) ψ := by
    intro j
    induction j with
    | zero =>
      intro k s _ κ₁ κ₂ _ _ _
      show testValC α (osemA (unrollWhile e₁ c₁ 0) s.1) (osemA Cmd.skip s.2) κ₁ κ₂ ≤ φ k s
      rw [show unrollWhile e₁ c₁ 0 = Cmd.abort from rfl, testValC,
        show osemA (Cmd.abort : Cmd ident M) s.1 = 0 from rfl,
        lintegral_zero_measure, ENNReal.zero_rpow_of_pos (by linarith : (0:ℝ) < α), zero_mul]
      exact zero_le
    | succ j ih =>
      intro k
      refine rrhl_if_l ?_ ?_
      · exact rrhl_congr (fun _ _ => rfl) (fun s _ => (osemA_skip_seq_skip s.2).symm)
          (rrhl_seq (dstep k) (ih (k + 1)))
      · exact rrhl_conseq (fun s hs => ⟨(hexit k s hs.1 hs.2).1, hs.2⟩)
          (fun s hs => (hexit k s hs.1 hs.2).2) (fun _ h => h) (fun _ _ => le_rfl)
          (rrhl_skip _ ψ)
  intro s hs κ₁ κ₂ hκ₁ hκ₂ hadm
  have key : ∀ j, (∫⁻ x, κ₁ x ∂(oubn (osemA c₁) (esem e₁) j s.1)) ^ α
      * (∫⁻ x, κ₂ x ∂(osemA Cmd.skip s.2)) ^ (1 - α) ≤ φ 0 s := by
    intro j
    have h := hiter j 0 s hs κ₁ κ₂ hκ₁ hκ₂ hadm
    rwa [testValC, osemA_unrollWhile] at h
  have hmon₁ : Monotone (fun j => oubn (osemA c₁) (esem e₁) j s.1) :=
    oubn_monotone (osemA_measurable _) e₁.measurable s.1
  show testValC α (osemA (Cmd.while e₁ c₁) s.1) (osemA Cmd.skip s.2) κ₁ κ₂ ≤ φ 0 s
  rw [testValC,
    show osemA (Cmd.while e₁ c₁) s.1 = ⨆ j, oubn (osemA c₁) (esem e₁) j s.1 from rfl,
    lintegral_iSup_measure hmon₁, iSup_rpow_pos (by linarith : (0:ℝ) < α), ENNReal.iSup_mul]
  exact iSup_le key

/-- **[While-R]**: a loop on the right against `skip`, which must stop within `n` rounds
    (`P n` forces the guard false).  Proved by unfolding once per level of the chain. -/
theorem rrhl_while_r {α : ℝ} {e₂ : BExpr M} {c₂ : Cmd ident M} (n : ℕ)
    (P : ℕ → St M × St M → Prop) (φ : ℕ → St M × St M → ℝ≥0∞)
    (E : St M × St M → Prop) (ψ : St M × St M → ℝ≥0∞)
    (dstep : ∀ k, k < n → RRhl α (fun s => P k s ∧ esem e₂ s.2.1 = true) (φ k)
      Cmd.skip c₂ (P (k + 1)) (φ (k + 1)))
    (hstop : ∀ s, P n s → esem e₂ s.2.1 = false)
    (hexit : ∀ k, k ≤ n → ∀ s, P k s → esem e₂ s.2.1 = false → E s ∧ ψ s ≤ φ k s) :
    RRhl α (P 0) (φ 0) Cmd.skip (Cmd.while e₂ c₂)
      (fun s => E s ∧ esem e₂ s.2.1 = false) ψ := by
  have hloop : ∀ i, i ≤ n → RRhl α (P (n - i)) (φ (n - i)) Cmd.skip (Cmd.while e₂ c₂)
      (fun s => E s ∧ esem e₂ s.2.1 = false) ψ := by
    intro i
    induction i with
    | zero =>
      intro _
      refine rrhl_congr (fun _ _ => rfl)
        (fun s hs => osemA_while_exit e₂ c₂ s.2 (hstop s (by simpa using hs))) ?_
      exact rrhl_conseq
        (fun s hs => ⟨(hexit n le_rfl s (by simpa using hs) (hstop s (by simpa using hs))).1,
          hstop s (by simpa using hs)⟩)
        (fun s hs => (hexit n le_rfl s (by simpa using hs) (hstop s (by simpa using hs))).2)
        (fun _ h => h) (fun _ _ => le_rfl) (rrhl_skip _ ψ)
    | succ i ih =>
      intro hi
      have hk : n - (i + 1) < n := by omega
      have e : n - (i + 1) + 1 = n - i := by omega
      refine rrhl_congr (fun _ _ => rfl) (fun s _ => osemA_while_unroll s.2) ?_
      refine rrhl_if_r ?_ ?_
      · refine rrhl_congr (fun s _ => (osemA_skip_seq_skip s.1).symm) (fun _ _ => rfl) ?_
        have hb := dstep (n - (i + 1)) hk
        rw [e] at hb
        exact rrhl_seq hb (ih (by omega))
      · exact rrhl_conseq (fun s hs => ⟨(hexit _ hk.le s hs.1 hs.2).1, hs.2⟩)
          (fun s hs => (hexit _ hk.le s hs.1 hs.2).2) (fun _ h => h) (fun _ _ => le_rfl)
          (rrhl_skip _ ψ)
  simpa using hloop n le_rfl

end Continuous
