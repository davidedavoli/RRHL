import Xhl.Language.SubMarkov
import Xhl.Measures.Range
import Xhl.Divergence.Weighted
import Xhl.Divergence.TestVal

open Continuous

/-!
# The RRHL judgment and its core rules

`RRhl α P φ c₁ c₂ Q ψ` (Definition 4.1) is valid when, from every pair of states satisfying
`P`, every pair of measurable tests `k₁, k₂` admissible for the postcondition and its weight,

    k₁ a ^ α * k₂ b ^ (1 − α) ≤ ψ (a, b)   whenever   Q (a, b),

has expectations bounded by the pre-budget:

    (∫ k₁ d⟦c₁⟧s₁) ^ α * (∫ k₂ d⟦c₂⟧s₂) ^ (1 − α) ≤ φ s.

* `testVal_le_weightedHellingerIntegral_same` — weighted weak duality on one space, the
  lemma behind the sampling rules (`Xhl/Logic/Rrhl/Sampling.lean`).
* `ewp` — the expectation transformer `ewp c k s = ∫ k d⟦c⟧s`.
* `rrhl_conseq`, `rrhl_skip`, `rrhl_assign`, `rrhl_release`, `rrhl_seq`, `rrhl_if`,
  `rrhl_while_gen` — the core structural rules of Figure 3.  The loop rule [While] has an
  invariant family indexed by the number of completed rounds and no variant or
  termination condition; [While-Prod] is derived from it (`tderiv_while_prod`).
-/

open MeasureTheory ProbabilityTheory ENNReal Cmd

namespace Continuous

/-! ## Weighted weak duality on measures -/

section Measures

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Pointwise, with a weight: an admissibility bound by `w` is carried through a density
    on the left. -/
lemma test_term_le_w {α : ℝ} (hα : 1 < α) {x y u w : ℝ≥0∞} (hu : u ≠ ⊤)
    (hxy : x ^ α * y ^ (1 - α) ≤ w) :
    (x * u) ^ α * y ^ (1 - α) ≤ w * u ^ α := by
  have hα0 : (0 : ℝ) < α := by linarith
  have h1α : (1 : ℝ) - α < 0 := by linarith
  rcases eq_or_ne u 0 with hu0 | hu0
  · rw [hu0, mul_zero, ENNReal.zero_rpow_of_pos hα0, zero_mul]; exact zero_le
  rcases eq_or_ne y ⊤ with hy | hy
  · rw [hy, ENNReal.top_rpow_of_neg h1α, mul_zero]; exact zero_le
  rcases eq_or_ne x ⊤ with hx | hx
  · -- the left test is infinite: the premise already forces `w = ⊤` unless `y ^ (1-α) = 0`
    rcases eq_or_ne (y ^ (1 - α)) 0 with hy0 | hy0
    · rw [hy0, mul_zero]; exact zero_le
    · rw [hx, ENNReal.top_rpow_of_pos hα0, ENNReal.top_mul hy0] at hxy
      have hw : w = ⊤ := top_le_iff.mp hxy
      rw [hw, ENNReal.top_mul (by
        exact (ENNReal.rpow_pos (pos_iff_ne_zero.mpr hu0) hu).ne')]
      exact le_top
  rw [ENNReal.mul_rpow_of_ne_top hx hu]
  calc x ^ α * u ^ α * y ^ (1 - α)
      = (x ^ α * y ^ (1 - α)) * u ^ α := by ring
    _ ≤ w * u ^ α := mul_le_mul' hxy le_rfl

/-- **Weighted weak duality on one space.**  Two tests whose pointwise Hellinger term is at
    most the weight `ν`-almost everywhere are bounded by the weighted Hellinger integral. -/
theorem testVal_le_weightedHellingerIntegral_same {α : ℝ} (hα : 1 < α) {w K₁ K₂ : Ω → ℝ≥0∞}
    (hK₁ : Measurable K₁) (hK₂ : Measurable K₂) (μ ν : Measure Ω)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ᵐ x ∂ν, K₁ x ^ α * K₂ x ^ (1 - α) ≤ w x) :
    (∫⁻ x, K₁ x ∂μ) ^ α * (∫⁻ x, K₂ x ∂ν) ^ (1 - α) ≤ weightedHellingerIntegral α w μ ν := by
  by_cases hac : μ ≪ ν
  · rw [weightedHellingerIntegral_of_ac _ hac]
    have hL : ∫⁻ x, K₁ x ∂μ = ∫⁻ x, μ.rnDeriv ν x * K₁ x ∂ν := by
      rw [lintegral_rnDeriv_mul hac hK₁.aemeasurable]
    rw [hL]
    calc (∫⁻ x, μ.rnDeriv ν x * K₁ x ∂ν) ^ α * (∫⁻ x, K₂ x ∂ν) ^ (1 - α)
        ≤ ∫⁻ x, (μ.rnDeriv ν x * K₁ x) ^ α * (K₂ x) ^ (1 - α) ∂ν :=
          lintegral_rpow_mul_rpow_le _ _ hα
            ((Measure.measurable_rnDeriv μ ν).mul hK₁).aemeasurable hK₂.aemeasurable
      _ ≤ ∫⁻ x, (μ.rnDeriv ν x) ^ α * w x ∂ν := by
          refine lintegral_mono_ae ?_
          filter_upwards [Measure.rnDeriv_lt_top μ ν, h] with x hx hwx
          rw [mul_comm (μ.rnDeriv ν x), mul_comm ((μ.rnDeriv ν x) ^ α)]
          exact test_term_le_w hα hx.ne hwx
  · rw [weightedHellingerIntegral_of_not_ac _ hac]; exact le_top

/-- Two tests on one space whose pointwise Hellinger term is at most `1` almost everywhere
    are bounded by the Hellinger integral: the weight-one case. -/
theorem testVal_le_hellingerIntegral_same {α : ℝ} (hα : 1 < α) {K₁ K₂ : Ω → ℝ≥0∞}
    (hK₁ : Measurable K₁) (hK₂ : Measurable K₂) (μ ν : Measure Ω) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (h : ∀ᵐ x ∂ν, K₁ x ^ α * K₂ x ^ (1 - α) ≤ 1) :
    (∫⁻ x, K₁ x ∂μ) ^ α * (∫⁻ x, K₂ x ∂ν) ^ (1 - α) ≤ hellingerIntegral α μ ν :=
  testVal_le_weightedHellingerIntegral_same hα hK₁ hK₂ μ ν h

end Measures

section Lifting

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

/-- Admissible tests for a postcondition `Q` and a weight `ψ` on pairs. -/
def TestAdmW (α : ℝ) (Q : A × B → Prop) (ψ : A × B → ℝ≥0∞) (k₁ : A → ℝ≥0∞)
    (k₂ : B → ℝ≥0∞) : Prop :=
  ∀ p, Q p → k₁ p.1 ^ α * k₂ p.2 ^ (1 - α) ≤ ψ p

end Lifting

/-! ## The judgment -/

variable {ident : Type} {M : MemType ident}


/-- The expectation transformer of a statement, on memories with transcripts. -/
noncomputable def ewp (c : Cmd ident M) (k : St M → ℝ≥0∞) (s : St M) : ℝ≥0∞ :=
  ∫⁻ x, k x ∂(osemA c s)

/-- **Definition 4.1 (validity)**: from every pair of states in `P`, every pair of
    measurable tests admissible for `(Q, ψ)` has test value at most `φ`. -/
def RRhl (α : ℝ) (P : St M × St M → Prop) (φ : St M × St M → ℝ≥0∞) (c₁ c₂ : Cmd ident M)
    (Q : St M × St M → Prop) (ψ : St M × St M → ℝ≥0∞) : Prop :=
  ∀ s, P s → ∀ k₁ k₂ : St M → ℝ≥0∞, Measurable k₁ → Measurable k₂ → TestAdmW α Q ψ k₁ k₂ →
    testValC α (osemA c₁ s.1) (osemA c₂ s.2) k₁ k₂ ≤ φ s

/-! ## The expectation transformer on loop-free statements -/

section Ewp

variable {k : St M → ℝ≥0∞}

lemma measurable_ewp {c : Cmd ident M} (hk : Measurable k) :
    Measurable (ewp c k) :=
  (Measure.measurable_lintegral hk).comp (osemA_measurable _)

lemma ewp_random (hk : Measurable k) {t : Ty} (x : Vars ident t)
    (κ : @ProbabilityTheory.Kernel M.heap t.interp M.heapMeas (Ty.measurableSpace t))
    [IsSubMarkovKernel κ]
    (s : St M) :
    ewp (Cmd.random x κ) k s = ∫⁻ v, k (M.set s.1 t x.name v, s.2) ∂(κ s.1) := by
  have hu : Measurable (fun v : t.interp => ((M.set s.1 t x.name v, s.2) : St M)) :=
    ((M.set_measurable x.name).comp measurable_prodMk_left).prodMk measurable_const
  show ∫⁻ y, k y ∂((κ s.1).bind (fun v => Measure.dirac (M.set s.1 t x.name v, s.2))) = _
  rw [Measure.bind_dirac_eq_map _ hu, lintegral_map hk hu]

lemma ewp_seq (hk : Measurable k) {c c' : Cmd ident M} (s : St M) :
    ewp (Cmd.seq c c') k s = ewp c (ewp c' k) s := by
  show ∫⁻ y, k y ∂((osemA c s).bind (osemA c')) = _
  rw [Measure.lintegral_bind (osemA_measurable _).aemeasurable hk.aemeasurable]
  rfl

end Ewp

/-! ## Structural rules -/

/-- **[Conseq]**. -/
theorem rrhl_conseq {α : ℝ} {P P₀ Q Q₀ : St M × St M → Prop}
    {φ φ₀ ψ ψ₀ : St M × St M → ℝ≥0∞} {c₁ c₂ : Cmd ident M}
    (hP : ∀ s, P s → P₀ s) (hφ : ∀ s, P s → φ₀ s ≤ φ s) (hQ : ∀ s, Q₀ s → Q s)
    (hψ : ∀ s, Q₀ s → ψ s ≤ ψ₀ s) (h : RRhl α P₀ φ₀ c₁ c₂ Q₀ ψ₀) :
    RRhl α P φ c₁ c₂ Q ψ := fun s hs k₁ k₂ hk₁ hk₂ hk =>
  (h s (hP s hs) k₁ k₂ hk₁ hk₂ fun p hp => (hk p (hQ p hp)).trans (hψ p hp)).trans (hφ s hs)

/-- Two statements whose semantics are Dirac measures; [Skip], [Assn] and [Release] are
    instances. -/
theorem rrhl_det {α : ℝ} {c₁ c₂ : Cmd ident M} {g₁ g₂ : St M → St M}
    (hc₁ : ∀ s, osemA c₁ s = Measure.dirac (g₁ s))
    (hc₂ : ∀ s, osemA c₂ s = Measure.dirac (g₂ s))
    (Q : St M × St M → Prop) (ψ : St M × St M → ℝ≥0∞) :
    RRhl α (fun s => Q (g₁ s.1, g₂ s.2)) (fun s => ψ (g₁ s.1, g₂ s.2)) c₁ c₂ Q ψ := by
  intro s hs k₁ k₂ hk₁ hk₂ hk
  rw [testValC, hc₁, hc₂, lintegral_dirac' _ hk₁, lintegral_dirac' _ hk₂]
  exact hk (g₁ s.1, g₂ s.2) hs

/-- **[Skip]**. -/
theorem rrhl_skip {α : ℝ} (Q : St M × St M → Prop) (ψ : St M × St M → ℝ≥0∞) :
    RRhl (M := M) α Q ψ Cmd.skip Cmd.skip Q ψ :=
  rrhl_det (g₁ := id) (g₂ := id) (fun _ => rfl) (fun _ => rfl) Q ψ

/-- **[Assn]**. -/
theorem rrhl_assign {α : ℝ} {t₁ t₂ : Ty}
    (x₁ : Vars ident t₁) (e₁ : Expr M t₁)
    (x₂ : Vars ident t₂) (e₂ : Expr M t₂)
    (Q : St M × St M → Prop) (ψ : St M × St M → ℝ≥0∞) :
    RRhl α
      (fun s => Q ((M.set s.1.1 t₁ x₁.name (esem e₁ s.1.1), s.1.2),
                   (M.set s.2.1 t₂ x₂.name (esem e₂ s.2.1), s.2.2)))
      (fun s => ψ ((M.set s.1.1 t₁ x₁.name (esem e₁ s.1.1), s.1.2),
                   (M.set s.2.1 t₂ x₂.name (esem e₂ s.2.1), s.2.2)))
      (Cmd.assign x₁ e₁) (Cmd.assign x₂ e₂) Q ψ :=
  rrhl_det (g₁ := fun s => (M.set s.1 t₁ x₁.name (esem e₁ s.1), s.2))
    (g₂ := fun s => (M.set s.1 t₂ x₂.name (esem e₂ s.1), s.2)) (fun _ => rfl) (fun _ => rfl) Q ψ

/-- **[Release]**. -/
theorem rrhl_release {α : ℝ} {t : Ty} (e₁ e₂ : Expr M t)
    (Q : St M × St M → Prop) (ψ : St M × St M → ℝ≥0∞) :
    RRhl α
      (fun s => Q ((s.1.1, s.1.2.snoc ⟨t, esem e₁ s.1.1⟩),
                   (s.2.1, s.2.2.snoc ⟨t, esem e₂ s.2.1⟩)))
      (fun s => ψ ((s.1.1, s.1.2.snoc ⟨t, esem e₁ s.1.1⟩),
                   (s.2.1, s.2.2.snoc ⟨t, esem e₂ s.2.1⟩)))
      (Cmd.release e₁) (Cmd.release e₂) Q ψ :=
  rrhl_det (g₁ := fun s => (s.1, s.2.snoc ⟨t, esem e₁ s.1⟩))
    (g₂ := fun s => (s.1, s.2.snoc ⟨t, esem e₂ s.1⟩)) (fun _ => rfl) (fun _ => rfl) Q ψ

/-- **[Seq]**: the tests are integrated through the second pair of statements. -/
theorem rrhl_seq {α : ℝ} {P Q R : St M × St M → Prop} {φ ψ χ : St M × St M → ℝ≥0∞}
    {c₁ c₂ c₁' c₂' : Cmd ident M} 
    (h : RRhl α P φ c₁ c₂ Q ψ) (h' : RRhl α Q ψ c₁' c₂' R χ) :
    RRhl α P φ (Cmd.seq c₁ c₁') (Cmd.seq c₂ c₂') R χ := by
  intro s hs k₁ k₂ hk₁ hk₂ hk
  have e₁ := ewp_seq hk₁ (c := c₁) (c' := c₁') s.1
  have e₂ := ewp_seq hk₂ (c := c₂) (c' := c₂') s.2
  unfold ewp at e₁ e₂
  rw [testValC, e₁, e₂]
  exact h s hs _ _ (measurable_ewp hk₁) (measurable_ewp hk₂)
    (fun p hp => h' p hp k₁ k₂ hk₁ hk₂ hk)

/-- **[If]** (synchronized conditional). -/
theorem rrhl_if {α : ℝ} {P Q : St M × St M → Prop} {φ ψ : St M × St M → ℝ≥0∞}
    {e₁ e₂ : BExpr M} {c1t c2t c1e c2e : Cmd ident M}
    (hsync : ∀ s, P s → esem e₁ s.1.1 = esem e₂ s.2.1)
    (hthen : RRhl α (fun s => P s ∧ esem e₁ s.1.1 = true) φ c1t c2t Q ψ)
    (helse : RRhl α (fun s => P s ∧ esem e₁ s.1.1 = false) φ c1e c2e Q ψ) :
    RRhl α P φ (Cmd.cond e₁ c1t c1e) (Cmd.cond e₂ c2t c2e) Q ψ := by
  intro s hs k₁ k₂ hk₁ hk₂ hk
  show testValC α (if esem e₁ s.1.1 then osemA c1t s.1 else osemA c1e s.1)
    (if esem e₂ s.2.1 then osemA c2t s.2 else osemA c2e s.2) k₁ k₂ ≤ φ s
  rw [← hsync s hs]
  cases hg : esem e₁ s.1.1 with
  | true => simpa using hthen s ⟨hs, hg⟩ k₁ k₂ hk₁ hk₂ hk
  | false => simpa using helse s ⟨hs, hg⟩ k₁ k₂ hk₁ hk₂ hk

/-! ## The loop rule -/

/-- The observational semantics of the guarded unrolling is the loop approximant. -/
lemma osemA_unrollWhile (e : BExpr M) (c : Cmd ident M) :
    ∀ k, osemA (unrollWhile e c k) = oubn (osemA c) (esem e) k
  | 0 => rfl
  | k + 1 => by
    funext s
    show (if esem e s.1 then (osemA c s).bind (osemA (unrollWhile e c k))
        else Measure.dirac s)
      = (if esem e s.1 then (osemA c s).bind (oubn (osemA c) (esem e) k)
        else Measure.dirac s)
    rw [osemA_unrollWhile e c k]

/-- A judgment with an unsatisfiable precondition. -/
theorem rrhl_bot {α : ℝ} {P Q : St M × St M → Prop} {φ ψ : St M × St M → ℝ≥0∞}
    {c₁ c₂ : Cmd ident M} (h : ∀ s, ¬ P s) : RRhl α P φ c₁ c₂ Q ψ :=
  fun s hs => absurd hs (h s)

/-! ## [While] -/

/-- A positive power commutes with suprema in `ℝ≥0∞`. -/
lemma iSup_rpow_pos {ι : Sort*} [Nonempty ι] {f : ι → ℝ≥0∞} {p : ℝ} (hp : 0 < p) :
    (⨆ i, f i) ^ p = ⨆ i, f i ^ p := by
  refine le_antisymm ?_ (iSup_le fun i => ENNReal.rpow_le_rpow (le_iSup f i) hp.le)
  have h : ∀ i, f i ≤ (⨆ i, f i ^ p) ^ p⁻¹ := fun i =>
    calc f i = (f i ^ p) ^ p⁻¹ := by
          rw [← ENNReal.rpow_mul, mul_inv_cancel₀ hp.ne', ENNReal.rpow_one]
      _ ≤ (⨆ i, f i ^ p) ^ p⁻¹ :=
          ENNReal.rpow_le_rpow (le_iSup (fun i => f i ^ p) i) (by positivity)
  calc (⨆ i, f i) ^ p ≤ ((⨆ i, f i ^ p) ^ p⁻¹) ^ p := ENNReal.rpow_le_rpow (iSup_le h) hp.le
    _ = ⨆ i, f i ^ p := by
        rw [← ENNReal.rpow_mul, inv_mul_cancel₀ hp.ne', ENNReal.rpow_one]

/-- A nonpositive power is antitone in `ℝ≥0∞`. -/
lemma rpow_antitone_of_nonpos {x y : ℝ≥0∞} {p : ℝ} (hxy : x ≤ y) (hp : p ≤ 0) :
    y ^ p ≤ x ^ p := by
  rw [← neg_neg p, ENNReal.rpow_neg x, ENNReal.rpow_neg y]
  exact ENNReal.inv_le_inv.mpr (ENNReal.rpow_le_rpow hxy (by linarith))

/-- **The Lebesgue integral commutes with a monotone supremum of measures.** -/
lemma lintegral_iSup_measure {Ω : Type*} [MeasurableSpace Ω] {μ : ℕ → Measure Ω}
    (hmon : Monotone μ) (f : Ω → ℝ≥0∞) :
    ∫⁻ a, f a ∂(⨆ n, μ n) = ⨆ n, ∫⁻ a, f a ∂(μ n) := by
  refine le_antisymm ?_ (iSup_le fun n => lintegral_mono' (le_iSup μ n) le_rfl)
  rw [lintegral_def]
  refine iSup_le fun g => iSup_le fun hg => ?_
  have hfib : ∀ x, (⨆ n, μ n) (g ⁻¹' {x}) = ⨆ n, μ n (g ⁻¹' {x}) :=
    fun x => iSup_measure_apply hmon (g.measurableSet_fiber x)
  calc g.lintegral (⨆ n, μ n)
      = ∑ x ∈ g.range, x * ⨆ n, μ n (g ⁻¹' {x}) := by
        simp only [SimpleFunc.lintegral, hfib]
    _ = ⨆ n, ∑ x ∈ g.range, x * μ n (g ⁻¹' {x}) := by
        simp_rw [ENNReal.mul_iSup]
        exact ENNReal.finsetSum_iSup_of_monotone fun x i j hij =>
          mul_le_mul' le_rfl (hmon hij _)
    _ ≤ ⨆ n, ∫⁻ a, f a ∂(μ n) := iSup_mono fun n => by
        show g.lintegral (μ n) ≤ _
        rw [← SimpleFunc.lintegral_eq_lintegral]
        exact lintegral_mono hg

/-- **[While]**: the invariant family `P` and budgets `φ` are indexed by the number `k` of
    completed rounds; a round with both guards true moves `P k` to `P (k+1)`, spending
    `φ k` down to `φ (k+1)`, and the exit data `(E, ψ)` is read wherever the loops stop.
    No variant or termination condition.

    Proof: bound every unrolling depth and pass to the limit; the left integral is
    continuous from below and the right factor has the negative exponent `1 - α`. -/
theorem rrhl_while_gen {α : ℝ} (hα : 1 < α) {e₁ e₂ : BExpr M} {c₁ c₂ : Cmd ident M}
    (P : ℕ → St M × St M → Prop) (φ : ℕ → St M × St M → ℝ≥0∞)
    (E : St M × St M → Prop) (ψ : St M × St M → ℝ≥0∞)
    (dstep : ∀ k, RRhl α
      (fun s => P k s ∧ esem e₁ s.1.1 = true ∧ esem e₂ s.2.1 = true) (φ k)
      c₁ c₂ (P (k + 1)) (φ (k + 1)))
    (hsync : ∀ k s, P k s → esem e₁ s.1.1 = esem e₂ s.2.1)
    (hexit : ∀ k s, P k s → esem e₁ s.1.1 = false → E s ∧ ψ s ≤ φ k s) :
    RRhl α (P 0) (φ 0) (Cmd.while e₁ c₁) (Cmd.while e₂ c₂)
      (fun s => E s ∧ esem e₁ s.1.1 = false ∧ esem e₂ s.2.1 = false) ψ := by
  -- the judgment holds at *every* unrolling depth, at every level of the family
  have hiter : ∀ j k, RRhl α (P k) (φ k)
      (unrollWhile e₁ c₁ j) (unrollWhile e₂ c₂ j)
      (fun s => E s ∧ esem e₁ s.1.1 = false ∧ esem e₂ s.2.1 = false) ψ := by
    intro j
    induction j with
    | zero =>
      intro k s _ κ₁ κ₂ _ _ _
      show testValC α (osemA (unrollWhile e₁ c₁ 0) s.1)
        (osemA (unrollWhile e₂ c₂ 0) s.2) κ₁ κ₂ ≤ φ k s
      rw [show unrollWhile e₁ c₁ 0 = Cmd.abort from rfl,
        show unrollWhile e₂ c₂ 0 = Cmd.abort from rfl, testValC,
        show osemA (Cmd.abort : Cmd ident M) s.1 = 0 from rfl,
        lintegral_zero_measure, ENNReal.zero_rpow_of_pos (by linarith : (0:ℝ) < α), zero_mul]
      exact zero_le
    | succ j ih =>
      intro k
      refine rrhl_if (hsync k) ?_ ?_
      · refine rrhl_conseq (fun s hs => ?_) (fun _ _ => le_rfl) (fun _ h => h)
          (fun _ _ => le_rfl) (rrhl_seq (dstep k) (ih (k + 1)))
        exact ⟨hs.1, hs.2, by rw [← hsync k s hs.1]; exact hs.2⟩
      · refine rrhl_conseq (fun s hs => ?_)
          (fun s hs => (hexit k s hs.1 hs.2).2)
          (fun _ h => h) (fun _ _ => le_rfl) (rrhl_skip _ ψ)
        exact ⟨(hexit k s hs.1 hs.2).1, hs.2,
          by rw [← hsync k s hs.1]; exact hs.2⟩
  -- pass to the limit: continuity from below on the left, monotonicity on the right
  intro s hs κ₁ κ₂ hκ₁ hκ₂ hadm
  have key : ∀ j, (∫⁻ x, κ₁ x ∂(oubn (osemA c₁) (esem e₁) j s.1)) ^ α
      * (∫⁻ x, κ₂ x ∂(oubn (osemA c₂) (esem e₂) j s.2)) ^ (1 - α) ≤ φ 0 s := by
    intro j
    have h := hiter j 0 s hs κ₁ κ₂ hκ₁ hκ₂ hadm
    rwa [testValC, osemA_unrollWhile, osemA_unrollWhile] at h
  have hmon₁ : Monotone (fun j => oubn (osemA c₁) (esem e₁) j s.1) :=
    oubn_monotone (osemA_measurable _) e₁.measurable s.1
  have hmon₂ : Monotone (fun j => oubn (osemA c₂) (esem e₂) j s.2) :=
    oubn_monotone (osemA_measurable _) e₂.measurable s.2
  show testValC α (osemA (Cmd.while e₁ c₁) s.1) (osemA (Cmd.while e₂ c₂) s.2) κ₁ κ₂ ≤ φ 0 s
  rw [testValC,
    show osemA (Cmd.while e₁ c₁) s.1 = ⨆ j, oubn (osemA c₁) (esem e₁) j s.1 from rfl,
    show osemA (Cmd.while e₂ c₂) s.2 = ⨆ j, oubn (osemA c₂) (esem e₂) j s.2 from rfl,
    lintegral_iSup_measure hmon₁, lintegral_iSup_measure hmon₂,
    iSup_rpow_pos (by linarith : (0:ℝ) < α), ENNReal.iSup_mul]
  refine iSup_le fun j => ?_
  exact le_trans (mul_le_mul' le_rfl (rpow_antitone_of_nonpos
    (le_iSup (fun i => ∫⁻ x, κ₂ x ∂(oubn (osemA c₂) (esem e₂) i s.2)) j)
    (by linarith : (1 : ℝ) - α ≤ 0))) (key j)

end Continuous
