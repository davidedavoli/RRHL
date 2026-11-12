import Xhl.Divergence.Weighted

/-!
# Dual characterization of the weighted Hellinger integral

`weightedHellingerIntegral_eq_testSupW` (Theorem 3.2): for a `GoodWeight` `w`, the weighted
Hellinger integral is the supremum `testSupW` of `(∫ k₁ dμ)^α (∫ k₂ dν)^(1−α)` over measurable
tests with `k₁^α k₂^(1−α) ≤ w`. The easy half (`testSupW_le_weightedHellingerIntegral`) needs no
hypothesis on `w`. For the other half, with `r = dμ/dν`, the pair `k₁ = w · r^(α−1)`,
`k₂ = w · r^α` attains the value, restricted to sets of finite integral and exhausted by
monotone convergence; when `¬ μ ≪ ν` an indicator pair gives `⊤`.
-/

open MeasureTheory ENNReal

namespace Continuous

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `k₁^α k₂^(1−α) ≤ w` pointwise: the admissibility of a pair of tests for a weight. -/
def TestAdm (α : ℝ) (w : Ω → ℝ≥0∞) (k₁ k₂ : Ω → ℝ≥0∞) : Prop :=
  ∀ a, k₁ a ^ α * k₂ a ^ (1 - α) ≤ w a

/-- The dual value of the weighted Hellinger integral: the supremum of
    `(∫ k₁ dμ)^α (∫ k₂ dν)^(1−α)` over admissible pairs of measurable tests. -/
noncomputable def testSupW (α : ℝ) (w : Ω → ℝ≥0∞) (μ ν : Measure Ω) : ℝ≥0∞ :=
  ⨆ (k₁ : Ω → ℝ≥0∞) (k₂ : Ω → ℝ≥0∞) (_ : Measurable k₁) (_ : Measurable k₂)
    (_ : TestAdm α w k₁ k₂), (∫⁻ a, k₁ a ∂μ) ^ α * (∫⁻ a, k₂ a ∂ν) ^ (1 - α)

lemma le_testSupW {α : ℝ} {w : Ω → ℝ≥0∞} {μ ν : Measure Ω} {k₁ k₂ : Ω → ℝ≥0∞}
    (h₁ : Measurable k₁) (h₂ : Measurable k₂) (hadm : TestAdm α w k₁ k₂) :
    (∫⁻ a, k₁ a ∂μ) ^ α * (∫⁻ a, k₂ a ∂ν) ^ (1 - α) ≤ testSupW α w μ ν :=
  le_iSup_of_le k₁ (le_iSup_of_le k₂ (le_iSup_of_le h₁ (le_iSup_of_le h₂
    (le_iSup_of_le hadm le_rfl))))

/-! ## The easy half, on one space -/

/-- **The easy half of duality**, with no hypothesis on the weight. -/
theorem testSupW_le_weightedHellingerIntegral {α : ℝ} (hα : 1 < α) (w : Ω → ℝ≥0∞) (μ ν : Measure Ω)
    [SigmaFinite μ] [SigmaFinite ν] : testSupW α w μ ν ≤ weightedHellingerIntegral α w μ ν := by
  by_cases hac : μ ≪ ν
  · rw [weightedHellingerIntegral_of_ac _ hac]
    refine iSup_le fun k₁ => iSup_le fun k₂ => iSup_le fun h₁ => iSup_le fun h₂ =>
      iSup_le fun hadm => ?_
    calc (∫⁻ a, k₁ a ∂μ) ^ α * (∫⁻ a, k₂ a ∂ν) ^ (1 - α)
        = (∫⁻ a, μ.rnDeriv ν a * k₁ a ∂ν) ^ α * (∫⁻ a, k₂ a ∂ν) ^ (1 - α) := by
          rw [lintegral_rnDeriv_mul hac h₁.aemeasurable]
      _ ≤ ∫⁻ a, (μ.rnDeriv ν a * k₁ a) ^ α * k₂ a ^ (1 - α) ∂ν :=
          lintegral_rpow_mul_rpow_le _ _ hα
            (((Measure.measurable_rnDeriv μ ν).mul h₁).aemeasurable) h₂.aemeasurable
      _ ≤ ∫⁻ a, μ.rnDeriv ν a ^ α * w a ∂ν := by
          refine lintegral_mono fun a => ?_
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by linarith : (0:ℝ) ≤ α), mul_assoc]
          exact mul_le_mul' le_rfl (hadm a)
  · rw [weightedHellingerIntegral_of_not_ac _ hac]; exact le_top

/-! ## The other half -/

/-- When `μ ⋠ ν` the dual value is already `⊤`: put the test on the left on a `ν`-null set
    carrying `μ`-mass, and the test on the right at `⊤` there, which costs nothing against
    `ν` because the set is null. -/
lemma testSupW_eq_top_of_not_ac {α : ℝ} (hα : 1 < α) (w : Ω → ℝ≥0∞) {μ ν : Measure Ω}
    (hac : ¬ μ ≪ ν) : testSupW α w μ ν = ⊤ := by
  have h1α : (1 : ℝ) - α < 0 := by linarith
  have hα0 : (0 : ℝ) < α := by linarith
  obtain ⟨S, hνS, hμS⟩ : ∃ S, ν S = 0 ∧ μ S ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hac fun s hs => hcon s hs
  obtain ⟨T, hST, hTm, hνT⟩ := exists_measurable_superset_of_null hνS
  have hμT : μ T ≠ 0 := fun h => hμS (measure_mono_null hST h)
  have hadm : TestAdm α w (T.indicator (fun _ => 1)) (T.indicator (fun _ => ⊤)) := by
    intro a
    by_cases ha : a ∈ T
    · rw [Set.indicator_of_mem ha, Set.indicator_of_mem ha,
        ENNReal.top_rpow_of_neg h1α, mul_zero]
      exact zero_le
    · rw [Set.indicator_of_notMem ha, Set.indicator_of_notMem ha,
        ENNReal.zero_rpow_of_pos hα0, zero_mul]
      exact zero_le
  have hi₁ : ∫⁻ a, T.indicator (fun _ => (1 : ℝ≥0∞)) a ∂μ = μ T := by
    rw [lintegral_indicator hTm, setLIntegral_one]
  have hi₂ : ∫⁻ a, T.indicator (fun _ => (⊤ : ℝ≥0∞)) a ∂ν = 0 := by
    rw [lintegral_indicator hTm, setLIntegral_const, hνT, mul_zero]
  have hpos : (0 : ℝ≥0∞) < μ T ^ α := by
    rcases eq_or_ne (μ T) ⊤ with h | h
    · rw [h, ENNReal.top_rpow_of_pos hα0]; simp
    · exact ENNReal.rpow_pos (pos_iff_ne_zero.mpr hμT) h
  have hle := le_testSupW (μ := μ) (ν := ν) (w := w) (α := α)
    (measurable_const.indicator hTm) (measurable_const.indicator hTm) hadm
  rw [hi₁, hi₂, ENNReal.zero_rpow_of_neg h1α, ENNReal.mul_top hpos.ne'] at hle
  exact top_le_iff.mp hle

/-- **Strong duality.**  For a measurable, everywhere non-zero and everywhere finite
    weight, the supremum over admissible pairs of tests *is* the weighted Hellinger
    integral.  No uniform bound on the weight. -/
theorem weightedHellingerIntegral_le_testSupW {α : ℝ} (hα : 1 < α) {w : Ω → ℝ≥0∞} (hw : GoodWeight w)
    (μ ν : Measure Ω) [SigmaFinite μ] [SigmaFinite ν] :
    weightedHellingerIntegral α w μ ν ≤ testSupW α w μ ν := by
  have hα0 : (0 : ℝ) < α := by linarith
  have h1α : (1 : ℝ) - α < 0 := by linarith
  have hα1 : (0 : ℝ) < α - 1 := by linarith
  by_cases hac : μ ≪ ν
  swap
  · rw [testSupW_eq_top_of_not_ac hα w hac]; exact le_top
  rw [weightedHellingerIntegral_of_ac _ hac]
  set r : Ω → ℝ≥0∞ := fun a => μ.rnDeriv ν a with hrdef
  have hrm : Measurable r := Measure.measurable_rnDeriv μ ν
  set F : Ω → ℝ≥0∞ := fun a => r a ^ α * w a with hFdef
  have hFm : Measurable F := (hrm.pow_const α).mul hw.meas
  -- the pieces: `ν`-finite, `F` bounded, `r` finite
  set A : ℕ → Set Ω := fun n =>
    spanningSets ν n ∩ {a | F a ≤ (n : ℝ≥0∞)} ∩ {a | r a ≠ ⊤} with hAdef
  have hAm : ∀ n, MeasurableSet (A n) := fun n =>
    ((measurableSet_spanningSets ν n).inter (hFm measurableSet_Iic)).inter
      (hrm (MeasurableSet.singleton ⊤)).compl
  have hAmono : Monotone A := by
    intro m n hmn a ha
    have hcast : ((m : ℕ) : ℝ≥0∞) ≤ ((n : ℕ) : ℝ≥0∞) := by exact_mod_cast hmn
    exact ⟨⟨monotone_spanningSets ν hmn ha.1.1, le_trans ha.1.2 hcast⟩, ha.2⟩
  have hind : Monotone (fun n => (A n).indicator F) := by
    intro m n hmn a
    show (A m).indicator F a ≤ (A n).indicator F a
    by_cases ha : a ∈ A m
    · rw [Set.indicator_of_mem ha, Set.indicator_of_mem (hAmono hmn ha)]
    · rw [Set.indicator_of_notMem ha]; exact zero_le
  have hsupF : ∀ a, r a ≠ ⊤ → (⨆ n, (A n).indicator F a) = F a := by
    intro a ha
    have hFa : F a ≠ ⊤ :=
      ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hα0.le ha) (hw.ne_top a)
    obtain ⟨n, hn⟩ := exists_nat_ge (F a).toReal
    obtain ⟨m, hm⟩ := Set.iUnion_eq_univ_iff.mp (iUnion_spanningSets ν) a
    refine le_antisymm (iSup_le fun k => ?_) ?_
    · by_cases hk : a ∈ A k
      · rw [Set.indicator_of_mem hk]
      · rw [Set.indicator_of_notMem hk]; exact zero_le
    · refine le_iSup_of_le (max n m) ?_
      rw [Set.indicator_of_mem]
      refine ⟨⟨monotone_spanningSets ν (le_max_right n m) hm, ?_⟩, ha⟩
      calc F a = ENNReal.ofReal (F a).toReal := (ENNReal.ofReal_toReal hFa).symm
        _ ≤ ENNReal.ofReal (n : ℝ) := ENNReal.ofReal_le_ofReal hn
        _ = (n : ℝ≥0∞) := by simp
        _ ≤ ((max n m : ℕ) : ℝ≥0∞) := by exact_mod_cast le_max_left n m
  have hrlt : ∀ᵐ a ∂ν, r a ≠ ⊤ := by
    filter_upwards [μ.rnDeriv_lt_top ν] with a ha using ha.ne
  have hmct : ∫⁻ a, F a ∂ν = ⨆ n, ∫⁻ a in A n, F a ∂ν := by
    have h1 : ∫⁻ a, F a ∂ν = ∫⁻ a, ⨆ n, (A n).indicator F a ∂ν := by
      refine lintegral_congr_ae ?_
      filter_upwards [hrlt] with a ha using (hsupF a ha).symm
    rw [h1, lintegral_iSup (fun n => hFm.indicator (hAm n)) hind]
    exact iSup_congr fun n => lintegral_indicator (hAm n) F
  rw [hmct]
  refine iSup_le fun n => ?_
  -- the piece is finite
  have hpfin : (∫⁻ a in A n, F a ∂ν) ≠ ⊤ := by
    have hb : ∫⁻ a in A n, F a ∂ν ≤ (n : ℝ≥0∞) * ν (A n) := by
      rw [← setLIntegral_const (A n) ((n : ℝ≥0∞))]
      exact setLIntegral_mono measurable_const fun a ha => ha.1.2
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (by simp) ?_) hb
    exact (lt_of_le_of_lt (measure_mono fun a ha => ha.1.1)
      (measure_spanningSets_lt_top ν n)).ne
  -- the optimiser of the reverse Hölder inequality, cut down to the piece
  have hk₁m : Measurable ((A n).indicator (fun a => w a * r a ^ (α - 1))) :=
    (hw.meas.mul (hrm.pow_const _)).indicator (hAm n)
  have hk₂m : Measurable ((A n).indicator (fun a => w a * r a ^ α)) :=
    (hw.meas.mul (hrm.pow_const _)).indicator (hAm n)
  have hadm : TestAdm α w ((A n).indicator (fun a => w a * r a ^ (α - 1)))
      ((A n).indicator (fun a => w a * r a ^ α)) := by
    intro a
    by_cases ha : a ∈ A n
    · rw [Set.indicator_of_mem ha, Set.indicator_of_mem ha]
      by_cases hr0 : r a = 0
      · rw [hr0, ENNReal.zero_rpow_of_pos hα1, ENNReal.zero_rpow_of_pos hα0,
          mul_zero, ENNReal.zero_rpow_of_pos hα0, zero_mul]
        exact zero_le
      · have hrt : r a ≠ ⊤ := ha.2
        have hwadd : w a ^ α * w a ^ (1 - α) = w a := by
          rw [← ENNReal.rpow_add _ _ (hw.ne_zero a) (hw.ne_top a),
            show α + (1 - α) = (1 : ℝ) by ring, ENNReal.rpow_one]
        have hradd : r a ^ ((α - 1) * α) * r a ^ (α * (1 - α)) = 1 := by
          rw [← ENNReal.rpow_add _ _ hr0 hrt,
            show (α - 1) * α + α * (1 - α) = (0 : ℝ) by ring, ENNReal.rpow_zero]
        calc (w a * r a ^ (α - 1)) ^ α * (w a * r a ^ α) ^ (1 - α)
            = w a ^ α * r a ^ ((α - 1) * α) * (w a ^ (1 - α) * r a ^ (α * (1 - α))) := by
              rw [ENNReal.mul_rpow_of_ne_top (hw.ne_top a)
                    (ENNReal.rpow_ne_top_of_nonneg hα1.le hrt) α,
                ENNReal.mul_rpow_of_ne_top (hw.ne_top a)
                    (ENNReal.rpow_ne_top_of_nonneg hα0.le hrt) (1 - α),
                ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
          _ = w a ^ α * w a ^ (1 - α) * (r a ^ ((α - 1) * α) * r a ^ (α * (1 - α))) := by
              ring
          _ = w a := by rw [hwadd, hradd, mul_one]
          _ ≤ w a := le_rfl
    · rw [Set.indicator_of_notMem ha, Set.indicator_of_notMem ha,
        ENNReal.zero_rpow_of_pos hα0, zero_mul]
      exact zero_le
  -- both integrals are the piece
  have hpt₁ : ∀ a, r a * (A n).indicator (fun a => w a * r a ^ (α - 1)) a
      = (A n).indicator F a := by
    intro a
    by_cases ha : a ∈ A n
    · rw [Set.indicator_of_mem ha, Set.indicator_of_mem ha]
      simp only [hFdef]
      by_cases hr0 : r a = 0
      · simp [hr0, ENNReal.zero_rpow_of_pos hα1, ENNReal.zero_rpow_of_pos hα0]
      · have hrt : r a ≠ ⊤ := ha.2
        calc r a * (w a * r a ^ (α - 1))
            = w a * (r a ^ (1 : ℝ) * r a ^ (α - 1)) := by rw [ENNReal.rpow_one]; ring
          _ = w a * r a ^ α := by
              rw [← ENNReal.rpow_add _ _ hr0 hrt, show (1 : ℝ) + (α - 1) = α by ring]
          _ = r a ^ α * w a := by ring
    · rw [Set.indicator_of_notMem ha, Set.indicator_of_notMem ha, mul_zero]
  have hpt₂ : ∀ a, (A n).indicator (fun a => w a * r a ^ α) a = (A n).indicator F a := by
    intro a
    by_cases ha : a ∈ A n
    · rw [Set.indicator_of_mem ha, Set.indicator_of_mem ha]
      simp only [hFdef]; ring
    · rw [Set.indicator_of_notMem ha, Set.indicator_of_notMem ha]
  have hval₁ : ∫⁻ a, (A n).indicator (fun a => w a * r a ^ (α - 1)) a ∂μ
      = ∫⁻ a in A n, F a ∂ν := by
    rw [← lintegral_rnDeriv_mul hac hk₁m.aemeasurable, lintegral_congr hpt₁,
      lintegral_indicator (hAm n) F]
  have hval₂ : ∫⁻ a, (A n).indicator (fun a => w a * r a ^ α) a ∂ν
      = ∫⁻ a in A n, F a ∂ν := by
    rw [lintegral_congr hpt₂, lintegral_indicator (hAm n) F]
  have hle := le_testSupW (μ := μ) (ν := ν) (w := w) (α := α) hk₁m hk₂m hadm
  rw [hval₁, hval₂] at hle
  rcases eq_or_ne (∫⁻ a in A n, F a ∂ν) 0 with h0 | h0
  · rw [h0]; exact zero_le
  · have hid : (∫⁻ a in A n, F a ∂ν) ^ α * (∫⁻ a in A n, F a ∂ν) ^ (1 - α)
        = ∫⁻ a in A n, F a ∂ν := by
      rw [← ENNReal.rpow_add _ _ h0 hpfin, show α + (1 - α) = (1 : ℝ) by ring,
        ENNReal.rpow_one]
    rw [← hid]; exact hle

/-- **Dual characterization of the weighted Hellinger integral** (Theorem 3.2), for a
    measurable, everywhere non-zero, everywhere finite weight. -/
theorem weightedHellingerIntegral_eq_testSupW {α : ℝ} (hα : 1 < α) {w : Ω → ℝ≥0∞} (hw : GoodWeight w)
    (μ ν : Measure Ω) [SigmaFinite μ] [SigmaFinite ν] :
    weightedHellingerIntegral α w μ ν = testSupW α w μ ν :=
  le_antisymm (weightedHellingerIntegral_le_testSupW hα hw μ ν) (testSupW_le_weightedHellingerIntegral hα w μ ν)

end Continuous
