/-
  Differential-privacy definitions for mechanisms `M : A → Measure B` with an adjacency
  relation `Adj` on inputs:

  * `EpsilonDeltaDP` — `(ε,δ)`-DP (Definition 2.1);
  * `renyiDiv`, `RenyiDP` — Rényi divergence and Rényi DP (Definition 3.4);
  * `RenyiDP.epsilonDeltaDP` — conversion to `(ε,δ)`-DP (Proposition 3.5);
  * `IndivRenyiDP` — individual RDP (Definition 3.6);
  * `IndivRenyiDP.renyiDP_iSup` — individual to global RDP (Lemma 3.7).
-/
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Xhl.Divergence.ChainUncond
import Xhl.Divergence.Convert

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace Continuous

variable {A B C : Type*} [MeasurableSpace B] [MeasurableSpace C]
variable {Ω : Type*} [MeasurableSpace Ω]

/-- **`(ε,δ)`-differential privacy** (Definition 2.1). -/
def EpsilonDeltaDP (ε δ : ℝ) (Adj : A → A → Prop) (M : A → Measure B) : Prop :=
  ∀ a₁ a₂, Adj a₁ a₂ → ∀ E : Set B, MeasurableSet E →
    M a₁ E ≤ ENNReal.ofReal (Real.exp ε) * M a₂ E + ENNReal.ofReal δ

/-- **The Rényi divergence** (Definition 3.4):
    `D_α(μ‖ν) = (α−1)⁻¹ · log hellingerIntegral α μ ν`, valued in `EReal`. -/
noncomputable def renyiDiv (α : ℝ) (μ ν : Measure Ω) : EReal :=
  ((α - 1)⁻¹ : ℝ) * ENNReal.log (hellingerIntegral α μ ν)

/-- For `α > 1`, `D_α(μ‖ν) ≤ ρ ↔ hellingerIntegral α μ ν ≤ e^{(α−1)ρ}`. -/
lemma renyiDiv_le_coe_iff {α ρ : ℝ} (hα : 1 < α) (μ ν : Measure Ω) :
    renyiDiv α μ ν ≤ (ρ : EReal) ↔
      hellingerIntegral α μ ν ≤ ENNReal.ofReal (Real.exp ((α - 1) * ρ)) := by
  have h1 : (0:ℝ) < α - 1 := by linarith
  have hpos : (0:ℝ) < (α - 1)⁻¹ := inv_pos.mpr h1
  rcases eq_or_ne (hellingerIntegral α μ ν) 0 with h0 | h0
  · rw [renyiDiv, h0, ENNReal.log_zero, EReal.coe_mul_bot_of_pos hpos]
    simp
  rcases eq_or_ne (hellingerIntegral α μ ν) ⊤ with htop | htop
  · rw [renyiDiv, htop, ENNReal.log_top, EReal.coe_mul_top_of_pos hpos]
    simp [top_le_iff]
  · have htR : 0 < (hellingerIntegral α μ ν).toReal := ENNReal.toReal_pos h0 htop
    rw [renyiDiv, ENNReal.log_pos_real h0 htop, ← EReal.coe_mul,
      EReal.coe_le_coe_iff,
      ENNReal.le_ofReal_iff_toReal_le htop (Real.exp_nonneg _),
      ← Real.log_le_iff_le_exp htR, inv_mul_le_iff₀ h1]

/-- **`(α,ρ)`-Rényi differential privacy** (Definition 3.4). -/
def RenyiDP (α ρ : ℝ) (Adj : A → A → Prop) (M : A → Measure B) : Prop :=
  ∀ a₁ a₂, Adj a₁ a₂ → renyiDiv α (M a₁) (M a₂) ≤ (ρ : EReal)

/-- **Individual Rényi differential privacy** (Definition 3.6): one adjacency `Adj i` and
    one budget `ρ i` per individual. -/
def IndivRenyiDP {ι : Type*} (α : ℝ) (ρ : ι → ℝ) (Adj : ι → A → A → Prop)
    (M : A → Measure B) : Prop :=
  ∀ i, RenyiDP α (ρ i) (Adj i) M

/-- **From individual to global RDP** (Lemma 3.7): a uniform bound `c` on the individual
    budgets is a global budget at the union of the adjacencies. -/
theorem IndivRenyiDP.renyiDP_of_le {ι : Type*} {α c : ℝ} {ρ : ι → ℝ}
    {Adj : ι → A → A → Prop} {M : A → Measure B}
    (h : IndivRenyiDP α ρ Adj M) (hb : ∀ i, ρ i ≤ c) :
    RenyiDP α c (fun a₁ a₂ => ∃ i, Adj i a₁ a₂) M := by
  rintro a₁ a₂ ⟨i, hi⟩
  exact (h i a₁ a₂ hi).trans (EReal.coe_le_coe_iff.mpr (hb i))

/-- **From individual to global RDP** (Lemma 3.7), supremum form: `(α, ⨆ i, ρ i)`-RDP at
    the union of the adjacencies. -/
theorem IndivRenyiDP.renyiDP_iSup {ι : Type*} [Nonempty ι] {α : ℝ} {ρ : ι → ℝ}
    {Adj : ι → A → A → Prop} {M : A → Measure B}
    (h : IndivRenyiDP α ρ Adj M) (hb : BddAbove (Set.range ρ)) :
    RenyiDP α (⨆ i, ρ i) (fun a₁ a₂ => ∃ i, Adj i a₁ a₂) M :=
  h.renyiDP_of_le fun i => le_ciSup hb i

/-- Data processing under a measurable map, without absolute continuity
    (Proposition A.20, item 2). -/
theorem hellingerIntegral_map_le_uncond {𝓧 𝓨 : Type*} [MeasurableSpace 𝓧] [MeasurableSpace 𝓨]
    {α : ℝ} (hα : 1 < α) {f : 𝓧 → 𝓨} (hf : Measurable f) (μ ν : Measure 𝓧)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    hellingerIntegral α (μ.map f) (ν.map f) ≤ hellingerIntegral α μ ν := by
  by_cases hac : μ ≪ ν
  · exact hellingerIntegral_map_le hα hf μ ν hac
  · rw [hellingerIntegral_eq_top_of_not_ac μ ν hac]; exact le_top

/-- **RDP ⇒ `(ε,δ)`-DP** (Proposition 3.5): an `(α,ρ)`-RDP mechanism is `(ε,δ)`-DP at
    `ε = ρ + log((α−1)/α) − (log δ + log α)/(α−1)`, for every `δ > 0`. -/
theorem RenyiDP.epsilonDeltaDP {α ρ δ : ℝ} (hα : 1 < α) (hδ0 : 0 < δ)
    {Adj : A → A → Prop} {M : A → Measure B} [∀ a, IsFiniteMeasure (M a)]
    (h : RenyiDP α ρ Adj M) :
    EpsilonDeltaDP (ρ + Real.log ((α - 1) / α) - (Real.log δ + Real.log α) / (α - 1))
      δ Adj M := by
  intro a₁ a₂ hadj E hE
  set ε : ℝ := ρ + Real.log ((α - 1) / α) - (Real.log δ + Real.log α) / (α - 1)
    with hε
  have hH := (renyiDiv_le_coe_iff hα _ _).mp (h a₁ a₂ hadj)
  have hac : M a₁ ≪ M a₂ := by
    by_contra hc
    rw [hellingerIntegral_eq_top_of_not_ac _ _ hc] at hH
    exact ENNReal.ofReal_ne_top (top_le_iff.mp hH)
  have hball := hellingerIntegral_to_dp_balle hα hδ0 (M a₁) (M a₂) hac hH hE
  calc M a₁ E
      = ENNReal.ofReal ((M a₁ E).toReal) :=
        (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    _ ≤ ENNReal.ofReal (Real.exp ε * (M a₂ E).toReal + δ) :=
        ENNReal.ofReal_le_ofReal hball
    _ ≤ ENNReal.ofReal (Real.exp ε * (M a₂ E).toReal) + ENNReal.ofReal δ :=
        ENNReal.ofReal_add_le
    _ = ENNReal.ofReal (Real.exp ε) * M a₂ E + ENNReal.ofReal δ := by
        rw [ENNReal.ofReal_mul (Real.exp_nonneg _),
          ENNReal.ofReal_toReal (measure_ne_top _ _)]

end Continuous
