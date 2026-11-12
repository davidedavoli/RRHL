import Xhl.Divergence.HellingerIntegral

/-!
# The test value

`testValC α μ₁ μ₂ k₁ k₂ = (∫ k₁ dμ₁) ^ α * (∫ k₂ dμ₂) ^ (1 − α)` for tests
`k₁ : A → ℝ≥0∞`, `k₂ : B → ℝ≥0∞`. The judgment `RRhl` (Definition 4.1) bounds it for every
pair of tests admissible for the postcondition.
-/

open MeasureTheory ProbabilityTheory ENNReal

namespace Continuous

section Lifting

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

/-- The Hellinger integral of the two test expectations. -/
noncomputable def testValC (α : ℝ) (μ₁ : Measure A) (μ₂ : Measure B)
    (k₁ : A → ℝ≥0∞) (k₂ : B → ℝ≥0∞) : ℝ≥0∞ :=
  (∫⁻ a, k₁ a ∂μ₁) ^ α * (∫⁻ b, k₂ b ∂μ₂) ^ (1 - α)

end Lifting

end Continuous
