import Xhl.Divergence.TestVal

/-!
# The witness-free Rényi lifting (lifting level)

Definitions at the level of one pair of measures, independent of the program syntax.
The two-witness reading is the judgment `WRhl` (`Xhl/Logic/Rrhl/Duality.lean`, Appendix C).

* `CodLiftMulC` — the witness-free lifting: for every pair of measurable tests
  `k₁ : A → ℝ≥0∞`, `k₂ : B → ℝ≥0∞` with `k₁ a ^ α * k₂ b ^ (1 − α) ≤ 1` on the
  relation, the Hellinger integral of the two test expectations is at most `η`.
-/

open MeasureTheory ProbabilityTheory ENNReal

namespace Continuous

section Lifting

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

/-- Admissible test pairs: pointwise Hellinger integral at most `1` on `R`. -/
def TestAdmC (α : ℝ) (R : A → B → Prop) (k₁ : A → ℝ≥0∞) (k₂ : B → ℝ≥0∞) : Prop :=
  ∀ a b, R a b → k₁ a ^ α * k₂ b ^ (1 - α) ≤ 1

/-- The witness-free (codensity, one-point-test) Rényi lifting, with measurable tests. -/
def CodLiftMulC (α : ℝ) (R : A → B → Prop) (η : ℝ≥0∞) (μ₁ : Measure A) (μ₂ : Measure B) :
    Prop :=
  ∀ k₁ : A → ℝ≥0∞, ∀ k₂ : B → ℝ≥0∞, Measurable k₁ → Measurable k₂ →
    TestAdmC α R k₁ k₂ → testValC α μ₁ μ₂ k₁ k₂ ≤ η

end Lifting

end Continuous
