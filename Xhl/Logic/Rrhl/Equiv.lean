import Xhl.Logic.Rrhl.Rrhl

open Continuous

/-!
# Program equivalence in the logic with the test interpretation

`rrhl_equiv` — **[Equiv]**: validity depends on the two programs only through their
semantics, so two programs with the same semantics from the states of the precondition are
interchangeable.  This is the rule through which equivalences about hidden variables
(fusing a hidden draw into the next sampling, removing a dead store, splitting a Gaussian)
enter a derivation.
-/

open MeasureTheory ProbabilityTheory ENNReal Cmd

variable {ident : Type} {M : MemType ident}

namespace Continuous

/-- **[Equiv]**. -/
theorem rrhl_equiv {α : ℝ} {P Q : St M × St M → Prop} {φ ψ : St M × St M → ℝ≥0∞}
    {c₁ c₂ c₁' c₂' : Cmd ident M}
    (h₁ : ∀ s, P s → osemA c₁ s.1 = osemA c₁' s.1)
    (h₂ : ∀ s, P s → osemA c₂ s.2 = osemA c₂' s.2)
    (h : RRhl α P φ c₁' c₂' Q ψ) : RRhl α P φ c₁ c₂ Q ψ := by
  intro s hs k₁ k₂ hk₁ hk₂ hk
  rw [h₁ s hs, h₂ s hs]
  exact h s hs k₁ k₂ hk₁ hk₂ hk

end Continuous
