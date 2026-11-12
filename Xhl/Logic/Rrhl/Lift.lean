import Xhl.Language.Semantics

open Continuous

/-!
# Lifting assertions and weights from memories to states

A judgment of the logic talks about states — a memory together with the transcript
released so far — but almost every assertion a case study writes down is about the
memories alone.  These two functions are how such an assertion is read as one on
states: `liftP` adds the demand that the two transcripts agree (which is what the
readout `rrhl_tr_hellingerIntegral_le` needs of a postcondition), and `liftW` leaves a weight
untouched, evaluating it on the memory components.
-/

open scoped ENNReal

variable {ident : Type} {M : MemType ident}

namespace Continuous

/-- An assertion on memories, as an assertion on states: it holds of the memory
    components, and the two transcripts agree. -/
def liftP (P : M.heap × M.heap → Prop) (s : St M × St M) : Prop :=
  P (s.1.1, s.2.1) ∧ s.1.2 = s.2.2

/-- A weight on memories, as a weight on states. -/
def liftW (ψ : M.heap × M.heap → ℝ≥0∞) (s : St M × St M) : ℝ≥0∞ := ψ (s.1.1, s.2.1)

end Continuous
