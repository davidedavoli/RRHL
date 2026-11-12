import Xhl.Duality.Discrete.Distr

open ENNReal Classical

namespace DStd

/-!
# The total weight of a discrete sub-distribution

Part of the discrete development (namespace `DStd`) used by the discrete duality theorem
(`Xhl/Duality/Discrete/RenyiDuality.lean`).
-/

open ENNReal Classical

namespace Distr

variable {α β : Type}

/-- Total mass of a sub-distribution. -/
noncomputable def weight (μ : Distr α) : ℝ≥0∞ := ∑' a, μ.mass a

end Distr

end DStd
