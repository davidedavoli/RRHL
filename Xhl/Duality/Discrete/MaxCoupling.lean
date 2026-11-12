import Xhl.Duality.Discrete.Total
import Xhl.Duality.Discrete.Coupling

open ENNReal Classical

namespace DStd

/-!
# Masses are bounded by the weight

`mass_le_weight`, `mass_ne_top`: the mass of a point is at most the total weight,
hence finite (discrete development, namespace `DStd`).
-/

open ENNReal Classical

namespace Distr

variable {α β V : Type}

lemma mass_le_weight (μ : Distr β) (b : β) : μ.mass b ≤ μ.weight :=
  ENNReal.le_tsum b

lemma mass_ne_top (μ : Distr β) (b : β) : μ.mass b ≠ ⊤ :=
  ((mass_le_weight μ b).trans μ.le_one).trans_lt one_lt_top |>.ne

end Distr

end DStd
