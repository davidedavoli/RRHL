import Mathlib.Topology.Algebra.InfiniteSum.Order
import Xhl.Duality.Discrete.Distr

open Classical

namespace DStd

open Classical

/-!
# Range Predicate for Sub-probability Distributions

`range P μ` holds when every element in the support of `μ` satisfies `P`
(discrete development, namespace `DStd`).
-/

/-- `range P μ`: every element in the support of `μ` satisfies `P`. -/
def range {α : Type} (P : α → Prop) (μ : Distr α) : Prop :=
  ∀ m, μ.mass m ≠ 0 → P m

namespace Range

variable {α β : Type} {P Q : α → Prop} {μ : Distr α}

end Range

end DStd
