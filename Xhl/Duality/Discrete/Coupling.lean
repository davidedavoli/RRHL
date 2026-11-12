import Xhl.Duality.Discrete.Distr

open ENNReal Classical

namespace DStd

/-!
# Sub-probability couplings

A sub-probability coupling of `μ₁ : Distr A` and `μ₂ : Distr B` is a joint distribution
`ν : Distr (A × B)` whose first marginal equals `μ₁` and whose second marginal equals `μ₂`
(discrete development, namespace `DStd`).
-/

open ENNReal Classical

namespace Distr

variable {A B C D : Type}

lemma fst_mass {α β : Type} (d : Distr (α × β)) (a : α) :
    d.fst.mass a = ∑' b : β, d.mass (a, b) := by
  change ∑' p : α × β, (if p.1 = a then d.mass p else 0) = ∑' b : β, d.mass (a, b)
  rw [ENNReal.tsum_prod', ENNReal.tsum_comm]
  congr 1; ext b
  rw [tsum_eq_single a (fun a' ha' => if_neg ha')]
  simp

lemma snd_mass {α β : Type} (d : Distr (α × β)) (b : β) :
    d.snd.mass b = ∑' a : α, d.mass (a, b) := by
  change ∑' p : α × β, (if p.2 = b then d.mass p else 0) = ∑' a : α, d.mass (a, b)
  rw [ENNReal.tsum_prod']
  congr 1; ext a
  rw [tsum_eq_single b (fun b' hb' => if_neg hb')]
  simp

end Distr

end DStd
