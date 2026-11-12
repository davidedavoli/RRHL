import Xhl.Language.Syntax

/-!
# Laws of memories derived from extensionality

From extensionality (`MemType.ext`) and the read-back laws:

* `MemType.set_set_absorb` — a write is overwritten by a later write to the same variable.
* `MemType.set_set_comm` — writes to different variables commute.
* `Continuous.get_set_other` — reading a variable is unaffected by writing another one.
-/

namespace Continuous

variable {ident : Type} (M : MemType ident)

namespace MemType

lemma set_set_absorb (t : Ty) (m : M.heap) (x : ident) (v w : t.interp) :
    M.set (M.set m t x v) t x w = M.set m t x w := by
  refine M.ext _ _ fun a z => ?_
  by_cases h : a = t ∧ z = x
  · obtain ⟨rfl, rfl⟩ := h
    rw [M.get_set_eq, M.get_set_eq]
  · have hne : t ≠ a ∨ x ≠ z := by
      rcases not_and_or.1 h with h | h
      · exact Or.inl (Ne.symm h)
      · exact Or.inr (Ne.symm h)
    rw [M.get_set_ne _ _ _ _ _ _ hne, M.get_set_ne _ _ _ _ _ _ hne,
      M.get_set_ne _ _ _ _ _ _ hne]

lemma set_set_comm (t u : Ty) (m : M.heap) (x y : ident)
    (hne : t ≠ u ∨ x ≠ y) (v : t.interp) (w : u.interp) :
    M.set (M.set m t x v) u y w = M.set (M.set m u y w) t x v := by
  refine M.ext _ _ fun a z => ?_
  by_cases h1 : a = u ∧ z = y
  · obtain ⟨rfl, rfl⟩ := h1
    rw [M.get_set_eq, M.get_set_ne t a _ x z v hne, M.get_set_eq]
  · have hne1 : u ≠ a ∨ y ≠ z := by
      rcases not_and_or.1 h1 with h | h
      · exact Or.inl (Ne.symm h)
      · exact Or.inr (Ne.symm h)
    rw [M.get_set_ne _ _ _ _ _ _ hne1]
    by_cases h2 : a = t ∧ z = x
    · obtain ⟨rfl, rfl⟩ := h2
      rw [M.get_set_eq, M.get_set_eq]
    · have hne2 : t ≠ a ∨ x ≠ z := by
        rcases not_and_or.1 h2 with h | h
        · exact Or.inl (Ne.symm h)
        · exact Or.inr (Ne.symm h)
      rw [M.get_set_ne _ _ _ _ _ _ hne2, M.get_set_ne _ _ _ _ _ _ hne2,
        M.get_set_ne _ _ _ _ _ _ hne1]

end MemType

end Continuous

namespace Continuous

variable {ident : Type} {M : MemType ident}

/-- Reading a variable after writing another one. -/
lemma get_set_other {t u : Ty} (h : M.heap) {a y : ident} (w : t.interp) (hne : a ≠ y) :
    M.get (M.set h t a w) u y = M.get h u y :=
  M.get_set_ne t u h a y w (Or.inr hne)

end Continuous
