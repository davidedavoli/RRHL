import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.GiryMonad
import Xhl.Measures.Isup

open MeasureTheory Classical Filter

/-!
# Range predicate

`range P μ` holds when `P` holds `μ`-almost everywhere.
-/

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable {P Q : α → Prop} {μ : Measure α}

namespace Continuous

/-- `range P μ`: `P` holds μ-almost everywhere. -/
def range (P : α → Prop) (μ : Measure α) : Prop := ∀ᵐ m ∂μ, P m


/-- The zero measure satisfies any range condition (vacuously). -/
lemma range_null (P : α → Prop) : range P (0 : Measure α) := by
  simp [range]

/-- A Dirac measure at `a` has range `{a}`. -/
lemma range_dirac (P : α → Prop) (a : α) (hP : MeasurableSet {m | P m}) (h : P a) :
    range P (Measure.dirac a) := by
  rw [range, ae_iff]
  have : {m | ¬P m} = {m | P m}ᶜ := Set.compl_ofPred P ▸ rfl
  simp only [this, Measure.dirac_apply' _ hP.compl,
    Set.indicator_apply, Set.mem_compl_iff, Set.mem_ofPred_eq, h, not_true, if_false]

/-- Range is preserved by monadic bind. -/
lemma range_bind {PA : α → Prop} {PB : β → Prop} (μ : Measure α) (κ : α → Measure β)
    (hκ : Measurable κ) (hPB : MeasurableSet {x | PB x})
    (hA : range PA μ) (hB : ∀ a, PA a → range PB (κ a)) :
    range PB (μ.bind κ) := by
  rw [range, ae_iff]
  have heq : {b | ¬PB b} = {x | PB x}ᶜ := by ext; simp
  rw [heq, Measure.bind_apply hPB.compl hκ.aemeasurable]
  have hmeas : Measurable (fun a => κ a {x | PB x}ᶜ) :=
    (Measure.measurable_coe hPB.compl).comp hκ
  rw [lintegral_eq_zero_iff hmeas]
  filter_upwards [hA] with a ha
  have : (κ a) {b | ¬PB b} = 0 := by rw [← ae_iff]; exact hB a ha
  rwa [← heq]

/-- Range is preserved by monotone suprema. -/
lemma range_iSup (P : α → Prop) (hP : MeasurableSet {m | P m})
    (μ : ℕ → Measure α) (hmono : Monotone μ)
    (h : ∀ n, range P (μ n)) :
    range P (⨆ n, μ n) := by
  rw [range, ae_iff]
  have hmeas : MeasurableSet {m | ¬P m} := hP.compl
  rw [iSup_measure_apply hmono hmeas]
  apply le_antisymm _ (zero_le)
  apply iSup_le
  intro n
  exact (ae_iff.mp (h n)).le

end Continuous
