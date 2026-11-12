import Xhl.Logic.Rrhl.Readout

open Continuous

/-!
# Deferred sampling

`bind_comm_of_sFinite`: the two orders of integration agree (Tonelli).  This is the
measure-level fact behind [E-Defer] (`osemA_defer`).
-/

open MeasureTheory ProbabilityTheory ENNReal

namespace Continuous

variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

/-- **The two orders of integration agree** for s-finite measures and a measurable family. -/
theorem bind_comm_of_sFinite (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν]
    (f : α × β → Measure γ) (hf : Measurable f) :
    μ.bind (fun a => ν.bind (fun b => f (a, b))) = ν.bind (fun b => μ.bind (fun a => f (a, b))) := by
  have hfa : ∀ a, Measurable (fun b => f (a, b)) := fun a => hf.comp measurable_prodMk_left
  have hfb : ∀ b, Measurable (fun a => f (a, b)) := fun b => hf.comp measurable_prodMk_right
  have hA : Measurable (fun a => ν.bind (fun b => f (a, b))) := by
    refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
    simp_rw [Measure.bind_apply hs (hfa _).aemeasurable]
    exact (Measure.measurable_coe hs |>.comp hf).lintegral_prod_right'
  have hB : Measurable (fun b => μ.bind (fun a => f (a, b))) := by
    refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
    simp_rw [Measure.bind_apply hs (hfb _).aemeasurable]
    exact (Measure.measurable_coe hs |>.comp hf).lintegral_prod_left'
  ext s hs
  rw [Measure.bind_apply hs hA.aemeasurable, Measure.bind_apply hs hB.aemeasurable]
  simp_rw [Measure.bind_apply hs (hfa _).aemeasurable, Measure.bind_apply hs (hfb _).aemeasurable]
  exact lintegral_lintegral_swap ((Measure.measurable_coe hs).comp hf).aemeasurable

end Continuous

variable {ident : Type} {M : MemType ident}

namespace Continuous

end Continuous
