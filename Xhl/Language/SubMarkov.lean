import Xhl.Language.Semantics

open Continuous

open MeasureTheory ProbabilityTheory ENNReal

/-!
# Sub-Markov denotation of commands

Every command denotes a sub-probability measure: `osemA c s Set.univ ≤ 1`
(`osemA_univ_le_one`). Mass is lost only to `abort`, to a deficient sampling kernel, or to
non-termination of `while`.
-/

namespace Continuous

variable {ident : Type} {M : MemType ident}


/-- The denotation of a command is a sub-probability measure. -/
lemma osemA_univ_le_one : ∀ (c : Cmd ident M) (s : St M), osemA c s Set.univ ≤ 1
  | .abort, s => by simp [osemA_abort]
  | .skip, s => by simp [osemA_skip]
  | .release _, s => by simp [osemA_release]
  | .assign x e, s => by simp [osemA_assign]
  | @Cmd.random _ _ t x κ _, s => by
      have hdm : Measurable (fun v : t.interp =>
          (Measure.dirac (M.set s.1 t x.name v, s.2) : Measure (St M))) :=
        Measure.measurable_dirac.comp
          (((M.set_measurable x.name).comp measurable_prodMk_left).prodMk measurable_const)
      rw [osemA_random, Measure.bind_apply MeasurableSet.univ hdm.aemeasurable]
      simp only [measure_univ]
      rw [lintegral_one]
      exact IsSubMarkovKernel.measure_univ_le_one s.1
  | .cond e c1 c2, s => by
      rw [osemA_cond]
      by_cases hg : esem e s.1
      · simp only [hg, if_true]; exact osemA_univ_le_one c1 s
      · simp only [hg, Bool.false_eq_true, if_false]; exact osemA_univ_le_one c2 s
  | .seq c1 c2, s => by
      rw [osemA_seq, Measure.bind_apply MeasurableSet.univ (osemA_measurable c2).aemeasurable]
      calc ∫⁻ a, osemA c2 a Set.univ ∂(osemA c1 s)
          ≤ ∫⁻ _, 1 ∂(osemA c1 s) := lintegral_mono (fun a => osemA_univ_le_one c2 a)
        _ = osemA c1 s Set.univ := lintegral_one
        _ ≤ 1 := osemA_univ_le_one c1 s
  | .while e c', s => by
      have he : Measurable (esem e) := e.measurable
      have hcm := osemA_measurable c'
      have hubn : ∀ n (s : St M), oubn (osemA c') (esem e) n s Set.univ ≤ 1 := by
        intro n
        induction n with
        | zero => intro s; simp [oubn]
        | succ n ih =>
            intro s
            rw [oubn]
            by_cases hg : esem e s.1
            · simp only [hg, if_true]
              rw [Measure.bind_apply MeasurableSet.univ (oubn_measurable hcm he n).aemeasurable]
              calc ∫⁻ a, oubn (osemA c') (esem e) n a Set.univ ∂(osemA c' s)
                  ≤ ∫⁻ _, 1 ∂(osemA c' s) := lintegral_mono (fun a => ih a)
                _ = osemA c' s Set.univ := lintegral_one
                _ ≤ 1 := osemA_univ_le_one c' s
            · simp only [hg, Bool.false_eq_true, if_false, measure_univ, le_refl]
      rw [osemA_while,
          iSup_measure_apply (oubn_monotone hcm he s) MeasurableSet.univ]
      exact iSup_le (fun n => hubn n s)
  | @Cmd.loc _ _ u x c, s => by
      rw [show osemA (.loc x c) s = (osemA c (M.set s.1 u x.name default, s.2)).map
          (fun s' => (M.set s'.1 u x.name default, s'.2)) from rfl,
        Measure.map_apply (measurable_resetS x) MeasurableSet.univ, Set.preimage_univ]
      exact osemA_univ_le_one c (M.set s.1 u x.name default, s.2)

end Continuous
