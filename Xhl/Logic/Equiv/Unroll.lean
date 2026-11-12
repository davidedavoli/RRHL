import Xhl.Logic.Rrhl.Equiv
import Xhl.Logic.Equiv.Frame
import Xhl.Language.Iter

open Continuous

/-!
# Unrolling loops

* `osemA_while_unroll` — `while e do c od ≡ if e then (c ; while e do c od) else skip`, from
  every state;
* `osemA_while_exit` — `while e do c od ≡ skip`, from a state where `e` is false;
* `osemA_while_eq_iterCmd` — a loop with a fuel certificate is its unrolling (behind
  [E-Count]).

Used through `CEquiv` ([E-Unroll], [E-Count]).
-/

open MeasureTheory ProbabilityTheory ENNReal Cmd

variable {ident : Type} {M : MemType ident}

namespace Continuous

/-- A loop whose guard is false is `skip`. -/
theorem osemA_while_exit (e : BExpr M) (c : Cmd ident M) (s : St M)
    (hs : esem e s.1 = false) : osemA (Cmd.while e c) s = osemA Cmd.skip s := by
  show (⨆ n, oubn (osemA c) (esem e) n s) = Measure.dirac s
  refine le_antisymm (iSup_le fun n => ?_) (le_iSup_of_le 1 ?_)
  · cases n with
    | zero => exact bot_le
    | succ n =>
        show (if esem e s.1 = true then _ else Measure.dirac s) ≤ _
        simp [hs]
  · show (if esem e s.1 = true then _ else Measure.dirac s) ≥ _
    simp [hs]

/-- **[E-Unroll]**: one unfolding of a loop. -/
theorem osemA_while_unroll {e : BExpr M} {c : Cmd ident M} (s : St M) :
    osemA (Cmd.while e c) s = osemA (Cmd.cond e (Cmd.seq c (Cmd.while e c)) Cmd.skip) s := by
  have he : Measurable (esem e) := e.measurable
  have hf : Measurable (osemA c) := osemA_measurable _
  show (⨆ n, oubn (osemA c) (esem e) n s)
    = if esem e s.1 then (osemA c s).bind (fun t => ⨆ n, oubn (osemA c) (esem e) n t)
      else Measure.dirac s
  by_cases hg : esem e s.1 = true
  · simp only [hg, if_true]
    -- the supremum over `n + 1`, by monotonicity
    have hshift : (⨆ n, oubn (osemA c) (esem e) n s) = ⨆ n, oubn (osemA c) (esem e) (n + 1) s :=
      le_antisymm (iSup_le fun n => le_iSup_of_le n (oubn_mono hf he s n))
        (iSup_le fun n => le_iSup (fun k => oubn (osemA c) (esem e) k s) (n + 1))
    rw [hshift]
    have hstep : ∀ n, oubn (osemA c) (esem e) (n + 1) s
        = (osemA c s).bind (oubn (osemA c) (esem e) n) := fun n => by
      show (if esem e s.1 = true then _ else _) = _
      simp [hg]
    simp only [hstep]
    -- the bind commutes with a monotone supremum
    ext A hA
    have hmon : Monotone fun n => (osemA c s).bind (oubn (osemA c) (esem e) n) := by
      intro m n hmn
      rw [Measure.le_iff]
      intro B hB
      rw [Measure.bind_apply hB (oubn_measurable hf he m).aemeasurable,
        Measure.bind_apply hB (oubn_measurable hf he n).aemeasurable]
      exact lintegral_mono fun t => Measure.le_iff'.mp (oubn_monotone hf he t hmn) B
    have hsupm : Measurable fun t => ⨆ n, oubn (osemA c) (esem e) n t := by
      refine Measure.measurable_of_measurable_coe _ fun B hB => ?_
      have : (fun t => (⨆ n, oubn (osemA c) (esem e) n t) B)
          = fun t => ⨆ n, oubn (osemA c) (esem e) n t B := by
        funext t; exact iSup_measure_apply (oubn_monotone hf he t) hB
      rw [this]
      exact Measurable.iSup fun n => (Measure.measurable_coe hB).comp (oubn_measurable hf he n)
    rw [iSup_measure_apply hmon hA, Measure.bind_apply hA hsupm.aemeasurable]
    have : (fun t => (⨆ n, oubn (osemA c) (esem e) n t) A)
        = fun t => ⨆ n, oubn (osemA c) (esem e) n t A := by
      funext t; exact iSup_measure_apply (oubn_monotone hf he t) hA
    rw [this]
    have hmeas : ∀ n, Measurable fun t => oubn (osemA c) (esem e) n t A := fun n =>
      (Measure.measurable_coe hA).comp (oubn_measurable hf he n)
    rw [lintegral_iSup hmeas (fun m n hmn t => Measure.le_iff'.mp (oubn_monotone hf he t hmn) A)]
    congr 1
    funext n
    exact Measure.bind_apply hA (oubn_measurable hf he n).aemeasurable
  · have hs : esem e s.1 = false := by simpa using hg
    simp only [hs, Bool.false_eq_true, if_false]
    exact osemA_while_exit e c s hs

private lemma bind_mono_ae_st {μ : Measure (St M)} {f g : St M → Measure (St M)}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) (h : ∀ᵐ a ∂μ, f a ≤ g a) :
    μ.bind f ≤ μ.bind g := by
  rw [Measure.le_iff]
  intro A hA
  rw [Measure.bind_apply hA hf, Measure.bind_apply hA hg]
  exact lintegral_mono_ae (by filter_upwards [h] with a ha using Measure.le_iff.mp ha A hA)

/-- **A loop that almost surely exits after `N` iterations is its `N`-fold unrolling.**
    `L k` certifies that `k` iterations remain. -/
lemma osemA_while_eq_iterCmd (e : BExpr M) {c : Cmd ident M} (L : ℕ → M.heap → Prop)
    (hfalse : ∀ a, L 0 a → esem e a = false)
    (htrue : ∀ k a, L (k + 1) a → esem e a = true)
    (hstep : ∀ k (s : St M), L (k + 1) s.1 → range (fun s' : St M => L k s'.1) (osemA c s))
    (N : ℕ) (s : St M) (hs : L N s.1) :
    osemA (Cmd.while e c) s = osemA (iterCmd c N) s := by
  have he : Measurable (esem e) := e.measurable
  have hcm := osemA_measurable c
  -- the step condition on the observational semantics
  have hstepO : ∀ k (s : St M), L (k + 1) s.1 → ∀ᵐ s' ∂(osemA c s), L k s'.1 := by
    intro k s hs
    have h := hstep k s hs
    rwa [range] at h
  -- stabilization of the approximants
  have hle : ∀ k (s : St M), L k s.1 → ∀ n,
      oubn (osemA c) (esem e) n s ≤ oubn (osemA c) (esem e) (k + 1) s := by
    intro k
    induction k with
    | zero =>
      intro s hs n
      cases n with
      | zero => exact bot_le
      | succ j => exact le_of_eq (by simp only [oubn, hfalse s.1 hs, Bool.false_eq_true, ↓reduceIte])
    | succ k ih =>
      intro s hs n
      cases n with
      | zero => exact bot_le
      | succ j =>
        have hb := htrue k s.1 hs
        have hL : oubn (osemA c) (esem e) (j + 1) s
            = (osemA c s).bind (oubn (osemA c) (esem e) j) := by simp only [oubn, hb, ↓reduceIte]
        have hR : oubn (osemA c) (esem e) (k + 1 + 1) s
            = (osemA c s).bind (oubn (osemA c) (esem e) (k + 1)) := by
          simp only [oubn, hb, ↓reduceIte]
        rw [hL, hR]
        refine bind_mono_ae_st (oubn_measurable hcm he j).aemeasurable
          (oubn_measurable hcm he (k + 1)).aemeasurable ?_
        filter_upwards [hstepO k s hs] with s' hs' using ih s' hs' j
  have hsup : ∀ k (s : St M), L k s.1 →
      osemA (Cmd.while e c) s = oubn (osemA c) (esem e) (k + 1) s := by
    intro k s hs
    show (⨆ n, oubn (osemA c) (esem e) n s) = _
    exact le_antisymm (iSup_le (hle k s hs)) (le_iSup (fun n => oubn (osemA c) (esem e) n s) (k + 1))
  have key : ∀ N (s : St M), L N s.1 →
      oubn (osemA c) (esem e) (N + 1) s = osemA (iterCmd c N) s := by
    intro N
    induction N with
    | zero =>
      intro s hs
      simp only [oubn, hfalse s.1 hs, Bool.false_eq_true, ↓reduceIte, iterCmd]
      rfl
    | succ n ih =>
      intro s hs
      have hL : oubn (osemA c) (esem e) (n + 1 + 1) s
          = (osemA c s).bind (oubn (osemA c) (esem e) (n + 1)) := by
        simp only [oubn, htrue n s.1 hs, ↓reduceIte]
      rw [hL]
      show _ = (osemA c s).bind (osemA (iterCmd c n))
      exact Measure.bind_congr_right ((hstepO n s hs).mono (fun a ha => ih a ha))
  rw [hsup N s hs, key N s hs]

end Continuous
