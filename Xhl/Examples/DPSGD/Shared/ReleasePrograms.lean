import Xhl.Examples.DPSGD.Shared.Paper
import Xhl.Logic.Equiv.LocalList

/-!
# The DP-SGD programs of Figure 1

* `blockLoc` — the sampling block of lines 4–7 (`prefixLI` under `local hidden`);
* `dpsgdTranscript` — the transcript model, releasing `w` (here `g̃`) every round;
* `dpsgdLastIter` — the last-iterate model, with projected update and the final model
  released (its loop is `dpsgdLastIterLoc`).

The `example`s after each program unfold every `~` splice and check the result equal to
the definition by `rfl`.
-/

open MeasureTheory ProbabilityTheory Continuous
open scoped NNReal ENNReal

namespace DPSGDPaper

/-! ## The sampling block -/

section Block

variable (N dx d : ℕ)
  (grad : EuclideanSpace ℝ (Fin dx) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
  (C : ℝ≥0)
  (v : ℝ≥0) (q : ℝ≥0)

/-- The body of the block: the Poisson loop, the clipped sum, the Gaussian. -/
noncomputable def prefixLI (hm : MeasOK dx d grad) : Cmd String PMem :=
  Cmd.seq (Cmd.seq (poissonSample N q) (Cmd.assign (gV d) (batchSumPaperE N dx d grad C hm)))
    (Cmd.random (gtV d) (gaussKernelE (M := PMem) (getG d) (measurable_getG d) v))

/-- The hidden variables of a round: the coin, the batch, the index and the clipped sum. -/
def hidden : List (AVar String) :=
  [⟨.bool, bv⟩, ⟨.finset (N + 1), bchV N⟩, ⟨.nat, jv⟩, ⟨.vec d, gV d⟩]

/-- The block of a round: the Poisson loop, the clipped sum and the Gaussian, with the
    hidden variables local. -/
noncomputable def blockLoc (hm : MeasOK dx d grad) : Cmd String PMem :=
  locs (hidden N d) (prefixLI N dx d grad C v q hm)

end Block

/-! ## DP-SGD with the noisy gradient released -/

section Release

variable (N dx d T : ℕ)
  (grad : EuclideanSpace ℝ (Fin dx) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
  (C : ℝ≥0)
  (η : ℝ) (σ q : ℝ≥0)

/-- The round: the block, the update, the release, the counter. -/
noncomputable def bodyRel (hm : MeasOK dx d grad) : Cmd String PMem :=
  ⟪ ~(blockLoc N dx d grad C ((σ * C) ^ 2) q hm) ;
    ( ~(Cmd.assign (thV d) (modelUpdE d (γv N η q))) ;
      ( release (gtV d) ;
        cnt ← cnt + (1 : ℕ) ) ) ⟫

/-- The program. -/
noncomputable def dpsgdTranscript (hm : MeasOK dx d grad) (θ₀ : EuclideanSpace ℝ (Fin d)) :
    Cmd String PMem :=
  ⟪ (thV d) ← θ₀ ;
    cnt ← (0 : ℕ) ;
    while cnt < T do
      ~(bodyRel N dx d grad C η σ q hm)
    od ⟫

/-- `dpsgdTranscript`, fully spelled out. -/
example (hm : MeasOK dx d grad) (θ₀ : EuclideanSpace ℝ (Fin d)) :
    dpsgdTranscript N dx d T grad C η σ q hm θ₀ =
    ⟪ (thV d) ← θ₀ ;
      cnt ← (0 : ℕ) ;
      while cnt < T do
        ( ~(locs (hidden N d) ⟪
              (bchV N) ← (∅ : Finset (Fin (N + 1))) ;
              jv ← (0 : ℕ) ;
              while jv < N + 1 do
                bv ←$ Bern(q) ;
                if bv then
                  ~(Cmd.assign (bchV N) (insertJE N))
                else
                  skip
                fi ;
                jv ← jv + (1 : ℕ)
              od ;
              ~(Cmd.assign (gV d) (batchSumPaperE N dx d grad C hm)) ;
              (gtV d) ←$ 𝒩(getG d, measurable_getG d, ((σ * C) ^ 2 : ℝ≥0)) ⟫) ;
          ( ~(Cmd.assign (thV d) (modelUpdE d (γv N η q))) ;
            ( release (gtV d) ;
              cnt ← cnt + (1 : ℕ) ) ) )
      od ⟫ := rfl

end Release

/-! ## The last iterate, released -/

section LastIterateRelease

variable (N dx d T : ℕ)
  (grad : EuclideanSpace ℝ (Fin dx) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
  (C : ℝ≥0)
  (proj : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
  (η : ℝ) (q : ℝ≥0)

/-- The round: the block, the projected update, the counter. -/
noncomputable def bodyLocLI (hm : MeasOK dx d grad) (hpm : Measurable proj)
    (v : ℝ≥0) : Cmd String PMem :=
  ⟪ ~(blockLoc N dx d grad C v q hm) ;
    ~(Cmd.assign (thV d) (modelUpdProjE d proj hpm (γv N η q))) ;
    cnt ← cnt + (1 : ℕ) ⟫

/-- The program (nothing released). -/
noncomputable def dpsgdLastIterLoc (hm : MeasOK dx d grad) (hpm : Measurable proj)
    (v : ℝ≥0) (θ₀ : EuclideanSpace ℝ (Fin d)) : Cmd String PMem :=
  ⟪ (thV d) ← θ₀ ;
    cnt ← (0 : ℕ) ;
    while cnt < T do
      ~(bodyLocLI N dx d grad C proj η q hm hpm v)
    od ⟫

/-- The last iterate, with the final model released. -/
noncomputable def dpsgdLastIter (hm : MeasOK dx d grad) (hpm : Measurable proj)
    (v : ℝ≥0) (θ₀ : EuclideanSpace ℝ (Fin d)) : Cmd String PMem :=
  ⟪ ~(dpsgdLastIterLoc N dx d T grad C proj η q hm hpm v θ₀) ;
    release (thV d) ⟫

/-- `dpsgdLastIter`, fully spelled out. -/
example (hm : MeasOK dx d grad) (hpm : Measurable proj) (v : ℝ≥0)
    (θ₀ : EuclideanSpace ℝ (Fin d)) :
    dpsgdLastIter N dx d T grad C proj η q hm hpm v θ₀ =
    ⟪ (thV d) ← θ₀ ;
      cnt ← (0 : ℕ) ;
      while cnt < T do
        ( ~(locs (hidden N d) ⟪
              (bchV N) ← (∅ : Finset (Fin (N + 1))) ;
              jv ← (0 : ℕ) ;
              while jv < N + 1 do
                bv ←$ Bern(q) ;
                if bv then
                  ~(Cmd.assign (bchV N) (insertJE N))
                else
                  skip
                fi ;
                jv ← jv + (1 : ℕ)
              od ;
              ~(Cmd.assign (gV d) (batchSumPaperE N dx d grad C hm)) ;
              (gtV d) ←$ 𝒩(getG d, measurable_getG d, v) ⟫) ;
          ~(Cmd.assign (thV d) (modelUpdProjE d proj hpm (γv N η q))) ;
          cnt ← cnt + (1 : ℕ) )
      od ;
      release (thV d) ⟫ := rfl

end LastIterateRelease

end DPSGDPaper
