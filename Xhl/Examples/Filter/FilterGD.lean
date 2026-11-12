import Xhl.Divergence.Weighted
import Xhl.Examples.Support.GaussVec
import Xhl.Examples.Support.Clip
import Xhl.Examples.Support.Adjacency
import Xhl.Language.MemLaws

open Continuous

/-!
# Noisy gradient descent with per-record Rényi filters: parameters and invariants

The ingredients of the program of Figure 5 (§5.2), Feldman–Zrnic's Algorithm 3: parameters
`TapParams` (clipping norm `Γ`, noise variance `v`, per-record budget `B`, step sizes), the
filter radius `tradius = min{Γ, √max(0, B − s[i])}`, the record step, and the invariants
`PreT`/`JT` with the state-dependent weights `wMidT`/`wEndT` of the derivation.

The filter lives inside the clipping radius: the meter `s[i]` holds the squared norms already
spent by record `i`, and the radius drops the record (radius `0`) once its budget is spent.
A missing record has `ḡ(X_i) = clip_r(∇ℓ(θ, ⊥)) = 0` (`tcg_bot`) and meters nothing.  The
program mentions no Rényi order; `α` enters only through `cT p α = α / 2v`.  `v` is the
variance of the single Gaussian added to the sum (§5.2).
-/

open MeasureTheory ProbabilityTheory ENNReal Real
open scoped NNReal

variable {ident : Type} {M : MemType ident}

namespace RenyiFilter

open Continuous

variable {d e n : ℕ} {τ : Ty}

/-! ## Vector and weight components -/

/-- Component `i` of a vector of length `n` (`0` out of range). -/
noncomputable def remAt (r : EuclideanSpace ℝ (Fin n)) (i : ℕ) : ℝ :=
  if h : i < n then r ⟨i, h⟩ else 0

/-- Fresh meters have spent nothing. -/
@[simp] lemma remAt_zero (i : ℕ) : remAt (n := n) 0 i = 0 := by
  unfold remAt; split_ifs <;> simp

/-- The unit vector at `i` (`0` out of range). -/
noncomputable def eAt (n i : ℕ) : EuclideanSpace ℝ (Fin n) :=
  if h : i < n then EuclideanSpace.single ⟨i, h⟩ 1 else 0

lemma measurable_remAt (i : ℕ) : Measurable (fun r : EuclideanSpace ℝ (Fin n) => remAt r i) := by
  unfold remAt
  split_ifs with h
  · exact (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) ⟨i, h⟩).measurable
  · exact measurable_const

/-- `exp((α − 1)·f)`, the weight of the filter derivation.  It is unclamped: the invariants
    keep `f` in range, and the bounds the derivation needs are obtained by **[Conseq]**. -/
noncomputable def expW (α : ℝ) (f : M.heap × M.heap → ℝ) (m : M.heap × M.heap) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp ((α - 1) * f m))

lemma goodWeight_expW {α : ℝ} {f : M.heap × M.heap → ℝ} (hf : Measurable f) :
    GoodWeight (expW (M := M) α f) :=
  ⟨ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul hf)),
    fun _ => (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne',
    fun _ => ofReal_ne_top⟩

/-- `1 ≤ exp((α − 1)·f)` when `0 ≤ f`. -/
lemma one_le_expW {α : ℝ} (hα : 1 < α) {f : M.heap × M.heap → ℝ} {m : M.heap × M.heap}
    (h0 : 0 ≤ f m) : 1 ≤ expW (M := M) α f m := by
  unfold expW
  rw [← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (Real.one_le_exp (mul_nonneg (by linarith) h0))

/-- `exp((α − 1)·f) ≤ exp((α − 1)·B)` when `f ≤ B`. -/
lemma expW_le_of_le {α B : ℝ} (hα : 1 < α) {f : M.heap × M.heap → ℝ} {m : M.heap × M.heap}
    (h : f m ≤ B) : expW (M := M) α f m ≤ ENNReal.ofReal (Real.exp ((α - 1) * B)) :=
  ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_left h (by linarith)))

/-- **The charge keeps the weight**: if the Gaussian step costs at most the charge `ρ`,
    the weight after the charge, times the Gaussian Hellinger bound, is at most the weight
    before. -/
lemma expW_charge_le {α : ℝ} (hα : 1 < α) {bv ρ D σ2 : ℝ}
    (hρ : α * D ^ 2 / (2 * σ2) ≤ ρ) :
    ENNReal.ofReal (Real.exp ((α - 1) * (bv - ρ)))
        * ENNReal.ofReal (Real.exp (α * (α - 1) * D ^ 2 / (2 * σ2)))
      ≤ ENNReal.ofReal (Real.exp ((α - 1) * bv)) := by
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
  have hα1 : 0 ≤ α - 1 := by linarith
  have hre : α * (α - 1) * D ^ 2 / (2 * σ2) = (α - 1) * (α * D ^ 2 / (2 * σ2)) := by ring
  rw [hre]
  nlinarith [mul_le_mul_of_nonneg_left hρ hα1]

/-- Parameters of filtered noisy gradient descent (Figure 5).  The budget is in squared-norm
    units; there is no Rényi order. -/
structure TapParams (d e n : ℕ) (τ : Ty) where
  /-- clipping norm `Γ` -/
  Cl : ℝ
  /-- the variance `v` of the Gaussian added to the sum -/
  nvar : ℝ≥0
  /-- the per-record squared-norm budget `B` -/
  Bnorm : ℝ
  /-- the learning rate `η_t` of round `t` -/
  η : ℕ → ℝ
  /-- per-example gradient, on records extended with `⊥`: `∇ℓ : ℝ^d → ℝ^e_⊥ → ℝ^d` -/
  grad : EuclideanSpace ℝ (Fin d) → Option (EuclideanSpace ℝ (Fin e)) →
    EuclideanSpace ℝ (Fin d)
  /-- `∇ℓ(θ, ⊥) = 0`: a missing record contributes nothing and meters nothing -/
  grad_bot : ∀ xx, grad xx none = 0
  /-- the `i`-th record of the dataset, `⊥` (`none`) if that slot is missing -/
  record : τ.interp → ℕ → Option (EuclideanSpace ℝ (Fin e))

/-- Program variables.  `s` holds the meters `Σ_{j<t} ‖ḡ_j(X_i)‖²`. -/
structure TapVars (ident : Type) (d n : ℕ) (τ : Ty) where
  x : Vars ident (.vec d)
  acc : Vars ident (.vec d)
  z : Vars ident (.vec d)
  s : Vars ident (.vec n)
  i : Vars ident .nat
  D : Vars ident τ
  distinct : [x.name, acc.name, z.name, s.name, i.name, D.name].Nodup

/-! ## The filter radius -/

section Clip

variable (p : TapParams d e n τ)

/-- The filter radius of record `i`: `r_i(s) = min{Γ, √max(0, B − s[i])}`. -/
noncomputable def tradius (s : EuclideanSpace ℝ (Fin n)) (i : ℕ) : ℝ :=
  min p.Cl (Real.sqrt (max 0 (p.Bnorm - remAt s i)))

/-- The gradient of record `i` clipped at its filter radius. -/
noncomputable def tcg (s : EuclideanSpace ℝ (Fin n)) (i : ℕ) (θ : EuclideanSpace ℝ (Fin d))
    (D : τ.interp) : EuclideanSpace ℝ (Fin d) :=
  clipV (tradius p s i) (p.grad θ (p.record D i))

end Clip

section ClipFacts

variable {p : TapParams d e n τ}

lemma tradius_nonneg (hC : 0 ≤ p.Cl) (ss : EuclideanSpace ℝ (Fin n)) (i : ℕ) :
    0 ≤ tradius p ss i :=
  le_min hC (Real.sqrt_nonneg _)

/-- **A missing record contributes nothing**: `∇ℓ(θ, ⊥) = 0` and `clip_r(0) = 0`. -/
lemma tcg_bot {ss : EuclideanSpace ℝ (Fin n)} {i : ℕ} (xx : EuclideanSpace ℝ (Fin d))
    {DD : τ.interp} (h : p.record DD i = none) : tcg p ss i xx DD = 0 := by
  unfold tcg; rw [h, p.grad_bot, clipV_zero]

/-- `∇ℓ` at a slot, split on the slot's presence: the form `TapOK` is stated in. -/
lemma grad_record_eq_ite (i : ℕ) (xx : EuclideanSpace ℝ (Fin d)) (DD : τ.interp) :
    p.grad xx (p.record DD i)
      = if (p.record DD i).isSome then p.grad xx (some ((p.record DD i).getD 0)) else 0 :=
  apply_option_split (g := p.grad xx) (p.grad_bot xx) _

/-- The clipped gradient has norm at most the radius. -/
lemma norm_tcg_le (hC : 0 ≤ p.Cl) (ss : EuclideanSpace ℝ (Fin n)) (i : ℕ)
    (xx : EuclideanSpace ℝ (Fin d)) (DD : τ.interp) :
    ‖tcg p ss i xx DD‖ ≤ tradius p ss i :=
  norm_clipV_le (tradius_nonneg hC ss i) _

/-- **The filter bound**: what a record spends in a round never exceeds what is left. -/
lemma norm_tcg_sq_le (hC : 0 ≤ p.Cl) (ss : EuclideanSpace ℝ (Fin n)) (i : ℕ)
    (xx : EuclideanSpace ℝ (Fin d)) (DD : τ.interp) :
    ‖tcg p ss i xx DD‖ ^ 2 ≤ max 0 (p.Bnorm - remAt ss i) := by
  have h1 : ‖tcg p ss i xx DD‖ ≤ Real.sqrt (max 0 (p.Bnorm - remAt ss i)) :=
    le_trans (norm_tcg_le hC ss i xx DD) (min_le_right _ _)
  have h2 := Real.sq_sqrt (le_max_left 0 (p.Bnorm - remAt ss i))
  nlinarith [norm_nonneg (tcg p ss i xx DD), Real.sqrt_nonneg (max 0 (p.Bnorm - remAt ss i))]

/-- The spend of a record with its budget still unexhausted fits in the budget. -/
lemma norm_tcg_sq_le_rem (hC : 0 ≤ p.Cl) {ss : EuclideanSpace ℝ (Fin n)} {i : ℕ}
    (hs : remAt ss i ≤ p.Bnorm) (xx : EuclideanSpace ℝ (Fin d)) (DD : τ.interp) :
    remAt ss i + ‖tcg p ss i xx DD‖ ^ 2 ≤ p.Bnorm := by
  have h := norm_tcg_sq_le hC ss i xx DD
  rw [max_eq_right (by linarith)] at h
  linarith

end ClipFacts

/-! ## The record step -/

section Step

variable (p : TapParams d e n τ)

/-- `acc + ḡ(X_i)`. -/
noncomputable def accStepTap (acc : EuclideanSpace ℝ (Fin d)) (s : EuclideanSpace ℝ (Fin n))
    (i : ℕ) (θ : EuclideanSpace ℝ (Fin d)) (D : τ.interp) : EuclideanSpace ℝ (Fin d) :=
  acc + tcg p s i θ D

/-- `s + ‖ḡ(X_i)‖² · e_i`: the meter of record `i` records what it spent. -/
noncomputable def sStepTap (s : EuclideanSpace ℝ (Fin n)) (i : ℕ)
    (θ : EuclideanSpace ℝ (Fin d)) (D : τ.interp) : EuclideanSpace ℝ (Fin n) :=
  s + ‖tcg p s i θ D‖ ^ 2 • eAt n i

/-- `x − (η t / n) · (acc + z)`: the gradient step on the averaged noisy sum. -/
noncomputable def updStepTap (η : ℕ → ℝ) (nn : ℕ) (t : ℕ) (θ acc z : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) :=
  θ - (η t / (nn : ℝ)) • (acc + z)

end Step

/-! ## Reading a component off `s + c • e_i` -/

section Components

lemma add_eAt_apply (r : EuclideanSpace ℝ (Fin n)) (c : ℝ) (t : ℕ) (k : Fin n) :
    (r + c • eAt n t) k = r k + if (k : ℕ) = t then c else 0 := by
  unfold eAt
  split_ifs with h1 h2 h2
  · simp [Fin.ext_iff, h2]
  · simp [Fin.ext_iff, h2]
  · exact absurd (h2 ▸ k.isLt) h1
  · simp

lemma remAt_add_eAt (r : EuclideanSpace ℝ (Fin n)) (c : ℝ) (t k : ℕ) :
    remAt (r + c • eAt n t) k = remAt r k + if k = t ∧ k < n then c else 0 := by
  unfold remAt
  split_ifs with h1 h2 h2
  · rw [add_eAt_apply]; simp [h2.1]
  · rw [add_eAt_apply]
    have : ¬ ((⟨k, h1⟩ : Fin n) : ℕ) = t := fun h => h2 ⟨h, h1⟩
    simp [this]
  · exact absurd h2.2 h1
  · simp

end Components

/-! ## Side conditions -/

/-- Measurability side conditions. -/
structure TapOK (p : TapParams d e n τ) (v : TapVars ident d n τ) : Prop where
  grad : Measurable (fun q : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin e) =>
    p.grad q.1 (some q.2))
  present : ∀ k, MeasurableSet {D : τ.interp | (p.record D k).isSome}
  recVal : ∀ k, Measurable (fun D : τ.interp => (p.record D k).getD 0)

lemma TapVars.ne (v : TapVars ident d n τ) :
    v.x.name ≠ v.acc.name ∧ v.x.name ≠ v.z.name ∧ v.x.name ≠ v.s.name ∧ v.x.name ≠ v.i.name ∧
    v.x.name ≠ v.D.name ∧ v.acc.name ≠ v.z.name ∧ v.acc.name ≠ v.s.name ∧
    v.acc.name ≠ v.i.name ∧ v.acc.name ≠ v.D.name ∧ v.z.name ≠ v.s.name ∧
    v.z.name ≠ v.i.name ∧ v.z.name ≠ v.D.name ∧ v.s.name ≠ v.i.name ∧ v.s.name ≠ v.D.name ∧
    v.i.name ≠ v.D.name := by
  have h := v.distinct
  simp only [List.nodup_cons, List.mem_cons, not_or, List.nodup_nil, and_true,
    List.not_mem_nil, not_false_eq_true] at h
  obtain ⟨⟨h1, h2, h3, h4, h5⟩, ⟨h6, h7, h8, h9⟩, ⟨h10, h11, h12⟩, ⟨h13, h14⟩, h15⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩

section Meas

variable {p : TapParams d e n τ} {v : TapVars ident d n τ}

lemma measurable_tradius (i : ℕ) :
    Measurable (fun ss : EuclideanSpace ℝ (Fin n) => tradius p ss i) :=
  measurable_const.min (Real.continuous_sqrt.measurable.comp
    (measurable_const.max (measurable_const.sub (measurable_remAt i))))

/-- The clipped gradient is jointly measurable in the meters, the model and the dataset
    (the radius depends on the state, so `measurable_clipV` does not apply). -/
lemma measurable_tcg (hok : TapOK p v) (i : ℕ) :
    Measurable (fun ((s, θ, D) : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin d) × τ.interp) =>
      tcg p s i θ D) := by
  have hr : Measurable (fun ((s, _, _) : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin d) ×
      τ.interp) => tradius p s i) := (measurable_tradius i).comp measurable_fst
  have hg : Measurable (fun ((_, θ, D) : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin d) ×
      τ.interp) => p.grad θ (p.record D i)) := by
    simp only [grad_record_eq_ite]
    refine Measurable.ite ((measurable_snd.comp measurable_snd) (hok.present i)) ?_
      measurable_const
    exact hok.grad.comp ((measurable_fst.comp measurable_snd).prodMk
      ((hok.recVal i).comp (measurable_snd.comp measurable_snd)))
  have hn : Measurable (fun ((_, θ, D) : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin d) ×
      τ.interp) => ‖p.grad θ (p.record D i)‖) := continuous_norm.measurable.comp hg
  unfold tcg clipV
  exact Measurable.ite (measurableSet_le hn hr) hg ((hr.div hn).smul hg)

end Meas

/-! ## The record step, as program expressions -/

section Program

variable (p : TapParams d e n τ) (v : TapVars ident d n τ)

/-- `acc + ḡ(X_i)`, on the memory. -/
noncomputable def accET (hok : TapOK p v) : Expr M (.vec d) :=
  ⟨fun h => accStepTap p (M.get h (.vec d) v.acc.name) (M.get h (.vec n) v.s.name)
      (M.get h .nat v.i.name) (M.get h (.vec d) v.x.name) (M.get h τ v.D.name), by
    set Φ : ((EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin d) ×
        τ.interp) × ℕ) → EuclideanSpace ℝ (Fin d) :=
      fun ((acc, s, θ, D), i) => accStepTap p acc s i θ D
    have hΦ : Measurable Φ := by
      refine measurable_from_prod_countable_left (fun i => ?_)
      have hc : Measurable (fun ((_, s, θ, D) : EuclideanSpace ℝ (Fin d) ×
          EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin d) × τ.interp) => tcg p s i θ D) :=
        (measurable_tcg hok i).comp measurable_snd
      exact measurable_fst.add hc
    exact hΦ.comp (((M.get_measurable (.vec d) v.acc.name).prodMk
      ((M.get_measurable (.vec n) v.s.name).prodMk ((M.get_measurable (.vec d) v.x.name).prodMk
        (M.get_measurable τ v.D.name)))).prodMk (M.get_measurable .nat v.i.name))⟩

/-- `s + ‖ḡ(X_i)‖² · e_i`, on the memory. -/
noncomputable def sET (hok : TapOK p v) : Expr M (.vec n) :=
  ⟨fun h => sStepTap p (M.get h (.vec n) v.s.name) (M.get h .nat v.i.name)
      (M.get h (.vec d) v.x.name) (M.get h τ v.D.name), by
    set Φ : ((EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin d) × τ.interp) × ℕ) →
        EuclideanSpace ℝ (Fin n) := fun ((s, θ, D), i) => sStepTap p s i θ D
    have hΦ : Measurable Φ := by
      refine measurable_from_prod_countable_left (fun i => ?_)
      have hc : Measurable (fun ((s, θ, D) : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin d) ×
          τ.interp) => ‖tcg p s i θ D‖ ^ 2) :=
        (continuous_norm.measurable.comp (measurable_tcg hok i)).pow_const 2
      exact measurable_fst.add (hc.smul (measurable_const' fun _ _ => rfl))
    exact hΦ.comp (((M.get_measurable (.vec n) v.s.name).prodMk
      ((M.get_measurable (.vec d) v.x.name).prodMk (M.get_measurable τ v.D.name))).prodMk
      (M.get_measurable .nat v.i.name))⟩

/-- `x := x − (η t / n)·(acc + z)`, reading the round counter `tv` for `η t`. -/
noncomputable def updET (tv : Vars ident .nat) : Expr M (.vec d) :=
  ⟨fun h => updStepTap (d := d) p.η n (M.get h .nat tv.name) (M.get h (.vec d) v.x.name)
      (M.get h (.vec d) v.acc.name) (M.get h (.vec d) v.z.name), by
    set Φ : ((EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ×
        EuclideanSpace ℝ (Fin d)) × ℕ) → EuclideanSpace ℝ (Fin d) :=
      fun ((θ, acc, z), t) => updStepTap (d := d) p.η n t θ acc z
    have hΦ : Measurable Φ := by
      refine measurable_from_prod_countable_left (fun t => ?_)
      exact measurable_fst.sub
        (((measurable_fst.comp measurable_snd).add (measurable_snd.comp measurable_snd)).const_smul
          (p.η t / (n : ℝ)))
    exact hΦ.comp (((M.get_measurable (.vec d) v.x.name).prodMk
      ((M.get_measurable (.vec d) v.acc.name).prodMk (M.get_measurable (.vec d) v.z.name))).prodMk
      (M.get_measurable .nat tv.name))⟩

/-- The record step: accumulate, meter, advance. -/
noncomputable def bodyT (hok : TapOK p v) : Cmd ident M :=
  Cmd.seq (Cmd.assign v.acc (accET p v hok)) (Cmd.seq (Cmd.assign v.s (sET p v hok))
    (Cmd.assign v.i (incW v.i)))

/-- `i := 0; acc := 0` -/
def initT : Cmd ident M :=
  Cmd.seq (Cmd.assign v.i (Expr.cst (t := .nat) 0)) (Cmd.assign v.acc (Expr.cst (t := .vec d) 0))

/-- The initialization: `s := 0; θ := 0`.  Both are constants, so the precondition of the
    program is adjacency alone. -/
noncomputable def initGDT : Cmd ident M :=
  Cmd.seq (Cmd.assign v.s (Expr.cst (t := .vec n) 0))
    (Cmd.assign v.x (Expr.cst (t := .vec d) 0))

end Program

/-! ## Reading the memory, and the record step as a map on memories -/

section Reading

variable {p : TapParams d e n τ} {v : TapVars ident d n τ}

abbrev tapX (v : TapVars ident d n τ) (h : M.heap) := M.get h (.vec d) v.x.name
abbrev tapA (v : TapVars ident d n τ) (h : M.heap) := M.get h (.vec d) v.acc.name
abbrev tapZ (v : TapVars ident d n τ) (h : M.heap) := M.get h (.vec d) v.z.name
abbrev tapS (v : TapVars ident d n τ) (h : M.heap) := M.get h (.vec n) v.s.name
abbrev tapI (v : TapVars ident d n τ) (h : M.heap) : ℕ := M.get h .nat v.i.name
abbrev tapD (v : TapVars ident d n τ) (h : M.heap) := M.get h τ v.D.name

/-- The memory after one record step: the three assignments of `bodyT`, by definition. -/
noncomputable def stepMapT (p : TapParams d e n τ) (v : TapVars ident d n τ) (h : M.heap) :
    M.heap :=
  let h₁ := M.set h (.vec d) v.acc.name
    (accStepTap p (tapA v h) (tapS v h) (tapI v h) (tapX v h) (tapD v h))
  let h₂ := M.set h₁ (.vec n) v.s.name (sStepTap p (tapS v h₁) (tapI v h₁) (tapX v h₁) (tapD v h₁))
  M.set h₂ .nat v.i.name (tapI v h₂ + 1)

lemma stepMapT_get (h : M.heap) :
    tapX v (stepMapT p v h) = tapX v h ∧ tapD v (stepMapT p v h) = tapD v h ∧
    tapI v (stepMapT p v h) = tapI v h + 1 ∧
    tapA v (stepMapT p v h) = accStepTap p (tapA v h) (tapS v h) (tapI v h) (tapX v h) (tapD v h) ∧
    tapS v (stepMapT p v h) = sStepTap p (tapS v h) (tapI v h) (tapX v h) (tapD v h) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := v.ne
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
  simp only [tapX, tapD, tapI, tapA, tapS, stepMapT, M.get_set_eq,
      get_set_other _ _ (Ne.symm h1), get_set_other _ _ (Ne.symm h3), get_set_other _ _ (Ne.symm h4),
      get_set_other _ _ h7, get_set_other _ _ (Ne.symm h7), get_set_other _ _ h8,
      get_set_other _ _ (Ne.symm h8), get_set_other _ _ h9, get_set_other _ _ h13,
      get_set_other _ _ (Ne.symm h13), get_set_other _ _ h14, get_set_other _ _ h15]

end Reading

/-! ## Weights and invariants

The invariants `PreT` and `JT` are in squared-norm units; only the weights `wMidT`/`wEndT`
mention `α`. -/

section Inv

variable {p : TapParams d e n τ} {v : TapVars ident d n τ}

/-- The remaining budget of record `j` in one run: `B − s[j]`. -/
noncomputable def remT (p : TapParams d e n τ) (v : TapVars ident d n τ) (j : ℕ) (h : M.heap) :
    ℝ := p.Bnorm - remAt (tapS v h) j

/-- **The remaining budget of record `j`** in the run that holds it:
    `B − s⟨1⟩[j] − s⟨2⟩[j]`, since the run without `j` spends nothing on it (`QuietT`). -/
noncomputable def remP (p : TapParams d e n τ) (v : TapVars ident d n τ) (j : ℕ)
    (m : M.heap × M.heap) : ℝ :=
  remT p v j m.1 + remT p v j m.2 - p.Bnorm

/-- A run without record `j` has spent nothing on it. -/
def QuietT (p : TapParams d e n τ) (v : TapVars ident d n τ) (j : ℕ) (m : M.heap × M.heap) :
    Prop :=
  (p.record (tapD v m.1) j = none → remAt (tapS v m.1) j = 0) ∧
    (p.record (tapD v m.2) j = none → remAt (tapS v m.2) j = 0)

/-- Squared norms to Rényi units at order `α`: `α / 2v`. -/
noncomputable def cT (p : TapParams d e n τ) (α : ℝ) : ℝ := α / (2 * (p.nvar : ℝ))

/-- The weight inside a round: the meter of `j` plus the charge of the gap. -/
noncomputable def wMidT (p : TapParams d e n τ) (v : TapVars ident d n τ) (α : ℝ) (j : ℕ) :
    M.heap × M.heap → ℝ≥0∞ :=
  expW α (fun m => cT p α * remP p v j m + cT p α * ‖tapA v m.1 - tapA v m.2‖ ^ 2)

/-- The weight between rounds: `ω = exp((α−1)α(B − s⟨1⟩[j] − s⟨2⟩[j])/2v)` (§5.2). -/
noncomputable def wEndT (p : TapParams d e n τ) (v : TapVars ident d n τ) (α : ℝ) (j : ℕ) :
    M.heap × M.heap → ℝ≥0∞ :=
  expW α (fun m => cT p α * remP p v j m)

/-- The invariant `R_j` of eq. (12) on memories (`liftP` adds the transcript equality). -/
def PreT (p : TapParams d e n τ) (v : TapVars ident d n τ) (j : ℕ) (m : M.heap × M.heap) :
    Prop :=
  AdjAtSym p.record j (tapD v m.1) (tapD v m.2) ∧ tapX v m.1 = tapX v m.2 ∧
    (∀ k : Fin n, (k : ℕ) ≠ j → tapS v m.1 k = tapS v m.2 k) ∧ QuietT p v j m ∧
    0 ≤ remP p v j m ∧ remP p v j m ≤ p.Bnorm

/-- The invariant of the record loop. -/
def JT (p : TapParams d e n τ) (v : TapVars ident d n τ) (j : ℕ) (t : ℕ)
    (m : M.heap × M.heap) : Prop :=
  AdjAtSym p.record j (tapD v m.1) (tapD v m.2) ∧ tapX v m.1 = tapX v m.2 ∧ tapI v m.1 = t ∧
    tapI v m.2 = t ∧ (∀ k : Fin n, (k : ℕ) ≠ j → tapS v m.1 k = tapS v m.2 k) ∧
    (t ≤ j → tapA v m.1 = tapA v m.2) ∧ QuietT p v j m ∧
    0 ≤ remP p v j m ∧ remP p v j m + ‖tapA v m.1 - tapA v m.2‖ ^ 2 ≤ p.Bnorm

lemma measurable_remT (j : ℕ) : Measurable (remT (M := M) p v j) :=
  measurable_const.sub ((measurable_remAt j).comp (M.get_measurable (.vec n) v.s.name))

lemma measurable_remP (j : ℕ) : Measurable (remP (M := M) p v j) :=
  (((measurable_remT j).comp measurable_fst).add ((measurable_remT j).comp measurable_snd)).sub
    measurable_const

lemma remP_comm {j : ℕ} (a b : M.heap) : remP p v j (b, a) = remP p v j (a, b) := by
  simp only [remP]; ring

/-- Writes that leave both meters alone leave `remP` alone. -/
lemma remP_congr {j : ℕ} {a b a' b' : M.heap} (h1 : tapS v a' = tapS v a)
    (h2 : tapS v b' = tapS v b) : remP p v j (a', b') = remP p v j (a, b) := by
  show remT p v j a' + remT p v j b' - p.Bnorm = remT p v j a + remT p v j b - p.Bnorm
  unfold remT; rw [h1, h2]

lemma cT_nonneg {α : ℝ} (hα : 1 < α) : 0 ≤ cT p α :=
  div_nonneg (by linarith) (mul_nonneg zero_le_two (NNReal.coe_nonneg _))

lemma goodWeight_wEndT {α : ℝ} (j : ℕ) : GoodWeight (wEndT (M := M) p v α j) :=
  goodWeight_expW (measurable_const.mul (measurable_remP j))

/-- The invariant does not see which run is on which side. -/
lemma JT_swap {j t : ℕ} {m : M.heap × M.heap} (hm : JT p v j t m) : JT p v j t m.swap := by
  obtain ⟨hadj, hx, hi1, hi2, hsk, hacc, ⟨hq1, hq2⟩, hr0, hrB⟩ := hm
  have hr : remP p v j m.swap = remP p v j m := remP_comm m.1 m.2
  refine ⟨hadj.symm, hx.symm, hi2, hi1, fun k hk => (hsk k hk).symm, fun h => (hacc h).symm,
    ⟨hq2, hq1⟩, by rw [hr]; exact hr0, ?_⟩
  rw [hr]
  show remP p v j m + ‖tapA v m.2 - tapA v m.1‖ ^ 2 ≤ p.Bnorm
  rw [norm_sub_rev]; exact hrB

end Inv

/-! ## The record step preserves the weight

The record step conserves `remP + ‖acc₁ − acc₂‖²` exactly: what record `j` adds to the gap
it subtracts from the meter of the run that holds it. -/

section StepPres

variable {p : TapParams d e n τ} {v : TapVars ident d n τ}

/-- One record step moves the meter of record `j` by the spend of the record it reads. -/
lemma remAt_stepMapT (h : M.heap) (j : ℕ) :
    remAt (tapS v (stepMapT p v h)) j = remAt (tapS v h) j
      + if j = tapI v h ∧ j < n then
          ‖tcg p (tapS v h) (tapI v h) (tapX v h) (tapD v h)‖ ^ 2 else 0 := by
  rw [(stepMapT_get (p := p) (v := v) h).2.2.2.2]; unfold sStepTap; rw [remAt_add_eAt]

/-- The step, when the differing record, if it is the one read, is absent on the right. -/
private theorem step_preservesT_of (hC : 0 ≤ p.Cl) {j : ℕ} (hj : j < n) (t : ℕ)
    (m : M.heap × M.heap) (hm : JT p v j t m)
    (hbot : t = j → p.record (tapD v m.2) j = none) :
    JT p v j (t + 1) (stepMapT p v m.1, stepMapT p v m.2) ∧
    remP p v j (stepMapT p v m.1, stepMapT p v m.2)
        + ‖tapA v (stepMapT p v m.1) - tapA v (stepMapT p v m.2)‖ ^ 2
      = remP p v j m + ‖tapA v m.1 - tapA v m.2‖ ^ 2 := by
  obtain ⟨hadj, hx, hi1, hi2, hsk, hacc, ⟨hq1, hq2⟩, hr0, hrB⟩ := hm
  obtain ⟨x1, d1, i1, a1, s1⟩ := stepMapT_get (p := p) (v := v) m.1
  obtain ⟨x2, d2, i2, a2, s2⟩ := stepMapT_get (p := p) (v := v) m.2
  have r1 := remAt_stepMapT (p := p) (v := v) m.1 j
  have r2 := remAt_stepMapT (p := p) (v := v) m.2 j
  have hremP : ∀ a b : M.heap,
      remP p v j (a, b) = p.Bnorm - remAt (tapS v a) j - remAt (tapS v b) j :=
    fun _ _ => by simp only [remP, remT]; ring
  have hremP0 : remP p v j m = p.Bnorm - remAt (tapS v m.1) j - remAt (tapS v m.2) j :=
    hremP m.1 m.2
  rw [hi1] at a1 s1 i1 r1
  rw [hi2] at a2 s2 i2 r2
  rw [hx] at a1 s1 r1
  set X := tapX v m.2
  set S1 := tapS v m.1
  set S2 := tapS v m.2
  set A1 := tapA v m.1
  set A2 := tapA v m.2
  set D1 := tapD v m.1
  set D2 := tapD v m.2
  by_cases htj : t = j
  · -- the differing record: it spends exactly what it contributes to the gap
    subst htj
    have hA : A1 = A2 := hacc le_rfl
    have hb : p.record D2 t = none := hbot rfl
    have hz : tcg p S2 t X D2 = 0 := tcg_bot X hb
    have hq2' : remAt S2 t = 0 := hq2 hb
    set G := tcg p S1 t X D1 with hG
    have hgap : tapA v (stepMapT p v m.1) - tapA v (stepMapT p v m.2) = G := by
      rw [a1, a2]; unfold accStepTap; rw [hz, hA]
      simp only [add_zero]
      abel
    have hR1 : remAt (tapS v (stepMapT p v m.1)) t = remAt S1 t + ‖G‖ ^ 2 := by
      rw [r1, if_pos ⟨rfl, hj⟩]
    have hR2 : remAt (tapS v (stepMapT p v m.2)) t = 0 := by
      rw [r2, if_pos ⟨rfl, hj⟩, hz, norm_zero, hq2']; ring
    have hsle : remAt S1 t ≤ p.Bnorm := by rw [hremP0, hq2'] at hr0; linarith
    have htap : remAt S1 t + ‖G‖ ^ 2 ≤ p.Bnorm := norm_tcg_sq_le_rem hC hsle X D1
    have hR : remP p v t (stepMapT p v m.1, stepMapT p v m.2) = p.Bnorm - remAt S1 t - ‖G‖ ^ 2 := by
      rw [hremP, hR1, hR2]; ring
    have hsum : remP p v t (stepMapT p v m.1, stepMapT p v m.2)
        + ‖tapA v (stepMapT p v m.1) - tapA v (stepMapT p v m.2)‖ ^ 2
          = remP p v t m + ‖A1 - A2‖ ^ 2 := by
      rw [hR, hgap, hremP0, hq2', hA, sub_self, norm_zero]; ring
    refine ⟨⟨?_, ?_, i1, i2, ?_, fun h => absurd h (by omega), ⟨?_, ?_⟩, ?_, ?_⟩, hsum⟩
    · show AdjAtSym p.record t (tapD v (stepMapT p v m.1)) (tapD v (stepMapT p v m.2)); rw [d1, d2]; exact hadj
    · show tapX v (stepMapT p v m.1) = tapX v (stepMapT p v m.2); rw [x1, x2, hx]
    · intro k hk
      show tapS v (stepMapT p v m.1) k = tapS v (stepMapT p v m.2) k
      rw [s1, s2]; unfold sStepTap
      rw [add_eAt_apply, add_eAt_apply, if_neg hk, if_neg hk, add_zero, add_zero]
      exact hsk k hk
    · intro hn
      have hn' : p.record D1 t = none := by rw [← d1]; exact hn
      rw [hR1, hq1 hn', hG, tcg_bot X hn', norm_zero]; ring
    · intro _; exact hR2
    · rw [hR]; linarith
    · rw [hsum, hA, sub_self, norm_zero]
      have := hrB; rw [hA, sub_self, norm_zero] at this; simpa using this
  · -- any other record: the two runs agree on it, so neither the gap nor `j`'s meter moves
    have hrec : p.record D1 t = p.record D2 t := by
      rcases hadj with h | h
      · exact h.1 t htj
      · exact (h.1 t htj).symm
    have hsa : remAt S1 t = remAt S2 t := by
      unfold remAt
      split_ifs with ht
      · exact hsk ⟨t, ht⟩ htj
      · rfl
    have hrad : tradius p S1 t = tradius p S2 t := by unfold tradius; rw [hsa]
    have htcg : tcg p S1 t X D1 = tcg p S2 t X D2 := by unfold tcg; rw [hrad, hrec]
    have hgap : tapA v (stepMapT p v m.1) - tapA v (stepMapT p v m.2) = A1 - A2 := by
      rw [a1, a2]; unfold accStepTap; rw [htcg]; abel
    have hjt : ¬ (j = t ∧ j < n) := fun h => htj h.1.symm
    have hR1 : remAt (tapS v (stepMapT p v m.1)) j = remAt S1 j := by
      rw [r1, if_neg hjt, add_zero]
    have hR2 : remAt (tapS v (stepMapT p v m.2)) j = remAt S2 j := by
      rw [r2, if_neg hjt, add_zero]
    have hR : remP p v j (stepMapT p v m.1, stepMapT p v m.2) = remP p v j m := by
      rw [hremP, hR1, hR2, hremP0]
    refine ⟨⟨?_, ?_, i1, i2, ?_, fun h => ?_, ⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
    · show AdjAtSym p.record j (tapD v (stepMapT p v m.1)) (tapD v (stepMapT p v m.2)); rw [d1, d2]; exact hadj
    · show tapX v (stepMapT p v m.1) = tapX v (stepMapT p v m.2); rw [x1, x2, hx]
    · intro k hk
      show tapS v (stepMapT p v m.1) k = tapS v (stepMapT p v m.2) k
      rw [s1, s2]; unfold sStepTap
      rw [add_eAt_apply, add_eAt_apply, hsk k hk, htcg]
    · show tapA v (stepMapT p v m.1) = tapA v (stepMapT p v m.2)
      rw [← sub_eq_zero, hgap, sub_eq_zero]; exact hacc (by omega)
    · intro hn; rw [hR1]; exact hq1 (by rw [← d1]; exact hn)
    · intro hn; rw [hR2]; exact hq2 (by rw [← d2]; exact hn)
    · rw [hR]; exact hr0
    · rw [hR, hgap]; exact hrB
    · rw [hR, hgap]

/-- **The record step keeps the invariant and conserves `remP + ‖acc₁ − acc₂‖²`**, whichever
    run holds the differing record (the other case by `JT_swap`). -/
theorem step_preservesT (hC : 0 ≤ p.Cl) {j : ℕ} (hj : j < n) (t : ℕ) (m : M.heap × M.heap)
    (hm : JT p v j t m) :
    JT p v j (t + 1) (stepMapT p v m.1, stepMapT p v m.2) ∧
    remP p v j (stepMapT p v m.1, stepMapT p v m.2)
        + ‖tapA v (stepMapT p v m.1) - tapA v (stepMapT p v m.2)‖ ^ 2
      = remP p v j m + ‖tapA v m.1 - tapA v m.2‖ ^ 2 := by
  by_cases hb : t = j → p.record (tapD v m.2) j = none
  · exact step_preservesT_of hC hj t m hm hb
  · have hb1 : p.record (tapD v m.1) j = none := by
      rcases hm.1 with h | h
      · exact absurd (fun _ => h.2) hb
      · exact h.2
    obtain ⟨h1, h2⟩ := step_preservesT_of hC hj t m.swap (JT_swap hm) (fun _ => hb1)
    refine ⟨JT_swap h1, ?_⟩
    have e1 : remP p v j (stepMapT p v m.2, stepMapT p v m.1)
        = remP p v j (stepMapT p v m.1, stepMapT p v m.2) := remP_comm _ _
    have e2 : remP p v j m.swap = remP p v j m := remP_comm m.1 m.2
    change remP p v j (stepMapT p v m.2, stepMapT p v m.1)
        + ‖tapA v (stepMapT p v m.2) - tapA v (stepMapT p v m.1)‖ ^ 2
      = remP p v j m.swap + ‖tapA v m.2 - tapA v m.1‖ ^ 2 at h2
    rw [e1, e2, norm_sub_rev, norm_sub_rev (tapA v m.2)] at h2
    exact h2

end StepPres

/-! ## The round -/

section Round

variable {p : TapParams d e n τ} {v : TapVars ident d n τ}

lemma initT_get (h : M.heap) :
    tapX v (M.set (M.set h .nat v.i.name 0) (.vec d) v.acc.name 0) = tapX v h ∧
    tapD v (M.set (M.set h .nat v.i.name 0) (.vec d) v.acc.name 0) = tapD v h ∧
    tapS v (M.set (M.set h .nat v.i.name 0) (.vec d) v.acc.name 0) = tapS v h ∧
    tapI v (M.set (M.set h .nat v.i.name 0) (.vec d) v.acc.name 0) = 0 ∧
    tapA v (M.set (M.set h .nat v.i.name 0) (.vec d) v.acc.name 0) = 0 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := v.ne
  refine ⟨?_, ?_, ?_, ?_, M.get_set_eq _ _ _ _⟩
  · rw [tapX, get_set_other _ _ (Ne.symm h1), get_set_other _ _ (Ne.symm h4)]
  · rw [tapD, get_set_other _ _ h9, get_set_other _ _ h15]
  · rw [tapS, get_set_other _ _ h7, get_set_other _ _ (Ne.symm h13)]
  · rw [tapI, get_set_other _ _ h8, M.get_set_eq]

/-- Reading the state after the initialization. -/
lemma initGDT_get (h : M.heap) :
    tapD v (M.set (M.set h (.vec n) v.s.name 0) (.vec d) v.x.name 0) = tapD v h ∧
    tapX v (M.set (M.set h (.vec n) v.s.name 0) (.vec d) v.x.name 0) = 0 ∧
    tapS v (M.set (M.set h (.vec n) v.s.name 0) (.vec d) v.x.name 0) = 0 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := v.ne
  refine ⟨?_, M.get_set_eq _ _ _ _, ?_⟩
  · rw [tapD, get_set_other _ _ h5, get_set_other _ _ h14]
  · rw [tapS, get_set_other _ _ h3, M.get_set_eq]

/-- After the noise: the noisy sums agree, and the budget of `j` is in `[0, B]`. -/
def Q2T (p : TapParams d e n τ) (v : TapVars ident d n τ) (j : ℕ) (m : M.heap × M.heap) :
    Prop :=
  PreT p v j m ∧ tapA v m.1 + tapZ v m.1 = tapA v m.2 + tapZ v m.2

end Round

end RenyiFilter
