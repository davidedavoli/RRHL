import Xhl.Duality.Discrete.Renyi
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Convex.Segment
import Mathlib.Topology.Order.Compact

open ENNReal Classical

namespace DStd

/-!
# Witness-free characterization of the discrete Rényi lifting

The two-witness lifting `FLiftMul α R η μ₁ μ₂` asks for witnesses `w₁, w₂` on
`A × B`, supported in `R`, pinning the left marginal of `w₁` to `μ₁` and the
right marginal of `w₂` to `μ₂`, with `hRen α w₁ w₂ ≤ η`.  This file proves
that it is equivalent to a *witness-free* condition on test functions:

    ∀ k₁ k₂, (∀ (a,b) ∈ R, k₁ a ^ α * k₂ b ^ (1−α) ≤ 1) →
      (∑ k₁ a μ₁ a) ^ α * (∑ k₂ b μ₂ b) ^ (1−α) ≤ η,

i.e. the codensity lifting with tests into the one-point space.

* `codLift_of_flift` — **weak duality** (witnesses ⇒ tests), for arbitrary types.
* The finite-type core of strong duality: a minimizer of the reduced problem over kernels
  (`J`), its first-order condition, and certificate tests (`kOne`, `kTwo`) whose value is
  the optimum (`testVal_cert`).  `RenyiDualityGen.lean` extends this to countable types.
-/

open ENNReal Classical Distr Range

namespace Distr

variable {A B : Type}

/-!
## The witness-free lifting
-/

/-- Admissible test pairs: pointwise Hellinger integral at most `1` on `R`. -/
def TestAdm (α : ℝ) (R : A → B → Prop) (k₁ : A → ℝ≥0∞) (k₂ : B → ℝ≥0∞) : Prop :=
  ∀ a b, R a b → k₁ a ^ α * k₂ b ^ (1 - α) ≤ 1

/-- The Hellinger integral of the two test expectations. -/
noncomputable def testVal (α : ℝ) (μ₁ : Distr A) (μ₂ : Distr B)
    (k₁ : A → ℝ≥0∞) (k₂ : B → ℝ≥0∞) : ℝ≥0∞ :=
  (∑' a, k₁ a * μ₁.mass a) ^ α * (∑' b, k₂ b * μ₂.mass b) ^ (1 - α)

/-- The witness-free (codensity, one-point-test) Rényi lifting. -/
def CodLiftMul (α : ℝ) (R : A → B → Prop) (η : ℝ≥0∞)
    (μ₁ : Distr A) (μ₂ : Distr B) : Prop :=
  ∀ k₁ k₂, TestAdm α R k₁ k₂ → testVal α μ₁ μ₂ k₁ k₂ ≤ η

/-!
## Weak duality
-/

/-- Pointwise bound: an admissible test pair does not increase the perspective. -/
lemma test_term_le {α : ℝ} (hα : 1 < α) {x y u v : ℝ≥0∞} (hu : u ≠ ⊤) (hv : v ≠ ⊤)
    (hxy : x ^ α * y ^ (1 - α) ≤ 1) :
    (x * u) ^ α * (y * v) ^ (1 - α) ≤ u ^ α * v ^ (1 - α) := by
  have hα0 : (0 : ℝ) < α := by linarith
  have h1α : (1 : ℝ) - α < 0 := by linarith
  rcases eq_or_ne u 0 with hu0 | hu0
  · rw [hu0, mul_zero, ENNReal.zero_rpow_of_pos hα0, zero_mul]; exact zero_le
  rcases eq_or_ne v 0 with hv0 | hv0
  · rw [hv0, ENNReal.zero_rpow_of_neg h1α, ENNReal.mul_top]
    · exact le_top
    · exact (ENNReal.rpow_pos (pos_iff_ne_zero.mpr hu0) hu).ne'
  rcases eq_or_ne y ⊤ with hy | hy
  · rw [hy, ENNReal.top_mul hv0, ENNReal.top_rpow_of_neg h1α, mul_zero]; exact zero_le
  have hx : x ≠ ⊤ := by
    intro hx
    rw [hx, ENNReal.top_rpow_of_pos hα0] at hxy
    have hy0 : y ^ (1 - α) = 0 := by
      by_contra h
      rw [ENNReal.top_mul h] at hxy
      exact absurd hxy (not_le.mpr ENNReal.one_lt_top)
    rw [ENNReal.rpow_eq_zero_iff] at hy0
    rcases hy0 with ⟨_, h⟩ | ⟨h, _⟩
    · linarith
    · exact hy h
  rw [ENNReal.mul_rpow_of_ne_top hx hu, ENNReal.mul_rpow_of_ne_top hy hv]
  calc x ^ α * u ^ α * (y ^ (1 - α) * v ^ (1 - α))
      = (x ^ α * y ^ (1 - α)) * (u ^ α * v ^ (1 - α)) := by ring
    _ ≤ 1 * (u ^ α * v ^ (1 - α)) := mul_le_mul' hxy le_rfl
    _ = u ^ α * v ^ (1 - α) := one_mul _

/-- **Weak duality**: for witnesses `w₁, w₂` with `w₁` supported in `R`, every
    admissible test pair is bounded by the Hellinger integral of the witnesses. -/
lemma testVal_le_hRen {α : ℝ} (hα : 1 < α) {R : A → B → Prop}
    {k₁ : A → ℝ≥0∞} {k₂ : B → ℝ≥0∞} (hk : TestAdm α R k₁ k₂)
    (w₁ w₂ : Distr (A × B)) (hr₁ : range (fun p => R p.1 p.2) w₁) :
    testVal α w₁.fst w₂.snd k₁ k₂ ≤ hRen α w₁ w₂ := by
  have hα0 : (0 : ℝ) < α := by linarith
  have hL : ∑' a, k₁ a * w₁.fst.mass a = ∑' p : A × B, k₁ p.1 * w₁.mass p := by
    rw [ENNReal.tsum_prod']
    exact tsum_congr fun a => by rw [fst_mass, ← ENNReal.tsum_mul_left]
  have hR : ∑' b, k₂ b * w₂.snd.mass b = ∑' p : A × B, k₂ p.2 * w₂.mass p := by
    rw [ENNReal.tsum_prod', ENNReal.tsum_comm]
    exact tsum_congr fun b => by rw [snd_mass, ← ENNReal.tsum_mul_left]
  rw [testVal, hL, hR]
  refine le_trans (tsum_rpow_mul_rpow_le _ _ hα) (ENNReal.tsum_le_tsum fun p => ?_)
  rcases eq_or_ne (w₁.mass p) 0 with h0 | h0
  · rw [h0, mul_zero, ENNReal.zero_rpow_of_pos hα0, zero_mul]; exact zero_le
  · exact test_term_le hα (w₁.mass_ne_top p) (w₂.mass_ne_top p) (hk p.1 p.2 (hr₁ p h0))

/-- **Weak duality** at the level of liftings. -/
theorem codLift_of_flift {α : ℝ} (hα : 1 < α) {R : A → B → Prop} {η : ℝ≥0∞}
    {μ₁ : Distr A} {μ₂ : Distr B} (h : FLiftMul α R η μ₁ μ₂) :
    CodLiftMul α R η μ₁ μ₂ := by
  obtain ⟨⟨w₁, w₂⟩, h1, h2, h3, _, h5⟩ := h
  intro k₁ k₂ hk
  rw [← h1, ← h2]
  exact le_trans (testVal_le_hRen hα hk w₁ w₂ h3) h5

/-!
## The first-order condition (real-analytic core)
-/

/-- Moving mass from a target of larger density ratio to one of smaller ratio
    decreases the objective: at a minimizer the ratios are ordered.  Real form. -/
lemma kkt_real {α : ℝ} (hα : 1 < α) {a b a' b' s t₀ : ℝ} (hs : 0 < s) (ht₀ : 0 < t₀)
    (hmin : ∀ t, 0 ≤ t → t ≤ t₀ →
      a ^ α * b ^ (1 - α) + a' ^ α * b' ^ (1 - α)
        ≤ (a - s * t) ^ α * b ^ (1 - α) + (a' + s * t) ^ α * b' ^ (1 - α)) :
    a ^ (α - 1) * b ^ (1 - α) ≤ a' ^ (α - 1) * b' ^ (1 - α) := by
  set g : ℝ → ℝ := fun t => (a - s * t) ^ α * b ^ (1 - α) + (a' + s * t) ^ α * b' ^ (1 - α)
    with hg
  have hd1 : HasDerivAt (fun t : ℝ => a - s * t) (-s) 0 :=
    (((hasDerivAt_id (0:ℝ)).const_mul s).const_sub a).congr_deriv (by simp)
  have hd2 : HasDerivAt (fun t : ℝ => a' + s * t) s 0 :=
    (((hasDerivAt_id (0:ℝ)).const_mul s).const_add a').congr_deriv (by simp)
  set D : ℝ := (-s) * α * a ^ (α - 1) * b ^ (1 - α) + s * α * a' ^ (α - 1) * b' ^ (1 - α)
    with hD
  have hdg : HasDerivAt g D 0 := by
    have h1 := (hd1.rpow_const (Or.inr hα.le)).mul_const (b ^ (1 - α))
    have h2 := (hd2.rpow_const (Or.inr hα.le)).mul_const (b' ^ (1 - α))
    have h := h1.add h2
    simp only [mul_zero, sub_zero, add_zero] at h
    exact h
  have hmin' : IsLocalMinOn g (Set.Icc 0 t₀) 0 := by
    refine eventually_nhdsWithin_of_forall fun t ht => ?_
    show g 0 ≤ g t
    simp only [hg, mul_zero, sub_zero, add_zero]
    exact hmin t ht.1 ht.2
  have htan : t₀ ∈ posTangentConeAt (Set.Icc 0 t₀) 0 := by
    refine mem_posTangentConeAt_of_segment_subset ?_
    rw [zero_add, segment_eq_Icc ht₀.le]
  have hnn := hmin'.hasFDerivWithinAt_nonneg hdg.hasDerivWithinAt.hasFDerivWithinAt htan
  have hD0 : 0 ≤ D := by
    have h' : 0 ≤ t₀ * D := by simpa [smul_eq_mul, mul_comm] using hnn
    exact nonneg_of_mul_nonneg_right h' ht₀
  have hsα : 0 < s * α := mul_pos hs (by linarith)
  have : 0 ≤ s * α * (a' ^ (α - 1) * b' ^ (1 - α) - a ^ (α - 1) * b ^ (1 - α)) := by
    rw [hD] at hD0; nlinarith
  have := nonneg_of_mul_nonneg_right this hsα
  linarith

/-- Helper: a nonzero finite base has finite powers. -/
lemma rpow_ne_top_of_ne_zero_of_ne_top {x : ℝ≥0∞} (hx0 : x ≠ 0) (hx : x ≠ ⊤) (y : ℝ) :
    x ^ y ≠ ⊤ := by
  intro h
  rw [ENNReal.rpow_eq_top_iff] at h
  rcases h with ⟨h, _⟩ | ⟨h, _⟩
  · exact hx0 h
  · exact hx h

/-- Helper: a nonzero finite base has nonzero powers. -/
lemma rpow_ne_zero_of_ne_zero_of_ne_top {x : ℝ≥0∞} (hx0 : x ≠ 0) (hx : x ≠ ⊤) (y : ℝ) :
    x ^ y ≠ 0 := by
  intro h
  rw [ENNReal.rpow_eq_zero_iff] at h
  rcases h with ⟨h, _⟩ | ⟨h, _⟩
  · exact hx0 h
  · exact hx h

/-- `(A / B) ^ (α - 1) = A ^ (α - 1) * B ^ (1 - α)`. -/
lemma div_rpow_sub_one {α : ℝ} (hα : 1 < α) (A B : ℝ≥0∞) :
    (A / B) ^ (α - 1) = A ^ (α - 1) * B ^ (1 - α) := by
  rw [ENNReal.div_rpow_of_nonneg _ _ (by linarith : (0:ℝ) ≤ α - 1), div_eq_mul_inv,
    ← ENNReal.rpow_neg, show -(α - 1) = 1 - α by ring]

/-- The first-order condition, `ℝ≥0∞` form: at a minimizer, moving mass from `b`
    to `b'` cannot help, hence the density ratio at `b` is at most that at `b'`. -/
lemma kkt_ennreal {α : ℝ} (hα : 1 < α) {A B A' B' s t₀ : ℝ≥0∞}
    (hA : A ≠ ⊤) (hA' : A' ≠ ⊤) (hB0 : B ≠ 0) (hB : B ≠ ⊤) (hB0' : B' ≠ 0) (hB' : B' ≠ ⊤)
    (hs0 : s ≠ 0) (hs : s ≠ ⊤) (ht0 : t₀ ≠ 0) (ht : t₀ ≠ ⊤) (hst : s * t₀ ≤ A)
    (hmin : ∀ t, t ≤ t₀ →
      A ^ α * B ^ (1 - α) + A' ^ α * B' ^ (1 - α)
        ≤ (A - s * t) ^ α * B ^ (1 - α) + (A' + s * t) ^ α * B' ^ (1 - α)) :
    A / B ≤ A' / B' := by
  have hα0 : (0 : ℝ) ≤ α := by linarith
  have hBr : B ^ (1 - α) ≠ ⊤ := rpow_ne_top_of_ne_zero_of_ne_top hB0 hB _
  have hBr' : B' ^ (1 - α) ≠ ⊤ := rpow_ne_top_of_ne_zero_of_ne_top hB0' hB' _
  -- the real-valued minimality hypothesis
  have hmin_real : ∀ t : ℝ, 0 ≤ t → t ≤ t₀.toReal →
      A.toReal ^ α * B.toReal ^ (1 - α) + A'.toReal ^ α * B'.toReal ^ (1 - α)
        ≤ (A.toReal - s.toReal * t) ^ α * B.toReal ^ (1 - α)
          + (A'.toReal + s.toReal * t) ^ α * B'.toReal ^ (1 - α) := by
    intro t ht0' htt
    set T : ℝ≥0∞ := ENNReal.ofReal t with hT
    have hTle : T ≤ t₀ := (ENNReal.ofReal_le_iff_le_toReal ht).mpr htt
    have hTtop : T ≠ ⊤ := ENNReal.ofReal_ne_top
    have hsT : s * T ≤ A := le_trans (mul_le_mul' le_rfl hTle) hst
    have hsTtop : s * T ≠ ⊤ := ENNReal.mul_ne_top hs hTtop
    have h := hmin T hTle
    have hL : A ^ α * B ^ (1 - α) + A' ^ α * B' ^ (1 - α) ≠ ⊤ :=
      ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hα0 hA) hBr,
        ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hα0 hA') hBr'⟩
    have hR : (A - s * T) ^ α * B ^ (1 - α) + (A' + s * T) ^ α * B' ^ (1 - α) ≠ ⊤ :=
      ENNReal.add_ne_top.mpr
        ⟨ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hα0 (ENNReal.sub_ne_top hA)) hBr,
         ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hα0
           (ENNReal.add_ne_top.mpr ⟨hA', hsTtop⟩)) hBr'⟩
    have h' := (ENNReal.toReal_le_toReal hL hR).mpr h
    rw [ENNReal.toReal_add (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hα0 hA) hBr)
          (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hα0 hA') hBr'),
        ENNReal.toReal_add
          (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hα0 (ENNReal.sub_ne_top hA)) hBr)
          (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hα0
            (ENNReal.add_ne_top.mpr ⟨hA', hsTtop⟩)) hBr'),
        ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul,
        ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow,
        ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow,
        ENNReal.toReal_sub_of_le hsT hA, ENNReal.toReal_add hA' hsTtop,
        ENNReal.toReal_mul, hT, ENNReal.toReal_ofReal ht0'] at h'
    exact h'
  have hs_pos : 0 < s.toReal := ENNReal.toReal_pos hs0 hs
  have ht_pos : 0 < t₀.toReal := ENNReal.toReal_pos ht0 ht
  have hreal := kkt_real hα hs_pos ht_pos hmin_real
  -- back to `ℝ≥0∞`
  have hX : A ^ (α - 1) * B ^ (1 - α) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by linarith) hA) hBr
  have hX' : A' ^ (α - 1) * B' ^ (1 - α) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by linarith) hA') hBr'
  have hle : A ^ (α - 1) * B ^ (1 - α) ≤ A' ^ (α - 1) * B' ^ (1 - α) := by
    rw [← ENNReal.toReal_le_toReal hX hX', ENNReal.toReal_mul, ENNReal.toReal_mul,
      ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow,
      ← ENNReal.toReal_rpow]
    exact hreal
  rw [← div_rpow_sub_one hα, ← div_rpow_sub_one hα] at hle
  exact (ENNReal.rpow_le_rpow_iff (by linarith)).mp hle

/-!
## The reduced problem over kernels (finite types)
-/

section Finite

variable [Fintype A] [Fintype B]

/-- Kernels from `A` to `B` (unnormalized; feasibility is a separate predicate). -/
abbrev Ker (A B : Type) := A → B → ℝ≥0∞

/-- Feasible kernels: on every source of positive mass, a probability vector
    supported in `R'`. -/
def Feas (μ₁ : Distr A) (R' : A → B → Prop) (K : Ker A B) : Prop :=
  ∀ a, μ₁.mass a ≠ 0 → (∑ b, K a b = 1) ∧ ∀ b, ¬ R' a b → K a b = 0

/-- The image of `μ₁` under the kernel. -/
noncomputable def nu (μ₁ : Distr A) (K : Ker A B) (b : B) : ℝ≥0∞ :=
  ∑ a, μ₁.mass a * K a b

/-- The reduced objective: the Hellinger integral of `ν_K` against `μ₂`, summed
    over the support of `μ₂` (so that it is continuous in `K`). -/
noncomputable def J (α : ℝ) (μ₁ : Distr A) (μ₂ : Distr B) (K : Ker A B) : ℝ≥0∞ :=
  ∑ b ∈ Finset.univ.filter (fun b => μ₂.mass b ≠ 0), nu μ₁ K b ^ α * μ₂.mass b ^ (1 - α)

/-- The same sum over all of `B`. -/
noncomputable def Jfull (α : ℝ) (μ₁ : Distr A) (μ₂ : Distr B) (K : Ker A B) : ℝ≥0∞ :=
  ∑ b, nu μ₁ K b ^ α * μ₂.mass b ^ (1 - α)

variable {μ₁ : Distr A} {μ₂ : Distr B} {R' : A → B → Prop} {K : Ker A B}

lemma Feas.le_one (hK : Feas μ₁ R' K) {a : A} (ha : μ₁.mass a ≠ 0) (b : B) : K a b ≤ 1 := by
  rw [← (hK a ha).1]
  exact Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ b)

lemma Feas.ne_top (hK : Feas μ₁ R' K) {a : A} (ha : μ₁.mass a ≠ 0) (b : B) : K a b ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (hK.le_one ha b)

lemma sum_mass_le_one (μ : Distr A) : ∑ a, μ.mass a ≤ 1 := by
  have h := μ.le_one; rwa [tsum_fintype] at h

lemma nu_le_one (hK : Feas μ₁ R' K) (b : B) : nu μ₁ K b ≤ 1 := by
  refine le_trans (Finset.sum_le_sum fun a _ => ?_) (sum_mass_le_one μ₁)
  rcases eq_or_ne (μ₁.mass a) 0 with ha | ha
  · rw [ha, zero_mul]
  · exact mul_le_of_le_one_right' (hK.le_one ha b)

lemma nu_ne_top (hK : Feas μ₁ R' K) (b : B) : nu μ₁ K b ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (nu_le_one hK b)

lemma nu_eq_zero_of_not (hK : Feas μ₁ R' K) {b : B} (hb : ∀ a, ¬ R' a b) : nu μ₁ K b = 0 := by
  refine Finset.sum_eq_zero fun a _ => ?_
  rcases eq_or_ne (μ₁.mass a) 0 with ha | ha
  · rw [ha, zero_mul]
  · rw [(hK a ha).2 b (hb a), mul_zero]

lemma single_le_nu {a : A} (b : B) : μ₁.mass a * K a b ≤ nu μ₁ K b := by
  unfold nu
  exact Finset.single_le_sum (f := fun a' => μ₁.mass a' * K a' b) (fun _ _ => zero_le)
    (Finset.mem_univ a)

lemma J_ne_top {α : ℝ} (hα : 1 < α) (hK : Feas μ₁ R' K) : J α μ₁ μ₂ K ≠ ⊤ := by
  refine (ENNReal.sum_lt_top.mpr fun b hb => ?_).ne
  have hb' : μ₂.mass b ≠ 0 := (Finset.mem_filter.mp hb).2
  exact ENNReal.mul_lt_top
    (ENNReal.rpow_lt_top_of_nonneg (by linarith) (nu_ne_top hK b))
    (rpow_ne_top_of_ne_zero_of_ne_top hb' (μ₂.mass_ne_top b) _).lt_top

/-- `J` agrees with `Jfull` on kernels feasible for a relation inside the
    support of `μ₂`. -/
lemma J_eq_Jfull {α : ℝ} (hα : 1 < α) (hR' : ∀ a b, R' a b → μ₂.mass b ≠ 0)
    (hK : Feas μ₁ R' K) : J α μ₁ μ₂ K = Jfull α μ₁ μ₂ K := by
  rw [Jfull, J, Finset.sum_filter]
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases hb : μ₂.mass b ≠ 0
  · rw [if_pos hb]
  · rw [if_neg hb]
    push Not at hb
    rw [nu_eq_zero_of_not hK (fun a h => absurd (hR' a b h) (not_not.mpr hb)),
      ENNReal.zero_rpow_of_pos (by linarith), zero_mul]

lemma J_continuous (α : ℝ) (μ₁ : Distr A) (μ₂ : Distr B) : Continuous (J α μ₁ μ₂) := by
  refine continuous_finsetSum _ fun b hb => ?_
  have hb' : μ₂.mass b ≠ 0 := (Finset.mem_filter.mp hb).2
  have hc : μ₂.mass b ^ (1 - α) ≠ ⊤ :=
    rpow_ne_top_of_ne_zero_of_ne_top hb' (μ₂.mass_ne_top b) _
  refine (ENNReal.continuous_mul_const hc).comp (ENNReal.continuous_rpow_const.comp ?_)
  exact continuous_finsetSum _ fun a _ =>
    (ENNReal.continuous_const_mul (μ₁.mass_ne_top a)).comp
      ((continuous_apply b).comp (continuous_apply a))

lemma isCompact_feas (μ₁ : Distr A) (R' : A → B → Prop) :
    IsCompact {K : Ker A B | Feas μ₁ R' K} := by
  refine isCompact_univ.of_isClosed_subset ?_ (Set.subset_univ _)
  have : {K : Ker A B | Feas μ₁ R' K} = ⋂ a, ⋂ (_ : μ₁.mass a ≠ 0),
      ({K : Ker A B | ∑ b, K a b = 1} ∩ ⋂ b, ⋂ (_ : ¬ R' a b), {K : Ker A B | K a b = 0}) := by
    ext K
    simp only [Feas, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_inter_iff]
  rw [this]
  refine isClosed_iInter fun a => isClosed_iInter fun _ => IsClosed.inter ?_ ?_
  · exact isClosed_eq (continuous_finsetSum _ fun b _ =>
      (continuous_apply b).comp (continuous_apply a)) continuous_const
  · exact isClosed_iInter fun b => isClosed_iInter fun _ =>
      isClosed_eq ((continuous_apply b).comp (continuous_apply a)) continuous_const

/-- A feasible kernel exists under the partner condition. -/
lemma feas_nonempty (μ₁ : Distr A) (R' : A → B → Prop)
    (hnd : ∀ a, μ₁.mass a ≠ 0 → ∃ b, R' a b) :
    ∃ K : Ker A B, Feas μ₁ R' K := by
  refine ⟨fun a b => if h : μ₁.mass a ≠ 0 then
      (if b = Classical.choose (hnd a h) then 1 else 0) else 0, fun a ha => ?_⟩
  simp only [dif_pos ha]
  refine ⟨?_, fun b hb => ?_⟩
  · rw [Finset.sum_ite_eq']; simp
  · split_ifs with hbe
    · exact absurd (hbe ▸ Classical.choose_spec (hnd a ha)) hb
    · rfl

/-- Attainment of the reduced problem. -/
lemma exists_min (α : ℝ) (μ₁ : Distr A) (μ₂ : Distr B) (R' : A → B → Prop)
    (hnd : ∀ a, μ₁.mass a ≠ 0 → ∃ b, R' a b) :
    ∃ K : Ker A B, Feas μ₁ R' K ∧ ∀ K', Feas μ₁ R' K' → J α μ₁ μ₂ K ≤ J α μ₁ μ₂ K' := by
  obtain ⟨K, hK, hmin⟩ := (isCompact_feas μ₁ R').exists_isMinOn (feas_nonempty μ₁ R' hnd)
    (J_continuous α μ₁ μ₂).continuousOn
  exact ⟨K, hK, fun K' hK' => (isMinOn_iff.mp hmin) K' hK'⟩

/-- **First-order condition at the minimizer**: on a source `a` of positive
    mass, every target actually used has density ratio `ν/μ₂` at most that of
    every admissible target. -/
lemma kkt_of_min {α : ℝ} (hα : 1 < α) (hR' : ∀ a b, R' a b → μ₂.mass b ≠ 0)
    (hK : Feas μ₁ R' K) (hmin : ∀ K', Feas μ₁ R' K' → J α μ₁ μ₂ K ≤ J α μ₁ μ₂ K')
    {a : A} {b b' : B} (ha : μ₁.mass a ≠ 0) (hb : R' a b) (hb' : R' a b') (hKab : K a b ≠ 0) :
    nu μ₁ K b / μ₂.mass b ≤ nu μ₁ K b' / μ₂.mass b' := by
  by_cases hbb : b = b'
  · subst hbb; exact le_rfl
  have hα0 : (0:ℝ) < α := by linarith
  -- the perturbed kernels
  set Kt : ℝ≥0∞ → Ker A B := fun t a₁ b₁ =>
    if a₁ = a then (if b₁ = b then K a b - t else if b₁ = b' then K a b' + t else K a b₁)
    else K a₁ b₁ with hKt
  have hKab1 : K a b ≤ 1 := hK.le_one ha b
  have hKab_top : K a b ≠ ⊤ := hK.ne_top ha b
  -- a sum over `univ` splits off `b` and `b'`
  have hsplit : ∀ (g : B → ℝ≥0∞), ∑ b₁, g b₁ =
      ∑ b₁ ∈ (Finset.univ.erase b).erase b', g b₁ + g b' + g b := by
    intro g
    rw [Finset.sum_erase_add _ _ (Finset.mem_erase.mpr ⟨Ne.symm hbb, Finset.mem_univ _⟩),
      Finset.sum_erase_add _ _ (Finset.mem_univ b)]
  have hKt_off : ∀ t a₁ b₁, b₁ ≠ b → b₁ ≠ b' → Kt t a₁ b₁ = K a₁ b₁ := by
    intro t a₁ b₁ h1 h2
    simp only [hKt]
    split_ifs with h <;> [subst h; rfl] <;> rfl
  have hKt_b : ∀ t, Kt t a b = K a b - t := by intro t; simp [hKt]
  have hKt_b' : ∀ t, Kt t a b' = K a b' + t := by
    intro t; simp [hKt, Ne.symm hbb]
  have hKt_a : ∀ t a₁ b₁, a₁ ≠ a → Kt t a₁ b₁ = K a₁ b₁ := by
    intro t a₁ b₁ h; simp [hKt, h]
  -- feasibility of the perturbation
  have hfeas : ∀ t, t ≤ K a b → Feas μ₁ R' (Kt t) := by
    intro t ht a₁ ha₁
    by_cases haa : a₁ = a
    · subst haa
      refine ⟨?_, fun b₁ hb₁ => ?_⟩
      · rw [hsplit, hKt_b, hKt_b', Finset.sum_congr rfl (fun b₁ hb₁ => hKt_off t a₁ b₁
          (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hb₁)) (Finset.ne_of_mem_erase hb₁)),
          ← (hK a₁ ha₁).1, hsplit (K a₁), add_assoc, add_assoc,
          add_tsub_cancel_of_le ht, add_assoc]
      · have h1 : b₁ ≠ b := fun h => hb₁ (h ▸ hb)
        have h2 : b₁ ≠ b' := fun h => hb₁ (h ▸ hb')
        rw [hKt_off t a₁ b₁ h1 h2]
        exact (hK a₁ ha₁).2 b₁ hb₁
    · refine ⟨?_, fun b₁ hb₁ => ?_⟩
      · rw [Finset.sum_congr rfl (fun b₁ _ => hKt_a t a₁ b₁ haa)]; exact (hK a₁ ha₁).1
      · rw [hKt_a t a₁ b₁ haa]; exact (hK a₁ ha₁).2 b₁ hb₁
  -- the image under the perturbation
  have hsplitA : ∀ (g : A → ℝ≥0∞), ∑ a₁, g a₁ = ∑ a₁ ∈ Finset.univ.erase a, g a₁ + g a :=
    fun g => (Finset.sum_erase_add _ _ (Finset.mem_univ a)).symm
  have hnu_off : ∀ t b₁, b₁ ≠ b → b₁ ≠ b' → nu μ₁ (Kt t) b₁ = nu μ₁ K b₁ := by
    intro t b₁ h1 h2
    exact Finset.sum_congr rfl fun a₁ _ => by rw [hKt_off t a₁ b₁ h1 h2]
  have hC : ∀ b₁, nu μ₁ K b₁ = ∑ a₁ ∈ Finset.univ.erase a, μ₁.mass a₁ * K a₁ b₁
      + μ₁.mass a * K a b₁ := fun b₁ => hsplitA _
  have hnuKt_b : ∀ t, nu μ₁ (Kt t) b =
      ∑ a₁ ∈ Finset.univ.erase a, μ₁.mass a₁ * K a₁ b + μ₁.mass a * (K a b - t) := by
    intro t
    rw [nu, hsplitA, hKt_b]
    congr 1
    exact Finset.sum_congr rfl fun a₁ ha₁ => by rw [hKt_a t a₁ b (Finset.ne_of_mem_erase ha₁)]
  have hnuKt_b' : ∀ t, nu μ₁ (Kt t) b' =
      ∑ a₁ ∈ Finset.univ.erase a, μ₁.mass a₁ * K a₁ b' + μ₁.mass a * (K a b' + t) := by
    intro t
    rw [nu, hsplitA, hKt_b']
    congr 1
    exact Finset.sum_congr rfl fun a₁ ha₁ => by rw [hKt_a t a₁ b' (Finset.ne_of_mem_erase ha₁)]
  have hnu_b : ∀ t, t ≤ K a b → nu μ₁ (Kt t) b = nu μ₁ K b - μ₁.mass a * t := by
    intro t ht
    have hst : μ₁.mass a * t ≠ ⊤ :=
      ENNReal.mul_ne_top (μ₁.mass_ne_top a) (ne_top_of_le_ne_top hKab_top ht)
    symm
    refine ENNReal.sub_eq_of_eq_add hst ?_
    rw [hnuKt_b, hC b, add_assoc, ← mul_add, tsub_add_cancel_of_le ht]
  have hnu_b' : ∀ t, nu μ₁ (Kt t) b' = nu μ₁ K b' + μ₁.mass a * t := by
    intro t; rw [hnuKt_b', hC b', mul_add, add_assoc]
  -- the objective under the perturbation
  have hbS : b ∈ Finset.univ.filter (fun b => μ₂.mass b ≠ 0) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hR' a b hb⟩
  have hb'S : b' ∈ (Finset.univ.filter (fun b => μ₂.mass b ≠ 0)).erase b :=
    Finset.mem_erase.mpr ⟨Ne.symm hbb, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hR' a b' hb'⟩⟩
  have hsplitS : ∀ (g : B → ℝ≥0∞), ∑ b₁ ∈ Finset.univ.filter (fun b => μ₂.mass b ≠ 0), g b₁ =
      ∑ b₁ ∈ ((Finset.univ.filter (fun b => μ₂.mass b ≠ 0)).erase b).erase b', g b₁
        + g b' + g b := by
    intro g
    rw [Finset.sum_erase_add _ _ hb'S, Finset.sum_erase_add _ _ hbS]
  set C := ∑ b₁ ∈ ((Finset.univ.filter (fun b => μ₂.mass b ≠ 0)).erase b).erase b',
    nu μ₁ K b₁ ^ α * μ₂.mass b₁ ^ (1 - α) with hCdef
  have hJK : J α μ₁ μ₂ K = C + nu μ₁ K b' ^ α * μ₂.mass b' ^ (1 - α)
      + nu μ₁ K b ^ α * μ₂.mass b ^ (1 - α) := hsplitS _
  have hJKt : ∀ t, t ≤ K a b → J α μ₁ μ₂ (Kt t) =
      C + (nu μ₁ K b' + μ₁.mass a * t) ^ α * μ₂.mass b' ^ (1 - α)
        + (nu μ₁ K b - μ₁.mass a * t) ^ α * μ₂.mass b ^ (1 - α) := by
    intro t ht
    rw [J, hsplitS, hnu_b t ht, hnu_b' t, hCdef]
    congr 2
    refine Finset.sum_congr rfl fun b₁ hb₁ => ?_
    rw [hnu_off t b₁ (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hb₁))
      (Finset.ne_of_mem_erase hb₁)]
  have hCtop : C ≠ ⊤ := by
    refine ne_top_of_le_ne_top (J_ne_top (μ₂ := μ₂) hα hK) ?_
    rw [hJK]; exact le_add_right (le_add_right le_rfl)
  have hmin' : ∀ t, t ≤ K a b →
      nu μ₁ K b ^ α * μ₂.mass b ^ (1 - α) + nu μ₁ K b' ^ α * μ₂.mass b' ^ (1 - α)
        ≤ (nu μ₁ K b - μ₁.mass a * t) ^ α * μ₂.mass b ^ (1 - α)
          + (nu μ₁ K b' + μ₁.mass a * t) ^ α * μ₂.mass b' ^ (1 - α) := by
    intro t ht
    have h := hmin (Kt t) (hfeas t ht)
    rw [hJK, hJKt t ht, add_assoc, add_assoc] at h
    have h' := ENNReal.le_of_add_le_add_left hCtop h
    rwa [add_comm, add_comm ((nu μ₁ K b' + μ₁.mass a * t) ^ α * μ₂.mass b' ^ (1 - α))] at h'
  exact kkt_ennreal hα (nu_ne_top hK b) (nu_ne_top hK b') (hR' a b hb) (μ₂.mass_ne_top b)
    (hR' a b' hb') (μ₂.mass_ne_top b') ha (μ₁.mass_ne_top a) hKab hKab_top
    (single_le_nu b) hmin'

end Finite

/-!
## The certificate: tests read off the minimizer
-/

section Certificate

variable [Fintype A] [Fintype B]
variable {μ₁ : Distr A} {μ₂ : Distr B} {R' : A → B → Prop} {K : Ker A B}

/-- `x * x ^ (α - 1) = x ^ α` for finite nonzero `x`. -/
lemma mul_rpow_sub_one {α : ℝ} {x : ℝ≥0∞} (hx0 : x ≠ 0) (hx : x ≠ ⊤) :
    x * x ^ (α - 1) = x ^ α := by
  calc x * x ^ (α - 1) = x ^ (1:ℝ) * x ^ (α - 1) := by rw [ENNReal.rpow_one]
    _ = x ^ (1 + (α - 1)) := (ENNReal.rpow_add _ _ hx0 hx).symm
    _ = x ^ α := by rw [show (1:ℝ) + (α - 1) = α by ring]

/-- Density ratio of the image against `μ₂`. -/
noncomputable def ratio (μ₁ : Distr A) (μ₂ : Distr B) (K : Ker A B) (b : B) : ℝ≥0∞ :=
  nu μ₁ K b / μ₂.mass b

/-- The admissible targets of a source. -/
noncomputable def targets (R' : A → B → Prop) (a : A) : Finset B :=
  Finset.univ.filter (fun b => R' a b)

lemma mem_targets {a : A} {b : B} (h : R' a b) : b ∈ targets R' a :=
  Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩

/-- The first test: the least density ratio over the targets, to the power `α - 1`. -/
noncomputable def kOne (α : ℝ) (μ₁ : Distr A) (μ₂ : Distr B) (R' : A → B → Prop)
    (K : Ker A B) (a : A) : ℝ≥0∞ :=
  if h : μ₁.mass a ≠ 0 ∧ (targets R' a).Nonempty then
    ((targets R' a).inf' h.2 (ratio μ₁ μ₂ K)) ^ (α - 1) else 0

/-- The second test: the density ratio to the power `α`, infinite off the support. -/
noncomputable def kTwo (α : ℝ) (μ₁ : Distr A) (μ₂ : Distr B) (K : Ker A B) (b : B) : ℝ≥0∞ :=
  if μ₂.mass b ≠ 0 then ratio μ₁ μ₂ K b ^ α else ⊤

lemma kOne_eq_of {α : ℝ} {a : A} (ha : μ₁.mass a ≠ 0) (hne : (targets R' a).Nonempty) :
    kOne α μ₁ μ₂ R' K a = ((targets R' a).inf' hne (ratio μ₁ μ₂ K)) ^ (α - 1) := by
  rw [kOne, dif_pos ⟨ha, hne⟩]

lemma kOne_eq_zero_of {α : ℝ} {a : A} (ha : μ₁.mass a = 0) : kOne α μ₁ μ₂ R' K a = 0 := by
  rw [kOne, dif_neg (fun h => h.1 ha)]

lemma kTwo_eq_of {α : ℝ} {b : B} (hb : μ₂.mass b ≠ 0) :
    kTwo α μ₁ μ₂ K b = ratio μ₁ μ₂ K b ^ α := by
  rw [kTwo, if_pos hb]

lemma kTwo_eq_top_of {α : ℝ} {b : B} (hb : μ₂.mass b = 0) : kTwo α μ₁ μ₂ K b = ⊤ := by
  rw [kTwo, if_neg (not_not.mpr hb)]

lemma ratio_ne_top (hK : Feas μ₁ R' K) {b : B} (hb : μ₂.mass b ≠ 0) :
    ratio μ₁ μ₂ K b ≠ ⊤ := by
  intro h
  rw [ratio, ENNReal.div_eq_top] at h
  rcases h with ⟨_, h⟩ | ⟨h, _⟩
  · exact hb h
  · exact nu_ne_top hK b h

/-- At a used target the ratio attains the infimum over the admissible targets. -/
lemma inf_eq_ratio (hkkt : ∀ a b b', μ₁.mass a ≠ 0 → R' a b → R' a b' → K a b ≠ 0 →
      ratio μ₁ μ₂ K b ≤ ratio μ₁ μ₂ K b')
    {a : A} {b : B} (ha : μ₁.mass a ≠ 0) (hb : R' a b) (hKab : K a b ≠ 0)
    (hne : (targets R' a).Nonempty) :
    (targets R' a).inf' hne (ratio μ₁ μ₂ K) = ratio μ₁ μ₂ K b :=
  le_antisymm (Finset.inf'_le _ (mem_targets hb))
    (Finset.le_inf' hne _ fun b' hb' => hkkt a b b' ha hb (Finset.mem_filter.mp hb').2 hKab)

/-- The certificate tests are admissible. -/
lemma testAdm_cert {α : ℝ} (hα : 1 < α) {R : A → B → Prop}
    (hR'' : ∀ a b, R a b → μ₂.mass b ≠ 0 → R' a b) (hK : Feas μ₁ R' K) :
    TestAdm α R (kOne α μ₁ μ₂ R' K) (kTwo α μ₁ μ₂ K) := by
  intro a b hab
  have h1α : (1:ℝ) - α < 0 := by linarith
  have hα0 : (0:ℝ) < α := by linarith
  by_cases hb : μ₂.mass b ≠ 0
  swap
  · push Not at hb
    rw [kTwo_eq_top_of hb, ENNReal.top_rpow_of_neg h1α, mul_zero]; exact zero_le
  have hRab : R' a b := hR'' a b hab hb
  have hne : (targets R' a).Nonempty := ⟨b, mem_targets hRab⟩
  by_cases ha : μ₁.mass a ≠ 0
  swap
  · push Not at ha
    rw [kOne_eq_zero_of ha, ENNReal.zero_rpow_of_pos hα0, zero_mul]; exact zero_le
  rw [kOne_eq_of ha hne, kTwo_eq_of hb]
  set ρ := ratio μ₁ μ₂ K b with hρ
  have hinf : (targets R' a).inf' hne (ratio μ₁ μ₂ K) ≤ ρ := Finset.inf'_le _ (mem_targets hRab)
  have hρtop : ρ ≠ ⊤ := ratio_ne_top hK hb
  rcases eq_or_ne ρ 0 with hρ0 | hρ0
  · have h0 : (targets R' a).inf' hne (ratio μ₁ μ₂ K) = 0 :=
      le_antisymm (hρ0 ▸ hinf) zero_le
    rw [h0, ENNReal.zero_rpow_of_pos (by linarith), ENNReal.zero_rpow_of_pos hα0, zero_mul]
    exact zero_le
  · calc (((targets R' a).inf' hne (ratio μ₁ μ₂ K)) ^ (α - 1)) ^ α * (ρ ^ α) ^ (1 - α)
        ≤ (ρ ^ (α - 1)) ^ α * (ρ ^ α) ^ (1 - α) :=
          mul_le_mul' (ENNReal.rpow_le_rpow (ENNReal.rpow_le_rpow hinf (by linarith)) hα0.le)
            le_rfl
      _ = ρ ^ ((α - 1) * α + α * (1 - α)) := by
          rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul, ← ENNReal.rpow_add _ _ hρ0 hρtop]
      _ = 1 := by rw [show (α - 1) * α + α * (1 - α) = 0 by ring, ENNReal.rpow_zero]

/-- The first test expectation equals the optimum. -/
lemma sum_kOne {α : ℝ} (hα : 1 < α) (hR' : ∀ a b, R' a b → μ₂.mass b ≠ 0) (hK : Feas μ₁ R' K)
    (hnd : ∀ a, μ₁.mass a ≠ 0 → (targets R' a).Nonempty)
    (hkkt : ∀ a b b', μ₁.mass a ≠ 0 → R' a b → R' a b' → K a b ≠ 0 →
      ratio μ₁ μ₂ K b ≤ ratio μ₁ μ₂ K b') :
    ∑ a, kOne α μ₁ μ₂ R' K a * μ₁.mass a = J α μ₁ μ₂ K := by
  have hα0 : (0:ℝ) < α := by linarith
  have h1 : ∀ a, kOne α μ₁ μ₂ R' K a * μ₁.mass a
      = ∑ b, μ₁.mass a * K a b * ratio μ₁ μ₂ K b ^ (α - 1) := by
    intro a
    by_cases ha : μ₁.mass a ≠ 0
    · calc kOne α μ₁ μ₂ R' K a * μ₁.mass a
          = μ₁.mass a * (∑ b, K a b) * ((targets R' a).inf' (hnd a ha) (ratio μ₁ μ₂ K)) ^ (α - 1) := by
            rw [kOne_eq_of ha (hnd a ha), (hK a ha).1, mul_one, mul_comm]
        _ = ∑ b, μ₁.mass a * K a b * ((targets R' a).inf' (hnd a ha) (ratio μ₁ μ₂ K)) ^ (α - 1) := by
            rw [Finset.mul_sum, Finset.sum_mul]
        _ = ∑ b, μ₁.mass a * K a b * ratio μ₁ μ₂ K b ^ (α - 1) := by
            refine Finset.sum_congr rfl fun b _ => ?_
            rcases eq_or_ne (K a b) 0 with hKab | hKab
            · rw [hKab, mul_zero, zero_mul, zero_mul]
            · have hRab : R' a b := by
                by_contra hcon; exact hKab ((hK a ha).2 b hcon)
              rw [inf_eq_ratio hkkt ha hRab hKab (hnd a ha)]
    · push Not at ha
      rw [kOne_eq_zero_of ha, zero_mul]
      symm
      exact Finset.sum_eq_zero fun b _ => by rw [ha, zero_mul, zero_mul]
  rw [Finset.sum_congr rfl fun a _ => h1 a, Finset.sum_comm]
  simp_rw [← Finset.sum_mul]
  rw [J, Finset.sum_filter]
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases hb : μ₂.mass b ≠ 0
  · rw [if_pos hb]
    show nu μ₁ K b * ratio μ₁ μ₂ K b ^ (α - 1) = nu μ₁ K b ^ α * μ₂.mass b ^ (1 - α)
    rw [ratio, div_rpow_sub_one hα, ← mul_assoc]
    congr 1
    rcases eq_or_ne (nu μ₁ K b) 0 with h0 | h0
    · rw [h0, zero_mul, ENNReal.zero_rpow_of_pos hα0]
    · exact mul_rpow_sub_one h0 (nu_ne_top hK b)
  · push Not at hb
    rw [if_neg (not_not.mpr hb)]
    show nu μ₁ K b * ratio μ₁ μ₂ K b ^ (α - 1) = 0
    rw [nu_eq_zero_of_not hK (fun a h => hR' a b h hb), zero_mul]

/-- The second test expectation equals the optimum. -/
lemma sum_kTwo {α : ℝ} (hα : 1 < α) (hK : Feas μ₁ R' K) :
    ∑ b, kTwo α μ₁ μ₂ K b * μ₂.mass b = J α μ₁ μ₂ K := by
  have hα0 : (0:ℝ) < α := by linarith
  rw [J, Finset.sum_filter]
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases hb : μ₂.mass b ≠ 0
  · rw [if_pos hb, kTwo_eq_of hb, ratio, ENNReal.div_rpow_of_nonneg _ _ hα0.le, div_eq_mul_inv,
      ← ENNReal.rpow_neg, mul_assoc]
    congr 1
    calc μ₂.mass b ^ (-α) * μ₂.mass b = μ₂.mass b ^ (-α) * μ₂.mass b ^ (1:ℝ) := by
          rw [ENNReal.rpow_one]
      _ = μ₂.mass b ^ (-α + 1) := (ENNReal.rpow_add _ _ hb (μ₂.mass_ne_top b)).symm
      _ = μ₂.mass b ^ (1 - α) := by rw [show -α + 1 = 1 - α by ring]
  · push Not at hb
    rw [if_neg (not_not.mpr hb), kTwo_eq_top_of hb, hb, mul_zero]

/-- The certificate's test value is exactly the optimum. -/
lemma testVal_cert {α : ℝ} (hα : 1 < α) (hR' : ∀ a b, R' a b → μ₂.mass b ≠ 0)
    (hK : Feas μ₁ R' K) (hnd : ∀ a, μ₁.mass a ≠ 0 → (targets R' a).Nonempty)
    (hkkt : ∀ a b b', μ₁.mass a ≠ 0 → R' a b → R' a b' → K a b ≠ 0 →
      ratio μ₁ μ₂ K b ≤ ratio μ₁ μ₂ K b') :
    testVal α μ₁ μ₂ (kOne α μ₁ μ₂ R' K) (kTwo α μ₁ μ₂ K) = J α μ₁ μ₂ K := by
  have hα0 : (0:ℝ) < α := by linarith
  rw [testVal, tsum_fintype, tsum_fintype, sum_kOne hα hR' hK hnd hkkt, sum_kTwo hα hK]
  rcases eq_or_ne (J α μ₁ μ₂ K) 0 with h0 | h0
  · rw [h0, ENNReal.zero_rpow_of_pos hα0, zero_mul]
  · rw [← ENNReal.rpow_add _ _ h0 (J_ne_top (μ₂ := μ₂) hα hK), show α + (1 - α) = 1 by ring,
      ENNReal.rpow_one]

end Certificate

end Distr

end DStd
