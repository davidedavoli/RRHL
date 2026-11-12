import Xhl.Duality.Discrete.RenyiDuality
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Instances.ENNReal.Lemmas

open ENNReal Classical Filter Topology

namespace DStd


/-!
# Discrete strong duality for the Rényi lifting

`flift_mul_iff_codLift_gen`: for discrete sub-distributions on arbitrary types `A`, `B`,
under the partner conditions, the two-witness lifting `FLiftMul` coincides with the
witness-free lifting `CodLiftMul`.  It is the discrete step of Theorem C.1
(`Xhl/Duality/DualityContStd.lean`).

The proof approximates by finite subproblems indexed by pairs `(E, G)` of finite
sets: the source is restricted to `E`, and the target is `G` plus one point
collecting the mass of `μ₂` outside `G`.  Witness-free bounds transfer to each
subproblem (`codLift_res`), the finite certificate (`RenyiDuality.lean`) gives a kernel
there with budget `η`, and the kernels are extended by zero to `A → B → ℝ≥0∞`.
A limit along an ultrafilter finer than `atTop` exists by compactness of the
kernel space.  Two facts pass to the limit:

* **no mass escapes** (`extK_tight`): a row of the kernel loses at most
  `(η · μ₂(Fᶜ)^{α−1})^{1/α}` outside a finite set `F`, the grouped form of the
  Hellinger bound, and this tends to `0` as `F` grows;
* **the budget survives** (`Jm_lsc`): the reduced objective is lower
  semicontinuous in the kernel.

The limit kernel then yields the two witnesses (`flift_of_kernel`).
-/

open ENNReal Classical Distr Range Filter Topology

namespace Distr

variable {A B : Type}

/-!
## Witnesses from a kernel (arbitrary types)
-/

section Kernel

/-- Feasible kernels: on every source of positive mass, a probability vector
    supported in `R'`. -/
def FeasC (μ₁ : Distr A) (R' : A → B → Prop) (K : A → B → ℝ≥0∞) : Prop :=
  ∀ a, μ₁.mass a ≠ 0 → (∑' b, K a b = 1) ∧ ∀ b, ¬ R' a b → K a b = 0

/-- The image of `μ₁` under the kernel. -/
noncomputable def nuC (μ₁ : Distr A) (K : A → B → ℝ≥0∞) (b : B) : ℝ≥0∞ :=
  ∑' a, μ₁.mass a * K a b

/-- The reduced objective. -/
noncomputable def JC (α : ℝ) (μ₁ : Distr A) (μ₂ : Distr B) (K : A → B → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' b, nuC μ₁ K b ^ α * μ₂.mass b ^ (1 - α)

/-- The reduced objective restricted to the support of `μ₂` (lower semicontinuous). -/
noncomputable def Jm (α : ℝ) (μ₁ : Distr A) (μ₂ : Distr B) (K : A → B → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' b, if μ₂.mass b ≠ 0 then nuC μ₁ K b ^ α * μ₂.mass b ^ (1 - α) else 0

variable {μ₁ : Distr A} {μ₂ : Distr B} {R' : A → B → Prop} {K : A → B → ℝ≥0∞}

lemma FeasC.row_mul (hK : FeasC μ₁ R' K) (a : A) : μ₁.mass a * ∑' b, K a b = μ₁.mass a := by
  rcases eq_or_ne (μ₁.mass a) 0 with ha | ha
  · rw [ha, zero_mul]
  · rw [(hK a ha).1, mul_one]

lemma FeasC.ne_top (hK : FeasC μ₁ R' K) {a : A} (ha : μ₁.mass a ≠ 0) (b : B) : K a b ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top ((hK a ha).1 ▸ ENNReal.le_tsum b)

lemma tsum_nuC_le (hK : FeasC μ₁ R' K) : ∑' b, nuC μ₁ K b ≤ 1 := by
  unfold nuC
  rw [ENNReal.tsum_comm]
  calc ∑' a, ∑' b, μ₁.mass a * K a b = ∑' a, μ₁.mass a :=
        tsum_congr fun a => by rw [ENNReal.tsum_mul_left, hK.row_mul a]
    _ ≤ 1 := μ₁.le_one

lemma nuC_ne_top (hK : FeasC μ₁ R' K) (b : B) : nuC μ₁ K b ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top ((ENNReal.le_tsum b).trans (tsum_nuC_le hK))

lemma nuC_eq_zero_of_not (hK : FeasC μ₁ R' K) {b : B} (hb : ∀ a, ¬ R' a b) :
    nuC μ₁ K b = 0 := by
  refine ENNReal.tsum_eq_zero.mpr fun a => ?_
  rcases eq_or_ne (μ₁.mass a) 0 with ha | ha
  · rw [ha, zero_mul]
  · rw [(hK a ha).2 b (hb a), mul_zero]

/-- Left witness: `μ₁ ⊗ K`. -/
noncomputable def wLeftC (μ₁ : Distr A) (R' : A → B → Prop) (K : A → B → ℝ≥0∞)
    (hK : FeasC μ₁ R' K) : Distr (A × B) where
  mass p := μ₁.mass p.1 * K p.1 p.2
  le_one := by
    have h : ∑' p : A × B, μ₁.mass p.1 * K p.1 p.2 = ∑' a, μ₁.mass a := by
      rw [ENNReal.tsum_prod']
      exact tsum_congr fun a => by
        show ∑' b, μ₁.mass a * K a b = μ₁.mass a
        rw [ENNReal.tsum_mul_left, hK.row_mul a]
    rw [h]; exact μ₁.le_one

/-- Right witness mass: `μ₂` disintegrated along the left witness, with a partner
    Dirac where the image vanishes. -/
noncomputable def wRightMassC (μ₁ : Distr A) (μ₂ : Distr B) (K : A → B → ℝ≥0∞)
    {R : A → B → Prop} (hp₂ : ∀ b, μ₂.mass b ≠ 0 → ∃ a, R a b) (p : A × B) : ℝ≥0∞ :=
  if h : μ₂.mass p.2 ≠ 0 then
    μ₂.mass p.2 * (if nuC μ₁ K p.2 ≠ 0 then μ₁.mass p.1 * K p.1 p.2 / nuC μ₁ K p.2
      else if p.1 = Classical.choose (hp₂ p.2 h) then 1 else 0)
  else 0

lemma wRightMassC_sum (hK : FeasC μ₁ R' K) {R : A → B → Prop}
    (hp₂ : ∀ b, μ₂.mass b ≠ 0 → ∃ a, R a b) (b : B) :
    ∑' a, wRightMassC μ₁ μ₂ K hp₂ (a, b) = μ₂.mass b := by
  by_cases hb : μ₂.mass b ≠ 0
  · simp only [wRightMassC, dif_pos hb, ENNReal.tsum_mul_left]
    rcases eq_or_ne (nuC μ₁ K b) 0 with hν | hν
    · simp only [if_neg (not_not.mpr hν)]
      rw [tsum_ite_eq (Classical.choose (hp₂ b hb)) (fun _ => (1 : ℝ≥0∞)), mul_one]
    · simp only [if_pos hν, div_eq_mul_inv]
      rw [ENNReal.tsum_mul_right]
      show μ₂.mass b * (nuC μ₁ K b * (nuC μ₁ K b)⁻¹) = μ₂.mass b
      rw [ENNReal.mul_inv_cancel hν (nuC_ne_top hK b), mul_one]
  · push Not at hb
    rw [hb]
    exact ENNReal.tsum_eq_zero.mpr fun a => by simp [wRightMassC, hb]

/-- Right witness. -/
noncomputable def wRightC (μ₁ : Distr A) (μ₂ : Distr B) (R' : A → B → Prop)
    (K : A → B → ℝ≥0∞) (hK : FeasC μ₁ R' K) {R : A → B → Prop}
    (hp₂ : ∀ b, μ₂.mass b ≠ 0 → ∃ a, R a b) : Distr (A × B) where
  mass := wRightMassC μ₁ μ₂ K hp₂
  le_one := by
    rw [ENNReal.tsum_prod', ENNReal.tsum_comm]
    calc ∑' b, ∑' a, wRightMassC μ₁ μ₂ K hp₂ (a, b) = ∑' b, μ₂.mass b :=
          tsum_congr fun b => wRightMassC_sum hK hp₂ b
      _ ≤ 1 := μ₂.le_one

lemma wLeftC_fst (hK : FeasC μ₁ R' K) : (wLeftC μ₁ R' K hK).fst = μ₁ := by
  ext a
  rw [fst_mass]
  show ∑' b, μ₁.mass a * K a b = μ₁.mass a
  rw [ENNReal.tsum_mul_left, hK.row_mul a]

lemma wRightC_snd (hK : FeasC μ₁ R' K) {R : A → B → Prop}
    (hp₂ : ∀ b, μ₂.mass b ≠ 0 → ∃ a, R a b) : (wRightC μ₁ μ₂ R' K hK hp₂).snd = μ₂ := by
  ext b
  rw [snd_mass]
  exact wRightMassC_sum hK hp₂ b

lemma wLeftC_range (hK : FeasC μ₁ R' K) {R : A → B → Prop} (hR'R : ∀ a b, R' a b → R a b) :
    range (fun p : A × B => R p.1 p.2) (wLeftC μ₁ R' K hK) := by
  intro p hp
  have h := mul_ne_zero_iff.mp hp
  refine hR'R _ _ ?_
  by_contra hcon
  exact h.2 ((hK p.1 h.1).2 p.2 hcon)

lemma wRightC_range (hK : FeasC μ₁ R' K) {R : A → B → Prop} (hR'R : ∀ a b, R' a b → R a b)
    (hp₂ : ∀ b, μ₂.mass b ≠ 0 → ∃ a, R a b) :
    range (fun p : A × B => R p.1 p.2) (wRightC μ₁ μ₂ R' K hK hp₂) := by
  rintro ⟨a, b⟩ hp
  change wRightMassC μ₁ μ₂ K hp₂ (a, b) ≠ 0 at hp
  simp only [wRightMassC] at hp
  split_ifs at hp with hb hν hc
  · have h := (mul_ne_zero_iff.mp hp).2
    have h' : μ₁.mass a * K a b ≠ 0 := fun h0 => h (by rw [h0, ENNReal.zero_div])
    have h'' := mul_ne_zero_iff.mp h'
    refine hR'R _ _ ?_
    by_contra hcon
    exact h''.2 ((hK a h''.1).2 b hcon)
  · exact hc ▸ Classical.choose_spec (hp₂ b hb)
  · exact absurd (mul_zero (μ₂.mass b)) hp
  · exact absurd rfl hp

/-- The Hellinger integral of the two witnesses is the reduced objective. -/
lemma hRen_witnessesC {α : ℝ} (hα : 1 < α) (hK : FeasC μ₁ R' K) {R : A → B → Prop}
    (hp₂ : ∀ b, μ₂.mass b ≠ 0 → ∃ a, R a b) :
    hRen α (wLeftC μ₁ R' K hK) (wRightC μ₁ μ₂ R' K hK hp₂) = JC α μ₁ μ₂ K := by
  have hα0 : (0:ℝ) < α := by linarith
  have h1α : (1:ℝ) - α < 0 := by linarith
  rw [hRen, ENNReal.tsum_prod', ENNReal.tsum_comm, JC]
  refine tsum_congr fun b => ?_
  change ∑' a, (μ₁.mass a * K a b) ^ α * wRightMassC μ₁ μ₂ K hp₂ (a, b) ^ (1 - α)
    = nuC μ₁ K b ^ α * μ₂.mass b ^ (1 - α)
  rcases eq_or_ne (nuC μ₁ K b) 0 with hν | hν
  · have hall : ∀ a, μ₁.mass a * K a b = 0 := ENNReal.tsum_eq_zero.mp hν
    rw [hν, ENNReal.zero_rpow_of_pos hα0, zero_mul]
    exact ENNReal.tsum_eq_zero.mpr fun a => by
      rw [hall a, ENNReal.zero_rpow_of_pos hα0, zero_mul]
  have hνtop : nuC μ₁ K b ≠ ⊤ := nuC_ne_top hK b
  by_cases hb : μ₂.mass b ≠ 0
  swap
  · push Not at hb
    obtain ⟨a, ha⟩ : ∃ a, μ₁.mass a * K a b ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hν (ENNReal.tsum_eq_zero.mpr hcon)
    have hw2 : ∀ a, wRightMassC μ₁ μ₂ K hp₂ (a, b) = 0 := fun a => by
      simp [wRightMassC, hb]
    rw [hb, ENNReal.zero_rpow_of_neg h1α,
      ENNReal.mul_top (rpow_ne_zero_of_ne_zero_of_ne_top hν hνtop _)]
    refine ENNReal.tsum_eq_top_of_eq_top ⟨a, ?_⟩
    rw [hw2 a, ENNReal.zero_rpow_of_neg h1α,
      ENNReal.mul_top (rpow_ne_zero_of_ne_zero_of_ne_top ha
        (ENNReal.mul_ne_top (μ₁.mass_ne_top a) (hK.ne_top (mul_ne_zero_iff.mp ha).1 b)) _)]
  set c := μ₂.mass b / nuC μ₁ K b with hc
  have hctop : c ≠ ⊤ := by
    intro h
    rw [hc, ENNReal.div_eq_top] at h
    rcases h with ⟨_, h⟩ | ⟨h, _⟩
    · exact hν h
    · exact μ₂.mass_ne_top b h
  have hw2 : ∀ a, wRightMassC μ₁ μ₂ K hp₂ (a, b) = c * (μ₁.mass a * K a b) := by
    intro a
    simp only [wRightMassC, dif_pos hb, if_pos hν, hc]
    rw [div_eq_mul_inv, div_eq_mul_inv]; ring
  have hterm : ∀ a, (μ₁.mass a * K a b) ^ α * wRightMassC μ₁ μ₂ K hp₂ (a, b) ^ (1 - α)
      = μ₁.mass a * K a b * c ^ (1 - α) := by
    intro a
    rw [hw2 a]
    rcases eq_or_ne (μ₁.mass a * K a b) 0 with h0 | h0
    · rw [h0, ENNReal.zero_rpow_of_pos hα0, zero_mul, zero_mul]
    · have htop : μ₁.mass a * K a b ≠ ⊤ :=
        ENNReal.mul_ne_top (μ₁.mass_ne_top a) (hK.ne_top (mul_ne_zero_iff.mp h0).1 b)
      rw [ENNReal.mul_rpow_of_ne_top hctop htop, mul_comm (c ^ (1 - α)), ← mul_assoc,
        ← ENNReal.rpow_add _ _ h0 htop, show α + (1 - α) = 1 by ring, ENNReal.rpow_one]
  rw [tsum_congr hterm, ENNReal.tsum_mul_right]
  show nuC μ₁ K b * c ^ (1 - α) = nuC μ₁ K b ^ α * μ₂.mass b ^ (1 - α)
  have hcinv : c = (nuC μ₁ K b / μ₂.mass b)⁻¹ := by
    rw [hc, ENNReal.inv_div (Or.inl (μ₂.mass_ne_top b)) (Or.inl hb)]
  rw [hcinv, ENNReal.inv_rpow, ← ENNReal.rpow_neg, show -(1 - α) = α - 1 by ring,
    div_rpow_sub_one hα, ← mul_assoc, mul_rpow_sub_one hν hνtop]

/-- **Witnesses from a feasible kernel**: a kernel supported in `R' ⊆ R`, with
    reduced objective at most `η`, gives the two-witness lifting at `η`. -/
theorem flift_of_kernel {α : ℝ} (hα : 1 < α) {R : A → B → Prop} {η : ℝ≥0∞}
    (hK : FeasC μ₁ R' K) (hR'R : ∀ a b, R' a b → R a b)
    (hp₂ : ∀ b, μ₂.mass b ≠ 0 → ∃ a, R a b) (hJ : JC α μ₁ μ₂ K ≤ η) :
    FLiftMul α R η μ₁ μ₂ :=
  ⟨(wLeftC μ₁ R' K hK, wRightC μ₁ μ₂ R' K hK hp₂), wLeftC_fst hK, wRightC_snd hK hp₂,
    wLeftC_range hK hR'R, wRightC_range hK hR'R hp₂,
    by rw [hRen_witnessesC hα hK hp₂]; exact hJ⟩

/-- On kernels supported in the support of `μ₂`, the two objectives agree. -/
lemma JC_eq_Jm {α : ℝ} (hα : 1 < α) (hK : FeasC μ₁ R' K)
    (hR' : ∀ a b, R' a b → μ₂.mass b ≠ 0) : JC α μ₁ μ₂ K = Jm α μ₁ μ₂ K := by
  refine tsum_congr fun b => ?_
  by_cases hb : μ₂.mass b ≠ 0
  · rw [if_pos hb]
  · rw [if_neg hb]
    push Not at hb
    rw [nuC_eq_zero_of_not hK (fun a h => hR' a b h hb),
      ENNReal.zero_rpow_of_pos (by linarith), zero_mul]

/-- The objective restricted to the support of `μ₂` is lower semicontinuous in
    the kernel (product topology). -/
lemma Jm_lsc {α : ℝ} (hα : 1 < α) (μ₁ : Distr A) (μ₂ : Distr B) :
    LowerSemicontinuous (Jm α μ₁ μ₂) := by
  unfold Jm
  refine lowerSemicontinuous_tsum fun b => ?_
  by_cases hb : μ₂.mass b ≠ 0
  · have hν : LowerSemicontinuous fun K : A → B → ℝ≥0∞ => nuC μ₁ K b :=
      lowerSemicontinuous_tsum fun a =>
        ((ENNReal.continuous_const_mul (μ₁.mass_ne_top a)).comp
          ((continuous_apply b).comp (continuous_apply a))).lowerSemicontinuous
    have hc : μ₂.mass b ^ (1 - α) ≠ ⊤ :=
      rpow_ne_top_of_ne_zero_of_ne_top hb (μ₂.mass_ne_top b) _
    have hg : Continuous fun x : ℝ≥0∞ => x ^ α * μ₂.mass b ^ (1 - α) :=
      (ENNReal.continuous_mul_const hc).comp ENNReal.continuous_rpow_const
    have hmono : Monotone fun x : ℝ≥0∞ => x ^ α * μ₂.mass b ^ (1 - α) :=
      fun x y hxy => mul_le_mul' (ENNReal.rpow_le_rpow hxy (by linarith)) le_rfl
    convert hg.comp_lowerSemicontinuous hν hmono using 1
    funext K
    exact if_pos hb
  · convert (lowerSemicontinuous_const : LowerSemicontinuous fun _ : A → B → ℝ≥0∞ => (0 : ℝ≥0∞))
      using 1
    funext K
    exact if_neg hb

end Kernel

/-!
## The degenerate cases
-/

/-- A source of positive mass whose partners all have zero `μ₂`-mass forces an
    infinite budget. -/
lemma eta_top_of_degenerate {α : ℝ} (hα : 1 < α) {R : A → B → Prop} {η : ℝ≥0∞}
    {μ₁ : Distr A} {μ₂ : Distr B} (h : CodLiftMul α R η μ₁ μ₂) {a₀ : A}
    (ha₀ : μ₁.mass a₀ ≠ 0) (hbad : ∀ b, R a₀ b → μ₂.mass b = 0) : η = ⊤ := by
  have hα0 : (0:ℝ) < α := by linarith
  have h1α : (1:ℝ) - α < 0 := by linarith
  refine top_le_iff.mp ?_
  set k₁ : A → ℝ≥0∞ := fun a => if a = a₀ then ⊤ else 0 with hk₁
  set k₂ : B → ℝ≥0∞ := fun b => if R a₀ b then ⊤ else 1 with hk₂
  have hadm : TestAdm α R k₁ k₂ := by
    intro a b hab
    by_cases ha : a = a₀
    · subst ha
      simp only [hk₁, hk₂, if_pos rfl, if_pos hab]
      rw [ENNReal.top_rpow_of_neg h1α, mul_zero]; exact zero_le
    · simp only [hk₁, if_neg ha]
      rw [ENNReal.zero_rpow_of_pos hα0, zero_mul]; exact zero_le
  have hL : ∑' a, k₁ a * μ₁.mass a = ⊤ := by
    refine top_le_iff.mp (le_trans ?_ (ENNReal.le_tsum a₀))
    simp only [hk₁, if_pos rfl]
    rw [ENNReal.top_mul ha₀]
  have hR : ∑' b, k₂ b * μ₂.mass b = ∑' b, μ₂.mass b := by
    refine tsum_congr fun b => ?_
    by_cases hb : R a₀ b
    · simp only [hk₂, if_pos hb]
      rw [hbad b hb, mul_zero]
    · simp only [hk₂, if_neg hb, one_mul]
  have hW : (∑' b, μ₂.mass b) ^ (1 - α) ≠ 0 := by
    intro h0
    rw [ENNReal.rpow_eq_zero_iff] at h0
    rcases h0 with ⟨_, h⟩ | ⟨h, _⟩
    · linarith
    · exact (ne_top_of_le_ne_top ENNReal.one_ne_top μ₂.le_one) h
  have := h k₁ k₂ hadm
  rwa [testVal, hL, hR, ENNReal.top_rpow_of_pos hα0, ENNReal.top_mul hW] at this

/-- At an infinite budget the lifting holds under the partner conditions. -/
lemma flift_top {α : ℝ} (hα : 1 < α) {R : A → B → Prop} {μ₁ : Distr A} {μ₂ : Distr B}
    (hp₁ : ∀ a, μ₁.mass a ≠ 0 → ∃ b, R a b) (hp₂ : ∀ b, μ₂.mass b ≠ 0 → ∃ a, R a b) :
    FLiftMul α R ⊤ μ₁ μ₂ := by
  set K : A → B → ℝ≥0∞ := fun a b =>
    if h : μ₁.mass a ≠ 0 then (if b = Classical.choose (hp₁ a h) then 1 else 0) else 0 with hKdef
  have hK : FeasC μ₁ R K := by
    intro a ha
    refine ⟨?_, fun b hb => ?_⟩
    · simp only [hKdef, dif_pos ha]
      exact tsum_ite_eq (Classical.choose (hp₁ a ha)) (fun _ => (1 : ℝ≥0∞))
    · simp only [hKdef, dif_pos ha]
      split_ifs with hbe
      · exact absurd (hbe ▸ Classical.choose_spec (hp₁ a ha)) hb
      · rfl
  exact flift_of_kernel hα hK (fun _ _ h => h) hp₂ le_top

/-!
## Finite subproblems
-/

section Finite

/-- The finite certificate, as a kernel: under the source partner condition, the
    witness-free bound gives a feasible kernel with objective at most `η`. -/
lemma exists_ker_of_codLift [Fintype A] [Fintype B] {α : ℝ} (hα : 1 < α)
    {R : A → B → Prop} {η : ℝ≥0∞} {μ₁ : Distr A} {μ₂ : Distr B}
    (hnd : ∀ a, μ₁.mass a ≠ 0 → ∃ b, R a b ∧ μ₂.mass b ≠ 0)
    (h : CodLiftMul α R η μ₁ μ₂) :
    ∃ K : Ker A B, Feas μ₁ (fun a b => R a b ∧ μ₂.mass b ≠ 0) K ∧ J α μ₁ μ₂ K ≤ η := by
  set R' : A → B → Prop := fun a b => R a b ∧ μ₂.mass b ≠ 0 with hR'def
  have hR' : ∀ a b, R' a b → μ₂.mass b ≠ 0 := fun _ _ h => h.2
  have hR'' : ∀ a b, R a b → μ₂.mass b ≠ 0 → R' a b := fun _ _ h1 h2 => ⟨h1, h2⟩
  obtain ⟨K, hK, hmin⟩ := exists_min α μ₁ μ₂ R' hnd
  have hkkt : ∀ a b b', μ₁.mass a ≠ 0 → R' a b → R' a b' → K a b ≠ 0 →
      ratio μ₁ μ₂ K b ≤ ratio μ₁ μ₂ K b' :=
    fun a b b' ha hb hb' hKab => kkt_of_min hα hR' hK hmin ha hb hb' hKab
  have htargets : ∀ a, μ₁.mass a ≠ 0 → (targets R' a).Nonempty := fun a ha =>
    let ⟨b, hb⟩ := hnd a ha; ⟨b, mem_targets hb⟩
  have hval := h _ _ (testAdm_cert hα hR'' hK)
  rw [testVal_cert hα hR' hK htargets hkkt] at hval
  exact ⟨K, hK, hval⟩

/-- **Tightness, finite form**: a row loses at most `(η · μ₂(Pᶜ)^{α−1})^{1/α}` of
    its mass outside `P`. -/
lemma tight_fin [Fintype A] [Fintype B] {α : ℝ} (hα : 1 < α) {μ₁ : Distr A} {μ₂ : Distr B}
    {R' : A → B → Prop} {K : Ker A B} {η : ℝ≥0∞}
    (hR' : ∀ a b, R' a b → μ₂.mass b ≠ 0) (hK : Feas μ₁ R' K) (hJ : J α μ₁ μ₂ K ≤ η)
    (P : B → Prop) {a : A} (ha : μ₁.mass a ≠ 0) :
    μ₁.mass a ≤ μ₁.mass a * ∑ b, (if P b then K a b else 0)
      + (η * (∑ b, if P b then 0 else μ₂.mass b) ^ (α - 1)) ^ (1 / α) := by
  have hα0 : (0:ℝ) < α := by linarith
  set x := ∑ b, (if P b then 0 else nu μ₁ K b) with hx
  set y := ∑ b, (if P b then 0 else μ₂.mass b) with hy
  have hrow : μ₁.mass a = μ₁.mass a * ∑ b, (if P b then K a b else 0)
      + μ₁.mass a * ∑ b, (if P b then 0 else K a b) := by
    rw [← mul_add, ← Finset.sum_add_distrib]
    conv_lhs => rw [← mul_one (μ₁.mass a), ← (hK a ha).1]
    congr 1
    refine Finset.sum_congr rfl fun b _ => ?_
    split_ifs <;> simp
  have hS : μ₁.mass a * ∑ b, (if P b then 0 else K a b) ≤ x := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun b _ => ?_
    split_ifs
    · simp
    · exact single_le_nu b
  have hxθ : x ≤ (η * y ^ (α - 1)) ^ (1 / α) := by
    rcases eq_or_ne y 0 with hy0 | hy0
    · have hx0 : x = 0 := by
        refine Finset.sum_eq_zero fun b _ => ?_
        split_ifs with hPb
        · rfl
        · have hb0 : μ₂.mass b = 0 := by
            have h0 := (Finset.sum_eq_zero_iff.mp hy0) b (Finset.mem_univ b)
            rwa [if_neg hPb] at h0
          exact nu_eq_zero_of_not hK fun a' h => hR' a' b h hb0
      rw [hx0]; exact zero_le
    · have hytop : y ≠ ⊤ := by
        refine ne_top_of_le_ne_top ENNReal.one_ne_top
          (le_trans (Finset.sum_le_sum fun b _ => ?_) (sum_mass_le_one μ₂))
        split_ifs
        · exact zero_le
        · exact le_rfl
      have hsup : x ^ α * y ^ (1 - α) ≤ η := by
        have h1 := tsum_rpow_mul_rpow_le (fun b => if P b then 0 else nu μ₁ K b)
          (fun b => if P b then 0 else μ₂.mass b) hα
        simp only [tsum_fintype] at h1
        refine le_trans h1 (le_trans ?_ hJ)
        rw [J_eq_Jfull hα hR' hK, Jfull]
        refine Finset.sum_le_sum fun b _ => ?_
        split_ifs
        · rw [ENNReal.zero_rpow_of_pos hα0, zero_mul]; exact zero_le
        · exact le_rfl
      have hxα : x ^ α ≤ η * y ^ (α - 1) := by
        calc x ^ α = x ^ α * y ^ (1 - α) * y ^ (α - 1) := by
              rw [mul_assoc, ← ENNReal.rpow_add _ _ hy0 hytop,
                show (1 - α) + (α - 1) = 0 by ring, ENNReal.rpow_zero, mul_one]
          _ ≤ η * y ^ (α - 1) := mul_le_mul' hsup le_rfl
      calc x = (x ^ α) ^ (1 / α) := by
            rw [← ENNReal.rpow_mul, mul_one_div_cancel hα0.ne', ENNReal.rpow_one]
        _ ≤ (η * y ^ (α - 1)) ^ (1 / α) :=
            ENNReal.rpow_le_rpow hxα (one_div_pos.mpr hα0).le
  calc μ₁.mass a = _ := hrow
    _ ≤ μ₁.mass a * ∑ b, (if P b then K a b else 0) + x := add_le_add le_rfl hS
    _ ≤ _ := add_le_add le_rfl hxθ

end Finite

/-- The mass of `μ₂` outside a finite set. -/
noncomputable def tailB (μ₂ : Distr B) (G : Finset B) : ℝ≥0∞ :=
  ∑' b, if b ∈ G then 0 else μ₂.mass b

lemma sum_add_tail (f : B → ℝ≥0∞) (G : Finset B) :
    ∑ b ∈ G, f b + ∑' b, (if b ∈ G then 0 else f b) = ∑' b, f b := by
  have h1 : ∑' b, (if b ∈ G then f b else 0) = ∑ b ∈ G, f b := by
    rw [tsum_eq_sum (s := G) (fun b hb => if_neg hb)]
    exact Finset.sum_congr rfl fun b hb => if_pos hb
  rw [← h1, ← ENNReal.tsum_add]
  exact tsum_congr fun b => by split_ifs <;> simp

/-- Restriction of the source to a finite set. -/
noncomputable def resA (μ₁ : Distr A) (E : Finset A) : Distr E where
  mass x := μ₁.mass x.1
  le_one := le_trans (ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective μ₁.mass)
    μ₁.le_one

/-- The target restricted to a finite set, with the remaining mass collected at
    the extra point `none`. -/
noncomputable def colB (μ₂ : Distr B) (G : Finset B) : Distr (Option G) where
  mass o := o.elim (tailB μ₂ G) (fun b => μ₂.mass b.1)
  le_one := by
    rw [tsum_fintype, Fintype.sum_option]
    show tailB μ₂ G + ∑ b : G, μ₂.mass b.1 ≤ 1
    rw [Finset.sum_coe_sort G μ₂.mass, add_comm, tailB, sum_add_tail]
    exact μ₂.le_one

/-- The relation of the finite subproblem: `none` stands for every target outside `G`. -/
def relEG (R : A → B → Prop) (E : Finset A) (G : Finset B) (x : E) (o : Option G) : Prop :=
  o.elim (∃ b, b ∉ G ∧ R x.1 b) (fun b => R x.1 b.1)

lemma hnd_res {R : A → B → Prop} {μ₁ : Distr A} {μ₂ : Distr B}
    (hnd : ∀ a, μ₁.mass a ≠ 0 → ∃ b, R a b ∧ μ₂.mass b ≠ 0) (E : Finset A) (G : Finset B) :
    ∀ x : E, (resA μ₁ E).mass x ≠ 0 →
      ∃ o, relEG R E G x o ∧ (colB μ₂ G).mass o ≠ 0 := by
  intro x hx
  obtain ⟨b, hRb, hb⟩ := hnd x.1 hx
  by_cases hbG : b ∈ G
  · exact ⟨some ⟨b, hbG⟩, hRb, hb⟩
  · refine ⟨none, ⟨b, hbG, hRb⟩, ?_⟩
    show tailB μ₂ G ≠ 0
    intro h0
    have h1 := (ENNReal.tsum_eq_zero.mp h0) b
    rw [if_neg hbG] at h1
    exact hb h1

/-- The witness-free bound transfers to every finite subproblem. -/
lemma codLift_res {α : ℝ} (hα : 1 < α) {R : A → B → Prop} {η : ℝ≥0∞}
    {μ₁ : Distr A} {μ₂ : Distr B} (h : CodLiftMul α R η μ₁ μ₂) (E : Finset A) (G : Finset B) :
    CodLiftMul α (relEG R E G) η (resA μ₁ E) (colB μ₂ G) := by
  have hα0 : (0:ℝ) < α := by linarith
  intro k₁ k₂ hk
  set k₁' : A → ℝ≥0∞ := fun a => if h : a ∈ E then k₁ ⟨a, h⟩ else 0 with hk₁'
  set k₂' : B → ℝ≥0∞ := fun b => if h : b ∈ G then k₂ (some ⟨b, h⟩) else k₂ none with hk₂'
  have hadm : TestAdm α R k₁' k₂' := by
    intro a b hab
    by_cases ha : a ∈ E
    · by_cases hb : b ∈ G
      · simp only [hk₁', hk₂', dif_pos ha, dif_pos hb]
        exact hk ⟨a, ha⟩ (some ⟨b, hb⟩) hab
      · simp only [hk₁', hk₂', dif_pos ha, dif_neg hb]
        exact hk ⟨a, ha⟩ none ⟨b, hb, hab⟩
    · simp only [hk₁', dif_neg ha]
      rw [ENNReal.zero_rpow_of_pos hα0, zero_mul]; exact zero_le
  have h1 : ∑' a, k₁' a * μ₁.mass a = ∑' x, k₁ x * (resA μ₁ E).mass x := by
    rw [tsum_eq_sum (s := E) (fun a ha => by simp only [hk₁', dif_neg ha, zero_mul]),
      ← Finset.tsum_subtype E (fun a => k₁' a * μ₁.mass a)]
    exact tsum_congr fun x => by simp only [hk₁', dif_pos x.2]; rfl
  have h2 : ∑' b, k₂' b * μ₂.mass b = ∑' o, k₂ o * (colB μ₂ G).mass o := by
    conv_rhs => rw [tsum_fintype, Fintype.sum_option]
    rw [← sum_add_tail (fun b => k₂' b * μ₂.mass b) G]
    have ht : ∑' b, (if b ∈ G then 0 else k₂' b * μ₂.mass b)
        = k₂ none * (colB μ₂ G).mass none := by
      show _ = k₂ none * tailB μ₂ G
      rw [tailB, ← ENNReal.tsum_mul_left]
      refine tsum_congr fun b => ?_
      by_cases hb : b ∈ G
      · simp [hb]
      · simp only [if_neg hb, hk₂', dif_neg hb]
    have hs : ∑ b ∈ G, k₂' b * μ₂.mass b
        = ∑ x : G, k₂ (some x) * (colB μ₂ G).mass (some x) := by
      rw [← Finset.sum_coe_sort G]
      exact Finset.sum_congr rfl fun x _ => by simp only [hk₂', dif_pos x.2]; rfl
    rw [ht, hs]
    exact add_comm _ _
  have := h k₁' k₂' hadm
  unfold testVal at this ⊢
  rwa [h1, h2] at this

/-!
## Extension of a finite kernel by zero
-/

section Ext

variable {μ₁ : Distr A} {μ₂ : Distr B} {R : A → B → Prop} {E : Finset A} {G : Finset B}
  {K' : Ker E (Option G)}

/-- A kernel of the subproblem `(E, G)`, extended by zero (and with rows of zero
    `μ₁`-mass cleared). -/
noncomputable def extK (μ₁ : Distr A) (E : Finset A) (G : Finset B) (K' : Ker E (Option G)) :
    A → B → ℝ≥0∞ :=
  fun a b => if h : (a ∈ E ∧ b ∈ G) ∧ μ₁.mass a ≠ 0 then K' ⟨a, h.1.1⟩ (some ⟨b, h.1.2⟩)
    else 0

lemma extK_of_mem {a : A} {b : B} (ha : a ∈ E) (hb : b ∈ G) (h0 : μ₁.mass a ≠ 0) :
    extK μ₁ E G K' a b = K' ⟨a, ha⟩ (some ⟨b, hb⟩) := by
  unfold extK; rw [dif_pos ⟨⟨ha, hb⟩, h0⟩]

lemma extK_eq_zero {a : A} {b : B} (h : ¬ ((a ∈ E ∧ b ∈ G) ∧ μ₁.mass a ≠ 0)) :
    extK μ₁ E G K' a b = 0 := by
  unfold extK; rw [dif_neg h]

variable (hK' : Feas (resA μ₁ E) (fun x o => relEG R E G x o ∧ (colB μ₂ G).mass o ≠ 0) K')
include hK'

lemma extK_supp {a : A} {b : B} (ha : μ₁.mass a ≠ 0) (hn : ¬ (R a b ∧ μ₂.mass b ≠ 0)) :
    extK μ₁ E G K' a b = 0 := by
  by_cases h : (a ∈ E ∧ b ∈ G) ∧ μ₁.mass a ≠ 0
  · rw [extK_of_mem h.1.1 h.1.2 ha]
    exact (hK' ⟨a, h.1.1⟩ ha).2 _ hn
  · exact extK_eq_zero h

lemma tsum_extK_le (a : A) : ∑' b, extK μ₁ E G K' a b ≤ 1 := by
  by_cases h : a ∈ E ∧ μ₁.mass a ≠ 0
  · rw [tsum_eq_sum (s := G) (fun b hb => extK_eq_zero (by tauto)), ← Finset.sum_coe_sort G]
    calc ∑ y : G, extK μ₁ E G K' a y = ∑ y : G, K' ⟨a, h.1⟩ (some y) :=
          Finset.sum_congr rfl fun y _ => extK_of_mem h.1 y.2 h.2
      _ ≤ ∑ o, K' ⟨a, h.1⟩ o := by rw [Fintype.sum_option]; exact le_add_self
      _ = 1 := (hK' ⟨a, h.1⟩ h.2).1
  · rw [ENNReal.tsum_eq_zero.mpr fun b => extK_eq_zero (by tauto)]; exact zero_le

omit hK' in
lemma nuC_extK_mem {b : B} (hb : b ∈ G) :
    nuC μ₁ (extK μ₁ E G K') b = nu (resA μ₁ E) K' (some ⟨b, hb⟩) := by
  unfold nuC nu
  rw [tsum_eq_sum (s := E) (fun a ha => by rw [extK_eq_zero (by tauto), mul_zero]),
    ← Finset.sum_coe_sort E]
  refine Finset.sum_congr rfl fun x _ => ?_
  rcases eq_or_ne (μ₁.mass x) 0 with h0 | h0
  · show μ₁.mass x * _ = μ₁.mass x * _
    rw [h0, zero_mul, zero_mul]
  · rw [extK_of_mem x.2 hb h0]; rfl

omit hK' in
lemma nuC_extK_not {b : B} (hb : b ∉ G) : nuC μ₁ (extK μ₁ E G K') b = 0 :=
  ENNReal.tsum_eq_zero.mpr fun a => by rw [extK_eq_zero (by tauto), mul_zero]

lemma Jm_extK_le {α : ℝ} (hα : 1 < α) {η : ℝ≥0∞} (hJ : J α (resA μ₁ E) (colB μ₂ G) K' ≤ η) :
    Jm α μ₁ μ₂ (extK μ₁ E G K') ≤ η := by
  have hα0 : (0:ℝ) < α := by linarith
  rw [Jm, tsum_eq_sum (s := G) (fun b hb => by
      rw [nuC_extK_not hb, ENNReal.zero_rpow_of_pos hα0, zero_mul, ite_self]),
    ← Finset.sum_coe_sort G]
  calc ∑ y : G, (if μ₂.mass y ≠ 0 then nuC μ₁ (extK μ₁ E G K') y ^ α * μ₂.mass y ^ (1 - α)
        else 0)
      ≤ ∑ y : G, nu (resA μ₁ E) K' (some y) ^ α * (colB μ₂ G).mass (some y) ^ (1 - α) := by
        refine Finset.sum_le_sum fun y _ => ?_
        rw [nuC_extK_mem y.2]
        split_ifs
        · exact le_rfl
        · exact zero_le
    _ ≤ Jfull α (resA μ₁ E) (colB μ₂ G) K' := by
        rw [Jfull, Fintype.sum_option]; exact le_add_self
    _ = J α (resA μ₁ E) (colB μ₂ G) K' := (J_eq_Jfull hα (fun _ _ h => h.2) hK').symm
    _ ≤ η := hJ

/-- **Tightness** of the extended kernel: on a finite set `F ⊆ G`, a row keeps all
    its mass up to `(η · μ₂(Fᶜ)^{α−1})^{1/α}`. -/
lemma extK_tight {α : ℝ} (hα : 1 < α) {η : ℝ≥0∞}
    (hJ : J α (resA μ₁ E) (colB μ₂ G) K' ≤ η) {a : A} (ha : μ₁.mass a ≠ 0) (haE : a ∈ E)
    {F : Finset B} (hFG : F ⊆ G) :
    μ₁.mass a ≤ μ₁.mass a * ∑ b ∈ F, extK μ₁ E G K' a b
      + (η * tailB μ₂ F ^ (α - 1)) ^ (1 / α) := by
  have hα0 : (0:ℝ) < α := by linarith
  set P : Option G → Prop := fun o => o.elim False (fun y => y.1 ∈ F) with hP
  have h := tight_fin hα (fun _ _ h => h.2) hK' hJ P (a := ⟨a, haE⟩) ha
  have hPn : ¬ P none := id
  -- the kept mass
  have hs1 : ∑ o, (if P o then K' ⟨a, haE⟩ o else 0) ≤ ∑ b ∈ F, extK μ₁ E G K' a b := by
    rw [Fintype.sum_option, if_neg hPn, zero_add]
    calc ∑ y : G, (if P (some y) then K' ⟨a, haE⟩ (some y) else 0)
        ≤ ∑ y : G, (if (y : B) ∈ F then extK μ₁ E G K' a y else 0) := by
          refine Finset.sum_le_sum fun y _ => ?_
          split_ifs with h1 h2 h2
          · rw [extK_of_mem haE y.2 ha]
          · exact absurd h1 h2
          · exact zero_le
          · exact le_rfl
      _ = ∑ b ∈ F, extK μ₁ E G K' a b := by
          rw [Finset.sum_coe_sort G (fun b => if b ∈ F then extK μ₁ E G K' a b else 0),
            Finset.sum_ite_mem, Finset.inter_eq_right.mpr hFG]
  -- the excluded target mass
  have hs2 : ∑ o, (if P o then 0 else (colB μ₂ G).mass o) ≤ tailB μ₂ F := by
    rw [Fintype.sum_option, if_neg hPn]
    calc (colB μ₂ G).mass none + ∑ y : G, (if P (some y) then 0 else (colB μ₂ G).mass (some y))
        ≤ tailB μ₂ G + ∑ y : G, (if (y : B) ∈ F then 0 else μ₂.mass y) := by
          refine add_le_add le_rfl (Finset.sum_le_sum fun y _ => ?_)
          split_ifs with h1 h2 h2
          · exact le_rfl
          · exact zero_le
          · exact absurd h2 h1
          · exact le_rfl
      _ = tailB μ₂ F := by
          rw [Finset.sum_coe_sort G (fun b => if b ∈ F then 0 else μ₂.mass b), add_comm]
          conv_rhs => rw [tailB, ← sum_add_tail (fun b => if b ∈ F then 0 else μ₂.mass b) G]
          congr 1
          rw [tailB]
          refine tsum_congr fun b => ?_
          by_cases hb : b ∈ G
          · simp [hb]
          · have hbF : b ∉ F := fun h => hb (hFG h)
            simp [hb, hbF]
  have hmono : (η * (∑ o, if P o then 0 else (colB μ₂ G).mass o) ^ (α - 1)) ^ (1 / α)
      ≤ (η * tailB μ₂ F ^ (α - 1)) ^ (1 / α) :=
    ENNReal.rpow_le_rpow (mul_le_mul' le_rfl (ENNReal.rpow_le_rpow hs2 (by linarith)))
      (one_div_pos.mpr hα0).le
  calc μ₁.mass a ≤ _ := h
    _ ≤ μ₁.mass a * ∑ b ∈ F, extK μ₁ E G K' a b + (η * tailB μ₂ F ^ (α - 1)) ^ (1 / α) :=
        add_le_add (mul_le_mul' le_rfl hs1) hmono

end Ext

/-!
## Strong duality for arbitrary types
-/

/-- The excluded mass of `μ₂` vanishes along finite sets. -/
lemma tendsto_tailB (μ₂ : Distr B) : Tendsto (fun F : Finset B => tailB μ₂ F) atTop (𝓝 0) := by
  have h := ENNReal.tendsto_tsum_compl_atTop_zero (f := μ₂.mass)
    (ne_top_of_le_ne_top ENNReal.one_ne_top μ₂.le_one)
  refine h.congr fun F => ?_
  rw [tailB]
  refine ((tsum_subtype ({x | x ∉ F} : Set B) μ₂.mass)).trans (tsum_congr fun b => ?_)
  by_cases hb : b ∈ F
  · simp [Set.indicator, hb]
  · simp [Set.indicator, hb]

/-- **Strong duality**, arbitrary types: under the partner conditions, the
    witness-free lifting implies the two-witness lifting. -/
theorem flift_of_codLift_gen {α : ℝ} (hα : 1 < α) {R : A → B → Prop} {η : ℝ≥0∞}
    {μ₁ : Distr A} {μ₂ : Distr B}
    (hp₁ : ∀ a, μ₁.mass a ≠ 0 → ∃ b, R a b) (hp₂ : ∀ b, μ₂.mass b ≠ 0 → ∃ a, R a b)
    (h : CodLiftMul α R η μ₁ μ₂) : FLiftMul α R η μ₁ μ₂ := by
  have hα0 : (0:ℝ) < α := by linarith
  have hα1 : (0:ℝ) < α - 1 := by linarith
  by_cases hnd : ∀ a, μ₁.mass a ≠ 0 → ∃ b, R a b ∧ μ₂.mass b ≠ 0
  swap
  · push Not at hnd
    obtain ⟨a₀, ha₀, hbad⟩ := hnd
    rw [eta_top_of_degenerate hα h ha₀ hbad]
    exact flift_top hα hp₁ hp₂
  by_cases hηtop : η = ⊤
  · rw [hηtop]; exact flift_top hα hp₁ hp₂
  -- a certified kernel on every finite subproblem
  have hex : ∀ p : Finset A × Finset B, ∃ K' : Ker p.1 (Option p.2),
      Feas (resA μ₁ p.1) (fun x o => relEG R p.1 p.2 x o ∧ (colB μ₂ p.2).mass o ≠ 0) K' ∧
      J α (resA μ₁ p.1) (colB μ₂ p.2) K' ≤ η :=
    fun p => exists_ker_of_codLift hα (hnd_res hnd p.1 p.2) (codLift_res hα h p.1 p.2)
  choose Kf hKf using hex
  set Kseq : Finset A × Finset B → A → B → ℝ≥0∞ := fun p => extK μ₁ p.1 p.2 (Kf p)
    with hKseq
  -- a limit along an ultrafilter finer than `atTop`
  set 𝒰 : Ultrafilter (Finset A × Finset B) := Ultrafilter.of atTop with h𝒰def
  have h𝒰 : (𝒰 : Filter (Finset A × Finset B)) ≤ atTop := Ultrafilter.of_le _
  obtain ⟨K, -, hKlim⟩ := isCompact_univ.ultrafilter_le_nhds (𝒰.map Kseq) (by simp)
  have hT : Tendsto Kseq 𝒰 (𝓝 K) := by
    rw [Tendsto, ← Ultrafilter.coe_map]; exact hKlim
  have hTab : ∀ a b, Tendsto (fun p => Kseq p a b) 𝒰 (𝓝 (K a b)) := fun a b =>
    (((continuous_apply b).comp (continuous_apply a) :
      Continuous fun K : A → B → ℝ≥0∞ => K a b).tendsto K).comp hT
  have hev : ∀ (E₀ : Finset A) (G₀ : Finset B),
      ∀ᶠ p in (𝒰 : Filter (Finset A × Finset B)), E₀ ⊆ p.1 ∧ G₀ ⊆ p.2 :=
    fun E₀ G₀ => ((eventually_ge_atTop (E₀, G₀)).filter_mono h𝒰).mono fun p hp => ⟨hp.1, hp.2⟩
  -- (1) support
  have hsupp : ∀ a b, μ₁.mass a ≠ 0 → ¬ (R a b ∧ μ₂.mass b ≠ 0) → K a b = 0 := by
    intro a b ha hn
    have h0 : (fun p => Kseq p a b) = fun _ => 0 :=
      funext fun p => extK_supp (hKf p).1 ha hn
    exact tendsto_nhds_unique (hTab a b) (by rw [h0]; exact tendsto_const_nhds)
  -- (2) rows: at most one ...
  have hrow_le : ∀ a, ∑' b, K a b ≤ 1 := by
    intro a
    rw [ENNReal.tsum_eq_iSup_sum]
    refine iSup_le fun F => le_of_tendsto' (tendsto_finset_sum F fun b _ => hTab a b) fun p => ?_
    exact le_trans (ENNReal.sum_le_tsum F) (tsum_extK_le (hKf p).1 a)
  -- ... and no mass escapes
  have hθ : Tendsto (fun F : Finset B => (η * tailB μ₂ F ^ (α - 1)) ^ (1 / α)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun F : Finset B => tailB μ₂ F ^ (α - 1)) atTop (𝓝 0) := by
      have := ((ENNReal.continuous_rpow_const (y := α - 1)).tendsto 0).comp (tendsto_tailB μ₂)
      rwa [ENNReal.zero_rpow_of_pos hα1] at this
    have h2 : Tendsto (fun F : Finset B => η * tailB μ₂ F ^ (α - 1)) atTop (𝓝 0) := by
      have := ENNReal.Tendsto.const_mul h1 (Or.inr hηtop)
      rwa [mul_zero] at this
    have := ((ENNReal.continuous_rpow_const (y := 1 / α)).tendsto 0).comp h2
    rwa [ENNReal.zero_rpow_of_pos (one_div_pos.mpr hα0)] at this
  have hrow : ∀ a, μ₁.mass a ≠ 0 → ∑' b, K a b = 1 := by
    intro a ha
    refine le_antisymm (hrow_le a) ?_
    have hstep : ∀ F : Finset B, μ₁.mass a ≤ μ₁.mass a * ∑' b, K a b
        + (η * tailB μ₂ F ^ (α - 1)) ^ (1 / α) := by
      intro F
      have hlim : Tendsto (fun p => μ₁.mass a * ∑ b ∈ F, Kseq p a b
          + (η * tailB μ₂ F ^ (α - 1)) ^ (1 / α)) 𝒰
          (𝓝 (μ₁.mass a * ∑ b ∈ F, K a b + (η * tailB μ₂ F ^ (α - 1)) ^ (1 / α))) :=
        (ENNReal.Tendsto.const_mul (tendsto_finset_sum F fun b _ => hTab a b)
          (Or.inr (μ₁.mass_ne_top a))).add tendsto_const_nhds
      have h1 := ge_of_tendsto hlim ((hev {a} F).mono fun p hp =>
        extK_tight (hKf p).1 hα (hKf p).2 ha (hp.1 (Finset.mem_singleton_self a)) hp.2)
      exact h1.trans (add_le_add (mul_le_mul' le_rfl (ENNReal.sum_le_tsum F)) le_rfl)
    have h2 : μ₁.mass a ≤ μ₁.mass a * ∑' b, K a b + 0 :=
      ge_of_tendsto (tendsto_const_nhds.add hθ) (Eventually.of_forall hstep)
    rw [add_zero] at h2
    exact (ENNReal.mul_le_mul_iff_right ha (μ₁.mass_ne_top a)).mp (by rwa [mul_one])
  -- (3) the budget survives the limit
  have hJm : Jm α μ₁ μ₂ K ≤ η := by
    by_contra hcon
    push Not at hcon
    obtain ⟨p, hp⟩ := (hT.eventually (Jm_lsc hα μ₁ μ₂ K η hcon)).exists
    exact absurd (Jm_extK_le (hKf p).1 hα (hKf p).2) (not_le.mpr hp)
  -- the witnesses
  have hfeas : FeasC μ₁ (fun a b => R a b ∧ μ₂.mass b ≠ 0) K :=
    fun a ha => ⟨hrow a ha, fun b hb => hsupp a b ha hb⟩
  refine flift_of_kernel hα hfeas (fun _ _ h => h.1) hp₂ ?_
  rwa [JC_eq_Jm hα hfeas (fun _ _ h => h.2)]

/-- **Witness-free characterization of the Rényi lifting**, arbitrary types:
    under the partner conditions, the two-witness lifting and the codensity
    lifting with one-point tests coincide. -/
theorem flift_mul_iff_codLift_gen {α : ℝ} (hα : 1 < α) {R : A → B → Prop} {η : ℝ≥0∞}
    {μ₁ : Distr A} {μ₂ : Distr B}
    (hp₁ : ∀ a, μ₁.mass a ≠ 0 → ∃ b, R a b) (hp₂ : ∀ b, μ₂.mass b ≠ 0 → ∃ a, R a b) :
    FLiftMul α R η μ₁ μ₂ ↔ CodLiftMul α R η μ₁ μ₂ :=
  ⟨codLift_of_flift hα, flift_of_codLift_gen hα hp₁ hp₂⟩

end Distr


end DStd
