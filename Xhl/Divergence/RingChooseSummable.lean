import Mathlib.RingTheory.Binomial
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.PSeries

/-!
# Summability of the generalized binomial coefficient at a real exponent

`summable_abs_ringChoose`: `Summable (fun n => |Ring.choose a n|)` for real `a > 0`, elementarily.

1. `choose_succ_eq`: `choose a (n+1) = choose a n * (a-n) / (n+1)`.
2. `log_ratio_le`: past a threshold, `log(|a-j|/(j+1)) ≤ -(1+a)/(j+1) + 2(1+a)²/(j+1)²`.
3. `accum`, `tail_sq_bound`: summed, the linear term telescopes to `-(1+a)·log n` and the
   quadratic one stays bounded.
4. `poly_decay`: `|choose a n| ≤ C · (n+1)^(-(1+a))`; comparison with a `p`-series concludes.
-/

open Finset Real

namespace RingChooseSummable

/-- `Ring.choose a n` as an explicit product, via `descPochhammer`'s eval-product formula. -/
theorem choose_eq_prod_div_factorial (a : ℝ) (n : ℕ) :
    Ring.choose a n = (n.factorial : ℝ)⁻¹ * ∏ j ∈ range n, (a - j) := by
  rw [Ring.choose_eq_smul, smul_eq_mul]
  congr 1
  rw [← Polynomial.aeval_eq_smeval (R := ℤ) a (descPochhammer ℤ n),
    Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, descPochhammer_map,
    descPochhammer_eval_eq_prod_range]

/-- `choose a (n+1) = choose a n * (a-n) / (n+1)`. -/
theorem choose_succ_eq (a : ℝ) (n : ℕ) :
    Ring.choose a (n + 1) = Ring.choose a n * (a - n) / (n + 1) := by
  rw [choose_eq_prod_div_factorial, choose_eq_prod_div_factorial,
    Finset.prod_range_succ, Nat.factorial_succ]
  push_cast
  field_simp

/-- First-order Taylor bound for `log(1-x)` with explicit quadratic remainder, via Mathlib's
`abs_log_sub_add_sum_range_le`. -/
theorem log_one_sub_le (x : ℝ) (hx : |x| < 1) :
    Real.log (1 - x) ≤ -x + x^2 / (1 - |x|) := by
  have h := abs_log_sub_add_sum_range_le hx 1
  simp only [Finset.sum_range_one] at h
  have h2 := (abs_le.mp h).2
  norm_num at h2
  linarith

/-- Past a threshold depending on `a`, `log(|a-j|/(j+1)) ≤ -(1+a)/(j+1) + 2(1+a)²/(j+1)²`. -/
theorem log_ratio_le (a : ℝ) {j : ℕ} (hj : 2 * (|a| + 1) ≤ (j:ℝ)) :
    Real.log (|a - (j:ℝ)| / ((j:ℝ) + 1)) ≤ -((1+a)/((j:ℝ)+1)) + 2*(1+a)^2/((j:ℝ)+1)^2 := by
  have hj0 : (0:ℝ) ≤ j := by positivity
  have hja : (j:ℝ) > a := by
    have : |a| ≥ a := le_abs_self a
    linarith
  have heq : |a - (j:ℝ)| / ((j:ℝ)+1) = 1 - (1+a)/((j:ℝ)+1) := by
    rw [abs_of_neg (by linarith : a - (j:ℝ) < 0)]
    field_simp
    ring
  rw [heq]
  have hxabs : |(1+a)/((j:ℝ)+1)| ≤ 1/2 := by
    rw [abs_div, abs_of_pos (by linarith : (0:ℝ) < (j:ℝ)+1)]
    rw [div_le_iff₀ (by linarith : (0:ℝ) < (j:ℝ)+1)]
    have h1a : |1+a| ≤ |a|+1 := by
      rcases abs_cases a with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> rcases abs_cases (1+a) with ⟨h3,h4⟩ | ⟨h3,h4⟩ <;>
        linarith
    linarith
  have hxlt1 : |(1+a)/((j:ℝ)+1)| < 1 := lt_of_le_of_lt hxabs (by norm_num)
  have hbound := log_one_sub_le ((1+a)/((j:ℝ)+1)) hxlt1
  have hxsq : ((1+a)/((j:ℝ)+1))^2 / (1 - |(1+a)/((j:ℝ)+1)|) ≤ 2 * ((1+a)/((j:ℝ)+1))^2 := by
    have h1mx : (1:ℝ)/2 ≤ 1 - |(1+a)/((j:ℝ)+1)| := by linarith
    rw [div_le_iff₀ (by linarith : (0:ℝ) < 1 - |(1+a)/((j:ℝ)+1)|)]
    nlinarith [sq_nonneg ((1+a)/((j:ℝ)+1))]
  have hpow : ((1+a)/((j:ℝ)+1))^2 = (1+a)^2/((j:ℝ)+1)^2 := by rw [div_pow]
  rw [hpow] at hxsq hbound
  ring_nf at hxsq hbound ⊢
  linarith [hbound, hxsq]

/-- Per-step log-decay bound for `Ring.choose`, combining `choose_succ_eq` with `log_ratio_le`. -/
theorem log_choose_succ_le (a : ℝ) {n : ℕ} (hn : 2*(|a|+1) ≤ (n:ℝ)) (hcn : Ring.choose a n ≠ 0) :
    Real.log |Ring.choose a (n+1)| ≤
      Real.log |Ring.choose a n| - ((1+a)/((n:ℝ)+1)) + 2*(1+a)^2/((n:ℝ)+1)^2 := by
  have hcn1 : Ring.choose a (n+1) = Ring.choose a n * (a-n)/(n+1) := choose_succ_eq a n
  have hna : (n:ℝ) > a := by have := le_abs_self a; linarith
  have hanz : a - (n:ℝ) ≠ 0 := by intro h; linarith [sub_eq_zero.mp h]
  have heq : |Ring.choose a (n+1)| = |Ring.choose a n| * (|a-(n:ℝ)|/((n:ℝ)+1)) := by
    rw [hcn1, abs_div, abs_mul, abs_of_pos (by positivity : (0:ℝ) < (n:ℝ)+1), mul_div_assoc]
  rw [heq, Real.log_mul (abs_ne_zero.mpr hcn) (by positivity)]
  have hlr := log_ratio_le a hn
  linarith

/-- Nonzero-ness of `Ring.choose a n` persists forward past the threshold where `n > a`. -/
theorem chain_nonzero (a : ℝ) {n : ℕ} (hna : (n:ℝ) > a) (hcn : Ring.choose a n ≠ 0) :
    Ring.choose a (n+1) ≠ 0 := by
  rw [choose_succ_eq a n]
  apply div_ne_zero
  · apply mul_ne_zero hcn
    intro h
    linarith [sub_eq_zero.mp h]
  · positivity

theorem harmonic_log_le (j : ℕ) : Real.log ((j:ℝ)+2) - Real.log ((j:ℝ)+1) ≤ 1/((j:ℝ)+1) := by
  have hpos : (0:ℝ) < ((j:ℝ)+2)/((j:ℝ)+1) := by positivity
  have h := log_le_sub_one_of_pos hpos
  rw [Real.log_div (by positivity) (by positivity)] at h
  have heq : ((j:ℝ)+2)/((j:ℝ)+1) - 1 = 1/((j:ℝ)+1) := by field_simp; ring
  linarith [h, heq]

theorem one_div_sq_le (j : ℕ) (hj : 1 ≤ j) : (1:ℝ)/((j:ℝ)+1)^2 ≤ 1/(j:ℝ) - 1/((j:ℝ)+1) := by
  have hj0 : (0:ℝ) < j := by exact_mod_cast hj
  have heq : 1/(j:ℝ) - 1/((j:ℝ)+1) = 1/((j:ℝ)*((j:ℝ)+1)) := by field_simp; ring
  rw [heq, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [sq_nonneg (j:ℝ)]

theorem tail_sq_bound_aux (N : ℕ) (hN : 1 ≤ N) :
    ∀ k : ℕ, ∑ j ∈ Finset.range k, (1:ℝ)/((N:ℝ)+j+1)^2 ≤ 1/(N:ℝ) - 1/((N:ℝ)+k) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have hNk : 1 ≤ N + k := by omega
    have hstep : (1:ℝ)/((N:ℝ)+k+1)^2 ≤ 1/((N:ℝ)+k) - 1/((N:ℝ)+k+1) := by
      have := one_div_sq_le (N+k) hNk
      push_cast at this ⊢
      convert this using 2 <;> ring
    push_cast
    push_cast at ih hstep
    ring_nf
    ring_nf at ih hstep
    linarith [ih, hstep]

/-- The quadratic error term, summed over any tail starting at `N`, is bounded by `1/N`. -/
theorem tail_sq_bound (N : ℕ) (hN : 1 ≤ N) (k : ℕ) :
    ∑ j ∈ Finset.range k, (1:ℝ)/((N:ℝ)+j+1)^2 ≤ 1/(N:ℝ) := by
  have h := tail_sq_bound_aux N hN k
  have hpos : (0:ℝ) ≤ 1/((N:ℝ)+k) := by positivity
  linarith

/-- The log-decay bound accumulated over `N, N+1, …, N+k`. -/
theorem accum (a : ℝ) (ha1 : -1 < a) (N : ℕ) (ha : 2*(|a|+1) ≤ (N:ℝ))
    (hcN : Ring.choose a N ≠ 0) :
    ∀ k : ℕ, Ring.choose a (N+k) ≠ 0 ∧
      Real.log |Ring.choose a (N+k)| ≤ Real.log |Ring.choose a N|
        - (1+a) * (Real.log ((N:ℝ)+(k:ℝ)+1) - Real.log ((N:ℝ)+1))
        + 2*(1+a)^2 * (∑ j ∈ Finset.range k, (1:ℝ)/((N:ℝ)+j+1)^2) := by
  have hNa : (N:ℝ) > a := by have := le_abs_self a; linarith
  intro k
  induction k with
  | zero => refine ⟨by simpa using hcN, by simp⟩
  | succ k ih =>
    obtain ⟨ihnz, ihle⟩ := ih
    have hNka : ((N:ℝ)+(k:ℝ)) > a := by
      have hk0 : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
      linarith
    have hnz' : Ring.choose a (N+(k+1)) ≠ 0 := by
      have heqn : N + (k+1) = (N+k)+1 := by ring
      rw [heqn]
      apply chain_nonzero a _ ihnz
      push_cast
      exact hNka
    refine ⟨hnz', ?_⟩
    have heqn : N + (k+1) = (N+k)+1 := by ring
    have hge : 2*(|a|+1) ≤ ((N+k:ℕ):ℝ) := by push_cast; linarith
    have hstep := log_choose_succ_le a (n := N+k) hge ihnz
    rw [heqn]
    rw [heqn] at hnz'
    have hharm := harmonic_log_le (N+k)
    have hsum_eq : ∑ j ∈ Finset.range (k+1), (1:ℝ)/((N:ℝ)+j+1)^2
        = (∑ j ∈ Finset.range k, (1:ℝ)/((N:ℝ)+j+1)^2) + 1/((N:ℝ)+k+1)^2 := by
      rw [Finset.sum_range_succ]
    rw [hsum_eq]
    push_cast at hstep ⊢
    push_cast at hharm
    have key : (1+a) * (Real.log ((N:ℝ)+(k:ℝ)+1+1) - Real.log ((N:ℝ)+(k:ℝ)+1))
        ≤ (1+a) * (1/((N:ℝ)+(k:ℝ)+1)) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      have h1 : ((N:ℝ)+(k:ℝ)+1+1) = ((N:ℝ)+(k:ℝ))+2 := by ring
      rw [h1]
      have h2 : ((N:ℝ)+(k:ℝ)+1) = ((N:ℝ)+(k:ℝ))+1 := by ring
      rw [h2]
      exact hharm
    ring_nf at hstep key ihle ⊢
    nlinarith [ihle, hstep, key]

/-- Polynomial decay: for `n ≥ N`, `|choose a n| ≤ C * (n+1)^(-(1+a))`. -/
theorem poly_decay (a : ℝ) (ha1 : -1 < a) (N : ℕ) (hN1 : 1 ≤ N) (ha : 2*(|a|+1) ≤ (N:ℝ))
    (hcN : Ring.choose a N ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ n ≥ N, |Ring.choose a n| ≤ C * ((n:ℝ)+1) ^ (-(1+a)) := by
  set C : ℝ := |Ring.choose a N| * Real.exp (2*(1+a)^2/(N:ℝ)) * ((N:ℝ)+1)^(1+a) with hCdef
  have hCpos : 0 < C := by
    rw [hCdef]
    have h1 : (0:ℝ) < |Ring.choose a N| := abs_pos.mpr hcN
    have h2 : (0:ℝ) < Real.exp (2*(1+a)^2/(N:ℝ)) := Real.exp_pos _
    have h3 : (0:ℝ) < ((N:ℝ)+1)^(1+a) := Real.rpow_pos_of_pos (by positivity) _
    positivity
  refine ⟨C, hCpos, ?_⟩
  intro n hn
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hn
  subst hk
  obtain ⟨_, hle⟩ := accum a ha1 N ha hcN k
  have htail := tail_sq_bound N hN1 k
  have hqerr : 2*(1+a)^2 * (∑ j ∈ Finset.range k, (1:ℝ)/((N:ℝ)+j+1)^2) ≤ 2*(1+a)^2/(N:ℝ) := by
    have hnn : (0:ℝ) ≤ 2*(1+a)^2 := by positivity
    calc 2*(1+a)^2 * (∑ j ∈ Finset.range k, (1:ℝ)/((N:ℝ)+j+1)^2)
        ≤ 2*(1+a)^2 * (1/(N:ℝ)) := mul_le_mul_of_nonneg_left htail hnn
      _ = 2*(1+a)^2/(N:ℝ) := by ring
  have hlogle : Real.log |Ring.choose a (N+k)| ≤
      Real.log |Ring.choose a N| - (1+a) * (Real.log ((N:ℝ)+(k:ℝ)+1) - Real.log ((N:ℝ)+1))
        + 2*(1+a)^2/(N:ℝ) := by linarith
  have hexp : |Ring.choose a (N+k)| ≤
      Real.exp (Real.log |Ring.choose a N| - (1+a) * (Real.log ((N:ℝ)+(k:ℝ)+1) - Real.log ((N:ℝ)+1))
        + 2*(1+a)^2/(N:ℝ)) := by
    have hpos : (0:ℝ) < |Ring.choose a (N+k)| := by
      obtain ⟨hnz, _⟩ := accum a ha1 N ha hcN k
      exact abs_pos.mpr hnz
    calc |Ring.choose a (N+k)| = Real.exp (Real.log |Ring.choose a (N+k)|) := (Real.exp_log hpos).symm
      _ ≤ _ := Real.exp_le_exp.mpr hlogle
  have hrw : Real.exp (Real.log |Ring.choose a N| - (1+a) * (Real.log ((N:ℝ)+(k:ℝ)+1) - Real.log ((N:ℝ)+1))
        + 2*(1+a)^2/(N:ℝ))
      = |Ring.choose a N| * Real.exp (2*(1+a)^2/(N:ℝ)) *
          Real.exp (-(1+a) * Real.log ((N:ℝ)+(k:ℝ)+1)) * Real.exp ((1+a) * Real.log ((N:ℝ)+1)) := by
    rw [show Real.log |Ring.choose a N| - (1+a) * (Real.log ((N:ℝ)+(k:ℝ)+1) - Real.log ((N:ℝ)+1))
        + 2*(1+a)^2/(N:ℝ)
        = Real.log |Ring.choose a N| + 2*(1+a)^2/(N:ℝ)
          + (-(1+a) * Real.log ((N:ℝ)+(k:ℝ)+1)) + ((1+a) * Real.log ((N:ℝ)+1)) by ring]
    rw [Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_log (abs_pos.mpr hcN)]
  rw [hrw] at hexp
  have hNk1pos : (0:ℝ) < (N:ℝ)+(k:ℝ)+1 := by positivity
  have hN1pos : (0:ℝ) < (N:ℝ)+1 := by positivity
  rw [show Real.exp (-(1+a) * Real.log ((N:ℝ)+(k:ℝ)+1)) = ((N:ℝ)+(k:ℝ)+1) ^ (-(1+a)) by
        rw [Real.rpow_def_of_pos hNk1pos]; ring_nf,
      show Real.exp ((1+a) * Real.log ((N:ℝ)+1)) = ((N:ℝ)+1) ^ (1+a) by
        rw [Real.rpow_def_of_pos hN1pos]; ring_nf] at hexp
  push_cast
  rw [hCdef]
  calc |Ring.choose a (N+k)|
      ≤ |Ring.choose a N| * Real.exp (2*(1+a)^2/(N:ℝ)) * ((N:ℝ)+(k:ℝ)+1) ^ (-(1+a)) * ((N:ℝ)+1) ^ (1+a) :=
        hexp
    _ = |Ring.choose a N| * Real.exp (2*(1+a)^2/(N:ℝ)) * ((N:ℝ)+1)^(1+a) * ((N:ℝ)+(k:ℝ)+1) ^ (-(1+a)) := by
        ring

/-- **`Ring.choose a n` is absolutely summable** for real `a > 0`, given a threshold `N` with
`2(|a|+1) ≤ N` and `Ring.choose a N ≠ 0` (`summable_abs_ringChoose_always` drops these). -/
theorem summable_abs_ringChoose (a : ℝ) (ha : 0 < a) (N : ℕ) (hN1 : 1 ≤ N)
    (hNbd : 2*(|a|+1) ≤ (N:ℝ)) (hcN : Ring.choose a N ≠ 0) :
    Summable (fun n : ℕ => |Ring.choose a n|) := by
  obtain ⟨C, hCpos, hCbd⟩ := poly_decay a (by linarith) N hN1 hNbd hcN
  rw [← summable_nat_add_iff N]
  have hp : Summable (fun n : ℕ => ((n:ℝ)+(N:ℝ)+1) ^ (-(1+a))) := by
    have hsum := (Real.summable_nat_rpow (p := -(1+a))).mpr (by linarith)
    have heq : (fun n : ℕ => ((n:ℝ)+(N:ℝ)+1) ^ (-(1+a)))
        = (fun n : ℕ => ((n + (N+1) : ℕ):ℝ) ^ (-(1+a))) := by
      funext n; push_cast; ring_nf
    rw [heq]
    exact (summable_nat_add_iff (N+1)).mpr hsum
  have hCsum : Summable (fun n : ℕ => C * ((n:ℝ)+(N:ℝ)+1) ^ (-(1+a))) := hp.mul_left C
  apply Summable.of_nonneg_of_le (fun n => abs_nonneg _) (fun n => ?_) hCsum
  have hge : N + n ≥ N := Nat.le_add_right N n
  have hb := hCbd (N + n) hge
  rw [show N + n = n + N from by ring] at hb
  push_cast at hb ⊢
  exact hb

end RingChooseSummable
