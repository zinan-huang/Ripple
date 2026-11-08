import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Frobenius framework — falling factorial and falling Euler operator

This file extends `Frobenius/Indicial.lean` with the falling-factorial basis
that is natural for linear ODEs written in `(d/dt)^k` form (rather than
Euler form).

Under the Frobenius ansatz `y = t^ρ · g(t)`, the leading behaviour of
`(d/dt)^k y` is `ρ^{(k)} · t^{ρ-k} · g(0)` where `ρ^{(k)} = ρ(ρ-1)…(ρ-k+1)`
is the falling factorial. The "falling Euler operator"
`(ρ + L)(ρ + L − 1)…(ρ + L − k + 1)` on the `g`-series encodes this
leading behaviour purely algebraically, with the same coefficient formula
`fallingFactorial (ρ + n) k · aₙ` on the `n`-th coefficient.

The monomial-basis `indicialPoly` defined in `Indicial.lean` can be
re-expressed in the falling-factorial basis via Stirling numbers; that
re-expression is deferred.
-/

namespace Ripple
namespace Number.Frobenius

open PowerSeries

/-- Falling factorial `x^{(k)} = x · (x-1) · (x-2) · … · (x - k + 1)`,
with the convention `x^{(0)} = 1`. -/
noncomputable def fallingFactorial (x : ℝ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => fallingFactorial x k * (x - k)

@[simp] lemma fallingFactorial_zero (x : ℝ) :
    fallingFactorial x 0 = 1 := rfl

lemma fallingFactorial_succ (x : ℝ) (k : ℕ) :
    fallingFactorial x (k + 1) = fallingFactorial x k * (x - k) := rfl

@[simp] lemma fallingFactorial_one (x : ℝ) :
    fallingFactorial x 1 = x := by
  simp [fallingFactorial]

lemma fallingFactorial_two (x : ℝ) :
    fallingFactorial x 2 = x * (x - 1) := by
  simp [fallingFactorial]

lemma fallingFactorial_three (x : ℝ) :
    fallingFactorial x 3 = x * (x - 1) * (x - 2) := by
  simp [fallingFactorial]

/-- At a natural-number argument, the falling factorial vanishes once `k > n`. -/
lemma fallingFactorial_nat_lt {n k : ℕ} (hk : n < k) :
    fallingFactorial (n : ℝ) k = 0 := by
  induction k with
  | zero => exact absurd hk (Nat.not_lt_zero _)
  | succ k ih =>
    rw [fallingFactorial_succ]
    by_cases h : n < k
    · rw [ih h]; ring
    · have hnk : n = k := by omega
      subst hnk
      simp

/-- Uniform absolute bound: `|x^{(k)}| ≤ (|x| + k)^k`. Each factor
`|x − j| ≤ |x| + j ≤ |x| + k` for `j < k`, and the empty product at
`k = 0` gives the base `1 ≤ 1^0`. -/
lemma abs_fallingFactorial_le (x : ℝ) (k : ℕ) :
    |fallingFactorial x k| ≤ (|x| + k) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [fallingFactorial_succ, abs_mul, pow_succ]
    have h_xk_nn : (0 : ℝ) ≤ |x| + (k : ℝ) := by
      have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
      linarith [abs_nonneg x]
    have h_xk1_nn : (0 : ℝ) ≤ |x| + ((k + 1 : ℕ) : ℝ) := by
      have : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith [abs_nonneg x]
    have h_step : (|x| + (k : ℝ)) ≤ (|x| + ((k + 1 : ℕ) : ℝ)) := by
      push_cast; linarith
    have h_base_pow : (|x| + (k : ℝ)) ^ k ≤ (|x| + ((k + 1 : ℕ) : ℝ)) ^ k := by
      exact pow_le_pow_left₀ h_xk_nn h_step k
    have h_absk : |x - (k : ℝ)| ≤ |x| + ((k + 1 : ℕ) : ℝ) := by
      have h1 : |x - (k : ℝ)| ≤ |x| + |(k : ℝ)| := abs_sub _ _
      have h2 : |(k : ℝ)| = (k : ℝ) := abs_of_nonneg (Nat.cast_nonneg _)
      rw [h2] at h1
      have h3 : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by push_cast; linarith
      linarith
    have h_ih_pow :
        |fallingFactorial x k| ≤ (|x| + ((k + 1 : ℕ) : ℝ)) ^ k :=
      le_trans ih h_base_pow
    have h_ff_nn : (0 : ℝ) ≤ |fallingFactorial x k| := abs_nonneg _
    have h_abs_nn : (0 : ℝ) ≤ |x - (k : ℝ)| := abs_nonneg _
    have h_pow_nn : (0 : ℝ) ≤ (|x| + ((k + 1 : ℕ) : ℝ)) ^ k :=
      pow_nonneg h_xk1_nn k
    exact mul_le_mul h_ih_pow h_absk h_abs_nn h_pow_nn

/-- **Lower bound on falling factorial at a large shifted argument.** If
the shift `m` exceeds `|ρ| + k`, then each factor
`(ρ + m − j) ≥ m − |ρ| − j ≥ m − |ρ| − k > 0`, giving the uniform bound
```
fallingFactorial (ρ + m) k ≥ ((m : ℝ) − |ρ| − k)^k.
```
This is the matching lower bound to `abs_fallingFactorial_le` and
provides the denominator control `|P(ρ + m)| ≳ m^{n+1}` in the
Frobenius convergence argument (via `simpleZeroIndicialPoly_factor`). -/
lemma fallingFactorial_shifted_lower_bound
    (ρ : ℝ) (k m : ℕ) (hm : (|ρ| + (k : ℝ)) < m) :
    ((m : ℝ) - |ρ| - (k : ℝ)) ^ k ≤
      fallingFactorial ((ρ : ℝ) + m) k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hcastk1 : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    have hm_k : (|ρ| + (k : ℝ)) < m := by
      rw [hcastk1] at hm; linarith
    have ihk := ih hm_k
    rw [fallingFactorial_succ, pow_succ]
    have h_kp1 : 0 ≤ (m : ℝ) - |ρ| - ((k + 1 : ℕ) : ℝ) := by
      rw [hcastk1]; linarith
    have h_k_nn : 0 ≤ (m : ℝ) - |ρ| - (k : ℝ) := by linarith
    have h_factor_step :
        (m : ℝ) - |ρ| - ((k + 1 : ℕ) : ℝ) ≤ (ρ + (m : ℝ)) - (k : ℝ) := by
      rw [hcastk1]
      have hn : -ρ ≤ |ρ| := neg_le_abs ρ
      linarith
    have h_base_step :
        ((m : ℝ) - |ρ| - ((k + 1 : ℕ) : ℝ)) ≤ ((m : ℝ) - |ρ| - (k : ℝ)) := by
      rw [hcastk1]; linarith
    have h_pow_le :
        ((m : ℝ) - |ρ| - ((k + 1 : ℕ) : ℝ)) ^ k ≤
          ((m : ℝ) - |ρ| - (k : ℝ)) ^ k :=
      pow_le_pow_left₀ h_kp1 h_base_step k
    have h_left :
        ((m : ℝ) - |ρ| - ((k + 1 : ℕ) : ℝ)) ^ k ≤
          fallingFactorial ((ρ : ℝ) + (m : ℝ)) k :=
      le_trans h_pow_le ihk
    have h_ff_nn : 0 ≤ fallingFactorial ((ρ : ℝ) + (m : ℝ)) k :=
      le_trans (pow_nonneg h_k_nn k) ihk
    exact mul_le_mul h_left h_factor_step h_kp1 h_ff_nn

/-- The falling Euler operator `(ρ + L)(ρ + L − 1) ⋯ (ρ + L − k + 1)`.
Acting on `Σ aₙ tⁿ`, it returns `Σ (ρ + n)^{(k)} aₙ tⁿ`. Equivalently, it is
the coefficient-wise scaling by `fallingFactorial (ρ + n) k`. -/
noncomputable def fallingEulerOp (ρ : ℝ) (k : ℕ) (f : PowerSeries ℝ) : PowerSeries ℝ :=
  mk fun n => fallingFactorial (ρ + n) k * coeff (R := ℝ) n f

@[simp] lemma coeff_fallingEulerOp (ρ : ℝ) (k : ℕ) (f : PowerSeries ℝ) (n : ℕ) :
    coeff (R := ℝ) n (fallingEulerOp ρ k f) =
      fallingFactorial (ρ + n) k * coeff (R := ℝ) n f := by
  simp [fallingEulerOp]

/-- Constant coefficient of the falling Euler operator applied to `g`:
the leading behaviour `ρ^{(k)} · g(0)` of `(d/dt)^k (t^ρ · g(t))`
algebraically. -/
lemma coeff_zero_fallingEulerOp (ρ : ℝ) (k : ℕ) (g : PowerSeries ℝ) :
    coeff (R := ℝ) 0 (fallingEulerOp ρ k g) =
      fallingFactorial ρ k * coeff (R := ℝ) 0 g := by
  rw [coeff_fallingEulerOp]
  norm_num

/-- Indicial polynomial in falling-factorial basis.

For a linear ODE `Σ_j p_j(z) y^{(j)}(z) = 0` at a regular singular point
`z = z₁`, the leading contribution to the Frobenius substitution is
controlled by constants `b_j` (extracted from the leading `t`-behaviour
of `p_j(z)`) combined with the falling factorials `ρ^{(j)}`. This
definition packages that combination. -/
noncomputable def indicialPolyFalling (bs : ℕ → ℝ) (k : ℕ) (ρ : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (k + 1), bs j * fallingFactorial ρ j

lemma indicialPolyFalling_zero_order (bs : ℕ → ℝ) (ρ : ℝ) :
    indicialPolyFalling bs 0 ρ = bs 0 := by
  simp [indicialPolyFalling]

lemma indicialPolyFalling_succ (bs : ℕ → ℝ) (k : ℕ) (ρ : ℝ) :
    indicialPolyFalling bs (k + 1) ρ =
      indicialPolyFalling bs k ρ + bs (k + 1) * fallingFactorial ρ (k + 1) := by
  simp [indicialPolyFalling, Finset.sum_range_succ]

/-- **Leading-coefficient identity, falling-factorial form.** The constant
coefficient of the falling-basis sum `Σ_j b_j · (falling-Euler)^j_{ρ} g`
factors as `indicialPolyFalling · g(0)`. -/
theorem coeff_zero_indicialSumFalling
    (bs : ℕ → ℝ) (k : ℕ) (ρ : ℝ) (g : PowerSeries ℝ) :
    coeff (R := ℝ) 0
        (∑ j ∈ Finset.range (k + 1), (bs j) • fallingEulerOp ρ j g)
      = indicialPolyFalling bs k ρ * coeff (R := ℝ) 0 g := by
  rw [map_sum]
  unfold indicialPolyFalling
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [LinearMap.map_smul, coeff_zero_fallingEulerOp]
  simp [smul_eq_mul]
  ring

/-- **Indicial equation, falling-factorial form.** -/
theorem indicial_root_of_leading_vanish_falling
    (bs : ℕ → ℝ) (k : ℕ) (ρ : ℝ) (g : PowerSeries ℝ)
    (hg : coeff (R := ℝ) 0 g ≠ 0)
    (hvanish : coeff (R := ℝ) 0
        (∑ j ∈ Finset.range (k + 1), (bs j) • fallingEulerOp ρ j g) = 0) :
    indicialPolyFalling bs k ρ = 0 := by
  have hmul : indicialPolyFalling bs k ρ * coeff (R := ℝ) 0 g = 0 := by
    rw [← coeff_zero_indicialSumFalling]; exact hvanish
  exact (mul_eq_zero.mp hmul).resolve_right hg

end Number.Frobenius
end Ripple
