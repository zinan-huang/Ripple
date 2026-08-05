/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Bracket

/-!
# The phase-3 absorption potential

In the endgame, consensus at minority count `y = 0` is absorbing.  The natural
geometric potential must therefore be corrected from `ρ ^ y` to `ρ ^ y - 1`,
which vanishes exactly at absorption.

This file contains the scalar arithmetic behind that correction.  The key
inequality `ρ ^ y - 1 ≤ y * ρ ^ y` turns a contraction proportional to `y`
into a uniform contraction of the corrected potential.  No probability enters
these statements.
-/

namespace Tri

/-- If `ρ ≥ 1` and `y ≥ 1`, multiplying `ρ ^ y` by `y` cannot make it smaller. -/
theorem mul_pow_ge_pow_sub_one {ρ : ℝ} (hρ : 1 ≤ ρ) {y : ℕ} (hy : 1 ≤ y) :
    ρ ^ y ≤ y * ρ ^ y := by
  have hpow : 0 ≤ ρ ^ y := pow_nonneg (zero_le_one.trans hρ) y
  have hy' : (1 : ℝ) ≤ y := by exact_mod_cast hy
  simpa using mul_le_mul_of_nonneg_right hy' hpow

/-- The absorption correction is bounded by the state-weighted geometric
potential.  At `y = 0`, both sides are zero. -/
theorem pow_sub_one_le_mul_pow {ρ : ℝ} (hρ : 1 ≤ ρ) (y : ℕ) :
    ρ ^ y - 1 ≤ y * ρ ^ y := by
  cases y with
  | zero => norm_num
  | succ y =>
      exact (sub_le_self _ zero_le_one).trans
        (mul_pow_ge_pow_sub_one hρ (Nat.succ_le_succ (Nat.zero_le y)))

/-- **Absorption uniformisation.**  A drift rate proportional to `y` for the
uncorrected geometric potential becomes a state-independent drift rate for
`ρ ^ y - 1`.

Only nonnegativity of the state-dependent rate is needed.  In particular, the
usual side condition `c * y / n ≤ 1` ensuring that the one-step multiplier is
nonnegative plays no role in this scalar implication. -/
theorem absorption_uniformise {E ρ c n : ℝ} (y : ℕ) (hρ : 1 ≤ ρ)
    (hrate : 0 ≤ c * (y : ℝ) / n)
    (hE : E ≤ ρ ^ y * (1 - c * (y : ℝ) / n)) :
    E - 1 ≤ (1 - c / n) * (ρ ^ y - 1) := by
  cases y with
  | zero =>
      simpa using sub_le_sub_right hE 1
  | succ y =>
      have hy : (0 : ℝ) < (Nat.succ y : ℕ) := by positivity
      have hrate' : 0 ≤ (c / n) * (Nat.succ y : ℕ) := by
        calc
          0 ≤ c * (Nat.succ y : ℕ) / n := hrate
          _ = (c / n) * (Nat.succ y : ℕ) := by ring
      have hcn : 0 ≤ c / n := nonneg_of_mul_nonneg_left hrate' hy
      have hcorrection := pow_sub_one_le_mul_pow hρ (Nat.succ y)
      have hgap : 0 ≤ c / n *
          ((Nat.succ y : ℕ) * ρ ^ Nat.succ y - (ρ ^ Nat.succ y - 1)) :=
        mul_nonneg hcn (sub_nonneg.mpr hcorrection)
      calc
        E - 1 ≤ ρ ^ Nat.succ y *
              (1 - c * (Nat.succ y : ℕ) / n) - 1 := sub_le_sub_right hE 1
        _ = (1 - c / n) * (ρ ^ Nat.succ y - 1) - c / n *
              ((Nat.succ y : ℕ) * ρ ^ Nat.succ y - (ρ ^ Nat.succ y - 1)) := by ring
        _ ≤ (1 - c / n) * (ρ ^ Nat.succ y - 1) := sub_le_self _ hgap

/-- A nonnegative scalar contraction factor iterates geometrically.  Applied
with `q = 1 - c / n`, this is the phase-3 bound
`V T ≤ V 0 * (1 - c / n) ^ T`. -/
theorem absorption_iterate (V : ℕ → ℝ) {c n : ℝ} (hfactor : 0 ≤ 1 - c / n)
    (hstep : ∀ t, V (t + 1) ≤ (1 - c / n) * V t) (T : ℕ) :
    V T ≤ V 0 * (1 - c / n) ^ T := by
  induction T with
  | zero => simp
  | succ T ih =>
      calc
        V (Nat.succ T) ≤ (1 - c / n) * V T := by
          simpa [Nat.succ_eq_add_one] using hstep T
        _ ≤ (1 - c / n) * (V 0 * (1 - c / n) ^ T) :=
          mul_le_mul_of_nonneg_left ih hfactor
        _ = V 0 * (1 - c / n) ^ Nat.succ T := by rw [pow_succ]; ring

/-- The exact horizon requirement for reaching a target `ε`: it suffices that
the iterated scalar upper bound is at most `ε`. -/
theorem absorption_iterate_reaches (V : ℕ → ℝ) {c n ε : ℝ}
    (hfactor : 0 ≤ 1 - c / n)
    (hstep : ∀ t, V (t + 1) ≤ (1 - c / n) * V t) (T : ℕ)
    (hT : V 0 * (1 - c / n) ^ T ≤ ε) :
    V T ≤ ε :=
  (absorption_iterate V hfactor hstep T).trans hT

end Tri
