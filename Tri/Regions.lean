/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Basic

/-!
# Productive mass in the three phase regions

This file proves the natural-number arithmetic behind the productive-reaction
lower bounds in Section 3.1 of the paper.  If `x + y = n`, the productive mass
is

    C(x, 2) y + x C(y, 2).

The statements avoid natural subtraction and division.  In particular, the
phase-2 coefficient `(2^(s+1) - 1) / 2^(2s+2)` is expressed by moving one copy
of `n^2` to the left-hand side.

Before formalization, the three claims were checked exhaustively over all
states with `n ≤ 500`; the phase-2 check covered every `s ≤ 8`.  No
counterexamples were found, and the strict phase-2 bound below is the paper's
exact constant rather than a weakening.

## Main results

* `productive_ge_phase3` gives the productive-mass identity together with
  `n ≤ x * y + 1` in the interior.
* `xy_ge_phase1` proves `7 * n^2 < 64 * x * y` in phase 1.
* `xy_ge_phase2` proves the exact stage-dependent phase-2 bound.
-/

namespace Tri

/-- **Phase 3 productive-mass bound.**

For an interior population, `x * y + 1 ≥ n`, the subtraction-free form of
`x * y ≥ n - 1`.  The first conjunct is `productive_two_mul` after replacing
`x + y` by `n`; together they give the paper's phase-3 lower bound on the
productive mass without mentioning `n - 2` or `n - 1`. -/
theorem productive_ge_phase3 {x y n : ℕ} (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hsum : x + y = n) :
    (2 * (Nat.choose x 2 * y + x * Nat.choose y 2) + 2 * (x * y) = x * y * n) ∧
      n ≤ x * y + 1 := by
  constructor
  · calc
      2 * (Nat.choose x 2 * y + x * Nat.choose y 2) + 2 * (x * y)
          = x * y * (x + y) := productive_two_mul x y
      _ = x * y * n := by rw [hsum]
  · rw [← hsum]
    nlinarith

/-- **Phase 1 product bound.**

The open region `n / 2 < x < 7 * n / 8` is stated by cross multiplication.
Inside it, `x * y` is strictly larger than `7 * n^2 / 64`, again stated by
cross multiplication. -/
theorem xy_ge_phase1 {x y n : ℕ} (hxLo : n < 2 * x) (hxHi : 8 * x < 7 * n)
    (hsum : x + y = n) :
    7 * n * n < 64 * x * y := by
  have hxLoZ : (n : ℤ) < 2 * (x : ℤ) := by exact_mod_cast hxLo
  have hxHiZ : 8 * (x : ℤ) < 7 * (n : ℤ) := by exact_mod_cast hxHi
  have hsumZ : (x : ℤ) + (y : ℤ) = (n : ℤ) := by exact_mod_cast hsum
  have hleft : 0 < 7 * (y : ℤ) - (x : ℤ) := by
    nlinarith
  have hright : 0 < 7 * (x : ℤ) - (y : ℤ) := by
    nlinarith
  have hprod : 0 < (7 * (y : ℤ) - (x : ℤ)) * (7 * (x : ℤ) - (y : ℤ)) :=
    mul_pos hleft hright
  exact_mod_cast (show 7 * (n : ℤ) * (n : ℤ) < 64 * (x : ℤ) * (y : ℤ) by
    nlinarith)

/-- **Phase 2 product bound with the paper's exact constant.**

Writing `k = 2^(s+1)`, the conclusion is the subtraction-free form of
`k^2 * x * y > (k - 1) * n^2`.  It is strict, so in particular it implies the
weak inequality requested for a lower bound; no weaker constant is used. -/
theorem xy_ge_phase2 {x y n s : ℕ} (hstage : 2 ^ (s + 1) * y > n)
    (hsum : x + y = n) (hmajor : 2 * x ≥ n) :
    2 ^ (2 * s + 2) * (x * y) + n * n > 2 ^ (s + 1) * n * n := by
  let k : ℕ := 2 ^ (s + 1)
  have hyx : y ≤ x := by omega
  have hknx : n < k * x := by
    exact lt_of_lt_of_le hstage (Nat.mul_le_mul_left k hyx)
  have hsumZ : (x : ℤ) + (y : ℤ) = (n : ℤ) := by exact_mod_cast hsum
  have hstageZ : (n : ℤ) < (k : ℤ) * (y : ℤ) := by exact_mod_cast hstage
  have hknxZ : (n : ℤ) < (k : ℤ) * (x : ℤ) := by exact_mod_cast hknx
  have hprod : 0 < ((k : ℤ) * (y : ℤ) - (n : ℤ)) *
      ((k : ℤ) * (x : ℤ) - (n : ℤ)) :=
    mul_pos (sub_pos.mpr hstageZ) (sub_pos.mpr hknxZ)
  have hz : (k : ℤ) * (k : ℤ) * ((x : ℤ) * (y : ℤ)) +
      (n : ℤ) * (n : ℤ) > (k : ℤ) * (n : ℤ) * (n : ℤ) := by
    calc
      (k : ℤ) * (n : ℤ) * (n : ℤ)
          < ((k : ℤ) * (y : ℤ) - (n : ℤ)) *
              ((k : ℤ) * (x : ℤ) - (n : ℤ)) +
              (k : ℤ) * (n : ℤ) * (n : ℤ) := by nlinarith
      _ = (k : ℤ) * (k : ℤ) * ((x : ℤ) * (y : ℤ)) +
              (n : ℤ) * (n : ℤ) := by
            rw [← hsumZ]
            ring
  rw [show 2 * s + 2 = (s + 1) + (s + 1) by omega, pow_add]
  change k * k * (x * y) + n * n > k * n * n
  exact_mod_cast hz

end Tri
