/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Theorem6FixedDecisiveFit

/-!
# Polynomial capacity conditions for the decisive stage

The critical-scale floor capacity is hidden behind two exact
multiplication-only sufficient conditions.
-/

namespace Tri

noncomputable section

/-- The decisive reaction fit follows from two polynomial conditions that
retain one complete floor-division denominator. -/
theorem theorem6FixedCriticalReactionLower_fit_of_polynomial_capacity
    {n q cStar : ℕ}
    (hn : 0 < n)
    (hcStar : 0 < cStar)
    (hactive :
      4500 * q + 1200 * cStar ≤
        7 * theorem6FixedCriticalScale n)
    (hmean :
      1200 * cStar *
          ((2 * theorem6FixedCriticalScale n) ^ 3 +
            n ^ 2) ≤
        (7 * theorem6FixedCriticalScale n) * n ^ 2) :
    1200 * cStar *
        lemma17FixedReactionLower n q cStar
          (theorem6FixedCriticalScale n) ≤
      7 * theorem6FixedCriticalScale n := by
  let D := 1200 * cStar
  let B := 7 * theorem6FixedCriticalScale n
  let r := B ⌊/⌋ D
  let X := (2 * theorem6FixedCriticalScale n) ^ 3
  let N := n ^ 2
  have hD : 0 < D := by
    dsimp [D]
    positivity
  have hcapacity : D ≤ B := by
    dsimp [D, B]
    omega
  have hBUpper : B < D * (r + 1) := by
    have hdiv : B / D < r + 1 := by
      simp [r, Nat.floorDiv_eq_div]
    have h := (Nat.div_lt_iff_lt_mul hD).1 hdiv
    simpa [mul_comm] using h
  have hmeanFit : X ≤ r * N := by
    have hupper :
        B * N < D * (r * N + N) := by
      calc
        B * N < (D * (r + 1)) * N :=
          Nat.mul_lt_mul_of_pos_right hBUpper
            (Nat.pow_pos hn)
        _ = D * (r * N + N) := by ring
    have hmean' :
        D * (X + N) ≤ B * N := by
      simpa [D, B, X, N] using hmean
    have hstrict :
        D * (X + N) < D * (r * N + N) :=
      hmean'.trans_lt hupper
    have hcancel : X + N < r * N + N :=
      Nat.lt_of_mul_lt_mul_left hstrict
    omega
  have hactiveFit : 15 * q ≤ 4 * cStar * r := by
    have h4500 : 4500 * q < D * r := by
      have : 4500 * q + D < D * r + D := by
        calc
          4500 * q + D ≤ B := by
            simpa [D, B] using hactive
          _ < D * (r + 1) := hBUpper
          _ = D * r + D := by ring
      omega
    have h300 :
        300 * (15 * q) <
          300 * (4 * cStar * r) := by
      calc
        300 * (15 * q) = 4500 * q := by ring
        _ < D * r := h4500
        _ = 300 * (4 * cStar * r) := by
          dsimp [D]
          ring
    exact (Nat.lt_of_mul_lt_mul_left h300).le
  apply
    theorem6FixedCriticalReactionLower_fit_of_capacity
      hn hcStar
  · simpa [D, B] using hcapacity
  · simpa [X, N, r, B, D, mul_comm] using hmeanFit
  · simpa [r, B, D] using hactiveFit

end

end Tri

#print axioms
  Tri.theorem6FixedCriticalReactionLower_fit_of_polynomial_capacity
