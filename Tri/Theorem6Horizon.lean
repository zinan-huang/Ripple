/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Theorem6Parameters
import Tri.Lemma19PostWindow

/-!
# Explicit logarithmic horizon for fixed Theorem 6

The activation clock and ordinary-Tri continuation clock have the same
`γ n log₂ n` factor.  This file collects their coefficients exactly.
-/

namespace Tri

/-- Absolute horizon coefficient after adding the fixed activation clock to
an ordinary-Tri clock with coefficient `C`. -/
def theorem6HorizonCoeff
    (C : ℕ) : ℕ :=
  C + 10_240

/-- Exact collection of the fixed activation and ordinary-Tri horizons. -/
theorem theorem6Horizon_eq
    (C n γ : ℕ) :
    ((2 * theorem6CStar + 8192) *
          theorem6Q n γ * n) +
        C * γ * n * Nat.log 2 n =
      theorem6HorizonCoeff C *
        γ * n * Nat.log 2 n := by
  norm_num [theorem6HorizonCoeff,
    theorem6CStar, theorem6Q]
  ring

end Tri

#print axioms Tri.theorem6Horizon_eq
