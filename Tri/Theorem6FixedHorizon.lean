/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Theorem6Parameters
import Tri.Lemma19FixedWindow

/-!
# Explicit logarithmic horizon for fixed Theorem 6

The activation clock and ordinary-Tri continuation clock have the same
`γ n log₂ n` factor.  This file collects their coefficients exactly.
-/

namespace Tri

/-- Absolute horizon coefficient after adding the fixed activation clock to
an ordinary-Tri clock with coefficient `C`. -/
def theorem6FixedHorizonCoeff
    (C : ℕ) : ℕ :=
  C + 10_240

/-- Exact collection of the fixed activation and ordinary-Tri horizons. -/
theorem theorem6FixedHorizon_eq
    (C n γ : ℕ) :
    ((2 * theorem6FixedCStar + 8192) *
          theorem6Q n γ * n) +
        C * γ * n * Nat.log 2 n =
      theorem6FixedHorizonCoeff C *
        γ * n * Nat.log 2 n := by
  norm_num [theorem6FixedHorizonCoeff,
    theorem6FixedCStar, theorem6Q]
  ring

end Tri

#print axioms Tri.theorem6FixedHorizon_eq
