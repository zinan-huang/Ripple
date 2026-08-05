/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Theorem6InitialScale
import Mathlib.Data.Nat.Sqrt

/-!
# Initial label radius for the fixed activation route

The positive upper square root is the canonical smallest simple radius paying
the initial concentration square.  Only its physical bias room remains an
independent scalar condition.
-/

namespace Tri

noncomputable section

/-- Positive upper square root of the initial label variance volume. -/
def theorem6InitialRadius
    (q a : ℕ) : ℕ :=
  Nat.sqrt (q * (a + 1)) + 1

@[simp] theorem theorem6InitialRadius_pos
    (q a : ℕ) :
    1 ≤ theorem6InitialRadius q a := by
  simp [theorem6InitialRadius]

/-- The upper square root pays the initial Lemma 17 radius condition. -/
theorem theorem6InitialRadius_sq
    (q a : ℕ) :
    q * (a + 1) ≤
      theorem6InitialRadius q a ^ 2 := by
  exact Nat.le_of_lt (by
    simpa [theorem6InitialRadius] using
      Nat.lt_succ_sqrt' (q * (a + 1)))

/-- Initial radius facts consumed by the fixed prefix certificate. -/
structure Theorem6InitialRadiusFacts
    (q a cStar : ℕ) : Prop where
  hpositive :
    1 ≤ theorem6InitialRadius q a
  hroot :
    q * (a + 1) ≤
      theorem6InitialRadius q a ^ 2
  hbias :
    38 * cStar * theorem6InitialRadius q a ≤ a

/-- The explicit bias-room inequality is the sole remaining premise for the
canonical initial radius. -/
theorem theorem6InitialRadiusFacts
    (q a cStar : ℕ)
    (hbias :
      38 * cStar * theorem6InitialRadius q a ≤ a) :
    Theorem6InitialRadiusFacts q a cStar :=
  { hpositive := theorem6InitialRadius_pos q a
    hroot := theorem6InitialRadius_sq q a
    hbias := hbias }

end

end Tri

#print axioms Tri.theorem6InitialRadius_pos
#print axioms Tri.theorem6InitialRadius_sq
#print axioms Tri.theorem6InitialRadiusFacts
