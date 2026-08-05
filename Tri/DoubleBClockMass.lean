/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.DoubleBClockSplitArithmetic

/-!
# One-step masses for the two-branch Double-B clock

The normal branch counts `xy` and `yb` as fuel events.  Its constant lower
bound is valid only under the explicit free-`Y` mask.
-/

namespace Tri

open scoped ENNReal

/-- Exact mass of a fuel event (`xy` or `yb`) in one raw interaction. -/
theorem dbPairPMF_fuel_mass
    (x y b : ℕ) (h : 2 ≤ x + y + b) :
    dbPairPMF x y b h .xy + dbPairPMF x y b h .yb =
      (y * (x + b) : ℝ≥0∞) /
        (Nat.choose (x + y + b) 2 : ℝ≥0∞) := by
  simp only [dbPairPMF_apply, PairComp.weight]
  rw [ENNReal.div_add_div_same]
  congr 1
  exact_mod_cast doubleB_fuel_weight x y b

/-- On a normal/free-`Y` tick, a fuel event has probability at least `1/16`.
There is intentionally no unguarded version of this theorem. -/
theorem dbPairPMF_fuel_mass_ge_sixteenth
    {n x y b : ℕ}
    (hn : 2 ≤ n)
    (hinv : x + y + b = n)
    (hmaj : y ≤ x)
    (hnormal : n ≤ 16 * y) :
    (1 : ℝ≥0∞) / 16 ≤
      dbPairPMF x y b (by omega) .xy +
        dbPairPMF x y b (by omega) .yb := by
  rw [dbPairPMF_fuel_mass]
  rw [hinv]
  have hcross := doubleB_normal_fuel_cross hinv hmaj hnormal
  have hden0 : ((Nat.choose n 2 : ℕ) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hn).ne'
  have hdenTop : ((Nat.choose n 2 : ℕ) : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  rw [doubleB_fuel_weight] at hcross
  apply (ENNReal.le_div_iff_mul_le (Or.inl hden0) (Or.inl hdenTop)).2
  calc
    (1 : ℝ≥0∞) / 16 * (Nat.choose n 2 : ℝ≥0∞)
        = (Nat.choose n 2 : ℝ≥0∞) / 16 := by
            simp only [div_eq_mul_inv]
            ac_rfl
    _ ≤ (y * (x + b) : ℝ≥0∞) := by
          apply ENNReal.div_le_of_le_mul
          exact_mod_cast (by simpa [mul_comm] using hcross)

end Tri

#print axioms Tri.dbPairPMF_fuel_mass
#print axioms Tri.dbPairPMF_fuel_mass_ge_sixteenth
