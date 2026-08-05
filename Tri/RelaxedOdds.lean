/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Direction
import Tri.RelaxedStep

/-!
# Exact odds for the unequal-rate kernel

The unshifted phase invariant already implies the exact finite-population odds
condition.  This file exposes that implication without natural subtraction or
division.
-/

namespace Tri

open scoped ENNReal

/-- Removing one molecule from each side preserves the rate-weighted bias.

The slack form records the exact gain caused by the finite-population
`(x-1)/(y-1)` correction. -/
theorem relaxed_shifted_bias_of_unshifted
    {α β s : NNReal} {a b : ℕ}
    (hslack : α + s ≤ β)
    (hbias :
      β * (b + 1 : NNReal) ≤ α * (a + 1 : NNReal)) :
    β * (b : NNReal) + s ≤ α * (a : NNReal) := by
  rw [← add_le_add_iff_right α]
  calc
    β * (b : NNReal) + s + α
        = β * (b : NNReal) + (α + s) := by ac_rfl
    _ ≤ β * (b : NNReal) + β := add_le_add_right hslack _
    _ = β * (b + 1 : NNReal) := by
          ring
    _ ≤ α * (a + 1 : NNReal) := hbias
    _ = α * (a : NNReal) + α := by
          ring

/-- The non-slack form consumed by the geometric-drift layer. -/
theorem relaxed_shifted_bias
    {α β : NNReal} {a b : ℕ}
    (hαβ : α ≤ β)
    (hbias :
      β * (b + 1 : NNReal) ≤ α * (a + 1 : NNReal)) :
    β * (b : NNReal) ≤ α * (a : NNReal) := by
  have h := relaxed_shifted_bias_of_unshifted
    (α := α) (β := β) (s := 0) (a := a) (b := b)
    (by simpa using hαβ) hbias
  simpa using h

/-- The shifted count inequality is exactly the weighted inequality between the
two productive triple counts. -/
theorem relaxed_weighted_counts_le
    {α β : NNReal} {a b : ℕ}
    (hshift : β * (b : NNReal) ≤ α * (a : NNReal)) :
    β * (downCount a b : NNReal) ≤
      α * (upCount a b : NNReal) := by
  have ha :
      (2 : NNReal) * Nat.choose (a + 1) 2 =
        (a + 1 : NNReal) * a := by
    exact_mod_cast two_mul_choose_two_succ a
  have hb :
      (2 : NNReal) * Nat.choose (b + 1) 2 =
        (b + 1 : NNReal) * b := by
    exact_mod_cast two_mul_choose_two_succ b
  have hscaled :=
    mul_le_mul_right
      hshift ((a + 1 : NNReal) * (b + 1 : NNReal))
  have htwo :
      (2 : NNReal) * (β * (downCount a b : NNReal)) ≤
        2 * (α * (upCount a b : NNReal)) := by
    calc
      (2 : NNReal) * (β * (downCount a b : NNReal))
          = ((a + 1 : NNReal) * (b + 1 : NNReal)) *
              (β * (b : NNReal)) := by
                simp only [downCount, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
                calc
                  2 * (β * ((a + 1) * Nat.choose (b + 1) 2 : NNReal))
                      = β * (a + 1) *
                          (2 * (Nat.choose (b + 1) 2 : NNReal)) := by ring
                  _ = β * (a + 1) * ((b + 1) * b) := by rw [hb]
                  _ = (a + 1) * (b + 1) * (β * b) := by ring
      _ ≤ ((a + 1 : NNReal) * (b + 1 : NNReal)) *
            (α * (a : NNReal)) := hscaled
      _ = 2 * (α * (upCount a b : NNReal)) := by
            simp only [upCount, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
            calc
              (a + 1) * (b + 1) * (α * a)
                  = α * (b + 1) * ((a + 1) * a) := by ring
              _ = α * (b + 1) *
                    (2 * (Nat.choose (a + 1) 2 : NNReal)) := by rw [ha]
              _ = 2 * (α * (Nat.choose (a + 1) 2 * (b + 1) : NNReal)) := by
                    ring
  exact le_of_mul_le_mul_left htwo (by norm_num : (0 : NNReal) < 2)

/-- The rate-weighted raw down mass is dominated by the raw up mass whenever
the unshifted phase bias holds. -/
theorem relaxedTriStep_mass_bias
    (r : RelaxedRate) {β : NNReal} {a b : ℕ}
    (h : 3 ≤ (a + 1) + (b + 1))
    (hfireβ : r.fire ≤ β)
    (hbias :
      β * (b + 1 : NNReal) ≤ r.fire * (a + 1 : NNReal)) :
    (β : ℝ≥0∞) * relaxedTriStep r (a + 1) (b + 1) h a ≤
      relaxedTriStep r (a + 1) (b + 1) h (a + 2) := by
  have hshift := relaxed_shifted_bias hfireβ hbias
  have hcounts := relaxed_weighted_counts_le hshift
  have hcounts' :
      (β : ℝ≥0∞) * (downCount a b : ℝ≥0∞) ≤
        (r.fire : ℝ≥0∞) * (upCount a b : ℝ≥0∞) := by
    exact_mod_cast hcounts
  rw [relaxedTriStep_down, relaxedTriStep_up]
  calc
    (β : ℝ≥0∞) *
        (((a : ℝ≥0∞) + 1) * (Nat.choose (b + 1) 2 : ℝ≥0∞) /
          (Nat.choose ((a + 1) + (b + 1)) 3 : ℝ≥0∞))
        = ((β : ℝ≥0∞) * (downCount a b : ℝ≥0∞)) /
            (Nat.choose ((a + 1) + (b + 1)) 3 : ℝ≥0∞) := by
              simp only [downCount, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
              simp only [div_eq_mul_inv]
              ring
    _ ≤ ((r.fire : ℝ≥0∞) * (upCount a b : ℝ≥0∞)) /
          (Nat.choose ((a + 1) + (b + 1)) 3 : ℝ≥0∞) :=
      ENNReal.div_le_div_right hcounts' _
    _ = (r.fire : ℝ≥0∞) * (upCount a b : ℝ≥0∞) /
          (Nat.choose ((a + 1) + (b + 1)) 3 : ℝ≥0∞) := rfl

end Tri

#print axioms Tri.relaxed_shifted_bias_of_unshifted
#print axioms Tri.relaxedTriStep_mass_bias
