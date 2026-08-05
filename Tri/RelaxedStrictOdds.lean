/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.RelaxedOdds

/-!
# Strict finite-population odds for unequal reaction rates

The gap between the favorable firing rate and the paper's comparison
parameter can be converted into a uniform extra odds factor on a finite band.
The statement is subtraction-free: `tau * bHi ≤ slack` is the only interface
later constant arithmetic needs.
-/

namespace Tri

open scoped ENNReal

/-- On `b ≤ bHi`, unused rate slack strengthens the productive up/down odds
from `beta` to `beta + tau`. -/
theorem relaxedTriStep_mass_bias_strong_on_band
    (r : RelaxedRate) {beta s tau : NNReal} {a b bHi : ℕ}
    (h : 3 ≤ (a + 1) + (b + 1))
    (hslack : r.fire + s ≤ beta)
    (hbias :
      beta * (b + 1 : NNReal) ≤
        r.fire * (a + 1 : NNReal))
    (hb : b ≤ bHi)
    (htau : tau * (bHi : NNReal) ≤ s) :
    ((beta + tau : NNReal) : ℝ≥0∞) *
        relaxedTriStep r (a + 1) (b + 1) h a ≤
      relaxedTriStep r (a + 1) (b + 1) h (a + 2) := by
  have hshift :
      beta * (b : NNReal) + s ≤
        r.fire * (a : NNReal) :=
    relaxed_shifted_bias_of_unshifted hslack hbias
  have heff :
      (beta + tau) * (b : NNReal) ≤
        r.fire * (a : NNReal) := by
    calc
      (beta + tau) * (b : NNReal)
          = beta * b + tau * b := by ring
      _ ≤ beta * b + tau * bHi := by
            gcongr
      _ ≤ beta * b + s := by
            gcongr
      _ ≤ r.fire * a := hshift
  have hcounts := relaxed_weighted_counts_le heff
  have hcounts' :
      ((beta + tau : NNReal) : ℝ≥0∞) *
          (downCount a b : ℝ≥0∞) ≤
        (r.fire : ℝ≥0∞) *
          (upCount a b : ℝ≥0∞) := by
    exact_mod_cast hcounts
  rw [relaxedTriStep_down, relaxedTriStep_up]
  calc
    ((beta + tau : NNReal) : ℝ≥0∞) *
        (((a : ℝ≥0∞) + 1) * (Nat.choose (b + 1) 2 : ℝ≥0∞) /
          (Nat.choose ((a + 1) + (b + 1)) 3 : ℝ≥0∞))
        = (((beta + tau : NNReal) : ℝ≥0∞) *
            (downCount a b : ℝ≥0∞)) /
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

#print axioms Tri.relaxedTriStep_mass_bias_strong_on_band
