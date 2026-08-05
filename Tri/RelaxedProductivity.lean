/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.ProdBound
import Tri.RelaxedCounting

/-!
# Productive interaction mass for unequal reaction rates

Slowing the favorable reaction by `r.fire` loses at most that same factor in
the total productive mass.  This makes the raw interaction-clock dependence on
the relaxation rate explicit.
-/

namespace Tri

open scoped ENNReal

/-- The relaxed favorable atom is the ordinary favorable atom multiplied by
the firing rate. -/
theorem relaxedTriStep_up_eq_fire_mul
    (r : RelaxedRate) (a y : ℕ) (h : 3 ≤ (a + 1) + y) :
    relaxedTriStep r (a + 1) y h (a + 2) =
      (r.fire : ℝ≥0∞) * triStep (a + 1) y h (a + 2) := by
  rw [relaxedTriStep_up, triStep_up]
  push_cast
  simp only [div_eq_mul_inv]
  ring

/-- The adverse atom is unchanged by relaxing only the favorable reaction. -/
theorem relaxedTriStep_down_eq
    (r : RelaxedRate) (a y : ℕ) (h : 3 ≤ (a + 1) + y) :
    relaxedTriStep r (a + 1) y h a =
      triStep (a + 1) y h a := by
  rw [relaxedTriStep_down, triStep_down]

/-- Relaxation loses at most the firing-rate factor in total productive mass. -/
theorem relaxed_productive_mass_ge_fire_mul
    (r : RelaxedRate) (a b : ℕ)
    (h : 3 ≤ (a + 1) + (b + 1)) :
    (r.fire : ℝ≥0∞) *
        (triStep (a + 1) (b + 1) h a +
          triStep (a + 1) (b + 1) h (a + 2)) ≤
      relaxedTriStep r (a + 1) (b + 1) h a +
        relaxedTriStep r (a + 1) (b + 1) h (a + 2) := by
  have hfireOne : (r.fire : ℝ≥0∞) ≤ 1 := by
    exact_mod_cast (show r.fire ≤ 1 by
      rw [← r.add_eq_one]
      exact le_add_right le_rfl)
  rw [relaxedTriStep_down_eq, relaxedTriStep_up_eq_fire_mul]
  calc
    (r.fire : ℝ≥0∞) *
          (triStep (a + 1) (b + 1) h a +
            triStep (a + 1) (b + 1) h (a + 2))
        = (r.fire : ℝ≥0∞) * triStep (a + 1) (b + 1) h a +
            (r.fire : ℝ≥0∞) * triStep (a + 1) (b + 1) h (a + 2) := by ring
    _ ≤ 1 * triStep (a + 1) (b + 1) h a +
          (r.fire : ℝ≥0∞) * triStep (a + 1) (b + 1) h (a + 2) := by
      gcongr
    _ = _ := by rw [one_mul]

/-- Every relaxed interior state has productive mass at least
`r.fire · (3/n)`. -/
theorem relaxed_productive_mass_ge_interior
    (r : RelaxedRate) (a b n : ℕ)
    (h3 : 3 ≤ n) (hpop : a + b + 2 = n) :
    (r.fire : ℝ≥0∞) * ((3 : ℝ≥0∞) / (n : ℝ≥0∞)) ≤
      relaxedTriStep r (a + 1) (b + 1) (by omega) a +
        relaxedTriStep r (a + 1) (b + 1) (by omega) (a + 2) := by
  calc
    (r.fire : ℝ≥0∞) * ((3 : ℝ≥0∞) / (n : ℝ≥0∞))
        ≤ (r.fire : ℝ≥0∞) *
            (triStep (a + 1) (b + 1) (by omega) a +
              triStep (a + 1) (b + 1) (by omega) (a + 2)) := by
          gcongr
          exact productive_mass_ge_interior a b n h3 hpop
    _ ≤ _ := relaxed_productive_mass_ge_fire_mul r a b (by omega)

end Tri

#print axioms Tri.relaxed_productive_mass_ge_fire_mul
#print axioms Tri.relaxed_productive_mass_ge_interior
