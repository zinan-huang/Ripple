/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.RelaxedStrictOdds
import Mathlib.Tactic.FieldSimp

/-!
# Direction parameters for the unequal-rate productive chain

For an effective productive odds factor `B > 1`, these parameters make the
counted geometric potential harmonic.  The multiplier `eta > 1` converts a
lower bound on productive events into strict directional progress.
-/

namespace Tri

/-- Reciprocal effective odds. -/
noncomputable def relaxedDirU (B : NNReal) : NNReal :=
  1 / B

/-- Geometric level base. -/
noncomputable def relaxedDirW (B : NNReal) : NNReal :=
  2 / (B + 1)

/-- Reward per productive event. -/
noncomputable def relaxedDirEta (B : NNReal) : NNReal :=
  2 * (B + 1) ^ 2 / (B ^ 2 + 6 * B + 1)

/-- Exact harmonicity relation for the event-indexed potential. -/
theorem relaxedDir_relation (B : NNReal) (hB : 0 < B) :
    relaxedDirEta B *
        (relaxedDirU B + relaxedDirW B ^ 2) =
      relaxedDirW B * (relaxedDirU B + 1) := by
  have hB0 : B ≠ 0 := ne_of_gt hB
  have hB1 : B + 1 ≠ 0 := by positivity
  have hden : B ^ 2 + 6 * B + 1 ≠ 0 := by positivity
  unfold relaxedDirEta relaxedDirU relaxedDirW
  field_simp
  ring

/-- The reciprocal odds lie strictly below the geometric base. -/
theorem relaxedDir_u_lt_w
    {B : NNReal} (hB : 1 < B) :
    relaxedDirU B < relaxedDirW B := by
  unfold relaxedDirU relaxedDirW
  rw [div_lt_div_iff₀ (by positivity : (0 : NNReal) < B)
    (by positivity : (0 : NNReal) < B + 1)]
  simpa [two_mul, add_comm] using add_lt_add_left hB B

/-- The geometric base is strictly below one. -/
theorem relaxedDir_w_lt_one
    {B : NNReal} (hB : 1 < B) :
    relaxedDirW B < 1 := by
  unfold relaxedDirW
  rw [div_lt_iff₀ (by positivity : (0 : NNReal) < B + 1)]
  simp only [one_mul]
  have hh : (1 : NNReal) + 1 < 1 + B :=
    add_lt_add_right hB 1
  calc
    (2 : NNReal) = 1 + 1 := by norm_num
    _ < 1 + B := hh
    _ = B + 1 := by ac_rfl

/-- The productive-event reward is genuinely larger than one. -/
theorem relaxedDir_eta_gt_one
    {B : NNReal} (hB : 1 < B) :
    1 < relaxedDirEta B := by
  unfold relaxedDirEta
  rw [lt_div_iff₀
    (by positivity : (0 : NNReal) < B ^ 2 + 6 * B + 1)]
  have hBR : (1 : ℝ) < (B : ℝ) := by exact_mod_cast hB
  have hsquare : 0 < ((B : ℝ) - 1) ^ 2 :=
    sq_pos_of_pos (sub_pos.mpr hBR)
  have hreal :
      (B : ℝ) ^ 2 + 6 * B + 1 <
        2 * ((B : ℝ) + 1) ^ 2 := by
    nlinarith [hsquare]
  simp only [one_mul]
  exact_mod_cast hreal

/-- The level base is no larger than the productive-event reward. -/
theorem relaxedDir_w_le_eta
    {B : NNReal} (hB : 1 < B) :
    relaxedDirW B ≤ relaxedDirEta B :=
  le_of_lt ((relaxedDir_w_lt_one hB).trans (relaxedDir_eta_gt_one hB))

end Tri

#print axioms Tri.relaxedDir_relation
#print axioms Tri.relaxedDir_u_lt_w
#print axioms Tri.relaxedDir_w_lt_one
#print axioms Tri.relaxedDir_eta_gt_one
#print axioms Tri.relaxedDir_w_le_eta
