/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.SingleBKernel

/-!
# Exact Single-B masses and effective-level updates

The fair `X+Y` branches contribute equally to the up and down masses.  Blank
resolution contributes the strict directional part.  These event-level facts
are the arithmetic interface for the later corrected geometric potential.
-/

namespace Tri

open scoped ENNReal

/-- The two level-up labels have doubled raw weight `xy + 2xb`. -/
theorem singleCompPMF_up_mass
    (x y b : ℕ) (h : 2 ≤ x + y + b) :
    singleCompPMF x y b h .xyToX + singleCompPMF x y b h .xb =
      ((x * y + 2 * (x * b) : ℕ) : ℝ≥0∞) /
        ((2 * Nat.choose (x + y + b) 2 : ℕ) : ℝ≥0∞) := by
  simp only [singleCompPMF_apply, SingleComp.weight]
  rw [ENNReal.div_add_div_same]
  simp only [mul_assoc]
  push_cast
  rfl

/-- The two level-down labels have doubled raw weight `xy + 2yb`. -/
theorem singleCompPMF_down_mass
    (x y b : ℕ) (h : 2 ≤ x + y + b) :
    singleCompPMF x y b h .xyToY + singleCompPMF x y b h .yb =
      ((x * y + 2 * (y * b) : ℕ) : ℝ≥0∞) /
        ((2 * Nat.choose (x + y + b) 2 : ℕ) : ℝ≥0∞) := by
  simp only [singleCompPMF_apply, SingleComp.weight]
  rw [ENNReal.div_add_div_same]
  simp only [mul_assoc]
  push_cast
  rfl

/-- `X+Y → X+B` raises the doubled effective level by one. -/
theorem single_next_xyToX_level (s : BiCfg) :
    (SingleComp.next s .xyToX).doubleLevel = s.doubleLevel + 1 := by
  change 2 * s.x + (s.b + 1) = 2 * s.x + s.b + 1
  omega

/-- `X+Y → Y+B` lowers the doubled effective level by one. -/
theorem single_next_xyToY_level (s : BiCfg) (hx : 1 ≤ s.x) :
    (SingleComp.next s .xyToY).doubleLevel + 1 = s.doubleLevel := by
  change 2 * (s.x - 1) + (s.b + 1) + 1 = 2 * s.x + s.b
  omega

/-- `X+B → 2X` raises the doubled effective level by one. -/
theorem single_next_xb_level (s : BiCfg) (hb : 1 ≤ s.b) :
    (SingleComp.next s .xb).doubleLevel = s.doubleLevel + 1 := by
  change 2 * (s.x + 1) + (s.b - 1) = 2 * s.x + s.b + 1
  omega

/-- `Y+B → 2Y` lowers the doubled effective level by one. -/
theorem single_next_yb_level (s : BiCfg) (hb : 1 ≤ s.b) :
    (SingleComp.next s .yb).doubleLevel + 1 = s.doubleLevel := by
  change 2 * s.x + (s.b - 1) + 1 = 2 * s.x + s.b
  omega

/-- The three homogeneous pair classes are level-inert. -/
theorem single_next_inert_level (s : BiCfg) :
    (SingleComp.next s .xx).doubleLevel = s.doubleLevel ∧
      (SingleComp.next s .yy).doubleLevel = s.doubleLevel ∧
      (SingleComp.next s .bb).doubleLevel = s.doubleLevel :=
  ⟨rfl, rfl, rfl⟩

/-- Unnormalized productive-pair weight with the common factor two removed. -/
def singleProductiveWeight (x y b : ℕ) : ℕ :=
  x * y + b * (x + y)

/-- Doubled numerator of the effective-level up mass. -/
def singleUpWeight (x y b : ℕ) : ℕ :=
  x * y + 2 * x * b

/-- Doubled numerator of the effective-level down mass. -/
def singleDownWeight (x y b : ℕ) : ℕ :=
  x * y + 2 * y * b

/-- A gap witness exposes the exact directional excess contributed by blanks. -/
theorem single_weights_of_gap
    {x y b d : ℕ} (hgap : y + d = x) :
    singleUpWeight x y b = singleProductiveWeight x y b + b * d ∧
      singleDownWeight x y b + b * d =
        singleProductiveWeight x y b := by
  subst x
  unfold singleUpWeight singleDownWeight singleProductiveWeight
  constructor <;> ring

/-- Up and down weights sum to twice the productive-pair weight. -/
theorem single_up_add_down_weight (x y b : ℕ) :
    singleUpWeight x y b + singleDownWeight x y b =
      2 * singleProductiveWeight x y b := by
  unfold singleUpWeight singleDownWeight singleProductiveWeight
  ring

end Tri

#print axioms Tri.singleCompPMF_up_mass
#print axioms Tri.singleCompPMF_down_mass
#print axioms Tri.single_weights_of_gap
#print axioms Tri.single_up_add_down_weight
