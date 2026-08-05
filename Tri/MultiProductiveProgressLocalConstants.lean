/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.MultiProductiveProgressLocalJoint

/-!
# Proper-stage local progress constants

This instantiates the locally stopped joint progress theorem at the paper's
protected half-gap, fixed-pair target, and involvement threshold.
-/

namespace Tri.Multi

open scoped BigOperators ENNReal

variable {m n : ℕ}

theorem properStageScale_pos
    (x0 : ℕ) (hx0 : 1 ≤ x0) :
    0 < properStageScale x0 := by
  unfold properStageScale
  omega

theorem halfGap_le_properStageScale
    (D x0 : ℕ) (hDx0 : D ≤ x0) :
    D / 2 ≤ properStageScale x0 := by
  unfold properStageScale
  omega

/-- Fixed-competitor completion-(c) tail at the proper-stage local scale. -/
theorem productivePairJointLocalStop_completion_tail
    (h3 : 3 ≤ n) (X Y : Species m) (hXY : X ≠ Y)
    (D x0 T : ℕ) (hD4 : 4 ≤ D) (hDx0 : D ≤ x0)
    (q0 : ProductivePairJointState m n) (hq0 : q0.CounterInv) :
    (∑' z : ProductivePairJointState m n,
      if pairGapNat z.config X Y < properPairTarget D ∧
          x0 ≤ 2 * z.involving then
        iter
          (productivePairJointLocalStop h3 X Y
            (properStageScale x0) (D / 2) (properPairTarget D))
          T q0 z
      else 0) ≤
      pairProgressPotential X Y
          (pairProgressTilt (properStageScale x0) (D / 2))
          (pairProgressFactor (properStageScale x0) (D / 2))
          q0.toRelevant /
        (pairProgressTilt (properStageScale x0) (D / 2) ^
            (properPairTarget D - 1) *
          (pairProgressFactor (properStageScale x0) (D / 2))⁻¹ ^
            properInvolvingTarget x0) := by
  simpa only [properInvolvingTarget_le_iff] using
    productivePairJointLocalStop_involving_tail
      h3 X Y hXY (properStageScale x0) (D / 2)
      (properPairTarget D) (properInvolvingTarget x0) T
      (properStageScale_pos x0 (by omega)) (by omega)
      (halfGap_le_properStageScale D x0 hDx0)
      (properPairTarget_pos D (by omega)) q0 hq0

/-- At a fresh stage state, the numerator of the local progress tail is
exactly the initial gap tilt. -/
theorem pairProgressPotential_fresh
    (X Y : Species m) (S d D : ℕ)
    (q0 : ProductivePairJointState m n)
    (hgap0 : pairGapNat q0.config X Y = D)
    (hrelevant0 : q0.relevant = 0) :
    pairProgressPotential X Y
        (pairProgressTilt S d) (pairProgressFactor S d) q0.toRelevant =
      pairProgressTilt S d ^ D := by
  simp [pairProgressPotential, ProductivePairJointState.toRelevant,
    hgap0, hrelevant0]

/-- Proper-stage completion-(c) tail with the fresh-stage numerator exposed
as a scalar power. -/
theorem productivePairJointLocalStop_completion_tail_fresh
    (h3 : 3 ≤ n) (X Y : Species m) (hXY : X ≠ Y)
    (D x0 T : ℕ) (hD4 : 4 ≤ D) (hDx0 : D ≤ x0)
    (q0 : ProductivePairJointState m n) (hq0 : q0.CounterInv)
    (hgap0 : pairGapNat q0.config X Y = D)
    (hrelevant0 : q0.relevant = 0) :
    (∑' z : ProductivePairJointState m n,
      if pairGapNat z.config X Y < properPairTarget D ∧
          x0 ≤ 2 * z.involving then
        iter
          (productivePairJointLocalStop h3 X Y
            (properStageScale x0) (D / 2) (properPairTarget D))
          T q0 z
      else 0) ≤
      pairProgressTilt (properStageScale x0) (D / 2) ^ D /
        (pairProgressTilt (properStageScale x0) (D / 2) ^
            (properPairTarget D - 1) *
          (pairProgressFactor (properStageScale x0) (D / 2))⁻¹ ^
            properInvolvingTarget x0) := by
  simpa [pairProgressPotential_fresh X Y
      (properStageScale x0) (D / 2) D q0 hgap0 hrelevant0] using
    productivePairJointLocalStop_completion_tail
      h3 X Y hXY D x0 T hD4 hDx0 q0 hq0

end Tri.Multi

#print axioms Tri.Multi.productivePairJointLocalStop_completion_tail
#print axioms Tri.Multi.productivePairJointLocalStop_completion_tail_fresh
