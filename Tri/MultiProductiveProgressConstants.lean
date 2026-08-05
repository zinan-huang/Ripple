/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.MultiProductiveProgressJoint

/-!
# Integer thresholds for a proper multi-species stage

The paper's fixed-pair target is `x-y ≥ 49D/48`, and completion (c) occurs
after `x0/2` productive reactions involving `X`.  Both are real thresholds;
their exact natural-number encodings use ceilings.
-/

namespace Tri.Multi

open scoped BigOperators ENNReal

variable {m n : ℕ}

/-- Least natural gap satisfying the paper's scaled target
`48 * gap ≥ 49 * D`. -/
def properPairTarget (D : ℕ) : ℕ :=
  (49 * D + 47) / 48

/-- The proper-stage target capped at the largest possible population gap,
as in the paper's `min(49D/48, n)`. -/
def properStageTarget (D n : ℕ) : ℕ :=
  min (properPairTarget D) n

/-- Least natural count at least the real threshold `x0 / 2`. -/
def properInvolvingTarget (x0 : ℕ) : ℕ :=
  (x0 + 1) / 2

@[simp] theorem properPairTarget_le_iff
    (D g : ℕ) :
    properPairTarget D ≤ g ↔ 49 * D ≤ 48 * g := by
  unfold properPairTarget
  omega

@[simp] theorem properInvolvingTarget_le_iff
    (x0 k : ℕ) :
    properInvolvingTarget x0 ≤ k ↔ x0 ≤ 2 * k := by
  unfold properInvolvingTarget
  omega

/-- The target written as the old gap plus the required one-forty-eighth
increment. -/
theorem properPairTarget_eq
    (D : ℕ) :
    properPairTarget D = D + (D + 47) / 48 := by
  unfold properPairTarget
  omega

theorem properPairTarget_ge
    (D : ℕ) :
    D ≤ properPairTarget D := by
  rw [properPairTarget_eq]
  omega

theorem properPairTarget_pos
    (D : ℕ) (hD : 1 ≤ D) :
    1 ≤ properPairTarget D := by
  exact hD.trans (properPairTarget_ge D)

theorem properStageTarget_le_pairTarget
    (D n : ℕ) :
    properStageTarget D n ≤ properPairTarget D := by
  exact Nat.min_le_left _ _

theorem properStageTarget_le_population
    (D n : ℕ) :
    properStageTarget D n ≤ n := by
  exact Nat.min_le_right _ _

theorem properStageTarget_ge
    (D n : ℕ) (hDn : D ≤ n) :
    D ≤ properStageTarget D n := by
  unfold properStageTarget
  exact le_min (properPairTarget_ge D) hDn

theorem properStageTarget_pos
    (D n : ℕ) (hD : 1 ≤ D) (hDn : D ≤ n) :
    1 ≤ properStageTarget D n := by
  exact hD.trans (properStageTarget_ge D n hDn)

/-- Exact equivalence between the paper's subtraction-free target and the
natural fixed-pair gap target. -/
theorem properPairTarget_le_gap_iff
    (c : Config m n) (X Y : Species m) (D : ℕ)
    (hYX : count c Y ≤ count c X) :
    properPairTarget D ≤ pairGapNat c X Y ↔
      48 * count c Y + 49 * D ≤ 48 * count c X := by
  rw [properPairTarget_le_iff]
  unfold pairGapNat
  omega

/-- Exact paper completion-(c) event in terms of the joint involvement
counter. -/
theorem properInvolvingTarget_le_joint_iff
    (x0 : ℕ) (q : ProductivePairJointState m n) :
    properInvolvingTarget x0 ≤ q.involving ↔
      x0 ≤ 2 * q.involving := by
  exact properInvolvingTarget_le_iff x0 q.involving

/-- Fixed-competitor completion-(c) tail with the paper's exact integer
thresholds and the protected half-gap parameter `D/2`. -/
theorem productivePairJointStop_completion_tail
    (h3 : 3 ≤ n) (X Y : Species m) (hXY : X ≠ Y)
    (D x0 T : ℕ) (hD4 : 4 ≤ D) (hDn : D ≤ n)
    (q0 : ProductivePairJointState m n) (hq0 : q0.CounterInv) :
    (∑' z : ProductivePairJointState m n,
      if pairGapNat z.config X Y < properPairTarget D ∧
          x0 ≤ 2 * z.involving then
        iter
          (productivePairJointStop h3 X Y (D / 2)
            (properPairTarget D))
          T q0 z
      else 0) ≤
      pairProgressPotential X Y
          (pairProgressTilt n (D / 2))
          (pairProgressFactor n (D / 2)) q0.toRelevant /
        (pairProgressTilt n (D / 2) ^ (properPairTarget D - 1) *
          (pairProgressFactor n (D / 2))⁻¹ ^
            properInvolvingTarget x0) := by
  simpa only [properInvolvingTarget_le_iff] using
    productivePairJointStop_involving_tail
      h3 X Y hXY (D / 2) (properPairTarget D)
      (properInvolvingTarget x0) T
      (by omega) (by omega) (properPairTarget_pos D (by omega))
      q0 hq0

end Tri.Multi

#print axioms Tri.Multi.properPairTarget_le_gap_iff
#print axioms Tri.Multi.productivePairJointStop_completion_tail
