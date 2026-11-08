/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.MultiProductiveProgressLocal

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

end Tri.Multi

