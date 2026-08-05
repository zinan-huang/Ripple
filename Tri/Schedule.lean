/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.PhaseGlue
import Tri.Phase3Horizon
import Tri.Phase2Reconciled

/-!
# The exact-horizon schedule

The reconciled ladder runs phase 1 for `C₁ γ n lg n`, phase 2 for
`8 n · phase2StageCount n γ`, and phase 3 for `16 γ n lg n` interactions.  Since
`phase2StageCount n γ ≤ lg n` and `1 ≤ γ`, the phase-2 block is at most
`8 γ n lg n`, so the three horizons sum to at most `(C₁ + 24) γ n lg n`.  The
`Theorem1b_statement` schedule input then holds with `C = C₁ + 24` by padding.
-/

namespace Tri

/-- The three reconciled phase horizons fit under `(C₁ + 24) γ n lg n`. -/
theorem reconciled_schedule (C₁ n γ : ℕ) (hγ : 1 ≤ γ) :
    ∃ U : ℕ,
      phase1Horizon C₁ n γ + 8 * n * phase2StageCount n γ
          + phase3HorizonScaled 16 n γ + U
        = (C₁ + 24) * γ * n * Nat.log 2 n := by
  refine Nat.le.dest ?_
  have hstage : 8 * n * phase2StageCount n γ ≤ 8 * γ * n * Nat.log 2 n := by
    calc 8 * n * phase2StageCount n γ
        ≤ 8 * n * Nat.log 2 n :=
          Nat.mul_le_mul_left _ (phase2StageCount_le_log n γ)
      _ = 8 * (n * Nat.log 2 n) := by ring
      _ ≤ 8 * (γ * (n * Nat.log 2 n)) :=
          Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (by omega))
      _ = 8 * γ * n * Nat.log 2 n := by ring
  have hsplit : (C₁ + 24) * γ * n * Nat.log 2 n
      = C₁ * γ * n * Nat.log 2 n + 8 * γ * n * Nat.log 2 n
        + 16 * γ * n * Nat.log 2 n := by ring
  rw [hsplit, phase1Horizon, phase3HorizonScaled]
  omega

end Tri

#print axioms Tri.reconciled_schedule
