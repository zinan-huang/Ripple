/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.RelaxedKernel

/-!
# Exact atom masses for the unequal-rate interaction kernel

Interior states are written with `x = a + 1`.  The firing and idle outcomes of
an `xxy` sample remain separate in the raw interaction chain.
-/

namespace Tri

open scoped ENNReal

/-- Exact mass of the reaction that increases the `X` count. -/
theorem relaxedTriStep_up
    (r : RelaxedRate) (a y : ℕ) (h : 3 ≤ (a + 1) + y) :
    relaxedTriStep r (a + 1) y h (a + 2) =
      (r.fire : ℝ≥0∞) * (Nat.choose (a + 1) 2 * y : ℕ) /
        (Nat.choose ((a + 1) + y) 3 : ℝ≥0∞) := by
  unfold relaxedTriStep
  rw [PMF.map_apply, tsum_fintype]
  rw [show (Finset.univ : Finset RelaxedTripleKind) =
    {RelaxedTripleKind.xxx, RelaxedTripleKind.xxyFire,
      RelaxedTripleKind.xxyIdle, RelaxedTripleKind.xyyFire,
      RelaxedTripleKind.yyy} from rfl]
  simp [RelaxedTripleKind.nextX, RelaxedTripleKind.weight,
    relaxedInteractionPMF]

/-- Exact mass of the reaction that decreases the `X` count. -/
theorem relaxedTriStep_down
    (r : RelaxedRate) (a y : ℕ) (h : 3 ≤ (a + 1) + y) :
    relaxedTriStep r (a + 1) y h a =
      ((a + 1) * Nat.choose y 2 : ℝ≥0∞) /
        (Nat.choose ((a + 1) + y) 3 : ℝ≥0∞) := by
  unfold relaxedTriStep
  rw [PMF.map_apply, tsum_fintype]
  rw [show (Finset.univ : Finset RelaxedTripleKind) =
    {RelaxedTripleKind.xxx, RelaxedTripleKind.xxyFire,
      RelaxedTripleKind.xxyIdle, RelaxedTripleKind.xyyFire,
      RelaxedTripleKind.yyy} from rfl]
  simp [RelaxedTripleKind.nextX, RelaxedTripleKind.weight,
    relaxedInteractionPMF, show a ≠ a + 1 + 1 by omega]

/-- Exact self-loop mass: homogeneous triples together with the idle `xxy`
outcome. -/
theorem relaxedTriStep_stay
    (r : RelaxedRate) (a y : ℕ) (h : 3 ≤ (a + 1) + y) :
    relaxedTriStep r (a + 1) y h (a + 1) =
      ((Nat.choose (a + 1) 3 : ℝ≥0∞) +
          (r.idle : ℝ≥0∞) * (Nat.choose (a + 1) 2 * y : ℕ) +
          (Nat.choose y 3 : ℝ≥0∞)) /
        (Nat.choose ((a + 1) + y) 3 : ℝ≥0∞) := by
  unfold relaxedTriStep
  rw [PMF.map_apply, tsum_fintype]
  rw [show (Finset.univ : Finset RelaxedTripleKind) =
    {RelaxedTripleKind.xxx, RelaxedTripleKind.xxyFire,
      RelaxedTripleKind.xxyIdle, RelaxedTripleKind.xyyFire,
      RelaxedTripleKind.yyy} from rfl]
  simp [RelaxedTripleKind.nextX, RelaxedTripleKind.weight,
    relaxedInteractionPMF]
  simp only [div_eq_mul_inv]
  ring

/-- All-`X` consensus is absorbing for every admissible relaxed rate. -/
theorem relaxedTriStep_consensus_X
    (r : RelaxedRate) (x : ℕ) (h : 3 ≤ x + 0) :
    relaxedTriStep r x 0 h = PMF.pure x := by
  have h' : 3 ≤ x := by omega
  have hne : ((Nat.choose x 3 : ℕ) : ℝ≥0∞) ≠ 0 :=
    Nat.cast_ne_zero.mpr (choose_three_pos h').ne'
  have htop : ((Nat.choose x 3 : ℕ) : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  ext z
  unfold relaxedTriStep
  rw [PMF.map_apply, tsum_fintype]
  rw [show (Finset.univ : Finset RelaxedTripleKind) =
    {RelaxedTripleKind.xxx, RelaxedTripleKind.xxyFire,
      RelaxedTripleKind.xxyIdle, RelaxedTripleKind.xyyFire,
      RelaxedTripleKind.yyy} from rfl]
  rcases eq_or_ne z x with rfl | hz
  · simp [RelaxedTripleKind.nextX, RelaxedTripleKind.weight,
      relaxedInteractionPMF, PMF.pure_apply, ENNReal.div_self hne htop]
  · simp [RelaxedTripleKind.nextX, RelaxedTripleKind.weight,
      relaxedInteractionPMF, PMF.pure_apply, hz]

/-- All-`Y` consensus is absorbing for every admissible relaxed rate. -/
theorem relaxedTriStep_consensus_Y
    (r : RelaxedRate) (y : ℕ) (h : 3 ≤ 0 + y) :
    relaxedTriStep r 0 y h = PMF.pure 0 := by
  have h' : 3 ≤ y := by omega
  have hne : ((Nat.choose y 3 : ℕ) : ℝ≥0∞) ≠ 0 :=
    Nat.cast_ne_zero.mpr (choose_three_pos h').ne'
  have htop : ((Nat.choose y 3 : ℕ) : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  ext z
  unfold relaxedTriStep
  rw [PMF.map_apply, tsum_fintype]
  rw [show (Finset.univ : Finset RelaxedTripleKind) =
    {RelaxedTripleKind.xxx, RelaxedTripleKind.xxyFire,
      RelaxedTripleKind.xxyIdle, RelaxedTripleKind.xyyFire,
      RelaxedTripleKind.yyy} from rfl]
  rcases eq_or_ne z 0 with rfl | hz
  · simp [RelaxedTripleKind.nextX, RelaxedTripleKind.weight,
      relaxedInteractionPMF, PMF.pure_apply, ENNReal.div_self hne htop]
  · simp [RelaxedTripleKind.nextX, RelaxedTripleKind.weight,
      relaxedInteractionPMF, PMF.pure_apply, hz]

end Tri

#print axioms Tri.relaxedTriStep_up
#print axioms Tri.relaxedTriStep_down
#print axioms Tri.relaxedTriStep_stay
#print axioms Tri.relaxedTriStep_consensus_X
#print axioms Tri.relaxedTriStep_consensus_Y
