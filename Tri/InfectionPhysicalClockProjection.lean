/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Lemma16To19Clock

/-!
# Projecting the frozen physical clock to the infection chain

The identity-refined physical kernel is an exact refinement of the ordinary
infection kernel.  Since the final activation checkpoint depends only on the
coarse state, this exact projection persists after freezing and at every
finite horizon.
-/

namespace Tri

open scoped ENNReal

noncomputable section

/-- Coarse form of the range-strengthened positive-gap endpoint. -/
def InfectionActivationGapRangeGood
    {n : ℕ} (A targetGap : ℕ)
    (s : InfectionState n) : Prop :=
  A ≤ s.1.active ∧
    s.1.active ≤ A + 1 ∧
    s.1.ay + targetGap ≤ s.1.ax

noncomputable instance infectionActivationGapRangeGoodDecidable
    {n : ℕ} (A targetGap : ℕ) :
    DecidablePred (@InfectionActivationGapRangeGood n A targetGap) :=
  Classical.decPred _

/-- The physical endpoint is exactly the pullback of its coarse form. -/
@[simp] theorem lemma19PhysicalStageRangeGood_iff_coarse
    {n : ℕ} (A targetGap : ℕ)
    (s : InfectionRevealPhysicalState n) :
    Lemma19PhysicalStageRangeGood A targetGap s ↔
      InfectionActivationGapRangeGood A targetGap
        (infectionRevealPhysicalForget s) :=
  Iff.rfl

/-- Freezing on the final activation checkpoint preserves the exact physical
to coarse intertwining. -/
theorem infectionRevealPhysicalStep_freeze_intertwines
    (n : ℕ) (h3 : 3 ≤ n) (targetGap : ℕ) :
    Intertwines infectionRevealPhysicalForget
      (freeze
        (Lemma19PhysicalStageRangeGood n targetGap)
        (infectionRevealPhysicalStep n h3))
      (freeze
        (InfectionActivationGapRangeGood n targetGap)
        (infectionStateStep n h3)) := by
  simpa only [lemma19PhysicalStageRangeGood_iff_coarse] using
    (infectionRevealPhysicalStep_intertwines n h3).onFreeze
      (InfectionActivationGapRangeGood n targetGap)

/-- At every frozen horizon, the physical and coarse endpoint laws agree
after forgetting identity data. -/
theorem infectionRevealPhysicalStep_iter_freeze_map_forget
    (n : ℕ) (h3 : 3 ≤ n) (targetGap T : ℕ)
    (s : InfectionRevealPhysicalState n) :
    (iter
        (freeze
          (Lemma19PhysicalStageRangeGood n targetGap)
          (infectionRevealPhysicalStep n h3))
        T s).map infectionRevealPhysicalForget =
      iter
        (freeze
          (InfectionActivationGapRangeGood n targetGap)
          (infectionStateStep n h3))
        T (infectionRevealPhysicalForget s) :=
  iter_map_of_intertwines
    (infectionRevealPhysicalStep_freeze_intertwines
      n h3 targetGap)
    T s

/-- The physical and coarse frozen chains have exactly the same failure mass
at the final activation checkpoint. -/
theorem infectionRevealPhysicalStep_iter_freeze_failure_eq
    (n : ℕ) (h3 : 3 ≤ n) (targetGap T : ℕ)
    (s : InfectionRevealPhysicalState n) :
    terminalFailureMass
        (iter
          (freeze
            (Lemma19PhysicalStageRangeGood n targetGap)
            (infectionRevealPhysicalStep n h3))
          T s)
        (Lemma19PhysicalStageRangeGood n targetGap)
      =
    terminalFailureMass
        (iter
          (freeze
            (InfectionActivationGapRangeGood n targetGap)
            (infectionStateStep n h3))
          T (infectionRevealPhysicalForget s))
        (InfectionActivationGapRangeGood n targetGap) := by
  let μ :=
    iter
      (freeze
        (Lemma19PhysicalStageRangeGood n targetGap)
        (infectionRevealPhysicalStep n h3))
      T s
  calc
    terminalFailureMass μ
        (Lemma19PhysicalStageRangeGood n targetGap) =
      terminalFailureMass μ
        (fun z =>
          InfectionActivationGapRangeGood n targetGap
            (infectionRevealPhysicalForget z)) := rfl
    _ =
      terminalFailureMass
        (μ.map infectionRevealPhysicalForget)
        (InfectionActivationGapRangeGood n targetGap) :=
      (terminalFailureMass_map μ infectionRevealPhysicalForget
        (InfectionActivationGapRangeGood n targetGap)).symm
    _ =
      terminalFailureMass
        (iter
          (freeze
            (InfectionActivationGapRangeGood n targetGap)
            (infectionStateStep n h3))
          T (infectionRevealPhysicalForget s))
        (InfectionActivationGapRangeGood n targetGap) := by
      rw [infectionRevealPhysicalStep_iter_freeze_map_forget]

end

end Tri

#print axioms Tri.lemma19PhysicalStageRangeGood_iff_coarse
#print axioms Tri.infectionRevealPhysicalStep_freeze_intertwines
#print axioms Tri.infectionRevealPhysicalStep_iter_freeze_map_forget
#print axioms Tri.infectionRevealPhysicalStep_iter_freeze_failure_eq
