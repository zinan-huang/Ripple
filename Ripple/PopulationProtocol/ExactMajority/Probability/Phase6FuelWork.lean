/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Slot-6 fuel work adapter

Packages the fuel-based Phase-6 drift survival into a single input structure
that `Theorem31.terminalWork` can consume directly.  This replaces the broken
`Phase6DrainReady` path (whose `mainFloor` makes the postcondition empty)
with the `Phase6FuelReady` path (whose `FuelLedger` is deterministically
preserved and compatible with `highMass = 0`).

Axiom-clean (propext, Classical.choice, Quot.sound only).
-/

import Ripple.PopulationProtocol.ExactMajority.Probability.Phase6FuelSurvival

namespace Ripple.PopulationProtocol.ExactMajority
namespace Phase6FuelWork

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

variable {L K : ℕ}

/-- All inputs needed to produce the fuel-based Phase-6 drift survival work
instance.  A value of this type replaces the old slot-6 section of
`PhaseWorkFamily.WorkFamilyData`. -/
structure Phase6FuelWorkHypotheses (n : ℕ) where
  D : ℕ
  hD : 1 ≤ D
  l : ℕ
  i : Fin (L + 1)
  K₀ : ℕ
  hK₀ : 1 ≤ K₀
  hK₀n : K₀ ≤ n
  hhgt : l - 1 < i.val
  hhne : i.val ≠ L
  η : ℝ≥0∞
  hesc : Phase6FuelSurvival.Phase6WinEscapeBound (L := L) (K := K) n η
  escapeε : ℝ≥0
  hescε :
    ((DriftSurvival.driftHorizon (K₀ : ℝ) n
        (Phase6PhiPotential.phase6PhiMax n l) D : ℕ) : ℝ≥0∞) * η
      ≤ (escapeε : ℝ≥0∞)

/-- Build the fuel-based Phase-6 work instance from `Phase6FuelWorkHypotheses`. -/
noncomputable def phase6FuelWork
    {n : ℕ} (hn : 2 ≤ n)
    (F : Phase6FuelWorkHypotheses (L := L) (K := K) n) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  Phase6FuelSurvival.phase6FuelSurvival
    (L := L) (K := K) hn F.D F.hD F.l F.i F.K₀ F.hK₀ F.hK₀n
    F.hhgt F.hhne F.η F.hesc F.escapeε F.hescε

#print axioms phase6FuelWork

end Phase6FuelWork
end Ripple.PopulationProtocol.ExactMajority
