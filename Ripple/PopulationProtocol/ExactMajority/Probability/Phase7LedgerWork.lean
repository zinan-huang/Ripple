/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Slot-7 ledger work adapter

Packages the ledger-based Phase-7 band survival into a single input structure
that `Theorem31.terminalWork` can consume directly.  This replaces the broken
`Phase7StageReady` path (whose static `phase7BandPool` is not one-step closed)
with the `Phase7LedgerStageReady` path (whose `MajorityBlockLedger` is
deterministically preserved under honest Phase-7 steps).

Axiom-clean (propext, Classical.choice, Quot.sound only).
-/

import Ripple.PopulationProtocol.ExactMajority.Probability.Phase7MajorityBlockLedger

namespace Ripple.PopulationProtocol.ExactMajority
namespace Phase7LedgerWork

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

variable {L K : ℕ}

/-- All inputs needed to produce the ledger-based Phase-7 band survival work
instance.  A value of this type replaces the old slot-7 section of
`PhaseWorkFamily.WorkFamilyData`. -/
structure Phase7LedgerWorkHypotheses (n : ℕ) where
  sigma : Sign
  l : ℕ
  G : ℕ
  hlL : l ≤ L
  hGpos : 1 ≤ G
  hGtop : 2 * G ≤ n * (n - 1)
  η : ℝ≥0∞
  hesc : Phase7MajorityBlockLedger.Phase7WinEscapeBound (L := L) (K := K) n η
  escapeε : ℝ≥0
  hescε :
    ((DriftSurvival.driftHorizon ((2 * G : ℕ) : ℝ) n n 6 : ℕ) : ℝ≥0∞) * η
      ≤ (escapeε : ℝ≥0∞)

/-- Build the ledger-based Phase-7 work instance from `Phase7LedgerWorkHypotheses`. -/
noncomputable def phase7LedgerWork
    {n : ℕ} (hn : 2 ≤ n)
    (F : Phase7LedgerWorkHypotheses (L := L) (K := K) n) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  Phase7MajorityBlockLedger.phase7LedgerBandsSurvival
    (L := L) (K := K) hn F.sigma F.l F.G F.hlL
    F.hGpos F.hGtop F.η F.hesc F.escapeε F.hescε

#print axioms phase7LedgerWork

end Phase7LedgerWork
end Ripple.PopulationProtocol.ExactMajority
