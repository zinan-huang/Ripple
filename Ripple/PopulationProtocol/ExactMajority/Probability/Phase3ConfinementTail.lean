
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Slot3ConfinementTailDischarge

Discharge `Phase035Work.Phase3ConfinementTail` from the landed
Theorem-6.2 / Main-profile confinement hour machinery.

`Phase035Work.lean` asks for a slot-3 tail to

  `allPhaseEq 3 n ∧ MainProfileConfinedToUseful`.

The landed confinement engine in `MainConfinementHours.lean` gives the global
Main confinement tail from per-hour squaring atoms:

* `MainHourSquaringHypotheses` carries the genuine per-hour probabilistic content:
  the gated one-step MGF drift `hdrift` and the optimized arithmetic `hbudget`;
* `hour_tail_of_squaring` turns one such atom into an hour-block tail;
* `main_confinement_tail_of_hour_squaring` composes the hour-block tails via the
  verified CK chain.

This file wraps those landed results into the exact `Phase3ConfinementTail` shape.
The final readout is strengthened to return both exact phase-3 window shape and
Main confinement.  That is the deterministic slot-shape bridge needed by the
faithful work family.

Uses only proved Lean terms and ordinary classical infrastructure.
-/

import Ripple.PopulationProtocol.ExactMajority.Probability.Phase035Work
import Ripple.PopulationProtocol.ExactMajority.Probability.MainConfinementHours

namespace Ripple.PopulationProtocol.ExactMajority

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal Real

namespace Phase3ConfinementTail

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/--
The landed hour-chain inputs sufficient to build the slot-3 confinement tail.

The genuine probabilistic content is exactly the family of
`MainExponentConfinement.MainHourSquaringHypotheses`s.  The remaining non-probabilistic
readout `hReadout` says that the final hour-good event implies the exact phase-3
window and the Main confinement predicate consumed by slot 3.
-/
structure Phase3ConfinementHourHypotheses (n : ℕ) where
  /-- Number of hour blocks in the Phase-3 confinement chain. -/
  H : ℕ

  /-- Length of each hour block. -/
  hourLen : ℕ → ℕ

  /-- Hour-good gates.  `Good 0` is the slot-3 entry gate; `Good H` is the final
  readout gate. -/
  Good : ℕ → Config (AgentState L K) → Prop

  /-- Per-hour failure budgets. -/
  ηhour : ℕ → ℝ≥0∞

  /-- The landed per-hour squaring atoms. -/
  atoms :
    ∀ i, i < H →
      MainExponentConfinement.MainHourSquaringHypotheses
        (L := L) (K := K)
        (hourLen i) (Good i) (Good (i + 1)) (ηhour i)

  /-- The slot-3 horizon. -/
  phase3to5Time : ℕ

  /-- The slot-3 horizon is the CK hour prefix. -/
  hTime : phase3to5Time = ChapmanKolmogorovChain.hourPrefix hourLen H

  /-- Exact phase-3 entry implies the initial hour-good gate. -/
  hGood0 :
    ∀ c, AdvanceEpidemics.allPhaseEq (L := L) (K := K) 3 n c →
      Good 0 c

  /-- Final readout: after all hours, the exact phase-3 shape and Main confinement hold. -/
  hReadout :
    ∀ c, Good H c →
      AdvanceEpidemics.allPhaseEq (L := L) (K := K) 3 n c ∧
        MainExponentConfinement.MainProfileConfinedToUseful
          (L := L) (K := K) c

  /-- Slot-3 failure budget. -/
  ε : ℝ≥0

  /-- Union budget for the per-hour tails. -/
  hBudget : (∑ i ∈ Finset.range H, ηhour i) ≤ (ε : ℝ≥0∞)

  /-- The assembled slot-3 horizon fits the locked aggregate `O(n log n)` phase budget. -/
  ht_le : phase3to5Time ≤ 17 * n * (L + 1)

/--
The slot-3 tail bound obtained from the landed hour-chain confinement engine.

This is the core wrapper: `ChapmanKolmogorovChain.ck_chain_bad_bound_lt` plus
`MainExponentConfinement.hour_tail_of_squaring` gives a tail for `¬ Good H`;
the readout `Good H → allPhaseEq 3 n ∧ MainProfileConfinedToUseful` converts it
to the exact `Phase3ConfinementTail` bad event.
-/
theorem phase3_confinement_tail_bound_of_hours
    {n : ℕ} (A : Phase3ConfinementHourHypotheses (L := L) (K := K) n) :
    ∀ c₀,
      AdvanceEpidemics.allPhaseEq (L := L) (K := K) 3 n c₀ →
      ((NonuniformMajority L K).transitionKernel ^ A.phase3to5Time) c₀
        {c | ¬
          (AdvanceEpidemics.allPhaseEq (L := L) (K := K) 3 n c ∧
            MainExponentConfinement.MainProfileConfinedToUseful
              (L := L) (K := K) c)}
        ≤ (A.ε : ℝ≥0∞) := by
  intro c₀ hEq0
  have hGood0 : A.Good 0 c₀ := A.hGood0 c₀ hEq0

  have hchain :
      ((NonuniformMajority L K).transitionKernel ^
          (ChapmanKolmogorovChain.hourPrefix A.hourLen A.H)) c₀
        {x | ¬ A.Good A.H x}
        ≤ ∑ i ∈ Finset.range A.H, A.ηhour i :=
    ChapmanKolmogorovChain.ck_chain_bad_bound_lt
      ((NonuniformMajority L K).transitionKernel)
      A.Good A.hourLen A.ηhour c₀ hGood0 A.H
      (fun i hi y hy =>
        MainExponentConfinement.hour_tail_of_squaring
          (L := L) (K := K) (A.atoms i hi) y hy)

  have hchainT :
      ((NonuniformMajority L K).transitionKernel ^ A.phase3to5Time) c₀
        {x | ¬ A.Good A.H x}
        ≤ ∑ i ∈ Finset.range A.H, A.ηhour i := by
    simpa [A.hTime] using hchain

  have hsub :
      {c : Config (AgentState L K) | ¬
        (AdvanceEpidemics.allPhaseEq (L := L) (K := K) 3 n c ∧
          MainExponentConfinement.MainProfileConfinedToUseful
            (L := L) (K := K) c)}
        ⊆ {c | ¬ A.Good A.H c} := by
    intro c hc hGood
    exact hc (A.hReadout c hGood)

  calc
    ((NonuniformMajority L K).transitionKernel ^ A.phase3to5Time) c₀
        {c | ¬
          (AdvanceEpidemics.allPhaseEq (L := L) (K := K) 3 n c ∧
            MainExponentConfinement.MainProfileConfinedToUseful
              (L := L) (K := K) c)}
        ≤ ((NonuniformMajority L K).transitionKernel ^ A.phase3to5Time) c₀
            {c | ¬ A.Good A.H c} :=
          measure_mono hsub
    _ ≤ ∑ i ∈ Finset.range A.H, A.ηhour i := hchainT
    _ ≤ (A.ε : ℝ≥0∞) := A.hBudget

/--
Concrete builder for `Phase035Work.Phase3ConfinementTail` from the landed
Main-confinement hour machinery.
-/
noncomputable def phase3ConfinementTail_of_hours
    {n : ℕ} (A : Phase3ConfinementHourHypotheses (L := L) (K := K) n) :
    Phase035Work.Phase3ConfinementTail (L := L) (K := K) n where
  t := A.phase3to5Time
  ht_le := A.ht_le
  ε := A.ε
  htail := phase3_confinement_tail_bound_of_hours
    (L := L) (K := K) A

/--
The corresponding concrete slot-3 work instance.
-/
noncomputable def phase3ConfinementWork_of_hours
    {n : ℕ} (A : Phase3ConfinementHourHypotheses (L := L) (K := K) n) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  Phase035Work.phase3ConfinementWork
    (L := L) (K := K)
    (phase3ConfinementTail_of_hours (L := L) (K := K) A)

/--
The corresponding legacy work atom, for the existing `WorkFromSlots` adapter.
-/
noncomputable def phase3WorkData_of_hours
    {n : ℕ} (A : Phase3ConfinementHourHypotheses (L := L) (K := K) n) :
    PhaseWorkFamily.Phase3WorkData (L := L) (K := K) n :=
  Phase035Work.phase3WorkData_of_tail
    (L := L) (K := K)
    (phase3ConfinementTail_of_hours (L := L) (K := K) A)

#print axioms phase3_confinement_tail_bound_of_hours
#print axioms phase3ConfinementTail_of_hours
#print axioms phase3ConfinementWork_of_hours
#print axioms phase3WorkData_of_hours

end Phase3ConfinementTail

end Ripple.PopulationProtocol.ExactMajority
