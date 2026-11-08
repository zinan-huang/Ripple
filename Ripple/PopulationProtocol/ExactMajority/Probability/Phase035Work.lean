
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# WorkConcreteSlots

Expose concrete public constructors for the remaining slot-0 / slot-3 / slot-5
work positions used by `WorkFromSlots`.

The previous `PhaseWorkFamily.WorkFamilyData` still carried three narrow work
atoms:

* slot 0: C0 role-split work;
* slot 3: Main exponent confinement work;
* slot 5: corrected slot-5 sampling / C5a work.

This file replaces those three carried work atoms by explicit `PhaseConvergenceW`
constructors.  Each constructor is parameterized by exactly the genuine tail bound
that its proof surface needs:

* `Phase0RoleSplitTail`: C0 role-split / floor tail;
* `Phase3ConfinementTail`: Theorem-6.2 main-confinement tail;
* `Phase5C5aTail`: corrected slot-5 tail, to be instantiated from the C5a package.

It also gives a `WorkFamilyTailData → PhaseWorkFamily.WorkFamilyData`
adapter, so all downstream `WorkFromSlots` machinery keeps working.

Important boundary:

`WorkShapeTies` is not fully definitional for the current committed work
family.  Slot 4’s landed `phase4Convergence` has
`Post = StableTie4 ∨ advFinished n`, not an exact `allPhaseEq` window, so a
same-shape exact-window tie is a real wiring obligation.  We therefore keep the
remaining post/pre seam-shape surface as one explicit `WorkWindowShape`,
while proving the deterministic slot-10 post bridge.

Uses only proved Lean terms and ordinary classical infrastructure.
-/

import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseWorkFamily
import Ripple.PopulationProtocol.ExactMajority.Probability.MainExponentConfinement

namespace Ripple.PopulationProtocol.ExactMajority

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal Real

namespace Phase035Work

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-! ## Slot 0 — C0 role-split work from the C0 tail atom -/

/--
The genuine C0 role-split tail needed for slot 0.

This is the reviewed C0 probability content: from a valid phase-0 initial window,
after `t` steps the chain reaches the exact phase-0 role-split postcondition except
with probability `ε`.

The postcondition is strengthened with `allPhaseEq 0 n`, so the seam post-window
tie for slot 0 is deterministic.
-/
structure Phase0RoleSplitTail (n : ℕ) where
  /-- Role-split slack parameter. -/
  η : ℝ
  /-- Phase-0 role-split horizon. -/
  t : ℕ
  /-- Slot-0 horizon fits the locked aggregate `O(n log n)` phase budget. -/
  ht_le : t ≤ 17 * n * (L + 1)
  /-- Phase-0 role-split failure budget. -/
  ε : ℝ≥0
  /-- C0 tail: role split plus exact phase-0 post-window. -/
  htail :
    ∀ c₀,
      RoleSplitConcentration.Phase0Initial (L := L) (K := K) n c₀ →
      ((NonuniformMajority L K).transitionKernel ^ t) c₀
        {c | ¬
          (AdvanceEpidemics.allPhaseEq (L := L) (K := K) 0 n c ∧
            RoleSplitConcentration.RoleSplitGood (L := L) (K := K) η n c)}
        ≤ (ε : ℝ≥0∞)

/-- Slot-0 `PhaseConvergenceW` from the explicit C0 tail. -/
noncomputable def phase0RoleSplitWork
    {n : ℕ} (A : Phase0RoleSplitTail (L := L) (K := K) n) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel where
  Pre c := RoleSplitConcentration.Phase0Initial (L := L) (K := K) n c
  Post c :=
    AdvanceEpidemics.allPhaseEq (L := L) (K := K) 0 n c ∧
      RoleSplitConcentration.RoleSplitGood (L := L) (K := K) A.η n c
  t := A.t
  ε := A.ε
  convergence := A.htail

/-- Package slot 0 as the legacy narrow `Phase0WorkData`. -/
noncomputable def phase0WorkData_of_tail
    {n : ℕ} (A : Phase0RoleSplitTail (L := L) (K := K) n) :
    PhaseWorkFamily.Phase0WorkData (L := L) (K := K) n where
  work := phase0RoleSplitWork (L := L) (K := K) A
  hPre := by
    intro c hc
    change RoleSplitConcentration.Phase0Initial (L := L) (K := K) n c
    exact hc
  hPostEq := by
    intro c hc
    exact hc.1

/-! ## Slot 3 — Main exponent confinement work from the confinement tail -/

/--
The slot-3 main-confinement tail.

This is the direct `PhaseConvergenceW` surface for Theorem 6.2 / main profile
confinement.  The landed `MainExponentConfinement.theorem6_2_main_confinement_whp`
is the intended source of `htail`, together with the exact phase-window part of
the slot-3 construction.
-/
structure Phase3ConfinementTail (n : ℕ) where
  /-- Slot-3 confinement horizon. -/
  t : ℕ
  /-- Slot-3 horizon fits the locked aggregate `O(n log n)` phase budget. -/
  ht_le : t ≤ 17 * n * (L + 1)
  /-- Slot-3 confinement failure budget. -/
  ε : ℝ≥0
  /-- Tail to exact phase-3 plus main-profile confinement. -/
  htail :
    ∀ c₀,
      AdvanceEpidemics.allPhaseEq (L := L) (K := K) 3 n c₀ →
      ((NonuniformMajority L K).transitionKernel ^ t) c₀
        {c | ¬
          (AdvanceEpidemics.allPhaseEq (L := L) (K := K) 3 n c ∧
            MainExponentConfinement.MainProfileConfinedToUseful
              (L := L) (K := K) c)}
        ≤ (ε : ℝ≥0∞)

/-- Slot-3 `PhaseConvergenceW` from the explicit confinement tail. -/
noncomputable def phase3ConfinementWork
    {n : ℕ} (A : Phase3ConfinementTail (L := L) (K := K) n) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel where
  Pre c := AdvanceEpidemics.allPhaseEq (L := L) (K := K) 3 n c
  Post c :=
    AdvanceEpidemics.allPhaseEq (L := L) (K := K) 3 n c ∧
      MainExponentConfinement.MainProfileConfinedToUseful
        (L := L) (K := K) c
  t := A.t
  ε := A.ε
  convergence := A.htail

/-- Package slot 3 as the legacy narrow `Phase3WorkData`. -/
noncomputable def phase3WorkData_of_tail
    {n : ℕ} (A : Phase3ConfinementTail (L := L) (K := K) n) :
    PhaseWorkFamily.Phase3WorkData (L := L) (K := K) n where
  work := phase3ConfinementWork (L := L) (K := K) A
  hPostEq := by
    intro c hc
    exact hc.1
  hPreEq := by
    intro c hc
    change AdvanceEpidemics.allPhaseEq (L := L) (K := K) 3 n c
    exact hc

/-! ## Slot 5 — corrected C5a-fed sampling work from a direct tail -/

/--
The corrected slot-5 tail.

This is the safe slot-5 surface for the faithful assembly.  It does not go through
the old `DrainEngine.phase5LevelsWork` / `SurvivalWorkHypotheses` route, because that route
still asks for `InvClosed Phase5AllWin`.  The intended instantiation is from the
corrected slot-5 drain plus the C5a `clockSeparationEscape` / concentration package.
-/
structure Phase5C5aTail (n : ℕ) where
  /-- Sampled hour/class. -/
  i5 : Fin (L + 1)
  /-- Sample floor parameter. -/
  K₀ : ℕ
  /-- The sampled floor cannot exceed the population. -/
  hK₀n : K₀ ≤ n
  /-- Honest C5a residual: slot 5 produces a paper-scale `0.04 n` floor. -/
  hK₀linear : n ≤ 25 * K₀
  /-- Slot-5 horizon. -/
  t : ℕ
  /-- Slot-5 failure budget. -/
  ε : ℝ≥0
  /-- Tail to exact phase-5 plus reserve-sample-good. -/
  htail :
    ∀ c₀,
      AdvanceEpidemics.allPhaseEq (L := L) (K := K) 5 n c₀ →
      ((NonuniformMajority L K).transitionKernel ^ t) c₀
        {c | ¬
          (AdvanceEpidemics.allPhaseEq (L := L) (K := K) 5 n c ∧
            Phase5Convergence.ReserveSampleGood
              (L := L) (K := K) i5 K₀ c)}
        ≤ (ε : ℝ≥0∞)

/-- Slot-5 `PhaseConvergenceW` from the corrected C5a-fed tail. -/
noncomputable def phase5C5aWork
    {n : ℕ} (A : Phase5C5aTail (L := L) (K := K) n) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel where
  Pre c := AdvanceEpidemics.allPhaseEq (L := L) (K := K) 5 n c
  Post c :=
    AdvanceEpidemics.allPhaseEq (L := L) (K := K) 5 n c ∧
      Phase5Convergence.ReserveSampleGood
        (L := L) (K := K) A.i5 A.K₀ c
  t := A.t
  ε := A.ε
  convergence := A.htail

/-- Package slot 5 as the legacy narrow `Phase5WorkData`. -/
noncomputable def phase5WorkData_of_tail
    {n : ℕ} (A : Phase5C5aTail (L := L) (K := K) n) :
    PhaseWorkFamily.Phase5WorkData (L := L) (K := K) n where
  i5 := A.i5
  K₀ := A.K₀
  hK₀n := A.hK₀n
  hK₀linear := A.hK₀linear
  work := phase5C5aWork (L := L) (K := K) A
  hPostEq := by
    intro c hc
    exact hc.1
  hPreEq := by
    intro c hc
    change AdvanceEpidemics.allPhaseEq (L := L) (K := K) 5 n c
    exact hc
  hPostSampled := by
    intro c hc
    exact hc.2

/-! ## Full concrete slot-input bundle -/

/--
Concrete slot inputs: the same public surface as `PhaseWorkFamily.WorkFamilyData`,
but slots 0/3/5 are specified by their actual tail atoms rather than carried work
objects.
-/
structure WorkFamilyTailData (n : ℕ) where
  /-- Common sign used by slots 6/7/8. -/
  σ : Sign
  hn : 2 ≤ n
  /-- Common allocated error cap for the survival slots. -/
  δ : ℝ≥0
  hδ : (δ : ℝ≥0∞) ≤ 1 / (n : ℝ≥0∞) ^ 2

  /-- Slot 0 C0 role-split tail. -/
  slot0 : Phase0RoleSplitTail (L := L) (K := K) n
  /-- Slot 3 confinement tail. -/
  slot3 : Phase3ConfinementTail (L := L) (K := K) n
  /-- Slot 5 corrected C5a tail. -/
  slot5 : Phase5C5aTail (L := L) (K := K) n

  /-- Slot 1 partner-pool floor. -/
  P1 : ℕ
  tWin1 : ℕ → ℕ
  η1 : ℝ≥0∞
  hesc1 : Phase1ReadySurvival.Phase1ReadyEscapeBound
    (L := L) (K := K) n P1 η1
  drainε1 : ℝ≥0
  hDrain1 :
    (∑ m ∈ Finset.Icc 1 n,
      (DrainEngine.qHat P1 n m) ^ (tWin1 m) : ℝ≥0∞)
        ≤ (drainε1 : ℝ≥0∞)
  escapeε1 : ℝ≥0
  hescε1 :
    (((∑ m ∈ Finset.Icc 1 n, tWin1 m) : ℕ) : ℝ≥0∞) * η1
      ≤ (escapeε1 : ℝ≥0∞)
  hTotal1 :
    (drainε1 : ℝ≥0∞) + (escapeε1 : ℝ≥0∞) ≤ (δ : ℝ≥0∞)

  /-- Slot 6 band level.  The sampled hour/floor are shared definitionally
  with the slot-5 tail above. -/
  l : ℕ
  hl1 : 1 ≤ l
  hlL : l ≤ L
  hhgt6 : l - 1 < slot5.i5.val
  hhne6 : slot5.i5.val ≠ L
  η6 : ℝ≥0∞
  hesc6 : Phase678ReadySurvival.Phase6ReadyEscapeBound
    (L := L) (K := K) n σ l hl1 hlL slot5.i5 slot5.K₀ η6
  escapeε6 : ℝ≥0
  hescε6 :
    ((DriftSurvival.driftHorizon (slot5.K₀ : ℝ) n
        (Phase6PhiPotential.phase6PhiMax n l) 2 : ℕ) : ℝ≥0∞) * η6
      ≤ (escapeε6 : ℝ≥0∞)
  hTotal6 :
    (DriftSurvival.driftBudgetNN 2 n : ℝ≥0∞) + (escapeε6 : ℝ≥0∞)
      ≤ (δ : ℝ≥0∞)

  /-- Slot 7 exact-band eliminator data. -/
  E7 : ℕ
  hE7pos : 1 ≤ E7
  hE7top : 2 * E7 ≤ n * (n - 1)
  hE7linear : n ≤ 4 * E7
  η7 : ℝ≥0∞
  hesc7 : Phase7BandSurvival.Phase7BandEscapeBound
    (L := L) (K := K) n σ l E7 η7
  escapeε7 : ℝ≥0
  hescε7 :
    ((DriftSurvival.driftHorizon ((2 * E7 : ℕ) : ℝ) n n 6 : ℕ) : ℝ≥0∞) * η7
      ≤ (escapeε7 : ℝ≥0∞)
  hescape7 : escapeε7 ≤ DriftSurvival.driftBudgetNN 6 n

  /-- Slot 8 eliminator margin data. -/
  E8 : ℕ
  tWin8 : ℕ → ℕ
  η8 : ℝ≥0∞
  hesc8 : Phase678ReadySurvival.Phase8ReadyEscapeBound
    (L := L) (K := K) n σ E8 η8
  drainε8 : ℝ≥0
  hDrain8 :
    (∑ m ∈ Finset.Icc 1 n,
      (DrainEngine.qHat E8 n m) ^ (tWin8 m) : ℝ≥0∞)
        ≤ (drainε8 : ℝ≥0∞)
  escapeε8 : ℝ≥0
  hescε8 :
    (((∑ m ∈ Finset.Icc 1 n, tWin8 m) : ℕ) : ℝ≥0∞) * η8
      ≤ (escapeε8 : ℝ≥0∞)
  hTotal8 :
    (drainε8 : ℝ≥0∞) + (escapeε8 : ℝ≥0∞) ≤ (δ : ℝ≥0∞)

  /-- Slot 10 block-geometric repetition count. -/
  k10 : ℕ

/-- Convert concrete slot inputs to the existing `WorkFromSlots` input record. -/
noncomputable def toWorkFamilyData
    {n : ℕ} (A : WorkFamilyTailData (L := L) (K := K) n) :
    PhaseWorkFamily.WorkFamilyData (L := L) (K := K) n where
  σ := A.σ
  hn := A.hn
  δ := A.δ
  hδ := A.hδ
  slot0 := phase0WorkData_of_tail (L := L) (K := K) A.slot0
  slot3 := phase3WorkData_of_tail (L := L) (K := K) A.slot3
  slot5 := phase5WorkData_of_tail (L := L) (K := K) A.slot5
  P1 := A.P1
  tWin1 := A.tWin1
  η1 := A.η1
  hesc1 := A.hesc1
  drainε1 := A.drainε1
  hDrain1 := A.hDrain1
  escapeε1 := A.escapeε1
  hescε1 := A.hescε1
  hTotal1 := A.hTotal1
  l := A.l
  hl1 := A.hl1
  hlL := A.hlL
  hhgt6 := A.hhgt6
  hhne6 := A.hhne6
  η6 := A.η6
  hesc6 := A.hesc6
  escapeε6 := A.escapeε6
  hescε6 := A.hescε6
  hTotal6 := A.hTotal6
  E7 := A.E7
  hE7pos := A.hE7pos
  hE7top := A.hE7top
  hE7linear := A.hE7linear
  η7 := A.η7
  hesc7 := A.hesc7
  escapeε7 := A.escapeε7
  hescε7 := A.hescε7
  hescape7 := A.hescape7
  E8 := A.E8
  tWin8 := A.tWin8
  η8 := A.η8
  hesc8 := A.hesc8
  drainε8 := A.drainε8
  hDrain8 := A.hDrain8
  escapeε8 := A.escapeε8
  hescε8 := A.hescε8
  hTotal8 := A.hTotal8
  k10 := A.k10

/-- The fully constructed work family from concrete slot inputs. -/
noncomputable def workFamily_of_tailData
    {n : ℕ} (A : WorkFamilyTailData (L := L) (K := K) n) :
    Fin 11 → PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  PhaseWorkFamily.workFamily
    (L := L) (K := K) (toWorkFamilyData (L := L) (K := K) A)

/-! ## Shape ties -/

/--
The remaining seam-shape residual for the constructed work family.

This is intentionally small: it no longer carries work slots.  It only carries the
truth that the constructed slot post/pre predicates match the seam exact windows.
Some of these are definitional projections; others are genuine cascade payloads.
In particular, slot 4 is not definitional because the landed `phase4Convergence`
post is `StableTie4 ∨ advFinished n`, not an exact `allPhaseEq` predicate.
-/
structure WorkWindowShape
    {n : ℕ} (A : WorkFamilyTailData (L := L) (K := K) n)
    (seamP : Fin 10 → ℕ) where
  /-- Work `Post` exposes the exact phase window for each seam. -/
  hPostEq :
    ∀ (k : Fin 10) (c : Config (AgentState L K)),
      ((workFamily_of_tailData (L := L) (K := K) A) ⟨k.val, by omega⟩).Post c →
      AdvanceEpidemics.allPhaseEq (L := L) (K := K) (seamP k) n c

  /-- Exact next-phase seam window supplies the next work `Pre`. -/
  hPreEq :
    ∀ (k : Fin 10) (c : Config (AgentState L K)),
      AdvanceEpidemics.allPhaseEq (L := L) (K := K) (seamP k + 1) n c →
      ((workFamily_of_tailData (L := L) (K := K) A) ⟨k.val + 1, by omega⟩).Pre c

/-- Slot-10 post bridge is deterministic for the constructed work family. -/
theorem workFamily_of_tailData_phase10_post
    {n : ℕ} (A : WorkFamilyTailData (L := L) (K := K) n) :
    ∀ c,
      ((workFamily_of_tailData (L := L) (K := K) A) ⟨10, by omega⟩).Post c →
      Phase10Drop.Phase10Post (L := L) (K := K) c := by
  intro c hc
  simpa [workFamily_of_tailData, toWorkFamilyData,
    PhaseWorkFamily.workFamily,
    WorkBuilder.work10_from_concrete] using hc

/--
Build the existing `PhaseWorkFamily.WorkShapeTies` from the constructed
work family plus the small residual post/pre seam-shape surface.
-/
noncomputable def workShapeTies_of_tailData
    {n : ℕ} (A : WorkFamilyTailData (L := L) (K := K) n)
    (seamP : Fin 10 → ℕ)
    (R : WorkWindowShape (L := L) (K := K) A seamP) :
    PhaseWorkFamily.WorkShapeTies
      (L := L) (K := K) (toWorkFamilyData (L := L) (K := K) A) seamP where
  hPostEq := by
    intro k c hc
    exact R.hPostEq k c hc
  hPreEq := by
    intro k c hc
    exact R.hPreEq k c hc
  hSlot10Post := workFamily_of_tailData_phase10_post (L := L) (K := K) A

#print axioms phase0RoleSplitWork
#print axioms phase0WorkData_of_tail
#print axioms phase3ConfinementWork
#print axioms phase3WorkData_of_tail
#print axioms phase5C5aWork
#print axioms phase5WorkData_of_tail
#print axioms toWorkFamilyData
#print axioms workFamily_of_tailData
#print axioms workFamily_of_tailData_phase10_post
#print axioms workShapeTies_of_tailData

end Phase035Work

end Ripple.PopulationProtocol.ExactMajority
