
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# WorkConcreteSlots

Expose concrete public constructors for the remaining slot-0 / slot-3 / slot-5
work positions used by `WorkFromSlots`.

The previous `WorkFromSlots.SlotInputs` still carried three narrow work
atoms:

* slot 0: C0 role-split work;
* slot 3: Main exponent confinement work;
* slot 5: corrected slot-5 sampling / C5a work.

This file replaces those three carried work atoms by explicit `PhaseConvergenceW`
constructors.  Each constructor is parameterized by exactly the genuine tail bound
that its proof surface needs:

* `Slot0RoleSplitTail`: C0 role-split / floor tail;
* `Slot3ConfinementTail`: Theorem-6.2 main-confinement tail;
* `Slot5C5aTail`: corrected slot-5 tail, to be instantiated from the C5a package.

It also gives a `SlotInputsConcrete → WorkFromSlots.SlotInputs`
adapter, so all downstream `WorkFromSlots` machinery keeps working.

Important boundary:

`WorkShapeTies` is not fully definitional for the current committed work
family.  Slot 4’s landed `phase4Convergence` has
`Post = StableTie4 ∨ advFinished n`, not an exact `allPhaseEq` window, so a
same-shape exact-window tie is a real wiring obligation.  We therefore keep the
remaining post/pre seam-shape surface as one explicit `WorkShapeResidual`,
while proving the deterministic slot-10 post bridge.

Uses only proved Lean terms and ordinary classical infrastructure.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.WorkFromSlots
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.MainExponentConfinement

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal Real

namespace WorkConcreteSlots

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
structure Slot0RoleSplitTail (n : ℕ) where
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
          (SeamEpidemics.allPhaseEq (L := L) (K := K) 0 n c ∧
            RoleSplitConcentration.RoleSplitGood (L := L) (K := K) η n c)}
        ≤ (ε : ℝ≥0∞)

/-- Slot-0 `PhaseConvergenceW` from the explicit C0 tail. -/
noncomputable def slot0RoleSplitWork
    {n : ℕ} (A : Slot0RoleSplitTail (L := L) (K := K) n) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel where
  Pre c := RoleSplitConcentration.Phase0Initial (L := L) (K := K) n c
  Post c :=
    SeamEpidemics.allPhaseEq (L := L) (K := K) 0 n c ∧
      RoleSplitConcentration.RoleSplitGood (L := L) (K := K) A.η n c
  t := A.t
  ε := A.ε
  convergence := A.htail

/-- Package slot 0 as the legacy narrow `Slot0WorkAtom`. -/
noncomputable def slot0WorkAtom_of_tail
    {n : ℕ} (A : Slot0RoleSplitTail (L := L) (K := K) n) :
    WorkFromSlots.Slot0WorkAtom (L := L) (K := K) n where
  work := slot0RoleSplitWork (L := L) (K := K) A
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
structure Slot3ConfinementTail (n : ℕ) where
  /-- Slot-3 confinement horizon. -/
  t : ℕ
  /-- Slot-3 horizon fits the locked aggregate `O(n log n)` phase budget. -/
  ht_le : t ≤ 17 * n * (L + 1)
  /-- Slot-3 confinement failure budget. -/
  ε : ℝ≥0
  /-- Tail to exact phase-3 plus main-profile confinement. -/
  htail :
    ∀ c₀,
      SeamEpidemics.allPhaseEq (L := L) (K := K) 3 n c₀ →
      ((NonuniformMajority L K).transitionKernel ^ t) c₀
        {c | ¬
          (SeamEpidemics.allPhaseEq (L := L) (K := K) 3 n c ∧
            MainExponentConfinement.MainProfileConfinedToUseful
              (L := L) (K := K) c)}
        ≤ (ε : ℝ≥0∞)

/-- Slot-3 `PhaseConvergenceW` from the explicit confinement tail. -/
noncomputable def slot3ConfinementWork
    {n : ℕ} (A : Slot3ConfinementTail (L := L) (K := K) n) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel where
  Pre c := SeamEpidemics.allPhaseEq (L := L) (K := K) 3 n c
  Post c :=
    SeamEpidemics.allPhaseEq (L := L) (K := K) 3 n c ∧
      MainExponentConfinement.MainProfileConfinedToUseful
        (L := L) (K := K) c
  t := A.t
  ε := A.ε
  convergence := A.htail

/-- Package slot 3 as the legacy narrow `Slot3WorkAtom`. -/
noncomputable def slot3WorkAtom_of_tail
    {n : ℕ} (A : Slot3ConfinementTail (L := L) (K := K) n) :
    WorkFromSlots.Slot3WorkAtom (L := L) (K := K) n where
  work := slot3ConfinementWork (L := L) (K := K) A
  hPostEq := by
    intro c hc
    exact hc.1
  hPreEq := by
    intro c hc
    change SeamEpidemics.allPhaseEq (L := L) (K := K) 3 n c
    exact hc

/-! ## Slot 5 — corrected C5a-fed sampling work from a direct tail -/

/--
The corrected slot-5 tail.

This is the safe slot-5 surface for the faithful assembly.  It does not go through
the old `SlotEngine.slot5Honest` / `WorkInputsFull` route, because that route
still asks for `InvClosed Phase5AllWin`.  The intended instantiation is from the
corrected slot-5 drain plus the C5a `clockSeparationEscape` / concentration package.
-/
structure Slot5C5aTail (n : ℕ) where
  /-- Sampled hour/class. -/
  i5 : Fin (L + 1)
  /-- Sample floor parameter. -/
  K₀ : ℕ
  /-- Slot-5 horizon. -/
  t : ℕ
  /-- Slot-5 failure budget. -/
  ε : ℝ≥0
  /-- Tail to exact phase-5 plus reserve-sample-good. -/
  htail :
    ∀ c₀,
      SeamEpidemics.allPhaseEq (L := L) (K := K) 5 n c₀ →
      ((NonuniformMajority L K).transitionKernel ^ t) c₀
        {c | ¬
          (SeamEpidemics.allPhaseEq (L := L) (K := K) 5 n c ∧
            Phase5Convergence.ReserveSampleGood
              (L := L) (K := K) i5 K₀ c)}
        ≤ (ε : ℝ≥0∞)

/-- Slot-5 `PhaseConvergenceW` from the corrected C5a-fed tail. -/
noncomputable def slot5C5aWork
    {n : ℕ} (A : Slot5C5aTail (L := L) (K := K) n) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel where
  Pre c := SeamEpidemics.allPhaseEq (L := L) (K := K) 5 n c
  Post c :=
    SeamEpidemics.allPhaseEq (L := L) (K := K) 5 n c ∧
      Phase5Convergence.ReserveSampleGood
        (L := L) (K := K) A.i5 A.K₀ c
  t := A.t
  ε := A.ε
  convergence := A.htail

/-- Package slot 5 as the legacy narrow `Slot5WorkAtom`. -/
noncomputable def slot5WorkAtom_of_tail
    {n : ℕ} (A : Slot5C5aTail (L := L) (K := K) n) :
    WorkFromSlots.Slot5WorkAtom (L := L) (K := K) n where
  work := slot5C5aWork (L := L) (K := K) A
  hPostEq := by
    intro c hc
    exact hc.1
  hPreEq := by
    intro c hc
    change SeamEpidemics.allPhaseEq (L := L) (K := K) 5 n c
    exact hc

/-! ## Full concrete slot-input bundle -/

/--
Concrete slot inputs: the same public surface as `WorkFromSlots.SlotInputs`,
but slots 0/3/5 are specified by their actual tail atoms rather than carried work
objects.
-/
structure SlotInputsConcrete (n : ℕ) where
  /-- Common sign used by slots 6/7/8. -/
  σ : Sign
  /-- Common drain budget cap. -/
  M₀ : ℕ
  hn : 2 ≤ n
  hM1 : 1 ≤ M₀

  /-- Slot 0 C0 role-split tail. -/
  slot0 : Slot0RoleSplitTail (L := L) (K := K) n
  /-- Slot 2 opinion epidemic inputs. -/
  slot2 : WorkBuilder.Slot2OpinionInputs n
  /-- Slot 3 confinement tail. -/
  slot3 : Slot3ConfinementTail (L := L) (K := K) n
  /-- Slot 4 scalar fit. -/
  slot4 : WorkBuilder.Slot4ScalarFit n
  /-- Slot 5 corrected C5a tail. -/
  slot5 : Slot5C5aTail (L := L) (K := K) n

  /-- Slot 1 partner-pool floor. -/
  P1 : ℕ
  tWin1 : ℕ → ℕ
  η1 : ℝ≥0∞
  hesc1 : Slot1SurvivalInputs.Slot1ReadyEscapeAtom
    (L := L) (K := K) n P1 η1
  hpt1 :
    ∀ m ∈ Finset.Icc 1 M₀,
      (SlotEngine.qHat P1 n m) ^ (tWin1 m)
        ≤ (DrainCalibration.budgetNN M₀ n : ℝ≥0∞)
  escapeε1 : ℝ≥0
  hescε1 :
    (((∑ m ∈ Finset.Icc 1 M₀, tWin1 m) : ℕ) : ℝ≥0∞) * η1
      ≤ (escapeε1 : ℝ≥0∞)

  /-- Slot 6 band level and sampled-class data. -/
  l : ℕ
  hl1 : 1 ≤ l
  hlL : l ≤ L
  i6 : Fin (L + 1)
  K₀6 : ℕ
  hhgt6 : l - 1 < i6.val
  hhne6 : i6.val ≠ L
  tWin6 : ℕ → ℕ
  η6 : ℝ≥0∞
  hesc6 : Slot678SurvivalInputs.Slot6ReadyEscapeAtom
    (L := L) (K := K) n σ l hl1 hlL i6 K₀6 η6
  hpt6 :
    ∀ m ∈ Finset.Icc 1 M₀,
      (SlotEngine.qHat K₀6 n m) ^ (tWin6 m)
        ≤ (DrainCalibration.budgetNN M₀ n : ℝ≥0∞)
  escapeε6 : ℝ≥0
  hescε6 :
    (((∑ m ∈ Finset.Icc 1 M₀, tWin6 m) : ℕ) : ℝ≥0∞) * η6
      ≤ (escapeε6 : ℝ≥0∞)

  /-- Slot 7 eliminator margin data. -/
  E7 : ℕ
  tWin7 : ℕ → ℕ
  η7 : ℝ≥0∞
  hesc7 : Slot678SurvivalInputs.Slot7ReadyEscapeAtom
    (L := L) (K := K) n σ E7 η7
  hpt7 :
    ∀ m ∈ Finset.Icc 1 M₀,
      (SlotEngine.qHat E7 n m) ^ (tWin7 m)
        ≤ (DrainCalibration.budgetNN M₀ n : ℝ≥0∞)
  escapeε7 : ℝ≥0
  hescε7 :
    (((∑ m ∈ Finset.Icc 1 M₀, tWin7 m) : ℕ) : ℝ≥0∞) * η7
      ≤ (escapeε7 : ℝ≥0∞)

  /-- Slot 8 eliminator margin data. -/
  E8 : ℕ
  tWin8 : ℕ → ℕ
  η8 : ℝ≥0∞
  hesc8 : Slot678SurvivalInputs.Slot8ReadyEscapeAtom
    (L := L) (K := K) n σ E8 η8
  hpt8 :
    ∀ m ∈ Finset.Icc 1 M₀,
      (SlotEngine.qHat E8 n m) ^ (tWin8 m)
        ≤ (DrainCalibration.budgetNN M₀ n : ℝ≥0∞)
  escapeε8 : ℝ≥0
  hescε8 :
    (((∑ m ∈ Finset.Icc 1 M₀, tWin8 m) : ℕ) : ℝ≥0∞) * η8
      ≤ (escapeε8 : ℝ≥0∞)

  /-- Slot 9 opinion epidemic inputs. -/
  slot9 : WorkFromSlots.Slot9OpinionInputs n
  /-- Slot 10 block-geometric repetition count. -/
  k10 : ℕ

/-- Convert concrete slot inputs to the existing `WorkFromSlots` input record. -/
noncomputable def toSlotInputs
    {n : ℕ} (A : SlotInputsConcrete (L := L) (K := K) n) :
    WorkFromSlots.SlotInputs (L := L) (K := K) n where
  σ := A.σ
  M₀ := A.M₀
  hn := A.hn
  hM1 := A.hM1
  slot0 := slot0WorkAtom_of_tail (L := L) (K := K) A.slot0
  slot2 := A.slot2
  slot3 := slot3WorkAtom_of_tail (L := L) (K := K) A.slot3
  slot4 := A.slot4
  slot5 := slot5WorkAtom_of_tail (L := L) (K := K) A.slot5
  P1 := A.P1
  tWin1 := A.tWin1
  η1 := A.η1
  hesc1 := A.hesc1
  hpt1 := A.hpt1
  escapeε1 := A.escapeε1
  hescε1 := A.hescε1
  l := A.l
  hl1 := A.hl1
  hlL := A.hlL
  i6 := A.i6
  K₀6 := A.K₀6
  hhgt6 := A.hhgt6
  hhne6 := A.hhne6
  tWin6 := A.tWin6
  η6 := A.η6
  hesc6 := A.hesc6
  hpt6 := A.hpt6
  escapeε6 := A.escapeε6
  hescε6 := A.hescε6
  E7 := A.E7
  tWin7 := A.tWin7
  η7 := A.η7
  hesc7 := A.hesc7
  hpt7 := A.hpt7
  escapeε7 := A.escapeε7
  hescε7 := A.hescε7
  E8 := A.E8
  tWin8 := A.tWin8
  η8 := A.η8
  hesc8 := A.hesc8
  hpt8 := A.hpt8
  escapeε8 := A.escapeε8
  hescε8 := A.hescε8
  slot9 := A.slot9
  k10 := A.k10

/-- The fully constructed work family from concrete slot inputs. -/
noncomputable def work_of_concreteSlots
    {n : ℕ} (A : SlotInputsConcrete (L := L) (K := K) n) :
    Fin 11 → PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  WorkFromSlots.work_of_slots
    (L := L) (K := K) (toSlotInputs (L := L) (K := K) A)

/-! ## Shape ties -/

/--
The remaining seam-shape residual for the constructed work family.

This is intentionally small: it no longer carries work slots.  It only carries the
truth that the constructed slot post/pre predicates match the seam exact windows.
Some of these are definitional projections; others are genuine cascade payloads.
In particular, slot 4 is not definitional because the landed `phase4Convergence`
post is `StableTie4 ∨ advFinished n`, not an exact `allPhaseEq` predicate.
-/
structure WorkShapeResidual
    {n : ℕ} (A : SlotInputsConcrete (L := L) (K := K) n)
    (seamP : Fin 10 → ℕ) where
  /-- Work `Post` exposes the exact phase window for each seam. -/
  hPostEq :
    ∀ (k : Fin 10) (c : Config (AgentState L K)),
      ((work_of_concreteSlots (L := L) (K := K) A) ⟨k.val, by omega⟩).Post c →
      SeamEpidemics.allPhaseEq (L := L) (K := K) (seamP k) n c

  /-- Exact next-phase seam window supplies the next work `Pre`. -/
  hPreEq :
    ∀ (k : Fin 10) (c : Config (AgentState L K)),
      SeamEpidemics.allPhaseEq (L := L) (K := K) (seamP k + 1) n c →
      ((work_of_concreteSlots (L := L) (K := K) A) ⟨k.val + 1, by omega⟩).Pre c

/-- Slot-10 post bridge is deterministic for the constructed work family. -/
theorem hSlot10Post_concrete
    {n : ℕ} (A : SlotInputsConcrete (L := L) (K := K) n) :
    ∀ c,
      ((work_of_concreteSlots (L := L) (K := K) A) ⟨10, by omega⟩).Post c →
      Phase10Drop.Phase10Post (L := L) (K := K) c := by
  intro c hc
  simpa [work_of_concreteSlots, toSlotInputs,
    WorkFromSlots.work_of_slots,
    WorkBuilder.work10_from_concrete] using hc

/--
Build the existing `WorkFromSlots.WorkShapeTies` from the constructed
work family plus the small residual post/pre seam-shape surface.
-/
noncomputable def workShapeTies_concrete
    {n : ℕ} (A : SlotInputsConcrete (L := L) (K := K) n)
    (seamP : Fin 10 → ℕ)
    (R : WorkShapeResidual (L := L) (K := K) A seamP) :
    WorkFromSlots.WorkShapeTies
      (L := L) (K := K) (toSlotInputs (L := L) (K := K) A) seamP where
  hPostEq := by
    intro k c hc
    exact R.hPostEq k c hc
  hPreEq := by
    intro k c hc
    exact R.hPreEq k c hc
  hSlot10Post := hSlot10Post_concrete (L := L) (K := K) A

/-! ## Convenience faithful-core wrapper -/

/-- Build `FaithfulCore` from concrete slot inputs, seam atoms, and shape residual. -/
noncomputable def faithfulCore_of_concreteSlotAtoms
    {n : ℕ} {c₀ : Config (AgentState L K)}
    (A : SlotInputsConcrete (L := L) (K := K) n)
    (S : WorkFromSlots.SeamAtoms
      (L := L) (K := K)
      (n := n)
      (work_of_concreteSlots (L := L) (K := K) A) c₀)
    (R : WorkShapeResidual (L := L) (K := K) A S.seamP) :
    FaithfulWitness.FaithfulCore (L := L) (K := K) n c₀ :=
  WorkFromSlots.faithfulCore_of_slotAtoms
    (L := L) (K := K)
    (toSlotInputs (L := L) (K := K) A)
    S
    (workShapeTies_concrete (L := L) (K := K) A S.seamP R)

#print axioms slot0RoleSplitWork
#print axioms slot0WorkAtom_of_tail
#print axioms slot3ConfinementWork
#print axioms slot3WorkAtom_of_tail
#print axioms slot5C5aWork
#print axioms slot5WorkAtom_of_tail
#print axioms toSlotInputs
#print axioms work_of_concreteSlots
#print axioms hSlot10Post_concrete
#print axioms workShapeTies_concrete
#print axioms faithfulCore_of_concreteSlotAtoms

end WorkConcreteSlots

end ExactMajority
