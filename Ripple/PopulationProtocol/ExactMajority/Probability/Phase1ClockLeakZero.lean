/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Phase-1 genuine-entry leak is zero while every clock is positive

The phase-1 far-mass argument is stopped at `Phase1GapFloorEntry`.  Its structural
fields are exactly conserved; the only possible one-step exit is a Clock at
counter zero advancing to Phase 2.  This file proves that such an exit has
zero mass on the separate `ClockPos` gate.  Clock depletion over a whole work
window remains a distinct prefix-tail obligation.
-/

import Ripple.PopulationProtocol.ExactMajority.Probability.Phase1GapFloorEntryClosure
import Ripple.PopulationProtocol.ExactMajority.Probability.CounterGuardedPhase
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase6LeakZero

namespace Ripple.PopulationProtocol.ExactMajority
namespace Phase1ClockLeakZero

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-- A Phase-1 pair stays in Phase 1 when both clock counters, if present, are
strictly positive. -/
theorem Phase1Transition_pair_phase_eq_of_counterPos
    (s t : AgentState L K)
    (hs : s.phase.val = 1) (ht : t.phase.val = 1)
    (hsPos : s.role = Role.clock → 0 < s.counter.val)
    (htPos : t.role = Role.clock → 0 < t.counter.val) :
    (Phase1Transition L K s t).1.phase.val = 1 ∧
      (Phase1Transition L K s t).2.phase.val = 1 := by
  unfold Phase1Transition
  dsimp only
  by_cases hmain : s.role = Role.main ∧ t.role = Role.main
  · rw [if_pos hmain]
    simp [clockCounterStep, hmain.1, hmain.2, hs, ht]
  · rw [if_neg hmain]
    exact ⟨CounterGuardedPhase.clockGuard_phase_eq 1 s hs hsPos,
      CounterGuardedPhase.clockGuard_phase_eq 1 t ht htPos⟩

/-- The full dispatcher has the same Phase-1 preservation property.  The
same-phase epidemic prefix is inert and `finishPhase10Entry` preserves phase. -/
theorem Transition_pair_phase1_eq_of_counterPos
    (s t : AgentState L K)
    (hs : s.phase.val = 1) (ht : t.phase.val = 1)
    (hsPos : s.role = Role.clock → 0 < s.counter.val)
    (htPos : t.role = Role.clock → 0 < t.counter.val) :
    (Transition L K s t).1.phase.val = 1 ∧
      (Transition L K s t).2.phase.val = 1 := by
  have hepi := Phase1Convergence.phaseEpidemicUpdate_eq_self_of_phase1
    (L := L) (K := K) s t hs ht
  have hphase : s.phase = ⟨1, by decide⟩ := Fin.ext hs
  have hpair := Phase1Transition_pair_phase_eq_of_counterPos
    (L := L) (K := K) s t hs ht hsPos htPos
  constructor
  · simp only [Transition, hepi, hphase]
    rw [finishPhase10Entry_phase_val]
    exact hpair.1
  · simp only [Transition, hepi, hphase]
    rw [finishPhase10Entry_phase_val]
    exact hpair.2

private theorem mem_of_app_left {c : Config (AgentState L K)}
    {r₁ r₂ : AgentState L K} (happ : Protocol.Applicable c r₁ r₂) : r₁ ∈ c :=
  Multiset.mem_of_le
    (show ({r₁, r₂} : Multiset (AgentState L K)) ≤ c from happ) (by simp)

private theorem mem_of_app_right {c : Config (AgentState L K)}
    {r₁ r₂ : AgentState L K} (happ : Protocol.Applicable c r₁ r₂) : r₂ ∈ c :=
  Multiset.mem_of_le
    (show ({r₁, r₂} : Multiset (AgentState L K)) ≤ c from happ) (by simp)

/-- Every support successor of a clock-positive genuine Phase-1 configuration
is again in the genuine Phase-1 window. -/
theorem phase1Win_on_support_of_clockPos
    (n : ℕ) (c c' : Config (AgentState L K))
    (hGenuine : PhaseOnlyWindows.Phase1Win (L := L) (K := K) n c)
    (hPos : Phase6LeakZero.ClockPos (L := L) (K := K) c)
    (hc' : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    PhaseOnlyWindows.Phase1Win (L := L) (K := K) n c' := by
  refine ⟨?_, ?_⟩
  · rw [Protocol.stepDistOrSelf_support_card_eq
      (NonuniformMajority L K) c c' hc']
    exact hGenuine.1
  · by_cases hc : 2 ≤ c.card
    · rw [show (NonuniformMajority L K).stepDistOrSelf c =
          (NonuniformMajority L K).stepDist c hc by
        unfold Protocol.stepDistOrSelf
        rw [dif_pos hc]] at hc'
      obtain ⟨⟨r₁, r₂⟩, hr⟩ :=
        Protocol.stepDist_support (NonuniformMajority L K) c hc c' hc'
      rw [← hr]
      simp only [Protocol.scheduledStep]
      by_cases happ : Protocol.Applicable c r₁ r₂
      · have hm1 := mem_of_app_left happ
        have hm2 := mem_of_app_right happ
        have hpair := Transition_pair_phase1_eq_of_counterPos
          (L := L) (K := K) r₁ r₂
          (hGenuine.2 r₁ hm1) (hGenuine.2 r₂ hm2)
          (hPos r₁ hm1) (hPos r₂ hm2)
        rw [show Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂ =
            c - {r₁, r₂} +
              {(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2} by
          unfold Protocol.stepOrSelf
          rw [if_pos happ]
          change c - {r₁, r₂} +
              {(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2} = _
          rfl]
        intro a ha
        rcases Multiset.mem_add.mp ha with hold | hnew
        · exact hGenuine.2 a
            (Multiset.mem_of_le (Multiset.sub_le_self _ _) hold)
        · rw [Multiset.insert_eq_cons, Multiset.mem_cons,
            Multiset.mem_singleton] at hnew
          rcases hnew with rfl | rfl
          · exact hpair.1
          · exact hpair.2
      · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]
        exact hGenuine.2
    · rw [show (NonuniformMajority L K).stepDistOrSelf c = PMF.pure c by
          unfold Protocol.stepDistOrSelf
          rw [dif_neg hc]] at hc'
      rw [PMF.mem_support_pure_iff] at hc'
      subst c'
      exact hGenuine.2

/-- Leaving the phase-only genuine window has one-step probability zero on the
clock-positive gate. -/
theorem phase1Win_leak_zero_on_clockPos
    (n : ℕ) (c : Config (AgentState L K))
    (hGenuine : PhaseOnlyWindows.Phase1Win (L := L) (K := K) n c)
    (hPos : Phase6LeakZero.ClockPos (L := L) (K := K) c) :
    (NonuniformMajority L K).transitionKernel c
        {c' | ¬ PhaseOnlyWindows.Phase1Win (L := L) (K := K) n c'} = 0 := by
  change ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
      {c' | ¬ PhaseOnlyWindows.Phase1Win (L := L) (K := K) n c'} = 0
  rw [PMF.toMeasure_apply_eq_zero_iff _
    (DiscreteMeasurableSpace.forall_measurableSet _)]
  rw [Set.disjoint_left]
  intro c' hsupp hbad
  exact hbad (phase1Win_on_support_of_clockPos n c c' hGenuine hPos hsupp)

/-- The full genuine-entry gate has no one-step leak while every clock remains
positive.  The gap and Main-count fields are preserved exactly by
`Phase1GenuineEntryClosure`; only clock depletion needs a cumulative tail. -/
theorem phase1GapFloorEntry_leak_zero_on_clockPos
    (n g mc : ℕ) (c : Config (AgentState L K))
    (hEntry : Phase1PartnerFloor.Phase1GapFloorEntry (L := L) (K := K) n g mc c)
    (hPos : Phase6LeakZero.ClockPos (L := L) (K := K) c) :
    (NonuniformMajority L K).transitionKernel c
        (Phase1FarPhiSurvival.phase1GapFloorEntryGate
          (L := L) (K := K) n g mc)ᶜ = 0 := by
  apply le_antisymm
  · exact (Phase1GapFloorEntryClosure.phase1GapFloorEntry_escape_le_phase1_escape
      n g mc c hEntry).trans_eq
        (phase1Win_leak_zero_on_clockPos n c hEntry.1 hPos)
  · exact bot_le

#print axioms Phase1Transition_pair_phase_eq_of_counterPos
#print axioms Transition_pair_phase1_eq_of_counterPos
#print axioms phase1Win_on_support_of_clockPos
#print axioms phase1Win_leak_zero_on_clockPos
#print axioms phase1GapFloorEntry_leak_zero_on_clockPos

end Phase1ClockLeakZero
end Ripple.PopulationProtocol.ExactMajority
