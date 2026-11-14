/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Structural closure of the genuine Phase-1 drift gate

`Phase1PartnerFloor.Phase1GapFloorEntry` consists of three facts: the phase-only Phase-1
window, a bound on the centred Main bias sum, and a Main-count floor.  Only the
first fact can fail during the Phase-1 work window.  This file proves that the
other two are exactly preserved on one-step support, including mixed-role
interactions.  Consequently, escape from `Phase1GapFloorEntry` is bounded by escape
from `PhaseOnlyWindows.Phase1Win`; no additional structural leak atom is needed.
-/

import Ripple.PopulationProtocol.ExactMajority.Probability.Phase1FarPhiSurvival
import Ripple.PopulationProtocol.ExactMajority.Analysis.Invariants

namespace Ripple.PopulationProtocol.ExactMajority
namespace Phase1GapFloorEntryClosure

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Classical

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-! ## Pairwise structural conservation -/

/-- In a mixed-role Phase-1 pair, each Main endpoint is fixed by the full
transition.  Non-Mains may run the clock subroutine, but never enter the Main
sub-population. -/
theorem main_endpoints_fixed_of_not_both_main (s t : AgentState L K)
    (hs1 : s.phase.val = 1) (ht1 : t.phase.val = 1)
    (hnb : ¬ (s.role = Role.main ∧ t.role = Role.main)) :
    (s.role = Role.main → (Transition L K s t).1 = s) ∧
      (t.role = Role.main → (Transition L K s t).2 = t) := by
  constructor
  · intro hsM
    have hepi := Phase1Convergence.phaseEpidemicUpdate_eq_self_of_phase1
      (L := L) (K := K) s t hs1 ht1
    have hsp : s.phase = ⟨1, by decide⟩ := Fin.ext hs1
    have hp1 : (Phase1Transition L K s t).1 = s := by
      unfold Phase1Transition
      rw [if_neg hnb]
      simp only []
      exact Phase1Convergence.clockCounterStep_eq_self_of_main s hsM
    unfold Transition
    rw [hepi]
    simp only [hsp]
    rw [finishPhase10Entry_eq_self_of_after_ne_10 (L := L) (K := K) s _
      (by rw [hp1, hs1]; decide)]
    exact hp1
  · intro htM
    have hepi := Phase1Convergence.phaseEpidemicUpdate_eq_self_of_phase1
      (L := L) (K := K) s t hs1 ht1
    have hsp : s.phase = ⟨1, by decide⟩ := Fin.ext hs1
    have hp1 : (Phase1Transition L K s t).2 = t := by
      unfold Phase1Transition
      rw [if_neg hnb]
      simp only []
      exact Phase1Convergence.clockCounterStep_eq_self_of_main t htM
    unfold Transition
    rw [hepi]
    simp only [hsp]
    rw [finishPhase10Entry_eq_self_of_after_ne_10 (L := L) (K := K) t _
      (by rw [hp1, ht1]; decide)]
    exact hp1

/-- The centred Main bias contribution is conserved by every Phase-1 pair,
with arbitrary roles. -/
theorem Transition_biasZ_pair_eq_of_phase1 (s t : AgentState L K)
    (hs1 : s.phase.val = 1) (ht1 : t.phase.val = 1) :
    AveragingRate.biasZ (Transition L K s t).1 +
        AveragingRate.biasZ (Transition L K s t).2 =
      AveragingRate.biasZ s + AveragingRate.biasZ t := by
  by_cases hboth : s.role = Role.main ∧ t.role = Role.main
  · have hpair := AveragingRate.Transition_centredBiasSum_pair_eq_of_both_main
      (L := L) (K := K) s t hs1 ht1 hboth.1 hboth.2
    simpa only [AveragingRate.biasZ_pair] using hpair
  · obtain ⟨hr1, hr2⟩ := PhaseOnlyWindows.Transition_role_phase1
      (L := L) (K := K) s t hs1 ht1
    obtain ⟨hfix1, hfix2⟩ :=
      main_endpoints_fixed_of_not_both_main s t hs1 ht1 hboth
    have hside1 : AveragingRate.biasZ (Transition L K s t).1 =
        AveragingRate.biasZ s := by
      by_cases hsM : s.role = Role.main
      · rw [hfix1 hsM]
      · unfold AveragingRate.biasZ
        rw [if_neg hsM, if_neg]
        intro hout
        rw [hr1] at hout
        exact hsM hout
    have hside2 : AveragingRate.biasZ (Transition L K s t).2 =
        AveragingRate.biasZ t := by
      by_cases htM : t.role = Role.main
      · rw [hfix2 htM]
      · unfold AveragingRate.biasZ
        rw [if_neg htM, if_neg]
        intro hout
        rw [hr2] at hout
        exact htM hout
    rw [hside1, hside2]

/-- Main-role count is conserved by every Phase-1 pair. -/
theorem Transition_mainCount_pair_eq_of_phase1 (s t : AgentState L K)
    (hs1 : s.phase.val = 1) (ht1 : t.phase.val = 1) :
    Multiset.countP (fun a : AgentState L K => a.role = Role.main)
        ({(Transition L K s t).1, (Transition L K s t).2} :
          Multiset (AgentState L K)) =
      Multiset.countP (fun a : AgentState L K => a.role = Role.main)
        ({s, t} : Multiset (AgentState L K)) := by
  obtain ⟨hr1, hr2⟩ := PhaseOnlyWindows.Transition_role_phase1
    (L := L) (K := K) s t hs1 ht1
  rw [Phase6Convergence.countP_main_pair, Phase6Convergence.countP_main_pair]
  simp only [hr1, hr2]

private theorem mem_of_app_left {c : Config (AgentState L K)}
    {r₁ r₂ : AgentState L K} (happ : Protocol.Applicable c r₁ r₂) : r₁ ∈ c :=
  Multiset.mem_of_le
    (show ({r₁, r₂} : Multiset (AgentState L K)) ≤ c from happ) (by simp)

private theorem mem_of_app_right {c : Config (AgentState L K)}
    {r₁ r₂ : AgentState L K} (happ : Protocol.Applicable c r₁ r₂) : r₂ ∈ c :=
  Multiset.mem_of_le
    (show ({r₁, r₂} : Multiset (AgentState L K)) ≤ c from happ) (by simp)

/-! ## Configuration and support conservation -/

/-- The centred Main bias sum is conserved by every chosen-pair update from the
phase-only genuine window. -/
theorem centredBiasSum_stepOrSelf_eq_of_phase1Win (n : ℕ)
    (c : Config (AgentState L K))
    (hInv : PhaseOnlyWindows.Phase1Win (L := L) (K := K) n c)
    (r₁ r₂ : AgentState L K) :
    AveragingRate.centredBiasSum
        (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂) =
      AveragingRate.centredBiasSum c := by
  obtain ⟨_, hphase⟩ := hInv
  by_cases happ : Protocol.Applicable c r₁ r₂
  · have hm1 := mem_of_app_left happ
    have hm2 := mem_of_app_right happ
    have hsub : ({r₁, r₂} : Multiset (AgentState L K)) ≤ c := happ
    have hc' : Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂ =
        c - {r₁, r₂} + {(Transition L K r₁ r₂).1,
          (Transition L K r₁ r₂).2} := by
      unfold Protocol.stepOrSelf
      rw [if_pos happ]
      rfl
    have hsplit : c = (c - {r₁, r₂}) +
        ({r₁, r₂} : Multiset (AgentState L K)) := by
      rw [Multiset.sub_add_cancel hsub]
    have hpair := Transition_biasZ_pair_eq_of_phase1 r₁ r₂
      (hphase r₁ hm1) (hphase r₂ hm2)
    have hpair' :
        ((({(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2}
            : Multiset (AgentState L K)).map AveragingRate.biasZ).sum) =
          ((({r₁, r₂} : Multiset (AgentState L K)).map
            AveragingRate.biasZ).sum) := by
      rw [AveragingRate.biasZ_pair, AveragingRate.biasZ_pair]
      exact hpair
    unfold AveragingRate.centredBiasSum
    rw [hc', Multiset.map_add, Multiset.sum_add]
    conv_rhs => rw [hsplit]
    rw [Multiset.map_add, Multiset.sum_add, hpair']
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]

/-- Main-role count is conserved by every chosen-pair update from the genuine
Phase-1 window. -/
theorem mainCount_stepOrSelf_eq_of_phase1Win (n : ℕ)
    (c : Config (AgentState L K))
    (hInv : PhaseOnlyWindows.Phase1Win (L := L) (K := K) n c)
    (r₁ r₂ : AgentState L K) :
    RoleSplitConcentration.mainCount (L := L) (K := K)
        (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂) =
      RoleSplitConcentration.mainCount (L := L) (K := K) c := by
  obtain ⟨_, hphase⟩ := hInv
  by_cases happ : Protocol.Applicable c r₁ r₂
  · have hm1 := mem_of_app_left happ
    have hm2 := mem_of_app_right happ
    have hsub : ({r₁, r₂} : Multiset (AgentState L K)) ≤ c := happ
    have hc' : Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂ =
        c - {r₁, r₂} + {(Transition L K r₁ r₂).1,
          (Transition L K r₁ r₂).2} := by
      unfold Protocol.stepOrSelf
      rw [if_pos happ]
      rfl
    have hsplit : c = (c - {r₁, r₂}) +
        ({r₁, r₂} : Multiset (AgentState L K)) := by
      rw [Multiset.sub_add_cancel hsub]
    have hpair := Transition_mainCount_pair_eq_of_phase1 r₁ r₂
      (hphase r₁ hm1) (hphase r₂ hm2)
    unfold RoleSplitConcentration.mainCount
    rw [hc', Multiset.countP_add]
    conv_rhs => rw [hsplit]
    rw [Multiset.countP_add, hpair]
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]

/-- Genuine structural facts are preserved on one-step PMF support.  This theorem
does not assert phase-window closure. -/
theorem structural_facts_on_support (n g mc : ℕ)
    (c c' : Config (AgentState L K))
    (hEntry : Phase1PartnerFloor.Phase1GapFloorEntry (L := L) (K := K) n g mc c)
    (hc' : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    |AveragingRate.centredBiasSum c'| ≤ (g : ℤ) ∧
      mc ≤ RoleSplitConcentration.mainCount (L := L) (K := K) c' := by
  by_cases hc : 2 ≤ c.card
  · rw [show (NonuniformMajority L K).stepDistOrSelf c =
        (NonuniformMajority L K).stepDist c hc by
      unfold Protocol.stepDistOrSelf
      rw [dif_pos hc]] at hc'
    obtain ⟨⟨r₁, r₂⟩, hr⟩ :=
      Protocol.stepDist_support (NonuniformMajority L K) c hc c' hc'
    rw [← hr]
    constructor
    · rw [Protocol.scheduledStep,
        centredBiasSum_stepOrSelf_eq_of_phase1Win n c hEntry.1 r₁ r₂]
      exact hEntry.2.1
    · rw [Protocol.scheduledStep,
        mainCount_stepOrSelf_eq_of_phase1Win n c hEntry.1 r₁ r₂]
      exact hEntry.2.2
  · rw [show (NonuniformMajority L K).stepDistOrSelf c = PMF.pure c by
      unfold Protocol.stepDistOrSelf
      rw [dif_neg hc]] at hc'
    rw [PMF.mem_support_pure_iff] at hc'
    subst c'
    exact hEntry.2

/-- If a support successor remains in the phase-only window, it remains in the
full genuine drift gate. -/
theorem phase1GapFloorEntry_of_phase1Win_on_support (n g mc : ℕ)
    (c c' : Config (AgentState L K))
    (hEntry : Phase1PartnerFloor.Phase1GapFloorEntry (L := L) (K := K) n g mc c)
    (hc' : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support)
    (hPhase : PhaseOnlyWindows.Phase1Win (L := L) (K := K) n c') :
    Phase1PartnerFloor.Phase1GapFloorEntry (L := L) (K := K) n g mc c' := by
  exact ⟨hPhase, structural_facts_on_support n g mc c c' hEntry hc'⟩

/-! ## Escape comparison -/

/-- One-step escape from `Phase1GapFloorEntry` is no larger than escape from its
phase-only component.  The gap and Main-count fields create no extra leak. -/
theorem phase1GapFloorEntry_escape_le_phase1_escape (n g mc : ℕ)
    (c : Config (AgentState L K))
    (hEntry : Phase1PartnerFloor.Phase1GapFloorEntry (L := L) (K := K) n g mc c) :
    (NonuniformMajority L K).transitionKernel c
        (Phase1FarPhiSurvival.phase1GapFloorEntryGate
          (L := L) (K := K) n g mc)ᶜ ≤
      (NonuniformMajority L K).transitionKernel c
        {c' | ¬ PhaseOnlyWindows.Phase1Win (L := L) (K := K) n c'} := by
  change ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
      {c' | ¬ Phase1PartnerFloor.Phase1GapFloorEntry (L := L) (K := K) n g mc c'} ≤
    ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
      {c' | ¬ PhaseOnlyWindows.Phase1Win (L := L) (K := K) n c'}
  apply ((NonuniformMajority L K).stepDistOrSelf c).toMeasure_mono
    (DiscreteMeasurableSpace.forall_measurableSet _)
  intro c' hc'
  rcases hc' with ⟨hbad, hsupp⟩
  simp only [Set.mem_setOf_eq] at hbad ⊢
  intro hPhase
  exact hbad (phase1GapFloorEntry_of_phase1Win_on_support
    n g mc c c' hEntry hsupp hPhase)

/-- Adapter from a phase-window escape bound to the gate-leak input expected by
`Phase1FarPhiSurvival.mainBiasSafe_tail`. -/
theorem phase1GapFloorEntry_leak_of_phase1_escape (n g mc : ℕ)
    (S : Set (Config (AgentState L K))) (q : ℝ≥0∞)
    (hPhase : ∀ c ∈ Phase1FarPhiSurvival.phase1GapFloorEntryGate
        (L := L) (K := K) n g mc, c ∈ S →
      (NonuniformMajority L K).transitionKernel c
        {c' | ¬ PhaseOnlyWindows.Phase1Win (L := L) (K := K) n c'} ≤ q) :
    ∀ c ∈ Phase1FarPhiSurvival.phase1GapFloorEntryGate
        (L := L) (K := K) n g mc, c ∈ S →
      (NonuniformMajority L K).transitionKernel c
        (Phase1FarPhiSurvival.phase1GapFloorEntryGate
          (L := L) (K := K) n g mc)ᶜ ≤ q := by
  intro c hc hS
  exact (phase1GapFloorEntry_escape_le_phase1_escape n g mc c hc).trans
    (hPhase c hc hS)

/-! ## Reachable endpoint closure -/

/-- The genuine endpoint produced by a far-mass drain.  Non-Main neutrality is
not repeated here: on reachable configurations it follows deterministically
from the protocol invariants. -/
def Phase1Drained (n : ℕ) (c : Config (AgentState L K)) : Prop :=
  PhaseOnlyWindows.Phase1Win (L := L) (K := K) n c ∧
    Phase1FarPhi.farPhiN c = 0

/-- A reachable drained endpoint has the full phase-2 initialization payload.
The role-partition invariant rules out transient roles in the exact phase-1
window, and the non-Main small-bias invariant supplies the neutral value `3`
for every Reserve or Clock agent. -/
theorem phase1Drained_to_phase1Safe (init c : Config (AgentState L K))
    (hinit : validInitial init)
    (hreach : (NonuniformMajority L K).Reachable init c)
    (n : ℕ) (h : Phase1Drained (L := L) (K := K) n c) :
    Phase1FarPhi.Phase1Safe (L := L) (K := K) n c := by
  refine ⟨h.1, ?_, h.2⟩
  intro a ha hnotMain
  have hpost : ∀ b ∈ c, b.phase.val ≥ 1 := by
    intro b hb
    have hb1 := h.1.2 b hb
    omega
  have hroles := post_phase_zero_role_partition (L := L) (K := K)
    init c hinit hreach hpost a ha
  rcases hroles with hmain | hreserve | hclock | hphase10
  · exact False.elim (hnotMain hmain)
  · exact reachable_nonMain_smallBias_zero (L := L) (K := K)
      init c hinit hreach a ha (Or.inl hreserve)
  · exact reachable_nonMain_smallBias_zero (L := L) (K := K)
      init c hinit hreach a ha (Or.inr hclock)
  · have hphase1 := h.1.2 a ha
    omega

/-- Every agent at a reachable drained endpoint lies in the three-value range
accepted by phase-2 initialization. -/
theorem all_bias_in234_of_phase1Drained (init c : Config (AgentState L K))
    (hinit : validInitial init)
    (hreach : (NonuniformMajority L K).Reachable init c)
    (n : ℕ) (h : Phase1Drained (L := L) (K := K) n c) :
    ∀ a ∈ c, a.smallBias.val ∈ ({2, 3, 4} : Finset ℕ) :=
  Phase1FarPhi.all_bias_in234_of_phase1Safe n c
    (phase1Drained_to_phase1Safe init c hinit hreach n h)

#print axioms Transition_biasZ_pair_eq_of_phase1
#print axioms Transition_mainCount_pair_eq_of_phase1
#print axioms centredBiasSum_stepOrSelf_eq_of_phase1Win
#print axioms mainCount_stepOrSelf_eq_of_phase1Win
#print axioms structural_facts_on_support
#print axioms phase1GapFloorEntry_escape_le_phase1_escape
#print axioms phase1GapFloorEntry_leak_of_phase1_escape
#print axioms phase1Drained_to_phase1Safe
#print axioms all_bias_in234_of_phase1Drained

end Phase1GapFloorEntryClosure
end Ripple.PopulationProtocol.ExactMajority
