/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Phase-2 initializer errors reach the Phase-10 ready surface

An initializer error creates an active Phase-10 seed.  If the configuration is
already entirely in Phase 10, signed-sum trichotomy gives `Phase10Ready`
immediately.  Otherwise the existing deterministic phase epidemic reaches an
all-Phase-10 configuration.  Activity at the first all-Phase-10 boundary is
provided by the protocol's canonical Phase-10 entry rule.
-/

import Ripple.PopulationProtocol.ExactMajority.Probability.Phase2EntryDispatcher
import Ripple.PopulationProtocol.ExactMajority.Probability.SeedStepAndSignThreading

namespace Ripple.PopulationProtocol.ExactMajority
namespace Phase2EntryDispatcher

open scoped Classical
open Phase10Drop

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-- Any active all-Phase-10 card-`n` configuration is a valid Phase-10 work
input.  No initial-configuration provenance is needed for this trichotomy. -/
theorem phase10Ready_of_allPhase10_card_active
    (n : ℕ) (c : Config (AgentState L K))
    (hAll : AllPhase10 c)
    (hcard : c.card = n)
    (hactive : hasActiveAgent c) :
    Phase10Drop.Phase10Ready (L := L) (K := K) n c := by
  rcases lt_trichotomy (phase10ActiveSignedSum c) 0 with hneg | hzero | hpos
  · exact Or.inr (Or.inl ⟨hAll, hcard, hneg⟩)
  · exact Or.inr (Or.inr ⟨⟨hAll, hcard, hzero⟩, hactive⟩)
  · exact Or.inl ⟨hAll, hcard, hpos⟩

/-- If a non-Phase-10 root reaches an all-Phase-10 configuration, the boundary
step creates an active backup source.  Once the chain is all Phase 10, the
existing Phase-10 liveness invariant preserves that source. -/
theorem hasActiveAgent_of_reachable_allPhase10_of_not_allPhase10
    {c d : Config (AgentState L K)}
    (hreach : (NonuniformMajority L K).Reachable c d)
    (hnot : ¬ AllPhase10 c)
    (hAll : AllPhase10 d) :
    hasActiveAgent d := by
  revert hnot hAll
  induction hreach with
  | refl =>
      intro hnot hAll
      exact False.elim (hnot hAll)
  | tail hprev hstep ih =>
      rename_i prev final
      intro hnot hAll
      by_cases hmid : AllPhase10 prev
      · have hactiveMid := ih hnot hmid
        exact phase10_hasActiveAgent_preserved_by_step
          (L := L) (K := K) prev final hmid hactiveMid hstep
      · exact hasActiveAgent_of_step_to_all_phase10_of_not_all_phase10
          (L := L) (K := K) prev final hmid hAll hstep

/-- A faithful Phase-2 initializer-error seed can be scheduled to the exact
Phase-10 ready surface. -/
theorem recovery10Entry_reaches_ready
    (n : ℕ) (c : Config (AgentState L K))
    (hentry : Recovery10Entry (L := L) (K := K) n c) :
    ∃ c10, (NonuniformMajority L K).Reachable c c10 ∧
      Phase10Drop.Phase10Ready (L := L) (K := K) n c10 := by
  rcases hentry with ⟨hcard, a, ha, haPhase, haFull, haBad⟩
  have hactive : hasActiveAgent c := ⟨a, ha, haFull⟩
  by_cases hc2 : 2 ≤ c.card
  · rcases phase_epidemic_reachability_from_config
        (L := L) (K := K) c hc2 with
      ⟨final, hreach, hcommon, hmax⟩
    have hseedMax : 10 ≤ maxPhase c := by
      have haLe : a.phase.val ≤ maxPhase c := by
        unfold maxPhase
        exact Finset.le_sup (f := fun b : AgentState L K => b.phase.val)
          (by simpa using ha)
      rw [haPhase] at haLe
      exact haLe
    have hfinalMax : 10 ≤ maxPhase final := le_trans hseedMax hmax
    have hAllFinal : AllPhase10 final := by
      intro b hb
      have hbCommon := hcommon b hb
      have hbUpper := b.phase.isLt
      omega
    have hcardFinal : final.card = n := by
      rw [Protocol.reachable_card_eq (P := NonuniformMajority L K) hreach]
      exact hcard
    have hactiveFinal : hasActiveAgent final := by
      by_cases hAllRoot : AllPhase10 c
      · exact (SeedStepAndSignThreading.hasActiveAgent_of_reachable
          (L := L) (K := K) hreach hAllRoot hactive).1
      · exact hasActiveAgent_of_reachable_allPhase10_of_not_allPhase10
          (L := L) (K := K) hreach hAllRoot hAllFinal
    exact ⟨final, hreach,
      phase10Ready_of_allPhase10_card_active
        (L := L) (K := K) n final hAllFinal hcardFinal hactiveFinal⟩
  · have hpos : 0 < c.card := Multiset.card_pos_iff_exists_mem.mpr ⟨a, ha⟩
    have hcardOne : c.card = 1 := by omega
    rcases Multiset.card_eq_one.mp hcardOne with ⟨b, hcb⟩
    have hab : a = b := by
      rw [hcb] at ha
      simpa using ha
    subst b
    have hAll : AllPhase10 c := by
      intro x hx
      rw [hcb] at hx
      simp only [Multiset.mem_singleton] at hx
      subst x
      exact haPhase
    exact ⟨c, Relation.ReflTransGen.refl,
      phase10Ready_of_allPhase10_card_active
        (L := L) (K := K) n c hAll hcard hactive⟩

/-- The named recovery residual is inhabited by the concrete deterministic
Phase-10 epidemic construction. -/
theorem exists_reachable_phase10Ready_of_recovery10Entry
    (n : ℕ) (c : Config (AgentState L K)) :
    Recovery10ReachesReady (L := L) (K := K) n c := by
  intro hentry
  exact recovery10Entry_reaches_ready (L := L) (K := K) n c hentry

#print axioms phase10Ready_of_allPhase10_card_active
#print axioms hasActiveAgent_of_reachable_allPhase10_of_not_allPhase10
#print axioms recovery10Entry_reaches_ready
#print axioms exists_reachable_phase10Ready_of_recovery10Entry

end Phase2EntryDispatcher
end Ripple.PopulationProtocol.ExactMajority
