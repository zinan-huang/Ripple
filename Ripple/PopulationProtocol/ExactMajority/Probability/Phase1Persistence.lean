import Ripple.PopulationProtocol.ExactMajority.Probability.Phase1GapFloorEntryClosure
import Ripple.PopulationProtocol.ExactMajority.Probability.TimeTheorem

/-!
# Deterministic persistence of Phase-1 observables

For a pair whose input agents both have phase 1, each non-Main output
preserves its own input's small bias. Consequently, non-Main neutrality
persists under every chosen-pair update and every scheduler draw.

Main count and the centred Main bias sum persist under the same input
window. Their chosen-pair proofs reuse the conservation theorems in
Phase1GapFloorEntryClosure.

These statements allow a clock to leave Phase 1 during the update.
-/

namespace Ripple.PopulationProtocol.ExactMajority
namespace Phase1Persistence

variable {L K : ℕ}

/-- On a Phase-1 input pair, each non-Main output retains the small bias
of its corresponding input. Clock timeout is allowed. -/
theorem Transition_nonMain_smallBias_phase1_pair
    (s t : AgentState L K)
    (hs : s.phase.val = 1) (ht : t.phase.val = 1) :
    ((Transition L K s t).1.role ≠ Role.main →
      (Transition L K s t).1.smallBias = s.smallBias) ∧
    ((Transition L K s t).2.role ≠ Role.main →
      (Transition L K s t).2.smallBias = t.smallBias) := by
  obtain ⟨hleftRole, hrightRole⟩ :=
    PhaseOnlyWindows.Transition_role_phase1
      (L := L) (K := K) s t hs ht
  have hepi :=
    Phase1Convergence.phaseEpidemicUpdate_eq_self_of_phase1
      (L := L) (K := K) s t hs ht
  have hsp : s.phase = ⟨1, by decide⟩ := Fin.ext hs
  constructor
  · intro hnotMain
    have hnb : ¬ (s.role = Role.main ∧ t.role = Role.main) := by
      intro hboth
      exact hnotMain (hleftRole.trans hboth.1)
    have hpair :=
      PhaseOnlyWindows.Phase1Transition_eq_of_not_both_main
        (L := L) (K := K) s t hnb
    unfold Transition
    rw [hepi]
    simp only [hsp]
    rw [finishPhase10Entry_smallBias, hpair, clockCounterStep_smallBias]
  · intro hnotMain
    have hnb : ¬ (s.role = Role.main ∧ t.role = Role.main) := by
      intro hboth
      exact hnotMain (hrightRole.trans hboth.2)
    have hpair :=
      PhaseOnlyWindows.Phase1Transition_eq_of_not_both_main
        (L := L) (K := K) s t hnb
    unfold Transition
    rw [hepi]
    simp only [hsp]
    rw [finishPhase10Entry_smallBias, hpair, clockCounterStep_smallBias]

/-- Non-Main neutrality persists under every chosen-pair update from
the Phase-1 window, including an update in which a clock advances. -/
theorem nonMainNeutral_stepOrSelf_of_phase1Win
    (n : ℕ) (c : Config (AgentState L K))
    (hwin : PhaseOnlyWindows.Phase1Win (L := L) (K := K) n c)
    (hneutral : Phase1FarPhi.NonMainNeutral c)
    (r₁ r₂ : AgentState L K) :
    Phase1FarPhi.NonMainNeutral
      (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂) := by
  by_cases happ : Protocol.Applicable c r₁ r₂
  · have hmleft : r₁ ∈ c :=
      Multiset.mem_of_le
        (show ({r₁, r₂} : Multiset (AgentState L K)) ≤ c from happ)
        (by simp)
    have hmright : r₂ ∈ c :=
      Multiset.mem_of_le
        (show ({r₁, r₂} : Multiset (AgentState L K)) ≤ c from happ)
        (by simp)
    have hpair :=
      Transition_nonMain_smallBias_phase1_pair
        r₁ r₂ (hwin.2 r₁ hmleft) (hwin.2 r₂ hmright)
    have hroles :=
      PhaseOnlyWindows.Transition_role_phase1
        (L := L) (K := K) r₁ r₂
        (hwin.2 r₁ hmleft) (hwin.2 r₂ hmright)
    have hc' :
        Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂ =
          c - {r₁, r₂} +
            {(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2} := by
      unfold Protocol.stepOrSelf
      rw [if_pos happ] <;> rfl
    intro a ha hnotMain
    rw [hc'] at ha
    rcases Multiset.mem_add.mp ha with hold | hnew
    · exact hneutral a
        (Multiset.mem_of_le (Multiset.sub_le_self _ _) hold) hnotMain
    · have hnew' :
          a = (Transition L K r₁ r₂).1 ∨
            a = (Transition L K r₁ r₂).2 := by
        simpa using hnew
      rcases hnew' with rfl | rfl
      · rw [hpair.1 hnotMain]
        apply hneutral r₁ hmleft
        intro hmain
        exact hnotMain (hroles.1.trans hmain)
      · rw [hpair.2 hnotMain]
        apply hneutral r₂ hmright
        intro hmain
        exact hnotMain (hroles.2.trans hmain)
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]
    exact hneutral

/-- Non-Main neutrality persists under an arbitrary scheduler draw from
the Phase-1 window. -/
theorem nonMainNeutral_applyDraw_of_phase1Win
    (n : ℕ) (c : Config (AgentState L K))
    (hwin : PhaseOnlyWindows.Phase1Win (L := L) (K := K) n c)
    (hneutral : Phase1FarPhi.NonMainNeutral c)
    (d : TimeTheorem.Draw L K) :
    Phase1FarPhi.NonMainNeutral (TimeTheorem.applyDraw c d) := by
  cases d with
  | none => exact hneutral
  | some p =>
      exact nonMainNeutral_stepOrSelf_of_phase1Win
        n c hwin hneutral p.1.1 p.2.1

/-- A chosen-pair update from the Phase-1 window preserves Main count. -/
theorem mainCount_stepOrSelf_of_phase1Win
    (n : ℕ) (c : Config (AgentState L K))
    (hwin : PhaseOnlyWindows.Phase1Win (L := L) (K := K) n c)
    (r₁ r₂ : AgentState L K) :
    RoleSplitConcentration.mainCount
        (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂) =
      RoleSplitConcentration.mainCount c := by
  exact Phase1GapFloorEntryClosure.mainCount_stepOrSelf_eq_of_phase1Win
    n c hwin r₁ r₂

/-- A chosen-pair update from the Phase-1 window preserves the centred
Main bias sum. -/
theorem centredBiasSum_stepOrSelf_of_phase1Win
    (n : ℕ) (c : Config (AgentState L K))
    (hwin : PhaseOnlyWindows.Phase1Win (L := L) (K := K) n c)
    (r₁ r₂ : AgentState L K) :
    AveragingRate.centredBiasSum
        (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂) =
      AveragingRate.centredBiasSum c := by
  exact Phase1GapFloorEntryClosure.centredBiasSum_stepOrSelf_eq_of_phase1Win
    n c hwin r₁ r₂

/-- An arbitrary scheduler draw from the Phase-1 window preserves Main count. -/
theorem mainCount_applyDraw_of_phase1Win
    (n : ℕ) (c : Config (AgentState L K))
    (hwin : PhaseOnlyWindows.Phase1Win (L := L) (K := K) n c)
    (d : TimeTheorem.Draw L K) :
    RoleSplitConcentration.mainCount (TimeTheorem.applyDraw c d) =
      RoleSplitConcentration.mainCount c := by
  cases d with
  | none => rfl
  | some p =>
      exact mainCount_stepOrSelf_of_phase1Win n c hwin p.1.1 p.2.1

/-- An arbitrary scheduler draw from the Phase-1 window preserves the
centred Main bias sum. -/
theorem centredBiasSum_applyDraw_of_phase1Win
    (n : ℕ) (c : Config (AgentState L K))
    (hwin : PhaseOnlyWindows.Phase1Win (L := L) (K := K) n c)
    (d : TimeTheorem.Draw L K) :
    AveragingRate.centredBiasSum (TimeTheorem.applyDraw c d) =
      AveragingRate.centredBiasSum c := by
  cases d with
  | none => rfl
  | some p =>
      exact centredBiasSum_stepOrSelf_of_phase1Win n c hwin p.1.1 p.2.1

end Phase1Persistence
end Ripple.PopulationProtocol.ExactMajority
