
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.

# RoleSplitFreeTargetFloor

The Lemma-5.1 floor is not `assignableCount`.  It is the free non-MCR
target pool `Mf + Sf`, where `Sf` includes raw CR, Clock, and Reserve.
Rule 4 (`CR,CR → Clock,Reserve`) is therefore not a death event for the
Lemma-5.1 pool.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.TopSplitInward
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.FreshPoolDeathCorrected

namespace ExactMajority
namespace RoleSplitConcentration

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real BigOperators

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-- Free Main pool `Mf`: unassigned Main agents. -/
def freeMainPred (a : AgentState L K) : Prop :=
  a.role = .main ∧ ¬ a.assigned

/-- Free CR-side pool `Sf`: unassigned raw-CR/Clock/Reserve agents. -/
def freeSidePred (a : AgentState L K) : Prop :=
  (a.role = .cr ∨ a.role = .clock ∨ a.role = .reserve) ∧ ¬ a.assigned

/-- The full Lemma-5.1 free target predicate `Mf ∪ Sf`: unassigned non-MCR agents. -/
def freeTargetPred (a : AgentState L K) : Prop :=
  a.role ≠ .mcr ∧ ¬ a.assigned

/-- Count of free Main agents. -/
noncomputable def freeMainCount (c : Config (AgentState L K)) : ℕ :=
  Multiset.countP (freeMainPred (L := L) (K := K)) c

/-- Count of free CR-side agents, including raw CR, Clock, and Reserve. -/
noncomputable def freeSideCount (c : Config (AgentState L K)) : ℕ :=
  Multiset.countP (freeSidePred (L := L) (K := K)) c

/-- Count of all free non-MCR targets.  This is the Lemma-5.1 floor pool. -/
noncomputable def freeTargetCount (c : Config (AgentState L K)) : ℕ :=
  Multiset.countP (freeTargetPred (L := L) (K := K)) c

/-- The free target predicate is the disjoint union of free Main and free CR-side. -/
theorem freeTargetPred_iff
    (a : AgentState L K) :
    freeTargetPred (L := L) (K := K) a ↔
      freeMainPred (L := L) (K := K) a ∨
        freeSidePred (L := L) (K := K) a := by
  unfold freeTargetPred freeMainPred freeSidePred
  cases a.role <;> simp

/-- The Lemma-5.1 free target count splits as `Mf + Sf`. -/
theorem freeTargetCount_eq_freeMain_add_freeSide
    (c : Config (AgentState L K)) :
    freeTargetCount (L := L) (K := K) c =
      freeMainCount (L := L) (K := K) c +
        freeSideCount (L := L) (K := K) c := by
  classical
  unfold freeTargetCount freeMainCount freeSideCount
  induction c using Multiset.induction with
  | empty => simp
  | cons a c ih =>
      rw [Multiset.countP_cons, Multiset.countP_cons, Multiset.countP_cons, ih]
      have hiff := freeTargetPred_iff (L := L) (K := K) a
      by_cases hM : freeMainPred (L := L) (K := K) a
      · have hnS : ¬ freeSidePred (L := L) (K := K) a := by
          rintro ⟨hs, _⟩
          rcases hM with ⟨hm, _⟩
          rcases hs with h | h | h <;> rw [hm] at h <;> exact absurd h (by decide)
        rw [if_pos hM, if_neg hnS, if_pos (hiff.mpr (Or.inl hM))]; ring
      · by_cases hS : freeSidePred (L := L) (K := K) a
        · rw [if_neg hM, if_pos hS, if_pos (hiff.mpr (Or.inr hS))]; ring
        · rw [if_neg hM, if_neg hS,
            if_neg (fun hT => (hiff.mp hT).elim hM hS)]; ring

end RoleSplitConcentration
end ExactMajority

namespace ExactMajority
namespace RoleSplitConcentration

open scoped Real

theorem scalar_freeTarget_birth_only_lt_one
    {s b : ℝ} (hs : 0 < s) (hb : 0 < b) :
    1 - b * (1 - Real.exp (-2 * s)) < 1 := by
  have h2s : 0 < 2 * s := by nlinarith
  have hexp : Real.exp (-2 * s) < 1 := by
    have hneg : -2 * s < 0 := by nlinarith
    simpa using Real.exp_lt_one_iff.mpr hneg
  have hgap : 0 < 1 - Real.exp (-2 * s) := by linarith
  nlinarith

end RoleSplitConcentration
end ExactMajority
