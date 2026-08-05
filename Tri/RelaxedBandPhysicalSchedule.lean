/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.RelaxedBandPhysicalLadder

/-!
# The concrete dyadic minority schedule

The minority scale is divided by two at every rung.  Running through
`log₂ P + 1` rungs includes the final scale-one rung, whose upper checkpoint
is exact all-`X` consensus.
-/

namespace Tri

open scoped ENNReal

/-- Minority scale after `j` halvings. -/
def relaxedDyadicScale (P j : ℕ) : ℕ :=
  P / 2 ^ j

/-- Number of rungs required to include the final scale-one rung. -/
def relaxedDyadicStageCount (P : ℕ) : ℕ :=
  Nat.log 2 P + 1

/-- Consecutive dyadic endpoints agree exactly. -/
theorem relaxedDyadicScale_link (n P j : ℕ) :
    relaxedDyadicTarget n (relaxedDyadicScale P j) =
      relaxedDyadicStart n (relaxedDyadicScale P (j + 1)) := by
  unfold relaxedDyadicTarget relaxedDyadicStart relaxedDyadicScale
  rw [pow_succ, Nat.div_div_eq_div_mul]

/-- Every scale used by the schedule is positive. -/
theorem relaxedDyadicScale_pos
    (P j : ℕ) (hP : P ≠ 0)
    (hj : j < relaxedDyadicStageCount P) :
    0 < relaxedDyadicScale P j := by
  unfold relaxedDyadicScale
  apply Nat.div_pos
  · apply Nat.pow_le_of_le_log hP
    unfold relaxedDyadicStageCount at hj
    omega
  · exact pow_pos (by norm_num) j

/-- The checkpoint after all scheduled rungs has minority scale zero. -/
theorem relaxedDyadicScale_final
    (P : ℕ) :
    relaxedDyadicScale P (relaxedDyadicStageCount P) = 0 := by
  unfold relaxedDyadicScale relaxedDyadicStageCount
  apply Nat.div_eq_of_lt
  exact Nat.lt_pow_succ_log_self (by norm_num) P

/-- A certified family of dyadic rungs reaches exact all-`X` consensus on one
raw physical chain. -/
theorem relaxedDyadicSchedule_raw_consensus
    (r : RelaxedRate) (n P : ℕ)
    (S : ℕ → RelaxedDyadicRungData r n)
    (hstageP :
      ∀ j < relaxedDyadicStageCount P,
        (S j).P = relaxedDyadicScale P j) :
    terminalFailureMass
        (iter
          (freeze (fun x : ℕ => x = n)
            (relaxedTriChain r n))
          (∑ j ∈ Finset.range (relaxedDyadicStageCount P),
            relaxedDyadicLadderHorizon n S j)
          (relaxedDyadicStart n P))
        (fun x : ℕ => x = n) ≤
      ∑ j ∈ Finset.range (relaxedDyadicStageCount P),
        relaxedDyadicLadderError r n S j := by
  have hraw :=
    relaxedDyadicLadder_raw_failure
      r n (relaxedDyadicStageCount P)
      (relaxedDyadicScale P) S hstageP
      (fun j hj => by
        rw [hstageP j hj]
        exact relaxedDyadicScale_link n P j)
  let A :=
    RelaxedDyadicLadderCheckpoint n
      (relaxedDyadicScale P) (relaxedDyadicStageCount P)
  have hA : ∀ x, A x ↔ x = n := by
    intro x
    simp [A, RelaxedDyadicLadderCheckpoint,
      relaxedDyadicScale_final, relaxedDyadicStart]
  have hfreeze :
      freeze A (relaxedTriChain r n) =
        freeze (fun x : ℕ => x = n) (relaxedTriChain r n) := by
    funext x
    unfold freeze
    by_cases hx : A x
    · rw [if_pos hx, if_pos ((hA x).1 hx)]
    · rw [if_neg hx, if_neg (fun hn => hx ((hA x).2 hn))]
  change terminalFailureMass
      (iter (freeze A (relaxedTriChain r n))
        (∑ j ∈ Finset.range (relaxedDyadicStageCount P),
          relaxedDyadicLadderHorizon n S j)
        (relaxedDyadicStart n (relaxedDyadicScale P 0)))
      A ≤ _ at hraw
  rw [hfreeze] at hraw
  have hmass :
      terminalFailureMass
          (iter
            (freeze (fun x : ℕ => x = n)
              (relaxedTriChain r n))
            (∑ j ∈ Finset.range (relaxedDyadicStageCount P),
              relaxedDyadicLadderHorizon n S j)
            (relaxedDyadicStart n (relaxedDyadicScale P 0)))
          A =
        terminalFailureMass
          (iter
            (freeze (fun x : ℕ => x = n)
              (relaxedTriChain r n))
            (∑ j ∈ Finset.range (relaxedDyadicStageCount P),
              relaxedDyadicLadderHorizon n S j)
            (relaxedDyadicStart n (relaxedDyadicScale P 0)))
          (fun x : ℕ => x = n) := by
    unfold terminalFailureMass
    apply tsum_congr
    intro x
    by_cases hx : A x
    · rw [if_pos hx, if_pos ((hA x).1 hx)]
    · rw [if_neg hx, if_neg (fun hn => hx ((hA x).2 hn))]
  rw [hmass] at hraw
  simpa [relaxedDyadicScale, relaxedDyadicStart] using hraw

end Tri

#print axioms Tri.relaxedDyadicScale_link
#print axioms Tri.relaxedDyadicScale_pos
#print axioms Tri.relaxedDyadicScale_final
#print axioms Tri.relaxedDyadicSchedule_raw_consensus
