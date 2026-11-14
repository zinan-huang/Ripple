/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Naturally truncated Phase-7 band stages

The paper drains the bands at indices `l`, `l+1`, and `l+2`, stopping at the
largest index available in `Fin (L+1)`.  This file gives that ordered stage set
as a `Fin m` family, where

  `m = min (l+3) (L+1) - l`.

It also supplies the deterministic adjacent-stage and final-clearance bridges.
No drift or probabilistic composition is introduced here.
-/

import Ripple.PopulationProtocol.ExactMajority.Probability.Phase7BandDefs

namespace Ripple.PopulationProtocol.ExactMajority
namespace Phase7BandStages

open Phase7BandDefs

variable {L K : ℕ}

/-- The number of available stages among `l`, `l+1`, and `l+2`. -/
def phase7StageCount (L l : ℕ) : ℕ :=
  min (l + 3) (L + 1) - l

/-- The `q`-th naturally truncated stage has exponent index `l+q`. -/
def phase7StageIndex (l : ℕ) (hlL : l ≤ L)
    (q : Fin (phase7StageCount L l)) : Fin (L + 1) := by
  have hlcut : l ≤ min (l + 3) (L + 1) :=
    le_min (by omega) (by omega)
  have hq : q.val < min (l + 3) (L + 1) - l := q.isLt
  have hlt : l + q.val < min (l + 3) (L + 1) := by omega
  exact ⟨l + q.val, lt_of_lt_of_le hlt (min_le_right _ _)⟩

@[simp] theorem phase7StageIndex_val (l : ℕ) (hlL : l ≤ L)
    (q : Fin (phase7StageCount L l)) :
    (phase7StageIndex (L := L) l hlL q).val = l + q.val := rfl

/-- If the first requested band exists, the naturally truncated stage family is nonempty. -/
theorem phase7StageCount_pos (l : ℕ) (hlL : l ≤ L) :
    0 < phase7StageCount L l := by
  have hlcut : l < min (l + 3) (L + 1) :=
    lt_min (by omega) (by omega)
  unfold phase7StageCount
  omega

/-- Natural truncation never produces more than the paper's three stages. -/
theorem phase7StageCount_le_three (L l : ℕ) :
    phase7StageCount L l ≤ 3 := by
  have hcut : min (l + 3) (L + 1) ≤ l + 3 := min_le_left _ _
  unfold phase7StageCount
  omega

/-- Every generated stage lies in the requested three-band interval. -/
theorem phase7StageIndex_range (l : ℕ) (hlL : l ≤ L)
    (q : Fin (phase7StageCount L l)) :
    l ≤ (phase7StageIndex (L := L) l hlL q).val ∧
      (phase7StageIndex (L := L) l hlL q).val < l + 3 := by
  have hlcut : l ≤ min (l + 3) (L + 1) :=
    le_min (by omega) (by omega)
  have hq : q.val < min (l + 3) (L + 1) - l := q.isLt
  have hlt : l + q.val < min (l + 3) (L + 1) := by omega
  constructor
  · simp [phase7StageIndex]
  · simpa [phase7StageIndex] using
      (lt_of_lt_of_le hlt (min_le_left (l + 3) (L + 1)))

/-- Consecutive `Fin` stage numbers produce consecutive exponent indices. -/
theorem phase7StageIndex_succ (l : ℕ) (hlL : l ≤ L)
    (q : Fin (phase7StageCount L l))
    (hq : q.val + 1 < phase7StageCount L l) :
    (phase7StageIndex (L := L) l hlL ⟨q.val + 1, hq⟩).val =
      (phase7StageIndex (L := L) l hlL q).val + 1 := by
  simp only [phase7StageIndex_val]
  omega

/-- The last naturally truncated stage. -/
def phase7LastStageIndex (l : ℕ) (hlL : l ≤ L) : Fin (L + 1) :=
  phase7StageIndex (L := L) l hlL
    ⟨phase7StageCount L l - 1, by
      have hm := phase7StageCount_pos (L := L) l hlL
      omega⟩

/-- The successor cutoff of the last stage is exactly the truncated endpoint. -/
theorem phase7LastStageIndex_succ_eq_cutoff (l : ℕ) (hlL : l ≤ L) :
    (phase7LastStageIndex (L := L) l hlL).val + 1 =
      min (l + 3) (L + 1) := by
  have hlcut : l ≤ min (l + 3) (L + 1) :=
    le_min (by omega) (by omega)
  have hm := phase7StageCount_pos (L := L) l hlL
  have hsum : l + phase7StageCount L l = min (l + 3) (L + 1) := by
    exact Nat.add_sub_of_le hlcut
  change l + (phase7StageCount L l - 1) + 1 = min (l + 3) (L + 1)
  omega

/-- A completed stage supplies the ready gate for its immediate successor. -/
theorem stageReady_succ_of_post
    {n l E7 : ℕ} {sigma : Sign} {j j' : Fin (L + 1)}
    {c : Config (AgentState L K)}
    (hnext : j.val + 1 = j'.val)
    (hpost :
      Phase7StageReady (L := L) (K := K) n sigma l E7 j c ∧
        bandCountN (L := L) (K := K) sigma j c = 0) :
    Phase7StageReady (L := L) (K := K) n sigma l E7 j' c := by
  refine ⟨hpost.1.genuine, ?_, hpost.1.pool⟩
  rw [← hnext]
  exact bandClear_succ_of_count_zero
    (L := L) (K := K) sigma j c hpost.1.cleared hpost.2

/-- Clearing the last available stage clears all requested bands below `l+3`.

When `l+1` or `l+2` lies beyond `Fin (L+1)`, the extra part of the strict
`BandClear sigma (l+3)` statement is vacuous by the index's own upper bound. -/
theorem bandClear_add_three_of_last_stage_post
    {sigma : Sign} (l : ℕ) (hlL : l ≤ L)
    (c : Config (AgentState L K))
    (hclear : BandClear (L := L) (K := K) sigma
      (phase7LastStageIndex (L := L) l hlL).val c)
    (hzero : bandCountN (L := L) (K := K) sigma
      (phase7LastStageIndex (L := L) l hlL) c = 0) :
    BandClear (L := L) (K := K) sigma (l + 3) c := by
  have hsucc := bandClear_succ_of_count_zero
    (L := L) (K := K) sigma
    (phase7LastStageIndex (L := L) l hlL) c hclear hzero
  intro k hk
  apply hsucc k
  rw [phase7LastStageIndex_succ_eq_cutoff (L := L) l hlL]
  exact lt_min hk k.isLt

/-- The raw postcondition of the last stage implies the public Phase-7 postcondition. -/
theorem post7Bands_of_last_stage_post
    {n l E7 : ℕ} {sigma : Sign} (hlL : l ≤ L)
    {c : Config (AgentState L K)}
    (hpost :
      Phase7StageReady (L := L) (K := K) n sigma l E7
          (phase7LastStageIndex (L := L) l hlL) c ∧
        bandCountN (L := L) (K := K) sigma
          (phase7LastStageIndex (L := L) l hlL) c = 0) :
    Post7Bands (L := L) (K := K) n sigma l c := by
  exact ⟨hpost.1.genuine,
    bandClear_add_three_of_last_stage_post
      (L := L) (K := K) l hlL c hpost.1.cleared hpost.2⟩

#print axioms phase7StageCount_pos
#print axioms phase7StageCount_le_three
#print axioms phase7StageIndex_range
#print axioms phase7StageIndex_succ
#print axioms phase7LastStageIndex_succ_eq_cutoff
#print axioms stageReady_succ_of_post
#print axioms bandClear_add_three_of_last_stage_post
#print axioms post7Bands_of_last_stage_post

end Phase7BandStages
end Ripple.PopulationProtocol.ExactMajority
