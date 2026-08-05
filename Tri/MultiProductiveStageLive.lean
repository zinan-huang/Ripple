/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.MultiProductiveInvolvingInvariant

/-!
# Live states of a proper productive-event stage

The capped global target rules out a zero-productive-mass state while the
stage is live.  Indeed, failure of the target rules out consensus, while the
protected pairwise gap supplies two copies of the plurality species.  Hence a
productive `XXY` reaction has positive weight.
-/

namespace Tri.Multi

open scoped BigOperators ENNReal

variable {m n : ℕ}

/-- A proper-stage state before any of its four stopping conditions occurs. -/
def ProductiveProperStageLive
    (X : Species m) (S d target K : ℕ)
    (q : Config m n × ℕ) : Prop :=
  HasPairwiseGap q.1 X d ∧ count q.1 X ≤ S ∧
    ¬ HasPairwiseGap q.1 X target ∧ q.2 < K

noncomputable instance productiveProperStageLiveDecidable
    (X : Species m) (S d target K : ℕ) :
    DecidablePred
      (fun q : Config m n × ℕ =>
        ProductiveProperStageLive X S d target K q) :=
  Classical.decPred _

/-- A live proper-stage configuration has positive productive mass.  The
assumption `target ≤ n` is why the paper caps the progress target at `n`. -/
theorem productiveMass_ne_zero_of_pairwiseGap_not_target
    (c : Config m n) (h3 : 3 ≤ n) (X : Species m)
    (d target : ℕ) (hd2 : 2 ≤ d) (htargetn : target ≤ n)
    (hgap : HasPairwiseGap c X d)
    (hnotTarget : ¬ HasPairwiseGap c X target) :
    productiveMass c h3 ≠ 0 := by
  classical
  have hnotConsensus : ¬ ConsensusOn c X := by
    intro hcons
    apply hnotTarget
    have hcountX : count c X = n := hcons
    have hother := (consensusOn_iff_other_zero c X).mp hcons
    intro Y hYX
    have hcountY : count c Y = 0 := hother Y hYX
    omega
  have hcountXlt : count c X < n := by
    unfold ConsensusOn at hnotConsensus
    have hcountXle : count c X ≤ n := by
      have htotal := count_add_zSum c X
      omega
    omega
  have hzpos : 0 < zSum c X := by
    have htotal := count_add_zSum c X
    omega
  have hcountX2 : 2 ≤ count c X := by
    unfold HasPairwiseGap at hnotTarget
    push Not at hnotTarget
    obtain ⟨Y, hYX, _hYtarget⟩ := hnotTarget
    have hYgap := hgap Y hYX
    omega
  have hterm :
      0 < Nat.choose (count c X) 2 * zSum c X :=
    Nat.mul_pos (Nat.choose_pos hcountX2) hzpos
  have hweight : 0 < productiveWeight c := by
    rw [productiveWeight_eq_sum_choose_mul_zSum]
    have hsingle :
        Nat.choose (count c X) 2 * zSum c X ≤
          ∑ winner : Species m,
            Nat.choose (count c winner) 2 * zSum c winner := by
      exact Finset.single_le_sum
        (fun winner _ =>
          Nat.zero_le (Nat.choose (count c winner) 2 * zSum c winner))
        (Finset.mem_univ X)
    exact hterm.trans_le hsingle
  rw [productiveMass_eq]
  exact ENNReal.div_ne_zero.mpr
    ⟨by exact_mod_cast hweight.ne',
      ENNReal.natCast_ne_top (Nat.choose n 3)⟩

/-- Specialization to the paper's capped proper-stage target. -/
theorem productiveMass_ne_zero_of_properStageLive
    (c : Config m n) (h3 : 3 ≤ n) (X : Species m)
    (D : ℕ) (hD4 : 4 ≤ D)
    (hgap : HasPairwiseGap c X (D / 2))
    (hnotTarget : ¬ HasPairwiseGap c X (properStageTarget D n)) :
    productiveMass c h3 ≠ 0 :=
  productiveMass_ne_zero_of_pairwiseGap_not_target
    c h3 X (D / 2) (properStageTarget D n)
    (by omega) (properStageTarget_le_population D n)
    hgap hnotTarget

end Tri.Multi

#print axioms Tri.Multi.productiveMass_ne_zero_of_pairwiseGap_not_target
#print axioms Tri.Multi.productiveMass_ne_zero_of_properStageLive
