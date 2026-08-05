/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.MultiFiniteHorizonEnvelope
import Tri.LazyHitting

/-!
# Finite-horizon consensus transfer

The binary lower envelope controls increasing success events.  Taking
complements converts its all-`X` upper-tail comparison into an upper bound on
the multi-species failure mass outside `X`-consensus.
-/

namespace Tri

open scoped ENNReal

variable {α : Type*}

/-- Failure mass is one minus the complementary success mass. -/
theorem terminalFailureMass_eq_one_sub_success
    (p : PMF α) (A : α → Prop) [DecidablePred A] :
    terminalFailureMass p A =
      1 - ∑' z, if A z then p z else 0 := by
  let success : ℝ≥0∞ := ∑' z, if A z then p z else 0
  have hsuccess_le : success ≤ 1 := by
    calc
      success ≤ ∑' z, p z :=
        ENNReal.tsum_le_tsum fun z => by
          split_ifs <;> simp
      _ = 1 := PMF.tsum_coe p
  have hsuccess_ne_top : success ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top hsuccess_le
  have hpoint :
      ∀ z,
        (if A z then 0 else p z) +
            (if A z then p z else 0) =
          p z := by
    intro z
    split_ifs <;> simp
  have hpartition :
      terminalFailureMass p A + success = 1 := by
    unfold terminalFailureMass success
    rw [← ENNReal.tsum_add, tsum_congr hpoint, PMF.tsum_coe]
  calc
    terminalFailureMass p A =
        (terminalFailureMass p A + success) - success :=
      (ENNReal.add_sub_cancel_right hsuccess_ne_top).symm
    _ = 1 - success := by rw [hpartition]

namespace Multi

variable {m n : ℕ}

noncomputable instance consensusOnDecidable
    (X : Species m) :
    DecidablePred (fun c : Config m n => ConsensusOn c X) :=
  Classical.decPred _

/-- Since every configuration has population `n`, reaching count at least
`n` is exactly consensus on the distinguished species. -/
theorem n_le_count_iff_consensusOn
    (c : Config m n) (X : Species m) :
    n ≤ count c X ↔ ConsensusOn c X := by
  constructor
  · intro h
    unfold ConsensusOn
    have hbound := (c.1 X).isLt
    unfold count at h ⊢
    omega
  · intro h
    unfold ConsensusOn at h
    omega

/-- At every finite horizon, failure of the physical multi-species chain to
reach `X`-consensus is bounded by failure of its ordinary binary lower
envelope to reach count `n`. -/
theorem multiStep_consensus_failure_le_triChain
    (c : Config m n) (X : Species m) (h3 : 3 ≤ n) (T : ℕ) :
    terminalFailureMass
        (iter (fun d : Config m n => multiStep d h3) T c)
        (fun d => ConsensusOn d X) ≤
      terminalFailureMass
        (iter (Tri.triChain n) T (count c X))
        (fun x => n ≤ x) := by
  have hsuccess :
      (∑' x, if n ≤ x then
          iter (Tri.triChain n) T (count c X) x else 0) ≤
        ∑' d, if ConsensusOn d X then
          iter (fun q : Config m n => multiStep q h3) T c d else 0 := by
    calc
      (∑' x, if n ≤ x then
          iter (Tri.triChain n) T (count c X) x else 0) ≤
          ∑' d, if n ≤ count d X then
            iter (fun q : Config m n => multiStep q h3) T c d else 0 :=
        triChain_iter_upperTail_le_multiStep_iter_count
          c X h3 T n
      _ = ∑' d, if ConsensusOn d X then
            iter (fun q : Config m n => multiStep q h3) T c d else 0 := by
        apply tsum_congr
        intro d
        by_cases hcount : n ≤ count d X
        · have hcons := (n_le_count_iff_consensusOn d X).1 hcount
          simp [hcount, hcons]
        · have hcons : ¬ ConsensusOn d X := by
            intro hc
            exact hcount ((n_le_count_iff_consensusOn d X).2 hc)
          simp [hcount, hcons]
  rw [terminalFailureMass_eq_one_sub_success,
    terminalFailureMass_eq_one_sub_success]
  exact tsub_le_tsub_left hsuccess 1

end Multi
end Tri

#print axioms Tri.terminalFailureMass_eq_one_sub_success
#print axioms Tri.Multi.n_le_count_iff_consensusOn
#print axioms Tri.Multi.multiStep_consensus_failure_le_triChain
