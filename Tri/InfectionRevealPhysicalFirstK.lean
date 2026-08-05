/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.InfectionRevealPhysicalWordLaw
import Tri.InfectionRevealPhysicalPath

/-!
# The physical reveal path stopped at its first `k` identities

A live quotient state retains the physical coordinate required by the next
raw record law and its complete revealed word.  Once the first `k` identities
exist, the done state retains only that prefix.  In particular, a two-identity
batch crossing from `k - 1` does not leak its overshoot identity into the
stopped result.
-/

namespace Tri

/-- The physical path has accumulated at least `k` activated identities. -/
def InfectionRevealPhysicalFirstKReached
    {n : ℕ} (k : ℕ)
    (q : InfectionRevealPhysicalPathState n) : Prop :=
  k ≤ q.revealed.length

/-- Data-minimal quotient of a physical path stopped at its first `k`
identities. -/
inductive InfectionRevealFirstKQuotient (n k : ℕ)
  | live
      (current : InfectionRevealPhysicalState n)
      (revealed : List (Fin n))
  | done
      (word : List (Fin n))

namespace InfectionRevealFirstKQuotient

/-- Project a path to its live state or durable first-`k` word. -/
def ofPath
    {n : ℕ} (k : ℕ)
    (q : InfectionRevealPhysicalPathState n) :
    InfectionRevealFirstKQuotient n k :=
  if k ≤ q.revealed.length then
    .done (q.revealed.take k)
  else
    .live q.current q.revealed

/-- Apply a raw physical record directly to a live quotient state. -/
noncomputable def afterRecord
    {n k : ℕ}
    {s : InfectionRevealPhysicalState n}
    (revealed : List (Fin n))
    (r : InfectionRevealRecord s) :
    InfectionRevealFirstKQuotient n k :=
  let nextWord := revealed ++ r.revealedIds
  if k ≤ nextWord.length then
    .done (nextWord.take k)
  else
    .live r.after nextWord

/-- Projection commutes with one physical record. -/
@[simp] theorem ofPath_afterRecord
    {n k : ℕ}
    (q : InfectionRevealPhysicalPathState n)
    (r : InfectionRevealRecord q.current) :
    ofPath k (q.afterRecord r) =
      afterRecord (k := k) q.revealed r :=
  rfl

/-- The absorbing raw-step kernel on the stopped quotient. -/
noncomputable def step
    (n : ℕ) (h3 : 3 ≤ n) (k : ℕ) :
    InfectionRevealFirstKQuotient n k →
      PMF (InfectionRevealFirstKQuotient n k)
  | .done word =>
      PMF.pure (.done word)
  | .live current revealed =>
      (infectionRevealRecordPMF n h3 current).map
        (fun r => afterRecord (k := k) revealed r)

end InfectionRevealFirstKQuotient

noncomputable instance infectionRevealPhysicalFirstKReachedDecidable
    (n k : ℕ) :
    DecidablePred
      (@InfectionRevealPhysicalFirstKReached n k) :=
  fun _ => Classical.dec _

/-- The genuine physical path kernel frozen at its first-`k` checkpoint. -/
noncomputable def infectionRevealPhysicalFirstKStep
    (n : ℕ) (h3 : 3 ≤ n) (k : ℕ) :
    InfectionRevealPhysicalPathState n →
      PMF (InfectionRevealPhysicalPathState n) :=
  freeze
    (InfectionRevealPhysicalFirstKReached k)
    (infectionRevealPhysicalPathStep n h3)

/-- The stopped physical path projects exactly to the absorbing first-`k`
quotient kernel. -/
theorem infectionRevealPhysicalFirstKStep_map_quotient
    (n : ℕ) (h3 : 3 ≤ n) (k : ℕ)
    (q : InfectionRevealPhysicalPathState n) :
    (infectionRevealPhysicalFirstKStep n h3 k q).map
        (InfectionRevealFirstKQuotient.ofPath k) =
      InfectionRevealFirstKQuotient.step n h3 k
        (InfectionRevealFirstKQuotient.ofPath k q) := by
  by_cases hk : k ≤ q.revealed.length
  · have hmem : InfectionRevealPhysicalFirstKReached k q := by
      simpa [InfectionRevealPhysicalFirstKReached] using hk
    have hq :
        InfectionRevealFirstKQuotient.ofPath k q =
          .done (q.revealed.take k) := by
      simp [InfectionRevealFirstKQuotient.ofPath, hk]
    unfold infectionRevealPhysicalFirstKStep
    rw [freeze_of_mem q hmem, PMF.pure_map, hq]
    rfl
  · have hnot : ¬ InfectionRevealPhysicalFirstKReached k q := by
      simpa [InfectionRevealPhysicalFirstKReached] using hk
    have hq :
        InfectionRevealFirstKQuotient.ofPath k q =
          .live q.current q.revealed := by
      simp [InfectionRevealFirstKQuotient.ofPath, hk]
    unfold infectionRevealPhysicalFirstKStep
    rw [freeze_of_not_mem q hnot, hq]
    change
      (((infectionRevealRecordPMF n h3 q.current).map
          (InfectionRevealPhysicalPathState.afterRecord q)).map
          (InfectionRevealFirstKQuotient.ofPath k)) =
        (infectionRevealRecordPMF n h3 q.current).map
          (fun r =>
            InfectionRevealFirstKQuotient.afterRecord
              (k := k) q.revealed r)
    rw [PMF.map_comp]
    congr 1

/-- Kernel-level stopped-path quotient. -/
theorem infectionRevealPhysicalFirstKStep_intertwines_quotient
    (n : ℕ) (h3 : 3 ≤ n) (k : ℕ) :
    Intertwines
      (InfectionRevealFirstKQuotient.ofPath k)
      (infectionRevealPhysicalFirstKStep n h3 k)
      (InfectionRevealFirstKQuotient.step n h3 k) :=
  infectionRevealPhysicalFirstKStep_map_quotient n h3 k

/-- The stopped physical path and its data-minimal quotient have the same law
at every raw horizon. -/
theorem infectionRevealPhysicalFirstKStep_iter_map_quotient
    (n : ℕ) (h3 : 3 ≤ n) (k T : ℕ)
    (q : InfectionRevealPhysicalPathState n) :
    (iter (infectionRevealPhysicalFirstKStep n h3 k) T q).map
        (InfectionRevealFirstKQuotient.ofPath k) =
      iter (InfectionRevealFirstKQuotient.step n h3 k) T
        (InfectionRevealFirstKQuotient.ofPath k q) :=
  iter_map_of_intertwines
    (infectionRevealPhysicalFirstKStep_intertwines_quotient n h3 k) T q

end Tri

#print axioms Tri.InfectionRevealFirstKQuotient.ofPath_afterRecord
#print axioms Tri.infectionRevealPhysicalFirstKStep_map_quotient
#print axioms Tri.infectionRevealPhysicalFirstKStep_intertwines_quotient
#print axioms Tri.infectionRevealPhysicalFirstKStep_iter_map_quotient
