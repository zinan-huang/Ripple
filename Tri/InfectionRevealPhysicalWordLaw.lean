/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.InfectionRevealPhysicalPairLaw
import Tri.DoubleBInvariant

/-!
# The chronological word law of physical activation batches

The total physical record uses an arbitrary effective witness on an
unreachable `none` atom of a positive event.  Consequently its chronological
word and the raw optional batch are not equal on every record value.  They are
equal on support, which is exactly the statement needed to identify their PMF
pushforwards.
-/

namespace Tri

open scoped ENNReal

/-- Chronological identity word represented by a physical activation batch. -/
def InfectionRevealBatch.ids
    {n : ℕ} {v : InfectionInactiveView n} :
    InfectionRevealBatch v → List (Fin n)
  | .none => []
  | .one i => [i.1]
  | .two p => [p.1.1.1, p.1.2.1]

/-- A stored positive witness gives exactly the word represented by its batch. -/
theorem InfectionRevealRecord.revealedIds_eq_batch_ids_of_some
    {n : ℕ} (s : InfectionRevealPhysicalState n)
    (e : InfectionEvent) (w : InfectionRevealWitness s e)
    (he : InfectionEvent.weight s.coarse.1 e ≠ 0) :
    (InfectionRevealRecord.revealedIds
      ({ event := e, witness := some w } :
        InfectionRevealRecord s)) =
      (infectionRevealBatchOf s e (some w)).ids := by
  cases e <;>
    simp [InfectionRevealRecord.revealedIds,
      InfectionRevealRecord.effectiveWitness,
      InfectionRevealBatch.ids, infectionRevealBatchOf,
      infectionRevealPositiveIds, he]

/-- At zero event weight the reachable `none` witness gives the empty word. -/
theorem InfectionRevealRecord.revealedIds_eq_batch_ids_of_zero_none
    {n : ℕ} (s : InfectionRevealPhysicalState n)
    (e : InfectionEvent)
    (he : InfectionEvent.weight s.coarse.1 e = 0) :
    (InfectionRevealRecord.revealedIds
      ({ event := e, witness := none } :
        InfectionRevealRecord s)) =
      (infectionRevealBatchOf s e none).ids := by
  simp [InfectionRevealRecord.revealedIds,
    InfectionRevealBatch.ids, infectionRevealBatchOf, he]

/-- At a fixed event, the record word and batch word have the same law. -/
theorem infectionRevealWitnessPMF_map_word
    {n : ℕ} (s : InfectionRevealPhysicalState n)
    (e : InfectionEvent) :
    (infectionRevealWitnessPMF s e).map
        (fun w =>
          InfectionRevealRecord.revealedIds
            ({ event := e, witness := w } :
              InfectionRevealRecord s)) =
      (infectionRevealWitnessPMF s e).map
        (fun w => (infectionRevealBatchOf s e w).ids) := by
  apply PMF.map_change_on_zero_mass
  intro w hdiff
  by_cases he : InfectionEvent.weight s.coarse.1 e = 0
  · cases w with
    | none =>
        exact absurd
          (InfectionRevealRecord.revealedIds_eq_batch_ids_of_zero_none
            s e he)
          hdiff
    | some w =>
        simp [infectionRevealWitnessPMF, he]
  · cases w with
    | none =>
        exact infectionRevealWitnessPMF_none s e he
    | some w =>
        exact absurd
          (InfectionRevealRecord.revealedIds_eq_batch_ids_of_some
            s e w he)
          hdiff

/-- The genuine record word law is the exact zero/one/two batch law pushed
through its chronological list representation. -/
theorem infectionRevealRecordPMF_map_revealedIds
    (n : ℕ) (h3 : 3 ≤ n) (s : InfectionRevealPhysicalState n) :
    (infectionRevealRecordPMF n h3 s).map
        InfectionRevealRecord.revealedIds =
      (infectionRevealBatchPMF n h3 s).map
        InfectionRevealBatch.ids := by
  unfold infectionRevealRecordPMF infectionRevealBatchPMF
  rw [PMF.map_bind, PMF.map_bind]
  simp_rw [PMF.map_comp]
  congr 1
  funext e
  exact infectionRevealWitnessPMF_map_word s e

end Tri

#print axioms Tri.InfectionRevealRecord.revealedIds_eq_batch_ids_of_some
#print axioms Tri.InfectionRevealRecord.revealedIds_eq_batch_ids_of_zero_none
#print axioms Tri.infectionRevealWitnessPMF_map_word
#print axioms Tri.infectionRevealRecordPMF_map_revealedIds
