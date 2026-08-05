/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.InfectionRevealPhysicalFirstK
import Tri.InfectionRevealPrefixTimeChange

/-!
# The genuine physical first-prefix kernel is a reveal time change

The physical quotient retains coarse state while live.  Its projection to the
remaining inactive identities and revealed word has a batch transition whose
zero-, one-, and two-identity branches are the stopped ordinary reveal chain
run for zero, one, and two steps.
-/

namespace Tri

noncomputable section

namespace InfectionRevealPrefixCheckpoint

/-- Forget the live coarse coordinate of the physical first-prefix quotient. -/
def ofPhysical
    {n k : ℕ} :
    InfectionRevealFirstKQuotient n k →
      InfectionRevealPrefixCheckpoint n
  | .live current word => .live current.inactive word
  | .done word => .done word

/-- Apply a genuine physical record to a logical live checkpoint. -/
def afterRecord
    {n : ℕ} (k : ℕ)
    {s : InfectionRevealPhysicalState n}
    (word : List (Fin n))
    (r : InfectionRevealRecord s) :
    InfectionRevealPrefixCheckpoint n :=
  if k ≤ word.length then
    .done (word.take k)
  else
    let nextWord := word ++ r.revealedIds
    if k ≤ nextWord.length then
      .done (nextWord.take k)
    else
      .live r.after.inactive nextWord

end InfectionRevealPrefixCheckpoint

/-- On a positive stored witness, the physical successor inactive view is the
remaining view represented by its batch. -/
theorem InfectionRevealRecord.after_inactive_eq_batch_remaining_of_some
    {n : ℕ} (s : InfectionRevealPhysicalState n)
    (e : InfectionEvent) (w : InfectionRevealWitness s e)
    (he : InfectionEvent.weight s.coarse.1 e ≠ 0) :
    (InfectionRevealRecord.after
      ({ event := e, witness := some w } :
        InfectionRevealRecord s)).inactive =
      (infectionRevealBatchOf s e (some w)).remaining := by
  cases e <;>
    simp [InfectionRevealRecord.after,
      InfectionRevealRecord.effectiveWitness,
      infectionRevealBatchOf,
      InfectionRevealBatch.remaining,
      infectionRevealPhysicalAfterPositive,
      he]
  all_goals rfl

/-- On a zero-weight event, the reachable absent witness preserves the
inactive view and represents the empty batch. -/
theorem InfectionRevealRecord.after_inactive_eq_batch_remaining_of_zero_none
    {n : ℕ} (s : InfectionRevealPhysicalState n)
    (e : InfectionEvent)
    (he : InfectionEvent.weight s.coarse.1 e = 0) :
    (InfectionRevealRecord.after
      ({ event := e, witness := none } :
        InfectionRevealRecord s)).inactive =
      (infectionRevealBatchOf s e none).remaining := by
  simp [InfectionRevealRecord.after,
    infectionRevealBatchOf,
    InfectionRevealBatch.remaining, he]

/-- A positive record and its batch give the same stopped logical checkpoint. -/
theorem infectionRevealRecordCheckpoint_eq_afterBatch_of_some
    {n : ℕ} (s : InfectionRevealPhysicalState n)
    (k : ℕ) (word : List (Fin n))
    (e : InfectionEvent) (w : InfectionRevealWitness s e)
    (he : InfectionEvent.weight s.coarse.1 e ≠ 0) :
    InfectionRevealPrefixCheckpoint.afterRecord k word
        ({ event := e, witness := some w } :
          InfectionRevealRecord s) =
      InfectionRevealPrefixCheckpoint.afterBatch
        k s.inactive word
          (infectionRevealBatchOf s e (some w)) := by
  have hword :=
    InfectionRevealRecord.revealedIds_eq_batch_ids_of_some
      s e w he
  have hview :=
    InfectionRevealRecord.after_inactive_eq_batch_remaining_of_some
      s e w he
  rw [InfectionRevealPrefixCheckpoint.afterBatch_eq]
  unfold InfectionRevealPrefixCheckpoint.afterRecord
  rw [hword, hview]

/-- A reachable zero-weight absent witness gives the same empty checkpoint. -/
theorem infectionRevealRecordCheckpoint_eq_afterBatch_of_zero_none
    {n : ℕ} (s : InfectionRevealPhysicalState n)
    (k : ℕ) (word : List (Fin n))
    (e : InfectionEvent)
    (he : InfectionEvent.weight s.coarse.1 e = 0) :
    InfectionRevealPrefixCheckpoint.afterRecord k word
        ({ event := e, witness := none } :
          InfectionRevealRecord s) =
      InfectionRevealPrefixCheckpoint.afterBatch
        k s.inactive word
          (infectionRevealBatchOf s e none) := by
  have hword :=
    InfectionRevealRecord.revealedIds_eq_batch_ids_of_zero_none
      s e he
  have hview :=
    InfectionRevealRecord.after_inactive_eq_batch_remaining_of_zero_none
      s e he
  rw [InfectionRevealPrefixCheckpoint.afterBatch_eq]
  unfold InfectionRevealPrefixCheckpoint.afterRecord
  rw [hword, hview]

/-- At a fixed semantic event, the record checkpoint and batch checkpoint have
the same law. -/
theorem infectionRevealWitnessPMF_map_checkpoint
    {n : ℕ} (s : InfectionRevealPhysicalState n)
    (k : ℕ) (word : List (Fin n))
    (e : InfectionEvent) :
    (infectionRevealWitnessPMF s e).map
        (fun w =>
          InfectionRevealPrefixCheckpoint.afterRecord k word
            ({ event := e, witness := w } :
              InfectionRevealRecord s)) =
      (infectionRevealWitnessPMF s e).map
        (fun w =>
          InfectionRevealPrefixCheckpoint.afterBatch
            k s.inactive word
              (infectionRevealBatchOf s e w)) := by
  apply PMF.map_change_on_zero_mass
  intro w hdiff
  by_cases he : InfectionEvent.weight s.coarse.1 e = 0
  · cases w with
    | none =>
        exact absurd
          (infectionRevealRecordCheckpoint_eq_afterBatch_of_zero_none
            s k word e he)
          hdiff
    | some w =>
        simp [infectionRevealWitnessPMF, he]
  · cases w with
    | none =>
        exact infectionRevealWitnessPMF_none s e he
    | some w =>
        exact absurd
          (infectionRevealRecordCheckpoint_eq_afterBatch_of_some
            s k word e w he)
          hdiff

/-- The full record checkpoint law is the exact physical batch law pushed
through the stopped logical update. -/
theorem infectionRevealRecordPMF_map_checkpoint
    (n : ℕ) (h3 : 3 ≤ n)
    (s : InfectionRevealPhysicalState n)
    (k : ℕ) (word : List (Fin n)) :
    (infectionRevealRecordPMF n h3 s).map
        (InfectionRevealPrefixCheckpoint.afterRecord k word) =
      (infectionRevealBatchPMF n h3 s).map
        (InfectionRevealPrefixCheckpoint.afterBatch
          k s.inactive word) := by
  unfold infectionRevealRecordPMF infectionRevealBatchPMF
  rw [PMF.map_bind, PMF.map_bind]
  simp_rw [PMF.map_comp]
  congr 1
  funext e
  exact infectionRevealWitnessPMF_map_checkpoint
    s k word e

/-- State-specific physical batch transition on a live logical checkpoint. -/
noncomputable def infectionRevealPhysicalCheckpointLiveStep
    (n : ℕ) (h3 : 3 ≤ n) (k : ℕ)
    (s : InfectionRevealPhysicalState n)
    (word : List (Fin n)) :
    PMF (InfectionRevealPrefixCheckpoint n) :=
  (infectionRevealBatchPMF n h3 s).map
    (InfectionRevealPrefixCheckpoint.afterBatch
      k s.inactive word)

/-- The explicit logical time change: a physical batch advances the stopped
ordinary reveal chain by zero, one, or two steps. -/
noncomputable def infectionRevealPrefixTimeChangeLiveStep
    (n : ℕ) (h3 : 3 ≤ n) (k : ℕ)
    (s : InfectionRevealPhysicalState n)
    (word : List (Fin n)) :
    PMF (InfectionRevealPrefixCheckpoint n) :=
  (infectionRevealBatchSizePMF n
      s.coarse.1.active s.inactive.ids.card h3
      (infectionReveal_active_add_inactive s)).bind fun
    | .zero =>
        PMF.pure
          (InfectionRevealPrefixCheckpoint.live
            s.inactive word)
    | .one =>
        InfectionRevealPrefixCheckpoint.oneStep n k
          (.live s.inactive word)
    | .two =>
        iter (InfectionRevealPrefixCheckpoint.oneStep n k) 2
          (.live s.inactive word)

/-- With room for two inactive identities, the exact physical batch kernel is
the zero/one/two-step logical reveal time change. -/
theorem infectionRevealPhysicalCheckpointLiveStep_eq_timeChange
    (n : ℕ) (h3 : 3 ≤ n) (k : ℕ)
    (s : InfectionRevealPhysicalState n)
    (word : List (Fin n))
    (hword : ¬ k ≤ word.length)
    {m : ℕ} (hcard : m + 2 = s.inactive.ids.card) :
    infectionRevealPhysicalCheckpointLiveStep
        n h3 k s word =
      infectionRevealPrefixTimeChangeLiveStep
        n h3 k s word := by
  unfold infectionRevealPhysicalCheckpointLiveStep
    infectionRevealPrefixTimeChangeLiveStep
  rw [infectionRevealBatchPMF_eq_mixture]
  unfold infectionRevealBatchMixturePMF
  rw [PMF.map_bind]
  congr 1
  funext d
  cases d with
  | zero =>
      change
        (PMF.pure InfectionRevealBatch.none).map
            (InfectionRevealPrefixCheckpoint.afterBatch
              k s.inactive word) =
          PMF.pure
            (InfectionRevealPrefixCheckpoint.live
              s.inactive word)
      rw [PMF.pure_map]
      simp [InfectionRevealPrefixCheckpoint.afterBatch,
        hword]
  | one =>
      exact
        infectionRevealGivenBatchSize_one_map_checkpoint
          s word
            (infectionSequentialReveal_first_nonempty
              s.inactive hcard)
  | two =>
      exact
        infectionRevealGivenBatchSize_two_map_checkpoint
          s word hcard

/-- One physical quotient step projects to its exact state-specific batch
transition. -/
theorem infectionRevealFirstKQuotient_step_map_checkpoint_live
    (n : ℕ) (h3 : 3 ≤ n) (k : ℕ)
    (s : InfectionRevealPhysicalState n)
    (word : List (Fin n))
    (hword : ¬ k ≤ word.length) :
    (InfectionRevealFirstKQuotient.step n h3 k
        (.live s word)).map
          InfectionRevealPrefixCheckpoint.ofPhysical =
      infectionRevealPhysicalCheckpointLiveStep
        n h3 k s word := by
  unfold InfectionRevealFirstKQuotient.step
    infectionRevealPhysicalCheckpointLiveStep
  rw [PMF.map_comp]
  have hfun :
      (@InfectionRevealPrefixCheckpoint.ofPhysical n k) ∘
          (fun r : InfectionRevealRecord s =>
            InfectionRevealFirstKQuotient.afterRecord
              (k := k) word r) =
        InfectionRevealPrefixCheckpoint.afterRecord k word := by
    funext r
    by_cases hr :
        k ≤ (word ++ r.revealedIds).length
    · have hr' :
          k ≤ word.length + r.revealedIds.length := by
        simpa using hr
      simp [InfectionRevealPrefixCheckpoint.ofPhysical,
        InfectionRevealFirstKQuotient.afterRecord,
        InfectionRevealPrefixCheckpoint.afterRecord,
        hword, hr']
    · have hr' :
          ¬ k ≤ word.length + r.revealedIds.length := by
        simpa using hr
      simp [InfectionRevealPrefixCheckpoint.ofPhysical,
      InfectionRevealFirstKQuotient.afterRecord,
      InfectionRevealPrefixCheckpoint.afterRecord,
      hword, hr']
  rw [hfun]
  exact infectionRevealRecordPMF_map_checkpoint
    n h3 s k word

end
end Tri

#print axioms Tri.InfectionRevealRecord.after_inactive_eq_batch_remaining_of_some
#print axioms Tri.InfectionRevealRecord.after_inactive_eq_batch_remaining_of_zero_none
#print axioms Tri.infectionRevealRecordCheckpoint_eq_afterBatch_of_some
#print axioms Tri.infectionRevealRecordCheckpoint_eq_afterBatch_of_zero_none
#print axioms Tri.infectionRevealWitnessPMF_map_checkpoint
#print axioms Tri.infectionRevealRecordPMF_map_checkpoint
#print axioms Tri.infectionRevealPhysicalCheckpointLiveStep_eq_timeChange
#print axioms Tri.infectionRevealFirstKQuotient_step_map_checkpoint_live
