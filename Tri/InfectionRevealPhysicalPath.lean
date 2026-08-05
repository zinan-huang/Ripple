/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.InfectionRevealPhysicalBatch

/-!
# Ordered physical activation paths

The path state anchors the initial inactive view and appends every ordered
activation batch. Its invariants identify the accumulated word with the
identities removed from the current view and relate word length to the
physical active count. Once a first-`k` prefix exists, later raw interactions
cannot change it.
-/

namespace Tri

/-- A physical state anchored at its initial inactive view, together with the
ordered identities activated since that anchor. -/
structure InfectionRevealPhysicalPathState (n : ℕ) where
  anchor : InfectionRevealPhysicalState n
  current : InfectionRevealPhysicalState n
  revealed : List (Fin n)
  hnodup : revealed.Nodup
  hpartition :
    revealed.toFinset ∪ current.inactive.ids =
      anchor.inactive.ids
  hdisjoint :
    Disjoint revealed.toFinset current.inactive.ids
  hinitialLabel :
    current.inactive.initialLabel =
      anchor.inactive.initialLabel
  hactiveLedger :
    anchor.coarse.1.active + revealed.length =
      current.coarse.1.active

/-- Fresh path state with an empty revealed word. -/
def infectionRevealPhysicalPathInitial
    {n : ℕ} (s : InfectionRevealPhysicalState n) :
    InfectionRevealPhysicalPathState n where
  anchor := s
  current := s
  revealed := []
  hnodup := by simp
  hpartition := by simp
  hdisjoint := by simp
  hinitialLabel := rfl
  hactiveLedger := by simp

/-- Append one raw interaction's activation batch and update the current
physical state. -/
noncomputable def InfectionRevealPhysicalPathState.afterRecord
    {n : ℕ} (q : InfectionRevealPhysicalPathState n)
    (r : InfectionRevealRecord q.current) :
    InfectionRevealPhysicalPathState n where
  anchor := q.anchor
  current := r.after
  revealed := q.revealed ++ r.revealedIds
  hnodup := by
    rw [List.nodup_append]
    refine ⟨q.hnodup, r.revealedIds_nodup, ?_⟩
    intro a ha b hb hab
    subst b
    exact (Finset.disjoint_left.mp q.hdisjoint)
      (List.mem_toFinset.mpr ha)
      (r.revealedIds_mem a hb)
  hpartition := by
    rw [List.toFinset_append, Finset.union_assoc,
      r.revealedIds_union_after, q.hpartition]
  hdisjoint := by
    rw [List.toFinset_append, Finset.disjoint_union_left]
    refine ⟨?_, r.revealedIds_disjoint_after⟩
    have hsub : r.after.inactive.ids ⊆ q.current.inactive.ids := by
      rw [r.after_ids]
      exact Finset.sdiff_subset
    exact q.hdisjoint.mono_right hsub
  hinitialLabel :=
    r.after_initialLabel.trans q.hinitialLabel
  hactiveLedger := by
    have hforget := r.after_forget
    change r.after.coarse =
      InfectionEvent.nextState q.current.coarse r.event at hforget
    have hstep :=
      InfectionEvent.nextState_active_eq_add_realizedActivationInc
        q.current.coarse r.event
    rw [← hforget] at hstep
    have hledger := q.hactiveLedger
    rw [List.length_append, r.revealedIds_length]
    omega

/-- The durable first `k` activated identities. -/
def InfectionRevealPhysicalPathState.firstKIds
    {n : ℕ} (q : InfectionRevealPhysicalPathState n) (k : ℕ) :
    List (Fin n) :=
  q.revealed.take k

/-- Immutable labels of the durable first `k` identities. -/
def InfectionRevealPhysicalPathState.firstKLabels
    {n : ℕ} (q : InfectionRevealPhysicalPathState n) (k : ℕ) :
    List InfectionLabel :=
  (q.firstKIds k).map q.anchor.inactive.initialLabel

/-- Once present, the first-`k` identity prefix survives every later record. -/
theorem InfectionRevealPhysicalPathState.firstKIds_afterRecord
    {n k : ℕ} (q : InfectionRevealPhysicalPathState n)
    (r : InfectionRevealRecord q.current)
    (hk : k ≤ q.revealed.length) :
    (q.afterRecord r).firstKIds k =
      q.firstKIds k := by
  exact List.take_append_of_le_length hk

/-- Once present, the first-`k` immutable-label prefix is durable. -/
theorem InfectionRevealPhysicalPathState.firstKLabels_afterRecord
    {n k : ℕ} (q : InfectionRevealPhysicalPathState n)
    (r : InfectionRevealRecord q.current)
    (hk : k ≤ q.revealed.length) :
    (q.afterRecord r).firstKLabels k =
      q.firstKLabels k := by
  change
    List.map q.anchor.inactive.initialLabel
        ((q.afterRecord r).firstKIds k) =
      List.map q.anchor.inactive.initialLabel
        (q.firstKIds k)
  rw [InfectionRevealPhysicalPathState.firstKIds_afterRecord q r hk]

/-- One identity-refined raw interaction on ordered path states. -/
noncomputable def infectionRevealPhysicalPathStep
    (n : ℕ) (h3 : 3 ≤ n) :
    InfectionRevealPhysicalPathState n → PMF (InfectionRevealPhysicalPathState n) :=
  fun q =>
    (infectionRevealRecordPMF n h3 q.current).map
      q.afterRecord

/-- Forget the anchor and revealed word. -/
def infectionRevealPhysicalPathCurrent
    {n : ℕ} (q : InfectionRevealPhysicalPathState n) :
    InfectionRevealPhysicalState n :=
  q.current

/-- The path kernel projects exactly to the identity-refined physical step. -/
theorem infectionRevealPhysicalPathStep_map_current
    (n : ℕ) (h3 : 3 ≤ n) (q : InfectionRevealPhysicalPathState n) :
    (infectionRevealPhysicalPathStep n h3 q).map infectionRevealPhysicalPathCurrent =
      infectionRevealPhysicalStep n h3 q.current := by
  unfold infectionRevealPhysicalPathStep infectionRevealPhysicalStep
  rw [PMF.map_comp]
  rfl

/-- Forget all identity and path information. -/
def infectionRevealPhysicalPathForget
    {n : ℕ} (q : InfectionRevealPhysicalPathState n) :
    InfectionState n :=
  q.current.coarse

/-- The path kernel projects exactly to the original infection kernel. -/
theorem infectionRevealPhysicalPathStep_map_forget
    (n : ℕ) (h3 : 3 ≤ n) (q : InfectionRevealPhysicalPathState n) :
    (infectionRevealPhysicalPathStep n h3 q).map infectionRevealPhysicalPathForget =
      infectionStateStep n h3 q.current.coarse := by
  calc
    (infectionRevealPhysicalPathStep n h3 q).map infectionRevealPhysicalPathForget =
        ((infectionRevealPhysicalPathStep n h3 q).map infectionRevealPhysicalPathCurrent).map
          infectionRevealPhysicalForget := by
            rw [PMF.map_comp]
            rfl
    _ = (infectionRevealPhysicalStep n h3 q.current).map
          infectionRevealPhysicalForget := by
            rw [infectionRevealPhysicalPathStep_map_current]
    _ = infectionStateStep n h3 q.current.coarse :=
          infectionRevealPhysicalStep_map_forget n h3 q.current

/-- Kernel-level form of the exact coarse path projection. -/
theorem infectionRevealPhysicalPathStep_intertwines_forget
    (n : ℕ) (h3 : 3 ≤ n) :
    Intertwines (@infectionRevealPhysicalPathForget n)
      (infectionRevealPhysicalPathStep n h3) (infectionStateStep n h3) :=
  infectionRevealPhysicalPathStep_map_forget n h3

/-- The exact coarse path projection persists at every raw horizon. -/
theorem infectionRevealPhysicalPathStep_iter_map_forget
    (n : ℕ) (h3 : 3 ≤ n) (T : ℕ)
    (q : InfectionRevealPhysicalPathState n) :
    (iter (infectionRevealPhysicalPathStep n h3) T q).map infectionRevealPhysicalPathForget =
      iter (infectionStateStep n h3) T
        (infectionRevealPhysicalPathForget q) :=
  iter_map_of_intertwines
    (infectionRevealPhysicalPathStep_intertwines_forget n h3) T q

/-- The accumulated physical reveal word and the current inactive view exactly
partition the anchored inactive population. -/
theorem InfectionRevealPhysicalPathState.revealed_length_add_current
    {n : ℕ} (q : InfectionRevealPhysicalPathState n) :
    q.revealed.length + q.current.inactive.ids.card =
      q.anchor.inactive.ids.card := by
  rw [← List.toFinset_card_of_nodup q.hnodup]
  rw [← Finset.card_union_of_disjoint q.hdisjoint,
    q.hpartition]

end Tri

#print axioms Tri.InfectionRevealPhysicalPathState.firstKIds_afterRecord
#print axioms Tri.InfectionRevealPhysicalPathState.firstKLabels_afterRecord
#print axioms Tri.infectionRevealPhysicalPathStep_map_current
#print axioms Tri.infectionRevealPhysicalPathStep_map_forget
#print axioms Tri.infectionRevealPhysicalPathStep_intertwines_forget
#print axioms Tri.infectionRevealPhysicalPathStep_iter_map_forget
#print axioms Tri.InfectionRevealPhysicalPathState.revealed_length_add_current
