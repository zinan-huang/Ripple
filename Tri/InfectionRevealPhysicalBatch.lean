/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.InfectionRevealPhysicalStep

/-!
# Ordered activation batches

Each refined physical record exposes the ordered list of zero, one, or two
identities activated by that raw interaction. The batch is duplicate-free,
lies in the source inactive view, is disjoint from the successor view, and
together with the successor view partitions the source identities.
-/

namespace Tri

/-- Ordered identities activated by a positive semantic event. -/
def infectionRevealPositiveIds
    {n : ℕ} {s : InfectionRevealPhysicalState n}
    (e : InfectionEvent) (w : InfectionRevealWitness s e) :
    List (Fin n) :=
  match e with
  | .activeXXX | .activeXXY | .activeXYY | .activeYYY |
      .inactiveOnly => []
  | .activateOneX => [(infectionInactiveXToId w).1]
  | .activateOneY => [(infectionInactiveYToId w).1]
  | .activateTwoXX =>
      let p := infectionInactiveXXToOrdered w
      [p.1.1.1, p.1.2.1]
  | .activateTwoXY =>
      let p := infectionInactiveXYToOrdered w
      [p.1.1.1, p.1.2.1]
  | .activateTwoYY =>
      let p := infectionInactiveYYToOrdered w
      [p.1.1.1, p.1.2.1]

/-- A positive batch has the event's activation increment as its length. -/
theorem infectionRevealPositiveIds_length
    {n : ℕ} {s : InfectionRevealPhysicalState n}
    (e : InfectionEvent) (w : InfectionRevealWitness s e) :
    (infectionRevealPositiveIds e w).length = e.activationInc := by
  cases e <;>
    rfl

/-- The auxiliary order never repeats an identity. -/
theorem infectionRevealPositiveIds_nodup
    {n : ℕ} {s : InfectionRevealPhysicalState n}
    (e : InfectionEvent) (w : InfectionRevealWitness s e) :
    (infectionRevealPositiveIds e w).Nodup := by
  cases e with
  | activeXXX | activeXXY | activeXYY | activeYYY | inactiveOnly =>
      simp [infectionRevealPositiveIds]
  | activateOneX | activateOneY =>
      simp [infectionRevealPositiveIds]
  | activateTwoXX =>
      have hp := (infectionInactiveXXToOrdered w).2
      simp [infectionRevealPositiveIds, hp]
  | activateTwoXY =>
      have hp := (infectionInactiveXYToOrdered w).2
      simp [infectionRevealPositiveIds, hp]
  | activateTwoYY =>
      have hp := (infectionInactiveYYToOrdered w).2
      simp [infectionRevealPositiveIds, hp]

/-- Every positive-batch identity was inactive before the event. -/
theorem infectionRevealPositiveIds_mem
    {n : ℕ} {s : InfectionRevealPhysicalState n}
    (e : InfectionEvent) (w : InfectionRevealWitness s e) :
    ∀ i ∈ infectionRevealPositiveIds e w, i ∈ s.inactive.ids := by
  cases e with
  | activeXXX | activeXXY | activeXYY | activeYYY | inactiveOnly =>
      simp [infectionRevealPositiveIds]
  | activateOneX =>
      intro i hi
      simp only [infectionRevealPositiveIds, List.mem_singleton] at hi
      subst i
      exact (Finset.mem_filter.mp w.2).1
  | activateOneY =>
      intro i hi
      simp only [infectionRevealPositiveIds, List.mem_singleton] at hi
      subst i
      exact (Finset.mem_filter.mp w.2).1
  | activateTwoXX =>
      intro i hi
      simp only [infectionRevealPositiveIds, List.mem_cons,
        List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · exact (Finset.mem_filter.mp w.1.1.2).1
      · exact (Finset.mem_filter.mp w.1.2.2).1
  | activateTwoXY =>
      cases w with
      | inl w =>
          intro i hi
          simp only [infectionRevealPositiveIds, List.mem_cons,
            List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl
          · exact (Finset.mem_filter.mp w.1.2).1
          · exact (Finset.mem_filter.mp w.2.2).1
      | inr w =>
          intro i hi
          simp only [infectionRevealPositiveIds, List.mem_cons,
            List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl
          · exact (Finset.mem_filter.mp w.1.2).1
          · exact (Finset.mem_filter.mp w.2.2).1
  | activateTwoYY =>
      intro i hi
      simp only [infectionRevealPositiveIds, List.mem_cons,
        List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · exact (Finset.mem_filter.mp w.1.1.2).1
      · exact (Finset.mem_filter.mp w.1.2.2).1

/-- A positive update preserves the immutable label map. -/
theorem infectionRevealPhysicalAfterPositive_initialLabel
    {n : ℕ} (s : InfectionRevealPhysicalState n)
    (e : InfectionEvent) (w : InfectionRevealWitness s e)
    (he : InfectionEvent.weight s.coarse.1 e ≠ 0) :
    (infectionRevealPhysicalAfterPositive s e w he).inactive.initialLabel =
      s.inactive.initialLabel := by
  cases e <;>
    rfl

/-- A positive update removes exactly its ordered batch as a set. -/
theorem infectionRevealPhysicalAfterPositive_ids
    {n : ℕ} (s : InfectionRevealPhysicalState n)
    (e : InfectionEvent) (w : InfectionRevealWitness s e)
    (he : InfectionEvent.weight s.coarse.1 e ≠ 0) :
    (infectionRevealPhysicalAfterPositive s e w he).inactive.ids =
      s.inactive.ids \ (infectionRevealPositiveIds e w).toFinset := by
  cases e with
  | activeXXX | activeXXY | activeXYY | activeYYY | inactiveOnly =>
      simp [infectionRevealPhysicalAfterPositive,
        infectionRevealPhysicalPreserve, infectionRevealPositiveIds]
  | activateOneX =>
      simp only [infectionRevealPhysicalAfterPositive,
        infectionRevealPhysicalActivateOneX, infectionRevealPositiveIds,
        List.toFinset_cons, List.toFinset_nil]
      exact (Finset.sdiff_singleton_eq_erase _ _).symm
  | activateOneY =>
      simp only [infectionRevealPhysicalAfterPositive,
        infectionRevealPhysicalActivateOneY, infectionRevealPositiveIds,
        List.toFinset_cons, List.toFinset_nil]
      exact (Finset.sdiff_singleton_eq_erase _ _).symm
  | activateTwoXX =>
      simp only [infectionRevealPhysicalAfterPositive,
        infectionRevealPhysicalActivateTwoXX, infectionRevealPositiveIds,
        infectionRevealEraseTwo, List.toFinset_cons,
        List.toFinset_nil]
      ext i
      simp [infectionRevealTwoSecondAfterFirst,
        and_comm, and_assoc]
  | activateTwoXY =>
      simp only [infectionRevealPhysicalAfterPositive,
        infectionRevealPhysicalActivateTwoXY, infectionRevealPositiveIds,
        infectionRevealEraseTwo, List.toFinset_cons,
        List.toFinset_nil]
      ext i
      simp [infectionRevealTwoSecondAfterFirst,
        and_comm, and_assoc]
  | activateTwoYY =>
      simp only [infectionRevealPhysicalAfterPositive,
        infectionRevealPhysicalActivateTwoYY, infectionRevealPositiveIds,
        infectionRevealEraseTwo, List.toFinset_cons,
        List.toFinset_nil]
      ext i
      simp [infectionRevealTwoSecondAfterFirst,
        and_comm, and_assoc]

/-- Ordered zero-, one-, or two-identity batch carried by a total record. -/
noncomputable def InfectionRevealRecord.revealedIds
    {n : ℕ} {s : InfectionRevealPhysicalState n}
    (r : InfectionRevealRecord s) : List (Fin n) :=
  if he : InfectionEvent.weight s.coarse.1 r.event = 0 then
    []
  else
    infectionRevealPositiveIds r.event (r.effectiveWitness he)

/-- The total batch length is the realized activation increment. -/
theorem InfectionRevealRecord.revealedIds_length
    {n : ℕ} {s : InfectionRevealPhysicalState n}
    (r : InfectionRevealRecord s) :
    r.revealedIds.length =
      r.event.realizedActivationInc s.coarse.1 := by
  unfold InfectionRevealRecord.revealedIds
  by_cases he : InfectionEvent.weight s.coarse.1 r.event = 0
  · rw [dif_pos he]
    simp [InfectionEvent.realizedActivationInc, he]
  · rw [dif_neg he]
    simp [InfectionEvent.realizedActivationInc, he]
    exact infectionRevealPositiveIds_length
      r.event (r.effectiveWitness he)

/-- Every total record batch is duplicate-free. -/
theorem InfectionRevealRecord.revealedIds_nodup
    {n : ℕ} {s : InfectionRevealPhysicalState n}
    (r : InfectionRevealRecord s) :
    r.revealedIds.Nodup := by
  unfold InfectionRevealRecord.revealedIds
  split_ifs with he
  · simp
  · exact infectionRevealPositiveIds_nodup
      r.event (r.effectiveWitness he)

/-- Every total record batch lies in the source inactive view. -/
theorem InfectionRevealRecord.revealedIds_mem
    {n : ℕ} {s : InfectionRevealPhysicalState n}
    (r : InfectionRevealRecord s) :
    ∀ i ∈ r.revealedIds, i ∈ s.inactive.ids := by
  unfold InfectionRevealRecord.revealedIds
  split_ifs with he
  · simp
  · exact infectionRevealPositiveIds_mem
      r.event (r.effectiveWitness he)

/-- A total record update preserves the immutable label map. -/
theorem InfectionRevealRecord.after_initialLabel
    {n : ℕ} {s : InfectionRevealPhysicalState n}
    (r : InfectionRevealRecord s) :
    r.after.inactive.initialLabel =
      s.inactive.initialLabel := by
  unfold InfectionRevealRecord.after
  by_cases he : InfectionEvent.weight s.coarse.1 r.event = 0
  · rw [dif_pos he]
  · rw [dif_neg he]
    exact infectionRevealPhysicalAfterPositive_initialLabel
      s r.event (r.effectiveWitness he) he

/-- The successor identities are exactly the source minus the batch. -/
theorem InfectionRevealRecord.after_ids
    {n : ℕ} {s : InfectionRevealPhysicalState n}
    (r : InfectionRevealRecord s) :
    r.after.inactive.ids =
      s.inactive.ids \ r.revealedIds.toFinset := by
  unfold InfectionRevealRecord.after
    InfectionRevealRecord.revealedIds
  by_cases he : InfectionEvent.weight s.coarse.1 r.event = 0
  · rw [dif_pos he, dif_pos he]
    simp
  · rw [dif_neg he, dif_neg he]
    exact infectionRevealPhysicalAfterPositive_ids
      s r.event (r.effectiveWitness he) he

/-- Set form of batch membership in the source view. -/
theorem InfectionRevealRecord.revealedIds_toFinset_subset
    {n : ℕ} {s : InfectionRevealPhysicalState n}
    (r : InfectionRevealRecord s) :
    r.revealedIds.toFinset ⊆ s.inactive.ids := by
  intro i hi
  exact InfectionRevealRecord.revealedIds_mem r i (List.mem_toFinset.mp hi)

/-- Activated and still-inactive identities are disjoint. -/
theorem InfectionRevealRecord.revealedIds_disjoint_after
    {n : ℕ} {s : InfectionRevealPhysicalState n}
    (r : InfectionRevealRecord s) :
    Disjoint r.revealedIds.toFinset r.after.inactive.ids := by
  rw [InfectionRevealRecord.after_ids]
  exact Finset.disjoint_sdiff

/-- Activated and still-inactive identities partition the source view. -/
theorem InfectionRevealRecord.revealedIds_union_after
    {n : ℕ} {s : InfectionRevealPhysicalState n}
    (r : InfectionRevealRecord s) :
    r.revealedIds.toFinset ∪ r.after.inactive.ids =
      s.inactive.ids := by
  rw [InfectionRevealRecord.after_ids]
  exact Finset.union_sdiff_of_subset
    (InfectionRevealRecord.revealedIds_toFinset_subset r)

end Tri

#print axioms Tri.InfectionRevealRecord.revealedIds_length
#print axioms Tri.InfectionRevealRecord.revealedIds_nodup
#print axioms Tri.InfectionRevealRecord.revealedIds_mem
#print axioms Tri.InfectionRevealRecord.after_initialLabel
#print axioms Tri.InfectionRevealRecord.after_ids
#print axioms Tri.InfectionRevealRecord.revealedIds_toFinset_subset
#print axioms Tri.InfectionRevealRecord.revealedIds_disjoint_after
#print axioms Tri.InfectionRevealRecord.revealedIds_union_after
#print axioms Tri.infectionRevealPositiveIds_length
#print axioms Tri.infectionRevealPositiveIds_nodup
#print axioms Tri.infectionRevealPositiveIds_mem
#print axioms Tri.infectionRevealPhysicalAfterPositive_initialLabel
#print axioms Tri.infectionRevealPhysicalAfterPositive_ids
