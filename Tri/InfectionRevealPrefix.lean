/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.InfectionReveal

/-!
# Prefixes of the infection reveal process

This file starts the without-replacement prefix construction by defining the
remaining inactive view after revealing one identity and proving its exact
label-count ledger.
-/

namespace Tri

namespace InfectionInactiveView

/-- Remove one revealed identity while retaining the immutable label map. -/
def erase {n : ℕ} (v : InfectionInactiveView n)
    (i : InfectionInactiveId v) : InfectionInactiveView n where
  ids := v.ids.erase i.1
  initialLabel := v.initialLabel

@[simp] theorem erase_ids {n : ℕ} (v : InfectionInactiveView n)
    (i : InfectionInactiveId v) :
    (v.erase i).ids = v.ids.erase i.1 := rfl

@[simp] theorem erase_initialLabel {n : ℕ} (v : InfectionInactiveView n)
    (i : InfectionInactiveId v) :
    (v.erase i).initialLabel = v.initialLabel := rfl

/-- Erasing a member decreases the remaining population by exactly one. -/
theorem erase_card_add_one {n : ℕ} (v : InfectionInactiveView n)
    (i : InfectionInactiveId v) :
    (v.erase i).ids.card + 1 = v.ids.card := by
  have hpos : 0 < v.ids.card :=
    Finset.card_pos.mpr ⟨i.1, i.2⟩
  rw [erase_ids, Finset.card_erase_of_mem i.2]
  omega

@[simp] theorem erase_xIds {n : ℕ} (v : InfectionInactiveView n)
    (i : InfectionInactiveId v) :
    (v.erase i).xIds = v.xIds.erase i.1 := by
  ext j
  simp [xIds, erase, and_assoc]

@[simp] theorem erase_yIds {n : ℕ} (v : InfectionInactiveView n)
    (i : InfectionInactiveId v) :
    (v.erase i).yIds = v.yIds.erase i.1 := by
  ext j
  simp [yIds, erase, and_assoc]

/-- The two immutable labels partition the remaining inactive identities. -/
theorem xIds_card_add_yIds_card {n : ℕ}
    (v : InfectionInactiveView n) :
    v.xIds.card + v.yIds.card = v.ids.card := by
  classical
  have hfilter :
      v.ids.filter (fun i => ¬ v.initialLabel i = .X) =
        v.ids.filter (fun i => v.initialLabel i = .Y) := by
    ext i
    cases hlabel : v.initialLabel i <;> simp [hlabel]
  unfold xIds yIds
  rw [← hfilter]
  exact Finset.card_filter_add_card_filter_not _

/-- Revealing an `X` removes one `X` and no `Y`. -/
theorem erase_counts_of_X {n a b : ℕ}
    (v : InfectionInactiveView n)
    (i : InfectionInactiveId v)
    (hlabel : v.initialLabel i.1 = .X)
    (hx : v.xIds.card = a + 1)
    (hy : v.yIds.card = b) :
    (v.erase i).xIds.card = a ∧
      (v.erase i).yIds.card = b := by
  have hiX : i.1 ∈ v.xIds := by
    simp [xIds, i.2, hlabel]
  have hiY : i.1 ∉ v.yIds := by
    simp [yIds, hlabel]
  constructor
  · rw [erase_xIds, Finset.card_erase_of_mem hiX, hx]
    omega
  · rw [erase_yIds, Finset.erase_eq_of_notMem hiY, hy]

/-- Revealing a `Y` removes one `Y` and no `X`. -/
theorem erase_counts_of_Y {n a b : ℕ}
    (v : InfectionInactiveView n)
    (i : InfectionInactiveId v)
    (hlabel : v.initialLabel i.1 = .Y)
    (hx : v.xIds.card = a)
    (hy : v.yIds.card = b + 1) :
    (v.erase i).xIds.card = a ∧
      (v.erase i).yIds.card = b := by
  have hiX : i.1 ∉ v.xIds := by
    simp [xIds, hlabel]
  have hiY : i.1 ∈ v.yIds := by
    simp [yIds, i.2, hlabel]
  constructor
  · rw [erase_xIds, Finset.erase_eq_of_notMem hiX, hx]
  · rw [erase_yIds, Finset.card_erase_of_mem hiY, hy]
    omega

end InfectionInactiveView

end Tri

#print axioms Tri.InfectionInactiveView.erase_ids
#print axioms Tri.InfectionInactiveView.erase_initialLabel
#print axioms Tri.InfectionInactiveView.erase_card_add_one
#print axioms Tri.InfectionInactiveView.erase_xIds
#print axioms Tri.InfectionInactiveView.erase_yIds
#print axioms Tri.InfectionInactiveView.xIds_card_add_yIds_card
#print axioms Tri.InfectionInactiveView.erase_counts_of_X
#print axioms Tri.InfectionInactiveView.erase_counts_of_Y
