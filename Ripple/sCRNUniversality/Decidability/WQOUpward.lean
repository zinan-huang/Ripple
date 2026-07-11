/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Mathlib.Order.WellQuasiOrder
import Mathlib.Order.UpperLower.Basic
import Mathlib.Order.WellFounded

/-!
# WQO ascending-chain stabilization for upward-closed sets

The key termination theorem for backward coverability:
in a WQO, every strictly ascending chain of upward-closed sets is finite.

## Main definitions

* `upClosure`: the upward closure of a finite set of elements

## Main results

* `upClosure_isUpperSet`: the upward closure is an upper set
* `no_strictly_ascending_upperSets`: no infinite strictly ascending chain of upper sets in a WQO
* `wellFounded_strictAscendingUpperSets`: well-foundedness of the strict ascending relation on
  upper sets
* `wellFounded_finset_upClosure`: well-foundedness on `Finset α` via `upClosure`
-/

namespace Ripple.sCRNUniversality.Decidability

variable {α : Type*}

/-- The upward closure of a finite set: all elements above some element of `B`. -/
def upClosure [LE α] (B : Finset α) : Set α :=
  {x | ∃ b ∈ B, b ≤ x}

theorem upClosure_isUpperSet [Preorder α] (B : Finset α) : IsUpperSet (upClosure B) := by
  intro a b hab ⟨c, hcB, hca⟩
  exact ⟨c, hcB, le_trans hca hab⟩

theorem upClosure_mono [Preorder α] {A B : Finset α} (h : ↑A ⊆ ↑B) :
    upClosure A ⊆ upClosure B := by
  intro x ⟨a, haA, hax⟩
  exact ⟨a, h haA, hax⟩

/-- The main theorem: in a WQO, there is no infinite strictly ascending chain of upper sets.

Given `U : ℕ → Set α` where each `U n` is an upper set, the chain is monotone, and each
`U n ⊊ U (n + 1)`, we derive a contradiction by constructing a bad sequence for the WQO. -/
theorem no_strictly_ascending_upperSets [Preorder α] [WellQuasiOrderedLE α]
    (U : ℕ → Set α) (hUpper : ∀ n, IsUpperSet (U n))
    (hMono : Monotone U) (hStrict : ∀ n, U n ⊂ U (n + 1)) : False := by
  -- For each n, pick a witness x_n ∈ U(n+1) \ U(n)
  have hWitness : ∀ n, ∃ x, x ∈ U (n + 1) ∧ x ∉ U n := by
    intro n
    obtain ⟨x, hx_in, hx_not⟩ := Set.exists_of_ssubset (hStrict n)
    exact ⟨x, hx_in, hx_not⟩
  choose x hx using hWitness
  -- x is a bad sequence: for i < j, ¬(x i ≤ x j)
  have hBad : ∀ i j, i < j → ¬(x i ≤ x j) := by
    intro i j hij hle
    -- x_i ∈ U(i+1) and i+1 ≤ j, so x_i ∈ U(j) by monotonicity
    have hxi_in : x i ∈ U j := hMono (by omega) (hx i).1
    -- U(j) is upward-closed, x_i ∈ U(j), x_i ≤ x_j, so x_j ∈ U(j)
    have hxj_in : x j ∈ U j := hUpper j hle hxi_in
    -- But x_j ∉ U(j) by construction
    exact (hx j).2 hxj_in
  -- Apply WQO to get m < n with x m ≤ x n — contradiction
  obtain ⟨m, n, hmn, hle⟩ := wellQuasiOrdered_le x
  exact hBad m n hmn hle

/-- Well-foundedness of the strict ascending relation on upper sets in a WQO.

The relation orders by strict superset (`V ⊃ U` means `U ⊂ V`), so that
larger sets are "smaller" in the well-founded sense. The backward coverability
saturation loop grows the upward-closed set at each step, consuming well-founded
fuel. -/
theorem wellFounded_strictAscendingUpperSets [Preorder α] [WellQuasiOrderedLE α] :
    WellFounded (fun (U V : {s : Set α // IsUpperSet s}) => V.1 ⊂ U.1) := by
  rw [wellFounded_iff_isEmpty_descending_chain]
  -- A descending chain f in our relation satisfies:
  -- ∀ n, (f n).1 ⊂ (f (n+1)).1  — an ascending chain of upper sets
  exact ⟨fun ⟨f, hf⟩ =>
    no_strictly_ascending_upperSets
      (fun n => (f n).1) (fun n => (f n).2)
      (fun a b hab => by
        induction hab with
        | refl => exact le_refl _
        | step hab ih => exact le_trans ih (hf _).1)
      hf⟩

/-- Well-foundedness of the strict superset relation on `Finset α` measured via `upClosure`.

This is the relation used for termination of the backward coverability saturation loop:
when we add a new basis element and the upward closure strictly grows, we are making
progress in a well-founded order. -/
theorem wellFounded_finset_upClosure [Preorder α] [WellQuasiOrderedLE α] :
    WellFounded (fun B' B : Finset α => upClosure B ⊂ upClosure B') := by
  have h := InvImage.wf (fun B : Finset α => ⟨upClosure B, upClosure_isUpperSet B⟩)
    wellFounded_strictAscendingUpperSets
  exact h

end Ripple.sCRNUniversality.Decidability
