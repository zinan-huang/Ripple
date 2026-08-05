/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Basic
import Mathlib.Data.Nat.Log

/-!
# Finite state space for multi-species Tri

Population conservation and coordinate bounds are built into the state type.
The designated plurality species remains an explicit parameter; no argmax or
tie-breaking choice enters the public predicates.
-/

namespace Tri.Multi

/-- Species labels for an `m`-species protocol. -/
abbrev Species (m : ℕ) := Fin m

/-- An `m`-species population vector of total size exactly `n`. -/
def Config (m n : ℕ) :=
  {c : Species m → Fin (n + 1) // ∑ i, (c i : ℕ) = n}

noncomputable instance : DecidableEq (Config m n) := Classical.decEq _
noncomputable instance : Fintype (Config m n) := by
  unfold Config
  infer_instance

/-- Population of one species. -/
def count (c : Config m n) (i : Species m) : ℕ := c.1 i

@[simp] theorem sum_count (c : Config m n) :
    ∑ i, count c i = n :=
  c.2

/-- Total population outside the designated species `X`. -/
def zSum (c : Config m n) (X : Species m) : ℕ :=
  ∑ i ∈ Finset.univ.erase X, count c i

/-- The designated species beats every competitor by at least `g`. -/
def HasPairwiseGap
    (c : Config m n) (X : Species m) (g : ℕ) : Prop :=
  ∀ Y, Y ≠ X → count c Y + g ≤ count c X

/-- The designated species beats the aggregate minority population by `g`. -/
def HasAggregateGap
    (c : Config m n) (X : Species m) (g : ℕ) : Prop :=
  zSum c X + g ≤ count c X

/-- Consensus on a designated species. -/
def ConsensusOn (c : Config m n) (X : Species m) : Prop :=
  count c X = n

/-- The paper's square-root plurality-gap hypothesis, with an integer witness. -/
def HasInitialPluralityGap
    (c : Config m n) (X : Species m) (γ : ℕ) : Prop :=
  ∃ g : ℕ,
    0 < g ∧
    γ * n * Nat.log 2 n ≤ g ^ 2 ∧
    HasPairwiseGap c X g

/-- The designated count plus the aggregate minority count is the population. -/
theorem count_add_zSum (c : Config m n) (X : Species m) :
    count c X + zSum c X = n := by
  unfold zSum
  rw [add_comm, Finset.sum_erase_add _ _ (Finset.mem_univ X)]
  exact sum_count c

/-- An aggregate gap is exactly a valid binary-Tri gap after projection. -/
theorem aggregateGap_to_binaryGap
    {c : Config m n} {X : Species m} {g : ℕ}
    (h : HasAggregateGap c X g) :
    n + g ≤ 2 * count c X := by
  have htotal := count_add_zSum c X
  unfold HasAggregateGap at h
  omega

/-- A positive pairwise gap makes the designated plurality unique. -/
theorem pairwiseGap_unique
    {c : Config m n} {X : Species m} {g : ℕ}
    (hg : 0 < g) (h : HasPairwiseGap c X g) :
    ∀ Y, Y ≠ X → count c Y < count c X := by
  intro Y hYX
  have := h Y hYX
  omega

/-- Consensus is equivalent to every competing coordinate being zero. -/
theorem consensusOn_iff_other_zero
    (c : Config m n) (X : Species m) :
    ConsensusOn c X ↔ ∀ Y, Y ≠ X → count c Y = 0 := by
  constructor
  · intro hcons Y hYX
    have htotal := count_add_zSum c X
    have hz : zSum c X = 0 := by
      unfold ConsensusOn at hcons
      omega
    have hmem : Y ∈ Finset.univ.erase X := by
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      exact hYX
    have hle :
        count c Y ≤ ∑ i ∈ Finset.univ.erase X, count c i := by
      exact Finset.single_le_sum
        (fun i _ => Nat.zero_le (count c i)) hmem
    unfold zSum at hz
    omega
  · intro hzero
    unfold ConsensusOn
    have hz : zSum c X = 0 := by
      unfold zSum
      apply Finset.sum_eq_zero
      intro Y hY
      simp only [Finset.mem_erase] at hY
      exact hzero Y hY.1
    have htotal := count_add_zSum c X
    omega

/-- A feasible pairwise-gap threshold cannot exceed the designated
population.  The explicit `g ≤ n` hypothesis covers the one-species case,
where the pairwise condition is vacuous. -/
theorem pairwiseGap_le_count_of_le_population
    {c : Config m n} {X : Species m} {g : ℕ}
    (hgn : g ≤ n) (hgap : HasPairwiseGap c X g) :
    g ≤ count c X := by
  by_cases hcons : ConsensusOn c X
  · unfold ConsensusOn at hcons
    omega
  · have hother :
        ¬ ∀ Y, Y ≠ X → count c Y = 0 := by
      intro hzero
      exact hcons ((consensusOn_iff_other_zero c X).2 hzero)
    push Not at hother
    obtain ⟨Y, hYX, -⟩ := hother
    have hY := hgap Y hYX
    omega

end Tri.Multi

#print axioms Tri.Multi.count_add_zSum
#print axioms Tri.Multi.aggregateGap_to_binaryGap
#print axioms Tri.Multi.consensusOn_iff_other_zero
#print axioms Tri.Multi.pairwiseGap_le_count_of_le_population
