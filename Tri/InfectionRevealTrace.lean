/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.InfectionRevealPhysicalFirstKTimeChange
import Tri.InfectionRevealUrn

/-!
# Anchored one-at-a-time reveal traces

The trace records the chronological uniform reveal word and the remaining
inactive view.  Its exact partition and label ledgers turn a bad revealed
prefix into an event on the remaining-count urn.
-/

namespace Tri

noncomputable section

/-- A one-at-a-time inactive reveal trace anchored at its initial view. -/
structure InfectionRevealTraceState (n : ℕ) where
  anchor : InfectionInactiveView n
  current : InfectionInactiveView n
  revealed : List (Fin n)
  hnodup : revealed.Nodup
  hpartition :
    revealed.toFinset ∪ current.ids = anchor.ids
  hdisjoint :
    Disjoint revealed.toFinset current.ids
  hinitialLabel :
    current.initialLabel = anchor.initialLabel

/-- Fresh reveal trace. -/
def infectionRevealTraceInitial
    {n : ℕ} (v : InfectionInactiveView n) :
    InfectionRevealTraceState n where
  anchor := v
  current := v
  revealed := []
  hnodup := by simp
  hpartition := by simp
  hdisjoint := by simp
  hinitialLabel := rfl

/-- Append one inactive identity and erase it from the remaining view. -/
def InfectionRevealTraceState.afterOne
    {n : ℕ} (q : InfectionRevealTraceState n)
    (i : InfectionInactiveId q.current) :
    InfectionRevealTraceState n where
  anchor := q.anchor
  current := q.current.erase i
  revealed := q.revealed ++ [i.1]
  hnodup := by
    rw [List.nodup_append]
    refine ⟨q.hnodup, by simp, ?_⟩
    intro a ha b hb hab
    simp only [List.mem_singleton] at hb
    subst b
    subst a
    exact (Finset.disjoint_left.mp q.hdisjoint)
      (List.mem_toFinset.mpr ha) i.2
  hpartition := by
    rw [List.toFinset_append]
    simp only [List.toFinset_cons, List.toFinset_nil]
    rw [InfectionInactiveView.erase_ids,
      Finset.union_assoc]
    change
      q.revealed.toFinset ∪
          ({i.1} ∪ q.current.ids.erase i.1) =
        q.anchor.ids
    rw [
      Finset.singleton_union,
      Finset.insert_erase i.2,
      q.hpartition]
  hdisjoint := by
    rw [List.toFinset_append,
      Finset.disjoint_union_left]
    constructor
    · exact q.hdisjoint.mono_right
        (Finset.erase_subset _ _)
    · simp [InfectionInactiveView.erase_ids]
  hinitialLabel :=
    (q.current.erase_initialLabel i).trans
      q.hinitialLabel

/-- Uniformly reveal and append one inactive identity; the empty view is
absorbing. -/
noncomputable def infectionRevealTraceStep
    {n : ℕ} :
    InfectionRevealTraceState n →
      PMF (InfectionRevealTraceState n)
  | q =>
      if h : 0 < q.current.ids.card then
        (infectionRevealOnePMF q.current
          (infectionRevealOne_nonempty_of_card_pos
            q.current h)).map q.afterOne
      else
        PMF.pure q

/-- Forget the chronological word. -/
def infectionRevealTraceCurrent
    {n : ℕ} (q : InfectionRevealTraceState n) :
    InfectionInactiveView n :=
  q.current

/-- The trace projects exactly to the ordinary identity reveal kernel. -/
theorem infectionRevealTraceStep_map_current
    {n : ℕ} (q : InfectionRevealTraceState n) :
    (infectionRevealTraceStep q).map
        infectionRevealTraceCurrent =
      infectionRevealKernel q.current := by
  unfold infectionRevealTraceStep infectionRevealKernel
  by_cases h : 0 < q.current.ids.card
  · rw [dif_pos h, dif_pos h, PMF.map_comp]
    rfl
  · rw [dif_neg h, dif_neg h, PMF.pure_map]
    rfl

/-- Remaining immutable label counts of a trace. -/
def infectionRevealTraceCounts
    {n : ℕ} (q : InfectionRevealTraceState n) :
    ℕ × ℕ :=
  infectionInactiveCounts q.current

/-- The anchored trace projects exactly to the count urn. -/
theorem infectionRevealTraceStep_intertwines_urnChain
    (n : ℕ) :
    Intertwines (@infectionRevealTraceCounts n)
      (@infectionRevealTraceStep n) urnChain := by
  intro q
  calc
    (infectionRevealTraceStep q).map
        infectionRevealTraceCounts =
      ((infectionRevealTraceStep q).map
        infectionRevealTraceCurrent).map
          infectionInactiveCounts := by
            rw [PMF.map_comp]
            rfl
    _ = (infectionRevealKernel q.current).map
          infectionInactiveCounts := by
            rw [infectionRevealTraceStep_map_current]
    _ = urnChain (infectionInactiveCounts q.current) :=
      infectionRevealKernel_intertwines_urnChain n q.current

/-- Exact count-urn endpoint law after every number of ordinary reveals. -/
theorem infectionRevealTraceStep_iter_map_counts
    (n T : ℕ) (q : InfectionRevealTraceState n) :
    (iter (@infectionRevealTraceStep n) T q).map
        infectionRevealTraceCounts =
      iter urnChain T (infectionRevealTraceCounts q) :=
  iter_map_of_intertwines
    (infectionRevealTraceStep_intertwines_urnChain n) T q

/-- The one-at-a-time trace has completed its first `k` reveals. -/
def InfectionRevealTraceReached
    {n : ℕ} (k : ℕ)
    (q : InfectionRevealTraceState n) : Prop :=
  k ≤ q.revealed.length

noncomputable instance infectionRevealTraceReachedDecidable
    (n k : ℕ) :
    DecidablePred (@InfectionRevealTraceReached n k) :=
  fun _ => Classical.dec _

/-- One-at-a-time trace frozen at its first `k` word. -/
noncomputable def infectionRevealTraceFirstKStep
    {n : ℕ} (k : ℕ) :
    InfectionRevealTraceState n →
      PMF (InfectionRevealTraceState n) :=
  freeze (InfectionRevealTraceReached k)
    infectionRevealTraceStep

/-- Project a trace to the logical first-prefix checkpoint. -/
def InfectionRevealPrefixCheckpoint.ofTrace
    {n : ℕ} (k : ℕ)
    (q : InfectionRevealTraceState n) :
    InfectionRevealPrefixCheckpoint n :=
  if k ≤ q.revealed.length then
    .done (q.revealed.take k)
  else
    .live q.current q.revealed

/-- The first-`k` trace projects exactly to the stopped ordinary reveal
checkpoint kernel. -/
theorem infectionRevealTraceFirstKStep_map_checkpoint
    {n : ℕ} (k : ℕ)
    (q : InfectionRevealTraceState n) :
    (infectionRevealTraceFirstKStep k q).map
        (InfectionRevealPrefixCheckpoint.ofTrace k) =
      InfectionRevealPrefixCheckpoint.oneStep n k
        (InfectionRevealPrefixCheckpoint.ofTrace k q) := by
  by_cases hk : k ≤ q.revealed.length
  · have hmem : InfectionRevealTraceReached k q := hk
    rw [show infectionRevealTraceFirstKStep k q =
        PMF.pure q by
          unfold infectionRevealTraceFirstKStep
          rw [freeze_of_mem q hmem],
      PMF.pure_map]
    simp [InfectionRevealPrefixCheckpoint.ofTrace,
      InfectionRevealPrefixCheckpoint.oneStep, hk]
  · have hnot : ¬ InfectionRevealTraceReached k q := hk
    unfold infectionRevealTraceFirstKStep
    rw [freeze_of_not_mem q hnot]
    simp only [InfectionRevealPrefixCheckpoint.ofTrace, hk,
      ↓reduceIte, InfectionRevealPrefixCheckpoint.oneStep]
    by_cases hcard : 0 < q.current.ids.card
    · unfold infectionRevealTraceStep
      rw [dif_pos hcard, dif_pos hcard, PMF.map_comp]
      congr 1
    · unfold infectionRevealTraceStep
      rw [dif_neg hcard, dif_neg hcard, PMF.pure_map]
      simp [InfectionRevealPrefixCheckpoint.ofTrace, hk]

/-- Kernel-level first-prefix trace quotient. -/
theorem infectionRevealTraceFirstKStep_intertwines_checkpoint
    (n k : ℕ) :
    Intertwines
      (InfectionRevealPrefixCheckpoint.ofTrace k)
      (@infectionRevealTraceFirstKStep n k)
      (InfectionRevealPrefixCheckpoint.oneStep n k) :=
  infectionRevealTraceFirstKStep_map_checkpoint k

/-- The trace and stopped ordinary reveal checkpoint have the same law at
every reveal horizon. -/
theorem infectionRevealTraceFirstKStep_iter_map_checkpoint
    (n k T : ℕ) (q : InfectionRevealTraceState n) :
    (iter (@infectionRevealTraceFirstKStep n k) T q).map
        (InfectionRevealPrefixCheckpoint.ofTrace k) =
      iter (InfectionRevealPrefixCheckpoint.oneStep n k) T
        (InfectionRevealPrefixCheckpoint.ofTrace k q) :=
  iter_map_of_intertwines
    (infectionRevealTraceFirstKStep_intertwines_checkpoint n k)
    T q

/-- Revealed identities carrying immutable label `X`. -/
def InfectionRevealTraceState.revealedXIds
    {n : ℕ} (q : InfectionRevealTraceState n) :
    Finset (Fin n) :=
  q.revealed.toFinset.filter fun i =>
    q.anchor.initialLabel i = .X

/-- Revealed identities carrying immutable label `Y`. -/
def InfectionRevealTraceState.revealedYIds
    {n : ℕ} (q : InfectionRevealTraceState n) :
    Finset (Fin n) :=
  q.revealed.toFinset.filter fun i =>
    q.anchor.initialLabel i = .Y

/-- Revealed and remaining `X` identities partition the anchored `X` set. -/
theorem InfectionRevealTraceState.revealedX_union_current
    {n : ℕ} (q : InfectionRevealTraceState n) :
    q.revealedXIds ∪ q.current.xIds =
      q.anchor.xIds := by
  ext i
  have hpart :
      (i ∈ q.revealed.toFinset ∨ i ∈ q.current.ids) ↔
        i ∈ q.anchor.ids := by
    have hmem := Finset.ext_iff.mp q.hpartition i
    simpa using hmem
  simp only [Finset.mem_union, Finset.mem_filter,
    InfectionRevealTraceState.revealedXIds,
    InfectionInactiveView.xIds]
  rw [q.hinitialLabel]
  constructor
  · rintro (⟨hi, hlabel⟩ | ⟨hi, hlabel⟩)
    · exact ⟨hpart.mp (Or.inl hi), hlabel⟩
    · exact ⟨hpart.mp (Or.inr hi), hlabel⟩
  · rintro ⟨hi, hlabel⟩
    rcases hpart.mpr hi with hi | hi
    · exact Or.inl ⟨hi, hlabel⟩
    · exact Or.inr ⟨hi, hlabel⟩

/-- Revealed and remaining `Y` identities partition the anchored `Y` set. -/
theorem InfectionRevealTraceState.revealedY_union_current
    {n : ℕ} (q : InfectionRevealTraceState n) :
    q.revealedYIds ∪ q.current.yIds =
      q.anchor.yIds := by
  ext i
  have hpart :
      (i ∈ q.revealed.toFinset ∨ i ∈ q.current.ids) ↔
        i ∈ q.anchor.ids := by
    have hmem := Finset.ext_iff.mp q.hpartition i
    simpa using hmem
  simp only [Finset.mem_union, Finset.mem_filter,
    InfectionRevealTraceState.revealedYIds,
    InfectionInactiveView.yIds]
  rw [q.hinitialLabel]
  constructor
  · rintro (⟨hi, hlabel⟩ | ⟨hi, hlabel⟩)
    · exact ⟨hpart.mp (Or.inl hi), hlabel⟩
    · exact ⟨hpart.mp (Or.inr hi), hlabel⟩
  · rintro ⟨hi, hlabel⟩
    rcases hpart.mpr hi with hi | hi
    · exact Or.inl ⟨hi, hlabel⟩
    · exact Or.inr ⟨hi, hlabel⟩

/-- Revealed and remaining `X` identities are disjoint. -/
theorem InfectionRevealTraceState.revealedX_disjoint_current
    {n : ℕ} (q : InfectionRevealTraceState n) :
    Disjoint q.revealedXIds q.current.xIds := by
  exact q.hdisjoint.mono
    (Finset.filter_subset _ _)
    (Finset.filter_subset _ _)

/-- Revealed and remaining `Y` identities are disjoint. -/
theorem InfectionRevealTraceState.revealedY_disjoint_current
    {n : ℕ} (q : InfectionRevealTraceState n) :
    Disjoint q.revealedYIds q.current.yIds := by
  exact q.hdisjoint.mono
    (Finset.filter_subset _ _)
    (Finset.filter_subset _ _)

/-- Exact additive `X` ledger. -/
theorem InfectionRevealTraceState.revealedX_card_add_current
    {n : ℕ} (q : InfectionRevealTraceState n) :
    q.revealedXIds.card + q.current.xIds.card =
      q.anchor.xIds.card := by
  rw [← Finset.card_union_of_disjoint
    q.revealedX_disjoint_current,
    q.revealedX_union_current]

/-- Exact additive `Y` ledger. -/
theorem InfectionRevealTraceState.revealedY_card_add_current
    {n : ℕ} (q : InfectionRevealTraceState n) :
    q.revealedYIds.card + q.current.yIds.card =
      q.anchor.yIds.card := by
  rw [← Finset.card_union_of_disjoint
    q.revealedY_disjoint_current,
    q.revealedY_union_current]

/-- Every reveal removes exactly one inactive identity. -/
theorem InfectionRevealTraceState.revealed_length_add_current
    {n : ℕ} (q : InfectionRevealTraceState n) :
    q.revealed.length + q.current.ids.card =
      q.anchor.ids.card := by
  rw [← List.toFinset_card_of_nodup q.hnodup]
  rw [← Finset.card_union_of_disjoint q.hdisjoint,
    q.hpartition]

end
end Tri

#print axioms Tri.InfectionRevealTraceState.revealedX_union_current
#print axioms Tri.InfectionRevealTraceState.revealedY_union_current
#print axioms Tri.InfectionRevealTraceState.revealedX_disjoint_current
#print axioms Tri.InfectionRevealTraceState.revealedY_disjoint_current
#print axioms Tri.InfectionRevealTraceState.revealedX_card_add_current
#print axioms Tri.InfectionRevealTraceState.revealedY_card_add_current
#print axioms Tri.InfectionRevealTraceState.revealed_length_add_current
#print axioms Tri.infectionRevealTraceStep_map_current
#print axioms Tri.infectionRevealTraceStep_intertwines_urnChain
#print axioms Tri.infectionRevealTraceStep_iter_map_counts
#print axioms Tri.infectionRevealTraceFirstKStep_map_checkpoint
#print axioms Tri.infectionRevealTraceFirstKStep_intertwines_checkpoint
#print axioms Tri.infectionRevealTraceFirstKStep_iter_map_checkpoint
