/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.InfectionRevealPhysicalTimeChange
import Tri.InfectionRevealPhysicalWordLaw

/-!
# A first-prefix chain driven by physical activation batches

This chain records uniform inactive reveals one identity at a time and absorbs
as soon as its word reaches length `k`.  A physical one-batch is one step of
this chain.  A physical two-batch is two successive steps, including the
boundary case where its first identity completes the prefix.
-/

namespace Tri

noncomputable section

inductive InfectionRevealPrefixCheckpoint (n : ℕ)
  | live
      (remaining : InfectionInactiveView n)
      (word : List (Fin n))
  | done
      (word : List (Fin n))

namespace InfectionRevealPrefixCheckpoint

/-- Add one uniformly revealed inactive identity, absorbing exactly at the
first `k`-prefix. -/
def afterOne
    {n : ℕ} (k : ℕ) (v : InfectionInactiveView n)
    (word : List (Fin n)) (i : InfectionInactiveId v) :
    InfectionRevealPrefixCheckpoint n :=
  let nextWord := word ++ [i.1]
  if k ≤ nextWord.length then
    .done (nextWord.take k)
  else
    .live (v.erase i) nextWord

/-- The stopped one-identity reveal kernel. -/
noncomputable def oneStep
    (n k : ℕ) :
    InfectionRevealPrefixCheckpoint n →
      PMF (InfectionRevealPrefixCheckpoint n)
  | .done word => PMF.pure (.done word)
  | .live v word =>
      if k ≤ word.length then
        PMF.pure (.done (word.take k))
      else if h : 0 < v.ids.card then
        (infectionRevealOnePMF v
          (infectionRevealOne_nonempty_of_card_pos v h)).map
          (afterOne k v word)
      else
        PMF.pure (.live v word)

/-- Apply a complete physical batch, stopping inside a two-batch when its first
identity completes the prefix. -/
def afterBatch
    {n : ℕ} (k : ℕ) (v : InfectionInactiveView n)
    (word : List (Fin n)) :
    InfectionRevealBatch v →
      InfectionRevealPrefixCheckpoint n
  | .none =>
      if k ≤ word.length then
        .done (word.take k)
      else
        .live v word
  | .one i =>
      if k ≤ word.length then
        .done (word.take k)
      else
        afterOne k v word i
  | .two p =>
      if k ≤ word.length then
        .done (word.take k)
      else
        let word₁ := word ++ [p.1.1.1]
        if k ≤ word₁.length then
          .done (word₁.take k)
        else
          let word₂ := word₁ ++ [p.1.2.1]
          if k ≤ word₂.length then
            .done (word₂.take k)
          else
            .live (infectionRevealEraseTwo v p) word₂

/-- Normal form of a batch update: append the whole batch unless the first
identity of a two-batch already completes the stopped prefix. -/
theorem afterBatch_eq
    {n : ℕ} (k : ℕ) (v : InfectionInactiveView n)
    (word : List (Fin n)) (b : InfectionRevealBatch v) :
    afterBatch k v word b =
      if k ≤ word.length then
        .done (word.take k)
      else
        let nextWord := word ++ b.ids
        if k ≤ nextWord.length then
          .done (nextWord.take k)
        else
          .live b.remaining nextWord := by
  cases b with
  | none =>
      simp [afterBatch, InfectionRevealBatch.ids,
        InfectionRevealBatch.remaining]
  | one i =>
      simp [afterBatch, InfectionRevealBatch.ids,
        InfectionRevealBatch.remaining, afterOne]
  | two p =>
      by_cases h₀ : k ≤ word.length
      · simp [afterBatch, InfectionRevealBatch.ids,
          InfectionRevealBatch.remaining, h₀]
      · by_cases h₁ :
            k ≤ (word ++ [p.1.1.1]).length
        · have htake :
              (word ++ [p.1.1.1, p.1.2.1]).take k =
                (word ++ [p.1.1.1]).take k := by
            rw [show word ++ [p.1.1.1, p.1.2.1] =
              (word ++ [p.1.1.1]) ++ [p.1.2.1] by
                simp [List.append_assoc]]
            exact List.take_append_of_le_length h₁
          have h₁' : k ≤ word.length + 1 := by
            simpa using h₁
          have h₂ :
              k ≤ (word ++ [p.1.1.1, p.1.2.1]).length := by
            simp only [List.length_append, List.length_cons,
              List.length_nil]
            omega
          have h₂' : k ≤ word.length + 2 := by
            simpa using h₂
          simp [afterBatch, InfectionRevealBatch.ids,
            InfectionRevealBatch.remaining, h₀, h₁',
            h₂', htake]
        · have h₁' : ¬ k ≤ word.length + 1 := by
            simpa using h₁
          simp [afterBatch, InfectionRevealBatch.ids,
            InfectionRevealBatch.remaining, h₀, h₁',
            List.append_assoc]

end InfectionRevealPrefixCheckpoint

theorem infectionInactiveView_ext
    {n : ℕ} {v w : InfectionInactiveView n}
    (hids : v.ids = w.ids)
    (hlabel : v.initialLabel = w.initialLabel) :
    v = w := by
  cases v
  cases w
  simp_all

@[simp] theorem infectionSequentialRevealTwoEquiv_first
    {n : ℕ} {v : InfectionInactiveView n}
    (i : InfectionInactiveId v)
    (j : InfectionInactiveId (v.erase i)) :
    (infectionSequentialRevealTwoEquiv v
      (infectionSequentialRevealMk i j)).1.1 = i :=
  rfl

@[simp] theorem infectionSequentialRevealTwoEquiv_second
    {n : ℕ} {v : InfectionInactiveView n}
    (i : InfectionInactiveId v)
    (j : InfectionInactiveId (v.erase i)) :
    infectionRevealTwoSecondAfterFirst
        (infectionSequentialRevealTwoEquiv v
          (infectionSequentialRevealMk i j)) = j := by
  apply Subtype.ext
  rfl

@[simp] theorem infectionSequentialRevealTwoEquiv_fst
    {n : ℕ} {v : InfectionInactiveView n}
    (q : InfectionSequentialRevealTwo v) :
    (infectionSequentialRevealTwoEquiv v q).1.1 = q.1 := by
  rcases q with ⟨i, j⟩
  rfl

@[simp] theorem infectionSequentialRevealTwoEquiv_snd
    {n : ℕ} {v : InfectionInactiveView n}
    (q : InfectionSequentialRevealTwo v) :
    infectionRevealTwoSecondAfterFirst
        (infectionSequentialRevealTwoEquiv v q) = q.2 := by
  rcases q with ⟨i, j⟩
  apply Subtype.ext
  rfl

@[simp] theorem infectionSequentialRevealTwoEquiv_second_value
    {n : ℕ} {v : InfectionInactiveView n}
    (i : InfectionInactiveId v)
    (j : InfectionInactiveId (v.erase i)) :
    (infectionSequentialRevealTwoEquiv v
      ⟨i, j⟩).1.2.1 = j.1 :=
  rfl

@[simp] theorem infectionSequentialRevealRemaining_mk
    {n : ℕ} {v : InfectionInactiveView n}
    (i : InfectionInactiveId v)
    (j : InfectionInactiveId (v.erase i)) :
    infectionSequentialRevealRemaining ⟨i, j⟩ =
      (v.erase i).erase j :=
  rfl

@[simp] theorem infectionSequentialRevealTwoEquiv_erase_fst
    {n : ℕ} {v : InfectionInactiveView n}
    (q : InfectionSequentialRevealTwo v) :
    v.erase (infectionSequentialRevealTwoEquiv v q).1.1 =
      v.erase q.1 := by
  rw [infectionSequentialRevealTwoEquiv_fst]

@[simp] theorem infectionRevealEraseTwo_equiv
    {n : ℕ} {v : InfectionInactiveView n}
    (q : InfectionSequentialRevealTwo v) :
    infectionRevealEraseTwo v
        (infectionSequentialRevealTwoEquiv v q) =
      infectionSequentialRevealRemaining q := by
  rcases q with ⟨i, j⟩
  apply infectionInactiveView_ext
  · have hs :
        (infectionRevealTwoSecondAfterFirst
          (infectionSequentialRevealTwoEquiv v ⟨i, j⟩)).1 =
            j.1 := rfl
    change
      (v.ids.erase i.1).erase
          (infectionRevealTwoSecondAfterFirst
            (infectionSequentialRevealTwoEquiv v ⟨i, j⟩)).1 =
        (v.ids.erase i.1).erase j.1
    exact congrArg (fun z => (v.ids.erase i.1).erase z) hs
  · rfl

/-- A conditional physical one-batch is exactly one stopped uniform reveal. -/
theorem infectionRevealGivenBatchSize_one_map_checkpoint
    {n k : ℕ} (s : InfectionRevealPhysicalState n)
    (word : List (Fin n))
    (h : Nonempty (InfectionInactiveId s.inactive)) :
    (infectionRevealGivenBatchSize s .one).map
        (InfectionRevealPrefixCheckpoint.afterBatch
          k s.inactive word) =
      InfectionRevealPrefixCheckpoint.oneStep n k
        (.live s.inactive word) := by
  classical
  have hpos : 0 < s.inactive.ids.card := by
    rcases h with ⟨i⟩
    exact Finset.card_pos.mpr ⟨i.1, i.2⟩
  simp only [infectionRevealGivenBatchSize,
    InfectionRevealPrefixCheckpoint.oneStep]
  rw [dif_pos h]
  by_cases hk : k ≤ word.length
  · rw [if_pos hk]
    simp only [PMF.map_comp]
    have hfun :
        InfectionRevealPrefixCheckpoint.afterBatch
              k s.inactive word ∘ InfectionRevealBatch.one =
            Function.const _
              (InfectionRevealPrefixCheckpoint.done (word.take k)) := by
      funext i
      simp [InfectionRevealPrefixCheckpoint.afterBatch, hk]
    rw [hfun, PMF.map_const]
  · rw [if_neg hk, dif_pos hpos]
    simp only [PMF.map_comp]
    congr 1
    funext i
    simp [InfectionRevealPrefixCheckpoint.afterBatch, hk]

/-- A conditional physical two-batch is exactly two stopped uniform reveals. -/
theorem infectionRevealGivenBatchSize_two_map_checkpoint
    {n m k : ℕ} (s : InfectionRevealPhysicalState n)
    (word : List (Fin n))
    (hcard : m + 2 = s.inactive.ids.card) :
    (infectionRevealGivenBatchSize s .two).map
        (InfectionRevealPrefixCheckpoint.afterBatch
          k s.inactive word) =
      iter (InfectionRevealPrefixCheckpoint.oneStep n k) 2
        (.live s.inactive word) := by
  classical
  let hfirst :=
    infectionSequentialReveal_first_nonempty
      s.inactive hcard
  let hsecond := fun i =>
    infectionSequentialReveal_second_nonempty
      s.inactive hcard i
  have hfirstPos : 0 < s.inactive.ids.card := by omega
  simp only [infectionRevealGivenBatchSize]
  rw [dif_pos
    (infectionSequentialReveal_ordered_nonempty
      s.inactive hcard)]
  rw [← infectionSequentialRevealTwoPMF_map_equiv
    s.inactive hcard]
  simp only [PMF.map_comp]
  change
    (infectionSequentialRevealTwoPMF
      s.inactive hcard).map
        (InfectionRevealPrefixCheckpoint.afterBatch
          k s.inactive word ∘
            InfectionRevealBatch.two ∘
              infectionSequentialRevealTwoEquiv s.inactive) =
      iter (InfectionRevealPrefixCheckpoint.oneStep n k) 2
        (.live s.inactive word)
  by_cases hk : k ≤ word.length
  · have hfun :
      (InfectionRevealPrefixCheckpoint.afterBatch
            k s.inactive word ∘
          InfectionRevealBatch.two ∘
            infectionSequentialRevealTwoEquiv s.inactive) =
        Function.const _
          (InfectionRevealPrefixCheckpoint.done
            (word.take k)) := by
      funext q
      simp [Function.comp_def,
        InfectionRevealPrefixCheckpoint.afterBatch, hk]
    rw [hfun, PMF.map_const]
    simp [iter, InfectionRevealPrefixCheckpoint.oneStep, hk]
  · simp only [iter, PMF.bind_pure]
    unfold infectionSequentialRevealTwoPMF
    simp only [InfectionRevealPrefixCheckpoint.oneStep]
    rw [PMF.map_bind]
    rw [if_neg hk, dif_pos hfirstPos, PMF.bind_map]
    congr 1
    funext i
    simp only [Function.comp_apply]
    let word₁ := word ++ [i.1]
    by_cases hk₁ : k ≤ word₁.length
    · have hafter :
        InfectionRevealPrefixCheckpoint.afterOne
            k s.inactive word i =
          InfectionRevealPrefixCheckpoint.done
            (word₁.take k) := by
            change
              (if k ≤ word₁.length then
                  InfectionRevealPrefixCheckpoint.done
                    (word₁.take k)
                else
                  InfectionRevealPrefixCheckpoint.live
                    (s.inactive.erase i) word₁) =
                InfectionRevealPrefixCheckpoint.done
                  (word₁.take k)
            rw [if_pos hk₁]
      rw [hafter]
      simp only [PMF.map_comp]
      have hfun :
          ((InfectionRevealPrefixCheckpoint.afterBatch
                k s.inactive word ∘
              InfectionRevealBatch.two ∘
                infectionSequentialRevealTwoEquiv s.inactive) ∘
              infectionSequentialRevealMk i) =
            Function.const _
              (InfectionRevealPrefixCheckpoint.done
                (word₁.take k)) := by
        funext j
        have hk₁' : k ≤ word.length + 1 := by
          simpa [word₁] using hk₁
        simp [Function.comp_def,
          InfectionRevealPrefixCheckpoint.afterBatch,
          infectionSequentialRevealMk,
          hk, hk₁', word₁]
      rw [hfun, PMF.map_const]
    · have hafter :
        InfectionRevealPrefixCheckpoint.afterOne
            k s.inactive word i =
          InfectionRevealPrefixCheckpoint.live
            (s.inactive.erase i) word₁ := by
            change
              (if k ≤ word₁.length then
                  InfectionRevealPrefixCheckpoint.done
                    (word₁.take k)
                else
                  InfectionRevealPrefixCheckpoint.live
                    (s.inactive.erase i) word₁) =
                InfectionRevealPrefixCheckpoint.live
                  (s.inactive.erase i) word₁
            rw [if_neg hk₁]
      rw [hafter]
      simp only [PMF.map_comp]
      have hsecondPos :
          0 < (s.inactive.erase i).ids.card := by
        rw [infectionErase_card_eq_add_one
          s.inactive hcard i]
        omega
      rw [if_neg hk₁, dif_pos hsecondPos]
      congr 1
      funext j
      have hk₁' : ¬ k ≤ word.length + 1 := by
        simpa [word₁] using hk₁
      simp [Function.comp_def,
        InfectionRevealPrefixCheckpoint.afterBatch,
        InfectionRevealPrefixCheckpoint.afterOne,
        infectionSequentialRevealMk,
        hk, hk₁', word₁]

end
end Tri

#print axioms Tri.infectionInactiveView_ext
#print axioms Tri.InfectionRevealPrefixCheckpoint.afterBatch_eq
#print axioms Tri.infectionSequentialRevealTwoEquiv_first
#print axioms Tri.infectionSequentialRevealTwoEquiv_second
#print axioms Tri.infectionSequentialRevealTwoEquiv_fst
#print axioms Tri.infectionSequentialRevealTwoEquiv_snd
#print axioms Tri.infectionSequentialRevealTwoEquiv_second_value
#print axioms Tri.infectionSequentialRevealRemaining_mk
#print axioms Tri.infectionSequentialRevealTwoEquiv_erase_fst
#print axioms Tri.infectionRevealEraseTwo_equiv
#print axioms Tri.infectionRevealGivenBatchSize_one_map_checkpoint
#print axioms Tri.infectionRevealGivenBatchSize_two_map_checkpoint
