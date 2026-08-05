/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.InfectionRevealPhysicalPairLaw

/-!
# Ordered two-reveals as successive sampling without replacement

The uniform ordered-pair carrier is equivalent to first choosing one inactive
identity and then choosing one from the erased view.  This identifies the
physical two-activation order with two successive ordinary urn reveals and,
in particular, proves that its first coordinate is uniform.
-/

namespace Tri

open scoped ENNReal BigOperators

noncomputable section

/-- Dependent carrier of two successive reveals without replacement. -/
abbrev InfectionSequentialRevealTwo
    {n : ℕ} (v : InfectionInactiveView n) :=
  Σ i : InfectionInactiveId v,
    InfectionInactiveId (v.erase i)

/-- Regard an identity in an erased view as an identity in the old view. -/
def infectionEraseIdToOld
    {n : ℕ} {v : InfectionInactiveView n}
    (i : InfectionInactiveId v)
    (j : InfectionInactiveId (v.erase i)) :
    InfectionInactiveId v :=
  ⟨j.1, by
    have hj : j.1 ∈ v.ids.erase i.1 := by
      simpa only [InfectionInactiveView.erase_ids] using j.2
    exact Finset.mem_of_mem_erase hj⟩

/-- A dependent first/second pair is an ordered distinct pair in the old view. -/
def infectionSequentialToOrdered
    {n : ℕ} {v : InfectionInactiveView n} :
    InfectionSequentialRevealTwo v → InfectionOrderedRevealTwo v
  | ⟨i, j⟩ =>
      ⟨(i, infectionEraseIdToOld i j), by
        intro hij
        have hj : j.1 ∈ v.ids.erase i.1 := by
          simpa only [InfectionInactiveView.erase_ids] using j.2
        have hval : i.1 = j.1 :=
          congrArg Subtype.val hij
        exact (Finset.ne_of_mem_erase hj) hval.symm⟩

/-- Ordered distinct pairs and dependent successive pairs are equivalent. -/
def infectionSequentialRevealTwoEquiv
    {n : ℕ} (v : InfectionInactiveView n) :
    InfectionSequentialRevealTwo v ≃ InfectionOrderedRevealTwo v where
  toFun := infectionSequentialToOrdered (v := v)
  invFun := fun p =>
    ⟨p.1.1, infectionRevealTwoSecondAfterFirst p⟩
  left_inv := by
    rintro ⟨i, j⟩
    apply Sigma.ext
    · rfl
    · rfl
  right_inv := by
    intro p
    apply Subtype.ext
    rfl

/-- Every second-draw fibre has the expected additive cardinality. -/
theorem infectionErase_card_eq_add_one
    {n m : ℕ} (v : InfectionInactiveView n)
    (hcard : m + 2 = v.ids.card)
    (i : InfectionInactiveId v) :
    (v.erase i).ids.card = m + 1 := by
  have h := v.erase_card_add_one i
  omega

theorem infectionSequentialReveal_first_nonempty
    {n m : ℕ} (v : InfectionInactiveView n)
    (hcard : m + 2 = v.ids.card) :
    Nonempty (InfectionInactiveId v) :=
  infectionRevealOne_nonempty_of_card_pos v (by omega)

theorem infectionSequentialReveal_second_nonempty
    {n m : ℕ} (v : InfectionInactiveView n)
    (hcard : m + 2 = v.ids.card)
    (i : InfectionInactiveId v) :
    Nonempty (InfectionInactiveId (v.erase i)) :=
  infectionRevealOne_nonempty_of_card_pos (v.erase i) (by
    rw [infectionErase_card_eq_add_one v hcard i]
    omega)

theorem infectionSequentialReveal_ordered_nonempty
    {n m : ℕ} (v : InfectionInactiveView n)
    (hcard : m + 2 = v.ids.card) :
    Nonempty (InfectionOrderedRevealTwo v) := by
  let i := Classical.choice
    (infectionSequentialReveal_first_nonempty v hcard)
  let j := Classical.choice
    (infectionSequentialReveal_second_nonempty v hcard i)
  exact ⟨infectionSequentialRevealTwoEquiv v ⟨i, j⟩⟩

/-- Cardinality of the dependent successive-reveal carrier. -/
theorem card_infectionSequentialRevealTwo
    {n m : ℕ} (v : InfectionInactiveView n)
    (hcard : m + 2 = v.ids.card) :
    Fintype.card (InfectionSequentialRevealTwo v) =
      (m + 2) * (m + 1) := by
  classical
  calc
    Fintype.card (InfectionSequentialRevealTwo v) =
        ∑ i : InfectionInactiveId v,
          Fintype.card (InfectionInactiveId (v.erase i)) := by
      rw [Fintype.card_sigma]
    _ = ∑ _i : InfectionInactiveId v, (m + 1) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [card_infectionInactiveId,
        infectionErase_card_eq_add_one v hcard i]
    _ = Fintype.card (InfectionInactiveId v) * (m + 1) := by
      simp
    _ = (m + 2) * (m + 1) := by
      rw [card_infectionInactiveId, ← hcard]

/-- Cardinality of ordered distinct pairs in the same additive form. -/
theorem card_infectionOrderedRevealTwo_add
    {n m : ℕ} (v : InfectionInactiveView n)
    (hcard : m + 2 = v.ids.card) :
    Fintype.card (InfectionOrderedRevealTwo v) =
      (m + 2) * (m + 1) := by
  calc
    Fintype.card (InfectionOrderedRevealTwo v) =
        Fintype.card (InfectionSequentialRevealTwo v) :=
      (Fintype.card_congr
        (infectionSequentialRevealTwoEquiv v)).symm
    _ = (m + 2) * (m + 1) :=
      card_infectionSequentialRevealTwo v hcard

def infectionSequentialRevealMk
    {n : ℕ} {v : InfectionInactiveView n}
    (i : InfectionInactiveId v)
    (j : InfectionInactiveId (v.erase i)) :
    InfectionSequentialRevealTwo v :=
  ⟨i, j⟩

theorem infectionSequentialRevealMk_injective
    {n : ℕ} {v : InfectionInactiveView n}
    (i : InfectionInactiveId v) :
    Function.Injective (infectionSequentialRevealMk (v := v) i) := by
  intro a b h
  cases h
  rfl

/-- Literal law of two successive dependent uniform draws. -/
noncomputable def infectionSequentialRevealTwoPMF
    {n m : ℕ} (v : InfectionInactiveView n)
    (hcard : m + 2 = v.ids.card) :
    PMF (InfectionSequentialRevealTwo v) :=
  (infectionRevealOnePMF v
      (infectionSequentialReveal_first_nonempty v hcard)).bind fun i =>
    (infectionRevealOnePMF (v.erase i)
      (infectionSequentialReveal_second_nonempty v hcard i)).map
        (infectionSequentialRevealMk (v := v) i)

/-- Exact point mass of the dependent bind. -/
theorem infectionSequentialRevealTwoPMF_apply
    {n m : ℕ} (v : InfectionInactiveView n)
    (hcard : m + 2 = v.ids.card)
    (q : InfectionSequentialRevealTwo v) :
    infectionSequentialRevealTwoPMF v hcard q =
      infectionRevealOnePMF v
          (infectionSequentialReveal_first_nonempty v hcard) q.1 *
        infectionRevealOnePMF (v.erase q.1)
          (infectionSequentialReveal_second_nonempty v hcard q.1) q.2 := by
  classical
  rcases q with ⟨i, j⟩
  unfold infectionSequentialRevealTwoPMF
  rw [PMF.bind_apply, tsum_eq_single i]
  · change
      infectionRevealOnePMF v
            (infectionSequentialReveal_first_nonempty v hcard) i *
          ((infectionRevealOnePMF (v.erase i)
            (infectionSequentialReveal_second_nonempty v hcard i)).map
              (infectionSequentialRevealMk (v := v) i))
            (infectionSequentialRevealMk i j) =
        infectionRevealOnePMF v
            (infectionSequentialReveal_first_nonempty v hcard) i *
          infectionRevealOnePMF (v.erase i)
            (infectionSequentialReveal_second_nonempty v hcard i) j
    rw [pmf_map_apply_of_injective _ _
      (infectionSequentialRevealMk_injective (v := v) i) j]
  · intro i' hi'
    have hnot :
        (⟨i, j⟩ : InfectionSequentialRevealTwo v) ∉
          Set.range (infectionSequentialRevealMk (v := v) i') := by
      rintro ⟨j', hj'⟩
      have hfirst : i' = i :=
        congrArg Sigma.fst hj'
      exact hi' hfirst
    rw [pmf_map_apply_eq_zero_of_not_mem_range]
    · simp
    · intro j' h
      exact hnot ⟨j', h.symm⟩

/-- Every successive pair has the common reciprocal product mass. -/
theorem infectionSequentialRevealTwoPMF_apply_uniform
    {n m : ℕ} (v : InfectionInactiveView n)
    (hcard : m + 2 = v.ids.card)
    (q : InfectionSequentialRevealTwo v) :
    infectionSequentialRevealTwoPMF v hcard q =
      (((((m + 2) * (m + 1) : ℕ) : ℝ≥0∞))⁻¹) := by
  rw [infectionSequentialRevealTwoPMF_apply,
    infectionRevealOnePMF_apply,
    infectionRevealOnePMF_apply,
    card_infectionInactiveId,
    card_infectionInactiveId,
    infectionErase_card_eq_add_one v hcard q.1,
    ← hcard]
  rw [Nat.cast_mul]
  exact (ENNReal.mul_inv
    (Or.inr (ENNReal.natCast_ne_top _))
    (Or.inl (ENNReal.natCast_ne_top _))).symm

/-- Two successive uniform draws push forward to the uniform ordered-pair law. -/
theorem infectionSequentialRevealTwoPMF_map_equiv
    {n m : ℕ} (v : InfectionInactiveView n)
    (hcard : m + 2 = v.ids.card) :
    (infectionSequentialRevealTwoPMF v hcard).map
        (infectionSequentialRevealTwoEquiv v) =
      infectionRevealTwoPMF v
        (infectionSequentialReveal_ordered_nonempty v hcard) := by
  apply PMF.ext
  intro p
  rw [show p = infectionSequentialRevealTwoEquiv v
      ((infectionSequentialRevealTwoEquiv v).symm p) by simp]
  rw [pmf_map_apply_of_injective _ _
    (infectionSequentialRevealTwoEquiv v).injective]
  rw [infectionSequentialRevealTwoPMF_apply_uniform,
    infectionRevealTwoPMF_apply,
    card_infectionOrderedRevealTwo_add v hcard]

/-- Forgetting the second dependent draw recovers the first uniform draw. -/
theorem infectionSequentialRevealTwoPMF_map_fst
    {n m : ℕ} (v : InfectionInactiveView n)
    (hcard : m + 2 = v.ids.card) :
    (infectionSequentialRevealTwoPMF v hcard).map Sigma.fst =
      infectionRevealOnePMF v
        (infectionSequentialReveal_first_nonempty v hcard) := by
  unfold infectionSequentialRevealTwoPMF
  rw [PMF.map_bind]
  simp_rw [PMF.map_comp]
  have hconst :
      ∀ i : InfectionInactiveId v,
        Sigma.fst ∘ infectionSequentialRevealMk (v := v) i =
          Function.const (InfectionInactiveId (v.erase i)) i := by
    intro i
    rfl
  simp_rw [hconst, PMF.map_const]
  exact PMF.bind_pure _

/-- The first coordinate of a uniform ordered distinct pair is uniform. -/
theorem infectionRevealTwoPMF_map_fst
    {n m : ℕ} (v : InfectionInactiveView n)
    (hcard : m + 2 = v.ids.card) :
    (infectionRevealTwoPMF v
        (infectionSequentialReveal_ordered_nonempty v hcard)).map
          (fun p => p.1.1) =
      infectionRevealOnePMF v
        (infectionSequentialReveal_first_nonempty v hcard) := by
  rw [← infectionSequentialRevealTwoPMF_map_equiv v hcard]
  rw [PMF.map_comp]
  change
    (infectionSequentialRevealTwoPMF v hcard).map Sigma.fst =
      infectionRevealOnePMF v
        (infectionSequentialReveal_first_nonempty v hcard)
  exact infectionSequentialRevealTwoPMF_map_fst v hcard

end
end Tri

#print axioms Tri.infectionSequentialRevealTwoEquiv
#print axioms Tri.card_infectionSequentialRevealTwo
#print axioms Tri.card_infectionOrderedRevealTwo_add
#print axioms Tri.infectionSequentialRevealTwoPMF_apply
#print axioms Tri.infectionSequentialRevealTwoPMF_apply_uniform
#print axioms Tri.infectionSequentialRevealTwoPMF_map_equiv
#print axioms Tri.infectionSequentialRevealTwoPMF_map_fst
#print axioms Tri.infectionRevealTwoPMF_map_fst
