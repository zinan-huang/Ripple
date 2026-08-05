/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.MultiFiber

/-!
# The exact binary law below the multi-species aggregate

Fix a distinguished species `X` and collapse every other species into one
binary label.  The resulting composition of a uniformly sampled physical
triple has exactly the ordinary binary hypergeometric law.  Combined with the
pointwise aggregate comparison from `Tri.MultiAggregation`, this identifies
the adverse one-step envelope with `Tri.triStep`.
-/

namespace Tri.Multi

open scoped BigOperators ENNReal

variable {m n : ℕ}

/-- The physical molecules whose species is not `X`. -/
noncomputable def otherMolecules
    (c : Config m n) (X : Species m) : Finset (Molecule c) :=
  Finset.univ.filter fun u => u.1 ≠ X

@[simp] theorem mem_otherMolecules
    (c : Config m n) (X : Species m) (u : Molecule c) :
    u ∈ otherMolecules c X ↔ u.1 ≠ X := by
  simp [otherMolecules]

@[simp] theorem card_otherMolecules
    (c : Config m n) (X : Species m) :
    (otherMolecules c X).card = zSum c X := by
  classical
  have hpartition :=
    Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Molecule c)))
      (p := fun u => u.1 = X)
  have hspecies :
      (Finset.univ.filter fun u : Molecule c => u.1 = X) =
        speciesMolecules c X := by
    ext u
    simp
  rw [hspecies] at hpartition
  change
    (speciesMolecules c X).card + (otherMolecules c X).card =
      Fintype.card (Molecule c) at hpartition
  rw [card_speciesMolecules, card_molecule] at hpartition
  have hpopulation := count_add_zSum c X
  omega

/-- A choice of `k` distinguished molecules and `3-k` other molecules. -/
abbrev CollapsedTripleChoice
    (c : Config m n) (X : Species m) (k : ℕ) :=
  ↥((speciesMolecules c X).powersetCard k) ×
    ↥((otherMolecules c X).powersetCard (3 - k))

noncomputable instance collapsedTripleChoiceDecidableEq
    (c : Config m n) (X : Species m) (k : ℕ) :
    DecidableEq (CollapsedTripleChoice c X k) :=
  Classical.decEq _

@[simp] theorem card_collapsedTripleChoice
    (c : Config m n) (X : Species m) (k : ℕ) :
    Fintype.card (CollapsedTripleChoice c X k) =
      Nat.choose (count c X) k * Nat.choose (zSum c X) (3 - k) := by
  classical
  unfold CollapsedTripleChoice
  rw [Fintype.card_prod, Fintype.card_coe, Fintype.card_coe,
    Finset.card_powersetCard, Finset.card_powersetCard,
    card_speciesMolecules, card_otherMolecules]

/-- The physical finset selected by a collapsed-composition choice. -/
noncomputable def collapsedChoiceFinset
    {c : Config m n} {X : Species m} {k : ℕ}
    (q : CollapsedTripleChoice c X k) :
    Finset (Molecule c) :=
  q.1.1 ∪ q.2.1

theorem collapsedChoice_disjoint
    {c : Config m n} {X : Species m} {k : ℕ}
    (q : CollapsedTripleChoice c X k) :
    Disjoint q.1.1 q.2.1 := by
  classical
  refine Finset.disjoint_left.mpr ?_
  intro u huX huOther
  have hXSubset := (Finset.mem_powersetCard.mp q.1.2).1
  have hOtherSubset := (Finset.mem_powersetCard.mp q.2.2).1
  have huEq : u.1 = X :=
    (mem_speciesMolecules c X u).1 (hXSubset huX)
  have huNe : u.1 ≠ X :=
    (mem_otherMolecules c X u).1 (hOtherSubset huOther)
  exact huNe huEq

@[simp] theorem card_collapsedChoiceFinset
    {c : Config m n} {X : Species m} {k : ℕ}
    (hk : k ≤ 3) (q : CollapsedTripleChoice c X k) :
    (collapsedChoiceFinset q).card = 3 := by
  rw [collapsedChoiceFinset,
    Finset.card_union_of_disjoint (collapsedChoice_disjoint q)]
  rw [(Finset.mem_powersetCard.mp q.1.2).2,
    (Finset.mem_powersetCard.mp q.2.2).2]
  omega

theorem collapsedChoice_filter_X
    {c : Config m n} {X : Species m} {k : ℕ}
    (q : CollapsedTripleChoice c X k) :
    (collapsedChoiceFinset q).filter (fun u => u.1 = X) = q.1.1 := by
  classical
  have hXSubset := (Finset.mem_powersetCard.mp q.1.2).1
  have hOtherSubset := (Finset.mem_powersetCard.mp q.2.2).1
  ext u
  constructor
  · intro hu
    rcases Finset.mem_union.mp (Finset.mem_filter.mp hu).1 with huX | huOther
    · exact huX
    · have huNe : u.1 ≠ X :=
        (mem_otherMolecules c X u).1 (hOtherSubset huOther)
      exact False.elim (huNe (Finset.mem_filter.mp hu).2)
  · intro hu
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_union_left _ hu,
        (mem_speciesMolecules c X u).1 (hXSubset hu)⟩

theorem collapsedChoice_filter_other
    {c : Config m n} {X : Species m} {k : ℕ}
    (q : CollapsedTripleChoice c X k) :
    (collapsedChoiceFinset q).filter (fun u => u.1 ≠ X) = q.2.1 := by
  classical
  have hXSubset := (Finset.mem_powersetCard.mp q.1.2).1
  have hOtherSubset := (Finset.mem_powersetCard.mp q.2.2).1
  ext u
  constructor
  · intro hu
    rcases Finset.mem_union.mp (Finset.mem_filter.mp hu).1 with huX | huOther
    · have huEq : u.1 = X :=
        (mem_speciesMolecules c X u).1 (hXSubset huX)
      exact False.elim ((Finset.mem_filter.mp hu).2 huEq)
    · exact huOther
  · intro hu
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_union_right _ hu,
        (mem_otherMolecules c X u).1 (hOtherSubset hu)⟩

/-- A collapsed-composition choice determines a physical triple sample. -/
noncomputable def collapsedChoiceSample
    {c : Config m n} {X : Species m} {k : ℕ}
    (hk : k ≤ 3) (q : CollapsedTripleChoice c X k) :
    TripleSample c :=
  ⟨collapsedChoiceFinset q, card_collapsedChoiceFinset hk q⟩

@[simp] theorem multiplicity_collapsedChoiceSample
    {c : Config m n} {X : Species m} {k : ℕ}
    (hk : k ≤ 3) (q : CollapsedTripleChoice c X k) :
    multiplicity (collapsedChoiceSample hk q) X = k := by
  unfold multiplicity collapsedChoiceSample
  rw [collapsedChoice_filter_X q]
  exact (Finset.mem_powersetCard.mp q.1.2).2

/-- Physical triple samples containing exactly `k` distinguished molecules. -/
abbrev CollapsedKindSample
    (c : Config m n) (X : Species m) (k : ℕ) :=
  {t : TripleSample c // multiplicity t X = k}

noncomputable instance collapsedKindSampleFintype
    (c : Config m n) (X : Species m) (k : ℕ) :
    Fintype (CollapsedKindSample c X k) :=
  Fintype.ofFinite _

noncomputable def collapsedChoiceToKindSample
    {c : Config m n} {X : Species m} {k : ℕ}
    (hk : k ≤ 3) :
    CollapsedTripleChoice c X k → CollapsedKindSample c X k :=
  fun q => ⟨collapsedChoiceSample hk q,
    multiplicity_collapsedChoiceSample hk q⟩

theorem collapsedChoiceToKindSample_injective
    {c : Config m n} {X : Species m} {k : ℕ}
    (hk : k ≤ 3) :
    Function.Injective
      (collapsedChoiceToKindSample (c := c) (X := X) hk) := by
  intro q q' hqq'
  have hs :
      collapsedChoiceFinset q = collapsedChoiceFinset q' :=
    congrArg
      (fun z : CollapsedKindSample c X k => z.1.1)
      hqq'
  have hX :=
    congrArg (fun s : Finset (Molecule c) =>
      s.filter (fun u => u.1 = X)) hs
  change
    (collapsedChoiceFinset q).filter (fun u => u.1 = X) =
      (collapsedChoiceFinset q').filter (fun u => u.1 = X) at hX
  rw [collapsedChoice_filter_X q, collapsedChoice_filter_X q'] at hX
  have hOther :=
    congrArg (fun s : Finset (Molecule c) =>
      s.filter (fun u => u.1 ≠ X)) hs
  change
    (collapsedChoiceFinset q).filter (fun u => u.1 ≠ X) =
      (collapsedChoiceFinset q').filter (fun u => u.1 ≠ X) at hOther
  rw [collapsedChoice_filter_other q,
    collapsedChoice_filter_other q'] at hOther
  exact Prod.ext (Subtype.ext hX) (Subtype.ext hOther)

theorem collapsedChoiceToKindSample_surjective
    {c : Config m n} {X : Species m} {k : ℕ}
    (hk : k ≤ 3) :
    Function.Surjective
      (collapsedChoiceToKindSample (c := c) (X := X) hk) := by
  intro ft
  let A : Finset (Molecule c) :=
    ft.1.1.filter fun u => u.1 = X
  let B : Finset (Molecule c) :=
    ft.1.1.filter fun u => u.1 ≠ X
  have hAsubset : A ⊆ speciesMolecules c X := by
    intro u hu
    exact (mem_speciesMolecules c X u).2
      (Finset.mem_filter.mp hu).2
  have hAcard : A.card = k := ft.2
  have hBsubset : B ⊆ otherMolecules c X := by
    intro u hu
    exact (mem_otherMolecules c X u).2
      (Finset.mem_filter.mp hu).2
  have hpartition :=
    Finset.card_filter_add_card_filter_not
      (s := ft.1.1) (p := fun u => u.1 = X)
  have hBcard : B.card = 3 - k := by
    change A.card + B.card = ft.1.1.card at hpartition
    rw [hAcard, ft.1.2] at hpartition
    omega
  have hAmem :
      A ∈ (speciesMolecules c X).powersetCard k :=
    Finset.mem_powersetCard.mpr ⟨hAsubset, hAcard⟩
  have hBmem :
      B ∈ (otherMolecules c X).powersetCard (3 - k) :=
    Finset.mem_powersetCard.mpr ⟨hBsubset, hBcard⟩
  let q : CollapsedTripleChoice c X k :=
    (⟨A, hAmem⟩, ⟨B, hBmem⟩)
  refine ⟨q, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change collapsedChoiceFinset q = ft.1.1
  unfold collapsedChoiceFinset
  change A ∪ B = ft.1.1
  exact Finset.filter_union_filter_not_eq _ _

noncomputable def collapsedChoiceKindEquiv
    {c : Config m n} {X : Species m} {k : ℕ}
    (hk : k ≤ 3) :
    CollapsedTripleChoice c X k ≃ CollapsedKindSample c X k :=
  Equiv.ofBijective
    (collapsedChoiceToKindSample (c := c) (X := X) hk)
    ⟨collapsedChoiceToKindSample_injective hk,
      collapsedChoiceToKindSample_surjective hk⟩

theorem card_collapsedKindSample
    (c : Config m n) (X : Species m) (k : ℕ) (hk : k ≤ 3) :
    Fintype.card (CollapsedKindSample c X k) =
      Nat.choose (count c X) k * Nat.choose (zSum c X) (3 - k) := by
  rw [← card_collapsedTripleChoice c X k]
  exact Fintype.card_congr
    (collapsedChoiceKindEquiv (c := c) (X := X) hk).symm

theorem multiplicity_le_three
    {c : Config m n} (t : TripleSample c) (X : Species m) :
    multiplicity t X ≤ 3 := by
  unfold multiplicity
  calc
    (t.1.filter fun u => u.1 = X).card ≤ t.1.card :=
      Finset.card_filter_le _ _
    _ = 3 := t.2

theorem collapsedBinaryKind_eq_iff
    {c : Config m n} (X : Species m) (t : TripleSample c)
    (kind : Tri.TripleKind) :
    collapsedBinaryKind X t = kind ↔
      multiplicity t X =
        match kind with
        | .xxx => 3
        | .xxy => 2
        | .xyy => 1
        | .yyy => 0 := by
  have hle := multiplicity_le_three t X
  by_cases hm3 : multiplicity t X = 3
  · cases kind <;> simp [collapsedBinaryKind, hm3]
  by_cases hm2 : multiplicity t X = 2
  · cases kind <;> simp [collapsedBinaryKind, hm2]
  by_cases hm1 : multiplicity t X = 1
  · cases kind <;> simp [collapsedBinaryKind, hm1]
  have hm0 : multiplicity t X = 0 := by omega
  cases kind <;> simp [collapsedBinaryKind, hm0]

theorem collapsedBinaryKind_distribution
    (c : Config m n) (X : Species m) (h3 : 3 ≤ n) :
    (triplePMF c h3).map (collapsedBinaryKind X) =
      Tri.interactionPMF (count c X) (zSum c X)
        (by simpa [count_add_zSum c X] using h3) := by
  ext kind
  rw [PMF.map_apply, tsum_fintype]
  simp_rw [triplePMF_apply]
  rw [← Finset.sum_filter]
  rw [Finset.sum_const, nsmul_eq_mul]
  have hpopulation := count_add_zSum c X
  have hcard :
      ((Finset.univ.filter fun t : TripleSample c =>
        collapsedBinaryKind X t = kind).card) =
        Tri.TripleKind.weight (count c X) (zSum c X) kind := by
    rw [← Fintype.card_subtype
      (fun t : TripleSample c => collapsedBinaryKind X t = kind)]
    cases kind
    · simpa [Tri.TripleKind.weight, collapsedBinaryKind_eq_iff] using
        card_collapsedKindSample c X 3 (by omega)
    · simpa [Tri.TripleKind.weight, collapsedBinaryKind_eq_iff] using
        card_collapsedKindSample c X 2 (by omega)
    · simpa [Tri.TripleKind.weight, collapsedBinaryKind_eq_iff,
        Nat.mul_comm] using
        card_collapsedKindSample c X 1 (by omega)
    · simpa [Tri.TripleKind.weight, collapsedBinaryKind_eq_iff] using
        card_collapsedKindSample c X 0 (by omega)
  have hcard' :
      ((Finset.univ.filter fun t : TripleSample c =>
        kind = collapsedBinaryKind X t).card) =
        Tri.TripleKind.weight (count c X) (zSum c X) kind := by
    simpa only [eq_comm] using hcard
  rw [hcard', Tri.interactionPMF_apply]
  simp only [div_eq_mul_inv]
  rw [hpopulation]

/-- The adverse collapsed one-step law is exactly the ordinary binary step. -/
theorem collapsedBinarySampleStep_eq_triStep
    (c : Config m n) (X : Species m) (h3 : 3 ≤ n) :
    collapsedBinarySampleStep c X h3 =
      Tri.triStep (count c X) (zSum c X)
        (by simpa [count_add_zSum c X] using h3) := by
  unfold collapsedBinarySampleStep collapsedBinaryNextX Tri.triStep
  calc
    (triplePMF c h3).map
        (fun t => Tri.nextX (count c X) (collapsedBinaryKind X t)) =
        ((triplePMF c h3).map (collapsedBinaryKind X)).map
          (Tri.nextX (count c X)) := by
      rw [PMF.map_comp]
      rfl
    _ = _ := by rw [collapsedBinaryKind_distribution]

/-- Every increasing one-step observable is smaller under the ordinary binary
envelope than under the physical multi-species process. -/
theorem triStep_expect_le_multiStep_count
    (c : Config m n) (X : Species m) (h3 : 3 ≤ n)
    (F : ℕ → ℝ≥0∞) (hF : Monotone F) :
    expect
        (Tri.triStep (count c X) (zSum c X)
          (by simpa [count_add_zSum c X] using h3)) F ≤
      expect ((multiStep c h3).map (fun d => count d X)) F := by
  rw [← collapsedBinarySampleStep_eq_triStep]
  exact collapsedBinarySampleStep_expect_le_multiStep_count c X h3 F hF

end Tri.Multi

#print axioms Tri.Multi.card_collapsedKindSample
#print axioms Tri.Multi.collapsedBinaryKind_distribution
#print axioms Tri.Multi.collapsedBinarySampleStep_eq_triStep
#print axioms Tri.Multi.triStep_expect_le_multiStep_count
