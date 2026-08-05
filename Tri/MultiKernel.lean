/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.MultiState
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset
import Mathlib.Probability.Distributions.Uniform

/-!
# Uniform semantic triple samples for multi-species Tri

A molecule is a dependent pair consisting of a species label and a slot below
that species' current population. An interaction sample is an unordered
three-element finset of distinct molecules. A sample fires when one species has
multiplicity two and a distinct species has multiplicity one.

This file deliberately stops before defining any population transfer or state
kernel.
-/

namespace Tri.Multi

open scoped BigOperators ENNReal

variable {m n : ℕ}

/-- A physical molecule in configuration `c`: a species label and a slot below
that species' current count. -/
def Molecule (c : Config m n) :=
  Σ i : Species m, Fin (count c i)

noncomputable instance moleculeDecidableEq
    (c : Config m n) : DecidableEq (Molecule c) :=
  Classical.decEq _

noncomputable instance moleculeFintype
    (c : Config m n) : Fintype (Molecule c) := by
  unfold Molecule
  infer_instance

/-- The dependent molecule type has exactly the conserved population size. -/
@[simp] theorem card_molecule (c : Config m n) :
    Fintype.card (Molecule c) = n := by
  classical
  change Fintype.card (Σ i : Species m, Fin (count c i)) = n
  rw [Fintype.card_sigma]
  simpa using sum_count c

/-- An unordered interaction sample containing exactly three distinct
molecules. -/
def TripleSample (c : Config m n) :=
  {s : Finset (Molecule c) // s.card = 3}

noncomputable instance tripleSampleDecidableEq
    (c : Config m n) : DecidableEq (TripleSample c) :=
  Classical.decEq _

noncomputable instance tripleSampleFintype
    (c : Config m n) : Fintype (TripleSample c) := by
  unfold TripleSample
  infer_instance

/-- There are exactly `C(n,3)` unordered three-molecule samples. -/
@[simp] theorem card_tripleSample (c : Config m n) :
    Fintype.card (TripleSample c) = Nat.choose n 3 := by
  classical
  simpa only [TripleSample, card_molecule] using
    (Fintype.card_finset_len (α := Molecule c) 3)

/-- At population at least three, the unordered sample type is inhabited. -/
theorem tripleSampleNonempty
    (c : Config m n) (h3 : 3 ≤ n) :
    Nonempty (TripleSample c) :=
  Fintype.card_pos_iff.mp (by
    rw [card_tripleSample]
    exact Tri.choose_three_pos h3)

/-- The uniform distribution on unordered three-molecule samples. -/
noncomputable def triplePMF
    (c : Config m n) (h3 : 3 ≤ n) :
    PMF (TripleSample c) :=
  @PMF.uniformOfFintype
    (TripleSample c)
    inferInstance
    (tripleSampleNonempty c h3)

/-- Every unordered sample has mass `1 / C(n,3)`. -/
@[simp] theorem triplePMF_apply
    (c : Config m n) (h3 : 3 ≤ n) (t : TripleSample c) :
    triplePMF c h3 t = (Nat.choose n 3 : ℝ≥0∞)⁻¹ := by
  letI : Nonempty (TripleSample c) := tripleSampleNonempty c h3
  unfold triplePMF
  rw [PMF.uniformOfFintype_apply, card_tripleSample]

/-- Number of sampled molecules whose species label is `i`. -/
def multiplicity
    {c : Config m n} (t : TripleSample c) (i : Species m) : ℕ :=
  (t.1.filter fun u => u.1 = i).card

/-- Positive sample multiplicity implies a positive population coordinate. -/
theorem count_pos_of_multiplicity_pos
    {c : Config m n} (t : TripleSample c) (i : Species m)
    (h : 0 < multiplicity t i) :
    0 < count c i := by
  classical
  unfold multiplicity at h
  obtain ⟨u, hu⟩ := Finset.card_pos.mp h
  have hui : u.1 = i := (Finset.mem_filter.mp hu).2
  have huBound : u.2.val < count c u.1 := u.2.isLt
  have hpos : 0 < count c u.1 :=
    lt_of_le_of_lt (Nat.zero_le _) huBound
  simpa [hui] using hpos

/-- A directed firing label: two sampled molecules have species `winner`, and
one has a distinct species `loser`. -/
def IsFirePair
    {c : Config m n} (t : TripleSample c)
    (p : Species m × Species m) : Prop :=
  p.1 ≠ p.2 ∧
    multiplicity t p.1 = 2 ∧
    multiplicity t p.2 = 1

/-- Proof-carrying directed firing labels for a fixed sample. -/
def FirePair
    {c : Config m n} (t : TripleSample c) :=
  {p : Species m × Species m // IsFirePair t p}

/-- In a firing sample, the winner and loser filters exhaust all three
molecules. -/
theorem fire_filters_cover
    {c : Config m n} (t : TripleSample c)
    {winner loser : Species m}
    (h : IsFirePair t (winner, loser)) :
    t.1.filter (fun u => u.1 = winner) ∪
        t.1.filter (fun u => u.1 = loser) = t.1 := by
  classical
  have hne : winner ≠ loser := h.1
  have hwinner : multiplicity t winner = 2 := h.2.1
  have hloser : multiplicity t loser = 1 := h.2.2
  apply Finset.eq_of_subset_of_card_le
  · intro u hu
    rcases Finset.mem_union.mp hu with hu | hu
    · exact (Finset.mem_filter.mp hu).1
    · exact (Finset.mem_filter.mp hu).1
  · have hd :
        Disjoint
          (t.1.filter (fun u => u.1 = winner))
          (t.1.filter (fun u => u.1 = loser)) := by
      refine Finset.disjoint_left.mpr ?_
      intro u huw hul
      have huw' : u.1 = winner := (Finset.mem_filter.mp huw).2
      have hul' : u.1 = loser := (Finset.mem_filter.mp hul).2
      exact hne (huw'.symm.trans hul')
    have hcard :
        (t.1.filter (fun u => u.1 = winner) ∪
          t.1.filter (fun u => u.1 = loser)).card = 3 := by
      rw [Finset.card_union_of_disjoint hd]
      change multiplicity t winner + multiplicity t loser = 3
      omega
    exact (t.2.trans hcard.symm).le

/-- Every molecule in a firing sample has either the winner or loser species. -/
theorem species_eq_or_eq_of_fire
    {c : Config m n} (t : TripleSample c)
    {winner loser : Species m}
    (h : IsFirePair t (winner, loser))
    {u : Molecule c} (hu : u ∈ t.1) :
    u.1 = winner ∨ u.1 = loser := by
  classical
  have hcover := fire_filters_cover t h
  rw [← hcover] at hu
  rcases Finset.mem_union.mp hu with hu | hu
  · exact Or.inl (Finset.mem_filter.mp hu).2
  · exact Or.inr (Finset.mem_filter.mp hu).2

/-- A three-molecule sample has at most one directed firing pair. -/
theorem isFirePair_unique
    {c : Config m n} (t : TripleSample c)
    {p q : Species m × Species m}
    (hp : IsFirePair t p) (hq : IsFirePair t q) :
    p = q := by
  classical
  rcases p with ⟨winner, loser⟩
  rcases q with ⟨winner', loser'⟩

  have hwpos : 0 < multiplicity t winner' := by
    rw [hq.2.1]
    omega
  have hwcard :
      0 < (t.1.filter fun u => u.1 = winner').card := by
    simpa [multiplicity] using hwpos
  obtain ⟨u, hu⟩ := Finset.card_pos.mp hwcard
  have hus : u ∈ t.1 := (Finset.mem_filter.mp hu).1
  have huw : u.1 = winner' := (Finset.mem_filter.mp hu).2
  have hwcases : winner' = winner ∨ winner' = loser := by
    rcases species_eq_or_eq_of_fire t hp hus with h | h
    · exact Or.inl (huw.symm.trans h)
    · exact Or.inr (huw.symm.trans h)
  have hWinner : winner' = winner := by
    rcases hwcases with h | h
    · exact h
    · have hbad : (2 : ℕ) = 1 := by
        calc
          2 = multiplicity t winner' := hq.2.1.symm
          _ = multiplicity t loser := by rw [h]
          _ = 1 := hp.2.2
      omega

  have hlpos : 0 < multiplicity t loser' := by
    rw [hq.2.2]
    omega
  have hlcard :
      0 < (t.1.filter fun u => u.1 = loser').card := by
    simpa [multiplicity] using hlpos
  obtain ⟨v, hv⟩ := Finset.card_pos.mp hlcard
  have hvs : v ∈ t.1 := (Finset.mem_filter.mp hv).1
  have hvl : v.1 = loser' := (Finset.mem_filter.mp hv).2
  have hlcases : loser' = winner ∨ loser' = loser := by
    rcases species_eq_or_eq_of_fire t hp hvs with h | h
    · exact Or.inl (hvl.symm.trans h)
    · exact Or.inr (hvl.symm.trans h)
  have hLoser : loser' = loser := by
    rcases hlcases with h | h
    · have hbad : (1 : ℕ) = 2 := by
        calc
          1 = multiplicity t loser' := hq.2.2.symm
          _ = multiplicity t winner := by rw [h]
          _ = 2 := hp.2.1
      omega
    · exact h

  exact Prod.ext hWinner.symm hLoser.symm

/-- The proof-carrying directed firing label is a subsingleton. -/
instance firePairSubsingleton
    {c : Config m n} (t : TripleSample c) :
    Subsingleton (FirePair t) where
  allEq p q :=
    Subtype.ext (isFirePair_unique t p.2 q.2)

/-- Classify a sample as inert (`none`) or as its unique directed firing pair. -/
noncomputable def classify
    {c : Config m n} (t : TripleSample c) :
    Option (FirePair t) := by
  classical
  by_cases h : Nonempty (FirePair t)
  · exact some (Classical.choice h)
  · exact none

/-- Every proof-carrying firing pair is the result of classification. -/
@[simp] theorem classify_eq_some_of_fire
    {c : Config m n} (t : TripleSample c)
    (p : FirePair t) :
    classify t = some p := by
  classical
  unfold classify
  rw [dif_pos (show Nonempty (FirePair t) from ⟨p⟩)]
  apply congrArg some
  exact Subsingleton.elim _ _

/-- If no directed firing pair exists, classification returns `none`. -/
theorem classify_eq_none_of_no_fire
    {c : Config m n} (t : TripleSample c)
    (h : ∀ p : Species m × Species m, ¬ IsFirePair t p) :
    classify t = none := by
  classical
  unfold classify
  rw [dif_neg (by
    rintro ⟨p⟩
    exact h p.1 p.2)]

/-- Classification returns `none` exactly for inert samples. -/
@[simp] theorem classify_eq_none_iff
    {c : Config m n} (t : TripleSample c) :
    classify t = none ↔
      ∀ p : Species m × Species m, ¬ IsFirePair t p := by
  constructor
  · intro hc p hp
    let fp : FirePair t := ⟨p, hp⟩
    have hsome := classify_eq_some_of_fire t fp
    rw [hc] at hsome
    cases hsome
  · exact classify_eq_none_of_no_fire t

/-- Any two successful classifications carry the same directed pair. -/
theorem classify_fire_unique
    {c : Config m n} (t : TripleSample c)
    {p q : FirePair t}
    (_hp : classify t = some p)
    (_hq : classify t = some q) :
    p = q :=
  Subsingleton.elim _ _

end Tri.Multi

#print axioms Tri.Multi.card_molecule
#print axioms Tri.Multi.card_tripleSample
#print axioms Tri.Multi.triplePMF_apply
#print axioms Tri.Multi.isFirePair_unique
#print axioms Tri.Multi.classify_eq_none_iff
