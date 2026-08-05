/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.MultiStep

/-!
# Physical firing fibers for multi-species Tri

This file counts the unordered physical triple samples that realize one fixed
directed reaction. The target count is `C(count winner, 2) * count loser`.
-/

namespace Tri.Multi

open scoped BigOperators ENNReal

variable {m n : ℕ}

/-- Embed a slot of one species into the dependent molecule space. -/
def speciesEmbedding
    (c : Config m n) (i : Species m) :
    Fin (count c i) ↪ Molecule c where
  toFun j := ⟨i, j⟩
  inj' := by
    intro a b h
    cases h
    rfl

/-- All physical molecules of one species. -/
def speciesMolecules
    (c : Config m n) (i : Species m) : Finset (Molecule c) :=
  Finset.univ.map (speciesEmbedding c i)

@[simp] theorem card_speciesMolecules
    (c : Config m n) (i : Species m) :
    (speciesMolecules c i).card = count c i := by
  simp [speciesMolecules]

@[simp] theorem mem_speciesMolecules
    (c : Config m n) (i : Species m) (u : Molecule c) :
    u ∈ speciesMolecules c i ↔ u.1 = i := by
  constructor
  · intro hu
    rw [speciesMolecules, Finset.mem_map] at hu
    obtain ⟨j, _hj, rfl⟩ := hu
    rfl
  · intro hu
    rcases u with ⟨j, slot⟩
    simp only at hu
    subst j
    rw [speciesMolecules, Finset.mem_map]
    exact ⟨slot, Finset.mem_univ _, rfl⟩

/-- A choice of two winner molecules and one loser molecule. -/
abbrev DirectedTripleChoice
    (c : Config m n) (winner loser : Species m) :=
  ↥((speciesMolecules c winner).powersetCard 2) ×
    ↥(speciesMolecules c loser)

noncomputable instance directedTripleChoiceDecidableEq
    (c : Config m n) (winner loser : Species m) :
    DecidableEq (DirectedTripleChoice c winner loser) :=
  Classical.decEq _

@[simp] theorem card_directedTripleChoice
    (c : Config m n) (winner loser : Species m) :
    Fintype.card (DirectedTripleChoice c winner loser) =
      Nat.choose (count c winner) 2 * count c loser := by
  classical
  unfold DirectedTripleChoice
  rw [Fintype.card_prod
    ↥((speciesMolecules c winner).powersetCard 2)
    ↥(speciesMolecules c loser)]
  rw [Fintype.card_coe, Fintype.card_coe,
    Finset.card_powersetCard, card_speciesMolecules,
    card_speciesMolecules]

/-- The three physical molecules selected by a directed choice. -/
noncomputable def directedChoiceFinset
    {c : Config m n} {winner loser : Species m}
    (q : DirectedTripleChoice c winner loser) :
    Finset (Molecule c) :=
  q.1.1 ∪ {q.2.1}

theorem directedChoice_loser_not_mem_pair
    {c : Config m n} {winner loser : Species m}
    (hne : winner ≠ loser)
    (q : DirectedTripleChoice c winner loser) :
    q.2.1 ∉ q.1.1 := by
  intro hu
  have hsubset :=
    (Finset.mem_powersetCard.mp q.1.2).1
  have huWinner :
      q.2.1 ∈ speciesMolecules c winner :=
    hsubset hu
  have hwinner : q.2.1.1 = winner :=
    (mem_speciesMolecules c winner q.2.1).1 huWinner
  have hloser : q.2.1.1 = loser :=
    (mem_speciesMolecules c loser q.2.1).1 q.2.2
  exact hne (hwinner.symm.trans hloser)

@[simp] theorem card_directedChoiceFinset
    {c : Config m n} {winner loser : Species m}
    (hne : winner ≠ loser)
    (q : DirectedTripleChoice c winner loser) :
    (directedChoiceFinset q).card = 3 := by
  have hpairCard :=
    (Finset.mem_powersetCard.mp q.1.2).2
  rw [directedChoiceFinset, Finset.union_singleton,
    Finset.card_insert_of_notMem
      (directedChoice_loser_not_mem_pair hne q),
    hpairCard]

theorem directedChoice_filter_winner
    {c : Config m n} {winner loser : Species m}
    (hne : winner ≠ loser)
    (q : DirectedTripleChoice c winner loser) :
    (directedChoiceFinset q).filter (fun u => u.1 = winner) =
      q.1.1 := by
  classical
  have hsubset :=
    (Finset.mem_powersetCard.mp q.1.2).1
  have hloser : q.2.1.1 = loser :=
    (mem_speciesMolecules c loser q.2.1).1 q.2.2
  ext u
  constructor
  · intro hu
    have hu' := Finset.mem_filter.mp hu
    rcases Finset.mem_union.mp hu'.1 with huPair | huOne
    · exact huPair
    · have hueq : u = q.2.1 := Finset.mem_singleton.mp huOne
      subst u
      exact False.elim (hne (hu'.2.symm.trans hloser))
  · intro hu
    have huWinner :
        u ∈ speciesMolecules c winner :=
      hsubset hu
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_union_left _ hu,
        (mem_speciesMolecules c winner u).1 huWinner⟩

theorem directedChoice_filter_loser
    {c : Config m n} {winner loser : Species m}
    (hne : winner ≠ loser)
    (q : DirectedTripleChoice c winner loser) :
    (directedChoiceFinset q).filter (fun u => u.1 = loser) =
      {q.2.1} := by
  classical
  have hsubset :=
    (Finset.mem_powersetCard.mp q.1.2).1
  have hloser : q.2.1.1 = loser :=
    (mem_speciesMolecules c loser q.2.1).1 q.2.2
  ext u
  constructor
  · intro hu
    have hu' := Finset.mem_filter.mp hu
    rcases Finset.mem_union.mp hu'.1 with huPair | huOne
    · have huWinner :
          u ∈ speciesMolecules c winner :=
        hsubset huPair
      have hwinner : u.1 = winner :=
        (mem_speciesMolecules c winner u).1 huWinner
      exact False.elim (hne (hwinner.symm.trans hu'.2))
    · exact huOne
  · intro hu
    have hueq : u = q.2.1 := Finset.mem_singleton.mp hu
    subst u
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_union_right _ (Finset.mem_singleton_self _),
        hloser⟩

/-- A directed molecular choice determines a physical firing sample. -/
noncomputable def directedChoiceSample
    {c : Config m n} {winner loser : Species m}
    (hne : winner ≠ loser)
    (q : DirectedTripleChoice c winner loser) :
    TripleSample c :=
  ⟨directedChoiceFinset q, card_directedChoiceFinset hne q⟩

theorem directedChoiceSample_isFirePair
    {c : Config m n} {winner loser : Species m}
    (hne : winner ≠ loser)
    (q : DirectedTripleChoice c winner loser) :
    IsFirePair (directedChoiceSample hne q) (winner, loser) := by
  refine ⟨hne, ?_, ?_⟩
  · unfold multiplicity directedChoiceSample
    rw [directedChoice_filter_winner hne q]
    exact (Finset.mem_powersetCard.mp q.1.2).2
  · unfold multiplicity directedChoiceSample
    rw [directedChoice_filter_loser hne q]
    simp

/-- Physical samples realizing one fixed directed reaction. -/
abbrev DirectedFireSample
    (c : Config m n) (winner loser : Species m) :=
  {t : TripleSample c // IsFirePair t (winner, loser)}

noncomputable instance directedFireSampleFintype
    (c : Config m n) (winner loser : Species m) :
    Fintype (DirectedFireSample c winner loser) :=
  Fintype.ofFinite _

/-- The map from two-winner/one-loser choices to firing samples. -/
noncomputable def directedChoiceToFireSample
    {c : Config m n} {winner loser : Species m}
    (hne : winner ≠ loser) :
    DirectedTripleChoice c winner loser →
      DirectedFireSample c winner loser :=
  fun q =>
    ⟨directedChoiceSample hne q,
      directedChoiceSample_isFirePair hne q⟩

theorem directedChoiceToFireSample_injective
    {c : Config m n} {winner loser : Species m}
    (hne : winner ≠ loser) :
    Function.Injective
      (directedChoiceToFireSample (c := c) hne) := by
  intro q q' hqq'
  have hs :
      directedChoiceFinset q = directedChoiceFinset q' :=
    congrArg
      (fun z : DirectedFireSample c winner loser => z.1.1)
      hqq'
  have hwinner :=
    congrArg (fun s : Finset (Molecule c) =>
      s.filter (fun u => u.1 = winner)) hs
  change
    (directedChoiceFinset q).filter (fun u => u.1 = winner) =
      (directedChoiceFinset q').filter (fun u => u.1 = winner)
    at hwinner
  rw [directedChoice_filter_winner hne q,
    directedChoice_filter_winner hne q'] at hwinner
  have hloser :=
    congrArg (fun s : Finset (Molecule c) =>
      s.filter (fun u => u.1 = loser)) hs
  change
    (directedChoiceFinset q).filter (fun u => u.1 = loser) =
      (directedChoiceFinset q').filter (fun u => u.1 = loser)
    at hloser
  rw [directedChoice_filter_loser hne q,
    directedChoice_filter_loser hne q'] at hloser
  apply Prod.ext
  · exact Subtype.ext hwinner
  · exact Subtype.ext (Finset.singleton_inj.mp hloser)

theorem directedChoiceToFireSample_surjective
    {c : Config m n} {winner loser : Species m}
    (hne : winner ≠ loser) :
    Function.Surjective
      (directedChoiceToFireSample (c := c) hne) := by
  intro ft
  let A : Finset (Molecule c) :=
    ft.1.1.filter (fun u => u.1 = winner)
  have hAsubset : A ⊆ speciesMolecules c winner := by
    intro u hu
    have huWinner : u.1 = winner :=
      (Finset.mem_filter.mp hu).2
    exact (mem_speciesMolecules c winner u).2 huWinner
  have hAcard : A.card = 2 := by
    exact ft.2.2.1
  have hAmem :
      A ∈ (speciesMolecules c winner).powersetCard 2 :=
    Finset.mem_powersetCard.mpr ⟨hAsubset, hAcard⟩
  let L : Finset (Molecule c) :=
    ft.1.1.filter (fun u => u.1 = loser)
  have hLcard : L.card = 1 := by
    exact ft.2.2.2
  obtain ⟨u, hu⟩ := Finset.card_eq_one.mp hLcard
  have huL : u ∈ L := by
    rw [hu]
    exact Finset.mem_singleton_self u
  have huLoser : u.1 = loser :=
    (Finset.mem_filter.mp huL).2
  have huMem : u ∈ speciesMolecules c loser :=
    (mem_speciesMolecules c loser u).2 huLoser
  let q : DirectedTripleChoice c winner loser :=
    (⟨A, hAmem⟩, ⟨u, huMem⟩)
  refine ⟨q, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change directedChoiceFinset q = ft.1.1
  unfold directedChoiceFinset
  change A ∪ {u} = ft.1.1
  rw [← hu]
  exact fire_filters_cover ft.1 ft.2

noncomputable def directedChoiceFireEquiv
    {c : Config m n} {winner loser : Species m}
    (hne : winner ≠ loser) :
    DirectedTripleChoice c winner loser ≃
      DirectedFireSample c winner loser :=
  Equiv.ofBijective
    (directedChoiceToFireSample (c := c) hne)
    ⟨directedChoiceToFireSample_injective hne,
      directedChoiceToFireSample_surjective hne⟩

theorem card_directedFireSample
    (c : Config m n) (winner loser : Species m)
    (hne : winner ≠ loser) :
    Fintype.card (DirectedFireSample c winner loser) =
      Nat.choose (count c winner) 2 * count c loser := by
  rw [← card_directedTripleChoice c winner loser]
  exact Fintype.card_congr
    (directedChoiceFireEquiv (c := c) hne).symm

/-- Probability mass of one fixed directed reaction under the physical
uniform triple sampler. -/
noncomputable def directedFireMass
    (c : Config m n) (h3 : 3 ≤ n)
    (winner loser : Species m) : ℝ≥0∞ := by
  classical
  exact ∑' t : TripleSample c,
    if IsFirePair t (winner, loser) then triplePMF c h3 t else 0

theorem directedFireMass_eq
    (c : Config m n) (h3 : 3 ≤ n)
    (winner loser : Species m) (hne : winner ≠ loser) :
    directedFireMass c h3 winner loser =
      (directedFireWeight c winner loser : ℝ≥0∞) /
        (Nat.choose n 3 : ℝ≥0∞) := by
  classical
  unfold directedFireMass
  simp_rw [triplePMF_apply]
  rw [tsum_fintype, ← Finset.sum_filter]
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcard :
      ((Finset.univ.filter fun t : TripleSample c =>
          IsFirePair t (winner, loser)).card) =
        Nat.choose (count c winner) 2 * count c loser := by
    rw [← Fintype.card_subtype
      (fun t : TripleSample c => IsFirePair t (winner, loser))]
    exact card_directedFireSample c winner loser hne
  rw [hcard]
  simp only [directedFireWeight, Nat.cast_mul, div_eq_mul_inv]

/-- Total physical mass of reactions won by the distinguished species. -/
noncomputable def xWinnerFireMass
    (c : Config m n) (h3 : 3 ≤ n) (X : Species m) : ℝ≥0∞ :=
  ∑ Y ∈ Finset.univ.erase X, directedFireMass c h3 X Y

/-- Total physical mass of reactions lost by the distinguished species. -/
noncomputable def xLoserFireMass
    (c : Config m n) (h3 : 3 ≤ n) (X : Species m) : ℝ≥0∞ :=
  ∑ Y ∈ Finset.univ.erase X, directedFireMass c h3 Y X

theorem xWinnerFireMass_eq
    (c : Config m n) (h3 : 3 ≤ n) (X : Species m) :
    xWinnerFireMass c h3 X =
      (xWinnerFireWeight c X : ℝ≥0∞) /
        (Nat.choose n 3 : ℝ≥0∞) := by
  classical
  unfold xWinnerFireMass
  calc
    ∑ Y ∈ Finset.univ.erase X, directedFireMass c h3 X Y =
        ∑ Y ∈ Finset.univ.erase X,
          (directedFireWeight c X Y : ℝ≥0∞) /
            (Nat.choose n 3 : ℝ≥0∞) := by
      apply Finset.sum_congr rfl
      intro Y hY
      rw [directedFireMass_eq c h3 X Y]
      simpa using (Finset.mem_erase.mp hY).1.symm
    _ = (xWinnerFireWeight c X : ℝ≥0∞) /
          (Nat.choose n 3 : ℝ≥0∞) := by
      simp only [div_eq_mul_inv]
      rw [← Finset.sum_mul]
      unfold xWinnerFireWeight
      push_cast
      rfl

theorem xLoserFireMass_eq
    (c : Config m n) (h3 : 3 ≤ n) (X : Species m) :
    xLoserFireMass c h3 X =
      (xLoserFireWeight c X : ℝ≥0∞) /
        (Nat.choose n 3 : ℝ≥0∞) := by
  classical
  unfold xLoserFireMass
  calc
    ∑ Y ∈ Finset.univ.erase X, directedFireMass c h3 Y X =
        ∑ Y ∈ Finset.univ.erase X,
          (directedFireWeight c Y X : ℝ≥0∞) /
            (Nat.choose n 3 : ℝ≥0∞) := by
      apply Finset.sum_congr rfl
      intro Y hY
      rw [directedFireMass_eq c h3 Y X]
      exact (Finset.mem_erase.mp hY).1
    _ = (xLoserFireWeight c X : ℝ≥0∞) /
          (Nat.choose n 3 : ℝ≥0∞) := by
      simp only [div_eq_mul_inv]
      rw [← Finset.sum_mul]
      unfold xLoserFireWeight
      push_cast
      rfl

theorem xLoserFireMass_le_binary
    (c : Config m n) (h3 : 3 ≤ n) (X : Species m) :
    xLoserFireMass c h3 X ≤
      (Tri.TripleKind.weight (count c X) (zSum c X) .xyy : ℝ≥0∞) /
        (Nat.choose n 3 : ℝ≥0∞) := by
  rw [xLoserFireMass_eq]
  apply ENNReal.div_le_div_right
  exact_mod_cast xLoserFireWeight_le_binary_down c X

end Tri.Multi

#print axioms Tri.Multi.card_speciesMolecules
#print axioms Tri.Multi.card_directedTripleChoice
#print axioms Tri.Multi.directedChoiceSample_isFirePair
#print axioms Tri.Multi.card_directedFireSample
#print axioms Tri.Multi.directedFireMass_eq
#print axioms Tri.Multi.xWinnerFireMass_eq
#print axioms Tri.Multi.xLoserFireMass_le_binary
