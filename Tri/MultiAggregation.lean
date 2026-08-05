/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.MultiKernel
import Tri.Decay
import Tri.Step
import Tri.BiKernel

/-!
# One-step aggregation around a distinguished species

Collapsing all non-`X` labels into one binary label gives an adverse envelope
for the next `X` count on every physical triple sample. It is not a Markov
quotient: reactions among non-`X` species preserve the immediate aggregate
but change its future collision hazard.
-/

namespace Tri.Multi

open scoped BigOperators ENNReal

variable {m n : ℕ}

theorem zSum_eq_of_count_eq
    (c d : Config m n) (X : Species m)
    (hX : count d X = count c X) :
    zSum d X = zSum c X := by
  have hc := count_add_zSum c X
  have hd := count_add_zSum d X
  omega

theorem zSum_succ_eq_of_count_eq_succ
    (c d : Config m n) (X : Species m)
    (hX : count d X = count c X + 1) :
    zSum d X + 1 = zSum c X := by
  have hc := count_add_zSum c X
  have hd := count_add_zSum d X
  omega

theorem zSum_eq_succ_of_count_succ_eq
    (c d : Config m n) (X : Species m)
    (hX : count d X + 1 = count c X) :
    zSum d X = zSum c X + 1 := by
  have hc := count_add_zSum c X
  have hd := count_add_zSum d X
  omega

/-- Binary composition obtained by forgetting distinctions between all
non-`X` species. -/
def collapsedBinaryKind
    {c : Config m n} (X : Species m) (t : TripleSample c) :
    Tri.TripleKind :=
  if multiplicity t X = 3 then .xxx
  else if multiplicity t X = 2 then .xxy
  else if multiplicity t X = 1 then .xyy
  else .yyy

/-- Actual classifier effect on the distinguished aggregate coordinate. -/
noncomputable def semanticAggregateKind
    {c : Config m n} (X : Species m) (t : TripleSample c) :
    Tri.TripleKind :=
  match classify t with
  | none => .xxx
  | some p =>
      if p.1.1 = X then .xxy
      else if p.1.2 = X then .xyy
      else .xxx

def collapsedBinaryNextX
    {c : Config m n} (X : Species m) (t : TripleSample c) : ℕ :=
  Tri.nextX (count c X) (collapsedBinaryKind X t)

noncomputable def semanticAggregateNextX
    {c : Config m n} (X : Species m) (t : TripleSample c) : ℕ :=
  Tri.nextX (count c X) (semanticAggregateKind X t)

theorem multiplicity_eq_zero_of_fire_away
    {c : Config m n} (t : TripleSample c)
    {winner loser X : Species m}
    (hfire : IsFirePair t (winner, loser))
    (hwinner : winner ≠ X) (hloser : loser ≠ X) :
    multiplicity t X = 0 := by
  apply Nat.eq_zero_of_not_pos
  intro hpos
  classical
  unfold multiplicity at hpos
  obtain ⟨u, hu⟩ := Finset.card_pos.mp hpos
  have hut : u ∈ t.1 := (Finset.mem_filter.mp hu).1
  have huX : u.1 = X := (Finset.mem_filter.mp hu).2
  rcases species_eq_or_eq_of_fire t hfire hut with h | h
  · exact hwinner (h.symm.trans huX)
  · exact hloser (h.symm.trans huX)

theorem exists_firePair_of_multiplicity_eq_two
    {c : Config m n} (t : TripleSample c) (X : Species m)
    (hX : multiplicity t X = 2) :
    ∃ Y, Y ≠ X ∧ IsFirePair t (X, Y) := by
  classical
  have hExists : ∃ u ∈ t.1, u.1 ≠ X := by
    by_contra hnone
    have hall : ∀ u, u ∈ t.1 → u.1 = X := by
      intro u hu
      by_contra hne
      exact hnone ⟨u, hu, hne⟩
    have hsub :
        t.1 ⊆ t.1.filter (fun u => u.1 = X) := by
      intro u hu
      exact Finset.mem_filter.mpr ⟨hu, hall u hu⟩
    have hcard := Finset.card_le_card hsub
    change t.1.card ≤ multiplicity t X at hcard
    rw [t.2, hX] at hcard
    omega
  obtain ⟨u, hu, huX⟩ := hExists
  let Y : Species m := u.1
  have hYX : Y ≠ X := huX
  have hYmem : u ∈ t.1.filter (fun v => v.1 = Y) :=
    Finset.mem_filter.mpr ⟨hu, rfl⟩
  have hYpos : 0 < multiplicity t Y := by
    unfold multiplicity
    exact Finset.card_pos.mpr ⟨u, hYmem⟩
  have hdisj :
      Disjoint
        (t.1.filter (fun v => v.1 = X))
        (t.1.filter (fun v => v.1 = Y)) := by
    refine Finset.disjoint_left.mpr ?_
    intro v hvX hvY
    have hvX' : v.1 = X := (Finset.mem_filter.mp hvX).2
    have hvY' : v.1 = Y := (Finset.mem_filter.mp hvY).2
    exact hYX (hvY'.symm.trans hvX')
  have hunionSubset :
      t.1.filter (fun v => v.1 = X) ∪
          t.1.filter (fun v => v.1 = Y) ⊆ t.1 := by
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact (Finset.mem_filter.mp hv).1
    · exact (Finset.mem_filter.mp hv).1
  have hcard := Finset.card_le_card hunionSubset
  rw [Finset.card_union_of_disjoint hdisj] at hcard
  change multiplicity t X + multiplicity t Y ≤ t.1.card at hcard
  rw [hX, t.2] at hcard
  have hYone : multiplicity t Y = 1 := by omega
  exact ⟨Y, hYX, Ne.symm hYX, hX, hYone⟩

theorem classify_ne_none_of_multiplicity_eq_two
    {c : Config m n} (t : TripleSample c) (X : Species m)
    (hX : multiplicity t X = 2) :
    classify t ≠ none := by
  obtain ⟨Y, _hYX, hfire⟩ :=
    exists_firePair_of_multiplicity_eq_two t X hX
  intro hnone
  exact ((classify_eq_none_iff t).1 hnone (X, Y)) hfire

theorem collapsedBinaryNextX_le_semanticAggregateNextX
    {c : Config m n} (X : Species m) (t : TripleSample c) :
    collapsedBinaryNextX X t ≤ semanticAggregateNextX X t := by
  classical
  unfold collapsedBinaryNextX semanticAggregateNextX
  cases hclass : classify t with
  | none =>
      have hm2 : multiplicity t X ≠ 2 := by
        intro hm2
        exact (classify_ne_none_of_multiplicity_eq_two t X hm2) hclass
      by_cases hm3 : multiplicity t X = 3
      · simp [collapsedBinaryKind, semanticAggregateKind,
          hclass, hm3, Tri.nextX]
      · by_cases hm1 : multiplicity t X = 1
        · simp [collapsedBinaryKind, semanticAggregateKind,
            hclass, hm1, Tri.nextX]
        · simp [collapsedBinaryKind, semanticAggregateKind,
            hclass, hm3, hm2, hm1, Tri.nextX]
  | some p =>
      by_cases hwinner : p.1.1 = X
      · have hm2 : multiplicity t X = 2 := by
          simpa [hwinner] using p.2.2.1
        simp [collapsedBinaryKind, semanticAggregateKind,
          hclass, hwinner, hm2, Tri.nextX]
      · by_cases hloser : p.1.2 = X
        · have hm1 : multiplicity t X = 1 := by
            simpa [hloser] using p.2.2.2
          simp [collapsedBinaryKind, semanticAggregateKind,
            hclass, hwinner, hloser, hm1, Tri.nextX]
        · have hm0 : multiplicity t X = 0 :=
            multiplicity_eq_zero_of_fire_away t p.2 hwinner hloser
          simp [collapsedBinaryKind, semanticAggregateKind,
            hclass, hwinner, hloser, hm0, Tri.nextX]

noncomputable def collapsedBinarySampleStep
    (c : Config m n) (X : Species m) (h3 : 3 ≤ n) : PMF ℕ :=
  (triplePMF c h3).map (collapsedBinaryNextX X)

noncomputable def semanticAggregateSampleStep
    (c : Config m n) (X : Species m) (h3 : 3 ≤ n) : PMF ℕ :=
  (triplePMF c h3).map (semanticAggregateNextX X)

theorem collapsedBinarySampleStep_expect_le_semanticAggregateSampleStep
    (c : Config m n) (X : Species m) (h3 : 3 ≤ n)
    (F : ℕ → ℝ≥0∞) (hF : Monotone F) :
    expect (collapsedBinarySampleStep c X h3) F ≤
      expect (semanticAggregateSampleStep c X h3) F := by
  unfold collapsedBinarySampleStep semanticAggregateSampleStep
  rw [expect_map, expect_map]
  unfold expect
  exact ENNReal.tsum_le_tsum fun t => by
    gcongr
    exact hF (collapsedBinaryNextX_le_semanticAggregateNextX X t)

/-! ## Exact aggregate firing weights -/

def directedFireWeight
    (c : Config m n) (winner loser : Species m) : ℕ :=
  Nat.choose (count c winner) 2 * count c loser

def xWinnerFireWeight (c : Config m n) (X : Species m) : ℕ :=
  ∑ Y ∈ Finset.univ.erase X, directedFireWeight c X Y

def minorityCollision (c : Config m n) (X : Species m) : ℕ :=
  ∑ Y ∈ Finset.univ.erase X, Nat.choose (count c Y) 2

def xLoserFireWeight (c : Config m n) (X : Species m) : ℕ :=
  ∑ Y ∈ Finset.univ.erase X, directedFireWeight c Y X

theorem xWinnerFireWeight_eq_binary_up
    (c : Config m n) (X : Species m) :
    xWinnerFireWeight c X =
      Tri.TripleKind.weight (count c X) (zSum c X) .xxy := by
  classical
  unfold xWinnerFireWeight directedFireWeight zSum
  simp only [Tri.TripleKind.weight]
  rw [Finset.mul_sum]

theorem xLoserFireWeight_eq_collision
    (c : Config m n) (X : Species m) :
    xLoserFireWeight c X = count c X * minorityCollision c X := by
  classical
  unfold xLoserFireWeight directedFireWeight minorityCollision
  rw [← Finset.sum_mul]
  ring

theorem sum_choose_two_le_choose_sum
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → ℕ) :
    (∑ i ∈ s, Nat.choose (f i) 2) ≤
      Nat.choose (∑ i ∈ s, f i) 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp only [Finset.sum_insert, ha, not_false_eq_true]
      calc
        Nat.choose (f a) 2 + ∑ i ∈ s, Nat.choose (f i) 2
            ≤ Nat.choose (f a) 2 +
                Nat.choose (∑ i ∈ s, f i) 2 :=
          Nat.add_le_add_left ih _
        _ ≤ Nat.choose (f a + ∑ i ∈ s, f i) 2 := by
          rw [Tri.pair_two_split]
          omega

theorem minorityCollision_le_choose_zSum
    (c : Config m n) (X : Species m) :
    minorityCollision c X ≤ Nat.choose (zSum c X) 2 := by
  classical
  unfold minorityCollision zSum
  exact sum_choose_two_le_choose_sum
    (Finset.univ.erase X) (fun Y => count c Y)

theorem xLoserFireWeight_le_binary_down
    (c : Config m n) (X : Species m) :
    xLoserFireWeight c X ≤
      Tri.TripleKind.weight (count c X) (zSum c X) .xyy := by
  rw [xLoserFireWeight_eq_collision]
  simp only [Tri.TripleKind.weight]
  exact Nat.mul_le_mul_left (count c X)
    (minorityCollision_le_choose_zSum c X)

theorem naiveMarkovQuotient_counterexample :
    5 + 4 + 0 = 9 ∧
      5 + 2 + 2 = 9 ∧
      4 < 5 ∧ 2 < 5 ∧
      4 + 0 = 2 + 2 ∧
      Nat.choose 5 2 * (4 + 0) =
        Nat.choose 5 2 * (2 + 2) ∧
      5 * (Nat.choose 4 2 + Nat.choose 0 2) ≠
        5 * (Nat.choose 2 2 + Nat.choose 2 2) := by
  norm_num [Nat.choose]

end Tri.Multi

#print axioms Tri.Multi.collapsedBinaryNextX_le_semanticAggregateNextX
#print axioms Tri.Multi.collapsedBinarySampleStep_expect_le_semanticAggregateSampleStep
#print axioms Tri.Multi.xWinnerFireWeight_eq_binary_up
#print axioms Tri.Multi.xLoserFireWeight_le_binary_down
#print axioms Tri.Multi.naiveMarkovQuotient_counterexample
