/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.MultiPairStop
import Mathlib.Algebra.Order.Chebyshev

/-!
# Total productive mass of multi-species Tri

The raw-clock analysis needs the exact probability that one physical
unordered-triple interaction fires.  Uniqueness of the firing classifier makes
the productive event a disjoint union of all ordered winner/loser fibers.
-/

namespace Tri.Multi

open scoped BigOperators ENNReal

variable {m n : ℕ}

/-- A physical sample is productive exactly when classification finds a
directed firing pair. -/
def IsProductiveSample
    {c : Config m n} (t : TripleSample c) : Prop :=
  classify t ≠ none

noncomputable instance isProductiveSampleDecidable
    {c : Config m n} (t : TripleSample c) :
    Decidable (IsProductiveSample t) := by
  unfold IsProductiveSample
  infer_instance

/-- Total probability mass of productive physical samples. -/
noncomputable def productiveMass
    (c : Config m n) (h3 : 3 ≤ n) : ℝ≥0∞ := by
  classical
  exact ∑' t : TripleSample c,
    if IsProductiveSample t then triplePMF c h3 t else 0

/-- Indicator mass of the productive-sample predicate. -/
noncomputable def productiveIndicator
    {c : Config m n} (t : TripleSample c) (q : ℝ≥0∞) : ℝ≥0∞ := by
  classical
  exact if IsProductiveSample t then q else 0

/-- Total ordered-fiber numerator of productive samples. -/
def productiveWeight (c : Config m n) : ℕ :=
  ∑ winner : Species m,
    ∑ loser ∈ Finset.univ.erase winner,
      directedFireWeight c winner loser

/-- Productive reactions whose winner or loser is the distinguished species. -/
def xInvolvingWeight (c : Config m n) (X : Species m) : ℕ :=
  xWinnerFireWeight c X + xLoserFireWeight c X

/-- Exact coordinate formula for productive reactions involving `X`. -/
theorem xInvolvingWeight_eq
    (c : Config m n) (X : Species m) :
    xInvolvingWeight c X =
      Nat.choose (count c X) 2 * zSum c X +
        count c X * minorityCollision c X := by
  unfold xInvolvingWeight
  rw [xWinnerFireWeight_eq_binary_up,
    xLoserFireWeight_eq_collision]
  rfl

/-- The ordered-fiber numerator can be collected by winner species. -/
theorem productiveWeight_eq_sum_choose_mul_zSum
    (c : Config m n) :
    productiveWeight c =
      ∑ winner : Species m,
        Nat.choose (count c winner) 2 * zSum c winner := by
  classical
  unfold productiveWeight zSum directedFireWeight
  apply Finset.sum_congr rfl
  intro winner _hwinner
  rw [Finset.mul_sum]

/-- Equivalent coordinate formula for the productive numerator. -/
theorem productiveWeight_eq_sum_choose_mul_complement
    (c : Config m n) :
    productiveWeight c =
      ∑ winner : Species m,
        Nat.choose (count c winner) 2 * (n - count c winner) := by
  rw [productiveWeight_eq_sum_choose_mul_zSum]
  apply Finset.sum_congr rfl
  intro winner _hwinner
  have htotal := count_add_zSum c winner
  congr 1
  omega

/-- Among productive reactions, the cross-multiplied probability of involving
`X` is at least `count X / n`.  This is the counting inequality used in the
paper's proper-stage argument. -/
theorem count_mul_productiveWeight_le_population_mul_xInvolvingWeight
    (c : Config m n) (X : Species m) :
    count c X * productiveWeight c ≤
      n * xInvolvingWeight c X := by
  classical
  rw [productiveWeight_eq_sum_choose_mul_complement,
    xInvolvingWeight_eq]
  have hsplit :
      (∑ i : Species m,
          Nat.choose (count c i) 2 * (n - count c i)) =
        Nat.choose (count c X) 2 * (n - count c X) +
          ∑ i ∈ Finset.univ.erase X,
            Nat.choose (count c i) 2 * (n - count c i) := by
    calc
      (∑ i : Species m,
          Nat.choose (count c i) 2 * (n - count c i)) =
          (∑ i ∈ Finset.univ.erase X,
            Nat.choose (count c i) 2 * (n - count c i)) +
            Nat.choose (count c X) 2 * (n - count c X) :=
        (Finset.sum_erase_add _ _ (Finset.mem_univ X)).symm
      _ = Nat.choose (count c X) 2 * (n - count c X) +
          ∑ i ∈ Finset.univ.erase X,
            Nat.choose (count c i) 2 * (n - count c i) := by
        rw [Nat.add_comm]
  rw [hsplit, Nat.mul_add, Nat.mul_add]
  apply Nat.add_le_add
  · have hx : count c X ≤ n := by
      have htotal := count_add_zSum c X
      omega
    gcongr
    have htotal := count_add_zSum c X
    omega
  · calc
      count c X *
          (∑ i ∈ Finset.univ.erase X,
            Nat.choose (count c i) 2 * (n - count c i)) =
          ∑ i ∈ Finset.univ.erase X,
            count c X *
              (Nat.choose (count c i) 2 * (n - count c i)) := by
        rw [Finset.mul_sum]
      _ ≤ ∑ i ∈ Finset.univ.erase X,
          n * (count c X * Nat.choose (count c i) 2) := by
        apply Finset.sum_le_sum
        intro i _hi
        have hi : n - count c i ≤ n := Nat.sub_le _ _
        calc
          count c X *
              (Nat.choose (count c i) 2 * (n - count c i)) =
              (count c X * Nat.choose (count c i) 2) *
                (n - count c i) := by ring
          _ ≤ (count c X * Nat.choose (count c i) 2) * n :=
            Nat.mul_le_mul_left _ hi
          _ = n * (count c X * Nat.choose (count c i) 2) := by
            ring
      _ = n * (count c X * minorityCollision c X) := by
        unfold minorityCollision
        rw [Finset.mul_sum, Finset.mul_sum]

/-- Exact relation between the coordinate square sum and the number of
same-species unordered pairs. -/
theorem sum_count_sq_eq_two_choose_add
    (c : Config m n) :
    (∑ i : Species m, count c i ^ 2) =
      2 * (∑ i : Species m, Nat.choose (count c i) 2) + n := by
  calc
    (∑ i : Species m, count c i ^ 2) =
        ∑ i : Species m,
          (2 * Nat.choose (count c i) 2 + count c i) := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [two_mul_choose_two]
      cases hcount : count c i with
      | zero => simp
      | succ k =>
          simp
          ring
    _ = 2 * (∑ i : Species m, Nat.choose (count c i) 2) +
          ∑ i : Species m, count c i := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ = 2 * (∑ i : Species m, Nat.choose (count c i) 2) + n := by
      rw [sum_count]

/-- Cauchy-Schwarz lower bound on the total number of same-species pairs, in
division-free natural arithmetic. -/
theorem population_sq_le_four_mul_species_mul_choose_sum
    (c : Config m n) (hnm : 2 * m ≤ n) :
    n ^ 2 ≤
      4 * m * (∑ i : Species m, Nat.choose (count c i) 2) := by
  let S := ∑ i : Species m, Nat.choose (count c i) 2
  have hcs :
      n ^ 2 ≤ m * (∑ i : Species m, count c i ^ 2) := by
    have h :=
      sq_sum_le_card_mul_sum_sq
        (s := (Finset.univ : Finset (Species m)))
        (f := fun i => count c i)
    simpa [sum_count] using h
  have hid : (∑ i : Species m, count c i ^ 2) = 2 * S + n := by
    exact sum_count_sq_eq_two_choose_add c
  rw [hid] at hcs
  have hmn : 2 * (m * n) ≤ n ^ 2 := by
    calc
      2 * (m * n) = (2 * m) * n := by ring
      _ ≤ n * n := Nat.mul_le_mul_right n hnm
      _ = n ^ 2 := by ring
  have hdouble : 2 * n ^ 2 ≤
      4 * m * S + 2 * (m * n) := by
    calc
      2 * n ^ 2 ≤ 2 * (m * (2 * S + n)) :=
        Nat.mul_le_mul_left 2 hcs
      _ = 4 * m * S + 2 * (m * n) := by ring
  have hfinal : n ^ 2 + n ^ 2 ≤ 4 * m * S + n ^ 2 := by
    calc
      n ^ 2 + n ^ 2 = 2 * n ^ 2 := by ring
      _ ≤ 4 * m * S + 2 * (m * n) := hdouble
      _ ≤ 4 * m * S + n ^ 2 := Nat.add_le_add_left hmn _
  have hcancel : n ^ 2 + n ^ 2 ≤ n ^ 2 + 4 * m * S := by
    simpa [Nat.add_comm] using hfinal
  exact Nat.le_of_add_le_add_left hcancel

/-- Cauchy--Schwarz pair-count lower bound on an arbitrary finite set of
coordinates.  The factor four avoids division and the small-population
exception where every coordinate could be zero or one. -/
theorem sum_sq_le_four_card_mul_choose_sum
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → ℕ)
    (hlarge : 2 * s.card ≤ ∑ i ∈ s, f i) :
    (∑ i ∈ s, f i) ^ 2 ≤
      4 * s.card * ∑ i ∈ s, Nat.choose (f i) 2 := by
  let A := ∑ i ∈ s, f i
  let S := ∑ i ∈ s, Nat.choose (f i) 2
  have hid :
      (∑ i ∈ s, f i ^ 2) = 2 * S + A := by
    calc
      (∑ i ∈ s, f i ^ 2) =
          ∑ i ∈ s, (2 * Nat.choose (f i) 2 + f i) := by
        apply Finset.sum_congr rfl
        intro i _hi
        rw [two_mul_choose_two]
        cases hfi : f i with
        | zero => simp
        | succ k =>
            simp
            ring
      _ = 2 * S + A := by
        dsimp only [S, A]
        rw [Finset.sum_add_distrib, Finset.mul_sum]
  have hcs :
      A ^ 2 ≤ s.card * (∑ i ∈ s, f i ^ 2) := by
    dsimp only [A]
    exact sq_sum_le_card_mul_sum_sq
  rw [hid] at hcs
  have hsmall : 2 * (s.card * A) ≤ A ^ 2 := by
    calc
      2 * (s.card * A) = (2 * s.card) * A := by ring
      _ ≤ A * A := Nat.mul_le_mul_right A hlarge
      _ = A ^ 2 := by ring
  have hdouble :
      2 * A ^ 2 ≤ 4 * s.card * S + 2 * (s.card * A) := by
    calc
      2 * A ^ 2 ≤ 2 * (s.card * (2 * S + A)) :=
        Nat.mul_le_mul_left 2 hcs
      _ = 4 * s.card * S + 2 * (s.card * A) := by ring
  have hfinal :
      A ^ 2 + A ^ 2 ≤ 4 * s.card * S + A ^ 2 := by
    calc
      A ^ 2 + A ^ 2 = 2 * A ^ 2 := by ring
      _ ≤ 4 * s.card * S + 2 * (s.card * A) := hdouble
      _ ≤ 4 * s.card * S + A ^ 2 :=
        Nat.add_le_add_left hsmall _
  have hcancel :
      A ^ 2 + A ^ 2 ≤ A ^ 2 + 4 * s.card * S := by
    simpa [Nat.add_comm] using hfinal
  exact Nat.le_of_add_le_add_left hcancel

/-- In the phase-0 region where the aggregate minority is at least half the
population, the productive numerator has the paper's `Ω(n³/m)` floor. -/
theorem population_cube_le_eight_mul_species_mul_productiveWeight
    (c : Config m n) (X : Species m)
    (hmax : IsMaxSpecies c X)
    (hminor : n ≤ 2 * zSum c X)
    (hnm : 2 * m ≤ n) :
    n ^ 3 ≤ 8 * m * productiveWeight c := by
  let S := ∑ i : Species m, Nat.choose (count c i) 2
  have hS : n ^ 2 ≤ 4 * m * S :=
    population_sq_le_four_mul_species_mul_choose_sum c hnm
  have hcomp :
      zSum c X * S ≤ productiveWeight c := by
    rw [productiveWeight_eq_sum_choose_mul_complement]
    calc
      zSum c X * S =
          S * zSum c X := Nat.mul_comm _ _
      _ =
          ∑ i : Species m,
            Nat.choose (count c i) 2 * zSum c X := by
        rw [Finset.sum_mul]
      _ ≤ ∑ i : Species m,
          Nat.choose (count c i) 2 * (n - count c i) := by
        apply Finset.sum_le_sum
        intro i _hi
        have hix : count c i ≤ count c X := hmax i
        have htotal := count_add_zSum c X
        gcongr
        omega
  have hnS : n * S ≤ 2 * (zSum c X * S) := by
    calc
      n * S ≤ (2 * zSum c X) * S :=
        Nat.mul_le_mul_right S hminor
      _ = 2 * (zSum c X * S) := by ring
  calc
    n ^ 3 = n * n ^ 2 := by ring
    _ ≤ n * (4 * m * S) := Nat.mul_le_mul_left n hS
    _ = 4 * m * (n * S) := by ring
    _ ≤ 4 * m * (2 * (zSum c X * S)) :=
      Nat.mul_le_mul_left (4 * m) hnS
    _ = 8 * m * (zSum c X * S) := by ring
    _ ≤ 8 * m * productiveWeight c :=
      Nat.mul_le_mul_left (8 * m) hcomp

/-- The total number of physical samples is bounded by the scaled productive
numerator in the phase-0 region. -/
theorem choose_three_le_eight_mul_species_mul_productiveWeight
    (c : Config m n) (X : Species m)
    (hmax : IsMaxSpecies c X)
    (hminor : n ≤ 2 * zSum c X)
    (hnm : 2 * m ≤ n) :
    Nat.choose n 3 ≤ 8 * m * productiveWeight c :=
  (Nat.choose_le_pow n 3).trans
    (population_cube_le_eight_mul_species_mul_productiveWeight
      c X hmax hminor hnm)

/-- On the paper's full phase-0 region `x ≤ zSum + D`, a modest size
assumption on `D` and the number of species still gives a uniform
`Ω(n³/m)` productive numerator. -/
theorem population_cube_le_108_mul_species_mul_productiveWeight
    (c : Config m n) (X : Species m) (D : ℕ)
    (hmax : IsMaxSpecies c X)
    (hphase : count c X ≤ zSum c X + D)
    (hD : 3 * D ≤ n)
    (hnm : 6 * m ≤ n) :
    n ^ 3 ≤ 108 * m * productiveWeight c := by
  let s : Finset (Species m) := Finset.univ.erase X
  let Z := zSum c X
  let S := ∑ i ∈ s, Nat.choose (count c i) 2
  have hnZ : n ≤ 3 * Z := by
    have htotal := count_add_zSum c X
    dsimp only [Z]
    omega
  have hcard : s.card = m - 1 := by
    dsimp only [s]
    simp
  have hlarge : 2 * s.card ≤ Z := by
    have h2m : 2 * m ≤ Z := by omega
    rw [hcard]
    omega
  have hZS : Z ^ 2 ≤ 4 * s.card * S := by
    have h :=
      sum_sq_le_four_card_mul_choose_sum
        s (fun i => count c i) hlarge
    simpa only [s, S, Z, zSum] using h
  have hcomp : Z * S ≤ productiveWeight c := by
    rw [productiveWeight_eq_sum_choose_mul_complement]
    calc
      Z * S = S * Z := Nat.mul_comm _ _
      _ = ∑ i ∈ s,
            Nat.choose (count c i) 2 * Z := by
        dsimp only [S]
        rw [Finset.sum_mul]
      _ ≤ ∑ i ∈ s,
          Nat.choose (count c i) 2 * (n - count c i) := by
        apply Finset.sum_le_sum
        intro i hi
        have hix : count c i ≤ count c X := hmax i
        have htotal := count_add_zSum c X
        have hzle : Z ≤ n - count c i := by
          dsimp only [Z]
          omega
        exact Nat.mul_le_mul_left _ hzle
      _ ≤ ∑ i : Species m,
          Nat.choose (count c i) 2 * (n - count c i) := by
        dsimp only [s]
        exact Finset.sum_le_sum_of_subset (Finset.erase_subset X _)
  have hZcube : Z ^ 3 ≤ 4 * m * productiveWeight c := by
    calc
      Z ^ 3 = Z * Z ^ 2 := by ring
      _ ≤ Z * (4 * s.card * S) :=
        Nat.mul_le_mul_left Z hZS
      _ = 4 * s.card * (Z * S) := by ring
      _ ≤ 4 * s.card * productiveWeight c :=
        Nat.mul_le_mul_left (4 * s.card) hcomp
      _ ≤ 4 * m * productiveWeight c := by
        gcongr
        simpa using Finset.card_le_univ s
  calc
    n ^ 3 ≤ (3 * Z) ^ 3 := Nat.pow_le_pow_left hnZ 3
    _ = 27 * Z ^ 3 := by ring
    _ ≤ 27 * (4 * m * productiveWeight c) :=
      Nat.mul_le_mul_left 27 hZcube
    _ = 108 * m * productiveWeight c := by ring

/-- The physical sample count is bounded by the full phase-0 productive
numerator with the same conservative constant. -/
theorem choose_three_le_108_mul_species_mul_productiveWeight
    (c : Config m n) (X : Species m) (D : ℕ)
    (hmax : IsMaxSpecies c X)
    (hphase : count c X ≤ zSum c X + D)
    (hD : 3 * D ≤ n)
    (hnm : 6 * m ≤ n) :
    Nat.choose n 3 ≤ 108 * m * productiveWeight c :=
  (Nat.choose_le_pow n 3).trans
    (population_cube_le_108_mul_species_mul_productiveWeight
      c X D hmax hphase hD hnm)

/-- Pointwise disjoint partition of one productive sample among all ordered
winner/loser fibers. -/
theorem directedFireIndicator_sum_eq_productive
    {c : Config m n} (t : TripleSample c) (q : ℝ≥0∞) :
    (∑ winner : Species m,
      ∑ loser ∈ Finset.univ.erase winner,
        fireIndicator t (winner, loser) q) =
      productiveIndicator t q := by
  classical
  cases hclass : classify t with
  | none =>
      have hnofire := (classify_eq_none_iff t).mp hclass
      have hprod : ¬ IsProductiveSample t := by
        simp [IsProductiveSample, hclass]
      rw [show productiveIndicator t q = 0 by
        simp [productiveIndicator, hprod]]
      apply Finset.sum_eq_zero
      intro winner _hwinner
      apply Finset.sum_eq_zero
      intro loser _hloser
      simp [fireIndicator, hnofire (winner, loser)]
  | some p =>
      have hprod : IsProductiveSample t := by
        simp [IsProductiveSample, hclass]
      rw [show productiveIndicator t q = q by
        simp [productiveIndicator, hprod]]
      let winner := p.1.1
      let loser := p.1.2
      have hloserMem :
          loser ∈ (Finset.univ.erase winner : Finset (Species m)) := by
        exact Finset.mem_erase.mpr
          ⟨Ne.symm p.2.1, Finset.mem_univ loser⟩
      calc
        (∑ W : Species m,
          ∑ L ∈ Finset.univ.erase W,
            fireIndicator t (W, L) q) =
          ∑ L ∈ Finset.univ.erase winner,
            fireIndicator t (winner, L) q := by
            apply Finset.sum_eq_single_of_mem winner
              (Finset.mem_univ winner)
            intro W _hW hW
            apply Finset.sum_eq_zero
            intro L hL
            have hnot : ¬ IsFirePair t (W, L) := by
              intro hfire
              have hp := isFirePair_unique t p.2 hfire
              have hw : winner = W := congrArg Prod.fst hp
              exact hW hw.symm
            simp [fireIndicator, hnot]
        _ = fireIndicator t (winner, loser) q := by
          apply Finset.sum_eq_single_of_mem loser hloserMem
          intro L _hL hL
          have hnot : ¬ IsFirePair t (winner, L) := by
            intro hfire
            have hp := isFirePair_unique t p.2 hfire
            have hl : loser = L := congrArg Prod.snd hp
            exact hL hl.symm
          simp [fireIndicator, hnot]
        _ = q := by
          have hp : IsFirePair t (winner, loser) := by
            simpa [winner, loser] using p.2
          simp [fireIndicator, hp]

/-- Productive physical mass is the disjoint sum of every directed reaction
fiber mass. -/
theorem productiveMass_eq_directedFireMass_sum
    (c : Config m n) (h3 : 3 ≤ n) :
    productiveMass c h3 =
      ∑ winner : Species m,
        ∑ loser ∈ Finset.univ.erase winner,
          directedFireMass c h3 winner loser := by
  classical
  unfold productiveMass directedFireMass
  simp only [tsum_fintype]
  symm
  calc
    (∑ winner : Species m,
      ∑ loser ∈ Finset.univ.erase winner,
        ∑ t : TripleSample c,
          if IsFirePair t (winner, loser) then triplePMF c h3 t else 0) =
      ∑ winner : Species m,
        ∑ loser ∈ Finset.univ.erase winner,
          ∑ t : TripleSample c,
            fireIndicator t (winner, loser) (triplePMF c h3 t) := by
        apply Finset.sum_congr rfl
        intro winner _hwinner
        apply Finset.sum_congr rfl
        intro loser _hloser
        apply Finset.sum_congr rfl
        intro t _ht
        simp [fireIndicator]
    _ = ∑ t : TripleSample c,
        ∑ winner : Species m,
          ∑ loser ∈ Finset.univ.erase winner,
            fireIndicator t (winner, loser) (triplePMF c h3 t) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro t _ht
      rw [Finset.sum_comm]
    _ = ∑ t : TripleSample c,
        if IsProductiveSample t then triplePMF c h3 t else 0 := by
      apply Finset.sum_congr rfl
      intro t _ht
      simpa [productiveIndicator] using
        directedFireIndicator_sum_eq_productive t (triplePMF c h3 t)

/-- Exact normalized formula for the total productive probability. -/
theorem productiveMass_eq
    (c : Config m n) (h3 : 3 ≤ n) :
    productiveMass c h3 =
      (productiveWeight c : ℝ≥0∞) /
        (Nat.choose n 3 : ℝ≥0∞) := by
  rw [productiveMass_eq_directedFireMass_sum]
  unfold productiveWeight
  calc
    (∑ winner : Species m,
      ∑ loser ∈ Finset.univ.erase winner,
        directedFireMass c h3 winner loser) =
      ∑ winner : Species m,
        ∑ loser ∈ Finset.univ.erase winner,
          (directedFireWeight c winner loser : ℝ≥0∞) /
            (Nat.choose n 3 : ℝ≥0∞) := by
        apply Finset.sum_congr rfl
        intro winner _hwinner
        apply Finset.sum_congr rfl
        intro loser hloser
        rw [directedFireMass_eq c h3 winner loser]
        exact (Finset.mem_erase.mp hloser).1.symm
    _ = ((∑ winner : Species m,
        ∑ loser ∈ Finset.univ.erase winner,
          directedFireWeight c winner loser : ℕ) : ℝ≥0∞) /
          (Nat.choose n 3 : ℝ≥0∞) := by
      simp only [div_eq_mul_inv, ← Finset.sum_mul]
      push_cast
      rfl

/-- Physical productive mass of reactions whose winner or loser is `X`. -/
noncomputable def xInvolvingMass
    (c : Config m n) (h3 : 3 ≤ n) (X : Species m) : ℝ≥0∞ :=
  xWinnerFireMass c h3 X + xLoserFireMass c h3 X

/-- Exact normalized formula for productive reactions involving `X`. -/
theorem xInvolvingMass_eq
    (c : Config m n) (h3 : 3 ≤ n) (X : Species m) :
    xInvolvingMass c h3 X =
      (xInvolvingWeight c X : ℝ≥0∞) /
        (Nat.choose n 3 : ℝ≥0∞) := by
  unfold xInvolvingMass xInvolvingWeight
  rw [xWinnerFireMass_eq, xLoserFireMass_eq]
  simp only [div_eq_mul_inv]
  push_cast
  ring

/-- Probability-level cross-multiplied lower bound for a productive reaction
to involve `X`. -/
theorem count_mul_productiveMass_le_population_mul_xInvolvingMass
    (c : Config m n) (h3 : 3 ≤ n) (X : Species m) :
    (count c X : ℝ≥0∞) * productiveMass c h3 ≤
      (n : ℝ≥0∞) * xInvolvingMass c h3 X := by
  rw [productiveMass_eq, xInvolvingMass_eq,
    ← mul_div_assoc, ← mul_div_assoc]
  apply ENNReal.div_le_div_right
  exact_mod_cast
    count_mul_productiveWeight_le_population_mul_xInvolvingWeight c X

/-- If the current `X` population is at least half its stage-start value `x0`,
then a productive reaction involves `X` with cross-multiplied probability at
least `x0/(2n)`. -/
theorem initialCount_mul_productiveMass_le_two_population_mul_xInvolvingMass
    (c : Config m n) (h3 : 3 ≤ n) (X : Species m) (x0 : ℕ)
    (hx : x0 ≤ 2 * count c X) :
    (x0 : ℝ≥0∞) * productiveMass c h3 ≤
      (2 * n : ℕ) * xInvolvingMass c h3 X := by
  calc
    (x0 : ℝ≥0∞) * productiveMass c h3 ≤
        (2 * count c X : ℕ) * productiveMass c h3 := by
      gcongr
    _ = 2 * ((count c X : ℝ≥0∞) * productiveMass c h3) := by
      push_cast
      ring
    _ ≤ 2 * ((n : ℝ≥0∞) * xInvolvingMass c h3 X) := by
      exact mul_le_mul_right
        (count_mul_productiveMass_le_population_mul_xInvolvingMass
          c h3 X) 2
    _ = (2 * n : ℕ) * xInvolvingMass c h3 X := by
      push_cast
      ring

/-- In the phase-0 region, one physical interaction is productive with
probability at least `1 / (8m)`. -/
theorem one_div_eight_species_le_productiveMass
    (c : Config m n) (X : Species m) (h3 : 3 ≤ n)
    (hmax : IsMaxSpecies c X)
    (hminor : n ≤ 2 * zSum c X)
    (hnm : 2 * m ≤ n) :
    (1 : ℝ≥0∞) / (8 * m : ℕ) ≤ productiveMass c h3 := by
  have hcrossNat :
      Nat.choose n 3 ≤ 8 * m * productiveWeight c :=
    choose_three_le_eight_mul_species_mul_productiveWeight
      c X hmax hminor hnm
  have hcross :
      (Nat.choose n 3 : ℝ≥0∞) ≤
        (8 * m : ℕ) * (productiveWeight c : ℝ≥0∞) := by
    exact_mod_cast hcrossNat
  have hm : 0 < m := Nat.zero_lt_of_lt X.isLt
  have hden0 : ((8 * m : ℕ) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast
      Nat.mul_ne_zero (by norm_num) (Nat.ne_of_gt hm)
  have hdentop : ((8 * m : ℕ) : ℝ≥0∞) ≠ ∞ :=
    ENNReal.coe_ne_top
  have hdiv :
      (Nat.choose n 3 : ℝ≥0∞) / (8 * m : ℕ) ≤
        (productiveWeight c : ℝ≥0∞) := by
    rw [ENNReal.div_le_iff_le_mul (Or.inl hden0) (Or.inl hdentop)]
    simpa [mul_comm] using hcross
  rw [productiveMass_eq]
  apply (ENNReal.le_div_iff_mul_le
    (Or.inl (by
      exact_mod_cast Nat.ne_of_gt (Nat.choose_pos h3)))
    (Or.inl ENNReal.coe_ne_top)).2
  simpa [div_eq_mul_inv, mul_comm] using hdiv

/-- On the paper's full phase-0 region, one physical interaction is productive
with probability at least `1/(108m)`. -/
theorem one_div_108_species_le_productiveMass
    (c : Config m n) (X : Species m) (D : ℕ) (h3 : 3 ≤ n)
    (hmax : IsMaxSpecies c X)
    (hphase : count c X ≤ zSum c X + D)
    (hD : 3 * D ≤ n)
    (hnm : 6 * m ≤ n) :
    (1 : ℝ≥0∞) / (108 * m : ℕ) ≤ productiveMass c h3 := by
  have hcrossNat :
      Nat.choose n 3 ≤ 108 * m * productiveWeight c :=
    choose_three_le_108_mul_species_mul_productiveWeight
      c X D hmax hphase hD hnm
  have hcross :
      (Nat.choose n 3 : ℝ≥0∞) ≤
        (108 * m : ℕ) * (productiveWeight c : ℝ≥0∞) := by
    exact_mod_cast hcrossNat
  have hm : 0 < m := Nat.zero_lt_of_lt X.isLt
  have hden0 : ((108 * m : ℕ) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast
      Nat.mul_ne_zero (by norm_num) (Nat.ne_of_gt hm)
  have hdentop : ((108 * m : ℕ) : ℝ≥0∞) ≠ ∞ :=
    ENNReal.coe_ne_top
  have hdiv :
      (Nat.choose n 3 : ℝ≥0∞) / (108 * m : ℕ) ≤
        (productiveWeight c : ℝ≥0∞) := by
    rw [ENNReal.div_le_iff_le_mul (Or.inl hden0) (Or.inl hdentop)]
    simpa [mul_comm] using hcross
  rw [productiveMass_eq]
  apply (ENNReal.le_div_iff_mul_le
    (Or.inl (by
      exact_mod_cast Nat.ne_of_gt (Nat.choose_pos h3)))
    (Or.inl ENNReal.coe_ne_top)).2
  simpa [div_eq_mul_inv, mul_comm] using hdiv

end Tri.Multi

#print axioms Tri.Multi.directedFireIndicator_sum_eq_productive
#print axioms Tri.Multi.productiveWeight_eq_sum_choose_mul_complement
#print axioms Tri.Multi.productiveMass_eq_directedFireMass_sum
#print axioms Tri.Multi.productiveMass_eq
#print axioms Tri.Multi.count_mul_productiveMass_le_population_mul_xInvolvingMass
#print axioms Tri.Multi.initialCount_mul_productiveMass_le_two_population_mul_xInvolvingMass
#print axioms Tri.Multi.one_div_eight_species_le_productiveMass
#print axioms Tri.Multi.one_div_108_species_le_productiveMass
