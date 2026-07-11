/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Random Scheduler

Uniform random pair selection over ordered pairs of distinct agents.
This is the standard population-protocol probabilistic model: at each
step, the scheduler picks a pair `(i, j)` uniformly from
`{ (i, j) : Fin n × Fin n // i ≠ j }`.

This file is a **scaffold**.  It states the intended signatures and
provides the simplest viable definitions.  See `docs/TIME_BOUND_PLAN.md`
for the design rationale and the open choice between `PMF`-based and
`Kernel`-based foundations.

This module lives outside the root import graph
(`SSExactMajority.lean` does not import it) until the time-bound layer
is closed.
-/

import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.Distributions.Uniform
import Ripple.PopulationProtocol.Majority.SSEM.Defs.Execution

namespace SSEM
namespace Probability

open scoped BigOperators
open PMF

variable {Q X Y : Type*} {n : ℕ}

/-- Ordered pairs of distinct agents on `n` positions. -/
def OffDiagonalPairs (n : ℕ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun p : Fin n × Fin n => p.1 ≠ p.2)

/-- Membership in the off-diagonal pair set. -/
theorem mem_offDiagonalPairs (n : ℕ) (p : Fin n × Fin n) :
    p ∈ OffDiagonalPairs n ↔ p.1 ≠ p.2 := by
  simp [OffDiagonalPairs]

/-- For `n ≥ 2`, the off-diagonal pair set is nonempty. -/
theorem offDiagonalPairs_nonempty (n : ℕ) (hn : 2 ≤ n) :
    (OffDiagonalPairs n).Nonempty := by
  refine ⟨⟨⟨0, by omega⟩, ⟨1, by omega⟩⟩, ?_⟩
  simp [OffDiagonalPairs, Fin.ext_iff]

/-- Cardinality of the off-diagonal pair set on `n` positions. -/
theorem offDiagonalPairs_card (n : ℕ) :
    (OffDiagonalPairs n).card = n * (n - 1) := by
  classical
  let diag : Finset (Fin n × Fin n) :=
    (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1 = p.2)
  have hdiag_eq :
      diag = (Finset.univ : Finset (Fin n)).image (fun i => (i, i)) := by
    ext p
    rcases p with ⟨i, j⟩
    simp [diag]
  have hdiag_card : diag.card = n := by
    rw [hdiag_eq, Finset.card_image_of_injective]
    · simp
    · intro a b h
      exact congrArg Prod.fst h
  have hsplit :=
    Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin n × Fin n)))
      (p := fun p : Fin n × Fin n => p.1 = p.2)
  have hoff :
      (OffDiagonalPairs n).card + diag.card = n * n := by
    simpa [OffDiagonalPairs, diag, Finset.card_product, Finset.card_fin,
      Nat.add_comm] using hsplit
  have harith : n * (n - 1) + n = n * n := by
    cases n with
    | zero => simp
    | succ k =>
        simp [Nat.succ_mul, Nat.mul_succ, Nat.add_comm, Nat.add_left_comm,
          Nat.add_assoc]
  rw [hdiag_card] at hoff
  exact Nat.add_right_cancel (by rw [hoff, harith])

/-- The uniform random scheduler: pick an ordered pair uniformly from
the `n(n-1)` off-diagonal pairs. -/
noncomputable def uniformPair (n : ℕ) (hn : 2 ≤ n) :
    PMF (Fin n × Fin n) :=
  PMF.uniformOfFinset (OffDiagonalPairs n) (offDiagonalPairs_nonempty n hn)

/-- A fixed ordered off-diagonal pair has probability
`1 / (n * (n - 1))`. -/
theorem uniformPair_apply_of_ne (n : ℕ) (hn : 2 ≤ n)
    {i j : Fin n} (hij : i ≠ j) :
    uniformPair n hn (i, j) = ((n * (n - 1) : ℕ) : ENNReal)⁻¹ := by
  rw [uniformPair, PMF.uniformOfFinset_apply_of_mem]
  · rw [offDiagonalPairs_card]
  · exact (mem_offDiagonalPairs n (i, j)).mpr hij

/-- A diagonal pair is never sampled by the uniform off-diagonal
scheduler. -/
theorem uniformPair_apply_self (n : ℕ) (hn : 2 ≤ n) (i : Fin n) :
    uniformPair n hn (i, i) = 0 := by
  rw [uniformPair, PMF.uniformOfFinset_apply_of_notMem]
  exact fun h => (mem_offDiagonalPairs n (i, i)).mp h rfl

/-- A fixed unordered off-diagonal pair has twice the mass of one ordered
orientation. -/
theorem uniformPair_apply_pair_add_swap_of_ne (n : ℕ) (hn : 2 ≤ n)
    {i j : Fin n} (hij : i ≠ j) :
    uniformPair n hn (i, j) + uniformPair n hn (j, i) =
      (2 : ENNReal) * ((n * (n - 1) : ℕ) : ENNReal)⁻¹ := by
  rw [uniformPair_apply_of_ne n hn hij,
    uniformPair_apply_of_ne n hn hij.symm, two_mul]

/-- Ordered off-diagonal scheduler pairs in which agent `i` participates. -/
def PairsInvolving (n : ℕ) (i : Fin n) : Finset (Fin n × Fin n) :=
  (OffDiagonalPairs n).filter fun p => p.1 = i ∨ p.2 = i

/-- Membership in `PairsInvolving`. -/
theorem mem_PairsInvolving (n : ℕ) (i : Fin n) (p : Fin n × Fin n) :
    p ∈ PairsInvolving n i ↔ p.1 ≠ p.2 ∧ (p.1 = i ∨ p.2 = i) := by
  simp [PairsInvolving, mem_offDiagonalPairs]

/-- There are exactly `2 * (n - 1)` ordered off-diagonal pairs involving a
fixed agent. -/
theorem pairsInvolving_card (n : ℕ) (i : Fin n) :
    (PairsInvolving n i).card = 2 * (n - 1) := by
  classical
  let left : Finset (Fin n × Fin n) :=
    ((Finset.univ : Finset (Fin n)).erase i).image fun j => (i, j)
  let right : Finset (Fin n × Fin n) :=
    ((Finset.univ : Finset (Fin n)).erase i).image fun j => (j, i)
  have hleft_card : left.card = n - 1 := by
    dsimp [left]
    rw [Finset.card_image_of_injective]
    · rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
        Fintype.card_fin]
    · intro a b h
      exact congrArg Prod.snd h
  have hright_card : right.card = n - 1 := by
    dsimp [right]
    rw [Finset.card_image_of_injective]
    · rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
        Fintype.card_fin]
    · intro a b h
      exact congrArg Prod.fst h
  have hdisjoint : Disjoint left right := by
    rw [Finset.disjoint_left]
    intro p hpLeft hpRight
    dsimp [left] at hpLeft
    dsimp [right] at hpRight
    rw [Finset.mem_image] at hpLeft hpRight
    rcases hpLeft with ⟨j, hj, hpj⟩
    rcases hpRight with ⟨k, hk, hpk⟩
    have hpair : (i, j) = (k, i) := hpj.trans hpk.symm
    exact (Finset.mem_erase.mp hj).1 (congrArg Prod.snd hpair)
  have hunion : PairsInvolving n i = left ∪ right := by
    ext p
    constructor
    · intro hp
      rw [mem_PairsInvolving] at hp
      rcases hp with ⟨hne, htouch | htouch⟩
      · subst htouch
        rw [Finset.mem_union]
        apply Or.inl
        dsimp [left]
        rw [Finset.mem_image]
        refine ⟨p.2, ?_, ?_⟩
        · rw [Finset.mem_erase]
          exact ⟨by simpa using hne.symm, Finset.mem_univ _⟩
        · exact Prod.ext rfl rfl
      · subst htouch
        rw [Finset.mem_union]
        apply Or.inr
        dsimp [right]
        rw [Finset.mem_image]
        refine ⟨p.1, ?_, ?_⟩
        · rw [Finset.mem_erase]
          exact ⟨by simpa using hne, Finset.mem_univ _⟩
        · exact Prod.ext rfl rfl
    · intro hp
      rw [Finset.mem_union] at hp
      rw [mem_PairsInvolving]
      rcases hp with hpLeft | hpRight
      · dsimp [left] at hpLeft
        rw [Finset.mem_image] at hpLeft
        rcases hpLeft with ⟨j, hj, hpj⟩
        have hji : j ≠ i := (Finset.mem_erase.mp hj).1
        rw [← hpj]
        exact ⟨hji.symm, Or.inl rfl⟩
      · dsimp [right] at hpRight
        rw [Finset.mem_image] at hpRight
        rcases hpRight with ⟨j, hj, hpj⟩
        have hji : j ≠ i := (Finset.mem_erase.mp hj).1
        rw [← hpj]
        exact ⟨hji, Or.inr rfl⟩
  rw [hunion, Finset.card_union_of_disjoint hdisjoint, hleft_card, hright_card]
  omega

/-- Scheduler mass of a finite ordered-pair set. -/
noncomputable def pairSetMass (n : ℕ) (hn : 2 ≤ n)
    (S : Finset (Fin n × Fin n)) : ENNReal :=
  S.sum fun p => uniformPair n hn p

/-- Scheduler mass is monotone in the finite pair set. -/
theorem pairSetMass_mono (n : ℕ) (hn : 2 ≤ n)
    {S T : Finset (Fin n × Fin n)} (hST : S ⊆ T) :
    pairSetMass n hn S ≤ pairSetMass n hn T := by
  unfold pairSetMass
  exact Finset.sum_le_sum_of_subset hST

/-- Any set contained in the off-diagonal scheduler support has mass
`|S| / (n(n-1))`. -/
theorem pairSetMass_eq_card_mul_inv_of_subset
    (n : ℕ) (hn : 2 ≤ n) (S : Finset (Fin n × Fin n))
    (hS : S ⊆ OffDiagonalPairs n) :
    pairSetMass n hn S =
      (S.card : ENNReal) * ((n * (n - 1) : ℕ) : ENNReal)⁻¹ := by
  unfold pairSetMass
  trans S.sum fun _p => ((n * (n - 1) : ℕ) : ENNReal)⁻¹
  · apply Finset.sum_congr rfl
    intro p hp
    exact uniformPair_apply_of_ne n hn ((mem_offDiagonalPairs n p).mp (hS hp))
  · simp [Finset.sum_const, nsmul_eq_mul]

/-- The scheduler mass of all ordered pairs involving a fixed agent is
`2 / n`. -/
theorem pairSetMass_pairsInvolving (n : ℕ) (hn : 2 ≤ n) (i : Fin n) :
    pairSetMass n hn (PairsInvolving n i) =
      (2 : ENNReal) * (n : ENNReal)⁻¹ := by
  rw [pairSetMass_eq_card_mul_inv_of_subset]
  · rw [pairsInvolving_card]
    have hnpos : 0 < n := by omega
    have hsub : 0 < n - 1 := by omega
    have hn_ne_zero : (n : ENNReal) ≠ 0 := by
      exact_mod_cast (ne_of_gt hnpos)
    have hn_ne_top : (n : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
    have hsub_ne_zero : ((n - 1 : ℕ) : ENNReal) ≠ 0 := by
      exact_mod_cast (ne_of_gt hsub)
    have hsub_ne_top : ((n - 1 : ℕ) : ENNReal) ≠ ⊤ :=
      ENNReal.natCast_ne_top _
    calc
      (((2 * (n - 1) : ℕ) : ENNReal) *
          ((n * (n - 1) : ℕ) : ENNReal)⁻¹)
          = ((2 : ENNReal) * ((n - 1 : ℕ) : ENNReal)) *
              (((n : ENNReal) * ((n - 1 : ℕ) : ENNReal))⁻¹) := by
              rw [Nat.cast_mul, Nat.cast_mul]
              norm_num
      _ = (2 : ENNReal) * (((n - 1 : ℕ) : ENNReal) *
              (((n : ENNReal) * ((n - 1 : ℕ) : ENNReal))⁻¹)) := by
              rw [mul_assoc]
      _ = (2 : ENNReal) * (n : ENNReal)⁻¹ := by
              rw [ENNReal.mul_inv (Or.inl hn_ne_zero) (Or.inl hn_ne_top)]
              calc
                (2 : ENNReal) * (((n - 1 : ℕ) : ENNReal) *
                    ((n : ENNReal)⁻¹ * ((n - 1 : ℕ) : ENNReal)⁻¹))
                    =
                  (2 : ENNReal) *
                    ((((n - 1 : ℕ) : ENNReal) *
                      ((n - 1 : ℕ) : ENNReal)⁻¹) * (n : ENNReal)⁻¹) := by
                    ac_rfl
                _ = (2 : ENNReal) * (n : ENNReal)⁻¹ := by
                    rw [ENNReal.mul_inv_cancel hsub_ne_zero hsub_ne_top, one_mul]
  · intro p hp
    exact (mem_offDiagonalPairs n p).mpr ((mem_PairsInvolving n i p).mp hp).1

/-- The whole scheduler support has mass one. -/
theorem pairSetMass_offDiagonalPairs
    (n : ℕ) (hn : 2 ≤ n) :
    pairSetMass n hn (OffDiagonalPairs n) = 1 := by
  rw [pairSetMass_eq_card_mul_inv_of_subset n hn (OffDiagonalPairs n)
      (fun _ h => h),
    offDiagonalPairs_card]
  have hnpos : 0 < n := by omega
  have hsub : 0 < n - 1 := by omega
  have hmul : 0 < n * (n - 1) := Nat.mul_pos hnpos hsub
  change (((n * (n - 1) : ℕ) : ENNReal) *
      (((n * (n - 1) : ℕ) : ENNReal))⁻¹ = 1)
  refine ENNReal.mul_inv_cancel ?_ ?_
  · change (((n * (n - 1) : ℕ) : ENNReal) ≠ 0)
    exact_mod_cast (ne_of_gt hmul)
  · change (((n * (n - 1) : ℕ) : ENNReal) ≠ ⊤)
    exact ENNReal.natCast_ne_top _

/-- Scheduler mass of an off-diagonal finite filter is the `PMF` mass of the
corresponding event. -/
theorem pairSetMass_filter_offDiagonal_eq_toOuterMeasure
    (n : ℕ) (hn : 2 ≤ n) (A : Fin n × Fin n → Prop) [DecidablePred A] :
    pairSetMass n hn ((OffDiagonalPairs n).filter A) =
      (uniformPair n hn).toOuterMeasure {p | A p} := by
  rw [pairSetMass_eq_card_mul_inv_of_subset]
  · rw [uniformPair, PMF.toOuterMeasure_uniformOfFinset_apply,
      offDiagonalPairs_card]
    rw [div_eq_mul_inv]
    congr
  · intro p hp
    exact (Finset.mem_filter.mp hp).1

/-- Ordered pairs whose single interaction strictly decreases a natural
potential.  This is the common bridge from deterministic descent lemmas
to one-step probability lower bounds. -/
def GoodPairs (P : Protocol Q X Y)
    (φ : Config Q X n → ℕ) (C : Config Q X n) :
    Finset (Fin n × Fin n) :=
  (OffDiagonalPairs n).filter fun p => φ (C.step P p.1 p.2) < φ C

/-- Membership in the good-pair set. -/
theorem mem_GoodPairs (P : Protocol Q X Y)
    (φ : Config Q X n → ℕ) (C : Config Q X n)
    (p : Fin n × Fin n) :
    p ∈ GoodPairs P φ C ↔
      p.1 ≠ p.2 ∧ φ (C.step P p.1 p.2) < φ C := by
  simp [GoodPairs, mem_offDiagonalPairs]

/-- The number of good pairs is at most the scheduler support size. -/
theorem GoodPairs_card_le (P : Protocol Q X Y)
    (φ : Config Q X n → ℕ) (C : Config Q X n) :
    (GoodPairs P φ C).card ≤ n * (n - 1) := by
  rw [← offDiagonalPairs_card n]
  exact Finset.card_filter_le _ _

/-- A deterministic one-step descent witness gives a nonempty good-pair
set. -/
theorem GoodPairs_nonempty_of_descent
    (P : Protocol Q X Y) (φ : Config Q X n → ℕ) (C : Config Q X n)
    {i j : Fin n} (hij : i ≠ j)
    (hdec : φ (C.step P i j) < φ C) :
    (GoodPairs P φ C).Nonempty := by
  exact ⟨(i, j), (mem_GoodPairs P φ C (i, j)).mpr ⟨hij, hdec⟩⟩

/-- Scheduler mass of the good-pair set, expressed by its cardinality. -/
theorem pairSetMass_GoodPairs
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (φ : Config Q X n → ℕ) (C : Config Q X n) :
    pairSetMass n hn (GoodPairs P φ C) =
      ((GoodPairs P φ C).card : ENNReal) *
        ((n * (n - 1) : ℕ) : ENNReal)⁻¹ := by
  apply pairSetMass_eq_card_mul_inv_of_subset
  intro p hp
  exact (mem_offDiagonalPairs n p).mpr ((mem_GoodPairs P φ C p).mp hp).1

/-- Single Markov step: from configuration `C`, draw a uniform random
pair `(i, j)` and apply `C.step P i j`. -/
noncomputable def stepDist (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C : Config Q X n) : PMF (Config Q X n) :=
  (uniformPair n hn).map (fun p => C.step P p.1 p.2)

/-- The `t`-th step distribution from `C₀`: composition of `t` Markov
steps. -/
noncomputable def nthStepDist (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) : ℕ → PMF (Config Q X n)
  | 0     => PMF.pure C₀
  | t + 1 => (nthStepDist P hn C₀ t).bind (stepDist P hn)

/-- Semigroup law for the uniform-scheduler Markov chain. -/
theorem nthStepDist_add (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (t k : ℕ) :
    nthStepDist P hn C₀ (t + k) =
      (nthStepDist P hn C₀ t).bind fun C =>
        nthStepDist P hn C k := by
  induction k generalizing t with
  | zero =>
      simp [nthStepDist]
  | succ k ih =>
      rw [Nat.add_succ, nthStepDist, ih t]
      simp only [nthStepDist, PMF.bind_bind]

end Probability
end SSEM
