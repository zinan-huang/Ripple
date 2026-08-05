/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.InfectionActivationConstants
import Tri.Ladder

/-!
# Finite early activation ladders

This file composes the concrete early `a → 2a` rungs. The arithmetic choice
of the number of rungs remains separate: the theorem accepts exactly the
condition required at every dyadic scale and exposes the resulting horizon
and union-bound error.
-/

namespace Tri

open scoped ENNReal

/-- Active lower bound at early rung `j`. -/
def infectionEarlyLevel (a j : ℕ) : ℕ :=
  2 ^ j * a

/-- Deterministic raw horizon of `k` early doubling rungs. -/
def infectionEarlyHorizon (n k : ℕ) : ℕ :=
  k * (128 * n)

/-- Exact union-bound budget of the selected early rungs. -/
noncomputable def infectionEarlyError (a k : ℕ) : ℝ≥0∞ :=
  ∑ j ∈ Finset.range k,
    ENNReal.ofReal (Real.exp (-(infectionEarlyLevel a j : ℝ)))

@[simp] theorem infectionEarlyLevel_zero (a : ℕ) :
    infectionEarlyLevel a 0 = a := by
  simp [infectionEarlyLevel]

theorem infectionEarlyLevel_succ (a j : ℕ) :
    2 * infectionEarlyLevel a j = infectionEarlyLevel a (j + 1) := by
  unfold infectionEarlyLevel
  rw [pow_succ]
  ring

theorem infectionEarlyLevel_pos
    (a j : ℕ) (ha : 1 ≤ a) :
    1 ≤ infectionEarlyLevel a j := by
  unfold infectionEarlyLevel
  have hpos : 0 < 2 ^ j * a :=
    Nat.mul_pos (by positivity) (by omega)
  omega

/-- Every finite family of admissible dyadic early rungs composes with its
exact summed horizon and failure budget. -/
theorem infectionActivation_early_ladder
    (n a k : ℕ) (h3 : 3 ≤ n) (ha : 1 ≤ a)
    (hvalid : ∀ j < k, 4 * infectionEarlyLevel a j ≤ n) :
    Reaches (infectionStateStep n h3)
      (infectionEarlyHorizon n k)
      (fun s : InfectionState n => a ≤ s.1.active)
      (fun s => infectionEarlyLevel a k ≤ s.1.active)
      (infectionEarlyError a k) := by
  let P : ℕ → InfectionState n → Prop :=
    fun j s => infectionEarlyLevel a j ≤ s.1.active
  let T : ℕ → ℕ := fun _ => 128 * n
  let ε : ℕ → ℝ≥0∞ := fun j =>
    ENNReal.ofReal (Real.exp (-(infectionEarlyLevel a j : ℝ)))
  have hrungs : ∀ j < k,
      Reaches (infectionStateStep n h3) (T j)
        (P j) (P (j + 1)) (ε j) := by
    intro j hj
    have hstage :=
      infectionActivation_doubling_Reaches
        n (infectionEarlyLevel a j) h3
        (infectionEarlyLevel_pos a j ha)
        (hvalid j hj)
    simpa only [P, T, ε, infectionEarlyLevel_succ] using hstage
  have hchain :=
    Reaches.chain
      (K := infectionStateStep n h3)
      (P := P) (T := T) (ε := ε) hrungs
  simpa [P, T, ε, infectionEarlyHorizon, infectionEarlyError] using hchain

/-- If the final dyadic checkpoint is at least one quarter active, the early
ladder is already in the precondition of every late activation rung. -/
theorem infectionActivation_early_ladder_to_quarter
    (n a k : ℕ) (h3 : 3 ≤ n) (ha : 1 ≤ a)
    (hvalid : ∀ j < k, 4 * infectionEarlyLevel a j ≤ n)
    (hquarter : n ≤ 4 * infectionEarlyLevel a k) :
    Reaches (infectionStateStep n h3)
      (infectionEarlyHorizon n k)
      (fun s : InfectionState n => a ≤ s.1.active)
      (fun s => n ≤ 4 * s.1.active)
      (infectionEarlyError a k) := by
  exact
    (infectionActivation_early_ladder n a k h3 ha hvalid).mono_post
      (fun s hs =>
        hquarter.trans
          (Nat.mul_le_mul_left 4 hs))

/-- A positive starting scale has some dyadic multiple at least one quarter
of the population. -/
theorem infectionEarly_exists_quarter
    (n a : ℕ) (ha : 1 ≤ a) :
    ∃ k, n ≤ 4 * infectionEarlyLevel a k := by
  refine ⟨n, ?_⟩
  unfold infectionEarlyLevel
  have hn := Nat.lt_two_pow_self (n := n)
  nlinarith

/-- Least number of early doublings required to reach the quarter-active
checkpoint. -/
noncomputable def infectionEarlyStages
    (n a : ℕ) (ha : 1 ≤ a) : ℕ :=
  Nat.find (infectionEarly_exists_quarter n a ha)

theorem infectionEarlyStages_quarter
    (n a : ℕ) (ha : 1 ≤ a) :
    n ≤ 4 * infectionEarlyLevel a (infectionEarlyStages n a ha) := by
  exact Nat.find_spec (infectionEarly_exists_quarter n a ha)

theorem infectionEarlyStages_valid
    (n a : ℕ) (ha : 1 ≤ a)
    (j : ℕ) (hj : j < infectionEarlyStages n a ha) :
    4 * infectionEarlyLevel a j ≤ n := by
  have hnot :=
    Nat.find_min (infectionEarly_exists_quarter n a ha) hj
  omega

theorem infectionEarlyStages_le_population
    (n a : ℕ) (ha : 1 ≤ a) :
    infectionEarlyStages n a ha ≤ n := by
  apply Nat.find_min' (infectionEarly_exists_quarter n a ha)
  unfold infectionEarlyLevel
  have hn := Nat.lt_two_pow_self (n := n)
  nlinarith

/-- The least quarter-reaching scale uses at most the base-two logarithm of
the population. -/
theorem infectionEarlyStages_le_log
    (n a : ℕ) (hn : 0 < n) (ha : 1 ≤ a) :
    infectionEarlyStages n a ha ≤ Nat.log 2 n := by
  apply Nat.find_min' (infectionEarly_exists_quarter n a ha)
  have hpow :=
    Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) n
  rw [pow_succ] at hpow
  unfold infectionEarlyLevel
  nlinarith

theorem infectionEarlyHorizon_le_log
    (n a : ℕ) (hn : 0 < n) (ha : 1 ≤ a) :
    infectionEarlyHorizon n (infectionEarlyStages n a ha) ≤
      Nat.log 2 n * (128 * n) := by
  unfold infectionEarlyHorizon
  exact Nat.mul_le_mul_right _
    (infectionEarlyStages_le_log n a hn ha)

/-- The exponentially decreasing dyadic rung errors sum to at most twice the
first one. -/
theorem infectionEarlyError_le_twice_first
    (a k : ℕ) (ha : 1 ≤ a) :
    infectionEarlyError a k ≤
      ENNReal.ofReal (2 * Real.exp (-(a : ℝ))) := by
  let f : ℕ → ℝ :=
    fun j => Real.exp (-(infectionEarlyLevel a j : ℝ))
  have hf : ∀ j, 0 ≤ f j :=
    fun j => (Real.exp_pos _).le
  have hhalf : ∀ j, 2 * f (j + 1) ≤ f j := by
    intro j
    let L : ℝ := infectionEarlyLevel a j
    have hL : (1 : ℝ) ≤ L := by
      dsimp only [L]
      exact_mod_cast infectionEarlyLevel_pos a j ha
    have hlog : Real.log 2 ≤ L := by
      have hlogOne : Real.log 2 ≤ (1 : ℝ) := by
        have h :=
          Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
        norm_num at h
        exact h
      exact hlogOne.trans hL
    have hexp : Real.exp (-L) ≤ (1 : ℝ) / 2 := by
      have hmono := Real.exp_le_exp.mpr (neg_le_neg hlog)
      have htwo : Real.exp (-Real.log 2) = (1 : ℝ) / 2 := by
        rw [Real.exp_neg, Real.exp_log
          (by norm_num : (0 : ℝ) < 2)]
        norm_num
      rwa [htwo] at hmono
    have hnext :
        f (j + 1) = Real.exp (-L) * Real.exp (-L) := by
      dsimp only [f, L]
      rw [← Real.exp_add]
      congr 1
      rw [← infectionEarlyLevel_succ]
      push_cast
      ring
    rw [hnext]
    nlinarith [Real.exp_pos (-L)]
  have hstrong : ∀ m : ℕ,
      (∑ j ∈ Finset.range m, f j) + 2 * f m ≤ 2 * f 0 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        rw [Finset.sum_range_succ]
        calc
          (∑ j ∈ Finset.range m, f j) + f m + 2 * f (m + 1)
              ≤ (∑ j ∈ Finset.range m, f j) + 2 * f m := by
                linarith [hhalf m]
          _ ≤ 2 * f 0 := ih
  have hsum : (∑ j ∈ Finset.range k, f j) ≤ 2 * f 0 :=
    (le_add_of_nonneg_right
      (mul_nonneg (by norm_num) (hf k))).trans (hstrong k)
  unfold infectionEarlyError
  rw [← ENNReal.ofReal_sum_of_nonneg
    (fun j _hj => hf j)]
  apply ENNReal.ofReal_le_ofReal
  simpa [f, infectionEarlyLevel] using hsum

/-- Canonical early schedule from a positive active lower bound to the
quarter-active checkpoint. -/
theorem infectionActivation_early_to_quarter
    (n a : ℕ) (h3 : 3 ≤ n) (ha : 1 ≤ a) :
    Reaches (infectionStateStep n h3)
      (infectionEarlyHorizon n (infectionEarlyStages n a ha))
      (fun s : InfectionState n => a ≤ s.1.active)
      (fun s => n ≤ 4 * s.1.active)
      (infectionEarlyError a (infectionEarlyStages n a ha)) := by
  exact infectionActivation_early_ladder_to_quarter
    n a (infectionEarlyStages n a ha) h3 ha
    (fun j hj => infectionEarlyStages_valid n a ha j hj)
    (infectionEarlyStages_quarter n a ha)

/-- Fixed integer checkpoint representing one quarter of the population. -/
def infectionQuarter (n : ℕ) : ℕ :=
  (n + 3) / 4

theorem infectionQuarter_covers (n : ℕ) :
    n ≤ 4 * infectionQuarter n := by
  unfold infectionQuarter
  omega

theorem infectionQuarter_le
    (n : ℕ) (hn : 1 ≤ n) :
    infectionQuarter n ≤ n := by
  unfold infectionQuarter
  omega

theorem infectionQuarter_le_of_cover
    (n A : ℕ) (hA : n ≤ 4 * A) :
    infectionQuarter n ≤ A := by
  unfold infectionQuarter
  omega

theorem two_le_infectionQuarter
    (n : ℕ) (hn : 5 ≤ n) :
    2 ≤ infectionQuarter n := by
  unfold infectionQuarter
  omega

/-- Complete activation-clock composition: the logarithmic early ladder
reaches the fixed quarter checkpoint, after which the inactive-halving ladder
activates every remaining molecule. -/
theorem infectionActivation_to_all
    (n a : ℕ) (h3 : 3 ≤ n) (hn : 5 ≤ n) (ha : 1 ≤ a) :
    Reaches (infectionStateStep n h3)
      (infectionEarlyHorizon n (infectionEarlyStages n a ha) +
        infectionLateStages (n - infectionQuarter n) * (1024 * n))
      (fun s : InfectionState n => a ≤ s.1.active)
      (fun s => n ≤ s.1.active)
      (infectionEarlyError a (infectionEarlyStages n a ha) +
        infectionLateError (n - infectionQuarter n)) := by
  let q := infectionQuarter n
  let r := n - q
  have hqn : q ≤ n := by
    dsimp only [q]
    exact infectionQuarter_le n (by omega)
  have hnsub : n - r = q := by
    dsimp only [r]
    exact Nat.sub_sub_self hqn
  have hearly :=
    infectionActivation_early_to_quarter n a h3 ha
  have hearlyQ :
      Reaches (infectionStateStep n h3)
        (infectionEarlyHorizon n (infectionEarlyStages n a ha))
        (fun s : InfectionState n => a ≤ s.1.active)
        (fun s => q ≤ s.1.active)
        (infectionEarlyError a (infectionEarlyStages n a ha)) :=
    hearly.mono_post (fun s hs =>
      infectionQuarter_le_of_cover n s.1.active hs)
  have hrn : r ≤ n := by
    dsimp only [r]
    exact Nat.sub_le _ _
  have hq2 : 2 ≤ q := by
    dsimp only [q]
    exact two_le_infectionQuarter n hn
  have hqquarter : n ≤ 4 * q := by
    dsimp only [q]
    exact infectionQuarter_covers n
  have hlate :=
    infectionActivation_late_to_all
      n r h3 hrn
      (by rwa [hnsub])
      (by rwa [hnsub])
  have hlateQ :
      Reaches (infectionStateStep n h3)
        (infectionLateStages r * (1024 * n))
        (fun s : InfectionState n => q ≤ s.1.active)
        (fun s => n ≤ s.1.active)
        (infectionLateError r) := by
    simpa only [hnsub] using hlate
  simpa only [q, r] using hearlyQ.comp hlateQ

end Tri

#print axioms Tri.infectionEarlyLevel_succ
#print axioms Tri.infectionActivation_early_ladder
#print axioms Tri.infectionActivation_early_ladder_to_quarter
#print axioms Tri.infectionEarlyStages_le_log
#print axioms Tri.infectionEarlyError_le_twice_first
#print axioms Tri.infectionActivation_early_to_quarter
#print axioms Tri.infectionActivation_to_all
