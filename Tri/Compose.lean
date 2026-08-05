/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Decay

/-!
# Composition over deterministic schedules

This file provides the deterministic-time Markov property for `iter` and a
probabilistic Hoare triple for chaining finite stages.  Sequential composition
uses only restricted sums and a union bound: states that miss an intermediate
postcondition pay the first-stage error, while states that satisfy it pay the
second-stage error.  No conditional probability or division is involved.

## Main results

* `iter_add` splits an iterate at a deterministic time.
* `Reaches.comp` composes two finite-horizon reachability bounds.
* `Reaches.iterate` applies the same stage a prescribed number of times.
-/

namespace Tri

open scoped ENNReal

variable {α : Type*}

/-- Splitting an iterate at a deterministic time gives the corresponding
Kleisli composition of the two pieces. -/
theorem iter_add (K : α → PMF α) (m T : ℕ) (s : α) :
    iter K (m + T) s = (iter K m s).bind (iter K T) := by
  induction m generalizing s with
  | zero => simp [iter, PMF.pure_bind]
  | succ m ih =>
    rw [Nat.succ_add, iter_succ, iter_succ]
    calc
      (K s).bind (iter K (m + T)) =
          (K s).bind (fun a => (iter K m a).bind (iter K T)) :=
        congrArg _ (funext ih)
      _ = ((K s).bind (iter K m)).bind (iter K T) :=
        (PMF.bind_bind _ _ _).symm

/-- `Reaches K T P Q ε` means that every state satisfying `P` reaches `Q`
after exactly `T` steps, except for probability at most `ε`. -/
def Reaches (K : α → PMF α) (T : ℕ) (P Q : α → Prop) [DecidablePred Q]
    (ε : ℝ≥0∞)
    : Prop :=
  ∀ s, P s → ∑' z, (if Q z then 0 else iter K T s z) ≤ ε

/-- Sequential composition of two finite-horizon reachability bounds. -/
theorem Reaches.comp {K : α → PMF α} {P Q R : α → Prop}
    [DecidablePred Q] [DecidablePred R] {T₁ T₂ : ℕ} {ε₁ ε₂ : ℝ≥0∞}
    (h₁ : Reaches K T₁ P Q ε₁) (h₂ : Reaches K T₂ Q R ε₂) :
    Reaches K (T₁ + T₂) P R (ε₁ + ε₂) := by
  intro s hs
  rw [iter_add]
  let p := iter K T₁ s
  let f := iter K T₂
  have hmass (q : PMF α) : ∑' z, (if R z then 0 else q z) ≤ 1 := by
    calc
      ∑' z, (if R z then 0 else q z) ≤ ∑' z, q z :=
        ENNReal.tsum_le_tsum fun z => by split_ifs <;> simp
      _ = 1 := PMF.tsum_coe q
  have hgood : ∑' y, (if Q y then p y * ε₂ else 0) ≤ ε₂ := by
    calc
      ∑' y, (if Q y then p y * ε₂ else 0) ≤ ∑' y, p y * ε₂ :=
        ENNReal.tsum_le_tsum fun y => by split_ifs <;> simp
      _ = (∑' y, p y) * ε₂ := ENNReal.tsum_mul_right
      _ = ε₂ := by rw [PMF.tsum_coe, one_mul]
  calc
    ∑' z, (if R z then 0 else (p.bind f) z)
        = ∑' z, ∑' y, p y * (if R z then 0 else f y z) := by
          apply tsum_congr
          intro z
          rw [PMF.bind_apply]
          by_cases hz : R z <;> simp [hz]
    _ = ∑' y, ∑' z, p y * (if R z then 0 else f y z) := ENNReal.tsum_comm
    _ = ∑' y, p y * ∑' z, (if R z then 0 else f y z) := by
          apply tsum_congr
          intro y
          rw [ENNReal.tsum_mul_left]
    _ ≤ ∑' y, ((if Q y then 0 else p y) + (if Q y then p y * ε₂ else 0)) := by
          refine ENNReal.tsum_le_tsum fun y => ?_
          by_cases hy : Q y
          · simp only [if_pos hy, zero_add]
            exact mul_le_mul_right (h₂ y hy) _
          · simp only [if_neg hy, add_zero]
            calc
              p y * ∑' z, (if R z then 0 else f y z) ≤ p y * 1 :=
                mul_le_mul_right (hmass (f y)) _
              _ = p y := mul_one _
    _ = (∑' y, (if Q y then 0 else p y)) +
        ∑' y, (if Q y then p y * ε₂ else 0) := ENNReal.tsum_add
    _ ≤ ε₁ + ε₂ := add_le_add (h₁ s hs) hgood

/-- Repeating one stage `k` times accumulates at most `k` copies of its failure
bound. -/
theorem Reaches.iterate {K : α → PMF α} {P : α → Prop} [DecidablePred P]
    {T : ℕ} {ε : ℝ≥0∞} (h : Reaches K T P P ε) (k : ℕ) :
    Reaches K (k * T) P P (k * ε) := by
  induction k with
  | zero =>
    simp only [zero_mul]
    intro s hs
    rw [tsum_eq_single s (by
      intro z hzs
      simp [iter, PMF.pure_apply, hzs])]
    simp [hs]
  | succ k ih =>
    simpa [Nat.succ_mul, Nat.cast_succ, add_mul] using ih.comp h

end Tri
