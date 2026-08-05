/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# The foray tail bound (phase-0 combinatorial core)

Phase 0 of Theorem 1(a) analyses an augmented random walk on checkpoint states.
By the paper's probability-preserving bijection, a sequence of forays with a
total of `T` transitions corresponds to a binary sequence that starts with `1`
and contains no two consecutive `0`s; the walk fails to reach the top checkpoint
only when such a bounded sequence is *not* forced to reach it, an event bounded
by the probability that a uniform binary string of the relevant length contains
no two consecutive `0`s.

`forayCount L` is the number of length-`L` binary strings with no two
consecutive `0`s (a Fibonacci-shifted sequence: `1, 2, 3, 5, 8, …`).  The core
quantitative fact is the geometric tail bound

`forayCount L ≤ (5/4) · (41/25)^L`,

whence the probability form

`forayCount L / 2^L ≤ (5/4) · (41/50)^L`.

Since `41/50 < 1`, taking `L = 2 γ lg n` gives the `exp(-Ω(γ lg n))` decay the
paper uses.  This file proves the two real-valued inequalities; the bridge to
the chain's failure mass is done where phase 0 is assembled.
-/

namespace Tri

/-- The number of length-`L` binary strings containing no two consecutive `0`s.
This is the Fibonacci-shifted count `1, 2, 3, 5, 8, 13, …`. -/
def forayCount : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | (n + 2) => forayCount (n + 1) + forayCount n

/-- The count obeys the defining two-term recurrence. -/
theorem forayCount_succ_succ (n : ℕ) :
    forayCount (n + 2) = forayCount (n + 1) + forayCount n := rfl

/-- **The foray tail bound (count form).**  The number of no-two-consecutive-`0`
binary strings of length `L` grows no faster than `(5/4) · (41/25)^L`.  The base
`41/25 = 1.64` sits above the golden ratio `φ ≈ 1.618`, giving the induction the
slack `66/25 ≤ (41/25)²`. -/
theorem forayCount_le (L : ℕ) : (forayCount L : ℝ) ≤ (5 / 4) * (41 / 25) ^ L := by
  have key : ∀ m, (forayCount m : ℝ) ≤ (5 / 4) * (41 / 25) ^ m
      ∧ (forayCount (m + 1) : ℝ) ≤ (5 / 4) * (41 / 25) ^ (m + 1) := by
    intro m
    induction m with
    | zero =>
      refine ⟨?_, ?_⟩ <;> simp [forayCount] <;> norm_num
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      have hpos : (0 : ℝ) ≤ (41 / 25) ^ k := by positivity
      have expand : (41 / 25 : ℝ) ^ (k + 2) = (41 / 25) ^ k * (41 / 25) ^ 2 := by ring
      have expand1 : (41 / 25 : ℝ) ^ (k + 1) = (41 / 25) ^ k * (41 / 25) := by ring
      rw [forayCount_succ_succ]
      push_cast
      nlinarith [ih.1, ih.2, hpos, expand, expand1]
  exact (key L).1

/-- **The foray tail bound (probability form).**  A uniform random binary string
of length `L` contains no two consecutive `0`s with probability at most
`(5/4) · (41/50)^L`.  As `41/50 = 0.82 < 1`, this decays geometrically. -/
theorem forayProb_le (L : ℕ) :
    (forayCount L : ℝ) / 2 ^ L ≤ (5 / 4) * (41 / 50) ^ L := by
  have hpow : (0 : ℝ) < 2 ^ L := by positivity
  rw [div_le_iff₀ hpow]
  have hsplit : (5 / 4 : ℝ) * (41 / 50) ^ L * 2 ^ L
      = (5 / 4) * (41 / 25) ^ L := by
    rw [mul_assoc, ← mul_pow]
    norm_num
  rw [hsplit]
  exact forayCount_le L

end Tri
