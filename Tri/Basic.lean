/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Combinatorial core of the tri-molecular Approximate Majority CRN

The CRN `Tri` of Condon, Hajiaghayi, Kirkpatrick and Mañuch acts on two species
`X` and `Y` with `n = x + y` invariant, via the reactions

    (1)  X + X + Y  →  X + X + X
    (2)  X + Y + Y  →  Y + Y + Y

An *interaction event* draws an unordered triple of the `n` molecules uniformly,
so the reaction probabilities are `C(x,2)·y / C(n,3)` and `C(y,2)·x / C(n,3)`.

This file proves the deterministic arithmetic that the probabilistic development
rests on. Two facts carry the weight:

* `choose_three_split` classifies an unordered triple by its composition
  (XXX / XXY / XYY / YYY). It is the obligation that makes the step kernel sum
  to one, and it is the only genuine combinatorial debt of the model.
* `productive_two_mul` is the identity behind the clean form of the *productive*
  probability, `q = 3xy/(n(n-1))`, used throughout the analysis.

Every statement here is deliberately free of natural subtraction, which
truncates at zero and would silently change the meaning at the boundary cases
`x, y ∈ {0, 1, 2}` — exactly the cases the endgame of the paper's analysis
lives in. The sole exception is `two_mul_choose_two`, stated in Mathlib's own
`n - 1` idiom; it is not used in the statements of the other results.

## Main results

* `choose_three_split` : `C(x+y,3) = C(x,3) + C(x,2)·y + x·C(y,2) + C(y,3)`
* `productive_two_mul` : `2·(C(x,2)·y + x·C(y,2)) + 2·x·y = x·y·(x+y)`

Reference: A. Condon, M. Hajiaghayi, D. Kirkpatrick, J. Mañuch,
*Approximate Majority Analyses using Tri-molecular Chemical Reaction Networks*,
Section 2.1 and Section 3.
-/

namespace Tri

open Finset

/-- Doubling a binomial coefficient `C(n+1,2)`, in subtraction-free form.
This is the successor-indexed companion of `Nat.choose_two_right`, phrased so
that it can be used without a divisibility side condition. -/
theorem two_mul_choose_two_succ (n : ℕ) : 2 * Nat.choose (n + 1) 2 = (n + 1) * n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [Nat.choose_succ_succ (k + 1) 1, Nat.mul_add, ih, Nat.choose_one_right]
    ring

/-- `2 * C(n,2) = n * (n-1)`, in Mathlib's truncated-subtraction idiom.
Provided for interoperability only; the results below avoid natural
subtraction entirely. -/
theorem two_mul_choose_two (n : ℕ) : 2 * Nat.choose n 2 = n * (n - 1) := by
  cases n with
  | zero => rfl
  | succ k => simpa using two_mul_choose_two_succ k

/-- **Composition split for unordered triples.**

An unordered triple drawn from a population of `x` molecules of species `X` and
`y` of species `Y` has exactly one of four compositions — `XXX`, `XXY`, `XYY`,
`YYY` — giving

`C(x+y,3) = C(x,3) + C(x,2)·y + x·C(y,2) + C(y,3)`.

The two middle terms are the reactant counts of reactions (1) and (2)
respectively, so this identity is precisely what makes the tri-molecular step
kernel a probability distribution. -/
theorem choose_three_split (x y : ℕ) :
    Nat.choose (x + y) 3
      = Nat.choose x 3 + Nat.choose x 2 * y + x * Nat.choose y 2 + Nat.choose y 3 := by
  rw [Nat.add_choose_eq]
  rw [show (3 : ℕ) = 2 + 1 from rfl, Finset.Nat.antidiagonal_succ]
  simp [Finset.Nat.antidiagonal_succ, Nat.choose_one_right, Nat.choose_zero_right,
    Finset.sum_insert]
  ring

/-- **Productive-mass identity.**

`C(x,2)·y + x·C(y,2)` counts the triples that trigger a *productive* reaction
(one of (1) or (2)); the unproductive triples are the homogeneous ones. Stated
without natural subtraction, the identity `C(x,2)·y + x·C(y,2) = xy(n-2)/2`
becomes the following, which is what yields the closed form
`q = 3xy/(n(n-1))` for the probability that an interaction event is
productive. -/
theorem productive_two_mul (x y : ℕ) :
    2 * (Nat.choose x 2 * y + x * Nat.choose y 2) + 2 * (x * y) = x * y * (x + y) := by
  cases x with
  | zero => simp
  | succ a =>
    cases y with
    | zero => simp
    | succ b =>
      have hx : 2 * Nat.choose (a + 1) 2 = (a + 1) * a := two_mul_choose_two_succ a
      have hy : 2 * Nat.choose (b + 1) 2 = (b + 1) * b := two_mul_choose_two_succ b
      calc 2 * (Nat.choose (a + 1) 2 * (b + 1) + (a + 1) * Nat.choose (b + 1) 2)
              + 2 * ((a + 1) * (b + 1))
          = (2 * Nat.choose (a + 1) 2) * (b + 1)
              + (a + 1) * (2 * Nat.choose (b + 1) 2)
              + 2 * ((a + 1) * (b + 1)) := by ring
        _ = (a + 1) * a * (b + 1) + (a + 1) * ((b + 1) * b)
              + 2 * ((a + 1) * (b + 1)) := by rw [hx, hy]
        _ = (a + 1) * (b + 1) * ((a + 1) + (b + 1)) := by ring

/-- The number of unordered triples is positive once the population is at
least three; this is the nonzero denominator of the step kernel. -/
theorem choose_three_pos {n : ℕ} (hn : 3 ≤ n) : 0 < Nat.choose n 3 :=
  Nat.choose_pos hn

section Sanity

/-! Guards against a vacuous or mis-transcribed statement: both identities are
claimed for *all* naturals, including the degenerate populations that the
paper's endgame analysis actually visits. -/

example : Nat.choose (0 + 0) 3
    = Nat.choose 0 3 + Nat.choose 0 2 * 0 + 0 * Nat.choose 0 2 + Nat.choose 0 3 := by decide
example : Nat.choose (2 + 1) 3
    = Nat.choose 2 3 + Nat.choose 2 2 * 1 + 2 * Nat.choose 1 2 + Nat.choose 1 3 := by decide
example : Nat.choose (1 + 2) 3
    = Nat.choose 1 3 + Nat.choose 1 2 * 2 + 1 * Nat.choose 2 2 + Nat.choose 2 3 := by decide
example : Nat.choose (5 + 4) 3
    = Nat.choose 5 3 + Nat.choose 5 2 * 4 + 5 * Nat.choose 4 2 + Nat.choose 4 3 := by decide

example : 2 * (Nat.choose 0 2 * 0 + 0 * Nat.choose 0 2) + 2 * (0 * 0) = 0 * 0 * (0 + 0) := by decide
example : 2 * (Nat.choose 2 2 * 1 + 2 * Nat.choose 1 2) + 2 * (2 * 1) = 2 * 1 * (2 + 1) := by decide
example : 2 * (Nat.choose 5 2 * 4 + 5 * Nat.choose 4 2) + 2 * (5 * 4) = 5 * 4 * (5 + 4) := by decide

end Sanity

end Tri
