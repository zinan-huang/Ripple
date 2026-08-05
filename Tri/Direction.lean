/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Step

/-!
# The conditional direction of a productive reaction

This file formalizes the identity that opens Section 3.1 of the paper, and on
which every drift estimate in the analysis rests:

> the probability that an interaction triggers one of these (a productive
> reaction event) is `xy(x+y-2)/(2 C(n,3))`, and the probability that such a
> reaction event is reaction (1) is `(x-1)/(x+y-2) ≥ x/n`, provided `x ≥ y`.

Both halves are proved here, and both are stated **division-free and
subtraction-free**, which is what makes them usable at the degenerate
populations the paper's endgame visits.

## How the statements avoid division and truncation

Write the interior state as `x = a + 1` and `y = b + 1`, so that
`n = a + b + 2`, hence `n - 2 = a + b` and `x - 1 = a` *on the nose*, with no
truncated subtraction. The paper's ratio

    P[reaction (1) | productive] = (x-1)/(x+y-2)

is then the cross-multiplied identity `direction_cross_mul`, and the comparison
`(x-1)/(x+y-2) ≥ x/n` is the cross-multiplied inequality `direction_ge_cross`.
Cross-multiplying is not a weakening: since the denominators are positive
exactly when a productive reaction is possible, the multiplicative forms are
equivalent to the paper's ratio statements wherever those are defined, and they
remain meaningful where the paper's are not.

## Main results

* `direction_cross_mul` — `P[(1) | productive] = (x-1)/(x+y-2)`, cross-multiplied.
* `direction_ge_cross` — `(x-1)/(x+y-2) ≥ x/n` when `x ≥ y`, cross-multiplied.
* `productive_pos` — the productive mass is nonzero exactly on the interior,
  which is what makes the conditional probability well defined.

Reference: A. Condon, M. Hajiaghayi, D. Kirkpatrick, J. Mañuch,
*Approximate Majority Analyses using Tri-molecular Chemical Reaction Networks*,
Section 3.1, opening paragraph.
-/

namespace Tri

/-- The number of triples triggering reaction (1), at state `x = a+1`,
`y = b+1`. -/
abbrev upCount (a b : ℕ) : ℕ := Nat.choose (a + 1) 2 * (b + 1)

/-- The number of triples triggering reaction (2), at state `x = a+1`,
`y = b+1`. -/
abbrev downCount (a b : ℕ) : ℕ := (a + 1) * Nat.choose (b + 1) 2

/-- **The paper's conditional-direction identity**, cross-multiplied.

At state `x = a+1`, `y = b+1` we have `n = a+b+2`, so `x-1 = a` and
`x+y-2 = a+b`. The paper's

    P[reaction (1) | productive] = (x-1)/(x+y-2)

is exactly the statement that `up · (a+b) = a · (up + down)`. -/
theorem direction_cross_mul (a b : ℕ) :
    upCount a b * (a + b) = a * (upCount a b + downCount a b) := by
  have h1 : 2 * Nat.choose (a + 1) 2 = (a + 1) * a := two_mul_choose_two_succ a
  have h2 : 2 * Nat.choose (b + 1) 2 = (b + 1) * b := two_mul_choose_two_succ b
  have key : 2 * (upCount a b * (a + b)) = 2 * (a * (upCount a b + downCount a b)) := by
    simp only [upCount, downCount]
    calc 2 * (Nat.choose (a + 1) 2 * (b + 1) * (a + b))
        = (2 * Nat.choose (a + 1) 2) * ((b + 1) * (a + b)) := by ring
      _ = (a + 1) * a * ((b + 1) * (a + b)) := by rw [h1]
      _ = a * ((a + 1) * a * (b + 1) + (a + 1) * ((b + 1) * b)) := by ring
      _ = a * ((2 * Nat.choose (a + 1) 2) * (b + 1)
            + (a + 1) * (2 * Nat.choose (b + 1) 2)) := by rw [h1, h2]
      _ = 2 * (a * (Nat.choose (a + 1) 2 * (b + 1) + (a + 1) * Nat.choose (b + 1) 2)) := by
            ring
  omega

/-- **The paper's lower bound** `(x-1)/(x+y-2) ≥ x/n` when `x ≥ y`,
cross-multiplied.

At `x = a+1`, `y = b+1`, `n = a+b+2`, the hypothesis `x ≥ y` is `b ≤ a` and the
claim `n·(x-1) ≥ x·(x+y-2)` is `(a+b+2)·a ≥ (a+1)·(a+b)`. -/
theorem direction_ge_cross {a b : ℕ} (hab : b ≤ a) :
    (a + 1) * (a + b) ≤ (a + b + 2) * a := by
  nlinarith [hab]

/-- The productive mass is nonzero exactly on the interior: a productive
reaction needs both an `X` and a `Y`, and a third molecule to complete the
triple. This is what makes the conditional probability in
`direction_cross_mul` well defined. -/
theorem productive_pos {a b : ℕ} (h : 1 ≤ a + b) :
    0 < upCount a b + downCount a b := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · -- x = 1: only reaction (2) can fire, and it needs two `Y`s
    have hb : 1 ≤ b := by omega
    have : 0 < Nat.choose (b + 1) 2 := by
      have : 2 ≤ b + 1 := by omega
      exact Nat.choose_pos this
    simp only [downCount]
    omega
  · -- x ≥ 2: reaction (1) can fire, since there is a `Y` present
    have : 0 < Nat.choose (a + 1) 2 := Nat.choose_pos (by omega)
    have : 0 < upCount a b := by
      simp only [upCount]
      exact Nat.mul_pos this (by omega)
    omega

/-- **The odds-ratio identity.**

The ratio of the two productive reaction counts is exactly `(x-1)/(y-1)`:

    upCount / downCount = (x-1)/(y-1)    at  x = a+1, y = b+1

stated cross-multiplied (and hence subtraction-free) as `up · b = down · a`.

This is the sharpest arithmetic fact about the Tri chain, and it is what makes
the safety analysis purely combinatorial: the *harmonic base* at which the
geometric potential is exactly conserved is `ρ = upCount/downCount = a/b`, so
conservation reduces to a comparison of integers with no probability, no
division and no real analysis. -/
theorem odds_cross_mul (a b : ℕ) : upCount a b * b = downCount a b * a := by
  have h1 : 2 * Nat.choose (a + 1) 2 = (a + 1) * a := two_mul_choose_two_succ a
  have h2 : 2 * Nat.choose (b + 1) 2 = (b + 1) * b := two_mul_choose_two_succ b
  have key : 2 * (upCount a b * b) = 2 * (downCount a b * a) := by
    simp only [upCount, downCount]
    calc 2 * (Nat.choose (a + 1) 2 * (b + 1) * b)
        = (2 * Nat.choose (a + 1) 2) * ((b + 1) * b) := by ring
      _ = (a + 1) * a * ((b + 1) * b) := by rw [h1]
      _ = (a + 1) * (2 * Nat.choose (b + 1) 2) * a := by rw [h2]; ring
      _ = 2 * ((a + 1) * Nat.choose (b + 1) 2 * a) := by ring
  omega

/-- On the majority side the up-count dominates the down-count. Immediate from
`odds_cross_mul`, and the form the safety argument consumes. -/
theorem downCount_le_upCount {a b : ℕ} (hab : b ≤ a) :
    downCount a b * b ≤ upCount a b * b := by
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp
  · have h := odds_cross_mul a b
    calc downCount a b * b ≤ downCount a b * a := by
          exact Nat.mul_le_mul_left _ hab
      _ = upCount a b * b := h.symm

/-- **Uniform odds bound over a region.**

The pointwise harmonic base `b/a` varies with the state, but `feller_ruin` needs
a *single* base for the whole live region. Since `b/a` is decreasing in `a`, the
worst case over a region `aLo ≤ a`, `b ≤ bHi` sits at the corner, giving the
uniform base `bHi/aLo`.

Stated cross-multiplied, so it is an inequality between natural numbers with no
division and no subtraction. Verified exhaustively before proving. -/
theorem odds_uniform {a b aLo bHi : ℕ} (hLo : aLo ≤ a) (hHi : b ≤ bHi)
    (haLo : 0 < aLo) :
    downCount a b * aLo ≤ upCount a b * bHi := by
  have ha : 0 < a := lt_of_lt_of_le haLo hLo
  have hodds : upCount a b * b = downCount a b * a := odds_cross_mul a b
  have hmid : b * aLo ≤ a * bHi :=
    calc b * aLo ≤ bHi * aLo := Nat.mul_le_mul_right _ hHi
      _ = aLo * bHi := by ring
      _ ≤ a * bHi := Nat.mul_le_mul_right _ hLo
  have key : (downCount a b * aLo) * a ≤ (upCount a b * bHi) * a := by
    calc (downCount a b * aLo) * a = (downCount a b * a) * aLo := by ring
      _ = (upCount a b * b) * aLo := by rw [hodds]
      _ = upCount a b * (b * aLo) := by ring
      _ ≤ upCount a b * (a * bHi) := Nat.mul_le_mul_left _ hmid
      _ = (upCount a b * bHi) * a := by ring
  exact Nat.le_of_mul_le_mul_right key ha

/-- The two counts are exactly the numerators appearing in `triStep_up` and
`triStep_down`, so the identities above are statements about the actual step
distribution and not about a re-derived model. -/
theorem upCount_eq_triStep_numerator (a b : ℕ) :
    upCount a b = TripleKind.weight (a + 1) (b + 1) .xxy := rfl

theorem downCount_eq_triStep_numerator (a b : ℕ) :
    downCount a b = TripleKind.weight (a + 1) (b + 1) .xyy := rfl

end Tri
