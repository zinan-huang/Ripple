/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Change in Potential Function f = u² + 2n

This file computes how the potential function `f = u² + 2n` changes
under each type of interaction. These calculations are the foundation
for Lemmas 2 and 3 of Angluin-Aspnes-Eisenstat 2008.

## Key results

For `f = u² + 2n`:

- `Δf` for `vb` interactions (xb, yb): `Δf = ±2u + 1` (since `Δu = ±1`)
- `Δf` for `xy` interactions (xy, yx): `Δf = ±2u + 1` (since `Δu = ±1`)

More precisely:
- xb: u → u+1, so Δ(u²) = (u+1)² - u² = 2u+1, hence Δf = 2u+1
- xy: u → u+1, so Δ(u²) = 2u+1, hence Δf = 2u+1
- yb: u → u-1, so Δ(u²) = (u-1)² - u² = -2u+1, hence Δf = -2u+1
- yx: u → u-1, so Δ(u²) = -2u+1, hence Δf = -2u+1

## Expected values (Section 4.4)

Conditioned on `I^vb` (an xb or yb interaction):
  E[Δf | I^vb] = E[Δ(u² + 2n) | I^vb]

An xb interaction occurs with probability proportional to x·b,
and a yb interaction with probability proportional to y·b.
So:
  E[Δf | I^vb] = (x·b·(2u+1) + y·b·(-2u+1)) / (x·b + y·b)
               = b·(x(2u+1) + y(-2u+1)) / (b·(x+y))
               = (x(2u+1) - y(2u-1)) / v
               = (2u(x-y) + (x+y)) / v    [since x-y = u]
               = (2u² + v) / v
               = 2u²/v + 1

Similarly for `I^xy`:
  E[Δf | I^xy] = (x·y·(2u+1) + y·x·(-2u+1)) / (x·y + y·x)
               = (2u+1 + (-2u+1)) / 2
                 [wait, need to be more careful with conditional probabilities]

  An xy interaction: Δu = +1 (responder y → b)
  A yx interaction: Δu = -1 (responder x → b)
  Prob of xy given I^xy: x·y / (x·y + y·x) = 1/2
  Prob of yx given I^xy: y·x / (x·y + y·x) = 1/2

  E[Δf | I^xy] = (1/2)(2u+1) + (1/2)(-2u+1) = 1

These match the paper's calculations on p. 92.
-/

import Ripple.PopulationProtocol.Majority.PopProto.Convergence.Notation
import Mathlib.Tactic

namespace PopProto

open State

namespace Config

variable {n : ℕ}

/-! ### Δ(u²) for each interaction type

Since `u` is an integer, we compute `Δ(u²) = u'² - u²` where `u' = u ± 1`. -/

/-- When u changes by +1: Δ(u²) = 2u + 1. -/
theorem sq_change_plus_one (u : ℤ) : (u + 1) ^ 2 - u ^ 2 = 2 * u + 1 := by ring

/-- When u changes by -1: Δ(u²) = -2u + 1. -/
theorem sq_change_minus_one (u : ℤ) : (u - 1) ^ 2 - u ^ 2 = -2 * u + 1 := by ring

/-! ### Δf for each state-changing interaction

We express Δf as an integer, where `f = u² + 2n` and only `u²` changes. -/

/-- Core lemma: `(potential c' : ℤ) - potential c` when `c'.u = c.u + d`. -/
private theorem delta_potential_of_u_change (c c' : Config n) (d : ℤ)
    (hd : c'.u = c.u + d) :
    (c'.potential : ℤ) - (c.potential : ℤ) = 2 * d * c.u + d ^ 2 := by
  have h1 : c'.u = c.u + d := hd
  -- Express potential in terms of u² using Int.natAbs_sq
  have lhs : (c'.potential : ℤ) = c'.u ^ 2 + 2 * n := by
    simp [potential, Int.natAbs_sq]
  have rhs : (c.potential : ℤ) = c.u ^ 2 + 2 * n := by
    simp [potential, Int.natAbs_sq]
  rw [lhs, rhs, h1]; ring

/-- Δf for xb interaction: `f' - f = 2u + 1`. -/
theorem delta_f_xb (c : Config n) (c' : Config n) (h : c.step x b = some c') :
    (c'.potential : ℤ) - (c.potential : ℤ) = 2 * c.u + 1 := by
  have := delta_potential_of_u_change c c' 1 (u_change_xb c c' h)
  linarith

/-- Δf for yb interaction: `f' - f = -2u + 1`. -/
theorem delta_f_yb (c : Config n) (c' : Config n) (h : c.step y b = some c') :
    (c'.potential : ℤ) - (c.potential : ℤ) = -2 * c.u + 1 := by
  have hu := u_change_yb c c' h -- c'.u = c.u - 1
  have := delta_potential_of_u_change c c' (-1) (by linarith)
  linarith

/-- Δf for xy interaction: `f' - f = 2u + 1`. -/
theorem delta_f_xy (c : Config n) (c' : Config n) (h : c.step x y = some c') :
    (c'.potential : ℤ) - (c.potential : ℤ) = 2 * c.u + 1 := by
  have := delta_potential_of_u_change c c' 1 (u_change_xy c c' h)
  linarith

/-- Δf for yx interaction: `f' - f = -2u + 1`. -/
theorem delta_f_yx (c : Config n) (c' : Config n) (h : c.step y x = some c') :
    (c'.potential : ℤ) - (c.potential : ℤ) = -2 * c.u + 1 := by
  have hu := u_change_yx c c' h
  have := delta_potential_of_u_change c c' (-1) (by linarith)
  linarith

/-! ### Expected values of Δf and (Δf)²

These are the key intermediate calculations for Lemmas 2 and 3.
We compute the probability-weighted sums over interaction types.

Notation: x = c.x_count, y = c.y_count, b = c.b_count, u = x - y, v = x + y.

For vb interactions (xb with weight x·b, yb with weight y·b):
  E[Δf | I^vb] = (x·b·(2u+1) + y·b·(-2u+1)) / (x·b + y·b)

Numerator = b·(x·(2u+1) + y·(-2u+1))
          = b·(2ux - 2uy + x + y)      [since x-y = u as integers]
          = b·(2u·u + v)
          = b·(2u² + v)

So: E[Δf | I^vb] = (2u² + v) / v  (after dividing by b·v = b·(x+y))
                  = 2u²/v + 1

For xy interactions (xy with weight x·y, yx with weight y·x):
  E[Δf | I^xy] = (x·y·(2u+1) + y·x·(-2u+1)) / (x·y + y·x)
               = x·y·((2u+1) + (-2u+1)) / (2·x·y)
               = 2 / 2 = 1

These are proven as algebraic identities below.
-/

/-- The weighted sum of Δf over vb interactions equals `b * (2u² + v)` (as ℤ),
    where the weights are interaction counts `x·b` and `y·b`.

    That is: `x·b·(2u+1) + y·b·(-2u+1) = b·(2u² + v)`.
    Here u = x-y (as ℤ) and v = x+y (as ℕ). -/
theorem weighted_delta_f_vb (c : Config n) :
    (c.x_count : ℤ) * c.b_count * (2 * c.u + 1) +
    (c.y_count : ℤ) * c.b_count * (-2 * c.u + 1) =
    (c.b_count : ℤ) * (2 * c.u ^ 2 + c.v) := by
  unfold u gap v
  push_cast
  ring

/-- The weighted sum of (Δf)² over vb interactions:
    `x·b·(2u+1)² + y·b·(-2u+1)² = b·((x+y)·(2u+1)²·... )`

    More precisely:
    `x·b·(2u+1)² + y·b·(2u-1)² = b·(x·(2u+1)² + y·(2u-1)²)`
    `= b·(4u²(x+y) + 4u(x-y) + (x+y))`    [expanding]
    `= b·(4u²·v + 4u² + v)`
    `= b·(4u²(v+1) + v)`  hmm, let me recompute...

    x(2u+1)² + y(2u-1)² = x(4u²+4u+1) + y(4u²-4u+1)
                         = 4u²(x+y) + 4u(x-y) + (x+y)
                         = 4u²·v + 4u·u + v     [since x-y = u, x+y = v]
                         = 4u²v + 4u² + v

    So: x·b·(2u+1)² + y·b·(-2u+1)² = b·(4u²v + 4u² + v)
                                     = b·(4u²(v+1) + v)  -/
theorem weighted_delta_f_sq_vb (c : Config n) :
    (c.x_count : ℤ) * c.b_count * (2 * c.u + 1) ^ 2 +
    (c.y_count : ℤ) * c.b_count * (-2 * c.u + 1) ^ 2 =
    (c.b_count : ℤ) * (4 * c.u ^ 2 * c.v + 4 * c.u ^ 2 + c.v) := by
  unfold u gap v
  push_cast
  ring

/-- The weighted sum of Δf over xy interactions is zero:
    `x·y·(2u+1) + y·x·(-2u+1) = 2·x·y`.

    That is, E[Δf | I^xy] = 1 (after dividing by 2xy). -/
theorem weighted_delta_f_xy (c : Config n) :
    (c.x_count : ℤ) * c.y_count * (2 * c.u + 1) +
    (c.y_count : ℤ) * c.x_count * (-2 * c.u + 1) =
    2 * (c.x_count : ℤ) * c.y_count := by
  unfold u gap
  push_cast
  ring

/-- The weighted sum of (Δf)² over xy interactions:
    `x·y·(2u+1)² + y·x·(-2u+1)² = 2·x·y·(4u²+1)`.

    More precisely:
    x·y·(2u+1)² + y·x·(2u-1)² = xy·((2u+1)² + (2u-1)²)
                                = xy·(4u²+4u+1 + 4u²-4u+1)
                                = xy·(8u²+2)
                                = 2xy·(4u²+1) -/
theorem weighted_delta_f_sq_xy (c : Config n) :
    (c.x_count : ℤ) * c.y_count * (2 * c.u + 1) ^ 2 +
    (c.y_count : ℤ) * c.x_count * (-2 * c.u + 1) ^ 2 =
    2 * (c.x_count : ℤ) * c.y_count * (4 * c.u ^ 2 + 1) := by
  unfold u gap
  push_cast
  ring

/-! ### Bounds on |Δf/f|

The paper (p. 92) shows `|Δf/f| = O(1/√n)`.
Since `|Δu| ≤ 1`, we have `|Δf| = |±2u+1| ≤ 2|u|+1`.
And `f = u²+2n ≥ 2n`, so `|Δf/f| ≤ (2|u|+1)/(u²+2n)`.

The maximum of `(2|u|+1)/(u²+2n)` over `u` occurs at `|u| = Θ(√n)`,
giving `|Δf/f| = O(1/√n)`. -/

/-- Helper: `|2u + 1| ≤ 2 * natAbs u + 1` for any integer `u`. -/
private theorem abs_two_u_add_one (u : ℤ) :
    |2 * u + 1| ≤ 2 * (u.natAbs : ℤ) + 1 := by
  rw [← Int.abs_eq_natAbs]
  rw [abs_le]; constructor
  · linarith [neg_abs_le u]
  · linarith [le_abs_self u]

/-- Helper: `|-2u + 1| ≤ 2 * natAbs u + 1` for any integer `u`. -/
private theorem abs_neg_two_u_add_one (u : ℤ) :
    |-2 * u + 1| ≤ 2 * (u.natAbs : ℤ) + 1 := by
  rw [← Int.abs_eq_natAbs]
  rw [abs_le]; constructor
  · linarith [le_abs_self u]
  · linarith [neg_abs_le u]

/-- `|Δf| ≤ 2|u| + 1` for any state-changing interaction. -/
theorem abs_delta_f_le (c : Config n) (c' : Config n) (i r : State)
    (h : c.step i r = some c') (hsc : isStateChanging i r) :
    |(c'.potential : ℤ) - (c.potential : ℤ)| ≤ 2 * (c.u.natAbs : ℤ) + 1 := by
  unfold isStateChanging isVB isXY at hsc
  rcases hsc with (⟨hi, hr⟩ | ⟨hi, hr⟩) | (⟨hi, hr⟩ | ⟨hi, hr⟩) <;>
    subst hi <;> subst hr
  · rw [delta_f_xb c c' h]; exact abs_two_u_add_one c.u
  · rw [delta_f_yb c c' h]; exact abs_neg_two_u_add_one c.u
  · rw [delta_f_xy c c' h]; exact abs_two_u_add_one c.u
  · rw [delta_f_yx c c' h]; exact abs_neg_two_u_add_one c.u

end Config
end PopProto
