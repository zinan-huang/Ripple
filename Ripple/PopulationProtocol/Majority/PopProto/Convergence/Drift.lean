/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Multiplicative Drift and Convergence Time

Combines the algebraic drift bounds from RegionBounds and Supermartingale
to establish multiplicative drift in each region, yielding O(n log n)
convergence.

## Key results

- `multiplicative_drift_largeX`: `64·(x(b+y)-2yb) ≥ 13n·(3y+b+1)`,
  giving multiplicative drift `δ ≥ 13/(64(n-1))` on `potentialLargeX`.

- `multiplicative_drift_largeY`: Symmetric.

- `multiplicative_drift_largeB`: `16·(bv-2xy) ≥ 13nv`,
  giving multiplicative drift `δ ≥ 13/(16(n-1))` on `v`.

## Proof structure

The algebraic bounds give the drift coefficient for each region.
The convergence time follows from the multiplicative drift theorem
(Theorem 3 of Lengler 2020 / standard result):

  If E[Φ(C_{t+1}) | C_t] ≤ (1-δ)·Φ(C_t) for all non-target states,
  then E[T] ≤ (1 + ln(Φ_max/Φ_min)) / δ.

This theorem is a standard probability result; its formalization requires
measure-theoretic infrastructure (supermartingales + stopping times) that
is beyond the current scope. The algebraic prerequisites are complete.
-/

import Ripple.PopulationProtocol.Majority.PopProto.Convergence.RegionBounds
import Ripple.PopulationProtocol.Majority.PopProto.Convergence.Supermartingale
import Ripple.PopulationProtocol.Majority.PopProto.Probability.Scheduler

namespace PopProto

open State

namespace Config

variable {n : ℕ}

/-! ### Multiplicative drift in large-x region

When `8x ≥ 7n` and `b+y ≥ 1` (not yet consensus), the potential
`Φ = 3y + b + 1` satisfies:

  E[-ΔΦ] / Φ ≥ 13 / (64(n-1))

In integer form: `64 · (x(b+y) - 2yb) ≥ 13 · n · (3y+b+1)`.

Proof: from `large_x_drift_quantitative` (gives `16·drift ≥ 13n(b+y)`)
and `4(b+y) ≥ 3y+b+1` (since `3b+y ≥ 1` when `b+y ≥ 1`).

By the multiplicative drift theorem:
  E[convergence from large-x] ≤ ln(Φ_max) · 64(n-1) / 13
  ≤ ln(n/2+1) · 64(n-1) / 13 = O(n log n).
-/

/-- **Multiplicative drift in large-x**: `64·(x(b+y)-2yb) ≥ 13n·(3y+b+1)`.
    This is the key bound for Lemma 7: the drift coefficient is
    `δ ≥ 13/(64(n-1))`. -/
theorem multiplicative_drift_largeX (c : Config n) (hx : c.inLargeX) (hn : n ≥ 2)
    (hby : c.b_count + c.y_count ≥ 1) :
    64 * ((c.x_count : ℤ) * (↑c.b_count + ↑c.y_count) -
      2 * ↑c.y_count * ↑c.b_count) ≥
    13 * (n : ℤ) * (3 * ↑c.y_count + ↑c.b_count + 1) := by
  have h16 := large_x_drift_quantitative c hx hn
  have hby_z : (↑c.b_count : ℤ) + ↑c.y_count ≥ 1 := by exact_mod_cast hby
  -- 64·drift ≥ 4·16·drift ≥ 4·13n(b+y) = 52n(b+y)
  -- Need: 52n(b+y) ≥ 13n(3y+b+1), i.e., 4(b+y) ≥ 3y+b+1, i.e., 3b+y ≥ 1
  -- From b+y ≥ 1 and b ≥ 0: 3b+y ≥ b+y ≥ 1 ✓
  nlinarith

/-- **Multiplicative drift in large-y**: `64·(y(b+x)-2xb) ≥ 13n·(3x+b+1)`. -/
theorem multiplicative_drift_largeY (c : Config n) (hy : c.inLargeY) (hn : n ≥ 2)
    (hbx : c.b_count + c.x_count ≥ 1) :
    64 * ((c.y_count : ℤ) * (↑c.b_count + ↑c.x_count) -
      2 * ↑c.x_count * ↑c.b_count) ≥
    13 * (n : ℤ) * (3 * ↑c.x_count + ↑c.b_count + 1) := by
  have h16 := large_y_drift_quantitative c hy hn
  have hbx_z : (↑c.b_count : ℤ) + ↑c.x_count ≥ 1 := by exact_mod_cast hbx
  nlinarith

/-! ### Multiplicative drift in large-b region

When `8b ≥ 7n` and `v = x+y ≥ 1`, the opinionated count `v` satisfies:

  E[Δv] / v ≥ 13 / (16(n-1))

In integer form: `16·(bv - 2xy) ≥ 13·n·v`.

The potential for convergence analysis is `1/v`, which decreases at rate δ.
Starting from `v ≥ 1` and needing `v > n/8` (to exit large-b), the expected
exit time is `O(n · log(n))` by multiplicative drift on `v`. -/

/-- **Multiplicative drift in large-b on v**: `16·(bv - 2xy) ≥ 13nv`.
    This is `large_b_drift_quantitative` directly. -/
theorem multiplicative_drift_largeB (c : Config n) (hb : c.inLargeB) (hn : n ≥ 2) :
    16 * ((c.b_count : ℤ) * ↑c.v - 2 * ↑c.x_count * ↑c.y_count) ≥
    13 * (n : ℤ) * ↑c.v := by
  unfold v
  push_cast
  have h := large_b_drift_quantitative c hb hn
  linarith

/-! ### Central region (Lemma 2 coefficient)

In the central region, the potential function is `f = u² + 2n`.
From `lemma2_coefficient`: `(2u²+v)·16n ≥ 7vf`, which gives
the drift coefficient `α = 7/(16n)` for the supermartingale.

The expected exit time from the central region is `O(n log n)`.
This follows from the supermartingale construction M_t (Lemma 4),
which requires the full measure-theoretic machinery. -/

/-- **Central region drift**: `(2u²+v)·16n ≥ 7v·f`.
    This is `lemma2_coefficient` repackaged: the conditional expected
    relative decrease of `1/f` per vb interaction has coefficient
    at least `7/(16n)`. -/
theorem central_drift_coefficient (c : Config n) (hn : n ≥ 1) :
    (2 * c.u ^ 2 + (c.v : ℤ)) * (16 * (n : ℤ)) ≥
    7 * (c.v : ℤ) * (c.u ^ 2 + 2 * n) :=
  lemma2_coefficient c hn

/-! ### Maximum potentials by region

These bounds on the maximum potential determine the `log(Φ_max)`
factor in the multiplicative drift time bound.
-/

/-- In large-x, `potentialLargeX ≤ n/2 + 1`. -/
theorem potentialLargeX_le (c : Config n) (hx : c.inLargeX) :
    c.potentialLargeX ≤ n / 2 + 1 := by
  unfold potentialLargeX inLargeX at *
  have := c.sum_eq
  omega

/-- In large-y, `potentialLargeY ≤ n/2 + 1`. -/
theorem potentialLargeY_le (c : Config n) (hy : c.inLargeY) :
    c.potentialLargeY ≤ n / 2 + 1 := by
  unfold potentialLargeY inLargeY at *
  have := c.sum_eq
  omega

/-- In the central region, `f = u² + 2n ≤ n² + 2n`. -/
theorem central_potential_le (c : Config n) : c.potential ≤ n ^ 2 + 2 * n :=
  potential_le c

/-- Expand `Finset.univ.sum` over `State = {x, b, y}`. -/
private lemma sum_state_eq {α : Type*} [AddCommMonoid α] (f : State → α) :
    Finset.univ.sum f = f .x + f .b + f .y := by
  rw [show (Finset.univ : Finset State) = {.x, .b, .y} from by
    ext s; simp [Finset.mem_univ]; cases s <;> simp]
  rw [Finset.sum_insert (show State.x ∉ ({.b, .y} : Finset State) from by decide)]
  rw [Finset.sum_insert (show State.b ∉ ({.y} : Finset State) from by decide)]
  rw [Finset.sum_singleton, ← add_assoc]

/-! ### stepOrSelf preserves potential for non-state-changing interactions

For interactions where the responder doesn't change state (xx, bb, yy, bx, by),
`stepOrSelf` returns the original configuration. -/

private theorem stepOrSelf_xx (c : Config n) : c.stepOrSelf x x = c := by
  unfold stepOrSelf step; split_ifs <;> simp
private theorem stepOrSelf_bb (c : Config n) : c.stepOrSelf b b = c := by
  unfold stepOrSelf step; split_ifs <;> simp
private theorem stepOrSelf_yy (c : Config n) : c.stepOrSelf y y = c := by
  unfold stepOrSelf step; split_ifs <;> simp
private theorem stepOrSelf_bx (c : Config n) : c.stepOrSelf b x = c := by
  unfold stepOrSelf step; split_ifs <;> simp
private theorem stepOrSelf_by' (c : Config n) : c.stepOrSelf b y = c := by
  unfold stepOrSelf step; split_ifs <;> simp

/-! ### Individual weighted terms for potentialLargeX

Each state-changing interaction contributes a weighted term to the drift.
We prove each term individually, handling feasibility case analysis and
ℕ→ℤ subtraction casting. -/

private theorem term_potLargeX_xb (c : Config n) :
    (c.interactionCount x b : ℤ) *
    (↑(c.stepOrSelf x b).potentialLargeX - ↑c.potentialLargeX) =
    -(↑c.x_count * ↑c.b_count) := by
  simp only [interactionCount, countOf, show (x : State) ≠ b from by decide,
             ite_false, stepOrSelf, step, potentialLargeX]
  split_ifs with h
  · obtain ⟨_, hb⟩ := h
    simp only [Option.getD_some]; push_cast
    rw [show (↑(c.b_count - 1) : ℤ) = ↑c.b_count - 1 from Nat.cast_sub hb]; ring
  · simp only [Option.getD_none, sub_self, mul_zero]
    have : c.x_count = 0 ∨ c.b_count = 0 := by
      by_contra hc; push_neg at hc; exact h ⟨by omega, by omega⟩
    rcases this with h | h <;> simp [h]

private theorem term_potLargeX_xy (c : Config n) :
    (c.interactionCount x y : ℤ) *
    (↑(c.stepOrSelf x y).potentialLargeX - ↑c.potentialLargeX) =
    -(2 * ↑c.x_count * ↑c.y_count) := by
  simp only [interactionCount, countOf, show (x : State) ≠ y from by decide,
             ite_false, stepOrSelf, step, potentialLargeX]
  split_ifs with h
  · obtain ⟨_, hy⟩ := h
    simp only [Option.getD_some]; push_cast
    rw [show (↑(c.y_count - 1) : ℤ) = ↑c.y_count - 1 from Nat.cast_sub hy]; ring
  · simp only [Option.getD_none, sub_self, mul_zero]
    have : c.x_count = 0 ∨ c.y_count = 0 := by
      by_contra hc; push_neg at hc; exact h ⟨by omega, by omega⟩
    rcases this with h | h <;> simp [h]

private theorem term_potLargeX_yx (c : Config n) :
    (c.interactionCount y x : ℤ) *
    (↑(c.stepOrSelf y x).potentialLargeX - ↑c.potentialLargeX) =
    ↑c.y_count * ↑c.x_count := by
  simp only [interactionCount, countOf, show (y : State) ≠ x from by decide,
             ite_false, stepOrSelf, step, potentialLargeX]
  split_ifs with h
  · simp only [Option.getD_some]; push_cast; ring
  · simp only [Option.getD_none, sub_self, mul_zero]
    have : c.y_count = 0 ∨ c.x_count = 0 := by
      by_contra hc; push_neg at hc; exact h ⟨by omega, by omega⟩
    rcases this with h | h <;> simp [h]

private theorem term_potLargeX_yb (c : Config n) :
    (c.interactionCount y b : ℤ) *
    (↑(c.stepOrSelf y b).potentialLargeX - ↑c.potentialLargeX) =
    2 * ↑c.y_count * ↑c.b_count := by
  simp only [interactionCount, countOf, show (y : State) ≠ b from by decide,
             ite_false, stepOrSelf, step, potentialLargeX]
  split_ifs with h
  · obtain ⟨_, hb⟩ := h
    simp only [Option.getD_some]; push_cast
    rw [show (↑(c.b_count - 1) : ℤ) = ↑c.b_count - 1 from Nat.cast_sub hb]; ring
  · simp only [Option.getD_none, sub_self, mul_zero]
    have : c.y_count = 0 ∨ c.b_count = 0 := by
      by_contra hc; push_neg at hc; exact h ⟨by omega, by omega⟩
    rcases this with h | h <;> simp [h]

/-- **Bridge theorem**: The weighted sum of `potentialLargeX` changes over all
    interactions equals `-(x(b+y) - 2yb)`.

    This is the formal connection between the algebraic drift analysis and
    the one-step distribution: dividing by `totalPairs(n)` gives the expected
    change `E[ΔΦ] = -(x(b+y) - 2yb) / (n(n-1))`. -/
theorem weighted_drift_potentialLargeX (c : Config n) :
    (Finset.univ.sum fun s₁ : State =>
      Finset.univ.sum fun s₂ : State =>
        (c.interactionCount s₁ s₂ : ℤ) *
        (↑(c.stepOrSelf s₁ s₂).potentialLargeX - ↑c.potentialLargeX)) =
    -((c.x_count : ℤ) * (↑c.b_count + ↑c.y_count) -
      2 * ↑c.y_count * ↑c.b_count) := by
  simp only [sum_state_eq]
  rw [stepOrSelf_xx, stepOrSelf_bb, stepOrSelf_yy, stepOrSelf_bx, stepOrSelf_by']
  simp only [sub_self, mul_zero, zero_add, add_zero]
  simp only [term_potLargeX_xb, term_potLargeX_xy, term_potLargeX_yx, term_potLargeX_yb]
  ring

/-! ### Individual weighted terms for v -/

private theorem term_v_xb (c : Config n) :
    (c.interactionCount x b : ℤ) *
    (↑(c.stepOrSelf x b).v - ↑c.v) =
    ↑c.x_count * ↑c.b_count := by
  simp only [interactionCount, countOf, show (x : State) ≠ b from by decide,
             ite_false, stepOrSelf, step, v]
  split_ifs with h
  · simp only [Option.getD_some]; push_cast; ring
  · simp only [Option.getD_none, sub_self, mul_zero]
    have : c.x_count = 0 ∨ c.b_count = 0 := by
      by_contra hc; push_neg at hc; exact h ⟨by omega, by omega⟩
    rcases this with h | h <;> simp [h]

private theorem term_v_xy (c : Config n) :
    (c.interactionCount x y : ℤ) *
    (↑(c.stepOrSelf x y).v - ↑c.v) =
    -(↑c.x_count * ↑c.y_count) := by
  simp only [interactionCount, countOf, show (x : State) ≠ y from by decide,
             ite_false, stepOrSelf, step, v]
  split_ifs with h
  · obtain ⟨_, hy⟩ := h
    simp only [Option.getD_some]; push_cast
    rw [show (↑(c.y_count - 1) : ℤ) = ↑c.y_count - 1 from Nat.cast_sub hy]; ring
  · simp only [Option.getD_none, sub_self, mul_zero]
    have : c.x_count = 0 ∨ c.y_count = 0 := by
      by_contra hc; push_neg at hc; exact h ⟨by omega, by omega⟩
    rcases this with h | h <;> simp [h]

private theorem term_v_yx (c : Config n) :
    (c.interactionCount y x : ℤ) *
    (↑(c.stepOrSelf y x).v - ↑c.v) =
    -(↑c.y_count * ↑c.x_count) := by
  simp only [interactionCount, countOf, show (y : State) ≠ x from by decide,
             ite_false, stepOrSelf, step, v]
  split_ifs with h
  · obtain ⟨_, hx⟩ := h
    simp only [Option.getD_some]; push_cast
    rw [show (↑(c.x_count - 1) : ℤ) = ↑c.x_count - 1 from Nat.cast_sub hx]; ring
  · simp only [Option.getD_none, sub_self, mul_zero]
    have : c.y_count = 0 ∨ c.x_count = 0 := by
      by_contra hc; push_neg at hc; exact h ⟨by omega, by omega⟩
    rcases this with h | h <;> simp [h]

private theorem term_v_yb (c : Config n) :
    (c.interactionCount y b : ℤ) *
    (↑(c.stepOrSelf y b).v - ↑c.v) =
    ↑c.y_count * ↑c.b_count := by
  simp only [interactionCount, countOf, show (y : State) ≠ b from by decide,
             ite_false, stepOrSelf, step, v]
  split_ifs with h
  · simp only [Option.getD_some]; push_cast; ring
  · simp only [Option.getD_none, sub_self, mul_zero]
    have : c.y_count = 0 ∨ c.b_count = 0 := by
      by_contra hc; push_neg at hc; exact h ⟨by omega, by omega⟩
    rcases this with h | h <;> simp [h]

/-- **Bridge theorem for v**: The weighted sum of `v` changes over all
    interactions equals `bv - 2xy`. -/
theorem weighted_drift_v (c : Config n) :
    (Finset.univ.sum fun s₁ : State =>
      Finset.univ.sum fun s₂ : State =>
        (c.interactionCount s₁ s₂ : ℤ) *
        (↑(c.stepOrSelf s₁ s₂).v - ↑c.v)) =
    (c.b_count : ℤ) * (↑c.x_count + ↑c.y_count) -
    2 * ↑c.x_count * ↑c.y_count := by
  simp only [sum_state_eq]
  rw [stepOrSelf_xx, stepOrSelf_bb, stepOrSelf_yy, stepOrSelf_bx, stepOrSelf_by']
  simp only [sub_self, mul_zero, zero_add, add_zero]
  simp only [term_v_xb, term_v_xy, term_v_yx, term_v_yb]
  ring

/-! ### Individual weighted terms for potentialLargeY (symmetric to X) -/

private theorem term_potLargeY_xb (c : Config n) :
    (c.interactionCount x b : ℤ) *
    (↑(c.stepOrSelf x b).potentialLargeY - ↑c.potentialLargeY) =
    2 * ↑c.x_count * ↑c.b_count := by
  simp only [interactionCount, countOf, show (x : State) ≠ b from by decide,
             ite_false, stepOrSelf, step, potentialLargeY]
  split_ifs with h
  · obtain ⟨_, hb⟩ := h
    simp only [Option.getD_some]; push_cast
    rw [show (↑(c.b_count - 1) : ℤ) = ↑c.b_count - 1 from Nat.cast_sub hb]; ring
  · simp only [Option.getD_none, sub_self, mul_zero]
    have : c.x_count = 0 ∨ c.b_count = 0 := by
      by_contra hc; push_neg at hc; exact h ⟨by omega, by omega⟩
    rcases this with h | h <;> simp [h]

private theorem term_potLargeY_xy (c : Config n) :
    (c.interactionCount x y : ℤ) *
    (↑(c.stepOrSelf x y).potentialLargeY - ↑c.potentialLargeY) =
    ↑c.x_count * ↑c.y_count := by
  simp only [interactionCount, countOf, show (x : State) ≠ y from by decide,
             ite_false, stepOrSelf, step, potentialLargeY]
  split_ifs with h
  · simp only [Option.getD_some]; push_cast; ring
  · simp only [Option.getD_none, sub_self, mul_zero]
    have : c.x_count = 0 ∨ c.y_count = 0 := by
      by_contra hc; push_neg at hc; exact h ⟨by omega, by omega⟩
    rcases this with h | h <;> simp [h]

private theorem term_potLargeY_yx (c : Config n) :
    (c.interactionCount y x : ℤ) *
    (↑(c.stepOrSelf y x).potentialLargeY - ↑c.potentialLargeY) =
    -(2 * ↑c.y_count * ↑c.x_count) := by
  simp only [interactionCount, countOf, show (y : State) ≠ x from by decide,
             ite_false, stepOrSelf, step, potentialLargeY]
  split_ifs with h
  · obtain ⟨_, hx⟩ := h
    simp only [Option.getD_some]; push_cast
    rw [show (↑(c.x_count - 1) : ℤ) = ↑c.x_count - 1 from Nat.cast_sub hx]; ring
  · simp only [Option.getD_none, sub_self, mul_zero]
    have : c.y_count = 0 ∨ c.x_count = 0 := by
      by_contra hc; push_neg at hc; exact h ⟨by omega, by omega⟩
    rcases this with h | h <;> simp [h]

private theorem term_potLargeY_yb (c : Config n) :
    (c.interactionCount y b : ℤ) *
    (↑(c.stepOrSelf y b).potentialLargeY - ↑c.potentialLargeY) =
    -(↑c.y_count * ↑c.b_count) := by
  simp only [interactionCount, countOf, show (y : State) ≠ b from by decide,
             ite_false, stepOrSelf, step, potentialLargeY]
  split_ifs with h
  · obtain ⟨_, hb⟩ := h
    simp only [Option.getD_some]; push_cast
    rw [show (↑(c.b_count - 1) : ℤ) = ↑c.b_count - 1 from Nat.cast_sub hb]; ring
  · simp only [Option.getD_none, sub_self, mul_zero]
    have : c.y_count = 0 ∨ c.b_count = 0 := by
      by_contra hc; push_neg at hc; exact h ⟨by omega, by omega⟩
    rcases this with h | h <;> simp [h]

/-- **Bridge theorem for potentialLargeY**: The weighted sum of `potentialLargeY`
    changes over all interactions equals `-(y(b+x) - 2xb)`. -/
theorem weighted_drift_potentialLargeY (c : Config n) :
    (Finset.univ.sum fun s₁ : State =>
      Finset.univ.sum fun s₂ : State =>
        (c.interactionCount s₁ s₂ : ℤ) *
        (↑(c.stepOrSelf s₁ s₂).potentialLargeY - ↑c.potentialLargeY)) =
    -((c.y_count : ℤ) * (↑c.b_count + ↑c.x_count) -
      2 * ↑c.x_count * ↑c.b_count) := by
  simp only [sum_state_eq]
  rw [stepOrSelf_xx, stepOrSelf_bb, stepOrSelf_yy, stepOrSelf_bx, stepOrSelf_by']
  simp only [sub_self, mul_zero, zero_add, add_zero]
  simp only [term_potLargeY_xb, term_potLargeY_xy, term_potLargeY_yx, term_potLargeY_yb]
  ring

/-! ### Combined drift inequalities

These theorems combine the bridge theorems (weighted drift = algebraic expression)
with the algebraic drift bounds (multiplicative drift coefficient) to obtain
the key integer inequality: the weighted drift gives sufficient decrease
relative to the potential. Dividing both sides by `totalPairs(n) * Φ(c)` would
give the multiplicative drift coefficient `δ`. -/

/-- **Large-x combined**: weighted drift of potentialLargeX satisfies the
    multiplicative drift bound `64·(-ΔΦ) ≥ 13n·Φ`. -/
theorem expected_decrease_potentialLargeX (c : Config n) (hx : c.inLargeX) (hn : n ≥ 2)
    (hby : c.b_count + c.y_count ≥ 1) :
    64 * (-(Finset.univ.sum fun s₁ : State =>
      Finset.univ.sum fun s₂ : State =>
        (c.interactionCount s₁ s₂ : ℤ) *
        (↑(c.stepOrSelf s₁ s₂).potentialLargeX - ↑c.potentialLargeX))) ≥
    13 * (n : ℤ) * ↑c.potentialLargeX := by
  rw [weighted_drift_potentialLargeX]; simp only [neg_neg, potentialLargeX]
  exact multiplicative_drift_largeX c hx hn hby

/-- **Large-y combined**: weighted drift of potentialLargeY satisfies the
    multiplicative drift bound `64·(-ΔΦ) ≥ 13n·Φ`. -/
theorem expected_decrease_potentialLargeY (c : Config n) (hy : c.inLargeY) (hn : n ≥ 2)
    (hbx : c.b_count + c.x_count ≥ 1) :
    64 * (-(Finset.univ.sum fun s₁ : State =>
      Finset.univ.sum fun s₂ : State =>
        (c.interactionCount s₁ s₂ : ℤ) *
        (↑(c.stepOrSelf s₁ s₂).potentialLargeY - ↑c.potentialLargeY))) ≥
    13 * (n : ℤ) * ↑c.potentialLargeY := by
  rw [weighted_drift_potentialLargeY]; simp only [neg_neg, potentialLargeY]
  exact multiplicative_drift_largeY c hy hn hbx

/-- **Large-b combined**: weighted drift of v satisfies the multiplicative
    drift bound `16·Δv ≥ 13n·v` (v increases in large-b). -/
theorem expected_increase_v (c : Config n) (hb : c.inLargeB) (hn : n ≥ 2) :
    16 * (Finset.univ.sum fun s₁ : State =>
      Finset.univ.sum fun s₂ : State =>
        (c.interactionCount s₁ s₂ : ℤ) *
        (↑(c.stepOrSelf s₁ s₂).v - ↑c.v)) ≥
    13 * (n : ℤ) * ↑c.v := by
  rw [weighted_drift_v]
  exact multiplicative_drift_largeB c hb hn

/-! ### Convergence time constants

From the multiplicative drift theorem with drift `δ ≥ 13/(64(n-1))`
and maximum potential `Φ_max ≤ n/2 + 1`:

  E[time in region] ≤ (1 + ln(n/2+1)) / δ
                     ≤ (1 + ln n) · 64(n-1) / 13
                     ≈ 5n · ln n

The paper uses three regions (large-x, large-y, large-b) plus the
central region, each contributing O(n log n). The total is O(n log n).

Specifically (Theorem 1 of AAE 2008):
  Pr[τ* ≥ 6769n·ln(n+2) + 6773cn·ln n + 2552n] ≤ 5n⁻ᶜ

**Formalized (zero sorry):**
1. Algebraic drift bounds for all regions
2. Bridge theorems: weighted drift = algebraic expression via stepOrSelf
3. Combined inequalities: multiplicative drift in integer form
4. Region classification and mutual exclusivity

**Completed (in Expected.lean):**
- Express weighted ℤ-drift as ℝ-valued PMF expectation ✓
- Multiplicative drift in ℝ for all three regions ✓

**Remaining (measure theory gap):**
- Construct the supermartingale M_t
- Apply multiplicative drift theorem / Doob's inequality
- Stopping times and union bound → Theorem 1
-/

/-- **Region coverage**: every configuration is in exactly one region
    (central, large-b, large-x, or large-y), or is at consensus.
    This is obvious from the definitions but useful for the union bound. -/
theorem region_classification (c : Config n) (hn : n ≥ 2) :
    c.inCentral ∨ c.inLargeB ∨ c.inLargeX ∨ c.inLargeY := by
  unfold inCentral
  by_cases hb : c.inLargeB
  · exact Or.inr (Or.inl hb)
  · by_cases hx : c.inLargeX
    · exact Or.inr (Or.inr (Or.inl hx))
    · by_cases hy : c.inLargeY
      · exact Or.inr (Or.inr (Or.inr hy))
      · exact Or.inl ⟨hb, hx, hy⟩

/-- At most one of large-b, large-x, large-y can hold (since each
    requires ≥ 7/8 of n, and two would exceed n). -/
theorem at_most_one_large (c : Config n) (hn : n ≥ 2) :
    ¬(c.inLargeB ∧ c.inLargeX) ∧
    ¬(c.inLargeB ∧ c.inLargeY) ∧
    ¬(c.inLargeX ∧ c.inLargeY) := by
  unfold inLargeB inLargeX inLargeY
  have := c.sum_eq
  constructor <;> [skip; constructor] <;> intro ⟨h1, h2⟩ <;> omega

/-! ### Quantitative drift for 1/v in large-b

For the 1/v potential in the large-b region, we need:
  `bv(v-1) - 2xy(v+1) ≥ 5n(v²-1)/16`

This gives the multiplicative contraction rate `δ = 5/(16(n-1))` for `1/v`.

The SOS certificate uses:
- `4xy ≤ v²` (AM-GM: `(x-y)² ≥ 0` gives `4xy ≤ (x+y)² = v²`)
- `n ≥ 8v` (from `8b ≥ 7n` and `b = n - v`)
- `8v² - 15v + 5 ≥ 0` for `v ≥ 2` -/

/-- **Reciprocal drift bound**: In large-b with `v ≥ 2`,
    `16(bv(v-1) - 2xy(v+1)) ≥ 5n(v²-1)`.
    This is the key integer inequality for the `1/v` drift. -/
theorem large_b_reciprocal_drift (c : Config n) (hb : c.inLargeB)
    (hv2 : c.v ≥ 2) :
    16 * ((c.b_count : ℤ) * ↑c.v * (↑c.v - 1) -
      2 * ↑c.x_count * ↑c.y_count * (↑c.v + 1)) ≥
    5 * (n : ℤ) * (↑c.v ^ 2 - 1) := by
  unfold inLargeB at hb; unfold v at hv2 ⊢
  have hsum := c.sum_eq
  -- Key substitution: b = n - (x + y)
  -- Key facts for nlinarith:
  -- (1) 4xy ≤ (x+y)² from (x-y)² ≥ 0
  -- (2) n ≥ 8(x+y) from 8b ≥ 7n
  -- (3) 8(x+y)² - 15(x+y) + 5 ≥ 0 for x+y ≥ 2
  have hx : (c.x_count : ℤ) ≥ 0 := Int.natCast_nonneg _
  have hy : (c.y_count : ℤ) ≥ 0 := Int.natCast_nonneg _
  have hsum_z : (c.x_count : ℤ) + ↑c.b_count + ↑c.y_count = ↑n := by exact_mod_cast hsum
  have hb_large : 8 * (c.b_count : ℤ) ≥ 7 * ↑n := by exact_mod_cast hb
  have hv_ge : (c.x_count : ℤ) + ↑c.y_count ≥ 2 := by exact_mod_cast hv2
  -- Eliminate b: b = n - x - y
  have hbeq : (c.b_count : ℤ) = ↑n - ↑c.x_count - ↑c.y_count := by linarith
  rw [hbeq]; push_cast
  -- n ≥ 8v (from 8b ≥ 7n and b = n - v)
  have hn8 : (n : ℤ) ≥ 8 * (↑c.x_count + ↑c.y_count) := by linarith
  -- SOS decomposition: goal = 8·h₁ + h₂ + 8·h₃ where
  --   h₁ = (v+1)(x-y)²  ≥ 0
  --   h₂ = (n-8v)(v-1)(11v-5) ≥ 0
  --   h₃ = v(8v²-15v+5) ≥ 0
  have h₁ : ((c.x_count : ℤ) + ↑c.y_count + 1) *
      ((↑c.x_count - ↑c.y_count) ^ 2) ≥ 0 :=
    mul_nonneg (by linarith) (sq_nonneg _)
  have h₂ : ((n : ℤ) - 8 * (↑c.x_count + ↑c.y_count)) *
      ((↑c.x_count + ↑c.y_count) - 1) *
      (11 * (↑c.x_count + ↑c.y_count) - 5) ≥ 0 :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  have h₃ : ((c.x_count : ℤ) + ↑c.y_count) *
      (8 * (↑c.x_count + ↑c.y_count) ^ 2 -
       15 * (↑c.x_count + ↑c.y_count) + 5) ≥ 0 :=
    mul_nonneg (by linarith)
      (by nlinarith [mul_nonneg (show (↑c.x_count + ↑c.y_count : ℤ) ≥ 0 from by linarith)
                                (show (↑c.x_count + ↑c.y_count : ℤ) - 2 ≥ 0 from by linarith)])
  nlinarith [h₁, h₂, h₃]

/-- For `v = 1` in large-b, the `1/v` drift is simpler: just `-b/2`.
    The bound `b ≥ 7n/8` gives `E[Δ(1/v)] ≤ -7/(16(n-1)v)`. -/
theorem large_b_reciprocal_drift_v1 (c : Config n) (hb : c.inLargeB)
    (hv1 : c.v = 1) :
    c.x_count * c.y_count = 0 := by
  unfold v at hv1
  rcases Nat.eq_zero_or_pos c.x_count with hx | hx
  · simp [hx]
  · have : c.y_count = 0 := by omega
    simp [this]

end Config
end PopProto
