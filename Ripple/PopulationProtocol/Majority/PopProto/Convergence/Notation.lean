/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Convergence Notation

Key quantities from Section 4 of Angluin-Aspnes-Eisenstat 2008:
- `u = x - y` : net majority (already `Config.gap`)
- `v = x + y = n - b` : number of opinionated agents
- `g = 1 / (n * (n - 1))` : probability normalization factor

We also define interaction type predicates (Table 1 of the paper)
and prove basic relationships between these quantities.
-/

import Ripple.PopulationProtocol.Majority.PopProto.Step

namespace PopProto

open State

namespace Config

variable {n : ℕ}

/-! ### Core quantities -/

/-- `v c` is the number of opinionated (non-blank) agents: `x + y`.
    In the paper's notation, `v = x + y = n - b`. -/
def v (c : Config n) : ℕ := c.x_count + c.y_count

/-- `u c` is the net majority as a natural-number gap.
    Alias for `gap`: `u = (x : ℤ) - (y : ℤ)`. -/
abbrev u (c : Config n) : ℤ := c.gap

/-- `v = n - b` when `x + b + y = n`. -/
theorem v_eq_sub_b (c : Config n) : (c.v : ℤ) = (n : ℤ) - (c.b_count : ℤ) := by
  unfold v
  have := c.sum_eq
  omega

/-- `b = n - v`. -/
theorem b_eq_sub_v (c : Config n) : c.b_count = n - c.v := by
  unfold v
  have := c.sum_eq
  omega

/-- `v ≤ n` always holds. -/
theorem v_le_n (c : Config n) : c.v ≤ n := by
  unfold v
  have := c.sum_eq
  omega

/-- `v ≥ 1` iff the configuration has at least one opinionated agent. -/
theorem v_pos_iff_hasOpinion (c : Config n) : 0 < c.v ↔ c.hasOpinion := by
  unfold v hasOpinion opinionated
  omega

/-- `|u| ≤ v` : the net majority is bounded by the number of opinionated agents. -/
theorem abs_u_le_v (c : Config n) : c.u.natAbs ≤ c.v := by
  unfold u gap v
  omega

/-- `u` and `v` have the same parity: `u = x - y`, `v = x + y`,
    so `v - u = 2y` and `v + u = 2x`. -/
theorem u_v_same_parity (c : Config n) : (c.u : ℤ) % 2 = (c.v : ℤ) % 2 := by
  unfold u gap v
  omega

/-! ### Interaction type classification

The paper classifies interactions by which counts change (Table 1).
We define predicates for each type based on the initiator-responder pair. -/

/-- An `(i, r)` interaction is of type `vb` (state-changing, x/y meets b)
    if it is `xb` or `yb`. These are the interactions that convert blanks. -/
def isVB (i r : State) : Prop := (i = x ∧ r = b) ∨ (i = y ∧ r = b)

/-- An `(i, r)` interaction is of type `xy` (state-changing, x meets y or vice versa)
    if it is `xy` or `yx`. These cancel an opinionated agent to blank. -/
def isXY (i r : State) : Prop := (i = x ∧ r = y) ∨ (i = y ∧ r = x)

/-- An interaction is state-changing iff the responder actually changes state. -/
def isStateChanging (i r : State) : Prop := isVB i r ∨ isXY i r

instance : Decidable (isVB i r) := by unfold isVB; exact inferInstance
instance : Decidable (isXY i r) := by unfold isXY; exact inferInstance
instance : Decidable (isStateChanging i r) := by unfold isStateChanging; exact inferInstance

/-- The only state-changing interactions are xb, yb, xy, yx. -/
theorem stateChanging_iff (i r : State) :
    isStateChanging i r ↔
      (i = x ∧ r = b) ∨ (i = y ∧ r = b) ∨
      (i = x ∧ r = y) ∨ (i = y ∧ r = x) := by
  unfold isStateChanging isVB isXY
  tauto

/-! ### How u and v change under each interaction -/

/-- Change in `u` (= x - y) for each interaction type.
    Only xy and yx interactions change u:
    - xb: Δu = 0 (x unchanged, y unchanged, b→x means x↑ b↓, but wait...)

    Actually, let's be more careful:
    - (x, x) → (x, x): Δx = 0, Δy = 0 → Δu = 0
    - (x, b) → (x, x): Δx = +1, Δy = 0, Δb = -1 → Δu = +1
    - (x, y) → (x, b): Δx = 0, Δy = -1, Δb = +1 → Δu = +1
    - (b, x) → (b, x): Δx = 0, Δy = 0 → Δu = 0
    - (b, b) → (b, b): no change → Δu = 0
    - (b, y) → (b, y): no change → Δu = 0
    - (y, b) → (y, y): Δx = 0, Δy = +1, Δb = -1 → Δu = -1
    - (y, x) → (y, b): Δx = -1, Δy = 0, Δb = +1 → Δu = -1
    - (y, y) → (y, y): no change → Δu = 0
-/
theorem u_change_xb (c : Config n) (c' : Config n) (h : c.step x b = some c') :
    c'.u = c.u + 1 := by
  simp [step, u, gap] at h ⊢; obtain ⟨_, rfl⟩ := h; simp; omega

theorem u_change_xy (c : Config n) (c' : Config n) (h : c.step x y = some c') :
    c'.u = c.u + 1 := by
  simp [step, u, gap] at h ⊢; obtain ⟨⟨_, _⟩, rfl⟩ := h; simp; omega

theorem u_change_yb (c : Config n) (c' : Config n) (h : c.step y b = some c') :
    c'.u = c.u - 1 := by
  simp [step, u, gap] at h ⊢; obtain ⟨_, rfl⟩ := h; simp; omega

theorem u_change_yx (c : Config n) (c' : Config n) (h : c.step y x = some c') :
    c'.u = c.u - 1 := by
  simp [step, u, gap] at h ⊢; obtain ⟨⟨_, _⟩, rfl⟩ := h; simp; omega

/-- Change in `v` (= x + y) for each interaction type.
    - xb: v increases by 1 (blank → x)
    - yb: v increases by 1 (blank → y)
    - xy: v decreases by 1 (y → b)
    - yx: v decreases by 1 (x → b)
    - all others: v unchanged
-/
theorem v_change_xb (c : Config n) (c' : Config n) (h : c.step x b = some c') :
    c'.v = c.v + 1 := by
  simp [step, v] at h ⊢; obtain ⟨_, rfl⟩ := h; simp; omega

theorem v_change_yb (c : Config n) (c' : Config n) (h : c.step y b = some c') :
    c'.v = c.v + 1 := by
  simp [step, v] at h ⊢; obtain ⟨_, rfl⟩ := h; simp; omega

theorem v_change_xy (c : Config n) (c' : Config n) (h : c.step x y = some c') :
    c'.v = c.v - 1 := by
  simp [step, v] at h ⊢; obtain ⟨⟨_, _⟩, rfl⟩ := h; simp; omega

theorem v_change_yx (c : Config n) (c' : Config n) (h : c.step y x = some c') :
    c'.v = c.v - 1 := by
  simp [step, v] at h ⊢; obtain ⟨⟨_, _⟩, rfl⟩ := h; simp; omega

/-- Non-state-changing interactions preserve both u and v. -/
theorem u_v_unchanged_xx (c : Config n) : (c.stepOrSelf x x).u = c.u ∧
    (c.stepOrSelf x x).v = c.v := by
  simp only [stepOrSelf, step, u, gap, v]; split_ifs <;> simp

theorem u_v_unchanged_bb (c : Config n) : (c.stepOrSelf b b).u = c.u ∧
    (c.stepOrSelf b b).v = c.v := by
  simp only [stepOrSelf, step, u, gap, v]; split_ifs <;> simp

theorem u_v_unchanged_yy (c : Config n) : (c.stepOrSelf y y).u = c.u ∧
    (c.stepOrSelf y y).v = c.v := by
  simp only [stepOrSelf, step, u, gap, v]; split_ifs <;> simp

theorem u_v_unchanged_bx (c : Config n) : (c.stepOrSelf b x).u = c.u ∧
    (c.stepOrSelf b x).v = c.v := by
  simp only [stepOrSelf, step, u, gap, v]; split_ifs <;> simp

theorem u_v_unchanged_by (c : Config n) : (c.stepOrSelf b y).u = c.u ∧
    (c.stepOrSelf b y).v = c.v := by
  simp only [stepOrSelf, step, u, gap, v]; split_ifs <;> simp

/-! ### The potential function f = u² + 2n

This is the central potential function from Section 4.4.
We work with `f` as a natural number since `u² ≥ 0` and `2n ≥ 0`. -/

/-- The potential function `f c = u² + 2n` from Section 4.4. -/
def potential (c : Config n) : ℕ := c.u.natAbs ^ 2 + 2 * n

/-- `f ≥ 2n` always holds. -/
theorem potential_ge_two_n (c : Config n) : c.potential ≥ 2 * n := by
  unfold potential; omega

/-- `f > 0` when `n ≥ 1`. -/
theorem potential_pos (c : Config n) (hn : n ≥ 1) : 0 < c.potential := by
  unfold potential; omega

/-- `f ≤ n² + 2n` since `|u| ≤ n`. -/
theorem potential_le (c : Config n) : c.potential ≤ n ^ 2 + 2 * n := by
  unfold potential
  have hub : c.u.natAbs ≤ n := by
    have hv := c.abs_u_le_v
    have hvn := c.v_le_n
    omega
  calc c.u.natAbs ^ 2 + 2 * n
      ≤ n ^ 2 + 2 * n := by
        apply Nat.add_le_add_right
        exact Nat.pow_le_pow_left hub 2

/-- At consensus (all X or all Y), `f = n² + 2n`. -/
theorem potential_at_allX (c : Config n) (h : c.allX) :
    c.potential = n ^ 2 + 2 * n := by
  unfold potential u gap allX at *
  obtain ⟨hx, hb, hy⟩ := h
  rw [hy, hx]
  simp

end Config
end PopProto
