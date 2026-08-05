/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.ByzantineRelaxedBridge

/-!
# Paper Lemma 9: the first Byzantine effective-rate bound

The paper writes the honest gap as `Δ = 2x - n`.  We use the equivalent
subtraction-free equality `n + Δ = 2x`.  The first theorem below is the
division-free form of the effective-rate estimate; the second transports it
through the exact physical-to-relaxed-rate bridge.
-/

namespace Tri.Byzantine

open scoped ENNReal

variable {n B : ℕ}

/-- Paper Lemma 9 in division-free count form:
`z / (y + z) ≤ Δ / (2n)`. -/
theorem lemma9_effectiveRate_cross
    {s : State n B} {Δ₀ Δ : ℕ}
    (hbudget : 16 * State.z s ≤ Δ₀)
    (hlower : Δ₀ ≤ 2 * Δ)
    (hupper : 2 * Δ ≤ n)
    (hgap : n + Δ = 2 * State.x s) :
    2 * n * State.z s ≤
      Δ * (State.y s + State.z s) := by
  have hz : 8 * State.z s ≤ Δ := by
    omega
  have htotal := State.total s
  have hyz : n ≤ 4 * (State.y s + State.z s) := by
    omega
  have hmul := Nat.mul_le_mul hz hyz
  nlinarith

/-- Effective idle-rate form of paper Lemma 9.  Since a `RelaxedRate` has
`fire + idle = 1`, this is exactly the paper inequality
`fire ≥ 1 - Δ / (2n)`, stated without division. -/
theorem lemma9_effectiveIdleRate_cross
    {s : State n B} {Δ₀ Δ : ℕ}
    (r : RelaxedRate)
    (hrate : IsPaperEffectiveRate r s)
    (hn : 0 < n)
    (hbudget : 16 * State.z s ≤ Δ₀)
    (hlower : Δ₀ ≤ 2 * Δ)
    (hupper : 2 * Δ ≤ n)
    (hgap : n + Δ = 2 * State.x s) :
    ((2 * n : ℕ) : ℝ≥0∞) * (r.idle : ℝ≥0∞) ≤
      (Δ : ℝ≥0∞) := by
  have hcross :=
    lemma9_effectiveRate_cross
      (s := s) hbudget hlower hupper hgap
  have htotal := State.total s
  have hyz_pos : 0 < State.y s + State.z s := by
    omega
  have hyz_ne : ((State.y s + State.z s : ℕ) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast hyz_pos.ne'
  have hyz_top :
      ((State.y s + State.z s : ℕ) : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  apply
    (ENNReal.mul_le_mul_iff_right hyz_ne hyz_top).mp
  simpa only [mul_comm] using
    (show
      (((2 * n : ℕ) : ℝ≥0∞) * (r.idle : ℝ≥0∞)) *
          ((State.y s + State.z s : ℕ) : ℝ≥0∞) ≤
          (Δ : ℝ≥0∞) *
            ((State.y s + State.z s : ℕ) : ℝ≥0∞) from by
      calc
        (((2 * n : ℕ) : ℝ≥0∞) * (r.idle : ℝ≥0∞)) *
            ((State.y s + State.z s : ℕ) : ℝ≥0∞) =
            ((2 * n : ℕ) : ℝ≥0∞) * (State.z s : ℝ≥0∞) := by
            rw [mul_assoc]
            simpa only [Nat.cast_add] using
              congrArg (fun q : ℝ≥0∞ =>
                ((2 * n : ℕ) : ℝ≥0∞) * q) hrate.idle_cross
        _ = ((2 * n * State.z s : ℕ) : ℝ≥0∞) := by
            push_cast
            ring
        _ ≤ ((Δ * (State.y s + State.z s) : ℕ) : ℝ≥0∞) := by
            exact_mod_cast hcross
        _ = (Δ : ℝ≥0∞) *
          ((State.y s + State.z s : ℕ) : ℝ≥0∞) := by
            push_cast
            ring)

end Tri.Byzantine
