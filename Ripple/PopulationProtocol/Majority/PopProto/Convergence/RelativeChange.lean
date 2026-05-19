/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Relative Change Lemma (Lemma 1)

Lemma 1 from Angluin-Aspnes-Eisenstat 2008, Section 4.3:

For positive reals `f` with `f + Δf > 0`:

  Δ(1/f) = 1/(f+Δf) - 1/f = -Δf / (f(f+Δf))

and the relative change satisfies:

  Δ(1/f) / (1/f) = -Δf / (f+Δf) = -Δf/f · 1/(1 + Δf/f)

When `|Δf/f|` is small, this is approximately `-Δf/f`.
-/

import Mathlib.Tactic

namespace PopProto

/-! ### Exact algebraic identities for 1/f changes -/

/-- Exact identity: `1/(f + Δf) - 1/f = -Δf / (f * (f + Δf))`. -/
theorem inv_change {f Δf : ℝ} (hf : f ≠ 0) (hf' : f + Δf ≠ 0) :
    1 / (f + Δf) - 1 / f = -Δf / (f * (f + Δf)) := by
  field_simp
  ring

/-- Relative change of `1/f`:
    `(1/(f+Δf) - 1/f) / (1/f) = -Δf / (f + Δf)`. -/
theorem inv_relative_change {f Δf : ℝ} (hf : f ≠ 0) (hf' : f + Δf ≠ 0) :
    (1 / (f + Δf) - 1 / f) / (1 / f) = -Δf / (f + Δf) := by
  field_simp
  ring

/-- Alternative form: `Δ(1/f) / (1/f) = (-Δf/f) / (1 + Δf/f)`.
    This is the form used in the series expansion of Lemma 1. -/
theorem inv_relative_change' {f Δf : ℝ} (hf : f ≠ 0) (hf' : f + Δf ≠ 0) :
    -Δf / (f + Δf) = (-Δf / f) / (1 + Δf / f) := by
  field_simp

/-- The key decomposition used in Lemmas 2 and 3:
    `Δ(1/f) / (1/f) = -Δf/f + (Δf/f)² / (1 + Δf/f)`.
    The first term is the linear approximation; the second is the error. -/
theorem inv_relative_change_decomp {f Δf : ℝ} (hf : f ≠ 0) (hf' : f + Δf ≠ 0) :
    -Δf / (f + Δf) = -Δf / f + Δf ^ 2 / (f * (f + Δf)) := by
  field_simp
  ring

/-- When `f + Δf > 0` and `f > 0`, the error term `Δf²/(f(f+Δf))` is non-negative. -/
theorem inv_change_error_nonneg {f Δf : ℝ} (hf : 0 < f) (hf' : 0 < f + Δf) :
    0 ≤ Δf ^ 2 / (f * (f + Δf)) := by
  positivity

/-- Bound on the error term when `|Δf| ≤ r·f` for some `r < 1`:
    `Δf²/(f(f+Δf)) ≤ r² · f / (f+Δf) ≤ r²/(1-r)`. -/
theorem inv_change_error_bound {f Δf r : ℝ} (hf : 0 < f)
    (hf' : 0 < f + Δf) (hr : |Δf| ≤ r * f) (hr1 : 0 ≤ r) :
    Δf ^ 2 / (f * (f + Δf)) ≤ r ^ 2 * f / (f + Δf) := by
  have hΔsq : Δf ^ 2 ≤ (r * f) ^ 2 := by
    have h1 : -|Δf| ≤ Δf := neg_abs_le Δf
    have h2 : Δf ≤ |Δf| := le_abs_self Δf
    nlinarith [sq_abs Δf, sq_abs (r * f), sq_nonneg (|Δf| - r * f)]
  -- Factor out 1/(f+Δf): both sides have this factor
  rw [show f * (f + Δf) = f * (f + Δf) from rfl]
  rw [show Δf ^ 2 / (f * (f + Δf)) = Δf ^ 2 / f / (f + Δf) from by
    rw [div_div]]
  apply div_le_div_of_nonneg_right _ hf'.le
  have : Δf ^ 2 ≤ r ^ 2 * f ^ 2 := by linarith [mul_pow r f 2]
  calc Δf ^ 2 / f = Δf ^ 2 * (1 / f) := by ring
    _ ≤ (r ^ 2 * f ^ 2) * (1 / f) := by apply mul_le_mul_of_nonneg_right this; positivity
    _ = r ^ 2 * f := by field_simp

end PopProto
