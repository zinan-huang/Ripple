/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Budget arithmetic for the headline error

Each phase exports an error `Aᵢ · n⁻¹ ^ (aᵢ · γ)` with `aᵢ > c` for the final
headline exponent `c`.  `inv_rpow_third` turns such a per-phase bound into a
third of the headline budget `n⁻¹ ^ (c · γ)`, provided `n` is large enough that
`3 Aᵢ ≤ n ^ ((aᵢ - c) γ)`.  Three applications and `1/3 + 1/3 + 1/3 = 1` close
the budget.

The content is pure `ENNReal` rpow bookkeeping: split the exponent, factor out
the common `n⁻¹ ^ b`, and reduce to the natural-number threshold.
-/

namespace Tri

open scoped ENNReal

/-- **The one-third budget step.**  A per-phase error `A · n⁻¹ ^ a` is at most a
third of a shallower power `n⁻¹ ^ b` once `n ^ (a - b)` clears `3 A`. -/
theorem inv_rpow_third (A : ℝ≥0∞) (a b : ℝ) (n : ℕ)
    (hab : b ≤ a) (hn : 1 ≤ n)
    (hthresh : 3 * A ≤ (n : ℝ≥0∞) ^ (a - b)) :
    A * (n : ℝ≥0∞)⁻¹ ^ a ≤ (1 / 3) * (n : ℝ≥0∞)⁻¹ ^ b := by
  have hn1 : (1 : ℝ≥0∞) ≤ (n : ℝ≥0∞) := by exact_mod_cast hn
  have hn0 : (n : ℝ≥0∞) ≠ 0 := by
    have : (0 : ℝ≥0∞) < n := lt_of_lt_of_le one_pos hn1
    exact this.ne'
  have hntop : (n : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top n
  have hinv0 : (n : ℝ≥0∞)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr hntop
  have hinvtop : (n : ℝ≥0∞)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hn0
  -- The clearing factor `c = n ^ (a - b)` is in `[1, ∞)`.
  set c : ℝ≥0∞ := (n : ℝ≥0∞) ^ (a - b) with hc
  have hcge1 : (1 : ℝ≥0∞) ≤ c := by
    rw [hc]
    calc (1 : ℝ≥0∞) = (n : ℝ≥0∞) ^ (0 : ℝ) := by rw [ENNReal.rpow_zero]
      _ ≤ (n : ℝ≥0∞) ^ (a - b) :=
          ENNReal.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have hc0 : c ≠ 0 := (lt_of_lt_of_le one_pos hcge1).ne'
  have hctop : c ≠ ⊤ := by
    rw [hc]; exact ENNReal.rpow_ne_top_of_nonneg (by linarith) hntop
  -- Split the deep power into the shallow power times the clearing power.
  have hsplit : (n : ℝ≥0∞)⁻¹ ^ a
      = (n : ℝ≥0∞)⁻¹ ^ (a - b) * (n : ℝ≥0∞)⁻¹ ^ b := by
    rw [← ENNReal.rpow_add _ _ hinv0 hinvtop]
    congr 1; ring
  -- The clearing power is `c⁻¹`.
  have hclear : (n : ℝ≥0∞)⁻¹ ^ (a - b) = c⁻¹ := by
    rw [hc, ENNReal.inv_rpow]
  -- `A · c⁻¹ ≤ 1/3` from the threshold.
  have hkey : A * c⁻¹ ≤ 1 / 3 := by
    have hmul : 3 * A * c⁻¹ ≤ 1 := by
      calc 3 * A * c⁻¹ ≤ c * c⁻¹ := mul_le_mul_right' hthresh c⁻¹
        _ = 1 := ENNReal.mul_inv_cancel hc0 hctop
    rw [ENNReal.le_div_iff_mul_le (Or.inl (by norm_num)) (Or.inl (by norm_num))]
    calc A * c⁻¹ * 3 = 3 * A * c⁻¹ := by ring
      _ ≤ 1 := hmul
  -- Assemble.
  calc A * (n : ℝ≥0∞)⁻¹ ^ a
      = (A * (n : ℝ≥0∞)⁻¹ ^ (a - b)) * (n : ℝ≥0∞)⁻¹ ^ b := by rw [hsplit]; ring
    _ = (A * c⁻¹) * (n : ℝ≥0∞)⁻¹ ^ b := by rw [hclear]
    _ ≤ (1 / 3) * (n : ℝ≥0∞)⁻¹ ^ b := mul_le_mul_right' hkey _

/-- Three one-third pieces sum to the whole headline budget. -/
theorem three_thirds_le {x y z w : ℝ≥0∞}
    (hx : x ≤ (1 / 3) * w) (hy : y ≤ (1 / 3) * w) (hz : z ≤ (1 / 3) * w) :
    x + y + z ≤ w := by
  have hsum : x + y + z ≤ (1 / 3) * w + (1 / 3) * w + (1 / 3) * w :=
    add_le_add (add_le_add hx hy) hz
  refine hsum.trans_eq ?_
  rw [← add_mul, ← add_mul]
  have h1 : (1 / 3 + 1 / 3 + 1 / 3 : ℝ≥0∞) = 1 := by
    simp only [one_div]
    rw [(by ring : (3 : ℝ≥0∞)⁻¹ + 3⁻¹ + 3⁻¹ = 3 * 3⁻¹)]
    exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
  rw [h1, one_mul]

/-- **The assembled reconciled budget.**  The three per-phase errors
`4 n⁻¹^(γ/34)`, `6 n⁻¹^(γ/50)`, `2 n⁻¹^γ` sum to at most the headline budget
`n⁻¹^(γ/100)`, given the three clearing thresholds (each holds for `n` beyond an
explicit `n₀`).  The exponents carry the `γ` factor, so the thresholds scale up
with `γ`. -/
theorem reconciled_budget (n γ : ℕ) (hn : 1 ≤ n) (hγ : 1 ≤ γ)
    (e1 e2 e3 : ℝ≥0∞)
    (h1 : e1 ≤ 4 * (n : ℝ≥0∞)⁻¹ ^ ((1 / 34 : ℝ) * (γ : ℝ)))
    (h2 : e2 ≤ 6 * (n : ℝ≥0∞)⁻¹ ^ ((1 / 50 : ℝ) * (γ : ℝ)))
    (h3e : e3 ≤ 2 * (n : ℝ≥0∞)⁻¹ ^ ((1 : ℝ) * (γ : ℝ)))
    (ht1 : 3 * 4 ≤ (n : ℝ≥0∞) ^ ((1 / 34 : ℝ) * (γ : ℝ) - (1 / 100 : ℝ) * (γ : ℝ)))
    (ht2 : 3 * 6 ≤ (n : ℝ≥0∞) ^ ((1 / 50 : ℝ) * (γ : ℝ) - (1 / 100 : ℝ) * (γ : ℝ)))
    (ht3 : 3 * 2 ≤ (n : ℝ≥0∞) ^ ((1 : ℝ) * (γ : ℝ) - (1 / 100 : ℝ) * (γ : ℝ))) :
    e1 + e2 + e3 ≤ (n : ℝ≥0∞)⁻¹ ^ ((1 / 100 : ℝ) * (γ : ℝ)) := by
  have hγR : (0 : ℝ) ≤ (γ : ℝ) := Nat.cast_nonneg γ
  have hb1 : (1 / 100 : ℝ) * (γ : ℝ) ≤ (1 / 34 : ℝ) * (γ : ℝ) :=
    mul_le_mul_of_nonneg_right (by norm_num) hγR
  have hb2 : (1 / 100 : ℝ) * (γ : ℝ) ≤ (1 / 50 : ℝ) * (γ : ℝ) :=
    mul_le_mul_of_nonneg_right (by norm_num) hγR
  have hb3 : (1 / 100 : ℝ) * (γ : ℝ) ≤ (1 : ℝ) * (γ : ℝ) :=
    mul_le_mul_of_nonneg_right (by norm_num) hγR
  have p1 := inv_rpow_third 4 ((1 / 34 : ℝ) * γ) ((1 / 100 : ℝ) * γ) n hb1 hn ht1
  have p2 := inv_rpow_third 6 ((1 / 50 : ℝ) * γ) ((1 / 100 : ℝ) * γ) n hb2 hn ht2
  have p3 := inv_rpow_third 2 ((1 : ℝ) * γ) ((1 / 100 : ℝ) * γ) n hb3 hn ht3
  exact three_thirds_le (h1.trans p1) (h2.trans p2) (h3e.trans p3)

end Tri

#print axioms Tri.inv_rpow_third
#print axioms Tri.three_thirds_le
#print axioms Tri.reconciled_budget
