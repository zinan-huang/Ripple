/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.InfectionActiveCount
import Tri.ProdBound

/-!
# Scalar bounds for all-active infection interactions

The exact finite-population all-active probability is bounded by the cubic
with-replacement envelope used in the paper.
-/

namespace Tri

open scoped ENNReal

theorem six_mul_choose_three (k : ℕ) :
    6 * Nat.choose k 3 = k * (k - 1) * (k - 2) := by
  cases k with
  | zero => simp
  | succ k =>
      cases k with
      | zero => norm_num [Nat.choose]
      | succ k =>
          simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel,
            Nat.add_sub_cancel_left] using
            six_mul_choose_three_add_two k

/-- Cross-multiplied natural-number core of the cubic envelope. -/
theorem choose_three_mul_cube_le
    (n A : ℕ) (hA : A ≤ n) :
    Nat.choose A 3 * n ^ 3 ≤
      Nat.choose n 3 * A ^ 3 := by
  by_cases hA3 : 3 ≤ A
  · obtain ⟨a, ha⟩ : ∃ a, A = a + 3 :=
      ⟨A - 3, by omega⟩
    obtain ⟨b, hb⟩ : ∃ b, n = b + 3 :=
      ⟨n - 3, by omega⟩
    subst A
    subst n
    have hab : a ≤ b := by omega
    have h1 :
        ((a + 3) - 1) * (b + 3) ≤
          (a + 3) * ((b + 3) - 1) := by
      have ha1 : a + 3 - 1 = a + 2 := by omega
      have hb1 : b + 3 - 1 = b + 2 := by omega
      rw [ha1, hb1]
      nlinarith
    have h2 :
        ((a + 3) - 2) * (b + 3) ≤
          (a + 3) * ((b + 3) - 2) := by
      have ha2 : a + 3 - 2 = a + 1 := by omega
      have hb2 : b + 3 - 2 = b + 1 := by omega
      rw [ha2, hb2]
      nlinarith
    have hproducts :
        ((a + 3) * (b + 3)) *
            (((a + 3) - 1) * (b + 3)) *
            (((a + 3) - 2) * (b + 3)) ≤
          ((a + 3) * (b + 3)) *
            ((a + 3) * ((b + 3) - 1)) *
            ((a + 3) * ((b + 3) - 2)) :=
      Nat.mul_le_mul
        (Nat.mul_le_mul le_rfl h1) h2
    have hfactor :
        (a + 3) * ((a + 3) - 1) * ((a + 3) - 2) * (b + 3) ^ 3 ≤
          (b + 3) * ((b + 3) - 1) * ((b + 3) - 2) * (a + 3) ^ 3 := by
      calc
        (a + 3) * ((a + 3) - 1) * ((a + 3) - 2) * (b + 3) ^ 3 =
            ((a + 3) * (b + 3)) *
              (((a + 3) - 1) * (b + 3)) *
              (((a + 3) - 2) * (b + 3)) := by ring
        _ ≤ ((a + 3) * (b + 3)) *
              ((a + 3) * ((b + 3) - 1)) *
              ((a + 3) * ((b + 3) - 2)) :=
          hproducts
        _ = (b + 3) * ((b + 3) - 1) * ((b + 3) - 2) *
              (a + 3) ^ 3 := by ring
    have hscaled :
        6 * (Nat.choose (a + 3) 3 * (b + 3) ^ 3) ≤
          6 * (Nat.choose (b + 3) 3 * (a + 3) ^ 3) := by
      calc
        6 * (Nat.choose (a + 3) 3 * (b + 3) ^ 3) =
            (6 * Nat.choose (a + 3) 3) * (b + 3) ^ 3 := by ring
        _ = (a + 3) * ((a + 3) - 1) * ((a + 3) - 2) *
              (b + 3) ^ 3 := by
          rw [six_mul_choose_three]
        _ ≤ (b + 3) * ((b + 3) - 1) * ((b + 3) - 2) *
              (a + 3) ^ 3 := hfactor
        _ = (6 * Nat.choose (b + 3) 3) * (a + 3) ^ 3 := by
          rw [six_mul_choose_three]
        _ = 6 * (Nat.choose (b + 3) 3 * (a + 3) ^ 3) := by ring
    exact Nat.le_of_mul_le_mul_left hscaled (by norm_num)
  · have hchoose : Nat.choose A 3 = 0 :=
      Nat.choose_eq_zero_of_lt (by omega)
    simp [hchoose]

/-- The exact without-replacement all-active cap is no larger than the paper's
with-replacement cubic envelope. -/
theorem infectionAllActiveCap_le_cube
    (n A : ℕ) (h3 : 3 ≤ n) (hA : A ≤ n) :
    infectionAllActiveCap n A ≤
      ((A : ℝ≥0∞) / (n : ℝ≥0∞)) ^ 3 := by
  unfold infectionAllActiveCap
  rw [show ((A : ℝ≥0∞) / (n : ℝ≥0∞)) ^ 3 =
      (A : ℝ≥0∞) ^ 3 / (n : ℝ≥0∞) ^ 3 by
    simp only [div_eq_mul_inv, mul_pow, ← ENNReal.inv_pow]]
  have hchoose0 : ((Nat.choose n 3 : ℕ) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (choose_three_pos h3).ne'
  have hchooseTop : ((Nat.choose n 3 : ℕ) : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  apply (ENNReal.div_le_iff hchoose0 hchooseTop).2
  have hn0 : ((n : ℝ≥0∞) ^ 3) ≠ 0 := by
    apply pow_ne_zero
    exact_mod_cast (show n ≠ 0 by omega)
  calc
    (Nat.choose A 3 : ℝ≥0∞) ≤
        ((A ^ 3 * Nat.choose n 3 : ℕ) : ℝ≥0∞) /
          ((n ^ 3 : ℕ) : ℝ≥0∞) := by
      apply (ENNReal.le_div_iff_mul_le
        (Or.inl (by exact_mod_cast hn0))
        (Or.inl (ENNReal.natCast_ne_top (n ^ 3)))).2
      exact_mod_cast
        (by
          simpa [mul_comm] using
            choose_three_mul_cube_le n A hA)
    _ = (A : ℝ≥0∞) ^ 3 / (n : ℝ≥0∞) ^ 3 *
        (Nat.choose n 3 : ℝ≥0∞) := by
      push_cast
      simp only [div_eq_mul_inv]
      ring

/-- The with-replacement cubic envelope for an active-population cap. -/
noncomputable def infectionAllActiveCube (n A : ℕ) : ℝ≥0∞ :=
  ((A : ℝ≥0∞) / (n : ℝ≥0∞)) ^ 3

/-- Complementary mass of the cubic envelope. -/
noncomputable def infectionAllActiveCubeCompl (n A : ℕ) : ℝ≥0∞ :=
  1 - infectionAllActiveCube n A

theorem infectionAllActiveCube_le_one
    (n A : ℕ) (h3 : 3 ≤ n) (hA : A ≤ n) :
    infectionAllActiveCube n A ≤ 1 := by
  have hn0 : (n : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (show n ≠ 0 by omega)
  have hnTop : (n : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.natCast_ne_top n
  have hratio : (A : ℝ≥0∞) / (n : ℝ≥0∞) ≤ 1 := by
    apply (ENNReal.div_le_iff hn0 hnTop).2
    simpa using (show (A : ℝ≥0∞) ≤ n by exact_mod_cast hA)
  exact pow_le_one₀ bot_le hratio

theorem infectionAllActiveCube_add_compl
    (n A : ℕ) (h3 : 3 ≤ n) (hA : A ≤ n) :
    infectionAllActiveCube n A +
        infectionAllActiveCubeCompl n A = 1 := by
  unfold infectionAllActiveCubeCompl
  rw [add_comm]
  exact tsub_add_cancel_of_le
    (infectionAllActiveCube_le_one n A h3 hA)

/-- Replacing the exact without-replacement cap by the cubic envelope only
increases every upper-tail MGF factor. -/
theorem infectionAllActive_factor_le_cube
    (n A : ℕ) (h3 : 3 ≤ n) (hA : A ≤ n)
    (w : ℝ≥0∞) (hw1 : 1 ≤ w) (hwt : w ≠ ⊤) :
    infectionAllActiveCapCompl n A +
        infectionAllActiveCap n A * w ≤
      infectionAllActiveCubeCompl n A +
        infectionAllActiveCube n A * w := by
  apply upper_step_factor_monotone_ennreal
    (infectionAllActiveCube_add_compl n A h3 hA)
    (infectionAllActiveCap_add_compl n A h3 hA)
    hw1
  · simpa [infectionAllActiveCube] using
      infectionAllActiveCap_le_cube n A h3 hA
  · exact hwt

/-- Finite-horizon all-active counter tail with the paper's cubic
with-replacement envelope. -/
theorem infectionAllActiveCount_tail_cube_zero
    (n : ℕ) (h3 : 3 ≤ n) (A : ℕ) (hA : A ≤ n)
    (w : ℝ≥0∞) (hw1 : 1 ≤ w) (hwt : w ≠ ⊤)
    (T M : ℕ) (s0 : InfectionState n) :
    ∑' q, (if M ≤ q.2 then
        iter (infectionAllActiveCount n h3 A) T (s0, 0) q else 0) ≤
      (infectionAllActiveCubeCompl n A +
          infectionAllActiveCube n A * w) ^ T / w ^ M := by
  refine (infectionAllActiveCount_tail_zero
    n h3 A hA w hw1 hwt T M s0).trans ?_
  apply ENNReal.div_le_div_right
  exact pow_le_pow_left₀ bot_le
    (infectionAllActive_factor_le_cube n A h3 hA w hw1 hwt) T

/-- The cubic-envelope counter tail at the fixed MGF parameter `4/3`. -/
theorem infectionAllActiveCount_tail_cube_four_thirds
    (n : ℕ) (h3 : 3 ≤ n) (A : ℕ) (hA : A ≤ n)
    (T M : ℕ) (s0 : InfectionState n) :
    ∑' q, (if M ≤ q.2 then
        iter (infectionAllActiveCount n h3 A) T (s0, 0) q else 0) ≤
      (infectionAllActiveCubeCompl n A +
          infectionAllActiveCube n A * (4 / 3 : ℝ≥0∞)) ^ T /
        (4 / 3 : ℝ≥0∞) ^ M := by
  have hw1 : (1 : ℝ≥0∞) ≤ 4 / 3 := by
    rw [ENNReal.le_div_iff_mul_le
      (Or.inl (by norm_num)) (Or.inl (by norm_num))]
    norm_num
  have hwt : (4 / 3 : ℝ≥0∞) ≠ ⊤ := by
    finiteness
  exact infectionAllActiveCount_tail_cube_zero
    n h3 A hA (4 / 3) hw1 hwt T M s0

end Tri

#print axioms Tri.choose_three_mul_cube_le
#print axioms Tri.infectionAllActiveCap_le_cube
#print axioms Tri.infectionAllActiveCount_tail_cube_zero
#print axioms Tri.infectionAllActiveCount_tail_cube_four_thirds
