/-
Ripple.BoundedUniversality.GPAC.IncrementerDemo
---------------------------
End-to-end demonstration (ChatGPT-pro RB4 design): a genuine bounded
register-machine step — a 3-state (Run/Halt/Ovf), 2-bit increment-with-
overflow machine — realized by an explicit RATIONAL (integer-coefficient)
polynomial transition `Tinc : ℝ⁵ → ℝ⁵`, instantiating the bounded
rational robust step.

Encoding `x = (r, h, o, a, b)`: one-hot state `(r,h,o)` (Run/Halt/Ovf),
2-bit register `(a,b)` with `a` low, `b` high.  Transition:
  Run,00 → Halt,01   Run,01 → Halt,10   Run,10 → Halt,11
  Run,11 → Ovf,11    Halt → Halt        Ovf → Ovf.
Unlike a 2-state version (partial on overflow / silent mod-4 wrap), the
Ovf state makes the bounded incrementer total and honest.
-/

import Ripple.BoundedUniversality.GPAC.BoundedRobustStep

namespace Ripple.BoundedUniversality.GPAC.IncrementerDemo

open Polynomial Ripple.BoundedUniversality.GPAC.BoundedRobustStep

/-- The explicit rational (integer-coefficient) transition polynomial. -/
noncomputable def Tinc (x : Fin 5 → ℝ) : Fin 5 → ℝ :=
  ![ 0,
     x 1 + x 0 * (1 - x 3 * x 4),
     x 2 + x 0 * (x 3 * x 4),
     x 3 + x 0 * (1 - 2 * x 3 + x 3 * x 4),
     x 4 + x 0 * (x 3 * (1 - x 4)) ]

/-- Exactness, `Run,00 → Halt,01`: `(1,0,0,0,0) ↦ (0,1,0,1,0)`. -/
theorem Tinc_run00 : Tinc ![1, 0, 0, 0, 0] = ![0, 1, 0, 1, 0] := by
  funext i; fin_cases i <;> simp [Tinc] <;> norm_num

/-- Exactness, `Run,01 → Halt,10`: `(1,0,0,1,0) ↦ (0,1,0,0,1)`. -/
theorem Tinc_run01 : Tinc ![1, 0, 0, 1, 0] = ![0, 1, 0, 0, 1] := by
  funext i; fin_cases i <;> simp [Tinc] <;> norm_num

/-- Exactness, `Run,10 → Halt,11`: `(1,0,0,0,1) ↦ (0,1,0,1,1)`. -/
theorem Tinc_run10 : Tinc ![1, 0, 0, 0, 1] = ![0, 1, 0, 1, 1] := by
  funext i; fin_cases i <;> simp [Tinc] <;> norm_num

/-- Exactness, `Run,11 → Ovf,11`: `(1,0,0,1,1) ↦ (0,0,1,1,1)`. -/
theorem Tinc_run11 : Tinc ![1, 0, 0, 1, 1] = ![0, 0, 1, 1, 1] := by
  funext i; fin_cases i <;> simp [Tinc] <;> norm_num

/-- Halt is absorbing: `(0,1,0,a,b) ↦ (0,1,0,a,b)`. -/
theorem Tinc_halt (a b : ℝ) : Tinc ![0, 1, 0, a, b] = ![0, 1, 0, a, b] := by
  funext i; fin_cases i <;> simp [Tinc]

/-- Ovf is absorbing: `(0,0,1,a,b) ↦ (0,0,1,a,b)`. -/
theorem Tinc_ovf (a b : ℝ) : Tinc ![0, 0, 1, a, b] = ![0, 0, 1, a, b] := by
  funext i; fin_cases i <;> simp [Tinc]

open Ripple.BoundedUniversality.GPAC.RobustnessAmplification Ripple.BoundedUniversality.GPAC.RationalRounding in
theorem robust_step_incrementer :
    ∃ (R : Polynomial ℚ) (ρ0 : ℝ), 0 < ρ0 ∧
      ∀ x : Fin 5 → ℝ, dist x ![1, 0, 0, 0, 0] ≤ ρ0 →
        dist ((Cmap R 5 ∘ Tinc ∘ (Cmap R 5)^[3]) x) ![0, 1, 0, 1, 0]
          ≤ (1/2) * dist x ![1, 0, 0, 0, 0] := by
  obtain ⟨R, ρ, hρ, hcw⟩ := coordinatewise_rounder_contracts 1 5
  let c : Fin 5 → ℝ := ![1, 0, 0, 0, 0]
  let c' : Fin 5 → ℝ := ![0, 1, 0, 1, 0]
  let ρ0 : ℝ := min ρ (1/2)
  have hρ0pos : 0 < ρ0 := lt_min hρ (by norm_num)
  have hcgrid : OnGrid 1 5 c := by
    intro j
    fin_cases j
    · exact ⟨1, by decide, by simp [c]⟩
    · exact ⟨0, by decide, by simp [c]⟩
    · exact ⟨0, by decide, by simp [c]⟩
    · exact ⟨0, by decide, by simp [c]⟩
    · exact ⟨0, by decide, by simp [c]⟩
  have hc'grid : OnGrid 1 5 c' := by
    intro j
    fin_cases j
    · exact ⟨0, by decide, by simp [c']⟩
    · exact ⟨1, by decide, by simp [c']⟩
    · exact ⟨0, by decide, by simp [c']⟩
    · exact ⟨1, by decide, by simp [c']⟩
    · exact ⟨0, by decide, by simp [c']⟩
  refine ⟨R, ρ0, hρ0pos, ?_⟩
  intro x hx
  have hRc : ∀ y, dist y c ≤ ρ0 →
      dist (Cmap R 5 y) c ≤ (1/2) * dist y c := by
    intro y hy
    exact hcw c hcgrid y (le_trans hy (min_le_left ρ (1/2)))
  have hRc' : ∀ y, dist y c' ≤ ρ0 →
      dist (Cmap R 5 y) c' ≤ (1/2) * dist y c' := by
    intro y hy
    exact hcw c' hc'grid y (le_trans hy (min_le_left ρ (1/2)))
  have hLip : ∀ y, dist y c ≤ ρ0 → dist (Tinc y) c' ≤ 8 * dist y c := by
    intro y hy
    let d : ℝ := dist y c
    have hd_nonneg : 0 ≤ d := dist_nonneg
    have hd_half : d ≤ 1/2 := le_trans hy (min_le_right ρ (1/2))
    have hcoord (j : Fin 5) : |y j - c j| ≤ d := by
      simpa [d, Real.dist_eq] using dist_le_pi_dist y c j
    have hy0m1 : |y 0 - 1| ≤ d := by
      simpa [c] using hcoord 0
    have hy1 : |y 1| ≤ d := by
      simpa [c] using hcoord 1
    have hy2 : |y 2| ≤ d := by
      simpa [c] using hcoord 2
    have hy3 : |y 3| ≤ d := by
      simpa [c] using hcoord 3
    have hy4 : |y 4| ≤ d := by
      simpa [c] using hcoord 4
    have hy0 : |y 0| ≤ (3/2 : ℝ) := by
      have hlo := (abs_le.mp hy0m1).1
      have hhi := (abs_le.mp hy0m1).2
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    have hy03 : |y 0 * y 3| ≤ (3/2 : ℝ) * d := by
      rw [abs_mul]
      exact mul_le_mul hy0 hy3 (abs_nonneg (y 3)) (by norm_num)
    have hy034_tmp : |y 0 * y 3 * y 4| ≤ ((3/2 : ℝ) * d) * d := by
      rw [abs_mul]
      exact mul_le_mul hy03 hy4 (abs_nonneg (y 4))
        (mul_nonneg (by norm_num) hd_nonneg)
    have hdd : d * d ≤ (1/2 : ℝ) * d :=
      mul_le_mul_of_nonneg_right hd_half hd_nonneg
    have hy034 : |y 0 * y 3 * y 4| ≤ (3/4 : ℝ) * d := by
      calc
        |y 0 * y 3 * y 4| ≤ ((3/2 : ℝ) * d) * d := hy034_tmp
        _ = (3/2 : ℝ) * (d * d) := by ring
        _ ≤ (3/2 : ℝ) * ((1/2 : ℝ) * d) :=
          mul_le_mul_of_nonneg_left hdd (by norm_num)
        _ = (3/4 : ℝ) * d := by ring
    have h2y03 : |2 * (y 0 * y 3)| ≤ 3 * d := by
      calc
        |2 * (y 0 * y 3)| = (2 : ℝ) * |y 0 * y 3| := by
          rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        _ ≤ 2 * ((3/2 : ℝ) * d) := by
          exact mul_le_mul_of_nonneg_left hy03 (by norm_num)
        _ = 3 * d := by ring
    have abs_add3 (a b e : ℝ) : |a + b + e| ≤ |a| + |b| + |e| := by
      have h1 := abs_add_le (a + b) e
      have h2 := abs_add_le a b
      linarith
    have abs_add4 (a b e f : ℝ) : |a + b + e + f| ≤ |a| + |b| + |e| + |f| := by
      have h1 := abs_add_le (a + b + e) f
      have h2 := abs_add3 a b e
      linarith
    have h8d : 0 ≤ 8 * d := mul_nonneg (by norm_num) hd_nonneg
    change dist (Tinc y) c' ≤ 8 * d
    rw [dist_pi_le_iff h8d]
    intro i
    fin_cases i
    · simpa [Tinc, c', Real.dist_eq] using h8d
    · rw [Real.dist_eq]
      simp [Tinc, c']
      change |y 1 + y 0 * (1 - y 3 * y 4) - 1| ≤ 8 * d
      have heq : y 1 + y 0 * (1 - y 3 * y 4) - 1 =
          y 1 + (y 0 - 1) + (-(y 0 * y 3 * y 4)) := by ring
      rw [heq]
      calc
        |y 1 + (y 0 - 1) + (-(y 0 * y 3 * y 4))|
            ≤ |y 1| + |y 0 - 1| + |-(y 0 * y 3 * y 4)| :=
          abs_add3 (y 1) (y 0 - 1) (-(y 0 * y 3 * y 4))
        _ = |y 1| + |y 0 - 1| + |y 0 * y 3 * y 4| := by rw [abs_neg]
        _ ≤ d + d + (3/4 : ℝ) * d := by linarith
        _ ≤ 8 * d := by linarith
    · rw [Real.dist_eq]
      simp [Tinc, c']
      change |y 2 + y 0 * (y 3 * y 4)| ≤ 8 * d
      have heq : y 2 + y 0 * (y 3 * y 4) = y 2 + y 0 * y 3 * y 4 := by ring
      rw [heq]
      calc
        |y 2 + y 0 * y 3 * y 4| ≤ |y 2| + |y 0 * y 3 * y 4| :=
          abs_add_le (y 2) (y 0 * y 3 * y 4)
        _ ≤ d + (3/4 : ℝ) * d := by linarith
        _ ≤ 8 * d := by linarith
    · rw [Real.dist_eq]
      simp [Tinc, c']
      change |y 3 + y 0 * (1 - 2 * y 3 + y 3 * y 4) - 1| ≤ 8 * d
      have heq : y 3 + y 0 * (1 - 2 * y 3 + y 3 * y 4) - 1 =
          y 3 + (y 0 - 1) + (-(2 * (y 0 * y 3))) + y 0 * y 3 * y 4 := by ring
      rw [heq]
      calc
        |y 3 + (y 0 - 1) + (-(2 * (y 0 * y 3))) + y 0 * y 3 * y 4|
            ≤ |y 3| + |y 0 - 1| + |-(2 * (y 0 * y 3))| + |y 0 * y 3 * y 4| :=
          abs_add4 (y 3) (y 0 - 1) (-(2 * (y 0 * y 3))) (y 0 * y 3 * y 4)
        _ = |y 3| + |y 0 - 1| + |2 * (y 0 * y 3)| + |y 0 * y 3 * y 4| := by rw [abs_neg]
        _ ≤ d + d + 3 * d + (3/4 : ℝ) * d := by linarith
        _ ≤ 8 * d := by linarith
    · rw [Real.dist_eq]
      simp [Tinc, c']
      change |y 4 + y 0 * (y 3 * (1 - y 4))| ≤ 8 * d
      have heq : y 4 + y 0 * (y 3 * (1 - y 4)) =
          y 4 + y 0 * y 3 + (-(y 0 * y 3 * y 4)) := by ring
      rw [heq]
      calc
        |y 4 + y 0 * y 3 + (-(y 0 * y 3 * y 4))|
            ≤ |y 4| + |y 0 * y 3| + |-(y 0 * y 3 * y 4)| :=
          abs_add3 (y 4) (y 0 * y 3) (-(y 0 * y 3 * y 4))
        _ = |y 4| + |y 0 * y 3| + |y 0 * y 3 * y 4| := by rw [abs_neg]
        _ ≤ d + (3/2 : ℝ) * d + (3/4 : ℝ) * d := by linarith
        _ ≤ 8 * d := by linarith
  simpa [c, c', ρ0] using
    step_contracts (Cmap R 5) Tinc c c' ρ0 8 3 (le_of_lt hρ0pos)
      (by norm_num) (by norm_num) hRc hRc'
      (by simpa [c, c'] using Tinc_run00) hLip x hx

end Ripple.BoundedUniversality.GPAC.IncrementerDemo
