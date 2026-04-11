/-
  Ripple.Number.Pi — π is real-time CRN-computable

  Theorem 3.3.3 from Huang's PhD thesis (Iowa State, 2020):
  The PIVP
    w' = -w,  x' = -2wxy,  y' = wx² - wy²,  z' = wx
  with w(0) = x(0) = 1, y(0) = z(0) = 0 has solution (via u = 1 - e^{-t}):
    x(u) = 1/(u²+1),  y(u) = u/(u²+1),  z(u) = arctan(u).

  Since u(t) = 1 - e^{-t} → 1, we get z → arctan(1) = π/4 exponentially.
  By ℝ_RTCRN being a field, π = 4 · (π/4) ∈ ℝ_RTCRN.
-/

import Ripple.Core.BoundedTime
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Real.Pi.Bounds

namespace Ripple.Number

open Real

/-! ## The PIVP for π -/

/-- The PIVP computing π/4: dimension 4, output = component 3. -/
noncomputable def piPIVP : Ripple.PIVP 4 where
  field := fun v => ![
    - v 0,                              -- w' = -w
    - 2 * v 0 * v 1 * v 2,             -- x' = -2wxy
    v 0 * v 1 ^ 2 - v 0 * v 2 ^ 2,     -- y' = wx² - wy²
    v 0 * v 1                           -- z' = wx
  ]
  init := ![1, 1, 0, 0]
  output := 3

/-! ## Closed-form solution -/

noncomputable def piSolution : ℝ → Fin 4 → ℝ :=
  fun t =>
    let u := 1 - exp (-t)
    ![exp (-t), 1 / (u ^ 2 + 1), u / (u ^ 2 + 1), arctan u]

theorem pi_sol_w (t : ℝ) : piSolution t 0 = exp (-t) := by
  simp [piSolution, Matrix.cons_val_zero]

theorem pi_sol_x (t : ℝ) : piSolution t 1 = 1 / ((1 - exp (-t)) ^ 2 + 1) := by
  unfold piSolution; simp [Matrix.cons_val_one]

theorem pi_sol_y (t : ℝ) : piSolution t 2 = (1 - exp (-t)) / ((1 - exp (-t)) ^ 2 + 1) := by
  unfold piSolution; simp

theorem pi_sol_z (t : ℝ) : piSolution t 3 = arctan (1 - exp (-t)) := by
  simp [piSolution]

theorem pi_sol_init : piSolution 0 = piPIVP.init := by
  ext i
  fin_cases i <;> simp [piSolution, piPIVP, Matrix.cons_val_zero, Matrix.cons_val_one,
    exp_zero, arctan_zero]

/-! ## Helper lemmas -/

theorem pi_exp_neg_le_one {t : ℝ} (ht : 0 ≤ t) : exp (-t) ≤ 1 := by
  rw [← exp_zero]; exact exp_le_exp.mpr (neg_nonpos.mpr ht)

/-- arctan x ≤ x for x ≥ 0. Proof: x ≤ tan x on [0, π/2), and tan(arctan x) = x. -/
theorem arctan_le_of_nonneg {x : ℝ} (hx : 0 ≤ x) : arctan x ≤ x := by
  calc arctan x ≤ tan (arctan x) :=
        le_tan (arctan_nonneg.mpr hx) (arctan_lt_pi_div_two x)
    _ = x := tan_arctan x

/-! ## Convergence -/

/-- Key convergence estimate: |z(t) - π/4| ≤ e^{-t} for t ≥ 0.

  Proof using the arctan addition formula:
    arctan(1) + arctan(-(1-e^{-t})) = arctan(e^{-t}/(2-e^{-t}))
  gives arctan(1) - arctan(1-e^{-t}) = arctan(e^{-t}/(2-e^{-t})) ≤ e^{-t}. -/
theorem pi_convergence (t : ℝ) (ht : 0 ≤ t) :
    |piSolution t 3 - π / 4| ≤ exp (-t) := by
  rw [pi_sol_z]
  -- Setup: u = 1-e^{-t} ∈ [0,1), arctan(u) ≤ arctan(1) = π/4
  set u := 1 - exp (-t) with hu_def
  have hu_nn : 0 ≤ u := by simp [hu_def]; linarith [pi_exp_neg_le_one ht]
  have hu_lt : u < 1 := by simp [hu_def]; linarith [exp_pos (-t)]
  have hle : arctan u ≤ π / 4 := by rw [← arctan_one]; exact arctan_mono hu_lt.le
  rw [abs_of_nonpos (by linarith)]
  -- Goal: -(arctan u - π/4) ≤ exp(-t), i.e., π/4 - arctan u ≤ exp(-t)
  suffices h : π / 4 - arctan u ≤ exp (-t) by linarith
  have h2pos : 0 < 2 - exp (-t) := by linarith [pi_exp_neg_le_one ht]
  -- Use arctan addition: arctan(1) + arctan(-u) = arctan((1-u)/(1+u))
  have h_sub : π / 4 - arctan u = arctan (exp (-t) / (2 - exp (-t))) := by
    have hprod : 1 * (-u) < 1 := by nlinarith
    have h_add := arctan_add hprod
    rw [arctan_neg, arctan_one] at h_add
    -- h_add : π/4 + -arctan u = arctan ((1 + -u) / (1 - 1 * -u))
    have heq : (1 + -u) / (1 - 1 * -u) = exp (-t) / (2 - exp (-t)) := by
      rw [div_eq_div_iff (by nlinarith : (1 : ℝ) - 1 * -u ≠ 0) (ne_of_gt h2pos)]
      rw [hu_def]; ring
    rw [heq] at h_add
    linarith
  rw [h_sub]
  -- Goal: arctan(e^{-t}/(2-e^{-t})) ≤ exp(-t)
  have hfrac_nn : 0 ≤ exp (-t) / (2 - exp (-t)) :=
    div_nonneg (le_of_lt (exp_pos _)) (le_of_lt h2pos)
  calc arctan (exp (-t) / (2 - exp (-t)))
      ≤ exp (-t) / (2 - exp (-t)) := arctan_le_of_nonneg hfrac_nn
    _ ≤ exp (-t) / 1 := by
        apply div_le_div_of_nonneg_left (le_of_lt (exp_pos _)) one_pos
        linarith [pi_exp_neg_le_one ht]
    _ = exp (-t) := div_one _

/-! ## Boundedness -/

theorem pi_bounded : piPIVP.IsBounded piSolution := by
  refine ⟨2, by norm_num, ?_⟩
  intro t ht
  rw [pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  intro i
  fin_cases i
  · -- w = e^{-t} ∈ (0, 1]
    change ‖piSolution t 0‖ ≤ 2
    rw [pi_sol_w, norm_of_nonneg (le_of_lt (exp_pos _))]
    linarith [pi_exp_neg_le_one ht]
  · -- x = 1/(u²+1) ∈ (0, 1]
    change ‖piSolution t 1‖ ≤ 2
    rw [pi_sol_x]
    have hpos : 0 < (1 - exp (-t)) ^ 2 + 1 := by positivity
    rw [norm_of_nonneg (div_nonneg one_pos.le (le_of_lt hpos))]
    exact le_trans (div_le_one_of_le₀ (by nlinarith) (by positivity)) (by norm_num)
  · -- y = u/(u²+1) ∈ [0, 1]
    change ‖piSolution t 2‖ ≤ 2
    rw [pi_sol_y]
    have hu : 0 ≤ 1 - exp (-t) := by linarith [pi_exp_neg_le_one ht]
    rw [norm_of_nonneg (div_nonneg hu (by positivity))]
    exact le_trans (div_le_one_of_le₀ (by nlinarith) (by positivity)) (by norm_num)
  · -- z = arctan(u) ∈ [0, π/4] ⊂ [0, 1] ⊂ [0, 2]
    change ‖piSolution t 3‖ ≤ 2
    rw [pi_sol_z]
    have hu : 0 ≤ 1 - exp (-t) := by linarith [pi_exp_neg_le_one ht]
    rw [norm_of_nonneg (arctan_nonneg.mpr hu)]
    calc arctan (1 - exp (-t))
        ≤ arctan 1 := arctan_mono (by linarith [exp_pos (-t)])
      _ = π / 4 := arctan_one
      _ ≤ 1 := by linarith [pi_lt_four]
      _ ≤ 2 := by norm_num

/-! ## Main theorems -/

/-- π/4 is real-time CRN-computable. -/
theorem pi_quarter_is_realtime : Ripple.IsRealTimeComputable (π / 4) := by
  refine ⟨4, ?_, ?_⟩
  · exact {
      pivp := piPIVP
      sol := {
        trajectory := piSolution
        init_cond := pi_sol_init
        is_solution := trivial
      }
      modulus := fun r => ↑r + 1
      bounded := pi_bounded
      convergence := by
        intro r t htr
        have hr_nn : (0 : ℝ) ≤ ↑r := Nat.cast_nonneg r
        have ht_pos : 0 ≤ t := by linarith
        calc |piSolution t 3 - π / 4|
            ≤ exp (-t) := pi_convergence t ht_pos
          _ < exp (-(↑r + 1)) := by
              apply exp_lt_exp.mpr; linarith
          _ = exp (-(↑r : ℝ) - 1) := by ring_nf
          _ < exp (-(↑r : ℝ)) := by
              apply exp_lt_exp.mpr; linarith
    }
  · exact ⟨(2 : ℝ), by norm_num, fun r => by push_cast; linarith⟩

/-- π is real-time CRN-computable (by field closure: π = 4 · (π/4)). -/
theorem pi_is_realtime : Ripple.IsRealTimeComputable π := by
  have := Ripple.realtime_field_mul (Ripple.realtime_const 4) pi_quarter_is_realtime
  convert this using 1
  ring

end Ripple.Number
