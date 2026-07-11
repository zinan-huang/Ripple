/-
  Ripple.Number.Ln2 — ln 2 is real-time CRN-computable

  Construction: ln 2 = ∫₀¹ 1/(1+t) dt.

  Under the time change s = 1 - e^{-t}, we get:
    f(t) = ∫₀^{1-e^{-t}} 1/(1+s) ds = ln(2 - e^{-t}).

  As t → ∞, f(t) → ln 2 exponentially.

  The 3-variable PIVP:
    f' = v·r          (f → ln 2)
    v' = -v           (v = e^{-t})
    r' = v·r²         (r = 1/(2 - e^{-t}))

  ICs: f(0) = 0, v(0) = 1, r(0) = 1.

  Boundedness: v ∈ (0,1], r ∈ [1/2, 1], f ∈ [0, ln 2].
  Convergence: |f(t) - ln 2| ≤ e^{-t}.
-/

import Ripple.Core.BoundedTime
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Inv

namespace Ripple.Number

open Real

/-- The PIVP computing ln 2: dimension 3, output = component 0. -/
noncomputable def ln2PIVP : Ripple.PIVP 3 where
  field := fun y => ![
    y 1 * y 2,            -- f' = v·r
    - y 1,                -- v' = -v
    - y 1 * y 2 ^ 2       -- r' = -v·r²
  ]
  init := ![0, 1, 1]
  output := 0

/-- The closed-form solution of the ln 2 PIVP. -/
noncomputable def ln2Solution : ℝ → Fin 3 → ℝ :=
  fun t => ![log (2 - exp (-t)), exp (-t), 1 / (2 - exp (-t))]

/-- f(t) = ln(2 - e^{-t}). -/
theorem ln2_sol_f (t : ℝ) : ln2Solution t 0 = log (2 - exp (-t)) := by
  simp [ln2Solution, Matrix.cons_val_zero]

/-- v(t) = e^{-t}. -/
theorem ln2_sol_v (t : ℝ) : ln2Solution t 1 = exp (-t) := by
  simp [ln2Solution]

/-- r(t) = 1/(2 - e^{-t}). -/
theorem ln2_sol_r (t : ℝ) : ln2Solution t 2 = 1 / (2 - exp (-t)) := by
  simp [ln2Solution, Matrix.cons_val_one]

/-- The solution satisfies the initial condition. -/
theorem ln2_sol_init : ln2Solution 0 = ln2PIVP.init := by
  ext i
  fin_cases i
  · -- f(0) = log(2 - e^0) = log 1 = 0
    simp [ln2Solution, ln2PIVP, Matrix.cons_val_zero, exp_zero]
    norm_num
  · simp [ln2Solution, ln2PIVP, Matrix.cons_val_zero, exp_zero]
  · simp [ln2Solution, ln2PIVP, exp_zero]
    norm_num

/-- exp(-t) ≤ 1 for t ≥ 0. -/
theorem exp_neg_le_one {t : ℝ} (ht : 0 ≤ t) : exp (-t) ≤ 1 := by
  rw [← exp_zero]
  exact exp_le_exp.mpr (neg_nonpos.mpr ht)

/-- 2 - e^{-t} > 0 for t ≥ 0. -/
theorem two_sub_exp_pos {t : ℝ} (ht : 0 ≤ t) : 0 < 2 - exp (-t) := by
  have := exp_neg_le_one ht
  linarith

/-- 2 - e^{-t} ≥ 1 for t ≥ 0. -/
theorem two_sub_exp_ge_one {t : ℝ} (ht : 0 ≤ t) : 1 ≤ 2 - exp (-t) := by
  have := exp_neg_le_one ht; linarith

/-- f(t) ≤ ln 2 for all t ≥ 0. -/
theorem ln2_f_le {t : ℝ} (ht : 0 ≤ t) : ln2Solution t 0 ≤ log 2 := by
  rw [ln2_sol_f]
  exact log_le_log (two_sub_exp_pos ht) (by linarith [exp_pos (-t)])

/-- The PIVP is bounded. -/
theorem ln2_bounded : ln2PIVP.IsBounded ln2Solution := by
  refine ⟨2, by norm_num, ?_⟩
  intro t ht
  rw [pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  intro i
  fin_cases i
  · -- component 0: f(t) = log(2 - exp(-t)) ∈ [0, log 2] ⊂ [0, 2]
    change ‖ln2Solution t 0‖ ≤ 2
    rw [ln2_sol_f, norm_of_nonneg (log_nonneg (two_sub_exp_ge_one ht))]
    have : log (2 - exp (-t)) ≤ log 2 :=
      log_le_log (two_sub_exp_pos ht) (by linarith [exp_pos (-t)])
    linarith [log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)]
  · -- component 1: v(t) = exp(-t) ∈ (0, 1]
    change ‖ln2Solution t 1‖ ≤ 2
    rw [ln2_sol_v, norm_of_nonneg (le_of_lt (exp_pos _))]
    linarith [exp_neg_le_one ht]
  · -- component 2: r(t) = 1/(2 - exp(-t)) ∈ (0, 1]
    change ‖ln2Solution t 2‖ ≤ 2
    rw [ln2_sol_r, norm_of_nonneg (div_nonneg one_pos.le (le_of_lt (two_sub_exp_pos ht)))]
    calc 1 / (2 - exp (-t))
        ≤ 1 := (div_le_one (two_sub_exp_pos ht)).mpr (two_sub_exp_ge_one ht)
      _ ≤ 2 := by norm_num

/-- Key convergence estimate: |f(t) - ln 2| ≤ e^{-t} for t ≥ 0.

  Proof:
    f(t) = ln(2 - e^{-t}) ≤ ln 2, so the difference is non-positive.
    ln 2 - ln(2 - e^{-t}) = ln(2/(2 - e^{-t})) = ln(1 + e^{-t}/(2 - e^{-t}))
    ≤ e^{-t}/(2 - e^{-t})    (by ln(1+x) ≤ x)
    ≤ e^{-t}                 (since 2 - e^{-t} ≥ 1 for t ≥ 0)
-/
theorem ln2_convergence (t : ℝ) (ht : 0 ≤ t) :
    |ln2Solution t 0 - log 2| ≤ exp (-t) := by
  rw [ln2_sol_f]
  have hle : log (2 - exp (-t)) ≤ log 2 := ln2_f_le ht
  rw [abs_of_nonpos (by linarith)]
  -- Goal: -(log(2 - exp(-t)) - log 2) ≤ exp(-t)
  -- i.e., log 2 - log(2 - exp(-t)) ≤ exp(-t)
  have h2pos : (0 : ℝ) < 2 := by norm_num
  have hsub_pos : 0 < 2 - exp (-t) := two_sub_exp_pos ht
  have : -(log (2 - exp (-t)) - log 2) = log 2 - log (2 - exp (-t)) := by ring
  rw [this]
  rw [← log_div (by linarith : (2 : ℝ) ≠ 0) (by linarith : 2 - exp (-t) ≠ 0)]
  -- Goal: log(2 / (2 - exp(-t))) ≤ exp(-t)
  -- Use: log y ≤ y - 1 for y > 0 (log_le_sub_one_of_pos)
  have hdiv_pos : 0 < 2 / (2 - exp (-t)) := by positivity
  calc log (2 / (2 - exp (-t)))
      ≤ 2 / (2 - exp (-t)) - 1 := log_le_sub_one_of_pos hdiv_pos
    _ = exp (-t) / (2 - exp (-t)) := by field_simp; ring
    _ ≤ exp (-t) / 1 := by
        apply div_le_div_of_nonneg_left (le_of_lt (exp_pos _)) one_pos
        exact two_sub_exp_ge_one ht
    _ = exp (-t) := div_one _

/-- ln 2 is real-time CRN-computable. -/
theorem ln2_is_realtime : Ripple.IsRealTimeComputable (log 2) := by
  refine ⟨3, ?_, ?_⟩
  · exact {
      pivp := ln2PIVP
      sol := {
        trajectory := ln2Solution
        init_cond := ln2_sol_init
        is_solution := fun t ht => by
          have hfield : ln2PIVP.field (ln2Solution t) =
              ![exp (-t) / (2 - exp (-t)), -exp (-t),
                -(exp (-t) / (2 - exp (-t)) ^ 2)] := by
            ext i; fin_cases i <;>
              simp [ln2PIVP, ln2Solution, Matrix.cons_val_zero,
                Matrix.cons_val_one]
            · field_simp
            · ring
          rw [hfield, hasDerivAt_pi]
          have h_neg : HasDerivAt (fun s : ℝ => -s) (-1 : ℝ) t := by
            simpa [id] using (hasDerivAt_id t).neg
          have h_exp_neg := h_neg.exp
          -- h_exp_neg : HasDerivAt (fun s => exp(-s)) (exp(-t) * -1) t
          have h_inner := (hasDerivAt_const t (2:ℝ)).sub h_exp_neg
          -- h_inner : HasDerivAt (fun s => 2 - exp(-s)) (0 - exp(-t)*(-1)) t
          have h2pos : (2 : ℝ) - exp (-t) ≠ 0 := ne_of_gt (two_sub_exp_pos ht)
          intro i; fin_cases i
          · -- d/dt log(2-exp(-t)) = exp(-t)/(2-exp(-t))
            change HasDerivAt (fun s => log (2 - exp (-s)))
              (exp (-t) / (2 - exp (-t))) t
            convert h_inner.log h2pos using 1
            simp [Pi.sub_apply]
          · -- d/dt exp(-t) = -exp(-t)
            change HasDerivAt (fun s => exp (-s)) (-exp (-t)) t
            convert h_exp_neg using 1; ring
          · -- d/dt 1/(2-exp(-t)) = -exp(-t)/(2-exp(-t))²
            change HasDerivAt (fun s => 1 / (2 - exp (-s)))
              (-(exp (-t) / (2 - exp (-t)) ^ 2)) t
            have h_one := hasDerivAt_const t (1:ℝ)
            convert h_one.div h_inner h2pos using 1
            simp [Pi.sub_apply]; ring
      }
      modulus := fun r => ↑r + 1
      bounded := ln2_bounded
      convergence := by
        intro r t htr
        have hr_nn : (0 : ℝ) ≤ ↑r := Nat.cast_nonneg r
        have ht_pos : 0 ≤ t := by linarith
        calc |ln2Solution t 0 - log 2|
            ≤ exp (-t) := ln2_convergence t ht_pos
          _ < exp (-(↑r + 1)) := by
              apply exp_lt_exp.mpr; linarith
          _ = exp (-(↑r : ℝ) - 1) := by ring_nf
          _ < exp (-(↑r : ℝ)) := by
              apply exp_lt_exp.mpr; linarith
    }
  · exact ⟨(2 : ℝ), by norm_num, fun r => by push_cast; linarith⟩

end Ripple.Number
