import Mathlib

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open Real Filter
open scoped Topology

theorem geometric_bound_of_contracting_recurrence
    {f : ℕ → ℝ} {q₀ C_r lam : ℝ}
    (hf0 : ∀ j, 0 ≤ f j)
    (hstep : ∀ j, f (j + 1) ≤ q₀ * f j + C_r * Real.exp (-lam * (j : ℝ)))
    (hq₀_nn : 0 ≤ q₀)
    (hq₀_lt : q₀ < Real.exp (-lam))
    (hCr : 0 ≤ C_r)
    (_hlam : 0 < lam) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j : ℕ, f j ≤ C * Real.exp (-lam * (j : ℝ)) := by
  set κ := q₀ * Real.exp lam with hκ_def
  have hexp_pos : 0 < Real.exp lam := Real.exp_pos lam
  have hexp_neg_pos : 0 < Real.exp (-lam) := Real.exp_pos (-lam)
  have hκ_lt : κ < 1 := by
    rw [hκ_def]
    calc q₀ * Real.exp lam < Real.exp (-lam) * Real.exp lam := by
          exact mul_lt_mul_of_pos_right hq₀_lt hexp_pos
      _ = 1 := by rw [← Real.exp_add]; simp
  have hκ_nn : 0 ≤ κ := mul_nonneg hq₀_nn hexp_pos.le
  set g : ℕ → ℝ := fun j => f j * Real.exp (lam * (j : ℝ)) with hg_def
  have hg0 : ∀ j, 0 ≤ g j := fun j =>
    mul_nonneg (hf0 j) (Real.exp_pos _).le
  have hg_step : ∀ j, g (j + 1) ≤ κ * g j + C_r * Real.exp lam := by
    intro j
    simp only [hg_def, hκ_def]
    have hexp_split : Real.exp (lam * ((j : ℝ) + 1)) =
        Real.exp (lam * (j : ℝ)) * Real.exp lam := by
      rw [← Real.exp_add]; ring_nf
    rw [Nat.cast_succ] at *
    calc f (j + 1) * Real.exp (lam * ((j : ℝ) + 1))
        = f (j + 1) * (Real.exp (lam * (j : ℝ)) * Real.exp lam) := by
          rw [hexp_split]
      _ ≤ (q₀ * f j + C_r * Real.exp (-lam * (j : ℝ))) *
            (Real.exp (lam * (j : ℝ)) * Real.exp lam) := by
          apply mul_le_mul_of_nonneg_right (hstep j)
          exact mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
      _ = q₀ * Real.exp lam * (f j * Real.exp (lam * (j : ℝ))) +
          C_r * (Real.exp (-lam * (j : ℝ)) * Real.exp (lam * (j : ℝ))) *
            Real.exp lam := by ring
      _ = q₀ * Real.exp lam * (f j * Real.exp (lam * (j : ℝ))) +
          C_r * 1 * Real.exp lam := by
          congr 1
          congr 1
          rw [← Real.exp_add]
          simp
      _ = κ * g j + C_r * Real.exp lam := by ring
  have hgap : 0 < 1 - κ := by linarith
  set B := C_r * Real.exp lam / (1 - κ) with hB_def
  have hB_nn : 0 ≤ B := div_nonneg (mul_nonneg hCr hexp_pos.le) hgap.le
  have hg_bound : ∀ j, g j ≤ g 0 + B := by
    intro j
    induction j with
    | zero => linarith [hB_nn]
    | succ k ih =>
      calc g (k + 1) ≤ κ * g k + C_r * Real.exp lam := hg_step k
        _ ≤ κ * (g 0 + B) + C_r * Real.exp lam := by
            linarith [mul_le_mul_of_nonneg_left ih hκ_nn]
        _ = κ * g 0 + (κ * B + C_r * Real.exp lam) := by ring
        _ = κ * g 0 + (κ * (C_r * Real.exp lam / (1 - κ)) + C_r * Real.exp lam) := by
            rw [hB_def]
        _ = κ * g 0 + C_r * Real.exp lam * (κ / (1 - κ) + 1) := by ring
        _ = κ * g 0 + C_r * Real.exp lam * (1 / (1 - κ)) := by
            congr 1
            field_simp
            ring
        _ = κ * g 0 + B := by rw [hB_def]; ring
        _ ≤ 1 * g 0 + B := by
            linarith [mul_le_mul_of_nonneg_right hκ_lt.le (hg0 0)]
        _ = g 0 + B := by ring
  set C := g 0 + B with hC_def
  have hC_nn : 0 ≤ C := by
    rw [hC_def]
    exact add_nonneg (hg0 0) hB_nn
  refine ⟨C, hC_nn, ?_⟩
  intro j
  have hgj := hg_bound j
  have hexp_neg_lam_pos : 0 < Real.exp (-lam * (j : ℝ)) := Real.exp_pos _
  have hfg : f j = g j * Real.exp (-lam * (j : ℝ)) := by
    simp [hg_def]
    rw [mul_assoc, ← Real.exp_add]
    simp [add_neg_cancel, mul_one]
  rw [hfg]
  exact mul_le_mul_of_nonneg_right hgj hexp_neg_lam_pos.le

end Ripple.BoundedUniversality.BGP
