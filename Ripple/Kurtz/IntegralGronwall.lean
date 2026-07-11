/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang, Zinan Huang
-/
import Ripple.Kurtz.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Integral Form of Gronwall's Inequality

  If u(t) ≤ α + ∫₀ᵗ β · u(s) ds for all t ∈ [0, T],
  then u(t) ≤ α · exp(β · t).

Proof by ChatGPT + Claude collaboration:
Define v(t) = α + ∫₀ᵗ β·u(s) ds. Then u ≤ v, v(0) = α,
v'(t) = β·u(t) ≤ β·v(t). Apply Mathlib's derivative-form Gronwall to v.
-/

open Set MeasureTheory
open scoped Interval

/-- **Integral Gronwall inequality (scalar, constant coefficients).**

Per ChatGPT: the FTC plumbing hypotheses are separated out so that
the core Gronwall argument is clean. These are discharged from
ContinuousOn u (Icc 0 T) at the call site. -/
theorem integral_gronwall_core
    {T α β : ℝ} {u : ℝ → ℝ}
    (_hT : 0 ≤ T) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hu_nonneg : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ u t)
    (hineq : ∀ t ∈ Icc (0 : ℝ) T,
        u t ≤ α + ∫ s in (0 : ℝ)..t, β * u s)
    (hg_int : ∀ x ∈ Ico (0 : ℝ) T,
        IntervalIntegrable (fun s => β * u s) volume (0 : ℝ) x)
    (hg_cont_right : ∀ x ∈ Ico (0 : ℝ) T,
        ContinuousWithinAt (fun s => β * u s) (Ioi x) x)
    (hg_sm : ∀ x ∈ Ico (0 : ℝ) T,
        StronglyMeasurableAtFilter (fun s => β * u s) (nhdsWithin x (Ioi x)))
    (hv_cont : ContinuousOn
        (fun t => α + ∫ s in (0 : ℝ)..t, β * u s) (Icc (0 : ℝ) T))
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
    u t ≤ α * Real.exp (β * t) := by
  let g : ℝ → ℝ := fun s => β * u s
  let v : ℝ → ℝ := fun t => α + ∫ s in (0 : ℝ)..t, g s
  have hv_cont' : ContinuousOn v (Icc (0 : ℝ) T) := hv_cont
  have hv_deriv : ∀ x ∈ Ico (0 : ℝ) T,
      HasDerivWithinAt v (β * u x) (Ici x) x := by
    intro x hx
    have hFTC : HasDerivWithinAt (fun y => ∫ s in (0 : ℝ)..y, g s) (g x) (Ici x) x :=
      intervalIntegral.integral_hasDerivWithinAt_right
        (hg_int x hx)
        (hg_sm x hx)
        (hg_cont_right x hx)
    exact hFTC.const_add α
  have hv_nonneg : ∀ x ∈ Icc (0 : ℝ) T, 0 ≤ v x := by
    intro x hx
    have hint_nonneg : 0 ≤ ∫ s in (0 : ℝ)..x, g s :=
      intervalIntegral.integral_nonneg hx.1 fun y hy =>
        mul_nonneg hβ (hu_nonneg y ⟨hy.1, le_trans hy.2 hx.2⟩)
    exact add_nonneg hα hint_nonneg
  have hv0 : ‖v 0‖ ≤ α := by simp [v, Real.norm_eq_abs, abs_of_nonneg hα]
  have hbound : ∀ x ∈ Ico (0 : ℝ) T, ‖β * u x‖ ≤ β * ‖v x‖ + 0 := by
    intro x hx
    have hxIcc : x ∈ Icc (0 : ℝ) T := ⟨hx.1, le_of_lt hx.2⟩
    have hv0x : 0 ≤ v x := hv_nonneg x hxIcc
    have huv : u x ≤ v x := hineq x hxIcc
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hβ (hu_nonneg x hxIcc)),
        Real.norm_eq_abs, abs_of_nonneg hv0x, add_zero]
    exact mul_le_mul_of_nonneg_left huv hβ
  have hgr : ‖v t‖ ≤ gronwallBound α β 0 (t - 0) :=
    norm_le_gronwallBound_of_norm_deriv_right_le hv_cont' hv_deriv hv0 hbound t ht
  calc u t ≤ v t := hineq t ht
    _ = ‖v t‖ := by rw [Real.norm_eq_abs, abs_of_nonneg (hv_nonneg t ht)]
    _ ≤ gronwallBound α β 0 (t - 0) := hgr
    _ = α * Real.exp (β * t) := by simp [gronwallBound_ε0]
