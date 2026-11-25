/-
  Ripple.DualRail.PowerGadgetInvariant — positivity footing for the α^β
  low-pass filter.

  The [BAC] §6 power gadget includes auxiliary species `x₁`, `u`, `v`
  satisfying
    x₁' = (x_input − 1) − x₁,   x₁(0) = 0,
  with `u = ln(1 + x₁)` and `v = x₁ / (1 + x₁)` tracking the logarithm and
  the rational auxiliary. Both require `1 + x₁(t) > 0` to be well-defined.

  This file proves that positivity as a scalar-ODE lemma: if the driving
  signal `f(t) = x_input(t)` stays nonnegative (standard for concentrations),
  then
      1 + x₁(t) ≥ exp(−t)
  on `[0, T]`.

  Proof via the integrating factor `φ(t) := exp(t) · (1 + x₁(t))`.
  Direct computation gives `φ'(t) = exp(t) · f(t) ≥ 0` on `[0, T]`, so
  `φ` is monotone nondecreasing; combined with `φ(0) = 1` this yields
  `φ(t) ≥ 1`, equivalently `1 + x₁(t) ≥ exp(−t) > 0`.

  The [BAC] paper asserts this positivity as an obvious consequence of the
  low-pass filter; formalization makes the barrier explicit.
-/

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Ripple.DualRail.Power

open Real Set

/-- Positivity footing (exponential lower bound). If `x1` solves the scalar
low-pass ODE `x1' = (f(t) − 1) − x1` on `[0, T]` with `x1(0) = 0` and the
driving signal `f(t) ≥ 0`, then `1 + x1(t) ≥ exp(−t)` on `[0, T]`.

Proof: multiply by integrating factor `exp(t)`. Let
`φ(t) := exp(t) · (1 + x1(t))`. Then `φ(0) = 1` and
`φ'(t) = exp(t) · f(t) ≥ 0`, so `φ` is monotone on `[0, T]`. Hence
`φ(t) ≥ φ(0) = 1`, which gives `1 + x1(t) ≥ exp(−t)`. -/
theorem one_plus_lowpass_ge_exp
    {f x1 : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hx0 : x1 0 = 0)
    (hx_deriv : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt x1 ((f t - 1) - x1 t) t)
    (hf_nonneg : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ f t) :
    ∀ t ∈ Icc (0 : ℝ) T, Real.exp (-t) ≤ 1 + x1 t := by
  -- Integrating factor: φ(t) = exp(t) · (1 + x1(t))
  set φ : ℝ → ℝ := fun t => Real.exp t * (1 + x1 t) with hφ_def
  -- φ(0) = 1
  have hφ0 : φ 0 = 1 := by
    simp [hφ_def, hx0]
  -- φ has derivative exp(t) · f(t) at each t ∈ [0, T]
  have hφ_deriv : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt φ (Real.exp t * f t) t := by
    intro t ht
    have hexp : HasDerivAt (fun s => Real.exp s) (Real.exp t) t :=
      Real.hasDerivAt_exp t
    have hg : HasDerivAt (fun s => 1 + x1 s) ((f t - 1) - x1 t) t :=
      (hx_deriv t ht).const_add 1
    have hprod := hexp.mul hg
    -- hprod : HasDerivAt φ (exp t * (1 + x1 t) + exp t * ((f t - 1) - x1 t)) t
    convert! hprod using 1
    ring
  -- φ is continuous on [0, T]
  have hφ_cont : ContinuousOn φ (Icc (0 : ℝ) T) := fun t ht =>
    (hφ_deriv t ht).continuousAt.continuousWithinAt
  -- Interior is Ioo 0 T
  have hinterior : interior (Icc (0 : ℝ) T) = Ioo 0 T := interior_Icc
  -- φ differentiable on the interior
  have hφ_diff : DifferentiableOn ℝ φ (interior (Icc (0 : ℝ) T)) := by
    rw [hinterior]
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) T := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    exact (hφ_deriv t ht').differentiableAt.differentiableWithinAt
  -- deriv φ ≥ 0 on the interior
  have hφ_deriv_nonneg : ∀ x ∈ interior (Icc (0 : ℝ) T), 0 ≤ deriv φ x := by
    rw [hinterior]
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) T := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    rw [(hφ_deriv t ht').deriv]
    exact mul_nonneg (Real.exp_pos t).le (hf_nonneg t ht')
  -- φ monotone on [0, T]
  have hφ_mono : MonotoneOn φ (Icc (0 : ℝ) T) :=
    monotoneOn_of_deriv_nonneg (convex_Icc 0 T) hφ_cont hφ_diff hφ_deriv_nonneg
  -- Conclude: φ(t) ≥ φ(0) = 1, hence 1 + x1(t) ≥ exp(-t)
  intro t ht
  have h0_mem : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_refl _, hT⟩
  have hφ_bound : 1 ≤ φ t := by
    have := hφ_mono h0_mem ht ht.1
    rw [hφ0] at this
    exact this
  -- Translate: 1 ≤ exp(t) · (1 + x1 t) ⇒ exp(-t) ≤ 1 + x1 t
  have hstep : Real.exp (-t) * 1 ≤ Real.exp (-t) * φ t :=
    mul_le_mul_of_nonneg_left hφ_bound (Real.exp_pos _).le
  rw [show φ t = Real.exp t * (1 + x1 t) from rfl] at hstep
  rw [mul_one, ← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero,
      one_mul] at hstep
  exact hstep

/-- Corollary: strict positivity of `1 + x1(t)` on `[0, T]`. -/
theorem one_plus_lowpass_pos
    {f x1 : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hx0 : x1 0 = 0)
    (hx_deriv : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt x1 ((f t - 1) - x1 t) t)
    (hf_nonneg : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ f t) :
    ∀ t ∈ Icc (0 : ℝ) T, 0 < 1 + x1 t := by
  intro t ht
  exact lt_of_lt_of_le (Real.exp_pos _)
    (one_plus_lowpass_ge_exp hT hx0 hx_deriv hf_nonneg t ht)

/-! ## Integrating-factor closed form

The same ODE admits an exact representation via the integrating factor
`exp(t)`. This closed form is the foundation for the low-pass tracking
bound `|x1(t) − (α − 1)| ≤ |α − 1| · exp(−t) + ε` when the driving signal
satisfies `|f(t) − α| ≤ ε`.
-/

/-- Integrating-factor identity. If `x1` solves `x1' = (f(t) − 1) − x1` on
`[0, T]` with `x1(0) = 0` and `f` continuous on `[0, T]`, then for every
`t ∈ [0, T]`:
  `exp(t) · x1(t) = ∫ s in 0..t, exp(s) · (f(s) − 1)`. -/
theorem lowpass_integrating_factor
    {f x1 : ℝ → ℝ} {T : ℝ}
    (hx0 : x1 0 = 0)
    (hx_deriv : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt x1 ((f t - 1) - x1 t) t)
    (hf_cont : ContinuousOn f (Icc (0 : ℝ) T)) :
    ∀ t ∈ Icc (0 : ℝ) T,
      Real.exp t * x1 t
        = ∫ s in (0 : ℝ)..t, Real.exp s * (f s - 1) := by
  intro t ht
  set G : ℝ → ℝ := fun s => Real.exp s * x1 s with hG_def
  have hG0 : G 0 = 0 := by simp [hG_def, hx0]
  -- G'(s) = exp(s) · (f(s) − 1)
  have hG_deriv : ∀ s ∈ Icc (0 : ℝ) T,
      HasDerivAt G (Real.exp s * (f s - 1)) s := by
    intro s hs
    have hexp : HasDerivAt (fun r => Real.exp r) (Real.exp s) s :=
      Real.hasDerivAt_exp s
    have hx := hx_deriv s hs
    have hprod := hexp.mul hx
    convert! hprod using 1
    ring
  -- Derivative on uIcc 0 t ⊆ Icc 0 T
  have ht_nn : (0 : ℝ) ≤ t := ht.1
  have ht_le : t ≤ T := ht.2
  have hderiv_uIcc : ∀ x ∈ Set.uIcc (0 : ℝ) t,
      HasDerivAt G (Real.exp x * (f x - 1)) x := by
    intro x hx
    have hxmem : x ∈ Icc (0 : ℝ) t := by rwa [Set.uIcc_of_le ht_nn] at hx
    exact hG_deriv x ⟨hxmem.1, le_trans hxmem.2 ht_le⟩
  -- Integrand continuous on [0, t] ⊆ [0, T], hence interval-integrable
  have hf_cont_t : ContinuousOn f (Icc (0 : ℝ) t) :=
    hf_cont.mono (Icc_subset_Icc (le_refl 0) ht_le)
  have hcont : ContinuousOn (fun s => Real.exp s * (f s - 1)) (Icc 0 t) := by
    exact Real.continuous_exp.continuousOn.mul (hf_cont_t.sub continuousOn_const)
  have hint : IntervalIntegrable (fun s => Real.exp s * (f s - 1))
      MeasureTheory.volume 0 t := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le ht_nn]
    exact hcont.integrableOn_Icc
  have key := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv_uIcc hint
  -- key : ∫ y in 0..t, exp y * (f y − 1) = G t − G 0
  rw [hG0, sub_zero] at key
  exact key.symm

/-! ## Low-pass tracking bound

When the driving signal tracks the target `α` up to error `ε`, i.e.
`|f(t) − α| ≤ ε`, the closed-form identity yields the pointwise bound
  `|x1(t) − (α − 1)| ≤ |α − 1| · exp(−t) + ε`
on `[0, T]`. The transient term decays exponentially; asymptotically the
tracking error is bounded by `ε`.
-/

/-- Tracking bound for the low-pass filter. Given `|f(t) − α| ≤ ε` on
`[0, T]` and the ODE `x1' = (f(t) − 1) − x1` with `x1(0) = 0`, we have
  `|x1(t) − (α − 1)| ≤ |α − 1| · exp(−t) + ε`  on `[0, T]`. -/
theorem lowpass_tracking_bound
    {f x1 : ℝ → ℝ} {T α ε : ℝ}
    (hx0 : x1 0 = 0)
    (hx_deriv : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt x1 ((f t - 1) - x1 t) t)
    (hf_cont : ContinuousOn f (Icc (0 : ℝ) T))
    (hf_err : ∀ t ∈ Icc (0 : ℝ) T, |f t - α| ≤ ε) :
    ∀ t ∈ Icc (0 : ℝ) T, |x1 t - (α - 1)| ≤ |α - 1| * Real.exp (-t) + ε := by
  intro t ht
  have ht_nn : (0 : ℝ) ≤ t := ht.1
  -- Closed form: exp(t) · x1(t) = ∫ 0..t, exp(s) · (f(s) − 1)
  have hclosed := lowpass_integrating_factor hx0 hx_deriv hf_cont t ht
  -- Split f(s) − 1 = (α − 1) + (f(s) − α)
  have hsplit : ∀ s, Real.exp s * (f s - 1)
      = Real.exp s * (α - 1) + Real.exp s * (f s - α) := by
    intro s; ring
  -- Integrand for (α − 1) part is exp(s) · (α − 1)
  have hint_const : IntervalIntegrable (fun s => Real.exp s * (α - 1))
      MeasureTheory.volume 0 t :=
    (Real.continuous_exp.continuousOn.mul continuousOn_const).intervalIntegrable_of_Icc ht_nn
  -- Integrand for error part is exp(s) · (f(s) − α)
  have hf_cont_t : ContinuousOn f (Icc (0 : ℝ) t) :=
    hf_cont.mono (Icc_subset_Icc (le_refl 0) ht.2)
  have hint_err : IntervalIntegrable (fun s => Real.exp s * (f s - α))
      MeasureTheory.volume 0 t :=
    (Real.continuous_exp.continuousOn.mul
      (hf_cont_t.sub continuousOn_const)).intervalIntegrable_of_Icc ht_nn
  -- Split the integral
  have hsplit_int :
      ∫ s in (0 : ℝ)..t, Real.exp s * (f s - 1)
        = (∫ s in (0 : ℝ)..t, Real.exp s * (α - 1))
          + ∫ s in (0 : ℝ)..t, Real.exp s * (f s - α) := by
    rw [← intervalIntegral.integral_add hint_const hint_err]
    apply intervalIntegral.integral_congr
    intro s _
    exact hsplit s
  -- Evaluate ∫ 0..t, exp(s) · (α − 1) = (α − 1) · (exp(t) − 1)
  have hint_const_eval :
      ∫ s in (0 : ℝ)..t, Real.exp s * (α - 1)
        = (α - 1) * (Real.exp t - 1) := by
    rw [show (fun s => Real.exp s * (α - 1)) = fun s => (α - 1) * Real.exp s
          from funext (fun s => by ring)]
    rw [intervalIntegral.integral_const_mul, integral_exp, Real.exp_zero]
  -- Bound the error integral: |∫ 0..t, exp(s)·(f(s)-α)| ≤ ε · (exp(t) − 1)
  have hexp_t_ge_one : (1 : ℝ) ≤ Real.exp t :=
    Real.one_le_exp ht_nn
  have herr_bound :
      |∫ s in (0 : ℝ)..t, Real.exp s * (f s - α)| ≤ ε * (Real.exp t - 1) := by
    have h_int_bound :
        ∫ s in (0 : ℝ)..t, |Real.exp s * (f s - α)|
          ≤ ∫ s in (0 : ℝ)..t, Real.exp s * ε := by
      apply intervalIntegral.integral_mono_on ht_nn
      · -- |exp s · (f s − α)| integrable on [0, t]
        exact (Real.continuous_exp.continuousOn.mul
          (hf_cont_t.sub continuousOn_const)).abs.intervalIntegrable_of_Icc ht_nn
      · exact (Real.continuous_exp.continuousOn.mul
          continuousOn_const).intervalIntegrable_of_Icc ht_nn
      · intro s hs
        rw [abs_mul, abs_of_pos (Real.exp_pos s)]
        exact mul_le_mul_of_nonneg_left (hf_err s ⟨hs.1, le_trans hs.2 ht.2⟩)
          (Real.exp_pos s).le
    have h_rhs_eval :
        ∫ s in (0 : ℝ)..t, Real.exp s * ε = ε * (Real.exp t - 1) := by
      rw [show (fun s => Real.exp s * ε) = fun s => ε * Real.exp s
            from funext (fun s => by ring)]
      rw [intervalIntegral.integral_const_mul, integral_exp, Real.exp_zero]
    calc |∫ s in (0 : ℝ)..t, Real.exp s * (f s - α)|
        ≤ ∫ s in (0 : ℝ)..t, |Real.exp s * (f s - α)| :=
          intervalIntegral.abs_integral_le_integral_abs ht_nn
      _ ≤ ∫ s in (0 : ℝ)..t, Real.exp s * ε := h_int_bound
      _ = ε * (Real.exp t - 1) := h_rhs_eval
  -- Nonnegativity of ε (derived from the error hypothesis at t = 0)
  have hε_nn : 0 ≤ ε := by
    have := hf_err 0 ⟨le_refl _, ht.1.trans ht.2⟩
    exact (abs_nonneg _).trans this
  -- Assemble: x1(t) = exp(−t) · [(α − 1)·(exp(t) − 1) + error]
  -- So x1(t) − (α − 1) = −(α − 1)·exp(−t) + exp(−t) · error
  have hexp_pos : (0 : ℝ) < Real.exp t := Real.exp_pos t
  have hexp_ne : Real.exp t ≠ 0 := ne_of_gt hexp_pos
  have hx1_eq : x1 t = Real.exp (-t) *
      ((α - 1) * (Real.exp t - 1)
        + ∫ s in (0 : ℝ)..t, Real.exp s * (f s - α)) := by
    have h1 : Real.exp t * x1 t
        = (α - 1) * (Real.exp t - 1)
          + ∫ s in (0 : ℝ)..t, Real.exp s * (f s - α) := by
      rw [hclosed, hsplit_int, hint_const_eval]
    have h2 : Real.exp (-t) * (Real.exp t * x1 t) = x1 t := by
      rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
    calc x1 t = Real.exp (-t) * (Real.exp t * x1 t) := h2.symm
      _ = Real.exp (-t) *
            ((α - 1) * (Real.exp t - 1)
              + ∫ s in (0 : ℝ)..t, Real.exp s * (f s - α)) := by rw [h1]
  -- Reduce x1(t) − (α − 1)
  have hmul_1 : Real.exp (-t) * Real.exp t = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hdiff : x1 t - (α - 1)
      = -(α - 1) * Real.exp (-t)
        + Real.exp (-t) * ∫ s in (0 : ℝ)..t, Real.exp s * (f s - α) := by
    rw [hx1_eq]
    linear_combination (α - 1) * hmul_1
  -- Triangle inequality
  have habs_exp : |Real.exp (-t)| = Real.exp (-t) :=
    abs_of_pos (Real.exp_pos _)
  calc |x1 t - (α - 1)|
      = |-(α - 1) * Real.exp (-t)
          + Real.exp (-t) * ∫ s in (0 : ℝ)..t, Real.exp s * (f s - α)| := by
          rw [hdiff]
    _ ≤ |-(α - 1) * Real.exp (-t)|
          + |Real.exp (-t) * ∫ s in (0 : ℝ)..t, Real.exp s * (f s - α)| :=
          abs_add_le _ _
    _ = |α - 1| * Real.exp (-t)
          + Real.exp (-t) * |∫ s in (0 : ℝ)..t, Real.exp s * (f s - α)| := by
          rw [abs_mul, habs_exp, abs_neg, abs_mul, habs_exp]
    _ ≤ |α - 1| * Real.exp (-t) + Real.exp (-t) * (ε * (Real.exp t - 1)) := by
          gcongr
    _ = |α - 1| * Real.exp (-t) + ε * (1 - Real.exp (-t)) := by
          have : Real.exp (-t) * (Real.exp t - 1)
              = 1 - Real.exp (-t) := by
            have h : Real.exp (-t) * Real.exp t = 1 := by
              rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
            linear_combination h
          rw [show Real.exp (-t) * (ε * (Real.exp t - 1))
                = ε * (Real.exp (-t) * (Real.exp t - 1)) by ring, this]
    _ ≤ |α - 1| * Real.exp (-t) + ε := by
          have : ε * (1 - Real.exp (-t)) ≤ ε := by
            have hle : 1 - Real.exp (-t) ≤ 1 := by
              have := (Real.exp_pos (-t)).le
              linarith
            nlinarith [hε_nn, Real.exp_pos (-t)]
          linarith

/-! ## Witness derivatives for `u` and `v`

Define the analytic witnesses
  `U(t) := ln(1 + x₁(t))`,     `V(t) := x₁(t) / (1 + x₁(t))`.

Paper [BAC] §6 claims these satisfy the gadget ODEs for `u` and `v`
respectively. The lemmas below verify this at the derivative level: given
positivity `1 + x₁(t) > 0`, `U'(t) = (1 − V(t)) · x₁'(t)` and
`V'(t) = (1 − V(t))² · x₁'(t)`. Uniqueness then identifies the PIVP
trajectories `u` and `v` with `U` and `V` on `[0, T]` (separate lemma,
next round).
-/

/-- Derivative of the u-witness. If `x1` is differentiable at `t` and
`1 + x1(t) > 0`, then `U(t) := ln(1 + x1(t))` has derivative
`x1'(t) / (1 + x1(t))`, i.e. `(1 − V(t)) · x1'(t)` where
`V(t) := x1(t)/(1 + x1(t))`. -/
theorem uWitness_hasDerivAt
    {x1 : ℝ → ℝ} {x1' : ℝ} {t : ℝ}
    (hx1 : HasDerivAt x1 x1' t)
    (hpos : 0 < 1 + x1 t) :
    HasDerivAt (fun s => Real.log (1 + x1 s)) (x1' / (1 + x1 t)) t := by
  have h_inner : HasDerivAt (fun s => 1 + x1 s) x1' t := hx1.const_add 1
  exact h_inner.log (ne_of_gt hpos)

/-- The u-witness derivative expressed in the ODE form
`(1 − V(t)) · x1'(t)`. -/
theorem uWitness_hasDerivAt_ode_form
    {x1 : ℝ → ℝ} {x1' : ℝ} {t : ℝ}
    (hx1 : HasDerivAt x1 x1' t)
    (hpos : 0 < 1 + x1 t) :
    HasDerivAt (fun s => Real.log (1 + x1 s))
      ((1 - x1 t / (1 + x1 t)) * x1') t := by
  have h := uWitness_hasDerivAt hx1 hpos
  have h_ne : 1 + x1 t ≠ 0 := ne_of_gt hpos
  convert h using 1
  field_simp
  ring

/-- Derivative of the v-witness. If `x1` is differentiable at `t` and
`1 + x1(t) > 0`, then `V(t) := x1(t) / (1 + x1(t))` has derivative
`x1'(t) / (1 + x1(t))²`. -/
theorem vWitness_hasDerivAt
    {x1 : ℝ → ℝ} {x1' : ℝ} {t : ℝ}
    (hx1 : HasDerivAt x1 x1' t)
    (hpos : 0 < 1 + x1 t) :
    HasDerivAt (fun s => x1 s / (1 + x1 s))
      (x1' / (1 + x1 t) ^ 2) t := by
  have h_denom : HasDerivAt (fun s => 1 + x1 s) x1' t := hx1.const_add 1
  have h_ne : 1 + x1 t ≠ 0 := ne_of_gt hpos
  have hquot := hx1.div h_denom h_ne
  convert! hquot using 1
  ring

/-- The v-witness derivative expressed in the ODE form
`(1 − V(t))² · x1'(t)`. -/
theorem vWitness_hasDerivAt_ode_form
    {x1 : ℝ → ℝ} {x1' : ℝ} {t : ℝ}
    (hx1 : HasDerivAt x1 x1' t)
    (hpos : 0 < 1 + x1 t) :
    HasDerivAt (fun s => x1 s / (1 + x1 s))
      ((1 - x1 t / (1 + x1 t)) ^ 2 * x1') t := by
  have h := vWitness_hasDerivAt hx1 hpos
  have h_ne : 1 + x1 t ≠ 0 := ne_of_gt hpos
  convert h using 1
  field_simp
  ring

/-- Derivative of the z-witness `Z(t) := exp(y(t) · u(t))`. Given
`HasDerivAt` hypotheses on `y` and `u`, product-rule + exp-chain yield
`Z'(t) = Z(t) · (y'(t)·u(t) + y(t)·u'(t))`. -/
theorem zWitness_hasDerivAt
    {y u : ℝ → ℝ} {y' u' : ℝ} {t : ℝ}
    (hy : HasDerivAt y y' t)
    (hu : HasDerivAt u u' t) :
    HasDerivAt (fun s => Real.exp (y s * u s))
      (Real.exp (y t * u t) * (y' * u t + y t * u')) t := by
  have hprod : HasDerivAt (fun s => y s * u s) (y' * u t + y t * u') t :=
    hy.mul hu
  exact hprod.exp

/-- The z-witness derivative in the PIVP ODE form. If
`u'(t) = (1 − v_t) · x1'(t)` (as given by `uWitness_hasDerivAt_ode_form`
with `v_t := V(t)`), then
  `Z'(t) = Z(t) · (y'(t)·u(t) + y(t)·(1 − v_t)·x1'(t))`,
matching the syntactic z-field of `powerPIVP`. -/
theorem zWitness_hasDerivAt_ode_form
    {y u : ℝ → ℝ} {y' x1' v_t : ℝ} {t : ℝ}
    (hy : HasDerivAt y y' t)
    (hu : HasDerivAt u ((1 - v_t) * x1') t) :
    HasDerivAt (fun s => Real.exp (y s * u s))
      (Real.exp (y t * u t) * (y' * u t + y t * (1 - v_t) * x1')) t := by
  have h := zWitness_hasDerivAt hy hu
  convert h using 1
  ring

/-! ## Witness uniqueness via Gronwall-zero

Having matched derivatives at the pointwise level, we now identify the
PIVP trajectories with the witnesses globally. The `v`-equation
`v' = (1 − v)² · x₁'` admits both `v` itself and `V(t) := x₁(t)/(1+x₁(t))`
as solutions with the same initial value `0`. Subtracting gives an
error satisfying a Lipschitz-like bound `|w'| ≤ K |w|`, and
Gronwall-zero pins it to `0`.

Once `v = V`, the `u`-equation becomes linear with a matching RHS for the
witness `U(t) := ln(1 + x₁(t))`, and similarly for `z` against
`Z(t) := exp(y(t) · u(t))`.
-/

/-- Uniqueness for the `v`-witness. If `v` satisfies the v-ODE
`v' = (1 − v)² · x1'` on `[0, T]` with `v(0) = 0` and `x1` is
differentiable with `1 + x1 > 0`, then `v(t) = x1(t)/(1 + x1(t))` for all
`t ∈ [0, T]`, provided the quadratic-factor product
`|x1'(t)| · |2 − v(t) − x1(t)/(1+x1(t))|` admits a uniform bound `K`.

The bound `K` is a free Lipschitz-constant parameter: in downstream
applications it comes from bounding `x1'` (from the low-pass ODE) and
the monotone cleanup of `v + V` (both in `[0, 1)` under the standard
input regime). -/
theorem vWitness_eq
    {x1 v : ℝ → ℝ} {x1' : ℝ → ℝ} {T K : ℝ}
    (hx1_deriv : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt x1 (x1' t) t)
    (hv_deriv : ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivAt v ((1 - v t) ^ 2 * x1' t) t)
    (hpos : ∀ t ∈ Icc (0 : ℝ) T, 0 < 1 + x1 t)
    (hx1_0 : x1 0 = 0) (hv0 : v 0 = 0)
    (hbound : ∀ t ∈ Icc (0 : ℝ) T,
      |x1' t| * |2 - v t - x1 t / (1 + x1 t)| ≤ K) :
    ∀ t ∈ Icc (0 : ℝ) T, v t = x1 t / (1 + x1 t) := by
  set V : ℝ → ℝ := fun t => x1 t / (1 + x1 t) with hV_def
  set w : ℝ → ℝ := fun t => v t - V t with hw_def
  -- Reduce to: w ≡ 0 on [0, T]
  suffices hzero : ∀ t ∈ Icc (0 : ℝ) T, w t = 0 by
    intro t ht
    have := hzero t ht
    have : v t - V t = 0 := this
    linarith
  -- w(0) = 0
  have hw0 : w 0 = 0 := by
    simp only [hw_def, hV_def, hv0, hx1_0]
    norm_num
  -- The error ODE: w'(t) = −x1'(t) · w(t) · (2 − v(t) − V(t))
  have hw_deriv : ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivAt w (-(x1' t) * w t * (2 - v t - V t)) t := by
    intro t ht
    have hV_der : HasDerivAt V ((1 - V t) ^ 2 * x1' t) t :=
      vWitness_hasDerivAt_ode_form (hx1_deriv t ht) (hpos t ht)
    have hsub := (hv_deriv t ht).sub hV_der
    convert! hsub using 1
    ring
  -- |w'(t)| ≤ K · |w(t)|
  have hw_bound : ∀ t ∈ Icc (0 : ℝ) T,
      |(-(x1' t) * w t * (2 - v t - V t))| ≤ K * |w t| := by
    intro t ht
    rw [show -(x1' t) * w t * (2 - v t - V t)
         = (x1' t * (2 - v t - V t)) * (-w t) from by ring,
        abs_mul, abs_neg, abs_mul]
    -- goal: |x1' t| * |2 - v t - V t| * |w t| ≤ K * |w t|
    exact mul_le_mul_of_nonneg_right (hbound t ht) (abs_nonneg _)
  -- Continuity of w on [0, T]
  have hw_cont : ContinuousOn w (Icc (0 : ℝ) T) := fun t ht =>
    (hw_deriv t ht).continuousAt.continuousWithinAt
  -- Right-derivative on [0, T)
  have hw_deriv_within : ∀ t ∈ Ico (0 : ℝ) T,
      HasDerivWithinAt w (-(x1' t) * w t * (2 - v t - V t)) (Ici t) t := by
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) T := ⟨ht.1, le_of_lt ht.2⟩
    exact (hw_deriv t ht').hasDerivWithinAt
  -- Gronwall-zero kernel
  have hbound_norm : ∀ t ∈ Ico (0 : ℝ) T,
      ‖-(x1' t) * w t * (2 - v t - V t)‖ ≤ K * ‖w t‖ := by
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) T := ⟨ht.1, le_of_lt ht.2⟩
    simpa [Real.norm_eq_abs] using hw_bound t ht'
  exact eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
    hw_cont hw_deriv_within hw0 hbound_norm

/-- **u-witness uniqueness.**  Once `v ≡ V = x1/(1+x1)` on `[0,T]`, the
ODE `u'(t) = (1 − v(t))·x1'(t)` forces `u(t) = ln(1 + x1(t))`.

Proof: the witness `U(t) := ln(1 + x1(t))` has `U'(t) = x1'(t)/(1+x1(t))
= (1 − V(t))·x1'(t) = (1 − v(t))·x1'(t)`, so `(u − U)' ≡ 0`.  With
`u(0) = U(0) = 0`, Gronwall-zero with `K = 0` gives `u ≡ U`. -/
theorem uWitness_eq
    {x1 u v : ℝ → ℝ} {x1' : ℝ → ℝ} {T : ℝ}
    (hx1_deriv : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt x1 (x1' t) t)
    (hu_deriv : ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivAt u ((1 - v t) * x1' t) t)
    (hpos : ∀ t ∈ Icc (0 : ℝ) T, 0 < 1 + x1 t)
    (hv_eq : ∀ t ∈ Icc (0 : ℝ) T, v t = x1 t / (1 + x1 t))
    (hx1_0 : x1 0 = 0) (hu0 : u 0 = 0) :
    ∀ t ∈ Icc (0 : ℝ) T, u t = Real.log (1 + x1 t) := by
  set U : ℝ → ℝ := fun t => Real.log (1 + x1 t) with hU_def
  set w : ℝ → ℝ := fun t => u t - U t with hw_def
  suffices hzero : ∀ t ∈ Icc (0 : ℝ) T, w t = 0 by
    intro t ht
    have := hzero t ht
    have : u t - U t = 0 := this
    linarith
  -- w(0) = 0
  have hw0 : w 0 = 0 := by
    simp only [hw_def, hU_def, hu0, hx1_0]
    simp
  -- Derivative of U via uWitness_hasDerivAt (ode form)
  have hU_der : ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivAt U ((1 - x1 t / (1 + x1 t)) * x1' t) t := by
    intro t ht
    exact uWitness_hasDerivAt_ode_form (hx1_deriv t ht) (hpos t ht)
  -- (u - U)' = 0 because (1 - v(t)) = (1 - V(t))
  have hw_deriv : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt w 0 t := by
    intro t ht
    have h1 : (1 - v t) * x1' t = (1 - x1 t / (1 + x1 t)) * x1' t := by
      rw [hv_eq t ht]
    have hsub := (hu_deriv t ht).sub (hU_der t ht)
    -- hsub : HasDerivAt w ((1 - v t) * x1' t - (1 - x1 t / (1+x1 t)) * x1' t) t
    simpa only [h1, sub_self] using! hsub
  -- Wrap for Gronwall-zero
  have hw_cont : ContinuousOn w (Icc (0 : ℝ) T) := fun t ht =>
    (hw_deriv t ht).continuousAt.continuousWithinAt
  have hw_deriv_within : ∀ t ∈ Ico (0 : ℝ) T,
      HasDerivWithinAt w 0 (Ici t) t := by
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) T := ⟨ht.1, le_of_lt ht.2⟩
    exact (hw_deriv t ht').hasDerivWithinAt
  have hbound_norm : ∀ t ∈ Ico (0 : ℝ) T,
      ‖(0 : ℝ)‖ ≤ (0 : ℝ) * ‖w t‖ := by
    intro _ _; simp
  exact eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
    hw_cont hw_deriv_within hw0 hbound_norm

/-- **z-witness uniqueness.**  With `u ≡ U = ln(1+x1)` and
`v ≡ V = x1/(1+x1)` already pinned, the ODE
`z'(t) = z(t) · (y'(t)·u(t) + y(t)·(1 − v(t))·x1'(t))` together with
`z(0) = 1` forces `z(t) = exp(y(t)·u(t))`.

Proof: letting `g(t) := y'(t)·u(t) + y(t)·(1 − v(t))·x1'(t)` be the
common multiplier, the witness `Z(t) := exp(y(t)·u(t))` satisfies
`Z'(t) = Z(t)·g(t)` (using `u' = (1−v)·x1'`), so `w := z − Z` obeys
`w' = w·g`; Gronwall-zero with `K` bounding `|g|` on `[0,T]` closes. -/
theorem zWitness_eq
    {u v y z : ℝ → ℝ} {x1' y' : ℝ → ℝ} {T K : ℝ}
    (hy_deriv : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt y (y' t) t)
    (hu_deriv : ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivAt u ((1 - v t) * x1' t) t)
    (hz_deriv : ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivAt z (z t * (y' t * u t + y t * ((1 - v t) * x1' t))) t)
    (hz0 : z 0 = 1) (hy0u0 : y 0 * u 0 = 0)
    (hbound : ∀ t ∈ Icc (0 : ℝ) T,
      |y' t * u t + y t * ((1 - v t) * x1' t)| ≤ K) :
    ∀ t ∈ Icc (0 : ℝ) T, z t = Real.exp (y t * u t) := by
  set g : ℝ → ℝ := fun t => y' t * u t + y t * ((1 - v t) * x1' t) with hg_def
  set Z : ℝ → ℝ := fun t => Real.exp (y t * u t) with hZ_def
  set w : ℝ → ℝ := fun t => z t - Z t with hw_def
  suffices hzero : ∀ t ∈ Icc (0 : ℝ) T, w t = 0 by
    intro t ht
    have := hzero t ht
    have : z t - Z t = 0 := this
    linarith
  -- w(0) = 0 since z(0) = 1 = exp(0) = exp(y(0)·u(0))
  have hw0 : w 0 = 0 := by
    simp only [hw_def, hZ_def, hz0, hy0u0]
    simp
  -- Derivative of Z: Z' = Z · (y'·u + y·u') = Z · g
  have hZ_der : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt Z (Z t * g t) t := by
    intro t ht
    have hyu : HasDerivAt (fun s => y s * u s)
        (y' t * u t + y t * ((1 - v t) * x1' t)) t :=
      (hy_deriv t ht).mul (hu_deriv t ht)
    have hZraw : HasDerivAt Z
        (Real.exp (y t * u t) * (y' t * u t + y t * ((1 - v t) * x1' t))) t :=
      hyu.exp
    convert hZraw using 1
  -- w' = z·g - Z·g = w·g
  have hw_deriv : ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivAt w (w t * g t) t := by
    intro t ht
    have hsub := (hz_deriv t ht).sub (hZ_der t ht)
    convert! hsub using 1
    simp only [hw_def, hg_def]
    ring
  -- |w'| ≤ K · |w|
  have hw_bound : ∀ t ∈ Icc (0 : ℝ) T, |w t * g t| ≤ K * |w t| := by
    intro t ht
    rw [abs_mul, mul_comm K (|w t|)]
    exact mul_le_mul_of_nonneg_left (hbound t ht) (abs_nonneg _)
  -- Wrap for Gronwall-zero
  have hw_cont : ContinuousOn w (Icc (0 : ℝ) T) := fun t ht =>
    (hw_deriv t ht).continuousAt.continuousWithinAt
  have hw_deriv_within : ∀ t ∈ Ico (0 : ℝ) T,
      HasDerivWithinAt w (w t * g t) (Ici t) t := by
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) T := ⟨ht.1, le_of_lt ht.2⟩
    exact (hw_deriv t ht').hasDerivWithinAt
  have hbound_norm : ∀ t ∈ Ico (0 : ℝ) T,
      ‖w t * g t‖ ≤ K * ‖w t‖ := by
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) T := ⟨ht.1, le_of_lt ht.2⟩
    simpa [Real.norm_eq_abs] using hw_bound t ht'
  exact eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
    hw_cont hw_deriv_within hw0 hbound_norm

/-! ### Qualitative convergence

Given the three uniqueness identities above, convergence of the driving
signal `f(t) → α` lifts through the chain

  x1(t) → α − 1   (tracking_bound with `ε → 0`)
  u(t)  → log α   (continuity of log at α > 0)
  z(t)  → α^β     (continuity of exp ∘ (y × u), and `y(t) → β` by hypothesis)

The modulus (Thm 6.3: max(μ_α, μ_β) + O(1)) will be quantified in a
follow-up lemma; these `Tendsto`-level lifts expose the topological
skeleton.
-/

open Filter Topology

/-- **Log lift.**  If `x1(t) → α − 1` and `α > 0`, then
`log(1 + x1(t)) → log α`. -/
theorem log_tendsto_of_lowpass
    {x1 : ℝ → ℝ} {α : ℝ} (hα : 0 < α)
    (hx1 : Tendsto x1 atTop (𝓝 (α - 1))) :
    Tendsto (fun t => Real.log (1 + x1 t)) atTop (𝓝 (Real.log α)) := by
  have h1 : Tendsto (fun t => 1 + x1 t) atTop (𝓝 (1 + (α - 1))) :=
    tendsto_const_nhds.add hx1
  have hα_eq : (1 + (α - 1) : ℝ) = α := by ring
  rw [hα_eq] at h1
  exact (Real.continuousAt_log hα.ne').tendsto.comp h1

/-- **Exp-product lift.**  If `y(t) → β` and `u(t) → v`, then
`exp(y(t) · u(t)) → exp(β · v)`. -/
theorem exp_mul_tendsto
    {y u : ℝ → ℝ} {β v : ℝ}
    (hy : Tendsto y atTop (𝓝 β))
    (hu : Tendsto u atTop (𝓝 v)) :
    Tendsto (fun t => Real.exp (y t * u t)) atTop (𝓝 (Real.exp (β * v))) :=
  Real.continuous_exp.tendsto _ |>.comp (hy.mul hu)

/-- **Full convergence.**  Combining the log and exp lifts, if the
low-pass tracks (`x1(t) → α − 1` with `α > 0`), the β input tracks
(`y(t) → β`), and the witness identities `u ≡ log(1+x1)`,
`z ≡ exp(y·u)` hold eventually, then `z(t) → α^β`.

The two `EventuallyEq` hypotheses come from `uWitness_eq` / `zWitness_eq`
applied on a half-line — packaging them at the filter level keeps this
theorem independent of any particular time bound `T`. -/
theorem zWitness_tendsto_rpow
    {x1 u y z : ℝ → ℝ} {α β : ℝ} (hα : 0 < α)
    (hx1 : Tendsto x1 atTop (𝓝 (α - 1)))
    (hy : Tendsto y atTop (𝓝 β))
    (hu_eq : u =ᶠ[atTop] fun t => Real.log (1 + x1 t))
    (hz_eq : z =ᶠ[atTop] fun t => Real.exp (y t * u t)) :
    Tendsto z atTop (𝓝 (α ^ β)) := by
  have hu_lim : Tendsto u atTop (𝓝 (Real.log α)) :=
    (log_tendsto_of_lowpass hα hx1).congr' hu_eq.symm
  have hz_lim : Tendsto z atTop (𝓝 (Real.exp (β * Real.log α))) :=
    (exp_mul_tendsto hy hu_lim).congr' hz_eq.symm
  rw [Real.rpow_def_of_pos hα, mul_comm]
  exact hz_lim

/-! ### Quantitative modulus (Thm 6.3 kernel)

Toward the paper's `max(μ_α, μ_β) + O(1)` bound we need analytic
modulus lemmas.  First: a Lipschitz estimate for `log` restricted to
`[m, ∞)` with `m > 0`. -/

/-- **Log modulus.**  For positive reals `a, b ≥ m > 0`,
`|log a − log b| ≤ |a − b| / m`.

Proof: `Real.log` is differentiable on `Ici m` with derivative `1/x`
bounded in norm by `1/m`; apply MVT on the convex set `Ici m`. -/
theorem abs_log_sub_log_le_div
    {a b m : ℝ} (hm : 0 < m) (ha : m ≤ a) (hb : m ≤ b) :
    |Real.log a - Real.log b| ≤ |a - b| / m := by
  have h_conv : Convex ℝ (Ici m) := convex_Ici m
  have hd : ∀ x ∈ Ici m, DifferentiableAt ℝ Real.log x := fun x hx =>
    Real.differentiableAt_log (by have := hm.trans_le hx; linarith)
  have hbound : ∀ x ∈ Ici m, ‖deriv Real.log x‖ ≤ 1 / m := by
    intro x hx
    have hx_pos : 0 < x := hm.trans_le hx
    rw [Real.deriv_log, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hx_pos),
        inv_eq_one_div]
    exact one_div_le_one_div_of_le hm hx
  have hab :=
    h_conv.norm_image_sub_le_of_norm_deriv_le hd hbound hb ha
  calc |Real.log a - Real.log b|
      = ‖Real.log a - Real.log b‖ := (Real.norm_eq_abs _).symm
    _ ≤ 1 / m * ‖a - b‖ := hab
    _ = |a - b| / m := by rw [Real.norm_eq_abs]; ring

/-- **Exp modulus.**  For `a, b ≤ M`, `|exp a − exp b| ≤ exp M · |a − b|`.

Proof: `Real.exp` is its own derivative, bounded by `exp M` on `Iic M`;
apply MVT on the convex set `Iic M`. -/
theorem abs_exp_sub_exp_le_mul
    {a b M : ℝ} (ha : a ≤ M) (hb : b ≤ M) :
    |Real.exp a - Real.exp b| ≤ Real.exp M * |a - b| := by
  have h_conv : Convex ℝ (Iic M) := convex_Iic M
  have hd : ∀ x ∈ Iic M, DifferentiableAt ℝ Real.exp x :=
    fun x _ => Real.differentiableAt_exp
  have hbound : ∀ x ∈ Iic M, ‖deriv Real.exp x‖ ≤ Real.exp M := by
    intro x hx
    rw [Real.deriv_exp, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr hx
  have hab :=
    h_conv.norm_image_sub_le_of_norm_deriv_le hd hbound hb ha
  simpa [Real.norm_eq_abs] using hab

/-- **Product modulus.**  `|y·u − β·v| ≤ |y|·|u − v| + |v|·|y − β|`,
a bilinear split useful for combining the `u`-tracking and `y`-tracking
bounds. -/
theorem abs_mul_sub_mul_le
    (y u β v : ℝ) :
    |y * u - β * v| ≤ |y| * |u - v| + |v| * |y - β| := by
  have h : y * u - β * v = y * (u - v) + v * (y - β) := by ring
  calc |y * u - β * v|
      = |y * (u - v) + v * (y - β)| := by rw [h]
    _ ≤ |y * (u - v)| + |v * (y - β)| := abs_add_le _ _
    _ = |y| * |u - v| + |v| * |y - β| := by rw [abs_mul, abs_mul]

/-- **Composite modulus for `exp ∘ (· * ·)`.**  Given upper bounds
`y·u ≤ M` and `β·v ≤ M`, and any `|y|`-bound `Y`,

  |exp(y·u) − exp(β·v)| ≤ exp M · (Y · |u − v| + |v| · |y − β|).

This is the `exp_modulus ∘ product_split` half of Thm 6.3;
plugging `v = log α` and combining with `abs_log_sub_log_le_div` gives
the full modulus for `|z(t) − α^β|`. -/
theorem abs_exp_mul_sub_exp_mul_le
    {y u β v M Y : ℝ}
    (hyu : y * u ≤ M) (hβv : β * v ≤ M) (hY : |y| ≤ Y) :
    |Real.exp (y * u) - Real.exp (β * v)|
      ≤ Real.exp M * (Y * |u - v| + |v| * |y - β|) := by
  have hexp := abs_exp_sub_exp_le_mul hyu hβv
  have hsplit := abs_mul_sub_mul_le y u β v
  have hYnn : 0 ≤ Y := (abs_nonneg y).trans hY
  have hM_pos : 0 < Real.exp M := Real.exp_pos _
  have hsplit' : |y * u - β * v| ≤ Y * |u - v| + |v| * |y - β| := by
    refine hsplit.trans ?_
    have h1 : |y| * |u - v| ≤ Y * |u - v| :=
      mul_le_mul_of_nonneg_right hY (abs_nonneg _)
    linarith
  calc |Real.exp (y * u) - Real.exp (β * v)|
      ≤ Real.exp M * |y * u - β * v| := hexp
    _ ≤ Real.exp M * (Y * |u - v| + |v| * |y - β| ) :=
        mul_le_mul_of_nonneg_left hsplit' hM_pos.le

/-- **u-tracking from x1-tracking.**  If `u(t) = log(1 + x1(t))`,
`m ≤ 1 + x1(t)`, `m ≤ α` with `m > 0`, and `|x1(t) − (α−1)| ≤ δ`,
then `|u(t) − log α| ≤ δ / m`.

Uses `u = log(1+x1)` combined with `abs_log_sub_log_le_div` on
`(1 + x1(t))` and `α`. -/
theorem abs_u_sub_log_le_of_tracking
    {x1 u : ℝ → ℝ} {α m δ t : ℝ}
    (hm : 0 < m)
    (hu_eq : u t = Real.log (1 + x1 t))
    (h_lb : m ≤ 1 + x1 t) (hα_lb : m ≤ α)
    (htrack : |x1 t - (α - 1)| ≤ δ) :
    |u t - Real.log α| ≤ δ / m := by
  rw [hu_eq]
  have hab := abs_log_sub_log_le_div hm h_lb hα_lb
  have hreduce : 1 + x1 t - α = x1 t - (α - 1) := by ring
  calc |Real.log (1 + x1 t) - Real.log α|
      ≤ |1 + x1 t - α| / m := hab
    _ = |x1 t - (α - 1)| / m := by rw [hreduce]
    _ ≤ δ / m := by exact div_le_div_of_nonneg_right htrack hm.le

/-- **Full α^β modulus** (Thm 6.3 core). Combining the witness identity
`u = log(1+x1)`, the low-pass tracking, the input β modulus, and the
exp/log/product estimates:

  |exp(y(t)·u(t)) − α^β| ≤ exp M · (Y/m · δ_x + |log α| · δ_y).

Here
- `M` is an upper bound on both `y(t)·u(t)` and `β·log α`,
- `Y` bounds `|y(t)|`,
- `m > 0` bounds both `1 + x1(t)` and `α` from below,
- `δ_x` bounds `|x1(t) − (α−1)|` (from `lowpass_tracking_bound`),
- `δ_y` bounds `|y(t) − β|` (β input modulus).

In the paper's framing, `δ_x ≤ |α−1|·e^{−t} + ε_f` and `δ_y → 0`
with modulus `μ_β`; composing gives `max(μ_α, μ_β) + O(1)`. -/
theorem abs_zWitness_sub_rpow_le
    {x1 u y : ℝ → ℝ} {α β M Y m δx δy t : ℝ}
    (hα : 0 < α) (hm : 0 < m)
    (hu_eq : u t = Real.log (1 + x1 t))
    (h_lb : m ≤ 1 + x1 t) (hα_lb : m ≤ α)
    (htrack_x : |x1 t - (α - 1)| ≤ δx)
    (htrack_y : |y t - β| ≤ δy)
    (hyu : y t * u t ≤ M) (hβlogα : β * Real.log α ≤ M)
    (hY : |y t| ≤ Y) :
    |Real.exp (y t * u t) - α ^ β|
      ≤ Real.exp M * (Y / m * δx + |Real.log α| * δy) := by
  -- Rewrite α^β as exp(β · log α).
  have hrpow : α ^ β = Real.exp (β * Real.log α) := by
    rw [Real.rpow_def_of_pos hα, mul_comm]
  rw [hrpow]
  -- Composite exp·product modulus.
  have hexp_prod :=
    abs_exp_mul_sub_exp_mul_le (y := y t) (u := u t)
      (β := β) (v := Real.log α) (M := M) (Y := Y)
      hyu hβlogα hY
  -- Lift u-tracking via log modulus.
  have hu_bound : |u t - Real.log α| ≤ δx / m :=
    abs_u_sub_log_le_of_tracking (t := t) hm hu_eq h_lb hα_lb htrack_x
  -- Bound each summand.
  have hYnn : 0 ≤ Y := (abs_nonneg _).trans hY
  have hterm1 : Y * |u t - Real.log α| ≤ Y * (δx / m) :=
    mul_le_mul_of_nonneg_left hu_bound hYnn
  have hterm2 : |Real.log α| * |y t - β| ≤ |Real.log α| * δy :=
    mul_le_mul_of_nonneg_left htrack_y (abs_nonneg _)
  have hsum :
      Y * |u t - Real.log α| + |Real.log α| * |y t - β|
        ≤ Y / m * δx + |Real.log α| * δy := by
    have hreorg : Y * (δx / m) = Y / m * δx := by ring
    linarith [hterm1, hterm2]
  have hM_nn : 0 ≤ Real.exp M := (Real.exp_pos _).le
  exact hexp_prod.trans (mul_le_mul_of_nonneg_left hsum hM_nn)

end Ripple.DualRail.Power
