import Mathlib

/-!
Ripple.BoundedUniversality.BGP.SelectorDuhamelWrite
--------------------------------

A scalar Gronwall / integrating-factor estimate for a moving-target write
ODE.  This is the sup-norm version of the Duhamel write estimate: the moving
part contributes with the damped factor `1 - exp(-∫ k)` rather than as an
undamped additive full-window error.
-/

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open Real intervalIntegral
open scoped Topology BigOperators

private theorem integral_primitive_hasDerivAt_right_of_continuousOn_Icc
    (g : ℝ → ℝ) {a b t : ℝ}
    (hg_cont : ContinuousOn g (Set.Icc a b))
    (ht : t ∈ Set.Ioo a b) :
    HasDerivAt (fun u : ℝ => ∫ s in a..u, g s) (g t) t := by
  have htIcc : t ∈ Set.Icc a b := Set.Ioo_subset_Icc_self ht
  have hat : ContinuousAt g t :=
    (hg_cont.continuousWithinAt htIcc).continuousAt
      (Icc_mem_nhds ht.1 ht.2)
  have hint : IntervalIntegrable g MeasureTheory.volume a t := by
    exact (hg_cont.mono (Set.Icc_subset_Icc_right ht.2.le)).intervalIntegrable_of_Icc ht.1.le
  have hmeas : StronglyMeasurableAtFilter g (𝓝 t) MeasureTheory.volume :=
    ContinuousAt.stronglyMeasurableAtFilter (s := Set.Ioo a b) isOpen_Ioo
      (fun x hx =>
        (hg_cont.continuousWithinAt (Set.Ioo_subset_Icc_self hx)).continuousAt
          (Icc_mem_nhds hx.1 hx.2)) t ht
  exact intervalIntegral.integral_hasDerivAt_right hint
    hmeas hat

/--
Gronwall moving-target write bound.

If `y' = k(t) * (m(t) - y(t))` on `[a,b]`, with `k ≥ 0`, and the moving target
stays within `δsup` of a fixed target `M`, then the endpoint error is bounded
by the initial error damped by the full write mass plus the damped target
variation term.
-/
theorem stack_write_gronwall_sup_bound
    (y m k : ℝ → ℝ) (M a b : ℝ)
    (hab : a ≤ b)
    (hk_cont : Continuous k)
    (hk_nonneg : ∀ t ∈ Set.Icc a b, 0 ≤ k t)
    (hm_cont : Continuous m)
    (hy_ode : ∀ t ∈ Set.Icc a b, HasDerivAt y (k t * (m t - y t)) t)
    {δsup : ℝ}
    (hmsup : ∀ t ∈ Set.Icc a b, |m t - M| ≤ δsup) :
    |y b - M| ≤ Real.exp (-(∫ t in a..b, k t)) * |y a - M| +
      δsup * (1 - Real.exp (-(∫ t in a..b, k t))) := by
  -- Forward accumulated write mass from `a` to `t`.
  set Φ : ℝ → ℝ := fun t => ∫ s in a..t, k s with hΦdef
  have hΦderiv : ∀ t : ℝ, HasDerivAt Φ (k t) t := by
    intro t
    exact intervalIntegral.integral_hasDerivAt_right
      (hk_cont.intervalIntegrable a t)
      (hk_cont.stronglyMeasurableAtFilter _ _)
      hk_cont.continuousAt
  have hΦa : Φ a = 0 := by
    simp [Φ]
  have hΦcont : Continuous Φ := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (hΦderiv t).continuousAt

  -- Integrating factor.
  set E : ℝ → ℝ := fun t => Real.exp (Φ t) with hEdef
  have hEderiv : ∀ t : ℝ, HasDerivAt E (k t * E t) t := by
    intro t
    have h2 := (hΦderiv t).exp
    convert h2 using 1
    simp only [E]
    ring
  have hEcont : Continuous E := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (hEderiv t).continuousAt
  have hEpos : ∀ t, 0 < E t := fun t => Real.exp_pos _
  have hEa : E a = 1 := by
    simp [E, hΦa]
  have hEb_eq : E b = Real.exp (∫ t in a..b, k t) := by
    simp [E, Φ]

  -- Differentiate `(y - M) * E`.
  set v : ℝ → ℝ := fun t => (y t - M) * E t with hvdef
  have hvderiv : ∀ t ∈ Set.Icc a b,
      HasDerivAt v (k t * (m t - M) * E t) t := by
    intro t ht
    have hyM : HasDerivAt (fun τ => y τ - M) (k t * (m t - y t)) t :=
      (hy_ode t ht).sub_const M
    have hprod := hyM.mul (hEderiv t)
    convert hprod using 1
    simp only [E]
    ring

  have hmM_cont : Continuous fun t => m t - M := hm_cont.sub continuous_const
  have h_integrand_cont : Continuous fun t => k t * (m t - M) * E t :=
    (hk_cont.mul hmM_cont).mul hEcont

  have hv_ftc :
      (∫ t in a..b, k t * (m t - M) * E t) = v b - v a := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro t ht
      rw [Set.uIcc_of_le hab] at ht
      exact hvderiv t ht
    · exact h_integrand_cont.intervalIntegrable a b

  -- Integral of the integrating-factor derivative.
  have hE_ftc : (∫ t in a..b, k t * E t) = E b - E a := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro t _
      exact hEderiv t
    · exact (hk_cont.mul hEcont).intervalIntegrable a b

  have hδ0 : 0 ≤ δsup :=
    le_trans (abs_nonneg _) (hmsup a (Set.left_mem_Icc.mpr hab))

  have hbound : |v b - v a| ≤ δsup * (E b - 1) := by
    rw [← hv_ftc]
    have h1 : |∫ t in a..b, k t * (m t - M) * E t|
        ≤ ∫ t in a..b, |k t * (m t - M) * E t| :=
      intervalIntegral.abs_integral_le_integral_abs hab
    have h2 : (∫ t in a..b, |k t * (m t - M) * E t|)
        ≤ ∫ t in a..b, δsup * (k t * E t) := by
      apply intervalIntegral.integral_mono_on hab
      · exact (h_integrand_cont.abs).intervalIntegrable a b
      · exact (continuous_const.mul (hk_cont.mul hEcont)).intervalIntegrable a b
      · intro t ht
        have hk0 : 0 ≤ k t := hk_nonneg t ht
        have hE0 : 0 ≤ E t := (hEpos t).le
        have hwt := hmsup t ht
        have hkE0 : 0 ≤ k t * E t := mul_nonneg hk0 hE0
        calc
          |k t * (m t - M) * E t|
              = (k t * E t) * |m t - M| := by
                rw [abs_mul, abs_mul, abs_of_nonneg hk0, abs_of_nonneg hE0]
                ring
          _ ≤ (k t * E t) * δsup :=
                mul_le_mul_of_nonneg_left hwt hkE0
          _ = δsup * (k t * E t) := by ring
    have h3 : (∫ t in a..b, δsup * (k t * E t)) = δsup * (E b - 1) := by
      rw [intervalIntegral.integral_const_mul, hE_ftc, hEa]
    exact le_trans h1 (le_trans h2 (le_of_eq h3))

  have hvb : |v b| ≤ |v a| + δsup * (E b - 1) := by
    have h := abs_sub_abs_le_abs_sub (v b) (v a)
    linarith [hbound]
  have hva : |v a| = |y a - M| := by
    simp [hvdef, hEa]
  have hvb' : |v b| = |y b - M| * E b := by
    rw [hvdef]
    rw [abs_mul, abs_of_pos (hEpos b)]
  rw [hva, hvb'] at hvb

  have hEbpos := hEpos b
  have hmain :
      |y b - M| ≤ |y a - M| / E b + δsup * ((E b - 1) / E b) := by
    calc
      |y b - M| ≤ (|y a - M| + δsup * (E b - 1)) / E b := by
        exact (le_div_iff₀ hEbpos).mpr hvb
      _ = |y a - M| / E b + δsup * ((E b - 1) / E b) := by
        field_simp [ne_of_gt hEbpos]
        try ring

  have hInv : (1 : ℝ) / E b = Real.exp (-(∫ t in a..b, k t)) := by
    rw [hEb_eq, one_div, Real.exp_neg]
  calc
    |y b - M| ≤ |y a - M| / E b + δsup * ((E b - 1) / E b) := hmain
    _ = Real.exp (-(∫ t in a..b, k t)) * |y a - M| +
        δsup * (1 - Real.exp (-(∫ t in a..b, k t))) := by
          rw [← hInv]
          field_simp [ne_of_gt hEbpos]
          try ring

/--
Integrating-factor weighted form of the write estimate.

This keeps the target movement under the weighted Duhamel integral before the
terminal-kernel rewrite.
-/
theorem stack_write_gronwall_weighted_ifactor_bound
    (y m k : ℝ → ℝ) (M a b : ℝ)
    (hab : a ≤ b)
    (hk_cont : Continuous k)
    (hk_nonneg : ∀ t ∈ Set.Icc a b, 0 ≤ k t)
    (hm_cont : Continuous m)
    (hy_ode : ∀ t ∈ Set.Icc a b, HasDerivAt y (k t * (m t - y t)) t) :
    |y b - M| ≤ Real.exp (-(∫ t in a..b, k t)) * |y a - M| +
      Real.exp (-(∫ t in a..b, k t)) *
        (∫ t in a..b,
          k t * |m t - M| * Real.exp (∫ s in a..t, k s)) := by
  set Φ : ℝ → ℝ := fun t => ∫ s in a..t, k s with hΦdef
  have hΦderiv : ∀ t : ℝ, HasDerivAt Φ (k t) t := by
    intro t
    exact intervalIntegral.integral_hasDerivAt_right
      (hk_cont.intervalIntegrable a t)
      (hk_cont.stronglyMeasurableAtFilter _ _)
      hk_cont.continuousAt
  have hΦa : Φ a = 0 := by
    simp [Φ]
  have hΦcont : Continuous Φ := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (hΦderiv t).continuousAt
  set E : ℝ → ℝ := fun t => Real.exp (Φ t) with hEdef
  have hEderiv : ∀ t : ℝ, HasDerivAt E (k t * E t) t := by
    intro t
    have h2 := (hΦderiv t).exp
    convert h2 using 1
    simp only [E]
    ring
  have hEcont : Continuous E := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (hEderiv t).continuousAt
  have hEpos : ∀ t, 0 < E t := fun t => Real.exp_pos _
  have hEa : E a = 1 := by
    simp [E, hΦa]
  have hEb_eq : E b = Real.exp (∫ t in a..b, k t) := by
    simp [E, Φ]
  set v : ℝ → ℝ := fun t => (y t - M) * E t with hvdef
  have hvderiv : ∀ t ∈ Set.Icc a b,
      HasDerivAt v (k t * (m t - M) * E t) t := by
    intro t ht
    have hyM : HasDerivAt (fun τ => y τ - M) (k t * (m t - y t)) t :=
      (hy_ode t ht).sub_const M
    have hprod := hyM.mul (hEderiv t)
    convert hprod using 1
    simp only [E]
    ring
  have hmM_cont : Continuous fun t => m t - M := hm_cont.sub continuous_const
  have hmM_abs_cont : Continuous fun t => |m t - M| := hmM_cont.abs
  have h_integrand_cont : Continuous fun t => k t * (m t - M) * E t :=
    (hk_cont.mul hmM_cont).mul hEcont
  have h_weighted_cont : Continuous fun t => k t * |m t - M| * E t :=
    (hk_cont.mul hmM_abs_cont).mul hEcont
  have hv_ftc :
      (∫ t in a..b, k t * (m t - M) * E t) = v b - v a := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro t ht
      rw [Set.uIcc_of_le hab] at ht
      exact hvderiv t ht
    · exact h_integrand_cont.intervalIntegrable a b
  have hbound :
      |v b - v a| ≤ ∫ t in a..b, k t * |m t - M| * E t := by
    rw [← hv_ftc]
    have h1 : |∫ t in a..b, k t * (m t - M) * E t|
        ≤ ∫ t in a..b, |k t * (m t - M) * E t| :=
      intervalIntegral.abs_integral_le_integral_abs hab
    have h2 : (∫ t in a..b, |k t * (m t - M) * E t|)
        ≤ ∫ t in a..b, k t * |m t - M| * E t := by
      apply intervalIntegral.integral_mono_on hab
      · exact h_integrand_cont.abs.intervalIntegrable a b
      · exact h_weighted_cont.intervalIntegrable a b
      · intro t ht
        have htIcc : t ∈ Set.Icc a b := ht
        have hk0 : 0 ≤ k t := hk_nonneg t htIcc
        have hE0 : 0 ≤ E t := (hEpos t).le
        apply le_of_eq
        rw [abs_mul, abs_mul, abs_of_nonneg hk0, abs_of_nonneg hE0]
    exact le_trans h1 h2
  have hvb : |v b| ≤ |v a| + ∫ t in a..b, k t * |m t - M| * E t := by
    have h := abs_sub_abs_le_abs_sub (v b) (v a)
    linarith [hbound]
  have hva : |v a| = |y a - M| := by
    simp [hvdef, hEa]
  have hvb' : |v b| = |y b - M| * E b := by
    rw [hvdef]
    rw [abs_mul, abs_of_pos (hEpos b)]
  rw [hva, hvb'] at hvb
  have hEbpos := hEpos b
  have hmain :
      |y b - M| ≤ |y a - M| / E b +
        (∫ t in a..b, k t * |m t - M| * E t) / E b := by
    calc
      |y b - M| ≤
          (|y a - M| + ∫ t in a..b, k t * |m t - M| * E t) / E b := by
        exact (le_div_iff₀ hEbpos).mpr hvb
      _ = |y a - M| / E b +
          (∫ t in a..b, k t * |m t - M| * E t) / E b := by
        field_simp [ne_of_gt hEbpos]
  have hInv : (1 : ℝ) / E b = Real.exp (-(∫ t in a..b, k t)) := by
    rw [hEb_eq, one_div, Real.exp_neg]
  have hweighted_eq :
      (∫ t in a..b, k t * |m t - M| * E t) =
        ∫ t in a..b,
          k t * |m t - M| * Real.exp (∫ s in a..t, k s) := by
    apply intervalIntegral.integral_congr
    intro t _ht
    simp [hEdef, hΦdef]
  calc
    |y b - M| ≤ |y a - M| / E b +
        (∫ t in a..b, k t * |m t - M| * E t) / E b := hmain
    _ = Real.exp (-(∫ t in a..b, k t)) * |y a - M| +
        Real.exp (-(∫ t in a..b, k t)) *
          (∫ t in a..b, k t * |m t - M| * Real.exp (∫ s in a..t, k s)) := by
      rw [hweighted_eq, ← hInv]
      simp only [E]
      field_simp [ne_of_gt hEbpos]

/-- Rewrite the integrating-factor weighted term as the terminal Duhamel kernel. -/
theorem stack_write_weighted_ifactor_eq_terminal_kernel
    (m k : ℝ → ℝ) (M a b : ℝ)
    (hk_cont : Continuous k) :
    Real.exp (-(∫ t in a..b, k t)) *
        (∫ t in a..b,
          k t * |m t - M| * Real.exp (∫ s in a..t, k s)) =
      ∫ t in a..b,
        Real.exp (-(∫ s in t..b, k s)) * k t * |m t - M| := by
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t _ht
  have hsplit :
      (∫ s in a..b, k s) = (∫ s in a..t, k s) + (∫ s in t..b, k s) := by
    exact (intervalIntegral.integral_add_adjacent_intervals
      (hk_cont.intervalIntegrable a t)
      (hk_cont.intervalIntegrable t b)).symm
  set A : ℝ := ∫ s in a..t, k s with hA
  set B : ℝ := ∫ s in t..b, k s with hB
  calc
    Real.exp (-(∫ s in a..b, k s)) *
        (k t * |m t - M| * Real.exp (∫ s in a..t, k s))
        = Real.exp (-(A + B)) * (k t * |m t - M| * Real.exp A) := by
          rw [hsplit]
    _ = Real.exp (-B) * k t * |m t - M| := by
          rw [show
            Real.exp (-(A + B)) * (k t * |m t - M| * Real.exp A) =
              (Real.exp (-(A + B)) * Real.exp A) * k t * |m t - M| by
            ring]
          rw [← Real.exp_add]
          have hlin : -(A + B) + A = -B := by ring
          rw [hlin]
    _ = Real.exp (-(∫ s in t..b, k s)) * k t * |m t - M| := by
          rw [hB]

/--
Weighted Gronwall moving-target write bound.

This keeps the moving-target error under the backward Duhamel kernel instead of
replacing it by a full-window supremum.
-/
theorem stack_write_gronwall_weighted_bound
    (y m k : ℝ → ℝ) (M a b : ℝ)
    (hab : a ≤ b)
    (hk_cont : Continuous k)
    (hk_nonneg : ∀ t ∈ Set.Icc a b, 0 ≤ k t)
    (hm_cont : Continuous m)
    (hy_ode : ∀ t ∈ Set.Icc a b, HasDerivAt y (k t * (m t - y t)) t) :
    |y b - M| ≤ Real.exp (-(∫ t in a..b, k t)) * |y a - M| +
        ∫ t in a..b,
          Real.exp (-(∫ s in t..b, k s)) * k t * |m t - M| := by
  have h0 := stack_write_gronwall_weighted_ifactor_bound
    y m k M a b hab hk_cont hk_nonneg hm_cont hy_ode
  rw [stack_write_weighted_ifactor_eq_terminal_kernel m k M a b hk_cont] at h0
  exact h0

/-- Inhomogeneous scalar Duhamel endpoint bound.

If `e' = - k e + src` on `[a,b]`, then the terminal error is bounded by the
initial error damped by the integrating factor plus the source against the
terminal Duhamel kernel. -/
theorem abs_inhomogeneous_decay_bound
    (e src k : ℝ → ℝ) {a b E0 S : ℝ}
    (hab : a ≤ b)
    (hk_cont : Continuous k)
    (hsrc_cont : Continuous src)
    (he_deriv : ∀ t ∈ Set.Icc a b,
      HasDerivAt e (-(k t) * e t + src t) t)
    (hinit : |e a| ≤ E0)
    (hsource :
      (∫ t in a..b,
        Real.exp (-(∫ s in t..b, k s)) * |src t|) ≤ S) :
    |e b| ≤ Real.exp (-(∫ s in a..b, k s)) * E0 + S := by
  set Φ : ℝ → ℝ := fun t => ∫ s in a..t, k s with hΦdef
  have hΦderiv : ∀ t : ℝ, HasDerivAt Φ (k t) t := by
    intro t
    exact intervalIntegral.integral_hasDerivAt_right
      (hk_cont.intervalIntegrable a t)
      (hk_cont.stronglyMeasurableAtFilter _ _)
      hk_cont.continuousAt
  have hΦa : Φ a = 0 := by
    simp [Φ]
  have hΦcont : Continuous Φ := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (hΦderiv t).continuousAt
  set E : ℝ → ℝ := fun t => Real.exp (Φ t) with hEdef
  have hEderiv : ∀ t : ℝ, HasDerivAt E (k t * E t) t := by
    intro t
    have h := (hΦderiv t).exp
    convert h using 1
    simp only [E]
    ring
  have hEcont : Continuous E := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (hEderiv t).continuousAt
  have hEpos : ∀ t, 0 < E t := fun t => Real.exp_pos _
  have hEa : E a = 1 := by
    simp [E, hΦa]
  have hEb_eq : E b = Real.exp (∫ t in a..b, k t) := by
    simp [E, Φ]
  set v : ℝ → ℝ := fun t => e t * E t with hvdef
  have hvderiv : ∀ t ∈ Set.Icc a b,
      HasDerivAt v (src t * E t) t := by
    intro t ht
    have hprod := (he_deriv t ht).mul (hEderiv t)
    convert hprod using 1
    simp only [E]
    ring
  have h_integrand_cont : Continuous fun t => src t * E t :=
    hsrc_cont.mul hEcont
  have h_weighted_cont : Continuous fun t => |src t| * E t :=
    hsrc_cont.abs.mul hEcont
  have hv_ftc :
      (∫ t in a..b, src t * E t) = v b - v a := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro t ht
      rw [Set.uIcc_of_le hab] at ht
      exact hvderiv t ht
    · exact h_integrand_cont.intervalIntegrable a b
  have hbound :
      |v b - v a| ≤ ∫ t in a..b, |src t| * E t := by
    rw [← hv_ftc]
    have h1 : |∫ t in a..b, src t * E t|
        ≤ ∫ t in a..b, |src t * E t| :=
      intervalIntegral.abs_integral_le_integral_abs hab
    have h2 : (∫ t in a..b, |src t * E t|)
        ≤ ∫ t in a..b, |src t| * E t := by
      apply intervalIntegral.integral_mono_on hab
      · exact h_integrand_cont.abs.intervalIntegrable a b
      · exact h_weighted_cont.intervalIntegrable a b
      · intro t _ht
        apply le_of_eq
        rw [abs_mul, abs_of_pos (hEpos t)]
    exact le_trans h1 h2
  have hvb : |v b| ≤ |v a| + ∫ t in a..b, |src t| * E t := by
    have h := abs_sub_abs_le_abs_sub (v b) (v a)
    linarith [hbound]
  have hva : |v a| = |e a| := by
    simp [v, hEa]
  have hvb' : |v b| = |e b| * E b := by
    rw [hvdef]
    rw [abs_mul, abs_of_pos (hEpos b)]
  rw [hva, hvb'] at hvb
  have hEbpos := hEpos b
  have hmain :
      |e b| ≤ |e a| / E b +
        (∫ t in a..b, |src t| * E t) / E b := by
    calc
      |e b| ≤
          (|e a| + ∫ t in a..b, |src t| * E t) / E b := by
        exact (le_div_iff₀ hEbpos).mpr hvb
      _ = |e a| / E b +
          (∫ t in a..b, |src t| * E t) / E b := by
        field_simp [ne_of_gt hEbpos]
  have hInv : (1 : ℝ) / E b = Real.exp (-(∫ t in a..b, k t)) := by
    rw [hEb_eq, one_div, Real.exp_neg]
  have hweighted_eq :
      Real.exp (-(∫ s in a..b, k s)) *
          (∫ t in a..b, |src t| * E t) =
        ∫ t in a..b,
          Real.exp (-(∫ s in t..b, k s)) * |src t| := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _ht
    have hsplit :
        (∫ s in a..b, k s) = (∫ s in a..t, k s) + (∫ s in t..b, k s) := by
      exact (intervalIntegral.integral_add_adjacent_intervals
        (hk_cont.intervalIntegrable a t)
        (hk_cont.intervalIntegrable t b)).symm
    set A : ℝ := ∫ s in a..t, k s with hA
    set B : ℝ := ∫ s in t..b, k s with hB
    calc
      Real.exp (-(∫ s in a..b, k s)) * (|src t| * E t)
          = Real.exp (-(A + B)) * (|src t| * Real.exp A) := by
            rw [hsplit, hA]
      _ = Real.exp (-B) * |src t| := by
            rw [show
              Real.exp (-(A + B)) * (|src t| * Real.exp A) =
                (Real.exp (-(A + B)) * Real.exp A) * |src t| by
              ring]
            rw [← Real.exp_add]
            have hlin : -(A + B) + A = -B := by ring
            rw [hlin]
      _ = Real.exp (-(∫ s in t..b, k s)) * |src t| := by
            rw [hB]
  have hmain' :
      |e b| ≤
        Real.exp (-(∫ t in a..b, k t)) * |e a| +
          ∫ t in a..b,
            Real.exp (-(∫ s in t..b, k s)) * |src t| := by
    calc
      |e b| ≤ |e a| / E b +
          (∫ t in a..b, |src t| * E t) / E b := hmain
      _ = Real.exp (-(∫ t in a..b, k t)) * |e a| +
          Real.exp (-(∫ t in a..b, k t)) *
            (∫ t in a..b, |src t| * E t) := by
        rw [← hInv]
        field_simp [ne_of_gt hEbpos]
      _ = Real.exp (-(∫ t in a..b, k t)) * |e a| +
          ∫ t in a..b,
            Real.exp (-(∫ s in t..b, k s)) * |src t| := by
        rw [hweighted_eq]
  have hinit' :
      Real.exp (-(∫ t in a..b, k t)) * |e a| ≤
        Real.exp (-(∫ t in a..b, k t)) * E0 :=
    mul_le_mul_of_nonneg_left hinit (Real.exp_nonneg _)
  linarith [hmain', hinit', hsource]

/-- Coarser endpoint form of the weighted write bound.

It drops the terminal damping kernel but keeps the moving-target error under
the integral, which is often enough for stitching adjacent write subwindows. -/
theorem stack_write_endpoint_le_initial_add_target_integral
    (y m k : ℝ → ℝ) (M a b : ℝ)
    (hab : a ≤ b)
    (hk_cont : Continuous k)
    (hk_nonneg : ∀ t ∈ Set.Icc a b, 0 ≤ k t)
    (hm_cont : Continuous m)
    (hy_ode : ∀ t ∈ Set.Icc a b,
      HasDerivAt y (k t * (m t - y t)) t) :
    |y b - M| ≤ |y a - M| + ∫ t in a..b, k t * |m t - M| := by
  have hbase :=
    stack_write_gronwall_weighted_bound y m k M a b hab hk_cont hk_nonneg
      hm_cont hy_ode
  have hK_nonneg : 0 ≤ ∫ t in a..b, k t := by
    apply intervalIntegral.integral_nonneg hab
    intro t ht
    exact hk_nonneg t ht
  have hinit_kernel :
      Real.exp (-(∫ t in a..b, k t)) * |y a - M| ≤ |y a - M| := by
    have hexp_le : Real.exp (-(∫ t in a..b, k t)) ≤ 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (neg_nonpos.mpr hK_nonneg)
    exact mul_le_of_le_one_left (abs_nonneg _) hexp_le
  have htarget :
      (∫ t in a..b,
        Real.exp (-(∫ s in t..b, k s)) * k t * |m t - M|) ≤
        ∫ t in a..b, k t * |m t - M| := by
    have hm_abs_cont : Continuous fun t => |m t - M| :=
      (hm_cont.sub continuous_const).abs
    have hKderiv : ∀ t : ℝ,
        HasDerivAt (fun u => ∫ s in u..b, k s) (-(k t)) t := by
      intro t
      exact intervalIntegral.integral_hasDerivAt_left
        (hk_cont.intervalIntegrable t b)
        (hk_cont.stronglyMeasurableAtFilter _ _)
        hk_cont.continuousAt
    have hKcont : Continuous fun t : ℝ => ∫ s in t..b, k s := by
      apply continuous_iff_continuousAt.mpr
      intro t
      exact (hKderiv t).continuousAt
    have hkernel_cont : Continuous fun t =>
        Real.exp (-(∫ s in t..b, k s)) := by
      exact Real.continuous_exp.comp (continuous_neg.comp hKcont)
    have hleft_int : IntervalIntegrable
        (fun t => Real.exp (-(∫ s in t..b, k s)) * k t * |m t - M|)
        MeasureTheory.volume a b :=
      ((hkernel_cont.mul hk_cont).mul hm_abs_cont).intervalIntegrable a b
    have hright_int : IntervalIntegrable
        (fun t => k t * |m t - M|) MeasureTheory.volume a b :=
      (hk_cont.mul hm_abs_cont).intervalIntegrable a b
    apply intervalIntegral.integral_mono_on hab hleft_int hright_int
    intro t ht
    have htail_nonneg : 0 ≤ ∫ s in t..b, k s := by
      apply intervalIntegral.integral_nonneg ht.2
      intro s hs
      exact hk_nonneg s ⟨le_trans ht.1 hs.1, hs.2⟩
    have hexp_le : Real.exp (-(∫ s in t..b, k s)) ≤ 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (neg_nonpos.mpr htail_nonneg)
    have hnonneg : 0 ≤ k t * |m t - M| :=
      mul_nonneg (hk_nonneg t ht) (abs_nonneg _)
    calc
      Real.exp (-(∫ s in t..b, k s)) * k t * |m t - M|
          = Real.exp (-(∫ s in t..b, k s)) * (k t * |m t - M|) := by
            ring
      _ ≤ 1 * (k t * |m t - M|) :=
            mul_le_mul_of_nonneg_right hexp_le hnonneg
      _ = k t * |m t - M| := by ring
  linarith

/-- Pointwise weighted write bound on every prefix `[a,t]` of `[a,b]`. -/
theorem stack_write_pointwise_weighted_bound_on_prefix
    (y m k : ℝ → ℝ) (M a b : ℝ)
    (_hab : a ≤ b)
    (hk_cont : Continuous k)
    (hk_nonneg : ∀ t ∈ Set.Icc a b, 0 ≤ k t)
    (hm_cont : Continuous m)
    (hy_ode : ∀ t ∈ Set.Icc a b,
      HasDerivAt y (k t * (m t - y t)) t) :
    ∀ t ∈ Set.Icc a b,
      |y t - M| ≤ Real.exp (-(∫ r in a..t, k r)) * |y a - M| +
        ∫ s in a..t,
          Real.exp (-(∫ r in s..t, k r)) * k s * |m s - M| := by
  intro t ht
  exact stack_write_gronwall_weighted_bound
    y m k M a t ht.1 hk_cont
    (by
      intro r hr
      exact hk_nonneg r ⟨hr.1, le_trans hr.2 ht.2⟩)
    hm_cont
    (by
      intro r hr
      exact hy_ode r ⟨hr.1, le_trans hr.2 ht.2⟩)

/-- Exact mass of the forward Duhamel kernel. -/
theorem forward_kernel_integral_eq_one_sub_exp
    (k : ℝ → ℝ) (s b : ℝ)
    (_hsb : s ≤ b)
    (hk_cont : Continuous k) :
    (∫ t in s..b,
      Real.exp (-(∫ r in s..t, k r)) * k t) =
        1 - Real.exp (-(∫ r in s..b, k r)) := by
  set K : ℝ → ℝ := fun t => ∫ r in s..t, k r with hKdef
  have hKderiv : ∀ t : ℝ, HasDerivAt K (k t) t := by
    intro t
    exact intervalIntegral.integral_hasDerivAt_right
      (hk_cont.intervalIntegrable s t)
      (hk_cont.stronglyMeasurableAtFilter _ _)
      hk_cont.continuousAt
  set F : ℝ → ℝ := fun t => 1 - Real.exp (-(K t)) with hFdef
  have hFderiv : ∀ t : ℝ,
      HasDerivAt F (Real.exp (-(K t)) * k t) t := by
    intro t
    have hneg : HasDerivAt (fun u => -(K u)) (-(k t)) t := by
      simpa using (hKderiv t).neg
    have hexp := hneg.exp
    have hsub := (hasDerivAt_const t (1 : ℝ)).sub hexp
    convert hsub using 1
    ring
  have hderiv_on : ∀ t ∈ Set.uIcc s b,
      HasDerivAt F (Real.exp (-(∫ r in s..t, k r)) * k t) t := by
    intro t _ht
    simpa [F, K] using hFderiv t
  have hcont_der :
      Continuous fun t : ℝ => Real.exp (-(∫ r in s..t, k r)) * k t := by
    have hKcont : Continuous K := by
      apply continuous_iff_continuousAt.mpr
      intro t
      exact (hKderiv t).continuousAt
    simpa [K] using
      (Real.continuous_exp.comp (continuous_neg.comp hKcont)).mul hk_cont
  have hFTC :
      (∫ t in s..b, Real.exp (-(∫ r in s..t, k r)) * k t) =
        F b - F s := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv_on
      (hcont_der.intervalIntegrable s b)
  calc
    (∫ t in s..b, Real.exp (-(∫ r in s..t, k r)) * k t)
        = F b - F s := hFTC
    _ = 1 - Real.exp (-(∫ r in s..b, k r)) := by
      simp [F, K]

/-- Forward kernel mass is at most one. -/
theorem write_forward_kernel_mass_le_one
    (k : ℝ → ℝ) (s b : ℝ)
    (hsb : s ≤ b)
    (hk_cont : Continuous k)
    (_hk_nonneg : ∀ t ∈ Set.Icc s b, 0 ≤ k t) :
    (∫ t in s..b,
      Real.exp (-(∫ r in s..t, k r)) * k t) ≤ 1 := by
  rw [forward_kernel_integral_eq_one_sub_exp k s b hsb hk_cont]
  exact sub_le_self _ (Real.exp_nonneg _)

/-- Integrating the write error against the write rate costs only the initial
error and the rate-weighted moving-target error. -/
theorem stack_write_error_integral_le_initial_add_target
    (y m k : ℝ → ℝ) (M a b : ℝ)
    (hab : a ≤ b)
    (hk_cont : Continuous k)
    (hk_nonneg : ∀ t ∈ Set.Icc a b, 0 ≤ k t)
    (hy_cont : Continuous y)
    (hm_cont : Continuous m)
    (hy_ode : ∀ t ∈ Set.Icc a b,
      HasDerivAt y (k t * (m t - y t)) t) :
    (∫ t in a..b, k t * |y t - M|) ≤
      |y a - M| + (∫ t in a..b, k t * |m t - M|) := by
  set Φ : ℝ → ℝ := fun t => ∫ s in a..t, k s with hΦdef
  have hΦderiv : ∀ t : ℝ, HasDerivAt Φ (k t) t := by
    intro t
    exact intervalIntegral.integral_hasDerivAt_right
      (hk_cont.intervalIntegrable a t)
      (hk_cont.stronglyMeasurableAtFilter _ _)
      hk_cont.continuousAt
  have hΦa : Φ a = 0 := by
    simp [Φ]
  have hΦcont : Continuous Φ := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (hΦderiv t).continuousAt
  set E : ℝ → ℝ := fun t => Real.exp (Φ t) with hEdef
  have hEderiv : ∀ t : ℝ, HasDerivAt E (k t * E t) t := by
    intro t
    have h := (hΦderiv t).exp
    convert h using 1
    simp only [E]
    ring
  have hEcont : Continuous E := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (hEderiv t).continuousAt
  set R : ℝ → ℝ := fun t => Real.exp (-(Φ t)) with hRdef
  have hRderiv : ∀ t : ℝ, HasDerivAt R (-(k t) * R t) t := by
    intro t
    have hneg : HasDerivAt (fun u => -(Φ u)) (-(k t)) t := (hΦderiv t).neg
    have h := hneg.exp
    convert h using 1
    simp only [R]
    ring
  have hRcont : Continuous R := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (hRderiv t).continuousAt
  set H : ℝ → ℝ := fun t =>
    |y a - M| + ∫ s in a..t, k s * |m s - M| * E s with hHdef
  have hmM_abs_cont : Continuous fun t => |m t - M| :=
    (hm_cont.sub continuous_const).abs
  have hsource_cont :
      Continuous fun t : ℝ => k t * |m t - M| * E t :=
    (hk_cont.mul hmM_abs_cont).mul hEcont
  have hHderiv : ∀ t : ℝ,
      HasDerivAt H (k t * |m t - M| * E t) t := by
    intro t
    have hint : HasDerivAt
        (fun u : ℝ => ∫ s in a..u, k s * |m s - M| * E s)
        (k t * |m t - M| * E t) t :=
      intervalIntegral.integral_hasDerivAt_right
        (hsource_cont.intervalIntegrable a t)
        (hsource_cont.stronglyMeasurableAtFilter _ _)
        hsource_cont.continuousAt
    have hconst : HasDerivAt (fun _ : ℝ => |y a - M|) 0 t :=
      hasDerivAt_const t _
    simpa [H] using hint.const_add (|y a - M|)
  have hHcont : Continuous H := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (hHderiv t).continuousAt
  set P : ℝ → ℝ := fun t => R t * H t with hPdef
  have hPcont : Continuous P := by
    simpa [P] using hRcont.mul hHcont
  have hPderiv : ∀ t : ℝ,
      HasDerivAt P (k t * |m t - M| - k t * (R t * H t)) t := by
    intro t
    have hprod := (hRderiv t).mul (hHderiv t)
    have hRE : R t * E t = 1 := by
      simp [R, E, Φ, ← Real.exp_add]
    have hval :
        -(k t * R t * H t) + R t * (k t * |m t - M| * E t) =
          k t * |m t - M| - k t * (R t * H t) := by
      calc
        -(k t * R t * H t) + R t * (k t * |m t - M| * E t)
            = k t * |m t - M| * (R t * E t) -
                k t * (R t * H t) := by ring
        _ = k t * |m t - M| - k t * (R t * H t) := by
            rw [hRE]
            ring
    have hprod_fun : HasDerivAt (fun x => R x * H x)
        (-(k t * R t * H t) + R t * (k t * |m t - M| * E t)) t := by
      simpa [Pi.mul_apply, mul_assoc] using hprod
    have hprod' : HasDerivAt (fun x => R x * H x)
        (k t * |m t - M| - k t * (R t * H t)) t := by
      simpa [hval] using hprod_fun
    simpa [P] using hprod'
  have hpoint : ∀ t ∈ Set.Icc a b, |y t - M| ≤ R t * H t := by
    intro t ht
    have hprefix := stack_write_gronwall_weighted_ifactor_bound
      y m k M a t ht.1 hk_cont
      (by
        intro r hr
        exact hk_nonneg r ⟨hr.1, le_trans hr.2 ht.2⟩)
      hm_cont
      (by
        intro r hr
        exact hy_ode r ⟨hr.1, le_trans hr.2 ht.2⟩)
    calc
      |y t - M| ≤
          Real.exp (-(∫ x in a..t, k x)) * |y a - M| +
            Real.exp (-(∫ x in a..t, k x)) *
              (∫ x in a..t,
                k x * |m x - M| * Real.exp (∫ s in a..x, k s)) := hprefix
      _ = R t * H t := by
            simp [R, H, E, Φ]
            ring
  have hleft_int : IntervalIntegrable (fun t => k t * |y t - M|)
      MeasureTheory.volume a b :=
    (hk_cont.mul ((hy_cont.sub continuous_const).abs)).intervalIntegrable a b
  have hright_int : IntervalIntegrable (fun t => k t * (R t * H t))
      MeasureTheory.volume a b := by
    simpa [P] using (hk_cont.mul hPcont).intervalIntegrable a b
  have hmono :
      (∫ t in a..b, k t * |y t - M|) ≤
        ∫ t in a..b, k t * (R t * H t) := by
    apply intervalIntegral.integral_mono_on hab hleft_int hright_int
    intro t ht
    exact mul_le_mul_of_nonneg_left (hpoint t ht) (hk_nonneg t ht)
  have hq_int : IntervalIntegrable (fun t => k t * |m t - M|)
      MeasureTheory.volume a b :=
    (hk_cont.mul hmM_abs_cont).intervalIntegrable a b
  have hP_integrand_int : IntervalIntegrable
      (fun t => k t * |m t - M| - k t * (R t * H t))
      MeasureTheory.volume a b := by
    exact ((hk_cont.mul hmM_abs_cont).sub
      (hk_cont.mul (hRcont.mul hHcont))).intervalIntegrable a b
  have hFTC :
      (∫ t in a..b, k t * |m t - M| - k t * (R t * H t)) =
        P b - P a := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro t _ht
      exact hPderiv t
    · exact hP_integrand_int
  have hsub :
      (∫ t in a..b, k t * |m t - M|) -
          (∫ t in a..b, k t * (R t * H t)) =
        P b - P a := by
    rw [← intervalIntegral.integral_sub]
    · exact hFTC
    · exact hq_int
    · exact hright_int
  have hPa : P a = |y a - M| := by
    simp [P, R, H, Φ]
  have hPb_nonneg : 0 ≤ P b := by
    exact le_trans (abs_nonneg (y b - M)) (hpoint b ⟨hab, le_rfl⟩)
  have hmajor :
      (∫ t in a..b, k t * (R t * H t)) ≤
        |y a - M| + (∫ t in a..b, k t * |m t - M|) := by
    have hsub' :
        (∫ t in a..b, k t * |m t - M|) -
            (∫ t in a..b, k t * (R t * H t)) =
          P b - |y a - M| := by
      simpa [hPa] using hsub
    linarith
  exact le_trans hmono hmajor

/-- Triangle reduction for the actual write field cap.

The ODE-independent part of the estimate is just
`|m - y| ≤ |m - M| + |y - M|`, multiplied by the nonnegative rate and integrated. -/
theorem stack_write_field_cap_triangle_reduce
    (y m k : ℝ → ℝ) (M a b : ℝ)
    (hab : a ≤ b)
    (hk_cont : Continuous k)
    (hk_nonneg : ∀ t ∈ Set.Icc a b, 0 ≤ k t)
    (hy_cont : Continuous y)
    (hm_cont : Continuous m) :
    (∫ t in a..b, k t * |m t - y t|) ≤
      (∫ t in a..b, k t * |m t - M|) +
        (∫ t in a..b, k t * |y t - M|) := by
  have hmM_cont : Continuous fun t => |m t - M| :=
    (hm_cont.sub continuous_const).abs
  have hyM_cont : Continuous fun t => |y t - M| :=
    (hy_cont.sub continuous_const).abs
  have hmy_cont : Continuous fun t => |m t - y t| :=
    (hm_cont.sub hy_cont).abs
  have hleft_int : IntervalIntegrable (fun t => k t * |m t - y t|)
      MeasureTheory.volume a b :=
    (hk_cont.mul hmy_cont).intervalIntegrable a b
  have hright_int : IntervalIntegrable (fun t => k t * |m t - M| +
      k t * |y t - M|) MeasureTheory.volume a b :=
    ((hk_cont.mul hmM_cont).add (hk_cont.mul hyM_cont)).intervalIntegrable a b
  calc
    (∫ t in a..b, k t * |m t - y t|)
        ≤ ∫ t in a..b, k t * |m t - M| + k t * |y t - M| := by
          apply intervalIntegral.integral_mono_on hab hleft_int hright_int
          intro t ht
          have hk0 : 0 ≤ k t := hk_nonneg t ht
          have htri : |m t - y t| ≤ |m t - M| + |y t - M| := by
            calc
              |m t - y t| = |(m t - M) + (M - y t)| := by
                congr 1
                ring
              _ ≤ |m t - M| + |M - y t| := abs_add_le _ _
              _ = |m t - M| + |y t - M| := by
                rw [abs_sub_comm M (y t)]
          exact calc
            k t * |m t - y t|
                ≤ k t * (|m t - M| + |y t - M|) :=
                  mul_le_mul_of_nonneg_left htri hk0
            _ = k t * |m t - M| + k t * |y t - M| := by ring
    _ = (∫ t in a..b, k t * |m t - M|) +
          (∫ t in a..b, k t * |y t - M|) := by
        rw [intervalIntegral.integral_add]
        · exact (hk_cont.mul hmM_cont).intervalIntegrable a b
        · exact (hk_cont.mul hyM_cont).intervalIntegrable a b

/-- Field-cap bound once the write error integral has been supplied. -/
theorem stack_write_field_cap_bound_of_error_integral
    (y m k : ℝ → ℝ) (M a b : ℝ)
    (hab : a ≤ b)
    (hk_cont : Continuous k)
    (hk_nonneg : ∀ t ∈ Set.Icc a b, 0 ≤ k t)
    (hy_cont : Continuous y)
    (hm_cont : Continuous m)
    (herrorInt :
      (∫ t in a..b, k t * |y t - M|) ≤
        |y a - M| + (∫ t in a..b, k t * |m t - M|)) :
    (∫ t in a..b, k t * |m t - y t|) ≤
      |y a - M| + 2 * (∫ t in a..b, k t * |m t - M|) := by
  have htri := stack_write_field_cap_triangle_reduce
    y m k M a b hab hk_cont hk_nonneg hy_cont hm_cont
  linarith

/-- Moving-target field-cap bound from target variation.

For `y' = k (m - y)` with `k ≥ 0`, the actual tracking field integral is
controlled by the initial tracking error and the total variation of the moving
target.  This avoids replacing the moving target by a fixed baseline. -/
theorem stack_write_field_cap_le_initial_tracking_add_target_deriv
    (y m k m' : ℝ → ℝ) (a b : ℝ)
    (hab : a ≤ b)
    (hk_cont : Continuous k)
    (hk_nonneg : ∀ t ∈ Set.Icc a b, 0 ≤ k t)
    (hy_cont : Continuous y)
    (hm_cont : Continuous m)
    (hm'_cont : Continuous m')
    (hy_ode : ∀ t ∈ Set.Icc a b,
      HasDerivAt y (k t * (m t - y t)) t)
    (hm_deriv : ∀ t ∈ Set.Icc a b, HasDerivAt m (m' t) t) :
    (∫ t in a..b, k t * |m t - y t|) ≤
      |m a - y a| + (∫ t in a..b, |m' t|) := by
  let e : ℝ → ℝ := fun t => y t - m t
  set Φ : ℝ → ℝ := fun t => ∫ s in a..t, k s with hΦdef
  have hΦderiv : ∀ t : ℝ, HasDerivAt Φ (k t) t := by
    intro t
    exact intervalIntegral.integral_hasDerivAt_right
      (hk_cont.intervalIntegrable a t)
      (hk_cont.stronglyMeasurableAtFilter _ _)
      hk_cont.continuousAt
  have hΦa : Φ a = 0 := by
    simp [Φ]
  have hΦcont : Continuous Φ := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (hΦderiv t).continuousAt
  set E : ℝ → ℝ := fun t => Real.exp (Φ t) with hEdef
  have hEderiv : ∀ t : ℝ, HasDerivAt E (k t * E t) t := by
    intro t
    have h := (hΦderiv t).exp
    convert h using 1
    simp only [E]
    ring
  have hEcont : Continuous E := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (hEderiv t).continuousAt
  have hEpos : ∀ t, 0 < E t := fun t => Real.exp_pos _
  have hEa : E a = 1 := by
    simp [E, hΦa]
  set R : ℝ → ℝ := fun t => Real.exp (-(Φ t)) with hRdef
  have hRderiv : ∀ t : ℝ, HasDerivAt R (-(k t) * R t) t := by
    intro t
    have hneg : HasDerivAt (fun u => -(Φ u)) (-(k t)) t := (hΦderiv t).neg
    have h := hneg.exp
    convert h using 1
    simp only [R]
    ring
  have hRcont : Continuous R := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (hRderiv t).continuousAt
  have hRE : ∀ t, R t * E t = 1 := by
    intro t
    simp [R, E, Φ, ← Real.exp_add]
  have hRa : R a = 1 := by
    simp [R, hΦa]

  set H : ℝ → ℝ := fun t =>
    |e a| + ∫ s in a..t, |m' s| * E s with hHdef
  have hm'_abs_cont : Continuous fun t => |m' t| := hm'_cont.abs
  have hsource_cont : Continuous fun t : ℝ => |m' t| * E t :=
    hm'_abs_cont.mul hEcont
  have hHderiv : ∀ t : ℝ, HasDerivAt H (|m' t| * E t) t := by
    intro t
    have hint : HasDerivAt
        (fun u : ℝ => ∫ s in a..u, |m' s| * E s)
        (|m' t| * E t) t :=
      intervalIntegral.integral_hasDerivAt_right
        (hsource_cont.intervalIntegrable a t)
        (hsource_cont.stronglyMeasurableAtFilter _ _)
        hsource_cont.continuousAt
    simpa [H] using hint.const_add (|e a|)
  have hHcont : Continuous H := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (hHderiv t).continuousAt
  set P : ℝ → ℝ := fun t => R t * H t with hPdef
  have hPcont : Continuous P := by
    simpa [P] using hRcont.mul hHcont

  have hpoint : ∀ t ∈ Set.Icc a b, |e t| ≤ P t := by
    intro t ht
    set v : ℝ → ℝ := fun u => e u * E u with hvdef
    have hvderiv : ∀ u ∈ Set.Icc a t,
        HasDerivAt v (-(m' u) * E u) u := by
      intro u hu
      have huab : u ∈ Set.Icc a b := ⟨hu.1, le_trans hu.2 ht.2⟩
      have he_deriv : HasDerivAt e (k u * (m u - y u) - m' u) u := by
        simpa [e] using (hy_ode u huab).sub (hm_deriv u huab)
      have hprod := he_deriv.mul (hEderiv u)
      convert hprod using 1
      simp only [e, E]
      ring
    have hv_cont : Continuous v := by
      have he_cont : Continuous e := hy_cont.sub hm_cont
      simpa [v] using he_cont.mul hEcont
    have hder_cont : Continuous fun u : ℝ => -(m' u) * E u :=
      (continuous_neg.comp hm'_cont).mul hEcont
    have hv_ftc :
        (∫ u in a..t, -(m' u) * E u) = v t - v a := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      · intro u hu
        rw [Set.uIcc_of_le ht.1] at hu
        exact hvderiv u hu
      · exact hder_cont.intervalIntegrable a t
    have hbound :
        |v t - v a| ≤ ∫ u in a..t, |m' u| * E u := by
      rw [← hv_ftc]
      have h1 : |∫ u in a..t, -(m' u) * E u|
          ≤ ∫ u in a..t, |-(m' u) * E u| :=
        intervalIntegral.abs_integral_le_integral_abs ht.1
      have h2 : (∫ u in a..t, |-(m' u) * E u|)
          ≤ ∫ u in a..t, |m' u| * E u := by
        apply intervalIntegral.integral_mono_on ht.1
        · exact hder_cont.abs.intervalIntegrable a t
        · exact hsource_cont.intervalIntegrable a t
        · intro u _hu
          apply le_of_eq
          rw [abs_mul, abs_neg, abs_of_pos (hEpos u)]
      exact le_trans h1 h2
    have hv_abs : |v t| ≤ |v a| + ∫ u in a..t, |m' u| * E u := by
      have h := abs_sub_abs_le_abs_sub (v t) (v a)
      linarith [hbound]
    have hva : |v a| = |e a| := by
      simp [v, hEa]
    have hvt : |v t| = |e t| * E t := by
      rw [hvdef]
      rw [abs_mul, abs_of_pos (hEpos t)]
    rw [hva, hvt] at hv_abs
    have hEt := hEpos t
    have hmain : |e t| ≤ (|e a| + ∫ u in a..t, |m' u| * E u) / E t :=
      (le_div_iff₀ hEt).mpr hv_abs
    calc
      |e t| ≤ (|e a| + ∫ u in a..t, |m' u| * E u) / E t := hmain
      _ = R t * H t := by
        field_simp [ne_of_gt hEt]
        have hER : E t * R t = 1 := by
          rw [mul_comm, hRE t]
        rw [hER]
        simp [H]
      _ = P t := by simp [P]

  have hPderiv : ∀ t : ℝ,
      HasDerivAt P (|m' t| - k t * (R t * H t)) t := by
    intro t
    have hprod := (hRderiv t).mul (hHderiv t)
    have hval :
        -(k t * R t * H t) + R t * (|m' t| * E t) =
          |m' t| - k t * (R t * H t) := by
      calc
        -(k t * R t * H t) + R t * (|m' t| * E t)
            = |m' t| * (R t * E t) - k t * (R t * H t) := by ring
        _ = |m' t| - k t * (R t * H t) := by
          rw [hRE t]
          ring
    have hprod_fun : HasDerivAt (fun x => R x * H x)
        (-(k t * R t * H t) + R t * (|m' t| * E t)) t := by
      simpa [Pi.mul_apply, mul_assoc] using hprod
    have hprod' : HasDerivAt (fun x => R x * H x)
        (|m' t| - k t * (R t * H t)) t := by
      simpa [hval] using hprod_fun
    simpa [P] using hprod'

  have hleft_int : IntervalIntegrable (fun t => k t * |e t|)
      MeasureTheory.volume a b := by
    exact (hk_cont.mul ((hy_cont.sub hm_cont).abs)).intervalIntegrable a b
  have hright_int : IntervalIntegrable (fun t => k t * P t)
      MeasureTheory.volume a b := by
    exact (hk_cont.mul hPcont).intervalIntegrable a b
  have hmono :
      (∫ t in a..b, k t * |e t|) ≤ ∫ t in a..b, k t * P t := by
    apply intervalIntegral.integral_mono_on hab hleft_int hright_int
    intro t ht
    exact mul_le_mul_of_nonneg_left (hpoint t ht) (hk_nonneg t ht)

  have htarget_int : IntervalIntegrable (fun t => |m' t|)
      MeasureTheory.volume a b :=
    hm'_abs_cont.intervalIntegrable a b
  have hP_integrand_int : IntervalIntegrable
      (fun t => |m' t| - k t * (R t * H t))
      MeasureTheory.volume a b := by
    exact (hm'_abs_cont.sub (hk_cont.mul (hRcont.mul hHcont))).intervalIntegrable a b
  have hFTC :
      (∫ t in a..b, |m' t| - k t * (R t * H t)) = P b - P a := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro t _ht
      exact hPderiv t
    · exact hP_integrand_int
  have hsub :
      (∫ t in a..b, |m' t|) - (∫ t in a..b, k t * (R t * H t)) =
        P b - P a := by
    rw [← intervalIntegral.integral_sub]
    · simpa [P] using hFTC
    · exact htarget_int
    · exact (hk_cont.mul (hRcont.mul hHcont)).intervalIntegrable a b
  have hPa : P a = |e a| := by
    simp [P, R, H, hΦa]
  have hHb_nonneg : 0 ≤ H b := by
    have hsrc_nonneg : ∀ t ∈ Set.Icc a b, 0 ≤ |m' t| * E t := by
      intro t _ht
      exact mul_nonneg (abs_nonneg _) (hEpos t).le
    have hint_nonneg : 0 ≤ ∫ t in a..b, |m' t| * E t :=
      intervalIntegral.integral_nonneg hab hsrc_nonneg
    dsimp [H]
    exact add_nonneg (abs_nonneg _) hint_nonneg
  have hPb_nonneg : 0 ≤ P b := by
    dsimp [P]
    exact mul_nonneg (Real.exp_nonneg _) hHb_nonneg
  have hmajor :
      (∫ t in a..b, k t * P t) ≤ |e a| + (∫ t in a..b, |m' t|) := by
    have hsub' :
        (∫ t in a..b, |m' t|) - (∫ t in a..b, k t * P t) =
          P b - |e a| := by
      simpa [P, hPa] using hsub
    linarith
  calc
    (∫ t in a..b, k t * |m t - y t|)
        = ∫ t in a..b, k t * |e t| := by
          apply intervalIntegral.integral_congr
          intro t _ht
          simp [e, abs_sub_comm]
    _ ≤ ∫ t in a..b, k t * P t := hmono
    _ ≤ |e a| + (∫ t in a..b, |m' t|) := hmajor
    _ = |m a - y a| + (∫ t in a..b, |m' t|) := by
      simp [e, abs_sub_comm]

/-- Forced moving-target field-cap bound.

For `y' = k (m - y) + f`, the same tracking estimate pays the moving target
variation and the additive forcing in total variation. -/
theorem stack_write_field_cap_le_initial_tracking_add_target_deriv_add_forcing
    (y m k f m' : ℝ → ℝ) (a b : ℝ)
    (hab : a ≤ b)
    (hk_cont : Continuous k)
    (hk_nonneg : ∀ t ∈ Set.Icc a b, 0 ≤ k t)
    (hy_cont : Continuous y)
    (hm_cont : Continuous m)
    (hf_cont : Continuous f)
    (hm'_cont : Continuous m')
    (hy_ode : ∀ t ∈ Set.Icc a b,
      HasDerivAt y (k t * (m t - y t) + f t) t)
    (hm_deriv : ∀ t ∈ Set.Icc a b, HasDerivAt m (m' t) t) :
    (∫ t in a..b, k t * |m t - y t|) ≤
      |m a - y a| + (∫ t in a..b, |m' t|) +
        (∫ t in a..b, |f t|) := by
  let e : ℝ → ℝ := fun t => y t - m t
  set Φ : ℝ → ℝ := fun t => ∫ s in a..t, k s with hΦdef
  have hΦderiv : ∀ t : ℝ, HasDerivAt Φ (k t) t := by
    intro t
    exact intervalIntegral.integral_hasDerivAt_right
      (hk_cont.intervalIntegrable a t)
      (hk_cont.stronglyMeasurableAtFilter _ _)
      hk_cont.continuousAt
  have hΦa : Φ a = 0 := by
    simp [Φ]
  have hΦcont : Continuous Φ := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (hΦderiv t).continuousAt
  set E : ℝ → ℝ := fun t => Real.exp (Φ t) with hEdef
  have hEderiv : ∀ t : ℝ, HasDerivAt E (k t * E t) t := by
    intro t
    have h := (hΦderiv t).exp
    convert h using 1
    simp only [E]
    ring
  have hEcont : Continuous E := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (hEderiv t).continuousAt
  have hEpos : ∀ t, 0 < E t := fun t => Real.exp_pos _
  have hEa : E a = 1 := by
    simp [E, hΦa]
  set R : ℝ → ℝ := fun t => Real.exp (-(Φ t)) with hRdef
  have hRderiv : ∀ t : ℝ, HasDerivAt R (-(k t) * R t) t := by
    intro t
    have hneg : HasDerivAt (fun u => -(Φ u)) (-(k t)) t := (hΦderiv t).neg
    have h := hneg.exp
    convert h using 1
    simp only [R]
    ring
  have hRcont : Continuous R := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (hRderiv t).continuousAt
  have hRE : ∀ t, R t * E t = 1 := by
    intro t
    simp [R, E, Φ, ← Real.exp_add]
  set H : ℝ → ℝ := fun t =>
    |e a| + ∫ s in a..t, (|m' s| + |f s|) * E s with hHdef
  have hm'_abs_cont : Continuous fun t => |m' t| := hm'_cont.abs
  have hf_abs_cont : Continuous fun t => |f t| := hf_cont.abs
  have hsource_cont : Continuous fun t : ℝ => (|m' t| + |f t|) * E t :=
    (hm'_abs_cont.add hf_abs_cont).mul hEcont
  have hHderiv : ∀ t : ℝ, HasDerivAt H ((|m' t| + |f t|) * E t) t := by
    intro t
    have hint : HasDerivAt
        (fun u : ℝ => ∫ s in a..u, (|m' s| + |f s|) * E s)
        ((|m' t| + |f t|) * E t) t :=
      intervalIntegral.integral_hasDerivAt_right
        (hsource_cont.intervalIntegrable a t)
        (hsource_cont.stronglyMeasurableAtFilter _ _)
        hsource_cont.continuousAt
    simpa [H] using hint.const_add (|e a|)
  have hHcont : Continuous H := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (hHderiv t).continuousAt
  set P : ℝ → ℝ := fun t => R t * H t with hPdef
  have hPcont : Continuous P := by
    simpa [P] using hRcont.mul hHcont
  have hpoint : ∀ t ∈ Set.Icc a b, |e t| ≤ P t := by
    intro t ht
    set v : ℝ → ℝ := fun u => e u * E u with hvdef
    have hvderiv : ∀ u ∈ Set.Icc a t,
        HasDerivAt v ((f u - m' u) * E u) u := by
      intro u hu
      have huab : u ∈ Set.Icc a b := ⟨hu.1, le_trans hu.2 ht.2⟩
      have he_deriv : HasDerivAt e (k u * (m u - y u) + f u - m' u) u := by
        simpa [e] using (hy_ode u huab).sub (hm_deriv u huab)
      have hprod := he_deriv.mul (hEderiv u)
      convert hprod using 1
      simp only [e, E]
      ring
    have hder_cont : Continuous fun u : ℝ => (f u - m' u) * E u :=
      (hf_cont.sub hm'_cont).mul hEcont
    have hv_ftc :
        (∫ u in a..t, (f u - m' u) * E u) = v t - v a := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      · intro u hu
        rw [Set.uIcc_of_le ht.1] at hu
        exact hvderiv u hu
      · exact hder_cont.intervalIntegrable a t
    have hbound :
        |v t - v a| ≤ ∫ u in a..t, (|m' u| + |f u|) * E u := by
      rw [← hv_ftc]
      have h1 : |∫ u in a..t, (f u - m' u) * E u|
          ≤ ∫ u in a..t, |(f u - m' u) * E u| :=
        intervalIntegral.abs_integral_le_integral_abs ht.1
      have h2 : (∫ u in a..t, |(f u - m' u) * E u|)
          ≤ ∫ u in a..t, (|m' u| + |f u|) * E u := by
        apply intervalIntegral.integral_mono_on ht.1
        · exact hder_cont.abs.intervalIntegrable a t
        · exact hsource_cont.intervalIntegrable a t
        · intro u _hu
          have htri : |f u - m' u| ≤ |m' u| + |f u| := by
            rw [abs_sub_comm]
            calc
              |m' u - f u| = |m' u + -(f u)| := by
                ring
              _ ≤ |m' u| + |-(f u)| := abs_add_le _ _
              _ = |m' u| + |f u| := by rw [abs_neg]
          calc
            |(f u - m' u) * E u| = |f u - m' u| * E u := by
              rw [abs_mul, abs_of_pos (hEpos u)]
            _ ≤ (|m' u| + |f u|) * E u :=
              mul_le_mul_of_nonneg_right htri (hEpos u).le
      exact le_trans h1 h2
    have hv_abs : |v t| ≤ |v a| + ∫ u in a..t, (|m' u| + |f u|) * E u := by
      have h := abs_sub_abs_le_abs_sub (v t) (v a)
      linarith [hbound]
    have hva : |v a| = |e a| := by
      simp [v, hEa]
    have hvt : |v t| = |e t| * E t := by
      rw [hvdef]
      rw [abs_mul, abs_of_pos (hEpos t)]
    rw [hva, hvt] at hv_abs
    have hEt := hEpos t
    have hmain :
        |e t| ≤ (|e a| + ∫ u in a..t, (|m' u| + |f u|) * E u) / E t :=
      (le_div_iff₀ hEt).mpr hv_abs
    calc
      |e t| ≤
          (|e a| + ∫ u in a..t, (|m' u| + |f u|) * E u) / E t := hmain
      _ = R t * H t := by
        field_simp [ne_of_gt hEt]
        have hER : E t * R t = 1 := by
          rw [mul_comm, hRE t]
        rw [hER]
        simp [H]
      _ = P t := by simp [P]
  have hPderiv : ∀ t : ℝ,
      HasDerivAt P ((|m' t| + |f t|) - k t * (R t * H t)) t := by
    intro t
    have hprod := (hRderiv t).mul (hHderiv t)
    have hval :
        -(k t * R t * H t) + R t * ((|m' t| + |f t|) * E t) =
          (|m' t| + |f t|) - k t * (R t * H t) := by
      calc
        -(k t * R t * H t) + R t * ((|m' t| + |f t|) * E t)
            = (|m' t| + |f t|) * (R t * E t) -
                k t * (R t * H t) := by ring
        _ = (|m' t| + |f t|) - k t * (R t * H t) := by
          rw [hRE t]
          ring
    have hprod_fun : HasDerivAt (fun x => R x * H x)
        (-(k t * R t * H t) + R t * ((|m' t| + |f t|) * E t)) t := by
      simpa [Pi.mul_apply, mul_assoc] using hprod
    have hprod' : HasDerivAt (fun x => R x * H x)
        ((|m' t| + |f t|) - k t * (R t * H t)) t := by
      simpa [hval] using hprod_fun
    simpa [P] using hprod'
  have hleft_int : IntervalIntegrable (fun t => k t * |e t|)
      MeasureTheory.volume a b := by
    exact (hk_cont.mul ((hy_cont.sub hm_cont).abs)).intervalIntegrable a b
  have hright_int : IntervalIntegrable (fun t => k t * P t)
      MeasureTheory.volume a b := by
    exact (hk_cont.mul hPcont).intervalIntegrable a b
  have hmono :
      (∫ t in a..b, k t * |e t|) ≤ ∫ t in a..b, k t * P t := by
    apply intervalIntegral.integral_mono_on hab hleft_int hright_int
    intro t ht
    exact mul_le_mul_of_nonneg_left (hpoint t ht) (hk_nonneg t ht)
  have htarget_int : IntervalIntegrable (fun t => |m' t| + |f t|)
      MeasureTheory.volume a b :=
    (hm'_abs_cont.add hf_abs_cont).intervalIntegrable a b
  have hP_integrand_int : IntervalIntegrable
      (fun t => (|m' t| + |f t|) - k t * (R t * H t))
      MeasureTheory.volume a b := by
    exact ((hm'_abs_cont.add hf_abs_cont).sub
      (hk_cont.mul (hRcont.mul hHcont))).intervalIntegrable a b
  have hFTC :
      (∫ t in a..b, (|m' t| + |f t|) - k t * (R t * H t)) =
        P b - P a := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro t _ht
      exact hPderiv t
    · exact hP_integrand_int
  have hsub :
      (∫ t in a..b, |m' t| + |f t|) -
          (∫ t in a..b, k t * (R t * H t)) =
        P b - P a := by
    rw [← intervalIntegral.integral_sub]
    · simpa [P] using hFTC
    · exact htarget_int
    · exact (hk_cont.mul (hRcont.mul hHcont)).intervalIntegrable a b
  have hPa : P a = |e a| := by
    simp [P, R, H, hΦa]
  have hHb_nonneg : 0 ≤ H b := by
    have hsrc_nonneg : ∀ t ∈ Set.Icc a b, 0 ≤ (|m' t| + |f t|) * E t := by
      intro t _ht
      exact mul_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) (hEpos t).le
    have hint_nonneg : 0 ≤ ∫ t in a..b, (|m' t| + |f t|) * E t :=
      intervalIntegral.integral_nonneg hab hsrc_nonneg
    dsimp [H]
    exact add_nonneg (abs_nonneg _) hint_nonneg
  have hPb_nonneg : 0 ≤ P b := by
    dsimp [P]
    exact mul_nonneg (Real.exp_nonneg _) hHb_nonneg
  have hmajor :
      (∫ t in a..b, k t * P t) ≤
        |e a| + (∫ t in a..b, |m' t| + |f t|) := by
    have hsub' :
        (∫ t in a..b, |m' t| + |f t|) - (∫ t in a..b, k t * P t) =
          P b - |e a| := by
      simpa [P, hPa] using hsub
    linarith
  have hsplit :
      (∫ t in a..b, |m' t| + |f t|) =
        (∫ t in a..b, |m' t|) + (∫ t in a..b, |f t|) := by
    rw [intervalIntegral.integral_add]
    · exact hm'_abs_cont.intervalIntegrable a b
    · exact hf_abs_cont.intervalIntegrable a b
  calc
    (∫ t in a..b, k t * |m t - y t|)
        = ∫ t in a..b, k t * |e t| := by
          apply intervalIntegral.integral_congr
          intro t _ht
          simp [e, abs_sub_comm]
    _ ≤ ∫ t in a..b, k t * P t := hmono
    _ ≤ |e a| + (∫ t in a..b, |m' t| + |f t|) := hmajor
    _ = |m a - y a| + (∫ t in a..b, |m' t|) +
        (∫ t in a..b, |f t|) := by
      rw [hsplit]
      simp [e, abs_sub_comm]
      ring_nf

/-- Forced moving-target field-cap bound with only closed-interval continuity
and open-interval derivative hypotheses.  This is the active-window interface:
the QSS target need only be continuous on the write suffix, and its derivative
is used only in the open interval. -/
theorem stack_write_field_cap_le_initial_tracking_add_target_deriv_add_forcing_on
    (y m k f m' : ℝ → ℝ) (a b : ℝ)
    (hab : a ≤ b)
    (hk_cont : ContinuousOn k (Set.Icc a b))
    (hk_nonneg : ∀ t ∈ Set.Icc a b, 0 ≤ k t)
    (hy_cont : ContinuousOn y (Set.Icc a b))
    (hm_cont : ContinuousOn m (Set.Icc a b))
    (hf_cont : ContinuousOn f (Set.Icc a b))
    (hm'_cont : ContinuousOn m' (Set.Icc a b))
    (hy_ode : ∀ t ∈ Set.Ioo a b,
      HasDerivAt y (k t * (m t - y t) + f t) t)
    (hm_deriv : ∀ t ∈ Set.Ioo a b, HasDerivAt m (m' t) t) :
    (∫ t in a..b, k t * |m t - y t|) ≤
      |m a - y a| + (∫ t in a..b, |m' t|) +
        (∫ t in a..b, |f t|) := by
  let e : ℝ → ℝ := fun t => y t - m t
  set Φ : ℝ → ℝ := fun t => ∫ s in a..t, k s with hΦdef
  have hk_int_ab : IntervalIntegrable k MeasureTheory.volume a b :=
    hk_cont.intervalIntegrable_of_Icc hab
  have hΦderiv : ∀ t ∈ Set.Ioo a b, HasDerivAt Φ (k t) t := by
    intro t ht
    simpa [Φ] using
      integral_primitive_hasDerivAt_right_of_continuousOn_Icc
        (g := k) hk_cont ht
  have hΦa : Φ a = 0 := by
    simp [Φ]
  have hΦcont : ContinuousOn Φ (Set.Icc a b) := by
    have hprim :=
      continuousOn_primitive_interval' (μ := MeasureTheory.volume)
        (a := a) (b₁ := a) (b₂ := b) hk_int_ab Set.left_mem_uIcc
    rw [← Set.uIcc_of_le hab]
    simpa [Φ] using hprim
  set E : ℝ → ℝ := fun t => Real.exp (Φ t) with hEdef
  have hEderiv : ∀ t ∈ Set.Ioo a b, HasDerivAt E (k t * E t) t := by
    intro t ht
    have h := (hΦderiv t ht).exp
    convert h using 1
    simp only [E]
    ring
  have hEcont : ContinuousOn E (Set.Icc a b) := by
    simpa [E] using Real.continuous_exp.comp_continuousOn hΦcont
  have hEpos : ∀ t, 0 < E t := fun t => Real.exp_pos _
  have hEa : E a = 1 := by
    simp [E, hΦa]
  set R : ℝ → ℝ := fun t => Real.exp (-(Φ t)) with hRdef
  have hRderiv : ∀ t ∈ Set.Ioo a b, HasDerivAt R (-(k t) * R t) t := by
    intro t ht
    have hneg : HasDerivAt (fun u => -(Φ u)) (-(k t)) t := (hΦderiv t ht).neg
    have h := hneg.exp
    convert h using 1
    simp only [R]
    ring
  have hRcont : ContinuousOn R (Set.Icc a b) := by
    simpa [R] using Real.continuous_exp.comp_continuousOn hΦcont.neg
  have hRE : ∀ t, R t * E t = 1 := by
    intro t
    simp [R, E, Φ, ← Real.exp_add]
  set H : ℝ → ℝ := fun t =>
    |e a| + ∫ s in a..t, (|m' s| + |f s|) * E s with hHdef
  have hm'_abs_cont : ContinuousOn (fun t => |m' t|) (Set.Icc a b) := hm'_cont.abs
  have hf_abs_cont : ContinuousOn (fun t => |f t|) (Set.Icc a b) := hf_cont.abs
  have hsource_cont : ContinuousOn (fun t : ℝ => (|m' t| + |f t|) * E t)
      (Set.Icc a b) :=
    (hm'_abs_cont.add hf_abs_cont).mul hEcont
  have hsource_int_ab : IntervalIntegrable
      (fun t : ℝ => (|m' t| + |f t|) * E t) MeasureTheory.volume a b :=
    hsource_cont.intervalIntegrable_of_Icc hab
  have hHderiv : ∀ t ∈ Set.Ioo a b,
      HasDerivAt H ((|m' t| + |f t|) * E t) t := by
    intro t ht
    have hint : HasDerivAt
        (fun u : ℝ => ∫ s in a..u, (|m' s| + |f s|) * E s)
        ((|m' t| + |f t|) * E t) t :=
      integral_primitive_hasDerivAt_right_of_continuousOn_Icc
        (g := fun s : ℝ => (|m' s| + |f s|) * E s) hsource_cont ht
    simpa [H] using hint.const_add (|e a|)
  have hHcont : ContinuousOn H (Set.Icc a b) := by
    have hprim :=
      continuousOn_primitive_interval' (μ := MeasureTheory.volume)
        (a := a) (b₁ := a) (b₂ := b) hsource_int_ab Set.left_mem_uIcc
    rw [← Set.uIcc_of_le hab]
    simpa [H] using continuousOn_const.add hprim
  set P : ℝ → ℝ := fun t => R t * H t with hPdef
  have hPcont : ContinuousOn P (Set.Icc a b) := by
    simpa [P] using hRcont.mul hHcont
  have hv_cont_ab : ContinuousOn (fun t : ℝ => e t * E t) (Set.Icc a b) := by
    simpa [e] using (hy_cont.sub hm_cont).mul hEcont
  have hpoint : ∀ t ∈ Set.Icc a b, |e t| ≤ P t := by
    intro t ht
    rcases lt_or_eq_of_le ht.1 with hlt | hta
    · set v : ℝ → ℝ := fun u => e u * E u with hvdef
      have hvderiv : ∀ u ∈ Set.Ioo a t,
          HasDerivAt v ((f u - m' u) * E u) u := by
        intro u hu
        have huab : u ∈ Set.Ioo a b := ⟨hu.1, lt_of_lt_of_le hu.2 ht.2⟩
        have he_deriv : HasDerivAt e (k u * (m u - y u) + f u - m' u) u := by
          simpa [e] using (hy_ode u huab).sub (hm_deriv u huab)
        have hprod := he_deriv.mul (hEderiv u huab)
        convert hprod using 1
        simp only [e, E]
        ring
      have hder_cont : ContinuousOn (fun u : ℝ => (f u - m' u) * E u)
          (Set.Icc a t) := by
        exact ((hf_cont.sub hm'_cont).mul hEcont).mono (Set.Icc_subset_Icc_right ht.2)
      have hv_cont_at : ContinuousOn v (Set.Icc a t) := by
        simpa [v] using hv_cont_ab.mono (Set.Icc_subset_Icc_right ht.2)
      have hv_ftc :
          (∫ u in a..t, (f u - m' u) * E u) = v t - v a := by
        exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hlt.le
          hv_cont_at hvderiv (hder_cont.intervalIntegrable_of_Icc hlt.le)
      have hbound :
          |v t - v a| ≤ ∫ u in a..t, (|m' u| + |f u|) * E u := by
        rw [← hv_ftc]
        have h1 : |∫ u in a..t, (f u - m' u) * E u|
            ≤ ∫ u in a..t, |(f u - m' u) * E u| :=
          intervalIntegral.abs_integral_le_integral_abs hlt.le
        have h2 : (∫ u in a..t, |(f u - m' u) * E u|)
            ≤ ∫ u in a..t, (|m' u| + |f u|) * E u := by
          apply intervalIntegral.integral_mono_on hlt.le
          · exact hder_cont.abs.intervalIntegrable_of_Icc hlt.le
          · exact (hsource_cont.mono (Set.Icc_subset_Icc_right ht.2)).intervalIntegrable_of_Icc hlt.le
          · intro u _hu
            have htri : |f u - m' u| ≤ |m' u| + |f u| := by
              rw [abs_sub_comm]
              calc
                |m' u - f u| = |m' u + -(f u)| := by
                  ring
                _ ≤ |m' u| + |-(f u)| := abs_add_le _ _
                _ = |m' u| + |f u| := by rw [abs_neg]
            calc
              |(f u - m' u) * E u| = |f u - m' u| * E u := by
                rw [abs_mul, abs_of_pos (hEpos u)]
              _ ≤ (|m' u| + |f u|) * E u :=
                mul_le_mul_of_nonneg_right htri (hEpos u).le
        exact le_trans h1 h2
      have hv_abs : |v t| ≤ |v a| + ∫ u in a..t, (|m' u| + |f u|) * E u := by
        have h := abs_sub_abs_le_abs_sub (v t) (v a)
        linarith [hbound]
      have hva : |v a| = |e a| := by
        simp [v, hEa]
      have hvt : |v t| = |e t| * E t := by
        rw [hvdef]
        rw [abs_mul, abs_of_pos (hEpos t)]
      rw [hva, hvt] at hv_abs
      have hEt := hEpos t
      have hmain :
          |e t| ≤ (|e a| + ∫ u in a..t, (|m' u| + |f u|) * E u) / E t :=
        (le_div_iff₀ hEt).mpr hv_abs
      calc
        |e t| ≤
            (|e a| + ∫ u in a..t, (|m' u| + |f u|) * E u) / E t := hmain
        _ = R t * H t := by
          field_simp [ne_of_gt hEt]
          have hER : E t * R t = 1 := by
            rw [mul_comm, hRE t]
          rw [hER]
          simp [H]
        _ = P t := by simp [P]
    · subst t
      have hPa0 : P a = |e a| := by
        simp [P, R, H, hΦa]
      simpa [hPa0]
  have hPderiv : ∀ t ∈ Set.Ioo a b,
      HasDerivAt P ((|m' t| + |f t|) - k t * (R t * H t)) t := by
    intro t ht
    have hprod := (hRderiv t ht).mul (hHderiv t ht)
    have hval :
        -(k t * R t * H t) + R t * ((|m' t| + |f t|) * E t) =
          (|m' t| + |f t|) - k t * (R t * H t) := by
      calc
        -(k t * R t * H t) + R t * ((|m' t| + |f t|) * E t)
            = (|m' t| + |f t|) * (R t * E t) -
                k t * (R t * H t) := by ring
        _ = (|m' t| + |f t|) - k t * (R t * H t) := by
          rw [hRE t]
          ring
    have hprod_fun : HasDerivAt (fun x => R x * H x)
        (-(k t * R t * H t) + R t * ((|m' t| + |f t|) * E t)) t := by
      simpa [Pi.mul_apply, mul_assoc] using hprod
    have hprod' : HasDerivAt (fun x => R x * H x)
        ((|m' t| + |f t|) - k t * (R t * H t)) t := by
      simpa [hval] using hprod_fun
    simpa [P] using hprod'
  have hleft_int : IntervalIntegrable (fun t => k t * |e t|)
      MeasureTheory.volume a b := by
    exact (hk_cont.mul ((hy_cont.sub hm_cont).abs)).intervalIntegrable_of_Icc hab
  have hright_int : IntervalIntegrable (fun t => k t * P t)
      MeasureTheory.volume a b := by
    exact (hk_cont.mul hPcont).intervalIntegrable_of_Icc hab
  have hmono :
      (∫ t in a..b, k t * |e t|) ≤ ∫ t in a..b, k t * P t := by
    apply intervalIntegral.integral_mono_on hab hleft_int hright_int
    intro t ht
    exact mul_le_mul_of_nonneg_left (hpoint t ht) (hk_nonneg t ht)
  have htarget_int : IntervalIntegrable (fun t => |m' t| + |f t|)
      MeasureTheory.volume a b :=
    (hm'_abs_cont.add hf_abs_cont).intervalIntegrable_of_Icc hab
  have hP_integrand_int : IntervalIntegrable
      (fun t => (|m' t| + |f t|) - k t * (R t * H t))
      MeasureTheory.volume a b := by
    exact ((hm'_abs_cont.add hf_abs_cont).sub
      (hk_cont.mul (hRcont.mul hHcont))).intervalIntegrable_of_Icc hab
  have hFTC :
      (∫ t in a..b, (|m' t| + |f t|) - k t * (R t * H t)) =
        P b - P a := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
      hPcont hPderiv hP_integrand_int
  have hsub :
      (∫ t in a..b, |m' t| + |f t|) -
          (∫ t in a..b, k t * (R t * H t)) =
        P b - P a := by
    rw [← intervalIntegral.integral_sub]
    · simpa [P] using hFTC
    · exact htarget_int
    · exact (hk_cont.mul (hRcont.mul hHcont)).intervalIntegrable_of_Icc hab
  have hPa : P a = |e a| := by
    simp [P, R, H, hΦa]
  have hHb_nonneg : 0 ≤ H b := by
    have hsrc_nonneg : ∀ t ∈ Set.Icc a b, 0 ≤ (|m' t| + |f t|) * E t := by
      intro t _ht
      exact mul_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) (hEpos t).le
    have hint_nonneg : 0 ≤ ∫ t in a..b, (|m' t| + |f t|) * E t :=
      intervalIntegral.integral_nonneg hab hsrc_nonneg
    dsimp [H]
    exact add_nonneg (abs_nonneg _) hint_nonneg
  have hPb_nonneg : 0 ≤ P b := by
    dsimp [P]
    exact mul_nonneg (Real.exp_nonneg _) hHb_nonneg
  have hmajor :
      (∫ t in a..b, k t * P t) ≤
        |e a| + (∫ t in a..b, |m' t| + |f t|) := by
    have hsub' :
        (∫ t in a..b, |m' t| + |f t|) - (∫ t in a..b, k t * P t) =
          P b - |e a| := by
      simpa [P, hPa] using hsub
    linarith
  have hsplit :
      (∫ t in a..b, |m' t| + |f t|) =
        (∫ t in a..b, |m' t|) + (∫ t in a..b, |f t|) := by
    rw [intervalIntegral.integral_add]
    · exact hm'_abs_cont.intervalIntegrable_of_Icc hab
    · exact hf_abs_cont.intervalIntegrable_of_Icc hab
  calc
    (∫ t in a..b, k t * |m t - y t|)
        = ∫ t in a..b, k t * |e t| := by
          apply intervalIntegral.integral_congr
          intro t _ht
          simp [e, abs_sub_comm]
    _ ≤ ∫ t in a..b, k t * P t := hmono
    _ ≤ |e a| + (∫ t in a..b, |m' t| + |f t|) := hmajor
    _ = |m a - y a| + (∫ t in a..b, |m' t|) +
        (∫ t in a..b, |f t|) := by
      rw [hsplit]
      simp [e, abs_sub_comm]
      ring

/-- Forced moving-target defect bound in source/relaxation form.

This is a direct corollary of
`stack_write_field_cap_le_initial_tracking_add_target_deriv_add_forcing`.
If `source = k * m`, then the instantaneous relaxation defect
`source - k * y` is exactly `k * (m - y)`, so the field-cap estimate controls
its absolute integral. -/
theorem stack_write_defect_integral_le_initial_tracking_add_target_deriv_add_forcing
    (y m k source f m' : ℝ → ℝ) (a b : ℝ)
    (hab : a ≤ b)
    (hk_cont : Continuous k)
    (hk_nonneg : ∀ t ∈ Set.Icc a b, 0 ≤ k t)
    (hy_cont : Continuous y)
    (hm_cont : Continuous m)
    (hf_cont : Continuous f)
    (hm'_cont : Continuous m')
    (hy_ode : ∀ t ∈ Set.Icc a b,
      HasDerivAt y (k t * (m t - y t) + f t) t)
    (hm_deriv : ∀ t ∈ Set.Icc a b, HasDerivAt m (m' t) t)
    (hsource : ∀ t ∈ Set.Icc a b, source t = k t * m t) :
    (∫ t in a..b, |source t - k t * y t|) ≤
      |m a - y a| + (∫ t in a..b, |m' t|) +
        (∫ t in a..b, |f t|) := by
  have hfield :=
    stack_write_field_cap_le_initial_tracking_add_target_deriv_add_forcing
      y m k f m' a b hab hk_cont hk_nonneg hy_cont hm_cont hf_cont
      hm'_cont hy_ode hm_deriv
  have hrewrite :
      (∫ t in a..b, |source t - k t * y t|) =
        ∫ t in a..b, k t * |m t - y t| := by
    apply intervalIntegral.integral_congr
    intro t ht
    have htIcc : t ∈ Set.Icc a b := by
      rwa [Set.uIcc_of_le hab] at ht
    have hk0 : 0 ≤ k t := hk_nonneg t htIcc
    have hdiff : k t * m t - k t * y t = k t * (m t - y t) := by
      ring_nf
    change |source t - k t * y t| = k t * |m t - y t|
    calc
      |source t - k t * y t| = |k t * m t - k t * y t| := by
        rw [hsource t htIcc]
      _ = |k t * (m t - y t)| := by
        rw [hdiff]
      _ = k t * |m t - y t| := by
        rw [abs_mul, abs_of_nonneg hk0]
  simpa [hrewrite] using hfield

/-- Closed-interval-continuity/open-interval-derivative version of
`stack_write_defect_integral_le_initial_tracking_add_target_deriv_add_forcing`. -/
theorem stack_write_defect_integral_le_initial_tracking_add_target_deriv_add_forcing_on
    (y m k source f m' : ℝ → ℝ) (a b : ℝ)
    (hab : a ≤ b)
    (hk_cont : ContinuousOn k (Set.Icc a b))
    (hk_nonneg : ∀ t ∈ Set.Icc a b, 0 ≤ k t)
    (hy_cont : ContinuousOn y (Set.Icc a b))
    (hm_cont : ContinuousOn m (Set.Icc a b))
    (hf_cont : ContinuousOn f (Set.Icc a b))
    (hm'_cont : ContinuousOn m' (Set.Icc a b))
    (hy_ode : ∀ t ∈ Set.Ioo a b,
      HasDerivAt y (k t * (m t - y t) + f t) t)
    (hm_deriv : ∀ t ∈ Set.Ioo a b, HasDerivAt m (m' t) t)
    (hsource : ∀ t ∈ Set.Icc a b, source t = k t * m t) :
    (∫ t in a..b, |source t - k t * y t|) ≤
      |m a - y a| + (∫ t in a..b, |m' t|) +
        (∫ t in a..b, |f t|) := by
  have hfield :=
    stack_write_field_cap_le_initial_tracking_add_target_deriv_add_forcing_on
      y m k f m' a b hab hk_cont hk_nonneg hy_cont hm_cont hf_cont
      hm'_cont hy_ode hm_deriv
  have hrewrite :
      (∫ t in a..b, |source t - k t * y t|) =
        ∫ t in a..b, k t * |m t - y t| := by
    apply intervalIntegral.integral_congr
    intro t ht
    have htIcc : t ∈ Set.Icc a b := by
      rwa [Set.uIcc_of_le hab] at ht
    have hk0 : 0 ≤ k t := hk_nonneg t htIcc
    have hdiff : k t * m t - k t * y t = k t * (m t - y t) := by
      ring_nf
    change |source t - k t * y t| = k t * |m t - y t|
    calc
      |source t - k t * y t| = |k t * m t - k t * y t| := by
        rw [hsource t htIcc]
      _ = |k t * (m t - y t)| := by
        rw [hdiff]
      _ = k t * |m t - y t| := by
        rw [abs_mul, abs_of_nonneg hk0]
  simpa [hrewrite] using hfield

/-- Forced moving-target defect bound with target given as a quotient.

This is the form used by active selector coordinates:
`m = r / k`, so the controlled defect is `|r - k * y|`. -/
theorem stack_write_linear_defect_integral_le_initial_tracking_add_target_deriv_add_forcing
    (y k r f m' : ℝ → ℝ) (a b : ℝ)
    (hab : a ≤ b)
    (hk_cont : Continuous k)
    (hk_nonneg : ∀ t ∈ Set.Icc a b, 0 ≤ k t)
    (hk_pos : ∀ t ∈ Set.Icc a b, 0 < k t)
    (hy_cont : Continuous y)
    (hm_cont : Continuous fun t => r t / k t)
    (hf_cont : Continuous f)
    (hm'_cont : Continuous m')
    (hy_ode : ∀ t ∈ Set.Icc a b,
      HasDerivAt y (k t * (r t / k t - y t) + f t) t)
    (hm_deriv : ∀ t ∈ Set.Icc a b,
      HasDerivAt (fun t => r t / k t) (m' t) t) :
    (∫ t in a..b, |r t - k t * y t|) ≤
      |r a / k a - y a| + (∫ t in a..b, |m' t|) +
        (∫ t in a..b, |f t|) := by
  let m : ℝ → ℝ := fun t => r t / k t
  refine
    stack_write_defect_integral_le_initial_tracking_add_target_deriv_add_forcing
      y m k r f m' a b hab hk_cont hk_nonneg hy_cont hm_cont hf_cont
      hm'_cont ?_ ?_ ?_
  · intro t ht
    simpa [m] using hy_ode t ht
  · intro t ht
    simpa [m] using hm_deriv t ht
  · intro t ht
    have hk_ne : k t ≠ 0 := ne_of_gt (hk_pos t ht)
    dsimp [m]
    field_simp [hk_ne]

/-- Closed-interval-continuity/open-interval-derivative version of
`stack_write_linear_defect_integral_le_initial_tracking_add_target_deriv_add_forcing`. -/
theorem stack_write_linear_defect_integral_le_initial_tracking_add_target_deriv_add_forcing_on
    (y k r f m' : ℝ → ℝ) (a b : ℝ)
    (hab : a ≤ b)
    (hk_cont : ContinuousOn k (Set.Icc a b))
    (hk_nonneg : ∀ t ∈ Set.Icc a b, 0 ≤ k t)
    (hk_pos : ∀ t ∈ Set.Icc a b, 0 < k t)
    (hy_cont : ContinuousOn y (Set.Icc a b))
    (hm_cont : ContinuousOn (fun t => r t / k t) (Set.Icc a b))
    (hf_cont : ContinuousOn f (Set.Icc a b))
    (hm'_cont : ContinuousOn m' (Set.Icc a b))
    (hy_ode : ∀ t ∈ Set.Ioo a b,
      HasDerivAt y (k t * (r t / k t - y t) + f t) t)
    (hm_deriv : ∀ t ∈ Set.Ioo a b,
      HasDerivAt (fun t => r t / k t) (m' t) t) :
    (∫ t in a..b, |r t - k t * y t|) ≤
      |r a / k a - y a| + (∫ t in a..b, |m' t|) +
        (∫ t in a..b, |f t|) := by
  let m : ℝ → ℝ := fun t => r t / k t
  refine
    stack_write_defect_integral_le_initial_tracking_add_target_deriv_add_forcing_on
      y m k r f m' a b hab hk_cont hk_nonneg hy_cont hm_cont hf_cont
      hm'_cont ?_ ?_ ?_
  · intro t ht
    simpa [m] using hy_ode t ht
  · intro t ht
    simpa [m] using hm_deriv t ht
  · intro t ht
    have hk_ne : k t ≠ 0 := ne_of_gt (hk_pos t ht)
    dsimp [m]
    field_simp [hk_ne]

/-- Exact mass of the terminal Duhamel kernel on a prefix interval. -/
theorem terminal_kernel_integral_eq_exp_sub
    (k : ℝ → ℝ) (a c b : ℝ)
    (_hac : a ≤ c)
    (hk_cont : Continuous k) :
    (∫ t in a..c,
        Real.exp (-(∫ s in t..b, k s)) * k t) =
      Real.exp (-(∫ s in c..b, k s)) -
        Real.exp (-(∫ s in a..b, k s)) := by
  set K : ℝ → ℝ := fun t => ∫ s in t..b, k s with hKdef
  have hKderiv : ∀ t : ℝ, HasDerivAt K (-(k t)) t := by
    intro t
    exact intervalIntegral.integral_hasDerivAt_left
      (hk_cont.intervalIntegrable t b)
      (hk_cont.stronglyMeasurableAtFilter _ _)
      hk_cont.continuousAt
  set E : ℝ → ℝ := fun t => Real.exp (-(K t)) with hEdef
  have hEderiv : ∀ t : ℝ, HasDerivAt E (Real.exp (-(K t)) * k t) t := by
    intro t
    have hneg : HasDerivAt (fun u => -(K u)) (k t) t := by
      simpa using (hKderiv t).neg
    have h := hneg.exp
    simpa [E] using h
  have hEcont : Continuous E := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (hEderiv t).continuousAt
  have hderiv_on : ∀ t ∈ Set.uIcc a c,
      HasDerivAt E (Real.exp (-(∫ s in t..b, k s)) * k t) t := by
    intro t _ht
    simpa [E, K] using hEderiv t
  have hcont_der :
      Continuous fun t : ℝ => Real.exp (-(∫ s in t..b, k s)) * k t := by
    have hKcont : Continuous K := by
      apply continuous_iff_continuousAt.mpr
      intro t
      exact (hKderiv t).continuousAt
    simpa [K] using
      (Real.continuous_exp.comp (continuous_neg.comp hKcont)).mul hk_cont
  have hFTC :
      (∫ t in a..c, Real.exp (-(∫ s in t..b, k s)) * k t) =
        E c - E a := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv_on
      (hcont_der.intervalIntegrable a c)
  calc
    (∫ t in a..c, Real.exp (-(∫ s in t..b, k s)) * k t)
        = E c - E a := hFTC
    _ = Real.exp (-(∫ s in c..b, k s)) -
        Real.exp (-(∫ s in a..b, k s)) := by
          simp [E, K]

/-- Prefix mass of the terminal kernel is bounded by the terminal exponential
at the prefix endpoint. -/
theorem terminal_kernel_prefix_mass_le_exp
    (k : ℝ → ℝ) (a c b : ℝ)
    (hac : a ≤ c)
    (hk_cont : Continuous k) :
    (∫ t in a..c,
        Real.exp (-(∫ s in t..b, k s)) * k t) ≤
      Real.exp (-(∫ s in c..b, k s)) := by
  rw [terminal_kernel_integral_eq_exp_sub k a c b hac hk_cont]
  exact sub_le_self _ (Real.exp_nonneg _)

/-- A terminal-kernel prefix weighted by a `[0,1]` factor is controlled by the
same prefix mass. -/
theorem terminal_kernel_weighted_unit_prefix_le_exp
    (k r : ℝ → ℝ) (a c b : ℝ)
    (hac : a ≤ c)
    (hk_cont : Continuous k)
    (hr_cont : Continuous r)
    (hk_nonneg : ∀ t ∈ Set.Icc a c, 0 ≤ k t)
    (_hr_nonneg : ∀ t ∈ Set.Icc a c, 0 ≤ r t)
    (hr_le_one : ∀ t ∈ Set.Icc a c, r t ≤ 1) :
    (∫ t in a..c,
        Real.exp (-(∫ s in t..b, k s)) * k t * r t) ≤
      Real.exp (-(∫ s in c..b, k s)) := by
  have hKderiv : ∀ t : ℝ,
      HasDerivAt (fun u => ∫ s in u..b, k s) (-(k t)) t := by
    intro t
    exact intervalIntegral.integral_hasDerivAt_left
      (hk_cont.intervalIntegrable t b)
      (hk_cont.stronglyMeasurableAtFilter _ _)
      hk_cont.continuousAt
  have hKcont : Continuous fun t : ℝ => ∫ s in t..b, k s := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (hKderiv t).continuousAt
  have hkernel_cont :
      Continuous fun t : ℝ => Real.exp (-(∫ s in t..b, k s)) :=
    Real.continuous_exp.comp (continuous_neg.comp hKcont)
  have hbase_cont :
      Continuous fun t : ℝ => Real.exp (-(∫ s in t..b, k s)) * k t :=
    hkernel_cont.mul hk_cont
  have hweighted_cont :
      Continuous fun t : ℝ => Real.exp (-(∫ s in t..b, k s)) * k t * r t :=
    hbase_cont.mul hr_cont
  have hle :
      (∫ t in a..c,
          Real.exp (-(∫ s in t..b, k s)) * k t * r t)
        ≤ ∫ t in a..c,
          Real.exp (-(∫ s in t..b, k s)) * k t := by
    apply intervalIntegral.integral_mono_on hac
    · exact hweighted_cont.intervalIntegrable a c
    · exact hbase_cont.intervalIntegrable a c
    · intro t ht
      have hbase_nonneg :
          0 ≤ Real.exp (-(∫ s in t..b, k s)) * k t :=
        mul_nonneg (Real.exp_nonneg _) (hk_nonneg t ht)
      calc
        Real.exp (-(∫ s in t..b, k s)) * k t * r t
            ≤ Real.exp (-(∫ s in t..b, k s)) * k t * 1 :=
              mul_le_mul_of_nonneg_left (hr_le_one t ht) hbase_nonneg
        _ = Real.exp (-(∫ s in t..b, k s)) * k t := by ring
  exact le_trans hle (terminal_kernel_prefix_mass_le_exp k a c b hac hk_cont)

/-- Split a terminal-kernel integral at `c`: a unit bound on the prefix and a
constant bound on the suffix give the prefix terminal exponential plus the
suffix constant. -/
theorem terminal_kernel_split_abs_bound
    (k d : ℝ → ℝ) (a c b C : ℝ)
    (hac : a ≤ c)
    (hcb : c ≤ b)
    (hk_cont : Continuous k)
    (hd_cont : Continuous d)
    (hk_nonneg : ∀ t ∈ Set.Icc a b, 0 ≤ k t)
    (hprefix : ∀ t ∈ Set.Icc a c, |d t| ≤ 1)
    (hsuffix : ∀ t ∈ Set.Icc c b, |d t| ≤ C)
    (hC : 0 ≤ C) :
    (∫ t in a..b,
        Real.exp (-(∫ s in t..b, k s)) * k t * |d t|) ≤
      Real.exp (-(∫ s in c..b, k s)) + C := by
  have hKderiv : ∀ t : ℝ,
      HasDerivAt (fun u => ∫ s in u..b, k s) (-(k t)) t := by
    intro t
    exact intervalIntegral.integral_hasDerivAt_left
      (hk_cont.intervalIntegrable t b)
      (hk_cont.stronglyMeasurableAtFilter _ _)
      hk_cont.continuousAt
  have hKcont : Continuous fun t : ℝ => ∫ s in t..b, k s := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (hKderiv t).continuousAt
  have hkernel_cont :
      Continuous fun t : ℝ => Real.exp (-(∫ s in t..b, k s)) :=
    Real.continuous_exp.comp (continuous_neg.comp hKcont)
  have hbase_cont :
      Continuous fun t : ℝ => Real.exp (-(∫ s in t..b, k s)) * k t :=
    hkernel_cont.mul hk_cont
  have hd_abs_cont : Continuous fun t : ℝ => |d t| := hd_cont.abs
  have hf_cont :
      Continuous fun t : ℝ =>
        Real.exp (-(∫ s in t..b, k s)) * k t * |d t| :=
    hbase_cont.mul hd_abs_cont
  have hI : ∀ x y : ℝ, IntervalIntegrable
      (fun t : ℝ => Real.exp (-(∫ s in t..b, k s)) * k t * |d t|)
      MeasureTheory.volume x y :=
    fun x y => hf_cont.intervalIntegrable x y
  have hpre :
      (∫ t in a..c,
          Real.exp (-(∫ s in t..b, k s)) * k t * |d t|) ≤
        Real.exp (-(∫ s in c..b, k s)) := by
    exact terminal_kernel_weighted_unit_prefix_le_exp k (fun t => |d t|)
      a c b hac hk_cont hd_abs_cont
      (fun t ht => hk_nonneg t ⟨ht.1, le_trans ht.2 hcb⟩)
      (fun t _ht => abs_nonneg (d t))
      hprefix
  have hsuf :
      (∫ t in c..b,
          Real.exp (-(∫ s in t..b, k s)) * k t * |d t|) ≤ C := by
    have hweighted_cont :
        Continuous fun t : ℝ =>
          C * (Real.exp (-(∫ s in t..b, k s)) * k t) :=
      continuous_const.mul hbase_cont
    have hle :
        (∫ t in c..b,
            Real.exp (-(∫ s in t..b, k s)) * k t * |d t|)
          ≤ ∫ t in c..b,
            C * (Real.exp (-(∫ s in t..b, k s)) * k t) := by
      apply intervalIntegral.integral_mono_on hcb
      · exact hf_cont.intervalIntegrable c b
      · exact hweighted_cont.intervalIntegrable c b
      · intro t ht
        have hbase_nonneg :
            0 ≤ Real.exp (-(∫ s in t..b, k s)) * k t :=
          mul_nonneg (Real.exp_nonneg _) (hk_nonneg t ⟨le_trans hac ht.1, ht.2⟩)
        calc
          Real.exp (-(∫ s in t..b, k s)) * k t * |d t|
              ≤ Real.exp (-(∫ s in t..b, k s)) * k t * C :=
                mul_le_mul_of_nonneg_left (hsuffix t ht) hbase_nonneg
          _ = C * (Real.exp (-(∫ s in t..b, k s)) * k t) := by ring
    have hmass :
        (∫ t in c..b,
            Real.exp (-(∫ s in t..b, k s)) * k t) ≤ 1 := by
      have h :=
        terminal_kernel_prefix_mass_le_exp k c b b hcb hk_cont
      simpa using h
    calc
      (∫ t in c..b,
          Real.exp (-(∫ s in t..b, k s)) * k t * |d t|)
          ≤ ∫ t in c..b,
              C * (Real.exp (-(∫ s in t..b, k s)) * k t) := hle
      _ = C * (∫ t in c..b,
              Real.exp (-(∫ s in t..b, k s)) * k t) := by
            rw [intervalIntegral.integral_const_mul]
      _ ≤ C * 1 := mul_le_mul_of_nonneg_left hmass hC
      _ = C := by ring
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hI a c) (hI c b)
  calc
    (∫ t in a..b,
        Real.exp (-(∫ s in t..b, k s)) * k t * |d t|)
        = (∫ t in a..c,
            Real.exp (-(∫ s in t..b, k s)) * k t * |d t|) +
          (∫ t in c..b,
            Real.exp (-(∫ s in t..b, k s)) * k t * |d t|) := by
            exact hsplit.symm
    _ ≤ Real.exp (-(∫ s in c..b, k s)) + C := add_le_add hpre hsuf

private theorem intervalIntegral_indicator_lt_left
    (f : ℝ → ℝ) {a t b : ℝ} (hat : a ≤ t) (htb : t ≤ b) :
    (∫ s in a..b, Set.indicator (Set.Iio t) f s) =
      ∫ s in a..t, f s := by
  have hab : a ≤ b := le_trans hat htb
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hat]
  rw [MeasureTheory.setIntegral_indicator measurableSet_Iio]
  rw [MeasureTheory.integral_Ioc_eq_integral_Ioo]
  have hset : Set.Ioc a b ∩ Set.Iio t = Set.Ioo a t := by
    ext s
    constructor
    · intro hs
      exact ⟨hs.1.1, hs.2⟩
    · intro hs
      exact ⟨⟨hs.1, le_trans hs.2.le htb⟩, hs.2⟩
  rw [hset]

private theorem intervalIntegral_indicator_lt_right
    (f : ℝ → ℝ) {a s b : ℝ} (has : a ≤ s) (hsb : s ≤ b) :
    (∫ t in a..b, Set.indicator (Set.Ioi s) f t) =
      ∫ t in s..b, f t := by
  have hab : a ≤ b := le_trans has hsb
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hsb]
  rw [MeasureTheory.setIntegral_indicator measurableSet_Ioi]
  have hset : Set.Ioc a b ∩ Set.Ioi s = Set.Ioc s b := by
    ext t
    constructor
    · intro ht
      exact ⟨ht.2, ht.1.2⟩
    · intro ht
      exact ⟨⟨lt_of_le_of_lt has ht.1, ht.2⟩, ht.1⟩
  rw [hset]

/-- Fubini triangle swap for interval integrals of continuous functions:
`∫_a^b ∫_a^t F(s,t) ds dt = ∫_a^b ∫_s^b F(s,t) dt ds`. -/
theorem intervalIntegral_triangle_swap
    (F : ℝ → ℝ → ℝ) {a b : ℝ}
    (hab : a ≤ b)
    (hF_cont : Continuous fun p : ℝ × ℝ => F p.1 p.2) :
    (∫ t in a..b, ∫ s in a..t, F s t) =
      ∫ s in a..b, ∫ t in s..b, F s t := by
  let K : ℝ → ℝ → ℝ := fun t s =>
    Set.indicator (Set.Iio t) (fun u => F u t) s
  have hG_cont : Continuous fun p : ℝ × ℝ => F p.2 p.1 := by
    fun_prop
  have hS_meas : MeasurableSet {p : ℝ × ℝ | p.2 < p.1} :=
    (isOpen_lt continuous_snd continuous_fst).measurableSet
  have hG_int_rect :
      MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => F p.2 p.1)
        (Set.uIcc a b ×ˢ Set.uIcc a b)
        (MeasureTheory.volume.prod MeasureTheory.volume) := by
    exact hG_cont.continuousOn.integrableOn_compact
      (isCompact_uIcc.prod isCompact_uIcc)
  have hG_int :
      MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => F p.2 p.1)
        (Set.uIoc a b ×ˢ Set.uIoc a b)
        (MeasureTheory.volume.prod MeasureTheory.volume) :=
    hG_int_rect.mono_set
      (Set.prod_mono Set.uIoc_subset_uIcc Set.uIoc_subset_uIcc)
  have hK_int_on :
      MeasureTheory.IntegrableOn
        (Set.indicator {p : ℝ × ℝ | p.2 < p.1}
          (fun p : ℝ × ℝ => F p.2 p.1))
        (Set.uIoc a b ×ˢ Set.uIoc a b)
        (MeasureTheory.volume.prod MeasureTheory.volume) :=
    hG_int.indicator hS_meas
  have hK_int :
      MeasureTheory.Integrable (Function.uncurry K)
        ((MeasureTheory.volume.restrict (Set.uIoc a b)).prod
          (MeasureTheory.volume.restrict (Set.uIoc a b))) := by
    rw [MeasureTheory.Measure.prod_restrict]
    change MeasureTheory.IntegrableOn (Function.uncurry K)
      (Set.uIoc a b ×ˢ Set.uIoc a b)
      (MeasureTheory.volume.prod MeasureTheory.volume)
    convert hK_int_on using 1
  have hswap :=
    MeasureTheory.intervalIntegral_integral_swap
      (a := a) (b := b)
      (μ := MeasureTheory.volume.restrict (Set.uIoc a b))
      (f := K) hK_int
  calc
    (∫ t in a..b, ∫ s in a..t, F s t)
        = ∫ t in a..b, ∫ s in a..b, K t s := by
            apply intervalIntegral.integral_congr
            intro t ht
            have htIcc : t ∈ Set.Icc a b := by
              rwa [Set.uIcc_of_le hab] at ht
            exact (intervalIntegral_indicator_lt_left
              (fun s => F s t) htIcc.1 htIcc.2).symm
    _ = ∫ t in a..b, ∫ s, K t s
          ∂(MeasureTheory.volume.restrict (Set.uIoc a b)) := by
            apply intervalIntegral.integral_congr
            intro t _ht
            change (∫ s in a..b, K t s) =
              ∫ s in Set.uIoc a b, K t s
            rw [intervalIntegral.integral_of_le hab, Set.uIoc_of_le hab]
    _ = ∫ s, (∫ t in a..b, K t s)
          ∂(MeasureTheory.volume.restrict (Set.uIoc a b)) := hswap
    _ = ∫ s in a..b, ∫ t in a..b, K t s := by
            rw [intervalIntegral.integral_of_le hab, Set.uIoc_of_le hab]
    _ = ∫ s in a..b, ∫ t in s..b, F s t := by
            apply intervalIntegral.integral_congr
            intro s hs
            have hsIcc : s ∈ Set.Icc a b := by
              rwa [Set.uIcc_of_le hab] at hs
            change (∫ t in a..b, Set.indicator (Set.Ioi s) (fun t => F s t) t) =
              ∫ t in s..b, F s t
            exact intervalIntegral_indicator_lt_right
              (fun t => F s t) hsIcc.1 hsIcc.2

/-- Volterra L1 contraction: the write-kernel convolution of a
nonneg function `g` is bounded by `∫ g`. -/
theorem volterra_write_kernel_l1_le
    (k g : ℝ → ℝ) {a b : ℝ}
    (hab : a ≤ b)
    (hk_cont : Continuous k)
    (hk_nonneg : ∀ t ∈ Set.Icc a b, 0 ≤ k t)
    (hg_cont : Continuous g)
    (hg_nonneg : ∀ t ∈ Set.Icc a b, 0 ≤ g t) :
    (∫ t in a..b,
      k t * (∫ s in a..t,
        Real.exp (-(∫ r in s..t, k r)) * g s)) ≤
      ∫ s in a..b, g s := by
  set K : ℝ → ℝ := fun t => ∫ r in a..t, k r with hKdef
  have hKderiv : ∀ t : ℝ, HasDerivAt K (k t) t := by
    intro t
    exact intervalIntegral.integral_hasDerivAt_right
      (hk_cont.intervalIntegrable a t)
      (hk_cont.stronglyMeasurableAtFilter _ _)
      hk_cont.continuousAt
  have hKcont : Continuous K := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (hKderiv t).continuousAt
  have hkernel_interval :
      ∀ s t : ℝ, (∫ r in s..t, k r) = K t - K s := by
    intro s t
    have hsplit :
        (∫ r in a..t, k r) =
          (∫ r in a..s, k r) + (∫ r in s..t, k r) :=
      (intervalIntegral.integral_add_adjacent_intervals
        (hk_cont.intervalIntegrable a s)
        (hk_cont.intervalIntegrable s t)).symm
    dsimp [K]
    linarith
  have hF_cont : Continuous fun p : ℝ × ℝ =>
      k p.2 * (Real.exp (-(∫ r in p.1..p.2, k r)) * g p.1) := by
    have hF_cont' : Continuous fun p : ℝ × ℝ =>
        k p.2 * (Real.exp (-(K p.2 - K p.1)) * g p.1) := by
      fun_prop
    refine hF_cont'.congr ?_
    intro p
    rw [hkernel_interval p.1 p.2]
  have hswap := intervalIntegral_triangle_swap
    (fun s t => k t * (Real.exp (-(∫ r in s..t, k r)) * g s))
    hab hF_cont
  have hrewrite :
      (∫ t in a..b,
        k t * (∫ s in a..t,
          Real.exp (-(∫ r in s..t, k r)) * g s)) =
        ∫ s in a..b,
          g s * (∫ t in s..b,
            Real.exp (-(∫ r in s..t, k r)) * k t) := by
    calc
      (∫ t in a..b,
        k t * (∫ s in a..t,
          Real.exp (-(∫ r in s..t, k r)) * g s))
          = ∫ t in a..b, ∫ s in a..t,
              k t * (Real.exp (-(∫ r in s..t, k r)) * g s) := by
              apply intervalIntegral.integral_congr
              intro t _ht
              change k t * (∫ s in a..t,
                  Real.exp (-(∫ r in s..t, k r)) * g s) =
                ∫ s in a..t,
                  k t * (Real.exp (-(∫ r in s..t, k r)) * g s)
              rw [intervalIntegral.integral_const_mul]
      _ = ∫ s in a..b, ∫ t in s..b,
              k t * (Real.exp (-(∫ r in s..t, k r)) * g s) := hswap
      _ = ∫ s in a..b,
              g s * (∫ t in s..b,
                Real.exp (-(∫ r in s..t, k r)) * k t) := by
              apply intervalIntegral.integral_congr
              intro s _hs
              calc
                (∫ t in s..b,
                    k t * (Real.exp (-(∫ r in s..t, k r)) * g s))
                    = ∫ t in s..b,
                        g s * (Real.exp (-(∫ r in s..t, k r)) * k t) := by
                        apply intervalIntegral.integral_congr
                        intro t _ht
                        ring
                _ = g s * (∫ t in s..b,
                        Real.exp (-(∫ r in s..t, k r)) * k t) := by
                        rw [intervalIntegral.integral_const_mul]
  rw [hrewrite]
  have hmass_cont_on : ContinuousOn
      (fun s : ℝ => ∫ t in s..b,
        Real.exp (-(∫ r in s..t, k r)) * k t)
      (Set.Icc a b) := by
    have hmass_expr_cont_on : ContinuousOn
        (fun s : ℝ => 1 - Real.exp (-(K b - K s))) (Set.Icc a b) := by
      exact (continuous_const.sub
        (Real.continuous_exp.comp
          (continuous_neg.comp
            (continuous_const.sub hKcont)))).continuousOn
    refine hmass_expr_cont_on.congr ?_
    intro s hs
    change (∫ t in s..b, Real.exp (-(∫ r in s..t, k r)) * k t) =
      1 - Real.exp (-(K b - K s))
    rw [forward_kernel_integral_eq_one_sub_exp k s b hs.2 hk_cont,
      hkernel_interval s b]
  have hleft_int : IntervalIntegrable
      (fun s : ℝ => g s *
        (∫ t in s..b, Real.exp (-(∫ r in s..t, k r)) * k t))
      MeasureTheory.volume a b :=
    ((hg_cont.continuousOn).mul hmass_cont_on).intervalIntegrable_of_Icc hab
  have hright_int : IntervalIntegrable g MeasureTheory.volume a b :=
    hg_cont.intervalIntegrable a b
  apply intervalIntegral.integral_mono_on hab hleft_int hright_int
  intro s hs
  have hmass_le :
      (∫ t in s..b, Real.exp (-(∫ r in s..t, k r)) * k t) ≤ 1 :=
    write_forward_kernel_mass_le_one k s b hs.2 hk_cont
      (by
        intro t ht
        exact hk_nonneg t ⟨le_trans hs.1 ht.1, ht.2⟩)
  calc
    g s * (∫ t in s..b, Real.exp (-(∫ r in s..t, k r)) * k t)
        ≤ g s * 1 := mul_le_mul_of_nonneg_left hmass_le (hg_nonneg s hs)
    _ = g s := by ring

/-- ODE total-variation bound: the integral of `k |m − y|` against the
write rate `k ≥ 0` is bounded by the initial error plus the total
variation of the moving target `m`.  This is strictly tighter than
`stack_write_error_integral_le_initial_add_target` (which keeps `k`
inside the target integral) and is needed when the write rate grows
exponentially on edge windows.

The proof uses variation of constants + Volterra L1 contraction,
avoiding the nondifferentiability of `|·|` at zeros. -/
theorem stack_write_tracking_total_variation_le
    (y m k mdot : ℝ → ℝ) {a b : ℝ}
    (hab : a ≤ b)
    (hk_cont : Continuous k)
    (hk_nonneg : ∀ t ∈ Set.Icc a b, 0 ≤ k t)
    (hm_cont : Continuous m)
    (hmdot_cont : Continuous mdot)
    (hm_deriv : ∀ t ∈ Set.Icc a b, HasDerivAt m (mdot t) t)
    (hy_ode : ∀ t ∈ Set.Icc a b,
      HasDerivAt y (k t * (m t - y t)) t) :
    (∫ t in a..b, k t * |m t - y t|) ≤
      |m a - y a| + (∫ t in a..b, |mdot t|) := by
  have hy_cont : ContinuousOn y (Set.Icc a b) := by
    intro t ht
    exact (hy_ode t ht).continuousAt.continuousWithinAt
  have hfield :=
    stack_write_field_cap_le_initial_tracking_add_target_deriv_add_forcing_on
      y m k (fun _ : ℝ => 0) mdot a b hab
      hk_cont.continuousOn hk_nonneg hy_cont hm_cont.continuousOn
      continuous_const.continuousOn hmdot_cont.continuousOn
      (by
        intro t ht
        simpa using hy_ode t (Set.Ioo_subset_Icc_self ht))
      (by
        intro t ht
        exact hm_deriv t (Set.Ioo_subset_Icc_self ht))
  simpa using hfield

/-! ## Affine recurrence unrolling -/

/-- Exact finite unrolling of an affine one-step recurrence:
`e(n) ≤ α^n e(0) + ∑_{j<n} α^{n-1-j} β(j)`. -/
theorem affine_rec_unroll
    {α : ℝ} {e β : ℕ → ℝ}
    (hα0 : 0 ≤ α)
    (hrec : ∀ j, e (j + 1) ≤ α * e j + β j) :
    ∀ n : ℕ,
      e n ≤ α ^ n * e 0 +
        (Finset.range n).sum (fun j => α ^ (n - 1 - j) * β j) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    change e (n + 1) ≤ α ^ (n + 1) * e 0 +
      (Finset.range (n + 1)).sum (fun j => α ^ (n + 1 - 1 - j) * β j)
    have hmul_ih :
        α * e n ≤ α * (α ^ n * e 0 +
          (Finset.range n).sum (fun j => α ^ (n - 1 - j) * β j)) :=
      mul_le_mul_of_nonneg_left ih hα0
    have hinit : α * (α ^ n * e 0) = α ^ (n + 1) * e 0 := by
      rw [← mul_assoc, mul_comm α (α ^ n), ← pow_succ]
    have hsum_shift :
        α * (Finset.range n).sum (fun j => α ^ (n - 1 - j) * β j) =
          (Finset.range n).sum (fun j => α ^ (n - j) * β j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      have hjlt : j < n := Finset.mem_range.mp hj
      have hsucc : n - j = (n - 1 - j) + 1 := by omega
      rw [← mul_assoc, mul_comm α (α ^ (n - 1 - j)), ← pow_succ, hsucc]
    have hunroll_step :
        α * (α ^ n * e 0 +
          (Finset.range n).sum (fun j => α ^ (n - 1 - j) * β j)) + β n =
        α ^ (n + 1) * e 0 +
          (Finset.range (n + 1)).sum (fun j => α ^ (n + 1 - 1 - j) * β j) := by
      rw [mul_add, hinit, hsum_shift, add_assoc, Finset.sum_range_succ]
      simp
    calc
      e (n + 1) ≤ α * e n + β n := hrec n
      _ ≤ α * (α ^ n * e 0 +
            (Finset.range n).sum (fun j => α ^ (n - 1 - j) * β j)) + β n := by
          linarith
      _ = α ^ (n + 1) * e 0 +
            (Finset.range (n + 1)).sum (fun j => α ^ (n + 1 - 1 - j) * β j) :=
          hunroll_step

/-- Geometric envelope for an affine recurrence with geometric source.
Given `e(n) ≤ α^n*e(0) + Σ α^{n-1-j}*β(j)` with `α ≤ σ < 1` and
`β(j) ≤ Cβ*r^j` with `r < σ`, conclude `e(n) ≤ C*σ^n`.

The convolution sum is bounded: `Σ σ^{n-1-j}*r^j ≤ σ^n/(σ-r)`. -/
theorem affine_unroll_geometric_envelope
    {σ r : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ < 1) (hr0 : 0 ≤ r) (hrσ : r < σ)
    {e β : ℕ → ℝ}
    {α : ℝ} (hα0 : 0 ≤ α) (hα_le : α ≤ σ)
    {Cβ : ℝ} (hCβ0 : 0 ≤ Cβ)
    (he_unroll : ∀ n,
      e n ≤ α ^ n * e 0 +
        (Finset.range n).sum (fun j => α ^ (n - 1 - j) * β j))
    (hβ_bound : ∀ j, β j ≤ Cβ * r ^ j) :
    ∀ n : ℕ, e n ≤ (max 0 (e 0) + Cβ / (σ - r)) * σ ^ n := by
  intro n
  have _ : σ < 1 := hσ1
  have hden_pos : 0 < σ - r := sub_pos.mpr hrσ
  have hσpow_nonneg : 0 ≤ σ ^ n := pow_nonneg hσ0 n
  have hinit :
      α ^ n * e 0 ≤ max 0 (e 0) * σ ^ n := by
    have hpow_le : α ^ n ≤ σ ^ n := pow_le_pow_left₀ hα0 hα_le n
    have hαpow_nonneg : 0 ≤ α ^ n := pow_nonneg hα0 n
    by_cases he0_nonneg : 0 ≤ e 0
    · calc
        α ^ n * e 0 ≤ σ ^ n * e 0 :=
          mul_le_mul_of_nonneg_right hpow_le he0_nonneg
        _ = max 0 (e 0) * σ ^ n := by
          rw [max_eq_right he0_nonneg]
          ring
    · have he0_nonpos : e 0 ≤ 0 := le_of_not_ge he0_nonneg
      calc
        α ^ n * e 0 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hαpow_nonneg he0_nonpos
        _ ≤ max 0 (e 0) * σ ^ n :=
          mul_nonneg (le_max_left 0 (e 0)) hσpow_nonneg
  have hsum_step :
      (Finset.range n).sum (fun j => α ^ (n - 1 - j) * β j) ≤
        (Finset.range n).sum (fun j => σ ^ (n - 1 - j) * (Cβ * r ^ j)) := by
    apply Finset.sum_le_sum
    intro j _hj
    have hpow_nonneg : 0 ≤ α ^ (n - 1 - j) := pow_nonneg hα0 _
    have hsrc_nonneg : 0 ≤ Cβ * r ^ j :=
      mul_nonneg hCβ0 (pow_nonneg hr0 j)
    have hpow_le : α ^ (n - 1 - j) ≤ σ ^ (n - 1 - j) :=
      pow_le_pow_left₀ hα0 hα_le _
    calc
      α ^ (n - 1 - j) * β j
          ≤ α ^ (n - 1 - j) * (Cβ * r ^ j) :=
            mul_le_mul_of_nonneg_left (hβ_bound j) hpow_nonneg
      _ ≤ σ ^ (n - 1 - j) * (Cβ * r ^ j) :=
            mul_le_mul_of_nonneg_right hpow_le hsrc_nonneg
  have hsum_bound :
      (Finset.range n).sum (fun j => σ ^ (n - 1 - j) * (Cβ * r ^ j)) ≤
        Cβ * (σ ^ n / (σ - r)) := by
    have hgeom_ne : r ≠ σ := ne_of_lt hrσ
    have hrpow_nonneg : 0 ≤ r ^ n := pow_nonneg hr0 n
    have hsum_rewrite :
        (Finset.range n).sum (fun j => σ ^ (n - 1 - j) * (Cβ * r ^ j)) =
          Cβ * (Finset.range n).sum (fun j => r ^ j * σ ^ (n - 1 - j)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _hj
      ring
    have hgeom :
        (Finset.range n).sum (fun j => r ^ j * σ ^ (n - 1 - j)) =
          (r ^ n - σ ^ n) / (r - σ) := by
      simpa using (geom₂_sum (x := r) (y := σ) hgeom_ne n)
    have hflip :
        (r ^ n - σ ^ n) / (r - σ) = (σ ^ n - r ^ n) / (σ - r) := by
      have hnum : r ^ n - σ ^ n = -(σ ^ n - r ^ n) := by ring
      have hden : r - σ = -(σ - r) := by ring
      rw [hnum, hden]
      exact neg_div_neg_eq (σ ^ n - r ^ n) (σ - r)
    have hnum_le : σ ^ n - r ^ n ≤ σ ^ n := sub_le_self _ hrpow_nonneg
    have hdiv_le :
        (σ ^ n - r ^ n) / (σ - r) ≤ σ ^ n / (σ - r) :=
      div_le_div_of_nonneg_right hnum_le hden_pos.le
    calc
      (Finset.range n).sum (fun j => σ ^ (n - 1 - j) * (Cβ * r ^ j))
          = Cβ * ((r ^ n - σ ^ n) / (r - σ)) := by rw [hsum_rewrite, hgeom]
      _ = Cβ * ((σ ^ n - r ^ n) / (σ - r)) := by rw [hflip]
      _ ≤ Cβ * (σ ^ n / (σ - r)) := mul_le_mul_of_nonneg_left hdiv_le hCβ0
  have htail :
      (Finset.range n).sum (fun j => α ^ (n - 1 - j) * β j) ≤
        Cβ * (σ ^ n / (σ - r)) :=
    hsum_step.trans hsum_bound
  have hmain :
      e n ≤ max 0 (e 0) * σ ^ n + Cβ * (σ ^ n / (σ - r)) := by
    calc
      e n ≤ α ^ n * e 0 +
          (Finset.range n).sum (fun j => α ^ (n - 1 - j) * β j) := he_unroll n
      _ ≤ max 0 (e 0) * σ ^ n + Cβ * (σ ^ n / (σ - r)) :=
          add_le_add hinit htail
  calc
    e n ≤ max 0 (e 0) * σ ^ n + Cβ * (σ ^ n / (σ - r)) := hmain
    _ = (max 0 (e 0) + Cβ / (σ - r)) * σ ^ n := by
      field_simp [hden_pos.ne']

end Ripple.BoundedUniversality.BGP
