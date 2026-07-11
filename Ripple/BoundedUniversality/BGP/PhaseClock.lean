/-
Ripple.BoundedUniversality.BGP.PhaseClock
---------------------
The rational phase-clock iterator and the all-time tracking theorem
(paper-draft/main.tex §3: constr:phase-clock, lem:pulse-integrals,
lem:full-period-reach, lem:active-half, lem:inactive-leakage,
lem:perturbation-recurrence, thm:all-time-tracking).

Revision 2 after adversarial round 1 (codex R1; log:
notes/bgp-adversarial-rounds.md):
* R1#4/#5: `perturbation_recurrence` and `all_time_tracking` now carry
  the paper's constants verbatim (factor 2 from the two-channel
  composition; cascade `2κ < 1`, `2κD + 2χD + ηstep ≤ η(1−2κ)`,
  `η + χD ≤ r₀` per main.tex:879).
* R1#6: the moving-box hypothesis now covers `x_{j+1}` and `F(u(t))`,
  not only `z, u` (per main.tex:872-875).
* P1 `targeting_bound` and P2 `hold_bound` are PROVED (transplanted
  from ProofsDraft, built EXIT_0 on uisai2 2026-06-11); statement
  delta vs scaffold v1: `Continuous φ/w` global (applications are
  qPulse and F∘u, both globally continuous), unused `φ ≤ 1` dropped,
  `0 ≤ δ` derived.

Remaining obligations: P3 (integral bounds), P4 (recurrence),
P5 (all-time tracking), P6 (feasibility).  No new axioms.
-/

import Ripple.BoundedUniversality.BGP.Interfaces
import Mathlib

namespace Ripple.BoundedUniversality.BGP

open Real intervalIntegral
open Filter Topology

/-! ## Pulses (paper notation q_M, r_M after constr:phase-clock) -/

/-- Active pulse `q_M(t) = ((1 + sin t)/2)^M`. -/
noncomputable def qPulse (M : ℕ) (t : ℝ) : ℝ := ((1 + Real.sin t) / 2) ^ M

/-- Passive pulse `r_M(t) = ((1 - sin t)/2)^M`. -/
noncomputable def rPulse (M : ℕ) (t : ℝ) : ℝ := ((1 - Real.sin t) / 2) ^ M

theorem qPulse_continuous (M : ℕ) : Continuous (qPulse M) := by
  unfold qPulse; fun_prop

theorem rPulse_continuous (M : ℕ) : Continuous (rPulse M) := by
  unfold rPulse; fun_prop

theorem qPulse_nonneg (M : ℕ) (t : ℝ) : 0 ≤ qPulse M t := by
  apply pow_nonneg
  nlinarith [Real.neg_one_le_sin t]

theorem rPulse_nonneg (M : ℕ) (t : ℝ) : 0 ≤ rPulse M t := by
  apply pow_nonneg
  nlinarith [Real.sin_le_one t]

theorem qPulse_le_one (M : ℕ) (t : ℝ) : qPulse M t ≤ 1 := by
  apply pow_le_one₀
  · nlinarith [Real.neg_one_le_sin t]
  · nlinarith [Real.sin_le_one t]

theorem rPulse_le_one (M : ℕ) (t : ℝ) : rPulse M t ≤ 1 := by
  apply pow_le_one₀
  · nlinarith [Real.sin_le_one t]
  · nlinarith [Real.neg_one_le_sin t]

/-- Off-phase suppression: where `sin ≤ 0`, the active pulse is at
most `2^{-M}` (lem:inactive-leakage's pointwise core). -/
theorem qPulse_le_offphase {M : ℕ} {t : ℝ} (h : Real.sin t ≤ 0) :
    qPulse M t ≤ (1 / 2) ^ M := by
  apply pow_le_pow_left₀
  · nlinarith [Real.neg_one_le_sin t]
  · linarith

/-- Active-window lower bound: where `sin ≥ 1/2`, the active pulse is
at least `(3/4)^M` (lem:active-half's pointwise core). -/
theorem qPulse_ge_active {M : ℕ} {t : ℝ} (h : (1:ℝ)/2 ≤ Real.sin t) :
    (3 / 4 : ℝ) ^ M ≤ qPulse M t := by
  apply pow_le_pow_left₀ (by norm_num)
  linarith

/-- Where `sin ≥ 0`, the passive pulse is at most `2^{-M}`. -/
theorem rPulse_le_offphase {M : ℕ} {t : ℝ} (h : 0 ≤ Real.sin t) :
    rPulse M t ≤ (1 / 2) ^ M := by
  apply pow_le_pow_left₀
  · nlinarith [Real.sin_le_one t]
  · linarith

/-- Where `sin ≤ -1/2`, the passive pulse is at least `(3/4)^M`. -/
theorem rPulse_ge_active {M : ℕ} {t : ℝ} (h : Real.sin t ≤ -(1/2)) :
    (3 / 4 : ℝ) ^ M ≤ rPulse M t := by
  apply pow_le_pow_left₀ (by norm_num)
  linarith

/-! ## Sine windows on shifted cycles -/

/-- `sin ≥ 1/2` on `[2πj + π/6, 2πj + 5π/6]`. -/
theorem sin_window_ge (j : ℕ) {t : ℝ}
    (h1 : 2*π*j + π/6 ≤ t) (h2 : t ≤ 2*π*j + 5*π/6) :
    (1:ℝ)/2 ≤ Real.sin t := by
  have hπ := Real.pi_pos
  have hteq : t = (t - 2*π*j) + (j : ℕ) * (2*π) := by push_cast; ring
  have hsin : Real.sin t = Real.sin (t - 2*π*j) := by
    conv_lhs => rw [hteq]
    rw [Real.sin_add_nat_mul_two_pi]
  rw [hsin]
  set x := t - 2*π*(j:ℝ) with hx
  have hx1 : π/6 ≤ x := by simp only [hx]; linarith
  have hx2 : x ≤ 5*π/6 := by simp only [hx]; linarith
  have hy : |π/2 - x| ≤ π/3 := abs_le.mpr ⟨by linarith, by linarith⟩
  calc (1:ℝ)/2 = Real.cos (π/3) := (Real.cos_pi_div_three).symm
    _ ≤ Real.cos |π/2 - x| :=
        Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith) hy
    _ = Real.cos (π/2 - x) := Real.cos_abs _
    _ = Real.sin x := Real.cos_pi_div_two_sub x

/-- `sin ≤ 0` on `[2πj + π, 2πj + 2π]`. -/
theorem sin_window_nonpos (j : ℕ) {t : ℝ}
    (h1 : 2*π*j + π ≤ t) (h2 : t ≤ 2*π*j + 2*π) :
    Real.sin t ≤ 0 := by
  have hπ := Real.pi_pos
  have hteq : t = (t - 2*π*j) + (j : ℕ) * (2*π) := by push_cast; ring
  have hsin : Real.sin t = Real.sin (t - 2*π*j) := by
    conv_lhs => rw [hteq]
    rw [Real.sin_add_nat_mul_two_pi]
  rw [hsin]
  set x := t - 2*π*(j:ℝ) with hx
  have hx1 : π ≤ x := by simp only [hx]; linarith
  have hx2 : x ≤ 2*π := by simp only [hx]; linarith
  have h0 : 0 ≤ Real.sin (x - π) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have hid := Real.sin_sub_pi x
  linarith [h0, hid.symm.le, hid.le]

/-- `sin ≥ 0` on `[2πj, 2πj + π]`. -/
theorem sin_window_nonneg (j : ℕ) {t : ℝ}
    (h1 : 2*π*(j:ℝ) ≤ t) (h2 : t ≤ 2*π*j + π) :
    0 ≤ Real.sin t := by
  have hπ := Real.pi_pos
  have hteq : t = (t - 2*π*j) + (j : ℕ) * (2*π) := by push_cast; ring
  have hsin : Real.sin t = Real.sin (t - 2*π*j) := by
    conv_lhs => rw [hteq]
    rw [Real.sin_add_nat_mul_two_pi]
  rw [hsin]
  exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)

/-- `sin ≤ -1/2` on `[2πj + 7π/6, 2πj + 11π/6]`. -/
theorem sin_window_le_neg_half (j : ℕ) {t : ℝ}
    (h1 : 2*π*j + 7*π/6 ≤ t) (h2 : t ≤ 2*π*j + 11*π/6) :
    Real.sin t ≤ -(1/2) := by
  have hπ := Real.pi_pos
  have hteq : t = (t - 2*π*j) + (j : ℕ) * (2*π) := by push_cast; ring
  have hsin : Real.sin t = Real.sin (t - 2*π*j) := by
    conv_lhs => rw [hteq]
    rw [Real.sin_add_nat_mul_two_pi]
  rw [hsin]
  set x := t - 2*π*(j:ℝ) with hx
  have hx1 : 7*π/6 ≤ x := by simp only [hx]; linarith
  have hx2 : x ≤ 11*π/6 := by simp only [hx]; linarith
  have hid := Real.sin_sub_pi x
  have hy : |π/2 - (x - π)| ≤ π/3 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hge : (1:ℝ)/2 ≤ Real.sin (x - π) := by
    calc (1:ℝ)/2 = Real.cos (π/3) := (Real.cos_pi_div_three).symm
      _ ≤ Real.cos |π/2 - (x - π)| :=
          Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith) hy
      _ = Real.cos (π/2 - (x - π)) := Real.cos_abs _
      _ = Real.sin (x - π) := Real.cos_pi_div_two_sub _
  linarith [hid]

/-! ## The iterator system (constr:phase-clock) -/

/-- A solution of the phase-clock iterator on `ℝ^{2d+2}` for the step
map `Fr` (the real evaluation of the rationalised step module), gain
`A`, pulse exponent `M`, started at the encoded configuration `x₀`.
The oscillator has been solved exactly (`sin`, `cos`): by
`Ripple.BoundedUniversality.GPAC.ratClockSemantics` and ODE uniqueness this is equivalent
to carrying `(s, c)` as coordinates. -/
structure IteratorSol (d : ℕ) (Fr : (Fin d → ℝ) → Fin d → ℝ)
    (A : ℝ) (M : ℕ) (x₀ : Fin d → ℝ) where
  z : ℝ → Fin d → ℝ
  u : ℝ → Fin d → ℝ
  init_z : z 0 = x₀
  init_u : u 0 = x₀
  -- FORWARD-ONLY ode fields (post-R3 author finding, agent-D blocker
  -- HANDOFF/p10-blocker.md): a two-sided `∀ t : ℝ` requirement is
  -- unsupplyable — the polynomial feedback can blow up backward in
  -- time.  Continuity is carried as explicit fields instead of being
  -- derived from global differentiability.
  cont_z : ∀ i : Fin d, Continuous fun t => z t i
  cont_u : ∀ i : Fin d, Continuous fun t => u t i
  ode_z : ∀ (t : ℝ), 0 ≤ t → ∀ (i : Fin d),
    HasDerivAt (fun τ => z τ i) (A * qPulse M t * (Fr (u t) i - z t i)) t
  ode_u : ∀ (t : ℝ), 0 ≤ t → ∀ (i : Fin d),
    HasDerivAt (fun τ => u τ i) (A * rPulse M t * (z t i - u t i)) t

/-! ## The two analytic workhorses (PROVED) -/

/-- **P2, hold bound** (inactive-half leakage mechanism,
lem:inactive-leakage).  If `|y'| ≤ η` on `[a, b]` then
`|y b - y a| ≤ η (b - a)`. -/
theorem hold_bound (y g : ℝ → ℝ) (η : ℝ) (a b : ℝ) (hab : a ≤ b)
    (hy : ∀ t ∈ Set.Icc a b, HasDerivAt y (g t) t)
    (hg : ∀ t ∈ Set.Icc a b, |g t| ≤ η) :
    |y b - y a| ≤ η * (b - a) := by
  have hconv : Convex ℝ (Set.Icc a b) := convex_Icc a b
  have hderiv : ∀ t ∈ Set.Icc a b, HasDerivWithinAt y (g t) (Set.Icc a b) t :=
    fun t ht => (hy t ht).hasDerivWithinAt
  have hbound : ∀ t ∈ Set.Icc a b, ‖g t‖ ≤ η := by
    intro t ht
    rw [Real.norm_eq_abs]
    exact hg t ht
  have h := hconv.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound
    (Set.right_mem_Icc.mpr hab) (Set.left_mem_Icc.mpr hab)
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at h
  calc |y b - y a| ≤ η * |b - a| := by
        simpa [abs_sub_comm] using h
    _ = η * (b - a) := by rw [abs_of_nonneg (by linarith)]

/-- **P1, targeting bound** (active-half reach mechanism,
lem:active-half).  Integrating-factor estimate: if
`y' = A φ(t) (w t - y)` with `φ ≥ 0` on `[a,b]` and `|w t - w₀| ≤ δ`
on `[a, b]`, then
`|y b - w₀| ≤ exp (-A ∫_a^b φ) · |y a - w₀| + δ`. -/
theorem targeting_bound
    (A : ℝ) (hA : 0 < A) (φ w : ℝ → ℝ) (y : ℝ → ℝ)
    (a b : ℝ) (hab : a ≤ b)
    (hφ_cont : Continuous φ)
    (hφ0 : ∀ t ∈ Set.Icc a b, 0 ≤ φ t)
    (hw_cont : Continuous w)
    (w₀ δ : ℝ) (hδ : ∀ t ∈ Set.Icc a b, |w t - w₀| ≤ δ)
    (hy : ∀ t ∈ Set.Icc a b, HasDerivAt y (A * φ t * (w t - y t)) t) :
    |y b - w₀| ≤ Real.exp (-(A * ∫ t in a..b, φ t)) * |y a - w₀| + δ := by
  set Φ : ℝ → ℝ := fun t => ∫ s in a..t, φ s with hΦdef
  have hΦderiv : ∀ t : ℝ, HasDerivAt Φ (φ t) t := by
    intro t
    exact intervalIntegral.integral_hasDerivAt_right
      (hφ_cont.intervalIntegrable a t)
      (hφ_cont.stronglyMeasurableAtFilter _ _)
      hφ_cont.continuousAt
  have hΦa : Φ a = 0 := by simp [hΦdef]
  have hΦcont : Continuous Φ := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (hΦderiv t).continuousAt
  set E : ℝ → ℝ := fun t => Real.exp (A * Φ t) with hEdef
  have hEderiv : ∀ t : ℝ,
      HasDerivAt E (A * φ t * Real.exp (A * Φ t)) t := by
    intro t
    have h1 : HasDerivAt (fun τ => A * Φ τ) (A * φ t) t :=
      (hΦderiv t).const_mul A
    have h2 := h1.exp
    convert h2 using 1
    ring
  have hEpos : ∀ t, 0 < E t := fun t => Real.exp_pos _
  have hδ0 : 0 ≤ δ :=
    le_trans (abs_nonneg _) (hδ a (Set.left_mem_Icc.mpr hab))
  set v : ℝ → ℝ := fun t => (y t - w₀) * E t with hvdef
  have hvderiv : ∀ t ∈ Set.Icc a b,
      HasDerivAt v (A * φ t * (w t - w₀) * E t) t := by
    intro t ht
    have h1 : HasDerivAt (fun τ => y τ - w₀) (A * φ t * (w t - y t)) t :=
      (hy t ht).sub_const w₀
    have h2 := h1.mul (hEderiv t)
    convert h2 using 1
    simp only [hEdef]
    ring
  have hcont_integrand : Continuous (fun t => A * φ t * (w t - w₀) * E t) := by
    have : Continuous E := Real.continuous_exp.comp (continuous_const.mul hΦcont)
    fun_prop
  have hv_ftc : (∫ t in a..b, A * φ t * (w t - w₀) * E t) = v b - v a := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro t ht
      rw [Set.uIcc_of_le hab] at ht
      exact hvderiv t ht
    · exact hcont_integrand.intervalIntegrable a b
  have hE_ftc : (∫ t in a..b, A * φ t * E t) = E b - E a := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro t _
      exact hEderiv t
    · have : Continuous (fun t => A * φ t * E t) := by
        have : Continuous E := Real.continuous_exp.comp (continuous_const.mul hΦcont)
        fun_prop
      exact this.intervalIntegrable a b
  have hEa : E a = 1 := by simp [hEdef, hΦa]
  have hbound : |v b - v a| ≤ δ * (E b - 1) := by
    rw [← hv_ftc]
    have h1 : |∫ t in a..b, A * φ t * (w t - w₀) * E t|
        ≤ ∫ t in a..b, |A * φ t * (w t - w₀) * E t| :=
      intervalIntegral.abs_integral_le_integral_abs hab
    have h2 : (∫ t in a..b, |A * φ t * (w t - w₀) * E t|)
        ≤ ∫ t in a..b, δ * (A * φ t * E t) := by
      apply intervalIntegral.integral_mono_on hab
      · exact (hcont_integrand.abs).intervalIntegrable a b
      · have : Continuous (fun t => δ * (A * φ t * E t)) := by
          have : Continuous E := Real.continuous_exp.comp (continuous_const.mul hΦcont)
          fun_prop
        exact this.intervalIntegrable a b
      · intro t ht
        have hφt := hφ0 t ht
        have hEt := (hEpos t).le
        have hwt := hδ t ht
        have hAφE : 0 ≤ A * φ t * E t := by positivity
        calc |A * φ t * (w t - w₀) * E t|
            = (A * φ t * E t) * |w t - w₀| := by
              rw [abs_mul, abs_mul, abs_mul]
              rw [abs_of_nonneg hA.le, abs_of_nonneg hφt, abs_of_nonneg hEt]
              ring
          _ ≤ (A * φ t * E t) * δ := by
              apply mul_le_mul_of_nonneg_left hwt hAφE
          _ = δ * (A * φ t * E t) := by ring
    have h3 : (∫ t in a..b, δ * (A * φ t * E t)) = δ * (E b - 1) := by
      rw [intervalIntegral.integral_const_mul, hE_ftc, hEa]
    calc |∫ t in a..b, A * φ t * (w t - w₀) * E t|
        ≤ ∫ t in a..b, |A * φ t * (w t - w₀) * E t| := h1
      _ ≤ ∫ t in a..b, δ * (A * φ t * E t) := h2
      _ = δ * (E b - 1) := h3
  have hvb : |v b| ≤ |v a| + δ * (E b - 1) := by
    have h := abs_sub_abs_le_abs_sub (v b) (v a)
    linarith [hbound]
  have hva : |v a| = |y a - w₀| := by
    simp [hvdef, hEa]
  have hvb' : |v b| = |y b - w₀| * E b := by
    rw [hvdef]
    rw [abs_mul, abs_of_pos (hEpos b)]
  rw [hva, hvb'] at hvb
  have hEb := hEpos b
  have key : |y b - w₀| ≤ |y a - w₀| / E b + δ := by
    rw [div_add' _ _ _ (ne_of_gt hEb)]
    rw [le_div_iff₀ hEb]
    calc |y b - w₀| * E b ≤ |y a - w₀| + δ * (E b - 1) := hvb
      _ = |y a - w₀| + δ * E b - δ := by ring
      _ ≤ |y a - w₀| + δ * E b := by linarith
  have hEinv : |y a - w₀| / E b
      = Real.exp (-(A * Φ b)) * |y a - w₀| := by
    simp only [hEdef]
    rw [Real.exp_neg, div_eq_mul_inv, mul_comm]
  rw [hEinv] at key
  simpa [hΦdef] using key

/-- **P2′, hold bound in INTEGRAL form** (ChatGPT life1 audit,
2026-06-11: the dynamic-gate leak constant `dynChi` dominates only the
integral-form drift, not sup×length — formalize the hold estimate as
`|Δy| ≤ ∫|g|`). -/
theorem hold_bound_integral (y g : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hgc : Continuous g)
    (hy : ∀ t ∈ Set.Icc a b, HasDerivAt y (g t) t) :
    |y b - y a| ≤ ∫ t in a..b, |g t| := by
  have hftc : (∫ t in a..b, g t) = y b - y a := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro t ht
      rw [Set.uIcc_of_le hab] at ht
      exact hy t ht
    · exact hgc.intervalIntegrable a b
  rw [← hftc]
  exact intervalIntegral.abs_integral_le_integral_abs hab

/-! ## Pulse integral bounds (lem:pulse-integrals) — P3, PROVED -/

private theorem intInt (f : ℝ → ℝ) (hf : Continuous f) (u v : ℝ) :
    IntervalIntegrable f MeasureTheory.volume u v :=
  hf.intervalIntegrable u v

/-- Active-half lower bound for the z-channel pulse:
`∫_{2πj}^{2πj+π} q_M ≥ (2π/3)(3/4)^M`. -/
theorem active_integral_lower (M : ℕ) (j : ℕ) :
    (2 * π / 3) * (3/4) ^ M ≤
      ∫ t in (2 * π * j)..(2 * π * j + π), qPulse M t := by
  have hπ := Real.pi_pos
  set a : ℝ := 2 * π * (j:ℝ) with ha
  have h1 : a ≤ a + π/6 := by linarith
  have h2 : a + π/6 ≤ a + 5*π/6 := by linarith
  have h3 : a + 5*π/6 ≤ a + π := by linarith
  have hint := intInt (qPulse M) (qPulse_continuous M)
  have e1 : (∫ t in a..(a+π/6), qPulse M t)
      + (∫ t in (a+π/6)..(a+π), qPulse M t)
      = ∫ t in a..(a+π), qPulse M t :=
    intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _)
  have e2 : (∫ t in (a+π/6)..(a+5*π/6), qPulse M t)
      + (∫ t in (a+5*π/6)..(a+π), qPulse M t)
      = ∫ t in (a+π/6)..(a+π), qPulse M t :=
    intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _)
  have hn1 : 0 ≤ ∫ t in a..(a+π/6), qPulse M t :=
    intervalIntegral.integral_nonneg h1 (fun t _ => qPulse_nonneg M t)
  have hn3 : 0 ≤ ∫ t in (a+5*π/6)..(a+π), qPulse M t :=
    intervalIntegral.integral_nonneg h3 (fun t _ => qPulse_nonneg M t)
  have hmid : (2*π/3) * (3/4:ℝ)^M ≤ ∫ t in (a+π/6)..(a+5*π/6), qPulse M t := by
    have hconst : (∫ _t in (a+π/6)..(a+5*π/6), ((3:ℝ)/4)^M)
        = (2*π/3) * (3/4:ℝ)^M := by
      rw [intervalIntegral.integral_const, smul_eq_mul]
      congr 1
      ring
    rw [← hconst]
    apply intervalIntegral.integral_mono_on h2
      _root_.intervalIntegrable_const (hint _ _)
    intro t ht
    apply qPulse_ge_active
    exact sin_window_ge j (by simpa [ha] using ht.1) (by simpa [ha] using ht.2)
  linarith [e1, e2, hn1, hn3, hmid]

/-- Passive-half leakage upper bound for the z-channel pulse:
`∫_{2πj+π}^{2πj+2π} q_M ≤ π (1/2)^M`. -/
theorem inactive_integral_upper (M : ℕ) (j : ℕ) :
    (∫ t in (2 * π * j + π)..(2 * π * j + 2 * π), qPulse M t)
      ≤ π * (1/2) ^ M := by
  have hπ := Real.pi_pos
  have hint := intInt (qPulse M) (qPulse_continuous M)
  have hconst : (∫ _t in (2*π*(j:ℝ) + π)..(2*π*(j:ℝ) + 2*π), ((1:ℝ)/2)^M)
      = π * (1/2:ℝ)^M := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
    congr 1
    ring
  rw [← hconst]
  apply intervalIntegral.integral_mono_on (by linarith)
    (hint _ _) _root_.intervalIntegrable_const
  intro t ht
  exact qPulse_le_offphase (sin_window_nonpos j ht.1 ht.2)

/-- Active-half lower bound for the u-channel pulse (the cycle's
passive half is the u-channel's active half) — R2#3. -/
theorem r_active_integral_lower (M : ℕ) (j : ℕ) :
    (2 * π / 3) * (3/4) ^ M ≤
      ∫ t in (2 * π * j + π)..(2 * π * j + 2 * π), rPulse M t := by
  have hπ := Real.pi_pos
  set a : ℝ := 2 * π * (j:ℝ) with ha
  have h1 : a + π ≤ a + 7*π/6 := by linarith
  have h2 : a + 7*π/6 ≤ a + 11*π/6 := by linarith
  have h3 : a + 11*π/6 ≤ a + 2*π := by linarith
  have hint := intInt (rPulse M) (rPulse_continuous M)
  have e1 : (∫ t in (a+π)..(a+7*π/6), rPulse M t)
      + (∫ t in (a+7*π/6)..(a+2*π), rPulse M t)
      = ∫ t in (a+π)..(a+2*π), rPulse M t :=
    intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _)
  have e2 : (∫ t in (a+7*π/6)..(a+11*π/6), rPulse M t)
      + (∫ t in (a+11*π/6)..(a+2*π), rPulse M t)
      = ∫ t in (a+7*π/6)..(a+2*π), rPulse M t :=
    intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _)
  have hn1 : 0 ≤ ∫ t in (a+π)..(a+7*π/6), rPulse M t :=
    intervalIntegral.integral_nonneg h1 (fun t _ => rPulse_nonneg M t)
  have hn3 : 0 ≤ ∫ t in (a+11*π/6)..(a+2*π), rPulse M t :=
    intervalIntegral.integral_nonneg h3 (fun t _ => rPulse_nonneg M t)
  have hmid : (2*π/3) * (3/4:ℝ)^M ≤ ∫ t in (a+7*π/6)..(a+11*π/6), rPulse M t := by
    have hconst : (∫ _t in (a+7*π/6)..(a+11*π/6), ((3:ℝ)/4)^M)
        = (2*π/3) * (3/4:ℝ)^M := by
      rw [intervalIntegral.integral_const, smul_eq_mul]
      congr 1
      ring
    rw [← hconst]
    apply intervalIntegral.integral_mono_on h2
      _root_.intervalIntegrable_const (hint _ _)
    intro t ht
    apply rPulse_ge_active
    exact sin_window_le_neg_half j (by simpa [ha] using ht.1)
      (by simpa [ha] using ht.2)
  linarith [e1, e2, hn1, hn3, hmid]

/-- Leakage upper bound for the u-channel pulse on the cycle's active
half — R2#3. -/
theorem r_inactive_integral_upper (M : ℕ) (j : ℕ) :
    (∫ t in (2 * π * j)..(2 * π * j + π), rPulse M t)
      ≤ π * (1/2) ^ M := by
  have hπ := Real.pi_pos
  have hint := intInt (rPulse M) (rPulse_continuous M)
  have hconst : (∫ _t in (2*π*(j:ℝ))..(2*π*(j:ℝ) + π), ((1:ℝ)/2)^M)
      = π * (1/2:ℝ)^M := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
    congr 1
    ring
  rw [← hconst]
  apply intervalIntegral.integral_mono_on (by linarith)
    (hint _ _) _root_.intervalIntegrable_const
  intro t ht
  exact rPulse_le_offphase (sin_window_nonneg j ht.1 ht.2)

/-! ## The per-cycle recurrence and all-time tracking -/

/-- Per-cycle contraction and leakage constants.  `trackingKappa` is
the residual factor after one active-half targeting (from P1 +
`active_integral_lower`).  `trackingChi` is an explicit UPPER BOUND
for the paper's leakage constant `χ(A,M) = 1 - exp(-A b_M)` (R2#4
honesty note: not the paper's expression verbatim; since
`1 - exp(-Ab) ≤ Ab ≤ A·π·2^{-M} ≤ trackingChi`, stating the cascade
with this bound only strengthens the hypotheses, and feasibility
still closes because `trackingChi → 0`).  The factor `2π` (vs the
half-window length `π`) deliberately absorbs the radius-vs-diameter
factor 2 in the recurrence derivation: see `MovingBox`. -/
noncomputable def trackingKappa (A : ℝ) (M : ℕ) : ℝ :=
  Real.exp (-(A * ((2 * π / 3) * (3/4) ^ M)))

noncomputable def trackingChi (A : ℝ) (M : ℕ) : ℝ :=
  A * (1/2) ^ M * (2 * π)

/-- The encoded discrete orbit. -/
def orbitPoint {Conf : Type} [Primcodable Conf]
    (Mch : DiscreteMachine Conf) {d : ℕ} (E : LatticeEncoding Mch d)
    (w j : ℕ) : Fin d → ℝ :=
  E.enc (Mch.step^[j] (Mch.init w))

/-- Moving-box certificate for one cycle (paper
lem:bounded-working-volume / thm:all-time-tracking hypothesis block,
main.tex:872-875): `x_j`, `x_{j+1}`, and all values `z(t), u(t),
F(u(t))` attained in cycle `C_j` lie within `D_K` of `x_j`
(R1#6: `x_{j+1}` and `F(u(t))` included).

R2#2 rebuttal — RADIUS normalisation, not diameter: pairwise gaps
like `|F(u) - z|` are then `≤ 2 D_K`, and the recurrence constants
still close because `trackingChi` carries the full-period factor
`2π` while each hold phase has length `π`: hold drift
`≤ A·2^{-M}·(2 D_K)·π = trackingChi·D_K`.  Full closure arithmetic:
HANDOFF-BGP.md, "P4 proof plan" (both channels end at
`≤ 2κe + 2κD_K + (κχ+χ)D_K + ηstep ≤` the stated bound via `κ ≤ 1`). -/
def MovingBox {Conf : Type} [Primcodable Conf]
    {Mch : DiscreteMachine Conf} {d : ℕ} {E : LatticeEncoding Mch d}
    (S : RobustRealExtension Mch d E)
    {A : ℝ} {M : ℕ} {w : ℕ}
    (sol : IteratorSol d S.evalF A M (orbitPoint Mch E w 0))
    (D_K : ℝ) : Prop :=
  ∀ (j : ℕ) (t : ℝ), t ∈ Set.Icc (2*π*j) (2*π*(j+1)) →
    (∀ i, |orbitPoint Mch E w (j+1) i - orbitPoint Mch E w j i| ≤ D_K) ∧
    (∀ i, |sol.z t i - orbitPoint Mch E w j i| ≤ D_K) ∧
    (∀ i, |sol.u t i - orbitPoint Mch E w j i| ≤ D_K) ∧
    (∀ i, |S.evalF (sol.u t) i - orbitPoint Mch E w j i| ≤ D_K)

/-- **P4, perturbation recurrence** (lem:perturbation-recurrence,
paper constants per main.tex:790): one cycle maps sampling error `e`
to at most `2κ e + 2κ D_K + 2χ D_K + ηstep`, provided the snap input
stays in the snap basin (`e + χ D_K ≤ r₀`). -/
theorem perturbation_recurrence
    {Conf : Type} [Primcodable Conf]
    (Mch : DiscreteMachine Conf) (d : ℕ) (E : LatticeEncoding Mch d)
    (S : RobustRealExtension Mch d E)
    (A : ℝ) (hA : 0 < A) (M : ℕ) (w : ℕ)
    (sol : IteratorSol d S.evalF A M (orbitPoint Mch E w 0))
    (D_K : ℝ) (hD : 0 < D_K) (hbox : MovingBox S sol D_K)
    (j : ℕ) (e : ℝ) (he0 : 0 ≤ e)
    (he : ∀ i, |sol.z (2*π*j) i - orbitPoint Mch E w j i| ≤ e ∧
               |sol.u (2*π*j) i - orbitPoint Mch E w j i| ≤ e)
    (hsnap : e + trackingChi A M * D_K ≤ (S.r₀ : ℝ)) :
    ∀ i, |sol.z (2*π*(j+1)) i - orbitPoint Mch E w (j+1) i| ≤
          2 * trackingKappa A M * e + 2 * trackingKappa A M * D_K
            + 2 * trackingChi A M * D_K + (S.ηstep : ℝ) ∧
         |sol.u (2*π*(j+1)) i - orbitPoint Mch E w (j+1) i| ≤
          2 * trackingKappa A M * e + 2 * trackingKappa A M * D_K
            + 2 * trackingChi A M * D_K + (S.ηstep : ℝ) := by
  intro i
  let a : ℝ := 2 * π * (j : ℝ)
  let m : ℝ := 2 * π * (j : ℝ) + π
  let b : ℝ := 2 * π * (j : ℝ) + 2 * π
  let xj : Fin d → ℝ := orbitPoint Mch E w j
  let xnext : Fin d → ℝ := orbitPoint Mch E w (j + 1)
  have hπ : 0 < π := Real.pi_pos
  have ha0 : (0:ℝ) ≤ a :=
    mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) (Nat.cast_nonneg j)
  have hamb : a ≤ m := by dsimp [a, m]; linarith
  have hmb : m ≤ b := by dsimp [a, m, b]; linarith [hπ]
  have hab : a ≤ b := le_trans hamb hmb
  have hb_eq : b = 2 * π * ((j : ℝ) + 1) := by dsimp [b]; ring
  have ha_eq : a = 2 * π * j := rfl
  have hm_eq : m = 2 * π * j + π := rfl
  have hcycle_m : m ∈ Set.Icc (2*π*j) (2*π*(j+1)) := by
    constructor
    · simpa [a, m] using hamb
    · simpa [← hb_eq] using hmb
  have hxnext_box : ∀ k, |xnext k - xj k| ≤ D_K := (hbox j m hcycle_m).1
  have hz_cont : ∀ k, Continuous fun t => sol.z t k := fun k => sol.cont_z k
  have hu_cont : ∀ k, Continuous fun t => sol.u t k := fun k => sol.cont_u k
  have hEval_cont : ∀ k, Continuous fun t => S.evalF (sol.u t) k := fun k => by
    have hsolu : Continuous fun t => sol.u t := continuous_pi fun l => hu_cont l
    unfold RobustRealExtension.evalF
    convert
      (MvPolynomial.continuous_eval (p := MvPolynomial.map (algebraMap ℚ ℝ) (S.F k))).comp hsolu
      using 1
    ext t
    exact MvPolynomial.eval₂_eq_eval_map (algebraMap ℚ ℝ) (sol.u t) (S.F k)
  have hχ_nonneg : 0 ≤ trackingChi A M := by
    unfold trackingChi
    positivity
  have hκ_nonneg : 0 ≤ trackingKappa A M := by
    unfold trackingKappa
    exact (Real.exp_pos _).le
  have hκ_le_one : trackingKappa A M ≤ 1 := by
    unfold trackingKappa
    apply Real.exp_le_one_iff.mpr
    have : 0 ≤ (2 * π / 3) * (3 / 4 : ℝ) ^ M := by positivity
    nlinarith
  have hη_nonneg : 0 ≤ (S.ηstep : ℝ) := by exact_mod_cast S.ηstep_pos.le
  have hD_nonneg : 0 ≤ D_K := hD.le
  have hχD_nonneg : 0 ≤ trackingChi A M * D_K := mul_nonneg hχ_nonneg hD_nonneg
  have hold_u_first :
      ∀ t ∈ Set.Icc a m, ∀ k, |sol.u t k - sol.u a k| ≤ trackingChi A M * D_K := by
    intro t ht k
    have hat : a ≤ t := ht.1
    have htm : t ≤ m := ht.2
    have hderiv : ∀ s ∈ Set.Icc a t,
        HasDerivAt (fun τ => sol.u τ k)
          (A * rPulse M s * (sol.z s k - sol.u s k)) s := by
      intro s hs
      exact sol.ode_u s (le_trans ha0 hs.1) k
    have hbound : ∀ s ∈ Set.Icc a t,
        |A * rPulse M s * (sol.z s k - sol.u s k)|
          ≤ A * (1/2) ^ M * (2 * D_K) := by
      intro s hs
      have hs_cycle : s ∈ Set.Icc (2*π*j) (2*π*(j+1)) := by
        simpa [a, ← hb_eq] using
          (⟨hs.1, le_trans hs.2 (le_trans ht.2 hmb)⟩ :
            s ∈ Set.Icc a b)
      have hzD := (hbox j s hs_cycle).2.1 k
      have huD := (hbox j s hs_cycle).2.2.1 k
      have hzu : |sol.z s k - sol.u s k| ≤ 2 * D_K := by
        calc
          |sol.z s k - sol.u s k|
              = |(sol.z s k - xj k) - (sol.u s k - xj k)| := by ring_nf
          _ ≤ |sol.z s k - xj k| + |sol.u s k - xj k| := by
            simpa [abs_sub_comm] using
              abs_sub_le (sol.z s k) (xj k) (sol.u s k)
          _ ≤ D_K + D_K := add_le_add hzD huD
          _ = 2 * D_K := by ring
      have hrle : rPulse M s ≤ (1/2 : ℝ) ^ M := by
        apply rPulse_le_offphase
        apply sin_window_nonneg j
        · simpa [a] using hs_cycle.1
        · have : s ≤ 2 * π * j + π := by
            rw [← hm_eq]
            exact le_trans hs.2 htm
          simpa using this
      have hrnn : 0 ≤ rPulse M s := rPulse_nonneg M s
      calc
        |A * rPulse M s * (sol.z s k - sol.u s k)|
            = A * rPulse M s * |sol.z s k - sol.u s k| := by
              rw [abs_mul, abs_mul, abs_of_pos hA, abs_of_nonneg hrnn]
        _ ≤ A * ((1/2 : ℝ) ^ M) * (2 * D_K) := by
              have htmp := mul_le_mul hrle hzu (abs_nonneg _)
                (pow_nonneg (by norm_num) M)
              convert mul_le_mul_of_nonneg_left htmp hA.le using 1 <;> ring
    have hhold := hold_bound (fun τ => sol.u τ k)
      (fun s => A * rPulse M s * (sol.z s k - sol.u s k))
      (A * (1/2) ^ M * (2 * D_K)) a t hat hderiv hbound
    have hlen : t - a ≤ π := by dsimp [a, m] at ht; linarith
    calc
      |sol.u t k - sol.u a k|
          ≤ (A * (1/2) ^ M * (2 * D_K)) * (t - a) := hhold
      _ ≤ (A * (1/2) ^ M * (2 * D_K)) * π := by
            have hcoef : 0 ≤ A * (1/2 : ℝ) ^ M * (2 * D_K) := by positivity
            exact mul_le_mul_of_nonneg_left hlen hcoef
      _ = trackingChi A M * D_K := by
            unfold trackingChi
            ring
  have hu_first_near : ∀ t ∈ Set.Icc a m, ∀ k, |sol.u t k - xj k| ≤ e + trackingChi A M * D_K := by
    intro t ht k
    have hstart := (he k).2
    rw [← ha_eq] at hstart
    have hhold := hold_u_first t ht k
    calc
      |sol.u t k - xj k|
          = |(sol.u t k - sol.u a k) + (sol.u a k - xj k)| := by ring_nf
      _ ≤ |sol.u t k - sol.u a k| + |sol.u a k - xj k| := abs_add_le _ _
      _ ≤ trackingChi A M * D_K + e := add_le_add hhold hstart
      _ = e + trackingChi A M * D_K := by ring
  have hsnap_first : ∀ t ∈ Set.Icc a m, ∀ k, |S.evalF (sol.u t) k - xnext k| ≤ (S.ηstep : ℝ) := by
    intro t ht k
    have hnear : ∀ l, |sol.u t l - E.enc (Mch.step^[j] (Mch.init w)) l| ≤ (S.r₀ : ℝ) := by
      intro l
      exact le_trans (hu_first_near t ht l) hsnap
    simpa [RobustRealExtension.evalF, orbitPoint, xnext, Function.iterate_succ_apply'] using
      S.snap (Mch.step^[j] (Mch.init w)) (sol.u t) hnear k
  have hz_mid :
      |sol.z m i - xnext i| ≤ trackingKappa A M * (e + D_K) + (S.ηstep : ℝ) := by
    have hδ : ∀ t ∈ Set.Icc a m, |S.evalF (sol.u t) i - xnext i| ≤ (S.ηstep : ℝ) :=
      fun t ht => hsnap_first t ht i
    have hderiv : ∀ t ∈ Set.Icc a m,
        HasDerivAt (fun τ => sol.z τ i)
          (A * qPulse M t * (S.evalF (sol.u t) i - sol.z t i)) t := by
      intro t ht
      exact sol.ode_z t (le_trans ha0 ht.1) i
    have htarget := targeting_bound A hA (qPulse M)
      (fun t => S.evalF (sol.u t) i) (fun t => sol.z t i) a m hamb
      (qPulse_continuous M) (fun t ht => qPulse_nonneg M t)
      (hEval_cont i) (xnext i) (S.ηstep : ℝ) hδ hderiv
    have hint := active_integral_lower M j
    have hInt : (2 * π / 3) * (3/4 : ℝ) ^ M ≤ ∫ t in a..m, qPulse M t := by
      simpa [a, m] using hint
    have hcoef :
        Real.exp (-(A * ∫ t in a..m, qPulse M t)) ≤ trackingKappa A M := by
      unfold trackingKappa
      apply Real.exp_le_exp.mpr
      nlinarith [hA, hInt]
    have hstartz := (he i).1
    rw [← ha_eq] at hstartz
    have hxgap := hxnext_box i
    have hza : |sol.z a i - xnext i| ≤ e + D_K := by
      calc
        |sol.z a i - xnext i|
            = |(sol.z a i - xj i) - (xnext i - xj i)| := by ring_nf
        _ ≤ |sol.z a i - xj i| + |xnext i - xj i| := by
          simpa [abs_sub_comm] using
            abs_sub_le (sol.z a i) (xj i) (xnext i)
        _ ≤ e + D_K := add_le_add hstartz hxgap
    have hmul :
        Real.exp (-(A * ∫ t in a..m, qPulse M t)) * |sol.z a i - xnext i|
          ≤ trackingKappa A M * (e + D_K) := by
      exact mul_le_mul hcoef hza (abs_nonneg _) hκ_nonneg
    exact le_trans htarget (by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_right hmul (S.ηstep : ℝ))
  have hold_z_second :
      ∀ t ∈ Set.Icc m b, ∀ k, |sol.z t k - sol.z m k| ≤ trackingChi A M * D_K := by
    intro t ht k
    have hmt : m ≤ t := ht.1
    have htb : t ≤ b := ht.2
    have hderiv : ∀ s ∈ Set.Icc m t,
        HasDerivAt (fun τ => sol.z τ k)
          (A * qPulse M s * (S.evalF (sol.u s) k - sol.z s k)) s := by
      intro s hs
      exact sol.ode_z s (le_trans (le_trans ha0 hamb) hs.1) k
    have hbound : ∀ s ∈ Set.Icc m t,
        |A * qPulse M s * (S.evalF (sol.u s) k - sol.z s k)|
          ≤ A * (1/2) ^ M * (2 * D_K) := by
      intro s hs
      have hs_cycle : s ∈ Set.Icc (2*π*j) (2*π*(j+1)) := by
        simpa [a, ← hb_eq] using
          (⟨le_trans hamb hs.1, le_trans hs.2 htb⟩ :
            s ∈ Set.Icc a b)
      have hFD := (hbox j s hs_cycle).2.2.2 k
      have hzD := (hbox j s hs_cycle).2.1 k
      have hFz : |S.evalF (sol.u s) k - sol.z s k| ≤ 2 * D_K := by
        calc
          |S.evalF (sol.u s) k - sol.z s k|
              = |(S.evalF (sol.u s) k - xj k) - (sol.z s k - xj k)| := by ring_nf
          _ ≤ |S.evalF (sol.u s) k - xj k| + |sol.z s k - xj k| := by
            simpa [abs_sub_comm] using
              abs_sub_le (S.evalF (sol.u s) k) (xj k) (sol.z s k)
          _ ≤ D_K + D_K := add_le_add hFD hzD
          _ = 2 * D_K := by ring
      have hqle : qPulse M s ≤ (1/2 : ℝ) ^ M := by
        apply qPulse_le_offphase
        apply sin_window_nonpos j
        · have : 2 * π * j + π ≤ s := by
            rw [← hm_eq]
            exact hs.1
          simpa using this
        · simpa [← hb_eq] using hs_cycle.2
      have hqnn : 0 ≤ qPulse M s := qPulse_nonneg M s
      calc
        |A * qPulse M s * (S.evalF (sol.u s) k - sol.z s k)|
            = A * qPulse M s * |S.evalF (sol.u s) k - sol.z s k| := by
              rw [abs_mul, abs_mul, abs_of_pos hA, abs_of_nonneg hqnn]
        _ ≤ A * ((1/2 : ℝ) ^ M) * (2 * D_K) := by
              have htmp := mul_le_mul hqle hFz (abs_nonneg _)
                (pow_nonneg (by norm_num) M)
              convert mul_le_mul_of_nonneg_left htmp hA.le using 1 <;> ring
    have hhold := hold_bound (fun τ => sol.z τ k)
      (fun s => A * qPulse M s * (S.evalF (sol.u s) k - sol.z s k))
      (A * (1/2) ^ M * (2 * D_K)) m t hmt hderiv hbound
    have hlen : t - m ≤ π := by dsimp [m, b] at ht; linarith
    calc
      |sol.z t k - sol.z m k|
          ≤ (A * (1/2) ^ M * (2 * D_K)) * (t - m) := hhold
      _ ≤ (A * (1/2) ^ M * (2 * D_K)) * π := by
            have hcoef : 0 ≤ A * (1/2 : ℝ) ^ M * (2 * D_K) := by positivity
            exact mul_le_mul_of_nonneg_left hlen hcoef
      _ = trackingChi A M * D_K := by
            unfold trackingChi
            ring
  have hz_second_near : ∀ t ∈ Set.Icc m b, ∀ k,
      |sol.z t k - xnext k| ≤
        trackingKappa A M * (e + D_K) + (S.ηstep : ℝ) + trackingChi A M * D_K := by
    intro t ht k
    have hmidk : |sol.z m k - xnext k| ≤
        trackingKappa A M * (e + D_K) + (S.ηstep : ℝ) := by
      -- same first-half targeting estimate as `hz_mid`, for coordinate `k`
      have hδ : ∀ s ∈ Set.Icc a m, |S.evalF (sol.u s) k - xnext k| ≤ (S.ηstep : ℝ) :=
        fun s hs => hsnap_first s hs k
      have hderiv : ∀ s ∈ Set.Icc a m,
          HasDerivAt (fun τ => sol.z τ k)
            (A * qPulse M s * (S.evalF (sol.u s) k - sol.z s k)) s := by
        intro s hs
        exact sol.ode_z s (le_trans ha0 hs.1) k
      have htarget := targeting_bound A hA (qPulse M)
        (fun s => S.evalF (sol.u s) k) (fun s => sol.z s k) a m hamb
        (qPulse_continuous M) (fun s hs => qPulse_nonneg M s)
        (hEval_cont k) (xnext k) (S.ηstep : ℝ) hδ hderiv
      have hInt : (2 * π / 3) * (3/4 : ℝ) ^ M ≤ ∫ s in a..m, qPulse M s := by
        simpa [a, m] using active_integral_lower M j
      have hcoef :
          Real.exp (-(A * ∫ s in a..m, qPulse M s)) ≤ trackingKappa A M := by
        unfold trackingKappa
        apply Real.exp_le_exp.mpr
        nlinarith [hA, hInt]
      have hstartz := (he k).1
      rw [← ha_eq] at hstartz
      have hxgap := hxnext_box k
      have hza : |sol.z a k - xnext k| ≤ e + D_K := by
        calc
          |sol.z a k - xnext k|
              = |(sol.z a k - xj k) - (xnext k - xj k)| := by ring_nf
          _ ≤ |sol.z a k - xj k| + |xnext k - xj k| := by
            simpa [abs_sub_comm] using
              abs_sub_le (sol.z a k) (xj k) (xnext k)
          _ ≤ e + D_K := add_le_add hstartz hxgap
      have hmul :
          Real.exp (-(A * ∫ s in a..m, qPulse M s)) * |sol.z a k - xnext k|
            ≤ trackingKappa A M * (e + D_K) := by
        exact mul_le_mul hcoef hza (abs_nonneg _) hκ_nonneg
      exact le_trans htarget (by
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_right hmul (S.ηstep : ℝ))
    have hhold := hold_z_second t ht k
    calc
      |sol.z t k - xnext k|
          = |(sol.z t k - sol.z m k) + (sol.z m k - xnext k)| := by ring_nf
      _ ≤ |sol.z t k - sol.z m k| + |sol.z m k - xnext k| := abs_add_le _ _
      _ ≤ trackingChi A M * D_K +
          (trackingKappa A M * (e + D_K) + (S.ηstep : ℝ)) := add_le_add hhold hmidk
      _ = trackingKappa A M * (e + D_K) + (S.ηstep : ℝ) + trackingChi A M * D_K := by ring
  have hz_b_pre :
      |sol.z b i - xnext i| ≤
        trackingKappa A M * (e + D_K) + (S.ηstep : ℝ) + trackingChi A M * D_K :=
    hz_second_near b (Set.right_mem_Icc.mpr hmb) i
  have hu_m_xnext : ∀ k, |sol.u m k - xnext k| ≤ e + trackingChi A M * D_K + D_K := by
    intro k
    have hu_near := hu_first_near m (Set.right_mem_Icc.mpr hamb) k
    have hxgap := hxnext_box k
    calc
      |sol.u m k - xnext k|
          = |(sol.u m k - xj k) - (xnext k - xj k)| := by ring_nf
      _ ≤ |sol.u m k - xj k| + |xnext k - xj k| := by
        simpa [abs_sub_comm] using
          abs_sub_le (sol.u m k) (xj k) (xnext k)
      _ ≤ (e + trackingChi A M * D_K) + D_K := add_le_add hu_near hxgap
      _ = e + trackingChi A M * D_K + D_K := by ring
  have hu_b_pre :
      |sol.u b i - xnext i| ≤
        trackingKappa A M * (e + trackingChi A M * D_K + D_K) +
          (trackingKappa A M * (e + D_K) + (S.ηstep : ℝ) + trackingChi A M * D_K) := by
    have hδ : ∀ t ∈ Set.Icc m b,
        |sol.z t i - xnext i| ≤
          trackingKappa A M * (e + D_K) + (S.ηstep : ℝ) + trackingChi A M * D_K :=
      fun t ht => hz_second_near t ht i
    have hderiv : ∀ t ∈ Set.Icc m b,
        HasDerivAt (fun τ => sol.u τ i)
          (A * rPulse M t * (sol.z t i - sol.u t i)) t := by
      intro t ht
      exact sol.ode_u t (le_trans (le_trans ha0 hamb) ht.1) i
    have htarget := targeting_bound A hA (rPulse M)
      (fun t => sol.z t i) (fun t => sol.u t i) m b hmb
      (rPulse_continuous M) (fun t ht => rPulse_nonneg M t)
      (hz_cont i) (xnext i)
      (trackingKappa A M * (e + D_K) + (S.ηstep : ℝ) + trackingChi A M * D_K)
      hδ hderiv
    have hInt : (2 * π / 3) * (3/4 : ℝ) ^ M ≤ ∫ t in m..b, rPulse M t := by
      simpa [m, b] using r_active_integral_lower M j
    have hcoef :
        Real.exp (-(A * ∫ t in m..b, rPulse M t)) ≤ trackingKappa A M := by
      unfold trackingKappa
      apply Real.exp_le_exp.mpr
      nlinarith [hA, hInt]
    have hmul :
        Real.exp (-(A * ∫ t in m..b, rPulse M t)) * |sol.u m i - xnext i|
          ≤ trackingKappa A M * (e + trackingChi A M * D_K + D_K) := by
      exact mul_le_mul hcoef (hu_m_xnext i) (abs_nonneg _) hκ_nonneg
    exact le_trans htarget (by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_right hmul
          (trackingKappa A M * (e + D_K) + (S.ηstep : ℝ) + trackingChi A M * D_K))
  constructor
  · change |sol.z (2 * π * ((j : ℝ) + 1)) i - xnext i| ≤
      2 * trackingKappa A M * e + 2 * trackingKappa A M * D_K
        + 2 * trackingChi A M * D_K + (S.ηstep : ℝ)
    have hb' : 2 * π * ((j : ℝ) + 1) = b := by dsimp [b]; ring
    rw [hb']
    calc
      |sol.z b i - xnext i|
          ≤ trackingKappa A M * (e + D_K) + (S.ηstep : ℝ) + trackingChi A M * D_K := hz_b_pre
      _ ≤ 2 * trackingKappa A M * e + 2 * trackingKappa A M * D_K
          + 2 * trackingChi A M * D_K + (S.ηstep : ℝ) := by
            nlinarith [hκ_nonneg, hχD_nonneg, he0, hD_nonneg]
  · change |sol.u (2 * π * ((j : ℝ) + 1)) i - xnext i| ≤
      2 * trackingKappa A M * e + 2 * trackingKappa A M * D_K
        + 2 * trackingChi A M * D_K + (S.ηstep : ℝ)
    have hb' : 2 * π * ((j : ℝ) + 1) = b := by dsimp [b]; ring
    rw [hb']
    calc
      |sol.u b i - xnext i|
          ≤ trackingKappa A M * (e + trackingChi A M * D_K + D_K) +
            (trackingKappa A M * (e + D_K) + (S.ηstep : ℝ) + trackingChi A M * D_K) := hu_b_pre
      _ ≤ 2 * trackingKappa A M * e + 2 * trackingKappa A M * D_K
          + 2 * trackingChi A M * D_K + (S.ηstep : ℝ) := by
            nlinarith [hκ_le_one, hκ_nonneg, hχD_nonneg, he0, hD_nonneg]

/-- **P5, all-time tracking** (thm:all-time-tracking, cascade per
main.tex:879): under `2κ < 1`, `2κ D_K + 2χ D_K + ηstep ≤ η (1 − 2κ)`,
and `η + χ D_K ≤ r₀`, the iterator tracks the discrete orbit within
`η` at every sampling time, with no time horizon.  Induction over P4:
`e ≤ η ⟹ 2κη + 2κD + 2χD + ηstep ≤ 2κη + η(1−2κ) = η`. -/
theorem all_time_tracking
    {Conf : Type} [Primcodable Conf]
    (Mch : DiscreteMachine Conf) (d : ℕ) (E : LatticeEncoding Mch d)
    (S : RobustRealExtension Mch d E)
    (A : ℝ) (hA : 0 < A) (M : ℕ) (w : ℕ)
    (sol : IteratorSol d S.evalF A M (orbitPoint Mch E w 0))
    (D_K : ℝ) (hD : 0 < D_K) (hbox : MovingBox S sol D_K)
    (η : ℝ) (hη : 0 < η)
    (hcasc₀ : 2 * trackingKappa A M < 1)
    (hcasc₁ : 2 * trackingKappa A M * D_K + 2 * trackingChi A M * D_K
        + (S.ηstep : ℝ) ≤ η * (1 - 2 * trackingKappa A M))
    (hcasc₂ : η + trackingChi A M * D_K ≤ (S.r₀ : ℝ)) :
    ∀ j : ℕ, ∀ i,
      |sol.z (2*π*j) i - orbitPoint Mch E w j i| ≤ η ∧
      |sol.u (2*π*j) i - orbitPoint Mch E w j i| ≤ η := by
  intro j
  induction j with
  | zero =>
    intro i
    have h0 : 2*π*((0:ℕ):ℝ) = 0 := by norm_num
    rw [h0, sol.init_z, sol.init_u]
    constructor <;> · rw [sub_self, abs_zero]; exact hη.le
  | succ k ih =>
    intro i
    have hrec := perturbation_recurrence Mch d E S A hA M w sol D_K hD hbox
      k η hη.le ih hcasc₂
    obtain ⟨hz, hu⟩ := hrec i
    have harith : 2 * trackingKappa A M * η + 2 * trackingKappa A M * D_K
        + 2 * trackingChi A M * D_K + (S.ηstep : ℝ) ≤ η := by
      nlinarith [hcasc₁]
    have hcast : ((k+1:ℕ):ℝ) = (k:ℝ) + 1 := by push_cast; ring
    rw [hcast]
    exact ⟨le_trans hz harith, le_trans hu harith⟩

private theorem active_integral_lower_to (M : ℕ) (j : ℕ) {t : ℝ}
    (hlo : 2 * π * j + 5 * π / 6 ≤ t)
    (hhi : t ≤ 2 * π * j + π) :
    (2 * π / 3) * (3/4) ^ M ≤
      ∫ s in (2 * π * j)..t, qPulse M s := by
  have hπ := Real.pi_pos
  set a : ℝ := 2 * π * (j:ℝ) with ha
  have h1 : a ≤ a + π/6 := by linarith
  have h2 : a + π/6 ≤ a + 5*π/6 := by linarith
  have h5t : a + 5*π/6 ≤ t := by simpa [ha] using hlo
  have h6t : a + π/6 ≤ t := le_trans h2 h5t
  have hat : a ≤ t := le_trans h1 h6t
  have hint := intInt (qPulse M) (qPulse_continuous M)
  have e1 : (∫ s in a..(a+π/6), qPulse M s)
      + (∫ s in (a+π/6)..t, qPulse M s)
      = ∫ s in a..t, qPulse M s :=
    intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _)
  have e2 : (∫ s in (a+π/6)..(a+5*π/6), qPulse M s)
      + (∫ s in (a+5*π/6)..t, qPulse M s)
      = ∫ s in (a+π/6)..t, qPulse M s :=
    intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _)
  have hn1 : 0 ≤ ∫ s in a..(a+π/6), qPulse M s :=
    intervalIntegral.integral_nonneg h1 (fun s _ => qPulse_nonneg M s)
  have hn3 : 0 ≤ ∫ s in (a+5*π/6)..t, qPulse M s :=
    intervalIntegral.integral_nonneg h5t (fun s _ => qPulse_nonneg M s)
  have hmid : (2*π/3) * (3/4:ℝ)^M ≤
      ∫ s in (a+π/6)..(a+5*π/6), qPulse M s := by
    have hconst : (∫ _s in (a+π/6)..(a+5*π/6), ((3:ℝ)/4)^M)
        = (2*π/3) * (3/4:ℝ)^M := by
      rw [intervalIntegral.integral_const, smul_eq_mul]
      congr 1
      ring
    rw [← hconst]
    apply intervalIntegral.integral_mono_on h2
      _root_.intervalIntegrable_const (hint _ _)
    intro s hs
    apply qPulse_ge_active
    exact sin_window_ge j (by simpa [ha] using hs.1) (by simpa [ha] using hs.2)
  linarith [e1, e2, hn1, hn3, hmid]

/-- **P4b (R3#6), stable-window tracking** (cor:stable-window-tracking):
under the all-time-tracking hypotheses, on the mid-cycle stable window
`[2πj + 5π/6, 2πj + 7π/6]` the z-channel stays within
`κ(η + D_K) + ηstep + χ D_K` of the POST-transition configuration
`x_{j+1}` — the active-half contraction is complete by `5π/6` (the
active window `[π/6, 5π/6]` has been integrated) and only hold drift
accrues afterwards.  This is the Lean counterpart the latch lemma's
stable-window hypothesis needs; without it P9's hypotheses were not
jointly dischargeable (codex R3#6). -/
theorem stable_window_tracking
    {Conf : Type} [Primcodable Conf]
    (Mch : DiscreteMachine Conf) (d : ℕ) (E : LatticeEncoding Mch d)
    (S : RobustRealExtension Mch d E)
    (A : ℝ) (hA : 0 < A) (M : ℕ) (w : ℕ)
    (sol : IteratorSol d S.evalF A M (orbitPoint Mch E w 0))
    (D_K : ℝ) (hD : 0 < D_K) (hbox : MovingBox S sol D_K)
    (η : ℝ) (hη : 0 < η)
    (hcasc₀ : 2 * trackingKappa A M < 1)
    (hcasc₁ : 2 * trackingKappa A M * D_K + 2 * trackingChi A M * D_K
        + (S.ηstep : ℝ) ≤ η * (1 - 2 * trackingKappa A M))
    (hcasc₂ : η + trackingChi A M * D_K ≤ (S.r₀ : ℝ)) :
    ∀ j : ℕ, ∀ t ∈ Set.Icc (2*π*j + 5*π/6) (2*π*j + 7*π/6), ∀ i,
      |sol.z t i - orbitPoint Mch E w (j+1) i| ≤
        trackingKappa A M * (η + D_K) + (S.ηstep : ℝ)
          + trackingChi A M * D_K := by
  intro j t ht i
  let a : ℝ := 2 * π * (j : ℝ)
  let m : ℝ := 2 * π * (j : ℝ) + π
  let b : ℝ := 2 * π * (j : ℝ) + 2 * π
  let xj : Fin d → ℝ := orbitPoint Mch E w j
  let xnext : Fin d → ℝ := orbitPoint Mch E w (j + 1)
  have hπ : 0 < π := Real.pi_pos
  have ha0 : (0:ℝ) ≤ a :=
    mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) (Nat.cast_nonneg j)
  have hamb : a ≤ m := by dsimp [a, m]; linarith
  have hmb : m ≤ b := by dsimp [a, m, b]; linarith [hπ]
  have hb_eq : b = 2 * π * ((j : ℝ) + 1) := by dsimp [b]; ring
  have ha_eq : a = 2 * π * j := rfl
  have hm_eq : m = 2 * π * j + π := rfl
  have ht_low : a + 5 * π / 6 ≤ t := by simpa [a] using ht.1
  have ht_cycle_upper : t ≤ b := by
    have : t ≤ a + 7 * π / 6 := by simpa [a] using ht.2
    dsimp [a, b] at this ⊢
    linarith [hπ, this]
  have hcycle_a : a ∈ Set.Icc (2*π*j) (2*π*(j+1)) := by
    constructor
    · rfl
    · simpa [a, ← hb_eq] using (le_trans hamb hmb)
  have hxnext_box : ∀ k, |xnext k - xj k| ≤ D_K := (hbox j a hcycle_a).1
  have hz_cont : ∀ k, Continuous fun t => sol.z t k := fun k => sol.cont_z k
  have hu_cont : ∀ k, Continuous fun t => sol.u t k := fun k => sol.cont_u k
  have hEval_cont : ∀ k, Continuous fun t => S.evalF (sol.u t) k := fun k => by
    have hsolu : Continuous fun t => sol.u t := continuous_pi fun l => hu_cont l
    unfold RobustRealExtension.evalF
    convert
      (MvPolynomial.continuous_eval (p := MvPolynomial.map (algebraMap ℚ ℝ) (S.F k))).comp hsolu
      using 1
    ext t
    exact MvPolynomial.eval₂_eq_eval_map (algebraMap ℚ ℝ) (sol.u t) (S.F k)
  have hχ_nonneg : 0 ≤ trackingChi A M := by
    unfold trackingChi
    positivity
  have hκ_nonneg : 0 ≤ trackingKappa A M := by
    unfold trackingKappa
    exact (Real.exp_pos _).le
  have hD_nonneg : 0 ≤ D_K := hD.le
  have hχD_nonneg : 0 ≤ trackingChi A M * D_K := mul_nonneg hχ_nonneg hD_nonneg
  have hsample := all_time_tracking Mch d E S A hA M w sol D_K hD hbox
    η hη hcasc₀ hcasc₁ hcasc₂ j
  have hold_u_first :
      ∀ s ∈ Set.Icc a m, ∀ k, |sol.u s k - sol.u a k| ≤ trackingChi A M * D_K := by
    intro s hs k
    have has : a ≤ s := hs.1
    have hsm : s ≤ m := hs.2
    have hderiv : ∀ r ∈ Set.Icc a s,
        HasDerivAt (fun τ => sol.u τ k)
          (A * rPulse M r * (sol.z r k - sol.u r k)) r := by
      intro r hr
      exact sol.ode_u r (le_trans ha0 hr.1) k
    have hbound : ∀ r ∈ Set.Icc a s,
        |A * rPulse M r * (sol.z r k - sol.u r k)|
          ≤ A * (1/2) ^ M * (2 * D_K) := by
      intro r hr
      have hr_cycle : r ∈ Set.Icc (2*π*j) (2*π*(j+1)) := by
        simpa [a, ← hb_eq] using
          (⟨hr.1, le_trans hr.2 (le_trans hsm hmb)⟩ : r ∈ Set.Icc a b)
      have hzD := (hbox j r hr_cycle).2.1 k
      have huD := (hbox j r hr_cycle).2.2.1 k
      have hzu : |sol.z r k - sol.u r k| ≤ 2 * D_K := by
        calc
          |sol.z r k - sol.u r k|
              = |(sol.z r k - xj k) - (sol.u r k - xj k)| := by ring_nf
          _ ≤ |sol.z r k - xj k| + |sol.u r k - xj k| := by
            simpa [abs_sub_comm] using
              abs_sub_le (sol.z r k) (xj k) (sol.u r k)
          _ ≤ D_K + D_K := add_le_add hzD huD
          _ = 2 * D_K := by ring
      have hrle : rPulse M r ≤ (1/2 : ℝ) ^ M := by
        apply rPulse_le_offphase
        apply sin_window_nonneg j
        · simpa [a] using hr_cycle.1
        · have : r ≤ 2 * π * j + π := by
            rw [← hm_eq]
            exact le_trans hr.2 hsm
          simpa using this
      have hrnn : 0 ≤ rPulse M r := rPulse_nonneg M r
      calc
        |A * rPulse M r * (sol.z r k - sol.u r k)|
            = A * rPulse M r * |sol.z r k - sol.u r k| := by
              rw [abs_mul, abs_mul, abs_of_pos hA, abs_of_nonneg hrnn]
        _ ≤ A * ((1/2 : ℝ) ^ M) * (2 * D_K) := by
              have htmp := mul_le_mul hrle hzu (abs_nonneg _)
                (pow_nonneg (by norm_num) M)
              convert mul_le_mul_of_nonneg_left htmp hA.le using 1 <;> ring
    have hhold := hold_bound (fun τ => sol.u τ k)
      (fun r => A * rPulse M r * (sol.z r k - sol.u r k))
      (A * (1/2) ^ M * (2 * D_K)) a s has hderiv hbound
    have hlen : s - a ≤ π := by dsimp [a, m] at hs; linarith
    calc
      |sol.u s k - sol.u a k|
          ≤ (A * (1/2) ^ M * (2 * D_K)) * (s - a) := hhold
      _ ≤ (A * (1/2) ^ M * (2 * D_K)) * π := by
            have hcoef : 0 ≤ A * (1/2 : ℝ) ^ M * (2 * D_K) := by positivity
            exact mul_le_mul_of_nonneg_left hlen hcoef
      _ = trackingChi A M * D_K := by
            unfold trackingChi
            ring
  have hu_first_near : ∀ s ∈ Set.Icc a m, ∀ k,
      |sol.u s k - xj k| ≤ η + trackingChi A M * D_K := by
    intro s hs k
    have hstart := (hsample k).2
    rw [← ha_eq] at hstart
    have hhold := hold_u_first s hs k
    calc
      |sol.u s k - xj k|
          = |(sol.u s k - sol.u a k) + (sol.u a k - xj k)| := by ring_nf
      _ ≤ |sol.u s k - sol.u a k| + |sol.u a k - xj k| := abs_add_le _ _
      _ ≤ trackingChi A M * D_K + η := add_le_add hhold hstart
      _ = η + trackingChi A M * D_K := by ring
  have hsnap_first : ∀ s ∈ Set.Icc a m, ∀ k,
      |S.evalF (sol.u s) k - xnext k| ≤ (S.ηstep : ℝ) := by
    intro s hs k
    have hnear : ∀ l, |sol.u s l - E.enc (Mch.step^[j] (Mch.init w)) l| ≤ (S.r₀ : ℝ) := by
      intro l
      exact le_trans (hu_first_near s hs l) hcasc₂
    simpa [RobustRealExtension.evalF, orbitPoint, xnext, Function.iterate_succ_apply'] using
      S.snap (Mch.step^[j] (Mch.init w)) (sol.u s) hnear k
  have target_to (s : ℝ) (hslo : a + 5 * π / 6 ≤ s) (hsm : s ≤ m) :
      |sol.z s i - xnext i| ≤ trackingKappa A M * (η + D_K) + (S.ηstep : ℝ) := by
    have has : a ≤ s := by linarith
    have hδ : ∀ r ∈ Set.Icc a s, |S.evalF (sol.u r) i - xnext i| ≤ (S.ηstep : ℝ) := by
      intro r hr
      exact hsnap_first r ⟨hr.1, le_trans hr.2 hsm⟩ i
    have hderiv : ∀ r ∈ Set.Icc a s,
        HasDerivAt (fun τ => sol.z τ i)
          (A * qPulse M r * (S.evalF (sol.u r) i - sol.z r i)) r := by
      intro r hr
      exact sol.ode_z r (le_trans ha0 hr.1) i
    have htarget := targeting_bound A hA (qPulse M)
      (fun r => S.evalF (sol.u r) i) (fun r => sol.z r i) a s has
      (qPulse_continuous M) (fun r hr => qPulse_nonneg M r)
      (hEval_cont i) (xnext i) (S.ηstep : ℝ) hδ hderiv
    have hInt : (2 * π / 3) * (3/4 : ℝ) ^ M ≤ ∫ r in a..s, qPulse M r := by
      have hslo' : 2 * π * j + 5 * π / 6 ≤ s := by simpa [a] using hslo
      have hshi' : s ≤ 2 * π * j + π := by simpa [m] using hsm
      simpa [a] using active_integral_lower_to M j hslo' hshi'
    have hcoef :
        Real.exp (-(A * ∫ r in a..s, qPulse M r)) ≤ trackingKappa A M := by
      unfold trackingKappa
      apply Real.exp_le_exp.mpr
      nlinarith [hA, hInt]
    have hstartz := (hsample i).1
    rw [← ha_eq] at hstartz
    have hxgap := hxnext_box i
    have hza : |sol.z a i - xnext i| ≤ η + D_K := by
      calc
        |sol.z a i - xnext i|
            = |(sol.z a i - xj i) - (xnext i - xj i)| := by ring_nf
        _ ≤ |sol.z a i - xj i| + |xnext i - xj i| := by
          simpa [abs_sub_comm] using
            abs_sub_le (sol.z a i) (xj i) (xnext i)
        _ ≤ η + D_K := add_le_add hstartz hxgap
    have hmul :
        Real.exp (-(A * ∫ r in a..s, qPulse M r)) * |sol.z a i - xnext i|
          ≤ trackingKappa A M * (η + D_K) := by
      exact mul_le_mul hcoef hza (abs_nonneg _) hκ_nonneg
    exact le_trans htarget (by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_right hmul (S.ηstep : ℝ))
  by_cases htm : t ≤ m
  · have htar := target_to t ht_low htm
    exact le_trans htar (by
      have : 0 ≤ trackingChi A M * D_K := hχD_nonneg
      linarith)
  · have hmt : m ≤ t := le_of_not_ge htm
    have hm_low : a + 5 * π / 6 ≤ m := by dsimp [a, m]; linarith
    have hz_m := target_to m hm_low le_rfl
    have hold_z_tail : |sol.z t i - sol.z m i| ≤ trackingChi A M * D_K := by
      have hderiv : ∀ r ∈ Set.Icc m t,
          HasDerivAt (fun τ => sol.z τ i)
            (A * qPulse M r * (S.evalF (sol.u r) i - sol.z r i)) r := by
        intro r hr
        exact sol.ode_z r (le_trans (le_trans ha0 hamb) hr.1) i
      have hbound : ∀ r ∈ Set.Icc m t,
          |A * qPulse M r * (S.evalF (sol.u r) i - sol.z r i)|
            ≤ A * (1/2) ^ M * (2 * D_K) := by
        intro r hr
        have hr_cycle : r ∈ Set.Icc (2*π*j) (2*π*(j+1)) := by
          simpa [a, ← hb_eq] using
            (⟨le_trans hamb hr.1, le_trans hr.2 ht_cycle_upper⟩ :
              r ∈ Set.Icc a b)
        have hFD := (hbox j r hr_cycle).2.2.2 i
        have hzD := (hbox j r hr_cycle).2.1 i
        have hFz : |S.evalF (sol.u r) i - sol.z r i| ≤ 2 * D_K := by
          calc
            |S.evalF (sol.u r) i - sol.z r i|
                = |(S.evalF (sol.u r) i - xj i) - (sol.z r i - xj i)| := by ring_nf
            _ ≤ |S.evalF (sol.u r) i - xj i| + |sol.z r i - xj i| := by
              simpa [abs_sub_comm] using
                abs_sub_le (S.evalF (sol.u r) i) (xj i) (sol.z r i)
            _ ≤ D_K + D_K := add_le_add hFD hzD
            _ = 2 * D_K := by ring
        have hqle : qPulse M r ≤ (1/2 : ℝ) ^ M := by
          apply qPulse_le_offphase
          apply sin_window_nonpos j
          · have : 2 * π * j + π ≤ r := by
              rw [← hm_eq]
              exact hr.1
            simpa using this
          · simpa [← hb_eq] using hr_cycle.2
        have hqnn : 0 ≤ qPulse M r := qPulse_nonneg M r
        calc
          |A * qPulse M r * (S.evalF (sol.u r) i - sol.z r i)|
              = A * qPulse M r * |S.evalF (sol.u r) i - sol.z r i| := by
                rw [abs_mul, abs_mul, abs_of_pos hA, abs_of_nonneg hqnn]
          _ ≤ A * ((1/2 : ℝ) ^ M) * (2 * D_K) := by
                have htmp := mul_le_mul hqle hFz (abs_nonneg _)
                  (pow_nonneg (by norm_num) M)
                convert mul_le_mul_of_nonneg_left htmp hA.le using 1 <;> ring
      have hhold := hold_bound (fun τ => sol.z τ i)
        (fun r => A * qPulse M r * (S.evalF (sol.u r) i - sol.z r i))
        (A * (1/2) ^ M * (2 * D_K)) m t hmt hderiv hbound
      have hlen : t - m ≤ π := by dsimp [a, m, b] at ht_cycle_upper ⊢; linarith
      calc
        |sol.z t i - sol.z m i|
            ≤ (A * (1/2) ^ M * (2 * D_K)) * (t - m) := hhold
        _ ≤ (A * (1/2) ^ M * (2 * D_K)) * π := by
              have hcoef : 0 ≤ A * (1/2 : ℝ) ^ M * (2 * D_K) := by positivity
              exact mul_le_mul_of_nonneg_left hlen hcoef
        _ = trackingChi A M * D_K := by
              unfold trackingChi
              ring
    calc
      |sol.z t i - xnext i|
          = |(sol.z t i - sol.z m i) + (sol.z m i - xnext i)| := by ring_nf
      _ ≤ |sol.z t i - sol.z m i| + |sol.z m i - xnext i| := abs_add_le _ _
      _ ≤ trackingChi A M * D_K +
          (trackingKappa A M * (η + D_K) + (S.ηstep : ℝ)) := add_le_add hold_z_tail hz_m
      _ = trackingKappa A M * (η + D_K) + (S.ηstep : ℝ)
          + trackingChi A M * D_K := by ring

private theorem phase_leak_tendsto (L C : ℝ) :
    Filter.Tendsto
      (fun M : ℕ => (((L / (2*π/3)) * (4/3:ℝ)^M + 1) * (1/2:ℝ)^M * C))
      Filter.atTop (𝓝 0) := by
  have h23 : Filter.Tendsto (fun M : ℕ => (2/3:ℝ)^M) Filter.atTop (𝓝 0) := by
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have h12 : Filter.Tendsto (fun M : ℕ => (1/2:ℝ)^M) Filter.atTop (𝓝 0) := by
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hmain : Filter.Tendsto
      (fun M : ℕ => (((L / (2*π/3)) * (2/3:ℝ)^M + (1/2:ℝ)^M) * C))
      Filter.atTop (𝓝 0) := by
    have hleft := h23.const_mul (L / (2*π/3))
    have hsum := hleft.add h12
    simpa using hsum.mul tendsto_const_nhds
  refine hmain.congr' ?_
  filter_upwards [] with M
  have hpow : (4 / 3:ℝ)^M * (1 / 2:ℝ)^M = (2 / 3:ℝ)^M := by
    rw [← mul_pow]
    norm_num
  calc
    (((L / (2*π/3)) * (2/3:ℝ)^M + (1/2:ℝ)^M) * C)
        = (((L / (2*π/3)) * ((4/3:ℝ)^M * (1/2:ℝ)^M) + (1/2:ℝ)^M) * C) := by
          rw [hpow]
    _ = (((L / (2*π/3)) * (4/3:ℝ)^M + 1) * (1/2:ℝ)^M * C) := by
          ring

private theorem exists_phase_leak_bound (L C ε : ℝ)
    (hL : 0 ≤ L) (hC : 0 ≤ C) (hε : 0 < ε) :
    ∃ M : ℕ,
      (((L / (2*π/3)) * (4/3:ℝ)^M + 1) * (1/2:ℝ)^M * C) ≤ ε := by
  obtain ⟨M, hM⟩ := (Metric.tendsto_atTop.mp (phase_leak_tendsto L C)) ε hε
  refine ⟨M, ?_⟩
  have hnonneg : 0 ≤ (((L / (2*π/3)) * (4/3:ℝ)^M + 1) * (1/2:ℝ)^M * C) := by
    have hcpos : 0 < (2 * π / 3 : ℝ) := by positivity
    have hdiv : 0 ≤ L / (2*π/3) := div_nonneg hL hcpos.le
    have hterm : 0 ≤ (L / (2*π/3)) * (4/3:ℝ)^M + 1 := by positivity
    exact mul_nonneg (mul_nonneg hterm (pow_nonneg (by norm_num) M)) hC
  have hdist := hM M le_rfl
  rw [dist_eq_norm, Real.norm_eq_abs, sub_zero, abs_of_nonneg hnonneg] at hdist
  exact le_of_lt hdist

/-- **P6, parameter feasibility** (prop:tracking-feasibility).  For
every target `η` with `ηstep < η (1 - 2κ)`-room and `η ≤ r₀/2`, there
are rational `A > 0`, `M : ℕ` satisfying the three cascade conditions.
Choose `M` large then `A ≈ (4/3)^M (3/(2π)) log(big)`; the leakage
`χ = A 2^{-M} 2π ∝ (2/3)^M log(big) → 0`. -/
theorem tracking_feasibility
    (r₀ ηstep : ℚ) (h0 : 0 < ηstep) (h1 : ηstep < r₀)
    (D_K : ℝ) (hD : 0 < D_K) (η : ℝ)
    (hη₀ : 2 * (ηstep : ℝ) < η) (hη₁ : η ≤ (r₀ : ℝ) / 2) :
    ∃ (A : ℚ) (M : ℕ), 0 < A ∧
      2 * trackingKappa A M < 1 ∧
      2 * trackingKappa A M * D_K + 2 * trackingChi A M * D_K
        + (ηstep : ℝ) ≤ η * (1 - 2 * trackingKappa A M) ∧
      η + trackingChi A M * D_K ≤ (r₀ : ℝ) := by
  let e : ℝ := (ηstep : ℝ)
  let r : ℝ := (r₀ : ℝ)
  have he_pos : 0 < e := by
    change (0 : ℝ) < (ηstep : ℝ)
    exact_mod_cast h0
  have hr_pos : 0 < r := by
    change (0 : ℝ) < (r₀ : ℝ)
    exact_mod_cast (lt_trans h0 h1)
  have hη_pos : 0 < η := by nlinarith [he_pos, hη₀]
  have hm_pos : 0 < η - e := by nlinarith [he_pos, hη₀]
  have hrη_pos : 0 < r - η := by
    nlinarith [hr_pos, hη₁]
  let κstar : ℝ := min (1/4) ((η - e) / (8 * (D_K + η)))
  have hDη_pos : 0 < D_K + η := by nlinarith [hD, hη_pos]
  have hκstar_pos : 0 < κstar := by
    dsimp [κstar]
    exact lt_min (by norm_num) (div_pos hm_pos (by positivity))
  have hκstar_le_quarter : κstar ≤ (1/4 : ℝ) := by
    dsimp [κstar]
    exact min_le_left _ _
  have hκstar_le_margin : κstar ≤ (η - e) / (8 * (D_K + η)) := by
    dsimp [κstar]
    exact min_le_right _ _
  have hκstar_lt_one : κstar < 1 := by nlinarith [hκstar_le_quarter]
  have hinv_gt_one : 1 < 1 / κstar := by
    rw [one_lt_div₀ hκstar_pos]
    linarith
  let L : ℝ := Real.log (1 / κstar)
  have hL_pos : 0 < L := by
    dsimp [L]
    exact Real.log_pos hinv_gt_one
  have hL_nonneg : 0 ≤ L := hL_pos.le
  let leakBudget : ℝ := min ((η - e) / 4) ((r - η) / 2)
  have hleakBudget_pos : 0 < leakBudget := by
    dsimp [leakBudget]
    exact lt_min (div_pos hm_pos (by norm_num)) (div_pos hrη_pos (by norm_num))
  have hleak_le_margin : leakBudget ≤ (η - e) / 4 := by
    dsimp [leakBudget]
    exact min_le_left _ _
  have hleak_le_final : leakBudget ≤ (r - η) / 2 := by
    dsimp [leakBudget]
    exact min_le_right _ _
  obtain ⟨M, hMleak⟩ :=
    exists_phase_leak_bound L (2 * π * D_K) leakBudget hL_nonneg (by positivity)
      hleakBudget_pos
  let lower : ℝ := (L / (2*π/3)) * (4/3:ℝ)^M
  have hlower_pos : 0 < lower := by
    dsimp [lower]
    positivity
  obtain ⟨Aq, hA_lower, hA_upper⟩ :=
    exists_rat_btwn (show lower < lower + 1 by linarith)
  have hAreal_pos : 0 < (Aq : ℝ) := lt_trans hlower_pos hA_lower
  have hAq_pos : 0 < Aq := Rat.cast_pos.mp hAreal_pos
  have hB_pos : 0 < (2 * π / 3) * (3/4:ℝ)^M := by positivity
  have hlower_mul :
      lower * ((2 * π / 3) * (3/4:ℝ)^M) = L := by
    dsimp [lower]
    have hc : (2 * π / 3 : ℝ) ≠ 0 := by positivity
    have hpow : (4 / 3:ℝ)^M * (3 / 4:ℝ)^M = 1 := by
      rw [← mul_pow]
      norm_num
    calc
      ((L / (2*π/3)) * (4/3:ℝ)^M) * ((2*π/3) * (3/4:ℝ)^M)
          = L * ((4/3:ℝ)^M * (3/4:ℝ)^M) := by
            field_simp [hc]
      _ = L := by rw [hpow]; ring
  have hAB_ge_L : L ≤ (Aq : ℝ) * ((2 * π / 3) * (3/4:ℝ)^M) := by
    have hlt := mul_lt_mul_of_pos_right hA_lower hB_pos
    rw [hlower_mul] at hlt
    exact le_of_lt hlt
  have hexp_negL : Real.exp (-L) = κstar := by
    dsimp [L]
    rw [Real.exp_neg, Real.exp_log (by positivity : 0 < 1 / κstar)]
    field_simp [ne_of_gt hκstar_pos]
  have hκ_le_star : trackingKappa (Aq : ℝ) M ≤ κstar := by
    unfold trackingKappa
    calc
      Real.exp (-((Aq : ℝ) * ((2 * π / 3) * (3/4:ℝ)^M)))
          ≤ Real.exp (-L) := by
            apply Real.exp_le_exp.mpr
            linarith
      _ = κstar := hexp_negL
  have hκ_nonneg : 0 ≤ trackingKappa (Aq : ℝ) M := by
    unfold trackingKappa
    exact (Real.exp_pos _).le
  have hχD_le_budget : trackingChi (Aq : ℝ) M * D_K ≤ leakBudget := by
    have hfactor_nonneg : 0 ≤ (1/2:ℝ)^M * (2 * π * D_K) := by positivity
    have hA_le : (Aq : ℝ) ≤ lower + 1 := hA_upper.le
    have hmul := mul_le_mul_of_nonneg_right hA_le hfactor_nonneg
    calc
      trackingChi (Aq : ℝ) M * D_K
          = (Aq : ℝ) * (1/2:ℝ)^M * (2 * π * D_K) := by
            unfold trackingChi
            ring
      _ ≤ (lower + 1) * (1/2:ℝ)^M * (2 * π * D_K) := by
            simpa [mul_assoc] using hmul
      _ = (((L / (2*π/3)) * (4/3:ℝ)^M + 1) * (1/2:ℝ)^M * (2 * π * D_K)) := by
            dsimp [lower]
      _ ≤ leakBudget := hMleak
  refine ⟨Aq, M, hAq_pos, ?_, ?_, ?_⟩
  · linarith [hκ_le_star, hκstar_le_quarter]
  · have hκ_le_margin :
        trackingKappa (Aq : ℝ) M ≤ (η - e) / (8 * (D_K + η)) :=
      le_trans hκ_le_star hκstar_le_margin
    have hκterm : 2 * trackingKappa (Aq : ℝ) M * (D_K + η) ≤ (η - e) / 4 := by
      have hmul := mul_le_mul_of_nonneg_right hκ_le_margin
        (show 0 ≤ 2 * (D_K + η) by positivity)
      have hden : 0 < 8 * (D_K + η) := by positivity
      calc
        2 * trackingKappa (Aq : ℝ) M * (D_K + η)
            = trackingKappa (Aq : ℝ) M * (2 * (D_K + η)) := by ring
        _ ≤ ((η - e) / (8 * (D_K + η))) * (2 * (D_K + η)) := hmul
        _ = (η - e) / 4 := by
              field_simp [ne_of_gt hDη_pos]
              ring
    have hχterm : 2 * (trackingChi (Aq : ℝ) M * D_K) ≤ (η - e) / 2 := by
      linarith [hχD_le_budget, hleak_le_margin]
    have hmain : 2 * trackingKappa (Aq : ℝ) M * D_K
        + 2 * (trackingChi (Aq : ℝ) M * D_K) + e
        + 2 * η * trackingKappa (Aq : ℝ) M ≤ η := by
      have : 2 * trackingKappa (Aq : ℝ) M * D_K
          + 2 * η * trackingKappa (Aq : ℝ) M
          = 2 * trackingKappa (Aq : ℝ) M * (D_K + η) := by ring
      linarith
    change 2 * trackingKappa (Aq : ℝ) M * D_K
        + 2 * trackingChi (Aq : ℝ) M * D_K + e
        ≤ η * (1 - 2 * trackingKappa (Aq : ℝ) M)
    linarith [hmain]
  · change η + trackingChi (Aq : ℝ) M * D_K ≤ r
    have hχfinal : trackingChi (Aq : ℝ) M * D_K ≤ (r - η) / 2 :=
      le_trans hχD_le_budget hleak_le_final
    linarith

end Ripple.BoundedUniversality.BGP
