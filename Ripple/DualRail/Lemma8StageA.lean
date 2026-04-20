/-
  Ripple.DualRail.Lemma8StageA — Stage A of the DNA25 Lemma 8 two-stage gadget.

  Given bounded continuous trajectories `x, y : ℝ → ℝ` (for `t ≥ 0`) with
  `|x(t) − y(t) − γ| → 0` (where `γ := α − β > 0` and `0 < γ < 1`),
  this file constructs the scalar ODE tracker

      z_r'(t) = 1 − (x(t) − y(t)) · z_r(t),    z_r(0) = 0

  and proves:
    1. existence + continuity of `z_r` on all `t ≥ 0`,
    2. non-negativity `z_r(t) ≥ 0`,
    3. a uniform upper bound `z_r(t) ≤ B_{z_r}` on `[0, ∞)`,
    4. exponential convergence `z_r(t) → 1/γ`, with an effective modulus.

  The construction uses the integrating-factor/Duhamel form. Let
  `A(t) := ∫_0^t (x − y)(u) du` and

      z_r(t) := exp(-A(t)) · ∫_0^t exp(A(s)) ds
              = ∫_0^t exp(-(A(t) - A(s))) ds.

  Key identity (split at `T`):
      z_r(t) = exp(-(A(t) - A(T))) · z_r(T) + ∫_T^t exp(-(A(t) - A(s))) ds.

  For `t ≥ T` with `driver ≥ γ/2` on `[T, t]`, `A(t) - A(s) ≥ (γ/2)(t-s)`, so
      z_r(t) ≤ exp(-(γ/2)(t-T)) · z_r(T) + (2/γ)·(1 - exp(-(γ/2)(t-T)))
            ≤ max (z_r T) (2/γ).

  This is the decay-to-`2/γ` estimate used to establish the uniform bound.

  Reference: [RTCRN2] Huang–Klinge–Lathrop, DNA 25 (2019), Lemma 8, Stage A
  (reciprocal tracker).

  Stage B (the `z` subtraction layer) is a separate file.
-/

import Ripple.LPP.AddRationalPos
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Mul

namespace Ripple
namespace DualRail
namespace Lemma8StageA

open MeasureTheory

/-! ## Input bundle -/

/-- The input bundle for Stage A: a bounded continuous driver `(x - y)(t)`
converging to `γ` with a `diffMod`-style time modulus. -/
structure DriverData (γ : ℝ) where
  /-- The driver function `(x - y)(t)`. -/
  driver : ℝ → ℝ
  /-- Global continuity. -/
  driver_cont : Continuous driver
  /-- A uniform bound for `|driver|` on `[0, ∞)`. -/
  driver_bound : ℝ
  /-- Non-negativity of the bound. -/
  driver_bound_nn : 0 ≤ driver_bound
  /-- Absolute bound on `[0, ∞)`. -/
  driver_abs_bd : ∀ t, 0 ≤ t → |driver t| ≤ driver_bound
  /-- Convergence modulus `diffMod r`: past it, `|driver t − γ| < exp(-r)`. -/
  diffMod : ℕ → ℝ
  /-- Convergence: for `t > diffMod r` with `t ≥ 0`,
      `|driver t − γ| < exp(-r)`. -/
  diffMod_conv : ∀ r t, 0 ≤ t → t > diffMod r →
      |driver t - γ| < Real.exp (-(r : ℝ))

namespace DriverData

variable {γ : ℝ} (D : DriverData γ)

/-- The integrated driver `A(t) := ∫_0^t driver(u) du`. -/
noncomputable def antideriv (t : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..t, D.driver u

@[simp] lemma antideriv_zero : D.antideriv 0 = 0 := by
  unfold antideriv; simp

lemma driver_intervalIntegrable (a b : ℝ) :
    IntervalIntegrable D.driver volume a b :=
  D.driver_cont.intervalIntegrable a b

/-- FTC-1 on the driver: `A'(t) = driver(t)` at every `t : ℝ`. -/
lemma antideriv_hasDerivAt (t : ℝ) :
    HasDerivAt D.antideriv (D.driver t) t := by
  unfold antideriv
  have hii : IntervalIntegrable D.driver volume 0 t :=
    D.driver_intervalIntegrable 0 t
  have hmeas : StronglyMeasurableAtFilter D.driver (nhds t) volume :=
    D.driver_cont.stronglyMeasurableAtFilter _ _
  have hcontAt : ContinuousAt D.driver t := D.driver_cont.continuousAt
  exact intervalIntegral.integral_hasDerivAt_right hii hmeas hcontAt

lemma antideriv_continuous : Continuous D.antideriv := by
  refine continuous_iff_continuousAt.mpr (fun t => ?_)
  exact (D.antideriv_hasDerivAt t).continuousAt

/-- For `0 ≤ t`, `|A(t)| ≤ driver_bound · t`. -/
lemma antideriv_abs_le {t : ℝ} (ht : 0 ≤ t) :
    |D.antideriv t| ≤ D.driver_bound * t := by
  unfold antideriv
  have habs : |∫ u in (0:ℝ)..t, D.driver u|
      ≤ ∫ u in (0:ℝ)..t, |D.driver u| :=
    intervalIntegral.abs_integral_le_integral_abs ht
  have hbound_ptw : ∀ u ∈ Set.Icc (0:ℝ) t,
      |D.driver u| ≤ D.driver_bound := by
    intro u hu; exact D.driver_abs_bd u hu.1
  have h_abs_int : IntervalIntegrable (fun u => |D.driver u|) volume 0 t :=
    D.driver_cont.abs.intervalIntegrable 0 t
  have h_const_int : IntervalIntegrable (fun _ : ℝ => D.driver_bound) volume 0 t :=
    continuous_const.intervalIntegrable 0 t
  have hle : (∫ u in (0:ℝ)..t, |D.driver u|)
      ≤ ∫ u in (0:ℝ)..t, D.driver_bound :=
    intervalIntegral.integral_mono_on ht h_abs_int h_const_int hbound_ptw
  have heval : ∫ _u in (0:ℝ)..t, D.driver_bound = D.driver_bound * t := by
    rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_comm]
  linarith

/-- For `0 ≤ T ≤ t` with `driver(u) ≥ γ/2` on `[T, t]`,
`A(t) - A(T) ≥ (γ/2)·(t - T)`. -/
lemma antideriv_diff_ge {T t c : ℝ} (hT_nn : 0 ≤ T) (hTt : T ≤ t)
    (hlb : ∀ u, T ≤ u → u ≤ t → c ≤ D.driver u) :
    c * (t - T) ≤ D.antideriv t - D.antideriv T := by
  -- A(t) - A(T) = ∫_T^t driver(u) du. Apply integral_mono on [T, t].
  have hsplit : D.antideriv t - D.antideriv T = ∫ u in T..t, D.driver u := by
    unfold antideriv
    have hii1 : IntervalIntegrable D.driver volume 0 T :=
      D.driver_intervalIntegrable 0 T
    have hii2 : IntervalIntegrable D.driver volume T t :=
      D.driver_intervalIntegrable T t
    have := intervalIntegral.integral_add_adjacent_intervals hii1 hii2
    linarith
  rw [hsplit]
  -- ∫_T^t c du = c·(t - T) ≤ ∫_T^t driver(u) du by monotonicity.
  have h_const_int : IntervalIntegrable (fun _ : ℝ => c) volume T t :=
    continuous_const.intervalIntegrable T t
  have hii2 : IntervalIntegrable D.driver volume T t :=
    D.driver_intervalIntegrable T t
  have hmono : (∫ _u in T..t, c) ≤ ∫ u in T..t, D.driver u := by
    apply intervalIntegral.integral_mono_on hTt h_const_int hii2
    intro u hu; exact hlb u hu.1 hu.2
  have heval : (∫ _u in T..t, c) = c * (t - T) := by
    rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm]
  linarith

end DriverData

/-! ## The tracker `z_r` via integrating factor. -/

/-- Inner integral `I(t) := ∫_0^t exp(A(s)) ds`. -/
noncomputable def zrInner {γ : ℝ} (D : DriverData γ) : ℝ → ℝ :=
  fun t => ∫ s in (0 : ℝ)..t, Real.exp (D.antideriv s)

/-- The Stage-A tracker trajectory: `z_r(t) := exp(-A(t)) · I(t)`. -/
noncomputable def zrTraj {γ : ℝ} (D : DriverData γ) : ℝ → ℝ :=
  fun t => Real.exp (- D.antideriv t) * zrInner D t

namespace zrTraj

variable {γ : ℝ} (D : DriverData γ)

lemma exp_antideriv_continuous : Continuous (fun s => Real.exp (D.antideriv s)) :=
  Real.continuous_exp.comp D.antideriv_continuous

lemma inner_continuous : Continuous (zrInner D) := by
  unfold zrInner
  refine continuous_iff_continuousAt.mpr (fun t => ?_)
  have hcont := exp_antideriv_continuous D
  have hii : IntervalIntegrable (fun s => Real.exp (D.antideriv s)) volume 0 t :=
    hcont.intervalIntegrable 0 t
  have hmeas : StronglyMeasurableAtFilter (fun s => Real.exp (D.antideriv s))
      (nhds t) volume := hcont.stronglyMeasurableAtFilter _ _
  exact (intervalIntegral.integral_hasDerivAt_right hii hmeas
    hcont.continuousAt).continuousAt

lemma continuous : Continuous (zrTraj D) := by
  unfold zrTraj
  have h1 : Continuous (fun t : ℝ => Real.exp (- D.antideriv t)) :=
    Real.continuous_exp.comp D.antideriv_continuous.neg
  exact h1.mul (inner_continuous D)

@[simp] lemma zero : zrTraj D 0 = 0 := by
  unfold zrTraj zrInner; simp

lemma inner_hasDerivAt (t : ℝ) :
    HasDerivAt (zrInner D) (Real.exp (D.antideriv t)) t := by
  unfold zrInner
  have hcont := exp_antideriv_continuous D
  have hii : IntervalIntegrable (fun s => Real.exp (D.antideriv s)) volume 0 t :=
    hcont.intervalIntegrable 0 t
  have hmeas : StronglyMeasurableAtFilter (fun s => Real.exp (D.antideriv s))
      (nhds t) volume := hcont.stronglyMeasurableAtFilter _ _
  exact intervalIntegral.integral_hasDerivAt_right hii hmeas hcont.continuousAt

/-- Stage-A ODE: `z_r'(t) = 1 − driver(t) · z_r(t)` at every `t : ℝ`. -/
lemma hasDerivAt (t : ℝ) :
    HasDerivAt (zrTraj D) (1 - D.driver t * zrTraj D t) t := by
  unfold zrTraj
  have hA := D.antideriv_hasDerivAt t
  have hExpNeg : HasDerivAt (fun s => Real.exp (- D.antideriv s))
      (Real.exp (- D.antideriv t) * (- D.driver t)) t := hA.neg.exp
  have hI := inner_hasDerivAt D t
  have hProd : HasDerivAt
      (fun s => Real.exp (- D.antideriv s) * zrInner D s)
      (Real.exp (- D.antideriv t) * (- D.driver t) * zrInner D t
        + Real.exp (- D.antideriv t) * Real.exp (D.antideriv t)) t :=
    hExpNeg.mul hI
  have hCancel : Real.exp (- D.antideriv t) * Real.exp (D.antideriv t) = 1 := by
    rw [← Real.exp_add]; simp
  convert hProd using 1
  rw [hCancel]; ring

lemma inner_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ zrInner D t := by
  unfold zrInner
  apply intervalIntegral.integral_nonneg ht
  intro s _; exact (Real.exp_pos _).le

lemma nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ zrTraj D t :=
  mul_nonneg (Real.exp_pos _).le (inner_nonneg D ht)

end zrTraj

/-! ## Key split identity.

For `0 ≤ T ≤ t`:
  `z_r(t) = exp(-(A(t) - A(T))) · z_r(T) + ∫_T^t exp(-(A(t) - A(s))) ds`.

This is the "shifted Duhamel" form, obtained by splitting the inner integral
at `T` and factoring out `exp(-A(T))`.
-/

namespace zrTraj

variable {γ : ℝ} (D : DriverData γ)

/-- Split identity: `z_r(t) = exp(-(A(t)-A(T)))·z_r(T) + ∫_T^t exp(-(A(t)-A(s))) ds`. -/
lemma split_identity {T t : ℝ} (hT_nn : 0 ≤ T) (hTt : T ≤ t) :
    zrTraj D t = Real.exp (-(D.antideriv t - D.antideriv T)) * zrTraj D T
      + ∫ s in T..t, Real.exp (-(D.antideriv t - D.antideriv s)) := by
  unfold zrTraj zrInner
  -- LHS = exp(-A(t)) · (∫_0^T + ∫_T^t)
  have hii1 : IntervalIntegrable (fun s => Real.exp (D.antideriv s)) volume 0 T :=
    (exp_antideriv_continuous D).intervalIntegrable 0 T
  have hii2 : IntervalIntegrable (fun s => Real.exp (D.antideriv s)) volume T t :=
    (exp_antideriv_continuous D).intervalIntegrable T t
  have hsplit : (∫ s in (0:ℝ)..t, Real.exp (D.antideriv s))
      = (∫ s in (0:ℝ)..T, Real.exp (D.antideriv s))
        + ∫ s in T..t, Real.exp (D.antideriv s) :=
    (intervalIntegral.integral_add_adjacent_intervals hii1 hii2).symm
  rw [hsplit, mul_add]
  have hExpSum : Real.exp (-(D.antideriv t - D.antideriv T))
      = Real.exp (- D.antideriv t) * Real.exp (D.antideriv T) := by
    rw [← Real.exp_add]; congr 1; ring
  congr 1
  · -- exp(-A(t)) · ∫_0^T exp(A(s)) ds
    --   = exp(-(A(t)-A(T))) · (exp(-A(T)) · ∫_0^T exp(A(s)) ds)
    rw [hExpSum]
    have hCancel : Real.exp (D.antideriv T) * Real.exp (- D.antideriv T) = 1 := by
      rw [← Real.exp_add]; simp
    -- Goal: exp(-A t) * I_0T = (exp(-A t) * exp(A T)) * (exp(-A T) * I_0T)
    have hrhs : Real.exp (- D.antideriv t) * Real.exp (D.antideriv T) *
          (Real.exp (- D.antideriv T) *
            ∫ s in (0:ℝ)..T, Real.exp (D.antideriv s))
        = Real.exp (- D.antideriv t) *
            ∫ s in (0:ℝ)..T, Real.exp (D.antideriv s) := by
      calc Real.exp (- D.antideriv t) * Real.exp (D.antideriv T) *
            (Real.exp (- D.antideriv T) *
              ∫ s in (0:ℝ)..T, Real.exp (D.antideriv s))
          = Real.exp (- D.antideriv t) *
              (Real.exp (D.antideriv T) * Real.exp (- D.antideriv T)) *
              ∫ s in (0:ℝ)..T, Real.exp (D.antideriv s) := by ring
        _ = Real.exp (- D.antideriv t) * 1 *
              ∫ s in (0:ℝ)..T, Real.exp (D.antideriv s) := by rw [hCancel]
        _ = Real.exp (- D.antideriv t) *
              ∫ s in (0:ℝ)..T, Real.exp (D.antideriv s) := by ring
    linarith
  · -- exp(-A(t)) · ∫_T^t exp(A(s)) ds = ∫_T^t exp(A(s) - A(t)) ds
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s _
    dsimp
    rw [← Real.exp_add]
    congr 1; ring

end zrTraj

/-! ## Uniform bound on `[0, ∞)`.

Strategy:
  * Pick `N0 : ℕ` with `exp(-N0) ≤ γ/2`.
  * `T* := max 0 (D.diffMod N0)`. For `t > T*`, `driver(t) ≥ γ/2`.
  * On `[0, T*]`: crude bound using integrating factor and `|driver| ≤ M`.
  * On `[T*, ∞)`: decay to `2/γ`.
-/

/-- Choose `N0 : ℕ` with `exp(-N0) ≤ γ/2`. -/
noncomputable def chooseN0 (γ : ℝ) : ℕ :=
  Nat.ceil (- Real.log (γ / 2))

lemma chooseN0_spec {γ : ℝ} (hγ : 0 < γ) :
    Real.exp (-(chooseN0 γ : ℝ)) ≤ γ / 2 := by
  have hγ2 : 0 < γ / 2 := by linarith
  have hle : -Real.log (γ / 2) ≤ (chooseN0 γ : ℝ) := by
    show _ ≤ ((Nat.ceil (- Real.log (γ / 2)) : ℕ) : ℝ)
    exact Nat.le_ceil _
  have h_neg : -(chooseN0 γ : ℝ) ≤ Real.log (γ / 2) := by linarith
  have h_exp_le : Real.exp (-(chooseN0 γ : ℝ)) ≤ Real.exp (Real.log (γ / 2)) :=
    Real.exp_le_exp.mpr h_neg
  rwa [Real.exp_log hγ2] at h_exp_le

/-- Past `T* := max 0 (D.diffMod N0)`, the driver is at least `γ/2 > 0`. -/
lemma driver_ge_half_gamma_past_Tstar {γ : ℝ} (hγ : 0 < γ) (D : DriverData γ)
    {t : ℝ} (ht_nn : 0 ≤ t) (ht_gt : t > D.diffMod (chooseN0 γ)) :
    γ / 2 ≤ D.driver t := by
  have hconv := D.diffMod_conv (chooseN0 γ) t ht_nn ht_gt
  have hbd : Real.exp (-(chooseN0 γ : ℝ)) ≤ γ / 2 := chooseN0_spec hγ
  have h1 : |D.driver t - γ| < γ / 2 := lt_of_lt_of_le hconv hbd
  have h2 : -(γ / 2) < D.driver t - γ := (abs_lt.mp h1).1
  linarith

namespace zrTraj

variable {γ : ℝ} (D : DriverData γ)

/-- Crude bound on `[0, T]`: `z_r(t) ≤ exp(2·B·t) · t` where `B := driver_bound`.

Proof: `exp(-A(t)) ≤ exp(B·t)` since `-A(t) ≤ |A(t)| ≤ B·t`, and
`∫_0^t exp(A(s)) ds ≤ ∫_0^t exp(B·t) ds = exp(B·t)·t`. -/
lemma crude_bound {t : ℝ} (ht : 0 ≤ t) :
    zrTraj D t ≤ Real.exp (2 * D.driver_bound * t) * t := by
  unfold zrTraj zrInner
  have hNeg_le : -D.antideriv t ≤ D.driver_bound * t := by
    have := D.antideriv_abs_le ht
    have h2 : -D.antideriv t ≤ |D.antideriv t| := neg_le_abs _
    linarith
  have hNegA_le : Real.exp (-D.antideriv t) ≤ Real.exp (D.driver_bound * t) :=
    Real.exp_le_exp.mpr hNeg_le
  have hExpNegA_nn : 0 ≤ Real.exp (-D.antideriv t) := (Real.exp_pos _).le
  -- Inner integral bound.
  have hInner_le : (∫ s in (0:ℝ)..t, Real.exp (D.antideriv s))
      ≤ ∫ _s in (0:ℝ)..t, Real.exp (D.driver_bound * t) := by
    apply intervalIntegral.integral_mono_on ht
    · exact (exp_antideriv_continuous D).intervalIntegrable 0 t
    · exact continuous_const.intervalIntegrable 0 t
    · intro s hs
      have hs0 : 0 ≤ s := hs.1
      have hst : s ≤ t := hs.2
      have h1 : D.antideriv s ≤ D.driver_bound * s := le_of_abs_le (D.antideriv_abs_le hs0)
      have h2 : D.driver_bound * s ≤ D.driver_bound * t :=
        mul_le_mul_of_nonneg_left hst D.driver_bound_nn
      exact Real.exp_le_exp.mpr (le_trans h1 h2)
  have hInnerEval : ∫ _s in (0:ℝ)..t, Real.exp (D.driver_bound * t)
      = Real.exp (D.driver_bound * t) * t := by
    rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_comm]
  have hInner_le' : (∫ s in (0:ℝ)..t, Real.exp (D.antideriv s))
      ≤ Real.exp (D.driver_bound * t) * t := by linarith
  have hInner_nn : 0 ≤ ∫ s in (0:ℝ)..t, Real.exp (D.antideriv s) := by
    apply intervalIntegral.integral_nonneg ht
    intro s _; exact (Real.exp_pos _).le
  have hExpBt_nn : 0 ≤ Real.exp (D.driver_bound * t) := (Real.exp_pos _).le
  calc Real.exp (-D.antideriv t) * ∫ s in (0:ℝ)..t, Real.exp (D.antideriv s)
      ≤ Real.exp (D.driver_bound * t) * (Real.exp (D.driver_bound * t) * t) :=
        mul_le_mul hNegA_le hInner_le' hInner_nn hExpBt_nn
    _ = Real.exp (2 * D.driver_bound * t) * t := by
        rw [show Real.exp (D.driver_bound * t) * (Real.exp (D.driver_bound * t) * t)
            = (Real.exp (D.driver_bound * t) * Real.exp (D.driver_bound * t)) * t by ring,
          ← Real.exp_add]
        congr 2; ring

/-- **Parametrized decay upper bound.** If `driver(s) ≥ c > 0` on `[T, t]`
with `0 ≤ T ≤ t`, then
  `z_r(t) ≤ exp(-c(t-T)) · z_r(T) + (1/c)·(1 - exp(-c(t-T)))`.
Proof: split identity + monotonicity of exp on `A(t) - A(s) ≥ c(t-s)`. -/
lemma decay_upper {T t c : ℝ} (hc : 0 < c) (hT_nn : 0 ≤ T) (hTt : T ≤ t)
    (hzT_nn : 0 ≤ zrTraj D T)
    (hdriver_ge : ∀ s, T ≤ s → s ≤ t → c ≤ D.driver s) :
    zrTraj D t ≤ Real.exp (-c * (t - T)) * zrTraj D T
      + (1 / c) * (1 - Real.exp (-c * (t - T))) := by
  rw [split_identity D hT_nn hTt]
  -- First term.
  have hAdiff_ge : c * (t - T) ≤ D.antideriv t - D.antideriv T :=
    D.antideriv_diff_ge hT_nn hTt hdriver_ge
  have hNegAdiff_le : -(D.antideriv t - D.antideriv T) ≤ -c * (t - T) := by linarith
  have hExp_first : Real.exp (-(D.antideriv t - D.antideriv T)) ≤ Real.exp (-c * (t - T)) :=
    Real.exp_le_exp.mpr hNegAdiff_le
  have hFirst_bd : Real.exp (-(D.antideriv t - D.antideriv T)) * zrTraj D T
      ≤ Real.exp (-c * (t - T)) * zrTraj D T :=
    mul_le_mul_of_nonneg_right hExp_first hzT_nn
  -- Second term.
  have hCont_lhs : Continuous (fun s : ℝ => Real.exp (-(D.antideriv t - D.antideriv s))) := by
    refine Real.continuous_exp.comp ?_
    exact (continuous_const.sub D.antideriv_continuous).neg
  have hCont_rhs : Continuous (fun s : ℝ => Real.exp (-c * (t - s))) := by
    refine Real.continuous_exp.comp ?_
    exact (continuous_const.mul (continuous_const.sub continuous_id))
  have hInt_bd : (∫ s in T..t, Real.exp (-(D.antideriv t - D.antideriv s)))
      ≤ ∫ s in T..t, Real.exp (-c * (t - s)) := by
    apply intervalIntegral.integral_mono_on hTt
    · exact hCont_lhs.intervalIntegrable T t
    · exact hCont_rhs.intervalIntegrable T t
    · intro s hs
      have hAdiff_ge' : c * (t - s) ≤ D.antideriv t - D.antideriv s := by
        apply D.antideriv_diff_ge (le_trans hT_nn hs.1) hs.2
        intro u hus hut; exact hdriver_ge u (le_trans hs.1 hus) hut
      have : -(D.antideriv t - D.antideriv s) ≤ -c * (t - s) := by linarith
      exact Real.exp_le_exp.mpr this
  have hEval : (∫ s in T..t, Real.exp (-c * (t - s)))
      = (1 / c) * (1 - Real.exp (-c * (t - T))) := by
    have h_comp1 : (∫ s in T..t, Real.exp (-c * (t - s)))
        = ∫ u in (0:ℝ)..(t - T), Real.exp (-c * u) := by
      have h := intervalIntegral.integral_comp_sub_left
        (f := fun u => Real.exp (-c * u)) (a := T) (b := t) (d := t)
      simp only [sub_self] at h
      rw [h]
    rw [h_comp1]
    have hc_ne : -c ≠ 0 := by linarith
    have h_mul := intervalIntegral.mul_integral_comp_mul_left
      (f := Real.exp) (c := -c) (a := 0) (b := t - T)
    rw [show (-c : ℝ) * 0 = 0 by ring] at h_mul
    rw [integral_exp, Real.exp_zero] at h_mul
    have hI_eq : (∫ u in (0:ℝ)..(t-T), Real.exp (-c * u))
        = (Real.exp (-c * (t - T)) - 1) / (-c) := by
      field_simp at h_mul ⊢
      linarith
    rw [hI_eq]
    field_simp
    ring
  linarith

/-- **Parametrized decay lower bound.** If `driver(s) ≤ c` on `[T, t]`
with `c > 0`, `0 ≤ T ≤ t`, and `z_r(T) ≥ 0`, then
  `z_r(t) ≥ exp(-c(t-T)) · z_r(T) + (1/c)·(1 - exp(-c(t-T)))`.

Proof: symmetric to `decay_upper`; using `A(t) - A(s) ≤ c(t - s)`. -/
lemma decay_lower {T t c : ℝ} (hc : 0 < c) (hT_nn : 0 ≤ T) (hTt : T ≤ t)
    (hzT_nn : 0 ≤ zrTraj D T)
    (hdriver_le : ∀ s, T ≤ s → s ≤ t → D.driver s ≤ c) :
    Real.exp (-c * (t - T)) * zrTraj D T
      + (1 / c) * (1 - Real.exp (-c * (t - T)))
      ≤ zrTraj D t := by
  rw [split_identity D hT_nn hTt]
  -- First term: exp(-(A(t)-A(T))) ≥ exp(-c(t-T)).
  -- A(t) - A(T) = ∫_T^t driver(u) du ≤ c·(t - T) since driver ≤ c.
  have hAdiff_le : D.antideriv t - D.antideriv T ≤ c * (t - T) := by
    -- analogous to antideriv_diff_ge.
    have hsplit : D.antideriv t - D.antideriv T = ∫ u in T..t, D.driver u := by
      unfold DriverData.antideriv
      have hii1 : IntervalIntegrable D.driver volume 0 T :=
        D.driver_intervalIntegrable 0 T
      have hii2 : IntervalIntegrable D.driver volume T t :=
        D.driver_intervalIntegrable T t
      have := intervalIntegral.integral_add_adjacent_intervals hii1 hii2
      linarith
    rw [hsplit]
    have h_const_int : IntervalIntegrable (fun _ : ℝ => c) volume T t :=
      continuous_const.intervalIntegrable T t
    have hii2 : IntervalIntegrable D.driver volume T t :=
      D.driver_intervalIntegrable T t
    have hmono : (∫ u in T..t, D.driver u) ≤ ∫ _u in T..t, c := by
      apply intervalIntegral.integral_mono_on hTt hii2 h_const_int
      intro u hu; exact hdriver_le u hu.1 hu.2
    have heval : (∫ _u in T..t, c) = c * (t - T) := by
      rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm]
    linarith
  have hNegAdiff_ge : -c * (t - T) ≤ -(D.antideriv t - D.antideriv T) := by linarith
  have hExp_first_ge : Real.exp (-c * (t - T))
      ≤ Real.exp (-(D.antideriv t - D.antideriv T)) :=
    Real.exp_le_exp.mpr hNegAdiff_ge
  have hFirst_bd : Real.exp (-c * (t - T)) * zrTraj D T
      ≤ Real.exp (-(D.antideriv t - D.antideriv T)) * zrTraj D T :=
    mul_le_mul_of_nonneg_right hExp_first_ge hzT_nn
  -- Second term (integral): reverse direction.
  have hCont_lhs : Continuous (fun s : ℝ => Real.exp (-(D.antideriv t - D.antideriv s))) := by
    refine Real.continuous_exp.comp ?_
    exact (continuous_const.sub D.antideriv_continuous).neg
  have hCont_rhs : Continuous (fun s : ℝ => Real.exp (-c * (t - s))) := by
    refine Real.continuous_exp.comp ?_
    exact (continuous_const.mul (continuous_const.sub continuous_id))
  have hInt_bd_ge : (∫ s in T..t, Real.exp (-c * (t - s)))
      ≤ ∫ s in T..t, Real.exp (-(D.antideriv t - D.antideriv s)) := by
    apply intervalIntegral.integral_mono_on hTt
    · exact hCont_rhs.intervalIntegrable T t
    · exact hCont_lhs.intervalIntegrable T t
    · intro s hs
      -- A(t) - A(s) ≤ c·(t - s) on [T, t].
      have hAdiff_le_s : D.antideriv t - D.antideriv s ≤ c * (t - s) := by
        -- Direct: ∫_s^t driver ≤ c·(t - s).
        have hsplit : D.antideriv t - D.antideriv s = ∫ u in s..t, D.driver u := by
          unfold DriverData.antideriv
          have hii1 : IntervalIntegrable D.driver volume 0 s :=
            D.driver_intervalIntegrable 0 s
          have hii2 : IntervalIntegrable D.driver volume s t :=
            D.driver_intervalIntegrable s t
          have := intervalIntegral.integral_add_adjacent_intervals hii1 hii2
          linarith
        rw [hsplit]
        have h_const_int : IntervalIntegrable (fun _ : ℝ => c) volume s t :=
          continuous_const.intervalIntegrable s t
        have hii2 : IntervalIntegrable D.driver volume s t :=
          D.driver_intervalIntegrable s t
        have hmono : (∫ u in s..t, D.driver u) ≤ ∫ _u in s..t, c := by
          apply intervalIntegral.integral_mono_on hs.2 hii2 h_const_int
          intro u hu; exact hdriver_le u (le_trans hs.1 hu.1) hu.2
        have heval : (∫ _u in s..t, c) = c * (t - s) := by
          rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm]
        linarith
      have : -c * (t - s) ≤ -(D.antideriv t - D.antideriv s) := by linarith
      exact Real.exp_le_exp.mpr this
  have hEval : (∫ s in T..t, Real.exp (-c * (t - s)))
      = (1 / c) * (1 - Real.exp (-c * (t - T))) := by
    have h_comp1 : (∫ s in T..t, Real.exp (-c * (t - s)))
        = ∫ u in (0:ℝ)..(t - T), Real.exp (-c * u) := by
      have h := intervalIntegral.integral_comp_sub_left
        (f := fun u => Real.exp (-c * u)) (a := T) (b := t) (d := t)
      simp only [sub_self] at h
      rw [h]
    rw [h_comp1]
    have hc_ne : -c ≠ 0 := by linarith
    have h_mul := intervalIntegral.mul_integral_comp_mul_left
      (f := Real.exp) (c := -c) (a := 0) (b := t - T)
    rw [show (-c : ℝ) * 0 = 0 by ring] at h_mul
    rw [integral_exp, Real.exp_zero] at h_mul
    have hI_eq : (∫ u in (0:ℝ)..(t-T), Real.exp (-c * u))
        = (Real.exp (-c * (t - T)) - 1) / (-c) := by
      field_simp at h_mul ⊢
      linarith
    rw [hI_eq]
    field_simp
    ring
  linarith

/-- The original decay bound, as a special case of `decay_upper` with `c := γ/2`. -/
lemma decay_bound {T t : ℝ} (hγ : 0 < γ) (hT_nn : 0 ≤ T) (hTt : T ≤ t)
    (hzT_nn : 0 ≤ zrTraj D T)
    (hdriver_ge : ∀ s, T ≤ s → s ≤ t → γ / 2 ≤ D.driver s) :
    zrTraj D t ≤ Real.exp (-(γ / 2) * (t - T)) * zrTraj D T
      + (2 / γ) * (1 - Real.exp (-(γ / 2) * (t - T))) := by
  have hc : 0 < γ / 2 := by linarith
  have := decay_upper D hc hT_nn hTt hzT_nn hdriver_ge
  have h_eq : (1 : ℝ) / (γ / 2) = 2 / γ := by field_simp
  rw [h_eq] at this
  exact this

end zrTraj

/-! ## Uniform bound assembly.

Define `T* := max 0 (D.diffMod (chooseN0 γ))`. Let
  `B0 := exp(2·B·T*)·T*`  (bound from the crude estimate on `[0, T*]`).
Let `B_zr := max (max B0 (2/γ)) 1 + 1`. Then `z_r(t) ≤ B_zr` for all `t ≥ 0`.

On `[0, T*]`: `z_r(t) ≤ B0 ≤ B_zr` by `crude_bound`.
On `(T*, ∞)`: applying `decay_bound` with `T := T*` and `U := max B0 (2/γ)`
yields `z_r(t) ≤ U ≤ B_zr`.
-/

namespace zrTraj

variable {γ : ℝ} (D : DriverData γ)

/-- The phase boundary `T* := max 0 (D.diffMod (chooseN0 γ) + 1)`.
Adding `+ 1` ensures `T* > D.diffMod (chooseN0 γ)` strictly, so
`driver(s) ≥ γ/2` holds for all `s ≥ T*`. -/
noncomputable def Tstar : ℝ := max 0 (D.diffMod (chooseN0 γ) + 1)

lemma Tstar_nn : 0 ≤ Tstar D := le_max_left _ _

lemma Tstar_gt_diffMod : D.diffMod (chooseN0 γ) < Tstar D := by
  unfold Tstar
  have : D.diffMod (chooseN0 γ) + 1 ≤ max 0 (D.diffMod (chooseN0 γ) + 1) :=
    le_max_right _ _
  linarith

/-- Value of `B0 = exp(2·B·T*)·T*`, the crude bound on `[0, T*]`. -/
noncomputable def B0 : ℝ :=
  Real.exp (2 * D.driver_bound * Tstar D) * Tstar D

lemma B0_nn : 0 ≤ B0 D :=
  mul_nonneg (Real.exp_pos _).le (Tstar_nn D)

/-- The uniform bound `B_zr := max (max B0 (2/γ)) 1 + 1 > 0`. -/
noncomputable def Bzr : ℝ := max (max (B0 D) (2 / γ)) 1 + 1

lemma Bzr_pos : 0 < Bzr D := by
  unfold Bzr
  have : (1 : ℝ) ≤ max (max (B0 D) (2 / γ)) 1 := le_max_right _ _
  linarith

lemma Bzr_ge_B0 : B0 D ≤ Bzr D := by
  unfold Bzr
  have h1 : B0 D ≤ max (B0 D) (2 / γ) := le_max_left _ _
  have h2 : max (B0 D) (2 / γ) ≤ max (max (B0 D) (2 / γ)) 1 := le_max_left _ _
  linarith

lemma Bzr_ge_two_div_gamma : 2 / γ ≤ Bzr D := by
  unfold Bzr
  have h1 : 2 / γ ≤ max (B0 D) (2 / γ) := le_max_right _ _
  have h2 : max (B0 D) (2 / γ) ≤ max (max (B0 D) (2 / γ)) 1 := le_max_left _ _
  linarith

/-- Uniform upper bound: for `γ > 0`, `z_r(t) ≤ B_zr` for all `t ≥ 0`. -/
lemma uniform_bound (hγ : 0 < γ) {t : ℝ} (ht : 0 ≤ t) :
    zrTraj D t ≤ Bzr D := by
  by_cases htT : t ≤ Tstar D
  · -- Phase 1: crude bound.
    have hbd := crude_bound D ht
    have hmono : Real.exp (2 * D.driver_bound * t) * t
        ≤ Real.exp (2 * D.driver_bound * Tstar D) * Tstar D := by
      apply mul_le_mul
      · apply Real.exp_le_exp.mpr
        have h2B_nn : 0 ≤ 2 * D.driver_bound := by linarith [D.driver_bound_nn]
        exact mul_le_mul_of_nonneg_left htT h2B_nn
      · exact htT
      · exact ht
      · exact (Real.exp_pos _).le
    have hB0 : zrTraj D t ≤ B0 D := le_trans hbd hmono
    linarith [Bzr_ge_B0 D]
  · -- Phase 2: decay bound past T*.
    push_neg at htT
    -- Apply decay_bound with T := Tstar D, U := max (B0 D) (2/γ).
    set U : ℝ := max (B0 D) (2 / γ) with hU_def
    have hU_ge : 2 / γ ≤ U := le_max_right _ _
    have hU_nn : 0 ≤ U := le_trans (by positivity : (0:ℝ) ≤ 2/γ) hU_ge
    have hzT_le : zrTraj D (Tstar D) ≤ U := by
      have hTstar := crude_bound D (Tstar_nn D)
      have hB0_le_U : B0 D ≤ U := le_max_left _ _
      have : zrTraj D (Tstar D) ≤ B0 D := hTstar
      linarith
    have hzT_nn : 0 ≤ zrTraj D (Tstar D) := nonneg D (Tstar_nn D)
    have hdriver_ge : ∀ s, Tstar D ≤ s → s ≤ t → γ / 2 ≤ D.driver s := by
      intro s hTs _hst
      have hs_nn : 0 ≤ s := le_trans (Tstar_nn D) hTs
      have hs_gt : s > D.diffMod (chooseN0 γ) :=
        lt_of_lt_of_le (Tstar_gt_diffMod D) hTs
      exact driver_ge_half_gamma_past_Tstar hγ D hs_nn hs_gt
    -- Decay gives z_r(t) ≤ exp(-(γ/2)(t-Tstar))·z_r(Tstar) + (2/γ)·(1 - exp(..)).
    have hdec := decay_bound D hγ (Tstar_nn D) (le_of_lt htT) hzT_nn hdriver_ge
    -- Bound each term by U.
    have hγ2_pos : 0 < γ / 2 := by linarith
    have hExp_nn : 0 ≤ Real.exp (-(γ / 2) * (t - Tstar D)) := (Real.exp_pos _).le
    have hExp_le : Real.exp (-(γ / 2) * (t - Tstar D)) ≤ 1 := by
      rw [show (1 : ℝ) = Real.exp 0 from Real.exp_zero.symm]
      apply Real.exp_le_exp.mpr
      have : 0 ≤ (γ / 2) * (t - Tstar D) :=
        mul_nonneg hγ2_pos.le (by linarith)
      linarith
    have hOneSub_nn : 0 ≤ 1 - Real.exp (-(γ / 2) * (t - Tstar D)) := by linarith
    -- z_r(t) ≤ exp(..)·U + (2/γ)·(1 - exp(..)) ≤ exp(..)·U + U·(1 - exp(..)) = U.
    have hFirst_le : Real.exp (-(γ / 2) * (t - Tstar D)) * zrTraj D (Tstar D)
        ≤ Real.exp (-(γ / 2) * (t - Tstar D)) * U :=
      mul_le_mul_of_nonneg_left hzT_le hExp_nn
    have hSecond_le : (2 / γ) * (1 - Real.exp (-(γ / 2) * (t - Tstar D)))
        ≤ U * (1 - Real.exp (-(γ / 2) * (t - Tstar D))) :=
      mul_le_mul_of_nonneg_right hU_ge hOneSub_nn
    have hCombined : zrTraj D t ≤ U := by
      have hsum : Real.exp (-(γ / 2) * (t - Tstar D)) * U
          + U * (1 - Real.exp (-(γ / 2) * (t - Tstar D))) = U := by ring
      linarith
    -- U ≤ Bzr D.
    have hU_le_Bzr : U ≤ Bzr D := by
      unfold Bzr
      have h1 : U ≤ max U 1 := le_max_left _ _
      linarith
    linarith

end zrTraj

/-! ## Convergence of `z_r` to `1/γ`.

Strategy: apply `decay_upper` with `c := γ - ε` and `decay_lower` with
`c := γ + ε` on `[T, t]` where `T := max (Tstar D) (D.diffMod Nr)` for a
suitably large `Nr : ℕ` depending on `r`. This sandwiches `z_r(t)`:

  1/(γ+ε) - transient ≤ z_r(t) ≤ 1/(γ-ε) + transient

so `|z_r(t) - 1/γ| ≤ ε·(2/γ²) + transient ≤ exp(-r)`.

We pick:
  * `Nr := chooseN0 γ + r + 2` (so `ε = exp(-Nr) ≤ γ/4` and `4ε/γ² ≤ exp(-r)`).
  * `Tr := max (Tstar D) (D.diffMod Nr + 1)`.
  * modulus `r := Tr + (2/γ)·(r + log(2·(Bzr + 2/γ)) + 1)`.

**Remark.** Instead of chasing the tightest possible constants, we pick
generous "slack" parameters so that each inequality is proved by a clean
`linarith`/`nlinarith`, avoiding brittle precision issues.
-/

namespace zrTraj

variable {γ : ℝ} (D : DriverData γ)

/-- Auxiliary: for `T ≥ Tstar D` and `t ≥ T` with `|driver(s) - γ| ≤ ε` on
`[T, t]` (with `0 < ε < γ`), we have the two-sided bound
  `|z_r(t) - 1/γ| ≤ ε/(γ·(γ-ε)) + (z_r(T) + 1/(γ-ε)) · exp(-(γ-ε)·(t-T))`.
Obtained by combining `decay_upper` (c := γ-ε) and `decay_lower` (c := γ+ε). -/
lemma two_sided_bound {T t ε : ℝ} (hγ : 0 < γ) (hε_pos : 0 < ε) (hε_lt : ε < γ)
    (hT_nn : 0 ≤ T) (hTt : T ≤ t)
    (hzT_nn : 0 ≤ zrTraj D T)
    (hdriver_close : ∀ s, T ≤ s → s ≤ t → |D.driver s - γ| ≤ ε) :
    |zrTraj D t - 1 / γ|
      ≤ ε / (γ * (γ - ε))
        + (zrTraj D T + 1 / (γ - ε)) * Real.exp (-(γ - ε) * (t - T)) := by
  have hγ_pos : 0 < γ := hγ
  have hγε_pos : 0 < γ - ε := by linarith
  have hγε_sum_pos : 0 < γ + ε := by linarith
  -- driver on [T, t]: γ - ε ≤ driver(s) ≤ γ + ε.
  have hd_ge : ∀ s, T ≤ s → s ≤ t → γ - ε ≤ D.driver s := by
    intro s hTs hst
    have := hdriver_close s hTs hst
    have : -ε ≤ D.driver s - γ := (abs_le.mp this).1
    linarith
  have hd_le : ∀ s, T ≤ s → s ≤ t → D.driver s ≤ γ + ε := by
    intro s hTs hst
    have := hdriver_close s hTs hst
    have : D.driver s - γ ≤ ε := (abs_le.mp this).2
    linarith
  -- Upper bound.
  have hUpper := decay_upper D hγε_pos hT_nn hTt hzT_nn hd_ge
  -- Lower bound.
  have hLower := decay_lower D hγε_sum_pos hT_nn hTt hzT_nn hd_le
  -- Exp decay bounds.
  have hExp1_nn : 0 ≤ Real.exp (-(γ - ε) * (t - T)) := (Real.exp_pos _).le
  have hExp2_nn : 0 ≤ Real.exp (-(γ + ε) * (t - T)) := (Real.exp_pos _).le
  have hExp1_le : Real.exp (-(γ - ε) * (t - T)) ≤ 1 := by
    rw [show (1:ℝ) = Real.exp 0 from Real.exp_zero.symm]
    apply Real.exp_le_exp.mpr
    have : 0 ≤ (γ - ε) * (t - T) := mul_nonneg hγε_pos.le (by linarith)
    linarith
  have hExp2_le : Real.exp (-(γ + ε) * (t - T)) ≤ 1 := by
    rw [show (1:ℝ) = Real.exp 0 from Real.exp_zero.symm]
    apply Real.exp_le_exp.mpr
    have : 0 ≤ (γ + ε) * (t - T) := mul_nonneg hγε_sum_pos.le (by linarith)
    linarith
  -- The key algebraic steps:
  --   z_r(t) - 1/γ ≤ [1/(γ-ε) - 1/γ] + exp(-(γ-ε)(t-T))·(z_r(T) - 1/(γ-ε))
  --                = ε/(γ(γ-ε)) + exp(-(γ-ε)(t-T))·(z_r(T) - 1/(γ-ε))
  --   z_r(t) - 1/γ ≥ [1/(γ+ε) - 1/γ] + exp(-(γ+ε)(t-T))·(z_r(T) - 1/(γ+ε))
  --                = -ε/(γ(γ+ε)) + exp(-(γ+ε)(t-T))·(z_r(T) - 1/(γ+ε))
  --
  -- Both |errors| ≤ ε/(γ(γ-ε)) since γ+ε > γ-ε.
  -- Transient: |z_r(T) - 1/(γ±ε)| ≤ z_r(T) + 1/(γ-ε).
  -- Using max of exp(-(γ±ε)(t-T)) ≤ exp(-(γ-ε)(t-T)) since γ - ε ≤ γ + ε.
  have hExpMono : Real.exp (-(γ + ε) * (t - T)) ≤ Real.exp (-(γ - ε) * (t - T)) := by
    apply Real.exp_le_exp.mpr
    have : -(γ + ε) * (t - T) ≤ -(γ - ε) * (t - T) := by
      have hdiff : -(γ + ε) - (-(γ - ε)) = -(2*ε) := by ring
      have h_neg : -(γ + ε) ≤ -(γ - ε) := by linarith
      exact mul_le_mul_of_nonneg_right h_neg (by linarith)
    exact this
  -- Algebraic massage: rewrite upper and lower bounds.
  have hUpper' : zrTraj D t - 1 / γ
      ≤ ε / (γ * (γ - ε))
        + Real.exp (-(γ - ε) * (t - T)) * (zrTraj D T - 1 / (γ - ε)) := by
    have h1 : (1 : ℝ) / (γ - ε) - 1 / γ = ε / (γ * (γ - ε)) := by
      field_simp
      ring
    have : Real.exp (-(γ - ε) * (t - T)) * zrTraj D T
        + 1 / (γ - ε) * (1 - Real.exp (-(γ - ε) * (t - T)))
        = 1 / (γ - ε) + Real.exp (-(γ - ε) * (t - T)) * (zrTraj D T - 1 / (γ - ε)) := by
      ring
    rw [this] at hUpper
    linarith
  have hLower' : -(ε / (γ * (γ + ε)))
        + Real.exp (-(γ + ε) * (t - T)) * (zrTraj D T - 1 / (γ + ε))
      ≤ zrTraj D t - 1 / γ := by
    have h1 : (1 : ℝ) / (γ + ε) - 1 / γ = -(ε / (γ * (γ + ε))) := by
      field_simp
      ring
    have : Real.exp (-(γ + ε) * (t - T)) * zrTraj D T
        + 1 / (γ + ε) * (1 - Real.exp (-(γ + ε) * (t - T)))
        = 1 / (γ + ε) + Real.exp (-(γ + ε) * (t - T)) * (zrTraj D T - 1 / (γ + ε)) := by
      ring
    rw [this] at hLower
    linarith
  -- Now bound |z_r(t) - 1/γ| by max of upper-side and lower-side.
  -- Upper side: ε/(γ(γ-ε)) + exp(-(γ-ε)(t-T))·(z_r(T) + |1/(γ-ε)|).
  -- Lower side: ε/(γ(γ+ε)) + exp(-(γ+ε)(t-T))·(z_r(T) + |1/(γ+ε)|).
  -- Use ε/(γ(γ+ε)) ≤ ε/(γ(γ-ε)) and the exp monotonicity.
  have hγε_inv_pos : 0 < 1 / (γ - ε) := by positivity
  have hγε_sum_inv_pos : 0 < 1 / (γ + ε) := by positivity
  have hγε_sum_inv_le : 1 / (γ + ε) ≤ 1 / (γ - ε) := by
    apply one_div_le_one_div_of_le hγε_pos
    linarith
  have hErr_common : ε / (γ * (γ + ε)) ≤ ε / (γ * (γ - ε)) := by
    apply div_le_div_of_nonneg_left hε_pos.le
    · positivity
    · apply mul_le_mul_of_nonneg_left _ hγ_pos.le
      linarith
  -- Upper: z_r(t) - 1/γ ≤ ε/(γ(γ-ε)) + exp(-(γ-ε)(t-T))·(z_r(T) + 1/(γ-ε)).
  have hUpperBd : zrTraj D t - 1 / γ
      ≤ ε / (γ * (γ - ε))
        + (zrTraj D T + 1 / (γ - ε)) * Real.exp (-(γ - ε) * (t - T)) := by
    have h_coef : zrTraj D T - 1 / (γ - ε) ≤ zrTraj D T + 1 / (γ - ε) := by linarith
    have h_coef_nn : 0 ≤ zrTraj D T + 1 / (γ - ε) := by linarith
    have hstep : Real.exp (-(γ - ε) * (t - T)) * (zrTraj D T - 1 / (γ - ε))
        ≤ (zrTraj D T + 1 / (γ - ε)) * Real.exp (-(γ - ε) * (t - T)) := by
      have h1 : Real.exp (-(γ - ε) * (t - T)) * (zrTraj D T - 1 / (γ - ε))
          ≤ Real.exp (-(γ - ε) * (t - T)) * (zrTraj D T + 1 / (γ - ε)) :=
        mul_le_mul_of_nonneg_left h_coef hExp1_nn
      linarith
    linarith
  -- Lower: z_r(t) - 1/γ ≥ -ε/(γ(γ+ε)) - exp(-(γ+ε)(t-T))·(z_r(T) + 1/(γ+ε)).
  -- Rewrite: -(z_r(t) - 1/γ) ≤ ε/(γ(γ+ε)) + exp(-(γ+ε)(t-T))·(z_r(T) + 1/(γ+ε)).
  --                         ≤ ε/(γ(γ-ε)) + exp(-(γ-ε)(t-T))·(z_r(T) + 1/(γ-ε)).
  have hLowerBd : -(zrTraj D t - 1 / γ)
      ≤ ε / (γ * (γ - ε))
        + (zrTraj D T + 1 / (γ - ε)) * Real.exp (-(γ - ε) * (t - T)) := by
    -- Use hLower': -(ε/(γ(γ+ε))) + exp·(z_r(T) - 1/(γ+ε)) ≤ z_r(t) - 1/γ.
    -- So -(z_r(t)-1/γ) ≤ ε/(γ(γ+ε)) - exp·(z_r(T) - 1/(γ+ε))
    --                 = ε/(γ(γ+ε)) + exp·(1/(γ+ε) - z_r(T))
    -- Bound: 1/(γ+ε) - z_r(T) ≤ 1/(γ+ε) ≤ 1/(γ-ε) ≤ z_r(T) + 1/(γ-ε) (since z_r(T) ≥ 0).
    have hkey : -(zrTraj D t - 1 / γ)
        ≤ ε / (γ * (γ + ε))
          + Real.exp (-(γ + ε) * (t - T)) * (1 / (γ + ε) - zrTraj D T) := by
      have h1 : -(zrTraj D t - 1 / γ)
          ≤ ε / (γ * (γ + ε))
            + -(Real.exp (-(γ + ε) * (t - T)) * (zrTraj D T - 1 / (γ + ε))) := by
        linarith
      have h2 : -(Real.exp (-(γ + ε) * (t - T)) * (zrTraj D T - 1 / (γ + ε)))
          = Real.exp (-(γ + ε) * (t - T)) * (1 / (γ + ε) - zrTraj D T) := by ring
      linarith
    -- ε/(γ(γ+ε)) ≤ ε/(γ(γ-ε)).
    have hbd_err : ε / (γ * (γ + ε)) ≤ ε / (γ * (γ - ε)) := hErr_common
    -- exp(-(γ+ε)(t-T))·(1/(γ+ε) - z_r(T)) ≤ exp(-(γ-ε)(t-T))·(z_r(T) + 1/(γ-ε)).
    have hbd_trans : Real.exp (-(γ + ε) * (t - T)) * (1 / (γ + ε) - zrTraj D T)
        ≤ Real.exp (-(γ - ε) * (t - T)) * (zrTraj D T + 1 / (γ - ε)) := by
      by_cases hdiff : 1 / (γ + ε) - zrTraj D T ≤ 0
      · -- LHS ≤ 0 since hExp2_nn, RHS ≥ 0.
        have hLHS_le : Real.exp (-(γ + ε) * (t - T)) * (1 / (γ + ε) - zrTraj D T) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hExp2_nn hdiff
        have hRHS_nn : 0 ≤ Real.exp (-(γ - ε) * (t - T)) * (zrTraj D T + 1 / (γ - ε)) :=
          mul_nonneg hExp1_nn (by linarith)
        linarith
      · push_neg at hdiff
        have hcoef_le : 1 / (γ + ε) - zrTraj D T ≤ zrTraj D T + 1 / (γ - ε) := by
          have : zrTraj D T - (1 / (γ + ε) - zrTraj D T) + 1 / (γ - ε) ≥ 0 := by
            have h := hzT_nn
            have : (2:ℝ) * zrTraj D T ≥ 0 := by linarith
            have h1 : 1 / (γ - ε) - 1 / (γ + ε) ≥ 0 := by linarith
            linarith
          linarith
        have h1 : Real.exp (-(γ + ε) * (t - T)) * (1 / (γ + ε) - zrTraj D T)
            ≤ Real.exp (-(γ - ε) * (t - T)) * (1 / (γ + ε) - zrTraj D T) :=
          mul_le_mul_of_nonneg_right hExpMono hdiff.le
        have h2 : Real.exp (-(γ - ε) * (t - T)) * (1 / (γ + ε) - zrTraj D T)
            ≤ Real.exp (-(γ - ε) * (t - T)) * (zrTraj D T + 1 / (γ - ε)) :=
          mul_le_mul_of_nonneg_left hcoef_le hExp1_nn
        linarith
    linarith
  -- Combine via abs_le.
  exact abs_le.mpr ⟨by linarith, hUpperBd⟩

end zrTraj

/-! ## Picking the convergence modulus.

Given the two-sided bound, we pick `ε := exp(-Nr)` with
`Nr := 2 · chooseN0 γ + r + 2`.  Since `exp(-chooseN0 γ) ≤ γ/2`, we get
`ε ≤ (γ/2)² · exp(-(r+2)) = γ² · exp(-r) · exp(-2) / 4`.

Then for piece 1 of `two_sided_bound`:
  `ε / (γ(γ-ε)) ≤ (4/3) · ε / γ²` (using `γ-ε ≥ 3γ/4` from `ε ≤ γ/4`)
              ` ≤ (1/3) · exp(-r) · exp(-2) ≤ exp(-r)/3`.

For piece 2:
  `(z_r(T) + 1/(γ-ε)) · exp(-(γ-ε)(t-T)) ≤ 2·Bzr·exp(-(γ/2)(t-T))`
  (using `γ-ε ≥ γ/2` and `1/(γ-ε) ≤ 2/γ ≤ Bzr`).
  For this to be `≤ exp(-r)/3`, need
  `t - T ≥ (2/γ) · (r + log(6·Bzr))`.
-/

namespace zrTraj

variable {γ : ℝ} (D : DriverData γ)

/-- Convergence modulus for `z_r → 1/γ`.

`zrModulus r := max (Tstar D + 1) (D.diffMod (2·chooseN0 γ + r + 2) + 1)
               + (4 / γ) · (r + Real.log (6 · Bzr D) + 1)`.

The `4/γ` factor plays the role of `1/(γ/2)` in the decay rate (we use
`γ - ε ≥ γ/2` since `ε ≤ γ/4`).  The `2·chooseN0 γ` part of `Nr`
compensates the `1/γ²` denominator in piece 1. -/
noncomputable def zrModulus (r : ℕ) : ℝ :=
  max (Tstar D + 1) (D.diffMod (2 * chooseN0 γ + r + 2) + 1)
    + (4 / γ) * ((r : ℝ) + Real.log (6 * Bzr D) + 1)

-- We briefly need `exp(-2) ≤ 1/2`.
private lemma exp_neg_two_le_half : Real.exp (-(2:ℝ)) ≤ 1 / 2 := by
  rw [Real.exp_neg]
  rw [show (1:ℝ)/2 = (2:ℝ)⁻¹ by ring]
  apply inv_anti₀ (by norm_num : (0:ℝ) < 2)
  have h2e : (2:ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_lt_exp (x := (1:ℝ)) (by norm_num)
    linarith
  have h_exp_mono : Real.exp 1 ≤ Real.exp 2 :=
    Real.exp_le_exp.mpr (by norm_num)
  linarith

set_option maxHeartbeats 4000000 in
-- Heartbeat bump: this proof combines the full two-sided Duhamel analysis
-- with the explicit ε = exp(-(2·N0+r+2)) choice and both piece-1 and piece-2
-- bookkeeping inline.  Splitting would require exposing >15 numeric
-- intermediate lemmas; the current form is clearer at the cost of time.
/-- **Main convergence theorem for Stage A.**

For every precision level `r`, past `zrModulus D r`, `z_r(t)` is within
`exp(-r)` of `1/γ`. -/
theorem zr_converges (hγ : 0 < γ) (hγ_hi : γ < 1) :
    ∀ r : ℕ, ∀ t : ℝ, t > zrModulus D r →
      |zrTraj D t - 1 / γ| < Real.exp (-(r : ℝ)) := by
  intro r t ht
  -- Setup.
  set Nr : ℕ := 2 * chooseN0 γ + r + 2 with hNr_def
  set ε : ℝ := Real.exp (-(Nr : ℝ)) with hε_def
  set T : ℝ := max (Tstar D + 1) (D.diffMod Nr + 1) with hT_def
  have hTstar_le : Tstar D + 1 ≤ T := le_max_left _ _
  have hDiffMod_le : D.diffMod Nr + 1 ≤ T := le_max_right _ _
  -- T ≥ 0.
  have hT_nn : 0 ≤ T := by
    have h := Tstar_nn D
    linarith [hTstar_le]
  -- Positive reals we need throughout.
  have hε_pos : 0 < ε := Real.exp_pos _
  have hExpR_pos : 0 < Real.exp (-(r : ℝ)) := Real.exp_pos _
  -- Unit bounds we reuse.
  have h_exp_r_le : Real.exp (-(r : ℝ)) ≤ 1 := by
    rw [show (1:ℝ) = Real.exp 0 from Real.exp_zero.symm]
    apply Real.exp_le_exp.mpr
    have : 0 ≤ (r : ℝ) := by positivity
    linarith
  have h_exp_2 : Real.exp (-(2:ℝ)) ≤ 1 / 2 := exp_neg_two_le_half
  have h_N0 : Real.exp (-(chooseN0 γ : ℝ)) ≤ γ / 2 := chooseN0_spec hγ
  have h_N0_nn : 0 ≤ Real.exp (-(chooseN0 γ : ℝ)) := (Real.exp_pos _).le
  -- Decompose ε into the three factors.
  have hε_split : ε =
      (Real.exp (-(chooseN0 γ : ℝ))) * (Real.exp (-(chooseN0 γ : ℝ)))
        * Real.exp (-(r:ℝ)) * Real.exp (-(2:ℝ)) := by
    rw [hε_def]
    rw [show (-(Nr : ℝ)) = -((chooseN0 γ : ℝ)) + (-(chooseN0 γ : ℝ))
        + (-(r : ℝ)) + (-(2 : ℝ)) from by
      show -(((2 * chooseN0 γ + r + 2 : ℕ) : ℝ)) = _
      push_cast; ring]
    rw [Real.exp_add, Real.exp_add, Real.exp_add]
  -- Bound ε ≤ (γ/2)² · exp(-r) · (1/2) = γ²·exp(-r)/8.
  have hε_le_key : ε ≤ γ^2 * Real.exp (-(r:ℝ)) / 8 := by
    rw [hε_split]
    have hp1 := h_N0
    have hp1_nn := h_N0_nn
    have hp_rn : 0 ≤ Real.exp (-(r:ℝ)) := (Real.exp_pos _).le
    have hp_2n : 0 ≤ Real.exp (-(2:ℝ)) := (Real.exp_pos _).le
    have hγ2_nn : 0 ≤ γ / 2 := by linarith
    -- step: exp(-N0)·exp(-N0) ≤ (γ/2)·(γ/2)
    have step1 : Real.exp (-(chooseN0 γ : ℝ)) * Real.exp (-(chooseN0 γ : ℝ))
        ≤ (γ/2) * (γ/2) := mul_le_mul hp1 hp1 hp1_nn hγ2_nn
    have step1_nn : 0 ≤ Real.exp (-(chooseN0 γ : ℝ)) * Real.exp (-(chooseN0 γ : ℝ)) :=
      mul_nonneg hp1_nn hp1_nn
    -- step: · exp(-r) ≤ (γ/2)²·1
    have step2 : Real.exp (-(chooseN0 γ : ℝ)) * Real.exp (-(chooseN0 γ : ℝ))
        * Real.exp (-(r:ℝ)) ≤ (γ/2)*(γ/2) * 1 :=
      mul_le_mul step1 h_exp_r_le hp_rn (by positivity)
    have step2_nn : 0 ≤ Real.exp (-(chooseN0 γ : ℝ)) * Real.exp (-(chooseN0 γ : ℝ))
        * Real.exp (-(r:ℝ)) := mul_nonneg step1_nn hp_rn
    have step3 :
        Real.exp (-(chooseN0 γ : ℝ)) * Real.exp (-(chooseN0 γ : ℝ))
          * Real.exp (-(r:ℝ)) * Real.exp (-(2:ℝ))
        ≤ (γ/2) * (γ/2) * 1 * (1/2) := by
      -- Mix: step2 paired with h_exp_2.
      have := mul_le_mul (a := Real.exp (-(chooseN0 γ : ℝ)) * Real.exp (-(chooseN0 γ : ℝ))
            * Real.exp (-(r:ℝ))) (b := (γ/2)*(γ/2) * 1)
          (c := Real.exp (-(2:ℝ))) (d := 1/2) step2 h_exp_2 hp_2n (by positivity)
      -- Issue: we want exp-r times exp-r without swap. The product is already in order.
      -- Regroup:
      simpa using this
    -- But we want exp(-r) factor not reduced to 1. Redo: simplify right side then
    -- replace 1 by exp(-r) explicitly after.  Instead, rearrange factors:
    -- LHS = (exp-N0 · exp-N0) · exp-r · exp-2, so bound (exp-N0·exp-N0)·exp-2 first.
    -- Alternative clean approach:
    have hLHS : Real.exp (-(chooseN0 γ : ℝ)) * Real.exp (-(chooseN0 γ : ℝ))
        * Real.exp (-(r:ℝ)) * Real.exp (-(2:ℝ))
        ≤ (γ/2) * (γ/2) * Real.exp (-(r:ℝ)) * (1/2) := by
      have ha : Real.exp (-(chooseN0 γ : ℝ)) * Real.exp (-(chooseN0 γ : ℝ))
          ≤ (γ/2) * (γ/2) := step1
      have hb : Real.exp (-(r:ℝ)) ≤ Real.exp (-(r:ℝ)) := le_refl _
      have hc : Real.exp (-(2:ℝ)) ≤ (1/2) := h_exp_2
      have hab : Real.exp (-(chooseN0 γ : ℝ)) * Real.exp (-(chooseN0 γ : ℝ))
          * Real.exp (-(r:ℝ)) ≤ (γ/2) * (γ/2) * Real.exp (-(r:ℝ)) :=
        mul_le_mul_of_nonneg_right ha hp_rn
      have hab_nn : 0 ≤ Real.exp (-(chooseN0 γ : ℝ)) * Real.exp (-(chooseN0 γ : ℝ))
          * Real.exp (-(r:ℝ)) := step2_nn
      have : Real.exp (-(chooseN0 γ : ℝ)) * Real.exp (-(chooseN0 γ : ℝ))
          * Real.exp (-(r:ℝ)) * Real.exp (-(2:ℝ))
          ≤ (γ/2) * (γ/2) * Real.exp (-(r:ℝ)) * (1/2) :=
        mul_le_mul hab hc hp_2n (by positivity)
      exact this
    have hRHS_eq : (γ/2) * (γ/2) * Real.exp (-(r:ℝ)) * (1/2) = γ^2 * Real.exp (-(r:ℝ)) / 8 := by
      ring
    linarith [hLHS, hRHS_eq.symm ▸ (le_refl ((γ/2) * (γ/2) * Real.exp (-(r:ℝ)) * (1/2)))]
  -- From ε ≤ γ²·exp(-r)/8 and γ < 1, exp(-r) ≤ 1: ε ≤ γ²/8 ≤ γ/8.
  have hγ2_pos : 0 < γ^2 := by positivity
  have hγ2_le_γ : γ^2 ≤ γ := by nlinarith [hγ, hγ_hi]
  have hε_le_γ8 : ε ≤ γ / 8 := by
    have h1 : γ^2 * Real.exp (-(r:ℝ)) ≤ γ^2 * 1 :=
      mul_le_mul_of_nonneg_left h_exp_r_le hγ2_pos.le
    have h2 : γ^2 * 1 ≤ γ := by linarith
    linarith
  have hε_le_γ4 : ε ≤ γ / 4 := by linarith
  have hε_lt_γ : ε < γ := by linarith
  have hγε_pos : 0 < γ - ε := by linarith
  have hγε_ge_3γ4 : 3 * γ / 4 ≤ γ - ε := by linarith
  have hγε_ge_half : γ / 2 ≤ γ - ε := by linarith
  -- Check T ≥ Tstar D and T > D.diffMod Nr.
  have hT_ge_Tstar : Tstar D ≤ T := by linarith
  have hT_gt_diffMod : D.diffMod Nr < T := by linarith
  -- Bzr ≥ 2 (since Bzr := max _ 1 + 1 ≥ 2).
  have hBzr_ge2 : 2 ≤ Bzr D := by
    unfold Bzr
    have : (1:ℝ) ≤ max (max (B0 D) (2/γ)) 1 := le_max_right _ _
    linarith
  have hBzr_pos : 0 < Bzr D := by linarith
  -- log(6·Bzr) ≥ log 12 > 0.
  have hlog_nn : 0 ≤ Real.log (6 * Bzr D) := by
    apply Real.log_nonneg
    have : (6:ℝ) * Bzr D ≥ 6 * 2 := by
      apply mul_le_mul_of_nonneg_left hBzr_ge2 (by norm_num)
    linarith
  have h4γ_pos : 0 < 4 / γ := by positivity
  have htmod_nn : 0 ≤ (4 / γ) * ((r : ℝ) + Real.log (6 * Bzr D) + 1) := by
    have : (0:ℝ) ≤ (r:ℝ) := by positivity
    have hsum_nn : 0 ≤ (r : ℝ) + Real.log (6 * Bzr D) + 1 := by linarith
    exact mul_nonneg h4γ_pos.le hsum_nn
  have hTt : T ≤ t := by
    unfold zrModulus at ht
    linarith
  -- Apply two_sided_bound.  For s ∈ [T, t], s > D.diffMod Nr, so |driver(s) - γ| ≤ exp(-Nr) = ε.
  have hdriver_close : ∀ s, T ≤ s → s ≤ t → |D.driver s - γ| ≤ ε := by
    intro s hTs _hst
    have hs_nn : 0 ≤ s := le_trans hT_nn hTs
    have hs_gt : s > D.diffMod Nr := lt_of_lt_of_le hT_gt_diffMod hTs
    exact (D.diffMod_conv Nr s hs_nn hs_gt).le
  have hzT_nn : 0 ≤ zrTraj D T := nonneg D hT_nn
  have hzT_le : zrTraj D T ≤ Bzr D := uniform_bound D hγ hT_nn
  have hbound := two_sided_bound D hγ hε_pos hε_lt_γ hT_nn hTt hzT_nn hdriver_close
  -- ================================================================
  -- Piece 1 bound: ε / (γ(γ-ε)) ≤ exp(-r)/3.
  -- ================================================================
  have hP1 : ε / (γ * (γ - ε)) ≤ Real.exp (-(r:ℝ)) / 3 := by
    -- ε/(γ(γ-ε)) ≤ (4/3)·ε/γ² (since γ-ε ≥ 3γ/4 > 0).
    have hγγ_ε_pos : 0 < γ * (γ - ε) := mul_pos hγ hγε_pos
    have h34γ2_pos : 0 < γ * (3 * γ / 4) := by positivity
    have hbd1 : ε / (γ * (γ - ε)) ≤ ε / (γ * (3 * γ / 4)) := by
      apply div_le_div_of_nonneg_left hε_pos.le h34γ2_pos
      exact mul_le_mul_of_nonneg_left hγε_ge_3γ4 hγ.le
    -- ε / (γ · 3γ/4) = 4ε/(3γ²).
    have hbd1_eq : ε / (γ * (3 * γ / 4)) = 4 * ε / (3 * γ^2) := by
      field_simp
    -- 4ε/(3γ²) ≤ 4·(γ²·exp(-r)/8)/(3γ²) = exp(-r)/6.
    have hbd2 : 4 * ε / (3 * γ^2) ≤ 4 * (γ^2 * Real.exp (-(r:ℝ)) / 8) / (3 * γ^2) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      linarith [hε_le_key]
    have hbd2_eq : 4 * (γ^2 * Real.exp (-(r:ℝ)) / 8) / (3 * γ^2)
        = Real.exp (-(r:ℝ)) / 6 := by
      field_simp
      ring
    -- Chain.
    have : ε / (γ * (γ - ε)) ≤ Real.exp (-(r:ℝ)) / 6 := by
      calc ε / (γ * (γ - ε))
          ≤ ε / (γ * (3 * γ / 4)) := hbd1
        _ = 4 * ε / (3 * γ^2) := hbd1_eq
        _ ≤ 4 * (γ^2 * Real.exp (-(r:ℝ)) / 8) / (3 * γ^2) := hbd2
        _ = Real.exp (-(r:ℝ)) / 6 := hbd2_eq
    linarith
  -- ================================================================
  -- Piece 2 bound: (z_r(T) + 1/(γ-ε)) · exp(-(γ-ε)(t-T)) < 2·exp(-r)/3.
  -- Actually we will show ≤ exp(-r)/3 but use < for final bound.
  -- Key: γ-ε ≥ γ/2, 1/(γ-ε) ≤ 2/γ ≤ Bzr, so coef ≤ 2·Bzr.
  -- Decay: exp(-(γ-ε)(t-T)) ≤ exp(-(γ/2)(t-T)).
  -- Need (γ/2)(t-T) ≥ log(6·Bzr) + r, i.e., (t-T) ≥ (2/γ)(log(6·Bzr) + r).
  -- htmod gives t - T ≥ (4/γ)·(r + log(6·Bzr) + 1) ≥ (2/γ)(r + log(6·Bzr) + 1) is wrong dir.
  -- We have (4/γ)·(...) ≥ (2/γ)·(...), good.
  -- ================================================================
  have hcoef_le : zrTraj D T + 1 / (γ - ε) ≤ 2 * Bzr D := by
    have h1 : 1 / (γ - ε) ≤ 2 / γ := by
      rw [div_le_div_iff₀ hγε_pos hγ]
      linarith
    have h2 : 2 / γ ≤ Bzr D := Bzr_ge_two_div_gamma D
    linarith
  have hcoef_nn : 0 ≤ zrTraj D T + 1 / (γ - ε) := by
    have : 0 ≤ 1 / (γ - ε) := by positivity
    linarith
  have hExpDecay_le : Real.exp (-(γ - ε) * (t - T)) ≤ Real.exp (-(γ/2) * (t - T)) := by
    apply Real.exp_le_exp.mpr
    have htT_nn : 0 ≤ t - T := by linarith
    have : γ/2 ≤ γ - ε := hγε_ge_half
    have hmul : (γ/2) * (t - T) ≤ (γ - ε) * (t - T) :=
      mul_le_mul_of_nonneg_right this htT_nn
    linarith
  have hExpDecay_nn : 0 ≤ Real.exp (-(γ/2) * (t - T)) := (Real.exp_pos _).le
  -- Bound exp(-(γ/2)(t-T)) ≤ exp(-r) / (6·Bzr).
  -- From htmod hypothesis: (4/γ)·(r + log(6·Bzr) + 1) ≤ t - T - max(...,...).
  -- So t - T ≥ max(...,...) + (4/γ)·(r + log(6·Bzr) + 1) ≥ 0 + (4/γ)·(r + log(6·Bzr) + 1).
  -- Hence (γ/2)(t-T) ≥ (γ/2)·(4/γ)·(r + log(6·Bzr) + 1) = 2·(r + log(6·Bzr) + 1).
  -- So exp(-(γ/2)(t-T)) ≤ exp(-2·(r+log(6Bzr)+1)).
  -- We want this ≤ exp(-r)/(6·Bzr·(1/2)) = exp(-r)/(3·Bzr). Actually we want
  -- 2·Bzr · exp(-(γ/2)(t-T)) ≤ exp(-r)/3, so exp(-(γ/2)(t-T)) ≤ exp(-r)/(6·Bzr).
  -- exp(-2·(r+log(6Bzr)+1)) ≤ exp(-(r+log(6Bzr))) = exp(-r)/(6·Bzr). Since r ≥ 0
  -- and log(6·Bzr) ≥ 0 and the extra '1' factor = exp(-2) absorbs, actually:
  -- We have exp(-2·(...)) ≤ exp(-(r+log(6·Bzr))) iff 2·(...) ≥ r+log(6·Bzr) iff
  -- 2r + 2·log(6·Bzr) + 2 ≥ r + log(6·Bzr), which gives r + log(6·Bzr) + 2 ≥ 0. ✓
  have htmT_ge : t - T ≥ (4 / γ) * ((r : ℝ) + Real.log (6 * Bzr D) + 1) := by
    have h1 : zrModulus D r ≥ T := by
      unfold zrModulus
      linarith
    have h2 : zrModulus D r
        = max (Tstar D + 1) (D.diffMod (2 * chooseN0 γ + r + 2) + 1)
          + (4 / γ) * ((r : ℝ) + Real.log (6 * Bzr D) + 1) := rfl
    linarith
  have hγ_tT_ge : (γ / 2) * (t - T) ≥ 2 * ((r : ℝ) + Real.log (6 * Bzr D) + 1) := by
    have hγ4_pos : 0 < γ / 2 := by linarith
    have := mul_le_mul_of_nonneg_left htmT_ge hγ4_pos.le
    -- (γ/2) · (4/γ) = 2.
    have heq : (γ / 2) * ((4 / γ) * ((r : ℝ) + Real.log (6 * Bzr D) + 1))
        = 2 * ((r : ℝ) + Real.log (6 * Bzr D) + 1) := by
      field_simp
      ring
    linarith
  -- Show exp(-(γ/2)(t-T)) ≤ exp(-r)/(6·Bzr).
  have h6Bzr_pos : 0 < 6 * Bzr D := by linarith
  have hlog_6Bzr : Real.log (6 * Bzr D) = Real.log (6 * Bzr D) := rfl
  have hExp_r_log : Real.exp (-(r : ℝ) - Real.log (6 * Bzr D)) = Real.exp (-(r:ℝ)) / (6 * Bzr D) := by
    have heq : (-(r : ℝ) - Real.log (6 * Bzr D)) = -(r:ℝ) + (-(Real.log (6 * Bzr D))) := by ring
    rw [heq, Real.exp_add]
    rw [show Real.exp (-(Real.log (6 * Bzr D))) = (6 * Bzr D)⁻¹ from by
      rw [Real.exp_neg, Real.exp_log h6Bzr_pos]]
    rw [div_eq_mul_inv]
  have hDecay_bd : Real.exp (-(γ/2) * (t - T)) ≤ Real.exp (-(r:ℝ)) / (6 * Bzr D) := by
    rw [← hExp_r_log]
    apply Real.exp_le_exp.mpr
    -- -(γ/2)(t-T) ≤ -r - log(6·Bzr)
    -- iff (γ/2)(t-T) ≥ r + log(6·Bzr).
    -- Have (γ/2)(t-T) ≥ 2r + 2·log(6·Bzr) + 2 ≥ r + log(6·Bzr) + (r + log(6·Bzr) + 2).
    have hrln_nn : 0 ≤ (r:ℝ) + Real.log (6 * Bzr D) + 2 := by
      have : (0:ℝ) ≤ (r:ℝ) := by positivity
      linarith
    have h1 : 2 * ((r : ℝ) + Real.log (6 * Bzr D) + 1)
        ≥ (r : ℝ) + Real.log (6 * Bzr D) := by linarith
    have h2 : (γ/2) * (t - T) ≥ (r : ℝ) + Real.log (6 * Bzr D) := by linarith
    linarith
  -- Combine: coef · decay ≤ 2·Bzr · exp(-r)/(6·Bzr) = exp(-r)/3.
  have hP2 : (zrTraj D T + 1 / (γ - ε)) * Real.exp (-(γ - ε) * (t - T))
      ≤ Real.exp (-(r:ℝ)) / 3 := by
    have h1 : (zrTraj D T + 1 / (γ - ε)) * Real.exp (-(γ - ε) * (t - T))
        ≤ (2 * Bzr D) * Real.exp (-(γ/2) * (t - T)) := by
      have ha : (zrTraj D T + 1 / (γ - ε)) * Real.exp (-(γ - ε) * (t - T))
          ≤ (2 * Bzr D) * Real.exp (-(γ - ε) * (t - T)) :=
        mul_le_mul_of_nonneg_right hcoef_le (Real.exp_pos _).le
      have hb : (2 * Bzr D) * Real.exp (-(γ - ε) * (t - T))
          ≤ (2 * Bzr D) * Real.exp (-(γ/2) * (t - T)) :=
        mul_le_mul_of_nonneg_left hExpDecay_le (by linarith)
      linarith
    have h2 : (2 * Bzr D) * Real.exp (-(γ/2) * (t - T))
        ≤ (2 * Bzr D) * (Real.exp (-(r:ℝ)) / (6 * Bzr D)) :=
      mul_le_mul_of_nonneg_left hDecay_bd (by linarith)
    have h3 : (2 * Bzr D) * (Real.exp (-(r:ℝ)) / (6 * Bzr D))
        = Real.exp (-(r:ℝ)) / 3 := by
      field_simp
      ring
    linarith
  -- Combine pieces.
  have hsum : |zrTraj D t - 1 / γ|
      ≤ Real.exp (-(r:ℝ)) / 3 + Real.exp (-(r:ℝ)) / 3 := by
    have := hbound
    linarith [hP1, hP2]
  -- Show exp(-r)/3 + exp(-r)/3 = 2·exp(-r)/3 < exp(-r).
  have hfinal : Real.exp (-(r:ℝ)) / 3 + Real.exp (-(r:ℝ)) / 3 < Real.exp (-(r:ℝ)) := by
    linarith [hExpR_pos]
  linarith

end zrTraj

/-! ## Main export theorem. -/

/-- **Main Stage A theorem.** Given a driver converging to `γ` (with `0 < γ < 1`),
there exists a `z_r` trajectory satisfying Stage A of Lemma 8:
existence + continuity + ODE + nonneg + bounded + exponential convergence to `1/γ`. -/
theorem zr_tracker_exists {γ : ℝ} (hγ_lo : 0 < γ) (hγ_hi : γ < 1)
    (D : DriverData γ) :
    ∃ (zr : ℝ → ℝ) (B_zr : ℝ) (zrMod : ℕ → ℝ),
      0 < B_zr ∧
      Continuous zr ∧
      zr 0 = 0 ∧
      (∀ t, 0 ≤ t → HasDerivAt zr (1 - D.driver t * zr t) t) ∧
      (∀ t, 0 ≤ t → 0 ≤ zr t) ∧
      (∀ t, 0 ≤ t → zr t ≤ B_zr) ∧
      (∀ r : ℕ, ∀ t : ℝ, t > zrMod r → |zr t - 1 / γ| < Real.exp (-(r : ℝ))) := by
  refine ⟨zrTraj D, zrTraj.Bzr D, zrTraj.zrModulus D, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact zrTraj.Bzr_pos D
  · exact zrTraj.continuous D
  · exact zrTraj.zero D
  · intro t _ht; exact zrTraj.hasDerivAt D t
  · intro t ht; exact zrTraj.nonneg D ht
  · intro t ht; exact zrTraj.uniform_bound D hγ_lo ht
  · exact zrTraj.zr_converges D hγ_lo hγ_hi

end Lemma8StageA
end DualRail
end Ripple
