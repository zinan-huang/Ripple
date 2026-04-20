/-
  Ripple.DualRail.Lemma8StageB — Stage B of the DNA25 Lemma 8 two-stage gadget.

  Given a converging `zr : ℝ → ℝ` (the Stage A reciprocal tracker) with
  `zr(t) → 1/γ` where `0 < γ < 1`, this file constructs the scalar ODE tracker

      z'(t) = 1 − zr(t) · z(t),    z(0) = 0

  and proves existence + continuity + non-negativity + uniform bound + exponential
  convergence `z(t) → γ`.

  The construction is the integrating-factor/Duhamel form:
    `A(t) := ∫_0^t zr(u) du`,
    `z(t) := exp(-A(t)) · ∫_0^t exp(A(s)) ds = ∫_0^t exp(-(A(t) - A(s))) ds`.

  Throughout, the "effective decay rate" is `1/(2γ)` (instead of `γ/2` in Stage A),
  since that is the eventual lower bound on the driver `zr`.  The steady-state
  value is therefore `1 / (1/(2γ)) = 2γ`, and the eventual target is `γ`.

  This file MIRRORS `Lemma8StageA.lean` almost verbatim:
    * `DriverData γ_A`          ↔ `ZrData γ`          (driver = zr, target = 1/γ)
    * `antideriv`                ↔ `zAntideriv`
    * `zrTraj`                   ↔ `zTraj`
    * `zrInner`                  ↔ `zInner`
    * `chooseN0 γ_A` : exp(-N0) ≤ γ_A/2  ↔  `chooseN0B γ` : exp(-N0) ≤ min(1/(2γ), γ/4)
    * `Bzr`                      ↔ `Bz`
    * `zrModulus`                ↔ `zModulus`
    * `zr_tracker_exists`        ↔ `z_tracker_exists`

  Reference: [RTCRN2] Huang–Klinge–Lathrop, DNA 25 (2019), Lemma 8, Stage B
  (subtraction layer).
-/

import Ripple.DualRail.Lemma8StageA

namespace Ripple
namespace DualRail
namespace Lemma8StageB

open MeasureTheory

/-! ## Input bundle -/

/-- Input bundle for Stage B: a converging reciprocal tracker `zr : ℝ → ℝ`
with target `1/γ`.  Produced by Stage A. -/
structure ZrData (γ : ℝ) where
  /-- The reciprocal tracker `zr(t)`. -/
  zr : ℝ → ℝ
  /-- Global continuity. -/
  zr_cont : Continuous zr
  /-- `zr(t) ≥ 0` for `t ≥ 0`. -/
  zr_nonneg : ∀ t, 0 ≤ t → 0 ≤ zr t
  /-- A uniform upper bound for `zr` on `[0, ∞)`. -/
  zr_bound : ℝ
  /-- The bound is positive. -/
  zr_bound_pos : 0 < zr_bound
  /-- `zr(t) ≤ zr_bound` on `[0, ∞)`. -/
  zr_abs_bd : ∀ t, 0 ≤ t → zr t ≤ zr_bound
  /-- Convergence modulus `zrModulus r`: past it, `|zr t − 1/γ| < exp(-r)`. -/
  zrModulus : ℕ → ℝ
  /-- Convergence: for `t > zrModulus r` with `t ≥ 0`,
      `|zr t − 1/γ| < exp(-r)`. -/
  zr_conv : ∀ r t, 0 ≤ t → t > zrModulus r →
      |zr t - 1 / γ| < Real.exp (-(r : ℝ))

namespace ZrData

variable {γ : ℝ} (Z : ZrData γ)

/-- Integrated driver `A(t) := ∫_0^t zr(u) du`. -/
noncomputable def antideriv (t : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..t, Z.zr u

@[simp] lemma antideriv_zero : Z.antideriv 0 = 0 := by
  unfold antideriv; simp

lemma zr_intervalIntegrable (a b : ℝ) :
    IntervalIntegrable Z.zr volume a b :=
  Z.zr_cont.intervalIntegrable a b

/-- FTC-1 on the driver: `A'(t) = zr(t)`. -/
lemma antideriv_hasDerivAt (t : ℝ) :
    HasDerivAt Z.antideriv (Z.zr t) t := by
  unfold antideriv
  have hii : IntervalIntegrable Z.zr volume 0 t :=
    Z.zr_intervalIntegrable 0 t
  have hmeas : StronglyMeasurableAtFilter Z.zr (nhds t) volume :=
    Z.zr_cont.stronglyMeasurableAtFilter _ _
  have hcontAt : ContinuousAt Z.zr t := Z.zr_cont.continuousAt
  exact intervalIntegral.integral_hasDerivAt_right hii hmeas hcontAt

lemma antideriv_continuous : Continuous Z.antideriv := by
  refine continuous_iff_continuousAt.mpr (fun t => ?_)
  exact (Z.antideriv_hasDerivAt t).continuousAt

/-- For `0 ≤ t`, `|A(t)| ≤ zr_bound · t`.  We use the pointwise bound `|zr| ≤ zr_bound`
valid on `[0, t]`. -/
lemma antideriv_abs_le {t : ℝ} (ht : 0 ≤ t) :
    |Z.antideriv t| ≤ Z.zr_bound * t := by
  unfold antideriv
  have habs : |∫ u in (0:ℝ)..t, Z.zr u|
      ≤ ∫ u in (0:ℝ)..t, |Z.zr u| :=
    intervalIntegral.abs_integral_le_integral_abs ht
  have hbound_ptw : ∀ u ∈ Set.Icc (0:ℝ) t,
      |Z.zr u| ≤ Z.zr_bound := by
    intro u hu
    have hu0 : 0 ≤ u := hu.1
    have h_nn : 0 ≤ Z.zr u := Z.zr_nonneg u hu0
    have h_le : Z.zr u ≤ Z.zr_bound := Z.zr_abs_bd u hu0
    rw [abs_of_nonneg h_nn]; exact h_le
  have h_abs_int : IntervalIntegrable (fun u => |Z.zr u|) volume 0 t :=
    Z.zr_cont.abs.intervalIntegrable 0 t
  have h_const_int : IntervalIntegrable (fun _ : ℝ => Z.zr_bound) volume 0 t :=
    continuous_const.intervalIntegrable 0 t
  have hle : (∫ u in (0:ℝ)..t, |Z.zr u|)
      ≤ ∫ u in (0:ℝ)..t, Z.zr_bound :=
    intervalIntegral.integral_mono_on ht h_abs_int h_const_int hbound_ptw
  have heval : ∫ _u in (0:ℝ)..t, Z.zr_bound = Z.zr_bound * t := by
    rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_comm]
  linarith

/-- For `0 ≤ T ≤ t` with `zr(u) ≥ c` on `[T, t]`,
`A(t) - A(T) ≥ c · (t - T)`. -/
lemma antideriv_diff_ge {T t c : ℝ} (hT_nn : 0 ≤ T) (hTt : T ≤ t)
    (hlb : ∀ u, T ≤ u → u ≤ t → c ≤ Z.zr u) :
    c * (t - T) ≤ Z.antideriv t - Z.antideriv T := by
  have hsplit : Z.antideriv t - Z.antideriv T = ∫ u in T..t, Z.zr u := by
    unfold antideriv
    have hii1 : IntervalIntegrable Z.zr volume 0 T := Z.zr_intervalIntegrable 0 T
    have hii2 : IntervalIntegrable Z.zr volume T t := Z.zr_intervalIntegrable T t
    have := intervalIntegral.integral_add_adjacent_intervals hii1 hii2
    linarith
  rw [hsplit]
  have h_const_int : IntervalIntegrable (fun _ : ℝ => c) volume T t :=
    continuous_const.intervalIntegrable T t
  have hii2 : IntervalIntegrable Z.zr volume T t := Z.zr_intervalIntegrable T t
  have hmono : (∫ _u in T..t, c) ≤ ∫ u in T..t, Z.zr u := by
    apply intervalIntegral.integral_mono_on hTt h_const_int hii2
    intro u hu; exact hlb u hu.1 hu.2
  have heval : (∫ _u in T..t, c) = c * (t - T) := by
    rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm]
  linarith

end ZrData

/-! ## Tracker `z` via integrating factor. -/

/-- Inner integral `I(t) := ∫_0^t exp(A(s)) ds`. -/
noncomputable def zInner {γ : ℝ} (Z : ZrData γ) : ℝ → ℝ :=
  fun t => ∫ s in (0 : ℝ)..t, Real.exp (Z.antideriv s)

/-- Stage-B tracker: `z(t) := exp(-A(t)) · I(t)`. -/
noncomputable def zTraj {γ : ℝ} (Z : ZrData γ) : ℝ → ℝ :=
  fun t => Real.exp (- Z.antideriv t) * zInner Z t

namespace zTraj

variable {γ : ℝ} (Z : ZrData γ)

lemma exp_antideriv_continuous : Continuous (fun s => Real.exp (Z.antideriv s)) :=
  Real.continuous_exp.comp Z.antideriv_continuous

lemma inner_continuous : Continuous (zInner Z) := by
  unfold zInner
  refine continuous_iff_continuousAt.mpr (fun t => ?_)
  have hcont := exp_antideriv_continuous Z
  have hii : IntervalIntegrable (fun s => Real.exp (Z.antideriv s)) volume 0 t :=
    hcont.intervalIntegrable 0 t
  have hmeas : StronglyMeasurableAtFilter (fun s => Real.exp (Z.antideriv s))
      (nhds t) volume := hcont.stronglyMeasurableAtFilter _ _
  exact (intervalIntegral.integral_hasDerivAt_right hii hmeas
    hcont.continuousAt).continuousAt

lemma continuous : Continuous (zTraj Z) := by
  unfold zTraj
  have h1 : Continuous (fun t : ℝ => Real.exp (- Z.antideriv t)) :=
    Real.continuous_exp.comp Z.antideriv_continuous.neg
  exact h1.mul (inner_continuous Z)

@[simp] lemma zero : zTraj Z 0 = 0 := by
  unfold zTraj zInner; simp

lemma inner_hasDerivAt (t : ℝ) :
    HasDerivAt (zInner Z) (Real.exp (Z.antideriv t)) t := by
  unfold zInner
  have hcont := exp_antideriv_continuous Z
  have hii : IntervalIntegrable (fun s => Real.exp (Z.antideriv s)) volume 0 t :=
    hcont.intervalIntegrable 0 t
  have hmeas : StronglyMeasurableAtFilter (fun s => Real.exp (Z.antideriv s))
      (nhds t) volume := hcont.stronglyMeasurableAtFilter _ _
  exact intervalIntegral.integral_hasDerivAt_right hii hmeas hcont.continuousAt

/-- Stage-B ODE: `z'(t) = 1 − zr(t) · z(t)`. -/
lemma hasDerivAt (t : ℝ) :
    HasDerivAt (zTraj Z) (1 - Z.zr t * zTraj Z t) t := by
  unfold zTraj
  have hA := Z.antideriv_hasDerivAt t
  have hExpNeg : HasDerivAt (fun s => Real.exp (- Z.antideriv s))
      (Real.exp (- Z.antideriv t) * (- Z.zr t)) t := hA.neg.exp
  have hI := inner_hasDerivAt Z t
  have hProd : HasDerivAt
      (fun s => Real.exp (- Z.antideriv s) * zInner Z s)
      (Real.exp (- Z.antideriv t) * (- Z.zr t) * zInner Z t
        + Real.exp (- Z.antideriv t) * Real.exp (Z.antideriv t)) t :=
    hExpNeg.mul hI
  have hCancel : Real.exp (- Z.antideriv t) * Real.exp (Z.antideriv t) = 1 := by
    rw [← Real.exp_add]; simp
  convert hProd using 1
  rw [hCancel]; ring

lemma inner_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ zInner Z t := by
  unfold zInner
  apply intervalIntegral.integral_nonneg ht
  intro s _; exact (Real.exp_pos _).le

lemma nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ zTraj Z t :=
  mul_nonneg (Real.exp_pos _).le (inner_nonneg Z ht)

end zTraj

/-! ## Key split identity. -/

namespace zTraj

variable {γ : ℝ} (Z : ZrData γ)

/-- Split identity: `z(t) = exp(-(A(t)-A(T)))·z(T) + ∫_T^t exp(-(A(t)-A(s))) ds`. -/
lemma split_identity {T t : ℝ} (hT_nn : 0 ≤ T) (hTt : T ≤ t) :
    zTraj Z t = Real.exp (-(Z.antideriv t - Z.antideriv T)) * zTraj Z T
      + ∫ s in T..t, Real.exp (-(Z.antideriv t - Z.antideriv s)) := by
  unfold zTraj zInner
  have hii1 : IntervalIntegrable (fun s => Real.exp (Z.antideriv s)) volume 0 T :=
    (exp_antideriv_continuous Z).intervalIntegrable 0 T
  have hii2 : IntervalIntegrable (fun s => Real.exp (Z.antideriv s)) volume T t :=
    (exp_antideriv_continuous Z).intervalIntegrable T t
  have hsplit : (∫ s in (0:ℝ)..t, Real.exp (Z.antideriv s))
      = (∫ s in (0:ℝ)..T, Real.exp (Z.antideriv s))
        + ∫ s in T..t, Real.exp (Z.antideriv s) :=
    (intervalIntegral.integral_add_adjacent_intervals hii1 hii2).symm
  rw [hsplit, mul_add]
  have hExpSum : Real.exp (-(Z.antideriv t - Z.antideriv T))
      = Real.exp (- Z.antideriv t) * Real.exp (Z.antideriv T) := by
    rw [← Real.exp_add]; congr 1; ring
  congr 1
  · rw [hExpSum]
    have hCancel : Real.exp (Z.antideriv T) * Real.exp (- Z.antideriv T) = 1 := by
      rw [← Real.exp_add]; simp
    have hrhs : Real.exp (- Z.antideriv t) * Real.exp (Z.antideriv T) *
          (Real.exp (- Z.antideriv T) *
            ∫ s in (0:ℝ)..T, Real.exp (Z.antideriv s))
        = Real.exp (- Z.antideriv t) *
            ∫ s in (0:ℝ)..T, Real.exp (Z.antideriv s) := by
      calc Real.exp (- Z.antideriv t) * Real.exp (Z.antideriv T) *
            (Real.exp (- Z.antideriv T) *
              ∫ s in (0:ℝ)..T, Real.exp (Z.antideriv s))
          = Real.exp (- Z.antideriv t) *
              (Real.exp (Z.antideriv T) * Real.exp (- Z.antideriv T)) *
              ∫ s in (0:ℝ)..T, Real.exp (Z.antideriv s) := by ring
        _ = Real.exp (- Z.antideriv t) * 1 *
              ∫ s in (0:ℝ)..T, Real.exp (Z.antideriv s) := by rw [hCancel]
        _ = Real.exp (- Z.antideriv t) *
              ∫ s in (0:ℝ)..T, Real.exp (Z.antideriv s) := by ring
    linarith
  · rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s _
    dsimp
    rw [← Real.exp_add]
    congr 1; ring

end zTraj

/-! ## Uniform bound on `[0, ∞)`.

Strategy: past `T* := max 0 (zrModulus N0 + 1)` with `N0` chosen so that
`exp(-N0) ≤ min(1/(2γ), γ/4)`, we have `zr(s) ≥ 1/(2γ)`, hence `z(t) → 2γ`.
Combine with crude bound on `[0, T*]`.
-/

/-- Choose `N0 : ℕ` with `exp(-N0) ≤ min(1/(2γ), γ/4)`.

Both bounds are used later:
  * `exp(-N0) ≤ 1/(2γ)`  ⇒ `zr ≥ 1/(2γ)` past the modulus.
  * `exp(-N0) ≤ γ/4`     ⇒ later, `ε ≤ Γ/4` where `Γ = 1/γ` (needed for the
                          two-sided bound's `γ-ε ≥ 3γ/4` analogue).

Actually in Stage B we need `ε ≤ Γ/4 = 1/(4γ)`.  Take
`chooseN0B γ := ceil(max(log(2γ), log(4γ))) = ceil(log(4γ))` (since `4γ > 2γ`).
Wait: we need `exp(-N) ≤ 1/(2γ)` AND `exp(-N) ≤ 1/(4γ)`.  The tighter is
`1/(4γ)` (smaller).  So take `N ≥ log(4γ)`.  Hmm but `4γ` could be `< 1`,
making `log(4γ) < 0`, in which case `N := 0` works.

We define: `chooseN0B γ := Nat.ceil(Real.log(4γ))` (which is `0` if `log(4γ) ≤ 0`).
Then `exp(-N0B) ≤ 1/(4γ) ≤ 1/(2γ)`. -/
noncomputable def chooseN0B (γ : ℝ) : ℕ :=
  Nat.ceil (Real.log (4 * γ))

lemma chooseN0B_spec_quarter {γ : ℝ} (hγ : 0 < γ) :
    Real.exp (-(chooseN0B γ : ℝ)) ≤ 1 / (4 * γ) := by
  have hγ4_pos : 0 < 4 * γ := by linarith
  have hle : Real.log (4 * γ) ≤ (chooseN0B γ : ℝ) := by
    show _ ≤ ((Nat.ceil (Real.log (4 * γ)) : ℕ) : ℝ)
    exact Nat.le_ceil _
  have h_neg : -(chooseN0B γ : ℝ) ≤ -Real.log (4 * γ) := by linarith
  have h_exp_le : Real.exp (-(chooseN0B γ : ℝ)) ≤ Real.exp (-Real.log (4 * γ)) :=
    Real.exp_le_exp.mpr h_neg
  have hlog : Real.exp (-Real.log (4 * γ)) = 1 / (4 * γ) := by
    rw [Real.exp_neg, Real.exp_log hγ4_pos, one_div]
  rwa [hlog] at h_exp_le

lemma chooseN0B_spec_half {γ : ℝ} (hγ : 0 < γ) :
    Real.exp (-(chooseN0B γ : ℝ)) ≤ 1 / (2 * γ) := by
  have h1 := chooseN0B_spec_quarter hγ
  have h2 : 1 / (4 * γ) ≤ 1 / (2 * γ) := by
    apply one_div_le_one_div_of_le (by linarith)
    linarith
  linarith

/-- Past `T* := max 0 (Z.zrModulus (chooseN0B γ) + 1)`, we have `zr(s) ≥ 1/(2γ)`. -/
lemma zr_ge_half_recip_past_Tstar {γ : ℝ} (hγ : 0 < γ) (Z : ZrData γ)
    {t : ℝ} (ht_nn : 0 ≤ t) (ht_gt : t > Z.zrModulus (chooseN0B γ)) :
    1 / (2 * γ) ≤ Z.zr t := by
  have hconv := Z.zr_conv (chooseN0B γ) t ht_nn ht_gt
  have hbd : Real.exp (-(chooseN0B γ : ℝ)) ≤ 1 / (2 * γ) := chooseN0B_spec_half hγ
  have h1 : |Z.zr t - 1 / γ| < 1 / (2 * γ) := lt_of_lt_of_le hconv hbd
  have h2 : -(1 / (2 * γ)) < Z.zr t - 1 / γ := (abs_lt.mp h1).1
  have h3 : 1 / γ - 1 / (2 * γ) = 1 / (2 * γ) := by
    field_simp; ring
  linarith

namespace zTraj

variable {γ : ℝ} (Z : ZrData γ)

/-- Crude bound on `[0, T]`: `z(t) ≤ exp(2·B·t) · t` where `B := zr_bound`. -/
lemma crude_bound {t : ℝ} (ht : 0 ≤ t) :
    zTraj Z t ≤ Real.exp (2 * Z.zr_bound * t) * t := by
  unfold zTraj zInner
  have hB_nn : 0 ≤ Z.zr_bound := Z.zr_bound_pos.le
  have hNeg_le : -Z.antideriv t ≤ Z.zr_bound * t := by
    have := Z.antideriv_abs_le ht
    have h2 : -Z.antideriv t ≤ |Z.antideriv t| := neg_le_abs _
    linarith
  have hNegA_le : Real.exp (-Z.antideriv t) ≤ Real.exp (Z.zr_bound * t) :=
    Real.exp_le_exp.mpr hNeg_le
  have hExpNegA_nn : 0 ≤ Real.exp (-Z.antideriv t) := (Real.exp_pos _).le
  have hInner_le : (∫ s in (0:ℝ)..t, Real.exp (Z.antideriv s))
      ≤ ∫ _s in (0:ℝ)..t, Real.exp (Z.zr_bound * t) := by
    apply intervalIntegral.integral_mono_on ht
    · exact (exp_antideriv_continuous Z).intervalIntegrable 0 t
    · exact continuous_const.intervalIntegrable 0 t
    · intro s hs
      have hs0 : 0 ≤ s := hs.1
      have hst : s ≤ t := hs.2
      have h1 : Z.antideriv s ≤ Z.zr_bound * s := le_of_abs_le (Z.antideriv_abs_le hs0)
      have h2 : Z.zr_bound * s ≤ Z.zr_bound * t :=
        mul_le_mul_of_nonneg_left hst hB_nn
      exact Real.exp_le_exp.mpr (le_trans h1 h2)
  have hInnerEval : ∫ _s in (0:ℝ)..t, Real.exp (Z.zr_bound * t)
      = Real.exp (Z.zr_bound * t) * t := by
    rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_comm]
  have hInner_le' : (∫ s in (0:ℝ)..t, Real.exp (Z.antideriv s))
      ≤ Real.exp (Z.zr_bound * t) * t := by linarith
  have hInner_nn : 0 ≤ ∫ s in (0:ℝ)..t, Real.exp (Z.antideriv s) := by
    apply intervalIntegral.integral_nonneg ht
    intro s _; exact (Real.exp_pos _).le
  have hExpBt_nn : 0 ≤ Real.exp (Z.zr_bound * t) := (Real.exp_pos _).le
  calc Real.exp (-Z.antideriv t) * ∫ s in (0:ℝ)..t, Real.exp (Z.antideriv s)
      ≤ Real.exp (Z.zr_bound * t) * (Real.exp (Z.zr_bound * t) * t) :=
        mul_le_mul hNegA_le hInner_le' hInner_nn hExpBt_nn
    _ = Real.exp (2 * Z.zr_bound * t) * t := by
        rw [show Real.exp (Z.zr_bound * t) * (Real.exp (Z.zr_bound * t) * t)
            = (Real.exp (Z.zr_bound * t) * Real.exp (Z.zr_bound * t)) * t by ring,
          ← Real.exp_add]
        congr 2; ring

/-- Parametrized decay upper bound.  If `zr(s) ≥ c > 0` on `[T, t]`, then
  `z(t) ≤ exp(-c(t-T))·z(T) + (1/c)·(1 - exp(-c(t-T)))`. -/
lemma decay_upper {T t c : ℝ} (hc : 0 < c) (hT_nn : 0 ≤ T) (hTt : T ≤ t)
    (hzT_nn : 0 ≤ zTraj Z T)
    (hzr_ge : ∀ s, T ≤ s → s ≤ t → c ≤ Z.zr s) :
    zTraj Z t ≤ Real.exp (-c * (t - T)) * zTraj Z T
      + (1 / c) * (1 - Real.exp (-c * (t - T))) := by
  rw [split_identity Z hT_nn hTt]
  have hAdiff_ge : c * (t - T) ≤ Z.antideriv t - Z.antideriv T :=
    Z.antideriv_diff_ge hT_nn hTt hzr_ge
  have hNegAdiff_le : -(Z.antideriv t - Z.antideriv T) ≤ -c * (t - T) := by linarith
  have hExp_first : Real.exp (-(Z.antideriv t - Z.antideriv T)) ≤ Real.exp (-c * (t - T)) :=
    Real.exp_le_exp.mpr hNegAdiff_le
  have hFirst_bd : Real.exp (-(Z.antideriv t - Z.antideriv T)) * zTraj Z T
      ≤ Real.exp (-c * (t - T)) * zTraj Z T :=
    mul_le_mul_of_nonneg_right hExp_first hzT_nn
  have hCont_lhs : Continuous (fun s : ℝ => Real.exp (-(Z.antideriv t - Z.antideriv s))) := by
    refine Real.continuous_exp.comp ?_
    exact (continuous_const.sub Z.antideriv_continuous).neg
  have hCont_rhs : Continuous (fun s : ℝ => Real.exp (-c * (t - s))) := by
    refine Real.continuous_exp.comp ?_
    exact (continuous_const.mul (continuous_const.sub continuous_id))
  have hInt_bd : (∫ s in T..t, Real.exp (-(Z.antideriv t - Z.antideriv s)))
      ≤ ∫ s in T..t, Real.exp (-c * (t - s)) := by
    apply intervalIntegral.integral_mono_on hTt
    · exact hCont_lhs.intervalIntegrable T t
    · exact hCont_rhs.intervalIntegrable T t
    · intro s hs
      have hAdiff_ge' : c * (t - s) ≤ Z.antideriv t - Z.antideriv s := by
        apply Z.antideriv_diff_ge (le_trans hT_nn hs.1) hs.2
        intro u hus hut; exact hzr_ge u (le_trans hs.1 hus) hut
      have : -(Z.antideriv t - Z.antideriv s) ≤ -c * (t - s) := by linarith
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

/-- Parametrized decay lower bound.  If `zr(s) ≤ c` on `[T, t]` with `c > 0`
and `z(T) ≥ 0`, then
  `z(t) ≥ exp(-c(t-T))·z(T) + (1/c)·(1 - exp(-c(t-T)))`. -/
lemma decay_lower {T t c : ℝ} (hc : 0 < c) (hT_nn : 0 ≤ T) (hTt : T ≤ t)
    (hzT_nn : 0 ≤ zTraj Z T)
    (hzr_le : ∀ s, T ≤ s → s ≤ t → Z.zr s ≤ c) :
    Real.exp (-c * (t - T)) * zTraj Z T
      + (1 / c) * (1 - Real.exp (-c * (t - T)))
      ≤ zTraj Z t := by
  rw [split_identity Z hT_nn hTt]
  have hAdiff_le : Z.antideriv t - Z.antideriv T ≤ c * (t - T) := by
    have hsplit : Z.antideriv t - Z.antideriv T = ∫ u in T..t, Z.zr u := by
      unfold ZrData.antideriv
      have hii1 : IntervalIntegrable Z.zr volume 0 T := Z.zr_intervalIntegrable 0 T
      have hii2 : IntervalIntegrable Z.zr volume T t := Z.zr_intervalIntegrable T t
      have := intervalIntegral.integral_add_adjacent_intervals hii1 hii2
      linarith
    rw [hsplit]
    have h_const_int : IntervalIntegrable (fun _ : ℝ => c) volume T t :=
      continuous_const.intervalIntegrable T t
    have hii2 : IntervalIntegrable Z.zr volume T t := Z.zr_intervalIntegrable T t
    have hmono : (∫ u in T..t, Z.zr u) ≤ ∫ _u in T..t, c := by
      apply intervalIntegral.integral_mono_on hTt hii2 h_const_int
      intro u hu; exact hzr_le u hu.1 hu.2
    have heval : (∫ _u in T..t, c) = c * (t - T) := by
      rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm]
    linarith
  have hNegAdiff_ge : -c * (t - T) ≤ -(Z.antideriv t - Z.antideriv T) := by linarith
  have hExp_first_ge : Real.exp (-c * (t - T))
      ≤ Real.exp (-(Z.antideriv t - Z.antideriv T)) :=
    Real.exp_le_exp.mpr hNegAdiff_ge
  have hFirst_bd : Real.exp (-c * (t - T)) * zTraj Z T
      ≤ Real.exp (-(Z.antideriv t - Z.antideriv T)) * zTraj Z T :=
    mul_le_mul_of_nonneg_right hExp_first_ge hzT_nn
  have hCont_lhs : Continuous (fun s : ℝ => Real.exp (-(Z.antideriv t - Z.antideriv s))) := by
    refine Real.continuous_exp.comp ?_
    exact (continuous_const.sub Z.antideriv_continuous).neg
  have hCont_rhs : Continuous (fun s : ℝ => Real.exp (-c * (t - s))) := by
    refine Real.continuous_exp.comp ?_
    exact (continuous_const.mul (continuous_const.sub continuous_id))
  have hInt_bd_ge : (∫ s in T..t, Real.exp (-c * (t - s)))
      ≤ ∫ s in T..t, Real.exp (-(Z.antideriv t - Z.antideriv s)) := by
    apply intervalIntegral.integral_mono_on hTt
    · exact hCont_rhs.intervalIntegrable T t
    · exact hCont_lhs.intervalIntegrable T t
    · intro s hs
      have hAdiff_le_s : Z.antideriv t - Z.antideriv s ≤ c * (t - s) := by
        have hsplit : Z.antideriv t - Z.antideriv s = ∫ u in s..t, Z.zr u := by
          unfold ZrData.antideriv
          have hii1 : IntervalIntegrable Z.zr volume 0 s := Z.zr_intervalIntegrable 0 s
          have hii2 : IntervalIntegrable Z.zr volume s t := Z.zr_intervalIntegrable s t
          have := intervalIntegral.integral_add_adjacent_intervals hii1 hii2
          linarith
        rw [hsplit]
        have h_const_int : IntervalIntegrable (fun _ : ℝ => c) volume s t :=
          continuous_const.intervalIntegrable s t
        have hii2 : IntervalIntegrable Z.zr volume s t := Z.zr_intervalIntegrable s t
        have hmono : (∫ u in s..t, Z.zr u) ≤ ∫ _u in s..t, c := by
          apply intervalIntegral.integral_mono_on hs.2 hii2 h_const_int
          intro u hu; exact hzr_le u (le_trans hs.1 hu.1) hu.2
        have heval : (∫ _u in s..t, c) = c * (t - s) := by
          rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm]
        linarith
      have : -c * (t - s) ≤ -(Z.antideriv t - Z.antideriv s) := by linarith
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

end zTraj

/-! ## Uniform bound assembly.

`T* := max 0 (Z.zrModulus (chooseN0B γ) + 1)`.  For `s ≥ T*`, `zr(s) ≥ 1/(2γ)`.
Crude bound on `[0, T*]`, decay to `2γ` on `[T*, ∞)`.
-/

namespace zTraj

variable {γ : ℝ} (Z : ZrData γ)

/-- Phase boundary `T* := max 0 (Z.zrModulus (chooseN0B γ) + 1)`.  Strictly
greater than the modulus so that `zr(s) ≥ 1/(2γ)` holds on `[T*, ∞)`. -/
noncomputable def Tstar : ℝ := max 0 (Z.zrModulus (chooseN0B γ) + 1)

lemma Tstar_nn : 0 ≤ Tstar Z := le_max_left _ _

lemma Tstar_gt_modulus : Z.zrModulus (chooseN0B γ) < Tstar Z := by
  unfold Tstar
  have : Z.zrModulus (chooseN0B γ) + 1 ≤ max 0 (Z.zrModulus (chooseN0B γ) + 1) :=
    le_max_right _ _
  linarith

/-- Crude bound value on `[0, T*]`. -/
noncomputable def B0 : ℝ :=
  Real.exp (2 * Z.zr_bound * Tstar Z) * Tstar Z

lemma B0_nn : 0 ≤ B0 Z :=
  mul_nonneg (Real.exp_pos _).le (Tstar_nn Z)

/-- Uniform bound `B_z := max (max B0 (2γ)) 1 + 1 > 0`. -/
noncomputable def Bz : ℝ := max (max (B0 Z) (2 * γ)) 1 + 1

lemma Bz_pos : 0 < Bz Z := by
  unfold Bz
  have : (1 : ℝ) ≤ max (max (B0 Z) (2 * γ)) 1 := le_max_right _ _
  linarith

lemma Bz_ge_B0 : B0 Z ≤ Bz Z := by
  unfold Bz
  have h1 : B0 Z ≤ max (B0 Z) (2 * γ) := le_max_left _ _
  have h2 : max (B0 Z) (2 * γ) ≤ max (max (B0 Z) (2 * γ)) 1 := le_max_left _ _
  linarith

lemma Bz_ge_two_mul_gamma : 2 * γ ≤ Bz Z := by
  unfold Bz
  have h1 : 2 * γ ≤ max (B0 Z) (2 * γ) := le_max_right _ _
  have h2 : max (B0 Z) (2 * γ) ≤ max (max (B0 Z) (2 * γ)) 1 := le_max_left _ _
  linarith

/-- Uniform upper bound: `z(t) ≤ B_z` for all `t ≥ 0`. -/
lemma uniform_bound (hγ : 0 < γ) {t : ℝ} (ht : 0 ≤ t) :
    zTraj Z t ≤ Bz Z := by
  by_cases htT : t ≤ Tstar Z
  · -- Phase 1: crude bound.
    have hbd := crude_bound Z ht
    have hmono : Real.exp (2 * Z.zr_bound * t) * t
        ≤ Real.exp (2 * Z.zr_bound * Tstar Z) * Tstar Z := by
      apply mul_le_mul
      · apply Real.exp_le_exp.mpr
        have h2B_nn : 0 ≤ 2 * Z.zr_bound := by linarith [Z.zr_bound_pos]
        exact mul_le_mul_of_nonneg_left htT h2B_nn
      · exact htT
      · exact ht
      · exact (Real.exp_pos _).le
    have hB0 : zTraj Z t ≤ B0 Z := le_trans hbd hmono
    linarith [Bz_ge_B0 Z]
  · -- Phase 2: decay bound past T*.
    push_neg at htT
    -- Apply decay_upper with T := Tstar Z, c := 1/(2γ), U := max (B0 Z) (2γ).
    set U : ℝ := max (B0 Z) (2 * γ) with hU_def
    have hU_ge : 2 * γ ≤ U := le_max_right _ _
    have hU_nn : 0 ≤ U := le_trans (by linarith : (0:ℝ) ≤ 2 * γ) hU_ge
    have hzT_le : zTraj Z (Tstar Z) ≤ U := by
      have hTstar := crude_bound Z (Tstar_nn Z)
      have hB0_le_U : B0 Z ≤ U := le_max_left _ _
      have : zTraj Z (Tstar Z) ≤ B0 Z := hTstar
      linarith
    have hzT_nn : 0 ≤ zTraj Z (Tstar Z) := nonneg Z (Tstar_nn Z)
    have hc_pos : 0 < 1 / (2 * γ) := by positivity
    have hzr_ge : ∀ s, Tstar Z ≤ s → s ≤ t → 1 / (2 * γ) ≤ Z.zr s := by
      intro s hTs _hst
      have hs_nn : 0 ≤ s := le_trans (Tstar_nn Z) hTs
      have hs_gt : s > Z.zrModulus (chooseN0B γ) :=
        lt_of_lt_of_le (Tstar_gt_modulus Z) hTs
      exact zr_ge_half_recip_past_Tstar hγ Z hs_nn hs_gt
    have hdec := decay_upper Z hc_pos (Tstar_nn Z) (le_of_lt htT) hzT_nn hzr_ge
    -- z(t) ≤ exp(-(1/(2γ))(t-Tstar))·z(Tstar) + (2γ)·(1 - exp(..)).
    have h_inv : (1 : ℝ) / (1 / (2 * γ)) = 2 * γ := by
      rw [one_div_one_div]
    rw [h_inv] at hdec
    have hExp_nn : 0 ≤ Real.exp (-(1 / (2 * γ)) * (t - Tstar Z)) := (Real.exp_pos _).le
    have hExp_le : Real.exp (-(1 / (2 * γ)) * (t - Tstar Z)) ≤ 1 := by
      have hprod_nn : 0 ≤ (1 / (2 * γ)) * (t - Tstar Z) := mul_nonneg hc_pos.le (by linarith)
      have hneg_le : -(1 / (2 * γ)) * (t - Tstar Z) ≤ 0 := by linarith
      have := Real.exp_le_exp.mpr hneg_le
      rwa [Real.exp_zero] at this
    have hOneSub_nn : 0 ≤ 1 - Real.exp (-(1 / (2 * γ)) * (t - Tstar Z)) := by linarith
    have hFirst_le : Real.exp (-(1 / (2 * γ)) * (t - Tstar Z)) * zTraj Z (Tstar Z)
        ≤ Real.exp (-(1 / (2 * γ)) * (t - Tstar Z)) * U :=
      mul_le_mul_of_nonneg_left hzT_le hExp_nn
    have hSecond_le : (2 * γ) * (1 - Real.exp (-(1 / (2 * γ)) * (t - Tstar Z)))
        ≤ U * (1 - Real.exp (-(1 / (2 * γ)) * (t - Tstar Z))) :=
      mul_le_mul_of_nonneg_right hU_ge hOneSub_nn
    have hCombined : zTraj Z t ≤ U := by
      have hsum : Real.exp (-(1 / (2 * γ)) * (t - Tstar Z)) * U
          + U * (1 - Real.exp (-(1 / (2 * γ)) * (t - Tstar Z))) = U := by ring
      linarith
    have hU_le_Bz : U ≤ Bz Z := by
      unfold Bz
      have h1 : U ≤ max U 1 := le_max_left _ _
      linarith
    linarith

end zTraj

/-! ## Convergence of `z` to `γ`.

Set `Γ := 1/γ`.  The driver `zr` converges to `Γ` with modulus `Z.zrModulus`.
The pattern mirrors Stage A with `γ → Γ`:
  * apply `decay_upper` with `c := Γ - ε`  (steady state `1/(Γ-ε)`),
  * apply `decay_lower` with `c := Γ + ε`  (steady state `1/(Γ+ε)`),
  * sandwich gives `|z(t) - 1/Γ| = |z(t) - γ| ≤ …`.

Choice of parameters:
  * `Nr := 2 · chooseN0B γ + r + 2`.  Then `ε ≤ Γ²·exp(-r)/8 = exp(-r)/(8γ²)`.
  * We also force `ε ≤ Γ/4 = 1/(4γ)` via `chooseN0B` construction.
  * `T := max (Tstar Z + 1) (Z.zrModulus Nr + 1)`.
  * decay slack `(4/Γ)·(r + log(6·Bz) + 1) = (4γ)·(r + log(6·Bz) + 1)`.
-/

namespace zTraj

variable {γ : ℝ} (Z : ZrData γ)

/-- Two-sided bound (parameterized in `ε`).  For `T ≥ Tstar Z` and `t ≥ T`
with `|zr(s) - Γ| ≤ ε` on `[T, t]` (where `Γ := 1/γ`, `0 < ε < Γ`),

  `|z(t) - γ| ≤ ε / (Γ · (Γ - ε)) + (z(T) + 1/(Γ - ε)) · exp(-(Γ - ε)(t - T))`.

Mirrors Stage A's `two_sided_bound` with `γ_A = Γ = 1/γ` and the trivial identity
`1/Γ = γ`. -/
lemma two_sided_bound {T t ε : ℝ} (hγ : 0 < γ)
    (hε_pos : 0 < ε) (hε_lt : ε < 1 / γ)
    (hT_nn : 0 ≤ T) (hTt : T ≤ t)
    (hzT_nn : 0 ≤ zTraj Z T)
    (hzr_close : ∀ s, T ≤ s → s ≤ t → |Z.zr s - 1 / γ| ≤ ε) :
    |zTraj Z t - γ|
      ≤ ε / ((1 / γ) * (1 / γ - ε))
        + (zTraj Z T + 1 / (1 / γ - ε)) *
            Real.exp (-(1 / γ - ε) * (t - T)) := by
  -- Let Γ := 1/γ.
  set Γ : ℝ := 1 / γ with hΓ_def
  have hΓ_pos : 0 < Γ := by simp only [hΓ_def]; positivity
  have hΓε_pos : 0 < Γ - ε := by linarith
  have hΓε_sum_pos : 0 < Γ + ε := by linarith
  -- 1/Γ = γ.
  have hInv : (1 : ℝ) / Γ = γ := by
    simp only [hΓ_def]; rw [one_div_one_div]
  -- zr on [T, t]: Γ - ε ≤ zr(s) ≤ Γ + ε.
  have hd_ge : ∀ s, T ≤ s → s ≤ t → Γ - ε ≤ Z.zr s := by
    intro s hTs hst
    have := hzr_close s hTs hst
    have : -ε ≤ Z.zr s - Γ := (abs_le.mp this).1
    linarith
  have hd_le : ∀ s, T ≤ s → s ≤ t → Z.zr s ≤ Γ + ε := by
    intro s hTs hst
    have := hzr_close s hTs hst
    have : Z.zr s - Γ ≤ ε := (abs_le.mp this).2
    linarith
  have hUpper := decay_upper Z hΓε_pos hT_nn hTt hzT_nn hd_ge
  have hLower := decay_lower Z hΓε_sum_pos hT_nn hTt hzT_nn hd_le
  have hExp1_nn : 0 ≤ Real.exp (-(Γ - ε) * (t - T)) := (Real.exp_pos _).le
  have hExp2_nn : 0 ≤ Real.exp (-(Γ + ε) * (t - T)) := (Real.exp_pos _).le
  have hExp1_le : Real.exp (-(Γ - ε) * (t - T)) ≤ 1 := by
    rw [show (1:ℝ) = Real.exp 0 from Real.exp_zero.symm]
    apply Real.exp_le_exp.mpr
    have : 0 ≤ (Γ - ε) * (t - T) := mul_nonneg hΓε_pos.le (by linarith)
    linarith
  have hExp2_le : Real.exp (-(Γ + ε) * (t - T)) ≤ 1 := by
    rw [show (1:ℝ) = Real.exp 0 from Real.exp_zero.symm]
    apply Real.exp_le_exp.mpr
    have : 0 ≤ (Γ + ε) * (t - T) := mul_nonneg hΓε_sum_pos.le (by linarith)
    linarith
  have hExpMono : Real.exp (-(Γ + ε) * (t - T)) ≤ Real.exp (-(Γ - ε) * (t - T)) := by
    apply Real.exp_le_exp.mpr
    have h_neg : -(Γ + ε) ≤ -(Γ - ε) := by linarith
    exact mul_le_mul_of_nonneg_right h_neg (by linarith)
  -- Algebraic massage.
  have hUpper' : zTraj Z t - γ
      ≤ ε / (Γ * (Γ - ε))
        + Real.exp (-(Γ - ε) * (t - T)) * (zTraj Z T - 1 / (Γ - ε)) := by
    have h1 : (1 : ℝ) / (Γ - ε) - 1 / Γ = ε / (Γ * (Γ - ε)) := by
      field_simp
      ring
    have hrec : Real.exp (-(Γ - ε) * (t - T)) * zTraj Z T
        + 1 / (Γ - ε) * (1 - Real.exp (-(Γ - ε) * (t - T)))
        = 1 / (Γ - ε) + Real.exp (-(Γ - ε) * (t - T)) * (zTraj Z T - 1 / (Γ - ε)) := by
      ring
    rw [hrec] at hUpper
    -- Use hInv : 1/Γ = γ, so 1/(Γ-ε) - 1/Γ = 1/(Γ-ε) - γ.
    -- hUpper : zTraj Z t ≤ 1/(Γ-ε) + exp(-(Γ-ε)(t-T))·(zTraj Z T - 1/(Γ-ε))
    -- Subtract γ = 1/Γ:
    linarith [h1, hInv]
  have hLower' : -(ε / (Γ * (Γ + ε)))
        + Real.exp (-(Γ + ε) * (t - T)) * (zTraj Z T - 1 / (Γ + ε))
      ≤ zTraj Z t - γ := by
    have h1 : (1 : ℝ) / (Γ + ε) - 1 / Γ = -(ε / (Γ * (Γ + ε))) := by
      field_simp
      ring
    have hrec : Real.exp (-(Γ + ε) * (t - T)) * zTraj Z T
        + 1 / (Γ + ε) * (1 - Real.exp (-(Γ + ε) * (t - T)))
        = 1 / (Γ + ε) + Real.exp (-(Γ + ε) * (t - T)) * (zTraj Z T - 1 / (Γ + ε)) := by
      ring
    rw [hrec] at hLower
    linarith [h1, hInv]
  -- Error bounds.
  have hΓε_inv_pos : 0 < 1 / (Γ - ε) := by positivity
  have hΓε_sum_inv_pos : 0 < 1 / (Γ + ε) := by positivity
  have hΓε_sum_inv_le : 1 / (Γ + ε) ≤ 1 / (Γ - ε) := by
    apply one_div_le_one_div_of_le hΓε_pos
    linarith
  have hErr_common : ε / (Γ * (Γ + ε)) ≤ ε / (Γ * (Γ - ε)) := by
    apply div_le_div_of_nonneg_left hε_pos.le
    · positivity
    · apply mul_le_mul_of_nonneg_left _ hΓ_pos.le
      linarith
  -- Upper:
  have hUpperBd : zTraj Z t - γ
      ≤ ε / (Γ * (Γ - ε))
        + (zTraj Z T + 1 / (Γ - ε)) * Real.exp (-(Γ - ε) * (t - T)) := by
    have h_coef : zTraj Z T - 1 / (Γ - ε) ≤ zTraj Z T + 1 / (Γ - ε) := by linarith
    have h_coef_nn : 0 ≤ zTraj Z T + 1 / (Γ - ε) := by linarith
    have hstep : Real.exp (-(Γ - ε) * (t - T)) * (zTraj Z T - 1 / (Γ - ε))
        ≤ (zTraj Z T + 1 / (Γ - ε)) * Real.exp (-(Γ - ε) * (t - T)) := by
      have h1 : Real.exp (-(Γ - ε) * (t - T)) * (zTraj Z T - 1 / (Γ - ε))
          ≤ Real.exp (-(Γ - ε) * (t - T)) * (zTraj Z T + 1 / (Γ - ε)) :=
        mul_le_mul_of_nonneg_left h_coef hExp1_nn
      linarith
    linarith
  -- Lower bound (negated).
  have hLowerBd : -(zTraj Z t - γ)
      ≤ ε / (Γ * (Γ - ε))
        + (zTraj Z T + 1 / (Γ - ε)) * Real.exp (-(Γ - ε) * (t - T)) := by
    have hkey : -(zTraj Z t - γ)
        ≤ ε / (Γ * (Γ + ε))
          + Real.exp (-(Γ + ε) * (t - T)) * (1 / (Γ + ε) - zTraj Z T) := by
      have h1 : -(zTraj Z t - γ)
          ≤ ε / (Γ * (Γ + ε))
            + -(Real.exp (-(Γ + ε) * (t - T)) * (zTraj Z T - 1 / (Γ + ε))) := by
        linarith
      have h2 : -(Real.exp (-(Γ + ε) * (t - T)) * (zTraj Z T - 1 / (Γ + ε)))
          = Real.exp (-(Γ + ε) * (t - T)) * (1 / (Γ + ε) - zTraj Z T) := by ring
      linarith
    have hbd_err : ε / (Γ * (Γ + ε)) ≤ ε / (Γ * (Γ - ε)) := hErr_common
    have hbd_trans : Real.exp (-(Γ + ε) * (t - T)) * (1 / (Γ + ε) - zTraj Z T)
        ≤ Real.exp (-(Γ - ε) * (t - T)) * (zTraj Z T + 1 / (Γ - ε)) := by
      by_cases hdiff : 1 / (Γ + ε) - zTraj Z T ≤ 0
      · have hLHS_le : Real.exp (-(Γ + ε) * (t - T)) * (1 / (Γ + ε) - zTraj Z T) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hExp2_nn hdiff
        have hRHS_nn : 0 ≤ Real.exp (-(Γ - ε) * (t - T)) * (zTraj Z T + 1 / (Γ - ε)) :=
          mul_nonneg hExp1_nn (by linarith)
        linarith
      · push_neg at hdiff
        have hcoef_le : 1 / (Γ + ε) - zTraj Z T ≤ zTraj Z T + 1 / (Γ - ε) := by
          have h := hzT_nn
          have : (2:ℝ) * zTraj Z T ≥ 0 := by linarith
          have h1 : 1 / (Γ - ε) - 1 / (Γ + ε) ≥ 0 := by linarith
          linarith
        have h1 : Real.exp (-(Γ + ε) * (t - T)) * (1 / (Γ + ε) - zTraj Z T)
            ≤ Real.exp (-(Γ - ε) * (t - T)) * (1 / (Γ + ε) - zTraj Z T) :=
          mul_le_mul_of_nonneg_right hExpMono hdiff.le
        have h2 : Real.exp (-(Γ - ε) * (t - T)) * (1 / (Γ + ε) - zTraj Z T)
            ≤ Real.exp (-(Γ - ε) * (t - T)) * (zTraj Z T + 1 / (Γ - ε)) :=
          mul_le_mul_of_nonneg_left hcoef_le hExp1_nn
        linarith
    linarith
  exact abs_le.mpr ⟨by linarith, hUpperBd⟩

end zTraj

/-! ## Picking the convergence modulus.

We take `ε := exp(-(2·chooseN0B γ + r + 2))`.  Letting `Γ = 1/γ`:
  * `ε ≤ (1/(4γ))² · exp(-r) · (1/2) = exp(-r)/(32 γ²)`.
  * Γ/4 = 1/(4γ), so `ε ≤ Γ/4`, giving `γ-ε ≥ 3Γ/4` is wrong — I mean `Γ-ε ≥ 3Γ/4`.
    (Using `chooseN0B γ` satisfies `exp(-N0) ≤ 1/(4γ)`, and since ε ≤ exp(-N0),
     we get `ε ≤ 1/(4γ) = Γ/4`.)

Slack: `4γ · (r + log(6·Bz) + 1)`, so `(Γ/2)·(t - T) ≥ 2·(r + log(6·Bz) + 1)`.
-/

namespace zTraj

variable {γ : ℝ} (Z : ZrData γ)

/-- Convergence modulus for `z → γ`. -/
noncomputable def zModulus (r : ℕ) : ℝ :=
  max (Tstar Z + 1) (Z.zrModulus (2 * chooseN0B γ + r + 2) + 1)
    + (4 * γ) * ((r : ℝ) + Real.log (6 * Bz Z) + 1)

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
/-- **Main convergence theorem for Stage B.**  For every `r`, past `zModulus r`,
`z(t)` is within `exp(-r)` of `γ`. -/
theorem z_converges (hγ : 0 < γ) (hγ_hi : γ < 1) :
    ∀ r : ℕ, ∀ t : ℝ, t > zModulus Z r →
      |zTraj Z t - γ| < Real.exp (-(r : ℝ)) := by
  intro r t ht
  -- Let Γ := 1/γ.
  set Γ : ℝ := 1 / γ with hΓ_def
  have hΓ_pos : 0 < Γ := by simp only [hΓ_def]; positivity
  have hΓ_gt_one : 1 < Γ := by
    simp only [hΓ_def]
    rw [lt_div_iff₀ hγ]; linarith
  -- Setup.
  set Nr : ℕ := 2 * chooseN0B γ + r + 2 with hNr_def
  set ε : ℝ := Real.exp (-(Nr : ℝ)) with hε_def
  set T : ℝ := max (Tstar Z + 1) (Z.zrModulus Nr + 1) with hT_def
  have hTstar_le : Tstar Z + 1 ≤ T := le_max_left _ _
  have hModulus_le : Z.zrModulus Nr + 1 ≤ T := le_max_right _ _
  have hT_nn : 0 ≤ T := by
    have h := Tstar_nn Z
    linarith [hTstar_le]
  have hε_pos : 0 < ε := Real.exp_pos _
  have hExpR_pos : 0 < Real.exp (-(r : ℝ)) := Real.exp_pos _
  have h_exp_r_le : Real.exp (-(r : ℝ)) ≤ 1 := by
    rw [show (1:ℝ) = Real.exp 0 from Real.exp_zero.symm]
    apply Real.exp_le_exp.mpr
    have : 0 ≤ (r : ℝ) := by positivity
    linarith
  have h_exp_2 : Real.exp (-(2:ℝ)) ≤ 1 / 2 := exp_neg_two_le_half
  have h_N0 : Real.exp (-(chooseN0B γ : ℝ)) ≤ 1 / (4 * γ) := chooseN0B_spec_quarter hγ
  have h_N0_nn : 0 ≤ Real.exp (-(chooseN0B γ : ℝ)) := (Real.exp_pos _).le
  -- Note: 1/(4γ) = Γ/4.
  have hΓ4 : 1 / (4 * γ) = Γ / 4 := by simp only [hΓ_def]; field_simp
  have h_N0' : Real.exp (-(chooseN0B γ : ℝ)) ≤ Γ / 4 := by rw [← hΓ4]; exact h_N0
  -- ε split.
  have hε_split : ε =
      (Real.exp (-(chooseN0B γ : ℝ))) * (Real.exp (-(chooseN0B γ : ℝ)))
        * Real.exp (-(r:ℝ)) * Real.exp (-(2:ℝ)) := by
    rw [hε_def]
    rw [show (-(Nr : ℝ)) = -((chooseN0B γ : ℝ)) + (-(chooseN0B γ : ℝ))
        + (-(r : ℝ)) + (-(2 : ℝ)) from by
      show -(((2 * chooseN0B γ + r + 2 : ℕ) : ℝ)) = _
      push_cast; ring]
    rw [Real.exp_add, Real.exp_add, Real.exp_add]
  -- Bound ε ≤ (Γ/4)² · exp(-r) · (1/2) = Γ²·exp(-r)/32.
  have hε_le_key : ε ≤ Γ^2 * Real.exp (-(r:ℝ)) / 32 := by
    rw [hε_split]
    have hp1 := h_N0'
    have hp1_nn := h_N0_nn
    have hp_rn : 0 ≤ Real.exp (-(r:ℝ)) := (Real.exp_pos _).le
    have hp_2n : 0 ≤ Real.exp (-(2:ℝ)) := (Real.exp_pos _).le
    have hΓ4_nn : 0 ≤ Γ / 4 := by linarith
    have step1 : Real.exp (-(chooseN0B γ : ℝ)) * Real.exp (-(chooseN0B γ : ℝ))
        ≤ (Γ/4) * (Γ/4) := mul_le_mul hp1 hp1 hp1_nn hΓ4_nn
    have step1_nn : 0 ≤ Real.exp (-(chooseN0B γ : ℝ)) * Real.exp (-(chooseN0B γ : ℝ)) :=
      mul_nonneg hp1_nn hp1_nn
    have hLHS : Real.exp (-(chooseN0B γ : ℝ)) * Real.exp (-(chooseN0B γ : ℝ))
        * Real.exp (-(r:ℝ)) * Real.exp (-(2:ℝ))
        ≤ (Γ/4) * (Γ/4) * Real.exp (-(r:ℝ)) * (1/2) := by
      have ha : Real.exp (-(chooseN0B γ : ℝ)) * Real.exp (-(chooseN0B γ : ℝ))
          ≤ (Γ/4) * (Γ/4) := step1
      have hc : Real.exp (-(2:ℝ)) ≤ (1/2) := h_exp_2
      have hab : Real.exp (-(chooseN0B γ : ℝ)) * Real.exp (-(chooseN0B γ : ℝ))
          * Real.exp (-(r:ℝ)) ≤ (Γ/4) * (Γ/4) * Real.exp (-(r:ℝ)) :=
        mul_le_mul_of_nonneg_right ha hp_rn
      exact mul_le_mul hab hc hp_2n (by positivity)
    have hRHS_eq : (Γ/4) * (Γ/4) * Real.exp (-(r:ℝ)) * (1/2) = Γ^2 * Real.exp (-(r:ℝ)) / 32 := by
      ring
    linarith
  -- ε ≤ Γ/4.  Use ε ≤ Γ²·exp(-r)/32 ≤ Γ²/32.  Need Γ²/32 ≤ Γ/4 ⇔ Γ ≤ 8.
  -- That's not automatic.  Instead: ε ≤ exp(-N0) · exp(-N0) · 1 · (1/2) ≤ (Γ/4)² · (1/2)
  -- ≤ (Γ/4) · (Γ/4) · (1/2) ≤ Γ/4 IF (Γ/4)·(1/2) ≤ 1, i.e., Γ ≤ 8.  Still bad.
  -- Better approach: ε ≤ exp(-N0) ≤ Γ/4 directly, since Nr ≥ N0 (as 2·N0 + r + 2 ≥ N0).
  have hε_le_N0 : ε ≤ Real.exp (-(chooseN0B γ : ℝ)) := by
    rw [hε_def]
    apply Real.exp_le_exp.mpr
    have : -(Nr : ℝ) ≤ -(chooseN0B γ : ℝ) := by
      have h1 : (chooseN0B γ : ℝ) ≤ (Nr : ℝ) := by
        rw [hNr_def]; push_cast; linarith
      linarith
    exact this
  have hε_le_Γ4 : ε ≤ Γ / 4 := le_trans hε_le_N0 h_N0'
  have hε_lt_Γ : ε < Γ := by
    have : Γ / 4 < Γ := by linarith
    linarith
  have hΓε_pos : 0 < Γ - ε := by linarith
  have hΓε_ge_3Γ4 : 3 * Γ / 4 ≤ Γ - ε := by linarith
  have hΓε_ge_half : Γ / 2 ≤ Γ - ε := by linarith
  have hT_ge_Tstar : Tstar Z ≤ T := by linarith
  have hT_gt_modulus : Z.zrModulus Nr < T := by linarith
  -- Bz ≥ 2.
  have hBz_ge2 : 2 ≤ Bz Z := by
    unfold Bz
    have : (1:ℝ) ≤ max (max (B0 Z) (2 * γ)) 1 := le_max_right _ _
    linarith
  have hBz_pos : 0 < Bz Z := by linarith
  have hlog_nn : 0 ≤ Real.log (6 * Bz Z) := by
    apply Real.log_nonneg
    have : (6:ℝ) * Bz Z ≥ 6 * 2 := by
      apply mul_le_mul_of_nonneg_left hBz_ge2 (by norm_num)
    linarith
  have h4γ_pos : 0 < 4 * γ := by linarith
  have hTt : T ≤ t := by
    unfold zModulus at ht
    have : (4 * γ) * ((r : ℝ) + Real.log (6 * Bz Z) + 1) ≥ 0 :=
      mul_nonneg h4γ_pos.le (by linarith [Nat.cast_nonneg r (α := ℝ)])
    linarith
  -- Apply two_sided_bound.
  have hzr_close : ∀ s, T ≤ s → s ≤ t → |Z.zr s - 1 / γ| ≤ ε := by
    intro s hTs _hst
    have hs_nn : 0 ≤ s := le_trans hT_nn hTs
    have hs_gt : s > Z.zrModulus Nr := lt_of_lt_of_le hT_gt_modulus hTs
    exact (Z.zr_conv Nr s hs_nn hs_gt).le
  have hzT_nn : 0 ≤ zTraj Z T := nonneg Z hT_nn
  have hzT_le : zTraj Z T ≤ Bz Z := uniform_bound Z hγ hT_nn
  have hbound := two_sided_bound Z hγ hε_pos hε_lt_Γ hT_nn hTt hzT_nn hzr_close
  -- Piece 1: ε / (Γ · (Γ - ε)) ≤ exp(-r)/3.
  have hP1 : ε / (Γ * (Γ - ε)) ≤ Real.exp (-(r:ℝ)) / 3 := by
    have hΓΓ_ε_pos : 0 < Γ * (Γ - ε) := mul_pos hΓ_pos hΓε_pos
    have h34Γ2_pos : 0 < Γ * (3 * Γ / 4) := by positivity
    have hbd1 : ε / (Γ * (Γ - ε)) ≤ ε / (Γ * (3 * Γ / 4)) := by
      apply div_le_div_of_nonneg_left hε_pos.le h34Γ2_pos
      exact mul_le_mul_of_nonneg_left hΓε_ge_3Γ4 hΓ_pos.le
    have hbd1_eq : ε / (Γ * (3 * Γ / 4)) = 4 * ε / (3 * Γ^2) := by
      field_simp
    have hbd2 : 4 * ε / (3 * Γ^2) ≤ 4 * (Γ^2 * Real.exp (-(r:ℝ)) / 32) / (3 * Γ^2) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      linarith [hε_le_key]
    have hbd2_eq : 4 * (Γ^2 * Real.exp (-(r:ℝ)) / 32) / (3 * Γ^2)
        = Real.exp (-(r:ℝ)) / 24 := by
      field_simp
      ring
    have : ε / (Γ * (Γ - ε)) ≤ Real.exp (-(r:ℝ)) / 24 := by
      calc ε / (Γ * (Γ - ε))
          ≤ ε / (Γ * (3 * Γ / 4)) := hbd1
        _ = 4 * ε / (3 * Γ^2) := hbd1_eq
        _ ≤ 4 * (Γ^2 * Real.exp (-(r:ℝ)) / 32) / (3 * Γ^2) := hbd2
        _ = Real.exp (-(r:ℝ)) / 24 := hbd2_eq
    linarith
  -- Piece 2: (z(T) + 1/(Γ-ε)) · exp(-(Γ-ε)(t-T)) ≤ exp(-r)/3.
  -- coef ≤ 2·Bz since 1/(Γ-ε) ≤ 2/Γ = 2γ ≤ Bz.
  have hcoef_le : zTraj Z T + 1 / (Γ - ε) ≤ 2 * Bz Z := by
    have h1 : 1 / (Γ - ε) ≤ 2 / Γ := by
      rw [div_le_div_iff₀ hΓε_pos hΓ_pos]
      linarith
    have h2 : (2 : ℝ) / Γ = 2 * γ := by simp only [hΓ_def]; field_simp
    have h3 : 2 * γ ≤ Bz Z := Bz_ge_two_mul_gamma Z
    linarith
  have hcoef_nn : 0 ≤ zTraj Z T + 1 / (Γ - ε) := by
    have : 0 ≤ 1 / (Γ - ε) := by positivity
    linarith
  have hExpDecay_le : Real.exp (-(Γ - ε) * (t - T)) ≤ Real.exp (-(Γ/2) * (t - T)) := by
    apply Real.exp_le_exp.mpr
    have htT_nn : 0 ≤ t - T := by linarith
    have : Γ/2 ≤ Γ - ε := hΓε_ge_half
    have hmul : (Γ/2) * (t - T) ≤ (Γ - ε) * (t - T) :=
      mul_le_mul_of_nonneg_right this htT_nn
    linarith
  have hExpDecay_nn : 0 ≤ Real.exp (-(Γ/2) * (t - T)) := (Real.exp_pos _).le
  -- Lower bound on (Γ/2)·(t - T) from htmT_ge:
  -- zModulus has "(4γ)·(r + log(6·Bz) + 1)" = (4/Γ)·(...).
  -- So t - T ≥ (4/Γ)·(...), i.e., (Γ/2)(t-T) ≥ 2·(...).
  have htmT_ge : t - T ≥ (4 * γ) * ((r : ℝ) + Real.log (6 * Bz Z) + 1) := by
    have h2 : zModulus Z r
        = max (Tstar Z + 1) (Z.zrModulus (2 * chooseN0B γ + r + 2) + 1)
          + (4 * γ) * ((r : ℝ) + Real.log (6 * Bz Z) + 1) := rfl
    -- T = max(Tstar Z + 1, Z.zrModulus Nr + 1), so T ≤ max(...) = T by definition.
    have hT_eq : T = max (Tstar Z + 1) (Z.zrModulus (2 * chooseN0B γ + r + 2) + 1) :=
      hT_def
    linarith [ht, h2, hT_eq]
  -- Convert: γ = 1/Γ, so (Γ/2)·(4γ) = (Γ/2)·(4/Γ) = 2.
  have hγ_eq : γ = 1 / Γ := by simp only [hΓ_def]; rw [one_div_one_div]
  have hΓ_tT_ge : (Γ / 2) * (t - T) ≥ 2 * ((r : ℝ) + Real.log (6 * Bz Z) + 1) := by
    have hΓ2_pos : 0 < Γ / 2 := by linarith
    have h := mul_le_mul_of_nonneg_left htmT_ge hΓ2_pos.le
    have hΓ_ne : Γ ≠ 0 := ne_of_gt hΓ_pos
    have heq_half : (Γ / 2) * (4 * γ) = 2 := by
      rw [hγ_eq]
      field_simp
      norm_num
    have heq : (Γ / 2) * ((4 * γ) * ((r : ℝ) + Real.log (6 * Bz Z) + 1))
        = 2 * ((r : ℝ) + Real.log (6 * Bz Z) + 1) := by
      calc (Γ / 2) * ((4 * γ) * ((r : ℝ) + Real.log (6 * Bz Z) + 1))
          = ((Γ / 2) * (4 * γ)) * ((r : ℝ) + Real.log (6 * Bz Z) + 1) := by ring
        _ = 2 * ((r : ℝ) + Real.log (6 * Bz Z) + 1) := by rw [heq_half]
    linarith
  have h6Bz_pos : 0 < 6 * Bz Z := by linarith
  have hExp_r_log : Real.exp (-(r : ℝ) - Real.log (6 * Bz Z)) =
      Real.exp (-(r:ℝ)) / (6 * Bz Z) := by
    have heq : (-(r : ℝ) - Real.log (6 * Bz Z)) = -(r:ℝ) + (-(Real.log (6 * Bz Z))) := by ring
    rw [heq, Real.exp_add]
    rw [show Real.exp (-(Real.log (6 * Bz Z))) = (6 * Bz Z)⁻¹ from by
      rw [Real.exp_neg, Real.exp_log h6Bz_pos]]
    rw [div_eq_mul_inv]
  have hDecay_bd : Real.exp (-(Γ/2) * (t - T)) ≤ Real.exp (-(r:ℝ)) / (6 * Bz Z) := by
    rw [← hExp_r_log]
    apply Real.exp_le_exp.mpr
    have hrln_nn : 0 ≤ (r:ℝ) + Real.log (6 * Bz Z) + 2 := by
      have : (0:ℝ) ≤ (r:ℝ) := by positivity
      linarith
    have h1 : 2 * ((r : ℝ) + Real.log (6 * Bz Z) + 1)
        ≥ (r : ℝ) + Real.log (6 * Bz Z) := by linarith
    have h2 : (Γ/2) * (t - T) ≥ (r : ℝ) + Real.log (6 * Bz Z) := by linarith
    linarith
  have hP2 : (zTraj Z T + 1 / (Γ - ε)) * Real.exp (-(Γ - ε) * (t - T))
      ≤ Real.exp (-(r:ℝ)) / 3 := by
    have h1 : (zTraj Z T + 1 / (Γ - ε)) * Real.exp (-(Γ - ε) * (t - T))
        ≤ (2 * Bz Z) * Real.exp (-(Γ/2) * (t - T)) := by
      have ha : (zTraj Z T + 1 / (Γ - ε)) * Real.exp (-(Γ - ε) * (t - T))
          ≤ (2 * Bz Z) * Real.exp (-(Γ - ε) * (t - T)) :=
        mul_le_mul_of_nonneg_right hcoef_le (Real.exp_pos _).le
      have hb : (2 * Bz Z) * Real.exp (-(Γ - ε) * (t - T))
          ≤ (2 * Bz Z) * Real.exp (-(Γ/2) * (t - T)) :=
        mul_le_mul_of_nonneg_left hExpDecay_le (by linarith)
      linarith
    have h2 : (2 * Bz Z) * Real.exp (-(Γ/2) * (t - T))
        ≤ (2 * Bz Z) * (Real.exp (-(r:ℝ)) / (6 * Bz Z)) :=
      mul_le_mul_of_nonneg_left hDecay_bd (by linarith)
    have h3 : (2 * Bz Z) * (Real.exp (-(r:ℝ)) / (6 * Bz Z))
        = Real.exp (-(r:ℝ)) / 3 := by
      field_simp
      ring
    linarith
  -- Combine pieces via hbound (which has Γ everywhere).
  -- hbound : |zTraj Z t - γ| ≤ ε / ((1/γ) · (1/γ - ε)) + (zTraj Z T + 1/(1/γ - ε)) · exp(-(1/γ - ε)(t-T))
  --        = ε / (Γ · (Γ - ε)) + (zTraj Z T + 1/(Γ - ε)) · exp(-(Γ - ε)(t-T))  [since Γ = 1/γ]
  have hsum : |zTraj Z t - γ|
      ≤ Real.exp (-(r:ℝ)) / 3 + Real.exp (-(r:ℝ)) / 3 := by
    have := hbound
    -- Rewrite hbound in terms of Γ.
    have h_gammaΓ : (1 : ℝ) / γ = Γ := hΓ_def.symm
    rw [h_gammaΓ] at this
    linarith [hP1, hP2]
  have hfinal : Real.exp (-(r:ℝ)) / 3 + Real.exp (-(r:ℝ)) / 3 < Real.exp (-(r:ℝ)) := by
    linarith [hExpR_pos]
  linarith

end zTraj

/-! ## Main export theorem. -/

/-- **Main Stage B theorem.**  Given a converging reciprocal tracker `zr` (with
target `1/γ`, `0 < γ < 1`), there exists a `z` trajectory satisfying Stage B of
Lemma 8: existence + continuity + ODE + non-negativity + uniform bound +
exponential convergence to `γ`. -/
theorem z_tracker_exists {γ : ℝ} (hγ_lo : 0 < γ) (hγ_hi : γ < 1)
    (Z : ZrData γ) :
    ∃ (z : ℝ → ℝ) (B_z : ℝ) (zMod : ℕ → ℝ),
      0 < B_z ∧
      Continuous z ∧
      z 0 = 0 ∧
      (∀ t, 0 ≤ t → HasDerivAt z (1 - Z.zr t * z t) t) ∧
      (∀ t, 0 ≤ t → 0 ≤ z t) ∧
      (∀ t, 0 ≤ t → z t ≤ B_z) ∧
      (∀ r : ℕ, ∀ t : ℝ, t > zMod r → |z t - γ| < Real.exp (-(r : ℝ))) := by
  refine ⟨zTraj Z, zTraj.Bz Z, zTraj.zModulus Z, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact zTraj.Bz_pos Z
  · exact zTraj.continuous Z
  · exact zTraj.zero Z
  · intro t _ht; exact zTraj.hasDerivAt Z t
  · intro t ht; exact zTraj.nonneg Z ht
  · intro t ht; exact zTraj.uniform_bound Z hγ_lo ht
  · exact zTraj.z_converges Z hγ_lo hγ_hi

end Lemma8StageB
end DualRail
end Ripple
