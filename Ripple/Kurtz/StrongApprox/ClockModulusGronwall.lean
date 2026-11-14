-- Ripple/Kurtz/StrongApprox/ClockModulusGronwall.lean
import Mathlib
import Ripple.Kurtz.IntegralGronwall

namespace Ripple.Kurtz.StrongApprox

open MeasureTheory Set Finset
open scoped BigOperators Interval

noncomputable section

variable {ι : Type*} [Fintype ι]

/-- Sum of channel weights. -/
noncomputable def channelWeight (a : ι → ℝ) : ℝ := ∑ l, a l

/-- Weighted sum of the channel clock Lipschitz constants. -/
noncomputable def channelClockLip (a k : ι → ℝ) : ℝ := ∑ l, a l * k l

theorem channelWeight_nonneg {a : ι → ℝ} (ha : ∀ l, 0 ≤ a l) :
    0 ≤ channelWeight a := by
  classical
  exact Finset.sum_nonneg fun l _ => ha l

theorem channelClockLip_nonneg {a k : ι → ℝ}
    (ha : ∀ l, 0 ≤ a l) (hk : ∀ l, 0 ≤ k l) :
    0 ≤ channelClockLip a k := by
  classical
  exact Finset.sum_nonneg fun l _ => mul_nonneg (ha l) (hk l)

/-- The elementary entropy estimate `-h log h ≤ 1`. -/
theorem neg_mul_log_le_one {h : ℝ} (hh : 0 < h) :
    -h * Real.log h ≤ 1 := by
  have hlog := Real.log_le_sub_one_of_pos (inv_pos.mpr hh)
  rw [Real.log_inv] at hlog
  have hmul := mul_le_mul_of_nonneg_left hlog hh.le
  rw [mul_sub, mul_inv_cancel₀ hh.ne', mul_one] at hmul
  nlinarith

/-- If `log H + tail ≤ q`, then the entropy term is at most `q(h+1)`. -/
theorem entropy_modulus_term_le
    {H q tail h : ℝ} (hH : 0 < H) (hq : 1 ≤ q) (htail : 0 ≤ tail)
    (hqH : Real.log H + tail ≤ q) (hh0 : 0 ≤ h) (hhH : h ≤ H) :
    h * (Real.log (H / h) + tail) ≤ q * (h + 1) := by
  by_cases hhzero : h = 0
  · subst h
    simp
    linarith
  have hh : 0 < h := lt_of_le_of_ne hh0 (Ne.symm hhzero)
  have hratio : 1 ≤ H / h := (le_div_iff₀ hh).2 (by simpa using hhH)
  have hlogratio : 0 ≤ Real.log (H / h) := Real.log_nonneg hratio
  have hterm0 : 0 ≤ h * (Real.log (H / h) + tail) :=
    mul_nonneg hh0 (add_nonneg hlogratio htail)
  rw [Real.log_div hH.ne' hh.ne']
  have hmain := mul_le_mul_of_nonneg_left hqH hh0
  have hsmall := neg_mul_log_le_one hh
  nlinarith

/-- The entropy-shaped Brownian modulus has a global affine majorant.

The convention at `h = 0` is Lean's real-field convention; the product is zero. -/
theorem brownian_modulus_shape_le_affine
    {H N C tail q h : ℝ} (hH : 0 < H) (hN : 0 < N) (hC : 0 ≤ C)
    (htail : 0 ≤ tail) (hq : 1 ≤ q)
    (hqH : Real.log H + tail ≤ q) (hqN : Real.log N + tail ≤ q)
    (hh0 : 0 ≤ h) (hhH : h ≤ H) :
    C * Real.sqrt (h * (Real.log (H / h) + tail)) + C * (Real.log N + tail) ≤
      2 * C * q + (C / 2) * h := by
  have hent := entropy_modulus_term_le hH hq htail hqH hh0 hhH
  have hsqrt :
      Real.sqrt (h * (Real.log (H / h) + tail)) ≤ (q + h + 1) / 2 := by
    rw [Real.sqrt_le_iff]
    constructor
    · nlinarith
    · nlinarith [sq_nonneg (q - (h + 1))]
  have hmul := mul_le_mul_of_nonneg_left hsqrt hC
  have hlog := mul_le_mul_of_nonneg_left hqN hC
  nlinarith

/-- Deterministic nonlinear-clock comparison once the modulus has an affine envelope.

`u` is the path error and `∫u` is the accumulated error.  The clipped argument is the
only place the clock horizon enters. -/
theorem clock_modulus_gronwall_of_affine
    {T N H R qZero qSlope drift : ℝ}
    {a k : ι → ℝ} {omega u : ℝ → ℝ}
    (hT : 0 ≤ T) (hN : 0 < N) (hH : 0 ≤ H) (hR : 0 ≤ R)
    (hqZero : 0 ≤ qZero) (hqSlope : 0 ≤ qSlope) (hDrift : 0 ≤ drift)
    (ha : ∀ l, 0 ≤ a l) (hk : ∀ l, 0 ≤ k l)
    (hu_nonneg : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ u t)
    (huint : IntegrableOn u (Icc (0 : ℝ) T))
    (hurc : ∀ t ∈ Ico (0 : ℝ) T,
      ContinuousWithinAt u (Ioi t) t)
    (homega : ∀ h ∈ Icc (0 : ℝ) H, omega h ≤ qZero + qSlope * h)
    (hraw : ∀ t ∈ Icc (0 : ℝ) T,
      u t ≤ channelWeight a * R / N +
        drift * (∫ s in (0 : ℝ)..t, u s) +
        (∑ l, a l * omega
          (min H (N * k l * (∫ s in (0 : ℝ)..t, u s)))) / N)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    u t ≤ channelWeight a * (R + qZero) / N *
      Real.exp ((drift + qSlope * channelClockLip a k) * t) := by
  classical
  let S : ℝ := channelWeight a
  let Ksum : ℝ := channelClockLip a k
  have hS : 0 ≤ S := by
    dsimp [S]
    exact channelWeight_nonneg ha
  have hKsum : 0 ≤ Ksum := by
    dsimp [Ksum]
    exact channelClockLip_nonneg ha hk
  have hlinear : ∀ r ∈ Icc (0 : ℝ) T,
      u r ≤ S * (R + qZero) / N +
        (drift + qSlope * Ksum) * (∫ s in (0 : ℝ)..r, u s) := by
    intro r hr
    let I : ℝ := ∫ s in (0 : ℝ)..r, u s
    have hI : 0 ≤ I := by
      dsimp [I]
      exact intervalIntegral.integral_nonneg hr.1 fun s hs =>
        hu_nonneg s ⟨hs.1, hs.2.trans hr.2⟩
    have harg0 (l : ι) : 0 ≤ min H (N * k l * I) :=
      le_min hH (mul_nonneg (mul_nonneg hN.le (hk l)) hI)
    have hargH (l : ι) : min H (N * k l * I) ≤ H := min_le_left _ _
    have hsum :
        (∑ l, a l * omega (min H (N * k l * I))) ≤
          ∑ l, a l * (qZero + qSlope * (N * k l * I)) := by
      refine Finset.sum_le_sum fun l _ => ?_
      have h1 := homega _ ⟨harg0 l, hargH l⟩
      have h2 : qSlope * min H (N * k l * I) ≤ qSlope * (N * k l * I) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) hqSlope
      exact mul_le_mul_of_nonneg_left (by linarith) (ha l)
    have hsumId :
        (∑ l, a l * (qZero + qSlope * (N * k l * I))) =
          qZero * S + (qSlope * N * I) * Ksum := by
      dsimp [S, Ksum, channelWeight, channelClockLip]
      calc
        (∑ l, a l * (qZero + qSlope * (N * k l * I))) =
            ∑ l, (qZero * a l + (qSlope * N * I) * (a l * k l)) := by
              refine Finset.sum_congr rfl fun l _ => ?_
              ring
        _ = qZero * (∑ l, a l) +
              (qSlope * N * I) * (∑ l, a l * k l) := by
              rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    have hcollapse :
        S * R / N + drift * I +
            (qZero * S + qSlope * N * I * Ksum) / N =
          S * (R + qZero) / N + (drift + qSlope * Ksum) * I := by
      field_simp [hN.ne']
      ring
    have hraw' :
        u r ≤ S * R / N + drift * I +
          (∑ l, a l * omega (min H (N * k l * I))) / N := by
      simpa [S, I] using hraw r hr
    have hsumDiv := div_le_div_of_nonneg_right hsum hN.le
    calc
      u r ≤ S * R / N + drift * I +
          (∑ l, a l * omega (min H (N * k l * I))) / N := hraw'
      _ ≤ S * R / N + drift * I +
          (∑ l, a l * (qZero + qSlope * (N * k l * I))) / N := by
            linarith
      _ = S * (R + qZero) / N + (drift + qSlope * Ksum) * I := by
            rw [hsumId]
            exact hcollapse
  have hA : 0 ≤ S * (R + qZero) / N :=
    div_nonneg (mul_nonneg hS (add_nonneg hR hqZero)) hN.le
  have hB : 0 ≤ drift + qSlope * Ksum :=
    add_nonneg hDrift (mul_nonneg hqSlope hKsum)
  have hineq : ∀ r ∈ Icc (0 : ℝ) T,
      u r ≤ S * (R + qZero) / N +
        ∫ s in (0 : ℝ)..r, (drift + qSlope * Ksum) * u s := by
    intro r hr
    rw [intervalIntegral.integral_const_mul]
    exact hlinear r hr
  have hBu_int : IntegrableOn
      (fun s => (drift + qSlope * Ksum) * u s) (Icc (0 : ℝ) T) :=
    huint.const_mul _
  exact Ripple.Kurtz.integral_gronwall
    (T := T) (α := S * (R + qZero) / N)
    (β := drift + qSlope * Ksum) (u := u)
    hT hA hB hu_nonneg hineq
    (fun r hr => (intervalIntegrable_iff_integrableOn_Icc_of_le hr.1).mpr
      (hBu_int.mono_set (Icc_subset_Icc_right hr.2.le)))
    (fun r hr => tendsto_const_nhds.mul (hurc r hr))
    (fun r hr => ⟨Icc 0 T, Icc_mem_nhdsGT_of_mem hr,
      hBu_int.aestronglyMeasurable⟩)
    (by
      have hint : IntegrableOn
          (fun s => (drift + qSlope * Ksum) * u s) (uIcc 0 T) volume := by
        rw [uIcc_of_le hT]
        exact hBu_int
      have hprim := intervalIntegral.continuousOn_primitive_interval hint
      rw [uIcc_of_le hT] at hprim
      exact continuousOn_const.add hprim)
    t ht

/-- Brownian entropy-envelope specialization of `clock_modulus_gronwall_of_affine`. -/
theorem clock_modulus_gronwall_of_brownian_shape
    {T N H R C tail q drift : ℝ}
    {a k : ι → ℝ} {omega u : ℝ → ℝ}
    (hT : 0 ≤ T) (hN : 0 < N) (hH : 0 < H) (hR : 0 ≤ R)
    (hC : 0 ≤ C) (htail : 0 ≤ tail) (hq : 1 ≤ q)
    (hqH : Real.log H + tail ≤ q) (hqN : Real.log N + tail ≤ q)
    (hRq : R ≤ q) (hDrift : 0 ≤ drift)
    (ha : ∀ l, 0 ≤ a l) (hk : ∀ l, 0 ≤ k l)
    (hu_nonneg : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ u t)
    (huint : IntegrableOn u (Icc (0 : ℝ) T))
    (hurc : ∀ t ∈ Ico (0 : ℝ) T,
      ContinuousWithinAt u (Ioi t) t)
    (hshape : ∀ h ∈ Icc (0 : ℝ) H,
      omega h ≤ C * Real.sqrt (h * (Real.log (H / h) + tail)) +
        C * (Real.log N + tail))
    (hraw : ∀ t ∈ Icc (0 : ℝ) T,
      u t ≤ channelWeight a * R / N +
        drift * (∫ s in (0 : ℝ)..t, u s) +
        (∑ l, a l * omega
          (min H (N * k l * (∫ s in (0 : ℝ)..t, u s)))) / N)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    u t ≤ channelWeight a * ((1 + 2 * C) * q) / N *
      Real.exp ((drift + (C / 2) * channelClockLip a k) * t) := by
  have homega : ∀ h ∈ Icc (0 : ℝ) H,
      omega h ≤ 2 * C * q + (C / 2) * h := by
    intro h hh
    exact (hshape h hh).trans
      (brownian_modulus_shape_le_affine hH hN hC htail hq hqH hqN hh.1 hh.2)
  have hmain := clock_modulus_gronwall_of_affine
    (T := T) (N := N) (H := H) (R := R)
    (qZero := 2 * C * q) (qSlope := C / 2) (drift := drift)
    (a := a) (k := k) (omega := omega) (u := u)
    hT hN hH.le hR (by positivity) (by positivity) hDrift ha hk
    hu_nonneg huint hurc homega hraw ht
  have hS : 0 ≤ channelWeight a := channelWeight_nonneg ha
  have hbase :
      channelWeight a * (R + 2 * C * q) / N ≤
        channelWeight a * ((1 + 2 * C) * q) / N := by
    apply div_le_div_of_nonneg_right _ hN.le
    apply mul_le_mul_of_nonneg_left _ hS
    nlinarith
  exact hmain.trans
    (mul_le_mul_of_nonneg_right hbase (Real.exp_pos _).le)

/-- The logarithmic budget used in the explicit `Γ_T` corollary. -/
theorem log_budget_le_factor
    {N D R tail : ℝ} (hN : 2 ≤ N) (hD : 1 ≤ D)
    (hR : 0 ≤ R) (htail : 0 ≤ tail) :
    R + Real.log N + tail + 1 + Real.log D ≤
      (1 + (1 + Real.log D) / Real.log 2) *
        (R + Real.log N + tail) := by
  let p : ℝ := R + Real.log N + tail
  let c : ℝ := 1 + Real.log D
  have hlogTwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlogN : Real.log (2 : ℝ) ≤ Real.log N :=
    Real.log_le_log (by norm_num) hN
  have hlogD : 0 ≤ Real.log D := Real.log_nonneg hD
  have hp : Real.log (2 : ℝ) ≤ p := by
    dsimp [p]
    linarith
  have hc : 0 ≤ c := by
    dsimp [c]
    linarith
  have hpDiv : 1 ≤ p / Real.log 2 := (le_div_iff₀ hlogTwo).2 (by rw [one_mul]; exact hp)
  have hcscale : c ≤ c / Real.log 2 * p := by
    calc
      c = c * 1 := by ring
      _ ≤ c * (p / Real.log 2) := mul_le_mul_of_nonneg_left hpDiv hc
      _ = c / Real.log 2 * p := by ring
  calc
    R + Real.log N + tail + 1 + Real.log D = p + c := by
      dsimp [p, c]
      ring
    _ ≤ p + c / Real.log 2 * p := by linarith
    _ = (1 + (1 + Real.log D) / Real.log 2) *
        (R + Real.log N + tail) := by
      dsimp [p, c]
      ring

/-- Explicit deterministic constant from the Brownian entropy modulus. -/
noncomputable def brownianComparisonGamma
    (S K C T D : ℝ) : ℝ :=
  S * (1 + 2 * C) *
    (1 + (1 + Real.log D) / Real.log 2) *
    Real.exp ((1 + C / 2) * K * T)

/-!
THEOREM LIST
* `neg_mul_log_le_one`, `entropy_modulus_term_le`
* `brownian_modulus_shape_le_affine`
* `clock_modulus_gronwall_of_affine`
* `clock_modulus_gronwall_of_brownian_shape`
* `log_budget_le_factor`, `brownianComparisonGamma`

CLOSES
* Scalar nonlinear-clock inequality -> affine Gronwall.
* Global affine envelope for the requested Brownian modulus.
* The algebraic logarithmic budget used by the explicit constant.
END
-/

end

end Ripple.Kurtz.StrongApprox
