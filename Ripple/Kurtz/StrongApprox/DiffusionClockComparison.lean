-- Ripple/Kurtz/StrongApprox/DiffusionClockComparison.lean
import Ripple.Kurtz.StrongApprox.ClockModulusGronwall
import Ripple.Kurtz.StrongApprox.ChainFluidLIL

namespace Ripple.Kurtz.StrongApprox

open MeasureTheory Set Finset
open scoped BigOperators Interval

noncomputable section

variable {d : ℕ} {ι : Type*} [Fintype ι]

/-- The scale-`N` internal clock. -/
noncomputable def scaledTcClock
    (N : ℝ) (beta : ι → (Fin d → ℝ) → ℝ)
    (X : ℝ → Fin d → ℝ) (l : ι) (t : ℝ) : ℝ :=
  N * clock beta X l t

/-- Compensated real-driver remainder. -/
noncomputable def realTimeChangeRemainder
    (beta : ι → (Fin d → ℝ) → ℝ) (v : ι → Fin d → ℝ)
    (Y : ι → ℝ → ℝ) (N : ℝ) (X : ℝ → Fin d → ℝ) (t : ℝ) : Fin d → ℝ :=
  ∑ l, ((Y l (scaledTcClock N beta X l t) -
    scaledTcClock N beta X l t) / N) • v l

/-- KMT error evaluated on the chain's own clock. -/
noncomputable def kmtDriverRemainder
    (beta : ι → (Fin d → ℝ) → ℝ) (v : ι → Fin d → ℝ)
    (Y W : ι → ℝ → ℝ) (N : ℝ) (X : ℝ → Fin d → ℝ) (t : ℝ) : Fin d → ℝ :=
  ∑ l, ((Y l (scaledTcClock N beta X l t) -
    scaledTcClock N beta X l t - W l (scaledTcClock N beta X l t)) / N) • v l

/-- Difference caused by evaluating the Brownian driver on the two clocks. -/
noncomputable def brownianClockShiftRemainder
    (beta : ι → (Fin d → ℝ) → ℝ) (v : ι → Fin d → ℝ)
    (W : ι → ℝ → ℝ) (N : ℝ)
    (X Z : ℝ → Fin d → ℝ) (t : ℝ) : Fin d → ℝ :=
  ∑ l, ((W l (scaledTcClock N beta X l t) -
    W l (scaledTcClock N beta Z l t)) / N) • v l

theorem intervalIntegrable_smul_const_vec
    {f : ℝ → ℝ} {a b : ℝ} (hf : IntervalIntegrable f volume a b)
    (w : Fin d → ℝ) :
    IntervalIntegrable (fun s => f s • w) volume a b :=
  ⟨hf.1.smul_const w, hf.2.smul_const w⟩

theorem intervalIntegrable_tcDrift
    {beta : ι → (Fin d → ℝ) → ℝ} {v : ι → Fin d → ℝ}
    {X : ℝ → Fin d → ℝ} {a b : ℝ}
    (hbeta : ∀ l, IntervalIntegrable (fun s => beta l (X s)) volume a b) :
    IntervalIntegrable (fun s => tcDrift beta v (X s)) volume a b := by
  classical
  have hfun : (fun s => tcDrift beta v (X s)) =
      ∑ l, fun s => beta l (X s) • v l := by
    funext s
    simp [tcDrift, Finset.sum_apply]
  rw [hfun]
  exact IntervalIntegrable.sum _ fun l _ => intervalIntegrable_smul_const_vec (hbeta l) (v l)

/-- The drift is Lipschitz on `U` with the explicit weighted channel constant. -/
theorem norm_tcDrift_sub_le_on
    {U : Set (Fin d → ℝ)}
    {beta : ι → (Fin d → ℝ) → ℝ} {v : ι → Fin d → ℝ}
    {K : ι → ℝ}
    (hK : ∀ l, 0 ≤ K l)
    (hbetaLip : ∀ l y z, y ∈ U → z ∈ U →
      |beta l y - beta l z| ≤ K l * ‖y - z‖)
    {y z : Fin d → ℝ} (hy : y ∈ U) (hz : z ∈ U) :
    ‖tcDrift beta v y - tcDrift beta v z‖ ≤
      channelClockLip (fun l => ‖v l‖) K * ‖y - z‖ := by
  classical
  have hid : tcDrift beta v y - tcDrift beta v z =
      ∑ l, (beta l y - beta l z) • v l := by
    unfold tcDrift
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [sub_smul]
  rw [hid]
  calc
    ‖∑ l, (beta l y - beta l z) • v l‖ ≤
        ∑ l, ‖(beta l y - beta l z) • v l‖ := norm_sum_le _ _
    _ ≤ ∑ l, (‖v l‖ * K l) * ‖y - z‖ := by
      refine Finset.sum_le_sum fun l _ => ?_
      rw [norm_smul, Real.norm_eq_abs]
      calc
        |beta l y - beta l z| * ‖v l‖ ≤
            (K l * ‖y - z‖) * ‖v l‖ :=
          mul_le_mul_of_nonneg_right (hbetaLip l y z hy hz) (norm_nonneg _)
        _ = (‖v l‖ * K l) * ‖y - z‖ := by ring
    _ = channelClockLip (fun l => ‖v l‖) K * ‖y - z‖ := by
      simp [channelClockLip, Finset.sum_mul]

/-- A local nonnegativity lemma for an internal clock. -/
theorem clock_nonneg_of_mem
    {U : Set (Fin d → ℝ)}
    {beta : ι → (Fin d → ℝ) → ℝ} {X : ℝ → Fin d → ℝ}
    {T : ℝ} (hbeta0 : ∀ l y, y ∈ U → 0 ≤ beta l y)
    (hXU : ∀ s ∈ Icc (0 : ℝ) T, X s ∈ U)
    {l : ι} {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    0 ≤ clock beta X l t := by
  unfold clock
  exact intervalIntegral.integral_nonneg ht.1 fun s hs =>
    hbeta0 l (X s) (hXU s ⟨hs.1, hs.2.trans ht.2⟩)

/-- A local upper bound for an internal clock. -/
theorem clock_le_of_mem
    {U : Set (Fin d → ℝ)}
    {beta : ι → (Fin d → ℝ) → ℝ} {B : ι → ℝ}
    {X : ℝ → Fin d → ℝ} {T : ℝ}
    (hbetaB : ∀ l y, y ∈ U → beta l y ≤ B l)
    (hXU : ∀ s ∈ Icc (0 : ℝ) T, X s ∈ U)
    {l : ι} {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T)
    (hbetaInt : IntervalIntegrable (fun s => beta l (X s)) volume 0 t) :
    clock beta X l t ≤ B l * t := by
  unfold clock
  have h := intervalIntegral.integral_mono_on ht.1 hbetaInt
    intervalIntegrable_const (fun s hs =>
      hbetaB l (X s) (hXU s ⟨hs.1, hs.2.trans ht.2⟩))
  rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_comm] at h
  exact h

/-- Both endpoints of a scale-`N` clock lie in the supplied horizon. -/
theorem scaledTcClock_mem_horizon
    {U : Set (Fin d → ℝ)}
    {beta : ι → (Fin d → ℝ) → ℝ} {B : ι → ℝ}
    {X : ℝ → Fin d → ℝ} {N T H : ℝ}
    (hN : 0 < N) (hT : 0 ≤ T) (hB : ∀ l, 0 ≤ B l)
    (hbeta0 : ∀ l y, y ∈ U → 0 ≤ beta l y)
    (hbetaB : ∀ l y, y ∈ U → beta l y ≤ B l)
    (hXU : ∀ s ∈ Icc (0 : ℝ) T, X s ∈ U)
    {l : ι} {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T)
    (hbetaInt : IntervalIntegrable (fun s => beta l (X s)) volume 0 t)
    (hHorizon : N * (B l * T) ≤ H) :
    scaledTcClock N beta X l t ∈ Icc (0 : ℝ) H := by
  have hclock0 := clock_nonneg_of_mem (l := l) hbeta0 hXU ht
  have hclockB := clock_le_of_mem hbetaB hXU ht hbetaInt
  have hclockT : clock beta X l t ≤ B l * T := by
    exact hclockB.trans (mul_le_mul_of_nonneg_left ht.2 (hB l))
  constructor
  · exact mul_nonneg hN.le hclock0
  · exact (mul_le_mul_of_nonneg_left hclockT hN.le).trans hHorizon

/-- Difference of two scale-`N` clocks. -/
theorem abs_scaledTcClock_sub_le
    {U : Set (Fin d → ℝ)}
    {beta : ι → (Fin d → ℝ) → ℝ} {K : ι → ℝ}
    {X Z : ℝ → Fin d → ℝ} {N T : ℝ}
    (hN : 0 < N) (hK : ∀ l, 0 ≤ K l)
    (hbetaLip : ∀ l y z, y ∈ U → z ∈ U →
      |beta l y - beta l z| ≤ K l * ‖y - z‖)
    (hXU : ∀ s ∈ Icc (0 : ℝ) T, X s ∈ U)
    (hZU : ∀ s ∈ Icc (0 : ℝ) T, Z s ∈ U)
    (huint : IntegrableOn (fun s => ‖X s - Z s‖) (Icc (0 : ℝ) T))
    {l : ι} {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T)
    (hbetaX : IntervalIntegrable (fun s => beta l (X s)) volume 0 t)
    (hbetaZ : IntervalIntegrable (fun s => beta l (Z s)) volume 0 t) :
    |scaledTcClock N beta X l t - scaledTcClock N beta Z l t| ≤
      N * K l * (∫ s in (0 : ℝ)..t, ‖X s - Z s‖) := by
  have hKint : IntervalIntegrable
      (fun s => K l * ‖X s - Z s‖) volume 0 t :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le ht.1).mpr
      ((show IntegrableOn (fun x => K l * ‖X x - Z x‖) (Icc (0:ℝ) T) volume from Integrable.const_mul huint (K l)).mono_set (Icc_subset_Icc_right ht.2))
  have hnorm :
      |clock beta X l t - clock beta Z l t| ≤
        ∫ s in (0 : ℝ)..t, K l * ‖X s - Z s‖ := by
    unfold clock
    rw [← intervalIntegral.integral_sub hbetaX hbetaZ]
    rw [← Real.norm_eq_abs]
    refine (intervalIntegral.norm_integral_le_integral_norm ht.1).trans ?_
    exact intervalIntegral.integral_mono_on ht.1 (hbetaX.sub hbetaZ).norm hKint
      fun s hs => by
        rw [Real.norm_eq_abs]
        exact hbetaLip l (X s) (Z s)
          (hXU s ⟨hs.1, hs.2.trans ht.2⟩)
          (hZU s ⟨hs.1, hs.2.trans ht.2⟩)
  rw [intervalIntegral.integral_const_mul] at hnorm
  unfold scaledTcClock
  rw [← mul_sub, abs_mul, abs_of_pos hN]
  simpa [mul_assoc] using mul_le_mul_of_nonneg_left hnorm hN.le

/-- Rewrite a real-driver time-change equation as drift plus compensated remainder. -/
theorem real_timeChange_eq_drift
    {beta : ι → (Fin d → ℝ) → ℝ} {v : ι → Fin d → ℝ}
    {Y : ι → ℝ → ℝ} {N : ℝ} {X : ℝ → Fin d → ℝ}
    {xZero : Fin d → ℝ} {t : ℝ} (hN : 0 < N)
    (hbetaInt : ∀ l, IntervalIntegrable (fun s => beta l (X s)) volume 0 t)
    (hX : X t = xZero + ∑ l,
      (Y l (scaledTcClock N beta X l t) / N) • v l) :
    X t = xZero + (∫ s in (0 : ℝ)..t, tcDrift beta v (X s)) +
      realTimeChangeRemainder beta v Y N X t := by
  classical
  have hint : ∫ s in (0 : ℝ)..t, tcDrift beta v (X s) =
      ∑ l, clock beta X l t • v l := by
    unfold tcDrift clock
    rw [intervalIntegral.integral_finsetSum
      (fun l _ => intervalIntegrable_smul_const_vec (hbetaInt l) (v l))]
    exact Finset.sum_congr rfl fun l _ => intervalIntegral.integral_smul_const _ _
  rw [hX, hint, add_assoc]
  congr 1
  unfold realTimeChangeRemainder
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← add_smul]
  congr 1
  unfold scaledTcClock
  field_simp [hN.ne']
  ring

/-- Exact subtraction identity for the chain and Brownian-clock equations. -/
theorem timeChange_diffusion_sub
    {beta : ι → (Fin d → ℝ) → ℝ} {v : ι → Fin d → ℝ}
    {Y W : ι → ℝ → ℝ} {N : ℝ}
    {X Z : ℝ → Fin d → ℝ} {xZero : Fin d → ℝ} {t : ℝ}
    (hN : 0 < N)
    (hbetaX : ∀ l, IntervalIntegrable (fun s => beta l (X s)) volume 0 t)
    (hbetaZ : ∀ l, IntervalIntegrable (fun s => beta l (Z s)) volume 0 t)
    (hX : X t = xZero + ∑ l,
      (Y l (scaledTcClock N beta X l t) / N) • v l)
    (hZ : Z t = xZero + (∫ s in (0 : ℝ)..t, tcDrift beta v (Z s)) +
      ∑ l, (W l (scaledTcClock N beta Z l t) / N) • v l) :
    X t - Z t =
      (∫ s in (0 : ℝ)..t,
        (tcDrift beta v (X s) - tcDrift beta v (Z s))) +
      kmtDriverRemainder beta v Y W N X t +
      brownianClockShiftRemainder beta v W N X Z t := by
  classical
  have hXd := real_timeChange_eq_drift hN hbetaX hX
  have hFX := intervalIntegrable_tcDrift (v := v) hbetaX
  have hFZ := intervalIntegrable_tcDrift (v := v) hbetaZ
  have hsum :
      realTimeChangeRemainder beta v Y N X t -
          (∑ l, (W l (scaledTcClock N beta Z l t) / N) • v l) =
        kmtDriverRemainder beta v Y W N X t +
          brownianClockShiftRemainder beta v W N X Z t := by
    unfold realTimeChangeRemainder kmtDriverRemainder brownianClockShiftRemainder
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← sub_smul, ← add_smul]
    congr 1
    field_simp [hN.ne']
    ring
  calc
    X t - Z t =
        (xZero + (∫ s in (0 : ℝ)..t, tcDrift beta v (X s)) +
            realTimeChangeRemainder beta v Y N X t) -
          (xZero + (∫ s in (0 : ℝ)..t, tcDrift beta v (Z s)) +
            ∑ l, (W l (scaledTcClock N beta Z l t) / N) • v l) := by
              rw [hXd, hZ]
    _ = ((∫ s in (0 : ℝ)..t, tcDrift beta v (X s)) -
          (∫ s in (0 : ℝ)..t, tcDrift beta v (Z s))) +
        (realTimeChangeRemainder beta v Y N X t -
          ∑ l, (W l (scaledTcClock N beta Z l t) / N) • v l) := by
            abel
    _ = (∫ s in (0 : ℝ)..t,
          (tcDrift beta v (X s) - tcDrift beta v (Z s))) +
        (kmtDriverRemainder beta v Y W N X t +
          brownianClockShiftRemainder beta v W N X Z t) := by
            rw [intervalIntegral.integral_sub hFX hFZ, hsum]
    _ = (∫ s in (0 : ℝ)..t,
          (tcDrift beta v (X s) - tcDrift beta v (Z s))) +
        kmtDriverRemainder beta v Y W N X t +
        brownianClockShiftRemainder beta v W N X Z t := by
          abel

/-- Norm bound for the KMT part of the remainder. -/
theorem norm_kmtDriverRemainder_le
    {beta : ι → (Fin d → ℝ) → ℝ} {v : ι → Fin d → ℝ}
    {Y W : ι → ℝ → ℝ} {N H R : ℝ} {X : ℝ → Fin d → ℝ} {t : ℝ}
    (hN : 0 < N) (hR : 0 ≤ R)
    (hclock : ∀ l, scaledTcClock N beta X l t ∈ Icc (0 : ℝ) H)
    (hKMT : ∀ l u, u ∈ Icc (0 : ℝ) H → |Y l u - u - W l u| ≤ R) :
    ‖kmtDriverRemainder beta v Y W N X t‖ ≤
      channelWeight (fun l => ‖v l‖) * R / N := by
  classical
  unfold kmtDriverRemainder
  refine (norm_sum_le _ _).trans ?_
  calc
    (∑ l, ‖((Y l (scaledTcClock N beta X l t) -
        scaledTcClock N beta X l t - W l (scaledTcClock N beta X l t)) / N) • v l‖) ≤
      ∑ l, (R / N) * ‖v l‖ := by
        refine Finset.sum_le_sum fun l _ => ?_
        rw [norm_smul, Real.norm_eq_abs, abs_div, abs_of_pos hN]
        exact mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right
            (hKMT l _ (hclock l)) hN.le) (norm_nonneg _)
    _ = channelWeight (fun l => ‖v l‖) * R / N := by
      unfold channelWeight
      rw [← Finset.mul_sum]
      ring

/-- Norm bound for the Brownian clock-shift part of the remainder. -/
theorem norm_brownianClockShiftRemainder_le
    {U : Set (Fin d → ℝ)}
    {beta : ι → (Fin d → ℝ) → ℝ} {v : ι → Fin d → ℝ}
    {K : ι → ℝ} {W : ι → ℝ → ℝ} {omega : ℝ → ℝ}
    {N T H : ℝ} {X Z : ℝ → Fin d → ℝ} {t : ℝ}
    (hN : 0 < N) (hK : ∀ l, 0 ≤ K l)
    (hbetaLip : ∀ l y z, y ∈ U → z ∈ U →
      |beta l y - beta l z| ≤ K l * ‖y - z‖)
    (hXU : ∀ s ∈ Icc (0 : ℝ) T, X s ∈ U)
    (hZU : ∀ s ∈ Icc (0 : ℝ) T, Z s ∈ U)
    (huint : IntegrableOn (fun s => ‖X s - Z s‖) (Icc (0 : ℝ) T))
    (ht : t ∈ Icc (0 : ℝ) T)
    (hbetaX : ∀ l, IntervalIntegrable (fun s => beta l (X s)) volume 0 t)
    (hbetaZ : ∀ l, IntervalIntegrable (fun s => beta l (Z s)) volume 0 t)
    (hclockX : ∀ l, scaledTcClock N beta X l t ∈ Icc (0 : ℝ) H)
    (hclockZ : ∀ l, scaledTcClock N beta Z l t ∈ Icc (0 : ℝ) H)
    (homega : Monotone omega)
    (hWmod : ∀ l u w, u ∈ Icc (0 : ℝ) H → w ∈ Icc (0 : ℝ) H →
      |W l u - W l w| ≤ omega |u - w|) :
    ‖brownianClockShiftRemainder beta v W N X Z t‖ ≤
      (∑ l, ‖v l‖ * omega
        (min H (N * K l * (∫ s in (0 : ℝ)..t, ‖X s - Z s‖)))) / N := by
  classical
  unfold brownianClockShiftRemainder
  refine (norm_sum_le _ _).trans ?_
  calc
    (∑ l, ‖((W l (scaledTcClock N beta X l t) -
        W l (scaledTcClock N beta Z l t)) / N) • v l‖) ≤
      ∑ l, (‖v l‖ * omega
        (min H (N * K l * (∫ s in (0 : ℝ)..t, ‖X s - Z s‖)))) / N := by
        refine Finset.sum_le_sum fun l _ => ?_
        let ux := scaledTcClock N beta X l t
        let uz := scaledTcClock N beta Z l t
        have hgapH : |ux - uz| ≤ H := by
          rw [abs_le]
          constructor <;> dsimp [ux, uz] <;>
            linarith [(hclockX l).1, (hclockX l).2,
              (hclockZ l).1, (hclockZ l).2]
        have hgapK : |ux - uz| ≤
            N * K l * (∫ s in (0 : ℝ)..t, ‖X s - Z s‖) := by
          dsimp [ux, uz]
          exact abs_scaledTcClock_sub_le hN hK hbetaLip hXU hZU huint ht
            (hbetaX l) (hbetaZ l)
        have hgap : |ux - uz| ≤
            min H (N * K l * (∫ s in (0 : ℝ)..t, ‖X s - Z s‖)) :=
          le_min hgapH hgapK
        have hw := hWmod l ux uz (hclockX l) (hclockZ l)
        have hom := homega hgap
        rw [norm_smul, Real.norm_eq_abs, abs_div, abs_of_pos hN]
        calc
          |W l ux - W l uz| / N * ‖v l‖ ≤
              omega |ux - uz| / N * ‖v l‖ :=
            mul_le_mul_of_nonneg_right
              (div_le_div_of_nonneg_right hw hN.le) (norm_nonneg _)
          _ ≤ omega (min H
                (N * K l * (∫ s in (0 : ℝ)..t, ‖X s - Z s‖))) / N * ‖v l‖ :=
            mul_le_mul_of_nonneg_right
              (div_le_div_of_nonneg_right hom hN.le) (norm_nonneg _)
          _ = ‖v l‖ * omega (min H
                (N * K l * (∫ s in (0 : ℝ)..t, ‖X s - Z s‖))) / N := by
            ring
    _ = (∑ l, ‖v l‖ * omega
          (min H (N * K l * (∫ s in (0 : ℝ)..t, ‖X s - Z s‖)))) / N := by
      rw [Finset.sum_div]

/-- The corrected general statement: the path equations imply the nonlinear clock-modulus
integral inequality (1). -/
theorem timeChange_diffusion_nonlinear_inequality
    {U : Set (Fin d → ℝ)}
    {beta : ι → (Fin d → ℝ) → ℝ} {v : ι → Fin d → ℝ}
    {B K : ι → ℝ} {Y W : ι → ℝ → ℝ} {omega : ℝ → ℝ}
    {N T H R : ℝ} {X Z : ℝ → Fin d → ℝ} {xZero : Fin d → ℝ}
    (hN : 0 < N) (hT : 0 ≤ T) (hH : 0 ≤ H) (hR : 0 ≤ R)
    (hB : ∀ l, 0 ≤ B l) (hK : ∀ l, 0 ≤ K l)
    (hbeta0 : ∀ l y, y ∈ U → 0 ≤ beta l y)
    (hbetaB : ∀ l y, y ∈ U → beta l y ≤ B l)
    (hbetaLip : ∀ l y z, y ∈ U → z ∈ U →
      |beta l y - beta l z| ≤ K l * ‖y - z‖)
    (hXU : ∀ s ∈ Icc (0 : ℝ) T, X s ∈ U)
    (hZU : ∀ s ∈ Icc (0 : ℝ) T, Z s ∈ U)
    (hbetaX : ∀ l t, t ∈ Icc (0 : ℝ) T →
      IntervalIntegrable (fun s => beta l (X s)) volume 0 t)
    (hbetaZ : ∀ l t, t ∈ Icc (0 : ℝ) T →
      IntervalIntegrable (fun s => beta l (Z s)) volume 0 t)
    (huint : IntegrableOn (fun s => ‖X s - Z s‖) (Icc (0 : ℝ) T))
    (hHorizon : ∀ l, N * (B l * T) ≤ H)
    (hXeq : ∀ t ∈ Icc (0 : ℝ) T,
      X t = xZero + ∑ l,
        (Y l (scaledTcClock N beta X l t) / N) • v l)
    (hZeq : ∀ t ∈ Icc (0 : ℝ) T,
      Z t = xZero + (∫ s in (0 : ℝ)..t, tcDrift beta v (Z s)) +
        ∑ l, (W l (scaledTcClock N beta Z l t) / N) • v l)
    (hKMT : ∀ l u, u ∈ Icc (0 : ℝ) H → |Y l u - u - W l u| ≤ R)
    (_hWcontinuous : ∀ l, Continuous (W l))
    (homega : Monotone omega)
    (hWmod : ∀ l u w, u ∈ Icc (0 : ℝ) H → w ∈ Icc (0 : ℝ) H →
      |W l u - W l w| ≤ omega |u - w|)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    ‖X t - Z t‖ ≤
      channelWeight (fun l => ‖v l‖) * R / N +
      channelClockLip (fun l => ‖v l‖) K *
        (∫ s in (0 : ℝ)..t, ‖X s - Z s‖) +
      (∑ l, ‖v l‖ * omega
        (min H (N * K l * (∫ s in (0 : ℝ)..t, ‖X s - Z s‖)))) / N := by
  classical
  let Ksum : ℝ := channelClockLip (fun l => ‖v l‖) K
  have hKsum : 0 ≤ Ksum := by
    dsimp [Ksum]
    exact channelClockLip_nonneg (fun l => norm_nonneg _) hK
  have hclockX : ∀ l, scaledTcClock N beta X l t ∈ Icc (0 : ℝ) H := fun l =>
    scaledTcClock_mem_horizon hN hT hB hbeta0 hbetaB hXU ht
      (hbetaX l t ht) (hHorizon l)
  have hclockZ : ∀ l, scaledTcClock N beta Z l t ∈ Icc (0 : ℝ) H := fun l =>
    scaledTcClock_mem_horizon hN hT hB hbeta0 hbetaB hZU ht
      (hbetaZ l t ht) (hHorizon l)
  have hid := timeChange_diffusion_sub hN
    (fun l => hbetaX l t ht) (fun l => hbetaZ l t ht)
    (hXeq t ht) (hZeq t ht)
  have hkmt := norm_kmtDriverRemainder_le (v := v) hN hR hclockX hKMT
  have hshift := norm_brownianClockShiftRemainder_le (v := v)
    hN hK hbetaLip hXU hZU huint ht
    (fun l => hbetaX l t ht) (fun l => hbetaZ l t ht)
    hclockX hclockZ homega hWmod
  have hFX := intervalIntegrable_tcDrift (v := v) (fun l => hbetaX l t ht)
  have hFZ := intervalIntegrable_tcDrift (v := v) (fun l => hbetaZ l t ht)
  have hKint : IntervalIntegrable
      (fun s => Ksum * ‖X s - Z s‖) volume 0 t :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le ht.1).mpr
      ((show IntegrableOn (fun x => Ksum * ‖X x - Z x‖) (Icc (0:ℝ) T) volume from Integrable.const_mul huint Ksum).mono_set (Icc_subset_Icc_right ht.2))
  have hnormF :
      ‖∫ s in (0 : ℝ)..t,
        (tcDrift beta v (X s) - tcDrift beta v (Z s))‖ ≤
        Ksum * (∫ s in (0 : ℝ)..t, ‖X s - Z s‖) := by
    refine (intervalIntegral.norm_integral_le_integral_norm ht.1).trans ?_
    have hmono := intervalIntegral.integral_mono_on ht.1
      (hFX.sub hFZ).norm hKint fun s hs => by
        exact norm_tcDrift_sub_le_on hK hbetaLip
          (hXU s ⟨hs.1, hs.2.trans ht.2⟩)
          (hZU s ⟨hs.1, hs.2.trans ht.2⟩)
    rw [intervalIntegral.integral_const_mul] at hmono
    exact hmono
  rw [hid]
  have htri :=
    (norm_add_le
      ((∫ s in (0 : ℝ)..t,
        (tcDrift beta v (X s) - tcDrift beta v (Z s))) +
          kmtDriverRemainder beta v Y W N X t)
      (brownianClockShiftRemainder beta v W N X Z t)).trans
      (add_le_add (norm_add_le _ _) le_rfl)
  dsimp [Ksum] at hnormF ⊢
  linarith

/-- Affine-modulus pathwise comparison. -/
theorem timeChange_diffusion_comparison_of_affine
    {U : Set (Fin d → ℝ)}
    {beta : ι → (Fin d → ℝ) → ℝ} {v : ι → Fin d → ℝ}
    {B K : ι → ℝ} {Y W : ι → ℝ → ℝ} {omega : ℝ → ℝ}
    {N T H R qZero qSlope : ℝ}
    {X Z : ℝ → Fin d → ℝ} {xZero : Fin d → ℝ}
    (hN : 0 < N) (hT : 0 ≤ T) (hH : 0 ≤ H) (hR : 0 ≤ R)
    (hqZero : 0 ≤ qZero) (hqSlope : 0 ≤ qSlope)
    (hB : ∀ l, 0 ≤ B l) (hK : ∀ l, 0 ≤ K l)
    (hbeta0 : ∀ l y, y ∈ U → 0 ≤ beta l y)
    (hbetaB : ∀ l y, y ∈ U → beta l y ≤ B l)
    (hbetaLip : ∀ l y z, y ∈ U → z ∈ U →
      |beta l y - beta l z| ≤ K l * ‖y - z‖)
    (hXU : ∀ s ∈ Icc (0 : ℝ) T, X s ∈ U)
    (hZU : ∀ s ∈ Icc (0 : ℝ) T, Z s ∈ U)
    (hbetaX : ∀ l t, t ∈ Icc (0 : ℝ) T →
      IntervalIntegrable (fun s => beta l (X s)) volume 0 t)
    (hbetaZ : ∀ l t, t ∈ Icc (0 : ℝ) T →
      IntervalIntegrable (fun s => beta l (Z s)) volume 0 t)
    (huint : IntegrableOn (fun s => ‖X s - Z s‖) (Icc (0 : ℝ) T))
    (hurc : ∀ t ∈ Ico (0 : ℝ) T,
      ContinuousWithinAt (fun s => ‖X s - Z s‖) (Ioi t) t)
    (hHorizon : ∀ l, N * (B l * T) ≤ H)
    (hXeq : ∀ t ∈ Icc (0 : ℝ) T,
      X t = xZero + ∑ l,
        (Y l (scaledTcClock N beta X l t) / N) • v l)
    (hZeq : ∀ t ∈ Icc (0 : ℝ) T,
      Z t = xZero + (∫ s in (0 : ℝ)..t, tcDrift beta v (Z s)) +
        ∑ l, (W l (scaledTcClock N beta Z l t) / N) • v l)
    (hKMT : ∀ l u, u ∈ Icc (0 : ℝ) H → |Y l u - u - W l u| ≤ R)
    (hWcontinuous : ∀ l, Continuous (W l))
    (homegaMono : Monotone omega)
    (hWmod : ∀ l u w, u ∈ Icc (0 : ℝ) H → w ∈ Icc (0 : ℝ) H →
      |W l u - W l w| ≤ omega |u - w|)
    (homegaAffine : ∀ h ∈ Icc (0 : ℝ) H,
      omega h ≤ qZero + qSlope * h)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    ‖X t - Z t‖ ≤
      channelWeight (fun l => ‖v l‖) * (R + qZero) / N *
        Real.exp (((1 + qSlope) *
          channelClockLip (fun l => ‖v l‖) K) * t) := by
  have hraw := fun t (ht : t ∈ Icc (0 : ℝ) T) =>
    timeChange_diffusion_nonlinear_inequality
    hN hT hH hR hB hK hbeta0 hbetaB hbetaLip hXU hZU
    hbetaX hbetaZ huint hHorizon hXeq hZeq hKMT hWcontinuous
    homegaMono hWmod ht
  have hmain := clock_modulus_gronwall_of_affine
    (T := T) (N := N) (H := H) (R := R)
    (qZero := qZero) (qSlope := qSlope)
    (drift := channelClockLip (fun l => ‖v l‖) K)
    (a := fun l => ‖v l‖) (k := K) (omega := omega)
    (u := fun s => ‖X s - Z s‖)
    hT hN hH hR hqZero hqSlope
    (channelClockLip_nonneg (fun l => norm_nonneg _) hK)
    (fun l => norm_nonneg _) hK (fun _ _ => norm_nonneg _)
    huint hurc homegaAffine hraw ht
  have hcoef :
      channelClockLip (fun l => ‖v l‖) K +
          qSlope * channelClockLip (fun l => ‖v l‖) K =
        (1 + qSlope) * channelClockLip (fun l => ‖v l‖) K := by
    ring
  simpa [hcoef] using hmain

/-- Brownian entropy-modulus pathwise comparison with an explicit budget `q`. -/
theorem timeChange_diffusion_comparison_brownian
    {U : Set (Fin d → ℝ)}
    {beta : ι → (Fin d → ℝ) → ℝ} {v : ι → Fin d → ℝ}
    {B K : ι → ℝ} {Y W : ι → ℝ → ℝ} {omega : ℝ → ℝ}
    {N T H R C tail q : ℝ}
    {X Z : ℝ → Fin d → ℝ} {xZero : Fin d → ℝ}
    (hN : 0 < N) (hT : 0 ≤ T) (hH : 0 < H) (hR : 0 ≤ R)
    (hC : 0 ≤ C) (htail : 0 ≤ tail) (hq : 1 ≤ q)
    (hqH : Real.log H + tail ≤ q) (hqN : Real.log N + tail ≤ q)
    (hRq : R ≤ q)
    (hB : ∀ l, 0 ≤ B l) (hK : ∀ l, 0 ≤ K l)
    (hbeta0 : ∀ l y, y ∈ U → 0 ≤ beta l y)
    (hbetaB : ∀ l y, y ∈ U → beta l y ≤ B l)
    (hbetaLip : ∀ l y z, y ∈ U → z ∈ U →
      |beta l y - beta l z| ≤ K l * ‖y - z‖)
    (hXU : ∀ s ∈ Icc (0 : ℝ) T, X s ∈ U)
    (hZU : ∀ s ∈ Icc (0 : ℝ) T, Z s ∈ U)
    (hbetaX : ∀ l t, t ∈ Icc (0 : ℝ) T →
      IntervalIntegrable (fun s => beta l (X s)) volume 0 t)
    (hbetaZ : ∀ l t, t ∈ Icc (0 : ℝ) T →
      IntervalIntegrable (fun s => beta l (Z s)) volume 0 t)
    (huint : IntegrableOn (fun s => ‖X s - Z s‖) (Icc (0 : ℝ) T))
    (hurc : ∀ t ∈ Ico (0 : ℝ) T,
      ContinuousWithinAt (fun s => ‖X s - Z s‖) (Ioi t) t)
    (hHorizon : ∀ l, N * (B l * T) ≤ H)
    (hXeq : ∀ t ∈ Icc (0 : ℝ) T,
      X t = xZero + ∑ l,
        (Y l (scaledTcClock N beta X l t) / N) • v l)
    (hZeq : ∀ t ∈ Icc (0 : ℝ) T,
      Z t = xZero + (∫ s in (0 : ℝ)..t, tcDrift beta v (Z s)) +
        ∑ l, (W l (scaledTcClock N beta Z l t) / N) • v l)
    (hKMT : ∀ l u, u ∈ Icc (0 : ℝ) H → |Y l u - u - W l u| ≤ R)
    (hWcontinuous : ∀ l, Continuous (W l))
    (homegaMono : Monotone omega)
    (hWmod : ∀ l u w, u ∈ Icc (0 : ℝ) H → w ∈ Icc (0 : ℝ) H →
      |W l u - W l w| ≤ omega |u - w|)
    (homegaShape : ∀ h ∈ Icc (0 : ℝ) H,
      omega h ≤ C * Real.sqrt (h * (Real.log (H / h) + tail)) +
        C * (Real.log N + tail))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    ‖X t - Z t‖ ≤
      channelWeight (fun l => ‖v l‖) * ((1 + 2 * C) * q) / N *
        Real.exp (((1 + C / 2) *
          channelClockLip (fun l => ‖v l‖) K) * t) := by
  have hraw := fun t (ht : t ∈ Icc (0 : ℝ) T) =>
    timeChange_diffusion_nonlinear_inequality
    hN hT hH.le hR hB hK hbeta0 hbetaB hbetaLip hXU hZU
    hbetaX hbetaZ huint hHorizon hXeq hZeq hKMT hWcontinuous
    homegaMono hWmod ht
  have hmain := clock_modulus_gronwall_of_brownian_shape
    (T := T) (N := N) (H := H) (R := R) (C := C)
    (tail := tail) (q := q)
    (drift := channelClockLip (fun l => ‖v l‖) K)
    (a := fun l => ‖v l‖) (k := K) (omega := omega)
    (u := fun s => ‖X s - Z s‖)
    hT hN hH hR hC htail hq hqH hqN hRq
    (channelClockLip_nonneg (fun l => norm_nonneg _) hK)
    (fun l => norm_nonneg _) hK (fun _ _ => norm_nonneg _)
    huint hurc homegaShape hraw ht
  have hcoef :
      channelClockLip (fun l => ‖v l‖) K +
          (C / 2) * channelClockLip (fun l => ‖v l‖) K =
        (1 + C / 2) * channelClockLip (fun l => ‖v l‖) K := by
    ring
  simpa [hcoef] using hmain

/-- Fully explicit `Γ_T (R + log N + tail) / N` form.

Choose `D ≥ 1` with `B_l T ≤ D`; in applications use
`D = max 1 ((max_l B_l) T)`. -/
theorem timeChange_diffusion_comparison_brownian_explicit
    {U : Set (Fin d → ℝ)}
    {beta : ι → (Fin d → ℝ) → ℝ} {v : ι → Fin d → ℝ}
    {B K : ι → ℝ} {Y W : ι → ℝ → ℝ} {omega : ℝ → ℝ}
    {N T D R C tail : ℝ}
    {X Z : ℝ → Fin d → ℝ} {xZero : Fin d → ℝ}
    (hNtwo : 2 ≤ N) (hT : 0 ≤ T) (hD : 1 ≤ D)
    (hR : 0 ≤ R) (hC : 0 ≤ C) (htail : 0 ≤ tail)
    (hB : ∀ l, 0 ≤ B l) (hK : ∀ l, 0 ≤ K l)
    (hBT : ∀ l, B l * T ≤ D)
    (hbeta0 : ∀ l y, y ∈ U → 0 ≤ beta l y)
    (hbetaB : ∀ l y, y ∈ U → beta l y ≤ B l)
    (hbetaLip : ∀ l y z, y ∈ U → z ∈ U →
      |beta l y - beta l z| ≤ K l * ‖y - z‖)
    (hXU : ∀ s ∈ Icc (0 : ℝ) T, X s ∈ U)
    (hZU : ∀ s ∈ Icc (0 : ℝ) T, Z s ∈ U)
    (hbetaX : ∀ l t, t ∈ Icc (0 : ℝ) T →
      IntervalIntegrable (fun s => beta l (X s)) volume 0 t)
    (hbetaZ : ∀ l t, t ∈ Icc (0 : ℝ) T →
      IntervalIntegrable (fun s => beta l (Z s)) volume 0 t)
    (huint : IntegrableOn (fun s => ‖X s - Z s‖) (Icc (0 : ℝ) T))
    (hurc : ∀ t ∈ Ico (0 : ℝ) T,
      ContinuousWithinAt (fun s => ‖X s - Z s‖) (Ioi t) t)
    (hXeq : ∀ t ∈ Icc (0 : ℝ) T,
      X t = xZero + ∑ l,
        (Y l (scaledTcClock N beta X l t) / N) • v l)
    (hZeq : ∀ t ∈ Icc (0 : ℝ) T,
      Z t = xZero + (∫ s in (0 : ℝ)..t, tcDrift beta v (Z s)) +
        ∑ l, (W l (scaledTcClock N beta Z l t) / N) • v l)
    (hKMT : ∀ l u, u ∈ Icc (0 : ℝ) (N * D) →
      |Y l u - u - W l u| ≤ R)
    (hWcontinuous : ∀ l, Continuous (W l))
    (homegaMono : Monotone omega)
    (hWmod : ∀ l u w, u ∈ Icc (0 : ℝ) (N * D) →
      w ∈ Icc (0 : ℝ) (N * D) →
      |W l u - W l w| ≤ omega |u - w|)
    (homegaShape : ∀ h ∈ Icc (0 : ℝ) (N * D),
      omega h ≤ C * Real.sqrt (h * (Real.log ((N * D) / h) + tail)) +
        C * (Real.log N + tail))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    ‖X t - Z t‖ ≤
      brownianComparisonGamma
          (channelWeight (fun l => ‖v l‖))
          (channelClockLip (fun l => ‖v l‖) K) C T D *
        (R + Real.log N + tail) / N := by
  let S : ℝ := channelWeight (fun l => ‖v l‖)
  let Ksum : ℝ := channelClockLip (fun l => ‖v l‖) K
  let p : ℝ := R + Real.log N + tail
  let fac : ℝ := 1 + (1 + Real.log D) / Real.log 2
  let q : ℝ := p + 1 + Real.log D
  have hN : 0 < N := lt_of_lt_of_le (by norm_num) hNtwo
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hH : 0 < N * D := mul_pos hN hDpos
  have hlogTwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlogN : Real.log (2 : ℝ) ≤ Real.log N :=
    Real.log_le_log (by norm_num) hNtwo
  have hlogD : 0 ≤ Real.log D := Real.log_nonneg hD
  have hp0 : 0 ≤ p := by
    dsimp [p]
    linarith
  have hq : 1 ≤ q := by
    dsimp [q, p]
    linarith
  have hqH : Real.log (N * D) + tail ≤ q := by
    rw [Real.log_mul hN.ne' hDpos.ne']
    dsimp [q, p]
    linarith
  have hqN : Real.log N + tail ≤ q := by
    dsimp [q, p]
    linarith
  have hRq : R ≤ q := by
    dsimp [q, p]
    linarith
  have hHorizon : ∀ l, N * (B l * T) ≤ N * D := fun l =>
    mul_le_mul_of_nonneg_left (hBT l) hN.le
  have hmain := timeChange_diffusion_comparison_brownian
    (N := N) (T := T) (H := N * D) (R := R) (C := C)
    (tail := tail) (q := q)
    hN hT hH hR hC htail hq hqH hqN hRq
    hB hK hbeta0 hbetaB hbetaLip hXU hZU hbetaX hbetaZ
    huint hurc hHorizon hXeq hZeq hKMT hWcontinuous
    homegaMono hWmod homegaShape ht
  have hqle : q ≤ fac * p := by
    simpa [q, p, fac, add_assoc] using
      log_budget_le_factor hNtwo hD hR htail
  have hS : 0 ≤ S := by
    dsimp [S]
    exact channelWeight_nonneg fun l => norm_nonneg _
  have hKsum : 0 ≤ Ksum := by
    dsimp [Ksum]
    exact channelClockLip_nonneg (fun l => norm_nonneg _) hK
  have hfac : 0 ≤ fac := by
    dsimp [fac]
    positivity
  have hpref : 0 ≤ S * (1 + 2 * C) :=
    mul_nonneg hS (by nlinarith)
  have hbase :
      S * ((1 + 2 * C) * q) / N ≤
        S * ((1 + 2 * C) * (fac * p)) / N := by
    apply div_le_div_of_nonneg_right _ hN.le
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hqle (by nlinarith)) hS
  have hrate : 0 ≤ (1 + C / 2) * Ksum :=
    mul_nonneg (by nlinarith) hKsum
  have hexp :
      Real.exp ((1 + C / 2) * Ksum * t) ≤
        Real.exp ((1 + C / 2) * Ksum * T) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left ht.2 hrate
  have hbig : 0 ≤ S * ((1 + 2 * C) * (fac * p)) / N := by
    exact div_nonneg
      (mul_nonneg hS (mul_nonneg (by nlinarith)
        (mul_nonneg hfac hp0))) hN.le
  calc
    ‖X t - Z t‖ ≤
        S * ((1 + 2 * C) * q) / N *
          Real.exp ((1 + C / 2) * Ksum * t) := by
            simpa [S, Ksum] using hmain
    _ ≤ S * ((1 + 2 * C) * (fac * p)) / N *
          Real.exp ((1 + C / 2) * Ksum * t) :=
        mul_le_mul_of_nonneg_right hbase (Real.exp_pos _).le
    _ ≤ S * ((1 + 2 * C) * (fac * p)) / N *
          Real.exp ((1 + C / 2) * Ksum * T) :=
        mul_le_mul_of_nonneg_left hexp hbig
    _ = brownianComparisonGamma S Ksum C T D * p / N := by
        unfold brownianComparisonGamma
        ring
    _ = brownianComparisonGamma
          (channelWeight (fun l => ‖v l‖))
          (channelClockLip (fun l => ‖v l‖) K) C T D *
        (R + Real.log N + tail) / N := by
      rfl

/-!
THEOREM LIST
* `scaledTcClock`, `realTimeChangeRemainder`
* `kmtDriverRemainder`, `brownianClockShiftRemainder`
* `norm_tcDrift_sub_le_on`
* `scaledTcClock_mem_horizon`, `abs_scaledTcClock_sub_le`
* `real_timeChange_eq_drift`, `timeChange_diffusion_sub`
* `norm_kmtDriverRemainder_le`, `norm_brownianClockShiftRemainder_le`
* `timeChange_diffusion_nonlinear_inequality`
* `timeChange_diffusion_comparison_of_affine`
* `timeChange_diffusion_comparison_brownian`
* `timeChange_diffusion_comparison_brownian_explicit`

CLOSES
* Exact deterministic subtraction of the two random-time-change equations.
* General nondecreasing-modulus inequality (1).
* Affine-modulus comparison (3).
* Brownian entropy-modulus comparison (6).
* Explicit `Γ_T (R + log N + tail) / N` comparison (7)-(8).

UNFINISHED OUTSIDE THIS ITEM
* Existence or uniqueness of the Brownian time-change solution `Z`.
* Construction of the KMT coupling and proof of the probabilistic Brownian modulus event.
* Tail bookkeeping and the stopped-path application to EK 11.3.1.
END
-/

end

end Ripple.Kurtz.StrongApprox
