-- Ripple/Kurtz/StrongApprox/PerturbedClockBound.lean
import Ripple.Kurtz.StrongApprox.DiffusionClockComparison

/-!
# Scaled clocks for two different rate families

In Kurtz 1978 the chain uses the rates `f_l^N` and the diffusion (1.6) the
rates `f_l`, related by (3.2), `|f_l - f_l^N| ≤ Γ ε_l / N` (p. 230).  The
existing comparison in `DiffusionClockComparison` takes one rate for both.
This file bounds the scaled clock of the chain, `N ∫ f_l^N(X)`, against the
scaled clock of the diffusion, `N ∫ f_l(Z)`: a uniform rate perturbation
`δ_l / N` contributes at most `δ_l t` along the same path
(`abs_scaledTcClock_rate_perturbation_le`), and the state-dependence is the
Lipschitz estimate (3.19) already available (`abs_scaledTcClock_sub_le`),
giving `δ_l t + N K_l ∫_0^t ‖X - Z‖`.
-/

namespace Ripple.Kurtz.StrongApprox

open MeasureTheory Set
open scoped Interval

variable {d : ℕ} {ι : Type*} [Fintype ι]

/-- A uniform rate perturbation of size delta/N contributes at most delta*t
    to the scaled clock along the same path. -/
theorem abs_scaledTcClock_rate_perturbation_le
    {U : Set (Fin d → ℝ)}
    {betaN beta : ι → (Fin d → ℝ) → ℝ} {delta : ι → ℝ}
    {X : ℝ → Fin d → ℝ} {N T : ℝ}
    (hN : 0 < N)
    (hpert : ∀ l x, x ∈ U → |betaN l x - beta l x| ≤ delta l / N)
    (hXU : ∀ s ∈ Icc (0 : ℝ) T, X s ∈ U)
    {l : ι} {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T)
    (hbetaNX : IntervalIntegrable (fun s => betaN l (X s)) volume 0 t)
    (hbetaX : IntervalIntegrable (fun s => beta l (X s)) volume 0 t) :
    |scaledTcClock N betaN X l t - scaledTcClock N beta X l t| ≤
      delta l * t := by
  have hnorm : |clock betaN X l t - clock beta X l t| ≤
      ∫ s in (0 : ℝ)..t, delta l / N := by
    unfold clock
    rw [← intervalIntegral.integral_sub hbetaNX hbetaX]
    rw [← Real.norm_eq_abs]
    refine (intervalIntegral.norm_integral_le_integral_norm ht.1).trans ?_
    exact intervalIntegral.integral_mono_on ht.1 (hbetaNX.sub hbetaX).norm
      intervalIntegrable_const fun s hs => by
        rw [Real.norm_eq_abs]
        exact hpert l (X s) (hXU s ⟨hs.1, hs.2.trans ht.2⟩)
  rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hnorm
  unfold scaledTcClock
  rw [← mul_sub, abs_mul, abs_of_pos hN]
  calc
    N * |clock betaN X l t - clock beta X l t| ≤
        N * (t * (delta l / N)) := mul_le_mul_of_nonneg_left hnorm hN.le
    _ = delta l * t := by field_simp [ne_of_gt hN] <;> ring

/-- Splitting rate perturbation and state dependence yields the perturbed
    scaled-clock comparison. -/
theorem abs_scaledTcClock_perturbed_sub_le
    {U : Set (Fin d → ℝ)}
    {betaN beta : ι → (Fin d → ℝ) → ℝ} {delta K : ι → ℝ}
    {X Z : ℝ → Fin d → ℝ} {N T : ℝ}
    (hN : 0 < N) (hK : ∀ l, 0 ≤ K l)
    (hpert : ∀ l x, x ∈ U → |betaN l x - beta l x| ≤ delta l / N)
    (hbetaLip : ∀ l y z, y ∈ U → z ∈ U →
      |beta l y - beta l z| ≤ K l * ‖y - z‖)
    (hXU : ∀ s ∈ Icc (0 : ℝ) T, X s ∈ U)
    (hZU : ∀ s ∈ Icc (0 : ℝ) T, Z s ∈ U)
    (huint : IntegrableOn (fun s => ‖X s - Z s‖) (Icc (0 : ℝ) T))
    {l : ι} {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T)
    (hbetaNX : IntervalIntegrable (fun s => betaN l (X s)) volume 0 t)
    (hbetaX : IntervalIntegrable (fun s => beta l (X s)) volume 0 t)
    (hbetaZ : IntervalIntegrable (fun s => beta l (Z s)) volume 0 t) :
    |scaledTcClock N betaN X l t - scaledTcClock N beta Z l t| ≤
      delta l * t + N * K l * (∫ s in (0 : ℝ)..t, ‖X s - Z s‖) := by
  exact (abs_sub_le (scaledTcClock N betaN X l t)
    (scaledTcClock N beta X l t) (scaledTcClock N beta Z l t)).trans
    (add_le_add
      (abs_scaledTcClock_rate_perturbation_le hN hpert hXU ht hbetaNX hbetaX)
      (abs_scaledTcClock_sub_le hN hK hbetaLip hXU hZU huint ht hbetaX hbetaZ))


end Ripple.Kurtz.StrongApprox
