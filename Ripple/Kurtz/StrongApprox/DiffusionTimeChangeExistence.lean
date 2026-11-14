-- Ripple/Kurtz/StrongApprox/DiffusionTimeChangeExistence.lean
import Ripple.Analysis.PeanoBoundedExistence
import Ripple.Kurtz.StrongApprox.DiffusionClockComparison

/-!
# Pathwise existence of the Kurtz diffusion time-change equation

For a fixed continuous driver family `W`, solve the finite-dimensional clock
ODE by bounded Peano existence and reconstruct the state from the clocks.
The result is pathwise; no measurable selection in a sample parameter is
asserted or needed by the comparison theorem.
-/

noncomputable section

open MeasureTheory Set Finset
open scoped BigOperators Interval

namespace Ripple.Kurtz.StrongApprox

open Ripple.Analysis.PeanoBoundedExistence

variable {d : ℕ} {ι : Type*} [Fintype ι]

/-- State reconstructed from a vector of internal clocks. -/
noncomputable def diffusionClockState
    (W : ι → ℝ → ℝ) (N : ℝ) (xZero : Fin d → ℝ)
    (v : ι → Fin d → ℝ) (tau : ι → ℝ) : Fin d → ℝ :=
  xZero + ∑ l, (tau l + W l (N * tau l) / N) • v l

/-- Clock vector field `tau ↦ (beta l (Phi tau))_l`. -/
noncomputable def diffusionClockField
    (beta : ι → (Fin d → ℝ) → ℝ) (W : ι → ℝ → ℝ)
    (N : ℝ) (xZero : Fin d → ℝ) (v : ι → Fin d → ℝ)
    (tau : ι → ℝ) : ι → ℝ :=
  fun l => beta l (diffusionClockState W N xZero v tau)

@[fun_prop]
theorem continuous_diffusionClockState
    {W : ι → ℝ → ℝ} {N : ℝ} {xZero : Fin d → ℝ}
    {v : ι → Fin d → ℝ} (hW : ∀ l, Continuous (W l)) :
    Continuous (diffusionClockState W N xZero v) := by
  unfold diffusionClockState
  fun_prop

@[fun_prop]
theorem continuous_diffusionClockField
    {beta : ι → (Fin d → ℝ) → ℝ} {W : ι → ℝ → ℝ}
    {N : ℝ} {xZero : Fin d → ℝ} {v : ι → Fin d → ℝ}
    (hW : ∀ l, Continuous (W l))
    (hbeta : ∀ l, Continuous (beta l)) :
    Continuous (diffusionClockField beta W N xZero v) := by
  apply continuous_pi
  intro l
  exact (hbeta l).comp (continuous_diffusionClockState hW)

/-- Coordinatewise rate bounds give a uniform norm bound for the clock field. -/
theorem norm_diffusionClockField_le
    {beta : ι → (Fin d → ℝ) → ℝ} {W : ι → ℝ → ℝ}
    {N : ℝ} {xZero : Fin d → ℝ} {v : ι → Fin d → ℝ}
    {B : ι → ℝ}
    (hbeta0 : ∀ l y, 0 ≤ beta l y)
    (hbetaB : ∀ l y, beta l y ≤ B l)
    (tau : ι → ℝ) :
    ‖diffusionClockField beta W N xZero v tau‖ ≤ ‖B‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg B)]
  intro l
  show ‖beta l (diffusionClockState W N xZero v tau)‖ ≤ ‖B‖
  rw [Real.norm_eq_abs, abs_of_nonneg (hbeta0 l _)]
  calc
    beta l (diffusionClockState W N xZero v tau) ≤ B l :=
      hbetaB l _
    _ ≤ |B l| := le_abs_self _
    _ = ‖B l‖ := by rw [Real.norm_eq_abs]
    _ ≤ ‖B‖ := norm_le_pi_norm B l

/-- Pathwise producer for the exact diffusion equation consumed by
`timeChange_diffusion_comparison_of_entropy`. -/
theorem exists_diffusionTimeChange_solution
    (W : ι → ℝ → ℝ) (hW : ∀ l, Continuous (W l))
    (beta : ι → (Fin d → ℝ) → ℝ)
    (hbeta : ∀ l, Continuous (beta l))
    (B : ι → ℝ)
    (hbeta0 : ∀ l y, 0 ≤ beta l y)
    (hbetaB : ∀ l y, beta l y ≤ B l)
    (v : ι → Fin d → ℝ) {N T : ℝ}
    (hN : 0 < N) (hT : 0 ≤ T) (xZero : Fin d → ℝ) :
    ∃ Z : ℝ → Fin d → ℝ,
      Continuous Z ∧
      (∀ l t, t ∈ Icc (0 : ℝ) T →
        IntervalIntegrable (fun s => beta l (Z s)) volume 0 t) ∧
      (∀ t ∈ Icc (0 : ℝ) T,
        Z t = xZero +
          (∫ s in (0 : ℝ)..t, tcDrift beta v (Z s)) +
          ∑ l, (W l (scaledTcClock N beta Z l t) / N) • v l) := by
  classical
  let G : (ι → ℝ) → (ι → ℝ) :=
    diffusionClockField beta W N xZero v
  have hG : Continuous G := by
    dsimp [G]
    exact continuous_diffusionClockField hW hbeta
  have hGbound : ∀ tau, ‖G tau‖ ≤ ‖B‖ := by
    intro tau
    simpa [G] using
      (norm_diffusionClockField_le
        (beta := beta) (W := W) (N := N) (xZero := xZero)
        (v := v) hbeta0 hbetaB tau)
  obtain ⟨tau, htau, htauEq, _htauDeriv⟩ :=
    exists_peanoBounded_solution G hG ‖B‖ hGbound
      (0 : ι → ℝ) hT
  let Z : ℝ → Fin d → ℝ := fun t =>
    diffusionClockState W N xZero v (tau t)
  have hZ : Continuous Z := by
    dsimp [Z]
    exact (continuous_diffusionClockState
      (W := W) (N := N) (xZero := xZero) (v := v) hW).comp htau
  have hbetaInt : ∀ l t, t ∈ Icc (0 : ℝ) T →
      IntervalIntegrable (fun s => beta l (Z s)) volume 0 t := by
    intro l t _ht
    exact intervalIntegrable_rate hbeta0 hbetaB
      (fun k => (hbeta k).measurable) hZ.measurable l 0 t
  have hGtau : Continuous (fun s => G (tau s)) := hG.comp htau
  have htauClock : ∀ l t, t ∈ Icc (0 : ℝ) T →
      tau t l = clock beta Z l t := by
    intro l t ht
    have hcoord :
        (∫ s in (0 : ℝ)..t, G (tau s)) l =
          ∫ s in (0 : ℝ)..t, G (tau s) l := by
      symm
      exact (ContinuousLinearMap.proj l :
        (ι → ℝ) →L[ℝ] ℝ).intervalIntegral_comp_comm
          (hGtau.intervalIntegrable 0 t)
    have h := congrArg (fun q : ι → ℝ => q l) (htauEq t ht)
    simp only [Pi.add_apply, Pi.zero_apply, zero_add] at h
    rw [hcoord] at h
    simpa [G, diffusionClockField, Z, clock] using h
  let Y : ι → ℝ → ℝ := fun l u => u + W l u
  have hRaw : ∀ t, t ∈ Icc (0 : ℝ) T →
      Z t = xZero + ∑ l,
        (Y l (scaledTcClock N beta Z l t) / N) • v l := by
    intro t ht
    change xZero + ∑ l, (tau t l + W l (N * tau t l) / N) • v l =
      xZero + ∑ l, (Y l (scaledTcClock N beta Z l t) / N) • v l
    congr 1
    refine Finset.sum_congr rfl fun l _ => ?_
    unfold scaledTcClock
    rw [← htauClock l t ht]
    dsimp [Y]
    congr 1
    field_simp [hN.ne']
  refine ⟨Z, hZ, hbetaInt, ?_⟩
  intro t ht
  have hDrift := real_timeChange_eq_drift
    (beta := beta) (v := v) (Y := Y) (N := N)
    (X := Z) (xZero := xZero) (t := t)
    hN (fun l => hbetaInt l t ht) (hRaw t ht)
  have hrem :
      realTimeChangeRemainder beta v Y N Z t =
        ∑ l, (W l (scaledTcClock N beta Z l t) / N) • v l := by
    unfold realTimeChangeRemainder
    refine Finset.sum_congr rfl fun l _ => ?_
    dsimp [Y]
    congr 1
    ring
  rw [hrem] at hDrift
  exact hDrift

/-!
THEOREM LIST
* `continuous_diffusionClockState`
* `continuous_diffusionClockField`
* `norm_diffusionClockField_le`
* `exists_diffusionTimeChange_solution`

CLOSES
* Item 2: a pathwise continuous solution of the exact Kurtz diffusion
  equation, together with every interval-integrability side fact consumed by
  `timeChange_diffusion_comparison_of_entropy`.

UNFINISHED
* Measurability of a choice `omega ↦ Z omega` is intentionally absent; the
  comparison theorem is pathwise and does not require it.
* Brownian sample-path continuity remains supplied by the existing
  `DyadicBrownianOn` almost-sure continuity result.
END
-/

end Ripple.Kurtz.StrongApprox

end
