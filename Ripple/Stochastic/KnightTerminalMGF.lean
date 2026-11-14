import Ripple.Stochastic.ExponentialMartingaleLimit
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Terminal exponential moments at a deterministic bracket

Only a sequence of deterministic physical times is used. Normalization of the
stochastic exponential at each such time, including the doubled parameter,
provides a uniform square bound. Uniform integrability then gives the exact
terminal moment generating function. There is no optional sampling at a
collection of different random clocks in this argument.

The normalization premises must be supplied for the actual stopped finite sum
of integrals. This file does not construct those stopped integrals.
-/

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

namespace Ripple.Stochastic.KnightTerminalMGF

open ExponentialMartingaleLimit

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Convergence of expectations from a uniform square bound. -/
theorem integral_limit_of_sq_bound
    {Z : ℕ → Ω → ℝ} {L : Ω → ℝ} {C : ℝ}
    (hZ : ∀ n, Integrable (Z n) P)
    (hsq : ∀ n, Integrable (fun ω => (Z n ω) ^ 2) P)
    (hbound : ∀ n, (∫ ω, (Z n ω) ^ 2 ∂P) ≤ C)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n => Z n ω) atTop (𝓝 (L ω))) :
    Integrable L P ∧
      Tendsto (fun n => ∫ ω, Z n ω ∂P) atTop (𝓝 (∫ ω, L ω ∂P)) := by
  have hui : UniformIntegrable Z 1 P :=
    uniformIntegrable_of_sq_integral_le (fun n => (hZ n).aestronglyMeasurable)
      hsq hbound
  have hiL : Integrable L P := hui.integrable_of_ae_tendsto hlim
  have hLp : Tendsto (fun n => eLpNorm (Z n - L) 1 P) atTop (𝓝 0) :=
    tendsto_Lp_finite_of_tendsto_ae (by norm_num) (by norm_num)
      (fun n => (hZ n).aestronglyMeasurable)
      (memLp_one_iff_integrable.mpr hiL) hui.2.1 hlim
  exact ⟨hiL, tendsto_integral_of_L1' L hiL.aestronglyMeasurable
    (Eventually.of_forall hZ) hLp⟩

/-- Exact terminal MGF from normalized exponentials and a bounded bracket.
The limit of the bracket is the deterministic number `q`; its intermediate
values may be random and need not be independent of the martingale. -/
theorem terminal_mgf_of_normalized_exponentials
    (Y Q : ℕ → Ω → ℝ) (L : Ω → ℝ) (q lam : ℝ)
    (hY : ∀ n, AEStronglyMeasurable (Y n) P)
    (hQ : ∀ n, AEStronglyMeasurable (Q n) P)
    (hbound : ∀ n, ∀ᵐ ω ∂P, Q n ω ≤ q)
    (hint : ∀ a n, Integrable
      (fun ω => Real.exp (a * Y n ω - a ^ 2 * Q n ω / 2)) P)
    (hmean : ∀ a n, (∫ ω, Real.exp (a * Y n ω - a ^ 2 * Q n ω / 2) ∂P) = 1)
    (hYlim : ∀ᵐ ω ∂P, Tendsto (fun n => Y n ω) atTop (𝓝 (L ω)))
    (hQlim : ∀ᵐ ω ∂P, Tendsto (fun n => Q n ω) atTop (𝓝 q)) :
    Integrable (fun ω => Real.exp (lam * L ω)) P ∧
      (∫ ω, Real.exp (lam * L ω) ∂P) = Real.exp (lam ^ 2 * q / 2) := by
  let Z : ℕ → Ω → ℝ := fun n ω =>
    Real.exp (lam * Y n ω - lam ^ 2 * Q n ω / 2)
  let E : Ω → ℝ := fun ω => Real.exp (lam * L ω - lam ^ 2 * q / 2)
  have hsquare : ∀ n, Integrable (fun ω => (Z n ω) ^ 2) P ∧
      (∫ ω, (Z n ω) ^ 2 ∂P) ≤ Real.exp (lam ^ 2 * q) := by
    intro n
    exact exponential_sq_bound (Y n) (Q n) lam q (hY n) (hQ n)
      (hbound n) (hint (2 * lam) n) (hmean (2 * lam) n)
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun n => Z n ω) atTop (𝓝 (E ω)) := by
    filter_upwards [hYlim, hQlim] with ω hy hq
    exact Real.continuous_exp.continuousAt.tendsto.comp
      ((hy.const_mul lam).sub ((hq.const_mul (lam ^ 2)).div_const 2))
  obtain ⟨hiE, htE⟩ := integral_limit_of_sq_bound
    (fun n => hint lam n) (fun n => (hsquare n).1) (fun n => (hsquare n).2) hlim
  have hEmean : (∫ ω, E ω ∂P) = 1 := by
    apply tendsto_nhds_unique htE
    simpa only [Z, hmean] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
  have hfactor : (fun ω => Real.exp (lam * L ω)) =
      (fun ω => Real.exp (lam ^ 2 * q / 2) * E ω) := by
    funext ω
    dsimp [E]
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hfactor]
  exact ⟨hiE.const_mul _, by rw [integral_const_mul, hEmean, mul_one]⟩

end Ripple.Stochastic.KnightTerminalMGF
