import Ripple.Stochastic.StrongSDEEstimates
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.MeasureTheory.Function.AEEqFun
import Mathlib.Probability.Process.Adapted
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Conditional strong-solution construction on a finite horizon

The carrier S must be the complete normed space of continuous
adapted processes modulo indistinguishability, with the L² path-sup norm. Its
construction is a separate obligation, not supplied by this generic theorem.
The drift and noise maps must be the integral maps on that carrier. The continuous
integral versions, the maximal estimate, the closed adapted subspace, coefficient
composition and realization are separate obligations.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Ripple.Stochastic.StrongSDE

variable {S : Type*} [NormedAddCommGroup S]

/-- Turn a squared-norm estimate into the actual contraction constant sqrt(q).
This uses the norm of the given carrier, so a discrete metric cannot be substituted. -/
theorem contracting_of_sq_estimate (Φ : S → S) {q : ℝ}
    (hq : 0 ≤ q) (hq_lt : q < 1)
    (hDifference : ∀ X Y, ‖Φ X - Φ Y‖ ^ 2 ≤ q * ‖X - Y‖ ^ 2) :
    ContractingWith ⟨Real.sqrt q, Real.sqrt_nonneg q⟩ Φ := by
  have hsqrt : Real.sqrt q < 1 := by
    nlinarith [Real.sq_sqrt hq, Real.sqrt_nonneg q]
  refine ⟨hsqrt, LipschitzWith.of_dist_le_mul ?_⟩
  intro X Y
  rw [dist_eq_norm, dist_eq_norm]
  change ‖Φ X - Φ Y‖ ≤ Real.sqrt q * ‖X - Y‖
  have hsq : (Real.sqrt q * ‖X - Y‖) ^ 2 = q * ‖X - Y‖ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hq]
  have hnonneg := mul_nonneg (Real.sqrt_nonneg q) (norm_nonneg (X - Y))
  nlinarith [hDifference X Y, norm_nonneg (Φ X - Φ Y)]

/-- Existence is supplied by Banach's theorem after the integral estimates, with
completeness of the carrier still an explicit premise. -/
theorem exists_unique_of_sq_estimate [CompleteSpace S]
    (Φ : S → S) {q : ℝ} (hq : 0 ≤ q) (hq_lt : q < 1)
    (hDifference : ∀ X Y, ‖Φ X - Φ Y‖ ^ 2 ≤ q * ‖X - Y‖ ^ 2) :
    ∃! X, Φ X = X := by
  let hc := contracting_of_sq_estimate Φ hq hq_lt hDifference
  refine ⟨ContractingWith.fixedPoint Φ hc, hc.fixedPoint_isFixedPt, ?_⟩
  intro Y hY
  exact hc.fixedPoint_unique hY

/-- Local existence and uniqueness from the two separate integral estimates.
The noise bound includes Doob's constant four; the final Lipschitz constant
is the square root of `2*h^2*LF^2 + 8*h*LSsq`. -/
theorem exists_unique_picard [CompleteSpace S]
    (initial : S) (drift noise : S → S) {h LF LSsq : ℝ}
    (hh : 0 ≤ h) (hLS : 0 ≤ LSsq)
    (hLocal : 2 * h ^ 2 * LF ^ 2 + 8 * h * LSsq < 1)
    (driftDifferenceBound : ∀ X Y,
      ‖drift X - drift Y‖ ^ 2 ≤ h ^ 2 * LF ^ 2 * ‖X - Y‖ ^ 2)
    (doobNoiseDifferenceBound : ∀ X Y,
      ‖noise X - noise Y‖ ^ 2 ≤ 4 * h * LSsq * ‖X - Y‖ ^ 2) :
    ∃! X, picardStep initial drift noise X = X := by
  apply exists_unique_of_sq_estimate (picardStep initial drift noise)
    (q := 2 * h ^ 2 * LF ^ 2 + 8 * h * LSsq) (by positivity) hLocal
  exact picardStep_difference_sq_le initial drift noise h LF LSsq
    driftDifferenceBound doobNoiseDifferenceBound

/-- The unscaled channel integral is evaluated against the same Brownian family
for every N. The caller must identify `ito` with continuous versions of the
filtered scalar Itô integral. The real/NNReal time conversion affects only drift. -/
def sdeRhs {ι Ω E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ito : ι → (ℝ≥0 → Ω → ℝ) → ℝ≥0 → Ω → ℝ)
    (ell : ι → E) (g : ι → E → ℝ) (F : E → E) (x₀ : E)
    (N : ℕ) (X : ℝ≥0 → Ω → E) (t : ℝ≥0) (ω : Ω) : E :=
  x₀ + (∑ i, ((Real.sqrt (N : ℝ))⁻¹ *
    ito i (fun s ω' => g i (X s ω')) t ω) • ell i) +
    ∫ s in (0 : ℝ)..(t : ℝ), F (X s.toNNReal ω)

/-- A fixed point yields a pathwise integral equation from a one-step realization
identity. `hStepRealization` is required for every input, not just for a solution;
it is produced by defining the two maps from the integrals and selecting coherent
continuous versions. `hAdapted` and `hContinuous` come from the process carrier.
The moment bound is part of that carrier, not derived by this transfer theorem. -/
theorem exists_realized_solution [CompleteSpace S]
    {ι Ω E : Type*} [Fintype ι] [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (P : Measure Ω) (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (T : ℝ≥0) (N : ℕ)
    (ito : ι → (ℝ≥0 → Ω → ℝ) → ℝ≥0 → Ω → ℝ)
    (ell : ι → E) (g : ι → E → ℝ) (F : E → E) (x₀ : E)
    (realize : S → ℝ≥0 → Ω → E) (Φ : S → S)
    (hAdapted : ∀ X, StronglyAdapted 𝓕 (realize X))
    (hContinuous : ∀ X, ∀ᵐ ω ∂P, Continuous (fun t => realize X t ω))
    (hSupMoment : ∀ X, Integrable
      (fun ω => ⨆ t : Set.Icc (0 : ℝ≥0) T, ‖realize X t.val ω‖ ^ 2) P)
    (hStepRealization : ∀ X, ∀ᵐ ω ∂P, ∀ t ≤ T,
      realize (Φ X) t ω = sdeRhs ito ell g F x₀ N (realize X) t ω)
    {q : ℝ} (hq : 0 ≤ q) (hq_lt : q < 1)
    (hDifference : ∀ X Y, ‖Φ X - Φ Y‖ ^ 2 ≤ q * ‖X - Y‖ ^ 2) :
    ∃ X : S, Φ X = X ∧ StronglyAdapted 𝓕 (realize X) ∧
      (∀ᵐ ω ∂P, Continuous (fun t => realize X t ω)) ∧
      Integrable (fun ω => ⨆ t : Set.Icc (0 : ℝ≥0) T,
        ‖realize X t.val ω‖ ^ 2) P ∧
      (∀ᵐ ω ∂P, ∀ t ≤ T,
        realize X t ω = sdeRhs ito ell g F x₀ N (realize X) t ω) := by
  obtain ⟨X, hX, _⟩ := exists_unique_of_sq_estimate Φ hq hq_lt hDifference
  refine ⟨X, hX, hAdapted X, hContinuous X, hSupMoment X, ?_⟩
  simpa only [hX] using hStepRealization X

/-- Choice of all positive integer scales on the SAME carrier. In an application
the carrier, measure, filtration, and integral operators are fixed before N.
There is no product of separately constructed solution laws in this statement. -/
theorem exists_simultaneous_fixedPoints [CompleteSpace S]
    (Φ : ℕ → S → S) {q : ℝ} (hq : 0 ≤ q) (hq_lt : q < 1)
    (hDifference : ∀ N, 1 ≤ N → ∀ X Y,
      ‖Φ N X - Φ N Y‖ ^ 2 ≤ q * ‖X - Y‖ ^ 2) :
    ∃ Z : ℕ → S, ∀ N, 1 ≤ N →
      Φ N (Z N) = Z N ∧ ∀ Y, Φ N Y = Y → Y = Z N := by
  classical
  have hex : ∀ N : {N : ℕ // 1 ≤ N}, ∃! X, Φ N.val X = X :=
    fun N => exists_unique_of_sq_estimate (Φ N.val) hq hq_lt
      (hDifference N.val N.property)
  let Z : ℕ → S := fun N => if h : 1 ≤ N then
    Classical.choose (hex ⟨N, h⟩) else 0
  refine ⟨Z, ?_⟩
  intro N hN
  simpa only [Z, dif_pos hN] using Classical.choose_spec (hex ⟨N, hN⟩)

/-- Countably many scales and horizons have one full-measure event. Each event
already quantifies over ALL times, so no uncountable intersection is taken. -/
theorem simultaneous_ae {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (Good : ℕ → ℕ → Ω → Prop)
    (hGood : ∀ N k, ∀ᵐ ω ∂P, Good N k ω) :
    ∀ᵐ ω ∂P, ∀ N k, Good N k ω := by
  exact ae_all_iff.mpr fun N => ae_all_iff.mpr (hGood N)

end Ripple.Stochastic.StrongSDE
