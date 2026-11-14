import Ripple.Stochastic.NonnegativeSupermartingaleMaximal

/-!
# Exponential maximal bounds: events, optimization, and the finite-grid theorem

The stochastic-exponential supermartingale is an explicit hypothesis here.
Construction of that supermartingale from an Itô integral is a separate obligation.
-/

open MeasureTheory Set
open scoped ENNReal NNReal

namespace Ripple.Stochastic.ExponentialMaximal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The exponential with the quadratic compensator normalized by one half. -/
noncomputable def stochasticExponential {ι : Type*}
    (M Q : ι → Ω → ℝ) (lam : ℝ) : ι → Ω → ℝ :=
  fun t ω => Real.exp (lam * M t ω - lam ^ 2 * Q t ω / 2)

/-- Compact-horizon crossing with a terminal energy restriction. -/
def crossingEvent (M Q : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (r q : ℝ) : Set Ω :=
  {ω | (∃ t ≤ T, r ≤ M t ω) ∧ Q T ω ≤ q}

/-- The continuous-time headline target; a specification, not an existence theorem. -/
def ExponentialMaximalBound (P : Measure Ω) (M Q : ℝ≥0 → Ω → ℝ) : Prop :=
  ∀ (T : ℝ≥0) (r q : ℝ), 0 ≤ r → 0 < q →
    P (crossingEvent M Q T r q) ≤ ENNReal.ofReal (Real.exp (-r ^ 2 / (2 * q)))

/-- The deterministic exponential comparison on the constrained crossing event. -/
theorem exp_threshold_le {m v r q lam : ℝ}
    (hlam : 0 ≤ lam) (hm : r ≤ m) (hv : v ≤ q) :
    Real.exp (lam * r - lam ^ 2 * q / 2) ≤ Real.exp (lam * m - lam ^ 2 * v / 2) := by
  apply Real.exp_le_exp.mpr
  have hm' := mul_le_mul_of_nonneg_left hm hlam
  have hv' := mul_le_mul_of_nonneg_left hv (sq_nonneg lam)
  linarith

/-- Completing the square identifies the optimal nonnegative parameter. -/
theorem optimized_exponent (r : ℝ) {q : ℝ} (hq : 0 < q) :
    -((r / q) * r - (r / q) ^ 2 * q / 2) = -r ^ 2 / (2 * q) := by
  field_simp [ne_of_gt hq]
  <;> ring

/-- Every other parameter has an exponent at least as large as the optimum. -/
theorem optimal_exponent_le (r lam : ℝ) {q : ℝ} (hq : 0 < q) :
    -r ^ 2 / (2 * q) ≤ -lam * r + lam ^ 2 * q / 2 := by
  apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hq)).mpr
  nlinarith [sq_nonneg (lam * q - r)]

/-- The continuous event is contained in the exponential crossing event.
The monotonicity premise may later be supplied outside one common null set. -/
theorem crossingEvent_subset (M Q : ℝ≥0 → Ω → ℝ)
    (hQ : ∀ ω, Monotone (fun t => Q t ω))
    (T : ℝ≥0) (r q : ℝ) {lam : ℝ} (hlam : 0 ≤ lam) :
    crossingEvent M Q T r q ⊆
      {ω | ∃ t ≤ T, Real.exp (lam * r - lam ^ 2 * q / 2) ≤
        stochasticExponential M Q lam t ω} := by
  rintro ω ⟨⟨t, ht, hm⟩, hq⟩
  exact ⟨t, ht, exp_threshold_le hlam hm ((hQ ω ht).trans hq)⟩

/-- Sharp finite-grid inequality conditional on the exponential supermartingale.
No assumption of independent channel integrals is used. -/
theorem finite_exponential_maximal
    {P : Measure Ω} [IsProbabilityMeasure P]
    {F : Filtration ℕ ‹MeasurableSpace Ω›} (M Q : ℕ → Ω → ℝ)
    (hMzero : ∀ ω, M 0 ω = 0) (hQzero : ∀ ω, Q 0 ω = 0)
    (hQ : ∀ ω, Monotone (fun n => Q n ω))
    (n : ℕ) {r q : ℝ} (hr : 0 ≤ r) (hq : 0 < q)
    (hZ : Supermartingale (stochasticExponential M Q (r / q)) F P) :
    P {ω | (∃ k ≤ n, r ≤ M k ω) ∧ Q n ω ≤ q} ≤
      ENNReal.ofReal (Real.exp (-r ^ 2 / (2 * q))) := by
  let lam : ℝ := r / q
  let a : ℝ := Real.exp (lam * r - lam ^ 2 * q / 2)
  have hlam : 0 ≤ lam := div_nonneg hr hq.le
  have ha : 0 < a := Real.exp_pos _
  have hsub : {ω | (∃ k ≤ n, r ≤ M k ω) ∧ Q n ω ≤ q} ⊆
      {ω | ∃ k ≤ n, a ≤ stochasticExponential M Q lam k ω} := by
    rintro ω ⟨⟨k, hk, hm⟩, hqω⟩
    exact ⟨k, hk, exp_threshold_le hlam hm ((hQ ω hk).trans hqω)⟩
  have hmax := SupermartingaleMaximal.finite_maximal_measure_le hZ
    (fun k ω => (Real.exp_pos _).le) ha n
  have hinit : (∫ ω, stochasticExponential M Q lam 0 ω ∂P) = 1 := by
    simp [stochasticExponential, hMzero, hQzero]
  have hopt : 1 / a = Real.exp (-r ^ 2 / (2 * q)) := by
    rw [one_div, ← Real.exp_neg]
    congr 1
    exact optimized_exponent r hq
  rw [hinit, hopt] at hmax
  exact (measure_mono hsub).trans hmax

end Ripple.Stochastic.ExponentialMaximal
