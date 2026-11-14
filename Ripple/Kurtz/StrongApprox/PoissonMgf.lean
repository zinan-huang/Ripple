/-
  Ripple.Kurtz.StrongApprox.PoissonMgf — moment generating function of a centered Poisson count

  For an `ℕ`-valued `N` with point masses `P{N = k} = e^{−λ} λ^k / k!` (as the coupled counts
  `poisCoupling h ∘ Z` have, `measure_poisCoupling_eq`): `e^{θ(N − λ)}` is integrable and
  `mgf (N − λ) P θ = exp (λ (e^θ − 1 − θ))`; the same for `−(N − λ)` with `θ ↦ −θ`.
-/

import Mathlib
import Ripple.Kurtz.StrongApprox.PoissonCouplingMean

namespace Ripple.Kurtz.StrongApprox

open MeasureTheory ProbabilityTheory Set

/-- `Σ_k e^{−λ} λ^k e^{θ k} / k! = exp (λ (e^θ − 1))`. -/
theorem hasSum_poisTerm_mul_exp {l : ℝ} (hl : 0 ≤ l) (θ : ℝ) :
    HasSum (fun k : ℕ => poisTerm k l * Real.exp (θ * k)) (Real.exp (l * (Real.exp θ - 1))) := by
  have h := (hasSum_poisTerm (h := l * Real.exp θ) (by positivity)).mul_left
    (Real.exp (-l) * Real.exp (l * Real.exp θ))
  rw [mul_one] at h
  have e : (fun k : ℕ => poisTerm k l * Real.exp (θ * k)) =
      fun k => Real.exp (-l) * Real.exp (l * Real.exp θ) * poisTerm k (l * Real.exp θ) := by
    funext k
    unfold poisTerm
    rw [mul_pow, ← Real.exp_nat_mul, Real.exp_neg (l * Real.exp θ), mul_comm (k : ℝ) θ]
    field_simp
  rw [e]
  convert h using 1
  rw [← Real.exp_add]
  congr 1; ring

theorem summable_poisTerm_mul_exp {l : ℝ} (hl : 0 ≤ l) (θ : ℝ) :
    Summable (fun k : ℕ => poisTerm k l * Real.exp (θ * k)) :=
  (hasSum_poisTerm_mul_exp hl θ).summable

/-- A measure on `ℕ` with the Poisson point masses: `e^{θ k}` is integrable. -/
theorem integrable_exp_mul_of_poisson_masses {μ : Measure ℕ} {l : ℝ} (hl : 0 ≤ l)
    (hμ : ∀ k, μ {k} = ENNReal.ofReal (poisTerm k l)) (θ : ℝ) :
    Integrable (fun k : ℕ => Real.exp (θ * k)) μ := by
  refine ⟨measurable_from_nat.aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral, lintegral_countable']
  have heq : ∀ k : ℕ, ‖Real.exp (θ * k)‖ₑ * μ {k} = ENNReal.ofReal (poisTerm k l * Real.exp (θ * k)) := by
    intro k
    rw [hμ k, ← ofReal_norm, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      ← ENNReal.ofReal_mul (Real.exp_pos _).le, mul_comm]
  simp only [heq]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => mul_nonneg (poisTerm_nonneg k hl) (Real.exp_pos _).le)
    (summable_poisTerm_mul_exp hl θ)]
  exact ENNReal.ofReal_lt_top

/-- The exponential moment of a Poisson count: `E e^{θ N} = exp (λ (e^θ − 1))`. -/
theorem integral_exp_mul_of_poisson_masses {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {N : Ω → ℕ} (hN : Measurable N) {l : ℝ} (hl : 0 ≤ l)
    (hlaw : ∀ k, P {ω | N ω = k} = ENNReal.ofReal (poisTerm k l)) (θ : ℝ) :
    Integrable (fun ω => Real.exp (θ * N ω)) P ∧
      ∫ ω, Real.exp (θ * N ω) ∂P = Real.exp (l * (Real.exp θ - 1)) := by
  have hcoe : Measurable fun k : ℕ => Real.exp (θ * k) := measurable_from_nat
  have hμ : ∀ k, (P.map N) {k} = ENNReal.ofReal (poisTerm k l) := by
    intro k
    rw [Measure.map_apply hN (measurableSet_singleton k)]
    exact hlaw k
  have hint := integrable_exp_mul_of_poisson_masses hl hμ θ
  constructor
  · rw [integrable_map_measure hcoe.aestronglyMeasurable hN.aemeasurable] at hint
    exact hint
  · calc ∫ ω, Real.exp (θ * N ω) ∂P
        = ∫ k : ℕ, Real.exp (θ * k) ∂(P.map N) := by
          rw [integral_map hN.aemeasurable hcoe.aestronglyMeasurable]
      _ = ∑' k : ℕ, (P.map N).real {k} • Real.exp (θ * k) := integral_countable hint
      _ = ∑' k : ℕ, poisTerm k l * Real.exp (θ * k) := by
          congr 1; funext k
          rw [measureReal_def, hμ k, ENNReal.toReal_ofReal (poisTerm_nonneg k hl), smul_eq_mul]
      _ = Real.exp (l * (Real.exp θ - 1)) := (hasSum_poisTerm_mul_exp hl θ).tsum_eq

/-- **mgf of a centered Poisson count**: `mgf (N − λ) P θ = exp (λ (e^θ − 1 − θ))`, with the
integrability of `e^{θ (N − λ)}`. -/
theorem mgf_poisson_centered {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {N : Ω → ℕ}
    (hN : Measurable N) {l : ℝ} (hl : 0 ≤ l)
    (hlaw : ∀ k, P {ω | N ω = k} = ENNReal.ofReal (poisTerm k l)) (θ : ℝ) :
    Integrable (fun ω => Real.exp (θ * ((N ω : ℝ) - l))) P ∧
      mgf (fun ω => (N ω : ℝ) - l) P θ = Real.exp (l * (Real.exp θ - 1 - θ)) := by
  obtain ⟨hint, hval⟩ := integral_exp_mul_of_poisson_masses P hN hl hlaw θ
  have e : (fun ω => Real.exp (θ * ((N ω : ℝ) - l))) =
      fun ω => Real.exp (-(θ * l)) * Real.exp (θ * N ω) := by
    funext ω; rw [← Real.exp_add]; congr 1; ring
  constructor
  · rw [e]; exact hint.const_mul _
  · unfold mgf
    rw [e, integral_const_mul, hval, ← Real.exp_add]
    congr 1; ring

/-- The same for the reflected count `−(N − λ)`. -/
theorem mgf_poisson_centered_neg {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {N : Ω → ℕ}
    (hN : Measurable N) {l : ℝ} (hl : 0 ≤ l)
    (hlaw : ∀ k, P {ω | N ω = k} = ENNReal.ofReal (poisTerm k l)) (θ : ℝ) :
    Integrable (fun ω => Real.exp (θ * -((N ω : ℝ) - l))) P ∧
      mgf (fun ω => -((N ω : ℝ) - l)) P θ = Real.exp (l * (Real.exp (-θ) - 1 + θ)) := by
  obtain ⟨hint, hval⟩ := mgf_poisson_centered P hN hl hlaw (-θ)
  have e : (fun ω => Real.exp (θ * -((N ω : ℝ) - l))) =
      fun ω => Real.exp (-θ * ((N ω : ℝ) - l)) := by
    funext ω; congr 1; ring
  constructor
  · rw [e]; exact hint
  · unfold mgf at hval ⊢
    rw [e, hval]
    congr 1; ring

end Ripple.Kurtz.StrongApprox
