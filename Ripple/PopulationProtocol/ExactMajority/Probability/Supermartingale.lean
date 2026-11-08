/-
Supermartingale convergence-time bound (Theorem 4.2 of Doty et al.).

Generic tool: if X₀, X₁, ... is a nonneg supermartingale with X₀ = x₀ and
multiplicative drift E[X_{t+1} | X_t] ≤ (1−γ) X_t, then the hitting time to
some threshold has exponential tail. Used throughout the paper to bound phase
durations.

This file re-exports `PopProtoCommon`'s `lintegral_geometric_decay`, which
proves the kernel-level multiplicative-decay bound and is independent of any
specific population protocol. We expose it under the `ExactMajority`
namespace for convenience here, and prove the kernel-version Markov tail
bound below.

Reference: Doty et al., Theorem 4.2; PopProtoCommon/Convergence/GeometricDrift.lean
(originally extracted from PP-Proof).
-/

import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Kernel.Defs
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Ripple.PopulationProtocol.PopProtoCommon.Convergence.GeometricDrift

open scoped ENNReal
open MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority

/-- Re-export of `PopProtoCommon`'s kernel multiplicative-decay theorem.

If `K : Kernel α α` is a Markov kernel, `Φ : α → ℝ≥0∞` is measurable, and the
one-step expectation satisfies `∫⁻ Φ dK(x) ≤ r·Φ(x)` for all `x`, then the
`t`-step expectation satisfies `∫⁻ Φ d(K^t)(x) ≤ r^t · Φ(x)`.

This is the analytic engine behind any "multiplicative drift" / geometric
supermartingale bound, and is reusable across population-protocol proofs. -/
abbrev lintegral_geometric_decay := @Ripple.PopulationProtocol.PopProtoCommon.lintegral_geometric_decay

/-- Re-export of `PopProtoCommon`'s `measure_potential_ge_one` (Markov
inequality specialization for the geometric-decay regime). -/
abbrev measure_potential_ge_one := @Ripple.PopulationProtocol.PopProtoCommon.measure_potential_ge_one

/-- Convert an `ℝ≥0∞` probability bound into the corresponding real-valued
`Measure.real` bound. -/
theorem measure_real_le_of_le_ofReal {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (S : Set Ω) {B : ℝ} (hB : 0 ≤ B)
    (h : μ S ≤ ENNReal.ofReal B) :
    μ.real S ≤ B := by
  rw [measureReal_def]
  calc
    (μ S).toReal ≤ (ENNReal.ofReal B).toReal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    _ = B := ENNReal.toReal_ofReal hB

/-- **Geometric-drift tail bound** (Theorem 4.2, kernel version).

If a Markov kernel `K` satisfies the multiplicative drift condition
`∫⁻ Φ dK(x) ≤ r · Φ(x)` for all `x`, then for any threshold `θ`,
`θ · (K ^ t) x {y | θ ≤ Φ y} ≤ r ^ t · Φ(x)`.

This is a direct consequence of Markov's inequality (`mul_meas_ge_le_lintegral₀`)
followed by the geometric-decay lemma (`lintegral_geometric_decay`). -/
theorem geometric_drift_tail_kernel {α : Type*} [MeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K]
    (Φ : α → ℝ≥0∞) (hΦ : Measurable Φ)
    (r : ℝ≥0∞)
    (hdrift : ∀ x, ∫⁻ y, Φ y ∂(K x) ≤ r * Φ x)
    (t : ℕ) (x : α) (θ : ℝ≥0∞) :
    θ * (K ^ t) x {y | θ ≤ Φ y} ≤ r ^ t * Φ x := by
  calc
    θ * (K ^ t) x {y | θ ≤ Φ y} ≤ ∫⁻ y, Φ y ∂((K ^ t) x) :=
      mul_meas_ge_le_lintegral₀ (hf := hΦ.aemeasurable) (ε := θ)
    _ ≤ r ^ t * Φ x := lintegral_geometric_decay K Φ hΦ r hdrift t x

/-- **Geometric-drift tail bound, division form** (Theorem 4.2 corollary).

Under the same drift condition as `geometric_drift_tail_kernel`, for a finite
non-zero threshold `θ` (i.e., `θ ≠ 0` and `θ ≠ ∞`), the measure of the
super-level set `{θ ≤ Φ}` after `t` steps is bounded by `r^t · Φ(x) / θ`.

This follows immediately from the multiplicative form by dividing both sides
by `θ` (using `ENNReal.inv_mul_cancel` when `θ` is finite and non-zero). -/
theorem geometric_drift_tail {α : Type*} [MeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K]
    (Φ : α → ℝ≥0∞) (hΦ : Measurable Φ)
    (r : ℝ≥0∞)
    (hdrift : ∀ x, ∫⁻ y, Φ y ∂(K x) ≤ r * Φ x)
    (t : ℕ) (x : α) (θ : ℝ≥0∞) (hθ0 : θ ≠ 0) (hθ_top : θ ≠ ∞) :
    (K ^ t) x {y | θ ≤ Φ y} ≤ r ^ t * Φ x / θ := by
  have h := geometric_drift_tail_kernel K Φ hΦ r hdrift t x θ
  -- h: θ * μ ≤ r^t * Φ x  where μ = (K^t) x {θ ≤ Φ}
  calc
    (K ^ t) x {y | θ ≤ Φ y} = (θ⁻¹ * θ) * (K ^ t) x {y | θ ≤ Φ y} := by
      simp [ENNReal.inv_mul_cancel hθ0 hθ_top]
    _ = θ⁻¹ * (θ * (K ^ t) x {y | θ ≤ Φ y}) := by
      simp [mul_assoc]
    _ ≤ θ⁻¹ * (r ^ t * Φ x) := by gcongr
    _ = r ^ t * Φ x * θ⁻¹ := by
      simp [mul_comm, mul_assoc]
    _ = r ^ t * Φ x / θ := rfl

/-- **Geometric-drift tail bound for a random variable with known law.**

If a random configuration/state variable `X : Ω → α` has law `(K ^ t) x`, then
the kernel tail bound pulls back to the probability space. This is the wrapper
needed by phase analyses that construct a concrete execution probability space
and then identify its `t`-step marginal with a Markov-kernel power. -/
theorem geometric_drift_tail_random_variable {Ω α : Type*}
    [MeasurableSpace Ω] [MeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K]
    (Φ : α → ℝ≥0∞) (hΦ : Measurable Φ)
    (r : ℝ≥0∞)
    (hdrift : ∀ x, ∫⁻ y, Φ y ∂(K x) ≤ r * Φ x)
    (μ : Measure Ω) (X : Ω → α) (hX : Measurable X)
    (t : ℕ) (x : α)
    (hlaw : Measure.map X μ = (K ^ t) x)
    (θ : ℝ≥0∞) (hθ0 : θ ≠ 0) (hθ_top : θ ≠ ∞) :
    μ {ω | θ ≤ Φ (X ω)} ≤ r ^ t * Φ x / θ := by
  let S : Set α := {y | θ ≤ Φ y}
  have hS : MeasurableSet S := measurableSet_le measurable_const hΦ
  have hmap :
      μ {ω | θ ≤ Φ (X ω)} = (K ^ t) x S := by
    calc
      μ {ω | θ ≤ Φ (X ω)} = μ (X ⁻¹' S) := rfl
      _ = Measure.map X μ S := (Measure.map_apply hX hS).symm
      _ = (K ^ t) x S := by rw [hlaw]
  rw [hmap]
  exact geometric_drift_tail K Φ hΦ r hdrift t x θ hθ0 hθ_top

/-- Real-valued probability form of `geometric_drift_tail_random_variable`.

The caller supplies the final algebraic comparison
`r^t * Φ x / θ ≤ ENNReal.ofReal B`; this theorem performs the law pullback and
the `Measure.real` conversion. -/
theorem geometric_drift_tail_random_variable_real_bound {Ω α : Type*}
    [MeasurableSpace Ω] [MeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K]
    (Φ : α → ℝ≥0∞) (hΦ : Measurable Φ)
    (r : ℝ≥0∞)
    (hdrift : ∀ x, ∫⁻ y, Φ y ∂(K x) ≤ r * Φ x)
    (μ : Measure Ω) (X : Ω → α) (hX : Measurable X)
    (t : ℕ) (x : α)
    (hlaw : Measure.map X μ = (K ^ t) x)
    (θ : ℝ≥0∞) (hθ0 : θ ≠ 0) (hθ_top : θ ≠ ∞)
    {B : ℝ} (hB : 0 ≤ B)
    (hbound : r ^ t * Φ x / θ ≤ ENNReal.ofReal B) :
    μ.real {ω | θ ≤ Φ (X ω)} ≤ B := by
  exact measure_real_le_of_le_ofReal μ _ hB
    ((geometric_drift_tail_random_variable
      K Φ hΦ r hdrift μ X hX t x hlaw θ hθ0 hθ_top).trans hbound)

/-- Threshold-one specialization of
`geometric_drift_tail_random_variable`. This is the form used by the regional
potential arguments, where the active event is encoded as `{1 ≤ Φ}`. -/
theorem geometric_drift_tail_random_variable_ge_one {Ω α : Type*}
    [MeasurableSpace Ω] [MeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K]
    (Φ : α → ℝ≥0∞) (hΦ : Measurable Φ)
    (r : ℝ≥0∞)
    (hdrift : ∀ x, ∫⁻ y, Φ y ∂(K x) ≤ r * Φ x)
    (μ : Measure Ω) (X : Ω → α) (hX : Measurable X)
    (t : ℕ) (x : α)
    (hlaw : Measure.map X μ = (K ^ t) x) :
    μ {ω | 1 ≤ Φ (X ω)} ≤ r ^ t * Φ x := by
  simpa using
    geometric_drift_tail_random_variable
      K Φ hΦ r hdrift μ X hX t x hlaw (1 : ℝ≥0∞)
      one_ne_zero ENNReal.one_ne_top

/-- Real-valued threshold-one specialization of the geometric-drift tail
bound. -/
theorem geometric_drift_tail_random_variable_ge_one_real_bound {Ω α : Type*}
    [MeasurableSpace Ω] [MeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K]
    (Φ : α → ℝ≥0∞) (hΦ : Measurable Φ)
    (r : ℝ≥0∞)
    (hdrift : ∀ x, ∫⁻ y, Φ y ∂(K x) ≤ r * Φ x)
    (μ : Measure Ω) (X : Ω → α) (hX : Measurable X)
    (t : ℕ) (x : α)
    (hlaw : Measure.map X μ = (K ^ t) x)
    {B : ℝ} (hB : 0 ≤ B)
    (hbound : r ^ t * Φ x ≤ ENNReal.ofReal B) :
    μ.real {ω | 1 ≤ Φ (X ω)} ≤ B := by
  exact measure_real_le_of_le_ofReal μ _ hB
    ((geometric_drift_tail_random_variable_ge_one
      K Φ hΦ r hdrift μ X hX t x hlaw).trans hbound)

end Ripple.PopulationProtocol.ExactMajority
