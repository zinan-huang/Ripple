/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Geometric Drift and Convergence (Generic)

The multiplicative drift theorem at the abstract Markov-kernel level.

This file is the *generic* core of `PopProto/Convergence/GeometricDrift.lean`:
it abstracts over an arbitrary Markov kernel `K : Kernel α α` and a measurable
potential `Φ : α → ℝ≥0∞`. The AAE-specific `IsMarkovKernel` instance for the
population-protocol transition kernel is **not** included here; it remains in
PP-Proof's downstream module.

## Main results

- `lintegral_geometric_decay`: If `∫⁻ Φ dK(x) ≤ r·Φ(x)` for all x, then
  `∫⁻ Φ d(K^t)(x) ≤ r^t · Φ(x)`.

- `measure_potential_ge_one`: The probability of `{Φ ≥ 1}` after `t` kernel
  iterations is at most `r^t · Φ(x₀)`.

## Dependencies

Requires `Mathlib.Probability.Kernel.Composition.Comp` for `Kernel.lintegral_comp`
and `Kernel.pow`.
-/

import Mathlib.Probability.Kernel.Composition.Comp

namespace PopProtoCommon

open scoped ENNReal
open MeasureTheory ProbabilityTheory

/-! ### Geometric Decay Lemma

The key measure-theoretic lemma: if a Markov kernel K satisfies
`∫⁻ Φ dK(x) ≤ r·Φ(x)` for all x, then iterating K for t steps gives
`∫⁻ Φ d(K^t)(x) ≤ r^t · Φ(x)`.

Proof by induction on t using:
- Base: K^0 = id, integral = Φ(x)
- Step: K^{t+1} = K^t ∘ₖ K, use Chapman-Kolmogorov + monotonicity -/

/-- **Geometric decay for lintegral**: multiplicative contraction composes
    geometrically under kernel iteration. -/
theorem lintegral_geometric_decay {α : Type*} [MeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K]
    (Φ : α → ℝ≥0∞) (hΦ : Measurable Φ)
    (r : ℝ≥0∞)
    (hdrift : ∀ x, ∫⁻ y, Φ y ∂(K x) ≤ r * Φ x)
    (t : ℕ) (x : α) :
    ∫⁻ y, Φ y ∂((K ^ t) x) ≤ r ^ t * Φ x := by
  induction t generalizing x with
  | zero =>
    simp only [pow_zero, one_mul]
    -- (1 : Kernel α α) = Kernel.id, so (1) x = dirac x
    change ∫⁻ y, Φ y ∂(Kernel.id x) ≤ Φ x
    rw [Kernel.id_apply, lintegral_dirac' x hΦ]
  | succ t ih =>
    -- K^{t+1} = K^t * K = (K^t) ∘ₖ K
    change ∫⁻ y, Φ y ∂(((K ^ t) ∘ₖ K) x) ≤ r ^ (t + 1) * Φ x
    -- Chapman-Kolmogorov: ∫⁻ Φ d((K^t ∘ₖ K) x) = ∫⁻ b, ∫⁻ Φ d(K^t b) d(K x)
    rw [Kernel.lintegral_comp _ K x hΦ]
    -- Chain: IH → monotonicity → linearity → drift → pow
    calc ∫⁻ b, ∫⁻ y, Φ y ∂((K ^ t) b) ∂(K x)
        ≤ ∫⁻ b, r ^ t * Φ b ∂(K x) := lintegral_mono (fun b => ih b)
      _ = r ^ t * ∫⁻ b, Φ b ∂(K x) := lintegral_const_mul _ hΦ
      _ ≤ r ^ t * (r * Φ x) := by gcongr; exact hdrift x
      _ = r ^ (t + 1) * Φ x := by rw [pow_succ, mul_assoc]

/-! ### Markov's inequality application

From geometric decay E[Φ_t] ≤ r^t · Φ_0 and Φ ≥ 1 in the region,
we get P[in region at time t] ≤ r^t · Φ_0. -/

/-- The measure of {y | 1 ≤ Φ(y)} under the t-step kernel is bounded
    by r^t · Φ(x₀). This gives the probability of remaining in a region
    where the potential is at least 1. -/
theorem measure_potential_ge_one {α : Type*} [MeasurableSpace α]
    (K : Kernel α α) [IsMarkovKernel K]
    (Φ : α → ℝ≥0∞) (hΦ : Measurable Φ)
    (r : ℝ≥0∞)
    (hdrift : ∀ x, ∫⁻ y, Φ y ∂(K x) ≤ r * Φ x)
    (t : ℕ) (x : α) :
    (K ^ t) x {y | 1 ≤ Φ y} ≤ r ^ t * Φ x := by
  have hmarkov := mul_meas_ge_le_lintegral₀ (μ := (K ^ t) x) hΦ.aemeasurable (1 : ℝ≥0∞)
  simp only [one_mul] at hmarkov
  exact le_trans hmarkov (lintegral_geometric_decay K Φ hΦ r hdrift t x)

end PopProtoCommon
