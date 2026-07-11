/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Absorbed Kernel Helpers (Generic)

Generic absorbed-kernel machinery extracted from PopProto/ConvergenceTime.lean.
These tools are protocol-independent: any Markov kernel K on a discrete
measurable space can be "absorbed" outside a region R via
`Kernel.piecewise hR K Kernel.id`.

## Main results

- `absorbedKernel_pow_eq_dirac_of_not_mem`: Outside R, the absorbed kernel
  iterates to a point mass forever.

- `lintegral_natCast_le_of_integral_le`: Bridge from Bochner integral bounds
  (over ℝ) to Lebesgue integral bounds (over ℝ≥0∞) for ℕ-valued potentials.

- `absorbed_drift_of_truncated`: If `Φ` contracts inside R, the truncated
  potential `ΦT = Φ · 1_R` contracts unconditionally under the absorbed kernel.

## Usage pattern (from ConvergenceTime.lean)

1. Define active region `R` and absorbed kernel `K_R = piecewise(hR, K, id)`.
2. Define truncated potential `ΦT(c) = if c ∈ R then Φ(c) else 0`.
3. Prove `∫⁻ ΦT dK_R(c) ≤ r · ΦT(c)` for ALL c (inside: drift; outside: 0=r·0).
4. Call `lintegral_geometric_decay` → `measure_potential_ge_one`.
5. Result: `K_R^t(c₀, R) ≤ r^t · ΦT(c₀)`.

This handles "stuck states" by absorbing them outside R.
-/

import Ripple.PopulationProtocol.Majority.PopProtoCommon.Convergence.GeometricDrift
import Mathlib.Probability.Kernel.Composition.Comp

namespace PopProtoCommon

open MeasureTheory ProbabilityTheory
open scoped ENNReal

attribute [local instance] Classical.propDecidable

/-! ### Absorbed kernel iteration -/

/-- Outside a region R, the absorbed kernel `piecewise(R, K, id)` iterates
to a Dirac mass forever. This is the key lemma that makes stuck states
contribute zero probability. -/
theorem absorbedKernel_pow_eq_dirac_of_not_mem
    {α : Type*} [MeasurableSpace α]
    {R : Set α} (hR : MeasurableSet R)
    (K : Kernel α α) (c : α)
    (hc : c ∉ R) (t : ℕ) :
    ((Kernel.piecewise hR K Kernel.id) ^ t) c = Measure.dirac c := by
  have hK : Kernel.piecewise hR K Kernel.id c = Measure.dirac c := by
    rw [Kernel.piecewise_apply, if_neg hc, Kernel.id_apply]
  induction t with
  | zero =>
    simp only [pow_zero]
    change Kernel.id c = Measure.dirac c
    exact Kernel.id_apply c
  | succ t ih =>
    exact Measure.ext (fun S hS => by
      rw [Kernel.pow_succ_apply_eq_lintegral _ _ _ hS, ih,
          MeasureTheory.lintegral_dirac' _
            (Kernel.measurable_coe _ hS), hK])

/-- The absorbed kernel is zero on R when started outside R. -/
theorem absorbedKernel_active_eq_zero_of_not_mem
    {α : Type*} [MeasurableSpace α]
    {R : Set α} (hR : MeasurableSet R)
    (K : Kernel α α) (c : α) (hc : c ∉ R) (t : ℕ) :
    ((Kernel.piecewise hR K Kernel.id) ^ t) c R = 0 := by
  rw [absorbedKernel_pow_eq_dirac_of_not_mem hR K c hc t,
      Measure.dirac_apply' c hR]
  simp [Set.indicator_apply, hc]

/-! ### Bochner → Lebesgue bridge for ℕ-valued potentials -/

/-- Bridge: a Bochner integral bound `∫ Φ ≤ r·Φ(c)` for ℕ-valued `Φ`
implies the corresponding Lebesgue integral bound in ℝ≥0∞.
Converts through `ENNReal.ofReal` using `∫⁻ f = ofReal(∫ f)` for
non-negative integrable functions. -/
theorem lintegral_natCast_le_of_integral_le
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (Φ : α → ℕ) (r : ℝ) (hr : 0 ≤ r) (c : α)
    (hfi : Integrable (fun c' => (Φ c' : ℝ)) μ)
    (h : ∫ c', (Φ c' : ℝ) ∂μ ≤ r * (Φ c : ℝ)) :
    ∫⁻ c', (Φ c' : ℝ≥0∞) ∂μ ≤ ENNReal.ofReal r * (Φ c : ℝ≥0∞) := by
  simp_rw [show ∀ c' : α, (Φ c' : ℝ≥0∞) = ENNReal.ofReal (Φ c' : ℝ) from
    fun c' => (ENNReal.ofReal_natCast (Φ c')).symm]
  rw [← ofReal_integral_eq_lintegral_ofReal hfi
    (ae_of_all _ fun c' => Nat.cast_nonneg (Φ c'))]
  rw [← ENNReal.ofReal_mul hr]
  exact ENNReal.ofReal_le_ofReal h

/-! ### Truncated potential drift -/

/-- If a potential `Φ` contracts under `K` inside region `R` (i.e.,
`∫⁻ Φ dK(c) ≤ r · Φ(c)` for c ∈ R), and `ΦT = Φ · 1_R` is the
truncated potential, then `ΦT` contracts unconditionally under the
absorbed kernel `K_R = piecewise(R, K, id)`.

Inside R: K_R = K, and ΦT ≤ Φ so the drift bound transfers.
Outside R: K_R = id (dirac), ΦT(c) = 0, and ∫ ΦT d(dirac c) = 0 = r·0. -/
theorem absorbed_drift_of_truncated
    {α : Type*} [MeasurableSpace α]
    {R : Set α} (hR : MeasurableSet R)
    (K : Kernel α α) [IsMarkovKernel K]
    (Φ : α → ℝ≥0∞) (hΦ : Measurable Φ)
    (r : ℝ≥0∞)
    (hdrift_inside : ∀ c, c ∈ R →
      ∫⁻ c', Φ c' ∂(K c) ≤ r * Φ c) :
    let ΦT := fun c => if c ∈ R then Φ c else 0
    let K_R := Kernel.piecewise hR K Kernel.id
    ∀ c, ∫⁻ c', ΦT c' ∂(K_R c) ≤ r * ΦT c := by
  intro ΦT K_R c
  by_cases hc : c ∈ R
  · -- Inside R: K_R c = K c, ΦT(c) = Φ(c)
    simp only [K_R, Kernel.piecewise_apply, if_pos hc]
    calc ∫⁻ c', ΦT c' ∂(K c)
        ≤ ∫⁻ c', Φ c' ∂(K c) := by
          apply lintegral_mono
          intro c'
          simp only [ΦT]
          split_ifs <;> simp
      _ ≤ r * Φ c := hdrift_inside c hc
      _ = r * ΦT c := by simp [ΦT, hc]
  · -- Outside R: K_R c = dirac c, ΦT(c) = 0
    simp only [K_R, Kernel.piecewise_apply, if_neg hc, Kernel.id_apply]
    have hΦT_meas : Measurable ΦT := by
      apply Measurable.ite hR hΦ measurable_const
    rw [lintegral_dirac' c hΦT_meas]
    simp [ΦT, hc]

/-- Combine absorbed_drift + geometric_decay + measure_potential_ge_one
into a single tail bound for region exit.

If Φ contracts inside R with rate r, then after t absorbed-kernel steps,
P[still in R] ≤ r^t · Φ(c₀). -/
theorem prob_in_region_le_of_drift
    {α : Type*} [MeasurableSpace α]
    {R : Set α} (hR : MeasurableSet R)
    (K : Kernel α α) [IsMarkovKernel K]
    (Φ : α → ℝ≥0∞) (hΦ : Measurable Φ)
    (r : ℝ≥0∞)
    (hdrift : ∀ c, c ∈ R → ∫⁻ c', Φ c' ∂(K c) ≤ r * Φ c)
    (hR_eq : R = {c | 1 ≤ Φ c})
    (t : ℕ) (c₀ : α) :
    (Kernel.piecewise hR K Kernel.id ^ t) c₀ R ≤
      r ^ t * (if c₀ ∈ R then Φ c₀ else 0) := by
  let ΦT := fun c => if c ∈ R then Φ c else 0
  have hΦT : Measurable ΦT := Measurable.ite hR hΦ measurable_const
  have hdrift_uncon := absorbed_drift_of_truncated hR K Φ hΦ r hdrift
  have hge := measure_potential_ge_one
    (Kernel.piecewise hR K Kernel.id) ΦT hΦT r hdrift_uncon t c₀
  have hR_sub : R ⊆ {c | 1 ≤ ΦT c} := by
    intro c hc
    simp only [Set.mem_setOf_eq, ΦT, if_pos hc]
    rw [hR_eq] at hc
    exact hc
  calc (Kernel.piecewise hR K Kernel.id ^ t) c₀ R
      ≤ (Kernel.piecewise hR K Kernel.id ^ t) c₀ {c | 1 ≤ ΦT c} :=
        Measure.measure_mono hR_sub
    _ ≤ r ^ t * ΦT c₀ := hge
    _ = r ^ t * (if c₀ ∈ R then Φ c₀ else 0) := rfl

end PopProtoCommon
