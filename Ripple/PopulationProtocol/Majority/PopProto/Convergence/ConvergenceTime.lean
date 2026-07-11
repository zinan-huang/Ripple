/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Convergence Time Bound

Combines the multiplicative drift conditions (Expected.lean) with the
geometric decay theorem (GeometricDrift.lean) to bound the time until
the approximate majority protocol exits each region.

## Strategy

1. Define the **absorbed kernel** `K_R = piecewise(R, K, id)` that absorbs
   outside the active region R.
2. Define the **truncated potential** `Φ̃ = Φ · 1_R` (zero outside R).
3. Show `Φ̃` satisfies the unconditional drift under `K_R`.
4. Apply `lintegral_geometric_decay` and `measure_potential_ge_one`.
5. Obtain: `(K_R^t)(c₀, R) ≤ r^t · Φ(c₀)`.

## Main results

- `absorbed_drift_largeX`: The truncated potential contracts under the
  absorbed kernel for the large-x region.

- `prob_in_activeLargeX_le`: Tail bound for exit from the large-x corner:
  P[still in active large-x at time t | absorbed] ≤ r^t · Φ̃(c₀).
-/

import Ripple.PopulationProtocol.Majority.PopProto.Convergence.GeometricDrift
import Ripple.PopulationProtocol.Majority.PopProto.Invariant.Absorbing

namespace PopProto

open MeasureTheory ProbabilityTheory
open scoped ENNReal
attribute [local instance] Classical.propDecidable

namespace Config

variable {n : ℕ}

/-! ### Discrete measurability helpers -/

private theorem measurable_ennreal (f : Config n → ℝ≥0∞) : Measurable f :=
  fun _ _ => instDiscreteMeasurableSpaceConfig.forall_measurableSet _

private theorem measurable_real (f : Config n → ℝ) : Measurable f :=
  fun _ _ => instDiscreteMeasurableSpaceConfig.forall_measurableSet _

/-! ### Generic absorbed-kernel helpers -/

/-- A kernel absorbed outside `R` stays fixed forever when started outside `R`. -/
private theorem absorbedKernel_pow_eq_dirac_of_not_mem
    {R : Set (Config n)} (hR : MeasurableSet R)
    (K : Kernel (Config n) (Config n)) (c : Config n)
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

/-! ### Active region definitions -/

/-- The active large-x region: x ≥ 7n/8 AND not at x-consensus (b+y ≥ 1).
    This excludes the absorbing all-x state where the drift bound fails. -/
def activeLargeX : Set (Config n) :=
  {c | c.inLargeX ∧ c.b_count + c.y_count ≥ 1}

/-- The active large-y region (symmetric). -/
def activeLargeY : Set (Config n) :=
  {c | c.inLargeY ∧ c.b_count + c.x_count ≥ 1}

private theorem activeLargeX_measurableSet :
    MeasurableSet (activeLargeX : Set (Config n)) :=
  instDiscreteMeasurableSpaceConfig.forall_measurableSet _

private theorem activeLargeY_measurableSet :
    MeasurableSet (activeLargeY : Set (Config n)) :=
  instDiscreteMeasurableSpaceConfig.forall_measurableSet _

/-! ### Absorbed kernels -/

/-- Absorbed kernel for large-x: transitions normally inside the active
    region, stays put (absorbs) outside. -/
noncomputable def absorbedKernelLargeX (hn : n ≥ 2) :
    Kernel (Config n) (Config n) :=
  Kernel.piecewise activeLargeX_measurableSet (transitionKernel hn) Kernel.id

/-- Absorbed kernel for large-y (symmetric). -/
noncomputable def absorbedKernelLargeY (hn : n ≥ 2) :
    Kernel (Config n) (Config n) :=
  Kernel.piecewise activeLargeY_measurableSet (transitionKernel hn) Kernel.id

instance instIsMarkovAbsorbedLargeX (hn : n ≥ 2) :
    IsMarkovKernel (absorbedKernelLargeX hn) := by
  unfold absorbedKernelLargeX
  have := instIsMarkovKernel hn
  infer_instance

instance instIsMarkovAbsorbedLargeY (hn : n ≥ 2) :
    IsMarkovKernel (absorbedKernelLargeY hn) := by
  unfold absorbedKernelLargeY
  have := instIsMarkovKernel hn
  infer_instance

theorem absorbedKernelLargeX_pow_eq_dirac_of_not_mem
    (hn : n ≥ 2) (c : Config n) (hc : c ∉ activeLargeX) (t : ℕ) :
    (absorbedKernelLargeX hn ^ t) c = Measure.dirac c := by
  unfold absorbedKernelLargeX
  exact absorbedKernel_pow_eq_dirac_of_not_mem activeLargeX_measurableSet
    (transitionKernel hn) c hc t

theorem absorbedKernelLargeY_pow_eq_dirac_of_not_mem
    (hn : n ≥ 2) (c : Config n) (hc : c ∉ activeLargeY) (t : ℕ) :
    (absorbedKernelLargeY hn ^ t) c = Measure.dirac c := by
  unfold absorbedKernelLargeY
  exact absorbedKernel_pow_eq_dirac_of_not_mem activeLargeY_measurableSet
    (transitionKernel hn) c hc t

theorem absorbedKernelLargeX_active_eq_zero_of_not_mem
    (hn : n ≥ 2) (c : Config n) (hc : c ∉ activeLargeX) (t : ℕ) :
    (absorbedKernelLargeX hn ^ t) c activeLargeX = 0 := by
  rw [absorbedKernelLargeX_pow_eq_dirac_of_not_mem hn c hc t,
    Measure.dirac_apply' _ activeLargeX_measurableSet]
  simp [hc]

theorem absorbedKernelLargeY_active_eq_zero_of_not_mem
    (hn : n ≥ 2) (c : Config n) (hc : c ∉ activeLargeY) (t : ℕ) :
    (absorbedKernelLargeY hn ^ t) c activeLargeY = 0 := by
  rw [absorbedKernelLargeY_pow_eq_dirac_of_not_mem hn c hc t,
    Measure.dirac_apply' _ activeLargeY_measurableSet]
  simp [hc]

/-! ### Truncated potentials -/

/-- Truncated potential for large-x: `potentialLargeX` inside the active
    region, 0 outside. -/
noncomputable def potentialLargeXTrunc (c : Config n) : ℝ≥0∞ :=
  if c ∈ activeLargeX then (c.potentialLargeX : ℝ≥0∞) else 0

/-- Truncated potential for large-y (symmetric). -/
noncomputable def potentialLargeYTrunc (c : Config n) : ℝ≥0∞ :=
  if c ∈ activeLargeY then (c.potentialLargeY : ℝ≥0∞) else 0

private theorem potentialLargeXTrunc_measurable :
    Measurable (potentialLargeXTrunc : Config n → ℝ≥0∞) :=
  measurable_ennreal _

private theorem potentialLargeYTrunc_measurable :
    Measurable (potentialLargeYTrunc : Config n → ℝ≥0∞) :=
  measurable_ennreal _

/-- The truncated potential is bounded by the full potential. -/
private theorem potentialLargeXTrunc_le (c : Config n) :
    potentialLargeXTrunc c ≤ (c.potentialLargeX : ℝ≥0∞) := by
  unfold potentialLargeXTrunc
  split_ifs <;> simp

private theorem potentialLargeYTrunc_le (c : Config n) :
    potentialLargeYTrunc c ≤ (c.potentialLargeY : ℝ≥0∞) := by
  unfold potentialLargeYTrunc
  split_ifs <;> simp

/-! ### Region = {Φ̃ ≥ 1}

The active region is exactly the set where the truncated potential is ≥ 1.
This connects the absorbed kernel's tail bound to region exit. -/

/-- The active large-x region equals `{c | 1 ≤ potentialLargeXTrunc c}`. -/
theorem activeLargeX_eq_ge_one :
    (activeLargeX : Set (Config n)) =
    {c | 1 ≤ potentialLargeXTrunc c} := by
  ext c
  simp only [Set.mem_setOf_eq, activeLargeX, potentialLargeXTrunc]
  constructor
  · intro hc
    rw [if_pos hc]
    have h1 : 1 ≤ c.potentialLargeX := by
      unfold potentialLargeX; obtain ⟨_, hby⟩ := hc; omega
    exact_mod_cast h1
  · intro hc
    by_contra hc'
    simp [if_neg hc'] at hc

theorem activeLargeY_eq_ge_one :
    (activeLargeY : Set (Config n)) =
    {c | 1 ≤ potentialLargeYTrunc c} := by
  ext c
  simp only [Set.mem_setOf_eq, activeLargeY, potentialLargeYTrunc]
  constructor
  · intro hc
    rw [if_pos hc]
    have h1 : 1 ≤ c.potentialLargeY := by
      unfold potentialLargeY; obtain ⟨_, hbx⟩ := hc; omega
    exact_mod_cast h1
  · intro hc
    by_contra hc'
    simp [if_neg hc'] at hc

/-! ### Integrability helpers

The drift conditions use Bochner integrals which require integrability.
Since our potentials are ℕ-valued and bounded by `3n + 1`, they are
integrable on any probability measure (hence finite measure). -/

private theorem potentialLargeX_le_3n (c' : Config n) :
    c'.potentialLargeX ≤ 3 * n + 1 := by
  unfold potentialLargeX; have := c'.sum_eq; omega

private theorem potentialLargeY_le_3n (c' : Config n) :
    c'.potentialLargeY ≤ 3 * n + 1 := by
  unfold potentialLargeY; have := c'.sum_eq; omega

private theorem integrable_potentialLargeX (c : Config n) (hn : n ≥ 2) :
    Integrable (fun c' => (c'.potentialLargeX : ℝ)) (transitionKernel hn c) := by
  have := (instIsMarkovKernel hn).isProbabilityMeasure c
  exact Integrable.of_bound (measurable_real _).aestronglyMeasurable (3 * n + 1 : ℝ)
    (ae_of_all _ fun c' => by
      rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
      exact_mod_cast potentialLargeX_le_3n c')

private theorem integrable_potentialLargeY (c : Config n) (hn : n ≥ 2) :
    Integrable (fun c' => (c'.potentialLargeY : ℝ)) (transitionKernel hn c) := by
  have := (instIsMarkovKernel hn).isProbabilityMeasure c
  exact Integrable.of_bound (measurable_real _).aestronglyMeasurable (3 * n + 1 : ℝ)
    (ae_of_all _ fun c' => by
      rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
      exact_mod_cast potentialLargeY_le_3n c')

/-! ### Bochner to Lebesgue bridge

The drift conditions in Expected.lean are stated as Bochner integral
bounds (over ℝ). The geometric decay theorem needs Lebesgue integral
bounds (over ℝ≥0∞). We bridge the gap using `ofReal` monotonicity. -/

/-- Bridge: a Bochner integral bound `∫ Φ ≤ r·Φ(c)` for ℕ-valued `Φ`
    implies the corresponding Lebesgue integral bound in ℝ≥0∞.
    The proof converts through `ENNReal.ofReal` using the identity
    `∫⁻ f = ofReal(∫ f)` for non-negative integrable functions. -/
private theorem lintegral_natCast_le_of_integral_le
    (μ : Measure (Config n)) [IsProbabilityMeasure μ]
    (Φ : Config n → ℕ) (r : ℝ) (hr : 0 ≤ r) (c : Config n)
    (hfi : Integrable (fun c' => (Φ c' : ℝ)) μ)
    (h : ∫ c', (Φ c' : ℝ) ∂μ ≤ r * (Φ c : ℝ)) :
    ∫⁻ c', (Φ c' : ℝ≥0∞) ∂μ ≤ ENNReal.ofReal r * (Φ c : ℝ≥0∞) := by
  -- Cast: (Φ c' : ℝ≥0∞) = ENNReal.ofReal (Φ c' : ℝ) via ofReal_natCast
  simp_rw [show ∀ c' : Config n, (Φ c' : ℝ≥0∞) = ENNReal.ofReal (Φ c' : ℝ) from
    fun c' => (ENNReal.ofReal_natCast (Φ c')).symm]
  -- ∫⁻ ofReal(Φ) = ofReal(∫ Φ) for non-negative integrable Φ
  rw [← ofReal_integral_eq_lintegral_ofReal hfi
    (ae_of_all _ fun c' => Nat.cast_nonneg (Φ c'))]
  -- Goal: ofReal(∫ Φ) ≤ ofReal(r) * ofReal(Φ c) = ofReal(r * Φ(c))
  rw [← ENNReal.ofReal_mul hr]
  exact ENNReal.ofReal_le_ofReal h

/-! ### Contraction rate -/

private theorem contraction_rate_nonneg (hn : n ≥ 2) :
    (0 : ℝ) ≤ 1 - 13 / (64 * ((n : ℝ) - 1)) := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h_nm1 : (1 : ℝ) ≤ (n : ℝ) - 1 := by linarith
  have hpos : (0 : ℝ) < 64 * ((n : ℝ) - 1) := by
    exact mul_pos (by norm_num : (0 : ℝ) < 64) (by linarith)
  suffices h : 13 ≤ 64 * ((n : ℝ) - 1) by
    linarith [(div_le_one hpos).mpr h]
  calc (13 : ℝ) ≤ 64 * 1 := by norm_num
    _ ≤ 64 * ((n : ℝ) - 1) :=
        mul_le_mul_of_nonneg_left h_nm1 (by norm_num : (0 : ℝ) ≤ 64)

/-! ### Core drift theorem: absorbed kernel contracts the truncated potential -/

/-- **Unconditional drift for the absorbed kernel (large-x)**:
    The truncated potential `Φ̃` satisfies `∫⁻ Φ̃ dK_R(c) ≤ r·Φ̃(c)`
    for ALL configurations c (not just those in the region).

    - Inside the region: `K_R = K`, and `∫⁻ Φ̃ ≤ ∫⁻ Φ ≤ r·Φ = r·Φ̃`.
    - Outside the region: `K_R = id`, and `∫⁻ Φ̃ d(dirac c) = Φ̃(c) = 0 = r·0`. -/
theorem absorbed_drift_largeX (hn : n ≥ 2) (c : Config n) :
    ∫⁻ c', potentialLargeXTrunc c' ∂(absorbedKernelLargeX hn c) ≤
    ENNReal.ofReal (1 - 13 / (64 * ((n : ℝ) - 1))) *
    potentialLargeXTrunc c := by
  unfold absorbedKernelLargeX
  rw [Kernel.lintegral_piecewise]
  by_cases hc : c ∈ activeLargeX
  · -- Case: c is in the active large-x region
    rw [if_pos hc]
    calc ∫⁻ c', potentialLargeXTrunc c' ∂(transitionKernel hn c)
        ≤ ∫⁻ c', (c'.potentialLargeX : ℝ≥0∞) ∂(transitionKernel hn c) :=
          lintegral_mono (fun c' => potentialLargeXTrunc_le c')
      _ ≤ ENNReal.ofReal (1 - 13 / (64 * ((n : ℝ) - 1))) *
          (c.potentialLargeX : ℝ≥0∞) := by
          -- Bridge from Bochner integral bound to Lebesgue integral bound
          have hprob : IsProbabilityMeasure (transitionKernel hn c) :=
            (instIsMarkovKernel hn).isProbabilityMeasure c
          exact lintegral_natCast_le_of_integral_le
            (transitionKernel hn c) Config.potentialLargeX _ (contraction_rate_nonneg hn) c
            (integrable_potentialLargeX c hn)
            (expected_potentialLargeX_le c hc.1 hn hc.2)
      _ = ENNReal.ofReal (1 - 13 / (64 * ((n : ℝ) - 1))) *
          potentialLargeXTrunc c := by
          congr 1; exact (show potentialLargeXTrunc c =
            (c.potentialLargeX : ℝ≥0∞) from if_pos hc).symm
  · -- Case: c is NOT in the active region (absorbed)
    rw [if_neg hc, Kernel.id_apply,
        lintegral_dirac' c potentialLargeXTrunc_measurable]
    simp [potentialLargeXTrunc, hc]

/-! ### Tail bound for region exit -/

/-- **Geometric tail bound (large-x region)**:
    The probability of remaining in the active large-x region for t steps
    under the absorbed kernel decays geometrically.

    `P[in activeLargeX at time t | absorbed] ≤ r^t · Φ̃(c₀)`

    where `r = 1 - 13/(64(n-1))` and `Φ̃(c₀) = potentialLargeX(c₀)` when
    `c₀` is in the active region. -/
theorem prob_in_activeLargeX_le (hn : n ≥ 2) (c₀ : Config n) (t : ℕ) :
    (absorbedKernelLargeX hn ^ t) c₀ activeLargeX ≤
    ENNReal.ofReal ((1 - 13 / (64 * ((n : ℝ) - 1))) ^ t) *
    potentialLargeXTrunc c₀ := by
  rw [activeLargeX_eq_ge_one]
  have h := measure_potential_ge_one
    (absorbedKernelLargeX hn) potentialLargeXTrunc potentialLargeXTrunc_measurable
    (ENNReal.ofReal (1 - 13 / (64 * ((n : ℝ) - 1))))
    (absorbed_drift_largeX hn) t c₀
  rw [ENNReal.ofReal_pow (contraction_rate_nonneg hn)]
  exact h

/-! ### Symmetric tail bound for large-y -/

theorem absorbed_drift_largeY (hn : n ≥ 2) (c : Config n) :
    ∫⁻ c', potentialLargeYTrunc c' ∂(absorbedKernelLargeY hn c) ≤
    ENNReal.ofReal (1 - 13 / (64 * ((n : ℝ) - 1))) *
    potentialLargeYTrunc c := by
  unfold absorbedKernelLargeY
  rw [Kernel.lintegral_piecewise]
  by_cases hc : c ∈ activeLargeY
  · rw [if_pos hc]
    calc ∫⁻ c', potentialLargeYTrunc c' ∂(transitionKernel hn c)
        ≤ ∫⁻ c', (c'.potentialLargeY : ℝ≥0∞) ∂(transitionKernel hn c) :=
          lintegral_mono (fun c' => potentialLargeYTrunc_le c')
      _ ≤ ENNReal.ofReal (1 - 13 / (64 * ((n : ℝ) - 1))) *
          (c.potentialLargeY : ℝ≥0∞) := by
          have hprob : IsProbabilityMeasure (transitionKernel hn c) :=
            (instIsMarkovKernel hn).isProbabilityMeasure c
          exact lintegral_natCast_le_of_integral_le
            (transitionKernel hn c) Config.potentialLargeY _ (contraction_rate_nonneg hn) c
            (integrable_potentialLargeY c hn)
            (expected_potentialLargeY_le c hc.1 hn hc.2)
      _ = ENNReal.ofReal (1 - 13 / (64 * ((n : ℝ) - 1))) *
          potentialLargeYTrunc c := by
          congr 1; exact (show potentialLargeYTrunc c =
            (c.potentialLargeY : ℝ≥0∞) from if_pos hc).symm
  · rw [if_neg hc, Kernel.id_apply,
        lintegral_dirac' c potentialLargeYTrunc_measurable]
    simp [potentialLargeYTrunc, hc]

theorem prob_in_activeLargeY_le (hn : n ≥ 2) (c₀ : Config n) (t : ℕ) :
    (absorbedKernelLargeY hn ^ t) c₀ activeLargeY ≤
    ENNReal.ofReal ((1 - 13 / (64 * ((n : ℝ) - 1))) ^ t) *
    potentialLargeYTrunc c₀ := by
  rw [activeLargeY_eq_ge_one]
  have h := measure_potential_ge_one
    (absorbedKernelLargeY hn) potentialLargeYTrunc potentialLargeYTrunc_measurable
    (ENNReal.ofReal (1 - 13 / (64 * ((n : ℝ) - 1))))
    (absorbed_drift_largeY hn) t c₀
  rw [ENNReal.ofReal_pow (contraction_rate_nonneg hn)]
  exact h

/-! ### Large-b region

In the large-b corner (b ≥ 7n/8), v = x+y increases multiplicatively:
`E[v'] ≥ (1 + 13/(16(n-1))) · v`. The natural potential is `1/v`, which
decreases multiplicatively. Since `1/v` is not ℕ-valued, we work directly
with the ℝ≥0∞-valued potential `(v : ℝ≥0∞)⁻¹`.

The drift computation for `1/v` requires a new algebraic argument:
  E[Δ(1/v)] = [-b/(v+1) + 2xy/(v(v-1))] / totalPairs

In large-b, `b ≥ 7v` and `xy ≤ v²/4`, so the negative term dominates. -/

/-- The active large-b region: b ≥ 7n/8 AND v ≥ 1 (at least one non-blank). -/
def activeLargeB : Set (Config n) :=
  {c | c.inLargeB ∧ c.v ≥ 1}

private theorem activeLargeB_measurableSet :
    MeasurableSet (activeLargeB : Set (Config n)) :=
  instDiscreteMeasurableSpaceConfig.forall_measurableSet _

/-- Absorbed kernel for large-b: transitions normally inside the active
    region, stays put (absorbs) outside. -/
noncomputable def absorbedKernelLargeB (hn : n ≥ 2) :
    Kernel (Config n) (Config n) :=
  Kernel.piecewise activeLargeB_measurableSet (transitionKernel hn) Kernel.id

instance instIsMarkovAbsorbedLargeB (hn : n ≥ 2) :
    IsMarkovKernel (absorbedKernelLargeB hn) := by
  unfold absorbedKernelLargeB
  have := instIsMarkovKernel hn
  infer_instance

theorem absorbedKernelLargeB_pow_eq_dirac_of_not_mem
    (hn : n ≥ 2) (c : Config n) (hc : c ∉ activeLargeB) (t : ℕ) :
    (absorbedKernelLargeB hn ^ t) c = Measure.dirac c := by
  unfold absorbedKernelLargeB
  exact absorbedKernel_pow_eq_dirac_of_not_mem activeLargeB_measurableSet
    (transitionKernel hn) c hc t

theorem absorbedKernelLargeB_active_eq_zero_of_not_mem
    (hn : n ≥ 2) (c : Config n) (hc : c ∉ activeLargeB) (t : ℕ) :
    (absorbedKernelLargeB hn ^ t) c activeLargeB = 0 := by
  rw [absorbedKernelLargeB_pow_eq_dirac_of_not_mem hn c hc t,
    Measure.dirac_apply' _ activeLargeB_measurableSet]
  simp [hc]

/-- **Potential for large-b**: `n/v` as an ℝ≥0∞-valued function,
    zero outside the active region.
    In activeLargeB, `v ≤ n` so `n/v ≥ 1`, enabling the Markov trick. -/
noncomputable def potentialLargeBTrunc (c : Config n) : ℝ≥0∞ :=
  if c ∈ activeLargeB then (n : ℝ≥0∞) * (c.v : ℝ≥0∞)⁻¹ else 0

private theorem potentialLargeBTrunc_measurable :
    Measurable (potentialLargeBTrunc : Config n → ℝ≥0∞) :=
  measurable_ennreal _

/-- The active large-b region equals `{c | 1 ≤ potentialLargeBTrunc c}`.
    This holds because `v ≤ n` implies `n/v ≥ 1`. -/
theorem activeLargeB_eq_ge_one :
    (activeLargeB : Set (Config n)) =
    {c | 1 ≤ potentialLargeBTrunc c} := by
  ext c
  simp only [Set.mem_setOf_eq, activeLargeB, potentialLargeBTrunc]
  constructor
  · intro hc
    rw [if_pos hc]
    have hv_pos : (0 : ℝ≥0∞) < (c.v : ℝ≥0∞) := by
      exact_mod_cast (show 0 < c.v from by obtain ⟨_, hv⟩ := hc; omega)
    have hv_le_n : c.v ≤ n := by unfold v; have := c.sum_eq; omega
    calc (1 : ℝ≥0∞) = (c.v : ℝ≥0∞) * (c.v : ℝ≥0∞)⁻¹ :=
          (ENNReal.mul_inv_cancel hv_pos.ne' (ENNReal.natCast_ne_top c.v)).symm
      _ ≤ (n : ℝ≥0∞) * (c.v : ℝ≥0∞)⁻¹ := by
          exact mul_le_mul_right' (by exact_mod_cast hv_le_n) _
  · intro hc
    by_contra hc'
    simp [if_neg hc'] at hc

/-! ### Weighted 1/v sum helpers -/

private lemma sum_state_expand' {α : Type*} [AddCommMonoid α] (f : State → α) :
    Finset.univ.sum f = f .x + f .b + f .y := by
  rw [show (Finset.univ : Finset State) = {.x, .b, .y} from by
    ext s; simp [Finset.mem_univ]; cases s <;> simp]
  rw [Finset.sum_insert (show State.x ∉ ({.b, .y} : Finset State) from by decide),
      Finset.sum_insert (show State.b ∉ ({.y} : Finset State) from by decide),
      Finset.sum_singleton]; abel

private theorem inv_v_xb' (c : Config n) :
    (c.interactionCount .x .b : ℝ) * ((c.stepOrSelf .x .b).v : ℝ)⁻¹ =
    ↑c.x_count * ↑c.b_count * ((c.v : ℝ) + 1)⁻¹ := by
  unfold interactionCount countOf stepOrSelf step v
  simp only [show (State.x : State) ≠ .b from by decide, ite_false]
  split_ifs with h
  · simp only [Option.getD_some]; push_cast; congr 1; ring
  · simp only [Option.getD_none]
    have : c.x_count = 0 ∨ c.b_count = 0 := by push_neg at h; omega
    rcases this with h | h <;> simp [h]

private theorem inv_v_yb' (c : Config n) :
    (c.interactionCount .y .b : ℝ) * ((c.stepOrSelf .y .b).v : ℝ)⁻¹ =
    ↑c.y_count * ↑c.b_count * ((c.v : ℝ) + 1)⁻¹ := by
  unfold interactionCount countOf stepOrSelf step v
  simp only [show (State.y : State) ≠ .b from by decide, ite_false]
  split_ifs with h
  · simp only [Option.getD_some]; push_cast; congr 1; ring
  · simp only [Option.getD_none]
    have : c.y_count = 0 ∨ c.b_count = 0 := by push_neg at h; omega
    rcases this with h | h <;> simp [h]

private theorem inv_v_xy' (c : Config n) :
    (c.interactionCount .x .y : ℝ) * ((c.stepOrSelf .x .y).v : ℝ)⁻¹ =
    ↑c.x_count * ↑c.y_count * ((c.v : ℝ) - 1)⁻¹ := by
  unfold interactionCount countOf stepOrSelf step v
  simp only [show (State.x : State) ≠ .y from by decide, ite_false]
  split_ifs with h
  · obtain ⟨_, hy⟩ := h
    simp only [Option.getD_some]; push_cast; rw [Nat.cast_sub hy]
    congr 1; congr 1; ring
  · simp only [Option.getD_none]
    have : c.x_count = 0 ∨ c.y_count = 0 := by push_neg at h; omega
    rcases this with h | h <;> simp [h]

private theorem inv_v_yx' (c : Config n) :
    (c.interactionCount .y .x : ℝ) * ((c.stepOrSelf .y .x).v : ℝ)⁻¹ =
    ↑c.y_count * ↑c.x_count * ((c.v : ℝ) - 1)⁻¹ := by
  unfold interactionCount countOf stepOrSelf step v
  simp only [show (State.y : State) ≠ .x from by decide, ite_false]
  split_ifs with h
  · obtain ⟨_, hx⟩ := h
    simp only [Option.getD_some]; push_cast; rw [Nat.cast_sub hx]
    congr 1; congr 1; ring
  · simp only [Option.getD_none]
    have : c.y_count = 0 ∨ c.x_count = 0 := by push_neg at h; omega
    rcases this with h | h <;> simp [h]

/-! ### Helpers for 1/v drift bound -/

/-- v ≥ 1 is preserved by `stepOrSelf`: the only v-decreasing interactions (xy, yx)
    need x ≥ 1 ∧ y ≥ 1, implying v ≥ 2, so v' = v-1 ≥ 1. -/
private theorem v_ge_one_after_step (c : Config n) (hv : c.v ≥ 1)
    (s₁ s₂ : State) : (c.stepOrSelf s₁ s₂).v ≥ 1 := by
  unfold v at hv ⊢
  unfold stepOrSelf step
  have hs := c.sum_eq
  cases s₁ <;> cases s₂ <;> simp only [] <;> split_ifs <;>
    simp only [Option.getD, Config.x_count, Config.y_count] <;> omega

/-- `(k : ℝ≥0∞)⁻¹ = ENNReal.ofReal ((k : ℝ)⁻¹)` for k ≥ 1. -/
private theorem ennreal_inv_natCast_eq_ofReal (k : ℕ) (hk : k ≥ 1) :
    (k : ℝ≥0∞)⁻¹ = ENNReal.ofReal ((k : ℝ)⁻¹) := by
  rw [ENNReal.ofReal_inv_of_pos (Nat.cast_pos.mpr (by omega : 0 < k)),
      ENNReal.ofReal_natCast]

/-- 1/(v:ℝ) is bounded by 1, hence integrable over any probability measure. -/
private theorem integrable_inv_v (c : Config n) (hn : n ≥ 2) :
    Integrable (fun c' : Config n => (c'.v : ℝ)⁻¹) (transitionKernel hn c) := by
  have := (instIsMarkovKernel hn).isProbabilityMeasure c
  exact Integrable.of_bound (measurable_real _).aestronglyMeasurable (1 : ℝ)
    (ae_of_all _ fun c' => by
      rw [Real.norm_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))]
      rcases Nat.eq_zero_or_pos c'.v with h | h
      · simp [h]
      · have hpos' : (0 : ℝ) < ↑c'.v := Nat.cast_pos.mpr h
        rw [inv_eq_one_div, div_le_one hpos']
        exact_mod_cast h)

/-- v(stepOrSelf) ≥ 1 a.e. under the transition kernel, for c with v ≥ 1.
    This follows from `v_ge_one_after_step` and the PMF structure:
    transitionKernel = (PMF.map g pmf).toMeasure = Measure.map g (pmf.toMeasure). -/
private theorem ae_v_ge_one (c : Config n) (hn : n ≥ 2)
    (hv : c.v ≥ 1) :
    ∀ᵐ c' ∂(transitionKernel hn c), c'.v ≥ 1 := by
  -- transitionKernel hn c = (c.stepDist hn).toMeasure definitionally
  have hk : transitionKernel hn c = (c.stepDist hn).toMeasure := rfl
  rw [hk]
  set g : State × State → Config n := fun p => c.stepOrSelf p.1 p.2
  have hg : Measurable g := fun _ _ => DiscreteMeasurableSpace.forall_measurableSet _
  rw [show c.stepDist hn = PMF.map g (c.interactionPMF hn) from rfl,
      ← PMF.toMeasure_map g _ hg]
  rw [ae_map_iff hg.aemeasurable
      (DiscreteMeasurableSpace.forall_measurableSet _)]
  exact ae_of_all _ fun p => v_ge_one_after_step c hv p.1 p.2

-- v-preservation lemmas: stepOrSelf returns c for 5 interaction types
private theorem stepOrSelf_xx' (c : Config n) : c.stepOrSelf .x .x = c := by
  unfold stepOrSelf step; split_ifs <;> simp
private theorem stepOrSelf_bb' (c : Config n) : c.stepOrSelf .b .b = c := by
  unfold stepOrSelf step; split_ifs <;> simp
private theorem stepOrSelf_yy' (c : Config n) : c.stepOrSelf .y .y = c := by
  unfold stepOrSelf step; split_ifs <;> simp
private theorem stepOrSelf_bx' (c : Config n) : c.stepOrSelf .b .x = c := by
  unfold stepOrSelf step; split_ifs <;> simp
private theorem stepOrSelf_by'' (c : Config n) : c.stepOrSelf .b .y = c := by
  unfold stepOrSelf step; split_ifs <;> simp

/-- **Bochner integral bound for 1/v** (ℝ version, v ≥ 2):
    `∫ (v':ℝ)⁻¹ ≤ (1 - 5/(16(n-1))) / v ≤ r / v`.
    Proof: `integral = (weighted_sum) / T`, multiply by `T·v·(v+1)·(v-1)` to
    clear all denominators, giving an integer inequality that follows from
    `large_b_reciprocal_drift`. -/
private theorem bochner_inv_v_le (c : Config n) (hn : n ≥ 2)
    (hc : c ∈ activeLargeB) :
    ∫ c', (c'.v : ℝ)⁻¹ ∂(c.stepDist hn).toMeasure ≤
    (1 - 13 / (64 * ((n : ℝ) - 1))) * (c.v : ℝ)⁻¹ := by
  obtain ⟨hb, hv1⟩ := hc
  -- Use integral_stepDist_eq_weighted_div: ∫ f = [Σ count * f(step)] / T
  rw [integral_stepDist_eq_weighted_div]
  -- Positivity/nonzero facts
  have hT_pos : (0 : ℝ) < (totalPairs n : ℝ) := by exact_mod_cast totalPairs_pos hn
  have hT_ne : (totalPairs n : ℝ) ≠ 0 := ne_of_gt hT_pos
  have hv_pos : (0 : ℝ) < (c.v : ℝ) := Nat.cast_pos.mpr (by omega)
  have hv_ne : (c.v : ℝ) ≠ 0 := ne_of_gt hv_pos
  have hn1_pos : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  -- Reduce to integer inequality via clearing denominators.
  -- Goal: [Σ count * (v':ℝ)⁻¹] / T ≤ (1 - 13/(64(n-1))) * v⁻¹
  -- ⟺ [Σ count * (v':ℝ)⁻¹] * v ≤ (1 - 13/(64(n-1))) * T  [mult by T*v/T]
  -- For all interactions: count * v/v' ≤ count (since v/v' ≤ 1 for v'≥v, but not for v'=v-1)
  -- We use the Bochner integral of (v * (v':ℝ)⁻¹) = v/v' and relate to drift of v
  --
  -- Instead we verify the bound computationally: reduce to large_b_reciprocal_drift.
  -- The weighted sum Σ count * (v':ℝ)⁻¹ is a Finset sum over State × State.
  -- We unfold it into 9 terms and clear denominators.
  --
  -- For brevity, we use `suffices` to reduce to a pure ℤ inequality.
  suffices h : ∀ (x y b : ℕ) (v : ℕ) (hsum : x + b + y = n),
      8 * b ≥ 7 * n → v = x + y → v ≥ 1 →
      (∑ p : State × State,
        (Config.interactionCount ⟨x, b, y, hsum⟩ p.1 p.2 : ℝ) *
        ((Config.stepOrSelf ⟨x, b, y, hsum⟩ p.1 p.2).v : ℝ)⁻¹) /
        (totalPairs n : ℝ) ≤
      (1 - 13 / (64 * ((n : ℝ) - 1))) * (v : ℝ)⁻¹ by
    exact h c.x_count c.y_count c.b_count c.v c.sum_eq
      (by exact_mod_cast hb) rfl (by omega)
  intro x y b v hsum hb_large hv_eq hv_pos
  have hn2 : n ≥ 2 := by omega
  set c : Config n := ⟨x, b, y, hsum⟩
  have hcv : c.v = v := hv_eq ▸ rfl
  -- Positivity facts
  have hv_pos_r : (0 : ℝ) < ↑v := Nat.cast_pos.mpr (by omega)
  have hv_ne : (↑v : ℝ) ≠ 0 := ne_of_gt hv_pos_r
  have hv1p : (0 : ℝ) < (↑v : ℝ) + 1 := by linarith
  have hv1ne : (↑v : ℝ) + 1 ≠ 0 := ne_of_gt hv1p
  have hTp : (0 : ℝ) < ↑(totalPairs n) := by exact_mod_cast totalPairs_pos hn2
  have hTne : (↑(totalPairs n) : ℝ) ≠ 0 := ne_of_gt hTp
  have hn1p : (0 : ℝ) < (↑n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ ↑n := by exact_mod_cast hn2
    linarith
  have hn1ne : (↑n : ℝ) - 1 ≠ 0 := ne_of_gt hn1p
  -- Step 1: Expand the Finset sum to 9 explicit terms
  rw [show (Finset.univ : Finset (State × State)) = Finset.univ ×ˢ Finset.univ
      from Finset.univ_product_univ.symm, Finset.sum_product]
  simp only [sum_state_expand']
  -- Step 2: Rewrite v-changing terms using helper lemmas
  rw [inv_v_xb' c, inv_v_yb' c, inv_v_xy' c, inv_v_yx' c]
  -- Step 3: Simplify v-preserving terms using external lemmas
  simp only [stepOrSelf_xx', stepOrSelf_bb', stepOrSelf_yy', stepOrSelf_bx', stepOrSelf_by'',
    hcv, show c.x_count = x from rfl, show c.b_count = b from rfl,
    show c.y_count = y from rfl]
  -- Step 4: Unfold interactionCount for the 5 v-preserving terms
  simp only [interactionCount, countOf,
    if_pos (show State.x = State.x from rfl),
    if_pos (show State.b = State.b from rfl),
    if_pos (show State.y = State.y from rfl),
    if_neg (show State.b ≠ State.x from fun h => State.noConfusion h),
    if_neg (show State.b ≠ State.y from fun h => State.noConfusion h),
    ite_true, ite_false]
  -- Step 5: Re-substitute field names after countOf expansion
  simp only [show c.x_count = x from rfl, show c.b_count = b from rfl,
    show c.y_count = y from rfl]
  -- Case split: v = 1 or v ≥ 2
  by_cases hv1 : v = 1
  · -- Case v = 1: x * y = 0 by large_b_reciprocal_drift_v1
    have hxy0 : x * y = 0 :=
      large_b_reciprocal_drift_v1 c (show c.inLargeB from hb_large) (by rw [hcv]; exact hv1)
    subst hv1
    rcases mul_eq_zero.mp hxy0 with hx0 | hy0
    · -- x = 0, y = 1
      have hy1 : y = 1 := by omega
      subst hx0; subst hy1
      simp only [Nat.zero_mul, Nat.mul_zero, Nat.cast_zero, zero_mul,
        mul_zero, zero_add, add_zero, Nat.cast_one, one_mul, mul_one,
        sub_self, inv_zero, inv_one]
      -- Goal: (↑(b*(b-1)) + ↑b + ↑b*(1+1)⁻¹) / ↑(totalPairs n) ≤ 1 - 13/(64*(↑n-1))
      have hb1 : 1 ≤ b := by omega
      have hn1 : 1 ≤ n := by omega
      have hbb : (↑(b * (b - 1)) : ℝ) = ↑b * (↑b - 1) := by
        rw [Nat.cast_mul, Nat.cast_sub hb1, Nat.cast_one]
      have hT : (↑(totalPairs n) : ℝ) = ↑n * (↑n - 1) := by
        unfold totalPairs; rw [Nat.cast_mul, Nat.cast_sub hn1, Nat.cast_one]
      rw [hbb, hT]
      have hb_eq : (↑b : ℝ) = ↑n - 1 := by
        rw [show b = n - 1 from by omega, Nat.cast_sub hn1, Nat.cast_one]
      rw [hb_eq]
      have hn_r : (↑n : ℝ) ≥ 2 := by exact_mod_cast hn2
      have hn_ne : (↑n : ℝ) ≠ 0 := by linarith
      have hn1_ne : (↑n : ℝ) - 1 ≠ 0 := by linarith
      field_simp [hn_ne, hn1_ne, show (1 + 1 : ℝ) ≠ 0 from by norm_num,
        show (64 : ℝ) ≠ 0 from by norm_num]
      simp only [show (1 - 1 : ℕ) = 0 from rfl, Nat.cast_zero, mul_zero, add_zero]
      nlinarith [sq_nonneg ((↑n : ℝ) - 2)]
    · -- y = 0, x = 1 (symmetric to above)
      have hx1 : x = 1 := by omega
      subst hy0; subst hx1
      simp only [Nat.mul_zero, Nat.zero_mul, Nat.cast_zero, zero_mul,
        mul_zero, zero_add, add_zero, Nat.cast_one, one_mul, mul_one,
        sub_self, inv_zero, inv_one]
      have hb1 : 1 ≤ b := by omega
      have hn1 : 1 ≤ n := by omega
      have hbb : (↑(b * (b - 1)) : ℝ) = ↑b * (↑b - 1) := by
        rw [Nat.cast_mul, Nat.cast_sub hb1, Nat.cast_one]
      have hT : (↑(totalPairs n) : ℝ) = ↑n * (↑n - 1) := by
        unfold totalPairs; rw [Nat.cast_mul, Nat.cast_sub hn1, Nat.cast_one]
      rw [hbb, hT]
      have hb_eq : (↑b : ℝ) = ↑n - 1 := by
        rw [show b = n - 1 from by omega, Nat.cast_sub hn1, Nat.cast_one]
      rw [hb_eq]
      have hn_r : (↑n : ℝ) ≥ 2 := by exact_mod_cast hn2
      have hn_ne : (↑n : ℝ) ≠ 0 := by linarith
      have hn1_ne : (↑n : ℝ) - 1 ≠ 0 := by linarith
      field_simp [hn_ne, hn1_ne, show (1 + 1 : ℝ) ≠ 0 from by norm_num,
        show (64 : ℝ) ≠ 0 from by norm_num]
      simp only [show (1 - 1 : ℕ) = 0 from rfl, Nat.cast_zero, mul_zero, add_zero]
      nlinarith [sq_nonneg ((↑n : ℝ) - 2)]
  · -- Case v ≥ 2: use large_b_reciprocal_drift
    have hv2 : v ≥ 2 := by omega
    have hvm1p : (0 : ℝ) < (↑v : ℝ) - 1 := by
      have : (2 : ℝ) ≤ ↑v := by exact_mod_cast hv2
      linarith
    have hvm1ne : (↑v : ℝ) - 1 ≠ 0 := ne_of_gt hvm1p
    -- Cast helper for a*(a-1) → ↑a*(↑a-1), handling a=0 case
    have cast_pred : ∀ (a : ℕ), (↑(a * (a - 1)) : ℝ) = ↑a * (↑a - 1) := by
      intro a; rcases Nat.eq_zero_or_pos a with rfl | ha
      · simp
      · rw [Nat.cast_mul, Nat.cast_sub ha, Nat.cast_one]
    rw [cast_pred x, cast_pred b, cast_pred y,
        show (↑(b * x) : ℝ) = ↑b * ↑x from by push_cast; ring,
        show (↑(b * y) : ℝ) = ↑b * ↑y from by push_cast; ring,
        show (↑(totalPairs n) : ℝ) = ↑n * (↑n - 1) from by
          unfold totalPairs; rw [Nat.cast_mul, Nat.cast_sub (show 1 ≤ n from by omega),
            Nat.cast_one]]
    -- The key integer bound from Drift.lean
    have hdrift := large_b_reciprocal_drift c (show c.inLargeB from hb_large)
      (show c.v ≥ 2 by rw [hcv]; exact hv2)
    simp only [show c.b_count = b from rfl, show c.x_count = x from rfl,
      show c.y_count = y from rfl, hcv] at hdrift
    -- Cast the ℤ drift bound to ℝ
    have hdrift_r : 16 * ((↑b : ℝ) * ↑v * (↑v - 1) - 2 * ↑x * ↑y * (↑v + 1)) ≥
        5 * ↑n * (↑v ^ 2 - 1) := by exact_mod_cast hdrift
    have hxyn : (↑x : ℝ) + ↑y = ↑v := by exact_mod_cast hv_eq.symm
    have hsum_r : (↑x : ℝ) + ↑b + ↑y = ↑n := by exact_mod_cast hsum
    have hn_r : (↑n : ℝ) ≥ 2 := by exact_mod_cast hn2
    -- Eliminate ↑y and ↑b in terms of ↑x, ↑v, ↑n
    have hy_val : (↑y : ℝ) = ↑v - ↑x := by linarith [hxyn]
    have hb_val : (↑b : ℝ) = ↑n - ↑v := by linarith [hsum_r, hxyn]
    -- Drift in reduced variables
    have hdrift3 : 16 * ((↑n - ↑v) * ↑v * (↑v - 1) - 2 * ↑x * (↑v - ↑x) * (↑v + 1)) ≥
        5 * ↑n * ((↑v : ℝ) ^ 2 - 1) := by rw [← hb_val, ← hy_val]; exact hdrift_r
    -- Clear all denominators
    field_simp [hv_ne, hv1ne, hvm1ne,
      show (↑n : ℝ) ≠ 0 from by linarith,
      show (↑n : ℝ) - 1 ≠ 0 from by linarith,
      show (64 : ℝ) ≠ 0 from by norm_num]
    -- Substitute ↑y and ↑b to reduce polynomial variables
    rw [hy_val, hb_val]
    nlinarith [hdrift3,
      sq_nonneg (↑x : ℝ), sq_nonneg (↑v : ℝ), sq_nonneg (↑n : ℝ),
      sq_nonneg ((↑v : ℝ) - ↑x),
      Nat.cast_nonneg (α := ℝ) x, Nat.cast_nonneg (α := ℝ) v,
      Nat.cast_nonneg (α := ℝ) n,
      mul_pos hv_pos_r hvm1p]

/-! ### Absorbed drift for 1/v potential (large-b)

The key unconditional drift condition for the absorbed kernel.
Combines the Bochner integral bound (`bochner_inv_v_le`) with the
Bochner-to-Lebesgue bridge (`ofReal_integral_eq_lintegral_ofReal`). -/

/-- The core 1/v drift computation: E[1/v'] ≤ r · (1/v) under the
    transition kernel, for c in activeLargeB.
    Uses `large_b_reciprocal_drift` to bound the rational expectation. -/
private theorem lintegral_inv_v_le (c : Config n) (hn : n ≥ 2)
    (hc : c ∈ activeLargeB) :
    ∫⁻ c', (c'.v : ℝ≥0∞)⁻¹ ∂(transitionKernel hn c) ≤
    ENNReal.ofReal (1 - 13 / (64 * ((n : ℝ) - 1))) *
    (c.v : ℝ≥0∞)⁻¹ := by
  obtain ⟨hb, hv1⟩ := hc
  -- Key ingredients
  have hfi := integrable_inv_v c hn
  have hfnn : ∀ᵐ c' ∂(transitionKernel hn c), (0 : ℝ) ≤ (c'.v : ℝ)⁻¹ :=
    ae_of_all _ (fun c' => inv_nonneg.mpr (Nat.cast_nonneg _))
  -- a.e. equality: (v':ℝ≥0∞)⁻¹ = ofReal((v':ℝ)⁻¹) since v' ≥ 1 on support
  have hae : ∀ᵐ c' ∂(transitionKernel hn c),
      (c'.v : ℝ≥0∞)⁻¹ = ENNReal.ofReal ((c'.v : ℝ)⁻¹) :=
    (ae_v_ge_one c hn (by omega)).mono (fun c' hv =>
      ennreal_inv_natCast_eq_ofReal c'.v hv)
  -- Bridge: ∫⁻ (v')⁻¹ = ofReal(∫ (v':ℝ)⁻¹) ≤ ofReal(r * v⁻¹) = ofReal(r) * v⁻¹
  calc ∫⁻ c', (c'.v : ℝ≥0∞)⁻¹ ∂(transitionKernel hn c)
      = ∫⁻ c', ENNReal.ofReal ((c'.v : ℝ)⁻¹) ∂(transitionKernel hn c) :=
        lintegral_congr_ae hae
    _ = ENNReal.ofReal (∫ c', (c'.v : ℝ)⁻¹ ∂(transitionKernel hn c)) :=
        (ofReal_integral_eq_lintegral_ofReal hfi hfnn).symm
    _ ≤ ENNReal.ofReal ((1 - 13 / (64 * ((n : ℝ) - 1))) * (c.v : ℝ)⁻¹) :=
        ENNReal.ofReal_le_ofReal (bochner_inv_v_le c hn ⟨hb, hv1⟩)
    _ = ENNReal.ofReal (1 - 13 / (64 * ((n : ℝ) - 1))) * ENNReal.ofReal ((c.v : ℝ)⁻¹) :=
        ENNReal.ofReal_mul (contraction_rate_nonneg hn)
    _ = ENNReal.ofReal (1 - 13 / (64 * ((n : ℝ) - 1))) * (c.v : ℝ≥0∞)⁻¹ := by
        congr 1; exact (ennreal_inv_natCast_eq_ofReal c.v (by omega)).symm

theorem absorbed_drift_largeB (hn : n ≥ 2) (c : Config n) :
    ∫⁻ c', potentialLargeBTrunc c' ∂(absorbedKernelLargeB hn c) ≤
    ENNReal.ofReal (1 - 13 / (64 * ((n : ℝ) - 1))) *
    potentialLargeBTrunc c := by
  unfold absorbedKernelLargeB
  rw [Kernel.lintegral_piecewise]
  by_cases hc : c ∈ activeLargeB
  · -- Case: c is in the active large-b region
    rw [if_pos hc]
    -- Step 1: Φ̃(c') ≤ n · (v')⁻¹ for all c'
    calc ∫⁻ c', potentialLargeBTrunc c' ∂(transitionKernel hn c)
        ≤ ∫⁻ c', (n : ℝ≥0∞) * (c'.v : ℝ≥0∞)⁻¹ ∂(transitionKernel hn c) := by
          apply lintegral_mono; intro c'
          unfold potentialLargeBTrunc
          split_ifs with h
          · exact le_refl _
          · exact zero_le'
      -- Step 2: Factor out the constant n
      _ = (n : ℝ≥0∞) * ∫⁻ c', (c'.v : ℝ≥0∞)⁻¹ ∂(transitionKernel hn c) :=
          lintegral_const_mul _ (measurable_ennreal _)
      -- Step 3: Apply the 1/v drift bound
      _ ≤ (n : ℝ≥0∞) * (ENNReal.ofReal (1 - 13 / (64 * ((n : ℝ) - 1))) *
          (c.v : ℝ≥0∞)⁻¹) := by
          gcongr; exact lintegral_inv_v_le c hn hc
      -- Step 4: Commute to match the goal
      _ = ENNReal.ofReal (1 - 13 / (64 * ((n : ℝ) - 1))) *
          ((n : ℝ≥0∞) * (c.v : ℝ≥0∞)⁻¹) := by ring
      _ = ENNReal.ofReal (1 - 13 / (64 * ((n : ℝ) - 1))) *
          potentialLargeBTrunc c := by
          congr 1; exact (if_pos hc).symm
  · -- Case: c is NOT in the active region (absorbed)
    rw [if_neg hc, Kernel.id_apply,
        lintegral_dirac' c potentialLargeBTrunc_measurable]
    simp [potentialLargeBTrunc, hc]

/-- **Large-b tail bound**: The probability of remaining in the active
    large-b region for t steps under the absorbed kernel decays
    geometrically.

    Combines `absorbed_drift_largeB` with `measure_potential_ge_one`
    from GeometricDrift.lean. -/
theorem prob_in_activeLargeB_le (hn : n ≥ 2) (c₀ : Config n) (t : ℕ) :
    (absorbedKernelLargeB hn ^ t) c₀ activeLargeB ≤
    ENNReal.ofReal ((1 - 13 / (64 * ((n : ℝ) - 1))) ^ t) *
    potentialLargeBTrunc c₀ := by
  rw [activeLargeB_eq_ge_one]
  have h := measure_potential_ge_one
    (absorbedKernelLargeB hn) potentialLargeBTrunc potentialLargeBTrunc_measurable
    (ENNReal.ofReal (1 - 13 / (64 * ((n : ℝ) - 1))))
    (absorbed_drift_largeB hn) t c₀
  rw [ENNReal.ofReal_pow (contraction_rate_nonneg hn)]
  exact h

/-! ### Convergence from corners

Combining the tail bounds: starting from any corner region, the protocol
exits with geometrically decaying probability. The three corner bounds
give the main ingredient for Theorem 1. -/

/-- The protocol has reached x-consensus: all agents hold opinion x. -/
def reachedConsensusX (c : Config n) : Prop :=
  c.x_count = n

/-- The protocol has reached y-consensus: all agents hold opinion y. -/
def reachedConsensusY (c : Config n) : Prop :=
  c.y_count = n

/-- In the active large-x region, `potentialLargeX = 1` iff `y = 0 ∧ b = 0`,
    i.e., the protocol has reached x-consensus. So `activeLargeX` is
    exactly the set of large-x configurations that have NOT yet converged. -/
theorem activeLargeX_iff_not_consensusX (c : Config n)
    (hx : c.inLargeX) :
    c ∈ activeLargeX ↔ ¬c.reachedConsensusX := by
  constructor
  · intro ⟨_, hby⟩
    unfold reachedConsensusX
    have := c.sum_eq; omega
  · intro hne
    refine ⟨hx, ?_⟩
    unfold reachedConsensusX at hne
    have := c.sum_eq; omega

/-- Symmetric characterization of the active large-y region as the large-y
    corner with y-consensus removed. -/
theorem activeLargeY_iff_not_consensusY (c : Config n)
    (hy : c.inLargeY) :
    c ∈ activeLargeY ↔ ¬c.reachedConsensusY := by
  constructor
  · intro ⟨_, hbx⟩
    unfold reachedConsensusY
    have := c.sum_eq; omega
  · intro hne
    refine ⟨hy, ?_⟩
    unfold reachedConsensusY at hne
    have := c.sum_eq; omega

/-- **Convergence time from large-x corner (explicit bound)**:
    For any initial configuration c₀ in large-x, the probability of not
    having reached x-consensus after t steps of the absorbed kernel is
    at most `r^t · (3n/8 + 1)` where `r = 1 - 13/(64(n-1))`.

    To get P ≤ 1/n^k, choose `t ≥ (64(n-1)/13) · (k+1) · ln(n)`. -/
theorem convergence_time_largeX (hn : n ≥ 2) (c₀ : Config n)
    (hc₀ : c₀ ∈ activeLargeX) (t : ℕ) :
    (absorbedKernelLargeX hn ^ t) c₀ activeLargeX ≤
    ENNReal.ofReal ((1 - 13 / (64 * ((n : ℝ) - 1))) ^ t) *
    (c₀.potentialLargeX : ℝ≥0∞) := by
  have h := prob_in_activeLargeX_le hn c₀ t
  rwa [show potentialLargeXTrunc c₀ = (c₀.potentialLargeX : ℝ≥0∞) from
    if_pos hc₀] at h

/-- Symmetric: convergence time from large-y corner. -/
theorem convergence_time_largeY (hn : n ≥ 2) (c₀ : Config n)
    (hc₀ : c₀ ∈ activeLargeY) (t : ℕ) :
    (absorbedKernelLargeY hn ^ t) c₀ activeLargeY ≤
    ENNReal.ofReal ((1 - 13 / (64 * ((n : ℝ) - 1))) ^ t) *
    (c₀.potentialLargeY : ℝ≥0∞) := by
  have h := prob_in_activeLargeY_le hn c₀ t
  rwa [show potentialLargeYTrunc c₀ = (c₀.potentialLargeY : ℝ≥0∞) from
    if_pos hc₀] at h

/-- Convergence-time wrapper for the large-b corner with the truncated
    reciprocal potential unfolded at an active initial configuration. -/
theorem convergence_time_largeB (hn : n ≥ 2) (c₀ : Config n)
    (hc₀ : c₀ ∈ activeLargeB) (t : ℕ) :
    (absorbedKernelLargeB hn ^ t) c₀ activeLargeB ≤
    ENNReal.ofReal ((1 - 13 / (64 * ((n : ℝ) - 1))) ^ t) *
    ((n : ℝ≥0∞) * (c₀.v : ℝ≥0∞)⁻¹) := by
  have h := prob_in_activeLargeB_le hn c₀ t
  rwa [show potentialLargeBTrunc c₀ =
      (n : ℝ≥0∞) * (c₀.v : ℝ≥0∞)⁻¹ from if_pos hc₀] at h

/-- **Initial potential bound (large-x)**: When starting in the active
    large-x region, `potentialLargeX ≤ 3(n/8) + n/8 + 1`. This bounds
    the constant factor in the geometric tail. -/
theorem initial_potential_largeX (c₀ : Config n) (hc₀ : c₀ ∈ activeLargeX) :
    (c₀.potentialLargeX : ℝ≥0∞) ≤ (3 * (n / 8) + n / 8 + 1 : ℕ) := by
  exact_mod_cast potentialLargeX_bound c₀ hc₀.1

/-! ### Central region

In the central region (no count ≥ 7n/8), the potential function is
`f = u² + 2n` (`Config.potential`). The reciprocal potential `(n²+2n)/f`
is ≥ 1 in this region (since `f ≤ n²+2n`, with equality only at consensus
which lies in `inLargeX` or `inLargeY`, not `inCentral`).

Each interaction changes `u` by ±1 or 0, so `f` changes by `±2u+1` or 0.
In the central region, the expected relative change `E[Δf/f']` is positive
and bounded below by `Ω(1/n)`, driven by:
- vb interactions: `E[Δf | I^vb] / f = (2u²+v)/(vf) ≥ 7/(16n)` (Lemma 2)
- xy interactions: `E[Δf | I^xy] / f = 1/f` (positive)

The reciprocal `1/f` therefore decreases multiplicatively, yielding a
geometric tail bound for the time to exit the central region. -/

/-- The active central region: in the central region with at least one
    opinionated agent. For `n ≥ 2`, `inCentral` implies `v > n/8 ≥ 1`,
    so the second condition is automatic. -/
def activeCentral : Set (Config n) :=
  {c | c.inCentral ∧ c.v ≥ 1}

private theorem activeCentral_measurableSet :
    MeasurableSet (activeCentral : Set (Config n)) :=
  instDiscreteMeasurableSpaceConfig.forall_measurableSet _

/-- Every non-consensus configuration with at least one opinionated agent lies
    in one of the four active regions used by the regional tail bounds.

This is the deterministic coverage step needed before applying a union bound:
large-x and large-y consensus points are removed from their active regions, and
the all-blank large-b point is removed by the `hasOpinion` hypothesis. -/
theorem nonconsensus_mem_activeRegion (hn : n ≥ 2) (c : Config n)
    (hop : c.hasOpinion) (hnot : ¬ c.isConsensus) :
    c ∈ (activeCentral : Set (Config n)) ∨
    c ∈ (activeLargeB : Set (Config n)) ∨
    c ∈ (activeLargeX : Set (Config n)) ∨
    c ∈ (activeLargeY : Set (Config n)) := by
  rcases region_classification c hn with hcentral | hlargeB | hlargeX | hlargeY
  · left
    unfold activeCentral
    exact ⟨hcentral, by
      exact Nat.succ_le_of_lt (central_v_pos c hcentral (by omega))⟩
  · by_cases hv : c.v ≥ 1
    · right; left
      unfold activeLargeB
      exact ⟨hlargeB, hv⟩
    · exfalso
      have hv0 : c.v = 0 := by omega
      unfold hasOpinion opinionated at hop
      unfold v at hv0
      omega
  · by_cases hby : c.b_count + c.y_count ≥ 1
    · right; right; left
      unfold activeLargeX
      exact ⟨hlargeX, hby⟩
    · exfalso
      apply hnot
      exact Or.inl (by
        unfold allX at *
        have := c.sum_eq
        omega)
  · by_cases hbx : c.b_count + c.x_count ≥ 1
    · right; right; right
      unfold activeLargeY
      exact ⟨hlargeY, hbx⟩
    · exfalso
      apply hnot
      exact Or.inr (by
        unfold allY at *
        have := c.sum_eq
        omega)

/-- The union of the four active regions used by the regional tail bounds. -/
def activeRegion : Set (Config n) :=
  ((activeCentral : Set (Config n)) ∪ activeLargeB ∪ activeLargeX) ∪ activeLargeY

theorem activeRegion_measurableSet : MeasurableSet (activeRegion : Set (Config n)) :=
  instDiscreteMeasurableSpaceConfig.forall_measurableSet _

/-- Set-valued form of `nonconsensus_mem_activeRegion`: every non-consensus
opinionated configuration lies in the union of the four active regions. -/
theorem nonconsensus_mem_activeRegion_set (hn : n ≥ 2) (c : Config n)
    (hop : c.hasOpinion) (hnot : ¬ c.isConsensus) :
    c ∈ (activeRegion : Set (Config n)) := by
  rcases nonconsensus_mem_activeRegion hn c hop hnot with hc | hb | hx | hy
  · exact Or.inl (Or.inl (Or.inl hc))
  · exact Or.inl (Or.inl (Or.inr hb))
  · exact Or.inl (Or.inr hx)
  · exact Or.inr hy

/-- Event-level coverage: the non-consensus opinionated event is contained in
the union of the four active regions. -/
theorem nonconsensus_opinionated_event_subset_activeRegion (hn : n ≥ 2) :
    {c : Config n | c.hasOpinion ∧ ¬c.isConsensus} ⊆
      (activeRegion : Set (Config n)) := by
  intro c hc
  exact nonconsensus_mem_activeRegion_set hn c hc.1 hc.2

/-- Union-bound interface for the four regional active events. -/
theorem measure_activeRegion_le_sum (μ : Measure (Config n)) :
    μ (activeRegion : Set (Config n)) ≤
      μ (activeCentral : Set (Config n)) + μ (activeLargeB : Set (Config n)) +
        μ (activeLargeX : Set (Config n)) + μ (activeLargeY : Set (Config n)) := by
  unfold activeRegion
  calc
    μ (((activeCentral : Set (Config n)) ∪ activeLargeB ∪ activeLargeX) ∪ activeLargeY)
        ≤ μ (((activeCentral : Set (Config n)) ∪ activeLargeB) ∪ activeLargeX) +
            μ (activeLargeY : Set (Config n)) := measure_union_le _ _
    _ ≤ (μ ((activeCentral : Set (Config n)) ∪ activeLargeB) +
            μ (activeLargeX : Set (Config n))) +
          μ (activeLargeY : Set (Config n)) := by
        gcongr
        exact measure_union_le _ _
    _ ≤ (μ (activeCentral : Set (Config n)) + μ (activeLargeB : Set (Config n)) +
            μ (activeLargeX : Set (Config n))) +
          μ (activeLargeY : Set (Config n)) := by
        gcongr
        exact measure_union_le _ _
    _ = μ (activeCentral : Set (Config n)) + μ (activeLargeB : Set (Config n)) +
          μ (activeLargeX : Set (Config n)) + μ (activeLargeY : Set (Config n)) := by
        rw [add_assoc]

/-- Probability of being both opinionated and non-consensus is bounded by the
sum of the four regional active-event probabilities. -/
theorem measure_nonconsensus_opinionated_le_region_sum
    (hn : n ≥ 2) (μ : Measure (Config n)) :
    μ {c : Config n | c.hasOpinion ∧ ¬c.isConsensus} ≤
      μ (activeCentral : Set (Config n)) + μ (activeLargeB : Set (Config n)) +
        μ (activeLargeX : Set (Config n)) + μ (activeLargeY : Set (Config n)) := by
  exact (measure_mono (nonconsensus_opinionated_event_subset_activeRegion hn)).trans
    (measure_activeRegion_le_sum μ)

/-- Original-chain union-bound interface. From an opinionated initial
configuration, the event of still being non-consensus after `t` steps is
bounded by the four active-region events at that same time. The all-blank
failure mode has zero mass by finite-step opinion preservation. -/
theorem transitionKernel_pow_nonconsensus_le_region_sum
    (hn : n ≥ 2) (c₀ : Config n) (hop : c₀.hasOpinion) (t : ℕ) :
    (transitionKernel hn ^ t) c₀ {c : Config n | ¬c.isConsensus} ≤
      (transitionKernel hn ^ t) c₀ (activeCentral : Set (Config n)) +
      (transitionKernel hn ^ t) c₀ (activeLargeB : Set (Config n)) +
      (transitionKernel hn ^ t) c₀ (activeLargeX : Set (Config n)) +
      (transitionKernel hn ^ t) c₀ (activeLargeY : Set (Config n)) := by
  let μ : Measure (Config n) := (transitionKernel hn ^ t) c₀
  have hnoOpinion :
      μ {c : Config n | ¬c.hasOpinion} = 0 :=
    transitionKernel_pow_not_hasOpinion_eq_zero c₀ hn hop t
  have hsubset :
      {c : Config n | ¬c.isConsensus} ⊆
        {c : Config n | c.hasOpinion ∧ ¬c.isConsensus} ∪
          {c : Config n | ¬c.hasOpinion} := by
    intro c hc
    by_cases hopc : c.hasOpinion
    · exact Or.inl ⟨hopc, hc⟩
    · exact Or.inr hopc
  calc
    μ {c : Config n | ¬c.isConsensus}
        ≤ μ ({c : Config n | c.hasOpinion ∧ ¬c.isConsensus} ∪
            {c : Config n | ¬c.hasOpinion}) := measure_mono hsubset
    _ ≤ μ {c : Config n | c.hasOpinion ∧ ¬c.isConsensus} +
          μ {c : Config n | ¬c.hasOpinion} := measure_union_le _ _
    _ = μ {c : Config n | c.hasOpinion ∧ ¬c.isConsensus} := by
        rw [hnoOpinion, add_zero]
    _ ≤ μ (activeCentral : Set (Config n)) + μ (activeLargeB : Set (Config n)) +
          μ (activeLargeX : Set (Config n)) + μ (activeLargeY : Set (Config n)) :=
        measure_nonconsensus_opinionated_le_region_sum hn μ

/-- A two-opinion initial configuration lies in the union of the active
regions used by the regional convergence bounds. -/
theorem initial_mem_activeRegion_of_pos_lt
    (hn : n ≥ 2) {a : ℕ} (h : a ≤ n) (ha_pos : 0 < a) (ha_lt : a < n) :
    Config.initial n a h ∈ (activeRegion : Set (Config n)) := by
  exact nonconsensus_mem_activeRegion_set hn (Config.initial n a h)
    (initial_hasOpinion h (by omega))
    (initial_not_isConsensus_of_pos_lt h ha_pos ha_lt)

/-- Initial-state specialization of the original-chain union-bound interface:
after `t` interactions from a two-opinion initial configuration, the
non-consensus probability is bounded by the sum of the four regional active
probabilities. -/
theorem initial_transitionKernel_pow_nonconsensus_le_region_sum
    (hn : n ≥ 2) {a : ℕ} (h : a ≤ n) (ha_pos : 0 < a) (ha_lt : a < n)
    (t : ℕ) :
    (transitionKernel hn ^ t) (Config.initial n a h)
        {c : Config n | ¬c.isConsensus} ≤
      (transitionKernel hn ^ t) (Config.initial n a h)
          (activeCentral : Set (Config n)) +
      (transitionKernel hn ^ t) (Config.initial n a h)
          (activeLargeB : Set (Config n)) +
      (transitionKernel hn ^ t) (Config.initial n a h)
          (activeLargeX : Set (Config n)) +
      (transitionKernel hn ^ t) (Config.initial n a h)
          (activeLargeY : Set (Config n)) := by
  have _ : Config.initial n a h ∈ (activeRegion : Set (Config n)) :=
    initial_mem_activeRegion_of_pos_lt hn h ha_pos ha_lt
  exact transitionKernel_pow_nonconsensus_le_region_sum hn (Config.initial n a h)
    (initial_hasOpinion h (by omega)) t

/-- Boundary initial configurations (`a = 0` or `a = n`) are already
consensus, hence the original chain stays at the same point for any finite
number of interactions. -/
theorem initial_consensus_transitionKernel_pow_eq_dirac
    (hn : n ≥ 2) {a : ℕ} (h : a ≤ n) (ha : a = n ∨ a = 0) (t : ℕ) :
    (transitionKernel hn ^ t) (Config.initial n a h) =
      Measure.dirac (Config.initial n a h) := by
  exact consensus_transitionKernel_pow_eq_dirac (Config.initial n a h) hn
    ((initial_isConsensus_iff h).2 ha) t

/-- Boundary initial configurations have zero probability of being
non-consensus after any finite number of interactions. -/
theorem initial_consensus_transitionKernel_pow_nonconsensus_eq_zero
    (hn : n ≥ 2) {a : ℕ} (h : a ≤ n) (ha : a = n ∨ a = 0) (t : ℕ) :
    (transitionKernel hn ^ t) (Config.initial n a h)
        {c : Config n | ¬c.isConsensus} = 0 := by
  have hc : (Config.initial n a h).isConsensus :=
    (initial_isConsensus_iff h).2 ha
  rw [initial_consensus_transitionKernel_pow_eq_dirac hn h ha t,
    Measure.dirac_apply' _
      (instDiscreteMeasurableSpaceConfig.forall_measurableSet _)]
  simp [hc]

/-- Global initial-state union-bound interface. For every initial split `a`,
including the two already-consensus boundary cases, the probability of being
non-consensus after `t` interactions is bounded by the sum of the four active
regional probabilities at that time. -/
theorem initial_transitionKernel_pow_nonconsensus_le_region_sum_all
    (hn : n ≥ 2) {a : ℕ} (h : a ≤ n) (t : ℕ) :
    (transitionKernel hn ^ t) (Config.initial n a h)
        {c : Config n | ¬c.isConsensus} ≤
      (transitionKernel hn ^ t) (Config.initial n a h)
          (activeCentral : Set (Config n)) +
      (transitionKernel hn ^ t) (Config.initial n a h)
          (activeLargeB : Set (Config n)) +
      (transitionKernel hn ^ t) (Config.initial n a h)
          (activeLargeX : Set (Config n)) +
      (transitionKernel hn ^ t) (Config.initial n a h)
          (activeLargeY : Set (Config n)) := by
  by_cases ha0 : a = 0
  · rw [initial_consensus_transitionKernel_pow_nonconsensus_eq_zero
      hn h (Or.inr ha0) t]
    exact zero_le'
  · by_cases han : a = n
    · rw [initial_consensus_transitionKernel_pow_nonconsensus_eq_zero
        hn h (Or.inl han) t]
      exact zero_le'
    · exact initial_transitionKernel_pow_nonconsensus_le_region_sum
        hn h (by omega) (by omega) t

/-- Absorbed kernel for the central region. -/
noncomputable def absorbedKernelCentral (hn : n ≥ 2) :
    Kernel (Config n) (Config n) :=
  Kernel.piecewise activeCentral_measurableSet (transitionKernel hn) Kernel.id

instance instIsMarkovAbsorbedCentral (hn : n ≥ 2) :
    IsMarkovKernel (absorbedKernelCentral hn) := by
  unfold absorbedKernelCentral
  have := instIsMarkovKernel hn
  infer_instance

theorem absorbedKernelCentral_pow_eq_dirac_of_not_mem
    (hn : n ≥ 2) (c : Config n) (hc : c ∉ activeCentral) (t : ℕ) :
    (absorbedKernelCentral hn ^ t) c = Measure.dirac c := by
  unfold absorbedKernelCentral
  exact absorbedKernel_pow_eq_dirac_of_not_mem activeCentral_measurableSet
    (transitionKernel hn) c hc t

theorem absorbedKernelCentral_active_eq_zero_of_not_mem
    (hn : n ≥ 2) (c : Config n) (hc : c ∉ activeCentral) (t : ℕ) :
    (absorbedKernelCentral hn ^ t) c activeCentral = 0 := by
  rw [absorbedKernelCentral_pow_eq_dirac_of_not_mem hn c hc t,
    Measure.dirac_apply' _ activeCentral_measurableSet]
  simp [hc]

/-- Truncated potential for the central region: `(n²+2n)/f` inside the
    active region, 0 outside. Since `f ≤ n²+2n` always, this is ≥ 1 in
    the active region. -/
noncomputable def potentialCentralTrunc (c : Config n) : ℝ≥0∞ :=
  if c ∈ activeCentral then
    ((n ^ 2 + 2 * n : ℕ) : ℝ≥0∞) * (c.potential : ℝ≥0∞)⁻¹
  else 0

private theorem potentialCentralTrunc_measurable :
    Measurable (potentialCentralTrunc : Config n → ℝ≥0∞) :=
  measurable_ennreal _

/-- In the central region, `f = u²+2n < n²+2n` (strict inequality,
    since `|u| < n` when no count exceeds `7n/8`). -/
private theorem central_potential_strict_lt (c : Config n)
    (hc : c.inCentral) (hn : n ≥ 2) :
    c.potential < n ^ 2 + 2 * n := by
  obtain ⟨hb, hx, hy⟩ := hc
  unfold inLargeB at hb; unfold inLargeX at hx; unfold inLargeY at hy
  push_neg at hb hx hy
  unfold potential u gap
  have hsum := c.sum_eq
  suffices h : Int.natAbs ((c.x_count : ℤ) - ↑c.y_count) < n by
    exact Nat.add_lt_add_right (Nat.pow_lt_pow_left h (by omega)) _
  have hx_lt : c.x_count < n := by omega
  have hy_lt : c.y_count < n := by omega
  by_cases hle : c.x_count ≤ c.y_count
  · rw [show ((c.x_count : ℤ) - ↑c.y_count).natAbs = c.y_count - c.x_count from by omega]
    omega
  · push_neg at hle
    rw [show ((c.x_count : ℤ) - ↑c.y_count).natAbs = c.x_count - c.y_count from by omega]
    omega

/-- The active central region equals `{c | 1 ≤ potentialCentralTrunc c}`. -/
theorem activeCentral_eq_ge_one (hn : n ≥ 2) :
    (activeCentral : Set (Config n)) =
    {c | 1 ≤ potentialCentralTrunc c} := by
  ext c
  simp only [Set.mem_setOf_eq, activeCentral, potentialCentralTrunc]
  constructor
  · intro hc
    rw [if_pos hc]
    have hf_pos : 0 < c.potential := potential_pos c (by omega)
    have hf_le : c.potential ≤ n ^ 2 + 2 * n := potential_le c
    have hf_ne : (c.potential : ℝ≥0∞) ≠ 0 := by exact_mod_cast hf_pos.ne'
    calc (1 : ℝ≥0∞)
        = (c.potential : ℝ≥0∞) * (c.potential : ℝ≥0∞)⁻¹ :=
          (ENNReal.mul_inv_cancel hf_ne (ENNReal.natCast_ne_top c.potential)).symm
      _ ≤ ((n ^ 2 + 2 * n : ℕ) : ℝ≥0∞) * (c.potential : ℝ≥0∞)⁻¹ :=
          mul_le_mul_right' (by exact_mod_cast hf_le) _
  · intro hc
    by_contra hc'
    simp [if_neg hc'] at hc

private theorem contraction_rate_central_nonneg (hn : n ≥ 2) :
    (0 : ℝ) ≤ 1 - 1 / (15000 * (n : ℝ)) := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hpos : (0 : ℝ) < 15000 * (n : ℝ) := by positivity
  linarith [div_le_one hpos |>.mpr (show (1 : ℝ) ≤ 15000 * ↑n by linarith)]

/-! ### Helpers for 1/f (potential) drift bound

For each state-changing interaction, we express `count * (potential')⁻¹`
in terms of `count * (f ± (2u+1))⁻¹` where `f = potential c` and `u = gap`.
The non-state-changing interactions leave the potential unchanged. -/

/-- Cast helper: `(potential c' : ℝ) = (potential c : ℝ) + 2*(u:ℝ) + 1` after xb or xy. -/
private theorem potential_cast_plus (c c' : Config n) (h : (c'.potential : ℤ) - c.potential = 2 * c.u + 1) :
    (c'.potential : ℝ) = (c.potential : ℝ) + 2 * (c.u : ℝ) + 1 := by
  have : (c'.potential : ℤ) = (c.potential : ℤ) + 2 * c.u + 1 := by linarith
  exact_mod_cast this

/-- Cast helper: `(potential c' : ℝ) = (potential c : ℝ) - 2*(u:ℝ) + 1` after yb or yx. -/
private theorem potential_cast_minus (c c' : Config n) (h : (c'.potential : ℤ) - c.potential = -2 * c.u + 1) :
    (c'.potential : ℝ) = (c.potential : ℝ) - 2 * (c.u : ℝ) + 1 := by
  have key : (c'.potential : ℤ) + 2 * c.u = c.potential + 1 := by linarith
  have : (c'.potential : ℝ) + 2 * (c.u : ℝ) = (c.potential : ℝ) + 1 := by exact_mod_cast key
  linarith

private theorem inv_f_xb' (c : Config n) :
    (c.interactionCount .x .b : ℝ) * ((c.stepOrSelf .x .b).potential : ℝ)⁻¹ =
    ↑c.x_count * ↑c.b_count * ((c.potential : ℝ) + 2 * (c.u : ℝ) + 1)⁻¹ := by
  unfold interactionCount countOf stepOrSelf step
  simp only [show (State.x : State) ≠ .b from by decide, ite_false]
  split_ifs with h
  · obtain ⟨_, hb⟩ := h
    simp only [Option.getD_some]
    have hstep : c.step .x .b = some ⟨c.x_count + 1, c.b_count - 1, c.y_count, by have := c.sum_eq; omega⟩ := by
      simp [step]; exact ⟨by omega, hb⟩
    set c' := (⟨c.x_count + 1, c.b_count - 1, c.y_count, _⟩ : Config n)
    have hd := delta_f_xb c c' hstep
    have hpot := potential_cast_plus c c' hd
    simp only [Nat.cast_mul, hpot]
  · simp only [Option.getD_none]
    have : c.x_count = 0 ∨ c.b_count = 0 := by push_neg at h; omega
    rcases this with h | h <;> simp [h]

private theorem inv_f_yb' (c : Config n) :
    (c.interactionCount .y .b : ℝ) * ((c.stepOrSelf .y .b).potential : ℝ)⁻¹ =
    ↑c.y_count * ↑c.b_count * ((c.potential : ℝ) - 2 * (c.u : ℝ) + 1)⁻¹ := by
  unfold interactionCount countOf stepOrSelf step
  simp only [show (State.y : State) ≠ .b from by decide, ite_false]
  split_ifs with h
  · obtain ⟨_, hb⟩ := h
    simp only [Option.getD_some]
    have hstep : c.step .y .b = some ⟨c.x_count, c.b_count - 1, c.y_count + 1, by have := c.sum_eq; omega⟩ := by
      simp [step]; exact ⟨by omega, hb⟩
    set c' := (⟨c.x_count, c.b_count - 1, c.y_count + 1, _⟩ : Config n)
    have hd := delta_f_yb c c' hstep
    have hpot := potential_cast_minus c c' hd
    simp only [Nat.cast_mul, hpot]
  · simp only [Option.getD_none]
    have : c.y_count = 0 ∨ c.b_count = 0 := by push_neg at h; omega
    rcases this with h | h <;> simp [h]

private theorem inv_f_xy' (c : Config n) :
    (c.interactionCount .x .y : ℝ) * ((c.stepOrSelf .x .y).potential : ℝ)⁻¹ =
    ↑c.x_count * ↑c.y_count * ((c.potential : ℝ) + 2 * (c.u : ℝ) + 1)⁻¹ := by
  unfold interactionCount countOf stepOrSelf step
  simp only [show (State.x : State) ≠ .y from by decide, ite_false]
  split_ifs with h
  · obtain ⟨_, hy⟩ := h
    simp only [Option.getD_some]
    have hstep : c.step .x .y = some ⟨c.x_count, c.b_count + 1, c.y_count - 1, by have := c.sum_eq; omega⟩ := by
      simp [step]; exact ⟨by omega, hy⟩
    set c' := (⟨c.x_count, c.b_count + 1, c.y_count - 1, _⟩ : Config n)
    have hd := delta_f_xy c c' hstep
    have hpot := potential_cast_plus c c' hd
    simp only [Nat.cast_mul, hpot]
  · simp only [Option.getD_none]
    have : c.x_count = 0 ∨ c.y_count = 0 := by push_neg at h; omega
    rcases this with h | h <;> simp [h]

private theorem inv_f_yx' (c : Config n) :
    (c.interactionCount .y .x : ℝ) * ((c.stepOrSelf .y .x).potential : ℝ)⁻¹ =
    ↑c.y_count * ↑c.x_count * ((c.potential : ℝ) - 2 * (c.u : ℝ) + 1)⁻¹ := by
  unfold interactionCount countOf stepOrSelf step
  simp only [show (State.y : State) ≠ .x from by decide, ite_false]
  split_ifs with h
  · obtain ⟨_, hx⟩ := h
    simp only [Option.getD_some]
    have hstep : c.step .y .x = some ⟨c.x_count - 1, c.b_count + 1, c.y_count, by have := c.sum_eq; omega⟩ := by
      simp [step]; exact ⟨by omega, hx⟩
    set c' := (⟨c.x_count - 1, c.b_count + 1, c.y_count, _⟩ : Config n)
    have hd := delta_f_yx c c' hstep
    have hpot := potential_cast_minus c c' hd
    simp only [Nat.cast_mul, hpot]
  · simp only [Option.getD_none]
    have : c.y_count = 0 ∨ c.x_count = 0 := by push_neg at h; omega
    rcases this with h | h <;> simp [h]

/-- 1/f is bounded by 1/(2n), hence integrable over any probability measure. -/
private theorem integrable_inv_potential (c : Config n) (hn : n ≥ 2) :
    Integrable (fun c' : Config n => (c'.potential : ℝ)⁻¹) (transitionKernel hn c) := by
  have := (instIsMarkovKernel hn).isProbabilityMeasure c
  exact Integrable.of_bound (measurable_real _).aestronglyMeasurable (1 : ℝ)
    (ae_of_all _ fun c' => by
      rw [Real.norm_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))]
      rcases Nat.eq_zero_or_pos c'.potential with h | h
      · simp [h]
      · have hpos' : (0 : ℝ) < ↑c'.potential := Nat.cast_pos.mpr h
        rw [inv_eq_one_div, div_le_one hpos']
        exact_mod_cast h)

/-- potential ≥ 1 a.e. under the transition kernel, for c with v ≥ 1.
    Since potential = u²+2n ≥ 2n ≥ 4 for n ≥ 2. -/
private theorem ae_potential_ge_one (c : Config n) (hn : n ≥ 2) :
    ∀ᵐ c' ∂(transitionKernel hn c), c'.potential ≥ 1 :=
  ae_of_all _ (fun c' => by have := potential_pos c' (by omega : n ≥ 1); omega)

/-!
### Central region drift: supermartingale approach required

**The per-step contraction `E[1/f'] ≤ (1-δ)/f` is FALSE in the central region.**

Counterexample: n=4, x=1, b=0, y=3 (in activeCentral).
E[1/f']/(1/f) = 103/102 > 1, so 1/f INCREASES on average.
The drift coefficient E[Δf] ≥ 0 does NOT imply E[1/f'] ≤ 1/f because
1/x is convex (Jensen goes the wrong way). The truncated version
`absorbed_drift_central` is also false: all transitions from this config
stay in activeCentral, so truncation provides no help.

**Correct approach (Lemma 4 of Angluin-Aspnes-Eisenstat 2008):**
Define the supermartingale M_t = α_vb^{S^vb_t} · α_xy^{S^xy_t} / f(C_t)
where α_vb = (16n+7)/(16n), α_xy = (16n-5)/(16n), and S^vb_t, S^xy_t
are cumulative counts of vb and xy interactions.

The per-step supermartingale condition E[M_{t+1}|F_t] ≤ M_t reduces to:
• vb interactions: α_vb · f · E[1/f'|vb] ≤ 1
  ↔ (16n+7)·f·(v(f+1)-2u²) ≤ 16n·v·((f+1)²-4u²)
  **Proven** in `supermartingale_factor_vb_le` (Supermartingale.lean)

• xy interactions: α_xy · f · E[1/f'|xy] ≤ 1
  ↔ (16n-5)·f·(f+1) ≤ 16n·((f+1)²-4u²)
  **Proven** in `supermartingale_factor_xy_le` (Supermartingale.lean)

Both hold for ALL n ≥ 1 (not just "sufficiently large n").

**Remaining theorem assembly steps:**
1. Define augmented state (Config × S^vb × S^xy) and augmented kernel
2. Define M as a function on the augmented state
3. Prove E[M_t] ≤ M_0 by induction using the per-step bounds
4. Apply Markov's inequality to bound S^vb and S^xy
5. Bound total central interactions (Lemma 5: S^c ≤ 130·S^vb + 258·S^xy)
6. Derive the geometric tail bound on exit time
-/

-- prob_in_activeCentral_le and convergence_time_central moved to
-- AugmentedState.lean to avoid circular import.
-- See central_geometric_decay in AugmentedState.lean.

end Config
end PopProto
