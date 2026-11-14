/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/

import Mathlib
import Ripple.Stochastic.BrownianMotion.Gaussian.BrownianMotion
import Ripple.Stochastic.WienerIntegralL2

/-!
# Itô isometry for an arbitrary Brownian filtration

Coefficients are measurable for the given filtration. Single future increments
are independent of that filtration. The rectangle pairing uses polarization of
squared increments, so no joint future-independence assumption is added.
-/


namespace Ripple.Stochastic
namespace FilteredItoIsometry

open MeasureTheory ProbabilityTheory Ripple.Stochastic.MathFin
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ} {𝓖 : Filtration ℝ≥0 mΩ}
  [hB : IsFilteredPreBrownian B 𝓖 μ]

/-- Measurability with respect to the given filtration at the initial time. -/
def AdaptedAt (_B : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (φ : Ω → ℝ) : Prop :=
  Measurable[𝓖 t] φ

/-- A filtration-measurable coefficient is ambient measurable. -/
theorem AdaptedAt.measurable (_hBmeas : ∀ t, Measurable (B t)) {t : ℝ≥0}
    {φ : Ω → ℝ} (hφ : AdaptedAt (𝓖 := 𝓖) B t φ) : Measurable φ :=
  Measurable.mono hφ (𝓖.le t) le_rfl

include hB in
/-- Brownian evaluations before the current time are adapted. -/
theorem adaptedAt_eval {t u : ℝ≥0} (hu : u ≤ t) :
    AdaptedAt (𝓖 := 𝓖) B t (B u) :=
  (hB.stronglyAdapted u).measurable.mono (𝓖.mono hu) le_rfl

include hB in
/-- Adaptedness is preserved by measurable composition. -/
theorem adaptedAt_comp_eval {t u : ℝ≥0} (hu : u ≤ t)
    {g : ℝ → ℝ} (hg : Measurable g) :
    AdaptedAt (𝓖 := 𝓖) B t (fun ω => g (B u ω)) :=
  hg.comp (adaptedAt_eval (𝓖 := 𝓖) (μ := μ) hu)

/-- Adaptedness is monotone in time. -/
theorem AdaptedAt.mono {s t : ℝ≥0} (hst : s ≤ t) {φ : Ω → ℝ}
    (hφ : AdaptedAt (𝓖 := 𝓖) B s φ) : AdaptedAt (𝓖 := 𝓖) B t φ :=
  Measurable.mono hφ (𝓖.mono hst) le_rfl

/-- Products of adapted coefficients are adapted. -/
theorem AdaptedAt.mul {t : ℝ≥0} {φ ψ : Ω → ℝ}
    (hφ : AdaptedAt (𝓖 := 𝓖) B t φ) (hψ : AdaptedAt (𝓖 := 𝓖) B t ψ) :
    AdaptedAt (𝓖 := 𝓖) B t (fun ω => φ ω * ψ ω) := Measurable.mul hφ hψ

/-- Differences of adapted coefficients are adapted. -/
theorem AdaptedAt.sub {t : ℝ≥0} {φ ψ : Ω → ℝ}
    (hφ : AdaptedAt (𝓖 := 𝓖) B t φ) (hψ : AdaptedAt (𝓖 := 𝓖) B t ψ) :
    AdaptedAt (𝓖 := 𝓖) B t (fun ω => φ ω - ψ ω) := Measurable.sub hφ hψ

/-- A filtration-measurable coefficient is independent of the next increment. -/
theorem adapted_indepFun_increment
    (_hBmeas : ∀ t, Measurable (B t)) {s t : ℝ≥0} (hst : s ≤ t)
    {φ : Ω → ℝ} (hφ : AdaptedAt (𝓖 := 𝓖) B s φ) :
    IndepFun φ (fun ω => B t ω - B s ω) μ := by
  apply (IndepFun_iff_Indep _ _ _).mpr
  exact (indep_of_indep_of_le_right (hB.indep s t hst)
    (measurable_iff_comap_le.mp hφ)).symm

/-- **Martingale-difference property of the Itô integral** (discrete form):
for `φ` adapted to `𝓕_{t₀}`, the integrand times the next Brownian increment
has mean zero, `E[φ · (B_{t₁} - B_{t₀})] = 0`. This is the reason the Itô
integral is a martingale — and it holds for *random* `φ`, where the Wiener
(deterministic) covariance argument does not apply. -/
theorem integral_adapted_mul_increment
    (hBmeas : ∀ t, Measurable (B t)) {t₀ t₁ : ℝ≥0} (ht : t₀ ≤ t₁)
    {φ : Ω → ℝ} (hφ : AdaptedAt (𝓖 := 𝓖) B t₀ φ) :
    ∫ ω, φ ω * (B t₁ ω - B t₀ ω) ∂μ = 0 := by
  have hindep := adapted_indepFun_increment (μ := μ) hBmeas ht hφ
  have hφm : Measurable φ := hφ.measurable hBmeas
  have hΔm : Measurable (fun ω => B t₁ ω - B t₀ ω) := (hBmeas t₁).sub (hBmeas t₀)
  rw [hindep.integral_fun_mul_eq_mul_integral hφm.aestronglyMeasurable
        hΔm.aestronglyMeasurable]
  have hmean : ∫ ω, (B t₁ ω - B t₀ ω) ∂μ = 0 := by
    have h := (hB.hasLaw_sub t₁ t₀).integral_eq
    rwa [integral_id_gaussianReal] at h
  rw [hmean, mul_zero]

/-- The forward increment has second moment `E[(B_{t₁} - B_{t₀})²] = t₁ - t₀`: the
diagonal instance of the Wiener-layer increment covariance
`WienerIntegralL2.covariance_increment_aux`. -/
theorem integral_increment_sq
    [hPB : IsPreBrownian B μ]
    {t₀ t₁ : ℝ≥0} (ht : t₀ ≤ t₁) :
    ∫ ω, (B t₁ ω - B t₀ ω) ^ 2 ∂μ = (t₁ : ℝ) - t₀ := by
  haveI : IsProbabilityMeasure μ := hPB.isGaussianProcess.isProbabilityMeasure
  have h := WienerIntegralL2.covariance_increment_aux (B := B) (μ := μ) t₀ t₁ t₀ t₁ ht ht
  simp only [min_self, max_self] at h
  rw [max_eq_right (sub_nonneg.mpr (NNReal.coe_le_coe.mpr ht))] at h
  rw [← h]
  exact integral_congr_ae (Filter.Eventually.of_forall fun ω => pow_two (B t₁ ω - B t₀ ω))

/-- **General isometry kernel**: for `χ` adapted to `𝓕_{t₀}`,
`E[χ · (B_{t₁} - B_{t₀})²] = E[χ] · (t₁ - t₀)`. The increment's square is
independent of the past (weak Markov) and has mean `t₁ - t₀`. Specialises to
`integral_adapted_sq_mul_increment_sq` (take `χ = φ²`); supplies the *diagonal*
term of the bilinear isometry below (`χ = φₖ · ψₖ`). -/
theorem integral_adapted_mul_increment_sq
    (hBmeas : ∀ t, Measurable (B t)) {t₀ t₁ : ℝ≥0} (ht : t₀ ≤ t₁)
    {χ : Ω → ℝ} (hχ : AdaptedAt (𝓖 := 𝓖) B t₀ χ) :
    ∫ ω, χ ω * (B t₁ ω - B t₀ ω) ^ 2 ∂μ = (∫ ω, χ ω ∂μ) * ((t₁ : ℝ) - t₀) := by
  have hχm : Measurable χ := hχ.measurable hBmeas
  have hΔm : Measurable (fun ω => B t₁ ω - B t₀ ω) := (hBmeas t₁).sub (hBmeas t₀)
  have hindep := adapted_indepFun_increment (μ := μ) hBmeas ht hχ
  have hindep2 := hindep.comp (φ := (id : ℝ → ℝ)) (ψ := fun x : ℝ => x ^ 2)
    measurable_id (by fun_prop)
  have key := hindep2.integral_fun_mul_eq_mul_integral
    hχm.aestronglyMeasurable (hΔm.pow_const 2).aestronglyMeasurable
  simp only [Function.comp_apply, id_eq] at key
  rw [key, integral_increment_sq (μ := μ) ht]

/-- **Isometry kernel** (the diagonal term of the Itô isometry): for `φ`
adapted to `𝓕_{t₀}`, `E[φ² · (B_{t₁} - B_{t₀})²] = E[φ²] · (t₁ - t₀)`. The
`χ = φ²` instance of `integral_adapted_mul_increment_sq`. -/
theorem integral_adapted_sq_mul_increment_sq
    (hBmeas : ∀ t, Measurable (B t)) {t₀ t₁ : ℝ≥0} (ht : t₀ ≤ t₁)
    {φ : Ω → ℝ} (hφ : AdaptedAt (𝓖 := 𝓖) B t₀ φ) :
    ∫ ω, (φ ω) ^ 2 * (B t₁ ω - B t₀ ω) ^ 2 ∂μ =
      (∫ ω, (φ ω) ^ 2 ∂μ) * ((t₁ : ℝ) - t₀) := by
  have hχ : AdaptedAt (𝓖 := 𝓖) B t₀ (fun ω => (φ ω) ^ 2) := by
    exact hφ.pow_const 2
  exact integral_adapted_mul_increment_sq hBmeas ht hχ

/-- If `φ` is adapted to `𝓕_{t₀}` and in `L²`, then `φ · (B_{t₁} - B_{t₀})` is
in `L²`: the increment is in `L²` and independent of `φ`, so the product's
square is integrable. This is the `L²`-membership of a single term of an
adapted simple integral. -/
theorem memLp_adapted_mul_increment
    (hBmeas : ∀ t, Measurable (B t)) {t₀ t₁ : ℝ≥0} (ht : t₀ ≤ t₁)
    {φ : Ω → ℝ} (hφ : AdaptedAt (𝓖 := 𝓖) B t₀ φ) (hφL2 : MemLp φ 2 μ) :
    MemLp (fun ω => φ ω * (B t₁ ω - B t₀ ω)) 2 μ := by
  have hindep := adapted_indepFun_increment (μ := μ) hBmeas ht hφ
  have hφm : Measurable φ := hφ.measurable hBmeas
  have hΔm : Measurable (fun ω => B t₁ ω - B t₀ ω) := (hBmeas t₁).sub (hBmeas t₀)
  have hφsq : Integrable (fun ω => (φ ω) ^ 2) μ := hφL2.integrable_sq
  have hΔsq : Integrable (fun ω => (B t₁ ω - B t₀ ω) ^ 2) μ :=
    (hB.isGaussianProcess.hasGaussianLaw_sub.memLp_two).integrable_sq
  have hindep2 := hindep.comp (φ := fun x : ℝ => x ^ 2) (ψ := fun x : ℝ => x ^ 2)
    (by fun_prop) (by fun_prop)
  have hprod : Integrable
      (fun ω => (φ ω) ^ 2 * (B t₁ ω - B t₀ ω) ^ 2) μ := by
    have h := hindep2.integrable_mul hφsq hΔsq
    simpa [Function.comp, Pi.mul_apply] using h
  refine (memLp_two_iff_integrable_sq (hφm.mul hΔm).aestronglyMeasurable).mpr ?_
  simpa [mul_pow] using hprod

/-! ### The discrete Itô isometry over a partition -/

/-- **Bilinear cross terms vanish.** For two adapted integrand families `φ`,
`ψ` and `j < k`, `E[(φⱼ·ΔBⱼ)·(ψₖ·ΔBₖ)] = 0`. The factor `φⱼ·ΔBⱼ·ψₖ` is
`𝓕_{tₖ}`-measurable, and `ΔBₖ` is independent of it with mean zero. -/
theorem integral_cross_increment_bilinear_eq_zero
    (hBmeas : ∀ s, Measurable (B s)) {t : ℕ → ℝ≥0} (hmono : Monotone t)
    {φ ψ : ℕ → Ω → ℝ} (hφ : ∀ n, AdaptedAt (𝓖 := 𝓖) B (t n) (φ n))
    (hψ : ∀ n, AdaptedAt (𝓖 := 𝓖) B (t n) (ψ n)) {j k : ℕ} (hjk : j < k) :
    ∫ ω, (φ j ω * (B (t (j + 1)) ω - B (t j) ω)) *
          (ψ k ω * (B (t (k + 1)) ω - B (t k) ω)) ∂μ = 0 := by
  have hΦ : AdaptedAt (𝓖 := 𝓖) B (t k)
      (fun ω => φ j ω * (B (t (j + 1)) ω - B (t j) ω) * ψ k ω) :=
    (((hφ j).mono (hmono hjk.le)).mul
      ((adaptedAt_eval (μ := μ) (hmono hjk)).sub (adaptedAt_eval (μ := μ) (hmono hjk.le)))).mul (hψ k)
  have hstep : t k ≤ t (k + 1) := hmono (Nat.le_succ k)
  have h0 := integral_adapted_mul_increment (μ := μ) hBmeas hstep hΦ
  rw [show (fun ω => (φ j ω * (B (t (j + 1)) ω - B (t j) ω)) *
        (ψ k ω * (B (t (k + 1)) ω - B (t k) ω)))
      = (fun ω => (φ j ω * (B (t (j + 1)) ω - B (t j) ω) * ψ k ω) *
        (B (t (k + 1)) ω - B (t k) ω)) from by funext ω; ring]
  exact h0

/-- **The bilinear discrete Itô isometry** (the inner-product/polarised form).
For adapted `L²` integrand families `φ`, `ψ` over a partition `t`,

  `E[(Σₖ φₖ·ΔBₖ)·(Σₖ ψₖ·ΔBₖ)] = Σₖ E[φₖ·ψₖ]·(t_{k+1} − t_k)`.

This is the workhorse for the continuous Itô isometry: the inner product of two
adapted simple integrals is the `L²(Ω × [0,T])` inner product of the integrands.
The diagonal terms give the mixed kernel `integral_adapted_mul_increment_sq`;
the off-diagonal terms vanish by `integral_cross_increment_bilinear_eq_zero`. -/
theorem ito_isometry_discrete_bilinear
    (hBmeas : ∀ s, Measurable (B s)) {N : ℕ} {t : ℕ → ℝ≥0} (hmono : Monotone t)
    {φ ψ : ℕ → Ω → ℝ} (hφ : ∀ n, AdaptedAt (𝓖 := 𝓖) B (t n) (φ n))
    (hψ : ∀ n, AdaptedAt (𝓖 := 𝓖) B (t n) (ψ n))
    (hφL2 : ∀ n, MemLp (φ n) 2 μ) (hψL2 : ∀ n, MemLp (ψ n) 2 μ) :
    ∫ ω, (∑ k ∈ Finset.range N, φ k ω * (B (t (k + 1)) ω - B (t k) ω)) *
          (∑ k ∈ Finset.range N, ψ k ω * (B (t (k + 1)) ω - B (t k) ω)) ∂μ =
      ∑ k ∈ Finset.range N, (∫ ω, φ k ω * ψ k ω ∂μ) * ((t (k + 1) : ℝ) - t k) := by
  classical
  haveI : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  set a : ℕ → Ω → ℝ := fun k ω => φ k ω * (B (t (k + 1)) ω - B (t k) ω) with ha_def
  set b : ℕ → Ω → ℝ := fun k ω => ψ k ω * (B (t (k + 1)) ω - B (t k) ω) with hb_def
  have ha_L2 : ∀ k, MemLp (a k) 2 μ := fun k =>
    memLp_adapted_mul_increment hBmeas (hmono (Nat.le_succ k)) (hφ k) (hφL2 k)
  have hb_L2 : ∀ k, MemLp (b k) 2 μ := fun k =>
    memLp_adapted_mul_increment hBmeas (hmono (Nat.le_succ k)) (hψ k) (hψL2 k)
  have hint : ∀ j k, Integrable (fun ω => a j ω * b k ω) μ := fun j k =>
    (ha_L2 j).integrable_mul (hb_L2 k)
  -- Diagonal term = mixed variance kernel.
  have hdiag : ∀ k, ∫ ω, a k ω * b k ω ∂μ =
      (∫ ω, φ k ω * ψ k ω ∂μ) * ((t (k + 1) : ℝ) - t k) := by
    intro k
    have hstep : t k ≤ t (k + 1) := hmono (Nat.le_succ k)
    have hχ : AdaptedAt (𝓖 := 𝓖) B (t k) (fun ω => φ k ω * ψ k ω) := (hφ k).mul (hψ k)
    rw [show (fun ω => a k ω * b k ω)
          = (fun ω => (φ k ω * ψ k ω) * (B (t (k + 1)) ω - B (t k) ω) ^ 2) from by
            funext ω; simp only [ha_def, hb_def]; ring]
    exact integral_adapted_mul_increment_sq (μ := μ) hBmeas hstep hχ
  -- Off-diagonal terms vanish.
  have hcross : ∀ j ∈ Finset.range N, ∀ k ∈ Finset.range N, j ≠ k →
      ∫ ω, a j ω * b k ω ∂μ = 0 := by
    intro j _ k _ hjk
    rcases lt_or_gt_of_ne hjk with h | h
    · exact integral_cross_increment_bilinear_eq_zero hBmeas hmono hφ hψ h
    · rw [show (fun ω => a j ω * b k ω) = (fun ω => b k ω * a j ω) from by funext ω; ring]
      exact integral_cross_increment_bilinear_eq_zero hBmeas hmono hψ hφ h
  calc ∫ ω, (∑ k ∈ Finset.range N, a k ω) * (∑ k ∈ Finset.range N, b k ω) ∂μ
      = ∫ ω, ∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N, a j ω * b k ω ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
        show (∑ k ∈ Finset.range N, a k ω) * (∑ k ∈ Finset.range N, b k ω)
          = ∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N, a j ω * b k ω
        rw [Finset.sum_mul_sum]
    _ = ∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N, ∫ ω, a j ω * b k ω ∂μ := by
        rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ => hint j k))]
        exact Finset.sum_congr rfl
          (fun j _ => integral_finsetSum _ (fun k _ => hint j k))
    _ = ∑ j ∈ Finset.range N, ∫ ω, a j ω * b j ω ∂μ := by
        refine Finset.sum_congr rfl (fun j hj => ?_)
        exact Finset.sum_eq_single j (fun k hk hkj => hcross j hj k hk (Ne.symm hkj))
          (fun hj' => absurd hj hj')
    _ = ∑ k ∈ Finset.range N, (∫ ω, φ k ω * ψ k ω ∂μ) * ((t (k + 1) : ℝ) - t k) :=
        Finset.sum_congr rfl (fun k _ => hdiag k)

/-- **The discrete Itô isometry** (adapted simple integrands):
`E[(Σₖ φₖ·(B_{t_{k+1}} − B_{t_k}))²] = Σₖ E[φₖ²]·(t_{k+1} − t_k)`. The genuine
Itô isometry — the integrand is *random*. It is the `ψ = φ` diagonal of the
inner-product form `ito_isometry_discrete_bilinear` (`x² = x·x`). -/
theorem ito_isometry_discrete
    (hBmeas : ∀ s, Measurable (B s)) {N : ℕ} {t : ℕ → ℝ≥0} (hmono : Monotone t)
    {φ : ℕ → Ω → ℝ} (hadapt : ∀ n, AdaptedAt (𝓖 := 𝓖) B (t n) (φ n))
    (hL2 : ∀ n, MemLp (φ n) 2 μ) :
    ∫ ω, (∑ k ∈ Finset.range N, φ k ω * (B (t (k + 1)) ω - B (t k) ω)) ^ 2 ∂μ =
      ∑ k ∈ Finset.range N, (∫ ω, (φ k ω) ^ 2 ∂μ) * ((t (k + 1) : ℝ) - t k) := by
  simp only [pow_two]
  exact ito_isometry_discrete_bilinear hBmeas hmono hadapt hadapt hL2 hL2

/-- `E[B_s²] = s` (mean zero, variance `s`). -/
theorem integral_eval_sq
    [hPB : IsPreBrownian B μ] (hBmeas : ∀ s, Measurable (B s)) (s : ℝ≥0) :
    ∫ ω, (B s ω) ^ 2 ∂μ = (s : ℝ) := by
  rw [← variance_of_integral_eq_zero (hBmeas s).aemeasurable (hPB.integral_eval s)]
  show Var[B s; μ] = (s : ℝ)
  rw [(hPB.hasLaw_eval s).variance_eq, variance_id_gaussianReal]

include hB in
/-- **The discrete `∫₀ᵀ B dB` isometry** — the canonical instance, with *no*
remaining hypotheses beyond measurability. Taking the adapted `L²` integrand
`φₖ = B(tₖ)`,

  `E[(Σₖ B(tₖ)·(B_{t_{k+1}} − B_{t_k}))²] = Σₖ t_k·(t_{k+1} − t_k)`,

the Riemann-sum form of the Itô isometry `E[(∫₀ᵀ B dB)²] = ∫₀ᵀ t dt`. -/
theorem ito_isometry_brownian_self
    (hBmeas : ∀ s, Measurable (B s)) {N : ℕ} {t : ℕ → ℝ≥0} (hmono : Monotone t) :
    ∫ ω, (∑ k ∈ Finset.range N, B (t k) ω * (B (t (k + 1)) ω - B (t k) ω)) ^ 2 ∂μ =
      ∑ k ∈ Finset.range N, (t k : ℝ) * ((t (k + 1) : ℝ) - t k) := by
  rw [ito_isometry_discrete (𝓖 := 𝓖) (μ := μ) hBmeas hmono (φ := fun k => B (t k))
    (fun n => adaptedAt_eval (𝓖 := 𝓖) (μ := μ) le_rfl)
    (fun n => (hB.isGaussianProcess.hasGaussianLaw_eval (t n)).memLp_two)]
  exact Finset.sum_congr rfl (fun k _ => by rw [integral_eval_sq hBmeas])

/-! ### Pairing identity for predictable rectangles

The bridge to the *continuous* Itô integral. For an adapted indicator `f`
(`𝓕_s`-measurable) and `g` (`𝓕_{s'}`-measurable),

  `E[f·(B_t − B_s) · g·(B_{t'} − B_{s'})] = E[f·g] · vol((s,t] ∩ (s',t'])`.

This is the adapted generalisation of `WienerIntegralL2.covariance_increment_aux`
(take `f = g = 1`). It is the inner-product identity that makes the assembly of
predictable simple integrands an isometry into `L²(Ω × [0,T])`. The split-at-the-
later-start argument: the pre-overlap part pairs to zero (martingale difference),
and the post-overlap part has both increments *forward* of the later start, so the
adapted coefficient factors out (weak Markov), leaving the deterministic overlap
covariance `integral_two_increment`. -/

/-- Two increments sharing a start: `E[(B_t − B_a)(B_{t'} − B_a)] = min t t' − a`
for `a ≤ t`, `a ≤ t'`: the shared-start instance of the Wiener-layer increment
covariance `WienerIntegralL2.covariance_increment_aux` (`max a a = a`, and the
overlap `min t t' − a` is nonnegative); the stochastic content lives in
`rect_increment_pairing`. -/
theorem integral_two_increment
    [hPB : IsPreBrownian B μ]
    {a t t' : ℝ≥0} (hat : a ≤ t) (hat' : a ≤ t') :
    ∫ ω, (B t ω - B a ω) * (B t' ω - B a ω) ∂μ = ((min t t' : ℝ≥0) : ℝ) - a := by
  haveI : IsProbabilityMeasure μ := hPB.isGaussianProcess.isProbabilityMeasure
  have h := WienerIntegralL2.covariance_increment_aux (B := B) (μ := μ) a t a t' hat hat'
  simp only [max_self] at h
  rw [h, NNReal.coe_min, max_eq_right]
  exact sub_nonneg.mpr (le_min (NNReal.coe_le_coe.mpr hat) (NNReal.coe_le_coe.mpr hat'))

/-- Integrability of `h · ΔB · ΔB'` for `h` bounded (the products that appear
when splitting the rectangle pairing). -/
private lemma integrable_bdd_two_increment
    [hPB : IsPreBrownian B μ]
    {h : Ω → ℝ} (hhm : Measurable h)
    {C : ℝ} (hhb : ∀ ω, |h ω| ≤ C) (a b c d : ℝ≥0) :
    Integrable (fun ω => h ω * ((B b ω - B a ω) * (B d ω - B c ω))) μ := by
  have hprod : Integrable (fun ω => (B b ω - B a ω) * (B d ω - B c ω)) μ :=
    (hPB.isGaussianProcess.hasGaussianLaw_sub.memLp_two).integrable_mul
      (hPB.isGaussianProcess.hasGaussianLaw_sub.memLp_two)
  exact hprod.bdd_mul hhm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hhb ω)

/-- Weighted covariance of two increments sharing a start, derived from
three weighted variance identities. This uses only single-increment independence. -/
theorem integral_adapted_mul_two_increment
    (hBmeas : ∀ u, Measurable (B u)) {a t u : ℝ≥0}
    {χ : Ω → ℝ} (hχ : AdaptedAt (𝓖 := 𝓖) B a χ)
    {C : ℝ} (hχb : ∀ ω, |χ ω| ≤ C) (hat : a ≤ t) (hau : a ≤ u) :
    ∫ ω, χ ω * ((B t ω - B a ω) * (B u ω - B a ω)) ∂μ =
      (∫ ω, χ ω ∂μ) * (((min t u : ℝ≥0) : ℝ) - a) := by
  have hχm : Measurable χ := hχ.measurable hBmeas
  have hint (b c : ℝ≥0) :
      Integrable (fun ω => χ ω * (B c ω - B b ω) ^ 2) μ := by
    simpa [pow_two] using integrable_bdd_two_increment hχm hχb b c b c
  have hpol :
      (fun ω => χ ω * ((B t ω - B a ω) * (B u ω - B a ω))) =
      (fun ω => ((χ ω * (B t ω - B a ω) ^ 2 +
        χ ω * (B u ω - B a ω) ^ 2) - χ ω * (B u ω - B t ω) ^ 2) / 2) := by
    funext ω; ring
  rw [hpol]
  simp_rw [div_eq_mul_inv]
  rw [integral_mul_const,
    integral_sub (show Integrable (fun ω => χ ω * (B t ω - B a ω) ^ 2 +
      χ ω * (B u ω - B a ω) ^ 2) μ from (hint a t).add (hint a u)) (hint t u),
    integral_add (hint a t) (hint a u),
    integral_adapted_mul_increment_sq hBmeas hat hχ,
    integral_adapted_mul_increment_sq hBmeas hau hχ]
  rcases le_total t u with htu | hut
  · rw [integral_adapted_mul_increment_sq hBmeas htu (hχ.mono hat),
      min_eq_left htu]
    ring
  · have hsq : (fun ω => χ ω * (B u ω - B t ω) ^ 2) =
        (fun ω => χ ω * (B t ω - B u ω) ^ 2) := by funext ω; ring
    rw [hsq, integral_adapted_mul_increment_sq hBmeas hut (hχ.mono hau),
      min_eq_right hut]
    ring

/-- Pairing identity, oriented case `s ≤ s'`. -/
private lemma rect_increment_pairing_aux
    (hBmeas : ∀ s, Measurable (B s)) {f g : Ω → ℝ} {s t s' t' : ℝ≥0}
    (hf : AdaptedAt (𝓖 := 𝓖) B s f) (hg : AdaptedAt (𝓖 := 𝓖) B s' g)
    {Cf Cg : ℝ} (hfb : ∀ ω, |f ω| ≤ Cf) (hgb : ∀ ω, |g ω| ≤ Cg)
    (_hst : s ≤ t) (hst' : s' ≤ t') (hss' : s ≤ s') :
    ∫ ω, (f ω * (B t ω - B s ω)) * (g ω * (B t' ω - B s' ω)) ∂μ =
      (∫ ω, f ω * g ω ∂μ) * max 0 ((min (t : ℝ) t') - max (s : ℝ) s') := by
  have hfm : Measurable f := hf.measurable hBmeas
  have hgm : Measurable g := hg.measurable hBmeas
  have hfg : AdaptedAt (𝓖 := 𝓖) B s' (fun ω => f ω * g ω) := (hf.mono hss').mul hg
  have hfgm : Measurable (fun ω => f ω * g ω) := hfm.mul hgm
  have hfgb : ∀ ω, |f ω * g ω| ≤ Cf * Cg := fun ω => by
    rw [abs_mul]
    exact mul_le_mul (hfb ω) (hgb ω) (abs_nonneg _) (le_trans (abs_nonneg _) (hfb ω))
  have hmaxss' : max (s : ℝ) s' = (s' : ℝ) := max_eq_right (by exact_mod_cast hss')
  rw [hmaxss']
  by_cases htle : t ≤ s'
  · -- Disjoint intervals: the whole pairing is a forward increment with mean zero.
    have hχ : AdaptedAt (𝓖 := 𝓖) B s' (fun ω => f ω * (B t ω - B s ω) * g ω) :=
      ((hf.mono hss').mul ((adaptedAt_eval (μ := μ) htle).sub (adaptedAt_eval (μ := μ) hss'))).mul hg
    have h0 := integral_adapted_mul_increment (μ := μ) hBmeas hst' hχ
    have hzero : max (0 : ℝ) ((min (t : ℝ) t') - s') = 0 := by
      refine max_eq_left ?_
      have : (min (t : ℝ) t') ≤ (s' : ℝ) :=
        le_trans (min_le_left _ _) (by exact_mod_cast htle)
      linarith
    rw [hzero, mul_zero, ← h0]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω => by ring)
  · -- Overlapping intervals: split the first increment at the later start `s'`.
    replace htle := not_le.mp htle
    have hT1 : ∫ ω, f ω * g ω * ((B s' ω - B s ω) * (B t' ω - B s' ω)) ∂μ = 0 := by
      have hχ : AdaptedAt (𝓖 := 𝓖) B s' (fun ω => f ω * g ω * (B s' ω - B s ω)) :=
        hfg.mul ((adaptedAt_eval (μ := μ) le_rfl).sub (adaptedAt_eval (μ := μ) hss'))
      have h0 := integral_adapted_mul_increment (μ := μ) hBmeas hst' hχ
      rw [← h0]
      exact integral_congr_ae (Filter.Eventually.of_forall fun ω => by ring)
    have hT2 : ∫ ω, f ω * g ω * ((B t ω - B s' ω) * (B t' ω - B s' ω)) ∂μ
        = (∫ ω, f ω * g ω ∂μ) * (((min t t' : ℝ≥0) : ℝ) - s') := by
      have hweighted := integral_adapted_mul_two_increment (𝓖 := 𝓖) (μ := μ)
        hBmeas hfg hfgb htle.le hst'
      exact hweighted
    have hsum : ∫ ω, (f ω * (B t ω - B s ω)) * (g ω * (B t' ω - B s' ω)) ∂μ
        = (∫ ω, f ω * g ω * ((B s' ω - B s ω) * (B t' ω - B s' ω)) ∂μ)
          + ∫ ω, f ω * g ω * ((B t ω - B s' ω) * (B t' ω - B s' ω)) ∂μ := by
      rw [← integral_add (integrable_bdd_two_increment hfgm hfgb s s' s' t')
                         (integrable_bdd_two_increment hfgm hfgb s' t s' t')]
      exact integral_congr_ae (Filter.Eventually.of_forall fun ω => by ring)
    have hcoe : ((min t t' : ℝ≥0) : ℝ) = min (t : ℝ) t' := by
      rcases le_total t t' with h | h
      · rw [min_eq_left h, min_eq_left (by exact_mod_cast h)]
      · rw [min_eq_right h, min_eq_right (by exact_mod_cast h)]
    rw [hsum, hT1, hT2, zero_add, hcoe]
    congr 1
    have h1 : (s' : ℝ) ≤ min (t : ℝ) t' :=
      le_min (by exact_mod_cast htle.le) (by exact_mod_cast hst')
    rw [max_eq_right (by linarith)]

/-- **Pairing identity for predictable rectangles.** For adapted bounded
integrands `f` (`𝓕_s`-measurable) and `g` (`𝓕_{s'}`-measurable),

  `E[f·(B_t − B_s) · g·(B_{t'} − B_{s'})] = E[f·g] · vol((s,t] ∩ (s',t'])`,

with `vol((s,t] ∩ (s',t']) = max 0 (min t t' − max s s')`. The adapted
generalisation of the Wiener covariance identity, and the inner-product core of
the continuous Itô isometry. -/
theorem rect_increment_pairing
    (hBmeas : ∀ s, Measurable (B s)) {f g : Ω → ℝ} {s t s' t' : ℝ≥0}
    (hf : AdaptedAt (𝓖 := 𝓖) B s f) (hg : AdaptedAt (𝓖 := 𝓖) B s' g)
    {Cf Cg : ℝ} (hfb : ∀ ω, |f ω| ≤ Cf) (hgb : ∀ ω, |g ω| ≤ Cg)
    (hst : s ≤ t) (hst' : s' ≤ t') :
    ∫ ω, (f ω * (B t ω - B s ω)) * (g ω * (B t' ω - B s' ω)) ∂μ =
      (∫ ω, f ω * g ω ∂μ) * max 0 ((min (t : ℝ) t') - max (s : ℝ) s') := by
  rcases le_total s s' with h | h
  · exact rect_increment_pairing_aux hBmeas hf hg hfb hgb hst hst' h
  · rw [show (∫ ω, (f ω * (B t ω - B s ω)) * (g ω * (B t' ω - B s' ω)) ∂μ)
          = ∫ ω, (g ω * (B t' ω - B s' ω)) * (f ω * (B t ω - B s ω)) ∂μ from
        integral_congr_ae (Filter.Eventually.of_forall fun ω => by ring),
        rect_increment_pairing_aux hBmeas hg hf hgb hfb hst' hst h]
    congr 1
    · exact integral_congr_ae (Filter.Eventually.of_forall fun ω => by ring)
    · rw [min_comm (t' : ℝ) t, max_comm (s' : ℝ) s]

end FilteredItoIsometry
end Ripple.Stochastic
