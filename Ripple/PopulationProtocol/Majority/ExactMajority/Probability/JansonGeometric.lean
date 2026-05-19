/-
Janson's tail bound for sums of independent geometric random variables
(Doty et al. Theorem 4.3, Corollary 4.4).

Reference: Janson [39, Theorems 2.1, 3.1].

These are the engine behind Doty Lemma 4.5 (epidemic time concentration)
and the various phase-time bounds in §§5–7. Mathlib does not currently
provide them.

  Theorem 4.3. Let X = X_1 + ... + X_k where each X_i ~ Geometric(p_i)
    independently. Let μ = E[X] = Σ 1/p_i and p* = min p_i. Then for all
    λ ≥ 1, P[X ≥ λ μ] ≤ exp(−p* μ (λ − 1 − ln λ)). For all λ ≤ 1,
    P[X ≤ λ μ] ≤ exp(−p* μ (λ − 1 − ln λ)).

  Corollary 4.4. For any 0 < ε < 1,
    P[(1 − ε) μ ≤ X ≤ (1 + ε) μ] ≥ 1 − exp(−Θ(ε² p* μ)).

This file proves the Markov/Chernoff step, the shifted-geometric MGF formula,
and the optimized one-sided Janson parameter substitutions from local geometric
parameter bounds.
-/

import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.Distributions.Geometric
import Mathlib.Probability.ProbabilityMassFunction.Integrals

open MeasureTheory ProbabilityTheory
open scoped Real BigOperators ENNReal NNReal

namespace ExactMajority

/-- The exponential series for the shifted geometric waiting time.

Mathlib's `geometricPMFReal p n` is the distribution on failures before the
first success, with mass `(1-p)^n p` at `n`.  The population-protocol waiting
time convention is the shifted variable `n + 1`, so its exponential series is
`exp t * p / (1 - (1-p) exp t)` on the convergence side
`(1-p) exp t < 1`.

This is the pure series identity behind the geometric MGF used in Janson's
tail bound. -/
theorem shifted_geometric_exp_series_hasSum {p t : ℝ}
    (_hp_pos : 0 < p) (hp_le_one : p ≤ 1)
    (hconv : (1 - p) * Real.exp t < 1) :
    HasSum (fun n : ℕ =>
      Real.exp (t * ((n : ℝ) + 1)) * geometricPMFReal p n)
      (Real.exp t * p * (1 - (1 - p) * Real.exp t)⁻¹) := by
  let r : ℝ := (1 - p) * Real.exp t
  have hr_nonneg : 0 ≤ r := by
    exact mul_nonneg (sub_nonneg.mpr hp_le_one) (Real.exp_pos t).le
  have hr_lt_one : r < 1 := by
    simpa [r] using hconv
  have hgeo : HasSum (fun n : ℕ => r ^ n) (1 - r)⁻¹ :=
    hasSum_geometric_of_lt_one hr_nonneg hr_lt_one
  have hmul :
      HasSum (fun n : ℕ => (Real.exp t * p) * r ^ n)
        (Real.exp t * p * (1 - r)⁻¹) :=
    hgeo.mul_left (Real.exp t * p)
  convert hmul using 1 with n
  · funext n
    rw [geometricPMFReal]
    have harg : t * ((n : ℝ) + 1) = t + (n : ℝ) * t := by ring
    rw [harg, Real.exp_add, Real.exp_nat_mul]
    simp [r, mul_pow, mul_assoc, mul_left_comm, mul_comm]

/-- The real mass of Mathlib's geometric PMF is `geometricPMFReal`. -/
theorem geometricPMF_toReal_eq {p : ℝ} (hp_pos : 0 < p) (hp_le_one : p ≤ 1) (n : ℕ) :
    ((geometricPMF hp_pos hp_le_one n).toReal : ℝ) = geometricPMFReal p n := by
  change (ENNReal.ofReal (geometricPMFReal p n)).toReal = geometricPMFReal p n
  rw [ENNReal.toReal_ofReal (geometricPMFReal_nonneg hp_pos hp_le_one)]

/-- Shifted-geometric exponential series, written with Mathlib's `PMF` weights. -/
theorem shifted_geometric_exp_pmf_hasSum {p t : ℝ}
    (hp_pos : 0 < p) (hp_le_one : p ≤ 1)
    (hconv : (1 - p) * Real.exp t < 1) :
    HasSum (fun n : ℕ =>
      ((geometricPMF hp_pos hp_le_one n).toReal : ℝ) *
        Real.exp (t * ((n : ℝ) + 1)))
      (Real.exp t * p * (1 - (1 - p) * Real.exp t)⁻¹) := by
  convert shifted_geometric_exp_series_hasSum hp_pos hp_le_one hconv using 1
  funext n
  rw [geometricPMF_toReal_eq hp_pos hp_le_one n]
  ring

/-- The closed form of the shifted-geometric exponential `tsum`. -/
theorem shifted_geometric_exp_pmf_tsum {p t : ℝ}
    (hp_pos : 0 < p) (hp_le_one : p ≤ 1)
    (hconv : (1 - p) * Real.exp t < 1) :
    (∑' n : ℕ,
      ((geometricPMF hp_pos hp_le_one n).toReal : ℝ) *
        Real.exp (t * ((n : ℝ) + 1))) =
      Real.exp t * p * (1 - (1 - p) * Real.exp t)⁻¹ :=
  (shifted_geometric_exp_pmf_hasSum hp_pos hp_le_one hconv).tsum_eq

/-- The shifted-geometric exponential integral under Mathlib's geometric measure.

This is the MGF formula before unfolding `mgf`: the random variable is
`n ↦ n + 1`, while Mathlib's geometric PMF puts mass on the number of failures
`n`. -/
theorem shifted_geometric_exp_integral_geometricMeasure {p t : ℝ}
    (hp_pos : 0 < p) (hp_le_one : p ≤ 1)
    (hconv : (1 - p) * Real.exp t < 1) :
    (∫ n : ℕ, Real.exp (t * ((n : ℝ) + 1)) ∂geometricMeasure hp_pos hp_le_one) =
      Real.exp t * p * (1 - (1 - p) * Real.exp t)⁻¹ := by
  rw [geometricMeasure]
  rw [← Measure.sum_smul_dirac (geometricPMF hp_pos hp_le_one).toMeasure]
  rw [MeasureTheory.integral_sum_dirac]
  · trans (∑' n : ℕ,
        ((geometricPMF hp_pos hp_le_one n).toReal : ℝ) *
          Real.exp (t * ((n : ℝ) + 1)))
    · congr with n
      rw [PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton n)]
      simp [smul_eq_mul]
    · exact shifted_geometric_exp_pmf_tsum hp_pos hp_le_one hconv
  · intro n
    finiteness

/-- Moment-generating function of the shifted geometric waiting time. -/
theorem shifted_geometric_mgf_geometricMeasure {p t : ℝ}
    (hp_pos : 0 < p) (hp_le_one : p ≤ 1)
    (hconv : (1 - p) * Real.exp t < 1) :
    mgf (fun n : ℕ => (n : ℝ) + 1) (geometricMeasure hp_pos hp_le_one) t =
      Real.exp t * p * (1 - (1 - p) * Real.exp t)⁻¹ := by
  rw [mgf]
  exact shifted_geometric_exp_integral_geometricMeasure hp_pos hp_le_one hconv

/-- For lower-tail Chernoff parameters `t ≤ 0`, the shifted-geometric MGF
convergence side condition is automatic. -/
theorem shifted_geometric_mgf_converges_of_nonpos {p t : ℝ}
    (hp_pos : 0 < p) (hp_le_one : p ≤ 1) (ht : t ≤ 0) :
    (1 - p) * Real.exp t < 1 := by
  have h_one_sub_nonneg : 0 ≤ 1 - p := sub_nonneg.mpr hp_le_one
  have h_one_sub_lt : 1 - p < 1 := by linarith
  have h_exp_le_one : Real.exp t ≤ 1 := Real.exp_le_one_iff.mpr ht
  calc
    (1 - p) * Real.exp t ≤ (1 - p) * 1 :=
      mul_le_mul_of_nonneg_left h_exp_le_one h_one_sub_nonneg
    _ < 1 := by simpa using h_one_sub_lt

/-- Lower-tail-friendly form of the shifted-geometric MGF formula. -/
theorem shifted_geometric_mgf_geometricMeasure_of_nonpos {p t : ℝ}
    (hp_pos : 0 < p) (hp_le_one : p ≤ 1) (ht : t ≤ 0) :
    mgf (fun n : ℕ => (n : ℝ) + 1) (geometricMeasure hp_pos hp_le_one) t =
      Real.exp t * p * (1 - (1 - p) * Real.exp t)⁻¹ :=
  shifted_geometric_mgf_geometricMeasure hp_pos hp_le_one
    (shifted_geometric_mgf_converges_of_nonpos hp_pos hp_le_one ht)

/-- MGF formula for any real random variable distributed as the shifted geometric
waiting time. -/
theorem shifted_geometric_mgf_of_identDistrib {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → ℝ) {p t : ℝ}
    (hp_pos : 0 < p) (hp_le_one : p ≤ 1)
    (hconv : (1 - p) * Real.exp t < 1)
    (hident : IdentDistrib X (fun n : ℕ => (n : ℝ) + 1) P
      (geometricMeasure hp_pos hp_le_one)) :
    mgf X P t = Real.exp t * p * (1 - (1 - p) * Real.exp t)⁻¹ := by
  rw [mgf_congr_identDistrib hident]
  exact shifted_geometric_mgf_geometricMeasure hp_pos hp_le_one hconv

/-- Lower-tail-friendly form for any random variable distributed as a shifted
geometric waiting time. -/
theorem shifted_geometric_mgf_of_identDistrib_of_nonpos {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → ℝ) {p t : ℝ}
    (hp_pos : 0 < p) (hp_le_one : p ≤ 1) (ht : t ≤ 0)
    (hident : IdentDistrib X (fun n : ℕ => (n : ℝ) + 1) P
      (geometricMeasure hp_pos hp_le_one)) :
    mgf X P t = Real.exp t * p * (1 - (1 - p) * Real.exp t)⁻¹ :=
  shifted_geometric_mgf_of_identDistrib (P := P) (X := X) hp_pos hp_le_one
    (shifted_geometric_mgf_converges_of_nonpos hp_pos hp_le_one ht) hident

/-- Product form of the shifted-geometric MGF formula for finitely many
waiting-time variables. -/
theorem shifted_geometric_product_mgf_of_identDistrib {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (k : ℕ) (X : ℕ → Ω → ℝ) (p : ℕ → ℝ) (t : ℝ)
    (hp_pos : ∀ i ∈ Finset.range k, 0 < p i)
    (hp_le_one : ∀ i ∈ Finset.range k, p i ≤ 1)
    (hconv : ∀ i ∈ Finset.range k, (1 - p i) * Real.exp t < 1)
    (hident : ∀ i (hi : i ∈ Finset.range k),
      IdentDistrib (X i) (fun n : ℕ => (n : ℝ) + 1) P
        (geometricMeasure (hp_pos i hi) (hp_le_one i hi))) :
    (∏ i ∈ Finset.range k, mgf (X i) P t) =
      ∏ i ∈ Finset.range k,
        Real.exp t * p i * (1 - (1 - p i) * Real.exp t)⁻¹ := by
  refine Finset.prod_congr rfl ?_
  intro i hi
  exact shifted_geometric_mgf_of_identDistrib
    (P := P) (X := X i) (hp_pos := hp_pos i hi) (hp_le_one := hp_le_one i hi)
    (hconv := hconv i hi) (hident := hident i hi)

/-- Product form of the shifted-geometric MGF formula for lower-tail parameters.

When `t ≤ 0`, each shifted geometric MGF is automatically inside its convergence
domain, so the product formula only needs the distributional identifications. -/
theorem shifted_geometric_product_mgf_of_identDistrib_of_nonpos {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (k : ℕ) (X : ℕ → Ω → ℝ) (p : ℕ → ℝ) (t : ℝ)
    (hp_pos : ∀ i ∈ Finset.range k, 0 < p i)
    (hp_le_one : ∀ i ∈ Finset.range k, p i ≤ 1)
    (ht : t ≤ 0)
    (hident : ∀ i (hi : i ∈ Finset.range k),
      IdentDistrib (X i) (fun n : ℕ => (n : ℝ) + 1) P
        (geometricMeasure (hp_pos i hi) (hp_le_one i hi))) :
    (∏ i ∈ Finset.range k, mgf (X i) P t) =
      ∏ i ∈ Finset.range k,
        Real.exp t * p i * (1 - (1 - p i) * Real.exp t)⁻¹ := by
  exact shifted_geometric_product_mgf_of_identDistrib
    (P := P) (k := k) (X := X) (p := p) (t := t)
    hp_pos hp_le_one
    (fun i hi => shifted_geometric_mgf_converges_of_nonpos
      (hp_pos i hi) (hp_le_one i hi) ht)
    hident

/-- Positivity of the denominator in the shifted-geometric closed-form MGF. -/
theorem shifted_geometric_mgf_closedForm_denom_pos {p t : ℝ}
    (hconv : (1 - p) * Real.exp t < 1) :
    0 < 1 - (1 - p) * Real.exp t := by
  linarith

/-- Positivity of the shifted-geometric closed-form MGF. -/
theorem shifted_geometric_mgf_closedForm_pos {p t : ℝ}
    (hp_pos : 0 < p) (hconv : (1 - p) * Real.exp t < 1) :
    0 < Real.exp t * p * (1 - (1 - p) * Real.exp t)⁻¹ := by
  exact mul_pos (mul_pos (Real.exp_pos t) hp_pos)
    (inv_pos.mpr (shifted_geometric_mgf_closedForm_denom_pos hconv))

/-- Integrability of the exponential of a finite independent sum of
shifted-geometric variables, derived from the positive closed-form MGF. -/
theorem shifted_geometric_integrable_exp_sum_of_identDistrib {Ω : Type*}
    [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (k : ℕ) (X : ℕ → Ω → ℝ) (p : ℕ → ℝ) (t : ℝ)
    (h_indep : iIndepFun X P)
    (h_meas : ∀ i, AEMeasurable (X i) P)
    (hp_pos : ∀ i ∈ Finset.range k, 0 < p i)
    (hp_le_one : ∀ i ∈ Finset.range k, p i ≤ 1)
    (hconv : ∀ i ∈ Finset.range k, (1 - p i) * Real.exp t < 1)
    (hident : ∀ i (hi : i ∈ Finset.range k),
      IdentDistrib (X i) (fun n : ℕ => (n : ℝ) + 1) P
        (geometricMeasure (hp_pos i hi) (hp_le_one i hi))) :
    Integrable (fun ω => Real.exp (t * ∑ i ∈ Finset.range k, X i ω)) P := by
  haveI : NeZero P := ⟨IsProbabilityMeasure.ne_zero P⟩
  have hfun :
      (fun ω => ∑ i ∈ Finset.range k, X i ω) =ᵐ[P]
        (∑ i ∈ Finset.range k, X i) := by
    exact Filter.Eventually.of_forall (by
      intro ω
      simp [Finset.sum_apply])
  have h_sum_mgf :
      mgf (fun ω => ∑ i ∈ Finset.range k, X i ω) P t =
        ∏ i ∈ Finset.range k, mgf (X i) P t := by
    rw [mgf_congr hfun]
    exact h_indep.mgf_sum₀ h_meas (Finset.range k)
  have h_prod_pos : 0 < ∏ i ∈ Finset.range k, mgf (X i) P t := by
    refine Finset.prod_pos ?_
    intro i hi
    rw [shifted_geometric_mgf_of_identDistrib
      (P := P) (X := X i) (hp_pos := hp_pos i hi)
      (hp_le_one := hp_le_one i hi) (hconv := hconv i hi)
      (hident := hident i hi)]
    exact shifted_geometric_mgf_closedForm_pos (hp_pos i hi) (hconv i hi)
  have hmgf_pos :
      0 < mgf (fun ω => ∑ i ∈ Finset.range k, X i ω) P t := by
    simpa [h_sum_mgf] using h_prod_pos
  exact (mgf_pos_iff.mp hmgf_pos)

/-- Logarithm of the shifted-geometric closed-form MGF. -/
theorem shifted_geometric_mgf_closedForm_log_eq {p t : ℝ}
    (hp_pos : 0 < p) (hconv : (1 - p) * Real.exp t < 1) :
    Real.log (Real.exp t * p * (1 - (1 - p) * Real.exp t)⁻¹) =
      t + Real.log p - Real.log (1 - (1 - p) * Real.exp t) := by
  have hden_pos : 0 < 1 - (1 - p) * Real.exp t :=
    shifted_geometric_mgf_closedForm_denom_pos hconv
  have hexp_ne : Real.exp t ≠ 0 := (Real.exp_pos t).ne'
  have hp_ne : p ≠ 0 := hp_pos.ne'
  have hden_ne : 1 - (1 - p) * Real.exp t ≠ 0 := hden_pos.ne'
  rw [mul_assoc]
  rw [Real.log_mul hexp_ne (mul_ne_zero hp_ne (inv_ne_zero hden_ne))]
  rw [Real.log_mul hp_ne (inv_ne_zero hden_ne)]
  rw [Real.log_exp, Real.log_inv]
  ring

/-- Denominator conversion used in Janson's geometric MGF estimate. -/
theorem shifted_geometric_mgf_closedForm_denom_eq_expNeg_mul (p t : ℝ) :
    1 - (1 - p) * Real.exp t =
      Real.exp t * (Real.exp (-t) - 1 + p) := by
  rw [Real.exp_neg]
  field_simp [(Real.exp_pos t).ne']
  ring

/-- Janson's alternate shifted-geometric MGF closed form,
`p / (exp (-t) - 1 + p)`. -/
theorem shifted_geometric_mgf_closedForm_eq_expNeg {p t : ℝ}
    (hden : Real.exp (-t) - 1 + p ≠ 0) :
    Real.exp t * p * (1 - (1 - p) * Real.exp t)⁻¹ =
      p / (Real.exp (-t) - 1 + p) := by
  rw [shifted_geometric_mgf_closedForm_denom_eq_expNeg_mul]
  field_simp [(Real.exp_pos t).ne', hden]

/-- The denominator in Janson's alternate upper-tail form is positive when
`0 ≤ t < p`, using `1 - t ≤ exp (-t)`. -/
theorem shifted_geometric_mgf_expNeg_denom_pos_of_lt {p t : ℝ}
    (_hp_pos : 0 < p) (_ht_nonneg : 0 ≤ t) (ht_lt : t < p) :
    0 < Real.exp (-t) - 1 + p := by
  have h_exp : -t + 1 ≤ Real.exp (-t) := Real.add_one_le_exp (-t)
  have hpt_pos : 0 < p - t := sub_pos.mpr ht_lt
  linarith

/-- For upper-tail Chernoff parameters, `0 ≤ t < p` implies the shifted
geometric MGF is inside its convergence domain. -/
theorem shifted_geometric_mgf_converges_of_nonneg_lt {p t : ℝ}
    (hp_pos : 0 < p) (ht_nonneg : 0 ≤ t) (ht_lt : t < p) :
    (1 - p) * Real.exp t < 1 := by
  have hden_pos : 0 < Real.exp (-t) - 1 + p :=
    shifted_geometric_mgf_expNeg_denom_pos_of_lt hp_pos ht_nonneg ht_lt
  have hden₁_pos : 0 < 1 - (1 - p) * Real.exp t := by
    rw [shifted_geometric_mgf_closedForm_denom_eq_expNeg_mul]
    exact mul_pos (Real.exp_pos t) hden_pos
  linarith

/-- Janson's elementary upper-tail MGF comparison
`E exp(tX) ≤ p / (p - t)` for a shifted geometric `X`. -/
theorem shifted_geometric_mgf_closedForm_le_upper_crude {p t : ℝ}
    (hp_pos : 0 < p) (ht_nonneg : 0 ≤ t) (ht_lt : t < p) :
    Real.exp t * p * (1 - (1 - p) * Real.exp t)⁻¹ ≤ p / (p - t) := by
  have hden_pos : 0 < Real.exp (-t) - 1 + p :=
    shifted_geometric_mgf_expNeg_denom_pos_of_lt hp_pos ht_nonneg ht_lt
  have hpt_pos : 0 < p - t := sub_pos.mpr ht_lt
  have h_exp : -t + 1 ≤ Real.exp (-t) := Real.add_one_le_exp (-t)
  have hden_le : p - t ≤ Real.exp (-t) - 1 + p := by linarith
  rw [shifted_geometric_mgf_closedForm_eq_expNeg hden_pos.ne']
  exact div_le_div_of_nonneg_left hp_pos.le hpt_pos hden_le

/-- Logarithmic form of Janson's elementary upper-tail MGF comparison. -/
theorem shifted_geometric_mgf_closedForm_log_le_upper_crude {p t : ℝ}
    (hp_pos : 0 < p) (ht_nonneg : 0 ≤ t) (ht_lt : t < p) :
    t + Real.log p - Real.log (1 - (1 - p) * Real.exp t) ≤
      - Real.log (1 - t / p) := by
  have hden_pos : 0 < Real.exp (-t) - 1 + p :=
    shifted_geometric_mgf_expNeg_denom_pos_of_lt hp_pos ht_nonneg ht_lt
  have hden₁_pos : 0 < 1 - (1 - p) * Real.exp t := by
    rw [shifted_geometric_mgf_closedForm_denom_eq_expNeg_mul]
    exact mul_pos (Real.exp_pos t) hden_pos
  have hconv : (1 - p) * Real.exp t < 1 :=
    shifted_geometric_mgf_converges_of_nonneg_lt hp_pos ht_nonneg ht_lt
  have hM_pos :
      0 < Real.exp t * p * (1 - (1 - p) * Real.exp t)⁻¹ :=
    shifted_geometric_mgf_closedForm_pos hp_pos hconv
  have hpt_pos : 0 < p - t := sub_pos.mpr ht_lt
  have hratio_pos : 0 < p / (p - t) := div_pos hp_pos hpt_pos
  have hM_le :
      Real.exp t * p * (1 - (1 - p) * Real.exp t)⁻¹ ≤ p / (p - t) :=
    shifted_geometric_mgf_closedForm_le_upper_crude hp_pos ht_nonneg ht_lt
  have hlog_le :
      Real.log (Real.exp t * p * (1 - (1 - p) * Real.exp t)⁻¹) ≤
        Real.log (p / (p - t)) :=
    Real.log_le_log hM_pos hM_le
  have hsub_ne : 1 - t / p ≠ 0 := by
    have htdiv : t / p < 1 := by
      rw [← div_self hp_pos.ne']
      exact div_lt_div_of_pos_right ht_lt hp_pos
    linarith
  have hlog_ratio : Real.log (p / (p - t)) = - Real.log (1 - t / p) := by
    have hratio_eq : p / (p - t) = (1 - t / p)⁻¹ := by
      field_simp [hp_pos.ne', hpt_pos.ne', hsub_ne]
    rw [hratio_eq, Real.log_inv]
  rw [← shifted_geometric_mgf_closedForm_log_eq hp_pos hconv]
  exact hlog_le.trans_eq hlog_ratio

/-- Lower-tail denominator conversion, written with a nonnegative parameter
`s` and Chernoff parameter `-s`. -/
theorem shifted_geometric_mgf_closedForm_lower_denom_eq_exp_mul (p s : ℝ) :
    1 - (1 - p) * Real.exp (-s) =
      Real.exp (-s) * (Real.exp s - 1 + p) := by
  simpa [neg_neg] using
    shifted_geometric_mgf_closedForm_denom_eq_expNeg_mul p (-s)

/-- The denominator in Janson's alternate lower-tail form is positive for
`s ≥ 0`, using `1 + s ≤ exp s`. -/
theorem shifted_geometric_mgf_exp_denom_pos_of_nonneg {p s : ℝ}
    (hp_pos : 0 < p) (hs_nonneg : 0 ≤ s) :
    0 < Real.exp s - 1 + p := by
  have h_exp : s + 1 ≤ Real.exp s := Real.add_one_le_exp s
  linarith

/-- Janson's elementary lower-tail MGF comparison
`E exp(-sX) ≤ p / (p + s)` for a shifted geometric `X`. -/
theorem shifted_geometric_mgf_closedForm_le_lower_crude {p s : ℝ}
    (hp_pos : 0 < p) (hs_nonneg : 0 ≤ s) :
    Real.exp (-s) * p * (1 - (1 - p) * Real.exp (-s))⁻¹ ≤ p / (p + s) := by
  have hden_pos : 0 < Real.exp s - 1 + p :=
    shifted_geometric_mgf_exp_denom_pos_of_nonneg hp_pos hs_nonneg
  have hps_pos : 0 < p + s := by linarith
  have h_exp : s + 1 ≤ Real.exp s := Real.add_one_le_exp s
  have hden_le : p + s ≤ Real.exp s - 1 + p := by linarith
  have hden_ne : Real.exp (-(-s)) - 1 + p ≠ 0 := by
    simpa [neg_neg] using hden_pos.ne'
  rw [shifted_geometric_mgf_closedForm_eq_expNeg hden_ne]
  simpa [neg_neg, add_comm, add_left_comm, add_assoc] using
    div_le_div_of_nonneg_left hp_pos.le hps_pos hden_le

/-- Logarithmic form of Janson's elementary lower-tail MGF comparison. -/
theorem shifted_geometric_mgf_closedForm_log_le_lower_crude {p s : ℝ}
    (hp_pos : 0 < p) (hs_nonneg : 0 ≤ s) :
    -s + Real.log p - Real.log (1 - (1 - p) * Real.exp (-s)) ≤
      - Real.log (1 + s / p) := by
  have hden_pos : 0 < Real.exp s - 1 + p :=
    shifted_geometric_mgf_exp_denom_pos_of_nonneg hp_pos hs_nonneg
  have hden₁_pos : 0 < 1 - (1 - p) * Real.exp (-s) := by
    rw [shifted_geometric_mgf_closedForm_lower_denom_eq_exp_mul]
    exact mul_pos (Real.exp_pos (-s)) hden_pos
  have hconv : (1 - p) * Real.exp (-s) < 1 := by linarith
  have hM_pos :
      0 < Real.exp (-s) * p * (1 - (1 - p) * Real.exp (-s))⁻¹ :=
    shifted_geometric_mgf_closedForm_pos hp_pos hconv
  have hps_pos : 0 < p + s := by linarith
  have hM_le :
      Real.exp (-s) * p * (1 - (1 - p) * Real.exp (-s))⁻¹ ≤ p / (p + s) :=
    shifted_geometric_mgf_closedForm_le_lower_crude hp_pos hs_nonneg
  have hlog_le :
      Real.log (Real.exp (-s) * p * (1 - (1 - p) * Real.exp (-s))⁻¹) ≤
        Real.log (p / (p + s)) :=
    Real.log_le_log hM_pos hM_le
  have hsum_ne : 1 + s / p ≠ 0 := by
    have hsdiv_nonneg : 0 ≤ s / p := div_nonneg hs_nonneg hp_pos.le
    linarith
  have hlog_ratio : Real.log (p / (p + s)) = - Real.log (1 + s / p) := by
    have hratio_eq : p / (p + s) = (1 + s / p)⁻¹ := by
      field_simp [hp_pos.ne', hps_pos.ne', hsum_ne]
    rw [hratio_eq, Real.log_inv]
  rw [← shifted_geometric_mgf_closedForm_log_eq hp_pos hconv]
  exact hlog_le.trans_eq hlog_ratio

/-- Convexity scaling for the upper-tail logarithmic endpoint:
`-log(1 - a b) ≤ a * -log(1 - b)` for `0 ≤ a ≤ 1` and `0 ≤ b < 1`. -/
theorem neg_log_one_sub_mul_le_mul_neg_log_one_sub {a b : ℝ}
    (ha_nonneg : 0 ≤ a) (ha_le_one : a ≤ 1)
    (_hb_nonneg : 0 ≤ b) (hb_lt_one : b < 1) :
    -Real.log (1 - a * b) ≤ a * (-Real.log (1 - b)) := by
  have hweight_nonneg : 0 ≤ 1 - a := sub_nonneg.mpr ha_le_one
  have hweight_sum : a + (1 - a) = 1 := by ring
  have hx : 1 - b ∈ Set.Ioi (0 : ℝ) := sub_pos.mpr hb_lt_one
  have hy : (1 : ℝ) ∈ Set.Ioi (0 : ℝ) := by
    change (0 : ℝ) < 1
    exact zero_lt_one
  have hconc :=
    strictConcaveOn_log_Ioi.concaveOn.2 hx hy ha_nonneg hweight_nonneg hweight_sum
  have hlog :
      a * Real.log (1 - b) ≤ Real.log (1 - a * b) := by
    have hleft :
        a * Real.log (1 - b) + (1 - a) * Real.log 1 =
          a * Real.log (1 - b) := by
      rw [Real.log_one]
      ring
    have harg : a * (1 - b) + (1 - a) * 1 = 1 - a * b := by ring
    calc
      a * Real.log (1 - b)
          = a * Real.log (1 - b) + (1 - a) * Real.log 1 := hleft.symm
      _ ≤ Real.log (a * (1 - b) + (1 - a) * 1) := by
          simpa [smul_eq_mul] using hconc
      _ = Real.log (1 - a * b) := by rw [harg]
  linarith

/-- Convexity scaling for the lower-tail logarithmic endpoint:
`-log(1 + a y) ≤ a * -log(1 + y)` for `0 ≤ a ≤ 1` and `0 ≤ y`. -/
theorem neg_log_one_add_mul_le_mul_neg_log_one_add {a y : ℝ}
    (ha_nonneg : 0 ≤ a) (ha_le_one : a ≤ 1) (hy_nonneg : 0 ≤ y) :
    -Real.log (1 + a * y) ≤ a * (-Real.log (1 + y)) := by
  have hweight_nonneg : 0 ≤ 1 - a := sub_nonneg.mpr ha_le_one
  have hweight_sum : a + (1 - a) = 1 := by ring
  have hx : 1 + y ∈ Set.Ioi (0 : ℝ) := by
    change (0 : ℝ) < 1 + y
    linarith
  have hy : (1 : ℝ) ∈ Set.Ioi (0 : ℝ) := by
    change (0 : ℝ) < 1
    exact zero_lt_one
  have hconc :=
    strictConcaveOn_log_Ioi.concaveOn.2 hx hy ha_nonneg hweight_nonneg hweight_sum
  have hlog :
      a * Real.log (1 + y) ≤ Real.log (1 + a * y) := by
    have hleft :
        a * Real.log (1 + y) + (1 - a) * Real.log 1 =
          a * Real.log (1 + y) := by
      rw [Real.log_one]
      ring
    have harg : a * (1 + y) + (1 - a) * 1 = 1 + a * y := by ring
    calc
      a * Real.log (1 + y)
          = a * Real.log (1 + y) + (1 - a) * Real.log 1 := hleft.symm
      _ ≤ Real.log (a * (1 + y) + (1 - a) * 1) := by
          simpa [smul_eq_mul] using hconc
      _ = Real.log (1 + a * y) := by rw [harg]
  linarith

/-- Upper-tail pointwise MGF bound after the Janson scaling substitution
`t / p = a * b`. -/
theorem shifted_geometric_mgf_closedForm_log_le_upper_scaled {p t a b : ℝ}
    (hp_pos : 0 < p) (ht_nonneg : 0 ≤ t) (ht_lt : t < p)
    (ha_nonneg : 0 ≤ a) (ha_le_one : a ≤ 1)
    (hb_nonneg : 0 ≤ b) (hb_lt_one : b < 1)
    (ht_div : t / p = a * b) :
    t + Real.log p - Real.log (1 - (1 - p) * Real.exp t) ≤
      a * (-Real.log (1 - b)) := by
  have hcrude :=
    shifted_geometric_mgf_closedForm_log_le_upper_crude hp_pos ht_nonneg ht_lt
  have hscale :=
    neg_log_one_sub_mul_le_mul_neg_log_one_sub
      ha_nonneg ha_le_one hb_nonneg hb_lt_one
  calc
    t + Real.log p - Real.log (1 - (1 - p) * Real.exp t)
        ≤ -Real.log (1 - t / p) := hcrude
    _ = -Real.log (1 - a * b) := by rw [ht_div]
    _ ≤ a * (-Real.log (1 - b)) := hscale

/-- Upper-tail pointwise Janson MGF inequality for the optimized parameter
`t = (1 - 1 / λ) * p_min`.  The remaining hypotheses are exactly the local
parameter facts: `p_min` is nonnegative and no larger than the current
geometric success probability `p`. -/
theorem shifted_geometric_mgf_closedForm_log_le_upper_janson_point {p p_min lam t : ℝ}
    (hp_pos : 0 < p) (hpmin_nonneg : 0 ≤ p_min) (hpmin_le : p_min ≤ p)
    (hlam_ge_one : 1 ≤ lam)
    (ht : t = (1 - lam⁻¹) * p_min) :
    t + Real.log p - Real.log (1 - (1 - p) * Real.exp t) ≤
      t * lam * p⁻¹ - p_min * p⁻¹ * (lam - 1 - Real.log lam) := by
  let a : ℝ := p_min / p
  let b : ℝ := 1 - lam⁻¹
  have hlam_pos : 0 < lam := zero_lt_one.trans_le hlam_ge_one
  have ha_nonneg : 0 ≤ a := div_nonneg hpmin_nonneg hp_pos.le
  have ha_le_one : a ≤ 1 := by
    dsimp [a]
    rw [← div_self hp_pos.ne']
    exact div_le_div_of_nonneg_right hpmin_le hp_pos.le
  have hb_nonneg : 0 ≤ b := by
    have hinv_le : lam⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hlam_ge_one
    dsimp [b]
    linarith
  have hb_lt_one : b < 1 := by
    have hinv_pos : 0 < lam⁻¹ := inv_pos.mpr hlam_pos
    dsimp [b]
    linarith
  have ht_nonneg : 0 ≤ t := by
    rw [ht]
    exact mul_nonneg hb_nonneg hpmin_nonneg
  have ht_lt : t < p := by
    have ht_le : t ≤ b * p := by
      rw [ht]
      simpa [b] using mul_le_mul_of_nonneg_left hpmin_le hb_nonneg
    have hb_mul_lt : b * p < 1 * p := mul_lt_mul_of_pos_right hb_lt_one hp_pos
    linarith
  have ht_div : t / p = a * b := by
    rw [ht]
    dsimp [a, b]
    field_simp [hp_pos.ne']
  have hscaled :
      t + Real.log p - Real.log (1 - (1 - p) * Real.exp t) ≤
        a * (-Real.log (1 - b)) :=
    shifted_geometric_mgf_closedForm_log_le_upper_scaled
      hp_pos ht_nonneg ht_lt ha_nonneg ha_le_one hb_nonneg hb_lt_one ht_div
  have hendpoint :
      a * (-Real.log (1 - b)) =
        t * lam * p⁻¹ - p_min * p⁻¹ * (lam - 1 - Real.log lam) := by
    have hlog :
        -Real.log (1 - (1 - lam⁻¹)) = Real.log lam := by
      have harg : 1 - (1 - lam⁻¹) = lam⁻¹ := by ring
      rw [harg, Real.log_inv]
      ring
    rw [ht]
    dsimp [a, b]
    rw [hlog]
    field_simp [hp_pos.ne', hlam_pos.ne']
    ring
  exact hscaled.trans_eq hendpoint

/-- Lower-tail pointwise MGF bound after the Janson scaling substitution
`s / p = a * y`, where the Chernoff parameter is `-s`. -/
theorem shifted_geometric_mgf_closedForm_log_le_lower_scaled {p s a y : ℝ}
    (hp_pos : 0 < p) (hs_nonneg : 0 ≤ s)
    (ha_nonneg : 0 ≤ a) (ha_le_one : a ≤ 1) (hy_nonneg : 0 ≤ y)
    (hs_div : s / p = a * y) :
    -s + Real.log p - Real.log (1 - (1 - p) * Real.exp (-s)) ≤
      a * (-Real.log (1 + y)) := by
  have hcrude :=
    shifted_geometric_mgf_closedForm_log_le_lower_crude hp_pos hs_nonneg
  have hscale :=
    neg_log_one_add_mul_le_mul_neg_log_one_add
      ha_nonneg ha_le_one hy_nonneg
  calc
    -s + Real.log p - Real.log (1 - (1 - p) * Real.exp (-s))
        ≤ -Real.log (1 + s / p) := hcrude
    _ = -Real.log (1 + a * y) := by rw [hs_div]
    _ ≤ a * (-Real.log (1 + y)) := hscale

/-- Lower-tail pointwise Janson MGF inequality for the optimized negative
parameter `t = -s`, where `s = (1 / λ - 1) * p_min`. -/
theorem shifted_geometric_mgf_closedForm_log_le_lower_janson_point {p p_min lam s : ℝ}
    (hp_pos : 0 < p) (hpmin_nonneg : 0 ≤ p_min) (hpmin_le : p_min ≤ p)
    (hlam_pos : 0 < lam) (hlam_le_one : lam ≤ 1)
    (hs : s = (lam⁻¹ - 1) * p_min) :
    -s + Real.log p - Real.log (1 - (1 - p) * Real.exp (-s)) ≤
      (-s) * lam * p⁻¹ - p_min * p⁻¹ * (lam - 1 - Real.log lam) := by
  let a : ℝ := p_min / p
  let y : ℝ := lam⁻¹ - 1
  have ha_nonneg : 0 ≤ a := div_nonneg hpmin_nonneg hp_pos.le
  have ha_le_one : a ≤ 1 := by
    dsimp [a]
    rw [← div_self hp_pos.ne']
    exact div_le_div_of_nonneg_right hpmin_le hp_pos.le
  have hy_nonneg : 0 ≤ y := by
    have hone_le_inv : 1 ≤ lam⁻¹ := (one_le_inv₀ hlam_pos).2 hlam_le_one
    dsimp [y]
    linarith
  have hs_nonneg : 0 ≤ s := by
    rw [hs]
    exact mul_nonneg hy_nonneg hpmin_nonneg
  have hs_div : s / p = a * y := by
    rw [hs]
    dsimp [a, y]
    field_simp [hp_pos.ne']
  have hscaled :
      -s + Real.log p - Real.log (1 - (1 - p) * Real.exp (-s)) ≤
        a * (-Real.log (1 + y)) :=
    shifted_geometric_mgf_closedForm_log_le_lower_scaled
      hp_pos hs_nonneg ha_nonneg ha_le_one hy_nonneg hs_div
  have hendpoint :
      a * (-Real.log (1 + y)) =
        (-s) * lam * p⁻¹ - p_min * p⁻¹ * (lam - 1 - Real.log lam) := by
    have hlog : -Real.log (1 + (lam⁻¹ - 1)) = Real.log lam := by
      have harg : 1 + (lam⁻¹ - 1) = lam⁻¹ := by ring
      rw [harg, Real.log_inv]
      ring
    rw [hs]
    dsimp [a, y]
    rw [hlog]
    field_simp [hp_pos.ne', hlam_pos.ne']
    ring
  exact hscaled.trans_eq hendpoint

/-- Logarithm of the finite product of shifted-geometric closed-form MGFs. -/
theorem shifted_geometric_product_mgf_closedForm_log_eq
    (k : ℕ) (p : ℕ → ℝ) (t : ℝ)
    (hp_pos : ∀ i ∈ Finset.range k, 0 < p i)
    (hconv : ∀ i ∈ Finset.range k, (1 - p i) * Real.exp t < 1) :
    Real.log
        (∏ i ∈ Finset.range k,
          Real.exp t * p i * (1 - (1 - p i) * Real.exp t)⁻¹) =
      ∑ i ∈ Finset.range k,
        (t + Real.log (p i) - Real.log (1 - (1 - p i) * Real.exp t)) := by
  rw [Real.log_prod]
  · refine Finset.sum_congr rfl ?_
    intro i hi
    exact shifted_geometric_mgf_closedForm_log_eq (hp_pos i hi) (hconv i hi)
  · intro i hi
    exact (shifted_geometric_mgf_closedForm_pos (hp_pos i hi) (hconv i hi)).ne'

/-- Convert a logarithmic closed-form MGF bound into the exponential product
bound used by Chernoff. -/
theorem shifted_geometric_product_mgf_closedForm_mul_le_exp_of_log_bound
    (k : ℕ) (p : ℕ → ℝ) (t threshold B : ℝ)
    (hp_pos : ∀ i ∈ Finset.range k, 0 < p i)
    (hconv : ∀ i ∈ Finset.range k, (1 - p i) * Real.exp t < 1)
    (hlog :
      -t * threshold +
          ∑ i ∈ Finset.range k,
            (t + Real.log (p i) - Real.log (1 - (1 - p i) * Real.exp t)) ≤ B) :
    Real.exp (-t * threshold) *
        (∏ i ∈ Finset.range k,
          Real.exp t * p i * (1 - (1 - p i) * Real.exp t)⁻¹) ≤
      Real.exp B := by
  have hprod_pos :
      0 < ∏ i ∈ Finset.range k,
        Real.exp t * p i * (1 - (1 - p i) * Real.exp t)⁻¹ := by
    exact Finset.prod_pos (fun i hi =>
      shifted_geometric_mgf_closedForm_pos (hp_pos i hi) (hconv i hi))
  have hlhs_pos :
      0 < Real.exp (-t * threshold) *
        (∏ i ∈ Finset.range k,
          Real.exp t * p i * (1 - (1 - p i) * Real.exp t)⁻¹) :=
    mul_pos (Real.exp_pos _) hprod_pos
  rw [← Real.log_le_iff_le_exp hlhs_pos]
  calc
    Real.log
        (Real.exp (-t * threshold) *
          (∏ i ∈ Finset.range k,
            Real.exp t * p i * (1 - (1 - p i) * Real.exp t)⁻¹))
        = -t * threshold +
            Real.log
              (∏ i ∈ Finset.range k,
                Real.exp t * p i * (1 - (1 - p i) * Real.exp t)⁻¹) := by
          rw [Real.log_mul (Real.exp_pos _).ne' hprod_pos.ne', Real.log_exp]
    _ = -t * threshold +
          ∑ i ∈ Finset.range k,
            (t + Real.log (p i) - Real.log (1 - (1 - p i) * Real.exp t)) := by
          rw [shifted_geometric_product_mgf_closedForm_log_eq k p t hp_pos hconv]
    _ ≤ B := hlog

/-- Finite-sum algebra reducing the Janson logarithmic Chernoff bound to a
pointwise logarithmic inequality for each geometric parameter. -/
theorem janson_geom_log_chernoff_of_pointwise_bound
    (k : ℕ) (p : ℕ → ℝ) (t μ_X p_min lam : ℝ)
    (hμ_X : μ_X = ∑ i ∈ Finset.range k, (p i)⁻¹)
    (hpoint : ∀ i ∈ Finset.range k,
      t + Real.log (p i) - Real.log (1 - (1 - p i) * Real.exp t) ≤
        t * lam * (p i)⁻¹ -
          p_min * (p i)⁻¹ * (lam - 1 - Real.log lam)) :
    -t * (lam * μ_X) +
        ∑ i ∈ Finset.range k,
          (t + Real.log (p i) - Real.log (1 - (1 - p i) * Real.exp t)) ≤
      -p_min * μ_X * (lam - 1 - Real.log lam) := by
  let c : ℝ := lam - 1 - Real.log lam
  have hsum :
      ∑ i ∈ Finset.range k,
          (t + Real.log (p i) - Real.log (1 - (1 - p i) * Real.exp t)) ≤
        ∑ i ∈ Finset.range k, (t * lam * (p i)⁻¹ - p_min * (p i)⁻¹ * c) := by
    exact Finset.sum_le_sum (fun i hi => by simpa [c] using hpoint i hi)
  calc
    -t * (lam * μ_X) +
        ∑ i ∈ Finset.range k,
          (t + Real.log (p i) - Real.log (1 - (1 - p i) * Real.exp t))
        ≤ -t * (lam * μ_X) +
            ∑ i ∈ Finset.range k, (t * lam * (p i)⁻¹ - p_min * (p i)⁻¹ * c) := by
          exact add_le_add le_rfl hsum
    _ = -p_min * μ_X * c := by
          have hsum₁ :
              (∑ i ∈ Finset.range k, t * lam * (p i)⁻¹) =
                (t * lam) * ∑ i ∈ Finset.range k, (p i)⁻¹ := by
            rw [← Finset.mul_sum]
          have hsum₂ :
              (∑ i ∈ Finset.range k, p_min * (p i)⁻¹ * c) =
                (p_min * c) * ∑ i ∈ Finset.range k, (p i)⁻¹ := by
            calc
              (∑ i ∈ Finset.range k, p_min * (p i)⁻¹ * c)
                  = ∑ i ∈ Finset.range k, (p_min * c) * (p i)⁻¹ := by
                      refine Finset.sum_congr rfl ?_
                      intro i _hi
                      ring
              _ = (p_min * c) * ∑ i ∈ Finset.range k, (p i)⁻¹ := by
                      rw [← Finset.mul_sum]
          rw [hμ_X]
          rw [Finset.sum_sub_distrib]
          rw [hsum₁, hsum₂]
          ring

/-- The `p_min = ⨅ i ∈ range k, p_i` convention gives the expected pointwise
lower bound on each indexed success probability. -/
theorem janson_pmin_le_of_iInf {k : ℕ} {p : ℕ → ℝ} {p_min : ℝ}
    (hp_min : p_min = ⨅ i, ⨅ _hi : i ∈ Finset.range k, p i)
    (hp_nonneg : ∀ i ∈ Finset.range k, 0 ≤ p i) :
    ∀ i ∈ Finset.range k, p_min ≤ p i := by
  intro i hi
  rw [hp_min]
  have hbdd_outer :
      BddBelow (Set.range fun j => ⨅ _hj : j ∈ Finset.range k, p j) := by
    refine ⟨0, ?_⟩
    rintro y ⟨j, rfl⟩
    by_cases hj : j ∈ Finset.range k
    · haveI : Nonempty (j ∈ Finset.range k) := ⟨hj⟩
      exact le_ciInf (fun h => hp_nonneg j h)
    · simp [hj]
  have hbdd_inner :
      BddBelow (Set.range fun _hi : i ∈ Finset.range k => p i) := by
    refine ⟨p i, ?_⟩
    rintro y ⟨_hi, rfl⟩
    exact le_rfl
  exact (ciInf_le hbdd_outer i).trans (ciInf_le hbdd_inner hi)

/-- Nonnegativity of the finite `p_min` value, derived from nonnegative
success probabilities under the same `iInf` convention. -/
theorem janson_pmin_nonneg_of_iInf {k : ℕ} {p : ℕ → ℝ} {p_min : ℝ}
    (hp_min : p_min = ⨅ i, ⨅ _hi : i ∈ Finset.range k, p i)
    (hp_nonneg : ∀ i ∈ Finset.range k, 0 ≤ p i) :
    0 ≤ p_min := by
  rw [hp_min]
  refine le_ciInf ?_
  intro i
  by_cases hi : i ∈ Finset.range k
  · haveI : Nonempty (i ∈ Finset.range k) := ⟨hi⟩
    exact le_ciInf (fun h => hp_nonneg i h)
  · simp [hi]

/-- The Janson rate function `λ - 1 - log λ` is nonnegative on `λ > 0`. -/
theorem janson_log_rate_nonneg {lam : ℝ} (hlam_pos : 0 < lam) :
    0 ≤ lam - 1 - Real.log lam := by
  have hlog : Real.log lam ≤ lam - 1 := Real.log_le_sub_one_of_pos hlam_pos
  linarith

/-- The Janson rate function is positive away from `λ = 1`. -/
theorem janson_log_rate_pos_of_ne_one {lam : ℝ} (hlam_pos : 0 < lam) (hlam_ne : lam ≠ 1) :
    0 < lam - 1 - Real.log lam := by
  have hlog : Real.log lam < lam - 1 := Real.log_lt_sub_one_of_pos hlam_pos hlam_ne
  linarith

/-- Quadratic lower bound for the upper-tail Janson rate at `λ = 1 + ε`.
The constant is deliberately crude; it is the one used by the current
two-sided wrapper. -/
theorem janson_log_rate_upper_quadratic {ε : ℝ} (hε_nonneg : 0 ≤ ε) (hε_le_one : ε ≤ 1) :
    (1 + ε) - 1 - Real.log (1 + ε) ≥ (1 / 8 : ℝ) * ε ^ 2 := by
  let F : ℝ → ℝ := fun x => x - Real.log (1 + x) - (1 / 8 : ℝ) * x ^ 2
  have hderiv : ∀ y ∈ Set.Icc 0 ε, HasDerivAt F
      (1 - (1 + y)⁻¹ - (1 / 4 : ℝ) * y) y := by
    intro y hy
    have hy_pos : 0 < 1 + y := by
      have hy_nonneg : 0 ≤ y := hy.1
      linarith
    have hlog :
        HasDerivAt (fun x : ℝ => Real.log (1 + x)) ((1 + y)⁻¹) y := by
      have hinner := (hasDerivAt_const y (1 : ℝ)).add (hasDerivAt_id y)
      simpa [one_div, add_comm, add_left_comm, add_assoc] using hinner.log hy_pos.ne'
    have hquad :
        HasDerivAt (fun x : ℝ => (1 / 8 : ℝ) * x ^ 2) ((1 / 4 : ℝ) * y) y := by
      convert (((hasDerivAt_id y).pow 2).const_mul (1 / 8 : ℝ)) using 1
      simp only [id_eq]
      ring_nf
    unfold F
    exact ((hasDerivAt_id y).sub hlog).sub hquad
  have hmono : MonotoneOn F (Set.Icc 0 ε) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 ε)
      (fun y hy => (hderiv y hy).continuousAt.continuousWithinAt)
      (fun y hy => (hderiv y (interior_subset hy)).hasDerivWithinAt) ?_
    intro y hy
    simp only [interior_Icc, Set.mem_Ioo] at hy
    have hy_nonneg : 0 ≤ y := hy.1.le
    have hy_le_one : y ≤ 1 := hy.2.le.trans hε_le_one
    have h_inv_ge : (1 / 4 : ℝ) ≤ (1 + y)⁻¹ := by
      have hpos : 0 < 1 + y := by linarith
      have hle : 1 + y ≤ 4 := by linarith
      rw [show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ by norm_num]
      exact (inv_le_inv₀ (by norm_num : (0 : ℝ) < 4) hpos).2 hle
    have hfactor : 0 ≤ (1 + y)⁻¹ - (1 / 4 : ℝ) := sub_nonneg.mpr h_inv_ge
    have hrewrite :
        1 - (1 + y)⁻¹ - (1 / 4 : ℝ) * y =
          y * ((1 + y)⁻¹ - (1 / 4 : ℝ)) := by
      field_simp [show 1 + y ≠ 0 by linarith]
      ring
    rw [hrewrite]
    exact mul_nonneg hy_nonneg hfactor
  have hF0 : F 0 = 0 := by
    simp [F]
  have hFε_nonneg : 0 ≤ F ε := by
    have hle := hmono ⟨le_rfl, hε_nonneg⟩ ⟨hε_nonneg, le_rfl⟩ hε_nonneg
    simpa [hF0] using hle
  dsimp [F] at hFε_nonneg
  linarith

/-- Quadratic lower bound for the lower-tail Janson rate at `λ = 1 - ε`. -/
theorem janson_log_rate_lower_quadratic {ε : ℝ} (hε_nonneg : 0 ≤ ε) (hε_lt_one : ε < 1) :
    (1 - ε) - 1 - Real.log (1 - ε) ≥ (1 / 8 : ℝ) * ε ^ 2 := by
  let F : ℝ → ℝ := fun x => -x - Real.log (1 - x) - (1 / 8 : ℝ) * x ^ 2
  have hderiv : ∀ y ∈ Set.Icc 0 ε, HasDerivAt F
      (-1 + (1 - y)⁻¹ - (1 / 4 : ℝ) * y) y := by
    intro y hy
    have hy_lt_one : y < 1 := lt_of_le_of_lt hy.2 hε_lt_one
    have hy_pos : 0 < 1 - y := by linarith
    have hnegid : HasDerivAt (fun x : ℝ => -x) (-1 : ℝ) y := by
      simpa using (hasDerivAt_id y).neg
    have hlog :
        HasDerivAt (fun x : ℝ => Real.log (1 - x)) (-(1 - y)⁻¹) y := by
      have hinner := (hasDerivAt_const y (1 : ℝ)).sub (hasDerivAt_id y)
      convert hinner.log hy_pos.ne' using 1
      simp [id, div_eq_mul_inv]
    have hquad :
        HasDerivAt (fun x : ℝ => (1 / 8 : ℝ) * x ^ 2) ((1 / 4 : ℝ) * y) y := by
      convert (((hasDerivAt_id y).pow 2).const_mul (1 / 8 : ℝ)) using 1
      simp only [id_eq]
      ring_nf
    unfold F
    convert (hnegid.sub hlog).sub hquad using 1
    ring
  have hmono : MonotoneOn F (Set.Icc 0 ε) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 ε)
      (fun y hy => (hderiv y hy).continuousAt.continuousWithinAt)
      (fun y hy => (hderiv y (interior_subset hy)).hasDerivWithinAt) ?_
    intro y hy
    simp only [interior_Icc, Set.mem_Ioo] at hy
    have hy_nonneg : 0 ≤ y := hy.1.le
    have hy_lt_one : y < 1 := lt_trans hy.2 hε_lt_one
    have h_inv_ge : (1 / 4 : ℝ) ≤ (1 - y)⁻¹ := by
      have hpos : 0 < 1 - y := by linarith
      have hle : 1 - y ≤ 4 := by linarith
      rw [show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ by norm_num]
      exact (inv_le_inv₀ (by norm_num : (0 : ℝ) < 4) hpos).2 hle
    have hfactor : 0 ≤ (1 - y)⁻¹ - (1 / 4 : ℝ) := sub_nonneg.mpr h_inv_ge
    have hrewrite :
        -1 + (1 - y)⁻¹ - (1 / 4 : ℝ) * y =
          y * ((1 - y)⁻¹ - (1 / 4 : ℝ)) := by
      field_simp [show 1 - y ≠ 0 by linarith]
      ring
    rw [hrewrite]
    exact mul_nonneg hy_nonneg hfactor
  have hF0 : F 0 = 0 := by
    simp [F]
  have hFε_nonneg : 0 ≤ F ε := by
    have hle := hmono ⟨le_rfl, hε_nonneg⟩ ⟨hε_nonneg, le_rfl⟩ hε_nonneg
    simpa [hF0] using hle
  dsimp [F] at hFε_nonneg
  linarith

/-- Absorb the two-sided union-bound factor into a weaker exponential rate. -/
theorem two_mul_exp_neg_eighth_le_exp_neg_sixteenth {x : ℝ}
    (hx : (16 : ℝ) * Real.log 2 ≤ x) :
    2 * Real.exp (-(1 / 8 : ℝ) * x) ≤ Real.exp (-(1 / 16 : ℝ) * x) := by
  have hlog2_le : Real.log 2 ≤ (1 / 16 : ℝ) * x := by
    nlinarith
  have htwo_le : (2 : ℝ) ≤ Real.exp ((1 / 16 : ℝ) * x) := by
    exact (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 2)).mp hlog2_le
  calc
    2 * Real.exp (-(1 / 8 : ℝ) * x)
        ≤ Real.exp ((1 / 16 : ℝ) * x) * Real.exp (-(1 / 8 : ℝ) * x) := by
          exact mul_le_mul_of_nonneg_right htwo_le (Real.exp_pos _).le
    _ = Real.exp (-(1 / 16 : ℝ) * x) := by
          rw [← Real.exp_add]
          ring_nf

/-- **Cramér–Chernoff tail bound from MGF**.

Given a real RV `X` and a measurement `t > 0`, if the MGF satisfies
`mgf X P t ≤ M`, then `P[ε ≤ X] ≤ exp(-t·ε) · M`. This is just Markov's
inequality on `exp(t·X)` with the supplied MGF bound.

Used to derive Janson-style tail bounds from sub-exponential MGF estimates. -/
theorem chernoff_from_mgf {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P]
    (X : Ω → ℝ) (t : ℝ) (ht : 0 < t)
    (h_int : Integrable (fun ω => Real.exp (t * X ω)) P)
    (M : ℝ) (h_mgf_bound : mgf X P t ≤ M)
    (ε : ℝ) :
    P.real {ω | ε ≤ X ω} ≤ Real.exp (-t * ε) * M := by
  have h_step1 : P.real {ω | ε ≤ X ω} ≤ Real.exp (-t * ε) * mgf X P t :=
    measure_ge_le_exp_mul_mgf ε ht.le h_int
  have h_exp_pos : 0 < Real.exp (-t * ε) := Real.exp_pos _
  calc P.real {ω | ε ≤ X ω}
      ≤ Real.exp (-t * ε) * mgf X P t := h_step1
    _ ≤ Real.exp (-t * ε) * M := by
        apply mul_le_mul_of_nonneg_left h_mgf_bound h_exp_pos.le

/--
Conditional upper-tail form of **Doty Theorem 4.3 (Janson's geometric sum
tail)**.

Let `X_i` be independent geometric random variables on `(Ω, μ)` with success
probabilities `p_i` and `μ_X = Σ 1/p_i`. Let `p_min := min p_i`. Then for all
`λ ≥ 1`,
  `μ {ω | λ * μ_X ≤ ∑ X_i ω} ≤ exp(- p_min * μ_X * (λ - 1 - log λ))`.

The companion lower tail is the same bound for `λ ≤ 1`.

**Proof status:** Mathlib provides `HasSubgaussianMGF` with `measure_ge_le_of_HasSubgaussianMGF`,
but geometric distributions are NOT sub-Gaussian (their MGF diverges at `-log(1-p)`),
so that tool cannot be used. The Janson bound relies on the exponential MGF of the
geometric via an optimized Cramér–Chernoff argument (Janson 2018). This theorem
only proves the final Markov step from a supplied MGF bound. -/
theorem janson_geom_upper_tail_of_mgf_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (k : ℕ) (X : ℕ → Ω → ℝ)
    (_h_indep : iIndepFun X P)
    (_h_meas : ∀ i, AEMeasurable (X i) P)
    (_h_geom_ge_one : ∀ i, ∀ᵐ ω ∂P, 1 ≤ X i ω)
    (_h_support : ∀ i ≥ k, ∀ᵐ ω ∂P, X i ω = 0)
    (p : ℕ → ℝ) (_h_p_pos : ∀ i, 0 < p i) (_h_p_le_one : ∀ i, p i ≤ 1)
    (_h_geom_dist : ∀ i, ∫ ω, X i ω ∂P = (p i)⁻¹)
    (μ_X : ℝ) (_hμ_X : μ_X = ∑ i ∈ Finset.range k, (p i)⁻¹)
    (p_min : ℝ) (_hp_min : p_min = ⨅ i ∈ Finset.range k, p i)
    (lam : ℝ) (_hlam_ge : 1 ≤ lam)
    -- Cramér MGF hypothesis: caller must supply `t > 0` and the bound on the
    -- sum's MGF. For independent Geometric(p_i) variables this is Janson's MGF
    -- estimate; outside this paper, e.g. for sub-exponential X_i, callers can
    -- discharge this hypothesis by other means.
    (t : ℝ) (ht_pos : 0 < t)
    (h_int : Integrable (fun ω => Real.exp (t * ∑ i ∈ Finset.range k, X i ω)) P)
    (h_chernoff : Real.exp (-t * (lam * μ_X)) *
                    mgf (fun ω => ∑ i ∈ Finset.range k, X i ω) P t ≤
                  Real.exp (-p_min * μ_X * (lam - 1 - Real.log lam))) :
    P.real {ω | lam * μ_X ≤ ∑ i ∈ Finset.range k, X i ω} ≤
      Real.exp (-p_min * μ_X * (lam - 1 - Real.log lam)) := by
  -- Apply Markov's inequality on exp(t · ∑X_i), then use the supplied MGF bound.
  have h_step :
      P.real {ω | lam * μ_X ≤ ∑ i ∈ Finset.range k, X i ω} ≤
        Real.exp (-t * (lam * μ_X)) *
          mgf (fun ω => ∑ i ∈ Finset.range k, X i ω) P t :=
    measure_ge_le_exp_mul_mgf (lam * μ_X) ht_pos.le h_int
  exact h_step.trans h_chernoff

/-- Upper-tail Janson/Chernoff step from an MGF product bound for the individual
summands.  The product form is the one naturally obtained from independence:
`iIndepFun.mgf_sum₀` turns it into the total-sum MGF bound used by
`janson_geom_upper_tail_of_mgf_bound`. -/
theorem janson_geom_upper_tail_of_individual_mgf_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (k : ℕ) (X : ℕ → Ω → ℝ)
    (h_indep : iIndepFun X P)
    (h_meas : ∀ i, AEMeasurable (X i) P)
    (_h_geom_ge_one : ∀ i, ∀ᵐ ω ∂P, 1 ≤ X i ω)
    (_h_support : ∀ i ≥ k, ∀ᵐ ω ∂P, X i ω = 0)
    (p : ℕ → ℝ) (_h_p_pos : ∀ i, 0 < p i) (_h_p_le_one : ∀ i, p i ≤ 1)
    (_h_geom_dist : ∀ i, ∫ ω, X i ω ∂P = (p i)⁻¹)
    (μ_X : ℝ) (_hμ_X : μ_X = ∑ i ∈ Finset.range k, (p i)⁻¹)
    (p_min : ℝ) (_hp_min : p_min = ⨅ i ∈ Finset.range k, p i)
    (lam : ℝ) (_hlam_ge : 1 ≤ lam)
    (t : ℝ) (ht_pos : 0 < t)
    (h_int : Integrable (fun ω => Real.exp (t * ∑ i ∈ Finset.range k, X i ω)) P)
    (h_chernoff :
      Real.exp (-t * (lam * μ_X)) * (∏ i ∈ Finset.range k, mgf (X i) P t) ≤
        Real.exp (-p_min * μ_X * (lam - 1 - Real.log lam))) :
    P.real {ω | lam * μ_X ≤ ∑ i ∈ Finset.range k, X i ω} ≤
      Real.exp (-p_min * μ_X * (lam - 1 - Real.log lam)) := by
  have h_sum_mgf :
      mgf (fun ω => ∑ i ∈ Finset.range k, X i ω) P t =
        ∏ i ∈ Finset.range k, mgf (X i) P t := by
    have hfun : (fun ω => ∑ i ∈ Finset.range k, X i ω) =ᵐ[P]
        (∑ i ∈ Finset.range k, X i) := by
      exact Filter.Eventually.of_forall (by intro ω; simp [Finset.sum_apply])
    rw [mgf_congr hfun]
    exact h_indep.mgf_sum₀ h_meas (Finset.range k)
  exact janson_geom_upper_tail_of_mgf_bound
    (P := P) (k := k) (X := X) h_indep h_meas _h_geom_ge_one _h_support
    p _h_p_pos _h_p_le_one _h_geom_dist μ_X _hμ_X p_min _hp_min
    lam _hlam_ge t ht_pos h_int (by simpa [h_sum_mgf] using h_chernoff)

/-- Upper-tail Janson/Chernoff step with the shifted-geometric closed-form MGF.

This removes the individual `mgf` product hypothesis: independent variables
identified with Mathlib's shifted geometric measure have the required product
MGF, and the remaining assumption is the purely analytic closed-form Chernoff
inequality. -/
theorem janson_geom_upper_tail_of_shifted_geometric_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (k : ℕ) (X : ℕ → Ω → ℝ)
    (h_indep : iIndepFun X P)
    (h_meas : ∀ i, AEMeasurable (X i) P)
    (h_geom_ge_one : ∀ i, ∀ᵐ ω ∂P, 1 ≤ X i ω)
    (h_support : ∀ i ≥ k, ∀ᵐ ω ∂P, X i ω = 0)
    (p : ℕ → ℝ) (h_p_pos : ∀ i, 0 < p i) (h_p_le_one : ∀ i, p i ≤ 1)
    (h_geom_dist : ∀ i, ∫ ω, X i ω ∂P = (p i)⁻¹)
    (μ_X : ℝ) (hμ_X : μ_X = ∑ i ∈ Finset.range k, (p i)⁻¹)
    (p_min : ℝ) (hp_min : p_min = ⨅ i ∈ Finset.range k, p i)
    (lam : ℝ) (hlam_ge : 1 ≤ lam)
    (t : ℝ) (ht_pos : 0 < t)
    (hconv : ∀ i ∈ Finset.range k, (1 - p i) * Real.exp t < 1)
    (hident : ∀ i (_hi : i ∈ Finset.range k),
      IdentDistrib (X i) (fun n : ℕ => (n : ℝ) + 1) P
        (geometricMeasure (h_p_pos i) (h_p_le_one i)))
    (h_int : Integrable (fun ω => Real.exp (t * ∑ i ∈ Finset.range k, X i ω)) P)
    (h_chernoff :
      Real.exp (-t * (lam * μ_X)) *
          (∏ i ∈ Finset.range k,
            Real.exp t * p i * (1 - (1 - p i) * Real.exp t)⁻¹) ≤
        Real.exp (-p_min * μ_X * (lam - 1 - Real.log lam))) :
    P.real {ω | lam * μ_X ≤ ∑ i ∈ Finset.range k, X i ω} ≤
      Real.exp (-p_min * μ_X * (lam - 1 - Real.log lam)) := by
  have hprod :
      (∏ i ∈ Finset.range k, mgf (X i) P t) =
        ∏ i ∈ Finset.range k,
          Real.exp t * p i * (1 - (1 - p i) * Real.exp t)⁻¹ := by
    exact shifted_geometric_product_mgf_of_identDistrib
      (P := P) (k := k) (X := X) (p := p) (t := t)
      (fun i _hi => h_p_pos i) (fun i _hi => h_p_le_one i) hconv hident
  exact janson_geom_upper_tail_of_individual_mgf_bound
    (P := P) (k := k) (X := X) h_indep h_meas h_geom_ge_one h_support
    p h_p_pos h_p_le_one h_geom_dist μ_X hμ_X p_min hp_min
    lam hlam_ge t ht_pos h_int (by simpa [hprod] using h_chernoff)

/-- Upper-tail shifted-geometric Janson/Chernoff step from the logarithmic
closed-form MGF inequality. -/
theorem janson_geom_upper_tail_of_shifted_geometric_log_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (k : ℕ) (X : ℕ → Ω → ℝ)
    (h_indep : iIndepFun X P)
    (h_meas : ∀ i, AEMeasurable (X i) P)
    (h_geom_ge_one : ∀ i, ∀ᵐ ω ∂P, 1 ≤ X i ω)
    (h_support : ∀ i ≥ k, ∀ᵐ ω ∂P, X i ω = 0)
    (p : ℕ → ℝ) (h_p_pos : ∀ i, 0 < p i) (h_p_le_one : ∀ i, p i ≤ 1)
    (h_geom_dist : ∀ i, ∫ ω, X i ω ∂P = (p i)⁻¹)
    (μ_X : ℝ) (hμ_X : μ_X = ∑ i ∈ Finset.range k, (p i)⁻¹)
    (p_min : ℝ) (hp_min : p_min = ⨅ i ∈ Finset.range k, p i)
    (lam : ℝ) (hlam_ge : 1 ≤ lam)
    (t : ℝ) (ht_pos : 0 < t)
    (hconv : ∀ i ∈ Finset.range k, (1 - p i) * Real.exp t < 1)
    (hident : ∀ i (_hi : i ∈ Finset.range k),
      IdentDistrib (X i) (fun n : ℕ => (n : ℝ) + 1) P
        (geometricMeasure (h_p_pos i) (h_p_le_one i)))
    (h_int : Integrable (fun ω => Real.exp (t * ∑ i ∈ Finset.range k, X i ω)) P)
    (h_log_chernoff :
      -t * (lam * μ_X) +
          ∑ i ∈ Finset.range k,
            (t + Real.log (p i) - Real.log (1 - (1 - p i) * Real.exp t)) ≤
        -p_min * μ_X * (lam - 1 - Real.log lam)) :
    P.real {ω | lam * μ_X ≤ ∑ i ∈ Finset.range k, X i ω} ≤
      Real.exp (-p_min * μ_X * (lam - 1 - Real.log lam)) := by
  exact janson_geom_upper_tail_of_shifted_geometric_bound
    (P := P) (k := k) (X := X) h_indep h_meas h_geom_ge_one h_support
    p h_p_pos h_p_le_one h_geom_dist μ_X hμ_X p_min hp_min
    lam hlam_ge t ht_pos hconv hident h_int
    (shifted_geometric_product_mgf_closedForm_mul_le_exp_of_log_bound
      k p t (lam * μ_X) (-p_min * μ_X * (lam - 1 - Real.log lam))
      (fun i _hi => h_p_pos i) hconv h_log_chernoff)

/-- Upper-tail shifted-geometric Janson/Chernoff step from pointwise logarithmic
MGF inequalities. -/
theorem janson_geom_upper_tail_of_shifted_geometric_pointwise_bound {Ω : Type*}
    [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (k : ℕ) (X : ℕ → Ω → ℝ)
    (h_indep : iIndepFun X P)
    (h_meas : ∀ i, AEMeasurable (X i) P)
    (h_geom_ge_one : ∀ i, ∀ᵐ ω ∂P, 1 ≤ X i ω)
    (h_support : ∀ i ≥ k, ∀ᵐ ω ∂P, X i ω = 0)
    (p : ℕ → ℝ) (h_p_pos : ∀ i, 0 < p i) (h_p_le_one : ∀ i, p i ≤ 1)
    (h_geom_dist : ∀ i, ∫ ω, X i ω ∂P = (p i)⁻¹)
    (μ_X : ℝ) (hμ_X : μ_X = ∑ i ∈ Finset.range k, (p i)⁻¹)
    (p_min : ℝ) (hp_min : p_min = ⨅ i ∈ Finset.range k, p i)
    (lam : ℝ) (hlam_ge : 1 ≤ lam)
    (t : ℝ) (ht_pos : 0 < t)
    (hconv : ∀ i ∈ Finset.range k, (1 - p i) * Real.exp t < 1)
    (hident : ∀ i (_hi : i ∈ Finset.range k),
      IdentDistrib (X i) (fun n : ℕ => (n : ℝ) + 1) P
        (geometricMeasure (h_p_pos i) (h_p_le_one i)))
    (h_int : Integrable (fun ω => Real.exp (t * ∑ i ∈ Finset.range k, X i ω)) P)
    (hpoint : ∀ i ∈ Finset.range k,
      t + Real.log (p i) - Real.log (1 - (1 - p i) * Real.exp t) ≤
        t * lam * (p i)⁻¹ -
          p_min * (p i)⁻¹ * (lam - 1 - Real.log lam)) :
    P.real {ω | lam * μ_X ≤ ∑ i ∈ Finset.range k, X i ω} ≤
      Real.exp (-p_min * μ_X * (lam - 1 - Real.log lam)) := by
  exact janson_geom_upper_tail_of_shifted_geometric_log_bound
    (P := P) (k := k) (X := X) h_indep h_meas h_geom_ge_one h_support
    p h_p_pos h_p_le_one h_geom_dist μ_X hμ_X p_min hp_min
    lam hlam_ge t ht_pos hconv hident h_int
    (janson_geom_log_chernoff_of_pointwise_bound k p t μ_X p_min lam hμ_X hpoint)

/-- Upper-tail shifted-geometric Janson/Chernoff step with Janson's optimized
parameter `t = (1 - 1 / λ) * p_min`.

This discharges both the closed-form convergence hypotheses and the pointwise
logarithmic MGF inequalities from the local facts `0 ≤ p_min` and
`p_min ≤ p_i`. -/
theorem janson_geom_upper_tail_of_shifted_geometric_janson_parameter {Ω : Type*}
    [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (k : ℕ) (X : ℕ → Ω → ℝ)
    (h_indep : iIndepFun X P)
    (h_meas : ∀ i, AEMeasurable (X i) P)
    (h_geom_ge_one : ∀ i, ∀ᵐ ω ∂P, 1 ≤ X i ω)
    (h_support : ∀ i ≥ k, ∀ᵐ ω ∂P, X i ω = 0)
    (p : ℕ → ℝ) (h_p_pos : ∀ i, 0 < p i) (h_p_le_one : ∀ i, p i ≤ 1)
    (h_geom_dist : ∀ i, ∫ ω, X i ω ∂P = (p i)⁻¹)
    (μ_X : ℝ) (hμ_X : μ_X = ∑ i ∈ Finset.range k, (p i)⁻¹)
    (p_min : ℝ) (hp_min : p_min = ⨅ i ∈ Finset.range k, p i)
    (hpmin_nonneg : 0 ≤ p_min)
    (hpmin_le : ∀ i ∈ Finset.range k, p_min ≤ p i)
    (lam : ℝ) (hlam_ge : 1 ≤ lam)
    (t : ℝ) (ht_pos : 0 < t) (ht : t = (1 - lam⁻¹) * p_min)
    (hident : ∀ i (_hi : i ∈ Finset.range k),
      IdentDistrib (X i) (fun n : ℕ => (n : ℝ) + 1) P
        (geometricMeasure (h_p_pos i) (h_p_le_one i)))
    (h_int : Integrable (fun ω => Real.exp (t * ∑ i ∈ Finset.range k, X i ω)) P) :
    P.real {ω | lam * μ_X ≤ ∑ i ∈ Finset.range k, X i ω} ≤
      Real.exp (-p_min * μ_X * (lam - 1 - Real.log lam)) := by
  let b : ℝ := 1 - lam⁻¹
  have hlam_pos : 0 < lam := zero_lt_one.trans_le hlam_ge
  have hb_nonneg : 0 ≤ b := by
    have hinv_le : lam⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hlam_ge
    dsimp [b]
    linarith
  have hb_lt_one : b < 1 := by
    have hinv_pos : 0 < lam⁻¹ := inv_pos.mpr hlam_pos
    dsimp [b]
    linarith
  have ht_nonneg : 0 ≤ t := by
    rw [ht]
    exact mul_nonneg hb_nonneg hpmin_nonneg
  have hconv : ∀ i ∈ Finset.range k, (1 - p i) * Real.exp t < 1 := by
    intro i hi
    have ht_le : t ≤ b * p i := by
      rw [ht]
      simpa [b] using mul_le_mul_of_nonneg_left (hpmin_le i hi) hb_nonneg
    have ht_lt : t < p i := by
      have hb_mul_lt : b * p i < 1 * p i := mul_lt_mul_of_pos_right hb_lt_one (h_p_pos i)
      linarith
    exact shifted_geometric_mgf_converges_of_nonneg_lt (h_p_pos i) ht_nonneg ht_lt
  have hpoint : ∀ i ∈ Finset.range k,
      t + Real.log (p i) - Real.log (1 - (1 - p i) * Real.exp t) ≤
        t * lam * (p i)⁻¹ -
          p_min * (p i)⁻¹ * (lam - 1 - Real.log lam) := by
    intro i hi
    exact shifted_geometric_mgf_closedForm_log_le_upper_janson_point
      (hp_pos := h_p_pos i) (hpmin_nonneg := hpmin_nonneg)
      (hpmin_le := hpmin_le i hi) (hlam_ge_one := hlam_ge) (ht := ht)
  exact janson_geom_upper_tail_of_shifted_geometric_pointwise_bound
    (P := P) (k := k) (X := X) h_indep h_meas h_geom_ge_one h_support
    p h_p_pos h_p_le_one h_geom_dist μ_X hμ_X p_min hp_min
    lam hlam_ge t ht_pos hconv hident h_int hpoint

/-- Upper-tail shifted-geometric Janson/Chernoff step with the optimized
parameter, deriving the local `p_min` facts from the finite `iInf`
definition. -/
theorem janson_geom_upper_tail_of_shifted_geometric_iInf_parameter {Ω : Type*}
    [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (k : ℕ) (X : ℕ → Ω → ℝ)
    (h_indep : iIndepFun X P)
    (h_meas : ∀ i, AEMeasurable (X i) P)
    (h_geom_ge_one : ∀ i, ∀ᵐ ω ∂P, 1 ≤ X i ω)
    (h_support : ∀ i ≥ k, ∀ᵐ ω ∂P, X i ω = 0)
    (p : ℕ → ℝ) (h_p_pos : ∀ i, 0 < p i) (h_p_le_one : ∀ i, p i ≤ 1)
    (h_geom_dist : ∀ i, ∫ ω, X i ω ∂P = (p i)⁻¹)
    (μ_X : ℝ) (hμ_X : μ_X = ∑ i ∈ Finset.range k, (p i)⁻¹)
    (p_min : ℝ) (hp_min : p_min = ⨅ i ∈ Finset.range k, p i)
    (lam : ℝ) (hlam_ge : 1 ≤ lam)
    (t : ℝ) (ht_pos : 0 < t) (ht : t = (1 - lam⁻¹) * p_min)
    (hident : ∀ i (_hi : i ∈ Finset.range k),
      IdentDistrib (X i) (fun n : ℕ => (n : ℝ) + 1) P
        (geometricMeasure (h_p_pos i) (h_p_le_one i)))
    (h_int : Integrable (fun ω => Real.exp (t * ∑ i ∈ Finset.range k, X i ω)) P) :
    P.real {ω | lam * μ_X ≤ ∑ i ∈ Finset.range k, X i ω} ≤
      Real.exp (-p_min * μ_X * (lam - 1 - Real.log lam)) := by
  exact janson_geom_upper_tail_of_shifted_geometric_janson_parameter
    (P := P) (k := k) (X := X) h_indep h_meas h_geom_ge_one h_support
    p h_p_pos h_p_le_one h_geom_dist μ_X hμ_X p_min hp_min
    (janson_pmin_nonneg_of_iInf hp_min (fun i hi => (h_p_pos i).le))
    (janson_pmin_le_of_iInf hp_min (fun i hi => (h_p_pos i).le))
    lam hlam_ge t ht_pos ht hident h_int

/-- Conditional lower-tail form of **Doty Theorem 4.3**. Same bound for
`λ ≤ 1`, assuming the needed negative-MGF estimate. -/
theorem janson_geom_lower_tail_of_mgf_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (k : ℕ) (X : ℕ → Ω → ℝ)
    (_h_indep : iIndepFun X P)
    (_h_meas : ∀ i, AEMeasurable (X i) P)
    (_h_geom_ge_one : ∀ i, ∀ᵐ ω ∂P, 1 ≤ X i ω)
    (_h_support : ∀ i ≥ k, ∀ᵐ ω ∂P, X i ω = 0)
    (p : ℕ → ℝ) (_h_p_pos : ∀ i, 0 < p i) (_h_p_le_one : ∀ i, p i ≤ 1)
    (_h_geom_dist : ∀ i, ∫ ω, X i ω ∂P = (p i)⁻¹)
    (μ_X : ℝ) (_hμ_X : μ_X = ∑ i ∈ Finset.range k, (p i)⁻¹)
    (p_min : ℝ) (_hp_min : p_min = ⨅ i ∈ Finset.range k, p i)
    (lam : ℝ) (_hlam_le : lam ≤ 1) (_hlam_pos : 0 < lam)
    -- Cramér MGF hypothesis (lower tail uses negative t).
    (t : ℝ) (ht_neg : t ≤ 0)
    (h_int : Integrable (fun ω => Real.exp (t * ∑ i ∈ Finset.range k, X i ω)) P)
    (h_chernoff : Real.exp (-t * (lam * μ_X)) *
                    mgf (fun ω => ∑ i ∈ Finset.range k, X i ω) P t ≤
                  Real.exp (-p_min * μ_X * (lam - 1 - Real.log lam))) :
    P.real {ω | (∑ i ∈ Finset.range k, X i ω) ≤ lam * μ_X} ≤
      Real.exp (-p_min * μ_X * (lam - 1 - Real.log lam)) := by
  have h_step :
      P.real {ω | ∑ i ∈ Finset.range k, X i ω ≤ lam * μ_X} ≤
        Real.exp (-t * (lam * μ_X)) *
          mgf (fun ω => ∑ i ∈ Finset.range k, X i ω) P t :=
    measure_le_le_exp_mul_mgf (lam * μ_X) ht_neg h_int
  exact h_step.trans h_chernoff

/-- Lower-tail Janson/Chernoff step from an MGF product bound for the individual
summands, with the product-to-sum MGF identity supplied by independence. -/
theorem janson_geom_lower_tail_of_individual_mgf_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (k : ℕ) (X : ℕ → Ω → ℝ)
    (h_indep : iIndepFun X P)
    (h_meas : ∀ i, AEMeasurable (X i) P)
    (_h_geom_ge_one : ∀ i, ∀ᵐ ω ∂P, 1 ≤ X i ω)
    (_h_support : ∀ i ≥ k, ∀ᵐ ω ∂P, X i ω = 0)
    (p : ℕ → ℝ) (_h_p_pos : ∀ i, 0 < p i) (_h_p_le_one : ∀ i, p i ≤ 1)
    (_h_geom_dist : ∀ i, ∫ ω, X i ω ∂P = (p i)⁻¹)
    (μ_X : ℝ) (_hμ_X : μ_X = ∑ i ∈ Finset.range k, (p i)⁻¹)
    (p_min : ℝ) (_hp_min : p_min = ⨅ i ∈ Finset.range k, p i)
    (lam : ℝ) (_hlam_le : lam ≤ 1) (_hlam_pos : 0 < lam)
    (t : ℝ) (ht_neg : t ≤ 0)
    (h_int : Integrable (fun ω => Real.exp (t * ∑ i ∈ Finset.range k, X i ω)) P)
    (h_chernoff :
      Real.exp (-t * (lam * μ_X)) * (∏ i ∈ Finset.range k, mgf (X i) P t) ≤
        Real.exp (-p_min * μ_X * (lam - 1 - Real.log lam))) :
    P.real {ω | (∑ i ∈ Finset.range k, X i ω) ≤ lam * μ_X} ≤
      Real.exp (-p_min * μ_X * (lam - 1 - Real.log lam)) := by
  have h_sum_mgf :
      mgf (fun ω => ∑ i ∈ Finset.range k, X i ω) P t =
        ∏ i ∈ Finset.range k, mgf (X i) P t := by
    have hfun : (fun ω => ∑ i ∈ Finset.range k, X i ω) =ᵐ[P]
        (∑ i ∈ Finset.range k, X i) := by
      exact Filter.Eventually.of_forall (by intro ω; simp [Finset.sum_apply])
    rw [mgf_congr hfun]
    exact h_indep.mgf_sum₀ h_meas (Finset.range k)
  exact janson_geom_lower_tail_of_mgf_bound
    (P := P) (k := k) (X := X) h_indep h_meas _h_geom_ge_one _h_support
    p _h_p_pos _h_p_le_one _h_geom_dist μ_X _hμ_X p_min _hp_min
    lam _hlam_le _hlam_pos t ht_neg h_int (by simpa [h_sum_mgf] using h_chernoff)

/-- Lower-tail Janson/Chernoff step with the shifted-geometric closed-form MGF.

For `t ≤ 0`, the convergence side of each shifted-geometric MGF is automatic,
so this theorem turns distributional shifted-geometric hypotheses directly into
the closed-form product Chernoff bound. -/
theorem janson_geom_lower_tail_of_shifted_geometric_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (k : ℕ) (X : ℕ → Ω → ℝ)
    (h_indep : iIndepFun X P)
    (h_meas : ∀ i, AEMeasurable (X i) P)
    (h_geom_ge_one : ∀ i, ∀ᵐ ω ∂P, 1 ≤ X i ω)
    (h_support : ∀ i ≥ k, ∀ᵐ ω ∂P, X i ω = 0)
    (p : ℕ → ℝ) (h_p_pos : ∀ i, 0 < p i) (h_p_le_one : ∀ i, p i ≤ 1)
    (h_geom_dist : ∀ i, ∫ ω, X i ω ∂P = (p i)⁻¹)
    (μ_X : ℝ) (hμ_X : μ_X = ∑ i ∈ Finset.range k, (p i)⁻¹)
    (p_min : ℝ) (hp_min : p_min = ⨅ i ∈ Finset.range k, p i)
    (lam : ℝ) (hlam_le : lam ≤ 1) (hlam_pos : 0 < lam)
    (t : ℝ) (ht_neg : t ≤ 0)
    (hident : ∀ i (_hi : i ∈ Finset.range k),
      IdentDistrib (X i) (fun n : ℕ => (n : ℝ) + 1) P
        (geometricMeasure (h_p_pos i) (h_p_le_one i)))
    (h_int : Integrable (fun ω => Real.exp (t * ∑ i ∈ Finset.range k, X i ω)) P)
    (h_chernoff :
      Real.exp (-t * (lam * μ_X)) *
          (∏ i ∈ Finset.range k,
            Real.exp t * p i * (1 - (1 - p i) * Real.exp t)⁻¹) ≤
        Real.exp (-p_min * μ_X * (lam - 1 - Real.log lam))) :
    P.real {ω | (∑ i ∈ Finset.range k, X i ω) ≤ lam * μ_X} ≤
      Real.exp (-p_min * μ_X * (lam - 1 - Real.log lam)) := by
  have hprod :
      (∏ i ∈ Finset.range k, mgf (X i) P t) =
        ∏ i ∈ Finset.range k,
          Real.exp t * p i * (1 - (1 - p i) * Real.exp t)⁻¹ := by
    exact shifted_geometric_product_mgf_of_identDistrib_of_nonpos
      (P := P) (k := k) (X := X) (p := p) (t := t)
      (fun i _hi => h_p_pos i) (fun i _hi => h_p_le_one i) ht_neg hident
  exact janson_geom_lower_tail_of_individual_mgf_bound
    (P := P) (k := k) (X := X) h_indep h_meas h_geom_ge_one h_support
    p h_p_pos h_p_le_one h_geom_dist μ_X hμ_X p_min hp_min
    lam hlam_le hlam_pos t ht_neg h_int (by simpa [hprod] using h_chernoff)

/-- Lower-tail shifted-geometric Janson/Chernoff step from the logarithmic
closed-form MGF inequality. -/
theorem janson_geom_lower_tail_of_shifted_geometric_log_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (k : ℕ) (X : ℕ → Ω → ℝ)
    (h_indep : iIndepFun X P)
    (h_meas : ∀ i, AEMeasurable (X i) P)
    (h_geom_ge_one : ∀ i, ∀ᵐ ω ∂P, 1 ≤ X i ω)
    (h_support : ∀ i ≥ k, ∀ᵐ ω ∂P, X i ω = 0)
    (p : ℕ → ℝ) (h_p_pos : ∀ i, 0 < p i) (h_p_le_one : ∀ i, p i ≤ 1)
    (h_geom_dist : ∀ i, ∫ ω, X i ω ∂P = (p i)⁻¹)
    (μ_X : ℝ) (hμ_X : μ_X = ∑ i ∈ Finset.range k, (p i)⁻¹)
    (p_min : ℝ) (hp_min : p_min = ⨅ i ∈ Finset.range k, p i)
    (lam : ℝ) (hlam_le : lam ≤ 1) (hlam_pos : 0 < lam)
    (t : ℝ) (ht_neg : t ≤ 0)
    (hident : ∀ i (_hi : i ∈ Finset.range k),
      IdentDistrib (X i) (fun n : ℕ => (n : ℝ) + 1) P
        (geometricMeasure (h_p_pos i) (h_p_le_one i)))
    (h_int : Integrable (fun ω => Real.exp (t * ∑ i ∈ Finset.range k, X i ω)) P)
    (h_log_chernoff :
      -t * (lam * μ_X) +
          ∑ i ∈ Finset.range k,
            (t + Real.log (p i) - Real.log (1 - (1 - p i) * Real.exp t)) ≤
        -p_min * μ_X * (lam - 1 - Real.log lam)) :
    P.real {ω | (∑ i ∈ Finset.range k, X i ω) ≤ lam * μ_X} ≤
      Real.exp (-p_min * μ_X * (lam - 1 - Real.log lam)) := by
  exact janson_geom_lower_tail_of_shifted_geometric_bound
    (P := P) (k := k) (X := X) h_indep h_meas h_geom_ge_one h_support
    p h_p_pos h_p_le_one h_geom_dist μ_X hμ_X p_min hp_min
    lam hlam_le hlam_pos t ht_neg hident h_int
    (shifted_geometric_product_mgf_closedForm_mul_le_exp_of_log_bound
      k p t (lam * μ_X) (-p_min * μ_X * (lam - 1 - Real.log lam))
      (fun i _hi => h_p_pos i)
      (fun i hi => shifted_geometric_mgf_converges_of_nonpos
        (h_p_pos i) (h_p_le_one i) ht_neg)
      h_log_chernoff)

/-- Lower-tail shifted-geometric Janson/Chernoff step from pointwise logarithmic
MGF inequalities. -/
theorem janson_geom_lower_tail_of_shifted_geometric_pointwise_bound {Ω : Type*}
    [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (k : ℕ) (X : ℕ → Ω → ℝ)
    (h_indep : iIndepFun X P)
    (h_meas : ∀ i, AEMeasurable (X i) P)
    (h_geom_ge_one : ∀ i, ∀ᵐ ω ∂P, 1 ≤ X i ω)
    (h_support : ∀ i ≥ k, ∀ᵐ ω ∂P, X i ω = 0)
    (p : ℕ → ℝ) (h_p_pos : ∀ i, 0 < p i) (h_p_le_one : ∀ i, p i ≤ 1)
    (h_geom_dist : ∀ i, ∫ ω, X i ω ∂P = (p i)⁻¹)
    (μ_X : ℝ) (hμ_X : μ_X = ∑ i ∈ Finset.range k, (p i)⁻¹)
    (p_min : ℝ) (hp_min : p_min = ⨅ i ∈ Finset.range k, p i)
    (lam : ℝ) (hlam_le : lam ≤ 1) (hlam_pos : 0 < lam)
    (t : ℝ) (ht_neg : t ≤ 0)
    (hident : ∀ i (_hi : i ∈ Finset.range k),
      IdentDistrib (X i) (fun n : ℕ => (n : ℝ) + 1) P
        (geometricMeasure (h_p_pos i) (h_p_le_one i)))
    (h_int : Integrable (fun ω => Real.exp (t * ∑ i ∈ Finset.range k, X i ω)) P)
    (hpoint : ∀ i ∈ Finset.range k,
      t + Real.log (p i) - Real.log (1 - (1 - p i) * Real.exp t) ≤
        t * lam * (p i)⁻¹ -
          p_min * (p i)⁻¹ * (lam - 1 - Real.log lam)) :
    P.real {ω | (∑ i ∈ Finset.range k, X i ω) ≤ lam * μ_X} ≤
      Real.exp (-p_min * μ_X * (lam - 1 - Real.log lam)) := by
  exact janson_geom_lower_tail_of_shifted_geometric_log_bound
    (P := P) (k := k) (X := X) h_indep h_meas h_geom_ge_one h_support
    p h_p_pos h_p_le_one h_geom_dist μ_X hμ_X p_min hp_min
    lam hlam_le hlam_pos t ht_neg hident h_int
    (janson_geom_log_chernoff_of_pointwise_bound k p t μ_X p_min lam hμ_X hpoint)

/-- Lower-tail shifted-geometric Janson/Chernoff step with Janson's optimized
negative parameter `t = -(1 / λ - 1) * p_min`.

This discharges the pointwise logarithmic MGF inequalities from the local facts
`0 ≤ p_min` and `p_min ≤ p_i`.  The convergence hypotheses are automatic for
the negative Chernoff parameter. -/
theorem janson_geom_lower_tail_of_shifted_geometric_janson_parameter {Ω : Type*}
    [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (k : ℕ) (X : ℕ → Ω → ℝ)
    (h_indep : iIndepFun X P)
    (h_meas : ∀ i, AEMeasurable (X i) P)
    (h_geom_ge_one : ∀ i, ∀ᵐ ω ∂P, 1 ≤ X i ω)
    (h_support : ∀ i ≥ k, ∀ᵐ ω ∂P, X i ω = 0)
    (p : ℕ → ℝ) (h_p_pos : ∀ i, 0 < p i) (h_p_le_one : ∀ i, p i ≤ 1)
    (h_geom_dist : ∀ i, ∫ ω, X i ω ∂P = (p i)⁻¹)
    (μ_X : ℝ) (hμ_X : μ_X = ∑ i ∈ Finset.range k, (p i)⁻¹)
    (p_min : ℝ) (hp_min : p_min = ⨅ i ∈ Finset.range k, p i)
    (hpmin_nonneg : 0 ≤ p_min)
    (hpmin_le : ∀ i ∈ Finset.range k, p_min ≤ p i)
    (lam : ℝ) (hlam_le : lam ≤ 1) (hlam_pos : 0 < lam)
    (s : ℝ) (hs : s = (lam⁻¹ - 1) * p_min)
    (hident : ∀ i (_hi : i ∈ Finset.range k),
      IdentDistrib (X i) (fun n : ℕ => (n : ℝ) + 1) P
        (geometricMeasure (h_p_pos i) (h_p_le_one i)))
    (h_int : Integrable (fun ω => Real.exp ((-s) * ∑ i ∈ Finset.range k, X i ω)) P) :
    P.real {ω | (∑ i ∈ Finset.range k, X i ω) ≤ lam * μ_X} ≤
      Real.exp (-p_min * μ_X * (lam - 1 - Real.log lam)) := by
  have hy_nonneg : 0 ≤ lam⁻¹ - 1 := by
    have hone_le_inv : 1 ≤ lam⁻¹ := (one_le_inv₀ hlam_pos).2 hlam_le
    linarith
  have hs_nonneg : 0 ≤ s := by
    rw [hs]
    exact mul_nonneg hy_nonneg hpmin_nonneg
  have ht_neg : (-s) ≤ 0 := by linarith
  have hpoint : ∀ i ∈ Finset.range k,
      (-s) + Real.log (p i) - Real.log (1 - (1 - p i) * Real.exp (-s)) ≤
        (-s) * lam * (p i)⁻¹ -
          p_min * (p i)⁻¹ * (lam - 1 - Real.log lam) := by
    intro i hi
    exact shifted_geometric_mgf_closedForm_log_le_lower_janson_point
      (hp_pos := h_p_pos i) (hpmin_nonneg := hpmin_nonneg)
      (hpmin_le := hpmin_le i hi) (hlam_pos := hlam_pos)
      (hlam_le_one := hlam_le) (hs := hs)
  exact janson_geom_lower_tail_of_shifted_geometric_pointwise_bound
    (P := P) (k := k) (X := X) h_indep h_meas h_geom_ge_one h_support
    p h_p_pos h_p_le_one h_geom_dist μ_X hμ_X p_min hp_min
    lam hlam_le hlam_pos (-s) ht_neg hident h_int hpoint

/-- Lower-tail shifted-geometric Janson/Chernoff step with the optimized
negative parameter, deriving the local `p_min` facts from the finite `iInf`
definition. -/
theorem janson_geom_lower_tail_of_shifted_geometric_iInf_parameter {Ω : Type*}
    [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (k : ℕ) (X : ℕ → Ω → ℝ)
    (h_indep : iIndepFun X P)
    (h_meas : ∀ i, AEMeasurable (X i) P)
    (h_geom_ge_one : ∀ i, ∀ᵐ ω ∂P, 1 ≤ X i ω)
    (h_support : ∀ i ≥ k, ∀ᵐ ω ∂P, X i ω = 0)
    (p : ℕ → ℝ) (h_p_pos : ∀ i, 0 < p i) (h_p_le_one : ∀ i, p i ≤ 1)
    (h_geom_dist : ∀ i, ∫ ω, X i ω ∂P = (p i)⁻¹)
    (μ_X : ℝ) (hμ_X : μ_X = ∑ i ∈ Finset.range k, (p i)⁻¹)
    (p_min : ℝ) (hp_min : p_min = ⨅ i ∈ Finset.range k, p i)
    (lam : ℝ) (hlam_le : lam ≤ 1) (hlam_pos : 0 < lam)
    (s : ℝ) (hs : s = (lam⁻¹ - 1) * p_min)
    (hident : ∀ i (_hi : i ∈ Finset.range k),
      IdentDistrib (X i) (fun n : ℕ => (n : ℝ) + 1) P
        (geometricMeasure (h_p_pos i) (h_p_le_one i)))
    (h_int : Integrable (fun ω => Real.exp ((-s) * ∑ i ∈ Finset.range k, X i ω)) P) :
    P.real {ω | (∑ i ∈ Finset.range k, X i ω) ≤ lam * μ_X} ≤
      Real.exp (-p_min * μ_X * (lam - 1 - Real.log lam)) := by
  exact janson_geom_lower_tail_of_shifted_geometric_janson_parameter
    (P := P) (k := k) (X := X) h_indep h_meas h_geom_ge_one h_support
    p h_p_pos h_p_le_one h_geom_dist μ_X hμ_X p_min hp_min
    (janson_pmin_nonneg_of_iInf hp_min (fun i hi => (h_p_pos i).le))
    (janson_pmin_le_of_iInf hp_min (fun i hi => (h_p_pos i).le))
    lam hlam_le hlam_pos s hs hident h_int

/-- Conditional form of **Doty Corollary 4.4**.

For any `0 < ε < 1`, the symmetric two-sided concentration
  `P[(1−ε) μ_X ≤ ∑ X_i ≤ (1+ε) μ_X] ≥ 1 - exp(-C ε² p_min μ_X)`
holds with some absolute constant `C > 0`. The constant comes from the
Taylor approximation `λ − 1 − ln λ ≥ Θ(ε²)` for `λ = 1 ± ε`.

This theorem assumes one-sided tail bounds with the analytic `2` factor
already absorbed into the constant, then applies the union-bound/complement
step. It does not prove the geometric one-sided tails themselves. -/
theorem janson_geom_concentration_of_tail_bounds {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (k : ℕ) (X : ℕ → Ω → ℝ)
    (_h_indep : iIndepFun X P)
    (_h_meas : ∀ i, AEMeasurable (X i) P)
    (_h_geom_ge_one : ∀ i, ∀ᵐ ω ∂P, 1 ≤ X i ω)
    (_h_support : ∀ i ≥ k, ∀ᵐ ω ∂P, X i ω = 0)
    (p : ℕ → ℝ) (_h_p_pos : ∀ i, 0 < p i) (_h_p_le_one : ∀ i, p i ≤ 1)
    (_h_geom_dist : ∀ i, ∫ ω, X i ω ∂P = (p i)⁻¹)
    (μ_X : ℝ) (_hμ_X : μ_X = ∑ i ∈ Finset.range k, (p i)⁻¹)
    (p_min : ℝ) (_hp_min : p_min = ⨅ i ∈ Finset.range k, p i)
    (ε : ℝ) (_hε_pos : 0 < ε) (_hε_lt_one : ε < 1)
    (h_upper : P.real {ω | (1 + ε) * μ_X ≤ ∑ i ∈ Finset.range k, X i ω} ≤
      (1 / 2 : ℝ) * Real.exp (-((1 / 8 : ℝ) * ε ^ 2 * p_min * μ_X)))
    (h_lower : P.real {ω | ∑ i ∈ Finset.range k, X i ω ≤ (1 - ε) * μ_X} ≤
      (1 / 2 : ℝ) * Real.exp (-((1 / 8 : ℝ) * ε ^ 2 * p_min * μ_X))) :
    ∃ C : ℝ, 0 < C ∧
      P.real {ω | (1 - ε) * μ_X ≤ ∑ i ∈ Finset.range k, X i ω ∧
                  ∑ i ∈ Finset.range k, X i ω ≤ (1 + ε) * μ_X} ≥
        1 - Real.exp (- C * ε ^ 2 * p_min * μ_X) := by
  let S : Ω → ℝ := fun ω => ∑ i ∈ Finset.range k, X i ω
  set A := {ω | (1 + ε) * μ_X < S ω}
  set B := {ω | S ω < (1 - ε) * μ_X}
  let r : ℝ := Real.exp (-((1 / 8 : ℝ) * ε ^ 2 * p_min * μ_X))
  have hA : P.real A ≤ (1 / 2 : ℝ) * r := by
    exact (measureReal_mono (μ := P) (s₁ := A)
      (s₂ := {ω | (1 + ε) * μ_X ≤ ∑ i ∈ Finset.range k, X i ω})
      (by
        intro ω hω
        change (1 + ε) * μ_X < S ω at hω
        exact le_of_lt hω)).trans (by simpa [r, S] using h_upper)
  have hB : P.real B ≤ (1 / 2 : ℝ) * r := by
    exact (measureReal_mono (μ := P) (s₁ := B)
      (s₂ := {ω | ∑ i ∈ Finset.range k, X i ω ≤ (1 - ε) * μ_X})
      (by
        intro ω hω
        change S ω < (1 - ε) * μ_X at hω
        exact le_of_lt hω)).trans (by simpa [r, S] using h_lower)
  have h_union : P.real (A ∪ B) ≤ r := by
    calc
      P.real (A ∪ B) ≤ P.real A + P.real B := measureReal_union_le A B
      _ ≤ (1 / 2 : ℝ) * r + (1 / 2 : ℝ) * r := add_le_add hA hB
      _ = r := by ring
  have h_good_eq : {ω | (1 - ε) * μ_X ≤ ∑ i ∈ Finset.range k, X i ω ∧
                       ∑ i ∈ Finset.range k, X i ω ≤ (1 + ε) * μ_X} =
      (A ∪ B)ᶜ := by
    ext ω
    simp [A, B, S, not_lt, and_comm]
  have hS : AEMeasurable S P := by
    have hS' : AEMeasurable (∑ i ∈ Finset.range k, X i) P :=
      Finset.aemeasurable_sum (Finset.range k) (fun i _ => _h_meas i)
    exact hS'.congr (Filter.Eventually.of_forall (by
      intro ω
      simp [S, Finset.sum_apply]))
  have hA_meas : NullMeasurableSet A P := by
    simpa [A, S] using
      nullMeasurableSet_lt (aemeasurable_const (μ := P)) hS
  have hB_meas : NullMeasurableSet B P := by
    simpa [B, S] using
      nullMeasurableSet_lt hS (aemeasurable_const (μ := P))
  have h_compl : P.real (A ∪ B) + P.real ((A ∪ B)ᶜ) = 1 := by
    simpa using
      (measureReal_add_measureReal_compl₀ (μ := P) (hA_meas.union hB_meas))
  have h_final : P.real ((A ∪ B)ᶜ) ≥ 1 - r := by
    linarith
  refine ⟨1 / 8, by norm_num, ?_⟩
  rw [h_good_eq]
  simpa [r] using h_final

/-- Two-sided shifted-geometric Janson concentration from the optimized
one-sided `iInf`-parameter bounds.

The only remaining supplied facts are integrability of the two Chernoff
exponentials and the elementary real inequalities that convert the Janson
rates at `λ = 1 ± ε` into the displayed `1/8` quadratic rate with the extra
`1/2` union-bound slack. -/
theorem janson_geom_concentration_of_shifted_geometric_iInf_parameters {Ω : Type*}
    [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (k : ℕ) (X : ℕ → Ω → ℝ)
    (h_indep : iIndepFun X P)
    (h_meas : ∀ i, AEMeasurable (X i) P)
    (h_geom_ge_one : ∀ i, ∀ᵐ ω ∂P, 1 ≤ X i ω)
    (h_support : ∀ i ≥ k, ∀ᵐ ω ∂P, X i ω = 0)
    (p : ℕ → ℝ) (h_p_pos : ∀ i, 0 < p i) (h_p_le_one : ∀ i, p i ≤ 1)
    (h_geom_dist : ∀ i, ∫ ω, X i ω ∂P = (p i)⁻¹)
    (μ_X : ℝ) (hμ_X : μ_X = ∑ i ∈ Finset.range k, (p i)⁻¹)
    (p_min : ℝ) (hp_min : p_min = ⨅ i ∈ Finset.range k, p i)
    (ε : ℝ) (hε_pos : 0 < ε) (hε_lt_one : ε < 1)
    (t_upper : ℝ) (ht_upper_pos : 0 < t_upper)
    (ht_upper : t_upper = (1 - (1 + ε)⁻¹) * p_min)
    (s_lower : ℝ) (hs_lower : s_lower = ((1 - ε)⁻¹ - 1) * p_min)
    (hident : ∀ i (_hi : i ∈ Finset.range k),
      IdentDistrib (X i) (fun n : ℕ => (n : ℝ) + 1) P
        (geometricMeasure (h_p_pos i) (h_p_le_one i)))
    (h_int_upper :
      Integrable (fun ω => Real.exp (t_upper * ∑ i ∈ Finset.range k, X i ω)) P)
    (h_int_lower :
      Integrable (fun ω => Real.exp ((-s_lower) * ∑ i ∈ Finset.range k, X i ω)) P)
    (h_upper_rate :
      Real.exp (-p_min * μ_X * ((1 + ε) - 1 - Real.log (1 + ε))) ≤
        (1 / 2 : ℝ) * Real.exp (-((1 / 8 : ℝ) * ε ^ 2 * p_min * μ_X)))
    (h_lower_rate :
      Real.exp (-p_min * μ_X * ((1 - ε) - 1 - Real.log (1 - ε))) ≤
        (1 / 2 : ℝ) * Real.exp (-((1 / 8 : ℝ) * ε ^ 2 * p_min * μ_X))) :
    ∃ C : ℝ, 0 < C ∧
      P.real {ω | (1 - ε) * μ_X ≤ ∑ i ∈ Finset.range k, X i ω ∧
                  ∑ i ∈ Finset.range k, X i ω ≤ (1 + ε) * μ_X} ≥
        1 - Real.exp (- C * ε ^ 2 * p_min * μ_X) := by
  have hlam_upper : 1 ≤ 1 + ε := by linarith
  have hlam_lower_le : 1 - ε ≤ 1 := by linarith
  have hlam_lower_pos : 0 < 1 - ε := by linarith
  have h_upper :
      P.real {ω | (1 + ε) * μ_X ≤ ∑ i ∈ Finset.range k, X i ω} ≤
        (1 / 2 : ℝ) * Real.exp (-((1 / 8 : ℝ) * ε ^ 2 * p_min * μ_X)) := by
    have htail :=
      janson_geom_upper_tail_of_shifted_geometric_iInf_parameter
        (P := P) (k := k) (X := X) h_indep h_meas h_geom_ge_one h_support
        p h_p_pos h_p_le_one h_geom_dist μ_X hμ_X p_min hp_min
        (lam := 1 + ε) hlam_upper (t := t_upper) ht_upper_pos ht_upper
        hident h_int_upper
    exact htail.trans h_upper_rate
  have h_lower :
      P.real {ω | ∑ i ∈ Finset.range k, X i ω ≤ (1 - ε) * μ_X} ≤
        (1 / 2 : ℝ) * Real.exp (-((1 / 8 : ℝ) * ε ^ 2 * p_min * μ_X)) := by
    have htail :=
      janson_geom_lower_tail_of_shifted_geometric_iInf_parameter
        (P := P) (k := k) (X := X) h_indep h_meas h_geom_ge_one h_support
        p h_p_pos h_p_le_one h_geom_dist μ_X hμ_X p_min hp_min
        (lam := 1 - ε) hlam_lower_le hlam_lower_pos
        (s := s_lower) hs_lower hident h_int_lower
    exact htail.trans h_lower_rate
  exact janson_geom_concentration_of_tail_bounds
    (P := P) (k := k) (X := X) h_indep h_meas h_geom_ge_one h_support
    p h_p_pos h_p_le_one h_geom_dist μ_X hμ_X p_min hp_min
    ε hε_pos hε_lt_one h_upper h_lower

/-- Two-sided shifted-geometric Janson concentration from the optimized
`iInf`-parameter bounds, with the rate conversion proved internally.

The remaining quantitative assumption is the usual large-deviation scale
needed to absorb the two one-sided tails:
`16 log 2 ≤ ε² p_min μ_X`. -/
theorem janson_geom_concentration_of_shifted_geometric_iInf_parameters_quadratic
    {Ω : Type*}
    [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (k : ℕ) (X : ℕ → Ω → ℝ)
    (h_indep : iIndepFun X P)
    (h_meas : ∀ i, AEMeasurable (X i) P)
    (h_geom_ge_one : ∀ i, ∀ᵐ ω ∂P, 1 ≤ X i ω)
    (h_support : ∀ i ≥ k, ∀ᵐ ω ∂P, X i ω = 0)
    (p : ℕ → ℝ) (h_p_pos : ∀ i, 0 < p i) (h_p_le_one : ∀ i, p i ≤ 1)
    (h_geom_dist : ∀ i, ∫ ω, X i ω ∂P = (p i)⁻¹)
    (μ_X : ℝ) (hμ_X : μ_X = ∑ i ∈ Finset.range k, (p i)⁻¹)
    (p_min : ℝ) (hp_min : p_min = ⨅ i ∈ Finset.range k, p i)
    (ε : ℝ) (hε_pos : 0 < ε) (hε_lt_one : ε < 1)
    (t_upper : ℝ) (ht_upper_pos : 0 < t_upper)
    (ht_upper : t_upper = (1 - (1 + ε)⁻¹) * p_min)
    (s_lower : ℝ) (hs_lower : s_lower = ((1 - ε)⁻¹ - 1) * p_min)
    (hident : ∀ i (_hi : i ∈ Finset.range k),
      IdentDistrib (X i) (fun n : ℕ => (n : ℝ) + 1) P
        (geometricMeasure (h_p_pos i) (h_p_le_one i)))
    (h_int_upper :
      Integrable (fun ω => Real.exp (t_upper * ∑ i ∈ Finset.range k, X i ω)) P)
    (h_int_lower :
      Integrable (fun ω => Real.exp ((-s_lower) * ∑ i ∈ Finset.range k, X i ω)) P)
    (h_scale : (16 : ℝ) * Real.log 2 ≤ ε ^ 2 * p_min * μ_X) :
    ∃ C : ℝ, 0 < C ∧
      P.real {ω | (1 - ε) * μ_X ≤ ∑ i ∈ Finset.range k, X i ω ∧
                  ∑ i ∈ Finset.range k, X i ω ≤ (1 + ε) * μ_X} ≥
        1 - Real.exp (- C * ε ^ 2 * p_min * μ_X) := by
  let S : Ω → ℝ := fun ω => ∑ i ∈ Finset.range k, X i ω
  set A := {ω | (1 + ε) * μ_X < S ω}
  set B := {ω | S ω < (1 - ε) * μ_X}
  let x : ℝ := ε ^ 2 * p_min * μ_X
  let r : ℝ := Real.exp (-(1 / 8 : ℝ) * x)
  have hε_nonneg : 0 ≤ ε := hε_pos.le
  have hpmin_nonneg : 0 ≤ p_min :=
    janson_pmin_nonneg_of_iInf hp_min (fun i hi => (h_p_pos i).le)
  have hμ_nonneg : 0 ≤ μ_X := by
    rw [hμ_X]
    exact Finset.sum_nonneg (fun i hi => inv_nonneg.mpr (h_p_pos i).le)
  have hM_nonneg : 0 ≤ p_min * μ_X := mul_nonneg hpmin_nonneg hμ_nonneg
  have hlam_upper : 1 ≤ 1 + ε := by linarith
  have hlam_lower_le : 1 - ε ≤ 1 := by linarith
  have hlam_lower_pos : 0 < 1 - ε := by linarith
  have h_upper_rate :
      Real.exp (-p_min * μ_X * ((1 + ε) - 1 - Real.log (1 + ε))) ≤ r := by
    have hrate :
        (1 / 8 : ℝ) * ε ^ 2 ≤ (1 + ε) - 1 - Real.log (1 + ε) :=
      janson_log_rate_upper_quadratic hε_nonneg hε_lt_one.le
    have hmul := mul_le_mul_of_nonneg_right hrate hM_nonneg
    apply Real.exp_le_exp.2
    dsimp [r, x]
    nlinarith
  have h_lower_rate :
      Real.exp (-p_min * μ_X * ((1 - ε) - 1 - Real.log (1 - ε))) ≤ r := by
    have hrate :
        (1 / 8 : ℝ) * ε ^ 2 ≤ (1 - ε) - 1 - Real.log (1 - ε) :=
      janson_log_rate_lower_quadratic hε_nonneg hε_lt_one
    have hmul := mul_le_mul_of_nonneg_right hrate hM_nonneg
    apply Real.exp_le_exp.2
    dsimp [r, x]
    nlinarith
  have h_upper :
      P.real {ω | (1 + ε) * μ_X ≤ ∑ i ∈ Finset.range k, X i ω} ≤ r := by
    have htail :=
      janson_geom_upper_tail_of_shifted_geometric_iInf_parameter
        (P := P) (k := k) (X := X) h_indep h_meas h_geom_ge_one h_support
        p h_p_pos h_p_le_one h_geom_dist μ_X hμ_X p_min hp_min
        (lam := 1 + ε) hlam_upper (t := t_upper) ht_upper_pos ht_upper
        hident h_int_upper
    exact htail.trans h_upper_rate
  have h_lower :
      P.real {ω | ∑ i ∈ Finset.range k, X i ω ≤ (1 - ε) * μ_X} ≤ r := by
    have htail :=
      janson_geom_lower_tail_of_shifted_geometric_iInf_parameter
        (P := P) (k := k) (X := X) h_indep h_meas h_geom_ge_one h_support
        p h_p_pos h_p_le_one h_geom_dist μ_X hμ_X p_min hp_min
        (lam := 1 - ε) hlam_lower_le hlam_lower_pos
        (s := s_lower) hs_lower hident h_int_lower
    exact htail.trans h_lower_rate
  have hA : P.real A ≤ r := by
    exact (measureReal_mono (μ := P) (s₁ := A)
      (s₂ := {ω | (1 + ε) * μ_X ≤ ∑ i ∈ Finset.range k, X i ω})
      (by
        intro ω hω
        change (1 + ε) * μ_X < S ω at hω
        exact le_of_lt hω)).trans (by simpa [r, S] using h_upper)
  have hB : P.real B ≤ r := by
    exact (measureReal_mono (μ := P) (s₁ := B)
      (s₂ := {ω | ∑ i ∈ Finset.range k, X i ω ≤ (1 - ε) * μ_X})
      (by
        intro ω hω
        change S ω < (1 - ε) * μ_X at hω
        exact le_of_lt hω)).trans (by simpa [r, S] using h_lower)
  have h_union : P.real (A ∪ B) ≤ 2 * r := by
    calc
      P.real (A ∪ B) ≤ P.real A + P.real B := measureReal_union_le A B
      _ ≤ r + r := add_le_add hA hB
      _ = 2 * r := by ring
  have h_union_exp :
      P.real (A ∪ B) ≤ Real.exp (-(1 / 16 : ℝ) * x) :=
    h_union.trans (two_mul_exp_neg_eighth_le_exp_neg_sixteenth (by simpa [x] using h_scale))
  have h_good_eq : {ω | (1 - ε) * μ_X ≤ ∑ i ∈ Finset.range k, X i ω ∧
                       ∑ i ∈ Finset.range k, X i ω ≤ (1 + ε) * μ_X} =
      (A ∪ B)ᶜ := by
    ext ω
    simp [A, B, S, not_lt, and_comm]
  have hS : AEMeasurable S P := by
    have hS' : AEMeasurable (∑ i ∈ Finset.range k, X i) P :=
      Finset.aemeasurable_sum (Finset.range k) (fun i _ => h_meas i)
    exact hS'.congr (Filter.Eventually.of_forall (by
      intro ω
      simp [S, Finset.sum_apply]))
  have hA_meas : NullMeasurableSet A P := by
    simpa [A, S] using
      nullMeasurableSet_lt (aemeasurable_const (μ := P)) hS
  have hB_meas : NullMeasurableSet B P := by
    simpa [B, S] using
      nullMeasurableSet_lt hS (aemeasurable_const (μ := P))
  have h_compl : P.real (A ∪ B) + P.real ((A ∪ B)ᶜ) = 1 := by
    simpa using
      (measureReal_add_measureReal_compl₀ (μ := P) (hA_meas.union hB_meas))
  have h_final : P.real ((A ∪ B)ᶜ) ≥ 1 - Real.exp (-(1 / 16 : ℝ) * x) := by
    linarith
  refine ⟨1 / 16, by norm_num, ?_⟩
  rw [h_good_eq]
  simpa [x, mul_assoc] using h_final

/-- Two-sided shifted-geometric Janson concentration with integrability derived
from the shifted-geometric MGF convergence conditions. -/
theorem janson_geom_concentration_of_shifted_geometric_iInf_parameters_quadratic_of_convergent
    {Ω : Type*}
    [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (k : ℕ) (X : ℕ → Ω → ℝ)
    (h_indep : iIndepFun X P)
    (h_meas : ∀ i, AEMeasurable (X i) P)
    (h_geom_ge_one : ∀ i, ∀ᵐ ω ∂P, 1 ≤ X i ω)
    (h_support : ∀ i ≥ k, ∀ᵐ ω ∂P, X i ω = 0)
    (p : ℕ → ℝ) (h_p_pos : ∀ i, 0 < p i) (h_p_le_one : ∀ i, p i ≤ 1)
    (h_geom_dist : ∀ i, ∫ ω, X i ω ∂P = (p i)⁻¹)
    (μ_X : ℝ) (hμ_X : μ_X = ∑ i ∈ Finset.range k, (p i)⁻¹)
    (p_min : ℝ) (hp_min : p_min = ⨅ i ∈ Finset.range k, p i)
    (ε : ℝ) (hε_pos : 0 < ε) (hε_lt_one : ε < 1)
    (t_upper : ℝ) (ht_upper_pos : 0 < t_upper)
    (ht_upper : t_upper = (1 - (1 + ε)⁻¹) * p_min)
    (s_lower : ℝ) (hs_lower : s_lower = ((1 - ε)⁻¹ - 1) * p_min)
    (hconv_upper : ∀ i ∈ Finset.range k, (1 - p i) * Real.exp t_upper < 1)
    (hconv_lower : ∀ i ∈ Finset.range k, (1 - p i) * Real.exp (-s_lower) < 1)
    (hident : ∀ i (_hi : i ∈ Finset.range k),
      IdentDistrib (X i) (fun n : ℕ => (n : ℝ) + 1) P
        (geometricMeasure (h_p_pos i) (h_p_le_one i)))
    (h_scale : (16 : ℝ) * Real.log 2 ≤ ε ^ 2 * p_min * μ_X) :
    ∃ C : ℝ, 0 < C ∧
      P.real {ω | (1 - ε) * μ_X ≤ ∑ i ∈ Finset.range k, X i ω ∧
                  ∑ i ∈ Finset.range k, X i ω ≤ (1 + ε) * μ_X} ≥
        1 - Real.exp (- C * ε ^ 2 * p_min * μ_X) := by
  have h_int_upper :
      Integrable (fun ω => Real.exp (t_upper * ∑ i ∈ Finset.range k, X i ω)) P :=
    shifted_geometric_integrable_exp_sum_of_identDistrib
      (P := P) (k := k) (X := X) (p := p) (t := t_upper)
      h_indep h_meas (fun i _ => h_p_pos i) (fun i _ => h_p_le_one i)
      hconv_upper (fun i hi => hident i hi)
  have h_int_lower :
      Integrable (fun ω => Real.exp ((-s_lower) * ∑ i ∈ Finset.range k, X i ω)) P :=
    shifted_geometric_integrable_exp_sum_of_identDistrib
      (P := P) (k := k) (X := X) (p := p) (t := -s_lower)
      h_indep h_meas (fun i _ => h_p_pos i) (fun i _ => h_p_le_one i)
      hconv_lower (fun i hi => hident i hi)
  exact janson_geom_concentration_of_shifted_geometric_iInf_parameters_quadratic
    (P := P) (k := k) (X := X) h_indep h_meas h_geom_ge_one h_support
    p h_p_pos h_p_le_one h_geom_dist μ_X hμ_X p_min hp_min
    ε hε_pos hε_lt_one t_upper ht_upper_pos ht_upper s_lower hs_lower
    hident h_int_upper h_int_lower h_scale

/-- Two-sided shifted-geometric Janson concentration with the optimized
Chernoff parameters and all MGF convergence/integrability side conditions
derived internally. -/
theorem janson_geom_concentration_of_shifted_geometric_iInf_parameters_quadratic_auto
    {Ω : Type*}
    [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (k : ℕ) (X : ℕ → Ω → ℝ)
    (h_indep : iIndepFun X P)
    (h_meas : ∀ i, AEMeasurable (X i) P)
    (h_geom_ge_one : ∀ i, ∀ᵐ ω ∂P, 1 ≤ X i ω)
    (h_support : ∀ i ≥ k, ∀ᵐ ω ∂P, X i ω = 0)
    (p : ℕ → ℝ) (h_p_pos : ∀ i, 0 < p i) (h_p_le_one : ∀ i, p i ≤ 1)
    (h_geom_dist : ∀ i, ∫ ω, X i ω ∂P = (p i)⁻¹)
    (μ_X : ℝ) (hμ_X : μ_X = ∑ i ∈ Finset.range k, (p i)⁻¹)
    (p_min : ℝ) (hp_min : p_min = ⨅ i ∈ Finset.range k, p i)
    (ε : ℝ) (hε_pos : 0 < ε) (hε_lt_one : ε < 1)
    (hident : ∀ i (_hi : i ∈ Finset.range k),
      IdentDistrib (X i) (fun n : ℕ => (n : ℝ) + 1) P
        (geometricMeasure (h_p_pos i) (h_p_le_one i)))
    (h_scale : (16 : ℝ) * Real.log 2 ≤ ε ^ 2 * p_min * μ_X) :
    ∃ C : ℝ, 0 < C ∧
      P.real {ω | (1 - ε) * μ_X ≤ ∑ i ∈ Finset.range k, X i ω ∧
                  ∑ i ∈ Finset.range k, X i ω ≤ (1 + ε) * μ_X} ≥
        1 - Real.exp (- C * ε ^ 2 * p_min * μ_X) := by
  let t_upper : ℝ := (1 - (1 + ε)⁻¹) * p_min
  let s_lower : ℝ := ((1 - ε)⁻¹ - 1) * p_min
  have hpmin_nonneg : 0 ≤ p_min :=
    janson_pmin_nonneg_of_iInf hp_min (fun i hi => (h_p_pos i).le)
  have hpmin_le : ∀ i ∈ Finset.range k, p_min ≤ p i :=
    janson_pmin_le_of_iInf hp_min (fun i hi => (h_p_pos i).le)
  have hμ_nonneg : 0 ≤ μ_X := by
    rw [hμ_X]
    exact Finset.sum_nonneg (fun i hi => inv_nonneg.mpr (h_p_pos i).le)
  have hx_pos : 0 < ε ^ 2 * p_min * μ_X := by
    exact lt_of_lt_of_le
      (mul_pos (by norm_num : (0 : ℝ) < 16) (Real.log_pos (by norm_num : (1 : ℝ) < 2)))
      h_scale
  have hM_pos : 0 < p_min * μ_X := by
    have hεsq_pos : 0 < ε ^ 2 := sq_pos_of_ne_zero hε_pos.ne'
    nlinarith
  have hpmin_pos : 0 < p_min := by
    by_contra hnot
    have hpmin_nonpos : p_min ≤ 0 := le_of_not_gt hnot
    have hprod_nonpos : p_min * μ_X ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hpmin_nonpos hμ_nonneg
    nlinarith
  have hcoeff_upper_pos : 0 < 1 - (1 + ε)⁻¹ := by
    have hlt : (1 + ε)⁻¹ < 1 := by
      have hlt' : (1 + ε)⁻¹ < (1 : ℝ)⁻¹ :=
        (inv_lt_inv₀ (by linarith : (0 : ℝ) < 1 + ε) (by norm_num : (0 : ℝ) < 1)).2
          (by linarith)
      simpa using hlt'
    linarith
  have hcoeff_upper_lt_one : 1 - (1 + ε)⁻¹ < 1 := by
    have hpos : 0 < (1 + ε)⁻¹ := inv_pos.mpr (by linarith)
    linarith
  have ht_upper_pos : 0 < t_upper := by
    dsimp [t_upper]
    exact mul_pos hcoeff_upper_pos hpmin_pos
  have hconv_upper : ∀ i ∈ Finset.range k, (1 - p i) * Real.exp t_upper < 1 := by
    intro i hi
    have ht_lt_pmin : t_upper < p_min := by
      dsimp [t_upper]
      simpa using mul_lt_mul_of_pos_right hcoeff_upper_lt_one hpmin_pos
    have ht_lt_pi : t_upper < p i := ht_lt_pmin.trans_le (hpmin_le i hi)
    exact shifted_geometric_mgf_converges_of_nonneg_lt
      (h_p_pos i) ht_upper_pos.le ht_lt_pi
  have hcoeff_lower_nonneg : 0 ≤ (1 - ε)⁻¹ - 1 := by
    have hpos : 0 < 1 - ε := by linarith
    have hle : 1 - ε ≤ 1 := by linarith
    have hone_le_inv : 1 ≤ (1 - ε)⁻¹ := (one_le_inv₀ hpos).2 hle
    linarith
  have hs_lower_nonneg : 0 ≤ s_lower := by
    dsimp [s_lower]
    exact mul_nonneg hcoeff_lower_nonneg hpmin_nonneg
  have hconv_lower : ∀ i ∈ Finset.range k, (1 - p i) * Real.exp (-s_lower) < 1 := by
    intro i hi
    exact shifted_geometric_mgf_converges_of_nonpos
      (h_p_pos i) (h_p_le_one i) (neg_nonpos.mpr hs_lower_nonneg)
  exact janson_geom_concentration_of_shifted_geometric_iInf_parameters_quadratic_of_convergent
    (P := P) (k := k) (X := X) h_indep h_meas h_geom_ge_one h_support
    p h_p_pos h_p_le_one h_geom_dist μ_X hμ_X p_min hp_min
    ε hε_pos hε_lt_one t_upper ht_upper_pos rfl s_lower rfl
    hconv_upper hconv_lower hident h_scale

end ExactMajority
