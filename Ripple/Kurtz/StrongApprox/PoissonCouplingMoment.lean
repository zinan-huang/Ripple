/-
  Ripple.Kurtz.StrongApprox.PoissonCouplingMoment — (W1): the Poisson–normal quantile coupling has
  error second moment at most `17`

  `poisCoupling h z = natQuantile (poisF h) (Φ z)` is monotone in `z`, hence measurable; with
  `Z ~ N(0,1)` the variable `Q = poisCoupling h ∘ Z` has cdf `P(Pois(h) ≤ k)` (`GaussianCdf`),
  and `R = Q − h − √h Z` satisfies `|R| ≤ 1 + 2Z²` pointwise (PQ), so `E R² ≤ E(1+2Z²)² = 17`.
-/

import Mathlib
import Ripple.Kurtz.StrongApprox.PoissonQuantileBound
import Ripple.Kurtz.StrongApprox.GaussianMoments
import Ripple.Kurtz.StrongApprox.GaussianCdf

namespace Ripple.Kurtz.StrongApprox

open MeasureTheory ProbabilityTheory Set

/-- The Poisson(h) quantile coupling map `z ↦ F_{Pois(h)}^{-1}(Φ z)`. -/
noncomputable def poisCoupling (h z : ℝ) : ℕ := natQuantile (poisF h) (stdNormalCdf z)

theorem poisCoupling_monotone {h : ℝ} (hh : 0 < h) : Monotone (poisCoupling h) := by
  intro z z' hzz'
  unfold poisCoupling
  have hex' := exists_poisF_ge hh z'
  have h1 : stdNormalCdf z' ≤ poisF h (natQuantile (poisF h) (stdNormalCdf z')) :=
    le_apply_natQuantile hex'
  exact natQuantile_le_of_le ((stdNormalCdf_monotone hzz').trans h1)

theorem measurable_poisCoupling {h : ℝ} (hh : 0 < h) : Measurable (poisCoupling h) :=
  (poisCoupling_monotone hh).measurable

/-- (PQ) for the coupling map. -/
theorem abs_poisCoupling_sub_le {h : ℝ} (hh : 0 < h) (z : ℝ) :
    |(poisCoupling h z : ℝ) - h - Real.sqrt h * z| ≤ 1 + 2 * z ^ 2 :=
  poisson_quantile_bound hh rfl

/-- The coupled count has the Poisson(h) cdf: `P{Q ≤ k} = P(Pois(h) ≤ k)`. -/
theorem measure_poisCoupling_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {Z : Ω → ℝ} (hZ : Measurable Z) (hlaw : P.map Z = gaussianReal 0 1)
    {h : ℝ} (hh : 0 < h) (k : ℕ) :
    P {ω | poisCoupling h (Z ω) ≤ k} = ENNReal.ofReal (poisCdf (k + 1) h) :=
  measure_natQuantile_le P (poisF_monotone hh.le) (poisF_nonneg hh.le) (poisF_le_one hh.le)
    (fun ω => exists_poisF_ge hh (Z ω))
    (fun t ht0 ht1 => measure_stdNormalCdf_comp_le P hZ hlaw ht0 ht1) k

/-- **(W1)**: `E (Q − h − √h Z)² ≤ 17`. -/
theorem integral_poisCoupling_error_sq_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {Z : Ω → ℝ} (hZ : Measurable Z) (hlaw : P.map Z = gaussianReal 0 1)
    {h : ℝ} (hh : 0 < h) :
    ∫ ω, ((poisCoupling h (Z ω) : ℝ) - h - Real.sqrt h * Z ω) ^ 2 ∂P ≤ 17 := by
  have hpt : ∀ ω, ((poisCoupling h (Z ω) : ℝ) - h - Real.sqrt h * Z ω) ^ 2 ≤
      (1 + 2 * Z ω ^ 2) ^ 2 := by
    intro ω
    have := abs_poisCoupling_sub_le hh (Z ω)
    have h0 : 0 ≤ |(poisCoupling h (Z ω) : ℝ) - h - Real.sqrt h * Z ω| := abs_nonneg _
    calc ((poisCoupling h (Z ω) : ℝ) - h - Real.sqrt h * Z ω) ^ 2
        = |(poisCoupling h (Z ω) : ℝ) - h - Real.sqrt h * Z ω| ^ 2 := (sq_abs _).symm
      _ ≤ (1 + 2 * Z ω ^ 2) ^ 2 := by gcongr
  have hg_int : Integrable (fun x : ℝ => (1 + 2 * x ^ 2) ^ 2) (gaussianReal 0 1) := by
    have h2 := integrable_pow_of_mem_interior_integrableExpSet zero_mem_interior_integrableExpSet 2
    have h4 := integrable_pow_of_mem_interior_integrableExpSet zero_mem_interior_integrableExpSet 4
    have hfun : (fun x : ℝ => (1 + 2 * x ^ 2) ^ 2) = fun x => (1 + 4 * x ^ 2) + 4 * x ^ 4 := by
      funext x; ring
    rw [hfun]
    refine ((integrable_const 1).add ?_).add ?_
    · simpa using h2.const_mul 4
    · simpa using h4.const_mul 4
  have hcomp : Integrable (fun ω => (1 + 2 * Z ω ^ 2) ^ 2) P := by
    rw [← hlaw] at hg_int
    exact hg_int.comp_measurable hZ
  calc ∫ ω, ((poisCoupling h (Z ω) : ℝ) - h - Real.sqrt h * Z ω) ^ 2 ∂P
      ≤ ∫ ω, (1 + 2 * Z ω ^ 2) ^ 2 ∂P := by
        apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => sq_nonneg _) hcomp
        exact Filter.Eventually.of_forall hpt
    _ = ∫ x, (1 + 2 * x ^ 2) ^ 2 ∂(P.map Z) := by
        rw [integral_map hZ.aemeasurable (by fun_prop : Measurable fun x : ℝ => (1 + 2 * x ^ 2) ^ 2).aestronglyMeasurable]
    _ = 17 := by rw [hlaw]; exact integral_one_add_two_sq_sq_gaussianReal

end Ripple.Kurtz.StrongApprox
