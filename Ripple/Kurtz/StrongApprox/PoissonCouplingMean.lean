/-
  Ripple.Kurtz.StrongApprox.PoissonCouplingMean — (W1), first half: the Poisson–normal quantile
  coupling error has mean zero

  The coupled count `Q = poisCoupling h ∘ Z` has point masses `P{Q = k} = e^{−h} h^k / k!`
  (from the law `measure_poisCoupling_le`), hence `E Q = Σ_k k e^{−h} h^k / k! = h`; with `E Z = 0`
  this gives `E (Q − h − √h Z) = 0`.
-/

import Mathlib
import Ripple.Kurtz.StrongApprox.PoissonCouplingMoment

namespace Ripple.Kurtz.StrongApprox

open MeasureTheory ProbabilityTheory Set

/-! ### The Poisson mean -/

theorem hasSum_poisTerm {h : ℝ} (hh : 0 ≤ h) : HasSum (fun j => poisTerm j h) 1 := by
  have := hasSum_one_poissonMeasure ⟨h, hh⟩
  simpa [poisTerm] using this

theorem poisTerm_succ_mul (j : ℕ) (h : ℝ) :
    ((j + 1 : ℕ) : ℝ) * poisTerm (j + 1) h = h * poisTerm j h := by
  unfold poisTerm
  rw [Nat.factorial_succ]
  push_cast
  field_simp
  ring

theorem hasSum_mul_poisTerm {h : ℝ} (hh : 0 ≤ h) :
    HasSum (fun k : ℕ => (k : ℝ) * poisTerm k h) h := by
  have e : (fun j : ℕ => ((j + 1 : ℕ) : ℝ) * poisTerm (j + 1) h) = fun j => h * poisTerm j h :=
    funext fun j => poisTerm_succ_mul j h
  have h1 : HasSum (fun j : ℕ => ((j + 1 : ℕ) : ℝ) * poisTerm (j + 1) h) h := by
    rw [e]; simpa using (hasSum_poisTerm hh).mul_left h
  have h2 : HasSum (fun n : ℕ => ((n + 1 : ℕ) : ℝ) * poisTerm (n + 1) h)
      (h - ∑ i ∈ Finset.range 1, (i : ℝ) * poisTerm i h) := by
    simpa using h1
  exact (hasSum_nat_add_iff' 1).mp h2

/-- `Σ_k k e^{−h} h^k / k! = h`. -/
theorem tsum_mul_poisTerm {h : ℝ} (hh : 0 ≤ h) : ∑' k : ℕ, (k : ℝ) * poisTerm k h = h :=
  (hasSum_mul_poisTerm hh).tsum_eq

/-! ### Point masses of the coupled count -/

/-- `P{Q = k} = e^{−h} h^k / k!`. -/
theorem measure_poisCoupling_eq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {Z : Ω → ℝ} (hZ : Measurable Z) (hlaw : P.map Z = gaussianReal 0 1)
    {h : ℝ} (hh : 0 < h) (k : ℕ) :
    P {ω | poisCoupling h (Z ω) = k} = ENNReal.ofReal (poisTerm k h) := by
  cases k with
  | zero =>
    have := measure_natQuantile_eq_zero P (poisF_monotone hh.le) (poisF_nonneg hh.le)
      (poisF_le_one hh.le) (fun ω => exists_poisF_ge hh (Z ω))
      (fun t ht0 ht1 => measure_stdNormalCdf_comp_le P hZ hlaw ht0 ht1)
    unfold poisCoupling
    rw [this]
    congr 1
    simp [poisF, poisCdf, poisTerm]
  | succ j =>
    have hU : Measurable fun ω => stdNormalCdf (Z ω) := stdNormalCdf_continuous.measurable.comp hZ
    have := measure_natQuantile_eq_succ P (poisF_monotone hh.le) (poisF_nonneg hh.le)
      (poisF_le_one hh.le) hU (fun ω => exists_poisF_ge hh (Z ω))
      (fun t ht0 ht1 => measure_stdNormalCdf_comp_le P hZ hlaw ht0 ht1) j
    unfold poisCoupling
    rw [this, ← ENNReal.ofReal_sub _ (poisF_nonneg hh.le j)]
    congr 1
    unfold poisF
    rw [poisCdf_succ (j + 1)]
    ring

/-! ### Mean of the coupled count -/

theorem integrable_poisCoupling {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {Z : Ω → ℝ} (hZ : Measurable Z) (hlaw : P.map Z = gaussianReal 0 1)
    {h : ℝ} (hh : 0 < h) :
    Integrable (fun ω => (poisCoupling h (Z ω) : ℝ)) P := by
  have hQm : Measurable fun ω => poisCoupling h (Z ω) := (measurable_poisCoupling hh).comp hZ
  have hcoe : Measurable fun n : ℕ => (n : ℝ) := measurable_from_nat
  have hZ1 : Integrable (fun x : ℝ => |x|) (gaussianReal 0 1) := by
    have := integrable_pow_of_mem_interior_integrableExpSet zero_mem_interior_integrableExpSet 1
    simpa using this.abs
  have hZ2 : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 1) :=
    integrable_pow_of_mem_interior_integrableExpSet zero_mem_interior_integrableExpSet 2
  have hg : Integrable (fun x : ℝ => h + Real.sqrt h * |x| + 1 + 2 * x ^ 2) (gaussianReal 0 1) :=
    (((integrable_const h).add (hZ1.const_mul _)).add (integrable_const 1)).add (hZ2.const_mul 2)
  rw [← hlaw] at hg
  have hgP := hg.comp_measurable hZ
  refine hgP.mono' (hcoe.comp hQm).aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
  show ‖(poisCoupling h (Z ω) : ℝ)‖ ≤ h + Real.sqrt h * |Z ω| + 1 + 2 * Z ω ^ 2
  have hb := abs_poisCoupling_sub_le hh (Z ω)
  rw [abs_le] at hb
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
  have : Real.sqrt h * Z ω ≤ Real.sqrt h * |Z ω| :=
    mul_le_mul_of_nonneg_left (le_abs_self _) (Real.sqrt_nonneg _)
  linarith [hb.2]

/-- `E Q = h`: the coupled count has the Poisson mean. -/
theorem integral_poisCoupling {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {Z : Ω → ℝ} (hZ : Measurable Z) (hlaw : P.map Z = gaussianReal 0 1)
    {h : ℝ} (hh : 0 < h) :
    ∫ ω, (poisCoupling h (Z ω) : ℝ) ∂P = h := by
  have hQm : Measurable fun ω => poisCoupling h (Z ω) := (measurable_poisCoupling hh).comp hZ
  have hcoe : Measurable fun n : ℕ => (n : ℝ) := measurable_from_nat
  have hint := integrable_poisCoupling P hZ hlaw hh
  have hmap : ∀ k : ℕ, (P.map fun ω => poisCoupling h (Z ω)) {k} = ENNReal.ofReal (poisTerm k h) := by
    intro k
    rw [Measure.map_apply hQm (measurableSet_singleton k)]
    exact measure_poisCoupling_eq P hZ hlaw hh k
  calc ∫ ω, (poisCoupling h (Z ω) : ℝ) ∂P
      = ∫ n : ℕ, (n : ℝ) ∂(P.map fun ω => poisCoupling h (Z ω)) := by
        rw [integral_map hQm.aemeasurable hcoe.aestronglyMeasurable]
    _ = ∑' k : ℕ, (P.map fun ω => poisCoupling h (Z ω)).real {k} • (k : ℝ) := by
        apply integral_countable
        rw [integrable_map_measure hcoe.aestronglyMeasurable hQm.aemeasurable]
        exact hint
    _ = ∑' k : ℕ, (k : ℝ) * poisTerm k h := by
        congr 1; funext k
        rw [measureReal_def, hmap k, ENNReal.toReal_ofReal (poisTerm_nonneg k hh.le), smul_eq_mul,
          mul_comm]
    _ = h := tsum_mul_poisTerm hh.le

/-- **(W1), mean**: `E (Q − h − √h Z) = 0`. -/
theorem integral_poisCoupling_error {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {Z : Ω → ℝ} (hZ : Measurable Z) (hlaw : P.map Z = gaussianReal 0 1)
    {h : ℝ} (hh : 0 < h) :
    ∫ ω, ((poisCoupling h (Z ω) : ℝ) - h - Real.sqrt h * Z ω) ∂P = 0 := by
  have hZint : Integrable Z P := by
    have h1 : Integrable (fun x : ℝ => x) (gaussianReal 0 1) := by
      simpa using integrable_pow_of_mem_interior_integrableExpSet zero_mem_interior_integrableExpSet 1
    rw [← hlaw] at h1
    exact h1.comp_measurable hZ
  have hZmean : ∫ ω, Z ω ∂P = 0 := by
    have := integral_map (μ := P) (φ := Z) hZ.aemeasurable (f := fun x : ℝ => x)
      measurable_id.aestronglyMeasurable
    rw [hlaw, integral_id_gaussianReal] at this
    exact this.symm
  have hQint := integrable_poisCoupling P hZ hlaw hh
  have h1 : Integrable (fun ω => (poisCoupling h (Z ω) : ℝ) - h) P := hQint.sub (integrable_const h)
  have h2 : Integrable (fun ω => Real.sqrt h * Z ω) P := hZint.const_mul _
  rw [integral_sub h1 h2, integral_sub hQint (integrable_const h), integral_poisCoupling P hZ hlaw hh,
    integral_const, integral_const_mul, hZmean]
  simp [measureReal_univ_eq_one]

end Ripple.Kurtz.StrongApprox
