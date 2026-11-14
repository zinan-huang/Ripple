/-
  Ripple.Kurtz.StrongApprox.NormalTail — a lower bound for the standard normal upper tail

  Mathematics: a Mills-type bound with a weak constant.

  `stdNormalTail u = ∫_{u}^{∞} φ`, `φ = gaussianPDFReal 0 1`.  For `u > 0`,
  `stdNormalTail u ≥ (1/u) φ(u + 1/u)`, hence for `u ≥ 1`
  `stdNormalTail u ≥ exp(−u²/2 − 3/2) / (√(2π) u)`.  This weak Mills bound is all the large
  regime of Lemma T needs.
-/

import Mathlib

namespace Ripple.Kurtz.StrongApprox

open MeasureTheory ProbabilityTheory Set Real

/-- The standard normal upper tail `Φ̄(u) = ∫_{u}^{∞} φ`. -/
noncomputable def stdNormalTail (u : ℝ) : ℝ := ∫ x in Ioi u, gaussianPDFReal 0 1 x

theorem gaussianPDFReal_zero_one (x : ℝ) :
    gaussianPDFReal 0 1 x = (Real.sqrt (2 * π))⁻¹ * Real.exp (-(x ^ 2) / 2) := by
  rw [gaussianPDFReal]; simp

theorem gaussianPDFReal_zero_one_antitoneOn : AntitoneOn (gaussianPDFReal 0 1) (Ici 0) := by
  intro x hx y hy hxy
  rw [gaussianPDFReal_zero_one, gaussianPDFReal_zero_one]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  have hx0 : 0 ≤ x := hx
  nlinarith

/-- Tail lower bound by the integral over `(u, u + 1/u]`. -/
theorem stdNormalTail_ge {u : ℝ} (hu : 0 < u) :
    (1 / u) * gaussianPDFReal 0 1 (u + 1 / u) ≤ stdNormalTail u := by
  have hint : IntegrableOn (gaussianPDFReal 0 1) (Ioi u) volume :=
    (integrable_gaussianPDFReal 0 1).integrableOn
  have h1 : ∫ x in Ioc u (u + 1 / u), gaussianPDFReal 0 1 x ≤ stdNormalTail u := by
    unfold stdNormalTail
    apply setIntegral_mono_set hint
    · exact Filter.Eventually.of_forall fun x => gaussianPDFReal_nonneg 0 1 x
    · exact Filter.Eventually.of_forall Ioc_subset_Ioi_self
  have hpos : (0 : ℝ) ≤ u + 1 / u := by have := one_div_pos.mpr hu; linarith
  have h2 : volume.real (Ioc u (u + 1 / u)) • gaussianPDFReal 0 1 (u + 1 / u) ≤
      ∫ x in Ioc u (u + 1 / u), gaussianPDFReal 0 1 x := by
    apply setIntegral_ge_of_const_le measurableSet_Ioc
    · exact measure_Ioc_lt_top.ne
    · intro x hx
      apply gaussianPDFReal_zero_one_antitoneOn
      · exact (hu.trans hx.1).le
      · exact hpos
      · exact hx.2
    · exact (integrable_gaussianPDFReal 0 1).integrableOn
  have hvol : volume.real (Ioc u (u + 1 / u)) = 1 / u := by
    rw [measureReal_def, Real.volume_Ioc,
      ENNReal.toReal_ofReal (by have := one_div_pos.mpr hu; linarith)]
    ring
  rw [hvol, smul_eq_mul] at h2
  linarith

/-- Explicit weak Mills bound: for `u ≥ 1`, `Φ̄(u) ≥ exp(−u²/2 − 3/2) / (√(2π) u)`. -/
theorem stdNormalTail_ge_exp {u : ℝ} (hu : 1 ≤ u) :
    Real.exp (-(u ^ 2) / 2 - 3 / 2) / (Real.sqrt (2 * π) * u) ≤ stdNormalTail u := by
  have hu0 : 0 < u := by linarith
  refine le_trans ?_ (stdNormalTail_ge hu0)
  rw [gaussianPDFReal_zero_one]
  have hexp : Real.exp (-(u ^ 2) / 2 - 3 / 2) ≤ Real.exp (-((u + 1 / u) ^ 2) / 2) := by
    apply Real.exp_le_exp.mpr
    have h1 : 1 / u ≤ 1 := by rw [div_le_one hu0]; exact hu
    have h2 : (1 / u) ^ 2 ≤ 1 := by nlinarith [one_div_pos.mpr hu0]
    have h3 : u * (1 / u) = 1 := by field_simp
    nlinarith
  have hs : 0 < Real.sqrt (2 * π) := Real.sqrt_pos.mpr (by positivity)
  calc Real.exp (-(u ^ 2) / 2 - 3 / 2) / (Real.sqrt (2 * π) * u)
      ≤ Real.exp (-((u + 1 / u) ^ 2) / 2) / (Real.sqrt (2 * π) * u) := by gcongr
    _ = 1 / u * ((Real.sqrt (2 * π))⁻¹ * Real.exp (-((u + 1 / u) ^ 2) / 2)) := by
        field_simp

end Ripple.Kurtz.StrongApprox
