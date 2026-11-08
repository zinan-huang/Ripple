import Ripple.Number.Modular.Phi41Fricke
import Ripple.Number.Modular.SturmPacked

/-!
# The level-41 cleared form vanishes

`phi41Level41ClearedAsModularForm = 0`, from the Fricke-halved Sturm theorem
(`levelGamma0_41_sturm_weight_1008_of_S`) and the packed certificate for the first `1765`
coefficients (`phi41Level41FrickeCoefficientCertificate_proof`). Every coefficient of the cleared
expansion is then `0`; in particular the `3529`-coefficient statements
`phi41Level41SturmCoefficientCertificate_proof` and
`phi41Level41RecurrenceCoeffArrayFirstZero_sturmBound` follow, as corollaries of `F = 0` rather than
by a computation of `3529` coefficients.
-/

namespace Ripple.Number.Modular

open scoped UpperHalfPlane

private theorem coeff_deltaQExpansion_eq_deltaEulerCoeff_of_hasSum
    (hsum :
      ∀ τ : ℍ,
        HasSum (fun d : ℕ =>
          deltaEulerCoeff d • Function.Periodic.qParam 1 (τ : ℂ) ^ d)
          (ModularForm.discriminant τ))
    (d : ℕ) :
    PowerSeries.coeff (R := ℂ) d deltaQExpansion = deltaEulerCoeff d := by
  unfold deltaQExpansion
  exact (ModularFormClass.qExpansion_coeff_unique (f := deltaLevelOneMF) one_pos
    one_mem_strictPeriods_SL hsum d).symm

theorem deltaQExpansion_eq_deltaEulerSeries_of_delta_hasSum
    (hsum :
      ∀ τ : ℍ,
        HasSum (fun d : ℕ =>
          deltaEulerCoeff d • Function.Periodic.qParam 1 (τ : ℂ) ^ d)
          (ModularForm.discriminant τ)) :
    deltaQExpansion = deltaEulerSeries := by
  exact deltaQExpansion_eq_deltaEulerSeries_of_coeff
    (coeff_deltaQExpansion_eq_deltaEulerCoeff_of_hasSum hsum)

theorem deltaQExpansion_eq_deltaEulerSeries :
    deltaQExpansion = deltaEulerSeries := by
  exact deltaQExpansion_eq_deltaEulerSeries_of_delta_hasSum delta_hasSum_deltaEulerCoeff

/-- The bridge of `q`-expansions for the cleared form. -/
private theorem phi41Level41ClearedAsModularForm_qExpansion_toFun :
    ModularFormClass.qExpansion (1 : ℝ) phi41Level41ClearedAsModularForm.toFun =
      phi41Level41ClearedEulerQExpansion :=
  phi41Level41ClearedAsModularForm_qExpansion deltaQExpansion_eq_deltaEulerSeries

/-- `Δ(τ)^42 Δ(41τ)^42 Φ₄₁(j(41τ), j(τ)) = 0`. -/
theorem phi41Level41ClearedAsModularForm_eq_zero : phi41Level41ClearedAsModularForm = 0 := by
  refine levelGamma0_41_sturm_weight_1008_of_S phi41Level41ClearedAsModularForm
    ((41 : ℂ)⁻¹ ^ 504) phi41Level41ClearedAsModularForm_S ?_
  intro n hn
  rw [phi41Level41ClearedAsModularForm_qExpansion_toFun,
    coeff_phi41Level41ClearedEulerQExpansion_eq_map_coeffZ,
    phi41Level41FrickeCoefficientCertificate_proof n hn, Int.cast_zero]

/-- Every coefficient of the cleared level-41 expansion vanishes. -/
theorem phi41Level41ClearedEulerQExpansionZ_coeff_eq_zero_of_fricke (n : ℕ) :
    PowerSeries.coeff (R := ℤ) n phi41Level41ClearedEulerQExpansionZ = 0 := by
  have hq : ModularFormClass.qExpansion (1 : ℝ) phi41Level41ClearedAsModularForm.toFun = 0 :=
    (gamma0_41_qExpansion_eq_zero_iff _).mpr phi41Level41ClearedAsModularForm_eq_zero
  rw [phi41Level41ClearedAsModularForm_qExpansion_toFun] at hq
  have hC := congrArg (PowerSeries.coeff (R := ℂ) n) hq
  rw [coeff_phi41Level41ClearedEulerQExpansion_eq_map_coeffZ, map_zero] at hC
  exact_mod_cast hC

/-- The first `3529` coefficients vanish (now a corollary of the vanishing of the form). -/
theorem phi41Level41SturmCoefficientCertificate_proof :
    phi41Level41SturmCoefficientCertificate :=
  fun n _ => phi41Level41ClearedEulerQExpansionZ_coeff_eq_zero_of_fricke n

/-- The recurrence-array form of the Sturm certificate, recovered from the coefficient
statement. -/
theorem phi41Level41RecurrenceCoeffArrayFirstZero_sturmBound :
    phi41Level41RecurrenceCoeffArrayFirstZero phi41Level41SturmBound = true := by
  have hrep :=
    phi41Level41ClearedEulerQExpansionZ_TruncRep_compressedMatrix phi41Level41SturmBound
  have harray :=
    ListArrayEq.phi41Level41CoeffCompressedMatrix_of_derivative_identities
      phi41Level41SturmBound
      (fun j hj => phi41LevelOneDenseRow_derivative_identity_of_base j hj
        (E4ZSeries_cubed_derivative_identity_of_E4_derivative_identity
          E4ZSeries_derivative_identity)
        deltaEulerSeriesZ_derivative_identity)
  unfold phi41Level41RecurrenceCoeffArrayFirstZero truncCoeffArrayFirstZero
  rw [List.all_eq_true]
  intro n hn
  have hn' : n < phi41Level41SturmBound := List.mem_range.mp hn
  rw [beq_iff_eq, ← harray n hn', ← hrep n hn']
  exact phi41Level41SturmCoefficientCertificate_proof n hn'

end Ripple.Number.Modular
