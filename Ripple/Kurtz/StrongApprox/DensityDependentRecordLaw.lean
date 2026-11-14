-- Ripple/Kurtz/StrongApprox/DensityDependentRecordLaw.lean
import Ripple.Kurtz.StrongApprox.RecordPastFreshness
import Ripple.sCRNUniversality.CTMCIdentification
import Ripple.CTMC.DensityDependent

noncomputable section

namespace Ripple.Kurtz.StrongApprox

open MeasureTheory ProbabilityTheory Preorder Finset
open scoped ENNReal BigOperators
open Ripple.CTMC
open Ripple.sCRNUniversality.CTMCIdentification

variable {d : ℕ}

/-- The existing density-dependent Q-matrix aggregates every listed channel
whose integer jump has the requested destination. -/
theorem density_offdiag_rate_aggregation
    (M : DensityDepCTMC d)
    (x y : Fin d → Fin (M.N + 1)) (hxy : x ≠ y) :
    M.toQMatrix.rate x y =
      ∑ ℓ ∈ M.rateSpec.jumps,
        if (∀ i, (y i : ℤ) - (x i : ℤ) = ℓ i) then
          (M.N : ℝ) * M.rateSpec.rate ℓ (M.scaledState x)
        else 0 := by
  change M.qMatrixRate x y = _
  simp [DensityDepCTMC.qMatrixRate, DensityDepCTMC.offDiagRate,
    hxy, Finset.sum_filter]
  rfl

/-- A zero jump cannot realize a genuinely off-diagonal destination. -/
theorem density_zero_jump_not_offdiag
    (M : DensityDepCTMC d)
    (x y : Fin d → Fin (M.N + 1)) (hxy : x ≠ y) :
    ¬ ∀ i, (y i : ℤ) - (x i : ℤ) = (0 : Fin d → ℤ) i := by
  intro h
  apply hxy
  funext i
  have hi := h i
  have hcast : (y i : ℤ) = (x i : ℤ) := by
    simpa using sub_eq_zero.mp hi
  exact Fin.ext (by exact_mod_cast hcast.symm)

/-- Boundary compatibility kills a listed jump that has no lattice target. -/
theorem density_invalid_jump_rate_zero
    (M : DensityDepCTMC d)
    (hBC : M.BoundaryCompatible)
    (x : Fin d → Fin (M.N + 1)) (hx : M.InSimplex x)
    (ℓ : Fin d → ℤ) (hℓ : ℓ ∈ M.rateSpec.jumps)
    (hinvalid : ¬ ∃ y : Fin d → Fin (M.N + 1),
      ∀ i, (y i : ℤ) - (x i : ℤ) = ℓ i) :
    M.rateSpec.rate ℓ (M.scaledState x) = 0 :=
  hBC x ℓ hℓ hinvalid

/-- Under boundary compatibility, and with the zero/self channel assigned
zero rate, the sum of listed channel rates is exactly the canonical exit
rate. -/
theorem density_exitRate_eq_channel_sum
    (M : DensityDepCTMC d)
    (hBC : M.BoundaryCompatible)
    (x : Fin d → Fin (M.N + 1)) (hx : M.InSimplex x)
    (hzero : M.rateSpec.rate (0 : Fin d → ℤ) (M.scaledState x) = 0) :
    M.exitRateAt x =
      (M.N : ℝ) * ∑ ℓ ∈ M.rateSpec.jumps,
        M.rateSpec.rate ℓ (M.scaledState x) := by
  classical
  let a : (Fin d → ℤ) → ℝ := fun ℓ =>
    (M.N : ℝ) * M.rateSpec.rate ℓ (M.scaledState x)
  rw [← M.sum_offDiagRate_eq_exitRateAt x]
  have hpoint (y : Fin d → Fin (M.N + 1)) :
      M.offDiagRate x y =
        ∑ ℓ ∈ M.rateSpec.jumps,
          if x ≠ y ∧ (∀ i, (y i : ℤ) - (x i : ℤ) = ℓ i)
          then a ℓ else 0 := by
    by_cases hxy : x = y
    · subst y
      simp [DensityDepCTMC.offDiagRate, a]
    · simp [DensityDepCTMC.offDiagRate, hxy, a, Finset.sum_filter]
      rfl
  calc
    (∑ y, M.offDiagRate x y) =
        ∑ y, ∑ ℓ ∈ M.rateSpec.jumps,
          if x ≠ y ∧ (∀ i, (y i : ℤ) - (x i : ℤ) = ℓ i)
          then a ℓ else 0 := by
            apply Finset.sum_congr rfl
            intro y _
            exact hpoint y
    _ = ∑ ℓ ∈ M.rateSpec.jumps,
        ∑ y, if x ≠ y ∧
          (∀ i, (y i : ℤ) - (x i : ℤ) = ℓ i)
          then a ℓ else 0 := by
            rw [Finset.sum_comm]
    _ = ∑ ℓ ∈ M.rateSpec.jumps, a ℓ := by
      apply Finset.sum_congr rfl
      intro ℓ hℓ
      by_cases hℓzero : ℓ = 0
      · subst ℓ
        simp [a, hzero]
      · have hmatch_ne : ∀ y : Fin d → Fin (M.N + 1),
            (∀ i, (y i : ℤ) - (x i : ℤ) = ℓ i) → x ≠ y := by
          intro y hy hxy
          subst y
          apply hℓzero
          funext i
          have hi := hy i
          simp only [Pi.zero_apply]
          linarith
        have hrewrite :
            (∑ y, if x ≠ y ∧
                (∀ i, (y i : ℤ) - (x i : ℤ) = ℓ i)
              then a ℓ else 0) =
              ∑ y ∈ (Finset.univ :
                Finset (Fin d → Fin (M.N + 1))).filter
                  (fun y => ∀ i,
                    (y i : ℤ) - (x i : ℤ) = ℓ i), a ℓ := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro y _
          by_cases hm : ∀ i, (y i : ℤ) - (x i : ℤ) = ℓ i
          · simp [hm, hmatch_ne y hm]
          · simp [hm]
        rw [hrewrite,
          M.sum_matchingStates_const_eq_ite_exists x ℓ (a ℓ)]
        by_cases hex : ∃ y : Fin d → Fin (M.N + 1),
            ∀ i, (y i : ℤ) - (x i : ℤ) = ℓ i
        · simp [hex]
        · have hr0 := hBC x ℓ hℓ hex
          simp [hex, a, hr0]
    _ = (M.N : ℝ) * ∑ ℓ ∈ M.rateSpec.jumps,
        M.rateSpec.rate ℓ (M.scaledState x) := by
      simp [a, Finset.mul_sum]

/-- A measurable source record process with the two finite-cylinder facts
needed by the canonical-law uniqueness theorem. -/
structure IsDensityRecordRealization
    (M : DensityDepCTMC d)
    (x₀ : Fin d → Fin (M.N + 1))
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω)
    (record : Ω → ℕ → ℝ × (Fin d → Fin (M.N + 1))) : Prop where
  measurable_record : Measurable record
  initial :
    (P.map record).map
        (frestrictLe
          (π := fun _ => ℝ × (Fin d → Fin (M.N + 1))) 0) =
      (Measure.dirac (0, x₀)).map
        (MeasurableEquiv.piUnique
          (fun _ : Finset.Iic 0 =>
            ℝ × (Fin d → Fin (M.N + 1)))).symm
  history_next : ∀ n : ℕ,
    (P.map record).map (fun ω =>
        (frestrictLe
          (π := fun _ : ℕ =>
            ℝ × (Fin d → Fin (M.N + 1))) n ω,
          ω (n + 1))) =
      (P.map record).map
          (frestrictLe
            (π := fun _ : ℕ =>
              ℝ × (Fin d → Fin (M.N + 1))) n) ⊗ₘ
        M.toQMatrix.jumpHoldTrajectoryStepKernel n

namespace IsDensityRecordRealization

variable {M : DensityDepCTMC d}
variable {x₀ : Fin d → Fin (M.N + 1)}
variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]
variable {record : Ω → ℕ → ℝ × (Fin d → Fin (M.N + 1))}

/-- Finite record cylinders determine the canonical density-dependent law. -/
theorem map_eq_canonicalRecordMeasure
    (h : IsDensityRecordRealization M x₀ P record) :
    P.map record = M.toQMatrix.canonicalRecordMeasure x₀ := by
  letI : IsProbabilityMeasure (P.map record) :=
    Measure.isProbabilityMeasure_map h.measurable_record.aemeasurable
  exact eq_canonicalRecordMeasure_of_history_next
    M.toQMatrix x₀ (P.map record) h.initial h.history_next

end IsDensityRecordRealization

/-- Direct measure-level form of the preceding reduction. -/
theorem density_record_law_of_history_next
    (M : DensityDepCTMC d)
    (x₀ : Fin d → Fin (M.N + 1))
    (μ : Measure (ℕ → ℝ × (Fin d → Fin (M.N + 1))))
    [IsProbabilityMeasure μ]
    (hinitial :
      μ.map (frestrictLe
          (π := fun _ => ℝ × (Fin d → Fin (M.N + 1))) 0) =
        (Measure.dirac (0, x₀)).map
          (MeasurableEquiv.piUnique
            (fun _ : Finset.Iic 0 =>
              ℝ × (Fin d → Fin (M.N + 1)))).symm)
    (hnext : ∀ n : ℕ,
      μ.map (fun ω =>
          (frestrictLe
            (π := fun _ : ℕ =>
              ℝ × (Fin d → Fin (M.N + 1))) n ω,
            ω (n + 1))) =
        μ.map (frestrictLe
          (π := fun _ : ℕ =>
            ℝ × (Fin d → Fin (M.N + 1))) n) ⊗ₘ
          M.toQMatrix.jumpHoldTrajectoryStepKernel n) :
    μ = M.toQMatrix.canonicalRecordMeasure x₀ :=
  eq_canonicalRecordMeasure_of_history_next
    M.toQMatrix x₀ μ hinitial hnext

end Ripple.Kurtz.StrongApprox

end
