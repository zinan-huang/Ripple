-- Ripple/Kurtz/StrongApprox/CellRecordLawInterface.lean
import Ripple.Kurtz.StrongApprox.CellStoppingLineAdapters
import Ripple.Kurtz.StrongApprox.DensityDependentRecordLaw
import Ripple.Kurtz.StrongApprox.PoissonCellTimeChangeFactor

noncomputable section

namespace Ripple.Kurtz.StrongApprox

open MeasureTheory ProbabilityTheory
open Ripple.CTMC
open CellStoppingLineFreshness
open CellStoppingLineResiduals
open CellStoppingLineAdapters
open scoped ENNReal NNReal

variable {ι S : Type*} [Fintype ι] [DecidableEq ι]
variable [MeasurableSpace S]

/-- The exact filtration obligations needed to apply the `CellExtendedStoppingLine` adapter at
all record indices.  This structure does not pretend that the obligations are
constructible for the current raw finite-valued stopping-line definition. -/
structure CellRecordFiltrationRealization
    (record : CellFamily ι → ℕ → ℝ × S)
    (internal : ℕ → CellFamily ι → ι → ℝ≥0) : Prop where
  stopping : ∀ k, CellStoppingLine (internal k)
  history : ∀ k,
    Measurable[cellStoppedPast (internal k) (stopping k)]
      (recordPrefix record k)

namespace CellRecordFiltrationRealization

/-- Once the stopping-line and stopped-history obligations are available,
`CellExtendedStoppingLine` supplies fresh iid residual clocks at every record index. -/
theorem freshResidualsAt
    {record : CellFamily ι → ℕ → ℝ × S}
    {internal : ℕ → CellFamily ι → ι → ℝ≥0}
    (h : CellRecordFiltrationRealization record internal)
    (k : ℕ) :
    FreshResidualsAt (cellFamilyLaw ι) record
      (stoppingResidual (internal k)) k :=
  cellStoppingLine_freshResidualsAt_final
    (h.stopping k) (h.history k)

end CellRecordFiltrationRealization

variable {d : ℕ}

/-- A direct cell-space density record realization.  The `filtration` field is
what a repaired stopping-line recursion must construct; the `density` field is
the finite-cylinder kernel statement consumed by
`density_record_law_of_history_next`. -/
structure CellDensityRecordRealization
    (M : DensityDepCTMC d)
    (x₀ : Fin d → Fin (M.N + 1))
    (record : CellFamily ι → ℕ →
      ℝ × (Fin d → Fin (M.N + 1)))
    (internal : ℕ → CellFamily ι → ι → ℝ≥0) : Prop where
  filtration : CellRecordFiltrationRealization record internal
  density : IsDensityRecordRealization M x₀ (cellFamilyLaw ι) record

namespace CellDensityRecordRealization

/-- Fresh residual clocks for the direct density record realization. -/
theorem freshResidualsAt
    {M : DensityDepCTMC d}
    {x₀ : Fin d → Fin (M.N + 1)}
    {record : CellFamily ι → ℕ →
      ℝ × (Fin d → Fin (M.N + 1))}
    {internal : ℕ → CellFamily ι → ι → ℝ≥0}
    (h : CellDensityRecordRealization M x₀ record internal)
    (k : ℕ) :
    FreshResidualsAt (cellFamilyLaw ι) record
      (stoppingResidual (internal k)) k :=
  h.filtration.freshResidualsAt k

/-- The requested use of
`DensityDependentRecordLaw.density_record_law_of_history_next`: finite record
cylinders identify the complete canonical record law. -/
theorem record_law
    {M : DensityDepCTMC d}
    {x₀ : Fin d → Fin (M.N + 1)}
    {record : CellFamily ι → ℕ →
      ℝ × (Fin d → Fin (M.N + 1))}
    {internal : ℕ → CellFamily ι → ι → ℝ≥0}
    (h : CellDensityRecordRealization M x₀ record internal) :
    (cellFamilyLaw ι).map record =
      M.toQMatrix.canonicalRecordMeasure x₀ := by
  letI : IsProbabilityMeasure ((cellFamilyLaw ι).map record) :=
    Measure.isProbabilityMeasure_map
      h.density.measurable_record.aemeasurable
  exact density_record_law_of_history_next
    M x₀ ((cellFamilyLaw ι).map record)
      h.density.initial h.density.history_next

/-- Mapping the direct record realization through the canonical density
readout gives the canonical nonnegative path law. -/
theorem readout_law
    {M : DensityDepCTMC d}
    {x₀ : Fin d → Fin (M.N + 1)}
    {record : CellFamily ι → ℕ →
      ℝ × (Fin d → Fin (M.N + 1))}
    {internal : ℕ → CellFamily ι → ι → ℝ≥0}
    (h : CellDensityRecordRealization M x₀ record internal) :
    (cellFamilyLaw ι).map
        (AlignedCellCoupling.canonicalDensityNonnegative M ∘ record) =
      (M.toQMatrix.canonicalRecordMeasure x₀).map
        (AlignedCellCoupling.canonicalDensityNonnegative M) := by
  have hread : Measurable
      (AlignedCellCoupling.canonicalDensityNonnegative M) :=
    AlignedCellCoupling.canonicalDensityNonnegative_measurable M
  calc
    (cellFamilyLaw ι).map
        (AlignedCellCoupling.canonicalDensityNonnegative M ∘ record) =
      ((cellFamilyLaw ι).map record).map
        (AlignedCellCoupling.canonicalDensityNonnegative M) :=
          (Measure.map_map hread
            h.density.measurable_record).symm
    _ = (M.toQMatrix.canonicalRecordMeasure x₀).map
        (AlignedCellCoupling.canonicalDensityNonnegative M) := by
          rw [h.record_law]

end CellDensityRecordRealization

/-!
THEOREM LIST
* `CellRecordFiltrationRealization.freshResidualsAt`
* `CellDensityRecordRealization.freshResidualsAt`
* `CellDensityRecordRealization.record_law`
* `CellDensityRecordRealization.readout_law`

CLOSES
* The `FreshResidualsAt` consequence once `hStopping` and `hHistory`
  are supplied.
* The complete-record-law consequence of `density_record_law_of_history_next`.
* The canonical density readout law of a direct cell record realization.

UNFINISHED
* Construction of `CellRecordFiltrationRealization` from the current raw
  `residualWait`; the counterexample above shows that construction is false.
-/

end Ripple.Kurtz.StrongApprox

end
