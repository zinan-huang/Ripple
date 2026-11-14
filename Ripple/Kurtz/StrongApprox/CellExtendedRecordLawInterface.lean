-- Ripple/Kurtz/StrongApprox/CellExtendedRecordLawInterface.lean
import Ripple.Kurtz.StrongApprox.CellExtendedRaceRecursion
import Ripple.Kurtz.StrongApprox.CellRecordLawInterface

noncomputable section

namespace Ripple.Kurtz.StrongApprox

open MeasureTheory ProbabilityTheory Preorder
open Ripple.CTMC
open scoped ENNReal NNReal BigOperators
open CellStoppingLineFreshness
open CellExtendedStoppingLine

variable {ι S : Type*} [Fintype ι] [DecidableEq ι]
variable [MeasurableSpace S]

/-- Extended-line replacement for `CellRecordFiltrationRealization`.

The additional `finite` field is essential: an extended stopping line may be
identically `∞`, and strong memorylessness is available only on the full-
measure event on which every coordinate is finite. -/
structure ExtendedCellRecordFiltrationRealization
    (record : CellFamily ι → ℕ → ℝ × S)
    (internal : ℕ → ExtendedCellLine ι) : Prop where
  stopping : ∀ k, ExtendedCellStoppingLine (internal k)
  finite : ∀ k,
    ∀ᵐ c ∂cellFamilyLaw ι,
      c ∈ extendedLineFinite (internal k)
  history : ∀ k,
    Measurable[extendedStoppedPast (internal k) (stopping k)]
      (recordPrefix record k)

namespace ExtendedCellRecordFiltrationRealization

/-- Every finite record coordinate is ambient measurable, hence the complete
record map is measurable. -/
theorem measurable_record
    {record : CellFamily ι → ℕ → ℝ × S}
    {internal : ℕ → ExtendedCellLine ι}
    (h : ExtendedCellRecordFiltrationRealization record internal) :
    Measurable record := by
  apply measurable_pi_lambda
  intro k
  have hhistory : Measurable (recordPrefix record k) :=
    measurable_extendedStoppedPast_ambient (h.history k)
  have heval :=
    (measurable_pi_apply
      (⟨k, Finset.mem_Iic.mpr le_rfl⟩ : Finset.Iic k)).comp hhistory
  simpa only [recordPrefix, frestrictLe_apply] using heval

/-- Strong memorylessness of the one-step stopping-line theorem, uniformly available at every record
index of an extended filtration realization. -/
theorem freshResidualsAt
    {record : CellFamily ι → ℕ → ℝ × S}
    {internal : ℕ → ExtendedCellLine ι}
    (h : ExtendedCellRecordFiltrationRealization record internal)
    (base : ℕ → ℝ × S) (k : ℕ) :
    FreshResidualsAt (cellFamilyLaw ι) record
      (extendedStoppingResidual (internal k)) k :=
  extendedCellStoppingLine_freshResidualsAt
    (h.stopping k) (h.history k) (h.finite k) base

end ExtendedCellRecordFiltrationRealization

variable {d : ℕ}

/-- Extended-line analogue of `CellDensityRecordRealization`.

The density kernel field is unchanged.  Only the filtration witness is
replaced, so the canonical record-law argument remains exactly the one in
`CellRecordLawInterface`. -/
structure ExtendedCellDensityRecordRealization
    (M : DensityDepCTMC d)
    (x0 : Fin d → Fin (M.N + 1))
    (record : CellFamily ι → ℕ →
      ℝ × (Fin d → Fin (M.N + 1)))
    (internal : ℕ → ExtendedCellLine ι) : Prop where
  filtration : ExtendedCellRecordFiltrationRealization record internal
  density : IsDensityRecordRealization M x0 (cellFamilyLaw ι) record

namespace ExtendedCellDensityRecordRealization

/-- Fresh iid residual clocks at every record index. -/
theorem freshResidualsAt
    {M : DensityDepCTMC d}
    {x0 : Fin d → Fin (M.N + 1)}
    {record : CellFamily ι → ℕ →
      ℝ × (Fin d → Fin (M.N + 1))}
    {internal : ℕ → ExtendedCellLine ι}
    (h : ExtendedCellDensityRecordRealization M x0 record internal)
    (base : ℕ → ℝ × (Fin d → Fin (M.N + 1)))
    (k : ℕ) :
    FreshResidualsAt (cellFamilyLaw ι) record
      (extendedStoppingResidual (internal k)) k :=
  h.filtration.freshResidualsAt base k

/-- The existing finite-cylinder uniqueness theorem consumes the unchanged
`density` field; no conversion back to finite-valued stopping lines is needed. -/
theorem record_law
    {M : DensityDepCTMC d}
    {x0 : Fin d → Fin (M.N + 1)}
    {record : CellFamily ι → ℕ →
      ℝ × (Fin d → Fin (M.N + 1))}
    {internal : ℕ → ExtendedCellLine ι}
    (h : ExtendedCellDensityRecordRealization M x0 record internal) :
    (cellFamilyLaw ι).map record =
      M.toQMatrix.canonicalRecordMeasure x0 := by
  letI : IsProbabilityMeasure ((cellFamilyLaw ι).map record) :=
    Measure.isProbabilityMeasure_map
      h.density.measurable_record.aemeasurable
  exact density_record_law_of_history_next
    M x0 ((cellFamilyLaw ι).map record)
      h.density.initial h.density.history_next

/-- Canonical nonnegative-path law obtained from the extended record
realization. -/
theorem readout_law
    {M : DensityDepCTMC d}
    {x0 : Fin d → Fin (M.N + 1)}
    {record : CellFamily ι → ℕ →
      ℝ × (Fin d → Fin (M.N + 1))}
    {internal : ℕ → ExtendedCellLine ι}
    (h : ExtendedCellDensityRecordRealization M x0 record internal) :
    (cellFamilyLaw ι).map
        (AlignedCellCoupling.canonicalDensityNonnegative M ∘ record) =
      (M.toQMatrix.canonicalRecordMeasure x0).map
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
    _ = (M.toQMatrix.canonicalRecordMeasure x0).map
        (AlignedCellCoupling.canonicalDensityNonnegative M) := by
          rw [h.record_law]

/-!
THEOREM LIST
* `ExtendedCellRecordFiltrationRealization.measurable_record`
* `ExtendedCellRecordFiltrationRealization.freshResidualsAt`
* `ExtendedCellDensityRecordRealization.freshResidualsAt`
* `ExtendedCellDensityRecordRealization.record_law`
* `ExtendedCellDensityRecordRealization.readout_law`

CLOSES
* Extended-line replacement for the finite-line filtration field.
* The a.s.-finiteness premise required by the one-step strong memorylessness theorem.
* Direct reuse of `density_record_law_of_history_next` and the canonical
  density readout law without a false finite-line conversion.

UNFINISHED
* Construction of `IsDensityRecordRealization.history_next`; this is the
  Γ/β/v channel-alignment item reserved for the next round.
* Identification of the resulting canonical density readout with the
  universal-cell time-change path.
END
-/

end ExtendedCellDensityRecordRealization

end Ripple.Kurtz.StrongApprox

end
