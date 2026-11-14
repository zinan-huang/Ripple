-- Ripple/Kurtz/StrongApprox/SIPDensityCellRecordPerScaleAE.lean
import Ripple.Kurtz.StrongApprox.CellPerScaleRecordPathAE
import Ripple.Kurtz.StrongApprox.SIPDensityPerScaleStart

noncomputable section

namespace Ripple.Kurtz.StrongApprox.SIPDensityCellRecordPerScaleAE

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators
open Ripple.CTMC
open Ripple.Kurtz
open CellPerScaleDensityAlignment
open CellPerScaleRecordPathAE

variable {Omega : Type*} [MeasurableSpace Omega]
variable {P : Measure Omega} [IsProbabilityMeasure P]
variable {N : ℕ → Omega → ℕ}
variable {d : ℕ} {ι : Type*}
variable [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- Per-scale, a.e.-correct replacement for
`DensitySIPCellRecordFamily`.  The record and extended filtration are now
canonical functions of `alignment`; only the same-driver clock equation is a
field. -/
structure AEDensitySIPCellRecordFamily
    (Gamma : RateSpec d)
    (beta : ι → (Fin d → ℝ) → ℝ)
    (v : ι → Fin d → ℝ) (b : ι → ℝ)
    (hbetaZero : ∀ l y, 0 ≤ beta l y)
    (hbetaBound : ∀ l y, beta l y ≤ b l)
    (hbetaMeasurable : ∀ l, Measurable (beta l)) : Type _ where
  alignment : ∀ n : ℕ, ∀ hn : 0 < n,
    PerScaleDensityChannelAlignment Gamma beta v n hn
  sameDriver : ∀ n : ℕ, ∀ hn : 0 < n,
    SameDriverCertificate (alignment n hn)

namespace AEDensitySIPCellRecordFamily

variable {Gamma : RateSpec d}
variable {beta : ι → (Fin d → ℝ) → ℝ}
variable {v : ι → Fin d → ℝ} {b : ι → ℝ}
variable {hbetaZero : ∀ l y, 0 ≤ beta l y}
variable {hbetaBound : ∀ l y, beta l y ≤ b l}
variable {hbetaMeasurable : ∀ l, Measurable (beta l)}

/-- Total scale-indexed start; scale zero is irrelevant to eventual results. -/
noncomputable def startDensity
    (D : AEDensitySIPCellRecordFamily Gamma beta v b
      hbetaZero hbetaBound hbetaMeasurable)
    (n : ℕ) : Fin d → ℝ :=
  if hn : 0 < n then (D.alignment n hn).xStart else 0

@[simp]
theorem startDensity_eq
    (D : AEDensitySIPCellRecordFamily Gamma beta v b
      hbetaZero hbetaBound hbetaMeasurable)
    {n : ℕ} (hn : 0 < n) :
    D.startDensity n = (D.alignment n hn).xStart := by
  simp [startDensity, hn]

/-- The family starts each positive scale at its exact scaled lattice state. -/
theorem startDensity_eq_scaledState
    (D : AEDensitySIPCellRecordFamily Gamma beta v b
      hbetaZero hbetaBound hbetaMeasurable)
    {n : ℕ} (hn : 0 < n) :
    D.startDensity n =
      (DensityDepCTMC.mk n hn Gamma).scaledState
        (D.alignment n hn).latticeStart := by
  rw [D.startDensity_eq hn]
  exact (D.alignment n hn).initial_alignment.symm

/-- The extended realization requested at one scale. -/
noncomputable def realization
    (D : AEDensitySIPCellRecordFamily Gamma beta v b
      hbetaZero hbetaBound hbetaMeasurable)
    (n : ℕ) (hn : 0 < n) :
    ExtendedCellDensityRecordRealization
      (DensityDepCTMC.mk n hn Gamma)
      (D.alignment n hn).latticeStart
      (recordMap (D.alignment n hn))
      (internalMap (D.alignment n hn)) :=
  extendedRealization (D.alignment n hn)

/-- Complete recursive-record law at one scale. -/
theorem record_law
    (D : AEDensitySIPCellRecordFamily Gamma beta v b
      hbetaZero hbetaBound hbetaMeasurable)
    (n : ℕ) (hn : 0 < n) :
    (cellFamilyLaw ι).map (recordMap (D.alignment n hn)) =
      (DensityDepCTMC.mk n hn Gamma).toQMatrix.canonicalRecordMeasure
        (D.alignment n hn).latticeStart :=
  CellPerScaleRecordPathAE.record_law (D.alignment n hn)

/-- Corrected a.e. path-identification field, derived from the clock equation. -/
theorem path_eq_ae
    (D : AEDensitySIPCellRecordFamily Gamma beta v b
      hbetaZero hbetaBound hbetaMeasurable)
    (n : ℕ) (hn : 0 < n) :
    cellTimeChangeNonnegative (β := beta) (v := v) (b := b)
        hn hbetaZero hbetaBound hbetaMeasurable
          (D.alignment n hn).xStart =ᵐ[cellFamilyLaw ι]
      recordReadout (D.alignment n hn) :=
  (D.sameDriver n hn).path_eq_ae

/-- Sample a.e.-measurability is enough for `Measure.map`. -/
theorem cell_path_aemeasurable
    (D : AEDensitySIPCellRecordFamily Gamma beta v b
      hbetaZero hbetaBound hbetaMeasurable)
    (n : ℕ) (hn : 0 < n) :
    AEMeasurable
      (cellTimeChangeNonnegative (β := beta) (v := v) (b := b)
        hn hbetaZero hbetaBound hbetaMeasurable
          (D.alignment n hn).xStart)
      (cellFamilyLaw ι) :=
  (D.sameDriver n hn).cell_path_aemeasurable

/-- `cell_path_law` survives unchanged after replacing pointwise equality by
a.e. equality. -/
theorem cell_path_law
    (D : AEDensitySIPCellRecordFamily Gamma beta v b
      hbetaZero hbetaBound hbetaMeasurable)
    (n : ℕ) (hn : 0 < n) :
    (cellFamilyLaw ι).map
        (cellTimeChangeNonnegative (β := beta) (v := v) (b := b)
          hn hbetaZero hbetaBound hbetaMeasurable
            (D.alignment n hn).xStart) =
      ((DensityDepCTMC.mk n hn Gamma).toQMatrix.canonicalRecordMeasure
        (D.alignment n hn).latticeStart).map
          (AlignedCellCoupling.canonicalDensityNonnegative
            (DensityDepCTMC.mk n hn Gamma)) :=
  (D.sameDriver n hn).cell_path_law

/-- Law transfer from the universal cells to the original SIP driver family.
The only change from the old proof is using `AEMeasurable` in `Measure.map_map`. -/
theorem path_law
    (D : AEDensitySIPCellRecordFamily Gamma beta v b
      hbetaZero hbetaBound hbetaMeasurable)
    (hNm : ∀ i, Measurable (N i))
    (hN : iIndepFun N P)
    (hNl : ∀ i k,
      P {omega | N i omega = k} = ENNReal.ofReal (poisTerm k 1))
    (n : ℕ) (hn : 0 < n) :
    (familyMeasure ι P).map
        (fun (omega : ι → PathSpace Omega) (t : ℝ≥0) =>
          namedPoissonTimeChange (N := N)
            beta v b hbetaZero hbetaBound hbetaMeasurable
            (D.startDensity n) n omega t) =
      ((DensityDepCTMC.mk n hn Gamma).toQMatrix.canonicalRecordMeasure
        (D.alignment n hn).latticeStart).map
          (AlignedCellCoupling.canonicalDensityNonnegative
            (DensityDepCTMC.mk n hn Gamma)) := by
  rw [D.startDensity_eq hn]
  have hnamed :
      (fun (omega : ι → PathSpace Omega) (t : ℝ≥0) =>
        namedPoissonTimeChange (N := N)
          beta v b hbetaZero hbetaBound hbetaMeasurable
          (D.alignment n hn).xStart n omega t) =
      globalNonnegativePath (N := N)
        (β := beta) (v := v) (b := b)
        hn hbetaZero hbetaBound hbetaMeasurable
          (D.alignment n hn).xStart := by
    funext omega t
    rw [namedPoissonTimeChange_eq_global
      (N := N) (v := v) hbetaZero hbetaBound
      hbetaMeasurable (D.alignment n hn).xStart hn]
    rfl
  rw [hnamed]
  have hfactor :
      globalNonnegativePath (N := N)
          (β := beta) (v := v) (b := b)
          hn hbetaZero hbetaBound hbetaMeasurable
            (D.alignment n hn).xStart =
        cellTimeChangeNonnegative
          (β := beta) (v := v) (b := b)
          hn hbetaZero hbetaBound hbetaMeasurable
            (D.alignment n hn).xStart ∘
          familyCellSequence ι N := by
    funext omega
    exact globalNonnegativePath_eq_cellFactor
      (N := N) (β := beta) (v := v) (b := b)
      hn hbetaZero hbetaBound hbetaMeasurable
      (D.alignment n hn).xStart omega
  rw [hfactor]
  have hcellsMeas : Measurable (familyCellSequence ι N) :=
    measurable_familyCellSequence ι hNm
  have hcellsLaw :
      (familyMeasure ι P).map (familyCellSequence ι N) =
        cellFamilyLaw ι :=
    familyCellSequence_law ι hNm hN hNl
  have houter :
      AEMeasurable
        (cellTimeChangeNonnegative
          (β := beta) (v := v) (b := b)
          hn hbetaZero hbetaBound hbetaMeasurable
            (D.alignment n hn).xStart)
        ((familyMeasure ι P).map (familyCellSequence ι N)) := by
    rw [hcellsLaw]
    exact D.cell_path_aemeasurable n hn
  calc
    (familyMeasure ι P).map
        (cellTimeChangeNonnegative
          (β := beta) (v := v) (b := b)
          hn hbetaZero hbetaBound hbetaMeasurable
            (D.alignment n hn).xStart ∘
          familyCellSequence ι N) =
      ((familyMeasure ι P).map (familyCellSequence ι N)).map
        (cellTimeChangeNonnegative
          (β := beta) (v := v) (b := b)
          hn hbetaZero hbetaBound hbetaMeasurable
            (D.alignment n hn).xStart) :=
        (AEMeasurable.map_map_of_aemeasurable houter hcellsMeas.aemeasurable).symm
    _ = (cellFamilyLaw ι).map
        (cellTimeChangeNonnegative
          (β := beta) (v := v) (b := b)
          hn hbetaZero hbetaBound hbetaMeasurable
            (D.alignment n hn).xStart) := by rw [hcellsLaw]
    _ = _ := D.cell_path_law n hn

/-- Corrected cell-record strong approximation.  The law half uses the a.e.
path field; the rate half is the already-proved per-scale-start Gronwall bound. -/
theorem sip_density_strong_approximation_of_ae_cell_records
    (D : AEDensitySIPCellRecordFamily Gamma beta v b
      hbetaZero hbetaBound hbetaMeasurable)
    (hNm : ∀ i, Measurable (N i))
    (hN : iIndepFun N P)
    (hNl : ∀ i k,
      P {omega | N i omega = k} = ENNReal.ofReal (poisTerm k 1))
    {L : ℝ} (hL : 0 ≤ L)
    (hF : ∀ y z,
      ‖tcDrift beta v y - tcDrift beta v z‖ ≤ L * ‖y - z‖)
    {T : ℝ} (hT : 0 ≤ T)
    {x : ℝ → Fin d → ℝ} {xZero : Fin d → ℝ}
    (hxc : ContinuousOn x (Icc 0 T))
    (hx : ∀ t ∈ Icc (0 : ℝ) T,
      x t = xZero +
        ∫ s in (0 : ℝ)..t, tcDrift beta v (x s)) :
    (∀ n : ℕ, ∀ hn : 0 < n,
      (familyMeasure ι P).map
          (fun (omega : ι → PathSpace Omega) (t : ℝ≥0) =>
            namedPoissonTimeChange (N := N)
              beta v b hbetaZero hbetaBound hbetaMeasurable
              (D.startDensity n) n omega t) =
        ((DensityDepCTMC.mk n hn Gamma).toQMatrix.canonicalRecordMeasure
          (D.alignment n hn).latticeStart).map
            (AlignedCellCoupling.canonicalDensityNonnegative
              (DensityDepCTMC.mk n hn Gamma))) ∧
      (∀ᵐ omega ∂familyMeasure ι P,
        ∀ᶠ n : ℕ in atTop,
          ∀ t ∈ Icc (0 : ℝ) T,
            ‖namedPoissonTimeChange (N := N)
                beta v b hbetaZero hbetaBound hbetaMeasurable
                (D.startDensity n) n omega t - x t‖ ≤
              Real.exp (L * T) *
                (‖D.startDensity n - xZero‖ +
                  SIPDensityPerScaleStart.densityLILError v b T n)) := by
  constructor
  · intro scale hscale
    exact D.path_law hNm hN hNl scale hscale
  · exact
      SIPDensityPerScaleStart.ae_perScaleStart_density_strong_approximation
        (N := N) hNm hN hNl
        hbetaZero hbetaBound hbetaMeasurable
        hL hF hT hxc hx D.startDensity

end AEDensitySIPCellRecordFamily

/-!
THEOREM LIST
* `AEDensitySIPCellRecordFamily`
* `AEDensitySIPCellRecordFamily.startDensity_eq_scaledState`
* `AEDensitySIPCellRecordFamily.realization`
* `AEDensitySIPCellRecordFamily.record_law`
* `AEDensitySIPCellRecordFamily.path_eq_ae`
* `AEDensitySIPCellRecordFamily.cell_path_aemeasurable`
* `AEDensitySIPCellRecordFamily.cell_path_law`
* `AEDensitySIPCellRecordFamily.path_law`
* `AEDensitySIPCellRecordFamily.sip_density_strong_approximation_of_ae_cell_records`

CLOSES
* The per-scale, a.e.-correct replacement of
  `DensitySIPCellRecordFamily.path_eq`.
* Assembly of the concrete extended record realization at every scale.
* `cell_path_law` using `Measure.map_congr`.
* SIP law transfer using `Measure.map_map` with `AEMeasurable`.
* The strong-approximation consumer with the initial-error term.

EXPLICIT INPUT
* `sameDriver n hn : SameDriverCertificate (alignment n hn)`.

UNFINISHED
* Construction of `sameDriver` from an alignment alone.  This is exactly the
  omitted probability-one simplicity plus integrated-clock induction listed
  in `CellPerScaleRecordPathAE`; no other downstream field remains open.
END
-/

end Ripple.Kurtz.StrongApprox.SIPDensityCellRecordPerScaleAE

end
