-- Ripple/Kurtz/StrongApprox/SIPDensityCellRecordFromClockProducer.lean
import Ripple.Kurtz.StrongApprox.CellRecursiveClockEquationProducer
import Ripple.Kurtz.StrongApprox.SIPDensityCellRecordPerScaleAE

/-!
# Per-scale density SIP assembly from the recursive clock producer

The input structure has no coupling and no `SameDriverCertificate` field.
That certificate is derived from the simple-cell record producer at each
scale, and the `SIPDensityCellRecordPerScaleAE` consumer is then reused unchanged.
-/

noncomputable section

namespace Ripple.Kurtz.StrongApprox.SIPDensityCellRecordFromClockProducer

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators
open Ripple.CTMC
open Ripple.Kurtz
open CellPerScaleDensityAlignment
open CellPerScaleRecordPathAE
open CellRecursiveClockEquationProducer
open SIPDensityCellRecordPerScaleAE

variable {Omega : Type*} [MeasurableSpace Omega]
variable {P : Measure Omega} [IsProbabilityMeasure P]
variable {N : ℕ → Omega → ℕ}
variable {d : ℕ} {ι : Type*}
variable [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- A genuinely producer-facing family: alignments plus deterministic
simple-cell record inductions, with no path/coupling field. -/
structure DensityCellRecordProducer
    (Gamma : RateSpec d)
    (beta : ι → (Fin d → ℝ) → ℝ)
    (v : ι → Fin d → ℝ) (b : ι → ℝ)
    (hbetaZero : ∀ l y, 0 ≤ beta l y)
    (hbetaBound : ∀ l y, beta l y ≤ b l)
    (hbetaMeasurable : ∀ l, Measurable (beta l)) : Type _ where
  alignment : ∀ scale : ℕ, ∀ hscale : 0 < scale,
    PerScaleDensityChannelAlignment Gamma beta v scale hscale
  recursiveClock : ∀ scale : ℕ, ∀ hscale : 0 < scale,
    SimpleRecordClockProducer (alignment scale hscale)

namespace DensityCellRecordProducer

variable {Gamma : RateSpec d}
variable {beta : ι → (Fin d → ℝ) → ℝ}
variable {v : ι → Fin d → ℝ} {b : ι → ℝ}
variable {hbetaZero : ∀ l y, 0 ≤ beta l y}
variable {hbetaBound : ∀ l y, beta l y ≤ b l}
variable {hbetaMeasurable : ∀ l, Measurable (beta l)}

/-- Derive the a.e. family of `SIPDensityCellRecordPerScaleAE`; `sameDriver` is constructed, not
assumed. -/
noncomputable def toAEFamily
    (D : DensityCellRecordProducer Gamma beta v b
      hbetaZero hbetaBound hbetaMeasurable) :
    AEDensitySIPCellRecordFamily Gamma beta v b
      hbetaZero hbetaBound hbetaMeasurable where
  alignment := D.alignment
  sameDriver := fun scale hscale =>
    sameDriverCertificate_of_simpleProducer
      (D.alignment scale hscale)
      (D.recursiveClock scale hscale)

/-- Scale-indexed start inherited from the exact lattice alignment. -/
noncomputable def startDensity
    (D : DensityCellRecordProducer Gamma beta v b
      hbetaZero hbetaBound hbetaMeasurable)
    (scale : ℕ) : Fin d → ℝ :=
  D.toAEFamily.startDensity scale

@[simp]
theorem startDensity_eq_scaledState
    (D : DensityCellRecordProducer Gamma beta v b
      hbetaZero hbetaBound hbetaMeasurable)
    {scale : ℕ} (hscale : 0 < scale) :
    D.startDensity scale =
      (DensityDepCTMC.mk scale hscale Gamma).scaledState
        (D.alignment scale hscale).latticeStart := by
  exact D.toAEFamily.startDensity_eq_scaledState hscale

/-- The a.e. same-driver path identity, now derived from the recursive clock
producer. -/
theorem path_eq_ae
    (D : DensityCellRecordProducer Gamma beta v b
      hbetaZero hbetaBound hbetaMeasurable)
    (scale : ℕ) (hscale : 0 < scale) :
    cellTimeChangeNonnegative (β := beta) (v := v) (b := b)
        hscale hbetaZero hbetaBound hbetaMeasurable
          (D.alignment scale hscale).xStart =ᵐ[cellFamilyLaw ι]
      recordReadout (D.alignment scale hscale) :=
  D.toAEFamily.path_eq_ae scale hscale

/-- Law transfer to the canonical density chain, with no coupling premise in
this theorem or in `DensityCellRecordProducer`. -/
theorem path_law
    (D : DensityCellRecordProducer Gamma beta v b
      hbetaZero hbetaBound hbetaMeasurable)
    (hNm : ∀ i, Measurable (N i))
    (hN : iIndepFun N P)
    (hNl : ∀ i k,
      P {omega | N i omega = k} = ENNReal.ofReal (poisTerm k 1))
    (scale : ℕ) (hscale : 0 < scale) :
    (familyMeasure ι P).map
        (fun (omega : ι → PathSpace Omega) (t : ℝ≥0) =>
          namedPoissonTimeChange (N := N)
            beta v b hbetaZero hbetaBound hbetaMeasurable
            (D.startDensity scale) scale omega t) =
      ((DensityDepCTMC.mk scale hscale Gamma).toQMatrix.canonicalRecordMeasure
        (D.alignment scale hscale).latticeStart).map
          (AlignedCellCoupling.canonicalDensityNonnegative
            (DensityDepCTMC.mk scale hscale Gamma)) := by
  simpa only [startDensity, toAEFamily] using
    D.toAEFamily.path_law hNm hN hNl scale hscale

/-- Final unconditional-per-driver, per-scale-start SIP theorem once the
recursive clock producers have been constructed. This is the `SIPDensityCellRecordPerScaleAE`
consumer with the same initial-error term; no coupling hypothesis remains. -/
theorem sip_density_strong_approximation_of_recursive_clock_producers
    (D : DensityCellRecordProducer Gamma beta v b
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
    (∀ scale : ℕ, ∀ hscale : 0 < scale,
      (familyMeasure ι P).map
          (fun (omega : ι → PathSpace Omega) (t : ℝ≥0) =>
            namedPoissonTimeChange (N := N)
              beta v b hbetaZero hbetaBound hbetaMeasurable
              (D.startDensity scale) scale omega t) =
        ((DensityDepCTMC.mk scale hscale Gamma).toQMatrix.canonicalRecordMeasure
          (D.alignment scale hscale).latticeStart).map
            (AlignedCellCoupling.canonicalDensityNonnegative
              (DensityDepCTMC.mk scale hscale Gamma))) ∧
      (∀ᵐ omega ∂familyMeasure ι P,
        ∀ᶠ scale : ℕ in atTop,
          ∀ t ∈ Icc (0 : ℝ) T,
            ‖namedPoissonTimeChange (N := N)
                beta v b hbetaZero hbetaBound hbetaMeasurable
                (D.startDensity scale) scale omega t - x t‖ ≤
              Real.exp (L * T) *
                (‖D.startDensity scale - xZero‖ +
                  SIPDensityPerScaleStart.densityLILError
                    v b T scale)) := by
  simpa only [startDensity, toAEFamily] using
    D.toAEFamily.sip_density_strong_approximation_of_ae_cell_records
      hNm hN hNl hL hF hT hxc hx

/-!
THEOREM LIST
* `DensityCellRecordProducer`
* `DensityCellRecordProducer.toAEFamily`
* `DensityCellRecordProducer.startDensity_eq_scaledState`
* `DensityCellRecordProducer.path_eq_ae`
* `DensityCellRecordProducer.path_law`
* `DensityCellRecordProducer.sip_density_strong_approximation_of_recursive_clock_producers`

CLOSES
* Composition with the a.e. reduction of `SIPDensityCellRecordPerScaleAE`.
* Construction of `SameDriverCertificate` rather than taking it as a field.
* The canonical density-chain law and final per-scale-start strong
  approximation theorem from recursive clock producers.

UNFINISHED
* The family constructor from alignments alone awaits
  `SimpleRecordClockProducer` at each scale.
END
-/

end DensityCellRecordProducer

end Ripple.Kurtz.StrongApprox.SIPDensityCellRecordFromClockProducer

end
