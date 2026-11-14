-- Ripple/Kurtz/StrongApprox/CellPerScaleRecordPathAE.lean
import Ripple.Kurtz.StrongApprox.CellPerScaleRecordRecursion
import Ripple.Kurtz.StrongApprox.PoissonPathArrivals
import Ripple.Kurtz.ExponentialTailPath

noncomputable section

namespace Ripple.Kurtz.StrongApprox.CellPerScaleRecordPathAE

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators
open Ripple.CTMC
open Ripple.Kurtz
open CellPerScaleDensityAlignment
open CellPerScaleRecordRecursion
open CellZeroAwareRecordSequence

variable {d : ℕ} {ι : Type*}
variable [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable [MeasurableSpace ι] [MeasurableSingletonClass ι]
variable {Gamma : RateSpec d}
variable {beta : ι → (Fin d → ℝ) → ℝ}
variable {v : ι → Fin d → ℝ}
variable {n : ℕ} {hn : 0 < n}

private abbrev DensityState (d n : ℕ) :=
  Fin d → Fin (n + 1)

private abbrev DensityModel
    (Gamma : RateSpec d) (n : ℕ) (hn : 0 < n) :=
  DensityDepCTMC.mk n hn Gamma

/-- The concrete record of `CellZeroAwareRecordSequence` at this one scale. -/
noncomputable def recordMap
    (A : PerScaleDensityChannelAlignment Gamma beta v n hn) :
    CellFamily ι → ℕ → ℝ × DensityState d n :=
  recursiveRecord A.latticeStart A.latticeRate A.latticeStep

/-- The concrete extended internal line at this one scale. -/
noncomputable def internalMap
    (A : PerScaleDensityChannelAlignment Gamma beta v n hn) :
    ℕ → CellExtendedStoppingLine.ExtendedCellLine ι :=
  recursiveInternal A.latticeStart A.latticeRate A.latticeStep

/-- Full real-time readout of the recursive record. -/
noncomputable def recordRealPath
    (A : PerScaleDensityChannelAlignment Gamma beta v n hn)
    (c : CellFamily ι) (t : ℝ) : Fin d → ℝ :=
  (DensityModel Gamma n hn).scaledState
    (((DensityModel Gamma n hn).canonicalPathMap
      (recordMap A c)).frozenStateAt t)

/-- Nonnegative-time version used by the SIP interface. -/
noncomputable def recordReadout
    (A : PerScaleDensityChannelAlignment Gamma beta v n hn) :
    CellFamily ι → ℝ≥0 → Fin d → ℝ :=
  AlignedCellCoupling.canonicalDensityNonnegative
      (DensityModel Gamma n hn) ∘ recordMap A

@[simp]
theorem recordReadout_apply
    (A : PerScaleDensityChannelAlignment Gamma beta v n hn)
    (c : CellFamily ι) (t : ℝ≥0) :
    recordReadout A c t = recordRealPath A c (t : ℝ) :=
  rfl

/-- Current main already constructs the correct extended realization from the
per-scale alignment alone. -/
noncomputable def extendedRealization
    (A : PerScaleDensityChannelAlignment Gamma beta v n hn) :
    ExtendedCellDensityRecordRealization
      (DensityModel Gamma n hn) A.latticeStart
      (recordMap A) (internalMap A) := by
  simpa only [recordMap, internalMap] using
    (perScaleRecursion A).toExtendedCellDensityRecordRealization

@[fun_prop]
theorem measurable_recordMap
    (A : PerScaleDensityChannelAlignment Gamma beta v n hn) :
    Measurable (recordMap A) :=
  (extendedRealization A).filtration.measurable_record

@[fun_prop]
theorem measurable_recordReadout
    (A : PerScaleDensityChannelAlignment Gamma beta v n hn) :
    Measurable (recordReadout A) := by
  exact
    (AlignedCellCoupling.canonicalDensityNonnegative_measurable
      (DensityModel Gamma n hn)).comp (measurable_recordMap A)

/-- The canonical frozen readout is measurable in physical time for every
fixed record sample. -/
theorem measurable_recordRealPath_time
    (A : PerScaleDensityChannelAlignment Gamma beta v n hn)
    (c : CellFamily ι) :
    Measurable (recordRealPath A c) := by
  exact
    (Measurable.of_discrete
      (f := (DensityModel Gamma n hn).scaledState)).comp
      ((DensityModel Gamma n hn).measurable_canonicalPathMap_frozenStateAt_section
        (recordMap A c))

/-- The complete recursive record law, with no coupling hypothesis. -/
theorem record_law
    (A : PerScaleDensityChannelAlignment Gamma beta v n hn) :
    (cellFamilyLaw ι).map (recordMap A) =
      (DensityModel Gamma n hn).toQMatrix.canonicalRecordMeasure
        A.latticeStart :=
  (extendedRealization A).record_law

/-- The canonical readout law, also with no coupling hypothesis. -/
theorem readout_law
    (A : PerScaleDensityChannelAlignment Gamma beta v n hn) :
    (cellFamilyLaw ι).map (recordReadout A) =
      ((DensityModel Gamma n hn).toQMatrix.canonicalRecordMeasure
        A.latticeStart).map
          (AlignedCellCoupling.canonicalDensityNonnegative
            (DensityModel Gamma n hn)) := by
  simpa only [recordReadout] using
    (extendedRealization A).readout_law

/-! ## The two local Γ/β/v identities needed by the missing clock induction -/

/-- `beta_eq` identifies the cell speed with the listed Γ rate. -/
theorem latticeRate_coe_eq_gamma
    (A : PerScaleDensityChannelAlignment Gamma beta v n hn)
    (hbetaZero : ∀ l y, 0 ≤ beta l y)
    (x : DensityState d n) (l : ι) :
    ((A.latticeRate x l : ℝ≥0) : ℝ) =
      (n : ℝ) * Gamma.rate (A.jump l)
        ((DensityModel Gamma n hn).scaledState x) := by
  have hnonneg : 0 ≤ A.densityRate x l := by
    unfold PerScaleDensityChannelAlignment.densityRate
    exact mul_nonneg (Nat.cast_nonneg _) (hbetaZero l _)
  change (Real.toNNReal (A.densityRate x l) : ℝ) = _
  rw [Real.coe_toNNReal _ hnonneg]
  unfold PerScaleDensityChannelAlignment.densityRate
  rw [A.beta_eq]
  rfl

/-- `vector_eq` turns one positive lattice step into the advertised scaled
jump `v_l / n`, coordinatewise. -/
theorem scaledState_latticeStep_sub_apply
    (A : PerScaleDensityChannelAlignment Gamma beta v n hn)
    (x : DensityState d n) (l : ι)
    (hpositive : 0 < A.latticeRate x l) (i : Fin d) :
    ((DensityModel Gamma n hn).scaledState (A.latticeStep x l) -
      (DensityModel Gamma n hn).scaledState x) i =
        (n : ℝ)⁻¹ * v l i := by
  have hstep := A.latticeStep_spec_of_positive x l hpositive i
  have hstep' :
      (A.latticeStep x l i : ℤ) - (x i : ℤ) =
        (A.channelEquiv l).1 i := by
    simpa [PerScaleDensityChannelAlignment.jump] using hstep
  have hreal :
      ((A.latticeStep x l i : ℕ) : ℝ) -
          ((x i : ℕ) : ℝ) = v l i := by
    rw [A.vector_eq]
    exact_mod_cast hstep'
  change
    ((A.latticeStep x l i : ℕ) : ℝ) / (n : ℝ) -
        ((x i : ℕ) : ℝ) / (n : ℝ) =
      (n : ℝ)⁻¹ * v l i
  rw [← sub_div, hreal, inv_mul_eq_div]

/-- Function form of the preceding coordinate identity. -/
theorem scaledState_latticeStep_eq
    (A : PerScaleDensityChannelAlignment Gamma beta v n hn)
    (x : DensityState d n) (l : ι)
    (hpositive : 0 < A.latticeRate x l) :
    (DensityModel Gamma n hn).scaledState (A.latticeStep x l) =
      (DensityModel Gamma n hn).scaledState x +
        (n : ℝ)⁻¹ • v l := by
  funext i
  have h := scaledState_latticeStep_sub_apply A x l hpositive i
  simp only [Pi.sub_apply] at h
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linarith

/-! ## Exact missing same-driver certificate and uniqueness reduction -/

/-- The bookkeeping statement that the recursive readout solves the random
Poisson time-change equation driven by the original cell family.

This is deliberately below path equality.  Its producer must prove that the
recursive line is the integrated clock and that each selected arrival is a
unit jump on a probability-one event. -/
structure RecursiveClockEquation
    (A : PerScaleDensityChannelAlignment Gamma beta v n hn)
    (c : CellFamily ι) : Prop where
  initial : recordRealPath A c 0 = A.xStart
  equation : ∀ t : ℝ, 0 ≤ t →
    recordRealPath A c t = A.xStart +
      ∑ l, ((cellPath
        ((n : ℝ) * clock beta (recordRealPath A c) l t) (c l) : ℝ) /
          (n : ℝ)) • v l

/-- The corrected probability-one producer target. -/
def RecursiveClockEquationAE
    (A : PerScaleDensityChannelAlignment Gamma beta v n hn) : Prop :=
  ∀ᵐ c ∂cellFamilyLaw ι, RecursiveClockEquation A c

/-- The canonical repackaging uses exactly the original cell counting path. -/
theorem canonicalDriver_apply
    (c : CellFamily ι) (l : ι) (u : ℝ) :
    poisFamily ι canonicalCount l u (cellFamilySample c) =
      cellPath u (c l) := by
  change poisPath canonicalCount u (cellSample (c l)) = cellPath u (c l)
  exact poisPath_cellSample (c l) u

/-- A recursive clock equation is an `IsPoissonTimeChangeSolution` on every
finite horizon. -/
theorem recursiveClockEquation_isSolution
    {b : ι → ℝ}
    (A : PerScaleDensityChannelAlignment Gamma beta v n hn)
    (hbetaZero : ∀ l y, 0 ≤ beta l y)
    (hbetaBound : ∀ l y, beta l y ≤ b l)
    (hbetaMeasurable : ∀ l, Measurable (beta l))
    {c : CellFamily ι} (H : RecursiveClockEquation A c)
    (T : ℝ) :
    IsPoissonTimeChangeSolution (N := canonicalCount)
      n beta v T A.xStart (cellFamilySample c)
        (recordRealPath A c) := by
  refine
    { measurable_path := measurable_recordRealPath_time A c
      initial_eq := H.initial
      equation := ?_ }
  intro t ht
  rw [H.initial]
  simpa only [canonicalDriver_apply] using H.equation t ht.1

/-- Uniqueness upgrades the clock equation to same-sample path equality. -/
theorem cellTimeChange_eq_recordReadout_of_clockEquation
    {b : ι → ℝ}
    (A : PerScaleDensityChannelAlignment Gamma beta v n hn)
    (hbetaZero : ∀ l y, 0 ≤ beta l y)
    (hbetaBound : ∀ l y, beta l y ≤ b l)
    (hbetaMeasurable : ∀ l, Measurable (beta l))
    {c : CellFamily ι} (H : RecursiveClockEquation A c) :
    cellTimeChangeNonnegative (β := beta) (v := v) (b := b)
        hn hbetaZero hbetaBound hbetaMeasurable A.xStart c =
      recordReadout A c := by
  funext t
  change
    cellTimeChangePath (β := beta) (v := v) (b := b)
        hn hbetaZero hbetaBound hbetaMeasurable A.xStart c (t : ℝ) =
      recordRealPath A c (t : ℝ)
  let horizonIndex := globalHorizonIndex (t : ℝ)
  have hHorizon : 0 ≤ (horizonIndex : ℝ) := Nat.cast_nonneg _
  have htimeChange :
      IsPoissonTimeChangeSolution (N := canonicalCount)
        n beta v (horizonIndex : ℝ) A.xStart (cellFamilySample c)
          (cellTimeChangePath (β := beta) (v := v) (b := b)
            hn hbetaZero hbetaBound hbetaMeasurable A.xStart c) := by
    refine
      { measurable_path := cellTimeChangePath_measurable_time
          (β := beta) (v := v) (b := b)
          hn hbetaZero hbetaBound hbetaMeasurable A.xStart c
        initial_eq := ?_
        equation := ?_ }
    · simpa only [cellTimeChangePath] using
        (globalPoissonPath_initial
          (N := canonicalCount) (v := v)
          hn hbetaZero hbetaBound hbetaMeasurable
          A.xStart (cellFamilySample c))
    · intro s hs
      simpa only [cellTimeChangePath] using
        (globalPoissonPath_equation
          (N := canonicalCount) (v := v)
          hn hbetaZero hbetaBound hbetaMeasurable
          A.xStart (cellFamilySample c) hs.1)
  have hrecord := recursiveClockEquation_isSolution
    A hbetaZero hbetaBound hbetaMeasurable H (horizonIndex : ℝ)
  have hunique := poisson_timeChangeSolution_unique
    (N := canonicalCount) hn hbetaZero hbetaBound hbetaMeasurable
    hHorizon A.xStart (cellFamilySample c) htimeChange hrecord
  exact hunique
    ⟨t.2, (lt_globalHorizonIndex_of_nonneg t.2).le⟩

/-- The actual corrected target: equality for almost every cell family. -/
theorem cellTimeChange_eq_recordReadout_ae_of_clockEquationAE
    {b : ι → ℝ}
    (A : PerScaleDensityChannelAlignment Gamma beta v n hn)
    (hbetaZero : ∀ l y, 0 ≤ beta l y)
    (hbetaBound : ∀ l y, beta l y ≤ b l)
    (hbetaMeasurable : ∀ l, Measurable (beta l))
    (H : RecursiveClockEquationAE A) :
    cellTimeChangeNonnegative (β := beta) (v := v) (b := b)
        hn hbetaZero hbetaBound hbetaMeasurable A.xStart =ᵐ[cellFamilyLaw ι]
      recordReadout A := by
  filter_upwards [H] with c hc
  exact cellTimeChange_eq_recordReadout_of_clockEquation
    A hbetaZero hbetaBound hbetaMeasurable hc

/-- Corrected one-scale package.  Unlike the old pointwise field, this carries
only a probability-one same-driver certificate. -/
structure SameDriverCertificate
    (A : PerScaleDensityChannelAlignment Gamma beta v n hn) : Prop where
  clockEquationAE : RecursiveClockEquationAE A

namespace SameDriverCertificate

variable {b : ι → ℝ}
variable {hbetaZero : ∀ l y, 0 ≤ beta l y}
variable {hbetaBound : ∀ l y, beta l y ≤ b l}
variable {hbetaMeasurable : ∀ l, Measurable (beta l)}

/-- Derived a.e. path equality at the one scale. -/
theorem path_eq_ae
    {A : PerScaleDensityChannelAlignment Gamma beta v n hn}
    (H : SameDriverCertificate A) :
    cellTimeChangeNonnegative (β := beta) (v := v) (b := b)
        hn hbetaZero hbetaBound hbetaMeasurable A.xStart =ᵐ[cellFamilyLaw ι]
      recordReadout A :=
  cellTimeChange_eq_recordReadout_ae_of_clockEquationAE
    A hbetaZero hbetaBound hbetaMeasurable H.clockEquationAE

/-- A.e. equality to the measurable record readout supplies the exact
measurability strength needed by `Measure.map`. -/
theorem cell_path_aemeasurable
    {A : PerScaleDensityChannelAlignment Gamma beta v n hn}
    (H : SameDriverCertificate A) :
    AEMeasurable
      (cellTimeChangeNonnegative (β := beta) (v := v) (b := b)
        hn hbetaZero hbetaBound hbetaMeasurable A.xStart)
      (cellFamilyLaw ι) :=
  (measurable_recordReadout A).aemeasurable.congr (H.path_eq_ae).symm

/-- The old `cell_path_law` consumer needs only a.e. equality, not pointwise
equality. -/
theorem cell_path_law
    {A : PerScaleDensityChannelAlignment Gamma beta v n hn}
    (H : SameDriverCertificate A) :
    (cellFamilyLaw ι).map
        (cellTimeChangeNonnegative (β := beta) (v := v) (b := b)
          hn hbetaZero hbetaBound hbetaMeasurable A.xStart) =
      ((DensityModel Gamma n hn).toQMatrix.canonicalRecordMeasure
        A.latticeStart).map
          (AlignedCellCoupling.canonicalDensityNonnegative
            (DensityModel Gamma n hn)) := by
  calc
    (cellFamilyLaw ι).map
        (cellTimeChangeNonnegative (β := beta) (v := v) (b := b)
          hn hbetaZero hbetaBound hbetaMeasurable A.xStart) =
      (cellFamilyLaw ι).map (recordReadout A) :=
        Measure.map_congr H.path_eq_ae
    _ = _ := readout_law A

end SameDriverCertificate

/-!
THEOREM LIST
* `extendedRealization`
* `record_law`
* `readout_law`
* `latticeRate_coe_eq_gamma`
* `scaledState_latticeStep_sub_apply`
* `scaledState_latticeStep_eq`
* `RecursiveClockEquation`
* `recursiveClockEquation_isSolution`
* `cellTimeChange_eq_recordReadout_of_clockEquation`
* `cellTimeChange_eq_recordReadout_ae_of_clockEquationAE`
* `SameDriverCertificate.path_eq_ae`
* `SameDriverCertificate.cell_path_aemeasurable`
* `SameDriverCertificate.cell_path_law`

CLOSES
* The exact one-scale extended density-record realization from the concrete
  zero-aware recursion.
* The uses of `beta_eq` and `vector_eq` in the local rate/jump identities.
* Reduction of the missing recursive-clock equation to same-driver path
  equality by `poisson_timeChangeSolution_unique`.
* Replacement of the false pointwise field by an a.e. field.
* The canonical cell-path law from that a.e. field.

EXPLICIT INPUT
* `SameDriverCertificate.clockEquationAE`.

UNFINISHED
* The producer `RecursiveClockEquationAE A` from `A` alone.  It requires a
  probability-one unit-jump lemma for the cell process and an induction
  identifying `recursiveInternal` with the integrated clocks of
  `recordRealPath`.  Current main proves neither statement; they are omitted
  rather than postulated as theorems.
END
-/

end Ripple.Kurtz.StrongApprox.CellPerScaleRecordPathAE

end
