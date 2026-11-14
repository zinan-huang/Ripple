-- Ripple/Kurtz/StrongApprox/SIPDensityPerScaleStart.lean
import Ripple.Kurtz.StrongApprox.CellPerScaleDensityAlignment
import Ripple.Kurtz.StrongApprox.SIPDensityStrongApprox

noncomputable section

namespace Ripple.Kurtz.StrongApprox.SIPDensityPerScaleStart

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators
open Ripple.CTMC
open Ripple.Kurtz
open CellPerScaleDensityAlignment

variable {Omega : Type*} [MeasurableSpace Omega]
variable {P : Measure Omega} [IsProbabilityMeasure P]
variable {N : ℕ → Omega → ℕ}
variable {d : ℕ} {ι : Type*}
variable [Fintype ι] [DecidableEq ι]

/-- The exact LIL error term already used by
`sip_density_strong_approximation`. -/
noncomputable def densityLILError
    (v : ι → Fin d → ℝ) (b : ι → ℝ)
    (T : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ)⁻¹ *
    ∑ l, ‖v l‖ * envelope ((n : ℝ) * (b l * T))

theorem densityLILError_nonneg
    (v : ι → Fin d → ℝ) (b : ι → ℝ)
    (T : ℝ) (n : ℕ) :
    0 ≤ densityLILError v b T n := by
  unfold densityLILError
  apply mul_nonneg
  · exact inv_nonneg.mpr (Nat.cast_nonneg n)
  · apply Finset.sum_nonneg
    intro l _hl
    apply mul_nonneg (norm_nonneg _)
    unfold envelope
    positivity

section FamilySection

variable [Nonempty ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- A family with an independently aligned start at every positive scale.
There is no fixed density in this structure. -/
structure PerScaleStartSIPFamily
    (Gamma : RateSpec d)
    (beta : ι → (Fin d → ℝ) → ℝ)
    (v : ι → Fin d → ℝ) (b : ι → ℝ)
    (hbetaZero : ∀ l y, 0 ≤ beta l y)
    (hbetaBound : ∀ l y, beta l y ≤ b l)
    (hbetaMeasurable : ∀ l, Measurable (beta l)) : Type _ where
  alignment : ∀ n : ℕ, ∀ hn : 0 < n,
    PerScaleDensityChannelAlignment Gamma beta v n hn
  system : ∀ n : ℕ, ∀ hn : 0 < n,
    CellPerScaleDensityAlignment.PerScaleDensityCellSystem
      (b := b) (hbetaZero := hbetaZero)
      (hbetaBound := hbetaBound)
      (hbetaMeasurable := hbetaMeasurable)
      (alignment n hn)

namespace PerScaleStartSIPFamily

variable {Gamma : RateSpec d}
variable {beta : ι → (Fin d → ℝ) → ℝ}
variable {v : ι → Fin d → ℝ} {b : ι → ℝ}
variable {hbetaZero : ∀ l y, 0 ≤ beta l y}
variable {hbetaBound : ∀ l y, beta l y ≤ b l}
variable {hbetaMeasurable : ∀ l, Measurable (beta l)}

/-- Total scale-indexed start.  Scale zero is irrelevant to every eventual
statement and is assigned zero. -/
noncomputable def startDensity
    (D : PerScaleStartSIPFamily Gamma beta v b
      hbetaZero hbetaBound hbetaMeasurable)
    (n : ℕ) : Fin d → ℝ :=
  if hn : 0 < n then (D.alignment n hn).xStart else 0

@[simp]
theorem startDensity_eq
    (D : PerScaleStartSIPFamily Gamma beta v b
      hbetaZero hbetaBound hbetaMeasurable)
    {n : ℕ} (hn : 0 < n) :
    D.startDensity n = (D.alignment n hn).xStart := by
  simp [startDensity, hn]

/-- At every positive scale, the actual start is exactly the scaled lattice
start. -/
theorem startDensity_eq_scaledState
    (D : PerScaleStartSIPFamily Gamma beta v b
      hbetaZero hbetaBound hbetaMeasurable)
    {n : ℕ} (hn : 0 < n) :
    D.startDensity n =
      (DensityDepCTMC.mk n hn Gamma).scaledState
        (D.alignment n hn).latticeStart := by
  rw [D.startDensity_eq hn]
  exact (D.alignment n hn).initial_alignment.symm

/-- Per-scale canonical record law. -/
theorem record_law
    (D : PerScaleStartSIPFamily Gamma beta v b
      hbetaZero hbetaBound hbetaMeasurable)
    (n : ℕ) (hn : 0 < n) :
    (cellFamilyLaw ι).map
        (CellZeroAwareRecordSequence.recursiveRecord
          (D.alignment n hn).latticeStart
          (D.alignment n hn).latticeRate
          (D.alignment n hn).latticeStep) =
      (DensityDepCTMC.mk n hn Gamma).toQMatrix.canonicalRecordMeasure
        (D.alignment n hn).latticeStart :=
  (D.system n hn).record_law (D.alignment n hn)

/-- Per-scale canonical readout law. -/
theorem readout_law
    (D : PerScaleStartSIPFamily Gamma beta v b
      hbetaZero hbetaBound hbetaMeasurable)
    (n : ℕ) (hn : 0 < n) :
    (cellFamilyLaw ι).map
        (AlignedCellCoupling.canonicalDensityNonnegative
          (DensityDepCTMC.mk n hn Gamma) ∘
          CellZeroAwareRecordSequence.recursiveRecord
            (D.alignment n hn).latticeStart
            (D.alignment n hn).latticeRate
            (D.alignment n hn).latticeStep) =
      ((DensityDepCTMC.mk n hn Gamma).toQMatrix.canonicalRecordMeasure
        (D.alignment n hn).latticeStart).map
          (AlignedCellCoupling.canonicalDensityNonnegative
            (DensityDepCTMC.mk n hn Gamma)) :=
  (D.system n hn).readout_law (D.alignment n hn)

/-- Every positive-scale SIP path has the canonical CTMC law with its own
lattice start. -/
theorem path_law
    (D : PerScaleStartSIPFamily Gamma beta v b
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
  have hstart := D.startDensity_eq hn
  rw [hstart]
  have hfun :
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
  rw [hfun]
  exact (D.system n hn).poisson_path_law
    (D.alignment n hn) hNm hN hNl

end PerScaleStartSIPFamily

end FamilySection

/-- Gronwall with a varying start.  This is a direct specialization of
`ae_chain_fluid_rate`, whose initial-error term was already present. -/
theorem ae_perScaleStart_density_strong_approximation
    (hNm : ∀ i, Measurable (N i))
    (hN : iIndepFun N P)
    (hNl : ∀ i k,
      P {omega | N i omega = k} = ENNReal.ofReal (poisTerm k 1))
    {beta : ι → (Fin d → ℝ) → ℝ}
    {v : ι → Fin d → ℝ} {b : ι → ℝ}
    (hbetaZero : ∀ l y, 0 ≤ beta l y)
    (hbetaBound : ∀ l y, beta l y ≤ b l)
    (hbetaMeasurable : ∀ l, Measurable (beta l))
    {L : ℝ} (hL : 0 ≤ L)
    (hF : ∀ y z,
      ‖tcDrift beta v y - tcDrift beta v z‖ ≤ L * ‖y - z‖)
    {T : ℝ} (hT : 0 ≤ T)
    {x : ℝ → Fin d → ℝ} {xZero : Fin d → ℝ}
    (hxc : ContinuousOn x (Icc 0 T))
    (hx : ∀ t ∈ Icc (0 : ℝ) T,
      x t = xZero +
        ∫ s in (0 : ℝ)..t, tcDrift beta v (x s))
    (xStart : ℕ → Fin d → ℝ) :
    ∀ᵐ omega ∂familyMeasure ι P,
      ∀ᶠ n : ℕ in atTop,
        ∀ t ∈ Icc (0 : ℝ) T,
          ‖namedPoissonTimeChange (N := N)
              beta v b hbetaZero hbetaBound hbetaMeasurable
              (xStart n) n omega t - x t‖ ≤
            Real.exp (L * T) *
              (‖xStart n - xZero‖ + densityLILError v b T n) := by
  have hrate := ae_chain_fluid_rate hNm hN hNl
    hbetaZero hbetaBound hbetaMeasurable
    hL hF hT hxc hx
  filter_upwards [hrate] with omega homega
  filter_upwards [homega, Filter.eventually_gt_atTop 0]
    with n hnAll hn
  let X := namedPoissonTimeChange (N := N)
    beta v b hbetaZero hbetaBound hbetaMeasurable
    (xStart n) n omega
  have hXm : Measurable X :=
    namedPoissonTimeChange_measurable_time
      (N := N) hbetaZero hbetaBound hbetaMeasurable
      (xStart n) n omega
  have hEq : ∀ t ∈ Icc (0 : ℝ) T,
      X t = X 0 +
        ∑ l, ((poisFamily ι N l
          ((n : ℝ) * clock beta X l t) omega : ℝ) /
            (n : ℝ)) • v l := by
    intro t ht
    exact namedPoissonTimeChange_equation
      (N := N) hbetaZero hbetaBound hbetaMeasurable
      (xStart n) hn omega ht.1
  have hbound := hnAll X hXm hEq
  intro t ht
  have hpoint := hbound t ht
  have hinitial : X 0 = xStart n :=
    namedPoissonTimeChange_initial
      (N := N) hbetaZero hbetaBound hbetaMeasurable
      (xStart n) n omega
  rw [hinitial] at hpoint
  have hpoint' :
      ‖namedPoissonTimeChange (N := N)
          beta v b hbetaZero hbetaBound hbetaMeasurable
          (xStart n) n omega t - x t‖ ≤
        (‖xStart n - xZero‖ + densityLILError v b T n) *
          Real.exp (L * t) := by
    simpa only [X, densityLILError] using hpoint
  have hexp : Real.exp (L * t) ≤ Real.exp (L * T) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left ht.2 hL
  have hbase :
      0 ≤ ‖xStart n - xZero‖ + densityLILError v b T n :=
    add_nonneg (norm_nonneg _)
      (densityLILError_nonneg v b T n)
  calc
    ‖namedPoissonTimeChange (N := N)
          beta v b hbetaZero hbetaBound hbetaMeasurable
          (xStart n) n omega t - x t‖
        ≤ (‖xStart n - xZero‖ + densityLILError v b T n) *
            Real.exp (L * t) := hpoint'
    _ ≤ (‖xStart n - xZero‖ + densityLILError v b T n) *
          Real.exp (L * T) :=
        mul_le_mul_of_nonneg_left hexp hbase
    _ = Real.exp (L * T) *
          (‖xStart n - xZero‖ + densityLILError v b T n) := by
        ring

/-- Final repaired family theorem: each scale has its canonical CTMC law and
the almost-sure uniform error pays the scale-dependent initial discrepancy. -/
theorem sip_density_strong_approximation_perScaleStart
    [Nonempty ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (hNm : ∀ i, Measurable (N i))
    (hN : iIndepFun N P)
    (hNl : ∀ i k,
      P {omega | N i omega = k} = ENNReal.ofReal (poisTerm k 1))
    {Gamma : RateSpec d}
    {beta : ι → (Fin d → ℝ) → ℝ}
    {v : ι → Fin d → ℝ} {b : ι → ℝ}
    {hbetaZero : ∀ l y, 0 ≤ beta l y}
    {hbetaBound : ∀ l y, beta l y ≤ b l}
    {hbetaMeasurable : ∀ l, Measurable (beta l)}
    (D : PerScaleStartSIPFamily Gamma beta v b
      hbetaZero hbetaBound hbetaMeasurable)
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
                  densityLILError v b T n)) := by
  constructor
  · intro n hn
    exact D.path_law hNm hN hNl n hn
  · exact ae_perScaleStart_density_strong_approximation
      (N := N) hNm hN hNl
      hbetaZero hbetaBound hbetaMeasurable
      hL hF hT hxc hx D.startDensity

/-- Lattice-rounding corollary.  A `C/n` start certificate adds exactly that
term and therefore leaves the `sqrt(log log n / n)` LIL scale unchanged. -/
theorem sip_density_strong_approximation_of_lattice_rounding
    [Nonempty ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (hNm : ∀ i, Measurable (N i))
    (hN : iIndepFun N P)
    (hNl : ∀ i k,
      P {omega | N i omega = k} = ENNReal.ofReal (poisTerm k 1))
    {Gamma : RateSpec d}
    {beta : ι → (Fin d → ℝ) → ℝ}
    {v : ι → Fin d → ℝ} {b : ι → ℝ}
    {hbetaZero : ∀ l y, 0 ≤ beta l y}
    {hbetaBound : ∀ l y, beta l y ≤ b l}
    {hbetaMeasurable : ∀ l, Measurable (beta l)}
    (D : PerScaleStartSIPFamily Gamma beta v b
      hbetaZero hbetaBound hbetaMeasurable)
    {L : ℝ} (hL : 0 ≤ L)
    (hF : ∀ y z,
      ‖tcDrift beta v y - tcDrift beta v z‖ ≤ L * ‖y - z‖)
    {T : ℝ} (hT : 0 ≤ T)
    {x : ℝ → Fin d → ℝ} {xZero : Fin d → ℝ}
    (hxc : ContinuousOn x (Icc 0 T))
    (hx : ∀ t ∈ Icc (0 : ℝ) T,
      x t = xZero +
        ∫ s in (0 : ℝ)..t, tcDrift beta v (x s))
    (C : ℝ) (hC : 0 ≤ C)
    (hround : ∀ n : ℕ, ∀ hn : 0 < n,
      ‖(DensityDepCTMC.mk n hn Gamma).scaledState
          (D.alignment n hn).latticeStart - xZero‖ ≤
        C / (n : ℝ)) :
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
                (C / (n : ℝ) + densityLILError v b T n)) := by
  have hmain := sip_density_strong_approximation_perScaleStart
    (N := N) hNm hN hNl D hL hF hT hxc hx
  refine ⟨hmain.1, ?_⟩
  filter_upwards [hmain.2] with omega homega
  filter_upwards [homega, Filter.eventually_gt_atTop 0]
    with n hn' hn
  intro t ht
  have hstart :
      ‖D.startDensity n - xZero‖ ≤ C / (n : ℝ) := by
    rw [D.startDensity_eq_scaledState hn]
    exact hround n hn
  have hsum :
      ‖D.startDensity n - xZero‖ + densityLILError v b T n ≤
        C / (n : ℝ) + densityLILError v b T n :=
    add_le_add_left hstart _
  exact (hn' t ht).trans
    (mul_le_mul_of_nonneg_left hsum (Real.exp_nonneg _))

/-!
THEOREM LIST
* `densityLILError`
* `PerScaleStartSIPFamily`
* `PerScaleStartSIPFamily.startDensity_eq_scaledState`
* `PerScaleStartSIPFamily.record_law`
* `PerScaleStartSIPFamily.readout_law`
* `PerScaleStartSIPFamily.path_law`
* `ae_perScaleStart_density_strong_approximation`
* `sip_density_strong_approximation_perScaleStart`
* `sip_density_strong_approximation_of_lattice_rounding`

CLOSES
* The fixed-start restriction in the SIP family.
* The a.s.-eventual uniform bound
  `exp (L*T) * (‖xStart n - xZero‖ + E_n)`.
* The exact `C/n + E_n` lattice-rounding corollary.
* Preservation of the canonical record/readout/path laws independently at
  every positive scale.

UNFINISHED
* No concrete coordinate-rounding function is selected here; a model supplies
  `hround`.  For nearest-integer rounding in the sup norm one normally takes a
  dimension-independent constant, while other norms contribute their usual
  finite-dimensional constant.
* The compatibility-only retyping of the concrete recursion constructor is
  the explicit input recorded in `PerScaleDensityCellSystem`.
END
-/

end Ripple.Kurtz.StrongApprox.SIPDensityPerScaleStart

end
