-- Ripple/Kurtz/StrongApprox/SIPDensityCellRecordInterface.lean
import Ripple.Kurtz.StrongApprox.CellRecordLawInterface
import Ripple.Kurtz.StrongApprox.SIPDensityStrongApprox

noncomputable section

namespace Ripple.Kurtz.StrongApprox

open MeasureTheory ProbabilityTheory Set Filter
open Ripple.CTMC
open scoped ENNReal NNReal BigOperators

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]
variable {N : ℕ → Ω → ℕ}
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Correct downstream replacement for `DensitySIPFamily`: instead of a map
into the independent-row construction, it carries a direct cell record
realization and an almost-sure/pathwise identification supplied by the repaired
record construction.  This structure is not claimed constructible from the
current raw `CellStoppingLine` API. -/
structure DensitySIPCellRecordFamily
    (Γ : Ripple.Kurtz.RateSpec d)
    (β : ι → (Fin d → ℝ) → ℝ)
    (v : ι → Fin d → ℝ) (b : ι → ℝ)
    (hβ0 : ∀ l y, 0 ≤ β l y)
    (hβb : ∀ l y, β l y ≤ b l)
    (hβm : ∀ l, Measurable (β l))
    (xDensity : Fin d → ℝ) : Type _ where
  latticeStart : ∀ n : ℕ, 0 < n → Fin d → Fin (n + 1)
  record : ∀ n : ℕ, ∀ hn : 0 < n,
    CellFamily ι → ℕ → ℝ × (Fin d → Fin (n + 1))
  internal : ∀ n : ℕ, ∀ hn : 0 < n,
    ℕ → CellFamily ι → ι → ℝ≥0
  realization : ∀ n : ℕ, ∀ hn : 0 < n,
    CellDensityRecordRealization
      (DensityDepCTMC.mk n hn Γ)
      (latticeStart n hn)
      (record n hn)
      (internal n hn)
  path_eq : ∀ n : ℕ, ∀ hn : 0 < n, ∀ c : CellFamily ι,
    cellTimeChangeNonnegative (β := β) (v := v) (b := b)
        hn hβ0 hβb hβm xDensity c =
      AlignedCellCoupling.canonicalDensityNonnegative
        (DensityDepCTMC.mk n hn Γ) (record n hn c)

namespace DensitySIPCellRecordFamily

/-- Sample measurability follows directly from the measurable record map and
canonical readout, with no map into `ConstructedΩ`. -/
theorem measurable_cell_path
    {Γ : Ripple.Kurtz.RateSpec d}
    {β : ι → (Fin d → ℝ) → ℝ}
    {v : ι → Fin d → ℝ} {b : ι → ℝ}
    {hβ0 : ∀ l y, 0 ≤ β l y}
    {hβb : ∀ l y, β l y ≤ b l}
    {hβm : ∀ l, Measurable (β l)}
    {xDensity : Fin d → ℝ}
    (D : DensitySIPCellRecordFamily
      Γ β v b hβ0 hβb hβm xDensity)
    (n : ℕ) (hn : 0 < n) :
    Measurable
      (cellTimeChangeNonnegative (β := β) (v := v) (b := b)
        hn hβ0 hβb hβm xDensity) := by
  have hfun :
      cellTimeChangeNonnegative (β := β) (v := v) (b := b)
          hn hβ0 hβb hβm xDensity =
        AlignedCellCoupling.canonicalDensityNonnegative
          (DensityDepCTMC.mk n hn Γ) ∘ D.record n hn := by
    funext c
    exact D.path_eq n hn c
  rw [hfun]
  exact
    (AlignedCellCoupling.canonicalDensityNonnegative_measurable
      (DensityDepCTMC.mk n hn Γ)).comp
        (D.realization n hn).density.measurable_record

/-- Direct canonical law of the universal-cell time-change path. -/
theorem cell_path_law
    {Γ : Ripple.Kurtz.RateSpec d}
    {β : ι → (Fin d → ℝ) → ℝ}
    {v : ι → Fin d → ℝ} {b : ι → ℝ}
    {hβ0 : ∀ l y, 0 ≤ β l y}
    {hβb : ∀ l y, β l y ≤ b l}
    {hβm : ∀ l, Measurable (β l)}
    {xDensity : Fin d → ℝ}
    (D : DensitySIPCellRecordFamily
      Γ β v b hβ0 hβb hβm xDensity)
    (n : ℕ) (hn : 0 < n) :
    (cellFamilyLaw ι).map
        (cellTimeChangeNonnegative (β := β) (v := v) (b := b)
          hn hβ0 hβb hβm xDensity) =
      ((DensityDepCTMC.mk n hn Γ).toQMatrix.canonicalRecordMeasure
        (D.latticeStart n hn)).map
          (AlignedCellCoupling.canonicalDensityNonnegative
            (DensityDepCTMC.mk n hn Γ)) := by
  have hfun :
      cellTimeChangeNonnegative (β := β) (v := v) (b := b)
          hn hβ0 hβb hβm xDensity =
        AlignedCellCoupling.canonicalDensityNonnegative
          (DensityDepCTMC.mk n hn Γ) ∘ D.record n hn := by
    funext c
    exact D.path_eq n hn c
  rw [hfun]
  exact (D.realization n hn).readout_law

/-- Law transfer from universal cells to the actual SIP family. -/
theorem path_law
    {Γ : Ripple.Kurtz.RateSpec d}
    {β : ι → (Fin d → ℝ) → ℝ}
    {v : ι → Fin d → ℝ} {b : ι → ℝ}
    {hβ0 : ∀ l y, 0 ≤ β l y}
    {hβb : ∀ l y, β l y ≤ b l}
    {hβm : ∀ l, Measurable (β l)}
    {xDensity : Fin d → ℝ}
    (D : DensitySIPCellRecordFamily
      Γ β v b hβ0 hβb hβm xDensity)
    (hNm : ∀ i, Measurable (N i))
    (hN : iIndepFun N P)
    (hNl : ∀ i k,
      P {ω | N i ω = k} = ENNReal.ofReal (poisTerm k 1))
    (n : ℕ) (hn : 0 < n) :
    (familyMeasure ι P).map
        (fun (ω : ι → PathSpace Ω) (t : ℝ≥0) =>
          namedPoissonTimeChange (N := N)
            β v b hβ0 hβb hβm xDensity n ω t) =
      ((DensityDepCTMC.mk n hn Γ).toQMatrix.canonicalRecordMeasure
        (D.latticeStart n hn)).map
          (AlignedCellCoupling.canonicalDensityNonnegative
            (DensityDepCTMC.mk n hn Γ)) := by
  have hnamed :
      (fun (ω : ι → PathSpace Ω) (t : ℝ≥0) =>
        namedPoissonTimeChange (N := N)
          β v b hβ0 hβb hβm xDensity n ω t) =
      globalNonnegativePath (N := N) (β := β) (v := v) (b := b)
        hn hβ0 hβb hβm xDensity := by
    funext ω t
    rw [namedPoissonTimeChange_eq_global
      (N := N) (v := v) hβ0 hβb hβm xDensity hn]
    rfl
  rw [hnamed]
  have hfactor :
      globalNonnegativePath (N := N) (β := β) (v := v) (b := b)
          hn hβ0 hβb hβm xDensity =
        cellTimeChangeNonnegative (β := β) (v := v) (b := b)
          hn hβ0 hβb hβm xDensity ∘
            familyCellSequence ι N := by
    funext ω
    exact globalNonnegativePath_eq_cellFactor
      (N := N) (β := β) (v := v) (b := b)
        hn hβ0 hβb hβm xDensity ω
  rw [hfactor, ← Measure.map_map
      (measurable_cell_path D n hn)
      (measurable_familyCellSequence ι hNm),
    familyCellSequence_law ι hNm hN hNl]
  exact cell_path_law D n hn

/-- Correct downstream one-space theorem.  It has no
`AlignedCellCoupling` hypothesis; instead it consumes a direct cell record
realization.  Constructing that realization requires the stopping-line repair
and channel-alignment assumptions stated above. -/
theorem sip_density_strong_approximation_of_cell_records
    (hNm : ∀ i, Measurable (N i))
    (hN : iIndepFun N P)
    (hNl : ∀ i k,
      P {ω | N i ω = k} = ENNReal.ofReal (poisTerm k 1))
    {Γ : Ripple.Kurtz.RateSpec d}
    {β : ι → (Fin d → ℝ) → ℝ}
    {v : ι → Fin d → ℝ} {b : ι → ℝ}
    {hβ0 : ∀ l y, 0 ≤ β l y}
    {hβb : ∀ l y, β l y ≤ b l}
    {hβm : ∀ l, Measurable (β l)}
    {xDensity : Fin d → ℝ}
    (D : DensitySIPCellRecordFamily
      Γ β v b hβ0 hβb hβm xDensity)
    {L : ℝ} (hL : 0 ≤ L)
    (hF : ∀ y z,
      ‖tcDrift β v y - tcDrift β v z‖ ≤ L * ‖y - z‖)
    {T : ℝ} (hT : 0 ≤ T)
    {x : ℝ → Fin d → ℝ}
    (hxc : ContinuousOn x (Icc 0 T))
    (hx : ∀ t ∈ Icc (0 : ℝ) T,
      x t = xDensity +
        ∫ s in (0 : ℝ)..t, tcDrift β v (x s)) :
    (∀ n : ℕ, ∀ hn : 0 < n,
      (familyMeasure ι P).map
          (fun (ω : ι → PathSpace Ω) (t : ℝ≥0) =>
            namedPoissonTimeChange (N := N)
              β v b hβ0 hβb hβm xDensity n ω t) =
        ((DensityDepCTMC.mk n hn Γ).toQMatrix.canonicalRecordMeasure
          (D.latticeStart n hn)).map
            (AlignedCellCoupling.canonicalDensityNonnegative
              (DensityDepCTMC.mk n hn Γ))) ∧
      (∀ᵐ ω ∂familyMeasure ι P,
        ∀ᶠ n : ℕ in atTop,
          ∀ t ∈ Icc (0 : ℝ) T,
            ‖namedPoissonTimeChange (N := N)
                β v b hβ0 hβb hβm xDensity n ω t - x t‖ ≤
              ((n : ℝ)⁻¹ *
                ∑ l, ‖v l‖ * envelope ((n : ℝ) * (b l * T))) *
                  Real.exp (L * t)) := by
  refine ⟨?_, ?_⟩
  · intro n hn
    exact path_law D hNm hN hNl n hn
  · exact ae_namedPoissonTimeChange_rate
      (N := N) hNm hN hNl
        hβ0 hβb hβm hL hF hT hxc hx

/-!
THEOREM LIST
* `DensitySIPCellRecordFamily.measurable_cell_path`
* `DensitySIPCellRecordFamily.cell_path_law`
* `DensitySIPCellRecordFamily.path_law`
* `DensitySIPCellRecordFamily.sip_density_strong_approximation_of_cell_records`

CLOSES
* The entire downstream law-transfer and strong-approximation composition once
  a direct cell record realization and readout identification are available.
* Syntactic removal of `AlignedCellCoupling`; no `ConstructedΩ` map appears in
  the replacement data or proofs.

UNFINISHED
* A direct inhabitant of `DensitySIPCellRecordFamily`.  Under the present raw
  finite-valued stopping-line definition, its `realization.filtration.stopping`
  field is refuted by Counterexample 1.
* The channel-alignment/boundary-compatibility construction needed to prove
  `realization.density.history_next` and `path_eq`; these hypotheses are absent
  from the original requested theorem and Counterexample 2 shows they cannot
  be omitted.
-/

end DensitySIPCellRecordFamily

end Ripple.Kurtz.StrongApprox

end
