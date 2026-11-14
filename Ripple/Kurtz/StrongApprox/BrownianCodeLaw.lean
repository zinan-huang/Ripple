-- Ripple/Kurtz/StrongApprox/BrownianCodeLaw.lean
import Ripple.Kurtz.StrongApprox.KMTTransfer
import Ripple.Kurtz.StrongApprox.AllTimeKMTLaws
import Ripple.Stochastic.BrownianMotion.Gaussian.BrownianMotion

/-!
# The rational-time code law of a Brownian motion

* `measure_eq_of_restrict_eq`: finite measures on a product space agreeing on all finite
  coordinate marginals are equal.
* `map_brownianCodeOf_eq_of_fdd`: two processes whose finite-dimensional laws at nonnegative
  rational times agree have the same rational-time path-code law.
* `map_brownianCodeOf_eq_of_isPreBrownian`: any two pre-Brownian processes have the same code law.
* `kmtBrownianCodeLaw_eq_of_isPreBrownian`: if the reference all-time KMT Brownian path is
  pre-Brownian (`hRefBrownian`), every pre-Brownian process has the law `kmtBrownianCodeLaw`,
  which is the hypothesis `hlaw` of the KMT transfer.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace Ripple.Kurtz.StrongApprox.KMTTransfer

open AllTimeKMT

theorem measure_eq_of_restrict_eq {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    {μ ν : Measure (∀ i, X i)} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ I : Finset ι, μ.map I.restrict = ν.map I.restrict) : μ = ν :=
  (show IsProjectiveLimit μ (fun I => ν.map I.restrict) from h).unique
    (show IsProjectiveLimit ν (fun I => ν.map I.restrict) from fun _ => rfl)

theorem aemeasurable_brownianCodeOf {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {β : ℝ≥0 → Ω → ℝ} (hβ : ∀ t, AEMeasurable (β t) P) :
    AEMeasurable (brownianCodeOf β) P :=
  aemeasurable_pi_iff.2 fun _ => hβ _

/-- Equal finite-dimensional laws at nonnegative rational times give equal code laws. -/
theorem map_brownianCodeOf_eq_of_fdd {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} [IsFiniteMeasure P] [IsFiniteMeasure P']
    {β : ℝ≥0 → Ω → ℝ} {β' : ℝ≥0 → Ω' → ℝ}
    (hβ : ∀ t, AEMeasurable (β t) P) (hβ' : ∀ t, AEMeasurable (β' t) P')
    (h : ∀ I : Finset KMTNonnegRat,
      P.map (fun ω (q : I) => β (nnrealOfNonnegRat q) ω) =
        P'.map (fun ω (q : I) => β' (nnrealOfNonnegRat q) ω)) :
    P.map (brownianCodeOf β) = P'.map (brownianCodeOf β') := by
  have hc := aemeasurable_brownianCodeOf hβ
  have hc' := aemeasurable_brownianCodeOf hβ'
  refine measure_eq_of_restrict_eq fun I => ?_
  rw [AEMeasurable.map_map_of_aemeasurable (Finset.measurable_restrict I).aemeasurable hc,
    AEMeasurable.map_map_of_aemeasurable (Finset.measurable_restrict I).aemeasurable hc']
  exact h I

/-- A pre-Brownian process has the Gaussian projective law at every finite rational set. -/
theorem map_rational_fdd_of_isPreBrownian {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {β : ℝ≥0 → Ω → ℝ} [hP : IsPreBrownian β P] (I : Finset KMTNonnegRat) :
    P.map (fun ω (q : I) => β (nnrealOfNonnegRat q) ω) =
      (gaussianProjectiveFamily (I.image nnrealOfNonnegRat)).map
        (fun x (q : I) => x ⟨nnrealOfNonnegRat q, Finset.mem_image_of_mem _ q.2⟩) := by
  have hJ := hP.hasLaw (I.image nnrealOfNonnegRat)
  have hg : Measurable (fun (x : (I.image nnrealOfNonnegRat) → ℝ) (q : I) =>
      x ⟨nnrealOfNonnegRat q, Finset.mem_image_of_mem _ q.2⟩) :=
    measurable_pi_lambda _ fun q => measurable_pi_apply _
  rw [← hJ.map_eq, AEMeasurable.map_map_of_aemeasurable hg.aemeasurable hJ.aemeasurable]
  rfl

/-- Any two pre-Brownian processes have the same rational-time path-code law. -/
theorem map_brownianCodeOf_eq_of_isPreBrownian {Ω Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] {P : Measure Ω} {P' : Measure Ω'}
    [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {β : ℝ≥0 → Ω → ℝ} {β' : ℝ≥0 → Ω' → ℝ}
    [IsPreBrownian β P] [IsPreBrownian β' P'] :
    P.map (brownianCodeOf β) = P'.map (brownianCodeOf β') :=
  map_brownianCodeOf_eq_of_fdd (IsPreBrownian.aemeasurable (X := β) (P := P))
    (IsPreBrownian.aemeasurable (X := β') (P := P')) fun I => by
      rw [map_rational_fdd_of_isPreBrownian (β := β) (P := P) I,
        map_rational_fdd_of_isPreBrownian (β := β') (P := P') I]

/-- The reference path as a process indexed by `ℝ≥0`. -/
def referenceBrownian (t : ℝ≥0) (ω : AllTimeKMTSpace) : ℝ := allTimeKMTBrownian (t : ℝ) ω

theorem brownianCodeOf_referenceBrownian :
    brownianCodeOf referenceBrownian = allTimeKMTBrownianCode := rfl

/-- If the reference all-time Brownian path is pre-Brownian, every pre-Brownian process has the
code law `kmtBrownianCodeLaw`; this discharges the hypothesis `hlaw` of the KMT transfer. -/
theorem kmtBrownianCodeLaw_eq_of_isPreBrownian
    (hRefBrownian : IsPreBrownian referenceBrownian allTimeKMTMeasure)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {β : ℝ≥0 → Ω → ℝ} [IsPreBrownian β P] :
    P.map (brownianCodeOf β) = kmtBrownianCodeLaw := by
  haveI := hRefBrownian
  exact map_brownianCodeOf_eq_of_isPreBrownian (β := β) (β' := referenceBrownian)
    (P := P) (P' := allTimeKMTMeasure)


/-- The KMT bound for a pre-Brownian process, with `hlaw` discharged. -/
theorem kmtTransfer_bound_ae_of_isPreBrownian
    (hRefBrownian : IsPreBrownian referenceBrownian allTimeKMTMeasure)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {β : ℝ≥0 → Ω → ℝ} [IsPreBrownian β P] (hβ : ∀ t, Measurable (β t))
    (hcont : ∀ᵐ ω ∂P, Continuous fun t => β t ω) :
    ∀ᵐ z ∂kmtTransferMeasure P (brownianCodeOf β) (measurable_brownianCodeOf hβ),
      ∀ t : ℝ≥0,
        |(cellPath (t : ℝ) z.2 : ℝ) - (t : ℝ) - β t z.1| ≤
          (kmtCodeXi (brownianCodeOf β z.1) z.2).toReal * Real.log (max 2 (t : ℝ)) :=
  kmtTransfer_bound_ae hβ hcont (kmtBrownianCodeLaw_eq_of_isPreBrownian hRefBrownian)

end Ripple.Kurtz.StrongApprox.KMTTransfer
