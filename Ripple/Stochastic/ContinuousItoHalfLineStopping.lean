import Ripple.Stochastic.ContinuousItoStopping

/-!
# Half-line martingales and random stopping

The integer-window construction gives a martingale on the entire half-line.
Stopping the raw integrand gives the same process as evaluating the original
half-line integral at its finite capped stopping time, on one event for every
time. All input compatibility and stopping identities are proved from the
installed finite-window operators.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal ENNReal

namespace Ripple.Stochastic.ContinuousItoHalfLineStopping
open AdaptedContinuousSpace ContinuousItoElementary ContinuousItoConsistency
open ContinuousItoStoppingGrid ContinuousItoStopping StoppedPredictableIntegrand
open FilteredItoIntegralCLM

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ}
  [IsFilteredPreBrownian B F μ]

section HalfLineMartingale
variable (hB : ∀ ω, Continuous (fun t => B t ω))
  (hBmeas : ∀ t, Measurable (B t))
  (H : ℝ≥0 × Ω → ℝ)
  (hH : ∀ n : ℕ, MemLp H 2
    (trimMeasure_T (𝓖 := F) (μ := μ) (n : ℝ≥0) hBmeas))

/-- Each selected integer-window path has the required adapted slice, even
though its selected horizon depends on the deterministic evaluation time. -/
theorem halfLineIto_stronglyAdapted
    (hnull : ∀ t A, MeasurableSet A → μ A = 0 → MeasurableSet[F t] A) :
    StronglyAdapted F (halfLineIto hB hBmeas H hH) := by
  intro t
  exact continuousIto_representative_adapted (coveringHorizon t) hB hBmeas hnull
    (integerIntegrand hBmeas H hH (coveringHorizon t))
    ⟨t, zero_le, (lt_coveringHorizon t).le⟩

/-- The actual patched half-line integral is a martingale. Conditional
expectations are transferred through a common integer window containing both times. -/
theorem halfLineIto_isMartingale
    (hnull : ∀ t A, MeasurableSet A → μ A = 0 → MeasurableSet[F t] A) :
    Martingale (halfLineIto hB hBmeas H hH) F μ := by
  refine ⟨halfLineIto_stronglyAdapted hB hBmeas H hH hnull, ?_⟩
  intro s t hst
  let n := coveringHorizon t
  have htn : t ≤ (n : ℝ≥0) := (lt_coveringHorizon t).le
  let ss : Set.Icc (0 : ℝ≥0) (n : ℝ≥0) := ⟨s, zero_le, hst.trans htn⟩
  let tt : Set.Icc (0 : ℝ≥0) (n : ℝ≥0) := ⟨t, zero_le, htn⟩
  have hm := continuousIto_representative_isMartingale (n : ℝ≥0) hB hBmeas hnull
    (integerIntegrand hBmeas H hH n)
  have hs : halfLineIto hB hBmeas H hH s =ᵐ[μ]
      fun ω => integerItoPath hB hBmeas H hH n ω ss :=
    (halfLineIto_integer_agreement hB hBmeas H hH).mono fun ω hω => hω n ss
  have ht : halfLineIto hB hBmeas H hH t =ᵐ[μ]
      fun ω => integerItoPath hB hBmeas H hH n ω tt :=
    (halfLineIto_integer_agreement hB hBmeas H hH).mono fun ω hω => hω n tt
  exact (condExp_congr_ae ht).trans ((hm.2 ss tt hst).trans hs.symm)

end HalfLineMartingale

/-- The stopped raw integrand uses exactly the installed predictable stochastic interval. -/
def stoppedRawIntegrand (τ : Ω → WithTop ℝ≥0) (H : ℝ≥0 × Ω → ℝ) :
    ℝ≥0 × Ω → ℝ := (stoppingRegion τ).indicator H

/-- Stopping the raw integrand produces integer-window L² membership directly. -/
theorem stoppedRawIntegrand_memLp
    (hBmeas : ∀ t, Measurable (B t))
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ)
    (H : ℝ≥0 × Ω → ℝ)
    (hH : ∀ n : ℕ, MemLp H 2
      (trimMeasure_T (𝓖 := F) (μ := μ) (n : ℝ≥0) hBmeas)) (n : ℕ) :
    MemLp (stoppedRawIntegrand τ H) 2
      (trimMeasure_T (𝓖 := F) (μ := μ) (n : ℝ≥0) hBmeas) :=
  memLp_stopped hτ (hH n)

/-- Capping to the enclosing window and then evaluating at t gives exactly
the cap at t, including for infinite stopping times. -/
theorem cappedStopTime_min {T t : ℝ≥0} (htT : t ≤ T)
    (τ : Ω → WithTop ℝ≥0) (ω : Ω) :
    min t (cappedStopTime T τ ω) = cappedStopTime t τ ω := by
  apply WithTop.coe_injective
  rw [WithTop.coe_min, coe_cappedStopTime, coe_cappedStopTime,
    min_left_comm, min_eq_left (WithTop.coe_le_coe.mpr htT)]

section HalfLineStopping
variable (hB : ∀ ω, Continuous (fun t => B t ω))
  (hBmeas : ∀ t, Measurable (B t))
  {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ)
  (H : ℝ≥0 × Ω → ℝ)
  (hH : ∀ n : ℕ, MemLp H 2
    (trimMeasure_T (𝓖 := F) (μ := μ) (n : ℝ≥0) hBmeas))

/-- The integer class constructed from the stopped raw function is exactly
the stopped class of the original integer integrand. -/
theorem integerIntegrand_stoppedRaw (n : ℕ) :
    integerIntegrand hBmeas (stoppedRawIntegrand τ H)
        (stoppedRawIntegrand_memLp hBmeas hτ H hH) n =
      stoppedIntegrand (n : ℝ≥0) hBmeas hτ (integerIntegrand hBmeas H hH n) := by
  apply Lp.ext
  filter_upwards [(stoppedRawIntegrand_memLp hBmeas hτ H hH n).coeFn_toLp,
    stoppedIntegrand_coeFn (n : ℝ≥0) hBmeas hτ (integerIntegrand hBmeas H hH n),
    (hH n).coeFn_toLp] with z hs ht hHraw
  change ((stoppedRawIntegrand_memLp hBmeas hτ H hH n).toLp _ :
    ℝ≥0 × Ω → ℝ) z = _
  rw [hs, ht]
  by_cases hz : z ∈ stoppingRegion τ
  · simpa only [stoppedRawIntegrand, Set.indicator_of_mem hz] using hHraw.symm
  · simp only [stoppedRawIntegrand, Set.indicator_of_notMem hz]

/-- All integer windows have the stopped identity on one common event. -/
theorem integerItoPath_stoppedRaw :
    ∀ᵐ ω ∂μ, ∀ n : ℕ, ∀ t : Set.Icc (0 : ℝ≥0) (n : ℝ≥0),
      integerItoPath hB hBmeas (stoppedRawIntegrand τ H)
          (stoppedRawIntegrand_memLp hBmeas hτ H hH) n ω t =
        integerItoPath hB hBmeas H hH n ω
          (stoppedWindowTime (n : ℝ≥0) (cappedStopTime (n : ℝ≥0) τ) ω t) := by
  apply ae_all_iff.mpr
  intro n
  change ∀ᵐ ω ∂μ, ∀ t : Set.Icc (0 : ℝ≥0) (n : ℝ≥0),
    representative (continuousIto (n : ℝ≥0) hB hBmeas
      (integerIntegrand hBmeas (stoppedRawIntegrand τ H)
        (stoppedRawIntegrand_memLp hBmeas hτ H hH) n)) ω t = _
  rw [integerIntegrand_stoppedRaw hBmeas hτ H hH n]
  exact continuousIto_stopped (n : ℝ≥0) hB hBmeas hτ (integerIntegrand hBmeas H hH n)

/-- The actual half-line integral of the stopped raw integrand equals the
original half-line integral evaluated at the finite capped stopping time.
One event supports this identity for every nonnegative time. -/
theorem halfLineIto_stoppedRaw :
    ∀ᵐ ω ∂μ, ∀ t : ℝ≥0,
      halfLineIto hB hBmeas (stoppedRawIntegrand τ H)
          (stoppedRawIntegrand_memLp hBmeas hτ H hH) t ω =
        halfLineIto hB hBmeas H hH (cappedStopTime t τ ω) ω := by
  filter_upwards [halfLineIto_integer_agreement hB hBmeas (stoppedRawIntegrand τ H)
      (stoppedRawIntegrand_memLp hBmeas hτ H hH),
    halfLineIto_integer_agreement hB hBmeas H hH,
    integerItoPath_stoppedRaw hB hBmeas hτ H hH] with ω hstop horig heq t
  let n := coveringHorizon t
  have htn : t ≤ (n : ℝ≥0) := (lt_coveringHorizon t).le
  let tt : Set.Icc (0 : ℝ≥0) (n : ℝ≥0) := ⟨t, zero_le, htn⟩
  let tc : Set.Icc (0 : ℝ≥0) (n : ℝ≥0) :=
    ⟨cappedStopTime t τ ω, zero_le, (cappedStopTime_le t τ ω).trans htn⟩
  have htime : stoppedWindowTime (n : ℝ≥0) (cappedStopTime (n : ℝ≥0) τ) ω tt = tc := by
    apply Subtype.ext
    exact cappedStopTime_min htn τ ω
  exact (hstop n tt).trans ((heq n tt).trans (by rw [htime]; exact (horig n tc).symm))

/-- The half-line integral of the stopped raw integrand is itself a
martingale, produced without requiring measurability of random half-line evaluation. -/
theorem halfLineIto_stoppedRaw_isMartingale
    (hnull : ∀ t A, MeasurableSet A → μ A = 0 → MeasurableSet[F t] A) :
    Martingale (halfLineIto hB hBmeas (stoppedRawIntegrand τ H)
      (stoppedRawIntegrand_memLp hBmeas hτ H hH)) F μ :=
  halfLineIto_isMartingale hB hBmeas (stoppedRawIntegrand τ H)
    (stoppedRawIntegrand_memLp hBmeas hτ H hH) hnull

end HalfLineStopping
end Ripple.Stochastic.ContinuousItoHalfLineStopping
