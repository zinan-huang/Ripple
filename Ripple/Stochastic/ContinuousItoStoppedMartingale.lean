import Ripple.Stochastic.ContinuousItoStopping

/-!
# Martingale property of the actual stopped continuous integral

The process below evaluates the installed continuous representative at the
finite minimum with the stopping time. Its martingale property is transferred
from the integral of the stopped integrand by the proved all-time identity.
The null-set completeness hypothesis is the same one used by the installed
exactly adapted continuous representative.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace Ripple.Stochastic.ContinuousItoStoppedMartingale
open AdaptedContinuousSpace ContinuousItoElementary ContinuousItoConsistency
open ContinuousItoStoppingGrid ContinuousItoStopping StoppedPredictableIntegrand
open FilteredItoIntegralCLM FilteredItoIntegralProcessGeneral

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ}
  [IsFilteredPreBrownian B F μ]

/-- The actual stopped path, with the infinite stopping-time case handled
by taking the finite horizon minimum first. -/
def stoppedContinuousIto (T : ℝ≥0)
    (hB : ∀ ω, Continuous (fun t => B t ω)) (hBmeas : ∀ t, Measurable (B t))
    (τ : Ω → WithTop ℝ≥0)
    (φ : Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas))
    (t : Set.Icc (0 : ℝ≥0) T) (ω : Ω) : ℝ :=
  representative (continuousIto T hB hBmeas φ) ω
    (stoppedWindowTime T (cappedStopTime T τ) ω t)

/-- The finite cap is an ambient measurable random variable. -/
theorem measurable_cappedStopTime (T : ℝ≥0) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime F τ) : Measurable (cappedStopTime T τ) := by
  apply measurable_of_Iic
  intro a
  have hs := (cappedStopTime_isStoppingTime T hτ).measurableSet_le a
  have hs' : MeasurableSet[F a] {ω | cappedStopTime T τ ω ≤ a} := by
    simpa only [WithTop.coe_le_coe] using hs
  exact F.le a _ hs'

/-- Random evaluation of the strongly measurable continuous path is measurable. -/
theorem stoppedContinuousIto_stronglyMeasurable (T : ℝ≥0)
    (hB : ∀ ω, Continuous (fun t => B t ω)) (hBmeas : ∀ t, Measurable (B t))
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ)
    (φ : Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas))
    (t : Set.Icc (0 : ℝ≥0) T) :
    StronglyMeasurable (stoppedContinuousIto T hB hBmeas τ φ t) := by
  have htime : Measurable (fun ω => stoppedWindowTime T (cappedStopTime T τ) ω t) :=
    (measurable_const.min (measurable_cappedStopTime T hτ)).subtype_mk
  have heval : Continuous (fun p : C(Set.Icc (0 : ℝ≥0) T, ℝ) × Set.Icc (0 : ℝ≥0) T =>
      p.1 p.2) := by fun_prop
  exact heval.comp_stronglyMeasurable
    ((representative_stronglyMeasurable (continuousIto T hB hBmeas φ)).prodMk
      htime.stronglyMeasurable)

/-- The stopped path agrees with the representative of the stopped integrand's integral. -/
theorem stoppedContinuousIto_ae_rep (T : ℝ≥0)
    (hB : ∀ ω, Continuous (fun t => B t ω)) (hBmeas : ∀ t, Measurable (B t))
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ)
    (φ : Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas))
    (t : Set.Icc (0 : ℝ≥0) T) :
    stoppedContinuousIto T hB hBmeas τ φ t =ᵐ[μ]
      fun ω => representative (continuousIto T hB hBmeas
        (stoppedIntegrand T hBmeas hτ φ)) ω t := by
  filter_upwards [continuousIto_stopped T hB hBmeas hτ φ] with ω hω
  exact (hω t).symm

/-- The stopped path has exactly the stopped-integrand slice L² class. -/
theorem stoppedContinuousIto_ae_slice (T : ℝ≥0)
    (hB : ∀ ω, Continuous (fun t => B t ω)) (hBmeas : ∀ t, Measurable (B t))
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ)
    (φ : Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas))
    (t : Set.Icc (0 : ℝ≥0) T) :
    stoppedContinuousIto T hB hBmeas τ φ t =ᵐ[μ]
      (itoProcessCLM (𝓖 := F) (μ := μ) T t.val hBmeas
        (stoppedIntegrand T hBmeas hτ φ) : Ω → ℝ) :=
  (stoppedContinuousIto_ae_rep T hB hBmeas hτ φ t).trans
    (representative_eval_ae T hB hBmeas (stoppedIntegrand T hBmeas hτ φ) t)

/-- Every stopped slice is square integrable, for every predictable L² integrand. -/
theorem stoppedContinuousIto_memLp (T : ℝ≥0)
    (hB : ∀ ω, Continuous (fun t => B t ω)) (hBmeas : ∀ t, Measurable (B t))
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ)
    (φ : Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas))
    (t : Set.Icc (0 : ℝ≥0) T) :
    MemLp (stoppedContinuousIto T hB hBmeas τ φ t) 2 μ :=
  (Lp.memLp _).ae_eq (stoppedContinuousIto_ae_slice T hB hBmeas hτ φ t).symm

/-- Completion transfers adaptedness to the same stopped continuous realization. -/
theorem stoppedContinuousIto_adapted (T : ℝ≥0)
    (hB : ∀ ω, Continuous (fun t => B t ω)) (hBmeas : ∀ t, Measurable (B t))
    (hnull : ∀ t A, MeasurableSet A → μ A = 0 → MeasurableSet[F t] A)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ)
    (φ : Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas))
    (t : Set.Icc (0 : ℝ≥0) T) :
    StronglyMeasurable[F t.val] (stoppedContinuousIto T hB hBmeas τ φ t) := by
  have heq := stoppedContinuousIto_ae_rep T hB hBmeas hτ φ t
  exact (measurable_of_ae_eq_of_null_sets (hnull t.val)
    (stoppedContinuousIto_stronglyMeasurable T hB hBmeas hτ φ t).measurable
    (continuousIto_representative_adapted T hB hBmeas hnull
      (stoppedIntegrand T hBmeas hτ φ) t).measurable heq).stronglyMeasurable

/-- The stopped integral is a martingale, with no stopping-identity premise.
The filtration completeness condition concerns only exact realization. -/
theorem stoppedContinuousIto_isMartingale (T : ℝ≥0)
    (hB : ∀ ω, Continuous (fun t => B t ω)) (hBmeas : ∀ t, Measurable (B t))
    (hnull : ∀ t A, MeasurableSet A → μ A = 0 → MeasurableSet[F t] A)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ)
    (φ : Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas)) :
    Martingale (stoppedContinuousIto T hB hBmeas τ φ)
      (Doob.Filtration.compMono mΩ F (fun t : Set.Icc (0 : ℝ≥0) T => t.val)
        (fun _ _ h => h)) μ := by
  have hm := continuousIto_representative_isMartingale T hB hBmeas hnull
    (stoppedIntegrand T hBmeas hτ φ)
  have heq : ∀ t : Set.Icc (0 : ℝ≥0) T,
      stoppedContinuousIto T hB hBmeas τ φ t =ᵐ[μ]
        fun ω => representative (continuousIto T hB hBmeas
          (stoppedIntegrand T hBmeas hτ φ)) ω t :=
    fun t => stoppedContinuousIto_ae_rep T hB hBmeas hτ φ t
  refine ⟨fun t => stoppedContinuousIto_adapted T hB hBmeas hnull hτ φ t, ?_⟩
  intro s t hst
  exact (condExp_congr_ae (heq t)).trans ((hm.2 s t hst).trans (heq s).symm)

end Ripple.Stochastic.ContinuousItoStoppedMartingale
