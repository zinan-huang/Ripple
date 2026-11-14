-- Ripple/Kurtz/StrongApprox/CellStoppingLineResiduals.lean
import Ripple.Kurtz.StrongApprox.CellStoppingLineFreshness
import Ripple.Kurtz.StrongApprox.RecordPastFreshness
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

noncomputable section

namespace Ripple.Kurtz.StrongApprox.CellStoppingLineResiduals

open MeasureTheory ProbabilityTheory Set Filter Topology Preorder
open scoped ENNReal NNReal BigOperators
open ExponentialRace
open CellRandomTimeEvaluation CellStoppingLineFreshness

variable {ι S : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [MeasurableSpace S]

abbrev CellΩ (ι : Type*) := CellFamily ι

/-- Residual vector after a deterministic internal-clock vector. -/
noncomputable def deterministicResidual
    (u : ι → ℝ≥0) (c : CellΩ ι) : ι → ℝ :=
  residualVector (fun _ => u) c

@[fun_prop]
theorem measurable_deterministicResidual (u : ι → ℝ≥0) :
    Measurable (deterministicResidual u) := by
  apply measurable_residualVector
  exact measurable_const

/-- Residual vector after a rounded line. -/
noncomputable def roundedResidual
    (m : ℕ) (σ : CellΩ ι → ι → ℝ≥0) (c : CellΩ ι) : ι → ℝ :=
  deterministicResidual (roundedLine m σ c) c

/-- Residual vector at the true line. -/
noncomputable def stoppingResidual
    (σ : CellΩ ι → ι → ℝ≥0) (c : CellΩ ι) : ι → ℝ :=
  residualVector σ c

@[fun_prop]
theorem measurable_roundedResidual
    {σ : CellΩ ι → ι → ℝ≥0} (hσ : CellStoppingLine σ)
    (m : ℕ) : Measurable (roundedResidual m σ) := by
  simpa only [roundedResidual] using
    (measurable_roundedFuture measurable_deterministicResidual hσ m)

@[fun_prop]
theorem measurable_stoppingResidual
    {σ : CellΩ ι → ι → ℝ≥0} (hσ : CellStoppingLine σ) :
    Measurable (stoppingResidual σ) := by
  exact measurable_residualVector hσ.measurable

/-- Explicit interface to the deterministic first-wait and
wait-vector product laws. -/
def DeterministicResidualFresh : Prop :=
  DeterministicFresh (ι := ι) deterministicResidual (clockLaw ι)

/-- Explicit interface to the rounded-residual convergence
lemma.  Its path hypotheses are now discharged only by `cellPath`. -/
def RoundedResidualConvergence
    (σ : CellΩ ι → ι → ℝ≥0) : Prop :=
  ∀ᵐ c ∂cellFamilyLaw ι,
    Tendsto (fun m => roundedResidual m σ c) atTop
      (𝓝 (stoppingResidual σ c))

/-- Generic limit lemma used by `CellStoppingLineFreshness`, restated here so this file has no
hidden dependency on it. -/
theorem freshResidualsAt_of_ae_tendsto
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {R : Ω → ℕ → ℝ × S} {k : ℕ}
    (residual : Ω → ι → ℝ)
    (approx : ℕ → Ω → ι → ℝ)
    (hHistory : Measurable (recordPrefix R k))
    (hResidual : Measurable residual)
    (hApprox : ∀ m, Measurable (approx m))
    (hFresh : ∀ m, FreshResidualsAt μ R (approx m) k)
    (hLimit : ∀ᵐ ω ∂μ,
      Tendsto (fun m => approx m ω) atTop (𝓝 (residual ω))) :
    FreshResidualsAt μ R residual k := by
  refine
    { measurable_history := hHistory
      measurable_residual := hResidual
      joint_law := ?_ }
  classical
  let hist : Ω → ((i : Finset.Iic k) → ℝ × S) := recordPrefix R k
  have hHist : Measurable hist := hHistory
  letI : IsProbabilityMeasure (μ.map hist) :=
    Measure.isProbabilityMeasure_map hHist.aemeasurable
  have hJointMeas : Measurable fun ω => (hist ω, residual ω) :=
    hHist.prodMk hResidual
  refine (Measure.prod_eq ?_).symm
  intro A B hA hB
  let flagOnHistory : ((i : Finset.Iic k) → ℝ × S) → ℝ :=
    fun h => if h ∈ A then 1 else 0
  have hFlagOnHistory : Measurable flagOnHistory :=
    Measurable.ite hA measurable_const measurable_const
  let flag : Ω → ℝ := flagOnHistory ∘ hist
  have hFlag : Measurable flag := hFlagOnHistory.comp hHist
  let Zm : ℕ → Ω → ℝ × (ι → ℝ) :=
    fun m ω => (flag ω, approx m ω)
  let Z : Ω → ℝ × (ι → ℝ) :=
    fun ω => (flag ω, residual ω)
  let μzero : Measure (ℝ × (ι → ℝ)) :=
    (μ.map flag).prod (clockLaw ι)
  letI : IsProbabilityMeasure (μ.map flag) :=
    Measure.isProbabilityMeasure_map hFlag.aemeasurable
  letI : IsProbabilityMeasure (clockLaw ι) := inferInstance
  letI : IsProbabilityMeasure μzero := by
    dsimp [μzero]
    infer_instance
  have hZmMeas (m : ℕ) : Measurable (Zm m) :=
    hFlag.prodMk (hApprox m)
  have hZMeas : Measurable Z := hFlag.prodMk hResidual
  have hZmLaw (m : ℕ) : μ.map (Zm m) = μzero := by
    calc
      μ.map (Zm m) =
          (μ.map (fun ω => (hist ω, approx m ω))).map
            (Prod.map flagOnHistory id) := by
        rw [Measure.map_map
          (hFlagOnHistory.prodMap measurable_id)
          (hHist.prodMk (hApprox m))]
        rfl
      _ = ((μ.map hist).prod (clockLaw ι)).map
            (Prod.map flagOnHistory id) := by
        rw [(hFresh m).joint_law]
      _ = ((μ.map hist).map flagOnHistory).prod
            ((clockLaw ι).map id) := by
        rw [Measure.map_prod_map _ _ hFlagOnHistory measurable_id]
      _ = μzero := by
        rw [Measure.map_id, Measure.map_map hFlagOnHistory hHist]
  have hPairLimit : ∀ᵐ ω ∂μ,
      Tendsto (fun m => Zm m ω) atTop (𝓝 (Z ω)) := by
    filter_upwards [hLimit] with ω hω
    exact (tendsto_const_nhds (x := flag ω)).prodMk_nhds hω
  have hInMeasure : TendstoInMeasure μ Zm atTop Z :=
    tendstoInMeasure_of_tendsto_ae
      (fun m => (hZmMeas m).aestronglyMeasurable) hPairLimit
  have hDistLimit : TendstoInDistribution Zm atTop Z
      (fun _ => μ) μ :=
    hInMeasure.tendstoInDistribution (fun m => (hZmMeas m).aemeasurable)
  let idVar : ℝ × (ι → ℝ) → ℝ × (ι → ℝ) := id
  have hDistConst : TendstoInDistribution Zm atTop idVar
      (fun _ => μ) μzero := by
    apply tendstoInDistribution_of_identDistrib 0
    · intro m
      exact
        { aemeasurable_fst := (hZmMeas 0).aemeasurable
          aemeasurable_snd := (hZmMeas m).aemeasurable
          map_eq := (hZmLaw 0).trans (hZmLaw m).symm }
    · exact
        { aemeasurable_fst := (hZmMeas 0).aemeasurable
          aemeasurable_snd := measurable_id.aemeasurable
          map_eq := by simpa [idVar] using hZmLaw 0 }
  have hZLaw : μ.map Z = μzero := by
    simpa [idVar] using
      (tendstoInDistribution_unique Zm hDistLimit hDistConst)
  have hZpre :
      Z ⁻¹' ({1} ×ˢ B) =
        (fun ω => (hist ω, residual ω)) ⁻¹' (A ×ˢ B) := by
    ext ω
    by_cases h : hist ω ∈ A <;> simp [Z, flag, flagOnHistory, h]
  have hFlagPre : flag ⁻¹' ({1} : Set ℝ) = hist ⁻¹' A := by
    ext ω
    by_cases h : hist ω ∈ A <;> simp [flag, flagOnHistory, h]
  have hRect := congrArg
    (fun ρ : Measure (ℝ × (ι → ℝ)) => ρ ({1} ×ˢ B)) hZLaw
  dsimp only at hRect
  have hμz : μzero ({1} ×ˢ B) = (μ.map flag) {1} * clockLaw ι B :=
    Measure.prod_prod _ _
  rw [Measure.map_apply hZMeas
      ((measurableSet_singleton (1 : ℝ)).prod hB),
    hZpre, hμz,
    Measure.map_apply hFlag (measurableSet_singleton (1 : ℝ)),
    hFlagPre] at hRect
  rw [Measure.map_apply hJointMeas (hA.prod hB), Measure.map_apply hHist hA]
  exact hRect

/-- Product-law version of `rounded_event_factor`. -/
theorem rounded_joint_law
    {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    {G : (ι → ℝ≥0) → CellΩ ι → F} {ν : Measure F}
    (hdet : DeterministicFresh G ν)
    {σ : CellΩ ι → ι → ℝ≥0} (hσ : CellStoppingLine σ)
    (m : ℕ) (H : CellΩ ι → E)
    (hH : Measurable[cellStoppedPast σ hσ] H) :
    (cellFamilyLaw ι).map
        (fun c => (H c, roundedFuture G m σ c)) =
      ((cellFamilyLaw ι).map H).prod ν := by
  have hHa : Measurable H := measurable_stoppedPast_ambient hH
  have hGa : Measurable (roundedFuture G m σ) :=
    measurable_roundedFuture hdet.measurable_future hσ m
  haveI : IsProbabilityMeasure ν := ⟨by
    have h := hdet.factor (fun _ => 0) Set.univ Set.univ
      (@MeasurableSet.univ _ (cellPast _)) MeasurableSet.univ
    simpa using h.symm⟩
  refine (Measure.prod_eq ?_).symm
  intro A B hA hB
  rw [Measure.map_apply (hHa.prodMk hGa) (hA.prod hB),
    Measure.map_apply hHa hA]
  exact rounded_event_factor hdet hσ m (H ⁻¹' A) B (hH hA) hB

/-- Fresh residuals at each rounded line, obtained by summing the deterministic
renewal law over the stopping-line grid fibres. -/
theorem rounded_freshResidualsAt
    {R : CellΩ ι → ℕ → ℝ × S} {k m : ℕ}
    {σ : CellΩ ι → ι → ℝ≥0} (hσ : CellStoppingLine σ)
    (hHistory :
      Measurable[cellStoppedPast σ hσ] (recordPrefix R k))
    (hdet : DeterministicResidualFresh (ι := ι)) :
    FreshResidualsAt (cellFamilyLaw ι) R
      (roundedResidual m σ) k := by
  have hHistAmbient : Measurable (recordPrefix R k) :=
    measurable_stoppedPast_ambient hHistory
  refine
    { measurable_history := hHistAmbient
      measurable_residual := measurable_roundedResidual hσ m
      joint_law := ?_ }
  exact rounded_joint_law hdet hσ m (recordPrefix R k) hHistory

/-- **Consumer-facing headline.**  At a genuine cell stopping line, the
residual waiting-time vector has iid unit-exponential law and is independent
of the complete finite record past. -/
theorem cellStoppingLine_freshResidualsAt
    {R : CellΩ ι → ℕ → ℝ × S} {k : ℕ}
    {σ : CellΩ ι → ι → ℝ≥0} (hσ : CellStoppingLine σ)
    (hHistory :
      Measurable[cellStoppedPast σ hσ] (recordPrefix R k))
    (hdet : DeterministicResidualFresh (ι := ι))
    (hlimit : RoundedResidualConvergence σ) :
    FreshResidualsAt (cellFamilyLaw ι) R
      (stoppingResidual σ) k := by
  apply freshResidualsAt_of_ae_tendsto
    (stoppingResidual σ) (fun m => roundedResidual m σ)
    (measurable_stoppedPast_ambient hHistory)
    (measurable_stoppingResidual hσ)
    (fun m => measurable_roundedResidual hσ m)
    (fun m => rounded_freshResidualsAt hσ hHistory hdet)
    hlimit

end Ripple.Kurtz.StrongApprox.CellStoppingLineResiduals

end
