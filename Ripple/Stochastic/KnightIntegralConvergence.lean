import Ripple.Stochastic.ClockStoppedIntegral
import Ripple.Stochastic.KnightDoobBlocks

/-!
# Finite-clock convergence for the installed half-line Itô integral

Finite-window increment isometry telescopes second moments. The concrete
inverse-clock stopping bound makes their total increment energy finite. Doob's
block theorem then gives full-time convergence of each stopped raw integral,
and countable localization removes the clock cap.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace Ripple.Stochastic.KnightIntegralConvergence
open Ripple.Analysis Ripple.ProbabilityTheory
open FilteredItoIntegralL2 FilteredItoIntegralCLM
open AdaptedContinuousSpace ContinuousItoElementary ContinuousItoConsistency
open ContinuousItoStoppingGrid ContinuousItoStopping ContinuousItoStoppedMartingale
open ContinuousItoStoppedIsometry ContinuousItoHalfLineStopping ClockStoppedIntegral

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ}
  [IsFilteredPreBrownian B F μ]

/-- Norm-square Lebesgue integration agrees with the real second moment
whenever the latter is supplied by actual L² membership. -/
theorem lintegral_norm_sq_eq_ofReal_integral {X : Ω → ℝ} (hX : MemLp X 2 μ) :
    (∫⁻ ω, (‖X ω‖₊ : ℝ≥0∞) ^ 2 ∂μ) = ENNReal.ofReal (∫ ω, X ω ^ 2 ∂μ) := by
  have he := ofReal_integral_eq_lintegral_ofReal hX.integrable_sq
    (ae_of_all μ fun ω => sq_nonneg (X ω))
  have hp : (fun ω => ENNReal.ofReal (X ω ^ 2)) =
      fun ω => (‖X ω‖₊ : ℝ≥0∞) ^ 2 := by
    funext ω
    have hx : X ω ^ 2 = ((‖X ω‖₊ ^ 2 : ℝ≥0) : ℝ) := by
      simp [sq_abs]
    rw [hx, ENNReal.ofReal_coe_nnreal, ENNReal.coe_pow]
  rw [hp] at he
  exact he.symm

/-- Uniform second moments give a sufficient first-moment bound without
introducing a square-root parameter. -/
theorem eLpNorm_one_le_secondMoment_add_one {X : Ω → ℝ} {u : ℝ≥0}
    (hu : (∫⁻ ω, (‖X ω‖₊ : ℝ≥0∞) ^ 2 ∂μ) ≤ u) :
    eLpNorm X 1 μ ≤ ((u + 1 : ℝ≥0) : ℝ≥0∞) := by
  rw [eLpNorm_one_eq_lintegral_enorm]
  calc
    _ ≤ ∫⁻ ω, (‖X ω‖₊ : ℝ≥0∞) ^ 2 + 1 ∂μ := by
      apply lintegral_mono
      intro ω
      have hnn : ‖X ω‖₊ ≤ ‖X ω‖₊ ^ 2 + 1 := by
        exact_mod_cast (show ‖X ω‖ ≤ ‖X ω‖ ^ 2 + 1 by
          nlinarith [sq_nonneg (‖X ω‖ - 1)])
      show ‖X ω‖ₑ ≤ (‖X ω‖₊ : ℝ≥0∞) ^ 2 + 1
      calc ‖X ω‖ₑ = (‖X ω‖₊ : ℝ≥0∞) := rfl
        _ ≤ ((‖X ω‖₊ ^ 2 + 1 : ℝ≥0) : ℝ≥0∞) := ENNReal.coe_le_coe.2 hnn
        _ = (‖X ω‖₊ : ℝ≥0∞) ^ 2 + 1 := by push_cast; ring
    _ = (∫⁻ ω, (‖X ω‖₊ : ℝ≥0∞) ^ 2 ∂μ) + ∫⁻ _ : Ω, (1 : ℝ≥0∞) ∂μ :=
      lintegral_add_right _ measurable_const
    _ ≤ _ := by simpa using add_le_add_right hu 1

/-- Every slice of the actual half-line construction lies in L². -/
theorem halfLineIto_memLp
    (hB : ∀ ω, Continuous (fun t => B t ω)) (hBmeas : ∀ t, Measurable (B t))
    (H : ℝ≥0 × Ω → ℝ)
    (hH : ∀ n : ℕ, MemLp H 2
      (trimMeasure_T (𝓖 := F) (μ := μ) (n : ℝ≥0) hBmeas)) (t : ℝ≥0) :
    MemLp (halfLineIto hB hBmeas H hH t) 2 μ := by
  have he := representative_eval_ae (coveringHorizon t) hB hBmeas
    (integerIntegrand hBmeas H hH (coveringHorizon t))
    ⟨t, zero_le, (lt_coveringHorizon t).le⟩
  exact (Lp.memLp _).ae_eq he.symm

/-- The finite-window second moment is exactly its zero-to-time energy. -/
theorem continuousIto_secondMoment_eq (T : ℝ≥0)
    (hB : ∀ ω, Continuous (fun t => B t ω)) (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas))
    (t : Set.Icc (0 : ℝ≥0) T) :
    (∫ ω, (representative (continuousIto T hB hBmeas φ) ω t) ^ 2 ∂μ) =
      ∫ z in Set.Ioc 0 t.val ×ˢ (Set.univ : Set Ω), (φ z) ^ 2
        ∂(trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas) := by
  calc
    _ = ∫ ω, (representative (continuousIto T hB hBmeas φ) ω t -
        representative (continuousIto T hB hBmeas φ) ω
          (⟨0, zero_le, zero_le⟩ : Set.Icc (0 : ℝ≥0) T)) ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [continuousIto_zero_ae T hB hBmeas φ] with ω hω
      simp only [hω, Pi.zero_apply, sub_zero]
    _ = _ := continuousIto_increment_moment T hB hBmeas φ
      ⟨0, zero_le, zero_le⟩ t t.property.1

/-- Increment isometry telescopes second moments in the same finite window. -/
theorem continuousIto_increment_secondMoment_sub (T : ℝ≥0)
    (hB : ∀ ω, Continuous (fun t => B t ω)) (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas))
    (s t : Set.Icc (0 : ℝ≥0) T) (hst : s ≤ t) :
    (∫ ω, (representative (continuousIto T hB hBmeas φ) ω t -
        representative (continuousIto T hB hBmeas φ) ω s) ^ 2 ∂μ) =
      (∫ ω, (representative (continuousIto T hB hBmeas φ) ω t) ^ 2 ∂μ) -
        ∫ ω, (representative (continuousIto T hB hBmeas φ) ω s) ^ 2 ∂μ := by
  rw [continuousIto_increment_moment T hB hBmeas φ s t hst,
    continuousIto_secondMoment_eq T hB hBmeas φ t,
    continuousIto_secondMoment_eq T hB hBmeas φ s]
  have hsub : Set.Ioc 0 s.val ×ˢ (Set.univ : Set Ω) ⊆
      Set.Ioc 0 t.val ×ˢ (Set.univ : Set Ω) :=
    Set.prod_mono (Set.Ioc_subset_Ioc le_rfl hst) subset_rfl
  have hdiff : (Set.Ioc 0 t.val ×ˢ (Set.univ : Set Ω)) \
      (Set.Ioc 0 s.val ×ˢ (Set.univ : Set Ω)) =
      Set.Ioc s.val t.val ×ˢ (Set.univ : Set Ω) := by
    ext z
    constructor
    · rintro ⟨hz, hnot⟩
      have hsz : s.val < z.1 := by
        apply lt_of_not_ge
        intro hle
        exact hnot ⟨⟨hz.1.1, hle⟩, Set.mem_univ _⟩
      exact ⟨⟨hsz, hz.1.2⟩, Set.mem_univ _⟩
    · rintro ⟨hz, _⟩
      exact ⟨⟨⟨lt_of_le_of_lt zero_le hz.1, hz.2⟩, Set.mem_univ _⟩,
        fun h => (not_lt_of_ge h.1.2) hz.1⟩
  rw [← hdiff]
  exact setIntegral_diff
    (measurableSet_predictable_Ioc_prod (𝓕 := F) 0 s.val MeasurableSet.univ)
    (Lp.memLp φ).integrable_sq.integrableOn hsub

/-- The same telescoping identity holds for the actual patched half-line
integral, using a common integer window for both observation times. -/
theorem halfLineIto_increment_secondMoment_sub
    (hB : ∀ ω, Continuous (fun t => B t ω)) (hBmeas : ∀ t, Measurable (B t))
    (H : ℝ≥0 × Ω → ℝ)
    (hH : ∀ n : ℕ, MemLp H 2
      (trimMeasure_T (𝓖 := F) (μ := μ) (n : ℝ≥0) hBmeas))
    (s t : ℝ≥0) (hst : s ≤ t) :
    (∫ ω, (halfLineIto hB hBmeas H hH t ω - halfLineIto hB hBmeas H hH s ω) ^ 2 ∂μ) =
      (∫ ω, (halfLineIto hB hBmeas H hH t ω) ^ 2 ∂μ) -
        ∫ ω, (halfLineIto hB hBmeas H hH s ω) ^ 2 ∂μ := by
  let n := coveringHorizon t
  let ss : Set.Icc (0 : ℝ≥0) (n : ℝ≥0) :=
    ⟨s, zero_le, hst.trans (lt_coveringHorizon t).le⟩
  let tt : Set.Icc (0 : ℝ≥0) (n : ℝ≥0) := ⟨t, zero_le, (lt_coveringHorizon t).le⟩
  have he := halfLineIto_integer_agreement hB hBmeas H hH
  have hs := he.mono fun ω hω => hω n ss
  have ht := he.mono fun ω hω => hω n tt
  have hinc : (∫ ω, (halfLineIto hB hBmeas H hH t ω -
      halfLineIto hB hBmeas H hH s ω) ^ 2 ∂μ) =
      ∫ ω, (integerItoPath hB hBmeas H hH n ω tt -
        integerItoPath hB hBmeas H hH n ω ss) ^ 2 ∂μ := by
    apply integral_congr_ae
    filter_upwards [hs, ht] with ω hsω htω
    rw [hsω, htω]
  have hs_sq := integral_congr_ae (hs.mono fun _ h => congrArg (fun x : ℝ => x ^ 2) h)
  have ht_sq := integral_congr_ae (ht.mono fun _ h => congrArg (fun x : ℝ => x ^ 2) h)
  rw [hinc, hs_sq, ht_sq]
  exact continuousIto_increment_secondMoment_sub n hB hBmeas
    (integerIntegrand hBmeas H hH n) ss tt hst

/-- Actual half-line integrals with bounded second moments have finite total
consecutive increment energy; the isometry is proved above, not passed as data. -/
theorem halfLineIto_increment_energy_ne_top
    (hB : ∀ ω, Continuous (fun t => B t ω)) (hBmeas : ∀ t, Measurable (B t))
    (H : ℝ≥0 × Ω → ℝ)
    (hH : ∀ n : ℕ, MemLp H 2
      (trimMeasure_T (𝓖 := F) (μ := μ) (n : ℝ≥0) hBmeas)) {u : ℝ≥0}
    (hcap : ∀ n : ℕ, (∫⁻ ω,
      (‖halfLineIto hB hBmeas H hH n ω‖₊ : ℝ≥0∞) ^ 2 ∂μ) ≤ u) :
    (∑' n : ℕ, ∫⁻ ω,
      (‖halfLineIto hB hBmeas H hH ((n : ℝ≥0) + 1) ω -
        halfLineIto hB hBmeas H hH n ω‖₊ : ℝ≥0∞) ^ 2 ∂μ) ≠ ⊤ := by
  let M := halfLineIto hB hBmeas H hH
  let e : ℕ → ℝ≥0 := fun n => ⟨∫ ω, (M n ω) ^ 2 ∂μ,
    integral_nonneg fun ω => sq_nonneg (M n ω)⟩
  have he : Monotone e := by
    intro n m hnm
    have hd := halfLineIto_increment_secondMoment_sub hB hBmeas H hH n m
      (show (n : ℝ≥0) ≤ m by exact_mod_cast hnm)
    have hn := integral_nonneg (μ := μ) (f := fun ω => (M m ω - M n ω) ^ 2) (fun ω => sq_nonneg (M m ω - M n ω))
    change (∫ ω, (M n ω) ^ 2 ∂μ) ≤ ∫ ω, (M m ω) ^ 2 ∂μ
    dsimp [M] at hn
    rw [hd] at hn
    linarith
  have hbound : ∀ n, e n ≤ u := by
    intro n
    have hc := hcap n
    rw [lintegral_norm_sq_eq_ofReal_integral (halfLineIto_memLp hB hBmeas H hH n)] at hc
    change ENNReal.ofReal (e n : ℝ) ≤ (u : ℝ≥0∞) at hc
    simpa only [ENNReal.ofReal_coe_nnreal, ENNReal.coe_le_coe] using hc
  apply increment_energy_ne_top_of_clock e he hbound
  intro n
  rw [lintegral_norm_sq_eq_ofReal_integral
    (X := fun ω => halfLineIto hB hBmeas H hH ((n : ℝ≥0) + 1) ω - halfLineIto hB hBmeas H hH n ω)
    ((halfLineIto_memLp hB hBmeas H hH ((n : ℝ≥0) + 1)).sub
      (halfLineIto_memLp hB hBmeas H hH n)),
    halfLineIto_increment_secondMoment_sub hB hBmeas H hH n ((n : ℝ≥0) + 1)
      (le_add_of_nonneg_right zero_le)]
  have hcast : ((n + 1 : ℕ) : ℝ≥0) = (n : ℝ≥0) + 1 := by push_cast; rfl
  rw [← hcast]
  change ENNReal.ofReal ((e (n + 1) : ℝ) - (e n : ℝ)) = _
  rw [← NNReal.coe_sub (he (Nat.le_succ n)), ENNReal.ofReal_coe_nnreal]

/-- A reusable global second-moment cap for the actual inverse-clock-stopped
raw half-line integral. It requires no filtration completeness premise. -/
theorem clockStoppedHalfLineIto_secondMoment_le
    (hB : ∀ ω, Continuous (fun t => B t ω)) (hBmeas : ∀ t, Measurable (B t))
    [F.IsRightContinuous] (A : ℝ≥0 → Ω → ℝ≥0)
    (ha : Adapted F A) (hc : ∀ ω, Continuous (fun t => A t ω))
    (hm : ∀ ω, Monotone (fun t => A t ω)) (hz : ∀ ω, A 0 ω = 0)
    (H : ℝ≥0 × Ω → ℝ) (hHsm : StronglyMeasurable[F.predictable] H)
    (hH : ∀ n : ℕ, MemLp H 2
      (trimMeasure_T (𝓖 := F) (μ := μ) (n : ℝ≥0) hBmeas))
    (hclock : ∀ ω r, (∫ v in Set.Ioc 0 r, H (v, ω) ^ 2 ∂timeMeasure) = (A r ω : ℝ))
    (u t : ℝ≥0) :
    (∫⁻ ω, (‖halfLineIto hB hBmeas (stoppedRawIntegrand (clockInverseTime A u) H)
      (stoppedRawIntegrand_memLp hBmeas (clockInverseTime_isStoppingTime ha hc hm hz u) H hH)
      t ω‖₊ : ℝ≥0∞) ^ 2 ∂μ) ≤ u := by
  let n := coveringHorizon t
  let tt : Set.Icc (0 : ℝ≥0) (n : ℝ≥0) := ⟨t, zero_le, (lt_coveringHorizon t).le⟩
  have hτ := clockInverseTime_isStoppingTime ha hc hm hz u
  have heq : halfLineIto hB hBmeas (stoppedRawIntegrand (clockInverseTime A u) H)
      (stoppedRawIntegrand_memLp hBmeas hτ H hH) t =ᵐ[μ]
      stoppedContinuousIto n hB hBmeas (clockInverseTime A u) ((hH n).toLp H) tt := by
    filter_upwards [halfLineIto_integer_agreement hB hBmeas
      (stoppedRawIntegrand (clockInverseTime A u) H)
      (stoppedRawIntegrand_memLp hBmeas hτ H hH),
      integerItoPath_stoppedRaw hB hBmeas hτ H hH] with ω hi hs
    exact (hi n tt).trans (hs n tt)
  calc
    _ = ∫⁻ ω, (‖stoppedContinuousIto n hB hBmeas (clockInverseTime A u)
        ((hH n).toLp H) tt ω‖₊ : ℝ≥0∞) ^ 2 ∂μ :=
      lintegral_congr_ae (heq.mono fun _ h => congrArg (fun x : ℝ => (‖x‖₊ : ℝ≥0∞) ^ 2) h)
    _ ≤ u := clockStoppedContinuousIto_secondMoment_le n hB hBmeas A ha hc hm hz
      H hHsm (hH n) hclock u tt

/-- The actual half-line Itô integral converges whenever its accumulated raw
energy clock has finite terminal value. Random stopping, martingale production,
first-moment bounds, and increment isometry are all discharged constructions. -/
theorem ae_finite_clock_halfLineIto_convergence
    (hB : ∀ ω, Continuous (fun t => B t ω)) (hBmeas : ∀ t, Measurable (B t))
    [F.IsRightContinuous]
    (hnull : ∀ t E, MeasurableSet E → μ E = 0 → MeasurableSet[F t] E)
    (A : ℝ≥0 → Ω → ℝ≥0) (ha : Adapted F A)
    (hc : ∀ ω, Continuous (fun t => A t ω))
    (hm : ∀ ω, Monotone (fun t => A t ω)) (hz : ∀ ω, A 0 ω = 0)
    (H : ℝ≥0 × Ω → ℝ) (hHsm : StronglyMeasurable[F.predictable] H)
    (hH : ∀ n : ℕ, MemLp H 2
      (trimMeasure_T (𝓖 := F) (μ := μ) (n : ℝ≥0) hBmeas))
    (hclock : ∀ ω r, (∫ v in Set.Ioc 0 r, H (v, ω) ^ 2 ∂timeMeasure) = (A r ω : ℝ)) :
    Measurable (knightTerminalValue (halfLineIto hB hBmeas H hH)) ∧
      ∀ᵐ ω ∂μ, terminalClock (fun t => A t ω) ≠ ⊤ →
        Tendsto (fun t => halfLineIto hB hBmeas H hH t ω) atTop
          (𝓝 (knightTerminalValue (halfLineIto hB hBmeas H hH) ω)) := by
  refine ⟨measurable_knightTerminalValue
    (fun n => (halfLineIto_stronglyMeasurable hB hBmeas H hH n).measurable), ?_⟩
  apply ae_tendsto_on_finite_terminalClock_of_stopped
  intro n
  let τ := clockInverseTime A (n : ℝ≥0)
  have hτ := clockInverseTime_isStoppingTime ha hc hm hz (n : ℝ≥0)
  let K := stoppedRawIntegrand τ H
  let hK := stoppedRawIntegrand_memLp hBmeas hτ H hH
  have hcap : ∀ t : ℝ≥0,
      (∫⁻ ω, (‖halfLineIto hB hBmeas K hK t ω‖₊ : ℝ≥0∞) ^ 2 ∂μ) ≤ (n : ℝ≥0) :=
    clockStoppedHalfLineIto_secondMoment_le hB hBmeas A ha hc hm hz H hHsm hH hclock n
  have henergy := halfLineIto_increment_energy_ne_top hB hBmeas K hK
    (fun k => hcap k)
  have hfirst : ∀ k : ℕ, eLpNorm (halfLineIto hB hBmeas K hK k) 1 μ ≤
      ((n : ℝ≥0) + 1 : ℝ≥0) := fun k =>
    eLpNorm_one_le_secondMoment_add_one (hcap k)
  have hlim := ae_tendsto_knightTerminalValue_of_increment_energy
    (halfLineIto_stoppedRaw_isMartingale hB hBmeas hτ H hH hnull)
    (halfLineIto_ae_continuous hB hBmeas K hK) hfirst henergy
  filter_upwards [hlim, halfLineIto_stoppedRaw hB hBmeas hτ H hH] with ω hl he
  refine ⟨knightTerminalValue (halfLineIto hB hBmeas K hK) ω, ?_⟩
  have hfun : clockStoppedPath (fun t => halfLineIto hB hBmeas H hH t ω)
      (fun t => A t ω) n = fun t => halfLineIto hB hBmeas K hK t ω := by
    funext t
    rw [clockStoppedPath, ← cappedStopTime_clockInverseTime t A n ω]
    exact (he t).symm
  rw [hfun]
  exact hl

end Ripple.Stochastic.KnightIntegralConvergence
