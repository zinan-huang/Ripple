import Ripple.Kurtz.StrongApprox.KurtzKnightIntegral
import Ripple.Stochastic.FiniteChannelExponentialLimit

/-!
# Regularity of the actual Kurtz energy clock

The clock is the installed rate integral, with the prescribed population-size
factor and nonnegative-real conversion. Adaptation follows from elementary
adapted bracket sums converging to its actual energy integral. Continuity and
monotonicity follow from the ordinary primitive of the nonnegative rate.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace Ripple.Kurtz.StrongApprox

open Ripple.Stochastic
open ContinuousAdaptedIntegrand BoundedStochasticExponential
open FiniteChannelExponentialLimit

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}

/-- The nonnegative-time rate integral is exactly the real interval primitive
of the same state path extended through `Real.toNNReal`. -/
theorem kurtzRateClock_eq_intervalIntegral (N : ℕ)
    (f : (Fin d → ℝ) → ℝ) (Z : ℝ≥0 → Ω → Fin d → ℝ)
    (t : ℝ≥0) (ω : Ω) :
    kurtzRateClock N f Z t ω = (N : ℝ) *
      ∫ s in (0 : ℝ)..(t : ℝ), f (Z s.toNNReal ω) := by
  unfold kurtzRateClock
  have h := KMTTransfer.setIntegral_timeMeasure_Ioc
    (fun s : ℝ => f (Z s.toNNReal ω)) t
  simpa only [Real.toNNReal_coe] using congrArg (fun x : ℝ => (N : ℝ) * x) h

/-- Pathwise continuity of the actual nonnegative energy clock. -/
theorem continuous_kurtzRateClockNN (N : ℕ) {f : (Fin d → ℝ) → ℝ}
    (hf : Continuous f) {Z : ℝ≥0 → Ω → Fin d → ℝ}
    (hc : ∀ ω, Continuous (fun t => Z t ω)) (ω : Ω) :
    Continuous (fun t => kurtzRateClockNN N f Z t ω) := by
  let r : ℝ → ℝ := fun s => f (Z s.toNNReal ω)
  have hr : Continuous r := hf.comp ((hc ω).comp continuous_real_toNNReal)
  have hp : Continuous (fun t : ℝ => ∫ s in (0 : ℝ)..t, r s) :=
    intervalIntegral.continuous_primitive (fun a b => hr.intervalIntegrable a b) 0
  have hm : Continuous (fun t : ℝ≥0 =>
      (N : ℝ) * ∫ s in (0 : ℝ)..(t : ℝ), r s) :=
    continuous_const.mul (hp.comp NNReal.continuous_coe)
  have heq : (fun t => kurtzRateClockNN N f Z t ω) =
      fun t : ℝ≥0 => ((N : ℝ) * ∫ s in (0 : ℝ)..(t : ℝ), r s).toNNReal := by
    funext t
    rw [kurtzRateClockNN, kurtzRateClock_eq_intervalIntegral]
  rw [heq]
  exact continuous_real_toNNReal.comp hm

/-- A nonnegative continuous rate makes the actual clock nondecreasing,
including channels whose rates vanish on entire intervals. -/
theorem monotone_kurtzRateClockNN (N : ℕ) {f : (Fin d → ℝ) → ℝ}
    (hf : Continuous f) (hfzero : ∀ x, 0 ≤ f x)
    {Z : ℝ≥0 → Ω → Fin d → ℝ}
    (hc : ∀ ω, Continuous (fun t => Z t ω)) (ω : Ω) :
    Monotone (fun t => kurtzRateClockNN N f Z t ω) := by
  let r : ℝ → ℝ := fun s => f (Z s.toNNReal ω)
  have hr : Continuous r := hf.comp ((hc ω).comp continuous_real_toNNReal)
  intro s t hst
  have hs : IntervalIntegrable r volume 0 (s : ℝ) := hr.intervalIntegrable _ _
  have ht : IntervalIntegrable r volume (s : ℝ) (t : ℝ) := hr.intervalIntegrable _ _
  have hadd := intervalIntegral.integral_add_adjacent_intervals hs ht
  have hnonneg : 0 ≤ ∫ u in (s : ℝ)..(t : ℝ), r u :=
    intervalIntegral.integral_nonneg (by exact_mod_cast hst) (fun u _ => hfzero _)
  have hle : (∫ u in (0 : ℝ)..(s : ℝ), r u) ≤
      ∫ u in (0 : ℝ)..(t : ℝ), r u := by linarith
  apply Real.toNNReal_le_toNNReal
  rw [kurtzRateClock_eq_intervalIntegral, kurtzRateClock_eq_intervalIntegral]
  exact mul_le_mul_of_nonneg_left hle (Nat.cast_nonneg N)

/-- The clock starts at zero by its actual integral formula. -/
@[simp] theorem kurtzRateClockNN_zero (N : ℕ) (f : (Fin d → ℝ) → ℝ)
    (Z : ℝ≥0 → Ω → Fin d → ℝ) (ω : Ω) :
    kurtzRateClockNN N f Z 0 ω = 0 := by
  simp [kurtzRateClockNN, kurtzRateClock]

variable {P : Measure Ω} [IsProbabilityMeasure P]
    {F : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ}

/-- Adaptation of the rate clock is constructed from the same deterministic
sampled brackets used for the stochastic integral. The limit is its actual
energy integral, so no clock-adaptation premise is carried. -/
theorem adapted_kurtzRateClockNN
    (hBmeas : ∀ t, Measurable (B t))
    (N : ℕ) {f : (Fin d → ℝ) → ℝ} (hf : Continuous f)
    (hfzero : ∀ x, 0 ≤ f x) {eps : ℝ} (hb : ∀ x, f x ≤ eps)
    {Z : ℝ≥0 → Ω → Fin d → ℝ} (ha : Adapted F Z)
    (hc : ∀ ω, Continuous (fun t => Z t ω)) :
    Adapted F (kurtzRateClockNN N f Z) := by
  let H := kurtzClockIntegrand N f Z
  let K := Real.sqrt ((N : ℝ) * eps)
  have hHa : ∀ t, Measurable[F t] (H t) := adapted_kurtzClockIntegrand N hf ha
  have hHc : ∀ ω, Continuous (fun t => H t ω) :=
    fun ω => continuous_kurtzClockIntegrand N hf (hc ω)
  have hHb : ∀ t ω, |H t ω| ≤ K := by
    intro t ω
    simpa only [Real.norm_eq_abs] using norm_kurtzClockIntegrand_le N hb Z t ω
  intro t
  let s : ℕ → ℕ → ℝ≥0 := fun n => samplePartition (1 / ((n : ℝ≥0) + 1)) t
  let Q : ℕ → Ω → ℝ := fun n => simpleBracket (s n)
    (fun i ω => H (s n i) ω) (sampleCells (1 / ((n : ℝ≥0) + 1)) t) t
  have hQ : ∀ n, Measurable[F t] (Q n) := by
    intro n
    exact (simpleBracket_stronglyAdapted F (s n)
      (samplePartition_mono _ _) (fun i ω => H (s n i) ω)
      (fun i => (hHa _).stronglyMeasurable)
      (sampleCells (1 / ((n : ℝ≥0) + 1)) t) t).measurable
  have hlim : ∀ ω, Tendsto (fun n => Q n ω) atTop
      (𝓝 (kurtzRateClock N f Z t ω)) := by
    intro ω
    have h := sampleBracket_tendsto t hBmeas H hHa hHc
      (Real.sqrt_nonneg _) hHb (⟨t, zero_le, le_rfl⟩ : Icc (0 : ℝ≥0) t) ω
    simpa only [H, Q, s, integral_kurtzClockIntegrand_sq N hfzero] using h
  have heq : (fun ω => kurtzRateClock N f Z t ω) =
      fun ω => limsup (fun n => Q n ω) atTop := by
    funext ω
    exact (hlim ω).limsup_eq.symm
  have hclockm : Measurable[F t] (fun ω => kurtzRateClock N f Z t ω) := by
    rw [heq]
    exact Measurable.limsup hQ
  exact continuous_real_toNNReal.measurable.comp hclockm

/-- All clock regularity inputs to the inverse-clock stopping construction,
for the actual bounded nonnegative Kurtz rate. -/
theorem kurtzRateClockNN_regularity
    (hBmeas : ∀ t, Measurable (B t))
    (N : ℕ) {f : (Fin d → ℝ) → ℝ} (hf : Continuous f)
    (hfzero : ∀ x, 0 ≤ f x) {eps : ℝ} (hb : ∀ x, f x ≤ eps)
    {Z : ℝ≥0 → Ω → Fin d → ℝ} (ha : Adapted F Z)
    (hc : ∀ ω, Continuous (fun t => Z t ω)) :
    Adapted F (kurtzRateClockNN N f Z) ∧
    (∀ ω, Continuous (fun t => kurtzRateClockNN N f Z t ω)) ∧
    (∀ ω, Monotone (fun t => kurtzRateClockNN N f Z t ω)) ∧
    (∀ ω, kurtzRateClockNN N f Z 0 ω = 0) :=
  ⟨adapted_kurtzRateClockNN hBmeas N hf hfzero hb ha hc,
    continuous_kurtzRateClockNN N hf hc,
    monotone_kurtzRateClockNN N hf hfzero hc,
    kurtzRateClockNN_zero N f Z⟩

end Ripple.Kurtz.StrongApprox
