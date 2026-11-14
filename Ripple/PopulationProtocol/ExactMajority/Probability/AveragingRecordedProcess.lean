-- Ripple/PopulationProtocol/ExactMajority/Probability/AveragingRecordedProcess.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingRecordedExpectation

/-!
# Adapted bounded sums of actual sampled increments

The construction uses the recorded prefix and the next draw. Its filtration is
shifted by the fixed observed start. Conditional means are computed under the
ordinary recorded continuation, so no future-success conditioning is used.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.AveragingRecordedProcess

open TimeTheorem PairLog AveragingRecordedExpectation

variable {L K : ℕ}

abbrev IncrementFamily (L K s : ℕ) :=
  (t : ℕ) → ((i : Finset.Iic (s + t)) → Draw L K) → Draw L K → ℝ

def recordedIncrement (s : ℕ) (F : IncrementFamily L K s)
    (t : ℕ) : Ω L K → ℝ :=
  recordedNext (s + t) (F t)

def recordedSum (s : ℕ) (F : IncrementFamily L K s)
    (t : ℕ) (ω : Ω L K) : ℝ :=
  ∑ i ∈ Finset.range t, recordedIncrement s F i ω

theorem recordedSum_zero (s : ℕ) (F : IncrementFamily L K s) :
    recordedSum s F 0 = 0 := by
  funext ω
  simp [recordedSum]

theorem recordedSum_succ (s : ℕ) (F : IncrementFamily L K s) (t : ℕ) :
    recordedSum s F (t + 1) = recordedSum s F t + recordedIncrement s F t := by
  funext ω
  simp only [recordedSum, Finset.sum_range_succ, Pi.add_apply]

theorem recordedIncrement_stronglyMeasurable (s : ℕ)
    (F : IncrementFamily L K s) (t : ℕ) :
    StronglyMeasurable[shiftedPairLog L K s (t + 1)] (recordedIncrement s F t) := by
  simpa only [recordedIncrement, shiftedPairLog, Nat.add_assoc] using
    (recordedNext_stronglyMeasurable (s + t) (F t))

theorem recordedSum_stronglyAdapted (s : ℕ) (F : IncrementFamily L K s) :
    StronglyAdapted (shiftedPairLog L K s) (recordedSum s F) := by
  intro t
  induction t with
  | zero =>
      rw [recordedSum_zero]
      exact stronglyMeasurable_const
  | succ t ih =>
      rw [recordedSum_succ]
      exact (ih.mono ((shiftedPairLog L K s).mono (Nat.le_succ t))).add
        (recordedIncrement_stronglyMeasurable s F t)

theorem recordedIncrement_integrable (μ : Measure (Ω L K)) [IsFiniteMeasure μ]
    (s : ℕ) (F : IncrementFamily L K s) (b : ℝ)
    (hbound : ∀ t q d, |F t q d| ≤ b) (t : ℕ) :
    Integrable (recordedIncrement s F t) μ :=
  recordedNext_integrable μ (s + t) (F t) b (hbound t)

theorem recordedSum_integrable (μ : Measure (Ω L K)) [IsFiniteMeasure μ]
    (s : ℕ) (F : IncrementFamily L K s) (b : ℝ)
    (hbound : ∀ t q d, |F t q d| ≤ b) (t : ℕ) :
    Integrable (recordedSum s F t) μ := by
  induction t with
  | zero =>
      rw [recordedSum_zero]
      exact integrable_const (0 : ℝ)
  | succ t ih =>
      rw [recordedSum_succ]
      exact ih.add (recordedIncrement_integrable μ s F b hbound t)

theorem recordedSum_increment_bound (s : ℕ) (F : IncrementFamily L K s)
    (b : ℝ) (hbound : ∀ t q d, |F t q d| ≤ b)
    (t : ℕ) (ω : Ω L K) :
    |recordedSum s F (t + 1) ω - recordedSum s F t ω| ≤ b := by
  rw [recordedSum_succ]
  simp only [Pi.add_apply, add_sub_cancel_left]
  exact hbound t _ _

/-- The conditional drift of the sampled increment is obtained from its
ordinary next-draw integral, including every gate-exit draw. -/
theorem recordedIncrement_condExp_le (init : Cfg L K)
    (s : ℕ) (p : (i : Finset.Iic s) → Draw L K)
    (F : IncrementFamily L K s) (b : ℝ)
    (hbound : ∀ t q d, |F t q d| ≤ b)
    (hmean : ∀ t q, (∫ d, F t q d ∂pairKernel init (s + t) q) ≤ 0)
    (t : ℕ) :
    (recordedFuture init s p)[recordedIncrement s F t | shiftedPairLog L K s t]
      ≤ᵐ[recordedFuture init s p] (0 : Ω L K → ℝ) := by
  have hce := recordedNext_condExp init s (s + t) (Nat.le_add_right s t)
    p (F t) b (hbound t)
  filter_upwards [hce] with ω hω
  exact hω.le.trans (hmean t _)

theorem recordedSum_supermartingale (init : Cfg L K)
    (s : ℕ) (p : (i : Finset.Iic s) → Draw L K)
    (F : IncrementFamily L K s) (b : ℝ)
    (hbound : ∀ t q d, |F t q d| ≤ b)
    (hmean : ∀ t q, (∫ d, F t q d ∂pairKernel init (s + t) q) ≤ 0) :
    Supermartingale (recordedSum s F) (shiftedPairLog L K s)
      (recordedFuture init s p) := by
  let μ := recordedFuture init s p
  have hadapt := recordedSum_stronglyAdapted s F
  have hint := recordedSum_integrable μ s F b hbound
  apply supermartingale_nat hadapt hint
  intro t
  rw [recordedSum_succ]
  have hcur : μ[recordedSum s F t | shiftedPairLog L K s t] =
      recordedSum s F t :=
    condExp_of_stronglyMeasurable ((shiftedPairLog L K s).le t)
      (hadapt t) (hint t)
  filter_upwards
    [condExp_add (hint t)
      (recordedIncrement_integrable μ s F b hbound t) (shiftedPairLog L K s t),
      recordedIncrement_condExp_le init s p F b hbound hmean t]
    with ω hadd hinc
  have heq :
      μ[recordedSum s F t + recordedIncrement s F t | shiftedPairLog L K s t] ω =
        recordedSum s F t ω +
          μ[recordedIncrement s F t | shiftedPairLog L K s t] ω := by
    simpa only [hcur, Pi.add_apply] using hadd
  rw [heq]
  change _ + _ ≤ _
  have hzero : μ[recordedIncrement s F t | shiftedPairLog L K s t] ω ≤ 0 := hinc
  linarith

theorem recordedSum_maximal_tail (init : Cfg L K)
    (s : ℕ) (p : (i : Finset.Iic s) → Draw L K)
    (F : IncrementFamily L K s) (b : ℝ) (hb : 0 ≤ b)
    (hbound : ∀ t q d, |F t q d| ≤ b)
    (hmean : ∀ t q, (∫ d, F t q d ∂pairKernel init (s + t) q) ≤ 0)
    (u : ℝ) (hu : 0 < u) (N : ℕ) :
    Ripple.Probability.prob (recordedFuture init s p)
      {ω | ∃ t, t ≤ N ∧ u ≤ recordedSum s F t ω - recordedSum s F 0 ω} ≤
      Real.exp (-(u ^ 2) / (2 * ((N : ℝ) * b ^ 2 + 2 * b * u / 3))) :=
  PhaseThreeScalar.supermartingale_max_tail_of_bounded_increments
    (recordedSum_supermartingale init s p F b hbound hmean) hb
    (fun t => ae_of_all _ fun ω => recordedSum_increment_bound s F b hbound t ω)
    hu N

end Ripple.PopulationProtocol.ExactMajority.AveragingRecordedProcess

end
