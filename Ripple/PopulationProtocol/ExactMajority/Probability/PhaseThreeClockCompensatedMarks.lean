-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockCompensatedMarks.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockRisingOpportunity

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockCompensatedMarks

open PhaseThreeScalar PhaseThreeClockOpportunityProcess PhaseThreeClockRisingOpportunity

variable {Ω : Type*} {m₀ : MeasurableSpace Ω}
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℕ m₀}

structure CompensatedMarkData (μ : Measure Ω) (ℱ : Filtration ℕ m₀) (a : ℕ) where
  order_pos : 1 ≤ a
  markCount : ℕ → Ω → ℝ
  immigration : ℕ → Ω → ℝ
  propagation : ℕ → Ω → ℝ
  opportunity : ℕ → Ω → ℝ
  rate : ℕ → Ω → ℝ
  initialUpper : ℝ
  mark_adapted : ∀ t, StronglyMeasurable[ℱ t] (markCount t)
  immigration_adapted : ∀ t, StronglyMeasurable[ℱ (t + 1)] (immigration t)
  propagation_adapted : ∀ t, StronglyMeasurable[ℱ (t + 1)] (propagation t)
  opportunity_adapted : ∀ t, StronglyMeasurable[ℱ (t + 1)] (opportunity t)
  rate_adapted : ∀ t, StronglyMeasurable[ℱ t] (rate t)
  mark_nonneg : ∀ t ω, 0 ≤ markCount t ω
  initial_bound : ∀ ω, markCount 0 ω ≤ initialUpper
  rate_nonneg : ∀ t ω, 0 ≤ rate t ω
  immigration_bernoulli : ∀ t ω, immigration t ω = 0 ∨ immigration t ω = 1
  propagation_bernoulli : ∀ t ω, propagation t ω = 0 ∨ propagation t ω = 1
  opportunity_bernoulli : ∀ t ω, opportunity t ω = 0 ∨ opportunity t ω = 1
  propagation_le_opportunity : ∀ t ω, propagation t ω ≤ opportunity t ω
  conditional_propagation : ∀ t, ∀ᵐ ω ∂μ,
    (μ[propagation t | ℱ t]) ω ≤
      (μ[opportunity t | ℱ t]) ω * rate t ω * markCount t ω

variable {a : ℕ}

def recordedImmigration (d : CompensatedMarkData μ ℱ a) (t : ℕ) (ω : Ω) : ℝ :=
  bernoulliCount d.immigration t ω

@[simp] theorem recordedImmigration_zero (d : CompensatedMarkData μ ℱ a) (ω : Ω) :
    recordedImmigration d 0 ω = 0 := by simp [recordedImmigration, bernoulliCount]

theorem recordedImmigration_succ (d : CompensatedMarkData μ ℱ a) (t : ℕ) (ω : Ω) :
    recordedImmigration d (t + 1) ω =
      recordedImmigration d t ω + d.immigration t ω := by
  simp only [recordedImmigration, bernoulliCount, Finset.sum_range_succ]

theorem recordedImmigration_step_mono (d : CompensatedMarkData μ ℱ a)
    (t : ℕ) (ω : Ω) :
    recordedImmigration d t ω ≤ recordedImmigration d (t + 1) ω := by
  rw [recordedImmigration_succ]
  rcases d.immigration_bernoulli t ω with h | h <;> simp [h]

theorem recordedImmigration_mono (d : CompensatedMarkData μ ℱ a) (ω : Ω) :
    Monotone (fun t => recordedImmigration d t ω) :=
  monotone_nat_of_le_succ (fun t => recordedImmigration_step_mono d t ω)

theorem recordedImmigration_nonneg (d : CompensatedMarkData μ ℱ a)
    (t : ℕ) (ω : Ω) : 0 ≤ recordedImmigration d t ω := by
  simpa only [recordedImmigration_zero] using
    recordedImmigration_mono d ω (show 0 ≤ t from zero_le)

theorem recordedImmigration_stronglyMeasurable (d : CompensatedMarkData μ ℱ a)
    (t : ℕ) : StronglyMeasurable[ℱ t] (recordedImmigration d t) :=
  bernoulliCount_stronglyMeasurable d.immigration_adapted t

open Classical in
def stoppedMarkValue (d : CompensatedMarkData μ ℱ a) : ℕ → Ω → ℝ
  | 0, ω => (a : ℝ) + d.markCount 0 ω
  | t + 1, ω =>
      let v := stoppedMarkValue d t ω
      if recordedImmigration d (t + 1) ω ≤ (a : ℝ) ∧ d.markCount t ω ≤ v
      then v + d.propagation t ω else v

open Classical in
def stoppedPropagation (d : CompensatedMarkData μ ℱ a) (t : ℕ) : Ω → ℝ :=
  fun ω => if recordedImmigration d (t + 1) ω ≤ (a : ℝ) ∧
    d.markCount t ω ≤ stoppedMarkValue d t ω then d.propagation t ω else 0

theorem stoppedMarkValue_succ (d : CompensatedMarkData μ ℱ a) (t : ℕ) (ω : Ω) :
    stoppedMarkValue d (t + 1) ω =
      stoppedMarkValue d t ω + stoppedPropagation d t ω := by
  classical
  simp only [stoppedMarkValue, stoppedPropagation]
  split_ifs <;> simp

theorem stoppedPropagation_zero_one (d : CompensatedMarkData μ ℱ a)
    (t : ℕ) (ω : Ω) :
    stoppedPropagation d t ω = 0 ∨ stoppedPropagation d t ω = 1 := by
  classical
  unfold stoppedPropagation
  split_ifs
  · exact d.propagation_bernoulli t ω
  · exact Or.inl rfl

theorem stoppedPropagation_le (d : CompensatedMarkData μ ℱ a)
    (t : ℕ) (ω : Ω) :
    stoppedPropagation d t ω ≤ d.propagation t ω := by
  classical
  unfold stoppedPropagation
  split_ifs
  · exact le_rfl
  · rcases d.propagation_bernoulli t ω with h | h <;> simp [h]

theorem stoppedMarkValue_bounds (d : CompensatedMarkData μ ℱ a) (t : ℕ) (ω : Ω) :
    (a : ℝ) ≤ stoppedMarkValue d t ω ∧
      stoppedMarkValue d t ω ≤ (a : ℝ) + d.initialUpper + (t : ℝ) := by
  induction t with
  | zero =>
      simp only [stoppedMarkValue, Nat.cast_zero, add_zero]
      constructor
      · linarith [d.mark_nonneg 0 ω]
      · linarith [d.initial_bound ω]
  | succ t ih =>
      rw [stoppedMarkValue_succ, Nat.cast_add, Nat.cast_one]
      rcases stoppedPropagation_zero_one d t ω with h | h <;> rw [h] <;>
        constructor <;> linarith [ih.1, ih.2]

theorem stoppedMarkValue_stronglyMeasurable (d : CompensatedMarkData μ ℱ a) (t : ℕ) :
    StronglyMeasurable[ℱ t] (stoppedMarkValue d t) := by
  classical
  induction t with
  | zero =>
      exact stronglyMeasurable_const.add (d.mark_adapted 0)
  | succ t ih =>
      have hv := ih.mono (ℱ.mono (Nat.le_succ t))
      have hM := (d.mark_adapted t).mono (ℱ.mono (Nat.le_succ t))
      have hI := recordedImmigration_stronglyMeasurable d (t + 1)
      have hg : MeasurableSet[ℱ (t + 1)]
          {ω | recordedImmigration d (t + 1) ω ≤ (a : ℝ) ∧
            d.markCount t ω ≤ stoppedMarkValue d t ω} :=
        (measurableSet_le hI.measurable measurable_const).inter
          (measurableSet_le hM.measurable hv.measurable)
      exact StronglyMeasurable.ite hg (hv.add (d.propagation_adapted t)) hv

theorem stoppedPropagation_stronglyMeasurable (d : CompensatedMarkData μ ℱ a) (t : ℕ) :
    StronglyMeasurable[ℱ (t + 1)] (stoppedPropagation d t) := by
  classical
  have hv := (stoppedMarkValue_stronglyMeasurable d t).mono (ℱ.mono (Nat.le_succ t))
  have hM := (d.mark_adapted t).mono (ℱ.mono (Nat.le_succ t))
  have hI := recordedImmigration_stronglyMeasurable d (t + 1)
  exact StronglyMeasurable.ite
    ((measurableSet_le hI.measurable measurable_const).inter
      (measurableSet_le hM.measurable hv.measurable))
    (d.propagation_adapted t) stronglyMeasurable_const

theorem stoppedMarkValue_freeze_on_breach (d : CompensatedMarkData μ ℱ a)
    (t : ℕ) (ω : Ω) (hbreach : (a : ℝ) < recordedImmigration d (t + 1) ω) :
    stoppedMarkValue d (t + 1) ω = stoppedMarkValue d t ω := by
  classical
  change (if recordedImmigration d (t + 1) ω ≤ (a : ℝ) ∧
    d.markCount t ω ≤ stoppedMarkValue d t ω
    then stoppedMarkValue d t ω + d.propagation t ω else stoppedMarkValue d t ω) =
      stoppedMarkValue d t ω
  exact if_neg (fun h => not_le_of_gt hbreach h.1)

theorem stoppedMarkValue_freeze_after_breach (d : CompensatedMarkData μ ℱ a)
    (t : ℕ) (ω : Ω) (hbreach : (a : ℝ) < recordedImmigration d t ω) :
    stoppedMarkValue d (t + 1) ω = stoppedMarkValue d t ω :=
  stoppedMarkValue_freeze_on_breach d t ω
    (hbreach.trans_le (recordedImmigration_step_mono d t ω))

theorem stoppedPropagation_conditional_rate (d : CompensatedMarkData μ ℱ a) (t : ℕ) :
    μ[stoppedPropagation d t | ℱ t] ≤ᵐ[μ] fun ω =>
      μ[d.opportunity t | ℱ t] ω * d.rate t ω * stoppedMarkValue d t ω := by
  classical
  let A : Set Ω := {ω | d.markCount t ω ≤ stoppedMarkValue d t ω}
  have hA : MeasurableSet[ℱ t] A :=
    measurableSet_le (d.mark_adapted t).measurable
      (stoppedMarkValue_stronglyMeasurable d t).measurable
  have hPi : Integrable (d.propagation t) μ :=
    bernoulli_integrable d.propagation_adapted
      (fun u => ae_of_all _ (d.propagation_bernoulli u)) t
  have hSi : Integrable (stoppedPropagation d t) μ :=
    bernoulli_integrable (stoppedPropagation_stronglyMeasurable d)
      (fun u => ae_of_all _ (stoppedPropagation_zero_one d u)) t
  have hdom : stoppedPropagation d t ≤ᵐ[μ] A.indicator (d.propagation t) := by
    refine ae_of_all _ (fun ω => ?_)
    by_cases hω : ω ∈ A
    · simpa only [Set.indicator_of_mem hω] using stoppedPropagation_le d t ω
    · have hnot : ¬ d.markCount t ω ≤ stoppedMarkValue d t ω := hω
      simp only [stoppedPropagation, hnot, and_false, if_false,
        Set.indicator_of_notMem hω, le_refl]
  have hce := condExp_mono (m := ℱ t) hSi
    (hPi.indicator ((ℱ.le t) _ hA)) hdom
  have hnonneg : ∀ᵐ ω ∂μ, 0 ≤ d.opportunity t ω := ae_of_all _ (fun ω => by
    rcases d.opportunity_bernoulli t ω with h | h <;> simp [h])
  filter_upwards [hce, condExp_indicator hPi hA, d.conditional_propagation t,
    condExp_nonneg (m := ℱ t) hnonneg] with ω hle hind hr hj
  rw [hind] at hle
  have hcoef : 0 ≤ μ[d.opportunity t | ℱ t] ω * d.rate t ω :=
    mul_nonneg hj (d.rate_nonneg t ω)
  have hv : 0 ≤ stoppedMarkValue d t ω :=
    (Nat.cast_nonneg a).trans (stoppedMarkValue_bounds d t ω).1
  by_cases hω : ω ∈ A
  · rw [Set.indicator_of_mem hω] at hle
    exact hle.trans (hr.trans (mul_le_mul_of_nonneg_left hω hcoef))
  · rw [Set.indicator_of_notMem hω] at hle
    exact hle.trans (mul_nonneg hcoef hv)

def compensatedRisingData (d : CompensatedMarkData μ ℱ a) :
    RisingOpportunityData μ ℱ a where
  order_pos := d.order_pos
  value := stoppedMarkValue d
  rate := d.rate
  propagation := stoppedPropagation d
  opportunity := d.opportunity
  upper := fun t => (a : ℝ) + d.initialUpper + (t : ℝ)
  value_adapted := stoppedMarkValue_stronglyMeasurable d
  rate_adapted := d.rate_adapted
  propagation_adapted := stoppedPropagation_stronglyMeasurable d
  opportunity_adapted := d.opportunity_adapted
  value_bounds := stoppedMarkValue_bounds d
  rate_nonneg := d.rate_nonneg
  propagation_bernoulli := stoppedPropagation_zero_one d
  opportunity_bernoulli := d.opportunity_bernoulli
  propagation_le_opportunity := fun t ω =>
    (stoppedPropagation_le d t ω).trans (d.propagation_le_opportunity t ω)
  value_step := fun t => ae_of_all _ (fun ω => (stoppedMarkValue_succ d t ω).le)
  conditional_rate := stoppedPropagation_conditional_rate d

theorem stoppedMarkValue_eq_compensated (d : CompensatedMarkData μ ℱ a)
    (ω : Ω) (N : ℕ) (himm : recordedImmigration d N ω ≤ (a : ℝ))
    (hledger : ∀ t < N, d.markCount (t + 1) ω =
      d.markCount t ω + d.immigration t ω + d.propagation t ω) :
    stoppedMarkValue d N ω = d.markCount N ω + (a : ℝ) - recordedImmigration d N ω := by
  classical
  induction N with
  | zero => simp [stoppedMarkValue, add_comm]
  | succ N ih =>
      have hprev := (recordedImmigration_step_mono d N ω).trans himm
      have hv := ih hprev (fun t ht => hledger t (by omega))
      have hguard : d.markCount N ω ≤ stoppedMarkValue d N ω := by
        rw [hv]
        linarith
      have hstep :
          stoppedMarkValue d (N + 1) ω = stoppedMarkValue d N ω + d.propagation N ω := by
        change (if recordedImmigration d (N + 1) ω ≤ (a : ℝ) ∧
          d.markCount N ω ≤ stoppedMarkValue d N ω then _ else _) = _
        rw [if_pos ⟨himm, hguard⟩]
      rw [hstep, hv, hledger N (Nat.lt_succ_self N), recordedImmigration_succ]
      ring

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockCompensatedMarks

end
