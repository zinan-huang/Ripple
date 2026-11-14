-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockImmigrationOpportunity.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockOpportunityProcess
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockImmigrationOpportunity

open PhaseThreeScalar PhaseThreeClockOpportunityProcess

variable {Ω : Type*} {m₀ : MeasurableSpace Ω}
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℕ m₀}

structure ImmigrationOpportunityData (μ : Measure Ω) (ℱ : Filtration ℕ m₀) where
  rate : ℕ → Ω → ℝ
  immigration : ℕ → Ω → ℝ
  opportunity : ℕ → Ω → ℝ
  rate_adapted : ∀ t, StronglyMeasurable[ℱ t] (rate t)
  immigration_adapted : ∀ t, StronglyMeasurable[ℱ (t + 1)] (immigration t)
  opportunity_adapted : ∀ t, StronglyMeasurable[ℱ (t + 1)] (opportunity t)
  rate_nonneg : ∀ t ω, 0 ≤ rate t ω
  immigration_bernoulli : ∀ t ω, immigration t ω = 0 ∨ immigration t ω = 1
  opportunity_bernoulli : ∀ t ω, opportunity t ω = 0 ∨ opportunity t ω = 1
  immigration_le_opportunity : ∀ t ω, immigration t ω ≤ opportunity t ω
  conditional_rate : ∀ t, ∀ᵐ ω ∂μ,
    (μ[immigration t | ℱ t]) ω ≤ (μ[opportunity t | ℱ t]) ω * rate t ω

def immigrationCharge (d : ImmigrationOpportunityData μ ℱ) : ℕ → Ω → ℝ :=
  opportunityCompensator d.rate d.opportunity

def immigrationEvents (d : ImmigrationOpportunityData μ ℱ) : ℕ → Ω → ℝ :=
  bernoulliCount d.immigration

def immigrationPotential (d : ImmigrationOpportunityData μ ℱ) (t : ℕ) (ω : Ω) : ℝ :=
  Real.exp (Real.log 2 * immigrationEvents d t ω - immigrationCharge d t ω)

@[simp] theorem immigrationCharge_zero (d : ImmigrationOpportunityData μ ℱ) (ω : Ω) :
    immigrationCharge d 0 ω = 0 := by simp only [immigrationCharge, opportunityCompensator_zero]

theorem immigrationCharge_succ (d : ImmigrationOpportunityData μ ℱ) (t : ℕ) (ω : Ω) :
    immigrationCharge d (t + 1) ω =
      immigrationCharge d t ω + d.rate t ω * d.opportunity t ω :=
  opportunityCompensator_succ _ _ t ω

theorem immigrationCharge_nonneg (d : ImmigrationOpportunityData μ ℱ) (t : ℕ) (ω : Ω) :
    0 ≤ immigrationCharge d t ω :=
  opportunityCompensator_nonneg _ _ d.rate_nonneg d.opportunity_bernoulli t ω

theorem immigrationCharge_stronglyMeasurable (d : ImmigrationOpportunityData μ ℱ) (t : ℕ) :
    StronglyMeasurable[ℱ t] (immigrationCharge d t) :=
  opportunityCompensator_stronglyMeasurable _ _ d.rate_adapted d.opportunity_adapted t

@[simp] theorem immigrationEvents_zero (d : ImmigrationOpportunityData μ ℱ) (ω : Ω) :
    immigrationEvents d 0 ω = 0 := by simp [immigrationEvents, bernoulliCount]

theorem immigrationEvents_succ (d : ImmigrationOpportunityData μ ℱ) (t : ℕ) (ω : Ω) :
    immigrationEvents d (t + 1) ω =
      immigrationEvents d t ω + d.immigration t ω := by
  simp only [immigrationEvents, bernoulliCount, Finset.sum_range_succ]

theorem immigrationEvents_bounds (d : ImmigrationOpportunityData μ ℱ) (t : ℕ) (ω : Ω) :
    0 ≤ immigrationEvents d t ω ∧ immigrationEvents d t ω ≤ (t : ℝ) := by
  constructor
  · unfold immigrationEvents bernoulliCount
    apply Finset.sum_nonneg
    intro u _
    rcases d.immigration_bernoulli u ω with h | h <;> simp only [h] <;> norm_num
  · calc
      immigrationEvents d t ω ≤ ∑ _u ∈ Finset.range t, (1 : ℝ) := by
        unfold immigrationEvents bernoulliCount
        apply Finset.sum_le_sum
        intro u _
        rcases d.immigration_bernoulli u ω with h | h <;> simp only [h] <;> norm_num
      _ = (t : ℝ) := by simp

theorem immigrationEvents_stronglyMeasurable (d : ImmigrationOpportunityData μ ℱ) (t : ℕ) :
    StronglyMeasurable[ℱ t] (immigrationEvents d t) :=
  bernoulliCount_stronglyMeasurable d.immigration_adapted t

theorem immigrationPotential_stronglyMeasurable (d : ImmigrationOpportunityData μ ℱ) (t : ℕ) :
    StronglyMeasurable[ℱ t] (immigrationPotential d t) := by
  have he := immigrationEvents_stronglyMeasurable d t
  have hc := immigrationCharge_stronglyMeasurable d t
  unfold immigrationPotential
  fun_prop

theorem immigrationPotential_bounds (d : ImmigrationOpportunityData μ ℱ) (t : ℕ) (ω : Ω) :
    0 ≤ immigrationPotential d t ω ∧
      immigrationPotential d t ω ≤ Real.exp (Real.log 2 * (t : ℝ)) := by
  refine ⟨Real.exp_nonneg _, Real.exp_le_exp.mpr ?_⟩
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hcount := mul_le_mul_of_nonneg_left (immigrationEvents_bounds d t ω).2 hlog
  have hcharge := immigrationCharge_nonneg d t ω
  linarith

theorem immigrationPotential_step (d : ImmigrationOpportunityData μ ℱ)
    (t : ℕ) (ω : Ω) :
    immigrationPotential d (t + 1) ω =
      immigrationPotential d t ω *
        (Real.exp (-d.rate t ω * d.opportunity t ω) *
          (1 + (1 : ℝ) * d.immigration t ω)) := by
  have he : Real.exp (Real.log 2 * d.immigration t ω) = 1 + d.immigration t ω := by
    rcases d.immigration_bernoulli t ω with h | h
    · simp only [h, mul_zero, Real.exp_zero, add_zero]
    · simp only [h, mul_one, Real.exp_log (by norm_num : (0 : ℝ) < 2)] <;> norm_num
  calc
    immigrationPotential d (t + 1) ω =
        immigrationPotential d t ω *
          Real.exp (Real.log 2 * d.immigration t ω - d.rate t ω * d.opportunity t ω) := by
      dsimp only [immigrationPotential]
      rw [immigrationEvents_succ, immigrationCharge_succ, ← Real.exp_add]
      congr 1
      ring
    _ = _ := by
      have hf : Real.exp (Real.log 2 * d.immigration t ω - d.rate t ω * d.opportunity t ω) =
          Real.exp (-d.rate t ω * d.opportunity t ω) *
            Real.exp (Real.log 2 * d.immigration t ω) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [hf, he, one_mul]

theorem immigrationOpportunity_supermartingale (d : ImmigrationOpportunityData μ ℱ) :
    Supermartingale (immigrationPotential d) ℱ μ := by
  have hrate : ∀ t, ∀ᵐ ω ∂μ,
      (1 : ℝ) * (μ[d.immigration t | ℱ t]) ω ≤
        (μ[d.opportunity t | ℱ t]) ω * d.rate t ω := by
    intro t
    simpa only [one_mul] using d.conditional_rate t
  exact opportunity_supermartingale (immigrationPotential d) (fun _ _ => 1) d.rate
    d.immigration d.opportunity (fun t => Real.exp (Real.log 2 * (t : ℝ))) (fun _ => 1)
    (immigrationPotential_stronglyMeasurable d) (fun _ => stronglyMeasurable_const)
    d.rate_adapted (immigrationPotential_bounds d) (fun _ _ => by norm_num) d.rate_nonneg
    d.immigration_adapted d.opportunity_adapted d.immigration_bernoulli d.opportunity_bernoulli
    d.immigration_le_opportunity
    (fun t => ae_of_all _ (fun ω => (immigrationPotential_step d t ω).le)) hrate

theorem immigration_opportunity_prefix_tail (d : ImmigrationOpportunityData μ ℱ)
    (E : Set Ω) (hE : MeasurableSet[ℱ 0] E) (a B : ℝ) :
    μ (E ∩ {ω | ∃ t, a ≤ immigrationEvents d t ω ∧ immigrationCharge d t ω ≤ B}) ≤
      ENNReal.ofReal (Real.exp (B - Real.log 2 * a)) * μ E := by
  let c : ℝ := Real.exp (B - Real.log 2 * a)
  have hc : 0 ≤ c := Real.exp_nonneg _
  have hzero (ω : Ω) (_he : ω ∈ E) : immigrationPotential d 0 ω ≤ 1 := by
    simp only [immigrationPotential, immigrationEvents_zero, immigrationCharge_zero,
      mul_zero, sub_zero, Real.exp_zero, le_refl]
  have hcross (ω : Ω)
      (hω : ω ∈ {ω | ∃ t, a ≤ immigrationEvents d t ω ∧ immigrationCharge d t ω ≤ B}) :
      ∃ t, 1 ≤ c * immigrationPotential d t ω := by
    obtain ⟨t, hcount, hcharge⟩ := hω
    have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have harg := mul_le_mul_of_nonneg_left hcount hlog
    have hpot : Real.exp (Real.log 2 * a - B) ≤ immigrationPotential d t ω :=
      Real.exp_le_exp.mpr (by linarith)
    refine ⟨t, ?_⟩
    calc
      1 = c * Real.exp (Real.log 2 * a - B) := by
        dsimp only [c]
        rw [← Real.exp_add]
        have he : B - Real.log 2 * a + (Real.log 2 * a - B) = 0 := by ring
        rw [he, Real.exp_zero]
      _ ≤ c * immigrationPotential d t ω := mul_le_mul_of_nonneg_left hpot hc
  have htail := prefix_crossing_tail (immigrationOpportunity_supermartingale d)
    (fun t ω => (immigrationPotential_bounds d t ω).1) E hE
    1 c (by norm_num) hc hzero _ hcross
  simpa only [c, mul_one] using htail

theorem log_two_lower : (2 / 3 : ℝ) ≤ Real.log 2 := by
  have h := Real.le_log_one_add_of_nonneg (x := (1 : ℝ)) (by norm_num)
  norm_num at h
  exact h

theorem immigration_opportunity_quarter_tail (d : ImmigrationOpportunityData μ ℱ)
    (E : Set Ω) (hE : MeasurableSet[ℱ 0] E) (a B : ℝ)
    (ha : 0 ≤ a) (hB : B ≤ a / 4) :
    μ (E ∩ {ω | ∃ t, a ≤ immigrationEvents d t ω ∧ immigrationCharge d t ω ≤ B}) ≤
      ENNReal.ofReal (Real.exp (-a / 3)) * μ E := by
  apply (immigration_opportunity_prefix_tail d E hE a B).trans
  apply mul_le_mul_right'
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  have hlog := mul_le_mul_of_nonneg_right log_two_lower ha
  linarith

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockImmigrationOpportunity

end
