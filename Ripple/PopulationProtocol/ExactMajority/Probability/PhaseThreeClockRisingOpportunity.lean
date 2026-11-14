-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockRisingOpportunity.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockOpportunityProcess

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockRisingOpportunity

open PhaseThreeClockRisingFactorial PhaseThreeClockOpportunityProcess

variable {Ω : Type*} {m₀ : MeasurableSpace Ω}
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℕ m₀}

structure RisingOpportunityData (μ : Measure Ω) (ℱ : Filtration ℕ m₀) (a : ℕ) where
  order_pos : 1 ≤ a
  value : ℕ → Ω → ℝ
  rate : ℕ → Ω → ℝ
  propagation : ℕ → Ω → ℝ
  opportunity : ℕ → Ω → ℝ
  upper : ℕ → ℝ
  value_adapted : ∀ t, StronglyMeasurable[ℱ t] (value t)
  rate_adapted : ∀ t, StronglyMeasurable[ℱ t] (rate t)
  propagation_adapted : ∀ t, StronglyMeasurable[ℱ (t + 1)] (propagation t)
  opportunity_adapted : ∀ t, StronglyMeasurable[ℱ (t + 1)] (opportunity t)
  value_bounds : ∀ t ω, (a : ℝ) ≤ value t ω ∧ value t ω ≤ upper t
  rate_nonneg : ∀ t ω, 0 ≤ rate t ω
  propagation_bernoulli : ∀ t ω, propagation t ω = 0 ∨ propagation t ω = 1
  opportunity_bernoulli : ∀ t ω, opportunity t ω = 0 ∨ opportunity t ω = 1
  propagation_le_opportunity : ∀ t ω, propagation t ω ≤ opportunity t ω
  value_step : ∀ t, value (t + 1) ≤ᵐ[μ] fun ω => value t ω + propagation t ω
  conditional_rate : ∀ t, ∀ᵐ ω ∂μ,
    (μ[propagation t | ℱ t]) ω ≤
      (μ[opportunity t | ℱ t]) ω * rate t ω * value t ω

variable {a : ℕ}

def risingCharge (d : RisingOpportunityData μ ℱ a) : ℕ → Ω → ℝ :=
  opportunityCompensator (fun t ω => (a : ℝ) * d.rate t ω) d.opportunity

def risingPotential (d : RisingOpportunityData μ ℱ a) (t : ℕ) (ω : Ω) : ℝ :=
  risingFactorial a (d.value t ω) * Real.exp (-risingCharge d t ω)

theorem RisingOpportunityData.value_pos (d : RisingOpportunityData μ ℱ a)
    (t : ℕ) (ω : Ω) : 0 < d.value t ω := by
  have ha : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by have h := d.order_pos; omega)
  exact ha.trans_le (d.value_bounds t ω).1

theorem risingCharge_nonneg (d : RisingOpportunityData μ ℱ a) (t : ℕ) (ω : Ω) :
    0 ≤ risingCharge d t ω :=
  opportunityCompensator_nonneg _ _ (fun u v => mul_nonneg (Nat.cast_nonneg a) (d.rate_nonneg u v))
    d.opportunity_bernoulli t ω

@[simp] theorem risingCharge_zero (d : RisingOpportunityData μ ℱ a) (ω : Ω) :
    risingCharge d 0 ω = 0 := by simp only [risingCharge, opportunityCompensator_zero]

theorem risingCharge_succ (d : RisingOpportunityData μ ℱ a) (t : ℕ) (ω : Ω) :
    risingCharge d (t + 1) ω =
      risingCharge d t ω + ((a : ℝ) * d.rate t ω) * d.opportunity t ω := by
  exact opportunityCompensator_succ _ _ t ω

theorem risingCharge_stronglyMeasurable (d : RisingOpportunityData μ ℱ a) (t : ℕ) :
    StronglyMeasurable[ℱ t] (risingCharge d t) :=
  opportunityCompensator_stronglyMeasurable _ _
    (fun u => stronglyMeasurable_const.mul (d.rate_adapted u)) d.opportunity_adapted t

theorem risingPotential_stronglyMeasurable (d : RisingOpportunityData μ ℱ a) (t : ℕ) :
    StronglyMeasurable[ℱ t] (risingPotential d t) := by
  have hPhi : StronglyMeasurable[ℱ t] (fun ω => risingFactorial a (d.value t ω)) := by
    unfold risingFactorial
    refine (Finset.range a).stronglyMeasurable_fun_prod ?_
    intro j _
    exact (d.value_adapted t).add stronglyMeasurable_const
  have hcharge := risingCharge_stronglyMeasurable d t
  unfold risingPotential
  exact hPhi.mul (Real.continuous_exp.comp_stronglyMeasurable hcharge.neg)

theorem risingPotential_bounds (d : RisingOpportunityData μ ℱ a) (t : ℕ) (ω : Ω) :
    0 ≤ risingPotential d t ω ∧
      risingPotential d t ω ≤ risingFactorial a (max 0 (d.upper t)) := by
  have hv := (d.value_pos t ω).le
  have hPhi := risingFactorial_nonneg a (d.value t ω) hv
  have he : Real.exp (-risingCharge d t ω) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (risingCharge_nonneg d t ω))
  refine ⟨mul_nonneg hPhi (Real.exp_nonneg _), ?_⟩
  calc
    risingPotential d t ω ≤ risingFactorial a (d.value t ω) :=
      mul_le_of_le_one_right hPhi he
    _ ≤ risingFactorial a (max 0 (d.upper t)) :=
      risingFactorial_mono a hv ((d.value_bounds t ω).2.trans (le_max_right _ _))

theorem risingPotential_step (d : RisingOpportunityData μ ℱ a) (t : ℕ) :
    risingPotential d (t + 1) ≤ᵐ[μ] fun ω =>
      risingPotential d t ω *
        (Real.exp (-((a : ℝ) * d.rate t ω) * d.opportunity t ω) *
          (1 + ((a : ℝ) / d.value t ω) * d.propagation t ω)) := by
  filter_upwards [d.value_step t] with ω hstep
  have hPhi := risingFactorial_step_le a (d.value t ω) (d.value (t + 1) ω)
    (d.propagation t ω) (d.value_pos t ω) (d.value_pos (t + 1) ω).le
    (d.propagation_bernoulli t ω) hstep
  calc
    risingPotential d (t + 1) ω =
        Real.exp (-risingCharge d (t + 1) ω) *
          risingFactorial a (d.value (t + 1) ω) := mul_comm _ _
    _ ≤ Real.exp (-risingCharge d (t + 1) ω) *
        (risingFactorial a (d.value t ω) +
          ((a : ℝ) * risingFactorial a (d.value t ω) / d.value t ω) *
            d.propagation t ω) :=
      mul_le_mul_of_nonneg_left hPhi (Real.exp_nonneg _)
    _ = _ := by
      dsimp only [risingPotential]
      rw [risingCharge_succ, neg_add, Real.exp_add]
      simp only [neg_mul]
      ring

theorem risingOpportunity_supermartingale (d : RisingOpportunityData μ ℱ a) :
    Supermartingale (risingPotential d) ℱ μ := by
  have hb (t : ℕ) :
      StronglyMeasurable[ℱ t] (fun ω => (a : ℝ) / d.value t ω) := by
    have hv := d.value_adapted t
    fun_prop
  have hbb (t : ℕ) (ω : Ω) :
      0 ≤ (a : ℝ) / d.value t ω ∧ (a : ℝ) / d.value t ω ≤ 1 :=
    ⟨div_nonneg (Nat.cast_nonneg a) (d.value_pos t ω).le,
      (div_le_one (d.value_pos t ω)).mpr (d.value_bounds t ω).1⟩
  have hrate : ∀ t, ∀ᵐ ω ∂μ,
      ((a : ℝ) / d.value t ω) * (μ[d.propagation t | ℱ t]) ω ≤
        (μ[d.opportunity t | ℱ t]) ω * ((a : ℝ) * d.rate t ω) := by
    intro t
    filter_upwards [d.conditional_rate t] with ω hω
    have hmul := mul_le_mul_of_nonneg_left hω (hbb t ω).1
    have hid :
        ((a : ℝ) / d.value t ω) *
            ((μ[d.opportunity t | ℱ t]) ω * d.rate t ω * d.value t ω) =
          (μ[d.opportunity t | ℱ t]) ω * ((a : ℝ) * d.rate t ω) := by
      field_simp [ne_of_gt (d.value_pos t ω)]
      <;> ring
    rwa [hid] at hmul
  exact opportunity_supermartingale (risingPotential d)
    (fun t ω => (a : ℝ) / d.value t ω) (fun t ω => (a : ℝ) * d.rate t ω)
    d.propagation d.opportunity (fun t => risingFactorial a (max 0 (d.upper t))) (fun _ => 1)
    (risingPotential_stronglyMeasurable d) hb
    (fun t => stronglyMeasurable_const.mul (d.rate_adapted t))
    (risingPotential_bounds d) hbb
    (fun t ω => mul_nonneg (Nat.cast_nonneg a) (d.rate_nonneg t ω))
    d.propagation_adapted d.opportunity_adapted d.propagation_bernoulli
    d.opportunity_bernoulli d.propagation_le_opportunity (risingPotential_step d) hrate

theorem rising_opportunity_prefix_tail (d : RisingOpportunityData μ ℱ a)
    (E : Set Ω) (hE : MeasurableSet[ℱ 0] E)
    (hstart : ∀ ω ∈ E, d.value 0 ω ≤ 2 * (a : ℝ))
    (R : ℝ) (hR : 0 < R) (B : ℝ) :
    μ (E ∩ {ω | ∃ t, R ≤ d.value t ω ∧ risingCharge d t ω ≤ B}) ≤
      ENNReal.ofReal ((3 * (a : ℝ)) ^ a * Real.exp B / R ^ a) * μ E := by
  let c : ℝ := Real.exp B / R ^ a
  have hc : 0 ≤ c := div_nonneg (Real.exp_nonneg _) (pow_nonneg hR.le a)
  have hepsilon : 0 ≤ (3 * (a : ℝ)) ^ a := by positivity
  have hzero (ω : Ω) (he : ω ∈ E) :
      risingPotential d 0 ω ≤ (3 * (a : ℝ)) ^ a := by
    simpa only [risingPotential, risingCharge_zero, neg_zero, Real.exp_zero, mul_one] using
      risingFactorial_initial_bound a (d.value 0 ω) (d.value_pos 0 ω).le (hstart ω he)
  have hcross (ω : Ω)
      (hω : ω ∈ {ω | ∃ t, R ≤ d.value t ω ∧ risingCharge d t ω ≤ B}) :
      ∃ t, 1 ≤ c * risingPotential d t ω := by
    obtain ⟨t, hvalue, hcharge⟩ := hω
    have hPhi : R ^ a ≤ risingFactorial a (d.value t ω) :=
      (pow_le_pow_left₀ hR.le hvalue a).trans
        (risingFactorial_lower a (d.value t ω) (d.value_pos t ω).le)
    have hexp : Real.exp (-B) ≤ Real.exp (-risingCharge d t ω) :=
      Real.exp_le_exp.mpr (neg_le_neg hcharge)
    have hpot : R ^ a * Real.exp (-B) ≤ risingPotential d t ω :=
      mul_le_mul hPhi hexp (Real.exp_nonneg _) (risingFactorial_nonneg a _ (d.value_pos t ω).le)
    refine ⟨t, ?_⟩
    calc
      1 = c * (R ^ a * Real.exp (-B)) := by
        dsimp only [c]
        rw [Real.exp_neg]
        field_simp [ne_of_gt (pow_pos hR a), ne_of_gt (Real.exp_pos B)]
        <;> ring
      _ ≤ c * risingPotential d t ω := mul_le_mul_of_nonneg_left hpot hc
  have htail := prefix_crossing_tail (risingOpportunity_supermartingale d)
    (fun t ω => (risingPotential_bounds d t ω).1) E hE
    ((3 * (a : ℝ)) ^ a) c hepsilon hc hzero _ hcross
  have hcoef : c * (3 * (a : ℝ)) ^ a =
      (3 * (a : ℝ)) ^ a * Real.exp B / R ^ a := by dsimp only [c]; ring
  rwa [hcoef] at htail

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockRisingOpportunity

end
