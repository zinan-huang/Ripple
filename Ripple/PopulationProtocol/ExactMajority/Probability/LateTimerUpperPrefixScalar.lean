-- Ripple/PopulationProtocol/ExactMajority/Probability/LateTimerUpperPrefixScalar.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.ScalarTails
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockPrefixTails

/-!
# Prefix-weighted scalar upper timer tail

This is the prefix-retaining form of the landed
`ScalarTails.late_timer_upper_scalar`:

* horizon `logWindow n 54 = ceil (54 n log n)`;
* adapted Bernoulli parameter `2/n`;
* lower-tail threshold `50 * clockHours n`;
* bound `n^(-5)` times the original prefix mass.

Theorem list:
* `late_timer_upper_prefix_scalar`
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped BigOperators ENNReal NNReal

namespace Ripple.PopulationProtocol.ExactMajority.LateTimerUpperPrefixScalar

open TimeTheorem PhaseThreeScalar

private theorem upperTimerLogTwoBounds :
    (69 / 100 : ℝ) ≤ Real.log 2 ∧
      Real.log 2 ≤ (347 / 500 : ℝ) := by
  have hlo := Real.sum_range_le_log_div
    (x := (1 / 3 : ℝ)) (by norm_num) (by norm_num) 2
  have hhi := Real.log_div_le_sum_range_add
    (x := (1 / 3 : ℝ)) (by norm_num) (by norm_num) 4
  norm_num [Finset.sum_range_succ] at hlo hhi
  constructor <;> linarith

private theorem upperTimerLogThreeHalvesBounds :
    0 ≤ Real.log (3 / 2 : ℝ) ∧
      Real.log (3 / 2 : ℝ) ≤ (41 / 100 : ℝ) := by
  have hhi := Real.log_div_le_sum_range_add
    (x := (1 / 5 : ℝ)) (by norm_num) (by norm_num) 2
  norm_num [Finset.sum_range_succ] at hhi
  constructor
  · exact Real.log_nonneg (by norm_num)
  · linarith

private theorem upperTimerLogRatio :
    Real.log (3 / 2 : ℝ) ≤ (3 / 5 : ℝ) * Real.log 2 := by
  linarith [upperTimerLogTwoBounds.1,
    upperTimerLogThreeHalvesBounds.2]

private theorem upperTimerHourLogBounds {n : ℕ}
    (hlog : 0 ≤ Real.log (n : ℝ)) :
    (PhaseThreeModel.Numeric.clockHours n : ℝ) * Real.log 2 ≤
      Real.log (n : ℝ) + 2 * Real.log 2 := by
  have hlp : 0 < Real.log 2 := by
    linarith [upperTimerLogTwoBounds.1]
  have hhi :
      (PhaseThreeModel.Numeric.hourIndex n : ℝ) <
        Real.log (n : ℝ) / Real.log 2 + 1 := by
    rw [PhaseThreeModel.Numeric.hourIndex_eq_real_ceiling]
    exact Nat.ceil_lt_add_one (div_nonneg hlog hlp.le)
  have h :
      ((PhaseThreeModel.Numeric.hourIndex n : ℝ) - 1) * Real.log 2 <
        Real.log (n : ℝ) :=
    (lt_div_iff₀ hlp).mp (by linarith only [hhi])
  simp only [PhaseThreeModel.Numeric.clockHours,
    Nat.cast_add, Nat.cast_one]
  nlinarith only [h]

/-- Prefix-weighted equation (10).  Unlike the unconditional scalar theorem,
this form can be summed over disjoint stopping-time and chosen-label fibres
without losing a factor equal to their number. -/
theorem late_timer_upper_prefix_scalar
    {Ω : Type*} {m : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ m}
    {n : ℕ} (hn : timePopulationThreshold ≤ n)
    (I : ℕ → Ω → ℝ)
    (hI : ∀ t, StronglyMeasurable[ℱ (t + 1)] (I t))
    (hzeroOne : ∀ t, ∀ᵐ ω ∂μ, I t ω = 0 ∨ I t ω = 1)
    (hprob : ∀ t, μ[I t | ℱ t] =ᵐ[μ]
      (fun _ => 2 / (n : ℝ)))
    (E : Set Ω) (hE : MeasurableSet[ℱ 0] E) :
    μ.real
        (E ∩ {ω |
          PhaseThreeScalar.bernoulliCount I (logWindow n 54) ω ≤
            ((50 * PhaseThreeModel.Numeric.clockHours n : ℕ) : ℝ)}) ≤
      (1 / (n : ℝ) ^ 5) * μ.real E := by
  obtain ⟨hnpos, hnlog⟩ :=
    ScalarTails.time_population_scalar_bounds hn
  have hlog : 0 ≤ Real.log (n : ℝ) := by
    linarith only [hnlog]
  have hceil :
      54 * (n : ℝ) * Real.log (n : ℝ) ≤
        (logWindow n 54 : ℝ) := by
    unfold logWindow
    exact Nat.le_ceil _
  have hmean :
      108 * Real.log (n : ℝ) ≤
        (logWindow n 54 : ℝ) * (2 / (n : ℝ)) := by
    calc
      108 * Real.log (n : ℝ) ≤
          (2 * (logWindow n 54 : ℝ)) / (n : ℝ) := by
        apply (le_div_iff₀ hnpos).2
        nlinarith only [hceil]
      _ = (logWindow n 54 : ℝ) * (2 / (n : ℝ)) := by ring
  have hscaled :
      (PhaseThreeModel.Numeric.clockHours n : ℝ) *
          Real.log (3 / 2 : ℝ) ≤
        (PhaseThreeModel.Numeric.clockHours n : ℝ) *
          ((3 / 5 : ℝ) * Real.log 2) :=
    mul_le_mul_of_nonneg_left upperTimerLogRatio (Nat.cast_nonneg _)
  have hhour := upperTimerHourLogBounds hlog
  have hclock :
      50 * (PhaseThreeModel.Numeric.clockHours n : ℝ) *
          Real.log (3 / 2 : ℝ) ≤
        30 * Real.log (n : ℝ) + 60 * Real.log 2 := by
    nlinarith only [hscaled, hhour]
  let θ : ℝ := -Real.log (3 / 2 : ℝ)
  let r : ℝ := ((50 * PhaseThreeModel.Numeric.clockHours n : ℕ) : ℝ)
  have hθ : θ ≤ 0 :=
    neg_nonpos.mpr upperTimerLogThreeHalvesBounds.1
  have hexp : Real.exp θ = (2 / 3 : ℝ) := by
    dsimp [θ]
    rw [Real.exp_neg,
      Real.exp_log (by norm_num : (0 : ℝ) < 3 / 2)]
    norm_num
  have htail :=
    PhaseThreeClockPrefixTails.prefix_bernoulli_exponential_tail
      (μ := μ) (ℱ := ℱ) (I := I) (p := 2 / (n : ℝ))
      hI hzeroOne hprob E hE θ r (logWindow n 54)
  have harg :
      (Real.exp θ - 1) * (2 / (n : ℝ)) *
            (logWindow n 54 : ℝ) - θ * r =
        (Real.exp θ - 1) * (logWindow n 54 : ℝ) *
            (2 / (n : ℝ)) - θ * r := by ring
  rw [harg] at htail
  have hscalar :
      Real.exp
          ((Real.exp θ - 1) * (logWindow n 54 : ℝ) *
              (2 / (n : ℝ)) - θ * r) ≤
        1 / (n : ℝ) ^ 5 := by
    calc
      Real.exp
          ((Real.exp θ - 1) * (logWindow n 54 : ℝ) *
              (2 / (n : ℝ)) - θ * r) ≤
          Real.exp (-((5 : ℝ) * Real.log (n : ℝ))) := by
        apply Real.exp_le_exp.mpr
        dsimp [θ, r]
        rw [hexp]
        simp only [Nat.cast_mul, Nat.cast_ofNat]
        nlinarith only [hmean, hclock,
          upperTimerLogTwoBounds.2, hnlog]
      _ = 1 / (n : ℝ) ^ 5 := by
        have he :
            Real.exp ((5 : ℝ) * Real.log (n : ℝ)) = (n : ℝ) ^ 5 := by
          simpa only [Real.exp_log hnpos] using
            (Real.exp_nat_mul (Real.log (n : ℝ)) 5)
        rw [Real.exp_neg, he, one_div]
  have hsub :
      E ∩ {ω |
          PhaseThreeScalar.bernoulliCount I (logWindow n 54) ω ≤ r} ⊆
        E ∩ {ω | θ * r ≤
          θ * PhaseThreeScalar.bernoulliCount I (logWindow n 54) ω} := by
    rintro ω ⟨hω, hcount⟩
    exact ⟨hω, mul_le_mul_of_nonpos_left hcount hθ⟩
  calc
    μ.real
        (E ∩ {ω |
          PhaseThreeScalar.bernoulliCount I (logWindow n 54) ω ≤ r}) ≤
      μ.real
        (E ∩ {ω | θ * r ≤
          θ * PhaseThreeScalar.bernoulliCount I (logWindow n 54) ω}) :=
      measureReal_mono hsub
    _ ≤ Real.exp
          ((Real.exp θ - 1) * (logWindow n 54 : ℝ) *
              (2 / (n : ℝ)) - θ * r) * μ.real E := htail
    _ ≤ (1 / (n : ℝ) ^ 5) * μ.real E := by
      gcongr

/-!
THEOREM LIST
* `late_timer_upper_prefix_scalar`

CLOSES
* The prefix-weighted scalar form of Lemma 3, equation (10).
* The exact `54`, `50H`, and `n^(-5)` arithmetic.

UNFINISHED
* Nothing mathematical in this scalar file.
END
-/

end Ripple.PopulationProtocol.ExactMajority.LateTimerUpperPrefixScalar

end
