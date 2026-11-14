-- Ripple/PopulationProtocol/ExactMajority/Probability/LateTimerPrefixScalar.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockPrefixTails
import Ripple.PopulationProtocol.ExactMajority.Probability.ScalarTails

/-!
# Prefix-weighted lower timer tail

This is the fixed-label scalar timer estimate with an arbitrary event from the
initial sigma algebra retained as a multiplicative factor.  It is the local
estimate needed on each genuine first-seed fibre.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Real
open scoped BigOperators ENNReal NNReal MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.LateTimerPrefixScalar

open PhaseThreeScalar

/-- The protection horizon `ceil(26.5 n log n)`. -/
noncomputable def protectionHorizon (n : ℕ) : ℕ :=
  Nat.ceil ((53 / 2 : ℝ) * n * Real.log (n : ℝ))

/-- A counter reset to `50 H` needs one further invocation because the zero
check precedes decrementing. -/
def invocationThreshold (n : ℕ) : ℕ :=
  50 * PhaseThreeModel.Numeric.clockHours n + 1

private theorem timerLogTwoBounds :
    (69 / 100 : ℝ) ≤ Real.log 2 ∧
      Real.log 2 ≤ (347 / 500 : ℝ) := by
  have hlo := Real.sum_range_le_log_div
    (x := (1 / 3 : ℝ)) (by norm_num) (by norm_num) 2
  have hhi := Real.log_div_le_sum_range_add
    (x := (1 / 3 : ℝ)) (by norm_num) (by norm_num) 4
  norm_num [Finset.sum_range_succ] at hlo hhi
  constructor <;> linarith

private theorem timerExpSmall :
    Real.exp (3 / 10 : ℝ) - 1 ≤ (7 / 20 : ℝ) := by
  have h := Real.exp_bound'
    (x := (3 / 10 : ℝ))
    (by norm_num) (by norm_num) (n := 4) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith

private theorem timerHourOneLe (n : ℕ) :
    (1 : ℝ) ≤ PhaseThreeModel.Numeric.clockHours n := by
  have hidx :
      (0 : ℝ) ≤ PhaseThreeModel.Numeric.hourIndex n :=
    Nat.cast_nonneg _
  simp only [PhaseThreeModel.Numeric.clockHours,
    Nat.cast_add, Nat.cast_one]
  linarith

private theorem timerHourLogBounds {n : ℕ}
    (hlog : 0 ≤ Real.log (n : ℝ)) :
    Real.log (n : ℝ) ≤
        ((PhaseThreeModel.Numeric.clockHours n : ℝ) - 1) *
          Real.log 2 ∧
      (PhaseThreeModel.Numeric.clockHours n : ℝ) * Real.log 2 ≤
        Real.log (n : ℝ) + 2 * Real.log 2 := by
  have hlp : 0 < Real.log 2 := by
    linarith [timerLogTwoBounds.1]
  have hlo :
      Real.log (n : ℝ) / Real.log 2 ≤
        (PhaseThreeModel.Numeric.hourIndex n : ℝ) := by
    rw [PhaseThreeModel.Numeric.hourIndex_eq_real_ceiling]
    exact Nat.le_ceil _
  have hhi :
      (PhaseThreeModel.Numeric.hourIndex n : ℝ) <
        Real.log (n : ℝ) / Real.log 2 + 1 := by
    rw [PhaseThreeModel.Numeric.hourIndex_eq_real_ceiling]
    exact Nat.ceil_lt_add_one (div_nonneg hlog hlp.le)
  constructor
  · have h := (div_le_iff₀ hlp).mp hlo
    simpa only [PhaseThreeModel.Numeric.clockHours,
      Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using h
  · have h :
        ((PhaseThreeModel.Numeric.hourIndex n : ℝ) - 1) *
            Real.log 2 < Real.log (n : ℝ) :=
      (lt_div_iff₀ hlp).mp (by linarith only [hhi])
    simp only [PhaseThreeModel.Numeric.clockHours,
      Nat.cast_add, Nat.cast_one]
    nlinarith only [h]

/-- Prefix-weighted form of `ScalarTails.late_timer_lower_scalar`.

The prefix event is measurable at filtration time zero.  No conditional
probability measure is introduced: the ordinary-law mass of the prefix remains
as a factor on the right.  The scoped heartbeat allowance is for the same
real-exponential and rational normalization used by the landed scalar theorem.
-/
theorem late_timer_lower_prefix_scalar
    {Omega : Type*} {m : MeasurableSpace Omega}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {filtration : Filtration ℕ m}
    {n : ℕ} (hn : TimeTheorem.timePopulationThreshold ≤ n)
    (I : ℕ → Omega → ℝ)
    (hI : ∀ t, StronglyMeasurable[filtration (t + 1)] (I t))
    (hzeroOne : ∀ t, ∀ᵐ omega ∂mu, I t omega = 0 ∨ I t omega = 1)
    (hprob : ∀ t, mu[I t | filtration t] =ᵐ[mu]
      (fun _ => 2 / (n : ℝ)))
    (E : Set Omega) (hE : MeasurableSet[filtration 0] E) :
    mu.real
        (E ∩ {omega |
          ((invocationThreshold n : ℕ) : ℝ) ≤
            bernoulliCount I (protectionHorizon n) omega}) ≤
      Real.rpow (n : ℝ) (-(153 / 50 : ℝ)) * mu.real E := by
  obtain ⟨hnpos, hnlog⟩ :=
    ScalarTails.time_population_scalar_bounds hn
  have hlog : 0 ≤ Real.log (n : ℝ) := by
    linarith only [hnlog]
  have hnone : (1 : ℝ) ≤ n := by
    have h := Real.add_one_le_exp (Real.log (n : ℝ))
    rw [Real.exp_log hnpos] at h
    linarith only [h, hnlog]
  let N : ℕ := protectionHorizon n
  let R : ℝ := (invocationThreshold n : ℕ)
  have hceil :
      (N : ℝ) ≤ (53 / 2 : ℝ) * n * Real.log (n : ℝ) + 1 := by
    dsimp [N, protectionHorizon]
    exact (Nat.ceil_lt_add_one (by positivity)).le
  have hmean :
      (N : ℝ) * (2 / (n : ℝ)) ≤
        53 * Real.log (n : ℝ) + 2 := by
    calc
      (N : ℝ) * (2 / (n : ℝ)) =
          (2 * (N : ℝ)) / (n : ℝ) := by ring
      _ ≤ 53 * Real.log (n : ℝ) + 2 := by
        apply (div_le_iff₀ hnpos).2
        nlinarith only [hceil, hnone]
  have hcoefficient :
      (Real.exp (3 / 10 : ℝ) - 1) * (N : ℝ) *
          (2 / (n : ℝ)) ≤
        (7 / 20 : ℝ) * (53 * Real.log (n : ℝ) + 2) := by
    calc
      (Real.exp (3 / 10 : ℝ) - 1) * (N : ℝ) *
          (2 / (n : ℝ)) =
          (Real.exp (3 / 10 : ℝ) - 1) *
            ((N : ℝ) * (2 / (n : ℝ))) := by ring
      _ ≤ (7 / 20 : ℝ) * ((N : ℝ) * (2 / (n : ℝ))) :=
        mul_le_mul_of_nonneg_right timerExpSmall (by positivity)
      _ ≤ (7 / 20 : ℝ) * (53 * Real.log (n : ℝ) + 2) :=
        mul_le_mul_of_nonneg_left hmean (by norm_num)
  have hcoefficient' :
      (Real.exp (3 / 10 : ℝ) - 1) * (2 / (n : ℝ)) *
          (N : ℝ) ≤
        (7 / 20 : ℝ) * (53 * Real.log (n : ℝ) + 2) := by
    calc
      (Real.exp (3 / 10 : ℝ) - 1) * (2 / (n : ℝ)) * (N : ℝ) =
          (Real.exp (3 / 10 : ℝ) - 1) * (N : ℝ) *
            (2 / (n : ℝ)) := by ring
      _ ≤ _ := hcoefficient
  have hHone := timerHourOneLe n
  have hHscaled :
      Real.log (n : ℝ) ≤
        (347 / 500 : ℝ) *
          ((PhaseThreeModel.Numeric.clockHours n : ℝ) - 1) := by
    calc
      Real.log (n : ℝ) ≤
          ((PhaseThreeModel.Numeric.clockHours n : ℝ) - 1) *
            Real.log 2 :=
        (timerHourLogBounds hlog).1
      _ ≤ ((PhaseThreeModel.Numeric.clockHours n : ℝ) - 1) *
          (347 / 500 : ℝ) :=
        mul_le_mul_of_nonneg_left timerLogTwoBounds.2
          (sub_nonneg.mpr hHone)
      _ = _ := by ring
  have htail :=
    PhaseThreeClockPrefixTails.prefix_bernoulli_exponential_tail
      (μ := mu) (ℱ := filtration) (I := I)
      hI hzeroOne hprob E hE
      (3 / 10 : ℝ) R N
  have hsubset :
      E ∩ {omega | R ≤ bernoulliCount I N omega} ⊆
        E ∩ {omega |
          (3 / 10 : ℝ) * R ≤
            (3 / 10 : ℝ) * bernoulliCount I N omega} := by
    rintro omega ⟨hEomega, hcount⟩
    have hc : R ≤ bernoulliCount I N omega := hcount
    exact ⟨hEomega,
      mul_le_mul_of_nonneg_left hc (by norm_num : (0 : ℝ) ≤ 3 / 10)⟩
  have hscalar :
      Real.exp
          ((Real.exp (3 / 10 : ℝ) - 1) * (2 / (n : ℝ)) *
              (N : ℝ) - (3 / 10 : ℝ) * R) ≤
        Real.rpow (n : ℝ) (-(153 / 50 : ℝ)) := by
    change _ ≤ (n : ℝ) ^ (-(153 / 50 : ℝ))
    rw [Real.rpow_def_of_pos hnpos]
    apply Real.exp_le_exp.mpr
    dsimp [R, invocationThreshold]
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one,
      Nat.cast_ofNat]
    nlinarith only [hcoefficient', hHscaled, hHone]
  have hmain :
      mu.real (E ∩ {omega | R ≤ bernoulliCount I N omega}) ≤
        Real.rpow (n : ℝ) (-(153 / 50 : ℝ)) * mu.real E := by
    calc
      mu.real (E ∩ {omega | R ≤ bernoulliCount I N omega}) ≤
          mu.real
            (E ∩ {omega |
              (3 / 10 : ℝ) * R ≤
                (3 / 10 : ℝ) * bernoulliCount I N omega}) :=
        measureReal_mono hsubset
      _ ≤ Real.exp
            ((Real.exp (3 / 10 : ℝ) - 1) * (2 / (n : ℝ)) *
                (N : ℝ) - (3 / 10 : ℝ) * R) * mu.real E :=
        htail
      _ ≤ Real.rpow (n : ℝ) (-(153 / 50 : ℝ)) * mu.real E :=
        mul_le_mul_of_nonneg_right hscalar (by positivity)
  simpa [N, R, protectionHorizon, invocationThreshold] using hmain

/-!
THEOREM LIST
* `protectionHorizon`
* `invocationThreshold`
* `late_timer_lower_prefix_scalar`

CLOSES
* The `n^(-3.06)` fixed-label tail with an arbitrary time-zero prefix event
  retained as a multiplicative original-law factor.
* The exact `ceil(26.5 n log n)` horizon and `50 H + 1` invocation threshold.
* No conditioning on a future success event.

UNFINISHED
* Nothing in this file.
END
-/

end Ripple.PopulationProtocol.ExactMajority.LateTimerPrefixScalar

end
