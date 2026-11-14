-- Ripple/PopulationProtocol/ExactMajority/Probability/LateAcceptedTrialTail.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.LateSamplingCounterTail

/-!
# Constant bad-reward ratio for stopped accepted samples

`CounterSpec` already provides prefix-defined event and bad bits.
This file supplies the complementary constant-ratio trial: on every live
prefix, `bad hazard ≤ q * accepted hazard`.  The resulting exponent is
`exp (-2 γ² k)` and uses no iid or future-success conditioning.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.LateAcceptedTrialTail

open TimeTheorem PairLog PairLogAuxiliary
open AveragingRecordedExpectation LateSamplingScalar
open LateSamplingCounterTail LateF6Hazards

variable {L K : ℕ}
variable {init : Cfg L K}

noncomputable def badCount
    (B : ℕ → Ω L K → ℝ) (N : ℕ) (ω : Ω L K) : ℝ :=
  ∑ u ∈ Finset.range N, B u ω

theorem CounterSpec.badCount_eq
    (R : CounterSpec init) (ω : Ω L K) (N : ℕ) :
    badCount R.badTrial N ω =
      ((R.state ω (R.start + N)).2.1 : ℝ) := by
  induction N with
  | zero =>
      rw [Nat.add_zero, R.state_before_start ω R.start le_rfl]
      simp [badCount]
  | succ N ih =>
      simp only [badCount, Finset.sum_range_succ] at *
      rw [ih, R.badTrial_eq_bit]
      rw [show R.start + (N + 1) = (R.start + N) + 1 by omega,
        R.bad_succ, Nat.cast_add]

noncomputable def unitCoefficient
    (u : ℕ) (ω : Ω L K) : ℝ := 1

noncomputable def fixedRatio
    (q : ℝ) (u : ℕ) (ω : Ω L K) : ℝ := q

/-- Build `Trials` directly from the prefix-defined pair indicators and a
constant accepted-bad hazard. -/
theorem CounterSpec.constant_trials
    (R : CounterSpec init) (hn : 2 ≤ init.card)
    (q : ℝ) (hq : 0 ≤ q)
    (hhazard : ∀ t p z, R.Enabled t p z →
      pairMass init R.bad (prefixLabels init t p) ≤
        q * pairMass init R.event (prefixLabels init t p))
    (p : (i : Finset.Iic R.start) → Draw L K) :
    Trials (μ := recordedFuture init R.start p)
      (ℱ := shiftedPairLog L K R.start)
      R.eventTrial R.badTrial unitCoefficient (fixedRatio q) := by
  classical
  refine
    ⟨R.eventTrial_measurable, R.badTrial_measurable,
      (fun _ => stronglyMeasurable_const),
      (fun _ => stronglyMeasurable_const), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u
    exact Filter.Eventually.of_forall fun ω =>
      pairIndicator_zero_one init (R.start + u)
        (R.prefixGate (R.start + u)) R.event ω
  · intro u
    exact Filter.Eventually.of_forall fun ω =>
      pairIndicator_zero_one init (R.start + u)
        (R.prefixGate (R.start + u)) R.bad ω
  · intro u
    exact Filter.Eventually.of_forall fun ω => by
      rw [R.eventTrial_eq_bit, R.badTrial_eq_bit]
      exact_mod_cast R.bits_subset (R.start + u) ω
  · intro u
    exact Filter.Eventually.of_forall fun _ => by
      simp [unitCoefficient]
  · intro u
    exact Filter.Eventually.of_forall fun _ => by
      simp [fixedRatio, hq]
  · intro u
    have hstart : R.start ≤ R.start + u := Nat.le_add_right _ _
    filter_upwards
      [pairIndicator_recorded_condExp init hn R.start (R.start + u)
        hstart p (R.prefixGate (R.start + u)) R.bad,
       pairIndicator_recorded_condExp init hn R.start (R.start + u)
        hstart p (R.prefixGate (R.start + u)) R.event] with ω hb ha
    change (recordedFuture init R.start p)[
      pairIndicator init (R.start + u) (R.prefixGate (R.start + u)) R.bad |
        pairLogFiltration L K (R.start + u)] ω ≤
      fixedRatio q u ω *
        (recordedFuture init R.start p)[
          pairIndicator init (R.start + u)
              (R.prefixGate (R.start + u)) R.event |
            pairLogFiltration L K (R.start + u)] ω
    rw [hb, ha]
    change (if R.active (R.start + u) ω then
        pairMass init R.bad (labelsAt init ω (R.start + u)) else 0) ≤
      q * (if R.active (R.start + u) ω then
        pairMass init R.event (labelsAt init ω (R.start + u)) else 0)
    by_cases he : R.active (R.start + u) ω
    · simp only [if_pos he]
      exact hhazard (R.start + u)
        (frestrictLe (R.start + u) ω)
        (R.state ω (R.start + u)) he
    · simp only [if_neg he, mul_zero, le_refl]

theorem CounterSpec.constant_score_eq
    (R : CounterSpec init) (q : ℝ) (N : ℕ) (ω : Ω L K) :
    score R.eventTrial R.badTrial unitCoefficient (fixedRatio q) N ω =
      badCount R.badTrial N ω - q * eventCount R.eventTrial N ω := by
  unfold score badCount eventCount unitCoefficient fixedRatio
  simp only [one_mul, Finset.sum_sub_distrib, Finset.mul_sum]

/-- Real-measure form of the stopped accepted-trial tail. -/
theorem CounterSpec.constant_real_tail
    (R : CounterSpec init) (hn : 2 ≤ init.card)
    (q γ : ℝ) (hq : 0 ≤ q) (hγ : 0 ≤ γ)
    (hhazard : ∀ t p z, R.Enabled t p z →
      pairMass init R.bad (prefixLabels init t p) ≤
        q * pairMass init R.event (prefixLabels init t p))
    (p : (i : Finset.Iic R.start) → Draw L K)
    (k N : ℕ) :
    (recordedFuture init R.start p).real
      {ω | k ≤ eventCount R.eventTrial N ω ∧
        (q + γ) * eventCount R.eventTrial N ω ≤
          badCount R.badTrial N ω} ≤
      Real.exp (-2 * γ ^ 2 * k) := by
  have htrials := CounterSpec.constant_trials R hn q hq hhazard p
  refine (measureReal_mono (μ := recordedFuture init R.start p) ?_).trans
    (htrials.raw_tail γ k hγ N)
  intro ω hω
  refine ⟨hω.1, ?_⟩
  rw [CounterSpec.constant_score_eq R q N ω]
  nlinarith only [hω.2, hγ, hω.1]

/-- ENNReal form used by the recorded-future/original-law splice. -/
theorem CounterSpec.constant_tail
    (R : CounterSpec init) (hn : 2 ≤ init.card)
    (q γ : ℝ) (hq : 0 ≤ q) (hγ : 0 ≤ γ)
    (hhazard : ∀ t p z, R.Enabled t p z →
      pairMass init R.bad (prefixLabels init t p) ≤
        q * pairMass init R.event (prefixLabels init t p))
    (p : (i : Finset.Iic R.start) → Draw L K)
    (k N : ℕ) :
    recordedFuture init R.start p
      {ω | k ≤ eventCount R.eventTrial N ω ∧
        (q + γ) * eventCount R.eventTrial N ω ≤
          badCount R.badTrial N ω} ≤
      ENNReal.ofReal (Real.exp (-2 * γ ^ 2 * k)) := by
  have hreal := CounterSpec.constant_real_tail R hn q γ hq hγ hhazard p k N
  calc
    recordedFuture init R.start p
        {ω | k ≤ eventCount R.eventTrial N ω ∧
          (q + γ) * eventCount R.eventTrial N ω ≤
            badCount R.badTrial N ω} =
      ENNReal.ofReal
        ((recordedFuture init R.start p).real
          {ω | k ≤ eventCount R.eventTrial N ω ∧
            (q + γ) * eventCount R.eventTrial N ω ≤
              badCount R.badTrial N ω}) :=
      (ENNReal.ofReal_toReal
        (measure_ne_top (recordedFuture init R.start p) _)).symm
    _ ≤ ENNReal.ofReal (Real.exp (-2 * γ ^ 2 * k)) :=
      ENNReal.ofReal_le_ofReal hreal

end Ripple.PopulationProtocol.ExactMajority.LateAcceptedTrialTail

end
