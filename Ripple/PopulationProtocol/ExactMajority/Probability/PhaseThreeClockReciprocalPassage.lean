-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockReciprocalPassage.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockReciprocalAlgebra
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockStoppedPassage
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockPotentialTail

/-!
# Calibrated sparse-front passage on the original pair-log law

The potential and its decrement are killed at the concrete PassageWindow
stop. The one-step inequality is proved from the actual gated
virtual update, and its conditional drift from the actual selected-pair
law. No drift or target-tail premise is left to the caller.

The resulting estimate has the P3a horizon and error. It bounds survival
of the explicitly stated window; identifying a window exit as a target
crossing requires the deterministic environment invariants.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockReciprocalPassage

open TimeTheorem PairLog PairLogAuxiliary PhaseThreeClockVirtual
  PhaseThreeClockGatedLaw PhaseThreeClockGatedLevelOne
  PhaseThreeClockProbabilityFloors PhaseThreeClockPrefixTails
  PhaseThreeClockStoppedPassage PhaseThreeClockReciprocalAlgebra
  PhaseThreeClockPotentialTail

variable {L : ℕ}

noncomputable def passageWeight (init : Cfg L 256) (ℓ b s t : ℕ) :
    Ω L 256 → ℝ :=
  {ω | (t : WithTop ℕ) < passageStop init ℓ b s ω}.indicator
    (fun ω => frontWeight (frontCount (virtualLabels init ω (s + t)) ℓ))

noncomputable def passageLoss (init : Cfg L 256) (ℓ b s t : ℕ) :
    Ω L 256 → ℝ :=
  {ω | (t : WithTop ℕ) < passageStop init ℓ b s ω}.indicator
    (fun ω => frontLoss (frontCount (virtualLabels init ω (s + t)) ℓ))

theorem passageWeight_stronglyMeasurable (init : Cfg L 256) (ℓ b s t : ℕ) :
    StronglyMeasurable[shiftedFiltration (pairLogFiltration L 256) s t]
      (passageWeight init ℓ b s t) := by
  have hstate := (measurable_aux_potential init virtualRule
    (fun f => frontWeight (frontCount f ℓ)) (s + t)).stronglyMeasurable
  exact hstate.indicator ((passageStop_isStoppingTime init ℓ b s).measurableSet_gt t)

theorem passageLoss_stronglyMeasurable (init : Cfg L 256) (ℓ b s t : ℕ) :
    StronglyMeasurable[shiftedFiltration (pairLogFiltration L 256) s t]
      (passageLoss init ℓ b s t) := by
  have hstate := (measurable_aux_potential init virtualRule
    (fun f => frontLoss (frontCount f ℓ)) (s + t)).stronglyMeasurable
  exact hstate.indicator ((passageStop_isStoppingTime init ℓ b s).measurableSet_gt t)

theorem passageWeight_bounds (init : Cfg L 256) (ℓ b s t : ℕ) (ω : Ω L 256) :
    0 ≤ passageWeight init ℓ b s t ω ∧ passageWeight init ℓ b s t ω ≤ 1 := by
  classical
  by_cases ht : (t : WithTop ℕ) < passageStop init ℓ b s ω
  · have htm : ω ∈ {ω | (t : WithTop ℕ) < passageStop init ℓ b s ω} := ht
    simpa only [passageWeight, Set.indicator_of_mem htm] using
      And.intro (frontWeight_pos (frontCount (virtualLabels init ω (s + t)) ℓ)).le
        (frontWeight_le_one (frontCount (virtualLabels init ω (s + t)) ℓ))
  · simp [passageWeight, ht]

theorem passageLoss_bounds (init : Cfg L 256) (ℓ b s t : ℕ) (ω : Ω L 256) :
    0 ≤ passageLoss init ℓ b s t ω ∧ passageLoss init ℓ b s t ω ≤ 1 := by
  classical
  by_cases ht : (t : WithTop ℕ) < passageStop init ℓ b s ω
  · have htm : ω ∈ {ω | (t : WithTop ℕ) < passageStop init ℓ b s ω} := ht
    simpa only [passageLoss, Set.indicator_of_mem htm] using
      frontLoss_bounds (frontCount (virtualLabels init ω (s + t)) ℓ)
  · simp [passageLoss, ht]

/-- On a live next step the front increment is exact. Killing the process
on the other steps can only strengthen the affine decrease inequality. -/
theorem passageWeight_step (init : Cfg L 256) (ℓ b s t : ℕ)
    (hℓ : 1 ≤ ℓ) (hcap : ℓ ≤ 256 * (L + 1)) (ω : Ω L 256) :
    passageWeight init ℓ b s (t + 1) ω ≤
      passageWeight init ℓ b s t ω -
        passageLoss init ℓ b s t ω * gatedIndicator init ℓ (s + t) ω := by
  classical
  by_cases hn : ((t + 1 : ℕ) : WithTop ℕ) < passageStop init ℓ b s ω
  · have ht : (t : WithTop ℕ) < passageStop init ℓ b s ω := by
      exact lt_of_le_of_lt (by exact_mod_cast Nat.le_succ t) hn
    have hw := passageWindow_of_lt_stop init ℓ b s (t + 1) ω hn
    have hstep :
        (frontCount (virtualLabels init ω (s + (t + 1))) ℓ : ℝ) =
          (frontCount (virtualLabels init ω (s + t)) ℓ : ℝ) +
            gatedIndicator init ℓ (s + t) ω := by
      simpa only [Nat.add_assoc] using
        front_step_on_window init ω (s + t) ℓ b hℓ hcap
          (hw t (by omega)) (by simpa only [Nat.add_assoc] using hw (t + 1) le_rfl)
    have hnm : ω ∈ {ω | ((t + 1 : ℕ) : WithTop ℕ) < passageStop init ℓ b s ω} := hn
    have htm : ω ∈ {ω | (t : WithTop ℕ) < passageStop init ℓ b s ω} := ht
    rw [passageWeight, Set.indicator_of_mem hnm,
      passageWeight, Set.indicator_of_mem htm,
      passageLoss, Set.indicator_of_mem htm]
    rcases gatedIndicator_zero_one init ℓ (s + t) ω with hz | ho
    · have hfront :
          frontCount (virtualLabels init ω (s + (t + 1))) ℓ =
            frontCount (virtualLabels init ω (s + t)) ℓ := by
        exact_mod_cast (show
          (frontCount (virtualLabels init ω (s + (t + 1))) ℓ : ℝ) =
            (frontCount (virtualLabels init ω (s + t)) ℓ : ℝ) by
              simpa only [hz, add_zero] using hstep)
      rw [hfront, hz, mul_zero, sub_zero]
    · have hfront :
          frontCount (virtualLabels init ω (s + (t + 1))) ℓ =
            frontCount (virtualLabels init ω (s + t)) ℓ + 1 := by
        exact_mod_cast (show
          (frontCount (virtualLabels init ω (s + (t + 1))) ℓ : ℝ) =
            (frontCount (virtualLabels init ω (s + t)) ℓ : ℝ) + 1 by
              simpa only [ho] using hstep)
      rw [hfront, ho, mul_one, frontLoss]
      linarith
  · have hnm : ω ∉ {ω | ((t + 1 : ℕ) : WithTop ℕ) < passageStop init ℓ b s ω} := hn
    rw [passageWeight, Set.indicator_of_notMem hnm]
    by_cases ht : (t : WithTop ℕ) < passageStop init ℓ b s ω
    · have htm : ω ∈ {ω | (t : WithTop ℕ) < passageStop init ℓ b s ω} := ht
      rw [passageWeight, Set.indicator_of_mem htm,
        passageLoss, Set.indicator_of_mem htm]
      rcases gatedIndicator_zero_one init ℓ (s + t) ω with hz | ho
      · rw [hz, mul_zero, sub_zero]
        exact (frontWeight_pos _).le
      · rw [ho, mul_one, frontLoss]
        have h := (frontWeight_pos
          (frontCount (virtualLabels init ω (s + t)) ℓ + 1)).le
        linarith
    · simp [passageWeight, passageLoss, ht]

/-- The state-dependent original-law pair rate gives the P3a contraction. -/
theorem passageWeight_conditional_drift (init : Cfg L 256) (hc : 2 ≤ init.card)
    (ℓ b s : ℕ) (hℓ : 1 ≤ ℓ) (hcap : ℓ ≤ 256 * (L + 1)) :
    ∀ t, (law init)[passageWeight init ℓ b s (t + 1) |
        shiftedFiltration (pairLogFiltration L 256) s t] ≤ᵐ[law init]
      fun ω => (1 - 1 / (3 * (init.card : ℝ))) * passageWeight init ℓ b s t ω := by
  have hZ := passageWeight_stronglyMeasurable init ℓ b s
  have hZbound : ∀ t, ∀ᵐ ω ∂law init,
      0 ≤ passageWeight init ℓ b s t ω ∧ passageWeight init ℓ b s t ω ≤ 1 :=
    fun t => ae_of_all _ (passageWeight_bounds init ℓ b s t)
  have hD := passageLoss_stronglyMeasurable init ℓ b s
  have hDbound : ∀ t, ∀ᵐ ω ∂law init,
      0 ≤ passageLoss init ℓ b s t ω ∧ passageLoss init ℓ b s t ω ≤ 1 :=
    fun t => ae_of_all _ (passageLoss_bounds init ℓ b s t)
  have hI : ∀ t,
      StronglyMeasurable[shiftedFiltration (pairLogFiltration L 256) s (t + 1)]
        (gatedIndicator init ℓ (s + t)) := by
    intro t
    simpa only [gatedIndicator, shiftedFiltration_apply, Nat.add_assoc] using
      stronglyMeasurable_aux_pair_indicator init virtualRule (GatedTick ℓ) (s + t)
  have hz : ∀ t, ∀ᵐ ω ∂law init,
      gatedIndicator init ℓ (s + t) ω = 0 ∨ gatedIndicator init ℓ (s + t) ω = 1 :=
    fun t => ae_of_all _ (gatedIndicator_zero_one init ℓ (s + t))
  have hstep : ∀ t, passageWeight init ℓ b s (t + 1) ≤ᵐ[law init]
      fun ω => passageWeight init ℓ b s t ω -
        passageLoss init ℓ b s t ω * gatedIndicator init ℓ (s + t) ω :=
    fun t => ae_of_all _ (passageWeight_step init ℓ b s t hℓ hcap)
  have hmR : (2 : ℝ) ≤ (init.card : ℝ) := by exact_mod_cast hc
  have hrate : ∀ t, ∀ᵐ ω ∂law init,
      (1 / (3 * (init.card : ℝ))) * passageWeight init ℓ b s t ω ≤
        passageLoss init ℓ b s t ω *
          ((law init)[gatedIndicator init ℓ (s + t) |
            shiftedFiltration (pairLogFiltration L 256) s t]) ω := by
    intro t
    filter_upwards [gated_conditional_sharp_floor init hc ℓ (s + t) hℓ] with ω hf
    classical
    by_cases ht : (t : WithTop ℕ) < passageStop init ℓ b s ω
    · have hw := passageWindow_of_lt_stop init ℓ b s t ω ht t le_rfl
      have htm : ω ∈ {ω | (t : WithTop ℕ) < passageStop init ℓ b s ω} := ht
      rw [passageWeight, Set.indicator_of_mem htm,
        passageLoss, Set.indicator_of_mem htm]
      have hfloor := hf hw.2.2.1 hw.2.2.2.2.2
      have hfloor' :
          2 * (frontCount (virtualLabels init ω (s + t)) ℓ : ℝ) /
              (5 * (init.card : ℝ)) ≤
            ((law init)[gatedIndicator init ℓ (s + t) |
              shiftedFiltration (pairLogFiltration L 256) s t]) ω := hfloor
      exact (frontLoss_rate_dominates
        (frontCount (virtualLabels init ω (s + t)) ℓ) hw.2.2.2.1
        (init.card : ℝ) (by linarith)).trans
          (mul_le_mul_of_nonneg_left hfloor'
            (frontLoss_bounds (frontCount (virtualLabels init ω (s + t)) ℓ)).1)
    · simp [passageWeight, passageLoss, ht]
  exact affine_conditional_drift hZ hZbound hD hDbound hI hz hstep hrate

theorem passage_survival_measurable (init : Cfg L 256)
    (ℓ b s N : ℕ) (E : Set (Ω L 256))
    (hE : MeasurableSet[pairLogFiltration L 256 s] E) :
    MeasurableSet[pairLogFiltration L 256 (s + N)]
      (E ∩ {ω | (N : WithTop ℕ) < passageStop init ℓ b s ω}) := by
  have hEend : MeasurableSet[pairLogFiltration L 256 (s + N)] E :=
    ((pairLogFiltration L 256).mono (by omega : s ≤ s + N)) _ hE
  exact hEend.inter ((passageStop_isStoppingTime init ℓ b s).measurableSet_gt N)

/-- The calibrated prefix-weighted tail has no remaining conditional-drift
premise: it is supplied by the actual gated virtual protocol above. -/
theorem reciprocal_passage_prefix_tail (init : Cfg L 256) (hc : 2 ≤ init.card)
    (ℓ b s N : ℕ) (hℓ : 1 ≤ ℓ) (hcap : ℓ ≤ 256 * (L + 1))
    (hb : 5 * b ≤ init.card)
    (E : Set (Ω L 256)) (hE : MeasurableSet[pairLogFiltration L 256 s] E)
    (hN : 30 * (init.card : ℝ) * Real.log (init.card : ℝ) ≤ (N : ℝ)) :
    law init (E ∩ {ω | (N : WithTop ℕ) < passageStop init ℓ b s ω}) ≤
      ENNReal.ofReal (1 / (init.card : ℝ) ^ 9) * law init E := by
  have hZbound : ∀ t, ∀ᵐ ω ∂law init,
      0 ≤ passageWeight init ℓ b s t ω ∧ passageWeight init ℓ b s t ω ≤ 1 :=
    fun t => ae_of_all _ (passageWeight_bounds init ℓ b s t)
  have hEs : MeasurableSet[shiftedFiltration (pairLogFiltration L 256) s 0] E := by
    simpa only [shiftedFiltration_apply, Nat.add_zero] using hE
  apply prefix_potential_calibrated_tail init.card N (by omega)
    (passageWeight_stronglyMeasurable init ℓ b s) hZbound
    (passageWeight_conditional_drift init hc ℓ b s hℓ hcap)
    E hEs {ω | (N : WithTop ℕ) < passageStop init ℓ b s ω}
    (5 * (b : ℝ)) (by positivity) (by exact_mod_cast hb) ?_ hN
  intro ω hω
  have hw := passageWindow_of_lt_stop init ℓ b s N ω hω N le_rfl
  simpa only [passageWeight, Set.indicator_of_mem hω] using
    frontWeight_boundary (frontCount (virtualLabels init ω (s + N)) ℓ)
      b hw.2.2.2.2.1

/-- The literal paper bulk threshold and first-hit horizon, on the original law. -/
theorem bulk_passage_prefix_tail (init : Cfg L 256) (hm : 20 ≤ init.card)
    (C ℓ s : ℕ) (hC : C ≤ init.card)
    (hℓ : 1 ≤ ℓ) (hcap : ℓ ≤ 256 * (L + 1))
    (E : Set (Ω L 256)) (hE : MeasurableSet[pairLogFiltration L 256 s] E) :
    law init (E ∩ {ω |
      (PhaseThreeModel.Numeric.firstHitHorizon init.card : WithTop ℕ) <
        passageStop init ℓ (StageEventSpec.bulkThreshold C) s ω}) ≤
      ENNReal.ofReal (1 / (init.card : ℝ) ^ 9) * law init E :=
  reciprocal_passage_prefix_tail init (by omega) ℓ
    (StageEventSpec.bulkThreshold C) s
    (PhaseThreeModel.Numeric.firstHitHorizon init.card) hℓ hcap
    (five_bulk_le_population init.card C hm hC) E hE (Nat.le_ceil _)

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockReciprocalPassage

end
