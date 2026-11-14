-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockSharpActivation.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockSmallActivation
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockWaitingProduct
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockActivationCalibration

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockSharpActivation

open TimeTheorem PairLog PhaseThreeClockVirtual PhaseThreeClockActivationLaw
  PhaseThreeClockActivationTails PhaseThreeClockMacroscopicActivation
  PhaseThreeClockPrefixTails PhaseThreeClockWaitingProduct
  PhaseThreeClockActivationCalibration

variable {L K : ℕ}

theorem activeCount_virtualLabels_measurable (init : Cfg L K) (t : ℕ) :
    Measurable[pairLogFiltration L K t]
      (fun ω => PhaseThreeClockActivationLaw.activeCount (virtualLabels init ω t)) :=
  (measurable_of_countable (fun f : Fin init.card → AgentState L K => PhaseThreeClockActivationLaw.activeCount f)).comp
    (measurable_virtualLabels init t)

theorem activationIndicator_conditional_real (init : Cfg L K)
    (hc : 2 ≤ init.card) (t : ℕ) :
    (law init)[activationIndicator init t | pairLogFiltration L K t] =ᵐ[law init]
      fun ω => activationProbability init.card (PhaseThreeClockActivationLaw.activeCount (virtualLabels init ω t)) := by
  filter_upwards [mixedActivation_conditional_law init hc t] with ω hω
  have hA := activeCount_le_card (virtualLabels init ω t)
  simpa only [activationIndicator, activationProbability, Nat.cast_mul,
    Nat.cast_sub hA, Nat.cast_ofNat] using hω

theorem activation_prefix_exponential_tail (init : Cfg L K) (hc : 2 ≤ init.card)
    (u r b N : ℕ) (theta : ℝ) (hrb : r ≤ b) (htheta : 0 ≤ theta)
    (hp : ∀ j ∈ Finset.Ico r b, 0 < activationProbability init.card j)
    (hsmall : ∀ j ∈ Finset.Ico r b,
      theta / activationProbability init.card j ≤ (1 / 1000 : ℝ))
    (E : Set (Ω L K)) (hE : MeasurableSet[pairLogFiltration L K u] E)
    (hstart : ∀ ω ∈ E, r ≤ PhaseThreeClockActivationLaw.activeCount (virtualLabels init ω u)) :
    law init (E ∩ {ω | PhaseThreeClockActivationLaw.activeCount (virtualLabels init ω (u + N)) < b}) ≤
      ENNReal.ofReal (Real.exp ((1000 / 999 : ℝ) * theta *
        (∑ j ∈ Finset.Ico r b, 1 / activationProbability init.card j) -
          theta * (N : ℝ))) * law init E := by
  let A : ℕ → Ω L K → ℕ := fun t ω => PhaseThreeClockActivationLaw.activeCount (virtualLabels init ω (u + t))
  let I : ℕ → Ω L K → ℝ := fun t => activationIndicator init (u + t)
  let ℱ := shiftedFiltration (pairLogFiltration L K) u
  have hA : ∀ t, Measurable[ℱ t] (A t) :=
    fun t => activeCount_virtualLabels_measurable init (u + t)
  have hmono : ∀ t ω, A t ω ≤ A (t + 1) ω := by
    intro t ω
    exact activeCount_virtualLabels_mono init ω (by omega : u + t ≤ u + (t + 1))
  have hI : ∀ t, StronglyMeasurable[ℱ (t + 1)] (I t) := by
    intro t
    simpa only [I, ℱ, shiftedFiltration_apply, Nat.add_assoc, activationIndicator] using
      mixedActivation_stronglyMeasurable init (u + t)
  have hz : ∀ t, ∀ᵐ ω ∂law init, I t ω = 0 ∨ I t ω = 1 :=
    fun t => ae_of_all _ (activationIndicator_zero_one init (u + t))
  have hinc : ∀ t, ∀ᵐ ω ∂law init,
      I t ω ≤ (A (t + 1) ω : ℝ) - (A t ω : ℝ) := by
    intro t
    apply ae_of_all
    intro ω
    have hstep := activeCount_virtualLabels_increment init ω (u + t)
    have hstep' : activationIndicator init (u + t) ω ≤
        (PhaseThreeClockActivationLaw.activeCount (virtualLabels init ω (u + t + 1)) : ℝ) -
          (PhaseThreeClockActivationLaw.activeCount (virtualLabels init ω (u + t)) : ℝ) := by
      change (PhaseThreeClockActivationLaw.activeCount (virtualLabels init ω (u + t)) : ℝ) +
        activationIndicator init (u + t) ω ≤ _ at hstep
      linarith
    simpa only [I, A, Nat.add_assoc] using hstep'
  have hrate : ∀ t, ∀ᵐ ω ∂law init,
      r ≤ A t ω → A t ω < b →
        activationProbability init.card (A t ω) ≤ (law init)[I t | ℱ t] ω := by
    intro t
    filter_upwards [activationIndicator_conditional_real init hc (u + t)] with ω hω
    intro _ _
    exact hω.symm.le
  have hEs : MeasurableSet[ℱ 0] E := by
    simpa only [ℱ, shiftedFiltration_apply, Nat.add_zero] using hE
  exact waiting_product_prefix_exponential_tail A I (activationProbability init.card)
    r b N theta hrb htheta hp hsmall hA hmono hI hz hinc hrate E hEs
    (by simpa only [A, Nat.add_zero] using hstart)

theorem sharp_activation_prefix_tail (init : Cfg L K) (C u : ℕ)
    (hn : PhaseThreeModel.Numeric.populationThreshold ≤ init.card)
    (hlo : (6 / 25 : ℝ) * (init.card : ℝ) ≤ (C : ℝ)) (hCn : C ≤ init.card)
    (E : Set (Ω L K)) (hE : MeasurableSet[pairLogFiltration L K u] E)
    (hstart : ∀ ω ∈ E, PhaseThreeModel.Numeric.smallActivation C ≤
      PhaseThreeClockActivationLaw.activeCount (virtualLabels init ω u)) :
    law init (E ∩ {ω | PhaseThreeClockActivationLaw.activeCount
      (virtualLabels init ω (u + PhaseThreeModel.Numeric.activationHalfHorizon init.card)) <
        macroscopicThreshold init.card}) ≤
      ENNReal.ofReal (1 / (C : ℝ) ^ 100) * law init E := by
  have hd := activation_calibration_data hn hlo hCn
  have hm := hd.population_large
  obtain ⟨hθ, hp⟩ := activation_rate_mgf_inputs hn hlo hCn
  have ht := activation_prefix_exponential_tail init (by omega) u
    (PhaseThreeModel.Numeric.smallActivation C) (macroThreshold init.card)
    (PhaseThreeModel.Numeric.activationHalfHorizon init.card) (activationTheta init.card C)
    hd.small_le_macro hθ (fun j hj => (hp j hj).1) (fun j hj => (hp j hj).2) E hE hstart
  apply ht.trans
  exact mul_le_mul_right'
    (ENNReal.ofReal_le_ofReal (activation_mgf_coefficient_calibration hn hlo hCn)) _

theorem macroscopicTime_gt_iff_count (init : Cfg L K) (s t : ℕ) (hst : s ≤ t)
    (ω : Ω L K) :
    (t : WithTop ℕ) < macroscopicTime init s ω ↔
      PhaseThreeClockActivationLaw.activeCount (virtualLabels init ω t) < macroscopicThreshold init.card := by
  constructor
  · intro hlate
    by_contra hnot
    have hge : macroscopicThreshold init.card ≤ PhaseThreeClockActivationLaw.activeCount (virtualLabels init ω t) := by
      omega
    have hle := (macroscopicTime_le_iff init s t ω).2 ⟨t, le_rfl, hst, hge⟩
    exact (not_lt_of_ge hle) hlate
  · intro hcount
    apply lt_of_not_ge
    intro hle
    obtain ⟨v, hvt, -, hlarge⟩ := (macroscopicTime_le_iff init s t ω).1 hle
    have hmono : PhaseThreeClockActivationLaw.activeCount (virtualLabels init ω v) ≤
        PhaseThreeClockActivationLaw.activeCount (virtualLabels init ω t) :=
      activeCount_virtualLabels_mono init ω hvt
    omega

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockSharpActivation

end
