-- Ripple/PopulationProtocol/ExactMajority/Probability/AveragingServiceProbability.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingPotentialDrift
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingStoppedDebt

/-!
# Both-orientation service rectangles for the physical scheduler

Disjoint target and partner predicates give the exact ordered-pair rectangle
mass. The lower bound is converted to an ordinary real draw integral for
the actual killed-debt conditional law.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.AveragingServiceProbability

open TimeTheorem PairLog TraceDrain AveragingPotentialDrift

variable {L K : ℕ}

open Classical in
theorem service_rectangle (c : Cfg L K) (hn : 2 ≤ c.card)
    (P Q : AgentState L K → Prop) (E : Cfg L K → Prop)
    (hdisjoint : ∀ a, P a → ¬ Q a)
    (hservice : ∀ s t, Protocol.Applicable c s t →
      (P s ∧ Q t) ∨ (Q s ∧ P t) →
      E (Protocol.stepOrSelf (NonuniformMajority L K) c s t)) :
    (2 * (c.countP P : ℝ≥0∞) * (c.countP Q : ℝ≥0∞)) /
        (c.totalPairs : ℝ≥0∞) ≤
      (NonuniformMajority L K).transitionKernel c {c' | E c'} := by
  classical
  let g : AgentState L K → ℝ≥0∞ := fun a => if P a then 1 else 0
  have hg : ∀ a, Q a → g a = 0 := by
    intro a ha
    exact if_neg (fun hp => hdisjoint a hp ha)
  have hl := weighted_partner_probability c Q g hg
  have hr := weighted_partner_probability_reverse c Q g hg
  have hmass : Config.sumOf g c = (c.countP P : ℝ≥0∞) :=
    sumOf_indicator_eq_count c P
  have hpair (s t : AgentState L K) :
      ((if Q t then g s else 0) + (if Q s then g t else 0)) *
          c.interactionProb s t ≤
        (if E (Protocol.stepOrSelf (NonuniformMajority L K) c s t)
          then (1 : ℝ≥0∞) else 0) * c.interactionProb s t := by
    by_cases happ : Protocol.Applicable c s t
    · apply mul_le_mul_right'
      have he := hservice s t happ
      have hds : ¬ (P s ∧ Q s) := fun h => hdisjoint s h.1 h.2
      have hdt : ¬ (P t ∧ Q t) := fun h => hdisjoint t h.1 h.2
      by_cases hps : P s <;> by_cases hqs : Q s <;>
        by_cases hpt : P t <;> by_cases hqt : Q t <;> simp_all [g]
    · simp only [interactionProb_zero_of_not_applicable c s t happ, mul_zero, le_refl]
  have hE : MeasurableSet {c' : Cfg L K | E c'} :=
    (Set.to_countable _).measurableSet
  have hintegral :
      (∫⁻ c', (if E c' then (1 : ℝ≥0∞) else 0)
        ∂(NonuniformMajority L K).transitionKernel c) =
        (NonuniformMajority L K).transitionKernel c {c' | E c'} := by
    calc
      _ = ∫⁻ c', {c' : Cfg L K | E c'}.indicator (fun _ => (1 : ℝ≥0∞)) c'
          ∂(NonuniformMajority L K).transitionKernel c := by
            apply lintegral_congr
            intro c'
            simp only [Set.indicator_apply, Set.mem_setOf_eq]
      _ = _ := by rw [lintegral_indicator_const hE, one_mul]
  calc
    (2 * (c.countP P : ℝ≥0∞) * (c.countP Q : ℝ≥0∞)) /
        (c.totalPairs : ℝ≥0∞) =
        ((c.countP Q : ℝ≥0∞) / c.totalPairs) * Config.sumOf g c +
          ((c.countP Q : ℝ≥0∞) / c.totalPairs) * Config.sumOf g c := by
            rw [hmass]
            simp only [div_eq_mul_inv]
            ring
    _ = (∑ pair : AgentState L K × AgentState L K,
        ((if Q pair.2 then g pair.1 else 0) +
          (if Q pair.1 then g pair.2 else 0)) *
          c.interactionProb pair.1 pair.2) := by
            nth_rewrite 1 [← hl]
            rw [← hr, ← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro pair _
            ring
    _ ≤ ∑ pair : AgentState L K × AgentState L K,
        (if E (Protocol.stepOrSelf (NonuniformMajority L K) c pair.1 pair.2)
          then (1 : ℝ≥0∞) else 0) * c.interactionProb pair.1 pair.2 :=
      Finset.sum_le_sum fun pair _ => hpair pair.1 pair.2
    _ = _ := by
      exact (Phase0Window.lintegral_transitionKernel_eq_sum
        (NonuniformMajority L K) c hn (fun c' => if E c' then (1 : ℝ≥0∞) else 0)).symm.trans
          hintegral

open Classical in
theorem integral_draw_indicator (c : Cfg L K) (E : Cfg L K → Prop) :
    (∫ d, (if E (applyDraw c d) then (1 : ℝ) else 0) ∂(drawLaw c).toMeasure) =
      ((NonuniformMajority L K).transitionKernel c).real {c' | E c'} := by
  classical
  have hm : Measurable (applyDraw c) := measurable_of_countable _
  have hE : MeasurableSet {c' : Cfg L K | E c'} :=
    (Set.to_countable _).measurableSet
  have hD : MeasurableSet {d : Draw L K | E (applyDraw c d)} :=
    (Set.to_countable _).measurableSet
  have hi :
      (∫ d, (if E (applyDraw c d) then (1 : ℝ) else 0) ∂(drawLaw c).toMeasure) =
        ((drawLaw c).toMeasure).real {d | E (applyDraw c d)} := by
    calc
      _ = ∫ d, {d : Draw L K | E (applyDraw c d)}.indicator
          (fun _ => (1 : ℝ)) d ∂(drawLaw c).toMeasure := by
            apply integral_congr_ae
            exact ae_of_all _ fun d => by
              simp only [Set.indicator_apply, Set.mem_setOf_eq]
      _ = _ := by rw [integral_indicator_const _ hD]; simp
  rw [hi]
  unfold Measure.real
  rw [← drawLaw_map_toMeasure, Measure.map_apply hm hE]
  rfl

open Classical in
theorem service_rectangle_real (c : Cfg L K) (hn : 2 ≤ c.card)
    (P Q : AgentState L K → Prop) (E : Cfg L K → Prop)
    (hdisjoint : ∀ a, P a → ¬ Q a)
    (hservice : ∀ s t, Protocol.Applicable c s t →
      (P s ∧ Q t) ∨ (Q s ∧ P t) →
      E (Protocol.stepOrSelf (NonuniformMajority L K) c s t)) :
    (2 * (c.countP P : ℝ) * (c.countP Q : ℝ)) / (c.totalPairs : ℝ) ≤
      ∫ d, (if E (applyDraw c d) then (1 : ℝ) else 0) ∂(drawLaw c).toMeasure := by
  rw [integral_draw_indicator]
  have h := ENNReal.toReal_mono
    (measure_ne_top ((NonuniformMajority L K).transitionKernel c) {c' | E c'})
    (service_rectangle c hn P Q E hdisjoint hservice)
  simpa only [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_ofNat, Measure.real] using h

end Ripple.PopulationProtocol.ExactMajority.AveragingServiceProbability

end
