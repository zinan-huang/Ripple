-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockActivationTails.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockActivationLaw
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockPotentialTail

/-!
# Activation from an observed positive seed, under the original law

The potential 1/A - 1/m contracts at rate 1 - 1/m, where A counts
phase-at-least-three labels and m is the population. Its reciprocal loss
uses the exact mixed-pair rate, so no first-half/second-half split is needed.
After ceil(7 m log m) interactions the failure probability is at most m^-5,
with the probability of the observed prefix retained.

Backup labels are active for this threshold process. The final bridge to
exact Phase 3 therefore states the current phase-upper-bound alternative
explicitly; it does not assume future safety in a prefix event.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockActivationTails

open TimeTheorem PairLog PairLogAuxiliary PhaseThreeClockVirtual
  PhaseThreeClockActivationLaw PhaseThreeClockPrefixTails
  PhaseThreeClockPotentialTail

variable {L K : ℕ}

def activationWeight (m A : ℝ) : ℝ := 1 / A - 1 / m

def activationLoss (A : ℝ) : ℝ := 1 / (A * (A + 1))

theorem activationWeight_bounds (m A : ℝ)
    (hm : 2 ≤ m) (hA : 1 ≤ A) (hAm : A ≤ m) :
    0 ≤ activationWeight m A ∧ activationWeight m A ≤ 1 := by
  have hApos : 0 < A := by linarith
  have hmpos : 0 < m := by linarith
  have hlow := one_div_le_one_div_of_le hApos hAm
  have hhigh : 1 / A ≤ (1 : ℝ) := (div_le_iff₀ hApos).2 (by linarith)
  have hnonneg : 0 ≤ (1 : ℝ) / m := by positivity
  dsimp only [activationWeight]
  constructor <;> linarith

theorem activationLoss_bounds (A : ℝ) (hA : 1 ≤ A) :
    0 ≤ activationLoss A ∧ activationLoss A ≤ 1 := by
  have hApos : 0 < A := by linarith
  have hden : 0 < A * (A + 1) := by positivity
  have hlarge : 1 ≤ A * (A + 1) := by nlinarith [sq_nonneg A]
  dsimp only [activationLoss]
  exact ⟨by positivity, (div_le_iff₀ hden).2 (by simpa using hlarge)⟩

theorem activationWeight_antitone (m A B : ℝ) (hA : 0 < A) (hAB : A ≤ B) :
    activationWeight m B ≤ activationWeight m A := by
  dsimp only [activationWeight]
  linarith [one_div_le_one_div_of_le hA hAB]

theorem activationWeight_sub_succ (m A : ℝ) (hA : 0 < A) :
    activationWeight m (A + 1) = activationWeight m A - activationLoss A := by
  have hAone : A + 1 ≠ 0 := by positivity
  have hrec : (1 : ℝ) / (A + 1) = 1 / A - 1 / (A * (A + 1)) := by
    field_simp [ne_of_gt hA, hAone]
    <;> ring
  dsimp only [activationWeight, activationLoss]
  linarith

/-- This inequality uses the true two-orientation mixed-pair probability. -/
theorem activationWeight_drift_rate (m A : ℝ)
    (hm : 2 ≤ m) (hA : 1 ≤ A) (hAm : A ≤ m) :
    (1 / m) * activationWeight m A ≤
      activationLoss A * (2 * A * (m - A) / (m * (m - 1))) := by
  have hmpos : 0 < m := by linarith
  have hApos : 0 < A := by linarith
  have hmone : 0 < m - 1 := by linarith
  have hAone : 0 < A + 1 := by linarith
  have hden : 0 < m ^ 2 * A * (A + 1) * (m - 1) := by positivity
  have hsmall : (m - 1) * (A + 1) ≤ 2 * m * A := by
    nlinarith [mul_nonneg hmpos.le (sub_nonneg.mpr hA)]
  have hnum :
      (m - A) * (A + 1) * (m - 1) ≤ 2 * m * A * (m - A) := by
    nlinarith only [mul_le_mul_of_nonneg_right hsmall (sub_nonneg.mpr hAm)]
  have hleft :
      (1 / m) * activationWeight m A =
        ((m - A) * (A + 1) * (m - 1)) /
          (m ^ 2 * A * (A + 1) * (m - 1)) := by
    dsimp only [activationWeight]
    field_simp [ne_of_gt hmpos, ne_of_gt hApos, ne_of_gt hmone, ne_of_gt hAone]
    <;> ring
  have hright :
      activationLoss A * (2 * A * (m - A) / (m * (m - 1))) =
        (2 * m * A * (m - A)) /
          (m ^ 2 * A * (A + 1) * (m - 1)) := by
    dsimp only [activationLoss]
    field_simp [ne_of_gt hmpos, ne_of_gt hApos, ne_of_gt hmone, ne_of_gt hAone]
    <;> ring
  rw [hleft, hright]
  exact div_le_div_of_nonneg_right hnum hden.le

theorem activationWeight_boundary (m A : ℝ)
    (hm : 2 ≤ m) (hA : 1 ≤ A) (hAm : A + 1 ≤ m) :
    1 ≤ m ^ 2 * activationWeight m A := by
  have hmpos : 0 < m := by linarith
  have hApos : 0 < A := by linarith
  have heq : m ^ 2 * activationWeight m A = m * (m - A) / A := by
    dsimp only [activationWeight]
    field_simp [ne_of_gt hmpos, ne_of_gt hApos]
    <;> ring
  rw [heq]
  apply (le_div_iff₀ hApos).2
  have hp := mul_le_mul_of_nonneg_left (by linarith : (1 : ℝ) ≤ m - A) hmpos.le
  nlinarith

def hasActiveAt (init : Cfg L K) (s : ℕ) : Set (Ω L K) :=
  {ω | 1 ≤ PhaseThreeClockActivationLaw.activeCount (virtualLabels init ω s)}

noncomputable def activePotential (init : Cfg L K) (s t : ℕ) : Ω L K → ℝ :=
  (hasActiveAt init s).indicator (fun ω =>
    activationWeight (init.card : ℝ)
      (PhaseThreeClockActivationLaw.activeCount (virtualLabels init ω (s + t)) : ℝ))

noncomputable def activeLoss (init : Cfg L K) (s t : ℕ) : Ω L K → ℝ :=
  (hasActiveAt init s).indicator (fun ω =>
    activationLoss (PhaseThreeClockActivationLaw.activeCount (virtualLabels init ω (s + t)) : ℝ))

noncomputable def activationIndicator (init : Cfg L K) (t : ℕ) : Ω L K → ℝ := by
  classical
  exact fun ω => if ∃ i j, drawLabels init ω (t + 1) = some (i, j) ∧
    MixedActivation (virtualLabels init ω t) i j then 1 else 0

theorem hasActiveAt_measurable (init : Cfg L K) (s : ℕ) :
    MeasurableSet[pairLogFiltration L K s] (hasActiveAt init s) := by
  exact (measurable_virtualLabels init s)
    (Set.to_countable {f : Fin init.card → AgentState L K | 1 ≤ PhaseThreeClockActivationLaw.activeCount f}).measurableSet

theorem activePotential_stronglyMeasurable (init : Cfg L K) (s t : ℕ) :
    StronglyMeasurable[shiftedFiltration (pairLogFiltration L K) s t]
      (activePotential init s t) := by
  have hstate := (measurable_aux_potential init virtualRule
    (fun f => activationWeight (init.card : ℝ) (PhaseThreeClockActivationLaw.activeCount f : ℝ)) (s + t)).stronglyMeasurable
  exact hstate.indicator
    (((pairLogFiltration L K).mono (by omega : s ≤ s + t)) _
      (hasActiveAt_measurable init s))

theorem activeLoss_stronglyMeasurable (init : Cfg L K) (s t : ℕ) :
    StronglyMeasurable[shiftedFiltration (pairLogFiltration L K) s t]
      (activeLoss init s t) := by
  have hstate := (measurable_aux_potential init virtualRule
    (fun f => activationLoss (PhaseThreeClockActivationLaw.activeCount f : ℝ)) (s + t)).stronglyMeasurable
  exact hstate.indicator
    (((pairLogFiltration L K).mono (by omega : s ≤ s + t)) _
      (hasActiveAt_measurable init s))

theorem activeCount_pos_of_seed (init : Cfg L K) (s t : ℕ) (ω : Ω L K)
    (hω : ω ∈ hasActiveAt init s) :
    1 ≤ PhaseThreeClockActivationLaw.activeCount (virtualLabels init ω (s + t)) :=
  hω.trans (activeCount_virtualLabels_mono init ω (by omega : s ≤ s + t))

theorem activePotential_bounds (init : Cfg L K) (hc : 2 ≤ init.card)
    (s t : ℕ) (ω : Ω L K) :
    0 ≤ activePotential init s t ω ∧ activePotential init s t ω ≤ 1 := by
  classical
  by_cases hω : ω ∈ hasActiveAt init s
  · rw [activePotential, Set.indicator_of_mem hω]
    exact activationWeight_bounds _ _ (by exact_mod_cast hc)
      (by exact_mod_cast activeCount_pos_of_seed init s t ω hω)
      (by exact_mod_cast activeCount_le_card (virtualLabels init ω (s + t)))
  · simp [activePotential, hω]

theorem activeLoss_bounds (init : Cfg L K) (s t : ℕ) (ω : Ω L K) :
    0 ≤ activeLoss init s t ω ∧ activeLoss init s t ω ≤ 1 := by
  classical
  by_cases hω : ω ∈ hasActiveAt init s
  · rw [activeLoss, Set.indicator_of_mem hω]
    exact activationLoss_bounds _
      (by exact_mod_cast activeCount_pos_of_seed init s t ω hω)
  · simp [activeLoss, hω]

theorem activationIndicator_zero_one (init : Cfg L K) (t : ℕ) (ω : Ω L K) :
    activationIndicator init t ω = 0 ∨ activationIndicator init t ω = 1 := by
  classical
  unfold activationIndicator
  split_ifs <;> simp

theorem activePotential_step (init : Cfg L K) (s t : ℕ) (ω : Ω L K) :
    activePotential init s (t + 1) ω ≤
      activePotential init s t ω - activeLoss init s t ω *
        activationIndicator init (s + t) ω := by
  classical
  by_cases hω : ω ∈ hasActiveAt init s
  · rw [activePotential, Set.indicator_of_mem hω,
      activePotential, Set.indicator_of_mem hω,
      activeLoss, Set.indicator_of_mem hω]
    have hA : (0 : ℝ) < (PhaseThreeClockActivationLaw.activeCount (virtualLabels init ω (s + t)) : ℝ) := by
      have h := activeCount_pos_of_seed init s t ω hω
      exact_mod_cast (by omega : 0 < PhaseThreeClockActivationLaw.activeCount (virtualLabels init ω (s + t)))
    have hinc :
        (PhaseThreeClockActivationLaw.activeCount (virtualLabels init ω (s + t)) : ℝ) +
            activationIndicator init (s + t) ω ≤
          (PhaseThreeClockActivationLaw.activeCount (virtualLabels init ω (s + (t + 1))) : ℝ) := by
      simpa only [activationIndicator, Nat.add_assoc] using
        activeCount_virtualLabels_increment init ω (s + t)
    rcases activationIndicator_zero_one init (s + t) ω with hz | ho
    · rw [hz, mul_zero, sub_zero]
      apply activationWeight_antitone _ _ _ hA
      simpa only [hz, add_zero] using hinc
    · rw [ho, mul_one]
      calc
        activationWeight (init.card : ℝ)
            (PhaseThreeClockActivationLaw.activeCount (virtualLabels init ω (s + (t + 1))) : ℝ) ≤
            activationWeight (init.card : ℝ)
              ((PhaseThreeClockActivationLaw.activeCount (virtualLabels init ω (s + t)) : ℝ) + 1) :=
          activationWeight_antitone _ _ _ (by positivity)
            (by simpa only [ho] using hinc)
        _ = _ := activationWeight_sub_succ _ _ hA
  · simp [activePotential, activeLoss, hω]

theorem activePotential_conditional_drift (init : Cfg L K)
    (hc : 2 ≤ init.card) (s : ℕ) :
    ∀ t, (law init)[activePotential init s (t + 1) |
        shiftedFiltration (pairLogFiltration L K) s t] ≤ᵐ[law init]
      fun ω => (1 - 1 / (init.card : ℝ)) * activePotential init s t ω := by
  have hZ := activePotential_stronglyMeasurable init s
  have hZb : ∀ t, ∀ᵐ ω ∂law init,
      0 ≤ activePotential init s t ω ∧ activePotential init s t ω ≤ 1 :=
    fun t => ae_of_all _ (activePotential_bounds init hc s t)
  have hD := activeLoss_stronglyMeasurable init s
  have hDb : ∀ t, ∀ᵐ ω ∂law init,
      0 ≤ activeLoss init s t ω ∧ activeLoss init s t ω ≤ 1 :=
    fun t => ae_of_all _ (activeLoss_bounds init s t)
  have hI : ∀ t,
      StronglyMeasurable[shiftedFiltration (pairLogFiltration L K) s (t + 1)]
        (activationIndicator init (s + t)) := by
    intro t
    simpa only [activationIndicator, shiftedFiltration_apply, Nat.add_assoc] using
      mixedActivation_stronglyMeasurable init (s + t)
  have hz : ∀ t, ∀ᵐ ω ∂law init,
      activationIndicator init (s + t) ω = 0 ∨ activationIndicator init (s + t) ω = 1 :=
    fun t => ae_of_all _ (activationIndicator_zero_one init (s + t))
  have hstep : ∀ t, activePotential init s (t + 1) ≤ᵐ[law init]
      fun ω => activePotential init s t ω -
        activeLoss init s t ω * activationIndicator init (s + t) ω :=
    fun t => ae_of_all _ (activePotential_step init s t)
  have hrate : ∀ t, ∀ᵐ ω ∂law init,
      (1 / (init.card : ℝ)) * activePotential init s t ω ≤
        activeLoss init s t ω *
          ((law init)[activationIndicator init (s + t) |
            shiftedFiltration (pairLogFiltration L K) s t]) ω := by
    intro t
    filter_upwards [mixedActivation_conditional_law init hc (s + t)] with ω hce
    classical
    by_cases hω : ω ∈ hasActiveAt init s
    · rw [activePotential, Set.indicator_of_mem hω,
        activeLoss, Set.indicator_of_mem hω]
      have hAm := activeCount_le_card (virtualLabels init ω (s + t))
      have hce' :
          ((law init)[activationIndicator init (s + t) |
            shiftedFiltration (pairLogFiltration L K) s t]) ω =
            2 * (PhaseThreeClockActivationLaw.activeCount (virtualLabels init ω (s + t)) : ℝ) *
                ((init.card : ℝ) -
                  (PhaseThreeClockActivationLaw.activeCount (virtualLabels init ω (s + t)) : ℝ)) /
              ((init.card : ℝ) * ((init.card : ℝ) - 1)) := by
        simpa only [activationIndicator, shiftedFiltration_apply,
          Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub hAm] using hce
      rw [hce']
      exact activationWeight_drift_rate _ _ (by exact_mod_cast hc)
        (by exact_mod_cast activeCount_pos_of_seed init s t ω hω)
        (by exact_mod_cast hAm)
    · simp [activePotential, activeLoss, hω]
  exact affine_conditional_drift hZ hZb hD hDb hI hz hstep hrate

theorem activation_contraction_nonneg (m : ℕ) (hm : 2 ≤ m) :
    (0 : ℝ) ≤ 1 - 1 / (m : ℝ) := by
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < (m : ℝ) := by linarith
  have hfrac : 1 / (m : ℝ) ≤ (1 : ℝ) :=
    (div_le_iff₀ hmpos).2 (by linarith)
  linarith

theorem activation_contraction_pow_le_exp (m N : ℕ) (hm : 2 ≤ m) :
    (1 - 1 / (m : ℝ)) ^ N ≤ Real.exp (-(N : ℝ) / (m : ℝ)) := by
  have hbase : 1 - 1 / (m : ℝ) ≤ Real.exp (-(1 / (m : ℝ))) := by
    simpa only [sub_eq_add_neg, add_comm] using
      Real.add_one_le_exp (-(1 / (m : ℝ)))
  calc
    (1 - 1 / (m : ℝ)) ^ N ≤ (Real.exp (-(1 / (m : ℝ)))) ^ N :=
      pow_le_pow_left₀ (activation_contraction_nonneg m hm) hbase N
    _ = Real.exp (-(N : ℝ) / (m : ℝ)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

theorem activation_tail_calibration (m N : ℕ) (hm : 2 ≤ m)
    (hN : 7 * (m : ℝ) * Real.log (m : ℝ) ≤ (N : ℝ)) :
    (m : ℝ) ^ 2 * (1 - 1 / (m : ℝ)) ^ N ≤ 1 / (m : ℝ) ^ 5 := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hratio : 7 * Real.log (m : ℝ) ≤ (N : ℝ) / (m : ℝ) := by
    apply (le_div_iff₀ hmpos).2
    nlinarith
  have hexp : Real.exp (7 * Real.log (m : ℝ)) = (m : ℝ) ^ 7 := by
    change Real.exp ((7 : ℕ) * Real.log (m : ℝ)) = _
    rw [Real.exp_nat_mul, Real.exp_log hmpos]
  have hlast :
      (m : ℝ) ^ 2 * Real.exp (-(7 * Real.log (m : ℝ))) = 1 / (m : ℝ) ^ 5 := by
    rw [Real.exp_neg, hexp]
    field_simp [ne_of_gt hmpos]
    <;> ring
  calc
    (m : ℝ) ^ 2 * (1 - 1 / (m : ℝ)) ^ N ≤
        (m : ℝ) ^ 2 * Real.exp (-(N : ℝ) / (m : ℝ)) :=
      mul_le_mul_of_nonneg_left (activation_contraction_pow_le_exp m N hm) (sq_nonneg _)
    _ ≤ (m : ℝ) ^ 2 * Real.exp (-(7 * Real.log (m : ℝ))) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by rw [neg_div]; linarith)) (sq_nonneg _)
    _ = _ := hlast

def activationHorizon (m : ℕ) : ℕ :=
  Nat.ceil (7 * (m : ℝ) * Real.log (m : ℝ))

def activationFailure (init : Cfg L K) (s N : ℕ) : Set (Ω L K) :=
  {ω | PhaseThreeClockActivationLaw.activeCount (virtualLabels init ω (s + N)) < init.card}

theorem activationFailure_measurable (init : Cfg L K) (s N : ℕ) :
    MeasurableSet[pairLogFiltration L K (s + N)] (activationFailure init s N) :=
  (measurable_virtualLabels init (s + N))
    (Set.to_countable {f : Fin init.card → AgentState L K |
      PhaseThreeClockActivationLaw.activeCount f < init.card}).measurableSet

/-- Original-law activation tail from any observed positive seed. -/
theorem activation_prefix_tail (init : Cfg L K) (hc : 2 ≤ init.card)
    (s N : ℕ) (E : Set (Ω L K))
    (hE : MeasurableSet[pairLogFiltration L K s] E)
    (hseed : E ⊆ hasActiveAt init s)
    (hN : 7 * (init.card : ℝ) * Real.log (init.card : ℝ) ≤ (N : ℝ)) :
    law init (E ∩ activationFailure init s N) ≤
      ENNReal.ofReal (1 / (init.card : ℝ) ^ 5) * law init E := by
  let B := hasActiveAt init s ∩ activationFailure init s N
  have hZb : ∀ t, ∀ᵐ ω ∂law init,
      0 ≤ activePotential init s t ω ∧ activePotential init s t ω ≤ 1 :=
    fun t => ae_of_all _ (activePotential_bounds init hc s t)
  have hEs : MeasurableSet[shiftedFiltration (pairLogFiltration L K) s 0] E := by
    simpa only [shiftedFiltration_apply, Nat.add_zero] using hE
  have hB : ∀ ω ∈ B, 1 ≤ (init.card : ℝ) ^ 2 * activePotential init s N ω := by
    rintro ω ⟨hω, hf⟩
    rw [activePotential, Set.indicator_of_mem hω]
    have hlt : PhaseThreeClockActivationLaw.activeCount (virtualLabels init ω (s + N)) < init.card := hf
    exact activationWeight_boundary _ _ (by exact_mod_cast hc)
      (by exact_mod_cast activeCount_pos_of_seed init s N ω hω)
      (by exact_mod_cast (by omega :
        PhaseThreeClockActivationLaw.activeCount (virtualLabels init ω (s + N)) + 1 ≤ init.card))
  have htail := prefix_potential_tail_ennreal
    (activePotential_stronglyMeasurable init s) hZb
    (activation_contraction_nonneg init.card hc)
    (activePotential_conditional_drift init hc s)
    E hEs N B ((init.card : ℝ) ^ 2) (sq_nonneg _) hB
  have heq : E ∩ B = E ∩ activationFailure init s N := by
    ext ω
    constructor
    · exact fun h => ⟨h.1, h.2.2⟩
    · exact fun h => ⟨h.1, hseed h.1, h.2⟩
  rw [heq] at htail
  exact htail.trans (mul_le_mul_right'
    (ENNReal.ofReal_le_ofReal (activation_tail_calibration init.card N hc hN)) _)

theorem activation_prefix_calibrated (init : Cfg L K) (hc : 2 ≤ init.card)
    (s : ℕ) (E : Set (Ω L K))
    (hE : MeasurableSet[pairLogFiltration L K s] E)
    (hseed : E ⊆ hasActiveAt init s) :
    law init (E ∩ activationFailure init s (activationHorizon init.card)) ≤
      ENNReal.ofReal (1 / (init.card : ℝ) ^ 5) * law init E :=
  activation_prefix_tail init hc s _ E hE hseed (Nat.le_ceil _)

/-- Failure of exact Phase 3 while every current phase is at most three
is contained in threshold-activation failure. The upper-bound event is
at the deadline, not imposed as a future-conditioned prefix. -/
theorem exact_phase_failure_subset (init : Cfg L K) (s N : ℕ) :
    {ω | (∀ i, (virtualLabels init ω (s + N) i).phase.val ≤ 3) ∧
      ¬ ∀ i, (virtualLabels init ω (s + N) i).phase.val = 3} ⊆
      activationFailure init s N := by
  intro ω hω
  change PhaseThreeClockActivationLaw.activeCount (virtualLabels init ω (s + N)) < init.card
  have hle := activeCount_le_card (virtualLabels init ω (s + N))
  by_contra hnot
  have heq : PhaseThreeClockActivationLaw.activeCount (virtualLabels init ω (s + N)) = init.card := by omega
  exact hω.2 (phase_three_of_activeCount_eq_card _ heq hω.1)

theorem exact_phase_prefix_tail (init : Cfg L K) (hc : 2 ≤ init.card)
    (s : ℕ) (E : Set (Ω L K))
    (hE : MeasurableSet[pairLogFiltration L K s] E)
    (hseed : E ⊆ hasActiveAt init s) :
    law init (E ∩ {ω |
      (∀ i, (virtualLabels init ω (s + activationHorizon init.card) i).phase.val ≤ 3) ∧
      ¬ ∀ i, (virtualLabels init ω (s + activationHorizon init.card) i).phase.val = 3}) ≤
      ENNReal.ofReal (1 / (init.card : ℝ) ^ 5) * law init E :=
  (measure_mono (Set.inter_subset_inter (subset_refl E)
    (exact_phase_failure_subset init s (activationHorizon init.card)))).trans
      (activation_prefix_calibrated init hc s E hE hseed)

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockActivationTails

end
