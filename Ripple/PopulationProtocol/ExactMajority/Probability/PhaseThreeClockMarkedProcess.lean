-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockMarkedProcess.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockMarkedCompensator
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockCompensatedMarks
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockImmigrationOpportunity

noncomputable section
open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockMarkedProcess

open TimeTheorem PairLog PhaseThreeScalar PhaseThreeClockPrefixTails
  PhaseThreeClockVirtual PhaseThreeClockGatedLaw PhaseThreeClockThinning
  PhaseThreeClockEarlyMarks PhaseThreeClockEarlyMarkRates PhaseThreeClockEarlyMarkEmbedding
  PhaseThreeClockImmigrationTails PhaseThreeClockMarkedClockRates
  PhaseThreeClockMarkedWindow PhaseThreeClockMarkedCompensator
  PhaseThreeClockTwoPeriodIndicators PhaseThreeClockCompensatedMarks
  PhaseThreeClockImmigrationOpportunity PhaseThreeClockActivationSeed PhaseThreeClockSeedTails

variable {L K : ℕ}

def markedMass (init : Cfg L K) (C : Finset (Fin init.card))
    (ℓ cutoff s u t : ℕ) (ω : Ω L K) : ℝ :=
  ((markedAt init C ℓ cutoff s ω (u + t)).card : ℝ)

def chargedImmigration (init : Cfg L K) (C : Finset (Fin init.card))
    (ℓ cutoff s u N t : ℕ) : Ω L K → ℝ :=
  periodCharge (rawSet init s u N t) (lateSet init s ℓ u N t)
    (maskedImmigrationIndicator init C ℓ cutoff (u + t))

def chargedPropagation (init : Cfg L K) (C : Finset (Fin init.card))
    (ℓ cutoff s u N t : ℕ) : Ω L K → ℝ :=
  periodCharge (rawSet init s u N t) (lateSet init s ℓ u N t)
    (propagationIndicator init C ℓ cutoff s (u + t))

theorem chargedImmigration_adapted (init : Cfg L K) (C : Finset (Fin init.card))
    (ℓ cutoff s u N t : ℕ) :
    StronglyMeasurable[shiftedFiltration (pairLogFiltration L K) u (t + 1)]
      (chargedImmigration init C ℓ cutoff s u N t) := by
  apply periodCharge_stronglyMeasurable t _ _ (rawSet_measurable init s u N t)
    (lateSet_measurable init s ℓ u N t)
  simpa only [shiftedFiltration_apply, Nat.add_assoc] using
    maskedImmigration_indicator_stronglyMeasurable init C ℓ cutoff (u + t)

theorem chargedPropagation_adapted (init : Cfg L K) (C : Finset (Fin init.card))
    (ℓ cutoff s u N t : ℕ) :
    StronglyMeasurable[shiftedFiltration (pairLogFiltration L K) u (t + 1)]
      (chargedPropagation init C ℓ cutoff s u N t) := by
  apply periodCharge_stronglyMeasurable t _ _ (rawSet_measurable init s u N t)
    (lateSet_measurable init s ℓ u N t)
  simpa only [shiftedFiltration_apply, Nat.add_assoc] using
    propagation_indicator_stronglyMeasurable init C ℓ cutoff s (u + t)

theorem chargedPropagation_conditional_rate (init : Cfg L K)
    (C : Finset (Fin init.card)) (ℓ cutoff s u N t : ℕ)
    (hn : 561 ≤ init.card) (hC : 2 ≤ C.card) (hupper : 25 * C.card ≤ 7 * init.card) :
    (law init)[chargedPropagation init C ℓ cutoff s u N t |
      shiftedFiltration (pairLogFiltration L K) u t] ≤ᵐ[law init] fun ω =>
      (law init)[markedOpportunity init C s ℓ u N t |
        shiftedFiltration (pairLogFiltration L K) u t] ω *
      markedRate init s u N ((561 / 1000 : ℝ) / init.card)
        (2 / ((C.card : ℝ) - 1)) t ω * markedMass init C ℓ cutoff s u t ω := by
  have hPi := bernoulli_integrable (μ := law init) (propagation_indicator_stronglyMeasurable init C ℓ cutoff s)
    (fun v => ae_of_all _ (propagation_indicator_bernoulli init C ℓ cutoff s v)) (u + t)
  have hJi := bernoulli_integrable (μ := law init) (maskTickIndicator_stronglyMeasurable init C)
    (fun v => ae_of_all _ (maskTickIndicator_zero_one init C v)) (u + t)
  apply periodCharge_conditional_rate t _ _ (rawSet_measurable init s u N t)
    (lateSet_measurable init s ℓ u N t) (rawSet_lateSet_disjoint init s ℓ u N t)
    _ _ _ _ _ hPi hJi
  · exact propagation_conditional_bound init C ℓ cutoff s (u + t) hn hupper
  · filter_upwards [propagation_conditional_clock_bound init (by omega) C hC ℓ cutoff s (u + t),
      maskTickIndicator_conditional_law init (by omega) C (u + t)] with ω hp hj
    change (law init)[propagationIndicator init C ℓ cutoff s (u + t) |
      pairLogFiltration L K (u + t)] ω ≤
      (law init)[maskTickIndicator init C (u + t) | pairLogFiltration L K (u + t)] ω *
        (2 / ((C.card : ℝ) - 1)) * markedMass init C ℓ cutoff s u t ω
    rw [hj]
    exact hp

def actualMarkData (init : Cfg L K) (C : Finset (Fin init.card))
    (ℓ cutoff s u N a : ℕ) (hn : 561 ≤ init.card) (hC : 2 ≤ C.card)
    (hupper : 25 * C.card ≤ 7 * init.card) (ha : 1 ≤ a) :
    CompensatedMarkData (law init) (shiftedFiltration (pairLogFiltration L K) u) a where
  order_pos := ha
  markCount := markedMass init C ℓ cutoff s u
  immigration := chargedImmigration init C ℓ cutoff s u N
  propagation := chargedPropagation init C ℓ cutoff s u N
  opportunity := markedOpportunity init C s ℓ u N
  rate := markedRate init s u N ((561 / 1000 : ℝ) / init.card) (2 / ((C.card : ℝ) - 1))
  initialUpper := (C.card : ℝ)
  mark_adapted := fun t => markedCount_stronglyMeasurable init C ℓ cutoff s (u + t)
  immigration_adapted := chargedImmigration_adapted init C ℓ cutoff s u N
  propagation_adapted := chargedPropagation_adapted init C ℓ cutoff s u N
  opportunity_adapted := markedOpportunity_stronglyMeasurable init C s ℓ u N
  rate_adapted := markedRate_stronglyMeasurable init s u N _ _
  mark_nonneg := fun _ _ => Nat.cast_nonneg _
  initial_bound := fun ω => by
    change ((markedAt init C ℓ cutoff s ω (u + 0)).card : ℝ) ≤ (C.card : ℝ)
    exact_mod_cast Finset.card_le_card (markedAt_subset_mask init C ℓ cutoff s ω (u + 0))
  rate_nonneg := by
    apply markedRate_nonneg
    · positivity
    · have hc : (2 : ℝ) ≤ C.card := by exact_mod_cast hC
      exact div_nonneg (by norm_num) (by linarith)
  immigration_bernoulli := fun t =>
    periodCharge_zero_one _ _ _ (maskedImmigration_indicator_bernoulli init C ℓ cutoff (u + t))
  propagation_bernoulli := fun t =>
    periodCharge_zero_one _ _ _ (propagation_indicator_bernoulli init C ℓ cutoff s (u + t))
  opportunity_bernoulli := markedOpportunity_zero_one init C s ℓ u N
  propagation_le_opportunity := fun t =>
    periodCharge_le_opportunity _ _ _ _ (rawSet_lateSet_disjoint init s ℓ u N t)
      (propagation_indicator_bernoulli init C ℓ cutoff s (u + t))
      (propagationIndicator_le_clockTick init C ℓ cutoff s (u + t))
  conditional_propagation :=
    fun t => chargedPropagation_conditional_rate init C ℓ cutoff s u N t hn hC hupper

theorem chargedImmigration_conditional_rate (init : Cfg L K)
    (C : Finset (Fin init.card)) (ℓ cutoff s u N t : ℕ)
    (hn : 2 ≤ init.card) (hC : 2 ≤ C.card) :
    (law init)[chargedImmigration init C ℓ cutoff s u N t |
      shiftedFiltration (pairLogFiltration L K) u t] ≤ᵐ[law init] fun ω =>
      (law init)[markedOpportunity init C s ℓ u N t |
        shiftedFiltration (pairLogFiltration L K) u t] ω *
      markedRate init s u N (2 * (cutoff : ℝ) ^ 2 / (init.card : ℝ) ^ 2)
        (2 * (cutoff : ℝ) ^ 2 / (C.card : ℝ) ^ 2) t ω := by
  have hIi := bernoulli_integrable (μ := law init) (maskedImmigration_indicator_stronglyMeasurable init C ℓ cutoff)
    (fun v => ae_of_all _ (maskedImmigration_indicator_bernoulli init C ℓ cutoff v)) (u + t)
  have hJi := bernoulli_integrable (μ := law init) (maskTickIndicator_stronglyMeasurable init C)
    (fun v => ae_of_all _ (maskTickIndicator_zero_one init C v)) (u + t)
  have hr := maskedImmigration_conditional_bound init hn C ℓ cutoff (u + t)
  have hc :
      (law init)[maskedImmigrationIndicator init C ℓ cutoff (u + t) |
        shiftedFiltration (pairLogFiltration L K) u t] ≤ᵐ[law init] fun ω =>
        (law init)[maskTickIndicator init C (u + t) |
          shiftedFiltration (pairLogFiltration L K) u t] ω *
          (2 * (cutoff : ℝ) ^ 2 / (C.card : ℝ) ^ 2) * 1 := by
    filter_upwards [maskedImmigration_conditional_clock_bound init hn C hC ℓ cutoff (u + t),
      maskTickIndicator_conditional_law init hn C (u + t)] with ω hi hj
    change (law init)[maskedImmigrationIndicator init C ℓ cutoff (u + t) |
      pairLogFiltration L K (u + t)] ω ≤
      (law init)[maskTickIndicator init C (u + t) | pairLogFiltration L K (u + t)] ω * _ * 1
    rw [hj, mul_one]
    exact hi
  have h := periodCharge_conditional_rate
    (μ := law init) (ℱ := shiftedFiltration (pairLogFiltration L K) u)
    t _ _ (rawSet_measurable init s u N t) (lateSet_measurable init s ℓ u N t)
    (rawSet_lateSet_disjoint init s ℓ u N t)
    (maskedImmigrationIndicator init C ℓ cutoff (u + t))
    (maskTickIndicator init C (u + t)) (fun _ => 1) _ _ hIi hJi
    (by simpa only [mul_one] using hr) hc
  simpa only [mul_one] using h

def actualImmigrationData (init : Cfg L K) (C : Finset (Fin init.card))
    (ℓ cutoff s u N : ℕ) (hn : 2 ≤ init.card) (hC : 2 ≤ C.card) :
    ImmigrationOpportunityData (law init) (shiftedFiltration (pairLogFiltration L K) u) where
  rate := markedRate init s u N (2 * (cutoff : ℝ) ^ 2 / (init.card : ℝ) ^ 2)
    (2 * (cutoff : ℝ) ^ 2 / (C.card : ℝ) ^ 2)
  immigration := chargedImmigration init C ℓ cutoff s u N
  opportunity := markedOpportunity init C s ℓ u N
  rate_adapted := markedRate_stronglyMeasurable init s u N _ _
  immigration_adapted := chargedImmigration_adapted init C ℓ cutoff s u N
  opportunity_adapted := markedOpportunity_stronglyMeasurable init C s ℓ u N
  rate_nonneg := markedRate_nonneg init s u N _ _ (by positivity) (by positivity)
  immigration_bernoulli := fun t =>
    periodCharge_zero_one _ _ _ (maskedImmigration_indicator_bernoulli init C ℓ cutoff (u + t))
  opportunity_bernoulli := markedOpportunity_zero_one init C s ℓ u N
  immigration_le_opportunity := fun t =>
    periodCharge_le_opportunity _ _ _ _ (rawSet_lateSet_disjoint init s ℓ u N t)
      (maskedImmigration_indicator_bernoulli init C ℓ cutoff (u + t))
      (maskedImmigrationIndicator_le_clockTick init C ℓ cutoff (u + t))
  conditional_rate := fun t => chargedImmigration_conditional_rate init C ℓ cutoff s u N t hn hC

variable {n : ℕ}

theorem actual_charged_mark_ledger (init : InputCfg n) (ω : InputLog n)
    (C : Finset (Fin init.card)) (ℓ cutoff s u N t : ℕ)
    (hseed : ω ∈ seedPrefix init s) (hsu : s ≤ u) (hℓ : 1 ≤ ℓ)
    (hmask : C = clockSet (labelsAt init ω s))
    (hcap : ∀ i, (virtualLabels init ω (u + t) i).phase.val ≤ 3) :
    markedMass init C ℓ cutoff s u (t + 1) ω =
      markedMass init C ℓ cutoff s u t ω +
        chargedImmigration init C ℓ cutoff s u N t ω +
        chargedPropagation init C ℓ cutoff s u N t ω := by
  classical
  have hmaskt : C = clockSet (virtualLabels init ω (u + t)) :=
    hmask.trans (virtual_clockSet_eq_seed_of_current_phase_cap init ω s (u + t)
      hseed (by omega) hcap).symm
  have hi := maskedImmigration_eq_actual_of_mask init C ℓ cutoff (u + t) ω hmaskt
  have hledger := markedAt_card_step_of_seedPrefix init ω C ℓ cutoff s (u + t)
    hseed (by omega) hℓ hmask hcap
  by_cases he : ω ∈ rawSet init s u N t ∪ lateSet init s ℓ u N t
  · simpa only [markedMass, Nat.add_assoc, chargedImmigration, chargedPropagation,
      periodCharge, Set.indicator_of_mem he, hi] using hledger
  · have hraw : ¬ rawFlag init s u N t ω := fun h => he (Or.inl h)
    have hlate : ¬ lateFlag init s ℓ u N t ω := fun h => he (Or.inr h)
    obtain ⟨hzero, himm, hprop, hnext⟩ :=
      gap_mark_step init ω C s ℓ cutoff u N t hseed hsu hℓ hmask hcap hraw hlate
    have hnext' : markedAt init C ℓ cutoff s ω (u + (t + 1)) = ∅ := hnext
    simp only [markedMass, Nat.add_assoc, hzero, hnext', Finset.card_empty, Nat.cast_zero,
      chargedImmigration, chargedPropagation, periodCharge, Set.indicator_of_notMem he, add_zero]

def markedBudgetFailure (init : InputCfg n) (C : Finset (Fin init.card))
    (ℓ cutoff s u N D : ℕ) (R : ℝ) : Set (InputLog n) :=
  {ω | ∃ t, (∀ i, (virtualLabels init ω (u + t) i).phase.val ≤ 3) ∧
    laterClockCount init C s ℓ u N t ω ≤ (D : ℝ) ∧ R < markedMass init C ℓ cutoff s u t ω}

theorem markedBudgetEndpoint_measurable (init : InputCfg n) (C : Finset (Fin init.card))
    (ℓ cutoff s u N D : ℕ) (R : ℝ) (t : ℕ) :
    MeasurableSet[pairLogFiltration _ _ (u + t)]
      {ω | (∀ i, (virtualLabels init ω (u + t) i).phase.val ≤ 3) ∧
        laterClockCount init C s ℓ u N t ω ≤ (D : ℝ) ∧
          R < markedMass init C ℓ cutoff s u t ω} := by
  have hs : MeasurableSet[pairLogFiltration _ _ (u + t)]
      {ω | ∀ i, (virtualLabels init ω (u + t) i).phase.val ≤ 3} :=
    (show MeasurableSet {f : Fin init.card → AgentState (PhaseThreeModel.Numeric.hourIndex n) 256 |
      ∀ i, (f i).phase.val ≤ 3} from (Set.to_countable _).measurableSet).preimage
        (measurable_virtualLabels init (u + t))
  exact hs.inter ((measurableSet_le
    (laterClockCount_stronglyMeasurable init C s ℓ u N t).measurable measurable_const).inter
    (measurableSet_lt measurable_const
      (markedCount_stronglyMeasurable init C ℓ cutoff s (u + t)).measurable))

theorem markedBudgetFailure_measurable (init : InputCfg n) (C : Finset (Fin init.card))
    (ℓ cutoff s u N D : ℕ) (R : ℝ) :
    MeasurableSet (markedBudgetFailure init C ℓ cutoff s u N D R) := by
  have heq : markedBudgetFailure init C ℓ cutoff s u N D R =
      ⋃ t, {ω | (∀ i, (virtualLabels init ω (u + t) i).phase.val ≤ 3) ∧
        laterClockCount init C s ℓ u N t ω ≤ (D : ℝ) ∧
          R < markedMass init C ℓ cutoff s u t ω} := by
    ext ω
    simp only [markedBudgetFailure, Set.mem_setOf_eq, Set.mem_iUnion]
  rw [heq]
  exact MeasurableSet.iUnion (fun t => ((pairLogFiltration _ _).le (u + t)) _
    (markedBudgetEndpoint_measurable init C ℓ cutoff s u N D R t))

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockMarkedProcess

end
