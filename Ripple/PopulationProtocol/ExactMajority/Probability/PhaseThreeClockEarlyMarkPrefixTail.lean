-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockEarlyMarkPrefixTail.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockMarkedProcess
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockEarlyMarkCalibration

noncomputable section
open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockEarlyMarkPrefixTail

open TimeTheorem PairLog PhaseThreeScalar PhaseThreeClockPrefixTails
  PhaseThreeClockVirtual PhaseThreeClockGatedLaw PhaseThreeClockSeedTails
  PhaseThreeClockMarkedProcess PhaseThreeClockMarkedWindow PhaseThreeClockMarkedCompensator
  PhaseThreeClockCompensatedMarks PhaseThreeClockRisingOpportunity
  PhaseThreeClockImmigrationOpportunity PhaseThreeClockEarlyMarkCalibration

variable {n : ℕ}

def calibratedMarkFailure (init : InputCfg n) (C : Finset (Fin init.card))
    (ℓ s u : ℕ) : Set (InputLog n) :=
  markedBudgetFailure init C ℓ (PhaseThreeModel.Numeric.earlyCutoff C.card) s u
    (PhaseThreeModel.Numeric.activationHalfHorizon init.card)
    (PhaseThreeModel.Numeric.fineTicks C.card) ((C.card : ℝ) ^ (1 / 3 : ℝ))

theorem calibrated_mark_prefix_tail (init : InputCfg n)
    (C : Finset (Fin init.card)) (ℓ s u : ℕ) (hℓ : 1 ≤ ℓ) (hsu : s ≤ u)
    (hn : PhaseThreeModel.Numeric.populationThreshold ≤ init.card)
    (hlo : (6 / 25 : ℝ) * (init.card : ℝ) ≤ (C.card : ℝ))
    (hCn : C.card ≤ init.card) (hupper : 25 * C.card ≤ 7 * init.card)
    (E : Set (InputLog n)) (hE : MeasurableSet[pairLogFiltration _ _ u] E)
    (hseed : ∀ ω ∈ E, ω ∈ seedPrefix init s ∧ C = clockSet (labelsAt init ω s))
    (hstart : ∀ ω ∈ E,
      (PhaseThreeClockEarlyMarks.markedAt init C ℓ
        (PhaseThreeModel.Numeric.earlyCutoff C.card) s ω u).card ≤
          PhaseThreeModel.Numeric.markOrder C.card) :
    law init (E ∩ calibratedMarkFailure init C ℓ s u) ≤
      ENNReal.ofReal (1 / (C.card : ℝ) ^ 100) * law init E := by
  let a := PhaseThreeModel.Numeric.markOrder C.card
  let w := PhaseThreeModel.Numeric.earlyCutoff C.card
  let N := PhaseThreeModel.Numeric.activationHalfHorizon init.card
  let D := PhaseThreeModel.Numeric.fineTicks C.card
  let R : ℝ := (C.card : ℝ) ^ (1 / 3 : ℝ)
  have hd := PhaseThreeClockActivationCalibration.activation_calibration_data hn hlo hCn
  have hnlarge : 561 ≤ init.card := by have h := hd.population_large; omega
  have hc : 2 ≤ C.card := by
    have hm : (1000 : ℝ) ≤ init.card := by exact_mod_cast hd.population_large
    have hh : (2 : ℝ) ≤ C.card := by linarith
    exact_mod_cast hh
  have hcal := initial_mark_calibration hn hlo hCn
  have ha : 1 ≤ a := hcal.1
  have hR : 0 < R := hcal.2.2.2
  let d := actualMarkData init C ℓ w s u N a hnlarge hc hupper ha
  let i := actualImmigrationData init C ℓ w s u N (by omega) hc
  let z := compensatedRisingData d
  let Ibad : Set (InputLog n) := {ω | ∃ t, (a : ℝ) ≤ immigrationEvents i t ω ∧
    immigrationCharge i t ω ≤ immigrationBudget init.card C.card}
  let Vbad : Set (InputLog n) := {ω | ∃ t, R ≤ z.value t ω ∧
    risingCharge z t ω ≤ (a : ℝ) * growthBudget init.card C.card}
  have hEs : MeasurableSet[shiftedFiltration (pairLogFiltration _ _) u 0] E := by
    simpa only [shiftedFiltration_apply, Nat.add_zero] using hE
  have hzstart : ∀ ω ∈ E, z.value 0 ω ≤ 2 * (a : ℝ) := by
    intro ω hω
    have hm : markedMass init C ℓ w s u 0 ω ≤ (a : ℝ) := by
      unfold markedMass
      simp only [Nat.add_zero]
      exact_mod_cast hstart ω hω
    change (a : ℝ) + markedMass init C ℓ w s u 0 ω ≤ _
    linarith
  have hItail := immigration_opportunity_prefix_tail i E hEs (a : ℝ)
    (immigrationBudget init.card C.card)
  have hVtail := rising_opportunity_prefix_tail z E hEs hzstart R hR
    ((a : ℝ) * growthBudget init.card C.card)
  have hsub : E ∩ calibratedMarkFailure init C ℓ s u ⊆
      (E ∩ Ibad) ∪ (E ∩ Vbad) := by
    rintro ω ⟨hEω, t, hcap, hD, hmark⟩
    have hIcharge : immigrationCharge i t ω ≤ immigrationBudget init.card C.card := by
      exact charge_le init C s ℓ u N D
        (2 * (w : ℝ) ^ 2 / (init.card : ℝ) ^ 2)
        (2 * (w : ℝ) ^ 2 / (C.card : ℝ) ^ 2)
        (by positivity) (by positivity) t ω hD
    by_cases hb : (a : ℝ) < immigrationEvents i t ω
    · exact Or.inl ⟨hEω, t, hb.le, hIcharge⟩
    · have himm : recordedImmigration d t ω ≤ (a : ℝ) := le_of_not_gt hb
      have hledger : ∀ j < t, d.markCount (j + 1) ω =
          d.markCount j ω + d.immigration j ω + d.propagation j ω := by
        intro j hj
        exact actual_charged_mark_ledger init ω C ℓ w s u N j
          (hseed ω hEω).1 hsu hℓ (hseed ω hEω).2
          (fun k => (PhaseThreeClockActivationLaw.virtualLabels_phase_mono init ω k
            (by omega : u + j ≤ u + t)).trans (hcap k))
      have hv := stoppedMarkValue_eq_compensated d ω t himm hledger
      have hvalue : R ≤ z.value t ω := by
        change R ≤ stoppedMarkValue d t ω
        rw [hv]
        change R < d.markCount t ω at hmark
        linarith
      have hclock : 0 ≤ (2 : ℝ) / ((C.card : ℝ) - 1) := by
        have hcR : (2 : ℝ) ≤ C.card := by exact_mod_cast hc
        exact div_nonneg (by norm_num) (by linarith)
      have hcharge : risingCharge z t ω ≤ (a : ℝ) * growthBudget init.card C.card := by
        calc
          _ ≤ (a : ℝ) *
              (((561 / 1000 : ℝ) / init.card) * (N : ℝ) +
                (2 / ((C.card : ℝ) - 1)) * (D : ℝ)) :=
            scaled_charge_le init C s ℓ u N D (a : ℝ)
              ((561 / 1000 : ℝ) / init.card) (2 / ((C.card : ℝ) - 1))
              (Nat.cast_nonneg a) (by positivity) hclock t ω hD
          _ = _ := by unfold growthBudget; dsimp only [N, D]; ring
      exact Or.inr ⟨hEω, t, hvalue, hcharge⟩
  have hIbound : law init (E ∩ Ibad) ≤
      ENNReal.ofReal (Real.exp (immigrationBudget init.card C.card -
        Real.log 2 * (a : ℝ))) * law init E := hItail
  have hVbound : law init (E ∩ Vbad) ≤
      ENNReal.ofReal (risingCoefficient init.card C.card) * law init E := hVtail
  calc
    law init (E ∩ calibratedMarkFailure init C ℓ s u) ≤
        law init ((E ∩ Ibad) ∪ (E ∩ Vbad)) := measure_mono hsub
    _ ≤ law init (E ∩ Ibad) + law init (E ∩ Vbad) := measure_union_le _ _
    _ ≤ ENNReal.ofReal (Real.exp (immigrationBudget init.card C.card -
          Real.log 2 * (a : ℝ))) * law init E +
        ENNReal.ofReal (risingCoefficient init.card C.card) * law init E :=
      add_le_add hIbound hVbound
    _ = (ENNReal.ofReal (Real.exp (immigrationBudget init.card C.card -
          Real.log 2 * (a : ℝ))) +
        ENNReal.ofReal (risingCoefficient init.card C.card)) * law init E := by rw [add_mul]
    _ ≤ _ := mul_le_mul_right' (two_period_error_ennreal_calibration hn hlo hCn) _

theorem calibratedMarkFailure_of_endpoint (init : InputCfg n)
    (C : Finset (Fin init.card)) (ℓ s u b v : ℕ) (ω : InputLog n)
    (hub : u ≤ b) (huv : u ≤ v)
    (hB : secondStart init s ℓ u (PhaseThreeModel.Numeric.activationHalfHorizon init.card) ω =
      (b : WithTop ℕ))
    (hcap : ∀ k, (virtualLabels init ω v k).phase.val ≤ 3)
    (hD : PhaseThreeClockThinning.maskContacts init C b v ω ≤ PhaseThreeModel.Numeric.fineTicks C.card)
    (hmark : (C.card : ℝ) ^ (1 / 3 : ℝ) <
      ((PhaseThreeClockEarlyMarks.markedAt init C ℓ
        (PhaseThreeModel.Numeric.earlyCutoff C.card) s ω v).card : ℝ)) :
    ω ∈ calibratedMarkFailure init C ℓ s u := by
  have hv : u + (v - u) = v := by omega
  refine ⟨v - u, ?_, ?_, ?_⟩
  · simpa only [hv] using hcap
  · rw [laterClockCount_eq_maskContacts init C s ℓ u
      (PhaseThreeModel.Numeric.activationHalfHorizon init.card) b ω hB hub, hv]
    exact_mod_cast hD
  · simpa only [markedMass, hv] using hmark

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockEarlyMarkPrefixTail

end
