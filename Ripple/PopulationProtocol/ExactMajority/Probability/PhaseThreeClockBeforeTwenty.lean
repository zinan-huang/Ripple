-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockBeforeTwenty.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockBulkActivation
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockFirstAfterFibres
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockShapeSeedFibre
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockWorkRows

/-!
P9a's additional exceptional event.  On an observed first bulk passage
of minute one, failure of macroscopic activation before an endpoint
requiring 38*C/5 subsequent Clock contacts has a C^(-100) prefix tail.
The first bulk time and physical Clock mask are summed out disjointly.

The lower contact requirement is part of the exceptional event.  This
file does not assert the missing P7 lower-passage process or its tail.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockBeforeTwenty

open TimeTheorem PairLog PhaseThreeClockVirtual PhaseThreeClockGatedLaw
  PhaseThreeClockThinning PhaseThreeClockThinningCalibrated
  PhaseThreeClockMacroscopicActivation PhaseThreeClockSharpActivation
  PhaseThreeClockActivationCalibration PhaseThreeClockActivationSeed
  PhaseThreeClockSeedTails PhaseThreeClockSharpActivationSeed
  PhaseThreeClockShapeSeedFibre PhaseThreeClockEarlyMarkCalibration
  PhaseThreeClockBulkActivation PhaseThreeClockFirstAfterFibres
  PhaseThreeClockWorkRows PhaseThreeClockRawLocalRow PhaseThreeModel.Numeric

variable {n : ℕ}

theorem twenty_contact_mean (m C : ℕ) (hm : 2 ≤ m) (hC : 1 ≤ C)
    (hCm : C ≤ m) (hupper : (C : ℝ) ≤ (7 / 25 : ℝ) * (m : ℝ)) :
    clockMaskRate m C * (20 * m : ℕ) ≤
      3 * ((38 / 5 : ℝ) * (C : ℝ)) / 4 := by
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hmp : (0 : ℝ) < m := by linarith
  have hrate := clockMaskRate_le_square m C hm hC hCm
  have hmul := mul_le_mul_of_nonneg_right hrate
    (show (0 : ℝ) ≤ (20 * m : ℕ) by positivity)
  have heq :
      ((C : ℝ) ^ 2 / (m : ℝ) ^ 2) * (20 * m : ℕ) =
        20 * (C : ℝ) ^ 2 / (m : ℝ) := by
    simp only [Nat.cast_mul, Nat.cast_ofNat]
    field_simp [ne_of_gt hmp]
    <;> ring
  rw [heq] at hmul
  have hproduct := mul_le_mul_of_nonneg_left hupper (Nat.cast_nonneg C)
  have hquot : 20 * (C : ℝ) ^ 2 / (m : ℝ) ≤ (28 / 5 : ℝ) * C := by
    apply (div_le_iff₀ hmp).2
    nlinarith only [hproduct]
  have hnonneg : (0 : ℝ) ≤ C := Nat.cast_nonneg C
  linarith only [hmul, hquot, hnonneg]

theorem twenty_contact_prefix_tail (init : InputCfg n)
    (hm : 2 ≤ init.card) (C : Finset (Fin init.card)) (hC : 1 ≤ C.card)
    (hupper : (C.card : ℝ) ≤ (7 / 25 : ℝ) * (init.card : ℝ))
    (s u : ℕ) (E : Set (InputLog n))
    (hE : MeasurableSet[pairLogFiltration _ _ u] E)
    (hmask : ∀ ω ∈ E, clockSet (labelsAt init ω s) = C) :
    law init (E ∩ {ω |
      (38 / 5 : ℝ) * (C.card : ℝ) ≤
        (StageEventSpec.clockContacts init ω s u (u + 20 * init.card) : ℝ)}) ≤
      ENNReal.ofReal (Real.exp (-(19 / 90 : ℝ) * (C.card : ℝ))) * law init E := by
  have hCm : C.card ≤ init.card := by simpa using Finset.card_le_univ C
  have ht := prefix_stageEvent_clockContacts_upper_tail_ennreal init hm C s u
    (20 * init.card) E hE hmask ((38 / 5 : ℝ) * C.card) (by positivity)
    (twenty_contact_mean init.card C.card hm hC hCm hupper)
  have heq : -((38 / 5 : ℝ) * (C.card : ℝ)) / 36 =
      -(19 / 90 : ℝ) * (C.card : ℝ) := by ring
  simpa only [heq] using ht

def twentyLateAt (init : InputCfg n) (C : Finset (Fin init.card)) (s u : ℕ) :
    Set (InputLog n) :=
  {ω | ∃ v, u ≤ v ∧
    (38 / 5 : ℝ) * (C.card : ℝ) ≤
      (StageEventSpec.clockContacts init ω s u v : ℝ) ∧
    (v : WithTop ℕ) < macroscopicTime init s ω}

theorem twenty_late_prefix_tail (init : InputCfg n)
    (hm : populationThreshold ≤ init.card)
    (C : Finset (Fin init.card))
    (hlower : (6 / 25 : ℝ) * (init.card : ℝ) ≤ (C.card : ℝ))
    (hupper : (C.card : ℝ) ≤ (7 / 25 : ℝ) * (init.card : ℝ))
    (s u : ℕ) (hsu : s ≤ u) (E : Set (InputLog n))
    (hE : MeasurableSet[pairLogFiltration _ _ u] E)
    (hmask : ∀ ω ∈ E, clockSet (labelsAt init ω s) = C)
    (hstart : ∀ ω ∈ E, bulkActivationLaunch init.card ≤
      PhaseThreeClockActivationLaw.activeCount (virtualLabels init ω u)) :
    law init (E ∩ twentyLateAt init C s u) ≤
      ENNReal.ofReal (1 / (C.card : ℝ) ^ 100) * law init E := by
  have hCm : C.card ≤ init.card := by simpa using Finset.card_le_univ C
  obtain ⟨hmlarge, hCtwo, hactcal, htickcal⟩ :=
    bulk_activation_error_calibration init.card C.card hm hlower hCm
  let A : Set (InputLog n) := {ω |
    PhaseThreeClockActivationLaw.activeCount
      (virtualLabels init ω (u + 20 * init.card)) < macroThreshold init.card}
  let B : Set (InputLog n) := {ω |
    (38 / 5 : ℝ) * (C.card : ℝ) ≤
      (StageEventSpec.clockContacts init ω s u (u + 20 * init.card) : ℝ)}
  have hact : law init (E ∩ A) ≤
      ENNReal.ofReal (1 / (C.card : ℝ) ^ 101) * law init E :=
    (bulk_activation_prefix_tail init hmlarge u E hE hstart).trans
      (mul_le_mul_right' (ENNReal.ofReal_le_ofReal hactcal) _)
  have htick : law init (E ∩ B) ≤
      ENNReal.ofReal (1 / (C.card : ℝ) ^ 101) * law init E :=
    (twenty_contact_prefix_tail init (by omega) C (by omega) hupper
      s u E hE hmask).trans
      (mul_le_mul_right' (ENNReal.ofReal_le_ofReal htickcal) _)
  have hcover : E ∩ twentyLateAt init C s u ⊆ (E ∩ A) ∪ (E ∩ B) := by
    rintro ω ⟨he, v, huv, hticks, hlate⟩
    by_cases hv : v ≤ u + 20 * init.card
    · apply Or.inr
      refine ⟨he, hticks.trans ?_⟩
      exact_mod_cast clockContacts_mono_right init ω s u v
        (u + 20 * init.card) hv
    · apply Or.inl
      refine ⟨he, ?_⟩
      have htime : ((u + 20 * init.card : ℕ) : WithTop ℕ) <
          macroscopicTime init s ω := by
        exact lt_trans (by exact_mod_cast (Nat.lt_of_not_ge hv)) hlate
      exact (macroscopicTime_gt_iff_count init s (u + 20 * init.card)
        (by omega) ω).1 htime
  calc
    _ ≤ law init ((E ∩ A) ∪ (E ∩ B)) := measure_mono hcover
    _ ≤ law init (E ∩ A) + law init (E ∩ B) := measure_union_le _ _
    _ ≤ ENNReal.ofReal (1 / (C.card : ℝ) ^ 101) * law init E +
          ENNReal.ofReal (1 / (C.card : ℝ) ^ 101) * law init E :=
      add_le_add hact htick
    _ = ENNReal.ofReal
        (1 / (C.card : ℝ) ^ 101 + 1 / (C.card : ℝ) ^ 101) * law init E := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity), add_mul]
    _ ≤ _ := mul_le_mul_right'
      (ENNReal.ofReal_le_ofReal (two_spare_powers_le C.card hCtwo)) _

def twentyFailure (init : InputCfg n) (C : Finset (Fin init.card)) (s : ℕ) :
    Set (InputLog n) :=
  {ω | ∃ u,
    StageEventSpec.firstAfter (fun v =>
      StageEventSpec.bulkThreshold C.card ≤ frontCount (virtualLabels init ω v) 1) s u ∧
    ω ∈ twentyLateAt init C s u}

/-- Genuine first-bulk splicing retains the seed-prefix probability.
No factor for the unbounded number of possible passage times occurs. -/
theorem twenty_failure_prefix_tail (init : InputCfg n)
    (hm : populationThreshold ≤ init.card)
    (C : Finset (Fin init.card))
    (hlower : (6 / 25 : ℝ) * (init.card : ℝ) ≤ (C.card : ℝ))
    (hupper : (C.card : ℝ) ≤ (7 / 25 : ℝ) * (init.card : ℝ))
    (s : ℕ) (E : Set (InputLog n))
    (hE : MeasurableSet[pairLogFiltration _ _ s] E)
    (hmask : ∀ ω ∈ E, clockSet (labelsAt init ω s) = C) :
    law init (E ∩ twentyFailure init C s) ≤
      ENNReal.ofReal (1 / (C.card : ℝ) ^ 100) * law init E := by
  let P : ℕ → InputLog n → Prop := fun v ω =>
    StageEventSpec.bulkThreshold C.card ≤ frontCount (virtualLabels init ω v) 1
  have hP (v : ℕ) (_hv : s ≤ v) :
      MeasurableSet[pairLogFiltration _ _ v] {ω | P v ω} :=
    (show MeasurableSet {f : Fin init.card → AgentState (hourIndex n) 256 |
      StageEventSpec.bulkThreshold C.card ≤ frontCount f 1} from
      (Set.to_countable _).measurableSet).preimage (measurable_virtualLabels init v)
  apply firstAfter_prefix_union (law init) (pairLogFiltration _ _)
    P s E hE hP (twentyLateAt init C s) (ENNReal.ofReal (1 / (C.card : ℝ) ^ 100))
  intro u
  let F := E ∩ {ω | StageEventSpec.firstAfter (fun v => P v ω) s u}
  by_cases hsu : s ≤ u
  · exact twenty_late_prefix_tail init hm C hlower hupper s u hsu F
      (firstAfter_prefix_measurable (pairLogFiltration _ _) P s u E hE hP)
      (fun ω hω => hmask ω hω.1)
      (fun ω hω => active_launch_of_bulk (virtualLabels init ω u) C.card 1
        (by omega) hlower hω.2.2.1)
  · have he : F = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro ω ⟨-, hω⟩
      exact hsu hω.1
    change law init (F ∩ twentyLateAt init C s u) ≤ _ * law init F
    rw [he, Set.empty_inter, measure_empty, mul_zero]

theorem seed_clock_upper (init : InputCfg n) (ω : InputLog n) (s : ℕ)
    (hseed : ω ∈ seedPrefix init s) (hn : 1 ≤ n) :
    (clockCount (labelsAt init ω s) : ℝ) ≤ (7 / 25 : ℝ) * (init.card : ℝ) := by
  have hg := (seed_work_geometry init hn ω s hseed).2.2.2
  rw [virtualCfg_eq_trace_at_seedPrefix init ω s hseed] at hg
  rw [clockCount_labelsAt_eq_trace init ω s, seedPrefix_card_eq init ω s hseed]
  have hgR : (25 : ℝ) * (StageEventSpec.clockCount (trace init ω s) : ℝ) ≤
      7 * (n : ℝ) := by exact_mod_cast hg
  change (StageEventSpec.clockCount (trace init ω s) : ℝ) ≤ (7 / 25 : ℝ) * (n : ℝ)
  linarith

def seedTwentyFailure (init : InputCfg n) (s : ℕ) : Set (InputLog n) :=
  {ω | ω ∈ twentyFailure init (clockSet (labelsAt init ω s)) s}

/-- Random-mask removal gives n^(-99), with AsyncEntry still absent from
the probabilistic estimate. -/
theorem seed_twenty_population_prefix_tail (init : InputCfg n)
    (hn : populationThreshold ≤ n) (s : ℕ)
    (E : Set (InputLog n)) (hE : MeasurableSet[pairLogFiltration _ _ s] E)
    (hseed : E ⊆ seedPrefix init s) :
    law init (E ∩ seedTwentyFailure init s) ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 99) * law init E := by
  apply seed_mask_prefix_union init s E hE
    (fun C => twentyFailure init C s) (ENNReal.ofReal (1 / (n : ℝ) ^ 99))
  intro C
  let A := E ∩ {ω | C = clockSet (labelsAt init ω s)}
  by_cases ha : A = ∅
  · simp only [show E ∩ {ω | C = clockSet (labelsAt init ω s)} = ∅ from ha,
      Set.empty_inter, measure_empty, mul_zero, le_refl]
  · obtain ⟨η, hη⟩ := Set.nonempty_iff_ne_empty.mpr ha
    have hc : clockCount (labelsAt init η s) = C.card := by
      change (clockSet (labelsAt init η s)).card = C.card
      rw [← hη.2]
    obtain ⟨hm, hlo, hCm⟩ :=
      seed_clock_calibration_inputs init hn η s C.card (hseed hη.1) hc
    have hcal := bulk_activation_error_calibration init.card C.card hm hlo hCm
    have hnsmall : 1 ≤ n := by
      have hmlarge : 200 ≤ init.card := hcal.1
      have hcard := seedPrefix_card_eq init η s (hseed hη.1)
      omega
    have hupper := seed_clock_upper init η s (hseed hη.1) hnsmall
    rw [hc] at hupper
    have ht := twenty_failure_prefix_tail init hm C hlo hupper s A
      (hE.inter (PhaseThreeClockEarlyMarkSeedTail.seed_clockMask_measurable init s C))
      (fun ω hω => hω.2.symm)
    exact ht.trans (mul_le_mul_right' (ENNReal.ofReal_le_ofReal
      (seed_clock_error_population init hn η s C (hseed hη.1) hη.2)) _)

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockBeforeTwenty

end
