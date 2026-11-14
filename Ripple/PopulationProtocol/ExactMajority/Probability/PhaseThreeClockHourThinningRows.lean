-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockHourThinningRows.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockBeforeTwenty

/-!
Calibrated raw-width conversion at the genuine hour starts, including
hour zero at macroscopic activation.  Start times and Clock masks are
summed over disjoint observed fibres, and all hours are united finitely.

The final estimate is for the intersection of raw-width failure with
the lower Clock-contact statement.  The latter remains a P7/P9 producer
obligation, and is never treated as a conditioning event.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockHourThinningRows

open TimeTheorem PairLog StageEventSpec PhaseThreeClockVirtual
  PhaseThreeClockCore PhaseThreeClockCoreCounts PhaseThreeClockRows
  PhaseThreeClockGatedLaw PhaseThreeClockActivationCalibration
  PhaseThreeClockActivationSeed PhaseThreeClockSeedTails
  PhaseThreeClockSharpActivationSeed PhaseThreeClockShapeSeedFibre
  PhaseThreeClockThinningCalibrated PhaseThreeClockBeforeTwenty
  PhaseThreeClockFirstAfterFibres PhaseThreeClockRawLocalRow
  PhaseThreeClockHourOccupancyRow PhaseThreeClockWorkRows PhaseThreeModel.Numeric
  PhaseThreeClockProducer

variable {n : ℕ}

theorem short_raw_endpoint_of_width (m C u v : ℕ) (hC : 1 ≤ C)
    (hwidth : C * (v - u) ≤ 70 * m ^ 2) :
    v ≤ u + shortHourRaw m C := by
  have hCp : (0 : ℝ) < C := by exact_mod_cast (show 0 < C by omega)
  have hwidthR : (C : ℝ) * ((v - u : ℕ) : ℝ) ≤ 70 * (m : ℝ) ^ 2 := by
    exact_mod_cast hwidth
  have hquot : ((v - u : ℕ) : ℝ) ≤ 70 * (m : ℝ) ^ 2 / (C : ℝ) :=
    (le_div_iff₀ hCp).2 (by nlinarith only [hwidthR])
  have hfloor : v - u ≤ shortHourRaw m C := by
    apply (Nat.le_floor_iff (show 0 ≤ 70 * (m : ℝ) ^ 2 / (C : ℝ) by positivity)).2
    exact hquot
  omega

def shortHourAt (init : InputCfg n) (C : Finset (Fin init.card)) (s u : ℕ) :
    Set (InputLog n) :=
  {ω | ∃ v,
    C.card * (v - u) ≤ 70 * init.card ^ 2 ∧
    (468 / 5 : ℝ) * (C.card : ℝ) ≤
      (StageEventSpec.clockContacts init ω s u v : ℝ)}

theorem short_hour_at_prefix_tail (init : InputCfg n)
    (hm : populationThreshold ≤ init.card) (C : Finset (Fin init.card))
    (hlower : (6 / 25 : ℝ) * (init.card : ℝ) ≤ (C.card : ℝ))
    (s u : ℕ) (E : Set (InputLog n))
    (hE : MeasurableSet[pairLogFiltration _ _ u] E)
    (hmask : ∀ ω ∈ E, clockSet (labelsAt init ω s) = C) :
    law init (E ∩ shortHourAt init C s u) ≤
      ENNReal.ofReal (1 / (C.card : ℝ) ^ 100) * law init E := by
  have hCm : C.card ≤ init.card := by simpa using Finset.card_le_univ C
  have hC := (thinning_exponential_calibration init.card C.card hm hlower hCm).2.1
  apply (measure_mono ?_).trans
    (by simpa only [PhaseThreeClockEarlyMarkCalibration.negative_hundred_rpow_eq] using
      short_hour_prefix_calibrated init hm C hlower s u E hE hmask)
  rintro ω ⟨he, v, hv, hticks⟩
  exact ⟨he, v, short_raw_endpoint_of_width init.card C.card u v hC hv, hticks⟩

def hourStartPred (init : InputCfg n) (C : Finset (Fin init.card))
    (h v : ℕ) (ω : InputLog n) : Prop :=
  if h = 0 then
    macroThreshold init.card ≤
      PhaseThreeClockActivationLaw.activeCount (virtualLabels init ω v)
  else highThreshold C.card ≤ frontCount (virtualLabels init ω v) (256 * h)

theorem hourStartPred_measurable (init : InputCfg n)
    (C : Finset (Fin init.card)) (h v : ℕ) :
    MeasurableSet[pairLogFiltration _ _ v] {ω | hourStartPred init C h v ω} := by
  let P : (Fin init.card → AgentState (hourIndex n) 256) → Prop := fun f =>
    if h = 0 then macroThreshold init.card ≤ PhaseThreeClockActivationLaw.activeCount f
    else highThreshold C.card ≤ frontCount f (256 * h)
  exact (show MeasurableSet {f | P f} from
    (Set.to_countable _).measurableSet).preimage (measurable_virtualLabels init v)

def hourThinningFailure (init : InputCfg n) (C : Finset (Fin init.card)) (s h : ℕ) :
    Set (InputLog n) :=
  {ω | ∃ u, firstAfter (fun v => hourStartPred init C h v ω) s u ∧
    ω ∈ shortHourAt init C s u}

theorem hour_thinning_prefix_tail (init : InputCfg n)
    (hm : populationThreshold ≤ init.card) (C : Finset (Fin init.card))
    (hlower : (6 / 25 : ℝ) * (init.card : ℝ) ≤ (C.card : ℝ))
    (s h : ℕ) (E : Set (InputLog n))
    (hE : MeasurableSet[pairLogFiltration _ _ s] E)
    (hmask : ∀ ω ∈ E, clockSet (labelsAt init ω s) = C) :
    law init (E ∩ hourThinningFailure init C s h) ≤
      ENNReal.ofReal (1 / (C.card : ℝ) ^ 100) * law init E := by
  apply firstAfter_prefix_union (law init) (pairLogFiltration _ _)
    (hourStartPred init C h) s E hE
    (fun v _ => hourStartPred_measurable init C h v)
    (shortHourAt init C s) (ENNReal.ofReal (1 / (C.card : ℝ) ^ 100))
  intro u
  exact short_hour_at_prefix_tail init hm C hlower s u
    (E ∩ {ω | firstAfter (fun v => hourStartPred init C h v ω) s u})
    (firstAfter_prefix_measurable (pairLogFiltration _ _) (hourStartPred init C h)
      s u E hE (fun v _ => hourStartPred_measurable init C h v))
    (fun ω hω => hmask ω hω.1)

def seedHourThinningFailure (init : InputCfg n) (s h : ℕ) : Set (InputLog n) :=
  {ω | ω ∈ hourThinningFailure init (clockSet (labelsAt init ω s)) s h}

theorem seed_hour_thinning_prefix_tail (init : InputCfg n)
    (hn : populationThreshold ≤ n) (s h : ℕ)
    (E : Set (InputLog n)) (hE : MeasurableSet[pairLogFiltration _ _ s] E)
    (hseed : E ⊆ seedPrefix init s) :
    law init (E ∩ seedHourThinningFailure init s h) ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 99) * law init E := by
  apply seed_mask_prefix_union init s E hE
    (fun C => hourThinningFailure init C s h) (ENNReal.ofReal (1 / (n : ℝ) ^ 99))
  intro C
  let A := E ∩ {ω | C = clockSet (labelsAt init ω s)}
  by_cases ha : A = ∅
  · simp only [show E ∩ {ω | C = clockSet (labelsAt init ω s)} = ∅ from ha,
      Set.empty_inter, measure_empty, mul_zero, le_refl]
  · obtain ⟨η, hη⟩ := Set.nonempty_iff_ne_empty.mpr ha
    have hc : PhaseThreeClockGatedLaw.clockCount (labelsAt init η s) = C.card := by
      change (clockSet (labelsAt init η s)).card = C.card
      rw [← hη.2]
    obtain ⟨hm, hlo, hCm⟩ :=
      seed_clock_calibration_inputs init hn η s C.card (hseed hη.1) hc
    have ht := hour_thinning_prefix_tail init hm C hlo s h A
      (hE.inter (PhaseThreeClockEarlyMarkSeedTail.seed_clockMask_measurable init s C))
      (fun ω hω => hω.2.symm)
    exact ht.trans (mul_le_mul_right' (ENNReal.ofReal_le_ofReal
      (seed_clock_error_population init hn η s C (hseed hη.1) hη.2)) _)

def allHourThinningFailure (init : InputCfg n) (s : ℕ) : Set (InputLog n) :=
  ⋃ h : Fin (clockHours n), seedHourThinningFailure init s h.val

theorem hour_thinning_union_coefficient (hn : populationThreshold ≤ n) :
    (clockHours n : ℝ≥0∞) * ENNReal.ofReal (1 / (n : ℝ) ^ 99) ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 98) := by
  have hlow : (6 / 25 : ℝ) * (n : ℝ) ≤ (n : ℝ) := by
    have hnonneg : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  obtain ⟨hnp, -, -, -, -, -, -, -, -, -, -, -, hH, -⟩ :=
    numeric_calibration_core hn hlow le_rfl
  have hcast : (clockHours n : ℝ≥0∞) ≤ (n : ℝ≥0∞) := by exact_mod_cast hH
  calc
    _ ≤ (n : ℝ≥0∞) * ENNReal.ofReal (1 / (n : ℝ) ^ 99) :=
      mul_le_mul_right' hcast _
    _ = ENNReal.ofReal ((n : ℝ) * (1 / (n : ℝ) ^ 99)) := by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg n), ENNReal.ofReal_natCast]
    _ = _ := by
      congr 1
      rw [show (99 : ℕ) = 98 + 1 from rfl, pow_succ]
      field_simp [ne_of_gt hnp]

theorem all_hour_thinning_prefix_tail (init : InputCfg n)
    (hn : populationThreshold ≤ n) (s : ℕ)
    (E : Set (InputLog n)) (hE : MeasurableSet[pairLogFiltration _ _ s] E)
    (hseed : E ⊆ seedPrefix init s) :
    law init (E ∩ allHourThinningFailure init s) ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 98) * law init E := by
  have hcover : E ∩ allHourThinningFailure init s ⊆
      ⋃ h : Fin (clockHours n), E ∩ seedHourThinningFailure init s h.val := by
    rintro ω ⟨he, hb⟩
    obtain ⟨h, hh⟩ := Set.mem_iUnion.mp hb
    exact Set.mem_iUnion.mpr ⟨h, he, hh⟩
  calc
    _ ≤ law init (⋃ h : Fin (clockHours n), E ∩ seedHourThinningFailure init s h.val) :=
      measure_mono hcover
    _ ≤ ∑' h : Fin (clockHours n), law init (E ∩ seedHourThinningFailure init s h.val) :=
      measure_iUnion_le _
    _ ≤ ∑' _h : Fin (clockHours n),
        ENNReal.ofReal (1 / (n : ℝ) ^ 99) * law init E :=
      ENNReal.tsum_le_tsum (fun h => seed_hour_thinning_prefix_tail init hn s h.val E hE hseed)
    _ = ((clockHours n : ℝ≥0∞) * ENNReal.ofReal (1 / (n : ℝ) ^ 99)) * law init E := by
      simp [tsum_fintype, nsmul_eq_mul, mul_assoc]
    _ ≤ _ := mul_le_mul_right' (hour_thinning_union_coefficient hn) _

theorem seed_core_clockCount_eq_mask (init : InputCfg n) (ω : InputLog n)
    (s : ℕ) (hseed : ω ∈ seedPrefix init s) :
    StageEventSpec.clockCount (virtualCfg init ω s) =
      (clockSet (labelsAt init ω s)).card := by
  rw [virtualCfg_eq_trace_at_seedPrefix init ω s hseed]
  exact (PhaseThreeClockActivationSeed.clockCount_labelsAt_eq_trace init ω s).symm

theorem hour_start_firstAfter (init : InputCfg n) (ω : InputLog n)
    (s T h : ℕ) (w : ClockTimes init)
    (hentry : AsyncEntry init ω s T) (hw : HourPassages init ω s w)
    (hh : h ≤ hourIndex n) :
    firstAfter (fun v => hourStartPred init (clockSet (labelsAt init ω s)) h v ω)
      s (w.start h) := by
  have hseed : ω ∈ seedPrefix init s :=
    ⟨(seedTime_eq_iff init 3 ω s).2 hentry.first_phase_seed, hentry.seed_profile⟩
  have hcard := seedPrefix_card_eq init ω s hseed
  have hcount := seed_core_clockCount_eq_mask init ω s hseed
  by_cases hz : h = 0
  · subst h
    rw [hw.2.1]
    simpa only [hourStartPred, if_pos rfl, macroThreshold, hcard,
      PhaseThreeClockActivationRows.ActivationFirstAt, activeCountL_eq_activeCount] using hw.1
  · have hpos : 1 ≤ h := by omega
    have hf := hw.2.2.1 h hpos hh
    refine ⟨hf.1, ?_, ?_⟩
    · have hhf := hf.2.1
      rw [hcount, core_front_eq_current_of_asyncEntry init ω s T (w.start h)
        (256 * h) hseed hentry hf.1] at hhf
      simpa only [hourStartPred, if_neg hz] using hhf
    · intro v hsv hvu hv
      apply hf.2.2 v hsv hvu
      rw [hcount, core_front_eq_current_of_asyncEntry init ω s T v
        (256 * h) hseed hentry hsv]
      simpa only [hourStartPred, if_neg hz] using hv

def LowerHourTicks (init : InputCfg n) (ω : InputLog n) (s : ℕ)
    (w : ClockTimes init) : Prop :=
  ∀ h, h ≤ hourIndex n →
    (468 / 5 : ℝ) * (StageEventSpec.clockCount (virtualCfg init ω s) : ℝ) ≤
      (clockContactsL init (virtualLabels init ω s) (drawLabels init ω)
        (w.start h) (w.finish h) : ℝ)

/-- This is the exact raw-width row after the still-separate P9 tick
lower bound.  HourPassages provides only the observed starts. -/
theorem raw_width_failure_after_ticks_subset (init : InputCfg n) (s : ℕ) :
    {ω | ∃ T, ∃ w : ClockTimes init, AsyncEntry init ω s T ∧
      HourPassages init ω s w ∧ LowerHourTicks init ω s w ∧ ¬ RawWidthRow init ω s w} ⊆
      allHourThinningFailure init s := by
  classical
  rintro ω ⟨T, w, hentry, hpass, hticks, hbad⟩
  have hseed : ω ∈ seedPrefix init s :=
    ⟨(seedTime_eq_iff init 3 ω s).2 hentry.first_phase_seed, hentry.seed_profile⟩
  have hcard := seedPrefix_card_eq init ω s hseed
  have hcount := seed_core_clockCount_eq_mask init ω s hseed
  obtain ⟨h, hh, hbad⟩ : ∃ h, h ≤ hourIndex n ∧
      StageEventSpec.clockCount (virtualCfg init ω s) * (w.finish h - w.start h) ≤
        70 * n ^ 2 := by
    simpa only [RawWidthRow, not_forall, _root_.not_imp, not_lt, exists_prop] using hbad
  have hfin : h < clockHours n := by unfold clockHours; omega
  apply Set.mem_iUnion.mpr
  refine ⟨⟨h, hfin⟩, w.start h, hour_start_firstAfter init ω s T h w hentry hpass hh,
    w.finish h, ?_, ?_⟩
  · simpa only [hcount, hcard] using hbad
  · have ht := hticks h hh
    rw [hcount, clockContactsL_virtual_seed init ω s (w.start h) (w.finish h) hseed] at ht
    exact ht

theorem seed_raw_width_after_ticks_tail (init : InputCfg n)
    (hn : populationThreshold ≤ n) (s : ℕ) :
    law init {ω | seedTime init 3 ω = (s : WithTop ℕ) ∧
      SeedProfile n init (trace init ω s) ∧
      ∃ T, ∃ w : ClockTimes init, AsyncEntry init ω s T ∧
        HourPassages init ω s w ∧ LowerHourTicks init ω s w ∧ ¬ RawWidthRow init ω s w} ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 98) *
        law init {ω | seedTime init 3 ω = (s : WithTop ℕ)} := by
  apply (measure_mono ?_).trans
    ((all_hour_thinning_prefix_tail init hn s (seedPrefix init s)
      (seedPrefix_measurable init s) (fun _ h => h)).trans
        (mul_le_mul_left' (measure_mono (show seedPrefix init s ⊆
          {ω | seedTime init 3 ω = (s : WithTop ℕ)} from fun _ h => h.1)) _))
  rintro ω ⟨hs, hp, hb⟩
  exact ⟨⟨hs, hp⟩, raw_width_failure_after_ticks_subset init s hb⟩

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockHourThinningRows

end
