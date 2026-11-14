-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockPassageOrderRows.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockFiniteAllCap
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockHourOccupancyRow

/-!
# Finite passage witnesses and their order relative to all-cap

The advanced entry profile puts every Clock strictly below the cap at
the genuine all-Phase-3 entry time. Therefore a genuine all-cap first
passage is later than that entry time. All lower front thresholds have
already been hit at cap, so every required level and hour first passage
exists and is no later than cap.

Together with the finite all-cap theorem this constructs the activation,
level, hour, and cap coordinates of ClockTimes almost surely on each
genuine seed fibre. The initialized coordinate is set to zero and no
claim about it is made. The four cap-relative ordering fields have empty
failure events. No quantitative cap deadline or hour-width estimate is
asserted.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockPassageOrderRows

open TimeTheorem PairLog StageEventSpec PhaseThreeClockProducer
  PhaseThreeClockVirtual PhaseThreeClockCore PhaseThreeClockSeedTails
  PhaseThreeClockActivationSeed PhaseThreeClockEmbeddingBridge
  PhaseThreeClockRawLocalRow PhaseThreeClockActivationRows
  PhaseThreeClockHourOccupancyRow PhaseThreeClockFiniteAllCap

variable {n : ℕ}

theorem firstAfter_le_of_holds {P : ℕ → Prop} {s a b : ℕ}
    (hfirst : firstAfter P s a) (hsb : s ≤ b) (hb : P b) : a ≤ b := by
  by_contra h
  exact hfirst.2.2 b hsb (by omega) hb

theorem exists_firstAfter_le_of_hit (P : ℕ → Prop) (s cap : ℕ)
    (hsc : s ≤ cap) (hcap : P cap) :
    ∃ v, firstAfter P s v ∧ v ≤ cap := by
  classical
  have hex : ∃ v, s ≤ v ∧ P v := ⟨cap, hsc, hcap⟩
  refine ⟨Nat.find hex, ?_, Nat.find_min' hex ⟨hsc, hcap⟩⟩
  refine ⟨(Nat.find_spec hex).1, (Nat.find_spec hex).2, ?_⟩
  intro v hsv hv hhit
  have hmin := Nat.find_min' hex ⟨hsv, hhit⟩
  omega

theorem frontCountL_antitone_level (init : InputCfg n) (fS fv : Lab init)
    (a b : ℕ) (hab : a ≤ b) :
    frontCountL init fS fv b ≤ frontCountL init fS fv a := by
  classical
  unfold frontCountL labelCount
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact ⟨hi.1, hab.trans hi.2⟩

theorem front_thresholds_le_clock_count (C : ℕ) :
    bulkThreshold C ≤ C ∧ highThreshold C ≤ C ∧ smallThreshold C ≤ C := by
  have hC : (0 : ℝ) ≤ C := Nat.cast_nonneg C
  refine ⟨?_, ?_, Nat.div_le_self C 1000⟩
  · unfold bulkThreshold
    apply Nat.ceil_le.mpr
    linarith
  · unfold highThreshold
    apply Nat.ceil_le.mpr
    linarith

def CapFirstAt (init : InputCfg n) (ω : InputLog n) (s cap : ℕ) : Prop :=
  firstAfter (fun v =>
    frontCountL init (virtualLabels init ω s) (virtualLabels init ω v)
      (clockTop n) = clockCount (virtualCfg init ω s)) s cap

/-- Only the genuine first-passage clauses, with the two level-zero
conventions. There are no width, deadline, or shape premises. -/
structure PassageTimes (init : InputCfg n) (ω : InputLog n) (s : ℕ)
    (w : ClockTimes init) : Prop where
  first_zero : w.first 0 = s
  bulk_zero : w.bulk 0 = s
  levels : LevelPassages init ω s w
  hours : HourPassages init ω s w
  cap : CapFirstAt init ω s w.cap

theorem passageTimes_of_virtualCore (init : InputCfg n) (ω : InputLog n)
    (s T : ℕ) (w : ClockTimes init) (hc : VirtualClockCore init ω s T w) :
    PassageTimes init ω s w :=
  ⟨hc.first_zero, hc.bulk_zero, levelPassages_of_virtualCore init ω s T w hc,
    hourPassages_of_virtualCore init ω s T w hc, hc.cap_first⟩

/-- The passage coordinates can be combined with the genuine initialization
map produced separately. None of their first-passage proofs changes. -/
theorem passageTimes_with_initialized (init : InputCfg n) (ω : InputLog n)
    (s : ℕ) (w : ClockTimes init) (j : Fin init.card → ℕ)
    (hw : PassageTimes init ω s w) :
    PassageTimes init ω s ({ w with initialized := j } : ClockTimes init) :=
  ⟨hw.first_zero, hw.bulk_zero, hw.levels, hw.hours, hw.cap⟩

theorem core_cap_front_zero_at_all (init : InputCfg n) (ω : InputLog n)
    (s T : ℕ) (hseed : ω ∈ seedPrefix init s) (hentry : AsyncEntry init ω s T) :
    frontCountL init (virtualLabels init ω s) (virtualLabels init ω T)
      (clockTop n) = 0 := by
  classical
  rw [core_front_eq_current_of_asyncEntry init ω s T T (clockTop n)
    hseed hentry hentry.order,
    virtualLabels_eq_labelsAt_through_asyncEntry init ω s T hentry T le_rfl]
  unfold PhaseThreeClockGatedLaw.frontCount
  apply Finset.card_eq_zero.mpr
  ext i
  constructor
  · intro hi
    simp only [PhaseThreeClockGatedLaw.aboveSet, Finset.mem_filter,
      Finset.mem_univ, true_and] at hi
    have hp := hentry.advanced_profile.all_three _ (labelsAt_mem_trace init ω T i)
    have ha : 3 ≤ (labelsAt init ω T i).phase.val := by omega
    have hm := hentry.advanced_profile.clock_height _
      (labelsAt_mem_trace init ω T i) hi.1
    simp only [PhaseThreeClockGatedLaw.effMinute, if_pos ha, clockTop] at hi
    omega
  · intro hi
    simp at hi

theorem all_lt_cap_of_capFirst (init : InputCfg n) (hn : 1 ≤ n)
    (ω : InputLog n) (s T cap : ℕ) (hseed : ω ∈ seedPrefix init s)
    (hentry : AsyncEntry init ω s T) (hcap : CapFirstAt init ω s cap) :
    T < cap := by
  have hdensity := (seed_role_density init ω s hseed).2
  have hC : 1 ≤ clockCount (virtualCfg init ω s) := by omega
  by_contra h
  have hct : cap ≤ T := by omega
  have hmono := core_front_mono_of_asyncEntry init ω s T (clockTop n) cap T
    hseed hentry (by unfold clockTop; omega) le_rfl hcap.1 hct
  rw [hcap.2.1, core_cap_front_zero_at_all init ω s T hseed hentry] at hmono
  omega

theorem activationFirst_le_all (init : InputCfg n) (ω : InputLog n)
    (s T α : ℕ) (hentry : AsyncEntry init ω s T)
    (hα : ActivationFirstAt init ω s α) : α ≤ T := by
  obtain ⟨a, haT, ha⟩ := exists_activationFirst_of_asyncEntry init ω s T hentry
  exact (firstAfter_le_of_holds hα ha.1 ha.2.1).trans haT

theorem lower_front_at_cap (init : InputCfg n) (ω : InputLog n)
    (s cap ell : ℕ) (hcap : CapFirstAt init ω s cap) (hell : ell ≤ clockTop n) :
    clockCount (virtualCfg init ω s) ≤
      frontCountL init (virtualLabels init ω s) (virtualLabels init ω cap) ell := by
  rw [← hcap.2.1]
  exact frontCountL_antitone_level init _ _ ell (clockTop n) hell

def ActivationBeforeCapRow (init : InputCfg n) (w : ClockTimes init) : Prop :=
  w.activation ≤ w.cap

def AllBeforeCapRow (init : InputCfg n) (T : ℕ) (w : ClockTimes init) : Prop :=
  T ≤ w.cap

def LevelBeforeCapRow (init : InputCfg n) (w : ClockTimes init) : Prop :=
  ∀ ell, ell ≤ clockTop n → w.first ell ≤ w.cap ∧ w.bulk ell ≤ w.cap

def HourBeforeCapRow (init : InputCfg n) (w : ClockTimes init) : Prop :=
  ∀ h, h ≤ PhaseThreeModel.Numeric.hourIndex n →
    w.start h ≤ w.cap ∧ w.finish h ≤ w.cap

theorem passage_order_rows (init : InputCfg n) (hn : 1 ≤ n)
    (ω : InputLog n) (s T : ℕ) (w : ClockTimes init)
    (hseed : ω ∈ seedPrefix init s) (hentry : AsyncEntry init ω s T)
    (hw : PassageTimes init ω s w) :
    ActivationBeforeCapRow init w ∧ AllBeforeCapRow init T w ∧
      LevelBeforeCapRow init w ∧ HourBeforeCapRow init w := by
  have hTC := (all_lt_cap_of_capFirst init hn ω s T w.cap hseed hentry hw.cap).le
  have hαC := (activationFirst_le_all init ω s T w.activation hentry hw.hours.1).trans hTC
  have hthreshold := front_thresholds_le_clock_count (clockCount (virtualCfg init ω s))
  have hdensity := (seed_role_density init ω s hseed).2
  have hC : 1 ≤ clockCount (virtualCfg init ω s) := by omega
  refine ⟨hαC, hTC, ?_, ?_⟩
  · intro ell hell
    by_cases hz : ell = 0
    · subst ell
      simpa only [hw.first_zero, hw.bulk_zero] using And.intro hw.cap.1 hw.cap.1
    · have hp : 1 ≤ ell := by omega
      have hfront := lower_front_at_cap init ω s w.cap ell hw.cap hell
      exact ⟨firstAfter_le_of_holds (hw.levels.1 ell hp hell) hw.cap.1 (hC.trans hfront),
        firstAfter_le_of_holds (hw.levels.2 ell hp hell) hw.cap.1
          (hthreshold.1.trans hfront)⟩
  · intro h hh
    have hnext : 256 * (h + 1) ≤ clockTop n := by unfold clockTop; omega
    have hfinish := firstAfter_le_of_holds (hw.hours.2.2.2 h hh) hw.cap.1
      (hthreshold.2.2.trans (lower_front_at_cap init ω s w.cap _ hw.cap hnext))
    refine ⟨?_, hfinish⟩
    by_cases hz : h = 0
    · subst h
      simpa only [hw.hours.2.1] using hαC
    · have hp : 1 ≤ h := by omega
      exact firstAfter_le_of_holds (hw.hours.2.2.1 h hp hh) hw.cap.1
        (hthreshold.2.1.trans (lower_front_at_cap init ω s w.cap _ hw.cap
          (by unfold clockTop; omega)))

/-- The finite cap hit supplies all lower first-passage witnesses.
No value of initialized is used in PassageTimes. -/
theorem exists_passageTimes_of_capFirst (init : InputCfg n) (hn : 1 ≤ n)
    (ω : InputLog n) (s T cap : ℕ) (hseed : ω ∈ seedPrefix init s)
    (hentry : AsyncEntry init ω s T) (hcap : CapFirstAt init ω s cap) :
    ∃ w : ClockTimes init, PassageTimes init ω s w := by
  classical
  have hdensity := (seed_role_density init ω s hseed).2
  have hC : 1 ≤ clockCount (virtualCfg init ω s) := by omega
  have ht := front_thresholds_le_clock_count (clockCount (virtualCfg init ω s))
  obtain ⟨α, -, hα⟩ := exists_activationFirst_of_asyncEntry init ω s T hentry
  have hfirst (ell : ℕ) (hp : 1 ≤ ell) (hell : ell ≤ clockTop n) :
      ∃ v, firstAfter (fun v => 1 ≤
        frontCountL init (virtualLabels init ω s) (virtualLabels init ω v) ell)
        s v ∧ v ≤ cap :=
    exists_firstAfter_le_of_hit _ s cap hcap.1
      (hC.trans (lower_front_at_cap init ω s cap ell hcap hell))
  have hbulk (ell : ℕ) (hp : 1 ≤ ell) (hell : ell ≤ clockTop n) :
      ∃ v, firstAfter (fun v => bulkThreshold (clockCount (virtualCfg init ω s)) ≤
        frontCountL init (virtualLabels init ω s) (virtualLabels init ω v) ell)
        s v ∧ v ≤ cap :=
    exists_firstAfter_le_of_hit _ s cap hcap.1
      (ht.1.trans (lower_front_at_cap init ω s cap ell hcap hell))
  have hstart (h : ℕ) (hp : 1 ≤ h) (hh : h ≤ PhaseThreeModel.Numeric.hourIndex n) :
      ∃ v, firstAfter (fun v => highThreshold (clockCount (virtualCfg init ω s)) ≤
        frontCountL init (virtualLabels init ω s) (virtualLabels init ω v) (256 * h))
        s v ∧ v ≤ cap :=
    exists_firstAfter_le_of_hit _ s cap hcap.1
      (ht.2.1.trans (lower_front_at_cap init ω s cap _ hcap (by unfold clockTop; omega)))
  have hfinish (h : ℕ) (hh : h ≤ PhaseThreeModel.Numeric.hourIndex n) :
      ∃ v, firstAfter (fun v => smallThreshold (clockCount (virtualCfg init ω s)) ≤
        frontCountL init (virtualLabels init ω s) (virtualLabels init ω v) (256 * (h + 1)))
        s v ∧ v ≤ cap :=
    exists_firstAfter_le_of_hit _ s cap hcap.1
      (ht.2.2.trans (lower_front_at_cap init ω s cap _ hcap (by unfold clockTop; omega)))
  let firstTimes : ℕ → ℕ := fun ell =>
    if he : 1 ≤ ell ∧ ell ≤ clockTop n then Classical.choose (hfirst ell he.1 he.2) else s
  let bulkTimes : ℕ → ℕ := fun ell =>
    if he : 1 ≤ ell ∧ ell ≤ clockTop n then Classical.choose (hbulk ell he.1 he.2) else s
  let startTimes : ℕ → ℕ := fun h =>
    if he : 1 ≤ h ∧ h ≤ PhaseThreeModel.Numeric.hourIndex n then
      Classical.choose (hstart h he.1 he.2) else α
  let finishTimes : ℕ → ℕ := fun h =>
    if he : h ≤ PhaseThreeModel.Numeric.hourIndex n then Classical.choose (hfinish h he) else s
  let w : ClockTimes init := { activation := α, cap := cap, first := firstTimes, bulk := bulkTimes, start := startTimes, finish := finishTimes, initialized := fun _ => 0 }
  refine ⟨w, ?_⟩
  constructor
  · change firstTimes 0 = s
    simp [firstTimes]
  · change bulkTimes 0 = s
    simp [bulkTimes]
  · constructor
    · intro ell hp hell
      change firstAfter _ s (firstTimes ell)
      simpa only [firstTimes, dif_pos (And.intro hp hell)] using
        (Classical.choose_spec (hfirst ell hp hell)).1
    · intro ell hp hell
      change firstAfter _ s (bulkTimes ell)
      simpa only [bulkTimes, dif_pos (And.intro hp hell)] using
        (Classical.choose_spec (hbulk ell hp hell)).1
  · refine ⟨hα, ?_, ?_, ?_⟩
    · change startTimes 0 = α
      simp [startTimes]
    · intro h hp hh
      change firstAfter _ s (startTimes h)
      simpa only [startTimes, dif_pos (And.intro hp hh)] using
        (Classical.choose_spec (hstart h hp hh)).1
    · intro h hh
      change firstAfter _ s (finishTimes h)
      simpa only [finishTimes, dif_pos hh] using (Classical.choose_spec (hfinish h hh)).1
  · exact hcap

def orderFailureAt (init : InputCfg n) (s : ℕ)
    (row : ℕ → ClockTimes init → Prop) : Set (InputLog n) :=
  {ω | seedTime init 3 ω = (s : WithTop ℕ) ∧
    SeedProfile n init (trace init ω s) ∧
    ∃ T, ∃ w : ClockTimes init, AsyncEntry init ω s T ∧
      PassageTimes init ω s w ∧ ¬ row T w}

private theorem orderFailureAt_eq_empty (init : InputCfg n) (s : ℕ)
    (row : ℕ → ClockTimes init → Prop)
    (hrow : ∀ ω T w, ω ∈ seedPrefix init s → AsyncEntry init ω s T →
      PassageTimes init ω s w → row T w) :
    orderFailureAt init s row = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro ω ⟨hs, hp, T, w, he, hw, hbad⟩
  exact hbad (hrow ω T w ⟨hs, hp⟩ he hw)

theorem seed_activation_before_cap_row_tail (init : InputCfg n) (hn : 1 ≤ n) (s : ℕ) :
    law init (orderFailureAt init s (fun _ w => ActivationBeforeCapRow init w)) ≤
      (0 : ℝ≥0∞) * law init {ω | seedTime init 3 ω = (s : WithTop ℕ)} := by
  rw [orderFailureAt_eq_empty init s _ (fun ω T w hs he hw =>
    (passage_order_rows init hn ω s T w hs he hw).1)]
  simp only [measure_empty, zero_mul, le_refl]

theorem seed_all_before_cap_row_tail (init : InputCfg n) (hn : 1 ≤ n) (s : ℕ) :
    law init (orderFailureAt init s (AllBeforeCapRow init)) ≤
      (0 : ℝ≥0∞) * law init {ω | seedTime init 3 ω = (s : WithTop ℕ)} := by
  rw [orderFailureAt_eq_empty init s _ (fun ω T w hs he hw =>
    (passage_order_rows init hn ω s T w hs he hw).2.1)]
  simp only [measure_empty, zero_mul, le_refl]

theorem seed_level_before_cap_row_tail (init : InputCfg n) (hn : 1 ≤ n) (s : ℕ) :
    law init (orderFailureAt init s (fun _ w => LevelBeforeCapRow init w)) ≤
      (0 : ℝ≥0∞) * law init {ω | seedTime init 3 ω = (s : WithTop ℕ)} := by
  rw [orderFailureAt_eq_empty init s _ (fun ω T w hs he hw =>
    (passage_order_rows init hn ω s T w hs he hw).2.2.1)]
  simp only [measure_empty, zero_mul, le_refl]

theorem seed_hour_before_cap_row_tail (init : InputCfg n) (hn : 1 ≤ n) (s : ℕ) :
    law init (orderFailureAt init s (fun _ w => HourBeforeCapRow init w)) ≤
      (0 : ℝ≥0∞) * law init {ω | seedTime init 3 ω = (s : WithTop ℕ)} := by
  rw [orderFailureAt_eq_empty init s _ (fun ω T w hs he hw =>
    (passage_order_rows init hn ω s T w hs he hw).2.2.2)]
  simp only [measure_empty, zero_mul, le_refl]

/-- All first-passage coordinates required above exist outside the same
null set as finite all-cap. There is no union cost for choosing them. -/
theorem seed_passage_times_null (init : InputCfg n) (hc : 2 ≤ init.card)
    (hn : 42 ≤ n) (s : ℕ) :
    law init {ω | ω ∈ seedPrefix init s ∧
      ∃ T, AsyncEntry init ω s T ∧
        ¬ ∃ w : ClockTimes init, PassageTimes init ω s w} = 0 := by
  apply le_antisymm ?_ bot_le
  apply le_trans (measure_mono ?_) (le_of_eq (seed_all_cap_first_null init hc hn s))
  rintro ω ⟨hseed, T, hentry, hbad⟩
  refine ⟨hseed, T, hentry, ?_⟩
  rintro ⟨cap, hcap⟩
  exact hbad (exists_passageTimes_of_capFirst init (by omega) ω s T cap hseed hentry hcap)

theorem seed_passage_times_row_tail (init : InputCfg n) (hc : 2 ≤ init.card)
    (hn : 42 ≤ n) (s : ℕ) :
    law init {ω | seedTime init 3 ω = (s : WithTop ℕ) ∧
      SeedProfile n init (trace init ω s) ∧
      ∃ T, AsyncEntry init ω s T ∧
        ¬ ∃ w : ClockTimes init, PassageTimes init ω s w} ≤
      (0 : ℝ≥0∞) * law init {ω | seedTime init 3 ω = (s : WithTop ℕ)} := by
  rw [zero_mul]
  apply le_trans (measure_mono ?_) (le_of_eq (seed_passage_times_null init hc hn s))
  rintro ω ⟨hs, hp, hbad⟩
  exact ⟨⟨hs, hp⟩, hbad⟩

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockPassageOrderRows

end
