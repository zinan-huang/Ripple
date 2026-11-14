-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockHighRows.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockHighFibres
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockContactIntervals
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockJointCore

/-!
Exact P8 uses in the existing Core fields.  The quantile comparison sums
twenty actual positive-minute P7 lower bounds.  Its endpoint argument
uses the strict pre-high exclusion, so equality at 8C is covered.
The high-width field then adds the already established P6 bulk width.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockHighRows

open PhaseThreeClockProducer PhaseThreeClockActivationSeed

open TimeTheorem PairLog StageEventSpec
  PhaseThreeClockVirtual PhaseThreeClockCore PhaseThreeClockCoreCounts
  PhaseThreeClockSeedTails PhaseThreeClockActivationSeed
  PhaseThreeClockRawLocalRow PhaseThreeClockHourOccupancyRow
  PhaseThreeClockThinning PhaseThreeClockShapeFreeze
  PhaseThreeClockJointCore PhaseThreeClockJointFields
  PhaseThreeClockContactIntervals PhaseThreeClockHighPassage PhaseThreeClockHighFibres
open PhaseThreeModel.Numeric

variable {n : ℕ}

def HighWidthRow (init : InputCfg n) (ω : InputLog n)
    (s : ℕ) (w : ClockTimes init) : Prop :=
  let C := RoleSplitConcentration.clockCount (virtualCfg init ω s)
  ∀ v, s ≤ v → v ≤ w.cap →
    frontHeightL init (virtualLabels init ω s) (virtualLabels init ω v) -
      frontQuantileL init (virtualLabels init ω s) (virtualLabels init ω v)
        (highThreshold C) ≤ 2 * PhaseThreeModel.Numeric.frontWidth C + 20

/-- The P8 allowance used at the positive-hour starts in P9. -/
def HighHourTicks (init : InputCfg n) (ω : InputLog n)
    (s : ℕ) (w : ClockTimes init) : Prop :=
  ∀ h, 1 ≤ h → h ≤ hourIndex n →
    clockContactsL init (virtualLabels init ω s) (drawLabels init ω)
      (w.bulk (256 * h)) (w.start h) ≤
        8 * RoleSplitConcentration.clockCount (virtualCfg init ω s)

theorem core_firstAfter_current (init : InputCfg n) (ω : InputLog n)
    (s T ell u b : ℕ) (hseed : ω ∈ seedPrefix init s)
    (he : AsyncEntry init ω s T)
    (hf : firstAfter (fun v => b ≤
      frontCountL init (virtualLabels init ω s) (virtualLabels init ω v) ell) s u) :
    firstAfter (fun v => b ≤
      PhaseThreeClockGatedLaw.frontCount (virtualLabels init ω v) ell) s u := by
  refine ⟨hf.1, ?_, ?_⟩
  · simpa only [core_front_eq_current_of_asyncEntry init ω s T u ell hseed he hf.1]
      using hf.2.1
  · intro v hsv hvu hv
    apply hf.2.2 v hsv hvu
    simpa only [core_front_eq_current_of_asyncEntry init ω s T v ell hseed he hsv]
      using hv

theorem core_mask_contacts_eq (init : InputCfg n) (ω : InputLog n)
    (C : Finset (Fin init.card)) (s u v : ℕ) (hseed : ω ∈ seedPrefix init s)
    (hmask : C = PhaseThreeClockGatedLaw.clockSet (labelsAt init ω s)) :
    clockContactsL init (virtualLabels init ω s) (drawLabels init ω) u v =
      maskContacts init C u v ω := by
  rw [clockContactsL_virtual_seed init ω s u v hseed]
  have h := maskContacts_seed_eq_stageEvent init ω s u v
  rw [← hmask] at h
  exact h.symm

theorem core_bulk_first_current (init : InputCfg n) (ω : InputLog n)
    (C : Finset (Fin init.card)) (s T : ℕ) (w : ClockTimes init)
    (hseed : ω ∈ seedPrefix init s) (he : AsyncEntry init ω s T)
    (hmask : C = PhaseThreeClockGatedLaw.clockSet (labelsAt init ω s))
    (hp : LevelPassages init ω s w) (ell : ℕ)
    (hell : 1 ≤ ell) (htop : ell ≤ clockTop n) :
    firstAfter (fun v => bulkThreshold C.card ≤
      PhaseThreeClockGatedLaw.frontCount (virtualLabels init ω v) ell) s (w.bulk ell) := by
  have hC := clockMask_card_eq_virtual_seed init C s ω hseed hmask
  apply core_firstAfter_current init ω s T ell (w.bulk ell) (bulkThreshold C.card) hseed he
  simpa only [hC] using hp.2 ell hell htop

theorem high_hour_ticks_of_good (init : InputCfg n) (ω : InputLog n)
    (s T : ℕ) (w : ClockTimes init) (he : AsyncEntry init ω s T)
    (hp : LevelPassages init ω s w) (hhour : HourPassages init ω s w)
    (hgood : ω ∉ allHighFailure init s) :
    HighHourTicks init ω s w := by
  have hseed : ω ∈ seedPrefix init s :=
    ⟨(seedTime_eq_iff init 3 ω s).2 he.first_phase_seed, he.seed_profile⟩
  let C := PhaseThreeClockGatedLaw.clockSet (labelsAt init ω s)
  have hC := clockMask_card_eq_virtual_seed init C s ω hseed rfl
  intro h hh hH
  have hell : 1 ≤ 256 * h := by omega
  have htop : 256 * h ≤ clockTop n := by
    unfold clockTop
    omega
  have hb := core_bulk_first_current init ω C s T w hseed he rfl hp (256 * h) hell htop
  have hhcore := hhour.2.2.1 h hh hH
  have hhcur : firstAfter (fun v => highThreshold C.card ≤
      PhaseThreeClockGatedLaw.frontCount (virtualLabels init ω v) (256 * h)) s (w.start h) := by
    apply core_firstAfter_current init ω s T (256 * h) (w.start h)
      (highThreshold C.card) hseed he
    simpa only [hC] using hhcore
  rw [core_mask_contacts_eq init ω C s _ _ hseed rfl, ← hC]
  exact high_contacts_of_family_good init C (256 * h) s (w.bulk (256 * h))
    (w.start h) ω hell htop rfl hb hhcur
    (shapeSafeAt_of_asyncEntry init C s T ω hseed rfl he (w.start h) hhcur.1) hgood

theorem high_quantile_gap_of_good (init : InputCfg n) (ω : InputLog n)
    (s T : ℕ) (w : ClockTimes init) (he : AsyncEntry init ω s T)
    (hp : LevelPassages init ω s w)
    (hlower : ∀ i, 1 ≤ i → i < clockTop n →
      (2 / 5 : ℝ) * (RoleSplitConcentration.clockCount (virtualCfg init ω s) : ℝ) ≤
        (clockContactsL init (virtualLabels init ω s) (drawLabels init ω)
          (w.bulk i) (w.bulk (i + 1)) : ℝ))
    (hgood : ω ∉ allHighFailure init s) :
    ∀ v, s ≤ v →
      frontQuantileL init (virtualLabels init ω s) (virtualLabels init ω v)
        (bulkThreshold (RoleSplitConcentration.clockCount (virtualCfg init ω s))) ≤
      frontQuantileL init (virtualLabels init ω s) (virtualLabels init ω v)
        (highThreshold (RoleSplitConcentration.clockCount (virtualCfg init ω s))) + 20 := by
  classical
  have hseed : ω ∈ seedPrefix init s :=
    ⟨(seedTime_eq_iff init 3 ω s).2 he.first_phase_seed, he.seed_profile⟩
  let C := PhaseThreeClockGatedLaw.clockSet (labelsAt init ω s)
  have hC := clockMask_card_eq_virtual_seed init C s ω hseed rfl
  intro v hsv
  let beta := frontQuantileL init (virtualLabels init ω s) (virtualLabels init ω v)
    (highThreshold (RoleSplitConcentration.clockCount (virtualCfg init ω s)))
  change _ ≤ beta + 20
  unfold frontQuantileL
  apply Finset.sup_le
  intro ell hellmem
  obtain ⟨hellrange, hellfront⟩ := Finset.mem_filter.mp hellmem
  have hellQ : ell ≤ clockTop n := by
    have := Finset.mem_range.mp hellrange
    omega
  by_cases hsmall : ell ≤ beta + 20
  · exact hsmall
  · let i := beta + 1
    have hip : 1 ≤ i := by dsimp only [i]; omega
    have hiell : i + 20 ≤ ell := by dsimp only [i]; omega
    have hiQ : i + 20 ≤ clockTop n := hiell.trans hellQ
    have hbulkNext := hp.2 (i + 20) (by omega) hiQ
    have hhit : bulkThreshold (RoleSplitConcentration.clockCount (virtualCfg init ω s)) ≤
        frontCountL init (virtualLabels init ω s) (virtualLabels init ω v) (i + 20) :=
      hellfront.trans (core_front_antitone_level init _ _ (i + 20) ell hiell)
    have htauv : w.bulk (i + 20) ≤ v := by
      by_contra hn
      exact hbulkNext.2.2 v hsv (by omega) hhit
    have hu : w.bulk i ≤ v :=
      (bulk_times_mono init ω s w hp i (i + 20) hip (by omega) hiQ).trans htauv
    have hchain := lower_contact_chain init ω s w hp
      ((2 / 5 : ℝ) * (RoleSplitConcentration.clockCount (virtualCfg init ω s) : ℝ))
      hlower i 20 hip hiQ
    have hmono : (clockContactsL init (virtualLabels init ω s) (drawLabels init ω)
        (w.bulk i) (w.bulk (i + 20)) : ℝ) ≤
      (clockContactsL init (virtualLabels init ω s) (drawLabels init ω)
        (w.bulk i) v : ℝ) := by
      exact_mod_cast core_contact_mono_right init _ _ (w.bulk i) (w.bulk (i + 20)) v htauv
    have hbudget : 8 * (C.card : ℝ) ≤ (maskContacts init C (w.bulk i) v ω : ℝ) := by
      rw [← core_mask_contacts_eq init ω C s _ _ hseed rfl, hC]
      norm_num at hchain
      linarith
    have hb := core_bulk_first_current init ω C s T w hseed he rfl hp i hip (by omega)
    have hhi := high_front_of_contact_budget init C i s (w.bulk i) v ω hu
      (shapeSafeAt_of_asyncEntry init C s T ω hseed rfl he v hsv) hbudget
      (high_clock_good_at_bulk init C i s (w.bulk i) ω hip
        (le_trans (Nat.le_add_right i 20) hiQ) rfl hb hgood)
    have hhicore : highThreshold (RoleSplitConcentration.clockCount (virtualCfg init ω s)) ≤
        frontCountL init (virtualLabels init ω s) (virtualLabels init ω v) i := by
      rw [core_front_eq_current_of_asyncEntry init ω s T v i hseed he hsv, ← hC]
      exact hhi
    have hmem : i ∈ (Finset.range (clockTop n + 1)).filter
        (fun q => highThreshold (RoleSplitConcentration.clockCount (virtualCfg init ω s)) ≤
          frontCountL init (virtualLabels init ω s) (virtualLabels init ω v) q) :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hhicore⟩
    have hle : i ≤ beta := Finset.le_sup (f := id) hmem
    dsimp only [i] at hle
    omega

theorem high_width_of_good (init : InputCfg n) (ω : InputLog n)
    (s T : ℕ) (w : ClockTimes init) (he : AsyncEntry init ω s T)
    (hp : LevelPassages init ω s w)
    (hjoint : JointFrontFields init ω s w)
    (hlower : ∀ i, 1 ≤ i → i < clockTop n →
      (2 / 5 : ℝ) * (RoleSplitConcentration.clockCount (virtualCfg init ω s) : ℝ) ≤
        (clockContactsL init (virtualLabels init ω s) (drawLabels init ω)
          (w.bulk i) (w.bulk (i + 1)) : ℝ))
    (hgood : ω ∉ allHighFailure init s) :
    HighWidthRow init ω s w := by
  intro v hsv hvcap
  have hb := hjoint.bulk_width v hsv hvcap
  have hh := high_quantile_gap_of_good init ω s T w he hp hlower hgood v hsv
  change _ ≤ 2 * PhaseThreeModel.Numeric.frontWidth _ + 20
  omega

/-- P8's additional failure, intersected with the previously proved
passage and P7/P6 fields, has its original observed-prefix coefficient. -/
theorem seed_high_width_after_lower_tail (init : InputCfg n)
    (hn : populationThreshold ≤ n) (s : ℕ)
    (E : Set (InputLog n)) (hE : MeasurableSet[pairLogFiltration _ _ s] E)
    (hseed : E ⊆ seedPrefix init s) :
    law init (E ∩ {ω | ∃ T, ∃ w : ClockTimes init,
      AsyncEntry init ω s T ∧ LevelPassages init ω s w ∧
      JointFrontFields init ω s w ∧
      (∀ i, 1 ≤ i → i < clockTop n →
        (2 / 5 : ℝ) * (RoleSplitConcentration.clockCount (virtualCfg init ω s) : ℝ) ≤
          (clockContactsL init (virtualLabels init ω s) (drawLabels init ω)
            (w.bulk i) (w.bulk (i + 1)) : ℝ)) ∧
      ¬ HighWidthRow init ω s w}) ≤
        ENNReal.ofReal (1 / (n : ℝ) ^ 98) * law init E := by
  apply (measure_mono ?_).trans (all_high_prefix_tail init hn s E hE hseed)
  rintro ω ⟨hEω, T, w, he, hp, hjoint, hlower, hbad⟩
  refine ⟨hEω, ?_⟩
  by_contra hgood
  exact hbad (high_width_of_good init ω s T w he hp hjoint hlower hgood)

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockHighRows

end
