-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockJointCore.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockJointFields
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockActivationRows

/-!
Exact Core fields obtained from the deterministic P6 induction.
This is not a RowShape tail: high_width, the hour windows, and their
probability aggregation are separate obligations.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockJointCore

open TimeTheorem PairLog StageEventSpec
  PhaseThreeClockVirtual PhaseThreeClockGatedLaw PhaseThreeClockCore
  PhaseThreeClockCoreCounts PhaseThreeClockSeedTails PhaseThreeClockActivationSeed
  PhaseThreeClockEmbeddingBridge PhaseThreeClockRawLocalRow
  PhaseThreeClockActivationRows PhaseThreeClockActivationLaw
  PhaseThreeClockMacroscopicActivation PhaseThreeClockThinning
  PhaseThreeClockShapeFreeze PhaseThreeClockMarkedShape
  PhaseThreeClockSharpActivationSeed PhaseThreeClockRareChainFibres
  PhaseThreeClockJointFront PhaseThreeClockJointFields PhaseThreeClockProducer
open PhaseThreeModel.Numeric

variable {L K n : ℕ}

theorem macroscopicTime_eq_firstAfter (init : Cfg L K)
    (s alpha : ℕ) (ω : Ω L K)
    (ha : firstAfter
      (fun t => macroscopicThreshold init.card ≤
        PhaseThreeClockActivationLaw.activeCount (virtualLabels init ω t)) s alpha) :
    macroscopicTime init s ω = (alpha : WithTop ℕ) := by
  classical
  have hex : ∃ t, s ≤ t ∧ macroscopicThreshold init.card ≤
      PhaseThreeClockActivationLaw.activeCount (virtualLabels init ω t) :=
    ⟨alpha, ha.1, ha.2.1⟩
  have he : Nat.find hex = alpha := by
    apply Nat.le_antisymm
    · exact Nat.find_min' hex ⟨ha.1, ha.2.1⟩
    · by_contra hnot
      have hh := Nat.find_spec hex
      exact ha.2.2 (Nat.find hex) hh.1 (by omega) hh.2
  simp only [macroscopicTime, dif_pos hex, he]

theorem macroscopicTime_eq_activationFirst (init : InputCfg n)
    (s alpha : ℕ) (ω : InputLog n) (hcard : init.card = n)
    (ha : ActivationFirstAt init ω s alpha) :
    macroscopicTime init s ω = (alpha : WithTop ℕ) := by
  have he (v : ℕ) :
      (Nat.ceil ((99 : ℝ) * (n : ℝ) / 100) ≤
        activeCountL init (virtualLabels init ω v)) ↔
      (macroscopicThreshold init.card ≤
        PhaseThreeClockActivationLaw.activeCount (virtualLabels init ω v)) := by
    have hm : macroscopicThreshold init.card = Nat.ceil ((99 : ℝ) * (n : ℝ) / 100) := by
      unfold macroscopicThreshold
      rw [hcard]
    rw [activeCountL_eq_activeCount, hm]
  apply macroscopicTime_eq_firstAfter init s alpha ω
  refine ⟨ha.1, (he alpha).mp ha.2.1, ?_⟩
  intro v hsv hva hv
  exact ha.2.2 v hsv hva ((he v).mpr hv)

theorem shapeSafeAt_of_asyncEntry (init : InputCfg n)
    (C : Finset (Fin init.card)) (s T : ℕ) (ω : InputLog n)
    (hseed : ω ∈ seedPrefix init s)
    (hmask : C = clockSet (labelsAt init ω s))
    (he : AsyncEntry init ω s T) :
    ∀ v, s ≤ v → shapeSafeAt init C s v ω := by
  intro v hsv
  refine ⟨⟨hseed, hmask.symm⟩, ?_⟩
  intro i
  exact ((virtualLabels_clockEnvironment_of_asyncEntry init ω s T he v hsv).phase_range i).2

/-- The three exact Core fields provided by P6. -/
structure JointFrontFields (init : InputCfg n) (ω : InputLog n)
    (s : ℕ) (w : ClockTimes init) : Prop where
  bulk_width :
    let C := RoleSplitConcentration.clockCount (virtualCfg init ω s)
    ∀ v, s ≤ v → v ≤ w.cap →
      frontHeightL init (virtualLabels init ω s) (virtualLabels init ω v) -
        frontQuantileL init (virtualLabels init ω s) (virtualLabels init ω v)
          (bulkThreshold C) ≤ 2 * PhaseThreeModel.Numeric.frontWidth C
  front_shape :
    let C := RoleSplitConcentration.clockCount (virtualCfg init ω s)
    ∀ ell v, 1 ≤ ell → ell < clockTop n →
      s ≤ v → v ≤ w.bulk ell →
      frontCutoff C ≤ frontCountL init (virtualLabels init ω s) (virtualLabels init ω v) ell →
      frontCountL init (virtualLabels init ω s) (virtualLabels init ω v) ell ≤ bulkThreshold C →
      C * frontCountL init (virtualLabels init ω s) (virtualLabels init ω v) (ell + 1) ≤
        frontCountL init (virtualLabels init ω s) (virtualLabels init ω v) ell ^ 2
  tick_local : ∀ ell, 1 ≤ ell → ell ≤ clockTop n →
    clockContactsL init (virtualLabels init ω s) (drawLabels init ω)
      (max (w.first ell) w.activation) (w.bulk ell) ≤
      localTickBudget (RoleSplitConcentration.clockCount (virtualCfg init ω s))

theorem joint_core_fields_of_local_good (init : InputCfg n)
    (hn : populationThreshold ≤ n) (C : Finset (Fin init.card))
    (s T : ℕ) (w : ClockTimes init) (ω : InputLog n)
    (he : AsyncEntry init ω s T)
    (hmask : C = clockSet (labelsAt init ω s))
    (hpass : LevelPassages init ω s w)
    (ha : ActivationFirstAt init ω s w.activation)
    (hraw : RawLocalRow init w)
    (hsharp : ω ∉ sharpActivationFailure init s C.card)
    (hmarked : ∀ ell, 1 ≤ ell → ell < clockCap n →
      ω ∉ markedShapeFailure init C ell s)
    (hbase : maskContacts init C w.activation (w.bulk 1) ω ≤ 100 * C.card)
    (hcoarse : ∀ ell, 1 ≤ ell → ell < clockCap n →
      maskContacts init C (w.bulk ell) (w.bulk (ell + 1)) ω ≤ 100 * C.card)
    (hrare : ω ∉ rareChainFamilyFailure init C.card s (clockCap n)) :
    JointFrontFields init ω s w := by
  have hseed : ω ∈ seedPrefix init s :=
    ⟨(seedTime_eq_iff init 3 ω s).2 he.first_phase_seed, he.seed_profile⟩
  have hC := clockMask_card_eq_virtual_seed init C s ω hseed hmask
  have hC' : StageEventSpec.clockCount (virtualCfg init ω s) = C.card := hC.symm
  have hsafe := shapeSafeAt_of_asyncEntry init C s T ω hseed hmask he
  have hfirst : ∀ ell, 1 ≤ ell → ell ≤ clockCap n →
      firstAfter (fun t => 1 ≤ PhaseThreeClockGatedLaw.frontCount
        (virtualLabels init ω t) ell) s (w.first ell) := by
    intro ell hell htop
    have hf := hpass.1 ell hell htop
    refine ⟨hf.1, ?_, ?_⟩
    · simpa only [core_front_eq_current_of_asyncEntry init ω s T (w.first ell) ell
        hseed he hf.1] using hf.2.1
    · intro v hsv hvf hv
      apply hf.2.2 v hsv hvf
      simpa only [core_front_eq_current_of_asyncEntry init ω s T v ell
        hseed he hsv] using hv
  have hbulk : ∀ ell, 1 ≤ ell → ell ≤ clockCap n →
      firstAfter (fun t => bulkThreshold C.card ≤ PhaseThreeClockGatedLaw.frontCount
        (virtualLabels init ω t) ell) s (w.bulk ell) := by
    intro ell hell htop
    have hb := hpass.2 ell hell htop
    refine ⟨hb.1, ?_, ?_⟩
    · simpa only [hC', core_front_eq_current_of_asyncEntry init ω s T (w.bulk ell) ell
        hseed he hb.1] using hb.2.1
    · intro v hsv hvb hv
      apply hb.2.2 v hsv hvb
      simpa only [hC', core_front_eq_current_of_asyncEntry init ω s T v ell
        hseed he hsv] using hv
  have hraw' : ∀ ell, 1 ≤ ell → ell ≤ clockCap n →
      w.bulk ell ≤ w.first ell + firstHitHorizon n := by
    intro ell hell htop
    have hr := hraw ell hell htop
    change w.bulk ell - w.first ell ≤ firstHitHorizon n at hr
    omega
  have hJ := joint_front_induction_of_rare_good init hn C s w.activation
    w.first w.bulk ω hseed hmask hsafe
    (macroscopicTime_eq_activationFirst init s w.activation ω
      (seedPrefix_card_eq init ω s hseed) ha)
    hfirst hbulk hsharp hmarked hraw' hbase hcoarse hrare
  refine ⟨?_, ?_, ?_⟩
  · intro C0 v hsv _
    dsimp only [C0]
    rw [← hC]
    exact bulk_width_of_first_hit_width init C s
      (2 * PhaseThreeModel.Numeric.frontWidth C.card) w.first w.bulk ω
      hseed hsafe hfirst hbulk (fun ell hell htop => (hJ ell hell htop).2.2) v hsv
  · exact core_front_shape_of_through_bulk init C s w.bulk ω hseed hmask hsafe
      (fun ell hell htop => (hJ ell hell htop.le).2.1 htop)
  · exact core_tick_local_of_mask_budget init C s w.activation w.first w.bulk ω
      hseed hmask (fun ell hell htop => (hJ ell hell htop).1)

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockJointCore

end
