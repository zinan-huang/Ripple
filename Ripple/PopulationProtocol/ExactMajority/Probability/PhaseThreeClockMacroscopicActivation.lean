-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockMacroscopicActivation.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockCoreCounts
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockActivationTime

/-!
# The 99-percent activation passage used for hour zero

ClockCore.activation_first uses ceil(99 n / 100), and start_zero starts
hour zero at that passage. The full-activation time in ActivationTime is
the later time T at which every label is active.

This file constructs the distinct macroscopic passage on the virtual
continuation. It is a genuine stopping time, is no later than full
activation, and inherits its coarse m^(-5) deadline bound and almost-sure
finiteness. Its finite fibres supply exactly the firstAfter predicate used
by ClockCore; an actual-path bridge is given on a finite agreement window
and on AsyncEntry paths.

No sharp sparse-seed-to-99-percent window or early-mark estimate is claimed.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockMacroscopicActivation

open TimeTheorem PairLog PhaseThreeClockProducer PhaseThreeClockSeedTails
  PhaseThreeClockVirtual PhaseThreeClockActivationLaw PhaseThreeClockActivationSeed
  PhaseThreeClockActivationTails PhaseThreeClockActivationTime
  PhaseThreeClockEmbeddingBridge PhaseThreeClockCoreCounts

variable {L K : ℕ}

def macroscopicThreshold (m : ℕ) : ℕ :=
  Nat.ceil ((99 : ℝ) * (m : ℝ) / 100)

theorem macroscopicThreshold_le_population (m : ℕ) :
    macroscopicThreshold m ≤ m := by
  apply Nat.ceil_le.mpr
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  linarith

open Classical in
/-- First absolute raw time at or after s with at least ceil(99m/100)
threshold-activated labels. -/
def macroscopicTime (init : Cfg L K) (s : ℕ) (ω : Ω L K) : WithTop ℕ :=
  if h : ∃ u, s ≤ u ∧ macroscopicThreshold init.card ≤
      PhaseThreeClockActivationLaw.activeCount (virtualLabels init ω u)
  then ((Nat.find h : ℕ) : WithTop ℕ) else ⊤

theorem macroscopicTime_le_iff (init : Cfg L K) (s N : ℕ) (ω : Ω L K) :
    macroscopicTime init s ω ≤ (N : WithTop ℕ) ↔
      ∃ u ≤ N, s ≤ u ∧ macroscopicThreshold init.card ≤
        PhaseThreeClockActivationLaw.activeCount (virtualLabels init ω u) := by
  classical
  unfold macroscopicTime
  split_ifs with h
  · constructor
    · intro hle
      have hu : Nat.find h ≤ N := by exact_mod_cast hle
      exact ⟨Nat.find h, hu, Nat.find_spec h⟩
    · rintro ⟨u, hu, hs, ha⟩
      have hle : Nat.find h ≤ N := (Nat.find_min' h ⟨hs, ha⟩).trans hu
      exact_mod_cast hle
  · constructor
    · intro hle
      exact absurd hle (by simp)
    · rintro ⟨u, -, hs, ha⟩
      exact absurd ⟨u, hs, ha⟩ h

theorem seed_le_macroscopicTime (init : Cfg L K) (s : ℕ) (ω : Ω L K) :
    (s : WithTop ℕ) ≤ macroscopicTime init s ω := by
  classical
  unfold macroscopicTime
  split_ifs with h
  · exact_mod_cast (Nat.find_spec h).1
  · exact le_top

theorem macroscopicTime_finite_state (init : Cfg L K) (s u : ℕ) (ω : Ω L K)
    (hu : macroscopicTime init s ω = (u : WithTop ℕ)) :
    s ≤ u ∧ macroscopicThreshold init.card ≤ PhaseThreeClockActivationLaw.activeCount (virtualLabels init ω u) := by
  classical
  unfold macroscopicTime at hu
  split_ifs at hu with h
  · have heq : Nat.find h = u := WithTop.coe_injective hu
    simpa only [heq] using Nat.find_spec h
  · exact absurd hu WithTop.top_ne_coe

theorem macroscopicTime_before (init : Cfg L K) (s u : ℕ) (ω : Ω L K)
    (hu : macroscopicTime init s ω = (u : WithTop ℕ)) :
    ∀ v, s ≤ v → v < u →
      PhaseThreeClockActivationLaw.activeCount (virtualLabels init ω v) < macroscopicThreshold init.card := by
  intro v hsv hvu
  by_contra hnot
  have hge : macroscopicThreshold init.card ≤ PhaseThreeClockActivationLaw.activeCount (virtualLabels init ω v) := by
    omega
  have hτ := (macroscopicTime_le_iff init s v ω).2 ⟨v, le_rfl, hsv, hge⟩
  rw [hu] at hτ
  have huv : u ≤ v := by exact_mod_cast hτ
  omega

theorem macroscopic_state_measurable (init : Cfg L K) (u : ℕ) :
    MeasurableSet[pairLogFiltration L K u]
      {ω | macroscopicThreshold init.card ≤ PhaseThreeClockActivationLaw.activeCount (virtualLabels init ω u)} :=
  (show MeasurableSet {f : Fin init.card → AgentState L K |
      macroscopicThreshold init.card ≤ PhaseThreeClockActivationLaw.activeCount f} from
    (Set.to_countable _).measurableSet).preimage (measurable_virtualLabels init u)

theorem macroscopicTime_isStoppingTime (init : Cfg L K) (s : ℕ) :
    IsStoppingTime (pairLogFiltration L K) (macroscopicTime init s) := by
  intro N
  have hm : MeasurableSet[pairLogFiltration L K N]
      (⋃ u, {ω | u ≤ N ∧ s ≤ u ∧
        macroscopicThreshold init.card ≤ PhaseThreeClockActivationLaw.activeCount (virtualLabels init ω u)}) := by
    refine MeasurableSet.iUnion fun u => ?_
    by_cases hu : u ≤ N
    · by_cases hs : s ≤ u
      · have ha : MeasurableSet[pairLogFiltration L K N]
            {ω | macroscopicThreshold init.card ≤ PhaseThreeClockActivationLaw.activeCount (virtualLabels init ω u)} :=
          ((pairLogFiltration L K).mono hu) _ (macroscopic_state_measurable init u)
        simpa only [hu, hs, true_and] using ha
      · simp only [hs, and_false, false_and, Set.setOf_false, MeasurableSet.empty]
    · simp only [hu, false_and, Set.setOf_false, MeasurableSet.empty]
  convert hm using 1
  ext ω
  simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
  exact macroscopicTime_le_iff init s N ω

theorem macroscopicTime_pastTime (init : Cfg L K) (s : ℕ) :
    PhaseOneDrain.PairLogPastTime (macroscopicTime init s) :=
  fun u => (macroscopicTime_isStoppingTime init s).measurableSet_eq_of_countable u

theorem macroscopicTime_le_full (init : Cfg L K) (s : ℕ) (ω : Ω L K) :
    macroscopicTime init s ω ≤ activationTime init s ω := by
  by_cases htop : activationTime init s ω = ⊤
  · simp [htop]
  · obtain ⟨u, hu⟩ := WithTop.ne_top_iff_exists.mp htop
    rw [← hu]
    apply (macroscopicTime_le_iff init s u ω).2
    have hstate := activationTime_finite_state init s u ω hu.symm
    refine ⟨u, le_rfl, hstate.1, ?_⟩
    rw [hstate.2]
    exact macroscopicThreshold_le_population init.card

theorem macroscopicTime_prefix_tail (init : Cfg L K) (hc : 2 ≤ init.card)
    (s : ℕ) (E : Set (Ω L K))
    (hE : MeasurableSet[pairLogFiltration L K s] E)
    (hseed : E ⊆ hasActiveAt init s) :
    law init (E ∩ {ω | ((s + activationHorizon init.card : ℕ) : WithTop ℕ) <
      macroscopicTime init s ω}) ≤
      ENNReal.ofReal (1 / (init.card : ℝ) ^ 5) * law init E := by
  have hsub : E ∩ {ω | ((s + activationHorizon init.card : ℕ) : WithTop ℕ) <
        macroscopicTime init s ω} ⊆
      E ∩ {ω | ((s + activationHorizon init.card : ℕ) : WithTop ℕ) <
        activationTime init s ω} := by
    rintro ω ⟨hω, hlate⟩
    exact ⟨hω, hlate.trans_le (macroscopicTime_le_full init s ω)⟩
  exact (measure_mono hsub).trans (activationTime_prefix_tail init hc s E hE hseed)

theorem macroscopicTime_infinite_prefix_null (init : Cfg L K) (hc : 2 ≤ init.card)
    (s : ℕ) (E : Set (Ω L K))
    (hE : MeasurableSet[pairLogFiltration L K s] E)
    (hseed : E ⊆ hasActiveAt init s) :
    law init (E ∩ {ω | macroscopicTime init s ω = ⊤}) = 0 := by
  have hsub : E ∩ {ω | macroscopicTime init s ω = ⊤} ⊆
      E ∩ {ω | activationTime init s ω = ⊤} := by
    rintro ω ⟨hω, htop⟩
    have hle : (⊤ : WithTop ℕ) ≤ activationTime init s ω := by
      have htop' : macroscopicTime init s ω = ⊤ := htop
      simpa only [htop'] using macroscopicTime_le_full init s ω
    exact ⟨hω, le_antisymm le_top hle⟩
  exact le_antisymm ((measure_mono hsub).trans_eq
    (activationTime_infinite_prefix_null init hc s E hE hseed)) zero_le

variable {n : ℕ}

/-- This is the precise ClockCore.activation_first predicate on the
virtual continuation, at any finite macroscopic passage. -/
theorem macroscopicTime_firstAfter_core_virtual (init : InputCfg n)
    (hcard : init.card = n) (s u : ℕ) (ω : InputLog n)
    (hu : macroscopicTime init s ω = (u : WithTop ℕ)) :
    StageEventSpec.firstAfter
      (fun v => Nat.ceil ((99 : ℝ) * (n : ℝ) / 100) ≤
        PhaseThreeClockCore.activeCountL init (virtualLabels init ω v)) s u := by
  have hstate := macroscopicTime_finite_state init s u ω hu
  have hthreshold : macroscopicThreshold init.card =
      Nat.ceil ((99 : ℝ) * (n : ℝ) / 100) := congrArg macroscopicThreshold hcard
  refine ⟨hstate.1, ?_, ?_⟩
  · simpa only [hthreshold, activeCountL_eq_activeCount] using hstate.2
  · intro v hsv hvu hge
    have hlt := macroscopicTime_before init s u ω hu v hsv hvu
    have hnot : ¬ macroscopicThreshold init.card ≤
        PhaseThreeClockActivationLaw.activeCount (virtualLabels init ω v) := Nat.not_le.mpr hlt
    apply hnot
    simpa only [hthreshold, activeCountL_eq_activeCount] using hge

/-- A finite agreement window transfers the 99-percent first passage
to the exact labelled-path predicate used by ClockCore. -/
theorem macroscopicTime_firstAfter_core_actual (init : InputCfg n)
    (hcard : init.card = n) (s u : ℕ) (ω : InputLog n)
    (hu : macroscopicTime init s ω = (u : WithTop ℕ))
    (hag : ∀ v, v ≤ u → virtualLabels init ω v = labelsAt init ω v) :
    StageEventSpec.firstAfter
      (fun v => Nat.ceil ((99 : ℝ) * (n : ℝ) / 100) ≤
        PhaseThreeClockCore.activeCountL init (labelsAt init ω v)) s u := by
  have hv := macroscopicTime_firstAfter_core_virtual init hcard s u ω hu
  refine ⟨hv.1, ?_, ?_⟩
  · simpa only [hag u le_rfl] using hv.2.1
  · intro v hsv hvu hge
    apply hv.2.2 v hsv hvu
    simpa only [hag v hvu.le] using hge

theorem macroscopicTime_firstAfter_of_actual_phase_cap (init : InputCfg n)
    (hcard : init.card = n) (s u : ℕ) (ω : InputLog n)
    (hu : macroscopicTime init s ω = (u : WithTop ℕ))
    (hcap : ∀ v ≤ u, ∀ i, (labelsAt init ω v i).phase.val < 4) :
    StageEventSpec.firstAfter
      (fun v => Nat.ceil ((99 : ℝ) * (n : ℝ) / 100) ≤
        PhaseThreeClockCore.activeCountL init (labelsAt init ω v)) s u :=
  macroscopicTime_firstAfter_core_actual init hcard s u ω hu
    (virtualLabels_eq_labelsAt_of_phases_lt_four init ω u hcap)

theorem macroscopicTime_le_asyncEntry_all (init : InputCfg n) (ω : InputLog n)
    (s T : ℕ) (hentry : StageEventSpec.AsyncEntry init ω s T) :
    macroscopicTime init s ω ≤ (T : WithTop ℕ) :=
  (macroscopicTime_le_full init s ω).trans_eq
    (activationTime_eq_of_asyncEntry init ω s T hentry)

theorem macroscopicTime_firstAfter_of_asyncEntry (init : InputCfg n)
    (hcard : init.card = n) (ω : InputLog n) (s T u : ℕ)
    (hentry : StageEventSpec.AsyncEntry init ω s T)
    (hu : macroscopicTime init s ω = (u : WithTop ℕ)) :
    StageEventSpec.firstAfter
      (fun v => Nat.ceil ((99 : ℝ) * (n : ℝ) / 100) ≤
        PhaseThreeClockCore.activeCountL init (labelsAt init ω v)) s u := by
  have huT : u ≤ T := by
    have hle := macroscopicTime_le_asyncEntry_all init ω s T hentry
    rw [hu] at hle
    exact_mod_cast hle
  apply macroscopicTime_firstAfter_core_actual init hcard s u ω hu
  intro v hv
  exact virtualLabels_eq_labelsAt_through_asyncEntry init ω s T hentry v (hv.trans huT)

/-- On an actual AsyncEntry path, a finite 99-percent passage exists no
later than T and supplies the actual ClockCore.activation_first clause. -/
theorem exists_macroscopic_firstAfter_of_asyncEntry (init : InputCfg n)
    (ω : InputLog n) (s T : ℕ)
    (hentry : StageEventSpec.AsyncEntry init ω s T) :
    ∃ u : ℕ, macroscopicTime init s ω = (u : WithTop ℕ) ∧ u ≤ T ∧
      StageEventSpec.firstAfter
        (fun v => Nat.ceil ((99 : ℝ) * (n : ℝ) / 100) ≤
          PhaseThreeClockCore.activeCountL init (labelsAt init ω v)) s u := by
  have hle := macroscopicTime_le_asyncEntry_all init ω s T hentry
  have hfinite : macroscopicTime init s ω ≠ ⊤ := by
    intro htop
    rw [htop] at hle
    exact absurd hle (by simp)
  obtain ⟨u, hu⟩ := WithTop.ne_top_iff_exists.mp hfinite
  have huT : u ≤ T := by exact WithTop.coe_le_coe.mp (hu.trans_le hle)
  have hseed : ω ∈ seedPrefix init s :=
    ⟨(seedTime_eq_iff init 3 ω s).2 hentry.first_phase_seed, hentry.seed_profile⟩
  exact ⟨u, hu.symm, huT,
    macroscopicTime_firstAfter_of_asyncEntry init (seedPrefix_card_eq init ω s hseed)
      ω s T u hentry hu.symm⟩

theorem seed_macroscopicTime_prefix_tail (init : InputCfg n) (hc : 2 ≤ init.card)
    (s : ℕ) (E : Set (InputLog n))
    (hE : MeasurableSet[pairLogFiltration _ _ s] E)
    (hseed : E ⊆ seedPrefix init s) :
    law init (E ∩ {ω | ((s + activationHorizon init.card : ℕ) : WithTop ℕ) <
      macroscopicTime init s ω}) ≤
      ENNReal.ofReal (1 / (init.card : ℝ) ^ 5) * law init E :=
  macroscopicTime_prefix_tail init hc s E hE
    (fun ω hω => positive_activation_at_seedPrefix init ω s (hseed hω))

theorem seed_macroscopicTime_infinite_prefix_null (init : InputCfg n)
    (hc : 2 ≤ init.card) (s : ℕ) (E : Set (InputLog n))
    (hE : MeasurableSet[pairLogFiltration _ _ s] E)
    (hseed : E ⊆ seedPrefix init s) :
    law init (E ∩ {ω | macroscopicTime init s ω = ⊤}) = 0 :=
  macroscopicTime_infinite_prefix_null init hc s E hE
    (fun ω hω => positive_activation_at_seedPrefix init ω s (hseed hω))

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockMacroscopicActivation

end
