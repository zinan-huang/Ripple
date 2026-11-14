-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockSmallActivation.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockMacroscopicActivation

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockSmallActivation

open TimeTheorem PairLog PhaseThreeClockVirtual PhaseThreeClockActivationLaw
  PhaseThreeClockActivationSeed PhaseThreeClockActivationTime PhaseThreeClockActivationTails
  PhaseThreeClockMacroscopicActivation PhaseThreeClockSeedTails PhaseThreeClockCoreCounts

variable {L K : ℕ}

open Classical in
def smallActivationTime (init : Cfg L K) (s C : ℕ) (ω : Ω L K) : WithTop ℕ :=
  if h : ∃ u, s ≤ u ∧ PhaseThreeModel.Numeric.smallActivation C ≤
      PhaseThreeClockActivationLaw.activeCount (virtualLabels init ω u)
  then ((Nat.find h : ℕ) : WithTop ℕ) else ⊤

theorem smallActivationTime_le_iff (init : Cfg L K) (s C N : ℕ) (ω : Ω L K) :
    smallActivationTime init s C ω ≤ (N : WithTop ℕ) ↔
      ∃ u ≤ N, s ≤ u ∧ PhaseThreeModel.Numeric.smallActivation C ≤
        PhaseThreeClockActivationLaw.activeCount (virtualLabels init ω u) := by
  classical
  unfold smallActivationTime
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

theorem seed_le_smallActivationTime (init : Cfg L K) (s C : ℕ) (ω : Ω L K) :
    (s : WithTop ℕ) ≤ smallActivationTime init s C ω := by
  classical
  unfold smallActivationTime
  split_ifs with h
  · exact_mod_cast (Nat.find_spec h).1
  · exact le_top

theorem smallActivationTime_finite_state (init : Cfg L K) (s C u : ℕ) (ω : Ω L K)
    (hu : smallActivationTime init s C ω = (u : WithTop ℕ)) :
    s ≤ u ∧ PhaseThreeModel.Numeric.smallActivation C ≤
      PhaseThreeClockActivationLaw.activeCount (virtualLabels init ω u) := by
  classical
  unfold smallActivationTime at hu
  split_ifs at hu with h
  · have heq : Nat.find h = u := WithTop.coe_injective hu
    simpa only [heq] using Nat.find_spec h
  · exact absurd hu WithTop.top_ne_coe

theorem smallActivationTime_before (init : Cfg L K) (s C u : ℕ) (ω : Ω L K)
    (hu : smallActivationTime init s C ω = (u : WithTop ℕ)) :
    ∀ v, s ≤ v → v < u →
      PhaseThreeClockActivationLaw.activeCount (virtualLabels init ω v) < PhaseThreeModel.Numeric.smallActivation C := by
  intro v hsv hvu
  by_contra hnot
  have hge : PhaseThreeModel.Numeric.smallActivation C ≤
      PhaseThreeClockActivationLaw.activeCount (virtualLabels init ω v) := by omega
  have hle := (smallActivationTime_le_iff init s C v ω).2 ⟨v, le_rfl, hsv, hge⟩
  rw [hu] at hle
  have huv : u ≤ v := by exact_mod_cast hle
  omega

theorem smallActivation_state_measurable (init : Cfg L K) (C u : ℕ) :
    MeasurableSet[pairLogFiltration L K u]
      {ω | PhaseThreeModel.Numeric.smallActivation C ≤ PhaseThreeClockActivationLaw.activeCount (virtualLabels init ω u)} :=
  (show MeasurableSet {f : Fin init.card → AgentState L K |
      PhaseThreeModel.Numeric.smallActivation C ≤ PhaseThreeClockActivationLaw.activeCount f} from
    (Set.to_countable _).measurableSet).preimage (measurable_virtualLabels init u)

theorem smallActivationTime_isStoppingTime (init : Cfg L K) (s C : ℕ) :
    IsStoppingTime (pairLogFiltration L K) (smallActivationTime init s C) := by
  intro N
  have hm : MeasurableSet[pairLogFiltration L K N]
      (⋃ u, {ω | u ≤ N ∧ s ≤ u ∧
        PhaseThreeModel.Numeric.smallActivation C ≤ PhaseThreeClockActivationLaw.activeCount (virtualLabels init ω u)}) := by
    refine MeasurableSet.iUnion fun u => ?_
    by_cases hu : u ≤ N
    · by_cases hs : s ≤ u
      · have ha : MeasurableSet[pairLogFiltration L K N]
            {ω | PhaseThreeModel.Numeric.smallActivation C ≤
              PhaseThreeClockActivationLaw.activeCount (virtualLabels init ω u)} :=
          ((pairLogFiltration L K).mono hu) _ (smallActivation_state_measurable init C u)
        simpa only [hu, hs, true_and] using ha
      · simp only [hs, and_false, false_and, Set.setOf_false, MeasurableSet.empty]
    · simp only [hu, false_and, Set.setOf_false, MeasurableSet.empty]
  convert hm using 1
  ext ω
  simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
  exact smallActivationTime_le_iff init s C N ω

theorem smallActivationTime_pastTime (init : Cfg L K) (s C : ℕ) :
    PhaseOneDrain.PairLogPastTime (smallActivationTime init s C) :=
  fun u => (smallActivationTime_isStoppingTime init s C).measurableSet_eq_of_countable u

theorem smallActivationTime_firstAfter (init : Cfg L K) (s C u : ℕ) (ω : Ω L K)
    (hu : smallActivationTime init s C ω = (u : WithTop ℕ)) :
    StageEventSpec.firstAfter
      (fun t => PhaseThreeModel.Numeric.smallActivation C ≤
        PhaseThreeClockActivationLaw.activeCount (virtualLabels init ω t)) s u := by
  have hstate := smallActivationTime_finite_state init s C u ω hu
  exact ⟨hstate.1, hstate.2,
    fun v hsv hvu => Nat.not_le.mpr (smallActivationTime_before init s C u ω hu v hsv hvu)⟩

theorem smallActivationTime_overshoot (init : Cfg L K) (s C u : ℕ) (ω : Ω L K)
    (hstart : PhaseThreeClockActivationLaw.activeCount (virtualLabels init ω s) ≤ PhaseThreeModel.Numeric.smallActivation C + 1)
    (hu : smallActivationTime init s C ω = (u : WithTop ℕ)) :
    PhaseThreeClockActivationLaw.activeCount (virtualLabels init ω u) ≤ PhaseThreeModel.Numeric.smallActivation C + 1 := by
  have hsu := (smallActivationTime_finite_state init s C u ω hu).1
  cases u with
  | zero =>
      have hs : s = 0 := by omega
      simpa only [hs] using hstart
  | succ u =>
      by_cases hs : s = u + 1
      · simpa only [hs] using hstart
      · have hprev := smallActivationTime_before init s C (u + 1) ω hu
          u (by omega) (Nat.lt_succ_self u)
        have hstep := (activeCount_virtualLabels_succ_bounds init ω u).2
        omega

theorem smallActivationTime_le_macroscopic (init : Cfg L K) (s C : ℕ) (ω : Ω L K)
    (hthreshold : PhaseThreeModel.Numeric.smallActivation C ≤ macroscopicThreshold init.card) :
    smallActivationTime init s C ω ≤ macroscopicTime init s ω := by
  by_cases htop : macroscopicTime init s ω = ⊤
  · simp [htop]
  · obtain ⟨u, hu⟩ := WithTop.ne_top_iff_exists.mp htop
    rw [← hu]
    have hstate := macroscopicTime_finite_state init s u ω hu.symm
    exact (smallActivationTime_le_iff init s C u ω).2
      ⟨u, le_rfl, hstate.1, hthreshold.trans hstate.2⟩

theorem smallActivationTime_le_full (init : Cfg L K) (s C : ℕ) (ω : Ω L K)
    (hthreshold : PhaseThreeModel.Numeric.smallActivation C ≤ init.card) :
    smallActivationTime init s C ω ≤ activationTime init s ω := by
  by_cases htop : activationTime init s ω = ⊤
  · simp [htop]
  · obtain ⟨u, hu⟩ := WithTop.ne_top_iff_exists.mp htop
    rw [← hu]
    have hstate := activationTime_finite_state init s u ω hu.symm
    exact (smallActivationTime_le_iff init s C u ω).2
      ⟨u, le_rfl, hstate.1, by simpa only [hstate.2] using hthreshold⟩

theorem smallActivationTime_infinite_prefix_null (init : Cfg L K) (hc : 2 ≤ init.card)
    (s C : ℕ) (hthreshold : PhaseThreeModel.Numeric.smallActivation C ≤ init.card)
    (E : Set (Ω L K)) (hE : MeasurableSet[pairLogFiltration L K s] E)
    (hseed : E ⊆ hasActiveAt init s) :
    law init (E ∩ {ω | smallActivationTime init s C ω = ⊤}) = 0 := by
  have hsub : E ∩ {ω | smallActivationTime init s C ω = ⊤} ⊆
      E ∩ {ω | activationTime init s ω = ⊤} := by
    rintro ω ⟨hω, htop⟩
    have hle := smallActivationTime_le_full init s C ω hthreshold
    rw [htop] at hle
    exact ⟨hω, le_antisymm le_top hle⟩
  exact le_antisymm ((measure_mono hsub).trans_eq
    (activationTime_infinite_prefix_null init hc s E hE hseed)) bot_le

variable {n : ℕ}

theorem activeCount_labelsAt_eq_trace (init : InputCfg n) (ω : InputLog n) (s : ℕ) :
    PhaseThreeClockActivationLaw.activeCount (labelsAt init ω s) =
      (trace init ω s).countP (fun a => 3 ≤ a.phase.val) := by
  rw [← labelsAt_config init ω s]
  exact (Multiset.countP_map (labelsAt init ω s) Finset.univ.val
    (fun a => 3 ≤ a.phase.val)).symm

theorem activeCount_at_seedPrefix (init : InputCfg n) (ω : InputLog n)
    (s : ℕ) (hseed : ω ∈ seedPrefix init s) :
    PhaseThreeClockActivationLaw.activeCount (virtualLabels init ω s) = 2 := by
  classical
  rw [virtual_eq_actual_at_seedPrefix init ω s hseed, activeCount_labelsAt_eq_trace]
  calc
    (trace init ω s).countP (fun a => 3 ≤ a.phase.val) =
        (trace init ω s).countP (fun a => a.phase.val = 3) := by
      apply Multiset.countP_congr rfl
      intro a ha
      apply propext
      have hp := (hseed.2.phase_range a ha).2
      omega
    _ = 2 := hseed.2.exactly_two

theorem smallActivationTime_overshoot_from_seed (init : InputCfg n) (ω : InputLog n)
    (s C u : ℕ) (hseed : ω ∈ seedPrefix init s)
    (hr : 1 ≤ PhaseThreeModel.Numeric.smallActivation C)
    (hu : smallActivationTime init s C ω = (u : WithTop ℕ)) :
    PhaseThreeModel.Numeric.smallActivation C ≤ PhaseThreeClockActivationLaw.activeCount (virtualLabels init ω u) ∧
      PhaseThreeClockActivationLaw.activeCount (virtualLabels init ω u) ≤ PhaseThreeModel.Numeric.smallActivation C + 1 := by
  refine ⟨(smallActivationTime_finite_state init s C u ω hu).2, ?_⟩
  apply smallActivationTime_overshoot init s C u ω ?_ hu
  rw [activeCount_at_seedPrefix init ω s hseed]
  omega

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockSmallActivation

end
