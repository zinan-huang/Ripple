-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockInitializationRows.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockCanonicalFieldTails
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockReserve

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockInitializationRows

open TimeTheorem PairLog PairLogAuxiliary StageEventSpec
  PhaseThreeClockVirtual PhaseThreeClockGatedLaw PhaseThreeClockEmbedding
  PhaseThreeClockEmbeddingBridge PhaseThreeClockActivationLaw
  PhaseThreeClockSeedTails PhaseThreeClockCore PhaseThreeClockRows
  PhaseThreeClockRawLocalRow PhaseThreeClockPassageOrderRows
  PhaseThreeClockCanonicalRows PhaseThreeClockCanonicalFieldTails
  PhaseThreeClockReserve

variable {L K n : ℕ}

theorem virtualRule_clock_counter_nonincrease_left
    (a b : AgentState L K) (ha : a.phase.val = 3)
    (har : a.role = .clock) (hb : b.phase.val ≤ 3)
    (hnb : (phaseEpidemicUpdate L K a b).1.phase.val ≠ 10 ∧
      (phaseEpidemicUpdate L K a b).2.phase.val ≠ 10) :
    (virtualRule a b).1.counter.val ≤ a.counter.val := by
  obtain ⟨hep, hepb⟩ := epidemic_left_of_phase_three a b ha hb hnb
  by_cases hcap : CapCounterPair a b
  · simp only [virtualRule, if_pos hcap, saturatedCounterStep_counter, hep]
    omega
  · rw [virtualRule_eq_transition_of_not_cap a b hcap,
      transition_eq_phase3_of_dispatch a b (by rw [hep]; exact ha), hep]
    simp only []
    set b' := (phaseEpidemicUpdate L K a b).2 with hb'
    by_cases hbr : b'.role = .clock
    · by_cases heq : a.minute = b'.minute
      · by_cases hlt : a.minute.val < K * (L + 1)
        · rw [phase3Transition_drip a b' har hbr heq hlt,
            finishPhase10Entry_eq_self_of_after_ne_10 L K _ _ (by simp [ha])]
        · exfalso
          apply hcap
          refine ⟨by rw [hep]; exact ha, hepb, by rw [hep]; exact har, hbr, ?_, ?_⟩
          · rw [hep]
            exact heq
          · rw [hep]
            have := a.minute.isLt
            omega
      · rw [phase3Transition_copy a b' har hbr heq,
          finishPhase10Entry_eq_self_of_after_ne_10 L K _ _ (by simp [ha])]
    · rw [phase3Transition_clock_left a b' har hbr,
        finishPhase10Entry_eq_self_of_after_ne_10 L K _ _ (by show a.phase.val ≠ 10; omega)]

theorem virtualRule_clock_counter_nonincrease_right
    (a b : AgentState L K) (hb : b.phase.val = 3)
    (hbr : b.role = .clock) (ha : a.phase.val ≤ 3)
    (hnb : (phaseEpidemicUpdate L K a b).1.phase.val ≠ 10 ∧
      (phaseEpidemicUpdate L K a b).2.phase.val ≠ 10) :
    (virtualRule a b).2.counter.val ≤ b.counter.val := by
  obtain ⟨hep, hepa⟩ := epidemic_right_of_phase_three a b hb ha hnb
  by_cases hcap : CapCounterPair a b
  · simp only [virtualRule, if_pos hcap, saturatedCounterStep_counter, hep]
    omega
  · rw [virtualRule_eq_transition_of_not_cap a b hcap,
      transition_eq_phase3_of_dispatch a b hepa, hep]
    simp only []
    set a' := (phaseEpidemicUpdate L K a b).1 with ha'
    by_cases har : a'.role = .clock
    · by_cases heq : a'.minute = b.minute
      · by_cases hlt : a'.minute.val < K * (L + 1)
        · rw [phase3Transition_drip a' b har hbr heq hlt,
            finishPhase10Entry_eq_self_of_after_ne_10 L K _ _ (by show b.phase.val ≠ 10; omega)]
        · exfalso
          apply hcap
          refine ⟨hepa, by rw [hep]; exact hb, har, by rw [hep]; exact hbr, ?_, ?_⟩
          · rw [hep]
            exact heq
          · rw [← ha']
            have := a'.minute.isLt
            omega
      · rw [phase3Transition_copy a' b har hbr heq,
          finishPhase10Entry_eq_self_of_after_ne_10 L K _ _ (by simp [hb])]
    · rw [phase3Transition_clock_right a' b har hbr,
        finishPhase10Entry_eq_self_of_after_ne_10 L K _ _ (by show b.phase.val ≠ 10; omega)]

theorem virtual_counter_nonincrease (init : InputCfg n) (ω : InputLog n)
    (s T : ℕ) (he : AsyncEntry init ω s T) (i : Fin init.card)
    (hi : fixedRoleL init (virtualLabels init ω s) .clock i)
    (u : ℕ) (hsu : s ≤ u) (hu : (virtualLabels init ω u i).phase.val = 3)
    (v : ℕ) (huv : u ≤ v) :
    (virtualLabels init ω v i).counter.val ≤
      (virtualLabels init ω u i).counter.val := by
  have henv := virtualLabels_clockEnvironment_of_asyncEntry init ω s T he
  have hroles := virtualLabels_roles_fixed_of_asyncEntry init ω s T he
  have hr (t : ℕ) (hst : s ≤ t) :
      (virtualLabels init ω t i).role = .clock := by
    rw [hroles t hst i, ← hroles s le_rfl i]
    exact hi
  induction v, huv using Nat.le_induction with
  | base => exact le_rfl
  | succ v huv ih =>
      have hsv : s ≤ v := hsu.trans huv
      have hv : (virtualLabels init ω v i).phase.val = 3 :=
        le_antisymm ((henv v hsv).phase_range i).2
          (hu.ge.trans (virtualLabels_phase_mono init ω i huv))
      have hout (j : Fin init.card) :
          (virtualLabels init ω (v + 1) j).phase.val ≤ 3 :=
        ((henv (v + 1) (by omega)).phase_range j).2
      have hstep : (virtualLabels init ω (v + 1) i).counter.val ≤
          (virtualLabels init ω v i).counter.val := by
        cases hd : drawLabels init ω (v + 1) with
        | none =>
            rw [virtualLabels_succ_none init ω hd]
        | some jl =>
            obtain ⟨j, l⟩ := jl
            have hjl : j ≠ l := (labelsAt_selected_transition init ω v j l hd).1
            have hj := virtualLabels_succ_left init ω hd hjl
            have hl := virtualLabels_succ_right init ω hd
            have hnb :
                (phaseEpidemicUpdate _ _ (virtualLabels init ω v j)
                  (virtualLabels init ω v l)).1.phase.val ≠ 10 ∧
                (phaseEpidemicUpdate _ _ (virtualLabels init ω v j)
                  (virtualLabels init ω v l)).2.phase.val ≠ 10 :=
              virtualRule_no_backup_of_phase_le_three _ _
                (by rw [← hj]; exact hout j) (by rw [← hl]; exact hout l)
            by_cases hij : i = j
            · subst j
              rw [hj]
              exact virtualRule_clock_counter_nonincrease_left _ _ hv (hr v hsv)
                ((henv v hsv).phase_range l).2 hnb
            · by_cases hil : i = l
              · subst l
                rw [hl]
                exact virtualRule_clock_counter_nonincrease_right _ _ hv (hr v hsv)
                  ((henv v hsv).phase_range j).2 hnb
              · rw [virtualLabels_succ_other init ω hd hij hil]
      exact hstep.trans ih

theorem canonical_initialized_first (init : InputCfg n) (ω : InputLog n)
    (s T : ℕ) (he : AsyncEntry init ω s T) (i : Fin init.card) :
    firstHit
      (fun a : AgentState (PhaseThreeModel.Numeric.hourIndex n) 256 => 3 ≤ a.phase.val)
      (fun v => virtualLabels init ω v i) ((virtualTimes init ω s).initialized i) := by
  classical
  have hT : 3 ≤ (virtualLabels init ω T i).phase.val := by
    rw [virtualLabels_eq_labelsAt_through_asyncEntry init ω s T he T le_rfl]
    exact (he.advanced_profile.all_three _ (labelsAt_mem_trace init ω T i)).ge
  have hex : ∃ u, 3 ≤ (virtualLabels init ω u i).phase.val := ⟨T, hT⟩
  have hf : firstHit
      (fun a : AgentState (PhaseThreeModel.Numeric.hourIndex n) 256 => 3 ≤ a.phase.val)
      (fun v => virtualLabels init ω v i) (Nat.find hex) := by
    refine ⟨Nat.find_spec hex, ?_⟩
    intro u hu hhit
    have := Nat.find_min' hex hhit
    omega
  have heq : (virtualTimes init ω s).initialized i = Nat.find hex := by
    exact firstHitTime_eq hf
  rw [heq]
  exact hf

theorem canonical_initialized_by_all (init : InputCfg n) (ω : InputLog n)
    (s T : ℕ) (he : AsyncEntry init ω s T) (i : Fin init.card) :
    (virtualTimes init ω s).initialized i ≤ T := by
  have hf := canonical_initialized_first init ω s T he i
  by_contra hnot
  apply hf.2 T (by omega)
  show 3 ≤ (virtualLabels init ω T i).phase.val
  rw [virtualLabels_eq_labelsAt_through_asyncEntry init ω s T he T le_rfl]
  exact (he.advanced_profile.all_three _ (labelsAt_mem_trace init ω T i)).ge

theorem seed_le_canonical_initialized (init : InputCfg n) (ω : InputLog n)
    (s T : ℕ) (he : AsyncEntry init ω s T) (i : Fin init.card) :
    s ≤ (virtualTimes init ω s).initialized i := by
  have hby := canonical_initialized_by_all init ω s T he i
  have hp := (canonical_initialized_first init ω s T he i).1
  by_contra hnot
  have hlt : (virtualTimes init ω s).initialized i < s := by omega
  have hp' : 3 ≤ (virtualLabels init ω ((virtualTimes init ω s).initialized i) i).phase.val := hp
  rw [virtualLabels_eq_labelsAt_through_asyncEntry init ω s T he _ hby] at hp'
  have hlow := he.first_phase_seed.2 _ hlt _
    (labelsAt_mem_trace init ω ((virtualTimes init ω s).initialized i) i)
  omega

theorem canonical_counter_reset (init : InputCfg n) (ω : InputLog n)
    (s T : ℕ) (he : AsyncEntry init ω s T) (i : Fin init.card)
    (hi : fixedRoleL init (virtualLabels init ω s) .clock i) :
    (virtualLabels init ω ((virtualTimes init ω s).initialized i) i).counter.val =
      50 * (PhaseThreeModel.Numeric.hourIndex n + 1) := by
  have hby := canonical_initialized_by_all init ω s T he i
  have hseed := seed_le_canonical_initialized init ω s T he i
  have hfirst := (canonical_initialized_first init ω s T he i).1
  have henv := virtualLabels_clockEnvironment_of_asyncEntry init ω s T he
  have hphase :
      (virtualLabels init ω ((virtualTimes init ω s).initialized i) i).phase.val = 3 :=
    le_antisymm ((henv _ hseed).phase_range i).2 hfirst
  have hmono := virtual_counter_nonincrease init ω s T he i hi _ hseed hphase T hby
  have hroles := virtualLabels_roles_fixed_of_asyncEntry init ω s T he
  have hr : (virtualLabels init ω T i).role = .clock := by
    rw [hroles T he.order i, ← hroles s le_rfl i]
    exact hi
  have hresetT :
      (virtualLabels init ω T i).counter.val = 50 * (PhaseThreeModel.Numeric.hourIndex n + 1) := by
    rw [virtualLabels_eq_labelsAt_through_asyncEntry init ω s T he T le_rfl] at hr ⊢
    exact he.advanced_profile.clock_counter _ (labelsAt_mem_trace init ω T i) hr
  rw [hresetT] at hmono
  have hbound := (virtualLabels init ω ((virtualTimes init ω s).initialized i) i).counter.isLt
  omega

theorem all_lt_first_cap (init : InputCfg n) (ω : InputLog n)
    (s T : ℕ) (hseed : ω ∈ seedPrefix init s) (he : AsyncEntry init ω s T)
    (hw : PassageTimes init ω s (virtualTimes init ω s)) :
    T < (virtualTimes init ω s).first (clockTop n) := by
  have hp : 1 ≤ clockTop n := by unfold clockTop; omega
  have hf := hw.levels.1 (clockTop n) hp le_rfl
  by_contra hnot
  have hft : (virtualTimes init ω s).first (clockTop n) ≤ T := by omega
  have hm := PhaseThreeClockHourOccupancyRow.core_front_mono_of_asyncEntry
    init ω s T (clockTop n) ((virtualTimes init ω s).first (clockTop n)) T
    hseed he hp le_rfl hf.1 hft
  rw [core_cap_front_zero_at_all init ω s T hseed he] at hm
  have := hf.2.1
  omega

theorem canonical_initialized_before_first_cap (init : InputCfg n) (ω : InputLog n)
    (s T : ℕ) (hseed : ω ∈ seedPrefix init s) (he : AsyncEntry init ω s T)
    (hw : PassageTimes init ω s (virtualTimes init ω s)) (i : Fin init.card) :
    (virtualTimes init ω s).initialized i < (virtualTimes init ω s).first (clockTop n) :=
  lt_of_le_of_lt (canonical_initialized_by_all init ω s T he i)
    (all_lt_first_cap init ω s T hseed he hw)

structure InitializationRow (init : InputCfg n) (ω : InputLog n) (s T : ℕ) : Prop where
  initialized_first : ∀ i, fixedRoleL init (virtualLabels init ω s) .clock i →
    firstHit
      (fun a : AgentState (PhaseThreeModel.Numeric.hourIndex n) 256 => 3 ≤ a.phase.val)
      (fun v => virtualLabels init ω v i) ((virtualTimes init ω s).initialized i)
  initialized_by_all : ∀ i, fixedRoleL init (virtualLabels init ω s) .clock i →
    (virtualTimes init ω s).initialized i ≤ T
  counter_reset : ∀ i, fixedRoleL init (virtualLabels init ω s) .clock i →
    (virtualLabels init ω ((virtualTimes init ω s).initialized i) i).counter.val =
      50 * (PhaseThreeModel.Numeric.hourIndex n + 1)
  initialized_before_first_cap : ∀ i, fixedRoleL init (virtualLabels init ω s) .clock i →
    (virtualTimes init ω s).initialized i < (virtualTimes init ω s).first (clockTop n)

theorem initialization_row_of_passages (init : InputCfg n) (ω : InputLog n)
    (s T : ℕ) (hseed : ω ∈ seedPrefix init s) (he : AsyncEntry init ω s T)
    (hw : PassageTimes init ω s (virtualTimes init ω s)) :
    InitializationRow init ω s T where
  initialized_first := fun i _ => canonical_initialized_first init ω s T he i
  initialized_by_all := fun i _ => canonical_initialized_by_all init ω s T he i
  counter_reset := fun i hi => canonical_counter_reset init ω s T he i hi
  initialized_before_first_cap := fun i _ =>
    canonical_initialized_before_first_cap init ω s T hseed he hw i

theorem seed_initialization_row_null (init : InputCfg n)
    (hc : 2 ≤ init.card) (hn : 42 ≤ n) (s : ℕ) :
    law init (canonicalFieldFailureAt init s (InitializationRow init)) = 0 :=
  seed_canonical_field_null init hc hn s (InitializationRow init)
    (fun ω T hs he hw => initialization_row_of_passages init ω s T hs he hw)

theorem initialization_row_global_null (init : InputCfg n)
    (hc : 2 ≤ init.card) (hn : 42 ≤ n) :
    law init (rowFailure init (InitializationRow init)) = 0 :=
  canonical_field_global_null init hc hn (InitializationRow init)
    (fun ω s T hs he hw => initialization_row_of_passages init ω s T hs he hw)

def BeforeTwentyRow (init : InputCfg n) (ω : InputLog n) (s : ℕ) (_T : ℕ) : Prop :=
  (virtualTimes init ω s).activation ≤ (virtualTimes init ω s).bulk 20

theorem activation_row_of_before_twenty (init : InputCfg n) (hn : 1 ≤ n)
    (ω : InputLog n) (s T : ℕ) (hseed : ω ∈ seedPrefix init s)
    (he : AsyncEntry init ω s T)
    (hw : PassageTimes init ω s (virtualTimes init ω s))
    (hb : BeforeTwentyRow init ω s T) : activationRow init ω s T := by
  have hj := initialization_row_of_passages init ω s T hseed he hw
  exact
    { activation_first := hw.hours.1
      all_before_cap := (passage_order_rows init hn ω s T _ hseed he hw).2.1
      activation_before_twenty := hb
      initialized_first := hj.initialized_first
      initialized_by_all := hj.initialized_by_all
      counter_reset := hj.counter_reset
      initialized_before_first_cap := hj.initialized_before_first_cap }

theorem activation_row_failure_le_before_twenty (init : InputCfg n)
    (hc : 2 ≤ init.card) (hn : 42 ≤ n) :
    law init (rowFailure init (activationRow init)) ≤
      law init (rowFailure init (BeforeTwentyRow init)) := by
  have hsub : rowFailure init (activationRow init) ⊆
      rowFailure init (BeforeTwentyRow init) ∪
      rowFailure init (fun ω s _T => PassageTimes init ω s (virtualTimes init ω s)) := by
    rintro ω ⟨s, T, hs, hT, he, hbad⟩
    by_cases hw : PassageTimes init ω s (virtualTimes init ω s)
    · left
      refine ⟨s, T, hs, hT, he, ?_⟩
      intro hb
      exact hbad (activation_row_of_before_twenty init (by omega)
        ω s T ⟨hs, he.seed_profile⟩ he hw hb)
    · exact Or.inr ⟨s, T, hs, hT, he, hw⟩
  calc
    law init (rowFailure init (activationRow init)) ≤ law init _ := measure_mono hsub
    _ ≤ law init (rowFailure init (BeforeTwentyRow init)) +
        law init (rowFailure init
          (fun ω s _T => PassageTimes init ω s (virtualTimes init ω s))) :=
      measure_union_le _ _
    _ = law init (rowFailure init (BeforeTwentyRow init)) := by
      rw [canonical_passage_times_global_null init hc hn, add_zero]

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockInitializationRows

end
