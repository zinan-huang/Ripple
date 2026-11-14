-- Ripple/PopulationProtocol/ExactMajority/Probability/LateTimerCounterStep.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.AdvanceRegimeDispatchFive
import Ripple.PopulationProtocol.ExactMajority.Probability.AdvanceOvershootSource
import Ripple.PopulationProtocol.ExactMajority.Probability.AdvancePairBound

/-!
# Per-step counter accounting for Clocks in the late timed phases (5..8)

Transition-level facts, both orientations, for a Clock `a` (left) or `b` (right) that
ends an interaction at phase `p` with `5 <= p <= 8`, when both agents are
well-formed and at phase `<= p`:

* if the Clock already had phase `p`, its counter dropped by exactly one;
* if it entered phase `p` in this interaction (by its own counter advance or dragged
  by the epidemic), `50 (L+1) <= counter' + 1`.

No `Wf` is assumed beyond `WfAgent` of the two interacting agents, and no
clock-clock hypothesis on the partner.
-/

noncomputable section

namespace Ripple.PopulationProtocol.ExactMajority

namespace AdvanceNoOvershoot

variable {L K : ℕ}

/-- The epidemic update is symmetric up to swapping the two outputs. -/
theorem epidemic_swap (a b : AgentState L K) :
    phaseEpidemicUpdate L K a b =
      ((phaseEpidemicUpdate L K b a).2, (phaseEpidemicUpdate L K b a).1) := by
  unfold phaseEpidemicUpdate
  dsimp only
  rw [max_comm a.phase b.phase]
  by_cases h : (a.phase.val < 10 ∨ b.phase.val < 10) ∧
      ((runInitsBetween L K a.phase.val (max b.phase a.phase).val
          { a with phase := max b.phase a.phase }).phase.val = 10 ∨
        (runInitsBetween L K b.phase.val (max b.phase a.phase).val
          { b with phase := max b.phase a.phase }).phase.val = 10)
  · have h' : (b.phase.val < 10 ∨ a.phase.val < 10) ∧
        ((runInitsBetween L K b.phase.val (max b.phase a.phase).val
            { b with phase := max b.phase a.phase }).phase.val = 10 ∨
          (runInitsBetween L K a.phase.val (max b.phase a.phase).val
            { a with phase := max b.phase a.phase }).phase.val = 10) :=
      ⟨h.1.symm, h.2.symm⟩
    rw [if_pos h, if_pos h']
  · have h' : ¬ ((b.phase.val < 10 ∨ a.phase.val < 10) ∧
        ((runInitsBetween L K b.phase.val (max b.phase a.phase).val
            { b with phase := max b.phase a.phase }).phase.val = 10 ∨
          (runInitsBetween L K a.phase.val (max b.phase a.phase).val
            { a with phase := max b.phase a.phase }).phase.val = 10)) := by
      intro hh
      exact h ⟨hh.1.symm, hh.2.symm⟩
    rw [if_neg h, if_neg h']

/-- The right epidemic output of a Clock is a Clock. -/
theorem phaseEpidemicUpdate_second_preserves_clock_role_of
    (a b : AgentState L K) (hb : b.role = .clock) :
    (phaseEpidemicUpdate L K a b).2.role = .clock := by
  have hswap := congrArg Prod.snd (epidemic_swap (L := L) (K := K) a b)
  have hswap' : (phaseEpidemicUpdate L K a b).2 =
      (phaseEpidemicUpdate L K b a).1 := hswap.symm ▸ rfl
  rw [hswap']
  exact phaseEpidemicUpdate_first_preserves_clock_role L K b a hb

/-- `phaseInit p` for `5 <= p <= 8` resets a Clock's counter and keeps its phase. -/
theorem phaseInit_clock_reset (p : Fin 11) (h5 : 5 ≤ p.val) (h8 : p.val ≤ 8)
    (a : AgentState L K) (hc : a.role = .clock) :
    (phaseInit L K p a).counter.val = 50 * (L + 1) ∧
      (phaseInit L K p a).phase = a.phase := by
  obtain ⟨pv, hpv⟩ := p
  simp only at h5 h8
  interval_cases pv <;> simp [phaseInit, hc]

/-- Entering phase `p` (`5 <= p <= 8`) by the counter advance resets a Clock's counter. -/
theorem advancePhaseWithInit_counter_reset (e : AgentState L K)
    (hc : e.role = .clock) (h5 : 4 ≤ e.phase.val) (h8 : e.phase.val ≤ 7) :
    (advancePhaseWithInit L K e).phase.val = e.phase.val + 1 ∧
      (advancePhaseWithInit L K e).counter.val = 50 * (L + 1) := by
  have hlt : e.phase.val < 10 := by omega
  have hrole : (advancePhase L K e).role = .clock := by
    rw [advancePhase_role]; exact hc
  have hphase : (advancePhase L K e).phase.val = e.phase.val + 1 := by
    unfold advancePhase
    rw [dif_pos hlt]
  have hpi := phaseInit_clock_reset (L := L) (K := K) (advancePhase L K e).phase
    (by omega) (by omega) (advancePhase L K e) hrole
  unfold advancePhaseWithInit
  dsimp only
  exact ⟨by rw [hpi.2]; exact hphase, hpi.1⟩

/-- A counter-zero advance changes the phase. -/
theorem advancePhaseWithInit_phase_ne_self (e : AgentState L K)
    (hlt : e.phase.val < 10) :
    (advancePhaseWithInit L K e).phase.val ≠ e.phase.val := by
  have hphase : (advancePhase L K e).phase.val = e.phase.val + 1 := by
    unfold advancePhase
    rw [dif_pos hlt]
  unfold advancePhaseWithInit
  dsimp only
  rcases phaseInit_phase_eq_or_ten (L := L) (K := K)
      (advancePhase L K e).phase (advancePhase L K e) with h | h
  · omega
  · omega

/-! ## Dispatcher outputs for a Clock in the timed phases -/

theorem dispatch_first_clock_std (e f : AgentState L K) (hc : e.role = .clock)
    (h5 : 5 ≤ e.phase.val) (h8 : e.phase.val ≤ 8) :
    (dispatchOut L K e f).1 = stdCounterSubroutine L K e := by
  unfold dispatchOut
  rcases hpv : e.phase with ⟨pv, hlt⟩
  have he : e.phase.val = pv := by rw [hpv]
  try simp only [hpv]
  have h5' : 5 ≤ pv := by omega
  have h8' : pv ≤ 8 := by omega
  interval_cases pv
  · exact Phase5Transition_left_clock e f hc
  · exact Phase6Transition_left_clock e f hc
  · exact Phase7Transition_left_clock e f hc
  · exact Phase8Transition_left_clock e f hc

theorem dispatch_second_clock_std (e f : AgentState L K) (hc : f.role = .clock)
    (h5 : 5 ≤ e.phase.val) (h8 : e.phase.val ≤ 8) :
    (dispatchOut L K e f).2 = stdCounterSubroutine L K f := by
  unfold dispatchOut
  rcases hpv : e.phase with ⟨pv, hlt⟩
  have he : e.phase.val = pv := by rw [hpv]
  try simp only [hpv]
  have h5' : 5 ≤ pv := by omega
  have h8' : pv ≤ 8 := by omega
  interval_cases pv
  · exact Phase5Transition_right_clock e f hc
  · exact Phase6Transition_right_clock e f hc
  · exact Phase7Transition_right_clock e f hc
  · exact Phase8Transition_right_clock e f hc

/-- If the first dispatched output of a Clock moves up one phase (phases 4..7), it is
`advancePhaseWithInit`. -/
theorem dispatch_first_clock_advance (e f : AgentState L K) (hc : e.role = .clock)
    (h4 : 4 ≤ e.phase.val) (h7 : e.phase.val ≤ 7)
    (hadv : (dispatchOut L K e f).1.phase.val = e.phase.val + 1) :
    (dispatchOut L K e f).1 = advancePhaseWithInit L K e := by
  by_cases h4e : e.phase.val = 4
  · unfold dispatchOut at hadv ⊢
    rcases hpv : e.phase with ⟨pv, hlt⟩
    have he : e.phase.val = pv := by rw [hpv]
    have hpv4 : pv = 4 := by omega
    subst hpv4
    simp only [hpv] at hadv ⊢
    unfold Phase4Transition at hadv ⊢
    dsimp only at hadv ⊢
    split_ifs at hadv ⊢ with hb
    · rfl
    · simp only at hadv; omega
  · have h5 : 5 ≤ e.phase.val := by omega
    rw [dispatch_first_clock_std e f hc h5 (by omega)] at hadv ⊢
    unfold stdCounterSubroutine at hadv ⊢
    split_ifs at hadv ⊢ with h0
    · rfl
    · simp only at hadv; omega

theorem dispatch_second_clock_advance (e f : AgentState L K) (hc : f.role = .clock)
    (h4 : 4 ≤ e.phase.val) (h7 : e.phase.val ≤ 7)
    (hadv : (dispatchOut L K e f).2.phase.val = f.phase.val + 1)
    (hef : e.phase.val = f.phase.val) :
    (dispatchOut L K e f).2 = advancePhaseWithInit L K f := by
  by_cases h4e : e.phase.val = 4
  · unfold dispatchOut at hadv ⊢
    rcases hpv : e.phase with ⟨pv, hlt⟩
    have he : e.phase.val = pv := by rw [hpv]
    have hpv4 : pv = 4 := by omega
    subst hpv4
    simp only [hpv] at hadv ⊢
    unfold Phase4Transition at hadv ⊢
    dsimp only at hadv ⊢
    split_ifs at hadv ⊢ with hb
    · rfl
    · simp only at hadv; omega
  · have h5 : 5 ≤ e.phase.val := by omega
    rw [dispatch_second_clock_std e f hc h5 (by omega)] at hadv ⊢
    unfold stdCounterSubroutine at hadv ⊢
    split_ifs at hadv ⊢ with h0
    · rfl
    · simp only at hadv; omega

/-! ## The counter step, left orientation -/

theorem timer_left_counter_step (p : ℕ) (hp5 : 5 ≤ p) (hp8 : p ≤ 8)
    (a b : AgentState L K)
    (hwa : WfAgent (L := L) (K := K) a) (hwb : WfAgent (L := L) (K := K) b)
    (hap : a.phase.val ≤ p) (hbp : b.phase.val ≤ p)
    (hclock : a.role = .clock)
    (hout : (Transition L K a b).1.phase.val = p) :
    (Transition L K a b).1.role = .clock ∧
      (a.phase.val = p → a.counter.val ≤ (Transition L K a b).1.counter.val + 1) ∧
      (a.phase.val < p → 50 * (L + 1) ≤ (Transition L K a b).1.counter.val + 1) ∧
      (max a.phase.val b.phase.val < p →
        (Transition L K a b).1.counter.val = 50 * (L + 1)) := by
  have heq := transition_eq_dispatch a b
  have hepmax : (phaseEpidemicUpdate L K a b).1.phase.val = max a.phase.val b.phase.val :=
    phaseEpidemicUpdate_left_phase_eq_max_of_wf a b hwa hwb (by omega) (by omega)
  have hle := Transition_left_phase_le_ep_succ_of_wf a b hwa hwb (by omega) (by omega)
  have hecl : (phaseEpidemicUpdate L K a b).1.role = .clock :=
    phaseEpidemicUpdate_first_preserves_clock_role L K a b hclock
  set e := (phaseEpidemicUpdate L K a b).1 with he
  set f := (phaseEpidemicUpdate L K a b).2 with hf
  have hphase1 : (Transition L K a b).1.phase.val = (dispatchOut L K e f).1.phase.val := by
    rw [heq]
    exact finishPhase10Entry_phase_val L K _ _
  have hD : (dispatchOut L K e f).1.phase.val = p := by omega
  have hfin : (Transition L K a b).1 = (dispatchOut L K e f).1 := by
    rw [heq]
    exact finishPhase10Entry_eq_self_of_after_ne_10 L K _ _ (by omega)
  rw [hfin]
  rcases (by omega : max a.phase.val b.phase.val = p ∨
      max a.phase.val b.phase.val + 1 = p) with hm | hm
  · -- the pair already sits at phase p
    have hep : e.phase.val = p := by omega
    have hstd := dispatch_first_clock_std e f hecl (by omega) (by omega)
    rw [hstd] at hD ⊢
    have hrole : (stdCounterSubroutine L K e).role = .clock :=
      stdCounterSubroutine_clock_role_eq L K e hecl
    refine ⟨hrole, ?_, ?_, fun hlt => by omega⟩
    · intro hapeq
      have hba : b.phase.val ≤ a.phase.val := by omega
      obtain ⟨hctr, -, -⟩ := phaseEpidemicUpdate_left_id_of_ge a b hba
      have hcne : e.counter.val ≠ 0 := by
        intro h0
        have := advancePhaseWithInit_phase_ne_self e (by omega)
        unfold stdCounterSubroutine at hD
        rw [dif_pos h0] at hD
        omega
      unfold stdCounterSubroutine at ⊢
      rw [dif_neg hcne]
      have : e.counter.val = a.counter.val := by rw [he, hctr]
      simp only
      omega
    · intro halt
      have himm : e.counter.val = 50 * (L + 1) :=
        phaseEpidemicUpdate_left_immigrant_full a b p
          (by unfold CounterTimedPhase; omega) halt hecl hep
      have hcne : e.counter.val ≠ 0 := by
        rw [himm]; omega
      unfold stdCounterSubroutine
      rw [dif_neg hcne]
      simp only
      omega
  · -- the pair is at phase p - 1 and the Clock advances into phase p
    have hep : e.phase.val + 1 = p := by omega
    have hadv := dispatch_first_clock_advance e f hecl (by omega) (by omega)
      (by omega)
    rw [hadv]
    have hreset := advancePhaseWithInit_counter_reset e hecl (by omega) (by omega)
    refine ⟨advancePhaseWithInit_clock_role_eq L K e hecl, ?_, ?_, ?_⟩
    · intro hapeq; omega
    · intro _; rw [hreset.2]; omega
    · intro _; exact hreset.2

/-! ## The counter step, right orientation -/

theorem timer_right_counter_step (p : ℕ) (hp5 : 5 ≤ p) (hp8 : p ≤ 8)
    (a b : AgentState L K)
    (hwa : WfAgent (L := L) (K := K) a) (hwb : WfAgent (L := L) (K := K) b)
    (hap : a.phase.val ≤ p) (hbp : b.phase.val ≤ p)
    (hclock : b.role = .clock)
    (hout : (Transition L K a b).2.phase.val = p) :
    (Transition L K a b).2.role = .clock ∧
      (b.phase.val = p → b.counter.val ≤ (Transition L K a b).2.counter.val + 1) ∧
      (b.phase.val < p → 50 * (L + 1) ≤ (Transition L K a b).2.counter.val + 1) ∧
      (max a.phase.val b.phase.val < p →
        (Transition L K a b).2.counter.val = 50 * (L + 1)) := by
  have heq := transition_eq_dispatch a b
  have hepmax : (phaseEpidemicUpdate L K a b).2.phase.val = max a.phase.val b.phase.val :=
    phaseEpidemicUpdate_right_phase_eq_max_of_wf a b hwa hwb (by omega) (by omega)
  have hle := Transition_right_phase_le_ep_succ_of_wf a b hwa hwb (by omega) (by omega)
  have hecl : (phaseEpidemicUpdate L K a b).2.role = .clock :=
    phaseEpidemicUpdate_second_preserves_clock_role_of a b hclock
  have hef := epidemic_phases_eq a b
  set e := (phaseEpidemicUpdate L K a b).1 with he
  set f := (phaseEpidemicUpdate L K a b).2 with hf
  have hphase2 : (Transition L K a b).2.phase.val = (dispatchOut L K e f).2.phase.val := by
    rw [heq]
    exact finishPhase10Entry_phase_val L K _ _
  have hD : (dispatchOut L K e f).2.phase.val = p := by omega
  have hfin : (Transition L K a b).2 = (dispatchOut L K e f).2 := by
    rw [heq]
    exact finishPhase10Entry_eq_self_of_after_ne_10 L K _ _ (by omega)
  rw [hfin]
  rcases (by omega : max a.phase.val b.phase.val = p ∨
      max a.phase.val b.phase.val + 1 = p) with hm | hm
  · have hfp : f.phase.val = p := by omega
    have hep : e.phase.val = p := by omega
    have hstd := dispatch_second_clock_std e f hecl (by omega) (by omega)
    rw [hstd] at hD ⊢
    have hrole : (stdCounterSubroutine L K f).role = .clock :=
      stdCounterSubroutine_clock_role_eq L K f hecl
    refine ⟨hrole, ?_, ?_, fun hlt => by omega⟩
    · intro hbpeq
      have hab : a.phase.val ≤ b.phase.val := by omega
      obtain ⟨hctr, -, -⟩ := phaseEpidemicUpdate_right_id_of_ge a b hab
      have hcne : f.counter.val ≠ 0 := by
        intro h0
        have := advancePhaseWithInit_phase_ne_self f (by omega)
        unfold stdCounterSubroutine at hD
        rw [dif_pos h0] at hD
        omega
      unfold stdCounterSubroutine
      rw [dif_neg hcne]
      have : f.counter.val = b.counter.val := by rw [hf, hctr]
      simp only
      omega
    · intro hblt
      have himm : f.counter.val = 50 * (L + 1) :=
        phaseEpidemicUpdate_right_immigrant_full a b p
          (by unfold CounterTimedPhase; omega) hblt hecl hfp
      have hcne : f.counter.val ≠ 0 := by
        rw [himm]; omega
      unfold stdCounterSubroutine
      rw [dif_neg hcne]
      simp only
      omega
  · have hfp : f.phase.val + 1 = p := by omega
    have hadv := dispatch_second_clock_advance e f hecl (by omega) (by omega)
      (by omega) hef
    rw [hadv]
    have hreset := advancePhaseWithInit_counter_reset f hecl (by omega) (by omega)
    refine ⟨advancePhaseWithInit_clock_role_eq L K f hecl, ?_, ?_, ?_⟩
    · intro hbpeq; omega
    · intro _; rw [hreset.2]; omega
    · intro _; exact hreset.2

/-! ## Non-Clocks do not advance in the timed phases -/

theorem Phase5Transition_left_phase_eq_of_not_clock (e f : AgentState L K)
    (hc : e.role ≠ .clock) :
    (Phase5Transition L K e f).1.phase.val = e.phase.val := by
  simp only [Phase5Transition]
  split_ifs with h1 h2 <;> simp_all

theorem Phase5Transition_right_phase_eq_of_not_clock (e f : AgentState L K)
    (hc : f.role ≠ .clock) :
    (Phase5Transition L K e f).2.phase.val = f.phase.val := by
  simp only [Phase5Transition]
  split_ifs with h1 h2 <;> simp_all

theorem dispatch_first_not_clock_phase (e f : AgentState L K) (hc : e.role ≠ .clock)
    (h5 : 5 ≤ e.phase.val) (h8 : e.phase.val ≤ 8) :
    (dispatchOut L K e f).1.phase.val = e.phase.val := by
  unfold dispatchOut
  rcases hpv : e.phase with ⟨pv, hlt⟩
  have he : e.phase.val = pv := by rw [hpv]
  try simp only [hpv]
  have h5' : 5 ≤ pv := by omega
  have h8' : pv ≤ 8 := by omega
  interval_cases pv
  · exact (Phase5Transition_left_phase_eq_of_not_clock e f hc).trans (by assumption)
  · exact (Phase6Transition_left_phase_eq_of_not_clock e f hc).trans (by assumption)
  · exact (Phase7Transition_left_phase_eq_of_not_clock e f hc).trans (by assumption)
  · exact (Phase8Transition_left_phase_eq_of_not_clock e f hc).trans (by assumption)

theorem dispatch_second_not_clock_phase (e f : AgentState L K) (hc : f.role ≠ .clock)
    (h5 : 5 ≤ e.phase.val) (h8 : e.phase.val ≤ 8) (hef : e.phase.val = f.phase.val) :
    (dispatchOut L K e f).2.phase.val = f.phase.val := by
  unfold dispatchOut
  rcases hpv : e.phase with ⟨pv, hlt⟩
  have he : e.phase.val = pv := by rw [hpv]
  try simp only [hpv]
  have h5' : 5 ≤ pv := by omega
  have h8' : pv ≤ 8 := by omega
  interval_cases pv
  · exact Phase5Transition_right_phase_eq_of_not_clock e f hc
  · exact Phase6Transition_right_phase_eq_of_not_clock e f hc
  · exact Phase7Transition_right_phase_eq_of_not_clock e f hc
  · exact Phase8Transition_right_phase_eq_of_not_clock e f hc

/-! ## The zero test -/

theorem timer_left_advance (p : ℕ) (hp5 : 5 ≤ p) (hp8 : p ≤ 8)
    (a b : AgentState L K)
    (hwa : WfAgent (L := L) (K := K) a) (hwb : WfAgent (L := L) (K := K) b)
    (hap : a.phase.val ≤ p) (hbp : b.phase.val ≤ p)
    (hout : p + 1 ≤ (Transition L K a b).1.phase.val) :
    a.role = .clock ∧ a.phase.val = p ∧ a.counter.val = 0 := by
  have heq := transition_eq_dispatch a b
  have hepmax : (phaseEpidemicUpdate L K a b).1.phase.val = max a.phase.val b.phase.val :=
    phaseEpidemicUpdate_left_phase_eq_max_of_wf a b hwa hwb (by omega) (by omega)
  have hle := Transition_left_phase_le_ep_succ_of_wf a b hwa hwb (by omega) (by omega)
  have hmax : max a.phase.val b.phase.val = p := by omega
  have hout' : (Transition L K a b).1.phase.val = p + 1 := by omega
  set e := (phaseEpidemicUpdate L K a b).1 with he
  set f := (phaseEpidemicUpdate L K a b).2 with hf
  have hphase1 : (Transition L K a b).1.phase.val = (dispatchOut L K e f).1.phase.val := by
    rw [heq]
    exact finishPhase10Entry_phase_val L K _ _
  have hD : (dispatchOut L K e f).1.phase.val = p + 1 := by omega
  have hep : e.phase.val = p := by omega
  by_cases hc : e.role = .clock
  · have hstd := dispatch_first_clock_std e f hc (by omega) (by omega)
    rw [hstd] at hD
    have h0 : e.counter.val = 0 := by
      by_contra hne
      unfold stdCounterSubroutine at hD
      rw [dif_neg hne] at hD
      simp only at hD
      omega
    have hapeq : a.phase.val = p := by
      by_contra hne
      have halt : a.phase.val < p := by omega
      have himm : e.counter.val = 50 * (L + 1) :=
        phaseEpidemicUpdate_left_immigrant_full a b p
          (by unfold CounterTimedPhase; omega) halt hc hep
      omega
    have hba : b.phase.val ≤ a.phase.val := by omega
    obtain ⟨hctr, hrole, -⟩ := phaseEpidemicUpdate_left_id_of_ge a b hba
    refine ⟨?_, hapeq, ?_⟩
    · rw [← hrole]; exact hc
    · rw [show a.counter.val = e.counter.val from by rw [he, hctr]]; exact h0
  · have := dispatch_first_not_clock_phase e f hc (by omega) (by omega)
    omega

theorem timer_right_advance (p : ℕ) (hp5 : 5 ≤ p) (hp8 : p ≤ 8)
    (a b : AgentState L K)
    (hwa : WfAgent (L := L) (K := K) a) (hwb : WfAgent (L := L) (K := K) b)
    (hap : a.phase.val ≤ p) (hbp : b.phase.val ≤ p)
    (hout : p + 1 ≤ (Transition L K a b).2.phase.val) :
    b.role = .clock ∧ b.phase.val = p ∧ b.counter.val = 0 := by
  have heq := transition_eq_dispatch a b
  have hepmax : (phaseEpidemicUpdate L K a b).2.phase.val = max a.phase.val b.phase.val :=
    phaseEpidemicUpdate_right_phase_eq_max_of_wf a b hwa hwb (by omega) (by omega)
  have hle := Transition_right_phase_le_ep_succ_of_wf a b hwa hwb (by omega) (by omega)
  have hef := epidemic_phases_eq a b
  have hmax : max a.phase.val b.phase.val = p := by omega
  have hout' : (Transition L K a b).2.phase.val = p + 1 := by omega
  set e := (phaseEpidemicUpdate L K a b).1 with he
  set f := (phaseEpidemicUpdate L K a b).2 with hf
  have hphase2 : (Transition L K a b).2.phase.val = (dispatchOut L K e f).2.phase.val := by
    rw [heq]
    exact finishPhase10Entry_phase_val L K _ _
  have hD : (dispatchOut L K e f).2.phase.val = p + 1 := by omega
  have hfp : f.phase.val = p := by omega
  by_cases hc : f.role = .clock
  · have hstd := dispatch_second_clock_std e f hc (by omega) (by omega)
    rw [hstd] at hD
    have h0 : f.counter.val = 0 := by
      by_contra hne
      unfold stdCounterSubroutine at hD
      rw [dif_neg hne] at hD
      simp only at hD
      omega
    have hbpeq : b.phase.val = p := by
      by_contra hne
      have hblt : b.phase.val < p := by omega
      have himm : f.counter.val = 50 * (L + 1) :=
        phaseEpidemicUpdate_right_immigrant_full a b p
          (by unfold CounterTimedPhase; omega) hblt hc hfp
      omega
    have hab : a.phase.val ≤ b.phase.val := by omega
    obtain ⟨hctr, hrole, -⟩ := phaseEpidemicUpdate_right_id_of_ge a b hab
    refine ⟨?_, hbpeq, ?_⟩
    · rw [← hrole]; exact hc
    · rw [show b.counter.val = f.counter.val from by rw [hf, hctr]]; exact h0
  · have := dispatch_second_not_clock_phase e f hc (by omega) (by omega) (by omega)
    omega

end AdvanceNoOvershoot

end Ripple.PopulationProtocol.ExactMajority

end
