/-
Local phase-progress lemmas for the Doty et al. exact-majority protocol.

This file records the simple one-interaction progress triggers.  It does not
claim that a global phase has completed; those statements require the separate
scheduling and invariant arguments for finding an applicable triggering pair.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Protocol.Transition
import Mathlib.Tactic

open Multiset

namespace ExactMajority

variable {L K : ℕ}

private lemma no_phase_init_between_self (p : ℕ) :
    (List.range 11).filter (fun k => decide (p < k ∧ k ≤ p)) = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro k _ hk
  simp only [decide_eq_true_eq] at hk
  exact Nat.not_lt_of_ge hk.2 hk.1

private lemma runInitsBetween_self (p : ℕ) (a : AgentState L K) :
    runInitsBetween L K p p a = a := by
  unfold runInitsBetween
  rw [no_phase_init_between_self p]
  rfl

private lemma phaseEpidemicUpdate_eq_self_of_phase
    (ph : Fin 11) (hph10 : ph.val ≠ 10)
    (s t : AgentState L K)
    (hs_phase : s.phase = ph) (ht_phase : t.phase = ph) :
    phaseEpidemicUpdate L K s t = (s, t) := by
  unfold phaseEpidemicUpdate
  rw [hs_phase, ht_phase, max_self]
  simp only [runInitsBetween_self]
  cases s
  cases t
  simp_all

/-! ## Shared clock-counter mechanism -/

/-- One standard counter update decreases the counter value while the counter is
positive.  At zero the subroutine advances phase and may run the next phase's
Init, so no counter monotonicity statement is true there. -/
theorem stdCounterSubroutine_counter_le
    (a : AgentState L K) (hpos : 0 < a.counter.val) :
    (stdCounterSubroutine L K a).counter.val ≤ a.counter.val := by
  have hne : a.counter.val ≠ 0 := by omega
  unfold stdCounterSubroutine
  simp [hne]

/-- If the counter is positive, one standard counter update strictly decreases
the counter value. -/
theorem stdCounterSubroutine_counter_lt_of_pos
    (a : AgentState L K) (hpos : 0 < a.counter.val) :
    (stdCounterSubroutine L K a).counter.val < a.counter.val := by
  have hne : a.counter.val ≠ 0 := by omega
  unfold stdCounterSubroutine
  simp only [hne, ↓reduceDIte]
  exact Nat.sub_one_lt hne

/-- Applying the standard counter subroutine to two clock agents never
increases their combined counter value.  The role hypotheses record the intended
use site in timed phases; the subroutine itself is unary and does not inspect
roles. -/
theorem stdCounterSubroutine_counter_descent
    (s t : AgentState L K) (_hs : s.role = .clock) (_ht : t.role = .clock) :
    0 < s.counter.val → 0 < t.counter.val →
    (stdCounterSubroutine L K s).counter.val +
        (stdCounterSubroutine L K t).counter.val ≤
      s.counter.val + t.counter.val := by
  intro hs_pos ht_pos
  exact Nat.add_le_add
    (stdCounterSubroutine_counter_le (L := L) (K := K) s hs_pos)
    (stdCounterSubroutine_counter_le (L := L) (K := K) t ht_pos)

/-- If both counters are positive, applying the standard counter subroutine to
both clock agents strictly decreases their combined counter value. -/
theorem stdCounterSubroutine_counter_strict_descent
    (s t : AgentState L K) (_hs : s.role = .clock) (_ht : t.role = .clock)
    (hs_pos : 0 < s.counter.val) (ht_pos : 0 < t.counter.val) :
    (stdCounterSubroutine L K s).counter.val +
        (stdCounterSubroutine L K t).counter.val <
      s.counter.val + t.counter.val := by
  have hs_lt := stdCounterSubroutine_counter_lt_of_pos (L := L) (K := K) s hs_pos
  have ht_lt := stdCounterSubroutine_counter_lt_of_pos (L := L) (K := K) t ht_pos
  omega

/-- A zero counter in a nonterminal phase advances at least to the next phase
under the standard counter subroutine.  The destination Init may jump to Phase
10, so equality is not true in general. -/
theorem stdCounterSubroutine_zero_advances
    (a : AgentState L K) (hcounter : a.counter.val = 0) (hphase : a.phase.val < 10) :
    a.phase.val + 1 ≤ (stdCounterSubroutine L K a).phase.val := by
  unfold stdCounterSubroutine advancePhaseWithInit
  simp only [hcounter, ↓reduceDIte]
  have h_adv : (advancePhase L K a).phase.val = a.phase.val + 1 := by
    unfold advancePhase
    simp [hphase]
  calc
    a.phase.val + 1 = (advancePhase L K a).phase.val := by rw [h_adv]
    _ ≤ (phaseInit L K (advancePhase L K a).phase (advancePhase L K a)).phase.val :=
      phaseInit_phase_nondec L K (advancePhase L K a).phase (advancePhase L K a)

@[simp] lemma stdCounterSubroutine_clock_role
    (a : AgentState L K) (ha : a.role = .clock) :
    (stdCounterSubroutine L K a).role = .clock := by
  by_cases hcounter : a.counter.val = 0
  · unfold stdCounterSubroutine
    simp [hcounter, advancePhaseWithInit_clock_role_eq, ha]
  · unfold stdCounterSubroutine
    simp [hcounter, ha]

/-! ## Phase-0 clock progress core -/

/-- In Phase 0, two clock agents use exactly the shared standard counter
subroutine, so their combined counter value cannot increase. -/
theorem Phase0Transition_clock_counter_descent
    (s t : AgentState L K) (hs : s.role = .clock) (ht : t.role = .clock)
    (hs_pos : 0 < s.counter.val) (ht_pos : 0 < t.counter.val) :
    (Phase0Transition L K s t).1.counter.val +
        (Phase0Transition L K s t).2.counter.val ≤
      s.counter.val + t.counter.val := by
  unfold Phase0Transition
  simp [hs, ht,
    stdCounterSubroutine_counter_descent (L := L) (K := K) s t hs ht hs_pos ht_pos]

/-- In Phase 0, if two clock agents interact and at least one counter is
positive, the combined counter value strictly decreases. -/
theorem Phase0Transition_clock_counter_strict_descent
    (s t : AgentState L K) (hs : s.role = .clock) (ht : t.role = .clock)
    (hs_pos : 0 < s.counter.val) (ht_pos : 0 < t.counter.val) :
    (Phase0Transition L K s t).1.counter.val +
        (Phase0Transition L K s t).2.counter.val <
      s.counter.val + t.counter.val := by
  unfold Phase0Transition
  simp [hs, ht,
    stdCounterSubroutine_counter_strict_descent (L := L) (K := K) s t hs ht hs_pos ht_pos]

/-- Local Phase-0 clock progress: once two Phase-0 clocks with zero counters
interact, the Phase-0 rule advances both to Phase 1. -/
theorem Phase0Transition_clock_zero_advances
    (s t : AgentState L K)
    (hs_phase : s.phase.val = 0) (ht_phase : t.phase.val = 0)
    (hs_clock : s.role = .clock) (ht_clock : t.role = .clock)
    (hs_counter : s.counter.val = 0) (ht_counter : t.counter.val = 0) :
    (Phase0Transition L K s t).1.phase.val = 1 ∧
      (Phase0Transition L K s t).2.phase.val = 1 := by
  unfold Phase0Transition stdCounterSubroutine advancePhaseWithInit advancePhase phaseInit
  simp [hs_clock, ht_clock, hs_counter, ht_counter, hs_phase, ht_phase]

/-- Dispatcher version of `Phase0Transition_clock_zero_advances`.  For two
agents already in Phase 0, the phase epidemic is inert before the Phase-0 rule
runs. -/
theorem Transition_phase0_clock_zero_advances
    (s t : AgentState L K)
    (hs_phase : s.phase.val = 0) (ht_phase : t.phase.val = 0)
    (hs_clock : s.role = .clock) (ht_clock : t.role = .clock)
    (hs_counter : s.counter.val = 0) (ht_counter : t.counter.val = 0) :
    (Transition L K s t).1.phase.val = 1 ∧
      (Transition L K s t).2.phase.val = 1 := by
  have hs_phase_eq : s.phase = ⟨0, by decide⟩ := Fin.ext hs_phase
  have ht_phase_eq : t.phase = ⟨0, by decide⟩ := Fin.ext ht_phase
  have hepidemic := phaseEpidemicUpdate_eq_self_of_phase
    (L := L) (K := K) ⟨0, by decide⟩ (by decide) s t hs_phase_eq ht_phase_eq
  have hlocal := Phase0Transition_clock_zero_advances
    (L := L) (K := K) s t hs_phase ht_phase hs_clock ht_clock hs_counter ht_counter
  unfold Transition
  rw [hepidemic]
  simp [hs_phase_eq, hlocal.1, hlocal.2]

/-- A single applicable zero-counter Phase-0 clock-clock interaction is
reachable and produces an agent in Phase at least 1. -/
theorem phase0_clock_zero_advance_step
    (c : Config (AgentState L K)) (s t : AgentState L K)
    (happ : Protocol.Applicable c s t)
    (hs_phase : s.phase.val = 0) (ht_phase : t.phase.val = 0)
    (hs_clock : s.role = .clock) (ht_clock : t.role = .clock)
    (hs_counter : s.counter.val = 0) (ht_counter : t.counter.val = 0) :
    ∃ final, (NonuniformMajority L K).Reachable c final ∧
      ∃ a ∈ final, 1 ≤ a.phase.val := by
  let final := Protocol.stepOrSelf (NonuniformMajority L K) c s t
  refine ⟨final, Protocol.reachable_stepOrSelf c s t, ?_⟩
  have hstep :
      final =
        c - ({s, t} : Multiset (AgentState L K)) +
          ({(Transition L K s t).1, (Transition L K s t).2} :
            Multiset (AgentState L K)) := by
    unfold final Protocol.stepOrSelf
    rw [if_pos happ]
    rfl
  have hadvance := Transition_phase0_clock_zero_advances
    (L := L) (K := K) s t hs_phase ht_phase hs_clock ht_clock hs_counter ht_counter
  refine ⟨(Transition L K s t).1, ?_, ?_⟩
  · rw [hstep]
    simp
  · omega

/-! ## Phase-0 role allocation core -/

/-- Phase-0 role allocation rule 1: two MCR agents become one Main and one CR. -/
theorem Phase0Transition_mcr_mcr_roles
    (s t : AgentState L K) (hs : s.role = .mcr) (ht : t.role = .mcr) :
    (Phase0Transition L K s t).1.role = .main ∧
      (Phase0Transition L K s t).2.role = .cr := by
  unfold Phase0Transition
  simp [hs, ht]

/-- Phase-0 role allocation rule 4: two CR agents become one Clock and one
Reserve.  The first output clock receives the standard initial counter. -/
theorem Phase0Transition_cr_cr_roles
    (s t : AgentState L K) (hs : s.role = .cr) (ht : t.role = .cr) :
    (Phase0Transition L K s t).1.role = .clock ∧
      (Phase0Transition L K s t).1.counter.val = 50 * (L + 1) ∧
      (Phase0Transition L K s t).2.role = .reserve := by
  unfold Phase0Transition
  simp [hs, ht]

/-- Dispatcher Phase-0 role allocation rule 1: two Phase-0 MCR agents become
one Main and one CR, and both outputs remain in Phase 0. -/
theorem Transition_phase0_mcr_mcr_roles
    (s t : AgentState L K)
    (hs_phase : s.phase.val = 0) (ht_phase : t.phase.val = 0)
    (hs : s.role = .mcr) (ht : t.role = .mcr) :
    (Transition L K s t).1.role = .main ∧
      (Transition L K s t).2.role = .cr ∧
      (Transition L K s t).1.phase.val = 0 ∧
      (Transition L K s t).2.phase.val = 0 := by
  have hs_phase_eq : s.phase = ⟨0, by decide⟩ := Fin.ext hs_phase
  have ht_phase_eq : t.phase = ⟨0, by decide⟩ := Fin.ext ht_phase
  have hepidemic := phaseEpidemicUpdate_eq_self_of_phase
    (L := L) (K := K) ⟨0, by decide⟩ (by decide) s t hs_phase_eq ht_phase_eq
  unfold Transition
  rw [hepidemic]
  unfold Phase0Transition
  simp [hs_phase_eq, ht_phase_eq, hs, ht]

/-- Dispatcher Phase-0 role allocation rule 4: two Phase-0 CR agents become
one Clock and one Reserve, and both outputs remain in Phase 0. -/
theorem Transition_phase0_cr_cr_roles
    (s t : AgentState L K)
    (hs_phase : s.phase.val = 0) (ht_phase : t.phase.val = 0)
    (hs : s.role = .cr) (ht : t.role = .cr) :
    (Transition L K s t).1.role = .clock ∧
      (Transition L K s t).1.counter.val = 50 * (L + 1) ∧
      (Transition L K s t).2.role = .reserve ∧
      (Transition L K s t).1.phase.val = 0 ∧
      (Transition L K s t).2.phase.val = 0 := by
  have hs_phase_eq : s.phase = ⟨0, by decide⟩ := Fin.ext hs_phase
  have ht_phase_eq : t.phase = ⟨0, by decide⟩ := Fin.ext ht_phase
  have hepidemic := phaseEpidemicUpdate_eq_self_of_phase
    (L := L) (K := K) ⟨0, by decide⟩ (by decide) s t hs_phase_eq ht_phase_eq
  unfold Transition
  rw [hepidemic]
  unfold Phase0Transition
  simp [hs_phase_eq, ht_phase_eq, hs, ht]

/-- Count agents currently carrying a given Phase-0 role. -/
def roleCount (r : Role) (c : Config (AgentState L K)) : ℕ :=
  Multiset.countP (fun a => a.role = r) c

lemma countP_singleton_of
    {α : Type*} {p : α → Prop} [DecidablePred p] {a : α} (ha : p a) :
    Multiset.countP p ({a} : Multiset α) = 1 := by
  have h :
      Multiset.countP p ({a} : Multiset α) =
        Multiset.card ({a} : Multiset α) :=
    (Multiset.countP_eq_card (p := p) (s := ({a} : Multiset α))).2
      (by
        intro b hb
        have hb_eq : b = a := by simpa using hb
        simpa [hb_eq] using ha)
  simpa using h

lemma countP_singleton_of_not
    {α : Type*} {p : α → Prop} [DecidablePred p] {a : α} (ha : ¬ p a) :
    Multiset.countP p ({a} : Multiset α) = 0 :=
  (Multiset.countP_eq_zero (p := p) (s := ({a} : Multiset α))).2
    (by
      intro b hb hp
      have hb_eq : b = a := by simpa using hb
      exact ha (by simpa [hb_eq] using hp))

private lemma exists_applicable_pair_of_countP_ge_two
    {α : Type*} {p : α → Prop} [DecidablePred p]
    {c : Multiset α} (h : 2 ≤ Multiset.countP p c) :
    ∃ s t, ({s, t} : Multiset α) ≤ c ∧ p s ∧ p t := by
  classical
  let good := c.filter p
  have hgood_card : 2 ≤ good.card := by
    simpa [good, Multiset.countP_eq_card_filter] using h
  have hgood_pos : 0 < good.card := by omega
  rcases Multiset.card_pos_iff_exists_mem.mp hgood_pos with ⟨s, hs⟩
  have herase_pos : 0 < (good.erase s).card := by
    have hcard := Multiset.card_erase_add_one hs
    omega
  rcases Multiset.card_pos_iff_exists_mem.mp herase_pos with ⟨t, ht⟩
  have ht_good : t ∈ good := Multiset.mem_of_mem_erase ht
  have hpair_good : ({s, t} : Multiset α) ≤ good := by
    change s ::ₘ ({t} : Multiset α) ≤ good
    rw [← Multiset.cons_erase hs]
    exact Multiset.cons_le_cons s (Multiset.singleton_le.mpr ht)
  exact ⟨s, t, le_trans hpair_good (Multiset.filter_le p c),
    (Multiset.mem_filter.mp hs).2, (Multiset.mem_filter.mp ht_good).2⟩

lemma exists_applicable_pair_of_roleCount_ge_two
    (r : Role) {c : Config (AgentState L K)}
    (h : 2 ≤ roleCount (L := L) (K := K) r c) :
    ∃ s t, Protocol.Applicable c s t ∧ s.role = r ∧ t.role = r := by
  rcases exists_applicable_pair_of_countP_ge_two
      (p := fun a : AgentState L K => a.role = r) h with
    ⟨s, t, hpair, hs, ht⟩
  exact ⟨s, t, hpair, hs, ht⟩

lemma phase0_mcr_step_data
    (c : Config (AgentState L K)) (s t : AgentState L K)
    (happ : Protocol.Applicable c s t)
    (hphase : ∀ a ∈ c, a.phase.val = 0)
    (hs : s.role = .mcr) (ht : t.role = .mcr) :
    let c' := Protocol.stepOrSelf (NonuniformMajority L K) c s t
    (NonuniformMajority L K).Reachable c c' ∧
      (∀ a ∈ c', a.phase.val = 0) ∧
      roleCount (L := L) (K := K) .mcr c' =
        roleCount (L := L) (K := K) .mcr c - 2 ∧
      roleCount (L := L) (K := K) .cr c' =
        roleCount (L := L) (K := K) .cr c + 1 ∧
      roleCount (L := L) (K := K) .clock c' =
        roleCount (L := L) (K := K) .clock c := by
  classical
  intro c'
  have hs_phase : s.phase.val = 0 := hphase s (Multiset.mem_of_le happ (by simp))
  have ht_phase : t.phase.val = 0 := hphase t (Multiset.mem_of_le happ (by simp))
  have htr := Transition_phase0_mcr_mcr_roles
    (L := L) (K := K) s t hs_phase ht_phase hs ht
  have hpair_mcr :
      Multiset.countP (fun a : AgentState L K => a.role = .mcr)
        ({s, t} : Multiset (AgentState L K)) = 2 := by
    rw [show ({s, t} : Multiset (AgentState L K)) = ({s} : Multiset _) + {t} by rfl,
      Multiset.countP_add,
      countP_singleton_of (p := fun a : AgentState L K => a.role = .mcr) hs,
      countP_singleton_of (p := fun a : AgentState L K => a.role = .mcr) ht]
  have hpair_cr :
      Multiset.countP (fun a : AgentState L K => a.role = .cr)
        ({s, t} : Multiset (AgentState L K)) = 0 := by
    rw [show ({s, t} : Multiset (AgentState L K)) = ({s} : Multiset _) + {t} by rfl,
      Multiset.countP_add,
      countP_singleton_of_not (p := fun a : AgentState L K => a.role = .cr)
        (by simp [hs]),
      countP_singleton_of_not (p := fun a : AgentState L K => a.role = .cr)
        (by simp [ht])]
  have hpair_clock :
      Multiset.countP (fun a : AgentState L K => a.role = .clock)
        ({s, t} : Multiset (AgentState L K)) = 0 := by
    rw [show ({s, t} : Multiset (AgentState L K)) = ({s} : Multiset _) + {t} by rfl,
      Multiset.countP_add,
      countP_singleton_of_not (p := fun a : AgentState L K => a.role = .clock)
        (by simp [hs]),
      countP_singleton_of_not (p := fun a : AgentState L K => a.role = .clock)
        (by simp [ht])]
  have hout_mcr :
      Multiset.countP (fun a : AgentState L K => a.role = .mcr)
        ({(Transition L K s t).1, (Transition L K s t).2} :
          Multiset (AgentState L K)) = 0 := by
    rw [show ({(Transition L K s t).1, (Transition L K s t).2} :
        Multiset (AgentState L K)) =
          ({(Transition L K s t).1} : Multiset _) + {(Transition L K s t).2} by rfl,
      Multiset.countP_add,
      countP_singleton_of_not (p := fun a : AgentState L K => a.role = .mcr)
        (by simp [htr.1]),
      countP_singleton_of_not (p := fun a : AgentState L K => a.role = .mcr)
        (by simp [htr.2.1])]
  have hout_cr :
      Multiset.countP (fun a : AgentState L K => a.role = .cr)
        ({(Transition L K s t).1, (Transition L K s t).2} :
          Multiset (AgentState L K)) = 1 := by
    rw [show ({(Transition L K s t).1, (Transition L K s t).2} :
        Multiset (AgentState L K)) =
          ({(Transition L K s t).1} : Multiset _) + {(Transition L K s t).2} by rfl,
      Multiset.countP_add,
      countP_singleton_of_not (p := fun a : AgentState L K => a.role = .cr)
        (by simp [htr.1]),
      countP_singleton_of (p := fun a : AgentState L K => a.role = .cr) htr.2.1]
  have hout_clock :
      Multiset.countP (fun a : AgentState L K => a.role = .clock)
        ({(Transition L K s t).1, (Transition L K s t).2} :
          Multiset (AgentState L K)) = 0 := by
    rw [show ({(Transition L K s t).1, (Transition L K s t).2} :
        Multiset (AgentState L K)) =
          ({(Transition L K s t).1} : Multiset _) + {(Transition L K s t).2} by rfl,
      Multiset.countP_add,
      countP_singleton_of_not (p := fun a : AgentState L K => a.role = .clock)
        (by simp [htr.1]),
      countP_singleton_of_not (p := fun a : AgentState L K => a.role = .clock)
        (by simp [htr.2.1])]
  have hstep :
      c' =
        c - ({s, t} : Multiset (AgentState L K)) +
          ({(Transition L K s t).1, (Transition L K s t).2} :
            Multiset (AgentState L K)) := by
    unfold c' Protocol.stepOrSelf
    rw [if_pos happ]
    rfl
  refine ⟨Protocol.reachable_stepOrSelf c s t, ?_, ?_, ?_, ?_⟩
  · intro a ha
    rw [hstep] at ha
    rcases Multiset.mem_add.mp ha with ha_old | ha_new
    · exact hphase a (Multiset.mem_of_le (Multiset.sub_le_self c
        ({s, t} : Multiset (AgentState L K))) ha_old)
    · have ha_new' :
          a = (Transition L K s t).1 ∨ a = (Transition L K s t).2 := by
        simpa using ha_new
      rcases ha_new' with rfl | rfl
      · exact htr.2.2.1
      · exact htr.2.2.2
  · rw [hstep]
    unfold roleCount
    rw [Multiset.countP_add,
      Multiset.countP_sub happ (fun a : AgentState L K => a.role = .mcr)]
    rw [hpair_mcr, hout_mcr]
    omega
  · rw [hstep]
    unfold roleCount
    rw [Multiset.countP_add,
      Multiset.countP_sub happ (fun a : AgentState L K => a.role = .cr)]
    rw [hpair_cr, hout_cr]
    omega
  · rw [hstep]
    unfold roleCount
    rw [Multiset.countP_add,
      Multiset.countP_sub happ (fun a : AgentState L K => a.role = .clock)]
    rw [hpair_clock, hout_clock]
    omega

lemma phase0_cr_step_data
    (c : Config (AgentState L K)) (s t : AgentState L K)
    (happ : Protocol.Applicable c s t)
    (hphase : ∀ a ∈ c, a.phase.val = 0)
    (hs : s.role = .cr) (ht : t.role = .cr) :
    let c' := Protocol.stepOrSelf (NonuniformMajority L K) c s t
    (NonuniformMajority L K).Reachable c c' ∧
      (∀ a ∈ c', a.phase.val = 0) ∧
      roleCount (L := L) (K := K) .cr c' =
        roleCount (L := L) (K := K) .cr c - 2 ∧
      roleCount (L := L) (K := K) .clock c' =
        roleCount (L := L) (K := K) .clock c + 1 := by
  classical
  intro c'
  have hs_phase : s.phase.val = 0 := hphase s (Multiset.mem_of_le happ (by simp))
  have ht_phase : t.phase.val = 0 := hphase t (Multiset.mem_of_le happ (by simp))
  have htr := Transition_phase0_cr_cr_roles
    (L := L) (K := K) s t hs_phase ht_phase hs ht
  have hpair_cr :
      Multiset.countP (fun a : AgentState L K => a.role = .cr)
        ({s, t} : Multiset (AgentState L K)) = 2 := by
    rw [show ({s, t} : Multiset (AgentState L K)) = ({s} : Multiset _) + {t} by rfl,
      Multiset.countP_add,
      countP_singleton_of (p := fun a : AgentState L K => a.role = .cr) hs,
      countP_singleton_of (p := fun a : AgentState L K => a.role = .cr) ht]
  have hpair_clock :
      Multiset.countP (fun a : AgentState L K => a.role = .clock)
        ({s, t} : Multiset (AgentState L K)) = 0 := by
    rw [show ({s, t} : Multiset (AgentState L K)) = ({s} : Multiset _) + {t} by rfl,
      Multiset.countP_add,
      countP_singleton_of_not (p := fun a : AgentState L K => a.role = .clock)
        (by simp [hs]),
      countP_singleton_of_not (p := fun a : AgentState L K => a.role = .clock)
        (by simp [ht])]
  have hout_cr :
      Multiset.countP (fun a : AgentState L K => a.role = .cr)
        ({(Transition L K s t).1, (Transition L K s t).2} :
          Multiset (AgentState L K)) = 0 := by
    rw [show ({(Transition L K s t).1, (Transition L K s t).2} :
        Multiset (AgentState L K)) =
          ({(Transition L K s t).1} : Multiset _) + {(Transition L K s t).2} by rfl,
      Multiset.countP_add,
      countP_singleton_of_not (p := fun a : AgentState L K => a.role = .cr)
        (by simp [htr.1]),
      countP_singleton_of_not (p := fun a : AgentState L K => a.role = .cr)
        (by simp [htr.2.2.1])]
  have hout_clock :
      Multiset.countP (fun a : AgentState L K => a.role = .clock)
        ({(Transition L K s t).1, (Transition L K s t).2} :
          Multiset (AgentState L K)) = 1 := by
    rw [show ({(Transition L K s t).1, (Transition L K s t).2} :
        Multiset (AgentState L K)) =
          ({(Transition L K s t).1} : Multiset _) + {(Transition L K s t).2} by rfl,
      Multiset.countP_add,
      countP_singleton_of (p := fun a : AgentState L K => a.role = .clock) htr.1,
      countP_singleton_of_not (p := fun a : AgentState L K => a.role = .clock)
        (by simp [htr.2.2.1])]
  have hstep :
      c' =
        c - ({s, t} : Multiset (AgentState L K)) +
          ({(Transition L K s t).1, (Transition L K s t).2} :
            Multiset (AgentState L K)) := by
    unfold c' Protocol.stepOrSelf
    rw [if_pos happ]
    rfl
  refine ⟨Protocol.reachable_stepOrSelf c s t, ?_, ?_, ?_⟩
  · intro a ha
    rw [hstep] at ha
    rcases Multiset.mem_add.mp ha with ha_old | ha_new
    · exact hphase a (Multiset.mem_of_le (Multiset.sub_le_self c
        ({s, t} : Multiset (AgentState L K))) ha_old)
    · have ha_new' :
          a = (Transition L K s t).1 ∨ a = (Transition L K s t).2 := by
        simpa using ha_new
      rcases ha_new' with rfl | rfl
      · exact htr.2.2.2.1
      · exact htr.2.2.2.2
  · rw [hstep]
    unfold roleCount
    rw [Multiset.countP_add,
      Multiset.countP_sub happ (fun a : AgentState L K => a.role = .cr)]
    rw [hpair_cr, hout_cr]
    omega
  · rw [hstep]
    unfold roleCount
    rw [Multiset.countP_add,
      Multiset.countP_sub happ (fun a : AgentState L K => a.role = .clock)]
    rw [hpair_clock, hout_clock]
    omega

/-- Phase 0 role allocation creates two clock agents from any all-MCR Phase-0
configuration of size at least eight.  The final clock pair is stated using
`Protocol.Applicable`, i.e. `{i, j} ≤ final`, so it correctly handles both
distinct clock states and two copies of the same clock state. -/
theorem phase0_creates_two_clocks
    (c : Config (AgentState L K))
    (hphase0 : ∀ a ∈ c, a.phase.val = 0)
    (hmcr : ∀ a ∈ c, a.role = .mcr)
    (hn : 8 ≤ c.card) :
    ∃ final, (NonuniformMajority L K).Reachable c final ∧
      (∀ a ∈ final, a.phase.val = 0) ∧
      (∃ i j, Protocol.Applicable final i j ∧ i.role = .clock ∧ j.role = .clock) := by
  classical
  have hmcr_count : 8 ≤ roleCount (L := L) (K := K) .mcr c := by
    have hcount :
        roleCount (L := L) (K := K) .mcr c = c.card := by
      simpa [roleCount] using
        (Multiset.countP_eq_card (p := fun a : AgentState L K => a.role = .mcr)
          (s := c)).2 hmcr
    rwa [hcount]
  have hcr_count0 : roleCount (L := L) (K := K) .cr c = 0 := by
    have hnone : ∀ a ∈ c, ¬ a.role = .cr := by
      intro a ha hcr
      have hm := hmcr a ha
      simp [hm] at hcr
    simp [roleCount, Multiset.countP_eq_zero.mpr hnone]
  have hclock_count0 : roleCount (L := L) (K := K) .clock c = 0 := by
    have hnone : ∀ a ∈ c, ¬ a.role = .clock := by
      intro a ha hclock
      have hm := hmcr a ha
      simp [hm] at hclock
    simp [roleCount, Multiset.countP_eq_zero.mpr hnone]
  rcases exists_applicable_pair_of_roleCount_ge_two
      (L := L) (K := K) .mcr (c := c) (by omega) with
    ⟨s₁, t₁, happ₁, hs₁, ht₁⟩
  let c₁ := Protocol.stepOrSelf (NonuniformMajority L K) c s₁ t₁
  rcases phase0_mcr_step_data
      (L := L) (K := K) c s₁ t₁ happ₁ hphase0 hs₁ ht₁ with
    ⟨hreach₁, hphase₁, hmcr₁, hcr₁, hclock₁⟩
  have hmcr_ge₁ : 6 ≤ roleCount (L := L) (K := K) .mcr c₁ := by
    rw [hmcr₁]
    omega
  have hcr_eq₁ : roleCount (L := L) (K := K) .cr c₁ = 1 := by
    rw [hcr₁, hcr_count0]
  have hclock_eq₁ : roleCount (L := L) (K := K) .clock c₁ = 0 := by
    rw [hclock₁, hclock_count0]
  rcases exists_applicable_pair_of_roleCount_ge_two
      (L := L) (K := K) .mcr (c := c₁) (by omega) with
    ⟨s₂, t₂, happ₂, hs₂, ht₂⟩
  let c₂ := Protocol.stepOrSelf (NonuniformMajority L K) c₁ s₂ t₂
  rcases phase0_mcr_step_data
      (L := L) (K := K) c₁ s₂ t₂ happ₂ hphase₁ hs₂ ht₂ with
    ⟨hreach₂, hphase₂, hmcr₂, hcr₂, hclock₂⟩
  have hmcr_ge₂ : 4 ≤ roleCount (L := L) (K := K) .mcr c₂ := by
    rw [hmcr₂]
    omega
  have hcr_eq₂ : roleCount (L := L) (K := K) .cr c₂ = 2 := by
    rw [hcr₂, hcr_eq₁]
  have hclock_eq₂ : roleCount (L := L) (K := K) .clock c₂ = 0 := by
    rw [hclock₂, hclock_eq₁]
  rcases exists_applicable_pair_of_roleCount_ge_two
      (L := L) (K := K) .mcr (c := c₂) (by omega) with
    ⟨s₃, t₃, happ₃, hs₃, ht₃⟩
  let c₃ := Protocol.stepOrSelf (NonuniformMajority L K) c₂ s₃ t₃
  rcases phase0_mcr_step_data
      (L := L) (K := K) c₂ s₃ t₃ happ₃ hphase₂ hs₃ ht₃ with
    ⟨hreach₃, hphase₃, hmcr₃, hcr₃, hclock₃⟩
  have hmcr_ge₃ : 2 ≤ roleCount (L := L) (K := K) .mcr c₃ := by
    rw [hmcr₃]
    omega
  have hcr_eq₃ : roleCount (L := L) (K := K) .cr c₃ = 3 := by
    rw [hcr₃, hcr_eq₂]
  have hclock_eq₃ : roleCount (L := L) (K := K) .clock c₃ = 0 := by
    rw [hclock₃, hclock_eq₂]
  rcases exists_applicable_pair_of_roleCount_ge_two
      (L := L) (K := K) .mcr (c := c₃) hmcr_ge₃ with
    ⟨s₄, t₄, happ₄, hs₄, ht₄⟩
  let c₄ := Protocol.stepOrSelf (NonuniformMajority L K) c₃ s₄ t₄
  rcases phase0_mcr_step_data
      (L := L) (K := K) c₃ s₄ t₄ happ₄ hphase₃ hs₄ ht₄ with
    ⟨hreach₄, hphase₄, _hmcr₄, hcr₄, hclock₄⟩
  have hcr_eq₄ : roleCount (L := L) (K := K) .cr c₄ = 4 := by
    rw [hcr₄, hcr_eq₃]
  have hclock_eq₄ : roleCount (L := L) (K := K) .clock c₄ = 0 := by
    rw [hclock₄, hclock_eq₃]
  rcases exists_applicable_pair_of_roleCount_ge_two
      (L := L) (K := K) .cr (c := c₄) (by rw [hcr_eq₄]; omega) with
    ⟨s₅, t₅, happ₅, hs₅, ht₅⟩
  let c₅ := Protocol.stepOrSelf (NonuniformMajority L K) c₄ s₅ t₅
  rcases phase0_cr_step_data
      (L := L) (K := K) c₄ s₅ t₅ happ₅ hphase₄ hs₅ ht₅ with
    ⟨hreach₅, hphase₅, hcr₅, hclock₅⟩
  have hcr_eq₅ : roleCount (L := L) (K := K) .cr c₅ = 2 := by
    rw [hcr₅, hcr_eq₄]
  have hclock_eq₅ : roleCount (L := L) (K := K) .clock c₅ = 1 := by
    rw [hclock₅, hclock_eq₄]
  rcases exists_applicable_pair_of_roleCount_ge_two
      (L := L) (K := K) .cr (c := c₅) (by rw [hcr_eq₅]) with
    ⟨s₆, t₆, happ₆, hs₆, ht₆⟩
  let c₆ := Protocol.stepOrSelf (NonuniformMajority L K) c₅ s₆ t₆
  rcases phase0_cr_step_data
      (L := L) (K := K) c₅ s₆ t₆ happ₆ hphase₅ hs₆ ht₆ with
    ⟨hreach₆, hphase₆, _hcr₆, hclock₆⟩
  have hclock_final : 2 ≤ roleCount (L := L) (K := K) .clock c₆ := by
    unfold c₆
    rw [hclock₆, hclock_eq₅]
  rcases exists_applicable_pair_of_roleCount_ge_two
      (L := L) (K := K) .clock (c := c₆) hclock_final with
    ⟨i, j, happ_clock, hi_clock, hj_clock⟩
  refine ⟨c₆, ?_, hphase₆, ⟨i, j, happ_clock, hi_clock, hj_clock⟩⟩
  exact Relation.ReflTransGen.trans hreach₁
    (Relation.ReflTransGen.trans hreach₂
      (Relation.ReflTransGen.trans hreach₃
        (Relation.ReflTransGen.trans hreach₄
          (Relation.ReflTransGen.trans hreach₅ hreach₆))))

/-! ## Other timed phase clock progress -/

/-- Phase 1 clock-clock interactions use the shared standard counter subroutine,
so their combined counter value cannot increase. -/
theorem Phase1Transition_clock_counter_descent
    (s t : AgentState L K) (hs : s.role = .clock) (ht : t.role = .clock)
    (hs_pos : 0 < s.counter.val) (ht_pos : 0 < t.counter.val) :
    (Phase1Transition L K s t).1.counter.val +
        (Phase1Transition L K s t).2.counter.val ≤
      s.counter.val + t.counter.val := by
  unfold Phase1Transition clockCounterStep
  simp [hs, ht,
    stdCounterSubroutine_counter_descent (L := L) (K := K) s t hs ht hs_pos ht_pos]

/-- Phase 1 clock-clock interactions strictly decrease the combined counter
value whenever both selected counters are positive. -/
theorem Phase1Transition_clock_counter_strict_descent
    (s t : AgentState L K) (hs : s.role = .clock) (ht : t.role = .clock)
    (hs_pos : 0 < s.counter.val) (ht_pos : 0 < t.counter.val) :
    (Phase1Transition L K s t).1.counter.val +
        (Phase1Transition L K s t).2.counter.val <
      s.counter.val + t.counter.val := by
  unfold Phase1Transition clockCounterStep
  simp [hs, ht,
    stdCounterSubroutine_counter_strict_descent (L := L) (K := K) s t hs ht hs_pos ht_pos]

/-- Local Phase-1 clock progress: once two Phase-1 clocks with zero counters
interact, both advance to Phase 2. -/
theorem Phase1Transition_clock_zero_advances
    (s t : AgentState L K)
    (hs_phase : s.phase.val = 1) (ht_phase : t.phase.val = 1)
    (hs_clock : s.role = .clock) (ht_clock : t.role = .clock)
    (hs_counter : s.counter.val = 0) (ht_counter : t.counter.val = 0) :
    2 ≤ (Phase1Transition L K s t).1.phase.val ∧
      2 ≤ (Phase1Transition L K s t).2.phase.val := by
  unfold Phase1Transition clockCounterStep stdCounterSubroutine advancePhaseWithInit advancePhase phaseInit
  simp [hs_clock, ht_clock, hs_counter, ht_counter, hs_phase, ht_phase, enterPhase10, phase10] <;>
    repeat' split_ifs <;> simp [enterPhase10, phase10] <;>
    omega

/-- Phase 3 clock-clock interactions never increase the combined counter
value.  If the clocks are not yet at the counter branch, the counters are
unchanged; once they are synchronized at the maximum minute, this reduces to
the shared standard counter subroutine. -/
theorem Phase3Transition_clock_counter_descent
    (s t : AgentState L K) (hs : s.role = .clock) (ht : t.role = .clock)
    (hs_pos : 0 < s.counter.val) (ht_pos : 0 < t.counter.val) :
    (Phase3Transition L K s t).1.counter.val +
        (Phase3Transition L K s t).2.counter.val ≤
      s.counter.val + t.counter.val := by
  unfold Phase3Transition
  by_cases hne : s.minute ≠ t.minute
  · simp [hs, ht, hne]
  · by_cases hlt : s.minute.val < K * (L + 1)
    · simp [hs, ht, hne, hlt]
    · simp [hs, ht, hne, hlt,
        stdCounterSubroutine_counter_descent (L := L) (K := K) s t hs ht hs_pos ht_pos]

/-- Phase 3 reaches the shared counter branch only after the two clocks have
the same minute and that minute is at the phase-3 threshold.  Under that real
precondition, zero counters advance both agents to Phase 4. -/
theorem Phase3Transition_clock_zero_advances
    (s t : AgentState L K)
    (hs_phase : s.phase.val = 3) (ht_phase : t.phase.val = 3)
    (hs_clock : s.role = .clock) (ht_clock : t.role = .clock)
    (hminute : s.minute = t.minute)
    (hminute_done : ¬ s.minute.val < K * (L + 1))
    (hs_counter : s.counter.val = 0) (ht_counter : t.counter.val = 0) :
    (Phase3Transition L K s t).1.phase.val = 4 ∧
      (Phase3Transition L K s t).2.phase.val = 4 := by
  have hminute_done_t : ¬ t.minute.val < K * (L + 1) := by
    simpa [hminute] using hminute_done
  unfold Phase3Transition stdCounterSubroutine advancePhaseWithInit advancePhase phaseInit
  simp [hs_clock, ht_clock, hminute, hminute_done_t, hs_counter, ht_counter,
    hs_phase, ht_phase]

/-- Dispatcher Phase-3 counter branch: once two Phase-3 clocks have equal
minutes at the Phase-3 threshold, a zero counter on either selected clock
already produces an agent in Phase at least 4. -/
theorem Transition_phase3_clock_done_counter_zero_advances
    (s t : AgentState L K)
    (hs_phase : s.phase.val = 3) (ht_phase : t.phase.val = 3)
    (hs_clock : s.role = .clock) (ht_clock : t.role = .clock)
    (hminute : s.minute = t.minute)
    (hminute_done : ¬ s.minute.val < K * (L + 1))
    (hzero : s.counter.val = 0 ∨ t.counter.val = 0) :
    4 ≤ (Transition L K s t).1.phase.val ∨
      4 ≤ (Transition L K s t).2.phase.val := by
  have hs_phase_eq : s.phase = ⟨3, by decide⟩ := Fin.ext hs_phase
  have ht_phase_eq : t.phase = ⟨3, by decide⟩ := Fin.ext ht_phase
  have hepidemic := phaseEpidemicUpdate_eq_self_of_phase
    (L := L) (K := K) ⟨3, by decide⟩ (by decide) s t hs_phase_eq ht_phase_eq
  have hminute_done_t : ¬ t.minute.val < K * (L + 1) := by
    simpa [hminute] using hminute_done
  rcases hzero with hs_zero | ht_zero
  · left
    unfold Transition
    rw [hepidemic]
    unfold Phase3Transition stdCounterSubroutine advancePhaseWithInit advancePhase phaseInit
    simp [hs_phase_eq, ht_phase_eq, hs_clock, ht_clock, hminute,
      hminute_done_t, hs_zero]
  · right
    unfold Transition
    rw [hepidemic]
    unfold Phase3Transition stdCounterSubroutine advancePhaseWithInit advancePhase phaseInit
    simp [hs_phase_eq, ht_phase_eq, hs_clock, ht_clock, hminute,
      hminute_done_t, ht_zero]

/-- Dispatcher Phase-3 counter branch with positive counters: the selected
clock pair remains in Phase 3 with equal threshold minutes, and the selected
counter sum strictly decreases. -/
theorem Transition_phase3_clock_done_positive_preserves_and_decreases
    (s t : AgentState L K)
    (hs_phase : s.phase.val = 3) (ht_phase : t.phase.val = 3)
    (hs_clock : s.role = .clock) (ht_clock : t.role = .clock)
    (hminute : s.minute = t.minute)
    (hminute_done : ¬ s.minute.val < K * (L + 1))
    (hs_pos : 0 < s.counter.val) (ht_pos : 0 < t.counter.val) :
    (Transition L K s t).1.phase.val = 3 ∧
      (Transition L K s t).2.phase.val = 3 ∧
      (Transition L K s t).1.role = .clock ∧
      (Transition L K s t).2.role = .clock ∧
      (Transition L K s t).1.minute = (Transition L K s t).2.minute ∧
      ¬ (Transition L K s t).1.minute.val < K * (L + 1) ∧
      (Transition L K s t).1.counter.val +
          (Transition L K s t).2.counter.val <
        s.counter.val + t.counter.val := by
  have hs_phase_eq : s.phase = ⟨3, by decide⟩ := Fin.ext hs_phase
  have ht_phase_eq : t.phase = ⟨3, by decide⟩ := Fin.ext ht_phase
  have hepidemic := phaseEpidemicUpdate_eq_self_of_phase
    (L := L) (K := K) ⟨3, by decide⟩ (by decide) s t hs_phase_eq ht_phase_eq
  have hminute_done_t : ¬ t.minute.val < K * (L + 1) := by
    simpa [hminute] using hminute_done
  unfold Transition
  rw [hepidemic]
  unfold Phase3Transition stdCounterSubroutine advancePhaseWithInit advancePhase phaseInit
  simp [hs_phase_eq, ht_phase_eq, hs_clock, ht_clock, hminute,
    hminute_done_t, hs_pos.ne', ht_pos.ne']
  omega

/-- Phase-3 progress once the two selected clocks are already synchronized at
the Phase-3 minute threshold.  This closes the counter part of the Phase-3
clock argument; the earlier minute-synchronization/drip schedule is a separate
obligation. -/
theorem phase3_done_counter_progress_of_applicable_two_clocks
    (c : Config (AgentState L K)) (s t : AgentState L K)
    (happ : Protocol.Applicable c s t)
    (hs_phase : s.phase.val = 3) (ht_phase : t.phase.val = 3)
    (hs_clock : s.role = .clock) (ht_clock : t.role = .clock)
    (hminute : s.minute = t.minute)
    (hminute_done : ¬ s.minute.val < K * (L + 1)) :
    ∃ final, (NonuniformMajority L K).Reachable c final ∧
      ∃ a ∈ final, 4 ≤ a.phase.val := by
  classical
  let total := s.counter.val + t.counter.val
  have aux :
      ∀ n, ∀ c : Config (AgentState L K), ∀ s t : AgentState L K,
        s.counter.val + t.counter.val = n →
        Protocol.Applicable c s t →
        s.phase.val = 3 → t.phase.val = 3 →
        s.role = .clock → t.role = .clock →
        s.minute = t.minute →
        ¬ s.minute.val < K * (L + 1) →
        ∃ final, (NonuniformMajority L K).Reachable c final ∧
          ∃ a ∈ final, 4 ≤ a.phase.val := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro c s t hn happ hs_phase ht_phase hs_clock ht_clock hminute hminute_done
      rcases Nat.eq_zero_or_pos s.counter.val with hs_zero | hs_pos
      · let final := Protocol.stepOrSelf (NonuniformMajority L K) c s t
        refine ⟨final, Protocol.reachable_stepOrSelf c s t, ?_⟩
        have hstep :
            final =
              c - ({s, t} : Multiset (AgentState L K)) +
                ({(Transition L K s t).1, (Transition L K s t).2} :
                  Multiset (AgentState L K)) := by
          unfold final Protocol.stepOrSelf
          rw [if_pos happ]
          rfl
        have hadvance := Transition_phase3_clock_done_counter_zero_advances
          (L := L) (K := K) s t hs_phase ht_phase hs_clock ht_clock
          hminute hminute_done (Or.inl hs_zero)
        rcases hadvance with hleft | hright
        · refine ⟨(Transition L K s t).1, ?_, hleft⟩
          rw [hstep]
          simp
        · refine ⟨(Transition L K s t).2, ?_, hright⟩
          rw [hstep]
          simp
      · rcases Nat.eq_zero_or_pos t.counter.val with ht_zero | ht_pos
        · let final := Protocol.stepOrSelf (NonuniformMajority L K) c s t
          refine ⟨final, Protocol.reachable_stepOrSelf c s t, ?_⟩
          have hstep :
              final =
                c - ({s, t} : Multiset (AgentState L K)) +
                  ({(Transition L K s t).1, (Transition L K s t).2} :
                    Multiset (AgentState L K)) := by
            unfold final Protocol.stepOrSelf
            rw [if_pos happ]
            rfl
          have hadvance := Transition_phase3_clock_done_counter_zero_advances
            (L := L) (K := K) s t hs_phase ht_phase hs_clock ht_clock
            hminute hminute_done (Or.inr ht_zero)
          rcases hadvance with hleft | hright
          · refine ⟨(Transition L K s t).1, ?_, hleft⟩
            rw [hstep]
            simp
          · refine ⟨(Transition L K s t).2, ?_, hright⟩
            rw [hstep]
            simp
        · let c₁ := Protocol.stepOrSelf (NonuniformMajority L K) c s t
          let s₁ := (Transition L K s t).1
          let t₁ := (Transition L K s t).2
          have hstep :
              c₁ =
                c - ({s, t} : Multiset (AgentState L K)) +
                  ({s₁, t₁} : Multiset (AgentState L K)) := by
            unfold c₁ s₁ t₁ Protocol.stepOrSelf
            rw [if_pos happ]
            rfl
          have hnext := Transition_phase3_clock_done_positive_preserves_and_decreases
            (L := L) (K := K) s t hs_phase ht_phase hs_clock ht_clock
            hminute hminute_done hs_pos ht_pos
          have hs₁_phase : s₁.phase.val = 3 := by
            unfold s₁
            exact hnext.1
          have ht₁_phase : t₁.phase.val = 3 := by
            unfold t₁
            exact hnext.2.1
          have hs₁_clock : s₁.role = .clock := by
            unfold s₁
            exact hnext.2.2.1
          have ht₁_clock : t₁.role = .clock := by
            unfold t₁
            exact hnext.2.2.2.1
          have hminute₁ : s₁.minute = t₁.minute := by
            unfold s₁ t₁
            exact hnext.2.2.2.2.1
          have hminute_done₁ : ¬ s₁.minute.val < K * (L + 1) := by
            unfold s₁
            exact hnext.2.2.2.2.2.1
          have hsum_lt : s₁.counter.val + t₁.counter.val < n := by
            unfold s₁ t₁
            rw [← hn]
            exact hnext.2.2.2.2.2.2
          have happ₁ : Protocol.Applicable c₁ s₁ t₁ := by
            dsimp [Protocol.Applicable]
            rw [hstep]
            exact Multiset.le_add_left ({s₁, t₁} : Multiset (AgentState L K))
              (c - ({s, t} : Multiset (AgentState L K)))
          rcases ih (s₁.counter.val + t₁.counter.val) hsum_lt
              c₁ s₁ t₁ rfl happ₁ hs₁_phase ht₁_phase hs₁_clock ht₁_clock
              hminute₁ hminute_done₁ with
            ⟨final, hreach₂, hwitness⟩
          refine ⟨final, ?_, hwitness⟩
          exact Relation.ReflTransGen.trans
            (Protocol.reachable_stepOrSelf c s t) hreach₂
  exact aux total c s t rfl happ hs_phase ht_phase hs_clock ht_clock hminute hminute_done

/-- Phase 6 can change a Reserve into a Main during a split.  This records why
the blanket statement "all phases after Phase 0 preserve every role" is false;
the useful preservation property for the clock-progress argument must be
restricted to clocks, or to phases/rules that do not split reserves. -/
theorem Phase6Transition_can_change_reserve_role
    (r m : AgentState L K) (sgn : Sign) (j : Fin (L + 1))
    (hr : r.role = .reserve) (hm : m.role = .main)
    (hbias : m.bias = .dyadic sgn j)
    (hguard : r.hour.val ≠ L ∧ r.hour.val > j.val)
    (hj : j.val < L) :
    (Phase6Transition L K r m).1.role = .main := by
  unfold Phase6Transition doSplit
  simp [hr, hm, hbias, hguard, hj]

private def phase3MinutePotential (s t : AgentState L K) : ℕ :=
  2 * (K * (L + 1) - max s.minute.val t.minute.val) +
    if s.minute = t.minute then 0 else 1

/-- Phase-3 unequal-minute clock step: the selected clocks synchronize upward
to the larger minute, stay clocks in Phase 3, and strictly decrease the
minute potential. -/
theorem Transition_phase3_clock_minute_sync_decreases
    (s t : AgentState L K)
    (hs_phase : s.phase.val = 3) (ht_phase : t.phase.val = 3)
    (hs_clock : s.role = .clock) (ht_clock : t.role = .clock)
    (hne : s.minute ≠ t.minute) :
    (Transition L K s t).1.phase.val = 3 ∧
      (Transition L K s t).2.phase.val = 3 ∧
      (Transition L K s t).1.role = .clock ∧
      (Transition L K s t).2.role = .clock ∧
      (Transition L K s t).1.minute = max s.minute t.minute ∧
      (Transition L K s t).2.minute = max s.minute t.minute ∧
      phase3MinutePotential (L := L) (K := K)
          (Transition L K s t).1 (Transition L K s t).2 <
        phase3MinutePotential (L := L) (K := K) s t := by
  have hs_phase_eq : s.phase = ⟨3, by decide⟩ := Fin.ext hs_phase
  have ht_phase_eq : t.phase = ⟨3, by decide⟩ := Fin.ext ht_phase
  have hepidemic := phaseEpidemicUpdate_eq_self_of_phase
    (L := L) (K := K) ⟨3, by decide⟩ (by decide) s t hs_phase_eq ht_phase_eq
  unfold Transition
  rw [hepidemic]
  unfold Phase3Transition phase3MinutePotential
  simp [hs_phase_eq, ht_phase_eq, hs_clock, ht_clock, hne]

/-- Phase-3 equal-minute drip step: below the threshold the first selected
clock increments its minute, the second remains at the old minute, and the
minute potential strictly decreases. -/
theorem Transition_phase3_clock_minute_drip_decreases
    (s t : AgentState L K)
    (hs_phase : s.phase.val = 3) (ht_phase : t.phase.val = 3)
    (hs_clock : s.role = .clock) (ht_clock : t.role = .clock)
    (hminute : s.minute = t.minute)
    (hlt : s.minute.val < K * (L + 1)) :
    (Transition L K s t).1.phase.val = 3 ∧
      (Transition L K s t).2.phase.val = 3 ∧
      (Transition L K s t).1.role = .clock ∧
      (Transition L K s t).2.role = .clock ∧
      (Transition L K s t).1.minute.val = s.minute.val + 1 ∧
      (Transition L K s t).2.minute = t.minute ∧
      phase3MinutePotential (L := L) (K := K)
          (Transition L K s t).1 (Transition L K s t).2 <
        phase3MinutePotential (L := L) (K := K) s t := by
  have hs_phase_eq : s.phase = ⟨3, by decide⟩ := Fin.ext hs_phase
  have ht_phase_eq : t.phase = ⟨3, by decide⟩ := Fin.ext ht_phase
  have hepidemic := phaseEpidemicUpdate_eq_self_of_phase
    (L := L) (K := K) ⟨3, by decide⟩ (by decide) s t hs_phase_eq ht_phase_eq
  have hlt_t : t.minute.val < K * (L + 1) := by
    simpa [hminute] using hlt
  have hnew_ne_t :
      (⟨t.minute.val + 1, by omega⟩ : Fin (K * (L + 1) + 1)) ≠ t.minute := by
    intro h
    have := congrArg Fin.val h
    simp at this
  unfold Transition
  rw [hepidemic]
  unfold Phase3Transition phase3MinutePotential
  simp [hs_phase_eq, ht_phase_eq, hs_clock, ht_clock, hminute, hlt_t, hnew_ne_t]
  omega

/-- Repeated Phase-3 clock-clock interactions drive a fixed applicable clock
pair to the synchronized threshold-minute state.  This is the minute part of
the Phase-3 progress argument; the counter part is
`phase3_done_counter_progress_of_applicable_two_clocks`. -/
theorem phase3_minute_sync_of_applicable_two_clocks
    (c : Config (AgentState L K)) (s t : AgentState L K)
    (happ : Protocol.Applicable c s t)
    (hs_phase : s.phase.val = 3) (ht_phase : t.phase.val = 3)
    (hs_clock : s.role = .clock) (ht_clock : t.role = .clock) :
    ∃ c' s' t',
      (NonuniformMajority L K).Reachable c c' ∧
      Protocol.Applicable c' s' t' ∧
      s'.phase.val = 3 ∧ t'.phase.val = 3 ∧
      s'.role = .clock ∧ t'.role = .clock ∧
      s'.minute = t'.minute ∧
      ¬ s'.minute.val < K * (L + 1) := by
  classical
  let μ := phase3MinutePotential (L := L) (K := K) s t
  have aux :
      ∀ n, ∀ c : Config (AgentState L K), ∀ s t : AgentState L K,
        phase3MinutePotential (L := L) (K := K) s t = n →
        Protocol.Applicable c s t →
        s.phase.val = 3 → t.phase.val = 3 →
        s.role = .clock → t.role = .clock →
        ∃ c' s' t',
          (NonuniformMajority L K).Reachable c c' ∧
          Protocol.Applicable c' s' t' ∧
          s'.phase.val = 3 ∧ t'.phase.val = 3 ∧
          s'.role = .clock ∧ t'.role = .clock ∧
          s'.minute = t'.minute ∧
          ¬ s'.minute.val < K * (L + 1) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro c s t hn happ hs_phase ht_phase hs_clock ht_clock
      by_cases hminute : s.minute = t.minute
      · by_cases hdone : s.minute.val < K * (L + 1)
        · let c₁ := Protocol.stepOrSelf (NonuniformMajority L K) c s t
          let s₁ := (Transition L K s t).1
          let t₁ := (Transition L K s t).2
          have hstep :
              c₁ =
                c - ({s, t} : Multiset (AgentState L K)) +
                  ({s₁, t₁} : Multiset (AgentState L K)) := by
            unfold c₁ s₁ t₁ Protocol.stepOrSelf
            rw [if_pos happ]
            rfl
          have hnext := Transition_phase3_clock_minute_drip_decreases
            (L := L) (K := K) s t hs_phase ht_phase hs_clock ht_clock hminute hdone
          have hμ_lt : phase3MinutePotential (L := L) (K := K) s₁ t₁ < n := by
            unfold s₁ t₁
            rw [← hn]
            exact hnext.2.2.2.2.2.2
          have happ₁ : Protocol.Applicable c₁ s₁ t₁ := by
            dsimp [Protocol.Applicable]
            rw [hstep]
            exact Multiset.le_add_left ({s₁, t₁} : Multiset (AgentState L K))
              (c - ({s, t} : Multiset (AgentState L K)))
          rcases ih (phase3MinutePotential (L := L) (K := K) s₁ t₁) hμ_lt
              c₁ s₁ t₁ rfl happ₁
              (by unfold s₁; exact hnext.1)
              (by unfold t₁; exact hnext.2.1)
              (by unfold s₁; exact hnext.2.2.1)
              (by unfold t₁; exact hnext.2.2.2.1) with
            ⟨c', s', t', hreach₂, hrest⟩
          refine ⟨c', s', t', ?_, hrest⟩
          exact Relation.ReflTransGen.trans
            (Protocol.reachable_stepOrSelf c s t) hreach₂
        · exact ⟨c, s, t, Relation.ReflTransGen.refl, happ, hs_phase, ht_phase,
            hs_clock, ht_clock, hminute, hdone⟩
      · let c₁ := Protocol.stepOrSelf (NonuniformMajority L K) c s t
        let s₁ := (Transition L K s t).1
        let t₁ := (Transition L K s t).2
        have hstep :
            c₁ =
              c - ({s, t} : Multiset (AgentState L K)) +
                ({s₁, t₁} : Multiset (AgentState L K)) := by
          unfold c₁ s₁ t₁ Protocol.stepOrSelf
          rw [if_pos happ]
          rfl
        have hnext := Transition_phase3_clock_minute_sync_decreases
          (L := L) (K := K) s t hs_phase ht_phase hs_clock ht_clock hminute
        have hμ_lt : phase3MinutePotential (L := L) (K := K) s₁ t₁ < n := by
          unfold s₁ t₁
          rw [← hn]
          exact hnext.2.2.2.2.2.2
        have happ₁ : Protocol.Applicable c₁ s₁ t₁ := by
          dsimp [Protocol.Applicable]
          rw [hstep]
          exact Multiset.le_add_left ({s₁, t₁} : Multiset (AgentState L K))
            (c - ({s, t} : Multiset (AgentState L K)))
        rcases ih (phase3MinutePotential (L := L) (K := K) s₁ t₁) hμ_lt
            c₁ s₁ t₁ rfl happ₁
            (by unfold s₁; exact hnext.1)
            (by unfold t₁; exact hnext.2.1)
            (by unfold s₁; exact hnext.2.2.1)
            (by unfold t₁; exact hnext.2.2.2.1) with
          ⟨c', s', t', hreach₂, hrest⟩
        refine ⟨c', s', t', ?_, hrest⟩
        exact Relation.ReflTransGen.trans
          (Protocol.reachable_stepOrSelf c s t) hreach₂
  exact aux μ c s t rfl happ hs_phase ht_phase hs_clock ht_clock

/-- Full Phase-3 clock progress for a concrete applicable clock pair: first
synchronize/drip minutes to the threshold, then use the already-proved counter
descent to enter Phase 4. -/
theorem phase3_progress_of_applicable_two_clocks
    (c : Config (AgentState L K)) (s t : AgentState L K)
    (happ : Protocol.Applicable c s t)
    (hs_phase : s.phase.val = 3) (ht_phase : t.phase.val = 3)
    (hs_clock : s.role = .clock) (ht_clock : t.role = .clock) :
    ∃ final, (NonuniformMajority L K).Reachable c final ∧
      ∃ a ∈ final, 4 ≤ a.phase.val := by
  rcases phase3_minute_sync_of_applicable_two_clocks
      (L := L) (K := K) c s t happ hs_phase ht_phase hs_clock ht_clock with
    ⟨c', s', t', hreach₁, happ', hs_phase', ht_phase',
      hs_clock', ht_clock', hminute', hdone'⟩
  rcases phase3_done_counter_progress_of_applicable_two_clocks
      (L := L) (K := K) c' s' t' happ' hs_phase' ht_phase'
      hs_clock' ht_clock' hminute' hdone' with
    ⟨final, hreach₂, hwitness⟩
  exact ⟨final, Relation.ReflTransGen.trans hreach₁ hreach₂, hwitness⟩

private lemma phase3_pair_le_of_mem_ne
    {α : Type*} {c : Multiset α} {s t : α}
    (hs : s ∈ c) (ht : t ∈ c) (hne : s ≠ t) :
    ({s, t} : Multiset α) ≤ c := by
  classical
  rw [Multiset.le_iff_count]
  intro x
  by_cases hxs : x = s
  · subst x
    have hs_pos : 0 < Multiset.count s c := (Multiset.count_pos).2 hs
    have ht_ne : s ≠ t := hne
    simp [ht_ne, Nat.succ_le_iff, hs_pos]
  · by_cases hxt : x = t
    · subst x
      have ht_pos : 0 < Multiset.count t c := (Multiset.count_pos).2 ht
      simp [hxs, Nat.succ_le_iff, ht_pos]
    · simp [hxs, hxt]

/-- Phase-3 progress from any configuration with two distinct clock states. -/
theorem phase3_progress_of_two_clocks
    (c : Config (AgentState L K))
    (hphase3 : ∀ a ∈ c, a.phase.val = 3)
    (hclocks :
      ∃ i j, i ∈ c ∧ j ∈ c ∧ i ≠ j ∧ i.role = .clock ∧ j.role = .clock) :
    ∃ final, (NonuniformMajority L K).Reachable c final ∧
      ∃ a ∈ final, 4 ≤ a.phase.val := by
  rcases hclocks with ⟨i, j, hi, hj, hij, hi_clock, hj_clock⟩
  have happ : Protocol.Applicable c i j :=
    phase3_pair_le_of_mem_ne hi hj hij
  exact phase3_progress_of_applicable_two_clocks
    (L := L) (K := K) c i j happ
    (hphase3 i hi) (hphase3 j hj) hi_clock hj_clock

/-- Phase 5 clock-clock interactions use the shared standard counter subroutine,
so their combined counter value cannot increase. -/
theorem Phase5Transition_clock_counter_descent
    (s t : AgentState L K) (hs : s.role = .clock) (ht : t.role = .clock)
    (hs_pos : 0 < s.counter.val) (ht_pos : 0 < t.counter.val) :
    (Phase5Transition L K s t).1.counter.val +
        (Phase5Transition L K s t).2.counter.val ≤
      s.counter.val + t.counter.val := by
  unfold Phase5Transition
  simp [hs, ht,
    stdCounterSubroutine_counter_descent (L := L) (K := K) s t hs ht hs_pos ht_pos]

/-- Phase 5 clock-clock interactions strictly decrease the combined counter
value whenever at least one counter is positive. -/
theorem Phase5Transition_clock_counter_strict_descent
    (s t : AgentState L K) (hs : s.role = .clock) (ht : t.role = .clock)
    (hs_pos : 0 < s.counter.val) (ht_pos : 0 < t.counter.val) :
    (Phase5Transition L K s t).1.counter.val +
        (Phase5Transition L K s t).2.counter.val <
      s.counter.val + t.counter.val := by
  unfold Phase5Transition
  simp [hs, ht,
    stdCounterSubroutine_counter_strict_descent (L := L) (K := K) s t hs ht hs_pos ht_pos]

/-- Local Phase-6 clock progress: once two Phase-6 clocks with zero counters
interact, both advance to Phase 7. -/
theorem Phase6Transition_clock_zero_advances
    (s t : AgentState L K)
    (hs_phase : s.phase.val = 6) (ht_phase : t.phase.val = 6)
    (hs_clock : s.role = .clock) (ht_clock : t.role = .clock)
    (hs_counter : s.counter.val = 0) (ht_counter : t.counter.val = 0) :
    (Phase6Transition L K s t).1.phase.val = 7 ∧
      (Phase6Transition L K s t).2.phase.val = 7 := by
  unfold Phase6Transition stdCounterSubroutine advancePhaseWithInit advancePhase phaseInit
  simp [hs_clock, ht_clock, hs_counter, ht_counter, hs_phase, ht_phase]

/-- Phase 6 clock-clock interactions use the shared standard counter subroutine,
so their combined counter value cannot increase. -/
theorem Phase6Transition_clock_counter_descent
    (s t : AgentState L K) (hs : s.role = .clock) (ht : t.role = .clock)
    (hs_pos : 0 < s.counter.val) (ht_pos : 0 < t.counter.val) :
    (Phase6Transition L K s t).1.counter.val +
        (Phase6Transition L K s t).2.counter.val ≤
      s.counter.val + t.counter.val := by
  unfold Phase6Transition
  simp [hs, ht,
    stdCounterSubroutine_counter_descent (L := L) (K := K) s t hs ht hs_pos ht_pos]

/-- Phase 6 clock-clock interactions strictly decrease the combined counter
value whenever at least one counter is positive. -/
theorem Phase6Transition_clock_counter_strict_descent
    (s t : AgentState L K) (hs : s.role = .clock) (ht : t.role = .clock)
    (hs_pos : 0 < s.counter.val) (ht_pos : 0 < t.counter.val) :
    (Phase6Transition L K s t).1.counter.val +
        (Phase6Transition L K s t).2.counter.val <
      s.counter.val + t.counter.val := by
  unfold Phase6Transition
  simp [hs, ht,
    stdCounterSubroutine_counter_strict_descent (L := L) (K := K) s t hs ht hs_pos ht_pos]

/-- Local Phase-7 clock progress: once two Phase-7 clocks with zero counters
interact, both advance to Phase 8. -/
theorem Phase7Transition_clock_zero_advances
    (s t : AgentState L K)
    (hs_phase : s.phase.val = 7) (ht_phase : t.phase.val = 7)
    (hs_clock : s.role = .clock) (ht_clock : t.role = .clock)
    (hs_counter : s.counter.val = 0) (ht_counter : t.counter.val = 0) :
    (Phase7Transition L K s t).1.phase.val = 8 ∧
      (Phase7Transition L K s t).2.phase.val = 8 := by
  unfold Phase7Transition stdCounterSubroutine advancePhaseWithInit advancePhase phaseInit
  simp [hs_clock, ht_clock, hs_counter, ht_counter, hs_phase, ht_phase]

/-- Phase 7 clock-clock interactions use the shared standard counter subroutine,
so their combined counter value cannot increase. -/
theorem Phase7Transition_clock_counter_descent
    (s t : AgentState L K) (hs : s.role = .clock) (ht : t.role = .clock)
    (hs_pos : 0 < s.counter.val) (ht_pos : 0 < t.counter.val) :
    (Phase7Transition L K s t).1.counter.val +
        (Phase7Transition L K s t).2.counter.val ≤
      s.counter.val + t.counter.val := by
  unfold Phase7Transition
  simp [hs, ht,
    stdCounterSubroutine_counter_descent (L := L) (K := K) s t hs ht hs_pos ht_pos]

/-- Phase 7 clock-clock interactions strictly decrease the combined counter
value whenever at least one counter is positive. -/
theorem Phase7Transition_clock_counter_strict_descent
    (s t : AgentState L K) (hs : s.role = .clock) (ht : t.role = .clock)
    (hs_pos : 0 < s.counter.val) (ht_pos : 0 < t.counter.val) :
    (Phase7Transition L K s t).1.counter.val +
        (Phase7Transition L K s t).2.counter.val <
      s.counter.val + t.counter.val := by
  unfold Phase7Transition
  simp [hs, ht,
    stdCounterSubroutine_counter_strict_descent (L := L) (K := K) s t hs ht hs_pos ht_pos]

/-- Local Phase-8 clock progress: once two Phase-8 clocks with zero counters
interact, both advance to Phase 9. -/
theorem Phase8Transition_clock_zero_advances
    (s t : AgentState L K)
    (hs_phase : s.phase.val = 8) (ht_phase : t.phase.val = 8)
    (hs_clock : s.role = .clock) (ht_clock : t.role = .clock)
    (hs_counter : s.counter.val = 0) (ht_counter : t.counter.val = 0) :
    9 ≤ (Phase8Transition L K s t).1.phase.val ∧
      9 ≤ (Phase8Transition L K s t).2.phase.val := by
  unfold Phase8Transition stdCounterSubroutine advancePhaseWithInit advancePhase phaseInit
  simp [hs_clock, ht_clock, hs_counter, ht_counter, hs_phase, ht_phase, enterPhase10, phase10] <;>
    repeat' split_ifs <;> simp [enterPhase10, phase10] <;>
    omega

/-- Phase 8 clock-clock interactions use the shared standard counter subroutine,
so their combined counter value cannot increase. -/
theorem Phase8Transition_clock_counter_descent
    (s t : AgentState L K) (hs : s.role = .clock) (ht : t.role = .clock)
    (hs_pos : 0 < s.counter.val) (ht_pos : 0 < t.counter.val) :
    (Phase8Transition L K s t).1.counter.val +
        (Phase8Transition L K s t).2.counter.val ≤
      s.counter.val + t.counter.val := by
  unfold Phase8Transition
  simp [hs, ht,
    stdCounterSubroutine_counter_descent (L := L) (K := K) s t hs ht hs_pos ht_pos]

/-- Phase 8 clock-clock interactions strictly decrease the combined counter
value whenever at least one counter is positive. -/
theorem Phase8Transition_clock_counter_strict_descent
    (s t : AgentState L K) (hs : s.role = .clock) (ht : t.role = .clock)
    (hs_pos : 0 < s.counter.val) (ht_pos : 0 < t.counter.val) :
    (Phase8Transition L K s t).1.counter.val +
        (Phase8Transition L K s t).2.counter.val <
      s.counter.val + t.counter.val := by
  unfold Phase8Transition
  simp [hs, ht,
    stdCounterSubroutine_counter_strict_descent (L := L) (K := K) s t hs ht hs_pos ht_pos]

private theorem timedPhase_cases {p : ℕ}
    (hp : p ∈ ({0, 1, 5, 6, 7, 8} : Finset ℕ)) :
    p = 0 ∨ p = 1 ∨ p = 5 ∨ p = 6 ∨ p = 7 ∨ p = 8 := by
  simpa using hp

/-- In the standard timed phases, if two clock agents interact while at least
one selected clock counter is zero, the dispatcher output already contains an
agent in the next phase. -/
theorem Transition_timed_clock_counter_zero_advances
    (p : ℕ) (hp : p ∈ ({0, 1, 5, 6, 7, 8} : Finset ℕ))
    (s t : AgentState L K)
    (hs_phase : s.phase.val = p) (ht_phase : t.phase.val = p)
    (hs_clock : s.role = .clock) (ht_clock : t.role = .clock)
    (hzero : s.counter.val = 0 ∨ t.counter.val = 0) :
    p + 1 ≤ (Transition L K s t).1.phase.val ∨
      p + 1 ≤ (Transition L K s t).2.phase.val := by
  rcases timedPhase_cases hp with rfl | rfl | rfl | rfl | rfl | rfl
  · have hs_phase_eq : s.phase = ⟨0, by decide⟩ := Fin.ext hs_phase
    have ht_phase_eq : t.phase = ⟨0, by decide⟩ := Fin.ext ht_phase
    have hepidemic := phaseEpidemicUpdate_eq_self_of_phase
      (L := L) (K := K) ⟨0, by decide⟩ (by decide) s t hs_phase_eq ht_phase_eq
    rcases hzero with hs_zero | ht_zero
    · left
      unfold Transition
      rw [hepidemic]
      unfold Phase0Transition stdCounterSubroutine advancePhaseWithInit advancePhase phaseInit
      simp [hs_clock, ht_clock, hs_zero, hs_phase_eq, ht_phase_eq]
    · right
      unfold Transition
      rw [hepidemic]
      unfold Phase0Transition stdCounterSubroutine advancePhaseWithInit advancePhase phaseInit
      simp [hs_clock, ht_clock, ht_zero, hs_phase_eq, ht_phase_eq]
  · have hs_phase_eq : s.phase = ⟨1, by decide⟩ := Fin.ext hs_phase
    have ht_phase_eq : t.phase = ⟨1, by decide⟩ := Fin.ext ht_phase
    have hepidemic := phaseEpidemicUpdate_eq_self_of_phase
      (L := L) (K := K) ⟨1, by decide⟩ (by decide) s t hs_phase_eq ht_phase_eq
    rcases hzero with hs_zero | ht_zero
    · left
      unfold Transition
      rw [hepidemic]
      unfold Phase1Transition clockCounterStep stdCounterSubroutine advancePhaseWithInit advancePhase phaseInit
      simp [hs_clock, ht_clock, hs_zero, hs_phase_eq, ht_phase_eq, enterPhase10, phase10] <;>
        repeat' split_ifs <;> simp [enterPhase10, phase10] <;>
        omega
    · right
      unfold Transition
      rw [hepidemic]
      unfold Phase1Transition clockCounterStep stdCounterSubroutine advancePhaseWithInit advancePhase phaseInit
      simp [hs_clock, ht_clock, ht_zero, hs_phase_eq, ht_phase_eq, enterPhase10, phase10] <;>
        repeat' split_ifs <;> simp [enterPhase10, phase10] <;>
        omega
  · have hs_phase_eq : s.phase = ⟨5, by decide⟩ := Fin.ext hs_phase
    have ht_phase_eq : t.phase = ⟨5, by decide⟩ := Fin.ext ht_phase
    have hepidemic := phaseEpidemicUpdate_eq_self_of_phase
      (L := L) (K := K) ⟨5, by decide⟩ (by decide) s t hs_phase_eq ht_phase_eq
    rcases hzero with hs_zero | ht_zero
    · left
      unfold Transition
      rw [hepidemic]
      unfold Phase5Transition stdCounterSubroutine advancePhaseWithInit advancePhase phaseInit
      simp [hs_clock, ht_clock, hs_zero, hs_phase_eq, ht_phase_eq]
    · right
      unfold Transition
      rw [hepidemic]
      unfold Phase5Transition stdCounterSubroutine advancePhaseWithInit advancePhase phaseInit
      simp [hs_clock, ht_clock, ht_zero, hs_phase_eq, ht_phase_eq]
  · have hs_phase_eq : s.phase = ⟨6, by decide⟩ := Fin.ext hs_phase
    have ht_phase_eq : t.phase = ⟨6, by decide⟩ := Fin.ext ht_phase
    have hepidemic := phaseEpidemicUpdate_eq_self_of_phase
      (L := L) (K := K) ⟨6, by decide⟩ (by decide) s t hs_phase_eq ht_phase_eq
    rcases hzero with hs_zero | ht_zero
    · left
      unfold Transition
      rw [hepidemic]
      unfold Phase6Transition stdCounterSubroutine advancePhaseWithInit advancePhase phaseInit
      simp [hs_clock, ht_clock, hs_zero, hs_phase_eq, ht_phase_eq]
    · right
      unfold Transition
      rw [hepidemic]
      unfold Phase6Transition stdCounterSubroutine advancePhaseWithInit advancePhase phaseInit
      simp [hs_clock, ht_clock, ht_zero, hs_phase_eq, ht_phase_eq]
  · have hs_phase_eq : s.phase = ⟨7, by decide⟩ := Fin.ext hs_phase
    have ht_phase_eq : t.phase = ⟨7, by decide⟩ := Fin.ext ht_phase
    have hepidemic := phaseEpidemicUpdate_eq_self_of_phase
      (L := L) (K := K) ⟨7, by decide⟩ (by decide) s t hs_phase_eq ht_phase_eq
    rcases hzero with hs_zero | ht_zero
    · left
      unfold Transition
      rw [hepidemic]
      unfold Phase7Transition stdCounterSubroutine advancePhaseWithInit advancePhase phaseInit
      simp [hs_clock, ht_clock, hs_zero, hs_phase_eq, ht_phase_eq]
    · right
      unfold Transition
      rw [hepidemic]
      unfold Phase7Transition stdCounterSubroutine advancePhaseWithInit advancePhase phaseInit
      simp [hs_clock, ht_clock, ht_zero, hs_phase_eq, ht_phase_eq]
  · have hs_phase_eq : s.phase = ⟨8, by decide⟩ := Fin.ext hs_phase
    have ht_phase_eq : t.phase = ⟨8, by decide⟩ := Fin.ext ht_phase
    have hepidemic := phaseEpidemicUpdate_eq_self_of_phase
      (L := L) (K := K) ⟨8, by decide⟩ (by decide) s t hs_phase_eq ht_phase_eq
    rcases hzero with hs_zero | ht_zero
    · left
      unfold Transition
      rw [hepidemic]
      unfold Phase8Transition stdCounterSubroutine advancePhaseWithInit advancePhase phaseInit
      simp [hs_clock, ht_clock, hs_zero, hs_phase_eq, ht_phase_eq, enterPhase10, phase10] <;>
        repeat' split_ifs <;> simp [enterPhase10, phase10] <;>
        omega
    · right
      unfold Transition
      rw [hepidemic]
      unfold Phase8Transition stdCounterSubroutine advancePhaseWithInit advancePhase phaseInit
      simp [hs_clock, ht_clock, ht_zero, hs_phase_eq, ht_phase_eq, enterPhase10, phase10] <;>
        repeat' split_ifs <;> simp [enterPhase10, phase10] <;>
        omega

/-- In the standard timed phases, if both selected clock counters are positive,
one clock-clock dispatcher step keeps the selected agents as clocks in the same
phase and strictly decreases their combined counter value. -/
theorem Transition_timed_clock_positive_preserves_and_decreases
    (p : ℕ) (hp : p ∈ ({0, 1, 5, 6, 7, 8} : Finset ℕ))
    (s t : AgentState L K)
    (hs_phase : s.phase.val = p) (ht_phase : t.phase.val = p)
    (hs_clock : s.role = .clock) (ht_clock : t.role = .clock)
    (hs_pos : 0 < s.counter.val) (ht_pos : 0 < t.counter.val) :
    (Transition L K s t).1.phase.val = p ∧
      (Transition L K s t).2.phase.val = p ∧
      (Transition L K s t).1.role = .clock ∧
      (Transition L K s t).2.role = .clock ∧
      (Transition L K s t).1.counter.val +
          (Transition L K s t).2.counter.val <
        s.counter.val + t.counter.val := by
  rcases timedPhase_cases hp with rfl | rfl | rfl | rfl | rfl | rfl
  · have hs_phase_eq : s.phase = ⟨0, by decide⟩ := Fin.ext hs_phase
    have ht_phase_eq : t.phase = ⟨0, by decide⟩ := Fin.ext ht_phase
    have hepidemic := phaseEpidemicUpdate_eq_self_of_phase
      (L := L) (K := K) ⟨0, by decide⟩ (by decide) s t hs_phase_eq ht_phase_eq
    unfold Transition
    rw [hepidemic]
    unfold Phase0Transition stdCounterSubroutine advancePhaseWithInit advancePhase phaseInit
    simp [hs_phase_eq, ht_phase_eq, hs_clock, ht_clock, hs_pos.ne', ht_pos.ne']
    omega
  · have hs_phase_eq : s.phase = ⟨1, by decide⟩ := Fin.ext hs_phase
    have ht_phase_eq : t.phase = ⟨1, by decide⟩ := Fin.ext ht_phase
    have hepidemic := phaseEpidemicUpdate_eq_self_of_phase
      (L := L) (K := K) ⟨1, by decide⟩ (by decide) s t hs_phase_eq ht_phase_eq
    unfold Transition
    rw [hepidemic]
    unfold Phase1Transition clockCounterStep stdCounterSubroutine advancePhaseWithInit advancePhase phaseInit
    simp [hs_phase_eq, ht_phase_eq, hs_clock, ht_clock, hs_pos.ne', ht_pos.ne']
    omega
  · have hs_phase_eq : s.phase = ⟨5, by decide⟩ := Fin.ext hs_phase
    have ht_phase_eq : t.phase = ⟨5, by decide⟩ := Fin.ext ht_phase
    have hepidemic := phaseEpidemicUpdate_eq_self_of_phase
      (L := L) (K := K) ⟨5, by decide⟩ (by decide) s t hs_phase_eq ht_phase_eq
    unfold Transition
    rw [hepidemic]
    unfold Phase5Transition stdCounterSubroutine advancePhaseWithInit advancePhase phaseInit
    simp [hs_phase_eq, ht_phase_eq, hs_clock, ht_clock, hs_pos.ne', ht_pos.ne']
    omega
  · have hs_phase_eq : s.phase = ⟨6, by decide⟩ := Fin.ext hs_phase
    have ht_phase_eq : t.phase = ⟨6, by decide⟩ := Fin.ext ht_phase
    have hepidemic := phaseEpidemicUpdate_eq_self_of_phase
      (L := L) (K := K) ⟨6, by decide⟩ (by decide) s t hs_phase_eq ht_phase_eq
    unfold Transition
    rw [hepidemic]
    unfold Phase6Transition stdCounterSubroutine advancePhaseWithInit advancePhase phaseInit
    simp [hs_phase_eq, ht_phase_eq, hs_clock, ht_clock, hs_pos.ne', ht_pos.ne']
    omega
  · have hs_phase_eq : s.phase = ⟨7, by decide⟩ := Fin.ext hs_phase
    have ht_phase_eq : t.phase = ⟨7, by decide⟩ := Fin.ext ht_phase
    have hepidemic := phaseEpidemicUpdate_eq_self_of_phase
      (L := L) (K := K) ⟨7, by decide⟩ (by decide) s t hs_phase_eq ht_phase_eq
    unfold Transition
    rw [hepidemic]
    unfold Phase7Transition stdCounterSubroutine advancePhaseWithInit advancePhase phaseInit
    simp [hs_phase_eq, ht_phase_eq, hs_clock, ht_clock, hs_pos.ne', ht_pos.ne']
    omega
  · have hs_phase_eq : s.phase = ⟨8, by decide⟩ := Fin.ext hs_phase
    have ht_phase_eq : t.phase = ⟨8, by decide⟩ := Fin.ext ht_phase
    have hepidemic := phaseEpidemicUpdate_eq_self_of_phase
      (L := L) (K := K) ⟨8, by decide⟩ (by decide) s t hs_phase_eq ht_phase_eq
    unfold Transition
    rw [hepidemic]
    unfold Phase8Transition stdCounterSubroutine advancePhaseWithInit advancePhase phaseInit
    simp [hs_phase_eq, ht_phase_eq, hs_clock, ht_clock, hs_pos.ne', ht_pos.ne']
    omega

private lemma pair_le_of_mem_ne
    {α : Type*} {c : Multiset α} {s t : α}
    (hs : s ∈ c) (ht : t ∈ c) (hne : s ≠ t) :
    ({s, t} : Multiset α) ≤ c := by
  classical
  rw [Multiset.le_iff_count]
  intro x
  by_cases hxs : x = s
  · subst x
    have hs_pos : 0 < Multiset.count s c := (Multiset.count_pos).2 hs
    have ht_ne : s ≠ t := hne
    simp [ht_ne, Nat.succ_le_iff, hs_pos]
  · by_cases hxt : x = t
    · subst x
      have ht_pos : 0 < Multiset.count t c := (Multiset.count_pos).2 ht
      simp [hxs, Nat.succ_le_iff, ht_pos]
    · simp [hxs, hxt]

/-- Generic timed-phase progress for a concrete applicable clock-clock pair.
Repeatedly interacting the same two clock agents decreases their combined
counter while both counters are positive; once either counter is zero, the next
interaction contains an agent in the next phase. -/
theorem timed_phase_progress_of_applicable_two_clocks
    (c : Config (AgentState L K))
    (p : ℕ) (hp : p ∈ ({0, 1, 5, 6, 7, 8} : Finset ℕ))
    (s t : AgentState L K)
    (happ : Protocol.Applicable c s t)
    (hs_phase : s.phase.val = p) (ht_phase : t.phase.val = p)
    (hs_clock : s.role = .clock) (ht_clock : t.role = .clock) :
    ∃ final, (NonuniformMajority L K).Reachable c final ∧
      ∃ a ∈ final, p + 1 ≤ a.phase.val := by
  classical
  let total := s.counter.val + t.counter.val
  have aux :
      ∀ n, ∀ c : Config (AgentState L K), ∀ s t : AgentState L K,
        s.counter.val + t.counter.val = n →
        Protocol.Applicable c s t →
        s.phase.val = p → t.phase.val = p →
        s.role = .clock → t.role = .clock →
        ∃ final, (NonuniformMajority L K).Reachable c final ∧
          ∃ a ∈ final, p + 1 ≤ a.phase.val := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro c s t hn happ hs_phase ht_phase hs_clock ht_clock
      rcases Nat.eq_zero_or_pos s.counter.val with hs_zero | hs_pos
      · let final := Protocol.stepOrSelf (NonuniformMajority L K) c s t
        refine ⟨final, Protocol.reachable_stepOrSelf c s t, ?_⟩
        have hstep :
            final =
              c - ({s, t} : Multiset (AgentState L K)) +
                ({(Transition L K s t).1, (Transition L K s t).2} :
                  Multiset (AgentState L K)) := by
          unfold final Protocol.stepOrSelf
          rw [if_pos happ]
          rfl
        have hadvance := Transition_timed_clock_counter_zero_advances
          (L := L) (K := K) p hp s t hs_phase ht_phase hs_clock ht_clock
          (Or.inl hs_zero)
        rcases hadvance with hleft | hright
        · refine ⟨(Transition L K s t).1, ?_, hleft⟩
          rw [hstep]
          simp
        · refine ⟨(Transition L K s t).2, ?_, hright⟩
          rw [hstep]
          simp
      · rcases Nat.eq_zero_or_pos t.counter.val with ht_zero | ht_pos
        · let final := Protocol.stepOrSelf (NonuniformMajority L K) c s t
          refine ⟨final, Protocol.reachable_stepOrSelf c s t, ?_⟩
          have hstep :
              final =
                c - ({s, t} : Multiset (AgentState L K)) +
                  ({(Transition L K s t).1, (Transition L K s t).2} :
                    Multiset (AgentState L K)) := by
            unfold final Protocol.stepOrSelf
            rw [if_pos happ]
            rfl
          have hadvance := Transition_timed_clock_counter_zero_advances
            (L := L) (K := K) p hp s t hs_phase ht_phase hs_clock ht_clock
            (Or.inr ht_zero)
          rcases hadvance with hleft | hright
          · refine ⟨(Transition L K s t).1, ?_, hleft⟩
            rw [hstep]
            simp
          · refine ⟨(Transition L K s t).2, ?_, hright⟩
            rw [hstep]
            simp
        · let c₁ := Protocol.stepOrSelf (NonuniformMajority L K) c s t
          let s₁ := (Transition L K s t).1
          let t₁ := (Transition L K s t).2
          have hstep :
              c₁ =
                c - ({s, t} : Multiset (AgentState L K)) +
                  ({s₁, t₁} : Multiset (AgentState L K)) := by
            unfold c₁ s₁ t₁ Protocol.stepOrSelf
            rw [if_pos happ]
            rfl
          have hnext := Transition_timed_clock_positive_preserves_and_decreases
            (L := L) (K := K) p hp s t hs_phase ht_phase hs_clock ht_clock hs_pos ht_pos
          have hs₁_phase : s₁.phase.val = p := by
            unfold s₁
            exact hnext.1
          have ht₁_phase : t₁.phase.val = p := by
            unfold t₁
            exact hnext.2.1
          have hs₁_clock : s₁.role = .clock := by
            unfold s₁
            exact hnext.2.2.1
          have ht₁_clock : t₁.role = .clock := by
            unfold t₁
            exact hnext.2.2.2.1
          have hsum_lt : s₁.counter.val + t₁.counter.val < n := by
            unfold s₁ t₁
            rw [← hn]
            exact hnext.2.2.2.2
          have happ₁ : Protocol.Applicable c₁ s₁ t₁ := by
            dsimp [Protocol.Applicable]
            rw [hstep]
            exact Multiset.le_add_left ({s₁, t₁} : Multiset (AgentState L K))
              (c - ({s, t} : Multiset (AgentState L K)))
          rcases ih (s₁.counter.val + t₁.counter.val) hsum_lt
              c₁ s₁ t₁ rfl happ₁ hs₁_phase ht₁_phase hs₁_clock ht₁_clock with
            ⟨final, hreach₂, hwitness⟩
          refine ⟨final, ?_, hwitness⟩
          exact Relation.ReflTransGen.trans
            (Protocol.reachable_stepOrSelf c s t) hreach₂
  exact aux total c s t rfl happ hs_phase ht_phase hs_clock ht_clock

/-- Generic timed-phase progress from two distinct clocks in the same standard
timed phase. This is the population-level wrapper around
`timed_phase_progress_of_applicable_two_clocks`; it still assumes the existence
of two clocks and does not prove the role-allocation/global-existence part. -/
theorem timed_phase_progress_of_two_clocks
    (c : Config (AgentState L K))
    (p : ℕ) (hp : p ∈ ({0, 1, 5, 6, 7, 8} : Finset ℕ))
    (hphase : ∀ a ∈ c, a.phase.val = p)
    (hclocks :
      ∃ i j, i ∈ c ∧ j ∈ c ∧ i ≠ j ∧ i.role = .clock ∧ j.role = .clock) :
    ∃ final, (NonuniformMajority L K).Reachable c final ∧
      ∃ a ∈ final, p + 1 ≤ a.phase.val := by
  rcases hclocks with ⟨i, j, hi, hj, hij, hi_clock, hj_clock⟩
  have happ : Protocol.Applicable c i j :=
    pair_le_of_mem_ne hi hj hij
  exact timed_phase_progress_of_applicable_two_clocks
    (L := L) (K := K) c p hp i j happ
    (hphase i hi) (hphase j hj) hi_clock hj_clock

/-- Phase-1 timed progress for a concrete applicable clock-clock pair.  This is
the Phase-1 specialization of the generic timed-phase theorem after §3.4's
Phase-1 counter subroutine is included in `Phase1Transition`. -/
theorem phase1_progress_of_applicable_two_clocks
    (c : Config (AgentState L K)) (s t : AgentState L K)
    (happ : Protocol.Applicable c s t)
    (hs_phase : s.phase.val = 1) (ht_phase : t.phase.val = 1)
    (hs_clock : s.role = .clock) (ht_clock : t.role = .clock) :
    ∃ final, (NonuniformMajority L K).Reachable c final ∧
      ∃ a ∈ final, 2 ≤ a.phase.val := by
  have hp1 : (1 : ℕ) ∈ ({0, 1, 5, 6, 7, 8} : Finset ℕ) := by simp
  simpa using
    timed_phase_progress_of_applicable_two_clocks
      (L := L) (K := K) c 1 hp1 s t happ
      hs_phase ht_phase hs_clock ht_clock

/-- Phase-1 timed progress from any configuration with two distinct clock
states in Phase 1. -/
theorem phase1_progress_of_two_clocks
    (c : Config (AgentState L K))
    (hphase1 : ∀ a ∈ c, a.phase.val = 1)
    (hclocks :
      ∃ i j, i ∈ c ∧ j ∈ c ∧ i ≠ j ∧ i.role = .clock ∧ j.role = .clock) :
    ∃ final, (NonuniformMajority L K).Reachable c final ∧
      ∃ a ∈ final, 2 ≤ a.phase.val := by
  have hp1 : (1 : ℕ) ∈ ({0, 1, 5, 6, 7, 8} : Finset ℕ) := by simp
  simpa using
    timed_phase_progress_of_two_clocks
      (L := L) (K := K) c 1 hp1 hphase1 hclocks

/-- Full Phase-0 progress from the initial all-MCR region: role allocation
first creates an applicable pair of clocks, then the standard timed-clock
argument drives one of them into Phase 1. -/
theorem phase0_progress
    (c : Config (AgentState L K))
    (hphase0 : ∀ a ∈ c, a.phase.val = 0)
    (hmcr : ∀ a ∈ c, a.role = .mcr)
    (hn : 8 ≤ c.card) :
    ∃ final, (NonuniformMajority L K).Reachable c final ∧
      ∃ a ∈ final, a.phase.val ≥ 1 := by
  rcases phase0_creates_two_clocks (L := L) (K := K) c hphase0 hmcr hn with
    ⟨c', hreach₁, hphase₁, i, j, happ, hi_clock, hj_clock⟩
  have hp0 : (0 : ℕ) ∈ ({0, 1, 5, 6, 7, 8} : Finset ℕ) := by simp
  rcases timed_phase_progress_of_applicable_two_clocks
      (L := L) (K := K) c' 0 hp0 i j happ
      (hphase₁ i (Multiset.mem_of_le happ (by simp)))
      (hphase₁ j (Multiset.mem_of_le happ (by simp)))
      hi_clock hj_clock with
    ⟨final, hreach₂, hwitness⟩
  exact ⟨final, Relation.ReflTransGen.trans hreach₁ hreach₂, hwitness⟩

/-- Phase-2 local trigger: if the two interacting opinion sets together still
contain both signs, the Phase-2 rule advances both agents to Phase 3. -/
theorem Phase2Transition_advances_of_union_has_opposite_signs
    (s t : AgentState L K)
    (hs_phase : s.phase.val = 2) (ht_phase : t.phase.val = 2)
    (hminus : hasMinusOne (opinionsUnion s.opinions t.opinions) = true)
    (hplus : hasPlusOne (opinionsUnion s.opinions t.opinions) = true) :
    (Phase2Transition L K s t).1.phase.val = 3 ∧
      (Phase2Transition L K s t).2.phase.val = 3 := by
  rcases s with
    ⟨sinput, soutput, sphase, srole, sassigned, sbias, ssmallBias,
      shour, sminute, sfull, sopinions, scounter⟩
  rcases t with
    ⟨tinput, toutput, tphase, trole, tassigned, tbias, tsmallBias,
      thour, tminute, tfull, topinions, tcounter⟩
  have hs_phase_eq : sphase = ⟨2, by decide⟩ := Fin.ext hs_phase
  have ht_phase_eq : tphase = ⟨2, by decide⟩ := Fin.ext ht_phase
  subst sphase
  subst tphase
  cases srole <;> cases trole <;>
    simp [Phase2Transition, advancePhaseWithInit, advancePhase, phaseInit,
      hminus, hplus] at hs_phase ht_phase ⊢

/-- Full dispatcher version of `Phase2Transition_advances_of_union_has_opposite_signs`.
For two agents already in Phase 2, the phase epidemic is inert, so the same
local trigger advances both dispatcher outputs to Phase 3. -/
theorem Transition_phase2_advances_of_union_has_opposite_signs
    (s t : AgentState L K)
    (hs_phase : s.phase.val = 2) (ht_phase : t.phase.val = 2)
    (hminus : hasMinusOne (opinionsUnion s.opinions t.opinions) = true)
    (hplus : hasPlusOne (opinionsUnion s.opinions t.opinions) = true) :
    (Transition L K s t).1.phase.val = 3 ∧
      (Transition L K s t).2.phase.val = 3 := by
  have hs_phase_eq : s.phase = ⟨2, by decide⟩ := Fin.ext hs_phase
  have ht_phase_eq : t.phase = ⟨2, by decide⟩ := Fin.ext ht_phase
  have hepidemic := phaseEpidemicUpdate_eq_self_of_phase
    (L := L) (K := K) ⟨2, by decide⟩ (by decide) s t hs_phase_eq ht_phase_eq
  have hlocal := Phase2Transition_advances_of_union_has_opposite_signs
    (L := L) (K := K) s t hs_phase ht_phase hminus hplus
  unfold Transition
  rw [hepidemic]
  simp [hs_phase_eq, hlocal.1, hlocal.2]

/-- A single applicable Phase-2 opposite-sign interaction is reachable and
produces an agent in Phase at least 3. -/
theorem phase2_advance_step_of_union_has_opposite_signs
    (c : Config (AgentState L K)) (s t : AgentState L K)
    (happ : Protocol.Applicable c s t)
    (hs_phase : s.phase.val = 2) (ht_phase : t.phase.val = 2)
    (hminus : hasMinusOne (opinionsUnion s.opinions t.opinions) = true)
    (hplus : hasPlusOne (opinionsUnion s.opinions t.opinions) = true) :
    ∃ final, (NonuniformMajority L K).Reachable c final ∧
      ∃ a ∈ final, 3 ≤ a.phase.val := by
  let final := Protocol.stepOrSelf (NonuniformMajority L K) c s t
  refine ⟨final, Protocol.reachable_stepOrSelf c s t, ?_⟩
  have hstep :
      final =
        c - ({s, t} : Multiset (AgentState L K)) +
          ({(Transition L K s t).1, (Transition L K s t).2} :
            Multiset (AgentState L K)) := by
    unfold final Protocol.stepOrSelf
    rw [if_pos happ]
    rfl
  have hadvance := Transition_phase2_advances_of_union_has_opposite_signs
    (L := L) (K := K) s t hs_phase ht_phase hminus hplus
  refine ⟨(Transition L K s t).1, ?_, ?_⟩
  · rw [hstep]
    simp
  · omega

/-- Phase-2 local no-advance condition: every applicable pair of agents in
the configuration is already unable to trigger the Phase-2 opposite-sign
advance.  Applicability is included because population-protocol steps require
the selected ordered pair as a submultiset. -/
def phase2LocallyStable (c : Config (AgentState L K)) : Prop :=
  (∀ a ∈ c, a.phase.val = 2) ∧
    ∀ a b, Protocol.Applicable c a b →
      ¬ (hasMinusOne (opinionsUnion a.opinions b.opinions) = true ∧
          hasPlusOne (opinionsUnion a.opinions b.opinions) = true)

/-- Phase 2 either has no applicable opposite-sign trigger, or one protocol
step reaches Phase at least 3. -/
theorem phase2_progress_or_locallyStable
    (c : Config (AgentState L K))
    (hphase2 : ∀ a ∈ c, a.phase.val = 2) :
    phase2LocallyStable (L := L) (K := K) c ∨
      (∃ final, (NonuniformMajority L K).Reachable c final ∧
        ∃ a ∈ final, 3 ≤ a.phase.val) := by
  classical
  by_cases htrigger :
      ∃ s t, Protocol.Applicable c s t ∧
        hasMinusOne (opinionsUnion s.opinions t.opinions) = true ∧
        hasPlusOne (opinionsUnion s.opinions t.opinions) = true
  · rcases htrigger with ⟨s, t, happ, hminus, hplus⟩
    have hs_mem : s ∈ c := Multiset.mem_of_le happ (by simp)
    have ht_mem : t ∈ c := Multiset.mem_of_le happ (by simp)
    exact Or.inr
      (phase2_advance_step_of_union_has_opposite_signs
        (L := L) (K := K) c s t happ
        (hphase2 s hs_mem) (hphase2 t ht_mem) hminus hplus)
  · refine Or.inl ⟨hphase2, ?_⟩
    intro a b happ hboth
    exact htrigger ⟨a, b, happ, hboth.1, hboth.2⟩

/-- If a Phase-2 configuration is not locally stable in the no-trigger sense,
one protocol step reaches Phase at least 3. -/
theorem phase2_advance_of_not_locallyStable
    (c : Config (AgentState L K))
    (hphase2 : ∀ a ∈ c, a.phase.val = 2)
    (hnot : ¬ phase2LocallyStable (L := L) (K := K) c) :
    ∃ final, (NonuniformMajority L K).Reachable c final ∧
      ∃ a ∈ final, 3 ≤ a.phase.val := by
  rcases phase2_progress_or_locallyStable (L := L) (K := K) c hphase2 with hstable | hadvance
  · exact False.elim (hnot hstable)
  · exact hadvance

/-- Phase 4 big-bias predicate matching the local transition trigger: a dyadic
bias whose exponent is strictly below `L`. -/
def phase4HasBigBias (a : AgentState L K) : Prop :=
  ∃ sgn i, a.bias = Bias.dyadic sgn i ∧ i.val < L

/-- Phase-4 local trigger: if either interacting agent has big bias, the Phase-4
rule advances both agents to Phase 5. -/
theorem Phase4Transition_advances_of_big_bias
    (s t : AgentState L K)
    (hs_phase : s.phase.val = 4) (ht_phase : t.phase.val = 4)
    (hbig : phase4HasBigBias (L := L) (K := K) s ∨
      phase4HasBigBias (L := L) (K := K) t) :
    (Phase4Transition L K s t).1.phase.val = 5 ∧
      (Phase4Transition L K s t).2.phase.val = 5 := by
  rcases hbig with hbig | hbig
  · rcases hbig with ⟨sgn, i, hbias, hi⟩
    unfold Phase4Transition advancePhase
    simp [hbias, hi, hs_phase, ht_phase]
  · rcases hbig with ⟨sgn, i, hbias, hi⟩
    unfold Phase4Transition advancePhase
    simp [hbias, hi, hs_phase, ht_phase]

/-- Full dispatcher version of `Phase4Transition_advances_of_big_bias`. -/
theorem Transition_phase4_advances_of_big_bias
    (s t : AgentState L K)
    (hs_phase : s.phase.val = 4) (ht_phase : t.phase.val = 4)
    (hbig : phase4HasBigBias (L := L) (K := K) s ∨
      phase4HasBigBias (L := L) (K := K) t) :
    (Transition L K s t).1.phase.val = 5 ∧
      (Transition L K s t).2.phase.val = 5 := by
  have hs_phase_eq : s.phase = ⟨4, by decide⟩ := Fin.ext hs_phase
  have ht_phase_eq : t.phase = ⟨4, by decide⟩ := Fin.ext ht_phase
  have hepidemic := phaseEpidemicUpdate_eq_self_of_phase
    (L := L) (K := K) ⟨4, by decide⟩ (by decide) s t hs_phase_eq ht_phase_eq
  have hlocal := Phase4Transition_advances_of_big_bias
    (L := L) (K := K) s t hs_phase ht_phase hbig
  unfold Transition
  rw [hepidemic]
  simp [hs_phase_eq, hlocal.1, hlocal.2]

/-- A single applicable Phase-4 big-bias interaction is reachable and produces
an agent in Phase at least 5. -/
theorem phase4_advance_step_of_big_bias
    (c : Config (AgentState L K)) (s t : AgentState L K)
    (happ : Protocol.Applicable c s t)
    (hs_phase : s.phase.val = 4) (ht_phase : t.phase.val = 4)
    (hbig : phase4HasBigBias (L := L) (K := K) s ∨
      phase4HasBigBias (L := L) (K := K) t) :
    ∃ final, (NonuniformMajority L K).Reachable c final ∧
      ∃ a ∈ final, 5 ≤ a.phase.val := by
  let final := Protocol.stepOrSelf (NonuniformMajority L K) c s t
  refine ⟨final, Protocol.reachable_stepOrSelf c s t, ?_⟩
  have hstep :
      final =
        c - ({s, t} : Multiset (AgentState L K)) +
          ({(Transition L K s t).1, (Transition L K s t).2} :
            Multiset (AgentState L K)) := by
    unfold final Protocol.stepOrSelf
    rw [if_pos happ]
    rfl
  have hadvance := Transition_phase4_advances_of_big_bias
    (L := L) (K := K) s t hs_phase ht_phase hbig
  refine ⟨(Transition L K s t).1, ?_, ?_⟩
  · rw [hstep]
    simp
  · omega

/-- Phase-4 local no-advance condition: all agents are in Phase 4 and every
applicable interaction pair fails the big-bias trigger. -/
def phase4LocallyStable (c : Config (AgentState L K)) : Prop :=
  (∀ a ∈ c, a.phase.val = 4) ∧
    ∀ a ∈ c, ∀ b ∈ c, Protocol.Applicable c a b →
      ¬ (phase4HasBigBias (L := L) (K := K) a ∨
          phase4HasBigBias (L := L) (K := K) b)

/-- Phase 4 either has no applicable big-bias trigger, or one protocol step
reaches Phase at least 5. -/
theorem phase4_progress_or_locallyStable
    (c : Config (AgentState L K))
    (hphase4 : ∀ a ∈ c, a.phase.val = 4) :
    phase4LocallyStable (L := L) (K := K) c ∨
      (∃ final, (NonuniformMajority L K).Reachable c final ∧
        ∃ a ∈ final, 5 ≤ a.phase.val) := by
  classical
  by_cases htrigger :
      ∃ s t, Protocol.Applicable c s t ∧
        (phase4HasBigBias (L := L) (K := K) s ∨
          phase4HasBigBias (L := L) (K := K) t)
  · rcases htrigger with ⟨s, t, happ, hbig⟩
    have hs_mem : s ∈ c := Multiset.mem_of_le happ (by simp)
    have ht_mem : t ∈ c := Multiset.mem_of_le happ (by simp)
    exact Or.inr
      (phase4_advance_step_of_big_bias
        (L := L) (K := K) c s t happ
        (hphase4 s hs_mem) (hphase4 t ht_mem) hbig)
  · refine Or.inl ⟨hphase4, ?_⟩
    intro a _ha b _hb happ hbig
    exact htrigger ⟨a, b, happ, hbig⟩

/-- If a Phase-4 configuration is not locally stable in the no-trigger sense,
one protocol step reaches Phase at least 5. -/
theorem phase4_advance_of_not_locallyStable
    (c : Config (AgentState L K))
    (hphase4 : ∀ a ∈ c, a.phase.val = 4)
    (hnot : ¬ phase4LocallyStable (L := L) (K := K) c) :
    ∃ final, (NonuniformMajority L K).Reachable c final ∧
      ∃ a ∈ final, 5 ≤ a.phase.val := by
  rcases phase4_progress_or_locallyStable (L := L) (K := K) c hphase4 with hstable | hadvance
  · exact False.elim (hnot hstable)
  · exact hadvance

/-- Phase-9 local trigger: Phase 9 reuses the Phase-2 opinion rule, so an
opposite-sign union advances both agents to Phase 10. -/
theorem Phase9Transition_advances_of_union_has_opposite_signs
    (s t : AgentState L K)
    (hs_phase : s.phase.val = 9) (ht_phase : t.phase.val = 9)
    (hminus : hasMinusOne (opinionsUnion s.opinions t.opinions) = true)
    (hplus : hasPlusOne (opinionsUnion s.opinions t.opinions) = true) :
    (Phase9Transition L K s t).1.phase.val = 10 ∧
      (Phase9Transition L K s t).2.phase.val = 10 := by
  rcases s with
    ⟨sinput, soutput, sphase, srole, sassigned, sbias, ssmallBias,
      shour, sminute, sfull, sopinions, scounter⟩
  rcases t with
    ⟨tinput, toutput, tphase, trole, tassigned, tbias, tsmallBias,
      thour, tminute, tfull, topinions, tcounter⟩
  have hs_phase_eq : sphase = ⟨9, by decide⟩ := Fin.ext hs_phase
  have ht_phase_eq : tphase = ⟨9, by decide⟩ := Fin.ext ht_phase
  subst sphase
  subst tphase
  cases srole <;> cases trole <;>
    simp [Phase9Transition, Phase2Transition, advancePhaseWithInit, advancePhase,
      phaseInit, enterPhase10, phase10, hminus, hplus] at hs_phase ht_phase ⊢

/-- Full dispatcher version of `Phase9Transition_advances_of_union_has_opposite_signs`.
The subsequent Phase-10 entry initialization preserves the phase value 10. -/
theorem Transition_phase9_advances_of_union_has_opposite_signs
    (s t : AgentState L K)
    (hs_phase : s.phase.val = 9) (ht_phase : t.phase.val = 9)
    (hminus : hasMinusOne (opinionsUnion s.opinions t.opinions) = true)
    (hplus : hasPlusOne (opinionsUnion s.opinions t.opinions) = true) :
    (Transition L K s t).1.phase.val = 10 ∧
      (Transition L K s t).2.phase.val = 10 := by
  have hs_phase_eq : s.phase = ⟨9, by decide⟩ := Fin.ext hs_phase
  have ht_phase_eq : t.phase = ⟨9, by decide⟩ := Fin.ext ht_phase
  have hepidemic := phaseEpidemicUpdate_eq_self_of_phase
    (L := L) (K := K) ⟨9, by decide⟩ (by decide) s t hs_phase_eq ht_phase_eq
  have hlocal := Phase9Transition_advances_of_union_has_opposite_signs
    (L := L) (K := K) s t hs_phase ht_phase hminus hplus
  unfold Transition
  rw [hepidemic]
  simp [hs_phase_eq, hlocal.1, hlocal.2]

/-- A single applicable Phase-9 opposite-sign interaction is reachable and
produces an agent in Phase 10. -/
theorem phase9_advance_step_of_union_has_opposite_signs
    (c : Config (AgentState L K)) (s t : AgentState L K)
    (happ : Protocol.Applicable c s t)
    (hs_phase : s.phase.val = 9) (ht_phase : t.phase.val = 9)
    (hminus : hasMinusOne (opinionsUnion s.opinions t.opinions) = true)
    (hplus : hasPlusOne (opinionsUnion s.opinions t.opinions) = true) :
    ∃ final, (NonuniformMajority L K).Reachable c final ∧
      ∃ a ∈ final, 10 ≤ a.phase.val := by
  let final := Protocol.stepOrSelf (NonuniformMajority L K) c s t
  refine ⟨final, Protocol.reachable_stepOrSelf c s t, ?_⟩
  have hstep :
      final =
        c - ({s, t} : Multiset (AgentState L K)) +
          ({(Transition L K s t).1, (Transition L K s t).2} :
            Multiset (AgentState L K)) := by
    unfold final Protocol.stepOrSelf
    rw [if_pos happ]
    rfl
  have hadvance := Transition_phase9_advances_of_union_has_opposite_signs
    (L := L) (K := K) s t hs_phase ht_phase hminus hplus
  refine ⟨(Transition L K s t).1, ?_, ?_⟩
  · rw [hstep]
    simp
  · omega

/-- Phase-9 local no-advance condition: every applicable pair of agents in
the configuration is unable to trigger the Phase-9 opposite-sign advance. -/
def phase9LocallyStable (c : Config (AgentState L K)) : Prop :=
  (∀ a ∈ c, a.phase.val = 9) ∧
    ∀ a b, Protocol.Applicable c a b →
      ¬ (hasMinusOne (opinionsUnion a.opinions b.opinions) = true ∧
          hasPlusOne (opinionsUnion a.opinions b.opinions) = true)

/-- Phase 9 either has no applicable opposite-sign trigger, or one protocol
step reaches Phase 10. -/
theorem phase9_progress_or_locallyStable
    (c : Config (AgentState L K))
    (hphase9 : ∀ a ∈ c, a.phase.val = 9) :
    phase9LocallyStable (L := L) (K := K) c ∨
      (∃ final, (NonuniformMajority L K).Reachable c final ∧
        ∃ a ∈ final, 10 ≤ a.phase.val) := by
  classical
  by_cases htrigger :
      ∃ s t, Protocol.Applicable c s t ∧
        hasMinusOne (opinionsUnion s.opinions t.opinions) = true ∧
        hasPlusOne (opinionsUnion s.opinions t.opinions) = true
  · rcases htrigger with ⟨s, t, happ, hminus, hplus⟩
    have hs_mem : s ∈ c := Multiset.mem_of_le happ (by simp)
    have ht_mem : t ∈ c := Multiset.mem_of_le happ (by simp)
    exact Or.inr
      (phase9_advance_step_of_union_has_opposite_signs
        (L := L) (K := K) c s t happ
        (hphase9 s hs_mem) (hphase9 t ht_mem) hminus hplus)
  · refine Or.inl ⟨hphase9, ?_⟩
    intro a b happ hboth
    exact htrigger ⟨a, b, happ, hboth.1, hboth.2⟩

/-- If a Phase-9 configuration is not locally stable in the no-trigger sense,
one protocol step reaches Phase 10. -/
theorem phase9_advance_of_not_locallyStable
    (c : Config (AgentState L K))
    (hphase9 : ∀ a ∈ c, a.phase.val = 9)
    (hnot : ¬ phase9LocallyStable (L := L) (K := K) c) :
    ∃ final, (NonuniformMajority L K).Reachable c final ∧
      ∃ a ∈ final, 10 ≤ a.phase.val := by
  rcases phase9_progress_or_locallyStable (L := L) (K := K) c hphase9 with hstable | hadvance
  · exact False.elim (hnot hstable)
  · exact hadvance

end ExactMajority
