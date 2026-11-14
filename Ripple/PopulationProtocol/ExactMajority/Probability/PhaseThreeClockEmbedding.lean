-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockEmbedding.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockGatedLevelOne

/-!
# The embedding of the clock front into the virtual continuation (N12, step 2 remainder)

Clock effective minutes change only at a Clock pair with an active endpoint. This file
proves the two remaining one-step facts and assembles the labelling-level step law.

* `virtualRule_inactive_clock_pair`: two inactive Clocks in the regime keep effective
  minute zero (they are dispatched at Phase 1 or 2; a Phase-2 advance resets the
  minute).
* `virtualRule_clock_nonclock`, `virtualRule_nonclock_clock`: a Clock meeting a
  non-Clock keeps its effective minute, provided the interaction is not a backup entry
  (hypothesis `hnb`: neither dispatched endpoint is in Phase 10).
* `frontCount_ruleUpdate_regime`: on a labelling in the regime, for `1 ≤ ℓ ≤ Q`, the
  level-`ℓ` front count changes by the `GatedTick` indicator of the drawn pair, with the
  roles after the step fixed (`hroles`, discharged downstream by `roles_fixed`).
* `frontCount_virtualLabels_succ_regime`: the same along the virtual process.
* `stageEvent_frontCount_eq`: the bridge to `StageEventSpec.frontCount` when the roles
  at `v` are those at `S`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockEmbedding

open TimeTheorem PairLog PairLogAuxiliary PhaseThreeClockVirtual PhaseThreeClockGatedLaw
  PhaseThreeClockGatedLevelOne

variable {L K : ℕ}

/-! ## Initializer phases and roles -/

theorem phaseInit_phase_eq_or_ten' (p : Fin 11) (a : AgentState L K) :
    (phaseInit L K p a).phase.val = a.phase.val ∨ (phaseInit L K p a).phase.val = 10 := by
  rcases a with
    ⟨input, output, phase, role, assigned, bias, smallBias, hour, minute, full, opinions, counter⟩
  fin_cases p <;> cases role <;> simp [phaseInit, enterPhase10, phase10] <;>
    (try split_ifs) <;> (try simp [enterPhase10, phase10])

theorem runInitsBetween_phase_eq_or_ten (oldP newP : ℕ) (a : AgentState L K) :
    (runInitsBetween L K oldP newP a).phase.val = a.phase.val ∨
    (runInitsBetween L K oldP newP a).phase.val = 10 := by
  unfold runInitsBetween
  generalize (List.range 11).filter (fun k => oldP < k ∧ k ≤ newP) = l
  induction l generalizing a with
  | nil => exact Or.inl rfl
  | cons k l ih =>
      rw [List.foldl_cons]
      rcases ih (if h : k < 11 then phaseInit L K ⟨k, h⟩ a else a) with h1 | h1
      · rw [h1]
        split_ifs with hk
        · exact phaseInit_phase_eq_or_ten' _ a
        · exact Or.inl rfl
      · exact Or.inr h1

theorem runInitsBetween_role_ne_clock (oldP newP : ℕ) (a : AgentState L K)
    (ha : a.role ≠ .clock) : (runInitsBetween L K oldP newP a).role ≠ .clock := by
  unfold runInitsBetween
  generalize (List.range 11).filter (fun k => oldP < k ∧ k ≤ newP) = l
  induction l generalizing a with
  | nil => exact ha
  | cons k l ih =>
      rw [List.foldl_cons]
      apply ih
      split_ifs with hk
      · rw [phaseInit_role]
        split_ifs with hcr
        · simp
        · exact ha
      · exact ha

/-- Without a backup entry, the phase epidemic is the pair of initializer chains. -/
theorem phaseEpidemicUpdate_eq_of_no_backup (s t : AgentState L K)
    (hs10 : s.phase.val < 10) (ht10 : t.phase.val < 10)
    (hnb : (phaseEpidemicUpdate L K s t).1.phase.val ≠ 10 ∧
      (phaseEpidemicUpdate L K s t).2.phase.val ≠ 10) :
    phaseEpidemicUpdate L K s t =
      (runInitsBetween L K s.phase.val (max s.phase t.phase).val
          { s with phase := max s.phase t.phase },
        runInitsBetween L K t.phase.val (max s.phase t.phase).val
          { t with phase := max s.phase t.phase }) := by
  unfold phaseEpidemicUpdate at hnb ⊢
  simp only [] at hnb ⊢
  split_ifs at hnb ⊢ with h10
  · exfalso
    have := hnb.1
    simp [hs10] at this
  · rfl

/-! ## Phase-3, Phase-1 and Phase-2 rules on a Clock with a non-Clock partner -/

theorem phase3Transition_clock_left (s t : AgentState L K)
    (hs : s.role = .clock) (ht : t.role ≠ .clock) :
    (Phase3Transition L K s t).1 = s := by
  simp [Phase3Transition, hs, ht]

theorem phase3Transition_clock_right (s t : AgentState L K)
    (hs : s.role ≠ .clock) (ht : t.role = .clock) :
    (Phase3Transition L K s t).2 = t := by
  simp [Phase3Transition, hs, ht]

theorem phase1Transition_clock_left (s t : AgentState L K) (hs : s.role = .clock) :
    (Phase1Transition L K s t).1 = clockCounterStep L K s := by
  simp [Phase1Transition, hs]

theorem phase1Transition_clock_right (s t : AgentState L K) (ht : t.role = .clock) :
    (Phase1Transition L K s t).2 = clockCounterStep L K t := by
  simp [Phase1Transition, ht]

/-- Advancing a Phase-1 Clock with neutral small bias: Phase 2, minute unchanged. -/
theorem advancePhaseWithInit_clock_one (b : AgentState L K) (hr : b.role = .clock)
    (hp : b.phase.val = 1) (hsb : b.smallBias.val = 3) :
    (advancePhaseWithInit L K b).role = .clock ∧
    (advancePhaseWithInit L K b).phase.val = 2 ∧
    (advancePhaseWithInit L K b).smallBias = b.smallBias ∧
    (advancePhaseWithInit L K b).minute = b.minute := by
  unfold advancePhaseWithInit
  set c := advancePhase L K b with hc
  have hcp : c.phase.val = 2 := by
    rw [hc]; unfold advancePhase; rw [dif_pos (by omega)]; simp [hp]
  have hcr : c.role = .clock := by rw [hc, advancePhase_role]; exact hr
  have hcs : c.smallBias = b.smallBias := by rw [hc, advancePhase_smallBias]
  have hcm : c.minute = b.minute := by
    rw [hc]; unfold advancePhase; rw [dif_pos (by omega)]
  have hcfin : c.phase = ⟨2, by omega⟩ := Fin.ext hcp
  dsimp only
  rw [hcfin, phaseInit_two_safe c (by rw [hcs]; exact hsb)]
  exact ⟨hcr, hcp, hcs, hcm⟩

/-- Advancing a Phase-2 Clock: Phase 3 with minute zero. -/
theorem advancePhaseWithInit_clock_two (b : AgentState L K) (hr : b.role = .clock)
    (hp : b.phase.val = 2) :
    (advancePhaseWithInit L K b).role = .clock ∧
    (advancePhaseWithInit L K b).phase.val = 3 ∧
    (advancePhaseWithInit L K b).smallBias = b.smallBias ∧
    (advancePhaseWithInit L K b).minute.val = 0 := by
  unfold advancePhaseWithInit
  set c := advancePhase L K b with hc
  have hcp : c.phase.val = 3 := by
    rw [hc]; unfold advancePhase; rw [dif_pos (by omega)]; simp [hp]
  have hcr : c.role = .clock := by rw [hc, advancePhase_role]; exact hr
  have hcs : c.smallBias = b.smallBias := by rw [hc, advancePhase_smallBias]
  have hcfin : c.phase = ⟨3, by omega⟩ := Fin.ext hcp
  dsimp only
  rw [hcfin, phaseInit_three_clock c hcr]
  exact ⟨hcr, hcp, hcs, rfl⟩

/-- The counter subroutine on a Phase-1 Clock keeps effective minute zero. -/
theorem stdCounterSubroutine_clock_low (a : AgentState L K) (hr : a.role = .clock)
    (hp : a.phase.val = 1) (hsb : a.smallBias.val = 3) :
    (stdCounterSubroutine L K a).role = .clock ∧
    (stdCounterSubroutine L K a).phase.val ≤ 2 ∧
    (stdCounterSubroutine L K a).smallBias = a.smallBias ∧
    effMinute (stdCounterSubroutine L K a) = 0 := by
  unfold stdCounterSubroutine
  split_ifs with h0
  · obtain ⟨h1, h2, h3, -⟩ := advancePhaseWithInit_clock_one a hr hp hsb
    refine ⟨h1, by omega, h3, ?_⟩
    unfold effMinute
    rw [if_neg (by omega)]
  · refine ⟨hr, by simp [hp], rfl, ?_⟩
    unfold effMinute
    rw [if_neg (by simp [hp])]

/-- The Phase-2 rule on a Clock (either position) keeps effective minute zero. -/
theorem phase2Transition_clock_left (s t : AgentState L K) (hs : s.role = .clock)
    (hp : s.phase.val = 2) :
    (Phase2Transition L K s t).1.role = .clock ∧
    (Phase2Transition L K s t).1.phase.val ≤ 3 ∧
    (Phase2Transition L K s t).1.smallBias = s.smallBias ∧
    effMinute (Phase2Transition L K s t).1 = 0 := by
  unfold Phase2Transition
  dsimp only
  split_ifs
  · dsimp only
    obtain ⟨h1, h2, h3, h4⟩ := advancePhaseWithInit_clock_two
      { s with opinions := opinionsUnion s.opinions t.opinions } hs hp
    refine ⟨h1, h2.le, h3, ?_⟩
    unfold effMinute
    rw [if_pos h2.ge, h4]
  all_goals
    dsimp only
    refine ⟨hs, by simp [hp], rfl, ?_⟩
    unfold effMinute
    rw [if_neg (by simp [hp])]

theorem phase2Transition_clock_right (s t : AgentState L K) (ht : t.role = .clock)
    (hp : t.phase.val = 2) :
    (Phase2Transition L K s t).2.role = .clock ∧
    (Phase2Transition L K s t).2.phase.val ≤ 3 ∧
    (Phase2Transition L K s t).2.smallBias = t.smallBias ∧
    effMinute (Phase2Transition L K s t).2 = 0 := by
  unfold Phase2Transition
  dsimp only
  split_ifs
  · dsimp only
    obtain ⟨h1, h2, h3, h4⟩ := advancePhaseWithInit_clock_two
      { t with opinions := opinionsUnion s.opinions t.opinions } ht hp
    refine ⟨h1, h2.le, h3, ?_⟩
    unfold effMinute
    rw [if_pos h2.ge, h4]
  all_goals
    dsimp only
    refine ⟨ht, by simp [hp], rfl, ?_⟩
    unfold effMinute
    rw [if_neg (by simp [hp])]

/-! ## Dispatch at Phases 1 and 2 -/

theorem transition_eq_phase1_of_dispatch (s t : AgentState L K)
    (h1 : (phaseEpidemicUpdate L K s t).1.phase.val = 1) :
    Transition L K s t =
      (finishPhase10Entry L K (phaseEpidemicUpdate L K s t).1
          (Phase1Transition L K (phaseEpidemicUpdate L K s t).1
            (phaseEpidemicUpdate L K s t).2).1,
        finishPhase10Entry L K (phaseEpidemicUpdate L K s t).2
          (Phase1Transition L K (phaseEpidemicUpdate L K s t).1
            (phaseEpidemicUpdate L K s t).2).2) := by
  unfold Transition
  generalize hd : phaseEpidemicUpdate L K s t = d at *
  obtain ⟨s', t'⟩ := d
  simp only at h1 ⊢
  have hph : s'.phase = ⟨1, by omega⟩ := Fin.ext h1
  rw [hph]

theorem transition_eq_phase2_of_dispatch (s t : AgentState L K)
    (h2 : (phaseEpidemicUpdate L K s t).1.phase.val = 2) :
    Transition L K s t =
      (finishPhase10Entry L K (phaseEpidemicUpdate L K s t).1
          (Phase2Transition L K (phaseEpidemicUpdate L K s t).1
            (phaseEpidemicUpdate L K s t).2).1,
        finishPhase10Entry L K (phaseEpidemicUpdate L K s t).2
          (Phase2Transition L K (phaseEpidemicUpdate L K s t).1
            (phaseEpidemicUpdate L K s t).2).2) := by
  unfold Transition
  generalize hd : phaseEpidemicUpdate L K s t = d at *
  obtain ⟨s', t'⟩ := d
  simp only at h2 ⊢
  have hph : s'.phase = ⟨2, by omega⟩ := Fin.ext h2
  rw [hph]

theorem virtualRule_eq_transition_of_not_cap (s t : AgentState L K)
    (h : ¬ CapCounterPair s t) : virtualRule s t = Transition L K s t := by
  unfold virtualRule
  rw [if_neg h]

/-! ## Two inactive Clocks -/

theorem virtualRule_inactive_clock_pair (s t : AgentState L K)
    (hs : ClockRegime s) (ht : ClockRegime t)
    (hs3 : s.phase.val < 3) (ht3 : t.phase.val < 3) :
    (virtualRule s t).1.role = .clock ∧ effMinute (virtualRule s t).1 = 0 ∧
    (virtualRule s t).1.phase.val ≤ 3 ∧ (virtualRule s t).1.smallBias.val = 3 ∧
    (virtualRule s t).2.role = .clock ∧ effMinute (virtualRule s t).2 = 0 ∧
    (virtualRule s t).2.phase.val ≤ 3 ∧ (virtualRule s t).2.smallBias.val = 3 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := phaseEpidemicUpdate_clock_regime s t hs ht
  have hmax : max s.phase.val t.phase.val ≤ 2 := by omega
  have hmax_ge : 1 ≤ max s.phase.val t.phase.val :=
    le_trans hs.phase_ge (le_max_left _ _)
  have hnc : ¬ CapCounterPair s t := by
    intro h
    have hdispatch := h.1
    rw [h3] at hdispatch
    omega
  rw [virtualRule_eq_transition_of_not_cap s t hnc]
  have hs'sb : (phaseEpidemicUpdate L K s t).1.smallBias.val = 3 := by
    rw [h5]
    exact hs.small
  have ht'sb : (phaseEpidemicUpdate L K s t).2.smallBias.val = 3 := by
    rw [h6]
    exact ht.small
  rcases (by omega : max s.phase.val t.phase.val = 1 ∨ max s.phase.val t.phase.val = 2) with
    hm | hm
  · rw [transition_eq_phase1_of_dispatch s t (by rw [h3, hm]),
      phase1Transition_clock_left _ _ h1, phase1Transition_clock_right _ _ h2]
    unfold clockCounterStep
    rw [if_pos h1, if_pos h2]
    obtain ⟨a1, a2, a3, a4⟩ := stdCounterSubroutine_clock_low
      (phaseEpidemicUpdate L K s t).1 h1 (by rw [h3, hm]) hs'sb
    obtain ⟨b1, b2, b3, b4⟩ := stdCounterSubroutine_clock_low
      (phaseEpidemicUpdate L K s t).2 h2 (by rw [h4, hm]) ht'sb
    have ha10 : (stdCounterSubroutine L K (phaseEpidemicUpdate L K s t).1).phase.val ≠ 10 := by
      omega
    have hb10 : (stdCounterSubroutine L K (phaseEpidemicUpdate L K s t).2).phase.val ≠ 10 := by
      omega
    rw [finishPhase10Entry_eq_self_of_after_ne_10 L K
        (phaseEpidemicUpdate L K s t).1
        (stdCounterSubroutine L K (phaseEpidemicUpdate L K s t).1) ha10,
      finishPhase10Entry_eq_self_of_after_ne_10 L K
        (phaseEpidemicUpdate L K s t).2
        (stdCounterSubroutine L K (phaseEpidemicUpdate L K s t).2) hb10]
    dsimp only
    exact ⟨a1, a4, le_trans a2 (by decide : 2 ≤ 3), by rw [a3]; exact hs'sb,
      b1, b4, le_trans b2 (by decide : 2 ≤ 3), by rw [b3]; exact ht'sb⟩
  · rw [transition_eq_phase2_of_dispatch s t (by rw [h3, hm])]
    obtain ⟨a1, a2, a3, a4⟩ := phase2Transition_clock_left
      (phaseEpidemicUpdate L K s t).1 (phaseEpidemicUpdate L K s t).2 h1 (by rw [h3, hm])
    obtain ⟨b1, b2, b3, b4⟩ := phase2Transition_clock_right
      (phaseEpidemicUpdate L K s t).1 (phaseEpidemicUpdate L K s t).2 h2 (by rw [h4, hm])
    have ha10 : (Phase2Transition L K (phaseEpidemicUpdate L K s t).1
        (phaseEpidemicUpdate L K s t).2).1.phase.val ≠ 10 := by
      omega
    have hb10 : (Phase2Transition L K (phaseEpidemicUpdate L K s t).1
        (phaseEpidemicUpdate L K s t).2).2.phase.val ≠ 10 := by
      omega
    rw [finishPhase10Entry_eq_self_of_after_ne_10 L K
        (phaseEpidemicUpdate L K s t).1
        (Phase2Transition L K (phaseEpidemicUpdate L K s t).1
          (phaseEpidemicUpdate L K s t).2).1 ha10,
      finishPhase10Entry_eq_self_of_after_ne_10 L K
        (phaseEpidemicUpdate L K s t).2
        (Phase2Transition L K (phaseEpidemicUpdate L K s t).1
          (phaseEpidemicUpdate L K s t).2).2 hb10]
    dsimp only
    exact ⟨a1, a4, a2, by rw [a3]; exact hs'sb, b1, b4, b2, by rw [b3]; exact ht'sb⟩

/-! ## A Clock meeting a non-Clock -/

/-- The dispatched states of a Clock in the regime and a non-Clock partner without a
backup entry. -/
theorem dispatched_clock_nonclock (c x : AgentState L K) (hc : ClockRegime c)
    (hx : x.role ≠ .clock) (hx1 : 1 ≤ x.phase.val) (hx3 : x.phase.val ≤ 3)
    (hnb : (phaseEpidemicUpdate L K c x).1.phase.val ≠ 10 ∧
      (phaseEpidemicUpdate L K c x).2.phase.val ≠ 10) :
    (phaseEpidemicUpdate L K c x).1.role = .clock ∧
    (phaseEpidemicUpdate L K c x).1.phase.val = max c.phase.val x.phase.val ∧
    (phaseEpidemicUpdate L K c x).1.smallBias = c.smallBias ∧
    effMinute (phaseEpidemicUpdate L K c x).1 = effMinute c ∧
    (phaseEpidemicUpdate L K c x).2.role ≠ .clock ∧
    (phaseEpidemicUpdate L K c x).2.phase.val = max c.phase.val x.phase.val := by
  have hepi := phaseEpidemicUpdate_eq_of_no_backup c x (by have := hc.phase_le; omega)
    (by omega) hnb
  rw [hepi] at hnb ⊢
  simp only [] at hnb ⊢
  have hpv : (max c.phase x.phase).val = max c.phase.val x.phase.val := fin_val_max _ _
  have hp3 : (max c.phase x.phase).val ≤ 3 := by rw [hpv]; have := hc.phase_le; omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rcases Nat.lt_or_ge c.phase.val (max c.phase x.phase).val with hlt | hge
    · exact (initialized_clock_facts c hc _ hlt hp3).1
    · have hcp : c.phase = max c.phase x.phase :=
        Fin.ext (le_antisymm (by rw [hpv]; exact le_max_left _ _) hge)
      rw [← hcp, runInitsBetween_self]
      exact hc.role
  · rcases Nat.lt_or_ge c.phase.val (max c.phase x.phase).val with hlt | hge
    · rw [(initialized_clock_facts c hc _ hlt hp3).2.1, hpv]
    · have hcp : c.phase = max c.phase x.phase :=
        Fin.ext (le_antisymm (by rw [hpv]; exact le_max_left _ _) hge)
      rw [← hcp, runInitsBetween_self]
      show c.phase.val = _
      rw [← hpv, ← hcp]
  · rcases Nat.lt_or_ge c.phase.val (max c.phase x.phase).val with hlt | hge
    · exact (initialized_clock_facts c hc _ hlt hp3).2.2.1
    · have hcp : c.phase = max c.phase x.phase :=
        Fin.ext (le_antisymm (by rw [hpv]; exact le_max_left _ _) hge)
      rw [← hcp, runInitsBetween_self]
  · rcases Nat.lt_or_ge c.phase.val (max c.phase x.phase).val with hlt | hge
    · exact (initialized_clock_facts c hc _ hlt hp3).2.2.2
    · have hcp : c.phase = max c.phase x.phase :=
        Fin.ext (le_antisymm (by rw [hpv]; exact le_max_left _ _) hge)
      rw [← hcp, runInitsBetween_self]
  · exact runInitsBetween_role_ne_clock _ _ _ (by simpa using hx)
  · rcases runInitsBetween_phase_eq_or_ten x.phase.val (max c.phase x.phase).val
        { x with phase := max c.phase x.phase } with h | h
    · rw [h]
      exact hpv
    · exact absurd h hnb.2

/-- A Clock meeting a non-Clock keeps its effective minute, role and small bias. -/
theorem virtualRule_clock_nonclock (c x : AgentState L K) (hc : ClockRegime c)
    (hx : x.role ≠ .clock) (hx1 : 1 ≤ x.phase.val) (hx3 : x.phase.val ≤ 3)
    (hnb : (phaseEpidemicUpdate L K c x).1.phase.val ≠ 10 ∧
      (phaseEpidemicUpdate L K c x).2.phase.val ≠ 10) :
    (virtualRule c x).1.role = .clock ∧ effMinute (virtualRule c x).1 = effMinute c ∧
    (virtualRule c x).1.phase.val ≤ 3 ∧ (virtualRule c x).1.smallBias.val = 3 := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := dispatched_clock_nonclock c x hc hx hx1 hx3 hnb
  have hnc : ¬ CapCounterPair c x := fun h => h5 h.2.2.2.1
  rw [virtualRule_eq_transition_of_not_cap c x hnc]
  have hsb : (phaseEpidemicUpdate L K c x).1.smallBias.val = 3 := by
    rw [h3]
    exact hc.small
  have hmax3 : max c.phase.val x.phase.val ≤ 3 := max_le hc.phase_le hx3
  have hmax_ge : 1 ≤ max c.phase.val x.phase.val :=
    le_trans hc.phase_ge (le_max_left _ _)
  rcases (by omega :
      max c.phase.val x.phase.val = 1 ∨ max c.phase.val x.phase.val = 2 ∨
        max c.phase.val x.phase.val = 3) with hm | hm | hm
  · rw [transition_eq_phase1_of_dispatch c x (by rw [h2, hm]),
      phase1Transition_clock_left (phaseEpidemicUpdate L K c x).1
        (phaseEpidemicUpdate L K c x).2 h1]
    unfold clockCounterStep
    rw [if_pos h1]
    obtain ⟨a1, a2, a3, a4⟩ := stdCounterSubroutine_clock_low
      (phaseEpidemicUpdate L K c x).1 h1 (by rw [h2, hm]) hsb
    have ha10 : (stdCounterSubroutine L K (phaseEpidemicUpdate L K c x).1).phase.val ≠ 10 := by
      omega
    rw [finishPhase10Entry_eq_self_of_after_ne_10 L K
      (phaseEpidemicUpdate L K c x).1
      (stdCounterSubroutine L K (phaseEpidemicUpdate L K c x).1) ha10]
    dsimp only
    refine ⟨a1, ?_, le_trans a2 (by decide : 2 ≤ 3), by rw [a3]; exact hsb⟩
    rw [a4, effMinute_eq_zero_of_lt_three c (by
      have hcle := le_max_left c.phase.val x.phase.val
      omega)]
  · rw [transition_eq_phase2_of_dispatch c x (by rw [h2, hm])]
    obtain ⟨a1, a2, a3, a4⟩ := phase2Transition_clock_left
      (phaseEpidemicUpdate L K c x).1 (phaseEpidemicUpdate L K c x).2 h1 (by rw [h2, hm])
    have ha10 : (Phase2Transition L K (phaseEpidemicUpdate L K c x).1
        (phaseEpidemicUpdate L K c x).2).1.phase.val ≠ 10 := by
      omega
    rw [finishPhase10Entry_eq_self_of_after_ne_10 L K
      (phaseEpidemicUpdate L K c x).1
      (Phase2Transition L K (phaseEpidemicUpdate L K c x).1
        (phaseEpidemicUpdate L K c x).2).1 ha10]
    dsimp only
    refine ⟨a1, ?_, a2, by rw [a3]; exact hsb⟩
    rw [a4, effMinute_eq_zero_of_lt_three c (by
      have hcle := le_max_left c.phase.val x.phase.val
      omega)]
  · have ha10 : (phaseEpidemicUpdate L K c x).1.phase.val ≠ 10 := by
      rw [h2, hm]
      decide
    rw [transition_eq_phase3_of_dispatch c x (by rw [h2, hm]),
      phase3Transition_clock_left (phaseEpidemicUpdate L K c x).1
        (phaseEpidemicUpdate L K c x).2 h1 h5,
      finishPhase10Entry_eq_self_of_after_ne_10 L K
        (phaseEpidemicUpdate L K c x).1 (phaseEpidemicUpdate L K c x).1 ha10]
    dsimp only
    exact ⟨h1, h4, le_trans h2.le hmax3, hsb⟩

/-- The symmetric statement with the Clock as responder. -/
theorem dispatched_nonclock_clock (x c : AgentState L K) (hc : ClockRegime c)
    (hx : x.role ≠ .clock) (hx1 : 1 ≤ x.phase.val) (hx3 : x.phase.val ≤ 3)
    (hnb : (phaseEpidemicUpdate L K x c).1.phase.val ≠ 10 ∧
      (phaseEpidemicUpdate L K x c).2.phase.val ≠ 10) :
    (phaseEpidemicUpdate L K x c).2.role = .clock ∧
    (phaseEpidemicUpdate L K x c).2.phase.val = max x.phase.val c.phase.val ∧
    (phaseEpidemicUpdate L K x c).2.smallBias = c.smallBias ∧
    effMinute (phaseEpidemicUpdate L K x c).2 = effMinute c ∧
    (phaseEpidemicUpdate L K x c).1.role ≠ .clock ∧
    (phaseEpidemicUpdate L K x c).1.phase.val = max x.phase.val c.phase.val := by
  have hepi := phaseEpidemicUpdate_eq_of_no_backup x c (by omega)
    (by have := hc.phase_le; omega) hnb
  rw [hepi] at hnb ⊢
  simp only [] at hnb ⊢
  have hpv : (max x.phase c.phase).val = max x.phase.val c.phase.val := fin_val_max _ _
  have hp3 : (max x.phase c.phase).val ≤ 3 := by rw [hpv]; have := hc.phase_le; omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rcases Nat.lt_or_ge c.phase.val (max x.phase c.phase).val with hlt | hge
    · exact (initialized_clock_facts c hc _ hlt hp3).1
    · have hcp : c.phase = max x.phase c.phase :=
        Fin.ext (le_antisymm (by rw [hpv]; exact le_max_right _ _) hge)
      rw [← hcp, runInitsBetween_self]
      exact hc.role
  · rcases Nat.lt_or_ge c.phase.val (max x.phase c.phase).val with hlt | hge
    · rw [(initialized_clock_facts c hc _ hlt hp3).2.1, hpv]
    · have hcp : c.phase = max x.phase c.phase :=
        Fin.ext (le_antisymm (by rw [hpv]; exact le_max_right _ _) hge)
      rw [← hcp, runInitsBetween_self]
      show c.phase.val = _
      rw [← hpv, ← hcp]
  · rcases Nat.lt_or_ge c.phase.val (max x.phase c.phase).val with hlt | hge
    · exact (initialized_clock_facts c hc _ hlt hp3).2.2.1
    · have hcp : c.phase = max x.phase c.phase :=
        Fin.ext (le_antisymm (by rw [hpv]; exact le_max_right _ _) hge)
      rw [← hcp, runInitsBetween_self]
  · rcases Nat.lt_or_ge c.phase.val (max x.phase c.phase).val with hlt | hge
    · exact (initialized_clock_facts c hc _ hlt hp3).2.2.2
    · have hcp : c.phase = max x.phase c.phase :=
        Fin.ext (le_antisymm (by rw [hpv]; exact le_max_right _ _) hge)
      rw [← hcp, runInitsBetween_self]
  · exact runInitsBetween_role_ne_clock _ _ _ (by simpa using hx)
  · rcases runInitsBetween_phase_eq_or_ten x.phase.val (max x.phase c.phase).val
        { x with phase := max x.phase c.phase } with h | h
    · rw [h]
      exact hpv
    · exact absurd h hnb.1

theorem virtualRule_nonclock_clock (x c : AgentState L K) (hc : ClockRegime c)
    (hx : x.role ≠ .clock) (hx1 : 1 ≤ x.phase.val) (hx3 : x.phase.val ≤ 3)
    (hnb : (phaseEpidemicUpdate L K x c).1.phase.val ≠ 10 ∧
      (phaseEpidemicUpdate L K x c).2.phase.val ≠ 10) :
    (virtualRule x c).2.role = .clock ∧ effMinute (virtualRule x c).2 = effMinute c ∧
    (virtualRule x c).2.phase.val ≤ 3 ∧ (virtualRule x c).2.smallBias.val = 3 := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := dispatched_nonclock_clock x c hc hx hx1 hx3 hnb
  have hnc : ¬ CapCounterPair x c := fun h => h5 h.2.2.1
  rw [virtualRule_eq_transition_of_not_cap x c hnc]
  have hsb : (phaseEpidemicUpdate L K x c).2.smallBias.val = 3 := by
    rw [h3]
    exact hc.small
  have hmax3 : max x.phase.val c.phase.val ≤ 3 := max_le hx3 hc.phase_le
  have hmax_ge : 1 ≤ max x.phase.val c.phase.val :=
    le_trans hc.phase_ge (le_max_right _ _)
  rcases (by omega :
      max x.phase.val c.phase.val = 1 ∨ max x.phase.val c.phase.val = 2 ∨
        max x.phase.val c.phase.val = 3) with hm | hm | hm
  · rw [transition_eq_phase1_of_dispatch x c (by rw [h6, hm]),
      phase1Transition_clock_right (phaseEpidemicUpdate L K x c).1
        (phaseEpidemicUpdate L K x c).2 h1]
    unfold clockCounterStep
    rw [if_pos h1]
    obtain ⟨a1, a2, a3, a4⟩ := stdCounterSubroutine_clock_low
      (phaseEpidemicUpdate L K x c).2 h1 (by rw [h2, hm]) hsb
    have ha10 : (stdCounterSubroutine L K (phaseEpidemicUpdate L K x c).2).phase.val ≠ 10 := by
      omega
    rw [finishPhase10Entry_eq_self_of_after_ne_10 L K
      (phaseEpidemicUpdate L K x c).2
      (stdCounterSubroutine L K (phaseEpidemicUpdate L K x c).2) ha10]
    dsimp only
    refine ⟨a1, ?_, le_trans a2 (by decide : 2 ≤ 3), by rw [a3]; exact hsb⟩
    rw [a4, effMinute_eq_zero_of_lt_three c (by
      have hcle := le_max_right x.phase.val c.phase.val
      omega)]
  · rw [transition_eq_phase2_of_dispatch x c (by rw [h6, hm])]
    obtain ⟨a1, a2, a3, a4⟩ := phase2Transition_clock_right
      (phaseEpidemicUpdate L K x c).1 (phaseEpidemicUpdate L K x c).2 h1 (by rw [h2, hm])
    have ha10 : (Phase2Transition L K (phaseEpidemicUpdate L K x c).1
        (phaseEpidemicUpdate L K x c).2).2.phase.val ≠ 10 := by
      omega
    rw [finishPhase10Entry_eq_self_of_after_ne_10 L K
      (phaseEpidemicUpdate L K x c).2
      (Phase2Transition L K (phaseEpidemicUpdate L K x c).1
        (phaseEpidemicUpdate L K x c).2).2 ha10]
    dsimp only
    refine ⟨a1, ?_, a2, by rw [a3]; exact hsb⟩
    rw [a4, effMinute_eq_zero_of_lt_three c (by
      have hcle := le_max_right x.phase.val c.phase.val
      omega)]
  · have ha10 : (phaseEpidemicUpdate L K x c).2.phase.val ≠ 10 := by
      rw [h2, hm]
      decide
    rw [transition_eq_phase3_of_dispatch x c (by rw [h6, hm]),
      phase3Transition_clock_right (phaseEpidemicUpdate L K x c).1
        (phaseEpidemicUpdate L K x c).2 h5 h1,
      finishPhase10Entry_eq_self_of_after_ne_10 L K
        (phaseEpidemicUpdate L K x c).2 (phaseEpidemicUpdate L K x c).2 ha10]
    dsimp only
    exact ⟨h1, h4, le_trans h2.le hmax3, hsb⟩

/-! ## The labelling-level step law -/

variable {m : ℕ}

theorem frontInd_eq_zero_of_not_clock (ℓ : ℕ) (a : AgentState L K) (h : a.role ≠ .clock) :
    frontInd ℓ a = 0 := by
  unfold frontInd
  rw [if_neg (fun h' => h h'.1)]

theorem frontInd_eq_zero_of_eff_zero (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (a : AgentState L K)
    (h : effMinute a = 0) : frontInd ℓ a = 0 := by
  unfold frontInd
  rw [if_neg (fun h' => by have := h'.2; omega)]

theorem frontInd_eq_of_eff_eq (ℓ : ℕ) (a b : AgentState L K) (hr : a.role = b.role)
    (he : effMinute a = effMinute b) : frontInd ℓ a = frontInd ℓ b := by
  unfold frontInd
  rw [hr, he]

theorem not_gatedTick_of_not_clock_left (ℓ : ℕ) (f : Fin m → AgentState L K) (i j : Fin m)
    (hi : (f i).role ≠ .clock) : ¬ GatedTick ℓ f i j := by
  rintro ⟨h, -⟩
  rcases h with ⟨hm, -⟩ | ⟨hm, -⟩ | ⟨hm, -⟩ <;>
    simp only [belowSet, aboveSet, exactSet, Finset.mem_filter, Finset.mem_univ, true_and] at hm <;>
    exact hi hm.1

theorem not_gatedTick_of_not_clock_right (ℓ : ℕ) (f : Fin m → AgentState L K) (i j : Fin m)
    (hj : (f j).role ≠ .clock) : ¬ GatedTick ℓ f i j := by
  rintro ⟨h, -⟩
  rcases h with ⟨-, hm⟩ | ⟨-, hm⟩ | ⟨-, hm⟩ <;>
    simp only [belowSet, aboveSet, exactSet, Finset.mem_filter, Finset.mem_univ, true_and] at hm <;>
    exact hj hm.1

/-- PHASE3 P2 on a labelling in the regime: for `1 ≤ ℓ ≤ Q` the level-`ℓ` front count
changes by the gated raising indicator of the drawn pair. `hnb` excludes a backup entry
in this interaction; `hroles` fixes the roles after the step. -/
theorem frontCount_ruleUpdate_regime (f : Fin m → AgentState L K) (hK : 0 < K)
    (i j : Fin m) (hij : i ≠ j)
    (hreg : ∀ k, 1 ≤ (f k).phase.val ∧ (f k).phase.val ≤ 3)
    (hclk : ∀ k, (f k).role = .clock → (f k).smallBias.val = 3)
    (hnb : (phaseEpidemicUpdate L K (f i) (f j)).1.phase.val ≠ 10 ∧
      (phaseEpidemicUpdate L K (f i) (f j)).2.phase.val ≠ 10)
    (hroles : ∀ k, (ruleUpdate virtualRule f i j k).role = (f k).role)
    (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (hcap : ℓ ≤ K * (L + 1)) :
    frontCount (ruleUpdate virtualRule f i j) ℓ =
      frontCount f ℓ + if GatedTick ℓ f i j then 1 else 0 := by
  have hri : (virtualRule (f i) (f j)).1.role = (f i).role := by
    have := hroles i
    simp only [ruleUpdate, Function.update_of_ne hij, Function.update_self] at this
    exact this
  have hrj : (virtualRule (f i) (f j)).2.role = (f j).role := by
    have := hroles j
    simp only [ruleUpdate, Function.update_self] at this
    exact this
  have hsum := sum_update_pair (frontInd ℓ) f i j hij
    (virtualRule (f i) (f j)).1 (virtualRule (f i) (f j)).2
  by_cases hic : (f i).role = .clock <;> by_cases hjc : (f j).role = .clock
  · by_cases hact : (f i).phase.val = 3 ∨ (f j).phase.val = 3
    · have hG : GatedTick ℓ f i j ↔ RaisingTick ℓ f i j :=
        ⟨fun h => h.1, fun h => ⟨h, by omega⟩⟩
      rw [if_congr hG rfl rfl]
      exact frontCount_ruleUpdate_clock_pair_some_active f hK i j hij
        ⟨hic, (hreg i).1, (hreg i).2, hclk i hic⟩ ⟨hjc, (hreg j).1, (hreg j).2, hclk j hjc⟩
        hact ℓ hℓ hcap
    · have hi3 : (f i).phase.val < 3 := by have := (hreg i).2; omega
      have hj3 : (f j).phase.val < 3 := by have := (hreg j).2; omega
      obtain ⟨-, a2, -, -, -, b2, -, -⟩ := virtualRule_inactive_clock_pair (f i) (f j)
        ⟨hic, (hreg i).1, (hreg i).2, hclk i hic⟩ ⟨hjc, (hreg j).1, (hreg j).2, hclk j hjc⟩ hi3 hj3
      have hG : ¬ GatedTick ℓ f i j := fun h => by rcases h.2 with h' | h' <;> omega
      rw [if_neg hG, add_zero, frontCount_eq_sum, frontCount_eq_sum]
      unfold ruleUpdate
      have e1 := frontInd_eq_zero_of_eff_zero ℓ hℓ _ a2
      have e2 := frontInd_eq_zero_of_eff_zero ℓ hℓ _ b2
      have e3 := frontInd_eq_zero_of_eff_zero ℓ hℓ (f i) (effMinute_eq_zero_of_lt_three _ hi3)
      have e4 := frontInd_eq_zero_of_eff_zero ℓ hℓ (f j) (effMinute_eq_zero_of_lt_three _ hj3)
      omega
  · obtain ⟨-, c2, -, -⟩ := virtualRule_clock_nonclock (f i) (f j)
      ⟨hic, (hreg i).1, (hreg i).2, hclk i hic⟩ hjc (hreg j).1 (hreg j).2 hnb
    rw [if_neg (not_gatedTick_of_not_clock_right ℓ f i j hjc), add_zero,
      frontCount_eq_sum, frontCount_eq_sum]
    unfold ruleUpdate
    have e1 := frontInd_eq_of_eff_eq ℓ _ (f i) hri c2
    have e2 := frontInd_eq_zero_of_not_clock ℓ _ (by rw [hrj]; exact hjc)
    have e4 := frontInd_eq_zero_of_not_clock ℓ (f j) hjc
    omega
  · obtain ⟨-, c2, -, -⟩ := virtualRule_nonclock_clock (f i) (f j)
      ⟨hjc, (hreg j).1, (hreg j).2, hclk j hjc⟩ hic (hreg i).1 (hreg i).2 hnb
    rw [if_neg (not_gatedTick_of_not_clock_left ℓ f i j hic), add_zero,
      frontCount_eq_sum, frontCount_eq_sum]
    unfold ruleUpdate
    have e2 := frontInd_eq_of_eff_eq ℓ _ (f j) hrj c2
    have e1 := frontInd_eq_zero_of_not_clock ℓ _ (by rw [hri]; exact hic)
    have e3 := frontInd_eq_zero_of_not_clock ℓ (f i) hic
    omega
  · rw [if_neg (not_gatedTick_of_not_clock_left ℓ f i j hic), add_zero,
      frontCount_eq_sum, frontCount_eq_sum]
    unfold ruleUpdate
    have e1 := frontInd_eq_zero_of_not_clock ℓ _ (by rw [hri]; exact hic)
    have e2 := frontInd_eq_zero_of_not_clock ℓ _ (by rw [hrj]; exact hjc)
    have e3 := frontInd_eq_zero_of_not_clock ℓ (f i) hic
    have e4 := frontInd_eq_zero_of_not_clock ℓ (f j) hjc
    omega

/-- The step law along the virtual process on a drawn pair. -/
theorem frontCount_virtualLabels_succ_regime (init : Cfg L K) (hK : 0 < K) (ω : Ω L K)
    (t : ℕ) (i j : Fin init.card) (hd : drawLabels init ω (t + 1) = some (i, j))
    (hreg : ∀ k, 1 ≤ (virtualLabels init ω t k).phase.val ∧
      (virtualLabels init ω t k).phase.val ≤ 3)
    (hclk : ∀ k, (virtualLabels init ω t k).role = .clock →
      (virtualLabels init ω t k).smallBias.val = 3)
    (hnb : (phaseEpidemicUpdate L K (virtualLabels init ω t i)
        (virtualLabels init ω t j)).1.phase.val ≠ 10 ∧
      (phaseEpidemicUpdate L K (virtualLabels init ω t i)
        (virtualLabels init ω t j)).2.phase.val ≠ 10)
    (hroles : ∀ k, (virtualLabels init ω (t + 1) k).role = (virtualLabels init ω t k).role)
    (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (hcap : ℓ ≤ K * (L + 1)) :
    frontCount (virtualLabels init ω (t + 1)) ℓ =
      frontCount (virtualLabels init ω t) ℓ +
        if GatedTick ℓ (virtualLabels init ω t) i j then 1 else 0 := by
  have hij := (labelsAt_selected_transition init ω t i j hd).1
  rw [virtualLabels_succ, hd] at hroles ⊢
  exact frontCount_ruleUpdate_regime _ hK i j hij hreg hclk hnb hroles ℓ hℓ hcap

/-! ## Bridge to the reviewed event specification -/

theorem stageEvent_frontCount_eq {n : ℕ} (init : InputCfg n) (ω : InputLog n) (S v ℓ : ℕ)
    (hroles : ∀ i, (labelsAt init ω v i).role = (labelsAt init ω S i).role) :
    StageEventSpec.frontCount init ω S v ℓ = frontCount (labelsAt init ω v) ℓ := by
  have heff : ∀ i, StageEventSpec.effectiveMinute init ω v i = effMinute (labelsAt init ω v i) := by
    intro i
    unfold StageEventSpec.effectiveMinute StageEventSpec.active effMinute
    split_ifs <;> first | rfl | (exfalso; omega)
  unfold StageEventSpec.frontCount StageEventSpec.labelCount frontCount aboveSet
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, StageEventSpec.fixedRole, heff, hroles]

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockEmbedding

end
