/-
Phase-10 backup invariants for the Doty et al. exact-majority protocol.

Phase 10 uses the `full` field as the active/passive flag.  Active A contributes
`+1`, active B contributes `-1`, and all other Phase-10 backup states contribute
`0`.  The local backup transition preserves this signed active sum.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Protocol.Transition
import Ripple.PopulationProtocol.Majority.ExactMajority.Analysis.Invariants

namespace ExactMajority

variable {L K : ℕ}

/-- Signed contribution of a single agent to the Phase-10 backup majority
invariant.  The `full` field is the active flag in Phase 10. -/
def signedContribution (a : AgentState L K) : ℤ :=
  if a.full then
    match a.output with
    | .A => 1
    | .B => -1
    | .T => 0
  else
    0

/-- Active signed sum for a configuration in the Phase-10 backup protocol. -/
def phase10ActiveSignedSum (c : Config (AgentState L K)) : ℤ :=
  (c.map signedContribution).sum

/-- An active Phase-10 `A` source. -/
def IsActiveA (a : AgentState L K) : Prop :=
  a.full = true ∧ a.output = .A

/-- An active Phase-10 `B` source. -/
def IsActiveB (a : AgentState L K) : Prop :=
  a.full = true ∧ a.output = .B

/-- An active Phase-10 tie source. -/
def IsActiveT (a : AgentState L K) : Prop :=
  a.full = true ∧ a.output = .T

instance decidablePred_isActiveA : DecidablePred (@IsActiveA L K) := by
  intro a
  unfold IsActiveA
  infer_instance

instance decidablePred_isActiveB : DecidablePred (@IsActiveB L K) := by
  intro a
  unfold IsActiveB
  infer_instance

instance decidablePred_isActiveT : DecidablePred (@IsActiveT L K) := by
  intro a
  unfold IsActiveT
  infer_instance

/-- Number of active `A` sources in a configuration. -/
def activeACount (c : Config (AgentState L K)) : ℕ :=
  c.countP IsActiveA

/-- Number of active `B` sources in a configuration. -/
def activeBCount (c : Config (AgentState L K)) : ℕ :=
  c.countP IsActiveB

/-- Number of active `T` sources in a configuration. -/
def activeTCount (c : Config (AgentState L K)) : ℕ :=
  c.countP IsActiveT

/-- Total number of active backup sources. -/
def activeCount (c : Config (AgentState L K)) : ℕ :=
  c.countP (fun a => a.full = true)

/-- Number of agents whose current output is not `A`. -/
def wrongACount (c : Config (AgentState L K)) : ℕ :=
  c.countP (fun a => a.output ≠ .A)

/-- Number of agents whose current output is not `B`. -/
def wrongBCount (c : Config (AgentState L K)) : ℕ :=
  c.countP (fun a => a.output ≠ .B)

/-- Number of agents whose current output is not `T`. -/
def wrongTCount (c : Config (AgentState L K)) : ℕ :=
  c.countP (fun a => a.output ≠ .T)

/-- The configuration contains at least one active backup source. -/
def hasActiveAgent (c : Config (AgentState L K)) : Prop :=
  ∃ a ∈ c, a.full = true

theorem hasActiveAgent_iff_activeCount_pos
    (c : Config (AgentState L K)) :
    hasActiveAgent c ↔ 0 < activeCount c := by
  simp [hasActiveAgent, activeCount, Multiset.countP_pos]

theorem phase10ActiveSignedSum_eq_activeACount_sub_activeBCount
    (c : Config (AgentState L K)) :
    phase10ActiveSignedSum c = (activeACount c : ℤ) - (activeBCount c : ℤ) := by
  induction c using Multiset.induction_on with
  | empty =>
      simp [phase10ActiveSignedSum, activeACount, activeBCount]
  | cons a c ih =>
      simp only [phase10ActiveSignedSum, Multiset.map_cons, Multiset.sum_cons]
      change signedContribution a + phase10ActiveSignedSum c =
        (activeACount (a ::ₘ c) : ℤ) - (activeBCount (a ::ₘ c) : ℤ)
      rw [ih]
      rcases a with
        ⟨ainput, aoutput, aphase, arole, aassigned, abias, asmallBias,
          ahour, aminute, afull, aopinions, acounter⟩
      cases aoutput <;> cases afull <;>
        simp [activeACount, activeBCount, IsActiveA, IsActiveB, signedContribution]
        <;> omega

theorem exists_activeA_of_phase10ActiveSignedSum_pos
    (c : Config (AgentState L K))
    (hpos : 0 < phase10ActiveSignedSum c) :
    ∃ a ∈ c, IsActiveA a := by
  have hcount : 0 < activeACount c := by
    rw [phase10ActiveSignedSum_eq_activeACount_sub_activeBCount] at hpos
    omega
  simpa [activeACount] using (Multiset.countP_pos.1 hcount :
    ∃ a ∈ c, IsActiveA a)

theorem exists_activeB_of_phase10ActiveSignedSum_neg
    (c : Config (AgentState L K))
    (hneg : phase10ActiveSignedSum c < 0) :
    ∃ a ∈ c, IsActiveB a := by
  have hcount : 0 < activeBCount c := by
    rw [phase10ActiveSignedSum_eq_activeACount_sub_activeBCount] at hneg
    omega
  simpa [activeBCount] using (Multiset.countP_pos.1 hcount :
    ∃ a ∈ c, IsActiveB a)

set_option linter.flexible false in
theorem active_of_no_activeA_no_activeB_is_activeT
    (c : Config (AgentState L K))
    (hA : activeACount c = 0) (hB : activeBCount c = 0)
    {a : AgentState L K} (ha : a ∈ c) (hfull : a.full = true) :
    IsActiveT a := by
  have hnotA : ¬ IsActiveA a := by
    exact (Multiset.countP_eq_zero.1 (by simpa [activeACount] using hA)) a ha
  have hnotB : ¬ IsActiveB a := by
    exact (Multiset.countP_eq_zero.1 (by simpa [activeBCount] using hB)) a ha
  rcases a with
    ⟨ainput, aoutput, aphase, arole, aassigned, abias, asmallBias,
      ahour, aminute, afull, aopinions, acounter⟩
  cases aoutput <;> simp [IsActiveA, IsActiveB, IsActiveT] at hfull hnotA hnotB ⊢
  · rw [hfull] at hnotA
    simp at hnotA
  · rw [hfull] at hnotB
    simp at hnotB
  · exact hfull

theorem exists_activeT_of_hasActive_no_activeA_no_activeB
    (c : Config (AgentState L K))
    (hactive : hasActiveAgent c)
    (hA : activeACount c = 0) (hB : activeBCount c = 0) :
    ∃ a ∈ c, IsActiveT a := by
  rcases hactive with ⟨a, ha, hfull⟩
  exact ⟨a, ha, active_of_no_activeA_no_activeB_is_activeT
    (L := L) (K := K) c hA hB ha hfull⟩

/-- Hybrid signal used before the whole population has entered Phase 10:
lower-phase agents contribute their immutable input, while Phase-10 agents
contribute the active backup signed value. -/
def backupContribution (a : AgentState L K) : ℤ :=
  if a.phase.val = 10 then signedContribution a else AgentState.inputBiasInt a

/-- Sum of the hybrid backup signal over a configuration. -/
def backupSignal (c : Config (AgentState L K)) : ℤ :=
  (c.map backupContribution).sum

theorem backupContribution_of_phase_ne_10
    (a : AgentState L K) (hphase : a.phase.val ≠ 10) :
    backupContribution a = AgentState.inputBiasInt a := by
  simp [backupContribution, hphase]

theorem backupContribution_of_phase_10
    (a : AgentState L K) (hphase : a.phase.val = 10) :
    backupContribution a = signedContribution a := by
  simp [backupContribution, hphase]

theorem backupSignal_of_all_phase10
    (c : Config (AgentState L K))
    (hphase : ∀ a ∈ c, a.phase.val = 10) :
    backupSignal c = phase10ActiveSignedSum c := by
  induction c using Multiset.induction_on with
  | empty =>
      simp [backupSignal, phase10ActiveSignedSum]
  | cons a c ih =>
      have ha : a.phase.val = 10 := hphase a (by simp)
      have hc : ∀ b ∈ c, b.phase.val = 10 := by
        intro b hb
        exact hphase b (by simp [hb])
      simp only [backupSignal, phase10ActiveSignedSum, Multiset.map_cons, Multiset.sum_cons]
      change backupContribution a + backupSignal c =
        signedContribution a + phase10ActiveSignedSum c
      rw [ih hc]
      simp [backupContribution, ha]

theorem backupSignal_initial_eq_initialGap
    (init : Config (AgentState L K)) (hinit : validInitial init) :
    backupSignal init = initialGap init := by
  rw [← inputBiasSum_initialGap (L := L) (K := K) init]
  induction init using Multiset.induction_on with
  | empty =>
      simp [backupSignal, inputBiasSum]
  | cons a c ih =>
      have ha0 : a.phase.val ≠ 10 := by
        have ha := (hinit a (by simp)).1
        intro h10
        have hval : a.phase.val = 0 := by
          rw [ha]
        omega
      have hcinit : validInitial c := by
        intro b hb
        exact hinit b (by simp [hb])
      simp only [backupSignal, inputBiasSum, Multiset.map_cons, Multiset.sum_cons]
      change backupContribution a + backupSignal c =
        AgentState.inputBiasInt a + inputBiasSum c
      rw [ih hcinit]
      simp [backupContribution, ha0]

theorem signedContribution_enterPhase10
    (a : AgentState L K) :
    signedContribution (enterPhase10 L K a) = AgentState.inputBiasInt a := by
  rcases a with
    ⟨ainput, aoutput, aphase, arole, aassigned, abias, asmallBias,
      ahour, aminute, afull, aopinions, acounter⟩
  cases ainput <;> simp [signedContribution, enterPhase10, AgentState.inputBiasInt]

theorem backupContribution_finishPhase10Entry_of_input_phase_nondec
    (before after : AgentState L K)
    (hinput : after.input = before.input)
    (hmono : before.phase.val ≤ after.phase.val) :
    backupContribution (finishPhase10Entry L K before after) =
      if before.phase.val = 10 then signedContribution after
      else AgentState.inputBiasInt before := by
  by_cases hbefore10 : before.phase.val = 10
  · have hafter10 : after.phase.val = 10 := by
      have hle : after.phase.val ≤ 10 := by
        have hlt := after.phase.2
        omega
      omega
    have hbefore_not_lt : ¬ before.phase.val < 10 := by omega
    simp [finishPhase10Entry, canonicalPhase10Entry, backupContribution,
      hbefore10, hafter10]
  · have hbefore_lt : before.phase.val < 10 := by
      have hle : before.phase.val ≤ 10 := by
        have hlt := before.phase.2
        omega
      omega
    by_cases hafter10 : after.phase.val = 10
    · simp [finishPhase10Entry, canonicalPhase10Entry, hbefore_lt, hafter10,
        backupContribution, signedContribution_enterPhase10, hinput, hbefore10,
        AgentState.inputBiasInt]
    · simp [finishPhase10Entry, canonicalPhase10Entry, hafter10,
        backupContribution, hbefore10, hinput, AgentState.inputBiasInt]

private lemma phaseInit_input_preserved_local
    (p : Fin 11) (a : AgentState L K) :
    (phaseInit L K p a).input = a.input := by
  rcases p with ⟨n, hn⟩
  match n, hn with
  | 0, _ => unfold phaseInit; simp
  | 1, _ => unfold phaseInit; simp; split_ifs <;> rfl
  | 2, _ => unfold phaseInit; simp; split_ifs <;> rfl
  | 3, _ => unfold phaseInit; simp; cases a.role <;> rfl
  | 4, _ => unfold phaseInit; simp
  | 5, _ => unfold phaseInit; simp; split_ifs <;> rfl
  | 6, _ => unfold phaseInit; simp; split_ifs <;> rfl
  | 7, _ => unfold phaseInit; simp; split_ifs <;> rfl
  | 8, _ => unfold phaseInit; simp
  | 9, _ => unfold phaseInit; simp; split_ifs <;> rfl
  | 10, _ => unfold phaseInit; simp
  | n + 11, _ => omega

set_option linter.flexible false in
private lemma runInitsBetween_input_preserved_local
    (oldP newP : ℕ) (a : AgentState L K) :
    (runInitsBetween L K oldP newP a).input = a.input := by
  unfold runInitsBetween
  let lst := (List.range 11).filter (fun k => oldP < k ∧ k ≤ newP)
  have h_ind : ∀ (a' : AgentState L K),
      (lst.foldl (fun (acc : AgentState L K) (k : ℕ) =>
        if h : k < 11 then phaseInit L K ⟨k, h⟩ acc else acc) a').input = a'.input := by
    induction lst with
    | nil => intro a'; rfl
    | cons k l IH =>
      intro a'
      simp [List.foldl]
      by_cases hk : k < 11
      · simp [hk]
        calc
          (l.foldl
              (fun (acc : AgentState L K) (k : ℕ) =>
                if h : k < 11 then phaseInit L K ⟨k, h⟩ acc else acc)
              (phaseInit L K ⟨k, hk⟩ a')).input =
              (phaseInit L K ⟨k, hk⟩ a').input := IH _
          _ = a'.input := phaseInit_input_preserved_local (L := L) (K := K) _ _
      · simp [hk]
        exact IH a'
  exact h_ind a

private lemma runInitsBetween_self_eq
    (n : ℕ) (a : AgentState L K) :
    runInitsBetween L K n n a = a := by
  unfold runInitsBetween
  have hfilter :
      (List.range 11).filter (fun k => decide (n < k) && decide (k ≤ n)) = [] := by
    apply List.eq_nil_iff_forall_not_mem.2
    intro k hk
    simp at hk
    omega
  simp [hfilter]

private lemma backupContribution_phase10EpidemicEntry_of_before_lt_10
    (before after : AgentState L K)
    (hbefore : before.phase.val < 10)
    (hinput : after.input = before.input) :
    backupContribution (phase10EpidemicEntry L K before after) =
      AgentState.inputBiasInt before := by
  rw [show phase10EpidemicEntry L K before after = enterPhase10 L K after by
    simp [phase10EpidemicEntry, hbefore]]
  simp [backupContribution, signedContribution_enterPhase10, hinput,
    AgentState.inputBiasInt]

private lemma max_phase_eq_left_of_left_phase10
    (s t : AgentState L K) (hs10 : s.phase.val = 10) :
    max s.phase t.phase = s.phase := by
  have hts : t.phase ≤ s.phase := by
    rw [Fin.le_iff_val_le_val]
    have ht_upper := t.phase.2
    omega
  exact max_eq_left hts

private lemma max_phase_eq_right_of_right_phase10
    (s t : AgentState L K) (ht10 : t.phase.val = 10) :
    max s.phase t.phase = t.phase := by
  have hst : s.phase ≤ t.phase := by
    rw [Fin.le_iff_val_le_val]
    have hs_upper := s.phase.2
    omega
  exact max_eq_right hst

private theorem phaseEpidemicUpdate_preserves_backupContribution_pair
    (s t : AgentState L K) :
    backupContribution (phaseEpidemicUpdate L K s t).1 +
        backupContribution (phaseEpidemicUpdate L K s t).2 =
      backupContribution s + backupContribution t := by
  unfold phaseEpidemicUpdate
  dsimp
  set p := max s.phase t.phase with hp
  generalize hs0 :
      runInitsBetween L K s.phase.val p.val ({ s with phase := p }) = s0
  generalize ht0 :
      runInitsBetween L K t.phase.val p.val ({ t with phase := p }) = t0
  have hs0_input : s0.input = s.input := by
    calc
      s0.input =
          (runInitsBetween L K s.phase.val p.val ({ s with phase := p })).input := by rw [hs0]
      _ = ({ s with phase := p } : AgentState L K).input :=
        runInitsBetween_input_preserved_local (L := L) (K := K) _ _ _
      _ = s.input := by simp
  have ht0_input : t0.input = t.input := by
    calc
      t0.input =
          (runInitsBetween L K t.phase.val p.val ({ t with phase := p })).input := by rw [ht0]
      _ = ({ t with phase := p } : AgentState L K).input :=
        runInitsBetween_input_preserved_local (L := L) (K := K) _ _ _
      _ = t.input := by simp
  have hs0_eq_of_s10 (hs10 : s.phase.val = 10) : s0 = s := by
    have hp_eq : p = s.phase := by
      rw [hp]
      exact max_phase_eq_left_of_left_phase10 (L := L) (K := K) s t hs10
    calc
      s0 = runInitsBetween L K s.phase.val p.val ({ s with phase := p }) := by
        rw [hs0]
      _ = runInitsBetween L K s.phase.val s.phase.val s := by
        rw [hp_eq]
      _ = s := runInitsBetween_self_eq (L := L) (K := K) s.phase.val s
  have ht0_eq_of_t10 (ht10 : t.phase.val = 10) : t0 = t := by
    have hp_eq : p = t.phase := by
      rw [hp]
      exact max_phase_eq_right_of_right_phase10 (L := L) (K := K) s t ht10
    calc
      t0 = runInitsBetween L K t.phase.val p.val ({ t with phase := p }) := by
        rw [ht0]
      _ = runInitsBetween L K t.phase.val t.phase.val t := by
        rw [hp_eq]
      _ = t := runInitsBetween_self_eq (L := L) (K := K) t.phase.val t
  by_cases h10 :
      (s.phase.val < 10 ∨ t.phase.val < 10) ∧
        (s0.phase.val = 10 ∨ t0.phase.val = 10)
  · have hs_contrib :
        backupContribution (phase10EpidemicEntry L K s s0) =
          backupContribution s := by
      by_cases hs_lt : s.phase.val < 10
      · have hs_ne : s.phase.val ≠ 10 := by omega
        rw [backupContribution_phase10EpidemicEntry_of_before_lt_10
          (L := L) (K := K) s s0 hs_lt hs0_input]
        simp [backupContribution, hs_ne]
      · have hs10 : s.phase.val = 10 := by
          have hs_upper := s.phase.2
          omega
        have hs0_eq := hs0_eq_of_s10 hs10
        simp [phase10EpidemicEntry, hs_lt, hs0_eq]
    have ht_contrib :
        backupContribution (phase10EpidemicEntry L K t t0) =
          backupContribution t := by
      by_cases ht_lt : t.phase.val < 10
      · have ht_ne : t.phase.val ≠ 10 := by omega
        rw [backupContribution_phase10EpidemicEntry_of_before_lt_10
          (L := L) (K := K) t t0 ht_lt ht0_input]
        simp [backupContribution, ht_ne]
      · have ht10 : t.phase.val = 10 := by
          have ht_upper := t.phase.2
          omega
        have ht0_eq := ht0_eq_of_t10 ht10
        simp [phase10EpidemicEntry, ht_lt, ht0_eq]
    simp [h10, hs_contrib, ht_contrib]
  · have hs_contrib : backupContribution s0 = backupContribution s := by
      by_cases hs10 : s.phase.val = 10
      · rw [hs0_eq_of_s10 hs10]
      · have hs_lt : s.phase.val < 10 := by
          have hs_upper := s.phase.2
          omega
        have hs0_ne : s0.phase.val ≠ 10 := by
          intro hs0_10
          exact h10 ⟨Or.inl hs_lt, Or.inl hs0_10⟩
        simp [backupContribution, hs10, hs0_ne, hs0_input, AgentState.inputBiasInt]
    have ht_contrib : backupContribution t0 = backupContribution t := by
      by_cases ht10 : t.phase.val = 10
      · rw [ht0_eq_of_t10 ht10]
      · have ht_lt : t.phase.val < 10 := by
          have ht_upper := t.phase.2
          omega
        have ht0_ne : t0.phase.val ≠ 10 := by
          intro ht0_10
          exact h10 ⟨Or.inr ht_lt, Or.inr ht0_10⟩
        simp [backupContribution, ht10, ht0_ne, ht0_input, AgentState.inputBiasInt]
    simp [h10, hs_contrib, ht_contrib]

set_option linter.flexible false in
private theorem phaseEpidemicUpdate_phase10_sync
    (s t : AgentState L K) :
    (phaseEpidemicUpdate L K s t).1.phase.val = 10 ↔
      (phaseEpidemicUpdate L K s t).2.phase.val = 10 := by
  unfold phaseEpidemicUpdate
  dsimp
  set p := max s.phase t.phase with hp
  generalize hs0 :
      runInitsBetween L K s.phase.val p.val ({ s with phase := p }) = s0
  generalize ht0 :
      runInitsBetween L K t.phase.val p.val ({ t with phase := p }) = t0
  have hs0_eq_of_s10 (hs10 : s.phase.val = 10) : s0 = s := by
    have hp_eq : p = s.phase := by
      rw [hp]
      exact max_phase_eq_left_of_left_phase10 (L := L) (K := K) s t hs10
    calc
      s0 = runInitsBetween L K s.phase.val p.val ({ s with phase := p }) := by
        rw [hs0]
      _ = runInitsBetween L K s.phase.val s.phase.val s := by
        rw [hp_eq]
      _ = s := runInitsBetween_self_eq (L := L) (K := K) s.phase.val s
  have ht0_eq_of_t10 (ht10 : t.phase.val = 10) : t0 = t := by
    have hp_eq : p = t.phase := by
      rw [hp]
      exact max_phase_eq_right_of_right_phase10 (L := L) (K := K) s t ht10
    calc
      t0 = runInitsBetween L K t.phase.val p.val ({ t with phase := p }) := by
        rw [ht0]
      _ = runInitsBetween L K t.phase.val t.phase.val t := by
        rw [hp_eq]
      _ = t := runInitsBetween_self_eq (L := L) (K := K) t.phase.val t
  by_cases h10 :
      (s.phase.val < 10 ∨ t.phase.val < 10) ∧
        (s0.phase.val = 10 ∨ t0.phase.val = 10)
  · have hs_phase : (phase10EpidemicEntry L K s s0).phase.val = 10 := by
      by_cases hs_lt : s.phase.val < 10
      · simp [phase10EpidemicEntry, hs_lt]
      · have hs10 : s.phase.val = 10 := by
          have hs_upper := s.phase.2
          omega
        have hs0_eq := hs0_eq_of_s10 hs10
        simp [phase10EpidemicEntry, hs0_eq, hs10]
    have ht_phase : (phase10EpidemicEntry L K t t0).phase.val = 10 := by
      by_cases ht_lt : t.phase.val < 10
      · simp [phase10EpidemicEntry, ht_lt]
      · have ht10 : t.phase.val = 10 := by
          have ht_upper := t.phase.2
          omega
        have ht0_eq := ht0_eq_of_t10 ht10
        simp [phase10EpidemicEntry, ht0_eq, ht10]
    simp [h10, hs_phase, ht_phase]
  · simp [h10]
    constructor
    · intro hs0_10
      have hnot_lower : ¬ (s.phase.val < 10 ∨ t.phase.val < 10) := by
        intro hlower
        exact h10 ⟨hlower, Or.inl hs0_10⟩
      have ht_not_lt : ¬ t.phase.val < 10 := fun ht_lt => hnot_lower (Or.inr ht_lt)
      have ht10 : t.phase.val = 10 := by
        have ht_upper := t.phase.2
        omega
      rw [ht0_eq_of_t10 ht10]
      exact ht10
    · intro ht0_10
      have hnot_lower : ¬ (s.phase.val < 10 ∨ t.phase.val < 10) := by
        intro hlower
        exact h10 ⟨hlower, Or.inr ht0_10⟩
      have hs_not_lt : ¬ s.phase.val < 10 := fun hs_lt => hnot_lower (Or.inl hs_lt)
      have hs10 : s.phase.val = 10 := by
        have hs_upper := s.phase.2
        omega
      rw [hs0_eq_of_s10 hs10]
      exact hs10

private theorem dispatch_preserves_backupContribution_pair
    (s t : AgentState L K)
    (hsync : s.phase.val = 10 ↔ t.phase.val = 10) :
    let out :=
      match s.phase with
      | ⟨0, _⟩ => Phase0Transition L K s t
      | ⟨1, _⟩ => Phase1Transition L K s t
      | ⟨2, _⟩ => Phase2Transition L K s t
      | ⟨3, _⟩ => Phase3Transition L K s t
      | ⟨4, _⟩ => Phase4Transition L K s t
      | ⟨5, _⟩ => Phase5Transition L K s t
      | ⟨6, _⟩ => Phase6Transition L K s t
      | ⟨7, _⟩ => Phase7Transition L K s t
      | ⟨8, _⟩ => Phase8Transition L K s t
      | ⟨9, _⟩ => Phase9Transition L K s t
      | ⟨10, _⟩ => Phase10Transition L K s t
      | _ => (s, t)
    backupContribution (finishPhase10Entry L K s out.1) +
        backupContribution (finishPhase10Entry L K t out.2) =
      backupContribution s + backupContribution t := by
  let closePre10 (out : AgentState L K × AgentState L K)
      (hs_ne : s.phase.val ≠ 10)
      (ht_ne : t.phase.val ≠ 10)
      (hinput : out.1.input = s.input ∧ out.2.input = t.input)
      (hmono : s.phase.val ≤ out.1.phase.val ∧ t.phase.val ≤ out.2.phase.val) :
      backupContribution (finishPhase10Entry L K s out.1) +
          backupContribution (finishPhase10Entry L K t out.2) =
        backupContribution s + backupContribution t := by
    rw [backupContribution_finishPhase10Entry_of_input_phase_nondec
        (L := L) (K := K) s out.1 hinput.1 hmono.1,
      backupContribution_finishPhase10Entry_of_input_phase_nondec
        (L := L) (K := K) t out.2 hinput.2 hmono.2]
    simp [backupContribution, hs_ne, ht_ne]
  rcases hphase : s.phase with ⟨n, hn⟩
  match n, hn with
  | 0, _ =>
      have hs_ne : s.phase.val ≠ 10 := by simp [hphase]
      have ht_ne : t.phase.val ≠ 10 := by
        intro ht
        have hs10 := hsync.mpr ht
        simp [hphase] at hs10
      exact closePre10 (Phase0Transition L K s t) hs_ne ht_ne
        (Phase0Transition_input_preserved (L := L) (K := K) s t)
        (Phase0Transition_phase_nondec L K s t)
  | 1, _ =>
      have hs_ne : s.phase.val ≠ 10 := by simp [hphase]
      have ht_ne : t.phase.val ≠ 10 := by
        intro ht
        have hs10 := hsync.mpr ht
        simp [hphase] at hs10
      exact closePre10 (Phase1Transition L K s t) hs_ne ht_ne
        (Phase1Transition_input_preserved (L := L) (K := K) s t)
        (Phase1Transition_phase_nondec L K s t)
  | 2, _ =>
      have hs_ne : s.phase.val ≠ 10 := by simp [hphase]
      have ht_ne : t.phase.val ≠ 10 := by
        intro ht
        have hs10 := hsync.mpr ht
        simp [hphase] at hs10
      exact closePre10 (Phase2Transition L K s t) hs_ne ht_ne
        (Phase2Transition_input_preserved (L := L) (K := K) s t)
        (Phase2Transition_phase_nondec L K s t)
  | 3, _ =>
      have hs_ne : s.phase.val ≠ 10 := by simp [hphase]
      have ht_ne : t.phase.val ≠ 10 := by
        intro ht
        have hs10 := hsync.mpr ht
        simp [hphase] at hs10
      exact closePre10 (Phase3Transition L K s t) hs_ne ht_ne
        (Phase3Transition_input_preserved (L := L) (K := K) s t)
        (Phase3Transition_phase_nondec L K s t)
  | 4, _ =>
      have hs_ne : s.phase.val ≠ 10 := by simp [hphase]
      have ht_ne : t.phase.val ≠ 10 := by
        intro ht
        have hs10 := hsync.mpr ht
        simp [hphase] at hs10
      exact closePre10 (Phase4Transition L K s t) hs_ne ht_ne
        (Phase4Transition_input_preserved (L := L) (K := K) s t)
        (Phase4Transition_phase_nondec L K s t)
  | 5, _ =>
      have hs_ne : s.phase.val ≠ 10 := by simp [hphase]
      have ht_ne : t.phase.val ≠ 10 := by
        intro ht
        have hs10 := hsync.mpr ht
        simp [hphase] at hs10
      exact closePre10 (Phase5Transition L K s t) hs_ne ht_ne
        (Phase5Transition_input_preserved (L := L) (K := K) s t)
        (Phase5Transition_phase_nondec L K s t)
  | 6, _ =>
      have hs_ne : s.phase.val ≠ 10 := by simp [hphase]
      have ht_ne : t.phase.val ≠ 10 := by
        intro ht
        have hs10 := hsync.mpr ht
        simp [hphase] at hs10
      exact closePre10 (Phase6Transition L K s t) hs_ne ht_ne
        (Phase6Transition_input_preserved (L := L) (K := K) s t)
        (Phase6Transition_phase_nondec L K s t)
  | 7, _ =>
      have hs_ne : s.phase.val ≠ 10 := by simp [hphase]
      have ht_ne : t.phase.val ≠ 10 := by
        intro ht
        have hs10 := hsync.mpr ht
        simp [hphase] at hs10
      exact closePre10 (Phase7Transition L K s t) hs_ne ht_ne
        (Phase7Transition_input_preserved (L := L) (K := K) s t)
        (Phase7Transition_phase_nondec L K s t)
  | 8, _ =>
      have hs_ne : s.phase.val ≠ 10 := by simp [hphase]
      have ht_ne : t.phase.val ≠ 10 := by
        intro ht
        have hs10 := hsync.mpr ht
        simp [hphase] at hs10
      exact closePre10 (Phase8Transition L K s t) hs_ne ht_ne
        (Phase8Transition_input_preserved (L := L) (K := K) s t)
        (Phase8Transition_phase_nondec L K s t)
  | 9, _ =>
      have hs_ne : s.phase.val ≠ 10 := by simp [hphase]
      have ht_ne : t.phase.val ≠ 10 := by
        intro ht
        have hs10 := hsync.mpr ht
        simp [hphase] at hs10
      exact closePre10 (Phase9Transition L K s t) hs_ne ht_ne
        (Phase9Transition_input_preserved (L := L) (K := K) s t)
        (Phase9Transition_phase_nondec L K s t)
  | 10, _ =>
      have hs10 : s.phase.val = 10 := by simp [hphase]
      have ht10 : t.phase.val = 10 := hsync.mp hs10
      have hs_not_lt : ¬ s.phase.val < 10 := by omega
      have ht_not_lt : ¬ t.phase.val < 10 := by omega
      change
        backupContribution (finishPhase10Entry L K s (Phase10Transition L K s t).1) +
            backupContribution (finishPhase10Entry L K t (Phase10Transition L K s t).2) =
          backupContribution s + backupContribution t
      rw [finishPhase10Entry_eq_self_of_before_not_lt_10
          (L := L) (K := K) s (Phase10Transition L K s t).1 hs_not_lt,
        finishPhase10Entry_eq_self_of_before_not_lt_10
          (L := L) (K := K) t (Phase10Transition L K s t).2 ht_not_lt]
      have hpres :
          signedContribution (Phase10Transition L K s t).1 +
              signedContribution (Phase10Transition L K s t).2 =
            signedContribution s + signedContribution t := by
        rcases s with
          ⟨sinput, soutput, sphase, srole, sassigned, sbias, ssmallBias,
            shour, sminute, sfull, sopinions, scounter⟩
        rcases t with
          ⟨tinput, toutput, tphase, trole, tassigned, tbias, tsmallBias,
            thour, tminute, tfull, topinions, tcounter⟩
        cases soutput <;> cases toutput <;> cases sfull <;> cases tfull <;>
          simp [Phase10Transition, signedContribution]
      have hout_phase := Phase10Transition_phase_nondec (L := L) (K := K) s t
      have hout1_10 : (Phase10Transition L K s t).1.phase.val = 10 := by
        have hge : 10 ≤ (Phase10Transition L K s t).1.phase.val := by
          simpa [hs10] using hout_phase.1
        have hlt := (Phase10Transition L K s t).1.phase.2
        omega
      have hout2_10 : (Phase10Transition L K s t).2.phase.val = 10 := by
        have hge : 10 ≤ (Phase10Transition L K s t).2.phase.val := by
          simpa [ht10] using hout_phase.2
        have hlt := (Phase10Transition L K s t).2.phase.2
        omega
      simpa [backupContribution, hs10, ht10, hout1_10, hout2_10] using hpres
  | n + 11, hn => omega

/-- The actual Phase-10 pair transition preserves the active signed sum on the
interacting pair. -/
theorem phase10Transition_preserves_signedContribution
    (a b : AgentState L K) :
    signedContribution (Phase10Transition L K a b).1 +
        signedContribution (Phase10Transition L K a b).2 =
      signedContribution a + signedContribution b := by
  rcases a with
    ⟨ainput, aoutput, aphase, arole, aassigned, abias, asmallBias,
      ahour, aminute, afull, aopinions, acounter⟩
  rcases b with
    ⟨binput, boutput, bphase, brole, bassigned, bbias, bsmallBias,
      bhour, bminute, bfull, bopinions, bcounter⟩
  cases aoutput <;> cases boutput <;> cases afull <;> cases bfull <;>
    simp [Phase10Transition, signedContribution]

/-- A Phase-10 backup step, or the explicit no-op case used by scheduled
executions, preserves the active signed sum on the interacting pair. -/
theorem phase10_transition_preserves_signedSum
    (a b a' b' : AgentState L K)
    (_ha : a.phase.val = 10) (_hb : b.phase.val = 10)
    (htrans : (a', b') = Phase10Transition L K a b ∨ (a', b') = (a, b)) :
    signedContribution a' + signedContribution b' =
      signedContribution a + signedContribution b := by
  rcases htrans with htrans | htrans
  · have ha' : a' = (Phase10Transition L K a b).1 := congrArg Prod.fst htrans
    have hb' : b' = (Phase10Transition L K a b).2 := congrArg Prod.snd htrans
    rw [ha', hb']
    exact phase10Transition_preserves_signedContribution (L := L) (K := K) a b
  · have ha' : a' = a := congrArg Prod.fst htrans
    have hb' : b' = b := congrArg Prod.snd htrans
    rw [ha', hb']

theorem phase10EpidemicEntry_full_of_before_lt_10
    (before after : AgentState L K) (hbefore : before.phase.val < 10) :
    (phase10EpidemicEntry L K before after).full = true := by
  simp [phase10EpidemicEntry, hbefore]

/-- The final Phase-10 entry guard activates any lower-phase agent that is
first sent to Phase 10 by the phase-specific transition. -/
theorem finishPhase10Entry_full_of_before_lt_10_final_phase10
    (before after : AgentState L K)
    (hbefore : before.phase.val < 10)
    (hfinal : (finishPhase10Entry L K before after).phase.val = 10) :
    (finishPhase10Entry L K before after).full = true := by
  by_cases hafter : after.phase.val = 10
  · simp [finishPhase10Entry, canonicalPhase10Entry, hbefore, hafter]
  · rw [finishPhase10Entry_eq_self_of_after_ne_10 (L := L) (K := K)
      before after hafter] at hfinal
    exact False.elim (hafter hfinal)

/-- A lower-phase left participant that reaches Phase 10 during the epidemic
entry stage is active and has a biased (`A`/`B`) backup output. -/
theorem phaseEpidemicUpdate_left_active_biased_of_before_lt_10_phase10
    (s t : AgentState L K)
    (hs : s.phase.val < 10)
    (hphase : (phaseEpidemicUpdate L K s t).1.phase.val = 10) :
    (phaseEpidemicUpdate L K s t).1.full = true ∧
      ((phaseEpidemicUpdate L K s t).1.output = .A ∨
        (phaseEpidemicUpdate L K s t).1.output = .B) := by
  unfold phaseEpidemicUpdate at hphase ⊢
  by_cases h10 :
      (s.phase.val < 10 ∨ t.phase.val < 10) ∧
        ((runInitsBetween L K s.phase.val (max s.phase.val t.phase.val)
            ({ s with phase := max s.phase t.phase })).phase.val = 10 ∨
          (runInitsBetween L K t.phase.val (max s.phase.val t.phase.val)
            ({ t with phase := max s.phase t.phase })).phase.val = 10)
  · constructor
    · simp [h10, phase10EpidemicEntry, hs]
    · cases hinput :
          (runInitsBetween L K s.phase.val (max s.phase.val t.phase.val)
            ({ s with phase := max s.phase t.phase })).input <;>
        simp [h10, phase10EpidemicEntry, hs, enterPhase10, hinput]
  · have hs0_phase :
        (runInitsBetween L K s.phase.val (max s.phase.val t.phase.val)
          ({ s with phase := max s.phase t.phase })).phase.val = 10 := by
      simpa [h10] using hphase
    exact False.elim (h10 ⟨Or.inl hs, Or.inl hs0_phase⟩)

/-- A lower-phase right participant that reaches Phase 10 during the epidemic
entry stage is active and has a biased (`A`/`B`) backup output. -/
theorem phaseEpidemicUpdate_right_active_biased_of_before_lt_10_phase10
    (s t : AgentState L K)
    (ht : t.phase.val < 10)
    (hphase : (phaseEpidemicUpdate L K s t).2.phase.val = 10) :
    (phaseEpidemicUpdate L K s t).2.full = true ∧
      ((phaseEpidemicUpdate L K s t).2.output = .A ∨
        (phaseEpidemicUpdate L K s t).2.output = .B) := by
  unfold phaseEpidemicUpdate at hphase ⊢
  by_cases h10 :
      (s.phase.val < 10 ∨ t.phase.val < 10) ∧
        ((runInitsBetween L K s.phase.val (max s.phase.val t.phase.val)
            ({ s with phase := max s.phase t.phase })).phase.val = 10 ∨
          (runInitsBetween L K t.phase.val (max s.phase.val t.phase.val)
            ({ t with phase := max s.phase t.phase })).phase.val = 10)
  · constructor
    · simp [h10, phase10EpidemicEntry, ht]
    · cases hinput :
          (runInitsBetween L K t.phase.val (max s.phase.val t.phase.val)
            ({ t with phase := max s.phase t.phase })).input <;>
        simp [h10, phase10EpidemicEntry, ht, enterPhase10, hinput]
  · have ht0_phase :
        (runInitsBetween L K t.phase.val (max s.phase.val t.phase.val)
          ({ t with phase := max s.phase t.phase })).phase.val = 10 := by
      simpa [h10] using hphase
    exact False.elim (h10 ⟨Or.inr ht, Or.inr ht0_phase⟩)

/-- The local Phase-10 backup rule never destroys the last active source among
the interacting pair. -/
theorem Phase10Transition_preserves_pair_hasActive
    (a b : AgentState L K)
    (hactive : a.full = true ∨ b.full = true) :
    (Phase10Transition L K a b).1.full = true ∨
      (Phase10Transition L K a b).2.full = true := by
  rcases a with
    ⟨ainput, aoutput, aphase, arole, aassigned, abias, asmallBias,
      ahour, aminute, afull, aopinions, acounter⟩
  rcases b with
    ⟨binput, boutput, bphase, brole, bassigned, bbias, bsmallBias,
      bhour, bminute, bfull, bopinions, bcounter⟩
  cases aoutput <;> cases boutput <;> cases afull <;> cases bfull <;>
    simp [Phase10Transition] at hactive ⊢

/-- An active biased left source (`A` or `B`) remains active after a Phase-10
backup interaction. -/
theorem Phase10Transition_left_full_of_active_biased
    (a b : AgentState L K)
    (ha_full : a.full = true)
    (ha_out : a.output = .A ∨ a.output = .B) :
    (Phase10Transition L K a b).1.full = true := by
  rcases a with
    ⟨ainput, aoutput, aphase, arole, aassigned, abias, asmallBias,
      ahour, aminute, afull, aopinions, acounter⟩
  rcases b with
    ⟨binput, boutput, bphase, brole, bassigned, bbias, bsmallBias,
      bhour, bminute, bfull, bopinions, bcounter⟩
  cases aoutput <;> cases boutput <;> cases afull <;> cases bfull <;>
    simp [Phase10Transition] at ha_full ha_out ⊢

/-- An active biased right source (`A` or `B`) remains active after a Phase-10
backup interaction. -/
theorem Phase10Transition_right_full_of_active_biased
    (a b : AgentState L K)
    (hb_full : b.full = true)
    (hb_out : b.output = .A ∨ b.output = .B) :
    (Phase10Transition L K a b).2.full = true := by
  rcases a with
    ⟨ainput, aoutput, aphase, arole, aassigned, abias, asmallBias,
      ahour, aminute, afull, aopinions, acounter⟩
  rcases b with
    ⟨binput, boutput, bphase, brole, bassigned, bbias, bsmallBias,
      bhour, bminute, bfull, bopinions, bcounter⟩
  cases aoutput <;> cases boutput <;> cases afull <;> cases bfull <;>
    simp [Phase10Transition] at hb_full hb_out ⊢

/-- The full protocol transition preserves the hybrid backup contribution on
the interacting pair.  Before Phase 10 this contribution is the immutable input
gap; after Phase 10 it is the active signed backup value. -/
theorem Transition_preserves_backupContribution_pair
    (a b : AgentState L K) :
    backupContribution (Transition L K a b).1 +
        backupContribution (Transition L K a b).2 =
      backupContribution a + backupContribution b := by
  unfold Transition
  rcases hpe : phaseEpidemicUpdate L K a b with ⟨s, t⟩
  have hep :=
    phaseEpidemicUpdate_preserves_backupContribution_pair (L := L) (K := K) a b
  have hsync := phaseEpidemicUpdate_phase10_sync (L := L) (K := K) a b
  simp only [hpe] at hep hsync ⊢
  let out :=
    match s.phase with
    | ⟨0, _⟩ => Phase0Transition L K s t
    | ⟨1, _⟩ => Phase1Transition L K s t
    | ⟨2, _⟩ => Phase2Transition L K s t
    | ⟨3, _⟩ => Phase3Transition L K s t
    | ⟨4, _⟩ => Phase4Transition L K s t
    | ⟨5, _⟩ => Phase5Transition L K s t
    | ⟨6, _⟩ => Phase6Transition L K s t
    | ⟨7, _⟩ => Phase7Transition L K s t
    | ⟨8, _⟩ => Phase8Transition L K s t
    | ⟨9, _⟩ => Phase9Transition L K s t
    | ⟨10, _⟩ => Phase10Transition L K s t
    | _ => (s, t)
  change
    backupContribution (finishPhase10Entry L K s out.1) +
        backupContribution (finishPhase10Entry L K t out.2) =
      backupContribution a + backupContribution b
  calc
    backupContribution (finishPhase10Entry L K s out.1) +
        backupContribution (finishPhase10Entry L K t out.2) =
        backupContribution s + backupContribution t := by
      exact dispatch_preserves_backupContribution_pair (L := L) (K := K) s t hsync
    _ = backupContribution a + backupContribution b := hep

/-- The hybrid backup signal is invariant along all reachable executions. -/
theorem backupSignal_reachable_eq
    (c c' : Config (AgentState L K))
    (hreach : (NonuniformMajority L K).Reachable c c') :
    backupSignal c' = backupSignal c := by
  simpa [backupSignal, Config.sumOf, NonuniformMajority] using
    Protocol.reachable_sumOf_eq
      (P := NonuniformMajority L K)
      (f := backupContribution)
      (hδ := fun r₁ r₂ =>
        Transition_preserves_backupContribution_pair (L := L) (K := K) r₁ r₂)
      hreach

/-- Once a reachable configuration is entirely in Phase 10, its active backup
signed sum is the initial input gap. -/
theorem phase10ActiveSignedSum_eq_initialGap_of_reachable
    (init c : Config (AgentState L K))
    (hinit : validInitial init)
    (hreach : (NonuniformMajority L K).Reachable init c)
    (hphase10 : ∀ a ∈ c, a.phase.val = 10) :
    phase10ActiveSignedSum c = initialGap init := by
  rw [← backupSignal_of_all_phase10 (L := L) (K := K) c hphase10]
  rw [backupSignal_reachable_eq (L := L) (K := K) init c hreach]
  exact backupSignal_initial_eq_initialGap (L := L) (K := K) init hinit

/-! ### Local Phase-10 schedule primitives -/

/-- Active A and active B cancel to two active T outputs. -/
theorem Phase10Transition_activeA_activeB_outputs_T
    (a b : AgentState L K)
    (ha_full : a.full = true) (hb_full : b.full = true)
    (ha_out : a.output = .A) (hb_out : b.output = .B) :
    (Phase10Transition L K a b).1.output = .T ∧
      (Phase10Transition L K a b).2.output = .T ∧
      (Phase10Transition L K a b).1.full = true ∧
      (Phase10Transition L K a b).2.full = true := by
  rcases a with
    ⟨ainput, aoutput, aphase, arole, aassigned, abias, asmallBias,
      ahour, aminute, afull, aopinions, acounter⟩
  rcases b with
    ⟨binput, boutput, bphase, brole, bassigned, bbias, bsmallBias,
      bhour, bminute, bfull, bopinions, bcounter⟩
  cases aoutput <;> cases boutput <;> cases afull <;> cases bfull <;>
    simp [Phase10Transition] at ha_full hb_full ha_out hb_out ⊢

/-- Active B and active A cancel to two active T outputs. -/
theorem Phase10Transition_activeB_activeA_outputs_T
    (a b : AgentState L K)
    (ha_full : a.full = true) (hb_full : b.full = true)
    (ha_out : a.output = .B) (hb_out : b.output = .A) :
    (Phase10Transition L K a b).1.output = .T ∧
      (Phase10Transition L K a b).2.output = .T ∧
      (Phase10Transition L K a b).1.full = true ∧
      (Phase10Transition L K a b).2.full = true := by
  rcases a with
    ⟨ainput, aoutput, aphase, arole, aassigned, abias, asmallBias,
      ahour, aminute, afull, aopinions, acounter⟩
  rcases b with
    ⟨binput, boutput, bphase, brole, bassigned, bbias, bsmallBias,
      bhour, bminute, bfull, bopinions, bcounter⟩
  cases aoutput <;> cases boutput <;> cases afull <;> cases bfull <;>
    simp [Phase10Transition] at ha_full hb_full ha_out hb_out ⊢

/-- An active A converts any partner except an active B to output A. -/
theorem Phase10Transition_activeA_nonActiveB_outputs_A
    (a b : AgentState L K)
    (ha_full : a.full = true) (ha_out : a.output = .A)
    (hb_not_activeB : ¬ (b.full = true ∧ b.output = .B)) :
    (Phase10Transition L K a b).1.output = .A ∧
      (Phase10Transition L K a b).2.output = .A := by
  rcases a with
    ⟨ainput, aoutput, aphase, arole, aassigned, abias, asmallBias,
      ahour, aminute, afull, aopinions, acounter⟩
  rcases b with
    ⟨binput, boutput, bphase, brole, bassigned, bbias, bsmallBias,
      bhour, bminute, bfull, bopinions, bcounter⟩
  cases aoutput <;> cases boutput <;> cases afull <;> cases bfull <;>
    simp [Phase10Transition] at ha_full ha_out hb_not_activeB ⊢

/-- An active A remains active A when it interacts with a non-active-B
partner. -/
theorem Phase10Transition_activeA_nonActiveB_left_activeA
    (a b : AgentState L K)
    (ha_full : a.full = true) (ha_out : a.output = .A)
    (hb_not_activeB : ¬ (b.full = true ∧ b.output = .B)) :
    (Phase10Transition L K a b).1.full = true ∧
      (Phase10Transition L K a b).1.output = .A := by
  rcases a with
    ⟨ainput, aoutput, aphase, arole, aassigned, abias, asmallBias,
      ahour, aminute, afull, aopinions, acounter⟩
  rcases b with
    ⟨binput, boutput, bphase, brole, bassigned, bbias, bsmallBias,
      bhour, bminute, bfull, bopinions, bcounter⟩
  cases aoutput <;> cases boutput <;> cases afull <;> cases bfull <;>
    simp [Phase10Transition] at ha_full ha_out hb_not_activeB ⊢

/-- An active B converts any partner except an active A to output B. -/
theorem Phase10Transition_activeB_nonActiveA_outputs_B
    (a b : AgentState L K)
    (ha_full : a.full = true) (ha_out : a.output = .B)
    (hb_not_activeA : ¬ (b.full = true ∧ b.output = .A)) :
    (Phase10Transition L K a b).1.output = .B ∧
      (Phase10Transition L K a b).2.output = .B := by
  rcases a with
    ⟨ainput, aoutput, aphase, arole, aassigned, abias, asmallBias,
      ahour, aminute, afull, aopinions, acounter⟩
  rcases b with
    ⟨binput, boutput, bphase, brole, bassigned, bbias, bsmallBias,
      bhour, bminute, bfull, bopinions, bcounter⟩
  cases aoutput <;> cases boutput <;> cases afull <;> cases bfull <;>
    simp [Phase10Transition] at ha_full ha_out hb_not_activeA ⊢

/-- An active B remains active B when it interacts with a non-active-A
partner. -/
theorem Phase10Transition_activeB_nonActiveA_left_activeB
    (a b : AgentState L K)
    (ha_full : a.full = true) (ha_out : a.output = .B)
    (hb_not_activeA : ¬ (b.full = true ∧ b.output = .A)) :
    (Phase10Transition L K a b).1.full = true ∧
      (Phase10Transition L K a b).1.output = .B := by
  rcases a with
    ⟨ainput, aoutput, aphase, arole, aassigned, abias, asmallBias,
      ahour, aminute, afull, aopinions, acounter⟩
  rcases b with
    ⟨binput, boutput, bphase, brole, bassigned, bbias, bsmallBias,
      bhour, bminute, bfull, bopinions, bcounter⟩
  cases aoutput <;> cases boutput <;> cases afull <;> cases bfull <;>
    simp [Phase10Transition] at ha_full ha_out hb_not_activeA ⊢

/-- In the tie case, an active T converts any partner that is not active A/B to
output T. -/
theorem Phase10Transition_activeT_noActiveBiased_outputs_T
    (a b : AgentState L K)
    (ha_full : a.full = true) (ha_out : a.output = .T)
    (hb_not_active_biased :
      ¬ (b.full = true ∧ (b.output = .A ∨ b.output = .B))) :
    (Phase10Transition L K a b).1.output = .T ∧
      (Phase10Transition L K a b).2.output = .T := by
  rcases a with
    ⟨ainput, aoutput, aphase, arole, aassigned, abias, asmallBias,
      ahour, aminute, afull, aopinions, acounter⟩
  rcases b with
    ⟨binput, boutput, bphase, brole, bassigned, bbias, bsmallBias,
      bhour, bminute, bfull, bopinions, bcounter⟩
  cases aoutput <;> cases boutput <;> cases afull <;> cases bfull <;>
    simp [Phase10Transition] at ha_full ha_out hb_not_active_biased ⊢

/-- An active T remains active T when it interacts with a partner that is not
active A/B. -/
theorem Phase10Transition_activeT_noActiveBiased_left_activeT
    (a b : AgentState L K)
    (ha_full : a.full = true) (ha_out : a.output = .T)
    (hb_not_active_biased :
      ¬ (b.full = true ∧ (b.output = .A ∨ b.output = .B))) :
    (Phase10Transition L K a b).1.full = true ∧
      (Phase10Transition L K a b).1.output = .T := by
  rcases a with
    ⟨ainput, aoutput, aphase, arole, aassigned, abias, asmallBias,
      ahour, aminute, afull, aopinions, acounter⟩
  rcases b with
    ⟨binput, boutput, bphase, brole, bassigned, bbias, bsmallBias,
      bhour, bminute, bfull, bopinions, bcounter⟩
  cases aoutput <;> cases boutput <;> cases afull <;> cases bfull <;>
    simp [Phase10Transition] at ha_full ha_out hb_not_active_biased ⊢

/-- If both inputs are already in Phase 10, the full dispatcher is exactly the
Phase-10 backup transition. -/
theorem Transition_eq_Phase10Transition_of_phase10
    (a b : AgentState L K)
    (ha : a.phase.val = 10) (hb : b.phase.val = 10) :
    Transition L K a b = Phase10Transition L K a b := by
  have ha_phase_eq : a.phase = phase10 := by
    apply Fin.ext
    simp [phase10, ha]
  have hb_phase_eq : b.phase = phase10 := by
    apply Fin.ext
    simp [phase10, hb]
  have hfilter10 :
      (List.range 11).filter (fun k => decide (10 < k) && decide (k ≤ 10)) = [] := by
    decide
  have ha_update : ({ a with phase := phase10 } : AgentState L K) = a := by
    rw [← ha_phase_eq]
  have hb_update : ({ b with phase := phase10 } : AgentState L K) = b := by
    rw [← hb_phase_eq]
  calc
    Transition L K a b =
        Phase10Transition L K ({ a with phase := phase10 }) ({ b with phase := phase10 }) := by
      simp [Transition, phaseEpidemicUpdate, runInitsBetween, ha_phase_eq,
        hb_phase_eq, phase10, hfilter10, finishPhase10Entry, canonicalPhase10Entry]
    _ = Phase10Transition L K a b := by
      rw [ha_update, hb_update]

private theorem pair_le_of_mem_ne
    {α : Type*} [DecidableEq α] {c : Multiset α} {a b : α}
    (ha : a ∈ c) (hb : b ∈ c) (hne : a ≠ b) :
    ({a, b} : Multiset α) ≤ c := by
  have hnot : a ∉ ({b} : Multiset α) := by
    simp [hne]
  change a ::ₘ ({b} : Multiset α) ≤ c
  rw [Multiset.cons_le_of_notMem hnot]
  exact ⟨ha, Multiset.singleton_le.2 hb⟩

private theorem reachable_step_of_mem_ne
    {c : Config (AgentState L K)} {a b : AgentState L K}
    (ha : a ∈ c) (hb : b ∈ c) (hne : a ≠ b) :
    (NonuniformMajority L K).Reachable c
      (c - ({a, b} : Multiset (AgentState L K)) +
        ({(Transition L K a b).1, (Transition L K a b).2} :
          Multiset (AgentState L K))) := by
  exact Relation.ReflTransGen.single
    ⟨a, b, pair_le_of_mem_ne ha hb hne, rfl⟩

private theorem ne_of_activeA_activeB
    {a b : AgentState L K} (ha : IsActiveA a) (hb : IsActiveB b) :
    a ≠ b := by
  intro h
  have : a.output = .B := by simpa [h] using hb.2
  simp [ha.2] at this

private theorem ne_of_activeA_wrongA
    {a b : AgentState L K} (ha : IsActiveA a) (hb : b.output ≠ .A) :
    a ≠ b := by
  intro h
  exact hb (by simpa [h] using ha.2)

private theorem ne_of_activeB_wrongB
    {a b : AgentState L K} (ha : IsActiveB a) (hb : b.output ≠ .B) :
    a ≠ b := by
  intro h
  exact hb (by simpa [h] using ha.2)

private theorem ne_of_activeT_wrongT
    {a b : AgentState L K} (ha : IsActiveT a) (hb : b.output ≠ .T) :
    a ≠ b := by
  intro h
  exact hb (by simpa [h] using ha.2)

private theorem activeBCount_cancel_A_B_lt
    (c : Config (AgentState L K)) {a b : AgentState L K}
    (hphase : ∀ x ∈ c, x.phase.val = 10)
    (ha_mem : a ∈ c) (hb_mem : b ∈ c)
    (ha : IsActiveA a) (hb : IsActiveB b) :
    activeBCount
        (c - ({a, b} : Multiset (AgentState L K)) +
          ({(Transition L K a b).1, (Transition L K a b).2} :
            Multiset (AgentState L K))) <
      activeBCount c := by
  have hne : a ≠ b := ne_of_activeA_activeB (L := L) (K := K) ha hb
  have happ : ({a, b} : Multiset (AgentState L K)) ≤ c :=
    pair_le_of_mem_ne ha_mem hb_mem hne
  have htransition :
      Transition L K a b = Phase10Transition L K a b :=
    Transition_eq_Phase10Transition_of_phase10
      (L := L) (K := K) a b (hphase a ha_mem) (hphase b hb_mem)
  have hpair_before :
      activeBCount ({a, b} : Multiset (AgentState L K)) = 1 := by
    change Multiset.countP IsActiveB ({a, b} : Multiset (AgentState L K)) = 1
    change Multiset.countP IsActiveB (a ::ₘ ({b} : Multiset (AgentState L K))) = 1
    rw [Multiset.countP_cons_of_neg]
    · change Multiset.countP IsActiveB (b ::ₘ (0 : Multiset (AgentState L K))) = 1
      rw [Multiset.countP_cons_of_pos]
      · simp
      · exact hb
    · intro hbad
      have : a.output = .B := hbad.2
      simp [ha.2] at this
  have hlocal :=
    Phase10Transition_activeA_activeB_outputs_T
      (L := L) (K := K) a b ha.1 hb.1 ha.2 hb.2
  have hpair_after :
      activeBCount
        ({(Transition L K a b).1, (Transition L K a b).2} :
          Multiset (AgentState L K)) = 0 := by
    rw [htransition]
    change Multiset.countP IsActiveB
      ({(Phase10Transition L K a b).1, (Phase10Transition L K a b).2} :
        Multiset (AgentState L K)) = 0
    rcases hlocal with ⟨h1out, h2out, h1full, h2full⟩
    change Multiset.countP IsActiveB
      ((Phase10Transition L K a b).1 ::ₘ
        ({(Phase10Transition L K a b).2} : Multiset (AgentState L K))) = 0
    rw [Multiset.countP_cons_of_neg]
    · change Multiset.countP IsActiveB
        ((Phase10Transition L K a b).2 ::ₘ
          (0 : Multiset (AgentState L K))) = 0
      rw [Multiset.countP_cons_of_neg]
      · simp
      · intro hbad
        have : (Phase10Transition L K a b).2.output = .B := hbad.2
        simp [h2out] at this
    · intro hbad
      have : (Phase10Transition L K a b).1.output = .B := hbad.2
      simp [h1out] at this
  have hres :
      activeBCount (c - ({a, b} : Multiset (AgentState L K))) =
        activeBCount c - 1 := by
    have hsub := Multiset.countP_sub
      (s := c) (t := ({a, b} : Multiset (AgentState L K))) happ IsActiveB
    have hpair_before' :
        Multiset.countP IsActiveB
          ({a, b} : Multiset (AgentState L K)) = 1 := by
      simpa [activeBCount] using hpair_before
    unfold activeBCount
    rw [hsub, hpair_before']
  have hnew :
      activeBCount
          (c - ({a, b} : Multiset (AgentState L K)) +
            ({(Transition L K a b).1, (Transition L K a b).2} :
              Multiset (AgentState L K))) =
        activeBCount (c - ({a, b} : Multiset (AgentState L K))) := by
    unfold activeBCount
    rw [Multiset.countP_add]
    change
        Multiset.countP IsActiveB (c - ({a, b} : Multiset (AgentState L K))) +
            activeBCount
              ({(Transition L K a b).1, (Transition L K a b).2} :
                Multiset (AgentState L K)) =
          Multiset.countP IsActiveB (c - ({a, b} : Multiset (AgentState L K)))
    rw [hpair_after]
    simp
  have hpos_old : 0 < activeBCount c := by
    simpa [activeBCount] using
      (Multiset.countP_pos_of_mem (s := c) hb_mem hb)
  omega

private theorem activeACount_cancel_B_A_lt
    (c : Config (AgentState L K)) {a b : AgentState L K}
    (hphase : ∀ x ∈ c, x.phase.val = 10)
    (ha_mem : a ∈ c) (hb_mem : b ∈ c)
    (ha : IsActiveB a) (hb : IsActiveA b) :
    activeACount
        (c - ({a, b} : Multiset (AgentState L K)) +
          ({(Transition L K a b).1, (Transition L K a b).2} :
            Multiset (AgentState L K))) <
      activeACount c := by
  have hne : a ≠ b := by
    intro h
    have : a.output = .A := by simpa [h] using hb.2
    simp [ha.2] at this
  have happ : ({a, b} : Multiset (AgentState L K)) ≤ c :=
    pair_le_of_mem_ne ha_mem hb_mem hne
  have htransition :
      Transition L K a b = Phase10Transition L K a b :=
    Transition_eq_Phase10Transition_of_phase10
      (L := L) (K := K) a b (hphase a ha_mem) (hphase b hb_mem)
  have hpair_before :
      activeACount ({a, b} : Multiset (AgentState L K)) = 1 := by
    change Multiset.countP IsActiveA (a ::ₘ ({b} : Multiset (AgentState L K))) = 1
    rw [Multiset.countP_cons_of_neg]
    · change Multiset.countP IsActiveA (b ::ₘ (0 : Multiset (AgentState L K))) = 1
      rw [Multiset.countP_cons_of_pos]
      · simp
      · exact hb
    · intro hbad
      have : a.output = .A := hbad.2
      simp [ha.2] at this
  have hlocal :=
    Phase10Transition_activeB_activeA_outputs_T
      (L := L) (K := K) a b ha.1 hb.1 ha.2 hb.2
  have hpair_after :
      activeACount
        ({(Transition L K a b).1, (Transition L K a b).2} :
          Multiset (AgentState L K)) = 0 := by
    rw [htransition]
    change Multiset.countP IsActiveA
      ((Phase10Transition L K a b).1 ::ₘ
        ({(Phase10Transition L K a b).2} : Multiset (AgentState L K))) = 0
    rcases hlocal with ⟨h1out, h2out, _h1full, _h2full⟩
    rw [Multiset.countP_cons_of_neg]
    · change Multiset.countP IsActiveA
        ((Phase10Transition L K a b).2 ::ₘ
          (0 : Multiset (AgentState L K))) = 0
      rw [Multiset.countP_cons_of_neg]
      · simp
      · intro hbad
        have : (Phase10Transition L K a b).2.output = .A := hbad.2
        simp [h2out] at this
    · intro hbad
      have : (Phase10Transition L K a b).1.output = .A := hbad.2
      simp [h1out] at this
  have hres :
      activeACount (c - ({a, b} : Multiset (AgentState L K))) =
        activeACount c - 1 := by
    have hsub := Multiset.countP_sub
      (s := c) (t := ({a, b} : Multiset (AgentState L K))) happ IsActiveA
    have hpair_before' :
        Multiset.countP IsActiveA
          ({a, b} : Multiset (AgentState L K)) = 1 := by
      simpa [activeACount] using hpair_before
    unfold activeACount
    rw [hsub, hpair_before']
  have hnew :
      activeACount
          (c - ({a, b} : Multiset (AgentState L K)) +
            ({(Transition L K a b).1, (Transition L K a b).2} :
              Multiset (AgentState L K))) =
        activeACount (c - ({a, b} : Multiset (AgentState L K))) := by
    unfold activeACount
    rw [Multiset.countP_add]
    change
        Multiset.countP IsActiveA (c - ({a, b} : Multiset (AgentState L K))) +
            activeACount
              ({(Transition L K a b).1, (Transition L K a b).2} :
                Multiset (AgentState L K)) =
          Multiset.countP IsActiveA (c - ({a, b} : Multiset (AgentState L K)))
    rw [hpair_after]
    simp
  have hpos_old : 0 < activeACount c := by
    simpa [activeACount] using
      (Multiset.countP_pos_of_mem (s := c) hb_mem hb)
  omega

private theorem wrongACount_activeA_nonActiveB_lt
    (c : Config (AgentState L K)) {a b : AgentState L K}
    (hphase : ∀ x ∈ c, x.phase.val = 10)
    (ha_mem : a ∈ c) (hb_mem : b ∈ c)
    (ha : IsActiveA a) (hb_wrong : b.output ≠ .A)
    (hb_not_activeB : ¬ IsActiveB b) :
    wrongACount
        (c - ({a, b} : Multiset (AgentState L K)) +
          ({(Transition L K a b).1, (Transition L K a b).2} :
            Multiset (AgentState L K))) <
      wrongACount c := by
  have hne : a ≠ b := ne_of_activeA_wrongA (L := L) (K := K) ha hb_wrong
  have happ : ({a, b} : Multiset (AgentState L K)) ≤ c :=
    pair_le_of_mem_ne ha_mem hb_mem hne
  have htransition :
      Transition L K a b = Phase10Transition L K a b :=
    Transition_eq_Phase10Transition_of_phase10
      (L := L) (K := K) a b (hphase a ha_mem) (hphase b hb_mem)
  have hpair_before :
      wrongACount ({a, b} : Multiset (AgentState L K)) = 1 := by
    change Multiset.countP (fun x : AgentState L K => x.output ≠ .A)
      (a ::ₘ ({b} : Multiset (AgentState L K))) = 1
    rw [Multiset.countP_cons_of_neg]
    · change Multiset.countP (fun x : AgentState L K => x.output ≠ .A)
        (b ::ₘ (0 : Multiset (AgentState L K))) = 1
      rw [Multiset.countP_cons_of_pos]
      · simp
      · exact hb_wrong
    · intro hbad
      exact hbad ha.2
  have hlocal :=
    Phase10Transition_activeA_nonActiveB_outputs_A
      (L := L) (K := K) a b ha.1 ha.2 hb_not_activeB
  have hpair_after :
      wrongACount
        ({(Transition L K a b).1, (Transition L K a b).2} :
          Multiset (AgentState L K)) = 0 := by
    rw [htransition]
    change Multiset.countP (fun x : AgentState L K => x.output ≠ .A)
      ((Phase10Transition L K a b).1 ::ₘ
        ({(Phase10Transition L K a b).2} : Multiset (AgentState L K))) = 0
    rcases hlocal with ⟨h1out, h2out⟩
    rw [Multiset.countP_cons_of_neg]
    · change Multiset.countP (fun x : AgentState L K => x.output ≠ .A)
        ((Phase10Transition L K a b).2 ::ₘ
          (0 : Multiset (AgentState L K))) = 0
      rw [Multiset.countP_cons_of_neg]
      · simp
      · intro hbad
        exact hbad h2out
    · intro hbad
      exact hbad h1out
  have hres :
      wrongACount (c - ({a, b} : Multiset (AgentState L K))) =
        wrongACount c - 1 := by
    have hsub := Multiset.countP_sub
      (s := c) (t := ({a, b} : Multiset (AgentState L K))) happ
      (fun x : AgentState L K => x.output ≠ .A)
    have hpair_before' :
        Multiset.countP (fun x : AgentState L K => x.output ≠ .A)
          ({a, b} : Multiset (AgentState L K)) = 1 := by
      simpa [wrongACount] using hpair_before
    unfold wrongACount
    rw [hsub, hpair_before']
  have hnew :
      wrongACount
          (c - ({a, b} : Multiset (AgentState L K)) +
            ({(Transition L K a b).1, (Transition L K a b).2} :
              Multiset (AgentState L K))) =
        wrongACount (c - ({a, b} : Multiset (AgentState L K))) := by
    unfold wrongACount
    rw [Multiset.countP_add]
    change
        Multiset.countP (fun x : AgentState L K => x.output ≠ .A)
            (c - ({a, b} : Multiset (AgentState L K))) +
          wrongACount
            ({(Transition L K a b).1, (Transition L K a b).2} :
              Multiset (AgentState L K)) =
        Multiset.countP (fun x : AgentState L K => x.output ≠ .A)
          (c - ({a, b} : Multiset (AgentState L K)))
    rw [hpair_after]
    simp
  have hpos_old : 0 < wrongACount c := by
    simpa [wrongACount] using
      (Multiset.countP_pos_of_mem
        (s := c) (p := fun x : AgentState L K => x.output ≠ .A) hb_mem hb_wrong)
  omega

private theorem activeBCount_activeA_nonActiveB_eq_zero
    (c : Config (AgentState L K)) {a b : AgentState L K}
    (hphase : ∀ x ∈ c, x.phase.val = 10)
    (ha_mem : a ∈ c) (hb_mem : b ∈ c)
    (ha : IsActiveA a) (hb_wrong : b.output ≠ .A)
    (hb_not_activeB : ¬ IsActiveB b)
    (hnoB : activeBCount c = 0) :
    activeBCount
        (c - ({a, b} : Multiset (AgentState L K)) +
          ({(Transition L K a b).1, (Transition L K a b).2} :
            Multiset (AgentState L K))) = 0 := by
  have hne : a ≠ b := ne_of_activeA_wrongA (L := L) (K := K) ha hb_wrong
  have happ : ({a, b} : Multiset (AgentState L K)) ≤ c :=
    pair_le_of_mem_ne ha_mem hb_mem hne
  have htransition :
      Transition L K a b = Phase10Transition L K a b :=
    Transition_eq_Phase10Transition_of_phase10
      (L := L) (K := K) a b (hphase a ha_mem) (hphase b hb_mem)
  have hlocal :=
    Phase10Transition_activeA_nonActiveB_outputs_A
      (L := L) (K := K) a b ha.1 ha.2 hb_not_activeB
  have hpair_after :
      activeBCount
        ({(Transition L K a b).1, (Transition L K a b).2} :
          Multiset (AgentState L K)) = 0 := by
    rw [htransition]
    change Multiset.countP IsActiveB
      ((Phase10Transition L K a b).1 ::ₘ
        ({(Phase10Transition L K a b).2} : Multiset (AgentState L K))) = 0
    rcases hlocal with ⟨h1out, h2out⟩
    rw [Multiset.countP_cons_of_neg]
    · change Multiset.countP IsActiveB
        ((Phase10Transition L K a b).2 ::ₘ
          (0 : Multiset (AgentState L K))) = 0
      rw [Multiset.countP_cons_of_neg]
      · simp
      · intro hbad
        exact by simp [IsActiveB, h2out] at hbad
    · intro hbad
      exact by simp [IsActiveB, h1out] at hbad
  have hres_zero :
      activeBCount (c - ({a, b} : Multiset (AgentState L K))) = 0 := by
    have hle := Multiset.countP_le_of_le
      (p := IsActiveB)
      (Multiset.sub_le_self c ({a, b} : Multiset (AgentState L K)))
    unfold activeBCount at hle hnoB ⊢
    omega
  unfold activeBCount
  rw [Multiset.countP_add]
  change
      activeBCount (c - ({a, b} : Multiset (AgentState L K))) +
        activeBCount
          ({(Transition L K a b).1, (Transition L K a b).2} :
            Multiset (AgentState L K)) = 0
  rw [hres_zero, hpair_after]

private theorem wrongBCount_activeB_nonActiveA_lt
    (c : Config (AgentState L K)) {a b : AgentState L K}
    (hphase : ∀ x ∈ c, x.phase.val = 10)
    (ha_mem : a ∈ c) (hb_mem : b ∈ c)
    (ha : IsActiveB a) (hb_wrong : b.output ≠ .B)
    (hb_not_activeA : ¬ IsActiveA b) :
    wrongBCount
        (c - ({a, b} : Multiset (AgentState L K)) +
          ({(Transition L K a b).1, (Transition L K a b).2} :
            Multiset (AgentState L K))) <
      wrongBCount c := by
  have hne : a ≠ b := ne_of_activeB_wrongB (L := L) (K := K) ha hb_wrong
  have happ : ({a, b} : Multiset (AgentState L K)) ≤ c :=
    pair_le_of_mem_ne ha_mem hb_mem hne
  have htransition :
      Transition L K a b = Phase10Transition L K a b :=
    Transition_eq_Phase10Transition_of_phase10
      (L := L) (K := K) a b (hphase a ha_mem) (hphase b hb_mem)
  have hpair_before :
      wrongBCount ({a, b} : Multiset (AgentState L K)) = 1 := by
    change Multiset.countP (fun x : AgentState L K => x.output ≠ .B)
      (a ::ₘ ({b} : Multiset (AgentState L K))) = 1
    rw [Multiset.countP_cons_of_neg]
    · change Multiset.countP (fun x : AgentState L K => x.output ≠ .B)
        (b ::ₘ (0 : Multiset (AgentState L K))) = 1
      rw [Multiset.countP_cons_of_pos]
      · simp
      · exact hb_wrong
    · intro hbad
      exact hbad ha.2
  have hlocal :=
    Phase10Transition_activeB_nonActiveA_outputs_B
      (L := L) (K := K) a b ha.1 ha.2 hb_not_activeA
  have hpair_after :
      wrongBCount
        ({(Transition L K a b).1, (Transition L K a b).2} :
          Multiset (AgentState L K)) = 0 := by
    rw [htransition]
    change Multiset.countP (fun x : AgentState L K => x.output ≠ .B)
      ((Phase10Transition L K a b).1 ::ₘ
        ({(Phase10Transition L K a b).2} : Multiset (AgentState L K))) = 0
    rcases hlocal with ⟨h1out, h2out⟩
    rw [Multiset.countP_cons_of_neg]
    · change Multiset.countP (fun x : AgentState L K => x.output ≠ .B)
        ((Phase10Transition L K a b).2 ::ₘ
          (0 : Multiset (AgentState L K))) = 0
      rw [Multiset.countP_cons_of_neg]
      · simp
      · intro hbad
        exact hbad h2out
    · intro hbad
      exact hbad h1out
  have hres :
      wrongBCount (c - ({a, b} : Multiset (AgentState L K))) =
        wrongBCount c - 1 := by
    have hsub := Multiset.countP_sub
      (s := c) (t := ({a, b} : Multiset (AgentState L K))) happ
      (fun x : AgentState L K => x.output ≠ .B)
    have hpair_before' :
        Multiset.countP (fun x : AgentState L K => x.output ≠ .B)
          ({a, b} : Multiset (AgentState L K)) = 1 := by
      simpa [wrongBCount] using hpair_before
    unfold wrongBCount
    rw [hsub, hpair_before']
  have hnew :
      wrongBCount
          (c - ({a, b} : Multiset (AgentState L K)) +
            ({(Transition L K a b).1, (Transition L K a b).2} :
              Multiset (AgentState L K))) =
        wrongBCount (c - ({a, b} : Multiset (AgentState L K))) := by
    unfold wrongBCount
    rw [Multiset.countP_add]
    change
        Multiset.countP (fun x : AgentState L K => x.output ≠ .B)
            (c - ({a, b} : Multiset (AgentState L K))) +
          wrongBCount
            ({(Transition L K a b).1, (Transition L K a b).2} :
              Multiset (AgentState L K)) =
        Multiset.countP (fun x : AgentState L K => x.output ≠ .B)
          (c - ({a, b} : Multiset (AgentState L K)))
    rw [hpair_after]
    simp
  have hpos_old : 0 < wrongBCount c := by
    simpa [wrongBCount] using
      (Multiset.countP_pos_of_mem
        (s := c) (p := fun x : AgentState L K => x.output ≠ .B) hb_mem hb_wrong)
  omega

private theorem activeACount_activeB_nonActiveA_eq_zero
    (c : Config (AgentState L K)) {a b : AgentState L K}
    (hphase : ∀ x ∈ c, x.phase.val = 10)
    (ha_mem : a ∈ c) (hb_mem : b ∈ c)
    (ha : IsActiveB a) (hb_wrong : b.output ≠ .B)
    (hb_not_activeA : ¬ IsActiveA b)
    (hnoA : activeACount c = 0) :
    activeACount
        (c - ({a, b} : Multiset (AgentState L K)) +
          ({(Transition L K a b).1, (Transition L K a b).2} :
            Multiset (AgentState L K))) = 0 := by
  have hne : a ≠ b := ne_of_activeB_wrongB (L := L) (K := K) ha hb_wrong
  have htransition :
      Transition L K a b = Phase10Transition L K a b :=
    Transition_eq_Phase10Transition_of_phase10
      (L := L) (K := K) a b (hphase a ha_mem) (hphase b hb_mem)
  have hlocal :=
    Phase10Transition_activeB_nonActiveA_outputs_B
      (L := L) (K := K) a b ha.1 ha.2 hb_not_activeA
  have hpair_after :
      activeACount
        ({(Transition L K a b).1, (Transition L K a b).2} :
          Multiset (AgentState L K)) = 0 := by
    rw [htransition]
    change Multiset.countP IsActiveA
      ((Phase10Transition L K a b).1 ::ₘ
        ({(Phase10Transition L K a b).2} : Multiset (AgentState L K))) = 0
    rcases hlocal with ⟨h1out, h2out⟩
    rw [Multiset.countP_cons_of_neg]
    · change Multiset.countP IsActiveA
        ((Phase10Transition L K a b).2 ::ₘ
          (0 : Multiset (AgentState L K))) = 0
      rw [Multiset.countP_cons_of_neg]
      · simp
      · intro hbad
        exact by simp [IsActiveA, h2out] at hbad
    · intro hbad
      exact by simp [IsActiveA, h1out] at hbad
  have hres_zero :
      activeACount (c - ({a, b} : Multiset (AgentState L K))) = 0 := by
    have hle := Multiset.countP_le_of_le
      (p := IsActiveA)
      (Multiset.sub_le_self c ({a, b} : Multiset (AgentState L K)))
    unfold activeACount at hle hnoA ⊢
    omega
  unfold activeACount
  rw [Multiset.countP_add]
  change
      activeACount (c - ({a, b} : Multiset (AgentState L K))) +
        activeACount
          ({(Transition L K a b).1, (Transition L K a b).2} :
            Multiset (AgentState L K)) = 0
  rw [hres_zero, hpair_after]

private theorem wrongTCount_activeT_noActiveBiased_lt
    (c : Config (AgentState L K)) {a b : AgentState L K}
    (hphase : ∀ x ∈ c, x.phase.val = 10)
    (ha_mem : a ∈ c) (hb_mem : b ∈ c)
    (ha : IsActiveT a) (hb_wrong : b.output ≠ .T)
    (hb_not_active_biased :
      ¬ (b.full = true ∧ (b.output = .A ∨ b.output = .B))) :
    wrongTCount
        (c - ({a, b} : Multiset (AgentState L K)) +
          ({(Transition L K a b).1, (Transition L K a b).2} :
            Multiset (AgentState L K))) <
      wrongTCount c := by
  have hne : a ≠ b := ne_of_activeT_wrongT (L := L) (K := K) ha hb_wrong
  have happ : ({a, b} : Multiset (AgentState L K)) ≤ c :=
    pair_le_of_mem_ne ha_mem hb_mem hne
  have htransition :
      Transition L K a b = Phase10Transition L K a b :=
    Transition_eq_Phase10Transition_of_phase10
      (L := L) (K := K) a b (hphase a ha_mem) (hphase b hb_mem)
  have hpair_before :
      wrongTCount ({a, b} : Multiset (AgentState L K)) = 1 := by
    change Multiset.countP (fun x : AgentState L K => x.output ≠ .T)
      (a ::ₘ ({b} : Multiset (AgentState L K))) = 1
    rw [Multiset.countP_cons_of_neg]
    · change Multiset.countP (fun x : AgentState L K => x.output ≠ .T)
        (b ::ₘ (0 : Multiset (AgentState L K))) = 1
      rw [Multiset.countP_cons_of_pos]
      · simp
      · exact hb_wrong
    · intro hbad
      exact hbad ha.2
  have hlocal :=
    Phase10Transition_activeT_noActiveBiased_outputs_T
      (L := L) (K := K) a b ha.1 ha.2 hb_not_active_biased
  have hpair_after :
      wrongTCount
        ({(Transition L K a b).1, (Transition L K a b).2} :
          Multiset (AgentState L K)) = 0 := by
    rw [htransition]
    change Multiset.countP (fun x : AgentState L K => x.output ≠ .T)
      ((Phase10Transition L K a b).1 ::ₘ
        ({(Phase10Transition L K a b).2} : Multiset (AgentState L K))) = 0
    rcases hlocal with ⟨h1out, h2out⟩
    rw [Multiset.countP_cons_of_neg]
    · change Multiset.countP (fun x : AgentState L K => x.output ≠ .T)
        ((Phase10Transition L K a b).2 ::ₘ
          (0 : Multiset (AgentState L K))) = 0
      rw [Multiset.countP_cons_of_neg]
      · simp
      · intro hbad
        exact hbad h2out
    · intro hbad
      exact hbad h1out
  have hres :
      wrongTCount (c - ({a, b} : Multiset (AgentState L K))) =
        wrongTCount c - 1 := by
    have hsub := Multiset.countP_sub
      (s := c) (t := ({a, b} : Multiset (AgentState L K))) happ
      (fun x : AgentState L K => x.output ≠ .T)
    have hpair_before' :
        Multiset.countP (fun x : AgentState L K => x.output ≠ .T)
          ({a, b} : Multiset (AgentState L K)) = 1 := by
      simpa [wrongTCount] using hpair_before
    unfold wrongTCount
    rw [hsub, hpair_before']
  have hnew :
      wrongTCount
          (c - ({a, b} : Multiset (AgentState L K)) +
            ({(Transition L K a b).1, (Transition L K a b).2} :
              Multiset (AgentState L K))) =
        wrongTCount (c - ({a, b} : Multiset (AgentState L K))) := by
    unfold wrongTCount
    rw [Multiset.countP_add]
    change
        Multiset.countP (fun x : AgentState L K => x.output ≠ .T)
            (c - ({a, b} : Multiset (AgentState L K))) +
          wrongTCount
            ({(Transition L K a b).1, (Transition L K a b).2} :
              Multiset (AgentState L K)) =
        Multiset.countP (fun x : AgentState L K => x.output ≠ .T)
          (c - ({a, b} : Multiset (AgentState L K)))
    rw [hpair_after]
    simp
  have hpos_old : 0 < wrongTCount c := by
    simpa [wrongTCount] using
      (Multiset.countP_pos_of_mem
        (s := c) (p := fun x : AgentState L K => x.output ≠ .T) hb_mem hb_wrong)
  omega

private theorem activeACount_activeT_noActiveBiased_eq_zero
    (c : Config (AgentState L K)) {a b : AgentState L K}
    (hphase : ∀ x ∈ c, x.phase.val = 10)
    (ha_mem : a ∈ c) (hb_mem : b ∈ c)
    (ha : IsActiveT a) (hb_wrong : b.output ≠ .T)
    (hb_not_active_biased :
      ¬ (b.full = true ∧ (b.output = .A ∨ b.output = .B)))
    (hnoA : activeACount c = 0) :
    activeACount
        (c - ({a, b} : Multiset (AgentState L K)) +
          ({(Transition L K a b).1, (Transition L K a b).2} :
            Multiset (AgentState L K))) = 0 := by
  have hne : a ≠ b := ne_of_activeT_wrongT (L := L) (K := K) ha hb_wrong
  have htransition :
      Transition L K a b = Phase10Transition L K a b :=
    Transition_eq_Phase10Transition_of_phase10
      (L := L) (K := K) a b (hphase a ha_mem) (hphase b hb_mem)
  have hlocal :=
    Phase10Transition_activeT_noActiveBiased_outputs_T
      (L := L) (K := K) a b ha.1 ha.2 hb_not_active_biased
  have hpair_after :
      activeACount
        ({(Transition L K a b).1, (Transition L K a b).2} :
          Multiset (AgentState L K)) = 0 := by
    rw [htransition]
    change Multiset.countP IsActiveA
      ((Phase10Transition L K a b).1 ::ₘ
        ({(Phase10Transition L K a b).2} : Multiset (AgentState L K))) = 0
    rcases hlocal with ⟨h1out, h2out⟩
    rw [Multiset.countP_cons_of_neg]
    · change Multiset.countP IsActiveA
        ((Phase10Transition L K a b).2 ::ₘ
          (0 : Multiset (AgentState L K))) = 0
      rw [Multiset.countP_cons_of_neg]
      · simp
      · intro hbad
        exact by simp [IsActiveA, h2out] at hbad
    · intro hbad
      exact by simp [IsActiveA, h1out] at hbad
  have hres_zero :
      activeACount (c - ({a, b} : Multiset (AgentState L K))) = 0 := by
    have hle := Multiset.countP_le_of_le
      (p := IsActiveA)
      (Multiset.sub_le_self c ({a, b} : Multiset (AgentState L K)))
    unfold activeACount at hle hnoA ⊢
    omega
  unfold activeACount
  rw [Multiset.countP_add]
  change
      activeACount (c - ({a, b} : Multiset (AgentState L K))) +
        activeACount
          ({(Transition L K a b).1, (Transition L K a b).2} :
            Multiset (AgentState L K)) = 0
  rw [hres_zero, hpair_after]

private theorem activeBCount_activeT_noActiveBiased_eq_zero
    (c : Config (AgentState L K)) {a b : AgentState L K}
    (hphase : ∀ x ∈ c, x.phase.val = 10)
    (ha_mem : a ∈ c) (hb_mem : b ∈ c)
    (ha : IsActiveT a) (hb_wrong : b.output ≠ .T)
    (hb_not_active_biased :
      ¬ (b.full = true ∧ (b.output = .A ∨ b.output = .B)))
    (hnoB : activeBCount c = 0) :
    activeBCount
        (c - ({a, b} : Multiset (AgentState L K)) +
          ({(Transition L K a b).1, (Transition L K a b).2} :
            Multiset (AgentState L K))) = 0 := by
  have hne : a ≠ b := ne_of_activeT_wrongT (L := L) (K := K) ha hb_wrong
  have htransition :
      Transition L K a b = Phase10Transition L K a b :=
    Transition_eq_Phase10Transition_of_phase10
      (L := L) (K := K) a b (hphase a ha_mem) (hphase b hb_mem)
  have hlocal :=
    Phase10Transition_activeT_noActiveBiased_outputs_T
      (L := L) (K := K) a b ha.1 ha.2 hb_not_active_biased
  have hpair_after :
      activeBCount
        ({(Transition L K a b).1, (Transition L K a b).2} :
          Multiset (AgentState L K)) = 0 := by
    rw [htransition]
    change Multiset.countP IsActiveB
      ((Phase10Transition L K a b).1 ::ₘ
        ({(Phase10Transition L K a b).2} : Multiset (AgentState L K))) = 0
    rcases hlocal with ⟨h1out, h2out⟩
    rw [Multiset.countP_cons_of_neg]
    · change Multiset.countP IsActiveB
        ((Phase10Transition L K a b).2 ::ₘ
          (0 : Multiset (AgentState L K))) = 0
      rw [Multiset.countP_cons_of_neg]
      · simp
      · intro hbad
        exact by simp [IsActiveB, h2out] at hbad
    · intro hbad
      exact by simp [IsActiveB, h1out] at hbad
  have hres_zero :
      activeBCount (c - ({a, b} : Multiset (AgentState L K))) = 0 := by
    have hle := Multiset.countP_le_of_le
      (p := IsActiveB)
      (Multiset.sub_le_self c ({a, b} : Multiset (AgentState L K)))
    unfold activeBCount at hle hnoB ⊢
    omega
  unfold activeBCount
  rw [Multiset.countP_add]
  change
      activeBCount (c - ({a, b} : Multiset (AgentState L K))) +
        activeBCount
          ({(Transition L K a b).1, (Transition L K a b).2} :
            Multiset (AgentState L K)) = 0
  rw [hres_zero, hpair_after]

/-- The full dispatcher has the same pair-level active-source preservation
when both interacting inputs are already in Phase 10. -/
theorem Transition_preserves_pair_hasActive_of_phase10
    (a b : AgentState L K)
    (ha : a.phase.val = 10) (hb : b.phase.val = 10)
    (hactive : a.full = true ∨ b.full = true) :
    (Transition L K a b).1.full = true ∨
      (Transition L K a b).2.full = true := by
  rw [Transition_eq_Phase10Transition_of_phase10 (L := L) (K := K) a b ha hb]
  exact Phase10Transition_preserves_pair_hasActive (L := L) (K := K) a b hactive

/-- If the left input was below Phase 10 and its output of the full dispatcher
is in Phase 10, then that output is active. -/
theorem Transition_left_full_of_before_lt_10_final_phase10
    (a b : AgentState L K)
    (ha : a.phase.val < 10)
    (hfinal : (Transition L K a b).1.phase.val = 10) :
    (Transition L K a b).1.full = true := by
  unfold Transition at hfinal ⊢
  rcases hpe : phaseEpidemicUpdate L K a b with ⟨s, t⟩
  simp only [hpe] at hfinal ⊢
  let out :=
    match s.phase with
    | ⟨0, _⟩ => Phase0Transition L K s t
    | ⟨1, _⟩ => Phase1Transition L K s t
    | ⟨2, _⟩ => Phase2Transition L K s t
    | ⟨3, _⟩ => Phase3Transition L K s t
    | ⟨4, _⟩ => Phase4Transition L K s t
    | ⟨5, _⟩ => Phase5Transition L K s t
    | ⟨6, _⟩ => Phase6Transition L K s t
    | ⟨7, _⟩ => Phase7Transition L K s t
    | ⟨8, _⟩ => Phase8Transition L K s t
    | ⟨9, _⟩ => Phase9Transition L K s t
    | ⟨10, _⟩ => Phase10Transition L K s t
    | _ => (s, t)
  change (finishPhase10Entry L K s out.1).full = true
  change (finishPhase10Entry L K s out.1).phase.val = 10 at hfinal
  by_cases hs_lt : s.phase.val < 10
  · exact finishPhase10Entry_full_of_before_lt_10_final_phase10
      (L := L) (K := K) s out.1 hs_lt hfinal
  · have hs10 : s.phase.val = 10 := by
      have hs_upper := s.phase.2
      omega
    have hs_phase_eq : s.phase = phase10 := by
      apply Fin.ext
      simp [phase10, hs10]
    have hentry :=
      phaseEpidemicUpdate_left_active_biased_of_before_lt_10_phase10
        (L := L) (K := K) a b ha (by simpa [hpe] using hs10)
    have hs_full : s.full = true := by
      simpa [hpe] using hentry.1
    have hs_out : s.output = .A ∨ s.output = .B := by
      simpa [hpe] using hentry.2
    have hout :
        out = Phase10Transition L K s t := by
      dsimp [out]
      rw [hs_phase_eq]
      rfl
    rw [hout]
    rw [finishPhase10Entry_eq_self_of_before_not_lt_10
      (L := L) (K := K) s (Phase10Transition L K s t).1 hs_lt]
    exact Phase10Transition_left_full_of_active_biased
      (L := L) (K := K) s t hs_full hs_out

/-- If the right input was below Phase 10 and its output of the full dispatcher
is in Phase 10, then that output is active. -/
theorem Transition_right_full_of_before_lt_10_final_phase10
    (a b : AgentState L K)
    (hb : b.phase.val < 10)
    (hfinal : (Transition L K a b).2.phase.val = 10) :
    (Transition L K a b).2.full = true := by
  unfold Transition at hfinal ⊢
  rcases hpe : phaseEpidemicUpdate L K a b with ⟨s, t⟩
  simp only [hpe] at hfinal ⊢
  let out :=
    match s.phase with
    | ⟨0, _⟩ => Phase0Transition L K s t
    | ⟨1, _⟩ => Phase1Transition L K s t
    | ⟨2, _⟩ => Phase2Transition L K s t
    | ⟨3, _⟩ => Phase3Transition L K s t
    | ⟨4, _⟩ => Phase4Transition L K s t
    | ⟨5, _⟩ => Phase5Transition L K s t
    | ⟨6, _⟩ => Phase6Transition L K s t
    | ⟨7, _⟩ => Phase7Transition L K s t
    | ⟨8, _⟩ => Phase8Transition L K s t
    | ⟨9, _⟩ => Phase9Transition L K s t
    | ⟨10, _⟩ => Phase10Transition L K s t
    | _ => (s, t)
  change (finishPhase10Entry L K t out.2).full = true
  change (finishPhase10Entry L K t out.2).phase.val = 10 at hfinal
  by_cases ht_lt : t.phase.val < 10
  · exact finishPhase10Entry_full_of_before_lt_10_final_phase10
      (L := L) (K := K) t out.2 ht_lt hfinal
  · have ht10 : t.phase.val = 10 := by
      have ht_upper := t.phase.2
      omega
    have hentry :=
      phaseEpidemicUpdate_right_active_biased_of_before_lt_10_phase10
        (L := L) (K := K) a b hb (by simpa [hpe] using ht10)
    have ht_full : t.full = true := by
      simpa [hpe] using hentry.1
    have ht_out : t.output = .A ∨ t.output = .B := by
      simpa [hpe] using hentry.2
    have hsync := phaseEpidemicUpdate_phase10_sync (L := L) (K := K) a b
    have hs10_ep : (phaseEpidemicUpdate L K a b).1.phase.val = 10 :=
      hsync.mpr (by simpa [hpe] using ht10)
    have hs10 : s.phase.val = 10 := by
      simpa [hpe] using hs10_ep
    have hs_phase_eq : s.phase = phase10 := by
      apply Fin.ext
      simp [phase10, hs10]
    have hout :
        out = Phase10Transition L K s t := by
      dsimp [out]
      rw [hs_phase_eq]
      rfl
    rw [hout]
    rw [finishPhase10Entry_eq_self_of_before_not_lt_10
      (L := L) (K := K) t (Phase10Transition L K s t).2 ht_lt]
    exact Phase10Transition_right_full_of_active_biased
      (L := L) (K := K) s t ht_full ht_out

/-- Boundary-crossing step: if a step enters the all-Phase-10 region from a
configuration that was not already all Phase 10, then the resulting
configuration contains an active backup source. -/
theorem hasActiveAgent_of_step_to_all_phase10_of_not_all_phase10
    (c c' : Config (AgentState L K))
    (hnot : ¬ ∀ a ∈ c, a.phase.val = 10)
    (hphase' : ∀ a ∈ c', a.phase.val = 10)
    (hstep : (NonuniformMajority L K).StepRel c c') :
  hasActiveAgent c' := by
  classical
  push Not at hnot
  rcases hnot with ⟨a, ha_mem, ha_ne⟩
  rcases hstep with ⟨r₁, r₂, happ, hc'⟩
  dsimp [Protocol.Applicable, NonuniformMajority] at happ hc'
  by_cases ha₁ : a = r₁
  · subst a
    have hr₁_lt : r₁.phase.val < 10 := by
      have hupper := r₁.phase.2
      omega
    have hp₁_mem : (Transition L K r₁ r₂).1 ∈ c' := by
      rw [hc']
      exact Multiset.mem_add.2 (Or.inr (Multiset.mem_cons_self _ _))
    have hp₁_phase : (Transition L K r₁ r₂).1.phase.val = 10 :=
      hphase' _ hp₁_mem
    exact ⟨(Transition L K r₁ r₂).1, hp₁_mem,
      Transition_left_full_of_before_lt_10_final_phase10
        (L := L) (K := K) r₁ r₂ hr₁_lt hp₁_phase⟩
  by_cases ha₂ : a = r₂
  · subst a
    have hr₂_lt : r₂.phase.val < 10 := by
      have hupper := r₂.phase.2
      omega
    have hp₂_mem : (Transition L K r₁ r₂).2 ∈ c' := by
      rw [hc']
      exact Multiset.mem_add.2 (Or.inr (Multiset.mem_cons_of_mem (by simp)))
    have hp₂_phase : (Transition L K r₁ r₂).2.phase.val = 10 :=
      hphase' _ hp₂_mem
    exact ⟨(Transition L K r₁ r₂).2, hp₂_mem,
      Transition_right_full_of_before_lt_10_final_phase10
        (L := L) (K := K) r₁ r₂ hr₂_lt hp₂_phase⟩
  · have ha_residual : a ∈ c - ({r₁, r₂} : Multiset (AgentState L K)) := by
      have h₁ : a ∈ c.erase r₁ := (Multiset.mem_erase_of_ne ha₁).2 ha_mem
      have h₂ : a ∈ (c.erase r₁).erase r₂ := (Multiset.mem_erase_of_ne ha₂).2 h₁
      simpa using h₂
    have ha_c' : a ∈ c' := by
      rw [hc']
      exact Multiset.mem_add.2 (Or.inl ha_residual)
    exact False.elim (ha_ne (hphase' a ha_c'))

/-- A single step inside the all-Phase-10 region preserves existence of an
active backup source. -/
theorem phase10_hasActiveAgent_preserved_by_step
    (c c' : Config (AgentState L K))
    (hphase : ∀ a ∈ c, a.phase.val = 10)
    (hactive : hasActiveAgent c)
    (hstep : (NonuniformMajority L K).StepRel c c') :
    hasActiveAgent c' := by
  rcases hstep with ⟨r₁, r₂, happ, hc'⟩
  dsimp [Protocol.Applicable, NonuniformMajority] at happ hc'
  have hr₁_mem : r₁ ∈ c :=
    Multiset.mem_of_le happ (Multiset.mem_cons_self r₁ {r₂})
  have hr₂_mem : r₂ ∈ c :=
    Multiset.mem_of_le happ (Multiset.mem_cons_of_mem (by simp))
  have hpair_phase :
      r₁.phase.val = 10 ∧ r₂.phase.val = 10 :=
    ⟨hphase r₁ hr₁_mem, hphase r₂ hr₂_mem⟩
  rw [hasActiveAgent_iff_activeCount_pos] at hactive ⊢
  rw [hc']
  by_cases hpair_active : r₁.full = true ∨ r₂.full = true
  · have hout_active :=
      Transition_preserves_pair_hasActive_of_phase10 (L := L) (K := K)
        r₁ r₂ hpair_phase.1 hpair_phase.2 hpair_active
    have hout_count :
        0 < activeCount ({(Transition L K r₁ r₂).1,
          (Transition L K r₁ r₂).2} : Multiset (AgentState L K)) := by
      rw [← hasActiveAgent_iff_activeCount_pos]
      rcases hout_active with hout | hout
      · exact ⟨(Transition L K r₁ r₂).1, by simp, hout⟩
      · exact ⟨(Transition L K r₁ r₂).2, by simp, hout⟩
    have hle :
        activeCount ({(Transition L K r₁ r₂).1,
          (Transition L K r₁ r₂).2} : Multiset (AgentState L K)) ≤
        activeCount (c - ({r₁, r₂} : Multiset (AgentState L K)) +
          ({(Transition L K r₁ r₂).1,
            (Transition L K r₁ r₂).2} : Multiset (AgentState L K))) := by
      unfold activeCount
      exact Multiset.countP_le_of_le
        (p := fun a : AgentState L K => a.full = true) (Multiset.le_add_left _ _)
    exact lt_of_lt_of_le hout_count hle
  · have hpair_zero :
        activeCount ({r₁, r₂} : Multiset (AgentState L K)) = 0 := by
      change Multiset.countP (fun a : AgentState L K => a.full = true)
        ({r₁, r₂} : Multiset (AgentState L K)) = 0
      rw [Multiset.countP_eq_zero]
      intro a ha
      simp at ha
      rcases ha with ha | ha
      · subst a
        exact fun h => hpair_active (Or.inl h)
      · subst a
        exact fun h => hpair_active (Or.inr h)
    have hres :
        activeCount (c - ({r₁, r₂} : Multiset (AgentState L K))) =
          activeCount c := by
      have hsub := Multiset.countP_sub
        (s := c) (t := ({r₁, r₂} : Multiset (AgentState L K))) happ
        (fun a : AgentState L K => a.full = true)
      unfold activeCount at hpair_zero ⊢
      rw [hsub]
      omega
    have hle :
        activeCount (c - ({r₁, r₂} : Multiset (AgentState L K))) ≤
        activeCount (c - ({r₁, r₂} : Multiset (AgentState L K)) +
          ({(Transition L K r₁ r₂).1,
            (Transition L K r₁ r₂).2} : Multiset (AgentState L K))) := by
      unfold activeCount
      exact Multiset.countP_le_of_le
        (p := fun a : AgentState L K => a.full = true) (Multiset.le_add_right _ _)
    rw [← hres] at hactive
    exact lt_of_lt_of_le hactive hle

/-- Any reachable all-Phase-10 configuration of population at least two has
an active backup source.  The active source is created at the boundary step
where the last lower-phase agent enters Phase 10, and Phase-10 steps preserve
non-emptiness of active sources. -/
theorem hasActiveAgent_of_reachable_all_phase10
    (init c : Config (AgentState L K))
    (hinit : validInitial init) (hn : 2 ≤ c.card)
    (hreach : (NonuniformMajority L K).Reachable init c)
    (hphase10 : ∀ a ∈ c, a.phase.val = 10) :
    hasActiveAgent c := by
  revert hn hphase10
  induction hreach with
  | refl =>
      intro hn hphase10
      have hpos : 0 < init.card := by omega
      rcases Multiset.card_pos_iff_exists_mem.1 hpos with ⟨a, ha⟩
      have h0 : a.phase.val = 0 := by
        have hphase := (hinit a ha).1
        rw [hphase]
      have h10 := hphase10 a ha
      omega
  | tail hprev hstep ih =>
      rename_i prev final
      intro hn hphase10
      by_cases hmid_phase : ∀ a ∈ prev, a.phase.val = 10
      · have hcard_mid : 2 ≤ prev.card := by
          have hcard := Protocol.stepRel_card_eq (P := NonuniformMajority L K) hstep
          omega
        have hactive_mid := ih hcard_mid hmid_phase
        exact phase10_hasActiveAgent_preserved_by_step
          (L := L) (K := K) prev _ hmid_phase hactive_mid hstep
      · exact hasActiveAgent_of_step_to_all_phase10_of_not_all_phase10
          (L := L) (K := K) prev _ hmid_phase hphase10 hstep

private theorem stepRel_source_card_ge_two
    {c c' : Config (AgentState L K)}
    (hstep : (NonuniformMajority L K).StepRel c c') :
    2 ≤ c.card := by
  rcases hstep with ⟨r₁, r₂, happ, _hc'⟩
  have hpair_card : ({r₁, r₂} : Multiset (AgentState L K)).card = 2 := by
    simp
  simpa [hpair_card] using Multiset.card_le_card happ

/-- Any reachable all-Phase-10 configuration is either empty or contains an
active backup source.  This removes the population-size side condition from
`hasActiveAgent_of_reachable_all_phase10`; the only size-0 case is vacuous for
unanimous-output witnesses. -/
theorem card_eq_zero_or_hasActiveAgent_of_reachable_all_phase10
    (init c : Config (AgentState L K))
    (hinit : validInitial init)
    (hreach : (NonuniformMajority L K).Reachable init c)
    (hphase10 : ∀ a ∈ c, a.phase.val = 10) :
    c.card = 0 ∨ hasActiveAgent c := by
  revert hphase10
  induction hreach with
  | refl =>
      intro hphase10
      by_cases hzero : init.card = 0
      · exact Or.inl hzero
      · have hpos : 0 < init.card := Nat.pos_of_ne_zero hzero
        rcases Multiset.card_pos_iff_exists_mem.1 hpos with ⟨a, ha⟩
        have h0 : a.phase.val = 0 := by
          have hphase := (hinit a ha).1
          rw [hphase]
        have h10 := hphase10 a ha
        omega
  | tail hprev hstep ih =>
      rename_i prev final
      intro hphase10
      by_cases hmid_phase : ∀ a ∈ prev, a.phase.val = 10
      · rcases ih hmid_phase with hprev_zero | hprev_active
        · have hcard_ge := stepRel_source_card_ge_two (L := L) (K := K) hstep
          omega
        · exact Or.inr
            (phase10_hasActiveAgent_preserved_by_step
              (L := L) (K := K) prev final hmid_phase hprev_active hstep)
      · exact Or.inr
          (hasActiveAgent_of_step_to_all_phase10_of_not_all_phase10
            (L := L) (K := K) prev final hmid_phase hphase10 hstep)

/-- A single protocol step starting from an all-Phase-10 configuration preserves
the Phase-10 active signed sum. -/
theorem phase10ActiveSignedSum_stepRel_eq
    (c c' : Config (AgentState L K))
    (hphase : ∀ a ∈ c, a.phase.val = 10)
    (hstep : (NonuniformMajority L K).StepRel c c') :
    phase10ActiveSignedSum c' = phase10ActiveSignedSum c := by
  rcases hstep with ⟨r₁, r₂, happ, hc'⟩
  dsimp [Protocol.Applicable, NonuniformMajority] at happ hc'
  have hr₁_mem : r₁ ∈ c :=
    Multiset.mem_of_le happ (Multiset.mem_cons_self r₁ {r₂})
  have hr₂_mem : r₂ ∈ c :=
    Multiset.mem_of_le happ (Multiset.mem_cons_of_mem (by simp))
  have htransition :
      Transition L K r₁ r₂ = Phase10Transition L K r₁ r₂ :=
    Transition_eq_Phase10Transition_of_phase10
      (L := L) (K := K) r₁ r₂ (hphase r₁ hr₁_mem) (hphase r₂ hr₂_mem)
  have hpair :
      signedContribution (Transition L K r₁ r₂).1 +
          signedContribution (Transition L K r₁ r₂).2 =
        signedContribution r₁ + signedContribution r₂ := by
    rw [htransition]
    exact phase10Transition_preserves_signedContribution (L := L) (K := K) r₁ r₂
  rw [hc']
  have hrestore : c - r₁ ::ₘ {r₂} + r₁ ::ₘ {r₂} = c :=
    Multiset.sub_add_cancel happ
  have hsum_c :
      phase10ActiveSignedSum c =
        phase10ActiveSignedSum (c - r₁ ::ₘ {r₂}) +
          (signedContribution r₁ + signedContribution r₂) := by
    rw [← hrestore]
    simp [phase10ActiveSignedSum, add_left_comm]
  have hsum_c' :
      phase10ActiveSignedSum
          (c - r₁ ::ₘ {r₂} +
          (Transition L K r₁ r₂).1 ::ₘ {(Transition L K r₁ r₂).2}) =
        phase10ActiveSignedSum (c - r₁ ::ₘ {r₂}) +
          (signedContribution (Transition L K r₁ r₂).1 +
            signedContribution (Transition L K r₁ r₂).2) := by
    simp [phase10ActiveSignedSum, add_left_comm]
  rw [hsum_c', hsum_c, hpair]

/-- A single protocol step starting from an all-Phase-10 configuration stays in
Phase 10. -/
theorem phase10_phase_preserved_by_step
    (c c' : Config (AgentState L K))
    (hphase : ∀ a ∈ c, a.phase.val = 10)
    (hstep : (NonuniformMajority L K).StepRel c c') :
    ∀ a ∈ c', a.phase.val = 10 := by
  rcases hstep with ⟨r₁, r₂, happ, hc'⟩
  dsimp [Protocol.Applicable, NonuniformMajority] at happ hc'
  have hr₁_mem : r₁ ∈ c :=
    Multiset.mem_of_le happ (Multiset.mem_cons_self r₁ {r₂})
  have hr₂_mem : r₂ ∈ c :=
    Multiset.mem_of_le happ (Multiset.mem_cons_of_mem (by simp))
  have hr₁_phase : r₁.phase.val = 10 := hphase r₁ hr₁_mem
  have hr₂_phase : r₂.phase.val = 10 := hphase r₂ hr₂_mem
  have hmono := Transition_phase_monotone (L := L) (K := K) r₁ r₂
  have hp₁_phase : (Transition L K r₁ r₂).1.phase.val = 10 := by
    have hge : 10 ≤ (Transition L K r₁ r₂).1.phase.val := by
      rw [← hr₁_phase]
      exact hmono.1
    have hlt := (Transition L K r₁ r₂).1.phase.2
    omega
  have hp₂_phase : (Transition L K r₁ r₂).2.phase.val = 10 := by
    have hge : 10 ≤ (Transition L K r₁ r₂).2.phase.val := by
      rw [← hr₂_phase]
      exact hmono.2
    have hlt := (Transition L K r₁ r₂).2.phase.2
    omega
  intro a ha
  rw [hc'] at ha
  rcases Multiset.mem_add.1 ha with ha_residual | ha_pair
  · by_cases ha₁ : a = r₁
    · simpa [ha₁] using hphase r₁ hr₁_mem
    by_cases ha₂ : a = r₂
    · simpa [ha₂] using hphase r₂ hr₂_mem
    have ha_c : a ∈ c := by
      exact Multiset.mem_of_le (Multiset.sub_le_self c (r₁ ::ₘ {r₂})) ha_residual
    exact hphase a ha_c
  · rcases Multiset.mem_cons.1 ha_pair with ha_p₁ | ha_tail
    · simpa [ha_p₁] using hp₁_phase
    · have ha_p₂ : a = (Transition L K r₁ r₂).2 := by
        simpa using ha_tail
      simpa [ha_p₂] using hp₂_phase

/-- Reachability inside the all-Phase-10 region preserves both Phase 10 and
the active signed sum. -/
theorem phase10_phase_and_activeSignedSum_preserved_by_reachable
    (c c' : Config (AgentState L K))
    (hphase : ∀ a ∈ c, a.phase.val = 10)
    (hreach : (NonuniformMajority L K).Reachable c c') :
    (∀ a ∈ c', a.phase.val = 10) ∧
      phase10ActiveSignedSum c' = phase10ActiveSignedSum c := by
  induction hreach with
  | refl =>
      exact ⟨hphase, rfl⟩
  | tail _ hstep ih =>
      rcases ih with ⟨hphase_mid, hsum_mid⟩
      have hphase_next :=
        phase10_phase_preserved_by_step (L := L) (K := K) _ _ hphase_mid hstep
      have hsum_step :=
        phase10ActiveSignedSum_stepRel_eq (L := L) (K := K) _ _ hphase_mid hstep
      exact ⟨hphase_next, hsum_step.trans hsum_mid⟩

theorem phase10_eliminate_activeB_of_pos
    (c : Config (AgentState L K))
    (hphase : ∀ a ∈ c, a.phase.val = 10)
    (hpos : 0 < phase10ActiveSignedSum c) :
    ∃ d, (NonuniformMajority L K).Reachable c d ∧
      (∀ a ∈ d, a.phase.val = 10) ∧
      0 < phase10ActiveSignedSum d ∧ activeBCount d = 0 := by
  classical
  let P : ℕ → Prop := fun n =>
    ∀ c : Config (AgentState L K), activeBCount c = n →
      (∀ a ∈ c, a.phase.val = 10) → 0 < phase10ActiveSignedSum c →
      ∃ d, (NonuniformMajority L K).Reachable c d ∧
        (∀ a ∈ d, a.phase.val = 10) ∧
        0 < phase10ActiveSignedSum d ∧ activeBCount d = 0
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro c hcount hphase hpos
        by_cases hzero : activeBCount c = 0
        · exact ⟨c, Relation.ReflTransGen.refl, hphase, hpos, hzero⟩
        · have hBpos : 0 < activeBCount c := Nat.pos_of_ne_zero hzero
          rcases (Multiset.countP_pos.1 (by simpa [activeBCount] using hBpos) :
              ∃ b ∈ c, IsActiveB b) with ⟨b, hb_mem, hb⟩
          rcases exists_activeA_of_phase10ActiveSignedSum_pos
              (L := L) (K := K) c hpos with ⟨a, ha_mem, ha⟩
          have hne : a ≠ b := ne_of_activeA_activeB (L := L) (K := K) ha hb
          let c1 : Config (AgentState L K) :=
            c - ({a, b} : Multiset (AgentState L K)) +
              ({(Transition L K a b).1, (Transition L K a b).2} :
                Multiset (AgentState L K))
          have happ : ({a, b} : Multiset (AgentState L K)) ≤ c :=
            pair_le_of_mem_ne ha_mem hb_mem hne
          have hstep : (NonuniformMajority L K).StepRel c c1 := by
            refine ⟨a, b, happ, ?_⟩
            rfl
          have hreach1 : (NonuniformMajority L K).Reachable c c1 :=
            Relation.ReflTransGen.single hstep
          have hphase1 : ∀ x ∈ c1, x.phase.val = 10 :=
            phase10_phase_preserved_by_step (L := L) (K := K) c c1 hphase hstep
          have hsum1 : phase10ActiveSignedSum c1 = phase10ActiveSignedSum c :=
            phase10ActiveSignedSum_stepRel_eq (L := L) (K := K) c c1 hphase hstep
          have hpos1 : 0 < phase10ActiveSignedSum c1 := by
            rw [hsum1]
            exact hpos
          have hlt : activeBCount c1 < n := by
            have hlt' :=
              activeBCount_cancel_A_B_lt
                (L := L) (K := K) c hphase ha_mem hb_mem ha hb
            rw [hcount] at hlt'
            exact hlt'
          rcases ih (activeBCount c1) hlt c1 rfl hphase1 hpos1 with
            ⟨d, hreach2, hphased, hposd, hBd⟩
          exact ⟨d, Relation.ReflTransGen.trans hreach1 hreach2,
            hphased, hposd, hBd⟩
  exact hP (activeBCount c) c rfl hphase hpos

theorem phase10_broadcast_A_of_pos_no_activeB
    (c : Config (AgentState L K))
    (hphase : ∀ a ∈ c, a.phase.val = 10)
    (hpos : 0 < phase10ActiveSignedSum c)
    (hnoB : activeBCount c = 0) :
    ∃ d, (NonuniformMajority L K).Reachable c d ∧
      (∀ a ∈ d, a.phase.val = 10) ∧
      0 < phase10ActiveSignedSum d ∧ activeBCount d = 0 ∧
      (∀ a ∈ d, a.output = .A) := by
  classical
  let P : ℕ → Prop := fun n =>
    ∀ c : Config (AgentState L K), wrongACount c = n →
      (∀ a ∈ c, a.phase.val = 10) → 0 < phase10ActiveSignedSum c →
      activeBCount c = 0 →
      ∃ d, (NonuniformMajority L K).Reachable c d ∧
        (∀ a ∈ d, a.phase.val = 10) ∧
        0 < phase10ActiveSignedSum d ∧ activeBCount d = 0 ∧
        (∀ a ∈ d, a.output = .A)
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro c hcount hphase hpos hnoB
        by_cases hwrong_zero : wrongACount c = 0
        · have hallA : ∀ a ∈ c, a.output = .A := by
            intro a ha
            have hnot : ¬ a.output ≠ .A := by
              exact (Multiset.countP_eq_zero.1
                (by simpa [wrongACount] using hwrong_zero)) a ha
            by_cases hout : a.output = .A
            · exact hout
            · exact False.elim (hnot hout)
          exact ⟨c, Relation.ReflTransGen.refl, hphase, hpos, hnoB, hallA⟩
        · have hwrong_pos : 0 < wrongACount c := Nat.pos_of_ne_zero hwrong_zero
          rcases (Multiset.countP_pos.1 (by simpa [wrongACount] using hwrong_pos) :
              ∃ b ∈ c, b.output ≠ .A) with ⟨b, hb_mem, hb_wrong⟩
          rcases exists_activeA_of_phase10ActiveSignedSum_pos
              (L := L) (K := K) c hpos with ⟨a, ha_mem, ha⟩
          have hne : a ≠ b := ne_of_activeA_wrongA (L := L) (K := K) ha hb_wrong
          have hb_not_activeB : ¬ IsActiveB b := by
            exact (Multiset.countP_eq_zero.1 (by simpa [activeBCount] using hnoB)) b hb_mem
          let c1 : Config (AgentState L K) :=
            c - ({a, b} : Multiset (AgentState L K)) +
              ({(Transition L K a b).1, (Transition L K a b).2} :
                Multiset (AgentState L K))
          have happ : ({a, b} : Multiset (AgentState L K)) ≤ c :=
            pair_le_of_mem_ne ha_mem hb_mem hne
          have hstep : (NonuniformMajority L K).StepRel c c1 := by
            refine ⟨a, b, happ, ?_⟩
            rfl
          have hreach1 : (NonuniformMajority L K).Reachable c c1 :=
            Relation.ReflTransGen.single hstep
          have hphase1 : ∀ x ∈ c1, x.phase.val = 10 :=
            phase10_phase_preserved_by_step (L := L) (K := K) c c1 hphase hstep
          have hsum1 : phase10ActiveSignedSum c1 = phase10ActiveSignedSum c :=
            phase10ActiveSignedSum_stepRel_eq (L := L) (K := K) c c1 hphase hstep
          have hpos1 : 0 < phase10ActiveSignedSum c1 := by
            rw [hsum1]
            exact hpos
          have hnoB1 : activeBCount c1 = 0 :=
            activeBCount_activeA_nonActiveB_eq_zero
              (L := L) (K := K) c hphase ha_mem hb_mem ha hb_wrong hb_not_activeB hnoB
          have hlt : wrongACount c1 < n := by
            have hlt' :=
              wrongACount_activeA_nonActiveB_lt
                (L := L) (K := K) c hphase ha_mem hb_mem ha hb_wrong hb_not_activeB
            rw [hcount] at hlt'
            exact hlt'
          rcases ih (wrongACount c1) hlt c1 rfl hphase1 hpos1 hnoB1 with
            ⟨d, hreach2, hphased, hposd, hnoBd, hallA⟩
          exact ⟨d, Relation.ReflTransGen.trans hreach1 hreach2,
            hphased, hposd, hnoBd, hallA⟩
  exact hP (wrongACount c) c rfl hphase hpos hnoB

theorem phase10_reach_unanimous_A_of_pos
    (c : Config (AgentState L K))
    (hphase : ∀ a ∈ c, a.phase.val = 10)
    (hpos : 0 < phase10ActiveSignedSum c) :
    ∃ d, (NonuniformMajority L K).Reachable c d ∧
      (∀ a ∈ d, a.phase.val = 10 ∧ a.output = .A) := by
  rcases phase10_eliminate_activeB_of_pos
      (L := L) (K := K) c hphase hpos with
    ⟨d, hreach1, hphased, hposd, hnoBd⟩
  rcases phase10_broadcast_A_of_pos_no_activeB
      (L := L) (K := K) d hphased hposd hnoBd with
    ⟨e, hreach2, hphasee, _hpose, _hnoBe, hallA⟩
  exact ⟨e, Relation.ReflTransGen.trans hreach1 hreach2,
    fun a ha => ⟨hphasee a ha, hallA a ha⟩⟩

theorem phase10_eliminate_activeA_of_neg
    (c : Config (AgentState L K))
    (hphase : ∀ a ∈ c, a.phase.val = 10)
    (hneg : phase10ActiveSignedSum c < 0) :
    ∃ d, (NonuniformMajority L K).Reachable c d ∧
      (∀ a ∈ d, a.phase.val = 10) ∧
      phase10ActiveSignedSum d < 0 ∧ activeACount d = 0 := by
  classical
  let P : ℕ → Prop := fun n =>
    ∀ c : Config (AgentState L K), activeACount c = n →
      (∀ a ∈ c, a.phase.val = 10) → phase10ActiveSignedSum c < 0 →
      ∃ d, (NonuniformMajority L K).Reachable c d ∧
        (∀ a ∈ d, a.phase.val = 10) ∧
        phase10ActiveSignedSum d < 0 ∧ activeACount d = 0
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro c hcount hphase hneg
        by_cases hzero : activeACount c = 0
        · exact ⟨c, Relation.ReflTransGen.refl, hphase, hneg, hzero⟩
        · have hApos : 0 < activeACount c := Nat.pos_of_ne_zero hzero
          rcases (Multiset.countP_pos.1 (by simpa [activeACount] using hApos) :
              ∃ b ∈ c, IsActiveA b) with ⟨b, hb_mem, hb⟩
          rcases exists_activeB_of_phase10ActiveSignedSum_neg
              (L := L) (K := K) c hneg with ⟨a, ha_mem, ha⟩
          have hne : a ≠ b := by
            intro h
            have : a.output = .A := by simpa [h] using hb.2
            simp [ha.2] at this
          let c1 : Config (AgentState L K) :=
            c - ({a, b} : Multiset (AgentState L K)) +
              ({(Transition L K a b).1, (Transition L K a b).2} :
                Multiset (AgentState L K))
          have happ : ({a, b} : Multiset (AgentState L K)) ≤ c :=
            pair_le_of_mem_ne ha_mem hb_mem hne
          have hstep : (NonuniformMajority L K).StepRel c c1 := by
            refine ⟨a, b, happ, ?_⟩
            rfl
          have hreach1 : (NonuniformMajority L K).Reachable c c1 :=
            Relation.ReflTransGen.single hstep
          have hphase1 : ∀ x ∈ c1, x.phase.val = 10 :=
            phase10_phase_preserved_by_step (L := L) (K := K) c c1 hphase hstep
          have hsum1 : phase10ActiveSignedSum c1 = phase10ActiveSignedSum c :=
            phase10ActiveSignedSum_stepRel_eq (L := L) (K := K) c c1 hphase hstep
          have hneg1 : phase10ActiveSignedSum c1 < 0 := by
            rw [hsum1]
            exact hneg
          have hlt : activeACount c1 < n := by
            have hlt' :=
              activeACount_cancel_B_A_lt
                (L := L) (K := K) c hphase ha_mem hb_mem ha hb
            rw [hcount] at hlt'
            exact hlt'
          rcases ih (activeACount c1) hlt c1 rfl hphase1 hneg1 with
            ⟨d, hreach2, hphased, hnegd, hAd⟩
          exact ⟨d, Relation.ReflTransGen.trans hreach1 hreach2,
            hphased, hnegd, hAd⟩
  exact hP (activeACount c) c rfl hphase hneg

theorem phase10_broadcast_B_of_neg_no_activeA
    (c : Config (AgentState L K))
    (hphase : ∀ a ∈ c, a.phase.val = 10)
    (hneg : phase10ActiveSignedSum c < 0)
    (hnoA : activeACount c = 0) :
    ∃ d, (NonuniformMajority L K).Reachable c d ∧
      (∀ a ∈ d, a.phase.val = 10) ∧
      phase10ActiveSignedSum d < 0 ∧ activeACount d = 0 ∧
      (∀ a ∈ d, a.output = .B) := by
  classical
  let P : ℕ → Prop := fun n =>
    ∀ c : Config (AgentState L K), wrongBCount c = n →
      (∀ a ∈ c, a.phase.val = 10) → phase10ActiveSignedSum c < 0 →
      activeACount c = 0 →
      ∃ d, (NonuniformMajority L K).Reachable c d ∧
        (∀ a ∈ d, a.phase.val = 10) ∧
        phase10ActiveSignedSum d < 0 ∧ activeACount d = 0 ∧
        (∀ a ∈ d, a.output = .B)
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro c hcount hphase hneg hnoA
        by_cases hwrong_zero : wrongBCount c = 0
        · have hallB : ∀ a ∈ c, a.output = .B := by
            intro a ha
            have hnot : ¬ a.output ≠ .B := by
              exact (Multiset.countP_eq_zero.1
                (by simpa [wrongBCount] using hwrong_zero)) a ha
            by_cases hout : a.output = .B
            · exact hout
            · exact False.elim (hnot hout)
          exact ⟨c, Relation.ReflTransGen.refl, hphase, hneg, hnoA, hallB⟩
        · have hwrong_pos : 0 < wrongBCount c := Nat.pos_of_ne_zero hwrong_zero
          rcases (Multiset.countP_pos.1 (by simpa [wrongBCount] using hwrong_pos) :
              ∃ b ∈ c, b.output ≠ .B) with ⟨b, hb_mem, hb_wrong⟩
          rcases exists_activeB_of_phase10ActiveSignedSum_neg
              (L := L) (K := K) c hneg with ⟨a, ha_mem, ha⟩
          have hne : a ≠ b := ne_of_activeB_wrongB (L := L) (K := K) ha hb_wrong
          have hb_not_activeA : ¬ IsActiveA b := by
            exact (Multiset.countP_eq_zero.1 (by simpa [activeACount] using hnoA)) b hb_mem
          let c1 : Config (AgentState L K) :=
            c - ({a, b} : Multiset (AgentState L K)) +
              ({(Transition L K a b).1, (Transition L K a b).2} :
                Multiset (AgentState L K))
          have happ : ({a, b} : Multiset (AgentState L K)) ≤ c :=
            pair_le_of_mem_ne ha_mem hb_mem hne
          have hstep : (NonuniformMajority L K).StepRel c c1 := by
            refine ⟨a, b, happ, ?_⟩
            rfl
          have hreach1 : (NonuniformMajority L K).Reachable c c1 :=
            Relation.ReflTransGen.single hstep
          have hphase1 : ∀ x ∈ c1, x.phase.val = 10 :=
            phase10_phase_preserved_by_step (L := L) (K := K) c c1 hphase hstep
          have hsum1 : phase10ActiveSignedSum c1 = phase10ActiveSignedSum c :=
            phase10ActiveSignedSum_stepRel_eq (L := L) (K := K) c c1 hphase hstep
          have hneg1 : phase10ActiveSignedSum c1 < 0 := by
            rw [hsum1]
            exact hneg
          have hnoA1 : activeACount c1 = 0 :=
            activeACount_activeB_nonActiveA_eq_zero
              (L := L) (K := K) c hphase ha_mem hb_mem ha hb_wrong hb_not_activeA hnoA
          have hlt : wrongBCount c1 < n := by
            have hlt' :=
              wrongBCount_activeB_nonActiveA_lt
                (L := L) (K := K) c hphase ha_mem hb_mem ha hb_wrong hb_not_activeA
            rw [hcount] at hlt'
            exact hlt'
          rcases ih (wrongBCount c1) hlt c1 rfl hphase1 hneg1 hnoA1 with
            ⟨d, hreach2, hphased, hnegd, hnoAd, hallB⟩
          exact ⟨d, Relation.ReflTransGen.trans hreach1 hreach2,
            hphased, hnegd, hnoAd, hallB⟩
  exact hP (wrongBCount c) c rfl hphase hneg hnoA

theorem phase10_reach_unanimous_B_of_neg
    (c : Config (AgentState L K))
    (hphase : ∀ a ∈ c, a.phase.val = 10)
    (hneg : phase10ActiveSignedSum c < 0) :
    ∃ d, (NonuniformMajority L K).Reachable c d ∧
      (∀ a ∈ d, a.phase.val = 10 ∧ a.output = .B) := by
  rcases phase10_eliminate_activeA_of_neg
      (L := L) (K := K) c hphase hneg with
    ⟨d, hreach1, hphased, hnegd, hnoAd⟩
  rcases phase10_broadcast_B_of_neg_no_activeA
      (L := L) (K := K) d hphased hnegd hnoAd with
    ⟨e, hreach2, hphasee, _hnege, _hnoAe, hallB⟩
  exact ⟨e, Relation.ReflTransGen.trans hreach1 hreach2,
    fun a ha => ⟨hphasee a ha, hallB a ha⟩⟩

theorem phase10_eliminate_activeAB_of_zero
    (c : Config (AgentState L K))
    (hphase : ∀ a ∈ c, a.phase.val = 10)
    (hzero : phase10ActiveSignedSum c = 0)
    (hactive : hasActiveAgent c) :
    ∃ d, (NonuniformMajority L K).Reachable c d ∧
      (∀ a ∈ d, a.phase.val = 10) ∧
      phase10ActiveSignedSum d = 0 ∧ activeACount d = 0 ∧
      activeBCount d = 0 ∧ hasActiveAgent d := by
  classical
  let P : ℕ → Prop := fun n =>
    ∀ c : Config (AgentState L K), activeACount c = n →
      (∀ a ∈ c, a.phase.val = 10) → phase10ActiveSignedSum c = 0 →
      hasActiveAgent c →
      ∃ d, (NonuniformMajority L K).Reachable c d ∧
        (∀ a ∈ d, a.phase.val = 10) ∧
        phase10ActiveSignedSum d = 0 ∧ activeACount d = 0 ∧
        activeBCount d = 0 ∧ hasActiveAgent d
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro c hcount hphase hzero hactive
        by_cases hnoA : activeACount c = 0
        · have hnoB : activeBCount c = 0 := by
            rw [phase10ActiveSignedSum_eq_activeACount_sub_activeBCount] at hzero
            omega
          exact ⟨c, Relation.ReflTransGen.refl, hphase, hzero, hnoA, hnoB, hactive⟩
        · have hApos : 0 < activeACount c := Nat.pos_of_ne_zero hnoA
          have hcount_eq : activeACount c = activeBCount c := by
            rw [phase10ActiveSignedSum_eq_activeACount_sub_activeBCount] at hzero
            omega
          have hBpos : 0 < activeBCount c := by
            rw [← hcount_eq]
            exact hApos
          rcases (Multiset.countP_pos.1 (by simpa [activeACount] using hApos) :
              ∃ b ∈ c, IsActiveA b) with ⟨b, hb_mem, hb⟩
          rcases (Multiset.countP_pos.1 (by simpa [activeBCount] using hBpos) :
              ∃ a ∈ c, IsActiveB a) with ⟨a, ha_mem, ha⟩
          have hne : a ≠ b := by
            intro h
            have : a.output = .A := by simpa [h] using hb.2
            simp [ha.2] at this
          let c1 : Config (AgentState L K) :=
            c - ({a, b} : Multiset (AgentState L K)) +
              ({(Transition L K a b).1, (Transition L K a b).2} :
                Multiset (AgentState L K))
          have happ : ({a, b} : Multiset (AgentState L K)) ≤ c :=
            pair_le_of_mem_ne ha_mem hb_mem hne
          have hstep : (NonuniformMajority L K).StepRel c c1 := by
            refine ⟨a, b, happ, ?_⟩
            rfl
          have hreach1 : (NonuniformMajority L K).Reachable c c1 :=
            Relation.ReflTransGen.single hstep
          have hphase1 : ∀ x ∈ c1, x.phase.val = 10 :=
            phase10_phase_preserved_by_step (L := L) (K := K) c c1 hphase hstep
          have hsum1 : phase10ActiveSignedSum c1 = phase10ActiveSignedSum c :=
            phase10ActiveSignedSum_stepRel_eq (L := L) (K := K) c c1 hphase hstep
          have hzero1 : phase10ActiveSignedSum c1 = 0 := by
            rw [hsum1]
            exact hzero
          have hactive1 : hasActiveAgent c1 :=
            phase10_hasActiveAgent_preserved_by_step
              (L := L) (K := K) c c1 hphase hactive hstep
          have hlt : activeACount c1 < n := by
            have hlt' :=
              activeACount_cancel_B_A_lt
                (L := L) (K := K) c hphase ha_mem hb_mem ha hb
            rw [hcount] at hlt'
            exact hlt'
          rcases ih (activeACount c1) hlt c1 rfl hphase1 hzero1 hactive1 with
            ⟨d, hreach2, hphased, hzerod, hnoAd, hnoBd, hactived⟩
          exact ⟨d, Relation.ReflTransGen.trans hreach1 hreach2,
            hphased, hzerod, hnoAd, hnoBd, hactived⟩
  exact hP (activeACount c) c rfl hphase hzero hactive

theorem phase10_broadcast_T_of_zero_no_activeAB
    (c : Config (AgentState L K))
    (hphase : ∀ a ∈ c, a.phase.val = 10)
    (hzero : phase10ActiveSignedSum c = 0)
    (hnoA : activeACount c = 0)
    (hnoB : activeBCount c = 0)
    (hactive : hasActiveAgent c) :
    ∃ d, (NonuniformMajority L K).Reachable c d ∧
      (∀ a ∈ d, a.phase.val = 10) ∧
      phase10ActiveSignedSum d = 0 ∧ activeACount d = 0 ∧
      activeBCount d = 0 ∧ hasActiveAgent d ∧
      (∀ a ∈ d, a.output = .T) := by
  classical
  let P : ℕ → Prop := fun n =>
    ∀ c : Config (AgentState L K), wrongTCount c = n →
      (∀ a ∈ c, a.phase.val = 10) → phase10ActiveSignedSum c = 0 →
      activeACount c = 0 → activeBCount c = 0 → hasActiveAgent c →
      ∃ d, (NonuniformMajority L K).Reachable c d ∧
        (∀ a ∈ d, a.phase.val = 10) ∧
        phase10ActiveSignedSum d = 0 ∧ activeACount d = 0 ∧
        activeBCount d = 0 ∧ hasActiveAgent d ∧
        (∀ a ∈ d, a.output = .T)
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro c hcount hphase hzero hnoA hnoB hactive
        by_cases hwrong_zero : wrongTCount c = 0
        · have hallT : ∀ a ∈ c, a.output = .T := by
            intro a ha
            have hnot : ¬ a.output ≠ .T := by
              exact (Multiset.countP_eq_zero.1
                (by simpa [wrongTCount] using hwrong_zero)) a ha
            by_cases hout : a.output = .T
            · exact hout
            · exact False.elim (hnot hout)
          exact ⟨c, Relation.ReflTransGen.refl, hphase, hzero, hnoA, hnoB, hactive, hallT⟩
        · have hwrong_pos : 0 < wrongTCount c := Nat.pos_of_ne_zero hwrong_zero
          rcases (Multiset.countP_pos.1 (by simpa [wrongTCount] using hwrong_pos) :
              ∃ b ∈ c, b.output ≠ .T) with ⟨b, hb_mem, hb_wrong⟩
          rcases exists_activeT_of_hasActive_no_activeA_no_activeB
              (L := L) (K := K) c hactive hnoA hnoB with ⟨a, ha_mem, ha⟩
          have hne : a ≠ b := ne_of_activeT_wrongT (L := L) (K := K) ha hb_wrong
          have hb_not_active_biased :
              ¬ (b.full = true ∧ (b.output = .A ∨ b.output = .B)) := by
            rintro ⟨hbfull, hbout⟩
            rcases hbout with hbout | hbout
            · have hbA : IsActiveA b := ⟨hbfull, hbout⟩
              exact (Multiset.countP_eq_zero.1
                (by simpa [activeACount] using hnoA)) b hb_mem hbA
            · have hbB : IsActiveB b := ⟨hbfull, hbout⟩
              exact (Multiset.countP_eq_zero.1
                (by simpa [activeBCount] using hnoB)) b hb_mem hbB
          let c1 : Config (AgentState L K) :=
            c - ({a, b} : Multiset (AgentState L K)) +
              ({(Transition L K a b).1, (Transition L K a b).2} :
                Multiset (AgentState L K))
          have happ : ({a, b} : Multiset (AgentState L K)) ≤ c :=
            pair_le_of_mem_ne ha_mem hb_mem hne
          have hstep : (NonuniformMajority L K).StepRel c c1 := by
            refine ⟨a, b, happ, ?_⟩
            rfl
          have hreach1 : (NonuniformMajority L K).Reachable c c1 :=
            Relation.ReflTransGen.single hstep
          have hphase1 : ∀ x ∈ c1, x.phase.val = 10 :=
            phase10_phase_preserved_by_step (L := L) (K := K) c c1 hphase hstep
          have hsum1 : phase10ActiveSignedSum c1 = phase10ActiveSignedSum c :=
            phase10ActiveSignedSum_stepRel_eq (L := L) (K := K) c c1 hphase hstep
          have hzero1 : phase10ActiveSignedSum c1 = 0 := by
            rw [hsum1]
            exact hzero
          have hactive1 : hasActiveAgent c1 :=
            phase10_hasActiveAgent_preserved_by_step
              (L := L) (K := K) c c1 hphase hactive hstep
          have hnoA1 : activeACount c1 = 0 :=
            activeACount_activeT_noActiveBiased_eq_zero
              (L := L) (K := K) c hphase ha_mem hb_mem ha hb_wrong
              hb_not_active_biased hnoA
          have hnoB1 : activeBCount c1 = 0 :=
            activeBCount_activeT_noActiveBiased_eq_zero
              (L := L) (K := K) c hphase ha_mem hb_mem ha hb_wrong
              hb_not_active_biased hnoB
          have hlt : wrongTCount c1 < n := by
            have hlt' :=
              wrongTCount_activeT_noActiveBiased_lt
                (L := L) (K := K) c hphase ha_mem hb_mem ha hb_wrong
                hb_not_active_biased
            rw [hcount] at hlt'
            exact hlt'
          rcases ih (wrongTCount c1) hlt c1 rfl hphase1 hzero1 hnoA1 hnoB1 hactive1 with
            ⟨d, hreach2, hphased, hzerod, hnoAd, hnoBd, hactived, hallT⟩
          exact ⟨d, Relation.ReflTransGen.trans hreach1 hreach2,
            hphased, hzerod, hnoAd, hnoBd, hactived, hallT⟩
  exact hP (wrongTCount c) c rfl hphase hzero hnoA hnoB hactive

theorem phase10_reach_unanimous_T_of_zero
    (init c : Config (AgentState L K))
    (hinit : validInitial init)
    (hreach : (NonuniformMajority L K).Reachable init c)
    (hphase : ∀ a ∈ c, a.phase.val = 10)
    (hzero : phase10ActiveSignedSum c = 0) :
    ∃ d, (NonuniformMajority L K).Reachable c d ∧
      (∀ a ∈ d, a.phase.val = 10 ∧ a.output = .T) := by
  rcases card_eq_zero_or_hasActiveAgent_of_reachable_all_phase10
      (L := L) (K := K) init c hinit hreach hphase with hcard | hactive
  · refine ⟨c, Relation.ReflTransGen.refl, ?_⟩
    have hempty : c = 0 := Multiset.card_eq_zero.1 hcard
    intro a ha
    rw [hempty] at ha
    simp at ha
  · rcases phase10_eliminate_activeAB_of_zero
        (L := L) (K := K) c hphase hzero hactive with
      ⟨d, hreach1, hphased, hzerod, hnoAd, hnoBd, hactived⟩
    rcases phase10_broadcast_T_of_zero_no_activeAB
        (L := L) (K := K) d hphased hzerod hnoAd hnoBd hactived with
      ⟨e, hreach2, hphasee, _hzeroe, _hnoAe, _hnoBe, _hactivee, hallT⟩
    exact ⟨e, Relation.ReflTransGen.trans hreach1 hreach2,
      fun a ha => ⟨hphasee a ha, hallT a ha⟩⟩

/-- Direct Phase-10 initialization sets the active signed contribution equal to
the immutable input contribution.  Note: the current implementation initializes
Phase-10 output from `input`, not from dyadic bias. -/
theorem signedContribution_phaseInit_phase10
    (a : AgentState L K) :
    signedContribution (phaseInit L K phase10 a) = AgentState.inputBiasInt a := by
  rcases a with
    ⟨ainput, aoutput, aphase, arole, aassigned, abias, asmallBias,
      ahour, aminute, afull, aopinions, acounter⟩
  cases ainput <;> simp [signedContribution, phaseInit, phase10, AgentState.inputBiasInt]

/-- If every agent is directly initialized into Phase 10 by `phaseInit 10`,
the active signed sum is exactly the initial input gap. -/
theorem phase10ActiveSignedSum_phaseInit_phase10_eq_initialGap
    (c : Config (AgentState L K)) :
    phase10ActiveSignedSum (c.map (phaseInit L K phase10)) = initialGap c := by
  rw [← inputBiasSum_initialGap (L := L) (K := K) c]
  induction c using Multiset.induction_on with
  | empty =>
      simp [phase10ActiveSignedSum, inputBiasSum]
  | cons a c ih =>
      simp [phase10ActiveSignedSum, inputBiasSum, signedContribution_phaseInit_phase10]

/-- Simplest terminal Phase-10 case: if a configuration is already in Phase 10
and already has the correct partition output, then it is already a Phase-10
majority witness. -/
theorem phase10_backup_reachability_of_phase10_partition_output
    (init c : Config (AgentState L K))
    (hphase : ∀ a ∈ c, a.phase.val = 10)
    (hout : (doutPartition L K).output (majorityVerdict init) c) :
    ∃ final, (NonuniformMajority L K).Reachable c final ∧
      phase10MajorityWitness (L := L) (K := K) init final := by
  refine ⟨c, Relation.ReflTransGen.refl, ?_⟩
  exact phase10MajorityWitness_of_phase10_partition_output
    (L := L) (K := K) init c hphase hout

/-- End-to-end Phase-10 backup reachability.  Once a reachable execution has
entered the all-Phase-10 region, the slow backup protocol can be scheduled to a
stable unanimous endpoint matching the initial input majority. -/
theorem phase10_backup_reachability
    (init c : Config (AgentState L K))
    (hinit : validInitial init)
    (hreach : (NonuniformMajority L K).Reachable init c)
    (hphase10 : ∀ a ∈ c, a.phase.val = 10) :
    ∃ final, (NonuniformMajority L K).Reachable c final ∧
      phase10MajorityWitness (L := L) (K := K) init final := by
  have hsum :
      phase10ActiveSignedSum c = initialGap init :=
    phase10ActiveSignedSum_eq_initialGap_of_reachable
      (L := L) (K := K) init c hinit hreach hphase10
  by_cases hpos : 0 < initialGap init
  · have hpos_sum : 0 < phase10ActiveSignedSum c := by
      rw [hsum]
      exact hpos
    rcases phase10_reach_unanimous_A_of_pos
        (L := L) (K := K) c hphase10 hpos_sum with
      ⟨final, hreach_final, hfinal⟩
    exact ⟨final, hreach_final, Or.inl ⟨hpos, hfinal⟩⟩
  · by_cases hneg : initialGap init < 0
    · have hneg_sum : phase10ActiveSignedSum c < 0 := by
        rw [hsum]
        exact hneg
      rcases phase10_reach_unanimous_B_of_neg
          (L := L) (K := K) c hphase10 hneg_sum with
        ⟨final, hreach_final, hfinal⟩
      exact ⟨final, hreach_final, Or.inr (Or.inl ⟨hneg, hfinal⟩)⟩
    · have hzero_gap : initialGap init = 0 := by omega
      have hzero_sum : phase10ActiveSignedSum c = 0 := by
        rw [hsum]
        exact hzero_gap
      rcases phase10_reach_unanimous_T_of_zero
          (L := L) (K := K) init c hinit hreach hphase10 hzero_sum with
        ⟨final, hreach_final, hfinal⟩
      exact ⟨final, hreach_final, Or.inr (Or.inr ⟨hzero_gap, hfinal⟩)⟩

/-- Maximum phase present in a configuration, with value `0` for the empty
configuration. -/
def maxPhase (c : Config (AgentState L K)) : ℕ :=
  c.toFinset.sup (fun a => a.phase.val)

/-- Phase deficit from the terminal Phase-10 level. -/
def phaseDeficit (a : AgentState L K) : ℕ :=
  10 - a.phase.val

/-- Total phase deficit in a configuration. -/
def phaseDeficitSum (c : Config (AgentState L K)) : ℕ :=
  (c.map phaseDeficit).sum

private lemma phase_le_maxPhase_of_mem {c : Config (AgentState L K)}
    {a : AgentState L K} (ha : a ∈ c) :
    a.phase.val ≤ maxPhase c := by
  unfold maxPhase
  exact Finset.le_sup (f := fun a : AgentState L K => a.phase.val) (by simpa using ha)

private lemma exists_mem_phase_eq_maxPhase {c : Config (AgentState L K)}
    (hpos : 0 < maxPhase c) :
    ∃ a ∈ c, a.phase.val = maxPhase c := by
  unfold maxPhase at hpos
  have hle :
      c.toFinset.sup (fun a : AgentState L K => a.phase.val) ≤
        c.toFinset.sup (fun a : AgentState L K => a.phase.val) := le_rfl
  rw [Finset.le_sup_iff hpos] at hle
  rcases hle with ⟨a, ha, hmax_le⟩
  have ha_mem : a ∈ c := by simpa using ha
  have ha_le := phase_le_maxPhase_of_mem (L := L) (K := K) ha_mem
  exact ⟨a, ha_mem, le_antisymm ha_le hmax_le⟩

private lemma phaseDeficit_le_of_phase_ge {a b : AgentState L K}
    (h : a.phase.val ≤ b.phase.val) :
    phaseDeficit b ≤ phaseDeficit a := by
  unfold phaseDeficit
  omega

private lemma phaseDeficit_lt_of_phase_gt {a b : AgentState L K}
    (h : a.phase.val < b.phase.val) :
    phaseDeficit b < phaseDeficit a := by
  unfold phaseDeficit
  omega

private lemma phaseDeficitSum_step_lt_of_phase_lt
    {c : Config (AgentState L K)} {hi lo : AgentState L K}
    (hpair : ({hi, lo} : Multiset (AgentState L K)) ≤ c)
    (hlt : lo.phase.val < hi.phase.val) :
    phaseDeficitSum
        (c - ({hi, lo} : Multiset (AgentState L K)) +
          ({(Transition L K hi lo).1, (Transition L K hi lo).2} :
            Multiset (AgentState L K))) <
      phaseDeficitSum c := by
  let residual := c - ({hi, lo} : Multiset (AgentState L K))
  let p₁ := (Transition L K hi lo).1
  let p₂ := (Transition L K hi lo).2
  have hrestore :
      residual + ({hi, lo} : Multiset (AgentState L K)) = c := by
    simpa [residual] using Multiset.sub_add_cancel hpair
  have hsum_c :
      phaseDeficitSum c =
        phaseDeficitSum residual + (phaseDeficit hi + phaseDeficit lo) := by
    rw [← hrestore]
    simp [phaseDeficitSum, phaseDeficit, residual, add_comm, add_left_comm, add_assoc]
  have hsum_next :
      phaseDeficitSum
          (c - ({hi, lo} : Multiset (AgentState L K)) +
            ({(Transition L K hi lo).1, (Transition L K hi lo).2} :
              Multiset (AgentState L K))) =
        phaseDeficitSum residual + (phaseDeficit p₁ + phaseDeficit p₂) := by
    simp [phaseDeficitSum, phaseDeficit, residual, p₁, p₂, add_comm, add_left_comm,
      add_assoc]
  have hp₁_ge : hi.phase.val ≤ p₁.phase.val := by
    have hmono := Transition_phase_monotone (L := L) (K := K) hi lo
    change hi.phase.val ≤ (Transition L K hi lo).1.phase.val
    exact hmono.1
  have hmax_eq : max hi.phase.val lo.phase.val = hi.phase.val :=
    max_eq_left (Nat.le_of_lt hlt)
  have hp₂_gt : lo.phase.val < p₂.phase.val := by
    have hge := Transition_right_phase_ge_pair_max (L := L) (K := K) hi lo
    have hhi_le : hi.phase.val ≤ p₂.phase.val := by simpa [hmax_eq, p₂] using hge
    omega
  have hdef₁ : phaseDeficit p₁ ≤ phaseDeficit hi :=
    phaseDeficit_le_of_phase_ge (L := L) (K := K) hp₁_ge
  have hdef₂ : phaseDeficit p₂ < phaseDeficit lo :=
    phaseDeficit_lt_of_phase_gt (L := L) (K := K) hp₂_gt
  rw [hsum_next, hsum_c]
  omega

private theorem phase_epidemic_reachability_from_config_aux :
    ∀ n, ∀ c : Config (AgentState L K),
      phaseDeficitSum c = n →
      2 ≤ c.card →
      ∃ final, (NonuniformMajority L K).Reachable c final ∧
        (∀ a ∈ final, a.phase.val = maxPhase final) ∧
        maxPhase c ≤ maxPhase final := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro c hsum hn
      by_cases hall : ∀ a ∈ c, a.phase.val = maxPhase c
      · exact ⟨c, Relation.ReflTransGen.refl, hall, le_rfl⟩
      · push_neg at hall
        rcases hall with ⟨lo, hlo_mem, hlo_ne⟩
        have hlo_le := phase_le_maxPhase_of_mem (L := L) (K := K) hlo_mem
        have hlo_lt : lo.phase.val < maxPhase c := by omega
        have hmax_pos : 0 < maxPhase c := by omega
        rcases exists_mem_phase_eq_maxPhase (L := L) (K := K) hmax_pos with
          ⟨hi, hhi_mem, hhi_phase⟩
        have hphase_lt : lo.phase.val < hi.phase.val := by omega
        have hne : hi ≠ lo := by
          intro h
          subst hi
          omega
        let c₁ :=
          c - ({hi, lo} : Multiset (AgentState L K)) +
            ({(Transition L K hi lo).1, (Transition L K hi lo).2} :
              Multiset (AgentState L K))
        have hpair : ({hi, lo} : Multiset (AgentState L K)) ≤ c :=
          pair_le_of_mem_ne hhi_mem hlo_mem hne
        have hstep : (NonuniformMajority L K).StepRel c c₁ := by
          exact ⟨hi, lo, hpair, by simp [c₁, NonuniformMajority]⟩
        have hreach₁ : (NonuniformMajority L K).Reachable c c₁ :=
          Relation.ReflTransGen.single hstep
        have hn₁ : 2 ≤ c₁.card := by
          have hcard := Protocol.stepRel_card_eq (P := NonuniformMajority L K) hstep
          omega
        have hdef_lt : phaseDeficitSum c₁ < n := by
          rw [← hsum]
          simpa [c₁] using
            phaseDeficitSum_step_lt_of_phase_lt (L := L) (K := K) hpair hphase_lt
        have hmax_step : maxPhase c ≤ maxPhase c₁ := by
          have hp₁_mem : (Transition L K hi lo).1 ∈ c₁ := by
            dsimp [c₁]
            exact Multiset.mem_add.2 (Or.inr (Multiset.mem_cons_self _ _))
          have hp₁_ge : maxPhase c ≤ (Transition L K hi lo).1.phase.val := by
            have hge := Transition_left_phase_ge_pair_max (L := L) (K := K) hi lo
            have hmax_eq : max hi.phase.val lo.phase.val = hi.phase.val :=
              max_eq_left (Nat.le_of_lt hphase_lt)
            have hhi_ge : hi.phase.val ≤ (Transition L K hi lo).1.phase.val := by
              simpa [hmax_eq] using hge
            omega
          have hp₁_le := phase_le_maxPhase_of_mem (L := L) (K := K) hp₁_mem
          exact le_trans hp₁_ge hp₁_le
        rcases ih (phaseDeficitSum c₁) hdef_lt c₁ rfl hn₁ with
          ⟨final, hreach_final, hphase_final, hmax_final⟩
        exact ⟨final, Relation.ReflTransGen.trans hreach₁ hreach_final,
          hphase_final, le_trans hmax_step hmax_final⟩

/-- Strong phase-epidemic liveness: from any configuration with at least two
agents, one can schedule interactions until all agents have the same phase.
The common phase is the final configuration's maximum phase, and the maximum
phase never decreases along this scheduled reachability witness. -/
theorem phase_epidemic_reachability_from_config
    (c : Config (AgentState L K))
    (hn : 2 ≤ c.card) :
    ∃ final, (NonuniformMajority L K).Reachable c final ∧
      (∀ a ∈ final, a.phase.val = maxPhase final) ∧
      maxPhase c ≤ maxPhase final :=
  phase_epidemic_reachability_from_config_aux
    (L := L) (K := K) (phaseDeficitSum c) c rfl hn

/-- Phase-epidemic liveness for reachable configurations.  The validity and
reachability hypotheses are not needed for the epidemic argument itself; they
are kept here to match the end-to-end exact-majority API. -/
theorem phase_epidemic_reachability
    (init c : Config (AgentState L K))
    (_hinit : validInitial init)
    (_hreach : (NonuniformMajority L K).Reachable init c)
    (hn : 2 ≤ c.card) :
    ∃ final, (NonuniformMajority L K).Reachable c final ∧
      (∀ a ∈ final, a.phase.val = maxPhase final) ∧
      maxPhase c ≤ maxPhase final :=
  phase_epidemic_reachability_from_config (L := L) (K := K) c hn

end ExactMajority
