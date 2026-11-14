import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockMainLedger
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase2AdvanceEpidemic

/-!
# The P11 ledger on every virtual step (N12, Main row: activation and self-advance)

`PhaseThreeClockMainLedger.virtualRule_ledger` is the P11 pair ledger on two Phase-3
agents. The Main row of PHASE3 is charged from the first seed, when agents are still in
Phases 1 and 2; those agents enter Phase 3 either through the phase epidemic
(`runInitsBetween` on an interaction with an active partner, followed by the Phase-3
rule on the initialized pair) or through the Phase-2 rule's own advance
(`advancePhaseWithInit`). In both cases the Phase-3 initializer writes hour zero and a
bias of index zero (`Phase3Pre3.Phase3EntryAgent`), so the freshly active Main carries no
outlier credit and cannot take part in a deep cancellation, and the activation contact
with a high Clock is counted by `contactInd` (whose Main side may be inactive).

`virtualRule_step_ledger`: the P11 pair ledger for the virtual rule on any two agents in
Phases 1–3 whose outputs stay in Phases ≤ 3 (no backup) and whose Clocks carry the
neutral small bias (the carrier invariant of the clock analysis).
-/

noncomputable section

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockMainActivation

open PhaseThreeClockVirtual PhaseThreeClockGatedLaw PhaseThreeClockEmbedding
  PhaseThreeClockEmbeddingBridge PhaseThreeClockMainLedger

variable {L K : ℕ}

/-! ## Fresh Phase-3 agents carry no credit -/

theorem phase3BiasOfSmallBias_index_zero (sb : Fin 7) (σ : Sign) (j : Fin (L + 1))
    (h : Phase3Pre3.phase3BiasOfSmallBias (L := L) sb = Bias.dyadic σ j) : j.val = 0 := by
  simp only [Phase3Pre3.phase3BiasOfSmallBias] at h
  split_ifs at h <;> simp only [Bias.dyadic.injEq, reduceCtorEq] at h
  · exact (congrArg Fin.val h.2).symm
  · exact (congrArg Fin.val h.2).symm

theorem mainFieldsLe_of_entry (h : ℕ) (a : AgentState L K)
    (ha : Phase3Pre3.Phase3EntryAgent a) : MainFieldsLe h a := by
  intro _ hm
  refine ⟨by rw [Phase3Pre3.main_hour_zero_of_Phase3EntryAgent ha hm]; exact Nat.zero_le _, ?_⟩
  intro σ j hb
  rw [Phase3Pre3.main_bias_of_Phase3EntryAgent ha hm] at hb
  rw [phase3BiasOfSmallBias_index_zero a.smallBias σ j hb]
  exact Nat.zero_le _

theorem creditV_eq_zero_of_entry (h : ℕ) (a : AgentState L K)
    (ha : Phase3Pre3.Phase3EntryAgent a) : creditV h a = 0 :=
  creditV_eq_zero_of_mainFieldsLe (mainFieldsLe_of_entry h a ha)

theorem highHourInd_eq_zero_of_entry (h : ℕ) (a : AgentState L K)
    (ha : Phase3Pre3.Phase3EntryAgent a) : highHourInd h a = 0 :=
  highHourInd_eq_zero_of_mainFieldsLe (mainFieldsLe_of_entry h a ha)

/-- A cancellation against an index-zero biased agent has no deep credit. -/
theorem cancelIdx_right_zero (h : ℕ) (b : Bias L) (σ : Sign) (j : Fin (L + 1))
    (hj : j.val = 0) : cancelIdx h b (Bias.dyadic σ j) = 0 := by
  cases b with
  | zero => simp [cancelIdx]
  | dyadic τ i =>
      cases τ <;> cases σ <;> simp only [cancelIdx] <;> split_ifs <;> omega

theorem cancelIdx_left_zero (h : ℕ) (b : Bias L) (σ : Sign) (j : Fin (L + 1))
    (hj : j.val = 0) : cancelIdx h (Bias.dyadic σ j) b = 0 := by
  cases b with
  | zero => cases σ <;> simp [cancelIdx]
  | dyadic τ i =>
      cases τ <;> cases σ <;> simp only [cancelIdx] <;> split_ifs <;> omega

/-- A fresh agent is never the deep side of a cancellation. -/
theorem cancelIdx_eq_zero_of_entry_right (h : ℕ) (s a : AgentState L K)
    (ha : Phase3Pre3.Phase3EntryAgent a) (hm : a.role = .main) :
    cancelIdx h s.bias a.bias = 0 := by
  rw [Phase3Pre3.main_bias_of_Phase3EntryAgent ha hm]
  simp only [Phase3Pre3.phase3BiasOfSmallBias]
  split_ifs
  · exact cancelIdx_right_zero h s.bias .neg _ rfl
  · exact cancelIdx_right_zero h s.bias .pos _ rfl
  · cases s.bias <;> simp [cancelIdx]

theorem cancelIdx_eq_zero_of_entry_left (h : ℕ) (a t : AgentState L K)
    (ha : Phase3Pre3.Phase3EntryAgent a) (hm : a.role = .main) :
    cancelIdx h a.bias t.bias = 0 := by
  rw [Phase3Pre3.main_bias_of_Phase3EntryAgent ha hm]
  simp only [Phase3Pre3.phase3BiasOfSmallBias]
  split_ifs
  · exact cancelIdx_left_zero h t.bias .neg _ rfl
  · exact cancelIdx_left_zero h t.bias .pos _ rfl
  · cases t.bias <;> simp [cancelIdx]

/-! ## The Phase-3 initializer on a raised agent -/

/-- The Phase-3 initializer on an agent raised to Phase 3 is an entry agent. -/
theorem entry_of_phaseInit_three (a : AgentState L K) :
    Phase3Pre3.Phase3EntryAgent
      (phaseInit L K ⟨3, by decide⟩ { a with phase := ⟨3, by decide⟩ }) := by
  rcases a with
    ⟨input, output, phase, role, assigned, bias, smallBias, hour, minute, full, opinions, counter⟩
  cases role <;>
    simp [Phase3Pre3.Phase3EntryAgent, Phase3Pre3.phase3BiasOfSmallBias, phaseInit]

/-- The Phase-2 initializer either enters the backup track or only rewrites the
opinions. -/
theorem phaseInit_two_cases (a : AgentState L K) :
    phaseInit L K ⟨2, by decide⟩ a = enterPhase10 L K a ∨
      ∃ o : Fin 8, phaseInit L K ⟨2, by decide⟩ a = { a with opinions := o } := by
  by_cases hb : a.smallBias.val ≤ 1 ∨ 5 ≤ a.smallBias.val
  · left
    simp [phaseInit, hb]
  · right
    refine ⟨if a.smallBias.val < 3 then ⟨1, by decide⟩ else
      if a.smallBias.val = 3 then ⟨2, by decide⟩ else ⟨4, by decide⟩, ?_⟩
    simp [phaseInit, hb]

/-- The initializer chain from Phase `p ∈ {1, 2}` to Phase 3 on an agent raised to Phase 3
is an entry agent unless it enters the backup track. -/
theorem entry_of_runInits (p : ℕ) (hp1 : 1 ≤ p) (hp2 : p ≤ 2) (a : AgentState L K)
    (hne : (runInitsBetween L K p 3 { a with phase := ⟨3, by decide⟩ }).phase.val ≠ 10) :
    Phase3Pre3.Phase3EntryAgent (runInitsBetween L K p 3 { a with phase := ⟨3, by decide⟩ }) := by
  interval_cases p
  · have hl : (List.range 11).filter (fun k => 1 < k ∧ k ≤ 3) = [2, 3] := by decide
    unfold runInitsBetween at hne ⊢
    rw [hl] at hne ⊢
    simp only [List.foldl] at hne ⊢
    rw [dif_pos (by norm_num : (2 : ℕ) < 11), dif_pos (by norm_num : (3 : ℕ) < 11)] at hne ⊢
    rcases phaseInit_two_cases (L := L) (K := K) { a with phase := ⟨3, by decide⟩ } with h2 | ⟨o, h2⟩
    · exfalso
      rw [h2] at hne
      rcases phaseInit_phase_eq_or_ten' (L := L) (K := K) ⟨3, by decide⟩
        (enterPhase10 L K { a with phase := ⟨3, by decide⟩ }) with h3 | h3
      · rw [h3] at hne
        exact hne (by simp [enterPhase10])
      · exact hne h3
    · rw [h2]
      exact entry_of_phaseInit_three { a with opinions := o }
  · have hl : (List.range 11).filter (fun k => 2 < k ∧ k ≤ 3) = [3] := by decide
    unfold runInitsBetween
    rw [hl]
    simp only [List.foldl]
    rw [dif_pos (by norm_num : (3 : ℕ) < 11)]
    exact entry_of_phaseInit_three a

/-! ## One active partner: the epidemic initializes the other -/

/-- The initialized partner of an activation step. -/
def initPartner (s t : AgentState L K) : AgentState L K :=
  runInitsBetween L K t.phase.val 3 { t with phase := ⟨3, by decide⟩ }

theorem initPartner_role (s t : AgentState L K) (ht1 : 1 ≤ t.phase.val) :
    (initPartner s t).role = t.role :=
  runInitsBetween_role_of_one_le _ _ ht1 _

/-- The phase epidemic on an active `s` and an inactive `t` (no backup). -/
theorem epidemic_activation (s t : AgentState L K) (hs3 : s.phase.val = 3)
    (ht1 : 1 ≤ t.phase.val) (ht2 : t.phase.val ≤ 2)
    (hnb : (phaseEpidemicUpdate L K s t).1.phase.val ≠ 10 ∧
      (phaseEpidemicUpdate L K s t).2.phase.val ≠ 10) :
    phaseEpidemicUpdate L K s t = (s, initPartner s t) := by
  have hmax : max s.phase t.phase = s.phase :=
    max_eq_left (Fin.le_iff_val_le_val.mpr (by omega))
  have hs3' : s.phase = ⟨3, by decide⟩ := Fin.ext hs3
  rw [phaseEpidemicUpdate_eq_of_no_backup s t (by omega) (by omega) hnb, hmax,
    runInitsBetween_self]
  refine Prod.ext rfl ?_
  show runInitsBetween L K t.phase.val s.phase.val { t with phase := s.phase } = initPartner s t
  rw [hs3']
  rfl

theorem initPartner_entry (s t : AgentState L K) (hs3 : s.phase.val = 3)
    (ht1 : 1 ≤ t.phase.val) (ht2 : t.phase.val ≤ 2)
    (hnb : (phaseEpidemicUpdate L K s t).1.phase.val ≠ 10 ∧
      (phaseEpidemicUpdate L K s t).2.phase.val ≠ 10) :
    Phase3Pre3.Phase3EntryAgent (initPartner s t) := by
  have h := hnb.2
  rw [epidemic_activation s t hs3 ht1 ht2 hnb] at h
  exact entry_of_runInits t.phase.val ht1 ht2 t h

/-- The virtual rule on an activation step is the virtual rule on the initialized
pair. -/
theorem virtualRule_activation (s t : AgentState L K) (hs3 : s.phase.val = 3)
    (ht1 : 1 ≤ t.phase.val) (ht2 : t.phase.val ≤ 2)
    (hnb : (phaseEpidemicUpdate L K s t).1.phase.val ≠ 10 ∧
      (phaseEpidemicUpdate L K s t).2.phase.val ≠ 10) :
    virtualRule s t = virtualRule s (initPartner s t) := by
  have hepi := epidemic_activation s t hs3 ht1 ht2 hnb
  have hentry := initPartner_entry s t hs3 ht1 ht2 hnb
  have hepi' : phaseEpidemicUpdate L K s (initPartner s t) = (s, initPartner s t) :=
    ClockRealKernel.phaseEpidemicUpdate_eq_self_p3 s _ hs3 hentry.1
  have hT : Transition L K s t = Transition L K s (initPartner s t) := by
    unfold Transition
    rw [hepi, hepi']
  have hC : CapCounterPair s t ↔ CapCounterPair s (initPartner s t) := by
    unfold CapCounterPair
    rw [hepi, hepi']
  unfold virtualRule
  by_cases hc : CapCounterPair s t
  · rw [if_pos hc, if_pos (hC.mp hc), hepi, hepi']
  · rw [if_neg hc, if_neg (fun h => hc (hC.mpr h)), hT]

/-- The symmetric activation step. -/
theorem epidemic_activation_left (s t : AgentState L K) (ht3 : t.phase.val = 3)
    (hs1 : 1 ≤ s.phase.val) (hs2 : s.phase.val ≤ 2)
    (hnb : (phaseEpidemicUpdate L K s t).1.phase.val ≠ 10 ∧
      (phaseEpidemicUpdate L K s t).2.phase.val ≠ 10) :
    phaseEpidemicUpdate L K s t = (initPartner t s, t) := by
  have hmax : max s.phase t.phase = t.phase :=
    max_eq_right (Fin.le_iff_val_le_val.mpr (by omega))
  have ht3' : t.phase = ⟨3, by decide⟩ := Fin.ext ht3
  rw [phaseEpidemicUpdate_eq_of_no_backup s t (by omega) (by omega) hnb, hmax,
    runInitsBetween_self]
  refine Prod.ext ?_ rfl
  show runInitsBetween L K s.phase.val t.phase.val { s with phase := t.phase } = initPartner t s
  rw [ht3']
  rfl

theorem initPartner_entry_left (s t : AgentState L K) (ht3 : t.phase.val = 3)
    (hs1 : 1 ≤ s.phase.val) (hs2 : s.phase.val ≤ 2)
    (hnb : (phaseEpidemicUpdate L K s t).1.phase.val ≠ 10 ∧
      (phaseEpidemicUpdate L K s t).2.phase.val ≠ 10) :
    Phase3Pre3.Phase3EntryAgent (initPartner t s) := by
  have h := hnb.1
  rw [epidemic_activation_left s t ht3 hs1 hs2 hnb] at h
  exact entry_of_runInits s.phase.val hs1 hs2 s h

theorem virtualRule_activation_left (s t : AgentState L K) (ht3 : t.phase.val = 3)
    (hs1 : 1 ≤ s.phase.val) (hs2 : s.phase.val ≤ 2)
    (hnb : (phaseEpidemicUpdate L K s t).1.phase.val ≠ 10 ∧
      (phaseEpidemicUpdate L K s t).2.phase.val ≠ 10) :
    virtualRule s t = virtualRule (initPartner t s) t := by
  have hepi := epidemic_activation_left s t ht3 hs1 hs2 hnb
  have hentry := initPartner_entry_left s t ht3 hs1 hs2 hnb
  have hepi' : phaseEpidemicUpdate L K (initPartner t s) t = (initPartner t s, t) :=
    ClockRealKernel.phaseEpidemicUpdate_eq_self_p3 _ t hentry.1 ht3
  have hT : Transition L K s t = Transition L K (initPartner t s) t := by
    unfold Transition
    rw [hepi, hepi']
  have hC : CapCounterPair s t ↔ CapCounterPair (initPartner t s) t := by
    unfold CapCounterPair
    rw [hepi, hepi']
  unfold virtualRule
  by_cases hc : CapCounterPair s t
  · rw [if_pos hc, if_pos (hC.mp hc), hepi, hepi']
  · rw [if_neg hc, if_neg (fun h => hc (hC.mpr h)), hT]

/-! ## Transfer of the credits from the initialized pair -/

theorem contactInd_initPartner (hK : 0 < K) (h : ℕ) (s t : AgentState L K)
    (ht1 : 1 ≤ t.phase.val) (ht2 : t.phase.val ≤ 2)
    (hentry : Phase3Pre3.Phase3EntryAgent (initPartner s t)) :
    contactInd h s (initPartner s t) = contactInd h s t := by
  have hrole := initPartner_role s t ht1
  unfold contactInd
  have h1 : ¬ (s.role = .main ∧ (initPartner s t).role = .clock ∧
      3 ≤ (initPartner s t).phase.val ∧ (h + 1) * K ≤ (initPartner s t).minute.val) := by
    rintro ⟨-, hc, -, hm⟩
    rw [Phase3Pre3.clock_minute_zero_of_Phase3EntryAgent hentry hc] at hm
    have : 1 ≤ (h + 1) * K := Nat.mul_pos (Nat.succ_pos h) hK
    omega
  have h2 : ¬ (s.role = .main ∧ t.role = .clock ∧ 3 ≤ t.phase.val ∧
      (h + 1) * K ≤ t.minute.val) := by
    rintro ⟨-, -, h3, -⟩
    omega
  simp only [h1, h2, false_or]
  simp only [hrole]

theorem contactInd_initPartner_left (hK : 0 < K) (h : ℕ) (s t : AgentState L K)
    (hs1 : 1 ≤ s.phase.val) (hs2 : s.phase.val ≤ 2)
    (hentry : Phase3Pre3.Phase3EntryAgent (initPartner t s)) :
    contactInd h (initPartner t s) t = contactInd h s t := by
  have hrole := initPartner_role t s hs1
  unfold contactInd
  have h1 : ¬ (t.role = .main ∧ (initPartner t s).role = .clock ∧
      3 ≤ (initPartner t s).phase.val ∧ (h + 1) * K ≤ (initPartner t s).minute.val) := by
    rintro ⟨-, hc, -, hm⟩
    rw [Phase3Pre3.clock_minute_zero_of_Phase3EntryAgent hentry hc] at hm
    have : 1 ≤ (h + 1) * K := Nat.mul_pos (Nat.succ_pos h) hK
    omega
  have h2 : ¬ (t.role = .main ∧ s.role = .clock ∧ 3 ≤ s.phase.val ∧
      (h + 1) * K ≤ s.minute.val) := by
    rintro ⟨-, -, h3, -⟩
    omega
  simp only [h1, h2, or_false]
  simp only [hrole]

theorem deepCancelInd_initPartner (h : ℕ) (s t : AgentState L K) (ht1 : 1 ≤ t.phase.val)
    (hentry : Phase3Pre3.Phase3EntryAgent (initPartner s t)) :
    deepCancelInd h s (initPartner s t) = 0 := by
  unfold deepCancelInd
  split_ifs with hc
  · exact cancelIdx_eq_zero_of_entry_right h s _ hentry hc.2.2.2
  · rfl

theorem deepCancelInd_initPartner_left (h : ℕ) (s t : AgentState L K) (hs1 : 1 ≤ s.phase.val)
    (hentry : Phase3Pre3.Phase3EntryAgent (initPartner t s)) :
    deepCancelInd h (initPartner t s) t = 0 := by
  unfold deepCancelInd
  split_ifs with hc
  · exact cancelIdx_eq_zero_of_entry_left h _ t hentry hc.2.2.1
  · rfl

theorem deepCancelInd_eq_zero_of_inactive_right (h : ℕ) (s t : AgentState L K)
    (ht : t.phase.val < 3) : deepCancelInd h s t = 0 := by
  unfold deepCancelInd
  rw [if_neg (fun hc => by omega)]

theorem deepCancelInd_eq_zero_of_inactive_left (h : ℕ) (s t : AgentState L K)
    (hs : s.phase.val < 3) : deepCancelInd h s t = 0 := by
  unfold deepCancelInd
  rw [if_neg (fun hc => by omega)]

/-- The ledger on an activation step (active `s`, inactive `t`). -/
theorem virtualRule_ledger_activation (hK : 0 < K) (h : ℕ) (s t : AgentState L K)
    (hs3 : s.phase.val = 3) (ht1 : 1 ≤ t.phase.val) (ht2 : t.phase.val ≤ 2)
    (hsout : (virtualRule s t).1.phase.val ≤ 3) (htout : (virtualRule s t).2.phase.val ≤ 3) :
    PairLedger h s t (virtualRule s t).1 (virtualRule s t).2 := by
  have hnb := virtualRule_no_backup_of_phase_le_three s t hsout htout
  have hentry := initPartner_entry s t hs3 ht1 ht2 hnb
  rw [virtualRule_activation s t hs3 ht1 ht2 hnb]
  have hl := virtualRule_ledger h s (initPartner s t) hs3 hentry.1
  have e1 := creditV_eq_zero_of_entry h _ hentry
  have e2 := highHourInd_eq_zero_of_entry h _ hentry
  have e3 := creditV_eq_zero_of_inactive h t (by omega)
  have e4 := highHourInd_eq_zero_of_inactive h t (by omega)
  have e5 := contactInd_initPartner hK h s t ht1 ht2 hentry
  have e6 := deepCancelInd_initPartner h s t ht1 hentry
  have e7 := deepCancelInd_eq_zero_of_inactive_right h s t (by omega)
  have hv := hl.v
  have hh := hl.hh
  rw [e1, e5, e6] at hv
  rw [e2, e5, e6] at hh
  exact ⟨by omega, by omega⟩

/-- The ledger on an activation step (inactive `s`, active `t`). -/
theorem virtualRule_ledger_activation_left (hK : 0 < K) (h : ℕ) (s t : AgentState L K)
    (ht3 : t.phase.val = 3) (hs1 : 1 ≤ s.phase.val) (hs2 : s.phase.val ≤ 2)
    (hsout : (virtualRule s t).1.phase.val ≤ 3) (htout : (virtualRule s t).2.phase.val ≤ 3) :
    PairLedger h s t (virtualRule s t).1 (virtualRule s t).2 := by
  have hnb := virtualRule_no_backup_of_phase_le_three s t hsout htout
  have hentry := initPartner_entry_left s t ht3 hs1 hs2 hnb
  rw [virtualRule_activation_left s t ht3 hs1 hs2 hnb]
  have hl := virtualRule_ledger h (initPartner t s) t hentry.1 ht3
  have e1 := creditV_eq_zero_of_entry h _ hentry
  have e2 := highHourInd_eq_zero_of_entry h _ hentry
  have e3 := creditV_eq_zero_of_inactive h s (by omega)
  have e4 := highHourInd_eq_zero_of_inactive h s (by omega)
  have e5 := contactInd_initPartner_left hK h s t hs1 hs2 hentry
  have e6 := deepCancelInd_initPartner_left h s t hs1 hentry
  have e7 := deepCancelInd_eq_zero_of_inactive_left h s t (by omega)
  have hv := hl.v
  have hh := hl.hh
  rw [e1, e5, e6] at hv
  rw [e2, e5, e6] at hh
  exact ⟨by omega, by omega⟩

/-! ## Two inactive agents: the outputs are inactive or fresh -/

/-- An output agent carries no credit: it is inactive or an entry agent. -/
def NoCredit (a : AgentState L K) : Prop :=
  a.phase.val < 3 ∨ Phase3Pre3.Phase3EntryAgent a

theorem creditV_eq_zero_of_noCredit (h : ℕ) (a : AgentState L K) (ha : NoCredit a) :
    creditV h a = 0 := by
  rcases ha with ha | ha
  · exact creditV_eq_zero_of_inactive h a ha
  · exact creditV_eq_zero_of_entry h a ha

theorem highHourInd_eq_zero_of_noCredit (h : ℕ) (a : AgentState L K) (ha : NoCredit a) :
    highHourInd h a = 0 := by
  rcases ha with ha | ha
  · exact highHourInd_eq_zero_of_inactive h a ha
  · exact highHourInd_eq_zero_of_entry h a ha

theorem pairLedger_of_noCredit {h : ℕ} {s t s' t' : AgentState L K}
    (hs : NoCredit s') (ht : NoCredit t') : PairLedger h s t s' t' := by
  have e1 := creditV_eq_zero_of_noCredit h s' hs
  have e2 := creditV_eq_zero_of_noCredit h t' ht
  have e3 := highHourInd_eq_zero_of_noCredit h s' hs
  have e4 := highHourInd_eq_zero_of_noCredit h t' ht
  exact ⟨by omega, by omega⟩

/-- The counter subroutine raises the phase by at most one unless it enters the backup
track. -/
theorem stdCounterSubroutine_phase_le_succ (a : AgentState L K) :
    (stdCounterSubroutine L K a).phase.val ≤ a.phase.val + 1 ∨
      (stdCounterSubroutine L K a).phase.val = 10 := by
  unfold stdCounterSubroutine
  split_ifs with h0
  · unfold advancePhaseWithInit advancePhase
    split_ifs with h10
    · rcases phaseInit_phase_eq_or_ten' (L := L) (K := K)
        ⟨a.phase.val.succ, by have := a.phase.2; omega⟩
        { a with phase := ⟨a.phase.val.succ, by have := a.phase.2; omega⟩ } with h | h
      · left
        rw [h]
      · right
        exact h
    · rcases phaseInit_phase_eq_or_ten' (L := L) (K := K) a.phase a with h | h
      · left
        rw [h]
        omega
      · right
        exact h
  · left
    show a.phase.val ≤ a.phase.val + 1
    omega

theorem clockCounterStep_phase_le_succ (a : AgentState L K) :
    (clockCounterStep L K a).phase.val ≤ a.phase.val + 1 ∨
      (clockCounterStep L K a).phase.val = 10 := by
  unfold clockCounterStep
  split_ifs
  · exact stdCounterSubroutine_phase_le_succ a
  · left
    omega

/-- The Phase-1 rule on two Phase-1 agents keeps both below Phase 3 unless it enters
the backup track. -/
theorem phase1Transition_noCredit (s t : AgentState L K) (hs : s.phase.val = 1)
    (ht : t.phase.val = 1)
    (h1 : (Phase1Transition L K s t).1.phase.val ≠ 10)
    (h2 : (Phase1Transition L K s t).2.phase.val ≠ 10) :
    NoCredit (Phase1Transition L K s t).1 ∧ NoCredit (Phase1Transition L K s t).2 := by
  have key : ∀ u : AgentState L K, u.phase.val = 1 →
      (clockCounterStep L K u).phase.val ≠ 10 → NoCredit (clockCounterStep L K u) := by
    intro u hu hne
    left
    rcases clockCounterStep_phase_le_succ u with h | h
    · omega
    · exact absurd h hne
  unfold Phase1Transition at h1 h2 ⊢
  split_ifs at h1 h2 ⊢ with hmm
  · rcases hav : avgFin7 s.smallBias t.smallBias with ⟨b1, b2⟩
    simp only [hav] at h1 h2 ⊢
    exact ⟨key _ hs h1, key _ ht h2⟩
  · simp only at h1 h2 ⊢
    exact ⟨key s hs h1, key t ht h2⟩

/-- The Phase-2 rule on two Phase-2 agents: the outputs are inactive or fresh. -/
theorem phase2Transition_noCredit (s t : AgentState L K) (hs : s.phase.val = 2)
    (ht : t.phase.val = 2) :
    NoCredit (Phase2Transition L K s t).1 ∧ NoCredit (Phase2Transition L K s t).2 := by
  unfold Phase2Transition
  dsimp only
  split_ifs with hboth
  · constructor
    · right
      exact Phase2AdvanceEpidemic.Phase3EntryAgent_advancePhaseWithInit_of_phase2 _ hs
    · right
      exact Phase2AdvanceEpidemic.Phase3EntryAgent_advancePhaseWithInit_of_phase2 _ ht
  all_goals exact ⟨Or.inl (by change s.phase.val < 3; omega),
    Or.inl (by change t.phase.val < 3; omega)⟩

/-- The virtual rule on two inactive agents produces no credit (no backup). -/
theorem virtualRule_noCredit_of_inactive (s t : AgentState L K)
    (hs1 : 1 ≤ s.phase.val) (hs2 : s.phase.val ≤ 2) (ht1 : 1 ≤ t.phase.val) (ht2 : t.phase.val ≤ 2)
    (hsout : (virtualRule s t).1.phase.val ≤ 3) (htout : (virtualRule s t).2.phase.val ≤ 3) :
    NoCredit (virtualRule s t).1 ∧ NoCredit (virtualRule s t).2 := by
  have hnb := virtualRule_no_backup_of_phase_le_three s t hsout htout
  have hepi := phaseEpidemicUpdate_eq_of_no_backup s t (by omega) (by omega) hnb
  -- the epidemic outputs have the phase `max s.phase t.phase ≤ 2`
  have hphase1 : (phaseEpidemicUpdate L K s t).1.phase.val = (max s.phase t.phase).val := by
    rw [hepi]
    rcases runInitsBetween_phase_eq_or_ten (L := L) (K := K) s.phase.val (max s.phase t.phase).val
      { s with phase := max s.phase t.phase } with h | h
    · exact h
    · exfalso
      apply hnb.1
      rw [hepi]
      exact h
  have hphase2 : (phaseEpidemicUpdate L K s t).2.phase.val = (max s.phase t.phase).val := by
    rw [hepi]
    rcases runInitsBetween_phase_eq_or_ten (L := L) (K := K) t.phase.val (max s.phase t.phase).val
      { t with phase := max s.phase t.phase } with h | h
    · exact h
    · exfalso
      apply hnb.2
      rw [hepi]
      exact h
  have hmaxval : (max s.phase t.phase).val = max s.phase.val t.phase.val := fin_val_max _ _
  have hnc : ¬ CapCounterPair s t := by
    intro hc
    have := hc.1
    omega
  rw [virtualRule_eq_transition_of_not_cap s t hnc] at hsout htout ⊢
  rcases Nat.lt_or_ge (max s.phase.val t.phase.val) 2 with hlt | hge
  · -- both in Phase 1
    have h1 : (phaseEpidemicUpdate L K s t).1.phase.val = 1 := by omega
    have h2 : (phaseEpidemicUpdate L K s t).2.phase.val = 1 := by omega
    rw [transition_eq_phase1_of_dispatch s t h1] at hsout htout ⊢
    simp only [finishPhase10Entry_phase_val] at hsout htout
    have hne1 : (Phase1Transition L K (phaseEpidemicUpdate L K s t).1
        (phaseEpidemicUpdate L K s t).2).1.phase.val ≠ 10 := by omega
    have hne2 : (Phase1Transition L K (phaseEpidemicUpdate L K s t).1
        (phaseEpidemicUpdate L K s t).2).2.phase.val ≠ 10 := by omega
    rw [finishPhase10Entry_eq_self_of_after_ne_10 L K _ _ hne1,
      finishPhase10Entry_eq_self_of_after_ne_10 L K _ _ hne2]
    exact phase1Transition_noCredit _ _ h1 h2 hne1 hne2
  · -- the maximum is Phase 2
    have h1 : (phaseEpidemicUpdate L K s t).1.phase.val = 2 := by omega
    have h2 : (phaseEpidemicUpdate L K s t).2.phase.val = 2 := by omega
    rw [transition_eq_phase2_of_dispatch s t h1] at hsout htout ⊢
    simp only [finishPhase10Entry_phase_val] at hsout htout
    have hne1 : (Phase2Transition L K (phaseEpidemicUpdate L K s t).1
        (phaseEpidemicUpdate L K s t).2).1.phase.val ≠ 10 := by omega
    have hne2 : (Phase2Transition L K (phaseEpidemicUpdate L K s t).1
        (phaseEpidemicUpdate L K s t).2).2.phase.val ≠ 10 := by omega
    rw [finishPhase10Entry_eq_self_of_after_ne_10 L K _ _ hne1,
      finishPhase10Entry_eq_self_of_after_ne_10 L K _ _ hne2]
    exact phase2Transition_noCredit _ _ h1 h2

/-! ## The ledger on every virtual step -/

/-- The P11 pair ledger on any virtual step of the clock analysis: phases in `1..3`
before, at most `3` after. -/
theorem virtualRule_step_ledger (hK : 0 < K) (h : ℕ) (s t : AgentState L K)
    (hs : 1 ≤ s.phase.val ∧ s.phase.val ≤ 3) (ht : 1 ≤ t.phase.val ∧ t.phase.val ≤ 3)
    (hsout : (virtualRule s t).1.phase.val ≤ 3) (htout : (virtualRule s t).2.phase.val ≤ 3) :
    PairLedger h s t (virtualRule s t).1 (virtualRule s t).2 := by
  by_cases hs3 : s.phase.val = 3
  · by_cases ht3 : t.phase.val = 3
    · exact virtualRule_ledger h s t hs3 ht3
    · exact virtualRule_ledger_activation hK h s t hs3 ht.1 (by omega) hsout htout
  · by_cases ht3 : t.phase.val = 3
    · exact virtualRule_ledger_activation_left hK h s t ht3 hs.1 (by omega) hsout htout
    · have hnc := virtualRule_noCredit_of_inactive s t hs.1 (by omega) ht.1 (by omega) hsout htout
      exact pairLedger_of_noCredit hnc.1 hnc.2

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockMainActivation

end
