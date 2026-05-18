/-
Per-step invariants of the Doty et al. exact-majority protocol.

Reference: Doty et al., §§5–7; §3.1 (bias-sum invariant `g`).
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Protocol.Transition
import Ripple.PopulationProtocol.Majority.ExactMajority.Analysis.MainTheorem
import Mathlib.Tactic

set_option maxHeartbeats 2000000

open Multiset

namespace ExactMajority

variable {L K : ℕ}

/-! ### Phase-monotonicity invariants -/

private lemma phaseInit_phase_nondec (p : Fin 11) (a : AgentState L K) :
    a.phase.val ≤ (phaseInit L K p a).phase.val := by
  have h_le_10 : a.phase.val ≤ 10 := by have := a.phase.2; omega
  rcases p with ⟨n, hn⟩
  match n, hn with
  | 0, _ => unfold phaseInit; simp
  | 1, _ =>
    unfold phaseInit; simp
    split_ifs <;> first | exact h_le_10 | exact le_refl _
  | 2, _ =>
    unfold phaseInit; simp
    split_ifs <;> first | exact h_le_10 | exact le_refl _
  | 3, _ =>
    unfold phaseInit; simp
    cases a.role <;> first | exact le_refl _ | exact h_le_10
  | 4, _ => unfold phaseInit; simp
  | 5, _ =>
    unfold phaseInit; simp
    split_ifs <;> first | exact le_refl _ | exact h_le_10
  | 6, _ =>
    unfold phaseInit; simp
    split_ifs <;> first | exact le_refl _ | exact h_le_10
  | 7, _ =>
    unfold phaseInit; simp
    split_ifs <;> first | exact le_refl _ | exact h_le_10
  | 8, _ => unfold phaseInit; simp
  | 9, _ =>
    unfold phaseInit; simp
    split_ifs <;> first | exact h_le_10 | exact le_refl _
  | 10, _ => unfold phaseInit; simp
  | n + 11, _ => omega

private lemma phaseInit_input_preserved (p : Fin 11) (a : AgentState L K) :
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

private lemma runInitsBetween_phase_nondec (oldP newP : ℕ) (a : AgentState L K) :
    a.phase.val ≤ (runInitsBetween L K oldP newP a).phase.val := by
  unfold runInitsBetween
  let lst := (List.range 11).filter (fun k => oldP < k ∧ k ≤ newP)
  have h_ind : ∀ (a' : AgentState L K), a'.phase.val ≤
      (lst.foldl (fun (acc : AgentState L K) (k : ℕ) =>
        if h : k < 11 then phaseInit L K ⟨k, h⟩ acc else acc) a').phase.val := by
    induction lst with
    | nil => exact fun a' => le_refl _
    | cons k l IH =>
      intro a'
      simp [List.foldl]
      by_cases hk : k < 11
      · simp [hk]
        have h1 : a'.phase.val ≤ (phaseInit L K ⟨k, hk⟩ a').phase.val :=
          phaseInit_phase_nondec _ a'
        have h2 : (phaseInit L K ⟨k, hk⟩ a').phase.val ≤
          (l.foldl (fun (acc : AgentState L K) (k : ℕ) =>
            if h : k < 11 then phaseInit L K ⟨k, h⟩ acc else acc)
            (phaseInit L K ⟨k, hk⟩ a')).phase.val :=
          IH (phaseInit L K ⟨k, hk⟩ a')
        exact le_trans h1 h2
      · simp [hk]; exact IH a'
  exact h_ind a

private lemma phaseEpidemicUpdate_phase_nondec (s t : AgentState L K) :
    s.phase.val ≤ (phaseEpidemicUpdate L K s t).1.phase.val ∧
    t.phase.val ≤ (phaseEpidemicUpdate L K s t).2.phase.val := by
  unfold phaseEpidemicUpdate
  set p := max s.phase t.phase with hp
  have hp_s : s.phase.val ≤ p.val := Nat.le_max_left _ _
  have hp_t : t.phase.val ≤ p.val := Nat.le_max_right _ _
  have h_s' : s.phase.val ≤ (runInitsBetween L K s.phase.val p.val ({ s with phase := p })).phase.val := by
    calc
      s.phase.val ≤ p.val := hp_s
      _ = ({ s with phase := p }).phase.val := by simp
      _ ≤ (runInitsBetween L K s.phase.val p.val ({ s with phase := p })).phase.val :=
        runInitsBetween_phase_nondec _ _ _
  have h_t' : t.phase.val ≤ (runInitsBetween L K t.phase.val p.val ({ t with phase := p })).phase.val := by
    calc
      t.phase.val ≤ p.val := hp_t
      _ = ({ t with phase := p }).phase.val := by simp
      _ ≤ (runInitsBetween L K t.phase.val p.val ({ t with phase := p })).phase.val :=
        runInitsBetween_phase_nondec _ _ _
  exact ⟨h_s', h_t'⟩

private lemma runInitsBetween_input_preserved (oldP newP : ℕ) (a : AgentState L K) :
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
        calc _ = (phaseInit L K ⟨k, hk⟩ a').input := IH _
          _ = a'.input := phaseInit_input_preserved _ _
      · simp [hk]; exact IH a'
  exact h_ind a

private lemma phaseEpidemicUpdate_input_preserved (s t : AgentState L K) :
    (phaseEpidemicUpdate L K s t).1.input = s.input ∧
    (phaseEpidemicUpdate L K s t).2.input = t.input := by
  unfold phaseEpidemicUpdate
  refine ⟨?_, ?_⟩
  · calc _ = ({ s with phase := max s.phase t.phase } : AgentState L K).input :=
            runInitsBetween_input_preserved _ _ _
      _ = s.input := by simp
  · calc _ = ({ t with phase := max s.phase t.phase } : AgentState L K).input :=
            runInitsBetween_input_preserved _ _ _
      _ = t.input := by simp

/-- Top-level phase monotonicity. Reduces to (a) the phase-epidemic update
non-decreasing each agent's phase, and (b) the dispatched `PhaseNTransition`
preserving phase. The dispatcher's case-analysis on `s'.phase.val` cites
the per-phase `Phase{N}Transition_phase_nondec` helpers; together with
`phaseEpidemicUpdate_phase_nondec` this closes the theorem.

The per-phase helpers Phase0/3-10 are cited after the dispatcher's
product-`let` is exposed by case analysis. -/
theorem Transition_phase_monotone (s t : AgentState L K) :
    let (s', t') := Transition L K s t
    s.phase.val ≤ s'.phase.val ∧ t.phase.val ≤ t'.phase.val := by
  simp only []
  rcases phaseEpidemicUpdate_phase_nondec (L := L) (K := K) s t with ⟨h_ep_s, h_ep_t⟩
  unfold Transition
  -- Dispatcher case-split on the post-epidemic phase.
  let s' := (phaseEpidemicUpdate L K s t).1
  let t' := (phaseEpidemicUpdate L K s t).2
  change s.phase.val ≤ (match s'.phase with
    | ⟨0, _⟩ => Phase0Transition L K s' t'
    | ⟨1, _⟩ => Phase1Transition L K s' t'
    | ⟨2, _⟩ => Phase2Transition L K s' t'
    | ⟨3, _⟩ => Phase3Transition L K s' t'
    | ⟨4, _⟩ => Phase4Transition L K s' t'
    | ⟨5, _⟩ => Phase5Transition L K s' t'
    | ⟨6, _⟩ => Phase6Transition L K s' t'
    | ⟨7, _⟩ => Phase7Transition L K s' t'
    | ⟨8, _⟩ => Phase8Transition L K s' t'
    | ⟨9, _⟩ => Phase9Transition L K s' t'
    | ⟨10, _⟩ => Phase10Transition L K s' t'
    | _ => (s', t')).1.phase.val ∧
    t.phase.val ≤ (match s'.phase with
    | ⟨0, _⟩ => Phase0Transition L K s' t'
    | ⟨1, _⟩ => Phase1Transition L K s' t'
    | ⟨2, _⟩ => Phase2Transition L K s' t'
    | ⟨3, _⟩ => Phase3Transition L K s' t'
    | ⟨4, _⟩ => Phase4Transition L K s' t'
    | ⟨5, _⟩ => Phase5Transition L K s' t'
    | ⟨6, _⟩ => Phase6Transition L K s' t'
    | ⟨7, _⟩ => Phase7Transition L K s' t'
    | ⟨8, _⟩ => Phase8Transition L K s' t'
    | ⟨9, _⟩ => Phase9Transition L K s' t'
    | ⟨10, _⟩ => Phase10Transition L K s' t'
    | _ => (s', t')).2.phase.val
  rcases h_phase : s'.phase with ⟨n, hn⟩
  match n, hn with
  | 0, _ =>
    rcases Phase0Transition_phase_nondec L K s' t' with ⟨h_s, h_t⟩
    refine ⟨le_trans h_ep_s ?_, le_trans h_ep_t ?_⟩ <;> exact_mod_cast (by assumption)
  | 1, _ =>
    rcases Phase1Transition_phase_nondec L K s' t' with ⟨h_s, h_t⟩
    refine ⟨le_trans h_ep_s ?_, le_trans h_ep_t ?_⟩ <;> exact_mod_cast (by assumption)
  | 2, _ =>
    rcases Phase2Transition_phase_nondec L K s' t' with ⟨h_s, h_t⟩
    refine ⟨le_trans h_ep_s ?_, le_trans h_ep_t ?_⟩ <;> exact_mod_cast (by assumption)
  | 3, _ =>
    rcases Phase3Transition_phase_nondec L K s' t' with ⟨h_s, h_t⟩
    refine ⟨le_trans h_ep_s ?_, le_trans h_ep_t ?_⟩ <;> exact_mod_cast (by assumption)
  | 4, _ =>
    rcases Phase4Transition_phase_nondec L K s' t' with ⟨h_s, h_t⟩
    refine ⟨le_trans h_ep_s ?_, le_trans h_ep_t ?_⟩ <;> exact_mod_cast (by assumption)
  | 5, _ =>
    rcases Phase5Transition_phase_nondec L K s' t' with ⟨h_s, h_t⟩
    refine ⟨le_trans h_ep_s ?_, le_trans h_ep_t ?_⟩ <;> exact_mod_cast (by assumption)
  | 6, _ =>
    rcases Phase6Transition_phase_nondec L K s' t' with ⟨h_s, h_t⟩
    refine ⟨le_trans h_ep_s ?_, le_trans h_ep_t ?_⟩ <;> exact_mod_cast (by assumption)
  | 7, _ =>
    rcases Phase7Transition_phase_nondec L K s' t' with ⟨h_s, h_t⟩
    refine ⟨le_trans h_ep_s ?_, le_trans h_ep_t ?_⟩ <;> exact_mod_cast (by assumption)
  | 8, _ =>
    rcases Phase8Transition_phase_nondec L K s' t' with ⟨h_s, h_t⟩
    refine ⟨le_trans h_ep_s ?_, le_trans h_ep_t ?_⟩ <;> exact_mod_cast (by assumption)
  | 9, _ =>
    rcases Phase9Transition_phase_nondec L K s' t' with ⟨h_s, h_t⟩
    refine ⟨le_trans h_ep_s ?_, le_trans h_ep_t ?_⟩ <;> exact_mod_cast (by assumption)
  | 10, _ =>
    rcases Phase10Transition_phase_nondec L K s' t' with ⟨h_s, h_t⟩
    refine ⟨le_trans h_ep_s ?_, le_trans h_ep_t ?_⟩ <;> exact_mod_cast (by assumption)
  | n + 11, hn => omega

/-- If two interacting agents are in Phase 10 and already report the same
output, the full transition keeps both agents in Phase 10 with that output. -/
theorem Transition_preserves_phase10_same_output
    (s t : AgentState L K) (o : Output)
    (hs_phase : s.phase.val = 10) (ht_phase : t.phase.val = 10)
    (hs_out : s.output = o) (ht_out : t.output = o) :
    ((Transition L K s t).1.phase.val = 10 ∧
      (Transition L K s t).1.output = o) ∧
    ((Transition L K s t).2.phase.val = 10 ∧
      (Transition L K s t).2.output = o) := by
  have hmono :
      s.phase.val ≤ (Transition L K s t).1.phase.val ∧
        t.phase.val ≤ (Transition L K s t).2.phase.val := by
    simpa using Transition_phase_monotone (L := L) (K := K) s t
  rcases hmono with ⟨hs_mono, ht_mono⟩
  rcases Transition_preserves_same_output_of_phase10 (L := L) (K := K)
      s t o hs_phase ht_phase hs_out ht_out with ⟨hs_out', ht_out'⟩
  have hs_upper : (Transition L K s t).1.phase.val ≤ 10 := by
    have hlt := (Transition L K s t).1.phase.2
    omega
  have ht_upper : (Transition L K s t).2.phase.val ≤ 10 := by
    have hlt := (Transition L K s t).2.phase.2
    omega
  have hs_lower : 10 ≤ (Transition L K s t).1.phase.val := by
    simpa [hs_phase] using hs_mono
  have ht_lower : 10 ≤ (Transition L K s t).2.phase.val := by
    simpa [ht_phase] using ht_mono
  exact ⟨⟨le_antisymm hs_upper hs_lower, hs_out'⟩,
    ⟨le_antisymm ht_upper ht_lower, ht_out'⟩⟩

/-- A configuration whose agents are all in Phase 10 and unanimously report
the same output is closed under one protocol step. -/
theorem phase10_unanimous_output_preserved_by_step
    (c c' : Config (AgentState L K)) (o : Output)
    (h_c : ∀ a ∈ c, a.phase.val = 10 ∧ a.output = o)
    (h_step : (NonuniformMajority L K).StepRel c c') :
    ∀ a ∈ c', a.phase.val = 10 ∧ a.output = o := by
  rcases h_step with ⟨r₁, r₂, happ, hc'⟩
  dsimp [Protocol.Applicable, NonuniformMajority] at happ hc'
  have hr₁_mem : r₁ ∈ c := Multiset.mem_of_le happ (by simp)
  have hr₂_mem : r₂ ∈ c := Multiset.mem_of_le happ (by simp)
  rcases h_c r₁ hr₁_mem with ⟨hr₁_phase, hr₁_out⟩
  rcases h_c r₂ hr₂_mem with ⟨hr₂_phase, hr₂_out⟩
  have htrans := Transition_preserves_phase10_same_output (L := L) (K := K)
    r₁ r₂ o hr₁_phase hr₂_phase hr₁_out hr₂_out
  rw [hc']
  intro a ha
  simp only [Multiset.mem_add, Multiset.mem_cons, Multiset.mem_singleton] at ha
  rcases ha with h_old | h_new
  · exact h_c a (Multiset.mem_of_le (Multiset.sub_le_self c {r₁, r₂}) h_old)
  · rcases h_new with h_eq | h_eq
    · simpa [h_eq] using htrans.1
    · simpa [h_eq] using htrans.2

/-- A configuration whose agents are all in Phase 10 and unanimously report
the same output remains so after any reachable sequence of protocol steps. -/
theorem phase10_unanimous_output_preserved_by_reachable
    (c c' : Config (AgentState L K)) (o : Output)
    (h_c : ∀ a ∈ c, a.phase.val = 10 ∧ a.output = o)
    (h_reach : (NonuniformMajority L K).Reachable c c') :
    ∀ a ∈ c', a.phase.val = 10 ∧ a.output = o := by
  induction h_reach with
  | refl => exact h_c
  | tail _ hstep ih =>
      exact phase10_unanimous_output_preserved_by_step
        (L := L) (K := K) _ _ o ih hstep

/-- The output triple used by `doutPartition` for a concrete `Output`. -/
def outputTripleOfOutput : Output → Bool × Bool × Bool
  | .A => (true, false, false)
  | .B => (false, true, false)
  | .T => (false, false, true)

/-- If all agents in a configuration report the same concrete `Output`, then
the generic output partition has the corresponding output triple. -/
theorem doutPartition_output_of_unanimous_output
    (c : Config (AgentState L K)) (o : Output)
    (h_c : ∀ a ∈ c, a.output = o) :
    (doutPartition L K).output (outputTripleOfOutput o) c := by
  intro a ha
  have hout := h_c a ha
  cases o <;> simp [outputTripleOfOutput, doutPartition, hout]

/-- Conversely, if `doutPartition` reports the triple for a concrete output,
then every agent has that concrete output field. -/
theorem unanimous_output_of_doutPartition_output
    (c : Config (AgentState L K)) (o : Output)
    (h_c : (doutPartition L K).output (outputTripleOfOutput o) c) :
    ∀ a ∈ c, a.output = o := by
  intro a ha
  have h := h_c a ha
  cases o <;> cases hout : a.output <;>
    simp [outputTripleOfOutput, doutPartition, hout] at h ⊢

/-- The generic partition output triple for a concrete `Output` is equivalent
to unanimity of the concrete `output` field. -/
theorem doutPartition_output_iff_unanimous_output
    (c : Config (AgentState L K)) (o : Output) :
    (doutPartition L K).output (outputTripleOfOutput o) c ↔
      ∀ a ∈ c, a.output = o :=
  ⟨unanimous_output_of_doutPartition_output (L := L) (K := K) c o,
    doutPartition_output_of_unanimous_output (L := L) (K := K) c o⟩

/-- A Phase-10 unanimous-output configuration is stable in the generic
population-protocol sense. -/
theorem phase10_unanimous_output_isStable
    (c : Config (AgentState L K)) (o : Output)
    (h_c : ∀ a ∈ c, a.phase.val = 10 ∧ a.output = o) :
    (NonuniformMajority L K).IsStable (doutPartition L K) c := by
  refine ⟨outputTripleOfOutput o, ?_, ?_⟩
  · exact doutPartition_output_of_unanimous_output (L := L) (K := K) c o
      (fun a ha => (h_c a ha).2)
  · intro c' hreach
    have h_c' := phase10_unanimous_output_preserved_by_reachable
      (L := L) (K := K) c c' o h_c hreach
    exact doutPartition_output_of_unanimous_output (L := L) (K := K) c' o
      (fun a ha => (h_c' a ha).2)

/-- Top-level input-preservation. Same dispatcher case analysis as
`Transition_phase_monotone`, citing each `Phase{N}Transition_input_preserved`
in turn. -/
theorem Transition_input_preserved (s t : AgentState L K) :
    let (s', t') := Transition L K s t
    s'.input = s.input ∧ t'.input = t.input := by
  simp only []
  rcases phaseEpidemicUpdate_input_preserved (L := L) (K := K) s t with ⟨h_ep_s, h_ep_t⟩
  unfold Transition
  let s' := (phaseEpidemicUpdate L K s t).1
  let t' := (phaseEpidemicUpdate L K s t).2
  change (match s'.phase with
    | ⟨0, _⟩ => Phase0Transition L K s' t'
    | ⟨1, _⟩ => Phase1Transition L K s' t'
    | ⟨2, _⟩ => Phase2Transition L K s' t'
    | ⟨3, _⟩ => Phase3Transition L K s' t'
    | ⟨4, _⟩ => Phase4Transition L K s' t'
    | ⟨5, _⟩ => Phase5Transition L K s' t'
    | ⟨6, _⟩ => Phase6Transition L K s' t'
    | ⟨7, _⟩ => Phase7Transition L K s' t'
    | ⟨8, _⟩ => Phase8Transition L K s' t'
    | ⟨9, _⟩ => Phase9Transition L K s' t'
    | ⟨10, _⟩ => Phase10Transition L K s' t'
    | _ => (s', t')).1.input = s.input ∧
    (match s'.phase with
    | ⟨0, _⟩ => Phase0Transition L K s' t'
    | ⟨1, _⟩ => Phase1Transition L K s' t'
    | ⟨2, _⟩ => Phase2Transition L K s' t'
    | ⟨3, _⟩ => Phase3Transition L K s' t'
    | ⟨4, _⟩ => Phase4Transition L K s' t'
    | ⟨5, _⟩ => Phase5Transition L K s' t'
    | ⟨6, _⟩ => Phase6Transition L K s' t'
    | ⟨7, _⟩ => Phase7Transition L K s' t'
    | ⟨8, _⟩ => Phase8Transition L K s' t'
    | ⟨9, _⟩ => Phase9Transition L K s' t'
    | ⟨10, _⟩ => Phase10Transition L K s' t'
    | _ => (s', t')).2.input = t.input
  rcases h_phase : s'.phase with ⟨n, hn⟩
  match n, hn with
  | 0, _ =>
    rcases Phase0Transition_input_preserved L K s' t' with ⟨h_s, h_t⟩
    exact ⟨h_s.trans h_ep_s, h_t.trans h_ep_t⟩
  | 1, _ =>
    rcases Phase1Transition_input_preserved L K s' t' with ⟨h_s, h_t⟩
    exact ⟨h_s.trans h_ep_s, h_t.trans h_ep_t⟩
  | 2, _ =>
    rcases Phase2Transition_input_preserved L K s' t' with ⟨h_s, h_t⟩
    exact ⟨h_s.trans h_ep_s, h_t.trans h_ep_t⟩
  | 3, _ =>
    rcases Phase3Transition_input_preserved L K s' t' with ⟨h_s, h_t⟩
    exact ⟨h_s.trans h_ep_s, h_t.trans h_ep_t⟩
  | 4, _ =>
    rcases Phase4Transition_input_preserved L K s' t' with ⟨h_s, h_t⟩
    exact ⟨h_s.trans h_ep_s, h_t.trans h_ep_t⟩
  | 5, _ =>
    rcases Phase5Transition_input_preserved L K s' t' with ⟨h_s, h_t⟩
    exact ⟨h_s.trans h_ep_s, h_t.trans h_ep_t⟩
  | 6, _ =>
    rcases Phase6Transition_input_preserved L K s' t' with ⟨h_s, h_t⟩
    exact ⟨h_s.trans h_ep_s, h_t.trans h_ep_t⟩
  | 7, _ =>
    rcases Phase7Transition_input_preserved L K s' t' with ⟨h_s, h_t⟩
    exact ⟨h_s.trans h_ep_s, h_t.trans h_ep_t⟩
  | 8, _ =>
    rcases Phase8Transition_input_preserved L K s' t' with ⟨h_s, h_t⟩
    exact ⟨h_s.trans h_ep_s, h_t.trans h_ep_t⟩
  | 9, _ =>
    rcases Phase9Transition_input_preserved L K s' t' with ⟨h_s, h_t⟩
    exact ⟨h_s.trans h_ep_s, h_t.trans h_ep_t⟩
  | 10, _ =>
    rcases Phase10Transition_input_preserved L K s' t' with ⟨h_s, h_t⟩
    exact ⟨h_s.trans h_ep_s, h_t.trans h_ep_t⟩
  | n + 11, hn => omega

/-! ### Bias-sum (gap) invariant -/

def AgentState.smallBiasInt (a : AgentState L K) : ℤ := (a.smallBias.val : ℤ) - 3

/-- Phase-0 quota invariant for the small-bias accumulator.

The bounds are phase-specific: Phase 1 averaging can move an unassigned `main`
outside the `≤ 2` bound, but Phase 0 is the only phase where `addSmallBias`
uses this quota to avoid clamping. -/
def well_formed_agent_quota {L K : ℕ} (a : AgentState L K) : Prop :=
  a.phase.val = 0 →
    (a.role = .mcr → (AgentState.smallBiasInt a).natAbs ≤ 1) ∧
    (a.role = .main → a.assigned = false → (AgentState.smallBiasInt a).natAbs ≤ 2)

private def smallBiasQuotaFields {L K : ℕ} (a : AgentState L K) : Prop :=
  (a.role = .mcr → (AgentState.smallBiasInt a).natAbs ≤ 1) ∧
  (a.role = .main → a.assigned = false → (AgentState.smallBiasInt a).natAbs ≤ 2)

private lemma smallBiasQuotaFields_of_well_formed_agent_quota (a : AgentState L K)
    (hphase : a.phase.val = 0) :
    well_formed_agent_quota a → smallBiasQuotaFields a := by
  intro h
  exact h hphase

def initialGap (c : Config (AgentState L K)) : ℤ :=
  ((c.filter (fun a => a.input = .A)).card : ℤ) -
    ((c.filter (fun a => a.input = .B)).card : ℤ)

def AgentState.inputBiasInt (a : AgentState L K) : ℤ :=
  match a.input with
  | .A => 1
  | .B => -1

def inputBiasSum (c : Config (AgentState L K)) : ℤ :=
  (c.map AgentState.inputBiasInt).sum

theorem inputBiasSum_initialGap (c : Config (AgentState L K)) :
    inputBiasSum c = initialGap c := by
  induction c using Multiset.induction_on with
  | empty =>
      simp [inputBiasSum, initialGap]
  | cons a c IH =>
      simp only [inputBiasSum, initialGap, AgentState.inputBiasInt,
        Multiset.map_cons, Multiset.sum_cons, Multiset.filter_cons]
      cases hinput : a.input with
      | A =>
          simp [hinput, inputBiasSum, initialGap, AgentState.inputBiasInt] at IH ⊢
          omega
      | B =>
          simp [hinput, inputBiasSum, initialGap, AgentState.inputBiasInt] at IH ⊢
          omega

theorem inputBiasSum_stepRel_invariant (c c' : Config (AgentState L K))
    (h_step : (NonuniformMajority L K).StepRel c c') :
    inputBiasSum c' = inputBiasSum c := by
  rcases h_step with ⟨r₁, r₂, happ, hc'⟩
  dsimp [Protocol.Applicable, NonuniformMajority] at happ hc'
  have hinput := Transition_input_preserved (L := L) (K := K) r₁ r₂
  have hpair :
      AgentState.inputBiasInt r₁ + AgentState.inputBiasInt r₂ =
        AgentState.inputBiasInt (Transition L K r₁ r₂).1 +
          AgentState.inputBiasInt (Transition L K r₁ r₂).2 := by
    rcases htr : Transition L K r₁ r₂ with ⟨p₁, p₂⟩
    simp [htr] at hinput ⊢
    simp [AgentState.inputBiasInt, hinput.1, hinput.2]
  rw [hc']
  have hrestore : c - r₁ ::ₘ {r₂} + r₁ ::ₘ {r₂} = c :=
    Multiset.sub_add_cancel happ
  have hsum_c :
      inputBiasSum c =
        inputBiasSum (c - r₁ ::ₘ {r₂}) +
          (AgentState.inputBiasInt r₁ + AgentState.inputBiasInt r₂) := by
    rw [← hrestore]
    simp [inputBiasSum, add_assoc, add_comm, add_left_comm]
  have hsum_c' :
      inputBiasSum
          (c - r₁ ::ₘ {r₂} +
          (Transition L K r₁ r₂).1 ::ₘ {(Transition L K r₁ r₂).2}) =
      inputBiasSum (c - r₁ ::ₘ {r₂}) +
        (AgentState.inputBiasInt (Transition L K r₁ r₂).1 +
          AgentState.inputBiasInt (Transition L K r₁ r₂).2) := by
    simp [inputBiasSum, add_assoc, add_comm, add_left_comm]
  rw [hsum_c', hsum_c, ← hpair]

theorem initialGap_stepRel_invariant (c c' : Config (AgentState L K))
    (h_step : (NonuniformMajority L K).StepRel c c') :
    initialGap c' = initialGap c := by
  rw [← inputBiasSum_initialGap c', ← inputBiasSum_initialGap c]
  exact inputBiasSum_stepRel_invariant (L := L) (K := K) c c' h_step

theorem reachable_initialGap_invariant (c c' : Config (AgentState L K))
    (h_reach : (NonuniformMajority L K).Reachable c c') :
    initialGap c' = initialGap c := by
  induction h_reach with
  | refl =>
      rfl
  | tail _ hstep ih =>
      exact (initialGap_stepRel_invariant (L := L) (K := K) _ _ hstep).trans ih

theorem majorityVerdict_eq_A_of_initialGap_pos (c : Config (AgentState L K))
    (hgap : 0 < initialGap c) :
    majorityVerdict c = outputTripleOfOutput .A := by
  have hgt :
      (c.filter (fun a => a.input = .A)).card >
        (c.filter (fun a => a.input = .B)).card := by
    dsimp [initialGap] at hgap
    omega
  simp [majorityVerdict, outputTripleOfOutput, hgt]

theorem majorityVerdict_eq_B_of_initialGap_neg (c : Config (AgentState L K))
    (hgap : initialGap c < 0) :
    majorityVerdict c = outputTripleOfOutput .B := by
  have hlt :
      (c.filter (fun a => a.input = .A)).card <
        (c.filter (fun a => a.input = .B)).card := by
    dsimp [initialGap] at hgap
    omega
  have hnot_gt :
      ¬ (c.filter (fun a => a.input = .A)).card >
        (c.filter (fun a => a.input = .B)).card := by
    omega
  simp [majorityVerdict, outputTripleOfOutput, hlt, hnot_gt]

theorem majorityVerdict_eq_T_of_initialGap_zero (c : Config (AgentState L K))
    (hgap : initialGap c = 0) :
    majorityVerdict c = outputTripleOfOutput .T := by
  have heq :
      (c.filter (fun a => a.input = .A)).card =
        (c.filter (fun a => a.input = .B)).card := by
    dsimp [initialGap] at hgap
    omega
  simp [majorityVerdict, outputTripleOfOutput, heq]

theorem majorityVerdict_reachable_invariant (c c' : Config (AgentState L K))
    (h_reach : (NonuniformMajority L K).Reachable c c') :
    majorityVerdict c' = majorityVerdict c := by
  have hgap_eq := reachable_initialGap_invariant (L := L) (K := K) c c' h_reach
  by_cases hpos : 0 < initialGap c
  · have hpos' : 0 < initialGap c' := by
      rw [hgap_eq]
      exact hpos
    rw [majorityVerdict_eq_A_of_initialGap_pos (L := L) (K := K) c' hpos',
      majorityVerdict_eq_A_of_initialGap_pos (L := L) (K := K) c hpos]
  · by_cases hneg : initialGap c < 0
    · have hneg' : initialGap c' < 0 := by
        rw [hgap_eq]
        exact hneg
      rw [majorityVerdict_eq_B_of_initialGap_neg (L := L) (K := K) c' hneg',
        majorityVerdict_eq_B_of_initialGap_neg (L := L) (K := K) c hneg]
    · have hzero : initialGap c = 0 := by omega
      have hzero' : initialGap c' = 0 := by
        rw [hgap_eq]
        exact hzero
      rw [majorityVerdict_eq_T_of_initialGap_zero (L := L) (K := K) c' hzero',
        majorityVerdict_eq_T_of_initialGap_zero (L := L) (K := K) c hzero]

theorem phase10_unanimous_A_majority_witness_of_initialGap_pos
    (init c : Config (AgentState L K))
    (h_c : ∀ a ∈ c, a.phase.val = 10 ∧ a.output = .A)
    (hgap : 0 < initialGap init) :
    (doutPartition L K).output (majorityVerdict init) c ∧
      (NonuniformMajority L K).IsStable (doutPartition L K) c := by
  constructor
  · rw [majorityVerdict_eq_A_of_initialGap_pos (L := L) (K := K) init hgap]
    exact doutPartition_output_of_unanimous_output (L := L) (K := K) c .A
      (fun a ha => (h_c a ha).2)
  · exact phase10_unanimous_output_isStable (L := L) (K := K) c .A h_c

theorem phase10_unanimous_B_majority_witness_of_initialGap_neg
    (init c : Config (AgentState L K))
    (h_c : ∀ a ∈ c, a.phase.val = 10 ∧ a.output = .B)
    (hgap : initialGap init < 0) :
    (doutPartition L K).output (majorityVerdict init) c ∧
      (NonuniformMajority L K).IsStable (doutPartition L K) c := by
  constructor
  · rw [majorityVerdict_eq_B_of_initialGap_neg (L := L) (K := K) init hgap]
    exact doutPartition_output_of_unanimous_output (L := L) (K := K) c .B
      (fun a ha => (h_c a ha).2)
  · exact phase10_unanimous_output_isStable (L := L) (K := K) c .B h_c

theorem phase10_unanimous_T_majority_witness_of_initialGap_zero
    (init c : Config (AgentState L K))
    (h_c : ∀ a ∈ c, a.phase.val = 10 ∧ a.output = .T)
    (hgap : initialGap init = 0) :
    (doutPartition L K).output (majorityVerdict init) c ∧
      (NonuniformMajority L K).IsStable (doutPartition L K) c := by
  constructor
  · rw [majorityVerdict_eq_T_of_initialGap_zero (L := L) (K := K) init hgap]
    exact doutPartition_output_of_unanimous_output (L := L) (K := K) c .T
      (fun a ha => (h_c a ha).2)
  · exact phase10_unanimous_output_isStable (L := L) (K := K) c .T h_c

/-- A Phase-10 configuration whose unanimous output agrees with the sign of
the initial input gap.  This is the deterministic endpoint needed by the
generic stable-computation definition; the probabilistic phase analysis must
still prove reachability of such endpoints. -/
def phase10MajorityWitness
    (init final : Config (AgentState L K)) : Prop :=
  (0 < initialGap init ∧ ∀ a ∈ final, a.phase.val = 10 ∧ a.output = .A) ∨
  (initialGap init < 0 ∧ ∀ a ∈ final, a.phase.val = 10 ∧ a.output = .B) ∨
  (initialGap init = 0 ∧ ∀ a ∈ final, a.phase.val = 10 ∧ a.output = .T)

theorem stable_witness_of_phase10MajorityWitness
    (init c final : Config (AgentState L K))
    (hreach : (NonuniformMajority L K).Reachable c final)
    (hwitness : phase10MajorityWitness (L := L) (K := K) init final) :
    ∃ o, (NonuniformMajority L K).Reachable c o ∧
      (doutPartition L K).output (majorityVerdict init) o ∧
      (NonuniformMajority L K).IsStable (doutPartition L K) o := by
  rcases hwitness with ⟨hgap, hfinal⟩ | ⟨hgap, hfinal⟩ | ⟨hgap, hfinal⟩
  · refine ⟨final, hreach, ?_, ?_⟩
    · exact (phase10_unanimous_A_majority_witness_of_initialGap_pos
        (L := L) (K := K) init final hfinal hgap).1
    · exact (phase10_unanimous_A_majority_witness_of_initialGap_pos
        (L := L) (K := K) init final hfinal hgap).2
  · refine ⟨final, hreach, ?_, ?_⟩
    · exact (phase10_unanimous_B_majority_witness_of_initialGap_neg
        (L := L) (K := K) init final hfinal hgap).1
    · exact (phase10_unanimous_B_majority_witness_of_initialGap_neg
        (L := L) (K := K) init final hfinal hgap).2
  · refine ⟨final, hreach, ?_, ?_⟩
    · exact (phase10_unanimous_T_majority_witness_of_initialGap_zero
        (L := L) (K := K) init final hfinal hgap).1
    · exact (phase10_unanimous_T_majority_witness_of_initialGap_zero
        (L := L) (K := K) init final hfinal hgap).2

/-- Reduction from the remaining phase-reachability obligation to the generic
stable-computation statement.

This is not the Doty theorem itself: the hypothesis is exactly the missing
phase analysis, namely that every configuration reachable from a valid initial
configuration can itself reach a Phase-10 unanimous endpoint matching the
initial majority sign.  Once that reachability fact is supplied, the already
proved deterministic Phase-10 stability lemmas close the `StablyComputes`
wrapper. -/
theorem stable_majority_correct_of_phase10MajorityWitness_reachability
    (hphase :
      ∀ init : Config (AgentState L K), validInitial init →
        ∀ c : Config (AgentState L K),
          (NonuniformMajority L K).Reachable init c →
            ∃ final : Config (AgentState L K),
              (NonuniformMajority L K).Reachable c final ∧
                phase10MajorityWitness (L := L) (K := K) init final) :
    stable_majority_correct_target L K := by
  intro init hinit c hreach
  rcases hphase init hinit c hreach with ⟨final, hfinal_reach, hfinal⟩
  exact stable_witness_of_phase10MajorityWitness
    (L := L) (K := K) init c final hfinal_reach hfinal

theorem nonuniform_majority_correctness_of_phase10MajorityWitness_reachability
    (hphase :
      ∀ init : Config (AgentState L K), validInitial init →
        ∀ c : Config (AgentState L K),
          (NonuniformMajority L K).Reachable init c →
            ∃ final : Config (AgentState L K),
              (NonuniformMajority L K).Reachable c final ∧
                phase10MajorityWitness (L := L) (K := K) init final) :
    nonuniform_majority_correctness_target L K := by
  exact stable_majority_correct_of_phase10MajorityWitness_reachability
    (L := L) (K := K) hphase

def smallBiasSum (c : Config (AgentState L K)) : ℤ :=
  (c.map AgentState.smallBiasInt).sum

theorem smallBiasSum_initialGap (c : Config (AgentState L K))
    (h : ∀ a ∈ c, a.phase = ⟨0, by decide⟩ ∧
                  ((a.input = .A → a.smallBias = ⟨4, by decide⟩) ∧
                   (a.input = .B → a.smallBias = ⟨2, by decide⟩))) :
    smallBiasSum c = initialGap c := by
  induction c using Multiset.induction_on with
  | empty =>
      simp [smallBiasSum, initialGap]
  | cons a c IH =>
      have ha := h a (Multiset.mem_cons_self a c)
      obtain ⟨_, hA, hB⟩ := ha
      have h_IH : smallBiasSum c = initialGap c :=
        IH (fun b hb => h b (Multiset.mem_cons_of_mem hb))
      simp only [smallBiasSum, initialGap, AgentState.smallBiasInt,
        Multiset.map_cons, Multiset.sum_cons, Multiset.filter_cons, Multiset.card_cons]
      cases h_in : a.input with
      | A =>
          have hsmall : a.smallBias = ⟨4, by decide⟩ := hA h_in
          simp [h_in, hsmall, smallBiasSum, initialGap, AgentState.smallBiasInt] at h_IH ⊢
          omega
      | B =>
          have hsmall : a.smallBias = ⟨2, by decide⟩ := hB h_in
          simp [h_in, hsmall, smallBiasSum, initialGap, AgentState.smallBiasInt] at h_IH ⊢
          omega

lemma avgFin7_preserves_sum (x y : Fin 7) :
    ((avgFin7 x y).1.val : ℤ) + ((avgFin7 x y).2.val : ℤ) = (x.val : ℤ) + (y.val : ℤ) := by
  unfold avgFin7
  have h : (x.val + y.val) / 2 + (x.val + y.val + 1) / 2 = x.val + y.val := by omega
  push_cast
  omega

private lemma phaseEpidemicUpdate_smallBiasInt_eq (s t : AgentState L K) :
    AgentState.smallBiasInt s + AgentState.smallBiasInt t =
    AgentState.smallBiasInt (phaseEpidemicUpdate L K s t).1 + AgentState.smallBiasInt (phaseEpidemicUpdate L K s t).2 := by
  have h := phaseEpidemicUpdate_preserves_smallBias L K s t
  rcases h with ⟨h1, h2⟩
  simp [AgentState.smallBiasInt, h1, h2]

private lemma runInitsBetween_self_eq (n : ℕ) (a : AgentState L K) :
    runInitsBetween L K n n a = a := by
  unfold runInitsBetween
  have hfilter : (List.range 11).filter (fun k => n < k ∧ k ≤ n) = [] := by
    induction List.range 11 with
    | nil => simp
    | cons k ks ih =>
      have hk : ¬ (n < k ∧ k ≤ n) := by omega
      simp [hk, ih]
  rw [hfilter]
  simp

private lemma phaseEpidemicUpdate_left_phase_ge_max (s t : AgentState L K) :
    max s.phase.val t.phase.val ≤ (phaseEpidemicUpdate L K s t).1.phase.val := by
  unfold phaseEpidemicUpdate
  set p := max s.phase t.phase with hp
  calc
    max s.phase.val t.phase.val = p.val := by rw [hp]; rfl
    _ = ({ s with phase := p }).phase.val := by simp
    _ ≤ (runInitsBetween L K s.phase.val p.val ({ s with phase := p })).phase.val :=
      runInitsBetween_phase_nondec (L := L) (K := K) s.phase.val p.val
        ({ s with phase := p })

private lemma phaseEpidemicUpdate_eq_of_left_phase_zero (s t : AgentState L K)
    (hzero : (phaseEpidemicUpdate L K s t).1.phase.val = 0) :
    phaseEpidemicUpdate L K s t = (s, t) := by
  have hmax0 : max s.phase.val t.phase.val = 0 := by
    have hle := phaseEpidemicUpdate_left_phase_ge_max (L := L) (K := K) s t
    omega
  have hs0 : s.phase.val = 0 := by
    have hle : s.phase.val ≤ max s.phase.val t.phase.val := Nat.le_max_left _ _
    omega
  have ht0 : t.phase.val = 0 := by
    have hle : t.phase.val ≤ max s.phase.val t.phase.val := Nat.le_max_right _ _
    omega
  have hp_s : max s.phase t.phase = s.phase := by
    ext
    simp [hs0, ht0]
  have hp_t : max s.phase t.phase = t.phase := by
    ext
    simp [hs0, ht0]
  unfold phaseEpidemicUpdate
  apply Prod.ext
  · rw [hp_s]
    simp [runInitsBetween_self_eq]
  · rw [hp_t]
    simp [runInitsBetween_self_eq]

private theorem phaseEpidemicUpdate_right_phase_pos_of_left_phase_pos_quota
    (s t : AgentState L K)
    (hleft : 1 ≤ (phaseEpidemicUpdate L K s t).1.phase.val) :
    1 ≤ (phaseEpidemicUpdate L K s t).2.phase.val := by
  unfold phaseEpidemicUpdate at hleft ⊢
  set p := max s.phase t.phase with hp
  by_cases hpzero : p.val = 0
  · have hs0 : s.phase.val = 0 := by
      have hle : s.phase.val ≤ p.val := by
        rw [hp]
        exact Nat.le_max_left _ _
      omega
    have hfirst : (runInitsBetween L K s.phase.val p.val ({ s with phase := p })).phase.val = 0 := by
      unfold runInitsBetween
      have hfilter :
          (List.range 11).filter (fun k => s.phase.val < k ∧ k ≤ p.val) = [] := by
        rw [hs0, hpzero]
        induction List.range 11 with
        | nil => simp
        | cons k ks ih =>
            simp [ih]
            constructor
            · intro hpos hzero
              omega
            · intro a _ha hpos hzero
              omega
      rw [hfilter]
      simp [hpzero]
    have hbad : 1 ≤ 0 := by
      simpa [hfirst] using hleft
    omega
  · have hp_pos : 1 ≤ p.val := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hpzero)
    have hp_le_right :
        p.val ≤ (runInitsBetween L K t.phase.val p.val ({ t with phase := p })).phase.val := by
      calc
        p.val = ({ t with phase := p } : AgentState L K).phase.val := by simp
        _ ≤ (runInitsBetween L K t.phase.val p.val ({ t with phase := p })).phase.val :=
          runInitsBetween_phase_nondec (L := L) (K := K) t.phase.val p.val
            ({ t with phase := p })
    exact le_trans hp_pos hp_le_right

lemma addSmallBias_smallBiasInt (x y : Fin 7) : (addSmallBias x y).val - 3 = max (-3 : ℤ) (min (3 : ℤ) ((x.val : ℤ) - 3 + ((y.val : ℤ) - 3))) := by
  fin_cases x <;> fin_cases y <;> decide

lemma addSmallBias_no_clamp (x y : Fin 7) (h : (((x.val : ℤ) - 3) + ((y.val : ℤ) - 3)).natAbs ≤ 3) :
    (addSmallBias x y).val - 3 = (x.val : ℤ) - 3 + ((y.val : ℤ) - 3) := by
  rw [addSmallBias_smallBiasInt]
  have h_range : -3 ≤ (x.val : ℤ) - 3 + ((y.val : ℤ) - 3) ∧ (x.val : ℤ) - 3 + ((y.val : ℤ) - 3) ≤ 3 := by
    omega
  rcases h_range with ⟨hneg, hpos⟩
  omega

private lemma smallBias_pair_bound_of_mcr_mcr (s t : AgentState L K)
    (hs_phase : s.phase.val = 0) (ht_phase : t.phase.val = 0)
    (hsq : well_formed_agent_quota s) (htq : well_formed_agent_quota t)
    (hs_role : s.role = .mcr) (ht_role : t.role = .mcr) :
    (AgentState.smallBiasInt s + AgentState.smallBiasInt t).natAbs ≤ 3 := by
  have hs_abs : (AgentState.smallBiasInt s).natAbs ≤ 1 := (hsq hs_phase).1 hs_role
  have ht_abs : (AgentState.smallBiasInt t).natAbs ≤ 1 := (htq ht_phase).1 ht_role
  omega

private lemma smallBias_pair_bound_of_mcr_main (s t : AgentState L K)
    (hs_phase : s.phase.val = 0) (ht_phase : t.phase.val = 0)
    (hsq : well_formed_agent_quota s) (htq : well_formed_agent_quota t)
    (hs_role : s.role = .mcr) (ht_role : t.role = .main)
    (ht_unassigned : t.assigned = false) :
    (AgentState.smallBiasInt s + AgentState.smallBiasInt t).natAbs ≤ 3 := by
  have hs_abs : (AgentState.smallBiasInt s).natAbs ≤ 1 := (hsq hs_phase).1 hs_role
  have ht_abs : (AgentState.smallBiasInt t).natAbs ≤ 2 :=
    (htq ht_phase).2 ht_role ht_unassigned
  omega

private lemma smallBias_pair_bound_of_main_mcr (s t : AgentState L K)
    (hs_phase : s.phase.val = 0) (ht_phase : t.phase.val = 0)
    (hsq : well_formed_agent_quota s) (htq : well_formed_agent_quota t)
    (hs_role : s.role = .main) (ht_role : t.role = .mcr)
    (hs_unassigned : s.assigned = false) :
    (AgentState.smallBiasInt s + AgentState.smallBiasInt t).natAbs ≤ 3 := by
  have hs_abs : (AgentState.smallBiasInt s).natAbs ≤ 2 :=
    (hsq hs_phase).2 hs_role hs_unassigned
  have ht_abs : (AgentState.smallBiasInt t).natAbs ≤ 1 := (htq ht_phase).1 ht_role
  omega

private lemma Phase0Transition_preserves_sum (s t : AgentState L K)
    (hsum : (AgentState.smallBiasInt s + AgentState.smallBiasInt t).natAbs ≤ 3) :
    AgentState.smallBiasInt s + AgentState.smallBiasInt t =
    AgentState.smallBiasInt (Phase0Transition L K s t).1 + AgentState.smallBiasInt (Phase0Transition L K s t).2 := by
  let s1 := if s.role = .mcr ∧ t.role = .mcr then
    { s with role := .main, smallBias := addSmallBias s.smallBias t.smallBias } else s
  let t1 := if s.role = .mcr ∧ t.role = .mcr then
    { t with role := .cr, smallBias := ⟨3, by decide⟩ } else t
  have hsum_conv : (((s.smallBias.val : ℤ) - 3) + ((t.smallBias.val : ℤ) - 3)).natAbs ≤ 3 := by
    simpa [AgentState.smallBiasInt] using hsum
  have h1 : AgentState.smallBiasInt s + AgentState.smallBiasInt t = AgentState.smallBiasInt s1 + AgentState.smallBiasInt t1 := by
    simp [s1, t1, AgentState.smallBiasInt]
    split_ifs <;> simp [addSmallBias_no_clamp s.smallBias t.smallBias hsum_conv]
  have hsum1 : (AgentState.smallBiasInt s1 + AgentState.smallBiasInt t1).natAbs ≤ 3 := by
    rw [← h1]; exact hsum
  have hsum1_conv : (((s1.smallBias.val : ℤ) - 3) + ((t1.smallBias.val : ℤ) - 3)).natAbs ≤ 3 := by
    simpa [AgentState.smallBiasInt] using hsum1
  have hsum1_conv' : (((t1.smallBias.val : ℤ) - 3) + ((s1.smallBias.val : ℤ) - 3)).natAbs ≤ 3 := by
    simpa [add_comm] using hsum1_conv
  let s2 := if s1.role = .mcr ∧ t1.role = .main ∧ ¬ t1.assigned then
              { s1 with role := .cr, smallBias := ⟨3, by decide⟩ }
            else if t1.role = .mcr ∧ s1.role = .main ∧ ¬ s1.assigned then
              { s1 with assigned := true, smallBias := addSmallBias t1.smallBias s1.smallBias }
            else s1
  let t2 := if s1.role = .mcr ∧ t1.role = .main ∧ ¬ t1.assigned then
              { t1 with assigned := true, smallBias := addSmallBias s1.smallBias t1.smallBias }
            else if t1.role = .mcr ∧ s1.role = .main ∧ ¬ s1.assigned then
              { t1 with role := .cr, smallBias := ⟨3, by decide⟩ }
            else t1
  have h2 : AgentState.smallBiasInt s1 + AgentState.smallBiasInt t1 = AgentState.smallBiasInt s2 + AgentState.smallBiasInt t2 := by
    by_cases h : s1.role = .mcr ∧ t1.role = .main ∧ ¬ t1.assigned
    · rcases h with ⟨hs_role, ht_role, ht_not⟩
      simp [hs_role, ht_role, ht_not, AgentState.smallBiasInt, s2, t2,
        addSmallBias_no_clamp s1.smallBias t1.smallBias hsum1_conv]
    · by_cases h' : t1.role = .mcr ∧ s1.role = .main ∧ ¬ s1.assigned
      · rcases h' with ⟨ht_role, hs_role, hs_not⟩
        simp [ht_role, hs_role, hs_not, AgentState.smallBiasInt, s2, t2,
          addSmallBias_no_clamp t1.smallBias s1.smallBias hsum1_conv', add_comm, add_left_comm, add_assoc]
      · have hs2 : s2 = s1 := by
          dsimp [s2]; rw [if_neg h, if_neg h']
        have ht2 : t2 = t1 := by
          dsimp [t2]; rw [if_neg h, if_neg h']
        simp [hs2, ht2, AgentState.smallBiasInt]
  let s3 := if s2.role = .mcr ∧ t2.role ≠ .main ∧ t2.role ≠ .mcr ∧ ¬ t2.assigned then s2
            else if t2.role = .mcr ∧ s2.role ≠ .main ∧ s2.role ≠ .mcr ∧ ¬ s2.assigned then
              { s2 with assigned := true }
            else s2
  let t3 := if s2.role = .mcr ∧ t2.role ≠ .main ∧ t2.role ≠ .mcr ∧ ¬ t2.assigned then
              { t2 with assigned := true }
            else if t2.role = .mcr ∧ s2.role ≠ .main ∧ s2.role ≠ .mcr ∧ ¬ s2.assigned then t2
            else t2
  have h3 : AgentState.smallBiasInt s2 + AgentState.smallBiasInt t2 = AgentState.smallBiasInt s3 + AgentState.smallBiasInt t3 := by
    by_cases h : s2.role = .mcr ∧ t2.role ≠ .main ∧ t2.role ≠ .mcr ∧ ¬ t2.assigned
    · rcases h with ⟨hs_role, ht_not_main, ht_not_mcr, ht_not⟩
      simp [hs_role, ht_not_main, ht_not_mcr, ht_not, AgentState.smallBiasInt, s3, t3]
    · by_cases h' : t2.role = .mcr ∧ s2.role ≠ .main ∧ s2.role ≠ .mcr ∧ ¬ s2.assigned
      · rcases h' with ⟨ht_role, hs_not_main, hs_not_mcr, hs_not⟩
        simp [ht_role, hs_not_main, hs_not_mcr, hs_not, AgentState.smallBiasInt, s3, t3]
      · have hs3 : s3 = s2 := by
          dsimp [s3]; rw [if_neg h, if_neg h']
        have ht3 : t3 = t2 := by
          dsimp [t3]; rw [if_neg h, if_neg h']
        simp [hs3, ht3, AgentState.smallBiasInt]
  let s3' := if s3.role = .mcr ∧ t3.role = .cr then { s3 with role := .main, assigned := true }
             else if t3.role = .mcr ∧ s3.role = .cr then s3
             else s3
  let t3' := if s3.role = .mcr ∧ t3.role = .cr then t3
             else if t3.role = .mcr ∧ s3.role = .cr then { t3 with role := .main, assigned := true }
             else t3
  have h3' : AgentState.smallBiasInt s3 + AgentState.smallBiasInt t3 = AgentState.smallBiasInt s3' + AgentState.smallBiasInt t3' := by
    by_cases h : s3.role = .mcr ∧ t3.role = .cr
    · rcases h with ⟨hs_role, ht_role⟩
      simp [hs_role, ht_role, AgentState.smallBiasInt, s3', t3']
    · by_cases h' : t3.role = .mcr ∧ s3.role = .cr
      · rcases h' with ⟨ht_role, hs_role⟩
        simp [ht_role, hs_role, AgentState.smallBiasInt, s3', t3']
      · have hs3' : s3' = s3 := by
          dsimp [s3']; rw [if_neg h, if_neg h']
        have ht3' : t3' = t3 := by
          dsimp [t3']; rw [if_neg h, if_neg h']
        simp [hs3', ht3', AgentState.smallBiasInt]
  let s4 := if s3'.role = .cr ∧ t3'.role = .cr then
              { s3' with role := .clock, counter := ⟨50 * (L + 1), by omega⟩ } else s3'
  let t4 := if s3'.role = .cr ∧ t3'.role = .cr then
              { t3' with role := .reserve } else t3'
  have h4 : AgentState.smallBiasInt s3' + AgentState.smallBiasInt t3' = AgentState.smallBiasInt s4 + AgentState.smallBiasInt t4 := by
    by_cases h : s3'.role = .cr ∧ t3'.role = .cr
    · rcases h with ⟨hs_role, ht_role⟩
      simp [hs_role, ht_role, AgentState.smallBiasInt, s4, t4]
    · have hs4 : s4 = s3' := by
        dsimp [s4]; rw [if_neg h]
      have ht4 : t4 = t3' := by
        dsimp [t4]; rw [if_neg h]
      simp [hs4, ht4, AgentState.smallBiasInt]
  let s5 := if s4.role = .clock ∧ t4.role = .clock then stdCounterSubroutine L K s4 else s4
  let t5 := if s4.role = .clock ∧ t4.role = .clock then stdCounterSubroutine L K t4 else t4
  have h5 : AgentState.smallBiasInt s4 + AgentState.smallBiasInt t4 = AgentState.smallBiasInt s5 + AgentState.smallBiasInt t5 := by
    by_cases h : s4.role = .clock ∧ t4.role = .clock
    · rcases h with ⟨hs, ht⟩
      have hs5 : s5 = stdCounterSubroutine L K s4 := by
        dsimp [s5]; rw [if_pos ⟨hs, ht⟩]
      have ht5 : t5 = stdCounterSubroutine L K t4 := by
        dsimp [t5]; rw [if_pos ⟨hs, ht⟩]
      simp [hs5, ht5, hs, ht, AgentState.smallBiasInt]
      dsimp [stdCounterSubroutine, advancePhase]
      split_ifs <;> simp
    · have hs5 : s5 = s4 := by
        dsimp [s5]; rw [if_neg h]
      have ht5 : t5 = t4 := by
        dsimp [t5]; rw [if_neg h]
      simp [hs5, ht5, AgentState.smallBiasInt]
  calc
    AgentState.smallBiasInt s + AgentState.smallBiasInt t
        = AgentState.smallBiasInt s1 + AgentState.smallBiasInt t1 := h1
    _ = AgentState.smallBiasInt s2 + AgentState.smallBiasInt t2 := h2
    _ = AgentState.smallBiasInt s3 + AgentState.smallBiasInt t3 := h3
    _ = AgentState.smallBiasInt s3' + AgentState.smallBiasInt t3' := h3'
    _ = AgentState.smallBiasInt s4 + AgentState.smallBiasInt t4 := h4
    _ = AgentState.smallBiasInt s5 + AgentState.smallBiasInt t5 := h5

private lemma Phase0Transition_preserves_sum_of_quota (s t : AgentState L K)
    (hs_phase : s.phase.val = 0) (ht_phase : t.phase.val = 0)
    (hsq : well_formed_agent_quota s) (htq : well_formed_agent_quota t) :
    AgentState.smallBiasInt s + AgentState.smallBiasInt t =
      AgentState.smallBiasInt (Phase0Transition L K s t).1 +
        AgentState.smallBiasInt (Phase0Transition L K s t).2 := by
  let s1 := if s.role = .mcr ∧ t.role = .mcr then
    { s with role := .main, smallBias := addSmallBias s.smallBias t.smallBias } else s
  let t1 := if s.role = .mcr ∧ t.role = .mcr then
    { t with role := .cr, smallBias := ⟨3, by decide⟩ } else t
  have h1 : AgentState.smallBiasInt s + AgentState.smallBiasInt t =
      AgentState.smallBiasInt s1 + AgentState.smallBiasInt t1 := by
    by_cases h : s.role = .mcr ∧ t.role = .mcr
    · have hsum : (((s.smallBias.val : ℤ) - 3) +
          ((t.smallBias.val : ℤ) - 3)).natAbs ≤ 3 := by
        simpa [AgentState.smallBiasInt] using
          smallBias_pair_bound_of_mcr_mcr (L := L) (K := K) s t hs_phase ht_phase
            hsq htq h.1 h.2
      rcases h with ⟨hs_role, ht_role⟩
      simp [s1, t1, hs_role, ht_role, AgentState.smallBiasInt,
        addSmallBias_no_clamp s.smallBias t.smallBias hsum]
    · have hs1 : s1 = s := by
        dsimp [s1]; rw [if_neg h]
      have ht1 : t1 = t := by
        dsimp [t1]; rw [if_neg h]
      simp [hs1, ht1]
  let s2 := if s1.role = .mcr ∧ t1.role = .main ∧ ¬ t1.assigned then
              { s1 with role := .cr, smallBias := ⟨3, by decide⟩ }
            else if t1.role = .mcr ∧ s1.role = .main ∧ ¬ s1.assigned then
              { s1 with assigned := true, smallBias := addSmallBias t1.smallBias s1.smallBias }
            else s1
  let t2 := if s1.role = .mcr ∧ t1.role = .main ∧ ¬ t1.assigned then
              { t1 with assigned := true, smallBias := addSmallBias s1.smallBias t1.smallBias }
            else if t1.role = .mcr ∧ s1.role = .main ∧ ¬ s1.assigned then
              { t1 with role := .cr, smallBias := ⟨3, by decide⟩ }
            else t1
  have h2 : AgentState.smallBiasInt s1 + AgentState.smallBiasInt t1 =
      AgentState.smallBiasInt s2 + AgentState.smallBiasInt t2 := by
    by_cases h : s1.role = .mcr ∧ t1.role = .main ∧ ¬ t1.assigned
    · have hsum1_conv : (((s1.smallBias.val : ℤ) - 3) +
          ((t1.smallBias.val : ℤ) - 3)).natAbs ≤ 3 := by
        by_cases h0 : s.role = .mcr ∧ t.role = .mcr
        · have hsum0 : (AgentState.smallBiasInt s + AgentState.smallBiasInt t).natAbs ≤ 3 :=
            smallBias_pair_bound_of_mcr_mcr (L := L) (K := K) s t hs_phase ht_phase
              hsq htq h0.1 h0.2
          have hsum1 : (AgentState.smallBiasInt s1 + AgentState.smallBiasInt t1).natAbs ≤ 3 := by
            rw [← h1]
            exact hsum0
          simpa [AgentState.smallBiasInt] using hsum1
        · have hs1 : s1 = s := by
            dsimp [s1]; rw [if_neg h0]
          have ht1 : t1 = t := by
            dsimp [t1]; rw [if_neg h0]
          have hs_role : s.role = .mcr := by simpa [hs1] using h.1
          have ht_role : t.role = .main := by simpa [ht1] using h.2.1
          have ht_unassigned : t.assigned = false := by
            simpa [ht1] using h.2.2
          simpa [hs1, ht1, AgentState.smallBiasInt] using
            smallBias_pair_bound_of_mcr_main (L := L) (K := K) s t hs_phase ht_phase
              hsq htq hs_role ht_role ht_unassigned
      rcases h with ⟨hs_role, ht_role, ht_not⟩
      simp [hs_role, ht_role, ht_not, AgentState.smallBiasInt, s2, t2,
        addSmallBias_no_clamp s1.smallBias t1.smallBias hsum1_conv]
    · by_cases h' : t1.role = .mcr ∧ s1.role = .main ∧ ¬ s1.assigned
      · have hsum1_conv' : (((t1.smallBias.val : ℤ) - 3) +
            ((s1.smallBias.val : ℤ) - 3)).natAbs ≤ 3 := by
          by_cases h0 : s.role = .mcr ∧ t.role = .mcr
          · have hsum0 : (AgentState.smallBiasInt s + AgentState.smallBiasInt t).natAbs ≤ 3 :=
              smallBias_pair_bound_of_mcr_mcr (L := L) (K := K) s t hs_phase ht_phase
                hsq htq h0.1 h0.2
            have hsum1 : (AgentState.smallBiasInt t1 + AgentState.smallBiasInt s1).natAbs ≤ 3 := by
              have hsum1' : (AgentState.smallBiasInt s1 + AgentState.smallBiasInt t1).natAbs ≤ 3 := by
                rw [← h1]
                exact hsum0
              simpa [add_comm] using hsum1'
            simpa [AgentState.smallBiasInt] using hsum1
          · have hs1 : s1 = s := by
              dsimp [s1]; rw [if_neg h0]
            have ht1 : t1 = t := by
              dsimp [t1]; rw [if_neg h0]
            have ht_role : t.role = .mcr := by simpa [ht1] using h'.1
            have hs_role : s.role = .main := by simpa [hs1] using h'.2.1
            have hs_unassigned : s.assigned = false := by
              simpa [hs1] using h'.2.2
            simpa [hs1, ht1, AgentState.smallBiasInt, add_comm] using
              smallBias_pair_bound_of_main_mcr (L := L) (K := K) s t hs_phase ht_phase
                hsq htq hs_role ht_role hs_unassigned
        rcases h' with ⟨ht_role, hs_role, hs_not⟩
        simp [ht_role, hs_role, hs_not, AgentState.smallBiasInt, s2, t2,
          addSmallBias_no_clamp t1.smallBias s1.smallBias hsum1_conv',
          add_comm, add_left_comm, add_assoc]
      · have hs2 : s2 = s1 := by
          dsimp [s2]; rw [if_neg h, if_neg h']
        have ht2 : t2 = t1 := by
          dsimp [t2]; rw [if_neg h, if_neg h']
        simp [hs2, ht2, AgentState.smallBiasInt]
  let s3 := if s2.role = .mcr ∧ t2.role ≠ .main ∧ t2.role ≠ .mcr ∧ ¬ t2.assigned then s2
            else if t2.role = .mcr ∧ s2.role ≠ .main ∧ s2.role ≠ .mcr ∧ ¬ s2.assigned then
              { s2 with assigned := true }
            else s2
  let t3 := if s2.role = .mcr ∧ t2.role ≠ .main ∧ t2.role ≠ .mcr ∧ ¬ t2.assigned then
              { t2 with assigned := true }
            else if t2.role = .mcr ∧ s2.role ≠ .main ∧ s2.role ≠ .mcr ∧ ¬ s2.assigned then t2
            else t2
  have h3 : AgentState.smallBiasInt s2 + AgentState.smallBiasInt t2 =
      AgentState.smallBiasInt s3 + AgentState.smallBiasInt t3 := by
    by_cases h : s2.role = .mcr ∧ t2.role ≠ .main ∧ t2.role ≠ .mcr ∧ ¬ t2.assigned
    · rcases h with ⟨hs_role, ht_not_main, ht_not_mcr, ht_not⟩
      simp [hs_role, ht_not_main, ht_not_mcr, ht_not, AgentState.smallBiasInt, s3, t3]
    · by_cases h' : t2.role = .mcr ∧ s2.role ≠ .main ∧ s2.role ≠ .mcr ∧ ¬ s2.assigned
      · rcases h' with ⟨ht_role, hs_not_main, hs_not_mcr, hs_not⟩
        simp [ht_role, hs_not_main, hs_not_mcr, hs_not, AgentState.smallBiasInt, s3, t3]
      · have hs3 : s3 = s2 := by
          dsimp [s3]; rw [if_neg h, if_neg h']
        have ht3 : t3 = t2 := by
          dsimp [t3]; rw [if_neg h, if_neg h']
        simp [hs3, ht3, AgentState.smallBiasInt]
  let s3' := if s3.role = .mcr ∧ t3.role = .cr then { s3 with role := .main, assigned := true }
             else if t3.role = .mcr ∧ s3.role = .cr then s3
             else s3
  let t3' := if s3.role = .mcr ∧ t3.role = .cr then t3
             else if t3.role = .mcr ∧ s3.role = .cr then { t3 with role := .main, assigned := true }
             else t3
  have h3' : AgentState.smallBiasInt s3 + AgentState.smallBiasInt t3 =
      AgentState.smallBiasInt s3' + AgentState.smallBiasInt t3' := by
    by_cases h : s3.role = .mcr ∧ t3.role = .cr
    · rcases h with ⟨hs_role, ht_role⟩
      simp [hs_role, ht_role, AgentState.smallBiasInt, s3', t3']
    · by_cases h' : t3.role = .mcr ∧ s3.role = .cr
      · rcases h' with ⟨ht_role, hs_role⟩
        simp [ht_role, hs_role, AgentState.smallBiasInt, s3', t3']
      · have hs3' : s3' = s3 := by
          dsimp [s3']; rw [if_neg h, if_neg h']
        have ht3' : t3' = t3 := by
          dsimp [t3']; rw [if_neg h, if_neg h']
        simp [hs3', ht3', AgentState.smallBiasInt]
  let s4 := if s3'.role = .cr ∧ t3'.role = .cr then
              { s3' with role := .clock, counter := ⟨50 * (L + 1), by omega⟩ } else s3'
  let t4 := if s3'.role = .cr ∧ t3'.role = .cr then
              { t3' with role := .reserve } else t3'
  have h4 : AgentState.smallBiasInt s3' + AgentState.smallBiasInt t3' =
      AgentState.smallBiasInt s4 + AgentState.smallBiasInt t4 := by
    by_cases h : s3'.role = .cr ∧ t3'.role = .cr
    · rcases h with ⟨hs_role, ht_role⟩
      simp [hs_role, ht_role, AgentState.smallBiasInt, s4, t4]
    · have hs4 : s4 = s3' := by
        dsimp [s4]; rw [if_neg h]
      have ht4 : t4 = t3' := by
        dsimp [t4]; rw [if_neg h]
      simp [hs4, ht4, AgentState.smallBiasInt]
  let s5 := if s4.role = .clock ∧ t4.role = .clock then stdCounterSubroutine L K s4 else s4
  let t5 := if s4.role = .clock ∧ t4.role = .clock then stdCounterSubroutine L K t4 else t4
  have h5 : AgentState.smallBiasInt s4 + AgentState.smallBiasInt t4 =
      AgentState.smallBiasInt s5 + AgentState.smallBiasInt t5 := by
    by_cases h : s4.role = .clock ∧ t4.role = .clock
    · rcases h with ⟨hs, ht⟩
      have hs5 : s5 = stdCounterSubroutine L K s4 := by
        dsimp [s5]; rw [if_pos ⟨hs, ht⟩]
      have ht5 : t5 = stdCounterSubroutine L K t4 := by
        dsimp [t5]; rw [if_pos ⟨hs, ht⟩]
      simp [hs5, ht5, hs, ht, AgentState.smallBiasInt]
      dsimp [stdCounterSubroutine, advancePhase]
      split_ifs <;> simp
    · have hs5 : s5 = s4 := by
        dsimp [s5]; rw [if_neg h]
      have ht5 : t5 = t4 := by
        dsimp [t5]; rw [if_neg h]
      simp [hs5, ht5, AgentState.smallBiasInt]
  calc
    AgentState.smallBiasInt s + AgentState.smallBiasInt t
        = AgentState.smallBiasInt s1 + AgentState.smallBiasInt t1 := h1
    _ = AgentState.smallBiasInt s2 + AgentState.smallBiasInt t2 := h2
    _ = AgentState.smallBiasInt s3 + AgentState.smallBiasInt t3 := h3
    _ = AgentState.smallBiasInt s3' + AgentState.smallBiasInt t3' := h3'
    _ = AgentState.smallBiasInt s4 + AgentState.smallBiasInt t4 := h4
    _ = AgentState.smallBiasInt s5 + AgentState.smallBiasInt t5 := h5

private theorem Phase0Transition_preserves_well_formed_agent_quota (s t : AgentState L K)
    (hs_phase : s.phase.val = 0) (ht_phase : t.phase.val = 0) :
    well_formed_agent_quota s → well_formed_agent_quota t →
    well_formed_agent_quota (Phase0Transition L K s t).1 ∧
    well_formed_agent_quota (Phase0Transition L K s t).2 := by
  intro hs ht
  let s1 := if s.role = .mcr ∧ t.role = .mcr then
    { s with role := .main, smallBias := addSmallBias s.smallBias t.smallBias } else s
  let t1 := if s.role = .mcr ∧ t.role = .mcr then
    { t with role := .cr, smallBias := ⟨3, by decide⟩ } else t
  have hs1 : smallBiasQuotaFields s1 := by
    by_cases h : s.role = .mcr ∧ t.role = .mcr
    · rcases h with ⟨hs_role, ht_role⟩
      have hs_abs : (AgentState.smallBiasInt s).natAbs ≤ 1 := (hs hs_phase).1 hs_role
      have ht_abs : (AgentState.smallBiasInt t).natAbs ≤ 1 := (ht ht_phase).1 ht_role
      have hsum3 : (((s.smallBias.val : ℤ) - 3) +
          ((t.smallBias.val : ℤ) - 3)).natAbs ≤ 3 := by
        have : (AgentState.smallBiasInt s + AgentState.smallBiasInt t).natAbs ≤ 3 := by
          omega
        simpa [AgentState.smallBiasInt] using this
      have hsum2 : (((s.smallBias.val : ℤ) - 3) +
          ((t.smallBias.val : ℤ) - 3)).natAbs ≤ 2 := by
        simpa [AgentState.smallBiasInt] using (by
          have : (AgentState.smallBiasInt s + AgentState.smallBiasInt t).natAbs ≤ 2 := by
            omega
          exact this)
      constructor
      · intro hrole
        simp [s1, hs_role, ht_role] at hrole
      · intro _hmain _hassigned
        simp [s1, hs_role, ht_role, AgentState.smallBiasInt,
          addSmallBias_no_clamp s.smallBias t.smallBias hsum3]
        exact hsum2
    · have hs1eq : s1 = s := by
        dsimp [s1]; rw [if_neg h]
      simpa [hs1eq] using smallBiasQuotaFields_of_well_formed_agent_quota
        (L := L) (K := K) s hs_phase hs
  have ht1 : smallBiasQuotaFields t1 := by
    by_cases h : s.role = .mcr ∧ t.role = .mcr
    · rcases h with ⟨hs_role, ht_role⟩
      constructor
      · intro hrole
        simp [t1, hs_role, ht_role] at hrole
      · intro hmain
        simp [t1, hs_role, ht_role] at hmain
    · have ht1eq : t1 = t := by
        dsimp [t1]; rw [if_neg h]
      simpa [ht1eq] using smallBiasQuotaFields_of_well_formed_agent_quota
        (L := L) (K := K) t ht_phase ht
  let s2 := if s1.role = .mcr ∧ t1.role = .main ∧ ¬ t1.assigned then
              { s1 with role := .cr, smallBias := ⟨3, by decide⟩ }
            else if t1.role = .mcr ∧ s1.role = .main ∧ ¬ s1.assigned then
              { s1 with assigned := true, smallBias := addSmallBias t1.smallBias s1.smallBias }
            else s1
  let t2 := if s1.role = .mcr ∧ t1.role = .main ∧ ¬ t1.assigned then
              { t1 with assigned := true, smallBias := addSmallBias s1.smallBias t1.smallBias }
            else if t1.role = .mcr ∧ s1.role = .main ∧ ¬ s1.assigned then
              { t1 with role := .cr, smallBias := ⟨3, by decide⟩ }
            else t1
  have hs2 : smallBiasQuotaFields s2 := by
    by_cases h : s1.role = .mcr ∧ t1.role = .main ∧ ¬ t1.assigned
    · rcases h with ⟨hs_role, ht_role, ht_unassigned⟩
      constructor
      · intro hrole
        simp [s2, hs_role, ht_role, ht_unassigned] at hrole
      · intro hmain
        simp [s2, hs_role, ht_role, ht_unassigned] at hmain
    · by_cases h' : t1.role = .mcr ∧ s1.role = .main ∧ ¬ s1.assigned
      · rcases h' with ⟨ht_role, hs_role, hs_unassigned⟩
        constructor
        · intro hrole
          simp [s2, h, ht_role, hs_role, hs_unassigned] at hrole
        · intro _hmain hassigned
          simp [s2, h, ht_role, hs_role, hs_unassigned] at hassigned
      · have hs2eq : s2 = s1 := by
          dsimp [s2]; rw [if_neg h, if_neg h']
        simpa [hs2eq] using hs1
  have ht2 : smallBiasQuotaFields t2 := by
    by_cases h : s1.role = .mcr ∧ t1.role = .main ∧ ¬ t1.assigned
    · rcases h with ⟨hs_role, ht_role, ht_unassigned⟩
      constructor
      · intro hrole
        simp [t2, hs_role, ht_role, ht_unassigned] at hrole
      · intro _hmain hassigned
        simp [t2, hs_role, ht_role, ht_unassigned] at hassigned
    · by_cases h' : t1.role = .mcr ∧ s1.role = .main ∧ ¬ s1.assigned
      · rcases h' with ⟨ht_role, hs_role, hs_unassigned⟩
        constructor
        · intro hrole
          simp [t2, h, ht_role, hs_role, hs_unassigned] at hrole
        · intro hmain
          simp [t2, h, ht_role, hs_role, hs_unassigned] at hmain
      · have ht2eq : t2 = t1 := by
          dsimp [t2]; rw [if_neg h, if_neg h']
        simpa [ht2eq] using ht1
  let s3 := if s2.role = .mcr ∧ t2.role ≠ .main ∧ t2.role ≠ .mcr ∧ ¬ t2.assigned then s2
            else if t2.role = .mcr ∧ s2.role ≠ .main ∧ s2.role ≠ .mcr ∧ ¬ s2.assigned then
              { s2 with assigned := true }
            else s2
  let t3 := if s2.role = .mcr ∧ t2.role ≠ .main ∧ t2.role ≠ .mcr ∧ ¬ t2.assigned then
              { t2 with assigned := true }
            else if t2.role = .mcr ∧ s2.role ≠ .main ∧ s2.role ≠ .mcr ∧ ¬ s2.assigned then t2
            else t2
  have hs3 : smallBiasQuotaFields s3 := by
    dsimp [s3]
    split_ifs <;> simp_all [smallBiasQuotaFields]
  have ht3 : smallBiasQuotaFields t3 := by
    dsimp [t3]
    split_ifs <;> simp_all [smallBiasQuotaFields]
  let s3' := if s3.role = .mcr ∧ t3.role = .cr then { s3 with role := .main, assigned := true }
             else if t3.role = .mcr ∧ s3.role = .cr then s3
             else s3
  let t3' := if s3.role = .mcr ∧ t3.role = .cr then t3
             else if t3.role = .mcr ∧ s3.role = .cr then { t3 with role := .main, assigned := true }
             else t3
  have hs3' : smallBiasQuotaFields s3' := by
    dsimp [s3']
    split_ifs <;> simp_all [smallBiasQuotaFields]
  have ht3' : smallBiasQuotaFields t3' := by
    dsimp [t3']
    split_ifs <;> simp_all [smallBiasQuotaFields]
  let s4 := if s3'.role = .cr ∧ t3'.role = .cr then
              { s3' with role := .clock, counter := ⟨50 * (L + 1), by omega⟩ } else s3'
  let t4 := if s3'.role = .cr ∧ t3'.role = .cr then
              { t3' with role := .reserve } else t3'
  have hs4 : smallBiasQuotaFields s4 := by
    dsimp [s4]
    split_ifs <;> simp_all [smallBiasQuotaFields]
  have ht4 : smallBiasQuotaFields t4 := by
    dsimp [t4]
    split_ifs <;> simp_all [smallBiasQuotaFields]
  let s5 := if s4.role = .clock ∧ t4.role = .clock then stdCounterSubroutine L K s4 else s4
  let t5 := if s4.role = .clock ∧ t4.role = .clock then stdCounterSubroutine L K t4 else t4
  have hs5 : smallBiasQuotaFields s5 := by
    by_cases hclock : s4.role = .clock ∧ t4.role = .clock
    · rcases hclock with ⟨hsclock, htclock⟩
      have hs5eq : s5 = stdCounterSubroutine L K s4 := by
        dsimp [s5]; rw [if_pos ⟨hsclock, htclock⟩]
      rw [hs5eq]
      unfold stdCounterSubroutine advancePhase
      split_ifs <;> simp [smallBiasQuotaFields, hsclock]
    · have hs5eq : s5 = s4 := by
        dsimp [s5]; rw [if_neg hclock]
      simpa [hs5eq] using hs4
  have ht5 : smallBiasQuotaFields t5 := by
    by_cases hclock : s4.role = .clock ∧ t4.role = .clock
    · rcases hclock with ⟨hsclock, htclock⟩
      have ht5eq : t5 = stdCounterSubroutine L K t4 := by
        dsimp [t5]; rw [if_pos ⟨hsclock, htclock⟩]
      rw [ht5eq]
      unfold stdCounterSubroutine advancePhase
      split_ifs <;> simp [smallBiasQuotaFields, htclock]
    · have ht5eq : t5 = t4 := by
        dsimp [t5]; rw [if_neg hclock]
      simpa [ht5eq] using ht4
  constructor
  · intro _hphase
    exact hs5
  · intro _hphase
    exact ht5

private lemma Phase1Transition_preserves_sum (s t : AgentState L K) :
    AgentState.smallBiasInt s + AgentState.smallBiasInt t =
    AgentState.smallBiasInt (Phase1Transition L K s t).1 + AgentState.smallBiasInt (Phase1Transition L K s t).2 := by
  simp [AgentState.smallBiasInt, Phase1Transition]; split_ifs <;> push_cast <;> linarith [avgFin7_preserves_sum (s.smallBias) (t.smallBias)]

private lemma Phase2Transition_preserves_sum (s t : AgentState L K) :
    AgentState.smallBiasInt s + AgentState.smallBiasInt t =
    AgentState.smallBiasInt (Phase2Transition L K s t).1 +
      AgentState.smallBiasInt (Phase2Transition L K s t).2 := by
  rcases Phase2Transition_preserves_smallBias L K s t with ⟨hs, ht⟩
  simp [AgentState.smallBiasInt, hs, ht]

private lemma phase3CancelSplit_preserves_smallBias (s t : AgentState L K) :
    (phase3CancelSplit L K s t).1.smallBias = s.smallBias ∧
    (phase3CancelSplit L K s t).2.smallBias = t.smallBias := by
  unfold phase3CancelSplit
  match s.bias, t.bias with
  | .zero, .zero => simp
  | .zero, .dyadic _ _ => simp; split_ifs <;> simp
  | .dyadic _ _, .zero => simp; split_ifs <;> simp
  | .dyadic .pos _, .dyadic .pos _ => simp
  | .dyadic .pos _, .dyadic .neg _ => simp; split_ifs <;> simp
  | .dyadic .neg _, .dyadic .pos _ => simp; split_ifs <;> simp
  | .dyadic .neg _, .dyadic .neg _ => simp

private lemma Phase3Transition_preserves_sum (s t : AgentState L K) :
    AgentState.smallBiasInt s + AgentState.smallBiasInt t =
    AgentState.smallBiasInt (Phase3Transition L K s t).1 +
      AgentState.smallBiasInt (Phase3Transition L K s t).2 := by
  let s1 := if s.role = .clock ∧ t.role = .clock then
    if s.minute ≠ t.minute then
      let pmax := max s.minute t.minute
      { s with minute := pmax }
    else if h_max : s.minute.val < K * (L + 1) then
      { s with minute := ⟨s.minute.val + 1, by omega⟩ }
    else
      stdCounterSubroutine L K s
  else s
  let t1 := if s.role = .clock ∧ t.role = .clock then
    if s.minute ≠ t.minute then
      let pmax := max s.minute t.minute
      { t with minute := pmax }
    else if h_max : s.minute.val < K * (L + 1) then
      t
    else
      stdCounterSubroutine L K t
  else t
  let s2 := if s1.role = .main ∧ s1.bias = .zero ∧ t1.role = .clock then
    let hVal := min L (t1.minute.val / K)
    have h_hour_lt : hVal < L + 1 := by
      apply Nat.lt_succ_of_le; exact Nat.min_le_left _ _
    { s1 with hour := ⟨hVal, h_hour_lt⟩ }
  else if t1.role = .main ∧ t1.bias = .zero ∧ s1.role = .clock then
    s1
  else s1
  let t2 := if s1.role = .main ∧ s1.bias = .zero ∧ t1.role = .clock then
    t1
  else if t1.role = .main ∧ t1.bias = .zero ∧ s1.role = .clock then
    let hVal := min L (s1.minute.val / K)
    have h_hour_lt : hVal < L + 1 := by
      apply Nat.lt_succ_of_le; exact Nat.min_le_left _ _
    { t1 with hour := ⟨hVal, h_hour_lt⟩ }
  else t1
  have hs1 : s1.smallBias = s.smallBias := by
    dsimp [s1]
    split_ifs <;> simp [stdCounterSubroutine_smallBias]
  have ht1 : t1.smallBias = t.smallBias := by
    dsimp [t1]
    split_ifs <;> simp [stdCounterSubroutine_smallBias]
  have hs2 : s2.smallBias = s1.smallBias := by
    dsimp [s2]
    split_ifs <;> simp
  have ht2 : t2.smallBias = t1.smallBias := by
    dsimp [t2]
    split_ifs <;> simp
  have hfinal :
      AgentState.smallBiasInt s2 + AgentState.smallBiasInt t2 =
      AgentState.smallBiasInt (Phase3Transition L K s t).1 +
        AgentState.smallBiasInt (Phase3Transition L K s t).2 := by
    unfold Phase3Transition
    change AgentState.smallBiasInt s2 + AgentState.smallBiasInt t2 =
      AgentState.smallBiasInt
        (if s2.role = .main ∧ t2.role = .main then phase3CancelSplit L K s2 t2
         else (s2, t2)).1 +
      AgentState.smallBiasInt
        (if s2.role = .main ∧ t2.role = .main then phase3CancelSplit L K s2 t2
         else (s2, t2)).2
    by_cases hmain : s2.role = .main ∧ t2.role = .main
    · rcases phase3CancelSplit_preserves_smallBias (L := L) (K := K) s2 t2 with ⟨hs, ht⟩
      simp [hmain, AgentState.smallBiasInt, hs, ht]
    · simp [hmain]
  calc
    AgentState.smallBiasInt s + AgentState.smallBiasInt t
        = AgentState.smallBiasInt s1 + AgentState.smallBiasInt t1 := by
          simp [AgentState.smallBiasInt, hs1, ht1]
    _ = AgentState.smallBiasInt s2 + AgentState.smallBiasInt t2 := by
          simp [AgentState.smallBiasInt, hs2, ht2]
    _ = AgentState.smallBiasInt (Phase3Transition L K s t).1 +
          AgentState.smallBiasInt (Phase3Transition L K s t).2 := hfinal

private lemma Phase4Transition_preserves_sum (s t : AgentState L K) :
    AgentState.smallBiasInt s + AgentState.smallBiasInt t =
    AgentState.smallBiasInt (Phase4Transition L K s t).1 +
      AgentState.smallBiasInt (Phase4Transition L K s t).2 := by
  rcases Phase4Transition_preserves_smallBias L K s t with ⟨hs, ht⟩
  simp [AgentState.smallBiasInt, hs, ht]

private lemma Phase5Transition_preserves_sum (s t : AgentState L K) :
    AgentState.smallBiasInt s + AgentState.smallBiasInt t =
    AgentState.smallBiasInt (Phase5Transition L K s t).1 +
      AgentState.smallBiasInt (Phase5Transition L K s t).2 := by
  unfold Phase5Transition
  dsimp
  split_ifs <;> simp [AgentState.smallBiasInt, stdCounterSubroutine_smallBias]

private lemma doSplit_preserves_smallBias (r m : AgentState L K) :
    (doSplit L K r m).1.smallBias = r.smallBias ∧
    (doSplit L K r m).2.smallBias = m.smallBias := by
  unfold doSplit
  match m.bias with
  | .zero => simp
  | .dyadic _ _ => simp; split_ifs <;> simp

private lemma Phase6Transition_preserves_sum (s t : AgentState L K) :
    AgentState.smallBiasInt s + AgentState.smallBiasInt t =
    AgentState.smallBiasInt (Phase6Transition L K s t).1 +
      AgentState.smallBiasInt (Phase6Transition L K s t).2 := by
  unfold Phase6Transition
  dsimp
  split_ifs <;>
    simp [AgentState.smallBiasInt, stdCounterSubroutine_smallBias, doSplit_preserves_smallBias]

private lemma cancelSplit_preserves_smallBias (s t : AgentState L K) :
    (cancelSplit L K s t).1.smallBias = s.smallBias ∧
    (cancelSplit L K s t).2.smallBias = t.smallBias := by
  unfold cancelSplit
  match s.bias, t.bias with
  | .zero, _ => simp
  | .dyadic _ _, .zero => simp
  | .dyadic _ _, .dyadic _ _ => simp; split_ifs <;> simp

private lemma Phase7Transition_preserves_sum (s t : AgentState L K) :
    AgentState.smallBiasInt s + AgentState.smallBiasInt t =
    AgentState.smallBiasInt (Phase7Transition L K s t).1 +
      AgentState.smallBiasInt (Phase7Transition L K s t).2 := by
  unfold Phase7Transition
  dsimp
  split_ifs <;>
    simp [AgentState.smallBiasInt, stdCounterSubroutine_smallBias,
      cancelSplit_preserves_smallBias]

private lemma absorbConsume_preserves_smallBias (s t : AgentState L K) :
    (absorbConsume L K s t).1.smallBias = s.smallBias ∧
    (absorbConsume L K s t).2.smallBias = t.smallBias := by
  unfold absorbConsume
  match s.bias, t.bias with
  | .zero, _ => simp
  | .dyadic .pos _, .zero => simp
  | .dyadic .neg _, .zero => simp
  | .dyadic .pos _, .dyadic .pos _ => simp
  | .dyadic .neg _, .dyadic .neg _ => simp
  | .dyadic .pos _, .dyadic .neg _ => simp; split_ifs <;> simp
  | .dyadic .neg _, .dyadic .pos _ => simp; split_ifs <;> simp

private lemma Phase8Transition_preserves_sum (s t : AgentState L K) :
    AgentState.smallBiasInt s + AgentState.smallBiasInt t =
    AgentState.smallBiasInt (Phase8Transition L K s t).1 +
      AgentState.smallBiasInt (Phase8Transition L K s t).2 := by
  unfold Phase8Transition
  dsimp
  split_ifs <;>
    simp [AgentState.smallBiasInt, stdCounterSubroutine_smallBias,
      absorbConsume_preserves_smallBias]

private lemma Phase9Transition_preserves_sum (s t : AgentState L K) :
    AgentState.smallBiasInt s + AgentState.smallBiasInt t =
    AgentState.smallBiasInt (Phase9Transition L K s t).1 +
      AgentState.smallBiasInt (Phase9Transition L K s t).2 := by
  rcases Phase9Transition_preserves_smallBias L K s t with ⟨hs, ht⟩
  simp [AgentState.smallBiasInt, hs, ht]

private lemma Phase10Transition_preserves_sum (s t : AgentState L K) :
    AgentState.smallBiasInt s + AgentState.smallBiasInt t =
    AgentState.smallBiasInt (Phase10Transition L K s t).1 +
      AgentState.smallBiasInt (Phase10Transition L K s t).2 := by
  unfold Phase10Transition
  dsimp
  split_ifs <;> simp [AgentState.smallBiasInt]

theorem smallBiasSum_step_invariant (s t : AgentState L K)
    (_hs : s.phase.val ≤ 1) (_ht : t.phase.val ≤ 1)
    (hsum : (AgentState.smallBiasInt s + AgentState.smallBiasInt t).natAbs ≤ 3) :
    AgentState.smallBiasInt s + AgentState.smallBiasInt t =
      AgentState.smallBiasInt ((Transition L K s t).1) + AgentState.smallBiasInt ((Transition L K s t).2) := by
  have hep_sum := phaseEpidemicUpdate_smallBiasInt_eq (L := L) (K := K) s t
  unfold Transition
  let s' := (phaseEpidemicUpdate L K s t).1
  let t' := (phaseEpidemicUpdate L K s t).2
  have hsum_ep : (AgentState.smallBiasInt s' + AgentState.smallBiasInt t').natAbs ≤ 3 := by
    rw [← hep_sum]
    exact hsum
  change AgentState.smallBiasInt s + AgentState.smallBiasInt t =
    AgentState.smallBiasInt (match s'.phase with
    | ⟨0, _⟩ => Phase0Transition L K s' t'
    | ⟨1, _⟩ => Phase1Transition L K s' t'
    | ⟨2, _⟩ => Phase2Transition L K s' t'
    | ⟨3, _⟩ => Phase3Transition L K s' t'
    | ⟨4, _⟩ => Phase4Transition L K s' t'
    | ⟨5, _⟩ => Phase5Transition L K s' t'
    | ⟨6, _⟩ => Phase6Transition L K s' t'
    | ⟨7, _⟩ => Phase7Transition L K s' t'
    | ⟨8, _⟩ => Phase8Transition L K s' t'
    | ⟨9, _⟩ => Phase9Transition L K s' t'
    | ⟨10, _⟩ => Phase10Transition L K s' t'
    | _ => (s', t')).1 +
    AgentState.smallBiasInt (match s'.phase with
    | ⟨0, _⟩ => Phase0Transition L K s' t'
    | ⟨1, _⟩ => Phase1Transition L K s' t'
    | ⟨2, _⟩ => Phase2Transition L K s' t'
    | ⟨3, _⟩ => Phase3Transition L K s' t'
    | ⟨4, _⟩ => Phase4Transition L K s' t'
    | ⟨5, _⟩ => Phase5Transition L K s' t'
    | ⟨6, _⟩ => Phase6Transition L K s' t'
    | ⟨7, _⟩ => Phase7Transition L K s' t'
    | ⟨8, _⟩ => Phase8Transition L K s' t'
    | ⟨9, _⟩ => Phase9Transition L K s' t'
    | ⟨10, _⟩ => Phase10Transition L K s' t'
    | _ => (s', t')).2
  rcases h_phase : s'.phase with ⟨n, hn⟩
  rw [hep_sum]
  match n, hn with
  | 0, _ => exact Phase0Transition_preserves_sum (L := L) (K := K) s' t' hsum_ep
  | 1, _ => exact Phase1Transition_preserves_sum (L := L) (K := K) s' t'
  | 2, _ => exact Phase2Transition_preserves_sum (L := L) (K := K) s' t'
  | 3, _ => exact Phase3Transition_preserves_sum (L := L) (K := K) s' t'
  | 4, _ => exact Phase4Transition_preserves_sum (L := L) (K := K) s' t'
  | 5, _ => exact Phase5Transition_preserves_sum (L := L) (K := K) s' t'
  | 6, _ => exact Phase6Transition_preserves_sum (L := L) (K := K) s' t'
  | 7, _ => exact Phase7Transition_preserves_sum (L := L) (K := K) s' t'
  | 8, _ => exact Phase8Transition_preserves_sum (L := L) (K := K) s' t'
  | 9, _ => exact Phase9Transition_preserves_sum (L := L) (K := K) s' t'
  | 10, _ => exact Phase10Transition_preserves_sum (L := L) (K := K) s' t'
  | n + 11, hn => omega

private theorem smallBiasSum_step_invariant_of_quota (s t : AgentState L K)
    (hsq : well_formed_agent_quota s) (htq : well_formed_agent_quota t) :
    AgentState.smallBiasInt s + AgentState.smallBiasInt t =
      AgentState.smallBiasInt ((Transition L K s t).1) +
      AgentState.smallBiasInt ((Transition L K s t).2) := by
  have hep_sum := phaseEpidemicUpdate_smallBiasInt_eq (L := L) (K := K) s t
  unfold Transition
  let s' := (phaseEpidemicUpdate L K s t).1
  let t' := (phaseEpidemicUpdate L K s t).2
  change AgentState.smallBiasInt s + AgentState.smallBiasInt t =
    AgentState.smallBiasInt (match s'.phase with
    | ⟨0, _⟩ => Phase0Transition L K s' t'
    | ⟨1, _⟩ => Phase1Transition L K s' t'
    | ⟨2, _⟩ => Phase2Transition L K s' t'
    | ⟨3, _⟩ => Phase3Transition L K s' t'
    | ⟨4, _⟩ => Phase4Transition L K s' t'
    | ⟨5, _⟩ => Phase5Transition L K s' t'
    | ⟨6, _⟩ => Phase6Transition L K s' t'
    | ⟨7, _⟩ => Phase7Transition L K s' t'
    | ⟨8, _⟩ => Phase8Transition L K s' t'
    | ⟨9, _⟩ => Phase9Transition L K s' t'
    | ⟨10, _⟩ => Phase10Transition L K s' t'
    | _ => (s', t')).1 +
    AgentState.smallBiasInt (match s'.phase with
    | ⟨0, _⟩ => Phase0Transition L K s' t'
    | ⟨1, _⟩ => Phase1Transition L K s' t'
    | ⟨2, _⟩ => Phase2Transition L K s' t'
    | ⟨3, _⟩ => Phase3Transition L K s' t'
    | ⟨4, _⟩ => Phase4Transition L K s' t'
    | ⟨5, _⟩ => Phase5Transition L K s' t'
    | ⟨6, _⟩ => Phase6Transition L K s' t'
    | ⟨7, _⟩ => Phase7Transition L K s' t'
    | ⟨8, _⟩ => Phase8Transition L K s' t'
    | ⟨9, _⟩ => Phase9Transition L K s' t'
    | ⟨10, _⟩ => Phase10Transition L K s' t'
    | _ => (s', t')).2
  rcases h_phase : s'.phase with ⟨n, hn⟩
  rw [hep_sum]
  match n, hn with
  | 0, _ =>
    have hs'_zero : s'.phase.val = 0 := by simpa [h_phase]
    have hep_eq : phaseEpidemicUpdate L K s t = (s, t) :=
      phaseEpidemicUpdate_eq_of_left_phase_zero (L := L) (K := K) s t (by simpa [s'] using hs'_zero)
    have hs'_eq : s' = s := by
      dsimp [s']
      simpa using congrArg Prod.fst hep_eq
    have ht'_eq : t' = t := by
      dsimp [t']
      simpa using congrArg Prod.snd hep_eq
    rw [hep_eq, hs'_eq, ht'_eq]
    exact Phase0Transition_preserves_sum_of_quota (L := L) (K := K) s t
      (by simpa [hs'_eq] using hs'_zero) (by
        have : t.phase.val = 0 := by
          have hmax : max s.phase.val t.phase.val = 0 := by
            have hle := phaseEpidemicUpdate_left_phase_ge_max (L := L) (K := K) s t
            have hle0 : max s.phase.val t.phase.val ≤ 0 := by
              simpa [s', hs'_zero] using hle
            omega
          have hle : t.phase.val ≤ max s.phase.val t.phase.val := Nat.le_max_right _ _
          omega
        exact this)
      hsq htq
  | 1, _ => exact Phase1Transition_preserves_sum (L := L) (K := K) s' t'
  | 2, _ => exact Phase2Transition_preserves_sum (L := L) (K := K) s' t'
  | 3, _ => exact Phase3Transition_preserves_sum (L := L) (K := K) s' t'
  | 4, _ => exact Phase4Transition_preserves_sum (L := L) (K := K) s' t'
  | 5, _ => exact Phase5Transition_preserves_sum (L := L) (K := K) s' t'
  | 6, _ => exact Phase6Transition_preserves_sum (L := L) (K := K) s' t'
  | 7, _ => exact Phase7Transition_preserves_sum (L := L) (K := K) s' t'
  | 8, _ => exact Phase8Transition_preserves_sum (L := L) (K := K) s' t'
  | 9, _ => exact Phase9Transition_preserves_sum (L := L) (K := K) s' t'
  | 10, _ => exact Phase10Transition_preserves_sum (L := L) (K := K) s' t'
  | n + 11, hn => omega

private lemma well_formed_agent_quota_of_phase_pos (a : AgentState L K)
    (hpos : 1 ≤ a.phase.val) : well_formed_agent_quota a := by
  intro hzero
  omega

private theorem Transition_preserves_well_formed_agent_quota (s t : AgentState L K) :
    well_formed_agent_quota s → well_formed_agent_quota t →
    well_formed_agent_quota (Transition L K s t).1 ∧
    well_formed_agent_quota (Transition L K s t).2 := by
  intro hsq htq
  unfold Transition
  let s' := (phaseEpidemicUpdate L K s t).1
  let t' := (phaseEpidemicUpdate L K s t).2
  change well_formed_agent_quota (match s'.phase with
    | ⟨0, _⟩ => Phase0Transition L K s' t'
    | ⟨1, _⟩ => Phase1Transition L K s' t'
    | ⟨2, _⟩ => Phase2Transition L K s' t'
    | ⟨3, _⟩ => Phase3Transition L K s' t'
    | ⟨4, _⟩ => Phase4Transition L K s' t'
    | ⟨5, _⟩ => Phase5Transition L K s' t'
    | ⟨6, _⟩ => Phase6Transition L K s' t'
    | ⟨7, _⟩ => Phase7Transition L K s' t'
    | ⟨8, _⟩ => Phase8Transition L K s' t'
    | ⟨9, _⟩ => Phase9Transition L K s' t'
    | ⟨10, _⟩ => Phase10Transition L K s' t'
    | _ => (s', t')).1 ∧
    well_formed_agent_quota (match s'.phase with
    | ⟨0, _⟩ => Phase0Transition L K s' t'
    | ⟨1, _⟩ => Phase1Transition L K s' t'
    | ⟨2, _⟩ => Phase2Transition L K s' t'
    | ⟨3, _⟩ => Phase3Transition L K s' t'
    | ⟨4, _⟩ => Phase4Transition L K s' t'
    | ⟨5, _⟩ => Phase5Transition L K s' t'
    | ⟨6, _⟩ => Phase6Transition L K s' t'
    | ⟨7, _⟩ => Phase7Transition L K s' t'
    | ⟨8, _⟩ => Phase8Transition L K s' t'
    | ⟨9, _⟩ => Phase9Transition L K s' t'
    | ⟨10, _⟩ => Phase10Transition L K s' t'
    | _ => (s', t')).2
  rcases h_phase : s'.phase with ⟨n, hn⟩
  match n, hn with
  | 0, _ =>
    have hs'_zero : s'.phase.val = 0 := by simpa [h_phase]
    have hep_eq : phaseEpidemicUpdate L K s t = (s, t) :=
      phaseEpidemicUpdate_eq_of_left_phase_zero (L := L) (K := K) s t (by simpa [s'] using hs'_zero)
    have hs'_eq : s' = s := by
      dsimp [s']
      simpa using congrArg Prod.fst hep_eq
    have ht'_eq : t' = t := by
      dsimp [t']
      simpa using congrArg Prod.snd hep_eq
    rw [hs'_eq, ht'_eq]
    exact Phase0Transition_preserves_well_formed_agent_quota (L := L) (K := K) s t
      (by simpa [hs'_eq] using hs'_zero)
      (by
        have hmax : max s.phase.val t.phase.val = 0 := by
          have hle := phaseEpidemicUpdate_left_phase_ge_max (L := L) (K := K) s t
          have hle0 : max s.phase.val t.phase.val ≤ 0 := by
            simpa [s', hs'_zero] using hle
          omega
        have hle : t.phase.val ≤ max s.phase.val t.phase.val := Nat.le_max_right _ _
        omega)
      hsq htq
  | 1, _ =>
    rcases Phase1Transition_phase_nondec L K s' t' with ⟨hsmono, htmono⟩
    have htpos : 1 ≤ t'.phase.val :=
      phaseEpidemicUpdate_right_phase_pos_of_left_phase_pos_quota (L := L) (K := K)
        s t (by simpa [s', h_phase])
    have hspos0 : 1 ≤ s'.phase.val := by simpa [h_phase]
    have hspos : 1 ≤ (Phase1Transition L K s' t').1.phase.val := le_trans hspos0 hsmono
    have htpos_out : 1 ≤ (Phase1Transition L K s' t').2.phase.val := le_trans htpos htmono
    exact ⟨by simpa using well_formed_agent_quota_of_phase_pos (Phase1Transition L K s' t').1 hspos,
      by simpa using well_formed_agent_quota_of_phase_pos (Phase1Transition L K s' t').2 htpos_out⟩
  | 2, _ =>
    rcases Phase2Transition_phase_nondec L K s' t' with ⟨hsmono, htmono⟩
    have htpos : 1 ≤ t'.phase.val :=
      phaseEpidemicUpdate_right_phase_pos_of_left_phase_pos_quota (L := L) (K := K)
        s t (by simpa [s', h_phase])
    have hspos0 : 1 ≤ s'.phase.val := by simpa [h_phase]
    have hspos : 1 ≤ (Phase2Transition L K s' t').1.phase.val := le_trans hspos0 hsmono
    have htpos_out : 1 ≤ (Phase2Transition L K s' t').2.phase.val := le_trans htpos htmono
    exact ⟨by simpa using well_formed_agent_quota_of_phase_pos (Phase2Transition L K s' t').1 hspos,
      by simpa using well_formed_agent_quota_of_phase_pos (Phase2Transition L K s' t').2 htpos_out⟩
  | 3, _ =>
    rcases Phase3Transition_phase_nondec L K s' t' with ⟨hsmono, htmono⟩
    have htpos : 1 ≤ t'.phase.val :=
      phaseEpidemicUpdate_right_phase_pos_of_left_phase_pos_quota (L := L) (K := K)
        s t (by simpa [s', h_phase])
    have hspos0 : 1 ≤ s'.phase.val := by simpa [h_phase]
    have hspos : 1 ≤ (Phase3Transition L K s' t').1.phase.val := le_trans hspos0 hsmono
    have htpos_out : 1 ≤ (Phase3Transition L K s' t').2.phase.val := le_trans htpos htmono
    exact ⟨by simpa using well_formed_agent_quota_of_phase_pos (Phase3Transition L K s' t').1 hspos,
      by simpa using well_formed_agent_quota_of_phase_pos (Phase3Transition L K s' t').2 htpos_out⟩
  | 4, _ =>
    rcases Phase4Transition_phase_nondec L K s' t' with ⟨hsmono, htmono⟩
    have htpos : 1 ≤ t'.phase.val :=
      phaseEpidemicUpdate_right_phase_pos_of_left_phase_pos_quota (L := L) (K := K)
        s t (by simpa [s', h_phase])
    have hspos0 : 1 ≤ s'.phase.val := by simpa [h_phase]
    have hspos : 1 ≤ (Phase4Transition L K s' t').1.phase.val := le_trans hspos0 hsmono
    have htpos_out : 1 ≤ (Phase4Transition L K s' t').2.phase.val := le_trans htpos htmono
    exact ⟨by simpa using well_formed_agent_quota_of_phase_pos (Phase4Transition L K s' t').1 hspos,
      by simpa using well_formed_agent_quota_of_phase_pos (Phase4Transition L K s' t').2 htpos_out⟩
  | 5, _ =>
    rcases Phase5Transition_phase_nondec L K s' t' with ⟨hsmono, htmono⟩
    have htpos : 1 ≤ t'.phase.val :=
      phaseEpidemicUpdate_right_phase_pos_of_left_phase_pos_quota (L := L) (K := K)
        s t (by simpa [s', h_phase])
    have hspos0 : 1 ≤ s'.phase.val := by simpa [h_phase]
    have hspos : 1 ≤ (Phase5Transition L K s' t').1.phase.val := le_trans hspos0 hsmono
    have htpos_out : 1 ≤ (Phase5Transition L K s' t').2.phase.val := le_trans htpos htmono
    exact ⟨by simpa using well_formed_agent_quota_of_phase_pos (Phase5Transition L K s' t').1 hspos,
      by simpa using well_formed_agent_quota_of_phase_pos (Phase5Transition L K s' t').2 htpos_out⟩
  | 6, _ =>
    rcases Phase6Transition_phase_nondec L K s' t' with ⟨hsmono, htmono⟩
    have htpos : 1 ≤ t'.phase.val :=
      phaseEpidemicUpdate_right_phase_pos_of_left_phase_pos_quota (L := L) (K := K)
        s t (by simpa [s', h_phase])
    have hspos0 : 1 ≤ s'.phase.val := by simpa [h_phase]
    have hspos : 1 ≤ (Phase6Transition L K s' t').1.phase.val := le_trans hspos0 hsmono
    have htpos_out : 1 ≤ (Phase6Transition L K s' t').2.phase.val := le_trans htpos htmono
    exact ⟨by simpa using well_formed_agent_quota_of_phase_pos (Phase6Transition L K s' t').1 hspos,
      by simpa using well_formed_agent_quota_of_phase_pos (Phase6Transition L K s' t').2 htpos_out⟩
  | 7, _ =>
    rcases Phase7Transition_phase_nondec L K s' t' with ⟨hsmono, htmono⟩
    have htpos : 1 ≤ t'.phase.val :=
      phaseEpidemicUpdate_right_phase_pos_of_left_phase_pos_quota (L := L) (K := K)
        s t (by simpa [s', h_phase])
    have hspos0 : 1 ≤ s'.phase.val := by simpa [h_phase]
    have hspos : 1 ≤ (Phase7Transition L K s' t').1.phase.val := le_trans hspos0 hsmono
    have htpos_out : 1 ≤ (Phase7Transition L K s' t').2.phase.val := le_trans htpos htmono
    exact ⟨by simpa using well_formed_agent_quota_of_phase_pos (Phase7Transition L K s' t').1 hspos,
      by simpa using well_formed_agent_quota_of_phase_pos (Phase7Transition L K s' t').2 htpos_out⟩
  | 8, _ =>
    rcases Phase8Transition_phase_nondec L K s' t' with ⟨hsmono, htmono⟩
    have htpos : 1 ≤ t'.phase.val :=
      phaseEpidemicUpdate_right_phase_pos_of_left_phase_pos_quota (L := L) (K := K)
        s t (by simpa [s', h_phase])
    have hspos0 : 1 ≤ s'.phase.val := by simpa [h_phase]
    have hspos : 1 ≤ (Phase8Transition L K s' t').1.phase.val := le_trans hspos0 hsmono
    have htpos_out : 1 ≤ (Phase8Transition L K s' t').2.phase.val := le_trans htpos htmono
    exact ⟨by simpa using well_formed_agent_quota_of_phase_pos (Phase8Transition L K s' t').1 hspos,
      by simpa using well_formed_agent_quota_of_phase_pos (Phase8Transition L K s' t').2 htpos_out⟩
  | 9, _ =>
    rcases Phase9Transition_phase_nondec L K s' t' with ⟨hsmono, htmono⟩
    have htpos : 1 ≤ t'.phase.val :=
      phaseEpidemicUpdate_right_phase_pos_of_left_phase_pos_quota (L := L) (K := K)
        s t (by simpa [s', h_phase])
    have hspos0 : 1 ≤ s'.phase.val := by simpa [h_phase]
    have hspos : 1 ≤ (Phase9Transition L K s' t').1.phase.val := le_trans hspos0 hsmono
    have htpos_out : 1 ≤ (Phase9Transition L K s' t').2.phase.val := le_trans htpos htmono
    exact ⟨by simpa using well_formed_agent_quota_of_phase_pos (Phase9Transition L K s' t').1 hspos,
      by simpa using well_formed_agent_quota_of_phase_pos (Phase9Transition L K s' t').2 htpos_out⟩
  | 10, _ =>
    rcases Phase10Transition_phase_nondec L K s' t' with ⟨hsmono, htmono⟩
    have htpos : 1 ≤ t'.phase.val :=
      phaseEpidemicUpdate_right_phase_pos_of_left_phase_pos_quota (L := L) (K := K)
        s t (by simpa [s', h_phase])
    have hspos0 : 1 ≤ s'.phase.val := by simpa [h_phase]
    have hspos : 1 ≤ (Phase10Transition L K s' t').1.phase.val := le_trans hspos0 hsmono
    have htpos_out : 1 ≤ (Phase10Transition L K s' t').2.phase.val := le_trans htpos htmono
    exact ⟨by simpa using well_formed_agent_quota_of_phase_pos (Phase10Transition L K s' t').1 hspos,
      by simpa using well_formed_agent_quota_of_phase_pos (Phase10Transition L K s' t').2 htpos_out⟩
  | n + 11, hn => omega

private theorem validInitial_well_formed_agent_quota (c : Config (AgentState L K))
    (hvalid : validInitial c) :
    ∀ a ∈ c, well_formed_agent_quota a := by
  intro a ha hphase
  rcases hvalid a ha with ⟨_hphase0, hrole, _hassigned, hA, hB⟩
  constructor
  · intro _hmcr
    cases hinput : a.input
    · have hsmall : a.smallBias = ⟨4, by decide⟩ := hA hinput
      simp [AgentState.smallBiasInt, hsmall]
    · have hsmall : a.smallBias = ⟨2, by decide⟩ := hB hinput
      simp [AgentState.smallBiasInt, hsmall]
  · intro hmain _hunassigned
    rw [hrole] at hmain
    cases hmain

private theorem well_formed_agent_quota_preserved_by_step (c c' : Config (AgentState L K))
    (h_c : ∀ a ∈ c, well_formed_agent_quota a)
    (h_step : (NonuniformMajority L K).StepRel c c') :
    ∀ a ∈ c', well_formed_agent_quota a := by
  rcases h_step with ⟨r₁, r₂, happ, hc'⟩
  dsimp [Protocol.Applicable, NonuniformMajority] at happ hc'
  have hr₁_mem : r₁ ∈ c := Multiset.mem_of_le happ (by simp)
  have hr₂_mem : r₂ ∈ c := Multiset.mem_of_le happ (by simp)
  have htrans := Transition_preserves_well_formed_agent_quota (L := L) (K := K) r₁ r₂
    (h_c r₁ hr₁_mem) (h_c r₂ hr₂_mem)
  rw [hc']
  intro a ha
  simp only [Multiset.mem_add, Multiset.mem_cons, Multiset.mem_singleton] at ha
  rcases ha with h_old | h_new
  · exact h_c a (Multiset.mem_of_le (Multiset.sub_le_self c {r₁, r₂}) h_old)
  · rcases h_new with h_eq | h_eq
    · simpa [h_eq] using htrans.1
    · simpa [h_eq] using htrans.2

private theorem reachable_preserves_well_formed_agent_quota (init c : Config (AgentState L K))
    (h_init : validInitial init)
    (h_reach : Protocol.Reachable (NonuniformMajority L K) init c) :
    ∀ a ∈ c, well_formed_agent_quota a := by
  induction h_reach with
  | refl =>
      exact validInitial_well_formed_agent_quota init h_init
  | tail _ hstep ih =>
      exact well_formed_agent_quota_preserved_by_step (L := L) (K := K) _ _ ih hstep

private lemma smallBiasSum_stepRel_invariant_of_quota (c c' : Config (AgentState L K))
    (hquota : ∀ a ∈ c, well_formed_agent_quota a)
    (hstep : (NonuniformMajority L K).StepRel c c') :
    smallBiasSum c' = smallBiasSum c := by
  rcases hstep with ⟨r₁, r₂, happ, hc'⟩
  dsimp [Protocol.Applicable, NonuniformMajority] at happ hc'
  have hr₁_mem : r₁ ∈ c := Multiset.mem_of_le happ (by simp)
  have hr₂_mem : r₂ ∈ c := Multiset.mem_of_le happ (by simp)
  have hpair := smallBiasSum_step_invariant_of_quota (L := L) (K := K) r₁ r₂
    (hquota r₁ hr₁_mem) (hquota r₂ hr₂_mem)
  rw [hc']
  have hrestore : c - r₁ ::ₘ {r₂} + r₁ ::ₘ {r₂} = c := Multiset.sub_add_cancel happ
  have hsum_c :
      smallBiasSum c =
        smallBiasSum (c - r₁ ::ₘ {r₂}) +
          (AgentState.smallBiasInt r₁ + AgentState.smallBiasInt r₂) := by
    rw [← hrestore]
    simp [smallBiasSum, add_assoc, add_comm, add_left_comm]
  have hsum_c' :
      smallBiasSum
          (c - r₁ ::ₘ {r₂} +
          (Transition L K r₁ r₂).1 ::ₘ {(Transition L K r₁ r₂).2}) =
      smallBiasSum (c - r₁ ::ₘ {r₂}) +
        (AgentState.smallBiasInt (Transition L K r₁ r₂).1 +
          AgentState.smallBiasInt (Transition L K r₁ r₂).2) := by
    simp [smallBiasSum, add_assoc, add_comm, add_left_comm]
  rw [hsum_c', hsum_c, ← hpair]

private lemma StepRel_phase_le_of_next_phase_le (c c' : Config (AgentState L K))
    (hstep : (NonuniformMajority L K).StepRel c c')
    (hphase' : ∀ a ∈ c', a.phase.val ≤ 1) :
    ∀ a ∈ c, a.phase.val ≤ 1 := by
  rcases hstep with ⟨r₁, r₂, happ, hc'⟩
  dsimp [Protocol.Applicable, NonuniformMajority] at happ hc'
  have hmono := Transition_phase_monotone (L := L) (K := K) r₁ r₂
  have hp₁_mem : (Transition L K r₁ r₂).1 ∈ c' := by
    rw [hc']
    exact Multiset.mem_add.2 (Or.inr (Multiset.mem_cons_self _ _))
  have hp₂_mem : (Transition L K r₁ r₂).2 ∈ c' := by
    rw [hc']
    exact Multiset.mem_add.2 (Or.inr (Multiset.mem_cons_of_mem (by simp)))
  have hr₁_phase : r₁.phase.val ≤ 1 := le_trans hmono.1 (hphase' _ hp₁_mem)
  have hr₂_phase : r₂.phase.val ≤ 1 := le_trans hmono.2 (hphase' _ hp₂_mem)
  intro a ha
  by_cases ha₁ : a = r₁
  · simpa [ha₁] using hr₁_phase
  by_cases ha₂ : a = r₂
  · simpa [ha₂] using hr₂_phase
  have ha_residual : a ∈ c - r₁ ::ₘ {r₂} := by
    have h₁ : a ∈ c.erase r₁ := (Multiset.mem_erase_of_ne ha₁).2 ha
    have h₂ : a ∈ (c.erase r₁).erase r₂ := (Multiset.mem_erase_of_ne ha₂).2 h₁
    simpa using h₂
  have ha_c' : a ∈ c' := by
    rw [hc']
    simp only [Multiset.mem_add]
    exact Or.inl ha_residual
  exact hphase' a ha_c'

theorem reachable_smallBiasSum_invariant (init c : Config (AgentState L K))
    (hvalid : validInitial init) (hreach : (NonuniformMajority L K).Reachable init c)
    (hphase : ∀ a ∈ c, a.phase.val ≤ 1) :
    smallBiasSum c = smallBiasSum init := by
  induction hreach with
  | refl =>
      -- Base case: c = init. From validInitial, every agent has smallBias = ±1.
      -- Then smallBiasSum init = initialGap init by `smallBiasSum_initialGap`.
      have h_init_phase : ∀ a ∈ init, a.phase = ⟨0, by decide⟩ ∧
          ((a.input = .A → a.smallBias = ⟨4, by decide⟩) ∧
           (a.input = .B → a.smallBias = ⟨2, by decide⟩)) := by
        intro a ha
        rcases hvalid a ha with ⟨hph, _, _, hA, hB⟩
        exact ⟨hph, ⟨hA, hB⟩⟩
      have h_gap : smallBiasSum init = initialGap init :=
        smallBiasSum_initialGap init h_init_phase
      rfl
    | tail hprev hstep ih =>
        have hphase_prev :=
          StepRel_phase_le_of_next_phase_le (L := L) (K := K) _ _ hstep hphase
        have hsum_prev := ih hphase_prev
        have hquota_prev :=
          reachable_preserves_well_formed_agent_quota (L := L) (K := K) init _ hvalid hprev
        have hstep_sum :=
          smallBiasSum_stepRel_invariant_of_quota (L := L) (K := K) _ _ hquota_prev hstep
        exact hstep_sum.trans hsum_prev

/-- Strong invariant: an agent in role MCR or CR must be at phase 0
(initial population-splitting) or phase 10 (error track). Equivalently,
once an agent reaches phase ∈ [1, 9], its role is in {Main, Reserve, Clock}. -/
def role_phase_invariant_agent {L K : ℕ} (a : AgentState L K) : Prop :=
  (a.role = .mcr ∨ a.role = .cr) → a.phase.val = 0 ∨ a.phase.val = 10

/-! ### Well-formed agent states

The current `validInitial` predicate fixes the active Phase-0 fields, but it
does not constrain dormant record fields such as `bias` or `opinions`.  The
well-formedness layer therefore records the joint constraints that are
derivable from the present initialization predicate and preserved by the
implemented transition code.  Stronger dormant-field constraints can be added
after `validInitial` is strengthened to initialize those fields explicitly.
-/

def defaultSmallBias : Fin 7 := ⟨3, by decide⟩

/-- Local state well-formedness for the role/phase interface.

The transient roles `MCR` and `CR` are allowed only during Phase 0 and on the
Phase-10 backup/error track.  Additionally, every `CR` state has the zero
small-bias value used by Phase 0 when creating `CR` agents.
-/
def well_formed_agent {L K : ℕ} (a : AgentState L K) : Prop :=
  role_phase_invariant_agent a ∧
  (a.role = .cr → a.smallBias = defaultSmallBias)

theorem well_formed_agent.role_phase {a : AgentState L K} :
    well_formed_agent a → role_phase_invariant_agent a := by
  intro h; exact h.1

theorem well_formed_agent.cr_smallBias {a : AgentState L K} :
    well_formed_agent a → a.role = .cr → a.smallBias = defaultSmallBias := by
  intro h; exact h.2

theorem validInitial_well_formed_agent (c : Config (AgentState L K))
    (hvalid : validInitial c) :
    ∀ a ∈ c, well_formed_agent a := by
  intro a ha
  rcases hvalid a ha with ⟨hphase, hrole, _hassigned, _hA, _hB⟩
  constructor
  · intro htrans
    left
    have : a.phase = (⟨0, by decide⟩ : Fin 11) := hphase
    simp [this]
  · intro hcr
    rw [hrole] at hcr
    cases hcr

theorem well_formed_agent.not_mcr_of_intermediate_phase {a : AgentState L K}
    (ha : well_formed_agent a) (hlo : 1 ≤ a.phase.val) (hhi : a.phase.val ≤ 9) :
    a.role ≠ .mcr := by
  intro hmcr
  rcases ha.1 (Or.inl hmcr) with h0 | h10 <;> omega

theorem well_formed_agent.not_cr_of_intermediate_phase {a : AgentState L K}
    (ha : well_formed_agent a) (hlo : 1 ≤ a.phase.val) (hhi : a.phase.val ≤ 9) :
    a.role ≠ .cr := by
  intro hcr
  rcases ha.1 (Or.inr hcr) with h0 | h10 <;> omega

theorem well_formed_agent_of_not_transient (a : AgentState L K)
    (hmcr : a.role ≠ .mcr) (hcr : a.role ≠ .cr) :
    well_formed_agent a := by
  constructor
  · intro htrans
    rcases htrans with hm | hc
    · exact False.elim (hmcr hm)
    · exact False.elim (hcr hc)
  · intro hc
    exact False.elim (hcr hc)

theorem well_formed_agent_of_eq_role_phase_smallBias {a b : AgentState L K}
    (ha : well_formed_agent a)
    (hrole : b.role = a.role)
    (hphase : b.phase.val = a.phase.val)
    (hsmallBias : b.smallBias = a.smallBias) :
    well_formed_agent b := by
  constructor
  · intro htrans
    have htrans_a : a.role = .mcr ∨ a.role = .cr := by
      simpa [hrole] using htrans
    rcases ha.1 htrans_a with h0 | h10
    · left; omega
    · right; omega
  · intro hcr
    have hcr_a : a.role = .cr := by
      simpa [hrole] using hcr
    rw [hsmallBias, ha.2 hcr_a]

theorem advancePhase_preserves_well_formed_agent_of_phase_pos (a : AgentState L K)
    (hpos : 1 ≤ a.phase.val) :
    well_formed_agent a → well_formed_agent (advancePhase L K a) := by
  intro ha
  unfold advancePhase
  split_ifs with hlt
  · have hmcr : a.role ≠ .mcr := by
      intro hrole
      rcases ha.1 (Or.inl hrole) with hzero | hten <;> omega
    have hcr : a.role ≠ .cr := by
      intro hrole
      rcases ha.1 (Or.inr hrole) with hzero | hten <;> omega
    exact well_formed_agent_of_not_transient _ (by simp [hmcr]) (by simp [hcr])
  · exact ha

theorem stdCounterSubroutine_preserves_well_formed_agent_of_clock (a : AgentState L K)
    (hclock : a.role = .clock) :
    well_formed_agent (stdCounterSubroutine L K a) := by
  unfold stdCounterSubroutine advancePhase
  split_ifs <;>
    exact well_formed_agent_of_not_transient _ (by simp [hclock]) (by simp [hclock])

theorem well_formed_agent_set_cr_default_of_phase_zero_or_ten (a : AgentState L K)
    (hphase : a.phase.val = 0 ∨ a.phase.val = 10) :
    well_formed_agent ({ a with role := .cr, smallBias := defaultSmallBias }) := by
  constructor
  · intro _htrans
    simpa using hphase
  · intro _hcr
    simp [defaultSmallBias]

theorem phaseInit_preserves_well_formed_agent (p : Fin 11) (a : AgentState L K) :
    well_formed_agent a → well_formed_agent (phaseInit L K p a) := by
  intro ha
  fin_cases p
  · simpa [phaseInit] using ha
  ·
    unfold phaseInit
    simp [well_formed_agent, role_phase_invariant_agent, defaultSmallBias, phase10] at ha ⊢
    split_ifs <;> simp_all [phase10]
  ·
    unfold phaseInit
    simp [well_formed_agent, role_phase_invariant_agent, defaultSmallBias, phase10] at ha ⊢
    split_ifs <;> simp_all [phase10]
  ·
    unfold phaseInit
    simp [well_formed_agent, role_phase_invariant_agent, defaultSmallBias, phase10] at ha ⊢
    cases a.role <;> simp_all
  · simpa [phaseInit] using ha
  ·
    unfold phaseInit
    simp [well_formed_agent, role_phase_invariant_agent, defaultSmallBias, phase10] at ha ⊢
    split_ifs <;> simp_all
  ·
    unfold phaseInit
    simp [well_formed_agent, role_phase_invariant_agent, defaultSmallBias, phase10] at ha ⊢
    split_ifs <;> simp_all
  ·
    unfold phaseInit
    simp [well_formed_agent, role_phase_invariant_agent, defaultSmallBias, phase10] at ha ⊢
    split_ifs <;> simp_all
  · simpa [phaseInit, well_formed_agent, role_phase_invariant_agent, defaultSmallBias] using ha
  ·
    unfold phaseInit
    simp [well_formed_agent, role_phase_invariant_agent, defaultSmallBias, phase10] at ha ⊢
    split_ifs <;> simp_all [phase10]
  · simpa [phaseInit, well_formed_agent, role_phase_invariant_agent, defaultSmallBias] using ha

theorem runInitsBetween_preserves_well_formed_agent (oldP newP : ℕ) (a : AgentState L K) :
    well_formed_agent a → well_formed_agent (runInitsBetween L K oldP newP a) := by
  intro ha
  unfold runInitsBetween
  let lst := (List.range 11).filter (fun k => oldP < k ∧ k ≤ newP)
  have h_ind : ∀ (a' : AgentState L K), well_formed_agent a' →
      well_formed_agent
        (lst.foldl (fun (acc : AgentState L K) (k : ℕ) =>
          if h : k < 11 then phaseInit L K ⟨k, h⟩ acc else acc) a') := by
    induction lst with
    | nil =>
      intro a' ha'
      simpa
    | cons k l IH =>
      intro a' ha'
      simp [List.foldl]
      by_cases hk : k < 11
      · simp [hk]
        exact IH (phaseInit L K ⟨k, hk⟩ a')
          (phaseInit_preserves_well_formed_agent (L := L) (K := K) ⟨k, hk⟩ a' ha')
      · simp [hk]
        exact IH a' ha'
  exact h_ind a ha

private theorem runInitsBetween_zero_eq_phaseInit_one (p : Fin 11) (a : AgentState L K)
    (hpos : 1 ≤ p.val) :
    runInitsBetween L K 0 p.val a =
      runInitsBetween L K 1 p.val (phaseInit L K ⟨1, by decide⟩ a) := by
  fin_cases p
  · simp at hpos
  ·
    unfold runInitsBetween
    have h1 : (List.range 11).filter (fun k => 0 < k ∧ k ≤ 1) = [1] := by decide
    have h2 : (List.range 11).filter (fun k => 1 < k ∧ k ≤ 1) = [] := by decide
    rw [h1, h2]
    simp
  ·
    unfold runInitsBetween
    have h1 : (List.range 11).filter (fun k => 0 < k ∧ k ≤ 2) = [1, 2] := by decide
    have h2 : (List.range 11).filter (fun k => 1 < k ∧ k ≤ 2) = [2] := by decide
    rw [h1, h2]
    simp
  ·
    unfold runInitsBetween
    have h1 : (List.range 11).filter (fun k => 0 < k ∧ k ≤ 3) = [1, 2, 3] := by decide
    have h2 : (List.range 11).filter (fun k => 1 < k ∧ k ≤ 3) = [2, 3] := by decide
    rw [h1, h2]
    simp
  ·
    unfold runInitsBetween
    have h1 : (List.range 11).filter (fun k => 0 < k ∧ k ≤ 4) = [1, 2, 3, 4] := by decide
    have h2 : (List.range 11).filter (fun k => 1 < k ∧ k ≤ 4) = [2, 3, 4] := by decide
    rw [h1, h2]
    simp
  ·
    unfold runInitsBetween
    have h1 : (List.range 11).filter (fun k => 0 < k ∧ k ≤ 5) = [1, 2, 3, 4, 5] := by decide
    have h2 : (List.range 11).filter (fun k => 1 < k ∧ k ≤ 5) = [2, 3, 4, 5] := by decide
    rw [h1, h2]
    simp
  ·
    unfold runInitsBetween
    have h1 : (List.range 11).filter (fun k => 0 < k ∧ k ≤ 6) = [1, 2, 3, 4, 5, 6] := by decide
    have h2 : (List.range 11).filter (fun k => 1 < k ∧ k ≤ 6) = [2, 3, 4, 5, 6] := by decide
    rw [h1, h2]
    simp
  ·
    unfold runInitsBetween
    have h1 : (List.range 11).filter (fun k => 0 < k ∧ k ≤ 7) = [1, 2, 3, 4, 5, 6, 7] := by decide
    have h2 : (List.range 11).filter (fun k => 1 < k ∧ k ≤ 7) = [2, 3, 4, 5, 6, 7] := by decide
    rw [h1, h2]
    simp
  ·
    unfold runInitsBetween
    have h1 : (List.range 11).filter (fun k => 0 < k ∧ k ≤ 8) = [1, 2, 3, 4, 5, 6, 7, 8] := by decide
    have h2 : (List.range 11).filter (fun k => 1 < k ∧ k ≤ 8) = [2, 3, 4, 5, 6, 7, 8] := by decide
    rw [h1, h2]
    simp
  ·
    unfold runInitsBetween
    have h1 : (List.range 11).filter (fun k => 0 < k ∧ k ≤ 9) = [1, 2, 3, 4, 5, 6, 7, 8, 9] := by decide
    have h2 : (List.range 11).filter (fun k => 1 < k ∧ k ≤ 9) = [2, 3, 4, 5, 6, 7, 8, 9] := by decide
    rw [h1, h2]
    simp
  ·
    unfold runInitsBetween
    have h1 : (List.range 11).filter (fun k => 0 < k ∧ k ≤ 10) = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] := by decide
    have h2 : (List.range 11).filter (fun k => 1 < k ∧ k ≤ 10) = [2, 3, 4, 5, 6, 7, 8, 9, 10] := by decide
    rw [h1, h2]
    simp

private theorem phaseInit_one_after_phase_update_transient_well_formed (p : Fin 11)
    (a : AgentState L K)
    (htrans : a.role = .mcr ∨ a.role = .cr) :
    well_formed_agent (phaseInit L K ⟨1, by decide⟩ ({ a with phase := p })) := by
  unfold phaseInit
  simp [well_formed_agent, role_phase_invariant_agent, defaultSmallBias, phase10]
  rcases htrans with hmcr | hcr
  · simp [hmcr, phase10]
  · simp [hcr, phase10]

private theorem phaseEpidemicUpdate_one_preserves_well_formed_agent (p : Fin 11)
    (a : AgentState L K) (hle : a.phase.val ≤ p.val) :
    well_formed_agent a →
    well_formed_agent (runInitsBetween L K a.phase.val p.val ({ a with phase := p })) := by
  intro ha
  by_cases hmcr : a.role = .mcr
  · rcases ha.1 (Or.inl hmcr) with hzero | hten
    · have hold : a.phase.val = 0 := hzero
      by_cases hpzero : p.val = 0
      · have hbase : well_formed_agent ({ a with phase := p }) :=
          well_formed_agent_of_eq_role_phase_smallBias ha (by simp) (by simp [hold, hpzero])
            (by simp)
        simpa [hold, hpzero] using
          runInitsBetween_preserves_well_formed_agent (L := L) (K := K) 0 0
            ({ a with phase := p }) hbase
      · have hpos : 1 ≤ p.val := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hpzero)
        rw [hold, runInitsBetween_zero_eq_phaseInit_one (L := L) (K := K) p
          ({ a with phase := p }) hpos]
        exact runInitsBetween_preserves_well_formed_agent (L := L) (K := K) 1 p.val
          (phaseInit L K ⟨1, by decide⟩ ({ a with phase := p }))
          (phaseInit_one_after_phase_update_transient_well_formed (L := L) (K := K)
            p a (Or.inl hmcr))
    · have hp : p.val = 10 := by
        have hp_le : p.val ≤ 10 := by omega
        omega
      have hbase : well_formed_agent ({ a with phase := p }) :=
        well_formed_agent_of_eq_role_phase_smallBias ha (by simp) (by simp [hten, hp]) (by simp)
      simpa [hten, hp] using
        runInitsBetween_preserves_well_formed_agent (L := L) (K := K) 10 10
          ({ a with phase := p }) hbase
  · by_cases hcr : a.role = .cr
    · rcases ha.1 (Or.inr hcr) with hzero | hten
      · have hold : a.phase.val = 0 := hzero
        by_cases hpzero : p.val = 0
        · have hbase : well_formed_agent ({ a with phase := p }) :=
            well_formed_agent_of_eq_role_phase_smallBias ha (by simp) (by simp [hold, hpzero])
              (by simp)
          simpa [hold, hpzero] using
            runInitsBetween_preserves_well_formed_agent (L := L) (K := K) 0 0
              ({ a with phase := p }) hbase
        · have hpos : 1 ≤ p.val := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hpzero)
          rw [hold, runInitsBetween_zero_eq_phaseInit_one (L := L) (K := K) p
            ({ a with phase := p }) hpos]
          exact runInitsBetween_preserves_well_formed_agent (L := L) (K := K) 1 p.val
            (phaseInit L K ⟨1, by decide⟩ ({ a with phase := p }))
            (phaseInit_one_after_phase_update_transient_well_formed (L := L) (K := K)
              p a (Or.inr hcr))
      · have hp : p.val = 10 := by
          have hp_le : p.val ≤ 10 := by omega
          omega
        have hbase : well_formed_agent ({ a with phase := p }) :=
          well_formed_agent_of_eq_role_phase_smallBias ha (by simp) (by simp [hten, hp]) (by simp)
        simpa [hten, hp] using
          runInitsBetween_preserves_well_formed_agent (L := L) (K := K) 10 10
            ({ a with phase := p }) hbase
    · have hbase : well_formed_agent ({ a with phase := p }) :=
        well_formed_agent_of_not_transient _ (by simp [hmcr]) (by simp [hcr])
      exact runInitsBetween_preserves_well_formed_agent (L := L) (K := K)
        a.phase.val p.val ({ a with phase := p }) hbase

theorem phaseEpidemicUpdate_preserves_well_formed_agent (s t : AgentState L K) :
    well_formed_agent s → well_formed_agent t →
    well_formed_agent (phaseEpidemicUpdate L K s t).1 ∧
    well_formed_agent (phaseEpidemicUpdate L K s t).2 := by
  intro hs ht
  unfold phaseEpidemicUpdate
  set p := max s.phase t.phase with hp
  have hle_s : s.phase.val ≤ p.val := by
    rw [hp]
    exact Nat.le_max_left _ _
  have hle_t : t.phase.val ≤ p.val := by
    rw [hp]
    exact Nat.le_max_right _ _
  exact ⟨phaseEpidemicUpdate_one_preserves_well_formed_agent (L := L) (K := K)
      p s hle_s hs,
    phaseEpidemicUpdate_one_preserves_well_formed_agent (L := L) (K := K)
      p t hle_t ht⟩

private theorem phaseEpidemicUpdate_right_phase_pos_of_left_phase_pos
    (s t : AgentState L K)
    (hleft : 1 ≤ (phaseEpidemicUpdate L K s t).1.phase.val) :
    1 ≤ (phaseEpidemicUpdate L K s t).2.phase.val := by
  unfold phaseEpidemicUpdate at hleft ⊢
  set p := max s.phase t.phase with hp
  by_cases hpzero : p.val = 0
  · have hs0 : s.phase.val = 0 := by
      have hle : s.phase.val ≤ p.val := by
        rw [hp]
        exact Nat.le_max_left _ _
      omega
    have hfirst : (runInitsBetween L K s.phase.val p.val ({ s with phase := p })).phase.val = 0 := by
      unfold runInitsBetween
      have hfilter :
          (List.range 11).filter (fun k => s.phase.val < k ∧ k ≤ p.val) = [] := by
        rw [hs0, hpzero]
        decide
      rw [hfilter]
      simp [hpzero]
    have hbad : 1 ≤ 0 := by
      simpa [hfirst] using hleft
    omega
  · have hp_pos : 1 ≤ p.val := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hpzero)
    have hp_le_right :
        p.val ≤ (runInitsBetween L K t.phase.val p.val ({ t with phase := p })).phase.val := by
      calc
        p.val = ({ t with phase := p } : AgentState L K).phase.val := by simp
        _ ≤ (runInitsBetween L K t.phase.val p.val ({ t with phase := p })).phase.val :=
          runInitsBetween_phase_nondec (L := L) (K := K) t.phase.val p.val
            ({ t with phase := p })
    exact le_trans hp_pos hp_le_right

/-! ### Per-phase preservation of `well_formed_agent` -/

theorem phase3CancelSplit_preserves_well_formed_agent (s t : AgentState L K) :
    well_formed_agent s → well_formed_agent t →
    well_formed_agent (phase3CancelSplit L K s t).1 ∧
    well_formed_agent (phase3CancelSplit L K s t).2 := by
  intro hs ht
  unfold phase3CancelSplit
  match s.bias, t.bias with
  | .zero, .zero => simp [hs, ht]
  | .zero, .dyadic _ _ =>
      simp
      split_ifs
      all_goals
        constructor
        · exact well_formed_agent_of_eq_role_phase_smallBias hs (by simp) (by simp) (by simp)
        · exact well_formed_agent_of_eq_role_phase_smallBias ht (by simp) (by simp) (by simp)
  | .dyadic _ _, .zero =>
      simp
      split_ifs
      all_goals
        constructor
        · exact well_formed_agent_of_eq_role_phase_smallBias hs (by simp) (by simp) (by simp)
        · exact well_formed_agent_of_eq_role_phase_smallBias ht (by simp) (by simp) (by simp)
  | .dyadic .pos _, .dyadic .pos _ => simp [hs, ht]
  | .dyadic .pos _, .dyadic .neg _ =>
      simp
      split_ifs
      all_goals
        constructor
        · exact well_formed_agent_of_eq_role_phase_smallBias hs (by simp) (by simp) (by simp)
        · exact well_formed_agent_of_eq_role_phase_smallBias ht (by simp) (by simp) (by simp)
  | .dyadic .neg _, .dyadic .pos _ =>
      simp
      split_ifs
      all_goals
        constructor
        · exact well_formed_agent_of_eq_role_phase_smallBias hs (by simp) (by simp) (by simp)
        · exact well_formed_agent_of_eq_role_phase_smallBias ht (by simp) (by simp) (by simp)
  | .dyadic .neg _, .dyadic .neg _ => simp [hs, ht]

theorem cancelSplit_preserves_well_formed_agent (s t : AgentState L K) :
    well_formed_agent s → well_formed_agent t →
    well_formed_agent (cancelSplit L K s t).1 ∧
    well_formed_agent (cancelSplit L K s t).2 := by
  intro hs ht
  unfold cancelSplit
  match s.bias, t.bias with
  | .zero, _ => simp [hs, ht]
  | .dyadic _ _, .zero => simp [hs, ht]
  | .dyadic _ _, .dyadic _ _ =>
      simp
      split_ifs
      all_goals
        constructor
        · exact well_formed_agent_of_eq_role_phase_smallBias hs (by simp) (by simp) (by simp)
        · exact well_formed_agent_of_eq_role_phase_smallBias ht (by simp) (by simp) (by simp)

theorem absorbConsume_preserves_well_formed_agent (s t : AgentState L K) :
    well_formed_agent s → well_formed_agent t →
    well_formed_agent (absorbConsume L K s t).1 ∧
    well_formed_agent (absorbConsume L K s t).2 := by
  intro hs ht
  unfold absorbConsume
  match s.bias, t.bias with
  | .zero, _ => simp [hs, ht]
  | .dyadic .pos _, .zero => simp [hs, ht]
  | .dyadic .neg _, .zero => simp [hs, ht]
  | .dyadic .pos _, .dyadic .pos _ => simp [hs, ht]
  | .dyadic .neg _, .dyadic .neg _ => simp [hs, ht]
  | .dyadic .pos _, .dyadic .neg _ =>
      simp
      split_ifs
      all_goals
        constructor
        · exact well_formed_agent_of_eq_role_phase_smallBias hs (by simp) (by simp) (by simp)
        · exact well_formed_agent_of_eq_role_phase_smallBias ht (by simp) (by simp) (by simp)
  | .dyadic .neg _, .dyadic .pos _ =>
      simp
      split_ifs
      all_goals
        constructor
        · exact well_formed_agent_of_eq_role_phase_smallBias hs (by simp) (by simp) (by simp)
        · exact well_formed_agent_of_eq_role_phase_smallBias ht (by simp) (by simp) (by simp)

theorem Phase0Transition_preserves_well_formed_agent (s t : AgentState L K) :
    well_formed_agent s → well_formed_agent t →
    well_formed_agent (Phase0Transition L K s t).1 ∧
    well_formed_agent (Phase0Transition L K s t).2 := by
  intro hs ht
  unfold Phase0Transition
  let s1 := if s.role = .mcr ∧ t.role = .mcr then
              { s with role := .main, smallBias := addSmallBias s.smallBias t.smallBias }
            else s
  let t1 := if s.role = .mcr ∧ t.role = .mcr then
              { t with role := .cr, smallBias := ⟨3, by decide⟩ }
            else t
  let s2 := if s1.role = .mcr ∧ t1.role = .main ∧ ¬ t1.assigned then
              { s1 with role := .cr, smallBias := ⟨3, by decide⟩ }
            else if t1.role = .mcr ∧ s1.role = .main ∧ ¬ s1.assigned then
              { s1 with assigned := true, smallBias := addSmallBias t1.smallBias s1.smallBias }
            else s1
  let t2 := if s1.role = .mcr ∧ t1.role = .main ∧ ¬ t1.assigned then
              { t1 with assigned := true, smallBias := addSmallBias s1.smallBias t1.smallBias }
            else if t1.role = .mcr ∧ s1.role = .main ∧ ¬ s1.assigned then
              { t1 with role := .cr, smallBias := ⟨3, by decide⟩ }
            else t1
  let s3 := if s2.role = .mcr ∧ t2.role ≠ .main ∧ t2.role ≠ .mcr ∧ ¬ t2.assigned then s2
            else if t2.role = .mcr ∧ s2.role ≠ .main ∧ s2.role ≠ .mcr ∧ ¬ s2.assigned then
              { s2 with assigned := true }
            else s2
  let t3 := if s2.role = .mcr ∧ t2.role ≠ .main ∧ t2.role ≠ .mcr ∧ ¬ t2.assigned then
              { t2 with assigned := true }
            else if t2.role = .mcr ∧ s2.role ≠ .main ∧ s2.role ≠ .mcr ∧ ¬ s2.assigned then t2
            else t2
  let s3' := if s3.role = .mcr ∧ t3.role = .cr then
               { s3 with role := .main, assigned := true }
             else if t3.role = .mcr ∧ s3.role = .cr then s3
             else s3
  let t3' := if s3.role = .mcr ∧ t3.role = .cr then t3
             else if t3.role = .mcr ∧ s3.role = .cr then
               { t3 with role := .main, assigned := true }
             else t3
  let s4 := if s3'.role = .cr ∧ t3'.role = .cr then
              { s3' with role := .clock, counter := ⟨50 * (L + 1), by omega⟩ }
            else s3'
  let t4 := if s3'.role = .cr ∧ t3'.role = .cr then
              { t3' with role := .reserve }
            else t3'
  let s5 := if s4.role = .clock ∧ t4.role = .clock then
              stdCounterSubroutine L K s4
            else s4
  let t5 := if s4.role = .clock ∧ t4.role = .clock then
              stdCounterSubroutine L K t4
            else t4
  have hs1 : well_formed_agent s1 := by
    dsimp [s1]
    split_ifs with h
    · exact well_formed_agent_of_not_transient _ (by simp) (by simp)
    · exact hs
  have ht1 : well_formed_agent t1 := by
    dsimp [t1]
    split_ifs with h
    · exact well_formed_agent_set_cr_default_of_phase_zero_or_ten _
        (ht.1 (Or.inl h.2))
    · exact ht
  have hs2 : well_formed_agent s2 := by
    dsimp [s2]
    split_ifs with hleft hright
    · exact well_formed_agent_set_cr_default_of_phase_zero_or_ten _
        (hs1.1 (Or.inl hleft.1))
    · exact well_formed_agent_of_not_transient _ (by simp [hright.2.1]) (by simp [hright.2.1])
    · exact hs1
  have ht2 : well_formed_agent t2 := by
    dsimp [t2]
    split_ifs with hleft hright
    · exact well_formed_agent_of_not_transient _ (by simp [hleft.2.1]) (by simp [hleft.2.1])
    · exact well_formed_agent_set_cr_default_of_phase_zero_or_ten _
        (ht1.1 (Or.inl hright.1))
    · exact ht1
  have hs3 : well_formed_agent s3 := by
    dsimp [s3]
    split_ifs
    · exact hs2
    · exact well_formed_agent_of_eq_role_phase_smallBias hs2 (by simp) (by simp) (by simp)
    · exact hs2
  have ht3 : well_formed_agent t3 := by
    dsimp [t3]
    split_ifs
    · exact well_formed_agent_of_eq_role_phase_smallBias ht2 (by simp) (by simp) (by simp)
    · exact ht2
    · exact ht2
  have hs3' : well_formed_agent s3' := by
    dsimp [s3']
    split_ifs with hleft hright
    · exact well_formed_agent_of_not_transient _ (by simp) (by simp)
    · exact hs3
    · exact hs3
  have ht3' : well_formed_agent t3' := by
    dsimp [t3']
    split_ifs with hleft hright
    · exact ht3
    · exact well_formed_agent_of_not_transient _ (by simp) (by simp)
    · exact ht3
  have hs4 : well_formed_agent s4 := by
    dsimp [s4]
    split_ifs
    · exact well_formed_agent_of_not_transient _ (by simp) (by simp)
    · exact hs3'
  have ht4 : well_formed_agent t4 := by
    dsimp [t4]
    split_ifs
    · exact well_formed_agent_of_not_transient _ (by simp) (by simp)
    · exact ht3'
  have hs5 : well_formed_agent s5 := by
    dsimp [s5]
    split_ifs with hclock
    · exact stdCounterSubroutine_preserves_well_formed_agent_of_clock _ hclock.1
    · exact hs4
  have ht5 : well_formed_agent t5 := by
    dsimp [t5]
    split_ifs with hclock
    · exact stdCounterSubroutine_preserves_well_formed_agent_of_clock _ hclock.2
    · exact ht4
  exact ⟨hs5, ht5⟩

theorem Phase1Transition_preserves_well_formed_agent (s t : AgentState L K) :
    well_formed_agent s → well_formed_agent t →
    well_formed_agent (Phase1Transition L K s t).1 ∧
    well_formed_agent (Phase1Transition L K s t).2 := by
  intro hs ht
  constructor
  · unfold Phase1Transition
    split_ifs with hmain
    · exact well_formed_agent_of_not_transient _ (by simp [hmain.1]) (by simp [hmain.1])
    · exact hs
  · unfold Phase1Transition
    split_ifs with hmain
    · exact well_formed_agent_of_not_transient _ (by simp [hmain.2]) (by simp [hmain.2])
    · exact ht

theorem Phase2Transition_preserves_well_formed_agent_of_phase_pos (s t : AgentState L K)
    (hs_pos : 1 ≤ s.phase.val) (ht_pos : 1 ≤ t.phase.val) :
    well_formed_agent s → well_formed_agent t →
    well_formed_agent (Phase2Transition L K s t).1 ∧
    well_formed_agent (Phase2Transition L K s t).2 := by
  intro hs ht
  unfold Phase2Transition
  let univ := opinionsUnion s.opinions t.opinions
  let s' := { s with opinions := univ }
  let t' := { t with opinions := univ }
  have hs' : well_formed_agent s' :=
    well_formed_agent_of_eq_role_phase_smallBias hs (by simp [s']) (by simp [s']) (by simp [s'])
  have ht' : well_formed_agent t' :=
    well_formed_agent_of_eq_role_phase_smallBias ht (by simp [t']) (by simp [t']) (by simp [t'])
  have hs'_pos : 1 ≤ s'.phase.val := by simp [s', hs_pos]
  have ht'_pos : 1 ≤ t'.phase.val := by simp [t', ht_pos]
  change well_formed_agent
      (if hasMinusOne univ && hasPlusOne univ then
        (advancePhase L K s', advancePhase L K t')
      else if hasPlusOne univ then
        ({ s' with output := .A }, { t' with output := .A })
      else if hasMinusOne univ then
        ({ s' with output := .B }, { t' with output := .B })
      else if univ.val = 2 then
        ({ s' with output := .T }, { t' with output := .T })
      else
        (s', t')).1 ∧
    well_formed_agent
      (if hasMinusOne univ && hasPlusOne univ then
        (advancePhase L K s', advancePhase L K t')
      else if hasPlusOne univ then
        ({ s' with output := .A }, { t' with output := .A })
      else if hasMinusOne univ then
        ({ s' with output := .B }, { t' with output := .B })
      else if univ.val = 2 then
        ({ s' with output := .T }, { t' with output := .T })
      else
        (s', t')).2
  by_cases hboth : hasMinusOne univ && hasPlusOne univ
  · simp [hboth, advancePhase_preserves_well_formed_agent_of_phase_pos, hs', ht',
      hs'_pos, ht'_pos]
  · by_cases hplus : hasPlusOne univ
    · constructor
      · have hminus_false : hasMinusOne univ = false := by
          cases hm : hasMinusOne univ <;> simp [hm, hplus] at hboth ⊢
        simp [hplus, hminus_false]
        exact well_formed_agent_of_eq_role_phase_smallBias hs' (by rfl) (by rfl) (by rfl)
      · have hminus_false : hasMinusOne univ = false := by
          cases hm : hasMinusOne univ <;> simp [hm, hplus] at hboth ⊢
        simp [hplus, hminus_false]
        exact well_formed_agent_of_eq_role_phase_smallBias ht' (by rfl) (by rfl) (by rfl)
    · by_cases hminus : hasMinusOne univ
      · constructor
        · simp [hboth, hplus, hminus]
          exact well_formed_agent_of_eq_role_phase_smallBias hs' (by rfl) (by rfl) (by rfl)
        · simp [hboth, hplus, hminus]
          exact well_formed_agent_of_eq_role_phase_smallBias ht' (by rfl) (by rfl) (by rfl)
      · by_cases htwo : univ.val = 2
        · constructor
          · simp [hboth, hplus, hminus, htwo]
            exact well_formed_agent_of_eq_role_phase_smallBias hs' (by rfl) (by rfl) (by rfl)
          · simp [hboth, hplus, hminus, htwo]
            exact well_formed_agent_of_eq_role_phase_smallBias ht' (by rfl) (by rfl) (by rfl)
        · simp [hboth, hplus, hminus, htwo, hs', ht']

theorem Phase2Transition_preserves_well_formed_agent (s t : AgentState L K)
    (hs_phase : s.phase.val = 2) (ht_phase : t.phase.val = 2) :
    well_formed_agent s → well_formed_agent t →
    well_formed_agent (Phase2Transition L K s t).1 ∧
    well_formed_agent (Phase2Transition L K s t).2 := by
  exact Phase2Transition_preserves_well_formed_agent_of_phase_pos (L := L) (K := K)
    s t (by omega) (by omega)

theorem Phase3Transition_preserves_well_formed_agent (s t : AgentState L K) :
    well_formed_agent s → well_formed_agent t →
    well_formed_agent (Phase3Transition L K s t).1 ∧
    well_formed_agent (Phase3Transition L K s t).2 := by
  intro hs ht
  unfold Phase3Transition
  let s1 := if s.role = .clock ∧ t.role = .clock then
    if s.minute ≠ t.minute then
      let pmax := max s.minute t.minute
      { s with minute := pmax }
    else if h_max : s.minute.val < K * (L + 1) then
      { s with minute := ⟨s.minute.val + 1, by omega⟩ }
    else
      stdCounterSubroutine L K s
  else s
  let t1 := if s.role = .clock ∧ t.role = .clock then
    if s.minute ≠ t.minute then
      let pmax := max s.minute t.minute
      { t with minute := pmax }
    else if h_max : s.minute.val < K * (L + 1) then
      t
    else
      stdCounterSubroutine L K t
  else t
  let s2 := if s1.role = .main ∧ s1.bias = .zero ∧ t1.role = .clock then
    let hVal := min L (t1.minute.val / K)
    have h_hour_lt : hVal < L + 1 := by
      apply Nat.lt_succ_of_le; exact Nat.min_le_left _ _
    { s1 with hour := ⟨hVal, h_hour_lt⟩ }
  else if t1.role = .main ∧ t1.bias = .zero ∧ s1.role = .clock then
    s1
  else s1
  let t2 := if s1.role = .main ∧ s1.bias = .zero ∧ t1.role = .clock then
    t1
  else if t1.role = .main ∧ t1.bias = .zero ∧ s1.role = .clock then
    let hVal := min L (s1.minute.val / K)
    have h_hour_lt : hVal < L + 1 := by
      apply Nat.lt_succ_of_le; exact Nat.min_le_left _ _
    { t1 with hour := ⟨hVal, h_hour_lt⟩ }
  else t1
  have hs1 : well_formed_agent s1 := by
    dsimp [s1]
    by_cases hclock : s.role = .clock ∧ t.role = .clock
    · by_cases hneq : s.minute ≠ t.minute
      · simp [hclock, hneq]
        exact well_formed_agent_of_eq_role_phase_smallBias hs (by exact hclock.1.symm)
          (by simp) (by simp)
      · by_cases hmax : s.minute.val < K * (L + 1)
        · simp [hclock, hneq, hmax]
          exact well_formed_agent_of_eq_role_phase_smallBias hs (by exact hclock.1.symm)
            (by simp) (by simp)
        · simp [hclock, hneq, hmax]
          exact stdCounterSubroutine_preserves_well_formed_agent_of_clock _ hclock.1
    · simp [hclock, hs]
  have ht1 : well_formed_agent t1 := by
    dsimp [t1]
    by_cases hclock : s.role = .clock ∧ t.role = .clock
    · by_cases hneq : s.minute ≠ t.minute
      · simp [hclock, hneq]
        exact well_formed_agent_of_eq_role_phase_smallBias ht (by exact hclock.2.symm)
          (by simp) (by simp)
      · by_cases hmax : s.minute.val < K * (L + 1)
        · simp [hclock, hneq, hmax, ht]
        · simp [hclock, hneq, hmax]
          exact stdCounterSubroutine_preserves_well_formed_agent_of_clock _ hclock.2
    · simp [hclock, ht]
  have hs2 : well_formed_agent s2 := by
    dsimp [s2]
    by_cases hleft : s1.role = .main ∧ s1.bias = .zero ∧ t1.role = .clock
    · simp [hleft]
      exact well_formed_agent_of_eq_role_phase_smallBias hs1 (by exact hleft.1.symm)
        (by simp) (by simp)
    · by_cases hright : t1.role = .main ∧ t1.bias = .zero ∧ s1.role = .clock
      · simp [hleft, hright, hs1]
      · simp [hleft, hright, hs1]
  have ht2 : well_formed_agent t2 := by
    dsimp [t2]
    by_cases hleft : s1.role = .main ∧ s1.bias = .zero ∧ t1.role = .clock
    · simp [hleft, ht1]
    · by_cases hright : t1.role = .main ∧ t1.bias = .zero ∧ s1.role = .clock
      · simp [hleft, hright]
        exact well_formed_agent_of_eq_role_phase_smallBias ht1 (by exact hright.1.symm)
          (by simp) (by simp)
      · simp [hleft, hright, ht1]
  change well_formed_agent
      (if s2.role = .main ∧ t2.role = .main then phase3CancelSplit L K s2 t2 else (s2, t2)).1 ∧
    well_formed_agent
      (if s2.role = .main ∧ t2.role = .main then phase3CancelSplit L K s2 t2 else (s2, t2)).2
  by_cases hmain : s2.role = .main ∧ t2.role = .main
  · simp [hmain, phase3CancelSplit_preserves_well_formed_agent, hs2, ht2]
  · simp [hmain, hs2, ht2]

theorem Phase4Transition_preserves_well_formed_agent_of_phase_pos (s t : AgentState L K)
    (hs_pos : 1 ≤ s.phase.val) (ht_pos : 1 ≤ t.phase.val) :
    well_formed_agent s → well_formed_agent t →
    well_formed_agent (Phase4Transition L K s t).1 ∧
    well_formed_agent (Phase4Transition L K s t).2 := by
  intro hs ht
  unfold Phase4Transition
  dsimp
  split_ifs
  · exact ⟨advancePhase_preserves_well_formed_agent_of_phase_pos (L := L) (K := K)
      s hs_pos hs,
      advancePhase_preserves_well_formed_agent_of_phase_pos (L := L) (K := K)
      t ht_pos ht⟩
  · exact ⟨hs, ht⟩

theorem Phase4Transition_preserves_well_formed_agent (s t : AgentState L K)
    (hs_phase : s.phase.val = 4) (ht_phase : t.phase.val = 4) :
    well_formed_agent s → well_formed_agent t →
    well_formed_agent (Phase4Transition L K s t).1 ∧
    well_formed_agent (Phase4Transition L K s t).2 := by
  exact Phase4Transition_preserves_well_formed_agent_of_phase_pos (L := L) (K := K)
    s t (by omega) (by omega)

theorem Phase5Transition_preserves_well_formed_agent (s t : AgentState L K) :
    well_formed_agent s → well_formed_agent t →
    well_formed_agent (Phase5Transition L K s t).1 ∧
    well_formed_agent (Phase5Transition L K s t).2 := by
  intro hs ht
  unfold Phase5Transition
  dsimp
  constructor <;>
    split_ifs <;>
    simp_all [well_formed_agent, role_phase_invariant_agent, defaultSmallBias,
      stdCounterSubroutine, advancePhase] <;>
    split_ifs <;> simp_all [defaultSmallBias]

theorem Phase6Transition_preserves_well_formed_agent (s t : AgentState L K) :
    well_formed_agent s → well_formed_agent t →
    well_formed_agent (Phase6Transition L K s t).1 ∧
    well_formed_agent (Phase6Transition L K s t).2 := by
  intro hs ht
  unfold Phase6Transition doSplit
  dsimp
  constructor <;>
    cases s.bias <;> cases t.bias <;>
    split_ifs <;>
    simp_all [well_formed_agent, role_phase_invariant_agent, defaultSmallBias,
      stdCounterSubroutine, advancePhase] <;>
    split_ifs <;> simp_all [defaultSmallBias]

theorem Phase7Transition_preserves_well_formed_agent (s t : AgentState L K) :
    well_formed_agent s → well_formed_agent t →
    well_formed_agent (Phase7Transition L K s t).1 ∧
    well_formed_agent (Phase7Transition L K s t).2 := by
  intro hs ht
  unfold Phase7Transition
  dsimp
  by_cases hmain : s.role = .main ∧ t.role = .main
  · rcases cancelSplit_preserves_well_formed_agent (L := L) (K := K) s t hs ht with ⟨hcs, hct⟩
    by_cases hsclock : (cancelSplit L K s t).1.role = .clock
    · by_cases htclock : (cancelSplit L K s t).2.role = .clock
      · simp [hmain, hsclock, htclock,
          stdCounterSubroutine_preserves_well_formed_agent_of_clock]
      · simp [hmain, hsclock, htclock,
          stdCounterSubroutine_preserves_well_formed_agent_of_clock, hct]
    · by_cases htclock : (cancelSplit L K s t).2.role = .clock
      · simp [hmain, hsclock, htclock,
          stdCounterSubroutine_preserves_well_formed_agent_of_clock, hcs]
      · simp [hmain, hsclock, htclock, hcs, hct]
  · by_cases hsclock : s.role = .clock
    · by_cases htclock : t.role = .clock
      · simp [hmain, hsclock, htclock,
          stdCounterSubroutine_preserves_well_formed_agent_of_clock]
      · simp [hmain, hsclock, htclock,
          stdCounterSubroutine_preserves_well_formed_agent_of_clock, ht]
    · by_cases htclock : t.role = .clock
      · simp [hmain, hsclock, htclock,
          stdCounterSubroutine_preserves_well_formed_agent_of_clock, hs]
      · simp [hmain, hsclock, htclock, hs, ht]

theorem Phase8Transition_preserves_well_formed_agent (s t : AgentState L K) :
    well_formed_agent s → well_formed_agent t →
    well_formed_agent (Phase8Transition L K s t).1 ∧
    well_formed_agent (Phase8Transition L K s t).2 := by
  intro hs ht
  unfold Phase8Transition
  dsimp
  by_cases hmain : s.role = .main ∧ t.role = .main
  · rcases absorbConsume_preserves_well_formed_agent (L := L) (K := K) s t hs ht with ⟨has, hat⟩
    by_cases hsclock : (absorbConsume L K s t).1.role = .clock
    · by_cases htclock : (absorbConsume L K s t).2.role = .clock
      · simp [hmain, hsclock, htclock,
          stdCounterSubroutine_preserves_well_formed_agent_of_clock]
      · simp [hmain, hsclock, htclock,
          stdCounterSubroutine_preserves_well_formed_agent_of_clock, hat]
    · by_cases htclock : (absorbConsume L K s t).2.role = .clock
      · simp [hmain, hsclock, htclock,
          stdCounterSubroutine_preserves_well_formed_agent_of_clock, has]
      · simp [hmain, hsclock, htclock, has, hat]
  · by_cases hsclock : s.role = .clock
    · by_cases htclock : t.role = .clock
      · simp [hmain, hsclock, htclock,
          stdCounterSubroutine_preserves_well_formed_agent_of_clock]
      · simp [hmain, hsclock, htclock,
          stdCounterSubroutine_preserves_well_formed_agent_of_clock, ht]
    · by_cases htclock : t.role = .clock
      · simp [hmain, hsclock, htclock,
          stdCounterSubroutine_preserves_well_formed_agent_of_clock, hs]
      · simp [hmain, hsclock, htclock, hs, ht]

theorem Phase9Transition_preserves_well_formed_agent (s t : AgentState L K)
    (hs_phase : s.phase.val = 9) (ht_phase : t.phase.val = 9) :
    well_formed_agent s → well_formed_agent t →
    well_formed_agent (Phase9Transition L K s t).1 ∧
    well_formed_agent (Phase9Transition L K s t).2 := by
  unfold Phase9Transition
  exact Phase2Transition_preserves_well_formed_agent_of_phase_pos (L := L) (K := K)
    s t (by omega) (by omega)

theorem Phase10Transition_preserves_well_formed_agent (s t : AgentState L K) :
    well_formed_agent s → well_formed_agent t →
    well_formed_agent (Phase10Transition L K s t).1 ∧
    well_formed_agent (Phase10Transition L K s t).2 := by
  intro hs ht
  unfold Phase10Transition
  dsimp
  constructor <;>
    split_ifs <;>
    simp_all [well_formed_agent, role_phase_invariant_agent, defaultSmallBias]

theorem Transition_preserves_well_formed (s t : AgentState L K) :
    well_formed_agent s → well_formed_agent t →
    well_formed_agent (Transition L K s t).1 ∧
    well_formed_agent (Transition L K s t).2 := by
  intro hs ht
  rcases phaseEpidemicUpdate_preserves_well_formed_agent (L := L) (K := K) s t hs ht with
    ⟨hs_ep, ht_ep⟩
  unfold Transition
  let s' := (phaseEpidemicUpdate L K s t).1
  let t' := (phaseEpidemicUpdate L K s t).2
  have ht_pos_of_s_pos : 1 ≤ s'.phase.val → 1 ≤ t'.phase.val := by
    intro hpos
    exact phaseEpidemicUpdate_right_phase_pos_of_left_phase_pos (L := L) (K := K)
      s t hpos
  change well_formed_agent (match s'.phase with
    | ⟨0, _⟩ => Phase0Transition L K s' t'
    | ⟨1, _⟩ => Phase1Transition L K s' t'
    | ⟨2, _⟩ => Phase2Transition L K s' t'
    | ⟨3, _⟩ => Phase3Transition L K s' t'
    | ⟨4, _⟩ => Phase4Transition L K s' t'
    | ⟨5, _⟩ => Phase5Transition L K s' t'
    | ⟨6, _⟩ => Phase6Transition L K s' t'
    | ⟨7, _⟩ => Phase7Transition L K s' t'
    | ⟨8, _⟩ => Phase8Transition L K s' t'
    | ⟨9, _⟩ => Phase9Transition L K s' t'
    | ⟨10, _⟩ => Phase10Transition L K s' t'
    | _ => (s', t')).1 ∧
    well_formed_agent (match s'.phase with
    | ⟨0, _⟩ => Phase0Transition L K s' t'
    | ⟨1, _⟩ => Phase1Transition L K s' t'
    | ⟨2, _⟩ => Phase2Transition L K s' t'
    | ⟨3, _⟩ => Phase3Transition L K s' t'
    | ⟨4, _⟩ => Phase4Transition L K s' t'
    | ⟨5, _⟩ => Phase5Transition L K s' t'
    | ⟨6, _⟩ => Phase6Transition L K s' t'
    | ⟨7, _⟩ => Phase7Transition L K s' t'
    | ⟨8, _⟩ => Phase8Transition L K s' t'
    | ⟨9, _⟩ => Phase9Transition L K s' t'
    | ⟨10, _⟩ => Phase10Transition L K s' t'
    | _ => (s', t')).2
  rcases h_phase : s'.phase with ⟨n, hn⟩
  match n, hn with
  | 0, _ =>
    exact Phase0Transition_preserves_well_formed_agent (L := L) (K := K) s' t' hs_ep ht_ep
  | 1, _ =>
    exact Phase1Transition_preserves_well_formed_agent (L := L) (K := K) s' t' hs_ep ht_ep
  | 2, _ =>
    have hs_pos : 1 ≤ s'.phase.val := by rw [h_phase]; simp
    exact Phase2Transition_preserves_well_formed_agent_of_phase_pos (L := L) (K := K)
      s' t' hs_pos (ht_pos_of_s_pos hs_pos) hs_ep ht_ep
  | 3, _ =>
    exact Phase3Transition_preserves_well_formed_agent (L := L) (K := K) s' t' hs_ep ht_ep
  | 4, _ =>
    have hs_pos : 1 ≤ s'.phase.val := by rw [h_phase]; simp
    exact Phase4Transition_preserves_well_formed_agent_of_phase_pos (L := L) (K := K)
      s' t' hs_pos (ht_pos_of_s_pos hs_pos) hs_ep ht_ep
  | 5, _ =>
    exact Phase5Transition_preserves_well_formed_agent (L := L) (K := K) s' t' hs_ep ht_ep
  | 6, _ =>
    exact Phase6Transition_preserves_well_formed_agent (L := L) (K := K) s' t' hs_ep ht_ep
  | 7, _ =>
    exact Phase7Transition_preserves_well_formed_agent (L := L) (K := K) s' t' hs_ep ht_ep
  | 8, _ =>
    exact Phase8Transition_preserves_well_formed_agent (L := L) (K := K) s' t' hs_ep ht_ep
  | 9, _ =>
    have hs_pos : 1 ≤ s'.phase.val := by rw [h_phase]; simp
    unfold Phase9Transition
    exact Phase2Transition_preserves_well_formed_agent_of_phase_pos (L := L) (K := K)
      s' t' hs_pos (ht_pos_of_s_pos hs_pos) hs_ep ht_ep
  | 10, _ =>
    exact Phase10Transition_preserves_well_formed_agent (L := L) (K := K) s' t' hs_ep ht_ep
  | n + 11, hn => omega

theorem well_formed_agent_post_phase_zero_role_partition (a : AgentState L K)
    (ha : well_formed_agent a) (hphase : 1 ≤ a.phase.val) :
    a.role = .main ∨ a.role = .reserve ∨ a.role = .clock ∨ a.phase.val = 10 := by
  cases hrole : a.role
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · right; right; right
    rcases ha.1 (Or.inl hrole) with h0 | h10
    · omega
    · exact h10
  · right; right; right
    rcases ha.1 (Or.inr hrole) with h0 | h10
    · omega
    · exact h10

private theorem well_formed_agents_preserved_by_step (c c' : Config (AgentState L K))
    (h_c : ∀ a ∈ c, well_formed_agent a)
    (h_step : (NonuniformMajority L K).StepRel c c') :
    ∀ a ∈ c', well_formed_agent a := by
  rcases h_step with ⟨r₁, r₂, happ, hc'⟩
  dsimp [Protocol.Applicable, NonuniformMajority] at happ hc'
  have hr₁_mem : r₁ ∈ c := Multiset.mem_of_le happ (by simp)
  have hr₂_mem : r₂ ∈ c := Multiset.mem_of_le happ (by simp)
  have htrans := Transition_preserves_well_formed (L := L) (K := K) r₁ r₂
    (h_c r₁ hr₁_mem) (h_c r₂ hr₂_mem)
  rw [hc']
  intro a ha
  simp only [Multiset.mem_add, Multiset.mem_cons, Multiset.mem_singleton] at ha
  rcases ha with h_old | h_new
  · exact h_c a (Multiset.mem_of_le (Multiset.sub_le_self c {r₁, r₂}) h_old)
  · rcases h_new with h_eq | h_eq
    · simpa [h_eq] using htrans.1
    · simpa [h_eq] using htrans.2

private theorem reachable_preserves_well_formed_agents (init c : Config (AgentState L K))
    (h_init : validInitial init)
    (h_reach : Protocol.Reachable (NonuniformMajority L K) init c) :
    ∀ a ∈ c, well_formed_agent a := by
  induction h_reach with
  | refl =>
      exact validInitial_well_formed_agent init h_init
  | tail _ hstep ih =>
      exact well_formed_agents_preserved_by_step (L := L) (K := K) _ _ ih hstep

/-- After Phase 0, every agent in `c` has either acquired a final role
(Main / Reserve / Clock) or has been routed to the slow stable-backup track
at phase 10.

This is true whenever `c` is reachable from a valid initial configuration
via the protocol; it follows from the reachable well-formedness invariant. -/
theorem post_phase_zero_role_partition
    {L K : ℕ} (init c : Config (AgentState L K))
    (h_init : validInitial init)
    (h_reach : Protocol.Reachable (NonuniformMajority L K) init c)
    (h : ∀ a ∈ c, a.phase.val ≥ 1) :
    ∀ a ∈ c, a.role = .main ∨ a.role = .reserve ∨ a.role = .clock ∨
              a.phase.val = 10 := by
  intro a ha
  have hwf := reachable_preserves_well_formed_agents (L := L) (K := K) init c h_init h_reach a ha
  exact well_formed_agent_post_phase_zero_role_partition (L := L) (K := K) a hwf (h a ha)

/-! ### Per-phase preservation of `role_phase_invariant_agent` -/

theorem role_phase_invariant_agent_of_not_transient (a : AgentState L K)
    (hmcr : a.role ≠ .mcr) (hcr : a.role ≠ .cr) :
    role_phase_invariant_agent a := by
  intro htrans
  rcases htrans with hm | hc
  · exact False.elim (hmcr hm)
  · exact False.elim (hcr hc)

theorem role_phase_invariant_agent_of_eq_role_phase {a b : AgentState L K}
    (ha : role_phase_invariant_agent a)
    (hrole : b.role = a.role)
    (hphase : b.phase.val = a.phase.val) :
    role_phase_invariant_agent b := by
  intro htrans
  have htrans_a : a.role = .mcr ∨ a.role = .cr := by
    simpa [hrole] using htrans
  rcases ha htrans_a with h0 | h10
  · left; omega
  · right; omega

theorem stdCounterSubroutine_preserves_role_phase_invariant_of_clock (a : AgentState L K)
    (hclock : a.role = .clock) :
    role_phase_invariant_agent (stdCounterSubroutine L K a) := by
  unfold stdCounterSubroutine advancePhase
  split_ifs <;>
    exact role_phase_invariant_agent_of_not_transient _ (by simp [hclock]) (by simp [hclock])

theorem doSplit_preserves_role_phase_invariant (r m : AgentState L K) :
    role_phase_invariant_agent r → role_phase_invariant_agent m →
    role_phase_invariant_agent (doSplit L K r m).1 ∧
    role_phase_invariant_agent (doSplit L K r m).2 := by
  intro hr hm
  unfold doSplit
  match m.bias with
  | .zero =>
      simp [hr, hm]
  | .dyadic sgn j =>
      by_cases hguard : ¬r.hour.val = L ∧ j < r.hour
      · by_cases hpos : j.val > 0
        · simp [hguard, hpos]
          exact ⟨role_phase_invariant_agent_of_not_transient _ (by simp) (by simp),
            role_phase_invariant_agent_of_eq_role_phase hm (by simp) (by simp)⟩
        · simp [hguard, hpos, hr, hm]
      · simp [hguard, hr, hm]

theorem cancelSplit_preserves_role_phase_invariant (s t : AgentState L K) :
    role_phase_invariant_agent s → role_phase_invariant_agent t →
    role_phase_invariant_agent (cancelSplit L K s t).1 ∧
    role_phase_invariant_agent (cancelSplit L K s t).2 := by
  intro hs ht
  unfold cancelSplit
  match s.bias, t.bias with
  | .zero, .zero =>
      simp [hs, ht]
  | .zero, .dyadic _ _ =>
      simp [hs, ht]
  | .dyadic _ _, .zero =>
      simp [hs, ht]
  | .dyadic sgn_s i, .dyadic sgn_t j =>
      have hs_bias : ∀ b : Bias L, role_phase_invariant_agent ({ s with bias := b }) := by
        intro b
        exact role_phase_invariant_agent_of_eq_role_phase hs (by simp) (by simp)
      have ht_bias : ∀ b : Bias L, role_phase_invariant_agent ({ t with bias := b }) := by
        intro b
        exact role_phase_invariant_agent_of_eq_role_phase ht (by simp) (by simp)
      by_cases hsgn : sgn_s ≠ sgn_t
      · by_cases heq : i.val = j.val
        · simp [hsgn, heq]
          exact ⟨hs_bias .zero, ht_bias .zero⟩
        · by_cases hg1 : i.val + 1 = j.val
          · simp [hsgn, heq, hg1]
            exact ⟨hs_bias (.dyadic sgn_s ⟨i.val + 1, by omega⟩), ht_bias .zero⟩
          · by_cases hg1' : j.val + 1 = i.val
            · simp [hsgn, heq, hg1, hg1']
              exact ⟨hs_bias .zero, ht_bias (.dyadic sgn_t ⟨j.val + 1, by omega⟩)⟩
            · by_cases hg2 : i.val + 2 = j.val
              · simp [hsgn, heq, hg1, hg1', hg2]
                exact ⟨hs_bias (.dyadic sgn_s ⟨i.val + 1, by omega⟩),
                  ht_bias (.dyadic sgn_s ⟨i.val + 2, by omega⟩)⟩
              · by_cases hg2' : j.val + 2 = i.val
                · simp [hsgn, heq, hg1, hg1', hg2, hg2']
                  exact ⟨hs_bias (.dyadic sgn_t ⟨j.val + 2, by omega⟩),
                    ht_bias (.dyadic sgn_t ⟨j.val + 1, by omega⟩)⟩
                · simp [hsgn, heq, hg1, hg1', hg2, hg2', hs, ht]
      · simp [hsgn, hs, ht]

theorem absorbConsume_preserves_role_phase_invariant (s t : AgentState L K) :
    role_phase_invariant_agent s → role_phase_invariant_agent t →
    role_phase_invariant_agent (absorbConsume L K s t).1 ∧
    role_phase_invariant_agent (absorbConsume L K s t).2 := by
  intro hs ht
  unfold absorbConsume
  match s.bias, t.bias with
  | .zero, .zero =>
      simp [hs, ht]
  | .zero, .dyadic _ _ =>
      simp [hs, ht]
  | .dyadic _ _, .zero =>
      simp [hs, ht]
  | .dyadic .pos _, .dyadic .pos _ =>
      simp [hs, ht]
  | .dyadic .neg _, .dyadic .neg _ =>
      simp [hs, ht]
  | .dyadic .pos i, .dyadic .neg j =>
      by_cases hleft : j < i ∧ s.full = false
      · simp [hleft]
        exact ⟨role_phase_invariant_agent_of_eq_role_phase hs (by simp) (by simp),
          role_phase_invariant_agent_of_eq_role_phase ht (by simp) (by simp)⟩
      · by_cases hright : i < j ∧ t.full = false
        · simp [hleft, hright]
          exact ⟨role_phase_invariant_agent_of_eq_role_phase hs (by simp) (by simp),
            role_phase_invariant_agent_of_eq_role_phase ht (by simp) (by simp)⟩
        · simp [hleft, hright, hs, ht]
  | .dyadic .neg i, .dyadic .pos j =>
      by_cases hleft : j < i ∧ s.full = false
      · simp [hleft]
        exact ⟨role_phase_invariant_agent_of_eq_role_phase hs (by simp) (by simp),
          role_phase_invariant_agent_of_eq_role_phase ht (by simp) (by simp)⟩
      · by_cases hright : i < j ∧ t.full = false
        · simp [hleft, hright]
          exact ⟨role_phase_invariant_agent_of_eq_role_phase hs (by simp) (by simp),
            role_phase_invariant_agent_of_eq_role_phase ht (by simp) (by simp)⟩
        · simp [hleft, hright, hs, ht]

theorem Phase1Transition_preserves_role_phase_invariant (s t : AgentState L K) :
    role_phase_invariant_agent s → role_phase_invariant_agent t →
    role_phase_invariant_agent (Phase1Transition L K s t).1 ∧
    role_phase_invariant_agent (Phase1Transition L K s t).2 := by
  intro hs ht
  unfold Phase1Transition role_phase_invariant_agent
  refine ⟨?_, ?_⟩ <;> split_ifs <;> intro h_or
  · exact hs (by simpa using h_or)
  · exact hs h_or
  · exact ht (by simpa using h_or)
  · exact ht h_or

-- Phase 2/9 conditionally advance phase; preservation requires a stronger joint invariant
-- (e.g. role ∈ {mcr, cr} implies opinions = 0). Deferred to paper §5 wellformedness work.

-- Phase 7/8 use cancelSplit/absorbConsume + stdCounterSubroutine; preservation needs
-- explicit case analysis on s.role and t.role + bias-match. Deferred — DS dispatch.

theorem Phase5Transition_preserves_role_phase_invariant (s t : AgentState L K) :
    role_phase_invariant_agent s → role_phase_invariant_agent t →
    role_phase_invariant_agent (Phase5Transition L K s t).1 ∧
    role_phase_invariant_agent (Phase5Transition L K s t).2 := by
  intro hs ht
  refine ⟨?_, ?_⟩ <;> intro h_or
  · unfold Phase5Transition at h_or ⊢
    dsimp at h_or ⊢
    simp only [stdCounterSubroutine, advancePhase] at h_or ⊢
    split_ifs at h_or ⊢ <;> simp_all <;>
    first | simpa using hs h_or | (simp at h_or; exfalso; exact h_or)
  · unfold Phase5Transition at h_or ⊢
    dsimp at h_or ⊢
    simp only [stdCounterSubroutine, advancePhase] at h_or ⊢
    split_ifs at h_or ⊢ <;> simp_all <;>
    first | simpa using ht h_or | (simp at h_or; exfalso; exact h_or)

theorem Phase6Transition_preserves_role_phase_invariant (s t : AgentState L K) :
    role_phase_invariant_agent s → role_phase_invariant_agent t →
    role_phase_invariant_agent (Phase6Transition L K s t).1 ∧
    role_phase_invariant_agent (Phase6Transition L K s t).2 := by
  intro hs ht
  unfold Phase6Transition
  dsimp
  by_cases hleft : s.role = .reserve ∧ t.role = .main ∧ t.bias ≠ .zero
  · rcases doSplit_preserves_role_phase_invariant (L := L) (K := K) s t hs ht with ⟨hds, hdt⟩
    by_cases hsclock : (doSplit L K s t).1.role = .clock
    · by_cases htclock : (doSplit L K s t).2.role = .clock
      · simp [hleft, hsclock, htclock,
          stdCounterSubroutine_preserves_role_phase_invariant_of_clock]
      · simp [hleft, hsclock, htclock,
          stdCounterSubroutine_preserves_role_phase_invariant_of_clock, hdt]
    · by_cases htclock : (doSplit L K s t).2.role = .clock
      · simp [hleft, hsclock, htclock,
          stdCounterSubroutine_preserves_role_phase_invariant_of_clock, hds]
      · simp [hleft, hsclock, htclock, hds, hdt]
  · by_cases hright : t.role = .reserve ∧ s.role = .main ∧ s.bias ≠ .zero
    · rcases doSplit_preserves_role_phase_invariant (L := L) (K := K) t s ht hs with ⟨hdt, hds⟩
      by_cases hsclock : (doSplit L K t s).2.role = .clock
      · by_cases htclock : (doSplit L K t s).1.role = .clock
        · simp [hleft, hright, hsclock, htclock,
            stdCounterSubroutine_preserves_role_phase_invariant_of_clock]
        · simp [hleft, hright, hsclock, htclock,
            stdCounterSubroutine_preserves_role_phase_invariant_of_clock, hdt]
      · by_cases htclock : (doSplit L K t s).1.role = .clock
        · simp [hleft, hright, hsclock, htclock,
            stdCounterSubroutine_preserves_role_phase_invariant_of_clock, hds]
        · simp [hleft, hright, hsclock, htclock, hds, hdt]
    · by_cases hsclock : s.role = .clock
      · by_cases htclock : t.role = .clock
        · simp [hleft, hright, hsclock, htclock,
            stdCounterSubroutine_preserves_role_phase_invariant_of_clock]
        · simp [hleft, hright, hsclock, htclock,
            stdCounterSubroutine_preserves_role_phase_invariant_of_clock, ht]
      · by_cases htclock : t.role = .clock
        · simp [hleft, hright, hsclock, htclock,
            stdCounterSubroutine_preserves_role_phase_invariant_of_clock, hs]
        · simp [hleft, hright, hsclock, htclock, hs, ht]

theorem Phase7Transition_preserves_role_phase_invariant (s t : AgentState L K) :
    role_phase_invariant_agent s → role_phase_invariant_agent t →
    role_phase_invariant_agent (Phase7Transition L K s t).1 ∧
    role_phase_invariant_agent (Phase7Transition L K s t).2 := by
  intro hs ht
  unfold Phase7Transition
  dsimp
  by_cases hmain : s.role = .main ∧ t.role = .main
  · rcases cancelSplit_preserves_role_phase_invariant (L := L) (K := K) s t hs ht with ⟨hcs, hct⟩
    by_cases hsclock : (cancelSplit L K s t).1.role = .clock
    · by_cases htclock : (cancelSplit L K s t).2.role = .clock
      · simp [hmain, hsclock, htclock,
          stdCounterSubroutine_preserves_role_phase_invariant_of_clock]
      · simp [hmain, hsclock, htclock,
          stdCounterSubroutine_preserves_role_phase_invariant_of_clock, hct]
    · by_cases htclock : (cancelSplit L K s t).2.role = .clock
      · simp [hmain, hsclock, htclock,
          stdCounterSubroutine_preserves_role_phase_invariant_of_clock, hcs]
      · simp [hmain, hsclock, htclock, hcs, hct]
  · by_cases hsclock : s.role = .clock
    · by_cases htclock : t.role = .clock
      · simp [hmain, hsclock, htclock,
          stdCounterSubroutine_preserves_role_phase_invariant_of_clock]
      · simp [hmain, hsclock, htclock,
          stdCounterSubroutine_preserves_role_phase_invariant_of_clock, ht]
    · by_cases htclock : t.role = .clock
      · simp [hmain, hsclock, htclock,
          stdCounterSubroutine_preserves_role_phase_invariant_of_clock, hs]
      · simp [hmain, hsclock, htclock, hs, ht]

theorem Phase8Transition_preserves_role_phase_invariant (s t : AgentState L K) :
    role_phase_invariant_agent s → role_phase_invariant_agent t →
    role_phase_invariant_agent (Phase8Transition L K s t).1 ∧
    role_phase_invariant_agent (Phase8Transition L K s t).2 := by
  intro hs ht
  unfold Phase8Transition
  dsimp
  by_cases hmain : s.role = .main ∧ t.role = .main
  · rcases absorbConsume_preserves_role_phase_invariant (L := L) (K := K) s t hs ht with ⟨has, hat⟩
    by_cases hsclock : (absorbConsume L K s t).1.role = .clock
    · by_cases htclock : (absorbConsume L K s t).2.role = .clock
      · simp [hmain, hsclock, htclock,
          stdCounterSubroutine_preserves_role_phase_invariant_of_clock]
      · simp [hmain, hsclock, htclock,
          stdCounterSubroutine_preserves_role_phase_invariant_of_clock, hat]
    · by_cases htclock : (absorbConsume L K s t).2.role = .clock
      · simp [hmain, hsclock, htclock,
          stdCounterSubroutine_preserves_role_phase_invariant_of_clock, has]
      · simp [hmain, hsclock, htclock, has, hat]
  · by_cases hsclock : s.role = .clock
    · by_cases htclock : t.role = .clock
      · simp [hmain, hsclock, htclock,
          stdCounterSubroutine_preserves_role_phase_invariant_of_clock]
      · simp [hmain, hsclock, htclock,
          stdCounterSubroutine_preserves_role_phase_invariant_of_clock, ht]
    · by_cases htclock : t.role = .clock
      · simp [hmain, hsclock, htclock,
          stdCounterSubroutine_preserves_role_phase_invariant_of_clock, hs]
      · simp [hmain, hsclock, htclock, hs, ht]

theorem Phase10Transition_preserves_role_phase_invariant (s t : AgentState L K) :
    role_phase_invariant_agent s → role_phase_invariant_agent t →
    role_phase_invariant_agent (Phase10Transition L K s t).1 ∧
    role_phase_invariant_agent (Phase10Transition L K s t).2 := by
  intro hs ht
  refine ⟨?_, ?_⟩ <;> intro h_or
  · unfold Phase10Transition at h_or ⊢
    dsimp at h_or ⊢
    split_ifs at h_or ⊢ <;> simp_all <;>
    first | simpa using hs h_or | (simp at h_or; exfalso; exact h_or)
  · unfold Phase10Transition at h_or ⊢
    dsimp at h_or ⊢
    split_ifs at h_or ⊢ <;> simp_all <;>
    first | simpa using ht h_or | (simp at h_or; exfalso; exact h_or)

/-- Target for **Doty Lemma 5.1** (population-splitting convergence).

This is not exported as a theorem until the geometric waiting-time coupling is
proved from the protocol Markov-chain model. -/
abbrev lemma_5_1_population_splitting_target {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (n : ℕ) (_hn : 0 < n)
    (T : Ω → ℝ) (_hT : AEMeasurable T μ)
    (_h_hitting : T ≥ 0)
    (ε : ℝ) (_hε : 0 < ε) : Prop :=
    μ.real {ω | T ω > 12.5 * Real.log (n : ℝ)} ≤ (1 : ℝ) / ((n : ℝ) ^ 2)
  /-
  -- Strategy: represent T as a sum of independent geometric waiting times G_i.
  -- The population-splitting process (Phase 0, Rules 1–5) requires k = O(n)
  -- sequential transitions, each with success probability p_i = Θ(1/n).
  -- Then T = Σ G_i with G_i ~ Geometric(p_i), E[G_i] = 1/p_i, μ_T = Σ 1/p_i = Θ(n²).
  -- Let p_min = min p_i = Θ(1/n). Apply the Janson geometric upper tail
  -- with λ = 12.5 log n / μ_T after proving the geometric MGF estimate.
  -- The bound simplifies to ≤ exp(−c · n · λ · (λ − 1 − log λ) / n) ... ≤ 1/n².
  -- The actual proof requires:
  -- (1) Define G_i as the inter-arrival times of the Phase 0 transitions
  --     (waiting time for the i-th MCR/CR/Clock assignment).
  -- (2) Prove G_i ~ Geometric(p_i) for appropriate p_i (involves the
  --     epidemic pairwise-interaction model, Doty §4.2).
  -- (3) Show T = Σ G_i (uses the sequential Phase 0 rule structure).
  -- (4) Bound k, p_i such that μ_T ≤ C·n² and p_min ≥ c/n.
  -- (5) Apply the Janson geometric tail bound with λ = 12.5 log n / μ_T.
  -- (6) Simplify the Janson bound to ≤ 1/n² using the Taylor expansion
  --     of λ − 1 − log λ and the lower bounds on p_min μ_T.
  -- Steps 1–4 require the Markov-chain / epidemic-coupling framework;
  -- steps 5–6 are algebraic and can be filled once the Janson lemma lands.
  -/

/-- **Doty Lemma 5.2** (Phase 0 role distribution).

By the end of Phase 0, with high probability `1 − O(1/n²)`:
  - `|RoleMCR | = 0`
  - `(n/2)(1−ε) ≤ |M| ≤ (n/2)(1+ε)`
  - `|C|, |R| ≥ (n/4)(1−ε)`

And deterministically (if Phase 1 initializes without error):
  `n/3 ≤ |M| ≤ 2n/3`, `n/6 ≤ |R| ≤ 2n/3`, `2 ≤ |C| ≤ n/3`.

This statement records the high-probability tail for the Phase 0 outcome
on a probability space `(Ω, μ)`. The proof (relying on Lemma 5.1 plus the
`RoleCR → Clock | Reserve` coupling) is deferred. -/
abbrev lemma_5_2_phase_zero_partition_target {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (n : ℕ) (_hn : 0 < n) (ε : ℝ) (_hε : 0 < ε)
    (badPhaseZeroPartition : Ω → Prop) : Prop :=
    μ.real {ω | badPhaseZeroPartition ω} ≤ (1 : ℝ) / ((n : ℝ) ^ 2)
  /-
  -- Full statement would reference the counts |M|, |C|, |R| on configurations
  -- reachable after Phase 0. The probability-space wrapper and the event
  -- definition need the protocol Markov-chain model, which is not yet built.
  -/

/-- **Doty Lemma 5.3** (Phase 1 convergence).

At the end of Phase 1, with high probability `1 − O(1/n²)`:
  - if `|g| ≥ 0.025·|M|`: the protocol stabilizes to the correct output
    in Phase 2 (no agents continue to Phase 3);
  - if `|g| < 0.025·|M|`: all agents have bias `∈ {−1, 0, +1}` and the
    total count of biased agents is `≤ 0.03·|M|`.

This is the discrete-averaging convergence bound (proved via the epidemic
Lemma 4.6). The Lean statement is a probability-space wrapper; the proof
requires the epidemic coupling, which is not yet formalized. -/
abbrev lemma_5_3_phase_one_concentration_target {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (n : ℕ) (_g : ℤ) (_M : ℕ) (ε : ℝ) (_hε : 0 < ε)
    (badPhaseOneConcentration : Ω → Prop) : Prop :=
    μ.real {ω | badPhaseOneConcentration ω} ≤ (1 : ℝ) / ((n : ℝ) ^ 2)
  /-
  -- Strategy: Phase 1 discrete averaging acts like an epidemic on the
  -- cancelling subpopulation (agents whose opinions differ from the majority).
  -- Let f_0 = |gap|/n be the initial majority fraction. The cancelling
  -- subpopulation has size ≈ (1 - f_0)·n.
  -- Applying the epidemic-time concentration theorem to this subpopulation with
  -- parameters a = 0 (start), b = 1 - ε (near-full convergence) shows
  -- that Phase 1 finishes in time ≤ (1 + ε)·E[t] w.h.p., where
  -- E[t] = (1/2)·log((1 - f_0)/f_0) (the epidemic time for cancelling pairs).
  -- The bound ≤ 1/n² follows from the exponential tail in
  -- the epidemic-time concentration theorem with
  -- C·ε²·E[t]·n·min(a,1-b) = Ω(log n).
  -- TODO: (1) Define the cancelling subpopulation size from |g| and n.
  -- (2) Show that Phase 1 biased-agent dynamics (opinionsUnion + advancePhase)
  --     simulate an epidemic on this subpopulation.
  -- (3) Compute the epidemic parameters a, b.
  -- (4) Apply the epidemic-time concentration theorem with those parameters.
  -- (5) Rearrange the bound to ≤ 1/n².
  -/

/-! ### §6 — Phase 3 fixed-resolution clock analysis -/

/-- **Doty Theorem 6.9**: clock concentration.

In the Phase 3 fixed-resolution clock (drip probability p = 1, k minutes
per hour), a fraction `c` of agents act as clocks with minute field
advancing from 0 to `kL`. The front tail behind the peak decays
exponentially; the back tail ahead of the peak decays double-exponentially.

Given a population size `n` and target minute `kL`, let `T` be the time
(hitting time) for a given Clock agent to reach minute `kL`. The tail
probability `P[T > t]` for deviations above the mean has exponential
decay.

This statement records a tail bound of the form
  `P[T > (1+δ)·E[T]] ≤ exp(−δ²·E[T] / C)`
on a probability space `(Ω, μ)`. The bound is a consequence of the
clock's sub-Gaussian properties (drip + epidemic reactions). The
proof (requiring the full clock analysis of §6) is deferred. -/
abbrev theorem_6_9_clock_concentration_target {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (n : ℕ) (_hn : 0 < n) (c : ℝ) (_hc : 0 < c ∧ c < 1)
    (k L : ℕ) (_hk : 0 < k) (_hL : 0 < L)
    (T : Ω → ℝ) (_hT : AEMeasurable T μ) (_hT_nonneg : 0 ≤ T)
    (δ : ℝ) (_hδ : 0 < δ) : Prop :=
    μ.real {ω | T ω > (1 + δ) * (2.5 * Real.log (n : ℝ))} ≤
    Real.exp (-(δ ^ 2) * (c : ℝ) * (n : ℝ) / (2 + δ))
  /-
  -- The factor 2.5·ln n is the expected clock-advance time (ref. §6.9 analysis).
  -- The exponential tail uses the observation that clock-minutes count at rate
  -- 2·c per interaction and the multiplicative Chernoff bound (Theorem 4.1).
  -/

/-- **Doty Theorem 6.1**: tie case. If the initial gap `g = 0`, then by
the end of Phase 3 all biased agents have minimal exponent `−L`, with
high probability `1 − O(1/n²)`.

The event `{ω | all biased agents have exponent = −L}` is defined on a
protocol execution `(Ω, μ)`. The proof (using the clock concentration
Theorem 6.9) is deferred. -/
abbrev theorem_6_1_tie_min_exponent_target {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (n : ℕ) (_hn : 0 < n)
    (badTieMinExponent : Ω → Prop) : Prop :=
    μ.real {ω | badTieMinExponent ω} ≤ (1 : ℝ) / ((n : ℝ) ^ 2)

/-- **Doty Theorem 6.2**: non-tie case. Assume `|g| < 0.025·|M|`. Let
`−l = ⌊log₂(0.4·|M| / |g|)⌋` and `i = sign(g)`. Let `M*` be the set of
Main agents with opinion `i` and exponent ∈ {−l, −(l+1), −(l+2)}. Then
by the end of Phase 3, `|M*| ≥ 0.92·|M|` with high probability
`1 − O(1/n²)`.

The event is quantified on a probability space `(Ω, μ)`. The proof
(using Theorem 6.9 + the Phase 3 cancel/split analysis) is deferred. -/
abbrev theorem_6_2_phase_three_distribution_target {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (n : ℕ) (_g : ℤ) (M : ℕ) (_hn : 0 < n) (_hM : 0 < M)
    (badPhaseThreeDistribution : Ω → Prop) : Prop :=
    μ.real {ω | badPhaseThreeDistribution ω} ≤ (1 : ℝ) / ((n : ℝ) ^ 2)

/-! ### §7 — cleanup phases (5–8) and stable backup (10) -/

/-- **Doty Lemma 7.1**: by end of Phase 5, all Reserve agents have
`sample ≠ ⊥`, with high probability `1 − O(1/n²)`.

Equivalently: the probability that some Reserve agent fails to sample
an exponent by the end of Phase 5 decays as `O(1/n²)`. The event is
defined on a protocol execution `(Ω, μ)` with population size `n`.
The proof (via Lemma 4.7 epidemic bound) is deferred. -/
abbrev lemma_7_1_reserve_sampled_target {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (n : ℕ) (_hn : 0 < n)
    (badReserveSampled : Ω → Prop) : Prop :=
    μ.real {ω | badReserveSampled ω} ≤ (1 : ℝ) / ((n : ℝ) ^ 2)

/-- **Doty Lemma 7.2**: by end of Phase 6, all biased agents have
exponent `≤ −l`, with high probability `1 − O(1/n²)`.

The event is defined on a protocol execution `(Ω, μ)`. The proof
(using Lemma 7.1 + the split analysis of Phase 6) is deferred. -/
abbrev lemma_7_2_phase_six_exponents_target {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (n : ℕ) (_l : ℕ) (_hn : 0 < n)
    (badPhaseSixExponents : Ω → Prop) : Prop :=
    μ.real {ω | badPhaseSixExponents ω} ≤ (1 : ℝ) / ((n : ℝ) ^ 2)

/-- **Doty Lemma 7.5**: at end of Phase 7, all minority agents have
exponent `< −(l+2)`, with high probability `1 − O(1/n²)`.

The event is defined on a protocol execution `(Ω, μ)`. The proof
(using Lemma 7.2 + the extended cancel/split analysis of Phase 7)
is deferred. -/
abbrev lemma_7_5_phase_seven_minority_target {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (n : ℕ) (_l : ℕ) (_hn : 0 < n)
    (badPhaseSevenMinority : Ω → Prop) : Prop :=
    μ.real {ω | badPhaseSevenMinority ω} ≤ (1 : ℝ) / ((n : ℝ) ^ 2)

/-- **Doty Lemma 7.6**: at end of Phase 8, there are no more minority
agents, with high probability `1 − O(1/n²)`.

The event is defined on a protocol execution `(Ω, μ)`. The proof
(using Lemma 7.5 + the consumption analysis of Phase 8) is deferred. -/
abbrev lemma_7_6_phase_eight_eliminates_target {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (n : ℕ) (_hn : 0 < n)
    (badPhaseEightEliminates : Ω → Prop) : Prop :=
    μ.real {ω | badPhaseEightEliminates ω} ≤ (1 : ℝ) / ((n : ℝ) ^ 2)

/-- **Doty Lemma 7.7**: the 6-state stable-backup protocol in Phase 10
stably computes majority in `O(n log n)` parallel time, both in
expectation and with high probability `1 − O(1/n²)`.

The tail bound is expressed on a probability space `(Ω, μ)` with a
hitting-time random variable `T`. The proof (standard coupon-collector
argument, as sketched in §7.3) is deferred. -/
abbrev lemma_7_7_phase_ten_stable_backup_target {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (n : ℕ) (_hn : 0 < n)
    (T : Ω → ℝ) (_hT : AEMeasurable T μ) (_hT_nonneg : 0 ≤ T)
    : Prop :=
    μ.real {ω | T ω > (n : ℝ) * Real.log (n : ℝ)} ≤ (1 : ℝ) / ((n : ℝ) ^ 2)

end ExactMajority
