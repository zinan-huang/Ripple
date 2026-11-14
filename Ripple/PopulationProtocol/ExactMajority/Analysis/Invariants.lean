/-
Per-step invariants of the Doty et al. exact-majority protocol.

Reference: Doty et al., §§5–7; §3.1 (bias-sum invariant `g`).
-/

import Ripple.PopulationProtocol.ExactMajority.Protocol.Transition
import Ripple.PopulationProtocol.ExactMajority.Analysis.MainTheorem
import Ripple.PopulationProtocol.ExactMajority.Analysis.Phase0Convergence
import Ripple.PopulationProtocol.ExactMajority.Analysis.Phase3Convergence
import Ripple.PopulationProtocol.ExactMajority.Analysis.TransitionMonotonicity
import Ripple.PopulationProtocol.ExactMajority.Probability.MarkovChain
import Ripple.PopulationProtocol.ExactMajority.Probability.NonuniformMarkovChain
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseConvergence
import Ripple.PopulationProtocol.ExactMajority.Probability.DriftPhaseOfDescent
import Ripple.PopulationProtocol.ExactMajority.Probability.JansonHitting
import Mathlib.Tactic

open Multiset
open scoped NNReal

namespace Ripple.PopulationProtocol.ExactMajority

variable {L K : ℕ}

/-! ### Phase-monotonicity invariants -/

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

set_option linter.flexible false in
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
        runInitsBetween_input_preserved _ _ _
      _ = s.input := by simp
  have ht0_input : t0.input = t.input := by
    calc
      t0.input =
          (runInitsBetween L K t.phase.val p.val ({ t with phase := p })).input := by rw [ht0]
      _ = ({ t with phase := p } : AgentState L K).input :=
        runInitsBetween_input_preserved _ _ _
      _ = t.input := by simp
  by_cases h10 :
      (s.phase.val < 10 ∨ t.phase.val < 10) ∧
        (s0.phase.val = 10 ∨ t0.phase.val = 10)
  · constructor
    · by_cases hs_lt : s.phase.val < 10
      · simp [h10, hs_lt, hs0_input]
      · have ht_lt : t.phase.val < 10 := by
          rcases h10.1 with hs | ht
          · exact False.elim (hs_lt hs)
          · exact ht
        have hs10 : s.phase.val = 10 := by
          have hs_le : s.phase.val ≤ 10 := by have := s.phase.2; omega
          omega
        simp [h10, hs_lt, ht_lt, hs10, hs0_input]
    · by_cases ht_lt : t.phase.val < 10
      · simp [h10, ht_lt, ht0_input]
      · have hs_lt : s.phase.val < 10 := by
          rcases h10.1 with hs | ht
          · exact hs
          · exact False.elim (ht_lt ht)
        have ht10 : t.phase.val = 10 := by
          have ht_le : t.phase.val ≤ 10 := by have := t.phase.2; omega
          omega
        simp [h10, hs_lt, ht_lt, ht10, ht0_input]
  · simp [h10, hs0_input, ht0_input]

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
  rcases hpe : phaseEpidemicUpdate L K s t with ⟨s', t'⟩
  simp only [hpe] at h_ep_s h_ep_t ⊢
  let out :=
    match s'.phase with
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
    | _ => (s', t')
  change (finishPhase10Entry L K s' out.1).input = s.input ∧
    (finishPhase10Entry L K t' out.2).input = t.input
  have hdispatch : out.1.input = s'.input ∧ out.2.input = t'.input := by
    dsimp [out]
    rcases h_phase : s'.phase with ⟨n, hn⟩
    match n, hn with
    | 0, _ => simpa [h_phase] using Phase0Transition_input_preserved L K s' t'
    | 1, _ => simpa [h_phase] using Phase1Transition_input_preserved L K s' t'
    | 2, _ => simpa [h_phase] using Phase2Transition_input_preserved L K s' t'
    | 3, _ => simpa [h_phase] using Phase3Transition_input_preserved L K s' t'
    | 4, _ => simpa [h_phase] using Phase4Transition_input_preserved L K s' t'
    | 5, _ => simpa [h_phase] using Phase5Transition_input_preserved L K s' t'
    | 6, _ => simpa [h_phase] using Phase6Transition_input_preserved L K s' t'
    | 7, _ => simpa [h_phase] using Phase7Transition_input_preserved L K s' t'
    | 8, _ => simpa [h_phase] using Phase8Transition_input_preserved L K s' t'
    | 9, _ => simpa [h_phase] using Phase9Transition_input_preserved L K s' t'
    | 10, _ => simpa [h_phase] using Phase10Transition_input_preserved L K s' t'
    | n + 11, hn => omega
  exact ⟨by simpa using hdispatch.1.trans h_ep_s,
    by simpa using hdispatch.2.trans h_ep_t⟩

/-! ### Bias-sum (gap) invariant -/

@[simp] private lemma finishPhase10Entry_smallBiasInt (before after : AgentState L K) :
    AgentState.smallBiasInt (finishPhase10Entry L K before after) =
      AgentState.smallBiasInt after := by
  simp [AgentState.smallBiasInt]

/-- Phase-0 quota invariant for the small-bias accumulator.

The bounds are phase-specific: Phase 1 averaging can move an unassigned `main`
outside the `≤ 2` bound, but Phase 0 is the only phase where `addSmallBias`
uses this quota to avoid clamping. -/
def WellFormedAgentQuota {L K : ℕ} (a : AgentState L K) : Prop :=
  a.phase.val = 0 →
    (a.role = .mcr → (AgentState.smallBiasInt a).natAbs ≤ 1) ∧
    (a.role = .main → a.assigned = false → (AgentState.smallBiasInt a).natAbs ≤ 2)

private def smallBiasQuotaFields {L K : ℕ} (a : AgentState L K) : Prop :=
  (a.role = .mcr → (AgentState.smallBiasInt a).natAbs ≤ 1) ∧
  (a.role = .main → a.assigned = false → (AgentState.smallBiasInt a).natAbs ≤ 2)

private lemma canonicalPhase10Entry_preserves_well_formed_agent_quota
    (before after : AgentState L K) :
    WellFormedAgentQuota after →
      WellFormedAgentQuota (canonicalPhase10Entry L K before after) := by
  intro hquota hzero
  unfold canonicalPhase10Entry at hzero ⊢
  split_ifs with hentry
  · have hzero_enter : (enterPhase10 L K after).phase.val = 0 := by
      simpa [hentry] using hzero
    have hten : (enterPhase10 L K after).phase.val = 10 :=
      enterPhase10_phase_val (L := L) (K := K) after
    omega
  · exact hquota (by simpa [hentry] using hzero)

private lemma finishPhase10Entry_preserves_well_formed_agent_quota
    (before after : AgentState L K) :
    WellFormedAgentQuota after →
      WellFormedAgentQuota (finishPhase10Entry L K before after) := by
  simpa [finishPhase10Entry] using
    canonicalPhase10Entry_preserves_well_formed_agent_quota (L := L) (K := K) before after

@[simp] private lemma finishPhase10Entry_well_formed_agent_quota_iff
    (before after : AgentState L K) :
    WellFormedAgentQuota (finishPhase10Entry L K before after) ↔
      WellFormedAgentQuota after := by
  unfold finishPhase10Entry canonicalPhase10Entry
  split_ifs with hentry
  · constructor
    · intro _hquota hzero
      omega
    · intro _hquota hzero
      have hten : (enterPhase10 L K after).phase.val = 10 :=
        enterPhase10_phase_val (L := L) (K := K) after
      omega
  · simp

private lemma smallBiasQuotaFields_of_well_formed_agent_quota (a : AgentState L K)
    (hphase : a.phase.val = 0) :
    WellFormedAgentQuota a → smallBiasQuotaFields a := by
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
          simp [inputBiasSum, initialGap, AgentState.inputBiasInt] at IH ⊢
          omega
      | B =>
          simp [inputBiasSum, initialGap, AgentState.inputBiasInt] at IH ⊢
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
    simp [inputBiasSum, add_left_comm]
  have hsum_c' :
      inputBiasSum
          (c - r₁ ::ₘ {r₂} +
          (Transition L K r₁ r₂).1 ::ₘ {(Transition L K r₁ r₂).2}) =
      inputBiasSum (c - r₁ ::ₘ {r₂}) +
        (AgentState.inputBiasInt (Transition L K r₁ r₂).1 +
          AgentState.inputBiasInt (Transition L K r₁ r₂).2) := by
    simp [inputBiasSum, add_left_comm]
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

theorem majorityVerdict_eq_A_iff_initialGap_pos (c : Config (AgentState L K)) :
    majorityVerdict c = outputTripleOfOutput .A ↔ 0 < initialGap c := by
  constructor
  · intro h
    by_contra hnot
    by_cases hneg : initialGap c < 0
    · have hB := majorityVerdict_eq_B_of_initialGap_neg (L := L) (K := K) c hneg
      rw [hB] at h
      simp [outputTripleOfOutput] at h
    · have hzero : initialGap c = 0 := by omega
      have hT := majorityVerdict_eq_T_of_initialGap_zero (L := L) (K := K) c hzero
      rw [hT] at h
      simp [outputTripleOfOutput] at h
  · exact majorityVerdict_eq_A_of_initialGap_pos (L := L) (K := K) c

theorem majorityVerdict_eq_B_iff_initialGap_neg (c : Config (AgentState L K)) :
    majorityVerdict c = outputTripleOfOutput .B ↔ initialGap c < 0 := by
  constructor
  · intro h
    by_contra hnot
    by_cases hpos : 0 < initialGap c
    · have hA := majorityVerdict_eq_A_of_initialGap_pos (L := L) (K := K) c hpos
      rw [hA] at h
      simp [outputTripleOfOutput] at h
    · have hzero : initialGap c = 0 := by omega
      have hT := majorityVerdict_eq_T_of_initialGap_zero (L := L) (K := K) c hzero
      rw [hT] at h
      simp [outputTripleOfOutput] at h
  · exact majorityVerdict_eq_B_of_initialGap_neg (L := L) (K := K) c

theorem majorityVerdict_eq_T_iff_initialGap_zero (c : Config (AgentState L K)) :
    majorityVerdict c = outputTripleOfOutput .T ↔ initialGap c = 0 := by
  constructor
  · intro h
    by_cases hpos : 0 < initialGap c
    · have hA := majorityVerdict_eq_A_of_initialGap_pos (L := L) (K := K) c hpos
      rw [hA] at h
      simp [outputTripleOfOutput] at h
    · by_cases hneg : initialGap c < 0
      · have hB := majorityVerdict_eq_B_of_initialGap_neg (L := L) (K := K) c hneg
        rw [hB] at h
        simp [outputTripleOfOutput] at h
      · omega
  · exact majorityVerdict_eq_T_of_initialGap_zero (L := L) (K := K) c

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

/-- Direct stable-output package for a Phase-10 majority witness endpoint. -/
theorem stable_output_of_phase10MajorityWitness
    (init final : Config (AgentState L K))
    (hwitness : phase10MajorityWitness (L := L) (K := K) init final) :
    (doutPartition L K).output (majorityVerdict init) final ∧
      (NonuniformMajority L K).IsStable (doutPartition L K) final := by
  rcases hwitness with ⟨hgap, hfinal⟩ | ⟨hgap, hfinal⟩ | ⟨hgap, hfinal⟩
  · exact phase10_unanimous_A_majority_witness_of_initialGap_pos
      (L := L) (K := K) init final hfinal hgap
  · exact phase10_unanimous_B_majority_witness_of_initialGap_neg
      (L := L) (K := K) init final hfinal hgap
  · exact phase10_unanimous_T_majority_witness_of_initialGap_zero
      (L := L) (K := K) init final hfinal hgap

/-- Convert a Phase-10 endpoint stated with the generic output partition into
the concrete A/B/T endpoint witness used by the deterministic stability
bridges. -/
theorem phase10MajorityWitness_of_phase10_partition_output
    (init final : Config (AgentState L K))
    (hphase : ∀ a ∈ final, a.phase.val = 10)
    (hout : (doutPartition L K).output (majorityVerdict init) final) :
    phase10MajorityWitness (L := L) (K := K) init final := by
  by_cases hpos : 0 < initialGap init
  · left
    refine ⟨hpos, ?_⟩
    intro a ha
    refine ⟨hphase a ha, ?_⟩
    have houtA : (doutPartition L K).output (outputTripleOfOutput .A) final := by
      rw [← majorityVerdict_eq_A_of_initialGap_pos (L := L) (K := K) init hpos]
      exact hout
    exact unanimous_output_of_doutPartition_output (L := L) (K := K) final .A houtA a ha
  · by_cases hneg : initialGap init < 0
    · right; left
      refine ⟨hneg, ?_⟩
      intro a ha
      refine ⟨hphase a ha, ?_⟩
      have houtB : (doutPartition L K).output (outputTripleOfOutput .B) final := by
        rw [← majorityVerdict_eq_B_of_initialGap_neg (L := L) (K := K) init hneg]
        exact hout
      exact unanimous_output_of_doutPartition_output (L := L) (K := K) final .B houtB a ha
    · right; right
      have hzero : initialGap init = 0 := by omega
      refine ⟨hzero, ?_⟩
      intro a ha
      refine ⟨hphase a ha, ?_⟩
      have houtT : (doutPartition L K).output (outputTripleOfOutput .T) final := by
        rw [← majorityVerdict_eq_T_of_initialGap_zero (L := L) (K := K) init hzero]
        exact hout
      exact unanimous_output_of_doutPartition_output (L := L) (K := K) final .T houtT a ha

/-- A Phase-10 majority witness is exactly a Phase-10 endpoint whose generic
partition output is the initial majority verdict. -/
theorem phase10MajorityWitness_iff_phase10_partition_output
    (init final : Config (AgentState L K)) :
    phase10MajorityWitness (L := L) (K := K) init final ↔
      (∀ a ∈ final, a.phase.val = 10) ∧
        (doutPartition L K).output (majorityVerdict init) final := by
  constructor
  · intro hwitness
    constructor
    · intro a ha
      rcases hwitness with ⟨_, hfinal⟩ | ⟨_, hfinal⟩ | ⟨_, hfinal⟩
      · exact (hfinal a ha).1
      · exact (hfinal a ha).1
      · exact (hfinal a ha).1
    · exact (stable_output_of_phase10MajorityWitness
        (L := L) (K := K) init final hwitness).1
  · rintro ⟨hphase, hout⟩
    exact phase10MajorityWitness_of_phase10_partition_output
      (L := L) (K := K) init final hphase hout

/-- Stable witness form for Phase-10 endpoints stated with the generic
partition output rather than the concrete `phase10MajorityWitness` predicate. -/
theorem stable_witness_of_phase10_partition_output
    (init c final : Config (AgentState L K))
    (hreach : (NonuniformMajority L K).Reachable c final)
    (hphase : ∀ a ∈ final, a.phase.val = 10)
    (hout : (doutPartition L K).output (majorityVerdict init) final) :
    ∃ o, (NonuniformMajority L K).Reachable c o ∧
      (doutPartition L K).output (majorityVerdict init) o ∧
      (NonuniformMajority L K).IsStable (doutPartition L K) o := by
  exact stable_witness_of_phase10MajorityWitness (L := L) (K := K) init c final hreach
    (phase10MajorityWitness_of_phase10_partition_output
      (L := L) (K := K) init final hphase hout)

/-- A Phase-10 endpoint whose `doutPartition` output is the initial majority
verdict is itself stable. -/
theorem phase10_partition_output_majority_isStable
    (init final : Config (AgentState L K))
    (hphase : ∀ a ∈ final, a.phase.val = 10)
    (hout : (doutPartition L K).output (majorityVerdict init) final) :
    (NonuniformMajority L K).IsStable (doutPartition L K) final := by
  have hwitness :=
    phase10MajorityWitness_of_phase10_partition_output
      (L := L) (K := K) init final hphase hout
  rcases hwitness with ⟨hgap, hfinal⟩ | ⟨hgap, hfinal⟩ | ⟨hgap, hfinal⟩
  · exact (phase10_unanimous_A_majority_witness_of_initialGap_pos
      (L := L) (K := K) init final hfinal hgap).2
  · exact (phase10_unanimous_B_majority_witness_of_initialGap_neg
      (L := L) (K := K) init final hfinal hgap).2
  · exact (phase10_unanimous_T_majority_witness_of_initialGap_zero
      (L := L) (K := K) init final hfinal hgap).2

/-- Direct stable-output package for a Phase-10 endpoint with the correct
partition output. -/
theorem stable_output_of_phase10_partition_output
    (init final : Config (AgentState L K))
    (hphase : ∀ a ∈ final, a.phase.val = 10)
    (hout : (doutPartition L K).output (majorityVerdict init) final) :
    (doutPartition L K).output (majorityVerdict init) final ∧
      (NonuniformMajority L K).IsStable (doutPartition L K) final :=
  ⟨hout, phase10_partition_output_majority_isStable
    (L := L) (K := K) init final hphase hout⟩

/-- Reduction from the remaining phase-reachability obligation to the generic
stable-computation statement.

This is not the Doty et al. theorem itself: the hypothesis is exactly the missing
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
    Protocol.StablyComputes (NonuniformMajority L K) (doutPartition L K)
      (validInitial) (majorityVerdict) := by
  intro init hinit c hc_reach
  obtain ⟨final, hfinal_reach, hwitness⟩ := hphase init hinit c hc_reach
  use final
  exact ⟨hfinal_reach, stable_output_of_phase10MajorityWitness init final hwitness⟩

/-- Variant of the correctness reduction for phase analyses that naturally
produce a Phase-10 endpoint plus the generic `doutPartition` output statement,
rather than the concrete A/B/T witness predicate. -/
theorem stable_majority_correct_of_phase10_partition_output_reachability
    (hphase :
      ∀ init : Config (AgentState L K), validInitial init →
        ∀ c : Config (AgentState L K),
          (NonuniformMajority L K).Reachable init c →
            ∃ final : Config (AgentState L K),
              (NonuniformMajority L K).Reachable c final ∧
                (∀ a ∈ final, a.phase.val = 10) ∧
                (doutPartition L K).output (majorityVerdict init) final) :
    Protocol.StablyComputes (NonuniformMajority L K) (doutPartition L K)
      (validInitial) (majorityVerdict) := by
  intro init hinit c hc_reach
  obtain ⟨final, hfinal_reach, hphase_final, hout⟩ := hphase init hinit c hc_reach
  use final
  exact ⟨hfinal_reach, stable_output_of_phase10_partition_output init final hphase_final hout⟩

def smallBiasSum (c : Config (AgentState L K)) : ℤ :=
  (c.map AgentState.smallBiasInt).sum

/-- The rational dyadic bias sum used in Doty et al.'s Phase-3/4 argument. -/
def dyadicBiasSum (c : Config (AgentState L K)) : ℚ :=
  (c.map (fun a => Bias.toRat a.bias)).sum

def prePhase4MassSum (c : Config (AgentState L K)) : ℚ :=
  (c.map prePhase4Mass).sum

theorem prePhase4MassSum_eq_smallBiasSum_of_phase_lt_three
    (c : Config (AgentState L K))
    (hphase : ∀ a ∈ c, a.phase.val < 3) :
    prePhase4MassSum c = (smallBiasSum c : ℚ) := by
  induction c using Multiset.induction_on with
  | empty =>
      simp [prePhase4MassSum, smallBiasSum]
  | cons a c ih =>
      have ha : a.phase.val < 3 := hphase a (Multiset.mem_cons_self a c)
      have htail : ∀ x ∈ c, x.phase.val < 3 := by
        intro x hx
        exact hphase x (Multiset.mem_cons_of_mem hx)
      simp [prePhase4MassSum, prePhase4Mass, smallBiasSum, ha]
      simpa [prePhase4MassSum, smallBiasSum] using ih htail

theorem prePhase4MassSum_eq_dyadicBiasSum_of_phase_ge_three
    (c : Config (AgentState L K))
    (hphase : ∀ a ∈ c, 3 ≤ a.phase.val) :
    prePhase4MassSum c = dyadicBiasSum c := by
  induction c using Multiset.induction_on with
  | empty =>
      simp [prePhase4MassSum, dyadicBiasSum]
  | cons a c ih =>
      have ha : ¬ a.phase.val < 3 := by
        have := hphase a (Multiset.mem_cons_self a c)
        omega
      have htail : ∀ x ∈ c, 3 ≤ x.phase.val := by
        intro x hx
        exact hphase x (Multiset.mem_cons_of_mem hx)
      simp [prePhase4MassSum, prePhase4Mass, dyadicBiasSum, ha]
      simpa [prePhase4MassSum, dyadicBiasSum] using ih htail

theorem smallBiasSum_pos_implies_exists_positive_smallBias
    (c : Config (AgentState L K)) (hsum : 0 < smallBiasSum c) :
    ∃ a ∈ c, 3 < a.smallBias.val := by
  induction c using Multiset.induction_on with
  | empty =>
      simp [smallBiasSum] at hsum
  | cons a c ih =>
      by_cases ha : 3 < a.smallBias.val
      · exact ⟨a, Multiset.mem_cons_self a c, ha⟩
      · have ha_nonpos : AgentState.smallBiasInt a ≤ 0 := by
          unfold AgentState.smallBiasInt
          omega
        have htail : 0 < smallBiasSum c := by
          simp [smallBiasSum, AgentState.smallBiasInt] at hsum ⊢
          omega
        rcases ih htail with ⟨b, hb, hbpos⟩
        exact ⟨b, Multiset.mem_cons_of_mem hb, hbpos⟩

theorem smallBiasSum_neg_implies_exists_negative_smallBias
    (c : Config (AgentState L K)) (hsum : smallBiasSum c < 0) :
    ∃ a ∈ c, a.smallBias.val < 3 := by
  induction c using Multiset.induction_on with
  | empty =>
      simp [smallBiasSum] at hsum
  | cons a c ih =>
      by_cases ha : a.smallBias.val < 3
      · exact ⟨a, Multiset.mem_cons_self a c, ha⟩
      · have ha_nonneg : 0 ≤ AgentState.smallBiasInt a := by
          unfold AgentState.smallBiasInt
          omega
        have htail : smallBiasSum c < 0 := by
          simp [smallBiasSum, AgentState.smallBiasInt] at hsum ⊢
          omega
        rcases ih htail with ⟨b, hb, hbneg⟩
        exact ⟨b, Multiset.mem_cons_of_mem hb, hbneg⟩

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
        Multiset.map_cons, Multiset.sum_cons, Multiset.filter_cons]
      cases h_in : a.input with
      | A =>
          have hsmall : a.smallBias = ⟨4, by decide⟩ := hA h_in
          simp [hsmall, smallBiasSum, initialGap, AgentState.smallBiasInt] at h_IH ⊢
          omega
      | B =>
          have hsmall : a.smallBias = ⟨2, by decide⟩ := hB h_in
          simp [hsmall, smallBiasSum, initialGap, AgentState.smallBiasInt] at h_IH ⊢
          omega

theorem validInitial_smallBiasSum_initialGap (c : Config (AgentState L K))
    (hvalid : validInitial c) :
    smallBiasSum c = initialGap c := by
  apply smallBiasSum_initialGap
  intro a ha
  rcases hvalid a ha with ⟨hphase, hrest⟩
  rcases hrest with ⟨_hrole, hrest⟩
  rcases hrest with ⟨_hassigned, hrest⟩
  rcases hrest with ⟨_hopinions, hrest⟩
  rcases hrest with ⟨hA, hB⟩
  exact ⟨hphase, ⟨hA, hB⟩⟩

lemma avgFin7_preserves_sum (x y : Fin 7) :
    ((avgFin7 x y).1.val : ℤ) + ((avgFin7 x y).2.val : ℤ) = (x.val : ℤ) + (y.val : ℤ) := by
  unfold avgFin7
  have h : (x.val + y.val) / 2 + (x.val + y.val + 1) / 2 = x.val + y.val := by omega
  push_cast
  omega

private lemma phaseEpidemicUpdate_smallBiasInt_eq (s t : AgentState L K) :
    AgentState.smallBiasInt s + AgentState.smallBiasInt t =
      AgentState.smallBiasInt (phaseEpidemicUpdate L K s t).1 +
        AgentState.smallBiasInt (phaseEpidemicUpdate L K s t).2 := by
  have h := phaseEpidemicUpdate_preserves_smallBias L K s t
  rcases h with ⟨h1, h2⟩
  simp [AgentState.smallBiasInt, h1, h2]

/-- Top-level phase-epidemic lower bound for the left output: after the full
transition, including the phase-specific dispatcher and Phase-10 entry wrapper,
the left output is at least the maximum of the two input phases. -/
theorem Transition_left_phase_ge_pair_max (s t : AgentState L K) :
    max s.phase.val t.phase.val ≤ (Transition L K s t).1.phase.val := by
  have h_ep := phaseEpidemicUpdate_left_phase_ge_max (L := L) (K := K) s t
  unfold Transition
  rcases hpe : phaseEpidemicUpdate L K s t with ⟨s', t'⟩
  simp only [hpe] at h_ep ⊢
  let out :=
    match s'.phase with
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
    | _ => (s', t')
  change max s.phase.val t.phase.val ≤ (finishPhase10Entry L K s' out.1).phase.val
  have hdispatch : s'.phase.val ≤ out.1.phase.val := by
    dsimp [out]
    rcases h_phase : s'.phase with ⟨n, hn⟩
    match n, hn with
    | 0, _ =>
      simpa [h_phase] using (Phase0Transition_phase_nondec L K s' t').1
    | 1, _ =>
      simpa [h_phase] using (Phase1Transition_phase_nondec L K s' t').1
    | 2, _ =>
      simpa [h_phase] using (Phase2Transition_phase_nondec L K s' t').1
    | 3, _ =>
      simpa [h_phase] using (Phase3Transition_phase_nondec L K s' t').1
    | 4, _ =>
      simpa [h_phase] using (Phase4Transition_phase_nondec L K s' t').1
    | 5, _ =>
      simpa [h_phase] using (Phase5Transition_phase_nondec L K s' t').1
    | 6, _ =>
      simpa [h_phase] using (Phase6Transition_phase_nondec L K s' t').1
    | 7, _ =>
      simpa [h_phase] using (Phase7Transition_phase_nondec L K s' t').1
    | 8, _ =>
      simpa [h_phase] using (Phase8Transition_phase_nondec L K s' t').1
    | 9, _ =>
      simpa [h_phase] using (Phase9Transition_phase_nondec L K s' t').1
    | 10, _ =>
      simpa [h_phase] using (Phase10Transition_phase_nondec L K s' t').1
    | n + 11, hn => omega
  exact le_trans h_ep (by simpa using hdispatch)

/-- Top-level phase-epidemic lower bound for the right output: after the full
transition, including the phase-specific dispatcher and Phase-10 entry wrapper,
the right output is at least the maximum of the two input phases. -/
theorem Transition_right_phase_ge_pair_max (s t : AgentState L K) :
    max s.phase.val t.phase.val ≤ (Transition L K s t).2.phase.val := by
  have h_ep := phaseEpidemicUpdate_right_phase_ge_max (L := L) (K := K) s t
  unfold Transition
  rcases hpe : phaseEpidemicUpdate L K s t with ⟨s', t'⟩
  simp only [hpe] at h_ep ⊢
  let out :=
    match s'.phase with
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
    | _ => (s', t')
  change max s.phase.val t.phase.val ≤ (finishPhase10Entry L K t' out.2).phase.val
  have hdispatch : t'.phase.val ≤ out.2.phase.val := by
    dsimp [out]
    rcases h_phase : s'.phase with ⟨n, hn⟩
    match n, hn with
    | 0, _ =>
      simpa [h_phase] using (Phase0Transition_phase_nondec L K s' t').2
    | 1, _ =>
      simpa [h_phase] using (Phase1Transition_phase_nondec L K s' t').2
    | 2, _ =>
      simpa [h_phase] using (Phase2Transition_phase_nondec L K s' t').2
    | 3, _ =>
      simpa [h_phase] using (Phase3Transition_phase_nondec L K s' t').2
    | 4, _ =>
      simpa [h_phase] using (Phase4Transition_phase_nondec L K s' t').2
    | 5, _ =>
      simpa [h_phase] using (Phase5Transition_phase_nondec L K s' t').2
    | 6, _ =>
      simpa [h_phase] using (Phase6Transition_phase_nondec L K s' t').2
    | 7, _ =>
      simpa [h_phase] using (Phase7Transition_phase_nondec L K s' t').2
    | 8, _ =>
      simpa [h_phase] using (Phase8Transition_phase_nondec L K s' t').2
    | 9, _ =>
      simpa [h_phase] using (Phase9Transition_phase_nondec L K s' t').2
    | 10, _ =>
      simpa [h_phase] using (Phase10Transition_phase_nondec L K s' t').2
    | n + 11, hn => omega
  exact le_trans h_ep (by simpa using hdispatch)

private lemma phaseEpidemicUpdate_eq_of_max_phase_zero (s t : AgentState L K)
    (hmax0 : max s.phase.val t.phase.val = 0) :
    phaseEpidemicUpdate L K s t = (s, t) := by
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
    simp [runInitsBetween_self, hs0, ht0]
  · rw [hp_t]
    simp [runInitsBetween_self, hs0, ht0]

private lemma phaseEpidemicUpdate_eq_of_left_phase_zero (s t : AgentState L K)
    (hzero : (phaseEpidemicUpdate L K s t).1.phase.val = 0) :
    phaseEpidemicUpdate L K s t = (s, t) := by
  have hmax0 : max s.phase.val t.phase.val = 0 := by
    have hle := phaseEpidemicUpdate_left_phase_ge_max (L := L) (K := K) s t
    omega
  exact phaseEpidemicUpdate_eq_of_max_phase_zero (L := L) (K := K) s t hmax0

set_option linter.flexible false in
private theorem phaseEpidemicUpdate_right_phase_pos_of_left_phase_pos
    (s t : AgentState L K)
    (hleft : 1 ≤ (phaseEpidemicUpdate L K s t).1.phase.val) :
    1 ≤ (phaseEpidemicUpdate L K s t).2.phase.val := by
  have hmax_left := phaseEpidemicUpdate_left_phase_ge_max (L := L) (K := K) s t
  have hmax_right := phaseEpidemicUpdate_right_phase_ge_max (L := L) (K := K) s t
  by_cases hmax0 : max s.phase.val t.phase.val = 0
  · have hep_eq := phaseEpidemicUpdate_eq_of_max_phase_zero (L := L) (K := K) s t hmax0
    have hleft0 : (phaseEpidemicUpdate L K s t).1.phase.val = 0 := by
      have hs0 : s.phase.val = 0 := by
        have hle : s.phase.val ≤ max s.phase.val t.phase.val := Nat.le_max_left _ _
        omega
      simpa [hep_eq, hs0]
    omega
  · have hmax_pos : 1 ≤ max s.phase.val t.phase.val :=
      Nat.succ_le_of_lt (Nat.pos_of_ne_zero hmax0)
    exact le_trans hmax_pos hmax_right

lemma addSmallBias_smallBiasInt (x y : Fin 7) :
    (addSmallBias x y).val - 3 =
      max (-3 : ℤ) (min (3 : ℤ) ((x.val : ℤ) - 3 + ((y.val : ℤ) - 3))) := by
  fin_cases x <;> fin_cases y <;> decide

lemma addSmallBias_no_clamp (x y : Fin 7)
    (h : (((x.val : ℤ) - 3) + ((y.val : ℤ) - 3)).natAbs ≤ 3) :
    (addSmallBias x y).val - 3 = (x.val : ℤ) - 3 + ((y.val : ℤ) - 3) := by
  rw [addSmallBias_smallBiasInt]
  have h_range :
      -3 ≤ (x.val : ℤ) - 3 + ((y.val : ℤ) - 3) ∧
        (x.val : ℤ) - 3 + ((y.val : ℤ) - 3) ≤ 3 := by
    omega
  rcases h_range with ⟨hneg, hpos⟩
  omega

private lemma smallBias_pair_bound_of_mcr_mcr (s t : AgentState L K)
    (hs_phase : s.phase.val = 0) (ht_phase : t.phase.val = 0)
    (hsq : WellFormedAgentQuota s) (htq : WellFormedAgentQuota t)
    (hs_role : s.role = .mcr) (ht_role : t.role = .mcr) :
    (AgentState.smallBiasInt s + AgentState.smallBiasInt t).natAbs ≤ 3 := by
  have hs_abs : (AgentState.smallBiasInt s).natAbs ≤ 1 := (hsq hs_phase).1 hs_role
  have ht_abs : (AgentState.smallBiasInt t).natAbs ≤ 1 := (htq ht_phase).1 ht_role
  omega

private lemma smallBias_pair_bound_of_mcr_main (s t : AgentState L K)
    (hs_phase : s.phase.val = 0) (ht_phase : t.phase.val = 0)
    (hsq : WellFormedAgentQuota s) (htq : WellFormedAgentQuota t)
    (hs_role : s.role = .mcr) (ht_role : t.role = .main)
    (ht_unassigned : t.assigned = false) :
    (AgentState.smallBiasInt s + AgentState.smallBiasInt t).natAbs ≤ 3 := by
  have hs_abs : (AgentState.smallBiasInt s).natAbs ≤ 1 := (hsq hs_phase).1 hs_role
  have ht_abs : (AgentState.smallBiasInt t).natAbs ≤ 2 :=
    (htq ht_phase).2 ht_role ht_unassigned
  omega

private lemma smallBias_pair_bound_of_main_mcr (s t : AgentState L K)
    (hs_phase : s.phase.val = 0) (ht_phase : t.phase.val = 0)
    (hsq : WellFormedAgentQuota s) (htq : WellFormedAgentQuota t)
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
      AgentState.smallBiasInt (Phase0Transition L K s t).1 +
        AgentState.smallBiasInt (Phase0Transition L K s t).2 := by
  let s1 := if s.role = .mcr ∧ t.role = .mcr then
    { s with role := .main, smallBias := addSmallBias s.smallBias t.smallBias } else s
  let t1 := if s.role = .mcr ∧ t.role = .mcr then
    { t with role := .cr, smallBias := ⟨3, by decide⟩ } else t
  have hsum_conv : (((s.smallBias.val : ℤ) - 3) + ((t.smallBias.val : ℤ) - 3)).natAbs ≤ 3 := by
    simpa [AgentState.smallBiasInt] using hsum
  have h1 :
      AgentState.smallBiasInt s + AgentState.smallBiasInt t =
        AgentState.smallBiasInt s1 + AgentState.smallBiasInt t1 := by
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
  have h2 :
      AgentState.smallBiasInt s1 + AgentState.smallBiasInt t1 =
        AgentState.smallBiasInt s2 + AgentState.smallBiasInt t2 := by
    by_cases h : s1.role = .mcr ∧ t1.role = .main ∧ ¬ t1.assigned
    · rcases h with ⟨hs_role, ht_role, ht_not⟩
      simp [hs_role, ht_role, ht_not, AgentState.smallBiasInt, s2, t2,
        addSmallBias_no_clamp s1.smallBias t1.smallBias hsum1_conv]
    · by_cases h' : t1.role = .mcr ∧ s1.role = .main ∧ ¬ s1.assigned
      · rcases h' with ⟨ht_role, hs_role, hs_not⟩
        simp [ht_role, hs_role, hs_not, AgentState.smallBiasInt, s2, t2,
          addSmallBias_no_clamp t1.smallBias s1.smallBias hsum1_conv', add_comm]
      · have hs2 : s2 = s1 := by
          dsimp [s2]; rw [if_neg h, if_neg h']
        have ht2 : t2 = t1 := by
          dsimp [t2]; rw [if_neg h, if_neg h']
        simp [hs2, ht2, AgentState.smallBiasInt]
  let s3 := if s2.role = .mcr ∧ t2.role ≠ .main ∧ t2.role ≠ .mcr ∧ ¬ t2.assigned then
              { s2 with role := .main }
            else if t2.role = .mcr ∧ s2.role ≠ .main ∧ s2.role ≠ .mcr ∧ ¬ s2.assigned then
              { s2 with assigned := true }
            else s2
  let t3 := if s2.role = .mcr ∧ t2.role ≠ .main ∧ t2.role ≠ .mcr ∧ ¬ t2.assigned then
              { t2 with assigned := true }
            else if t2.role = .mcr ∧ s2.role ≠ .main ∧ s2.role ≠ .mcr ∧ ¬ s2.assigned then
              { t2 with role := .main }
            else t2
  have h3 :
      AgentState.smallBiasInt s2 + AgentState.smallBiasInt t2 =
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
  let s3' := s3
  let t3' := t3
  have h3' :
      AgentState.smallBiasInt s3 + AgentState.smallBiasInt t3 =
        AgentState.smallBiasInt s3' + AgentState.smallBiasInt t3' := by
    simp [s3', t3']
  let s4 := if s3'.role = .cr ∧ t3'.role = .cr then
              { s3' with role := .clock, counter := ⟨50 * (L + 1), by omega⟩ } else s3'
  let t4 := if s3'.role = .cr ∧ t3'.role = .cr then
              { t3' with role := .reserve } else t3'
  have h4 :
      AgentState.smallBiasInt s3' + AgentState.smallBiasInt t3' =
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
  have h5 :
      AgentState.smallBiasInt s4 + AgentState.smallBiasInt t4 =
        AgentState.smallBiasInt s5 + AgentState.smallBiasInt t5 := by
    by_cases h : s4.role = .clock ∧ t4.role = .clock
    · rcases h with ⟨hs, ht⟩
      have hs5 : s5 = stdCounterSubroutine L K s4 := by
        dsimp [s5]; rw [if_pos ⟨hs, ht⟩]
      have ht5 : t5 = stdCounterSubroutine L K t4 := by
        dsimp [t5]; rw [if_pos ⟨hs, ht⟩]
      simp [hs5, ht5, AgentState.smallBiasInt, stdCounterSubroutine_smallBias]
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
    (hsq : WellFormedAgentQuota s) (htq : WellFormedAgentQuota t) :
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
              have hsum1' :
                  (AgentState.smallBiasInt s1 + AgentState.smallBiasInt t1).natAbs ≤ 3 := by
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
          add_comm]
      · have hs2 : s2 = s1 := by
          dsimp [s2]; rw [if_neg h, if_neg h']
        have ht2 : t2 = t1 := by
          dsimp [t2]; rw [if_neg h, if_neg h']
        simp [hs2, ht2, AgentState.smallBiasInt]
  let s3 := if s2.role = .mcr ∧ t2.role ≠ .main ∧ t2.role ≠ .mcr ∧ ¬ t2.assigned then
              { s2 with role := .main }
            else if t2.role = .mcr ∧ s2.role ≠ .main ∧ s2.role ≠ .mcr ∧ ¬ s2.assigned then
              { s2 with assigned := true }
            else s2
  let t3 := if s2.role = .mcr ∧ t2.role ≠ .main ∧ t2.role ≠ .mcr ∧ ¬ t2.assigned then
              { t2 with assigned := true }
            else if t2.role = .mcr ∧ s2.role ≠ .main ∧ s2.role ≠ .mcr ∧ ¬ s2.assigned then
              { t2 with role := .main }
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
  let s3' := s3
  let t3' := t3
  have h3' : AgentState.smallBiasInt s3 + AgentState.smallBiasInt t3 =
      AgentState.smallBiasInt s3' + AgentState.smallBiasInt t3' := by
    simp [s3', t3']
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
      simp [hs5, ht5, AgentState.smallBiasInt, stdCounterSubroutine_smallBias]
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

set_option linter.flexible false in
private theorem Phase0Transition_preserves_well_formed_agent_quota (s t : AgentState L K)
    (hs_phase : s.phase.val = 0) (ht_phase : t.phase.val = 0) :
    WellFormedAgentQuota s → WellFormedAgentQuota t →
    WellFormedAgentQuota (Phase0Transition L K s t).1 ∧
    WellFormedAgentQuota (Phase0Transition L K s t).2 := by
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
          simp [s2, ht_role, hs_role, hs_unassigned] at hrole
        · intro _hmain hassigned
          simp [s2, ht_role, hs_role, hs_unassigned] at hassigned
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
          simp [t2, ht_role, hs_role, hs_unassigned] at hrole
        · intro hmain
          simp [t2, ht_role, hs_role, hs_unassigned] at hmain
      · have ht2eq : t2 = t1 := by
          dsimp [t2]; rw [if_neg h, if_neg h']
        simpa [ht2eq] using ht1
  let s3 := if s2.role = .mcr ∧ t2.role ≠ .main ∧ t2.role ≠ .mcr ∧ ¬ t2.assigned then
              { s2 with role := .main }
            else if t2.role = .mcr ∧ s2.role ≠ .main ∧ s2.role ≠ .mcr ∧ ¬ s2.assigned then
              { s2 with assigned := true }
            else s2
  let t3 := if s2.role = .mcr ∧ t2.role ≠ .main ∧ t2.role ≠ .mcr ∧ ¬ t2.assigned then
              { t2 with assigned := true }
            else if t2.role = .mcr ∧ s2.role ≠ .main ∧ s2.role ≠ .mcr ∧ ¬ s2.assigned then
              { t2 with role := .main }
            else t2
  -- With the paper-faithful Rule 3, the fresh Main keeps `assigned = s2.assigned`
  -- (no longer forced to `true`).  In the fresh-Main branch `s2.role = .mcr`, so the
  -- MCR-quota half of `hs2` gives `|smallBiasInt| ≤ 1 ≤ 2`, discharging the new
  -- `main ∧ ¬assigned → ≤ 2` obligation.  (Bias is unchanged by the role flip.)
  have hs3 : smallBiasQuotaFields s3 := by
    by_cases h : s2.role = .mcr ∧ t2.role ≠ .main ∧ t2.role ≠ .mcr ∧ ¬ t2.assigned
    · rcases h with ⟨hs2_role, _, _, _⟩
      have hbound : (AgentState.smallBiasInt s2).natAbs ≤ 1 := hs2.1 hs2_role
      have hs3eq : s3 = { s2 with role := .main } := by
        dsimp [s3]; rw [if_pos ⟨hs2_role, by tauto⟩]
      refine ⟨?_, ?_⟩
      · intro hrole; rw [hs3eq] at hrole; simp at hrole
      · intro _ _
        have : AgentState.smallBiasInt ({ s2 with role := .main } : AgentState L K)
            = AgentState.smallBiasInt s2 := by simp [AgentState.smallBiasInt]
        rw [hs3eq, this]; omega
    · by_cases h' : t2.role = .mcr ∧ s2.role ≠ .main ∧ s2.role ≠ .mcr ∧ ¬ s2.assigned
      · have hs3eq : s3 = { s2 with assigned := true } := by
          dsimp [s3]; rw [if_neg h, if_pos h']
        rw [hs3eq]
        refine ⟨?_, ?_⟩
        · intro hrole
          have : AgentState.smallBiasInt ({ s2 with assigned := true } : AgentState L K)
              = AgentState.smallBiasInt s2 := by simp [AgentState.smallBiasInt]
          rw [this]; exact hs2.1 (by simpa using hrole)
        · intro hmain hassigned; simp at hassigned
      · have hs3eq : s3 = s2 := by dsimp [s3]; rw [if_neg h, if_neg h']
        rw [hs3eq]; exact hs2
  have ht3 : smallBiasQuotaFields t3 := by
    by_cases h : s2.role = .mcr ∧ t2.role ≠ .main ∧ t2.role ≠ .mcr ∧ ¬ t2.assigned
    · have ht3eq : t3 = { t2 with assigned := true } := by
        dsimp [t3]; rw [if_pos h]
      rw [ht3eq]
      refine ⟨?_, ?_⟩
      · intro hrole
        have : AgentState.smallBiasInt ({ t2 with assigned := true } : AgentState L K)
            = AgentState.smallBiasInt t2 := by simp [AgentState.smallBiasInt]
        rw [this]; exact ht2.1 (by simpa using hrole)
      · intro hmain hassigned; simp at hassigned
    · by_cases h' : t2.role = .mcr ∧ s2.role ≠ .main ∧ s2.role ≠ .mcr ∧ ¬ s2.assigned
      · rcases h' with ⟨ht2_role, _, _, _⟩
        have hbound : (AgentState.smallBiasInt t2).natAbs ≤ 1 := ht2.1 ht2_role
        have ht3eq : t3 = { t2 with role := .main } := by
          dsimp [t3]; rw [if_neg h, if_pos ⟨ht2_role, by tauto⟩]
        refine ⟨?_, ?_⟩
        · intro hrole; rw [ht3eq] at hrole; simp at hrole
        · intro _ _
          have : AgentState.smallBiasInt ({ t2 with role := .main } : AgentState L K)
              = AgentState.smallBiasInt t2 := by simp [AgentState.smallBiasInt]
          rw [ht3eq, this]; omega
      · have ht3eq : t3 = t2 := by dsimp [t3]; rw [if_neg h, if_neg h']
        rw [ht3eq]; exact ht2
  let s3' := s3
  let t3' := t3
  have hs3' : smallBiasQuotaFields s3' := hs3
  have ht3' : smallBiasQuotaFields t3' := ht3
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
      have hrole : (stdCounterSubroutine L K s4).role = .clock :=
        stdCounterSubroutine_clock_role_eq L K s4 hsclock
      simp [smallBiasQuotaFields, hrole]
    · have hs5eq : s5 = s4 := by
        dsimp [s5]; rw [if_neg hclock]
      simpa [hs5eq] using hs4
  have ht5 : smallBiasQuotaFields t5 := by
    by_cases hclock : s4.role = .clock ∧ t4.role = .clock
    · rcases hclock with ⟨hsclock, htclock⟩
      have ht5eq : t5 = stdCounterSubroutine L K t4 := by
        dsimp [t5]; rw [if_pos ⟨hsclock, htclock⟩]
      rw [ht5eq]
      have hrole : (stdCounterSubroutine L K t4).role = .clock :=
        stdCounterSubroutine_clock_role_eq L K t4 htclock
      simp [smallBiasQuotaFields, hrole]
    · have ht5eq : t5 = t4 := by
        dsimp [t5]; rw [if_neg hclock]
      simpa [ht5eq] using ht4
  constructor
  · intro _hphase
    exact hs5
  · intro _hphase
    exact ht5

set_option linter.flexible false in
private lemma Phase1Transition_preserves_sum (s t : AgentState L K) :
    AgentState.smallBiasInt s + AgentState.smallBiasInt t =
      AgentState.smallBiasInt (Phase1Transition L K s t).1 +
        AgentState.smallBiasInt (Phase1Transition L K s t).2 := by
  by_cases hmain : s.role = .main ∧ t.role = .main
  · simp [AgentState.smallBiasInt, Phase1Transition, hmain, clockCounterStep,
      hmain.1, hmain.2]
    push_cast
    linarith [avgFin7_preserves_sum s.smallBias t.smallBias]
  · by_cases hsclock : s.role = .clock
    · by_cases htclock : t.role = .clock
      · simp [AgentState.smallBiasInt, Phase1Transition, hmain, clockCounterStep,
          hsclock, htclock, stdCounterSubroutine_smallBias]
      · simp [AgentState.smallBiasInt, Phase1Transition, hmain, clockCounterStep,
          hsclock, htclock, stdCounterSubroutine_smallBias]
    · by_cases htclock : t.role = .clock
      · simp [AgentState.smallBiasInt, Phase1Transition, hmain, clockCounterStep,
          hsclock, htclock, stdCounterSubroutine_smallBias]
      · simp [AgentState.smallBiasInt, Phase1Transition, hmain, clockCounterStep,
          hsclock, htclock]

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
    let hVal := max s1.hour.val (min L (t1.minute.val / K))
    have h_hour_lt : hVal < L + 1 := by
      exact (Nat.max_lt).mpr ⟨s1.hour.2, Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩
    { s1 with hour := ⟨hVal, h_hour_lt⟩ }
  else if t1.role = .main ∧ t1.bias = .zero ∧ s1.role = .clock then
    s1
  else s1
  let t2 := if s1.role = .main ∧ s1.bias = .zero ∧ t1.role = .clock then
    t1
  else if t1.role = .main ∧ t1.bias = .zero ∧ s1.role = .clock then
    let hVal := max t1.hour.val (min L (s1.minute.val / K))
    have h_hour_lt : hVal < L + 1 := by
      exact (Nat.max_lt).mpr ⟨t1.hour.2, Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩
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
      AgentState.smallBiasInt ((Transition L K s t).1) +
        AgentState.smallBiasInt ((Transition L K s t).2) := by
  have hep_sum := phaseEpidemicUpdate_smallBiasInt_eq (L := L) (K := K) s t
  unfold Transition
  rcases hpe : phaseEpidemicUpdate L K s t with ⟨s', t'⟩
  simp only [hpe] at hep_sum ⊢
  have hsum_ep : (AgentState.smallBiasInt s' + AgentState.smallBiasInt t').natAbs ≤ 3 := by
    rw [← hep_sum]
    exact hsum
  let out :=
    match s'.phase with
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
    | _ => (s', t')
  change AgentState.smallBiasInt s + AgentState.smallBiasInt t =
    AgentState.smallBiasInt (finishPhase10Entry L K s' out.1) +
    AgentState.smallBiasInt (finishPhase10Entry L K t' out.2)
  rw [hep_sum]
  dsimp [out]
  rcases h_phase : s'.phase with ⟨n, hn⟩
  match n, hn with
  | 0, _ => simpa using Phase0Transition_preserves_sum (L := L) (K := K) s' t' hsum_ep
  | 1, _ => simpa using Phase1Transition_preserves_sum (L := L) (K := K) s' t'
  | 2, _ => simpa using Phase2Transition_preserves_sum (L := L) (K := K) s' t'
  | 3, _ => simpa using Phase3Transition_preserves_sum (L := L) (K := K) s' t'
  | 4, _ => simpa using Phase4Transition_preserves_sum (L := L) (K := K) s' t'
  | 5, _ => simpa using Phase5Transition_preserves_sum (L := L) (K := K) s' t'
  | 6, _ => simpa using Phase6Transition_preserves_sum (L := L) (K := K) s' t'
  | 7, _ => simpa using Phase7Transition_preserves_sum (L := L) (K := K) s' t'
  | 8, _ => simpa using Phase8Transition_preserves_sum (L := L) (K := K) s' t'
  | 9, _ => simpa using Phase9Transition_preserves_sum (L := L) (K := K) s' t'
  | 10, _ => simpa using Phase10Transition_preserves_sum (L := L) (K := K) s' t'
  | n + 11, hn => omega

theorem smallBiasSum_step_invariant_of_quota (s t : AgentState L K)
    (hsq : WellFormedAgentQuota s) (htq : WellFormedAgentQuota t) :
    AgentState.smallBiasInt s + AgentState.smallBiasInt t =
      AgentState.smallBiasInt ((Transition L K s t).1) +
      AgentState.smallBiasInt ((Transition L K s t).2) := by
  have hep_sum := phaseEpidemicUpdate_smallBiasInt_eq (L := L) (K := K) s t
  unfold Transition
  rcases hpe : phaseEpidemicUpdate L K s t with ⟨s', t'⟩
  simp only [hpe] at hep_sum ⊢
  let out :=
    match s'.phase with
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
    | _ => (s', t')
  change AgentState.smallBiasInt s + AgentState.smallBiasInt t =
    AgentState.smallBiasInt (finishPhase10Entry L K s' out.1) +
    AgentState.smallBiasInt (finishPhase10Entry L K t' out.2)
  rw [hep_sum]
  dsimp [out]
  rcases h_phase : s'.phase with ⟨n, hn⟩
  match n, hn with
  | 0, _ =>
    have hs'_zero : s'.phase.val = 0 := by simp [h_phase]
    have hep_eq : phaseEpidemicUpdate L K s t = (s, t) :=
      phaseEpidemicUpdate_eq_of_left_phase_zero (L := L) (K := K) s t
        (by simpa [hpe] using hs'_zero)
    have hs'_eq : s' = s := by
      simpa [hpe] using congrArg Prod.fst hep_eq
    have ht'_eq : t' = t := by
      simpa [hpe] using congrArg Prod.snd hep_eq
    rw [hs'_eq, ht'_eq]
    have ht_zero : t.phase.val = 0 := by
      have hmax : max s.phase.val t.phase.val = 0 := by
        have hle := phaseEpidemicUpdate_left_phase_ge_max (L := L) (K := K) s t
        have hle0 : max s.phase.val t.phase.val ≤ 0 := by
          simpa [hpe, hs'_zero] using hle
        omega
      have hle : t.phase.val ≤ max s.phase.val t.phase.val := Nat.le_max_right _ _
      omega
    simpa using
      Phase0Transition_preserves_sum_of_quota (L := L) (K := K) s t
        (by simpa [hs'_eq] using hs'_zero) ht_zero hsq htq
  | 1, _ => simpa using Phase1Transition_preserves_sum (L := L) (K := K) s' t'
  | 2, _ => simpa using Phase2Transition_preserves_sum (L := L) (K := K) s' t'
  | 3, _ => simpa using Phase3Transition_preserves_sum (L := L) (K := K) s' t'
  | 4, _ => simpa using Phase4Transition_preserves_sum (L := L) (K := K) s' t'
  | 5, _ => simpa using Phase5Transition_preserves_sum (L := L) (K := K) s' t'
  | 6, _ => simpa using Phase6Transition_preserves_sum (L := L) (K := K) s' t'
  | 7, _ => simpa using Phase7Transition_preserves_sum (L := L) (K := K) s' t'
  | 8, _ => simpa using Phase8Transition_preserves_sum (L := L) (K := K) s' t'
  | 9, _ => simpa using Phase9Transition_preserves_sum (L := L) (K := K) s' t'
  | 10, _ => simpa using Phase10Transition_preserves_sum (L := L) (K := K) s' t'
  | n + 11, hn => omega

private lemma well_formed_agent_quota_of_phase_pos (a : AgentState L K)
    (hpos : 1 ≤ a.phase.val) : WellFormedAgentQuota a := by
  intro hzero
  omega

private theorem Transition_preserves_well_formed_agent_quota (s t : AgentState L K) :
    WellFormedAgentQuota s → WellFormedAgentQuota t →
    WellFormedAgentQuota (Transition L K s t).1 ∧
    WellFormedAgentQuota (Transition L K s t).2 := by
  intro hsq htq
  unfold Transition
  simp only [finishPhase10Entry_well_formed_agent_quota_iff]
  let s' := (phaseEpidemicUpdate L K s t).1
  let t' := (phaseEpidemicUpdate L K s t).2
  change WellFormedAgentQuota (match s'.phase with
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
    WellFormedAgentQuota (match s'.phase with
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
    have hs'_zero : s'.phase.val = 0 := by simp [h_phase]
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
      phaseEpidemicUpdate_right_phase_pos_of_left_phase_pos (L := L) (K := K)
        s t (by simp [s', h_phase])
    have hspos0 : 1 ≤ s'.phase.val := by simp [h_phase]
    have hspos : 1 ≤ (Phase1Transition L K s' t').1.phase.val := le_trans hspos0 hsmono
    have htpos_out : 1 ≤ (Phase1Transition L K s' t').2.phase.val := le_trans htpos htmono
    exact ⟨by simpa using well_formed_agent_quota_of_phase_pos (Phase1Transition L K s' t').1 hspos,
      by simpa using well_formed_agent_quota_of_phase_pos (Phase1Transition L K s' t').2 htpos_out⟩
  | 2, _ =>
    rcases Phase2Transition_phase_nondec L K s' t' with ⟨hsmono, htmono⟩
    have htpos : 1 ≤ t'.phase.val :=
      phaseEpidemicUpdate_right_phase_pos_of_left_phase_pos (L := L) (K := K)
        s t (by simp [s', h_phase])
    have hspos0 : 1 ≤ s'.phase.val := by simp [h_phase]
    have hspos : 1 ≤ (Phase2Transition L K s' t').1.phase.val := le_trans hspos0 hsmono
    have htpos_out : 1 ≤ (Phase2Transition L K s' t').2.phase.val := le_trans htpos htmono
    exact ⟨by simpa using well_formed_agent_quota_of_phase_pos (Phase2Transition L K s' t').1 hspos,
      by simpa using well_formed_agent_quota_of_phase_pos (Phase2Transition L K s' t').2 htpos_out⟩
  | 3, _ =>
    rcases Phase3Transition_phase_nondec L K s' t' with ⟨hsmono, htmono⟩
    have htpos : 1 ≤ t'.phase.val :=
      phaseEpidemicUpdate_right_phase_pos_of_left_phase_pos (L := L) (K := K)
        s t (by simp [s', h_phase])
    have hspos0 : 1 ≤ s'.phase.val := by simp [h_phase]
    have hspos : 1 ≤ (Phase3Transition L K s' t').1.phase.val := le_trans hspos0 hsmono
    have htpos_out : 1 ≤ (Phase3Transition L K s' t').2.phase.val := le_trans htpos htmono
    exact ⟨by simpa using well_formed_agent_quota_of_phase_pos (Phase3Transition L K s' t').1 hspos,
      by simpa using well_formed_agent_quota_of_phase_pos (Phase3Transition L K s' t').2 htpos_out⟩
  | 4, _ =>
    rcases Phase4Transition_phase_nondec L K s' t' with ⟨hsmono, htmono⟩
    have htpos : 1 ≤ t'.phase.val :=
      phaseEpidemicUpdate_right_phase_pos_of_left_phase_pos (L := L) (K := K)
        s t (by simp [s', h_phase])
    have hspos0 : 1 ≤ s'.phase.val := by simp [h_phase]
    have hspos : 1 ≤ (Phase4Transition L K s' t').1.phase.val := le_trans hspos0 hsmono
    have htpos_out : 1 ≤ (Phase4Transition L K s' t').2.phase.val := le_trans htpos htmono
    exact ⟨by simpa using well_formed_agent_quota_of_phase_pos (Phase4Transition L K s' t').1 hspos,
      by simpa using well_formed_agent_quota_of_phase_pos (Phase4Transition L K s' t').2 htpos_out⟩
  | 5, _ =>
    rcases Phase5Transition_phase_nondec L K s' t' with ⟨hsmono, htmono⟩
    have htpos : 1 ≤ t'.phase.val :=
      phaseEpidemicUpdate_right_phase_pos_of_left_phase_pos (L := L) (K := K)
        s t (by simp [s', h_phase])
    have hspos0 : 1 ≤ s'.phase.val := by simp [h_phase]
    have hspos : 1 ≤ (Phase5Transition L K s' t').1.phase.val := le_trans hspos0 hsmono
    have htpos_out : 1 ≤ (Phase5Transition L K s' t').2.phase.val := le_trans htpos htmono
    exact ⟨by simpa using well_formed_agent_quota_of_phase_pos (Phase5Transition L K s' t').1 hspos,
      by simpa using well_formed_agent_quota_of_phase_pos (Phase5Transition L K s' t').2 htpos_out⟩
  | 6, _ =>
    rcases Phase6Transition_phase_nondec L K s' t' with ⟨hsmono, htmono⟩
    have htpos : 1 ≤ t'.phase.val :=
      phaseEpidemicUpdate_right_phase_pos_of_left_phase_pos (L := L) (K := K)
        s t (by simp [s', h_phase])
    have hspos0 : 1 ≤ s'.phase.val := by simp [h_phase]
    have hspos : 1 ≤ (Phase6Transition L K s' t').1.phase.val := le_trans hspos0 hsmono
    have htpos_out : 1 ≤ (Phase6Transition L K s' t').2.phase.val := le_trans htpos htmono
    exact ⟨by simpa using well_formed_agent_quota_of_phase_pos (Phase6Transition L K s' t').1 hspos,
      by simpa using well_formed_agent_quota_of_phase_pos (Phase6Transition L K s' t').2 htpos_out⟩
  | 7, _ =>
    rcases Phase7Transition_phase_nondec L K s' t' with ⟨hsmono, htmono⟩
    have htpos : 1 ≤ t'.phase.val :=
      phaseEpidemicUpdate_right_phase_pos_of_left_phase_pos (L := L) (K := K)
        s t (by simp [s', h_phase])
    have hspos0 : 1 ≤ s'.phase.val := by simp [h_phase]
    have hspos : 1 ≤ (Phase7Transition L K s' t').1.phase.val := le_trans hspos0 hsmono
    have htpos_out : 1 ≤ (Phase7Transition L K s' t').2.phase.val := le_trans htpos htmono
    exact ⟨by simpa using well_formed_agent_quota_of_phase_pos (Phase7Transition L K s' t').1 hspos,
      by simpa using well_formed_agent_quota_of_phase_pos (Phase7Transition L K s' t').2 htpos_out⟩
  | 8, _ =>
    rcases Phase8Transition_phase_nondec L K s' t' with ⟨hsmono, htmono⟩
    have htpos : 1 ≤ t'.phase.val :=
      phaseEpidemicUpdate_right_phase_pos_of_left_phase_pos (L := L) (K := K)
        s t (by simp [s', h_phase])
    have hspos0 : 1 ≤ s'.phase.val := by simp [h_phase]
    have hspos : 1 ≤ (Phase8Transition L K s' t').1.phase.val := le_trans hspos0 hsmono
    have htpos_out : 1 ≤ (Phase8Transition L K s' t').2.phase.val := le_trans htpos htmono
    exact ⟨by simpa using well_formed_agent_quota_of_phase_pos (Phase8Transition L K s' t').1 hspos,
      by simpa using well_formed_agent_quota_of_phase_pos (Phase8Transition L K s' t').2 htpos_out⟩
  | 9, _ =>
    rcases Phase9Transition_phase_nondec L K s' t' with ⟨hsmono, htmono⟩
    have htpos : 1 ≤ t'.phase.val :=
      phaseEpidemicUpdate_right_phase_pos_of_left_phase_pos (L := L) (K := K)
        s t (by simp [s', h_phase])
    have hspos0 : 1 ≤ s'.phase.val := by simp [h_phase]
    have hspos : 1 ≤ (Phase9Transition L K s' t').1.phase.val := le_trans hspos0 hsmono
    have htpos_out : 1 ≤ (Phase9Transition L K s' t').2.phase.val := le_trans htpos htmono
    exact ⟨by simpa using well_formed_agent_quota_of_phase_pos (Phase9Transition L K s' t').1 hspos,
      by simpa using well_formed_agent_quota_of_phase_pos (Phase9Transition L K s' t').2 htpos_out⟩
  | 10, _ =>
    rcases Phase10Transition_phase_nondec L K s' t' with ⟨hsmono, htmono⟩
    have htpos : 1 ≤ t'.phase.val :=
      phaseEpidemicUpdate_right_phase_pos_of_left_phase_pos (L := L) (K := K)
        s t (by simp [s', h_phase])
    have hspos0 : 1 ≤ s'.phase.val := by simp [h_phase]
    have hspos : 1 ≤ (Phase10Transition L K s' t').1.phase.val := le_trans hspos0 hsmono
    have htpos_out : 1 ≤ (Phase10Transition L K s' t').2.phase.val := le_trans htpos htmono
    exact ⟨by simpa using
        well_formed_agent_quota_of_phase_pos (Phase10Transition L K s' t').1 hspos,
      by simpa using well_formed_agent_quota_of_phase_pos (Phase10Transition L K s' t').2 htpos_out⟩
  | n + 11, hn => omega

private theorem validInitial_well_formed_agent_quota (c : Config (AgentState L K))
    (hvalid : validInitial c) :
  ∀ a ∈ c, WellFormedAgentQuota a := by
  intro a ha hphase
  rcases hvalid a ha with ⟨_hphase0, hrest⟩
  rcases hrest with ⟨hrole, hrest⟩
  rcases hrest with ⟨_hassigned, hrest⟩
  rcases hrest with ⟨_hopinions, hrest⟩
  rcases hrest with ⟨hA, hB⟩
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
    (h_c : ∀ a ∈ c, WellFormedAgentQuota a)
    (h_step : (NonuniformMajority L K).StepRel c c') :
    ∀ a ∈ c', WellFormedAgentQuota a := by
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

theorem reachable_preserves_well_formed_agent_quota (init c : Config (AgentState L K))
    (h_init : validInitial init)
    (h_reach : Protocol.Reachable (NonuniformMajority L K) init c) :
    ∀ a ∈ c, WellFormedAgentQuota a := by
  induction h_reach with
  | refl =>
      exact validInitial_well_formed_agent_quota init h_init
  | tail _ hstep ih =>
      exact well_formed_agent_quota_preserved_by_step (L := L) (K := K) _ _ ih hstep

private lemma smallBiasSum_stepRel_invariant_of_quota (c c' : Config (AgentState L K))
    (hquota : ∀ a ∈ c, WellFormedAgentQuota a)
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
    simp [smallBiasSum, add_left_comm]
  have hsum_c' :
      smallBiasSum
          (c - r₁ ::ₘ {r₂} +
          (Transition L K r₁ r₂).1 ::ₘ {(Transition L K r₁ r₂).2}) =
      smallBiasSum (c - r₁ ::ₘ {r₂}) +
        (AgentState.smallBiasInt (Transition L K r₁ r₂).1 +
          AgentState.smallBiasInt (Transition L K r₁ r₂).2) := by
    simp [smallBiasSum, add_left_comm]
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
        rcases hvalid a ha with ⟨hph, hrest⟩
        rcases hrest with ⟨_hrole, hrest⟩
        rcases hrest with ⟨_hassigned, hrest⟩
        rcases hrest with ⟨_hopinions, hrest⟩
        rcases hrest with ⟨hA, hB⟩
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

theorem reachable_smallBiasSum_eq_initialGap (init c : Config (AgentState L K))
    (hvalid : validInitial init) (hreach : (NonuniformMajority L K).Reachable init c)
    (hphase : ∀ a ∈ c, a.phase.val ≤ 1) :
    smallBiasSum c = initialGap init := by
  calc
    smallBiasSum c = smallBiasSum init :=
      reachable_smallBiasSum_invariant (L := L) (K := K) init c hvalid hreach hphase
    _ = initialGap init :=
      validInitial_smallBiasSum_initialGap (L := L) (K := K) init hvalid

/-- The small-bias accumulator is preserved by every reachable transition,
independently of the final phase.

This is the all-phase form of the gap invariant for the `smallBias` field.  It
does not assert that the phase-active dyadic `bias` field has already been
initialized consistently. -/
theorem reachable_smallBiasSum_invariant_all_phases (init c : Config (AgentState L K))
    (hvalid : validInitial init) (hreach : (NonuniformMajority L K).Reachable init c) :
    smallBiasSum c = smallBiasSum init := by
  induction hreach with
  | refl =>
      rfl
  | tail hprev hstep ih =>
      have hquota_prev :=
        reachable_preserves_well_formed_agent_quota (L := L) (K := K) init _ hvalid hprev
      have hstep_sum :=
        smallBiasSum_stepRel_invariant_of_quota (L := L) (K := K) _ _ hquota_prev hstep
      exact hstep_sum.trans ih

/-- All-phase small-bias gap invariant from a valid initial configuration. -/
theorem reachable_smallBiasSum_eq_initialGap_all_phases (init c : Config (AgentState L K))
    (hvalid : validInitial init) (hreach : (NonuniformMajority L K).Reachable init c) :
    smallBiasSum c = initialGap init := by
  calc
    smallBiasSum c = smallBiasSum init :=
      reachable_smallBiasSum_invariant_all_phases (L := L) (K := K) init c hvalid hreach
    _ = initialGap init :=
      validInitial_smallBiasSum_initialGap (L := L) (K := K) init hvalid

/-- Carrier-side small-bias invariant.

The active Phase-0 bias mass is carried by MCR/Main agents.  Every CR created by
Phase 0 is initialized with zero small-bias, and later Reserve/Clock carriers
inherit only such CR states. -/
def nonMainCarrierSmallBiasZeroAgent {L K : ℕ} (a : AgentState L K) : Prop :=
  (a.role = .cr ∨ a.role = .reserve ∨ a.role = .clock) → a.smallBias.val = 3

private lemma validInitial_nonMainCarrierSmallBiasZero
    (init : Config (AgentState L K)) (hvalid : validInitial init) :
    ∀ a ∈ init, nonMainCarrierSmallBiasZeroAgent a := by
  intro a ha hrole
  have hmcr : a.role = .mcr := (hvalid a ha).2.1
  rcases hrole with hcr | hreserve | hclock <;> simp [hmcr] at *

private lemma phaseInit_preserves_nonMainCarrierSmallBiasZero
    (p : Fin 11) (a : AgentState L K)
    (ha : nonMainCarrierSmallBiasZeroAgent a) :
    nonMainCarrierSmallBiasZeroAgent (phaseInit L K p a) := by
  intro hrole
  rw [phaseInit_smallBias_eq]
  apply ha
  rcases a with
    ⟨input, output, phase, role, assigned, bias, smallBias,
      hour, minute, full, opinions, counter⟩
  cases role <;> fin_cases p <;>
    simp [phaseInit, enterPhase10] at hrole ⊢ <;>
    repeat' split_ifs at hrole <;> simp_all

private lemma runInitsBetween_preserves_nonMainCarrierSmallBiasZero
    (oldP newP : ℕ) (a : AgentState L K)
    (ha : nonMainCarrierSmallBiasZeroAgent a) :
    nonMainCarrierSmallBiasZeroAgent (runInitsBetween L K oldP newP a) := by
  unfold runInitsBetween
  generalize
      ((List.range 11).filter (fun k => oldP < k ∧ k ≤ newP)) = ks
  induction ks generalizing a with
  | nil =>
      simpa using ha
  | cons k ks ih =>
      simp [List.foldl]
      by_cases hk : k < 11
      · simp [hk]
        exact ih (phaseInit L K ⟨k, hk⟩ a)
          (phaseInit_preserves_nonMainCarrierSmallBiasZero
            (L := L) (K := K) ⟨k, hk⟩ a ha)
      · simp [hk]
        exact ih a ha

theorem phaseEpidemicUpdate_preserves_nonMainCarrierSmallBiasZero
    (s t : AgentState L K)
    (hs : nonMainCarrierSmallBiasZeroAgent s)
    (ht : nonMainCarrierSmallBiasZeroAgent t) :
    nonMainCarrierSmallBiasZeroAgent (phaseEpidemicUpdate L K s t).1 ∧
      nonMainCarrierSmallBiasZeroAgent (phaseEpidemicUpdate L K s t).2 := by
  unfold phaseEpidemicUpdate
  dsimp
  generalize hs0 :
    runInitsBetween L K s.phase.val (max s.phase.val t.phase.val)
      ({ s with phase := max s.phase t.phase }) = s0
  generalize ht0 :
    runInitsBetween L K t.phase.val (max s.phase.val t.phase.val)
      ({ t with phase := max s.phase t.phase }) = t0
  have hs0_carrier : nonMainCarrierSmallBiasZeroAgent s0 := by
    rw [← hs0]
    exact runInitsBetween_preserves_nonMainCarrierSmallBiasZero
      (L := L) (K := K) s.phase.val (max s.phase.val t.phase.val)
      ({ s with phase := max s.phase t.phase }) (by
        simpa [nonMainCarrierSmallBiasZeroAgent] using hs)
  have ht0_carrier : nonMainCarrierSmallBiasZeroAgent t0 := by
    rw [← ht0]
    exact runInitsBetween_preserves_nonMainCarrierSmallBiasZero
      (L := L) (K := K) t.phase.val (max s.phase.val t.phase.val)
      ({ t with phase := max s.phase t.phase }) (by
        simpa [nonMainCarrierSmallBiasZeroAgent] using ht)
  by_cases h10 :
      (s.phase.val < 10 ∨ t.phase.val < 10) ∧
        (s0.phase.val = 10 ∨ t0.phase.val = 10)
  · constructor
    · simpa [h10, nonMainCarrierSmallBiasZeroAgent, enterPhase10] using hs0_carrier
    · simpa [h10, nonMainCarrierSmallBiasZeroAgent, enterPhase10] using ht0_carrier
  · simpa [h10] using And.intro hs0_carrier ht0_carrier

private lemma nonMainCarrierSmallBiasZeroAgent_of_role_main
    {a : AgentState L K} (hrole : a.role = .main) :
    nonMainCarrierSmallBiasZeroAgent a := by
  intro hcarrier
  rcases hcarrier with hcr | hreserve | hclock <;> simp [hrole] at *

private lemma nonMainCarrierSmallBiasZeroAgent_of_role_cr_default
    {a : AgentState L K} (hrole : a.role = .cr) (hsmall : a.smallBias.val = 3) :
    nonMainCarrierSmallBiasZeroAgent a := by
  intro _hcarrier
  exact hsmall

private lemma nonMainCarrierSmallBiasZeroAgent_of_same_role_smallBias
    {a b : AgentState L K}
    (ha : nonMainCarrierSmallBiasZeroAgent a)
    (hrole : b.role = a.role) (hsmall : b.smallBias = a.smallBias) :
    nonMainCarrierSmallBiasZeroAgent b := by
  intro hcarrier
  rw [hsmall]
  exact ha (by simpa [hrole] using hcarrier)

set_option linter.flexible false in
private lemma Phase0Transition_preserves_nonMainCarrierSmallBiasZero
    (s t : AgentState L K)
    (hs : nonMainCarrierSmallBiasZeroAgent s)
    (ht : nonMainCarrierSmallBiasZeroAgent t) :
    nonMainCarrierSmallBiasZeroAgent (Phase0Transition L K s t).1 ∧
      nonMainCarrierSmallBiasZeroAgent (Phase0Transition L K s t).2 := by
  let s1 := if s.role = .mcr ∧ t.role = .mcr then
    { s with role := .main, smallBias := addSmallBias s.smallBias t.smallBias } else s
  let t1 := if s.role = .mcr ∧ t.role = .mcr then
    { t with role := .cr, smallBias := ⟨3, by decide⟩ } else t
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
  let s3 := if s2.role = .mcr ∧ t2.role ≠ .main ∧ t2.role ≠ .mcr ∧ ¬ t2.assigned then
    { s2 with role := .main }
    else if t2.role = .mcr ∧ s2.role ≠ .main ∧ s2.role ≠ .mcr ∧ ¬ s2.assigned then
    { s2 with assigned := true } else s2
  let t3 := if s2.role = .mcr ∧ t2.role ≠ .main ∧ t2.role ≠ .mcr ∧ ¬ t2.assigned then
    { t2 with assigned := true }
    else if t2.role = .mcr ∧ s2.role ≠ .main ∧ s2.role ≠ .mcr ∧ ¬ s2.assigned then
    { t2 with role := .main }
    else t2
  let s3' := s3
  let t3' := t3
  let s4 := if s3'.role = .cr ∧ t3'.role = .cr then
    { s3' with role := .clock, counter := ⟨50 * (L + 1), by omega⟩ } else s3'
  let t4 := if s3'.role = .cr ∧ t3'.role = .cr then
    { t3' with role := .reserve } else t3'
  let s5 := if s4.role = .clock ∧ t4.role = .clock then stdCounterSubroutine L K s4 else s4
  let t5 := if s4.role = .clock ∧ t4.role = .clock then stdCounterSubroutine L K t4 else t4
  have hs1 : nonMainCarrierSmallBiasZeroAgent s1 := by
    dsimp [s1]
    split_ifs with h <;>
      first
      | exact nonMainCarrierSmallBiasZeroAgent_of_role_main (by simp)
      | exact hs
  have ht1 : nonMainCarrierSmallBiasZeroAgent t1 := by
    dsimp [t1]
    split_ifs with h <;>
      first
      | exact nonMainCarrierSmallBiasZeroAgent_of_role_cr_default
          (by simp) (by simp)
      | exact ht
  have hs2 : nonMainCarrierSmallBiasZeroAgent s2 := by
    dsimp [s2]
    split_ifs with hleft hright
    · exact nonMainCarrierSmallBiasZeroAgent_of_role_cr_default
        (by simp) (by simp)
    · exact nonMainCarrierSmallBiasZeroAgent_of_role_main (by simp [hright.2.1])
    · exact hs1
  have ht2 : nonMainCarrierSmallBiasZeroAgent t2 := by
    dsimp [t2]
    split_ifs with hleft hright
    · exact nonMainCarrierSmallBiasZeroAgent_of_role_main (by simp [hleft.2.1])
    · exact nonMainCarrierSmallBiasZeroAgent_of_role_cr_default
        (by simp) (by simp)
    · exact ht1
  have hs3 : nonMainCarrierSmallBiasZeroAgent s3 := by
    dsimp [s3]; split_ifs with h1 h2
    · exact nonMainCarrierSmallBiasZeroAgent_of_role_main (by simp)
    · exact nonMainCarrierSmallBiasZeroAgent_of_same_role_smallBias hs2 (by simp) (by simp)
    · exact hs2
  have ht3 : nonMainCarrierSmallBiasZeroAgent t3 := by
    dsimp [t3]; split_ifs with h1 h2
    · exact nonMainCarrierSmallBiasZeroAgent_of_same_role_smallBias ht2 (by simp) (by simp)
    · exact nonMainCarrierSmallBiasZeroAgent_of_role_main (by simp)
    · exact ht2
  have hs3' : nonMainCarrierSmallBiasZeroAgent s3' := by dsimp [s3']; exact hs3
  have ht3' : nonMainCarrierSmallBiasZeroAgent t3' := by dsimp [t3']; exact ht3
  have hs4 : nonMainCarrierSmallBiasZeroAgent s4 := by
    dsimp [s4]
    split_ifs with hcr
    · intro _hcarrier
      exact hs3' (Or.inl hcr.1)
    · exact hs3'
  have ht4 : nonMainCarrierSmallBiasZeroAgent t4 := by
    dsimp [t4]
    split_ifs with hcr
    · intro _hcarrier
      exact ht3' (Or.inl hcr.2)
    · exact ht3'
  have hs5 : nonMainCarrierSmallBiasZeroAgent s5 := by
    dsimp [s5]
    split_ifs with hclock
    · intro _hcarrier
      rw [stdCounterSubroutine_smallBias]
      exact hs4 (Or.inr (Or.inr hclock.1))
    · exact hs4
  have ht5 : nonMainCarrierSmallBiasZeroAgent t5 := by
    dsimp [t5]
    split_ifs with hclock
    · intro _hcarrier
      rw [stdCounterSubroutine_smallBias]
      exact ht4 (Or.inr (Or.inr hclock.2))
    · exact ht4
  exact ⟨hs5, ht5⟩

private lemma Phase1Transition_preserves_nonMainCarrierSmallBiasZero
    (s t : AgentState L K)
    (hs : nonMainCarrierSmallBiasZeroAgent s)
    (ht : nonMainCarrierSmallBiasZeroAgent t) :
    nonMainCarrierSmallBiasZeroAgent (Phase1Transition L K s t).1 ∧
      nonMainCarrierSmallBiasZeroAgent (Phase1Transition L K s t).2 := by
  constructor
  · intro hcarrier
    by_cases hmain : s.role = .main ∧ t.role = .main
    · simp [Phase1Transition, hmain, clockCounterStep] at hcarrier
    · by_cases hsclock : s.role = .clock
      · rw [show (Phase1Transition L K s t).1.smallBias.val = s.smallBias.val by
          simp [Phase1Transition, hmain, clockCounterStep, hsclock]]
        exact hs (Or.inr (Or.inr hsclock))
      · have hs_carrier : s.role = .cr ∨ s.role = .reserve ∨ s.role = .clock := by
          simpa [Phase1Transition, hmain, clockCounterStep, hsclock] using hcarrier
        rw [show (Phase1Transition L K s t).1.smallBias.val = s.smallBias.val by
          simp [Phase1Transition, hmain, clockCounterStep, hsclock]]
        exact hs hs_carrier
  · intro hcarrier
    by_cases hmain : s.role = .main ∧ t.role = .main
    · simp [Phase1Transition, hmain, clockCounterStep] at hcarrier
    · by_cases htclock : t.role = .clock
      · rw [show (Phase1Transition L K s t).2.smallBias.val = t.smallBias.val by
          simp [Phase1Transition, hmain, clockCounterStep, htclock]]
        exact ht (Or.inr (Or.inr htclock))
      · have ht_carrier : t.role = .cr ∨ t.role = .reserve ∨ t.role = .clock := by
          simpa [Phase1Transition, hmain, clockCounterStep, htclock] using hcarrier
        rw [show (Phase1Transition L K s t).2.smallBias.val = t.smallBias.val by
          simp [Phase1Transition, hmain, clockCounterStep, htclock]]
        exact ht ht_carrier

/-- `advancePhaseWithInit` keeps the non-main carrier role set `{cr, reserve,
clock}` closed: the only role rewrite any `phaseInit` branch performs is Phase-1
`cr → reserve` (both already in the set); `main`/`mcr` are each preserved.  So if
the advanced agent has a carrier role, the original did too. -/
private lemma carrier_of_advancePhaseWithInit (a : AgentState L K) :
    ((advancePhaseWithInit L K a).role = .cr ∨
        (advancePhaseWithInit L K a).role = .reserve ∨
        (advancePhaseWithInit L K a).role = .clock) →
      a.role = .cr ∨ a.role = .reserve ∨ a.role = .clock := by
  intro h
  have hr : (advancePhaseWithInit L K a).role =
      if (advancePhase L K a).phase.val = 1 ∧ a.role = .cr then .reserve else a.role := by
    show (phaseInit L K (advancePhase L K a).phase (advancePhase L K a)).role = _
    rw [phaseInit_role, advancePhase_role]
  rw [hr] at h
  split_ifs at h with hc
  · exact Or.inl hc.2
  · exact h

/-- The opinion set does not influence the role written by `advancePhaseWithInit`. -/
private lemma advancePhaseWithInit_role_update_opinions (a : AgentState L K) (o : Fin 8) :
    (advancePhaseWithInit L K { a with opinions := o }).role =
      (advancePhaseWithInit L K a).role := by
  have hph : (advancePhase L K { a with opinions := o }).phase = (advancePhase L K a).phase := by
    by_cases h : a.phase.val < 10 <;> simp [advancePhase, h]
  show (phaseInit L K (advancePhase L K { a with opinions := o }).phase
      (advancePhase L K { a with opinions := o })).role =
    (phaseInit L K (advancePhase L K a).phase (advancePhase L K a)).role
  rw [phaseInit_role, phaseInit_role, advancePhase_role, advancePhase_role, hph]

private lemma Phase2Transition_preserves_nonMainCarrierSmallBiasZero
    (s t : AgentState L K)
    (hs : nonMainCarrierSmallBiasZeroAgent s)
    (ht : nonMainCarrierSmallBiasZeroAgent t) :
    nonMainCarrierSmallBiasZeroAgent (Phase2Transition L K s t).1 ∧
      nonMainCarrierSmallBiasZeroAgent (Phase2Transition L K s t).2 := by
  rcases Phase2Transition_preserves_smallBias L K s t with ⟨hsb, htb⟩
  constructor
  · intro hcarrier
    rw [hsb]
    apply hs
    unfold Phase2Transition at hcarrier
    dsimp at hcarrier
    split_ifs at hcarrier
    · exact carrier_of_advancePhaseWithInit s (by
        rcases hcarrier with hcr | hrest
        · exact Or.inl (by
            simpa [advancePhaseWithInit_role_update_opinions] using hcr)
        · rcases hrest with hreserve | hclock
          · exact Or.inr (Or.inl (by
              simpa [advancePhaseWithInit_role_update_opinions] using hreserve))
          · exact Or.inr (Or.inr (by
              simpa [advancePhaseWithInit_role_update_opinions] using hclock)))
    · simpa using hcarrier
    · simpa using hcarrier
    · simpa using hcarrier
    · simpa using hcarrier
  · intro hcarrier
    rw [htb]
    apply ht
    unfold Phase2Transition at hcarrier
    dsimp at hcarrier
    split_ifs at hcarrier
    · exact carrier_of_advancePhaseWithInit t (by
        rcases hcarrier with hcr | hrest
        · exact Or.inl (by
            simpa [advancePhaseWithInit_role_update_opinions] using hcr)
        · rcases hrest with hreserve | hclock
          · exact Or.inr (Or.inl (by
              simpa [advancePhaseWithInit_role_update_opinions] using hreserve))
          · exact Or.inr (Or.inr (by
              simpa [advancePhaseWithInit_role_update_opinions] using hclock)))
    · simpa using hcarrier
    · simpa using hcarrier
    · simpa using hcarrier
    · simpa using hcarrier

private lemma phase3CancelSplit_preserves_role (s t : AgentState L K) :
    (phase3CancelSplit L K s t).1.role = s.role ∧
      (phase3CancelSplit L K s t).2.role = t.role := by
  unfold phase3CancelSplit
  match s.bias, t.bias with
  | .zero, .zero => simp
  | .zero, .dyadic _ _ => simp; split_ifs <;> simp
  | .dyadic _ _, .zero => simp; split_ifs <;> simp
  | .dyadic .pos _, .dyadic .pos _ => simp
  | .dyadic .pos _, .dyadic .neg _ => simp; split_ifs <;> simp
  | .dyadic .neg _, .dyadic .pos _ => simp; split_ifs <;> simp
  | .dyadic .neg _, .dyadic .neg _ => simp

private lemma Phase3Transition_preserves_nonMainCarrierSmallBiasZero
    (s t : AgentState L K)
    (hs : nonMainCarrierSmallBiasZeroAgent s)
    (ht : nonMainCarrierSmallBiasZeroAgent t) :
    nonMainCarrierSmallBiasZeroAgent (Phase3Transition L K s t).1 ∧
      nonMainCarrierSmallBiasZeroAgent (Phase3Transition L K s t).2 := by
  let s1 := if s.role = .clock ∧ t.role = .clock then
    if s.minute ≠ t.minute then { s with minute := max s.minute t.minute }
    else if _h : s.minute.val < K * (L + 1) then
      { s with minute := ⟨s.minute.val + 1, by omega⟩ }
    else stdCounterSubroutine L K s
  else s
  let t1 := if s.role = .clock ∧ t.role = .clock then
    if s.minute ≠ t.minute then { t with minute := max s.minute t.minute }
    else if _h : s.minute.val < K * (L + 1) then t
    else stdCounterSubroutine L K t
  else t
  let s2 := if s1.role = .main ∧ s1.bias = .zero ∧ t1.role = .clock then
    let hVal := max s1.hour.val (min L (t1.minute.val / K))
    have h_hour_lt : hVal < L + 1 :=
      (Nat.max_lt).mpr ⟨s1.hour.2, Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩
    { s1 with hour := ⟨hVal, h_hour_lt⟩ }
  else if t1.role = .main ∧ t1.bias = .zero ∧ s1.role = .clock then s1
  else s1
  let t2 := if s1.role = .main ∧ s1.bias = .zero ∧ t1.role = .clock then t1
  else if t1.role = .main ∧ t1.bias = .zero ∧ s1.role = .clock then
    let hVal := max t1.hour.val (min L (s1.minute.val / K))
    have h_hour_lt : hVal < L + 1 :=
      (Nat.max_lt).mpr ⟨t1.hour.2, Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩
    { t1 with hour := ⟨hVal, h_hour_lt⟩ }
  else t1
  have hs1 : nonMainCarrierSmallBiasZeroAgent s1 := by
    dsimp [s1]
    split_ifs with hclock hneq hmax <;>
      first
      | exact hs
      | intro _; rw [stdCounterSubroutine_smallBias]; exact hs (Or.inr (Or.inr hclock.1))
  have ht1 : nonMainCarrierSmallBiasZeroAgent t1 := by
    dsimp [t1]
    split_ifs with hclock hneq hmax <;>
      first
      | exact ht
      | intro _; rw [stdCounterSubroutine_smallBias]; exact ht (Or.inr (Or.inr hclock.2))
  have hs2 : nonMainCarrierSmallBiasZeroAgent s2 := by
    dsimp [s2]
    split_ifs <;>
      first
      | exact nonMainCarrierSmallBiasZeroAgent_of_same_role_smallBias hs1 (by simp) (by simp)
      | exact hs1
  have ht2 : nonMainCarrierSmallBiasZeroAgent t2 := by
    dsimp [t2]
    split_ifs <;>
      first
      | exact ht1
      | exact nonMainCarrierSmallBiasZeroAgent_of_same_role_smallBias ht1 (by simp) (by simp)
  rcases phase3CancelSplit_preserves_smallBias (L := L) (K := K) s2 t2 with ⟨hcs_s, hcs_t⟩
  rcases phase3CancelSplit_preserves_role (L := L) (K := K) s2 t2 with ⟨hrole_s, hrole_t⟩
  constructor
  · change nonMainCarrierSmallBiasZeroAgent
      (if s2.role = .main ∧ t2.role = .main then phase3CancelSplit L K s2 t2 else (s2, t2)).1
    split_ifs with hmain
    · intro hcarrier
      rw [hcs_s]
      apply hs2
      simpa [hrole_s] using hcarrier
    · exact hs2
  · change nonMainCarrierSmallBiasZeroAgent
      (if s2.role = .main ∧ t2.role = .main then phase3CancelSplit L K s2 t2 else (s2, t2)).2
    split_ifs with hmain
    · intro hcarrier
      rw [hcs_t]
      apply ht2
      simpa [hrole_t] using hcarrier
    · exact ht2

private lemma Phase4Transition_preserves_nonMainCarrierSmallBiasZero
    (s t : AgentState L K)
    (hs : nonMainCarrierSmallBiasZeroAgent s)
    (ht : nonMainCarrierSmallBiasZeroAgent t) :
    nonMainCarrierSmallBiasZeroAgent (Phase4Transition L K s t).1 ∧
      nonMainCarrierSmallBiasZeroAgent (Phase4Transition L K s t).2 := by
  rcases Phase4Transition_preserves_smallBias L K s t with ⟨hsb, htb⟩
  constructor
  · intro hcarrier
    rw [hsb]
    apply hs
    unfold Phase4Transition at hcarrier
    dsimp at hcarrier
    split_ifs at hcarrier
    · exact carrier_of_advancePhaseWithInit (L := L) (K := K) s hcarrier
    · simpa using hcarrier
  · intro hcarrier
    rw [htb]
    apply ht
    unfold Phase4Transition at hcarrier
    dsimp at hcarrier
    split_ifs at hcarrier
    · exact carrier_of_advancePhaseWithInit (L := L) (K := K) t hcarrier
    · simpa using hcarrier

private lemma Phase5Transition_preserves_nonMainCarrierSmallBiasZero
    (s t : AgentState L K)
    (hs : nonMainCarrierSmallBiasZeroAgent s)
    (ht : nonMainCarrierSmallBiasZeroAgent t) :
    nonMainCarrierSmallBiasZeroAgent (Phase5Transition L K s t).1 ∧
      nonMainCarrierSmallBiasZeroAgent (Phase5Transition L K s t).2 := by
  unfold Phase5Transition
  let doSample (r m : AgentState L K) : AgentState L K × AgentState L K :=
    if r.hour.val = L then ({ r with hour := exponentOf L m.bias }, m)
    else (r, m)
  let s1 := if s.role = .reserve ∧ t.role = .main ∧ (t.bias ≠ .zero) then
    (doSample s t).1
  else if t.role = .reserve ∧ s.role = .main ∧ (s.bias ≠ .zero) then
    (doSample t s).2
  else s
  let t1 := if s.role = .reserve ∧ t.role = .main ∧ (t.bias ≠ .zero) then
    (doSample s t).2
  else if t.role = .reserve ∧ s.role = .main ∧ (s.bias ≠ .zero) then
    (doSample t s).1
  else t
  have hstd :
      ∀ a : AgentState L K, nonMainCarrierSmallBiasZeroAgent a →
        nonMainCarrierSmallBiasZeroAgent
          (if a.role = .clock then stdCounterSubroutine L K a else a) := by
    intro a ha
    by_cases hclock : a.role = .clock
    · intro _hcarrier
      simp [hclock, stdCounterSubroutine_smallBias]
      exact ha (Or.inr (Or.inr hclock))
    · simpa [hclock] using ha
  have hs1 : nonMainCarrierSmallBiasZeroAgent s1 := by
    dsimp [s1, doSample]
    split_ifs <;> simpa [nonMainCarrierSmallBiasZeroAgent] using hs
  have ht1 : nonMainCarrierSmallBiasZeroAgent t1 := by
    dsimp [t1, doSample]
    split_ifs <;> simpa [nonMainCarrierSmallBiasZeroAgent] using ht
  change
    nonMainCarrierSmallBiasZeroAgent
      (if s1.role = .clock then stdCounterSubroutine L K s1 else s1) ∧
    nonMainCarrierSmallBiasZeroAgent
      (if t1.role = .clock then stdCounterSubroutine L K t1 else t1)
  exact ⟨hstd s1 hs1, hstd t1 ht1⟩

private lemma doSplit_preserves_nonMainCarrierSmallBiasZero
    (r m : AgentState L K)
    (hr : nonMainCarrierSmallBiasZeroAgent r)
    (hm : nonMainCarrierSmallBiasZeroAgent m) :
    nonMainCarrierSmallBiasZeroAgent (doSplit L K r m).1 ∧
      nonMainCarrierSmallBiasZeroAgent (doSplit L K r m).2 := by
  unfold doSplit
  match m.bias with
  | .zero =>
      exact ⟨hr, hm⟩
  | .dyadic _ j =>
      by_cases hguard : (¬ r.hour.val = L ∧ j < r.hour)
      · by_cases hj : j.val < L
        · constructor
          · exact nonMainCarrierSmallBiasZeroAgent_of_role_main (by simp [hguard, hj])
          · simpa [hguard, hj, nonMainCarrierSmallBiasZeroAgent] using hm
        · simp [hguard, hj, hr, hm]
      · simp [hguard, hr, hm]

private lemma Phase6Transition_preserves_nonMainCarrierSmallBiasZero
    (s t : AgentState L K)
    (hs : nonMainCarrierSmallBiasZeroAgent s)
    (ht : nonMainCarrierSmallBiasZeroAgent t) :
    nonMainCarrierSmallBiasZeroAgent (Phase6Transition L K s t).1 ∧
      nonMainCarrierSmallBiasZeroAgent (Phase6Transition L K s t).2 := by
  unfold Phase6Transition
  let s1 := if s.role = .reserve ∧ t.role = .main ∧ (t.bias ≠ .zero) then
    (doSplit L K s t).1
  else if t.role = .reserve ∧ s.role = .main ∧ (s.bias ≠ .zero) then
    (doSplit L K t s).2
  else s
  let t1 := if s.role = .reserve ∧ t.role = .main ∧ (t.bias ≠ .zero) then
    (doSplit L K s t).2
  else if t.role = .reserve ∧ s.role = .main ∧ (s.bias ≠ .zero) then
    (doSplit L K t s).1
  else t
  have hstd :
      ∀ a : AgentState L K, nonMainCarrierSmallBiasZeroAgent a →
        nonMainCarrierSmallBiasZeroAgent
          (if a.role = .clock then stdCounterSubroutine L K a else a) := by
    intro a ha
    by_cases hclock : a.role = .clock
    · intro _hcarrier
      simp [hclock, stdCounterSubroutine_smallBias]
      exact ha (Or.inr (Or.inr hclock))
    · simpa [hclock] using ha
  rcases doSplit_preserves_nonMainCarrierSmallBiasZero (L := L) (K := K) s t hs ht with
    ⟨hst_left, hst_right⟩
  rcases doSplit_preserves_nonMainCarrierSmallBiasZero (L := L) (K := K) t s ht hs with
    ⟨hts_left, hts_right⟩
  have hs1 : nonMainCarrierSmallBiasZeroAgent s1 := by
    dsimp [s1]
    split_ifs <;> assumption
  have ht1 : nonMainCarrierSmallBiasZeroAgent t1 := by
    dsimp [t1]
    split_ifs <;> assumption
  change
    nonMainCarrierSmallBiasZeroAgent
      (if s1.role = .clock then stdCounterSubroutine L K s1 else s1) ∧
    nonMainCarrierSmallBiasZeroAgent
      (if t1.role = .clock then stdCounterSubroutine L K t1 else t1)
  exact ⟨hstd s1 hs1, hstd t1 ht1⟩

private lemma cancelSplit_preserves_role (s t : AgentState L K) :
    (cancelSplit L K s t).1.role = s.role ∧
      (cancelSplit L K s t).2.role = t.role := by
  unfold cancelSplit
  match s.bias, t.bias with
  | .zero, _ => simp
  | .dyadic _ _, .zero => simp
  | .dyadic _ _, .dyadic _ _ => simp; split_ifs <;> simp

private lemma cancelSplit_preserves_nonMainCarrierSmallBiasZero
    (s t : AgentState L K)
    (hs : nonMainCarrierSmallBiasZeroAgent s)
    (ht : nonMainCarrierSmallBiasZeroAgent t) :
    nonMainCarrierSmallBiasZeroAgent (cancelSplit L K s t).1 ∧
      nonMainCarrierSmallBiasZeroAgent (cancelSplit L K s t).2 := by
  rcases cancelSplit_preserves_smallBias (L := L) (K := K) s t with ⟨hssmall, htsmall⟩
  rcases cancelSplit_preserves_role (L := L) (K := K) s t with ⟨hsrole, htrole⟩
  constructor
  · intro hcarrier
    rw [hssmall]
    exact hs (by simpa [hsrole] using hcarrier)
  · intro hcarrier
    rw [htsmall]
    exact ht (by simpa [htrole] using hcarrier)

private lemma Phase7Transition_preserves_nonMainCarrierSmallBiasZero
    (s t : AgentState L K)
    (hs : nonMainCarrierSmallBiasZeroAgent s)
    (ht : nonMainCarrierSmallBiasZeroAgent t) :
    nonMainCarrierSmallBiasZeroAgent (Phase7Transition L K s t).1 ∧
      nonMainCarrierSmallBiasZeroAgent (Phase7Transition L K s t).2 := by
  unfold Phase7Transition
  let s1 := if s.role = .main ∧ t.role = .main then (cancelSplit L K s t).1 else s
  let t1 := if s.role = .main ∧ t.role = .main then (cancelSplit L K s t).2 else t
  have hstd :
      ∀ a : AgentState L K, nonMainCarrierSmallBiasZeroAgent a →
        nonMainCarrierSmallBiasZeroAgent
          (if a.role = .clock then stdCounterSubroutine L K a else a) := by
    intro a ha
    by_cases hclock : a.role = .clock
    · intro _hcarrier
      simp [hclock, stdCounterSubroutine_smallBias]
      exact ha (Or.inr (Or.inr hclock))
    · simpa [hclock] using ha
  rcases cancelSplit_preserves_nonMainCarrierSmallBiasZero (L := L) (K := K) s t hs ht with
    ⟨hcancel_s, hcancel_t⟩
  have hs1 : nonMainCarrierSmallBiasZeroAgent s1 := by
    dsimp [s1]
    split_ifs <;> assumption
  have ht1 : nonMainCarrierSmallBiasZeroAgent t1 := by
    dsimp [t1]
    split_ifs <;> assumption
  change
    nonMainCarrierSmallBiasZeroAgent
      (if s1.role = .clock then stdCounterSubroutine L K s1 else s1) ∧
    nonMainCarrierSmallBiasZeroAgent
      (if t1.role = .clock then stdCounterSubroutine L K t1 else t1)
  exact ⟨hstd s1 hs1, hstd t1 ht1⟩

private lemma absorbConsume_preserves_role (s t : AgentState L K) :
    (absorbConsume L K s t).1.role = s.role ∧
      (absorbConsume L K s t).2.role = t.role := by
  unfold absorbConsume
  match s.bias, t.bias with
  | .zero, _ => simp
  | .dyadic .pos _, .zero => simp
  | .dyadic .neg _, .zero => simp
  | .dyadic .pos _, .dyadic .pos _ => simp
  | .dyadic .neg _, .dyadic .neg _ => simp
  | .dyadic .pos _, .dyadic .neg _ => simp; split_ifs <;> simp
  | .dyadic .neg _, .dyadic .pos _ => simp; split_ifs <;> simp

private lemma absorbConsume_preserves_nonMainCarrierSmallBiasZero
    (s t : AgentState L K)
    (hs : nonMainCarrierSmallBiasZeroAgent s)
    (ht : nonMainCarrierSmallBiasZeroAgent t) :
    nonMainCarrierSmallBiasZeroAgent (absorbConsume L K s t).1 ∧
      nonMainCarrierSmallBiasZeroAgent (absorbConsume L K s t).2 := by
  rcases absorbConsume_preserves_smallBias (L := L) (K := K) s t with ⟨hssmall, htsmall⟩
  rcases absorbConsume_preserves_role (L := L) (K := K) s t with ⟨hsrole, htrole⟩
  constructor
  · intro hcarrier
    rw [hssmall]
    exact hs (by simpa [hsrole] using hcarrier)
  · intro hcarrier
    rw [htsmall]
    exact ht (by simpa [htrole] using hcarrier)

private lemma Phase8Transition_preserves_nonMainCarrierSmallBiasZero
    (s t : AgentState L K)
    (hs : nonMainCarrierSmallBiasZeroAgent s)
    (ht : nonMainCarrierSmallBiasZeroAgent t) :
    nonMainCarrierSmallBiasZeroAgent (Phase8Transition L K s t).1 ∧
      nonMainCarrierSmallBiasZeroAgent (Phase8Transition L K s t).2 := by
  unfold Phase8Transition
  let s1 := if s.role = .main ∧ t.role = .main then (absorbConsume L K s t).1 else s
  let t1 := if s.role = .main ∧ t.role = .main then (absorbConsume L K s t).2 else t
  have hstd :
      ∀ a : AgentState L K, nonMainCarrierSmallBiasZeroAgent a →
        nonMainCarrierSmallBiasZeroAgent
          (if a.role = .clock then stdCounterSubroutine L K a else a) := by
    intro a ha
    by_cases hclock : a.role = .clock
    · intro _hcarrier
      simp [hclock, stdCounterSubroutine_smallBias]
      exact ha (Or.inr (Or.inr hclock))
    · simpa [hclock] using ha
  rcases absorbConsume_preserves_nonMainCarrierSmallBiasZero (L := L) (K := K) s t hs ht with
    ⟨habs_s, habs_t⟩
  have hs1 : nonMainCarrierSmallBiasZeroAgent s1 := by
    dsimp [s1]
    split_ifs <;> assumption
  have ht1 : nonMainCarrierSmallBiasZeroAgent t1 := by
    dsimp [t1]
    split_ifs <;> assumption
  change
    nonMainCarrierSmallBiasZeroAgent
      (if s1.role = .clock then stdCounterSubroutine L K s1 else s1) ∧
    nonMainCarrierSmallBiasZeroAgent
      (if t1.role = .clock then stdCounterSubroutine L K t1 else t1)
  exact ⟨hstd s1 hs1, hstd t1 ht1⟩

private lemma Phase9Transition_preserves_nonMainCarrierSmallBiasZero
    (s t : AgentState L K)
    (hs : nonMainCarrierSmallBiasZeroAgent s)
    (ht : nonMainCarrierSmallBiasZeroAgent t) :
    nonMainCarrierSmallBiasZeroAgent (Phase9Transition L K s t).1 ∧
      nonMainCarrierSmallBiasZeroAgent (Phase9Transition L K s t).2 := by
  unfold Phase9Transition
  exact Phase2Transition_preserves_nonMainCarrierSmallBiasZero (L := L) (K := K) s t hs ht

private lemma Phase10Transition_preserves_nonMainCarrierSmallBiasZero
    (s t : AgentState L K)
    (hs : nonMainCarrierSmallBiasZeroAgent s)
    (ht : nonMainCarrierSmallBiasZeroAgent t) :
    nonMainCarrierSmallBiasZeroAgent (Phase10Transition L K s t).1 ∧
      nonMainCarrierSmallBiasZeroAgent (Phase10Transition L K s t).2 := by
  unfold Phase10Transition
  dsimp
  constructor
  · intro hcarrier
    split_ifs at hcarrier ⊢ <;> exact hs (by simpa using hcarrier)
  · intro hcarrier
    split_ifs at hcarrier ⊢ <;> exact ht (by simpa using hcarrier)

private lemma finishPhase10Entry_preserves_nonMainCarrierSmallBiasZero
    (before after : AgentState L K)
    (ha : nonMainCarrierSmallBiasZeroAgent after) :
    nonMainCarrierSmallBiasZeroAgent (finishPhase10Entry L K before after) := by
  intro hcarrier
  rw [finishPhase10Entry_smallBias]
  apply ha
  simpa [finishPhase10Entry_role] using hcarrier

theorem Transition_preserves_nonMainCarrierSmallBiasZero
    (s t : AgentState L K)
    (hs : nonMainCarrierSmallBiasZeroAgent s)
    (ht : nonMainCarrierSmallBiasZeroAgent t) :
    nonMainCarrierSmallBiasZeroAgent (Transition L K s t).1 ∧
      nonMainCarrierSmallBiasZeroAgent (Transition L K s t).2 := by
  rcases phaseEpidemicUpdate_preserves_nonMainCarrierSmallBiasZero
      (L := L) (K := K) s t hs ht with
    ⟨hs_ep, ht_ep⟩
  unfold Transition
  let s' := (phaseEpidemicUpdate L K s t).1
  let t' := (phaseEpidemicUpdate L K s t).2
  let out :=
    match s'.phase with
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
    | _ => (s', t')
  have hout :
      nonMainCarrierSmallBiasZeroAgent out.1 ∧
        nonMainCarrierSmallBiasZeroAgent out.2 := by
    change nonMainCarrierSmallBiasZeroAgent
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
        | _ => (s', t')).1 ∧
      nonMainCarrierSmallBiasZeroAgent
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
        | _ => (s', t')).2
    rcases h_phase : s'.phase with ⟨n, hn⟩
    match n, hn with
    | 0, _ =>
      exact Phase0Transition_preserves_nonMainCarrierSmallBiasZero
        (L := L) (K := K) s' t' hs_ep ht_ep
    | 1, _ =>
      exact Phase1Transition_preserves_nonMainCarrierSmallBiasZero
        (L := L) (K := K) s' t' hs_ep ht_ep
    | 2, _ =>
      exact Phase2Transition_preserves_nonMainCarrierSmallBiasZero
        (L := L) (K := K) s' t' hs_ep ht_ep
    | 3, _ =>
      exact Phase3Transition_preserves_nonMainCarrierSmallBiasZero
        (L := L) (K := K) s' t' hs_ep ht_ep
    | 4, _ =>
      exact Phase4Transition_preserves_nonMainCarrierSmallBiasZero
        (L := L) (K := K) s' t' hs_ep ht_ep
    | 5, _ =>
      exact Phase5Transition_preserves_nonMainCarrierSmallBiasZero
        (L := L) (K := K) s' t' hs_ep ht_ep
    | 6, _ =>
      exact Phase6Transition_preserves_nonMainCarrierSmallBiasZero
        (L := L) (K := K) s' t' hs_ep ht_ep
    | 7, _ =>
      exact Phase7Transition_preserves_nonMainCarrierSmallBiasZero
        (L := L) (K := K) s' t' hs_ep ht_ep
    | 8, _ =>
      exact Phase8Transition_preserves_nonMainCarrierSmallBiasZero
        (L := L) (K := K) s' t' hs_ep ht_ep
    | 9, _ =>
      exact Phase9Transition_preserves_nonMainCarrierSmallBiasZero
        (L := L) (K := K) s' t' hs_ep ht_ep
    | 10, _ =>
      exact Phase10Transition_preserves_nonMainCarrierSmallBiasZero
        (L := L) (K := K) s' t' hs_ep ht_ep
    | n + 11, hn => omega
  exact
    ⟨finishPhase10Entry_preserves_nonMainCarrierSmallBiasZero
        (L := L) (K := K) s' out.1 hout.1,
      finishPhase10Entry_preserves_nonMainCarrierSmallBiasZero
        (L := L) (K := K) t' out.2 hout.2⟩

theorem reachable_nonMain_smallBias_zero
    (init c : Config (AgentState L K))
    (hinit : validInitial init)
    (hreach : (NonuniformMajority L K).Reachable init c) :
    ∀ a ∈ c, (a.role = .reserve ∨ a.role = .clock) → a.smallBias.val = 3 := by
  have hcarrier : ∀ a ∈ c, nonMainCarrierSmallBiasZeroAgent a := by
    induction hreach with
    | refl =>
        exact validInitial_nonMainCarrierSmallBiasZero (L := L) (K := K) init hinit
    | tail hprev hstep ih =>
        rcases hstep with ⟨r₁, r₂, happ, hc'⟩
        dsimp [Protocol.Applicable, NonuniformMajority] at happ hc'
        have hr₁_mem : r₁ ∈ _ := Multiset.mem_of_le happ (by simp)
        have hr₂_mem : r₂ ∈ _ := Multiset.mem_of_le happ (by simp)
        have htrans := Transition_preserves_nonMainCarrierSmallBiasZero
          (L := L) (K := K) r₁ r₂ (ih r₁ hr₁_mem) (ih r₂ hr₂_mem)
        rw [hc']
        intro a ha
        simp only [Multiset.mem_add, Multiset.mem_cons, Multiset.mem_singleton] at ha
        rcases ha with hold | hnew
        · exact ih a (Multiset.mem_of_le (Multiset.sub_le_self _ {r₁, r₂}) hold)
        · rcases hnew with hnew | hnew
          · subst a
            exact htrans.1
          · subst a
            exact htrans.2
  intro a ha hrole
  exact hcarrier a ha (Or.inr hrole)

theorem reachable_nonMainCarrierSmallBiasZeroAgent
    (init c : Config (AgentState L K))
    (hinit : validInitial init)
    (hreach : (NonuniformMajority L K).Reachable init c) :
    ∀ a ∈ c, nonMainCarrierSmallBiasZeroAgent a := by
  induction hreach with
  | refl =>
      exact validInitial_nonMainCarrierSmallBiasZero (L := L) (K := K) init hinit
  | tail hprev hstep ih =>
      rcases hstep with ⟨r₁, r₂, happ, hc'⟩
      dsimp [Protocol.Applicable, NonuniformMajority] at happ hc'
      have hr₁_mem : r₁ ∈ _ := Multiset.mem_of_le happ (by simp)
      have hr₂_mem : r₂ ∈ _ := Multiset.mem_of_le happ (by simp)
      have htrans := Transition_preserves_nonMainCarrierSmallBiasZero
        (L := L) (K := K) r₁ r₂ (ih r₁ hr₁_mem) (ih r₂ hr₂_mem)
      rw [hc']
      intro a ha
      simp only [Multiset.mem_add, Multiset.mem_cons, Multiset.mem_singleton] at ha
      rcases ha with hold | hnew
      · exact ih a (Multiset.mem_of_le (Multiset.sub_le_self _ {r₁, r₂}) hold)
      · rcases hnew with hnew | hnew
        · subst a
          exact htrans.1
        · subst a
          exact htrans.2

private lemma prePhase4Mass_phaseInit_three_of_carrier
    (a : AgentState L K)
    (hcarrier : nonMainCarrierSmallBiasZeroAgent a)
    (hmcr : a.role ≠ .mcr)
    (hphase : 3 ≤ a.phase.val)
    (hsmall : a.smallBias.val = 2 ∨ a.smallBias.val = 3 ∨ a.smallBias.val = 4) :
    prePhase4Mass (phaseInit L K ⟨3, by decide⟩ a) =
      (AgentState.smallBiasInt a : ℚ) := by
  have hnot_lt : ¬ a.phase.val < 3 := by omega
  rcases hsmall with h2 | h34
  · cases hrole : a.role <;>
      simp [prePhase4Mass, phaseInit, AgentState.smallBiasInt, Bias.toRat,
        hrole, h2, hnot_lt, nonMainCarrierSmallBiasZeroAgent] at hcarrier hmcr ⊢
  · rcases h34 with h3 | h4
    · cases hrole : a.role <;>
        simp [prePhase4Mass, phaseInit, AgentState.smallBiasInt, Bias.toRat,
          hrole, h3, hnot_lt, nonMainCarrierSmallBiasZeroAgent] at hcarrier hmcr ⊢
    · cases hrole : a.role <;>
        simp [prePhase4Mass, phaseInit, AgentState.smallBiasInt, Bias.toRat,
          hrole, h4, hnot_lt, nonMainCarrierSmallBiasZeroAgent] at hcarrier hmcr ⊢

lemma StepRel_phase_le_of_next_phase_le_four (c c' : Config (AgentState L K))
    (hstep : (NonuniformMajority L K).StepRel c c')
    (hphase' : ∀ a ∈ c', a.phase.val ≤ 4) :
    ∀ a ∈ c, a.phase.val ≤ 4 := by
  rcases hstep with ⟨r₁, r₂, happ, hc'⟩
  dsimp [Protocol.Applicable, NonuniformMajority] at happ hc'
  have hmono := Transition_phase_monotone (L := L) (K := K) r₁ r₂
  have hp₁_mem : (Transition L K r₁ r₂).1 ∈ c' := by
    rw [hc']
    exact Multiset.mem_add.2 (Or.inr (Multiset.mem_cons_self _ _))
  have hp₂_mem : (Transition L K r₁ r₂).2 ∈ c' := by
    rw [hc']
    exact Multiset.mem_add.2 (Or.inr (Multiset.mem_cons_of_mem (by simp)))
  have hr₁_phase : r₁.phase.val ≤ 4 := le_trans hmono.1 (hphase' _ hp₁_mem)
  have hr₂_phase : r₂.phase.val ≤ 4 := le_trans hmono.2 (hphase' _ hp₂_mem)
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

/-- Strong invariant: an agent in role MCR or CR must be at phase 0
(initial population-splitting) or phase 10 (error track). Equivalently,
once an agent reaches phase ∈ [1, 9], its role is in {Main, Reserve, Clock}. -/
def RolePhaseInvariantAgent {L K : ℕ} (a : AgentState L K) : Prop :=
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
def WellFormedAgent {L K : ℕ} (a : AgentState L K) : Prop :=
  RolePhaseInvariantAgent a ∧
  (a.role = .cr → a.smallBias = defaultSmallBias)

private lemma enterPhase10_preserves_well_formed_agent
    (a : AgentState L K) :
    WellFormedAgent a → WellFormedAgent (enterPhase10 L K a) := by
  intro ha
  constructor
  · intro _htrans
    exact Or.inr rfl
  · intro hcr
    have hcr_a : a.role = .cr := by simpa using hcr
    simpa using ha.2 hcr_a

private lemma canonicalPhase10Entry_preserves_well_formed_agent
    (before after : AgentState L K) :
    WellFormedAgent after →
      WellFormedAgent (canonicalPhase10Entry L K before after) := by
  intro ha
  unfold canonicalPhase10Entry
  split_ifs with hentry
  · exact enterPhase10_preserves_well_formed_agent (L := L) (K := K) after ha
  · exact ha

private lemma phase10EpidemicEntry_preserves_well_formed_agent
    (before after : AgentState L K) :
    WellFormedAgent after →
      WellFormedAgent (phase10EpidemicEntry L K before after) := by
  intro ha
  unfold phase10EpidemicEntry
  split_ifs with hentry
  · exact enterPhase10_preserves_well_formed_agent (L := L) (K := K) after ha
  · exact ha

private lemma finishPhase10Entry_preserves_well_formed_agent
    (before after : AgentState L K) :
    WellFormedAgent after →
      WellFormedAgent (finishPhase10Entry L K before after) := by
  simpa [finishPhase10Entry] using
    canonicalPhase10Entry_preserves_well_formed_agent (L := L) (K := K) before after

@[simp] private lemma finishPhase10Entry_well_formed_agent_iff
    (before after : AgentState L K) :
    WellFormedAgent (finishPhase10Entry L K before after) ↔
      WellFormedAgent after := by
  unfold finishPhase10Entry canonicalPhase10Entry
  split_ifs with hentry
  · constructor
    · intro hfin
      constructor
      · intro _htrans
        exact Or.inr hentry.2
      · intro hcr
        have hcr_fin : (enterPhase10 L K after).role = .cr := by simpa using hcr
        simpa using hfin.2 hcr_fin
    · exact enterPhase10_preserves_well_formed_agent (L := L) (K := K) after
  · simp

theorem WellFormedAgent.role_phase {a : AgentState L K} :
    WellFormedAgent a → RolePhaseInvariantAgent a := by
  intro h; exact h.1

theorem WellFormedAgent.cr_smallBias {a : AgentState L K} :
    WellFormedAgent a → a.role = .cr → a.smallBias = defaultSmallBias := by
  intro h; exact h.2

theorem validInitial_well_formed_agent (c : Config (AgentState L K))
    (hvalid : validInitial c) :
  ∀ a ∈ c, WellFormedAgent a := by
  intro a ha
  rcases hvalid a ha with ⟨hphase, hrest⟩
  rcases hrest with ⟨hrole, hrest⟩
  rcases hrest with ⟨_hassigned, hrest⟩
  rcases hrest with ⟨_hopinions, _hsmall⟩
  constructor
  · intro htrans
    left
    have : a.phase = (⟨0, by decide⟩ : Fin 11) := hphase
    simp [this]
  · intro hcr
    rw [hrole] at hcr
    cases hcr

theorem WellFormedAgent.not_mcr_of_intermediate_phase {a : AgentState L K}
    (ha : WellFormedAgent a) (hlo : 1 ≤ a.phase.val) (hhi : a.phase.val ≤ 9) :
    a.role ≠ .mcr := by
  intro hmcr
  rcases ha.1 (Or.inl hmcr) with h0 | h10 <;> omega

theorem WellFormedAgent.not_cr_of_intermediate_phase {a : AgentState L K}
    (ha : WellFormedAgent a) (hlo : 1 ≤ a.phase.val) (hhi : a.phase.val ≤ 9) :
    a.role ≠ .cr := by
  intro hcr
  rcases ha.1 (Or.inr hcr) with h0 | h10 <;> omega

theorem well_formed_agent_of_not_transient (a : AgentState L K)
    (hmcr : a.role ≠ .mcr) (hcr : a.role ≠ .cr) :
    WellFormedAgent a := by
  constructor
  · intro htrans
    rcases htrans with hm | hc
    · exact False.elim (hmcr hm)
    · exact False.elim (hcr hc)
  · intro hc
    exact False.elim (hcr hc)

theorem well_formed_agent_of_eq_role_phase_smallBias {a b : AgentState L K}
    (ha : WellFormedAgent a)
    (hrole : b.role = a.role)
    (hphase : b.phase.val = a.phase.val)
    (hsmallBias : b.smallBias = a.smallBias) :
    WellFormedAgent b := by
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
    WellFormedAgent a → WellFormedAgent (advancePhase L K a) := by
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

@[simp] theorem stdCounterSubroutine_preserves_well_formed_agent_of_clock (a : AgentState L K)
    (hclock : a.role = .clock) :
    WellFormedAgent (stdCounterSubroutine L K a) := by
  have hrole : (stdCounterSubroutine L K a).role = .clock :=
    stdCounterSubroutine_clock_role_eq L K a hclock
  exact well_formed_agent_of_not_transient _
    (by simp [hrole]) (by simp [hrole])

theorem well_formed_agent_set_cr_default_of_phase_zero_or_ten (a : AgentState L K)
    (hphase : a.phase.val = 0 ∨ a.phase.val = 10) :
    WellFormedAgent ({ a with role := .cr, smallBias := defaultSmallBias }) := by
  constructor
  · intro _htrans
    simpa using hphase
  · intro _hcr
    simp [defaultSmallBias]

@[simp] private lemma phase10_zero_or_ten :
    (phase10 : Fin 11) = 0 ∨ (phase10 : Fin 11).val = 10 :=
  Or.inr rfl

theorem phaseInit_preserves_well_formed_agent (p : Fin 11) (a : AgentState L K) :
    WellFormedAgent a → WellFormedAgent (phaseInit L K p a) := by
  intro ha
  fin_cases p
  · simpa [phaseInit] using ha
  · unfold phaseInit
    simp [WellFormedAgent, RolePhaseInvariantAgent, defaultSmallBias, phase10] at ha ⊢
    split_ifs <;> simp_all

  · unfold phaseInit
    simp [WellFormedAgent, RolePhaseInvariantAgent, defaultSmallBias, phase10] at ha ⊢
    split_ifs <;> simp_all
  · unfold phaseInit
    simp [WellFormedAgent, RolePhaseInvariantAgent, defaultSmallBias] at ha ⊢
    cases hrole : a.role
    · simp_all
    · simp_all
    · simp_all
    · simpa [hrole] using ha.1 (by simp [hrole])
    · simpa [hrole] using ⟨ha.1 (by simp [hrole]), ha.2 (by simp [hrole])⟩
  · simpa [phaseInit] using ha
  · unfold phaseInit
    simp [WellFormedAgent, RolePhaseInvariantAgent, defaultSmallBias] at ha ⊢
    split_ifs <;> simp_all
  · unfold phaseInit
    simp [WellFormedAgent, RolePhaseInvariantAgent, defaultSmallBias] at ha ⊢
    split_ifs <;> simp_all
  · unfold phaseInit
    simp [WellFormedAgent, RolePhaseInvariantAgent, defaultSmallBias] at ha ⊢
    split_ifs <;> simp_all
  · simpa [phaseInit, WellFormedAgent, RolePhaseInvariantAgent, defaultSmallBias] using ha
  · unfold phaseInit
    simp [WellFormedAgent, RolePhaseInvariantAgent, defaultSmallBias, phase10] at ha ⊢
    split_ifs <;> simp_all
  · simpa [phaseInit] using
      enterPhase10_preserves_well_formed_agent (L := L) (K := K) a ha

theorem advancePhaseWithInit_preserves_well_formed_agent_of_phase_pos (a : AgentState L K)
    (hpos : 1 ≤ a.phase.val) :
    WellFormedAgent a → WellFormedAgent (advancePhaseWithInit L K a) := by
  intro ha
  unfold advancePhaseWithInit
  exact phaseInit_preserves_well_formed_agent (L := L) (K := K)
    (advancePhase L K a).phase (advancePhase L K a)
    (advancePhase_preserves_well_formed_agent_of_phase_pos
      (L := L) (K := K) a hpos ha)

set_option linter.flexible false in
theorem runInitsBetween_preserves_well_formed_agent (oldP newP : ℕ) (a : AgentState L K) :
    WellFormedAgent a → WellFormedAgent (runInitsBetween L K oldP newP a) := by
  intro ha
  unfold runInitsBetween
  let lst := (List.range 11).filter (fun k => oldP < k ∧ k ≤ newP)
  have h_ind : ∀ (a' : AgentState L K), WellFormedAgent a' →
      WellFormedAgent
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
  · unfold runInitsBetween
    have h1 : (List.range 11).filter (fun k => 0 < k ∧ k ≤ 1) = [1] := by decide
    have h2 : (List.range 11).filter (fun k => 1 < k ∧ k ≤ 1) = [] := by decide
    rw [h1, h2]
    simp
  · unfold runInitsBetween
    have h1 : (List.range 11).filter (fun k => 0 < k ∧ k ≤ 2) = [1, 2] := by decide
    have h2 : (List.range 11).filter (fun k => 1 < k ∧ k ≤ 2) = [2] := by decide
    rw [h1, h2]
    simp
  · unfold runInitsBetween
    have h1 : (List.range 11).filter (fun k => 0 < k ∧ k ≤ 3) = [1, 2, 3] := by decide
    have h2 : (List.range 11).filter (fun k => 1 < k ∧ k ≤ 3) = [2, 3] := by decide
    rw [h1, h2]
    simp
  · unfold runInitsBetween
    have h1 : (List.range 11).filter (fun k => 0 < k ∧ k ≤ 4) = [1, 2, 3, 4] := by decide
    have h2 : (List.range 11).filter (fun k => 1 < k ∧ k ≤ 4) = [2, 3, 4] := by decide
    rw [h1, h2]
    simp
  · unfold runInitsBetween
    have h1 : (List.range 11).filter (fun k => 0 < k ∧ k ≤ 5) = [1, 2, 3, 4, 5] := by decide
    have h2 : (List.range 11).filter (fun k => 1 < k ∧ k ≤ 5) = [2, 3, 4, 5] := by decide
    rw [h1, h2]
    simp
  · unfold runInitsBetween
    have h1 : (List.range 11).filter (fun k => 0 < k ∧ k ≤ 6) = [1, 2, 3, 4, 5, 6] := by decide
    have h2 : (List.range 11).filter (fun k => 1 < k ∧ k ≤ 6) = [2, 3, 4, 5, 6] := by decide
    rw [h1, h2]
    simp
  · unfold runInitsBetween
    have h1 : (List.range 11).filter (fun k => 0 < k ∧ k ≤ 7) = [1, 2, 3, 4, 5, 6, 7] := by decide
    have h2 : (List.range 11).filter (fun k => 1 < k ∧ k ≤ 7) = [2, 3, 4, 5, 6, 7] := by decide
    rw [h1, h2]
    simp
  · unfold runInitsBetween
    have h1 :
        (List.range 11).filter (fun k => 0 < k ∧ k ≤ 8) =
          [1, 2, 3, 4, 5, 6, 7, 8] := by decide
    have h2 :
        (List.range 11).filter (fun k => 1 < k ∧ k ≤ 8) =
          [2, 3, 4, 5, 6, 7, 8] := by decide
    rw [h1, h2]
    simp
  · unfold runInitsBetween
    have h1 :
        (List.range 11).filter (fun k => 0 < k ∧ k ≤ 9) =
          [1, 2, 3, 4, 5, 6, 7, 8, 9] := by decide
    have h2 :
        (List.range 11).filter (fun k => 1 < k ∧ k ≤ 9) =
          [2, 3, 4, 5, 6, 7, 8, 9] := by decide
    rw [h1, h2]
    simp
  · unfold runInitsBetween
    have h1 :
        (List.range 11).filter (fun k => 0 < k ∧ k ≤ 10) =
          [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] := by decide
    have h2 :
        (List.range 11).filter (fun k => 1 < k ∧ k ≤ 10) =
          [2, 3, 4, 5, 6, 7, 8, 9, 10] := by decide
    rw [h1, h2]
    simp

set_option linter.flexible false in
private theorem phaseInit_one_after_phase_update_transient_well_formed (p : Fin 11)
    (a : AgentState L K)
    (htrans : a.role = .mcr ∨ a.role = .cr) :
    WellFormedAgent (phaseInit L K ⟨1, by decide⟩ ({ a with phase := p })) := by
  unfold phaseInit
  simp [WellFormedAgent, RolePhaseInvariantAgent, defaultSmallBias, phase10]
  rcases htrans with hmcr | hcr
  · simp [hmcr]
  · simp [hcr]

private theorem phaseEpidemicUpdate_one_preserves_well_formed_agent (p : Fin 11)
    (a : AgentState L K) (hle : a.phase.val ≤ p.val) :
    WellFormedAgent a →
    WellFormedAgent (runInitsBetween L K a.phase.val p.val ({ a with phase := p })) := by
  intro ha
  by_cases hmcr : a.role = .mcr
  · rcases ha.1 (Or.inl hmcr) with hzero | hten
    · have hold : a.phase.val = 0 := hzero
      by_cases hpzero : p.val = 0
      · have hbase : WellFormedAgent ({ a with phase := p }) :=
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
      have hbase : WellFormedAgent ({ a with phase := p }) :=
        well_formed_agent_of_eq_role_phase_smallBias ha (by simp) (by simp [hten, hp]) (by simp)
      simpa [hten, hp] using
        runInitsBetween_preserves_well_formed_agent (L := L) (K := K) 10 10
          ({ a with phase := p }) hbase
  · by_cases hcr : a.role = .cr
    · rcases ha.1 (Or.inr hcr) with hzero | hten
      · have hold : a.phase.val = 0 := hzero
        by_cases hpzero : p.val = 0
        · have hbase : WellFormedAgent ({ a with phase := p }) :=
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
        have hbase : WellFormedAgent ({ a with phase := p }) :=
          well_formed_agent_of_eq_role_phase_smallBias ha (by simp) (by simp [hten, hp]) (by simp)
        simpa [hten, hp] using
          runInitsBetween_preserves_well_formed_agent (L := L) (K := K) 10 10
            ({ a with phase := p }) hbase
    · have hbase : WellFormedAgent ({ a with phase := p }) :=
        well_formed_agent_of_not_transient _ (by simp [hmcr]) (by simp [hcr])
      exact runInitsBetween_preserves_well_formed_agent (L := L) (K := K)
        a.phase.val p.val ({ a with phase := p }) hbase

theorem phaseEpidemicUpdate_preserves_well_formed_agent (s t : AgentState L K) :
    WellFormedAgent s → WellFormedAgent t →
    WellFormedAgent (phaseEpidemicUpdate L K s t).1 ∧
    WellFormedAgent (phaseEpidemicUpdate L K s t).2 := by
  intro hs ht
  unfold phaseEpidemicUpdate
  set p := max s.phase t.phase with hp
  generalize hs0 :
      runInitsBetween L K s.phase.val p.val ({ s with phase := p }) = s0
  generalize ht0 :
      runInitsBetween L K t.phase.val p.val ({ t with phase := p }) = t0
  have hle_s : s.phase.val ≤ p.val := by
    rw [hp]
    exact Nat.le_max_left _ _
  have hle_t : t.phase.val ≤ p.val := by
    rw [hp]
    exact Nat.le_max_right _ _
  have hs0_wf : WellFormedAgent s0 := by
    rw [← hs0]
    exact phaseEpidemicUpdate_one_preserves_well_formed_agent (L := L) (K := K)
      p s hle_s hs
  have ht0_wf : WellFormedAgent t0 := by
    rw [← ht0]
    exact phaseEpidemicUpdate_one_preserves_well_formed_agent (L := L) (K := K)
      p t hle_t ht
  by_cases h10 :
      (s.phase.val < 10 ∨ t.phase.val < 10) ∧
        (s0.phase.val = 10 ∨ t0.phase.val = 10)
  · exact ⟨
      by
        simpa [h10, hs0, ht0] using
          phase10EpidemicEntry_preserves_well_formed_agent (L := L) (K := K) s s0 hs0_wf,
      by
        simpa [h10, hs0, ht0] using
          phase10EpidemicEntry_preserves_well_formed_agent (L := L) (K := K) t t0 ht0_wf⟩
  · exact ⟨by simpa [h10, hs0, ht0] using hs0_wf,
      by simpa [h10, hs0, ht0] using ht0_wf⟩

/-! ### Per-phase preservation of `WellFormedAgent` -/

set_option linter.flexible false in
theorem phase3CancelSplit_preserves_well_formed_agent (s t : AgentState L K) :
    WellFormedAgent s → WellFormedAgent t →
    WellFormedAgent (phase3CancelSplit L K s t).1 ∧
    WellFormedAgent (phase3CancelSplit L K s t).2 := by
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

set_option linter.flexible false in
theorem cancelSplit_preserves_well_formed_agent (s t : AgentState L K) :
    WellFormedAgent s → WellFormedAgent t →
    WellFormedAgent (cancelSplit L K s t).1 ∧
    WellFormedAgent (cancelSplit L K s t).2 := by
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

set_option linter.flexible false in
theorem absorbConsume_preserves_well_formed_agent (s t : AgentState L K) :
    WellFormedAgent s → WellFormedAgent t →
    WellFormedAgent (absorbConsume L K s t).1 ∧
    WellFormedAgent (absorbConsume L K s t).2 := by
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
    WellFormedAgent s → WellFormedAgent t →
    WellFormedAgent (Phase0Transition L K s t).1 ∧
    WellFormedAgent (Phase0Transition L K s t).2 := by
  intro hs ht
  -- Mirror the let-chain of Phase0Transition, proving WellFormedAgent at each step.
  -- Rule 1
  let s1 := if s.role = .mcr ∧ t.role = .mcr then
    { s with role := .main, smallBias := addSmallBias s.smallBias t.smallBias } else s
  let t1 := if s.role = .mcr ∧ t.role = .mcr then
    { t with role := .cr, smallBias := ⟨3, by decide⟩ } else t
  have hs1 : WellFormedAgent s1 := by
    dsimp [s1]; split_ifs with h
    · exact well_formed_agent_of_not_transient _ (by simp) (by simp)
    · exact hs
  have ht1 : WellFormedAgent t1 := by
    dsimp [t1]; split_ifs with h
    · exact well_formed_agent_set_cr_default_of_phase_zero_or_ten _
        (by simpa using ht.1 (Or.inl h.2))
    · exact ht
  -- Rule 2
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
  have hs2 : WellFormedAgent s2 := by
    dsimp [s2]; split_ifs with hleft hright
    · exact well_formed_agent_set_cr_default_of_phase_zero_or_ten _
        (by simpa using hs1.1 (Or.inl hleft.1))
    · exact well_formed_agent_of_not_transient _ (by simp [hright.2.1]) (by simp [hright.2.1])
    · exact hs1
  have ht2 : WellFormedAgent t2 := by
    dsimp [t2]; split_ifs with hleft hright
    · exact well_formed_agent_of_not_transient _ (by simp [hleft.2.1]) (by simp [hleft.2.1])
    · exact well_formed_agent_set_cr_default_of_phase_zero_or_ten _
        (by simpa using ht1.1 (Or.inl hright.1))
    · exact ht1
  -- Rule 3
  let s3 := if s2.role = .mcr ∧ t2.role ≠ .main ∧ t2.role ≠ .mcr ∧ ¬ t2.assigned then
              { s2 with role := .main }
            else if t2.role = .mcr ∧ s2.role ≠ .main ∧ s2.role ≠ .mcr ∧ ¬ s2.assigned then
              { s2 with assigned := true }
            else s2
  let t3 := if s2.role = .mcr ∧ t2.role ≠ .main ∧ t2.role ≠ .mcr ∧ ¬ t2.assigned then
              { t2 with assigned := true }
            else if t2.role = .mcr ∧ s2.role ≠ .main ∧ s2.role ≠ .mcr ∧ ¬ s2.assigned then
              { t2 with role := .main }
            else t2
  have hs3 : WellFormedAgent s3 := by
    dsimp [s3]; split_ifs with h1 h2
    · exact well_formed_agent_of_not_transient _ (by simp) (by simp)
    · exact well_formed_agent_of_eq_role_phase_smallBias hs2 (by simp) (by simp) (by simp)
    · exact hs2
  have ht3 : WellFormedAgent t3 := by
    dsimp [t3]; split_ifs with h1 h2
    · exact well_formed_agent_of_eq_role_phase_smallBias ht2 (by simp) (by simp) (by simp)
    · exact well_formed_agent_of_not_transient _ (by simp) (by simp)
    · exact ht2
  -- Rule 3' (trivial passthrough)
  let s3' := s3
  let t3' := t3
  have hs3' : WellFormedAgent s3' := by dsimp [s3']; exact hs3
  have ht3' : WellFormedAgent t3' := by dsimp [t3']; exact ht3
  -- Rule 4: CR + CR → clock + reserve
  let s4 := if s3'.role = .cr ∧ t3'.role = .cr then
    { s3' with role := .clock, counter := ⟨50 * (L + 1), by omega⟩ } else s3'
  let t4 := if s3'.role = .cr ∧ t3'.role = .cr then
    { t3' with role := .reserve } else t3'
  have hs4 : WellFormedAgent s4 := by
    dsimp [s4]; split_ifs with h
    · exact well_formed_agent_of_not_transient _ (by simp) (by simp)
    · exact hs3'
  have ht4 : WellFormedAgent t4 := by
    dsimp [t4]; split_ifs with h
    · exact well_formed_agent_of_not_transient _ (by simp) (by simp)
    · exact ht3'
  -- Rule 5: clock + clock → stdCounterSubroutine
  let s5 := if s4.role = .clock ∧ t4.role = .clock then stdCounterSubroutine L K s4 else s4
  let t5 := if s4.role = .clock ∧ t4.role = .clock then stdCounterSubroutine L K t4 else t4
  have hs5 : WellFormedAgent s5 := by
    dsimp [s5]; split_ifs with h
    · exact stdCounterSubroutine_preserves_well_formed_agent_of_clock _ h.1
    · exact hs4
  have ht5 : WellFormedAgent t5 := by
    dsimp [t5]; split_ifs with h
    · exact stdCounterSubroutine_preserves_well_formed_agent_of_clock _ h.2
    · exact ht4
  exact ⟨hs5, ht5⟩

theorem Phase1Transition_preserves_well_formed_agent (s t : AgentState L K) :
    WellFormedAgent s → WellFormedAgent t →
    WellFormedAgent (Phase1Transition L K s t).1 ∧
    WellFormedAgent (Phase1Transition L K s t).2 := by
  intro hs ht
  constructor
  · by_cases hmain : s.role = .main ∧ t.role = .main
    · simpa [Phase1Transition, hmain, clockCounterStep, hmain.1] using
        well_formed_agent_of_not_transient
          ({ s with smallBias := (avgFin7 s.smallBias t.smallBias).1 })
          (by simp [hmain.1]) (by simp [hmain.1])
    · by_cases hclock : s.role = .clock
      · simpa [Phase1Transition, hmain, clockCounterStep, hclock] using
          stdCounterSubroutine_preserves_well_formed_agent_of_clock (L := L) (K := K) s hclock
      · simpa [Phase1Transition, hmain, clockCounterStep, hclock] using hs
  · by_cases hmain : s.role = .main ∧ t.role = .main
    · simpa [Phase1Transition, hmain, clockCounterStep, hmain.2] using
        well_formed_agent_of_not_transient
          ({ t with smallBias := (avgFin7 s.smallBias t.smallBias).2 })
          (by simp [hmain.2]) (by simp [hmain.2])
    · by_cases hclock : t.role = .clock
      · simpa [Phase1Transition, hmain, clockCounterStep, hclock] using
          stdCounterSubroutine_preserves_well_formed_agent_of_clock (L := L) (K := K) t hclock
      · simpa [Phase1Transition, hmain, clockCounterStep, hclock] using ht

set_option linter.flexible false in
theorem Phase2Transition_preserves_well_formed_agent_of_phase_pos (s t : AgentState L K)
    (hs_pos : 1 ≤ s.phase.val) (ht_pos : 1 ≤ t.phase.val) :
    WellFormedAgent s → WellFormedAgent t →
    WellFormedAgent (Phase2Transition L K s t).1 ∧
    WellFormedAgent (Phase2Transition L K s t).2 := by
  intro hs ht
  unfold Phase2Transition
  let univ := opinionsUnion s.opinions t.opinions
  let s' := { s with opinions := univ }
  let t' := { t with opinions := univ }
  have hs' : WellFormedAgent s' :=
    well_formed_agent_of_eq_role_phase_smallBias hs (by simp [s']) (by simp [s']) (by simp [s'])
  have ht' : WellFormedAgent t' :=
    well_formed_agent_of_eq_role_phase_smallBias ht (by simp [t']) (by simp [t']) (by simp [t'])
  have hs'_pos : 1 ≤ s'.phase.val := by simp [s', hs_pos]
  have ht'_pos : 1 ≤ t'.phase.val := by simp [t', ht_pos]
  change WellFormedAgent
      (if hasMinusOne univ && hasPlusOne univ then
        (advancePhaseWithInit L K s', advancePhaseWithInit L K t')
      else if hasPlusOne univ then
        ({ s' with output := .A }, { t' with output := .A })
      else if hasMinusOne univ then
        ({ s' with output := .B }, { t' with output := .B })
      else if univ.val = 2 then
        ({ s' with output := .T }, { t' with output := .T })
      else
        (s', t')).1 ∧
    WellFormedAgent
      (if hasMinusOne univ && hasPlusOne univ then
        (advancePhaseWithInit L K s', advancePhaseWithInit L K t')
      else if hasPlusOne univ then
        ({ s' with output := .A }, { t' with output := .A })
      else if hasMinusOne univ then
        ({ s' with output := .B }, { t' with output := .B })
      else if univ.val = 2 then
        ({ s' with output := .T }, { t' with output := .T })
      else
        (s', t')).2
  by_cases hboth : hasMinusOne univ && hasPlusOne univ
  · simp [hboth, advancePhaseWithInit_preserves_well_formed_agent_of_phase_pos, hs', ht',
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
        · simp [hplus, hminus]
          exact well_formed_agent_of_eq_role_phase_smallBias hs' (by rfl) (by rfl) (by rfl)
        · simp [hplus, hminus]
          exact well_formed_agent_of_eq_role_phase_smallBias ht' (by rfl) (by rfl) (by rfl)
      · by_cases htwo : univ.val = 2
        · constructor
          · simp [hplus, hminus, htwo]
            exact well_formed_agent_of_eq_role_phase_smallBias hs' (by rfl) (by rfl) (by rfl)
          · simp [hplus, hminus, htwo]
            exact well_formed_agent_of_eq_role_phase_smallBias ht' (by rfl) (by rfl) (by rfl)
        · simp [hplus, hminus, htwo, hs', ht']

theorem Phase2Transition_preserves_well_formed_agent (s t : AgentState L K)
    (hs_phase : s.phase.val = 2) (ht_phase : t.phase.val = 2) :
    WellFormedAgent s → WellFormedAgent t →
    WellFormedAgent (Phase2Transition L K s t).1 ∧
    WellFormedAgent (Phase2Transition L K s t).2 := by
  exact Phase2Transition_preserves_well_formed_agent_of_phase_pos (L := L) (K := K)
    s t (by omega) (by omega)

set_option linter.flexible false in
theorem Phase3Transition_preserves_well_formed_agent (s t : AgentState L K) :
    WellFormedAgent s → WellFormedAgent t →
    WellFormedAgent (Phase3Transition L K s t).1 ∧
    WellFormedAgent (Phase3Transition L K s t).2 := by
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
    let hVal := max s1.hour.val (min L (t1.minute.val / K))
    have h_hour_lt : hVal < L + 1 := by
      exact (Nat.max_lt).mpr ⟨s1.hour.2, Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩
    { s1 with hour := ⟨hVal, h_hour_lt⟩ }
  else if t1.role = .main ∧ t1.bias = .zero ∧ s1.role = .clock then
    s1
  else s1
  let t2 := if s1.role = .main ∧ s1.bias = .zero ∧ t1.role = .clock then
    t1
  else if t1.role = .main ∧ t1.bias = .zero ∧ s1.role = .clock then
    let hVal := max t1.hour.val (min L (s1.minute.val / K))
    have h_hour_lt : hVal < L + 1 := by
      exact (Nat.max_lt).mpr ⟨t1.hour.2, Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩
    { t1 with hour := ⟨hVal, h_hour_lt⟩ }
  else t1
  have hs1 : WellFormedAgent s1 := by
    by_cases hclock : s.role = .clock ∧ t.role = .clock
    · by_cases hneq : s.minute ≠ t.minute
      · simpa [s1, hclock, hneq] using
          well_formed_agent_of_eq_role_phase_smallBias hs (by exact hclock.1.symm)
            (by simp) (by simp)
      · by_cases hmax : s.minute.val < K * (L + 1)
        · simpa [s1, hclock, hneq, hmax] using
            well_formed_agent_of_eq_role_phase_smallBias hs (by exact hclock.1.symm)
              (by simp) (by simp)
        · simpa [s1, hclock, hneq, hmax] using
            stdCounterSubroutine_preserves_well_formed_agent_of_clock (L := L) (K := K) s hclock.1
    · simpa [s1, hclock] using hs
  have ht1 : WellFormedAgent t1 := by
    by_cases hclock : s.role = .clock ∧ t.role = .clock
    · by_cases hneq : s.minute ≠ t.minute
      · simpa [t1, hclock, hneq] using
          well_formed_agent_of_eq_role_phase_smallBias ht (by exact hclock.2.symm)
            (by simp) (by simp)
      · by_cases hmax : s.minute.val < K * (L + 1)
        · simpa [t1, hclock, hneq, hmax] using ht
        · simpa [t1, hclock, hneq, hmax] using
            stdCounterSubroutine_preserves_well_formed_agent_of_clock (L := L) (K := K) t hclock.2
    · simpa [t1, hclock] using ht
  have hs2 : WellFormedAgent s2 := by
    dsimp [s2]
    by_cases hleft : s1.role = .main ∧ s1.bias = .zero ∧ t1.role = .clock
    · simp [hleft]
      exact well_formed_agent_of_eq_role_phase_smallBias hs1 (by exact hleft.1.symm)
        (by simp) (by simp)
    · by_cases hright : t1.role = .main ∧ t1.bias = .zero ∧ s1.role = .clock
      · simp [hright, hs1]
      · simp [hleft, hright, hs1]
  have ht2 : WellFormedAgent t2 := by
    dsimp [t2]
    by_cases hleft : s1.role = .main ∧ s1.bias = .zero ∧ t1.role = .clock
    · simp [hleft, ht1]
    · by_cases hright : t1.role = .main ∧ t1.bias = .zero ∧ s1.role = .clock
      · simp [hright]
        exact well_formed_agent_of_eq_role_phase_smallBias ht1 (by exact hright.1.symm)
          (by simp) (by simp)
      · simp [hleft, hright, ht1]
  change WellFormedAgent
      (if s2.role = .main ∧ t2.role = .main then phase3CancelSplit L K s2 t2 else (s2, t2)).1 ∧
    WellFormedAgent
      (if s2.role = .main ∧ t2.role = .main then phase3CancelSplit L K s2 t2 else (s2, t2)).2
  by_cases hmain : s2.role = .main ∧ t2.role = .main
  · simp [hmain, phase3CancelSplit_preserves_well_formed_agent, hs2, ht2]
  · simp [hmain, hs2, ht2]

theorem Phase4Transition_preserves_well_formed_agent_of_phase_pos (s t : AgentState L K)
    (hs_pos : 1 ≤ s.phase.val) (ht_pos : 1 ≤ t.phase.val) :
    WellFormedAgent s → WellFormedAgent t →
    WellFormedAgent (Phase4Transition L K s t).1 ∧
    WellFormedAgent (Phase4Transition L K s t).2 := by
  intro hs ht
  unfold Phase4Transition
  dsimp
  split_ifs
  · exact ⟨advancePhaseWithInit_preserves_well_formed_agent_of_phase_pos (L := L) (K := K)
      s hs_pos hs,
      advancePhaseWithInit_preserves_well_formed_agent_of_phase_pos (L := L) (K := K)
      t ht_pos ht⟩
  · exact ⟨hs, ht⟩

theorem Phase4Transition_preserves_well_formed_agent (s t : AgentState L K)
    (hs_phase : s.phase.val = 4) (ht_phase : t.phase.val = 4) :
    WellFormedAgent s → WellFormedAgent t →
    WellFormedAgent (Phase4Transition L K s t).1 ∧
    WellFormedAgent (Phase4Transition L K s t).2 := by
  exact Phase4Transition_preserves_well_formed_agent_of_phase_pos (L := L) (K := K)
    s t (by omega) (by omega)

theorem Phase5Transition_preserves_well_formed_agent (s t : AgentState L K) :
    WellFormedAgent s → WellFormedAgent t →
    WellFormedAgent (Phase5Transition L K s t).1 ∧
    WellFormedAgent (Phase5Transition L K s t).2 := by
  intro hs ht
  unfold Phase5Transition
  dsimp
  constructor <;>
      split_ifs <;>
      simp_all [WellFormedAgent, RolePhaseInvariantAgent, defaultSmallBias,
        stdCounterSubroutine_preserves_well_formed_agent_of_clock] <;>
      split_ifs <;> simp_all

/-- A Reserve-fueled split either leaves both agents unchanged or makes the Reserve a Main
agent and only rewrites the Main agent's bias; neither touches the role, phase or small bias
that well-formedness reads, except the new role `main`, which is never transient. -/
private lemma doSplit_preserves_well_formed_agent (r m : AgentState L K)
    (hr : WellFormedAgent r) (hm : WellFormedAgent m) :
    WellFormedAgent (doSplit L K r m).1 ∧ WellFormedAgent (doSplit L K r m).2 := by
  unfold doSplit
  split
  · split_ifs
    · exact ⟨well_formed_agent_of_not_transient _ (by simp) (by simp), hm⟩
    · exact ⟨hr, hm⟩
    · exact ⟨hr, hm⟩
  · exact ⟨hr, hm⟩

theorem Phase6Transition_preserves_well_formed_agent (s t : AgentState L K) :
    WellFormedAgent s → WellFormedAgent t →
    WellFormedAgent (Phase6Transition L K s t).1 ∧
    WellFormedAgent (Phase6Transition L K s t).2 := by
  intro hs ht
  have hst := doSplit_preserves_well_formed_agent (L := L) (K := K) s t hs ht
  have hts := doSplit_preserves_well_formed_agent (L := L) (K := K) t s ht hs
  have hclock : ∀ x : AgentState L K, WellFormedAgent x →
      WellFormedAgent (if x.role = .clock then stdCounterSubroutine L K x else x) := by
    intro x hx
    split_ifs with hc
    · exact stdCounterSubroutine_preserves_well_formed_agent_of_clock x hc
    · exact hx
  unfold Phase6Transition
  dsimp only
  constructor
  · apply hclock
    split_ifs
    · exact hst.1
    · exact hts.2
    · exact hs
  · apply hclock
    split_ifs
    · exact hst.2
    · exact hts.1
    · exact ht

theorem Phase7Transition_preserves_well_formed_agent (s t : AgentState L K) :
    WellFormedAgent s → WellFormedAgent t →
    WellFormedAgent (Phase7Transition L K s t).1 ∧
    WellFormedAgent (Phase7Transition L K s t).2 := by
  intro hs ht
  unfold Phase7Transition
  dsimp
  by_cases hmain : s.role = .main ∧ t.role = .main
  · rcases cancelSplit_preserves_well_formed_agent (L := L) (K := K) s t hs ht with ⟨hcs, hct⟩
    have : ¬(s.role = .clock) := by simp [hmain.1]
    have : ¬(t.role = .clock) := by simp [hmain.2]
    simp [hmain, hcs, hct, *]
  · by_cases hsclock : s.role = .clock
    · by_cases htclock : t.role = .clock
      · simp [hsclock, htclock,
          stdCounterSubroutine_preserves_well_formed_agent_of_clock]
      · simp [hsclock, htclock,
          stdCounterSubroutine_preserves_well_formed_agent_of_clock, ht]
    · by_cases htclock : t.role = .clock
      · simp [hsclock, htclock,
          stdCounterSubroutine_preserves_well_formed_agent_of_clock, hs]
      · simp [hmain, hsclock, htclock, hs, ht]

theorem Phase8Transition_preserves_well_formed_agent (s t : AgentState L K) :
    WellFormedAgent s → WellFormedAgent t →
    WellFormedAgent (Phase8Transition L K s t).1 ∧
    WellFormedAgent (Phase8Transition L K s t).2 := by
  intro hs ht
  unfold Phase8Transition
  dsimp
  by_cases hmain : s.role = .main ∧ t.role = .main
  · rcases absorbConsume_preserves_well_formed_agent (L := L) (K := K) s t hs ht with ⟨has, hat⟩
    have : ¬(s.role = .clock) := by simp [hmain.1]
    have : ¬(t.role = .clock) := by simp [hmain.2]
    simp [hmain, has, hat, *]
  · by_cases hsclock : s.role = .clock
    · by_cases htclock : t.role = .clock
      · simp [hsclock, htclock,
          stdCounterSubroutine_preserves_well_formed_agent_of_clock]
      · simp [hsclock, htclock,
          stdCounterSubroutine_preserves_well_formed_agent_of_clock, ht]
    · by_cases htclock : t.role = .clock
      · simp [hsclock, htclock,
          stdCounterSubroutine_preserves_well_formed_agent_of_clock, hs]
      · simp [hmain, hsclock, htclock, hs, ht]

theorem Phase9Transition_preserves_well_formed_agent (s t : AgentState L K)
    (hs_phase : s.phase.val = 9) (ht_phase : t.phase.val = 9) :
    WellFormedAgent s → WellFormedAgent t →
    WellFormedAgent (Phase9Transition L K s t).1 ∧
    WellFormedAgent (Phase9Transition L K s t).2 := by
  unfold Phase9Transition
  exact Phase2Transition_preserves_well_formed_agent_of_phase_pos (L := L) (K := K)
    s t (by omega) (by omega)

theorem Phase10Transition_preserves_well_formed_agent (s t : AgentState L K) :
    WellFormedAgent s → WellFormedAgent t →
    WellFormedAgent (Phase10Transition L K s t).1 ∧
    WellFormedAgent (Phase10Transition L K s t).2 := by
  intro hs ht
  unfold Phase10Transition
  dsimp
  constructor <;>
    split_ifs <;>
    simp_all [WellFormedAgent, RolePhaseInvariantAgent, defaultSmallBias]

theorem Transition_preserves_well_formed (s t : AgentState L K) :
    WellFormedAgent s → WellFormedAgent t →
    WellFormedAgent (Transition L K s t).1 ∧
    WellFormedAgent (Transition L K s t).2 := by
  intro hs ht
  rcases phaseEpidemicUpdate_preserves_well_formed_agent (L := L) (K := K) s t hs ht with
    ⟨hs_ep, ht_ep⟩
  unfold Transition
  simp only [finishPhase10Entry_well_formed_agent_iff]
  let s' := (phaseEpidemicUpdate L K s t).1
  let t' := (phaseEpidemicUpdate L K s t).2
  have ht_pos_of_s_pos : 1 ≤ s'.phase.val → 1 ≤ t'.phase.val := by
    intro hpos
    exact phaseEpidemicUpdate_right_phase_pos_of_left_phase_pos (L := L) (K := K)
      s t hpos
  change WellFormedAgent (match s'.phase with
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
    WellFormedAgent (match s'.phase with
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
    (ha : WellFormedAgent a) (hphase : 1 ≤ a.phase.val) :
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
    (h_c : ∀ a ∈ c, WellFormedAgent a)
    (h_step : (NonuniformMajority L K).StepRel c c') :
    ∀ a ∈ c', WellFormedAgent a := by
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

theorem reachable_preserves_well_formed_agents (init c : Config (AgentState L K))
    (h_init : validInitial init)
    (h_reach : Protocol.Reachable (NonuniformMajority L K) init c) :
    ∀ a ∈ c, WellFormedAgent a := by
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

/-! ### Per-phase preservation of `RolePhaseInvariantAgent` -/

theorem role_phase_invariant_agent_of_not_transient (a : AgentState L K)
    (hmcr : a.role ≠ .mcr) (hcr : a.role ≠ .cr) :
    RolePhaseInvariantAgent a := by
  intro htrans
  rcases htrans with hm | hc
  · exact False.elim (hmcr hm)
  · exact False.elim (hcr hc)

theorem role_phase_invariant_agent_of_eq_role_phase {a b : AgentState L K}
    (ha : RolePhaseInvariantAgent a)
    (hrole : b.role = a.role)
    (hphase : b.phase.val = a.phase.val) :
    RolePhaseInvariantAgent b := by
  intro htrans
  have htrans_a : a.role = .mcr ∨ a.role = .cr := by
    simpa [hrole] using htrans
  rcases ha htrans_a with h0 | h10
  · left; omega
  · right; omega

@[simp] theorem stdCounterSubroutine_preserves_role_phase_invariant_of_clock (a : AgentState L K)
    (hclock : a.role = .clock) :
    RolePhaseInvariantAgent (stdCounterSubroutine L K a) := by
  have hrole : (stdCounterSubroutine L K a).role = .clock :=
    stdCounterSubroutine_clock_role_eq L K a hclock
  exact role_phase_invariant_agent_of_not_transient _
    (by simp [hrole]) (by simp [hrole])

set_option linter.flexible false in
theorem doSplit_preserves_role_phase_invariant (r m : AgentState L K) :
    RolePhaseInvariantAgent r → RolePhaseInvariantAgent m →
    RolePhaseInvariantAgent (doSplit L K r m).1 ∧
    RolePhaseInvariantAgent (doSplit L K r m).2 := by
  intro hr hm
  unfold doSplit
  match m.bias with
  | .zero =>
      simp [hr, hm]
  | .dyadic sgn j =>
      by_cases hguard : ¬r.hour.val = L ∧ j < r.hour
      · by_cases hpos : j.val < L
        · simp [hguard, hpos]
          exact ⟨role_phase_invariant_agent_of_not_transient _ (by simp) (by simp),
            role_phase_invariant_agent_of_eq_role_phase hm (by simp) (by simp)⟩
        · simp [hguard, hpos, hr, hm]
      · simp [hguard, hr, hm]

set_option linter.flexible false in
theorem cancelSplit_preserves_role_phase_invariant (s t : AgentState L K) :
    RolePhaseInvariantAgent s → RolePhaseInvariantAgent t →
    RolePhaseInvariantAgent (cancelSplit L K s t).1 ∧
    RolePhaseInvariantAgent (cancelSplit L K s t).2 := by
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
      have hs_bias : ∀ b : Bias L, RolePhaseInvariantAgent ({ s with bias := b }) := by
        intro b
        exact role_phase_invariant_agent_of_eq_role_phase hs (by simp) (by simp)
      have ht_bias : ∀ b : Bias L, RolePhaseInvariantAgent ({ t with bias := b }) := by
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

set_option linter.flexible false in
theorem absorbConsume_preserves_role_phase_invariant (s t : AgentState L K) :
    RolePhaseInvariantAgent s → RolePhaseInvariantAgent t →
    RolePhaseInvariantAgent (absorbConsume L K s t).1 ∧
    RolePhaseInvariantAgent (absorbConsume L K s t).2 := by
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
      by_cases hleft : i < j ∧ s.full = false
      · simp [hleft]
        exact ⟨role_phase_invariant_agent_of_eq_role_phase hs (by simp) (by simp),
          role_phase_invariant_agent_of_eq_role_phase ht (by simp) (by simp)⟩
      · by_cases hright : j < i ∧ t.full = false
        · simp [hleft, hright]
          exact ⟨role_phase_invariant_agent_of_eq_role_phase hs (by simp) (by simp),
            role_phase_invariant_agent_of_eq_role_phase ht (by simp) (by simp)⟩
        · simp [hleft, hright, hs, ht]
  | .dyadic .neg i, .dyadic .pos j =>
      by_cases hleft : i < j ∧ s.full = false
      · simp [hleft]
        exact ⟨role_phase_invariant_agent_of_eq_role_phase hs (by simp) (by simp),
          role_phase_invariant_agent_of_eq_role_phase ht (by simp) (by simp)⟩
      · by_cases hright : j < i ∧ t.full = false
        · simp [hleft, hright]
          exact ⟨role_phase_invariant_agent_of_eq_role_phase hs (by simp) (by simp),
            role_phase_invariant_agent_of_eq_role_phase ht (by simp) (by simp)⟩
        · simp [hleft, hright, hs, ht]

theorem Phase1Transition_preserves_role_phase_invariant (s t : AgentState L K) :
    RolePhaseInvariantAgent s → RolePhaseInvariantAgent t →
    RolePhaseInvariantAgent (Phase1Transition L K s t).1 ∧
    RolePhaseInvariantAgent (Phase1Transition L K s t).2 := by
  intro hs ht
  constructor
  · intro h_or
    by_cases hmain : s.role = .main ∧ t.role = .main
    · exfalso
      simpa [Phase1Transition, hmain, clockCounterStep] using h_or
    · by_cases hclock : s.role = .clock
      · exfalso
        simpa [Phase1Transition, hmain, clockCounterStep, hclock] using h_or
      · simpa [Phase1Transition, hmain, clockCounterStep, hclock] using
          hs (by simpa [Phase1Transition, hmain, clockCounterStep, hclock] using h_or)
  · intro h_or
    by_cases hmain : s.role = .main ∧ t.role = .main
    · exfalso
      simpa [Phase1Transition, hmain, clockCounterStep] using h_or
    · by_cases hclock : t.role = .clock
      · exfalso
        simpa [Phase1Transition, hmain, clockCounterStep, hclock] using h_or
      · simpa [Phase1Transition, hmain, clockCounterStep, hclock] using
          ht (by simpa [Phase1Transition, hmain, clockCounterStep, hclock] using h_or)

-- Phase 2/9 conditionally advance phase; preservation requires a stronger joint invariant
-- (e.g. role ∈ {mcr, cr} implies opinions = 0). Deferred to paper §5 wellformedness work.

-- Phase 7/8 use cancelSplit/absorbConsume + stdCounterSubroutine; preservation needs
-- explicit case analysis on s.role and t.role + bias-match. Deferred — DS dispatch.

theorem Phase5Transition_preserves_role_phase_invariant (s t : AgentState L K) :
    RolePhaseInvariantAgent s → RolePhaseInvariantAgent t →
    RolePhaseInvariantAgent (Phase5Transition L K s t).1 ∧
    RolePhaseInvariantAgent (Phase5Transition L K s t).2 := by
    intro hs ht
    refine ⟨?_, ?_⟩ <;> intro h_or
    · unfold Phase5Transition at h_or ⊢
      dsimp at h_or ⊢
      split_ifs at h_or ⊢
      all_goals simp_all [stdCounterSubroutine_preserves_role_phase_invariant_of_clock]
      all_goals simpa using hs h_or
    · unfold Phase5Transition at h_or ⊢
      dsimp at h_or ⊢
      split_ifs at h_or ⊢
      all_goals simp_all [stdCounterSubroutine_preserves_role_phase_invariant_of_clock]
      all_goals simpa using ht h_or

theorem Phase6Transition_preserves_role_phase_invariant (s t : AgentState L K) :
    RolePhaseInvariantAgent s → RolePhaseInvariantAgent t →
    RolePhaseInvariantAgent (Phase6Transition L K s t).1 ∧
    RolePhaseInvariantAgent (Phase6Transition L K s t).2 := by
  intro hs ht
  unfold Phase6Transition
  dsimp
  by_cases hleft : s.role = .reserve ∧ t.role = .main ∧ t.bias ≠ .zero
  · rcases doSplit_preserves_role_phase_invariant (L := L) (K := K) s t hs ht with ⟨hds, hdt⟩
    have ht_nc : ¬(t.role = .clock) := by simp [hleft.2.1]
    by_cases hsclock : (doSplit L K s t).1.role = .clock
    · simp [hleft, hsclock, ht_nc,
        stdCounterSubroutine_preserves_role_phase_invariant_of_clock, hdt]
    · simp [hleft, hsclock, ht_nc, hds, hdt]
  · by_cases hright : t.role = .reserve ∧ s.role = .main ∧ s.bias ≠ .zero
    · rcases doSplit_preserves_role_phase_invariant (L := L) (K := K) t s ht hs with ⟨hdt, hds⟩
      have hs_nc : ¬(s.role = .clock) := by simp [hright.2.1]
      by_cases htclock : (doSplit L K t s).1.role = .clock
      · simp [hright, hs_nc, htclock,
          stdCounterSubroutine_preserves_role_phase_invariant_of_clock, hds]
      · simp [hright, hs_nc, htclock, hds, hdt]
    · by_cases hsclock : s.role = .clock
      · by_cases htclock : t.role = .clock
        · simp [hsclock, htclock,
            stdCounterSubroutine_preserves_role_phase_invariant_of_clock]
        · simp [hsclock, htclock,
            stdCounterSubroutine_preserves_role_phase_invariant_of_clock, ht]
      · by_cases htclock : t.role = .clock
        · simp [hsclock, htclock,
            stdCounterSubroutine_preserves_role_phase_invariant_of_clock, hs]
        · simp [hleft, hright, hsclock, htclock, hs, ht]

theorem Phase7Transition_preserves_role_phase_invariant (s t : AgentState L K) :
    RolePhaseInvariantAgent s → RolePhaseInvariantAgent t →
    RolePhaseInvariantAgent (Phase7Transition L K s t).1 ∧
    RolePhaseInvariantAgent (Phase7Transition L K s t).2 := by
  intro hs ht
  unfold Phase7Transition
  dsimp
  by_cases hmain : s.role = .main ∧ t.role = .main
  · rcases cancelSplit_preserves_role_phase_invariant (L := L) (K := K) s t hs ht with ⟨hcs, hct⟩
    have : ¬(s.role = .clock) := by simp [hmain.1]
    have : ¬(t.role = .clock) := by simp [hmain.2]
    simp [hmain, hcs, hct, *]
  · by_cases hsclock : s.role = .clock
    · by_cases htclock : t.role = .clock
      · simp [hsclock, htclock,
          stdCounterSubroutine_preserves_role_phase_invariant_of_clock]
      · simp [hsclock, htclock,
          stdCounterSubroutine_preserves_role_phase_invariant_of_clock, ht]
    · by_cases htclock : t.role = .clock
      · simp [hsclock, htclock,
          stdCounterSubroutine_preserves_role_phase_invariant_of_clock, hs]
      · simp [hmain, hsclock, htclock, hs, ht]

theorem Phase8Transition_preserves_role_phase_invariant (s t : AgentState L K) :
    RolePhaseInvariantAgent s → RolePhaseInvariantAgent t →
    RolePhaseInvariantAgent (Phase8Transition L K s t).1 ∧
    RolePhaseInvariantAgent (Phase8Transition L K s t).2 := by
  intro hs ht
  unfold Phase8Transition
  dsimp
  by_cases hmain : s.role = .main ∧ t.role = .main
  · rcases absorbConsume_preserves_role_phase_invariant (L := L) (K := K) s t hs ht with ⟨has, hat⟩
    have : ¬(s.role = .clock) := by simp [hmain.1]
    have : ¬(t.role = .clock) := by simp [hmain.2]
    simp [hmain, has, hat, *]
  · by_cases hsclock : s.role = .clock
    · by_cases htclock : t.role = .clock
      · simp [hsclock, htclock,
          stdCounterSubroutine_preserves_role_phase_invariant_of_clock]
      · simp [hsclock, htclock,
          stdCounterSubroutine_preserves_role_phase_invariant_of_clock, ht]
    · by_cases htclock : t.role = .clock
      · simp [hsclock, htclock,
          stdCounterSubroutine_preserves_role_phase_invariant_of_clock, hs]
      · simp [hmain, hsclock, htclock, hs, ht]

theorem Phase10Transition_preserves_role_phase_invariant (s t : AgentState L K) :
    RolePhaseInvariantAgent s → RolePhaseInvariantAgent t →
    RolePhaseInvariantAgent (Phase10Transition L K s t).1 ∧
    RolePhaseInvariantAgent (Phase10Transition L K s t).2 := by
  intro hs ht
  refine ⟨?_, ?_⟩ <;> intro h_or
  · unfold Phase10Transition at h_or ⊢
    dsimp at h_or ⊢
    split_ifs at h_or ⊢
    all_goals simp_all
    all_goals simpa using hs h_or
  · unfold Phase10Transition at h_or ⊢
    dsimp at h_or ⊢
    split_ifs at h_or ⊢
    all_goals simp_all
    all_goals simpa using ht h_or

/-- The mean waiting time for Phase 0 milestones satisfies
    `meanTime ≤ n * log(n)`.

    Proof sketch: `meanTime = Σ_{M=1}^{n} n(n-1)/(M(2n-M-1))`.
    Each term ≤ `n/M` (since `(n-1)/(2n-M-1) ≤ 1`), so
    `meanTime ≤ n * H_n ≤ n * (log n + 1) ≤ n * log n` for `n ≥ 8`. -/
private lemma harmonic_le_one_add_log' :
    ∀ n : ℕ, 1 ≤ n →
      (Finset.range n).sum (fun k => ((k : ℝ) + 1)⁻¹) ≤ 1 + Real.log (n : ℝ) := by
  intro n hn; induction n with
  | zero => omega
  | succ m ih =>
    rw [Finset.sum_range_succ]; by_cases hm0 : m = 0
    · subst hm0; simp [Real.log_one]
    · have hm_pos : 1 ≤ m := by omega
      have hm_c : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (by omega)
      have hm1_c : (0 : ℝ) < (m : ℝ) + 1 := by linarith
      specialize ih hm_pos
      -- 1/(m+1) ≤ log((m+1)/m) from log(t) ≥ 1-1/t
      have h_inv_le : ((m : ℝ) + 1)⁻¹ ≤ Real.log (((m : ℝ) + 1) / (m : ℝ)) := by
        -- We need: log(t) ≥ 1 - 1/t for t = (m+1)/m > 0
        -- Equivalently: log(t) ≥ 1 - 1/t
        -- From exp(y) ≥ 1 + y applied to y = 1/t - 1:
        --   exp(1/t - 1) ≥ 1/t, so exp(-log t) ≥ 1/t is trivial,
        --   but we need: log(t) + 1/t - 1 ≥ 0
        -- From add_one_le_exp applied to y = -(log t):
        --   1 - log(t) ≤ exp(-log t) = 1/t
        --   So log(t) ≥ 1 - 1/t
        set t := ((m : ℝ) + 1) / (m : ℝ) with ht_def
        have ht_pos : (0 : ℝ) < t := div_pos hm1_c hm_c
        have h_key : 1 - Real.log t ≤ t⁻¹ := by
          have h1 : -(Real.log t) + 1 ≤ Real.exp (-(Real.log t)) :=
            Real.add_one_le_exp _
          rw [Real.exp_neg, Real.exp_log ht_pos] at h1
          linarith
        have h_tinv : t⁻¹ = (m : ℝ) / ((m : ℝ) + 1) := by
          rw [ht_def, inv_div]
        rw [h_tinv] at h_key
        have h_eq : 1 - (m : ℝ) / ((m : ℝ) + 1) = ((m : ℝ) + 1)⁻¹ := by
          rw [inv_eq_one_div]
          have : (m : ℝ) / ((m : ℝ) + 1) + 1 / ((m : ℝ) + 1) = 1 := by
            rw [← add_div]
            simp [add_comm, ne_of_gt hm1_c]
          linarith
        linarith
      calc (Finset.range m).sum (fun k => ((k : ℝ) + 1)⁻¹) + ((m : ℝ) + 1)⁻¹
          ≤ (1 + Real.log (m : ℝ)) + Real.log (((m : ℝ) + 1) / (m : ℝ)) := by linarith
        _ = 1 + (Real.log (m : ℝ) + Real.log (((m : ℝ) + 1) / (m : ℝ))) := by ring
        _ = 1 + Real.log ((m : ℝ) * (((m : ℝ) + 1) / (m : ℝ))) := by
            rw [← Real.log_mul (ne_of_gt hm_c) (ne_of_gt (div_pos hm1_c hm_c))]
        _ = 1 + Real.log ((m : ℝ) + 1) := by
            congr 1; rw [mul_div_cancel₀ _ (ne_of_gt hm_c)]
        _ = 1 + Real.log ((m + 1 : ℕ) : ℝ) := by push_cast; ring_nf
private lemma log_succ_le_harmonic' :
    ∀ n : ℕ, 1 ≤ n →
      Real.log ((n : ℝ) + 1) ≤ (Finset.range n).sum (fun k => ((k : ℝ) + 1)⁻¹) := by
  intro n hn; induction n with
  | zero => omega
  | succ m ih =>
    rw [Finset.sum_range_succ]; by_cases hm0 : m = 0
    · subst hm0; simp
      -- Goal: Real.log (1 + 1) ≤ 1, i.e., log(2) ≤ 1
      -- Equivalently: 2 ≤ exp(1), which follows from add_one_le_exp
      have h2 : (1 : ℝ) + 1 > 0 := by norm_num
      rw [Real.log_le_iff_le_exp h2]
      linarith [Real.add_one_le_exp (1 : ℝ)]
    · have hm_pos : 1 ≤ m := by omega
      have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
      have hm2 : (0 : ℝ) < (m : ℝ) + 2 := by linarith
      specialize ih hm_pos
      -- log((m+2)/(m+1)) ≤ 1/(m+1) from log(1+x) ≤ x
      have h_log_le : Real.log (((m : ℝ) + 2) / ((m : ℝ) + 1)) ≤ ((m : ℝ) + 1)⁻¹ := by
        have h_ratio : ((m : ℝ) + 2) / ((m : ℝ) + 1) = 1 + ((m : ℝ) + 1)⁻¹ := by
          have hne : ((m : ℝ) + 1) ≠ 0 := ne_of_gt hm1
          field_simp
          ring
        rw [h_ratio]
        have h_inv_pos : (0 : ℝ) < ((m : ℝ) + 1)⁻¹ := inv_pos.mpr hm1
        rw [Real.log_le_iff_le_exp (by linarith)]
        linarith [Real.add_one_le_exp ((m : ℝ) + 1)⁻¹]
      calc Real.log ((m + 1 : ℕ) + 1 : ℝ)
          = Real.log ((m : ℝ) + 2) := by push_cast; ring_nf
        _ = Real.log (((m : ℝ) + 1) * (((m : ℝ) + 2) / ((m : ℝ) + 1))) := by
            rw [mul_div_cancel₀ _ (ne_of_gt hm1)]
        _ = Real.log ((m : ℝ) + 1) + Real.log (((m : ℝ) + 2) / ((m : ℝ) + 1)) := by
            rw [Real.log_mul (ne_of_gt hm1) (ne_of_gt (div_pos hm2 hm1))]
        _ ≤ (Finset.range m).sum (fun k => ((k : ℝ) + 1)⁻¹) + ((m : ℝ) + 1)⁻¹ := by linarith
private lemma reindex_harmonic' (n : ℕ) :
    (Finset.range n).sum (fun k => ((n : ℝ) - (k : ℝ))⁻¹) =
    (Finset.range n).sum (fun k => ((k : ℝ) + 1)⁻¹) := by
  rw [← Finset.sum_range_reflect (fun j => ((j : ℝ) + 1)⁻¹) n]
  apply Finset.sum_congr rfl; intro k hk; rw [Finset.mem_range] at hk
  congr 1
  -- Goal: (n : ℝ) - (k : ℝ) = ((n - 1 - k : ℕ) : ℝ) + 1
  -- n - 1 - k + 1 = n - k as naturals (since k < n)
  have h_nat : n - 1 - k + 1 = n - k := by omega
  have : ((n - 1 - k : ℕ) : ℝ) + 1 = ((n - k : ℕ) : ℝ) := by
    rw [← h_nat]; push_cast; ring
  rw [this, Nat.cast_sub hk.le]
/-- With MCR-only (homogeneous) milestone probabilities M*(M-1)/(n*(n-1)),
    the mean time is Σ n*(n-1)/(M*(M-1)) for M=2..n.
    By the telescoping identity 1/(M*(M-1)) = 1/(M-1) - 1/M,
    this equals n*(n-1)*(1 - 1/(n-1)) = n*(n-1)*(n-2)/(n-1) = n*(n-2).
    In particular, meanTime ≤ n². -/
private lemma phase0MilestonePhase_meanTime_eq (n : ℕ) (hn : 2 ≤ n) :
    (phase0MilestonePhase (L := L) (K := K) n hn).meanTime = ((n : ℝ) - 1) ^ 2 := by
  simp only [MilestonePhase.meanTime, phase0MilestonePhase_k, phase0MilestonePhase_p]
  set g : ℕ → ℝ := fun j => (n : ℝ) * ((n : ℝ) - 1) / ((n : ℝ) - (j : ℝ))
  have h_eq : ∀ (i : Fin (n - 1)),
      (phase0MilestoneProb n i)⁻¹ = g (i.val + 1) - g i.val := by
    intro i; unfold phase0MilestoneProb; simp only []
    have hi : i.val < n - 1 := i.isLt
    have hM_cast : ((n - 1 - i.val + 1 : ℕ) : ℝ) = (n : ℝ) - (i.val : ℝ) := by
      rw [show n - 1 - i.val + 1 = n - i.val from by omega,
          Nat.cast_sub (by omega : i.val ≤ n)]
    rw [inv_div, hM_cast]
    set A := (n : ℝ) - (i.val : ℝ); set B := A - 1
    have hA : A ≠ 0 := by
      simp only [A]; linarith [show (i.val : ℝ) < (n : ℝ) from by exact_mod_cast (show i.val < n by omega)]
    have hB : B ≠ 0 := by
      simp only [B, A]; linarith [show (i.val : ℝ) + 1 < (n : ℝ) from by exact_mod_cast (show i.val + 1 < n by omega)]
    simp only [g]
    rw [show ((i.val + 1 : ℕ) : ℝ) = (i.val : ℝ) + 1 from by push_cast; ring]
    rw [show (n : ℝ) - ((i.val : ℝ) + 1) = B from by simp only [B, A]; ring]
    rw [div_sub_div _ _ hB hA]; congr 1 <;> ring
  simp_rw [h_eq]
  -- Use calc to avoid rw matching issue with bound variables in ∑
  calc ∑ x : Fin (n - 1), (g (↑x + 1) - g ↑x)
      = (Finset.range (n - 1)).sum (fun j => g (j + 1) - g j) :=
        Fin.sum_univ_eq_sum_range (fun j => g (j + 1) - g j) (n - 1)
    _ = g (n - 1) - g 0 := Finset.sum_range_sub g (n - 1)
    _ = ((n : ℝ) - 1) ^ 2 := by
        simp only [g, Nat.cast_zero, sub_zero]
        rw [show ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 from by rw [Nat.cast_sub (by omega : 1 ≤ n)]; simp]
        rw [show (n : ℝ) - ((n : ℝ) - 1) = 1 from by ring, div_one]
        rw [mul_div_cancel_left₀ _ (show (n : ℝ) ≠ 0 from by exact_mod_cast (show n ≠ 0 by omega))]
        ring

private lemma phase0MilestonePhase_meanTime_le (n : ℕ) (hn : 8 ≤ n) :
    (phase0MilestonePhase (L := L) (K := K) n (by omega)).meanTime ≤
      (n : ℝ) ^ 2 := by
  rw [phase0MilestonePhase_meanTime_eq n (by omega)]
  nlinarith [sq_nonneg ((n : ℝ) - 1), show (1 : ℝ) ≤ (n : ℝ) from by exact_mod_cast (show 1 ≤ n by omega)]

private lemma phase0MilestonePhase_pMin_ge (n : ℕ) (hn : 2 ≤ n) :
    2 / ((n : ℝ) * ((n : ℝ) - 1)) ≤
      (phase0MilestonePhase (L := L) (K := K) n hn).pMin := by
  simp only [MilestonePhase.pMin, phase0MilestonePhase_k, phase0MilestonePhase_p]
  have : Nonempty (Fin (n - 1)) := ⟨⟨0, by omega⟩⟩
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hn1_pos : (0 : ℝ) < (n : ℝ) - 1 := by
    linarith [show (2 : ℝ) ≤ (n : ℝ) from by exact_mod_cast hn]
  apply le_ciInf; intro i
  unfold phase0MilestoneProb; simp only []
  apply div_le_div_of_nonneg_right _ (le_of_lt (mul_pos hn_pos hn1_pos))
  nlinarith [show (2 : ℝ) ≤ ((n - 1 - i.val + 1 : ℕ) : ℝ) from by
    exact_mod_cast (show 2 ≤ n - 1 - i.val + 1 from by omega)]

/-- With MCR-only probabilities, pMin ≥ 2/(n*(n-1)) and meanTime = (n-1)².
    The compound bound pMin * meanTime * (n-1-log n) ≥ 2*log n
    reduces to (n-1)² ≥ (2n-1)*log n, which holds for n ≥ 8. -/
private lemma phase0MilestonePhase_pMin_meanTime_logn_bound (n : ℕ) (hn : 8 ≤ n) :
    2 * Real.log (n : ℝ) ≤
      (phase0MilestonePhase (L := L) (K := K) n (by omega)).pMin *
      (phase0MilestonePhase (L := L) (K := K) n (by omega)).meanTime *
      ((n : ℝ) - 1 - Real.log (n : ℝ)) := by
  have h_pmin := phase0MilestonePhase_pMin_ge (L := L) (K := K) n (by omega)
  have h_mean := phase0MilestonePhase_meanTime_eq (L := L) (K := K) n (by omega)
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hn1_pos : (0 : ℝ) < (n : ℝ) - 1 := by
    linarith [show (8 : ℝ) ≤ (n : ℝ) from by exact_mod_cast hn]
  -- pMin * meanTime ≥ 2/(n*(n-1)) * (n-1)² = 2*(n-1)/n
  have h_prod : 2 * ((n : ℝ) - 1) / (n : ℝ) ≤
      (phase0MilestonePhase (L := L) (K := K) n (by omega)).pMin *
      (phase0MilestonePhase (L := L) (K := K) n (by omega)).meanTime := by
    rw [h_mean]
    have h_eq : 2 * ((n : ℝ) - 1) / (n : ℝ) =
        2 / ((n : ℝ) * ((n : ℝ) - 1)) * ((n : ℝ) - 1) ^ 2 := by field_simp
    rw [h_eq]
    exact mul_le_mul_of_nonneg_right h_pmin (by positivity)
  -- log(n) ≤ n/2 - 1 for n ≥ 8
  have hlog_bound : Real.log (n : ℝ) ≤ (n : ℝ) / 2 - 1 := by
    rw [Real.log_le_iff_le_exp (by positivity)]
    have hn8 : (8 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    calc (n : ℝ) ≤ 4 * (n : ℝ) - 24 := by linarith
      _ ≤ 8 * (1 + ((n : ℝ) - 8) / 2) := by ring_nf; linarith
      _ ≤ Real.exp 3 * (1 + ((n : ℝ) - 8) / 2) := by
          apply mul_le_mul_of_nonneg_right _ (by linarith)
          have : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nsmul]; simp [nsmul_eq_mul]
          rw [this]; nlinarith [Real.add_one_le_exp (1 : ℝ), sq_nonneg (Real.exp 1)]
      _ ≤ Real.exp 3 * Real.exp (((n : ℝ) - 8) / 2) := by
          apply mul_le_mul_of_nonneg_left _ (Real.exp_pos 3).le
          linarith [Real.add_one_le_exp (((n : ℝ) - 8) / 2)]
      _ = Real.exp ((n : ℝ) / 2 - 1) := by rw [← Real.exp_add]; congr 1; ring
  have h_diff_pos : (0 : ℝ) < (n : ℝ) - 1 - Real.log (n : ℝ) := by linarith
  calc 2 * Real.log (n : ℝ)
      ≤ 2 * ((n : ℝ) - 1) / (n : ℝ) * ((n : ℝ) - 1 - Real.log (n : ℝ)) := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hn_pos]
        nlinarith [sq_nonneg ((n : ℝ) - 1)]
    _ ≤ _ := mul_le_mul_of_nonneg_right h_prod (le_of_lt h_diff_pos)
/-- **Doty et al. Lemma 5.1** (Phase 0 convergence — MCR elimination).

With MCR-only milestone probabilities M*(M-1)/(n*(n-1)), the mean time is
O(n²) (not O(n log n) as in the heterogeneous case). We use λ = n in the
Janson tail bound, giving time hypothesis O(n³) and failure ≤ 1/n². -/
theorem lemma_5_1_population_splitting
    (init : Config (AgentState L K))
    (hinit : validInitial init)
    (hn : 8 ≤ init.card)
    (t : ℕ) (ht : ((init.card : ℝ) ^ 3) < ↑t) :
    ((NonuniformMajority L K).transitionKernel ^ t) init
        {c : Config (AgentState L K) |
          ¬(phase0MilestonePhase (L := L) (K := K) init.card (by omega)).Post c} ≤
      ENNReal.ofReal (1 / ((init.card : ℝ) ^ 2)) := by
  have hcard_pos : (0 : ℝ) < (init.card : ℝ) := by
    exact_mod_cast (by omega : 0 < init.card)
  have hlog_pos : 0 < Real.log (init.card : ℝ) := by
    exact Real.log_pos (by exact_mod_cast (show 1 < init.card by omega))
  let mp : MilestonePhase (NonuniformMajority L K) :=
    phase0MilestonePhase (L := L) (K := K) init.card (by omega)
  -- All milestones are initially unmet
  have hPre_milestones : ∀ i, ¬mp.milestone i init := by
    intro i hm
    dsimp [mp, phase0MilestonePhase, phase0Milestone] at hm
    rcases hm with h_mcr | h_card
    · have hmcr : mcrCount init = init.card := by
        unfold mcrCount
        congr 1
        exact Multiset.filter_eq_self.mpr (fun a ha => (hinit a ha).2.1)
      rw [hmcr] at h_mcr
      dsimp [mcrThreshold] at h_mcr
      have : i.val < init.card - 1 := i.2
      omega
    · rcases h_card with h_ne | ⟨a, ha_mem, ha_mcr, ha_phase⟩
      · exact h_ne rfl
      · have h_phase0 := (hinit a ha_mem).1
        have : a.phase.val = 0 := by rw [h_phase0]
        exact absurd this ha_phase
  -- Key bound: meanTime ≤ n²
  have h_meanTime_le := phase0MilestonePhase_meanTime_le (L := L) (K := K)
    init.card (by omega : 8 ≤ init.card)
  -- Key bound: pMin * meanTime * (n - 1 - log n) ≥ 2 * log n
  have h_compound := phase0MilestonePhase_pMin_meanTime_logn_bound (L := L) (K := K)
    init.card (by omega : 8 ≤ init.card)
  -- Use λ = n (init.card) in the Janson tail bound.
  -- Need: n * meanTime ≤ t
  have hn_ge_one : (1 : ℝ) ≤ (init.card : ℝ) := by exact_mod_cast (show 1 ≤ init.card by omega)
  have ht_bound : (init.card : ℝ) * mp.meanTime ≤ (t : ℝ) := by
    calc (init.card : ℝ) * mp.meanTime
        ≤ (init.card : ℝ) * ((init.card : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left h_meanTime_le (by linarith)
      _ = (init.card : ℝ) ^ 3 := by ring
      _ ≤ (t : ℝ) := le_of_lt ht
  -- ε bound: exp(-pMin * meanTime * f(n)) ≤ 1/n²
  -- where f(n) = n - 1 - log n.
  -- Strategy: show the exponent is ≤ -2 log n, so
  -- exp(exponent) ≤ exp(-2 log n) = 1/n².
  have hε_bound : Real.exp (-mp.pMin * mp.meanTime *
      ((init.card : ℝ) - 1 - Real.log (init.card : ℝ))) ≤
      1 / ((init.card : ℝ) ^ 2) := by
    have h_exp_neg_log : Real.exp (-2 * Real.log (init.card : ℝ)) =
        1 / ((init.card : ℝ) ^ 2) := by
      rw [neg_mul, Real.exp_neg,
        show (2 : ℝ) * Real.log (init.card : ℝ) =
          Real.log ((init.card : ℝ) ^ 2) from by rw [Real.log_pow]; ring,
        Real.exp_log (by positivity : (0 : ℝ) < (init.card : ℝ) ^ 2),
        one_div]
    rw [← h_exp_neg_log]
    apply Real.exp_le_exp.mpr
    -- Need: -pMin * meanTime * (n - 1 - log n) ≤ -2 * log n
    -- i.e.: 2 * log n ≤ pMin * meanTime * (n - 1 - log n)
    linarith
  -- Apply milestone_hitting_time_bound with λ = init.card
  have h_conv := milestone_hitting_time_bound mp init hPre_milestones
    (init.card : ℝ) hn_ge_one t ht_bound
  exact le_trans h_conv (ENNReal.ofReal_le_ofReal hε_bound)
/-- **Doty et al. Lemma 5.2** (Phase 0 role distribution).

By the end of Phase 0, with high probability `1 − O(1/n²)`:
  - `|RoleMCR | = 0`
  - `(n/2)(1−ε) ≤ |M| ≤ (n/2)(1+ε)`
  - `|C|, |R| ≥ (n/4)(1−ε)`

And deterministically (if Phase 1 initializes without error):
  `n/3 ≤ |M| ≤ 2n/3`, `n/6 ≤ |R| ≤ 2n/3`, `2 ≤ |C| ≤ n/3`.

This statement records the high-probability tail for the Phase 0 outcome
on a probability space `(Ω, μ)`. The proof (relying on Lemma 5.1 plus the
`RoleCR → Clock | Reserve` coupling) is deferred. -/
theorem lemma_5_2_phase_zero_partition
    (init : Config (AgentState L K))
    (hinit : validInitial init) (hn : 8 ≤ init.card)
    (t : ℕ) (ht : (12.5 * Real.log (init.card : ℝ)) < ↑t) :
    ∀ᵐ c ∂((NonuniformMajority L K).transitionKernel ^ t) init,
      ∀ a ∈ c, (a.role = .main ∨ a.role = .reserve ∨ a.role = .clock) ∨
        a.phase.val = 0 ∨ a.phase.val = 10 := by
  change ∀ᵐ c ∂((nonuniformTransitionKernel L K ^ t) init), _
  have hreach := ae_nonuniformReachable_transitionKernel_pow
    (L := L) (K := K) init t
  filter_upwards [hreach] with c hc
  intro a ha
  have hwf := reachable_preserves_well_formed_agents (L := L) (K := K) init c hinit hc a ha
  have hrpi : RolePhaseInvariantAgent a := hwf.1
  by_cases hmain : a.role = .main
  · left; exact Or.inl hmain
  by_cases hres : a.role = .reserve
  · left; exact Or.inr (Or.inl hres)
  by_cases hclk : a.role = .clock
  · left; exact Or.inr (Or.inr hclk)
  by_cases hmcr : a.role = .mcr
  · right; exact hrpi (Or.inl hmcr)
  · have : a.role = .cr := by
      cases h_role : a.role <;> simp_all
    right; exact hrpi (Or.inr this)

/-- **Doty et al. Lemma 5.3** (Phase 1 convergence).

At the end of Phase 1, with high probability `1 − O(1/n²)`:
  - if `|g| ≥ 0.025·|M|`: the protocol stabilizes to the correct output
    in Phase 2 (no agents continue to Phase 3);
  - if `|g| < 0.025·|M|`: all agents have bias `∈ {−1, 0, +1}` and the
    total count of biased agents is `≤ 0.03·|M|`.

This is the discrete-averaging convergence bound.  The Lean proof uses
step-preservation (`ae_of_stepDistOrSelf_support_preserved`): the per-agent
`smallBias ∈ {2,3,4}` property holds at init (vacuously) and is preserved by
each transition rule, so it holds a.e. at all times. -/
theorem lemma_5_3_phase_one_concentration
    (init : Config (AgentState L K))
    (hinit : validInitial init) (hn : 8 ≤ init.card)
    (t : ℕ) (ht : (25 * Real.log (init.card : ℝ)) < ↑t) :
    ∀ᵐ c ∂((NonuniformMajority L K).transitionKernel ^ t) init,
      ∀ a ∈ c, 2 ≤ a.phase.val → a.phase.val ≤ 9 →
        a.smallBias.val ∈ ({2, 3, 4} : Finset ℕ) := by
  -- Use ae_of_stepDistOrSelf_support_preserved with Q = per-agent noerror.
  -- Q holds at init (vacuous: no agents at phase ≥ 2).
  -- Q is step-preserved: smallBias preserved for phase ≥ 2, new phase-2
  -- agents get noerror from phaseInit(2) (which error-jumps to 10 if bad).
  have hQ : ∀ c c' : Config (AgentState L K),
      (∀ a ∈ c, 2 ≤ a.phase.val → a.phase.val ≤ 9 →
        a.smallBias.val ∈ ({2, 3, 4} : Finset ℕ)) →
      c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support →
      ∀ a ∈ c', 2 ≤ a.phase.val → a.phase.val ≤ 9 →
        a.smallBias.val ∈ ({2, 3, 4} : Finset ℕ) := by
    -- Proof: stepDistOrSelf decomposition + per-output-agent case analysis.
    intro c c' hprev hsupp a ha hge2 hle9
    unfold Protocol.stepDistOrSelf at hsupp
    by_cases hsize : 2 ≤ c.card
    · rw [dif_pos hsize] at hsupp
      obtain ⟨⟨r₁, r₂⟩, heq⟩ := _root_.Ripple.PopulationProtocol.ExactMajority.Protocol.stepDist_support
        (NonuniformMajority L K) c hsize c' hsupp
      -- c' = scheduledStep = stepOrSelf c r₁ r₂
      subst heq
      unfold Protocol.scheduledStep Protocol.stepOrSelf at ha
      by_cases happ : Protocol.Applicable c r₁ r₂
      · rw [if_pos happ] at ha
        -- a ∈ c - {r₁, r₂} + {(δ r₁ r₂).1, (δ r₁ r₂).2}
        rw [Multiset.mem_add] at ha
        rcases ha with ha_res | ha_out
        · -- Residual: a ∈ c (unchanged)
          have ha_c := Multiset.mem_of_le (Multiset.sub_le_self _ _) ha_res
          exact hprev a ha_c hge2 hle9
        · -- Output: a = (δ r₁ r₂).1 or a = (δ r₁ r₂).2
          simp only [Multiset.insert_eq_cons, Multiset.mem_cons,
            Multiset.mem_singleton] at ha_out
          -- ha_out : a = (NonuniformMajority ..).δ r₁ r₂).1 ∨ ... .2
          -- δ = Transition, so work with Transition throughout.
          unfold Protocol.Applicable at happ
          have hr₁_mem : r₁ ∈ c := Multiset.mem_of_le happ (by simp)
          have hr₂_mem : r₂ ∈ c := Multiset.mem_of_le happ (by simp)
          -- Useful abbreviations for epidemic update
          set ep := phaseEpidemicUpdate L K r₁ r₂ with hep_def
          have hep_le_T := phaseEpidemicUpdate_phase_le_Transition_phase
            (L := L) (K := K) r₁ r₂
          have hep_small := phaseEpidemicUpdate_preserves_smallBias L K r₁ r₂
          -- Unify ep with phaseEpidemicUpdate in lemma types
          rw [← hep_def] at hep_le_T hep_small
          rcases ha_out with rfl | rfl
          · -- LEFT OUTPUT: a = (Transition L K r₁ r₂).1
            change (Transition L K r₁ r₂).1.smallBias.val ∈ ({2, 3, 4} : Finset ℕ)
            change 2 ≤ (Transition L K r₁ r₂).1.phase.val at hge2
            change (Transition L K r₁ r₂).1.phase.val ≤ 9 at hle9
            by_cases hr₁_ge2 : 2 ≤ r₁.phase.val
            · -- r₁.phase ≥ 2: Transition preserves smallBias from epidemic,
              -- epidemic preserves from r₁, and hprev gives the goal.
              have hep1_ge2 : 2 ≤ ep.1.phase.val := by
                simpa [hep_def] using
                  le_trans hr₁_ge2
                    (phaseEpidemicUpdate_phase_nondec (L := L) (K := K) r₁ r₂).1
              have hpres := Transition_preserves_epidemic_smallBias_left_of_phase_ge_two
                (L := L) (K := K) r₁ r₂ hep1_ge2
              have h_mono := Transition_phase_monotone (L := L) (K := K) r₁ r₂
              have hr₁_le9 : r₁.phase.val ≤ 9 := le_trans h_mono.1 hle9
              rw [show (Transition L K r₁ r₂).1.smallBias.val = r₁.smallBias.val from
                congr_arg Fin.val (hpres.trans hep_small.1)]
              exact hprev r₁ hr₁_mem hr₁_ge2 hr₁_le9
            · -- r₁.phase < 2
              push_neg at hr₁_ge2
              have hne10 : (Transition L K r₁ r₂).1.phase.val ≠ 10 := by omega
              by_cases hep1_ge2 : 2 ≤ ep.1.phase.val
              · -- Epidemic entered phase ≥ 2 from input < 2.
                have hep1_ne10 : ep.1.phase.val ≠ 10 := by
                  linarith [hep_le_T.1]
                have hnoerr := phaseEpidemicUpdate_left_smallBias_noerror_of_entered_not_ten
                  (L := L) (K := K) r₁ r₂ hr₁_ge2 hep1_ge2 hep1_ne10
                have hpres := Transition_preserves_epidemic_smallBias_left_of_phase_ge_two
                  (L := L) (K := K) r₁ r₂ hep1_ge2
                rw [show (Transition L K r₁ r₂).1.smallBias.val = ep.1.smallBias.val from
                  congr_arg Fin.val hpres]
                exact hnoerr
              · -- Epidemic.1 phase < 2: output ≤ 2, combined with ≥ 2 gives = 2.
                push_neg at hep1_ge2
                have hout_le2 :=
                  Transition_left_phase_le_two_of_epidemic_phase_lt_two_of_ne_ten
                    (L := L) (K := K) r₁ r₂ hep1_ge2 hne10
                have hout_eq2 : (Transition L K r₁ r₂).1.phase.val = 2 := by omega
                exact Transition_left_phase2_smallBias_noerror_of_input_lt_two
                  (L := L) (K := K) r₁ r₂ hr₁_ge2 hout_eq2
          · -- RIGHT OUTPUT: a = (Transition L K r₁ r₂).2
            change (Transition L K r₁ r₂).2.smallBias.val ∈ ({2, 3, 4} : Finset ℕ)
            change 2 ≤ (Transition L K r₁ r₂).2.phase.val at hge2
            change (Transition L K r₁ r₂).2.phase.val ≤ 9 at hle9
            by_cases hr₂_ge2 : 2 ≤ r₂.phase.val
            · -- r₂.phase ≥ 2: Transition preserves smallBias via epidemic.
              have hep1_ge2 : 2 ≤ ep.1.phase.val := by
                simpa [hep_def] using
                  le_trans (le_trans hr₂_ge2 (Nat.le_max_right r₁.phase.val r₂.phase.val))
                    (phaseEpidemicUpdate_left_phase_ge_max (L := L) (K := K) r₁ r₂)
              have hpres := Transition_preserves_epidemic_smallBias_right_of_dispatch_phase_ge_two
                (L := L) (K := K) r₁ r₂ hep1_ge2
              have h_mono := Transition_phase_monotone (L := L) (K := K) r₁ r₂
              have hr₂_le9 : r₂.phase.val ≤ 9 := le_trans h_mono.2 hle9
              rw [show (Transition L K r₁ r₂).2.smallBias.val = r₂.smallBias.val from
                congr_arg Fin.val (hpres.trans hep_small.2)]
              exact hprev r₂ hr₂_mem hr₂_ge2 hr₂_le9
            · -- r₂.phase < 2
              push_neg at hr₂_ge2
              have hne10 : (Transition L K r₁ r₂).2.phase.val ≠ 10 := by omega
              -- Derive epidemic.2 info: epidemic.2 ≤ Transition.2 ≤ 9, so ≠ 10
              have hep2_ne10 : ep.2.phase.val ≠ 10 := by
                linarith [hep_le_T.2]
              -- Also epidemic.1 ≠ 10 (both inputs < 10 → ten-or-neither)
              have hr₁_lt10 : r₁.phase.val < 10 := by
                have hr₁_le_ep2 : r₁.phase.val ≤ ep.2.phase.val := by
                  simpa [hep_def] using
                    le_trans (Nat.le_max_left r₁.phase.val r₂.phase.val)
                      (phaseEpidemicUpdate_right_phase_ge_max (L := L) (K := K) r₁ r₂)
                exact lt_of_le_of_lt hr₁_le_ep2
                  (lt_of_le_of_lt (le_trans hep_le_T.2 hle9) (by norm_num))
              have hep1_ne10 : ep.1.phase.val ≠ 10 := by
                have hboth := phaseEpidemicUpdate_phases_both_ten_or_neither
                  (L := L) (K := K) r₁ r₂ hr₁_lt10 (by omega)
                exact fun h => hep2_ne10 (hboth.mp h)
              by_cases hep1_ge2 : 2 ≤ ep.1.phase.val
              · -- Dispatch phase ≥ 2.
                -- Need epidemic.2 ≥ 2 for phaseEpidemicUpdate_right_..._of_entered_not_ten.
                have hep2_ge2 : 2 ≤ ep.2.phase.val := by
                  by_cases hr₁_ge2' : 2 ≤ r₁.phase.val
                  · -- r₁ ≥ 2: epidemic.2 ≥ max ≥ r₁ ≥ 2
                    simpa [hep_def] using
                      le_trans (le_trans hr₁_ge2' (Nat.le_max_left r₁.phase.val r₂.phase.val))
                        (phaseEpidemicUpdate_right_phase_ge_max (L := L) (K := K) r₁ r₂)
                  · -- r₁ < 2: both inputs < 2 ≤ 2 and both epidemic ≠ 10
                    -- → phases_eq → epidemic.2 = epidemic.1 ≥ 2
                    push_neg at hr₁_ge2'
                    have hphases_eq :=
                      phaseEpidemicUpdate_phases_eq_of_phases_le_two_not_ten
                        (L := L) (K := K) r₁ r₂ (by omega) (by omega)
                        hep1_ne10 hep2_ne10
                    rw [← hep_def] at hphases_eq
                    rwa [← hphases_eq]
                have hnoerr :=
                  phaseEpidemicUpdate_right_smallBias_noerror_of_entered_not_ten
                    (L := L) (K := K) r₁ r₂ hr₂_ge2 hep2_ge2 hep2_ne10
                have hpres :=
                  Transition_preserves_epidemic_smallBias_right_of_dispatch_phase_ge_two
                    (L := L) (K := K) r₁ r₂ hep1_ge2
                rw [show (Transition L K r₁ r₂).2.smallBias.val = ep.2.smallBias.val from
                  congr_arg Fin.val hpres]
                exact hnoerr
              · -- Epidemic.1 phase < 2: output.2 ≤ 2, combined with ≥ 2 gives = 2.
                push_neg at hep1_ge2
                have hout_le2 :=
                  Transition_right_phase_le_two_of_epidemic_phase_lt_two_of_ne_ten
                    (L := L) (K := K) r₁ r₂ hep1_ge2 hne10
                have hout_eq2 : (Transition L K r₁ r₂).2.phase.val = 2 := by omega
                exact Transition_right_phase2_smallBias_noerror_of_input_lt_two
                  (L := L) (K := K) r₁ r₂ hr₂_ge2 hout_eq2
      · rw [if_neg happ] at ha
        exact hprev a ha hge2 hle9
    · rw [dif_neg hsize] at hsupp
      rw [PMF.mem_support_pure_iff] at hsupp
      subst hsupp
      exact hprev a ha hge2 hle9
  have hQ0 : ∀ a ∈ init, 2 ≤ a.phase.val → a.phase.val ≤ 9 →
      a.smallBias.val ∈ ({2, 3, 4} : Finset ℕ) := by
    intro a ha hge2
    have := (hinit a ha).1
    have hval : a.phase.val = 0 := by simpa using congr_arg Fin.val this
    omega
  exact Protocol.ae_of_stepDistOrSelf_support_preserved
    (NonuniformMajority L K) _ hQ init hQ0 t
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

/-! ### Phase-3 epidemic convergence infrastructure

The Phase-3 epidemic spreading uses `phaseBelowCount 3` as potential.
Once at least one agent reaches phase ≥ 3, the phase-epidemic mechanism
ensures that any agent interacting with a phase-≥3 agent gets promoted
to phase ≥ 3 (since max(k, ≥3) ≥ 3). This is used by theorem_6_9. -/

section Phase3LowEpidemic

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

/-- Auxiliary: distinct members of a multiset form an applicable pair. -/
private lemma applicable_of_mem_ne3 {c : Config (AgentState L K)}
    {a b : AgentState L K} (ha : a ∈ c) (hb : b ∈ c) (hab : a ≠ b) :
    Protocol.Applicable c a b := by
  rw [Protocol.Applicable]
  rw [Multiset.le_iff_count]
  intro x
  by_cases hxa : x = a
  · subst x
    have ha_pos : 0 < Multiset.count a c := Multiset.count_pos.2 ha
    simp [hab, Nat.succ_le_iff, ha_pos]
  · by_cases hxb : x = b
    · subst x
      have hb_pos : 0 < Multiset.count b c := Multiset.count_pos.2 hb
      simp [hxa, Nat.succ_le_iff, hb_pos]
    · simp [hxa, hxb]

/-- Source predicate for Phase-3 epidemic: at least one agent has phase ≥ 3. -/
def hasSource3 (c : Config (AgentState L K)) : Prop :=
  ∃ a ∈ c, 3 ≤ a.phase.val

/-- Post condition for Phase-3 epidemic: all agents have phase ≥ 3. -/
def allPhaseGe3 (c : Config (AgentState L K)) : Prop :=
  ∀ a ∈ c, 3 ≤ a.phase.val

/-- `allPhaseGe3 c` holds iff `phaseBelowCount 3 c = 0`. -/
lemma allPhaseGe3_iff_phaseBelowCount_zero (c : Config (AgentState L K)) :
    allPhaseGe3 c ↔ phaseBelowCount 3 c = 0 := by
  unfold allPhaseGe3 phaseBelowCount
  constructor
  · intro h
    rw [Multiset.card_eq_zero, Multiset.filter_eq_nil]
    intro a ha
    simp only [decide_eq_true_eq, not_lt]
    exact h a ha
  · intro h a ha
    rw [Multiset.card_eq_zero, Multiset.filter_eq_nil] at h
    have := h a ha
    simp only [decide_eq_true_eq, not_lt] at this
    exact this

/-- Source-3 is preserved by the one-step stochastic support: phase monotonicity
ensures that once an agent reaches phase ≥ 3, it stays there. -/
lemma hasSource3_preserved_by_stepDistOrSelf
    (c c' : Config (AgentState L K))
    (hc : hasSource3 c) :
    c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support → hasSource3 c' := by
  intro hsupp
  obtain ⟨a, ha_mem, ha_phase⟩ := hc
  unfold Protocol.stepDistOrSelf at hsupp
  split_ifs at hsupp with h_size
  · obtain ⟨⟨r₁, r₂⟩, heq⟩ := Protocol.stepDist_support _ _ h_size _ hsupp
    subst heq
    show hasSource3 (Protocol.scheduledStep (NonuniformMajority L K) c (r₁, r₂))
    unfold Protocol.scheduledStep Protocol.stepOrSelf
    split_ifs with h_app
    · change ∃ a' ∈ c - {r₁, r₂} + {(Transition L K r₁ r₂).1,
        (Transition L K r₁ r₂).2}, 3 ≤ a'.phase.val
      by_cases ha_r1 : a = r₁
      · subst ha_r1
        exact ⟨(Transition L K a r₂).1,
          Multiset.mem_add.mpr (Or.inr (Multiset.mem_cons_self _ _)),
          le_trans ha_phase (Transition_phase_monotone (L := L) (K := K) a r₂).1⟩
      · by_cases ha_r2 : a = r₂
        · subst ha_r2
          exact ⟨(Transition L K r₁ a).2,
            Multiset.mem_add.mpr (Or.inr (by
              simp only [Multiset.insert_eq_cons]
              exact Multiset.mem_cons.mpr (Or.inr (Multiset.mem_singleton.mpr rfl)))),
            le_trans ha_phase (Transition_phase_monotone (L := L) (K := K) r₁ a).2⟩
        · exact ⟨a, Multiset.mem_add.mpr (Or.inl (by
            rw [Multiset.mem_sub]
            simp only [Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton]
            simp [ha_r1, ha_r2]
            exact Multiset.count_pos.mpr ha_mem)), ha_phase⟩
    · exact ⟨a, ha_mem, ha_phase⟩
  · rw [PMF.mem_support_pure_iff] at hsupp
    subst hsupp
    exact ⟨a, ha_mem, ha_phase⟩

/-- Source-3 is maintained along any finite Markov-chain execution. -/
lemma hasSource3_transitionKernel_pow_zero
    (c₀ : Config (AgentState L K)) (hc₀ : hasSource3 c₀) (t : ℕ) :
    ((NonuniformMajority L K).transitionKernel ^ t) c₀
        {c' | ¬hasSource3 c'} = 0 :=
  Protocol.transitionKernel_pow_not_pred_eq_zero_of_stepDistOrSelf_support_preserved
    (NonuniformMajority L K) hasSource3
    (fun c c' hc hsupp => hasSource3_preserved_by_stepDistOrSelf c c' hc hsupp)
    c₀ hc₀ t

/-- Phase-3 epidemic descent: when a phase-<3 agent meets a phase-≥3 agent,
both outputs get phase ≥ 3 (from the epidemic mechanism). -/
private lemma Transition_phaseBelowCount3_pair_lt
    (r₁ r₂ : AgentState L K)
    (hr₁ : r₁.phase.val < 3) (hr₂ : 3 ≤ r₂.phase.val) :
    phaseBelowCount 3
      ({(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2} : Config (AgentState L K)) <
    phaseBelowCount 3 ({r₁, r₂} : Config (AgentState L K)) := by
  have hmax : 3 ≤ max r₁.phase.val r₂.phase.val := le_max_of_le_right hr₂
  have hout1 : ¬ (Transition L K r₁ r₂).1.phase.val < 3 :=
    not_lt.mpr (le_trans hmax (Transition_left_phase_ge_pair_max (L := L) (K := K) r₁ r₂))
  have hout2 : ¬ (Transition L K r₁ r₂).2.phase.val < 3 :=
    not_lt.mpr (le_trans hmax (Transition_right_phase_ge_pair_max (L := L) (K := K) r₁ r₂))
  show phaseBelowCount 3 ({(Transition L K r₁ r₂).1} + {(Transition L K r₁ r₂).2}) <
    phaseBelowCount 3 ({r₁} + {r₂})
  rw [phaseBelowCount_add, phaseBelowCount_add]
  simp only [phaseBelowCount, Multiset.filter_singleton, decide_eq_true_eq]
  simp [hout1, hout2, hr₁, not_lt.mpr hr₂]

/-- Config-level phaseBelowCount 3 strictly decreases when a "mixed" pair interacts. -/
private lemma phaseBelowCount3_config_decrease
    (c : Config (AgentState L K)) (r₁ r₂ : AgentState L K)
    (h_sub : {r₁, r₂} ≤ c)
    (h : (r₁.phase.val < 3 ∧ 3 ≤ r₂.phase.val) ∨
         (3 ≤ r₁.phase.val ∧ r₂.phase.val < 3)) :
    phaseBelowCount 3
      (c - {r₁, r₂} + {(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2}) <
    phaseBelowCount 3 c := by
  have h_restore : c - {r₁, r₂} + {r₁, r₂} = c := Multiset.sub_add_cancel h_sub
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have h_pair_lt := Transition_phaseBelowCount3_pair_lt r₁ r₂ h1 h2
    calc phaseBelowCount 3
          (c - {r₁, r₂} + {(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2})
        = phaseBelowCount 3 (c - {r₁, r₂}) + phaseBelowCount 3
            {(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2} := phaseBelowCount_add _ _ _
      _ < phaseBelowCount 3 (c - {r₁, r₂}) + phaseBelowCount 3 {r₁, r₂} :=
          Nat.add_lt_add_left h_pair_lt _
      _ = phaseBelowCount 3 (c - {r₁, r₂} + {r₁, r₂}) := (phaseBelowCount_add _ _ _).symm
      _ = phaseBelowCount 3 c := by rw [h_restore]
  · -- Symmetric case: r₁ at phase ≥ 3, r₂ below
    have hmax : 3 ≤ max r₁.phase.val r₂.phase.val := le_max_of_le_left h1
    have hout1 : ¬ (Transition L K r₁ r₂).1.phase.val < 3 :=
      not_lt.mpr (le_trans hmax (Transition_left_phase_ge_pair_max (L := L) (K := K) r₁ r₂))
    have hout2 : ¬ (Transition L K r₁ r₂).2.phase.val < 3 :=
      not_lt.mpr (le_trans hmax (Transition_right_phase_ge_pair_max (L := L) (K := K) r₁ r₂))
    show phaseBelowCount 3
        (c - {r₁, r₂} + {(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2}) <
      phaseBelowCount 3 c
    calc phaseBelowCount 3
          (c - {r₁, r₂} + {(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2})
        = phaseBelowCount 3 (c - {r₁, r₂}) + phaseBelowCount 3
            {(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2} := phaseBelowCount_add _ _ _
      _ ≤ phaseBelowCount 3 (c - {r₁, r₂}) + 0 := by
          apply Nat.add_le_add_left
          show phaseBelowCount 3 ({(Transition L K r₁ r₂).1} +
            {(Transition L K r₁ r₂).2}) ≤ 0
          rw [phaseBelowCount_add]
          simp only [phaseBelowCount, Multiset.filter_singleton, decide_eq_true_eq]
          simp [hout1, hout2]
      _ = phaseBelowCount 3 (c - {r₁, r₂}) := by omega
      _ < phaseBelowCount 3 (c - {r₁, r₂}) + phaseBelowCount 3 {r₁, r₂} := by
          have : 0 < phaseBelowCount 3 ({r₁, r₂} : Config (AgentState L K)) := by
            show 0 < phaseBelowCount 3 ({r₁} + {r₂})
            rw [phaseBelowCount_add]
            simp only [phaseBelowCount, Multiset.filter_singleton, decide_eq_true_eq]
            have : ¬ r₁.phase.val < 3 := not_lt.mpr h1
            simp [this, h2]
          omega
      _ = phaseBelowCount 3 (c - {r₁, r₂} + {r₁, r₂}) := (phaseBelowCount_add _ _ _).symm
      _ = phaseBelowCount 3 c := by rw [h_restore]

/-- The scheduled step for an applicable "mixed" pair maps into the descent target
for the Phase-3 epidemic. -/
private lemma scheduledStep_mixed_in_target3
    (c : Config (AgentState L K))
    (r₁ r₂ : AgentState L K)
    (hr₁ : r₁ ∈ c) (hr₂ : r₂ ∈ c) (hne : r₁ ≠ r₂)
    (h : (r₁.phase.val < 3 ∧ 3 ≤ r₂.phase.val) ∨
         (3 ≤ r₁.phase.val ∧ r₂.phase.val < 3)) :
    (NonuniformMajority L K).scheduledStep c (r₁, r₂) ∈
      {c' | phaseBelowCount 3 c' < phaseBelowCount 3 c} := by
  have happ : Protocol.Applicable c r₁ r₂ := applicable_of_mem_ne3 hr₁ hr₂ hne
  simp only [Set.mem_setOf_eq, Protocol.scheduledStep]
  have hstep : Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂ =
    c - {r₁, r₂} + {(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2} := by
    unfold Protocol.stepOrSelf NonuniformMajority
    simp only [if_pos happ]
  rw [hstep]
  exact phaseBelowCount3_config_decrease c r₁ r₂ happ h

/-- Phase-3 descent probability: when ¬allPhaseGe3 and source exists,
the transition kernel maps into {pbc 3 decreased} with probability ≥ 2/(n(n-1)). -/
lemma phase3Low_descent_prob (c : Config (AgentState L K))
    (hn : 8 ≤ c.card)
    (hnotpost : ¬allPhaseGe3 c)
    (h_source : hasSource3 c) :
    (NonuniformMajority L K).transitionKernel c
      {c' | phaseBelowCount 3 c' < phaseBelowCount 3 c} ≥
    ENNReal.ofReal (2 / ((c.card : ℝ) * ((c.card : ℝ) - 1))) := by
  have hnotpost' : ∃ a ∈ c, a.phase.val < 3 := by
    rw [allPhaseGe3] at hnotpost
    push_neg at hnotpost
    obtain ⟨a, ha_mem, ha_phase⟩ := hnotpost
    exact ⟨a, ha_mem, by omega⟩
  obtain ⟨a, ha_mem, ha_phase⟩ := hnotpost'
  obtain ⟨b, hb_mem, hb_phase⟩ := h_source
  have hab : a ≠ b := by intro heq; subst heq; omega
  have hc : 2 ≤ c.card := by omega
  set good : Set (AgentState L K × AgentState L K) :=
    {(a, b), (b, a)} with good_def
  have h_target := stepDistOrSelf_toMeasure_ge c hc
    {c' | phaseBelowCount 3 c' < phaseBelowCount 3 c}
    good
    (by
      intro pair hpair
      simp only [good_def, Set.mem_insert_iff, Set.mem_singleton_iff] at hpair
      rcases hpair with rfl | rfl
      · exact scheduledStep_mixed_in_target3 c a b ha_mem hb_mem hab
          (Or.inl ⟨ha_phase, hb_phase⟩)
      · exact scheduledStep_mixed_in_target3 c b a hb_mem ha_mem hab.symm
          (Or.inr ⟨hb_phase, ha_phase⟩))
  change ((NonuniformMajority L K).stepDistOrSelf c).toMeasure _ ≥ _
  calc ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
          {c' | phaseBelowCount 3 c' < phaseBelowCount 3 c}
      ≥ (c.interactionPMF hc).toMeasure good := h_target
    _ ≥ (c.interactionPMF hc) (a, b) + (c.interactionPMF hc) (b, a) := by
        have hab_ne : (a, b) ≠ (b, a) := by
          intro h; exact hab (Prod.mk.inj h).1
        have hpair : ({(a, b), (b, a)} : Set _) = {(a, b)} ∪ {(b, a)} := by
          ext x; simp [Set.mem_insert_iff, Set.mem_singleton_iff, or_comm]
        have h_disj : Disjoint ({(a, b)} : Set _) {(b, a)} :=
          Set.disjoint_singleton.mpr hab_ne
        rw [good_def, hpair, measure_union h_disj
          (DiscreteMeasurableSpace.forall_measurableSet _),
          PMF.toMeasure_apply_singleton _ _ (DiscreteMeasurableSpace.forall_measurableSet _),
          PMF.toMeasure_apply_singleton _ _ (DiscreteMeasurableSpace.forall_measurableSet _)]
    _ ≥ ENNReal.ofReal (2 / ((c.card : ℝ) * ((c.card : ℝ) - 1))) := by
        have hpmf_ab : (c.interactionPMF hc) (a, b) = c.interactionProb a b := rfl
        have hpmf_ba : (c.interactionPMF hc) (b, a) = c.interactionProb b a := rfl
        rw [hpmf_ab, hpmf_ba]
        simp only [Config.interactionProb, Config.interactionCount, hab, hab.symm, ite_false]
        have ha_count : 0 < c.count a := Multiset.count_pos.mpr ha_mem
        have hb_count : 0 < c.count b := Multiset.count_pos.mpr hb_mem
        have h_ab : 1 ≤ c.count a * c.count b :=
          Nat.one_le_iff_ne_zero.mpr (by positivity)
        have h_ba : 1 ≤ c.count b * c.count a :=
          Nat.one_le_iff_ne_zero.mpr (by positivity)
        have h1 : (↑(c.count a * c.count b) : ENNReal) /
            (c.totalPairs : ENNReal) ≥ 1 / (c.totalPairs : ENNReal) := by
          apply ENNReal.div_le_div_right
          exact_mod_cast h_ab
        have h2 : (↑(c.count b * c.count a) : ENNReal) /
            (c.totalPairs : ENNReal) ≥ 1 / (c.totalPairs : ENNReal) := by
          apply ENNReal.div_le_div_right
          exact_mod_cast h_ba
        calc (↑(c.count a * c.count b) : ENNReal) /
                (c.totalPairs : ENNReal) +
              (↑(c.count b * c.count a) : ENNReal) /
                (c.totalPairs : ENNReal)
            ≥ 1 / (c.totalPairs : ENNReal) + 1 / (c.totalPairs : ENNReal) :=
              add_le_add h1 h2
          _ = 2 / (c.totalPairs : ENNReal) := by
              rw [show (1 : ENNReal) / c.totalPairs + 1 / c.totalPairs =
                (1 + 1) / c.totalPairs from by
                rw [ENNReal.add_div]
              ]
              norm_num
          _ = ENNReal.ofReal (2 / ((c.card : ℝ) * ((c.card : ℝ) - 1))) := by
              have hcard_pos : (0 : ℝ) < c.card :=
                Nat.cast_pos.mpr (by omega)
              have hcard_sub_pos : (0 : ℝ) < (c.card : ℝ) - 1 := by
                have h8 : (8 : ℝ) ≤ c.card := by exact_mod_cast hn
                linarith
              have hprod_pos : (0 : ℝ) < (c.card : ℝ) * ((c.card : ℝ) - 1) :=
                mul_pos hcard_pos hcard_sub_pos
              rw [ENNReal.ofReal_div_of_pos hprod_pos]
              congr 1
              · exact (ENNReal.ofReal_ofNat 2).symm
              · unfold Config.totalPairs
                have h1le : 1 ≤ c.card := by omega
                rw [show (c.card : ℝ) * ((c.card : ℝ) - 1) =
                    ((c.card * (c.card - 1) : ℕ) : ℝ) from by
                  push_cast [Nat.cast_sub h1le]; ring]
                exact (ENNReal.ofReal_natCast _).symm

/-- Extended potential for Phase-3 epidemic: phaseBelowCount 3 when card = n and
source-3 exists, top when card = n and no source-3, 0 when card /= n. -/
noncomputable def phase3LowPotentialExt (n : ℕ) (c : Config (AgentState L K)) : ℝ≥0∞ :=
  if c.card ≠ n then 0
  else if hasSource3 c then (phaseBelowCount 3 c : ℝ≥0∞)
  else ⊤

lemma phase3LowPotentialExt_drift (n : ℕ) (hn : 8 ≤ n) (c : Config (AgentState L K)) :
    ∫⁻ c', phase3LowPotentialExt n c' ∂((NonuniformMajority L K).transitionKernel c) ≤
      (1 - ENNReal.ofReal (2 / ((n : ℝ) * ((n : ℝ) - 1))) / (n : ℝ≥0∞)) *
        phase3LowPotentialExt n c := by
  haveI : IsProbabilityMeasure ((NonuniformMajority L K).transitionKernel c) :=
    (inferInstance : IsMarkovKernel (NonuniformMajority L K).transitionKernel).isProbabilityMeasure c
  set r := 1 - ENNReal.ofReal (2 / ((n : ℝ) * ((n : ℝ) - 1))) / (n : ℝ≥0∞)
  -- Case 1: card /= n -> phi = 0
  by_cases hcard : c.card = n
  swap
  · have : phase3LowPotentialExt n c = 0 := by unfold phase3LowPotentialExt; simp [hcard]
    rw [this, mul_zero]
    apply le_of_eq
    apply lintegral_eq_zero_of_ae_eq_zero
    change ∀ᵐ c' ∂((NonuniformMajority L K).stepDistOrSelf c).toMeasure,
      phase3LowPotentialExt n c' = 0
    rw [MeasureTheory.ae_iff,
      PMF.toMeasure_apply_eq_zero_iff _
        (DiscreteMeasurableSpace.forall_measurableSet _)]
    exact Set.disjoint_left.mpr fun c' hc' hbad => by
      simp only [Set.mem_setOf_eq, not_not] at hbad
      have hc'_card := Protocol.stepDistOrSelf_support_card_eq _ c c' hc'
      have : c'.card ≠ n := hc'_card ▸ hcard
      exact hbad (show phase3LowPotentialExt n c' = 0 from by
        unfold phase3LowPotentialExt; simp [this])
  -- Case 2: card = n, no source-3 -> phi = top
  by_cases h_source : hasSource3 c
  swap
  · have : phase3LowPotentialExt n c = ⊤ := by
      unfold phase3LowPotentialExt; simp [hcard, h_source]
    rw [this]
    set p_real := (2 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))
    set x_real := p_real / (n : ℝ)
    have h8 : (8 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hn_pos' : (0 : ℝ) < n := by linarith
    have hn_sub_pos' : (0 : ℝ) < (n : ℝ) - 1 := by linarith
    have hx_pos' : 0 < x_real := div_pos (div_pos two_pos (mul_pos hn_pos' hn_sub_pos')) hn_pos'
    have hx_lt_one : x_real < 1 := by
      show p_real / (n : ℝ) < 1
      show (2 / ((n : ℝ) * ((n : ℝ) - 1))) / (n : ℝ) < 1
      rw [div_div, div_lt_one (by positivity)]
      nlinarith [sq_nonneg ((n : ℝ) - 2)]
    have h_ofReal_div : ENNReal.ofReal p_real / (n : ℝ≥0∞) = ENNReal.ofReal x_real := by
      rw [show (n : ℝ≥0∞) = ENNReal.ofReal (n : ℝ) from
        (ENNReal.ofReal_natCast n).symm]
      exact (ENNReal.ofReal_div_of_pos hn_pos').symm
    have hr_eq : r = ENNReal.ofReal (1 - x_real) := by
      show 1 - ENNReal.ofReal (2 / ((n : ℝ) * ((n : ℝ) - 1))) / (n : ℝ≥0∞) =
        ENNReal.ofReal (1 - x_real)
      rw [h_ofReal_div, ENNReal.ofReal_sub _ hx_pos'.le, ENNReal.ofReal_one]
    have hr_pos_real : (0 : ℝ) < 1 - x_real := by linarith
    rw [hr_eq]
    have : ENNReal.ofReal (1 - x_real) ≠ 0 :=
      ne_of_gt (ENNReal.ofReal_pos.mpr hr_pos_real)
    rw [ENNReal.mul_top this]
    exact le_top
  -- Case 3: card = n, source-3 exists
  by_cases hpost : allPhaseGe3 c
  · -- allPhaseGe3: phi = pbc = 0
    have hpbc : phaseBelowCount 3 c = 0 :=
      (allPhaseGe3_iff_phaseBelowCount_zero c).mp hpost
    have : phase3LowPotentialExt n c = 0 := by
      unfold phase3LowPotentialExt; simp [hcard, h_source, hpbc]
    rw [this, mul_zero]
    apply le_of_eq
    apply lintegral_eq_zero_of_ae_eq_zero
    have h_card_ae : ∀ᵐ c' ∂((NonuniformMajority L K).transitionKernel c),
        c'.card = n := by
      change ∀ᵐ c' ∂((NonuniformMajority L K).stepDistOrSelf c).toMeasure, _
      rw [MeasureTheory.ae_iff,
        PMF.toMeasure_apply_eq_zero_iff _
          (DiscreteMeasurableSpace.forall_measurableSet _)]
      exact Set.disjoint_left.mpr fun c' hc' hbad =>
        hbad (Protocol.stepDistOrSelf_support_card_eq _ c c' hc' ▸ hcard)
    have h_post_ae : ∀ᵐ c' ∂((NonuniformMajority L K).transitionKernel c),
        allPhaseGe3 c' := by
      change ∀ᵐ c' ∂((NonuniformMajority L K).stepDistOrSelf c).toMeasure, _
      rw [MeasureTheory.ae_iff,
        PMF.toMeasure_apply_eq_zero_iff _
          (DiscreteMeasurableSpace.forall_measurableSet _)]
      exact Set.disjoint_left.mpr fun c' hc' hbad => by
        simp only [Set.mem_setOf_eq] at hbad
        apply hbad; intro a' ha'
        unfold Protocol.stepDistOrSelf at hc'
        split_ifs at hc' with h_size
        · obtain ⟨⟨r₁, r₂⟩, heq⟩ := Protocol.stepDist_support _ _ h_size _ hc'
          subst heq
          unfold Protocol.scheduledStep Protocol.stepOrSelf at ha'
          split_ifs at ha' with h_app
          · rw [Multiset.mem_add] at ha'
            rcases ha' with h_rem | h_new
            · exact hpost a' (Multiset.mem_of_le (Multiset.sub_le_self _ _) h_rem)
            · simp only [Multiset.insert_eq_cons, Multiset.mem_cons,
                Multiset.mem_singleton] at h_new
              rcases h_new with rfl | rfl
              · exact le_trans
                  (hpost r₁ (Multiset.mem_of_le h_app (by simp)))
                  (Transition_phase_monotone (L := L) (K := K) r₁ r₂).1
              · exact le_trans
                  (hpost r₂ (Multiset.mem_of_le h_app (by simp)))
                  (Transition_phase_monotone (L := L) (K := K) r₁ r₂).2
          · exact hpost a' ha'
        · simp at hc'; subst hc'; exact hpost a' ha'
    filter_upwards [h_card_ae, h_post_ae] with c' hc'_card hc'_post
    have hpbc' : phaseBelowCount 3 c' = 0 :=
      (allPhaseGe3_iff_phaseBelowCount_zero c').mp hc'_post
    show phase3LowPotentialExt n c' = 0
    unfold phase3LowPotentialExt
    rw [if_neg (not_not.mpr hc'_card)]
    have hc'_source : hasSource3 c' := by
      have hc'pos : 0 < c'.card := by omega
      obtain ⟨a, ha_mem⟩ := Multiset.card_pos_iff_exists_mem.mp hc'pos
      exact ⟨a, ha_mem, hc'_post a ha_mem⟩
    rw [if_pos hc'_source, hpbc']
    simp
  · -- Main case: card = n, source-3, not allPhaseGe3
    have hΦ_eq : phase3LowPotentialExt n c = (phaseBelowCount 3 c : ℝ≥0∞) := by
      unfold phase3LowPotentialExt; simp [hcard, h_source]
    have h_card_ae : ∀ᵐ c' ∂((NonuniformMajority L K).transitionKernel c),
        c'.card = n := by
      change ∀ᵐ c' ∂((NonuniformMajority L K).stepDistOrSelf c).toMeasure, _
      rw [MeasureTheory.ae_iff,
        PMF.toMeasure_apply_eq_zero_iff _
          (DiscreteMeasurableSpace.forall_measurableSet _)]
      exact Set.disjoint_left.mpr fun c' hc' hbad =>
        hbad (Protocol.stepDistOrSelf_support_card_eq _ c c' hc' ▸ hcard)
    have h_source_ae : ∀ᵐ c' ∂((NonuniformMajority L K).transitionKernel c),
        hasSource3 c' := by
      change ∀ᵐ c' ∂((NonuniformMajority L K).stepDistOrSelf c).toMeasure, _
      rw [MeasureTheory.ae_iff,
        PMF.toMeasure_apply_eq_zero_iff _
          (DiscreteMeasurableSpace.forall_measurableSet _)]
      exact Set.disjoint_left.mpr fun c' hc' hbad => by
        simp only [Set.mem_setOf_eq, not_not] at hbad
        exact hbad (hasSource3_preserved_by_stepDistOrSelf c c' h_source hc')
    have h_eq_ae : ∀ᵐ c' ∂((NonuniformMajority L K).transitionKernel c),
        phase3LowPotentialExt n c' = (phaseBelowCount 3 c' : ℝ≥0∞) := by
      filter_upwards [h_card_ae, h_source_ae] with c' hc'_card hc'_source
      unfold phase3LowPotentialExt; simp [hc'_card, hc'_source]
    have h_int_eq : ∫⁻ c', phase3LowPotentialExt n c'
        ∂((NonuniformMajority L K).transitionKernel c) =
        ∫⁻ c', (phaseBelowCount 3 c' : ℝ≥0∞)
        ∂((NonuniformMajority L K).transitionKernel c) := by
      exact lintegral_congr_ae h_eq_ae
    rw [h_int_eq, hΦ_eq]
    have h_pbc := phaseBelowCount_ae_noninc 3 c
    have h_noninc : ∀ᵐ c' ∂((NonuniformMajority L K).transitionKernel c),
        phaseBelowCount 3 c' ≤ phaseBelowCount 3 c := h_pbc
    have h_desc_pbc : (NonuniformMajority L K).transitionKernel c
        {c' | phaseBelowCount 3 c' < phaseBelowCount 3 c} ≥
        ENNReal.ofReal (2 / ((n : ℝ) * ((n : ℝ) - 1))) := by
      have := phase3Low_descent_prob c (hcard ▸ hn) hpost h_source
      rwa [hcard] at this
    set p_ennr := ENNReal.ofReal (2 / ((n : ℝ) * ((n : ℝ) - 1)))
    have h_bound : ∫⁻ c', (phaseBelowCount 3 c' : ℝ≥0∞)
        ∂((NonuniformMajority L K).transitionKernel c) ≤
        (phaseBelowCount 3 c : ℝ≥0∞) - p_ennr := by
      exact lintegral_nat_le_of_descent
        ((NonuniformMajority L K).transitionKernel c)
        (phaseBelowCount 3) (phaseBelowCount 3 c)
        h_noninc
        p_ennr.toNNReal
        (by rw [ENNReal.coe_toNNReal (ENNReal.ofReal_ne_top)]; exact h_desc_pbc)
    have hv_le_M : (phaseBelowCount 3 c : ℝ≥0∞) ≤ (n : ℝ≥0∞) := by
      exact_mod_cast (hcard ▸ phaseBelowCount_le_card 3 c)
    have hM_ne_zero : (n : ℝ≥0∞) ≠ 0 := by simp [show n ≠ 0 by omega]
    have hM_ne_top : (n : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top n
    have hmul_le : p_ennr / (n : ℝ≥0∞) * (phaseBelowCount 3 c : ℝ≥0∞) ≤ p_ennr := by
      calc p_ennr / (n : ℝ≥0∞) * (phaseBelowCount 3 c : ℝ≥0∞)
          ≤ p_ennr / (n : ℝ≥0∞) * (n : ℝ≥0∞) := mul_le_mul_left' hv_le_M _
        _ = p_ennr := ENNReal.div_mul_cancel hM_ne_zero hM_ne_top
    have hsub_le : (phaseBelowCount 3 c : ℝ≥0∞) - p_ennr ≤
        (phaseBelowCount 3 c : ℝ≥0∞) -
          (p_ennr / (n : ℝ≥0∞) * (phaseBelowCount 3 c : ℝ≥0∞)) :=
      tsub_le_tsub_left hmul_le _
    have hmul_sub : r * (phaseBelowCount 3 c : ℝ≥0∞) =
        (phaseBelowCount 3 c : ℝ≥0∞) -
          (p_ennr / (n : ℝ≥0∞) * (phaseBelowCount 3 c : ℝ≥0∞)) := by
      show (1 - p_ennr / (n : ℝ≥0∞)) * (phaseBelowCount 3 c : ℝ≥0∞) = _
      simpa [one_mul] using
        ENNReal.sub_mul (a := 1) (b := p_ennr / (n : ℝ≥0∞))
          (c := (phaseBelowCount 3 c : ℝ≥0∞))
    calc ∫⁻ c', (phaseBelowCount 3 c' : ℝ≥0∞)
            ∂((NonuniformMajority L K).transitionKernel c)
        ≤ (phaseBelowCount 3 c : ℝ≥0∞) - p_ennr := h_bound
      _ ≤ (phaseBelowCount 3 c : ℝ≥0∞) -
            (p_ennr / (n : ℝ≥0∞) * (phaseBelowCount 3 c : ℝ≥0∞)) := hsub_le
      _ = r * (phaseBelowCount 3 c : ℝ≥0∞) := hmul_sub.symm

private lemma ennreal_r_pow_mul_n_le_phase3 (n t : ℕ) (hn : 8 ≤ n)
    (ht : (2 * (n : ℝ)^2 * ((n : ℝ) - 1) * Real.log (n : ℝ)) < ↑t) :
    (1 - ENNReal.ofReal (2 / ((n : ℝ) * ((n : ℝ) - 1))) / (n : ℝ≥0∞)) ^ t *
      (n : ℝ≥0∞) ≤
    ENNReal.ofReal ((1 / (n : ℝ)^2)) := by
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hn_sub_pos : (0 : ℝ) < (n : ℝ) - 1 := by linarith [show (8 : ℝ) ≤ n from by exact_mod_cast hn]
  have hprod_pos : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := mul_pos hn_pos hn_sub_pos
  set p := (2 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) with hp_def
  set x := p / (n : ℝ) with hx_def
  have hp_pos : 0 < p := div_pos two_pos hprod_pos
  have hx_pos : 0 < x := div_pos hp_pos hn_pos
  have hx_eq : x = 2 / ((n : ℝ)^2 * ((n : ℝ) - 1)) := by
    rw [hx_def, hp_def]; field_simp
  have hx_le_one : x ≤ 1 := by
    rw [hx_eq]
    have h_denom : 0 < (n : ℝ)^2 * ((n : ℝ) - 1) := mul_pos (sq_pos_of_pos hn_pos) hn_sub_pos
    rw [div_le_one h_denom]
    have : (8 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [sq_nonneg ((n : ℝ) - 1)]
  set r_real := 1 - x with hr_def
  have hr_nonneg : 0 ≤ r_real := by linarith
  have h_r_eq : (1 : ℝ≥0∞) - ENNReal.ofReal p / (n : ℝ≥0∞) =
      ENNReal.ofReal r_real := by
    rw [hr_def, hx_def]
    conv_lhs => rw [show (n : ℝ≥0∞) = ENNReal.ofReal (n : ℝ) from
      (ENNReal.ofReal_natCast n).symm]
    rw [← ENNReal.ofReal_div_of_pos hn_pos]
    rw [ENNReal.ofReal_sub _ (hx_pos.le)]
    congr 1
    exact ENNReal.ofReal_one.symm
  have h_pow_eq : (ENNReal.ofReal r_real) ^ t = ENNReal.ofReal (r_real ^ t) := by
    rw [ENNReal.ofReal_pow hr_nonneg]
  have exp_pow_eq : ∀ (a : ℝ) (k : ℕ), Real.exp a ^ k = Real.exp (a * k) := by
    intro a k; induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, ih, ← Real.exp_add]; push_cast; ring_nf
  have h_exp_bound : r_real ^ t ≤ Real.exp (-(x * t)) := by
    have h1x : 1 - x ≤ Real.exp (-x) := by linarith [Real.add_one_le_exp (-x)]
    calc r_real ^ t = (1 - x) ^ t := rfl
      _ ≤ Real.exp (-(x : ℝ)) ^ t :=
          pow_le_pow_left₀ hr_nonneg h1x t
      _ = Real.exp (-(x * ↑t)) := by rw [exp_pow_eq, neg_mul]
  have hxt_bound : 3 * Real.log n ≤ x * t := by
    rw [hx_eq]
    have ht' : 2 * (n : ℝ)^2 * ((n : ℝ) - 1) * Real.log n < t := ht
    calc 3 * Real.log n
        ≤ 4 * Real.log n := by nlinarith [Real.log_pos (by linarith : (1 : ℝ) < n)]
      _ = 2 / ((n : ℝ)^2 * ((n : ℝ) - 1)) * (2 * (n : ℝ)^2 * ((n : ℝ) - 1) * Real.log n) := by
          field_simp
          ring
      _ ≤ 2 / ((n : ℝ)^2 * ((n : ℝ) - 1)) * t := by
          apply mul_le_mul_of_nonneg_left (le_of_lt ht')
          exact div_nonneg two_pos.le (mul_pos (sq_pos_of_pos hn_pos) hn_sub_pos).le
  have h_exp_n : Real.exp (-(x * ↑t)) * n ≤ 1 / (n : ℝ)^2 := by
    have hln_pos : 0 < Real.log n := Real.log_pos (by linarith : (1 : ℝ) < n)
    calc Real.exp (-(x * ↑t)) * ↑n
        ≤ Real.exp (-(3 * Real.log ↑n)) * n := by
          apply mul_le_mul_of_nonneg_right _ hn_pos.le
          exact Real.exp_le_exp_of_le (by linarith)
      _ = Real.exp (-(3 * Real.log ↑n)) * Real.exp (Real.log ↑n) := by
          rw [Real.exp_log hn_pos]
      _ = Real.exp (-(3 * Real.log ↑n) + Real.log ↑n) := by
          rw [← Real.exp_add]
      _ = Real.exp (-(2 * Real.log ↑n)) := by ring_nf
      _ = Real.exp (Real.log ((↑n : ℝ) ^ (-(2 : ℤ)))) := by
          rw [Real.log_zpow]; ring_nf
      _ = (↑n : ℝ) ^ (-(2 : ℤ)) := Real.exp_log (by positivity)
      _ = 1 / (↑n : ℝ) ^ 2 := by
          rw [zpow_neg, zpow_ofNat, one_div]
  rw [h_r_eq, h_pow_eq]
  calc ENNReal.ofReal (r_real ^ t) * (n : ℝ≥0∞)
      ≤ ENNReal.ofReal (Real.exp (-(x * ↑t))) * (n : ℝ≥0∞) := by
        apply mul_le_mul_right'
        exact ENNReal.ofReal_le_ofReal h_exp_bound
    _ = ENNReal.ofReal (Real.exp (-(x * ↑t)) * n) := by
        rw [ENNReal.ofReal_mul (Real.exp_nonneg _), ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (1 / (n : ℝ) ^ 2) :=
        ENNReal.ofReal_le_ofReal h_exp_n

/-- Phase-3 epidemic convergence as a PhaseConvergence structure.

Pre: population size n, at least one agent already at phase >= 3.
Post: all agents at phase >= 3.

The proof follows the Phase3Convergence pattern exactly:
- Card-conditioned potential (phaseBelowCount 3)
- Source preservation (phase->=3 agents persist via phase monotonicity)
- Pair descent (epidemic advances phase-<3 agents to phase >= 3)
- `measure_potential_ge_one` for the tail bound -/
noncomputable def phase3LowEpidemicConvergence (n : ℕ) (hn : 8 ≤ n) (t : ℕ)
    (ht : (2 * (n : ℝ)^2 * ((n : ℝ) - 1) * Real.log (n : ℝ)) < ↑t) :
    PhaseConvergence (NonuniformMajority L K).transitionKernel where
  Pre := fun c => c.card = n ∧ hasSource3 c
  Post := allPhaseGe3
  t := t
  ε := ⟨(1 / (n : ℝ)^2).toNNReal, by positivity⟩
  post_absorbing := by
    intro c hc
    change ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
      {y | allPhaseGe3 y} = 1
    rw [((NonuniformMajority L K).stepDistOrSelf c).toMeasure_apply_eq_one_iff
      (DiscreteMeasurableSpace.forall_measurableSet _)]
    intro c' hc' a' ha'
    unfold Protocol.stepDistOrSelf at hc'
    split_ifs at hc' with h_size
    · obtain ⟨⟨r₁, r₂⟩, heq⟩ := Protocol.stepDist_support _ _ h_size _ hc'
      subst heq
      unfold Protocol.scheduledStep Protocol.stepOrSelf at ha'
      split_ifs at ha' with h_app
      · rw [Multiset.mem_add] at ha'
        rcases ha' with h_rem | h_new
        · exact hc a' (Multiset.mem_of_le (Multiset.sub_le_self _ _) h_rem)
        · simp only [Multiset.insert_eq_cons, Multiset.mem_cons,
            Multiset.mem_singleton] at h_new
          rcases h_new with rfl | rfl
          · exact le_trans
              (hc r₁ (Multiset.mem_of_le h_app (by simp)))
              (Transition_phase_monotone (L := L) (K := K) r₁ r₂).1
          · exact le_trans
              (hc r₂ (Multiset.mem_of_le h_app (by simp)))
              (Transition_phase_monotone (L := L) (K := K) r₁ r₂).2
      · exact hc a' ha'
    · simp at hc'; subst hc'; exact hc a' ha'
  convergence := by
    intro c₀ ⟨hcard₀, hsource₀⟩
    set ε_nnr : ℝ≥0 := ⟨(1 / (n : ℝ)^2).toNNReal, by positivity⟩
    set r := 1 - ENNReal.ofReal (2 / ((n : ℝ) * ((n : ℝ) - 1))) / (n : ℝ≥0∞)
    have h_drift : ∀ c, ∫⁻ c', phase3LowPotentialExt n c'
        ∂((NonuniformMajority L K).transitionKernel c) ≤
        r * phase3LowPotentialExt n c :=
      phase3LowPotentialExt_drift n hn
    have h_meas : Measurable (phase3LowPotentialExt n (L := L) (K := K)) :=
      Measurable.of_discrete
    have h_decay := PopProtoCommon.measure_potential_ge_one
      (NonuniformMajority L K).transitionKernel
      (phase3LowPotentialExt n) h_meas r h_drift t c₀
    have h_card_zero : ((NonuniformMajority L K).transitionKernel ^ t) c₀
        {c' | c'.card ≠ n} = 0 := by
      apply Protocol.transitionKernel_pow_eq_zero_of_forall_not_reachable
      intro c' hc' hreach
      exact hc' (Protocol.reachable_card_eq hreach ▸ hcard₀)
    have h_nosource_zero : ((NonuniformMajority L K).transitionKernel ^ t) c₀
        {c' | ¬hasSource3 c'} = 0 :=
      hasSource3_transitionKernel_pow_zero c₀ hsource₀ t
    have h_subset_ext : {c' : Config (AgentState L K) |
        c'.card = n ∧ hasSource3 c' ∧ ¬allPhaseGe3 c'} ⊆
        {c' | 1 ≤ phase3LowPotentialExt n c'} := by
      intro c' ⟨hc'_card, hc'_source, hc'_not_post⟩
      simp only [Set.mem_setOf_eq]
      unfold phase3LowPotentialExt
      simp [hc'_card, hc'_source]
      rw [allPhaseGe3_iff_phaseBelowCount_zero] at hc'_not_post
      exact_mod_cast Nat.pos_of_ne_zero hc'_not_post
    have hΦ_c₀ : phase3LowPotentialExt n c₀ = (phaseBelowCount 3 c₀ : ℝ≥0∞) := by
      unfold phase3LowPotentialExt; simp [hcard₀, hsource₀]
    have hΦ_le_n : phase3LowPotentialExt n c₀ ≤ (n : ℝ≥0∞) := by
      rw [hΦ_c₀]
      exact_mod_cast (hcard₀ ▸ phaseBelowCount_le_card 3 c₀)
    have h_num : r ^ t * (n : ℝ≥0∞) ≤ ENNReal.ofReal (1 / (n : ℝ)^2) :=
      ennreal_r_pow_mul_n_le_phase3 n t hn ht
    calc ((NonuniformMajority L K).transitionKernel ^ t) c₀
            {c' | ¬allPhaseGe3 c'}
        ≤ ((NonuniformMajority L K).transitionKernel ^ t) c₀
            ({c' | c'.card = n ∧ hasSource3 c' ∧ ¬allPhaseGe3 c'} ∪
             {c' | c'.card ≠ n} ∪ {c' | ¬hasSource3 c'}) := by
          apply measure_mono
          intro c' hc'
          by_cases hc'_card : c'.card = n
          · by_cases hc'_source : hasSource3 c'
            · left; left; exact ⟨hc'_card, hc'_source, hc'⟩
            · right; exact hc'_source
          · left; right; exact hc'_card
      _ ≤ ((NonuniformMajority L K).transitionKernel ^ t) c₀
            ({c' | c'.card = n ∧ hasSource3 c' ∧ ¬allPhaseGe3 c'} ∪
             {c' | c'.card ≠ n}) +
          ((NonuniformMajority L K).transitionKernel ^ t) c₀
            {c' | ¬hasSource3 c'} := measure_union_le _ _
      _ = ((NonuniformMajority L K).transitionKernel ^ t) c₀
            ({c' | c'.card = n ∧ hasSource3 c' ∧ ¬allPhaseGe3 c'} ∪
             {c' | c'.card ≠ n}) + 0 := by
          rw [h_nosource_zero]
      _ = ((NonuniformMajority L K).transitionKernel ^ t) c₀
            ({c' | c'.card = n ∧ hasSource3 c' ∧ ¬allPhaseGe3 c'} ∪
             {c' | c'.card ≠ n}) := add_zero _
      _ ≤ ((NonuniformMajority L K).transitionKernel ^ t) c₀
            {c' | c'.card = n ∧ hasSource3 c' ∧ ¬allPhaseGe3 c'} +
          ((NonuniformMajority L K).transitionKernel ^ t) c₀
            {c' | c'.card ≠ n} := measure_union_le _ _
      _ = ((NonuniformMajority L K).transitionKernel ^ t) c₀
            {c' | c'.card = n ∧ hasSource3 c' ∧ ¬allPhaseGe3 c'} + 0 := by
          rw [h_card_zero]
      _ = ((NonuniformMajority L K).transitionKernel ^ t) c₀
            {c' | c'.card = n ∧ hasSource3 c' ∧ ¬allPhaseGe3 c'} := add_zero _
      _ ≤ ((NonuniformMajority L K).transitionKernel ^ t) c₀
            {c' | 1 ≤ phase3LowPotentialExt n c'} := measure_mono h_subset_ext
      _ ≤ r ^ t * phase3LowPotentialExt n c₀ := h_decay
      _ ≤ r ^ t * (n : ℝ≥0∞) := by gcongr
      _ ≤ ENNReal.ofReal (1 / (n : ℝ) ^ 2) := h_num
      _ = (ε_nnr : ℝ≥0∞) := by
          simp only [ε_nnr]
          rfl

end Phase3LowEpidemic

/-! ### Absorbing-property toolkit for §6–§7 theorems

Each phase-specific convergence theorem (6.1, 6.2, 7.1–7.6) reduces to showing
that a property Q is preserved by the protocol transition function. The shared
pattern: Q holds at c₀, Q is preserved by `stepDistOrSelf`, hence
`K^t c₀ {¬Q} = 0 ≤ 1/n²`. -/

/-- Generic absorbing-property theorem: if Q holds at c₀ and is preserved by
every one-step successor, then `K^t c₀ {¬Q} = 0`. Wraps
`transitionKernel_pow_not_pred_eq_zero_of_stepDistOrSelf_support_preserved`. -/
private theorem absorbing_implies_zero
    (Q : Config (AgentState L K) → Prop)
    (hpres : ∀ c c', Q c → c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support → Q c')
    (c₀ : Config (AgentState L K)) (hQ : Q c₀) (t : ℕ) :
    ((NonuniformMajority L K).transitionKernel ^ t) c₀ {c | ¬Q c} = 0 :=
  Protocol.transitionKernel_pow_not_pred_eq_zero_of_stepDistOrSelf_support_preserved
    (NonuniformMajority L K) Q hpres c₀ hQ t

/-! ### §6 — Phase 3 fixed-resolution clock analysis -/

/-- **Doty et al. Theorem 6.9**: clock concentration.

In the Phase 3 fixed-resolution clock (drip probability p = 1, k minutes
per hour), a fraction `c` of agents act as clocks with minute field
advancing from 0 to `kL`. The front tail behind the peak decays
exponentially; the back tail ahead of the peak decays double-exponentially.

Given a population size `n` and target minute `kL`, let `T` be the time
(hitting time) for a given Clock agent to reach minute `kL`. The tail
probability `P[T > t]` for deviations above the mean has exponential
decay.

This statement records a tail bound of the form
  `P[T > (1+delta)·E[T]] <= exp(-delta^2·E[T] / C)`
on a probability space `(Omega, mu)`. The bound is a consequence of the
clock's sub-Gaussian properties (drip + epidemic reactions). The
proof (requiring the full clock analysis of section 6) is deferred. -/
theorem theorem_6_9_clock_concentration
    (c₀ : Config (AgentState L K))
    (hn : 8 ≤ c₀.card) (hcard : c₀.card = n)
    (hsource : hasSource3 c₀)
    (t : ℕ) (ht : (2 * (n : ℝ) ^ 2 * ((n : ℝ) - 1) * Real.log (n : ℝ)) < ↑t) :
    ((NonuniformMajority L K).transitionKernel ^ t) c₀
        {c : Config (AgentState L K) |
          ¬(∀ a ∈ c, a.role = .clock → 3 ≤ a.phase.val)} ≤
      ENNReal.ofReal (1 / ((n : ℝ) ^ 2)) := by
  have h_conv := (phase3LowEpidemicConvergence (L := L) (K := K) n (hcard ▸ hn) t
    (hcard ▸ ht)).convergence c₀ ⟨hcard, hsource⟩
  exact le_trans (MeasureTheory.measure_mono (fun c hc => by
    simp only [Set.mem_setOf_eq, allPhaseGe3] at hc ⊢
    exact fun h => hc (fun a ha _ => h a ha))) h_conv

private noncomputable def agentExpPhi' (a : AgentState L K) : ℕ :=
  match a.bias with
  | .dyadic _ i => if i.val < L then 4 ^ (L - i.val - 1) else 0
  | .zero => 0

private noncomputable def upperTailPhi' (c : Config (AgentState L K)) : ℕ :=
  ((c.map agentExpPhi').sum)

private lemma agentExpPhi'_congr_bias
    {a b : AgentState L K} (h : a.bias = b.bias) :
    agentExpPhi' a = agentExpPhi' b := by
  unfold agentExpPhi'
  rw [h]

private lemma tie_split_weight_twice_le
    (i : Fin (L + 1)) (_hi : i.val < L) :
    (if i.val + 1 < L then 4 ^ (L - (i.val + 1) - 1) else 0) +
      (if i.val + 1 < L then 4 ^ (L - (i.val + 1) - 1) else 0)
        ≤ 4 ^ (L - i.val - 1) := by
  by_cases hnext : i.val + 1 < L
  · simp [hnext]
    set m := L - (i.val + 1) - 1
    have h_exp : L - i.val - 1 = m + 1 := by omega
    rw [h_exp]
    calc
      4 ^ m + 4 ^ m = 2 * 4 ^ m := by ring
      _ ≤ 4 * 4 ^ m := Nat.mul_le_mul_right _ (by decide : 2 ≤ 4)
      _ = 4 ^ (m + 1) := by rw [pow_succ]; ring
  · simp [hnext]

private lemma phase3CancelSplit_agentExpPhi'_pair_noninc
    (s t : AgentState L K) :
    agentExpPhi' (phase3CancelSplit L K s t).1 +
      agentExpPhi' (phase3CancelSplit L K s t).2
        ≤ agentExpPhi' s + agentExpPhi' t := by
  cases hs : s.bias with
  | zero =>
      cases ht : t.bias with
      | zero => simp [phase3CancelSplit, hs, ht, agentExpPhi']
      | dyadic sgn i =>
          by_cases hgt : s.hour.val > i.val
          · have hi : i.val < L := by
              have := s.hour.2; omega
            simp [phase3CancelSplit, hs, ht, hgt, agentExpPhi', hi]
            simpa using tie_split_weight_twice_le (L := L) (i := i) hi
          · simp [phase3CancelSplit, hs, ht, hgt, agentExpPhi']
  | dyadic sgn i =>
      cases ht : t.bias with
      | zero =>
          by_cases hgt : t.hour.val > i.val
          · have hi : i.val < L := by
              have := t.hour.2; omega
            simp [phase3CancelSplit, hs, ht, hgt, agentExpPhi', hi]
            simpa [Nat.add_comm] using tie_split_weight_twice_le (L := L) (i := i) hi
          · simp [phase3CancelSplit, hs, ht, hgt, agentExpPhi']
      | dyadic sgn' j =>
          cases sgn <;> cases sgn'
          · simp [phase3CancelSplit, hs, ht, agentExpPhi']
          · by_cases h_eq : i.val = j.val
            · simp [phase3CancelSplit, hs, ht, h_eq, agentExpPhi']
            · simp [phase3CancelSplit, hs, ht, h_eq, agentExpPhi']
          · by_cases h_eq : i.val = j.val
            · simp [phase3CancelSplit, hs, ht, h_eq, agentExpPhi']
            · simp [phase3CancelSplit, hs, ht, h_eq, agentExpPhi']
          · simp [phase3CancelSplit, hs, ht, agentExpPhi']

private lemma Phase3Transition_agentExpPhi'_pair_noninc
    (s t : AgentState L K) (hs_phase : s.phase.val = 3) (ht_phase : t.phase.val = 3) :
    agentExpPhi' (Phase3Transition L K s t).1 +
      agentExpPhi' (Phase3Transition L K s t).2
        ≤ agentExpPhi' s + agentExpPhi' t := by
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
    let hVal := max s1.hour.val (min L (t1.minute.val / K))
    have h_hour_lt : hVal < L + 1 := by
      exact (Nat.max_lt).mpr ⟨s1.hour.2, Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩
    { s1 with hour := ⟨hVal, h_hour_lt⟩ }
  else if t1.role = .main ∧ t1.bias = .zero ∧ s1.role = .clock then
    s1
  else s1
  let t2 := if s1.role = .main ∧ s1.bias = .zero ∧ t1.role = .clock then
    t1
  else if t1.role = .main ∧ t1.bias = .zero ∧ s1.role = .clock then
    let hVal := max t1.hour.val (min L (s1.minute.val / K))
    have h_hour_lt : hVal < L + 1 := by
      exact (Nat.max_lt).mpr ⟨t1.hour.2, Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩
    { t1 with hour := ⟨hVal, h_hour_lt⟩ }
  else t1
  have hs1 : s1.bias = s.bias := by
    dsimp [s1]
    split_ifs <;> simp [stdCounterSubroutine_preserves_bias_of_phase_three, hs_phase]
  have ht1 : t1.bias = t.bias := by
    dsimp [t1]
    split_ifs <;> simp [stdCounterSubroutine_preserves_bias_of_phase_three, ht_phase]
  have hs2 : s2.bias = s1.bias := by
    dsimp [s2]
    split_ifs <;> simp
  have ht2 : t2.bias = t1.bias := by
    dsimp [t2]
    split_ifs <;> simp
  have hs_eq : agentExpPhi' s2 = agentExpPhi' s :=
    agentExpPhi'_congr_bias (by rw [hs2, hs1])
  have ht_eq : agentExpPhi' t2 = agentExpPhi' t :=
    agentExpPhi'_congr_bias (by rw [ht2, ht1])
  have hfinal :
      agentExpPhi' (Phase3Transition L K s t).1 +
        agentExpPhi' (Phase3Transition L K s t).2
          ≤ agentExpPhi' s2 + agentExpPhi' t2 := by
    unfold Phase3Transition
    change agentExpPhi'
        (if s2.role = .main ∧ t2.role = .main then phase3CancelSplit L K s2 t2
         else (s2, t2)).1 +
      agentExpPhi'
        (if s2.role = .main ∧ t2.role = .main then phase3CancelSplit L K s2 t2
         else (s2, t2)).2
          ≤ agentExpPhi' s2 + agentExpPhi' t2
    by_cases hmain : s2.role = .main ∧ t2.role = .main
    · simp [hmain]
      exact phase3CancelSplit_agentExpPhi'_pair_noninc s2 t2
    · simp [hmain]
  calc
    agentExpPhi' (Phase3Transition L K s t).1 +
        agentExpPhi' (Phase3Transition L K s t).2
        ≤ agentExpPhi' s2 + agentExpPhi' t2 := hfinal
    _ = agentExpPhi' s + agentExpPhi' t := by rw [hs_eq, ht_eq]

/-! ### Phase 6 high-tail potential -/

-- Phase-3/6 "above-band" potential used by `theorem_6_2_phase_three_distribution`:
-- an agent whose index exceeds the target band (`i.val > ell`, paper exponent
-- `< -ell`) carries weight `4^(i.val - ell - 1)`; `Phi = 0` iff every Main agent
-- sits at index `≤ ell`.  (This is the orientation `theorem_6_2` reads: its goal is
-- `i.val ≤ 2` with `ell = 2`.)
private noncomputable def phase6HighTailWeight (ell : ℕ) (i : Fin (L + 1)) : ℕ :=
  if ell < i.val then 4 ^ (i.val - ell - 1) else 0

private noncomputable def phase6HighTailAgent (ell : ℕ) (a : AgentState L K) : ℕ :=
  if a.role = .main then
    match a.bias with
    | .dyadic _ i => phase6HighTailWeight ell i
    | .zero => 0
  else 0

private noncomputable def phase6HighTailPhi (ell : ℕ) (c : Config (AgentState L K)) : ℕ :=
  (c.map (phase6HighTailAgent ell)).sum

-- NOTE (protocol fix 2026-06-10): the previous per-pair non-increase scaffold for
-- `phase6HighTailPhi` (`phase6HighTailWeight_pred_twice_le →
-- doSplit_phase6HighTailAgent_pair_noninc → Phase6Transition_phase6HighTailAgent_pair_noninc`)
-- was specific to the OLD inverted split rule `j → j-1`, under which a Reserve-fuelled
-- split moved a Main DOWN the above-band weight and the pair quantity did not increase.
-- Under the paper-faithful rule `j → j+1` (Doty et al. §7 line 4, mass halved), a split of an
-- above-band Main (index `j > ell`) produces two index-`(j+1)` Mains, so this particular
-- above-band per-pair quantity strictly INCREASES; the per-pair monotone discharge of
-- `hnoninc` does not transfer to the corrected rule.  The Phase-6 progress is the paper's
-- global/probabilistic argument (Lemma 7.2), not a per-pair monotone potential here.
-- `theorem_6_2_phase_three_distribution` takes `hnoninc`/`hprogress` as hypotheses, so it
-- is unaffected.  The dead scaffold (no downstream consumer) is removed rather than left
-- asserting a claim that is false under the corrected protocol.  Discharging `hnoninc`
-- under the corrected rule is deferred to the Lemma-7.2 follow-up.

/-! ### Drift assembly for Theorem 6.1 -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

private def potentialProgressFrom (φ : Config (AgentState L K) → ℕ)
    (c : Config (AgentState L K)) : Prop :=
  ∃ a ∈ c, ∃ b ∈ c, a ≠ b ∧
    φ ((NonuniformMajority L K).scheduledStep c (a, b)) < φ c ∧
    φ ((NonuniformMajority L K).scheduledStep c (b, a)) < φ c

private lemma potentialProgressFrom_descent_prob
    (φ : Config (AgentState L K) → ℕ)
    (c : Config (AgentState L K))
    (hn : 8 ≤ c.card)
    (hprog : potentialProgressFrom φ c) :
    (NonuniformMajority L K).transitionKernel c
      {c' | φ c' < φ c} ≥
    ENNReal.ofReal (2 / ((c.card : ℝ) * ((c.card : ℝ) - 1))) := by
  obtain ⟨a, ha_mem, b, hb_mem, hab, h_ab, h_ba⟩ := hprog
  have hc : 2 ≤ c.card := by omega
  set good : Set (AgentState L K × AgentState L K) :=
    {(a, b), (b, a)} with good_def
  have h_target := stepDistOrSelf_toMeasure_ge c hc
    {c' | φ c' < φ c} good
    (by
      intro pair hpair
      simp only [good_def, Set.mem_insert_iff, Set.mem_singleton_iff] at hpair
      rcases hpair with rfl | rfl
      · exact h_ab
      · exact h_ba)
  change ((NonuniformMajority L K).stepDistOrSelf c).toMeasure _ ≥ _
  calc ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
          {c' | φ c' < φ c}
      ≥ (c.interactionPMF hc).toMeasure good := h_target
    _ ≥ (c.interactionPMF hc) (a, b) + (c.interactionPMF hc) (b, a) := by
        have hab_ne : (a, b) ≠ (b, a) := by
          intro h; exact hab (Prod.mk.inj h).1
        have hpair : ({(a, b), (b, a)} : Set _) = {(a, b)} ∪ {(b, a)} := by
          ext x; simp [Set.mem_insert_iff, Set.mem_singleton_iff, or_comm]
        have h_disj : Disjoint ({(a, b)} : Set _) {(b, a)} :=
          Set.disjoint_singleton.mpr hab_ne
        rw [good_def, hpair, measure_union h_disj
          (DiscreteMeasurableSpace.forall_measurableSet _),
          PMF.toMeasure_apply_singleton _ _ (DiscreteMeasurableSpace.forall_measurableSet _),
          PMF.toMeasure_apply_singleton _ _ (DiscreteMeasurableSpace.forall_measurableSet _)]
    _ ≥ ENNReal.ofReal (2 / ((c.card : ℝ) * ((c.card : ℝ) - 1))) := by
        have hpmf_ab : (c.interactionPMF hc) (a, b) = c.interactionProb a b := rfl
        have hpmf_ba : (c.interactionPMF hc) (b, a) = c.interactionProb b a := rfl
        rw [hpmf_ab, hpmf_ba]
        simp only [Config.interactionProb, Config.interactionCount, hab, hab.symm, ite_false]
        have ha_count : 0 < c.count a := Multiset.count_pos.mpr ha_mem
        have hb_count : 0 < c.count b := Multiset.count_pos.mpr hb_mem
        have h_ab_ct : 1 ≤ c.count a * c.count b :=
          Nat.one_le_iff_ne_zero.mpr (by positivity)
        have h_ba_ct : 1 ≤ c.count b * c.count a :=
          Nat.one_le_iff_ne_zero.mpr (by positivity)
        have h1 : (↑(c.count a * c.count b) : ENNReal) /
            (c.totalPairs : ENNReal) ≥ 1 / (c.totalPairs : ENNReal) := by
          apply ENNReal.div_le_div_right
          exact_mod_cast h_ab_ct
        have h2 : (↑(c.count b * c.count a) : ENNReal) /
            (c.totalPairs : ENNReal) ≥ 1 / (c.totalPairs : ENNReal) := by
          apply ENNReal.div_le_div_right
          exact_mod_cast h_ba_ct
        calc (↑(c.count a * c.count b) : ENNReal) /
                (c.totalPairs : ENNReal) +
              (↑(c.count b * c.count a) : ENNReal) /
                (c.totalPairs : ENNReal)
            ≥ 1 / (c.totalPairs : ENNReal) + 1 / (c.totalPairs : ENNReal) :=
              add_le_add h1 h2
          _ = 2 / (c.totalPairs : ENNReal) := by
              rw [show (1 : ENNReal) / c.totalPairs + 1 / c.totalPairs =
                (1 + 1) / c.totalPairs from by rw [ENNReal.add_div]]
              norm_num
          _ = ENNReal.ofReal (2 / ((c.card : ℝ) * ((c.card : ℝ) - 1))) := by
              have hcard_pos : (0 : ℝ) < c.card :=
                Nat.cast_pos.mpr (by omega)
              have hcard_sub_pos : (0 : ℝ) < (c.card : ℝ) - 1 := by
                have h8 : (8 : ℝ) ≤ c.card := by exact_mod_cast hn
                linarith
              have hprod_pos : (0 : ℝ) < (c.card : ℝ) * ((c.card : ℝ) - 1) :=
                mul_pos hcard_pos hcard_sub_pos
              rw [ENNReal.ofReal_div_of_pos hprod_pos]
              congr 1
              · exact (ENNReal.ofReal_ofNat 2).symm
              · unfold Config.totalPairs
                have h1le : 1 ≤ c.card := by omega
                rw [show (c.card : ℝ) * ((c.card : ℝ) - 1) =
                    ((c.card * (c.card - 1) : ℕ) : ℝ) from by
                  push_cast [Nat.cast_sub h1le]; ring]
                exact (ENNReal.ofReal_natCast _).symm

private def upperTailPost (c : Config (AgentState L K)) : Prop :=
  upperTailPhi' c = 0

private noncomputable def upperTailPhiExt (n : ℕ)
    (c : Config (AgentState L K)) : ℕ :=
  if c.card = n then upperTailPhi' c else 0

theorem theorem_6_1_tie_min_exponent
    (c₀ : Config (AgentState L K))
    (hn : 8 ≤ c₀.card) (hcard : c₀.card = n)
    (hphase : ∀ a ∈ c₀, a.phase.val = 3)
    (htie : prePhase4MassSum c₀ = 0)
    (hnoninc : ∀ c, c.card = n →
      ∀ᵐ c' ∂((NonuniformMajority L K).transitionKernel c),
        upperTailPhi' c' ≤ upperTailPhi' c)
    (hprogress : ∀ c, c.card = n → upperTailPhi' c ≠ 0 →
      potentialProgressFrom (upperTailPhi' (L := L) (K := K)) c)
    (hbounded : ∀ c : Config (AgentState L K), c.card = n → upperTailPhi' c ≤ n)
    (t : ℕ) (ht : (2 * (n : ℝ) ^ 2 * ((n : ℝ) - 1) * Real.log (n : ℝ)) < ↑t) :
    ((NonuniformMajority L K).transitionKernel ^ t) c₀
        {c : Config (AgentState L K) |
          ¬(∀ a ∈ c, a.phase.val = 3 →
            match a.bias with | .dyadic _ i => i.val = L | .zero => True)} ≤
      ENNReal.ofReal (1 / ((n : ℝ) ^ 2)) := by
  have hn8 : 8 ≤ n := hcard ▸ hn
  set φ := upperTailPhiExt n (L := L) (K := K)
  set r := 1 - ENNReal.ofReal (2 / ((n : ℝ) * ((n : ℝ) - 1))) / (n : ℝ≥0∞)
  have hφ_eq : ∀ c, c.card = n → φ c = upperTailPhi' c := by
    intro c hc; show upperTailPhiExt n c = _; unfold upperTailPhiExt; simp [hc]
  have hφ_zero_ne : ∀ c, c.card ≠ n → φ c = 0 := by
    intro c hc; show upperTailPhiExt n c = _; unfold upperTailPhiExt; simp [hc]
  have hφ_le_n : ∀ c, φ c ≤ n := by
    intro c; by_cases hc : c.card = n
    · rw [hφ_eq c hc]; exact hbounded c hc
    · rw [hφ_zero_ne c hc]; omega
  have h_card_ae : ∀ c, c.card = n →
      ∀ᵐ c' ∂((NonuniformMajority L K).transitionKernel c), c'.card = n := by
    intro c hc
    change ∀ᵐ c' ∂((NonuniformMajority L K).stepDistOrSelf c).toMeasure, _
    rw [MeasureTheory.ae_iff,
      PMF.toMeasure_apply_eq_zero_iff _
        (DiscreteMeasurableSpace.forall_measurableSet _)]
    exact Set.disjoint_left.mpr fun c' hc' hbad =>
      hbad (Protocol.stepDistOrSelf_support_card_eq _ c c' hc' ▸ hc)
  have h_drift : ∀ c, ∫⁻ c', (φ c' : ℝ≥0∞)
      ∂((NonuniformMajority L K).transitionKernel c) ≤ r * (φ c : ℝ≥0∞) := by
    intro c
    haveI : IsProbabilityMeasure ((NonuniformMajority L K).transitionKernel c) :=
      (inferInstance : IsMarkovKernel
        (NonuniformMajority L K).transitionKernel).isProbabilityMeasure c
    by_cases hc_card : c.card = n; swap
    · rw [show (φ c : ℝ≥0∞) = 0 from by simp [hφ_zero_ne c hc_card], mul_zero]
      apply le_of_eq; apply lintegral_eq_zero_of_ae_eq_zero
      change ∀ᵐ c' ∂((NonuniformMajority L K).stepDistOrSelf c).toMeasure, _
      rw [MeasureTheory.ae_iff,
        PMF.toMeasure_apply_eq_zero_iff _
          (DiscreteMeasurableSpace.forall_measurableSet _)]
      exact Set.disjoint_left.mpr fun c' hc' hbad => by
        simp only [Set.mem_setOf_eq, not_not] at hbad
        exact hbad (show (φ c' : ℝ≥0∞) = 0 from by
          simp [hφ_zero_ne c'
            ((Protocol.stepDistOrSelf_support_card_eq _ c c' hc') ▸ hc_card)])
    by_cases hφ_ne : upperTailPhi' c = 0
    · rw [show (φ c : ℝ≥0∞) = 0 from by simp [hφ_eq c hc_card, hφ_ne], mul_zero]
      apply le_of_eq; apply lintegral_eq_zero_of_ae_eq_zero
      filter_upwards [hnoninc c hc_card, h_card_ae c hc_card] with c' hle hc'_card
      show (φ c' : ℝ≥0∞) = 0
      have h0 : φ c' = 0 := by rw [hφ_eq c' hc'_card]; omega
      simp [h0]
    · have hae_ext : ∀ᵐ c' ∂((NonuniformMajority L K).transitionKernel c),
          φ c' ≤ φ c := by
        filter_upwards [hnoninc c hc_card, h_card_ae c hc_card] with c' hle hc'_card
        rw [hφ_eq c' hc'_card, hφ_eq c hc_card]; exact hle
      have h_desc_ext : (NonuniformMajority L K).transitionKernel c {c' | φ c' < φ c} ≥
          ENNReal.ofReal (2 / ((n : ℝ) * ((n : ℝ) - 1))) := by
        have h_sub : {c' | upperTailPhi' c' < upperTailPhi' c} ⊆ {c' | φ c' < φ c} := by
          intro c' hc'; simp only [Set.mem_setOf_eq] at hc' ⊢
          by_cases hc'_card : c'.card = n
          · rw [hφ_eq c' hc'_card, hφ_eq c hc_card]; exact hc'
          · rw [hφ_zero_ne c' hc'_card, hφ_eq c hc_card]
            exact Nat.pos_of_ne_zero hφ_ne
        have h_prob := potentialProgressFrom_descent_prob upperTailPhi' c
          (hc_card ▸ hn8) (hprogress c hc_card hφ_ne)
        calc (NonuniformMajority L K).transitionKernel c {c' | φ c' < φ c}
            ≥ (NonuniformMajority L K).transitionKernel c
                {c' | upperTailPhi' c' < upperTailPhi' c} :=
              MeasureTheory.measure_mono h_sub
          _ ≥ ENNReal.ofReal (2 / (↑c.card * (↑c.card - 1))) := h_prob
          _ = ENNReal.ofReal (2 / ((n : ℝ) * ((n : ℝ) - 1))) := by rw [hc_card]
      have hv_le_n : (φ c : ℝ≥0∞) ≤ (n : ℝ≥0∞) := by exact_mod_cast hφ_le_n c
      have hn_ne_zero : (n : ℝ≥0∞) ≠ 0 := by
        simp only [ne_eq, Nat.cast_eq_zero]; omega
      have hn_ne_top : (n : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top n
      set q_nnr := (ENNReal.ofReal (2 / ((n : ℝ) * ((n : ℝ) - 1)))).toNNReal
      have hq_coe : (q_nnr : ℝ≥0∞) =
          ENNReal.ofReal (2 / ((n : ℝ) * ((n : ℝ) - 1))) :=
        ENNReal.coe_toNNReal ENNReal.ofReal_ne_top
      have h_int_le := lintegral_nat_le_of_descent
        ((NonuniformMajority L K).transitionKernel c) φ (φ c) hae_ext q_nnr
        (by rw [hq_coe]; exact h_desc_ext)
      have hmul_le :
          (q_nnr : ℝ≥0∞) / (n : ℝ≥0∞) * (φ c : ℝ≥0∞) ≤ (q_nnr : ℝ≥0∞) :=
        calc (q_nnr : ℝ≥0∞) / (n : ℝ≥0∞) * (φ c : ℝ≥0∞)
            ≤ (q_nnr : ℝ≥0∞) / (n : ℝ≥0∞) * (n : ℝ≥0∞) :=
              mul_le_mul_left' hv_le_n _
          _ = (q_nnr : ℝ≥0∞) :=
              ENNReal.div_mul_cancel hn_ne_zero hn_ne_top
      have hmul_sub :
          (1 - (q_nnr : ℝ≥0∞) / (n : ℝ≥0∞)) * (φ c : ℝ≥0∞) =
            (φ c : ℝ≥0∞) -
              ((q_nnr : ℝ≥0∞) / (n : ℝ≥0∞) * (φ c : ℝ≥0∞)) := by
        simpa [one_mul] using
          ENNReal.sub_mul (a := 1)
            (b := (q_nnr : ℝ≥0∞) / (n : ℝ≥0∞))
            (c := (φ c : ℝ≥0∞))
      calc ∫⁻ c', (φ c' : ℝ≥0∞) ∂((NonuniformMajority L K).transitionKernel c)
          ≤ (φ c : ℝ≥0∞) - (q_nnr : ℝ≥0∞) := h_int_le
        _ ≤ (φ c : ℝ≥0∞) -
              ((q_nnr : ℝ≥0∞) / (n : ℝ≥0∞) * (φ c : ℝ≥0∞)) :=
            tsub_le_tsub_left hmul_le _
        _ = (1 - (q_nnr : ℝ≥0∞) / (n : ℝ≥0∞)) * (φ c : ℝ≥0∞) :=
            hmul_sub.symm
        _ = r * (φ c : ℝ≥0∞) := by rw [hq_coe]
  have h_meas : Measurable (fun c => (φ c : ℝ≥0∞)) := Measurable.of_discrete
  have h_decay := PopProtoCommon.measure_potential_ge_one
    (NonuniformMajority L K).transitionKernel
    (fun c => (φ c : ℝ≥0∞)) h_meas r h_drift t c₀
  have h_card_zero : ((NonuniformMajority L K).transitionKernel ^ t) c₀
      {c' | c'.card ≠ n} = 0 := by
    apply Protocol.transitionKernel_pow_eq_zero_of_forall_not_reachable
    intro c' hc' hreach
    exact hc' (Protocol.reachable_card_eq hreach ▸ hcard)
  have h_subset : {c : Config (AgentState L K) |
      ¬(∀ a ∈ c, a.phase.val = 3 →
        match a.bias with | .dyadic _ i => i.val = L | .zero => True)} ⊆
      {c | 1 ≤ (φ c : ℝ≥0∞)} ∪ {c | c.card ≠ n} := by
    intro c hc
    by_cases hc_card : c.card = n; swap
    · right; exact hc_card
    · left; simp only [Set.mem_setOf_eq]; rw [hφ_eq c hc_card]
      have hne : upperTailPhi' c ≠ 0 := by
        intro h0; apply hc; intro a ha hph
        have : agentExpPhi' a = 0 :=
          Multiset.sum_eq_zero_iff.mp h0 _ (Multiset.mem_map_of_mem _ ha)
        unfold agentExpPhi' at this
        match hb : a.bias with
        | .zero => trivial
        | .dyadic _ i =>
          rw [hb] at this; simp only at this
          split_ifs at this with hi
          · exact absurd this (by positivity)
          · omega
      exact_mod_cast Nat.pos_of_ne_zero hne
  have hΦ_le_n : (φ c₀ : ℝ≥0∞) ≤ (n : ℝ≥0∞) := by
    exact_mod_cast hφ_le_n c₀
  have h_num : r ^ t * (n : ℝ≥0∞) ≤ ENNReal.ofReal (1 / (n : ℝ) ^ 2) :=
    ennreal_r_pow_mul_n_le_phase3 n t hn8 ht
  calc ((NonuniformMajority L K).transitionKernel ^ t) c₀
          {c | ¬(∀ a ∈ c, a.phase.val = 3 →
            match a.bias with | .dyadic _ i => i.val = L | .zero => True)}
      ≤ ((NonuniformMajority L K).transitionKernel ^ t) c₀
          ({c | 1 ≤ (φ c : ℝ≥0∞)} ∪ {c | c.card ≠ n}) :=
        MeasureTheory.measure_mono h_subset
    _ ≤ ((NonuniformMajority L K).transitionKernel ^ t) c₀
          {c | 1 ≤ (φ c : ℝ≥0∞)} +
        ((NonuniformMajority L K).transitionKernel ^ t) c₀
          {c | c.card ≠ n} := MeasureTheory.measure_union_le _ _
    _ = ((NonuniformMajority L K).transitionKernel ^ t) c₀
          {c | 1 ≤ (φ c : ℝ≥0∞)} := by rw [h_card_zero, add_zero]
    _ ≤ r ^ t * (φ c₀ : ℝ≥0∞) := h_decay
    _ ≤ r ^ t * (n : ℝ≥0∞) := by gcongr
    _ ≤ ENNReal.ofReal (1 / (n : ℝ) ^ 2) := h_num

/-- **Doty et al. Theorem 6.2**: non-tie case. Assume `|g| < 0.025·|M|`. Let
`−l = ⌊log₂(0.4·|M| / |g|)⌋` and `i = sign(g)`. Let `M*` be the set of
Main agents with opinion `i` and exponent ∈ {−l, −(l+1), −(l+2)}. Then
by the end of Phase 3, `|M*| ≥ 0.92·|M|` with high probability
`1 − O(1/n²)`.

The event is quantified on a probability space `(Ω, μ)`. The proof
(using Theorem 6.9 + the Phase 3 cancel/split analysis) is deferred. -/
theorem theorem_6_2_phase_three_distribution
    (c₀ : Config (AgentState L K))
    (hn : 8 ≤ c₀.card)
    (hphase : ∀ a ∈ c₀, a.phase.val = 3)
    (hpost : ∀ a ∈ c₀, a.role = .main → a.bias ≠ .zero →
      match a.bias with | .dyadic _ i => i.val ≤ 2 | .zero => True)
    (hnoninc : ∀ c, c.card = c₀.card →
      ∀ᵐ c' ∂((NonuniformMajority L K).transitionKernel c),
        phase6HighTailPhi 2 c' ≤ phase6HighTailPhi 2 c)
    (hprogress : ∀ c, c.card = c₀.card → phase6HighTailPhi 2 c ≠ 0 →
      potentialProgressFrom (phase6HighTailPhi (L := L) (K := K) 2) c)
    (hbounded : ∀ c : Config (AgentState L K), c.card = c₀.card →
      phase6HighTailPhi 2 c ≤ c₀.card)
    (t : ℕ) :
    ((NonuniformMajority L K).transitionKernel ^ t) c₀
        {c : Config (AgentState L K) |
          ¬(∀ a ∈ c, 4 ≤ a.phase.val → a.role = .main → a.bias ≠ .zero →
            match a.bias with | .dyadic _ i => i.val ≤ 2 | .zero => True)} ≤
      ENNReal.ofReal (1 / ((c₀.card : ℝ) ^ 2)) := by
  set n := c₀.card
  have hn8 : 8 ≤ n := hn
  set φ : Config (AgentState L K) → ℕ := fun c =>
    if c.card = n then phase6HighTailPhi 2 c else 0
  set r := 1 - ENNReal.ofReal (2 / ((n : ℝ) * ((n : ℝ) - 1))) / (n : ℝ≥0∞)
  have hφ_eq : ∀ c, c.card = n → φ c = phase6HighTailPhi 2 c := by
    intro c hc; show (if c.card = n then _ else _) = _; simp [hc]
  have hφ_zero_ne : ∀ c, c.card ≠ n → φ c = 0 := by
    intro c hc; show (if c.card = n then _ else _) = _; simp [hc]
  have hφ_le_n : ∀ c, φ c ≤ n := by
    intro c; by_cases hc : c.card = n
    · rw [hφ_eq c hc]; exact hbounded c hc
    · rw [hφ_zero_ne c hc]; omega
  have h_card_ae : ∀ c, c.card = n →
      ∀ᵐ c' ∂((NonuniformMajority L K).transitionKernel c), c'.card = n := by
    intro c hc
    change ∀ᵐ c' ∂((NonuniformMajority L K).stepDistOrSelf c).toMeasure, _
    rw [MeasureTheory.ae_iff,
      PMF.toMeasure_apply_eq_zero_iff _
        (DiscreteMeasurableSpace.forall_measurableSet _)]
    exact Set.disjoint_left.mpr fun c' hc' hbad =>
      hbad (Protocol.stepDistOrSelf_support_card_eq _ c c' hc' ▸ hc)
  have h_drift : ∀ c, ∫⁻ c', (φ c' : ℝ≥0∞)
      ∂((NonuniformMajority L K).transitionKernel c) ≤ r * (φ c : ℝ≥0∞) := by
    intro c
    haveI : IsProbabilityMeasure ((NonuniformMajority L K).transitionKernel c) :=
      (inferInstance : IsMarkovKernel
        (NonuniformMajority L K).transitionKernel).isProbabilityMeasure c
    by_cases hc_card : c.card = n; swap
    · rw [show (φ c : ℝ≥0∞) = 0 from by simp [hφ_zero_ne c hc_card], mul_zero]
      apply le_of_eq; apply lintegral_eq_zero_of_ae_eq_zero
      change ∀ᵐ c' ∂((NonuniformMajority L K).stepDistOrSelf c).toMeasure, _
      rw [MeasureTheory.ae_iff,
        PMF.toMeasure_apply_eq_zero_iff _
          (DiscreteMeasurableSpace.forall_measurableSet _)]
      exact Set.disjoint_left.mpr fun c' hc' hbad => by
        simp only [Set.mem_setOf_eq, not_not] at hbad
        exact hbad (show (φ c' : ℝ≥0∞) = 0 from by
          simp [hφ_zero_ne c'
            ((Protocol.stepDistOrSelf_support_card_eq _ c c' hc') ▸ hc_card)])
    by_cases hφ_ne : phase6HighTailPhi 2 c = 0
    · rw [show (φ c : ℝ≥0∞) = 0 from by simp [hφ_eq c hc_card, hφ_ne], mul_zero]
      apply le_of_eq; apply lintegral_eq_zero_of_ae_eq_zero
      filter_upwards [hnoninc c hc_card, h_card_ae c hc_card] with c' hle hc'_card
      show (φ c' : ℝ≥0∞) = 0
      have h0 : φ c' = 0 := by rw [hφ_eq c' hc'_card]; omega
      simp [h0]
    · have hae_ext : ∀ᵐ c' ∂((NonuniformMajority L K).transitionKernel c),
          φ c' ≤ φ c := by
        filter_upwards [hnoninc c hc_card, h_card_ae c hc_card] with c' hle hc'_card
        rw [hφ_eq c' hc'_card, hφ_eq c hc_card]; exact hle
      have h_desc_ext : (NonuniformMajority L K).transitionKernel c {c' | φ c' < φ c} ≥
          ENNReal.ofReal (2 / ((n : ℝ) * ((n : ℝ) - 1))) := by
        have h_sub : {c' | phase6HighTailPhi 2 c' < phase6HighTailPhi 2 c} ⊆
            {c' | φ c' < φ c} := by
          intro c' hc'; simp only [Set.mem_setOf_eq] at hc' ⊢
          by_cases hc'_card : c'.card = n
          · rw [hφ_eq c' hc'_card, hφ_eq c hc_card]; exact hc'
          · rw [hφ_zero_ne c' hc'_card, hφ_eq c hc_card]
            exact Nat.pos_of_ne_zero hφ_ne
        have h_prob := potentialProgressFrom_descent_prob (phase6HighTailPhi 2) c
          (hc_card ▸ hn8) (hprogress c hc_card hφ_ne)
        calc (NonuniformMajority L K).transitionKernel c {c' | φ c' < φ c}
            ≥ (NonuniformMajority L K).transitionKernel c
                {c' | phase6HighTailPhi 2 c' < phase6HighTailPhi 2 c} :=
              MeasureTheory.measure_mono h_sub
          _ ≥ ENNReal.ofReal (2 / (↑c.card * (↑c.card - 1))) := h_prob
          _ = ENNReal.ofReal (2 / ((n : ℝ) * ((n : ℝ) - 1))) := by rw [hc_card]
      have hv_le_n : (φ c : ℝ≥0∞) ≤ (n : ℝ≥0∞) := by exact_mod_cast hφ_le_n c
      have hn_ne_zero : (n : ℝ≥0∞) ≠ 0 := by
        simp only [ne_eq, Nat.cast_eq_zero]; omega
      have hn_ne_top : (n : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top n
      set q_nnr := (ENNReal.ofReal (2 / ((n : ℝ) * ((n : ℝ) - 1)))).toNNReal
      have hq_coe : (q_nnr : ℝ≥0∞) =
          ENNReal.ofReal (2 / ((n : ℝ) * ((n : ℝ) - 1))) :=
        ENNReal.coe_toNNReal ENNReal.ofReal_ne_top
      have h_int_le := lintegral_nat_le_of_descent
        ((NonuniformMajority L K).transitionKernel c) φ (φ c) hae_ext q_nnr
        (by rw [hq_coe]; exact h_desc_ext)
      have hmul_le :
          (q_nnr : ℝ≥0∞) / (n : ℝ≥0∞) * (φ c : ℝ≥0∞) ≤ (q_nnr : ℝ≥0∞) :=
        calc (q_nnr : ℝ≥0∞) / (n : ℝ≥0∞) * (φ c : ℝ≥0∞)
            ≤ (q_nnr : ℝ≥0∞) / (n : ℝ≥0∞) * (n : ℝ≥0∞) :=
              mul_le_mul_left' hv_le_n _
          _ = (q_nnr : ℝ≥0∞) :=
              ENNReal.div_mul_cancel hn_ne_zero hn_ne_top
      have hmul_sub :
          (1 - (q_nnr : ℝ≥0∞) / (n : ℝ≥0∞)) * (φ c : ℝ≥0∞) =
            (φ c : ℝ≥0∞) -
              ((q_nnr : ℝ≥0∞) / (n : ℝ≥0∞) * (φ c : ℝ≥0∞)) := by
        simpa [one_mul] using
          ENNReal.sub_mul (a := 1)
            (b := (q_nnr : ℝ≥0∞) / (n : ℝ≥0∞))
            (c := (φ c : ℝ≥0∞))
      calc ∫⁻ c', (φ c' : ℝ≥0∞) ∂((NonuniformMajority L K).transitionKernel c)
          ≤ (φ c : ℝ≥0∞) - (q_nnr : ℝ≥0∞) := h_int_le
        _ ≤ (φ c : ℝ≥0∞) -
              ((q_nnr : ℝ≥0∞) / (n : ℝ≥0∞) * (φ c : ℝ≥0∞)) :=
            tsub_le_tsub_left hmul_le _
        _ = (1 - (q_nnr : ℝ≥0∞) / (n : ℝ≥0∞)) * (φ c : ℝ≥0∞) :=
            hmul_sub.symm
        _ = r * (φ c : ℝ≥0∞) := by rw [hq_coe]
  have h_meas : Measurable (fun c => (φ c : ℝ≥0∞)) := Measurable.of_discrete
  have h_decay := PopProtoCommon.measure_potential_ge_one
    (NonuniformMajority L K).transitionKernel
    (fun c => (φ c : ℝ≥0∞)) h_meas r h_drift t c₀
  have h_card_zero : ((NonuniformMajority L K).transitionKernel ^ t) c₀
      {c' | c'.card ≠ n} = 0 := by
    apply Protocol.transitionKernel_pow_eq_zero_of_forall_not_reachable
    intro c' hc' hreach
    exact hc' (Protocol.reachable_card_eq hreach)
  have h_subset : {c : Config (AgentState L K) |
      ¬(∀ a ∈ c, 4 ≤ a.phase.val → a.role = .main → a.bias ≠ .zero →
        match a.bias with | .dyadic _ i => i.val ≤ 2 | .zero => True)} ⊆
      {c | 1 ≤ (φ c : ℝ≥0∞)} ∪ {c | c.card ≠ n} := by
    intro c hc
    by_cases hc_card : c.card = n; swap
    · right; exact hc_card
    · left; simp only [Set.mem_setOf_eq]; rw [hφ_eq c hc_card]
      have hne : phase6HighTailPhi 2 c ≠ 0 := by
        intro h0; apply hc; intro a ha _ hrole hbias
        have : phase6HighTailAgent 2 a = 0 :=
          Multiset.sum_eq_zero_iff.mp h0 _ (Multiset.mem_map_of_mem _ ha)
        unfold phase6HighTailAgent at this
        rw [show a.role = .main from hrole] at this
        simp only [↓reduceIte] at this
        match hb : a.bias with
        | .zero => exact absurd hb hbias
        | .dyadic _ i =>
          rw [hb] at this
          unfold phase6HighTailWeight at this
          simp only at this
          split_ifs at this with hi
          · exact absurd this (by positivity)
          · push_neg at hi; exact hi
      exact_mod_cast Nat.pos_of_ne_zero hne
  have hΦ_zero : φ c₀ = 0 := by
    show (if c₀.card = n then _ else _) = _
    simp only [show c₀.card = n from rfl, ↓reduceIte]
    apply Multiset.sum_eq_zero_iff.mpr
    intro x hx
    rw [Multiset.mem_map] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    simp only [phase6HighTailAgent]
    by_cases hrole : a.role = .main; swap
    · simp [hrole]
    · simp only [hrole, ↓reduceIte]
      match hb : a.bias with
      | .zero => rfl
      | .dyadic _ i =>
        have hle : i.val ≤ 2 := by
          have := hpost a ha hrole (by simp [hb])
          simp only [hb] at this; exact this
        simp only [phase6HighTailWeight, show ¬(2 < i.val) from by omega, ↓reduceIte]
  calc ((NonuniformMajority L K).transitionKernel ^ t) c₀
          {c | ¬(∀ a ∈ c, 4 ≤ a.phase.val → a.role = .main → a.bias ≠ .zero →
            match a.bias with | .dyadic _ i => i.val ≤ 2 | .zero => True)}
      ≤ ((NonuniformMajority L K).transitionKernel ^ t) c₀
          ({c | 1 ≤ (φ c : ℝ≥0∞)} ∪ {c | c.card ≠ n}) :=
        MeasureTheory.measure_mono h_subset
    _ ≤ ((NonuniformMajority L K).transitionKernel ^ t) c₀
          {c | 1 ≤ (φ c : ℝ≥0∞)} +
        ((NonuniformMajority L K).transitionKernel ^ t) c₀
          {c | c.card ≠ n} := MeasureTheory.measure_union_le _ _
    _ = ((NonuniformMajority L K).transitionKernel ^ t) c₀
          {c | 1 ≤ (φ c : ℝ≥0∞)} := by rw [h_card_zero, add_zero]
    _ ≤ r ^ t * (φ c₀ : ℝ≥0∞) := h_decay
    _ = 0 := by rw [hΦ_zero]; simp
    _ ≤ ENNReal.ofReal (1 / ((n : ℝ) ^ 2)) := zero_le'

/-! ### §7 — cleanup phases (5–8) and stable backup (10) -/

/-- **Doty et al. Lemma 7.1**: by end of Phase 5, all Reserve agents have
`sample ≠ ⊥`, with high probability `1 − O(1/n²)`.

Equivalently: the probability that some Reserve agent fails to sample
an exponent by the end of Phase 5 decays as `O(1/n²)`. The event is
defined on a protocol execution `(Ω, μ)` with population size `n`.
The proof (via Lemma 4.7 epidemic bound) is deferred. -/
theorem lemma_7_1_reserve_sampled
    (c₀ : Config (AgentState L K))
    (hn : 8 ≤ c₀.card)
    (hphase5 : ∀ a ∈ c₀, 5 ≤ a.phase.val)
    (hpost : ∀ a ∈ c₀, a.role = .reserve → a.hour.val < L)
    (t : ℕ) :
    ((NonuniformMajority L K).transitionKernel ^ t) c₀
        {c : Config (AgentState L K) |
          ¬(∀ a ∈ c, 6 ≤ a.phase.val → a.role = .reserve → a.hour.val < L)} ≤
      ENNReal.ofReal (1 / ((c₀.card : ℝ) ^ 2)) := by
  set Q := fun c : Config (AgentState L K) =>
    (∀ a ∈ c, 5 ≤ a.phase.val) ∧ (∀ a ∈ c, a.role = .reserve → a.hour.val < L)
  suffices h : ((NonuniformMajority L K).transitionKernel ^ t) c₀ {c | ¬Q c} = 0 by
    have hmono : {c : Config (AgentState L K) |
        ¬(∀ a ∈ c, 6 ≤ a.phase.val → a.role = .reserve → a.hour.val < L)} ⊆ {c | ¬Q c} := by
      intro c hc ⟨_, hprop⟩
      exact hc (fun a ha _ => hprop a ha)
    exact le_trans (MeasureTheory.measure_mono hmono) (h ▸ zero_le')
  exact absorbing_implies_zero Q (fun c c' ⟨hcph, hcprop⟩ hsupp => by
    constructor
    · intro a' ha'
      unfold Protocol.stepDistOrSelf at hsupp
      split_ifs at hsupp with h_size
      · obtain ⟨⟨r₁, r₂⟩, heq⟩ := Protocol.stepDist_support _ _ h_size _ hsupp
        subst heq
        unfold Protocol.scheduledStep Protocol.stepOrSelf at ha'
        split_ifs at ha' with h_app
        · rw [Multiset.mem_add] at ha'
          rcases ha' with h_rem | h_new
          · exact hcph a' (Multiset.mem_of_le (Multiset.sub_le_self _ _) h_rem)
          · simp only [Multiset.insert_eq_cons, Multiset.mem_cons,
                Multiset.mem_singleton] at h_new
            rcases h_new with rfl | rfl
            · exact le_trans (hcph r₁ (Multiset.mem_of_le h_app (by simp)))
                (Transition_phase_monotone (L := L) (K := K) r₁ r₂).1
            · exact le_trans (hcph r₂ (Multiset.mem_of_le h_app (by simp)))
                (Transition_phase_monotone (L := L) (K := K) r₁ r₂).2
        · exact hcph a' ha'
      · rw [PMF.mem_support_pure_iff] at hsupp; subst hsupp; exact hcph a' ha'
    · intro a' ha' hrole
      unfold Protocol.stepDistOrSelf at hsupp
      split_ifs at hsupp with h_size
      · obtain ⟨⟨r₁, r₂⟩, heq⟩ := Protocol.stepDist_support _ _ h_size _ hsupp
        subst heq
        unfold Protocol.scheduledStep Protocol.stepOrSelf at ha'
        split_ifs at ha' with h_app
        · rw [Multiset.mem_add] at ha'
          rcases ha' with h_rem | h_new
          · exact hcprop a' (Multiset.mem_of_le (Multiset.sub_le_self _ _) h_rem) hrole
          · simp only [Multiset.insert_eq_cons, Multiset.mem_cons,
                Multiset.mem_singleton] at h_new
            rcases h_new with rfl | rfl
            · have hpres := Transition_preserves_reserve_hour_lt_L_of_phase_ge_five
                (L := L) (K := K) r₁ r₂
                (hcph r₁ (Multiset.mem_of_le h_app (by simp)))
                (hcph r₂ (Multiset.mem_of_le h_app (by simp)))
                (hcprop r₁ (Multiset.mem_of_le h_app (by simp)))
                (hcprop r₂ (Multiset.mem_of_le h_app (by simp)))
              simp only [NonuniformMajority] at hrole ⊢
              exact hpres.1 hrole
            · have hpres := Transition_preserves_reserve_hour_lt_L_of_phase_ge_five
                (L := L) (K := K) r₁ r₂
                (hcph r₁ (Multiset.mem_of_le h_app (by simp)))
                (hcph r₂ (Multiset.mem_of_le h_app (by simp)))
                (hcprop r₁ (Multiset.mem_of_le h_app (by simp)))
                (hcprop r₂ (Multiset.mem_of_le h_app (by simp)))
              simp only [NonuniformMajority] at hrole ⊢
              exact hpres.2 hrole
        · exact hcprop a' ha' hrole
      · rw [PMF.mem_support_pure_iff] at hsupp; subst hsupp; exact hcprop a' ha' hrole)
    c₀ ⟨hphase5, hpost⟩ t

private def phase6ExponentBoundPost (ell : ℕ) (c : Config (AgentState L K)) : Prop :=
  ∀ a ∈ c, a.role = .main → a.bias ≠ .zero →
    match a.bias with | .dyadic _ i => i.val ≤ ell | .zero => True

/-- **Doty et al. Lemma 7.2**: by end of Phase 6, all biased agents have
exponent `≤ −l`, with high probability `1 − O(1/n²)`.

The event is defined on a protocol execution `(Ω, μ)`. The proof
(using Lemma 7.1 + the split analysis of Phase 6) is deferred. -/
theorem lemma_7_2_phase_six_exponents
    (c₀ : Config (AgentState L K))
    (hn : 8 ≤ c₀.card)
    (hphase6 : ∀ a ∈ c₀, a.phase.val = 6)
    (hsampled : ∀ a ∈ c₀, a.role = .reserve → a.hour.val < L)
    (hpost : ∀ a ∈ c₀, a.role = .main → a.bias ≠ .zero →
      match a.bias with | .dyadic _ i => i.val ≤ 2 | .zero => True)
    (hnoninc : ∀ c, c.card = c₀.card →
      ∀ᵐ c' ∂((NonuniformMajority L K).transitionKernel c),
        phase6HighTailPhi 2 c' ≤ phase6HighTailPhi 2 c)
    (hprogress : ∀ c, c.card = c₀.card → phase6HighTailPhi 2 c ≠ 0 →
      potentialProgressFrom (phase6HighTailPhi (L := L) (K := K) 2) c)
    (hbounded : ∀ c : Config (AgentState L K), c.card = c₀.card →
      phase6HighTailPhi 2 c ≤ c₀.card)
    (t : ℕ) :
    ((NonuniformMajority L K).transitionKernel ^ t) c₀
        {c : Config (AgentState L K) |
          ¬(∀ a ∈ c, 7 ≤ a.phase.val → a.role = .main → a.bias ≠ .zero →
            match a.bias with | .dyadic _ i => i.val ≤ 2 | .zero => True)} ≤
      ENNReal.ofReal (1 / ((c₀.card : ℝ) ^ 2)) := by
  set n := c₀.card
  have hn8 : 8 ≤ n := hn
  set φ : Config (AgentState L K) → ℕ := fun c =>
    if c.card = n then phase6HighTailPhi 2 c else 0
  set r := 1 - ENNReal.ofReal (2 / ((n : ℝ) * ((n : ℝ) - 1))) / (n : ℝ≥0∞)
  have hφ_eq : ∀ c, c.card = n → φ c = phase6HighTailPhi 2 c := by
    intro c hc; show (if c.card = n then _ else _) = _; simp [hc]
  have hφ_zero_ne : ∀ c, c.card ≠ n → φ c = 0 := by
    intro c hc; show (if c.card = n then _ else _) = _; simp [hc]
  have hφ_le_n : ∀ c, φ c ≤ n := by
    intro c; by_cases hc : c.card = n
    · rw [hφ_eq c hc]; exact hbounded c hc
    · rw [hφ_zero_ne c hc]; omega
  have h_card_ae : ∀ c, c.card = n →
      ∀ᵐ c' ∂((NonuniformMajority L K).transitionKernel c), c'.card = n := by
    intro c hc
    change ∀ᵐ c' ∂((NonuniformMajority L K).stepDistOrSelf c).toMeasure, _
    rw [MeasureTheory.ae_iff,
      PMF.toMeasure_apply_eq_zero_iff _
        (DiscreteMeasurableSpace.forall_measurableSet _)]
    exact Set.disjoint_left.mpr fun c' hc' hbad =>
      hbad (Protocol.stepDistOrSelf_support_card_eq _ c c' hc' ▸ hc)
  have h_drift : ∀ c, ∫⁻ c', (φ c' : ℝ≥0∞)
      ∂((NonuniformMajority L K).transitionKernel c) ≤ r * (φ c : ℝ≥0∞) := by
    intro c
    haveI : IsProbabilityMeasure ((NonuniformMajority L K).transitionKernel c) :=
      (inferInstance : IsMarkovKernel
        (NonuniformMajority L K).transitionKernel).isProbabilityMeasure c
    by_cases hc_card : c.card = n; swap
    · rw [show (φ c : ℝ≥0∞) = 0 from by simp [hφ_zero_ne c hc_card], mul_zero]
      apply le_of_eq; apply lintegral_eq_zero_of_ae_eq_zero
      change ∀ᵐ c' ∂((NonuniformMajority L K).stepDistOrSelf c).toMeasure, _
      rw [MeasureTheory.ae_iff,
        PMF.toMeasure_apply_eq_zero_iff _
          (DiscreteMeasurableSpace.forall_measurableSet _)]
      exact Set.disjoint_left.mpr fun c' hc' hbad => by
        simp only [Set.mem_setOf_eq, not_not] at hbad
        exact hbad (show (φ c' : ℝ≥0∞) = 0 from by
          simp [hφ_zero_ne c'
            ((Protocol.stepDistOrSelf_support_card_eq _ c c' hc') ▸ hc_card)])
    by_cases hφ_ne : phase6HighTailPhi 2 c = 0
    · rw [show (φ c : ℝ≥0∞) = 0 from by simp [hφ_eq c hc_card, hφ_ne], mul_zero]
      apply le_of_eq; apply lintegral_eq_zero_of_ae_eq_zero
      filter_upwards [hnoninc c hc_card, h_card_ae c hc_card] with c' hle hc'_card
      show (φ c' : ℝ≥0∞) = 0
      have h0 : φ c' = 0 := by rw [hφ_eq c' hc'_card]; omega
      simp [h0]
    · have hae_ext : ∀ᵐ c' ∂((NonuniformMajority L K).transitionKernel c),
          φ c' ≤ φ c := by
        filter_upwards [hnoninc c hc_card, h_card_ae c hc_card] with c' hle hc'_card
        rw [hφ_eq c' hc'_card, hφ_eq c hc_card]; exact hle
      have h_desc_ext : (NonuniformMajority L K).transitionKernel c {c' | φ c' < φ c} ≥
          ENNReal.ofReal (2 / ((n : ℝ) * ((n : ℝ) - 1))) := by
        have h_sub : {c' | phase6HighTailPhi 2 c' < phase6HighTailPhi 2 c} ⊆
            {c' | φ c' < φ c} := by
          intro c' hc'; simp only [Set.mem_setOf_eq] at hc' ⊢
          by_cases hc'_card : c'.card = n
          · rw [hφ_eq c' hc'_card, hφ_eq c hc_card]; exact hc'
          · rw [hφ_zero_ne c' hc'_card, hφ_eq c hc_card]
            exact Nat.pos_of_ne_zero hφ_ne
        have h_prob := potentialProgressFrom_descent_prob (phase6HighTailPhi 2) c
          (hc_card ▸ hn8) (hprogress c hc_card hφ_ne)
        calc (NonuniformMajority L K).transitionKernel c {c' | φ c' < φ c}
            ≥ (NonuniformMajority L K).transitionKernel c
                {c' | phase6HighTailPhi 2 c' < phase6HighTailPhi 2 c} :=
              MeasureTheory.measure_mono h_sub
          _ ≥ ENNReal.ofReal (2 / (↑c.card * (↑c.card - 1))) := h_prob
          _ = ENNReal.ofReal (2 / ((n : ℝ) * ((n : ℝ) - 1))) := by rw [hc_card]
      have hv_le_n : (φ c : ℝ≥0∞) ≤ (n : ℝ≥0∞) := by exact_mod_cast hφ_le_n c
      have hn_ne_zero : (n : ℝ≥0∞) ≠ 0 := by
        simp only [ne_eq, Nat.cast_eq_zero]; omega
      have hn_ne_top : (n : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top n
      set q_nnr := (ENNReal.ofReal (2 / ((n : ℝ) * ((n : ℝ) - 1)))).toNNReal
      have hq_coe : (q_nnr : ℝ≥0∞) =
          ENNReal.ofReal (2 / ((n : ℝ) * ((n : ℝ) - 1))) :=
        ENNReal.coe_toNNReal ENNReal.ofReal_ne_top
      have h_int_le := lintegral_nat_le_of_descent
        ((NonuniformMajority L K).transitionKernel c) φ (φ c) hae_ext q_nnr
        (by rw [hq_coe]; exact h_desc_ext)
      have hmul_le :
          (q_nnr : ℝ≥0∞) / (n : ℝ≥0∞) * (φ c : ℝ≥0∞) ≤ (q_nnr : ℝ≥0∞) :=
        calc (q_nnr : ℝ≥0∞) / (n : ℝ≥0∞) * (φ c : ℝ≥0∞)
            ≤ (q_nnr : ℝ≥0∞) / (n : ℝ≥0∞) * (n : ℝ≥0∞) :=
              mul_le_mul_left' hv_le_n _
          _ = (q_nnr : ℝ≥0∞) :=
              ENNReal.div_mul_cancel hn_ne_zero hn_ne_top
      have hmul_sub :
          (1 - (q_nnr : ℝ≥0∞) / (n : ℝ≥0∞)) * (φ c : ℝ≥0∞) =
            (φ c : ℝ≥0∞) -
              ((q_nnr : ℝ≥0∞) / (n : ℝ≥0∞) * (φ c : ℝ≥0∞)) := by
        simpa [one_mul] using
          ENNReal.sub_mul (a := 1)
            (b := (q_nnr : ℝ≥0∞) / (n : ℝ≥0∞))
            (c := (φ c : ℝ≥0∞))
      calc ∫⁻ c', (φ c' : ℝ≥0∞) ∂((NonuniformMajority L K).transitionKernel c)
          ≤ (φ c : ℝ≥0∞) - (q_nnr : ℝ≥0∞) := h_int_le
        _ ≤ (φ c : ℝ≥0∞) -
              ((q_nnr : ℝ≥0∞) / (n : ℝ≥0∞) * (φ c : ℝ≥0∞)) :=
            tsub_le_tsub_left hmul_le _
        _ = (1 - (q_nnr : ℝ≥0∞) / (n : ℝ≥0∞)) * (φ c : ℝ≥0∞) :=
            hmul_sub.symm
        _ = r * (φ c : ℝ≥0∞) := by rw [hq_coe]
  have h_meas : Measurable (fun c => (φ c : ℝ≥0∞)) := Measurable.of_discrete
  have h_decay := PopProtoCommon.measure_potential_ge_one
    (NonuniformMajority L K).transitionKernel
    (fun c => (φ c : ℝ≥0∞)) h_meas r h_drift t c₀
  have h_card_zero : ((NonuniformMajority L K).transitionKernel ^ t) c₀
      {c' | c'.card ≠ n} = 0 := by
    apply Protocol.transitionKernel_pow_eq_zero_of_forall_not_reachable
    intro c' hc' hreach
    exact hc' (Protocol.reachable_card_eq hreach)
  have h_subset : {c : Config (AgentState L K) |
      ¬(∀ a ∈ c, 7 ≤ a.phase.val → a.role = .main → a.bias ≠ .zero →
        match a.bias with | .dyadic _ i => i.val ≤ 2 | .zero => True)} ⊆
      {c | 1 ≤ (φ c : ℝ≥0∞)} ∪ {c | c.card ≠ n} := by
    intro c hc
    by_cases hc_card : c.card = n; swap
    · right; exact hc_card
    · left; simp only [Set.mem_setOf_eq]; rw [hφ_eq c hc_card]
      have hne : phase6HighTailPhi 2 c ≠ 0 := by
        intro h0; apply hc; intro a ha _ hrole hbias
        have : phase6HighTailAgent 2 a = 0 :=
          Multiset.sum_eq_zero_iff.mp h0 _ (Multiset.mem_map_of_mem _ ha)
        unfold phase6HighTailAgent at this
        rw [show a.role = .main from hrole] at this
        simp only [↓reduceIte] at this
        match hb : a.bias with
        | .zero => exact absurd hb hbias
        | .dyadic _ i =>
          rw [hb] at this
          unfold phase6HighTailWeight at this
          simp only at this
          split_ifs at this with hi
          · exact absurd this (by positivity)
          · push_neg at hi; exact hi
      exact_mod_cast Nat.pos_of_ne_zero hne
  have hΦ_zero : φ c₀ = 0 := by
    show (if c₀.card = n then _ else _) = _
    simp only [show c₀.card = n from rfl, ↓reduceIte]
    apply Multiset.sum_eq_zero_iff.mpr
    intro x hx
    rw [Multiset.mem_map] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    simp only [phase6HighTailAgent]
    by_cases hrole : a.role = .main; swap
    · simp [hrole]
    · simp only [hrole, ↓reduceIte]
      match hb : a.bias with
      | .zero => rfl
      | .dyadic _ i =>
        have hle : i.val ≤ 2 := by
          have := hpost a ha hrole (by simp [hb])
          simp only [hb] at this; exact this
        simp only [phase6HighTailWeight, show ¬(2 < i.val) from by omega, ↓reduceIte]
  calc ((NonuniformMajority L K).transitionKernel ^ t) c₀
          {c | ¬(∀ a ∈ c, 7 ≤ a.phase.val → a.role = .main → a.bias ≠ .zero →
            match a.bias with | .dyadic _ i => i.val ≤ 2 | .zero => True)}
      ≤ ((NonuniformMajority L K).transitionKernel ^ t) c₀
          ({c | 1 ≤ (φ c : ℝ≥0∞)} ∪ {c | c.card ≠ n}) :=
        MeasureTheory.measure_mono h_subset
    _ ≤ ((NonuniformMajority L K).transitionKernel ^ t) c₀
          {c | 1 ≤ (φ c : ℝ≥0∞)} +
        ((NonuniformMajority L K).transitionKernel ^ t) c₀
          {c | c.card ≠ n} := MeasureTheory.measure_union_le _ _
    _ = ((NonuniformMajority L K).transitionKernel ^ t) c₀
          {c | 1 ≤ (φ c : ℝ≥0∞)} := by rw [h_card_zero, add_zero]
    _ ≤ r ^ t * (φ c₀ : ℝ≥0∞) := h_decay
    _ = 0 := by rw [hΦ_zero]; simp
    _ ≤ ENNReal.ofReal (1 / ((n : ℝ) ^ 2)) := zero_le'

/-- **Doty et al. Lemma 7.5**: at end of Phase 7, all minority agents have
exponent `< −(l+2)`, with high probability `1 − O(1/n²)`.

The event is defined on a protocol execution `(Ω, μ)`. The proof
(using Lemma 7.2 + the extended cancel/split analysis of Phase 7)
is deferred. -/
theorem lemma_7_5_phase_seven_minority
    (c₀ : Config (AgentState L K))
    (hn : 8 ≤ c₀.card)
    (hphase : ∀ a ∈ c₀, 8 ≤ a.phase.val)
    (hpost : ∀ a ∈ c₀, a.role = .main → a.bias ≠ .zero →
      match a.bias with | .dyadic .pos _ => True | _ => False)
    (hnonmain : ∀ a ∈ c₀, a.role ≠ .main → a.bias = .zero)
    (t : ℕ) :
    ((NonuniformMajority L K).transitionKernel ^ t) c₀
        {c : Config (AgentState L K) |
          ¬(∀ a ∈ c, 8 ≤ a.phase.val → a.role = .main → a.bias ≠ .zero →
            match a.bias with | .dyadic .pos _ => True | _ => False)} ≤
      ENNReal.ofReal (1 / ((c₀.card : ℝ) ^ 2)) := by
  set Q := fun c : Config (AgentState L K) =>
    (∀ a ∈ c, 8 ≤ a.phase.val) ∧ (∀ a ∈ c, ∀ i, a.bias ≠ .dyadic .neg i)
  suffices h : ((NonuniformMajority L K).transitionKernel ^ t) c₀ {c | ¬Q c} = 0 by
    have hmono : {c : Config (AgentState L K) |
        ¬(∀ a ∈ c, 8 ≤ a.phase.val → a.role = .main → a.bias ≠ .zero →
          match a.bias with | .dyadic .pos _ => True | _ => False)} ⊆ {c | ¬Q c} := by
      intro c hc ⟨hph, hbias⟩
      exact hc (fun a ha _ _ hnz => by
        have hnn := hbias a ha
        rcases hb : a.bias with _ | ⟨(_ | _), _⟩
        · exact absurd hb hnz
        · trivial
        · exact absurd hb (hnn _))
    exact le_trans (MeasureTheory.measure_mono hmono) (h ▸ zero_le')
  exact absorbing_implies_zero Q (fun c c' ⟨hcph, hcbias⟩ hsupp => by
    constructor
    · intro a' ha'
      unfold Protocol.stepDistOrSelf at hsupp
      split_ifs at hsupp with h_size
      · obtain ⟨⟨r₁, r₂⟩, heq⟩ := Protocol.stepDist_support _ _ h_size _ hsupp
        subst heq
        unfold Protocol.scheduledStep Protocol.stepOrSelf at ha'
        split_ifs at ha' with h_app
        · rw [Multiset.mem_add] at ha'
          rcases ha' with h_rem | h_new
          · exact hcph a' (Multiset.mem_of_le (Multiset.sub_le_self _ _) h_rem)
          · simp only [Multiset.insert_eq_cons, Multiset.mem_cons,
                Multiset.mem_singleton] at h_new
            rcases h_new with rfl | rfl
            · exact le_trans (hcph r₁ (Multiset.mem_of_le h_app (by simp)))
                (Transition_phase_monotone (L := L) (K := K) r₁ r₂).1
            · exact le_trans (hcph r₂ (Multiset.mem_of_le h_app (by simp)))
                (Transition_phase_monotone (L := L) (K := K) r₁ r₂).2
        · exact hcph a' ha'
      · rw [PMF.mem_support_pure_iff] at hsupp; subst hsupp; exact hcph a' ha'
    · intro a' ha' i
      unfold Protocol.stepDistOrSelf at hsupp
      split_ifs at hsupp with h_size
      · obtain ⟨⟨r₁, r₂⟩, heq⟩ := Protocol.stepDist_support _ _ h_size _ hsupp
        subst heq
        unfold Protocol.scheduledStep Protocol.stepOrSelf at ha'
        split_ifs at ha' with h_app
        · rw [Multiset.mem_add] at ha'
          rcases ha' with h_rem | h_new
          · exact hcbias a' (Multiset.mem_of_le (Multiset.sub_le_self _ _) h_rem) i
          · simp only [Multiset.insert_eq_cons, Multiset.mem_cons,
                Multiset.mem_singleton] at h_new
            rcases h_new with rfl | rfl
            · have hpres := Transition_preserves_no_neg_bias_of_phase_ge_eight
                (L := L) (K := K) r₁ r₂
                (hcph r₁ (Multiset.mem_of_le h_app (by simp)))
                (hcph r₂ (Multiset.mem_of_le h_app (by simp)))
                (hcbias r₁ (Multiset.mem_of_le h_app (by simp)))
                (hcbias r₂ (Multiset.mem_of_le h_app (by simp)))
              simp only [NonuniformMajority] at ⊢
              exact hpres.1 i
            · have hpres := Transition_preserves_no_neg_bias_of_phase_ge_eight
                (L := L) (K := K) r₁ r₂
                (hcph r₁ (Multiset.mem_of_le h_app (by simp)))
                (hcph r₂ (Multiset.mem_of_le h_app (by simp)))
                (hcbias r₁ (Multiset.mem_of_le h_app (by simp)))
                (hcbias r₂ (Multiset.mem_of_le h_app (by simp)))
              simp only [NonuniformMajority] at ⊢
              exact hpres.2 i
        · exact hcbias a' ha' i
      · rw [PMF.mem_support_pure_iff] at hsupp; subst hsupp; exact hcbias a' ha' i)
    c₀ ⟨hphase, fun a ha i heq => by
      by_cases hrole : a.role = .main
      · by_cases hzero : a.bias = .zero
        · simp [hzero] at heq
        · have hm := hpost a ha hrole hzero; rw [heq] at hm; exact hm
      · simp [hnonmain a ha hrole] at heq⟩ t

/-- **Doty et al. Lemma 7.6**: at end of Phase 8, there are no more minority
agents, with high probability `1 − O(1/n²)`.

The event is defined on a protocol execution `(Ω, μ)`. The proof
(using Lemma 7.5 + the consumption analysis of Phase 8) is deferred. -/
theorem lemma_7_6_phase_eight_eliminates
    (c₀ : Config (AgentState L K))
    (hn : 8 ≤ c₀.card)
    (hphase : ∀ a ∈ c₀, 9 ≤ a.phase.val)
    (hpost : ∀ a ∈ c₀, a.role = .main → a.bias = .zero)
    (t : ℕ) :
    ((NonuniformMajority L K).transitionKernel ^ t) c₀
        {c : Config (AgentState L K) |
          ¬(∀ a ∈ c, 9 ≤ a.phase.val → a.role = .main → a.bias = .zero)} ≤
      ENNReal.ofReal (1 / ((c₀.card : ℝ) ^ 2)) := by
  set Q := fun c : Config (AgentState L K) =>
    (∀ a ∈ c, 9 ≤ a.phase.val) ∧ (∀ a ∈ c, a.role = .main → a.bias = .zero)
  suffices h : ((NonuniformMajority L K).transitionKernel ^ t) c₀ {c | ¬Q c} = 0 by
    have hmono : {c : Config (AgentState L K) |
        ¬(∀ a ∈ c, 9 ≤ a.phase.val → a.role = .main → a.bias = .zero)} ⊆ {c | ¬Q c} := by
      intro c hc ⟨hph, hbias⟩
      exact hc (fun a ha hpv => hbias a ha)
    exact le_trans (MeasureTheory.measure_mono hmono) (h ▸ zero_le')
  exact absorbing_implies_zero Q (fun c c' ⟨hcph, hcbias⟩ hsupp => by
    constructor
    · intro a' ha'
      unfold Protocol.stepDistOrSelf at hsupp
      split_ifs at hsupp with h_size
      · obtain ⟨⟨r₁, r₂⟩, heq⟩ := Protocol.stepDist_support _ _ h_size _ hsupp
        subst heq
        unfold Protocol.scheduledStep Protocol.stepOrSelf at ha'
        split_ifs at ha' with h_app
        · rw [Multiset.mem_add] at ha'
          rcases ha' with h_rem | h_new
          · exact hcph a' (Multiset.mem_of_le (Multiset.sub_le_self _ _) h_rem)
          · simp only [Multiset.insert_eq_cons, Multiset.mem_cons,
                Multiset.mem_singleton] at h_new
            rcases h_new with rfl | rfl
            · exact le_trans (hcph r₁ (Multiset.mem_of_le h_app (by simp)))
                (Transition_phase_monotone (L := L) (K := K) r₁ r₂).1
            · exact le_trans (hcph r₂ (Multiset.mem_of_le h_app (by simp)))
                (Transition_phase_monotone (L := L) (K := K) r₁ r₂).2
        · exact hcph a' ha'
      · rw [PMF.mem_support_pure_iff] at hsupp; subst hsupp; exact hcph a' ha'
    · intro a' ha' hrole
      unfold Protocol.stepDistOrSelf at hsupp
      split_ifs at hsupp with h_size
      · obtain ⟨⟨r₁, r₂⟩, heq⟩ := Protocol.stepDist_support _ _ h_size _ hsupp
        subst heq
        unfold Protocol.scheduledStep Protocol.stepOrSelf at ha'
        split_ifs at ha' with h_app
        · rw [Multiset.mem_add] at ha'
          rcases ha' with h_rem | h_new
          · exact hcbias a' (Multiset.mem_of_le (Multiset.sub_le_self _ _) h_rem) hrole
          · simp only [Multiset.insert_eq_cons, Multiset.mem_cons,
                Multiset.mem_singleton] at h_new
            rcases h_new with rfl | rfl
            · have hpres := Transition_role_bias_preserved_of_phase_ge_nine
                (L := L) (K := K) r₁ r₂
                (hcph r₁ (Multiset.mem_of_le h_app (by simp)))
                (hcph r₂ (Multiset.mem_of_le h_app (by simp)))
              simp only [NonuniformMajority] at hrole ⊢
              rw [hpres.2.1]
              exact hcbias r₁ (Multiset.mem_of_le h_app (by simp))
                (hpres.1 ▸ hrole)
            · have hpres := Transition_role_bias_preserved_of_phase_ge_nine
                (L := L) (K := K) r₁ r₂
                (hcph r₁ (Multiset.mem_of_le h_app (by simp)))
                (hcph r₂ (Multiset.mem_of_le h_app (by simp)))
              simp only [NonuniformMajority] at hrole ⊢
              rw [hpres.2.2.2]
              exact hcbias r₂ (Multiset.mem_of_le h_app (by simp))
                (hpres.2.2.1 ▸ hrole)
        · exact hcbias a' ha' hrole
      · rw [PMF.mem_support_pure_iff] at hsupp; subst hsupp; exact hcbias a' ha' hrole)
    c₀ ⟨hphase, hpost⟩ t

section Phase10Epidemic

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

/-! ### Phase-10 epidemic convergence infrastructure

The Phase-10 epidemic spreading uses `phaseBelowCount 10` as potential,
following exactly the Phase3Convergence pattern. Once at least one agent
reaches phase 10, the phase-epidemic mechanism ensures that any agent
interacting with a phase-10 agent gets promoted to phase 10 (since
max(k, 10) = 10 and 10 is the maximum phase). -/

/-- Source predicate for Phase-10 epidemic: at least one agent has phase 10. -/
def hasSource10 (c : Config (AgentState L K)) : Prop :=
  ∃ a ∈ c, a.phase.val = 10

/-- Post condition for Phase-10 epidemic: all agents have phase 10. -/
def Phase10EpidemicPost (c : Config (AgentState L K)) : Prop :=
  ∀ a ∈ c, a.phase.val = 10

/-- `Phase10EpidemicPost c` holds iff `phaseBelowCount 10 c = 0`. -/
lemma Phase10EpidemicPost_iff_phaseBelowCount_zero (c : Config (AgentState L K)) :
    Phase10EpidemicPost c ↔ phaseBelowCount 10 c = 0 := by
  unfold Phase10EpidemicPost phaseBelowCount
  constructor
  · intro h
    rw [Multiset.card_eq_zero, Multiset.filter_eq_nil]
    intro a ha
    simp only [decide_eq_true_eq, not_lt]
    have := h a ha
    have hle : a.phase.val < 11 := a.phase.isLt
    omega
  · intro h a ha
    rw [Multiset.card_eq_zero, Multiset.filter_eq_nil] at h
    have := h a ha
    simp only [decide_eq_true_eq, not_lt] at this
    have hle : a.phase.val < 11 := a.phase.isLt
    omega

/-- hasSource10 implies hasSource (phase ≥ 4). -/
lemma hasSource10_implies_hasSource (c : Config (AgentState L K))
    (h : hasSource10 c) : hasSource c := by
  obtain ⟨a, ha_mem, ha_phase⟩ := h
  exact ⟨a, ha_mem, by omega⟩

lemma Transition_left_phase_eq_10 (s t : AgentState L K)
    (hs : s.phase.val = 10) :
    (Transition L K s t).1.phase.val = 10 := by
  have hge : 10 ≤ (Transition L K s t).1.phase.val :=
    le_trans (by simp [hs]) (Transition_left_phase_ge_pair_max (L := L) (K := K) s t)
  have hlt : (Transition L K s t).1.phase.val < 11 := (Transition L K s t).1.phase.isLt
  omega

lemma Transition_right_phase_eq_10 (s t : AgentState L K)
    (ht : t.phase.val = 10) :
    (Transition L K s t).2.phase.val = 10 := by
  have hge : 10 ≤ (Transition L K s t).2.phase.val :=
    le_trans (by simp [ht]) (Transition_right_phase_ge_pair_max (L := L) (K := K) s t)
  have hlt : (Transition L K s t).2.phase.val < 11 := (Transition L K s t).2.phase.isLt
  omega

/-- Source-10 is preserved by the one-step stochastic support: phase monotonicity
ensures that once an agent reaches phase 10, it stays there. -/
lemma hasSource10_preserved_by_stepDistOrSelf
    (c c' : Config (AgentState L K))
    (hc : hasSource10 c) :
    c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support → hasSource10 c' := by
  intro hsupp
  obtain ⟨a, ha_mem, ha_phase⟩ := hc
  unfold Protocol.stepDistOrSelf at hsupp
  split_ifs at hsupp with h_size
  · obtain ⟨⟨r₁, r₂⟩, heq⟩ := Protocol.stepDist_support _ _ h_size _ hsupp
    subst heq
    show hasSource10 (Protocol.scheduledStep (NonuniformMajority L K) c (r₁, r₂))
    unfold Protocol.scheduledStep Protocol.stepOrSelf
    split_ifs with h_app
    · change ∃ a' ∈ c - {r₁, r₂} + {(Transition L K r₁ r₂).1,
        (Transition L K r₁ r₂).2}, a'.phase.val = 10
      by_cases ha_r1 : a = r₁
      · subst ha_r1
        refine ⟨(Transition L K a r₂).1, ?_, ?_⟩
        · exact Multiset.mem_add.mpr (Or.inr (Multiset.mem_cons_self _ _))
        · exact Transition_left_phase_eq_10 a r₂ ha_phase
      · by_cases ha_r2 : a = r₂
        · subst ha_r2
          refine ⟨(Transition L K r₁ a).2, ?_, ?_⟩
          · exact Multiset.mem_add.mpr (Or.inr (by
              simp only [Multiset.insert_eq_cons]
              exact Multiset.mem_cons.mpr (Or.inr (Multiset.mem_singleton.mpr rfl))))
          · exact Transition_right_phase_eq_10 r₁ a ha_phase
        · have ha_rem : a ∈ c - {r₁, r₂} := by
            rw [Multiset.mem_sub]
            simp only [Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton]
            simp [ha_r1, ha_r2]
            exact Multiset.count_pos.mpr ha_mem
          exact ⟨a, Multiset.mem_add.mpr (Or.inl ha_rem), ha_phase⟩
    · exact ⟨a, ha_mem, ha_phase⟩
  · rw [PMF.mem_support_pure_iff] at hsupp
    subst hsupp
    exact ⟨a, ha_mem, ha_phase⟩

/-- Source-10 is maintained along any finite Markov-chain execution. -/
lemma hasSource10_transitionKernel_pow_zero
    (c₀ : Config (AgentState L K)) (hc₀ : hasSource10 c₀) (t : ℕ) :
    ((NonuniformMajority L K).transitionKernel ^ t) c₀
        {c' | ¬hasSource10 c'} = 0 :=
  Protocol.transitionKernel_pow_not_pred_eq_zero_of_stepDistOrSelf_support_preserved
    (NonuniformMajority L K) hasSource10
    (fun c c' hc hsupp => hasSource10_preserved_by_stepDistOrSelf c c' hc hsupp)
    c₀ hc₀ t

/-- Phase-10 epidemic descent: when a phase-<10 agent meets a phase-10 agent,
both outputs get phase 10 (from the epidemic mechanism). -/
private lemma Transition_phaseBelowCount10_pair_lt
    (r₁ r₂ : AgentState L K)
    (hr₁ : r₁.phase.val < 10) (hr₂ : r₂.phase.val = 10) :
    phaseBelowCount 10
      ({(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2} : Config (AgentState L K)) <
    phaseBelowCount 10 ({r₁, r₂} : Config (AgentState L K)) := by
  have hmax : 10 ≤ max r₁.phase.val r₂.phase.val := by
    rw [hr₂]; exact le_max_right _ _
  have hout1 : 10 ≤ (Transition L K r₁ r₂).1.phase.val :=
    le_trans hmax (Transition_left_phase_ge_pair_max (L := L) (K := K) r₁ r₂)
  have hout2 : 10 ≤ (Transition L K r₁ r₂).2.phase.val :=
    le_trans hmax (Transition_right_phase_ge_pair_max (L := L) (K := K) r₁ r₂)
  have hout1_eq : (Transition L K r₁ r₂).1.phase.val = 10 := by
    have hupper : (Transition L K r₁ r₂).1.phase.val < 11 := by
      exact (Transition L K r₁ r₂).1.phase.isLt
    omega
  have hout2_eq : (Transition L K r₁ r₂).2.phase.val = 10 := by
    have hupper : (Transition L K r₁ r₂).2.phase.val < 11 := by
      exact (Transition L K r₁ r₂).2.phase.isLt
    omega
  show phaseBelowCount 10 ({(Transition L K r₁ r₂).1} + {(Transition L K r₁ r₂).2}) <
    phaseBelowCount 10 ({r₁} + {r₂})
  rw [phaseBelowCount_add, phaseBelowCount_add]
  simp only [phaseBelowCount, Multiset.filter_singleton, decide_eq_true_eq]
  have h1 : ¬ (Transition L K r₁ r₂).1.phase.val < 10 := not_lt.mpr (le_of_eq hout1_eq.symm)
  have h2 : ¬ (Transition L K r₁ r₂).2.phase.val < 10 := not_lt.mpr (le_of_eq hout2_eq.symm)
  have h3 : ¬ r₂.phase.val < 10 := not_lt.mpr (le_of_eq hr₂.symm)
  simp [h1, h2, hr₁, h3]

/-- Config-level phaseBelowCount 10 strictly decreases when a "mixed" pair interacts. -/
private lemma phaseBelowCount10_config_decrease
    (c : Config (AgentState L K)) (r₁ r₂ : AgentState L K)
    (h_sub : {r₁, r₂} ≤ c)
    (h : (r₁.phase.val < 10 ∧ r₂.phase.val = 10) ∨
         (r₁.phase.val = 10 ∧ r₂.phase.val < 10)) :
    phaseBelowCount 10
      (c - {r₁, r₂} + {(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2}) <
    phaseBelowCount 10 c := by
  have h_restore : c - {r₁, r₂} + {r₁, r₂} = c := Multiset.sub_add_cancel h_sub
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have h_pair_lt := Transition_phaseBelowCount10_pair_lt r₁ r₂ h1 h2
    calc phaseBelowCount 10
          (c - {r₁, r₂} + {(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2})
        = phaseBelowCount 10 (c - {r₁, r₂}) + phaseBelowCount 10
            {(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2} := phaseBelowCount_add _ _ _
      _ < phaseBelowCount 10 (c - {r₁, r₂}) + phaseBelowCount 10 {r₁, r₂} :=
          Nat.add_lt_add_left h_pair_lt _
      _ = phaseBelowCount 10 (c - {r₁, r₂} + {r₁, r₂}) := (phaseBelowCount_add _ _ _).symm
      _ = phaseBelowCount 10 c := by rw [h_restore]
  · -- Symmetric case: r₁ at phase 10, r₂ below
    have hmax : 10 ≤ max r₁.phase.val r₂.phase.val := by
      rw [h1]; exact le_max_left _ _
    have hout1 : (Transition L K r₁ r₂).1.phase.val = 10 := by
      have hle := le_trans hmax (Transition_left_phase_ge_pair_max (L := L) (K := K) r₁ r₂)
      have hupper : (Transition L K r₁ r₂).1.phase.val < 11 := by
        exact (Transition L K r₁ r₂).1.phase.isLt
      omega
    have hout2 : (Transition L K r₁ r₂).2.phase.val = 10 := by
      have hle := le_trans hmax (Transition_right_phase_ge_pair_max (L := L) (K := K) r₁ r₂)
      have hupper : (Transition L K r₁ r₂).2.phase.val < 11 := by
        exact (Transition L K r₁ r₂).2.phase.isLt
      omega
    show phaseBelowCount 10
        (c - {r₁, r₂} + {(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2}) <
      phaseBelowCount 10 c
    calc phaseBelowCount 10
          (c - {r₁, r₂} + {(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2})
        = phaseBelowCount 10 (c - {r₁, r₂}) + phaseBelowCount 10
            {(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2} := phaseBelowCount_add _ _ _
      _ ≤ phaseBelowCount 10 (c - {r₁, r₂}) + 0 := by
          apply Nat.add_le_add_left
          show phaseBelowCount 10 ({(Transition L K r₁ r₂).1} +
            {(Transition L K r₁ r₂).2}) ≤ 0
          rw [phaseBelowCount_add]
          simp only [phaseBelowCount, Multiset.filter_singleton, decide_eq_true_eq]
          have h1' : ¬ (Transition L K r₁ r₂).1.phase.val < 10 := by omega
          have h2' : ¬ (Transition L K r₁ r₂).2.phase.val < 10 := by omega
          simp [h1', h2']
      _ = phaseBelowCount 10 (c - {r₁, r₂}) := by omega
      _ < phaseBelowCount 10 (c - {r₁, r₂}) + phaseBelowCount 10 {r₁, r₂} := by
          have : 0 < phaseBelowCount 10 ({r₁, r₂} : Config (AgentState L K)) := by
            show 0 < phaseBelowCount 10 ({r₁} + {r₂})
            rw [phaseBelowCount_add]
            simp only [phaseBelowCount, Multiset.filter_singleton, decide_eq_true_eq]
            have : ¬ r₁.phase.val < 10 := by omega
            simp [this, h2]
          omega
      _ = phaseBelowCount 10 (c - {r₁, r₂} + {r₁, r₂}) := (phaseBelowCount_add _ _ _).symm
      _ = phaseBelowCount 10 c := by rw [h_restore]

/-- The scheduled step for an applicable "mixed" pair maps into the descent target
for the Phase-10 epidemic. -/
private lemma scheduledStep_mixed_in_target10
    (c : Config (AgentState L K))
    (r₁ r₂ : AgentState L K)
    (hr₁ : r₁ ∈ c) (hr₂ : r₂ ∈ c) (hne : r₁ ≠ r₂)
    (h : (r₁.phase.val < 10 ∧ r₂.phase.val = 10) ∨
         (r₁.phase.val = 10 ∧ r₂.phase.val < 10)) :
    (NonuniformMajority L K).scheduledStep c (r₁, r₂) ∈
      {c' | phaseBelowCount 10 c' < phaseBelowCount 10 c} := by
  have happ : Protocol.Applicable c r₁ r₂ := applicable_of_mem_ne3 hr₁ hr₂ hne
  simp only [Set.mem_setOf_eq, Protocol.scheduledStep]
  have hstep : Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂ =
    c - {r₁, r₂} + {(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2} := by
    unfold Protocol.stepOrSelf NonuniformMajority
    simp only [if_pos happ]
  rw [hstep]
  exact phaseBelowCount10_config_decrease c r₁ r₂ happ h

/-- Phase-10 descent probability: when ¬Phase10EpidemicPost and source exists,
the transition kernel maps into {pbc 10 decreased} with probability ≥ 2/(n(n-1)). -/
lemma phase10_descent_prob (c : Config (AgentState L K))
    (hn : 8 ≤ c.card)
    (hnotpost : ¬Phase10EpidemicPost c)
    (h_source : hasSource10 c) :
    (NonuniformMajority L K).transitionKernel c
      {c' | phaseBelowCount 10 c' < phaseBelowCount 10 c} ≥
    ENNReal.ofReal (2 / ((c.card : ℝ) * ((c.card : ℝ) - 1))) := by
  -- Extract witnesses
  have hnotpost' : ∃ a ∈ c, a.phase.val < 10 := by
    rw [Phase10EpidemicPost] at hnotpost
    push_neg at hnotpost
    obtain ⟨a, ha_mem, ha_phase⟩ := hnotpost
    have hle : a.phase.val < 11 := a.phase.isLt
    exact ⟨a, ha_mem, by omega⟩
  obtain ⟨a, ha_mem, ha_phase⟩ := hnotpost'
  obtain ⟨b, hb_mem, hb_phase⟩ := h_source
  have hab : a ≠ b := by intro heq; subst heq; omega
  have hc : 2 ≤ c.card := by omega
  set good : Set (AgentState L K × AgentState L K) :=
    {(a, b), (b, a)} with good_def
  have h_target := stepDistOrSelf_toMeasure_ge c hc
    {c' | phaseBelowCount 10 c' < phaseBelowCount 10 c}
    good
    (by
      intro pair hpair
      simp only [good_def, Set.mem_insert_iff, Set.mem_singleton_iff] at hpair
      rcases hpair with rfl | rfl
      · exact scheduledStep_mixed_in_target10 c a b ha_mem hb_mem hab
          (Or.inl ⟨ha_phase, hb_phase⟩)
      · exact scheduledStep_mixed_in_target10 c b a hb_mem ha_mem hab.symm
          (Or.inr ⟨hb_phase, ha_phase⟩))
  change ((NonuniformMajority L K).stepDistOrSelf c).toMeasure _ ≥ _
  calc ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
          {c' | phaseBelowCount 10 c' < phaseBelowCount 10 c}
      ≥ (c.interactionPMF hc).toMeasure good := h_target
    _ ≥ (c.interactionPMF hc) (a, b) + (c.interactionPMF hc) (b, a) := by
        have hab_ne : (a, b) ≠ (b, a) := by
          intro h; exact hab (Prod.mk.inj h).1
        have hpair : ({(a, b), (b, a)} : Set _) = {(a, b)} ∪ {(b, a)} := by
          ext x; simp [Set.mem_insert_iff, Set.mem_singleton_iff, or_comm]
        have h_disj : Disjoint ({(a, b)} : Set _) {(b, a)} :=
          Set.disjoint_singleton.mpr hab_ne
        rw [good_def, hpair, measure_union h_disj
          (DiscreteMeasurableSpace.forall_measurableSet _),
          PMF.toMeasure_apply_singleton _ _ (DiscreteMeasurableSpace.forall_measurableSet _),
          PMF.toMeasure_apply_singleton _ _ (DiscreteMeasurableSpace.forall_measurableSet _)]
    _ ≥ ENNReal.ofReal (2 / ((c.card : ℝ) * ((c.card : ℝ) - 1))) := by
        have hpmf_ab : (c.interactionPMF hc) (a, b) = c.interactionProb a b := rfl
        have hpmf_ba : (c.interactionPMF hc) (b, a) = c.interactionProb b a := rfl
        rw [hpmf_ab, hpmf_ba]
        simp only [Config.interactionProb, Config.interactionCount, hab, hab.symm, ite_false]
        have ha_count : 0 < c.count a := Multiset.count_pos.mpr ha_mem
        have hb_count : 0 < c.count b := Multiset.count_pos.mpr hb_mem
        have h_ab : 1 ≤ c.count a * c.count b :=
          Nat.one_le_iff_ne_zero.mpr (by positivity)
        have h_ba : 1 ≤ c.count b * c.count a :=
          Nat.one_le_iff_ne_zero.mpr (by positivity)
        have h1 : (↑(c.count a * c.count b) : ENNReal) /
            (c.totalPairs : ENNReal) ≥ 1 / (c.totalPairs : ENNReal) := by
          apply ENNReal.div_le_div_right
          exact_mod_cast h_ab
        have h2 : (↑(c.count b * c.count a) : ENNReal) /
            (c.totalPairs : ENNReal) ≥ 1 / (c.totalPairs : ENNReal) := by
          apply ENNReal.div_le_div_right
          exact_mod_cast h_ba
        calc (↑(c.count a * c.count b) : ENNReal) /
                (c.totalPairs : ENNReal) +
              (↑(c.count b * c.count a) : ENNReal) /
                (c.totalPairs : ENNReal)
            ≥ 1 / (c.totalPairs : ENNReal) + 1 / (c.totalPairs : ENNReal) :=
              add_le_add h1 h2
          _ = 2 / (c.totalPairs : ENNReal) := by
              rw [show (1 : ENNReal) / c.totalPairs + 1 / c.totalPairs =
                (1 + 1) / c.totalPairs from by
                rw [ENNReal.add_div]
              ]
              norm_num
          _ = ENNReal.ofReal (2 / ((c.card : ℝ) * ((c.card : ℝ) - 1))) := by
              have hcard_pos : (0 : ℝ) < c.card :=
                Nat.cast_pos.mpr (by omega)
              have hcard_sub_pos : (0 : ℝ) < (c.card : ℝ) - 1 := by
                have h8 : (8 : ℝ) ≤ c.card := by exact_mod_cast hn
                linarith
              have hprod_pos : (0 : ℝ) < (c.card : ℝ) * ((c.card : ℝ) - 1) :=
                mul_pos hcard_pos hcard_sub_pos
              rw [ENNReal.ofReal_div_of_pos hprod_pos]
              congr 1
              · exact (ENNReal.ofReal_ofNat 2).symm
              · unfold Config.totalPairs
                have h1le : 1 ≤ c.card := by omega
                rw [show (c.card : ℝ) * ((c.card : ℝ) - 1) =
                    ((c.card * (c.card - 1) : ℕ) : ℝ) from by
                  push_cast [Nat.cast_sub h1le]; ring]
                exact (ENNReal.ofReal_natCast _).symm

/-- Extended potential for Phase-10 epidemic: phaseBelowCount 10 when card = n and
source-10 exists, ⊤ when card = n and no source-10, 0 when card ≠ n. -/
noncomputable def phase10PotentialExt (n : ℕ) (c : Config (AgentState L K)) : ℝ≥0∞ :=
  if c.card ≠ n then 0
  else if hasSource10 c then (phaseBelowCount 10 c : ℝ≥0∞)
  else ⊤

lemma phase10PotentialExt_drift (n : ℕ) (hn : 8 ≤ n) (c : Config (AgentState L K)) :
    ∫⁻ c', phase10PotentialExt n c' ∂((NonuniformMajority L K).transitionKernel c) ≤
      (1 - ENNReal.ofReal (2 / ((n : ℝ) * ((n : ℝ) - 1))) / (n : ℝ≥0∞)) *
        phase10PotentialExt n c := by
  haveI : IsProbabilityMeasure ((NonuniformMajority L K).transitionKernel c) :=
    (inferInstance : IsMarkovKernel (NonuniformMajority L K).transitionKernel).isProbabilityMeasure c
  set r := 1 - ENNReal.ofReal (2 / ((n : ℝ) * ((n : ℝ) - 1))) / (n : ℝ≥0∞)
  -- Case 1: card ≠ n → Φ = 0
  by_cases hcard : c.card = n
  swap
  · have : phase10PotentialExt n c = 0 := by unfold phase10PotentialExt; simp [hcard]
    rw [this, mul_zero]
    apply le_of_eq
    apply lintegral_eq_zero_of_ae_eq_zero
    change ∀ᵐ c' ∂((NonuniformMajority L K).stepDistOrSelf c).toMeasure,
      phase10PotentialExt n c' = 0
    rw [MeasureTheory.ae_iff,
      PMF.toMeasure_apply_eq_zero_iff _
        (DiscreteMeasurableSpace.forall_measurableSet _)]
    exact Set.disjoint_left.mpr fun c' hc' hbad => by
      simp only [Set.mem_setOf_eq, not_not] at hbad
      have hc'_card := Protocol.stepDistOrSelf_support_card_eq _ c c' hc'
      have : c'.card ≠ n := hc'_card ▸ hcard
      exact hbad (show phase10PotentialExt n c' = 0 from by
        unfold phase10PotentialExt; simp [this])
  -- Case 2: card = n, no source-10 → Φ = ⊤
  by_cases h_source : hasSource10 c
  swap
  · have : phase10PotentialExt n c = ⊤ := by
      unfold phase10PotentialExt; simp [hcard, h_source]
    rw [this]
    set p_real := (2 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))
    set x_real := p_real / (n : ℝ)
    have h8 : (8 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hn_pos' : (0 : ℝ) < n := by linarith
    have hn_sub_pos' : (0 : ℝ) < (n : ℝ) - 1 := by linarith
    have hx_pos' : 0 < x_real := div_pos (div_pos two_pos (mul_pos hn_pos' hn_sub_pos')) hn_pos'
    have hx_lt_one : x_real < 1 := by
      show p_real / (n : ℝ) < 1
      show (2 / ((n : ℝ) * ((n : ℝ) - 1))) / (n : ℝ) < 1
      rw [div_div, div_lt_one (by positivity)]
      nlinarith [sq_nonneg ((n : ℝ) - 2)]
    have h_ofReal_div : ENNReal.ofReal p_real / (n : ℝ≥0∞) = ENNReal.ofReal x_real := by
      rw [show (n : ℝ≥0∞) = ENNReal.ofReal (n : ℝ) from
        (ENNReal.ofReal_natCast n).symm]
      exact (ENNReal.ofReal_div_of_pos hn_pos').symm
    have hr_eq : r = ENNReal.ofReal (1 - x_real) := by
      show 1 - ENNReal.ofReal (2 / ((n : ℝ) * ((n : ℝ) - 1))) / (n : ℝ≥0∞) =
        ENNReal.ofReal (1 - x_real)
      rw [h_ofReal_div, ENNReal.ofReal_sub _ hx_pos'.le, ENNReal.ofReal_one]
    have hr_pos_real : (0 : ℝ) < 1 - x_real := by linarith
    rw [hr_eq]
    have : ENNReal.ofReal (1 - x_real) ≠ 0 :=
      ne_of_gt (ENNReal.ofReal_pos.mpr hr_pos_real)
    rw [ENNReal.mul_top this]
    exact le_top
  -- Case 3: card = n, source-10 exists
  by_cases hpost : Phase10EpidemicPost c
  · -- Phase10EpidemicPost: Φ = pbc = 0
    have hpbc : phaseBelowCount 10 c = 0 :=
      (Phase10EpidemicPost_iff_phaseBelowCount_zero c).mp hpost
    have : phase10PotentialExt n c = 0 := by
      unfold phase10PotentialExt; simp [hcard, h_source, hpbc]
    rw [this, mul_zero]
    apply le_of_eq
    apply lintegral_eq_zero_of_ae_eq_zero
    have h_card_ae : ∀ᵐ c' ∂((NonuniformMajority L K).transitionKernel c),
        c'.card = n := by
      change ∀ᵐ c' ∂((NonuniformMajority L K).stepDistOrSelf c).toMeasure, _
      rw [MeasureTheory.ae_iff,
        PMF.toMeasure_apply_eq_zero_iff _
          (DiscreteMeasurableSpace.forall_measurableSet _)]
      exact Set.disjoint_left.mpr fun c' hc' hbad =>
        hbad (Protocol.stepDistOrSelf_support_card_eq _ c c' hc' ▸ hcard)
    have h_post_ae : ∀ᵐ c' ∂((NonuniformMajority L K).transitionKernel c),
        Phase10EpidemicPost c' := by
      change ∀ᵐ c' ∂((NonuniformMajority L K).stepDistOrSelf c).toMeasure, _
      rw [MeasureTheory.ae_iff,
        PMF.toMeasure_apply_eq_zero_iff _
          (DiscreteMeasurableSpace.forall_measurableSet _)]
      exact Set.disjoint_left.mpr fun c' hc' hbad => by
        simp only [Set.mem_setOf_eq] at hbad
        apply hbad; intro a' ha'
        unfold Protocol.stepDistOrSelf at hc'
        split_ifs at hc' with h_size
        · obtain ⟨⟨r₁, r₂⟩, heq⟩ := Protocol.stepDist_support _ _ h_size _ hc'
          subst heq
          unfold Protocol.scheduledStep Protocol.stepOrSelf at ha'
          split_ifs at ha' with h_app
          · rw [Multiset.mem_add] at ha'
            rcases ha' with h_rem | h_new
            · have := hpost a' (Multiset.mem_of_le (Multiset.sub_le_self _ _) h_rem)
              have hle : a'.phase.val < 11 := a'.phase.isLt
              omega
            · simp only [Multiset.insert_eq_cons, Multiset.mem_cons,
                Multiset.mem_singleton] at h_new
              rcases h_new with rfl | rfl
              · have hr₁_phase := hpost r₁ (Multiset.mem_of_le h_app (by simp))
                exact Transition_left_phase_eq_10 r₁ r₂ hr₁_phase
              · have hr₂_phase := hpost r₂ (Multiset.mem_of_le h_app (by simp))
                exact Transition_right_phase_eq_10 r₁ r₂ hr₂_phase
          · exact hpost a' ha'
        · simp at hc'; subst hc'; exact hpost a' ha'
    filter_upwards [h_card_ae, h_post_ae] with c' hc'_card hc'_post
    have hpbc' : phaseBelowCount 10 c' = 0 :=
      (Phase10EpidemicPost_iff_phaseBelowCount_zero c').mp hc'_post
    show phase10PotentialExt n c' = 0
    unfold phase10PotentialExt
    rw [if_neg (not_not.mpr hc'_card)]
    have hc'_source : hasSource10 c' := by
      have hc'pos : 0 < c'.card := by omega
      obtain ⟨a, ha_mem⟩ := Multiset.card_pos_iff_exists_mem.mp hc'pos
      exact ⟨a, ha_mem, hc'_post a ha_mem⟩
    rw [if_pos hc'_source, hpbc']
    simp
  · -- Main case: card = n, source-10, ¬Phase10EpidemicPost
    have hΦ_eq : phase10PotentialExt n c = (phaseBelowCount 10 c : ℝ≥0∞) := by
      unfold phase10PotentialExt; simp [hcard, h_source]
    have h_card_ae : ∀ᵐ c' ∂((NonuniformMajority L K).transitionKernel c),
        c'.card = n := by
      change ∀ᵐ c' ∂((NonuniformMajority L K).stepDistOrSelf c).toMeasure, _
      rw [MeasureTheory.ae_iff,
        PMF.toMeasure_apply_eq_zero_iff _
          (DiscreteMeasurableSpace.forall_measurableSet _)]
      exact Set.disjoint_left.mpr fun c' hc' hbad =>
        hbad (Protocol.stepDistOrSelf_support_card_eq _ c c' hc' ▸ hcard)
    have h_source_ae : ∀ᵐ c' ∂((NonuniformMajority L K).transitionKernel c),
        hasSource10 c' := by
      change ∀ᵐ c' ∂((NonuniformMajority L K).stepDistOrSelf c).toMeasure, _
      rw [MeasureTheory.ae_iff,
        PMF.toMeasure_apply_eq_zero_iff _
          (DiscreteMeasurableSpace.forall_measurableSet _)]
      exact Set.disjoint_left.mpr fun c' hc' hbad => by
        simp only [Set.mem_setOf_eq, not_not] at hbad
        exact hbad (hasSource10_preserved_by_stepDistOrSelf c c' h_source hc')
    have h_eq_ae : ∀ᵐ c' ∂((NonuniformMajority L K).transitionKernel c),
        phase10PotentialExt n c' = (phaseBelowCount 10 c' : ℝ≥0∞) := by
      filter_upwards [h_card_ae, h_source_ae] with c' hc'_card hc'_source
      unfold phase10PotentialExt; simp [hc'_card, hc'_source]
    have h_int_eq : ∫⁻ c', phase10PotentialExt n c'
        ∂((NonuniformMajority L K).transitionKernel c) =
        ∫⁻ c', (phaseBelowCount 10 c' : ℝ≥0∞)
        ∂((NonuniformMajority L K).transitionKernel c) := by
      exact lintegral_congr_ae h_eq_ae
    rw [h_int_eq, hΦ_eq]
    have h_pbc := phaseBelowCount_ae_noninc 10 c
    have h_noninc : ∀ᵐ c' ∂((NonuniformMajority L K).transitionKernel c),
        phaseBelowCount 10 c' ≤ phaseBelowCount 10 c := h_pbc
    have h_desc_pbc : (NonuniformMajority L K).transitionKernel c
        {c' | phaseBelowCount 10 c' < phaseBelowCount 10 c} ≥
        ENNReal.ofReal (2 / ((n : ℝ) * ((n : ℝ) - 1))) := by
      have := phase10_descent_prob c (hcard ▸ hn) hpost h_source
      rwa [hcard] at this
    set p_ennr := ENNReal.ofReal (2 / ((n : ℝ) * ((n : ℝ) - 1)))
    have h_bound : ∫⁻ c', (phaseBelowCount 10 c' : ℝ≥0∞)
        ∂((NonuniformMajority L K).transitionKernel c) ≤
        (phaseBelowCount 10 c : ℝ≥0∞) - p_ennr := by
      exact lintegral_nat_le_of_descent
        ((NonuniformMajority L K).transitionKernel c)
        (phaseBelowCount 10) (phaseBelowCount 10 c)
        h_noninc
        p_ennr.toNNReal
        (by rw [ENNReal.coe_toNNReal (ENNReal.ofReal_ne_top)]; exact h_desc_pbc)
    have hv_le_M : (phaseBelowCount 10 c : ℝ≥0∞) ≤ (n : ℝ≥0∞) := by
      exact_mod_cast (hcard ▸ phaseBelowCount_le_card 10 c)
    have hM_ne_zero : (n : ℝ≥0∞) ≠ 0 := by simp [show n ≠ 0 by omega]
    have hM_ne_top : (n : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top n
    have hmul_le : p_ennr / (n : ℝ≥0∞) * (phaseBelowCount 10 c : ℝ≥0∞) ≤ p_ennr := by
      calc p_ennr / (n : ℝ≥0∞) * (phaseBelowCount 10 c : ℝ≥0∞)
          ≤ p_ennr / (n : ℝ≥0∞) * (n : ℝ≥0∞) := mul_le_mul_left' hv_le_M _
        _ = p_ennr := ENNReal.div_mul_cancel hM_ne_zero hM_ne_top
    have hsub_le : (phaseBelowCount 10 c : ℝ≥0∞) - p_ennr ≤
        (phaseBelowCount 10 c : ℝ≥0∞) -
          (p_ennr / (n : ℝ≥0∞) * (phaseBelowCount 10 c : ℝ≥0∞)) :=
      tsub_le_tsub_left hmul_le _
    have hmul_sub : r * (phaseBelowCount 10 c : ℝ≥0∞) =
        (phaseBelowCount 10 c : ℝ≥0∞) -
          (p_ennr / (n : ℝ≥0∞) * (phaseBelowCount 10 c : ℝ≥0∞)) := by
      show (1 - p_ennr / (n : ℝ≥0∞)) * (phaseBelowCount 10 c : ℝ≥0∞) = _
      simpa [one_mul] using
        ENNReal.sub_mul (a := 1) (b := p_ennr / (n : ℝ≥0∞))
          (c := (phaseBelowCount 10 c : ℝ≥0∞))
    calc ∫⁻ c', (phaseBelowCount 10 c' : ℝ≥0∞)
            ∂((NonuniformMajority L K).transitionKernel c)
        ≤ (phaseBelowCount 10 c : ℝ≥0∞) - p_ennr := h_bound
      _ ≤ (phaseBelowCount 10 c : ℝ≥0∞) -
            (p_ennr / (n : ℝ≥0∞) * (phaseBelowCount 10 c : ℝ≥0∞)) := hsub_le
      _ = r * (phaseBelowCount 10 c : ℝ≥0∞) := hmul_sub.symm

/-- Phase-10 epidemic convergence as a PhaseConvergence structure.

Pre: population size n, at least one agent already at phase 10.
Post: all agents at phase 10.

The proof follows the Phase3Convergence pattern exactly:
- Card-conditioned potential (phaseBelowCount 10)
- Source preservation (phase-10 agents persist via phase monotonicity)
- Pair descent (epidemic advances phase-<10 agents to phase 10)
- `measure_potential_ge_one` for the tail bound -/
noncomputable def phase10EpidemicConvergence (n : ℕ) (hn : 8 ≤ n) (t : ℕ)
    (ht : (2 * (n : ℝ)^2 * ((n : ℝ) - 1) * Real.log (n : ℝ)) < ↑t) :
    PhaseConvergence (NonuniformMajority L K).transitionKernel where
  Pre := fun c => c.card = n ∧ hasSource10 c
  Post := Phase10EpidemicPost
  t := t
  ε := ⟨(1 / (n : ℝ)^2).toNNReal, by positivity⟩
  post_absorbing := by
    intro c hc
    change ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
      {y | Phase10EpidemicPost y} = 1
    rw [((NonuniformMajority L K).stepDistOrSelf c).toMeasure_apply_eq_one_iff
      (DiscreteMeasurableSpace.forall_measurableSet _)]
    intro c' hc' a' ha'
    unfold Protocol.stepDistOrSelf at hc'
    split_ifs at hc' with h_size
    · obtain ⟨⟨r₁, r₂⟩, heq⟩ := Protocol.stepDist_support _ _ h_size _ hc'
      subst heq
      unfold Protocol.scheduledStep Protocol.stepOrSelf at ha'
      split_ifs at ha' with h_app
      · rw [Multiset.mem_add] at ha'
        rcases ha' with h_rem | h_new
        · have := hc a' (Multiset.mem_of_le (Multiset.sub_le_self _ _) h_rem)
          have hle : a'.phase.val < 11 := a'.phase.isLt
          omega
        · simp only [Multiset.insert_eq_cons, Multiset.mem_cons,
            Multiset.mem_singleton] at h_new
          rcases h_new with rfl | rfl
          · have hr₁_phase := hc r₁ (Multiset.mem_of_le h_app (by simp))
            exact Transition_left_phase_eq_10 r₁ r₂ hr₁_phase
          · have hr₂_phase := hc r₂ (Multiset.mem_of_le h_app (by simp))
            exact Transition_right_phase_eq_10 r₁ r₂ hr₂_phase
      · exact hc a' ha'
    · simp at hc'; subst hc'; exact hc a' ha'
  convergence := by
    intro c₀ ⟨hcard₀, hsource₀⟩
    set ε_nnr : ℝ≥0 := ⟨(1 / (n : ℝ)^2).toNNReal, by positivity⟩
    set r := 1 - ENNReal.ofReal (2 / ((n : ℝ) * ((n : ℝ) - 1))) / (n : ℝ≥0∞)
    have h_drift : ∀ c, ∫⁻ c', phase10PotentialExt n c'
        ∂((NonuniformMajority L K).transitionKernel c) ≤
        r * phase10PotentialExt n c :=
      phase10PotentialExt_drift n hn
    have h_meas : Measurable (phase10PotentialExt n (L := L) (K := K)) :=
      Measurable.of_discrete
    have h_decay := PopProtoCommon.measure_potential_ge_one
      (NonuniformMajority L K).transitionKernel
      (phase10PotentialExt n) h_meas r h_drift t c₀
    have h_card_zero : ((NonuniformMajority L K).transitionKernel ^ t) c₀
        {c' | c'.card ≠ n} = 0 := by
      apply Protocol.transitionKernel_pow_eq_zero_of_forall_not_reachable
      intro c' hc' hreach
      exact hc' (Protocol.reachable_card_eq hreach ▸ hcard₀)
    have h_nosource_zero : ((NonuniformMajority L K).transitionKernel ^ t) c₀
        {c' | ¬hasSource10 c'} = 0 :=
      hasSource10_transitionKernel_pow_zero c₀ hsource₀ t
    have h_subset_ext : {c' : Config (AgentState L K) |
        c'.card = n ∧ hasSource10 c' ∧ ¬Phase10EpidemicPost c'} ⊆
        {c' | 1 ≤ phase10PotentialExt n c'} := by
      intro c' ⟨hc'_card, hc'_source, hc'_not_post⟩
      simp only [Set.mem_setOf_eq]
      unfold phase10PotentialExt
      simp [hc'_card, hc'_source]
      rw [Phase10EpidemicPost_iff_phaseBelowCount_zero] at hc'_not_post
      exact_mod_cast Nat.pos_of_ne_zero hc'_not_post
    have hΦ_c₀ : phase10PotentialExt n c₀ = (phaseBelowCount 10 c₀ : ℝ≥0∞) := by
      unfold phase10PotentialExt; simp [hcard₀, hsource₀]
    have hΦ_le_n : phase10PotentialExt n c₀ ≤ (n : ℝ≥0∞) := by
      rw [hΦ_c₀]
      exact_mod_cast (hcard₀ ▸ phaseBelowCount_le_card 10 c₀)
    have h_num : r ^ t * (n : ℝ≥0∞) ≤ ENNReal.ofReal (1 / (n : ℝ)^2) :=
      ennreal_r_pow_mul_n_le_phase3 n t hn ht
    calc ((NonuniformMajority L K).transitionKernel ^ t) c₀
            {c' | ¬Phase10EpidemicPost c'}
        ≤ ((NonuniformMajority L K).transitionKernel ^ t) c₀
            ({c' | c'.card = n ∧ hasSource10 c' ∧ ¬Phase10EpidemicPost c'} ∪
             {c' | c'.card ≠ n} ∪ {c' | ¬hasSource10 c'}) := by
          apply measure_mono
          intro c' hc'
          by_cases hc'_card : c'.card = n
          · by_cases hc'_source : hasSource10 c'
            · left; left; exact ⟨hc'_card, hc'_source, hc'⟩
            · right; exact hc'_source
          · left; right; exact hc'_card
      _ ≤ ((NonuniformMajority L K).transitionKernel ^ t) c₀
            ({c' | c'.card = n ∧ hasSource10 c' ∧ ¬Phase10EpidemicPost c'} ∪
             {c' | c'.card ≠ n}) +
          ((NonuniformMajority L K).transitionKernel ^ t) c₀
            {c' | ¬hasSource10 c'} := measure_union_le _ _
      _ = ((NonuniformMajority L K).transitionKernel ^ t) c₀
            ({c' | c'.card = n ∧ hasSource10 c' ∧ ¬Phase10EpidemicPost c'} ∪
             {c' | c'.card ≠ n}) + 0 := by
          rw [h_nosource_zero]
      _ = ((NonuniformMajority L K).transitionKernel ^ t) c₀
            ({c' | c'.card = n ∧ hasSource10 c' ∧ ¬Phase10EpidemicPost c'} ∪
             {c' | c'.card ≠ n}) := add_zero _
      _ ≤ ((NonuniformMajority L K).transitionKernel ^ t) c₀
            {c' | c'.card = n ∧ hasSource10 c' ∧ ¬Phase10EpidemicPost c'} +
          ((NonuniformMajority L K).transitionKernel ^ t) c₀
            {c' | c'.card ≠ n} := measure_union_le _ _
      _ = ((NonuniformMajority L K).transitionKernel ^ t) c₀
            {c' | c'.card = n ∧ hasSource10 c' ∧ ¬Phase10EpidemicPost c'} + 0 := by
          rw [h_card_zero]
      _ = ((NonuniformMajority L K).transitionKernel ^ t) c₀
            {c' | c'.card = n ∧ hasSource10 c' ∧ ¬Phase10EpidemicPost c'} := add_zero _
      _ ≤ ((NonuniformMajority L K).transitionKernel ^ t) c₀
            {c' | 1 ≤ phase10PotentialExt n c'} := measure_mono h_subset_ext
      _ ≤ r ^ t * phase10PotentialExt n c₀ := h_decay
      _ ≤ r ^ t * (n : ℝ≥0∞) := by gcongr
      _ ≤ ENNReal.ofReal (1 / (n : ℝ) ^ 2) := h_num
      _ = (ε_nnr : ℝ≥0∞) := by
          simp only [ε_nnr]
          rfl

/-- **Doty et al. Lemma 7.7**: the 6-state stable-backup protocol in Phase 10
stably computes majority in `O(n log n)` parallel time, both in
expectation and with high probability `1 − O(1/n²)`.

The tail bound is expressed on a probability space `(Ω, μ)` with a
hitting-time random variable `T`. The proof uses the Phase3Convergence
pattern: card-conditioned potential `phaseBelowCount 10`, epidemic
source preservation, pair descent, and `measure_potential_ge_one`. -/
theorem lemma_7_7_phase_ten_stable_backup
    (c₀ : Config (AgentState L K))
    (hn : 8 ≤ c₀.card) (hcard : c₀.card = n)
    (hsource : hasSource10 c₀)
    (t : ℕ) (ht : (2 * (n : ℝ) ^ 2 * ((n : ℝ) - 1) * Real.log (n : ℝ)) < ↑t) :
    ((NonuniformMajority L K).transitionKernel ^ t) c₀
        {c : Config (AgentState L K) | ¬(∀ a ∈ c, a.phase.val = 10)} ≤
      ENNReal.ofReal (1 / ((n : ℝ) ^ 2)) := by
  have h_conv := (phase10EpidemicConvergence (L := L) (K := K) n (hcard ▸ hn) t
    (hcard ▸ ht)).convergence c₀ ⟨hcard, hsource⟩
  exact le_trans (measure_mono (fun c hc => by
    simp only [Set.mem_setOf_eq, Phase10EpidemicPost] at hc ⊢; exact hc)) h_conv

end Phase10Epidemic

/-! ### Phase-4 tie detection: prePhase4MassSum = initialGap -/

/-- Base case: at a valid initial configuration (all agents phase 0),
`prePhase4MassSum = (smallBiasSum : ℚ) = (initialGap : ℚ)`. -/
theorem prePhase4MassSum_validInitial_eq_initialGap
    (init : Config (AgentState L K))
    (hinit : validInitial init) :
    prePhase4MassSum init = (initialGap init : ℚ) := by
  have hphase : ∀ a ∈ init, a.phase.val < 3 := by
    intro a ha
    have hph := (hinit a ha).1
    have : a.phase.val = 0 := by
      have := congr_arg Fin.val hph
      simpa using this
    omega
  have h1 : prePhase4MassSum init = (smallBiasSum init : ℚ) :=
    prePhase4MassSum_eq_smallBiasSum_of_phase_lt_three (L := L) (K := K) init hphase
  have h2 : smallBiasSum init = initialGap init :=
    validInitial_smallBiasSum_initialGap (L := L) (K := K) init hinit
  rw [h1, h2]

end Ripple.PopulationProtocol.ExactMajority
