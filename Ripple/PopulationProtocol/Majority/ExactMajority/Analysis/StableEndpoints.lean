/-
Stable endpoint lemmas for the Doty et al. exact-majority protocol.

This file contains deterministic endpoint facts only.  The phase analysis must
still prove that these endpoints are reachable from arbitrary reachable
configurations.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Analysis.Invariants
import Ripple.PopulationProtocol.Majority.ExactMajority.Analysis.PhaseProgress

open Multiset

namespace ExactMajority

variable {L K : ℕ}

private theorem one_lt_eight : 1 < 8 :=
  Nat.succ_lt_succ (Nat.succ_pos 6)

private theorem two_lt_eight : 2 < 8 :=
  Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_pos 5))

private theorem four_lt_eight : 4 < 8 :=
  Nat.succ_lt_succ
    (Nat.succ_lt_succ
      (Nat.succ_lt_succ
        (Nat.succ_lt_succ (Nat.succ_pos 3))))

private theorem two_lt_eleven : 2 < 11 :=
  Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_pos 8))

/-- Phase-2 singleton opinion set `{+1}`. -/
def phase2OpinionA : Fin 8 := ⟨4, four_lt_eight⟩

/-- Phase-2 singleton opinion set `{-1}`. -/
def phase2OpinionB : Fin 8 := ⟨1, one_lt_eight⟩

/-- Phase-2 singleton opinion set `{0}`. -/
def phase2OpinionT : Fin 8 := ⟨2, two_lt_eight⟩

private def phase2ConsensusWith
    (opinion : Fin 8) (out : Output) (c : Config (AgentState L K)) : Prop :=
  ∀ a ∈ c, a.phase.val = 2 ∧ a.opinions = opinion ∧ a.output = out

private def phase2OutputAWithSigns (c : Config (AgentState L K)) : Prop :=
  phase2LocallyStable (L := L) (K := K) c ∧
    ∀ a ∈ c, a.output = .A ∧ hasPlusOne a.opinions = true ∧
      hasMinusOne a.opinions = false

private def phase2OutputBWithSigns (c : Config (AgentState L K)) : Prop :=
  phase2LocallyStable (L := L) (K := K) c ∧
    ∀ a ∈ c, a.output = .B ∧ hasMinusOne a.opinions = true ∧
      hasPlusOne a.opinions = false

private def phase2OutputTWithSigns (c : Config (AgentState L K)) : Prop :=
  phase2LocallyStable (L := L) (K := K) c ∧
    ∀ a ∈ c, a.output = .T ∧ hasMinusOne a.opinions = false ∧
      hasPlusOne a.opinions = false

private def phase2GoodA (a : AgentState L K) : Prop :=
  a.phase.val = 2 ∧ a.output = .A ∧
    hasPlusOne a.opinions = true ∧ hasMinusOne a.opinions = false

private def phase2GoodB (a : AgentState L K) : Prop :=
  a.phase.val = 2 ∧ a.output = .B ∧
    hasMinusOne a.opinions = true ∧ hasPlusOne a.opinions = false

private def phase2GoodT (a : AgentState L K) : Prop :=
  a.phase.val = 2 ∧ a.output = .T ∧
    a.opinions = phase2OpinionT

private noncomputable def phase2WrongACount (c : Config (AgentState L K)) : ℕ := by
  classical
  exact Multiset.countP (fun a => ¬ phase2GoodA (L := L) (K := K) a) c

private noncomputable def phase2WrongBCount (c : Config (AgentState L K)) : ℕ := by
  classical
  exact Multiset.countP (fun a => ¬ phase2GoodB (L := L) (K := K) a) c

private noncomputable def phase2WrongTCount (c : Config (AgentState L K)) : ℕ := by
  classical
  exact Multiset.countP (fun a => ¬ phase2GoodT (L := L) (K := K) a) c

/-- A Phase-2 consensus endpoint at the output/sign-support level.  Opinions
are not required to be singleton: for example `{0,+1}` is a valid `A` endpoint
state.  The sign-support side conditions are needed for stability; unanimous
output plus local no-advance alone would allow `{0}`-only agents to change an
`A` output back to `T`. -/
def phase2ConsensusEndpoint
    (init c : Config (AgentState L K)) : Prop :=
  (majorityVerdict init = outputTripleOfOutput .A ∧
    phase2OutputAWithSigns (L := L) (K := K) c) ∨
  (majorityVerdict init = outputTripleOfOutput .B ∧
    phase2OutputBWithSigns (L := L) (K := K) c) ∨
  (majorityVerdict init = outputTripleOfOutput .T ∧
    phase2OutputTWithSigns (L := L) (K := K) c)

theorem phase2ConsensusEndpoint_of_A
    (init c : Config (AgentState L K))
    (hmajor : majorityVerdict init = outputTripleOfOutput .A)
    (hstable : phase2LocallyStable (L := L) (K := K) c)
    (h : ∀ a ∈ c, a.output = .A ∧ hasPlusOne a.opinions = true ∧
      hasMinusOne a.opinions = false) :
    phase2ConsensusEndpoint (L := L) (K := K) init c :=
  Or.inl ⟨hmajor, hstable, h⟩

theorem phase2ConsensusEndpoint_of_B
    (init c : Config (AgentState L K))
    (hmajor : majorityVerdict init = outputTripleOfOutput .B)
    (hstable : phase2LocallyStable (L := L) (K := K) c)
    (h : ∀ a ∈ c, a.output = .B ∧ hasMinusOne a.opinions = true ∧
      hasPlusOne a.opinions = false) :
    phase2ConsensusEndpoint (L := L) (K := K) init c :=
  Or.inr (Or.inl ⟨hmajor, hstable, h⟩)

theorem phase2ConsensusEndpoint_of_T
    (init c : Config (AgentState L K))
    (hmajor : majorityVerdict init = outputTripleOfOutput .T)
    (hstable : phase2LocallyStable (L := L) (K := K) c)
    (h : ∀ a ∈ c, a.output = .T ∧ hasMinusOne a.opinions = false ∧
      hasPlusOne a.opinions = false) :
    phase2ConsensusEndpoint (L := L) (K := K) init c :=
  Or.inr (Or.inr ⟨hmajor, hstable, h⟩)

private lemma phase_eq_two (a : AgentState L K) (h : a.phase.val = 2) :
    a.phase = ⟨2, two_lt_eleven⟩ := by
  exact Fin.ext h

private lemma no_phase_init_between_two :
    (List.range 11).filter (fun k => decide (2 < k ∧ k ≤ 2)) = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro k _ hk
  simp only [decide_eq_true_eq] at hk
  exact Nat.not_lt_of_ge hk.2 hk.1

private lemma runInitsBetween_two_two (a : AgentState L K) :
    runInitsBetween L K 2 2 a = a := by
  unfold runInitsBetween
  rw [no_phase_init_between_two]
  rfl

private lemma phaseEpidemicUpdate_eq_self_of_phase2
    (s t : AgentState L K)
    (hs_phase : s.phase = ⟨2, two_lt_eleven⟩)
    (ht_phase : t.phase = ⟨2, two_lt_eleven⟩) :
    phaseEpidemicUpdate L K s t = (s, t) := by
  unfold phaseEpidemicUpdate
  rw [hs_phase, ht_phase, max_self]
  simp only [runInitsBetween_two_two]
  cases s
  cases t
  simp_all

private lemma opinionsUnion_A_A :
    opinionsUnion phase2OpinionA phase2OpinionA = phase2OpinionA := by
  rfl

private lemma opinionsUnion_B_B :
    opinionsUnion phase2OpinionB phase2OpinionB = phase2OpinionB := by
  rfl

private lemma opinionsUnion_T_T :
    opinionsUnion phase2OpinionT phase2OpinionT = phase2OpinionT := by
  rfl

private lemma hasMinusOne_A : hasMinusOne phase2OpinionA = false := by
  rfl

private lemma hasPlusOne_A : hasPlusOne phase2OpinionA = true := by
  rfl

private lemma hasMinusOne_B : hasMinusOne phase2OpinionB = true := by
  rfl

private lemma hasPlusOne_B : hasPlusOne phase2OpinionB = false := by
  rfl

private lemma hasMinusOne_T : hasMinusOne phase2OpinionT = false := by
  rfl

private lemma hasPlusOne_T : hasPlusOne phase2OpinionT = false := by
  rfl

private lemma phase2OpinionT_val : phase2OpinionT.val = 2 := by
  rfl

private lemma hasMinusOne_opinionsUnion_false
    (x y : Fin 8) (hx : hasMinusOne x = false) (hy : hasMinusOne y = false) :
    hasMinusOne (opinionsUnion x y) = false := by
  fin_cases x <;> simp [hasMinusOne] at hx ⊢ <;>
    fin_cases y <;> simp [opinionsUnion, hasMinusOne] at hy ⊢

private lemma hasPlusOne_opinionsUnion_false
    (x y : Fin 8) (hx : hasPlusOne x = false) (hy : hasPlusOne y = false) :
    hasPlusOne (opinionsUnion x y) = false := by
  fin_cases x <;> simp [hasPlusOne] at hx ⊢ <;>
    fin_cases y <;> simp [opinionsUnion, hasPlusOne] at hy ⊢

private lemma hasPlusOne_opinionsUnion_true_left
    (x y : Fin 8) (hx : hasPlusOne x = true) :
    hasPlusOne (opinionsUnion x y) = true := by
  fin_cases x <;> simp [hasPlusOne] at hx ⊢ <;>
    fin_cases y <;> simp [opinionsUnion, hasPlusOne] at hx ⊢

private lemma hasMinusOne_opinionsUnion_true_left
    (x y : Fin 8) (hx : hasMinusOne x = true) :
    hasMinusOne (opinionsUnion x y) = true := by
  fin_cases x <;> simp [hasMinusOne] at hx ⊢ <;>
    fin_cases y <;> simp [opinionsUnion, hasMinusOne] at hx ⊢

private theorem Phase2Transition_preserves_phase2_A
    (s t : AgentState L K)
    (hs_op : s.opinions = phase2OpinionA)
    (ht_op : t.opinions = phase2OpinionA) :
    ((Phase2Transition L K s t).1.phase.val = s.phase.val ∧
      (Phase2Transition L K s t).1.opinions = phase2OpinionA ∧
      (Phase2Transition L K s t).1.output = .A) ∧
    ((Phase2Transition L K s t).2.phase.val = t.phase.val ∧
      (Phase2Transition L K s t).2.opinions = phase2OpinionA ∧
      (Phase2Transition L K s t).2.output = .A) := by
  simp only [Phase2Transition, hs_op, ht_op, opinionsUnion_A_A, hasMinusOne_A,
    hasPlusOne_A, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  repeat constructor

private theorem Phase2Transition_preserves_phase2_B
    (s t : AgentState L K)
    (hs_op : s.opinions = phase2OpinionB)
    (ht_op : t.opinions = phase2OpinionB) :
    ((Phase2Transition L K s t).1.phase.val = s.phase.val ∧
      (Phase2Transition L K s t).1.opinions = phase2OpinionB ∧
      (Phase2Transition L K s t).1.output = .B) ∧
    ((Phase2Transition L K s t).2.phase.val = t.phase.val ∧
      (Phase2Transition L K s t).2.opinions = phase2OpinionB ∧
      (Phase2Transition L K s t).2.output = .B) := by
  simp only [Phase2Transition, hs_op, ht_op, opinionsUnion_B_B, hasMinusOne_B,
    hasPlusOne_B, Bool.true_and, Bool.false_eq_true, ↓reduceIte]
  repeat constructor

private theorem Phase2Transition_preserves_phase2_T
    (s t : AgentState L K)
    (hs_op : s.opinions = phase2OpinionT)
    (ht_op : t.opinions = phase2OpinionT) :
    ((Phase2Transition L K s t).1.phase.val = s.phase.val ∧
      (Phase2Transition L K s t).1.opinions = phase2OpinionT ∧
      (Phase2Transition L K s t).1.output = .T) ∧
    ((Phase2Transition L K s t).2.phase.val = t.phase.val ∧
      (Phase2Transition L K s t).2.opinions = phase2OpinionT ∧
      (Phase2Transition L K s t).2.output = .T) := by
  simp only [Phase2Transition, hs_op, ht_op, opinionsUnion_T_T, hasMinusOne_T,
    hasPlusOne_T, Bool.false_and, Bool.false_eq_true, phase2OpinionT_val,
    ↓reduceIte]
  repeat constructor

private theorem Transition_preserves_phase2_A
    (s t : AgentState L K)
    (hs_phase : s.phase.val = 2) (ht_phase : t.phase.val = 2)
    (hs_op : s.opinions = phase2OpinionA)
    (ht_op : t.opinions = phase2OpinionA) :
    ((Transition L K s t).1.phase.val = 2 ∧
      (Transition L K s t).1.opinions = phase2OpinionA ∧
      (Transition L K s t).1.output = .A) ∧
    ((Transition L K s t).2.phase.val = 2 ∧
      (Transition L K s t).2.opinions = phase2OpinionA ∧
      (Transition L K s t).2.output = .A) := by
  have hs_phase_eq := phase_eq_two (L := L) (K := K) s hs_phase
  have ht_phase_eq := phase_eq_two (L := L) (K := K) t ht_phase
  have hepidemic := phaseEpidemicUpdate_eq_self_of_phase2 (L := L) (K := K)
    s t hs_phase_eq ht_phase_eq
  simp [Transition, hepidemic, hs_phase_eq, ht_phase_eq, Phase2Transition, hs_op, ht_op,
    opinionsUnion_A_A, hasMinusOne_A, hasPlusOne_A]
  all_goals
    try rw [finishPhase10Entry_eq_self_of_after_ne_10]
    simp [finishPhase10Entry, canonicalPhase10Entry, hs_phase, ht_phase]

private theorem Transition_preserves_phase2_B
    (s t : AgentState L K)
    (hs_phase : s.phase.val = 2) (ht_phase : t.phase.val = 2)
    (hs_op : s.opinions = phase2OpinionB)
    (ht_op : t.opinions = phase2OpinionB) :
    ((Transition L K s t).1.phase.val = 2 ∧
      (Transition L K s t).1.opinions = phase2OpinionB ∧
      (Transition L K s t).1.output = .B) ∧
    ((Transition L K s t).2.phase.val = 2 ∧
      (Transition L K s t).2.opinions = phase2OpinionB ∧
      (Transition L K s t).2.output = .B) := by
  have hs_phase_eq := phase_eq_two (L := L) (K := K) s hs_phase
  have ht_phase_eq := phase_eq_two (L := L) (K := K) t ht_phase
  have hepidemic := phaseEpidemicUpdate_eq_self_of_phase2 (L := L) (K := K)
    s t hs_phase_eq ht_phase_eq
  simp [Transition, hepidemic, hs_phase_eq, ht_phase_eq, Phase2Transition, hs_op, ht_op,
    opinionsUnion_B_B, hasMinusOne_B, hasPlusOne_B]
  all_goals
    try rw [finishPhase10Entry_eq_self_of_after_ne_10]
    simp [finishPhase10Entry, canonicalPhase10Entry]

private theorem Transition_preserves_phase2_T
    (s t : AgentState L K)
    (hs_phase : s.phase.val = 2) (ht_phase : t.phase.val = 2)
    (hs_op : s.opinions = phase2OpinionT)
    (ht_op : t.opinions = phase2OpinionT) :
    ((Transition L K s t).1.phase.val = 2 ∧
      (Transition L K s t).1.opinions = phase2OpinionT ∧
      (Transition L K s t).1.output = .T) ∧
    ((Transition L K s t).2.phase.val = 2 ∧
      (Transition L K s t).2.opinions = phase2OpinionT ∧
      (Transition L K s t).2.output = .T) := by
  have hs_phase_eq := phase_eq_two (L := L) (K := K) s hs_phase
  have ht_phase_eq := phase_eq_two (L := L) (K := K) t ht_phase
  have hepidemic := phaseEpidemicUpdate_eq_self_of_phase2 (L := L) (K := K)
    s t hs_phase_eq ht_phase_eq
  simp [Transition, hepidemic, hs_phase_eq, ht_phase_eq, Phase2Transition, hs_op, ht_op,
    opinionsUnion_T_T, hasMinusOne_T, hasPlusOne_T, phase2OpinionT_val]
  all_goals
    try rw [finishPhase10Entry_eq_self_of_after_ne_10]
    simp [finishPhase10Entry, canonicalPhase10Entry]

private theorem phase2_A_preserved_by_step
    (c c' : Config (AgentState L K))
    (h_c : phase2ConsensusWith (L := L) (K := K) phase2OpinionA .A c)
    (h_step : (NonuniformMajority L K).StepRel c c') :
    phase2ConsensusWith (L := L) (K := K) phase2OpinionA .A c' := by
  rcases h_step with ⟨r₁, r₂, happ, hc'⟩
  dsimp [Protocol.Applicable, NonuniformMajority] at happ hc'
  have hr₁_mem : r₁ ∈ c := Multiset.mem_of_le happ (by simp)
  have hr₂_mem : r₂ ∈ c := Multiset.mem_of_le happ (by simp)
  rcases h_c r₁ hr₁_mem with ⟨hr₁_phase, hr₁_op, _hr₁_out⟩
  rcases h_c r₂ hr₂_mem with ⟨hr₂_phase, hr₂_op, _hr₂_out⟩
  have htrans := Transition_preserves_phase2_A (L := L) (K := K)
    r₁ r₂ hr₁_phase hr₂_phase hr₁_op hr₂_op
  rw [hc']
  intro a ha
  simp only [Multiset.mem_add, Multiset.mem_cons, Multiset.mem_singleton] at ha
  rcases ha with h_old | h_new
  · exact h_c a (Multiset.mem_of_le (Multiset.sub_le_self c {r₁, r₂}) h_old)
  · rcases h_new with h_eq | h_eq
    · simpa [h_eq] using htrans.1
    · simpa [h_eq] using htrans.2

private theorem phase2_B_preserved_by_step
    (c c' : Config (AgentState L K))
    (h_c : phase2ConsensusWith (L := L) (K := K) phase2OpinionB .B c)
    (h_step : (NonuniformMajority L K).StepRel c c') :
    phase2ConsensusWith (L := L) (K := K) phase2OpinionB .B c' := by
  rcases h_step with ⟨r₁, r₂, happ, hc'⟩
  dsimp [Protocol.Applicable, NonuniformMajority] at happ hc'
  have hr₁_mem : r₁ ∈ c := Multiset.mem_of_le happ (by simp)
  have hr₂_mem : r₂ ∈ c := Multiset.mem_of_le happ (by simp)
  rcases h_c r₁ hr₁_mem with ⟨hr₁_phase, hr₁_op, _hr₁_out⟩
  rcases h_c r₂ hr₂_mem with ⟨hr₂_phase, hr₂_op, _hr₂_out⟩
  have htrans := Transition_preserves_phase2_B (L := L) (K := K)
    r₁ r₂ hr₁_phase hr₂_phase hr₁_op hr₂_op
  rw [hc']
  intro a ha
  simp only [Multiset.mem_add, Multiset.mem_cons, Multiset.mem_singleton] at ha
  rcases ha with h_old | h_new
  · exact h_c a (Multiset.mem_of_le (Multiset.sub_le_self c {r₁, r₂}) h_old)
  · rcases h_new with h_eq | h_eq
    · simpa [h_eq] using htrans.1
    · simpa [h_eq] using htrans.2

private theorem phase2_T_preserved_by_step
    (c c' : Config (AgentState L K))
    (h_c : phase2ConsensusWith (L := L) (K := K) phase2OpinionT .T c)
    (h_step : (NonuniformMajority L K).StepRel c c') :
    phase2ConsensusWith (L := L) (K := K) phase2OpinionT .T c' := by
  rcases h_step with ⟨r₁, r₂, happ, hc'⟩
  dsimp [Protocol.Applicable, NonuniformMajority] at happ hc'
  have hr₁_mem : r₁ ∈ c := Multiset.mem_of_le happ (by simp)
  have hr₂_mem : r₂ ∈ c := Multiset.mem_of_le happ (by simp)
  rcases h_c r₁ hr₁_mem with ⟨hr₁_phase, hr₁_op, _hr₁_out⟩
  rcases h_c r₂ hr₂_mem with ⟨hr₂_phase, hr₂_op, _hr₂_out⟩
  have htrans := Transition_preserves_phase2_T (L := L) (K := K)
    r₁ r₂ hr₁_phase hr₂_phase hr₁_op hr₂_op
  rw [hc']
  intro a ha
  simp only [Multiset.mem_add, Multiset.mem_cons, Multiset.mem_singleton] at ha
  rcases ha with h_old | h_new
  · exact h_c a (Multiset.mem_of_le (Multiset.sub_le_self c {r₁, r₂}) h_old)
  · rcases h_new with h_eq | h_eq
    · simpa [h_eq] using htrans.1
    · simpa [h_eq] using htrans.2

private theorem phase2_A_preserved_by_reachable
    (c c' : Config (AgentState L K))
    (h_c : phase2ConsensusWith (L := L) (K := K) phase2OpinionA .A c)
    (h_reach : (NonuniformMajority L K).Reachable c c') :
    phase2ConsensusWith (L := L) (K := K) phase2OpinionA .A c' := by
  induction h_reach with
  | refl => exact h_c
  | tail _ hstep ih =>
      exact phase2_A_preserved_by_step (L := L) (K := K) _ _ ih hstep

private theorem phase2_B_preserved_by_reachable
    (c c' : Config (AgentState L K))
    (h_c : phase2ConsensusWith (L := L) (K := K) phase2OpinionB .B c)
    (h_reach : (NonuniformMajority L K).Reachable c c') :
    phase2ConsensusWith (L := L) (K := K) phase2OpinionB .B c' := by
  induction h_reach with
  | refl => exact h_c
  | tail _ hstep ih =>
      exact phase2_B_preserved_by_step (L := L) (K := K) _ _ ih hstep

private theorem phase2_T_preserved_by_reachable
    (c c' : Config (AgentState L K))
    (h_c : phase2ConsensusWith (L := L) (K := K) phase2OpinionT .T c)
    (h_reach : (NonuniformMajority L K).Reachable c c') :
    phase2ConsensusWith (L := L) (K := K) phase2OpinionT .T c' := by
  induction h_reach with
  | refl => exact h_c
  | tail _ hstep ih =>
      exact phase2_T_preserved_by_step (L := L) (K := K) _ _ ih hstep

private theorem Transition_preserves_phase2_A_signs
    (s t : AgentState L K)
    (hs_phase : s.phase.val = 2) (ht_phase : t.phase.val = 2)
    (hs_out : s.output = .A) (ht_out : t.output = .A)
    (hs_plus : hasPlusOne s.opinions = true)
    (ht_plus : hasPlusOne t.opinions = true)
    (hs_minus : hasMinusOne s.opinions = false)
    (ht_minus : hasMinusOne t.opinions = false) :
    ((Transition L K s t).1.phase.val = 2 ∧
      (Transition L K s t).1.output = .A ∧
      hasPlusOne (Transition L K s t).1.opinions = true ∧
      hasMinusOne (Transition L K s t).1.opinions = false) ∧
    ((Transition L K s t).2.phase.val = 2 ∧
      (Transition L K s t).2.output = .A ∧
      hasPlusOne (Transition L K s t).2.opinions = true ∧
      hasMinusOne (Transition L K s t).2.opinions = false) := by
  have hs_phase_eq := phase_eq_two (L := L) (K := K) s hs_phase
  have ht_phase_eq := phase_eq_two (L := L) (K := K) t ht_phase
  have hepidemic := phaseEpidemicUpdate_eq_self_of_phase2 (L := L) (K := K)
    s t hs_phase_eq ht_phase_eq
  have hplus_union :
      hasPlusOne (opinionsUnion s.opinions t.opinions) = true :=
    hasPlusOne_opinionsUnion_true_left s.opinions t.opinions hs_plus
  have hminus_union :
      hasMinusOne (opinionsUnion s.opinions t.opinions) = false :=
    hasMinusOne_opinionsUnion_false s.opinions t.opinions hs_minus ht_minus
  simp [Transition, hepidemic, hs_phase_eq, ht_phase_eq, Phase2Transition,
    hs_out, ht_out, hplus_union, hminus_union]
  all_goals
    try rw [finishPhase10Entry_eq_self_of_after_ne_10]
    simp [finishPhase10Entry, canonicalPhase10Entry, hplus_union, hminus_union]

private theorem Transition_preserves_phase2_B_signs
    (s t : AgentState L K)
    (hs_phase : s.phase.val = 2) (ht_phase : t.phase.val = 2)
    (hs_out : s.output = .B) (ht_out : t.output = .B)
    (hs_minus : hasMinusOne s.opinions = true)
    (ht_minus : hasMinusOne t.opinions = true)
    (hs_plus : hasPlusOne s.opinions = false)
    (ht_plus : hasPlusOne t.opinions = false) :
    ((Transition L K s t).1.phase.val = 2 ∧
      (Transition L K s t).1.output = .B ∧
      hasMinusOne (Transition L K s t).1.opinions = true ∧
      hasPlusOne (Transition L K s t).1.opinions = false) ∧
    ((Transition L K s t).2.phase.val = 2 ∧
      (Transition L K s t).2.output = .B ∧
      hasMinusOne (Transition L K s t).2.opinions = true ∧
      hasPlusOne (Transition L K s t).2.opinions = false) := by
  have hs_phase_eq := phase_eq_two (L := L) (K := K) s hs_phase
  have ht_phase_eq := phase_eq_two (L := L) (K := K) t ht_phase
  have hepidemic := phaseEpidemicUpdate_eq_self_of_phase2 (L := L) (K := K)
    s t hs_phase_eq ht_phase_eq
  have hminus_union :
      hasMinusOne (opinionsUnion s.opinions t.opinions) = true :=
    hasMinusOne_opinionsUnion_true_left s.opinions t.opinions hs_minus
  have hplus_union :
      hasPlusOne (opinionsUnion s.opinions t.opinions) = false :=
    hasPlusOne_opinionsUnion_false s.opinions t.opinions hs_plus ht_plus
  simp [Transition, hepidemic, hs_phase_eq, ht_phase_eq, Phase2Transition,
    hs_out, ht_out, hplus_union, hminus_union]
  all_goals
    try rw [finishPhase10Entry_eq_self_of_after_ne_10]
    simp [finishPhase10Entry, canonicalPhase10Entry, hplus_union, hminus_union]

private theorem Transition_preserves_phase2_T_signs
    (s t : AgentState L K)
    (hs_phase : s.phase.val = 2) (ht_phase : t.phase.val = 2)
    (hs_out : s.output = .T) (ht_out : t.output = .T)
    (hs_minus : hasMinusOne s.opinions = false)
    (ht_minus : hasMinusOne t.opinions = false)
    (hs_plus : hasPlusOne s.opinions = false)
    (ht_plus : hasPlusOne t.opinions = false) :
    ((Transition L K s t).1.phase.val = 2 ∧
      (Transition L K s t).1.output = .T ∧
      hasMinusOne (Transition L K s t).1.opinions = false ∧
      hasPlusOne (Transition L K s t).1.opinions = false) ∧
    ((Transition L K s t).2.phase.val = 2 ∧
      (Transition L K s t).2.output = .T ∧
      hasMinusOne (Transition L K s t).2.opinions = false ∧
      hasPlusOne (Transition L K s t).2.opinions = false) := by
  have hs_phase_eq := phase_eq_two (L := L) (K := K) s hs_phase
  have ht_phase_eq := phase_eq_two (L := L) (K := K) t ht_phase
  have hepidemic := phaseEpidemicUpdate_eq_self_of_phase2 (L := L) (K := K)
    s t hs_phase_eq ht_phase_eq
  have hminus_union :
      hasMinusOne (opinionsUnion s.opinions t.opinions) = false :=
    hasMinusOne_opinionsUnion_false s.opinions t.opinions hs_minus ht_minus
  have hplus_union :
      hasPlusOne (opinionsUnion s.opinions t.opinions) = false :=
    hasPlusOne_opinionsUnion_false s.opinions t.opinions hs_plus ht_plus
  simp [Transition, hepidemic, hs_phase_eq, ht_phase_eq, Phase2Transition,
    hs_out, ht_out, hplus_union, hminus_union]
  all_goals
    try rw [finishPhase10Entry_eq_self_of_after_ne_10]
    split_ifs <;> simp [finishPhase10Entry, canonicalPhase10Entry,
      hplus_union, hminus_union]

private theorem pair_le_of_mem_ne
    {α : Type*} [DecidableEq α] {c : Multiset α} {a b : α}
    (ha : a ∈ c) (hb : b ∈ c) (hne : a ≠ b) :
    ({a, b} : Multiset α) ≤ c := by
  have hnot : a ∉ ({b} : Multiset α) := by
    simp [hne]
  change a ::ₘ ({b} : Multiset α) ≤ c
  rw [Multiset.cons_le_of_notMem hnot]
  exact ⟨ha, Multiset.singleton_le.2 hb⟩

private lemma exists_applicable_pair_left_of_mem_card_ge_two
    {c : Config (AgentState L K)} {a : AgentState L K}
    (ha : a ∈ c) (hcard : 2 ≤ c.card) :
    ∃ b, Protocol.Applicable c a b := by
  have herase_pos : 0 < (c.erase a).card := by
    have hcard_erase := Multiset.card_erase_add_one ha
    omega
  rcases Multiset.card_pos_iff_exists_mem.mp herase_pos with ⟨b, hb⟩
  refine ⟨b, ?_⟩
  change a ::ₘ ({b} : Multiset (AgentState L K)) ≤ c
  rw [← Multiset.cons_erase ha]
  exact Multiset.cons_le_cons a (Multiset.singleton_le.mpr hb)

theorem Transition_phase2_A_carrier_closes
    (s t : AgentState L K)
    (hs_phase : s.phase.val = 2) (ht_phase : t.phase.val = 2)
    (hs_out : s.output = .A)
    (hs_plus : hasPlusOne s.opinions = true)
    (hs_minus : hasMinusOne s.opinions = false)
    (ht_minus : hasMinusOne t.opinions = false) :
    ((Transition L K s t).1.phase.val = 2 ∧
      (Transition L K s t).1.output = .A ∧
      hasPlusOne (Transition L K s t).1.opinions = true ∧
      hasMinusOne (Transition L K s t).1.opinions = false) ∧
    ((Transition L K s t).2.phase.val = 2 ∧
      (Transition L K s t).2.output = .A ∧
      hasPlusOne (Transition L K s t).2.opinions = true ∧
      hasMinusOne (Transition L K s t).2.opinions = false) := by
  have hs_phase_eq := phase_eq_two (L := L) (K := K) s hs_phase
  have ht_phase_eq := phase_eq_two (L := L) (K := K) t ht_phase
  have hepidemic := phaseEpidemicUpdate_eq_self_of_phase2 (L := L) (K := K)
    s t hs_phase_eq ht_phase_eq
  have hplus_union :
      hasPlusOne (opinionsUnion s.opinions t.opinions) = true :=
    hasPlusOne_opinionsUnion_true_left s.opinions t.opinions hs_plus
  have hminus_union :
      hasMinusOne (opinionsUnion s.opinions t.opinions) = false :=
    hasMinusOne_opinionsUnion_false s.opinions t.opinions hs_minus ht_minus
  simp [Transition, hepidemic, hs_phase_eq, ht_phase_eq, Phase2Transition,
    hs_out, hplus_union, hminus_union]
  all_goals
    try rw [finishPhase10Entry_eq_self_of_after_ne_10]
    simp [finishPhase10Entry, canonicalPhase10Entry, hplus_union, hminus_union]

theorem Transition_phase2_B_carrier_closes
    (s t : AgentState L K)
    (hs_phase : s.phase.val = 2) (ht_phase : t.phase.val = 2)
    (hs_out : s.output = .B)
    (hs_minus : hasMinusOne s.opinions = true)
    (hs_plus : hasPlusOne s.opinions = false)
    (ht_plus : hasPlusOne t.opinions = false) :
    ((Transition L K s t).1.phase.val = 2 ∧
      (Transition L K s t).1.output = .B ∧
      hasMinusOne (Transition L K s t).1.opinions = true ∧
      hasPlusOne (Transition L K s t).1.opinions = false) ∧
    ((Transition L K s t).2.phase.val = 2 ∧
      (Transition L K s t).2.output = .B ∧
      hasMinusOne (Transition L K s t).2.opinions = true ∧
      hasPlusOne (Transition L K s t).2.opinions = false) := by
  have hs_phase_eq := phase_eq_two (L := L) (K := K) s hs_phase
  have ht_phase_eq := phase_eq_two (L := L) (K := K) t ht_phase
  have hepidemic := phaseEpidemicUpdate_eq_self_of_phase2 (L := L) (K := K)
    s t hs_phase_eq ht_phase_eq
  have hminus_union :
      hasMinusOne (opinionsUnion s.opinions t.opinions) = true :=
    hasMinusOne_opinionsUnion_true_left s.opinions t.opinions hs_minus
  have hplus_union :
      hasPlusOne (opinionsUnion s.opinions t.opinions) = false :=
    hasPlusOne_opinionsUnion_false s.opinions t.opinions hs_plus ht_plus
  simp [Transition, hepidemic, hs_phase_eq, ht_phase_eq, Phase2Transition,
    hs_out, hplus_union, hminus_union]
  all_goals
    try rw [finishPhase10Entry_eq_self_of_after_ne_10]
    simp [finishPhase10Entry, canonicalPhase10Entry, hplus_union, hminus_union]

theorem Transition_phase2_A_from_plus
    (s t : AgentState L K)
    (hs_phase : s.phase.val = 2) (ht_phase : t.phase.val = 2)
    (hs_plus : hasPlusOne s.opinions = true)
    (hs_minus : hasMinusOne s.opinions = false)
    (ht_minus : hasMinusOne t.opinions = false) :
    ((Transition L K s t).1.phase.val = 2 ∧
      (Transition L K s t).1.output = .A ∧
      hasPlusOne (Transition L K s t).1.opinions = true ∧
      hasMinusOne (Transition L K s t).1.opinions = false) ∧
    ((Transition L K s t).2.phase.val = 2 ∧
      (Transition L K s t).2.output = .A ∧
      hasPlusOne (Transition L K s t).2.opinions = true ∧
      hasMinusOne (Transition L K s t).2.opinions = false) := by
  have hs_phase_eq := phase_eq_two (L := L) (K := K) s hs_phase
  have ht_phase_eq := phase_eq_two (L := L) (K := K) t ht_phase
  have hepidemic := phaseEpidemicUpdate_eq_self_of_phase2 (L := L) (K := K)
    s t hs_phase_eq ht_phase_eq
  have hplus_union :
      hasPlusOne (opinionsUnion s.opinions t.opinions) = true :=
    hasPlusOne_opinionsUnion_true_left s.opinions t.opinions hs_plus
  have hminus_union :
      hasMinusOne (opinionsUnion s.opinions t.opinions) = false :=
    hasMinusOne_opinionsUnion_false s.opinions t.opinions hs_minus ht_minus
  simp [Transition, hepidemic, hs_phase_eq, ht_phase_eq, Phase2Transition,
    hplus_union, hminus_union]
  all_goals
    try rw [finishPhase10Entry_eq_self_of_after_ne_10]
    simp [finishPhase10Entry, canonicalPhase10Entry, hplus_union, hminus_union]

theorem Transition_phase2_B_from_minus
    (s t : AgentState L K)
    (hs_phase : s.phase.val = 2) (ht_phase : t.phase.val = 2)
    (hs_minus : hasMinusOne s.opinions = true)
    (hs_plus : hasPlusOne s.opinions = false)
    (ht_plus : hasPlusOne t.opinions = false) :
    ((Transition L K s t).1.phase.val = 2 ∧
      (Transition L K s t).1.output = .B ∧
      hasMinusOne (Transition L K s t).1.opinions = true ∧
      hasPlusOne (Transition L K s t).1.opinions = false) ∧
    ((Transition L K s t).2.phase.val = 2 ∧
      (Transition L K s t).2.output = .B ∧
      hasMinusOne (Transition L K s t).2.opinions = true ∧
      hasPlusOne (Transition L K s t).2.opinions = false) := by
  have hs_phase_eq := phase_eq_two (L := L) (K := K) s hs_phase
  have ht_phase_eq := phase_eq_two (L := L) (K := K) t ht_phase
  have hepidemic := phaseEpidemicUpdate_eq_self_of_phase2 (L := L) (K := K)
    s t hs_phase_eq ht_phase_eq
  have hminus_union :
      hasMinusOne (opinionsUnion s.opinions t.opinions) = true :=
    hasMinusOne_opinionsUnion_true_left s.opinions t.opinions hs_minus
  have hplus_union :
      hasPlusOne (opinionsUnion s.opinions t.opinions) = false :=
    hasPlusOne_opinionsUnion_false s.opinions t.opinions hs_plus ht_plus
  simp [Transition, hepidemic, hs_phase_eq, ht_phase_eq, Phase2Transition,
    hplus_union, hminus_union]
  all_goals
    try rw [finishPhase10Entry_eq_self_of_after_ne_10]
    simp [finishPhase10Entry, canonicalPhase10Entry, hplus_union, hminus_union]

private theorem phase2_A_carrier_step
    (c : Config (AgentState L K)) (g b : AgentState L K)
    (hphase : ∀ a ∈ c, a.phase.val = 2)
    (hnoMinus : ∀ a ∈ c, hasMinusOne a.opinions = false)
    (hg_mem : g ∈ c) (hb_mem : b ∈ c)
    (hg : phase2GoodA (L := L) (K := K) g)
    (hb_bad : ¬ phase2GoodA (L := L) (K := K) b) :
    let c' := Protocol.stepOrSelf (NonuniformMajority L K) c g b
    (NonuniformMajority L K).Reachable c c' ∧
      (∀ a ∈ c', a.phase.val = 2) ∧
      (∀ a ∈ c', hasMinusOne a.opinions = false) ∧
      (∃ g' ∈ c', phase2GoodA (L := L) (K := K) g') ∧
      phase2WrongACount (L := L) (K := K) c' <
        phase2WrongACount (L := L) (K := K) c := by
  classical
  intro c'
  have hne : g ≠ b := by
    intro h
    subst b
    exact hb_bad hg
  have happ : Protocol.Applicable c g b :=
    pair_le_of_mem_ne hg_mem hb_mem hne
  have hb_phase : b.phase.val = 2 := hphase b hb_mem
  have hb_minus : hasMinusOne b.opinions = false := hnoMinus b hb_mem
  have htrans := Transition_phase2_A_carrier_closes (L := L) (K := K) g b
    hg.1 hb_phase hg.2.1 hg.2.2.1 hg.2.2.2 hb_minus
  have hstep :
      c' =
        c - ({g, b} : Multiset (AgentState L K)) +
          ({(Transition L K g b).1, (Transition L K g b).2} :
            Multiset (AgentState L K)) := by
    unfold c' Protocol.stepOrSelf
    rw [if_pos happ]
    rfl
  refine ⟨Protocol.reachable_stepOrSelf c g b, ?_, ?_, ?_, ?_⟩
  · intro a ha
    rw [hstep] at ha
    simp only [Multiset.mem_add, Multiset.mem_cons, Multiset.mem_singleton] at ha
    rcases ha with ha_old | ha_new
    · have ha_c : a ∈ c :=
        Multiset.mem_of_le (Multiset.sub_le_self c ({g, b} :
          Multiset (AgentState L K))) ha_old
      by_cases hag : a = g
      · simpa [hag] using hg.1
      · by_cases hab : a = b
        · simpa [hab] using hb_phase
        · exact hphase a ha_c
    · have ha_new' :
          a = (Transition L K g b).1 ∨ a = (Transition L K g b).2 := by
        simpa using ha_new
      rcases ha_new' with h_eq1 | h_eq2
      · simpa [h_eq1] using htrans.1.1
      · simpa [h_eq2] using htrans.2.1
  · intro a ha
    rw [hstep] at ha
    simp only [Multiset.mem_add, Multiset.mem_cons, Multiset.mem_singleton] at ha
    rcases ha with ha_old | ha_new
    · have ha_c : a ∈ c :=
        Multiset.mem_of_le (Multiset.sub_le_self c ({g, b} :
          Multiset (AgentState L K))) ha_old
      by_cases hag : a = g
      · simpa [hag] using hg.2.2.2
      · by_cases hab : a = b
        · simpa [hab] using hb_minus
        · exact hnoMinus a ha_c
    · have ha_new' :
          a = (Transition L K g b).1 ∨ a = (Transition L K g b).2 := by
        simpa using ha_new
      rcases ha_new' with h_eq1 | h_eq2
      · simpa [h_eq1] using htrans.1.2.2.2
      · simpa [h_eq2] using htrans.2.2.2.2
  · refine ⟨(Transition L K g b).1, ?_, ?_⟩
    · rw [hstep]
      simp
    · exact htrans.1
  · have hpair :
        Multiset.countP
            (fun a : AgentState L K => ¬ phase2GoodA (L := L) (K := K) a)
            ({g, b} : Multiset (AgentState L K)) = 1 := by
      rw [show ({g, b} : Multiset (AgentState L K)) =
          ({g} : Multiset _) + {b} by rfl,
        Multiset.countP_add,
        countP_singleton_of_not
          (p := fun a : AgentState L K => ¬ phase2GoodA (L := L) (K := K) a)
          (by simpa using hg),
        countP_singleton_of
          (p := fun a : AgentState L K => ¬ phase2GoodA (L := L) (K := K) a)
          hb_bad]
    have hout :
        Multiset.countP
            (fun a : AgentState L K => ¬ phase2GoodA (L := L) (K := K) a)
            ({(Transition L K g b).1, (Transition L K g b).2} :
              Multiset (AgentState L K)) = 0 := by
      rw [show ({(Transition L K g b).1, (Transition L K g b).2} :
          Multiset (AgentState L K)) =
            ({(Transition L K g b).1} : Multiset _) +
              {(Transition L K g b).2} by rfl,
        Multiset.countP_add,
        countP_singleton_of_not
          (p := fun a : AgentState L K => ¬ phase2GoodA (L := L) (K := K) a)
          (by simpa using htrans.1),
        countP_singleton_of_not
          (p := fun a : AgentState L K => ¬ phase2GoodA (L := L) (K := K) a)
          (by simpa using htrans.2)]
    rw [hstep]
    unfold phase2WrongACount
    rw [Multiset.countP_add,
      Multiset.countP_sub happ
        (fun a : AgentState L K => ¬ phase2GoodA (L := L) (K := K) a)]
    rw [hpair, hout]
    have hpos :
        0 < Multiset.countP
          (fun a : AgentState L K => ¬ phase2GoodA (L := L) (K := K) a) c := by
      have hle := Multiset.countP_le_of_le
        (p := fun a : AgentState L K => ¬ phase2GoodA (L := L) (K := K) a) happ
      omega
    omega

theorem phase2_output_closure_A
    (c : Config (AgentState L K))
    (hphase : ∀ a ∈ c, a.phase.val = 2)
    (hnoMinus : ∀ a ∈ c, hasMinusOne a.opinions = false)
    (hcarrier : ∃ a ∈ c, a.output = .A ∧ hasPlusOne a.opinions = true) :
    ∃ final, (NonuniformMajority L K).Reachable c final ∧
      (∀ a ∈ final, a.phase.val = 2 ∧ a.output = .A ∧
        hasPlusOne a.opinions = true ∧ hasMinusOne a.opinions = false) := by
  classical
  have hcarrier_good : ∃ a ∈ c, phase2GoodA (L := L) (K := K) a := by
    rcases hcarrier with ⟨a, ha, hout, hplus⟩
    exact ⟨a, ha, hphase a ha, hout, hplus, hnoMinus a ha⟩
  let n := phase2WrongACount (L := L) (K := K) c
  have main :
      ∀ n, ∀ c : Config (AgentState L K),
        phase2WrongACount (L := L) (K := K) c = n →
        (∀ a ∈ c, a.phase.val = 2) →
        (∀ a ∈ c, hasMinusOne a.opinions = false) →
        (∃ a ∈ c, phase2GoodA (L := L) (K := K) a) →
        ∃ final, (NonuniformMajority L K).Reachable c final ∧
          (∀ a ∈ final, phase2GoodA (L := L) (K := K) a) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro c hcount hphase_c hnoMinus_c hcarrier_c
      by_cases hdone : ∀ a ∈ c, phase2GoodA (L := L) (K := K) a
      · exact ⟨c, Relation.ReflTransGen.refl, hdone⟩
      · have hbad_exists :
            ∃ b ∈ c, ¬ phase2GoodA (L := L) (K := K) b := by
          by_contra hnone
          apply hdone
          intro a ha
          by_contra hbad
          exact hnone ⟨a, ha, hbad⟩
        rcases hbad_exists with ⟨b, hb_mem, hb_bad⟩
        rcases hcarrier_c with ⟨g, hg_mem, hg_good⟩
        let c' := Protocol.stepOrSelf (NonuniformMajority L K) c g b
        have hstep := phase2_A_carrier_step
          (L := L) (K := K) c g b hphase_c hnoMinus_c
          hg_mem hb_mem hg_good hb_bad
        have hcount_lt : phase2WrongACount (L := L) (K := K) c' < n := by
          simpa [c', hcount] using hstep.2.2.2.2
        rcases ih (phase2WrongACount (L := L) (K := K) c') hcount_lt
            c' rfl hstep.2.1 hstep.2.2.1 hstep.2.2.2.1 with
          ⟨final, hreach_final, hgood_final⟩
        exact ⟨final, Relation.ReflTransGen.trans hstep.1 hreach_final, hgood_final⟩
  rcases main n c rfl hphase hnoMinus hcarrier_good with
    ⟨final, hreach, hgood⟩
  exact ⟨final, hreach, by
    intro a ha
    exact hgood a ha⟩

private theorem phase2_B_carrier_step
    (c : Config (AgentState L K)) (g b : AgentState L K)
    (hphase : ∀ a ∈ c, a.phase.val = 2)
    (hnoPlus : ∀ a ∈ c, hasPlusOne a.opinions = false)
    (hg_mem : g ∈ c) (hb_mem : b ∈ c)
    (hg : phase2GoodB (L := L) (K := K) g)
    (hb_bad : ¬ phase2GoodB (L := L) (K := K) b) :
    let c' := Protocol.stepOrSelf (NonuniformMajority L K) c g b
    (NonuniformMajority L K).Reachable c c' ∧
      (∀ a ∈ c', a.phase.val = 2) ∧
      (∀ a ∈ c', hasPlusOne a.opinions = false) ∧
      (∃ g' ∈ c', phase2GoodB (L := L) (K := K) g') ∧
      phase2WrongBCount (L := L) (K := K) c' <
        phase2WrongBCount (L := L) (K := K) c := by
  classical
  intro c'
  have hne : g ≠ b := by
    intro h
    subst b
    exact hb_bad hg
  have happ : Protocol.Applicable c g b :=
    pair_le_of_mem_ne hg_mem hb_mem hne
  have hb_phase : b.phase.val = 2 := hphase b hb_mem
  have hb_plus : hasPlusOne b.opinions = false := hnoPlus b hb_mem
  have htrans := Transition_phase2_B_carrier_closes (L := L) (K := K) g b
    hg.1 hb_phase hg.2.1 hg.2.2.1 hg.2.2.2 hb_plus
  have hstep :
      c' =
        c - ({g, b} : Multiset (AgentState L K)) +
          ({(Transition L K g b).1, (Transition L K g b).2} :
            Multiset (AgentState L K)) := by
    unfold c' Protocol.stepOrSelf
    rw [if_pos happ]
    rfl
  refine ⟨Protocol.reachable_stepOrSelf c g b, ?_, ?_, ?_, ?_⟩
  · intro a ha
    rw [hstep] at ha
    simp only [Multiset.mem_add, Multiset.mem_cons, Multiset.mem_singleton] at ha
    rcases ha with ha_old | ha_new
    · have ha_c : a ∈ c :=
        Multiset.mem_of_le (Multiset.sub_le_self c ({g, b} :
          Multiset (AgentState L K))) ha_old
      by_cases hag : a = g
      · simpa [hag] using hg.1
      · by_cases hab : a = b
        · simpa [hab] using hb_phase
        · exact hphase a ha_c
    · have ha_new' :
          a = (Transition L K g b).1 ∨ a = (Transition L K g b).2 := by
        simpa using ha_new
      rcases ha_new' with h_eq1 | h_eq2
      · simpa [h_eq1] using htrans.1.1
      · simpa [h_eq2] using htrans.2.1
  · intro a ha
    rw [hstep] at ha
    simp only [Multiset.mem_add, Multiset.mem_cons, Multiset.mem_singleton] at ha
    rcases ha with ha_old | ha_new
    · have ha_c : a ∈ c :=
        Multiset.mem_of_le (Multiset.sub_le_self c ({g, b} :
          Multiset (AgentState L K))) ha_old
      by_cases hag : a = g
      · simpa [hag] using hg.2.2.2
      · by_cases hab : a = b
        · simpa [hab] using hb_plus
        · exact hnoPlus a ha_c
    · have ha_new' :
          a = (Transition L K g b).1 ∨ a = (Transition L K g b).2 := by
        simpa using ha_new
      rcases ha_new' with h_eq1 | h_eq2
      · simpa [h_eq1] using htrans.1.2.2.2
      · simpa [h_eq2] using htrans.2.2.2.2
  · refine ⟨(Transition L K g b).1, ?_, ?_⟩
    · rw [hstep]
      simp
    · exact htrans.1
  · have hpair :
        Multiset.countP
            (fun a : AgentState L K => ¬ phase2GoodB (L := L) (K := K) a)
            ({g, b} : Multiset (AgentState L K)) = 1 := by
      rw [show ({g, b} : Multiset (AgentState L K)) =
          ({g} : Multiset _) + {b} by rfl,
        Multiset.countP_add,
        countP_singleton_of_not
          (p := fun a : AgentState L K => ¬ phase2GoodB (L := L) (K := K) a)
          (by simpa using hg),
        countP_singleton_of
          (p := fun a : AgentState L K => ¬ phase2GoodB (L := L) (K := K) a)
          hb_bad]
    have hout :
        Multiset.countP
            (fun a : AgentState L K => ¬ phase2GoodB (L := L) (K := K) a)
            ({(Transition L K g b).1, (Transition L K g b).2} :
              Multiset (AgentState L K)) = 0 := by
      rw [show ({(Transition L K g b).1, (Transition L K g b).2} :
          Multiset (AgentState L K)) =
            ({(Transition L K g b).1} : Multiset _) +
              {(Transition L K g b).2} by rfl,
        Multiset.countP_add,
        countP_singleton_of_not
          (p := fun a : AgentState L K => ¬ phase2GoodB (L := L) (K := K) a)
          (by simpa using htrans.1),
        countP_singleton_of_not
          (p := fun a : AgentState L K => ¬ phase2GoodB (L := L) (K := K) a)
          (by simpa using htrans.2)]
    rw [hstep]
    unfold phase2WrongBCount
    rw [Multiset.countP_add,
      Multiset.countP_sub happ
        (fun a : AgentState L K => ¬ phase2GoodB (L := L) (K := K) a)]
    rw [hpair, hout]
    have hpos :
        0 < Multiset.countP
          (fun a : AgentState L K => ¬ phase2GoodB (L := L) (K := K) a) c := by
      have hle := Multiset.countP_le_of_le
        (p := fun a : AgentState L K => ¬ phase2GoodB (L := L) (K := K) a) happ
      omega
    omega

theorem phase2_output_closure_B
    (c : Config (AgentState L K))
    (hphase : ∀ a ∈ c, a.phase.val = 2)
    (hnoPlus : ∀ a ∈ c, hasPlusOne a.opinions = false)
    (hcarrier : ∃ a ∈ c, a.output = .B ∧ hasMinusOne a.opinions = true) :
    ∃ final, (NonuniformMajority L K).Reachable c final ∧
      (∀ a ∈ final, a.phase.val = 2 ∧ a.output = .B ∧
        hasMinusOne a.opinions = true ∧ hasPlusOne a.opinions = false) := by
  classical
  have hcarrier_good : ∃ a ∈ c, phase2GoodB (L := L) (K := K) a := by
    rcases hcarrier with ⟨a, ha, hout, hminus⟩
    exact ⟨a, ha, hphase a ha, hout, hminus, hnoPlus a ha⟩
  let n := phase2WrongBCount (L := L) (K := K) c
  have main :
      ∀ n, ∀ c : Config (AgentState L K),
        phase2WrongBCount (L := L) (K := K) c = n →
        (∀ a ∈ c, a.phase.val = 2) →
        (∀ a ∈ c, hasPlusOne a.opinions = false) →
        (∃ a ∈ c, phase2GoodB (L := L) (K := K) a) →
        ∃ final, (NonuniformMajority L K).Reachable c final ∧
          (∀ a ∈ final, phase2GoodB (L := L) (K := K) a) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro c hcount hphase_c hnoPlus_c hcarrier_c
      by_cases hdone : ∀ a ∈ c, phase2GoodB (L := L) (K := K) a
      · exact ⟨c, Relation.ReflTransGen.refl, hdone⟩
      · have hbad_exists :
            ∃ b ∈ c, ¬ phase2GoodB (L := L) (K := K) b := by
          by_contra hnone
          apply hdone
          intro a ha
          by_contra hbad
          exact hnone ⟨a, ha, hbad⟩
        rcases hbad_exists with ⟨b, hb_mem, hb_bad⟩
        rcases hcarrier_c with ⟨g, hg_mem, hg_good⟩
        let c' := Protocol.stepOrSelf (NonuniformMajority L K) c g b
        have hstep := phase2_B_carrier_step
          (L := L) (K := K) c g b hphase_c hnoPlus_c
          hg_mem hb_mem hg_good hb_bad
        have hcount_lt : phase2WrongBCount (L := L) (K := K) c' < n := by
          simpa [c', hcount] using hstep.2.2.2.2
        rcases ih (phase2WrongBCount (L := L) (K := K) c') hcount_lt
            c' rfl hstep.2.1 hstep.2.2.1 hstep.2.2.2.1 with
          ⟨final, hreach_final, hgood_final⟩
        exact ⟨final, Relation.ReflTransGen.trans hstep.1 hreach_final, hgood_final⟩
  rcases main n c rfl hphase hnoPlus hcarrier_good with
    ⟨final, hreach, hgood⟩
  exact ⟨final, hreach, by
    intro a ha
    exact hgood a ha⟩

theorem phase2_output_closure_A_from_plus
    (c : Config (AgentState L K))
    (hphase : ∀ a ∈ c, a.phase.val = 2)
    (hnoMinus : ∀ a ∈ c, hasMinusOne a.opinions = false)
    (hplus : ∃ a ∈ c, hasPlusOne a.opinions = true)
    (hcard : 2 ≤ c.card) :
    ∃ final, (NonuniformMajority L K).Reachable c final ∧
      (∀ a ∈ final, a.phase.val = 2 ∧ a.output = .A ∧
        hasPlusOne a.opinions = true ∧ hasMinusOne a.opinions = false) := by
  classical
  rcases hplus with ⟨a, ha, ha_plus⟩
  by_cases ha_out : a.output = .A
  · exact phase2_output_closure_A (L := L) (K := K) c hphase hnoMinus
      ⟨a, ha, ha_out, ha_plus⟩
  · rcases exists_applicable_pair_left_of_mem_card_ge_two
      (L := L) (K := K) ha hcard with ⟨b, happ⟩
    let c' := Protocol.stepOrSelf (NonuniformMajority L K) c a b
    have hb : b ∈ c := Multiset.mem_of_le happ (by simp)
    have htrans := Transition_phase2_A_from_plus (L := L) (K := K) a b
      (hphase a ha) (hphase b hb) ha_plus (hnoMinus a ha) (hnoMinus b hb)
    have hstep :
        c' =
          c - ({a, b} : Multiset (AgentState L K)) +
            ({(Transition L K a b).1, (Transition L K a b).2} :
              Multiset (AgentState L K)) := by
      unfold c' Protocol.stepOrSelf
      rw [if_pos happ]
      rfl
    have hphase' : ∀ x ∈ c', x.phase.val = 2 := by
      intro x hx
      rw [hstep] at hx
      simp only [Multiset.mem_add, Multiset.mem_cons, Multiset.mem_singleton] at hx
      rcases hx with hx_old | hx_new
      · exact hphase x (Multiset.mem_of_le
          (Multiset.sub_le_self c ({a, b} : Multiset (AgentState L K))) hx_old)
      · have hx_new' :
            x = (Transition L K a b).1 ∨ x = (Transition L K a b).2 := by
          simpa using hx_new
        rcases hx_new' with h_eq1 | h_eq2
        · simpa [h_eq1] using htrans.1.1
        · simpa [h_eq2] using htrans.2.1
    have hnoMinus' : ∀ x ∈ c', hasMinusOne x.opinions = false := by
      intro x hx
      rw [hstep] at hx
      simp only [Multiset.mem_add, Multiset.mem_cons, Multiset.mem_singleton] at hx
      rcases hx with hx_old | hx_new
      · exact hnoMinus x (Multiset.mem_of_le
          (Multiset.sub_le_self c ({a, b} : Multiset (AgentState L K))) hx_old)
      · have hx_new' :
            x = (Transition L K a b).1 ∨ x = (Transition L K a b).2 := by
          simpa using hx_new
        rcases hx_new' with h_eq1 | h_eq2
        · simpa [h_eq1] using htrans.1.2.2.2
        · simpa [h_eq2] using htrans.2.2.2.2
    have hcarrier' :
        ∃ x ∈ c', x.output = .A ∧ hasPlusOne x.opinions = true := by
      refine ⟨(Transition L K a b).1, ?_, htrans.1.2.1, htrans.1.2.2.1⟩
      rw [hstep]
      simp
    rcases phase2_output_closure_A (L := L) (K := K) c'
        hphase' hnoMinus' hcarrier' with ⟨final, hreach, hgood⟩
    exact ⟨final, Relation.ReflTransGen.trans
      (Protocol.reachable_stepOrSelf c a b) hreach, hgood⟩

theorem phase2_output_closure_B_from_minus
    (c : Config (AgentState L K))
    (hphase : ∀ a ∈ c, a.phase.val = 2)
    (hnoPlus : ∀ a ∈ c, hasPlusOne a.opinions = false)
    (hminus : ∃ a ∈ c, hasMinusOne a.opinions = true)
    (hcard : 2 ≤ c.card) :
    ∃ final, (NonuniformMajority L K).Reachable c final ∧
      (∀ a ∈ final, a.phase.val = 2 ∧ a.output = .B ∧
        hasMinusOne a.opinions = true ∧ hasPlusOne a.opinions = false) := by
  classical
  rcases hminus with ⟨a, ha, ha_minus⟩
  by_cases ha_out : a.output = .B
  · exact phase2_output_closure_B (L := L) (K := K) c hphase hnoPlus
      ⟨a, ha, ha_out, ha_minus⟩
  · rcases exists_applicable_pair_left_of_mem_card_ge_two
      (L := L) (K := K) ha hcard with ⟨b, happ⟩
    let c' := Protocol.stepOrSelf (NonuniformMajority L K) c a b
    have hb : b ∈ c := Multiset.mem_of_le happ (by simp)
    have htrans := Transition_phase2_B_from_minus (L := L) (K := K) a b
      (hphase a ha) (hphase b hb) ha_minus (hnoPlus a ha) (hnoPlus b hb)
    have hstep :
        c' =
          c - ({a, b} : Multiset (AgentState L K)) +
            ({(Transition L K a b).1, (Transition L K a b).2} :
              Multiset (AgentState L K)) := by
      unfold c' Protocol.stepOrSelf
      rw [if_pos happ]
      rfl
    have hphase' : ∀ x ∈ c', x.phase.val = 2 := by
      intro x hx
      rw [hstep] at hx
      simp only [Multiset.mem_add, Multiset.mem_cons, Multiset.mem_singleton] at hx
      rcases hx with hx_old | hx_new
      · exact hphase x (Multiset.mem_of_le
          (Multiset.sub_le_self c ({a, b} : Multiset (AgentState L K))) hx_old)
      · have hx_new' :
            x = (Transition L K a b).1 ∨ x = (Transition L K a b).2 := by
          simpa using hx_new
        rcases hx_new' with h_eq1 | h_eq2
        · simpa [h_eq1] using htrans.1.1
        · simpa [h_eq2] using htrans.2.1
    have hnoPlus' : ∀ x ∈ c', hasPlusOne x.opinions = false := by
      intro x hx
      rw [hstep] at hx
      simp only [Multiset.mem_add, Multiset.mem_cons, Multiset.mem_singleton] at hx
      rcases hx with hx_old | hx_new
      · exact hnoPlus x (Multiset.mem_of_le
          (Multiset.sub_le_self c ({a, b} : Multiset (AgentState L K))) hx_old)
      · have hx_new' :
            x = (Transition L K a b).1 ∨ x = (Transition L K a b).2 := by
          simpa using hx_new
        rcases hx_new' with h_eq1 | h_eq2
        · simpa [h_eq1] using htrans.1.2.2.2
        · simpa [h_eq2] using htrans.2.2.2.2
    have hcarrier' :
        ∃ x ∈ c', x.output = .B ∧ hasMinusOne x.opinions = true := by
      refine ⟨(Transition L K a b).1, ?_, htrans.1.2.1, htrans.1.2.2.1⟩
      rw [hstep]
      simp
    rcases phase2_output_closure_B (L := L) (K := K) c'
        hphase' hnoPlus' hcarrier' with ⟨final, hreach, hgood⟩
    exact ⟨final, Relation.ReflTransGen.trans
      (Protocol.reachable_stepOrSelf c a b) hreach, hgood⟩

private theorem phase2_T_carrier_step
    (c : Config (AgentState L K)) (g b : AgentState L K)
    (hphase : ∀ a ∈ c, a.phase.val = 2)
    (hop : ∀ a ∈ c, a.opinions = phase2OpinionT)
    (hg_mem : g ∈ c) (hb_mem : b ∈ c)
    (hg : phase2GoodT (L := L) (K := K) g)
    (hb_bad : ¬ phase2GoodT (L := L) (K := K) b) :
    let c' := Protocol.stepOrSelf (NonuniformMajority L K) c g b
    (NonuniformMajority L K).Reachable c c' ∧
      (∀ a ∈ c', a.phase.val = 2) ∧
      (∀ a ∈ c', a.opinions = phase2OpinionT) ∧
      (∃ g' ∈ c', phase2GoodT (L := L) (K := K) g') ∧
      phase2WrongTCount (L := L) (K := K) c' <
        phase2WrongTCount (L := L) (K := K) c := by
  classical
  intro c'
  have hne : g ≠ b := by
    intro h
    subst b
    exact hb_bad hg
  have happ : Protocol.Applicable c g b :=
    pair_le_of_mem_ne hg_mem hb_mem hne
  have hb_phase : b.phase.val = 2 := hphase b hb_mem
  have hb_op : b.opinions = phase2OpinionT := hop b hb_mem
  have htrans := Transition_preserves_phase2_T (L := L) (K := K) g b
    hg.1 hb_phase hg.2.2 hb_op
  have hstep :
      c' =
        c - ({g, b} : Multiset (AgentState L K)) +
          ({(Transition L K g b).1, (Transition L K g b).2} :
            Multiset (AgentState L K)) := by
    unfold c' Protocol.stepOrSelf
    rw [if_pos happ]
    rfl
  refine ⟨Protocol.reachable_stepOrSelf c g b, ?_, ?_, ?_, ?_⟩
  · intro a ha
    rw [hstep] at ha
    simp only [Multiset.mem_add, Multiset.mem_cons, Multiset.mem_singleton] at ha
    rcases ha with ha_old | ha_new
    · exact hphase a (Multiset.mem_of_le
        (Multiset.sub_le_self c ({g, b} : Multiset (AgentState L K))) ha_old)
    · have ha_new' :
          a = (Transition L K g b).1 ∨ a = (Transition L K g b).2 := by
        simpa using ha_new
      rcases ha_new' with h_eq1 | h_eq2
      · simpa [h_eq1] using htrans.1.1
      · simpa [h_eq2] using htrans.2.1
  · intro a ha
    rw [hstep] at ha
    simp only [Multiset.mem_add, Multiset.mem_cons, Multiset.mem_singleton] at ha
    rcases ha with ha_old | ha_new
    · exact hop a (Multiset.mem_of_le
        (Multiset.sub_le_self c ({g, b} : Multiset (AgentState L K))) ha_old)
    · have ha_new' :
          a = (Transition L K g b).1 ∨ a = (Transition L K g b).2 := by
        simpa using ha_new
      rcases ha_new' with h_eq1 | h_eq2
      · simpa [h_eq1] using htrans.1.2.1
      · simpa [h_eq2] using htrans.2.2.1
  · refine ⟨(Transition L K g b).1, ?_, ?_⟩
    · rw [hstep]
      simp
    · exact ⟨htrans.1.1, htrans.1.2.2, htrans.1.2.1⟩
  · have hpair :
        Multiset.countP
            (fun a : AgentState L K => ¬ phase2GoodT (L := L) (K := K) a)
            ({g, b} : Multiset (AgentState L K)) = 1 := by
      rw [show ({g, b} : Multiset (AgentState L K)) =
          ({g} : Multiset _) + {b} by rfl,
        Multiset.countP_add,
        countP_singleton_of_not
          (p := fun a : AgentState L K => ¬ phase2GoodT (L := L) (K := K) a)
          (by simpa using hg),
        countP_singleton_of
          (p := fun a : AgentState L K => ¬ phase2GoodT (L := L) (K := K) a)
          hb_bad]
    have hout :
        Multiset.countP
            (fun a : AgentState L K => ¬ phase2GoodT (L := L) (K := K) a)
            ({(Transition L K g b).1, (Transition L K g b).2} :
              Multiset (AgentState L K)) = 0 := by
      rw [show ({(Transition L K g b).1, (Transition L K g b).2} :
          Multiset (AgentState L K)) =
            ({(Transition L K g b).1} : Multiset _) +
              {(Transition L K g b).2} by rfl,
        Multiset.countP_add,
        countP_singleton_of_not
          (p := fun a : AgentState L K => ¬ phase2GoodT (L := L) (K := K) a)
          (by
            intro hbad
            exact hbad ⟨htrans.1.1, htrans.1.2.2, htrans.1.2.1⟩),
        countP_singleton_of_not
          (p := fun a : AgentState L K => ¬ phase2GoodT (L := L) (K := K) a)
          (by
            intro hbad
            exact hbad ⟨htrans.2.1, htrans.2.2.2, htrans.2.2.1⟩)]
    rw [hstep]
    unfold phase2WrongTCount
    rw [Multiset.countP_add,
      Multiset.countP_sub happ
        (fun a : AgentState L K => ¬ phase2GoodT (L := L) (K := K) a)]
    rw [hpair, hout]
    have hpos :
        0 < Multiset.countP
          (fun a : AgentState L K => ¬ phase2GoodT (L := L) (K := K) a) c := by
      have hle := Multiset.countP_le_of_le
        (p := fun a : AgentState L K => ¬ phase2GoodT (L := L) (K := K) a) happ
      omega
    omega

private theorem phase2_output_closure_T_with_carrier
    (c : Config (AgentState L K))
    (hphase : ∀ a ∈ c, a.phase.val = 2)
    (hop : ∀ a ∈ c, a.opinions = phase2OpinionT)
    (hcarrier : ∃ a ∈ c, phase2GoodT (L := L) (K := K) a) :
    ∃ final, (NonuniformMajority L K).Reachable c final ∧
      (∀ a ∈ final, phase2GoodT (L := L) (K := K) a) := by
  classical
  let n := phase2WrongTCount (L := L) (K := K) c
  have main :
      ∀ n, ∀ c : Config (AgentState L K),
        phase2WrongTCount (L := L) (K := K) c = n →
        (∀ a ∈ c, a.phase.val = 2) →
        (∀ a ∈ c, a.opinions = phase2OpinionT) →
        (∃ a ∈ c, phase2GoodT (L := L) (K := K) a) →
        ∃ final, (NonuniformMajority L K).Reachable c final ∧
          (∀ a ∈ final, phase2GoodT (L := L) (K := K) a) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro c hcount hphase_c hop_c hcarrier_c
      by_cases hdone : ∀ a ∈ c, phase2GoodT (L := L) (K := K) a
      · exact ⟨c, Relation.ReflTransGen.refl, hdone⟩
      · have hbad_exists :
            ∃ b ∈ c, ¬ phase2GoodT (L := L) (K := K) b := by
          by_contra hnone
          apply hdone
          intro a ha
          by_contra hbad
          exact hnone ⟨a, ha, hbad⟩
        rcases hbad_exists with ⟨b, hb_mem, hb_bad⟩
        rcases hcarrier_c with ⟨g, hg_mem, hg_good⟩
        let c' := Protocol.stepOrSelf (NonuniformMajority L K) c g b
        have hstep := phase2_T_carrier_step
          (L := L) (K := K) c g b hphase_c hop_c
          hg_mem hb_mem hg_good hb_bad
        have hcount_lt : phase2WrongTCount (L := L) (K := K) c' < n := by
          simpa [c', hcount] using hstep.2.2.2.2
        rcases ih (phase2WrongTCount (L := L) (K := K) c') hcount_lt
            c' rfl hstep.2.1 hstep.2.2.1 hstep.2.2.2.1 with
          ⟨final, hreach_final, hgood_final⟩
        exact ⟨final, Relation.ReflTransGen.trans hstep.1 hreach_final, hgood_final⟩
  exact main n c rfl hphase hop hcarrier

theorem phase2_output_closure_T
    (c : Config (AgentState L K))
    (hphase : ∀ a ∈ c, a.phase.val = 2)
    (hop : ∀ a ∈ c, a.opinions = phase2OpinionT)
    (hcard : 2 ≤ c.card) :
    ∃ final, (NonuniformMajority L K).Reachable c final ∧
      (∀ a ∈ final, a.phase.val = 2 ∧ a.output = .T ∧
        hasMinusOne a.opinions = false ∧ hasPlusOne a.opinions = false) := by
  classical
  have hmem : ∃ a, a ∈ c := by
    exact Multiset.card_pos_iff_exists_mem.mp (by omega)
  rcases hmem with ⟨a, ha⟩
  by_cases ha_good : phase2GoodT (L := L) (K := K) a
  · rcases phase2_output_closure_T_with_carrier (L := L) (K := K) c
        hphase hop ⟨a, ha, ha_good⟩ with ⟨final, hreach, hgood⟩
    exact ⟨final, hreach, by
      intro x hx
      rcases hgood x hx with ⟨hph, hout, hopx⟩
      exact ⟨hph, hout, by simp [hopx, phase2OpinionT, hasMinusOne],
        by simp [hopx, phase2OpinionT, hasPlusOne]⟩⟩
  · rcases exists_applicable_pair_left_of_mem_card_ge_two
      (L := L) (K := K) ha hcard with ⟨b, happ⟩
    let c' := Protocol.stepOrSelf (NonuniformMajority L K) c a b
    have hb : b ∈ c := Multiset.mem_of_le happ (by simp)
    have htrans := Transition_preserves_phase2_T (L := L) (K := K) a b
      (hphase a ha) (hphase b hb) (hop a ha) (hop b hb)
    have hstep :
        c' =
          c - ({a, b} : Multiset (AgentState L K)) +
            ({(Transition L K a b).1, (Transition L K a b).2} :
              Multiset (AgentState L K)) := by
      unfold c' Protocol.stepOrSelf
      rw [if_pos happ]
      rfl
    have hphase' : ∀ x ∈ c', x.phase.val = 2 := by
      intro x hx
      rw [hstep] at hx
      simp only [Multiset.mem_add, Multiset.mem_cons, Multiset.mem_singleton] at hx
      rcases hx with hx_old | hx_new
      · exact hphase x (Multiset.mem_of_le
          (Multiset.sub_le_self c ({a, b} : Multiset (AgentState L K))) hx_old)
      · have hx_new' :
            x = (Transition L K a b).1 ∨ x = (Transition L K a b).2 := by
          simpa using hx_new
        rcases hx_new' with h_eq1 | h_eq2
        · simpa [h_eq1] using htrans.1.1
        · simpa [h_eq2] using htrans.2.1
    have hop' : ∀ x ∈ c', x.opinions = phase2OpinionT := by
      intro x hx
      rw [hstep] at hx
      simp only [Multiset.mem_add, Multiset.mem_cons, Multiset.mem_singleton] at hx
      rcases hx with hx_old | hx_new
      · exact hop x (Multiset.mem_of_le
          (Multiset.sub_le_self c ({a, b} : Multiset (AgentState L K))) hx_old)
      · have hx_new' :
            x = (Transition L K a b).1 ∨ x = (Transition L K a b).2 := by
          simpa using hx_new
        rcases hx_new' with h_eq1 | h_eq2
        · simpa [h_eq1] using htrans.1.2.1
        · simpa [h_eq2] using htrans.2.2.1
    have hcarrier' :
        ∃ x ∈ c', phase2GoodT (L := L) (K := K) x := by
      refine ⟨(Transition L K a b).1, ?_, ?_⟩
      · rw [hstep]
        simp
      · exact ⟨htrans.1.1, htrans.1.2.2, htrans.1.2.1⟩
    rcases phase2_output_closure_T_with_carrier (L := L) (K := K) c'
        hphase' hop' hcarrier' with ⟨final, hreach, hgood⟩
    exact ⟨final, Relation.ReflTransGen.trans
      (Protocol.reachable_stepOrSelf c a b) hreach, by
      intro x hx
      rcases hgood x hx with ⟨hph, hout, hopx⟩
      exact ⟨hph, hout, by simp [hopx, phase2OpinionT, hasMinusOne],
        by simp [hopx, phase2OpinionT, hasPlusOne]⟩⟩

private theorem phase2_A_signs_preserved_by_step
    (c c' : Config (AgentState L K))
    (h_c : phase2OutputAWithSigns (L := L) (K := K) c)
    (h_step : (NonuniformMajority L K).StepRel c c') :
    phase2OutputAWithSigns (L := L) (K := K) c' := by
  rcases h_step with ⟨r₁, r₂, happ, hc'⟩
  dsimp [Protocol.Applicable, NonuniformMajority] at happ hc'
  have hr₁_mem : r₁ ∈ c := Multiset.mem_of_le happ (by simp)
  have hr₂_mem : r₂ ∈ c := Multiset.mem_of_le happ (by simp)
  rcases h_c with ⟨hstable, hsigns⟩
  rcases hsigns r₁ hr₁_mem with ⟨hr₁_out, hr₁_plus, hr₁_minus⟩
  rcases hsigns r₂ hr₂_mem with ⟨hr₂_out, hr₂_plus, hr₂_minus⟩
  have htrans := Transition_preserves_phase2_A_signs (L := L) (K := K)
    r₁ r₂ (hstable.1 r₁ hr₁_mem) (hstable.1 r₂ hr₂_mem)
    hr₁_out hr₂_out hr₁_plus hr₂_plus hr₁_minus hr₂_minus
  rw [hc']
  let cnext :=
    c - ({r₁, r₂} : Multiset (AgentState L K)) +
      ({(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2} :
        Multiset (AgentState L K))
  have hdata : ∀ a ∈ cnext,
      a.phase.val = 2 ∧ a.output = .A ∧
        hasPlusOne a.opinions = true ∧ hasMinusOne a.opinions = false := by
    intro a ha
    simp only [cnext, Multiset.mem_add, Multiset.mem_cons,
      Multiset.mem_singleton] at ha
    rcases ha with h_old | h_new
    · have ha_c : a ∈ c :=
        Multiset.mem_of_le (Multiset.sub_le_self c ({r₁, r₂} :
          Multiset (AgentState L K))) h_old
      rcases hsigns a ha_c with ⟨hout, hplus, hminus⟩
      exact ⟨hstable.1 a ha_c, hout, hplus, hminus⟩
    · have hnew' :
          a = (Transition L K r₁ r₂).1 ∨
            a = (Transition L K r₁ r₂).2 := by
        simpa using h_new
      rcases hnew' with h_eq | h_eq
      · simpa [h_eq] using htrans.1
      · simpa [h_eq] using htrans.2
  refine ⟨?_, ?_⟩
  · refine ⟨fun a ha => (hdata a ha).1, ?_⟩
    intro a b hab hboth
    have ha := hdata a (Multiset.mem_of_le hab (by simp))
    have hb := hdata b (Multiset.mem_of_le hab (by simp))
    have hminus_union :=
      hasMinusOne_opinionsUnion_false a.opinions b.opinions ha.2.2.2 hb.2.2.2
    rw [hminus_union] at hboth
    simp at hboth
  · intro a ha
    exact (hdata a ha).2

private theorem phase2_B_signs_preserved_by_step
    (c c' : Config (AgentState L K))
    (h_c : phase2OutputBWithSigns (L := L) (K := K) c)
    (h_step : (NonuniformMajority L K).StepRel c c') :
    phase2OutputBWithSigns (L := L) (K := K) c' := by
  rcases h_step with ⟨r₁, r₂, happ, hc'⟩
  dsimp [Protocol.Applicable, NonuniformMajority] at happ hc'
  have hr₁_mem : r₁ ∈ c := Multiset.mem_of_le happ (by simp)
  have hr₂_mem : r₂ ∈ c := Multiset.mem_of_le happ (by simp)
  rcases h_c with ⟨hstable, hsigns⟩
  rcases hsigns r₁ hr₁_mem with ⟨hr₁_out, hr₁_minus, hr₁_plus⟩
  rcases hsigns r₂ hr₂_mem with ⟨hr₂_out, hr₂_minus, hr₂_plus⟩
  have htrans := Transition_preserves_phase2_B_signs (L := L) (K := K)
    r₁ r₂ (hstable.1 r₁ hr₁_mem) (hstable.1 r₂ hr₂_mem)
    hr₁_out hr₂_out hr₁_minus hr₂_minus hr₁_plus hr₂_plus
  rw [hc']
  let cnext :=
    c - ({r₁, r₂} : Multiset (AgentState L K)) +
      ({(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2} :
        Multiset (AgentState L K))
  have hdata : ∀ a ∈ cnext,
      a.phase.val = 2 ∧ a.output = .B ∧
        hasMinusOne a.opinions = true ∧ hasPlusOne a.opinions = false := by
    intro a ha
    simp only [cnext, Multiset.mem_add, Multiset.mem_cons,
      Multiset.mem_singleton] at ha
    rcases ha with h_old | h_new
    · have ha_c : a ∈ c :=
        Multiset.mem_of_le (Multiset.sub_le_self c ({r₁, r₂} :
          Multiset (AgentState L K))) h_old
      rcases hsigns a ha_c with ⟨hout, hminus, hplus⟩
      exact ⟨hstable.1 a ha_c, hout, hminus, hplus⟩
    · have hnew' :
          a = (Transition L K r₁ r₂).1 ∨
            a = (Transition L K r₁ r₂).2 := by
        simpa using h_new
      rcases hnew' with h_eq | h_eq
      · simpa [h_eq] using htrans.1
      · simpa [h_eq] using htrans.2
  refine ⟨?_, ?_⟩
  · refine ⟨fun a ha => (hdata a ha).1, ?_⟩
    intro a b hab hboth
    have ha := hdata a (Multiset.mem_of_le hab (by simp))
    have hb := hdata b (Multiset.mem_of_le hab (by simp))
    have hplus_union :=
      hasPlusOne_opinionsUnion_false a.opinions b.opinions ha.2.2.2 hb.2.2.2
    rw [hplus_union] at hboth
    simp at hboth
  · intro a ha
    exact (hdata a ha).2

private theorem phase2_T_signs_preserved_by_step
    (c c' : Config (AgentState L K))
    (h_c : phase2OutputTWithSigns (L := L) (K := K) c)
    (h_step : (NonuniformMajority L K).StepRel c c') :
    phase2OutputTWithSigns (L := L) (K := K) c' := by
  rcases h_step with ⟨r₁, r₂, happ, hc'⟩
  dsimp [Protocol.Applicable, NonuniformMajority] at happ hc'
  have hr₁_mem : r₁ ∈ c := Multiset.mem_of_le happ (by simp)
  have hr₂_mem : r₂ ∈ c := Multiset.mem_of_le happ (by simp)
  rcases h_c with ⟨hstable, hsigns⟩
  rcases hsigns r₁ hr₁_mem with ⟨hr₁_out, hr₁_minus, hr₁_plus⟩
  rcases hsigns r₂ hr₂_mem with ⟨hr₂_out, hr₂_minus, hr₂_plus⟩
  have htrans := Transition_preserves_phase2_T_signs (L := L) (K := K)
    r₁ r₂ (hstable.1 r₁ hr₁_mem) (hstable.1 r₂ hr₂_mem)
    hr₁_out hr₂_out hr₁_minus hr₂_minus hr₁_plus hr₂_plus
  rw [hc']
  let cnext :=
    c - ({r₁, r₂} : Multiset (AgentState L K)) +
      ({(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2} :
        Multiset (AgentState L K))
  have hdata : ∀ a ∈ cnext,
      a.phase.val = 2 ∧ a.output = .T ∧
        hasMinusOne a.opinions = false ∧ hasPlusOne a.opinions = false := by
    intro a ha
    simp only [cnext, Multiset.mem_add, Multiset.mem_cons,
      Multiset.mem_singleton] at ha
    rcases ha with h_old | h_new
    · have ha_c : a ∈ c :=
        Multiset.mem_of_le (Multiset.sub_le_self c ({r₁, r₂} :
          Multiset (AgentState L K))) h_old
      rcases hsigns a ha_c with ⟨hout, hminus, hplus⟩
      exact ⟨hstable.1 a ha_c, hout, hminus, hplus⟩
    · have hnew' :
          a = (Transition L K r₁ r₂).1 ∨
            a = (Transition L K r₁ r₂).2 := by
        simpa using h_new
      rcases hnew' with h_eq | h_eq
      · simpa [h_eq] using htrans.1
      · simpa [h_eq] using htrans.2
  refine ⟨?_, ?_⟩
  · refine ⟨fun a ha => (hdata a ha).1, ?_⟩
    intro a b hab hboth
    have ha := hdata a (Multiset.mem_of_le hab (by simp))
    have hb := hdata b (Multiset.mem_of_le hab (by simp))
    have hminus_union :=
      hasMinusOne_opinionsUnion_false a.opinions b.opinions ha.2.2.1 hb.2.2.1
    rw [hminus_union] at hboth
    simp at hboth
  · intro a ha
    exact (hdata a ha).2

private theorem phase2_A_signs_preserved_by_reachable
    (c c' : Config (AgentState L K))
    (h_c : phase2OutputAWithSigns (L := L) (K := K) c)
    (h_reach : (NonuniformMajority L K).Reachable c c') :
    phase2OutputAWithSigns (L := L) (K := K) c' := by
  induction h_reach with
  | refl => exact h_c
  | tail _ hstep ih =>
      exact phase2_A_signs_preserved_by_step (L := L) (K := K) _ _ ih hstep

private theorem phase2_B_signs_preserved_by_reachable
    (c c' : Config (AgentState L K))
    (h_c : phase2OutputBWithSigns (L := L) (K := K) c)
    (h_reach : (NonuniformMajority L K).Reachable c c') :
    phase2OutputBWithSigns (L := L) (K := K) c' := by
  induction h_reach with
  | refl => exact h_c
  | tail _ hstep ih =>
      exact phase2_B_signs_preserved_by_step (L := L) (K := K) _ _ ih hstep

private theorem phase2_T_signs_preserved_by_reachable
    (c c' : Config (AgentState L K))
    (h_c : phase2OutputTWithSigns (L := L) (K := K) c)
    (h_reach : (NonuniformMajority L K).Reachable c c') :
    phase2OutputTWithSigns (L := L) (K := K) c' := by
  induction h_reach with
  | refl => exact h_c
  | tail _ hstep ih =>
      exact phase2_T_signs_preserved_by_step (L := L) (K := K) _ _ ih hstep

private theorem doutPartition_output_of_phase2ConsensusWith
    (c : Config (AgentState L K)) (opinion : Fin 8) (out : Output)
    (h : phase2ConsensusWith (L := L) (K := K) opinion out c) :
    (doutPartition L K).output (outputTripleOfOutput out) c :=
  doutPartition_output_of_unanimous_output (L := L) (K := K) c out
    (fun a ha => (h a ha).2.2)

/-- A Phase-2 consensus endpoint has the majority-verdict output by definition
of the endpoint predicate. -/
theorem phase2ConsensusEndpoint_output
    (init c : Config (AgentState L K))
    (h : phase2ConsensusEndpoint (L := L) (K := K) init c) :
    (doutPartition L K).output (majorityVerdict init) c := by
  rcases h with ⟨hmaj, hc⟩ | ⟨hmaj, hc⟩ | ⟨hmaj, hc⟩
  · rw [hmaj]
    exact doutPartition_output_of_unanimous_output (L := L) (K := K) c .A
      (fun a ha => (hc.2 a ha).1)
  · rw [hmaj]
    exact doutPartition_output_of_unanimous_output (L := L) (K := K) c .B
      (fun a ha => (hc.2 a ha).1)
  · rw [hmaj]
    exact doutPartition_output_of_unanimous_output (L := L) (K := K) c .T
      (fun a ha => (hc.2 a ha).1)

/-- Phase-2 consensus endpoints are stable under all reachable executions of
the full nonuniform exact-majority protocol. -/
theorem phase2ConsensusEndpoint_isStable
    (init c : Config (AgentState L K))
    (h : phase2ConsensusEndpoint (L := L) (K := K) init c) :
    (NonuniformMajority L K).IsStable (doutPartition L K) c := by
  refine ⟨majorityVerdict init, phase2ConsensusEndpoint_output
    (L := L) (K := K) init c h, ?_⟩
  intro c' hreach
  rcases h with ⟨hmaj, hc⟩ | ⟨hmaj, hc⟩ | ⟨hmaj, hc⟩
  · rw [hmaj]
    exact doutPartition_output_of_unanimous_output (L := L) (K := K) c' .A
      (fun a ha =>
        ((phase2_A_signs_preserved_by_reachable
          (L := L) (K := K) c c' hc hreach).2 a ha).1)
  · rw [hmaj]
    exact doutPartition_output_of_unanimous_output (L := L) (K := K) c' .B
      (fun a ha =>
        ((phase2_B_signs_preserved_by_reachable
          (L := L) (K := K) c c' hc hreach).2 a ha).1)
  · rw [hmaj]
    exact doutPartition_output_of_unanimous_output (L := L) (K := K) c' .T
      (fun a ha =>
        ((phase2_T_signs_preserved_by_reachable
          (L := L) (K := K) c c' hc hreach).2 a ha).1)

/-- A Phase-2 consensus endpoint packages both required facts for stable
correctness: the output is the initial majority verdict and it is stable. -/
theorem stable_output_of_phase2ConsensusEndpoint
    (init c : Config (AgentState L K))
    (h : phase2ConsensusEndpoint (L := L) (K := K) init c) :
    (doutPartition L K).output (majorityVerdict init) c ∧
      (NonuniformMajority L K).IsStable (doutPartition L K) c :=
  ⟨phase2ConsensusEndpoint_output (L := L) (K := K) init c h,
    phase2ConsensusEndpoint_isStable (L := L) (K := K) init c h⟩

/-- Phase-2 consensus endpoints remain Phase-2 consensus endpoints along every
reachable execution. -/
theorem phase2ConsensusEndpoint_preserved_by_reachable
    (init c c' : Config (AgentState L K))
    (h : phase2ConsensusEndpoint (L := L) (K := K) init c)
    (hreach : (NonuniformMajority L K).Reachable c c') :
    phase2ConsensusEndpoint (L := L) (K := K) init c' := by
  rcases h with ⟨hmaj, hc⟩ | ⟨hmaj, hc⟩ | ⟨hmaj, hc⟩
  · exact Or.inl ⟨hmaj,
      phase2_A_signs_preserved_by_reachable (L := L) (K := K) c c' hc hreach⟩
  · exact Or.inr (Or.inl ⟨hmaj,
      phase2_B_signs_preserved_by_reachable (L := L) (K := K) c c' hc hreach⟩)
  · exact Or.inr (Or.inr ⟨hmaj,
      phase2_T_signs_preserved_by_reachable (L := L) (K := K) c c' hc hreach⟩)

/-! ## Phase-9 consensus endpoints -/

private theorem nine_lt_eleven : 9 < 11 := by omega

private def phase9ConsensusWith
    (opinion : Fin 8) (out : Output) (c : Config (AgentState L K)) : Prop :=
  ∀ a ∈ c, a.phase.val = 9 ∧ a.opinions = opinion ∧ a.output = out

private def phase9OutputAWithSigns (c : Config (AgentState L K)) : Prop :=
  phase9LocallyStable (L := L) (K := K) c ∧
    ∀ a ∈ c, a.output = .A ∧ hasPlusOne a.opinions = true ∧
      hasMinusOne a.opinions = false

private def phase9OutputBWithSigns (c : Config (AgentState L K)) : Prop :=
  phase9LocallyStable (L := L) (K := K) c ∧
    ∀ a ∈ c, a.output = .B ∧ hasMinusOne a.opinions = true ∧
      hasPlusOne a.opinions = false

private def phase9OutputTWithSigns (c : Config (AgentState L K)) : Prop :=
  phase9LocallyStable (L := L) (K := K) c ∧
    ∀ a ∈ c, a.output = .T ∧ hasMinusOne a.opinions = false ∧
      hasPlusOne a.opinions = false

private def phase9GoodA (a : AgentState L K) : Prop :=
  a.phase.val = 9 ∧ a.output = .A ∧
    hasPlusOne a.opinions = true ∧ hasMinusOne a.opinions = false

private def phase9GoodB (a : AgentState L K) : Prop :=
  a.phase.val = 9 ∧ a.output = .B ∧
    hasMinusOne a.opinions = true ∧ hasPlusOne a.opinions = false

private def phase9GoodT (a : AgentState L K) : Prop :=
  a.phase.val = 9 ∧ a.output = .T ∧
    a.opinions = phase2OpinionT

private noncomputable def phase9WrongACount (c : Config (AgentState L K)) : ℕ := by
  classical
  exact Multiset.countP (fun a => ¬ phase9GoodA (L := L) (K := K) a) c

private noncomputable def phase9WrongBCount (c : Config (AgentState L K)) : ℕ := by
  classical
  exact Multiset.countP (fun a => ¬ phase9GoodB (L := L) (K := K) a) c

private noncomputable def phase9WrongTCount (c : Config (AgentState L K)) : ℕ := by
  classical
  exact Multiset.countP (fun a => ¬ phase9GoodT (L := L) (K := K) a) c

/-- A Phase-9 consensus endpoint at the output/sign-support level.  As in
Phase 2, singleton opinions are not required, but the remaining sign support
must be compatible with the unanimous output. -/
def phase9ConsensusEndpoint
    (init c : Config (AgentState L K)) : Prop :=
  (majorityVerdict init = outputTripleOfOutput .A ∧
    phase9OutputAWithSigns (L := L) (K := K) c) ∨
  (majorityVerdict init = outputTripleOfOutput .B ∧
    phase9OutputBWithSigns (L := L) (K := K) c) ∨
  (majorityVerdict init = outputTripleOfOutput .T ∧
    phase9OutputTWithSigns (L := L) (K := K) c)

theorem phase9ConsensusEndpoint_of_A
    (init c : Config (AgentState L K))
    (hmajor : majorityVerdict init = outputTripleOfOutput .A)
    (hstable : phase9LocallyStable (L := L) (K := K) c)
    (h : ∀ a ∈ c, a.output = .A ∧ hasPlusOne a.opinions = true ∧
      hasMinusOne a.opinions = false) :
    phase9ConsensusEndpoint (L := L) (K := K) init c :=
  Or.inl ⟨hmajor, hstable, h⟩

theorem phase9ConsensusEndpoint_of_B
    (init c : Config (AgentState L K))
    (hmajor : majorityVerdict init = outputTripleOfOutput .B)
    (hstable : phase9LocallyStable (L := L) (K := K) c)
    (h : ∀ a ∈ c, a.output = .B ∧ hasMinusOne a.opinions = true ∧
      hasPlusOne a.opinions = false) :
    phase9ConsensusEndpoint (L := L) (K := K) init c :=
  Or.inr (Or.inl ⟨hmajor, hstable, h⟩)

theorem phase9ConsensusEndpoint_of_T
    (init c : Config (AgentState L K))
    (hmajor : majorityVerdict init = outputTripleOfOutput .T)
    (hstable : phase9LocallyStable (L := L) (K := K) c)
    (h : ∀ a ∈ c, a.output = .T ∧ hasMinusOne a.opinions = false ∧
      hasPlusOne a.opinions = false) :
    phase9ConsensusEndpoint (L := L) (K := K) init c :=
  Or.inr (Or.inr ⟨hmajor, hstable, h⟩)

private lemma phase_eq_nine (a : AgentState L K) (h : a.phase.val = 9) :
    a.phase = ⟨9, nine_lt_eleven⟩ := by
  exact Fin.ext h

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

private lemma phaseEpidemicUpdate_eq_self_of_phase9
    (s t : AgentState L K)
    (hs_phase : s.phase = ⟨9, nine_lt_eleven⟩)
    (ht_phase : t.phase = ⟨9, nine_lt_eleven⟩) :
    phaseEpidemicUpdate L K s t = (s, t) := by
  unfold phaseEpidemicUpdate
  rw [hs_phase, ht_phase, max_self]
  simp only [runInitsBetween_self]
  cases s
  cases t
  simp_all

private theorem Transition_preserves_phase9_A
    (s t : AgentState L K)
    (hs_phase : s.phase.val = 9) (ht_phase : t.phase.val = 9)
    (hs_op : s.opinions = phase2OpinionA)
    (ht_op : t.opinions = phase2OpinionA) :
    ((Transition L K s t).1.phase.val = 9 ∧
      (Transition L K s t).1.opinions = phase2OpinionA ∧
      (Transition L K s t).1.output = .A) ∧
    ((Transition L K s t).2.phase.val = 9 ∧
      (Transition L K s t).2.opinions = phase2OpinionA ∧
      (Transition L K s t).2.output = .A) := by
  have hs_phase_eq := phase_eq_nine (L := L) (K := K) s hs_phase
  have ht_phase_eq := phase_eq_nine (L := L) (K := K) t ht_phase
  have hepidemic := phaseEpidemicUpdate_eq_self_of_phase9 (L := L) (K := K)
    s t hs_phase_eq ht_phase_eq
  simp [Transition, hepidemic, hs_phase_eq, ht_phase_eq, Phase9Transition, Phase2Transition,
    hs_op, ht_op, opinionsUnion_A_A, hasMinusOne_A, hasPlusOne_A]
  all_goals
    try rw [finishPhase10Entry_eq_self_of_after_ne_10]
    simp [finishPhase10Entry, canonicalPhase10Entry]

private theorem Transition_preserves_phase9_B
    (s t : AgentState L K)
    (hs_phase : s.phase.val = 9) (ht_phase : t.phase.val = 9)
    (hs_op : s.opinions = phase2OpinionB)
    (ht_op : t.opinions = phase2OpinionB) :
    ((Transition L K s t).1.phase.val = 9 ∧
      (Transition L K s t).1.opinions = phase2OpinionB ∧
      (Transition L K s t).1.output = .B) ∧
    ((Transition L K s t).2.phase.val = 9 ∧
      (Transition L K s t).2.opinions = phase2OpinionB ∧
      (Transition L K s t).2.output = .B) := by
  have hs_phase_eq := phase_eq_nine (L := L) (K := K) s hs_phase
  have ht_phase_eq := phase_eq_nine (L := L) (K := K) t ht_phase
  have hepidemic := phaseEpidemicUpdate_eq_self_of_phase9 (L := L) (K := K)
    s t hs_phase_eq ht_phase_eq
  simp [Transition, hepidemic, hs_phase_eq, ht_phase_eq, Phase9Transition, Phase2Transition,
    hs_op, ht_op, opinionsUnion_B_B, hasMinusOne_B, hasPlusOne_B]
  all_goals
    try rw [finishPhase10Entry_eq_self_of_after_ne_10]
    simp [finishPhase10Entry, canonicalPhase10Entry]

private theorem Transition_preserves_phase9_T
    (s t : AgentState L K)
    (hs_phase : s.phase.val = 9) (ht_phase : t.phase.val = 9)
    (hs_op : s.opinions = phase2OpinionT)
    (ht_op : t.opinions = phase2OpinionT) :
    ((Transition L K s t).1.phase.val = 9 ∧
      (Transition L K s t).1.opinions = phase2OpinionT ∧
      (Transition L K s t).1.output = .T) ∧
    ((Transition L K s t).2.phase.val = 9 ∧
      (Transition L K s t).2.opinions = phase2OpinionT ∧
      (Transition L K s t).2.output = .T) := by
  have hs_phase_eq := phase_eq_nine (L := L) (K := K) s hs_phase
  have ht_phase_eq := phase_eq_nine (L := L) (K := K) t ht_phase
  have hepidemic := phaseEpidemicUpdate_eq_self_of_phase9 (L := L) (K := K)
    s t hs_phase_eq ht_phase_eq
  simp [Transition, hepidemic, hs_phase_eq, ht_phase_eq, Phase9Transition, Phase2Transition,
    hs_op, ht_op, opinionsUnion_T_T, hasMinusOne_T, hasPlusOne_T, phase2OpinionT_val]
  all_goals
    try rw [finishPhase10Entry_eq_self_of_after_ne_10]
    simp [finishPhase10Entry, canonicalPhase10Entry]

private theorem phase9_A_preserved_by_step
    (c c' : Config (AgentState L K))
    (h_c : phase9ConsensusWith (L := L) (K := K) phase2OpinionA .A c)
    (h_step : (NonuniformMajority L K).StepRel c c') :
    phase9ConsensusWith (L := L) (K := K) phase2OpinionA .A c' := by
  rcases h_step with ⟨r₁, r₂, happ, hc'⟩
  dsimp [Protocol.Applicable, NonuniformMajority] at happ hc'
  have hr₁_mem : r₁ ∈ c := Multiset.mem_of_le happ (by simp)
  have hr₂_mem : r₂ ∈ c := Multiset.mem_of_le happ (by simp)
  rcases h_c r₁ hr₁_mem with ⟨hr₁_phase, hr₁_op, _hr₁_out⟩
  rcases h_c r₂ hr₂_mem with ⟨hr₂_phase, hr₂_op, _hr₂_out⟩
  have htrans := Transition_preserves_phase9_A (L := L) (K := K)
    r₁ r₂ hr₁_phase hr₂_phase hr₁_op hr₂_op
  rw [hc']
  intro a ha
  simp only [Multiset.mem_add, Multiset.mem_cons, Multiset.mem_singleton] at ha
  rcases ha with h_old | h_new
  · exact h_c a (Multiset.mem_of_le (Multiset.sub_le_self c {r₁, r₂}) h_old)
  · rcases h_new with h_eq | h_eq
    · simpa [h_eq] using htrans.1
    · simpa [h_eq] using htrans.2

private theorem phase9_B_preserved_by_step
    (c c' : Config (AgentState L K))
    (h_c : phase9ConsensusWith (L := L) (K := K) phase2OpinionB .B c)
    (h_step : (NonuniformMajority L K).StepRel c c') :
    phase9ConsensusWith (L := L) (K := K) phase2OpinionB .B c' := by
  rcases h_step with ⟨r₁, r₂, happ, hc'⟩
  dsimp [Protocol.Applicable, NonuniformMajority] at happ hc'
  have hr₁_mem : r₁ ∈ c := Multiset.mem_of_le happ (by simp)
  have hr₂_mem : r₂ ∈ c := Multiset.mem_of_le happ (by simp)
  rcases h_c r₁ hr₁_mem with ⟨hr₁_phase, hr₁_op, _hr₁_out⟩
  rcases h_c r₂ hr₂_mem with ⟨hr₂_phase, hr₂_op, _hr₂_out⟩
  have htrans := Transition_preserves_phase9_B (L := L) (K := K)
    r₁ r₂ hr₁_phase hr₂_phase hr₁_op hr₂_op
  rw [hc']
  intro a ha
  simp only [Multiset.mem_add, Multiset.mem_cons, Multiset.mem_singleton] at ha
  rcases ha with h_old | h_new
  · exact h_c a (Multiset.mem_of_le (Multiset.sub_le_self c {r₁, r₂}) h_old)
  · rcases h_new with h_eq | h_eq
    · simpa [h_eq] using htrans.1
    · simpa [h_eq] using htrans.2

private theorem phase9_T_preserved_by_step
    (c c' : Config (AgentState L K))
    (h_c : phase9ConsensusWith (L := L) (K := K) phase2OpinionT .T c)
    (h_step : (NonuniformMajority L K).StepRel c c') :
    phase9ConsensusWith (L := L) (K := K) phase2OpinionT .T c' := by
  rcases h_step with ⟨r₁, r₂, happ, hc'⟩
  dsimp [Protocol.Applicable, NonuniformMajority] at happ hc'
  have hr₁_mem : r₁ ∈ c := Multiset.mem_of_le happ (by simp)
  have hr₂_mem : r₂ ∈ c := Multiset.mem_of_le happ (by simp)
  rcases h_c r₁ hr₁_mem with ⟨hr₁_phase, hr₁_op, _hr₁_out⟩
  rcases h_c r₂ hr₂_mem with ⟨hr₂_phase, hr₂_op, _hr₂_out⟩
  have htrans := Transition_preserves_phase9_T (L := L) (K := K)
    r₁ r₂ hr₁_phase hr₂_phase hr₁_op hr₂_op
  rw [hc']
  intro a ha
  simp only [Multiset.mem_add, Multiset.mem_cons, Multiset.mem_singleton] at ha
  rcases ha with h_old | h_new
  · exact h_c a (Multiset.mem_of_le (Multiset.sub_le_self c {r₁, r₂}) h_old)
  · rcases h_new with h_eq | h_eq
    · simpa [h_eq] using htrans.1
    · simpa [h_eq] using htrans.2

private theorem phase9_A_preserved_by_reachable
    (c c' : Config (AgentState L K))
    (h_c : phase9ConsensusWith (L := L) (K := K) phase2OpinionA .A c)
    (h_reach : (NonuniformMajority L K).Reachable c c') :
    phase9ConsensusWith (L := L) (K := K) phase2OpinionA .A c' := by
  induction h_reach with
  | refl => exact h_c
  | tail _ hstep ih =>
      exact phase9_A_preserved_by_step (L := L) (K := K) _ _ ih hstep

private theorem phase9_B_preserved_by_reachable
    (c c' : Config (AgentState L K))
    (h_c : phase9ConsensusWith (L := L) (K := K) phase2OpinionB .B c)
    (h_reach : (NonuniformMajority L K).Reachable c c') :
    phase9ConsensusWith (L := L) (K := K) phase2OpinionB .B c' := by
  induction h_reach with
  | refl => exact h_c
  | tail _ hstep ih =>
      exact phase9_B_preserved_by_step (L := L) (K := K) _ _ ih hstep

private theorem phase9_T_preserved_by_reachable
    (c c' : Config (AgentState L K))
    (h_c : phase9ConsensusWith (L := L) (K := K) phase2OpinionT .T c)
    (h_reach : (NonuniformMajority L K).Reachable c c') :
    phase9ConsensusWith (L := L) (K := K) phase2OpinionT .T c' := by
  induction h_reach with
  | refl => exact h_c
  | tail _ hstep ih =>
      exact phase9_T_preserved_by_step (L := L) (K := K) _ _ ih hstep

private theorem Transition_preserves_phase9_A_signs
    (s t : AgentState L K)
    (hs_phase : s.phase.val = 9) (ht_phase : t.phase.val = 9)
    (hs_out : s.output = .A) (ht_out : t.output = .A)
    (hs_plus : hasPlusOne s.opinions = true)
    (ht_plus : hasPlusOne t.opinions = true)
    (hs_minus : hasMinusOne s.opinions = false)
    (ht_minus : hasMinusOne t.opinions = false) :
    ((Transition L K s t).1.phase.val = 9 ∧
      (Transition L K s t).1.output = .A ∧
      hasPlusOne (Transition L K s t).1.opinions = true ∧
      hasMinusOne (Transition L K s t).1.opinions = false) ∧
    ((Transition L K s t).2.phase.val = 9 ∧
      (Transition L K s t).2.output = .A ∧
      hasPlusOne (Transition L K s t).2.opinions = true ∧
      hasMinusOne (Transition L K s t).2.opinions = false) := by
  have hs_phase_eq := phase_eq_nine (L := L) (K := K) s hs_phase
  have ht_phase_eq := phase_eq_nine (L := L) (K := K) t ht_phase
  have hepidemic := phaseEpidemicUpdate_eq_self_of_phase9 (L := L) (K := K)
    s t hs_phase_eq ht_phase_eq
  have hplus_union :
      hasPlusOne (opinionsUnion s.opinions t.opinions) = true :=
    hasPlusOne_opinionsUnion_true_left s.opinions t.opinions hs_plus
  have hminus_union :
      hasMinusOne (opinionsUnion s.opinions t.opinions) = false :=
    hasMinusOne_opinionsUnion_false s.opinions t.opinions hs_minus ht_minus
  simp [Transition, hepidemic, hs_phase_eq, ht_phase_eq, Phase9Transition,
    Phase2Transition, hs_out, ht_out, hplus_union, hminus_union]
  all_goals
    try rw [finishPhase10Entry_eq_self_of_after_ne_10]
    simp [finishPhase10Entry, canonicalPhase10Entry, hplus_union, hminus_union]

private theorem Transition_preserves_phase9_B_signs
    (s t : AgentState L K)
    (hs_phase : s.phase.val = 9) (ht_phase : t.phase.val = 9)
    (hs_out : s.output = .B) (ht_out : t.output = .B)
    (hs_minus : hasMinusOne s.opinions = true)
    (ht_minus : hasMinusOne t.opinions = true)
    (hs_plus : hasPlusOne s.opinions = false)
    (ht_plus : hasPlusOne t.opinions = false) :
    ((Transition L K s t).1.phase.val = 9 ∧
      (Transition L K s t).1.output = .B ∧
      hasMinusOne (Transition L K s t).1.opinions = true ∧
      hasPlusOne (Transition L K s t).1.opinions = false) ∧
    ((Transition L K s t).2.phase.val = 9 ∧
      (Transition L K s t).2.output = .B ∧
      hasMinusOne (Transition L K s t).2.opinions = true ∧
      hasPlusOne (Transition L K s t).2.opinions = false) := by
  have hs_phase_eq := phase_eq_nine (L := L) (K := K) s hs_phase
  have ht_phase_eq := phase_eq_nine (L := L) (K := K) t ht_phase
  have hepidemic := phaseEpidemicUpdate_eq_self_of_phase9 (L := L) (K := K)
    s t hs_phase_eq ht_phase_eq
  have hminus_union :
      hasMinusOne (opinionsUnion s.opinions t.opinions) = true :=
    hasMinusOne_opinionsUnion_true_left s.opinions t.opinions hs_minus
  have hplus_union :
      hasPlusOne (opinionsUnion s.opinions t.opinions) = false :=
    hasPlusOne_opinionsUnion_false s.opinions t.opinions hs_plus ht_plus
  simp [Transition, hepidemic, hs_phase_eq, ht_phase_eq, Phase9Transition,
    Phase2Transition, hs_out, ht_out, hplus_union, hminus_union]
  all_goals
    try rw [finishPhase10Entry_eq_self_of_after_ne_10]
    simp [finishPhase10Entry, canonicalPhase10Entry, hplus_union, hminus_union]

private theorem Transition_preserves_phase9_T_signs
    (s t : AgentState L K)
    (hs_phase : s.phase.val = 9) (ht_phase : t.phase.val = 9)
    (hs_out : s.output = .T) (ht_out : t.output = .T)
    (hs_minus : hasMinusOne s.opinions = false)
    (ht_minus : hasMinusOne t.opinions = false)
    (hs_plus : hasPlusOne s.opinions = false)
    (ht_plus : hasPlusOne t.opinions = false) :
    ((Transition L K s t).1.phase.val = 9 ∧
      (Transition L K s t).1.output = .T ∧
      hasMinusOne (Transition L K s t).1.opinions = false ∧
      hasPlusOne (Transition L K s t).1.opinions = false) ∧
    ((Transition L K s t).2.phase.val = 9 ∧
      (Transition L K s t).2.output = .T ∧
      hasMinusOne (Transition L K s t).2.opinions = false ∧
      hasPlusOne (Transition L K s t).2.opinions = false) := by
  have hs_phase_eq := phase_eq_nine (L := L) (K := K) s hs_phase
  have ht_phase_eq := phase_eq_nine (L := L) (K := K) t ht_phase
  have hepidemic := phaseEpidemicUpdate_eq_self_of_phase9 (L := L) (K := K)
    s t hs_phase_eq ht_phase_eq
  have hminus_union :
      hasMinusOne (opinionsUnion s.opinions t.opinions) = false :=
    hasMinusOne_opinionsUnion_false s.opinions t.opinions hs_minus ht_minus
  have hplus_union :
      hasPlusOne (opinionsUnion s.opinions t.opinions) = false :=
    hasPlusOne_opinionsUnion_false s.opinions t.opinions hs_plus ht_plus
  simp [Transition, hepidemic, hs_phase_eq, ht_phase_eq, Phase9Transition,
    Phase2Transition, hs_out, ht_out, hplus_union, hminus_union]
  all_goals
    try rw [finishPhase10Entry_eq_self_of_after_ne_10]
    split_ifs <;> simp [finishPhase10Entry, canonicalPhase10Entry,
      hplus_union, hminus_union]

theorem Transition_phase9_A_carrier_closes
    (s t : AgentState L K)
    (hs_phase : s.phase.val = 9) (ht_phase : t.phase.val = 9)
    (hs_out : s.output = .A)
    (hs_plus : hasPlusOne s.opinions = true)
    (hs_minus : hasMinusOne s.opinions = false)
    (ht_minus : hasMinusOne t.opinions = false) :
    ((Transition L K s t).1.phase.val = 9 ∧
      (Transition L K s t).1.output = .A ∧
      hasPlusOne (Transition L K s t).1.opinions = true ∧
      hasMinusOne (Transition L K s t).1.opinions = false) ∧
    ((Transition L K s t).2.phase.val = 9 ∧
      (Transition L K s t).2.output = .A ∧
      hasPlusOne (Transition L K s t).2.opinions = true ∧
      hasMinusOne (Transition L K s t).2.opinions = false) := by
  have hs_phase_eq := phase_eq_nine (L := L) (K := K) s hs_phase
  have ht_phase_eq := phase_eq_nine (L := L) (K := K) t ht_phase
  have hepidemic := phaseEpidemicUpdate_eq_self_of_phase9 (L := L) (K := K)
    s t hs_phase_eq ht_phase_eq
  have hplus_union :
      hasPlusOne (opinionsUnion s.opinions t.opinions) = true :=
    hasPlusOne_opinionsUnion_true_left s.opinions t.opinions hs_plus
  have hminus_union :
      hasMinusOne (opinionsUnion s.opinions t.opinions) = false :=
    hasMinusOne_opinionsUnion_false s.opinions t.opinions hs_minus ht_minus
  simp [Transition, hepidemic, hs_phase_eq, ht_phase_eq, Phase9Transition,
    Phase2Transition, hs_out, hplus_union, hminus_union]
  all_goals
    try rw [finishPhase10Entry_eq_self_of_after_ne_10]
    simp [finishPhase10Entry, canonicalPhase10Entry, hplus_union, hminus_union]

theorem Transition_phase9_B_carrier_closes
    (s t : AgentState L K)
    (hs_phase : s.phase.val = 9) (ht_phase : t.phase.val = 9)
    (hs_out : s.output = .B)
    (hs_minus : hasMinusOne s.opinions = true)
    (hs_plus : hasPlusOne s.opinions = false)
    (ht_plus : hasPlusOne t.opinions = false) :
    ((Transition L K s t).1.phase.val = 9 ∧
      (Transition L K s t).1.output = .B ∧
      hasMinusOne (Transition L K s t).1.opinions = true ∧
      hasPlusOne (Transition L K s t).1.opinions = false) ∧
    ((Transition L K s t).2.phase.val = 9 ∧
      (Transition L K s t).2.output = .B ∧
      hasMinusOne (Transition L K s t).2.opinions = true ∧
      hasPlusOne (Transition L K s t).2.opinions = false) := by
  have hs_phase_eq := phase_eq_nine (L := L) (K := K) s hs_phase
  have ht_phase_eq := phase_eq_nine (L := L) (K := K) t ht_phase
  have hepidemic := phaseEpidemicUpdate_eq_self_of_phase9 (L := L) (K := K)
    s t hs_phase_eq ht_phase_eq
  have hminus_union :
      hasMinusOne (opinionsUnion s.opinions t.opinions) = true :=
    hasMinusOne_opinionsUnion_true_left s.opinions t.opinions hs_minus
  have hplus_union :
      hasPlusOne (opinionsUnion s.opinions t.opinions) = false :=
    hasPlusOne_opinionsUnion_false s.opinions t.opinions hs_plus ht_plus
  simp [Transition, hepidemic, hs_phase_eq, ht_phase_eq, Phase9Transition,
    Phase2Transition, hs_out, hplus_union, hminus_union]
  all_goals
    try rw [finishPhase10Entry_eq_self_of_after_ne_10]
    simp [finishPhase10Entry, canonicalPhase10Entry, hplus_union, hminus_union]

theorem Transition_phase9_A_from_plus
    (s t : AgentState L K)
    (hs_phase : s.phase.val = 9) (ht_phase : t.phase.val = 9)
    (hs_plus : hasPlusOne s.opinions = true)
    (hs_minus : hasMinusOne s.opinions = false)
    (ht_minus : hasMinusOne t.opinions = false) :
    ((Transition L K s t).1.phase.val = 9 ∧
      (Transition L K s t).1.output = .A ∧
      hasPlusOne (Transition L K s t).1.opinions = true ∧
      hasMinusOne (Transition L K s t).1.opinions = false) ∧
    ((Transition L K s t).2.phase.val = 9 ∧
      (Transition L K s t).2.output = .A ∧
      hasPlusOne (Transition L K s t).2.opinions = true ∧
      hasMinusOne (Transition L K s t).2.opinions = false) := by
  have hs_phase_eq := phase_eq_nine (L := L) (K := K) s hs_phase
  have ht_phase_eq := phase_eq_nine (L := L) (K := K) t ht_phase
  have hepidemic := phaseEpidemicUpdate_eq_self_of_phase9 (L := L) (K := K)
    s t hs_phase_eq ht_phase_eq
  have hplus_union :
      hasPlusOne (opinionsUnion s.opinions t.opinions) = true :=
    hasPlusOne_opinionsUnion_true_left s.opinions t.opinions hs_plus
  have hminus_union :
      hasMinusOne (opinionsUnion s.opinions t.opinions) = false :=
    hasMinusOne_opinionsUnion_false s.opinions t.opinions hs_minus ht_minus
  simp [Transition, hepidemic, hs_phase_eq, ht_phase_eq, Phase9Transition,
    Phase2Transition, hplus_union, hminus_union]
  all_goals
    try rw [finishPhase10Entry_eq_self_of_after_ne_10]
    simp [finishPhase10Entry, canonicalPhase10Entry, hplus_union, hminus_union]

theorem Transition_phase9_B_from_minus
    (s t : AgentState L K)
    (hs_phase : s.phase.val = 9) (ht_phase : t.phase.val = 9)
    (hs_minus : hasMinusOne s.opinions = true)
    (hs_plus : hasPlusOne s.opinions = false)
    (ht_plus : hasPlusOne t.opinions = false) :
    ((Transition L K s t).1.phase.val = 9 ∧
      (Transition L K s t).1.output = .B ∧
      hasMinusOne (Transition L K s t).1.opinions = true ∧
      hasPlusOne (Transition L K s t).1.opinions = false) ∧
    ((Transition L K s t).2.phase.val = 9 ∧
      (Transition L K s t).2.output = .B ∧
      hasMinusOne (Transition L K s t).2.opinions = true ∧
      hasPlusOne (Transition L K s t).2.opinions = false) := by
  have hs_phase_eq := phase_eq_nine (L := L) (K := K) s hs_phase
  have ht_phase_eq := phase_eq_nine (L := L) (K := K) t ht_phase
  have hepidemic := phaseEpidemicUpdate_eq_self_of_phase9 (L := L) (K := K)
    s t hs_phase_eq ht_phase_eq
  have hminus_union :
      hasMinusOne (opinionsUnion s.opinions t.opinions) = true :=
    hasMinusOne_opinionsUnion_true_left s.opinions t.opinions hs_minus
  have hplus_union :
      hasPlusOne (opinionsUnion s.opinions t.opinions) = false :=
    hasPlusOne_opinionsUnion_false s.opinions t.opinions hs_plus ht_plus
  simp [Transition, hepidemic, hs_phase_eq, ht_phase_eq, Phase9Transition,
    Phase2Transition, hplus_union, hminus_union]
  all_goals
    try rw [finishPhase10Entry_eq_self_of_after_ne_10]
    simp [finishPhase10Entry, canonicalPhase10Entry, hplus_union, hminus_union]

private theorem phase9_A_carrier_step
    (c : Config (AgentState L K)) (g b : AgentState L K)
    (hphase : ∀ a ∈ c, a.phase.val = 9)
    (hnoMinus : ∀ a ∈ c, hasMinusOne a.opinions = false)
    (hg_mem : g ∈ c) (hb_mem : b ∈ c)
    (hg : phase9GoodA (L := L) (K := K) g)
    (hb_bad : ¬ phase9GoodA (L := L) (K := K) b) :
    let c' := Protocol.stepOrSelf (NonuniformMajority L K) c g b
    (NonuniformMajority L K).Reachable c c' ∧
      (∀ a ∈ c', a.phase.val = 9) ∧
      (∀ a ∈ c', hasMinusOne a.opinions = false) ∧
      (∃ g' ∈ c', phase9GoodA (L := L) (K := K) g') ∧
      phase9WrongACount (L := L) (K := K) c' <
        phase9WrongACount (L := L) (K := K) c := by
  classical
  intro c'
  have hne : g ≠ b := by
    intro h
    subst b
    exact hb_bad hg
  have happ : Protocol.Applicable c g b :=
    pair_le_of_mem_ne hg_mem hb_mem hne
  have hb_phase : b.phase.val = 9 := hphase b hb_mem
  have hb_minus : hasMinusOne b.opinions = false := hnoMinus b hb_mem
  have htrans := Transition_phase9_A_carrier_closes (L := L) (K := K) g b
    hg.1 hb_phase hg.2.1 hg.2.2.1 hg.2.2.2 hb_minus
  have hstep :
      c' =
        c - ({g, b} : Multiset (AgentState L K)) +
          ({(Transition L K g b).1, (Transition L K g b).2} :
            Multiset (AgentState L K)) := by
    unfold c' Protocol.stepOrSelf
    rw [if_pos happ]
    rfl
  refine ⟨Protocol.reachable_stepOrSelf c g b, ?_, ?_, ?_, ?_⟩
  · intro a ha
    rw [hstep] at ha
    simp only [Multiset.mem_add, Multiset.mem_cons, Multiset.mem_singleton] at ha
    rcases ha with ha_old | ha_new
    · have ha_c : a ∈ c :=
        Multiset.mem_of_le (Multiset.sub_le_self c ({g, b} :
          Multiset (AgentState L K))) ha_old
      by_cases hag : a = g
      · simpa [hag] using hg.1
      · by_cases hab : a = b
        · simpa [hab] using hb_phase
        · exact hphase a ha_c
    · have ha_new' :
          a = (Transition L K g b).1 ∨ a = (Transition L K g b).2 := by
        simpa using ha_new
      rcases ha_new' with h_eq1 | h_eq2
      · simpa [h_eq1] using htrans.1.1
      · simpa [h_eq2] using htrans.2.1
  · intro a ha
    rw [hstep] at ha
    simp only [Multiset.mem_add, Multiset.mem_cons, Multiset.mem_singleton] at ha
    rcases ha with ha_old | ha_new
    · have ha_c : a ∈ c :=
        Multiset.mem_of_le (Multiset.sub_le_self c ({g, b} :
          Multiset (AgentState L K))) ha_old
      by_cases hag : a = g
      · simpa [hag] using hg.2.2.2
      · by_cases hab : a = b
        · simpa [hab] using hb_minus
        · exact hnoMinus a ha_c
    · have ha_new' :
          a = (Transition L K g b).1 ∨ a = (Transition L K g b).2 := by
        simpa using ha_new
      rcases ha_new' with h_eq1 | h_eq2
      · simpa [h_eq1] using htrans.1.2.2.2
      · simpa [h_eq2] using htrans.2.2.2.2
  · refine ⟨(Transition L K g b).1, ?_, ?_⟩
    · rw [hstep]
      simp
    · exact htrans.1
  · have hpair :
        Multiset.countP
            (fun a : AgentState L K => ¬ phase9GoodA (L := L) (K := K) a)
            ({g, b} : Multiset (AgentState L K)) = 1 := by
      rw [show ({g, b} : Multiset (AgentState L K)) =
          ({g} : Multiset _) + {b} by rfl,
        Multiset.countP_add,
        countP_singleton_of_not
          (p := fun a : AgentState L K => ¬ phase9GoodA (L := L) (K := K) a)
          (by simpa using hg),
        countP_singleton_of
          (p := fun a : AgentState L K => ¬ phase9GoodA (L := L) (K := K) a)
          hb_bad]
    have hout :
        Multiset.countP
            (fun a : AgentState L K => ¬ phase9GoodA (L := L) (K := K) a)
            ({(Transition L K g b).1, (Transition L K g b).2} :
              Multiset (AgentState L K)) = 0 := by
      rw [show ({(Transition L K g b).1, (Transition L K g b).2} :
          Multiset (AgentState L K)) =
            ({(Transition L K g b).1} : Multiset _) +
              {(Transition L K g b).2} by rfl,
        Multiset.countP_add,
        countP_singleton_of_not
          (p := fun a : AgentState L K => ¬ phase9GoodA (L := L) (K := K) a)
          (by simpa using htrans.1),
        countP_singleton_of_not
          (p := fun a : AgentState L K => ¬ phase9GoodA (L := L) (K := K) a)
          (by simpa using htrans.2)]
    rw [hstep]
    unfold phase9WrongACount
    rw [Multiset.countP_add,
      Multiset.countP_sub happ
        (fun a : AgentState L K => ¬ phase9GoodA (L := L) (K := K) a)]
    rw [hpair, hout]
    have hpos :
        0 < Multiset.countP
          (fun a : AgentState L K => ¬ phase9GoodA (L := L) (K := K) a) c := by
      have hle := Multiset.countP_le_of_le
        (p := fun a : AgentState L K => ¬ phase9GoodA (L := L) (K := K) a) happ
      omega
    omega

theorem phase9_output_closure_A
    (c : Config (AgentState L K))
    (hphase : ∀ a ∈ c, a.phase.val = 9)
    (hnoMinus : ∀ a ∈ c, hasMinusOne a.opinions = false)
    (hcarrier : ∃ a ∈ c, a.output = .A ∧ hasPlusOne a.opinions = true) :
    ∃ final, (NonuniformMajority L K).Reachable c final ∧
      (∀ a ∈ final, a.phase.val = 9 ∧ a.output = .A ∧
        hasPlusOne a.opinions = true ∧ hasMinusOne a.opinions = false) := by
  classical
  have hcarrier_good : ∃ a ∈ c, phase9GoodA (L := L) (K := K) a := by
    rcases hcarrier with ⟨a, ha, hout, hplus⟩
    exact ⟨a, ha, hphase a ha, hout, hplus, hnoMinus a ha⟩
  let n := phase9WrongACount (L := L) (K := K) c
  have main :
      ∀ n, ∀ c : Config (AgentState L K),
        phase9WrongACount (L := L) (K := K) c = n →
        (∀ a ∈ c, a.phase.val = 9) →
        (∀ a ∈ c, hasMinusOne a.opinions = false) →
        (∃ a ∈ c, phase9GoodA (L := L) (K := K) a) →
        ∃ final, (NonuniformMajority L K).Reachable c final ∧
          (∀ a ∈ final, phase9GoodA (L := L) (K := K) a) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro c hcount hphase_c hnoMinus_c hcarrier_c
      by_cases hdone : ∀ a ∈ c, phase9GoodA (L := L) (K := K) a
      · exact ⟨c, Relation.ReflTransGen.refl, hdone⟩
      · have hbad_exists :
            ∃ b ∈ c, ¬ phase9GoodA (L := L) (K := K) b := by
          by_contra hnone
          apply hdone
          intro a ha
          by_contra hbad
          exact hnone ⟨a, ha, hbad⟩
        rcases hbad_exists with ⟨b, hb_mem, hb_bad⟩
        rcases hcarrier_c with ⟨g, hg_mem, hg_good⟩
        let c' := Protocol.stepOrSelf (NonuniformMajority L K) c g b
        have hstep := phase9_A_carrier_step
          (L := L) (K := K) c g b hphase_c hnoMinus_c
          hg_mem hb_mem hg_good hb_bad
        have hcount_lt : phase9WrongACount (L := L) (K := K) c' < n := by
          simpa [c', hcount] using hstep.2.2.2.2
        rcases ih (phase9WrongACount (L := L) (K := K) c') hcount_lt
            c' rfl hstep.2.1 hstep.2.2.1 hstep.2.2.2.1 with
          ⟨final, hreach_final, hgood_final⟩
        exact ⟨final, Relation.ReflTransGen.trans hstep.1 hreach_final, hgood_final⟩
  rcases main n c rfl hphase hnoMinus hcarrier_good with
    ⟨final, hreach, hgood⟩
  exact ⟨final, hreach, by
    intro a ha
    exact hgood a ha⟩

private theorem phase9_B_carrier_step
    (c : Config (AgentState L K)) (g b : AgentState L K)
    (hphase : ∀ a ∈ c, a.phase.val = 9)
    (hnoPlus : ∀ a ∈ c, hasPlusOne a.opinions = false)
    (hg_mem : g ∈ c) (hb_mem : b ∈ c)
    (hg : phase9GoodB (L := L) (K := K) g)
    (hb_bad : ¬ phase9GoodB (L := L) (K := K) b) :
    let c' := Protocol.stepOrSelf (NonuniformMajority L K) c g b
    (NonuniformMajority L K).Reachable c c' ∧
      (∀ a ∈ c', a.phase.val = 9) ∧
      (∀ a ∈ c', hasPlusOne a.opinions = false) ∧
      (∃ g' ∈ c', phase9GoodB (L := L) (K := K) g') ∧
      phase9WrongBCount (L := L) (K := K) c' <
        phase9WrongBCount (L := L) (K := K) c := by
  classical
  intro c'
  have hne : g ≠ b := by
    intro h
    subst b
    exact hb_bad hg
  have happ : Protocol.Applicable c g b :=
    pair_le_of_mem_ne hg_mem hb_mem hne
  have hb_phase : b.phase.val = 9 := hphase b hb_mem
  have hb_plus : hasPlusOne b.opinions = false := hnoPlus b hb_mem
  have htrans := Transition_phase9_B_carrier_closes (L := L) (K := K) g b
    hg.1 hb_phase hg.2.1 hg.2.2.1 hg.2.2.2 hb_plus
  have hstep :
      c' =
        c - ({g, b} : Multiset (AgentState L K)) +
          ({(Transition L K g b).1, (Transition L K g b).2} :
            Multiset (AgentState L K)) := by
    unfold c' Protocol.stepOrSelf
    rw [if_pos happ]
    rfl
  refine ⟨Protocol.reachable_stepOrSelf c g b, ?_, ?_, ?_, ?_⟩
  · intro a ha
    rw [hstep] at ha
    simp only [Multiset.mem_add, Multiset.mem_cons, Multiset.mem_singleton] at ha
    rcases ha with ha_old | ha_new
    · have ha_c : a ∈ c :=
        Multiset.mem_of_le (Multiset.sub_le_self c ({g, b} :
          Multiset (AgentState L K))) ha_old
      by_cases hag : a = g
      · simpa [hag] using hg.1
      · by_cases hab : a = b
        · simpa [hab] using hb_phase
        · exact hphase a ha_c
    · have ha_new' :
          a = (Transition L K g b).1 ∨ a = (Transition L K g b).2 := by
        simpa using ha_new
      rcases ha_new' with h_eq1 | h_eq2
      · simpa [h_eq1] using htrans.1.1
      · simpa [h_eq2] using htrans.2.1
  · intro a ha
    rw [hstep] at ha
    simp only [Multiset.mem_add, Multiset.mem_cons, Multiset.mem_singleton] at ha
    rcases ha with ha_old | ha_new
    · have ha_c : a ∈ c :=
        Multiset.mem_of_le (Multiset.sub_le_self c ({g, b} :
          Multiset (AgentState L K))) ha_old
      by_cases hag : a = g
      · simpa [hag] using hg.2.2.2
      · by_cases hab : a = b
        · simpa [hab] using hb_plus
        · exact hnoPlus a ha_c
    · have ha_new' :
          a = (Transition L K g b).1 ∨ a = (Transition L K g b).2 := by
        simpa using ha_new
      rcases ha_new' with h_eq1 | h_eq2
      · simpa [h_eq1] using htrans.1.2.2.2
      · simpa [h_eq2] using htrans.2.2.2.2
  · refine ⟨(Transition L K g b).1, ?_, ?_⟩
    · rw [hstep]
      simp
    · exact htrans.1
  · have hpair :
        Multiset.countP
            (fun a : AgentState L K => ¬ phase9GoodB (L := L) (K := K) a)
            ({g, b} : Multiset (AgentState L K)) = 1 := by
      rw [show ({g, b} : Multiset (AgentState L K)) =
          ({g} : Multiset _) + {b} by rfl,
        Multiset.countP_add,
        countP_singleton_of_not
          (p := fun a : AgentState L K => ¬ phase9GoodB (L := L) (K := K) a)
          (by simpa using hg),
        countP_singleton_of
          (p := fun a : AgentState L K => ¬ phase9GoodB (L := L) (K := K) a)
          hb_bad]
    have hout :
        Multiset.countP
            (fun a : AgentState L K => ¬ phase9GoodB (L := L) (K := K) a)
            ({(Transition L K g b).1, (Transition L K g b).2} :
              Multiset (AgentState L K)) = 0 := by
      rw [show ({(Transition L K g b).1, (Transition L K g b).2} :
          Multiset (AgentState L K)) =
            ({(Transition L K g b).1} : Multiset _) +
              {(Transition L K g b).2} by rfl,
        Multiset.countP_add,
        countP_singleton_of_not
          (p := fun a : AgentState L K => ¬ phase9GoodB (L := L) (K := K) a)
          (by simpa using htrans.1),
        countP_singleton_of_not
          (p := fun a : AgentState L K => ¬ phase9GoodB (L := L) (K := K) a)
          (by simpa using htrans.2)]
    rw [hstep]
    unfold phase9WrongBCount
    rw [Multiset.countP_add,
      Multiset.countP_sub happ
        (fun a : AgentState L K => ¬ phase9GoodB (L := L) (K := K) a)]
    rw [hpair, hout]
    have hpos :
        0 < Multiset.countP
          (fun a : AgentState L K => ¬ phase9GoodB (L := L) (K := K) a) c := by
      have hle := Multiset.countP_le_of_le
        (p := fun a : AgentState L K => ¬ phase9GoodB (L := L) (K := K) a) happ
      omega
    omega

theorem phase9_output_closure_B
    (c : Config (AgentState L K))
    (hphase : ∀ a ∈ c, a.phase.val = 9)
    (hnoPlus : ∀ a ∈ c, hasPlusOne a.opinions = false)
    (hcarrier : ∃ a ∈ c, a.output = .B ∧ hasMinusOne a.opinions = true) :
    ∃ final, (NonuniformMajority L K).Reachable c final ∧
      (∀ a ∈ final, a.phase.val = 9 ∧ a.output = .B ∧
        hasMinusOne a.opinions = true ∧ hasPlusOne a.opinions = false) := by
  classical
  have hcarrier_good : ∃ a ∈ c, phase9GoodB (L := L) (K := K) a := by
    rcases hcarrier with ⟨a, ha, hout, hminus⟩
    exact ⟨a, ha, hphase a ha, hout, hminus, hnoPlus a ha⟩
  let n := phase9WrongBCount (L := L) (K := K) c
  have main :
      ∀ n, ∀ c : Config (AgentState L K),
        phase9WrongBCount (L := L) (K := K) c = n →
        (∀ a ∈ c, a.phase.val = 9) →
        (∀ a ∈ c, hasPlusOne a.opinions = false) →
        (∃ a ∈ c, phase9GoodB (L := L) (K := K) a) →
        ∃ final, (NonuniformMajority L K).Reachable c final ∧
          (∀ a ∈ final, phase9GoodB (L := L) (K := K) a) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro c hcount hphase_c hnoPlus_c hcarrier_c
      by_cases hdone : ∀ a ∈ c, phase9GoodB (L := L) (K := K) a
      · exact ⟨c, Relation.ReflTransGen.refl, hdone⟩
      · have hbad_exists :
            ∃ b ∈ c, ¬ phase9GoodB (L := L) (K := K) b := by
          by_contra hnone
          apply hdone
          intro a ha
          by_contra hbad
          exact hnone ⟨a, ha, hbad⟩
        rcases hbad_exists with ⟨b, hb_mem, hb_bad⟩
        rcases hcarrier_c with ⟨g, hg_mem, hg_good⟩
        let c' := Protocol.stepOrSelf (NonuniformMajority L K) c g b
        have hstep := phase9_B_carrier_step
          (L := L) (K := K) c g b hphase_c hnoPlus_c
          hg_mem hb_mem hg_good hb_bad
        have hcount_lt : phase9WrongBCount (L := L) (K := K) c' < n := by
          simpa [c', hcount] using hstep.2.2.2.2
        rcases ih (phase9WrongBCount (L := L) (K := K) c') hcount_lt
            c' rfl hstep.2.1 hstep.2.2.1 hstep.2.2.2.1 with
          ⟨final, hreach_final, hgood_final⟩
        exact ⟨final, Relation.ReflTransGen.trans hstep.1 hreach_final, hgood_final⟩
  rcases main n c rfl hphase hnoPlus hcarrier_good with
    ⟨final, hreach, hgood⟩
  exact ⟨final, hreach, by
    intro a ha
    exact hgood a ha⟩

theorem phase9_output_closure_A_from_plus
    (c : Config (AgentState L K))
    (hphase : ∀ a ∈ c, a.phase.val = 9)
    (hnoMinus : ∀ a ∈ c, hasMinusOne a.opinions = false)
    (hplus : ∃ a ∈ c, hasPlusOne a.opinions = true)
    (hcard : 2 ≤ c.card) :
    ∃ final, (NonuniformMajority L K).Reachable c final ∧
      (∀ a ∈ final, a.phase.val = 9 ∧ a.output = .A ∧
        hasPlusOne a.opinions = true ∧ hasMinusOne a.opinions = false) := by
  classical
  rcases hplus with ⟨a, ha, ha_plus⟩
  by_cases ha_out : a.output = .A
  · exact phase9_output_closure_A (L := L) (K := K) c hphase hnoMinus
      ⟨a, ha, ha_out, ha_plus⟩
  · rcases exists_applicable_pair_left_of_mem_card_ge_two
      (L := L) (K := K) ha hcard with ⟨b, happ⟩
    let c' := Protocol.stepOrSelf (NonuniformMajority L K) c a b
    have hb : b ∈ c := Multiset.mem_of_le happ (by simp)
    have htrans := Transition_phase9_A_from_plus (L := L) (K := K) a b
      (hphase a ha) (hphase b hb) ha_plus (hnoMinus a ha) (hnoMinus b hb)
    have hstep :
        c' =
          c - ({a, b} : Multiset (AgentState L K)) +
            ({(Transition L K a b).1, (Transition L K a b).2} :
              Multiset (AgentState L K)) := by
      unfold c' Protocol.stepOrSelf
      rw [if_pos happ]
      rfl
    have hphase' : ∀ x ∈ c', x.phase.val = 9 := by
      intro x hx
      rw [hstep] at hx
      simp only [Multiset.mem_add, Multiset.mem_cons, Multiset.mem_singleton] at hx
      rcases hx with hx_old | hx_new
      · exact hphase x (Multiset.mem_of_le
          (Multiset.sub_le_self c ({a, b} : Multiset (AgentState L K))) hx_old)
      · have hx_new' :
            x = (Transition L K a b).1 ∨ x = (Transition L K a b).2 := by
          simpa using hx_new
        rcases hx_new' with h_eq1 | h_eq2
        · simpa [h_eq1] using htrans.1.1
        · simpa [h_eq2] using htrans.2.1
    have hnoMinus' : ∀ x ∈ c', hasMinusOne x.opinions = false := by
      intro x hx
      rw [hstep] at hx
      simp only [Multiset.mem_add, Multiset.mem_cons, Multiset.mem_singleton] at hx
      rcases hx with hx_old | hx_new
      · exact hnoMinus x (Multiset.mem_of_le
          (Multiset.sub_le_self c ({a, b} : Multiset (AgentState L K))) hx_old)
      · have hx_new' :
            x = (Transition L K a b).1 ∨ x = (Transition L K a b).2 := by
          simpa using hx_new
        rcases hx_new' with h_eq1 | h_eq2
        · simpa [h_eq1] using htrans.1.2.2.2
        · simpa [h_eq2] using htrans.2.2.2.2
    have hcarrier' :
        ∃ x ∈ c', x.output = .A ∧ hasPlusOne x.opinions = true := by
      refine ⟨(Transition L K a b).1, ?_, htrans.1.2.1, htrans.1.2.2.1⟩
      rw [hstep]
      simp
    rcases phase9_output_closure_A (L := L) (K := K) c'
        hphase' hnoMinus' hcarrier' with ⟨final, hreach, hgood⟩
    exact ⟨final, Relation.ReflTransGen.trans
      (Protocol.reachable_stepOrSelf c a b) hreach, hgood⟩

theorem phase9_output_closure_B_from_minus
    (c : Config (AgentState L K))
    (hphase : ∀ a ∈ c, a.phase.val = 9)
    (hnoPlus : ∀ a ∈ c, hasPlusOne a.opinions = false)
    (hminus : ∃ a ∈ c, hasMinusOne a.opinions = true)
    (hcard : 2 ≤ c.card) :
    ∃ final, (NonuniformMajority L K).Reachable c final ∧
      (∀ a ∈ final, a.phase.val = 9 ∧ a.output = .B ∧
        hasMinusOne a.opinions = true ∧ hasPlusOne a.opinions = false) := by
  classical
  rcases hminus with ⟨a, ha, ha_minus⟩
  by_cases ha_out : a.output = .B
  · exact phase9_output_closure_B (L := L) (K := K) c hphase hnoPlus
      ⟨a, ha, ha_out, ha_minus⟩
  · rcases exists_applicable_pair_left_of_mem_card_ge_two
      (L := L) (K := K) ha hcard with ⟨b, happ⟩
    let c' := Protocol.stepOrSelf (NonuniformMajority L K) c a b
    have hb : b ∈ c := Multiset.mem_of_le happ (by simp)
    have htrans := Transition_phase9_B_from_minus (L := L) (K := K) a b
      (hphase a ha) (hphase b hb) ha_minus (hnoPlus a ha) (hnoPlus b hb)
    have hstep :
        c' =
          c - ({a, b} : Multiset (AgentState L K)) +
            ({(Transition L K a b).1, (Transition L K a b).2} :
              Multiset (AgentState L K)) := by
      unfold c' Protocol.stepOrSelf
      rw [if_pos happ]
      rfl
    have hphase' : ∀ x ∈ c', x.phase.val = 9 := by
      intro x hx
      rw [hstep] at hx
      simp only [Multiset.mem_add, Multiset.mem_cons, Multiset.mem_singleton] at hx
      rcases hx with hx_old | hx_new
      · exact hphase x (Multiset.mem_of_le
          (Multiset.sub_le_self c ({a, b} : Multiset (AgentState L K))) hx_old)
      · have hx_new' :
            x = (Transition L K a b).1 ∨ x = (Transition L K a b).2 := by
          simpa using hx_new
        rcases hx_new' with h_eq1 | h_eq2
        · simpa [h_eq1] using htrans.1.1
        · simpa [h_eq2] using htrans.2.1
    have hnoPlus' : ∀ x ∈ c', hasPlusOne x.opinions = false := by
      intro x hx
      rw [hstep] at hx
      simp only [Multiset.mem_add, Multiset.mem_cons, Multiset.mem_singleton] at hx
      rcases hx with hx_old | hx_new
      · exact hnoPlus x (Multiset.mem_of_le
          (Multiset.sub_le_self c ({a, b} : Multiset (AgentState L K))) hx_old)
      · have hx_new' :
            x = (Transition L K a b).1 ∨ x = (Transition L K a b).2 := by
          simpa using hx_new
        rcases hx_new' with h_eq1 | h_eq2
        · simpa [h_eq1] using htrans.1.2.2.2
        · simpa [h_eq2] using htrans.2.2.2.2
    have hcarrier' :
        ∃ x ∈ c', x.output = .B ∧ hasMinusOne x.opinions = true := by
      refine ⟨(Transition L K a b).1, ?_, htrans.1.2.1, htrans.1.2.2.1⟩
      rw [hstep]
      simp
    rcases phase9_output_closure_B (L := L) (K := K) c'
        hphase' hnoPlus' hcarrier' with ⟨final, hreach, hgood⟩
    exact ⟨final, Relation.ReflTransGen.trans
      (Protocol.reachable_stepOrSelf c a b) hreach, hgood⟩

private theorem phase9_T_carrier_step
    (c : Config (AgentState L K)) (g b : AgentState L K)
    (hphase : ∀ a ∈ c, a.phase.val = 9)
    (hop : ∀ a ∈ c, a.opinions = phase2OpinionT)
    (hg_mem : g ∈ c) (hb_mem : b ∈ c)
    (hg : phase9GoodT (L := L) (K := K) g)
    (hb_bad : ¬ phase9GoodT (L := L) (K := K) b) :
    let c' := Protocol.stepOrSelf (NonuniformMajority L K) c g b
    (NonuniformMajority L K).Reachable c c' ∧
      (∀ a ∈ c', a.phase.val = 9) ∧
      (∀ a ∈ c', a.opinions = phase2OpinionT) ∧
      (∃ g' ∈ c', phase9GoodT (L := L) (K := K) g') ∧
      phase9WrongTCount (L := L) (K := K) c' <
        phase9WrongTCount (L := L) (K := K) c := by
  classical
  intro c'
  have hne : g ≠ b := by
    intro h
    subst b
    exact hb_bad hg
  have happ : Protocol.Applicable c g b :=
    pair_le_of_mem_ne hg_mem hb_mem hne
  have hb_phase : b.phase.val = 9 := hphase b hb_mem
  have hb_op : b.opinions = phase2OpinionT := hop b hb_mem
  have htrans := Transition_preserves_phase9_T (L := L) (K := K) g b
    hg.1 hb_phase hg.2.2 hb_op
  have hstep :
      c' =
        c - ({g, b} : Multiset (AgentState L K)) +
          ({(Transition L K g b).1, (Transition L K g b).2} :
            Multiset (AgentState L K)) := by
    unfold c' Protocol.stepOrSelf
    rw [if_pos happ]
    rfl
  refine ⟨Protocol.reachable_stepOrSelf c g b, ?_, ?_, ?_, ?_⟩
  · intro a ha
    rw [hstep] at ha
    simp only [Multiset.mem_add, Multiset.mem_cons, Multiset.mem_singleton] at ha
    rcases ha with ha_old | ha_new
    · exact hphase a (Multiset.mem_of_le
        (Multiset.sub_le_self c ({g, b} : Multiset (AgentState L K))) ha_old)
    · have ha_new' :
          a = (Transition L K g b).1 ∨ a = (Transition L K g b).2 := by
        simpa using ha_new
      rcases ha_new' with h_eq1 | h_eq2
      · simpa [h_eq1] using htrans.1.1
      · simpa [h_eq2] using htrans.2.1
  · intro a ha
    rw [hstep] at ha
    simp only [Multiset.mem_add, Multiset.mem_cons, Multiset.mem_singleton] at ha
    rcases ha with ha_old | ha_new
    · exact hop a (Multiset.mem_of_le
        (Multiset.sub_le_self c ({g, b} : Multiset (AgentState L K))) ha_old)
    · have ha_new' :
          a = (Transition L K g b).1 ∨ a = (Transition L K g b).2 := by
        simpa using ha_new
      rcases ha_new' with h_eq1 | h_eq2
      · simpa [h_eq1] using htrans.1.2.1
      · simpa [h_eq2] using htrans.2.2.1
  · refine ⟨(Transition L K g b).1, ?_, ?_⟩
    · rw [hstep]
      simp
    · exact ⟨htrans.1.1, htrans.1.2.2, htrans.1.2.1⟩
  · have hpair :
        Multiset.countP
            (fun a : AgentState L K => ¬ phase9GoodT (L := L) (K := K) a)
            ({g, b} : Multiset (AgentState L K)) = 1 := by
      rw [show ({g, b} : Multiset (AgentState L K)) =
          ({g} : Multiset _) + {b} by rfl,
        Multiset.countP_add,
        countP_singleton_of_not
          (p := fun a : AgentState L K => ¬ phase9GoodT (L := L) (K := K) a)
          (by simpa using hg),
        countP_singleton_of
          (p := fun a : AgentState L K => ¬ phase9GoodT (L := L) (K := K) a)
          hb_bad]
    have hout :
        Multiset.countP
            (fun a : AgentState L K => ¬ phase9GoodT (L := L) (K := K) a)
            ({(Transition L K g b).1, (Transition L K g b).2} :
              Multiset (AgentState L K)) = 0 := by
      rw [show ({(Transition L K g b).1, (Transition L K g b).2} :
          Multiset (AgentState L K)) =
            ({(Transition L K g b).1} : Multiset _) +
              {(Transition L K g b).2} by rfl,
        Multiset.countP_add,
        countP_singleton_of_not
          (p := fun a : AgentState L K => ¬ phase9GoodT (L := L) (K := K) a)
          (by
            intro hbad
            exact hbad ⟨htrans.1.1, htrans.1.2.2, htrans.1.2.1⟩),
        countP_singleton_of_not
          (p := fun a : AgentState L K => ¬ phase9GoodT (L := L) (K := K) a)
          (by
            intro hbad
            exact hbad ⟨htrans.2.1, htrans.2.2.2, htrans.2.2.1⟩)]
    rw [hstep]
    unfold phase9WrongTCount
    rw [Multiset.countP_add,
      Multiset.countP_sub happ
        (fun a : AgentState L K => ¬ phase9GoodT (L := L) (K := K) a)]
    rw [hpair, hout]
    have hpos :
        0 < Multiset.countP
          (fun a : AgentState L K => ¬ phase9GoodT (L := L) (K := K) a) c := by
      have hle := Multiset.countP_le_of_le
        (p := fun a : AgentState L K => ¬ phase9GoodT (L := L) (K := K) a) happ
      omega
    omega

private theorem phase9_output_closure_T_with_carrier
    (c : Config (AgentState L K))
    (hphase : ∀ a ∈ c, a.phase.val = 9)
    (hop : ∀ a ∈ c, a.opinions = phase2OpinionT)
    (hcarrier : ∃ a ∈ c, phase9GoodT (L := L) (K := K) a) :
    ∃ final, (NonuniformMajority L K).Reachable c final ∧
      (∀ a ∈ final, phase9GoodT (L := L) (K := K) a) := by
  classical
  let n := phase9WrongTCount (L := L) (K := K) c
  have main :
      ∀ n, ∀ c : Config (AgentState L K),
        phase9WrongTCount (L := L) (K := K) c = n →
        (∀ a ∈ c, a.phase.val = 9) →
        (∀ a ∈ c, a.opinions = phase2OpinionT) →
        (∃ a ∈ c, phase9GoodT (L := L) (K := K) a) →
        ∃ final, (NonuniformMajority L K).Reachable c final ∧
          (∀ a ∈ final, phase9GoodT (L := L) (K := K) a) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro c hcount hphase_c hop_c hcarrier_c
      by_cases hdone : ∀ a ∈ c, phase9GoodT (L := L) (K := K) a
      · exact ⟨c, Relation.ReflTransGen.refl, hdone⟩
      · have hbad_exists :
            ∃ b ∈ c, ¬ phase9GoodT (L := L) (K := K) b := by
          by_contra hnone
          apply hdone
          intro a ha
          by_contra hbad
          exact hnone ⟨a, ha, hbad⟩
        rcases hbad_exists with ⟨b, hb_mem, hb_bad⟩
        rcases hcarrier_c with ⟨g, hg_mem, hg_good⟩
        let c' := Protocol.stepOrSelf (NonuniformMajority L K) c g b
        have hstep := phase9_T_carrier_step
          (L := L) (K := K) c g b hphase_c hop_c
          hg_mem hb_mem hg_good hb_bad
        have hcount_lt : phase9WrongTCount (L := L) (K := K) c' < n := by
          simpa [c', hcount] using hstep.2.2.2.2
        rcases ih (phase9WrongTCount (L := L) (K := K) c') hcount_lt
            c' rfl hstep.2.1 hstep.2.2.1 hstep.2.2.2.1 with
          ⟨final, hreach_final, hgood_final⟩
        exact ⟨final, Relation.ReflTransGen.trans hstep.1 hreach_final, hgood_final⟩
  exact main n c rfl hphase hop hcarrier

theorem phase9_output_closure_T
    (c : Config (AgentState L K))
    (hphase : ∀ a ∈ c, a.phase.val = 9)
    (hop : ∀ a ∈ c, a.opinions = phase2OpinionT)
    (hcard : 2 ≤ c.card) :
    ∃ final, (NonuniformMajority L K).Reachable c final ∧
      (∀ a ∈ final, a.phase.val = 9 ∧ a.output = .T ∧
        hasMinusOne a.opinions = false ∧ hasPlusOne a.opinions = false) := by
  classical
  have hmem : ∃ a, a ∈ c := by
    exact Multiset.card_pos_iff_exists_mem.mp (by omega)
  rcases hmem with ⟨a, ha⟩
  by_cases ha_good : phase9GoodT (L := L) (K := K) a
  · rcases phase9_output_closure_T_with_carrier (L := L) (K := K) c
        hphase hop ⟨a, ha, ha_good⟩ with ⟨final, hreach, hgood⟩
    exact ⟨final, hreach, by
      intro x hx
      rcases hgood x hx with ⟨hph, hout, hopx⟩
      exact ⟨hph, hout, by simp [hopx, phase2OpinionT, hasMinusOne],
        by simp [hopx, phase2OpinionT, hasPlusOne]⟩⟩
  · rcases exists_applicable_pair_left_of_mem_card_ge_two
      (L := L) (K := K) ha hcard with ⟨b, happ⟩
    let c' := Protocol.stepOrSelf (NonuniformMajority L K) c a b
    have hb : b ∈ c := Multiset.mem_of_le happ (by simp)
    have htrans := Transition_preserves_phase9_T (L := L) (K := K) a b
      (hphase a ha) (hphase b hb) (hop a ha) (hop b hb)
    have hstep :
        c' =
          c - ({a, b} : Multiset (AgentState L K)) +
            ({(Transition L K a b).1, (Transition L K a b).2} :
              Multiset (AgentState L K)) := by
      unfold c' Protocol.stepOrSelf
      rw [if_pos happ]
      rfl
    have hphase' : ∀ x ∈ c', x.phase.val = 9 := by
      intro x hx
      rw [hstep] at hx
      simp only [Multiset.mem_add, Multiset.mem_cons, Multiset.mem_singleton] at hx
      rcases hx with hx_old | hx_new
      · exact hphase x (Multiset.mem_of_le
          (Multiset.sub_le_self c ({a, b} : Multiset (AgentState L K))) hx_old)
      · have hx_new' :
            x = (Transition L K a b).1 ∨ x = (Transition L K a b).2 := by
          simpa using hx_new
        rcases hx_new' with h_eq1 | h_eq2
        · simpa [h_eq1] using htrans.1.1
        · simpa [h_eq2] using htrans.2.1
    have hop' : ∀ x ∈ c', x.opinions = phase2OpinionT := by
      intro x hx
      rw [hstep] at hx
      simp only [Multiset.mem_add, Multiset.mem_cons, Multiset.mem_singleton] at hx
      rcases hx with hx_old | hx_new
      · exact hop x (Multiset.mem_of_le
          (Multiset.sub_le_self c ({a, b} : Multiset (AgentState L K))) hx_old)
      · have hx_new' :
            x = (Transition L K a b).1 ∨ x = (Transition L K a b).2 := by
          simpa using hx_new
        rcases hx_new' with h_eq1 | h_eq2
        · simpa [h_eq1] using htrans.1.2.1
        · simpa [h_eq2] using htrans.2.2.1
    have hcarrier' :
        ∃ x ∈ c', phase9GoodT (L := L) (K := K) x := by
      refine ⟨(Transition L K a b).1, ?_, ?_⟩
      · rw [hstep]
        simp
      · exact ⟨htrans.1.1, htrans.1.2.2, htrans.1.2.1⟩
    rcases phase9_output_closure_T_with_carrier (L := L) (K := K) c'
        hphase' hop' hcarrier' with ⟨final, hreach, hgood⟩
    exact ⟨final, Relation.ReflTransGen.trans
      (Protocol.reachable_stepOrSelf c a b) hreach, by
      intro x hx
      rcases hgood x hx with ⟨hph, hout, hopx⟩
      exact ⟨hph, hout, by simp [hopx, phase2OpinionT, hasMinusOne],
        by simp [hopx, phase2OpinionT, hasPlusOne]⟩⟩

private theorem phase9_A_signs_preserved_by_step
    (c c' : Config (AgentState L K))
    (h_c : phase9OutputAWithSigns (L := L) (K := K) c)
    (h_step : (NonuniformMajority L K).StepRel c c') :
    phase9OutputAWithSigns (L := L) (K := K) c' := by
  rcases h_step with ⟨r₁, r₂, happ, hc'⟩
  dsimp [Protocol.Applicable, NonuniformMajority] at happ hc'
  have hr₁_mem : r₁ ∈ c := Multiset.mem_of_le happ (by simp)
  have hr₂_mem : r₂ ∈ c := Multiset.mem_of_le happ (by simp)
  rcases h_c with ⟨hstable, hsigns⟩
  rcases hsigns r₁ hr₁_mem with ⟨hr₁_out, hr₁_plus, hr₁_minus⟩
  rcases hsigns r₂ hr₂_mem with ⟨hr₂_out, hr₂_plus, hr₂_minus⟩
  have htrans := Transition_preserves_phase9_A_signs (L := L) (K := K)
    r₁ r₂ (hstable.1 r₁ hr₁_mem) (hstable.1 r₂ hr₂_mem)
    hr₁_out hr₂_out hr₁_plus hr₂_plus hr₁_minus hr₂_minus
  rw [hc']
  let cnext :=
    c - ({r₁, r₂} : Multiset (AgentState L K)) +
      ({(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2} :
        Multiset (AgentState L K))
  have hdata : ∀ a ∈ cnext,
      a.phase.val = 9 ∧ a.output = .A ∧
        hasPlusOne a.opinions = true ∧ hasMinusOne a.opinions = false := by
    intro a ha
    simp only [cnext, Multiset.mem_add, Multiset.mem_cons,
      Multiset.mem_singleton] at ha
    rcases ha with h_old | h_new
    · have ha_c : a ∈ c :=
        Multiset.mem_of_le (Multiset.sub_le_self c ({r₁, r₂} :
          Multiset (AgentState L K))) h_old
      rcases hsigns a ha_c with ⟨hout, hplus, hminus⟩
      exact ⟨hstable.1 a ha_c, hout, hplus, hminus⟩
    · have hnew' :
          a = (Transition L K r₁ r₂).1 ∨
            a = (Transition L K r₁ r₂).2 := by
        simpa using h_new
      rcases hnew' with h_eq | h_eq
      · simpa [h_eq] using htrans.1
      · simpa [h_eq] using htrans.2
  refine ⟨?_, ?_⟩
  · refine ⟨fun a ha => (hdata a ha).1, ?_⟩
    intro a b hab hboth
    have ha := hdata a (Multiset.mem_of_le hab (by simp))
    have hb := hdata b (Multiset.mem_of_le hab (by simp))
    have hminus_union :=
      hasMinusOne_opinionsUnion_false a.opinions b.opinions ha.2.2.2 hb.2.2.2
    rw [hminus_union] at hboth
    simp at hboth
  · intro a ha
    exact (hdata a ha).2

private theorem phase9_B_signs_preserved_by_step
    (c c' : Config (AgentState L K))
    (h_c : phase9OutputBWithSigns (L := L) (K := K) c)
    (h_step : (NonuniformMajority L K).StepRel c c') :
    phase9OutputBWithSigns (L := L) (K := K) c' := by
  rcases h_step with ⟨r₁, r₂, happ, hc'⟩
  dsimp [Protocol.Applicable, NonuniformMajority] at happ hc'
  have hr₁_mem : r₁ ∈ c := Multiset.mem_of_le happ (by simp)
  have hr₂_mem : r₂ ∈ c := Multiset.mem_of_le happ (by simp)
  rcases h_c with ⟨hstable, hsigns⟩
  rcases hsigns r₁ hr₁_mem with ⟨hr₁_out, hr₁_minus, hr₁_plus⟩
  rcases hsigns r₂ hr₂_mem with ⟨hr₂_out, hr₂_minus, hr₂_plus⟩
  have htrans := Transition_preserves_phase9_B_signs (L := L) (K := K)
    r₁ r₂ (hstable.1 r₁ hr₁_mem) (hstable.1 r₂ hr₂_mem)
    hr₁_out hr₂_out hr₁_minus hr₂_minus hr₁_plus hr₂_plus
  rw [hc']
  let cnext :=
    c - ({r₁, r₂} : Multiset (AgentState L K)) +
      ({(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2} :
        Multiset (AgentState L K))
  have hdata : ∀ a ∈ cnext,
      a.phase.val = 9 ∧ a.output = .B ∧
        hasMinusOne a.opinions = true ∧ hasPlusOne a.opinions = false := by
    intro a ha
    simp only [cnext, Multiset.mem_add, Multiset.mem_cons,
      Multiset.mem_singleton] at ha
    rcases ha with h_old | h_new
    · have ha_c : a ∈ c :=
        Multiset.mem_of_le (Multiset.sub_le_self c ({r₁, r₂} :
          Multiset (AgentState L K))) h_old
      rcases hsigns a ha_c with ⟨hout, hminus, hplus⟩
      exact ⟨hstable.1 a ha_c, hout, hminus, hplus⟩
    · have hnew' :
          a = (Transition L K r₁ r₂).1 ∨
            a = (Transition L K r₁ r₂).2 := by
        simpa using h_new
      rcases hnew' with h_eq | h_eq
      · simpa [h_eq] using htrans.1
      · simpa [h_eq] using htrans.2
  refine ⟨?_, ?_⟩
  · refine ⟨fun a ha => (hdata a ha).1, ?_⟩
    intro a b hab hboth
    have ha := hdata a (Multiset.mem_of_le hab (by simp))
    have hb := hdata b (Multiset.mem_of_le hab (by simp))
    have hplus_union :=
      hasPlusOne_opinionsUnion_false a.opinions b.opinions ha.2.2.2 hb.2.2.2
    rw [hplus_union] at hboth
    simp at hboth
  · intro a ha
    exact (hdata a ha).2

private theorem phase9_T_signs_preserved_by_step
    (c c' : Config (AgentState L K))
    (h_c : phase9OutputTWithSigns (L := L) (K := K) c)
    (h_step : (NonuniformMajority L K).StepRel c c') :
    phase9OutputTWithSigns (L := L) (K := K) c' := by
  rcases h_step with ⟨r₁, r₂, happ, hc'⟩
  dsimp [Protocol.Applicable, NonuniformMajority] at happ hc'
  have hr₁_mem : r₁ ∈ c := Multiset.mem_of_le happ (by simp)
  have hr₂_mem : r₂ ∈ c := Multiset.mem_of_le happ (by simp)
  rcases h_c with ⟨hstable, hsigns⟩
  rcases hsigns r₁ hr₁_mem with ⟨hr₁_out, hr₁_minus, hr₁_plus⟩
  rcases hsigns r₂ hr₂_mem with ⟨hr₂_out, hr₂_minus, hr₂_plus⟩
  have htrans := Transition_preserves_phase9_T_signs (L := L) (K := K)
    r₁ r₂ (hstable.1 r₁ hr₁_mem) (hstable.1 r₂ hr₂_mem)
    hr₁_out hr₂_out hr₁_minus hr₂_minus hr₁_plus hr₂_plus
  rw [hc']
  let cnext :=
    c - ({r₁, r₂} : Multiset (AgentState L K)) +
      ({(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2} :
        Multiset (AgentState L K))
  have hdata : ∀ a ∈ cnext,
      a.phase.val = 9 ∧ a.output = .T ∧
        hasMinusOne a.opinions = false ∧ hasPlusOne a.opinions = false := by
    intro a ha
    simp only [cnext, Multiset.mem_add, Multiset.mem_cons,
      Multiset.mem_singleton] at ha
    rcases ha with h_old | h_new
    · have ha_c : a ∈ c :=
        Multiset.mem_of_le (Multiset.sub_le_self c ({r₁, r₂} :
          Multiset (AgentState L K))) h_old
      rcases hsigns a ha_c with ⟨hout, hminus, hplus⟩
      exact ⟨hstable.1 a ha_c, hout, hminus, hplus⟩
    · have hnew' :
          a = (Transition L K r₁ r₂).1 ∨
            a = (Transition L K r₁ r₂).2 := by
        simpa using h_new
      rcases hnew' with h_eq | h_eq
      · simpa [h_eq] using htrans.1
      · simpa [h_eq] using htrans.2
  refine ⟨?_, ?_⟩
  · refine ⟨fun a ha => (hdata a ha).1, ?_⟩
    intro a b hab hboth
    have ha := hdata a (Multiset.mem_of_le hab (by simp))
    have hb := hdata b (Multiset.mem_of_le hab (by simp))
    have hminus_union :=
      hasMinusOne_opinionsUnion_false a.opinions b.opinions ha.2.2.1 hb.2.2.1
    rw [hminus_union] at hboth
    simp at hboth
  · intro a ha
    exact (hdata a ha).2

private theorem phase9_A_signs_preserved_by_reachable
    (c c' : Config (AgentState L K))
    (h_c : phase9OutputAWithSigns (L := L) (K := K) c)
    (h_reach : (NonuniformMajority L K).Reachable c c') :
    phase9OutputAWithSigns (L := L) (K := K) c' := by
  induction h_reach with
  | refl => exact h_c
  | tail _ hstep ih =>
      exact phase9_A_signs_preserved_by_step (L := L) (K := K) _ _ ih hstep

private theorem phase9_B_signs_preserved_by_reachable
    (c c' : Config (AgentState L K))
    (h_c : phase9OutputBWithSigns (L := L) (K := K) c)
    (h_reach : (NonuniformMajority L K).Reachable c c') :
    phase9OutputBWithSigns (L := L) (K := K) c' := by
  induction h_reach with
  | refl => exact h_c
  | tail _ hstep ih =>
      exact phase9_B_signs_preserved_by_step (L := L) (K := K) _ _ ih hstep

private theorem phase9_T_signs_preserved_by_reachable
    (c c' : Config (AgentState L K))
    (h_c : phase9OutputTWithSigns (L := L) (K := K) c)
    (h_reach : (NonuniformMajority L K).Reachable c c') :
    phase9OutputTWithSigns (L := L) (K := K) c' := by
  induction h_reach with
  | refl => exact h_c
  | tail _ hstep ih =>
      exact phase9_T_signs_preserved_by_step (L := L) (K := K) _ _ ih hstep

private theorem doutPartition_output_of_phase9ConsensusWith
    (c : Config (AgentState L K)) (opinion : Fin 8) (out : Output)
    (h : phase9ConsensusWith (L := L) (K := K) opinion out c) :
    (doutPartition L K).output (outputTripleOfOutput out) c :=
  doutPartition_output_of_unanimous_output (L := L) (K := K) c out
    (fun a ha => (h a ha).2.2)

theorem phase9ConsensusEndpoint_output
    (init c : Config (AgentState L K))
    (h : phase9ConsensusEndpoint (L := L) (K := K) init c) :
    (doutPartition L K).output (majorityVerdict init) c := by
  rcases h with ⟨hmaj, hc⟩ | ⟨hmaj, hc⟩ | ⟨hmaj, hc⟩
  · rw [hmaj]
    exact doutPartition_output_of_unanimous_output (L := L) (K := K) c .A
      (fun a ha => (hc.2 a ha).1)
  · rw [hmaj]
    exact doutPartition_output_of_unanimous_output (L := L) (K := K) c .B
      (fun a ha => (hc.2 a ha).1)
  · rw [hmaj]
    exact doutPartition_output_of_unanimous_output (L := L) (K := K) c .T
      (fun a ha => (hc.2 a ha).1)

theorem phase9ConsensusEndpoint_isStable
    (init c : Config (AgentState L K))
    (h : phase9ConsensusEndpoint (L := L) (K := K) init c) :
    (NonuniformMajority L K).IsStable (doutPartition L K) c := by
  refine ⟨majorityVerdict init, phase9ConsensusEndpoint_output
    (L := L) (K := K) init c h, ?_⟩
  intro c' hreach
  rcases h with ⟨hmaj, hc⟩ | ⟨hmaj, hc⟩ | ⟨hmaj, hc⟩
  · rw [hmaj]
    exact doutPartition_output_of_unanimous_output (L := L) (K := K) c' .A
      (fun a ha =>
        ((phase9_A_signs_preserved_by_reachable
          (L := L) (K := K) c c' hc hreach).2 a ha).1)
  · rw [hmaj]
    exact doutPartition_output_of_unanimous_output (L := L) (K := K) c' .B
      (fun a ha =>
        ((phase9_B_signs_preserved_by_reachable
          (L := L) (K := K) c c' hc hreach).2 a ha).1)
  · rw [hmaj]
    exact doutPartition_output_of_unanimous_output (L := L) (K := K) c' .T
      (fun a ha =>
        ((phase9_T_signs_preserved_by_reachable
          (L := L) (K := K) c c' hc hreach).2 a ha).1)

theorem stable_output_of_phase9ConsensusEndpoint
    (init c : Config (AgentState L K))
    (h : phase9ConsensusEndpoint (L := L) (K := K) init c) :
    (doutPartition L K).output (majorityVerdict init) c ∧
      (NonuniformMajority L K).IsStable (doutPartition L K) c :=
  ⟨phase9ConsensusEndpoint_output (L := L) (K := K) init c h,
    phase9ConsensusEndpoint_isStable (L := L) (K := K) init c h⟩

/-- Phase-9 consensus endpoints remain Phase-9 consensus endpoints along every
reachable execution. -/
theorem phase9ConsensusEndpoint_preserved_by_reachable
    (init c c' : Config (AgentState L K))
    (h : phase9ConsensusEndpoint (L := L) (K := K) init c)
    (hreach : (NonuniformMajority L K).Reachable c c') :
    phase9ConsensusEndpoint (L := L) (K := K) init c' := by
  rcases h with ⟨hmaj, hc⟩ | ⟨hmaj, hc⟩ | ⟨hmaj, hc⟩
  · exact Or.inl ⟨hmaj,
      phase9_A_signs_preserved_by_reachable (L := L) (K := K) c c' hc hreach⟩
  · exact Or.inr (Or.inl ⟨hmaj,
      phase9_B_signs_preserved_by_reachable (L := L) (K := K) c c' hc hreach⟩)
  · exact Or.inr (Or.inr ⟨hmaj,
      phase9_T_signs_preserved_by_reachable (L := L) (K := K) c c' hc hreach⟩)

/-! ## Phase-4 tie endpoints -/

private theorem four_lt_eleven : 4 < 11 := by omega

private def phase4NoBigBias (a : AgentState L K) : Prop :=
  match a.bias with
  | .zero => True
  | .dyadic _ i => ¬ i.val < L

private def phase4TieWith (c : Config (AgentState L K)) : Prop :=
  ∀ a ∈ c, a.phase.val = 4 ∧ a.output = .T ∧ phase4NoBigBias (L := L) (K := K) a

/-- Phase-4 tie endpoint: all agents are in Phase 4, report tie, and no agent
has a dyadic bias exponent strictly below `L`, so Phase 4 has no big-bias
trigger left.  The endpoint also records that the initial majority verdict is
tie; this is the mathematical condition needed for the unanimous `T` output to
be the correct stable output. -/
def phase4TieEndpoint
    (init c : Config (AgentState L K)) : Prop :=
  majorityVerdict init = outputTripleOfOutput .T ∧
    phase4TieWith (L := L) (K := K) c

theorem phase4TieEndpoint_of_data
    (init c : Config (AgentState L K))
    (hmajor : majorityVerdict init = outputTripleOfOutput .T)
    (h : ∀ a ∈ c, a.phase.val = 4 ∧ a.output = .T ∧
      ∀ sgn i, a.bias = Bias.dyadic sgn i → ¬ i.val < L) :
    phase4TieEndpoint (L := L) (K := K) init c := by
  refine ⟨hmajor, ?_⟩
  intro a ha
  rcases h a ha with ⟨hphase, hout, hbias⟩
  refine ⟨hphase, hout, ?_⟩
  unfold phase4NoBigBias
  cases hb : a.bias with
  | zero =>
      trivial
  | dyadic sgn i =>
      exact hbias sgn i hb

private lemma phase_eq_four (a : AgentState L K) (h : a.phase.val = 4) :
    a.phase = ⟨4, four_lt_eleven⟩ := by
  exact Fin.ext h

private lemma phaseEpidemicUpdate_eq_self_of_phase4
    (s t : AgentState L K)
    (hs_phase : s.phase = ⟨4, four_lt_eleven⟩)
    (ht_phase : t.phase = ⟨4, four_lt_eleven⟩) :
    phaseEpidemicUpdate L K s t = (s, t) := by
  unfold phaseEpidemicUpdate
  rw [hs_phase, ht_phase, max_self]
  simp only [runInitsBetween_self]
  cases s
  cases t
  simp_all

private lemma Phase4Transition_eq_self_of_noBigBias
    (s t : AgentState L K)
    (hs : phase4NoBigBias (L := L) (K := K) s)
    (ht : phase4NoBigBias (L := L) (K := K) t) :
    Phase4Transition L K s t = (s, t) := by
  rcases s with
    ⟨sinput, soutput, sphase, srole, sassigned, sbias, ssmallBias,
      shour, sminute, sfull, sopinions, scounter⟩
  rcases t with
    ⟨tinput, toutput, tphase, trole, tassigned, tbias, tsmallBias,
      thour, tminute, tfull, topinions, tcounter⟩
  unfold phase4NoBigBias at hs ht
  unfold Phase4Transition
  dsimp at hs ht ⊢
  cases sbias with
  | zero =>
      cases tbias with
      | zero => simp
      | dyadic sgn i =>
          simp [ht]
  | dyadic sgn i =>
      cases tbias with
      | zero =>
          simp [hs]
      | dyadic sgn' j =>
          simp [hs, ht]

private theorem Transition_preserves_phase4Tie
    (s t : AgentState L K)
    (hs_phase : s.phase.val = 4) (ht_phase : t.phase.val = 4)
    (hs_out : s.output = .T) (ht_out : t.output = .T)
    (hs_no : phase4NoBigBias (L := L) (K := K) s)
    (ht_no : phase4NoBigBias (L := L) (K := K) t) :
    ((Transition L K s t).1.phase.val = 4 ∧
      (Transition L K s t).1.output = .T ∧
      phase4NoBigBias (L := L) (K := K) (Transition L K s t).1) ∧
    ((Transition L K s t).2.phase.val = 4 ∧
      (Transition L K s t).2.output = .T ∧
      phase4NoBigBias (L := L) (K := K) (Transition L K s t).2) := by
  have hs_phase_eq := phase_eq_four (L := L) (K := K) s hs_phase
  have ht_phase_eq := phase_eq_four (L := L) (K := K) t ht_phase
  have hepidemic := phaseEpidemicUpdate_eq_self_of_phase4 (L := L) (K := K)
    s t hs_phase_eq ht_phase_eq
  have hphase4 := Phase4Transition_eq_self_of_noBigBias (L := L) (K := K) s t hs_no ht_no
  simp [Transition, hepidemic, hs_phase_eq, ht_phase_eq, hphase4]
  exact ⟨⟨hs_out, hs_no⟩, ⟨ht_out, ht_no⟩⟩

private theorem phase4Tie_preserved_by_step
    (c c' : Config (AgentState L K))
    (h_c : phase4TieWith (L := L) (K := K) c)
    (h_step : (NonuniformMajority L K).StepRel c c') :
    phase4TieWith (L := L) (K := K) c' := by
  rcases h_step with ⟨r₁, r₂, happ, hc'⟩
  dsimp [Protocol.Applicable, NonuniformMajority] at happ hc'
  have hr₁_mem : r₁ ∈ c := Multiset.mem_of_le happ (by simp)
  have hr₂_mem : r₂ ∈ c := Multiset.mem_of_le happ (by simp)
  rcases h_c r₁ hr₁_mem with ⟨hr₁_phase, hr₁_out, hr₁_no⟩
  rcases h_c r₂ hr₂_mem with ⟨hr₂_phase, hr₂_out, hr₂_no⟩
  have htrans := Transition_preserves_phase4Tie (L := L) (K := K)
    r₁ r₂ hr₁_phase hr₂_phase hr₁_out hr₂_out hr₁_no hr₂_no
  rw [hc']
  intro a ha
  simp only [Multiset.mem_add, Multiset.mem_cons, Multiset.mem_singleton] at ha
  rcases ha with h_old | h_new
  · exact h_c a (Multiset.mem_of_le (Multiset.sub_le_self c {r₁, r₂}) h_old)
  · rcases h_new with h_eq | h_eq
    · simpa [h_eq] using htrans.1
    · simpa [h_eq] using htrans.2

private theorem phase4Tie_preserved_by_reachable
    (c c' : Config (AgentState L K))
    (h_c : phase4TieWith (L := L) (K := K) c)
    (h_reach : (NonuniformMajority L K).Reachable c c') :
    phase4TieWith (L := L) (K := K) c' := by
  induction h_reach with
  | refl => exact h_c
  | tail _ hstep ih =>
      exact phase4Tie_preserved_by_step (L := L) (K := K) _ _ ih hstep

private theorem doutPartition_output_of_phase4TieWith
    (c : Config (AgentState L K))
    (h : phase4TieWith (L := L) (K := K) c) :
    (doutPartition L K).output (outputTripleOfOutput .T) c :=
  doutPartition_output_of_unanimous_output (L := L) (K := K) c .T
    (fun a ha => (h a ha).2.1)

theorem phase4TieEndpoint_output
    (init c : Config (AgentState L K))
    (h : phase4TieEndpoint (L := L) (K := K) init c) :
    (doutPartition L K).output (majorityVerdict init) c := by
  rcases h with ⟨hmaj, hc⟩
  rw [hmaj]
  exact doutPartition_output_of_phase4TieWith (L := L) (K := K) c hc

theorem phase4TieEndpoint_isStable
    (init c : Config (AgentState L K))
    (h : phase4TieEndpoint (L := L) (K := K) init c) :
    (NonuniformMajority L K).IsStable (doutPartition L K) c := by
  refine ⟨majorityVerdict init, phase4TieEndpoint_output
    (L := L) (K := K) init c h, ?_⟩
  intro c' hreach
  rcases h with ⟨hmaj, hc⟩
  rw [hmaj]
  exact doutPartition_output_of_phase4TieWith (L := L) (K := K) c'
    (phase4Tie_preserved_by_reachable (L := L) (K := K) c c' hc hreach)

theorem stable_output_of_phase4TieEndpoint
    (init c : Config (AgentState L K))
    (h : phase4TieEndpoint (L := L) (K := K) init c) :
    (doutPartition L K).output (majorityVerdict init) c ∧
      (NonuniformMajority L K).IsStable (doutPartition L K) c :=
  ⟨phase4TieEndpoint_output (L := L) (K := K) init c h,
    phase4TieEndpoint_isStable (L := L) (K := K) init c h⟩

/-- Phase-4 tie endpoints remain Phase-4 tie endpoints along every reachable
execution. -/
theorem phase4TieEndpoint_preserved_by_reachable
    (init c c' : Config (AgentState L K))
    (h : phase4TieEndpoint (L := L) (K := K) init c)
    (hreach : (NonuniformMajority L K).Reachable c c') :
    phase4TieEndpoint (L := L) (K := K) init c' := by
  rcases h with ⟨hmaj, hc⟩
  exact ⟨hmaj, phase4Tie_preserved_by_reachable (L := L) (K := K) c c' hc hreach⟩

/-! ## Combined deterministic stable endpoint -/

/-- Combined deterministic endpoint predicate for currently formalized stable
end states: Phase 2 consensus, Phase 4 tie, Phase 9 consensus, or the existing
Phase 10 stable-backup majority witness. -/
def majorityStableEndpoint
    (init c : Config (AgentState L K)) : Prop :=
  phase2ConsensusEndpoint (L := L) (K := K) init c ∨
  phase4TieEndpoint (L := L) (K := K) init c ∨
  phase9ConsensusEndpoint (L := L) (K := K) init c ∨
  phase10MajorityWitness (L := L) (K := K) init c

theorem stable_output_of_majorityStableEndpoint
    (init c : Config (AgentState L K))
    (h : majorityStableEndpoint (L := L) (K := K) init c) :
    (doutPartition L K).output (majorityVerdict init) c ∧
      (NonuniformMajority L K).IsStable (doutPartition L K) c := by
  rcases h with h2 | h4 | h9 | h10
  · exact stable_output_of_phase2ConsensusEndpoint (L := L) (K := K) init c h2
  · exact stable_output_of_phase4TieEndpoint (L := L) (K := K) init c h4
  · exact stable_output_of_phase9ConsensusEndpoint (L := L) (K := K) init c h9
  · exact stable_output_of_phase10MajorityWitness (L := L) (K := K) init c h10

/-- Stable witness form for the combined deterministic endpoint predicate. -/
theorem stable_witness_of_majorityStableEndpoint
    (init c final : Config (AgentState L K))
    (hreach : (NonuniformMajority L K).Reachable c final)
    (hfinal : majorityStableEndpoint (L := L) (K := K) init final) :
    ∃ o, (NonuniformMajority L K).Reachable c o ∧
      (doutPartition L K).output (majorityVerdict init) o ∧
      (NonuniformMajority L K).IsStable (doutPartition L K) o := by
  refine ⟨final, hreach, ?_, ?_⟩
  · exact (stable_output_of_majorityStableEndpoint
      (L := L) (K := K) init final hfinal).1
  · exact (stable_output_of_majorityStableEndpoint
      (L := L) (K := K) init final hfinal).2

/-- Correctness reduction for phase analyses that can reach any of the
currently formalized stable endpoint forms. -/
theorem stable_majority_correct_of_majorityStableEndpoint_reachability
    (hphase :
      ∀ init : Config (AgentState L K), validInitial init →
        ∀ c : Config (AgentState L K),
          (NonuniformMajority L K).Reachable init c →
            ∃ final : Config (AgentState L K),
              (NonuniformMajority L K).Reachable c final ∧
                majorityStableEndpoint (L := L) (K := K) init final) :
    Protocol.StablyComputes (NonuniformMajority L K) (doutPartition L K)
      (validInitial) (majorityVerdict) := by
  intro init hinit c hreach
  rcases hphase init hinit c hreach with ⟨final, hfinal_reach, hfinal⟩
  exact stable_witness_of_majorityStableEndpoint
    (L := L) (K := K) init c final hfinal_reach hfinal

theorem nonuniform_majority_correctness_of_majorityStableEndpoint_reachability
    (hphase :
      ∀ init : Config (AgentState L K), validInitial init →
        ∀ c : Config (AgentState L K),
          (NonuniformMajority L K).Reachable init c →
            ∃ final : Config (AgentState L K),
              (NonuniformMajority L K).Reachable c final ∧
                majorityStableEndpoint (L := L) (K := K) init final) :
    Protocol.StablyComputes (NonuniformMajority L K) (doutPartition L K)
      (validInitial) (majorityVerdict) :=
  stable_majority_correct_of_majorityStableEndpoint_reachability
    (L := L) (K := K) hphase

end ExactMajority
