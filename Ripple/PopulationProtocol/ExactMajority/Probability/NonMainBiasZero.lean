/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Non-Main agents carry no dyadic bias in Phases 3–9

The Phase-3 Init writes `bias := .zero` on every non-Main role, every later
bias-writing reaction is Main–Main guarded (`phase3CancelSplit`,
`cancelSplit`, `absorbConsume`) or converts the recipient to Main in the same
update (`doSplit`), and the only entries into Phases `≥ 3` that skip the
Phase-3 Init are the error jumps into the exempt Phase 10.  Hence along every
real execution from a valid initial configuration, an agent that is not Main
and sits in a phase in `[3, 9]` has bias exactly `.zero`.

This is the reachable discharge of the `hnonmain` hypothesis of the
outcome-seed bridge (`OutcomeOriginLedger.seed_of_drained_*`): at an
all-Phase-8 drained endpoint, `minorityU σ = 0` only rules out Main
carriers, and this invariant rules out everyone else.
-/

import Ripple.PopulationProtocol.ExactMajority.Analysis.Invariants

namespace Ripple.PopulationProtocol.ExactMajority
namespace NonMainBiasZero

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-! ## The pointwise predicate -/

/-- A non-Main agent in the dyadic window `3 ≤ phase ≤ 9` carries bias zero. -/
def agentOk (a : AgentState L K) : Prop :=
  a.role ≠ .main → 3 ≤ a.phase.val → a.phase.val ≤ 9 → a.bias = .zero

/-- Configuration-level invariant. -/
def NonMainBiasZeroInv (c : Config (AgentState L K)) : Prop :=
  ∀ a ∈ c, agentOk a

theorem agentOk_of_phase_lt_three (a : AgentState L K)
    (h : a.phase.val < 3) : agentOk a := by
  intro _ h3 _
  omega

theorem agentOk_of_phase_eq_ten (a : AgentState L K)
    (h : a.phase.val = 10) : agentOk a := by
  intro _ _ h9
  omega

theorem agentOk_of_role_main (a : AgentState L K)
    (h : a.role = .main) : agentOk a := by
  intro hrole
  exact (hrole h).elim

theorem agentOk_of_bias_zero (a : AgentState L K)
    (h : a.bias = .zero) : agentOk a := by
  intro _ _ _
  exact h

/-- Transport along an agent with the same role, phase, and bias. -/
theorem agentOk_congr {a b : AgentState L K}
    (ha : agentOk a) (hrole : b.role = a.role) (hphase : b.phase = a.phase)
    (hbias : b.bias = a.bias) : agentOk b := by
  intro hb h3 h9
  rw [hbias]
  rw [hphase] at h3 h9
  exact ha (by rw [← hrole]; exact hb) h3 h9

/-! ## Per-init facts -/

private lemma phaseInit_role_ne_main (p : Fin 11) (a : AgentState L K)
    (ha : a.role ≠ .main) : (phaseInit L K p a).role ≠ .main := by
  rcases a with
    ⟨input, output, phase, role, assigned, bias, smallBias,
      hour, minute, full, opinions, counter⟩
  cases role <;> fin_cases p <;>
    simp [phaseInit, enterPhase10] at ha ⊢ <;>
    repeat' split_ifs <;> simp_all

private lemma phaseInit_role_main (p : Fin 11) (a : AgentState L K)
    (ha : a.role = .main) : (phaseInit L K p a).role = .main := by
  rcases a with
    ⟨input, output, phase, role, assigned, bias, smallBias,
      hour, minute, full, opinions, counter⟩
  cases role <;> fin_cases p <;>
    simp [phaseInit, enterPhase10] at ha ⊢ <;>
    repeat' split_ifs <;> simp_all

/-- The stable core: non-Main and (bias already zero, or parked at the error
phase 10).  Every single `phaseInit` preserves it. -/
private def S (a : AgentState L K) : Prop :=
  a.role ≠ .main ∧ (a.bias = .zero ∨ a.phase.val = 10)

private lemma phaseInit_S (p : Fin 11) (a : AgentState L K)
    (ha : S a) : S (phaseInit L K p a) := by
  obtain ⟨hrole, hcore⟩ := ha
  refine ⟨phaseInit_role_ne_main p a hrole, ?_⟩
  rcases a with
    ⟨input, output, phase, role, assigned, bias, smallBias,
      hour, minute, full, opinions, counter⟩
  cases role <;> fin_cases p <;>
    simp [phaseInit, enterPhase10, phase10] at hrole hcore ⊢ <;>
    (repeat' split_ifs) <;> simp_all

/-- Phase-3 Init writes `bias := .zero` on every non-Main role. -/
private lemma phaseInit_three_establishes (a : AgentState L K)
    (ha : a.role ≠ .main) :
    S (phaseInit L K ⟨3, by decide⟩ a) := by
  refine ⟨phaseInit_role_ne_main _ a ha, Or.inl ?_⟩
  rcases a with
    ⟨input, output, phase, role, assigned, bias, smallBias,
      hour, minute, full, opinions, counter⟩
  cases role <;> simp_all [phaseInit]

private lemma phaseInit_phase_eq_or_ten (p : Fin 11) (a : AgentState L K) :
    (phaseInit L K p a).phase.val = a.phase.val ∨
      (phaseInit L K p a).phase.val = 10 := by
  rcases a with
    ⟨input, output, phase, role, assigned, bias, smallBias,
      hour, minute, full, opinions, counter⟩
  cases role <;> fin_cases p <;>
    simp [phaseInit, enterPhase10, phase10] <;>
    repeat' split_ifs <;> simp_all

/-! ## Order-free fold lemmas -/

private def initFold (lst : List ℕ) (a : AgentState L K) : AgentState L K :=
  lst.foldl (fun acc k => if h : k < 11 then phaseInit L K ⟨k, h⟩ acc else acc) a

private lemma initFold_role_ne_main (lst : List ℕ) (a : AgentState L K)
    (ha : a.role ≠ .main) : (initFold (L := L) (K := K) lst a).role ≠ .main := by
  induction lst generalizing a with
  | nil => simpa [initFold] using ha
  | cons k l ih =>
      simp only [initFold, List.foldl_cons]
      by_cases hk : k < 11
      · rw [dif_pos hk]
        exact ih _ (phaseInit_role_ne_main ⟨k, hk⟩ a ha)
      · rw [dif_neg hk]
        exact ih a ha

private lemma initFold_role_main (lst : List ℕ) (a : AgentState L K)
    (ha : a.role = .main) : (initFold (L := L) (K := K) lst a).role = .main := by
  induction lst generalizing a with
  | nil => simpa [initFold] using ha
  | cons k l ih =>
      simp only [initFold, List.foldl_cons]
      by_cases hk : k < 11
      · rw [dif_pos hk]
        exact ih _ (phaseInit_role_main ⟨k, hk⟩ a ha)
      · rw [dif_neg hk]
        exact ih a ha

private lemma initFold_S (lst : List ℕ) (a : AgentState L K)
    (ha : S a) : S (initFold (L := L) (K := K) lst a) := by
  induction lst generalizing a with
  | nil => simpa [initFold] using ha
  | cons k l ih =>
      simp only [initFold, List.foldl_cons]
      by_cases hk : k < 11
      · rw [dif_pos hk]
        exact ih _ (phaseInit_S ⟨k, hk⟩ a ha)
      · rw [dif_neg hk]
        exact ih a ha

private lemma initFold_phase_eq_or_ten (lst : List ℕ) (a : AgentState L K) :
    (initFold (L := L) (K := K) lst a).phase.val = a.phase.val ∨
      (initFold (L := L) (K := K) lst a).phase.val = 10 := by
  induction lst generalizing a with
  | nil => simp [initFold]
  | cons k l ih =>
      simp only [initFold, List.foldl_cons]
      by_cases hk : k < 11
      · rw [dif_pos hk]
        rcases ih (phaseInit L K ⟨k, hk⟩ a) with h | h
        · rcases phaseInit_phase_eq_or_ten ⟨k, hk⟩ a with h' | h'
          · exact Or.inl (h.trans h')
          · exact Or.inr (h.trans h')
        · exact Or.inr h
      · rw [dif_neg hk]
        exact ih a

/-- Crossing the Phase-3 Init inside a fold puts every non-Main agent
into the stable core, regardless of where it started. -/
private lemma initFold_crossing_three (lst : List ℕ) (h3 : 3 ∈ lst)
    (a : AgentState L K) (ha : a.role ≠ .main) :
    S (initFold (L := L) (K := K) lst a) := by
  obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem h3
  have hsplit : initFold (L := L) (K := K) (l₁ ++ 3 :: l₂) a =
      initFold (L := L) (K := K) l₂
        (phaseInit L K ⟨3, by decide⟩ (initFold (L := L) (K := K) l₁ a)) := by
    simp only [initFold, List.foldl_append, List.foldl_cons]
    rw [dif_pos (by norm_num : (3 : ℕ) < 11)]
  rw [hsplit]
  exact initFold_S l₂ _
    (phaseInit_three_establishes _ (initFold_role_ne_main l₁ a ha))

/-! ## `runInitsBetween` consequences -/

private lemma runInitsBetween_eq_initFold (oldP newP : ℕ) (a : AgentState L K) :
    runInitsBetween L K oldP newP a =
      initFold (L := L) (K := K)
        ((List.range 11).filter (fun k => oldP < k ∧ k ≤ newP)) a := rfl

private lemma agentOk_of_S (a : AgentState L K) (ha : S a) : agentOk a := by
  intro _ _ h9
  rcases ha.2 with hzero | hten
  · exact hzero
  · omega

/-- The raised-and-initialized agent of the phase epidemic satisfies the
pointwise invariant. -/
private lemma epidemic_leg_agentOk (a : AgentState L K) (p : ℕ) (hp : p < 11)
    (hap : a.phase.val ≤ p) (ha : agentOk a) :
    agentOk (runInitsBetween L K a.phase.val p
      ({ a with phase := ⟨p, hp⟩ } : AgentState L K)) := by
  set a' : AgentState L K := { a with phase := ⟨p, hp⟩ } with ha'
  rw [runInitsBetween_eq_initFold]
  by_cases hmain : a.role = .main
  · exact agentOk_of_role_main _
      (initFold_role_main _ a' (by simp [ha', hmain]))
  have ha'role : a'.role ≠ .main := by simpa [ha'] using hmain
  by_cases hp3 : p < 3
  · -- Target below the dyadic window: output phase is `p < 3` or the exempt 10.
    rcases initFold_phase_eq_or_ten
        ((List.range 11).filter (fun k => a.phase.val < k ∧ k ≤ p)) a' with h | h
    · exact agentOk_of_phase_lt_three _ (by rw [h]; simpa [ha'] using hp3)
    · exact agentOk_of_phase_eq_ten _ h
  · by_cases hp9 : p ≤ 9
    · by_cases haphase : 3 ≤ a.phase.val
      · -- Already inside the window: bias is zero and stays zero.
        have hbias : a.bias = .zero := ha hmain haphase (by omega)
        exact agentOk_of_S _ (initFold_S _ a' ⟨ha'role, Or.inl (by simp [ha', hbias])⟩)
      · -- Entering the window: the chain runs the Phase-3 Init.
        have h3mem : 3 ∈ (List.range 11).filter
            (fun k => a.phase.val < k ∧ k ≤ p) := by
          simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
          omega
        exact agentOk_of_S _ (initFold_crossing_three _ h3mem a' ha'role)
    · -- Target is the exempt phase 10.
      have hp10 : p = 10 := by omega
      rcases initFold_phase_eq_or_ten
          ((List.range 11).filter (fun k => a.phase.val < k ∧ k ≤ p)) a' with h | h
      · exact agentOk_of_phase_eq_ten _ (by rw [h]; simp [ha', hp10])
      · exact agentOk_of_phase_eq_ten _ h

/-- Pointwise invariance through the full phase-epidemic update. -/
theorem phaseEpidemicUpdate_agentOk (s t : AgentState L K)
    (hs : agentOk s) (ht : agentOk t) :
    agentOk (phaseEpidemicUpdate L K s t).1 ∧
      agentOk (phaseEpidemicUpdate L K s t).2 := by
  unfold phaseEpidemicUpdate
  dsimp only
  have hmax_lt : (max s.phase t.phase).val < 11 := (max s.phase t.phase).2
  have hs_le : s.phase.val ≤ (max s.phase t.phase).val :=
    le_max_left s.phase t.phase
  have ht_le : t.phase.val ≤ (max s.phase t.phase).val :=
    le_max_right s.phase t.phase
  have hs_raised :
      ({ s with phase := max s.phase t.phase } : AgentState L K) =
        ({ s with phase := ⟨(max s.phase t.phase).val, hmax_lt⟩ } : AgentState L K) := by
    rfl
  have ht_raised :
      ({ t with phase := max s.phase t.phase } : AgentState L K) =
        ({ t with phase := ⟨(max s.phase t.phase).val, hmax_lt⟩ } : AgentState L K) := by
    rfl
  have hs' : agentOk (runInitsBetween L K s.phase.val (max s.phase t.phase).val
      ({ s with phase := max s.phase t.phase } : AgentState L K)) := by
    rw [hs_raised]
    exact epidemic_leg_agentOk s (max s.phase t.phase).val hmax_lt hs_le hs
  have ht' : agentOk (runInitsBetween L K t.phase.val (max s.phase t.phase).val
      ({ t with phase := max s.phase t.phase } : AgentState L K)) := by
    rw [ht_raised]
    exact epidemic_leg_agentOk t (max s.phase t.phase).val hmax_lt ht_le ht
  split_ifs with hcond
  · -- Phase-10 epidemic entry: each output is either the exempt phase-10
    -- entry or the (already handled) initialized leg itself.
    refine ⟨?_, ?_⟩
    · dsimp only
      unfold phase10EpidemicEntry
      split_ifs with hbefore
      · exact agentOk_of_phase_eq_ten _ (by simp [enterPhase10, phase10])
      · exact hs'
    · dsimp only
      unfold phase10EpidemicEntry
      split_ifs with hbefore
      · exact agentOk_of_phase_eq_ten _ (by simp [enterPhase10, phase10])
      · exact ht'
  · exact ⟨hs', ht'⟩

/-! ## Base case -/

theorem nonMainBiasZeroInv_validInitial (init : Config (AgentState L K))
    (hvalid : validInitial init) :
    NonMainBiasZeroInv init := by
  intro a ha
  apply agentOk_of_phase_lt_three
  rw [(hvalid a ha).1]
  decide

/-! ## Field-transport helpers -/

/-- Transport for a non-Main source whose target keeps phase and bias
(the target's role is irrelevant). -/
theorem agentOk_of_fields {a b : AgentState L K}
    (ha : agentOk a) (haRole : a.role ≠ .main)
    (hphase : b.phase = a.phase) (hbias : b.bias = a.bias) : agentOk b := by
  intro _ h3 h9
  rw [hbias]
  rw [hphase] at h3 h9
  exact ha haRole h3 h9

/-! ## Single-init and counter-subroutine preservation -/

private lemma phaseInit_bias_eq_of_ne_three (p : Fin 11) (hp : p.val ≠ 3)
    (a : AgentState L K) : (phaseInit L K p a).bias = a.bias := by
  rcases a with
    ⟨input, output, phase, role, assigned, bias, smallBias,
      hour, minute, full, opinions, counter⟩
  cases role <;> fin_cases p <;>
    simp_all [phaseInit, enterPhase10] <;>
    (repeat' split_ifs) <;> simp_all

/-- A single `phaseInit` preserves the pointwise invariant unconditionally:
it never raises the phase (except into the exempt 10), the only bias write is
the Phase-3 zeroing of non-Mains, and Main never loses its role. -/
private lemma phaseInit_agentOk (p : Fin 11) (a : AgentState L K)
    (ha : agentOk a) : agentOk (phaseInit L K p a) := by
  by_cases hmain : a.role = .main
  · exact agentOk_of_role_main _ (phaseInit_role_main p a hmain)
  by_cases hp3 : p.val = 3
  · have hp : p = ⟨3, by decide⟩ := Fin.ext hp3
    subst hp
    exact agentOk_of_S _ (phaseInit_three_establishes a hmain)
  · intro _ h3 h9
    rw [phaseInit_bias_eq_of_ne_three p hp3 a]
    rcases phaseInit_phase_eq_or_ten p a with h | h
    · rw [h] at h3 h9
      exact ha hmain h3 h9
    · rw [h] at h9
      omega

private lemma advancePhase_bias (a : AgentState L K) :
    (advancePhase L K a).bias = a.bias := by
  unfold advancePhase
  split <;> rfl

private lemma advancePhase_role (a : AgentState L K) :
    (advancePhase L K a).role = a.role := by
  unfold advancePhase
  split <;> rfl

private lemma advancePhase_phase_of_lt (a : AgentState L K)
    (h : a.phase.val < 10) : (advancePhase L K a).phase.val = a.phase.val + 1 := by
  unfold advancePhase
  rw [dif_pos h]

private lemma advancePhase_phase_of_ge (a : AgentState L K)
    (h : ¬ a.phase.val < 10) : (advancePhase L K a).phase.val = a.phase.val := by
  unfold advancePhase
  rw [dif_neg h]

/-- The bare `advancePhase` (no Init) is safe away from the 2→3 boundary. -/
private lemma agentOk_advancePhase_of_ne_two (a : AgentState L K)
    (h2 : a.phase.val ≠ 2) (ha : agentOk a) :
    agentOk (advancePhase L K a) := by
  intro hrole h3 h9
  rw [advancePhase_bias]
  have hrole' : a.role ≠ .main := by
    rw [← advancePhase_role a]; exact hrole
  by_cases hlt : a.phase.val < 10
  · rw [advancePhase_phase_of_lt a hlt] at h3 h9
    exact ha hrole' (by omega) (by omega)
  · rw [advancePhase_phase_of_ge a hlt] at h3 h9
    exact ha hrole' h3 h9

/-- `advancePhaseWithInit` preserves the invariant unconditionally: the 2→3
boundary is exactly where the Phase-3 Init re-establishes it. -/
private lemma advancePhaseWithInit_agentOk (a : AgentState L K)
    (ha : agentOk a) : agentOk (advancePhaseWithInit L K a) := by
  unfold advancePhaseWithInit
  dsimp only
  by_cases hmain : a.role = .main
  · exact agentOk_of_role_main _
      (phaseInit_role_main _ _ (by rw [advancePhase_role]; exact hmain))
  by_cases h2 : a.phase.val = 2
  · have hphase3 : (advancePhase L K a).phase = ⟨3, by decide⟩ := by
      apply Fin.ext
      rw [advancePhase_phase_of_lt a (by omega), h2]
    rw [hphase3]
    exact agentOk_of_S _
      (phaseInit_three_establishes _ (by rw [advancePhase_role]; exact hmain))
  · exact phaseInit_agentOk _ _ (agentOk_advancePhase_of_ne_two a h2 ha)

private lemma stdCounterSubroutine_agentOk (a : AgentState L K)
    (ha : agentOk a) : agentOk (stdCounterSubroutine L K a) := by
  unfold stdCounterSubroutine
  split_ifs
  · exact advancePhaseWithInit_agentOk a ha
  · exact agentOk_congr ha rfl rfl rfl

private lemma clockCounterStep_agentOk (a : AgentState L K)
    (ha : agentOk a) : agentOk (clockCounterStep L K a) := by
  unfold clockCounterStep
  split_ifs
  · exact stdCounterSubroutine_agentOk a ha
  · exact ha

/-! ## Per-phase dispatcher preservation -/

private lemma Phase0Transition_agentOk (s t : AgentState L K)
    (hs : agentOk s) (ht : agentOk t) :
    agentOk (Phase0Transition L K s t).1 ∧ agentOk (Phase0Transition L K s t).2 := by
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
  have hs1 : agentOk s1 := by
    dsimp [s1]
    split_ifs with h
    · exact agentOk_of_role_main _ (by simp)
    · exact hs
  have ht1 : agentOk t1 := by
    dsimp [t1]
    split_ifs with h
    · exact agentOk_of_fields ht (by simp [h.2]) (by simp) (by simp)
    · exact ht
  have hs2 : agentOk s2 := by
    dsimp [s2]
    split_ifs with hleft hright
    · exact agentOk_of_fields hs1 (by simp [hleft.1]) (by simp) (by simp)
    · exact agentOk_congr hs1 (by simp) (by simp) (by simp)
    · exact hs1
  have ht2 : agentOk t2 := by
    dsimp [t2]
    split_ifs with hleft hright
    · exact agentOk_congr ht1 (by simp) (by simp) (by simp)
    · exact agentOk_of_fields ht1 (by simp [hright.1]) (by simp) (by simp)
    · exact ht1
  have hs3 : agentOk s3 := by
    dsimp [s3]
    split_ifs with h1 h2
    · exact agentOk_of_role_main _ (by simp)
    · exact agentOk_congr hs2 (by simp) (by simp) (by simp)
    · exact hs2
  have ht3 : agentOk t3 := by
    dsimp [t3]
    split_ifs with h1 h2
    · exact agentOk_congr ht2 (by simp) (by simp) (by simp)
    · exact agentOk_of_role_main _ (by simp)
    · exact ht2
  have hs3' : agentOk s3' := hs3
  have ht3' : agentOk t3' := ht3
  have hs4 : agentOk s4 := by
    dsimp [s4]
    split_ifs with hcr
    · exact agentOk_of_fields hs3' (by simp [hcr.1]) (by simp) (by simp)
    · exact hs3'
  have ht4 : agentOk t4 := by
    dsimp [t4]
    split_ifs with hcr
    · exact agentOk_of_fields ht3' (by simp [hcr.2]) (by simp) (by simp)
    · exact ht3'
  have hs5 : agentOk s5 := by
    dsimp [s5]
    split_ifs with hclock
    · exact stdCounterSubroutine_agentOk s4 hs4
    · exact hs4
  have ht5 : agentOk t5 := by
    dsimp [t5]
    split_ifs with hclock
    · exact stdCounterSubroutine_agentOk t4 ht4
    · exact ht4
  exact ⟨hs5, ht5⟩

private lemma Phase1Transition_agentOk (s t : AgentState L K)
    (hs : agentOk s) (ht : agentOk t) :
    agentOk (Phase1Transition L K s t).1 ∧ agentOk (Phase1Transition L K s t).2 := by
  unfold Phase1Transition
  dsimp only
  split_ifs with h
  · exact ⟨clockCounterStep_agentOk _ (agentOk_congr hs (by simp) (by simp) (by simp)),
      clockCounterStep_agentOk _ (agentOk_congr ht (by simp) (by simp) (by simp))⟩
  · exact ⟨clockCounterStep_agentOk _ hs, clockCounterStep_agentOk _ ht⟩

private lemma Phase2Transition_agentOk (s t : AgentState L K)
    (hs : agentOk s) (ht : agentOk t) :
    agentOk (Phase2Transition L K s t).1 ∧ agentOk (Phase2Transition L K s t).2 := by
  unfold Phase2Transition
  dsimp only
  have hs' : agentOk ({ s with opinions := opinionsUnion s.opinions t.opinions }) :=
    agentOk_congr hs (by simp) (by simp) (by simp)
  have ht' : agentOk ({ t with opinions := opinionsUnion s.opinions t.opinions }) :=
    agentOk_congr ht (by simp) (by simp) (by simp)
  split_ifs with h1 h2 h3 h4
  · exact ⟨advancePhaseWithInit_agentOk _ hs', advancePhaseWithInit_agentOk _ ht'⟩
  · exact ⟨agentOk_congr hs' (by simp) (by simp) (by simp),
      agentOk_congr ht' (by simp) (by simp) (by simp)⟩
  · exact ⟨agentOk_congr hs' (by simp) (by simp) (by simp),
      agentOk_congr ht' (by simp) (by simp) (by simp)⟩
  · exact ⟨agentOk_congr hs' (by simp) (by simp) (by simp),
      agentOk_congr ht' (by simp) (by simp) (by simp)⟩
  · exact ⟨hs', ht'⟩

private lemma phase3CancelSplit_role (s t : AgentState L K) :
    (phase3CancelSplit L K s t).1.role = s.role ∧
      (phase3CancelSplit L K s t).2.role = t.role := by
  unfold phase3CancelSplit
  match s.bias, t.bias with
  | .zero, .zero => simp
  | .zero, .dyadic _ _ => simp only; split_ifs <;> simp
  | .dyadic _ _, .zero => simp only; split_ifs <;> simp
  | .dyadic .pos _, .dyadic .pos _ => simp
  | .dyadic .pos _, .dyadic .neg _ => simp only; split_ifs <;> simp
  | .dyadic .neg _, .dyadic .pos _ => simp only; split_ifs <;> simp
  | .dyadic .neg _, .dyadic .neg _ => simp

private lemma Phase3Transition_agentOk (s t : AgentState L K)
    (hs : agentOk s) (ht : agentOk t) :
    agentOk (Phase3Transition L K s t).1 ∧ agentOk (Phase3Transition L K s t).2 := by
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
      exact (Nat.max_lt).mpr
        ⟨s1.hour.2, Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩
    { s1 with hour := ⟨hVal, h_hour_lt⟩ }
  else if t1.role = .main ∧ t1.bias = .zero ∧ s1.role = .clock then
    s1
  else s1
  let t2 := if s1.role = .main ∧ s1.bias = .zero ∧ t1.role = .clock then
    t1
  else if t1.role = .main ∧ t1.bias = .zero ∧ s1.role = .clock then
    let hVal := max t1.hour.val (min L (s1.minute.val / K))
    have h_hour_lt : hVal < L + 1 := by
      exact (Nat.max_lt).mpr
        ⟨t1.hour.2, Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩
    { t1 with hour := ⟨hVal, h_hour_lt⟩ }
  else t1
  have hs1 : agentOk s1 := by
    dsimp only [s1]
    split_ifs with h h' h''
    · exact agentOk_congr hs (by simp) (by simp) (by simp)
    · exact agentOk_congr hs (by simp) (by simp) (by simp)
    · exact stdCounterSubroutine_agentOk s hs
    · exact hs
  have ht1 : agentOk t1 := by
    dsimp only [t1]
    split_ifs with h h' h''
    · exact agentOk_congr ht (by simp) (by simp) (by simp)
    · exact ht
    · exact stdCounterSubroutine_agentOk t ht
    · exact ht
  have hs2 : agentOk s2 := by
    dsimp only [s2]
    split_ifs with h h'
    · exact agentOk_congr hs1 (by simp) (by simp) (by simp)
    · exact hs1
    · exact hs1
  have ht2 : agentOk t2 := by
    dsimp only [t2]
    split_ifs with h h'
    · exact ht1
    · exact agentOk_congr ht1 (by simp) (by simp) (by simp)
    · exact ht1
  have hfin : agentOk (if s2.role = .main ∧ t2.role = .main then
      phase3CancelSplit L K s2 t2 else (s2, t2)).1 ∧
      agentOk (if s2.role = .main ∧ t2.role = .main then
        phase3CancelSplit L K s2 t2 else (s2, t2)).2 := by
    split_ifs with hmm
    · constructor
      · exact agentOk_of_role_main _
          (by rw [(phase3CancelSplit_role s2 t2).1]; exact hmm.1)
      · exact agentOk_of_role_main _
          (by rw [(phase3CancelSplit_role s2 t2).2]; exact hmm.2)
    · exact ⟨hs2, ht2⟩
  exact hfin

/- 2026-07-16 Init-layer fix: `Phase4Transition` now advances via
`advancePhaseWithInit` (running the destination Init), so no phase-2
side condition is needed — `advancePhaseWithInit_agentOk` is unconditional. -/
private lemma Phase4Transition_agentOk (s t : AgentState L K)
    (hs : agentOk s) (ht : agentOk t) :
    agentOk (Phase4Transition L K s t).1 ∧ agentOk (Phase4Transition L K s t).2 := by
  unfold Phase4Transition
  dsimp only
  split_ifs
  · exact ⟨advancePhaseWithInit_agentOk s hs, advancePhaseWithInit_agentOk t ht⟩
  · exact ⟨hs, ht⟩

private lemma Phase5Transition_agentOk (s t : AgentState L K)
    (hs : agentOk s) (ht : agentOk t) :
    agentOk (Phase5Transition L K s t).1 ∧ agentOk (Phase5Transition L K s t).2 := by
  unfold Phase5Transition
  dsimp only
  constructor
  · split_ifs <;>
      first
      | exact stdCounterSubroutine_agentOk _
          (agentOk_congr hs (by simp) (by simp) (by simp))
      | exact agentOk_congr hs (by simp) (by simp) (by simp)
      | exact stdCounterSubroutine_agentOk _ hs
      | exact hs
  · split_ifs <;>
      first
      | exact stdCounterSubroutine_agentOk _
          (agentOk_congr ht (by simp) (by simp) (by simp))
      | exact agentOk_congr ht (by simp) (by simp) (by simp)
      | exact stdCounterSubroutine_agentOk _ ht
      | exact ht

private lemma doSplit_agentOk_fst (r m : AgentState L K)
    (hr : agentOk r) : agentOk (doSplit L K r m).1 := by
  unfold doSplit
  match m.bias with
  | .zero => exact hr
  | .dyadic sgn j =>
      dsimp only
      split_ifs with h1 h2
      · exact agentOk_of_role_main _ (by simp)
      · exact hr
      · exact hr

private lemma doSplit_agentOk_snd (r m : AgentState L K)
    (hm : m.role = .main) : agentOk (doSplit L K r m).2 :=
  agentOk_of_role_main _ (by rw [doSplit_role_snd]; exact hm)

private lemma Phase6Transition_agentOk (s t : AgentState L K)
    (hs : agentOk s) (ht : agentOk t) :
    agentOk (Phase6Transition L K s t).1 ∧ agentOk (Phase6Transition L K s t).2 := by
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
  have hs1 : agentOk s1 := by
    dsimp only [s1]
    split_ifs with h1 h2
    · exact doSplit_agentOk_fst s t hs
    · exact doSplit_agentOk_snd t s h2.2.1
    · exact hs
  have ht1 : agentOk t1 := by
    dsimp only [t1]
    split_ifs with h1 h2
    · exact doSplit_agentOk_snd s t h1.2.1
    · exact doSplit_agentOk_fst t s ht
    · exact ht
  have hfin : agentOk (if s1.role = .clock then stdCounterSubroutine L K s1 else s1) ∧
      agentOk (if t1.role = .clock then stdCounterSubroutine L K t1 else t1) := by
    constructor
    · split_ifs
      · exact stdCounterSubroutine_agentOk _ hs1
      · exact hs1
    · split_ifs
      · exact stdCounterSubroutine_agentOk _ ht1
      · exact ht1
  exact hfin

private lemma Phase7Transition_agentOk (s t : AgentState L K)
    (hs : agentOk s) (ht : agentOk t) :
    agentOk (Phase7Transition L K s t).1 ∧ agentOk (Phase7Transition L K s t).2 := by
  unfold Phase7Transition
  dsimp only
  constructor
  · split_ifs with h <;>
      first
      | exact stdCounterSubroutine_agentOk _ (agentOk_of_role_main _
          (by rw [cancelSplit_role_fst]; exact h.1))
      | exact agentOk_of_role_main _ (by rw [cancelSplit_role_fst]; exact h.1)
      | exact stdCounterSubroutine_agentOk _ hs
      | exact hs
  · split_ifs with h <;>
      first
      | exact stdCounterSubroutine_agentOk _ (agentOk_of_role_main _
          (by rw [cancelSplit_role_snd]; exact h.2))
      | exact agentOk_of_role_main _ (by rw [cancelSplit_role_snd]; exact h.2)
      | exact stdCounterSubroutine_agentOk _ ht
      | exact ht

private lemma Phase8Transition_agentOk (s t : AgentState L K)
    (hs : agentOk s) (ht : agentOk t) :
    agentOk (Phase8Transition L K s t).1 ∧ agentOk (Phase8Transition L K s t).2 := by
  unfold Phase8Transition
  dsimp only
  constructor
  · split_ifs with h <;>
      first
      | exact stdCounterSubroutine_agentOk _ (agentOk_of_role_main _
          (by rw [absorbConsume_role_fst]; exact h.1))
      | exact agentOk_of_role_main _ (by rw [absorbConsume_role_fst]; exact h.1)
      | exact stdCounterSubroutine_agentOk _ hs
      | exact hs
  · split_ifs with h <;>
      first
      | exact stdCounterSubroutine_agentOk _ (agentOk_of_role_main _
          (by rw [absorbConsume_role_snd]; exact h.2))
      | exact agentOk_of_role_main _ (by rw [absorbConsume_role_snd]; exact h.2)
      | exact stdCounterSubroutine_agentOk _ ht
      | exact ht

private lemma Phase9Transition_agentOk (s t : AgentState L K)
    (hs : agentOk s) (ht : agentOk t) :
    agentOk (Phase9Transition L K s t).1 ∧ agentOk (Phase9Transition L K s t).2 := by
  unfold Phase9Transition
  exact Phase2Transition_agentOk s t hs ht

private lemma Phase10Transition_agentOk (s t : AgentState L K)
    (hs : agentOk s) (ht : agentOk t) :
    agentOk (Phase10Transition L K s t).1 ∧ agentOk (Phase10Transition L K s t).2 := by
  unfold Phase10Transition
  dsimp only
  constructor
  · split_ifs <;>
      first
      | exact agentOk_congr hs (by simp) (by simp) (by simp)
      | exact hs
  · split_ifs <;>
      first
      | exact agentOk_congr ht (by simp) (by simp) (by simp)
      | exact ht

private lemma finishPhase10Entry_agentOk (before after : AgentState L K)
    (h : agentOk after) : agentOk (finishPhase10Entry L K before after) := by
  unfold finishPhase10Entry canonicalPhase10Entry
  split_ifs
  · exact agentOk_of_phase_eq_ten _ (by simp)
  · exact h

/-! ## Epidemic output phases -/

private lemma phaseEpidemicUpdate_phase (s t : AgentState L K) :
    ((phaseEpidemicUpdate L K s t).1.phase.val = (max s.phase t.phase).val ∨
      (phaseEpidemicUpdate L K s t).1.phase.val = 10) ∧
    ((phaseEpidemicUpdate L K s t).2.phase.val = (max s.phase t.phase).val ∨
      (phaseEpidemicUpdate L K s t).2.phase.val = 10) := by
  unfold phaseEpidemicUpdate
  dsimp only
  have h1 : (runInitsBetween L K s.phase.val (max s.phase t.phase).val
      ({ s with phase := max s.phase t.phase } : AgentState L K)).phase.val
        = (max s.phase t.phase).val ∨
      (runInitsBetween L K s.phase.val (max s.phase t.phase).val
        ({ s with phase := max s.phase t.phase } : AgentState L K)).phase.val = 10 := by
    rw [runInitsBetween_eq_initFold]
    exact initFold_phase_eq_or_ten _ _
  have h2 : (runInitsBetween L K t.phase.val (max s.phase t.phase).val
      ({ t with phase := max s.phase t.phase } : AgentState L K)).phase.val
        = (max s.phase t.phase).val ∨
      (runInitsBetween L K t.phase.val (max s.phase t.phase).val
        ({ t with phase := max s.phase t.phase } : AgentState L K)).phase.val = 10 := by
    rw [runInitsBetween_eq_initFold]
    exact initFold_phase_eq_or_ten _ _
  split_ifs with hcond
  · constructor
    · dsimp only
      unfold phase10EpidemicEntry
      split_ifs
      · right
        simp [enterPhase10, phase10]
      · exact h1
    · dsimp only
      unfold phase10EpidemicEntry
      split_ifs
      · right
        simp [enterPhase10, phase10]
      · exact h2
  · exact ⟨h1, h2⟩

/-! ## The full transition -/

theorem Transition_agentOk (s t : AgentState L K)
    (hs : agentOk s) (ht : agentOk t) :
    agentOk (Transition L K s t).1 ∧ agentOk (Transition L K s t).2 := by
  rcases phaseEpidemicUpdate_agentOk (L := L) (K := K) s t hs ht with ⟨hs_ep, ht_ep⟩
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
  have hout : agentOk out.1 ∧ agentOk out.2 := by
    change agentOk
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
      agentOk
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
    | 0, _ => exact Phase0Transition_agentOk (L := L) (K := K) s' t' hs_ep ht_ep
    | 1, _ => exact Phase1Transition_agentOk (L := L) (K := K) s' t' hs_ep ht_ep
    | 2, _ => exact Phase2Transition_agentOk (L := L) (K := K) s' t' hs_ep ht_ep
    | 3, _ => exact Phase3Transition_agentOk (L := L) (K := K) s' t' hs_ep ht_ep
    | 4, _ => exact Phase4Transition_agentOk (L := L) (K := K) s' t' hs_ep ht_ep
    | 5, _ => exact Phase5Transition_agentOk (L := L) (K := K) s' t' hs_ep ht_ep
    | 6, _ => exact Phase6Transition_agentOk (L := L) (K := K) s' t' hs_ep ht_ep
    | 7, _ => exact Phase7Transition_agentOk (L := L) (K := K) s' t' hs_ep ht_ep
    | 8, _ => exact Phase8Transition_agentOk (L := L) (K := K) s' t' hs_ep ht_ep
    | 9, _ => exact Phase9Transition_agentOk (L := L) (K := K) s' t' hs_ep ht_ep
    | 10, _ => exact Phase10Transition_agentOk (L := L) (K := K) s' t' hs_ep ht_ep
    | n + 11, hn => omega
  exact ⟨finishPhase10Entry_agentOk (L := L) (K := K) s' out.1 hout.1,
    finishPhase10Entry_agentOk (L := L) (K := K) t' out.2 hout.2⟩

/-! ## Reachable invariance and the drained-endpoint discharge -/

theorem reachable_nonMainBiasZero (init c : Config (AgentState L K))
    (hinit : validInitial init)
    (hreach : (NonuniformMajority L K).Reachable init c) :
    NonMainBiasZeroInv c := by
  induction hreach with
  | refl => exact nonMainBiasZeroInv_validInitial (L := L) (K := K) init hinit
  | tail hprev hstep ih =>
      rcases hstep with ⟨r₁, r₂, happ, hc'⟩
      dsimp [Protocol.Applicable, NonuniformMajority] at happ hc'
      have hr₁_mem : r₁ ∈ _ := Multiset.mem_of_le happ (by simp)
      have hr₂_mem : r₂ ∈ _ := Multiset.mem_of_le happ (by simp)
      have htrans := Transition_agentOk (L := L) (K := K) r₁ r₂
        (ih r₁ hr₁_mem) (ih r₂ hr₂_mem)
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

/-- **Drained-endpoint discharge.**  At any all-Phase-8 configuration reachable
from a valid input, every non-Main agent is bias-free — exactly the
`hnonmain` hypothesis of `OutcomeOriginLedger.seed_of_drained_*`. -/
theorem reachable_nonMain_bias_zero_of_all8 (init c : Config (AgentState L K))
    (hinit : validInitial init)
    (hreach : (NonuniformMajority L K).Reachable init c)
    (hall8 : ∀ a ∈ c, a.phase.val = 8) :
    ∀ a ∈ c, a.role ≠ .main → a.bias = .zero := by
  intro a ha hrole
  exact reachable_nonMainBiasZero init c hinit hreach a ha hrole
    (by have := hall8 a ha; omega) (by have := hall8 a ha; omega)

#print axioms phaseEpidemicUpdate_agentOk
#print axioms Transition_agentOk
#print axioms reachable_nonMainBiasZero
#print axioms reachable_nonMain_bias_zero_of_all8
#print axioms nonMainBiasZeroInv_validInitial

end NonMainBiasZero
end Ripple.PopulationProtocol.ExactMajority
