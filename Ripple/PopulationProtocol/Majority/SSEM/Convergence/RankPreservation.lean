/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Rank-Field Projection Helpers

The `.rank` field of an `AgentState` is never modified by any record
update used in `transitionPEM`.  These helpers project `.rank` through
single-field updates, available as building blocks for rank-preservation
proofs.
-/

import Ripple.PopulationProtocol.Majority.SSEM.Convergence.SwapPhase
import Ripple.PopulationProtocol.Majority.SSEM.Convergence.SwapStep

namespace SSEM

variable {n : ℕ}



@[simp] theorem AgentState.rank_with_role (s : AgentState n) (r : Role) :
    ({s with role := r}).rank = s.rank := rfl

@[simp] theorem AgentState.rank_with_leader (s : AgentState n) (l : Leader) :
    ({s with leader := l}).rank = s.rank := rfl

@[simp] theorem AgentState.rank_with_resetcount (s : AgentState n) (rc : ℕ) :
    ({s with resetcount := rc}).rank = s.rank := rfl

-- Struct update projection lemmas: answer/timer changes preserve all structural fields
-- role_with_answer and role_with_timer are now in Protocol/State.lean
@[simp] theorem AgentState.children_with_timer (s : AgentState n) (t : ℕ) :
    ({s with timer := t}).children = s.children := rfl
@[simp] theorem AgentState.delaytimer_with_timer (s : AgentState n) (t : ℕ) :
    ({s with timer := t}).delaytimer = s.delaytimer := rfl
/-! ### Propagation rank preservation -/

/-- The propagation phase preserves the `.rank` field of both agents. -/
theorem propagation_rank_preserved (Rmax : ℕ) (b₀ b₁ : AgentState n) :
    let prop := if b₀.rank.val + 1 = ceilHalf n then
      let b₀' := if b₁.rank.val + 1 = n then
          { b₀ with timer := b₀.timer - 1 } else b₀
      if b₀'.timer = 0 ∧ b₀'.answer ≠ b₁.answer then
        ({ b₀' with role := Role.Resetting,
                    leader := Leader.L,
                    resetcount := Rmax },
         { b₁ with answer := b₀'.answer,
                   role := Role.Resetting,
                   leader := Leader.L,
                   resetcount := Rmax })
      else (b₀', b₁)
    else if b₁.rank.val + 1 = ceilHalf n then
      let b₁' := if b₀.rank.val + 1 = n then
          { b₁ with timer := b₁.timer - 1 } else b₁
      if b₁'.timer = 0 ∧ b₁'.answer ≠ b₀.answer then
        ({ b₀ with answer := b₁'.answer,
                   role := Role.Resetting,
                   leader := Leader.L,
                   resetcount := Rmax },
         { b₁' with role := Role.Resetting,
                    leader := Leader.L,
                    resetcount := Rmax })
      else (b₀, b₁')
    else (b₀, b₁)
    prop.1.rank = b₀.rank ∧ prop.2.rank = b₁.rank := by
  by_cases hA : b₀.rank.val + 1 = ceilHalf n
  · simp only [hA, if_true]
    by_cases hT : b₁.rank.val + 1 = n
    · simp only [hT, if_true]
      split_ifs <;> refine ⟨?_, ?_⟩ <;> first | rfl | trivial
    · simp only [hT, if_false]
      split_ifs <;> refine ⟨?_, ?_⟩ <;> first | rfl | trivial
  · simp only [hA, if_false]
    by_cases hB : b₁.rank.val + 1 = ceilHalf n
    · simp only [hB, if_true]
      by_cases hT : b₀.rank.val + 1 = n
      · simp only [hT, if_true]
        split_ifs <;> refine ⟨?_, ?_⟩ <;> first | rfl | trivial
      · simp only [hT, if_false]
        split_ifs <;> refine ⟨?_, ?_⟩ <;> first | rfl | trivial
    · simp only [hB, if_false]
      refine ⟨?_, ?_⟩ <;> first | rfl | trivial

/-! ### Decision phase rank preservation -/

/-- The decision phase preserves the `.rank` field of both agents
(it only modifies `.answer`). -/
theorem decision_rank_preserved_even (b₀ b₁ : AgentState n) (x₀ x₁ : Opinion) :
    let dec := if b₀.rank.val + 1 = n / 2 ∧ b₁.rank.val + 1 = n / 2 + 1 then
      (if x₀ = x₁ then
        ({ b₀ with answer := opinionToAnswer x₀ },
         { b₁ with answer := opinionToAnswer x₀ })
      else
        ({ b₀ with answer := Answer.outT }, { b₁ with answer := Answer.outT }))
    else if b₁.rank.val + 1 = n / 2 ∧ b₀.rank.val + 1 = n / 2 + 1 then
      (if x₁ = x₀ then
        ({ b₀ with answer := opinionToAnswer x₁ },
         { b₁ with answer := opinionToAnswer x₁ })
      else
        ({ b₀ with answer := Answer.outT }, { b₁ with answer := Answer.outT }))
    else (b₀, b₁)
    dec.1.rank = b₀.rank ∧ dec.2.rank = b₁.rank := by
  split_ifs <;> refine ⟨?_, ?_⟩ <;> first | rfl | trivial

/-- The decision phase (odd `n`) preserves the `.rank` field of both agents. -/
theorem decision_rank_preserved_odd (b₀ b₁ : AgentState n) (x₀ x₁ : Opinion) :
    let b₀' := if b₀.rank.val + 1 = ceilHalf n then
        { b₀ with answer := opinionToAnswer x₀ } else b₀
    let b₁' := if b₁.rank.val + 1 = ceilHalf n then
        { b₁ with answer := opinionToAnswer x₁ } else b₁
    b₀'.rank = b₀.rank ∧ b₁'.rank = b₁.rank := by
  refine ⟨?_, ?_⟩ <;> split_ifs <;> first | rfl | trivial

/-! ### Combined: rank-swap at misorder -/

set_option maxHeartbeats 16000000 in
/-- **Unconditional rank-swap lemma at any misorder pair.** -/
theorem transitionPEM_rank_swap_at_misorder
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    {u v : Fin n} (hMis : MisorderedPair C (u, v)) :
    (transitionPEM n trank Rmax rankDelta (C u, C v)).1.rank = (C v).1.rank ∧
    (transitionPEM n trank Rmax rankDelta (C u, C v)).2.rank = (C u).1.rank := by
  obtain ⟨huB, hvA, hlt⟩ := hMis
  have hsu : (C u).1.role = .Settled := hC.allSettled u
  have hsv : (C v).1.role = .Settled := hC.allSettled v
  have hRD : rankDelta ((C u).1, (C v).1) = ((C u).1, (C v).1) :=
    hRank (C u).1 (C v).1 hsu hsv (ne_of_lt hlt)
  have hswap : (C u).1.rank < (C v).1.rank ∧ (C u).2 = Opinion.B ∧ (C v).2 = Opinion.A :=
    ⟨hlt, huB, hvA⟩
  unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4 phase4_swap phase4_decide phase4_propagate
  simp only [hRD, hsu, hsv, ne_eq,
    role_settled_ne_resetting,
    not_true_eq_false, not_false_eq_true,
    false_and, and_false, if_false,
    and_self, if_true, hswap]
  -- After Phase 1-3 + swap, (b₀, b₁) = ((C v).1, (C u).1). Rank-preserve through
  -- decision and propagation by case split on every conditional.
  by_cases hpar : n % 2 = 0
  · simp only [hpar, if_true]
    split_ifs <;>
      refine ⟨?_, ?_⟩ <;>
      first | rfl | trivial |
        (show ({_ with answer := _, role := _, leader := _, resetcount := _}.rank) = _; rfl) |
        (show ({_ with answer := _}.rank) = _; rfl) |
        (show ({_ with timer := _}.rank) = _; rfl) |
        (show ({_ with role := _, leader := _, resetcount := _}.rank) = _; rfl) |
        (show ({_ with timer := _, role := _, leader := _, resetcount := _}.rank) = _; rfl)
  · simp only [hpar, if_false]
    split_ifs <;>
      refine ⟨?_, ?_⟩ <;>
      first | rfl | trivial |
        (show ({_ with answer := _, role := _, leader := _, resetcount := _}.rank) = _; rfl) |
        (show ({_ with answer := _}.rank) = _; rfl) |
        (show ({_ with timer := _}.rank) = _; rfl) |
        (show ({_ with role := _, leader := _, resetcount := _}.rank) = _; rfl) |
        (show ({_ with timer := _, role := _, leader := _, resetcount := _}.rank) = _; rfl)

/-! ### Role preservation: only reset modifies it; reset is blocked under timer hypothesis -/

/-- Propagation phase preserves the `.role` field when the reset trigger
condition is false. -/
theorem propagation_role_preserved_no_reset (Rmax : ℕ) (b₀ b₁ : AgentState n)
    (h_no_reset_A : ¬ (({b₀ with timer := b₀.timer - 1}).timer = 0 ∧
                       ({b₀ with timer := b₀.timer - 1}).answer ≠ b₁.answer))
    (h_no_reset_A_no_dec : ¬ (b₀.timer = 0 ∧ b₀.answer ≠ b₁.answer))
    (h_no_reset_B : ¬ (({b₁ with timer := b₁.timer - 1}).timer = 0 ∧
                       ({b₁ with timer := b₁.timer - 1}).answer ≠ b₀.answer))
    (h_no_reset_B_no_dec : ¬ (b₁.timer = 0 ∧ b₁.answer ≠ b₀.answer)) :
    let prop := if b₀.rank.val + 1 = ceilHalf n then
      let b₀' := if b₁.rank.val + 1 = n then
          { b₀ with timer := b₀.timer - 1 } else b₀
      if b₀'.timer = 0 ∧ b₀'.answer ≠ b₁.answer then
        ({ b₀' with role := Role.Resetting,
                    leader := Leader.L,
                    resetcount := Rmax },
         { b₁ with answer := b₀'.answer,
                   role := Role.Resetting,
                   leader := Leader.L,
                   resetcount := Rmax })
      else (b₀', b₁)
    else if b₁.rank.val + 1 = ceilHalf n then
      let b₁' := if b₀.rank.val + 1 = n then
          { b₁ with timer := b₁.timer - 1 } else b₁
      if b₁'.timer = 0 ∧ b₁'.answer ≠ b₀.answer then
        ({ b₀ with answer := b₁'.answer,
                   role := Role.Resetting,
                   leader := Leader.L,
                   resetcount := Rmax },
         { b₁' with role := Role.Resetting,
                    leader := Leader.L,
                    resetcount := Rmax })
      else (b₀, b₁')
    else (b₀, b₁)
    prop.1.role = b₀.role ∧ prop.2.role = b₁.role := by
  by_cases hA : b₀.rank.val + 1 = ceilHalf n
  · simp only [hA, if_true]
    by_cases hT : b₁.rank.val + 1 = n
    · simp only [hT, if_true, h_no_reset_A, if_false]
      refine ⟨?_, ?_⟩ <;> first | rfl | trivial
    · simp only [hT, if_false, h_no_reset_A_no_dec, if_false]
      refine ⟨?_, ?_⟩ <;> first | rfl | trivial
  · simp only [hA, if_false]
    by_cases hB : b₁.rank.val + 1 = ceilHalf n
    · simp only [hB, if_true]
      by_cases hT : b₀.rank.val + 1 = n
      · simp only [hT, if_true, h_no_reset_B, if_false]
        refine ⟨?_, ?_⟩ <;> first | rfl | trivial
      · simp only [hT, if_false, h_no_reset_B_no_dec, if_false]
        refine ⟨?_, ?_⟩ <;> first | rfl | trivial
    · simp only [hB, if_false]
      refine ⟨?_, ?_⟩ <;> first | rfl | trivial



theorem AgentState.role_with_answer' (s : AgentState n) (a : Answer) :
    ({s with answer := a}).role = s.role := rfl

theorem AgentState.role_with_timer' (s : AgentState n) (t : ℕ) :
    ({s with timer := t}).role = s.role := rfl

/-! ### Reset blocking under timer ≥ 1 / ≥ 2 -/

/-- If `s.timer ≥ 1`, the reset condition `s.timer = 0 ∧ ...` is false. -/
theorem reset_blocked_timer_ge_1 {s : AgentState n} {a : Answer} {ans' : Answer}
    (h : 1 ≤ s.timer) :
    ¬ (({s with answer := a}).timer = 0 ∧
       ({s with answer := a}).answer ≠ ans') := by
  intro ⟨h_t, _⟩
  have : s.timer = 0 := h_t
  omega

/-- If `s.timer ≥ 2`, the reset condition on `{s with answer := a, timer := s.timer - 1}`
is false (the post-dec timer is ≥ 1). -/
theorem reset_blocked_timer_ge_2 {s : AgentState n} {a : Answer} {ans' : Answer}
    (h : 2 ≤ s.timer) :
    ¬ (({s with answer := a, timer := s.timer - 1}).timer = 0 ∧
       ({s with answer := a, timer := s.timer - 1}).answer ≠ ans') := by
  intro ⟨h_t, _⟩
  have : s.timer - 1 = 0 := h_t
  omega

/-- Generic reset-blocking lemma: any agent with timer ≠ 0 cannot trigger
the reset condition `timer = 0 ∧ ...`, regardless of how the agent
record was constructed. -/
theorem reset_blocked_generic (b : AgentState n) (a' : Answer)
    (h : b.timer ≠ 0) :
    ¬ (b.timer = 0 ∧ b.answer ≠ a') :=
  fun ⟨h_t, _⟩ => h h_t

/-! ### Role preservation under "v not at max rank" + "median timer ≥ 1" -/

/-- Special case: the propagation reset condition uses the agent's raw
`.timer` (not decremented) when inner timer-dec doesn't fire.  Under
this scenario, `timer ≥ 1` suffices to block reset. -/
theorem reset_blocked_no_inner_dec_timer_pos {b : AgentState n} {a : Answer} {ans' : Answer}
    (h : 1 ≤ b.timer) :
    ¬ (({b with answer := a}).timer = 0 ∧ ¬ ({b with answer := a}).answer = ans') := by
  intro ⟨h_t, _⟩
  have : b.timer = 0 := h_t
  omega

theorem reset_blocked_unmodified_timer_pos {b : AgentState n} {ans' : Answer}
    (h : 1 ≤ b.timer) :
    ¬ (b.timer = 0 ∧ ¬ b.answer = ans') := by
  intro ⟨h_t, _⟩; omega

/-! ### Parameterized InSrank-preservation: assumes role-Settled at output -/

/-- If the swap step at a misorder pair produces a result whose `.role`
fields are both `.Settled`, then `InSrank` is preserved.  This isolates
the only difficult ingredient (role preservation under timer hypothesis)
from the structurally easy parts (rank-swap and ranks_inj). -/
theorem step_at_misorder_preserves_InSrank_of_role_settled
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    {u v : Fin n} (hMis : MisorderedPair C (u, v))
    (h_role :
      (transitionPEM n trank Rmax rankDelta (C u, C v)).1.role = Role.Settled ∧
      (transitionPEM n trank Rmax rankDelta (C u, C v)).2.role = Role.Settled) :
    InSrank (C.step (protocolPEM n trank Rmax rankDelta) u v) := by
  set C' := C.step (protocolPEM n trank Rmax rankDelta) u v with hC'_def
  have huv : u ≠ v := by
    intro heq; obtain ⟨_, _, hlt⟩ := hMis; rw [heq] at hlt; exact absurd hlt (lt_irrefl _)
  have h_rank := transitionPEM_rank_swap_at_misorder
    (trank := trank) (Rmax := Rmax) hRank hC hMis
  refine { allSettled := ?_, ranks_inj := ?_ }
  · intro w
    by_cases hwu : w = u
    · rw [hwu]
      show ((C.step (protocolPEM n trank Rmax rankDelta) u v) u).1.role = .Settled
      unfold Config.step
      simp only [if_neg huv, if_pos rfl]
      show (transitionPEM n trank Rmax rankDelta (C u, C v)).1.role = .Settled
      exact h_role.1
    · by_cases hwv : w = v
      · rw [hwv]
        show ((C.step (protocolPEM n trank Rmax rankDelta) u v) v).1.role = .Settled
        unfold Config.step
        have hvu : v ≠ u := huv.symm
        simp only [if_neg huv, if_neg hvu, if_pos rfl]
        show (transitionPEM n trank Rmax rankDelta (C u, C v)).2.role = .Settled
        exact h_role.2
      · show ((C.step (protocolPEM n trank Rmax rankDelta) u v) w).1.role = .Settled
        unfold Config.step
        simp [huv, hwu, hwv]
        exact hC.allSettled w
  · intro w₁ w₂ hw
    let τ : Fin n → Fin n := fun w => if w = u then v else if w = v then u else w
    have hτ_invol : ∀ w, τ (τ w) = w := by
      intro w
      by_cases hwu : w = u
      · simp [τ, hwu, show (v : Fin n) ≠ u from huv.symm]
      · by_cases hwv : w = v
        · simp [τ, hwv, hwu]
        · simp [τ, hwu, hwv]
    have hτ_inj : Function.Injective τ := by
      intro a b hab
      have : τ (τ a) = τ (τ b) := congrArg τ hab
      rw [hτ_invol, hτ_invol] at this
      exact this
    have hτ_rank : ∀ w, (C' w).1.rank = (C (τ w)).1.rank := by
      intro w
      show ((C.step (protocolPEM n trank Rmax rankDelta) u v) w).1.rank = (C (τ w)).1.rank
      unfold Config.step
      by_cases hwu : w = u
      · rw [hwu]
        simp only [if_neg huv, if_pos rfl]
        show (transitionPEM n trank Rmax rankDelta (C u, C v)).1.rank = (C (τ u)).1.rank
        rw [h_rank.1]
        simp [τ]
      · by_cases hwv : w = v
        · rw [hwv]
          simp only [if_neg huv, if_neg huv.symm, if_pos rfl]
          show (transitionPEM n trank Rmax rankDelta (C u, C v)).2.rank = (C (τ v)).1.rank
          rw [h_rank.2]
          simp [τ, show (v : Fin n) ≠ u from huv.symm]
        · simp [huv, hwu, hwv, τ]
    have hwval : (C' w₁).1.rank = (C' w₂).1.rank := hw
    rw [hτ_rank w₁, hτ_rank w₂] at hwval
    have hτeq : τ w₁ = τ w₂ := hC.ranks_inj hwval
    exact hτ_inj hτeq

/-! ### Unconditional misorderedCount-decrease via rank-swap -/

set_option maxHeartbeats 8000000 in
/-- **Unconditional count-decrease lemma.**  At any misorder pair, the
swap step strictly decreases the misorderedCount — whether or not the
median agent is involved.  No timer hypothesis needed; relies only on
the unconditional rank-swap. -/
theorem misorderedCount_decreases_step_at_misorder
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    {u v : Fin n} (hMis : MisorderedPair C (u, v)) :
    misorderedCount (C.step (protocolPEM n trank Rmax rankDelta) u v)
      < misorderedCount C := by
  classical
  set C' := C.step (protocolPEM n trank Rmax rankDelta) u v with hC'_def
  have huv : u ≠ v := by
    intro heq; obtain ⟨_, _, hlt⟩ := hMis; rw [heq] at hlt; exact absurd hlt (lt_irrefl _)
  have h_rank :=
    transitionPEM_rank_swap_at_misorder (trank := trank) (Rmax := Rmax) hRank hC hMis
  -- Rank fields:
  --   (C' u).1.rank = (C v).1.rank, (C' v).1.rank = (C u).1.rank, others unchanged.
  -- Inputs unchanged (Config.step preserves inputs).
  have hu_rank : (C' u).1.rank = (C v).1.rank := by
    show ((C.step (protocolPEM n trank Rmax rankDelta) u v) u).1.rank = (C v).1.rank
    unfold Config.step
    simp only [if_neg huv, if_pos rfl]
    show (transitionPEM n trank Rmax rankDelta (C u, C v)).1.rank = (C v).1.rank
    exact h_rank.1
  have hv_rank : (C' v).1.rank = (C u).1.rank := by
    show ((C.step (protocolPEM n trank Rmax rankDelta) u v) v).1.rank = (C u).1.rank
    unfold Config.step
    have hvu : v ≠ u := huv.symm
    simp only [if_neg huv, if_neg hvu, if_pos rfl]
    show (transitionPEM n trank Rmax rankDelta (C u, C v)).2.rank = (C u).1.rank
    exact h_rank.2
  have h_other_rank : ∀ w, w ≠ u → w ≠ v → (C' w).1.rank = (C w).1.rank := by
    intro w hwu hwv
    show ((C.step (protocolPEM n trank Rmax rankDelta) u v) w).1.rank = (C w).1.rank
    unfold Config.step
    simp [huv, hwu, hwv]
  have h_input : ∀ w, (C' w).2 = (C w).2 := by
    intro w
    show ((C.step (protocolPEM n trank Rmax rankDelta) u v) w).2 = (C w).2
    unfold Config.step
    by_cases hwu : w = u
    · rw [hwu]; simp [huv]
    · by_cases hwv : w = v
      · have hvu : v ≠ u := huv.symm
        rw [hwv]; simp [huv, hvu]
      · simp [huv, hwu, hwv]
  -- Now reuse the combinatorial argument from
  -- `misorderedCount_decreases_at_non_median`.
  obtain ⟨huB, hvA, h_uv_lt⟩ := hMis
  have h_uv_val : (C u).1.rank.val < (C v).1.rank.val := h_uv_lt
  have hsub : misorderedSet C' ⊆ misorderedSet C := by
    intro p hp
    have hp_pair := mem_misorderedSet.mp hp
    obtain ⟨h1, h2, h3⟩ := hp_pair
    apply mem_misorderedSet.mpr
    have h1' : (C p.1).2 = Opinion.B := by rw [← h_input p.1]; exact h1
    have h2' : (C p.2).2 = Opinion.A := by rw [← h_input p.2]; exact h2
    have hp1_ne_v : p.1 ≠ v := fun heq => by rw [heq, hvA] at h1'; cases h1'
    have hp2_ne_u : p.2 ≠ u := fun heq => by rw [heq, huB] at h2'; cases h2'
    refine ⟨h1', h2', ?_⟩
    have h3val : (C' p.1).1.rank.val < (C' p.2).1.rank.val := h3
    have h_C'p1 : (C' p.1).1.rank.val =
        (if p.1 = u then (C v).1.rank.val else (C p.1).1.rank.val) := by
      by_cases hp1u : p.1 = u
      · rw [hp1u, hu_rank]; simp
      · rw [h_other_rank p.1 hp1u hp1_ne_v]; simp [hp1u]
    have h_C'p2 : (C' p.2).1.rank.val =
        (if p.2 = v then (C u).1.rank.val else (C p.2).1.rank.val) := by
      by_cases hp2v : p.2 = v
      · rw [hp2v, hv_rank]; simp
      · rw [h_other_rank p.2 hp2_ne_u hp2v]; simp [hp2v]
    rw [h_C'p1, h_C'p2] at h3val
    show (C p.1).1.rank < (C p.2).1.rank
    by_cases hp1u : p.1 = u
    · by_cases hp2v : p.2 = v
      · simp [hp1u, hp2v] at h3val; omega
      · simp [hp1u, hp2v] at h3val
        show (C p.1).1.rank.val < (C p.2).1.rank.val
        rw [hp1u]; omega
    · by_cases hp2v : p.2 = v
      · simp [hp1u, hp2v] at h3val
        show (C p.1).1.rank.val < (C p.2).1.rank.val
        rw [hp2v]; omega
      · simp [hp1u, hp2v] at h3val
        show (C p.1).1.rank.val < (C p.2).1.rank.val
        exact h3val
  have h_uv_in : (u, v) ∈ misorderedSet C := mem_misorderedSet.mpr ⟨huB, hvA, h_uv_lt⟩
  have h_uv_not_in : (u, v) ∉ misorderedSet C' := by
    intro hin
    obtain ⟨_, _, hlt⟩ := mem_misorderedSet.mp hin
    have hlt' : (C' u).1.rank.val < (C' v).1.rank.val := hlt
    rw [hu_rank, hv_rank] at hlt'
    omega
  unfold misorderedCount
  apply Finset.card_lt_card
  refine ⟨hsub, ?_⟩
  intro h_supset
  exact h_uv_not_in (h_supset h_uv_in)

/-! ### Full single-step lemma at any misorder pair (under role-Settled hypothesis) -/

/-- **Full single-step lemma at ANY misorder pair (median or non-median)**:
under InSrank + role-preservation hypothesis at output, the step
preserves InSrank and strictly decreases the misordered count. -/
theorem swap_step_decreases_at_misorder_of_role_settled
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    {u v : Fin n} (hMis : MisorderedPair C (u, v))
    (h_role :
      (transitionPEM n trank Rmax rankDelta (C u, C v)).1.role = Role.Settled ∧
      (transitionPEM n trank Rmax rankDelta (C u, C v)).2.role = Role.Settled) :
    InSrank (C.step (protocolPEM n trank Rmax rankDelta) u v) ∧
    misorderedCount (C.step (protocolPEM n trank Rmax rankDelta) u v)
      < misorderedCount C :=
  ⟨step_at_misorder_preserves_InSrank_of_role_settled hRank hC hMis h_role,
   misorderedCount_decreases_step_at_misorder hRank hC hMis⟩

/-! ### Role preservation: non-median case (corollary of full state-swap) -/

/-- At a non-median misorder pair, the result of `transitionPEM` has both
agents' `.role` field equal to `.Settled`.  Direct corollary of
`transitionPEM_at_misordered_non_median`. -/
theorem transitionPEM_role_settled_at_misorder_non_median
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    {u v : Fin n} (hMis : MisorderedPair C (u, v))
    (hu_no_med : (C u).1.rank.val + 1 ≠ ceilHalf n)
    (hv_no_med : (C v).1.rank.val + 1 ≠ ceilHalf n) :
    (transitionPEM n trank Rmax rankDelta (C u, C v)).1.role = Role.Settled ∧
    (transitionPEM n trank Rmax rankDelta (C u, C v)).2.role = Role.Settled := by
  rw [transitionPEM_at_misordered_non_median hRank hC hMis hu_no_med hv_no_med]
  exact ⟨hC.allSettled v, hC.allSettled u⟩

/-! ### Combined-form reset blocking using arithmetic + h_reset.2 rfl chain -/

/-- A unified reset-blocking lemma: if `b.timer ≥ 1` then the reset
condition `b.timer = 0 ∧ ...` is False.  This works regardless of the
specific record-update structure on b.answer. -/
theorem reset_blocked_by_pos_timer_simple {b : AgentState n} {ans' : Answer}
    (h : 1 ≤ b.timer) (h_reset : b.timer = 0 ∧ ¬ b.answer = ans') :
    False := by
  exact absurd h_reset.1 (by omega)

/-- Truly generic: if a Nat `t ≥ 1`, the reset condition `t = 0 ∧ ...` is
False, regardless of any answer values. -/
theorem reset_blocked_pos_timer_any_answer {t : ℕ} {a₀ a₁ : Answer}
    (h : 1 ≤ t) :
    ¬ (t = 0 ∧ ¬ a₀ = a₁) := by
  intro ⟨h_t, _⟩; omega

/-! ### Median-pair case (even n, u at lower median, v at upper median) -/

set_option maxHeartbeats 8000000 in
/-- Specific case: even `n ≥ 4`, u at lower-median rank `n/2 - 1`, v at
upper-median rank `n/2`.  The pair `(u, v)` then satisfies misorder
preconditions, the decision phase fires its second branch with mismatched
inputs (`x₀ = .B ≠ .A = x₁`), setting both answers to `.outT`.

Reset is blocked because both answers agree (`.outT = .outT`), so the
`b.answer ≠ b'.answer` conjunct of the reset condition fails.  Inner
timer-dec only fires when `b₀.rank.val + 1 = n` which for the upper-median
configuration means `n = 2`; we exclude this edge with `hn_ge_4`.

Result: `({(C v).1 with answer := .outT}, {(C u).1 with answer := .outT})`. -/
theorem transitionPEM_at_misordered_u_lower_median_even
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    {u v : Fin n} (hMis : MisorderedPair C (u, v))
    (hpar : n % 2 = 0)
    (hu_med : (C u).1.rank.val + 1 = n / 2)
    (hv_upper : (C v).1.rank.val + 1 = n / 2 + 1)
    (hn_ge_4 : 4 ≤ n) :
    transitionPEM n trank Rmax rankDelta (C u, C v)
      = ({(C v).1 with answer := .outT}, {(C u).1 with answer := .outT}) := by
  obtain ⟨huB, hvA, hlt⟩ := hMis
  have hsu : (C u).1.role = .Settled := hC.allSettled u
  have hsv : (C v).1.role = .Settled := hC.allSettled v
  have hRD : rankDelta ((C u).1, (C v).1) = ((C u).1, (C v).1) :=
    hRank (C u).1 (C v).1 hsu hsv (ne_of_lt hlt)
  have hswap : (C u).1.rank < (C v).1.rank ∧ (C u).2 = Opinion.B ∧ (C v).2 = Opinion.A :=
    ⟨hlt, huB, hvA⟩
  have hceil : ceilHalf n = n / 2 := by unfold ceilHalf; omega
  have hb0_no_med_ceil : ¬ ((C v).1.rank.val + 1 = ceilHalf n) := by
    rw [hceil, hv_upper]; omega
  have hb1_med_ceil : (C u).1.rank.val + 1 = ceilHalf n := by
    rw [hceil]; exact hu_med
  -- Even n decision: branch 1 requires b₀ at n/2 ∧ b₁ at n/2+1; we have the
  -- opposite.
  have hd1_fail : ¬ ((C v).1.rank.val + 1 = n / 2 ∧
                     (C u).1.rank.val + 1 = n / 2 + 1) := by
    intro ⟨h, _⟩; omega
  -- Branch 2 fires with hu_med ∧ hv_upper.
  have hd2 : (C u).1.rank.val + 1 = n / 2 ∧ (C v).1.rank.val + 1 = n / 2 + 1 :=
    ⟨hu_med, hv_upper⟩
  have hxne : ¬ ((C v).2 = (C u).2) := by rw [huB, hvA]; intro h; cases h
  -- Inner timer-dec doesn't fire: b₀.rank.val + 1 = n/2 + 1 = n requires n = 2.
  have hb0_no_max : ¬ ((C v).1.rank.val + 1 = n) := by
    rw [hv_upper]; omega
  have hBA : ¬ (Opinion.B = Opinion.A) := by intro h; cases h
  have hAB : ¬ (Opinion.A = Opinion.B) := by intro h; cases h
  -- Explicit Nat arithmetic facts (avoid omega in simp args).
  have hN1 : ¬ (n / 2 + 1 = n / 2) := fun h => by omega
  have hN2 : ¬ (n / 2 = n / 2 + 1) := fun h => by omega
  have hN3 : ¬ (n / 2 = n) := fun h => by omega  -- needs n ≥ 4
  have hN4 : ¬ (n / 2 + 1 = n) := fun h => by omega  -- needs n ≥ 4
  unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4 phase4_swap phase4_decide phase4_propagate
  simp only [hRD, hsu, hsv, ne_eq,
    role_settled_ne_resetting,
    not_true_eq_false, not_false_eq_true,
    false_and, and_false, if_false,
    and_self, if_true, hswap, hpar, hd1_fail, hd2, hxne,
    hb0_no_med_ceil, hb1_med_ceil, hb0_no_max, hBA, hAB,
    hN1, hN2, hN3, hN4, hceil]

/-- Role-Settled at the even-n median-pair case (n ≥ 4). -/
theorem transitionPEM_role_settled_at_misorder_u_lower_median_even
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    {u v : Fin n} (hMis : MisorderedPair C (u, v))
    (hpar : n % 2 = 0)
    (hu_med : (C u).1.rank.val + 1 = n / 2)
    (hv_upper : (C v).1.rank.val + 1 = n / 2 + 1)
    (hn_ge_4 : 4 ≤ n) :
    (transitionPEM n trank Rmax rankDelta (C u, C v)).1.role = Role.Settled ∧
    (transitionPEM n trank Rmax rankDelta (C u, C v)).2.role = Role.Settled := by
  rw [transitionPEM_at_misordered_u_lower_median_even
        hRank hC hMis hpar hu_med hv_upper hn_ge_4]
  exact ⟨hC.allSettled v, hC.allSettled u⟩

/-- Unconditional swap-step decrease for the even-n median-pair case (n ≥ 4). -/
theorem swap_step_decreases_at_misorder_u_lower_median_even
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    {u v : Fin n} (hMis : MisorderedPair C (u, v))
    (hpar : n % 2 = 0)
    (hu_med : (C u).1.rank.val + 1 = n / 2)
    (hv_upper : (C v).1.rank.val + 1 = n / 2 + 1)
    (hn_ge_4 : 4 ≤ n) :
    InSrank (C.step (protocolPEM n trank Rmax rankDelta) u v) ∧
    misorderedCount (C.step (protocolPEM n trank Rmax rankDelta) u v)
      < misorderedCount C :=
  swap_step_decreases_at_misorder_of_role_settled hRank hC hMis
    (transitionPEM_role_settled_at_misorder_u_lower_median_even
      hRank hC hMis hpar hu_med hv_upper hn_ge_4)

/-! ### Median-corner case (odd n, u at median, v not at max, timer pos) -/

set_option maxHeartbeats 8000000 in
/-- Specific case: odd `n`, u at median rank, v not at max rank,
`(C u).1.timer ≥ 1`.  Under these, transitionPEM's result is
`((C v).1, {(C u).1 with answer := opinionToAnswer (C v).2})`. -/
theorem transitionPEM_at_misordered_u_median_odd_v_not_max
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    {u v : Fin n} (hMis : MisorderedPair C (u, v))
    (hpar : ¬ n % 2 = 0)
    (hu_med : (C u).1.rank.val + 1 = ceilHalf n)
    (hv_no_max : (C v).1.rank.val + 1 ≠ n)
    (h_timer : 1 ≤ (C u).1.timer) :
    transitionPEM n trank Rmax rankDelta (C u, C v)
      = ((C v).1, {(C u).1 with answer := opinionToAnswer (C v).2}) := by
  obtain ⟨huB, hvA, hlt⟩ := hMis
  have hsu : (C u).1.role = .Settled := hC.allSettled u
  have hsv : (C v).1.role = .Settled := hC.allSettled v
  have hRD : rankDelta ((C u).1, (C v).1) = ((C u).1, (C v).1) :=
    hRank (C u).1 (C v).1 hsu hsv (ne_of_lt hlt)
  have hswap : (C u).1.rank < (C v).1.rank ∧ (C u).2 = Opinion.B ∧ (C v).2 = Opinion.A :=
    ⟨hlt, huB, hvA⟩
  have hb0_no_med : ¬ ((C v).1.rank.val + 1 = ceilHalf n) := by
    have : (C u).1.rank.val < (C v).1.rank.val := hlt; omega
  have h_no_inner_A : ¬ ((C u).1.rank.val + 1 = n) := by
    have hvlt : (C v).1.rank.val < n := (C v).1.rank.isLt; omega
  unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4 phase4_swap phase4_decide phase4_propagate
  simp only [hRD, hsu, hsv, ne_eq,
    role_settled_ne_resetting,
    not_true_eq_false, not_false_eq_true,
    false_and, and_false, if_false,
    and_self, if_true, hswap, hpar, hb0_no_med, hu_med, h_no_inner_A, hv_no_max]
  -- After this simp:
  --   * Phase 1-3 collapsed
  --   * Phase 4 swap fired: (b₀, b₁) = ((C v).1, (C u).1)
  --   * n is odd: pick odd-n decision branch
  --   * Decision: b₀ not at median → unchanged; b₁ at median → answer := opinionToAnswer x₁
  --   * Propagation: case A doesn't fire (b₀ not at median); case B fires (b₁ at median)
  --   * Inner timer-dec: case A doesn't fire (rank_u < n already); case B inner = (rank_v + 1 = n) which is hv_no_max excluded
  --   * Reset: b₁.timer = (C u).1.timer ≥ 1, so timer ≠ 0, reset blocked.
  -- The result is ((C v).1, {(C u).1 with answer := opinionToAnswer (C v).2}).
  -- Split any remaining if-then-elses; reset branches contradict h_timer ≥ 1.
  split_ifs with h
  · exfalso; exact absurd h.1 (by omega)
  · rfl

/-! ### Median-corner case (odd n, u at median, v AT max, timer ≥ 2) -/

set_option maxHeartbeats 8000000 in
/-- Specific case: odd `n`, u at median rank, v AT max rank
(`(C v).1.rank.val + 1 = n`), `(C u).1.timer ≥ 2`.  The inner timer-dec
fires (because v is at max), reducing u.timer by 1; the post-dec timer is
`(C u).1.timer - 1 ≥ 1`, blocking reset.  Result is the swap with
`b₁.timer` decremented and `b₁.answer` set by the decision phase. -/
theorem transitionPEM_at_misordered_u_median_odd_v_max
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    {u v : Fin n} (hMis : MisorderedPair C (u, v))
    (hpar : ¬ n % 2 = 0)
    (hu_med : (C u).1.rank.val + 1 = ceilHalf n)
    (hv_max : (C v).1.rank.val + 1 = n)
    (h_timer : 2 ≤ (C u).1.timer) :
    transitionPEM n trank Rmax rankDelta (C u, C v)
      = ((C v).1,
         {(C u).1 with answer := opinionToAnswer (C v).2,
                       timer := (C u).1.timer - 1}) := by
  obtain ⟨huB, hvA, hlt⟩ := hMis
  have hsu : (C u).1.role = .Settled := hC.allSettled u
  have hsv : (C v).1.role = .Settled := hC.allSettled v
  have hRD : rankDelta ((C u).1, (C v).1) = ((C u).1, (C v).1) :=
    hRank (C u).1 (C v).1 hsu hsv (ne_of_lt hlt)
  have hswap : (C u).1.rank < (C v).1.rank ∧ (C u).2 = Opinion.B ∧ (C v).2 = Opinion.A :=
    ⟨hlt, huB, hvA⟩
  have hb0_no_med : ¬ ((C v).1.rank.val + 1 = ceilHalf n) := by
    have : (C u).1.rank.val < (C v).1.rank.val := hlt; omega
  have h_no_inner_A : ¬ ((C u).1.rank.val + 1 = n) := by
    have hvlt : (C v).1.rank.val < n := (C v).1.rank.isLt; omega
  -- Re-state hb0_no_med after substituting (C v).1.rank.val + 1 → n (via hv_max).
  have hN_ne_ceil : ¬ (n = ceilHalf n) := by
    have hcl : (C u).1.rank.val < (C v).1.rank.val := hlt; omega
  unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4 phase4_swap phase4_decide phase4_propagate
  simp only [hRD, hsu, hsv, ne_eq,
    role_settled_ne_resetting,
    not_true_eq_false, not_false_eq_true,
    false_and, and_false, if_false,
    and_self, if_true, hswap, hpar, hb0_no_med, hu_med, h_no_inner_A, hv_max,
    hN_ne_ceil]
  -- After simp: inner timer-dec on b₁ fires (v at max).
  -- Reset cond: b₁.timer = (C u).1.timer - 1 ≥ 1 (h_timer ≥ 2), reset blocked.
  split_ifs with h
  · exfalso; exact absurd h.1 (by omega)
  · rfl

/-! ### Role preservation: median-corner case -/

/-- Corollary: at the odd-n median-corner misorder pair with positive timer,
both result components are `.Settled` (the first equals `(C v).1` which is
Settled by `hC.allSettled v`, and the second is `(C u).1` with only its
`.answer` updated). -/
theorem transitionPEM_role_settled_at_misorder_u_median_odd_v_not_max
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    {u v : Fin n} (hMis : MisorderedPair C (u, v))
    (hpar : ¬ n % 2 = 0)
    (hu_med : (C u).1.rank.val + 1 = ceilHalf n)
    (hv_no_max : (C v).1.rank.val + 1 ≠ n)
    (h_timer : 1 ≤ (C u).1.timer) :
    (transitionPEM n trank Rmax rankDelta (C u, C v)).1.role = Role.Settled ∧
    (transitionPEM n trank Rmax rankDelta (C u, C v)).2.role = Role.Settled := by
  rw [transitionPEM_at_misordered_u_median_odd_v_not_max
        hRank hC hMis hpar hu_med hv_no_max h_timer]
  refine ⟨hC.allSettled v, ?_⟩
  -- second component is `{(C u).1 with answer := ...}` — its `.role`
  -- equals `(C u).1.role`, which is `.Settled` by `hC.allSettled u`.
  exact hC.allSettled u

/-- Unconditional swap-step decrease for the median-corner case (odd n,
u at median, v not at max, positive timer at u). -/
theorem swap_step_decreases_at_misorder_u_median_odd_v_not_max
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    {u v : Fin n} (hMis : MisorderedPair C (u, v))
    (hpar : ¬ n % 2 = 0)
    (hu_med : (C u).1.rank.val + 1 = ceilHalf n)
    (hv_no_max : (C v).1.rank.val + 1 ≠ n)
    (h_timer : 1 ≤ (C u).1.timer) :
    InSrank (C.step (protocolPEM n trank Rmax rankDelta) u v) ∧
    misorderedCount (C.step (protocolPEM n trank Rmax rankDelta) u v)
      < misorderedCount C :=
  swap_step_decreases_at_misorder_of_role_settled hRank hC hMis
    (transitionPEM_role_settled_at_misorder_u_median_odd_v_not_max
      hRank hC hMis hpar hu_med hv_no_max h_timer)

/-- Role-Settled at the odd-n median-corner with v at max + timer ≥ 2. -/
theorem transitionPEM_role_settled_at_misorder_u_median_odd_v_max
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    {u v : Fin n} (hMis : MisorderedPair C (u, v))
    (hpar : ¬ n % 2 = 0)
    (hu_med : (C u).1.rank.val + 1 = ceilHalf n)
    (hv_max : (C v).1.rank.val + 1 = n)
    (h_timer : 2 ≤ (C u).1.timer) :
    (transitionPEM n trank Rmax rankDelta (C u, C v)).1.role = Role.Settled ∧
    (transitionPEM n trank Rmax rankDelta (C u, C v)).2.role = Role.Settled := by
  rw [transitionPEM_at_misordered_u_median_odd_v_max
        hRank hC hMis hpar hu_med hv_max h_timer]
  exact ⟨hC.allSettled v, hC.allSettled u⟩

/-- Unconditional swap-step decrease for the odd-n median-corner with v at
max + timer ≥ 2. -/
theorem swap_step_decreases_at_misorder_u_median_odd_v_max
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    {u v : Fin n} (hMis : MisorderedPair C (u, v))
    (hpar : ¬ n % 2 = 0)
    (hu_med : (C u).1.rank.val + 1 = ceilHalf n)
    (hv_max : (C v).1.rank.val + 1 = n)
    (h_timer : 2 ≤ (C u).1.timer) :
    InSrank (C.step (protocolPEM n trank Rmax rankDelta) u v) ∧
    misorderedCount (C.step (protocolPEM n trank Rmax rankDelta) u v)
      < misorderedCount C :=
  swap_step_decreases_at_misorder_of_role_settled hRank hC hMis
    (transitionPEM_role_settled_at_misorder_u_median_odd_v_max
      hRank hC hMis hpar hu_med hv_max h_timer)

/-! ### Unified swap-step: non-median OR median-corner-with-timer -/

/-- Unified swap-step single-step decrease: at any misorder pair that is
either fully non-median, OR (under odd `n`) at the median-corner configuration
`(u at median, v not at max, u.timer ≥ 1)`, `transitionPEM` preserves InSrank
and strictly decreases the misordered count. -/
theorem swap_step_decreases_non_median_or_median_corner
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    {u v : Fin n} (hMis : MisorderedPair C (u, v))
    (h_case :
      ((C u).1.rank.val + 1 ≠ ceilHalf n ∧ (C v).1.rank.val + 1 ≠ ceilHalf n) ∨
      (¬ n % 2 = 0 ∧ (C u).1.rank.val + 1 = ceilHalf n ∧
        (C v).1.rank.val + 1 ≠ n ∧ 1 ≤ (C u).1.timer)) :
    InSrank (C.step (protocolPEM n trank Rmax rankDelta) u v) ∧
    misorderedCount (C.step (protocolPEM n trank Rmax rankDelta) u v)
      < misorderedCount C := by
  rcases h_case with ⟨hu_no_med, hv_no_med⟩ | ⟨hpar, hu_med, hv_no_max, h_timer⟩
  · exact swap_step_non_median_decreases hRank hC hMis hu_no_med hv_no_med
  · exact swap_step_decreases_at_misorder_u_median_odd_v_not_max
      hRank hC hMis hpar hu_med hv_no_max h_timer

/-! ### Lift unified swap-step to swap-phase reachability -/

/-- Swap-phase reachability via the unified swap-step: from any `InSrank`
with positive count, if we always have a witnessing misorder pair that is
either non-median or median-corner-with-timer, we reach `InSswap`. -/
theorem swap_reaches_Sswap_via_unified
    [Inhabited (Fin n × Fin n)]
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    (hExists : ∀ C : Config (AgentState n) Opinion n, InSrank C →
                0 < misorderedCount C →
                ∃ u v : Fin n, MisorderedPair C (u, v) ∧
                  (((C u).1.rank.val + 1 ≠ ceilHalf n ∧
                    (C v).1.rank.val + 1 ≠ ceilHalf n) ∨
                   (¬ n % 2 = 0 ∧ (C u).1.rank.val + 1 = ceilHalf n ∧
                    (C v).1.rank.val + 1 ≠ n ∧ 1 ≤ (C u).1.timer))) :
    ∀ C : Config (AgentState n) Opinion n, InSrank C →
      ∃ (γ : DetScheduler n) (t : ℕ),
        InSswap (execution (protocolPEM n trank Rmax rankDelta) C γ t) := by
  apply swap_reaches_Sswap_of_singleStep
    (trank := trank) (Rmax := Rmax) (rankDelta := rankDelta)
  intro C hC hpos
  obtain ⟨u, v, hMis, hcase⟩ := hExists C hC hpos
  exact ⟨u, v, swap_step_decreases_non_median_or_median_corner hRank hC hMis hcase⟩

/-- Theorem 4 corollary using the unified swap-step (covers both non-median
and median-corner-with-timer misorder configurations). -/
theorem P_EM_solves_SSEM_via_unified_swap_and_trivial_decision
    [Inhabited (Fin n × Fin n)]
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    (hRankPhase : ∀ C₀ : Config (AgentState n) Opinion n,
      ∃ (γ : DetScheduler n) (t : ℕ),
        InSrank (execution (protocolPEM n trank Rmax rankDelta) C₀ γ t))
    (hExists : ∀ C : Config (AgentState n) Opinion n, InSrank C →
                0 < misorderedCount C →
                ∃ u v : Fin n, MisorderedPair C (u, v) ∧
                  (((C u).1.rank.val + 1 ≠ ceilHalf n ∧
                    (C v).1.rank.val + 1 ≠ ceilHalf n) ∨
                   (¬ n % 2 = 0 ∧ (C u).1.rank.val + 1 = ceilHalf n ∧
                    (C v).1.rank.val + 1 ≠ n ∧ 1 ≤ (C u).1.timer)))
    (hSwapImpliesSout : ∀ C : Config (AgentState n) Opinion n, InSswap C → InSout C) :
    SolvesSSEM (protocolPEM n trank Rmax rankDelta) n := by
  apply P_EM_solves_SSEM_via_phases hRank hRankPhase
    (swap_reaches_Sswap_via_unified hRank hExists)
  intro C hSwap
  refine ⟨fun _ => default, 0, ?_⟩
  refine { allSettled := hSwap.allSettled, ranks_inj := hSwap.ranks_inj,
           input_rank := hSwap.input_rank, allAnswerCorrect := ?_ }
  exact hSwapImpliesSout C hSwap

/-! ### Four-way unified swap-step -/

/-- Four-way unified swap-step covering:
  (i) any non-median misorder pair, or
  (ii) odd-`n` median-corner with v not at max and `u.timer ≥ 1`, or
  (iii) odd-`n` median-corner with v AT max and `u.timer ≥ 2`, or
  (iv) even-`n` median-pair with `n ≥ 4`. -/
theorem swap_step_decreases_four_way
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    {u v : Fin n} (hMis : MisorderedPair C (u, v))
    (h_case :
      ((C u).1.rank.val + 1 ≠ ceilHalf n ∧ (C v).1.rank.val + 1 ≠ ceilHalf n) ∨
      (¬ n % 2 = 0 ∧ (C u).1.rank.val + 1 = ceilHalf n ∧
        (C v).1.rank.val + 1 ≠ n ∧ 1 ≤ (C u).1.timer) ∨
      (¬ n % 2 = 0 ∧ (C u).1.rank.val + 1 = ceilHalf n ∧
        (C v).1.rank.val + 1 = n ∧ 2 ≤ (C u).1.timer) ∨
      (n % 2 = 0 ∧ (C u).1.rank.val + 1 = n / 2 ∧
        (C v).1.rank.val + 1 = n / 2 + 1 ∧ 4 ≤ n)) :
    InSrank (C.step (protocolPEM n trank Rmax rankDelta) u v) ∧
    misorderedCount (C.step (protocolPEM n trank Rmax rankDelta) u v)
      < misorderedCount C := by
  rcases h_case with
    ⟨hu_no_med, hv_no_med⟩
    | ⟨hpar, hu_med, hv_no_max, h_timer⟩
    | ⟨hpar, hu_med, hv_max, h_timer⟩
    | ⟨hpar, hu_lower, hv_upper, hn_ge_4⟩
  · exact swap_step_non_median_decreases hRank hC hMis hu_no_med hv_no_med
  · exact swap_step_decreases_at_misorder_u_median_odd_v_not_max
      hRank hC hMis hpar hu_med hv_no_max h_timer
  · exact swap_step_decreases_at_misorder_u_median_odd_v_max
      hRank hC hMis hpar hu_med hv_max h_timer
  · exact swap_step_decreases_at_misorder_u_lower_median_even
      hRank hC hMis hpar hu_lower hv_upper hn_ge_4

/-! ### Three-way unified swap-step (non-median ∨ odd-median-corner ∨ even-median-pair) -/

/-- Three-way unified swap-step single-step decrease covering:
  (i) any non-median misorder pair, or
  (ii) the odd-`n` median-corner case with positive timer at `u`, or
  (iii) the even-`n` median-pair case with `n ≥ 4`. -/
theorem swap_step_decreases_three_way
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    {u v : Fin n} (hMis : MisorderedPair C (u, v))
    (h_case :
      ((C u).1.rank.val + 1 ≠ ceilHalf n ∧ (C v).1.rank.val + 1 ≠ ceilHalf n) ∨
      (¬ n % 2 = 0 ∧ (C u).1.rank.val + 1 = ceilHalf n ∧
        (C v).1.rank.val + 1 ≠ n ∧ 1 ≤ (C u).1.timer) ∨
      (n % 2 = 0 ∧ (C u).1.rank.val + 1 = n / 2 ∧
        (C v).1.rank.val + 1 = n / 2 + 1 ∧ 4 ≤ n)) :
    InSrank (C.step (protocolPEM n trank Rmax rankDelta) u v) ∧
    misorderedCount (C.step (protocolPEM n trank Rmax rankDelta) u v)
      < misorderedCount C := by
  rcases h_case with
    ⟨hu_no_med, hv_no_med⟩
    | ⟨hpar, hu_med, hv_no_max, h_timer⟩
    | ⟨hpar, hu_lower, hv_upper, hn_ge_4⟩
  · exact swap_step_non_median_decreases hRank hC hMis hu_no_med hv_no_med
  · exact swap_step_decreases_at_misorder_u_median_odd_v_not_max
      hRank hC hMis hpar hu_med hv_no_max h_timer
  · exact swap_step_decreases_at_misorder_u_lower_median_even
      hRank hC hMis hpar hu_lower hv_upper hn_ge_4

/-- Swap-phase reachability via the three-way unified swap-step. -/
theorem swap_reaches_Sswap_via_three_way
    [Inhabited (Fin n × Fin n)]
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    (hExists : ∀ C : Config (AgentState n) Opinion n, InSrank C →
                0 < misorderedCount C →
                ∃ u v : Fin n, MisorderedPair C (u, v) ∧
                  (((C u).1.rank.val + 1 ≠ ceilHalf n ∧
                    (C v).1.rank.val + 1 ≠ ceilHalf n) ∨
                   (¬ n % 2 = 0 ∧ (C u).1.rank.val + 1 = ceilHalf n ∧
                    (C v).1.rank.val + 1 ≠ n ∧ 1 ≤ (C u).1.timer) ∨
                   (n % 2 = 0 ∧ (C u).1.rank.val + 1 = n / 2 ∧
                    (C v).1.rank.val + 1 = n / 2 + 1 ∧ 4 ≤ n))) :
    ∀ C : Config (AgentState n) Opinion n, InSrank C →
      ∃ (γ : DetScheduler n) (t : ℕ),
        InSswap (execution (protocolPEM n trank Rmax rankDelta) C γ t) := by
  apply swap_reaches_Sswap_of_singleStep
    (trank := trank) (Rmax := Rmax) (rankDelta := rankDelta)
  intro C hC hpos
  obtain ⟨u, v, hMis, hcase⟩ := hExists C hC hpos
  exact ⟨u, v, swap_step_decreases_three_way hRank hC hMis hcase⟩

/-- Swap-phase reachability via the four-way unified swap-step. -/
theorem swap_reaches_Sswap_via_four_way
    [Inhabited (Fin n × Fin n)]
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    (hExists : ∀ C : Config (AgentState n) Opinion n, InSrank C →
                0 < misorderedCount C →
                ∃ u v : Fin n, MisorderedPair C (u, v) ∧
                  (((C u).1.rank.val + 1 ≠ ceilHalf n ∧
                    (C v).1.rank.val + 1 ≠ ceilHalf n) ∨
                   (¬ n % 2 = 0 ∧ (C u).1.rank.val + 1 = ceilHalf n ∧
                    (C v).1.rank.val + 1 ≠ n ∧ 1 ≤ (C u).1.timer) ∨
                   (¬ n % 2 = 0 ∧ (C u).1.rank.val + 1 = ceilHalf n ∧
                    (C v).1.rank.val + 1 = n ∧ 2 ≤ (C u).1.timer) ∨
                   (n % 2 = 0 ∧ (C u).1.rank.val + 1 = n / 2 ∧
                    (C v).1.rank.val + 1 = n / 2 + 1 ∧ 4 ≤ n))) :
    ∀ C : Config (AgentState n) Opinion n, InSrank C →
      ∃ (γ : DetScheduler n) (t : ℕ),
        InSswap (execution (protocolPEM n trank Rmax rankDelta) C γ t) := by
  apply swap_reaches_Sswap_of_singleStep
    (trank := trank) (Rmax := Rmax) (rankDelta := rankDelta)
  intro C hC hpos
  obtain ⟨u, v, hMis, hcase⟩ := hExists C hC hpos
  exact ⟨u, v, swap_step_decreases_four_way hRank hC hMis hcase⟩

/-- Theorem 4 corollary using the three-way unified swap-step. -/
theorem P_EM_solves_SSEM_via_three_way_swap_and_trivial_decision
    [Inhabited (Fin n × Fin n)]
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    (hRankPhase : ∀ C₀ : Config (AgentState n) Opinion n,
      ∃ (γ : DetScheduler n) (t : ℕ),
        InSrank (execution (protocolPEM n trank Rmax rankDelta) C₀ γ t))
    (hExists : ∀ C : Config (AgentState n) Opinion n, InSrank C →
                0 < misorderedCount C →
                ∃ u v : Fin n, MisorderedPair C (u, v) ∧
                  (((C u).1.rank.val + 1 ≠ ceilHalf n ∧
                    (C v).1.rank.val + 1 ≠ ceilHalf n) ∨
                   (¬ n % 2 = 0 ∧ (C u).1.rank.val + 1 = ceilHalf n ∧
                    (C v).1.rank.val + 1 ≠ n ∧ 1 ≤ (C u).1.timer) ∨
                   (n % 2 = 0 ∧ (C u).1.rank.val + 1 = n / 2 ∧
                    (C v).1.rank.val + 1 = n / 2 + 1 ∧ 4 ≤ n)))
    (hSwapImpliesSout : ∀ C : Config (AgentState n) Opinion n, InSswap C → InSout C) :
    SolvesSSEM (protocolPEM n trank Rmax rankDelta) n := by
  apply P_EM_solves_SSEM_via_phases hRank hRankPhase
    (swap_reaches_Sswap_via_three_way hRank hExists)
  intro C hSwap
  refine ⟨fun _ => default, 0, ?_⟩
  refine { allSettled := hSwap.allSettled, ranks_inj := hSwap.ranks_inj,
           input_rank := hSwap.input_rank, allAnswerCorrect := ?_ }
  exact hSwapImpliesSout C hSwap

/-- Theorem 4 corollary using the four-way unified swap-step. -/
theorem P_EM_solves_SSEM_via_four_way_swap_and_trivial_decision
    [Inhabited (Fin n × Fin n)]
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    (hRankPhase : ∀ C₀ : Config (AgentState n) Opinion n,
      ∃ (γ : DetScheduler n) (t : ℕ),
        InSrank (execution (protocolPEM n trank Rmax rankDelta) C₀ γ t))
    (hExists : ∀ C : Config (AgentState n) Opinion n, InSrank C →
                0 < misorderedCount C →
                ∃ u v : Fin n, MisorderedPair C (u, v) ∧
                  (((C u).1.rank.val + 1 ≠ ceilHalf n ∧
                    (C v).1.rank.val + 1 ≠ ceilHalf n) ∨
                   (¬ n % 2 = 0 ∧ (C u).1.rank.val + 1 = ceilHalf n ∧
                    (C v).1.rank.val + 1 ≠ n ∧ 1 ≤ (C u).1.timer) ∨
                   (¬ n % 2 = 0 ∧ (C u).1.rank.val + 1 = ceilHalf n ∧
                    (C v).1.rank.val + 1 = n ∧ 2 ≤ (C u).1.timer) ∨
                   (n % 2 = 0 ∧ (C u).1.rank.val + 1 = n / 2 ∧
                    (C v).1.rank.val + 1 = n / 2 + 1 ∧ 4 ≤ n)))
    (hSwapImpliesSout : ∀ C : Config (AgentState n) Opinion n, InSswap C → InSout C) :
    SolvesSSEM (protocolPEM n trank Rmax rankDelta) n := by
  apply P_EM_solves_SSEM_via_phases hRank hRankPhase
    (swap_reaches_Sswap_via_four_way hRank hExists)
  intro C hSwap
  refine ⟨fun _ => default, 0, ?_⟩
  refine { allSettled := hSwap.allSettled, ranks_inj := hSwap.ranks_inj,
           input_rank := hSwap.input_rank, allAnswerCorrect := ?_ }
  exact hSwapImpliesSout C hSwap

end SSEM
