/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Timer Descent Without Swap (InSswap case)

At an `InSswap` configuration, scheduling the median agent against the
max-rank agent produces NO swap. The propagation step decrements the
median's timer by 1.
-/

import Ripple.PopulationProtocol.Majority.SSEM.Convergence.MedianWitnesses

namespace SSEM

variable {n : ℕ}

private theorem ceilHalf_lt_of_ge_two (hn : 2 ≤ n) : ceilHalf n < n := by
  unfold ceilHalf; omega

/-! ### The median-max pair properties at InSswap -/

theorem InSswap.median_input_A
    {C : Config (AgentState n) Opinion n}
    (hC : InSswap C)
    {μ : Fin n} (hμ : (C μ).1.rank.val + 1 = ceilHalf n)
    (hA_ge : ceilHalf n ≤ nAOf C) :
    (C μ).2 = Opinion.A := by
  rw [hC.input_rank μ]; omega

theorem InSswap.max_input_B
    {C : Config (AgentState n) Opinion n}
    (hC : InSswap C)
    {v : Fin n} (hv : (C v).1.rank.val + 1 = n)
    (hB_exists : nAOf C < n) :
    (C v).2 = Opinion.B := by
  have h_not_A : ¬ ((C v).1.rank.val < nAOf C) := by omega
  rw [← not_iff_not.mpr (hC.input_rank v)] at h_not_A
  push_neg at h_not_A
  cases h : (C v).2 with
  | A => exact absurd h h_not_A
  | B => rfl

/-! ### Step-level result for (median, max) no-swap, odd n, timer ≥ 2

The transition at this pair produces:
  * μ's state: answer → opinionToAnswer(input), timer → timer - 1, rank/role unchanged
  * v's state: unchanged
  * All other agents: unchanged
  * All inputs: unchanged
-/

set_option maxHeartbeats 16000000 in
theorem step_at_median_max_no_swap_odd
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n} (hC : InSswap C)
    (hn : 2 ≤ n)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (hv_max : (C v).1.rank.val + 1 = n)
    (hpar : ¬ n % 2 = 0)
    (hμ_input_A : (C μ).2 = Opinion.A)
    (h_timer : 2 ≤ (C μ).1.timer) :
    let P := protocolPEM n trank Rmax rankDelta
    let C' := C.step P μ v
    -- μ's timer decreases, answer set, rank/role preserved
    (C' μ).1.timer = (C μ).1.timer - 1 ∧
    (C' μ).1.answer = opinionToAnswer (C μ).2 ∧
    (C' μ).1.rank = (C μ).1.rank ∧
    (C' μ).1.role = (C μ).1.role ∧
    -- v unchanged
    (C' v).1 = (C v).1 ∧
    -- others unchanged
    (∀ w, w ≠ μ → w ≠ v → C' w = C w) ∧
    -- inputs preserved
    (∀ w, (C' w).2 = (C w).2) := by
  -- The proof traces through transitionPEM: rankDelta is identity (both
  -- Settled), no role transition, no swap (μ has input A), odd-n decision
  -- sets median's answer, propagation decrements timer, reset doesn't fire
  -- (timer - 1 ≥ 1).
  have hsu : (C μ).1.role = .Settled := hC.allSettled μ
  have hsv : (C v).1.role = .Settled := hC.allSettled v
  have hRD : rankDelta ((C μ).1, (C v).1) = ((C μ).1, (C v).1) :=
    hRank (C μ).1 (C v).1 hsu hsv (by intro h; have := congrArg Fin.val h; unfold ceilHalf at hμ_med; omega)
  have h_ceil_lt : ceilHalf n < n := ceilHalf_lt_of_ge_two hn
  have hv_not_med : (C v).1.rank.val + 1 ≠ ceilHalf n := by omega
  have hμ_not_max : (C μ).1.rank.val + 1 ≠ n := by omega
  have hvμ : v ≠ μ := Ne.symm hμv
  -- Compute the transition result
  have hno_swap : ¬ ((C μ).1.rank < (C v).1.rank ∧ (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A) := by
    rintro ⟨_, hB, _⟩; rw [hμ_input_A] at hB; exact Opinion.noConfusion hB
  have hN_ne_ceil : ¬ (n = ceilHalf n) := by omega
  have htr : transitionPEM n trank Rmax rankDelta (C μ, C v) =
    ({(C μ).1 with answer := opinionToAnswer (C μ).2,
                   timer := (C μ).1.timer - 1},
     (C v).1) := by
    unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4 phase4_swap phase4_decide phase4_propagate
    simp only [hRD, hsu, hsv, ne_eq,
      role_settled_ne_resetting,
      not_true_eq_false, not_false_eq_true,
      false_and, and_false, if_false,
      and_self, if_true, hno_swap, hpar, hμ_med, hv_not_med, hv_max, hN_ne_ceil]
    split_ifs with h
    · exfalso; obtain ⟨h1, _⟩ := h; omega
    · rfl
  -- Extract each component
  set P := protocolPEM n trank Rmax rankDelta
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- timer
    show (C.step P μ v μ).1.timer = (C μ).1.timer - 1
    unfold Config.step; simp only [if_neg hμv, if_pos rfl]
    show (transitionPEM n trank Rmax rankDelta (C μ, C v)).1.timer = _
    rw [htr]
  · -- answer
    show (C.step P μ v μ).1.answer = opinionToAnswer (C μ).2
    unfold Config.step; simp only [if_neg hμv, if_pos rfl]
    show (transitionPEM n trank Rmax rankDelta (C μ, C v)).1.answer = _
    rw [htr]
  · -- rank
    show (C.step P μ v μ).1.rank = (C μ).1.rank
    unfold Config.step; simp only [if_neg hμv, if_pos rfl]
    show (transitionPEM n trank Rmax rankDelta (C μ, C v)).1.rank = _
    rw [htr]
  · -- role
    show (C.step P μ v μ).1.role = (C μ).1.role
    unfold Config.step; simp only [if_neg hμv, if_pos rfl]
    show (transitionPEM n trank Rmax rankDelta (C μ, C v)).1.role = _
    rw [htr]
  · -- v unchanged
    show (C.step P μ v v).1 = (C v).1
    unfold Config.step; rw [if_neg hμv, if_neg hvμ, if_pos rfl]
    show (transitionPEM n trank Rmax rankDelta (C μ, C v)).2 = _
    rw [htr]
  · -- others
    intro w hw hwv
    show C.step P μ v w = C w
    unfold Config.step; simp only [if_neg hμv, if_neg hw, if_neg hwv]
  · -- inputs
    intro w
    show (C.step P μ v w).2 = (C w).2
    unfold Config.step
    simp only [if_neg hμv]
    split
    · rename_i h; simp only [h]
    · split
      · rename_i _ h; simp only [h]
      · rfl

/-! ### InSswap preservation -/

theorem step_at_median_max_no_swap_odd_preserves_InSswap
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n} (hC : InSswap C)
    (hn : 2 ≤ n)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (hv_max : (C v).1.rank.val + 1 = n)
    (hpar : ¬ n % 2 = 0)
    (hμ_input_A : (C μ).2 = Opinion.A)
    (h_timer : 2 ≤ (C μ).1.timer) :
    InSswap (C.step (protocolPEM n trank Rmax rankDelta) μ v) := by
  set P := protocolPEM n trank Rmax rankDelta
  obtain ⟨_, _, h_rank, h_role, h_v, h_others, h_inputs⟩ :=
    step_at_median_max_no_swap_odd hRank hC hn hμv hμ_med hv_max hpar hμ_input_A h_timer
  -- Ranks preserved at every position
  have h_rank_w : ∀ w, (C.step P μ v w).1.rank = (C w).1.rank := by
    intro w
    by_cases hw : w = μ
    · rw [hw, h_rank]
    · by_cases hwv : w = v
      · rw [hwv]; exact congrArg (fun s => s.rank) h_v
      · rw [show C.step P μ v w = C w from h_others w hw hwv]
  -- nAOf preserved
  have h_nA : nAOf (C.step P μ v) = nAOf C := by
    unfold nAOf Config.agentsWithInput Config.inputOf
    congr 1; ext w; simp only [Finset.mem_filter]
    exact ⟨fun ⟨hm, h⟩ => ⟨hm, by rw [h_inputs] at h; exact h⟩,
           fun ⟨hm, h⟩ => ⟨hm, by rw [h_inputs]; exact h⟩⟩
  constructor
  · constructor
    · intro w
      by_cases hw : w = μ
      · rw [hw, h_role]; exact hC.allSettled μ
      · by_cases hwv : w = v
        · rw [hwv]; exact congrArg (fun s => s.role) h_v ▸ hC.allSettled v
        · rw [show (C.step P μ v w).1 = (C w).1 from
            congrArg Prod.fst (h_others w hw hwv)]
          exact hC.allSettled w
    · intro w₁ w₂ heq
      have := h_rank_w w₁; have := h_rank_w w₂
      simp only [this, *] at heq; exact hC.ranks_inj heq
  · intro w
    rw [show (C.step P μ v w).2 = (C w).2 from h_inputs w,
        show (C.step P μ v w).1.rank = (C w).1.rank from h_rank_w w,
        h_nA]
    exact hC.input_rank w

/-! ### Timer strictly decreases -/

theorem timer_decreases_at_median_max_no_swap_odd
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n} (hC : InSswap C)
    (hn : 2 ≤ n)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (hv_max : (C v).1.rank.val + 1 = n)
    (hpar : ¬ n % 2 = 0)
    (hμ_input_A : (C μ).2 = Opinion.A)
    (h_timer : 2 ≤ (C μ).1.timer) :
    (C.step (protocolPEM n trank Rmax rankDelta) μ v μ).1.timer + 1 = (C μ).1.timer := by
  obtain ⟨h_timer_eq, _, _, _, _, _, _⟩ :=
    step_at_median_max_no_swap_odd hRank hC hn hμv hμ_med hv_max hpar hμ_input_A h_timer
  rw [h_timer_eq]; omega

/-! ### Multi-step timer descent via iteration

The single-step preserves InSswap and keeps the median at the same
position (no swap). So we can iterate: schedule (μ, v) for T−1 steps
to bring the timer from T down to 1. -/

/-- From InSswap with timer = T ≥ 2, scheduling (μ, v) for T−1 steps brings
the timer down to 1, preserving InSswap throughout.

Proof by strong induction on `(C μ).1.timer`. -/
theorem timer_descent_to_one
    [Inhabited (Fin n × Fin n)]
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {C₀ : Config (AgentState n) Opinion n} (hC₀ : InSswap C₀)
    (hn : 2 ≤ n) (hpar : ¬ n % 2 = 0)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hμ_med : (C₀ μ).1.rank.val + 1 = ceilHalf n)
    (hv_max : (C₀ v).1.rank.val + 1 = n)
    (hμ_input : (C₀ μ).2 = Opinion.A)
    (h_timer : 2 ≤ (C₀ μ).1.timer) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      let Ct := execution (protocolPEM n trank Rmax rankDelta) C₀ γ t
      InSswap Ct ∧
      (Ct μ).1.timer ≤ 1 ∧
      (Ct μ).1.rank.val + 1 = ceilHalf n ∧
      (Ct v).1.rank.val + 1 = n ∧
      (Ct μ).2 = Opinion.A := by
  set P := protocolPEM n trank Rmax rankDelta
  suffices h : ∀ k, ∀ C : Config (AgentState n) Opinion n, InSswap C →
      (C μ).1.rank.val + 1 = ceilHalf n →
      (C v).1.rank.val + 1 = n →
      (C μ).2 = Opinion.A →
      (C μ).1.timer ≤ k →
      2 ≤ (C μ).1.timer →
      ∃ (γ : DetScheduler n) (t : ℕ),
        InSswap (execution P C γ t) ∧
        (execution P C γ t μ).1.timer ≤ 1 ∧
        (execution P C γ t μ).1.rank.val + 1 = ceilHalf n ∧
        (execution P C γ t v).1.rank.val + 1 = n ∧
        (execution P C γ t μ).2 = Opinion.A from
    h (C₀ μ).1.timer C₀ hC₀ hμ_med hv_max hμ_input le_rfl h_timer
  intro k
  induction k with
  | zero => intro C _ _ _ _ hle hge; omega
  | succ k ih =>
    intro C hC hmed hmax hinp hle hge
    obtain ⟨h_timer_eq, _, h_rank, _, _, h_others, h_inputs⟩ :=
      step_at_median_max_no_swap_odd hRank hC hn hμv hmed hmax hpar hinp hge
    set C' := C.step P μ v
    have hC' : InSswap C' := step_at_median_max_no_swap_odd_preserves_InSswap
      hRank hC hn hμv hmed hmax hpar hinp hge
    have hmed' : (C' μ).1.rank.val + 1 = ceilHalf n := by rw [h_rank]; exact hmed
    have hmax' : (C' v).1.rank.val + 1 = n := by
      obtain ⟨_, _, _, _, h_v, _, _⟩ :=
        step_at_median_max_no_swap_odd hRank hC hn hμv hmed hmax hpar hinp hge
      rw [h_v]; exact hmax
    have hinp' : (C' μ).2 = Opinion.A := by rw [h_inputs]; exact hinp
    have htimer' : (C' μ).1.timer = (C μ).1.timer - 1 := h_timer_eq
    by_cases h2 : 2 ≤ (C' μ).1.timer
    · obtain ⟨γ', t', hC_t', htimer_t', hmed_t', hmax_t', hinp_t'⟩ := ih C' hC' hmed' hmax' hinp'
        (by rw [htimer']; omega) h2
      let γ₁ : DetScheduler n := fun _ => (μ, v)
      refine ⟨concatScheduler γ₁ 1 γ', 1 + t', ?_, ?_, ?_, ?_, ?_⟩
      · rw [execution_concat]; exact hC_t'
      · rw [execution_concat]; exact htimer_t'
      · rw [execution_concat]; exact hmed_t'
      · rw [execution_concat]; exact hmax_t'
      · rw [execution_concat]; exact hinp_t'
    · push_neg at h2
      refine ⟨fun _ => (μ, v), 1, hC', ?_, hmed', hmax', hinp'⟩
      rw [show execution P C (fun _ => (μ, v)) 1 = C' from rfl, htimer']
      omega

/-! ### Timer = 0 reset step

When the median has timer = 0 and meets a non-max agent whose answer
differs from the median's (post-decision) answer, the reset fires.
Both agents enter Resetting. -/

set_option maxHeartbeats 16000000 in
/-- At InSswap with timer = 0, scheduling (median, wrong_agent) where
the wrong agent is not at max rank and not at median rank, the reset
fires: both agents enter Resetting with the median's answer propagated.

This is the second piece of the macro-step: after timer descent brings
timer to 0, we find a wrong-answer agent and trigger the reset. -/
theorem step_at_median_timer_zero_reset_fires
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n} (hC : InSswap C)
    (hn : 2 ≤ n)
    {μ w : Fin n} (hμw : μ ≠ w)
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (hw_not_max : (C w).1.rank.val + 1 ≠ n)
    (hw_not_med : (C w).1.rank.val + 1 ≠ ceilHalf n)
    (hpar : ¬ n % 2 = 0)
    (hμ_input_A : (C μ).2 = Opinion.A)
    (h_timer : (C μ).1.timer = 0)
    (h_wrong : (C w).1.answer ≠ opinionToAnswer (C μ).2) :
    let P := protocolPEM n trank Rmax rankDelta
    let C' := C.step P μ w
    (C' μ).1.role = .Resetting ∧
    (C' w).1.role = .Resetting ∧
    (C' w).1.answer = opinionToAnswer (C μ).2 := by
  have hsu : (C μ).1.role = .Settled := hC.allSettled μ
  have hsw : (C w).1.role = .Settled := hC.allSettled w
  have hRD : rankDelta ((C μ).1, (C w).1) = ((C μ).1, (C w).1) :=
    hRank (C μ).1 (C w).1 hsu hsw (by intro h; have := congrArg Fin.val h; omega)
  have hno_swap : ¬ ((C μ).1.rank < (C w).1.rank ∧ (C μ).2 = Opinion.B ∧ (C w).2 = Opinion.A) := by
    rintro ⟨_, hB, _⟩; rw [hμ_input_A] at hB; exact Opinion.noConfusion hB
  have hN_ne_ceil : ¬ (n = ceilHalf n) := by
    have := ceilHalf_lt_of_ge_two hn; omega
  -- Compute the full transition
  have htr : transitionPEM n trank Rmax rankDelta (C μ, C w) =
    ({ (C μ).1 with answer := opinionToAnswer (C μ).2,
                    role := .Resetting, leader := .L, resetcount := Rmax },
     { (C w).1 with answer := opinionToAnswer (C μ).2,
                    role := .Resetting, leader := .L, resetcount := Rmax }) := by
    unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4 phase4_swap phase4_decide phase4_propagate
    simp only [hRD, hsu, hsw, ne_eq,
      role_settled_ne_resetting,
      not_true_eq_false, not_false_eq_true,
      false_and, and_false, if_false,
      and_self, if_true, hno_swap, hpar, hμ_med, hw_not_med, hw_not_max, hN_ne_ceil,
      h_timer]
    split_ifs with h
    · rfl
    · exfalso; apply h; exact ⟨trivial, fun h_eq => h_wrong h_eq.symm⟩
  set P := protocolPEM n trank Rmax rankDelta
  refine ⟨?_, ?_, ?_⟩
  · -- μ's role = Resetting
    show (C.step P μ w μ).1.role = .Resetting
    unfold Config.step; simp only [if_neg hμw, if_pos rfl]
    show (transitionPEM n trank Rmax rankDelta (C μ, C w)).1.role = _
    rw [htr]
  · -- w's role = Resetting
    show (C.step P μ w w).1.role = .Resetting
    unfold Config.step; rw [if_neg hμw, if_neg (Ne.symm hμw), if_pos rfl]
    show (transitionPEM n trank Rmax rankDelta (C μ, C w)).2.role = _
    rw [htr]
  · -- w's answer = opinionToAnswer (C μ).2
    show (C.step P μ w w).1.answer = opinionToAnswer (C μ).2
    unfold Config.step; rw [if_neg hμw, if_neg (Ne.symm hμw), if_pos rfl]
    show (transitionPEM n trank Rmax rankDelta (C μ, C w)).2.answer = _
    rw [htr]

end SSEM
