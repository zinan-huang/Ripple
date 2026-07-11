/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Formal Proof of BurmanConvergence

This file works toward proving `BurmanConvergence` for the concrete
`rankDeltaOSSR` protocol, which is the ONLY remaining gap in the
full formalization of Kanaya et al.'s Theorem 4.

## Strategy

Burman et al. (PODC 2021) Theorem 4.3 proves OPTIMAL-SILENT-SSR
converges in O(n) expected time. For our deterministic formalization,
we need to show the EXISTENCE of a schedule reaching InSrank
(for `ranking`) and InSswap with all correct answers (for `epidemic`).

### Phase structure

1. **Binary-tree rank assignment** (Lemma 4.1): from a single leader
   + n−1 Unsettled agents, a deterministic schedule assigns unique
   ranks to all agents via Protocol 3's recruitment (lines 8-12).

2. **Leader election** (Lemma 4.2): from an awakening configuration,
   the L,L → L,F rule reduces to a single leader with constant
   probability (for deterministic: we can schedule L,L pairs).

3. **PROPAGATE-RESET cycle** (Theorem 3.4): from any partially
   triggered config, reach an awakening config.

4. **Collision/errorcount entry**: from any config, reach a
   partially triggered config via collision detection or errorcount
   timeout.

5. **Epidemic propagation**: the Resetting-phase answer spreading
   (lines 7-8 of Algorithm 1) propagates the correct answer.

### Current file

This file begins with Phase 1 — the binary-tree rank assignment.
-/

import Ripple.PopulationProtocol.Majority.SSEM.Convergence.BurmanProperties
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card

namespace SSEM

open scoped BigOperators

variable {n : ℕ}

/-! ### Binary-tree rank assignment

From a leader (Settled, rank 0, children 0) and n−1 Unsettled agents,
Protocol 3's recruitment (lines 8-12) assigns unique ranks via a
binary tree. Each interaction between a Settled agent with children < 2
and an Unsettled agent recruits the Unsettled agent as a child.

The schedule: repeatedly pair a "ready" Settled agent (children < 2,
valid child rank < n) with any Unsettled agent.

After n−1 such interactions, all agents are Settled with unique ranks
from a binary tree rooted at rank 0 (1-indexed: rank 1).
-/

/-- A config where one agent is the leader (Settled, rank 0) and all
others are Unsettled. -/
def IsLeaderConfig (C : Config (AgentState n) Opinion n) (hn : 0 < n) : Prop :=
  ∃ leader : Fin n,
    (C leader).1.role = .Settled ∧
    (C leader).1.rank = ⟨0, hn⟩ ∧
    (C leader).1.children = 0 ∧
    ∀ w : Fin n, w ≠ leader → (C w).1.role = .Unsettled

/-- Count of Settled agents in a configuration. -/
def settledCount (C : Config (AgentState n) Opinion n) : ℕ :=
  (Finset.univ.filter (fun w => (C w).1.role == .Settled)).card

/-! ### Recruitment step: Settled agent recruits Unsettled agent -/

/-- When a Settled agent with children < 2 and valid child rank
interacts with an Unsettled agent, rankDeltaOSSR recruits the
Unsettled agent as a child in the binary tree. -/
theorem rankDeltaOSSR_recruits
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {s : AgentState n} {t : AgentState n}
    (hs : s.role = .Settled) (ht : t.role = .Unsettled)
    (h_children : s.children < 2)
    (h_valid : 2 * s.rank.val + s.children + 1 < n) :
    let result := rankDeltaOSSR Rmax Emax Dmax hn (s, t)
    result.1.role = .Settled ∧
    result.1.children = s.children + 1 ∧
    result.1.rank = s.rank ∧
    result.2.role = .Settled ∧
    result.2.children = 0 ∧
    result.2.rank = ⟨2 * s.rank.val + s.children + 1, h_valid⟩ := by
  unfold rankDeltaOSSR
  have h_not_res : ¬(s.role = .Resetting ∨ t.role = .Resetting) := by
    rw [hs, ht]; simp
  have h_not_coll : ¬(s.role = .Settled ∧ t.role = .Settled ∧ s.rank = t.rank) := by
    intro ⟨_, h, _⟩; rw [ht] at h; exact Role.noConfusion h
  simp only [h_not_res, h_not_coll, ite_false]
  rw [dif_pos ⟨hs, ht, h_children, h_valid⟩]
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl⟩
  show { s with children := s.children + 1 }.role = .Settled
  exact hs
/-! ### Binary tree rank uniqueness

The binary tree formula `childRank = 2 * parentRank + childIndex + 1`
(0-indexed) assigns unique ranks. Left child: 2r+1, right child: 2r+2.
All ranks in [0, n) are unique because the binary tree is a standard
complete binary tree with n nodes. -/

/-- Child ranks from distinct parents are distinct from each other and
from any parent rank. -/
theorem binary_tree_ranks_distinct
    {r₁ r₂ : ℕ} (h_ne : r₁ ≠ r₂ ∨ True) :
    2 * r₁ + 1 ≠ r₁ ∧ 2 * r₁ + 2 ≠ r₁ := by
  constructor <;> omega

/-! ### Timer initialization at median during recruitment

When a child is recruited at the median rank (rank = ceilHalf n - 1),
transitionPEM Phase 2 (line 51-53) sets its timer to 7*(trank+4).
This ensures the timer ≥ 2 bound needed by BurmanConvergence.ranking.

The timer 7*(trank+4) ≥ 7*4 = 28 ≥ 2 for any trank ≥ 0. -/

theorem timer_init_ge_2 (trank : ℕ) : 2 ≤ 7 * (trank + 4) := by omega

/-! ### Phase A: BurmanConvergence.ranking for InSrank configs

If the initial config is already InSrank with timer ≥ 2, ranking is
trivially satisfied — the empty schedule (t = 0) works. -/

def RankingEndpoint (C : Config (AgentState n) Opinion n) : Prop :=
  InSrank C ∧
    ((∀ μ : Fin n, (C μ).1.rank.val + 1 = ceilHalf n → 2 ≤ (C μ).1.timer) ∨
     IsConsensusConfig C)

theorem ranking_of_InSrank
    [Inhabited (Fin n × Fin n)]
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    {C₀ : Config (AgentState n) Opinion n}
    (hC₀ : InSrank C₀)
    (h_timer : ∀ μ : Fin n, (C₀ μ).1.rank.val + 1 = ceilHalf n →
                2 ≤ (C₀ μ).1.timer) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n trank Rmax rankDelta) C₀ γ t) ∧
      (∀ μ : Fin n,
        (execution (protocolPEM n trank Rmax rankDelta) C₀ γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n trank Rmax rankDelta) C₀ γ t μ).1.timer) :=
  ⟨fun _ => default, 0, hC₀, h_timer⟩

theorem ranking_goal_of_InSrank_timer_or_consensus
    [Inhabited (Fin n × Fin n)]
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    {C₀ : Config (AgentState n) Opinion n}
    (hC₀ : InSrank C₀)
    (hDone :
      (∀ μ : Fin n, (C₀ μ).1.rank.val + 1 = ceilHalf n → 2 ≤ (C₀ μ).1.timer) ∨
      IsConsensusConfig C₀) :
    RankingEndpoint C₀ :=
  ⟨hC₀, hDone⟩

theorem ranking_goal_of_RankingEndpoint
    [Inhabited (Fin n × Fin n)]
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    {C₀ : Config (AgentState n) Opinion n}
    (hEndpoint : RankingEndpoint C₀) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n trank Rmax rankDelta) C₀ γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n trank Rmax rankDelta) C₀ γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n trank Rmax rankDelta) C₀ γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n trank Rmax rankDelta) C₀ γ t)) :=
  ⟨fun _ => default, 0, hEndpoint.1, hEndpoint.2⟩

/-! ### Phase B: Binary tree construction from leader config

From a leader config (one Settled agent + rest Unsettled), construct
a schedule that recruits all agents into a binary tree via Protocol 3.

The schedule pairs "ready" Settled agents (children < 2, valid child
rank < n) with Unsettled agents, one by one. After n-1 steps, all
agents are Settled with unique ranks 0..n-1 from a binary tree. -/

/-- The number of Unsettled agents in a config. -/
def unsettledCount (C : Config (AgentState n) Opinion n) : ℕ :=
  (Finset.univ.filter (fun w => (C w).1.role == .Unsettled)).card

/-! ### Propagation reset: median with timer = 0 triggers reset -/

set_option maxHeartbeats 4000000 in
/-- When the median (timer = 0) meets a non-median agent, and the
post-decision answer at the median differs from v's answer, both go
Resetting. The decision phase sets median's answer to opinionToAnswer
of its input; the propagation then checks timer = 0 AND answers differ.

This is used when median has the correct answer (from decision) but
v has a wrong answer → reset fires → re-rank with fresh timer. -/
theorem propagation_reset_fires_no_swap
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (hv_no_med : (C v).1.rank.val + 1 ≠ ceilHalf n)
    (h_timer : (C μ).1.timer = 0)
    (h_no_swap : ¬((C μ).1.rank < (C v).1.rank ∧ (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A))
    (hpar : ¬ n % 2 = 0)
    (h_post_diff : opinionToAnswer (C μ).2 ≠ (C v).1.answer) :
    (transitionPEM n trank Rmax rankDelta (C μ, C v)).1.role = .Resetting ∧
    (transitionPEM n trank Rmax rankDelta (C μ, C v)).2.role = .Resetting := by
  have hμ_settled : (C μ).1.role = .Settled := hC.allSettled μ
  have hv_settled : (C v).1.role = .Settled := hC.allSettled v
  have h_rank_ne : (C μ).1.rank ≠ (C v).1.rank := by
    intro hEq
    exact hμv (hC.ranks_inj hEq)
  have hRD : rankDelta ((C μ).1, (C v).1) = ((C μ).1, (C v).1) :=
    hRank (C μ).1 (C v).1 hμ_settled hv_settled h_rank_ne
  have htr : transitionPEM n trank Rmax rankDelta (C μ, C v) =
      ({ (C μ).1 with role := .Resetting, leader := .L, resetcount := Rmax, answer := opinionToAnswer ((C μ).2) },
       { (C v).1 with role := .Resetting, leader := .L, resetcount := Rmax, answer := opinionToAnswer ((C μ).2) }) := by
    unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4
      phase4_swap phase4_decide phase4_propagate
    simp only [hRD, hμ_settled, hv_settled, ne_eq,
      role_settled_ne_resetting, not_true_eq_false, not_false_eq_true,
      false_and, and_false, if_false, and_self, if_true, h_no_swap, hpar,
      hμ_med, hv_no_med, h_timer]
    split_ifs <;> simp_all
  constructor <;> rw [htr]

set_option maxHeartbeats 4000000 in
theorem propagation_reset_fires_no_swap_trace
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (hv_no_med : (C v).1.rank.val + 1 ≠ ceilHalf n)
    (h_timer : (C μ).1.timer = 0)
    (h_no_swap : ¬((C μ).1.rank < (C v).1.rank ∧ (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A))
    (hpar : ¬ n % 2 = 0)
    (h_post_diff : opinionToAnswer (C μ).2 ≠ (C v).1.answer) :
    transitionPEM n trank Rmax rankDelta (C μ, C v) =
      ({ (C μ).1 with role := .Resetting, leader := .L, resetcount := Rmax, answer := opinionToAnswer ((C μ).2) },
       { (C v).1 with role := .Resetting, leader := .L, resetcount := Rmax, answer := opinionToAnswer ((C μ).2) }) := by
  have hμ_settled : (C μ).1.role = .Settled := hC.allSettled μ
  have hv_settled : (C v).1.role = .Settled := hC.allSettled v
  have h_rank_ne : (C μ).1.rank ≠ (C v).1.rank := by
    intro hEq
    exact hμv (hC.ranks_inj hEq)
  have hRD : rankDelta ((C μ).1, (C v).1) = ((C μ).1, (C v).1) :=
    hRank (C μ).1 (C v).1 hμ_settled hv_settled h_rank_ne
  unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4
    phase4_swap phase4_decide phase4_propagate
  simp only [hRD, hμ_settled, hv_settled, ne_eq,
    role_settled_ne_resetting, not_true_eq_false, not_false_eq_true,
    false_and, and_false, if_false, and_self, if_true, h_no_swap, hpar,
    hμ_med, hv_no_med, h_timer]
  split_ifs <;> simp_all

theorem trigger_reset_from_InSrank_timer_zero_no_swap_with_snapshot
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (hv_no_med : (C v).1.rank.val + 1 ≠ ceilHalf n)
    (h_timer : (C μ).1.timer = 0)
    (h_no_swap : ¬((C μ).1.rank < (C v).1.rank ∧ (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A))
    (hpar : ¬ n % 2 = 0)
    (h_post_diff : opinionToAnswer (C μ).2 ≠ (C v).1.answer) :
    let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := C.step P μ v
    (C' μ).1.role = .Resetting ∧ (C' μ).1.resetcount = Rmax ∧
      (C' μ).1.leader = .L ∧
    (C' v).1.role = .Resetting ∧ (C' v).1.resetcount = Rmax ∧
      (C' v).1.leader = .L ∧
    ∀ y : Fin n, (C' y).1.role = .Resetting →
      (C' y).1.resetcount = Rmax ∧ (C' y).1.leader = .L := by
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  let C' : Config (AgentState n) Opinion n := C.step P μ v
  have htr :=
    propagation_reset_fires_no_swap_trace
      (trank := Rmax) (Rmax := Rmax)
      (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
      (hRank := rankDeltaOSSR_satisfies_fix)
      (C := C) hC hμv hμ_med hv_no_med h_timer h_no_swap hpar h_post_diff
  have hfst := Config.step_fst_state P C hμv
  have hsnd := Config.step_snd_state P C hμv hμv.symm
  have hμ_role : (C' μ).1.role = .Resetting := by
    dsimp [C']
    rw [congrArg AgentState.role hfst]
    change (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).1.role = .Resetting
    rw [htr]
  have hμ_rc : (C' μ).1.resetcount = Rmax := by
    dsimp [C']
    rw [congrArg AgentState.resetcount hfst]
    change (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).1.resetcount = Rmax
    rw [htr]
  have hμ_leader : (C' μ).1.leader = .L := by
    dsimp [C']
    rw [congrArg AgentState.leader hfst]
    change (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).1.leader = .L
    rw [htr]
  have hv_role : (C' v).1.role = .Resetting := by
    dsimp [C']
    rw [congrArg AgentState.role hsnd]
    change (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).2.role = .Resetting
    rw [htr]
  have hv_rc : (C' v).1.resetcount = Rmax := by
    dsimp [C']
    rw [congrArg AgentState.resetcount hsnd]
    change (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).2.resetcount = Rmax
    rw [htr]
  have hv_leader : (C' v).1.leader = .L := by
    dsimp [C']
    rw [congrArg AgentState.leader hsnd]
    change (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).2.leader = .L
    rw [htr]
  refine ⟨hμ_role, hμ_rc, hμ_leader, hv_role, hv_rc, hv_leader, ?_⟩
  intro y hy_reset
  by_cases hyμ : y = μ
  · subst y
    exact ⟨hμ_rc, hμ_leader⟩
  · by_cases hyv : y = v
    · subst y
      exact ⟨hv_rc, hv_leader⟩
    · have hy_old : C' y = C y := by
        dsimp [C', P]
        simp [Config.step, hμv, hyμ, hyv]
      have hy_settled : (C' y).1.role = .Settled := by
        rw [hy_old]
        exact hC.allSettled y
      rw [hy_settled] at hy_reset
      cases hy_reset

set_option maxHeartbeats 8000000 in
theorem propagation_reset_fires_even_lower_timer_zero_no_swap_trace
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hpar : n % 2 = 0)
    (hμ_lower : (C μ).1.rank.val + 1 = n / 2)
    (hv_not_lower : (C v).1.rank.val + 1 ≠ n / 2)
    (hv_not_upper : (C v).1.rank.val + 1 ≠ n / 2 + 1)
    (h_timer : (C μ).1.timer = 0)
    (h_no_swap : ¬((C μ).1.rank < (C v).1.rank ∧
      (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A))
    (h_post_diff : (C μ).1.answer ≠ (C v).1.answer) :
    transitionPEM n trank Rmax rankDelta (C μ, C v) =
      ({ (C μ).1 with role := .Resetting, leader := .L, resetcount := Rmax },
       { (C v).1 with role := .Resetting, leader := .L, resetcount := Rmax, answer := ((C μ).1).answer }) := by
  have hμ_settled : (C μ).1.role = .Settled := hC.allSettled μ
  have hv_settled : (C v).1.role = .Settled := hC.allSettled v
  have h_rank_ne : (C μ).1.rank ≠ (C v).1.rank := by
    intro hEq
    exact hμv (hC.ranks_inj hEq)
  have hRD : rankDelta ((C μ).1, (C v).1) = ((C μ).1, (C v).1) :=
    hRank (C μ).1 (C v).1 hμ_settled hv_settled h_rank_ne
  have hceil : ceilHalf n = n / 2 := by
    unfold ceilHalf
    omega
  have hμ_ceil : (C μ).1.rank.val + 1 = ceilHalf n := by
    rw [hceil]
    exact hμ_lower
  have hv_not_ceil : (C v).1.rank.val + 1 ≠ ceilHalf n := by
    rw [hceil]
    exact hv_not_lower
  have h_dec1 :
      ¬ ((C μ).1.rank.val + 1 = n / 2 ∧
        (C v).1.rank.val + 1 = n / 2 + 1) := by
    intro h
    exact hv_not_upper h.2
  have h_dec2 :
      ¬ ((C v).1.rank.val + 1 = n / 2 ∧
        (C μ).1.rank.val + 1 = n / 2 + 1) := by
    intro h
    omega
  have h_dec1' :
      ¬ (ceilHalf n = n / 2 ∧ (C v).1.rank.val = n / 2) := by
    intro h
    exact hv_not_upper (by omega)
  have h_dec2' :
      ¬ ((C v).1.rank.val + 1 = n / 2 ∧ ceilHalf n = n / 2 + 1) := by
    intro h
    omega
  have h_dec1a :
      ¬ ((C μ).1.rank.val + 1 = n / 2 ∧ (C v).1.rank.val = n / 2) := by
    intro h
    exact hv_not_upper (by omega)
  have h_dec2a :
      ¬ ((C v).1.rank.val + 1 = n / 2 ∧ (C μ).1.rank.val = n / 2) := by
    intro h
    omega
  have h_reset :
      (C μ).1.timer = 0 ∧ (C μ).1.answer ≠ (C v).1.answer :=
    ⟨h_timer, h_post_diff⟩
  have hswap :
      phase4_swap (C μ).1 (C v).1 (C μ).2 (C v).2 = ((C μ).1, (C v).1) := by
    unfold phase4_swap
    simp [h_no_swap]
  have hdec :
      phase4_decide n (C μ).1 (C v).1 (C μ).2 (C v).2 = ((C μ).1, (C v).1) := by
    unfold phase4_decide
    simp [hpar, h_dec1, h_dec2, h_dec1a, h_dec2a]
  have hprop :
      phase4_propagate n Rmax (C μ).1 (C v).1 =
        ({ (C μ).1 with role := .Resetting, leader := .L, resetcount := Rmax },
         { (C v).1 with role := .Resetting, leader := .L, resetcount := Rmax, answer := ((C μ).1).answer }) := by
    unfold phase4_propagate
    by_cases hvmax : (C v).1.rank.val + 1 = n
    · simp [hμ_ceil, hv_not_ceil, hvmax, h_timer, h_post_diff]
    · simp [hμ_ceil, hv_not_ceil, hvmax, h_timer, h_post_diff]
  unfold transitionPEM transitionPEM_prePhase4 transitionPEM_phase4
  simp [hRD, hμ_settled, hv_settled, role_settled_ne_resetting,
    hswap, hdec, hprop]

theorem trigger_reset_from_InSrank_even_lower_timer_zero_no_swap_with_snapshot
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hpar : n % 2 = 0)
    (hμ_lower : (C μ).1.rank.val + 1 = n / 2)
    (hv_not_lower : (C v).1.rank.val + 1 ≠ n / 2)
    (hv_not_upper : (C v).1.rank.val + 1 ≠ n / 2 + 1)
    (h_timer : (C μ).1.timer = 0)
    (h_no_swap : ¬((C μ).1.rank < (C v).1.rank ∧
      (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A))
    (h_post_diff : (C μ).1.answer ≠ (C v).1.answer) :
    let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := C.step P μ v
    (C' μ).1.role = .Resetting ∧ (C' μ).1.resetcount = Rmax ∧
      (C' μ).1.leader = .L ∧
    (C' v).1.role = .Resetting ∧ (C' v).1.resetcount = Rmax ∧
      (C' v).1.leader = .L ∧
    ∀ y : Fin n, (C' y).1.role = .Resetting →
      (C' y).1.resetcount = Rmax ∧ (C' y).1.leader = .L := by
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  let C' : Config (AgentState n) Opinion n := C.step P μ v
  have htr :=
    propagation_reset_fires_even_lower_timer_zero_no_swap_trace
      (trank := Rmax) (Rmax := Rmax)
      (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
      (hRank := rankDeltaOSSR_satisfies_fix)
      (C := C) hC hμv hpar hμ_lower hv_not_lower hv_not_upper h_timer
      h_no_swap h_post_diff
  have hfst := Config.step_fst_state P C hμv
  have hsnd := Config.step_snd_state P C hμv hμv.symm
  have hμ_role : (C' μ).1.role = .Resetting := by
    dsimp [C']
    rw [congrArg AgentState.role hfst]
    change (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).1.role = .Resetting
    rw [htr]
  have hμ_rc : (C' μ).1.resetcount = Rmax := by
    dsimp [C']
    rw [congrArg AgentState.resetcount hfst]
    change (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).1.resetcount = Rmax
    rw [htr]
  have hμ_leader : (C' μ).1.leader = .L := by
    dsimp [C']
    rw [congrArg AgentState.leader hfst]
    change (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).1.leader = .L
    rw [htr]
  have hv_role : (C' v).1.role = .Resetting := by
    dsimp [C']
    rw [congrArg AgentState.role hsnd]
    change (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).2.role = .Resetting
    rw [htr]
  have hv_rc : (C' v).1.resetcount = Rmax := by
    dsimp [C']
    rw [congrArg AgentState.resetcount hsnd]
    change (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).2.resetcount = Rmax
    rw [htr]
  have hv_leader : (C' v).1.leader = .L := by
    dsimp [C']
    rw [congrArg AgentState.leader hsnd]
    change (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).2.leader = .L
    rw [htr]
  refine ⟨hμ_role, hμ_rc, hμ_leader, hv_role, hv_rc, hv_leader, ?_⟩
  intro y hy_reset
  by_cases hyμ : y = μ
  · subst y
    exact ⟨hμ_rc, hμ_leader⟩
  · by_cases hyv : y = v
    · subst y
      exact ⟨hv_rc, hv_leader⟩
    · have hy_old : C' y = C y := by
        dsimp [C', P]
        simp [Config.step, hμv, hyμ, hyv]
      have hy_settled : (C' y).1.role = .Settled := by
        rw [hy_old]
        exact hC.allSettled y
      rw [hy_settled] at hy_reset
      cases hy_reset

theorem no_reset_even_lower_max_timer_one_trace
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    (hn4 : 4 ≤ n)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hpar : n % 2 = 0)
    (hμ_lower : (C μ).1.rank.val + 1 = n / 2)
    (hv_max : (C v).1.rank.val + 1 = n)
    (h_timer : (C μ).1.timer = 1)
    (h_no_swap : ¬((C μ).1.rank < (C v).1.rank ∧
      (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A))
    (h_post_same : (C μ).1.answer = (C v).1.answer) :
    transitionPEM n trank Rmax rankDelta (C μ, C v) =
      ({ (C μ).1 with timer := 0 }, (C v).1) := by
  have hμ_settled : (C μ).1.role = .Settled := hC.allSettled μ
  have hv_settled : (C v).1.role = .Settled := hC.allSettled v
  have h_rank_ne : (C μ).1.rank ≠ (C v).1.rank := by
    intro hEq
    exact hμv (hC.ranks_inj hEq)
  have hRD : rankDelta ((C μ).1, (C v).1) = ((C μ).1, (C v).1) :=
    hRank (C μ).1 (C v).1 hμ_settled hv_settled h_rank_ne
  have hceil : ceilHalf n = n / 2 := by
    unfold ceilHalf
    omega
  have hμ_ceil : (C μ).1.rank.val + 1 = ceilHalf n := by
    rw [hceil]
    exact hμ_lower
  have hv_not_ceil : (C v).1.rank.val + 1 ≠ ceilHalf n := by
    rw [hceil]
    omega
  have hv_not_upper : (C v).1.rank.val + 1 ≠ n / 2 + 1 := by
    omega
  have h_dec1a :
      ¬ ((C μ).1.rank.val + 1 = n / 2 ∧ (C v).1.rank.val = n / 2) := by
    intro h
    exact hv_not_upper (by omega)
  have h_dec2a :
      ¬ ((C v).1.rank.val + 1 = n / 2 ∧ (C μ).1.rank.val = n / 2) := by
    intro h
    omega
  have h_no_reset :
      ¬ (0 = 0 ∧ { (C μ).1 with timer := 0 }.answer ≠ (C v).1.answer) := by
    rintro ⟨_, hneq⟩
    exact hneq h_post_same
  have hswap :
      phase4_swap (C μ).1 (C v).1 (C μ).2 (C v).2 = ((C μ).1, (C v).1) := by
    unfold phase4_swap
    simp [h_no_swap]
  have hdec :
      phase4_decide n (C μ).1 (C v).1 (C μ).2 (C v).2 = ((C μ).1, (C v).1) := by
    unfold phase4_decide
    simp [hpar, h_dec1a, h_dec2a]
  have hprop :
      phase4_propagate n Rmax (C μ).1 (C v).1 =
        ({ (C μ).1 with timer := 0 }, (C v).1) := by
    unfold phase4_propagate
    simp [hμ_ceil, hv_max, h_timer]
    intro hneq
    exact (hneq h_post_same).elim
  unfold transitionPEM transitionPEM_prePhase4 transitionPEM_phase4
  simp [hRD, hμ_settled, hv_settled, role_settled_ne_resetting,
    hswap, hdec, hprop]

theorem no_reset_even_lower_max_timer_one_step_state
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    (hn4 : 4 ≤ n)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hpar : n % 2 = 0)
    (hμ_lower : (C μ).1.rank.val + 1 = n / 2)
    (hv_max : (C v).1.rank.val + 1 = n)
    (h_timer : (C μ).1.timer = 1)
    (h_no_swap : ¬((C μ).1.rank < (C v).1.rank ∧
      (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A))
    (h_post_same : (C μ).1.answer = (C v).1.answer) :
    let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := C.step P μ v
    C' μ = ({ (C μ).1 with timer := 0 }, (C μ).2) ∧
    C' v = C v ∧
    ∀ w : Fin n, w ≠ μ → w ≠ v → C' w = C w := by
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  let C' : Config (AgentState n) Opinion n := C.step P μ v
  have htr :=
    no_reset_even_lower_max_timer_one_trace
      (trank := Rmax) (Rmax := Rmax)
      (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
      (hRank := rankDeltaOSSR_satisfies_fix)
      (C := C) hC hn4 hμv hpar hμ_lower hv_max h_timer h_no_swap h_post_same
  refine ⟨?_, ?_, ?_⟩
  · dsimp [C']
    unfold Config.step
    simp [P, hμv]
    change
      (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).1 =
        { (C μ).1 with timer := 0 }
    rw [htr]
  · dsimp [C']
    unfold Config.step
    simp [P, hμv, hμv.symm]
    change
      ((transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).2,
        (C v).2) =
      C v
    rw [htr]
  · intro w hwμ hwv
    dsimp [C', P]
    simp [Config.step, hμv, hwμ, hwv]

theorem no_reset_even_lower_max_timer_one_step_InSrank
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    (hn4 : 4 ≤ n)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hpar : n % 2 = 0)
    (hμ_lower : (C μ).1.rank.val + 1 = n / 2)
    (hv_max : (C v).1.rank.val + 1 = n)
    (h_timer : (C μ).1.timer = 1)
    (h_no_swap : ¬((C μ).1.rank < (C v).1.rank ∧
      (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A))
    (h_post_same : (C μ).1.answer = (C v).1.answer) :
    let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := C.step P μ v
    InSrank C' ∧
      (C' μ).1.timer = 0 ∧
      (C' μ).1.answer = (C μ).1.answer ∧
      (C' μ).1.rank.val + 1 = n / 2 := by
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  let C' : Config (AgentState n) Opinion n := C.step P μ v
  have htr :=
    no_reset_even_lower_max_timer_one_trace
      (trank := Rmax) (Rmax := Rmax)
      (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
      (hRank := rankDeltaOSSR_satisfies_fix)
      (C := C) hC hn4 hμv hpar hμ_lower hv_max h_timer h_no_swap h_post_same
  have hfst := Config.step_fst_state P C hμv
  have hsnd := Config.step_snd_state P C hμv hμv.symm
  have hothers : ∀ w : Fin n, w ≠ μ → w ≠ v → C' w = C w := by
    intro w hwμ hwv
    dsimp [C', P]
    simp [Config.step, hμv, hwμ, hwv]
  have hμ_state : (C' μ).1 = { (C μ).1 with timer := 0 } := by
    dsimp [C']
    rw [hfst]
    change (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).1 =
      { (C μ).1 with timer := 0 }
    rw [htr]
  have hv_state : (C' v).1 = (C v).1 := by
    dsimp [C']
    rw [hsnd]
    change (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).2 =
      (C v).1
    rw [htr]
  have hrole : ∀ w : Fin n, (C' w).1.role = .Settled := by
    intro w
    by_cases hwμ : w = μ
    · subst w
      rw [hμ_state]
      exact hC.allSettled μ
    · by_cases hwv : w = v
      · subst w
        rw [hv_state]
        exact hC.allSettled v
      · rw [show (C' w).1 = (C w).1 from congrArg Prod.fst (hothers w hwμ hwv)]
        exact hC.allSettled w
  have hrank : ∀ w : Fin n, (C' w).1.rank = (C w).1.rank := by
    intro w
    by_cases hwμ : w = μ
    · subst w
      rw [hμ_state]
    · by_cases hwv : w = v
      · subst w
        rw [hv_state]
      · rw [show (C' w).1 = (C w).1 from congrArg Prod.fst (hothers w hwμ hwv)]
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨hrole, ?_⟩
    intro w₁ w₂ heq
    have heqC' : (C' w₁).1.rank = (C' w₂).1.rank := by
      simpa [C'] using heq
    exact hC.ranks_inj (by simpa [hrank w₁, hrank w₂] using heqC')
  · rw [hμ_state]
  · rw [hμ_state]
  · rw [hμ_state]
    exact hμ_lower

theorem no_reset_even_lower_max_timer_one_step_InSswap
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {C : Config (AgentState n) Opinion n} (hSwap : InSswap C)
    (hn4 : 4 ≤ n)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hpar : n % 2 = 0)
    (hμ_lower : (C μ).1.rank.val + 1 = n / 2)
    (hv_max : (C v).1.rank.val + 1 = n)
    (h_timer : (C μ).1.timer = 1)
    (h_no_swap : ¬((C μ).1.rank < (C v).1.rank ∧
      (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A))
    (h_post_same : (C μ).1.answer = (C v).1.answer) :
    let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := C.step P μ v
    InSswap C' ∧
      (C' μ).1.timer = 0 ∧
      (C' μ).1.answer = (C μ).1.answer ∧
      (C' μ).1.rank.val + 1 = n / 2 := by
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  let C' : Config (AgentState n) Opinion n := C.step P μ v
  obtain ⟨hμ_state, hv_state, hothers⟩ :=
    no_reset_even_lower_max_timer_one_step_state
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hSwap.toInSrank hn4 hμv hpar hμ_lower hv_max h_timer h_no_swap h_post_same
  have hμ_state' : C' μ = ({ (C μ).1 with timer := 0 }, (C μ).2) := by
    simpa [C', P] using hμ_state
  have hv_state' : C' v = C v := by
    simpa [C', P] using hv_state
  have hothers' : ∀ w : Fin n, w ≠ μ → w ≠ v → C' w = C w := by
    intro w hwμ hwv
    simpa [C', P] using hothers w hwμ hwv
  have hrole : ∀ w : Fin n, (C' w).1.role = .Settled := by
    intro w
    by_cases hwμ : w = μ
    · subst w
      rw [hμ_state']
      exact hSwap.allSettled μ
    · by_cases hwv : w = v
      · subst w
        rw [hv_state']
        exact hSwap.allSettled v
      · rw [hothers' w hwμ hwv]
        exact hSwap.allSettled w
  have hrank : ∀ w : Fin n, (C' w).1.rank = (C w).1.rank := by
    intro w
    by_cases hwμ : w = μ
    · subst w
      rw [hμ_state']
    · by_cases hwv : w = v
      · subst w
        rw [hv_state']
      · rw [hothers' w hwμ hwv]
  have hinput : ∀ w : Fin n, (C' w).2 = (C w).2 := by
    intro w
    by_cases hwμ : w = μ
    · subst w
      rw [hμ_state']
    · by_cases hwv : w = v
      · subst w
        rw [hv_state']
      · rw [hothers' w hwμ hwv]
  have hnA : nAOf C' = nAOf C := by
    simpa [C', P] using
      (nAOf_step_eq
        (trank := Rmax) (Rmax := Rmax)
        (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn) C μ v)
  change
    InSswap C' ∧
      (C' μ).1.timer = 0 ∧
      (C' μ).1.answer = (C μ).1.answer ∧
      (C' μ).1.rank.val + 1 = n / 2
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine { allSettled := ?_, ranks_inj := ?_, input_rank := ?_ }
    · intro w
      exact hrole w
    · intro w₁ w₂ heq
      apply hSwap.ranks_inj
      simpa [hrank w₁, hrank w₂] using heq
    · intro w
      rw [hinput w, hrank w, hnA]
      exact hSwap.input_rank w
  · rw [hμ_state']
  · rw [hμ_state']
  · rw [hμ_state']
    exact hμ_lower

theorem propagation_reset_fires_even_lower_timer_one_max_no_swap_trace
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    (hn4 : 4 ≤ n)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hpar : n % 2 = 0)
    (hμ_lower : (C μ).1.rank.val + 1 = n / 2)
    (hv_max : (C v).1.rank.val + 1 = n)
    (h_timer : (C μ).1.timer = 1)
    (h_no_swap : ¬((C μ).1.rank < (C v).1.rank ∧
      (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A))
    (h_post_diff : (C μ).1.answer ≠ (C v).1.answer) :
    transitionPEM n trank Rmax rankDelta (C μ, C v) =
      ({ (C μ).1 with timer := 0, role := .Resetting, leader := .L, resetcount := Rmax },
       { (C v).1 with role := .Resetting, leader := .L, resetcount := Rmax, answer := ((C μ).1).answer }) := by
  have hμ_settled : (C μ).1.role = .Settled := hC.allSettled μ
  have hv_settled : (C v).1.role = .Settled := hC.allSettled v
  have h_rank_ne : (C μ).1.rank ≠ (C v).1.rank := by
    intro hEq
    exact hμv (hC.ranks_inj hEq)
  have hRD : rankDelta ((C μ).1, (C v).1) = ((C μ).1, (C v).1) :=
    hRank (C μ).1 (C v).1 hμ_settled hv_settled h_rank_ne
  have hceil : ceilHalf n = n / 2 := by
    unfold ceilHalf
    omega
  have hμ_ceil : (C μ).1.rank.val + 1 = ceilHalf n := by
    rw [hceil]
    exact hμ_lower
  have hv_not_ceil : (C v).1.rank.val + 1 ≠ ceilHalf n := by
    rw [hceil]
    omega
  have hv_not_upper : (C v).1.rank.val + 1 ≠ n / 2 + 1 := by
    omega
  have h_dec1a :
      ¬ ((C μ).1.rank.val + 1 = n / 2 ∧ (C v).1.rank.val = n / 2) := by
    intro h
    exact hv_not_upper (by omega)
  have h_dec2a :
      ¬ ((C v).1.rank.val + 1 = n / 2 ∧ (C μ).1.rank.val = n / 2) := by
    intro h
    omega
  have hswap :
      phase4_swap (C μ).1 (C v).1 (C μ).2 (C v).2 = ((C μ).1, (C v).1) := by
    unfold phase4_swap
    simp [h_no_swap]
  have hdec :
      phase4_decide n (C μ).1 (C v).1 (C μ).2 (C v).2 = ((C μ).1, (C v).1) := by
    unfold phase4_decide
    simp [hpar, h_dec1a, h_dec2a]
  have hprop :
      phase4_propagate n Rmax (C μ).1 (C v).1 =
        ({ (C μ).1 with timer := 0, role := .Resetting, leader := .L, resetcount := Rmax },
         { (C v).1 with role := .Resetting, leader := .L, resetcount := Rmax, answer := ((C μ).1).answer }) := by
    unfold phase4_propagate
    simp [hμ_ceil, hv_not_ceil, hv_max, h_timer, h_post_diff]
  unfold transitionPEM transitionPEM_prePhase4 transitionPEM_phase4
  simp [hRD, hμ_settled, hv_settled, role_settled_ne_resetting,
    hswap, hdec, hprop]

theorem trigger_reset_from_InSrank_even_lower_timer_one_max_no_swap_with_snapshot
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    (hn4 : 4 ≤ n)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hpar : n % 2 = 0)
    (hμ_lower : (C μ).1.rank.val + 1 = n / 2)
    (hv_max : (C v).1.rank.val + 1 = n)
    (h_timer : (C μ).1.timer = 1)
    (h_no_swap : ¬((C μ).1.rank < (C v).1.rank ∧
      (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A))
    (h_post_diff : (C μ).1.answer ≠ (C v).1.answer) :
    let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := C.step P μ v
    (C' μ).1.role = .Resetting ∧ (C' μ).1.resetcount = Rmax ∧
      (C' μ).1.leader = .L ∧
    (C' v).1.role = .Resetting ∧ (C' v).1.resetcount = Rmax ∧
      (C' v).1.leader = .L ∧
    ∀ y : Fin n, (C' y).1.role = .Resetting →
      (C' y).1.resetcount = Rmax ∧ (C' y).1.leader = .L := by
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  let C' : Config (AgentState n) Opinion n := C.step P μ v
  have htr :=
    propagation_reset_fires_even_lower_timer_one_max_no_swap_trace
      (trank := Rmax) (Rmax := Rmax)
      (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
      (hRank := rankDeltaOSSR_satisfies_fix)
      (C := C) hC hn4 hμv hpar hμ_lower hv_max h_timer h_no_swap h_post_diff
  have hfst := Config.step_fst_state P C hμv
  have hsnd := Config.step_snd_state P C hμv hμv.symm
  have hμ_role : (C' μ).1.role = .Resetting := by
    dsimp [C']
    rw [congrArg AgentState.role hfst]
    change (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).1.role = .Resetting
    rw [htr]
  have hμ_rc : (C' μ).1.resetcount = Rmax := by
    dsimp [C']
    rw [congrArg AgentState.resetcount hfst]
    change (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).1.resetcount = Rmax
    rw [htr]
  have hμ_leader : (C' μ).1.leader = .L := by
    dsimp [C']
    rw [congrArg AgentState.leader hfst]
    change (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).1.leader = .L
    rw [htr]
  have hv_role : (C' v).1.role = .Resetting := by
    dsimp [C']
    rw [congrArg AgentState.role hsnd]
    change (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).2.role = .Resetting
    rw [htr]
  have hv_rc : (C' v).1.resetcount = Rmax := by
    dsimp [C']
    rw [congrArg AgentState.resetcount hsnd]
    change (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).2.resetcount = Rmax
    rw [htr]
  have hv_leader : (C' v).1.leader = .L := by
    dsimp [C']
    rw [congrArg AgentState.leader hsnd]
    change (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).2.leader = .L
    rw [htr]
  refine ⟨hμ_role, hμ_rc, hμ_leader, hv_role, hv_rc, hv_leader, ?_⟩
  intro y hy_reset
  by_cases hyμ : y = μ
  · subst y
    exact ⟨hμ_rc, hμ_leader⟩
  · by_cases hyv : y = v
    · subst y
      exact ⟨hv_rc, hv_leader⟩
    · have hy_old : C' y = C y := by
        dsimp [C', P]
        simp [Config.step, hμv, hyμ, hyv]
      have hy_settled : (C' y).1.role = .Settled := by
        rw [hy_old]
        exact hC.allSettled y
      rw [hy_settled] at hy_reset
      cases hy_reset

set_option maxHeartbeats 8000000 in
theorem propagation_reset_fires_swap_timer_zero_trace
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (hv_no_med : (C v).1.rank.val + 1 ≠ ceilHalf n)
    (h_timer : (C μ).1.timer = 0)
    (h_swap : (C μ).1.rank < (C v).1.rank ∧ (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A)
    (hpar : ¬ n % 2 = 0)
    (h_post_diff : opinionToAnswer (C v).2 ≠ (C v).1.answer) :
    transitionPEM n trank Rmax rankDelta (C μ, C v) =
      ({ (C v).1 with role := .Resetting, leader := .L, resetcount := Rmax, answer := opinionToAnswer ((C v).2) },
       { (C μ).1 with role := .Resetting, leader := .L, resetcount := Rmax, answer := opinionToAnswer ((C v).2), timer := 0 }) := by
  have hμ_settled : (C μ).1.role = .Settled := hC.allSettled μ
  have hv_settled : (C v).1.role = .Settled := hC.allSettled v
  have h_rank_ne : (C μ).1.rank ≠ (C v).1.rank := by
    intro hEq
    exact hμv (hC.ranks_inj hEq)
  have hRD : rankDelta ((C μ).1, (C v).1) = ((C μ).1, (C v).1) :=
    hRank (C μ).1 (C v).1 hμ_settled hv_settled h_rank_ne
  have h_reset_cond :
      ((C μ).1.timer = 0 ∧ ¬ (opinionToAnswer (C v).2 = (C v).1.answer)) := by
    refine ⟨h_timer, ?_⟩
    intro h_eq
    exact h_post_diff h_eq
  have hv_op : (C v).2 = Opinion.A := h_swap.2.2
  have h_post_diff_A : Answer.outA ≠ (C v).1.answer := by
    simpa [hv_op, opinionToAnswer] using h_post_diff
  unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4
    phase4_swap phase4_decide phase4_propagate
  simp only [hRD, hμ_settled, hv_settled, ne_eq,
    role_settled_ne_resetting, not_true_eq_false, not_false_eq_true,
    false_and, and_false, if_false, and_self, if_true, h_swap, hpar,
    hv_no_med, hμ_med, h_timer]
  by_cases hv_max : (C v).1.rank.val + 1 = n
  · simp [hv_max, h_timer, h_reset_cond, h_post_diff_A]
  · simp [hv_max, h_timer, h_reset_cond, h_post_diff_A]

theorem trigger_reset_from_InSrank_timer_zero_swap_with_snapshot
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (hv_no_med : (C v).1.rank.val + 1 ≠ ceilHalf n)
    (h_timer : (C μ).1.timer = 0)
    (h_swap : (C μ).1.rank < (C v).1.rank ∧ (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A)
    (hpar : ¬ n % 2 = 0)
    (h_post_diff : opinionToAnswer (C v).2 ≠ (C v).1.answer) :
    let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := C.step P μ v
    (C' μ).1.role = .Resetting ∧ (C' μ).1.resetcount = Rmax ∧
      (C' μ).1.leader = .L ∧
    (C' v).1.role = .Resetting ∧ (C' v).1.resetcount = Rmax ∧
      (C' v).1.leader = .L ∧
    ∀ y : Fin n, (C' y).1.role = .Resetting →
      (C' y).1.resetcount = Rmax ∧ (C' y).1.leader = .L := by
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  let C' : Config (AgentState n) Opinion n := C.step P μ v
  have htr :=
    propagation_reset_fires_swap_timer_zero_trace
      (trank := Rmax) (Rmax := Rmax)
      (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
      (hRank := rankDeltaOSSR_satisfies_fix)
      (C := C) hC hμv hμ_med hv_no_med h_timer h_swap hpar h_post_diff
  have hfst := Config.step_fst_state P C hμv
  have hsnd := Config.step_snd_state P C hμv hμv.symm
  have hμ_role : (C' μ).1.role = .Resetting := by
    dsimp [C']
    rw [congrArg AgentState.role hfst]
    change (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).1.role = .Resetting
    rw [htr]
  have hμ_rc : (C' μ).1.resetcount = Rmax := by
    dsimp [C']
    rw [congrArg AgentState.resetcount hfst]
    change (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).1.resetcount = Rmax
    rw [htr]
  have hμ_leader : (C' μ).1.leader = .L := by
    dsimp [C']
    rw [congrArg AgentState.leader hfst]
    change (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).1.leader = .L
    rw [htr]
  have hv_role : (C' v).1.role = .Resetting := by
    dsimp [C']
    rw [congrArg AgentState.role hsnd]
    change (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).2.role = .Resetting
    rw [htr]
  have hv_rc : (C' v).1.resetcount = Rmax := by
    dsimp [C']
    rw [congrArg AgentState.resetcount hsnd]
    change (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).2.resetcount = Rmax
    rw [htr]
  have hv_leader : (C' v).1.leader = .L := by
    dsimp [C']
    rw [congrArg AgentState.leader hsnd]
    change (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).2.leader = .L
    rw [htr]
  refine ⟨hμ_role, hμ_rc, hμ_leader, hv_role, hv_rc, hv_leader, ?_⟩
  intro y hy_reset
  by_cases hyμ : y = μ
  · subst y
    exact ⟨hμ_rc, hμ_leader⟩
  · by_cases hyv : y = v
    · subst y
      exact ⟨hv_rc, hv_leader⟩
    · have hy_old : C' y = C y := by
        dsimp [C', P]
        simp [Config.step, hμv, hyμ, hyv]
      have hy_settled : (C' y).1.role = .Settled := by
        rw [hy_old]
        exact hC.allSettled y
      rw [hy_settled] at hy_reset
      cases hy_reset

set_option maxHeartbeats 4000000 in
theorem propagation_reset_fires_no_swap_max_timer_one_trace
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    (hn4 : 4 ≤ n)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (hv_max : (C v).1.rank.val + 1 = n)
    (h_timer : (C μ).1.timer = 1)
    (h_no_swap : ¬((C μ).1.rank < (C v).1.rank ∧ (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A))
    (hpar : ¬ n % 2 = 0)
    (h_post_diff : opinionToAnswer (C μ).2 ≠ (C v).1.answer) :
    transitionPEM n trank Rmax rankDelta (C μ, C v) =
      ({ (C μ).1 with role := .Resetting, leader := .L, resetcount := Rmax, answer := opinionToAnswer ((C μ).2), timer := 0 },
       { (C v).1 with role := .Resetting, leader := .L, resetcount := Rmax, answer := opinionToAnswer ((C μ).2) }) := by
  have hμ_settled : (C μ).1.role = .Settled := hC.allSettled μ
  have hv_settled : (C v).1.role = .Settled := hC.allSettled v
  have h_rank_ne : (C μ).1.rank ≠ (C v).1.rank := by
    intro hEq
    exact hμv (hC.ranks_inj hEq)
  have hRD : rankDelta ((C μ).1, (C v).1) = ((C μ).1, (C v).1) :=
    hRank (C μ).1 (C v).1 hμ_settled hv_settled h_rank_ne
  have hv_no_med : (C v).1.rank.val + 1 ≠ ceilHalf n := by
    unfold ceilHalf at hμ_med ⊢
    omega
  have hN_ne_ceil : ¬ (n = ceilHalf n) := by
    unfold ceilHalf
    omega
  have h_reset_cond :
      ((C μ).1.timer - 1 = 0 ∧ ¬ (opinionToAnswer (C μ).2 = (C v).1.answer)) := by
    refine ⟨by rw [h_timer], ?_⟩
    intro h_eq
    exact h_post_diff h_eq
  unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4
    phase4_swap phase4_decide phase4_propagate
  simp only [hRD, hμ_settled, hv_settled, ne_eq,
    role_settled_ne_resetting, not_true_eq_false, not_false_eq_true,
    false_and, and_false, if_false, and_self, if_true, h_no_swap, hpar,
    hμ_med, hv_no_med, hv_max, hN_ne_ceil, h_timer]
  simpa [h_timer] using h_reset_cond

theorem trigger_reset_from_InSrank_timer_one_max_no_swap_with_snapshot
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    (hn4 : 4 ≤ n)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (hv_max : (C v).1.rank.val + 1 = n)
    (h_timer : (C μ).1.timer = 1)
    (h_no_swap : ¬((C μ).1.rank < (C v).1.rank ∧ (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A))
    (hpar : ¬ n % 2 = 0)
    (h_post_diff : opinionToAnswer (C μ).2 ≠ (C v).1.answer) :
    let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := C.step P μ v
    (C' μ).1.role = .Resetting ∧ (C' μ).1.resetcount = Rmax ∧
      (C' μ).1.leader = .L ∧
    (C' v).1.role = .Resetting ∧ (C' v).1.resetcount = Rmax ∧
      (C' v).1.leader = .L ∧
    ∀ y : Fin n, (C' y).1.role = .Resetting →
      (C' y).1.resetcount = Rmax ∧ (C' y).1.leader = .L := by
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  let C' : Config (AgentState n) Opinion n := C.step P μ v
  have htr :=
    propagation_reset_fires_no_swap_max_timer_one_trace
      (trank := Rmax) (Rmax := Rmax)
      (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
      (hRank := rankDeltaOSSR_satisfies_fix)
      (C := C) hC hn4 hμv hμ_med hv_max h_timer h_no_swap hpar h_post_diff
  have hfst := Config.step_fst_state P C hμv
  have hsnd := Config.step_snd_state P C hμv hμv.symm
  have hμ_role : (C' μ).1.role = .Resetting := by
    dsimp [C']
    rw [congrArg AgentState.role hfst]
    change (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).1.role = .Resetting
    rw [htr]
  have hμ_rc : (C' μ).1.resetcount = Rmax := by
    dsimp [C']
    rw [congrArg AgentState.resetcount hfst]
    change (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).1.resetcount = Rmax
    rw [htr]
  have hμ_leader : (C' μ).1.leader = .L := by
    dsimp [C']
    rw [congrArg AgentState.leader hfst]
    change (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).1.leader = .L
    rw [htr]
  have hv_role : (C' v).1.role = .Resetting := by
    dsimp [C']
    rw [congrArg AgentState.role hsnd]
    change (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).2.role = .Resetting
    rw [htr]
  have hv_rc : (C' v).1.resetcount = Rmax := by
    dsimp [C']
    rw [congrArg AgentState.resetcount hsnd]
    change (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).2.resetcount = Rmax
    rw [htr]
  have hv_leader : (C' v).1.leader = .L := by
    dsimp [C']
    rw [congrArg AgentState.leader hsnd]
    change (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).2.leader = .L
    rw [htr]
  refine ⟨hμ_role, hμ_rc, hμ_leader, hv_role, hv_rc, hv_leader, ?_⟩
  intro y hy_reset
  by_cases hyμ : y = μ
  · subst y
    exact ⟨hμ_rc, hμ_leader⟩
  · by_cases hyv : y = v
    · subst y
      exact ⟨hv_rc, hv_leader⟩
    · have hy_old : C' y = C y := by
        dsimp [C', P]
        simp [Config.step, hμv, hyμ, hyv]
      have hy_settled : (C' y).1.role = .Settled := by
        rw [hy_old]
        exact hC.allSettled y
      rw [hy_settled] at hy_reset
      cases hy_reset

set_option maxHeartbeats 8000000 in
theorem propagation_reset_fires_swap_max_timer_one_trace
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    (hn4 : 4 ≤ n)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (hv_max : (C v).1.rank.val + 1 = n)
    (h_timer : (C μ).1.timer = 1)
    (h_swap : (C μ).1.rank < (C v).1.rank ∧ (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A)
    (hpar : ¬ n % 2 = 0)
    (h_post_diff : opinionToAnswer (C v).2 ≠ (C v).1.answer) :
    transitionPEM n trank Rmax rankDelta (C μ, C v) =
      ({ (C v).1 with role := .Resetting, leader := .L, resetcount := Rmax, answer := opinionToAnswer ((C v).2) },
       { (C μ).1 with role := .Resetting, leader := .L, resetcount := Rmax, answer := opinionToAnswer ((C v).2), timer := 0 }) := by
  have hμ_settled : (C μ).1.role = .Settled := hC.allSettled μ
  have hv_settled : (C v).1.role = .Settled := hC.allSettled v
  have h_rank_ne : (C μ).1.rank ≠ (C v).1.rank := by
    intro hEq
    exact hμv (hC.ranks_inj hEq)
  have hRD : rankDelta ((C μ).1, (C v).1) = ((C μ).1, (C v).1) :=
    hRank (C μ).1 (C v).1 hμ_settled hv_settled h_rank_ne
  have hv_no_med : (C v).1.rank.val + 1 ≠ ceilHalf n := by
    unfold ceilHalf at hμ_med ⊢
    omega
  have hN_ne_ceil : ¬ (n = ceilHalf n) := by
    unfold ceilHalf
    omega
  have h_reset_cond :
      ((C μ).1.timer - 1 = 0 ∧ ¬ (opinionToAnswer (C v).2 = (C v).1.answer)) := by
    refine ⟨by rw [h_timer], ?_⟩
    intro h_eq
    exact h_post_diff h_eq
  have hv_op : (C v).2 = Opinion.A := h_swap.2.2
  have h_post_diff_A : Answer.outA ≠ (C v).1.answer := by
    simpa [hv_op, opinionToAnswer] using h_post_diff
  unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4
    phase4_swap phase4_decide phase4_propagate
  simp only [hRD, hμ_settled, hv_settled, ne_eq,
    role_settled_ne_resetting, not_true_eq_false, not_false_eq_true,
    false_and, and_false, if_false, and_self, if_true, h_swap, hpar,
    hμ_med, hv_no_med, hv_max, hN_ne_ceil, h_timer]
  simp [h_timer, h_reset_cond, h_post_diff_A]

theorem trigger_reset_from_InSrank_timer_one_max_swap_with_snapshot
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    (hn4 : 4 ≤ n)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (hv_max : (C v).1.rank.val + 1 = n)
    (h_timer : (C μ).1.timer = 1)
    (h_swap : (C μ).1.rank < (C v).1.rank ∧ (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A)
    (hpar : ¬ n % 2 = 0)
    (h_post_diff : opinionToAnswer (C v).2 ≠ (C v).1.answer) :
    let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := C.step P μ v
    (C' μ).1.role = .Resetting ∧ (C' μ).1.resetcount = Rmax ∧
      (C' μ).1.leader = .L ∧
    (C' v).1.role = .Resetting ∧ (C' v).1.resetcount = Rmax ∧
      (C' v).1.leader = .L ∧
    ∀ y : Fin n, (C' y).1.role = .Resetting →
      (C' y).1.resetcount = Rmax ∧ (C' y).1.leader = .L := by
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  let C' : Config (AgentState n) Opinion n := C.step P μ v
  have htr :=
    propagation_reset_fires_swap_max_timer_one_trace
      (trank := Rmax) (Rmax := Rmax)
      (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
      (hRank := rankDeltaOSSR_satisfies_fix)
      (C := C) hC hn4 hμv hμ_med hv_max h_timer h_swap hpar h_post_diff
  have hfst := Config.step_fst_state P C hμv
  have hsnd := Config.step_snd_state P C hμv hμv.symm
  have hμ_role : (C' μ).1.role = .Resetting := by
    dsimp [C']
    rw [congrArg AgentState.role hfst]
    change (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).1.role = .Resetting
    rw [htr]
  have hμ_rc : (C' μ).1.resetcount = Rmax := by
    dsimp [C']
    rw [congrArg AgentState.resetcount hfst]
    change (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).1.resetcount = Rmax
    rw [htr]
  have hμ_leader : (C' μ).1.leader = .L := by
    dsimp [C']
    rw [congrArg AgentState.leader hfst]
    change (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).1.leader = .L
    rw [htr]
  have hv_role : (C' v).1.role = .Resetting := by
    dsimp [C']
    rw [congrArg AgentState.role hsnd]
    change (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).2.role = .Resetting
    rw [htr]
  have hv_rc : (C' v).1.resetcount = Rmax := by
    dsimp [C']
    rw [congrArg AgentState.resetcount hsnd]
    change (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).2.resetcount = Rmax
    rw [htr]
  have hv_leader : (C' v).1.leader = .L := by
    dsimp [C']
    rw [congrArg AgentState.leader hsnd]
    change (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).2.leader = .L
    rw [htr]
  refine ⟨hμ_role, hμ_rc, hμ_leader, hv_role, hv_rc, hv_leader, ?_⟩
  intro y hy_reset
  by_cases hyμ : y = μ
  · subst y
    exact ⟨hμ_rc, hμ_leader⟩
  · by_cases hyv : y = v
    · subst y
      exact ⟨hv_rc, hv_leader⟩
    · have hy_old : C' y = C y := by
        dsimp [C', P]
        simp [Config.step, hμv, hyμ, hyv]
      have hy_settled : (C' y).1.role = .Settled := by
        rw [hy_old]
        exact hC.allSettled y
      rw [hy_settled] at hy_reset
      cases hy_reset

set_option maxHeartbeats 4000000 in
theorem no_reset_no_swap_max_timer_one_trace
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    (hn4 : 4 ≤ n)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (hv_max : (C v).1.rank.val + 1 = n)
    (h_timer : (C μ).1.timer = 1)
    (h_no_swap : ¬((C μ).1.rank < (C v).1.rank ∧ (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A))
    (hpar : ¬ n % 2 = 0)
    (h_post_same : opinionToAnswer (C μ).2 = (C v).1.answer) :
    transitionPEM n trank Rmax rankDelta (C μ, C v) =
      ({ (C μ).1 with answer := opinionToAnswer ((C μ).2), timer := 0 },
       (C v).1) := by
  have hμ_settled : (C μ).1.role = .Settled := hC.allSettled μ
  have hv_settled : (C v).1.role = .Settled := hC.allSettled v
  have h_rank_ne : (C μ).1.rank ≠ (C v).1.rank := by
    intro hEq
    exact hμv (hC.ranks_inj hEq)
  have hRD : rankDelta ((C μ).1, (C v).1) = ((C μ).1, (C v).1) :=
    hRank (C μ).1 (C v).1 hμ_settled hv_settled h_rank_ne
  have hv_no_med : (C v).1.rank.val + 1 ≠ ceilHalf n := by
    unfold ceilHalf at hμ_med ⊢
    omega
  have hN_ne_ceil : ¬ (n = ceilHalf n) := by
    unfold ceilHalf
    omega
  have h_no_reset :
      ¬((C μ).1.timer - 1 = 0 ∧
        { (C μ).1 with answer := opinionToAnswer (C μ).2 }.answer ≠ (C v).1.answer) := by
    rintro ⟨_, hneq⟩
    exact hneq h_post_same
  unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4
    phase4_swap phase4_decide phase4_propagate
  simp only [hRD, hμ_settled, hv_settled, ne_eq,
    role_settled_ne_resetting, not_true_eq_false, not_false_eq_true,
    false_and, and_false, if_false, and_self, if_true, h_no_swap, hpar,
    hμ_med, hv_no_med, hv_max, hN_ne_ceil, h_timer]
  simp [h_timer, h_no_reset, h_post_same]

theorem no_reset_no_swap_max_timer_one_step_InSrank
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    (hn4 : 4 ≤ n)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (hv_max : (C v).1.rank.val + 1 = n)
    (h_timer : (C μ).1.timer = 1)
    (h_no_swap : ¬((C μ).1.rank < (C v).1.rank ∧ (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A))
    (hpar : ¬ n % 2 = 0)
    (h_post_same : opinionToAnswer (C μ).2 = (C v).1.answer) :
    let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := C.step P μ v
    InSrank C' ∧
      (C' μ).1.timer = 0 ∧
      (C' μ).1.answer = opinionToAnswer (C μ).2 ∧
      (C' μ).1.rank.val + 1 = ceilHalf n := by
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  let C' : Config (AgentState n) Opinion n := C.step P μ v
  have htr :=
    no_reset_no_swap_max_timer_one_trace
      (trank := Rmax) (Rmax := Rmax)
      (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
      (hRank := rankDeltaOSSR_satisfies_fix)
      (C := C) hC hn4 hμv hμ_med hv_max h_timer h_no_swap hpar h_post_same
  have hfst := Config.step_fst_state P C hμv
  have hsnd := Config.step_snd_state P C hμv hμv.symm
  have hothers : ∀ w : Fin n, w ≠ μ → w ≠ v → C' w = C w := by
    intro w hwμ hwv
    dsimp [C', P]
    simp [Config.step, hμv, hwμ, hwv]
  have hμ_state : (C' μ).1 = { (C μ).1 with answer := opinionToAnswer (C μ).2, timer := 0 } := by
    dsimp [C']
    rw [hfst]
    change (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).1 =
      { (C μ).1 with answer := opinionToAnswer (C μ).2, timer := 0 }
    rw [htr]
  have hv_state : (C' v).1 = (C v).1 := by
    dsimp [C']
    rw [hsnd]
    change (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).2 =
      (C v).1
    rw [htr]
  have hrole : ∀ w : Fin n, (C' w).1.role = .Settled := by
    intro w
    by_cases hwμ : w = μ
    · subst w
      rw [hμ_state]
      exact hC.allSettled μ
    · by_cases hwv : w = v
      · subst w
        rw [hv_state]
        exact hC.allSettled v
      · rw [show (C' w).1 = (C w).1 from congrArg Prod.fst (hothers w hwμ hwv)]
        exact hC.allSettled w
  have hrank : ∀ w : Fin n, (C' w).1.rank = (C w).1.rank := by
    intro w
    by_cases hwμ : w = μ
    · subst w
      rw [hμ_state]
    · by_cases hwv : w = v
      · subst w
        rw [hv_state]
      · rw [show (C' w).1 = (C w).1 from congrArg Prod.fst (hothers w hwμ hwv)]
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨hrole, ?_⟩
    intro w₁ w₂ heq
    have heqC' : (C' w₁).1.rank = (C' w₂).1.rank := by
      simpa [C'] using heq
    exact hC.ranks_inj (by simpa [hrank w₁, hrank w₂] using heqC')
  · rw [hμ_state]
  · rw [hμ_state]
  · rw [hμ_state]
    exact hμ_med

set_option maxHeartbeats 8000000 in
theorem no_reset_swap_max_timer_one_trace
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    (hn4 : 4 ≤ n)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (hv_max : (C v).1.rank.val + 1 = n)
    (h_timer : (C μ).1.timer = 1)
    (h_swap : (C μ).1.rank < (C v).1.rank ∧ (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A)
    (hpar : ¬ n % 2 = 0)
    (h_post_same : opinionToAnswer (C v).2 = (C v).1.answer) :
    transitionPEM n trank Rmax rankDelta (C μ, C v) =
      ((C v).1,
       { (C μ).1 with answer := opinionToAnswer ((C v).2), timer := 0 }) := by
  have hμ_settled : (C μ).1.role = .Settled := hC.allSettled μ
  have hv_settled : (C v).1.role = .Settled := hC.allSettled v
  have h_rank_ne : (C μ).1.rank ≠ (C v).1.rank := by
    intro hEq
    exact hμv (hC.ranks_inj hEq)
  have hRD : rankDelta ((C μ).1, (C v).1) = ((C μ).1, (C v).1) :=
    hRank (C μ).1 (C v).1 hμ_settled hv_settled h_rank_ne
  have hv_no_med : (C v).1.rank.val + 1 ≠ ceilHalf n := by
    unfold ceilHalf at hμ_med ⊢
    omega
  have hN_ne_ceil : ¬ (n = ceilHalf n) := by
    unfold ceilHalf
    omega
  have h_no_reset :
      ¬((C μ).1.timer - 1 = 0 ∧
        { (C μ).1 with answer := opinionToAnswer (C v).2 }.answer ≠ (C v).1.answer) := by
    rintro ⟨_, hneq⟩
    exact hneq h_post_same
  unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4
    phase4_swap phase4_decide phase4_propagate
  simp only [hRD, hμ_settled, hv_settled, ne_eq,
    role_settled_ne_resetting, not_true_eq_false, not_false_eq_true,
    false_and, and_false, if_false, and_self, if_true, h_swap, hpar,
    hμ_med, hv_no_med, hv_max, hN_ne_ceil, h_timer]
  split_ifs with hreset <;> simp_all

theorem no_reset_swap_max_timer_one_step_InSrank
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    (hn4 : 4 ≤ n)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (hv_max : (C v).1.rank.val + 1 = n)
    (h_timer : (C μ).1.timer = 1)
    (h_swap : (C μ).1.rank < (C v).1.rank ∧ (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A)
    (hpar : ¬ n % 2 = 0)
    (h_post_same : opinionToAnswer (C v).2 = (C v).1.answer) :
    let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := C.step P μ v
    InSrank C' ∧
      (C' v).1.timer = 0 ∧
      (C' v).1.answer = opinionToAnswer (C v).2 ∧
      (C' v).1.rank.val + 1 = ceilHalf n := by
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  let C' : Config (AgentState n) Opinion n := C.step P μ v
  have htr :=
    no_reset_swap_max_timer_one_trace
      (trank := Rmax) (Rmax := Rmax)
      (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
      (hRank := rankDeltaOSSR_satisfies_fix)
      (C := C) hC hn4 hμv hμ_med hv_max h_timer h_swap hpar h_post_same
  have hfst := Config.step_fst_state P C hμv
  have hsnd := Config.step_snd_state P C hμv hμv.symm
  have hvμ : v ≠ μ := hμv.symm
  have hothers : ∀ w : Fin n, w ≠ μ → w ≠ v → C' w = C w := by
    intro w hwμ hwv
    dsimp [C', P]
    simp [Config.step, hμv, hwμ, hwv]
  have hμ_state : (C' μ).1 = (C v).1 := by
    dsimp [C']
    rw [hfst]
    change (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).1 =
      (C v).1
    rw [htr]
  have hv_state : (C' v).1 = { (C μ).1 with answer := opinionToAnswer (C v).2, timer := 0 } := by
    dsimp [C']
    rw [hsnd]
    change (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).2 =
      { (C μ).1 with answer := opinionToAnswer (C v).2, timer := 0 }
    rw [htr]
  have hrole : ∀ w : Fin n, (C' w).1.role = .Settled := by
    intro w
    by_cases hwμ : w = μ
    · subst w
      rw [hμ_state]
      exact hC.allSettled v
    · by_cases hwv : w = v
      · subst w
        rw [hv_state]
        exact hC.allSettled μ
      · rw [show (C' w).1 = (C w).1 from congrArg Prod.fst (hothers w hwμ hwv)]
        exact hC.allSettled w
  have hrank : ∀ w : Fin n,
      (C' w).1.rank =
        if w = μ then (C v).1.rank else if w = v then (C μ).1.rank else (C w).1.rank := by
    intro w
    by_cases hwμ : w = μ
    · subst w
      rw [hμ_state]
      simp
    · by_cases hwv : w = v
      · subst w
        rw [hv_state]
        simp [hvμ]
      · rw [show (C' w).1 = (C w).1 from congrArg Prod.fst (hothers w hwμ hwv)]
        simp [hwμ, hwv]
  have hinj : Function.Injective (fun w : Fin n => (C' w).1.rank) := by
    intro w₁ w₂ heq
    by_cases h1μ : w₁ = μ
    · subst w₁
      by_cases h2μ : w₂ = μ
      · exact h2μ.symm
      · by_cases h2v : w₂ = v
        · subst w₂
          have heq_old : (C v).1.rank = (C μ).1.rank := by
            simpa [hrank, hvμ] using heq
          exact False.elim (hμv (hC.ranks_inj heq_old).symm)
        · have heq_old : (C v).1.rank = (C w₂).1.rank := by
            simpa [hrank, h2μ, h2v] using heq
          exact False.elim (h2v (hC.ranks_inj heq_old).symm)
    · by_cases h1v : w₁ = v
      · subst w₁
        by_cases h2μ : w₂ = μ
        · subst w₂
          have heq_old : (C μ).1.rank = (C v).1.rank := by
            simpa [hrank, hvμ] using heq
          exact False.elim (hμv (hC.ranks_inj heq_old))
        · by_cases h2v : w₂ = v
          · exact h2v.symm
          · have heq_old : (C μ).1.rank = (C w₂).1.rank := by
              simpa [hrank, h1μ, h2μ, h2v] using heq
            exact False.elim (h2μ (hC.ranks_inj heq_old).symm)
      · by_cases h2μ : w₂ = μ
        · subst w₂
          have heq_old : (C w₁).1.rank = (C v).1.rank := by
            simpa [hrank, h1μ, h1v] using heq
          exact False.elim (h1v (hC.ranks_inj heq_old))
        · by_cases h2v : w₂ = v
          · subst w₂
            have heq_old : (C w₁).1.rank = (C μ).1.rank := by
              simpa [hrank, h1μ, h1v, h2μ] using heq
            exact False.elim (h1μ (hC.ranks_inj heq_old))
          · exact hC.ranks_inj (by simpa [hrank, h1μ, h1v, h2μ, h2v] using heq)
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ⟨hrole, hinj⟩
  · rw [hv_state]
  · rw [hv_state]
  · rw [hv_state]
    exact hμ_med

/-! ### PROPAGATE-RESET: Resetting agent recruits non-Resetting -/

set_option maxHeartbeats 16000000 in
/-- Phase 1 of propagateReset: recruitment of non-Resetting agent.
After Phase 1: b becomes `{ t with role:=Resetting, rc:=0, dt:=Dmax }`, oldRcB = 0.
Phase 2 sync sets b.rc := max(s.rc - 1, 0) = s.rc - 1 (≥ 0).
Phase 3 calls `processAgent Emax Dmax hn b_post 0 true`:
  * if `s.rc - 1 ≠ 0`: `processAgent_rc_ne_zero` → identity, role stays Resetting;
  * if `s.rc - 1 = 0` (i.e. `s.rc = 1`): rc=0 case with oldRc=0, partnerResetting=true,
    and dt = Dmax > 1, so `processAgent_oldRc_zero_partner_true_delay_gt_one_stays` applies. -/
theorem propagateReset_recruits
    {Emax Dmax : ℕ} {hn : 0 < n}
    {s t : AgentState n}
    (hs_res : s.role = .Resetting)
    (hs_rc : 0 < s.resetcount)
    (ht_not_res : t.role ≠ .Resetting)
    (hDmax : 1 < Dmax) :
    (propagateReset Emax Dmax hn s t).2.role = .Resetting := by
  unfold propagateReset processAgent
  by_cases hrc : s.resetcount = 1
  · simp [hs_res, hs_rc, ht_not_res, hrc, resetOSSR, show (Dmax : ℕ) ≠ 0 from by omega,
      show Dmax - 1 ≠ 0 from by omega]
  · have hne : s.resetcount - 1 ≠ 0 := by omega
    simp [hs_res, hs_rc, ht_not_res, hne, resetOSSR, show (Dmax : ℕ) ≠ 0 from by omega]

/-- PROPAGATE-RESET spreader trace: the Resetting recruiter stays Resetting and
its resetcount decrements while the non-Resetting partner is recruited. -/
theorem propagateReset_spreader_trace
    {Emax Dmax : ℕ} {hn : 0 < n}
    {s t : AgentState n}
    (hs_res : s.role = .Resetting)
    (hs_rc : 0 < s.resetcount)
    (ht_not_res : t.role ≠ .Resetting)
    (hDmax : 1 < Dmax) :
    (propagateReset Emax Dmax hn s t).1.role = .Resetting ∧
    (propagateReset Emax Dmax hn s t).1.resetcount = s.resetcount - 1 := by
  unfold propagateReset processAgent
  by_cases hrc : s.resetcount = 1
  · simp [hs_res, hs_rc, ht_not_res, hrc, resetOSSR,
      show (Dmax : ℕ) ≠ 0 from by omega]
  · have hne : s.resetcount - 1 ≠ 0 := by omega
    simp [hs_res, hs_rc, ht_not_res, hne, resetOSSR,
      show (Dmax : ℕ) ≠ 0 from by omega]

/-- The Resetting recruiter keeps its leader field while recruiting a
non-Resetting partner. -/
theorem propagateReset_spreader_leader
    {Emax Dmax : ℕ} {hn : 0 < n}
    {s t : AgentState n}
    (hs_res : s.role = .Resetting)
    (hs_rc : 0 < s.resetcount)
    (ht_not_res : t.role ≠ .Resetting)
    (hDmax : 1 < Dmax) :
    (propagateReset Emax Dmax hn s t).1.leader = s.leader := by
  unfold propagateReset processAgent
  by_cases hrc : s.resetcount = 1
  · simp [hs_res, hs_rc, ht_not_res, hrc, resetOSSR,
      show (Dmax : ℕ) ≠ 0 from by omega]
  · have hne : s.resetcount - 1 ≠ 0 := by omega
    simp [hs_res, hs_rc, ht_not_res, hne, resetOSSR,
      show (Dmax : ℕ) ≠ 0 from by omega]

/-- PROPAGATE-RESET: Resetting (resetcount > 0) recruits non-Resetting. -/
theorem rankDeltaOSSR_propagate_reset
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {s t : AgentState n}
    (hs_res : s.role = .Resetting)
    (hs_rc : 0 < s.resetcount)
    (ht_not_res : t.role ≠ .Resetting)
    (hDmax : 1 < Dmax) :
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.role = .Resetting := by
  unfold rankDeltaOSSR
  simp only [hs_res, true_or, ite_true]
  -- propagateReset is called, then leader dedup. Leader dedup doesn't change role.
  have h_pr := propagateReset_recruits (Emax := Emax) (hn := hn)
    hs_res hs_rc ht_not_res hDmax
  split_ifs <;> exact h_pr

/-- RankDelta trace for the spreader side of PROPAGATE-RESET. -/
theorem rankDeltaOSSR_propagate_reset_spreader
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {s t : AgentState n}
    (hs_res : s.role = .Resetting)
    (hs_rc : 0 < s.resetcount)
    (ht_not_res : t.role ≠ .Resetting)
    (hDmax : 1 < Dmax) :
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.role = .Resetting ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.resetcount = s.resetcount - 1 := by
  unfold rankDeltaOSSR
  simp only [hs_res, true_or, ite_true]
  exact propagateReset_spreader_trace (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hs_res hs_rc ht_not_res hDmax

theorem rankDeltaOSSR_propagate_reset_spreader_leader
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {s t : AgentState n}
    (hs_res : s.role = .Resetting)
    (hs_rc : 0 < s.resetcount)
    (ht_not_res : t.role ≠ .Resetting)
    (hDmax : 1 < Dmax) :
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.leader = s.leader := by
  unfold rankDeltaOSSR
  simp only [hs_res, true_or, ite_true]
  exact propagateReset_spreader_leader (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hs_res hs_rc ht_not_res hDmax

/-! ### Awakening config: all Resetting, one leader -/

/-- A dormant configuration: all agents Resetting with resetcount = 0,
unique leader. This is the stable region reached after Phase 2 (sync/dedup). -/
def IsDormantConfig (C : Config (AgentState n) Opinion n) : Prop :=
  (∀ w : Fin n, (C w).1.role = .Resetting) ∧
  (∀ w : Fin n, (C w).1.resetcount = 0) ∧
  (∃! ℓ : Fin n, (C ℓ).1.leader = .L) ∧
  (∀ w : Fin n, (C w).1.leader = .L ∨ (C w).1.leader = .F)

def IsAwakeningConfig (C : Config (AgentState n) Opinion n) : Prop :=
  (∃! ℓ : Fin n, (C ℓ).1.leader = .L) ∧
  (∀ ℓ : Fin n, (C ℓ).1.leader = .L →
    (C ℓ).1.role = .Settled ∧ (C ℓ).1.rank.val = 0 ∧ (C ℓ).1.children = 0) ∧
  (∀ w : Fin n, (C w).1.leader = .F →
    (C w).1.role = .Unsettled ∨ ((C w).1.role = .Resetting ∧ (C w).1.resetcount = 0))

/-- RESET for a leader produces Settled at rank 0. -/
theorem resetOSSR_leader {Emax : ℕ} {hn : 0 < n}
    {s : AgentState n} (h_leader : s.leader = .L) :
    (resetOSSR Emax hn s).role = .Settled ∧
    (resetOSSR Emax hn s).rank = ⟨0, hn⟩ ∧
    (resetOSSR Emax hn s).children = 0 := by
  unfold resetOSSR; rw [h_leader]; exact ⟨rfl, rfl, rfl⟩

/-- RESET for a follower produces Unsettled with errorcount = Emax. -/
theorem resetOSSR_follower {Emax : ℕ} {hn : 0 < n}
    {s : AgentState n} (h_follower : s.leader = .F) :
    (resetOSSR Emax hn s).role = .Unsettled ∧
    (resetOSSR Emax hn s).errorcount = Emax := by
  unfold resetOSSR; rw [h_follower]; exact ⟨rfl, rfl⟩

/-! ### List-based schedule execution

Following ChatGPT's suggestion: prove reachability via finite lists
of interactions, then convert to ℕ → Fin n × Fin n at the end.
This is much simpler than working with scheduler functions directly. -/

/-- Execute a finite list of interactions. -/
def runPairs {Q X Y : Type*} (P : Protocol Q X Y) (C : Config Q X n)
    (L : List (Fin n × Fin n)) : Config Q X n :=
  L.foldl (fun C ij => C.step P ij.1 ij.2) C

@[simp] theorem runPairs_nil {Q X Y : Type*} (P : Protocol Q X Y) (C : Config Q X n) :
    runPairs P C [] = C := rfl

@[simp] theorem runPairs_cons {Q X Y : Type*} (P : Protocol Q X Y) (C : Config Q X n)
    (ij : Fin n × Fin n) (L : List (Fin n × Fin n)) :
    runPairs P C (ij :: L) = runPairs P (C.step P ij.1 ij.2) L := rfl

theorem runPairs_append {Q X Y : Type*} (P : Protocol Q X Y) (C : Config Q X n)
    (L₁ L₂ : List (Fin n × Fin n)) :
    runPairs P C (L₁ ++ L₂) = runPairs P (runPairs P C L₁) L₂ := by
  simp [runPairs, List.foldl_append]

/-- Convert a list schedule to a function schedule. -/
def schedOfList [Inhabited (Fin n × Fin n)] (L : List (Fin n × Fin n)) :
    DetScheduler n :=
  fun t => L.getD t default

/-- Bridge: runPairs via list = execution via scheduler.
Proved by induction on the list, using execution_concat. -/
theorem exists_schedule_of_runPairs [Inhabited (Fin n × Fin n)]
    {Q X Y : Type*} (P : Protocol Q X Y)
    (C₀ : Config Q X n) (L : List (Fin n × Fin n))
    {Goal : Config Q X n → Prop}
    (h : Goal (runPairs P C₀ L)) :
    ∃ (γ : DetScheduler n) (t : ℕ), Goal (execution P C₀ γ t) := by
  induction L generalizing C₀ with
  | nil => exact ⟨fun _ => default, 0, h⟩
  | cons ij L ih =>
    have h' := ih (C₀.step P ij.1 ij.2) h
    obtain ⟨γ', t', hGoal⟩ := h'
    exact ⟨concatScheduler (fun _ => ij) 1 γ', 1 + t',
      by rw [execution_concat]; exact hGoal⟩

/-! ### Phase 1a: Collision detection (same-rank Settled → Resetting)

When all agents are Settled but ranks are not injective (not InSrank),
there exist two distinct agents with the same rank. Scheduling them
triggers collision detection → both become Resetting. -/

/-- If all Settled but ranks not injective, ∃ two with same rank. -/
theorem exists_collision_of_not_inj
    {C : Config (AgentState n) Opinion n}
    (hSettled : ∀ v : Fin n, (C v).1.role = .Settled)
    (hNotInj : ¬ Function.Injective (fun v : Fin n => (C v).1.rank)) :
    ∃ u v : Fin n, u ≠ v ∧ (C u).1.rank = (C v).1.rank := by
  by_contra h
  push_neg at h
  apply hNotInj
  intro a b hab
  by_contra hne
  exact hne (h a b hne hab).elim

/-- Collision detection: two Settled agents with the same rank both
become Resetting via rankDeltaOSSR Part 2. -/
theorem rankDeltaOSSR_collision
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {s t : AgentState n}
    (hs : s.role = .Settled) (ht : t.role = .Settled)
    (h_same : s.rank = t.rank) :
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.role = .Resetting ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.role = .Resetting ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.resetcount = Rmax ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.resetcount = Rmax := by
  unfold rankDeltaOSSR
  have h_not_res : ¬(s.role = .Resetting ∨ t.role = .Resetting) := by
    rw [hs, ht]; simp
  simp only [h_not_res, ite_false, hs, ht, h_same, and_self, ite_true]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-! ### Collision through transitionPEM: both → Resetting -/

set_option maxHeartbeats 16000000 in
/-- After collision in rankDeltaOSSR (both Settled, same rank → both
Resetting), transitionPEM preserves the Resetting role. Phase 2 clears
answer but keeps role. Phase 4 requires both Settled which is false. -/
theorem transitionPEM_collision_both_resetting
    {trank Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {C : Config (AgentState n) Opinion n}
    {u v : Fin n}
    (hsu : (C u).1.role = .Settled) (hsv : (C v).1.role = .Settled)
    (h_same : (C u).1.rank = (C v).1.rank) :
    (transitionPEM n trank Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C u, C v)).1.role = .Resetting ∧
    (transitionPEM n trank Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C u, C v)).2.role = .Resetting ∧
    (transitionPEM n trank Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C u, C v)).1.resetcount = Rmax ∧
    (transitionPEM n trank Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C u, C v)).2.resetcount = Rmax := by
  unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4 phase4_swap phase4_decide phase4_propagate rankDeltaOSSR
  simp [hsu, hsv, h_same]

theorem transitionPEM_collision_both_resetting_leader
    {trank Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {C : Config (AgentState n) Opinion n}
    {u v : Fin n}
    (hsu : (C u).1.role = .Settled) (hsv : (C v).1.role = .Settled)
    (h_same : (C u).1.rank = (C v).1.rank) :
    (transitionPEM n trank Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C u, C v)).1.leader = .L ∧
    (transitionPEM n trank Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C u, C v)).2.leader = .L := by
  unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4 phase4_swap phase4_decide phase4_propagate rankDeltaOSSR
  simp [hsu, hsv, h_same]

/-! ### Phase 1a: Trigger reset from all-Settled non-InSrank

When all agents are Settled but InSrank fails (ranks not injective),
schedule one collision pair → both become Resetting. -/

theorem trigger_reset_from_all_settled_non_InSrank
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {C₀ : Config (AgentState n) Opinion n}
    (hSettled : ∀ v : Fin n, (C₀ v).1.role = .Settled)
    (hNotInSrank : ¬ InSrank C₀) :
    ∃ u v : Fin n, u ≠ v ∧
      let C' := C₀.step (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) u v
      (C' u).1.role = .Resetting ∧ (C' v).1.role = .Resetting ∧
      (C' u).1.resetcount = Rmax ∧ (C' v).1.resetcount = Rmax := by
  have hNotInj : ¬ Function.Injective (fun v : Fin n => (C₀ v).1.rank) := by
    intro hInj
    exact hNotInSrank ⟨hSettled, hInj⟩
  obtain ⟨u, v, huv, h_same⟩ := exists_collision_of_not_inj hSettled hNotInj
  refine ⟨u, v, huv, ?_⟩
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have h_tr := transitionPEM_collision_both_resetting (trank := Rmax) (Rmax := Rmax)
    (Emax := Emax) (Dmax := Dmax) (hn := hn) (C := C₀) (u := u) (v := v)
    (hSettled u) (hSettled v) h_same
  have h_fst := Config.step_fst_state P C₀ huv
  have h_snd := Config.step_snd_state P C₀ huv huv.symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [congrArg AgentState.role h_fst]
    change (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C₀ u, C₀ v)).1.role = .Resetting
    exact h_tr.1
  · rw [congrArg AgentState.role h_snd]
    change (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C₀ u, C₀ v)).2.role = .Resetting
    exact h_tr.2.1
  · rw [congrArg AgentState.resetcount h_fst]
    change (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C₀ u, C₀ v)).1.resetcount = Rmax
    exact h_tr.2.2.1
  · rw [congrArg AgentState.resetcount h_snd]
    change (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C₀ u, C₀ v)).2.resetcount = Rmax
    exact h_tr.2.2.2

theorem trigger_reset_from_all_settled_non_InSrank_with_leader
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {C₀ : Config (AgentState n) Opinion n}
    (hSettled : ∀ v : Fin n, (C₀ v).1.role = .Settled)
    (hNotInSrank : ¬ InSrank C₀) :
    ∃ u v : Fin n, u ≠ v ∧
      let C' := C₀.step (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) u v
      (C' u).1.role = .Resetting ∧ (C' u).1.resetcount = Rmax ∧
      (C' u).1.leader = .L ∧
      (C' v).1.role = .Resetting ∧ (C' v).1.resetcount = Rmax ∧
      (C' v).1.leader = .L := by
  have hNotInj : ¬ Function.Injective (fun v : Fin n => (C₀ v).1.rank) := by
    intro hInj
    exact hNotInSrank ⟨hSettled, hInj⟩
  obtain ⟨u, v, huv, h_same⟩ := exists_collision_of_not_inj hSettled hNotInj
  refine ⟨u, v, huv, ?_⟩
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have h_tr := transitionPEM_collision_both_resetting (trank := Rmax) (Rmax := Rmax)
    (Emax := Emax) (Dmax := Dmax) (hn := hn) (C := C₀) (u := u) (v := v)
    (hSettled u) (hSettled v) h_same
  have h_leader := transitionPEM_collision_both_resetting_leader (trank := Rmax) (Rmax := Rmax)
    (Emax := Emax) (Dmax := Dmax) (hn := hn) (C := C₀) (u := u) (v := v)
    (hSettled u) (hSettled v) h_same
  have h_fst := Config.step_fst_state P C₀ huv
  have h_snd := Config.step_snd_state P C₀ huv huv.symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [congrArg AgentState.role h_fst]
    change (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C₀ u, C₀ v)).1.role = .Resetting
    exact h_tr.1
  · rw [congrArg AgentState.resetcount h_fst]
    change (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C₀ u, C₀ v)).1.resetcount = Rmax
    exact h_tr.2.2.1
  · rw [congrArg AgentState.leader h_fst]
    change (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C₀ u, C₀ v)).1.leader = .L
    exact h_leader.1
  · rw [congrArg AgentState.role h_snd]
    change (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C₀ u, C₀ v)).2.role = .Resetting
    exact h_tr.2.1
  · rw [congrArg AgentState.resetcount h_snd]
    change (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C₀ u, C₀ v)).2.resetcount = Rmax
    exact h_tr.2.2.2
  · rw [congrArg AgentState.leader h_snd]
    change (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C₀ u, C₀ v)).2.leader = .L
    exact h_leader.2


/-! ### Unsettled branch induction (from ChatGPT)

Well-founded induction on unsettledMass = Σ (errorcount + 1). -/

def unsettledContribution (s : AgentState n) : ℕ :=
  if s.role == .Unsettled then s.errorcount + 1 else 0

def unsettledMass (C : Config (AgentState n) Opinion n) : ℕ :=
  ∑ w : Fin n, unsettledContribution (C w).1

/-- RankDelta-only progress when the first agent is Unsettled and the second is
not Resetting. This avoids unfolding the outer `transitionPEM` phases while
case-splitting the OSSR ranking protocol. -/
lemma rankDeltaOSSR_unsettled_no_resetting_progress
    {Rmax Emax Dmax : ℕ} {hn : 0 < n} {s t : AgentState n}
    (hs_uns : s.role = .Unsettled)
    (ht_not_res : t.role ≠ .Resetting) :
    let r := rankDeltaOSSR Rmax Emax Dmax hn (s, t)
    (r.1.role = .Resetting ∨ r.2.role = .Resetting) ∨
    (r.1.role ≠ .Resetting ∧
     r.2.role ≠ .Resetting ∧
     (if r.1.role == .Unsettled then r.1.errorcount + 1 else 0) <
       (if s.role == .Unsettled then s.errorcount + 1 else 0) ∧
     (if r.2.role == .Unsettled then r.2.errorcount + 1 else 0) ≤
       (if t.role == .Unsettled then t.errorcount + 1 else 0)) := by
  set_option maxHeartbeats 8000000 in
  unfold rankDeltaOSSR
  simp [hs_uns, ht_not_res]
  split_ifs <;> simp_all <;> omega

lemma rankDeltaOSSR_unsettled_no_resetting_resetcount
    {Rmax Emax Dmax : ℕ} {hn : 0 < n} {s t : AgentState n}
    (hs_uns : s.role = .Unsettled)
    (ht_not_res : t.role ≠ .Resetting) :
    let r := rankDeltaOSSR Rmax Emax Dmax hn (s, t)
    (r.1.role = .Resetting → r.1.resetcount = Rmax) ∧
    (r.2.role = .Resetting → r.2.resetcount = Rmax) := by
  unfold rankDeltaOSSR
  simp [hs_uns, ht_not_res]
  split_ifs <;> simp_all

lemma rankDeltaOSSR_unsettled_no_resetting_reset_leader
    {Rmax Emax Dmax : ℕ} {hn : 0 < n} {s t : AgentState n}
    (hs_uns : s.role = .Unsettled)
    (ht_not_res : t.role ≠ .Resetting) :
    let r := rankDeltaOSSR Rmax Emax Dmax hn (s, t)
    (r.1.role = .Resetting → r.1.leader = .L) ∧
    (r.2.role = .Resetting → r.2.leader = .L) := by
  unfold rankDeltaOSSR
  simp [hs_uns, ht_not_res]
  split_ifs <;> simp_all

lemma phase4_propagate_resetting_resetcount
    {Rmax : ℕ} {b₀ b₁ : AgentState n}
    (h₀ : b₀.role = .Settled) (h₁ : b₁.role = .Settled) :
    let r := phase4_propagate n Rmax b₀ b₁
    (r.1.role = .Resetting → r.1.resetcount = Rmax) ∧
    (r.2.role = .Resetting → r.2.resetcount = Rmax) := by
  unfold phase4_propagate
  repeat' split_ifs <;> simp [h₀, h₁]

lemma phase4_propagate_resetting_leader
    {Rmax : ℕ} {b₀ b₁ : AgentState n}
    (h₀ : b₀.role = .Settled) (h₁ : b₁.role = .Settled) :
    let r := phase4_propagate n Rmax b₀ b₁
    (r.1.role = .Resetting → r.1.leader = .L) ∧
    (r.2.role = .Resetting → r.2.leader = .L) := by
  unfold phase4_propagate
  repeat' split_ifs <;> simp [h₀, h₁]

lemma phase4_resetting_resetcount
    {Rmax : ℕ} {a : AgentState n × AgentState n} {x₀ x₁ : Opinion}
    (h₀ : a.1.role = .Settled) (h₁ : a.2.role = .Settled) :
    let r := transitionPEM_phase4 n Rmax a x₀ x₁
    (r.1.role = .Resetting → r.1.resetcount = Rmax) ∧
    (r.2.role = .Resetting → r.2.resetcount = Rmax) := by
  rcases a with ⟨a₀, a₁⟩
  dsimp at h₀ h₁
  let b := phase4_swap a₀ a₁ x₀ x₁
  let c := phase4_decide n b.1 b.2 x₀ x₁
  have hb : b.1.role = .Settled ∧ b.2.role = .Settled := by
    dsimp [b, phase4_swap]
    split_ifs <;> simp [h₀, h₁]
  have hc : c.1.role = .Settled ∧ c.2.role = .Settled := by
    dsimp [c, phase4_decide]
    split_ifs <;> simp [hb.1, hb.2]
  simpa [transitionPEM_phase4, h₀, h₁, b, c] using
    phase4_propagate_resetting_resetcount
      (n := n) (Rmax := Rmax) (b₀ := c.1) (b₁ := c.2) hc.1 hc.2

lemma phase4_resetting_leader
    {Rmax : ℕ} {a : AgentState n × AgentState n} {x₀ x₁ : Opinion}
    (h₀ : a.1.role = .Settled) (h₁ : a.2.role = .Settled) :
    let r := transitionPEM_phase4 n Rmax a x₀ x₁
    (r.1.role = .Resetting → r.1.leader = .L) ∧
    (r.2.role = .Resetting → r.2.leader = .L) := by
  rcases a with ⟨a₀, a₁⟩
  dsimp at h₀ h₁
  let b := phase4_swap a₀ a₁ x₀ x₁
  let c := phase4_decide n b.1 b.2 x₀ x₁
  have hb : b.1.role = .Settled ∧ b.2.role = .Settled := by
    dsimp [b, phase4_swap]
    split_ifs <;> simp [h₀, h₁]
  have hc : c.1.role = .Settled ∧ c.2.role = .Settled := by
    dsimp [c, phase4_decide]
    split_ifs <;> simp [hb.1, hb.2]
  simpa [transitionPEM_phase4, h₀, h₁, b, c] using
    phase4_propagate_resetting_leader
      (n := n) (Rmax := Rmax) (b₀ := c.1) (b₁ := c.2) hc.1 hc.2

lemma phase4_propagate_reset_both_of_not_both_settled
    {Rmax : ℕ} {b₀ b₁ : AgentState n}
    (h₀ : b₀.role = .Settled) (h₁ : b₁.role = .Settled)
    (hnot :
      ¬ ((phase4_propagate n Rmax b₀ b₁).1.role = .Settled ∧
         (phase4_propagate n Rmax b₀ b₁).2.role = .Settled)) :
    (phase4_propagate n Rmax b₀ b₁).1.role = .Resetting ∧
    (phase4_propagate n Rmax b₀ b₁).2.role = .Resetting := by
  by_cases hA : b₀.rank.val + 1 = ceilHalf n
  · let b₀' : AgentState n :=
      if b₁.rank.val + 1 = n then { b₀ with timer := b₀.timer - 1 } else b₀
    have hb₀' : b₀'.role = .Settled := by
      dsimp [b₀']
      split_ifs <;> simp [h₀]
    by_cases hR : b₀'.timer = 0 ∧ b₀'.answer ≠ b₁.answer
    · unfold phase4_propagate
      simp only [hA, if_true]
      change (if b₀'.timer = 0 ∧ b₀'.answer ≠ b₁.answer then
          ({ b₀' with role := .Resetting, leader := .L, resetcount := Rmax },
           { b₁ with answer := b₀'.answer, role := .Resetting, leader := .L, resetcount := Rmax })
        else (b₀', b₁)).1.role = .Resetting ∧
        (if b₀'.timer = 0 ∧ b₀'.answer ≠ b₁.answer then
          ({ b₀' with role := .Resetting, leader := .L, resetcount := Rmax },
           { b₁ with answer := b₀'.answer, role := .Resetting, leader := .L, resetcount := Rmax })
        else (b₀', b₁)).2.role = .Resetting
      rw [if_pos hR]
      exact ⟨rfl, rfl⟩
    · exfalso
      apply hnot
      unfold phase4_propagate
      simp only [hA, if_true]
      change (if b₀'.timer = 0 ∧ b₀'.answer ≠ b₁.answer then
          ({ b₀' with role := .Resetting, leader := .L, resetcount := Rmax },
           { b₁ with answer := b₀'.answer, role := .Resetting, leader := .L, resetcount := Rmax })
        else (b₀', b₁)).1.role = .Settled ∧
        (if b₀'.timer = 0 ∧ b₀'.answer ≠ b₁.answer then
          ({ b₀' with role := .Resetting, leader := .L, resetcount := Rmax },
           { b₁ with answer := b₀'.answer, role := .Resetting, leader := .L, resetcount := Rmax })
        else (b₀', b₁)).2.role = .Settled
      rw [if_neg hR]
      exact ⟨hb₀', h₁⟩
  · by_cases hB : b₁.rank.val + 1 = ceilHalf n
    · let b₁' : AgentState n :=
        if b₀.rank.val + 1 = n then { b₁ with timer := b₁.timer - 1 } else b₁
      have hb₁' : b₁'.role = .Settled := by
        dsimp [b₁']
        split_ifs <;> simp [h₁]
      by_cases hR : b₁'.timer = 0 ∧ b₁'.answer ≠ b₀.answer
      · unfold phase4_propagate
        simp only [hA, if_false, hB, if_true]
        change (if b₁'.timer = 0 ∧ b₁'.answer ≠ b₀.answer then
            ({ b₀ with answer := b₁'.answer, role := .Resetting, leader := .L, resetcount := Rmax },
             { b₁' with role := .Resetting, leader := .L, resetcount := Rmax })
          else (b₀, b₁')).1.role = .Resetting ∧
          (if b₁'.timer = 0 ∧ b₁'.answer ≠ b₀.answer then
            ({ b₀ with answer := b₁'.answer, role := .Resetting, leader := .L, resetcount := Rmax },
             { b₁' with role := .Resetting, leader := .L, resetcount := Rmax })
          else (b₀, b₁')).2.role = .Resetting
        rw [if_pos hR]
        exact ⟨rfl, rfl⟩
      · exfalso
        apply hnot
        unfold phase4_propagate
        simp only [hA, if_false, hB, if_true]
        change (if b₁'.timer = 0 ∧ b₁'.answer ≠ b₀.answer then
            ({ b₀ with answer := b₁'.answer, role := .Resetting, leader := .L, resetcount := Rmax },
             { b₁' with role := .Resetting, leader := .L, resetcount := Rmax })
          else (b₀, b₁')).1.role = .Settled ∧
          (if b₁'.timer = 0 ∧ b₁'.answer ≠ b₀.answer then
            ({ b₀ with answer := b₁'.answer, role := .Resetting, leader := .L, resetcount := Rmax },
             { b₁' with role := .Resetting, leader := .L, resetcount := Rmax })
          else (b₀, b₁')).2.role = .Settled
        rw [if_neg hR]
        exact ⟨h₀, hb₁'⟩
    · exfalso
      apply hnot
      unfold phase4_propagate
      simp [hA, hB, h₀, h₁]

lemma transitionPEM_phase4_reset_both_of_not_both_settled
    {Rmax : ℕ} {a : AgentState n × AgentState n} {x₀ x₁ : Opinion}
    (h₀ : a.1.role = .Settled) (h₁ : a.2.role = .Settled)
    (hnot :
      ¬ ((transitionPEM_phase4 n Rmax a x₀ x₁).1.role = .Settled ∧
         (transitionPEM_phase4 n Rmax a x₀ x₁).2.role = .Settled)) :
    (transitionPEM_phase4 n Rmax a x₀ x₁).1.role = .Resetting ∧
    (transitionPEM_phase4 n Rmax a x₀ x₁).2.role = .Resetting := by
  rcases a with ⟨a₀, a₁⟩
  dsimp at h₀ h₁
  let b := phase4_swap a₀ a₁ x₀ x₁
  let c := phase4_decide n b.1 b.2 x₀ x₁
  have hb : b.1.role = .Settled ∧ b.2.role = .Settled := by
    dsimp [b, phase4_swap]
    split_ifs <;> simp [h₀, h₁]
  have hc : c.1.role = .Settled ∧ c.2.role = .Settled := by
    dsimp [c, phase4_decide]
    split_ifs <;> simp [hb.1, hb.2]
  have hnot_prop :
      ¬ ((phase4_propagate n Rmax c.1 c.2).1.role = .Settled ∧
         (phase4_propagate n Rmax c.1 c.2).2.role = .Settled) := by
    intro hprop
    apply hnot
    simpa [transitionPEM_phase4, h₀, h₁, b, c] using hprop
  simpa [transitionPEM_phase4, h₀, h₁, b, c] using
    phase4_propagate_reset_both_of_not_both_settled
      (n := n) (Rmax := Rmax) (b₀ := c.1) (b₁ := c.2)
      hc.1 hc.2 hnot_prop

/-- Pre-Phase-4 preserves structural fields from the rankDelta output. -/
lemma transitionPEM_prePhase4_structural
    {trank : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    {s₀ s₁ : AgentState n} {x₀ x₁ : Opinion} :
    let p := transitionPEM_prePhase4 n trank rankDelta s₀ s₁ x₀ x₁
    let r := rankDelta (s₀, s₁)
    p.1.role = r.1.role ∧ p.1.leader = r.1.leader ∧ p.1.rank = r.1.rank ∧
    p.1.children = r.1.children ∧ p.1.resetcount = r.1.resetcount ∧
    p.1.delaytimer = r.1.delaytimer ∧
    p.2.role = r.2.role ∧ p.2.leader = r.2.leader ∧ p.2.rank = r.2.rank ∧
    p.2.children = r.2.children ∧ p.2.resetcount = r.2.resetcount ∧
    p.2.delaytimer = r.2.delaytimer ∧
    p.1.errorcount = r.1.errorcount ∧ p.2.errorcount = r.2.errorcount := by
  unfold transitionPEM_prePhase4
  generalize hr : rankDelta (s₀, s₁) = r
  rcases r with ⟨r₀, r₁⟩
  let a₀ : AgentState n :=
    if r₀.role = .Resetting ∧ s₀.role ≠ .Resetting then { r₀ with answer := .phi } else r₀
  let a₁ : AgentState n :=
    if r₁.role = .Resetting ∧ s₁.role ≠ .Resetting then { r₁ with answer := .phi } else r₁
  have ha₀ : a₀.role = r₀.role ∧ a₀.leader = r₀.leader ∧ a₀.rank = r₀.rank ∧
      a₀.children = r₀.children ∧ a₀.resetcount = r₀.resetcount ∧
      a₀.delaytimer = r₀.delaytimer ∧ a₀.errorcount = r₀.errorcount := by
    dsimp [a₀]
    split_ifs <;> simp
  have ha₁ : a₁.role = r₁.role ∧ a₁.leader = r₁.leader ∧ a₁.rank = r₁.rank ∧
      a₁.children = r₁.children ∧ a₁.resetcount = r₁.resetcount ∧
      a₁.delaytimer = r₁.delaytimer ∧ a₁.errorcount = r₁.errorcount := by
    dsimp [a₁]
    split_ifs <;> simp
  let b₀ : AgentState n :=
    if a₀.role = .Settled ∧ s₀.role ≠ .Settled ∧ a₀.rank.val + 1 = ceilHalf n then
      { a₀ with timer := 7 * (trank + 4) }
    else a₀
  let b₁ : AgentState n :=
    if a₁.role = .Settled ∧ s₁.role ≠ .Settled ∧ a₁.rank.val + 1 = ceilHalf n then
      { a₁ with timer := 7 * (trank + 4) }
    else a₁
  have hb₀ : b₀.role = r₀.role ∧ b₀.leader = r₀.leader ∧ b₀.rank = r₀.rank ∧
      b₀.children = r₀.children ∧ b₀.resetcount = r₀.resetcount ∧
      b₀.delaytimer = r₀.delaytimer ∧ b₀.errorcount = r₀.errorcount := by
    dsimp [b₀]
    split_ifs <;> simp [ha₀]
  have hb₁ : b₁.role = r₁.role ∧ b₁.leader = r₁.leader ∧ b₁.rank = r₁.rank ∧
      b₁.children = r₁.children ∧ b₁.resetcount = r₁.resetcount ∧
      b₁.delaytimer = r₁.delaytimer ∧ b₁.errorcount = r₁.errorcount := by
    dsimp [b₁]
    split_ifs <;> simp [ha₁]
  let c : AgentState n × AgentState n :=
    if b₀.role = .Resetting ∧ b₁.role = .Resetting then
      if b₀.answer = .phi ∧ b₁.answer ≠ .phi then
        ({ b₀ with answer := b₁.answer }, b₁)
      else if b₁.answer = .phi ∧ b₀.answer ≠ .phi then
        (b₀, { b₁ with answer := b₀.answer })
      else (b₀, b₁)
    else (b₀, b₁)
  have hc : c.1.role = r₀.role ∧ c.1.leader = r₀.leader ∧ c.1.rank = r₀.rank ∧
      c.1.children = r₀.children ∧ c.1.resetcount = r₀.resetcount ∧
      c.1.delaytimer = r₀.delaytimer ∧
      c.2.role = r₁.role ∧ c.2.leader = r₁.leader ∧ c.2.rank = r₁.rank ∧
      c.2.children = r₁.children ∧ c.2.resetcount = r₁.resetcount ∧
      c.2.delaytimer = r₁.delaytimer ∧
      c.1.errorcount = r₀.errorcount ∧ c.2.errorcount = r₁.errorcount := by
    dsimp [c]
    split_ifs <;> simp [hb₀, hb₁]
  change c.1.role = r₀.role ∧ c.1.leader = r₀.leader ∧ c.1.rank = r₀.rank ∧
    c.1.children = r₀.children ∧ c.1.resetcount = r₀.resetcount ∧
    c.1.delaytimer = r₀.delaytimer ∧
    c.2.role = r₁.role ∧ c.2.leader = r₁.leader ∧ c.2.rank = r₁.rank ∧
    c.2.children = r₁.children ∧ c.2.resetcount = r₁.resetcount ∧
    c.2.delaytimer = r₁.delaytimer ∧
    c.1.errorcount = r₀.errorcount ∧ c.2.errorcount = r₁.errorcount
  exact hc

set_option maxHeartbeats 8000000 in
/-- General passthrough: when rankDelta outputs are NOT both Settled,
transitionPEM preserves ALL structural fields (role, leader, rank,
children, resetcount, delaytimer, errorcount) from rankDelta output.
Only answer and timer may change (Phase 2/3). Phase 4 is skipped. -/
theorem transitionPEM_structural_passthrough
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    {s₀ s₁ : AgentState n} {x₀ x₁ : Opinion}
    (h : ¬((rankDelta (s₀, s₁)).1.role = .Settled ∧
            (rankDelta (s₀, s₁)).2.role = .Settled)) :
    let t := transitionPEM n trank Rmax rankDelta ((s₀, x₀), (s₁, x₁))
    let r := rankDelta (s₀, s₁)
    t.1.role = r.1.role ∧ t.1.leader = r.1.leader ∧ t.1.rank = r.1.rank ∧
    t.1.children = r.1.children ∧ t.1.resetcount = r.1.resetcount ∧
    t.1.delaytimer = r.1.delaytimer ∧
    t.2.role = r.2.role ∧ t.2.leader = r.2.leader ∧ t.2.rank = r.2.rank ∧
    t.2.children = r.2.children ∧ t.2.resetcount = r.2.resetcount ∧
    t.2.delaytimer = r.2.delaytimer ∧
    t.1.errorcount = r.1.errorcount ∧ t.2.errorcount = r.2.errorcount := by
  simp only [transitionPEM]
  have hpre := transitionPEM_prePhase4_structural
    (trank := trank) (rankDelta := rankDelta)
    (s₀ := s₀) (s₁ := s₁) (x₀ := x₀) (x₁ := x₁)
  have h_not_settled : ¬((transitionPEM_prePhase4 n trank rankDelta s₀ s₁ x₀ x₁).1.role = .Settled ∧
      (transitionPEM_prePhase4 n trank rankDelta s₀ s₁ x₀ x₁).2.role = .Settled) := by
    rw [hpre.1, hpre.2.2.2.2.2.2.1]; exact h
  rw [transitionPEM_phase4_of_not_both_settled h_not_settled]
  exact hpre

/-- Local progress trace for Algorithm 1 when the first interacting agent is
Unsettled and no Resetting agents are present before the interaction.

This packages the expensive `transitionPEM`/`rankDeltaOSSR` case analysis so
`unsettled_one_step_progress` does not repeatedly unfold the whole protocol
inside a `simp` call. -/
theorem transitionPEM_unsettled_one_step_progress
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (C : Config (AgentState n) Opinion n)
    {w v : Fin n}
    (hw_unsettled : (C w).1.role = .Unsettled)
    (hNoReset : ∀ x : Fin n, (C x).1.role ≠ .Resetting) :
    let r : AgentState n × AgentState n :=
      transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C w, C v)
    (r.1.role = .Resetting ∨ r.2.role = .Resetting) ∨
    (r.1.role ≠ .Resetting ∧
     r.2.role ≠ .Resetting ∧
     (if r.1.role == .Unsettled then r.1.errorcount + 1 else 0) <
       (if (C w).1.role == .Unsettled then (C w).1.errorcount + 1 else 0) ∧
     (if r.2.role == .Unsettled then r.2.errorcount + 1 else 0) ≤
       (if (C v).1.role == .Unsettled then (C v).1.errorcount + 1 else 0)) := by
  have hrd :=
    rankDeltaOSSR_unsettled_no_resetting_progress
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      (s := (C w).1) (t := (C v).1) hw_unsettled (hNoReset v)
  dsimp at hrd ⊢
  rcases hrd with hrd_reset | hrd_prog
  · have h_not_both :
        ¬((rankDeltaOSSR Rmax Emax Dmax hn ((C w).1, (C v).1)).1.role = .Settled ∧
          (rankDeltaOSSR Rmax Emax Dmax hn ((C w).1, (C v).1)).2.role = .Settled) := by
      intro hboth
      rcases hrd_reset with hreset | hreset
      · rw [hreset] at hboth
        exact Role.noConfusion hboth.1
      · rw [hreset] at hboth
        exact Role.noConfusion hboth.2
    have hpass := transitionPEM_structural_passthrough (trank := Rmax) (Rmax := Rmax)
      (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
      (s₀ := (C w).1) (s₁ := (C v).1) (x₀ := (C w).2) (x₁ := (C v).2)
      (h := h_not_both)
    rcases hpass with ⟨hrole₁, _, _, _, _, _, hrole₂, _, _, _, _, _, _, _⟩
    rcases hrd_reset with hreset | hreset
    · exact Or.inl (Or.inl (by rw [hrole₁]; exact hreset))
    · exact Or.inl (Or.inr (by rw [hrole₂]; exact hreset))
  · by_cases hboth :
        (rankDeltaOSSR Rmax Emax Dmax hn ((C w).1, (C v).1)).1.role = .Settled ∧
        (rankDeltaOSSR Rmax Emax Dmax hn ((C w).1, (C v).1)).2.role = .Settled
    · by_cases hreset :
          (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C w, C v)).1.role = .Resetting ∨
          (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C w, C v)).2.role = .Resetting
      · exact Or.inl hreset
      · push_neg at hreset
        have hpre_struct := transitionPEM_prePhase4_structural
          (trank := Rmax) (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
          (s₀ := (C w).1) (s₁ := (C v).1) (x₀ := (C w).2) (x₁ := (C v).2)
        have hpre₁ :
            (transitionPEM_prePhase4 n Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
              (C w).1 (C v).1 (C w).2 (C v).2).1.role = .Settled := by
          rw [hpre_struct.1]
          exact hboth.1
        have hpre₂ :
            (transitionPEM_prePhase4 n Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
              (C w).1 (C v).1 (C w).2 (C v).2).2.role = .Settled := by
          rw [hpre_struct.2.2.2.2.2.2.1]
          exact hboth.2
        have hnotU :=
          transitionPEM_phase4_not_unsettled_of_both_settled
            (n := n) (Rmax := Rmax)
            (a := transitionPEM_prePhase4 n Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
              (C w).1 (C v).1 (C w).2 (C v).2)
            (x₀ := (C w).2) (x₁ := (C v).2) hpre₁ hpre₂
        refine Or.inr ⟨hreset.1, hreset.2, ?_, ?_⟩
        · have hpos : 0 < (C w).1.errorcount + 1 := Nat.succ_pos _
          simpa [transitionPEM, hnotU.1, hw_unsettled] using hpos
        · simp [transitionPEM, hnotU.2]
    · have hpass := transitionPEM_structural_passthrough (trank := Rmax) (Rmax := Rmax)
        (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
        (s₀ := (C w).1) (s₁ := (C v).1) (x₀ := (C w).2) (x₁ := (C v).2)
        (h := hboth)
      rcases hpass with
        ⟨hrole₁, _, _, _, _, _, hrole₂, _, _, _, _, _, herr₁, herr₂⟩
      refine Or.inr ⟨?_, ?_, ?_, ?_⟩
      · rw [hrole₁]
        exact hrd_prog.1
      · rw [hrole₂]
        exact hrd_prog.2.1
      · simpa [hrole₁, hrole₂, herr₁, herr₂, hw_unsettled] using hrd_prog.2.2.1
      · simpa [hrole₁, hrole₂, herr₁, herr₂] using hrd_prog.2.2.2

theorem transitionPEM_unsettled_one_step_resetcount
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (C : Config (AgentState n) Opinion n)
    {w v : Fin n}
    (hw_unsettled : (C w).1.role = .Unsettled)
    (hNoReset : ∀ x : Fin n, (C x).1.role ≠ .Resetting) :
    let r : AgentState n × AgentState n :=
      transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C w, C v)
    (r.1.role = .Resetting → r.1.resetcount = Rmax) ∧
    (r.2.role = .Resetting → r.2.resetcount = Rmax) := by
  let rankDelta : AgentState n × AgentState n → AgentState n × AgentState n :=
    rankDeltaOSSR Rmax Emax Dmax hn
  let p :=
    transitionPEM_prePhase4 n Rmax rankDelta (C w).1 (C v).1 (C w).2 (C v).2
  have hrd_rc :=
    rankDeltaOSSR_unsettled_no_resetting_resetcount
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      (s := (C w).1) (t := (C v).1) hw_unsettled (hNoReset v)
  have hpre := transitionPEM_prePhase4_structural
    (trank := Rmax) (rankDelta := rankDelta)
    (s₀ := (C w).1) (s₁ := (C v).1) (x₀ := (C w).2) (x₁ := (C v).2)
  by_cases hboth :
      (rankDelta ((C w).1, (C v).1)).1.role = .Settled ∧
      (rankDelta ((C w).1, (C v).1)).2.role = .Settled
  · have hp₁ : p.1.role = .Settled := by
      simpa [p] using hpre.1.trans hboth.1
    have hp₂ : p.2.role = .Settled := by
      simpa [p] using hpre.2.2.2.2.2.2.1.trans hboth.2
    have hphase :=
      phase4_resetting_resetcount
        (n := n) (Rmax := Rmax) (a := p) (x₀ := (C w).2) (x₁ := (C v).2)
        hp₁ hp₂
    simpa [transitionPEM, rankDelta, p] using hphase
  · have hpass :=
      transitionPEM_structural_passthrough
        (n := n) (trank := Rmax) (Rmax := Rmax)
        (rankDelta := rankDelta)
        (s₀ := (C w).1) (s₁ := (C v).1) (x₀ := (C w).2) (x₁ := (C v).2)
        hboth
    dsimp [rankDelta] at hrd_rc
    rcases hpass with
      ⟨hrole₁, _, _, _, hrc₁, _, hrole₂, _, _, _, hrc₂, _, _, _⟩
    refine ⟨?_, ?_⟩
    · intro hreset
      rw [hrc₁]
      exact hrd_rc.1 (by
        rw [← hrole₁]
        exact hreset)
    · intro hreset
      rw [hrc₂]
      exact hrd_rc.2 (by
        rw [← hrole₂]
        exact hreset)

theorem transitionPEM_unsettled_one_step_reset_leader
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (C : Config (AgentState n) Opinion n)
    {w v : Fin n}
    (hw_unsettled : (C w).1.role = .Unsettled)
    (hNoReset : ∀ x : Fin n, (C x).1.role ≠ .Resetting) :
    let r : AgentState n × AgentState n :=
      transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C w, C v)
    (r.1.role = .Resetting → r.1.leader = .L) ∧
    (r.2.role = .Resetting → r.2.leader = .L) := by
  let rankDelta : AgentState n × AgentState n → AgentState n × AgentState n :=
    rankDeltaOSSR Rmax Emax Dmax hn
  let p :=
    transitionPEM_prePhase4 n Rmax rankDelta (C w).1 (C v).1 (C w).2 (C v).2
  have hrd_leader :=
    rankDeltaOSSR_unsettled_no_resetting_reset_leader
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      (s := (C w).1) (t := (C v).1) hw_unsettled (hNoReset v)
  have hpre := transitionPEM_prePhase4_structural
    (trank := Rmax) (rankDelta := rankDelta)
    (s₀ := (C w).1) (s₁ := (C v).1) (x₀ := (C w).2) (x₁ := (C v).2)
  by_cases hboth :
      (rankDelta ((C w).1, (C v).1)).1.role = .Settled ∧
      (rankDelta ((C w).1, (C v).1)).2.role = .Settled
  · have hp₁ : p.1.role = .Settled := by
      simpa [p] using hpre.1.trans hboth.1
    have hp₂ : p.2.role = .Settled := by
      simpa [p] using hpre.2.2.2.2.2.2.1.trans hboth.2
    have hphase :=
      phase4_resetting_leader
        (n := n) (Rmax := Rmax) (a := p) (x₀ := (C w).2) (x₁ := (C v).2)
        hp₁ hp₂
    simpa [transitionPEM, rankDelta, p] using hphase
  · have hpass :=
      transitionPEM_structural_passthrough
        (n := n) (trank := Rmax) (Rmax := Rmax)
        (rankDelta := rankDelta)
        (s₀ := (C w).1) (s₁ := (C v).1) (x₀ := (C w).2) (x₁ := (C v).2)
        hboth
    dsimp [rankDelta] at hrd_leader
    rcases hpass with
      ⟨hrole₁, hleader₁, _, _, _, _, hrole₂, hleader₂, _, _, _, _, _, _⟩
    refine ⟨?_, ?_⟩
    · intro hreset
      rw [hleader₁]
      exact hrd_leader.1 (by
        rw [← hrole₁]
        exact hreset)
    · intro hreset
      rw [hleader₂]
      exact hrd_leader.2 (by
        rw [← hrole₂]
        exact hreset)

theorem unsettled_one_step_progress
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (C : Config (AgentState n) Opinion n)
    {w v : Fin n} (hwv : v ≠ w)
    (hw_unsettled : (C w).1.role = .Unsettled)
    (hNoReset : ∀ x : Fin n, (C x).1.role ≠ .Resetting) :
    let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := runPairs P C [(w, v)]
    (∃ x : Fin n, (C' x).1.role = .Resetting) ∨
    ((∀ x : Fin n, (C' x).1.role ≠ .Resetting) ∧ unsettledMass C' < unsettledMass C) := by
  classical
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  set C' := runPairs P C [(w, v)]
  have hC' : C' = C.step P w v := by
    simp [C', runPairs]
  have hstep :=
    transitionPEM_unsettled_one_step_progress
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      C (w := w) (v := v) hw_unsettled hNoReset
  dsimp at hstep
  change (∃ x : Fin n, (C' x).1.role = .Resetting) ∨
    ((∀ x : Fin n, (C' x).1.role ≠ .Resetting) ∧ unsettledMass C' < unsettledMass C)
  have hfst : (C' w).1 =
      (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C w, C v)).1 := by
    rw [hC']
    simpa [P, protocolPEM] using Config.step_fst_state P C hwv.symm
  have hsnd : (C' v).1 =
      (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C w, C v)).2 := by
    rw [hC']
    simpa [P, protocolPEM] using Config.step_snd_state P C hwv.symm hwv
  rcases hstep with hreset | hprogress
  · rcases hreset with hreset | hreset
    · exact Or.inl ⟨w, by rw [hfst]; exact hreset⟩
    · exact Or.inl ⟨v, by rw [hsnd]; exact hreset⟩
  · have hNoReset' : ∀ x : Fin n, (C' x).1.role ≠ .Resetting := by
      intro x
      by_cases hxw : x = w
      · subst x
        rw [hfst]
        exact hprogress.1
      · by_cases hxv : x = v
        · subst x
          rw [hsnd]
          exact hprogress.2.1
        · rw [hC']
          unfold Config.step
          simp [hwv.symm, hxw, hxv, hNoReset x]
    have hw_lt :
        unsettledContribution (C' w).1 < unsettledContribution (C w).1 := by
      rw [hfst]
      simpa [unsettledContribution] using hprogress.2.2.1
    have hv_le :
        unsettledContribution (C' v).1 ≤ unsettledContribution (C v).1 := by
      rw [hsnd]
      simpa [unsettledContribution] using hprogress.2.2.2
    have hpointwise :
        ∀ x ∈ (Finset.univ : Finset (Fin n)),
          unsettledContribution (C' x).1 ≤ unsettledContribution (C x).1 := by
      intro x _
      by_cases hxw : x = w
      · subst x
        exact le_of_lt hw_lt
      · by_cases hxv : x = v
        · simpa [hxv] using hv_le
        · have hx_state : (C' x).1 = (C x).1 := by
            rw [hC']
            unfold Config.step
            simp [hwv.symm, hxw, hxv]
          rw [hx_state]
    have hstrict :
        ∃ x ∈ (Finset.univ : Finset (Fin n)),
          unsettledContribution (C' x).1 < unsettledContribution (C x).1 :=
      ⟨w, Finset.mem_univ w, hw_lt⟩
    refine Or.inr ⟨hNoReset', ?_⟩
    unfold unsettledMass
    exact Finset.sum_lt_sum hpointwise hstrict

theorem unsettled_one_step_progress_resetcount
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (C : Config (AgentState n) Opinion n)
    {w v : Fin n} (hwv : v ≠ w)
    (hw_unsettled : (C w).1.role = .Unsettled)
    (hNoReset : ∀ x : Fin n, (C x).1.role ≠ .Resetting) :
    let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := runPairs P C [(w, v)]
    (∃ x : Fin n, (C' x).1.role = .Resetting ∧ (C' x).1.resetcount = Rmax) ∨
    ((∀ x : Fin n, (C' x).1.role ≠ .Resetting) ∧ unsettledMass C' < unsettledMass C) := by
  classical
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  set C' := runPairs P C [(w, v)]
  have hC' : C' = C.step P w v := by
    simp [C', runPairs]
  have hstep :=
    transitionPEM_unsettled_one_step_progress
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      C (w := w) (v := v) hw_unsettled hNoReset
  have hrc :=
    transitionPEM_unsettled_one_step_resetcount
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      C (w := w) (v := v) hw_unsettled hNoReset
  dsimp at hstep hrc
  have hfst : (C' w).1 =
      (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C w, C v)).1 := by
    rw [hC']
    simpa [P, protocolPEM] using Config.step_fst_state P C hwv.symm
  have hsnd : (C' v).1 =
      (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C w, C v)).2 := by
    rw [hC']
    simpa [P, protocolPEM] using Config.step_snd_state P C hwv.symm hwv
  rcases hstep with hreset | hprogress
  · rcases hreset with hreset | hreset
    · refine Or.inl ⟨w, ?_, ?_⟩
      · rw [hfst]
        exact hreset
      · rw [congrArg AgentState.resetcount hfst]
        exact hrc.1 hreset
    · refine Or.inl ⟨v, ?_, ?_⟩
      · rw [hsnd]
        exact hreset
      · rw [congrArg AgentState.resetcount hsnd]
        exact hrc.2 hreset
  · have hNoReset' : ∀ x : Fin n, (C' x).1.role ≠ .Resetting := by
      intro x
      by_cases hxw : x = w
      · subst x
        rw [hfst]
        exact hprogress.1
      · by_cases hxv : x = v
        · subst x
          rw [hsnd]
          exact hprogress.2.1
        · rw [hC']
          unfold Config.step
          simp [hwv.symm, hxw, hxv, hNoReset x]
    have hw_lt :
        unsettledContribution (C' w).1 < unsettledContribution (C w).1 := by
      rw [hfst]
      simpa [unsettledContribution] using hprogress.2.2.1
    have hv_le :
        unsettledContribution (C' v).1 ≤ unsettledContribution (C v).1 := by
      rw [hsnd]
      simpa [unsettledContribution] using hprogress.2.2.2
    have hpointwise :
        ∀ x ∈ (Finset.univ : Finset (Fin n)),
          unsettledContribution (C' x).1 ≤ unsettledContribution (C x).1 := by
      intro x _
      by_cases hxw : x = w
      · subst x
        exact le_of_lt hw_lt
      · by_cases hxv : x = v
        · simpa [hxv] using hv_le
        · have hx_state : (C' x).1 = (C x).1 := by
            rw [hC']
            unfold Config.step
            simp [hwv.symm, hxw, hxv]
          rw [hx_state]
    have hstrict :
        ∃ x ∈ (Finset.univ : Finset (Fin n)),
          unsettledContribution (C' x).1 < unsettledContribution (C x).1 :=
      ⟨w, Finset.mem_univ w, hw_lt⟩
    refine Or.inr ⟨hNoReset', ?_⟩
    unfold unsettledMass
    exact Finset.sum_lt_sum hpointwise hstrict

theorem unsettled_one_step_progress_resetcount_leader
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (C : Config (AgentState n) Opinion n)
    {w v : Fin n} (hwv : v ≠ w)
    (hw_unsettled : (C w).1.role = .Unsettled)
    (hNoReset : ∀ x : Fin n, (C x).1.role ≠ .Resetting) :
    let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := runPairs P C [(w, v)]
    (∃ x : Fin n, (C' x).1.role = .Resetting ∧
      (C' x).1.resetcount = Rmax ∧ (C' x).1.leader = .L) ∨
    ((∀ x : Fin n, (C' x).1.role ≠ .Resetting) ∧ unsettledMass C' < unsettledMass C) := by
  classical
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  set C' := runPairs P C [(w, v)]
  have hC' : C' = C.step P w v := by
    simp [C', runPairs]
  have hstep :=
    transitionPEM_unsettled_one_step_progress
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      C (w := w) (v := v) hw_unsettled hNoReset
  have hrc :=
    transitionPEM_unsettled_one_step_resetcount
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      C (w := w) (v := v) hw_unsettled hNoReset
  have hleader :=
    transitionPEM_unsettled_one_step_reset_leader
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      C (w := w) (v := v) hw_unsettled hNoReset
  dsimp at hstep hrc hleader
  have hfst : (C' w).1 =
      (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C w, C v)).1 := by
    rw [hC']
    simpa [P, protocolPEM] using Config.step_fst_state P C hwv.symm
  have hsnd : (C' v).1 =
      (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C w, C v)).2 := by
    rw [hC']
    simpa [P, protocolPEM] using Config.step_snd_state P C hwv.symm hwv
  rcases hstep with hreset | hprogress
  · rcases hreset with hreset | hreset
    · refine Or.inl ⟨w, ?_, ?_, ?_⟩
      · rw [hfst]
        exact hreset
      · rw [congrArg AgentState.resetcount hfst]
        exact hrc.1 hreset
      · rw [congrArg AgentState.leader hfst]
        exact hleader.1 hreset
    · refine Or.inl ⟨v, ?_, ?_, ?_⟩
      · rw [hsnd]
        exact hreset
      · rw [congrArg AgentState.resetcount hsnd]
        exact hrc.2 hreset
      · rw [congrArg AgentState.leader hsnd]
        exact hleader.2 hreset
  · have hNoReset' : ∀ x : Fin n, (C' x).1.role ≠ .Resetting := by
      intro x
      by_cases hxw : x = w
      · subst x
        rw [hfst]
        exact hprogress.1
      · by_cases hxv : x = v
        · subst x
          rw [hsnd]
          exact hprogress.2.1
        · rw [hC']
          unfold Config.step
          simp [hwv.symm, hxw, hxv, hNoReset x]
    have hw_lt :
        unsettledContribution (C' w).1 < unsettledContribution (C w).1 := by
      rw [hfst]
      simpa [unsettledContribution] using hprogress.2.2.1
    have hv_le :
        unsettledContribution (C' v).1 ≤ unsettledContribution (C v).1 := by
      rw [hsnd]
      simpa [unsettledContribution] using hprogress.2.2.2
    have hpointwise :
        ∀ x ∈ (Finset.univ : Finset (Fin n)),
          unsettledContribution (C' x).1 ≤ unsettledContribution (C x).1 := by
      intro x _
      by_cases hxw : x = w
      · subst x
        exact le_of_lt hw_lt
      · by_cases hxv : x = v
        · simpa [hxv] using hv_le
        · have hx_state : (C' x).1 = (C x).1 := by
            rw [hC']
            unfold Config.step
            simp [hwv.symm, hxw, hxv]
          rw [hx_state]
    have hstrict :
        ∃ x ∈ (Finset.univ : Finset (Fin n)),
          unsettledContribution (C' x).1 < unsettledContribution (C x).1 :=
      ⟨w, Finset.mem_univ w, hw_lt⟩
    refine Or.inr ⟨hNoReset', ?_⟩
    unfold unsettledMass
    exact Finset.sum_lt_sum hpointwise hstrict

theorem unsettled_one_step_progress_reset_snapshot
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (C : Config (AgentState n) Opinion n)
    {w v : Fin n} (hwv : v ≠ w)
    (hw_unsettled : (C w).1.role = .Unsettled)
    (hNoReset : ∀ x : Fin n, (C x).1.role ≠ .Resetting) :
    let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := runPairs P C [(w, v)]
    (∃ x : Fin n, (C' x).1.role = .Resetting ∧
      (C' x).1.resetcount = Rmax ∧ (C' x).1.leader = .L ∧
      ∀ y : Fin n, (C' y).1.role = .Resetting →
        (C' y).1.resetcount = Rmax ∧ (C' y).1.leader = .L) ∨
    ((∀ x : Fin n, (C' x).1.role ≠ .Resetting) ∧ unsettledMass C' < unsettledMass C) := by
  classical
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  set C' := runPairs P C [(w, v)]
  have hC' : C' = C.step P w v := by
    simp [C', runPairs]
  have hstep :=
    transitionPEM_unsettled_one_step_progress
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      C (w := w) (v := v) hw_unsettled hNoReset
  have hrc :=
    transitionPEM_unsettled_one_step_resetcount
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      C (w := w) (v := v) hw_unsettled hNoReset
  have hleader :=
    transitionPEM_unsettled_one_step_reset_leader
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      C (w := w) (v := v) hw_unsettled hNoReset
  dsimp at hstep hrc hleader
  have hfst : (C' w).1 =
      (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C w, C v)).1 := by
    rw [hC']
    simpa [P, protocolPEM] using Config.step_fst_state P C hwv.symm
  have hsnd : (C' v).1 =
      (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C w, C v)).2 := by
    rw [hC']
    simpa [P, protocolPEM] using Config.step_snd_state P C hwv.symm hwv
  have hreset_fields :
      ∀ y : Fin n, (C' y).1.role = .Resetting →
        (C' y).1.resetcount = Rmax ∧ (C' y).1.leader = .L := by
    intro y hy_reset
    by_cases hyw : y = w
    · subst y
      rw [congrArg AgentState.resetcount hfst, congrArg AgentState.leader hfst]
      exact ⟨hrc.1 (by rw [← hfst]; exact hy_reset),
        hleader.1 (by rw [← hfst]; exact hy_reset)⟩
    · by_cases hyv : y = v
      · subst y
        rw [congrArg AgentState.resetcount hsnd, congrArg AgentState.leader hsnd]
        exact ⟨hrc.2 (by rw [← hsnd]; exact hy_reset),
          hleader.2 (by rw [← hsnd]; exact hy_reset)⟩
      · exfalso
        rw [hC'] at hy_reset
        unfold Config.step at hy_reset
        simp [hwv.symm, hyw, hyv, hNoReset y] at hy_reset
  rcases hstep with hreset | hprogress
  · rcases hreset with hreset | hreset
    · refine Or.inl ⟨w, ?_, ?_, ?_, hreset_fields⟩
      · rw [hfst]
        exact hreset
      · rw [congrArg AgentState.resetcount hfst]
        exact hrc.1 hreset
      · rw [congrArg AgentState.leader hfst]
        exact hleader.1 hreset
    · refine Or.inl ⟨v, ?_, ?_, ?_, hreset_fields⟩
      · rw [hsnd]
        exact hreset
      · rw [congrArg AgentState.resetcount hsnd]
        exact hrc.2 hreset
      · rw [congrArg AgentState.leader hsnd]
        exact hleader.2 hreset
  · have hNoReset' : ∀ x : Fin n, (C' x).1.role ≠ .Resetting := by
      intro x
      by_cases hxw : x = w
      · subst x
        rw [hfst]
        exact hprogress.1
      · by_cases hxv : x = v
        · subst x
          rw [hsnd]
          exact hprogress.2.1
        · rw [hC']
          unfold Config.step
          simp [hwv.symm, hxw, hxv, hNoReset x]
    have hw_lt :
        unsettledContribution (C' w).1 < unsettledContribution (C w).1 := by
      rw [hfst]
      simpa [unsettledContribution] using hprogress.2.2.1
    have hv_le :
        unsettledContribution (C' v).1 ≤ unsettledContribution (C v).1 := by
      rw [hsnd]
      simpa [unsettledContribution] using hprogress.2.2.2
    have hpointwise :
        ∀ x ∈ (Finset.univ : Finset (Fin n)),
          unsettledContribution (C' x).1 ≤ unsettledContribution (C x).1 := by
      intro x _
      by_cases hxw : x = w
      · subst x
        exact le_of_lt hw_lt
      · by_cases hxv : x = v
        · simpa [hxv] using hv_le
        · have hx_state : (C' x).1 = (C x).1 := by
            rw [hC']
            unfold Config.step
            simp [hwv.symm, hxw, hxv]
          rw [hx_state]
    have hstrict :
        ∃ x ∈ (Finset.univ : Finset (Fin n)),
          unsettledContribution (C' x).1 < unsettledContribution (C x).1 :=
      ⟨w, Finset.mem_univ w, hw_lt⟩
    refine Or.inr ⟨hNoReset', ?_⟩
    unfold unsettledMass
    exact Finset.sum_lt_sum hpointwise hstrict

theorem unsettled_branch_eventually_reset_or_allSettled
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n)
    (C : Config (AgentState n) Opinion n)
    (hUnsettled : ∃ w : Fin n, (C w).1.role = .Unsettled)
    (hNoReset : ∀ w : Fin n, (C w).1.role ≠ .Resetting) :
    let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    ∃ L : List (Fin n × Fin n),
      (∃ w : Fin n, (runPairs P C L w).1.role = .Resetting) ∨
      (∀ w : Fin n, (runPairs P C L w).1.role = .Settled) := by
  classical
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  change ∃ L : List (Fin n × Fin n),
      (∃ w : Fin n, (runPairs P C L w).1.role = .Resetting) ∨
      (∀ w : Fin n, (runPairs P C L w).1.role = .Settled)
  have hne_of_fin (w : Fin n) : ∃ v : Fin n, v ≠ w := by
    have hcard : 1 < Fintype.card (Fin n) := by
      rw [Fintype.card_fin]
      omega
    exact Fintype.exists_ne_of_one_lt_card hcard w
  have hrec :
      ∀ k : ℕ, ∀ C₀ : Config (AgentState n) Opinion n,
        unsettledMass C₀ = k →
        (∀ w : Fin n, (C₀ w).1.role ≠ .Resetting) →
        ∃ L : List (Fin n × Fin n),
          (∃ w : Fin n, (runPairs P C₀ L w).1.role = .Resetting) ∨
          (∀ w : Fin n, (runPairs P C₀ L w).1.role = .Settled) := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro C₀ hmass hNoReset₀
      by_cases hUn : ∃ w : Fin n, (C₀ w).1.role = .Unsettled
      · rcases hUn with ⟨w, hw_unsettled⟩
        rcases hne_of_fin w with ⟨v, hvw⟩
        have hstep :=
          unsettled_one_step_progress
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            C₀ (w := w) (v := v) hvw hw_unsettled hNoReset₀
        set C₁ := runPairs P C₀ [(w, v)]
        have hC₁ :
            C₁ =
              runPairs
                (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn))
                C₀ [(w, v)] := by
          simp [C₁, P]
        rcases hstep with hreset | hprogress
        · refine ⟨[(w, v)], Or.inl ?_⟩
          simpa [P] using hreset
        · have hNoReset₁ : ∀ x : Fin n, (C₁ x).1.role ≠ .Resetting := by
            intro x
            rw [hC₁]
            exact hprogress.1 x
          have hlt : unsettledMass C₁ < k := by
            rw [hC₁]
            rw [← hmass]
            exact hprogress.2
          have htail := ih (unsettledMass C₁) hlt C₁ rfl hNoReset₁
          rcases htail with ⟨Ltail, htail⟩
          refine ⟨(w, v) :: Ltail, ?_⟩
          simpa [C₁, runPairs_cons] using htail
      · refine ⟨[], Or.inr ?_⟩
        intro w
        simp only [runPairs_nil]
        have hnotU : (C₀ w).1.role ≠ .Unsettled := by
          intro hw
          exact hUn ⟨w, hw⟩
        have hnotR : (C₀ w).1.role ≠ .Resetting := hNoReset₀ w
        cases hrole : (C₀ w).1.role with
        | Resetting => exact False.elim (hnotR hrole)
        | Settled => rfl
        | Unsettled => exact False.elim (hnotU hrole)
  exact hrec (unsettledMass C) C rfl hNoReset

theorem unsettled_branch_eventually_resetcount_or_allSettled
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n)
    (C : Config (AgentState n) Opinion n)
    (hUnsettled : ∃ w : Fin n, (C w).1.role = .Unsettled)
    (hNoReset : ∀ w : Fin n, (C w).1.role ≠ .Resetting) :
    let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    ∃ L : List (Fin n × Fin n),
      (∃ w : Fin n, (runPairs P C L w).1.role = .Resetting ∧
        (runPairs P C L w).1.resetcount = Rmax) ∨
      (∀ w : Fin n, (runPairs P C L w).1.role = .Settled) := by
  classical
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  change ∃ L : List (Fin n × Fin n),
      (∃ w : Fin n, (runPairs P C L w).1.role = .Resetting ∧
        (runPairs P C L w).1.resetcount = Rmax) ∨
      (∀ w : Fin n, (runPairs P C L w).1.role = .Settled)
  have hne_of_fin (w : Fin n) : ∃ v : Fin n, v ≠ w := by
    have hcard : 1 < Fintype.card (Fin n) := by
      rw [Fintype.card_fin]
      omega
    exact Fintype.exists_ne_of_one_lt_card hcard w
  have hrec :
      ∀ k : ℕ, ∀ C₀ : Config (AgentState n) Opinion n,
        unsettledMass C₀ = k →
        (∀ w : Fin n, (C₀ w).1.role ≠ .Resetting) →
        ∃ L : List (Fin n × Fin n),
          (∃ w : Fin n, (runPairs P C₀ L w).1.role = .Resetting ∧
            (runPairs P C₀ L w).1.resetcount = Rmax) ∨
          (∀ w : Fin n, (runPairs P C₀ L w).1.role = .Settled) := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro C₀ hmass hNoReset₀
      by_cases hUn : ∃ w : Fin n, (C₀ w).1.role = .Unsettled
      · rcases hUn with ⟨w, hw_unsettled⟩
        rcases hne_of_fin w with ⟨v, hvw⟩
        have hstep :=
          unsettled_one_step_progress_resetcount
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            C₀ (w := w) (v := v) hvw hw_unsettled hNoReset₀
        set C₁ := runPairs P C₀ [(w, v)]
        have hC₁ :
            C₁ =
              runPairs
                (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn))
                C₀ [(w, v)] := by
          simp [C₁, P]
        rcases hstep with hreset | hprogress
        · refine ⟨[(w, v)], Or.inl ?_⟩
          simpa [P] using hreset
        · have hNoReset₁ : ∀ x : Fin n, (C₁ x).1.role ≠ .Resetting := by
            intro x
            rw [hC₁]
            exact hprogress.1 x
          have hlt : unsettledMass C₁ < k := by
            rw [hC₁]
            rw [← hmass]
            exact hprogress.2
          have htail := ih (unsettledMass C₁) hlt C₁ rfl hNoReset₁
          rcases htail with ⟨Ltail, htail⟩
          refine ⟨(w, v) :: Ltail, ?_⟩
          simp only [runPairs_cons]
          change
            (∃ x : Fin n, (runPairs P C₁ Ltail x).1.role = .Resetting ∧
              (runPairs P C₁ Ltail x).1.resetcount = Rmax) ∨
            (∀ x : Fin n, (runPairs P C₁ Ltail x).1.role = .Settled)
          exact htail
      · refine ⟨[], Or.inr ?_⟩
        intro w
        simp only [runPairs_nil]
        have hnotU : (C₀ w).1.role ≠ .Unsettled := by
          intro hw
          exact hUn ⟨w, hw⟩
        have hnotR : (C₀ w).1.role ≠ .Resetting := hNoReset₀ w
        cases hrole : (C₀ w).1.role with
        | Resetting => exact False.elim (hnotR hrole)
        | Settled => rfl
        | Unsettled => exact False.elim (hnotU hrole)
  exact hrec (unsettledMass C) C rfl hNoReset

theorem unsettled_branch_eventually_resetcount_leader_or_allSettled
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n)
    (C : Config (AgentState n) Opinion n)
    (hUnsettled : ∃ w : Fin n, (C w).1.role = .Unsettled)
    (hNoReset : ∀ w : Fin n, (C w).1.role ≠ .Resetting) :
    let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    ∃ L : List (Fin n × Fin n),
      (∃ w : Fin n, (runPairs P C L w).1.role = .Resetting ∧
        (runPairs P C L w).1.resetcount = Rmax ∧
        (runPairs P C L w).1.leader = .L) ∨
      (∀ w : Fin n, (runPairs P C L w).1.role = .Settled) := by
  classical
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  change ∃ L : List (Fin n × Fin n),
      (∃ w : Fin n, (runPairs P C L w).1.role = .Resetting ∧
        (runPairs P C L w).1.resetcount = Rmax ∧
        (runPairs P C L w).1.leader = .L) ∨
      (∀ w : Fin n, (runPairs P C L w).1.role = .Settled)
  have hne_of_fin (w : Fin n) : ∃ v : Fin n, v ≠ w := by
    have hcard : 1 < Fintype.card (Fin n) := by
      rw [Fintype.card_fin]
      omega
    exact Fintype.exists_ne_of_one_lt_card hcard w
  have hrec :
      ∀ k : ℕ, ∀ C₀ : Config (AgentState n) Opinion n,
        unsettledMass C₀ = k →
        (∀ w : Fin n, (C₀ w).1.role ≠ .Resetting) →
        ∃ L : List (Fin n × Fin n),
          (∃ w : Fin n, (runPairs P C₀ L w).1.role = .Resetting ∧
            (runPairs P C₀ L w).1.resetcount = Rmax ∧
            (runPairs P C₀ L w).1.leader = .L) ∨
          (∀ w : Fin n, (runPairs P C₀ L w).1.role = .Settled) := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro C₀ hmass hNoReset₀
      by_cases hUn : ∃ w : Fin n, (C₀ w).1.role = .Unsettled
      · rcases hUn with ⟨w, hw_unsettled⟩
        rcases hne_of_fin w with ⟨v, hvw⟩
        have hstep :=
          unsettled_one_step_progress_resetcount_leader
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            C₀ (w := w) (v := v) hvw hw_unsettled hNoReset₀
        set C₁ := runPairs P C₀ [(w, v)]
        have hC₁ :
            C₁ =
              runPairs
                (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn))
                C₀ [(w, v)] := by
          simp [C₁, P]
        rcases hstep with hreset | hprogress
        · refine ⟨[(w, v)], Or.inl ?_⟩
          simpa [P] using hreset
        · have hNoReset₁ : ∀ x : Fin n, (C₁ x).1.role ≠ .Resetting := by
            intro x
            rw [hC₁]
            exact hprogress.1 x
          have hlt : unsettledMass C₁ < k := by
            rw [hC₁]
            rw [← hmass]
            exact hprogress.2
          have htail := ih (unsettledMass C₁) hlt C₁ rfl hNoReset₁
          rcases htail with ⟨Ltail, htail⟩
          refine ⟨(w, v) :: Ltail, ?_⟩
          simp only [runPairs_cons]
          change
            (∃ x : Fin n, (runPairs P C₁ Ltail x).1.role = .Resetting ∧
              (runPairs P C₁ Ltail x).1.resetcount = Rmax ∧
              (runPairs P C₁ Ltail x).1.leader = .L) ∨
            (∀ x : Fin n, (runPairs P C₁ Ltail x).1.role = .Settled)
          exact htail
      · refine ⟨[], Or.inr ?_⟩
        intro w
        simp only [runPairs_nil]
        have hnotU : (C₀ w).1.role ≠ .Unsettled := by
          intro hw
          exact hUn ⟨w, hw⟩
        have hnotR : (C₀ w).1.role ≠ .Resetting := hNoReset₀ w
        cases hrole : (C₀ w).1.role with
        | Resetting => exact False.elim (hnotR hrole)
        | Settled => rfl
        | Unsettled => exact False.elim (hnotU hrole)
  exact hrec (unsettledMass C) C rfl hNoReset

theorem unsettled_branch_eventually_reset_snapshot_or_allSettled
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n)
    (C : Config (AgentState n) Opinion n)
    (hUnsettled : ∃ w : Fin n, (C w).1.role = .Unsettled)
    (hNoReset : ∀ w : Fin n, (C w).1.role ≠ .Resetting) :
    let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    ∃ L : List (Fin n × Fin n),
      (∃ w : Fin n, (runPairs P C L w).1.role = .Resetting ∧
        (runPairs P C L w).1.resetcount = Rmax ∧
        (runPairs P C L w).1.leader = .L ∧
        ∀ y : Fin n, (runPairs P C L y).1.role = .Resetting →
          (runPairs P C L y).1.resetcount = Rmax ∧
          (runPairs P C L y).1.leader = .L) ∨
      (∀ w : Fin n, (runPairs P C L w).1.role = .Settled) := by
  classical
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  change ∃ L : List (Fin n × Fin n),
      (∃ w : Fin n, (runPairs P C L w).1.role = .Resetting ∧
        (runPairs P C L w).1.resetcount = Rmax ∧
        (runPairs P C L w).1.leader = .L ∧
        ∀ y : Fin n, (runPairs P C L y).1.role = .Resetting →
          (runPairs P C L y).1.resetcount = Rmax ∧
          (runPairs P C L y).1.leader = .L) ∨
      (∀ w : Fin n, (runPairs P C L w).1.role = .Settled)
  have hne_of_fin (w : Fin n) : ∃ v : Fin n, v ≠ w := by
    have hcard : 1 < Fintype.card (Fin n) := by
      rw [Fintype.card_fin]
      omega
    exact Fintype.exists_ne_of_one_lt_card hcard w
  have hrec :
      ∀ k : ℕ, ∀ C₀ : Config (AgentState n) Opinion n,
        unsettledMass C₀ = k →
        (∀ w : Fin n, (C₀ w).1.role ≠ .Resetting) →
        ∃ L : List (Fin n × Fin n),
          (∃ w : Fin n, (runPairs P C₀ L w).1.role = .Resetting ∧
            (runPairs P C₀ L w).1.resetcount = Rmax ∧
            (runPairs P C₀ L w).1.leader = .L ∧
            ∀ y : Fin n, (runPairs P C₀ L y).1.role = .Resetting →
              (runPairs P C₀ L y).1.resetcount = Rmax ∧
              (runPairs P C₀ L y).1.leader = .L) ∨
          (∀ w : Fin n, (runPairs P C₀ L w).1.role = .Settled) := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro C₀ hmass hNoReset₀
      by_cases hUn : ∃ w : Fin n, (C₀ w).1.role = .Unsettled
      · rcases hUn with ⟨w, hw_unsettled⟩
        rcases hne_of_fin w with ⟨v, hvw⟩
        have hstep :=
          unsettled_one_step_progress_reset_snapshot
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            C₀ (w := w) (v := v) hvw hw_unsettled hNoReset₀
        set C₁ := runPairs P C₀ [(w, v)]
        have hC₁ :
            C₁ =
              runPairs
                (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn))
                C₀ [(w, v)] := by
          simp [C₁, P]
        rcases hstep with hreset | hprogress
        · refine ⟨[(w, v)], Or.inl ?_⟩
          simpa [P] using hreset
        · have hNoReset₁ : ∀ x : Fin n, (C₁ x).1.role ≠ .Resetting := by
            intro x
            rw [hC₁]
            exact hprogress.1 x
          have hlt : unsettledMass C₁ < k := by
            rw [hC₁]
            rw [← hmass]
            exact hprogress.2
          have htail := ih (unsettledMass C₁) hlt C₁ rfl hNoReset₁
          rcases htail with ⟨Ltail, htail⟩
          refine ⟨(w, v) :: Ltail, ?_⟩
          simp only [runPairs_cons]
          change
            (∃ x : Fin n, (runPairs P C₁ Ltail x).1.role = .Resetting ∧
              (runPairs P C₁ Ltail x).1.resetcount = Rmax ∧
              (runPairs P C₁ Ltail x).1.leader = .L ∧
              ∀ y : Fin n, (runPairs P C₁ Ltail y).1.role = .Resetting →
                (runPairs P C₁ Ltail y).1.resetcount = Rmax ∧
                (runPairs P C₁ Ltail y).1.leader = .L) ∨
            (∀ x : Fin n, (runPairs P C₁ Ltail x).1.role = .Settled)
          exact htail
      · refine ⟨[], Or.inr ?_⟩
        intro w
        simp only [runPairs_nil]
        have hnotU : (C₀ w).1.role ≠ .Unsettled := by
          intro hw
          exact hUn ⟨w, hw⟩
        have hnotR : (C₀ w).1.role ≠ .Resetting := hNoReset₀ w
        cases hrole : (C₀ w).1.role with
        | Resetting => exact False.elim (hnotR hrole)
        | Settled => rfl
        | Unsettled => exact False.elim (hnotU hrole)
  exact hrec (unsettledMass C) C rfl hNoReset

/-! ### Phase lemma stubs for BurmanConvergence composition

Each phase takes a precondition and produces a list schedule + post-condition.
The full convergence proof composes them via runPairs_append. -/

/-- Phase 1: From ANY config, reach InSrank OR produce ≥ 1 Resetting agent.
(ChatGPT insight: returning InSrank directly handles the case where
Unsettled agents get recruited to Settled without triggering reset.) -/
theorem phase1_trigger_reset_or_InSrank
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (C : Config (AgentState n) Opinion n) :
    ∃ L : List (Fin n × Fin n),
      let C' := runPairs (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L
      InSrank C' ∨ (∃ w : Fin n, (C' w).1.role = .Resetting) := by
  classical
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  change ∃ L : List (Fin n × Fin n),
      let C' := runPairs P C L
      InSrank C' ∨ (∃ w : Fin n, (C' w).1.role = .Resetting)
  by_cases hReset : ∃ w : Fin n, (C w).1.role = .Resetting
  · refine ⟨[], ?_⟩
    simp only [runPairs_nil]
    exact Or.inr hReset
  · have hNoReset : ∀ w : Fin n, (C w).1.role ≠ .Resetting := by
      intro w hw
      exact hReset ⟨w, hw⟩
    have hReach :
        ∃ L : List (Fin n × Fin n),
          (∃ w : Fin n, (runPairs P C L w).1.role = .Resetting) ∨
          (∀ w : Fin n, (runPairs P C L w).1.role = .Settled) := by
      by_cases hUn : ∃ w : Fin n, (C w).1.role = .Unsettled
      · simpa [P] using
          unsettled_branch_eventually_reset_or_allSettled
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            hn4 C hUn hNoReset
      · refine ⟨[], Or.inr ?_⟩
        intro w
        simp only [runPairs_nil]
        have hnotU : (C w).1.role ≠ .Unsettled := by
          intro hw
          exact hUn ⟨w, hw⟩
        have hnotR : (C w).1.role ≠ .Resetting := hNoReset w
        cases hrole : (C w).1.role with
        | Resetting => exact False.elim (hnotR hrole)
        | Settled => rfl
        | Unsettled => exact False.elim (hnotU hrole)
    rcases hReach with ⟨L₀, hReach⟩
    rcases hReach with hResetAfter | hAllSettled
    · refine ⟨L₀, ?_⟩
      exact Or.inr hResetAfter
    · set C₀ := runPairs P C L₀
      have hAllSettled₀ : ∀ w : Fin n, (C₀ w).1.role = .Settled := by
        intro w
        simpa [C₀] using hAllSettled w
      by_cases hSrank : InSrank C₀
      · refine ⟨L₀, ?_⟩
        exact Or.inl hSrank
      · obtain ⟨u, v, huv, hcol⟩ :=
          trigger_reset_from_all_settled_non_InSrank
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            (C₀ := C₀) hAllSettled₀ hSrank
        refine ⟨L₀ ++ [(u, v)], ?_⟩
        refine Or.inr ⟨u, ?_⟩
        have hcol_u : (runPairs P C₀ [(u, v)] u).1.role = .Resetting := by
          simpa [P, runPairs] using hcol.1
        rw [runPairs_append]
        change (runPairs P C₀ [(u, v)] u).1.role = .Resetting
        exact hcol_u

theorem phase1_no_reset_trigger_resetcount_or_InSrank
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (C : Config (AgentState n) Opinion n)
    (hNoReset : ∀ w : Fin n, (C w).1.role ≠ .Resetting) :
    ∃ L : List (Fin n × Fin n),
      let C' := runPairs (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L
      InSrank C' ∨
        (∃ w : Fin n, (C' w).1.role = .Resetting ∧ (C' w).1.resetcount = Rmax) := by
  classical
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  change ∃ L : List (Fin n × Fin n),
      let C' := runPairs P C L
      InSrank C' ∨
        (∃ w : Fin n, (C' w).1.role = .Resetting ∧ (C' w).1.resetcount = Rmax)
  have hReach :
      ∃ L : List (Fin n × Fin n),
        (∃ w : Fin n, (runPairs P C L w).1.role = .Resetting ∧
          (runPairs P C L w).1.resetcount = Rmax) ∨
        (∀ w : Fin n, (runPairs P C L w).1.role = .Settled) := by
    by_cases hUn : ∃ w : Fin n, (C w).1.role = .Unsettled
    · simpa [P] using
        unsettled_branch_eventually_resetcount_or_allSettled
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hn4 C hUn hNoReset
    · refine ⟨[], Or.inr ?_⟩
      intro w
      simp only [runPairs_nil]
      have hnotU : (C w).1.role ≠ .Unsettled := by
        intro hw
        exact hUn ⟨w, hw⟩
      have hnotR : (C w).1.role ≠ .Resetting := hNoReset w
      cases hrole : (C w).1.role with
      | Resetting => exact False.elim (hnotR hrole)
      | Settled => rfl
      | Unsettled => exact False.elim (hnotU hrole)
  rcases hReach with ⟨L₀, hReach⟩
  rcases hReach with hResetAfter | hAllSettled
  · refine ⟨L₀, ?_⟩
    exact Or.inr hResetAfter
  · set C₀ := runPairs P C L₀
    have hAllSettled₀ : ∀ w : Fin n, (C₀ w).1.role = .Settled := by
      intro w
      simpa [C₀] using hAllSettled w
    by_cases hSrank : InSrank C₀
    · refine ⟨L₀, ?_⟩
      exact Or.inl hSrank
    · obtain ⟨u, v, huv, hcol⟩ :=
        trigger_reset_from_all_settled_non_InSrank
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          (C₀ := C₀) hAllSettled₀ hSrank
      refine ⟨L₀ ++ [(u, v)], ?_⟩
      refine Or.inr ⟨u, ?_, ?_⟩
      · have hcol_u : (runPairs P C₀ [(u, v)] u).1.role = .Resetting := by
          simpa [P, runPairs] using hcol.1
        rw [runPairs_append]
        change (runPairs P C₀ [(u, v)] u).1.role = .Resetting
        exact hcol_u
      · have hcol_u_rc : (runPairs P C₀ [(u, v)] u).1.resetcount = Rmax := by
          simpa [P, runPairs] using hcol.2.2.1
        rw [runPairs_append]
        change (runPairs P C₀ [(u, v)] u).1.resetcount = Rmax
        exact hcol_u_rc

theorem phase1_no_reset_trigger_resetcount_leader_or_InSrank
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (C : Config (AgentState n) Opinion n)
    (hNoReset : ∀ w : Fin n, (C w).1.role ≠ .Resetting) :
    ∃ L : List (Fin n × Fin n),
      let C' := runPairs (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L
      InSrank C' ∨
        (∃ w : Fin n, (C' w).1.role = .Resetting ∧
          (C' w).1.resetcount = Rmax ∧ (C' w).1.leader = .L) := by
  classical
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  change ∃ L : List (Fin n × Fin n),
      let C' := runPairs P C L
      InSrank C' ∨
        (∃ w : Fin n, (C' w).1.role = .Resetting ∧
          (C' w).1.resetcount = Rmax ∧ (C' w).1.leader = .L)
  have hReach :
      ∃ L : List (Fin n × Fin n),
        (∃ w : Fin n, (runPairs P C L w).1.role = .Resetting ∧
          (runPairs P C L w).1.resetcount = Rmax ∧
          (runPairs P C L w).1.leader = .L) ∨
        (∀ w : Fin n, (runPairs P C L w).1.role = .Settled) := by
    by_cases hUn : ∃ w : Fin n, (C w).1.role = .Unsettled
    · simpa [P] using
        unsettled_branch_eventually_resetcount_leader_or_allSettled
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hn4 C hUn hNoReset
    · refine ⟨[], Or.inr ?_⟩
      intro w
      simp only [runPairs_nil]
      have hnotU : (C w).1.role ≠ .Unsettled := by
        intro hw
        exact hUn ⟨w, hw⟩
      have hnotR : (C w).1.role ≠ .Resetting := hNoReset w
      cases hrole : (C w).1.role with
      | Resetting => exact False.elim (hnotR hrole)
      | Settled => rfl
      | Unsettled => exact False.elim (hnotU hrole)
  rcases hReach with ⟨L₀, hReach⟩
  rcases hReach with hResetAfter | hAllSettled
  · refine ⟨L₀, ?_⟩
    exact Or.inr hResetAfter
  · set C₀ := runPairs P C L₀
    have hAllSettled₀ : ∀ w : Fin n, (C₀ w).1.role = .Settled := by
      intro w
      simpa [C₀] using hAllSettled w
    by_cases hSrank : InSrank C₀
    · refine ⟨L₀, ?_⟩
      exact Or.inl hSrank
    · obtain ⟨u, v, huv, hcol⟩ :=
        trigger_reset_from_all_settled_non_InSrank_with_leader
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          (C₀ := C₀) hAllSettled₀ hSrank
      refine ⟨L₀ ++ [(u, v)], ?_⟩
      refine Or.inr ⟨u, ?_, ?_, ?_⟩
      · have hcol_u : (runPairs P C₀ [(u, v)] u).1.role = .Resetting := by
          simpa [P, runPairs] using hcol.1
        rw [runPairs_append]
        change (runPairs P C₀ [(u, v)] u).1.role = .Resetting
        exact hcol_u
      · have hcol_u_rc : (runPairs P C₀ [(u, v)] u).1.resetcount = Rmax := by
          simpa [P, runPairs] using hcol.2.1
        rw [runPairs_append]
        change (runPairs P C₀ [(u, v)] u).1.resetcount = Rmax
        exact hcol_u_rc
      · have hcol_u_leader : (runPairs P C₀ [(u, v)] u).1.leader = .L := by
          simpa [P, runPairs] using hcol.2.2.1
        rw [runPairs_append]
        change (runPairs P C₀ [(u, v)] u).1.leader = .L
        exact hcol_u_leader

theorem phase1_no_reset_trigger_snapshot_or_InSrank
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (C : Config (AgentState n) Opinion n)
    (hNoReset : ∀ w : Fin n, (C w).1.role ≠ .Resetting) :
    ∃ L : List (Fin n × Fin n),
      let C' := runPairs (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L
      InSrank C' ∨
        (∃ w : Fin n, (C' w).1.role = .Resetting ∧
          (C' w).1.resetcount = Rmax ∧ (C' w).1.leader = .L ∧
          ∀ y : Fin n, (C' y).1.role = .Resetting →
            (C' y).1.resetcount = Rmax ∧ (C' y).1.leader = .L) := by
  classical
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  change ∃ L : List (Fin n × Fin n),
      let C' := runPairs P C L
      InSrank C' ∨
        (∃ w : Fin n, (C' w).1.role = .Resetting ∧
          (C' w).1.resetcount = Rmax ∧ (C' w).1.leader = .L ∧
          ∀ y : Fin n, (C' y).1.role = .Resetting →
            (C' y).1.resetcount = Rmax ∧ (C' y).1.leader = .L)
  have hReach :
      ∃ L : List (Fin n × Fin n),
        (∃ w : Fin n, (runPairs P C L w).1.role = .Resetting ∧
          (runPairs P C L w).1.resetcount = Rmax ∧
          (runPairs P C L w).1.leader = .L ∧
          ∀ y : Fin n, (runPairs P C L y).1.role = .Resetting →
            (runPairs P C L y).1.resetcount = Rmax ∧
            (runPairs P C L y).1.leader = .L) ∨
        (∀ w : Fin n, (runPairs P C L w).1.role = .Settled) := by
    by_cases hUn : ∃ w : Fin n, (C w).1.role = .Unsettled
    · simpa [P] using
        unsettled_branch_eventually_reset_snapshot_or_allSettled
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hn4 C hUn hNoReset
    · refine ⟨[], Or.inr ?_⟩
      intro w
      simp only [runPairs_nil]
      have hnotU : (C w).1.role ≠ .Unsettled := by
        intro hw
        exact hUn ⟨w, hw⟩
      have hnotR : (C w).1.role ≠ .Resetting := hNoReset w
      cases hrole : (C w).1.role with
      | Resetting => exact False.elim (hnotR hrole)
      | Settled => rfl
      | Unsettled => exact False.elim (hnotU hrole)
  rcases hReach with ⟨L₀, hReach⟩
  rcases hReach with hResetAfter | hAllSettled
  · refine ⟨L₀, ?_⟩
    exact Or.inr hResetAfter
  · set C₀ := runPairs P C L₀
    have hAllSettled₀ : ∀ w : Fin n, (C₀ w).1.role = .Settled := by
      intro w
      simpa [C₀] using hAllSettled w
    by_cases hSrank : InSrank C₀
    · refine ⟨L₀, ?_⟩
      exact Or.inl hSrank
    · obtain ⟨u, v, huv, hcol⟩ :=
        trigger_reset_from_all_settled_non_InSrank_with_leader
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          (C₀ := C₀) hAllSettled₀ hSrank
      have hsnap :
          ∀ y : Fin n, (runPairs P C₀ [(u, v)] y).1.role = .Resetting →
            (runPairs P C₀ [(u, v)] y).1.resetcount = Rmax ∧
            (runPairs P C₀ [(u, v)] y).1.leader = .L := by
        intro y hy_reset
        by_cases hyu : y = u
        · subst y
          exact ⟨by simpa [P, runPairs] using hcol.2.1,
            by simpa [P, runPairs] using hcol.2.2.1⟩
        · by_cases hyv : y = v
          · subst y
            exact ⟨by simpa [P, runPairs] using hcol.2.2.2.2.1,
              by simpa [P, runPairs] using hcol.2.2.2.2.2⟩
          · have hy_state : runPairs P C₀ [(u, v)] y = C₀ y := by
              simp [runPairs, Config.step, huv, hyu, hyv]
            have hy_settled : (runPairs P C₀ [(u, v)] y).1.role = .Settled := by
              rw [hy_state]
              exact hAllSettled₀ y
            rw [hy_settled] at hy_reset
            cases hy_reset
      refine ⟨L₀ ++ [(u, v)], ?_⟩
      rw [runPairs_append]
      refine Or.inr ⟨u, ?_, ?_, ?_, ?_⟩
      · change (runPairs P C₀ [(u, v)] u).1.role = .Resetting
        simpa [P, runPairs] using hcol.1
      · change (runPairs P C₀ [(u, v)] u).1.resetcount = Rmax
        simpa [P, runPairs] using hcol.2.1
      · change (runPairs P C₀ [(u, v)] u).1.leader = .L
        simpa [P, runPairs] using hcol.2.2.1
      · intro y hy_reset
        change (runPairs P C₀ [(u, v)] y).1.resetcount = Rmax ∧
          (runPairs P C₀ [(u, v)] y).1.leader = .L
        exact hsnap y hy_reset

/-- Phase 3b/3c target, Phase 4 input: one Settled root + rest Unsettled.
(ChatGPT: uses rank.val = 0 to avoid hn parameter.) -/
def FreshRankingStart (C : Config (AgentState n) Opinion n) : Prop :=
  ∃ root : Fin n,
    (C root).1.role = .Settled ∧
    (C root).1.rank.val = 0 ∧
    (C root).1.children = 0 ∧
    ∀ w : Fin n, w ≠ root → (C w).1.role = .Unsettled

def nonResettingCount (C : Config (AgentState n) Opinion n) : ℕ :=
  (Finset.univ.filter (fun w : Fin n => (C w).1.role ≠ .Resetting)).card

/-- Single-step spread: Resetting(rc>0) meets non-Resetting → second becomes Resetting. -/
theorem propagate_reset_one_step
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 1 < Dmax)
    (C₀ : Config (AgentState n) Opinion n)
    {r v : Fin n} (hrv : r ≠ v)
    (hr_res : (C₀ r).1.role = .Resetting) (hr_rc : 0 < (C₀ r).1.resetcount)
    (hv_not : (C₀ v).1.role ≠ .Resetting) :
    let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    (C₀.step P r v v).1.role = .Resetting := by
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  change (C₀.step P r v v).1.role = .Resetting
  have h_rd := rankDeltaOSSR_propagate_reset (Rmax := Rmax) (Emax := Emax)
    (Dmax := Dmax) (hn := hn) hr_res hr_rc hv_not hDmax
  have h_not_both : ¬((rankDeltaOSSR Rmax Emax Dmax hn ((C₀ r).1, (C₀ v).1)).1.role = .Settled ∧
                      (rankDeltaOSSR Rmax Emax Dmax hn ((C₀ r).1, (C₀ v).1)).2.role = .Settled) := by
    intro hsettled
    rw [h_rd] at hsettled
    exact Role.noConfusion hsettled.2
  have h_pass := transitionPEM_structural_passthrough (trank := Rmax) (Rmax := Rmax)
    (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn) (x₀ := (C₀ r).2) (x₁ := (C₀ v).2)
    h_not_both
  have h_snd := Config.step_snd_state P C₀ hrv hrv.symm
  rw [congrArg AgentState.role h_snd]
  exact h_pass.2.2.2.2.2.2.1 ▸ h_rd

/-- After spread step, the spreader stays Resetting with rc decremented. -/
theorem propagate_reset_spreader_state
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 1 < Dmax)
    (C₀ : Config (AgentState n) Opinion n)
    {r v : Fin n} (hrv : r ≠ v)
    (hr_res : (C₀ r).1.role = .Resetting) (hr_rc : 0 < (C₀ r).1.resetcount)
    (hv_not : (C₀ v).1.role ≠ .Resetting) :
    let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    (C₀.step P r v r).1.role = .Resetting ∧
    (C₀.step P r v r).1.resetcount = (C₀ r).1.resetcount - 1 ∧
    (C₀.step P r v r).1.leader = (C₀ r).1.leader := by
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  change (C₀.step P r v r).1.role = .Resetting ∧
    (C₀.step P r v r).1.resetcount = (C₀ r).1.resetcount - 1 ∧
    (C₀.step P r v r).1.leader = (C₀ r).1.leader
  have h_rd := rankDeltaOSSR_propagate_reset_spreader (Rmax := Rmax) (Emax := Emax)
    (Dmax := Dmax) (hn := hn) hr_res hr_rc hv_not hDmax
  have h_rd_leader := rankDeltaOSSR_propagate_reset_spreader_leader
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hr_res hr_rc hv_not hDmax
  have h_not_both : ¬((rankDeltaOSSR Rmax Emax Dmax hn ((C₀ r).1, (C₀ v).1)).1.role = .Settled ∧
                      (rankDeltaOSSR Rmax Emax Dmax hn ((C₀ r).1, (C₀ v).1)).2.role = .Settled) := by
    intro hsettled
    rw [h_rd.1] at hsettled
    exact Role.noConfusion hsettled.1
  have h_pass := transitionPEM_structural_passthrough (trank := Rmax) (Rmax := Rmax)
    (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn) (x₀ := (C₀ r).2) (x₁ := (C₀ v).2)
    h_not_both
  have h_fst := Config.step_fst_state P C₀ hrv
  refine ⟨?_, ?_, ?_⟩
  · rw [congrArg AgentState.role h_fst]
    exact h_pass.1 ▸ h_rd.1
  · rw [congrArg AgentState.resetcount h_fst]
    exact h_pass.2.2.2.2.1 ▸ h_rd.2
  · rw [congrArg AgentState.leader h_fst]
    exact h_pass.2.1 ▸ h_rd_leader

theorem propagate_reset_step_nonResettingCount_lt
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 1 < Dmax)
    (C₀ : Config (AgentState n) Opinion n)
    {r v : Fin n} (hrv : r ≠ v)
    (hr_res : (C₀ r).1.role = .Resetting) (hr_rc : 0 < (C₀ r).1.resetcount)
    (hv_not : (C₀ v).1.role ≠ .Resetting) :
    let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C₁ := C₀.step P r v
    (C₁ r).1.role = .Resetting ∧
    (C₁ r).1.resetcount = (C₀ r).1.resetcount - 1 ∧
    (C₁ v).1.role = .Resetting ∧
    nonResettingCount C₁ < nonResettingCount C₀ := by
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  set C₁ := C₀.step P r v with hC₁
  have hv_reset : (C₁ v).1.role = .Resetting := by
    rw [hC₁]
    exact propagate_reset_one_step
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hDmax C₀ hrv hr_res hr_rc hv_not
  have hr_trace :=
    propagate_reset_spreader_state
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hDmax C₀ hrv hr_res hr_rc hv_not
  have hr_reset : (C₁ r).1.role = .Resetting := by
    rw [hC₁]
    exact hr_trace.1
  have hr_rc_eq : (C₁ r).1.resetcount = (C₀ r).1.resetcount - 1 := by
    rw [hC₁]
    exact hr_trace.2.1
  set S := Finset.univ.filter (fun w : Fin n => (C₀ w).1.role ≠ .Resetting) with hS
  set S' := Finset.univ.filter (fun w : Fin n => (C₁ w).1.role ≠ .Resetting) with hS'
  have hv_mem : v ∈ S := by
    rw [hS, Finset.mem_filter]
    exact ⟨Finset.mem_univ v, hv_not⟩
  have hsub : S' ⊆ S.erase v := by
    intro x hx
    have hx_not : (C₁ x).1.role ≠ .Resetting := by
      rw [hS'] at hx
      exact (Finset.mem_filter.mp hx).2
    have hx_ne_v : x ≠ v := by
      intro hxv
      subst x
      exact hx_not hv_reset
    have hx_ne_r : x ≠ r := by
      intro hxr
      subst x
      exact hx_not hr_reset
    have hx_C : (C₀ x).1.role ≠ .Resetting := by
      have hx_state : C₁ x = C₀ x := by
        rw [hC₁]
        unfold Config.step
        simp [hrv, hx_ne_r, hx_ne_v]
      intro hx_reset
      exact hx_not (by rw [hx_state]; exact hx_reset)
    rw [Finset.mem_erase]
    exact ⟨hx_ne_v, by rw [hS, Finset.mem_filter]; exact ⟨Finset.mem_univ x, hx_C⟩⟩
  have hcard_le : S'.card ≤ (S.erase v).card := Finset.card_le_card hsub
  have hcard_erase : (S.erase v).card = S.card - 1 := Finset.card_erase_of_mem hv_mem
  have hcard_pos : 0 < S.card := Finset.card_pos.mpr ⟨v, hv_mem⟩
  have hcount_lt : S'.card < S.card := by omega
  refine ⟨hr_reset, hr_rc_eq, hv_reset, ?_⟩
  change S'.card < S.card
  exact hcount_lt

/-- Phase 2: From config with ≥ 1 Resetting (with sufficient resetcount), spread to all agents. -/
theorem phase2_propagate_reset
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 1 < Dmax)
    (C : Config (AgentState n) Opinion n)
    (hReset : ∃ r : Fin n, (C r).1.role = .Resetting ∧ n ≤ (C r).1.resetcount) :
    ∃ L : List (Fin n × Fin n),
      ∀ w : Fin n, (runPairs (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L w).1.role = .Resetting := by
  classical
  rcases hReset with ⟨r, hr_res, hr_rc_ge⟩
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have hrec :
      ∀ k : ℕ, ∀ C₀ : Config (AgentState n) Opinion n,
        nonResettingCount C₀ = k →
        (C₀ r).1.role = .Resetting →
        nonResettingCount C₀ < (C₀ r).1.resetcount →
        ∃ L : List (Fin n × Fin n),
          ∀ w : Fin n, (runPairs P C₀ L w).1.role = .Resetting := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro C₀ hcount hr_res₀ hcount_lt_rc
      by_cases hk0 : k = 0
      · refine ⟨[], ?_⟩
        intro w
        simp only [runPairs_nil]
        by_contra hw_not
        have hw_mem :
            w ∈ Finset.univ.filter (fun x : Fin n => (C₀ x).1.role ≠ .Resetting) := by
          rw [Finset.mem_filter]
          exact ⟨Finset.mem_univ w, hw_not⟩
        have hpos :
            0 < (Finset.univ.filter
              (fun x : Fin n => (C₀ x).1.role ≠ .Resetting)).card :=
          Finset.card_pos.mpr ⟨w, hw_mem⟩
        unfold nonResettingCount at hcount
        omega
      · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
        have hcount_pos : 0 < nonResettingCount C₀ := by
          rw [hcount]
          exact hkpos
        obtain ⟨v, hv_mem⟩ : ∃ v : Fin n,
            v ∈ Finset.univ.filter (fun x : Fin n => (C₀ x).1.role ≠ .Resetting) := by
          exact Finset.card_pos.mp hcount_pos
        have hv_not : (C₀ v).1.role ≠ .Resetting :=
          (Finset.mem_filter.mp hv_mem).2
        have hrv : r ≠ v := by
          intro hrv_eq
          subst v
          exact hv_not hr_res₀
        have hr_rc_pos : 0 < (C₀ r).1.resetcount := by omega
        have hstep :=
          propagate_reset_step_nonResettingCount_lt
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            hDmax C₀ hrv hr_res₀ hr_rc_pos hv_not
        set C₁ := C₀.step P r v with hC₁
        have hr_res₁ : (C₁ r).1.role = .Resetting := by
          rw [hC₁]
          exact hstep.1
        have hr_rc₁ : (C₁ r).1.resetcount = (C₀ r).1.resetcount - 1 := by
          rw [hC₁]
          exact hstep.2.1
        have hcount_lt : nonResettingCount C₁ < nonResettingCount C₀ := by
          rw [hC₁]
          exact hstep.2.2.2
        have hlt_k : nonResettingCount C₁ < k := by
          rw [← hcount]
          exact hcount_lt
        have hcount_lt_rc₁ : nonResettingCount C₁ < (C₁ r).1.resetcount := by
          rw [hr_rc₁]
          omega
        obtain ⟨Ltail, htail⟩ :=
          ih (nonResettingCount C₁) hlt_k C₁ rfl hr_res₁ hcount_lt_rc₁
        refine ⟨(r, v) :: Ltail, ?_⟩
        simpa [C₁, runPairs_cons] using htail
  have hcount_lt_initial : nonResettingCount C < (C r).1.resetcount := by
    set S := Finset.univ.filter (fun w : Fin n => (C w).1.role ≠ .Resetting) with hS
    have hsub : S ⊆ (Finset.univ.erase r) := by
      intro x hx
      have hx_not : (C x).1.role ≠ .Resetting := by
        rw [hS] at hx
        exact (Finset.mem_filter.mp hx).2
      have hx_ne_r : x ≠ r := by
        intro hxr
        subst x
        exact hx_not hr_res
      rw [Finset.mem_erase]
      exact ⟨hx_ne_r, Finset.mem_univ x⟩
    have hcard_le : S.card ≤ (Finset.univ.erase r).card := Finset.card_le_card hsub
    have hcard_erase : (Finset.univ.erase r).card = n - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ r)]
      simp
    unfold nonResettingCount
    rw [← hS]
    omega
  exact hrec (nonResettingCount C) C rfl hr_res hcount_lt_initial

theorem phase2_propagate_reset_with_leader
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 1 < Dmax)
    (C : Config (AgentState n) Opinion n)
    (hReset : ∃ r : Fin n, (C r).1.role = .Resetting ∧
      n ≤ (C r).1.resetcount ∧ (C r).1.leader = .L) :
    ∃ L : List (Fin n × Fin n),
      (∀ w : Fin n,
        (runPairs (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L w).1.role =
          .Resetting) ∧
      (∃ ℓ : Fin n,
        (runPairs (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L ℓ).1.leader =
          .L) := by
  classical
  rcases hReset with ⟨r, hr_res, hr_rc_ge, hr_leader⟩
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have hrec :
      ∀ k : ℕ, ∀ C₀ : Config (AgentState n) Opinion n,
        nonResettingCount C₀ = k →
        (C₀ r).1.role = .Resetting →
        (C₀ r).1.leader = .L →
        nonResettingCount C₀ < (C₀ r).1.resetcount →
        ∃ L : List (Fin n × Fin n),
          (∀ w : Fin n, (runPairs P C₀ L w).1.role = .Resetting) ∧
          (runPairs P C₀ L r).1.leader = .L := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro C₀ hcount hr_res₀ hr_leader₀ hcount_lt_rc
      by_cases hk0 : k = 0
      · refine ⟨[], ?_, ?_⟩
        · intro w
          simp only [runPairs_nil]
          by_contra hw_not
          have hw_mem :
              w ∈ Finset.univ.filter (fun x : Fin n => (C₀ x).1.role ≠ .Resetting) := by
            rw [Finset.mem_filter]
            exact ⟨Finset.mem_univ w, hw_not⟩
          have hpos :
              0 < (Finset.univ.filter
                (fun x : Fin n => (C₀ x).1.role ≠ .Resetting)).card :=
            Finset.card_pos.mpr ⟨w, hw_mem⟩
          unfold nonResettingCount at hcount
          omega
        · simp only [runPairs_nil]
          exact hr_leader₀
      · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
        have hcount_pos : 0 < nonResettingCount C₀ := by
          rw [hcount]
          exact hkpos
        obtain ⟨v, hv_mem⟩ : ∃ v : Fin n,
            v ∈ Finset.univ.filter (fun x : Fin n => (C₀ x).1.role ≠ .Resetting) := by
          exact Finset.card_pos.mp hcount_pos
        have hv_not : (C₀ v).1.role ≠ .Resetting :=
          (Finset.mem_filter.mp hv_mem).2
        have hrv : r ≠ v := by
          intro hrv_eq
          subst v
          exact hv_not hr_res₀
        have hr_rc_pos : 0 < (C₀ r).1.resetcount := by omega
        have hstep :=
          propagate_reset_step_nonResettingCount_lt
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            hDmax C₀ hrv hr_res₀ hr_rc_pos hv_not
        have htrace :=
          propagate_reset_spreader_state
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            hDmax C₀ hrv hr_res₀ hr_rc_pos hv_not
        set C₁ := C₀.step P r v with hC₁
        have hr_res₁ : (C₁ r).1.role = .Resetting := by
          rw [hC₁]
          exact hstep.1
        have hr_leader₁ : (C₁ r).1.leader = .L := by
          rw [hC₁]
          rw [htrace.2.2]
          exact hr_leader₀
        have hr_rc₁ : (C₁ r).1.resetcount = (C₀ r).1.resetcount - 1 := by
          rw [hC₁]
          exact hstep.2.1
        have hcount_lt : nonResettingCount C₁ < nonResettingCount C₀ := by
          rw [hC₁]
          exact hstep.2.2.2
        have hlt_k : nonResettingCount C₁ < k := by
          rw [← hcount]
          exact hcount_lt
        have hcount_lt_rc₁ : nonResettingCount C₁ < (C₁ r).1.resetcount := by
          rw [hr_rc₁]
          omega
        obtain ⟨Ltail, htail_roles, htail_leader⟩ :=
          ih (nonResettingCount C₁) hlt_k C₁ rfl hr_res₁ hr_leader₁ hcount_lt_rc₁
        refine ⟨(r, v) :: Ltail, ?_, ?_⟩
        · simpa [C₁, runPairs_cons] using htail_roles
        · simpa [C₁, runPairs_cons] using htail_leader
  have hcount_lt_initial : nonResettingCount C < (C r).1.resetcount := by
    set S := Finset.univ.filter (fun w : Fin n => (C w).1.role ≠ .Resetting) with hS
    have hsub : S ⊆ (Finset.univ.erase r) := by
      intro x hx
      have hx_not : (C x).1.role ≠ .Resetting := by
        rw [hS] at hx
        exact (Finset.mem_filter.mp hx).2
      have hx_ne_r : x ≠ r := by
        intro hxr
        subst x
        exact hx_not hr_res
      rw [Finset.mem_erase]
      exact ⟨hx_ne_r, Finset.mem_univ x⟩
    have hcard_le : S.card ≤ (Finset.univ.erase r).card := Finset.card_le_card hsub
    have hcard_erase : (Finset.univ.erase r).card = n - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ r)]
      simp
    unfold nonResettingCount
    rw [← hS]
    omega
  obtain ⟨L, hroles, hleader⟩ :=
    hrec (nonResettingCount C) C rfl hr_res hr_leader hcount_lt_initial
  exact ⟨L, hroles, ⟨r, hleader⟩⟩

theorem phase2_propagate_reset_with_leader_pos
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 1 < Dmax)
    (C : Config (AgentState n) Opinion n)
    (hReset : ∃ r : Fin n, (C r).1.role = .Resetting ∧
      n ≤ (C r).1.resetcount ∧ (C r).1.leader = .L)
    (hResetPos : ∀ w : Fin n, (C w).1.role = .Resetting → 0 < (C w).1.resetcount) :
    ∃ L : List (Fin n × Fin n),
      let C' := runPairs (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L
      (∀ w : Fin n, (C' w).1.role = .Resetting) ∧
      (∀ w : Fin n, 0 < (C' w).1.resetcount) ∧
      (∃ ℓ : Fin n, (C' ℓ).1.leader = .L) := by
  classical
  rcases hReset with ⟨r, hr_res, hr_rc_ge, hr_leader⟩
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have hrec :
      ∀ k : ℕ, ∀ C₀ : Config (AgentState n) Opinion n,
        nonResettingCount C₀ = k →
        (C₀ r).1.role = .Resetting →
        (C₀ r).1.leader = .L →
        (∀ w : Fin n, (C₀ w).1.role = .Resetting → 0 < (C₀ w).1.resetcount) →
        nonResettingCount C₀ < (C₀ r).1.resetcount →
        ∃ L : List (Fin n × Fin n),
          let C' := runPairs P C₀ L
          (∀ w : Fin n, (C' w).1.role = .Resetting) ∧
          (∀ w : Fin n, 0 < (C' w).1.resetcount) ∧
          (C' r).1.leader = .L := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro C₀ hcount hr_res₀ hr_leader₀ hPos₀ hcount_lt_rc
      by_cases hk0 : k = 0
      · refine ⟨[], ?_, ?_, ?_⟩
        · intro w
          simp only [runPairs_nil]
          by_contra hw_not
          have hw_mem :
              w ∈ Finset.univ.filter (fun x : Fin n => (C₀ x).1.role ≠ .Resetting) := by
            rw [Finset.mem_filter]
            exact ⟨Finset.mem_univ w, hw_not⟩
          have hpos :
              0 < (Finset.univ.filter
                (fun x : Fin n => (C₀ x).1.role ≠ .Resetting)).card :=
            Finset.card_pos.mpr ⟨w, hw_mem⟩
          unfold nonResettingCount at hcount
          omega
        · intro w
          simp only [runPairs_nil]
          have hw_res : (C₀ w).1.role = .Resetting := by
            by_contra hw_not
            have hw_mem :
                w ∈ Finset.univ.filter (fun x : Fin n => (C₀ x).1.role ≠ .Resetting) := by
              rw [Finset.mem_filter]
              exact ⟨Finset.mem_univ w, hw_not⟩
            have hpos :
                0 < (Finset.univ.filter
                  (fun x : Fin n => (C₀ x).1.role ≠ .Resetting)).card :=
              Finset.card_pos.mpr ⟨w, hw_mem⟩
            unfold nonResettingCount at hcount
            omega
          exact hPos₀ w hw_res
        · simp only [runPairs_nil]
          exact hr_leader₀
      · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
        have hcount_pos : 0 < nonResettingCount C₀ := by
          rw [hcount]
          exact hkpos
        obtain ⟨v, hv_mem⟩ : ∃ v : Fin n,
            v ∈ Finset.univ.filter (fun x : Fin n => (C₀ x).1.role ≠ .Resetting) := by
          exact Finset.card_pos.mp hcount_pos
        have hv_not : (C₀ v).1.role ≠ .Resetting :=
          (Finset.mem_filter.mp hv_mem).2
        have hrv : r ≠ v := by
          intro hrv_eq
          subst v
          exact hv_not hr_res₀
        have hr_rc_pos : 0 < (C₀ r).1.resetcount := hPos₀ r hr_res₀
        have hstep :=
          propagate_reset_step_nonResettingCount_lt
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            hDmax C₀ hrv hr_res₀ hr_rc_pos hv_not
        have htrace :=
          propagate_reset_spreader_state
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            hDmax C₀ hrv hr_res₀ hr_rc_pos hv_not
        set C₁ := C₀.step P r v with hC₁
        have hr_res₁ : (C₁ r).1.role = .Resetting := by
          rw [hC₁]
          exact hstep.1
        have hv_res₁ : (C₁ v).1.role = .Resetting := by
          rw [hC₁]
          exact hstep.2.2.1
        have hr_leader₁ : (C₁ r).1.leader = .L := by
          rw [hC₁]
          rw [htrace.2.2]
          exact hr_leader₀
        have hr_rc₁ : (C₁ r).1.resetcount = (C₀ r).1.resetcount - 1 := by
          rw [hC₁]
          exact hstep.2.1
        have hcount_lt : nonResettingCount C₁ < nonResettingCount C₀ := by
          rw [hC₁]
          exact hstep.2.2.2
        have hlt_k : nonResettingCount C₁ < k := by
          rw [← hcount]
          exact hcount_lt
        have hcount_lt_rc₁ : nonResettingCount C₁ < (C₁ r).1.resetcount := by
          rw [hr_rc₁]
          omega
        have hr_rc_pos₁ : 0 < (C₁ r).1.resetcount := by
          have hnonneg : 0 ≤ nonResettingCount C₁ := Nat.zero_le _
          exact Nat.lt_of_le_of_lt hnonneg hcount_lt_rc₁
        have hPos₁ : ∀ w : Fin n, (C₁ w).1.role = .Resetting → 0 < (C₁ w).1.resetcount := by
          intro w hw_res
          by_cases hwr : w = r
          · subst w
            exact hr_rc_pos₁
          · by_cases hwv : w = v
            · subst w
              have hv_rc_eq : (C₁ v).1.resetcount = (C₁ r).1.resetcount := by
                rw [hC₁]
                have hchild_rc :
                    (C₀.step P r v v).1.resetcount = (C₀ r).1.resetcount - 1 := by
                  set rankDelta := rankDeltaOSSR Rmax Emax Dmax hn
                  have h_rd_child :
                      (rankDelta ((C₀ r).1, (C₀ v).1)).2.resetcount =
                        (C₀ r).1.resetcount - 1 := by
                    unfold rankDelta rankDeltaOSSR propagateReset processAgent
                    by_cases hrc1 : (C₀ r).1.resetcount = 1
                    · simp [hr_res₀, hv_not, hrc1, resetOSSR,
                        show (Dmax : ℕ) ≠ 0 from by omega,
                        show Dmax - 1 ≠ 0 from by omega]
                      split_ifs <;> rfl
                    · have hne : (C₀ r).1.resetcount - 1 ≠ 0 := by omega
                      simp [hr_res₀, hr_rc_pos, hv_not, hne, resetOSSR,
                        show (Dmax : ℕ) ≠ 0 from by omega]
                      split_ifs <;> rfl
                  have h_not_both :
                      ¬((rankDelta ((C₀ r).1, (C₀ v).1)).1.role = .Settled ∧
                        (rankDelta ((C₀ r).1, (C₀ v).1)).2.role = .Settled) := by
                    intro hboth
                    have hchild_reset :
                        (rankDelta ((C₀ r).1, (C₀ v).1)).2.role = .Resetting := by
                      simpa [rankDelta] using
                        rankDeltaOSSR_propagate_reset
                          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
                          hr_res₀ hr_rc_pos hv_not hDmax
                    rw [hchild_reset] at hboth
                    exact Role.noConfusion hboth.2
                  have h_pass := transitionPEM_structural_passthrough
                    (n := n) (trank := Rmax) (Rmax := Rmax)
                    (rankDelta := rankDelta) (s₀ := (C₀ r).1) (s₁ := (C₀ v).1)
                    (x₀ := (C₀ r).2) (x₁ := (C₀ v).2) h_not_both
                  have h_snd := Config.step_snd_state P C₀ hrv hrv.symm
                  rw [congrArg AgentState.resetcount h_snd]
                  exact h_pass.2.2.2.2.2.2.2.2.2.2.1 ▸ h_rd_child
                rw [hchild_rc]
                exact hr_rc₁.symm
              rw [hv_rc_eq]
              exact hr_rc_pos₁
            · have hw_old : C₁ w = C₀ w := by
                rw [hC₁]
                simp [Config.step, hrv, hwr, hwv]
              have hw_old_res : (C₀ w).1.role = .Resetting := by
                rw [← hw_old]
                exact hw_res
              rw [hw_old]
              exact hPos₀ w hw_old_res
        obtain ⟨Ltail, htail_roles, htail_pos, htail_leader⟩ :=
          ih (nonResettingCount C₁) hlt_k C₁ rfl hr_res₁ hr_leader₁ hPos₁ hcount_lt_rc₁
        refine ⟨(r, v) :: Ltail, ?_⟩
        rw [runPairs_cons]
        change
          let C' := runPairs P C₁ Ltail
          (∀ w : Fin n, (C' w).1.role = .Resetting) ∧
          (∀ w : Fin n, 0 < (C' w).1.resetcount) ∧
          (C' r).1.leader = .L
        exact ⟨htail_roles, htail_pos, htail_leader⟩
  have hcount_lt_initial : nonResettingCount C < (C r).1.resetcount := by
    set S := Finset.univ.filter (fun w : Fin n => (C w).1.role ≠ .Resetting) with hS
    have hsub : S ⊆ (Finset.univ.erase r) := by
      intro x hx
      have hx_not : (C x).1.role ≠ .Resetting := by
        rw [hS] at hx
        exact (Finset.mem_filter.mp hx).2
      have hx_ne_r : x ≠ r := by
        intro hxr
        subst x
        exact hx_not hr_res
      rw [Finset.mem_erase]
      exact ⟨hx_ne_r, Finset.mem_univ x⟩
    have hcard_le : S.card ≤ (Finset.univ.erase r).card := Finset.card_le_card hsub
    have hcard_erase : (Finset.univ.erase r).card = n - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ r)]
      simp
    unfold nonResettingCount
    rw [← hS]
    omega
  obtain ⟨L, hroles, hpos, hleader⟩ :=
    hrec (nonResettingCount C) C rfl hr_res hr_leader hResetPos hcount_lt_initial
  exact ⟨L, hroles, hpos, ⟨r, hleader⟩⟩

theorem phase12_no_reset_to_all_resetting_or_InSrank
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (hRmax : n ≤ Rmax)
    (C : Config (AgentState n) Opinion n)
    (hNoReset : ∀ w : Fin n, (C w).1.role ≠ .Resetting) :
    ∃ L : List (Fin n × Fin n),
      let C' := runPairs (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L
      InSrank C' ∨ (∀ w : Fin n, (C' w).1.role = .Resetting) := by
  classical
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  obtain ⟨L₁, h₁⟩ :=
    phase1_no_reset_trigger_resetcount_or_InSrank
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hEmax hDmax C hNoReset
  let C₁ : Config (AgentState n) Opinion n := runPairs P C L₁
  rcases h₁ with hSrank | hReset
  · refine ⟨L₁, ?_⟩
    exact Or.inl hSrank
  · obtain ⟨r, hr_role, hr_rc⟩ := hReset
    have hDmax_gt_one : 1 < Dmax := by omega
    have hReset_phase2 : ∃ r : Fin n, (C₁ r).1.role = .Resetting ∧ n ≤ (C₁ r).1.resetcount := by
      refine ⟨r, ?_, ?_⟩
      · simpa [C₁, P] using hr_role
      · have hrc₁ : (C₁ r).1.resetcount = Rmax := by
          simpa [C₁, P] using hr_rc
        rw [hrc₁]
        exact hRmax
    obtain ⟨L₂, h₂⟩ :=
      phase2_propagate_reset
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hDmax_gt_one C₁ hReset_phase2
    refine ⟨L₁ ++ L₂, ?_⟩
    rw [runPairs_append]
    change InSrank (runPairs P C₁ L₂) ∨
      (∀ w : Fin n, (runPairs P C₁ L₂ w).1.role = .Resetting)
    exact Or.inr h₂

theorem phase12_no_reset_to_all_resetting_with_leader_or_InSrank
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (hRmax : n ≤ Rmax)
    (C : Config (AgentState n) Opinion n)
    (hNoReset : ∀ w : Fin n, (C w).1.role ≠ .Resetting) :
    ∃ L : List (Fin n × Fin n),
      let C' := runPairs (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L
      InSrank C' ∨
        ((∀ w : Fin n, (C' w).1.role = .Resetting) ∧
          ∃ ℓ : Fin n, (C' ℓ).1.leader = .L) := by
  classical
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  obtain ⟨L₁, h₁⟩ :=
    phase1_no_reset_trigger_resetcount_leader_or_InSrank
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hEmax hDmax C hNoReset
  let C₁ : Config (AgentState n) Opinion n := runPairs P C L₁
  rcases h₁ with hSrank | hReset
  · refine ⟨L₁, ?_⟩
    exact Or.inl hSrank
  · obtain ⟨r, hr_role, hr_rc, hr_leader⟩ := hReset
    have hDmax_gt_one : 1 < Dmax := by omega
    have hReset_phase2 : ∃ r : Fin n, (C₁ r).1.role = .Resetting ∧
        n ≤ (C₁ r).1.resetcount ∧ (C₁ r).1.leader = .L := by
      refine ⟨r, ?_, ?_, ?_⟩
      · simpa [C₁, P] using hr_role
      · have hrc₁ : (C₁ r).1.resetcount = Rmax := by
          simpa [C₁, P] using hr_rc
        rw [hrc₁]
        exact hRmax
      · simpa [C₁, P] using hr_leader
    obtain ⟨L₂, hroles, hleader⟩ :=
      phase2_propagate_reset_with_leader
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hDmax_gt_one C₁ hReset_phase2
    refine ⟨L₁ ++ L₂, ?_⟩
    rw [runPairs_append]
    change InSrank (runPairs P C₁ L₂) ∨
      ((∀ w : Fin n, (runPairs P C₁ L₂ w).1.role = .Resetting) ∧
        ∃ ℓ : Fin n, (runPairs P C₁ L₂ ℓ).1.leader = .L)
    exact Or.inr ⟨hroles, hleader⟩

theorem phase12_no_reset_to_all_resetting_pos_with_leader_or_InSrank
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (hRmax : n ≤ Rmax)
    (C : Config (AgentState n) Opinion n)
    (hNoReset : ∀ w : Fin n, (C w).1.role ≠ .Resetting) :
    ∃ L : List (Fin n × Fin n),
      let C' := runPairs (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L
      InSrank C' ∨
        ((∀ w : Fin n, (C' w).1.role = .Resetting) ∧
          (∀ w : Fin n, 0 < (C' w).1.resetcount) ∧
          ∃ ℓ : Fin n, (C' ℓ).1.leader = .L) := by
  classical
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  obtain ⟨L₁, h₁⟩ :=
    phase1_no_reset_trigger_snapshot_or_InSrank
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hEmax hDmax C hNoReset
  let C₁ : Config (AgentState n) Opinion n := runPairs P C L₁
  rcases h₁ with hSrank | hReset
  · refine ⟨L₁, ?_⟩
    exact Or.inl hSrank
  · obtain ⟨r, hr_role, hr_rc, hr_leader, hSnapshot⟩ := hReset
    have hDmax_gt_one : 1 < Dmax := by omega
    have hReset_phase2 : ∃ r : Fin n, (C₁ r).1.role = .Resetting ∧
        n ≤ (C₁ r).1.resetcount ∧ (C₁ r).1.leader = .L := by
      refine ⟨r, ?_, ?_, ?_⟩
      · simpa [C₁, P] using hr_role
      · have hrc₁ : (C₁ r).1.resetcount = Rmax := by
          simpa [C₁, P] using hr_rc
        rw [hrc₁]
        exact hRmax
      · simpa [C₁, P] using hr_leader
    have hResetPos₁ : ∀ w : Fin n, (C₁ w).1.role = .Resetting → 0 < (C₁ w).1.resetcount := by
      intro w hw
      have hfields := hSnapshot w (by simpa [C₁, P] using hw)
      have hrc : (C₁ w).1.resetcount = Rmax := by
        simpa [C₁, P] using hfields.1
      rw [hrc]
      have hn_pos : 0 < n := Nat.lt_of_lt_of_le (by omega : 0 < 4) hn4
      exact Nat.lt_of_lt_of_le hn_pos hRmax
    obtain ⟨L₂, hroles, hpos, hleader⟩ :=
      phase2_propagate_reset_with_leader_pos
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hDmax_gt_one C₁ hReset_phase2 hResetPos₁
    refine ⟨L₁ ++ L₂, ?_⟩
    rw [runPairs_append]
    change InSrank (runPairs P C₁ L₂) ∨
      ((∀ w : Fin n, (runPairs P C₁ L₂ w).1.role = .Resetting) ∧
        (∀ w : Fin n, 0 < (runPairs P C₁ L₂ w).1.resetcount) ∧
        ∃ ℓ : Fin n, (runPairs P C₁ L₂ ℓ).1.leader = .L)
    exact Or.inr ⟨hroles, hpos, hleader⟩

/- From all-Resetting (with leader + sufficient Rmax/Dmax), reach IsDormantConfig.
This requires: (1) resetcount countdown via sync, (2) leader deduplication,
(3) delaytimer irrelevant (IsDormantConfig doesn't require dt=0). -/

/-- Strong endpoint for Phase 2: once all agents are Resetting, all resetcounts
are zero, and there is a unique leader, the empty schedule is already dormant. -/
theorem all_resetting_zero_unique_to_dormant
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (C : Config (AgentState n) Opinion n)
    (hAllReset : ∀ w : Fin n, (C w).1.role = .Resetting)
    (hAllRc0 : ∀ w : Fin n, (C w).1.resetcount = 0)
    (hUniqueLeader : ∃! ℓ : Fin n, (C ℓ).1.leader = .L) :
    ∃ L : List (Fin n × Fin n),
      IsDormantConfig
        (runPairs (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L) := by
  refine ⟨[], ?_⟩
  simp only [runPairs_nil]
  refine ⟨hAllReset, hAllRc0, hUniqueLeader, ?_⟩
  intro w
  cases (C w).1.leader <;> simp

/-- Post-Phase-2 strong version of `all_resetting_to_dormant`. The remaining
work for the weak theorem is to prove schedules that establish `hAllRc0` and
`hUniqueLeader`; this lemma composes those facts into `IsDormantConfig`. -/
theorem all_resetting_to_dormant_post_phase2
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (C : Config (AgentState n) Opinion n)
    (hAllReset : ∀ w : Fin n, (C w).1.role = .Resetting)
    (hAllRc0 : ∀ w : Fin n, (C w).1.resetcount = 0)
    (hUniqueLeader : ∃! ℓ : Fin n, (C ℓ).1.leader = .L) :
    ∃ L : List (Fin n × Fin n),
      IsDormantConfig
        (runPairs (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L) :=
  all_resetting_zero_unique_to_dormant (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
    (hn := hn) C hAllReset hAllRc0 hUniqueLeader

/-- Schedule-level composition for Phase 2. Once some finite schedule reaches
the post-Phase-2 facts, it is already a witness for `IsDormantConfig`. -/
theorem all_resetting_to_dormant_from_phase2_schedule
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (C : Config (AgentState n) Opinion n)
    (hPhase2 : ∃ L₀ : List (Fin n × Fin n),
      let C' := runPairs (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L₀
      (∀ w : Fin n, (C' w).1.role = .Resetting) ∧
      (∀ w : Fin n, (C' w).1.resetcount = 0) ∧
      (∃! ℓ : Fin n, (C' ℓ).1.leader = .L)) :
    ∃ L : List (Fin n × Fin n),
      IsDormantConfig
        (runPairs (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L) := by
  obtain ⟨L₀, hAllReset, hAllRc0, hUniqueLeader⟩ := hPhase2
  refine ⟨L₀, ?_⟩
  refine ⟨hAllReset, hAllRc0, hUniqueLeader, ?_⟩
  intro w
  cases (runPairs (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L₀ w).1.leader <;>
    simp

set_option maxHeartbeats 400000000 in
/-- When two Resetting agents with rc > 0 interact with Dmax > 0, both stay Resetting.
(The rc sync may reach 0, but dt is set to Dmax, preventing premature waking.) -/
theorem propagateReset_both_rc_pos_stay
    {Emax Dmax : ℕ} {hn : 0 < n}
    {s t : AgentState n}
    (hs : s.role = .Resetting) (ht : t.role = .Resetting)
    (hs_rc : 0 < s.resetcount) (ht_rc : 0 < t.resetcount)
    (hDmax : 0 < Dmax) :
    (propagateReset Emax Dmax hn s t).1.role = .Resetting ∧
    (propagateReset Emax Dmax hn s t).2.role = .Resetting := by
  unfold propagateReset
  dsimp only []
  simp only [hs, ht, hs_rc, ht_rc,
    show ¬(t.role ≠ .Resetting) from not_not.mpr ht,
    show ¬(s.role ≠ .Resetting) from not_not.mpr hs,
    show ¬(t.role = .Resetting ∧ 0 < t.resetcount ∧ s.role ≠ .Resetting) from
      fun ⟨_, _, h⟩ => h hs,
    show ¬(Role.Resetting ≠ .Resetting) from not_not.mpr rfl,
    show (Role.Resetting == Role.Resetting) = true from rfl,
    and_true, and_false, ite_false, and_self, ite_true, true_and, not_true]
  set M := Nat.max (s.resetcount - 1) (t.resetcount - 1) with hM
  by_cases hM0 : M = 0
  · constructor
    · show (processAgent Emax Dmax hn ⟨.Resetting, s.rank, s.leader, M, s.answer, s.timer,
        s.children, s.errorcount, s.delaytimer⟩ s.resetcount true).role = .Resetting
      rw [hM0]; exact processAgent_dormant_fresh_stays rfl rfl hs_rc hDmax rfl
    · show (processAgent Emax Dmax hn ⟨.Resetting, t.rank, t.leader, M, t.answer, t.timer,
        t.children, t.errorcount, t.delaytimer⟩ t.resetcount true).role = .Resetting
      rw [hM0]; exact processAgent_dormant_fresh_stays rfl rfl ht_rc hDmax rfl
  · constructor
    · show (processAgent Emax Dmax hn ⟨.Resetting, s.rank, s.leader, M, s.answer, s.timer,
        s.children, s.errorcount, s.delaytimer⟩ s.resetcount true).role = .Resetting
      rw [processAgent_rc_ne_zero hM0]
    · show (processAgent Emax Dmax hn ⟨.Resetting, t.rank, t.leader, M, t.answer, t.timer,
        t.children, t.errorcount, t.delaytimer⟩ t.resetcount true).role = .Resetting
      rw [processAgent_rc_ne_zero hM0]

set_option maxHeartbeats 400000000 in
/-- Strong trace for `propagateReset` when both inputs are Resetting with rc > 0.
Both stay Resetting AND both new rc equal `max(s.rc - 1, t.rc - 1)`. -/
theorem propagateReset_both_rc_pos_rc
    {Emax Dmax : ℕ} {hn : 0 < n}
    {s t : AgentState n}
    (hs : s.role = .Resetting) (ht : t.role = .Resetting)
    (hs_rc : 0 < s.resetcount) (ht_rc : 0 < t.resetcount)
    (hDmax : 0 < Dmax) :
    (propagateReset Emax Dmax hn s t).1.resetcount =
        Nat.max (s.resetcount - 1) (t.resetcount - 1) ∧
    (propagateReset Emax Dmax hn s t).2.resetcount =
        Nat.max (s.resetcount - 1) (t.resetcount - 1) := by
  unfold propagateReset
  dsimp only []
  simp only [hs, ht, hs_rc, ht_rc,
    show ¬(t.role ≠ .Resetting) from not_not.mpr ht,
    show ¬(s.role ≠ .Resetting) from not_not.mpr hs,
    show ¬(t.role = .Resetting ∧ 0 < t.resetcount ∧ s.role ≠ .Resetting) from
      fun ⟨_, _, h⟩ => h hs,
    show ¬(Role.Resetting ≠ .Resetting) from not_not.mpr rfl,
    show (Role.Resetting == Role.Resetting) = true from rfl,
    and_true, and_false, ite_false, and_self, ite_true, true_and, not_true]
  set M := Nat.max (s.resetcount - 1) (t.resetcount - 1) with hM
  by_cases hM0 : M = 0
  · constructor
    · show (processAgent Emax Dmax hn ⟨.Resetting, s.rank, s.leader, M, s.answer, s.timer,
        s.children, s.errorcount, s.delaytimer⟩ s.resetcount true).resetcount = M
      rw [hM0]
      exact processAgent_dormant_fresh_keeps_rc rfl rfl hs_rc hDmax rfl
    · show (processAgent Emax Dmax hn ⟨.Resetting, t.rank, t.leader, M, t.answer, t.timer,
        t.children, t.errorcount, t.delaytimer⟩ t.resetcount true).resetcount = M
      rw [hM0]
      exact processAgent_dormant_fresh_keeps_rc rfl rfl ht_rc hDmax rfl
  · constructor
    · show (processAgent Emax Dmax hn ⟨.Resetting, s.rank, s.leader, M, s.answer, s.timer,
        s.children, s.errorcount, s.delaytimer⟩ s.resetcount true).resetcount = M
      rw [processAgent_rc_ne_zero hM0]
    · show (processAgent Emax Dmax hn ⟨.Resetting, t.rank, t.leader, M, t.answer, t.timer,
        t.children, t.errorcount, t.delaytimer⟩ t.resetcount true).resetcount = M
      rw [processAgent_rc_ne_zero hM0]

/-- First endpoint's leader is preserved through propagateReset when both
inputs are Resetting with rc > 0. -/
theorem propagateReset_both_rc_pos_leader_fst
    {Emax Dmax : ℕ} {hn : 0 < n}
    {s t : AgentState n}
    (hs : s.role = .Resetting) (ht : t.role = .Resetting)
    (hs_rc : 0 < s.resetcount) (ht_rc : 0 < t.resetcount)
    (hDmax : 0 < Dmax) :
    (propagateReset Emax Dmax hn s t).1.leader = s.leader := by
  unfold propagateReset
  dsimp only []
  simp only [hs, ht, hs_rc, ht_rc,
    show ¬(t.role ≠ .Resetting) from not_not.mpr ht,
    show ¬(s.role ≠ .Resetting) from not_not.mpr hs,
    show ¬(t.role = .Resetting ∧ 0 < t.resetcount ∧ s.role ≠ .Resetting) from
      fun ⟨_, _, h⟩ => h hs,
    show ¬(Role.Resetting ≠ .Resetting) from not_not.mpr rfl,
    show (Role.Resetting == Role.Resetting) = true from rfl,
    and_true, and_false, ite_false, and_self, ite_true, true_and, not_true]
  set M := Nat.max (s.resetcount - 1) (t.resetcount - 1) with hM
  by_cases hM0 : M = 0
  · show (processAgent Emax Dmax hn ⟨.Resetting, s.rank, s.leader, M, s.answer, s.timer,
        s.children, s.errorcount, s.delaytimer⟩ s.resetcount true).leader = s.leader
    rw [hM0]
    exact processAgent_dormant_fresh_keeps_leader rfl rfl hs_rc hDmax rfl
  · show (processAgent Emax Dmax hn ⟨.Resetting, s.rank, s.leader, M, s.answer, s.timer,
        s.children, s.errorcount, s.delaytimer⟩ s.resetcount true).leader = s.leader
    rw [processAgent_rc_ne_zero hM0]

theorem propagateReset_both_rc_pos_leader_snd
    {Emax Dmax : ℕ} {hn : 0 < n}
    {s t : AgentState n}
    (hs : s.role = .Resetting) (ht : t.role = .Resetting)
    (hs_rc : 0 < s.resetcount) (ht_rc : 0 < t.resetcount)
    (hDmax : 0 < Dmax) :
    (propagateReset Emax Dmax hn s t).2.leader = t.leader := by
  unfold propagateReset
  dsimp only []
  simp only [hs, ht, hs_rc, ht_rc,
    show ¬(t.role ≠ .Resetting) from not_not.mpr ht,
    show ¬(s.role ≠ .Resetting) from not_not.mpr hs,
    show ¬(t.role = .Resetting ∧ 0 < t.resetcount ∧ s.role ≠ .Resetting) from
      fun ⟨_, _, h⟩ => h hs,
    show ¬(Role.Resetting ≠ .Resetting) from not_not.mpr rfl,
    show (Role.Resetting == Role.Resetting) = true from rfl,
    and_true, and_false, ite_false, and_self, ite_true, true_and, not_true]
  set M := Nat.max (s.resetcount - 1) (t.resetcount - 1) with hM
  by_cases hM0 : M = 0
  · show (processAgent Emax Dmax hn ⟨.Resetting, t.rank, t.leader, M, t.answer, t.timer,
        t.children, t.errorcount, t.delaytimer⟩ t.resetcount true).leader = t.leader
    rw [hM0]
    exact processAgent_dormant_fresh_keeps_leader rfl rfl ht_rc hDmax rfl
  · show (processAgent Emax Dmax hn ⟨.Resetting, t.rank, t.leader, M, t.answer, t.timer,
        t.children, t.errorcount, t.delaytimer⟩ t.resetcount true).leader = t.leader
    rw [processAgent_rc_ne_zero hM0]

/-- Lift of `propagateReset_both_rc_pos_stay` through `rankDeltaOSSR`'s leader
dedup wrapper. The dedup only touches `.leader` of the second agent (when both
are L); roles and resetcounts are unchanged. -/
theorem rankDeltaOSSR_both_rc_pos_role
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {s t : AgentState n}
    (hs : s.role = .Resetting) (ht : t.role = .Resetting)
    (hs_rc : 0 < s.resetcount) (ht_rc : 0 < t.resetcount)
    (hDmax : 0 < Dmax) :
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.role = .Resetting ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.role = .Resetting ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.resetcount =
        Nat.max (s.resetcount - 1) (t.resetcount - 1) ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.resetcount =
        Nat.max (s.resetcount - 1) (t.resetcount - 1) ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.leader = s.leader := by
  unfold rankDeltaOSSR
  simp only [hs, true_or, ite_true]
  have h_role := propagateReset_both_rc_pos_stay (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hs ht hs_rc ht_rc hDmax
  have h_rc := propagateReset_both_rc_pos_rc (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hs ht hs_rc ht_rc hDmax
  have h_leader := propagateReset_both_rc_pos_leader_fst (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hs ht hs_rc ht_rc hDmax
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact h_role.1
  · split_ifs <;> exact h_role.2
  · exact h_rc.1
  · split_ifs <;> exact h_rc.2
  · exact h_leader

theorem rankDeltaOSSR_both_rc_pos_LF_trace
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {s t : AgentState n}
    (hs : s.role = .Resetting) (ht : t.role = .Resetting)
    (hs_rc : 0 < s.resetcount) (ht_rc : 0 < t.resetcount)
    (hs_L : s.leader = .L) (ht_F : t.leader = .F)
    (hDmax : 0 < Dmax) :
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.role = .Resetting ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.role = .Resetting ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.resetcount =
        Nat.max (s.resetcount - 1) (t.resetcount - 1) ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.resetcount =
        Nat.max (s.resetcount - 1) (t.resetcount - 1) ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.leader = .L ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.leader = .F := by
  unfold rankDeltaOSSR
  simp only [hs, true_or, ite_true]
  have h_role := propagateReset_both_rc_pos_stay (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hs ht hs_rc ht_rc hDmax
  have h_rc := propagateReset_both_rc_pos_rc (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hs ht hs_rc ht_rc hDmax
  have h_leader₁ := propagateReset_both_rc_pos_leader_fst (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hs ht hs_rc ht_rc hDmax
  have h_leader₂ := propagateReset_both_rc_pos_leader_snd (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hs ht hs_rc ht_rc hDmax
  have hnot_dedup :
      ¬((propagateReset Emax Dmax hn s t).1.leader = .L ∧
        (propagateReset Emax Dmax hn s t).2.leader = .L ∧
        (propagateReset Emax Dmax hn s t).1.role = .Resetting ∧
        (propagateReset Emax Dmax hn s t).2.role = .Resetting) := by
    intro h
    have hF : (propagateReset Emax Dmax hn s t).2.leader = .F := by
      rw [h_leader₂, ht_F]
    rw [h.2.1] at hF
    cases hF
  simp [hnot_dedup]
  exact ⟨h_role.1, h_role.2, h_rc.1, h_rc.2,
    by rw [h_leader₁, hs_L], by rw [h_leader₂, ht_F]⟩

theorem rankDeltaOSSR_both_rc_pos_FF_trace
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {s t : AgentState n}
    (hs : s.role = .Resetting) (ht : t.role = .Resetting)
    (hs_rc : 0 < s.resetcount) (ht_rc : 0 < t.resetcount)
    (hs_F : s.leader = .F) (ht_F : t.leader = .F)
    (hDmax : 0 < Dmax) :
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.role = .Resetting ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.role = .Resetting ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.resetcount =
        Nat.max (s.resetcount - 1) (t.resetcount - 1) ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.resetcount =
        Nat.max (s.resetcount - 1) (t.resetcount - 1) ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.leader = .F ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.leader = .F := by
  unfold rankDeltaOSSR
  simp only [hs, true_or, ite_true]
  have h_role := propagateReset_both_rc_pos_stay (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hs ht hs_rc ht_rc hDmax
  have h_rc := propagateReset_both_rc_pos_rc (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hs ht hs_rc ht_rc hDmax
  have h_leader₁ := propagateReset_both_rc_pos_leader_fst (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hs ht hs_rc ht_rc hDmax
  have h_leader₂ := propagateReset_both_rc_pos_leader_snd (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hs ht hs_rc ht_rc hDmax
  have hnot_dedup :
      ¬((propagateReset Emax Dmax hn s t).1.leader = .L ∧
        (propagateReset Emax Dmax hn s t).2.leader = .L ∧
        (propagateReset Emax Dmax hn s t).1.role = .Resetting ∧
        (propagateReset Emax Dmax hn s t).2.role = .Resetting) := by
    intro h
    have hF : (propagateReset Emax Dmax hn s t).1.leader = .F := by
      rw [h_leader₁, hs_F]
    rw [h.1] at hF
    cases hF
  simp [hnot_dedup]
  exact ⟨h_role.1, h_role.2, h_rc.1, h_rc.2,
    by rw [h_leader₁, hs_F], by rw [h_leader₂, ht_F]⟩

theorem rankDeltaOSSR_both_rc_pos_LL_trace
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {s t : AgentState n}
    (hs : s.role = .Resetting) (ht : t.role = .Resetting)
    (hs_rc : 0 < s.resetcount) (ht_rc : 0 < t.resetcount)
    (hs_L : s.leader = .L) (ht_L : t.leader = .L)
    (hDmax : 0 < Dmax) :
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.role = .Resetting ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.role = .Resetting ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.resetcount =
        Nat.max (s.resetcount - 1) (t.resetcount - 1) ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.resetcount =
        Nat.max (s.resetcount - 1) (t.resetcount - 1) ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.leader = .L ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.leader = .F := by
  unfold rankDeltaOSSR
  simp only [hs, true_or, ite_true]
  have h_role := propagateReset_both_rc_pos_stay (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hs ht hs_rc ht_rc hDmax
  have h_rc := propagateReset_both_rc_pos_rc (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hs ht hs_rc ht_rc hDmax
  have h_leader₁ := propagateReset_both_rc_pos_leader_fst (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hs ht hs_rc ht_rc hDmax
  have h_leader₂ := propagateReset_both_rc_pos_leader_snd (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hs ht hs_rc ht_rc hDmax
  have hdedup :
      (propagateReset Emax Dmax hn s t).1.leader = .L ∧
        (propagateReset Emax Dmax hn s t).2.leader = .L ∧
        (propagateReset Emax Dmax hn s t).1.role = .Resetting ∧
        (propagateReset Emax Dmax hn s t).2.role = .Resetting := by
    exact ⟨by rw [h_leader₁, hs_L], by rw [h_leader₂, ht_L], h_role.1, h_role.2⟩
  simp [hdedup]
  exact ⟨h_rc.1, h_rc.2⟩

theorem rankDeltaOSSR_both_rc_pos_fst_delay_final
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {s t : AgentState n}
    (hs : s.role = .Resetting) (ht : t.role = .Resetting)
    (hs_rc : 0 < s.resetcount) (ht_rc : 0 < t.resetcount)
    (hnew : Nat.max (s.resetcount - 1) (t.resetcount - 1) = 0)
    (hDmax : 0 < Dmax) :
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.delaytimer = Dmax := by
  unfold rankDeltaOSSR propagateReset processAgent resetOSSR
  simp [hs, ht, hs_rc, ht_rc, hnew, show (Dmax : ℕ) ≠ 0 from by omega]

theorem rankDeltaOSSR_L_pos_F_zero_trace
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {s t : AgentState n}
    (hs : s.role = .Resetting) (ht : t.role = .Resetting)
    (hs_rc : 0 < s.resetcount) (ht_rc : t.resetcount = 0)
    (hs_L : s.leader = .L) (ht_F : t.leader = .F)
    (ht_dt : 1 < t.delaytimer)
    (hDmax : 0 < Dmax) :
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.role = .Resetting ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.role = .Resetting ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.resetcount = s.resetcount - 1 ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.resetcount = s.resetcount - 1 ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.leader = .L ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.leader = .F ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.delaytimer =
      (if s.resetcount = 1 then t.delaytimer - 1 else t.delaytimer) := by
  unfold rankDeltaOSSR propagateReset processAgent resetOSSR
  by_cases hs_one : s.resetcount = 1
  · have hnew : max (s.resetcount - 1) (0 - 1) = 0 := by omega
    have ht_dt_ne : t.delaytimer - 1 ≠ 0 := by omega
    simp [hs, ht, hs_rc, ht_rc, hs_L, ht_F, hs_one, hnew, ht_dt_ne,
      show (Dmax : ℕ) ≠ 0 from by omega]
  · have hs_pred_ne : s.resetcount - 1 ≠ 0 := by omega
    have hnew : max (s.resetcount - 1) (0 - 1) = s.resetcount - 1 := by omega
    simp [hs, ht, hs_rc, ht_rc, hs_L, ht_F, hs_one, hs_pred_ne, hnew]

theorem rankDeltaOSSR_L_pos_L_zero_trace
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {s t : AgentState n}
    (hs : s.role = .Resetting) (ht : t.role = .Resetting)
    (hs_rc : 0 < s.resetcount) (ht_rc : t.resetcount = 0)
    (hs_L : s.leader = .L) (ht_L : t.leader = .L)
    (ht_dt : 1 < t.delaytimer)
    (hDmax : 0 < Dmax) :
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.role = .Resetting ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.role = .Resetting ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.resetcount = s.resetcount - 1 ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.resetcount = s.resetcount - 1 ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.leader = .L ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.leader = .F ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.delaytimer =
      (if s.resetcount = 1 then t.delaytimer - 1 else t.delaytimer) := by
  unfold rankDeltaOSSR propagateReset processAgent resetOSSR
  by_cases hs_one : s.resetcount = 1
  · have hnew : max (s.resetcount - 1) (0 - 1) = 0 := by omega
    have ht_dt_ne : t.delaytimer - 1 ≠ 0 := by omega
    simp [hs, ht, hs_rc, ht_rc, hs_L, ht_L, hs_one, hnew, ht_dt_ne,
      show (Dmax : ℕ) ≠ 0 from by omega]
  · have hs_pred_ne : s.resetcount - 1 ≠ 0 := by omega
    have hnew : max (s.resetcount - 1) (0 - 1) = s.resetcount - 1 := by omega
    simp [hs, ht, hs_rc, ht_rc, hs_L, ht_L, hs_one, hs_pred_ne, hnew]

theorem rankDeltaOSSR_F_pos_F_zero_trace
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {s t : AgentState n}
    (hs : s.role = .Resetting) (ht : t.role = .Resetting)
    (hs_rc : 0 < s.resetcount) (ht_rc : t.resetcount = 0)
    (hs_F : s.leader = .F) (ht_F : t.leader = .F)
    (ht_dt : 1 < t.delaytimer)
    (hDmax : 0 < Dmax) :
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.role = .Resetting ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.role = .Resetting ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.resetcount = s.resetcount - 1 ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.resetcount = s.resetcount - 1 ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.leader = .F ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.leader = .F := by
  unfold rankDeltaOSSR propagateReset processAgent resetOSSR
  by_cases hs_one : s.resetcount = 1
  · have hnew : max (s.resetcount - 1) (0 - 1) = 0 := by omega
    have ht_dt_ne : t.delaytimer - 1 ≠ 0 := by omega
    simp [hs, ht, hs_rc, ht_rc, hs_F, ht_F, hs_one, hnew, ht_dt_ne,
      show (Dmax : ℕ) ≠ 0 from by omega]
  · have hs_pred_ne : s.resetcount - 1 ≠ 0 := by omega
    have hnew : max (s.resetcount - 1) (0 - 1) = s.resetcount - 1 := by omega
    simp [hs, ht, hs_rc, ht_rc, hs_F, ht_F, hs_one, hs_pred_ne, hnew]

theorem rankDeltaOSSR_L_pos_any_zero_gt_one_trace
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {s t : AgentState n}
    (hs : s.role = .Resetting) (ht : t.role = .Resetting)
    (hs_rc : 1 < s.resetcount) (ht_rc : t.resetcount = 0)
    (hs_L : s.leader = .L) :
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.role = .Resetting ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.role = .Resetting ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.resetcount = s.resetcount - 1 ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.resetcount = s.resetcount - 1 ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.leader = .L ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.leader = .F := by
  have hnew : max (s.resetcount - 1) (0 - 1) = s.resetcount - 1 := by omega
  have hs_pred_ne : s.resetcount - 1 ≠ 0 := by omega
  cases ht_leader : t.leader <;>
    unfold rankDeltaOSSR propagateReset processAgent resetOSSR <;>
    simp [hs, ht, ht_rc, hs_L, ht_leader, hnew, hs_pred_ne]

theorem rankDeltaOSSR_F_pos_F_zero_gt_one_trace
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {s t : AgentState n}
    (hs : s.role = .Resetting) (ht : t.role = .Resetting)
    (hs_rc : 1 < s.resetcount) (ht_rc : t.resetcount = 0)
    (hs_F : s.leader = .F) (ht_F : t.leader = .F) :
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.role = .Resetting ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.role = .Resetting ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.resetcount = s.resetcount - 1 ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.resetcount = s.resetcount - 1 ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.leader = .F ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.leader = .F := by
  have hnew : max (s.resetcount - 1) (0 - 1) = s.resetcount - 1 := by omega
  have hs_pred_ne : s.resetcount - 1 ≠ 0 := by omega
  unfold rankDeltaOSSR propagateReset processAgent resetOSSR
  simp [hs, ht, ht_rc, hs_F, ht_F, hnew, hs_pred_ne]

theorem rankDeltaOSSR_L_pos_one_F_zero_low_trace
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {s t : AgentState n}
    (hs : s.role = .Resetting) (ht : t.role = .Resetting)
    (hs_rc : s.resetcount = 1) (ht_rc : t.resetcount = 0)
    (hs_L : s.leader = .L) (ht_F : t.leader = .F)
    (ht_low : t.delaytimer ≤ 1) (hDmax : 0 < Dmax) :
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.role = .Resetting ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.resetcount = 0 ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.leader = .L ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.delaytimer = Dmax ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.role = .Unsettled ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.leader = .F := by
  have hnew : max (s.resetcount - 1) (0 - 1) = 0 := by omega
  have ht_dt_zero : t.delaytimer - 1 = 0 := by omega
  unfold rankDeltaOSSR propagateReset processAgent resetOSSR
  simp [hs, ht, hs_rc, ht_rc, hs_L, ht_F, hnew, ht_dt_zero,
    show (Dmax : ℕ) ≠ 0 from by omega]

theorem rankDeltaOSSR_L_pos_one_L_zero_low_trace
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {s t : AgentState n}
    (hs : s.role = .Resetting) (ht : t.role = .Resetting)
    (hs_rc : s.resetcount = 1) (ht_rc : t.resetcount = 0)
    (hs_L : s.leader = .L) (ht_L : t.leader = .L)
    (ht_low : t.delaytimer ≤ 1) (hDmax : 0 < Dmax) :
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.role = .Resetting ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.resetcount = 0 ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.leader = .L ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.delaytimer = Dmax ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.role = .Settled ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.rank = ⟨0, hn⟩ ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.children = 0 ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.leader = .L := by
  have hnew : max (s.resetcount - 1) (0 - 1) = 0 := by omega
  have ht_dt_zero : t.delaytimer - 1 = 0 := by omega
  unfold rankDeltaOSSR propagateReset processAgent resetOSSR
  simp [hs, ht, hs_rc, ht_rc, hs_L, ht_L, hnew, ht_dt_zero,
    show (Dmax : ℕ) ≠ 0 from by omega]

theorem rankDeltaOSSR_F_pos_one_F_zero_low_trace
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {s t : AgentState n}
    (hs : s.role = .Resetting) (ht : t.role = .Resetting)
    (hs_rc : s.resetcount = 1) (ht_rc : t.resetcount = 0)
    (hs_F : s.leader = .F) (ht_F : t.leader = .F)
    (ht_low : t.delaytimer ≤ 1) (hDmax : 0 < Dmax) :
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.role = .Resetting ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.resetcount = 0 ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.leader = .F ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.delaytimer = Dmax ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.role = .Unsettled ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.leader = .F := by
  have hnew : max (s.resetcount - 1) (0 - 1) = 0 := by omega
  have ht_dt_zero : t.delaytimer - 1 = 0 := by omega
  unfold rankDeltaOSSR propagateReset processAgent resetOSSR
  simp [hs, ht, hs_rc, ht_rc, hs_F, ht_F, hnew, ht_dt_zero,
    show (Dmax : ℕ) ≠ 0 from by omega]

theorem rankDeltaOSSR_F_pos_one_settled_L_trace
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {s t : AgentState n}
    (hs : s.role = .Resetting) (ht : t.role = .Settled)
    (hs_rc : s.resetcount = 1)
    (hs_F : s.leader = .F) (ht_L : t.leader = .L)
    (hDmax : 1 < Dmax) :
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.role = .Resetting ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.resetcount = 0 ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.leader = .F ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.role = .Resetting ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.resetcount = 0 ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.leader = .L ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.delaytimer = Dmax - 1 := by
  have hnew : max (s.resetcount - 1) (0 - 1) = 0 := by omega
  have hDmax_pred_ne : Dmax - 1 ≠ 0 := by omega
  unfold rankDeltaOSSR propagateReset processAgent resetOSSR
  simp [hs, ht, hs_rc, hs_F, ht_L, hnew, hDmax_pred_ne,
    show (Dmax : ℕ) ≠ 0 from by omega]

theorem rankDeltaOSSR_L_zero_F_pos_trace
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {s t : AgentState n}
    (hs : s.role = .Resetting) (ht : t.role = .Resetting)
    (hs_rc : s.resetcount = 0) (ht_rc : 0 < t.resetcount)
    (hs_L : s.leader = .L) (ht_F : t.leader = .F)
    (hs_dt : 1 < s.delaytimer)
    (hDmax : 0 < Dmax) :
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.role = .Resetting ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.role = .Resetting ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.resetcount = t.resetcount - 1 ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.resetcount = t.resetcount - 1 ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.leader = .L ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.leader = .F ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.delaytimer =
      (if t.resetcount = 1 then s.delaytimer - 1 else s.delaytimer) := by
    unfold rankDeltaOSSR propagateReset processAgent resetOSSR
    by_cases ht_one : t.resetcount = 1
    · have hnew : max (0 - 1) (t.resetcount - 1) = 0 := by omega
      have hs_dt_ne : s.delaytimer - 1 ≠ 0 := by omega
      simp [hs, ht, hs_rc, ht_rc, hs_L, ht_F, ht_one, hnew, hs_dt_ne,
        show (Dmax : ℕ) ≠ 0 from by omega]
    · have ht_pred_ne : t.resetcount - 1 ≠ 0 := by omega
      have hnew : max (0 - 1) (t.resetcount - 1) = t.resetcount - 1 := by omega
      simp [hs, ht, hs_rc, ht_rc, hs_L, ht_F, ht_one, ht_pred_ne, hnew]

theorem rankDeltaOSSR_L_zero_F_pos_gt_one_trace
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {s t : AgentState n}
    (hs : s.role = .Resetting) (ht : t.role = .Resetting)
    (hs_rc : s.resetcount = 0) (ht_rc : 1 < t.resetcount)
    (hs_L : s.leader = .L) (ht_F : t.leader = .F) :
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.role = .Resetting ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.role = .Resetting ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.resetcount = t.resetcount - 1 ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.resetcount = t.resetcount - 1 ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.leader = .L ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.leader = .F := by
  have ht_one : ¬ t.resetcount = 1 := by omega
  have ht_pos : 0 < t.resetcount := by omega
  have ht_pred_ne : t.resetcount - 1 ≠ 0 := by omega
  have hnew : max (0 - 1) (t.resetcount - 1) = t.resetcount - 1 := by omega
  unfold rankDeltaOSSR propagateReset processAgent resetOSSR
  simp [hs, ht, hs_rc, ht_pos, hs_L, ht_F, ht_one, ht_pred_ne, hnew]

theorem rankDeltaOSSR_L_zero_F_pos_one_low_trace
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {s t : AgentState n}
    (hs : s.role = .Resetting) (ht : t.role = .Resetting)
    (hs_rc : s.resetcount = 0) (ht_rc : t.resetcount = 1)
    (hs_L : s.leader = .L) (ht_F : t.leader = .F)
    (hs_low : s.delaytimer ≤ 1) (hDmax : 0 < Dmax) :
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.role = .Settled ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.rank = ⟨0, hn⟩ ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.children = 0 ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.leader = .L ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.role = .Resetting ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.resetcount = 0 ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.leader = .F ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.delaytimer = Dmax := by
  have hnew : max (0 - 1) (t.resetcount - 1) = 0 := by omega
  have hs_dt_zero : s.delaytimer - 1 = 0 := by omega
  unfold rankDeltaOSSR propagateReset processAgent resetOSSR
  simp [hs, ht, hs_rc, ht_rc, hs_L, ht_F, hnew, hs_dt_zero,
    show (Dmax : ℕ) ≠ 0 from by omega]

theorem rankDeltaOSSR_L_zero_L_pos_trace
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {s t : AgentState n}
    (hs : s.role = .Resetting) (ht : t.role = .Resetting)
    (hs_rc : s.resetcount = 0) (ht_rc : 0 < t.resetcount)
    (hs_L : s.leader = .L) (ht_L : t.leader = .L)
    (hs_dt : 1 < s.delaytimer)
    (hDmax : 0 < Dmax) :
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.role = .Resetting ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.role = .Resetting ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.resetcount = t.resetcount - 1 ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.resetcount = t.resetcount - 1 ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.leader = .L ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.leader = .F ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.delaytimer =
      (if t.resetcount = 1 then s.delaytimer - 1 else s.delaytimer) := by
  unfold rankDeltaOSSR propagateReset processAgent resetOSSR
  by_cases ht_one : t.resetcount = 1
  · have hnew : max (0 - 1) (t.resetcount - 1) = 0 := by omega
    have hs_dt_ne : s.delaytimer - 1 ≠ 0 := by omega
    simp [hs, ht, hs_rc, ht_rc, hs_L, ht_L, ht_one, hnew, hs_dt_ne,
      show (Dmax : ℕ) ≠ 0 from by omega]
  · have ht_pred_ne : t.resetcount - 1 ≠ 0 := by omega
    have hnew : max (0 - 1) (t.resetcount - 1) = t.resetcount - 1 := by omega
    simp [hs, ht, hs_rc, ht_rc, hs_L, ht_L, ht_one, ht_pred_ne, hnew]

/-- Leader dedup: when two Resetting+rc=0+L agents with dt > 1 interact,
rankDeltaOSSR sets the second's leader to F (outer dedup) while keeping both
Resetting with rc=0 and decreasing both delaytimers by 1. -/
theorem rankDeltaOSSR_leader_dedup_step
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {s t : AgentState n}
    (hs : s.role = .Resetting) (hs_rc : s.resetcount = 0)
    (ht : t.role = .Resetting) (ht_rc : t.resetcount = 0)
    (hs_L : s.leader = .L) (ht_L : t.leader = .L)
    (hs_dt : 1 < s.delaytimer) (ht_dt : 1 < t.delaytimer) :
      let r := rankDeltaOSSR Rmax Emax Dmax hn (s, t)
      r.1.role = .Resetting ∧ r.1.resetcount = 0 ∧
      r.1.delaytimer = s.delaytimer - 1 ∧ r.1.leader = .L ∧
      r.2.role = .Resetting ∧ r.2.resetcount = 0 ∧
      r.2.delaytimer = t.delaytimer - 1 ∧ r.2.leader = .F := by
  have hs_dt_ne : s.delaytimer - 1 ≠ 0 := by omega
  have ht_dt_ne : t.delaytimer - 1 ≠ 0 := by omega
  unfold rankDeltaOSSR propagateReset processAgent resetOSSR
  simp [hs, ht, hs_rc, ht_rc, hs_L, ht_L, hs_dt_ne, ht_dt_ne]

set_option maxHeartbeats 4000000 in
/-- Config.step lift: when scheduling two Resetting agents both with rc > 0,
after one step both stay Resetting and both rc equal `max(s.rc-1, t.rc-1)`.
Composes `rankDeltaOSSR_both_rc_pos_role` (rankDelta-level role + rc), the
`transitionPEM_structural_passthrough` for not-both-Settled, and the standard
`Config.step_*_state` projections. -/
theorem step_both_rc_pos
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 0 < Dmax)
    (C : Config (AgentState n) Opinion n)
    {u v : Fin n} (huv : u ≠ v)
    (hu_res : (C u).1.role = .Resetting) (hv_res : (C v).1.role = .Resetting)
    (hu_rc : 0 < (C u).1.resetcount) (hv_rc : 0 < (C v).1.resetcount) :
    let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := C.step P u v
    (C' u).1.role = .Resetting ∧
    (C' v).1.role = .Resetting ∧
    (C' u).1.resetcount = Nat.max ((C u).1.resetcount - 1) ((C v).1.resetcount - 1) ∧
    (C' v).1.resetcount = Nat.max ((C u).1.resetcount - 1) ((C v).1.resetcount - 1) ∧
    (C' u).1.leader = (C u).1.leader := by
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have h_rd := rankDeltaOSSR_both_rc_pos_role (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
    (hn := hn) hu_res hv_res hu_rc hv_rc hDmax
  have h_not_both : ¬((rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1)).1.role = .Settled ∧
                      (rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1)).2.role = .Settled) := by
    intro ⟨h1, _⟩; rw [h_rd.1] at h1; exact Role.noConfusion h1
  have h_pass := transitionPEM_structural_passthrough (trank := Rmax) (Rmax := Rmax)
    (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn) (x₀ := (C u).2) (x₁ := (C v).2) h_not_both
  have h_fst := Config.step_fst_state P C huv
  have h_snd := Config.step_snd_state P C huv huv.symm
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [congrArg AgentState.role h_fst]; exact h_pass.1 ▸ h_rd.1
  · rw [congrArg AgentState.role h_snd]; exact h_pass.2.2.2.2.2.2.1 ▸ h_rd.2.1
  · rw [congrArg AgentState.resetcount h_fst]; exact h_pass.2.2.2.2.1 ▸ h_rd.2.2.1
  · rw [congrArg AgentState.resetcount h_snd]; exact h_pass.2.2.2.2.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.1
  · rw [congrArg AgentState.leader h_fst]; exact h_pass.2.1 ▸ h_rd.2.2.2.2

set_option maxHeartbeats 4000000 in
theorem step_both_rc_pos_fst_delay_final
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 0 < Dmax)
    (C : Config (AgentState n) Opinion n)
    {u v : Fin n} (huv : u ≠ v)
    (hu_res : (C u).1.role = .Resetting) (hv_res : (C v).1.role = .Resetting)
    (hu_rc : 0 < (C u).1.resetcount) (hv_rc : 0 < (C v).1.resetcount)
    (hnew : Nat.max ((C u).1.resetcount - 1) ((C v).1.resetcount - 1) = 0) :
    let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := C.step P u v
    (C' u).1.delaytimer = Dmax := by
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have h_rd_role := rankDeltaOSSR_both_rc_pos_role (Rmax := Rmax) (Emax := Emax)
    (Dmax := Dmax) (hn := hn) hu_res hv_res hu_rc hv_rc hDmax
  have h_rd_delay := rankDeltaOSSR_both_rc_pos_fst_delay_final
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hu_res hv_res hu_rc hv_rc hnew hDmax
  have h_not_both : ¬((rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1)).1.role = .Settled ∧
                      (rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1)).2.role = .Settled) := by
    intro ⟨h1, _⟩; rw [h_rd_role.1] at h1; exact Role.noConfusion h1
  have h_pass := transitionPEM_structural_passthrough (trank := Rmax) (Rmax := Rmax)
    (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn) (x₀ := (C u).2) (x₁ := (C v).2) h_not_both
  have h_fst := Config.step_fst_state P C huv
  change (C.step P u v u).1.delaytimer = Dmax
  rw [congrArg AgentState.delaytimer h_fst]
  exact h_pass.2.2.2.2.2.1 ▸ h_rd_delay

set_option maxHeartbeats 4000000 in
theorem step_both_rc_pos_LF
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 0 < Dmax)
    (C : Config (AgentState n) Opinion n)
    {u v : Fin n} (huv : u ≠ v)
    (hu_res : (C u).1.role = .Resetting) (hv_res : (C v).1.role = .Resetting)
    (hu_rc : 0 < (C u).1.resetcount) (hv_rc : 0 < (C v).1.resetcount)
    (hu_L : (C u).1.leader = .L) (hv_F : (C v).1.leader = .F) :
    let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := C.step P u v
    (C' u).1.role = .Resetting ∧
    (C' v).1.role = .Resetting ∧
    (C' u).1.resetcount = Nat.max ((C u).1.resetcount - 1) ((C v).1.resetcount - 1) ∧
    (C' v).1.resetcount = Nat.max ((C u).1.resetcount - 1) ((C v).1.resetcount - 1) ∧
    (C' u).1.leader = .L ∧
    (C' v).1.leader = .F := by
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have h_rd := rankDeltaOSSR_both_rc_pos_LF_trace (Rmax := Rmax) (Emax := Emax)
    (Dmax := Dmax) (hn := hn) hu_res hv_res hu_rc hv_rc hu_L hv_F hDmax
  have h_not_both : ¬((rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1)).1.role = .Settled ∧
                      (rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1)).2.role = .Settled) := by
    intro ⟨h1, _⟩; rw [h_rd.1] at h1; exact Role.noConfusion h1
  have h_pass := transitionPEM_structural_passthrough (trank := Rmax) (Rmax := Rmax)
    (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn) (x₀ := (C u).2) (x₁ := (C v).2) h_not_both
  have h_fst := Config.step_fst_state P C huv
  have h_snd := Config.step_snd_state P C huv huv.symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [congrArg AgentState.role h_fst]; exact h_pass.1 ▸ h_rd.1
  · rw [congrArg AgentState.role h_snd]; exact h_pass.2.2.2.2.2.2.1 ▸ h_rd.2.1
  · rw [congrArg AgentState.resetcount h_fst]; exact h_pass.2.2.2.2.1 ▸ h_rd.2.2.1
  · rw [congrArg AgentState.resetcount h_snd]; exact h_pass.2.2.2.2.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.1
  · rw [congrArg AgentState.leader h_fst]; exact h_pass.2.1 ▸ h_rd.2.2.2.2.1
  · rw [congrArg AgentState.leader h_snd]; exact h_pass.2.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.2.2

set_option maxHeartbeats 4000000 in
theorem step_both_rc_pos_FF
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 0 < Dmax)
    (C : Config (AgentState n) Opinion n)
    {u v : Fin n} (huv : u ≠ v)
    (hu_res : (C u).1.role = .Resetting) (hv_res : (C v).1.role = .Resetting)
    (hu_rc : 0 < (C u).1.resetcount) (hv_rc : 0 < (C v).1.resetcount)
    (hu_F : (C u).1.leader = .F) (hv_F : (C v).1.leader = .F) :
    let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := C.step P u v
    (C' u).1.role = .Resetting ∧
    (C' v).1.role = .Resetting ∧
    (C' u).1.resetcount = Nat.max ((C u).1.resetcount - 1) ((C v).1.resetcount - 1) ∧
    (C' v).1.resetcount = Nat.max ((C u).1.resetcount - 1) ((C v).1.resetcount - 1) ∧
    (C' u).1.leader = .F ∧
    (C' v).1.leader = .F := by
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have h_rd := rankDeltaOSSR_both_rc_pos_FF_trace (Rmax := Rmax) (Emax := Emax)
    (Dmax := Dmax) (hn := hn) hu_res hv_res hu_rc hv_rc hu_F hv_F hDmax
  have h_not_both : ¬((rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1)).1.role = .Settled ∧
                      (rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1)).2.role = .Settled) := by
    intro ⟨h1, _⟩; rw [h_rd.1] at h1; exact Role.noConfusion h1
  have h_pass := transitionPEM_structural_passthrough (trank := Rmax) (Rmax := Rmax)
    (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn) (x₀ := (C u).2) (x₁ := (C v).2) h_not_both
  have h_fst := Config.step_fst_state P C huv
  have h_snd := Config.step_snd_state P C huv huv.symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [congrArg AgentState.role h_fst]; exact h_pass.1 ▸ h_rd.1
  · rw [congrArg AgentState.role h_snd]; exact h_pass.2.2.2.2.2.2.1 ▸ h_rd.2.1
  · rw [congrArg AgentState.resetcount h_fst]; exact h_pass.2.2.2.2.1 ▸ h_rd.2.2.1
  · rw [congrArg AgentState.resetcount h_snd]; exact h_pass.2.2.2.2.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.1
  · rw [congrArg AgentState.leader h_fst]; exact h_pass.2.1 ▸ h_rd.2.2.2.2.1
  · rw [congrArg AgentState.leader h_snd]; exact h_pass.2.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.2.2

set_option maxHeartbeats 4000000 in
theorem step_both_rc_pos_LL
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 0 < Dmax)
    (C : Config (AgentState n) Opinion n)
    {u v : Fin n} (huv : u ≠ v)
    (hu_res : (C u).1.role = .Resetting) (hv_res : (C v).1.role = .Resetting)
    (hu_rc : 0 < (C u).1.resetcount) (hv_rc : 0 < (C v).1.resetcount)
    (hu_L : (C u).1.leader = .L) (hv_L : (C v).1.leader = .L) :
    let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := C.step P u v
    (C' u).1.role = .Resetting ∧
    (C' v).1.role = .Resetting ∧
    (C' u).1.resetcount = Nat.max ((C u).1.resetcount - 1) ((C v).1.resetcount - 1) ∧
    (C' v).1.resetcount = Nat.max ((C u).1.resetcount - 1) ((C v).1.resetcount - 1) ∧
    (C' u).1.leader = .L ∧
    (C' v).1.leader = .F := by
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have h_rd := rankDeltaOSSR_both_rc_pos_LL_trace (Rmax := Rmax) (Emax := Emax)
    (Dmax := Dmax) (hn := hn) hu_res hv_res hu_rc hv_rc hu_L hv_L hDmax
  have h_not_both : ¬((rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1)).1.role = .Settled ∧
                      (rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1)).2.role = .Settled) := by
    intro ⟨h1, _⟩; rw [h_rd.1] at h1; exact Role.noConfusion h1
  have h_pass := transitionPEM_structural_passthrough (trank := Rmax) (Rmax := Rmax)
    (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn) (x₀ := (C u).2) (x₁ := (C v).2) h_not_both
  have h_fst := Config.step_fst_state P C huv
  have h_snd := Config.step_snd_state P C huv huv.symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [congrArg AgentState.role h_fst]; exact h_pass.1 ▸ h_rd.1
  · rw [congrArg AgentState.role h_snd]; exact h_pass.2.2.2.2.2.2.1 ▸ h_rd.2.1
  · rw [congrArg AgentState.resetcount h_fst]; exact h_pass.2.2.2.2.1 ▸ h_rd.2.2.1
  · rw [congrArg AgentState.resetcount h_snd]; exact h_pass.2.2.2.2.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.1
  · rw [congrArg AgentState.leader h_fst]; exact h_pass.2.1 ▸ h_rd.2.2.2.2.1
  · rw [congrArg AgentState.leader h_snd]; exact h_pass.2.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.2.2

set_option maxHeartbeats 4000000 in
theorem step_L_pos_F_zero
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 0 < Dmax)
    (C : Config (AgentState n) Opinion n)
    {u v : Fin n} (huv : u ≠ v)
    (hu_res : (C u).1.role = .Resetting) (hv_res : (C v).1.role = .Resetting)
    (hu_rc : 0 < (C u).1.resetcount) (hv_rc : (C v).1.resetcount = 0)
    (hu_L : (C u).1.leader = .L) (hv_F : (C v).1.leader = .F)
    (hv_dt : 1 < (C v).1.delaytimer) :
    let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := C.step P u v
    (C' u).1.role = .Resetting ∧
    (C' v).1.role = .Resetting ∧
    (C' u).1.resetcount = (C u).1.resetcount - 1 ∧
    (C' v).1.resetcount = (C u).1.resetcount - 1 ∧
    (C' u).1.leader = .L ∧
    (C' v).1.leader = .F ∧
    (C' v).1.delaytimer =
      (if (C u).1.resetcount = 1 then (C v).1.delaytimer - 1 else (C v).1.delaytimer) := by
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have h_rd := rankDeltaOSSR_L_pos_F_zero_trace (Rmax := Rmax) (Emax := Emax)
    (Dmax := Dmax) (hn := hn) hu_res hv_res hu_rc hv_rc hu_L hv_F hv_dt hDmax
  have h_not_both : ¬((rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1)).1.role = .Settled ∧
                      (rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1)).2.role = .Settled) := by
    intro ⟨h1, _⟩; rw [h_rd.1] at h1; exact Role.noConfusion h1
  have h_pass := transitionPEM_structural_passthrough (trank := Rmax) (Rmax := Rmax)
    (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn) (x₀ := (C u).2) (x₁ := (C v).2) h_not_both
  have h_fst := Config.step_fst_state P C huv
  have h_snd := Config.step_snd_state P C huv huv.symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [congrArg AgentState.role h_fst]; exact h_pass.1 ▸ h_rd.1
  · rw [congrArg AgentState.role h_snd]; exact h_pass.2.2.2.2.2.2.1 ▸ h_rd.2.1
  · rw [congrArg AgentState.resetcount h_fst]; exact h_pass.2.2.2.2.1 ▸ h_rd.2.2.1
  · rw [congrArg AgentState.resetcount h_snd]; exact h_pass.2.2.2.2.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.1
  · rw [congrArg AgentState.leader h_fst]; exact h_pass.2.1 ▸ h_rd.2.2.2.2.1
  · rw [congrArg AgentState.leader h_snd]; exact h_pass.2.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.2.2.1
  · rw [congrArg AgentState.delaytimer h_snd]; exact h_pass.2.2.2.2.2.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.2.2.2

set_option maxHeartbeats 4000000 in
theorem step_L_pos_L_zero
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 0 < Dmax)
    (C : Config (AgentState n) Opinion n)
    {u v : Fin n} (huv : u ≠ v)
    (hu_res : (C u).1.role = .Resetting) (hv_res : (C v).1.role = .Resetting)
    (hu_rc : 0 < (C u).1.resetcount) (hv_rc : (C v).1.resetcount = 0)
    (hu_L : (C u).1.leader = .L) (hv_L : (C v).1.leader = .L)
    (hv_dt : 1 < (C v).1.delaytimer) :
    let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := C.step P u v
    (C' u).1.role = .Resetting ∧
    (C' v).1.role = .Resetting ∧
    (C' u).1.resetcount = (C u).1.resetcount - 1 ∧
    (C' v).1.resetcount = (C u).1.resetcount - 1 ∧
    (C' u).1.leader = .L ∧
    (C' v).1.leader = .F ∧
    (C' v).1.delaytimer =
      (if (C u).1.resetcount = 1 then (C v).1.delaytimer - 1 else (C v).1.delaytimer) := by
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have h_rd := rankDeltaOSSR_L_pos_L_zero_trace (Rmax := Rmax) (Emax := Emax)
    (Dmax := Dmax) (hn := hn) hu_res hv_res hu_rc hv_rc hu_L hv_L hv_dt hDmax
  have h_not_both : ¬((rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1)).1.role = .Settled ∧
                      (rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1)).2.role = .Settled) := by
    intro ⟨h1, _⟩; rw [h_rd.1] at h1; exact Role.noConfusion h1
  have h_pass := transitionPEM_structural_passthrough (trank := Rmax) (Rmax := Rmax)
    (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn) (x₀ := (C u).2) (x₁ := (C v).2) h_not_both
  have h_fst := Config.step_fst_state P C huv
  have h_snd := Config.step_snd_state P C huv huv.symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [congrArg AgentState.role h_fst]; exact h_pass.1 ▸ h_rd.1
  · rw [congrArg AgentState.role h_snd]; exact h_pass.2.2.2.2.2.2.1 ▸ h_rd.2.1
  · rw [congrArg AgentState.resetcount h_fst]; exact h_pass.2.2.2.2.1 ▸ h_rd.2.2.1
  · rw [congrArg AgentState.resetcount h_snd]; exact h_pass.2.2.2.2.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.1
  · rw [congrArg AgentState.leader h_fst]; exact h_pass.2.1 ▸ h_rd.2.2.2.2.1
  · rw [congrArg AgentState.leader h_snd]; exact h_pass.2.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.2.2.1
  · rw [congrArg AgentState.delaytimer h_snd]; exact h_pass.2.2.2.2.2.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.2.2.2

set_option maxHeartbeats 4000000 in
theorem step_F_pos_F_zero
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 0 < Dmax)
    (C : Config (AgentState n) Opinion n)
    {u v : Fin n} (huv : u ≠ v)
    (hu_res : (C u).1.role = .Resetting) (hv_res : (C v).1.role = .Resetting)
    (hu_rc : 0 < (C u).1.resetcount) (hv_rc : (C v).1.resetcount = 0)
    (hu_F : (C u).1.leader = .F) (hv_F : (C v).1.leader = .F)
    (hv_dt : 1 < (C v).1.delaytimer) :
    let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := C.step P u v
    (C' u).1.role = .Resetting ∧
    (C' v).1.role = .Resetting ∧
    (C' u).1.resetcount = (C u).1.resetcount - 1 ∧
    (C' v).1.resetcount = (C u).1.resetcount - 1 ∧
    (C' u).1.leader = .F ∧
    (C' v).1.leader = .F := by
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have h_rd := rankDeltaOSSR_F_pos_F_zero_trace (Rmax := Rmax) (Emax := Emax)
    (Dmax := Dmax) (hn := hn) hu_res hv_res hu_rc hv_rc hu_F hv_F hv_dt hDmax
  have h_not_both : ¬((rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1)).1.role = .Settled ∧
                      (rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1)).2.role = .Settled) := by
    intro ⟨h1, _⟩; rw [h_rd.1] at h1; exact Role.noConfusion h1
  have h_pass := transitionPEM_structural_passthrough (trank := Rmax) (Rmax := Rmax)
    (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn) (x₀ := (C u).2) (x₁ := (C v).2) h_not_both
  have h_fst := Config.step_fst_state P C huv
  have h_snd := Config.step_snd_state P C huv huv.symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [congrArg AgentState.role h_fst]; exact h_pass.1 ▸ h_rd.1
  · rw [congrArg AgentState.role h_snd]; exact h_pass.2.2.2.2.2.2.1 ▸ h_rd.2.1
  · rw [congrArg AgentState.resetcount h_fst]; exact h_pass.2.2.2.2.1 ▸ h_rd.2.2.1
  · rw [congrArg AgentState.resetcount h_snd]; exact h_pass.2.2.2.2.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.1
  · rw [congrArg AgentState.leader h_fst]; exact h_pass.2.1 ▸ h_rd.2.2.2.2.1
  · rw [congrArg AgentState.leader h_snd]; exact h_pass.2.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.2.2

set_option maxHeartbeats 4000000 in
theorem step_L_pos_any_zero_gt_one
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (C : Config (AgentState n) Opinion n)
    {u v : Fin n} (huv : u ≠ v)
    (hu_res : (C u).1.role = .Resetting) (hv_res : (C v).1.role = .Resetting)
    (hu_rc : 1 < (C u).1.resetcount) (hv_rc : (C v).1.resetcount = 0)
    (hu_L : (C u).1.leader = .L) :
    let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := C.step P u v
    (C' u).1.role = .Resetting ∧
    (C' v).1.role = .Resetting ∧
    (C' u).1.resetcount = (C u).1.resetcount - 1 ∧
    (C' v).1.resetcount = (C u).1.resetcount - 1 ∧
    (C' u).1.leader = .L ∧
    (C' v).1.leader = .F := by
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have h_rd := rankDeltaOSSR_L_pos_any_zero_gt_one_trace
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hu_res hv_res hu_rc hv_rc hu_L
  have h_not_both : ¬((rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1)).1.role = .Settled ∧
                      (rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1)).2.role = .Settled) := by
    intro ⟨h1, _⟩; rw [h_rd.1] at h1; exact Role.noConfusion h1
  have h_pass := transitionPEM_structural_passthrough (trank := Rmax) (Rmax := Rmax)
    (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn) (x₀ := (C u).2) (x₁ := (C v).2) h_not_both
  have h_fst := Config.step_fst_state P C huv
  have h_snd := Config.step_snd_state P C huv huv.symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [congrArg AgentState.role h_fst]; exact h_pass.1 ▸ h_rd.1
  · rw [congrArg AgentState.role h_snd]; exact h_pass.2.2.2.2.2.2.1 ▸ h_rd.2.1
  · rw [congrArg AgentState.resetcount h_fst]; exact h_pass.2.2.2.2.1 ▸ h_rd.2.2.1
  · rw [congrArg AgentState.resetcount h_snd]; exact h_pass.2.2.2.2.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.1
  · rw [congrArg AgentState.leader h_fst]; exact h_pass.2.1 ▸ h_rd.2.2.2.2.1
  · rw [congrArg AgentState.leader h_snd]; exact h_pass.2.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.2.2

set_option maxHeartbeats 4000000 in
theorem step_F_pos_F_zero_gt_one
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (C : Config (AgentState n) Opinion n)
    {u v : Fin n} (huv : u ≠ v)
    (hu_res : (C u).1.role = .Resetting) (hv_res : (C v).1.role = .Resetting)
    (hu_rc : 1 < (C u).1.resetcount) (hv_rc : (C v).1.resetcount = 0)
    (hu_F : (C u).1.leader = .F) (hv_F : (C v).1.leader = .F) :
    let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := C.step P u v
    (C' u).1.role = .Resetting ∧
    (C' v).1.role = .Resetting ∧
    (C' u).1.resetcount = (C u).1.resetcount - 1 ∧
    (C' v).1.resetcount = (C u).1.resetcount - 1 ∧
    (C' u).1.leader = .F ∧
    (C' v).1.leader = .F := by
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have h_rd := rankDeltaOSSR_F_pos_F_zero_gt_one_trace
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hu_res hv_res hu_rc hv_rc hu_F hv_F
  have h_not_both : ¬((rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1)).1.role = .Settled ∧
                      (rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1)).2.role = .Settled) := by
    intro ⟨h1, _⟩; rw [h_rd.1] at h1; exact Role.noConfusion h1
  have h_pass := transitionPEM_structural_passthrough (trank := Rmax) (Rmax := Rmax)
    (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn) (x₀ := (C u).2) (x₁ := (C v).2) h_not_both
  have h_fst := Config.step_fst_state P C huv
  have h_snd := Config.step_snd_state P C huv huv.symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [congrArg AgentState.role h_fst]; exact h_pass.1 ▸ h_rd.1
  · rw [congrArg AgentState.role h_snd]; exact h_pass.2.2.2.2.2.2.1 ▸ h_rd.2.1
  · rw [congrArg AgentState.resetcount h_fst]; exact h_pass.2.2.2.2.1 ▸ h_rd.2.2.1
  · rw [congrArg AgentState.resetcount h_snd]; exact h_pass.2.2.2.2.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.1
  · rw [congrArg AgentState.leader h_fst]; exact h_pass.2.1 ▸ h_rd.2.2.2.2.1
  · rw [congrArg AgentState.leader h_snd]; exact h_pass.2.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.2.2

set_option maxHeartbeats 4000000 in
theorem step_L_pos_one_F_zero_low
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 0 < Dmax)
    (C : Config (AgentState n) Opinion n)
    {u v : Fin n} (huv : u ≠ v)
    (hu_res : (C u).1.role = .Resetting) (hv_res : (C v).1.role = .Resetting)
    (hu_rc : (C u).1.resetcount = 1) (hv_rc : (C v).1.resetcount = 0)
    (hu_L : (C u).1.leader = .L) (hv_F : (C v).1.leader = .F)
    (hv_low : (C v).1.delaytimer ≤ 1) :
    let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := C.step P u v
    (C' u).1.role = .Resetting ∧
    (C' u).1.resetcount = 0 ∧
    (C' u).1.leader = .L ∧
    (C' u).1.delaytimer = Dmax ∧
    (C' v).1.role = .Unsettled ∧
    (C' v).1.leader = .F := by
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have h_rd := rankDeltaOSSR_L_pos_one_F_zero_low_trace
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hu_res hv_res hu_rc hv_rc hu_L hv_F hv_low hDmax
  have h_not_both : ¬((rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1)).1.role = .Settled ∧
                      (rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1)).2.role = .Settled) := by
    intro ⟨h1, _⟩; rw [h_rd.1] at h1; exact Role.noConfusion h1
  have h_pass := transitionPEM_structural_passthrough (trank := Rmax) (Rmax := Rmax)
    (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn) (x₀ := (C u).2) (x₁ := (C v).2) h_not_both
  have h_fst := Config.step_fst_state P C huv
  have h_snd := Config.step_snd_state P C huv huv.symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [congrArg AgentState.role h_fst]; exact h_pass.1 ▸ h_rd.1
  · rw [congrArg AgentState.resetcount h_fst]; exact h_pass.2.2.2.2.1 ▸ h_rd.2.1
  · rw [congrArg AgentState.leader h_fst]; exact h_pass.2.1 ▸ h_rd.2.2.1
  · rw [congrArg AgentState.delaytimer h_fst]; exact h_pass.2.2.2.2.2.1 ▸ h_rd.2.2.2.1
  · rw [congrArg AgentState.role h_snd]; exact h_pass.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.2.1
  · rw [congrArg AgentState.leader h_snd]; exact h_pass.2.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.2.2

set_option maxHeartbeats 4000000 in
theorem step_F_pos_one_F_zero_low
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 0 < Dmax)
    (C : Config (AgentState n) Opinion n)
    {u v : Fin n} (huv : u ≠ v)
    (hu_res : (C u).1.role = .Resetting) (hv_res : (C v).1.role = .Resetting)
    (hu_rc : (C u).1.resetcount = 1) (hv_rc : (C v).1.resetcount = 0)
    (hu_F : (C u).1.leader = .F) (hv_F : (C v).1.leader = .F)
    (hv_low : (C v).1.delaytimer ≤ 1) :
    let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := C.step P u v
    (C' u).1.role = .Resetting ∧
    (C' u).1.resetcount = 0 ∧
    (C' u).1.leader = .F ∧
    (C' u).1.delaytimer = Dmax ∧
    (C' v).1.role = .Unsettled ∧
    (C' v).1.leader = .F := by
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have h_rd := rankDeltaOSSR_F_pos_one_F_zero_low_trace
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hu_res hv_res hu_rc hv_rc hu_F hv_F hv_low hDmax
  have h_not_both : ¬((rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1)).1.role = .Settled ∧
                      (rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1)).2.role = .Settled) := by
    intro ⟨h1, _⟩; rw [h_rd.1] at h1; exact Role.noConfusion h1
  have h_pass := transitionPEM_structural_passthrough (trank := Rmax) (Rmax := Rmax)
    (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn) (x₀ := (C u).2) (x₁ := (C v).2) h_not_both
  have h_fst := Config.step_fst_state P C huv
  have h_snd := Config.step_snd_state P C huv huv.symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [congrArg AgentState.role h_fst]; exact h_pass.1 ▸ h_rd.1
  · rw [congrArg AgentState.resetcount h_fst]; exact h_pass.2.2.2.2.1 ▸ h_rd.2.1
  · rw [congrArg AgentState.leader h_fst]; exact h_pass.2.1 ▸ h_rd.2.2.1
  · rw [congrArg AgentState.delaytimer h_fst]; exact h_pass.2.2.2.2.2.1 ▸ h_rd.2.2.2.1
  · rw [congrArg AgentState.role h_snd]; exact h_pass.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.2.1
  · rw [congrArg AgentState.leader h_snd]; exact h_pass.2.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.2.2

set_option maxHeartbeats 4000000 in
theorem step_F_pos_one_settled_L
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 1 < Dmax)
    (C : Config (AgentState n) Opinion n)
    {u v : Fin n} (huv : u ≠ v)
    (hu_res : (C u).1.role = .Resetting) (hv_settled : (C v).1.role = .Settled)
    (hu_rc : (C u).1.resetcount = 1)
    (hu_F : (C u).1.leader = .F) (hv_L : (C v).1.leader = .L) :
    let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := C.step P u v
    (C' u).1.role = .Resetting ∧
    (C' u).1.resetcount = 0 ∧
    (C' u).1.leader = .F ∧
    (C' v).1.role = .Resetting ∧
    (C' v).1.resetcount = 0 ∧
    (C' v).1.leader = .L ∧
    (C' v).1.delaytimer = Dmax - 1 := by
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have h_rd := rankDeltaOSSR_F_pos_one_settled_L_trace
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hu_res hv_settled hu_rc hu_F hv_L hDmax
  have h_not_both : ¬((rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1)).1.role = .Settled ∧
                      (rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1)).2.role = .Settled) := by
    intro ⟨h1, _⟩; rw [h_rd.1] at h1; exact Role.noConfusion h1
  have h_pass := transitionPEM_structural_passthrough (trank := Rmax) (Rmax := Rmax)
    (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn) (x₀ := (C u).2) (x₁ := (C v).2) h_not_both
  have h_fst := Config.step_fst_state P C huv
  have h_snd := Config.step_snd_state P C huv huv.symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [congrArg AgentState.role h_fst]; exact h_pass.1 ▸ h_rd.1
  · rw [congrArg AgentState.resetcount h_fst]; exact h_pass.2.2.2.2.1 ▸ h_rd.2.1
  · rw [congrArg AgentState.leader h_fst]; exact h_pass.2.1 ▸ h_rd.2.2.1
  · rw [congrArg AgentState.role h_snd]; exact h_pass.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.1
  · rw [congrArg AgentState.resetcount h_snd]; exact h_pass.2.2.2.2.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.2.1
  · rw [congrArg AgentState.leader h_snd]; exact h_pass.2.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.2.2.1
  · rw [congrArg AgentState.delaytimer h_snd]; exact h_pass.2.2.2.2.2.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.2.2.2

set_option maxHeartbeats 4000000 in
theorem step_L_pos_one_L_zero_low
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 0 < Dmax)
    (C : Config (AgentState n) Opinion n)
    {u v : Fin n} (huv : u ≠ v)
    (hu_res : (C u).1.role = .Resetting) (hv_res : (C v).1.role = .Resetting)
    (hu_rc : (C u).1.resetcount = 1) (hv_rc : (C v).1.resetcount = 0)
    (hu_L : (C u).1.leader = .L) (hv_L : (C v).1.leader = .L)
    (hv_low : (C v).1.delaytimer ≤ 1) :
    let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := C.step P u v
    (C' u).1.role = .Resetting ∧
    (C' u).1.resetcount = 0 ∧
    (C' u).1.leader = .L ∧
    (C' u).1.delaytimer = Dmax ∧
    (C' v).1.role = .Settled ∧
    (C' v).1.rank.val = 0 ∧
    (C' v).1.children = 0 ∧
    (C' v).1.leader = .L := by
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have h_rd := rankDeltaOSSR_L_pos_one_L_zero_low_trace
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hu_res hv_res hu_rc hv_rc hu_L hv_L hv_low hDmax
  have h_not_both : ¬((rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1)).1.role = .Settled ∧
                      (rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1)).2.role = .Settled) := by
    intro ⟨h1, _⟩; rw [h_rd.1] at h1; exact Role.noConfusion h1
  have h_pass := transitionPEM_structural_passthrough (trank := Rmax) (Rmax := Rmax)
    (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn) (x₀ := (C u).2) (x₁ := (C v).2) h_not_both
  have h_fst := Config.step_fst_state P C huv
  have h_snd := Config.step_snd_state P C huv huv.symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [congrArg AgentState.role h_fst]; exact h_pass.1 ▸ h_rd.1
  · rw [congrArg AgentState.resetcount h_fst]; exact h_pass.2.2.2.2.1 ▸ h_rd.2.1
  · rw [congrArg AgentState.leader h_fst]; exact h_pass.2.1 ▸ h_rd.2.2.1
  · rw [congrArg AgentState.delaytimer h_fst]; exact h_pass.2.2.2.2.2.1 ▸ h_rd.2.2.2.1
  · rw [congrArg AgentState.role h_snd]; exact h_pass.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.2.1
  · rw [congrArg AgentState.rank h_snd]
    exact congrArg Fin.val (h_pass.2.2.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.2.2.1)
  · rw [congrArg AgentState.children h_snd]; exact h_pass.2.2.2.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.2.2.2.1
  · rw [congrArg AgentState.leader h_snd]; exact h_pass.2.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.2.2.2.2

set_option maxHeartbeats 4000000 in
theorem step_L_zero_F_pos
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 0 < Dmax)
    (C : Config (AgentState n) Opinion n)
    {u v : Fin n} (huv : u ≠ v)
    (hu_res : (C u).1.role = .Resetting) (hv_res : (C v).1.role = .Resetting)
    (hu_rc : (C u).1.resetcount = 0) (hv_rc : 0 < (C v).1.resetcount)
    (hu_L : (C u).1.leader = .L) (hv_F : (C v).1.leader = .F)
    (hu_dt : 1 < (C u).1.delaytimer) :
    let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := C.step P u v
    (C' u).1.role = .Resetting ∧
    (C' v).1.role = .Resetting ∧
    (C' u).1.resetcount = (C v).1.resetcount - 1 ∧
    (C' v).1.resetcount = (C v).1.resetcount - 1 ∧
    (C' u).1.leader = .L ∧
    (C' v).1.leader = .F ∧
    (C' u).1.delaytimer =
      (if (C v).1.resetcount = 1 then (C u).1.delaytimer - 1 else (C u).1.delaytimer) := by
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have h_rd := rankDeltaOSSR_L_zero_F_pos_trace (Rmax := Rmax) (Emax := Emax)
    (Dmax := Dmax) (hn := hn) hu_res hv_res hu_rc hv_rc hu_L hv_F hu_dt hDmax
  have h_not_both : ¬((rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1)).1.role = .Settled ∧
                      (rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1)).2.role = .Settled) := by
    intro ⟨h1, _⟩; rw [h_rd.1] at h1; exact Role.noConfusion h1
  have h_pass := transitionPEM_structural_passthrough (trank := Rmax) (Rmax := Rmax)
    (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn) (x₀ := (C u).2) (x₁ := (C v).2) h_not_both
  have h_fst := Config.step_fst_state P C huv
  have h_snd := Config.step_snd_state P C huv huv.symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [congrArg AgentState.role h_fst]; exact h_pass.1 ▸ h_rd.1
  · rw [congrArg AgentState.role h_snd]; exact h_pass.2.2.2.2.2.2.1 ▸ h_rd.2.1
  · rw [congrArg AgentState.resetcount h_fst]; exact h_pass.2.2.2.2.1 ▸ h_rd.2.2.1
  · rw [congrArg AgentState.resetcount h_snd]; exact h_pass.2.2.2.2.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.1
  · rw [congrArg AgentState.leader h_fst]; exact h_pass.2.1 ▸ h_rd.2.2.2.2.1
  · rw [congrArg AgentState.leader h_snd]; exact h_pass.2.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.2.2.1
  · rw [congrArg AgentState.delaytimer h_fst]; exact h_pass.2.2.2.2.2.1 ▸ h_rd.2.2.2.2.2.2

set_option maxHeartbeats 4000000 in
theorem step_L_zero_F_pos_gt_one
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (C : Config (AgentState n) Opinion n)
    {u v : Fin n} (huv : u ≠ v)
    (hu_res : (C u).1.role = .Resetting) (hv_res : (C v).1.role = .Resetting)
    (hu_rc : (C u).1.resetcount = 0) (hv_rc : 1 < (C v).1.resetcount)
    (hu_L : (C u).1.leader = .L) (hv_F : (C v).1.leader = .F) :
    let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := C.step P u v
    (C' u).1.role = .Resetting ∧
    (C' v).1.role = .Resetting ∧
    (C' u).1.resetcount = (C v).1.resetcount - 1 ∧
    (C' v).1.resetcount = (C v).1.resetcount - 1 ∧
    (C' u).1.leader = .L ∧
    (C' v).1.leader = .F := by
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have h_rd := rankDeltaOSSR_L_zero_F_pos_gt_one_trace
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hu_res hv_res hu_rc hv_rc hu_L hv_F
  have h_not_both :
      ¬((rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1)).1.role = .Settled ∧
        (rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1)).2.role = .Settled) := by
    intro ⟨h1, _⟩
    rw [h_rd.1] at h1
    exact Role.noConfusion h1
  have h_pass := transitionPEM_structural_passthrough (trank := Rmax) (Rmax := Rmax)
    (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn) (x₀ := (C u).2) (x₁ := (C v).2) h_not_both
  have h_fst := Config.step_fst_state P C huv
  have h_snd := Config.step_snd_state P C huv huv.symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [congrArg AgentState.role h_fst]; exact h_pass.1 ▸ h_rd.1
  · rw [congrArg AgentState.role h_snd]; exact h_pass.2.2.2.2.2.2.1 ▸ h_rd.2.1
  · rw [congrArg AgentState.resetcount h_fst]; exact h_pass.2.2.2.2.1 ▸ h_rd.2.2.1
  · rw [congrArg AgentState.resetcount h_snd]; exact h_pass.2.2.2.2.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.1
  · rw [congrArg AgentState.leader h_fst]; exact h_pass.2.1 ▸ h_rd.2.2.2.2.1
  · rw [congrArg AgentState.leader h_snd]; exact h_pass.2.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.2.2

set_option maxHeartbeats 4000000 in
theorem step_L_zero_F_pos_one_low
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 0 < Dmax)
    (C : Config (AgentState n) Opinion n)
    {u v : Fin n} (huv : u ≠ v)
    (hu_res : (C u).1.role = .Resetting) (hv_res : (C v).1.role = .Resetting)
    (hu_rc : (C u).1.resetcount = 0) (hv_rc : (C v).1.resetcount = 1)
    (hu_L : (C u).1.leader = .L) (hv_F : (C v).1.leader = .F)
    (hu_low : (C u).1.delaytimer ≤ 1) :
    let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := C.step P u v
    (C' u).1.role = .Settled ∧
    (C' u).1.rank.val = 0 ∧
    (C' u).1.children = 0 ∧
    (C' u).1.leader = .L ∧
    (C' v).1.role = .Resetting ∧
    (C' v).1.resetcount = 0 ∧
    (C' v).1.leader = .F ∧
    (C' v).1.delaytimer = Dmax := by
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have h_rd := rankDeltaOSSR_L_zero_F_pos_one_low_trace
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hu_res hv_res hu_rc hv_rc hu_L hv_F hu_low hDmax
  have h_not_both : ¬((rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1)).1.role = .Settled ∧
                      (rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1)).2.role = .Settled) := by
    intro hboth
    rw [h_rd.2.2.2.2.1] at hboth
    exact Role.noConfusion hboth.2
  have h_pass := transitionPEM_structural_passthrough (trank := Rmax) (Rmax := Rmax)
    (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn) (x₀ := (C u).2) (x₁ := (C v).2) h_not_both
  have h_fst := Config.step_fst_state P C huv
  have h_snd := Config.step_snd_state P C huv huv.symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [congrArg AgentState.role h_fst]; exact h_pass.1 ▸ h_rd.1
  · rw [congrArg AgentState.rank h_fst]
    exact congrArg Fin.val (h_pass.2.2.1 ▸ h_rd.2.1)
  · rw [congrArg AgentState.children h_fst]; exact h_pass.2.2.2.1 ▸ h_rd.2.2.1
  · rw [congrArg AgentState.leader h_fst]; exact h_pass.2.1 ▸ h_rd.2.2.2.1
  · rw [congrArg AgentState.role h_snd]; exact h_pass.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.2.1
  · rw [congrArg AgentState.resetcount h_snd]; exact h_pass.2.2.2.2.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.2.2.1
  · rw [congrArg AgentState.leader h_snd]; exact h_pass.2.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.2.2.2.1
  · rw [congrArg AgentState.delaytimer h_snd]; exact h_pass.2.2.2.2.2.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.2.2.2.2

set_option maxHeartbeats 4000000 in
theorem step_L_zero_L_pos
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 0 < Dmax)
    (C : Config (AgentState n) Opinion n)
    {u v : Fin n} (huv : u ≠ v)
    (hu_res : (C u).1.role = .Resetting) (hv_res : (C v).1.role = .Resetting)
    (hu_rc : (C u).1.resetcount = 0) (hv_rc : 0 < (C v).1.resetcount)
    (hu_L : (C u).1.leader = .L) (hv_L : (C v).1.leader = .L)
    (hu_dt : 1 < (C u).1.delaytimer) :
    let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := C.step P u v
    (C' u).1.role = .Resetting ∧
    (C' v).1.role = .Resetting ∧
    (C' u).1.resetcount = (C v).1.resetcount - 1 ∧
    (C' v).1.resetcount = (C v).1.resetcount - 1 ∧
    (C' u).1.leader = .L ∧
    (C' v).1.leader = .F ∧
    (C' u).1.delaytimer =
      (if (C v).1.resetcount = 1 then (C u).1.delaytimer - 1 else (C u).1.delaytimer) := by
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have h_rd := rankDeltaOSSR_L_zero_L_pos_trace (Rmax := Rmax) (Emax := Emax)
    (Dmax := Dmax) (hn := hn) hu_res hv_res hu_rc hv_rc hu_L hv_L hu_dt hDmax
  have h_not_both : ¬((rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1)).1.role = .Settled ∧
                      (rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1)).2.role = .Settled) := by
    intro ⟨h1, _⟩; rw [h_rd.1] at h1; exact Role.noConfusion h1
  have h_pass := transitionPEM_structural_passthrough (trank := Rmax) (Rmax := Rmax)
    (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn) (x₀ := (C u).2) (x₁ := (C v).2) h_not_both
  have h_fst := Config.step_fst_state P C huv
  have h_snd := Config.step_snd_state P C huv huv.symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [congrArg AgentState.role h_fst]; exact h_pass.1 ▸ h_rd.1
  · rw [congrArg AgentState.role h_snd]; exact h_pass.2.2.2.2.2.2.1 ▸ h_rd.2.1
  · rw [congrArg AgentState.resetcount h_fst]; exact h_pass.2.2.2.2.1 ▸ h_rd.2.2.1
  · rw [congrArg AgentState.resetcount h_snd]; exact h_pass.2.2.2.2.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.1
  · rw [congrArg AgentState.leader h_fst]; exact h_pass.2.1 ▸ h_rd.2.2.2.2.1
  · rw [congrArg AgentState.leader h_snd]; exact h_pass.2.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.2.2.1
  · rw [congrArg AgentState.delaytimer h_fst]; exact h_pass.2.2.2.2.2.1 ▸ h_rd.2.2.2.2.2.2

set_option maxHeartbeats 4000000 in
/-- Config.step lift of `rankDeltaOSSR_leader_dedup_step`: pair two L agents
(both R, both rc=0, both dt>1), second's leader becomes F, both dt decrease. -/
theorem step_leader_dedup
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {C : Config (AgentState n) Opinion n}
    {ℓ w : Fin n} (hℓw : ℓ ≠ w)
    (hℓ_res : (C ℓ).1.role = .Resetting) (hℓ_rc : (C ℓ).1.resetcount = 0)
    (hw_res : (C w).1.role = .Resetting) (hw_rc : (C w).1.resetcount = 0)
    (hℓ_L : (C ℓ).1.leader = .L) (hw_L : (C w).1.leader = .L)
    (hℓ_dt : 1 < (C ℓ).1.delaytimer) (hw_dt : 1 < (C w).1.delaytimer) :
    let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := C.step P ℓ w
    (C' ℓ).1.role = .Resetting ∧ (C' ℓ).1.resetcount = 0 ∧
    (C' ℓ).1.leader = .L ∧ (C' ℓ).1.delaytimer = (C ℓ).1.delaytimer - 1 ∧
    (C' w).1.role = .Resetting ∧ (C' w).1.resetcount = 0 ∧
    (C' w).1.leader = .F ∧ (C' w).1.delaytimer = (C w).1.delaytimer - 1 := by
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have h_rd := rankDeltaOSSR_leader_dedup_step (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
    (hn := hn) hℓ_res hℓ_rc hw_res hw_rc hℓ_L hw_L hℓ_dt hw_dt
  have h_not_both : ¬((rankDeltaOSSR Rmax Emax Dmax hn ((C ℓ).1, (C w).1)).1.role = .Settled ∧
                      (rankDeltaOSSR Rmax Emax Dmax hn ((C ℓ).1, (C w).1)).2.role = .Settled) := by
    intro ⟨h1, _⟩; rw [h_rd.1] at h1; exact Role.noConfusion h1
  have h_pass := transitionPEM_structural_passthrough (trank := Rmax) (Rmax := Rmax)
    (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn) (x₀ := (C ℓ).2) (x₁ := (C w).2) h_not_both
  have h_fst := Config.step_fst_state P C hℓw
  have h_snd := Config.step_snd_state P C hℓw hℓw.symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [congrArg AgentState.role h_fst]; exact h_pass.1 ▸ h_rd.1
  · rw [congrArg AgentState.resetcount h_fst]; exact h_pass.2.2.2.2.1 ▸ h_rd.2.1
  · rw [congrArg AgentState.leader h_fst]; exact h_pass.2.1 ▸ h_rd.2.2.2.1
  · rw [congrArg AgentState.delaytimer h_fst]; exact h_pass.2.2.2.2.2.1 ▸ h_rd.2.2.1
  · rw [congrArg AgentState.role h_snd]; exact h_pass.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.2.1
  · rw [congrArg AgentState.resetcount h_snd]; exact h_pass.2.2.2.2.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.2.2.1
  · rw [congrArg AgentState.leader h_snd]; exact h_pass.2.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.2.2.2.2
  · rw [congrArg AgentState.delaytimer h_snd]; exact h_pass.2.2.2.2.2.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.2.2.2.1

theorem step_leader_dedup_trace
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {C : Config (AgentState n) Opinion n}
    {ℓ w : Fin n} (hℓw : ℓ ≠ w)
    (hℓ_res : (C ℓ).1.role = .Resetting) (hℓ_rc : (C ℓ).1.resetcount = 0)
    (hw_res : (C w).1.role = .Resetting) (hw_rc : (C w).1.resetcount = 0)
    (hℓ_L : (C ℓ).1.leader = .L) (hw_L : (C w).1.leader = .L)
    (hℓ_dt : 1 < (C ℓ).1.delaytimer) (hw_dt : 1 < (C w).1.delaytimer) :
    let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := C.step P ℓ w
    (C' ℓ).1.role = .Resetting ∧
    (C' ℓ).1.resetcount = 0 ∧
    (C' ℓ).1.leader = .L ∧
    (C' ℓ).1.delaytimer = (C ℓ).1.delaytimer - 1 ∧
    (C' w).1.role = .Resetting ∧
    (C' w).1.resetcount = 0 ∧
    (C' w).1.leader = .F ∧
    (C' w).1.delaytimer = (C w).1.delaytimer - 1 ∧
    (∀ x : Fin n, x ≠ ℓ → x ≠ w → C' x = C x) := by
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have hstep :=
    step_leader_dedup
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      (C := C) (ℓ := ℓ) (w := w) hℓw
      hℓ_res hℓ_rc hw_res hw_rc hℓ_L hw_L hℓ_dt hw_dt
  refine ⟨hstep.1, hstep.2.1, hstep.2.2.1, hstep.2.2.2.1,
    hstep.2.2.2.2.1, hstep.2.2.2.2.2.1, hstep.2.2.2.2.2.2.1,
    hstep.2.2.2.2.2.2.2, ?_⟩
  intro x hxℓ hxw
  simp [Config.step, hℓw, hxℓ, hxw, P]

def resetLeaderCount (C : Config (AgentState n) Opinion n) : ℕ :=
  (Finset.univ.filter (fun w : Fin n =>
    (C w).1.role = .Resetting ∧ (C w).1.resetcount = 0 ∧ (C w).1.leader = .L)).card

theorem step_leader_dedup_resetLeaderCount_lt
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {C : Config (AgentState n) Opinion n}
    {ℓ w : Fin n} (hℓw : ℓ ≠ w)
    (hℓ_res : (C ℓ).1.role = .Resetting) (hℓ_rc : (C ℓ).1.resetcount = 0)
    (hw_res : (C w).1.role = .Resetting) (hw_rc : (C w).1.resetcount = 0)
    (hℓ_L : (C ℓ).1.leader = .L) (hw_L : (C w).1.leader = .L)
    (hℓ_dt : 1 < (C ℓ).1.delaytimer) (hw_dt : 1 < (C w).1.delaytimer) :
    let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    resetLeaderCount (C.step P ℓ w) < resetLeaderCount C := by
  classical
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  let C' : Config (AgentState n) Opinion n := C.step P ℓ w
  have hstep :=
    step_leader_dedup_trace
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      (C := C) (ℓ := ℓ) (w := w) hℓw
      hℓ_res hℓ_rc hw_res hw_rc hℓ_L hw_L hℓ_dt hw_dt
  set S := Finset.univ.filter (fun x : Fin n =>
    (C x).1.role = .Resetting ∧ (C x).1.resetcount = 0 ∧ (C x).1.leader = .L) with hS
  set S' := Finset.univ.filter (fun x : Fin n =>
    (C' x).1.role = .Resetting ∧ (C' x).1.resetcount = 0 ∧ (C' x).1.leader = .L) with hS'
  have hw_mem : w ∈ S := by
    rw [hS, Finset.mem_filter]
    exact ⟨Finset.mem_univ w, hw_res, hw_rc, hw_L⟩
  have hsub : S' ⊆ S.erase w := by
    intro x hx
    have hx_fields :
        (C' x).1.role = .Resetting ∧ (C' x).1.resetcount = 0 ∧
          (C' x).1.leader = .L := by
      rw [hS'] at hx
      exact (Finset.mem_filter.mp hx).2
    have hx_ne_w : x ≠ w := by
      intro hxw
      subst x
      rw [show (C' w).1.leader = .F from hstep.2.2.2.2.2.2.1] at hx_fields
      cases hx_fields.2.2
    have hx_mem_old : x ∈ S := by
      rw [hS, Finset.mem_filter]
      by_cases hxℓ : x = ℓ
      · subst x
        exact ⟨Finset.mem_univ ℓ, hℓ_res, hℓ_rc, hℓ_L⟩
      · have hx_old : C' x = C x := hstep.2.2.2.2.2.2.2.2 x hxℓ hx_ne_w
        rw [hx_old] at hx_fields
        exact ⟨Finset.mem_univ x, hx_fields⟩
    exact Finset.mem_erase.mpr ⟨hx_ne_w, hx_mem_old⟩
  have hle : S'.card ≤ (S.erase w).card := Finset.card_le_card hsub
  have herase : (S.erase w).card = S.card - 1 := Finset.card_erase_of_mem hw_mem
  have hlt : S'.card < S.card := by
    rw [herase] at hle
    have hpos : 0 < S.card := Finset.card_pos.mpr ⟨w, hw_mem⟩
    omega
  change resetLeaderCount C' < resetLeaderCount C
  unfold resetLeaderCount
  rw [← hS, ← hS']
  exact hlt

theorem drain_pair_rc
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 0 < Dmax)
    (C : Config (AgentState n) Opinion n)
    {u v : Fin n} (huv : u ≠ v)
    (hu_res : (C u).1.role = .Resetting) (hv_res : (C v).1.role = .Resetting)
    (hu_rc : 0 < (C u).1.resetcount) (hv_rc : 0 < (C v).1.resetcount) :
    let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    ∃ L : List (Fin n × Fin n),
      (runPairs P C L u).1.role = .Resetting ∧
      (runPairs P C L u).1.resetcount = 0 ∧
      (runPairs P C L v).1.role = .Resetting ∧
      (runPairs P C L v).1.resetcount = 0 ∧
      (runPairs P C L u).1.leader = (C u).1.leader ∧
      ∀ w : Fin n, w ≠ u → w ≠ v → runPairs P C L w = C w := by
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  -- Strong induction on `max (C u).rc (C v).rc`.
  suffices drain : ∀ k (C' : Config (AgentState n) Opinion n),
      (C' u).1.role = .Resetting → (C' v).1.role = .Resetting →
      0 < (C' u).1.resetcount → 0 < (C' v).1.resetcount →
      Nat.max ((C' u).1.resetcount) ((C' v).1.resetcount) ≤ k →
      ∃ L,
        (runPairs P C' L u).1.role = .Resetting ∧
        (runPairs P C' L u).1.resetcount = 0 ∧
        (runPairs P C' L v).1.role = .Resetting ∧
        (runPairs P C' L v).1.resetcount = 0 ∧
        (runPairs P C' L u).1.leader = (C' u).1.leader ∧
        ∀ w : Fin n, w ≠ u → w ≠ v → runPairs P C' L w = C' w by
    exact drain (Nat.max ((C u).1.resetcount) ((C v).1.resetcount))
      C hu_res hv_res hu_rc hv_rc le_rfl
  intro k
  induction k with
  | zero =>
    intros C' _ _ hu_rc' _ hmax
    exfalso
    have : (C' u).1.resetcount ≤ Nat.max ((C' u).1.resetcount) ((C' v).1.resetcount) :=
      Nat.le_max_left _ _
    omega
  | succ k ih =>
    intros C' hu_res' hv_res' hu_rc' hv_rc' hmax
    have h_step := step_both_rc_pos (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hDmax C' huv hu_res' hv_res' hu_rc' hv_rc'
    -- Unpack h_step (avoids `set C₁ := ...` issues with rewrites)
    have hu_role₁ : (C'.step P u v u).1.role = .Resetting := h_step.1
    have hv_role₁ : (C'.step P u v v).1.role = .Resetting := h_step.2.1
    have hu_rc₁_eq : (C'.step P u v u).1.resetcount =
        Nat.max ((C' u).1.resetcount - 1) ((C' v).1.resetcount - 1) := h_step.2.2.1
    have hv_rc₁_eq : (C'.step P u v v).1.resetcount =
        Nat.max ((C' u).1.resetcount - 1) ((C' v).1.resetcount - 1) := h_step.2.2.2.1
    have hu_leader₁ : (C'.step P u v u).1.leader = (C' u).1.leader :=
      h_step.2.2.2.2
    have h_others : ∀ w, w ≠ u → w ≠ v → C'.step P u v w = C' w := by
      intro w hwu hwv
      simp [Config.step, huv, hwu, hwv]
    have hM_le : Nat.max ((C'.step P u v u).1.resetcount) ((C'.step P u v v).1.resetcount)
                  ≤ k := by
      have hu_pred_le : (C' u).1.resetcount - 1 ≤ k := by
        have hu_le_succ : (C' u).1.resetcount ≤ k + 1 :=
          Nat.le_trans (Nat.le_max_left ((C' u).1.resetcount) ((C' v).1.resetcount)) hmax
        omega
      have hv_pred_le : (C' v).1.resetcount - 1 ≤ k := by
        have hv_le_succ : (C' v).1.resetcount ≤ k + 1 :=
          Nat.le_trans (Nat.le_max_right ((C' u).1.resetcount) ((C' v).1.resetcount)) hmax
        omega
      have hpred :
          Nat.max ((C' u).1.resetcount - 1) ((C' v).1.resetcount - 1) ≤ k :=
        max_le hu_pred_le hv_pred_le
      rw [hu_rc₁_eq, hv_rc₁_eq]
      exact max_le hpred hpred
    by_cases hdone :
        Nat.max ((C'.step P u v u).1.resetcount) ((C'.step P u v v).1.resetcount) = 0
    · -- Both rc on C'.step P u v are 0; one step suffices.
      have hu_zero : (C'.step P u v u).1.resetcount = 0 := by
        have hle := Nat.le_max_left ((C'.step P u v u).1.resetcount)
          ((C'.step P u v v).1.resetcount)
        have hdone' : max ((C'.step P u v u).1.resetcount)
            ((C'.step P u v v).1.resetcount) = 0 := by
          simpa using hdone
        exact Nat.eq_zero_of_le_zero (Nat.le_trans hle (le_of_eq hdone'))
      have hv_zero : (C'.step P u v v).1.resetcount = 0 := by
        have hle := Nat.le_max_right ((C'.step P u v u).1.resetcount)
          ((C'.step P u v v).1.resetcount)
        have hdone' : max ((C'.step P u v u).1.resetcount)
            ((C'.step P u v v).1.resetcount) = 0 := by
          simpa using hdone
        exact Nat.eq_zero_of_le_zero (Nat.le_trans hle (le_of_eq hdone'))
      refine ⟨[(u, v)], ?_, ?_, ?_, ?_, ?_, ?_⟩
      · show (runPairs P C' [(u, v)] u).1.role = .Resetting
        simp [runPairs]; exact hu_role₁
      · show (runPairs P C' [(u, v)] u).1.resetcount = 0
        simp [runPairs]; exact hu_zero
      · show (runPairs P C' [(u, v)] v).1.role = .Resetting
        simp [runPairs]; exact hv_role₁
      · show (runPairs P C' [(u, v)] v).1.resetcount = 0
        simp [runPairs]; exact hv_zero
      · show (runPairs P C' [(u, v)] u).1.leader = (C' u).1.leader
        simp [runPairs]; exact hu_leader₁
      · intro w hwu hwv
        show runPairs P C' [(u, v)] w = C' w
        simp [runPairs]; exact h_others w hwu hwv
    · -- Still positive after one step; recurse via ih.
      have hu_rc₁ : 0 < (C'.step P u v u).1.resetcount := by
        have hpos : 0 < Nat.max ((C'.step P u v u).1.resetcount)
            ((C'.step P u v v).1.resetcount) :=
          Nat.pos_of_ne_zero hdone
        simpa [hu_rc₁_eq, hv_rc₁_eq] using hpos
      have hv_rc₁ : 0 < (C'.step P u v v).1.resetcount := by
        have hpos : 0 < Nat.max ((C'.step P u v u).1.resetcount)
            ((C'.step P u v v).1.resetcount) :=
          Nat.pos_of_ne_zero hdone
        simpa [hu_rc₁_eq, hv_rc₁_eq] using hpos
      obtain ⟨Ltail, hu_role_t, hu_rc_t, hv_role_t, hv_rc_t, hu_leader_t, h_others_t⟩ :=
        ih (C'.step P u v) hu_role₁ hv_role₁ hu_rc₁ hv_rc₁ hM_le
      refine ⟨[(u, v)] ++ Ltail, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [runPairs_append]; show (runPairs P (C'.step P u v) Ltail u).1.role = .Resetting
        simp [runPairs]; exact hu_role_t
      · rw [runPairs_append]; show (runPairs P (C'.step P u v) Ltail u).1.resetcount = 0
        simp [runPairs]; exact hu_rc_t
      · rw [runPairs_append]; show (runPairs P (C'.step P u v) Ltail v).1.role = .Resetting
        simp [runPairs]; exact hv_role_t
      · rw [runPairs_append]; show (runPairs P (C'.step P u v) Ltail v).1.resetcount = 0
        simp [runPairs]; exact hv_rc_t
      · rw [runPairs_append]
        show (runPairs P (C'.step P u v) Ltail u).1.leader = (C' u).1.leader
        rw [hu_leader_t]
        exact hu_leader₁
      · intro w hwu hwv
        rw [runPairs_append]
        change runPairs P (C'.step P u v) Ltail w = C' w
        rw [h_others_t w hwu hwv]
        exact h_others w hwu hwv

set_option maxHeartbeats 8000000 in
theorem drain_pair_rc_LF
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 0 < Dmax)
    (C : Config (AgentState n) Opinion n)
    {u v : Fin n} (huv : u ≠ v)
    (hu_res : (C u).1.role = .Resetting) (hv_res : (C v).1.role = .Resetting)
    (hu_rc : 0 < (C u).1.resetcount) (hv_rc : 0 < (C v).1.resetcount)
    (hu_L : (C u).1.leader = .L) (hv_F : (C v).1.leader = .F) :
    let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    ∃ L : List (Fin n × Fin n),
      (runPairs P C L u).1.role = .Resetting ∧
      (runPairs P C L u).1.resetcount = 0 ∧
      (runPairs P C L u).1.leader = .L ∧
      (runPairs P C L v).1.role = .Resetting ∧
      (runPairs P C L v).1.resetcount = 0 ∧
      (runPairs P C L v).1.leader = .F ∧
      ∀ w : Fin n, w ≠ u → w ≠ v → runPairs P C L w = C w := by
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  suffices drain : ∀ k (C' : Config (AgentState n) Opinion n),
      (C' u).1.role = .Resetting → (C' v).1.role = .Resetting →
      0 < (C' u).1.resetcount → 0 < (C' v).1.resetcount →
      (C' u).1.leader = .L → (C' v).1.leader = .F →
      Nat.max ((C' u).1.resetcount) ((C' v).1.resetcount) ≤ k →
      ∃ L,
        (runPairs P C' L u).1.role = .Resetting ∧
        (runPairs P C' L u).1.resetcount = 0 ∧
        (runPairs P C' L u).1.leader = .L ∧
        (runPairs P C' L v).1.role = .Resetting ∧
        (runPairs P C' L v).1.resetcount = 0 ∧
        (runPairs P C' L v).1.leader = .F ∧
        ∀ w : Fin n, w ≠ u → w ≠ v → runPairs P C' L w = C' w by
    exact drain (Nat.max ((C u).1.resetcount) ((C v).1.resetcount))
      C hu_res hv_res hu_rc hv_rc hu_L hv_F le_rfl
  intro k
  induction k with
  | zero =>
    intros C' _ _ hu_rc' _ _ _ hmax
    exfalso
    have : (C' u).1.resetcount ≤ Nat.max ((C' u).1.resetcount) ((C' v).1.resetcount) :=
      Nat.le_max_left _ _
    omega
  | succ k ih =>
    intros C' hu_res' hv_res' hu_rc' hv_rc' hu_L' hv_F' hmax
    have h_step := step_both_rc_pos_LF (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      (hn := hn) hDmax C' huv hu_res' hv_res' hu_rc' hv_rc' hu_L' hv_F'
    have hu_role₁ : (C'.step P u v u).1.role = .Resetting := h_step.1
    have hv_role₁ : (C'.step P u v v).1.role = .Resetting := h_step.2.1
    have hu_rc₁_eq : (C'.step P u v u).1.resetcount =
        Nat.max ((C' u).1.resetcount - 1) ((C' v).1.resetcount - 1) := h_step.2.2.1
    have hv_rc₁_eq : (C'.step P u v v).1.resetcount =
        Nat.max ((C' u).1.resetcount - 1) ((C' v).1.resetcount - 1) := h_step.2.2.2.1
    have hu_L₁ : (C'.step P u v u).1.leader = .L := h_step.2.2.2.2.1
    have hv_F₁ : (C'.step P u v v).1.leader = .F := h_step.2.2.2.2.2
    have h_others : ∀ w, w ≠ u → w ≠ v → C'.step P u v w = C' w := by
      intro w hwu hwv
      simp [Config.step, huv, hwu, hwv]
    have hM_le : Nat.max ((C'.step P u v u).1.resetcount) ((C'.step P u v v).1.resetcount)
                  ≤ k := by
      have hu_pred_le : (C' u).1.resetcount - 1 ≤ k := by
        have hu_le_succ : (C' u).1.resetcount ≤ k + 1 :=
          Nat.le_trans (Nat.le_max_left ((C' u).1.resetcount) ((C' v).1.resetcount)) hmax
        omega
      have hv_pred_le : (C' v).1.resetcount - 1 ≤ k := by
        have hv_le_succ : (C' v).1.resetcount ≤ k + 1 :=
          Nat.le_trans (Nat.le_max_right ((C' u).1.resetcount) ((C' v).1.resetcount)) hmax
        omega
      have hpred :
          Nat.max ((C' u).1.resetcount - 1) ((C' v).1.resetcount - 1) ≤ k :=
        max_le hu_pred_le hv_pred_le
      rw [hu_rc₁_eq, hv_rc₁_eq]
      exact max_le hpred hpred
    by_cases hdone :
        Nat.max ((C'.step P u v u).1.resetcount) ((C'.step P u v v).1.resetcount) = 0
    · have hu_zero : (C'.step P u v u).1.resetcount = 0 := by
        have hle := Nat.le_max_left ((C'.step P u v u).1.resetcount)
          ((C'.step P u v v).1.resetcount)
        exact Nat.eq_zero_of_le_zero (Nat.le_trans hle (le_of_eq hdone))
      have hv_zero : (C'.step P u v v).1.resetcount = 0 := by
        have hle := Nat.le_max_right ((C'.step P u v u).1.resetcount)
          ((C'.step P u v v).1.resetcount)
        exact Nat.eq_zero_of_le_zero (Nat.le_trans hle (le_of_eq hdone))
      refine ⟨[(u, v)], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · show (runPairs P C' [(u, v)] u).1.role = .Resetting
        simp [runPairs]; exact hu_role₁
      · show (runPairs P C' [(u, v)] u).1.resetcount = 0
        simp [runPairs]; exact hu_zero
      · show (runPairs P C' [(u, v)] u).1.leader = .L
        simp [runPairs]; exact hu_L₁
      · show (runPairs P C' [(u, v)] v).1.role = .Resetting
        simp [runPairs]; exact hv_role₁
      · show (runPairs P C' [(u, v)] v).1.resetcount = 0
        simp [runPairs]; exact hv_zero
      · show (runPairs P C' [(u, v)] v).1.leader = .F
        simp [runPairs]; exact hv_F₁
      · intro w hwu hwv
        show runPairs P C' [(u, v)] w = C' w
        simp [runPairs]; exact h_others w hwu hwv
    · have hu_rc₁ : 0 < (C'.step P u v u).1.resetcount := by
        have hpos : 0 < Nat.max ((C'.step P u v u).1.resetcount)
            ((C'.step P u v v).1.resetcount) :=
          Nat.pos_of_ne_zero hdone
        simpa [hu_rc₁_eq, hv_rc₁_eq] using hpos
      have hv_rc₁ : 0 < (C'.step P u v v).1.resetcount := by
        have hpos : 0 < Nat.max ((C'.step P u v u).1.resetcount)
            ((C'.step P u v v).1.resetcount) :=
          Nat.pos_of_ne_zero hdone
        simpa [hu_rc₁_eq, hv_rc₁_eq] using hpos
      obtain ⟨Ltail, hu_role_t, hu_rc_t, hu_L_t, hv_role_t, hv_rc_t, hv_F_t, h_others_t⟩ :=
        ih (C'.step P u v) hu_role₁ hv_role₁ hu_rc₁ hv_rc₁ hu_L₁ hv_F₁ hM_le
      refine ⟨[(u, v)] ++ Ltail, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [runPairs_append]; show (runPairs P (C'.step P u v) Ltail u).1.role = .Resetting
        simp [runPairs]; exact hu_role_t
      · rw [runPairs_append]; show (runPairs P (C'.step P u v) Ltail u).1.resetcount = 0
        simp [runPairs]; exact hu_rc_t
      · rw [runPairs_append]; show (runPairs P (C'.step P u v) Ltail u).1.leader = .L
        simp [runPairs]; exact hu_L_t
      · rw [runPairs_append]; show (runPairs P (C'.step P u v) Ltail v).1.role = .Resetting
        simp [runPairs]; exact hv_role_t
      · rw [runPairs_append]; show (runPairs P (C'.step P u v) Ltail v).1.resetcount = 0
        simp [runPairs]; exact hv_rc_t
      · rw [runPairs_append]; show (runPairs P (C'.step P u v) Ltail v).1.leader = .F
        simp [runPairs]; exact hv_F_t
      · intro w hwu hwv
        rw [runPairs_append]
        change runPairs P (C'.step P u v) Ltail w = C' w
        rw [h_others_t w hwu hwv]
        exact h_others w hwu hwv

set_option maxHeartbeats 8000000 in
theorem drain_pair_rc_FF
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 0 < Dmax)
    (C : Config (AgentState n) Opinion n)
    {u v : Fin n} (huv : u ≠ v)
    (hu_res : (C u).1.role = .Resetting) (hv_res : (C v).1.role = .Resetting)
    (hu_rc : 0 < (C u).1.resetcount) (hv_rc : 0 < (C v).1.resetcount)
    (hu_F : (C u).1.leader = .F) (hv_F : (C v).1.leader = .F) :
    let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    ∃ L : List (Fin n × Fin n),
      (runPairs P C L u).1.role = .Resetting ∧
      (runPairs P C L u).1.resetcount = 0 ∧
      (runPairs P C L u).1.leader = .F ∧
      (runPairs P C L v).1.role = .Resetting ∧
      (runPairs P C L v).1.resetcount = 0 ∧
      (runPairs P C L v).1.leader = .F ∧
      ∀ w : Fin n, w ≠ u → w ≠ v → runPairs P C L w = C w := by
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  suffices drain : ∀ k (C' : Config (AgentState n) Opinion n),
      (C' u).1.role = .Resetting → (C' v).1.role = .Resetting →
      0 < (C' u).1.resetcount → 0 < (C' v).1.resetcount →
      (C' u).1.leader = .F → (C' v).1.leader = .F →
      Nat.max ((C' u).1.resetcount) ((C' v).1.resetcount) ≤ k →
      ∃ L,
        (runPairs P C' L u).1.role = .Resetting ∧
        (runPairs P C' L u).1.resetcount = 0 ∧
        (runPairs P C' L u).1.leader = .F ∧
        (runPairs P C' L v).1.role = .Resetting ∧
        (runPairs P C' L v).1.resetcount = 0 ∧
        (runPairs P C' L v).1.leader = .F ∧
        ∀ w : Fin n, w ≠ u → w ≠ v → runPairs P C' L w = C' w by
    exact drain (Nat.max ((C u).1.resetcount) ((C v).1.resetcount))
      C hu_res hv_res hu_rc hv_rc hu_F hv_F le_rfl
  intro k
  induction k with
  | zero =>
    intros C' _ _ hu_rc' _ _ _ hmax
    exfalso
    have : (C' u).1.resetcount ≤ Nat.max ((C' u).1.resetcount) ((C' v).1.resetcount) :=
      Nat.le_max_left _ _
    omega
  | succ k ih =>
    intros C' hu_res' hv_res' hu_rc' hv_rc' hu_F' hv_F' hmax
    have h_step := step_both_rc_pos_FF (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      (hn := hn) hDmax C' huv hu_res' hv_res' hu_rc' hv_rc' hu_F' hv_F'
    have hu_role₁ : (C'.step P u v u).1.role = .Resetting := h_step.1
    have hv_role₁ : (C'.step P u v v).1.role = .Resetting := h_step.2.1
    have hu_rc₁_eq : (C'.step P u v u).1.resetcount =
        Nat.max ((C' u).1.resetcount - 1) ((C' v).1.resetcount - 1) := h_step.2.2.1
    have hv_rc₁_eq : (C'.step P u v v).1.resetcount =
        Nat.max ((C' u).1.resetcount - 1) ((C' v).1.resetcount - 1) := h_step.2.2.2.1
    have hu_F₁ : (C'.step P u v u).1.leader = .F := h_step.2.2.2.2.1
    have hv_F₁ : (C'.step P u v v).1.leader = .F := h_step.2.2.2.2.2
    have h_others : ∀ w, w ≠ u → w ≠ v → C'.step P u v w = C' w := by
      intro w hwu hwv
      simp [Config.step, huv, hwu, hwv]
    have hM_le : Nat.max ((C'.step P u v u).1.resetcount) ((C'.step P u v v).1.resetcount)
                  ≤ k := by
      have hu_pred_le : (C' u).1.resetcount - 1 ≤ k := by
        have hu_le_succ : (C' u).1.resetcount ≤ k + 1 :=
          Nat.le_trans (Nat.le_max_left ((C' u).1.resetcount) ((C' v).1.resetcount)) hmax
        omega
      have hv_pred_le : (C' v).1.resetcount - 1 ≤ k := by
        have hv_le_succ : (C' v).1.resetcount ≤ k + 1 :=
          Nat.le_trans (Nat.le_max_right ((C' u).1.resetcount) ((C' v).1.resetcount)) hmax
        omega
      have hpred :
          Nat.max ((C' u).1.resetcount - 1) ((C' v).1.resetcount - 1) ≤ k :=
        max_le hu_pred_le hv_pred_le
      rw [hu_rc₁_eq, hv_rc₁_eq]
      exact max_le hpred hpred
    by_cases hdone :
        Nat.max ((C'.step P u v u).1.resetcount) ((C'.step P u v v).1.resetcount) = 0
    · have hu_zero : (C'.step P u v u).1.resetcount = 0 := by
        have hle := Nat.le_max_left ((C'.step P u v u).1.resetcount)
          ((C'.step P u v v).1.resetcount)
        exact Nat.eq_zero_of_le_zero (Nat.le_trans hle (le_of_eq hdone))
      have hv_zero : (C'.step P u v v).1.resetcount = 0 := by
        have hle := Nat.le_max_right ((C'.step P u v u).1.resetcount)
          ((C'.step P u v v).1.resetcount)
        exact Nat.eq_zero_of_le_zero (Nat.le_trans hle (le_of_eq hdone))
      refine ⟨[(u, v)], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · show (runPairs P C' [(u, v)] u).1.role = .Resetting
        simp [runPairs]; exact hu_role₁
      · show (runPairs P C' [(u, v)] u).1.resetcount = 0
        simp [runPairs]; exact hu_zero
      · show (runPairs P C' [(u, v)] u).1.leader = .F
        simp [runPairs]; exact hu_F₁
      · show (runPairs P C' [(u, v)] v).1.role = .Resetting
        simp [runPairs]; exact hv_role₁
      · show (runPairs P C' [(u, v)] v).1.resetcount = 0
        simp [runPairs]; exact hv_zero
      · show (runPairs P C' [(u, v)] v).1.leader = .F
        simp [runPairs]; exact hv_F₁
      · intro w hwu hwv
        show runPairs P C' [(u, v)] w = C' w
        simp [runPairs]; exact h_others w hwu hwv
    · have hu_rc₁ : 0 < (C'.step P u v u).1.resetcount := by
        have hpos : 0 < Nat.max ((C'.step P u v u).1.resetcount)
            ((C'.step P u v v).1.resetcount) :=
          Nat.pos_of_ne_zero hdone
        simpa [hu_rc₁_eq, hv_rc₁_eq] using hpos
      have hv_rc₁ : 0 < (C'.step P u v v).1.resetcount := by
        have hpos : 0 < Nat.max ((C'.step P u v u).1.resetcount)
            ((C'.step P u v v).1.resetcount) :=
          Nat.pos_of_ne_zero hdone
        simpa [hu_rc₁_eq, hv_rc₁_eq] using hpos
      obtain ⟨Ltail, hu_role_t, hu_rc_t, hu_F_t, hv_role_t, hv_rc_t, hv_F_t, h_others_t⟩ :=
        ih (C'.step P u v) hu_role₁ hv_role₁ hu_rc₁ hv_rc₁ hu_F₁ hv_F₁ hM_le
      refine ⟨[(u, v)] ++ Ltail, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [runPairs_append]; show (runPairs P (C'.step P u v) Ltail u).1.role = .Resetting
        simp [runPairs]; exact hu_role_t
      · rw [runPairs_append]; show (runPairs P (C'.step P u v) Ltail u).1.resetcount = 0
        simp [runPairs]; exact hu_rc_t
      · rw [runPairs_append]; show (runPairs P (C'.step P u v) Ltail u).1.leader = .F
        simp [runPairs]; exact hu_F_t
      · rw [runPairs_append]; show (runPairs P (C'.step P u v) Ltail v).1.role = .Resetting
        simp [runPairs]; exact hv_role_t
      · rw [runPairs_append]; show (runPairs P (C'.step P u v) Ltail v).1.resetcount = 0
        simp [runPairs]; exact hv_rc_t
      · rw [runPairs_append]; show (runPairs P (C'.step P u v) Ltail v).1.leader = .F
        simp [runPairs]; exact hv_F_t
      · intro w hwu hwv
        rw [runPairs_append]
        change runPairs P (C'.step P u v) Ltail w = C' w
        rw [h_others_t w hwu hwv]
        exact h_others w hwu hwv

set_option maxHeartbeats 8000000 in
theorem drain_pair_rc_LF_with_u_delay
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 1 < Dmax)
    (C : Config (AgentState n) Opinion n)
    {u v : Fin n} (huv : u ≠ v)
    (hu_res : (C u).1.role = .Resetting) (hv_res : (C v).1.role = .Resetting)
    (hu_rc : 0 < (C u).1.resetcount) (hv_rc : 0 < (C v).1.resetcount)
    (hu_L : (C u).1.leader = .L) (hv_F : (C v).1.leader = .F) :
    let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    ∃ L : List (Fin n × Fin n),
      (runPairs P C L u).1.role = .Resetting ∧
      (runPairs P C L u).1.resetcount = 0 ∧
      (runPairs P C L u).1.leader = .L ∧
      (runPairs P C L u).1.delaytimer = Dmax ∧
      (runPairs P C L v).1.role = .Resetting ∧
      (runPairs P C L v).1.resetcount = 0 ∧
      (runPairs P C L v).1.leader = .F ∧
      ∀ w : Fin n, w ≠ u → w ≠ v → runPairs P C L w = C w := by
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  suffices drain : ∀ k (C' : Config (AgentState n) Opinion n),
      (C' u).1.role = .Resetting → (C' v).1.role = .Resetting →
      0 < (C' u).1.resetcount → 0 < (C' v).1.resetcount →
      (C' u).1.leader = .L → (C' v).1.leader = .F →
      Nat.max ((C' u).1.resetcount) ((C' v).1.resetcount) ≤ k →
      ∃ L,
        (runPairs P C' L u).1.role = .Resetting ∧
        (runPairs P C' L u).1.resetcount = 0 ∧
        (runPairs P C' L u).1.leader = .L ∧
        (runPairs P C' L u).1.delaytimer = Dmax ∧
        (runPairs P C' L v).1.role = .Resetting ∧
        (runPairs P C' L v).1.resetcount = 0 ∧
        (runPairs P C' L v).1.leader = .F ∧
        ∀ w : Fin n, w ≠ u → w ≠ v → runPairs P C' L w = C' w by
    exact drain (Nat.max ((C u).1.resetcount) ((C v).1.resetcount))
      C hu_res hv_res hu_rc hv_rc hu_L hv_F le_rfl
  intro k
  induction k with
  | zero =>
    intros C' _ _ hu_rc' _ _ _ hmax
    exfalso
    have : (C' u).1.resetcount ≤ Nat.max ((C' u).1.resetcount) ((C' v).1.resetcount) :=
      Nat.le_max_left _ _
    omega
  | succ k ih =>
    intros C' hu_res' hv_res' hu_rc' hv_rc' hu_L' hv_F' hmax
    have h_step := step_both_rc_pos_LF (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      (hn := hn) (by omega : 0 < Dmax) C' huv hu_res' hv_res' hu_rc' hv_rc' hu_L' hv_F'
    have hu_role₁ : (C'.step P u v u).1.role = .Resetting := h_step.1
    have hv_role₁ : (C'.step P u v v).1.role = .Resetting := h_step.2.1
    have hu_rc₁_eq : (C'.step P u v u).1.resetcount =
        Nat.max ((C' u).1.resetcount - 1) ((C' v).1.resetcount - 1) := h_step.2.2.1
    have hv_rc₁_eq : (C'.step P u v v).1.resetcount =
        Nat.max ((C' u).1.resetcount - 1) ((C' v).1.resetcount - 1) := h_step.2.2.2.1
    have hu_L₁ : (C'.step P u v u).1.leader = .L := h_step.2.2.2.2.1
    have hv_F₁ : (C'.step P u v v).1.leader = .F := h_step.2.2.2.2.2
    have h_others : ∀ w, w ≠ u → w ≠ v → C'.step P u v w = C' w := by
      intro w hwu hwv
      simp [Config.step, huv, hwu, hwv]
    have hM_le : Nat.max ((C'.step P u v u).1.resetcount) ((C'.step P u v v).1.resetcount)
                  ≤ k := by
      have hu_pred_le : (C' u).1.resetcount - 1 ≤ k := by
        have hu_le_succ : (C' u).1.resetcount ≤ k + 1 :=
          Nat.le_trans (Nat.le_max_left ((C' u).1.resetcount) ((C' v).1.resetcount)) hmax
        omega
      have hv_pred_le : (C' v).1.resetcount - 1 ≤ k := by
        have hv_le_succ : (C' v).1.resetcount ≤ k + 1 :=
          Nat.le_trans (Nat.le_max_right ((C' u).1.resetcount) ((C' v).1.resetcount)) hmax
        omega
      have hpred :
          Nat.max ((C' u).1.resetcount - 1) ((C' v).1.resetcount - 1) ≤ k :=
        max_le hu_pred_le hv_pred_le
      rw [hu_rc₁_eq, hv_rc₁_eq]
      exact max_le hpred hpred
    by_cases hdone :
        Nat.max ((C'.step P u v u).1.resetcount) ((C'.step P u v v).1.resetcount) = 0
    · have hu_zero : (C'.step P u v u).1.resetcount = 0 := by
        have hle := Nat.le_max_left ((C'.step P u v u).1.resetcount)
          ((C'.step P u v v).1.resetcount)
        exact Nat.eq_zero_of_le_zero (Nat.le_trans hle (le_of_eq hdone))
      have hv_zero : (C'.step P u v v).1.resetcount = 0 := by
        have hle := Nat.le_max_right ((C'.step P u v u).1.resetcount)
          ((C'.step P u v v).1.resetcount)
        exact Nat.eq_zero_of_le_zero (Nat.le_trans hle (le_of_eq hdone))
      have hnew : Nat.max ((C' u).1.resetcount - 1) ((C' v).1.resetcount - 1) = 0 := by
        have hdone' := hdone
        rw [hu_rc₁_eq, hv_rc₁_eq] at hdone'
        simpa using hdone'
      have hu_delay₁ : (C'.step P u v u).1.delaytimer = Dmax :=
        step_both_rc_pos_fst_delay_final
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          (by omega : 0 < Dmax) C' huv hu_res' hv_res' hu_rc' hv_rc' hnew
      refine ⟨[(u, v)], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · show (runPairs P C' [(u, v)] u).1.role = .Resetting
        simp [runPairs]; exact hu_role₁
      · show (runPairs P C' [(u, v)] u).1.resetcount = 0
        simp [runPairs]; exact hu_zero
      · show (runPairs P C' [(u, v)] u).1.leader = .L
        simp [runPairs]; exact hu_L₁
      · show (runPairs P C' [(u, v)] u).1.delaytimer = Dmax
        simp [runPairs]; rw [hu_delay₁]
      · show (runPairs P C' [(u, v)] v).1.role = .Resetting
        simp [runPairs]; exact hv_role₁
      · show (runPairs P C' [(u, v)] v).1.resetcount = 0
        simp [runPairs]; exact hv_zero
      · show (runPairs P C' [(u, v)] v).1.leader = .F
        simp [runPairs]; exact hv_F₁
      · intro w hwu hwv
        show runPairs P C' [(u, v)] w = C' w
        simp [runPairs]; exact h_others w hwu hwv
    · have hu_rc₁ : 0 < (C'.step P u v u).1.resetcount := by
        have hpos : 0 < Nat.max ((C'.step P u v u).1.resetcount)
            ((C'.step P u v v).1.resetcount) :=
          Nat.pos_of_ne_zero hdone
        simpa [hu_rc₁_eq, hv_rc₁_eq] using hpos
      have hv_rc₁ : 0 < (C'.step P u v v).1.resetcount := by
        have hpos : 0 < Nat.max ((C'.step P u v u).1.resetcount)
            ((C'.step P u v v).1.resetcount) :=
          Nat.pos_of_ne_zero hdone
        simpa [hu_rc₁_eq, hv_rc₁_eq] using hpos
      obtain ⟨Ltail, hu_role_t, hu_rc_t, hu_L_t, hu_dt_t,
          hv_role_t, hv_rc_t, hv_F_t, h_others_t⟩ :=
        ih (C'.step P u v) hu_role₁ hv_role₁ hu_rc₁ hv_rc₁ hu_L₁ hv_F₁ hM_le
      refine ⟨[(u, v)] ++ Ltail, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [runPairs_append]; show (runPairs P (C'.step P u v) Ltail u).1.role = .Resetting
        simp [runPairs]; exact hu_role_t
      · rw [runPairs_append]; show (runPairs P (C'.step P u v) Ltail u).1.resetcount = 0
        simp [runPairs]; exact hu_rc_t
      · rw [runPairs_append]; show (runPairs P (C'.step P u v) Ltail u).1.leader = .L
        simp [runPairs]; exact hu_L_t
      · rw [runPairs_append]; show (runPairs P (C'.step P u v) Ltail u).1.delaytimer = Dmax
        simp [runPairs]; exact hu_dt_t
      · rw [runPairs_append]; show (runPairs P (C'.step P u v) Ltail v).1.role = .Resetting
        simp [runPairs]; exact hv_role_t
      · rw [runPairs_append]; show (runPairs P (C'.step P u v) Ltail v).1.resetcount = 0
        simp [runPairs]; exact hv_rc_t
      · rw [runPairs_append]; show (runPairs P (C'.step P u v) Ltail v).1.leader = .F
        simp [runPairs]; exact hv_F_t
      · intro w hwu hwv
        rw [runPairs_append]
        change runPairs P (C'.step P u v) Ltail w = C' w
        rw [h_others_t w hwu hwv]
        exact h_others w hwu hwv

set_option maxHeartbeats 8000000 in
theorem drain_pair_rc_LL_to_LF_zero_with_u_delay
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 1 < Dmax)
    (C : Config (AgentState n) Opinion n)
    {u v : Fin n} (huv : u ≠ v)
    (hu_res : (C u).1.role = .Resetting) (hv_res : (C v).1.role = .Resetting)
    (hu_rc : 0 < (C u).1.resetcount) (hv_rc : 0 < (C v).1.resetcount)
    (hu_L : (C u).1.leader = .L) (hv_L : (C v).1.leader = .L) :
    let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    ∃ L : List (Fin n × Fin n),
      (runPairs P C L u).1.role = .Resetting ∧
      (runPairs P C L u).1.resetcount = 0 ∧
      (runPairs P C L u).1.leader = .L ∧
      (runPairs P C L u).1.delaytimer = Dmax ∧
      (runPairs P C L v).1.role = .Resetting ∧
      (runPairs P C L v).1.resetcount = 0 ∧
      (runPairs P C L v).1.leader = .F ∧
      ∀ w : Fin n, w ≠ u → w ≠ v → runPairs P C L w = C w := by
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have hstep := step_both_rc_pos_LL
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    (by omega : 0 < Dmax) C huv hu_res hv_res hu_rc hv_rc hu_L hv_L
  let C₁ : Config (AgentState n) Opinion n := C.step P u v
  have hu_role₁ : (C₁ u).1.role = .Resetting := by
    simpa [C₁, P] using hstep.1
  have hv_role₁ : (C₁ v).1.role = .Resetting := by
    simpa [C₁, P] using hstep.2.1
  have hu_rc₁ : (C₁ u).1.resetcount =
      Nat.max ((C u).1.resetcount - 1) ((C v).1.resetcount - 1) := by
    simpa [C₁, P] using hstep.2.2.1
  have hv_rc₁ : (C₁ v).1.resetcount =
      Nat.max ((C u).1.resetcount - 1) ((C v).1.resetcount - 1) := by
    simpa [C₁, P] using hstep.2.2.2.1
  have hu_L₁ : (C₁ u).1.leader = .L := by
    simpa [C₁, P] using hstep.2.2.2.2.1
  have hv_F₁ : (C₁ v).1.leader = .F := by
    simpa [C₁, P] using hstep.2.2.2.2.2
  have hothers₁ : ∀ w : Fin n, w ≠ u → w ≠ v → C₁ w = C w := by
    intro w hwu hwv
    simp [C₁, Config.step, P, huv, hwu, hwv]
  by_cases hzero :
      Nat.max ((C u).1.resetcount - 1) ((C v).1.resetcount - 1) = 0
  · have hu_delay₁ : (C₁ u).1.delaytimer = Dmax := by
      simpa [C₁, P] using
        step_both_rc_pos_fst_delay_final
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          (by omega : 0 < Dmax) C huv hu_res hv_res hu_rc hv_rc hzero
    refine ⟨[(u, v)], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show (runPairs P C [(u, v)] u).1.role = .Resetting
      simp [runPairs, C₁, P]
      exact hu_role₁
    · show (runPairs P C [(u, v)] u).1.resetcount = 0
      simp [runPairs, C₁, P]
      rw [hu_rc₁, hzero]
    · show (runPairs P C [(u, v)] u).1.leader = .L
      simp [runPairs, C₁, P]
      exact hu_L₁
    · show (runPairs P C [(u, v)] u).1.delaytimer = Dmax
      simp [runPairs, C₁, P]
      exact hu_delay₁
    · show (runPairs P C [(u, v)] v).1.role = .Resetting
      simp [runPairs, C₁, P]
      exact hv_role₁
    · show (runPairs P C [(u, v)] v).1.resetcount = 0
      simp [runPairs, C₁, P]
      rw [hv_rc₁, hzero]
    · show (runPairs P C [(u, v)] v).1.leader = .F
      simp [runPairs, C₁, P]
      exact hv_F₁
    · intro w hwu hwv
      show runPairs P C [(u, v)] w = C w
      simp [runPairs, C₁, P]
      exact hothers₁ w hwu hwv
  · have hposM : 0 < Nat.max ((C u).1.resetcount - 1) ((C v).1.resetcount - 1) :=
      Nat.pos_of_ne_zero hzero
    have hu_pos₁ : 0 < (C₁ u).1.resetcount := by
      rw [hu_rc₁]
      exact hposM
    have hv_pos₁ : 0 < (C₁ v).1.resetcount := by
      rw [hv_rc₁]
      exact hposM
    obtain ⟨Ltail, hu_role_t, hu_rc_t, hu_L_t, hu_dt_t,
        hv_role_t, hv_rc_t, hv_F_t, hothers_t⟩ :=
      drain_pair_rc_LF_with_u_delay
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hDmax C₁ huv hu_role₁ hv_role₁ hu_pos₁ hv_pos₁ hu_L₁ hv_F₁
    refine ⟨[(u, v)] ++ Ltail, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [runPairs_append]
      show (runPairs P C₁ Ltail u).1.role = .Resetting
      simp [runPairs]
      exact hu_role_t
    · rw [runPairs_append]
      show (runPairs P C₁ Ltail u).1.resetcount = 0
      simp [runPairs]
      exact hu_rc_t
    · rw [runPairs_append]
      show (runPairs P C₁ Ltail u).1.leader = .L
      simp [runPairs]
      exact hu_L_t
    · rw [runPairs_append]
      show (runPairs P C₁ Ltail u).1.delaytimer = Dmax
      exact hu_dt_t
    · rw [runPairs_append]
      show (runPairs P C₁ Ltail v).1.role = .Resetting
      simp [runPairs]
      exact hv_role_t
    · rw [runPairs_append]
      show (runPairs P C₁ Ltail v).1.resetcount = 0
      simp [runPairs]
      exact hv_rc_t
    · rw [runPairs_append]
      show (runPairs P C₁ Ltail v).1.leader = .F
      simp [runPairs]
      exact hv_F_t
    · intro w hwu hwv
      rw [runPairs_append]
      change runPairs P C₁ Ltail w = C w
      rw [hothers_t w hwu hwv]
      exact hothers₁ w hwu hwv

set_option maxHeartbeats 8000000 in
theorem drain_L_pos_F_zero_to_zero
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 0 < Dmax)
    (C : Config (AgentState n) Opinion n)
    {u v : Fin n} (huv : u ≠ v)
    (hu_res : (C u).1.role = .Resetting) (hv_res : (C v).1.role = .Resetting)
    (hu_rc : 0 < (C u).1.resetcount) (hv_rc : (C v).1.resetcount = 0)
    (hu_L : (C u).1.leader = .L) (hv_F : (C v).1.leader = .F)
    (hv_dt : 1 < (C v).1.delaytimer) :
    let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    ∃ L : List (Fin n × Fin n),
      (runPairs P C L u).1.role = .Resetting ∧
      (runPairs P C L u).1.resetcount = 0 ∧
      (runPairs P C L u).1.leader = .L ∧
      (runPairs P C L v).1.role = .Resetting ∧
      (runPairs P C L v).1.resetcount = 0 ∧
      (runPairs P C L v).1.leader = .F ∧
      ∀ w : Fin n, w ≠ u → w ≠ v → runPairs P C L w = C w := by
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have hstep := step_L_pos_F_zero
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hDmax C huv hu_res hv_res hu_rc hv_rc hu_L hv_F hv_dt
  let C₁ : Config (AgentState n) Opinion n := C.step P u v
  have hu_role₁ : (C₁ u).1.role = .Resetting := by
    simpa [C₁, P] using hstep.1
  have hv_role₁ : (C₁ v).1.role = .Resetting := by
    simpa [C₁, P] using hstep.2.1
  have hu_rc₁ : (C₁ u).1.resetcount = (C u).1.resetcount - 1 := by
    simpa [C₁, P] using hstep.2.2.1
  have hv_rc₁ : (C₁ v).1.resetcount = (C u).1.resetcount - 1 := by
    simpa [C₁, P] using hstep.2.2.2.1
  have hu_L₁ : (C₁ u).1.leader = .L := by
    simpa [C₁, P] using hstep.2.2.2.2.1
  have hv_F₁ : (C₁ v).1.leader = .F := by
    simpa [C₁, P] using hstep.2.2.2.2.2.1
  have hothers₁ : ∀ w : Fin n, w ≠ u → w ≠ v → C₁ w = C w := by
    intro w hwu hwv
    simp [C₁, Config.step, P, huv, hwu, hwv]
  by_cases hzero : (C u).1.resetcount - 1 = 0
  · refine ⟨[(u, v)], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show (runPairs P C [(u, v)] u).1.role = .Resetting
      simp [runPairs, C₁, P]
      exact hu_role₁
    · show (runPairs P C [(u, v)] u).1.resetcount = 0
      simp [runPairs, C₁, P]
      rw [hu_rc₁, hzero]
    · show (runPairs P C [(u, v)] u).1.leader = .L
      simp [runPairs, C₁, P]
      exact hu_L₁
    · show (runPairs P C [(u, v)] v).1.role = .Resetting
      simp [runPairs, C₁, P]
      exact hv_role₁
    · show (runPairs P C [(u, v)] v).1.resetcount = 0
      simp [runPairs, C₁, P]
      rw [hv_rc₁, hzero]
    · show (runPairs P C [(u, v)] v).1.leader = .F
      simp [runPairs, C₁, P]
      exact hv_F₁
    · intro w hwu hwv
      show runPairs P C [(u, v)] w = C w
      simp [runPairs, C₁, P]
      exact hothers₁ w hwu hwv
  · have hpos : 0 < (C u).1.resetcount - 1 :=
      Nat.pos_of_ne_zero hzero
    have hu_pos₁ : 0 < (C₁ u).1.resetcount := by
      rw [hu_rc₁]
      exact hpos
    have hv_pos₁ : 0 < (C₁ v).1.resetcount := by
      rw [hv_rc₁]
      exact hpos
    obtain ⟨Ltail, hu_role_t, hu_rc_t, hu_L_t, hv_role_t, hv_rc_t, hv_F_t, hothers_t⟩ :=
      drain_pair_rc_LF
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hDmax C₁ huv hu_role₁ hv_role₁ hu_pos₁ hv_pos₁ hu_L₁ hv_F₁
    refine ⟨[(u, v)] ++ Ltail, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [runPairs_append]
      show (runPairs P C₁ Ltail u).1.role = .Resetting
      simp [runPairs]
      exact hu_role_t
    · rw [runPairs_append]
      show (runPairs P C₁ Ltail u).1.resetcount = 0
      simp [runPairs]
      exact hu_rc_t
    · rw [runPairs_append]
      show (runPairs P C₁ Ltail u).1.leader = .L
      simp [runPairs]
      exact hu_L_t
    · rw [runPairs_append]
      show (runPairs P C₁ Ltail v).1.role = .Resetting
      simp [runPairs]
      exact hv_role_t
    · rw [runPairs_append]
      show (runPairs P C₁ Ltail v).1.resetcount = 0
      simp [runPairs]
      exact hv_rc_t
    · rw [runPairs_append]
      show (runPairs P C₁ Ltail v).1.leader = .F
      simp [runPairs]
      exact hv_F_t
    · intro w hwu hwv
      rw [runPairs_append]
      change runPairs P C₁ Ltail w = C w
      rw [hothers_t w hwu hwv]
      exact hothers₁ w hwu hwv

set_option maxHeartbeats 8000000 in
theorem drain_L_pos_L_zero_to_zero
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 0 < Dmax)
    (C : Config (AgentState n) Opinion n)
    {u v : Fin n} (huv : u ≠ v)
    (hu_res : (C u).1.role = .Resetting) (hv_res : (C v).1.role = .Resetting)
    (hu_rc : 0 < (C u).1.resetcount) (hv_rc : (C v).1.resetcount = 0)
    (hu_L : (C u).1.leader = .L) (hv_L : (C v).1.leader = .L)
    (hv_dt : 1 < (C v).1.delaytimer) :
    let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    ∃ L : List (Fin n × Fin n),
      (runPairs P C L u).1.role = .Resetting ∧
      (runPairs P C L u).1.resetcount = 0 ∧
      (runPairs P C L u).1.leader = .L ∧
      (runPairs P C L v).1.role = .Resetting ∧
      (runPairs P C L v).1.resetcount = 0 ∧
      (runPairs P C L v).1.leader = .F ∧
      ∀ w : Fin n, w ≠ u → w ≠ v → runPairs P C L w = C w := by
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have hstep := step_L_pos_L_zero
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hDmax C huv hu_res hv_res hu_rc hv_rc hu_L hv_L hv_dt
  let C₁ : Config (AgentState n) Opinion n := C.step P u v
  have hu_role₁ : (C₁ u).1.role = .Resetting := by
    simpa [C₁, P] using hstep.1
  have hv_role₁ : (C₁ v).1.role = .Resetting := by
    simpa [C₁, P] using hstep.2.1
  have hu_rc₁ : (C₁ u).1.resetcount = (C u).1.resetcount - 1 := by
    simpa [C₁, P] using hstep.2.2.1
  have hv_rc₁ : (C₁ v).1.resetcount = (C u).1.resetcount - 1 := by
    simpa [C₁, P] using hstep.2.2.2.1
  have hu_L₁ : (C₁ u).1.leader = .L := by
    simpa [C₁, P] using hstep.2.2.2.2.1
  have hv_F₁ : (C₁ v).1.leader = .F := by
    simpa [C₁, P] using hstep.2.2.2.2.2.1
  have hothers₁ : ∀ w : Fin n, w ≠ u → w ≠ v → C₁ w = C w := by
    intro w hwu hwv
    simp [C₁, Config.step, P, huv, hwu, hwv]
  by_cases hzero : (C u).1.resetcount - 1 = 0
  · refine ⟨[(u, v)], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show (runPairs P C [(u, v)] u).1.role = .Resetting
      simp [runPairs, C₁, P]
      exact hu_role₁
    · show (runPairs P C [(u, v)] u).1.resetcount = 0
      simp [runPairs, C₁, P]
      rw [hu_rc₁, hzero]
    · show (runPairs P C [(u, v)] u).1.leader = .L
      simp [runPairs, C₁, P]
      exact hu_L₁
    · show (runPairs P C [(u, v)] v).1.role = .Resetting
      simp [runPairs, C₁, P]
      exact hv_role₁
    · show (runPairs P C [(u, v)] v).1.resetcount = 0
      simp [runPairs, C₁, P]
      rw [hv_rc₁, hzero]
    · show (runPairs P C [(u, v)] v).1.leader = .F
      simp [runPairs, C₁, P]
      exact hv_F₁
    · intro w hwu hwv
      show runPairs P C [(u, v)] w = C w
      simp [runPairs, C₁, P]
      exact hothers₁ w hwu hwv
  · have hpos : 0 < (C u).1.resetcount - 1 :=
      Nat.pos_of_ne_zero hzero
    have hu_pos₁ : 0 < (C₁ u).1.resetcount := by
      rw [hu_rc₁]
      exact hpos
    have hv_pos₁ : 0 < (C₁ v).1.resetcount := by
      rw [hv_rc₁]
      exact hpos
    obtain ⟨Ltail, hu_role_t, hu_rc_t, hu_L_t, hv_role_t, hv_rc_t, hv_F_t, hothers_t⟩ :=
      drain_pair_rc_LF
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hDmax C₁ huv hu_role₁ hv_role₁ hu_pos₁ hv_pos₁ hu_L₁ hv_F₁
    refine ⟨[(u, v)] ++ Ltail, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [runPairs_append]
      show (runPairs P C₁ Ltail u).1.role = .Resetting
      simp [runPairs]
      exact hu_role_t
    · rw [runPairs_append]
      show (runPairs P C₁ Ltail u).1.resetcount = 0
      simp [runPairs]
      exact hu_rc_t
    · rw [runPairs_append]
      show (runPairs P C₁ Ltail u).1.leader = .L
      simp [runPairs]
      exact hu_L_t
    · rw [runPairs_append]
      show (runPairs P C₁ Ltail v).1.role = .Resetting
      simp [runPairs]
      exact hv_role_t
    · rw [runPairs_append]
      show (runPairs P C₁ Ltail v).1.resetcount = 0
      simp [runPairs]
      exact hv_rc_t
    · rw [runPairs_append]
      show (runPairs P C₁ Ltail v).1.leader = .F
      simp [runPairs]
      exact hv_F_t
    · intro w hwu hwv
      rw [runPairs_append]
      change runPairs P C₁ Ltail w = C w
      rw [hothers_t w hwu hwv]
      exact hothers₁ w hwu hwv

theorem drain_L_pos_any_zero_to_zero
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 0 < Dmax)
    (C : Config (AgentState n) Opinion n)
    {u v : Fin n} (huv : u ≠ v)
    (hu_res : (C u).1.role = .Resetting) (hv_res : (C v).1.role = .Resetting)
    (hu_rc : 0 < (C u).1.resetcount) (hv_rc : (C v).1.resetcount = 0)
    (hu_L : (C u).1.leader = .L)
    (hv_dt : 1 < (C v).1.delaytimer) :
    let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    ∃ L : List (Fin n × Fin n),
      (runPairs P C L u).1.role = .Resetting ∧
      (runPairs P C L u).1.resetcount = 0 ∧
      (runPairs P C L u).1.leader = .L ∧
      (runPairs P C L v).1.role = .Resetting ∧
      (runPairs P C L v).1.resetcount = 0 ∧
      (runPairs P C L v).1.leader = .F ∧
      ∀ w : Fin n, w ≠ u → w ≠ v → runPairs P C L w = C w := by
  cases hv_leader : (C v).1.leader with
  | L =>
      exact drain_L_pos_L_zero_to_zero
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hDmax C huv hu_res hv_res hu_rc hv_rc hu_L hv_leader hv_dt
  | F =>
      exact drain_L_pos_F_zero_to_zero
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hDmax C huv hu_res hv_res hu_rc hv_rc hu_L hv_leader hv_dt

set_option maxHeartbeats 8000000 in
theorem drain_F_pos_F_zero_to_zero
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 0 < Dmax)
    (C : Config (AgentState n) Opinion n)
    {u v : Fin n} (huv : u ≠ v)
    (hu_res : (C u).1.role = .Resetting) (hv_res : (C v).1.role = .Resetting)
    (hu_rc : 0 < (C u).1.resetcount) (hv_rc : (C v).1.resetcount = 0)
    (hu_F : (C u).1.leader = .F) (hv_F : (C v).1.leader = .F)
    (hv_dt : 1 < (C v).1.delaytimer) :
    let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    ∃ L : List (Fin n × Fin n),
      (runPairs P C L u).1.role = .Resetting ∧
      (runPairs P C L u).1.resetcount = 0 ∧
      (runPairs P C L v).1.role = .Resetting ∧
      (runPairs P C L v).1.resetcount = 0 ∧
      ∀ w : Fin n, w ≠ u → w ≠ v → runPairs P C L w = C w := by
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have hstep := step_F_pos_F_zero
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hDmax C huv hu_res hv_res hu_rc hv_rc hu_F hv_F hv_dt
  let C₁ : Config (AgentState n) Opinion n := C.step P u v
  have hu_role₁ : (C₁ u).1.role = .Resetting := by
    simpa [C₁, P] using hstep.1
  have hv_role₁ : (C₁ v).1.role = .Resetting := by
    simpa [C₁, P] using hstep.2.1
  have hu_rc₁ : (C₁ u).1.resetcount = (C u).1.resetcount - 1 := by
    simpa [C₁, P] using hstep.2.2.1
  have hv_rc₁ : (C₁ v).1.resetcount = (C u).1.resetcount - 1 := by
    simpa [C₁, P] using hstep.2.2.2.1
  have hothers₁ : ∀ w : Fin n, w ≠ u → w ≠ v → C₁ w = C w := by
    intro w hwu hwv
    simp [C₁, Config.step, P, huv, hwu, hwv]
  by_cases hzero : (C u).1.resetcount - 1 = 0
  · refine ⟨[(u, v)], ?_, ?_, ?_, ?_, ?_⟩
    · show (runPairs P C [(u, v)] u).1.role = .Resetting
      simp [runPairs, C₁, P]
      exact hu_role₁
    · show (runPairs P C [(u, v)] u).1.resetcount = 0
      simp [runPairs, C₁, P]
      rw [hu_rc₁, hzero]
    · show (runPairs P C [(u, v)] v).1.role = .Resetting
      simp [runPairs, C₁, P]
      exact hv_role₁
    · show (runPairs P C [(u, v)] v).1.resetcount = 0
      simp [runPairs, C₁, P]
      rw [hv_rc₁, hzero]
    · intro w hwu hwv
      show runPairs P C [(u, v)] w = C w
      simp [runPairs, C₁, P]
      exact hothers₁ w hwu hwv
  · have hpos : 0 < (C u).1.resetcount - 1 :=
      Nat.pos_of_ne_zero hzero
    have hu_pos₁ : 0 < (C₁ u).1.resetcount := by
      rw [hu_rc₁]
      exact hpos
    have hv_pos₁ : 0 < (C₁ v).1.resetcount := by
      rw [hv_rc₁]
      exact hpos
    obtain ⟨Ltail, hu_role_t, hu_rc_t, hv_role_t, hv_rc_t, _hu_leader_t, hothers_t⟩ :=
      drain_pair_rc
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hDmax C₁ huv hu_role₁ hv_role₁ hu_pos₁ hv_pos₁
    refine ⟨[(u, v)] ++ Ltail, ?_, ?_, ?_, ?_, ?_⟩
    · rw [runPairs_append]
      show (runPairs P C₁ Ltail u).1.role = .Resetting
      simp [runPairs]
      exact hu_role_t
    · rw [runPairs_append]
      show (runPairs P C₁ Ltail u).1.resetcount = 0
      simp [runPairs]
      exact hu_rc_t
    · rw [runPairs_append]
      show (runPairs P C₁ Ltail v).1.role = .Resetting
      simp [runPairs]
      exact hv_role_t
    · rw [runPairs_append]
      show (runPairs P C₁ Ltail v).1.resetcount = 0
      simp [runPairs]
      exact hv_rc_t
    · intro w hwu hwv
      rw [runPairs_append]
      change runPairs P C₁ Ltail w = C w
      rw [hothers_t w hwu hwv]
      exact hothers₁ w hwu hwv

set_option maxHeartbeats 8000000 in
theorem drain_F_pos_F_zero_to_zero_FF
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 0 < Dmax)
    (C : Config (AgentState n) Opinion n)
    {u v : Fin n} (huv : u ≠ v)
    (hu_res : (C u).1.role = .Resetting) (hv_res : (C v).1.role = .Resetting)
    (hu_rc : 0 < (C u).1.resetcount) (hv_rc : (C v).1.resetcount = 0)
    (hu_F : (C u).1.leader = .F) (hv_F : (C v).1.leader = .F)
    (hv_dt : 1 < (C v).1.delaytimer) :
    let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    ∃ L : List (Fin n × Fin n),
      (runPairs P C L u).1.role = .Resetting ∧
      (runPairs P C L u).1.resetcount = 0 ∧
      (runPairs P C L u).1.leader = .F ∧
      (runPairs P C L v).1.role = .Resetting ∧
      (runPairs P C L v).1.resetcount = 0 ∧
      (runPairs P C L v).1.leader = .F ∧
      ∀ w : Fin n, w ≠ u → w ≠ v → runPairs P C L w = C w := by
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have hstep := step_F_pos_F_zero
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hDmax C huv hu_res hv_res hu_rc hv_rc hu_F hv_F hv_dt
  let C₁ : Config (AgentState n) Opinion n := C.step P u v
  have hu_role₁ : (C₁ u).1.role = .Resetting := by
    simpa [C₁, P] using hstep.1
  have hv_role₁ : (C₁ v).1.role = .Resetting := by
    simpa [C₁, P] using hstep.2.1
  have hu_rc₁ : (C₁ u).1.resetcount = (C u).1.resetcount - 1 := by
    simpa [C₁, P] using hstep.2.2.1
  have hv_rc₁ : (C₁ v).1.resetcount = (C u).1.resetcount - 1 := by
    simpa [C₁, P] using hstep.2.2.2.1
  have hu_F₁ : (C₁ u).1.leader = .F := by
    simpa [C₁, P] using hstep.2.2.2.2.1
  have hv_F₁ : (C₁ v).1.leader = .F := by
    simpa [C₁, P] using hstep.2.2.2.2.2
  have hothers₁ : ∀ w : Fin n, w ≠ u → w ≠ v → C₁ w = C w := by
    intro w hwu hwv
    simp [C₁, Config.step, P, huv, hwu, hwv]
  by_cases hzero : (C u).1.resetcount - 1 = 0
  · refine ⟨[(u, v)], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show (runPairs P C [(u, v)] u).1.role = .Resetting
      simp [runPairs, C₁, P]
      exact hu_role₁
    · show (runPairs P C [(u, v)] u).1.resetcount = 0
      simp [runPairs, C₁, P]
      rw [hu_rc₁, hzero]
    · show (runPairs P C [(u, v)] u).1.leader = .F
      simp [runPairs, C₁, P]
      exact hu_F₁
    · show (runPairs P C [(u, v)] v).1.role = .Resetting
      simp [runPairs, C₁, P]
      exact hv_role₁
    · show (runPairs P C [(u, v)] v).1.resetcount = 0
      simp [runPairs, C₁, P]
      rw [hv_rc₁, hzero]
    · show (runPairs P C [(u, v)] v).1.leader = .F
      simp [runPairs, C₁, P]
      exact hv_F₁
    · intro w hwu hwv
      show runPairs P C [(u, v)] w = C w
      simp [runPairs, C₁, P]
      exact hothers₁ w hwu hwv
  · have hpos : 0 < (C u).1.resetcount - 1 :=
      Nat.pos_of_ne_zero hzero
    have hu_pos₁ : 0 < (C₁ u).1.resetcount := by
      rw [hu_rc₁]
      exact hpos
    have hv_pos₁ : 0 < (C₁ v).1.resetcount := by
      rw [hv_rc₁]
      exact hpos
    obtain ⟨Ltail, hu_role_t, hu_rc_t, hu_F_t, hv_role_t, hv_rc_t, hv_F_t, hothers_t⟩ :=
      drain_pair_rc_FF
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hDmax C₁ huv hu_role₁ hv_role₁ hu_pos₁ hv_pos₁ hu_F₁ hv_F₁
    refine ⟨[(u, v)] ++ Ltail, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [runPairs_append]
      show (runPairs P C₁ Ltail u).1.role = .Resetting
      simp [runPairs]
      exact hu_role_t
    · rw [runPairs_append]
      show (runPairs P C₁ Ltail u).1.resetcount = 0
      simp [runPairs]
      exact hu_rc_t
    · rw [runPairs_append]
      show (runPairs P C₁ Ltail u).1.leader = .F
      simp [runPairs]
      exact hu_F_t
    · rw [runPairs_append]
      show (runPairs P C₁ Ltail v).1.role = .Resetting
      simp [runPairs]
      exact hv_role_t
    · rw [runPairs_append]
      show (runPairs P C₁ Ltail v).1.resetcount = 0
      simp [runPairs]
      exact hv_rc_t
    · rw [runPairs_append]
      show (runPairs P C₁ Ltail v).1.leader = .F
      simp [runPairs]
      exact hv_F_t
    · intro w hwu hwv
      rw [runPairs_append]
      change runPairs P C₁ Ltail w = C w
      rw [hothers_t w hwu hwv]
      exact hothers₁ w hwu hwv

set_option maxHeartbeats 8000000 in
theorem drain_L_zero_pos_to_zero_of_step
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 0 < Dmax)
    (C : Config (AgentState n) Opinion n)
    {u v : Fin n} (huv : u ≠ v)
    (hstep :
      let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
      let C' := C.step P u v
      (C' u).1.role = .Resetting ∧
      (C' v).1.role = .Resetting ∧
      (C' u).1.resetcount = (C v).1.resetcount - 1 ∧
      (C' v).1.resetcount = (C v).1.resetcount - 1 ∧
      (C' u).1.leader = .L ∧
      (C' v).1.leader = .F) :
    let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    ∃ L : List (Fin n × Fin n),
      (runPairs P C L u).1.role = .Resetting ∧
      (runPairs P C L u).1.resetcount = 0 ∧
      (runPairs P C L u).1.leader = .L ∧
      (runPairs P C L v).1.role = .Resetting ∧
      (runPairs P C L v).1.resetcount = 0 ∧
      (runPairs P C L v).1.leader = .F ∧
      ∀ w : Fin n, w ≠ u → w ≠ v → runPairs P C L w = C w := by
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  let C₁ : Config (AgentState n) Opinion n := C.step P u v
  have hu_role₁ : (C₁ u).1.role = .Resetting := by
    simpa [C₁, P] using hstep.1
  have hv_role₁ : (C₁ v).1.role = .Resetting := by
    simpa [C₁, P] using hstep.2.1
  have hu_rc₁ : (C₁ u).1.resetcount = (C v).1.resetcount - 1 := by
    simpa [C₁, P] using hstep.2.2.1
  have hv_rc₁ : (C₁ v).1.resetcount = (C v).1.resetcount - 1 := by
    simpa [C₁, P] using hstep.2.2.2.1
  have hu_L₁ : (C₁ u).1.leader = .L := by
    simpa [C₁, P] using hstep.2.2.2.2.1
  have hv_F₁ : (C₁ v).1.leader = .F := by
    simpa [C₁, P] using hstep.2.2.2.2.2
  have hothers₁ : ∀ w : Fin n, w ≠ u → w ≠ v → C₁ w = C w := by
    intro w hwu hwv
    simp [C₁, Config.step, P, huv, hwu, hwv]
  by_cases hzero : (C v).1.resetcount - 1 = 0
  · refine ⟨[(u, v)], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show (runPairs P C [(u, v)] u).1.role = .Resetting
      simp [runPairs, C₁, P]
      exact hu_role₁
    · show (runPairs P C [(u, v)] u).1.resetcount = 0
      simp [runPairs, C₁, P]
      rw [hu_rc₁, hzero]
    · show (runPairs P C [(u, v)] u).1.leader = .L
      simp [runPairs, C₁, P]
      exact hu_L₁
    · show (runPairs P C [(u, v)] v).1.role = .Resetting
      simp [runPairs, C₁, P]
      exact hv_role₁
    · show (runPairs P C [(u, v)] v).1.resetcount = 0
      simp [runPairs, C₁, P]
      rw [hv_rc₁, hzero]
    · show (runPairs P C [(u, v)] v).1.leader = .F
      simp [runPairs, C₁, P]
      exact hv_F₁
    · intro w hwu hwv
      show runPairs P C [(u, v)] w = C w
      simp [runPairs, C₁, P]
      exact hothers₁ w hwu hwv
  · have hpos : 0 < (C v).1.resetcount - 1 :=
      Nat.pos_of_ne_zero hzero
    have hu_pos₁ : 0 < (C₁ u).1.resetcount := by
      rw [hu_rc₁]
      exact hpos
    have hv_pos₁ : 0 < (C₁ v).1.resetcount := by
      rw [hv_rc₁]
      exact hpos
    obtain ⟨Ltail, hu_role_t, hu_rc_t, hu_L_t, hv_role_t, hv_rc_t, hv_F_t, hothers_t⟩ :=
      drain_pair_rc_LF
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hDmax C₁ huv hu_role₁ hv_role₁ hu_pos₁ hv_pos₁ hu_L₁ hv_F₁
    refine ⟨[(u, v)] ++ Ltail, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [runPairs_append]
      show (runPairs P C₁ Ltail u).1.role = .Resetting
      simp [runPairs]
      exact hu_role_t
    · rw [runPairs_append]
      show (runPairs P C₁ Ltail u).1.resetcount = 0
      simp [runPairs]
      exact hu_rc_t
    · rw [runPairs_append]
      show (runPairs P C₁ Ltail u).1.leader = .L
      simp [runPairs]
      exact hu_L_t
    · rw [runPairs_append]
      show (runPairs P C₁ Ltail v).1.role = .Resetting
      simp [runPairs]
      exact hv_role_t
    · rw [runPairs_append]
      show (runPairs P C₁ Ltail v).1.resetcount = 0
      simp [runPairs]
      exact hv_rc_t
    · rw [runPairs_append]
      show (runPairs P C₁ Ltail v).1.leader = .F
      simp [runPairs]
      exact hv_F_t
    · intro w hwu hwv
      rw [runPairs_append]
      change runPairs P C₁ Ltail w = C w
      rw [hothers_t w hwu hwv]
      exact hothers₁ w hwu hwv

theorem drain_L_zero_any_pos_to_zero
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 0 < Dmax)
    (C : Config (AgentState n) Opinion n)
    {u v : Fin n} (huv : u ≠ v)
    (hu_res : (C u).1.role = .Resetting) (hv_res : (C v).1.role = .Resetting)
    (hu_rc : (C u).1.resetcount = 0) (hv_rc : 0 < (C v).1.resetcount)
    (hu_L : (C u).1.leader = .L) (hu_dt : 1 < (C u).1.delaytimer) :
    let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    ∃ L : List (Fin n × Fin n),
      (runPairs P C L u).1.role = .Resetting ∧
      (runPairs P C L u).1.resetcount = 0 ∧
      (runPairs P C L u).1.leader = .L ∧
      (runPairs P C L v).1.role = .Resetting ∧
      (runPairs P C L v).1.resetcount = 0 ∧
      (runPairs P C L v).1.leader = .F ∧
      ∀ w : Fin n, w ≠ u → w ≠ v → runPairs P C L w = C w := by
  cases hv_leader : (C v).1.leader with
  | L =>
      have hstep_full := step_L_zero_L_pos
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hDmax C huv hu_res hv_res hu_rc hv_rc hu_L hv_leader hu_dt
      exact drain_L_zero_pos_to_zero_of_step
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hDmax C huv
        ⟨hstep_full.1, hstep_full.2.1, hstep_full.2.2.1,
          hstep_full.2.2.2.1, hstep_full.2.2.2.2.1,
          hstep_full.2.2.2.2.2.1⟩
  | F =>
      have hstep_full := step_L_zero_F_pos
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hDmax C huv hu_res hv_res hu_rc hv_rc hu_L hv_leader hu_dt
      exact drain_L_zero_pos_to_zero_of_step
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hDmax C huv
        ⟨hstep_full.1, hstep_full.2.1, hstep_full.2.2.1,
          hstep_full.2.2.2.1, hstep_full.2.2.2.2.1,
          hstep_full.2.2.2.2.2.1⟩

set_option maxHeartbeats 8000000 in
theorem drain_L_zero_pos_to_zero_of_step_with_anchor_delay
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 1 < Dmax)
    (C : Config (AgentState n) Opinion n)
    {u v : Fin n} (huv : u ≠ v)
    (hv_rc : 0 < (C v).1.resetcount)
    (hu_dt : 1 < (C u).1.delaytimer)
    (hstep :
      let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
      let C' := C.step P u v
      (C' u).1.role = .Resetting ∧
      (C' v).1.role = .Resetting ∧
      (C' u).1.resetcount = (C v).1.resetcount - 1 ∧
      (C' v).1.resetcount = (C v).1.resetcount - 1 ∧
      (C' u).1.leader = .L ∧
      (C' v).1.leader = .F ∧
      (C' u).1.delaytimer =
        (if (C v).1.resetcount = 1 then (C u).1.delaytimer - 1 else (C u).1.delaytimer)) :
    let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    ∃ L : List (Fin n × Fin n),
      (runPairs P C L u).1.role = .Resetting ∧
      (runPairs P C L u).1.resetcount = 0 ∧
      (runPairs P C L u).1.leader = .L ∧
      (runPairs P C L u).1.delaytimer =
        (if (C v).1.resetcount = 1 then (C u).1.delaytimer - 1 else Dmax) ∧
      (runPairs P C L v).1.role = .Resetting ∧
      (runPairs P C L v).1.resetcount = 0 ∧
      (runPairs P C L v).1.leader = .F ∧
      ∀ w : Fin n, w ≠ u → w ≠ v → runPairs P C L w = C w := by
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  let C₁ : Config (AgentState n) Opinion n := C.step P u v
  have hu_role₁ : (C₁ u).1.role = .Resetting := by
    simpa [C₁, P] using hstep.1
  have hv_role₁ : (C₁ v).1.role = .Resetting := by
    simpa [C₁, P] using hstep.2.1
  have hu_rc₁ : (C₁ u).1.resetcount = (C v).1.resetcount - 1 := by
    simpa [C₁, P] using hstep.2.2.1
  have hv_rc₁ : (C₁ v).1.resetcount = (C v).1.resetcount - 1 := by
    simpa [C₁, P] using hstep.2.2.2.1
  have hu_L₁ : (C₁ u).1.leader = .L := by
    simpa [C₁, P] using hstep.2.2.2.2.1
  have hv_F₁ : (C₁ v).1.leader = .F := by
    simpa [C₁, P] using hstep.2.2.2.2.2.1
  have hu_dt₁ : (C₁ u).1.delaytimer =
      (if (C v).1.resetcount = 1 then (C u).1.delaytimer - 1 else (C u).1.delaytimer) := by
    simpa [C₁, P] using hstep.2.2.2.2.2.2
  have hothers₁ : ∀ w : Fin n, w ≠ u → w ≠ v → C₁ w = C w := by
    intro w hwu hwv
    simp [C₁, Config.step, P, huv, hwu, hwv]
  by_cases hzero : (C v).1.resetcount - 1 = 0
  · have hv_one : (C v).1.resetcount = 1 := by omega
    refine ⟨[(u, v)], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show (runPairs P C [(u, v)] u).1.role = .Resetting
      simp [runPairs, C₁, P]
      exact hu_role₁
    · show (runPairs P C [(u, v)] u).1.resetcount = 0
      simp [runPairs, C₁, P]
      rw [hu_rc₁, hzero]
    · show (runPairs P C [(u, v)] u).1.leader = .L
      simp [runPairs, C₁, P]
      exact hu_L₁
    · show (runPairs P C [(u, v)] u).1.delaytimer =
          (if (C v).1.resetcount = 1 then (C u).1.delaytimer - 1 else Dmax)
      simp [runPairs, C₁, P]
      rw [hu_dt₁, if_pos hv_one]
      rw [if_pos hv_one]
    · show (runPairs P C [(u, v)] v).1.role = .Resetting
      simp [runPairs, C₁, P]
      exact hv_role₁
    · show (runPairs P C [(u, v)] v).1.resetcount = 0
      simp [runPairs, C₁, P]
      rw [hv_rc₁, hzero]
    · show (runPairs P C [(u, v)] v).1.leader = .F
      simp [runPairs, C₁, P]
      exact hv_F₁
    · intro w hwu hwv
      show runPairs P C [(u, v)] w = C w
      simp [runPairs, C₁, P]
      exact hothers₁ w hwu hwv
  · have hpos : 0 < (C v).1.resetcount - 1 :=
      Nat.pos_of_ne_zero hzero
    have hu_pos₁ : 0 < (C₁ u).1.resetcount := by
      rw [hu_rc₁]
      exact hpos
    have hv_pos₁ : 0 < (C₁ v).1.resetcount := by
      rw [hv_rc₁]
      exact hpos
    obtain ⟨Ltail, hu_role_t, hu_rc_t, hu_L_t, hu_dt_t,
        hv_role_t, hv_rc_t, hv_F_t, hothers_t⟩ :=
      drain_pair_rc_LF_with_u_delay
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hDmax C₁ huv hu_role₁ hv_role₁ hu_pos₁ hv_pos₁ hu_L₁ hv_F₁
    refine ⟨[(u, v)] ++ Ltail, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [runPairs_append]
      show (runPairs P C₁ Ltail u).1.role = .Resetting
      simp [runPairs]
      exact hu_role_t
    · rw [runPairs_append]
      show (runPairs P C₁ Ltail u).1.resetcount = 0
      simp [runPairs]
      exact hu_rc_t
    · rw [runPairs_append]
      show (runPairs P C₁ Ltail u).1.leader = .L
      simp [runPairs]
      exact hu_L_t
    · have hv_not_one : (C v).1.resetcount ≠ 1 := by
        intro hv_one
        exact hzero (by omega)
      rw [runPairs_append]
      show (runPairs P C₁ Ltail u).1.delaytimer =
        (if (C v).1.resetcount = 1 then (C u).1.delaytimer - 1 else Dmax)
      rw [hu_dt_t, if_neg hv_not_one]
    · rw [runPairs_append]
      show (runPairs P C₁ Ltail v).1.role = .Resetting
      simp [runPairs]
      exact hv_role_t
    · rw [runPairs_append]
      show (runPairs P C₁ Ltail v).1.resetcount = 0
      simp [runPairs]
      exact hv_rc_t
    · rw [runPairs_append]
      show (runPairs P C₁ Ltail v).1.leader = .F
      simp [runPairs]
      exact hv_F_t
    · intro w hwu hwv
      rw [runPairs_append]
      change runPairs P C₁ Ltail w = C w
      rw [hothers_t w hwu hwv]
      exact hothers₁ w hwu hwv

theorem drain_L_zero_any_pos_to_zero_with_anchor_delay
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 1 < Dmax)
    (C : Config (AgentState n) Opinion n)
    {u v : Fin n} (huv : u ≠ v)
    (hu_res : (C u).1.role = .Resetting) (hv_res : (C v).1.role = .Resetting)
    (hu_rc : (C u).1.resetcount = 0) (hv_rc : 0 < (C v).1.resetcount)
    (hu_L : (C u).1.leader = .L) (hu_dt : 1 < (C u).1.delaytimer) :
    let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    ∃ L : List (Fin n × Fin n),
      (runPairs P C L u).1.role = .Resetting ∧
      (runPairs P C L u).1.resetcount = 0 ∧
      (runPairs P C L u).1.leader = .L ∧
      (runPairs P C L u).1.delaytimer =
        (if (C v).1.resetcount = 1 then (C u).1.delaytimer - 1 else Dmax) ∧
      (runPairs P C L v).1.role = .Resetting ∧
      (runPairs P C L v).1.resetcount = 0 ∧
      (runPairs P C L v).1.leader = .F ∧
      ∀ w : Fin n, w ≠ u → w ≠ v → runPairs P C L w = C w := by
  cases hv_leader : (C v).1.leader with
  | L =>
      have hstep_full := step_L_zero_L_pos
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        (by omega : 0 < Dmax) C huv hu_res hv_res hu_rc hv_rc hu_L hv_leader
        (by omega : 1 < (C u).1.delaytimer)
      exact drain_L_zero_pos_to_zero_of_step_with_anchor_delay
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hDmax C huv hv_rc hu_dt hstep_full
  | F =>
      have hstep_full := step_L_zero_F_pos
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        (by omega : 0 < Dmax) C huv hu_res hv_res hu_rc hv_rc hu_L hv_leader
        (by omega : 1 < (C u).1.delaytimer)
      exact drain_L_zero_pos_to_zero_of_step_with_anchor_delay
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hDmax C huv hv_rc hu_dt hstep_full

set_option maxHeartbeats 8000000 in
theorem drain_pair_rc_LL_to_LF_zero
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 0 < Dmax)
    (C : Config (AgentState n) Opinion n)
    {u v : Fin n} (huv : u ≠ v)
    (hu_res : (C u).1.role = .Resetting) (hv_res : (C v).1.role = .Resetting)
    (hu_rc : 0 < (C u).1.resetcount) (hv_rc : 0 < (C v).1.resetcount)
    (hu_L : (C u).1.leader = .L) (hv_L : (C v).1.leader = .L) :
    let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    ∃ L : List (Fin n × Fin n),
      (runPairs P C L u).1.role = .Resetting ∧
      (runPairs P C L u).1.resetcount = 0 ∧
      (runPairs P C L u).1.leader = .L ∧
      (runPairs P C L v).1.role = .Resetting ∧
      (runPairs P C L v).1.resetcount = 0 ∧
      (runPairs P C L v).1.leader = .F ∧
      ∀ w : Fin n, w ≠ u → w ≠ v → runPairs P C L w = C w := by
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have hstep := step_both_rc_pos_LL
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hDmax C huv hu_res hv_res hu_rc hv_rc hu_L hv_L
  let C₁ : Config (AgentState n) Opinion n := C.step P u v
  have hu_role₁ : (C₁ u).1.role = .Resetting := by
    simpa [C₁, P] using hstep.1
  have hv_role₁ : (C₁ v).1.role = .Resetting := by
    simpa [C₁, P] using hstep.2.1
  have hu_rc₁ : (C₁ u).1.resetcount =
      Nat.max ((C u).1.resetcount - 1) ((C v).1.resetcount - 1) := by
    simpa [C₁, P] using hstep.2.2.1
  have hv_rc₁ : (C₁ v).1.resetcount =
      Nat.max ((C u).1.resetcount - 1) ((C v).1.resetcount - 1) := by
    simpa [C₁, P] using hstep.2.2.2.1
  have hu_L₁ : (C₁ u).1.leader = .L := by
    simpa [C₁, P] using hstep.2.2.2.2.1
  have hv_F₁ : (C₁ v).1.leader = .F := by
    simpa [C₁, P] using hstep.2.2.2.2.2
  have hothers₁ : ∀ w : Fin n, w ≠ u → w ≠ v → C₁ w = C w := by
    intro w hwu hwv
    simp [C₁, Config.step, P, huv, hwu, hwv]
  by_cases hzero :
      Nat.max ((C u).1.resetcount - 1) ((C v).1.resetcount - 1) = 0
  · refine ⟨[(u, v)], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show (runPairs P C [(u, v)] u).1.role = .Resetting
      simp [runPairs, C₁, P]
      exact hu_role₁
    · show (runPairs P C [(u, v)] u).1.resetcount = 0
      simp [runPairs, C₁, P]
      rw [hu_rc₁, hzero]
    · show (runPairs P C [(u, v)] u).1.leader = .L
      simp [runPairs, C₁, P]
      exact hu_L₁
    · show (runPairs P C [(u, v)] v).1.role = .Resetting
      simp [runPairs, C₁, P]
      exact hv_role₁
    · show (runPairs P C [(u, v)] v).1.resetcount = 0
      simp [runPairs, C₁, P]
      rw [hv_rc₁, hzero]
    · show (runPairs P C [(u, v)] v).1.leader = .F
      simp [runPairs, C₁, P]
      exact hv_F₁
    · intro w hwu hwv
      show runPairs P C [(u, v)] w = C w
      simp [runPairs, C₁, P]
      exact hothers₁ w hwu hwv
  · have hposM : 0 < Nat.max ((C u).1.resetcount - 1) ((C v).1.resetcount - 1) :=
      Nat.pos_of_ne_zero hzero
    have hu_pos₁ : 0 < (C₁ u).1.resetcount := by
      rw [hu_rc₁]
      exact hposM
    have hv_pos₁ : 0 < (C₁ v).1.resetcount := by
      rw [hv_rc₁]
      exact hposM
    obtain ⟨Ltail, hu_role_t, hu_rc_t, hu_L_t, hv_role_t, hv_rc_t, hv_F_t, hothers_t⟩ :=
      drain_pair_rc_LF
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hDmax C₁ huv hu_role₁ hv_role₁ hu_pos₁ hv_pos₁ hu_L₁ hv_F₁
    refine ⟨[(u, v)] ++ Ltail, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [runPairs_append]
      show (runPairs P C₁ Ltail u).1.role = .Resetting
      simp [runPairs]
      exact hu_role_t
    · rw [runPairs_append]
      show (runPairs P C₁ Ltail u).1.resetcount = 0
      simp [runPairs]
      exact hu_rc_t
    · rw [runPairs_append]
      show (runPairs P C₁ Ltail u).1.leader = .L
      simp [runPairs]
      exact hu_L_t
    · rw [runPairs_append]
      show (runPairs P C₁ Ltail v).1.role = .Resetting
      simp [runPairs]
      exact hv_role_t
    · rw [runPairs_append]
      show (runPairs P C₁ Ltail v).1.resetcount = 0
      simp [runPairs]
      exact hv_rc_t
    · rw [runPairs_append]
      show (runPairs P C₁ Ltail v).1.leader = .F
      simp [runPairs]
      exact hv_F_t
    · intro w hwu hwv
      rw [runPairs_append]
      change runPairs P C₁ Ltail w = C w
      rw [hothers_t w hwu hwv]
      exact hothers₁ w hwu hwv

theorem drain_pair_rc_L_any_to_LF_zero
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 0 < Dmax)
    (C : Config (AgentState n) Opinion n)
    {u v : Fin n} (huv : u ≠ v)
    (hu_res : (C u).1.role = .Resetting) (hv_res : (C v).1.role = .Resetting)
    (hu_rc : 0 < (C u).1.resetcount) (hv_rc : 0 < (C v).1.resetcount)
    (hu_L : (C u).1.leader = .L) :
    let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    ∃ L : List (Fin n × Fin n),
      (runPairs P C L u).1.role = .Resetting ∧
      (runPairs P C L u).1.resetcount = 0 ∧
      (runPairs P C L u).1.leader = .L ∧
      (runPairs P C L v).1.role = .Resetting ∧
      (runPairs P C L v).1.resetcount = 0 ∧
      (runPairs P C L v).1.leader = .F ∧
      ∀ w : Fin n, w ≠ u → w ≠ v → runPairs P C L w = C w := by
  cases hv_leader : (C v).1.leader with
  | L =>
      exact drain_pair_rc_LL_to_LF_zero
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hDmax C huv hu_res hv_res hu_rc hv_rc hu_L hv_leader
  | F =>
      exact drain_pair_rc_LF
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hDmax C huv hu_res hv_res hu_rc hv_rc hu_L hv_leader

theorem drain_pair_rc_L_any_to_LF_zero_with_u_delay
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 1 < Dmax)
    (C : Config (AgentState n) Opinion n)
    {u v : Fin n} (huv : u ≠ v)
    (hu_res : (C u).1.role = .Resetting) (hv_res : (C v).1.role = .Resetting)
    (hu_rc : 0 < (C u).1.resetcount) (hv_rc : 0 < (C v).1.resetcount)
    (hu_L : (C u).1.leader = .L) :
    let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    ∃ L : List (Fin n × Fin n),
      (runPairs P C L u).1.role = .Resetting ∧
      (runPairs P C L u).1.resetcount = 0 ∧
      (runPairs P C L u).1.leader = .L ∧
      (runPairs P C L u).1.delaytimer = Dmax ∧
      (runPairs P C L v).1.role = .Resetting ∧
      (runPairs P C L v).1.resetcount = 0 ∧
      (runPairs P C L v).1.leader = .F ∧
      ∀ w : Fin n, w ≠ u → w ≠ v → runPairs P C L w = C w := by
  cases hv_leader : (C v).1.leader with
  | L =>
      exact drain_pair_rc_LL_to_LF_zero_with_u_delay
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hDmax C huv hu_res hv_res hu_rc hv_rc hu_L hv_leader
  | F =>
      obtain ⟨L, hu_role, hu_rc0, hu_L', hu_dt, hv_role, hv_rc0, hv_F', hothers⟩ :=
        drain_pair_rc_LF_with_u_delay
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hDmax C huv hu_res hv_res hu_rc hv_rc hu_L hv_leader
      exact ⟨L, hu_role, hu_rc0, hu_L', hu_dt, hv_role, hv_rc0, hv_F', hothers⟩

def positiveRcExcept (C : Config (AgentState n) Opinion n) (ℓ : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun w : Fin n => w ≠ ℓ ∧ 0 < (C w).1.resetcount)

def positiveRcAgents (C : Config (AgentState n) Opinion n) : Finset (Fin n) :=
  Finset.univ.filter (fun w : Fin n => 0 < (C w).1.resetcount)

def resettingCount (C : Config (AgentState n) Opinion n) : ℕ :=
  (Finset.univ.filter (fun w : Fin n => (C w).1.role = .Resetting)).card

def followerDormantContribution (s : AgentState n) : ℕ :=
  if s.role == .Resetting then s.delaytimer + 1 else 0

def followerDormantMeasure (C : Config (AgentState n) Opinion n) : ℕ :=
  ∑ w : Fin n, followerDormantContribution (C w).1

theorem positiveRcExcept_card_lt_n
    {C : Config (AgentState n) Opinion n} {ℓ : Fin n}
    (hn : 0 < n) :
    (positiveRcExcept C ℓ).card < n := by
  classical
  have hsub : positiveRcExcept C ℓ ⊆ Finset.univ.erase ℓ := by
    intro w hw
    rw [positiveRcExcept, Finset.mem_filter] at hw
    rw [Finset.mem_erase]
    exact ⟨hw.2.1, Finset.mem_univ w⟩
  have hcard_le : (positiveRcExcept C ℓ).card ≤ (Finset.univ.erase ℓ).card :=
    Finset.card_le_card hsub
  have hcard_erase : (Finset.univ.erase ℓ).card = n - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ ℓ)]
    simp
  omega

theorem positiveRcExcept_eq_zero_iff
    {C : Config (AgentState n) Opinion n} {ℓ : Fin n} :
    (positiveRcExcept C ℓ).card = 0 ↔
      ∀ w : Fin n, w ≠ ℓ → (C w).1.resetcount = 0 := by
  classical
  constructor
  · intro hzero w hw_ne
    by_contra hrc_ne
    have hpos : 0 < (C w).1.resetcount := Nat.pos_of_ne_zero hrc_ne
    have hw_mem : w ∈ positiveRcExcept C ℓ := by
      rw [positiveRcExcept, Finset.mem_filter]
      exact ⟨Finset.mem_univ w, hw_ne, hpos⟩
    have hcard_pos : 0 < (positiveRcExcept C ℓ).card :=
      Finset.card_pos.mpr ⟨w, hw_mem⟩
    omega
  · intro hzero
    by_contra hcard_ne
    have hcard_pos : 0 < (positiveRcExcept C ℓ).card := Nat.pos_of_ne_zero hcard_ne
    obtain ⟨w, hw_mem⟩ := Finset.card_pos.mp hcard_pos
    rw [positiveRcExcept, Finset.mem_filter] at hw_mem
    have hw_rc0 := hzero w hw_mem.2.1
    omega

theorem positiveRcExcept_exists_of_card_pos
    {C : Config (AgentState n) Opinion n} {ℓ : Fin n}
    (hpos : 0 < (positiveRcExcept C ℓ).card) :
    ∃ w : Fin n, w ≠ ℓ ∧ 0 < (C w).1.resetcount := by
  classical
  obtain ⟨w, hw_mem⟩ := Finset.card_pos.mp hpos
  rw [positiveRcExcept, Finset.mem_filter] at hw_mem
  exact ⟨w, hw_mem.2.1, hw_mem.2.2⟩

theorem positiveRcAgents_eq_zero_iff
    {C : Config (AgentState n) Opinion n} :
    (positiveRcAgents C).card = 0 ↔
      ∀ w : Fin n, (C w).1.resetcount = 0 := by
  classical
  constructor
  · intro hzero w
    by_contra hrc_ne
    have hpos : 0 < (C w).1.resetcount := Nat.pos_of_ne_zero hrc_ne
    have hw_mem : w ∈ positiveRcAgents C := by
      rw [positiveRcAgents, Finset.mem_filter]
      exact ⟨Finset.mem_univ w, hpos⟩
    have hcard_pos : 0 < (positiveRcAgents C).card :=
      Finset.card_pos.mpr ⟨w, hw_mem⟩
    omega
  · intro hzero
    by_contra hcard_ne
    have hcard_pos : 0 < (positiveRcAgents C).card := Nat.pos_of_ne_zero hcard_ne
    obtain ⟨w, hw_mem⟩ := Finset.card_pos.mp hcard_pos
    rw [positiveRcAgents, Finset.mem_filter] at hw_mem
    have hw_rc0 := hzero w
    omega

theorem positiveRcAgents_exists_of_card_pos
    {C : Config (AgentState n) Opinion n}
    (hpos : 0 < (positiveRcAgents C).card) :
    ∃ w : Fin n, 0 < (C w).1.resetcount := by
  classical
  obtain ⟨w, hw_mem⟩ := Finset.card_pos.mp hpos
  rw [positiveRcAgents, Finset.mem_filter] at hw_mem
  exact ⟨w, hw_mem.2⟩

set_option maxHeartbeats 16000000 in
theorem drain_positive_except_anchor_to_zero
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 1 < Dmax) (hDmax_n : n ≤ Dmax)
    (C : Config (AgentState n) Opinion n) {ℓ : Fin n}
    (hAllReset : ∀ w : Fin n, (C w).1.role = .Resetting)
    (hℓ_L : (C ℓ).1.leader = .L)
    (hℓ_rc0 : (C ℓ).1.resetcount = 0)
    (hBudget : (positiveRcExcept C ℓ).card < (C ℓ).1.delaytimer)
    (hZeroF : ∀ w : Fin n, w ≠ ℓ → (C w).1.resetcount = 0 → (C w).1.leader = .F) :
    let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    ∃ L : List (Fin n × Fin n),
      let C' := runPairs P C L
      (∀ w : Fin n, (C' w).1.role = .Resetting) ∧
      (C' ℓ).1.resetcount = 0 ∧
      (C' ℓ).1.leader = .L ∧
      (∀ w : Fin n, w ≠ ℓ → (C' w).1.resetcount = 0) ∧
      (∀ w : Fin n, w ≠ ℓ → (C' w).1.leader = .F) := by
  classical
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  suffices drain :
      ∀ k (C₀ : Config (AgentState n) Opinion n),
        (positiveRcExcept C₀ ℓ).card ≤ k →
        (∀ w : Fin n, (C₀ w).1.role = .Resetting) →
        (C₀ ℓ).1.leader = .L →
        (C₀ ℓ).1.resetcount = 0 →
        (positiveRcExcept C₀ ℓ).card < (C₀ ℓ).1.delaytimer →
        (∀ w : Fin n, w ≠ ℓ → (C₀ w).1.resetcount = 0 → (C₀ w).1.leader = .F) →
        ∃ L : List (Fin n × Fin n),
          let C' := runPairs P C₀ L
          (∀ w : Fin n, (C' w).1.role = .Resetting) ∧
          (C' ℓ).1.resetcount = 0 ∧
          (C' ℓ).1.leader = .L ∧
          (∀ w : Fin n, w ≠ ℓ → (C' w).1.resetcount = 0) ∧
          (∀ w : Fin n, w ≠ ℓ → (C' w).1.leader = .F) by
    exact drain (positiveRcExcept C ℓ).card C le_rfl hAllReset hℓ_L hℓ_rc0 hBudget hZeroF
  intro k
  induction k with
  | zero =>
      intro C₀ hcard_le hAll hL hrc0 _hBudget hZero
      have hcard0 : (positiveRcExcept C₀ ℓ).card = 0 := by omega
      have hAllRc0_except : ∀ w : Fin n, w ≠ ℓ → (C₀ w).1.resetcount = 0 :=
        (positiveRcExcept_eq_zero_iff.mp hcard0)
      refine ⟨[], ?_⟩
      simp only [runPairs_nil]
      exact ⟨hAll, hrc0, hL, hAllRc0_except,
        fun w hw_ne => hZero w hw_ne (hAllRc0_except w hw_ne)⟩
  | succ k ih =>
      intro C₀ hcard_le hAll hL hrc0 hBudget₀ hZero
      by_cases hcard0 : (positiveRcExcept C₀ ℓ).card = 0
      · have hAllRc0_except : ∀ w : Fin n, w ≠ ℓ → (C₀ w).1.resetcount = 0 :=
          (positiveRcExcept_eq_zero_iff.mp hcard0)
        refine ⟨[], ?_⟩
        simp only [runPairs_nil]
        exact ⟨hAll, hrc0, hL, hAllRc0_except,
          fun w hw_ne => hZero w hw_ne (hAllRc0_except w hw_ne)⟩
      · have hcard_pos : 0 < (positiveRcExcept C₀ ℓ).card :=
          Nat.pos_of_ne_zero hcard0
        obtain ⟨v, hv_ne, hv_pos⟩ :=
          positiveRcExcept_exists_of_card_pos (C := C₀) (ℓ := ℓ) hcard_pos
        have hℓv : ℓ ≠ v := hv_ne.symm
        have hℓ_delay : 1 < (C₀ ℓ).1.delaytimer := by omega
        obtain ⟨Lstep, hℓ_role₁, hℓ_rc₁, hℓ_L₁, hℓ_dt₁,
            hv_role₁, hv_rc₁, hv_F₁, hothers₁⟩ :=
          drain_L_zero_any_pos_to_zero_with_anchor_delay
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            hDmax C₀ hℓv (hAll ℓ) (hAll v) hrc0 hv_pos hL hℓ_delay
        let C₁ : Config (AgentState n) Opinion n := runPairs P C₀ Lstep
        have hAll₁ : ∀ w : Fin n, (C₁ w).1.role = .Resetting := by
          intro w
          by_cases hwℓ : w = ℓ
          · subst w
            exact hℓ_role₁
          · by_cases hwv : w = v
            · subst w
              exact hv_role₁
            · dsimp [C₁]
              rw [hothers₁ w hwℓ hwv]
              exact hAll w
        have hZero₁ : ∀ w : Fin n, w ≠ ℓ → (C₁ w).1.resetcount = 0 → (C₁ w).1.leader = .F := by
          intro w hw_ne hw_rc0
          by_cases hwv : w = v
          · subst w
            exact hv_F₁
          · have hw_old : C₁ w = C₀ w := hothers₁ w hw_ne hwv
            have hw_old_rc0 : (C₀ w).1.resetcount = 0 := by
              rw [← hw_old]
              exact hw_rc0
            rw [hw_old]
            exact hZero w hw_ne hw_old_rc0
        have hsub : positiveRcExcept C₁ ℓ ⊆ (positiveRcExcept C₀ ℓ).erase v := by
          intro w hw_mem
          rw [positiveRcExcept, Finset.mem_filter] at hw_mem
          have hw_ne : w ≠ ℓ := hw_mem.2.1
          have hw_pos : 0 < (C₁ w).1.resetcount := hw_mem.2.2
          rw [Finset.mem_erase]
          refine ⟨?_, ?_⟩
          · intro hwv
            subst w
            rw [hv_rc₁] at hw_pos
            omega
          · rw [positiveRcExcept, Finset.mem_filter]
            by_cases hwv : w = v
            · subst w
              rw [hv_rc₁] at hw_pos
              omega
            · have hw_old : C₁ w = C₀ w := hothers₁ w hw_ne hwv
              have hw_old_pos : 0 < (C₀ w).1.resetcount := by
                rwa [hw_old] at hw_pos
              exact ⟨Finset.mem_univ w, hw_ne, hw_old_pos⟩
        have hv_mem_old : v ∈ positiveRcExcept C₀ ℓ := by
          rw [positiveRcExcept, Finset.mem_filter]
          exact ⟨Finset.mem_univ v, hv_ne, hv_pos⟩
        have hcard_erase :
            ((positiveRcExcept C₀ ℓ).erase v).card =
              (positiveRcExcept C₀ ℓ).card - 1 :=
          Finset.card_erase_of_mem hv_mem_old
        have hcard₁_le : (positiveRcExcept C₁ ℓ).card ≤ k := by
          have hle := Finset.card_le_card hsub
          rw [hcard_erase] at hle
          omega
        have hBudget₁ : (positiveRcExcept C₁ ℓ).card < (C₁ ℓ).1.delaytimer := by
          by_cases hv_one : (C₀ v).1.resetcount = 1
          · have hdt : (C₁ ℓ).1.delaytimer = (C₀ ℓ).1.delaytimer - 1 := by
              rw [hℓ_dt₁, if_pos hv_one]
            rw [hdt]
            have hle := Finset.card_le_card hsub
            rw [hcard_erase] at hle
            omega
          · have hdt : (C₁ ℓ).1.delaytimer = Dmax := by
              rw [hℓ_dt₁, if_neg hv_one]
            rw [hdt]
            exact Nat.lt_of_lt_of_le (positiveRcExcept_card_lt_n (C := C₁) (ℓ := ℓ) hn) hDmax_n
        obtain ⟨Ltail, htail⟩ :=
          ih C₁ hcard₁_le hAll₁ hℓ_L₁ hℓ_rc₁ hBudget₁ hZero₁
        refine ⟨Lstep ++ Ltail, ?_⟩
        rw [runPairs_append]
        change
          let C' := runPairs P C₁ Ltail
          (∀ w : Fin n, (C' w).1.role = .Resetting) ∧
          (C' ℓ).1.resetcount = 0 ∧
          (C' ℓ).1.leader = .L ∧
          (∀ w : Fin n, w ≠ ℓ → (C' w).1.resetcount = 0) ∧
          (∀ w : Fin n, w ≠ ℓ → (C' w).1.leader = .F)
        exact htail

set_option maxHeartbeats 16000000 in
theorem drain_positive_except_anchor_to_all_zero
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hDmax : 1 < Dmax) (hDmax_n : n ≤ Dmax)
    (C : Config (AgentState n) Opinion n) {ℓ : Fin n}
    (hAllReset : ∀ w : Fin n, (C w).1.role = .Resetting)
    (hℓ_L : (C ℓ).1.leader = .L)
    (hℓ_rc0 : (C ℓ).1.resetcount = 0)
    (hBudget : (positiveRcExcept C ℓ).card < (C ℓ).1.delaytimer) :
    let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    ∃ L : List (Fin n × Fin n),
      let C' := runPairs P C L
      (∀ w : Fin n, (C' w).1.role = .Resetting) ∧
      (∀ w : Fin n, (C' w).1.resetcount = 0) ∧
      (C' ℓ).1.leader = .L := by
  classical
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  suffices drain :
      ∀ k (C₀ : Config (AgentState n) Opinion n),
        (positiveRcExcept C₀ ℓ).card ≤ k →
        (∀ w : Fin n, (C₀ w).1.role = .Resetting) →
        (C₀ ℓ).1.leader = .L →
        (C₀ ℓ).1.resetcount = 0 →
        (positiveRcExcept C₀ ℓ).card < (C₀ ℓ).1.delaytimer →
        ∃ L : List (Fin n × Fin n),
          let C' := runPairs P C₀ L
          (∀ w : Fin n, (C' w).1.role = .Resetting) ∧
          (∀ w : Fin n, (C' w).1.resetcount = 0) ∧
          (C' ℓ).1.leader = .L by
    exact drain (positiveRcExcept C ℓ).card C le_rfl hAllReset hℓ_L hℓ_rc0 hBudget
  intro k
  induction k with
  | zero =>
      intro C₀ hcard_le hAll hL hrc0 _hBudget
      have hcard0 : (positiveRcExcept C₀ ℓ).card = 0 := by omega
      have hAllRc0_except : ∀ w : Fin n, w ≠ ℓ → (C₀ w).1.resetcount = 0 :=
        (positiveRcExcept_eq_zero_iff.mp hcard0)
      refine ⟨[], ?_⟩
      simp only [runPairs_nil]
      refine ⟨hAll, ?_, hL⟩
      intro w
      by_cases hwℓ : w = ℓ
      · subst w
        exact hrc0
      · exact hAllRc0_except w hwℓ
  | succ k ih =>
      intro C₀ hcard_le hAll hL hrc0 hBudget₀
      by_cases hcard0 : (positiveRcExcept C₀ ℓ).card = 0
      · have hAllRc0_except : ∀ w : Fin n, w ≠ ℓ → (C₀ w).1.resetcount = 0 :=
          (positiveRcExcept_eq_zero_iff.mp hcard0)
        refine ⟨[], ?_⟩
        simp only [runPairs_nil]
        refine ⟨hAll, ?_, hL⟩
        intro w
        by_cases hwℓ : w = ℓ
        · subst w
          exact hrc0
        · exact hAllRc0_except w hwℓ
      · have hcard_pos : 0 < (positiveRcExcept C₀ ℓ).card :=
          Nat.pos_of_ne_zero hcard0
        obtain ⟨v, hv_ne, hv_pos⟩ :=
          positiveRcExcept_exists_of_card_pos (C := C₀) (ℓ := ℓ) hcard_pos
        have hℓv : ℓ ≠ v := hv_ne.symm
        have hℓ_delay : 1 < (C₀ ℓ).1.delaytimer := by omega
        obtain ⟨Lstep, hℓ_role₁, hℓ_rc₁, hℓ_L₁, hℓ_dt₁,
            hv_role₁, hv_rc₁, _hv_F₁, hothers₁⟩ :=
          drain_L_zero_any_pos_to_zero_with_anchor_delay
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            hDmax C₀ hℓv (hAll ℓ) (hAll v) hrc0 hv_pos hL hℓ_delay
        let C₁ : Config (AgentState n) Opinion n := runPairs P C₀ Lstep
        have hAll₁ : ∀ w : Fin n, (C₁ w).1.role = .Resetting := by
          intro w
          by_cases hwℓ : w = ℓ
          · subst w
            exact hℓ_role₁
          · by_cases hwv : w = v
            · subst w
              exact hv_role₁
            · dsimp [C₁]
              rw [hothers₁ w hwℓ hwv]
              exact hAll w
        have hsub : positiveRcExcept C₁ ℓ ⊆ (positiveRcExcept C₀ ℓ).erase v := by
          intro w hw_mem
          rw [positiveRcExcept, Finset.mem_filter] at hw_mem
          have hw_ne : w ≠ ℓ := hw_mem.2.1
          have hw_pos : 0 < (C₁ w).1.resetcount := hw_mem.2.2
          rw [Finset.mem_erase]
          refine ⟨?_, ?_⟩
          · intro hwv
            subst w
            rw [hv_rc₁] at hw_pos
            omega
          · rw [positiveRcExcept, Finset.mem_filter]
            by_cases hwv : w = v
            · subst w
              rw [hv_rc₁] at hw_pos
              omega
            · have hw_old : C₁ w = C₀ w := hothers₁ w hw_ne hwv
              have hw_old_pos : 0 < (C₀ w).1.resetcount := by
                rwa [hw_old] at hw_pos
              exact ⟨Finset.mem_univ w, hw_ne, hw_old_pos⟩
        have hv_mem_old : v ∈ positiveRcExcept C₀ ℓ := by
          rw [positiveRcExcept, Finset.mem_filter]
          exact ⟨Finset.mem_univ v, hv_ne, hv_pos⟩
        have hcard_erase :
            ((positiveRcExcept C₀ ℓ).erase v).card =
              (positiveRcExcept C₀ ℓ).card - 1 :=
          Finset.card_erase_of_mem hv_mem_old
        have hcard₁_le : (positiveRcExcept C₁ ℓ).card ≤ k := by
          have hle := Finset.card_le_card hsub
          rw [hcard_erase] at hle
          omega
        have hBudget₁ : (positiveRcExcept C₁ ℓ).card < (C₁ ℓ).1.delaytimer := by
          by_cases hv_one : (C₀ v).1.resetcount = 1
          · have hdt : (C₁ ℓ).1.delaytimer = (C₀ ℓ).1.delaytimer - 1 := by
              rw [hℓ_dt₁, if_pos hv_one]
            rw [hdt]
            have hle := Finset.card_le_card hsub
            rw [hcard_erase] at hle
            omega
          · have hdt : (C₁ ℓ).1.delaytimer = Dmax := by
              rw [hℓ_dt₁, if_neg hv_one]
            rw [hdt]
            exact Nat.lt_of_lt_of_le (positiveRcExcept_card_lt_n (C := C₁) (ℓ := ℓ) hn) hDmax_n
        obtain ⟨Ltail, htail⟩ :=
          ih C₁ hcard₁_le hAll₁ hℓ_L₁ hℓ_rc₁ hBudget₁
        refine ⟨Lstep ++ Ltail, ?_⟩
        rw [runPairs_append]
        change
          let C' := runPairs P C₁ Ltail
          (∀ w : Fin n, (C' w).1.role = .Resetting) ∧
          (∀ w : Fin n, (C' w).1.resetcount = 0) ∧
          (C' ℓ).1.leader = .L
        exact htail

set_option maxHeartbeats 64000000 in
theorem all_resetting_pos_with_leader_to_dormant
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax_n : n ≤ Dmax)
    (C : Config (AgentState n) Opinion n)
    (hAllReset : ∀ w : Fin n, (C w).1.role = .Resetting)
    (hAllPos : ∀ w : Fin n, 0 < (C w).1.resetcount)
    (hHasL : ∃ ℓ : Fin n, (C ℓ).1.leader = .L) :
    ∃ L : List (Fin n × Fin n),
      IsDormantConfig
        (runPairs (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L) := by
  classical
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have hDmax_gt_one : 1 < Dmax := by omega
  obtain ⟨ℓ, hℓ_L⟩ := hHasL
  have hne_of_fin (a : Fin n) : ∃ b : Fin n, b ≠ a := by
    have hcard : 1 < Fintype.card (Fin n) := by
      rw [Fintype.card_fin]
      omega
    exact Fintype.exists_ne_of_one_lt_card hcard a
  obtain ⟨v, hv_ne_ℓ⟩ := hne_of_fin ℓ
  have hℓv : ℓ ≠ v := hv_ne_ℓ.symm
  obtain ⟨L₁, hℓ_role₁, hℓ_rc₁, hℓ_L₁, hℓ_delay₁,
      hv_role₁, hv_rc₁, hv_F₁, hothers₁⟩ :=
    drain_pair_rc_L_any_to_LF_zero_with_u_delay
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hDmax_gt_one C hℓv (hAllReset ℓ) (hAllReset v)
      (hAllPos ℓ) (hAllPos v) hℓ_L
  let C₁ : Config (AgentState n) Opinion n := runPairs P C L₁
  have hAllReset₁ : ∀ w : Fin n, (C₁ w).1.role = .Resetting := by
    intro w
    by_cases hwℓ : w = ℓ
    · subst w
      exact hℓ_role₁
    · by_cases hwv : w = v
      · subst w
        exact hv_role₁
      · dsimp [C₁]
        rw [hothers₁ w hwℓ hwv]
        exact hAllReset w
  have hZeroF₁ :
      ∀ w : Fin n, w ≠ ℓ → (C₁ w).1.resetcount = 0 → (C₁ w).1.leader = .F := by
    intro w hw_ne hw_rc0
    by_cases hwv : w = v
    · subst w
      exact hv_F₁
    · have hw_old : C₁ w = C w := hothers₁ w hw_ne hwv
      have hw_old_rc0 : (C w).1.resetcount = 0 := by
        rw [← hw_old]
        exact hw_rc0
      have hw_pos := hAllPos w
      omega
  have hBudget₁ : (positiveRcExcept C₁ ℓ).card < (C₁ ℓ).1.delaytimer := by
    rw [hℓ_delay₁]
    exact Nat.lt_of_lt_of_le (positiveRcExcept_card_lt_n (C := C₁) (ℓ := ℓ) hn) hDmax_n
  obtain ⟨L₂, hAllReset₂, hℓ_rc₂, hℓ_L₂, hAllRc0_except₂, hAllF_except₂⟩ :=
    drain_positive_except_anchor_to_zero
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hDmax_gt_one hDmax_n C₁ hAllReset₁ hℓ_L₁ hℓ_rc₁ hBudget₁ hZeroF₁
  refine ⟨L₁ ++ L₂, ?_⟩
  rw [runPairs_append]
  change IsDormantConfig (runPairs P C₁ L₂)
  refine ⟨hAllReset₂, ?_, ?_, ?_⟩
  · intro w
    by_cases hwℓ : w = ℓ
    · subst w
      exact hℓ_rc₂
    · exact hAllRc0_except₂ w hwℓ
  · refine ⟨ℓ, hℓ_L₂, ?_⟩
    intro w hwL
    by_cases hwℓ : w = ℓ
    · exact hwℓ
    · have hwF := hAllF_except₂ w hwℓ
      rw [hwF] at hwL
      cases hwL
  · intro w
    cases (runPairs P C₁ L₂ w).1.leader <;> simp

/-! ### Awakening step helpers

When all agents are dormant (Resetting, rc=0, dt=0), scheduling the leader
with any follower fires resetOSSR on both: leader → Settled(rank 0),
follower → Unsettled. After the first step, scheduling the now-Settled root
with remaining dormant followers converts them to Unsettled one by one. -/

set_option maxHeartbeats 64000000 in
/-- RankDeltaOSSR: dormant leader (Resetting, rc=0) meets non-Resetting agent →
leader wakes via resetOSSR (because !partnerResetting = true). -/
theorem rankDeltaOSSR_dormant_leader_wakes
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {s t : AgentState n}
    (hs_res : s.role = .Resetting) (hs_rc : s.resetcount = 0)
    (hs_L : s.leader = .L)
    (ht_not_res : t.role ≠ .Resetting) :
      let r := rankDeltaOSSR Rmax Emax Dmax hn (s, t)
      r.1.role = .Settled ∧ r.1.rank = ⟨0, hn⟩ ∧ r.1.children = 0 ∧
      r.1.leader = s.leader ∧ r.2 = t := by
  unfold rankDeltaOSSR propagateReset processAgent resetOSSR
  simp [hs_res, hs_rc, hs_L, ht_not_res]

theorem rankDeltaOSSR_dormant_follower_wakes
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {s t : AgentState n}
    (hs_res : s.role = .Resetting) (hs_rc : s.resetcount = 0)
    (hs_F : s.leader = .F)
    (ht_not_res : t.role ≠ .Resetting) :
      let r := rankDeltaOSSR Rmax Emax Dmax hn (s, t)
      r.1.role = .Unsettled ∧ r.1.leader = .F ∧ r.2 = t := by
  unfold rankDeltaOSSR propagateReset processAgent resetOSSR
  simp [hs_res, hs_rc, hs_F, ht_not_res]

set_option maxHeartbeats 200000000 in
/-- When two dormant agents (Resetting, rc=0) with dt > 1 interact,
both stay Resetting with dt decreased by 1 and leader preserved. -/
theorem rankDeltaOSSR_dormant_dt_decrease
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {s t : AgentState n}
    (hs : s.role = .Resetting) (hs_rc : s.resetcount = 0)
    (ht : t.role = .Resetting) (ht_rc : t.resetcount = 0)
    (hs_L : s.leader = .L) (ht_F : t.leader = .F)
    (hs_dt : 1 < s.delaytimer) (ht_dt : 1 < t.delaytimer) :
      let r := rankDeltaOSSR Rmax Emax Dmax hn (s, t)
      r.1.role = .Resetting ∧ r.1.resetcount = 0 ∧
      r.1.delaytimer = s.delaytimer - 1 ∧ r.1.leader = .L ∧
      r.2.role = .Resetting ∧ r.2.resetcount = 0 ∧
      r.2.delaytimer = t.delaytimer - 1 ∧ r.2.leader = .F := by
  have hs_dt_ne : s.delaytimer - 1 ≠ 0 := by omega
  have ht_dt_ne : t.delaytimer - 1 ≠ 0 := by omega
  unfold rankDeltaOSSR propagateReset processAgent resetOSSR
  simp [hs, ht, hs_rc, ht_rc, hs_L, ht_F, hs_dt_ne, ht_dt_ne]

set_option maxHeartbeats 200000000 in
/-- When leader has dt ≤ 1: leader wakes via resetOSSR regardless of follower dt. -/
theorem rankDeltaOSSR_dormant_leader_low_dt_wakes
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {s t : AgentState n}
    (hs : s.role = .Resetting) (hs_rc : s.resetcount = 0) (hs_dt : s.delaytimer ≤ 1)
    (hs_L : s.leader = .L)
    (ht : t.role = .Resetting) (ht_rc : t.resetcount = 0)
    (ht_F : t.leader = .F) :
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.role = .Settled ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.rank = ⟨0, hn⟩ ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.children = 0 ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.leader = .L := by
  have hs_dt_zero : s.delaytimer - 1 = 0 := by omega
  unfold rankDeltaOSSR propagateReset processAgent resetOSSR
  simp [hs, hs_rc, hs_dt_zero, hs_L, ht, ht_rc, ht_F]

set_option maxHeartbeats 200000000 in
theorem rankDeltaOSSR_dormant_leader_low_dt_wakes_with_follower_ok
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {s t : AgentState n}
    (hs : s.role = .Resetting) (hs_rc : s.resetcount = 0) (hs_dt : s.delaytimer ≤ 1)
    (hs_L : s.leader = .L)
    (ht : t.role = .Resetting) (ht_rc : t.resetcount = 0)
    (ht_F : t.leader = .F) :
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.role = .Settled ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.rank = ⟨0, hn⟩ ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.children = 0 ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.leader = .L ∧
    ((rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.role = .Unsettled ∨
      ((rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.role = .Resetting ∧
       (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.resetcount = 0)) := by
  have hs_dt_zero : s.delaytimer - 1 = 0 := by omega
  unfold rankDeltaOSSR propagateReset processAgent resetOSSR
  by_cases ht_dt_zero : t.delaytimer - 1 = 0
  · simp [hs, hs_rc, hs_dt_zero, hs_L, ht, ht_rc, ht_F, ht_dt_zero]
  · simp [hs, hs_rc, hs_dt_zero, hs_L, ht, ht_rc, ht_F, ht_dt_zero]

set_option maxHeartbeats 200000000 in
/-- TransitionPEM wrapper: both dormant with dt > 1 → both stay Resetting, dt decreased. -/
theorem transitionPEM_dormant_dt_decrease
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {C : Config (AgentState n) Opinion n}
    {ℓ w : Fin n} (hℓw : ℓ ≠ w)
    (hℓ_res : (C ℓ).1.role = .Resetting) (hℓ_rc : (C ℓ).1.resetcount = 0)
    (hℓ_L : (C ℓ).1.leader = .L)
    (hw_res : (C w).1.role = .Resetting) (hw_rc : (C w).1.resetcount = 0)
    (hw_F : (C w).1.leader = .F)
    (hℓ_dt : 1 < (C ℓ).1.delaytimer) (hw_dt : 1 < (C w).1.delaytimer) :
    let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := C.step P ℓ w
    (C' ℓ).1.role = .Resetting ∧ (C' ℓ).1.resetcount = 0 ∧
    (C' ℓ).1.delaytimer = (C ℓ).1.delaytimer - 1 ∧ (C' ℓ).1.leader = .L ∧
    (C' w).1.role = .Resetting ∧ (C' w).1.resetcount = 0 ∧
    (C' w).1.delaytimer = (C w).1.delaytimer - 1 ∧ (C' w).1.leader = .F := by
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have h_rd := rankDeltaOSSR_dormant_dt_decrease (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
    (hn := hn) hℓ_res hℓ_rc hw_res hw_rc hℓ_L hw_F hℓ_dt hw_dt
  have h_not_both : ¬((rankDeltaOSSR Rmax Emax Dmax hn ((C ℓ).1, (C w).1)).1.role = .Settled ∧
                      (rankDeltaOSSR Rmax Emax Dmax hn ((C ℓ).1, (C w).1)).2.role = .Settled) := by
    intro ⟨h1, _⟩; rw [h_rd.1] at h1; exact Role.noConfusion h1
  have h_pass := transitionPEM_structural_passthrough (trank := Rmax) (Rmax := Rmax)
    (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn) (x₀ := (C ℓ).2) (x₁ := (C w).2) h_not_both
  have h_fst := Config.step_fst_state P C hℓw
  have h_snd := Config.step_snd_state P C hℓw hℓw.symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [congrArg AgentState.role h_fst]; exact h_pass.1 ▸ h_rd.1
  · rw [congrArg AgentState.resetcount h_fst]; exact h_pass.2.2.2.2.1 ▸ h_rd.2.1
  · rw [congrArg AgentState.delaytimer h_fst]; exact h_pass.2.2.2.2.2.1 ▸ h_rd.2.2.1
  · rw [congrArg AgentState.leader h_fst]; exact h_pass.2.1 ▸ h_rd.2.2.2.1
  · rw [congrArg AgentState.role h_snd]; exact h_pass.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.2.1
  · rw [congrArg AgentState.resetcount h_snd]; exact h_pass.2.2.2.2.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.2.2.1
  · rw [congrArg AgentState.delaytimer h_snd]; exact h_pass.2.2.2.2.2.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.2.2.2.1
  · rw [congrArg AgentState.leader h_snd]; exact h_pass.2.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.2.2.2.2

set_option maxHeartbeats 64000000 in
theorem transitionPEM_dormant_leader_low_dt_wakes
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {C : Config (AgentState n) Opinion n}
    {ℓ w : Fin n} (hℓw : ℓ ≠ w)
    (hℓ_res : (C ℓ).1.role = .Resetting) (hℓ_rc : (C ℓ).1.resetcount = 0)
    (hℓ_dt : (C ℓ).1.delaytimer ≤ 1) (hℓ_L : (C ℓ).1.leader = .L)
    (hw_res : (C w).1.role = .Resetting) (hw_rc : (C w).1.resetcount = 0)
    (hw_F : (C w).1.leader = .F) :
    let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := C.step P ℓ w
    (C' ℓ).1.role = .Settled ∧
    (C' ℓ).1.rank = ⟨0, hn⟩ ∧
    (C' ℓ).1.children = 0 ∧
    (C' ℓ).1.leader = .L ∧
    ((C' w).1.role = .Unsettled ∨
      ((C' w).1.role = .Resetting ∧ (C' w).1.resetcount = 0)) := by
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have h_rd :=
    rankDeltaOSSR_dormant_leader_low_dt_wakes_with_follower_ok
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hℓ_res hℓ_rc hℓ_dt hℓ_L hw_res hw_rc hw_F
  have h_not_both :
      ¬((rankDeltaOSSR Rmax Emax Dmax hn ((C ℓ).1, (C w).1)).1.role = .Settled ∧
        (rankDeltaOSSR Rmax Emax Dmax hn ((C ℓ).1, (C w).1)).2.role = .Settled) := by
    intro hboth
    rcases h_rd.2.2.2.2 with hw_unsettled | hw_reset
    · rw [hw_unsettled] at hboth
      exact Role.noConfusion hboth.2
    · rw [hw_reset.1] at hboth
      exact Role.noConfusion hboth.2
  have h_pass := transitionPEM_structural_passthrough (trank := Rmax) (Rmax := Rmax)
    (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn) (x₀ := (C ℓ).2) (x₁ := (C w).2) h_not_both
  have h_fst := Config.step_fst_state P C hℓw
  have h_snd := Config.step_snd_state P C hℓw hℓw.symm
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [congrArg AgentState.role h_fst]
    exact h_pass.1 ▸ h_rd.1
  · rw [congrArg AgentState.rank h_fst]
    exact h_pass.2.2.1 ▸ h_rd.2.1
  · rw [congrArg AgentState.children h_fst]
    exact h_pass.2.2.2.1 ▸ h_rd.2.2.1
  · rw [congrArg AgentState.leader h_fst]
    exact h_pass.2.1 ▸ h_rd.2.2.2.1
  · rcases h_rd.2.2.2.2 with hw_unsettled | hw_reset
    · exact Or.inl (by
        rw [congrArg AgentState.role h_snd]
        exact h_pass.2.2.2.2.2.2.1 ▸ hw_unsettled)
    · exact Or.inr ⟨by
        rw [congrArg AgentState.role h_snd]
        exact h_pass.2.2.2.2.2.2.1 ▸ hw_reset.1, by
        rw [congrArg AgentState.resetcount h_snd]
        exact h_pass.2.2.2.2.2.2.2.2.2.2.1 ▸ hw_reset.2⟩

theorem rankDeltaOSSR_dormant_leader_low_dt_follower_leader
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {s t : AgentState n}
    (hs : s.role = .Resetting) (hs_rc : s.resetcount = 0) (hs_dt : s.delaytimer ≤ 1)
    (hs_L : s.leader = .L)
    (ht : t.role = .Resetting) (ht_rc : t.resetcount = 0)
    (ht_F : t.leader = .F) :
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.leader = .F := by
  have hs_dt_zero : s.delaytimer - 1 = 0 := by omega
  unfold rankDeltaOSSR propagateReset processAgent resetOSSR
  by_cases ht_dt_zero : t.delaytimer - 1 = 0
  · simp [hs, hs_rc, hs_dt_zero, hs_L, ht, ht_rc, ht_F, ht_dt_zero]
  · simp [hs, hs_rc, hs_dt_zero, hs_L, ht, ht_rc, ht_F, ht_dt_zero]

theorem transitionPEM_dormant_leader_low_dt_follower_leader
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {C : Config (AgentState n) Opinion n}
    {ℓ w : Fin n} (hℓw : ℓ ≠ w)
    (hℓ_res : (C ℓ).1.role = .Resetting) (hℓ_rc : (C ℓ).1.resetcount = 0)
    (hℓ_dt : (C ℓ).1.delaytimer ≤ 1) (hℓ_L : (C ℓ).1.leader = .L)
    (hw_res : (C w).1.role = .Resetting) (hw_rc : (C w).1.resetcount = 0)
    (hw_F : (C w).1.leader = .F) :
    let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := C.step P ℓ w
    (C' w).1.leader = .F := by
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have h_rd :=
    rankDeltaOSSR_dormant_leader_low_dt_follower_leader
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hℓ_res hℓ_rc hℓ_dt hℓ_L hw_res hw_rc hw_F
  have h_role :=
    rankDeltaOSSR_dormant_leader_low_dt_wakes_with_follower_ok
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hℓ_res hℓ_rc hℓ_dt hℓ_L hw_res hw_rc hw_F
  have h_not_both :
      ¬((rankDeltaOSSR Rmax Emax Dmax hn ((C ℓ).1, (C w).1)).1.role = .Settled ∧
        (rankDeltaOSSR Rmax Emax Dmax hn ((C ℓ).1, (C w).1)).2.role = .Settled) := by
    intro hboth
    rcases h_role.2.2.2.2 with hw_unsettled | hw_reset
    · rw [hw_unsettled] at hboth
      exact Role.noConfusion hboth.2
    · rw [hw_reset.1] at hboth
      exact Role.noConfusion hboth.2
  have h_pass := transitionPEM_structural_passthrough (trank := Rmax) (Rmax := Rmax)
    (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn) (x₀ := (C ℓ).2) (x₁ := (C w).2) h_not_both
  have h_snd := Config.step_snd_state P C hℓw hℓw.symm
  change (Config.step P C ℓ w w).1.leader = .F
  rw [congrArg AgentState.leader h_snd]
  exact h_pass.2.2.2.2.2.2.2.1 ▸ h_rd

theorem rankDeltaOSSR_dormant_leader_low_dt_L_partner_wakes
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {s t : AgentState n}
    (hs : s.role = .Resetting) (hs_rc : s.resetcount = 0) (hs_dt : s.delaytimer ≤ 1)
    (hs_L : s.leader = .L)
    (ht : t.role = .Resetting) (ht_rc : t.resetcount = 0)
    (ht_L : t.leader = .L) :
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.role = .Settled ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.rank = ⟨0, hn⟩ ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.children = 0 ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.leader = .L ∧
    (((rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.role = .Settled ∧
        (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.rank = ⟨0, hn⟩ ∧
        (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.children = 0 ∧
        (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.leader = .L) ∨
      ((rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.role = .Resetting ∧
        (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.resetcount = 0 ∧
        (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.leader = .L)) := by
  have hs_dt_zero : s.delaytimer - 1 = 0 := by omega
  unfold rankDeltaOSSR propagateReset processAgent resetOSSR
  by_cases ht_dt_zero : t.delaytimer - 1 = 0
  · simp [hs, hs_rc, hs_dt_zero, hs_L, ht, ht_rc, ht_L, ht_dt_zero]
  · simp [hs, hs_rc, hs_dt_zero, hs_L, ht, ht_rc, ht_L, ht_dt_zero]

set_option maxHeartbeats 200000000 in
theorem rankDeltaOSSR_dormant_follower_low_dt_unsettles
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {s t : AgentState n}
    (hs : s.role = .Resetting) (hs_rc : s.resetcount = 0) (hs_dt : 1 < s.delaytimer)
    (hs_L : s.leader = .L)
    (ht : t.role = .Resetting) (ht_rc : t.resetcount = 0) (ht_dt : t.delaytimer ≤ 1)
    (ht_F : t.leader = .F) :
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.role = .Resetting ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.resetcount = 0 ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.delaytimer = s.delaytimer - 1 ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.leader = .L ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.role = .Unsettled ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.leader = .F := by
  have hs_dt_ne : s.delaytimer - 1 ≠ 0 := by omega
  have ht_dt_zero : t.delaytimer - 1 = 0 := by omega
  unfold rankDeltaOSSR propagateReset processAgent resetOSSR
  simp [hs, hs_rc, hs_dt_ne, hs_L, ht, ht_rc, ht_dt_zero, ht_F]

set_option maxHeartbeats 64000000 in
theorem transitionPEM_dormant_follower_low_dt_unsettles
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {C : Config (AgentState n) Opinion n}
    {ℓ w : Fin n} (hℓw : ℓ ≠ w)
    (hℓ_res : (C ℓ).1.role = .Resetting) (hℓ_rc : (C ℓ).1.resetcount = 0)
    (hℓ_dt : 1 < (C ℓ).1.delaytimer) (hℓ_L : (C ℓ).1.leader = .L)
    (hw_res : (C w).1.role = .Resetting) (hw_rc : (C w).1.resetcount = 0)
    (hw_dt : (C w).1.delaytimer ≤ 1) (hw_F : (C w).1.leader = .F) :
    let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := C.step P ℓ w
    (C' ℓ).1.role = .Resetting ∧
    (C' ℓ).1.resetcount = 0 ∧
    (C' ℓ).1.delaytimer = (C ℓ).1.delaytimer - 1 ∧
    (C' ℓ).1.leader = .L ∧
    (C' w).1.role = .Unsettled ∧
    (C' w).1.leader = .F := by
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have h_rd :=
    rankDeltaOSSR_dormant_follower_low_dt_unsettles
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hℓ_res hℓ_rc hℓ_dt hℓ_L hw_res hw_rc hw_dt hw_F
  have h_not_both :
      ¬((rankDeltaOSSR Rmax Emax Dmax hn ((C ℓ).1, (C w).1)).1.role = .Settled ∧
        (rankDeltaOSSR Rmax Emax Dmax hn ((C ℓ).1, (C w).1)).2.role = .Settled) := by
    intro hboth
    rw [h_rd.1] at hboth
    exact Role.noConfusion hboth.1
  have h_pass := transitionPEM_structural_passthrough (trank := Rmax) (Rmax := Rmax)
    (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn) (x₀ := (C ℓ).2) (x₁ := (C w).2) h_not_both
  have h_fst := Config.step_fst_state P C hℓw
  have h_snd := Config.step_snd_state P C hℓw hℓw.symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [congrArg AgentState.role h_fst]
    exact h_pass.1 ▸ h_rd.1
  · rw [congrArg AgentState.resetcount h_fst]
    exact h_pass.2.2.2.2.1 ▸ h_rd.2.1
  · rw [congrArg AgentState.delaytimer h_fst]
    exact h_pass.2.2.2.2.2.1 ▸ h_rd.2.2.1
  · rw [congrArg AgentState.leader h_fst]
    exact h_pass.2.1 ▸ h_rd.2.2.2.1
  · rw [congrArg AgentState.role h_snd]
    exact h_pass.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.2.1
  · rw [congrArg AgentState.leader h_snd]
    exact h_pass.2.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.2.2

set_option maxHeartbeats 64000000 in
theorem transitionPEM_dormant_follower_with_unsettled_partner_wakes
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {C : Config (AgentState n) Opinion n}
    {u w : Fin n} (huw : u ≠ w)
    (hu_res : (C u).1.role = .Resetting) (hu_rc : (C u).1.resetcount = 0)
    (hu_F : (C u).1.leader = .F)
    (hw_unsettled : (C w).1.role = .Unsettled) :
    let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := C.step P u w
    (C' u).1.role = .Unsettled ∧
    (C' u).1.leader = .F ∧
    (C' w).1.role = .Unsettled := by
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have h_rd := rankDeltaOSSR_dormant_follower_wakes
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hu_res hu_rc hu_F (by rw [hw_unsettled]; decide)
  have h_not_both :
      ¬((rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C w).1)).1.role = .Settled ∧
        (rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C w).1)).2.role = .Settled) := by
    intro hboth
    rw [h_rd.1] at hboth
    exact Role.noConfusion hboth.1
  have h_pass := transitionPEM_structural_passthrough (trank := Rmax) (Rmax := Rmax)
    (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn) (x₀ := (C u).2) (x₁ := (C w).2) h_not_both
  have h_fst := Config.step_fst_state P C huw
  have h_snd := Config.step_snd_state P C huw huw.symm
  refine ⟨?_, ?_, ?_⟩
  · rw [congrArg AgentState.role h_fst]
    exact h_pass.1 ▸ h_rd.1
  · rw [congrArg AgentState.leader h_fst]
    exact h_pass.2.1 ▸ h_rd.2.1
  · rw [congrArg AgentState.role h_snd]
    change
      (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
        (C u, C w)).2.role = .Unsettled
    rw [h_pass.2.2.2.2.2.2.1, h_rd.2.2]
    exact hw_unsettled

theorem transitionPEM_dormant_follower_with_nonresetting_partner_wakes
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {C : Config (AgentState n) Opinion n}
    {u w : Fin n} (huw : u ≠ w)
    (hu_res : (C u).1.role = .Resetting) (hu_rc : (C u).1.resetcount = 0)
    (hu_F : (C u).1.leader = .F)
    (hw_not_reset : (C w).1.role ≠ .Resetting) :
    let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := C.step P u w
    (C' u).1.role = .Unsettled ∧
    (C' u).1.leader = .F ∧
    (C' w).1.role = (C w).1.role := by
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have h_rd := rankDeltaOSSR_dormant_follower_wakes
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hu_res hu_rc hu_F hw_not_reset
  have h_not_both :
      ¬((rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C w).1)).1.role = .Settled ∧
        (rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C w).1)).2.role = .Settled) := by
    intro hboth
    rw [h_rd.1] at hboth
    exact Role.noConfusion hboth.1
  have h_pass := transitionPEM_structural_passthrough (trank := Rmax) (Rmax := Rmax)
    (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn) (x₀ := (C u).2) (x₁ := (C w).2) h_not_both
  have h_fst := Config.step_fst_state P C huw
  have h_snd := Config.step_snd_state P C huw huw.symm
  refine ⟨?_, ?_, ?_⟩
  · rw [congrArg AgentState.role h_fst]
    exact h_pass.1 ▸ h_rd.1
  · rw [congrArg AgentState.leader h_fst]
    exact h_pass.2.1 ▸ h_rd.2.1
  · rw [h_snd]
    change
      (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
        (C u, C w)).2.role = (C w).1.role
    rw [h_pass.2.2.2.2.2.2.1]
    exact congrArg AgentState.role h_rd.2.2

theorem dormant_follower_unsettled_step_resettingCount_lt
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {C : Config (AgentState n) Opinion n}
    {u w : Fin n} (huw : u ≠ w)
    (hu_res : (C u).1.role = .Resetting) (hu_rc : (C u).1.resetcount = 0)
    (hu_F : (C u).1.leader = .F)
    (hw_unsettled : (C w).1.role = .Unsettled) :
    let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    resettingCount (C.step P u w) < resettingCount C := by
  classical
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  let C' : Config (AgentState n) Opinion n := C.step P u w
  have hstep := by
    simpa [P, C'] using
      (transitionPEM_dormant_follower_with_unsettled_partner_wakes
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        (C := C) (u := u) (w := w) huw hu_res hu_rc hu_F hw_unsettled)
  set S := Finset.univ.filter (fun x : Fin n => (C x).1.role = .Resetting) with hS
  set S' := Finset.univ.filter (fun x : Fin n => (C' x).1.role = .Resetting) with hS'
  have hu_mem : u ∈ S := by
    rw [hS, Finset.mem_filter]
    exact ⟨Finset.mem_univ u, hu_res⟩
  have hsub : S' ⊆ S.erase u := by
    intro x hx
    have hx_reset : (C' x).1.role = .Resetting := by
      rw [hS'] at hx
      exact (Finset.mem_filter.mp hx).2
    have hx_ne_u : x ≠ u := by
      intro hxu
      subst x
      rw [hstep.1] at hx_reset
      cases hx_reset
    have hx_ne_w : x ≠ w := by
      intro hxw
      subst x
      rw [hstep.2.2] at hx_reset
      cases hx_reset
    have hx_old : C' x = C x := by
      dsimp [C', P]
      simp [Config.step, huw, hx_ne_u, hx_ne_w]
    have hx_mem_old : x ∈ S := by
      rw [hS, Finset.mem_filter]
      rw [hx_old] at hx_reset
      exact ⟨Finset.mem_univ x, hx_reset⟩
    exact Finset.mem_erase.mpr ⟨hx_ne_u, hx_mem_old⟩
  have hle : S'.card ≤ (S.erase u).card := Finset.card_le_card hsub
  have herase : (S.erase u).card = S.card - 1 := Finset.card_erase_of_mem hu_mem
  have hpos : 0 < S.card := Finset.card_pos.mpr ⟨u, hu_mem⟩
  have hlt : S'.card < S.card := by
    rw [herase] at hle
    omega
  have hS_card : S.card = resettingCount C := by
    rw [hS]
    rfl
  have hS'_card : S'.card = resettingCount C' := by
    rw [hS']
    rfl
  change resettingCount C' < resettingCount C
  simpa [hS_card, hS'_card] using hlt

theorem dormant_follower_nonresetting_step_resettingCount_lt
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {C : Config (AgentState n) Opinion n}
    {u w : Fin n} (huw : u ≠ w)
    (hu_res : (C u).1.role = .Resetting) (hu_rc : (C u).1.resetcount = 0)
    (hu_F : (C u).1.leader = .F)
    (hw_not_reset : (C w).1.role ≠ .Resetting) :
    let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    resettingCount (C.step P u w) < resettingCount C := by
  classical
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  let C' : Config (AgentState n) Opinion n := C.step P u w
  have hstep := by
    simpa [P, C'] using
      (transitionPEM_dormant_follower_with_nonresetting_partner_wakes
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        (C := C) (u := u) (w := w) huw hu_res hu_rc hu_F hw_not_reset)
  set S := Finset.univ.filter (fun x : Fin n => (C x).1.role = .Resetting) with hS
  set S' := Finset.univ.filter (fun x : Fin n => (C' x).1.role = .Resetting) with hS'
  have hu_mem : u ∈ S := by
    rw [hS, Finset.mem_filter]
    exact ⟨Finset.mem_univ u, hu_res⟩
  have hsub : S' ⊆ S.erase u := by
    intro x hx
    have hx_reset : (C' x).1.role = .Resetting := by
      rw [hS'] at hx
      exact (Finset.mem_filter.mp hx).2
    have hx_ne_u : x ≠ u := by
      intro hxu
      subst x
      rw [hstep.1] at hx_reset
      cases hx_reset
    have hx_ne_w : x ≠ w := by
      intro hxw
      subst x
      rw [hstep.2.2] at hx_reset
      exact hw_not_reset hx_reset
    have hx_old : C' x = C x := by
      dsimp [C', P]
      simp [Config.step, huw, hx_ne_u, hx_ne_w]
    have hx_mem_old : x ∈ S := by
      rw [hS, Finset.mem_filter]
      rw [hx_old] at hx_reset
      exact ⟨Finset.mem_univ x, hx_reset⟩
    exact Finset.mem_erase.mpr ⟨hx_ne_u, hx_mem_old⟩
  have hle : S'.card ≤ (S.erase u).card := Finset.card_le_card hsub
  have herase : (S.erase u).card = S.card - 1 := Finset.card_erase_of_mem hu_mem
  have hpos : 0 < S.card := Finset.card_pos.mpr ⟨u, hu_mem⟩
  have hlt : S'.card < S.card := by
    rw [herase] at hle
    omega
  have hS_card : S.card = resettingCount C := by
    rw [hS]
    rfl
  have hS'_card : S'.card = resettingCount C' := by
    rw [hS']
    rfl
  change resettingCount C' < resettingCount C
  simpa [hS_card, hS'_card] using hlt

theorem dormant_follower_unsettled_step_followerDormantMeasure_lt
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {C : Config (AgentState n) Opinion n}
    {u w : Fin n} (huw : u ≠ w)
    (hu_res : (C u).1.role = .Resetting) (hu_rc : (C u).1.resetcount = 0)
    (hu_F : (C u).1.leader = .F)
    (hw_unsettled : (C w).1.role = .Unsettled) :
    let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    followerDormantMeasure (C.step P u w) < followerDormantMeasure C := by
  classical
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  let C' : Config (AgentState n) Opinion n := C.step P u w
  have hstep := by
    simpa [P, C'] using
      (transitionPEM_dormant_follower_with_unsettled_partner_wakes
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        (C := C) (u := u) (w := w) huw hu_res hu_rc hu_F hw_unsettled)
  have hu_lt :
      followerDormantContribution (C' u).1 <
        followerDormantContribution (C u).1 := by
    unfold followerDormantContribution
    rw [hstep.1, hu_res]
    simp
  have hw_le :
      followerDormantContribution (C' w).1 ≤
        followerDormantContribution (C w).1 := by
    unfold followerDormantContribution
    rw [hstep.2.2, hw_unsettled]
    simp
  have hpointwise :
      ∀ x ∈ (Finset.univ : Finset (Fin n)),
        followerDormantContribution (C' x).1 ≤ followerDormantContribution (C x).1 := by
    intro x _
    by_cases hxu : x = u
    · subst x
      exact le_of_lt hu_lt
    · by_cases hxw : x = w
      · subst x
        exact hw_le
      · have hx_state : C' x = C x := by
          dsimp [C', P]
          simp [Config.step, huw, hxu, hxw]
        rw [hx_state]
  have hstrict :
      ∃ x ∈ (Finset.univ : Finset (Fin n)),
        followerDormantContribution (C' x).1 < followerDormantContribution (C x).1 :=
    ⟨u, Finset.mem_univ u, hu_lt⟩
  change followerDormantMeasure C' < followerDormantMeasure C
  unfold followerDormantMeasure
  exact Finset.sum_lt_sum hpointwise hstrict

theorem dormant_follower_nonresetting_step_followerDormantMeasure_lt
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {C : Config (AgentState n) Opinion n}
    {u w : Fin n} (huw : u ≠ w)
    (hu_res : (C u).1.role = .Resetting) (hu_rc : (C u).1.resetcount = 0)
    (hu_F : (C u).1.leader = .F)
    (hw_not_reset : (C w).1.role ≠ .Resetting) :
    let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    followerDormantMeasure (C.step P u w) < followerDormantMeasure C := by
  classical
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  let C' : Config (AgentState n) Opinion n := C.step P u w
  have hstep := by
    simpa [P, C'] using
      (transitionPEM_dormant_follower_with_nonresetting_partner_wakes
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        (C := C) (u := u) (w := w) huw hu_res hu_rc hu_F hw_not_reset)
  have hu_lt :
      followerDormantContribution (C' u).1 <
        followerDormantContribution (C u).1 := by
    unfold followerDormantContribution
    rw [hstep.1, hu_res]
    simp
  have hw_le :
      followerDormantContribution (C' w).1 ≤
        followerDormantContribution (C w).1 := by
    unfold followerDormantContribution
    rw [hstep.2.2]
    simp [hw_not_reset]
  have hpointwise :
      ∀ x ∈ (Finset.univ : Finset (Fin n)),
        followerDormantContribution (C' x).1 ≤ followerDormantContribution (C x).1 := by
    intro x _
    by_cases hxu : x = u
    · subst x
      exact le_of_lt hu_lt
    · by_cases hxw : x = w
      · subst x
        exact hw_le
      · have hx_state : C' x = C x := by
          dsimp [C', P]
          simp [Config.step, huw, hxu, hxw]
        rw [hx_state]
  have hstrict :
      ∃ x ∈ (Finset.univ : Finset (Fin n)),
        followerDormantContribution (C' x).1 < followerDormantContribution (C x).1 :=
    ⟨u, Finset.mem_univ u, hu_lt⟩
  change followerDormantMeasure C' < followerDormantMeasure C
  unfold followerDormantMeasure
  exact Finset.sum_lt_sum hpointwise hstrict

set_option maxHeartbeats 64000000 in
theorem transitionPEM_dormant_leader_with_unsettled_follower_wakes
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {C : Config (AgentState n) Opinion n}
    {ℓ w : Fin n} (hℓw : ℓ ≠ w)
    (hℓ_res : (C ℓ).1.role = .Resetting) (hℓ_rc : (C ℓ).1.resetcount = 0)
    (hℓ_L : (C ℓ).1.leader = .L)
    (hw_unsettled : (C w).1.role = .Unsettled) (hw_F : (C w).1.leader = .F) :
    let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := C.step P ℓ w
    (C' ℓ).1.role = .Settled ∧
    (C' ℓ).1.rank = ⟨0, hn⟩ ∧
    (C' ℓ).1.children = 0 ∧
    (C' ℓ).1.leader = .L ∧
    (C' w).1.role = .Unsettled ∧
    (C' w).1.leader = .F := by
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have h_rd := rankDeltaOSSR_dormant_leader_wakes
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hℓ_res hℓ_rc hℓ_L (by rw [hw_unsettled]; decide)
  have h_not_both :
      ¬((rankDeltaOSSR Rmax Emax Dmax hn ((C ℓ).1, (C w).1)).1.role = .Settled ∧
        (rankDeltaOSSR Rmax Emax Dmax hn ((C ℓ).1, (C w).1)).2.role = .Settled) := by
    intro hboth
    have hw_role : (rankDeltaOSSR Rmax Emax Dmax hn ((C ℓ).1, (C w).1)).2.role = .Unsettled := by
      rw [h_rd.2.2.2.2]
      exact hw_unsettled
    rw [hw_role] at hboth
    exact Role.noConfusion hboth.2
  have h_pass := transitionPEM_structural_passthrough (trank := Rmax) (Rmax := Rmax)
    (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn) (x₀ := (C ℓ).2) (x₁ := (C w).2) h_not_both
  have h_fst := Config.step_fst_state P C hℓw
  have h_snd := Config.step_snd_state P C hℓw hℓw.symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [congrArg AgentState.role h_fst]
    exact h_pass.1 ▸ h_rd.1
  · rw [congrArg AgentState.rank h_fst]
    exact h_pass.2.2.1 ▸ h_rd.2.1
  · rw [congrArg AgentState.children h_fst]
    exact h_pass.2.2.2.1 ▸ h_rd.2.2.1
  · rw [congrArg AgentState.leader h_fst]
    change
      (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
        (C ℓ, C w)).1.leader = .L
    rw [h_pass.2.1, h_rd.2.2.2.1]
    exact hℓ_L
  · rw [congrArg AgentState.role h_snd]
    change
      (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
        (C ℓ, C w)).2.role = .Unsettled
    rw [h_pass.2.2.2.2.2.2.1, h_rd.2.2.2.2]
    exact hw_unsettled
  · rw [congrArg AgentState.leader h_snd]
    change
      (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
        (C ℓ, C w)).2.leader = .F
    rw [h_pass.2.2.2.2.2.2.2.1, h_rd.2.2.2.2]
    exact hw_F

set_option maxHeartbeats 64000000 in
/-- RankDeltaOSSR on two dormant agents (leader + follower): both fire resetOSSR. -/
theorem rankDeltaOSSR_both_dormant
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {s t : AgentState n}
    (hs_res : s.role = .Resetting) (hs_rc : s.resetcount = 0) (hs_dt : s.delaytimer = 0)
    (ht_res : t.role = .Resetting) (ht_rc : t.resetcount = 0) (ht_dt : t.delaytimer = 0)
    (hs_L : s.leader = .L) (ht_F : t.leader = .F) :
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.role = .Settled ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.rank = ⟨0, hn⟩ ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.children = 0 ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.role = .Unsettled := by
  unfold rankDeltaOSSR propagateReset processAgent resetOSSR
  simp [hs_res, hs_rc, hs_dt, hs_L, ht_res, ht_rc, ht_dt, ht_F]

set_option maxHeartbeats 64000000 in
/-- Two follower dormant agents with low delay timers both leave Resetting. -/
theorem rankDeltaOSSR_both_dormant_followers_low_dt
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {s t : AgentState n}
    (hs_res : s.role = .Resetting) (hs_rc : s.resetcount = 0)
    (hs_dt : s.delaytimer ≤ 1) (hs_F : s.leader = .F)
    (ht_res : t.role = .Resetting) (ht_rc : t.resetcount = 0)
    (ht_dt : t.delaytimer ≤ 1) (ht_F : t.leader = .F) :
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.role = .Unsettled ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.role = .Unsettled := by
  have hs_dt_zero : s.delaytimer - 1 = 0 := by omega
  have ht_dt_zero : t.delaytimer - 1 = 0 := by omega
  unfold rankDeltaOSSR propagateReset processAgent resetOSSR
  simp [hs_res, hs_rc, hs_dt_zero, hs_F, ht_res, ht_rc, ht_dt_zero, ht_F]

set_option maxHeartbeats 64000000 in
theorem transitionPEM_both_dormant_followers_low_dt_unsettle
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {C : Config (AgentState n) Opinion n}
    {u v : Fin n} (huv : u ≠ v)
    (hu_res : (C u).1.role = .Resetting) (hu_rc : (C u).1.resetcount = 0)
    (hu_dt : (C u).1.delaytimer ≤ 1) (hu_F : (C u).1.leader = .F)
    (hv_res : (C v).1.role = .Resetting) (hv_rc : (C v).1.resetcount = 0)
    (hv_dt : (C v).1.delaytimer ≤ 1) (hv_F : (C v).1.leader = .F) :
    let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := C.step P u v
    (C' u).1.role = .Unsettled ∧ (C' v).1.role = .Unsettled := by
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have h_rd :=
    rankDeltaOSSR_both_dormant_followers_low_dt
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hu_res hu_rc hu_dt hu_F hv_res hv_rc hv_dt hv_F
  have h_not_both :
      ¬((rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1)).1.role = .Settled ∧
        (rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1)).2.role = .Settled) := by
    intro hboth
    rw [h_rd.1] at hboth
    exact Role.noConfusion hboth.1
  have h_pass := transitionPEM_structural_passthrough (trank := Rmax) (Rmax := Rmax)
    (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn) (x₀ := (C u).2) (x₁ := (C v).2)
    h_not_both
  have h_fst := Config.step_fst_state P C huv
  have h_snd := Config.step_snd_state P C huv huv.symm
  refine ⟨?_, ?_⟩
  · rw [congrArg AgentState.role h_fst]
    exact h_pass.1 ▸ h_rd.1
  · rw [congrArg AgentState.role h_snd]
    exact h_pass.2.2.2.2.2.2.1 ▸ h_rd.2

theorem both_dormant_followers_low_dt_step_resettingCount_lt
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {C : Config (AgentState n) Opinion n}
    {u v : Fin n} (huv : u ≠ v)
    (hu_res : (C u).1.role = .Resetting) (hu_rc : (C u).1.resetcount = 0)
    (hu_dt : (C u).1.delaytimer ≤ 1) (hu_F : (C u).1.leader = .F)
    (hv_res : (C v).1.role = .Resetting) (hv_rc : (C v).1.resetcount = 0)
    (hv_dt : (C v).1.delaytimer ≤ 1) (hv_F : (C v).1.leader = .F) :
    let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    resettingCount (C.step P u v) < resettingCount C := by
  classical
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  let C' : Config (AgentState n) Opinion n := C.step P u v
  have hstep := by
    simpa [P, C'] using
      (transitionPEM_both_dormant_followers_low_dt_unsettle
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        (C := C) (u := u) (v := v) huv hu_res hu_rc hu_dt hu_F hv_res hv_rc hv_dt hv_F)
  set S := Finset.univ.filter (fun x : Fin n => (C x).1.role = .Resetting) with hS
  set S' := Finset.univ.filter (fun x : Fin n => (C' x).1.role = .Resetting) with hS'
  have hu_mem : u ∈ S := by
    rw [hS, Finset.mem_filter]
    exact ⟨Finset.mem_univ u, hu_res⟩
  have hsub : S' ⊆ S.erase u := by
    intro x hx
    have hx_reset : (C' x).1.role = .Resetting := by
      rw [hS'] at hx
      exact (Finset.mem_filter.mp hx).2
    have hx_ne_u : x ≠ u := by
      intro hxu
      subst x
      rw [hstep.1] at hx_reset
      cases hx_reset
    have hx_ne_v : x ≠ v := by
      intro hxv
      subst x
      rw [hstep.2] at hx_reset
      cases hx_reset
    have hx_old : C' x = C x := by
      dsimp [C', P]
      simp [Config.step, huv, hx_ne_u, hx_ne_v]
    have hx_mem_old : x ∈ S := by
      rw [hS, Finset.mem_filter]
      rw [hx_old] at hx_reset
      exact ⟨Finset.mem_univ x, hx_reset⟩
    exact Finset.mem_erase.mpr ⟨hx_ne_u, hx_mem_old⟩
  have hle : S'.card ≤ (S.erase u).card := Finset.card_le_card hsub
  have herase : (S.erase u).card = S.card - 1 := Finset.card_erase_of_mem hu_mem
  have hpos : 0 < S.card := Finset.card_pos.mpr ⟨u, hu_mem⟩
  have hlt : S'.card < S.card := by
    rw [herase] at hle
    omega
  have hS_card : S.card = resettingCount C := by
    rw [hS]
    rfl
  have hS'_card : S'.card = resettingCount C' := by
    rw [hS']
    rfl
  change resettingCount C' < resettingCount C
  simpa [hS_card, hS'_card] using hlt

theorem both_dormant_followers_low_dt_step_followerDormantMeasure_lt
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {C : Config (AgentState n) Opinion n}
    {u v : Fin n} (huv : u ≠ v)
    (hu_res : (C u).1.role = .Resetting) (hu_rc : (C u).1.resetcount = 0)
    (hu_dt : (C u).1.delaytimer ≤ 1) (hu_F : (C u).1.leader = .F)
    (hv_res : (C v).1.role = .Resetting) (hv_rc : (C v).1.resetcount = 0)
    (hv_dt : (C v).1.delaytimer ≤ 1) (hv_F : (C v).1.leader = .F) :
    let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    followerDormantMeasure (C.step P u v) < followerDormantMeasure C := by
  classical
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  let C' : Config (AgentState n) Opinion n := C.step P u v
  have hstep := by
    simpa [P, C'] using
      (transitionPEM_both_dormant_followers_low_dt_unsettle
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        (C := C) (u := u) (v := v) huv hu_res hu_rc hu_dt hu_F hv_res hv_rc hv_dt hv_F)
  have hu_lt :
      followerDormantContribution (C' u).1 <
        followerDormantContribution (C u).1 := by
    unfold followerDormantContribution
    rw [hstep.1, hu_res]
    simp
  have hv_le :
      followerDormantContribution (C' v).1 ≤
        followerDormantContribution (C v).1 := by
    unfold followerDormantContribution
    rw [hstep.2, hv_res]
    simp
  have hpointwise :
      ∀ x ∈ (Finset.univ : Finset (Fin n)),
        followerDormantContribution (C' x).1 ≤ followerDormantContribution (C x).1 := by
    intro x _
    by_cases hxu : x = u
    · subst x
      exact le_of_lt hu_lt
    · by_cases hxv : x = v
      · subst x
        exact hv_le
      · have hx_state : C' x = C x := by
          dsimp [C', P]
          simp [Config.step, huv, hxu, hxv]
        rw [hx_state]
  have hstrict :
      ∃ x ∈ (Finset.univ : Finset (Fin n)),
        followerDormantContribution (C' x).1 < followerDormantContribution (C x).1 :=
    ⟨u, Finset.mem_univ u, hu_lt⟩
  change followerDormantMeasure C' < followerDormantMeasure C
  unfold followerDormantMeasure
  exact Finset.sum_lt_sum hpointwise hstrict

set_option maxHeartbeats 200000000 in
/-- Two follower dormant agents with high delay timers stay Resetting and both
delay timers decrease. -/
theorem rankDeltaOSSR_both_dormant_followers_dt_decrease
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {s t : AgentState n}
    (hs_res : s.role = .Resetting) (hs_rc : s.resetcount = 0)
    (hs_dt : 1 < s.delaytimer) (hs_F : s.leader = .F)
    (ht_res : t.role = .Resetting) (ht_rc : t.resetcount = 0)
    (ht_dt : 1 < t.delaytimer) (ht_F : t.leader = .F) :
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.role = .Resetting ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.resetcount = 0 ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.delaytimer = s.delaytimer - 1 ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.leader = .F ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.role = .Resetting ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.resetcount = 0 ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.delaytimer = t.delaytimer - 1 ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.leader = .F := by
  have hs_dt_ne : s.delaytimer - 1 ≠ 0 := by omega
  have ht_dt_ne : t.delaytimer - 1 ≠ 0 := by omega
  unfold rankDeltaOSSR propagateReset processAgent resetOSSR
  simp [hs_res, hs_rc, hs_dt_ne, hs_F, ht_res, ht_rc, ht_dt_ne, ht_F]

set_option maxHeartbeats 64000000 in
theorem transitionPEM_both_dormant_followers_dt_decrease
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {C : Config (AgentState n) Opinion n}
    {u v : Fin n} (huv : u ≠ v)
    (hu_res : (C u).1.role = .Resetting) (hu_rc : (C u).1.resetcount = 0)
    (hu_dt : 1 < (C u).1.delaytimer) (hu_F : (C u).1.leader = .F)
    (hv_res : (C v).1.role = .Resetting) (hv_rc : (C v).1.resetcount = 0)
    (hv_dt : 1 < (C v).1.delaytimer) (hv_F : (C v).1.leader = .F) :
    let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := C.step P u v
    (C' u).1.role = .Resetting ∧
    (C' u).1.resetcount = 0 ∧
    (C' u).1.delaytimer = (C u).1.delaytimer - 1 ∧
    (C' u).1.leader = .F ∧
    (C' v).1.role = .Resetting ∧
    (C' v).1.resetcount = 0 ∧
    (C' v).1.delaytimer = (C v).1.delaytimer - 1 ∧
    (C' v).1.leader = .F := by
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have h_rd :=
    rankDeltaOSSR_both_dormant_followers_dt_decrease
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hu_res hu_rc hu_dt hu_F hv_res hv_rc hv_dt hv_F
  have h_not_both :
      ¬((rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1)).1.role = .Settled ∧
        (rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1)).2.role = .Settled) := by
    intro hboth
    rw [h_rd.1] at hboth
    exact Role.noConfusion hboth.1
  have h_pass := transitionPEM_structural_passthrough (trank := Rmax) (Rmax := Rmax)
    (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn) (x₀ := (C u).2) (x₁ := (C v).2)
    h_not_both
  have h_fst := Config.step_fst_state P C huv
  have h_snd := Config.step_snd_state P C huv huv.symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [congrArg AgentState.role h_fst]
    exact h_pass.1 ▸ h_rd.1
  · rw [congrArg AgentState.resetcount h_fst]
    exact h_pass.2.2.2.2.1 ▸ h_rd.2.1
  · rw [congrArg AgentState.delaytimer h_fst]
    exact h_pass.2.2.2.2.2.1 ▸ h_rd.2.2.1
  · rw [congrArg AgentState.leader h_fst]
    exact h_pass.2.1 ▸ h_rd.2.2.2.1
  · rw [congrArg AgentState.role h_snd]
    exact h_pass.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.2.1
  · rw [congrArg AgentState.resetcount h_snd]
    exact h_pass.2.2.2.2.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.2.2.1
  · rw [congrArg AgentState.delaytimer h_snd]
    exact h_pass.2.2.2.2.2.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.2.2.2.1
  · rw [congrArg AgentState.leader h_snd]
    exact h_pass.2.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.2.2.2.2

theorem both_dormant_followers_dt_step_followerDormantMeasure_lt
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {C : Config (AgentState n) Opinion n}
    {u v : Fin n} (huv : u ≠ v)
    (hu_res : (C u).1.role = .Resetting) (hu_rc : (C u).1.resetcount = 0)
    (hu_dt : 1 < (C u).1.delaytimer) (hu_F : (C u).1.leader = .F)
    (hv_res : (C v).1.role = .Resetting) (hv_rc : (C v).1.resetcount = 0)
    (hv_dt : 1 < (C v).1.delaytimer) (hv_F : (C v).1.leader = .F) :
    let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    followerDormantMeasure (C.step P u v) < followerDormantMeasure C := by
  classical
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  let C' : Config (AgentState n) Opinion n := C.step P u v
  have hstep := by
    simpa [P, C'] using
      (transitionPEM_both_dormant_followers_dt_decrease
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        (C := C) (u := u) (v := v) huv
        hu_res hu_rc hu_dt hu_F hv_res hv_rc hv_dt hv_F)
  have hu_lt :
      followerDormantContribution (C' u).1 <
        followerDormantContribution (C u).1 := by
    have hdelay_eq : (C u).1.delaytimer - 1 + 1 = (C u).1.delaytimer := by
      omega
    unfold followerDormantContribution
    rw [hstep.1, hstep.2.2.1, hu_res]
    simp [hdelay_eq]
  have hv_lt :
      followerDormantContribution (C' v).1 <
        followerDormantContribution (C v).1 := by
    have hdelay_eq : (C v).1.delaytimer - 1 + 1 = (C v).1.delaytimer := by
      omega
    unfold followerDormantContribution
    rw [hstep.2.2.2.2.1, hstep.2.2.2.2.2.2.1, hv_res]
    simp [hdelay_eq]
  have hpointwise :
      ∀ x ∈ (Finset.univ : Finset (Fin n)),
        followerDormantContribution (C' x).1 ≤ followerDormantContribution (C x).1 := by
    intro x _
    by_cases hxu : x = u
    · subst x
      exact le_of_lt hu_lt
    · by_cases hxv : x = v
      · subst x
        exact le_of_lt hv_lt
      · have hx_state : C' x = C x := by
          dsimp [C', P]
          simp [Config.step, huv, hxu, hxv]
        rw [hx_state]
  have hstrict :
      ∃ x ∈ (Finset.univ : Finset (Fin n)),
        followerDormantContribution (C' x).1 < followerDormantContribution (C x).1 :=
    ⟨u, Finset.mem_univ u, hu_lt⟩
  change followerDormantMeasure C' < followerDormantMeasure C
  unfold followerDormantMeasure
  exact Finset.sum_lt_sum hpointwise hstrict

set_option maxHeartbeats 64000000 in
/-- If a low-delay dormant follower meets a high-delay dormant follower, the
low-delay follower wakes while the high-delay follower stays dormant. -/
theorem rankDeltaOSSR_dormant_follower_low_high
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {s t : AgentState n}
    (hs_res : s.role = .Resetting) (hs_rc : s.resetcount = 0)
    (hs_dt : s.delaytimer ≤ 1) (hs_F : s.leader = .F)
    (ht_res : t.role = .Resetting) (ht_rc : t.resetcount = 0)
    (ht_dt : 1 < t.delaytimer) (ht_F : t.leader = .F) :
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.role = .Unsettled ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1.leader = .F ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.role = .Resetting ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.resetcount = 0 ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.delaytimer = t.delaytimer - 1 ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.leader = .F := by
  have hs_dt_zero : s.delaytimer - 1 = 0 := by omega
  have ht_dt_ne : t.delaytimer - 1 ≠ 0 := by omega
  unfold rankDeltaOSSR propagateReset processAgent resetOSSR
  simp [hs_res, hs_rc, hs_dt_zero, hs_F, ht_res, ht_rc, ht_dt_ne, ht_F]

set_option maxHeartbeats 64000000 in
theorem transitionPEM_dormant_followers_low_high
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {C : Config (AgentState n) Opinion n}
    {u v : Fin n} (huv : u ≠ v)
    (hu_res : (C u).1.role = .Resetting) (hu_rc : (C u).1.resetcount = 0)
    (hu_dt : (C u).1.delaytimer ≤ 1) (hu_F : (C u).1.leader = .F)
    (hv_res : (C v).1.role = .Resetting) (hv_rc : (C v).1.resetcount = 0)
    (hv_dt : 1 < (C v).1.delaytimer) (hv_F : (C v).1.leader = .F) :
    let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := C.step P u v
    (C' u).1.role = .Unsettled ∧
    (C' u).1.leader = .F ∧
    (C' v).1.role = .Resetting ∧
    (C' v).1.resetcount = 0 ∧
    (C' v).1.delaytimer = (C v).1.delaytimer - 1 ∧
    (C' v).1.leader = .F := by
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have h_rd :=
    rankDeltaOSSR_dormant_follower_low_high
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hu_res hu_rc hu_dt hu_F hv_res hv_rc hv_dt hv_F
  have h_not_both :
      ¬((rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1)).1.role = .Settled ∧
        (rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1)).2.role = .Settled) := by
    intro hboth
    rw [h_rd.1] at hboth
    exact Role.noConfusion hboth.1
  have h_pass := transitionPEM_structural_passthrough (trank := Rmax) (Rmax := Rmax)
    (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn) (x₀ := (C u).2) (x₁ := (C v).2)
    h_not_both
  have h_fst := Config.step_fst_state P C huv
  have h_snd := Config.step_snd_state P C huv huv.symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [congrArg AgentState.role h_fst]
    exact h_pass.1 ▸ h_rd.1
  · rw [congrArg AgentState.leader h_fst]
    exact h_pass.2.1 ▸ h_rd.2.1
  · rw [congrArg AgentState.role h_snd]
    exact h_pass.2.2.2.2.2.2.1 ▸ h_rd.2.2.1
  · rw [congrArg AgentState.resetcount h_snd]
    exact h_pass.2.2.2.2.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.1
  · rw [congrArg AgentState.delaytimer h_snd]
    exact h_pass.2.2.2.2.2.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.2.1
  · rw [congrArg AgentState.leader h_snd]
    exact h_pass.2.2.2.2.2.2.2.1 ▸ h_rd.2.2.2.2.2

theorem dormant_followers_low_high_step_resettingCount_lt
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {C : Config (AgentState n) Opinion n}
    {u v : Fin n} (huv : u ≠ v)
    (hu_res : (C u).1.role = .Resetting) (hu_rc : (C u).1.resetcount = 0)
    (hu_dt : (C u).1.delaytimer ≤ 1) (hu_F : (C u).1.leader = .F)
    (hv_res : (C v).1.role = .Resetting) (hv_rc : (C v).1.resetcount = 0)
    (hv_dt : 1 < (C v).1.delaytimer) (hv_F : (C v).1.leader = .F) :
    let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    resettingCount (C.step P u v) < resettingCount C := by
  classical
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  let C' : Config (AgentState n) Opinion n := C.step P u v
  have hstep := by
    simpa [P, C'] using
      (transitionPEM_dormant_followers_low_high
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        (C := C) (u := u) (v := v) huv
        hu_res hu_rc hu_dt hu_F hv_res hv_rc hv_dt hv_F)
  set S := Finset.univ.filter (fun x : Fin n => (C x).1.role = .Resetting) with hS
  set S' := Finset.univ.filter (fun x : Fin n => (C' x).1.role = .Resetting) with hS'
  have hu_mem : u ∈ S := by
    rw [hS, Finset.mem_filter]
    exact ⟨Finset.mem_univ u, hu_res⟩
  have hsub : S' ⊆ S.erase u := by
    intro x hx
    have hx_reset : (C' x).1.role = .Resetting := by
      rw [hS'] at hx
      exact (Finset.mem_filter.mp hx).2
    have hx_ne_u : x ≠ u := by
      intro hxu
      subst x
      rw [hstep.1] at hx_reset
      cases hx_reset
    have hx_mem_old : x ∈ S := by
      rw [hS, Finset.mem_filter]
      by_cases hxv : x = v
      · subst x
        exact ⟨Finset.mem_univ v, hv_res⟩
      · have hx_old : C' x = C x := by
          dsimp [C', P]
          simp [Config.step, huv, hx_ne_u, hxv]
        rw [hx_old] at hx_reset
        exact ⟨Finset.mem_univ x, hx_reset⟩
    exact Finset.mem_erase.mpr ⟨hx_ne_u, hx_mem_old⟩
  have hle : S'.card ≤ (S.erase u).card := Finset.card_le_card hsub
  have herase : (S.erase u).card = S.card - 1 := Finset.card_erase_of_mem hu_mem
  have hpos : 0 < S.card := Finset.card_pos.mpr ⟨u, hu_mem⟩
  have hlt : S'.card < S.card := by
    rw [herase] at hle
    omega
  have hS_card : S.card = resettingCount C := by
    rw [hS]
    rfl
  have hS'_card : S'.card = resettingCount C' := by
    rw [hS']
    rfl
  change resettingCount C' < resettingCount C
  simpa [hS_card, hS'_card] using hlt

theorem dormant_followers_low_high_step_followerDormantMeasure_lt
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {C : Config (AgentState n) Opinion n}
    {u v : Fin n} (huv : u ≠ v)
    (hu_res : (C u).1.role = .Resetting) (hu_rc : (C u).1.resetcount = 0)
    (hu_dt : (C u).1.delaytimer ≤ 1) (hu_F : (C u).1.leader = .F)
    (hv_res : (C v).1.role = .Resetting) (hv_rc : (C v).1.resetcount = 0)
    (hv_dt : 1 < (C v).1.delaytimer) (hv_F : (C v).1.leader = .F) :
    let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    followerDormantMeasure (C.step P u v) < followerDormantMeasure C := by
  classical
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  let C' : Config (AgentState n) Opinion n := C.step P u v
  have hstep := by
    simpa [P, C'] using
      (transitionPEM_dormant_followers_low_high
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        (C := C) (u := u) (v := v) huv
        hu_res hu_rc hu_dt hu_F hv_res hv_rc hv_dt hv_F)
  have hu_lt :
      followerDormantContribution (C' u).1 <
        followerDormantContribution (C u).1 := by
    unfold followerDormantContribution
    rw [hstep.1, hu_res]
    simp
  have hv_le :
      followerDormantContribution (C' v).1 ≤
        followerDormantContribution (C v).1 := by
    have hdelay_eq : (C v).1.delaytimer - 1 + 1 = (C v).1.delaytimer := by
      omega
    unfold followerDormantContribution
    rw [hstep.2.2.1, hstep.2.2.2.2.1, hv_res]
    simp [hdelay_eq]
  have hpointwise :
      ∀ x ∈ (Finset.univ : Finset (Fin n)),
        followerDormantContribution (C' x).1 ≤ followerDormantContribution (C x).1 := by
    intro x _
    by_cases hxu : x = u
    · subst x
      exact le_of_lt hu_lt
    · by_cases hxv : x = v
      · subst x
        exact hv_le
      · have hx_state : C' x = C x := by
          dsimp [C', P]
          simp [Config.step, huv, hxu, hxv]
        rw [hx_state]
  have hstrict :
      ∃ x ∈ (Finset.univ : Finset (Fin n)),
        followerDormantContribution (C' x).1 < followerDormantContribution (C x).1 :=
    ⟨u, Finset.mem_univ u, hu_lt⟩
  change followerDormantMeasure C' < followerDormantMeasure C
  unfold followerDormantMeasure
  exact Finset.sum_lt_sum hpointwise hstrict

def FollowerClean (C : Config (AgentState n) Opinion n) : Prop :=
  ∀ w : Fin n,
    ((C w).1.role = .Resetting ∧ (C w).1.resetcount = 0 ∧ (C w).1.leader = .F) ∨
      (C w).1.role = .Unsettled

def FollowerDormantOrNonResetting (C : Config (AgentState n) Opinion n) : Prop :=
  ∀ w : Fin n,
    ((C w).1.role = .Resetting ∧ (C w).1.resetcount = 0 ∧ (C w).1.leader = .F) ∨
      (C w).1.role ≠ .Resetting

theorem follower_clean_to_no_reset
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n)
    (C : Config (AgentState n) Opinion n)
    (hClean : FollowerClean C) :
    ∃ L : List (Fin n × Fin n),
      let C' := runPairs (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L
      ∀ w : Fin n, (C' w).1.role ≠ .Resetting := by
  classical
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have hne_of_fin (a : Fin n) : ∃ b : Fin n, b ≠ a := by
    have hcard : 1 < Fintype.card (Fin n) := by
      rw [Fintype.card_fin]
      omega
    exact Fintype.exists_ne_of_one_lt_card hcard a
  suffices rec :
      ∀ m (C₀ : Config (AgentState n) Opinion n),
        followerDormantMeasure C₀ = m →
        FollowerClean C₀ →
        ∃ L : List (Fin n × Fin n),
          let C' := runPairs P C₀ L
          ∀ w : Fin n, (C' w).1.role ≠ .Resetting by
    exact rec (followerDormantMeasure C) C rfl hClean
  intro m
  induction m using Nat.strongRecOn with
  | ind m IH =>
      intro C₀ hm hClean₀
      by_cases hNoReset : ∀ w : Fin n, (C₀ w).1.role ≠ .Resetting
      · refine ⟨[], ?_⟩
        simpa using hNoReset
      · push_neg at hNoReset
        obtain ⟨u, hu_res⟩ := hNoReset
        have hu_fields : (C₀ u).1.resetcount = 0 ∧ (C₀ u).1.leader = .F := by
          rcases hClean₀ u with hreset | hun
          · exact ⟨hreset.2.1, hreset.2.2⟩
          · rw [hun] at hu_res
            cases hu_res
        by_cases hAllReset : ∀ w : Fin n, (C₀ w).1.role = .Resetting
        · obtain ⟨v, hv_ne_u⟩ := hne_of_fin u
          have huv : u ≠ v := hv_ne_u.symm
          have hv_res : (C₀ v).1.role = .Resetting := hAllReset v
          have hv_fields : (C₀ v).1.resetcount = 0 ∧ (C₀ v).1.leader = .F := by
            rcases hClean₀ v with hreset | hun
            · exact ⟨hreset.2.1, hreset.2.2⟩
            · rw [hun] at hv_res
              cases hv_res
          by_cases hu_low : (C₀ u).1.delaytimer ≤ 1
          · by_cases hv_low : (C₀ v).1.delaytimer ≤ 1
            · let C₁ : Config (AgentState n) Opinion n := C₀.step P u v
              have hstep := by
                simpa [P, C₁] using
                  (transitionPEM_both_dormant_followers_low_dt_unsettle
                    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
                    (C := C₀) (u := u) (v := v) huv
                    hu_res hu_fields.1 hu_low hu_fields.2
                    hv_res hv_fields.1 hv_low hv_fields.2)
              have hmeasure :
                  followerDormantMeasure C₁ < followerDormantMeasure C₀ := by
                simpa [P, C₁] using
                  (both_dormant_followers_low_dt_step_followerDormantMeasure_lt
                    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
                    (C := C₀) (u := u) (v := v) huv
                    hu_res hu_fields.1 hu_low hu_fields.2
                    hv_res hv_fields.1 hv_low hv_fields.2)
              have hClean₁ : FollowerClean C₁ := by
                intro x
                by_cases hxu : x = u
                · subst x
                  exact Or.inr hstep.1
                · by_cases hxv : x = v
                  · subst x
                    exact Or.inr hstep.2
                  · have hx_state : C₁ x = C₀ x := by
                      dsimp [C₁, P]
                      simp [Config.step, huv, hxu, hxv]
                    rw [hx_state]
                    exact hClean₀ x
              obtain ⟨Ltail, htail⟩ :=
                IH (followerDormantMeasure C₁) (by omega) C₁ rfl hClean₁
              refine ⟨[(u, v)] ++ Ltail, ?_⟩
              rw [runPairs_append]
              change ∀ w : Fin n, (runPairs P C₁ Ltail w).1.role ≠ .Resetting
              exact htail
            · have hv_high : 1 < (C₀ v).1.delaytimer := by omega
              let C₁ : Config (AgentState n) Opinion n := C₀.step P u v
              have hstep := by
                simpa [P, C₁] using
                  (transitionPEM_dormant_followers_low_high
                    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
                    (C := C₀) (u := u) (v := v) huv
                    hu_res hu_fields.1 hu_low hu_fields.2
                    hv_res hv_fields.1 hv_high hv_fields.2)
              have hmeasure :
                  followerDormantMeasure C₁ < followerDormantMeasure C₀ := by
                simpa [P, C₁] using
                  (dormant_followers_low_high_step_followerDormantMeasure_lt
                    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
                    (C := C₀) (u := u) (v := v) huv
                    hu_res hu_fields.1 hu_low hu_fields.2
                    hv_res hv_fields.1 hv_high hv_fields.2)
              have hClean₁ : FollowerClean C₁ := by
                intro x
                by_cases hxu : x = u
                · subst x
                  exact Or.inr hstep.1
                · by_cases hxv : x = v
                  · subst x
                    exact Or.inl ⟨hstep.2.2.1, hstep.2.2.2.1, hstep.2.2.2.2.2⟩
                  · have hx_state : C₁ x = C₀ x := by
                      dsimp [C₁, P]
                      simp [Config.step, huv, hxu, hxv]
                    rw [hx_state]
                    exact hClean₀ x
              obtain ⟨Ltail, htail⟩ :=
                IH (followerDormantMeasure C₁) (by omega) C₁ rfl hClean₁
              refine ⟨[(u, v)] ++ Ltail, ?_⟩
              rw [runPairs_append]
              change ∀ w : Fin n, (runPairs P C₁ Ltail w).1.role ≠ .Resetting
              exact htail
          · have hu_high : 1 < (C₀ u).1.delaytimer := by omega
            by_cases hv_low : (C₀ v).1.delaytimer ≤ 1
            · let C₁ : Config (AgentState n) Opinion n := C₀.step P v u
              have hvu : v ≠ u := hv_ne_u
              have hstep := by
                simpa [P, C₁] using
                  (transitionPEM_dormant_followers_low_high
                    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
                    (C := C₀) (u := v) (v := u) hvu
                    hv_res hv_fields.1 hv_low hv_fields.2
                    hu_res hu_fields.1 hu_high hu_fields.2)
              have hmeasure :
                  followerDormantMeasure C₁ < followerDormantMeasure C₀ := by
                simpa [P, C₁] using
                  (dormant_followers_low_high_step_followerDormantMeasure_lt
                    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
                    (C := C₀) (u := v) (v := u) hvu
                    hv_res hv_fields.1 hv_low hv_fields.2
                    hu_res hu_fields.1 hu_high hu_fields.2)
              have hClean₁ : FollowerClean C₁ := by
                intro x
                by_cases hxv : x = v
                · subst x
                  exact Or.inr hstep.1
                · by_cases hxu : x = u
                  · subst x
                    exact Or.inl ⟨hstep.2.2.1, hstep.2.2.2.1, hstep.2.2.2.2.2⟩
                  · have hx_state : C₁ x = C₀ x := by
                      dsimp [C₁, P]
                      simp [Config.step, hvu, hxv, hxu]
                    rw [hx_state]
                    exact hClean₀ x
              obtain ⟨Ltail, htail⟩ :=
                IH (followerDormantMeasure C₁) (by omega) C₁ rfl hClean₁
              refine ⟨[(v, u)] ++ Ltail, ?_⟩
              rw [runPairs_append]
              change ∀ w : Fin n, (runPairs P C₁ Ltail w).1.role ≠ .Resetting
              exact htail
            · have hv_high : 1 < (C₀ v).1.delaytimer := by omega
              let C₁ : Config (AgentState n) Opinion n := C₀.step P u v
              have hstep := by
                simpa [P, C₁] using
                  (transitionPEM_both_dormant_followers_dt_decrease
                    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
                    (C := C₀) (u := u) (v := v) huv
                    hu_res hu_fields.1 hu_high hu_fields.2
                    hv_res hv_fields.1 hv_high hv_fields.2)
              have hmeasure :
                  followerDormantMeasure C₁ < followerDormantMeasure C₀ := by
                simpa [P, C₁] using
                  (both_dormant_followers_dt_step_followerDormantMeasure_lt
                    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
                    (C := C₀) (u := u) (v := v) huv
                    hu_res hu_fields.1 hu_high hu_fields.2
                    hv_res hv_fields.1 hv_high hv_fields.2)
              have hClean₁ : FollowerClean C₁ := by
                intro x
                by_cases hxu : x = u
                · subst x
                  exact Or.inl ⟨hstep.1, hstep.2.1, hstep.2.2.2.1⟩
                · by_cases hxv : x = v
                  · subst x
                    exact Or.inl ⟨hstep.2.2.2.2.1, hstep.2.2.2.2.2.1,
                      hstep.2.2.2.2.2.2.2⟩
                  · have hx_state : C₁ x = C₀ x := by
                      dsimp [C₁, P]
                      simp [Config.step, huv, hxu, hxv]
                    rw [hx_state]
                    exact hClean₀ x
              obtain ⟨Ltail, htail⟩ :=
                IH (followerDormantMeasure C₁) (by omega) C₁ rfl hClean₁
              refine ⟨[(u, v)] ++ Ltail, ?_⟩
              rw [runPairs_append]
              change ∀ w : Fin n, (runPairs P C₁ Ltail w).1.role ≠ .Resetting
              exact htail
        · push_neg at hAllReset
          obtain ⟨w, hw_not_reset⟩ := hAllReset
          have hw_un : (C₀ w).1.role = .Unsettled := by
            rcases hClean₀ w with hreset | hun
            · exact False.elim (hw_not_reset hreset.1)
            · exact hun
          have huw : u ≠ w := by
            intro huw
            subst w
            exact hw_not_reset hu_res
          let C₁ : Config (AgentState n) Opinion n := C₀.step P u w
          have hstep := by
            simpa [P, C₁] using
              (transitionPEM_dormant_follower_with_unsettled_partner_wakes
                (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
                (C := C₀) (u := u) (w := w) huw
                hu_res hu_fields.1 hu_fields.2 hw_un)
          have hmeasure :
              followerDormantMeasure C₁ < followerDormantMeasure C₀ := by
            simpa [P, C₁] using
              (dormant_follower_unsettled_step_followerDormantMeasure_lt
                (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
                (C := C₀) (u := u) (w := w) huw
                hu_res hu_fields.1 hu_fields.2 hw_un)
          have hClean₁ : FollowerClean C₁ := by
            intro x
            by_cases hxu : x = u
            · subst x
              exact Or.inr hstep.1
            · by_cases hxw : x = w
              · subst x
                exact Or.inr hstep.2.2
              · have hx_state : C₁ x = C₀ x := by
                  dsimp [C₁, P]
                  simp [Config.step, huw, hxu, hxw]
                rw [hx_state]
                exact hClean₀ x
          obtain ⟨Ltail, htail⟩ :=
            IH (followerDormantMeasure C₁) (by omega) C₁ rfl hClean₁
          refine ⟨[(u, w)] ++ Ltail, ?_⟩
          rw [runPairs_append]
          change ∀ w : Fin n, (runPairs P C₁ Ltail w).1.role ≠ .Resetting
          exact htail

theorem follower_dormant_or_nonresetting_to_no_reset
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n)
    (C : Config (AgentState n) Opinion n)
    (hClean : FollowerDormantOrNonResetting C) :
    ∃ L : List (Fin n × Fin n),
      let C' := runPairs (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L
      ∀ w : Fin n, (C' w).1.role ≠ .Resetting := by
  classical
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  suffices rec :
      ∀ m (C₀ : Config (AgentState n) Opinion n),
        followerDormantMeasure C₀ = m →
        FollowerDormantOrNonResetting C₀ →
        ∃ L : List (Fin n × Fin n),
          let C' := runPairs P C₀ L
          ∀ w : Fin n, (C' w).1.role ≠ .Resetting by
    exact rec (followerDormantMeasure C) C rfl hClean
  intro m
  induction m using Nat.strongRecOn with
  | ind m IH =>
      intro C₀ hm hClean₀
      by_cases hNoReset : ∀ w : Fin n, (C₀ w).1.role ≠ .Resetting
      · refine ⟨[], ?_⟩
        simpa using hNoReset
      · push_neg at hNoReset
        obtain ⟨u, hu_res⟩ := hNoReset
        have hu_fields : (C₀ u).1.resetcount = 0 ∧ (C₀ u).1.leader = .F := by
          rcases hClean₀ u with hreset | hnot
          · exact ⟨hreset.2.1, hreset.2.2⟩
          · exact False.elim (hnot hu_res)
        by_cases hAllReset : ∀ w : Fin n, (C₀ w).1.role = .Resetting
        · have hFollower : FollowerClean C₀ := by
            intro x
            rcases hClean₀ x with hreset | hnot
            · exact Or.inl hreset
            · exact False.elim (hnot (hAllReset x))
          exact
            follower_clean_to_no_reset
              (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
              hn4 C₀ hFollower
        · push_neg at hAllReset
          obtain ⟨w, hw_not_reset⟩ := hAllReset
          have huw : u ≠ w := by
            intro huw
            subst w
            exact hw_not_reset hu_res
          let C₁ : Config (AgentState n) Opinion n := C₀.step P u w
          have hstep := by
            simpa [P, C₁] using
              (transitionPEM_dormant_follower_with_nonresetting_partner_wakes
                (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
                (C := C₀) (u := u) (w := w) huw hu_res hu_fields.1 hu_fields.2
                hw_not_reset)
          have hmeasure :
              followerDormantMeasure C₁ < followerDormantMeasure C₀ := by
            simpa [P, C₁] using
              (dormant_follower_nonresetting_step_followerDormantMeasure_lt
                (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
                (C := C₀) (u := u) (w := w) huw hu_res hu_fields.1 hu_fields.2
                hw_not_reset)
          have hClean₁ : FollowerDormantOrNonResetting C₁ := by
            intro x
            by_cases hxu : x = u
            · subst x
              exact Or.inr (by rw [hstep.1]; decide)
            · by_cases hxw : x = w
              · subst x
                exact Or.inr (by
                  rw [hstep.2.2]
                  exact hw_not_reset)
              · have hx_state : C₁ x = C₀ x := by
                  dsimp [C₁, P]
                  simp [Config.step, huw, hxu, hxw]
                rw [hx_state]
                exact hClean₀ x
          obtain ⟨Ltail, htail⟩ :=
            IH (followerDormantMeasure C₁) (by omega) C₁ rfl hClean₁
          refine ⟨[(u, w)] ++ Ltail, ?_⟩
          rw [runPairs_append]
          change ∀ w : Fin n, (runPairs P C₁ Ltail w).1.role ≠ .Resetting
          exact htail

  /-- RankDeltaOSSR: Settled root meets dormant follower → root unchanged, follower Unsettled. -/
  theorem rankDeltaOSSR_settled_meets_dormant
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {s t : AgentState n}
    (hs_settled : s.role = .Settled)
    (ht_res : t.role = .Resetting) (ht_rc : t.resetcount = 0)
    (ht_F : t.leader = .F) :
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1 = s ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.role = .Unsettled := by
  unfold rankDeltaOSSR propagateReset processAgent resetOSSR
  simp [hs_settled, ht_res, ht_rc, ht_F]

theorem rankDeltaOSSR_settled_meets_dormant_L_trace
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {s t : AgentState n}
    (hs_settled : s.role = .Settled)
    (ht_res : t.role = .Resetting) (ht_rc : t.resetcount = 0)
    (ht_L : t.leader = .L) :
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).1 = s ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.role = .Settled ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.rank = ⟨0, hn⟩ ∧
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.children = 0 := by
  unfold rankDeltaOSSR propagateReset processAgent resetOSSR
  simp [hs_settled, ht_res, ht_rc, ht_L]

theorem transitionPEM_phase4_rank0_pair_id
    {Rmax : ℕ} (hn4 : 4 ≤ n)
    {a₀ a₁ : AgentState n} {x₀ x₁ : Opinion}
    (h₀ : a₀.role = .Settled) (h₁ : a₁.role = .Settled)
    (hr₀ : a₀.rank.val = 0) (hr₁ : a₁.rank.val = 0) :
    transitionPEM_phase4 n Rmax (a₀, a₁) x₀ x₁ = (a₀, a₁) := by
  have hno_swap : ¬ (a₀.rank < a₁.rank ∧ x₀ = .B ∧ x₁ = .A) := by
    intro h
    have hlt : a₀.rank.val < a₁.rank.val := h.1
    omega
  have hnot_half₀ : ¬ (a₀.rank.val + 1 = n / 2) := by omega
  have hnot_half₁ : ¬ (a₁.rank.val + 1 = n / 2) := by omega
  have hnot_half_succ₀ : ¬ (a₀.rank.val + 1 = n / 2 + 1) := by omega
  have hnot_half_succ₁ : ¬ (a₁.rank.val + 1 = n / 2 + 1) := by omega
  have hnot_ceil₀ : ¬ (a₀.rank.val + 1 = ceilHalf n) := by
    unfold ceilHalf
    omega
  have hnot_ceil₁ : ¬ (a₁.rank.val + 1 = ceilHalf n) := by
    unfold ceilHalf
    omega
  unfold transitionPEM_phase4 phase4_swap phase4_decide phase4_propagate
  simp [h₀, h₁, hno_swap, hnot_half₀, hnot_half₁,
    hnot_half_succ₀, hnot_half_succ₁, hnot_ceil₀, hnot_ceil₁]

set_option maxHeartbeats 64000000 in
theorem transitionPEM_dormant_leader_low_dt_L_partner_wakes
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n)
    {C : Config (AgentState n) Opinion n}
    {ℓ w : Fin n} (hℓw : ℓ ≠ w)
    (hℓ_res : (C ℓ).1.role = .Resetting) (hℓ_rc : (C ℓ).1.resetcount = 0)
    (hℓ_dt : (C ℓ).1.delaytimer ≤ 1) (hℓ_L : (C ℓ).1.leader = .L)
    (hw_res : (C w).1.role = .Resetting) (hw_rc : (C w).1.resetcount = 0)
    (hw_L : (C w).1.leader = .L) :
    let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := C.step P ℓ w
    (C' ℓ).1.role = .Settled ∧
    (C' ℓ).1.rank.val = 0 ∧
    (C' ℓ).1.children = 0 ∧
    (C' ℓ).1.leader = .L ∧
    ((C' w).1.role = .Settled ∨
      ((C' w).1.role = .Resetting ∧ (C' w).1.resetcount = 0 ∧
        (C' w).1.leader = .L)) := by
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  let p :=
    transitionPEM_prePhase4 n Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
      (C ℓ).1 (C w).1 (C ℓ).2 (C w).2
  have h_rd :=
    rankDeltaOSSR_dormant_leader_low_dt_L_partner_wakes
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hℓ_res hℓ_rc hℓ_dt hℓ_L hw_res hw_rc hw_L
  have hpre :=
    transitionPEM_prePhase4_structural
      (trank := Rmax)
      (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
      (s₀ := (C ℓ).1) (s₁ := (C w).1)
      (x₀ := (C ℓ).2) (x₁ := (C w).2)
  have hp₁_role : p.1.role = .Settled := by
    dsimp [p]
    rw [hpre.1]
    exact h_rd.1
  have hp₁_rank0 : p.1.rank.val = 0 := by
    dsimp [p]
    rw [hpre.2.2.1, h_rd.2.1]
  have hp₁_children : p.1.children = 0 := by
    dsimp [p]
    rw [hpre.2.2.2.1]
    exact h_rd.2.2.1
  have hp₁_leader : p.1.leader = .L := by
    dsimp [p]
    rw [hpre.2.1]
    exact h_rd.2.2.2.1
  have h_fst := Config.step_fst_state P C hℓw
  have h_snd := Config.step_snd_state P C hℓw hℓw.symm
  rcases h_rd.2.2.2.2 with hsettled | hreset
  · have hp₂_role : p.2.role = .Settled := by
      dsimp [p]
      rw [hpre.2.2.2.2.2.2.1]
      exact hsettled.1
    have hp₂_rank0 : p.2.rank.val = 0 := by
      dsimp [p]
      rw [hpre.2.2.2.2.2.2.2.2.1, hsettled.2.1]
    have hphase :
        transitionPEM_phase4 n Rmax p (C ℓ).2 (C w).2 = p := by
      exact
        transitionPEM_phase4_rank0_pair_id
          (n := n) (Rmax := Rmax) hn4
          (a₀ := p.1) (a₁ := p.2)
          (x₀ := (C ℓ).2) (x₁ := (C w).2)
          hp₁_role hp₂_role hp₁_rank0 hp₂_rank0
    refine ⟨?_, ?_, ?_, ?_, Or.inl ?_⟩
    · rw [congrArg AgentState.role h_fst]
      change (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C ℓ, C w)).1.role = .Settled
      rw [transitionPEM_eq, show
        transitionPEM_prePhase4 n Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
          (C ℓ).1 (C w).1 (C ℓ).2 (C w).2 = p from rfl, hphase]
      exact hp₁_role
    · rw [congrArg AgentState.rank h_fst]
      change (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C ℓ, C w)).1.rank.val = 0
      rw [transitionPEM_eq, show
        transitionPEM_prePhase4 n Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
          (C ℓ).1 (C w).1 (C ℓ).2 (C w).2 = p from rfl, hphase]
      exact hp₁_rank0
    · rw [congrArg AgentState.children h_fst]
      change (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C ℓ, C w)).1.children = 0
      rw [transitionPEM_eq, show
        transitionPEM_prePhase4 n Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
          (C ℓ).1 (C w).1 (C ℓ).2 (C w).2 = p from rfl, hphase]
      exact hp₁_children
    · rw [congrArg AgentState.leader h_fst]
      change (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C ℓ, C w)).1.leader = .L
      rw [transitionPEM_eq, show
        transitionPEM_prePhase4 n Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
          (C ℓ).1 (C w).1 (C ℓ).2 (C w).2 = p from rfl, hphase]
      exact hp₁_leader
    · rw [congrArg AgentState.role h_snd]
      change (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C ℓ, C w)).2.role = .Settled
      rw [transitionPEM_eq, show
        transitionPEM_prePhase4 n Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
          (C ℓ).1 (C w).1 (C ℓ).2 (C w).2 = p from rfl, hphase]
      exact hp₂_role
  · have h_not_both :
        ¬((rankDeltaOSSR Rmax Emax Dmax hn ((C ℓ).1, (C w).1)).1.role = .Settled ∧
          (rankDeltaOSSR Rmax Emax Dmax hn ((C ℓ).1, (C w).1)).2.role = .Settled) := by
      intro hboth
      rw [hreset.1] at hboth
      exact Role.noConfusion hboth.2
    have h_pass := transitionPEM_structural_passthrough (trank := Rmax) (Rmax := Rmax)
      (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn) (x₀ := (C ℓ).2) (x₁ := (C w).2) h_not_both
    refine ⟨?_, ?_, ?_, ?_, Or.inr ⟨?_, ?_, ?_⟩⟩
    · rw [congrArg AgentState.role h_fst]
      exact h_pass.1 ▸ h_rd.1
    · rw [congrArg AgentState.rank h_fst]
      exact congrArg Fin.val (h_pass.2.2.1 ▸ h_rd.2.1)
    · rw [congrArg AgentState.children h_fst]
      exact h_pass.2.2.2.1 ▸ h_rd.2.2.1
    · rw [congrArg AgentState.leader h_fst]
      exact h_pass.2.1 ▸ h_rd.2.2.2.1
    · rw [congrArg AgentState.role h_snd]
      exact h_pass.2.2.2.2.2.2.1 ▸ hreset.1
    · rw [congrArg AgentState.resetcount h_snd]
      exact h_pass.2.2.2.2.2.2.2.2.2.2.1 ▸ hreset.2.1
    · rw [congrArg AgentState.leader h_snd]
      exact h_pass.2.2.2.2.2.2.2.1 ▸ hreset.2.2

set_option maxHeartbeats 32000000 in
/-- TransitionPEM on two dormant agents (leader + follower): leader → Settled rank 0,
follower → Unsettled. Requires n ≥ 4 (so rank 0 is not the median). -/
theorem transitionPEM_both_dormant_role
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n)
    {C : Config (AgentState n) Opinion n}
    {ℓ w : Fin n} (hℓw : ℓ ≠ w)
    (hℓ_res : (C ℓ).1.role = .Resetting)
    (hℓ_rc : (C ℓ).1.resetcount = 0) (hℓ_dt : (C ℓ).1.delaytimer = 0)
    (hℓ_L : (C ℓ).1.leader = .L)
    (hw_res : (C w).1.role = .Resetting)
    (hw_rc : (C w).1.resetcount = 0) (hw_dt : (C w).1.delaytimer = 0)
    (hw_F : (C w).1.leader = .F) :
    let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    (C.step P ℓ w ℓ).1.role = .Settled ∧
    (C.step P ℓ w ℓ).1.rank.val = 0 ∧
    (C.step P ℓ w ℓ).1.children = 0 ∧
    (C.step P ℓ w ℓ).1.leader = .L ∧
    (C.step P ℓ w w).1.role = .Unsettled ∧
    (C.step P ℓ w w).1.leader = .F := by
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have h_rd := rankDeltaOSSR_both_dormant (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
    (hn := hn) hℓ_res hℓ_rc hℓ_dt hw_res hw_rc hw_dt hℓ_L hw_F
  have h_rd_leaders :
      (rankDeltaOSSR Rmax Emax Dmax hn ((C ℓ).1, (C w).1)).1.leader = .L ∧
      (rankDeltaOSSR Rmax Emax Dmax hn ((C ℓ).1, (C w).1)).2.leader = .F := by
    unfold rankDeltaOSSR propagateReset processAgent resetOSSR
    simp [hℓ_res, hℓ_rc, hℓ_dt, hℓ_L, hw_res, hw_rc, hw_dt, hw_F]
  have h_not_both : ¬((rankDeltaOSSR Rmax Emax Dmax hn ((C ℓ).1, (C w).1)).1.role = .Settled ∧
                      (rankDeltaOSSR Rmax Emax Dmax hn ((C ℓ).1, (C w).1)).2.role = .Settled) := by
    intro ⟨_, h2⟩; rw [h_rd.2.2.2] at h2; exact Role.noConfusion h2
  have h_pass := transitionPEM_structural_passthrough (trank := Rmax) (Rmax := Rmax)
    (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn) (x₀ := (C ℓ).2) (x₁ := (C w).2) h_not_both
  have h_fst := Config.step_fst_state P C hℓw
  have h_snd := Config.step_snd_state P C hℓw hℓw.symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [congrArg AgentState.role h_fst]; exact h_pass.1 ▸ h_rd.1
  · rw [congrArg AgentState.rank h_fst]
    exact congrArg Fin.val (h_pass.2.2.1 ▸ h_rd.2.1)
  · rw [congrArg AgentState.children h_fst]; exact h_pass.2.2.2.1 ▸ h_rd.2.2.1
  · rw [congrArg AgentState.leader h_fst]; exact h_pass.2.1 ▸ h_rd_leaders.1
  · rw [congrArg AgentState.role h_snd]; exact h_pass.2.2.2.2.2.2.1 ▸ h_rd.2.2.2
  · rw [congrArg AgentState.leader h_snd]; exact h_pass.2.2.2.2.2.2.2.1 ▸ h_rd_leaders.2

set_option maxHeartbeats 64000000 in
/-- TransitionPEM on Settled root + dormant follower: root state unchanged, follower Unsettled.
Requires n ≥ 4 (so rank 0 is not the median). -/
theorem transitionPEM_settled_meets_dormant_role
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n)
    {C : Config (AgentState n) Opinion n}
    {ℓ w : Fin n} (hℓw : ℓ ≠ w)
    (hℓ_settled : (C ℓ).1.role = .Settled)
    (hℓ_rank0 : (C ℓ).1.rank.val = 0)
    (hw_res : (C w).1.role = .Resetting)
    (hw_rc : (C w).1.resetcount = 0)
    (hw_F : (C w).1.leader = .F) :
    let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    (C.step P ℓ w ℓ).1.role = .Settled ∧
    (C.step P ℓ w ℓ).1.rank.val = 0 ∧
    (C.step P ℓ w w).1.role = .Unsettled := by
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have h_rd := rankDeltaOSSR_settled_meets_dormant (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
    (hn := hn) hℓ_settled hw_res hw_rc hw_F
  have h_not_both : ¬((rankDeltaOSSR Rmax Emax Dmax hn ((C ℓ).1, (C w).1)).1.role = .Settled ∧
                      (rankDeltaOSSR Rmax Emax Dmax hn ((C ℓ).1, (C w).1)).2.role = .Settled) := by
    intro ⟨_, h2⟩; rw [h_rd.2] at h2; exact Role.noConfusion h2
  have h_pass := transitionPEM_structural_passthrough (trank := Rmax) (Rmax := Rmax)
    (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn) (x₀ := (C ℓ).2) (x₁ := (C w).2) h_not_both
  have h_fst := Config.step_fst_state P C hℓw
  have h_snd := Config.step_snd_state P C hℓw hℓw.symm
  refine ⟨?_, ?_, ?_⟩
  · rw [congrArg AgentState.role h_fst]
    change (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C ℓ, C w)).1.role = .Settled
    rw [h_pass.1, congrArg AgentState.role h_rd.1]
    exact hℓ_settled
  · rw [congrArg AgentState.rank h_fst]
    change (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C ℓ, C w)).1.rank.val = 0
    rw [h_pass.2.2.1, congrArg AgentState.rank h_rd.1]
    exact hℓ_rank0
  · rw [congrArg AgentState.role h_snd]; exact h_pass.2.2.2.2.2.2.1 ▸ h_rd.2

theorem rankDeltaOSSR_settled_meets_dormant_leader
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {s t : AgentState n}
    (hs : s.role = .Settled)
    (ht : t.role = .Resetting) (ht_rc : t.resetcount = 0)
    (ht_F : t.leader = .F) :
    (rankDeltaOSSR Rmax Emax Dmax hn (s, t)).2.leader = .F := by
  unfold rankDeltaOSSR propagateReset processAgent resetOSSR
  simp [hs, ht, ht_rc, ht_F]

theorem transitionPEM_settled_meets_dormant_trace
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n)
    {C : Config (AgentState n) Opinion n}
    {ℓ w : Fin n} (hℓw : ℓ ≠ w)
    (hℓ_settled : (C ℓ).1.role = .Settled)
    (hℓ_rank0 : (C ℓ).1.rank.val = 0)
    (hℓ_children : (C ℓ).1.children = 0)
    (hℓ_L : (C ℓ).1.leader = .L)
    (hw_res : (C w).1.role = .Resetting)
    (hw_rc : (C w).1.resetcount = 0)
    (hw_F : (C w).1.leader = .F) :
    let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := C.step P ℓ w
    (C' ℓ).1.role = .Settled ∧
    (C' ℓ).1.rank.val = 0 ∧
    (C' ℓ).1.children = 0 ∧
    (C' ℓ).1.leader = .L ∧
    (C' w).1.role = .Unsettled ∧
    (C' w).1.leader = .F := by
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have h_rd := rankDeltaOSSR_settled_meets_dormant (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
    (hn := hn) hℓ_settled hw_res hw_rc hw_F
  have h_rd_leader := rankDeltaOSSR_settled_meets_dormant_leader
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hℓ_settled hw_res hw_rc hw_F
  have h_not_both : ¬((rankDeltaOSSR Rmax Emax Dmax hn ((C ℓ).1, (C w).1)).1.role = .Settled ∧
                      (rankDeltaOSSR Rmax Emax Dmax hn ((C ℓ).1, (C w).1)).2.role = .Settled) := by
    intro ⟨_, h2⟩; rw [h_rd.2] at h2; exact Role.noConfusion h2
  have h_pass := transitionPEM_structural_passthrough (trank := Rmax) (Rmax := Rmax)
    (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn) (x₀ := (C ℓ).2) (x₁ := (C w).2) h_not_both
  have h_fst := Config.step_fst_state P C hℓw
  have h_snd := Config.step_snd_state P C hℓw hℓw.symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [congrArg AgentState.role h_fst]
    change (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C ℓ, C w)).1.role = .Settled
    rw [h_pass.1, congrArg AgentState.role h_rd.1]
    exact hℓ_settled
  · rw [congrArg AgentState.rank h_fst]
    change (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C ℓ, C w)).1.rank.val = 0
    rw [h_pass.2.2.1, congrArg AgentState.rank h_rd.1]
    exact hℓ_rank0
  · rw [congrArg AgentState.children h_fst]
    change (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C ℓ, C w)).1.children = 0
    rw [h_pass.2.2.2.1, congrArg AgentState.children h_rd.1]
    exact hℓ_children
  · rw [congrArg AgentState.leader h_fst]
    change (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C ℓ, C w)).1.leader = .L
    rw [h_pass.2.1, congrArg AgentState.leader h_rd.1]
    exact hℓ_L
  · rw [congrArg AgentState.role h_snd]
    exact h_pass.2.2.2.2.2.2.1 ▸ h_rd.2
  · rw [congrArg AgentState.leader h_snd]
    exact h_pass.2.2.2.2.2.2.2.1 ▸ h_rd_leader

theorem transitionPEM_settled_meets_dormant_L_trace
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n)
    {C : Config (AgentState n) Opinion n}
    {ℓ w : Fin n} (hℓw : ℓ ≠ w)
    (hℓ_settled : (C ℓ).1.role = .Settled)
    (hℓ_rank0 : (C ℓ).1.rank.val = 0)
    (hℓ_children : (C ℓ).1.children = 0)
    (hℓ_L : (C ℓ).1.leader = .L)
    (hw_res : (C w).1.role = .Resetting)
    (hw_rc : (C w).1.resetcount = 0)
    (hw_L : (C w).1.leader = .L) :
    let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := C.step P ℓ w
    (C' ℓ).1.role = .Settled ∧
    (C' ℓ).1.rank.val = 0 ∧
    (C' ℓ).1.children = 0 ∧
    (C' ℓ).1.leader = .L ∧
    (C' w).1.role = .Settled ∧
    (C' w).1.rank.val = 0 ∧
    (C' w).1.children = 0 := by
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  let p :=
    transitionPEM_prePhase4 n Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
      (C ℓ).1 (C w).1 (C ℓ).2 (C w).2
  have h_rd :=
    rankDeltaOSSR_settled_meets_dormant_L_trace
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hℓ_settled hw_res hw_rc hw_L
  have hpre :=
    transitionPEM_prePhase4_structural
      (trank := Rmax)
      (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
      (s₀ := (C ℓ).1) (s₁ := (C w).1)
      (x₀ := (C ℓ).2) (x₁ := (C w).2)
  have hp₁_role : p.1.role = .Settled := by
    dsimp [p]
    rw [hpre.1, congrArg AgentState.role h_rd.1]
    exact hℓ_settled
  have hp₁_rank0 : p.1.rank.val = 0 := by
    dsimp [p]
    rw [hpre.2.2.1, congrArg AgentState.rank h_rd.1]
    exact hℓ_rank0
  have hp₁_children : p.1.children = 0 := by
    dsimp [p]
    rw [hpre.2.2.2.1, congrArg AgentState.children h_rd.1]
    exact hℓ_children
  have hp₁_leader : p.1.leader = .L := by
    dsimp [p]
    rw [hpre.2.1, congrArg AgentState.leader h_rd.1]
    exact hℓ_L
  have hp₂_role : p.2.role = .Settled := by
    dsimp [p]
    rw [hpre.2.2.2.2.2.2.1]
    exact h_rd.2.1
  have hp₂_rank0 : p.2.rank.val = 0 := by
    dsimp [p]
    rw [hpre.2.2.2.2.2.2.2.2.1, h_rd.2.2.1]
  have hp₂_children : p.2.children = 0 := by
    dsimp [p]
    rw [hpre.2.2.2.2.2.2.2.2.2.1]
    exact h_rd.2.2.2
  have hphase :
      transitionPEM_phase4 n Rmax p (C ℓ).2 (C w).2 = p := by
    exact
      transitionPEM_phase4_rank0_pair_id
        (n := n) (Rmax := Rmax) hn4
        (a₀ := p.1) (a₁ := p.2)
        (x₀ := (C ℓ).2) (x₁ := (C w).2)
        hp₁_role hp₂_role hp₁_rank0 hp₂_rank0
  have h_fst := Config.step_fst_state P C hℓw
  have h_snd := Config.step_snd_state P C hℓw hℓw.symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [congrArg AgentState.role h_fst]
    change (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C ℓ, C w)).1.role = .Settled
    rw [transitionPEM_eq, show
      transitionPEM_prePhase4 n Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
        (C ℓ).1 (C w).1 (C ℓ).2 (C w).2 = p from rfl, hphase]
    exact hp₁_role
  · rw [congrArg AgentState.rank h_fst]
    change (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C ℓ, C w)).1.rank.val = 0
    rw [transitionPEM_eq, show
      transitionPEM_prePhase4 n Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
        (C ℓ).1 (C w).1 (C ℓ).2 (C w).2 = p from rfl, hphase]
    exact hp₁_rank0
  · rw [congrArg AgentState.children h_fst]
    change (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C ℓ, C w)).1.children = 0
    rw [transitionPEM_eq, show
      transitionPEM_prePhase4 n Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
        (C ℓ).1 (C w).1 (C ℓ).2 (C w).2 = p from rfl, hphase]
    exact hp₁_children
  · rw [congrArg AgentState.leader h_fst]
    change (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C ℓ, C w)).1.leader = .L
    rw [transitionPEM_eq, show
      transitionPEM_prePhase4 n Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
        (C ℓ).1 (C w).1 (C ℓ).2 (C w).2 = p from rfl, hphase]
    exact hp₁_leader
  · rw [congrArg AgentState.role h_snd]
    change (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C ℓ, C w)).2.role = .Settled
    rw [transitionPEM_eq, show
      transitionPEM_prePhase4 n Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
        (C ℓ).1 (C w).1 (C ℓ).2 (C w).2 = p from rfl, hphase]
    exact hp₂_role
  · rw [congrArg AgentState.rank h_snd]
    change (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C ℓ, C w)).2.rank.val = 0
    rw [transitionPEM_eq, show
      transitionPEM_prePhase4 n Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
        (C ℓ).1 (C w).1 (C ℓ).2 (C w).2 = p from rfl, hphase]
    exact hp₂_rank0
  · rw [congrArg AgentState.children h_snd]
    change (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C ℓ, C w)).2.children = 0
    rw [transitionPEM_eq, show
      transitionPEM_prePhase4 n Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
        (C ℓ).1 (C w).1 (C ℓ).2 (C w).2 = p from rfl, hphase]
    exact hp₂_children

theorem settled_root_dormant_step_resettingCount_lt
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n)
    {C : Config (AgentState n) Opinion n}
    {ℓ w : Fin n} (hℓw : ℓ ≠ w)
    (hℓ_settled : (C ℓ).1.role = .Settled)
    (hℓ_rank0 : (C ℓ).1.rank.val = 0)
    (hℓ_children : (C ℓ).1.children = 0)
    (hℓ_L : (C ℓ).1.leader = .L)
    (hw_res : (C w).1.role = .Resetting)
    (hw_rc : (C w).1.resetcount = 0) :
    let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    resettingCount (C.step P ℓ w) < resettingCount C := by
  classical
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  let C' : Config (AgentState n) Opinion n := C.step P ℓ w
  have hstep :
      (C' ℓ).1.role = .Settled ∧ (C' w).1.role ≠ .Resetting := by
    cases hw_leader : (C w).1.leader with
    | F =>
        have h :=
          transitionPEM_settled_meets_dormant_trace
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            hn4 (C := C) (ℓ := ℓ) (w := w) hℓw
            hℓ_settled hℓ_rank0 hℓ_children hℓ_L hw_res hw_rc hw_leader
        exact ⟨by simpa [C', P] using h.1, by
          intro hw_reset'
          have hw_unsettled : (C' w).1.role = .Unsettled := by
            simpa [C', P] using h.2.2.2.2.1
          rw [hw_unsettled] at hw_reset'
          cases hw_reset'⟩
    | L =>
        have h :=
          transitionPEM_settled_meets_dormant_L_trace
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            hn4 (C := C) (ℓ := ℓ) (w := w) hℓw
            hℓ_settled hℓ_rank0 hℓ_children hℓ_L hw_res hw_rc hw_leader
        exact ⟨by simpa [C', P] using h.1, by
          intro hw_reset'
          have hw_settled : (C' w).1.role = .Settled := by
            simpa [C', P] using h.2.2.2.2.1
          rw [hw_settled] at hw_reset'
          cases hw_reset'⟩
  set S := Finset.univ.filter (fun x : Fin n => (C x).1.role = .Resetting) with hS
  set S' := Finset.univ.filter (fun x : Fin n => (C' x).1.role = .Resetting) with hS'
  have hw_mem : w ∈ S := by
    rw [hS, Finset.mem_filter]
    exact ⟨Finset.mem_univ w, hw_res⟩
  have hsub : S' ⊆ S.erase w := by
    intro x hx
    have hx_reset : (C' x).1.role = .Resetting := by
      rw [hS'] at hx
      exact (Finset.mem_filter.mp hx).2
    have hx_ne_w : x ≠ w := by
      intro hxw
      subst x
      exact hstep.2 hx_reset
    have hx_ne_ℓ : x ≠ ℓ := by
      intro hxℓ
      subst x
      rw [hstep.1] at hx_reset
      cases hx_reset
    have hx_old : C' x = C x := by
      dsimp [C', P]
      simp [Config.step, hℓw, hx_ne_ℓ, hx_ne_w]
    have hx_mem_old : x ∈ S := by
      rw [hS, Finset.mem_filter]
      rw [hx_old] at hx_reset
      exact ⟨Finset.mem_univ x, hx_reset⟩
    exact Finset.mem_erase.mpr ⟨hx_ne_w, hx_mem_old⟩
  have hle : S'.card ≤ (S.erase w).card := Finset.card_le_card hsub
  have herase : (S.erase w).card = S.card - 1 := Finset.card_erase_of_mem hw_mem
  have hlt : S'.card < S.card := by
    rw [herase] at hle
    have hpos : 0 < S.card := Finset.card_pos.mpr ⟨w, hw_mem⟩
    omega
  have hS_card : S.card = resettingCount C := by
    rw [hS]
    rfl
  have hS'_card : S'.card = resettingCount C' := by
    rw [hS']
    rfl
  change resettingCount C' < resettingCount C
  simpa [hS_card, hS'_card] using hlt

set_option maxHeartbeats 64000000 in
theorem settled_root_zero_resetting_to_no_reset
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n)
    (C : Config (AgentState n) Opinion n) {ℓ : Fin n}
    (hℓ_settled : (C ℓ).1.role = .Settled)
    (hℓ_rank0 : (C ℓ).1.rank.val = 0)
    (hℓ_children : (C ℓ).1.children = 0)
    (hℓ_L : (C ℓ).1.leader = .L)
    (hResetZero : ∀ w : Fin n, (C w).1.role = .Resetting → (C w).1.resetcount = 0) :
    let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    ∃ L : List (Fin n × Fin n),
      ∀ w : Fin n, (runPairs P C L w).1.role ≠ .Resetting := by
  classical
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  suffices go :
      ∀ k (C₀ : Config (AgentState n) Opinion n),
        resettingCount C₀ = k →
        (C₀ ℓ).1.role = .Settled →
        (C₀ ℓ).1.rank.val = 0 →
        (C₀ ℓ).1.children = 0 →
        (C₀ ℓ).1.leader = .L →
        (∀ w : Fin n, (C₀ w).1.role = .Resetting → (C₀ w).1.resetcount = 0) →
        ∃ L : List (Fin n × Fin n),
          ∀ w : Fin n, (runPairs P C₀ L w).1.role ≠ .Resetting by
    exact go (resettingCount C) C rfl hℓ_settled hℓ_rank0 hℓ_children hℓ_L hResetZero
  intro k
  induction k using Nat.strongRecOn with
  | ind k IH =>
    intro C₀ hk hroot_role hroot_rank hroot_children hroot_L hzero
    by_cases hk0 : k = 0
    · refine ⟨[], ?_⟩
      intro w hw_reset
      have hmem :
          w ∈ Finset.univ.filter (fun x : Fin n => (C₀ x).1.role = .Resetting) := by
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ w, hw_reset⟩
      have hcard_pos :
          0 < (Finset.univ.filter (fun x : Fin n => (C₀ x).1.role = .Resetting)).card :=
        Finset.card_pos.mpr ⟨w, hmem⟩
      unfold resettingCount at hk
      omega
    · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
      have hcard_pos :
          0 < (Finset.univ.filter (fun x : Fin n => (C₀ x).1.role = .Resetting)).card := by
        unfold resettingCount at hk
        omega
      obtain ⟨w, hw_mem⟩ := Finset.card_pos.mp hcard_pos
      have hw_res : (C₀ w).1.role = .Resetting := by
        exact (Finset.mem_filter.mp hw_mem).2
      have hw_rc : (C₀ w).1.resetcount = 0 := hzero w hw_res
      have hℓw : ℓ ≠ w := by
        intro h
        subst w
        rw [hroot_role] at hw_res
        cases hw_res
      let C₁ : Config (AgentState n) Opinion n := C₀.step P ℓ w
      have hmeasure : resettingCount C₁ < resettingCount C₀ := by
        simpa [P, C₁] using
          (settled_root_dormant_step_resettingCount_lt
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            hn4 (C := C₀) (ℓ := ℓ) (w := w) hℓw
            hroot_role hroot_rank hroot_children hroot_L hw_res hw_rc)
      have hstep_root :
          (C₁ ℓ).1.role = .Settled ∧
          (C₁ ℓ).1.rank.val = 0 ∧
          (C₁ ℓ).1.children = 0 ∧
          (C₁ ℓ).1.leader = .L ∧
          (C₁ w).1.role ≠ .Resetting := by
        cases hw_leader : (C₀ w).1.leader with
        | F =>
            have h :=
              transitionPEM_settled_meets_dormant_trace
                (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
                hn4 (C := C₀) (ℓ := ℓ) (w := w) hℓw
                hroot_role hroot_rank hroot_children hroot_L hw_res hw_rc hw_leader
            refine ⟨by simpa [C₁, P] using h.1,
              by simpa [C₁, P] using h.2.1,
              by simpa [C₁, P] using h.2.2.1,
              by simpa [C₁, P] using h.2.2.2.1, ?_⟩
            intro hw_reset'
            have hw_unsettled : (C₁ w).1.role = .Unsettled := by
              simpa [C₁, P] using h.2.2.2.2.1
            rw [hw_unsettled] at hw_reset'
            cases hw_reset'
        | L =>
            have h :=
              transitionPEM_settled_meets_dormant_L_trace
                (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
                hn4 (C := C₀) (ℓ := ℓ) (w := w) hℓw
                hroot_role hroot_rank hroot_children hroot_L hw_res hw_rc hw_leader
            refine ⟨by simpa [C₁, P] using h.1,
              by simpa [C₁, P] using h.2.1,
              by simpa [C₁, P] using h.2.2.1,
              by simpa [C₁, P] using h.2.2.2.1, ?_⟩
            intro hw_reset'
            have hw_settled : (C₁ w).1.role = .Settled := by
              simpa [C₁, P] using h.2.2.2.2.1
            rw [hw_settled] at hw_reset'
            cases hw_reset'
      have hzero₁ :
          ∀ x : Fin n, (C₁ x).1.role = .Resetting → (C₁ x).1.resetcount = 0 := by
        intro x hx_reset
        by_cases hxℓ : x = ℓ
        · subst x
          rw [hstep_root.1] at hx_reset
          cases hx_reset
        · by_cases hxw : x = w
          · subst x
            exact False.elim (hstep_root.2.2.2.2 hx_reset)
          · have hx_old : C₁ x = C₀ x := by
              dsimp [C₁, P]
              simp [Config.step, hℓw, hxℓ, hxw]
            have hx_old_reset : (C₀ x).1.role = .Resetting := by
              rw [← hx_old]
              exact hx_reset
            rw [hx_old]
            exact hzero x hx_old_reset
      obtain ⟨Ltail, htail⟩ :=
        IH (resettingCount C₁) (by omega) C₁ rfl
          hstep_root.1 hstep_root.2.1 hstep_root.2.2.1
          hstep_root.2.2.2.1 hzero₁
      refine ⟨[(ℓ, w)] ++ Ltail, ?_⟩
      intro x
      rw [runPairs_append]
      change (runPairs P C₁ Ltail x).1.role ≠ .Resetting
      exact htail x

theorem awakening_of_pair_trace
    {C C' : Config (AgentState n) Opinion n} {ℓ w : Fin n}
    (hDormant : IsDormantConfig C) (hℓw : ℓ ≠ w)
    (hℓ_old_leader : (C ℓ).1.leader = .L)
    (hℓ_leader : (C' ℓ).1.leader = .L)
    (hℓ_role : (C' ℓ).1.role = .Settled)
    (hℓ_rank : (C' ℓ).1.rank.val = 0)
    (hℓ_children : (C' ℓ).1.children = 0)
    (hw_leader : (C' w).1.leader = .F)
    (hw_ok : (C' w).1.role = .Unsettled ∨
      ((C' w).1.role = .Resetting ∧ (C' w).1.resetcount = 0))
    (hOthers : ∀ x : Fin n, x ≠ ℓ → x ≠ w → C' x = C x) :
    IsAwakeningConfig C' := by
  rcases hDormant with ⟨hAllR, hAllRc0, hUnique, _hLeaderCases⟩
  obtain ⟨oldℓ, _holdℓ_L, hOldUnique⟩ := hUnique
  have hUnique' : ∃! x : Fin n, (C' x).1.leader = .L := by
    refine ⟨ℓ, hℓ_leader, ?_⟩
    intro y hy
    by_cases hyℓ : y = ℓ
    · exact hyℓ
    · by_cases hyw : y = w
      · subst y
        rw [hw_leader] at hy
        cases hy
      · have hy_old : (C y).1.leader = .L := by
          have hxy := hOthers y hyℓ hyw
          rw [hxy] at hy
          exact hy
        have hy_old_eq : y = oldℓ := hOldUnique y hy_old
        have hℓ_old_eq : ℓ = oldℓ := hOldUnique ℓ hℓ_old_leader
        exact hy_old_eq.trans hℓ_old_eq.symm
  refine ⟨hUnique', ?_, ?_⟩
  · intro y hyL
    obtain ⟨newℓ, _hnewℓ_L, hNewUnique⟩ := hUnique'
    have hyu : y = newℓ := hNewUnique y hyL
    have hℓu : ℓ = newℓ := hNewUnique ℓ hℓ_leader
    have hy_eq : y = ℓ := hyu.trans hℓu.symm
    rw [hy_eq]
    exact ⟨hℓ_role, hℓ_rank, hℓ_children⟩
  · intro y hyF
    by_cases hyℓ : y = ℓ
    · subst y
      rw [hℓ_leader] at hyF
      cases hyF
    · by_cases hyw : y = w
      · subst y
        exact hw_ok
      · have hxy := hOthers y hyℓ hyw
        rw [hxy]
        exact Or.inr ⟨hAllR y, hAllRc0 y⟩

theorem phase3a_to_awakening
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hRmax : 0 < Rmax) (hDmax : 0 < Dmax)
    (C : Config (AgentState n) Opinion n)
    (hDormant : IsDormantConfig C) :
    ∃ L : List (Fin n × Fin n),
      IsAwakeningConfig (runPairs (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L) := by
  classical
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  rcases hDormant with ⟨hAllR₀, hAllRc0₀, hUnique₀, hLeaderCases₀⟩
  obtain ⟨ℓ, hℓ_L₀, hℓ_unique₀⟩ := hUnique₀
  have hne_of_fin (a : Fin n) : ∃ b : Fin n, b ≠ a := by
    have hcard : 1 < Fintype.card (Fin n) := by
      rw [Fintype.card_fin]
      omega
    exact Fintype.exists_ne_of_one_lt_card hcard a
  obtain ⟨w, hw_ne_ℓ⟩ := hne_of_fin ℓ
  have hℓw : ℓ ≠ w := hw_ne_ℓ.symm
  have hw_F₀ : (C w).1.leader = .F := by
    cases hw_leader : (C w).1.leader with
    | L =>
        have hw_eq : w = ℓ := hℓ_unique₀ w hw_leader
        exact False.elim (hw_ne_ℓ hw_eq)
    | F => rfl
  have hDormant₀ : IsDormantConfig C :=
    ⟨hAllR₀, hAllRc0₀, ⟨ℓ, hℓ_L₀, hℓ_unique₀⟩, hLeaderCases₀⟩
  suffices wake :
      ∀ k (C₀ : Config (AgentState n) Opinion n),
        IsDormantConfig C₀ →
        (C₀ ℓ).1.leader = .L →
        (C₀ w).1.leader = .F →
        (C₀ ℓ).1.delaytimer ≤ k →
        ∃ L : List (Fin n × Fin n), IsAwakeningConfig (runPairs P C₀ L) by
    exact wake (C ℓ).1.delaytimer C hDormant₀ hℓ_L₀ hw_F₀ le_rfl
  intro k
  induction k using Nat.strongRecOn with
  | ind k IH =>
    intro C₀ hDorm hℓ_L hw_F hdt_le
    rcases hDorm with ⟨hAllR, hAllRc0, hUnique, hLeaderCases⟩
    have hUnique_saved : ∃! x : Fin n, (C₀ x).1.leader = .L := hUnique
    obtain ⟨oldℓ, _holdℓ_L, hOldUnique⟩ := hUnique
    by_cases hℓ_low : (C₀ ℓ).1.delaytimer ≤ 1
    · let C₁ : Config (AgentState n) Opinion n := C₀.step P ℓ w
      have hstep := by
        simpa [P] using
          (transitionPEM_dormant_leader_low_dt_wakes
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            (C := C₀) (ℓ := ℓ) (w := w) hℓw
            (hAllR ℓ) (hAllRc0 ℓ) hℓ_low hℓ_L
            (hAllR w) (hAllRc0 w) hw_F)
      have hw_leader₁ : (C₁ w).1.leader = .F := by
        simpa [C₁, P] using
          (transitionPEM_dormant_leader_low_dt_follower_leader
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            (C := C₀) (ℓ := ℓ) (w := w) hℓw
            (hAllR ℓ) (hAllRc0 ℓ) hℓ_low hℓ_L
            (hAllR w) (hAllRc0 w) hw_F)
      have hOthers₁ : ∀ x : Fin n, x ≠ ℓ → x ≠ w → C₁ x = C₀ x := by
        intro x hxℓ hxw
        dsimp [C₁]
        simp [Config.step, hℓw, hxℓ, hxw]
      refine ⟨[(ℓ, w)], ?_⟩
      change IsAwakeningConfig C₁
      exact awakening_of_pair_trace
        (C := C₀) (C' := C₁) (ℓ := ℓ) (w := w)
        ⟨hAllR, hAllRc0, hUnique_saved, hLeaderCases⟩ hℓw hℓ_L
        hstep.2.2.2.1 hstep.1 (congrArg Fin.val hstep.2.1)
        hstep.2.2.1 hw_leader₁ hstep.2.2.2.2 hOthers₁
    · have hℓ_high : 1 < (C₀ ℓ).1.delaytimer := by omega
      by_cases hw_low : (C₀ w).1.delaytimer ≤ 1
      · let C₁ : Config (AgentState n) Opinion n := C₀.step P ℓ w
        let C₂ : Config (AgentState n) Opinion n := C₁.step P ℓ w
        have hstep₁ := by
          simpa [P] using
            (transitionPEM_dormant_follower_low_dt_unsettles
              (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
              (C := C₀) (ℓ := ℓ) (w := w) hℓw
              (hAllR ℓ) (hAllRc0 ℓ) hℓ_high hℓ_L
              (hAllR w) (hAllRc0 w) hw_low hw_F)
        have hstep₂ := by
          simpa [P, C₁] using
            (transitionPEM_dormant_leader_with_unsettled_follower_wakes
              (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
              (C := C₁) (ℓ := ℓ) (w := w) hℓw
              hstep₁.1 hstep₁.2.1 hstep₁.2.2.2.1
              hstep₁.2.2.2.2.1 hstep₁.2.2.2.2.2)
        have hOthers₂ : ∀ x : Fin n, x ≠ ℓ → x ≠ w → C₂ x = C₀ x := by
          intro x hxℓ hxw
          dsimp [C₂, C₁]
          simp [Config.step, hℓw, hxℓ, hxw]
        refine ⟨[(ℓ, w), (ℓ, w)], ?_⟩
        change IsAwakeningConfig C₂
        exact awakening_of_pair_trace
          (C := C₀) (C' := C₂) (ℓ := ℓ) (w := w)
          ⟨hAllR, hAllRc0, hUnique_saved, hLeaderCases⟩ hℓw hℓ_L
          hstep₂.2.2.2.1 hstep₂.1 (congrArg Fin.val hstep₂.2.1)
          hstep₂.2.2.1 hstep₂.2.2.2.2.2 (Or.inl hstep₂.2.2.2.2.1) hOthers₂
      · have hw_high : 1 < (C₀ w).1.delaytimer := by omega
        let C₁ : Config (AgentState n) Opinion n := C₀.step P ℓ w
        have hstep := by
          simpa [P] using
            (transitionPEM_dormant_dt_decrease
              (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
              (C := C₀) (ℓ := ℓ) (w := w) hℓw
              (hAllR ℓ) (hAllRc0 ℓ) hℓ_L
              (hAllR w) (hAllRc0 w) hw_F hℓ_high hw_high)
        have hOthers₁ : ∀ x : Fin n, x ≠ ℓ → x ≠ w → C₁ x = C₀ x := by
          intro x hxℓ hxw
          dsimp [C₁]
          simp [Config.step, hℓw, hxℓ, hxw]
        have hAllR₁ : ∀ x : Fin n, (C₁ x).1.role = .Resetting := by
          intro x
          by_cases hxℓ : x = ℓ
          · subst x
            exact hstep.1
          · by_cases hxw : x = w
            · subst x
              exact hstep.2.2.2.2.1
            · rw [hOthers₁ x hxℓ hxw]
              exact hAllR x
        have hAllRc0₁ : ∀ x : Fin n, (C₁ x).1.resetcount = 0 := by
          intro x
          by_cases hxℓ : x = ℓ
          · subst x
            exact hstep.2.1
          · by_cases hxw : x = w
            · subst x
              exact hstep.2.2.2.2.2.1
            · rw [hOthers₁ x hxℓ hxw]
              exact hAllRc0 x
        have hUnique₁ : ∃! x : Fin n, (C₁ x).1.leader = .L := by
          refine ⟨ℓ, hstep.2.2.2.1, ?_⟩
          intro x hxL
          by_cases hxℓ : x = ℓ
          · exact hxℓ
          · by_cases hxw : x = w
            · subst x
              rw [hstep.2.2.2.2.2.2.2] at hxL
              cases hxL
            · have hx_old : (C₀ x).1.leader = .L := by
                rw [hOthers₁ x hxℓ hxw] at hxL
                exact hxL
              have hx_old_eq : x = oldℓ := hOldUnique x hx_old
              have hℓ_old_eq : ℓ = oldℓ := hOldUnique ℓ hℓ_L
              exact hx_old_eq.trans hℓ_old_eq.symm
        have hDorm₁ : IsDormantConfig C₁ := by
          refine ⟨hAllR₁, hAllRc0₁, hUnique₁, ?_⟩
          intro x
          cases (C₁ x).1.leader <;> simp
        have hm_lt : (C₁ ℓ).1.delaytimer < k := by
          rw [hstep.2.2.1]
          omega
        obtain ⟨Ltail, htail⟩ :=
          IH (C₁ ℓ).1.delaytimer hm_lt C₁ hDorm₁ hstep.2.2.2.1
            hstep.2.2.2.2.2.2.2 le_rfl
        refine ⟨[(ℓ, w)] ++ Ltail, ?_⟩
        rw [runPairs_append]
        change IsAwakeningConfig (runPairs P C₁ Ltail)
        exact htail

def awakeningResettingFollowers (C : Config (AgentState n) Opinion n) : Finset (Fin n) :=
  Finset.univ.filter (fun w : Fin n =>
    (C w).1.leader = .F ∧ (C w).1.role = .Resetting)

/-- Phase 3b+3c: from IsAwakeningConfig, sweep to FreshRankingStart.
(ChatGPT: unique leader enables clean one-pass sweep.) -/
theorem phase3bc_from_awakening
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n)
    (C : Config (AgentState n) Opinion n)
    (hAwake : IsAwakeningConfig C) :
    ∃ L : List (Fin n × Fin n),
      FreshRankingStart (runPairs (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L) := by
  classical
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  suffices sweep :
      ∀ k (C₀ : Config (AgentState n) Opinion n),
        IsAwakeningConfig C₀ →
        (awakeningResettingFollowers C₀).card = k →
        ∃ L : List (Fin n × Fin n), FreshRankingStart (runPairs P C₀ L) by
    exact sweep (awakeningResettingFollowers C).card C hAwake rfl
  intro k
  induction k using Nat.strongRecOn with
  | ind k IH =>
    intro C₀ hAwake₀ hcard
    rcases hAwake₀ with ⟨hUnique, hLeaderOK, hFollowerOK⟩
    obtain ⟨root, hroot_L, hroot_unique⟩ := hUnique
    by_cases hk0 : k = 0
    · refine ⟨[], ?_⟩
      simp only [runPairs_nil]
      have hroot_ok := hLeaderOK root hroot_L
      refine ⟨root, hroot_ok.1, hroot_ok.2.1, hroot_ok.2.2, ?_⟩
      intro w hw_ne_root
      have hw_F : (C₀ w).1.leader = .F := by
        cases hw_leader : (C₀ w).1.leader with
        | L =>
            have hw_eq : w = root := hroot_unique w hw_leader
            exact False.elim (hw_ne_root hw_eq)
        | F => rfl
      rcases hFollowerOK w hw_F with hw_un | hw_res
      · exact hw_un
      · exfalso
        have hw_bad : w ∈ awakeningResettingFollowers C₀ := by
          dsimp [awakeningResettingFollowers]
          simp [hw_F, hw_res.1]
        have hpos : 0 < (awakeningResettingFollowers C₀).card :=
          Finset.card_pos.mpr ⟨w, hw_bad⟩
        omega
    · have hpos : 0 < (awakeningResettingFollowers C₀).card := by
        rw [hcard]
        omega
      obtain ⟨w, hw_bad⟩ := Finset.card_pos.mp hpos
      have hw_F : (C₀ w).1.leader = .F := by
        exact (Finset.mem_filter.mp hw_bad).2.1
      have hw_res : (C₀ w).1.role = .Resetting := by
        exact (Finset.mem_filter.mp hw_bad).2.2
      have hw_rc : (C₀ w).1.resetcount = 0 := by
        rcases hFollowerOK w hw_F with hw_un | hw_reset
        · rw [hw_un] at hw_res
          cases hw_res
        · exact hw_reset.2
      have hroot_ne_w : root ≠ w := by
        intro hrw
        subst w
        rw [hroot_L] at hw_F
        cases hw_F
      let C₁ : Config (AgentState n) Opinion n := C₀.step P root w
      have hroot_ok := hLeaderOK root hroot_L
      have htrace := by
        simpa [P, C₁] using
          (transitionPEM_settled_meets_dormant_trace
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            hn4 (C := C₀) (ℓ := root) (w := w) hroot_ne_w
            hroot_ok.1 hroot_ok.2.1 hroot_ok.2.2 hroot_L
            hw_res hw_rc hw_F)
      have hOthers : ∀ x : Fin n, x ≠ root → x ≠ w → C₁ x = C₀ x := by
        intro x hxroot hxw
        dsimp [C₁]
        simp [Config.step, hroot_ne_w, hxroot, hxw]
      have hAwake₁ : IsAwakeningConfig C₁ := by
        refine ⟨?_, ?_, ?_⟩
        · refine ⟨root, htrace.2.2.2.1, ?_⟩
          intro y hyL
          by_cases hyroot : y = root
          · exact hyroot
          · by_cases hyw : y = w
            · subst y
              rw [htrace.2.2.2.2.2] at hyL
              cases hyL
            · have hy_old : (C₀ y).1.leader = .L := by
                have hxy := hOthers y hyroot hyw
                rw [hxy] at hyL
                exact hyL
              exact hroot_unique y hy_old
        · intro y hyL
          have hyroot : y = root := by
            by_cases hyroot : y = root
            · exact hyroot
            · by_cases hyw : y = w
              · subst y
                rw [htrace.2.2.2.2.2] at hyL
                cases hyL
              · have hy_old : (C₀ y).1.leader = .L := by
                  have hxy := hOthers y hyroot hyw
                  rw [hxy] at hyL
                  exact hyL
                exact hroot_unique y hy_old
          subst y
          exact ⟨htrace.1, htrace.2.1, htrace.2.2.1⟩
        · intro y hyF
          by_cases hyroot : y = root
          · subst y
            rw [htrace.2.2.2.1] at hyF
            cases hyF
          · by_cases hyw : y = w
            · subst y
              exact Or.inl htrace.2.2.2.2.1
            · have hyF_old : (C₀ y).1.leader = .F := by
                have hxy := hOthers y hyroot hyw
                rw [hxy] at hyF
                exact hyF
              have hy_ok := hFollowerOK y hyF_old
              rw [hOthers y hyroot hyw]
              exact hy_ok
      have hsubset :
          awakeningResettingFollowers C₁ ⊆ (awakeningResettingFollowers C₀).erase w := by
        intro x hx
        have hxF : (C₁ x).1.leader = .F := (Finset.mem_filter.mp hx).2.1
        have hxR : (C₁ x).1.role = .Resetting := (Finset.mem_filter.mp hx).2.2
        have hx_ne_w : x ≠ w := by
          intro hxw
          subst x
          rw [htrace.2.2.2.2.1] at hxR
          cases hxR
        have hx_ne_root : x ≠ root := by
          intro hxroot
          subst x
          rw [htrace.1] at hxR
          cases hxR
        have hx_old_state := hOthers x hx_ne_root hx_ne_w
        have hx_old : x ∈ awakeningResettingFollowers C₀ := by
          dsimp [awakeningResettingFollowers]
          rw [hx_old_state] at hxF hxR
          simp [hxF, hxR]
        exact Finset.mem_erase.mpr ⟨hx_ne_w, hx_old⟩
      have hcard_lt : (awakeningResettingFollowers C₁).card < k := by
        have hle := Finset.card_le_card hsubset
        have herase : ((awakeningResettingFollowers C₀).erase w).card =
            (awakeningResettingFollowers C₀).card - 1 :=
          Finset.card_erase_of_mem hw_bad
        rw [herase, hcard] at hle
        omega
      obtain ⟨Ltail, htail⟩ :=
        IH (awakeningResettingFollowers C₁).card hcard_lt C₁ hAwake₁ rfl
      refine ⟨[(root, w)] ++ Ltail, ?_⟩
      rw [runPairs_append]
      change FreshRankingStart (runPairs P C₁ Ltail)
      exact htail

/-! ### Phase 4 infrastructure (from ChatGPT)

HeapPrefix-based induction: grow the binary tree rank by rank. -/

def heapParent (k : ℕ) : ℕ := (k - 1) / 2
def heapChildIndex (k : ℕ) : ℕ := (k - 1) % 2

def heapChildrenBefore (k r : ℕ) : ℕ :=
  (if 2 * r + 1 < k then 1 else 0) + (if 2 * r + 2 < k then 1 else 0)

lemma heap_parent_rank {k : ℕ} (hk : 1 ≤ k) :
    2 * heapParent k + heapChildIndex k + 1 = k := by
  unfold heapParent heapChildIndex; omega

lemma heapChildIndex_lt_two (k : ℕ) : heapChildIndex k < 2 := by
  unfold heapChildIndex
  exact Nat.mod_lt _ (by omega)

lemma heapParent_lt_self {k : ℕ} (hk : 1 ≤ k) : heapParent k < k := by
  have hp := heap_parent_rank hk
  have hi := heapChildIndex_lt_two k
  omega

lemma heapChildrenBefore_parent {k : ℕ} (hk : 1 ≤ k) :
    heapChildrenBefore k (heapParent k) = heapChildIndex k := by
  have hp := heap_parent_rank hk
  have hi := heapChildIndex_lt_two k
  unfold heapChildrenBefore
  split_ifs <;> omega

lemma heapChildrenBefore_succ_parent {k : ℕ} (hk : 1 ≤ k) :
    heapChildrenBefore (k + 1) (heapParent k) = heapChildIndex k + 1 := by
  have hp := heap_parent_rank hk
  have hi := heapChildIndex_lt_two k
  unfold heapChildrenBefore
  split_ifs <;> omega

lemma heapChildrenBefore_succ_ne_parent {k r : ℕ}
    (hr : r ≠ heapParent k) :
    heapChildrenBefore (k + 1) r = heapChildrenBefore k r := by
  unfold heapChildrenBefore
  unfold heapParent at hr
  split_ifs <;> omega

lemma heapChildrenBefore_self_succ (k : ℕ) :
    heapChildrenBefore (k + 1) k = 0 := by
  unfold heapChildrenBefore
  split_ifs <;> omega

def SettledMedianTimerGood (C : Config (AgentState n) Opinion n) : Prop :=
  ∀ μ : Fin n, (C μ).1.role = .Settled →
    (C μ).1.rank.val + 1 = ceilHalf n → 2 ≤ (C μ).1.timer

def SettledMedianTimerStrong (C : Config (AgentState n) Opinion n) : Prop :=
  ∀ μ : Fin n, (C μ).1.role = .Settled →
    (C μ).1.rank.val + 1 = ceilHalf n → 3 ≤ (C μ).1.timer

theorem SettledMedianTimerStrong.toGood {C : Config (AgentState n) Opinion n}
    (h : SettledMedianTimerStrong C) : SettledMedianTimerGood C :=
  fun μ hs hr => Nat.le_trans (show 2 ≤ 3 by omega) (h μ hs hr)

def HeapPrefix (C : Config (AgentState n) Opinion n) (k : ℕ) : Prop :=
  k ≤ n ∧
  (∀ w, (C w).1.role = .Settled → (C w).1.rank.val < k) ∧
  (∀ r, r < k → ∃! w : Fin n, (C w).1.role = .Settled ∧ (C w).1.rank.val = r) ∧
  (∀ w, (C w).1.role = .Settled ∨ (C w).1.role = .Unsettled) ∧
  (∀ w, (C w).1.role = .Settled →
    (C w).1.children = heapChildrenBefore k (C w).1.rank.val)

lemma FreshRankingStart.to_heapPrefix_one
    {C : Config (AgentState n) Opinion n} (hSeed : FreshRankingStart C) :
    HeapPrefix C 1 := by
  obtain ⟨root, hroot_settled, hroot_rank, hroot_children, hothers⟩ := hSeed
  refine ⟨by omega, ?_, ?_, ?_, ?_⟩
  · -- All Settled agents have rank < 1
    intro w hw; by_cases h : w = root
    · subst h; omega
    · exact absurd hw (by rw [hothers w h]; decide)
  · -- Rank 0 has a unique Settled holder
    intro r hr
    have hr0 : r = 0 := by omega
    subst hr0
    exact ⟨root, ⟨hroot_settled, hroot_rank⟩,
      fun w ⟨hw_s, hw_r⟩ => by
        by_contra hne
        exact absurd hw_s (by rw [hothers w hne]; decide)⟩
  · -- Every agent is Settled or Unsettled
    intro w; by_cases h : w = root
    · exact Or.inl (h ▸ hroot_settled)
    · exact Or.inr (hothers w h)
  · -- Children counters match heapChildrenBefore 1
    intro w hw; by_cases h : w = root
    · subst h; simp [hroot_children, heapChildrenBefore]
    · exact absurd hw (by rw [hothers w h]; decide)

lemma FreshRankingStart.to_timerGood {C : Config (AgentState n) Opinion n}
    (hn4 : 4 ≤ n) (hSeed : FreshRankingStart C) :
    SettledMedianTimerGood C := by
  intro μ hμ_settled hμ_med
  obtain ⟨root, hroot_settled, hroot_rank, _, hothers⟩ := hSeed
  -- μ must be root (only Settled agent)
  by_cases h : μ = root
  · -- μ = root: rank.val = 0, so rank.val + 1 = 1. ceilHalf n ≥ 2 for n ≥ 4.
    subst h; rw [hroot_rank] at hμ_med; unfold ceilHalf at hμ_med; omega
  · -- μ ≠ root: μ is Unsettled, contradicts hμ_settled
    exact absurd hμ_settled (by rw [hothers μ h]; decide)

lemma FreshRankingStart.to_timerStrong {C : Config (AgentState n) Opinion n}
    (hn4 : 4 ≤ n) (hSeed : FreshRankingStart C) :
    SettledMedianTimerStrong C := by
  intro μ hμ_settled hμ_med
  obtain ⟨root, _hroot_settled, hroot_rank, _, hothers⟩ := hSeed
  by_cases h : μ = root
  · subst h
    rw [hroot_rank] at hμ_med
    unfold ceilHalf at hμ_med
    omega
  · exact absurd hμ_settled (by rw [hothers μ h]; decide)

lemma HeapPrefix.to_InSrank {C : Config (AgentState n) Opinion n}
    (hHeap : HeapPrefix C n) : InSrank C := by
  classical
  rcases hHeap with ⟨_hkn, _hrank_lt, hRankUnique, _hRoles, _hChildren⟩
  let S : Finset (Fin n) :=
    Finset.univ.filter (fun w : Fin n => (C w).1.role = .Settled)
  have hUniqueFin :
      ∀ r : Fin n, ∃! w : Fin n, w ∈ S ∧ (C w).1.rank = r := by
    intro r
    obtain ⟨w, hw, hw_unique⟩ := hRankUnique r.val r.isLt
    refine ⟨w, ?_, ?_⟩
    · exact ⟨by simpa [S] using hw.1, Fin.ext hw.2⟩
    · intro y hy
      exact hw_unique y ⟨by simpa [S] using hy.1, congrArg Fin.val hy.2⟩
  let rankOnSettled : {w : Fin n // w ∈ S} → Fin n :=
    fun w => (C w.1).1.rank
  have hBij : Function.Bijective rankOnSettled := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      obtain ⟨z, _hz, hz_unique⟩ := hUniqueFin (rankOnSettled x)
      have hxz : x.1 = z := hz_unique x.1 ⟨x.2, rfl⟩
      have hyz : y.1 = z := hz_unique y.1 ⟨y.2, hxy.symm⟩
      exact hxz.trans hyz.symm
    · intro r
      obtain ⟨w, hw, _⟩ := hUniqueFin r
      exact ⟨⟨w, hw.1⟩, hw.2⟩
  have hCardS : S.card = n := by
    have hCardSubtype :
        Fintype.card {w : Fin n // w ∈ S} = Fintype.card (Fin n) :=
      Fintype.card_congr (Equiv.ofBijective rankOnSettled hBij)
    simpa using hCardSubtype
  have hS_univ : S = Finset.univ := by
    by_contra hne
    obtain ⟨w, hw_not⟩ : ∃ w : Fin n, w ∉ S := by
      by_contra hnone
      have hall : ∀ w : Fin n, w ∈ S := by
        intro w
        by_contra hw
        exact hnone ⟨w, hw⟩
      exact hne (Finset.eq_univ_of_forall hall)
    have hSub : S ⊆ Finset.univ.erase w := by
      intro x hx
      exact Finset.mem_erase.mpr ⟨by
        intro hxw
        subst x
        exact hw_not hx, Finset.mem_univ x⟩
    have hCardLe : S.card ≤ (Finset.univ.erase w).card := Finset.card_le_card hSub
    have hErase : (Finset.univ.erase w).card = n - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ w)]
      simp
    have hn_pos : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le w.val) w.isLt
    rw [hCardS, hErase] at hCardLe
    omega
  have hAllSettled : ∀ w : Fin n, (C w).1.role = .Settled := by
    intro w
    have hw : w ∈ S := by
      rw [hS_univ]
      exact Finset.mem_univ w
    simpa [S] using hw
  refine ⟨hAllSettled, ?_⟩
  intro u v huv
  obtain ⟨z, _hz, hz_unique⟩ := hUniqueFin ((C u).1.rank)
  have huz : u = z := hz_unique u ⟨by simpa [S, hAllSettled u], rfl⟩
  have hvz : v = z := hz_unique v ⟨by simpa [S, hAllSettled v], huv.symm⟩
  exact huz.trans hvz.symm

lemma HeapPrefix.to_RankingEndpoint {C : Config (AgentState n) Opinion n}
    (hHeap : HeapPrefix C n)
    (hTimer : SettledMedianTimerGood C) :
    RankingEndpoint C := by
  have hSrank : InSrank C := HeapPrefix.to_InSrank hHeap
  exact ⟨hSrank, Or.inl (fun μ hμ_med => hTimer μ (hSrank.allSettled μ) hμ_med)⟩

/-- The ONE protocol-specific lemma: recruit rank k into the heap prefix. -/

-- Supporting Lemmas

lemma heapPrefix_no_unsettled_contradiction {n : ℕ} {C : Config (AgentState n) Opinion n} {k : ℕ}
    (hk_lt : k < n) (hHeap : HeapPrefix C k) (hall_settled : ∀ w : Fin n, (C w).1.role = .Settled) : False := by
  classical
  rcases hHeap with ⟨_hkn, hRank_lt, hRankUnique, _hRoles, _hChildren⟩
  let rankIntoPrefix : Fin n → Fin k :=
    fun w => ⟨(C w).1.rank.val, hRank_lt w (hall_settled w)⟩
  have hInjective : Function.Injective rankIntoPrefix := by
    intro u v huv
    have hrank_val : (C u).1.rank.val = (C v).1.rank.val := by
      simpa [rankIntoPrefix] using congrArg Fin.val huv
    obtain ⟨z, _hz, hz_unique⟩ := hRankUnique (C u).1.rank.val (hRank_lt u (hall_settled u))
    have huz : u = z := hz_unique u ⟨hall_settled u, rfl⟩
    have hvz : v = z := hz_unique v ⟨hall_settled v, hrank_val.symm⟩
    exact huz.trans hvz.symm
  have hCardLe : n ≤ k := by
    simpa using Fintype.card_le_of_injective rankIntoPrefix hInjective
  omega

lemma rankDeltaOSSR_recruit_ba
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {a b : AgentState n}
    (ha : a.role = .Unsettled)
    (hb : b.role = .Settled)
    (hb_children : b.children < 2)
    (h_valid : 2 * b.rank.val + b.children + 1 < n) :
    rankDeltaOSSR Rmax Emax Dmax hn (a, b) =
      ({ a with role := .Settled, children := 0,
                rank := ⟨2 * b.rank.val + b.children + 1, h_valid⟩ },
       { b with children := b.children + 1 }) := by
  have ha_not_reset : a.role ≠ .Resetting := by rw [ha]; decide
  have hb_not_reset : b.role ≠ .Resetting := by rw [hb]; decide
  have ha_not_settled : a.role ≠ .Settled := by rw [ha]; decide
  have hb_not_unsettled : b.role ≠ .Unsettled := by rw [hb]; decide
  unfold rankDeltaOSSR
  simp [ha, hb, ha_not_reset, hb_not_reset, ha_not_settled, hb_not_unsettled,
    hb_children, h_valid]

lemma phase4_swap_eq_of_not_swap
    {a₀ a₁ : AgentState n} {x₀ x₁ : Opinion}
    (h : ¬(a₀.rank < a₁.rank ∧ x₀ = .B ∧ x₁ = .A)) :
    phase4_swap a₀ a₁ x₀ x₁ = (a₀, a₁) := by
  simp [phase4_swap, h]

lemma phase4_decide_preserves_role_rank_children
    {b₀ b₁ : AgentState n} {x₀ x₁ : Opinion} :
    let c := phase4_decide n b₀ b₁ x₀ x₁
    c.1.role = b₀.role ∧ c.1.rank = b₀.rank ∧ c.1.children = b₀.children ∧
    c.2.role = b₁.role ∧ c.2.rank = b₁.rank ∧ c.2.children = b₁.children := by
  unfold phase4_decide
  split_ifs <;> simp

lemma phase4_decide_preserves_timer
    {b₀ b₁ : AgentState n} {x₀ x₁ : Opinion} :
    let c := phase4_decide n b₀ b₁ x₀ x₁
    c.1.timer = b₀.timer ∧ c.2.timer = b₁.timer := by
  unfold phase4_decide
  split_ifs <;> simp

lemma phase4_propagate_preserves_rank_children
    {Rmax : ℕ} {b₀ b₁ : AgentState n} :
    let c := phase4_propagate n Rmax b₀ b₁
    c.1.rank = b₀.rank ∧ c.1.children = b₀.children ∧
    c.2.rank = b₁.rank ∧ c.2.children = b₁.children := by
  unfold phase4_propagate
  by_cases hmed₀ : b₀.rank.val + 1 = ceilHalf n
  · simp [hmed₀]
    by_cases hmax₁ : b₁.rank.val + 1 = n
    · simp [hmax₁]
      by_cases hreset : b₀.timer - 1 = 0 ∧ b₀.answer ≠ b₁.answer
      · simp [hreset]
      · simp [hreset]
    · simp [hmax₁]
      by_cases hreset : b₀.timer = 0 ∧ b₀.answer ≠ b₁.answer
      · simp [hreset]
      · simp [hreset]
  · simp [hmed₀]
    by_cases hmed₁ : b₁.rank.val + 1 = ceilHalf n
    · simp [hmed₁]
      by_cases hmax₀ : b₀.rank.val + 1 = n
      · simp [hmax₀]
        by_cases hreset : b₁.timer - 1 = 0 ∧ b₁.answer ≠ b₀.answer
        · simp [hreset]
        · simp [hreset]
      · simp [hmax₀]
        by_cases hreset : b₁.timer = 0 ∧ b₁.answer ≠ b₀.answer
        · simp [hreset]
        · simp [hreset]
    · simp [hmed₁]

lemma phase4_propagate_settled_of_positive_median_timers
    {Rmax : ℕ} {b₀ b₁ : AgentState n}
    (h₀ : b₀.role = .Settled) (h₁ : b₁.role = .Settled)
    (ht₀ : b₀.rank.val + 1 = ceilHalf n →
      (if b₁.rank.val + 1 = n then b₀.timer - 1 else b₀.timer) ≠ 0)
    (ht₁ : b₁.rank.val + 1 = ceilHalf n →
      (if b₀.rank.val + 1 = n then b₁.timer - 1 else b₁.timer) ≠ 0) :
    (phase4_propagate n Rmax b₀ b₁).1.role = .Settled ∧
    (phase4_propagate n Rmax b₀ b₁).2.role = .Settled := by
  unfold phase4_propagate
  by_cases hmed₀ : b₀.rank.val + 1 = ceilHalf n
  · simp [hmed₀]
    by_cases hmax₁ : b₁.rank.val + 1 = n
    · simp [hmax₁]
      have hnz : b₀.timer - 1 ≠ 0 := by simpa [hmax₁] using ht₀ hmed₀
      by_cases hreset : b₀.timer - 1 = 0 ∧ b₀.answer ≠ b₁.answer
      · exact False.elim (hnz hreset.1)
      · simp [hreset, h₀, h₁]
    · simp [hmax₁]
      have hnz : b₀.timer ≠ 0 := by simpa [hmax₁] using ht₀ hmed₀
      by_cases hreset : b₀.timer = 0 ∧ b₀.answer ≠ b₁.answer
      · exact False.elim (hnz hreset.1)
      · simp [hreset, h₀, h₁]
  · simp [hmed₀]
    by_cases hmed₁ : b₁.rank.val + 1 = ceilHalf n
    · simp [hmed₁]
      by_cases hmax₀ : b₀.rank.val + 1 = n
      · simp [hmax₀]
        have hnz : b₁.timer - 1 ≠ 0 := by simpa [hmax₀] using ht₁ hmed₁
        by_cases hreset : b₁.timer - 1 = 0 ∧ b₁.answer ≠ b₀.answer
        · exact False.elim (hnz hreset.1)
        · simp [hreset, h₀, h₁]
      · simp [hmax₀]
        have hnz : b₁.timer ≠ 0 := by simpa [hmax₀] using ht₁ hmed₁
        by_cases hreset : b₁.timer = 0 ∧ b₁.answer ≠ b₀.answer
        · exact False.elim (hnz hreset.1)
        · simp [hreset, h₀, h₁]
    · simp [hmed₁, h₀, h₁]

lemma transitionPEM_recruit_ba_rank_children
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {a b : AgentState n} {x₀ x₁ : Opinion}
    (ha : a.role = .Unsettled)
    (hb : b.role = .Settled)
    (hb_children : b.children < 2)
    (h_valid : 2 * b.rank.val + b.children + 1 < n) :
    let t := transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
      ((a, x₀), (b, x₁))
    t.1.rank.val = 2 * b.rank.val + b.children + 1 ∧
    t.1.children = 0 ∧
    t.2.rank = b.rank ∧
    t.2.children = b.children + 1 := by
  have hrd :=
    rankDeltaOSSR_recruit_ba (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      (hn := hn) (a := a) (b := b) ha hb hb_children h_valid
  let p := transitionPEM_prePhase4 n Rmax (rankDeltaOSSR Rmax Emax Dmax hn) a b x₀ x₁
  have hpre := transitionPEM_prePhase4_structural
    (trank := Rmax) (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
    (s₀ := a) (s₁ := b) (x₀ := x₀) (x₁ := x₁)
  have hp₁_role : p.1.role = .Settled := by
    simpa [p, hrd] using hpre.1
  have hp₂_role : p.2.role = .Settled := by
    simpa [p, hrd, hb] using hpre.2.2.2.2.2.2.1
  have hp₁_rank : p.1.rank = ⟨2 * b.rank.val + b.children + 1, h_valid⟩ := by
    simpa [p, hrd] using hpre.2.2.1
  have hp₁_children : p.1.children = 0 := by
    simpa [p, hrd] using hpre.2.2.2.1
  have hp₂_rank : p.2.rank = b.rank := by
    simpa [p, hrd] using hpre.2.2.2.2.2.2.2.2.1
  have hp₂_children : p.2.children = b.children + 1 := by
    simpa [p, hrd] using hpre.2.2.2.2.2.2.2.2.2.1
  have hp₂_lt_hp₁ : p.2.rank.val < p.1.rank.val := by
    have hnat : b.rank.val < 2 * b.rank.val + b.children + 1 := by omega
    simpa [hp₁_rank, hp₂_rank] using hnat
  have hnot_swap : ¬(p.1.rank < p.2.rank ∧ x₀ = .B ∧ x₁ = .A) := by
    intro h
    have hv : p.1.rank.val < p.2.rank.val := by
      exact h.1
    exact (Nat.not_lt_of_ge (Nat.le_of_lt hp₂_lt_hp₁)) hv
  let q := phase4_decide n p.1 p.2 x₀ x₁
  have hdec := phase4_decide_preserves_role_rank_children
    (n := n) (b₀ := p.1) (b₁ := p.2) (x₀ := x₀) (x₁ := x₁)
  have hprop := phase4_propagate_preserves_rank_children
    (n := n) (Rmax := Rmax) (b₀ := q.1) (b₁ := q.2)
  have ht :
      transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) ((a, x₀), (b, x₁)) =
        phase4_propagate n Rmax q.1 q.2 := by
    simp [transitionPEM, p, transitionPEM_phase4, hp₁_role, hp₂_role,
      phase4_swap_eq_of_not_swap hnot_swap, q]
  rw [ht]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hprop.1, hdec.2.1, hp₁_rank]
  · rw [hprop.2.1, hdec.2.2.1, hp₁_children]
  · rw [hprop.2.2.1, hdec.2.2.2.2.1, hp₂_rank]
  · rw [hprop.2.2.2, hdec.2.2.2.2.2, hp₂_children]

set_option maxHeartbeats 1600000 in
/-- **prePhase4 of a recruit `(child Unsettled, parent Settled)` pair is
answer-inert.**  `rankDeltaOSSR_recruit_ba` keeps both `.answer` fields;
the prePhase4 phi-wipe fires only on a *fresh* `Resetting` (neither
endpoint becomes `Resetting`: both are `Settled`), the timer-init only
touches `timer`, and the phi-spread guard needs both `Resetting` (false
here).  Hence both prePhase4 output answers equal the inputs. -/
lemma prePhase4_recruit_ba_answer_preserved
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {a b : AgentState n} {x₀ x₁ : Opinion}
    (ha : a.role = .Unsettled)
    (hb : b.role = .Settled)
    (hb_children : b.children < 2)
    (h_valid : 2 * b.rank.val + b.children + 1 < n) :
    (transitionPEM_prePhase4 n Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
        a b x₀ x₁).1.answer = a.answer ∧
    (transitionPEM_prePhase4 n Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
        a b x₀ x₁).2.answer = b.answer := by
  have hrd :=
    rankDeltaOSSR_recruit_ba (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      (hn := hn) (a := a) (b := b) ha hb hb_children h_valid
  -- The recruit `rankDeltaOSSR` output (explicit via `hrd`): child Settled
  -- with answer `a.answer`, parent Settled with answer `b.answer`.  No
  -- phi-wipe (both outputs `.Settled`, not `.Resetting`), timer-init only
  -- modifies `.timer`, phi-spread needs both `.Resetting`.
  unfold transitionPEM_prePhase4
  rw [hrd]
  simp only []
  refine ⟨?_, ?_⟩ <;>
    · split_ifs <;>
        simp_all [AgentState.answer]

set_option maxHeartbeats 1600000 in
/-- **A recruit `(child Unsettled, parent Settled)` `transitionPEM` step
is answer-inert when neither resulting agent lands at a median decision
rank.**  prePhase4 preserves answers (`prePhase4_recruit_ba_answer_
preserved`); both agents are `Settled` so Phase 4 fires, but
`phase4_swap` only reorders, `phase4_decide` writes `.answer` *only* at a
median rank (none here), and `phase4_propagate` only changes `timer`/role
unless an agent is at the median rank (none here).  Hence both output
answers equal the input answers. -/
lemma transitionPEM_recruit_ba_answer_inert_of_no_median
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {a b : AgentState n} {x₀ x₁ : Opinion}
    (ha : a.role = .Unsettled)
    (hb : b.role = .Settled)
    (hb_children : b.children < 2)
    (h_valid : 2 * b.rank.val + b.children + 1 < n)
    (hchild_no_med : 2 * b.rank.val + b.children + 1 + 1 ≠ ceilHalf n)
    (hchild_no_lower : 2 * b.rank.val + b.children + 1 + 1 ≠ n / 2)
    (hchild_no_upper : 2 * b.rank.val + b.children + 1 + 1 ≠ n / 2 + 1)
    (hpar_no_med : b.rank.val + 1 ≠ ceilHalf n)
    (hpar_no_lower : b.rank.val + 1 ≠ n / 2)
    (hpar_no_upper : b.rank.val + 1 ≠ n / 2 + 1) :
    let t := transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
      ((a, x₀), (b, x₁))
    t.1.answer = a.answer ∧ t.2.answer = b.answer := by
  have hrd :=
    rankDeltaOSSR_recruit_ba (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      (hn := hn) (a := a) (b := b) ha hb hb_children h_valid
  let p := transitionPEM_prePhase4 n Rmax (rankDeltaOSSR Rmax Emax Dmax hn) a b x₀ x₁
  have hpre := transitionPEM_prePhase4_structural
    (trank := Rmax) (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
    (s₀ := a) (s₁ := b) (x₀ := x₀) (x₁ := x₁)
  have hp_ans := prePhase4_recruit_ba_answer_preserved
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    (a := a) (b := b) (x₀ := x₀) (x₁ := x₁) ha hb hb_children h_valid
  have hp₁_role : p.1.role = .Settled := by
    simpa [p, hrd] using hpre.1
  have hp₂_role : p.2.role = .Settled := by
    simpa [p, hrd, hb] using hpre.2.2.2.2.2.2.1
  have hp₁_rank : p.1.rank = ⟨2 * b.rank.val + b.children + 1, h_valid⟩ := by
    simpa [p, hrd] using hpre.2.2.1
  have hp₂_rank : p.2.rank = b.rank := by
    simpa [p, hrd] using hpre.2.2.2.2.2.2.2.2.1
  have hp₂_lt_hp₁ : p.2.rank.val < p.1.rank.val := by
    have hnat : b.rank.val < 2 * b.rank.val + b.children + 1 := by omega
    simpa [hp₁_rank, hp₂_rank] using hnat
  have hnot_swap : ¬(p.1.rank < p.2.rank ∧ x₀ = .B ∧ x₁ = .A) := by
    intro h
    exact (Nat.not_lt_of_ge (Nat.le_of_lt hp₂_lt_hp₁)) h.1
  -- `phase4_decide` is the identity: neither rank is a median decision rank.
  have hp₁_rankv : p.1.rank.val = 2 * b.rank.val + b.children + 1 := by
    rw [hp₁_rank]
  have hp₂_rankv : p.2.rank.val = b.rank.val := by
    rw [hp₂_rank]
  -- Restate the no-median guards in terms of `p`'s ranks.
  have hc_med : p.1.rank.val + 1 ≠ ceilHalf n := by
    rw [hp₁_rankv]; exact hchild_no_med
  have hc_low : p.1.rank.val + 1 ≠ n / 2 := by
    rw [hp₁_rankv]; exact hchild_no_lower
  have hc_up : p.1.rank.val + 1 ≠ n / 2 + 1 := by
    rw [hp₁_rankv]; exact hchild_no_upper
  have hpar_med : p.2.rank.val + 1 ≠ ceilHalf n := by
    rw [hp₂_rankv]; exact hpar_no_med
  have hpar_low : p.2.rank.val + 1 ≠ n / 2 := by
    rw [hp₂_rankv]; exact hpar_no_lower
  have hpar_up : p.2.rank.val + 1 ≠ n / 2 + 1 := by
    rw [hp₂_rankv]; exact hpar_no_upper
  -- The four median-decision guards of `phase4_decide` are all false.
  have hg_even1 : ¬ (p.1.rank.val + 1 = n / 2 ∧ p.2.rank.val + 1 = n / 2 + 1) := by
    rintro ⟨h, _⟩; exact hc_low h
  have hg_even2 : ¬ (p.2.rank.val + 1 = n / 2 ∧ p.1.rank.val + 1 = n / 2 + 1) := by
    rintro ⟨h, _⟩; exact hpar_low h
  let q := phase4_decide n p.1 p.2 x₀ x₁
  have hdec_id : q = (p.1, p.2) := by
    show phase4_decide n p.1 p.2 x₀ x₁ = (p.1, p.2)
    unfold phase4_decide
    by_cases hpar : n % 2 = 0
    · rw [if_pos hpar, if_neg hg_even1, if_neg hg_even2]
    · rw [if_neg hpar, if_neg hc_med, if_neg hpar_med]
  have hq₁ : q.1 = p.1 := by rw [hdec_id]
  have hq₂ : q.2 = p.2 := by rw [hdec_id]
  -- `phase4_propagate` only touches `timer`/role unless at the (ceilHalf)
  -- median rank; neither endpoint is there.
  have hprop_ans :
      (phase4_propagate n Rmax q.1 q.2).1.answer = p.1.answer ∧
      (phase4_propagate n Rmax q.1 q.2).2.answer = p.2.answer := by
    rw [hq₁, hq₂]
    unfold phase4_propagate
    rw [if_neg hc_med, if_neg hpar_med]
    exact ⟨rfl, rfl⟩
  have ht :
      transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
          ((a, x₀), (b, x₁)) =
        phase4_propagate n Rmax q.1 q.2 := by
    simp [transitionPEM, p, transitionPEM_phase4, hp₁_role, hp₂_role,
      phase4_swap_eq_of_not_swap hnot_swap, q]
  refine ⟨?_, ?_⟩
  · rw [ht, hprop_ans.1]; exact hp_ans.1
  · rw [ht, hprop_ans.2]; exact hp_ans.2

lemma prePhase4_recruit_ba_child_timer_of_median
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {a b : AgentState n} {x₀ x₁ : Opinion}
    (ha : a.role = .Unsettled)
    (hb : b.role = .Settled)
    (hb_children : b.children < 2)
    (h_valid : 2 * b.rank.val + b.children + 1 < n) :
    (transitionPEM_prePhase4 n Rmax (rankDeltaOSSR Rmax Emax Dmax hn) a b x₀ x₁).1.rank.val + 1 =
      ceilHalf n →
    (transitionPEM_prePhase4 n Rmax (rankDeltaOSSR Rmax Emax Dmax hn) a b x₀ x₁).1.timer =
      7 * (Rmax + 4) := by
    intro hmed
    have hrd :=
      rankDeltaOSSR_recruit_ba (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        (hn := hn) (a := a) (b := b) ha hb hb_children h_valid
    unfold transitionPEM_prePhase4 at hmed ⊢
    rw [hrd] at hmed ⊢
    simp [ha, hb] at hmed ⊢
    by_cases h : 2 * b.rank.val + b.children + 1 + 1 = ceilHalf n
    · simp [h]
    · have h' : 2 * b.rank.val + b.children + 1 + 1 = ceilHalf n := by
        simpa [h] using hmed
      exact False.elim (h h')

lemma prePhase4_recruit_ba_parent_timer
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {a b : AgentState n} {x₀ x₁ : Opinion}
    (ha : a.role = .Unsettled)
    (hb : b.role = .Settled)
    (hb_children : b.children < 2)
    (h_valid : 2 * b.rank.val + b.children + 1 < n) :
    (transitionPEM_prePhase4 n Rmax (rankDeltaOSSR Rmax Emax Dmax hn) a b x₀ x₁).2.timer =
      b.timer := by
    have hrd :=
      rankDeltaOSSR_recruit_ba (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        (hn := hn) (a := a) (b := b) ha hb hb_children h_valid
    unfold transitionPEM_prePhase4
    simp [hrd, ha, hb]

set_option maxHeartbeats 8000000 in
lemma transitionPEM_recruit_ba_settled_rank_children
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {a b : AgentState n} {x₀ x₁ : Opinion}
    (ha : a.role = .Unsettled)
    (hb : b.role = .Settled)
    (hb_children : b.children < 2)
    (h_valid : 2 * b.rank.val + b.children + 1 < n)
    (ht_parent : b.rank.val + 1 = ceilHalf n →
      (if 2 * b.rank.val + b.children + 1 + 1 = n then b.timer - 1 else b.timer) ≠ 0) :
    let t := transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
      ((a, x₀), (b, x₁))
    t.1.role = .Settled ∧ t.2.role = .Settled ∧
    t.1.rank.val = 2 * b.rank.val + b.children + 1 ∧
    t.1.children = 0 ∧
    t.2.rank = b.rank ∧
    t.2.children = b.children + 1 := by
  have hstruct :=
    transitionPEM_recruit_ba_rank_children
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      (a := a) (b := b) (x₀ := x₀) (x₁ := x₁)
      ha hb hb_children h_valid
  let p := transitionPEM_prePhase4 n Rmax (rankDeltaOSSR Rmax Emax Dmax hn) a b x₀ x₁
  have hrd :=
    rankDeltaOSSR_recruit_ba (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      (hn := hn) (a := a) (b := b) ha hb hb_children h_valid
  have hpre := transitionPEM_prePhase4_structural
    (trank := Rmax) (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
    (s₀ := a) (s₁ := b) (x₀ := x₀) (x₁ := x₁)
  have hp₁_role : p.1.role = .Settled := by
    simpa [p, hrd] using hpre.1
  have hp₂_role : p.2.role = .Settled := by
    simpa [p, hrd, hb] using hpre.2.2.2.2.2.2.1
  have hp₁_rank : p.1.rank = ⟨2 * b.rank.val + b.children + 1, h_valid⟩ := by
    simpa [p, hrd] using hpre.2.2.1
  have hp₂_rank : p.2.rank = b.rank := by
    simpa [p, hrd] using hpre.2.2.2.2.2.2.2.2.1
  have hp₂_lt_hp₁ : p.2.rank.val < p.1.rank.val := by
    have hnat : b.rank.val < 2 * b.rank.val + b.children + 1 := by omega
    simpa [hp₁_rank, hp₂_rank] using hnat
  have hnot_swap : ¬(p.1.rank < p.2.rank ∧ x₀ = .B ∧ x₁ = .A) := by
    intro h
    exact (Nat.not_lt_of_ge (Nat.le_of_lt hp₂_lt_hp₁)) h.1
  let q := phase4_decide n p.1 p.2 x₀ x₁
  have hdec := phase4_decide_preserves_role_rank_children
    (n := n) (b₀ := p.1) (b₁ := p.2) (x₀ := x₀) (x₁ := x₁)
  have hdt := phase4_decide_preserves_timer
    (n := n) (b₀ := p.1) (b₁ := p.2) (x₀ := x₀) (x₁ := x₁)
  have hq₁_role : q.1.role = .Settled := by
    rw [hdec.1, hp₁_role]
  have hq₂_role : q.2.role = .Settled := by
    rw [hdec.2.2.2.1, hp₂_role]
  have ht₀ : q.1.rank.val + 1 = ceilHalf n →
      (if q.2.rank.val + 1 = n then q.1.timer - 1 else q.1.timer) ≠ 0 := by
    intro hmed
    have hparent_not_max : q.2.rank.val + 1 ≠ n := by
      rw [hdec.2.2.2.2.1, hp₂_rank]
      omega
    simp [hparent_not_max]
    have hpmed : p.1.rank.val + 1 = ceilHalf n := by
      rwa [hdec.2.1] at hmed
    have hp_timer :=
      prePhase4_recruit_ba_child_timer_of_median
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        (a := a) (b := b) (x₀ := x₀) (x₁ := x₁)
        ha hb hb_children h_valid hpmed
    rw [hdt.1, hp_timer]
    omega
  have ht₁ : q.2.rank.val + 1 = ceilHalf n →
      (if q.1.rank.val + 1 = n then q.2.timer - 1 else q.2.timer) ≠ 0 := by
    intro hmed
    have hpmed : b.rank.val + 1 = ceilHalf n := by
      rw [hdec.2.2.2.2.1, hp₂_rank] at hmed
      exact hmed
    have hp_timer :=
      prePhase4_recruit_ba_parent_timer
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        (a := a) (b := b) (x₀ := x₀) (x₁ := x₁)
        ha hb hb_children h_valid
    rw [hdt.2, hp_timer, hdec.2.1, hp₁_rank]
    exact ht_parent hpmed
  have hroles :=
    phase4_propagate_settled_of_positive_median_timers
      (n := n) (Rmax := Rmax) (b₀ := q.1) (b₁ := q.2)
      hq₁_role hq₂_role ht₀ ht₁
  have ht :
      transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) ((a, x₀), (b, x₁)) =
        phase4_propagate n Rmax q.1 q.2 := by
    simp [transitionPEM, p, transitionPEM_phase4, hp₁_role, hp₂_role,
      phase4_swap_eq_of_not_swap hnot_swap, q]
  rw [ht]
  refine ⟨hroles.1, hroles.2, ?_, ?_, ?_, ?_⟩
  · simpa [ht] using hstruct.1
  · simpa [ht] using hstruct.2.1
  · simpa [ht] using hstruct.2.2.1
  · simpa [ht] using hstruct.2.2.2

lemma transitionPEM_recruit_ba_child_timer_ge_three
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {a b : AgentState n} {x₀ x₁ : Opinion}
    (ha : a.role = .Unsettled)
    (hb : b.role = .Settled)
    (hb_children : b.children < 2)
    (h_valid : 2 * b.rank.val + b.children + 1 < n)
    (hmed : 2 * b.rank.val + b.children + 1 + 1 = ceilHalf n) :
    3 ≤
      (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
        ((a, x₀), (b, x₁))).1.timer := by
  have hrd :=
    rankDeltaOSSR_recruit_ba (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      (hn := hn) (a := a) (b := b) ha hb hb_children h_valid
  let p := transitionPEM_prePhase4 n Rmax (rankDeltaOSSR Rmax Emax Dmax hn) a b x₀ x₁
  have hpre := transitionPEM_prePhase4_structural
    (trank := Rmax) (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
    (s₀ := a) (s₁ := b) (x₀ := x₀) (x₁ := x₁)
  have hp₁_role : p.1.role = .Settled := by
    simpa [p, hrd] using hpre.1
  have hp₂_role : p.2.role = .Settled := by
    simpa [p, hrd, hb] using hpre.2.2.2.2.2.2.1
  have hp₁_rank : p.1.rank = ⟨2 * b.rank.val + b.children + 1, h_valid⟩ := by
    simpa [p, hrd] using hpre.2.2.1
  have hp₂_rank : p.2.rank = b.rank := by
    simpa [p, hrd] using hpre.2.2.2.2.2.2.2.2.1
  have hp₂_lt_hp₁ : p.2.rank.val < p.1.rank.val := by
    have hnat : b.rank.val < 2 * b.rank.val + b.children + 1 := by omega
    simpa [hp₁_rank, hp₂_rank] using hnat
  have hnot_swap : ¬(p.1.rank < p.2.rank ∧ x₀ = .B ∧ x₁ = .A) := by
    intro h
    exact (Nat.not_lt_of_ge (Nat.le_of_lt hp₂_lt_hp₁)) h.1
  let q := phase4_decide n p.1 p.2 x₀ x₁
  have hdec := phase4_decide_preserves_role_rank_children
    (n := n) (b₀ := p.1) (b₁ := p.2) (x₀ := x₀) (x₁ := x₁)
  have hdt := phase4_decide_preserves_timer
    (n := n) (b₀ := p.1) (b₁ := p.2) (x₀ := x₀) (x₁ := x₁)
  have hq₁_med : q.1.rank.val + 1 = ceilHalf n := by
    rw [hdec.2.1, hp₁_rank]
    exact hmed
  have hq₂_not_max : q.2.rank.val + 1 ≠ n := by
    rw [hdec.2.2.2.2.1, hp₂_rank]
    omega
  have hp_timer :=
    prePhase4_recruit_ba_child_timer_of_median
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      (a := a) (b := b) (x₀ := x₀) (x₁ := x₁)
      ha hb hb_children h_valid (by simpa [p, hp₁_rank] using hmed)
  have ht :
      transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) ((a, x₀), (b, x₁)) =
        phase4_propagate n Rmax q.1 q.2 := by
    simp [transitionPEM, p, transitionPEM_phase4, hp₁_role, hp₂_role,
      phase4_swap_eq_of_not_swap hnot_swap, q]
  rw [ht]
  unfold phase4_propagate
  simp [hq₁_med, hq₂_not_max]
  split_ifs <;> rw [hdt.1, hp_timer] <;> omega

lemma transitionPEM_recruit_ba_parent_timer_bounds
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {a b : AgentState n} {x₀ x₁ : Opinion}
    (ha : a.role = .Unsettled)
    (hb : b.role = .Settled)
    (hb_children : b.children < 2)
    (h_valid : 2 * b.rank.val + b.children + 1 < n)
    (htimer : b.rank.val + 1 = ceilHalf n → 3 ≤ b.timer) :
    (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
      ((a, x₀), (b, x₁))).2.rank.val + 1 = ceilHalf n →
      2 ≤
          (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
            ((a, x₀), (b, x₁))).2.timer ∧
        (2 * b.rank.val + b.children + 1 + 1 < n →
          3 ≤
            (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
              ((a, x₀), (b, x₁))).2.timer) := by
  intro hmed_t
  have hrd :=
    rankDeltaOSSR_recruit_ba (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      (hn := hn) (a := a) (b := b) ha hb hb_children h_valid
  let p := transitionPEM_prePhase4 n Rmax (rankDeltaOSSR Rmax Emax Dmax hn) a b x₀ x₁
  have hpre := transitionPEM_prePhase4_structural
    (trank := Rmax) (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
    (s₀ := a) (s₁ := b) (x₀ := x₀) (x₁ := x₁)
  have hp₁_role : p.1.role = .Settled := by
    simpa [p, hrd] using hpre.1
  have hp₂_role : p.2.role = .Settled := by
    simpa [p, hrd, hb] using hpre.2.2.2.2.2.2.1
  have hp₁_rank : p.1.rank = ⟨2 * b.rank.val + b.children + 1, h_valid⟩ := by
    simpa [p, hrd] using hpre.2.2.1
  have hp₂_rank : p.2.rank = b.rank := by
    simpa [p, hrd] using hpre.2.2.2.2.2.2.2.2.1
  have hp₂_lt_hp₁ : p.2.rank.val < p.1.rank.val := by
    have hnat : b.rank.val < 2 * b.rank.val + b.children + 1 := by omega
    simpa [hp₁_rank, hp₂_rank] using hnat
  have hnot_swap : ¬(p.1.rank < p.2.rank ∧ x₀ = .B ∧ x₁ = .A) := by
    intro h
    exact (Nat.not_lt_of_ge (Nat.le_of_lt hp₂_lt_hp₁)) h.1
  let q := phase4_decide n p.1 p.2 x₀ x₁
  have hdec := phase4_decide_preserves_role_rank_children
    (n := n) (b₀ := p.1) (b₁ := p.2) (x₀ := x₀) (x₁ := x₁)
  have hdt := phase4_decide_preserves_timer
    (n := n) (b₀ := p.1) (b₁ := p.2) (x₀ := x₀) (x₁ := x₁)
  have hp_timer :=
    prePhase4_recruit_ba_parent_timer
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      (a := a) (b := b) (x₀ := x₀) (x₁ := x₁)
      ha hb hb_children h_valid
  have hq₂_timer : q.2.timer = b.timer := by
    rw [hdt.2, hp_timer]
  have hq₁_rank : q.1.rank = ⟨2 * b.rank.val + b.children + 1, h_valid⟩ := by
    rw [hdec.2.1, hp₁_rank]
  have ht :
      transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) ((a, x₀), (b, x₁)) =
        phase4_propagate n Rmax q.1 q.2 := by
    simp [transitionPEM, p, transitionPEM_phase4, hp₁_role, hp₂_role,
      phase4_swap_eq_of_not_swap hnot_swap, q]
  have hq₂_med : q.2.rank.val + 1 = ceilHalf n := by
    rw [ht] at hmed_t
    unfold phase4_propagate at hmed_t
    by_cases hq₁_med : q.1.rank.val + 1 = ceilHalf n
    · simp [hq₁_med] at hmed_t
      split_ifs at hmed_t <;> simpa using hmed_t
    · simp [hq₁_med] at hmed_t
      by_cases hq₂_med : q.2.rank.val + 1 = ceilHalf n
      · exact hq₂_med
      · simp [hq₂_med] at hmed_t
  have hb_med : b.rank.val + 1 = ceilHalf n := by
    rw [hdec.2.2.2.2.1, hp₂_rank] at hq₂_med
    exact hq₂_med
  have hq₁_not_med : q.1.rank.val + 1 ≠ ceilHalf n := by
    rw [hdec.2.1, hp₁_rank]
    omega
  have hparent_timer : 3 ≤ b.timer := htimer hb_med
  rw [ht]
  unfold phase4_propagate
  simp [hq₁_not_med, hq₂_med]
  by_cases hmax : q.1.rank.val + 1 = n
  · simp [hmax]
    split_ifs <;> simp [hq₂_timer] <;> refine ⟨by omega, ?_⟩
    · intro hlt
      have hmax_child : 2 * b.rank.val + b.children + 1 + 1 = n := by
        simpa [hq₁_rank] using hmax
      omega
    · intro hlt
      have hmax_child : 2 * b.rank.val + b.children + 1 + 1 = n := by
        simpa [hq₁_rank] using hmax
      omega
  · simp [hmax]
    split_ifs <;> simp [hq₂_timer] <;> exact ⟨by omega, by intro hlt; omega⟩

theorem heapPrefix_recruit_step [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n} {k : ℕ}
    (hk_pos : 1 ≤ k) (hk_lt : k < n)
    (C : Config (AgentState n) Opinion n)
    (hHeap : HeapPrefix C k) (hTimer : SettledMedianTimerStrong C) :
    ∃ parent child : Fin n,
      let C' := runPairs (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C [(parent, child)]
      HeapPrefix C' (k + 1) ∧ SettledMedianTimerGood C' ∧
        (k + 1 < n → SettledMedianTimerStrong C') := by
  classical
  let pr := heapParent k
  have hpr_lt : pr < k := by
    simpa [pr] using heapParent_lt_self hk_pos
  rcases hHeap with ⟨hkn, hRankLt, hUnique, hRoles, hChildren⟩
  obtain ⟨v, hv_prop, hv_unique⟩ := hUnique pr hpr_lt
  have hv_settled : (C v).1.role = .Settled := hv_prop.1
  have hv_rank : (C v).1.rank.val = pr := hv_prop.2
  have hHeap_old : HeapPrefix C k :=
    ⟨hkn, hRankLt, hUnique, hRoles, hChildren⟩
  have hExistsUnsettled : ∃ u : Fin n, (C u).1.role = .Unsettled := by
    by_contra hnone
    push_neg at hnone
    have hall : ∀ w : Fin n, (C w).1.role = .Settled := by
      intro w
      rcases hRoles w with hs | hu
      · exact hs
      · exact False.elim (hnone w hu)
    exact heapPrefix_no_unsettled_contradiction hk_lt hHeap_old hall
  obtain ⟨u, hu_unsettled⟩ := hExistsUnsettled
  have huv : u ≠ v := by
    intro huv
    subst u
    rw [hv_settled] at hu_unsettled
    cases hu_unsettled
  have hv_children_old : (C v).1.children = heapChildIndex k := by
    have hchild := hChildren v hv_settled
    rw [hchild, hv_rank]
    exact heapChildrenBefore_parent hk_pos
  have hv_children_lt : (C v).1.children < 2 := by
    rw [hv_children_old]
    exact heapChildIndex_lt_two k
  have h_valid : 2 * (C v).1.rank.val + (C v).1.children + 1 < n := by
    rw [hv_rank, hv_children_old]
    have hp := heap_parent_rank hk_pos
    omega
  refine ⟨u, v, ?_⟩
  let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  let C' : Config (AgentState n) Opinion n := runPairs P C [(u, v)]
  have ht_parent :
      (C v).1.rank.val + 1 = ceilHalf n →
      (if 2 * (C v).1.rank.val + (C v).1.children + 1 + 1 = n
       then (C v).1.timer - 1 else (C v).1.timer) ≠ 0 := by
    intro hmed
    have ht := hTimer v hv_settled hmed
    split_ifs <;> omega
  have hstep :=
    transitionPEM_recruit_ba_settled_rank_children
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      (a := (C u).1) (b := (C v).1)
      (x₀ := (C u).2) (x₁ := (C v).2)
      hu_unsettled hv_settled hv_children_lt h_valid ht_parent
  have hfst :
      (C' u).1 =
        (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
          (C u, C v)).1 := by
    simpa [C', P, protocolPEM] using Config.step_fst_state P C huv
  have hsnd :
      (C' v).1 =
        (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
          (C u, C v)).2 := by
    simpa [C', P, protocolPEM] using Config.step_snd_state P C huv huv.symm
  have hother (w : Fin n) (hwu : w ≠ u) (hwv : w ≠ v) : C' w = C w := by
    simp [C', P, runPairs, Config.step, huv, hwu, hwv]
  have hu_settled' : (C' u).1.role = .Settled := by
    rw [congrArg AgentState.role hfst]
    exact hstep.1
  have hv_settled' : (C' v).1.role = .Settled := by
    rw [congrArg AgentState.role hsnd]
    exact hstep.2.1
  have hu_rank' : (C' u).1.rank.val = k := by
    rw [congrArg AgentState.rank hfst]
    have hr := hstep.2.2.1
    rw [hr, hv_rank, hv_children_old]
    exact heap_parent_rank hk_pos
  have hu_children' : (C' u).1.children = 0 := by
    rw [congrArg AgentState.children hfst]
    exact hstep.2.2.2.1
  have hv_rank' : (C' v).1.rank.val = pr := by
    rw [congrArg AgentState.rank hsnd]
    rw [hstep.2.2.2.2.1]
    exact hv_rank
  have hv_children' : (C' v).1.children = heapChildIndex k + 1 := by
    rw [congrArg AgentState.children hsnd]
    rw [hstep.2.2.2.2.2, hv_children_old]
  have hHeap' : HeapPrefix C' (k + 1) := by
    refine ⟨by omega, ?_, ?_, ?_, ?_⟩
    · intro w hw_settled
      by_cases hwu : w = u
      · subst w
        rw [hu_rank']
        omega
      · by_cases hwv : w = v
        · subst w
          rw [hv_rank']
          omega
        · have hw_old_settled : (C w).1.role = .Settled := by
            have hw_eq := hother w hwu hwv
            simpa [hw_eq] using hw_settled
          have hr := hRankLt w hw_old_settled
          have hw_eq := hother w hwu hwv
          rw [hw_eq]
          omega
    · intro r hr
      by_cases hrk : r = k
      · subst r
        refine ⟨u, ⟨hu_settled', hu_rank'⟩, ?_⟩
        intro w hw
        by_cases hwu : w = u
        · exact hwu
        · by_cases hwv : w = v
          · subst w
            have hpr_ne : pr ≠ k := by omega
            exact False.elim (hpr_ne (by simpa [hv_rank'] using hw.2))
          · have hw_eq := hother w hwu hwv
            have hw_old_settled : (C w).1.role = .Settled := by
              simpa [hw_eq] using hw.1
            have hw_old_lt := hRankLt w hw_old_settled
            rw [hw_eq] at hw
            omega
      · have hr_lt_k : r < k := by omega
        obtain ⟨z, hz, hz_unique⟩ := hUnique r hr_lt_k
        have hzu : z ≠ u := by
          intro hzu
          subst z
          rw [hu_unsettled] at hz
          cases hz.1
        by_cases hzv : z = v
        · subst z
          refine ⟨v, ⟨hv_settled', by
            rw [hv_rank']
            rw [hv_rank] at hz
            exact hz.2⟩, ?_⟩
          intro w hw
          by_cases hwu : w = u
          · subst w
            omega
          · by_cases hwv : w = v
            · exact hwv
            · have hw_eq := hother w hwu hwv
              have hw_old : (C w).1.role = .Settled ∧ (C w).1.rank.val = r := by
                rw [hw_eq] at hw
                exact hw
              exact hz_unique w hw_old
        · refine ⟨z, ?_, ?_⟩
          · have hz_eq := hother z hzu hzv
            simpa [hz_eq] using hz
          · intro w hw
            by_cases hwu : w = u
            · subst w
              omega
            · by_cases hwv : w = v
              · subst w
                have hv_old : (C v).1.role = .Settled ∧ (C v).1.rank.val = r := by
                  have hpr_r : pr = r := by simpa [hv_rank'] using hw.2
                  exact ⟨hv_settled, by rw [hv_rank]; exact hpr_r⟩
                exact hz_unique v hv_old
              · have hw_eq := hother w hwu hwv
                have hw_old : (C w).1.role = .Settled ∧ (C w).1.rank.val = r := by
                  rw [hw_eq] at hw
                  exact hw
                exact hz_unique w hw_old
    · intro w
      by_cases hwu : w = u
      · subst w
        exact Or.inl hu_settled'
      · by_cases hwv : w = v
        · subst w
          exact Or.inl hv_settled'
        · have hw_eq := hother w hwu hwv
          simpa [hw_eq] using hRoles w
    · intro w hw_settled
      by_cases hwu : w = u
      · subst w
        rw [hu_children', hu_rank']
        exact (heapChildrenBefore_self_succ k).symm
      · by_cases hwv : w = v
        · subst w
          rw [hv_children', hv_rank']
          simpa [pr] using (heapChildrenBefore_succ_parent hk_pos).symm
        · have hw_eq := hother w hwu hwv
          have hw_old_settled : (C w).1.role = .Settled := by
            simpa [hw_eq] using hw_settled
          have hchild_old := hChildren w hw_old_settled
          have hr_ne : (C w).1.rank.val ≠ pr := by
            intro hr_eq
            have hw_old : (C w).1.role = .Settled ∧ (C w).1.rank.val = pr :=
              ⟨hw_old_settled, hr_eq⟩
            exact hwv (hv_unique w hw_old)
          rw [hw_eq, hchild_old]
          exact (heapChildrenBefore_succ_ne_parent hr_ne).symm
  have hTimerGood' : SettledMedianTimerGood C' := by
    intro μ hμ_settled hμ_med
    by_cases hμu : μ = u
    · subst μ
      rw [congrArg AgentState.timer hfst]
      have hchild_med :
          2 * (C v).1.rank.val + (C v).1.children + 1 + 1 = ceilHalf n := by
        rw [hu_rank'] at hμ_med
        rw [hv_rank, hv_children_old]
        have hp := heap_parent_rank hk_pos
        omega
      have hge3 :=
        transitionPEM_recruit_ba_child_timer_ge_three
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          (a := (C u).1) (b := (C v).1)
          (x₀ := (C u).2) (x₁ := (C v).2)
          hu_unsettled hv_settled hv_children_lt h_valid hchild_med
      exact Nat.le_trans (show 2 ≤ 3 by omega) (by simpa using hge3)
    · by_cases hμv : μ = v
      · subst μ
        rw [congrArg AgentState.timer hsnd]
        have hbounds :=
          transitionPEM_recruit_ba_parent_timer_bounds
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            (a := (C u).1) (b := (C v).1)
            (x₀ := (C u).2) (x₁ := (C v).2)
            hu_unsettled hv_settled hv_children_lt h_valid
            (fun hmed => hTimer v hv_settled hmed)
        have hmed_t :
            (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
              (C u, C v)).2.rank.val + 1 = ceilHalf n := by
          simpa [hsnd] using hμ_med
        exact (hbounds hmed_t).1
      · have hμ_eq := hother μ hμu hμv
        have hμ_old_settled : (C μ).1.role = .Settled := by
          simpa [hμ_eq] using hμ_settled
        have hμ_old_med : (C μ).1.rank.val + 1 = ceilHalf n := by
          rwa [hμ_eq] at hμ_med
        have ht := hTimer μ hμ_old_settled hμ_old_med
        rw [hμ_eq]
        omega
  have hTimerStrong' : k + 1 < n → SettledMedianTimerStrong C' := by
    intro hk_next μ hμ_settled hμ_med
    by_cases hμu : μ = u
    · subst μ
      rw [congrArg AgentState.timer hfst]
      have hchild_med :
          2 * (C v).1.rank.val + (C v).1.children + 1 + 1 = ceilHalf n := by
        rw [hu_rank'] at hμ_med
        rw [hv_rank, hv_children_old]
        have hp := heap_parent_rank hk_pos
        omega
      exact
        transitionPEM_recruit_ba_child_timer_ge_three
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          (a := (C u).1) (b := (C v).1)
          (x₀ := (C u).2) (x₁ := (C v).2)
          hu_unsettled hv_settled hv_children_lt h_valid hchild_med
    · by_cases hμv : μ = v
      · subst μ
        rw [congrArg AgentState.timer hsnd]
        have hbounds :=
          transitionPEM_recruit_ba_parent_timer_bounds
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            (a := (C u).1) (b := (C v).1)
            (x₀ := (C u).2) (x₁ := (C v).2)
            hu_unsettled hv_settled hv_children_lt h_valid
            (fun hmed => hTimer v hv_settled hmed)
        have hmed_t :
            (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
              (C u, C v)).2.rank.val + 1 = ceilHalf n := by
          simpa [hsnd] using hμ_med
        exact (hbounds hmed_t).2 (by
          rw [hv_rank, hv_children_old]
          have hp := heap_parent_rank hk_pos
          omega)
      · have hμ_eq := hother μ hμu hμv
        have hμ_old_settled : (C μ).1.role = .Settled := by
          simpa [hμ_eq] using hμ_settled
        have hμ_old_med : (C μ).1.rank.val + 1 = ceilHalf n := by
          rwa [hμ_eq] at hμ_med
        rw [hμ_eq]
        exact hTimer μ hμ_old_settled hμ_old_med
  exact ⟨hHeap', hTimerGood', hTimerStrong'⟩

/-- Phase 4: binary tree recruitment → InSrank (ChatGPT induction on n-k). -/
theorem phase4_binary_tree
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n)
    (C : Config (AgentState n) Opinion n)
    (hSeed : FreshRankingStart C) :
    ∃ L : List (Fin n × Fin n),
      let C' := runPairs (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L
      InSrank C' ∧
      ((∀ μ : Fin n, (C' μ).1.rank.val + 1 = ceilHalf n → 2 ≤ (C' μ).1.timer) ∨
       IsConsensusConfig C') := by
    classical
    set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    have hHeap0 : HeapPrefix C 1 := FreshRankingStart.to_heapPrefix_one hSeed
    have hTimer0 : SettledMedianTimerStrong C :=
      FreshRankingStart.to_timerStrong hn4 hSeed
    have grow :
        ∀ fuel k (C₀ : Config (AgentState n) Opinion n),
          n - k ≤ fuel →
          1 ≤ k →
          k ≤ n →
          HeapPrefix C₀ k →
          SettledMedianTimerStrong C₀ →
          ∃ L : List (Fin n × Fin n),
            let C' := runPairs P C₀ L
            HeapPrefix C' n ∧ SettledMedianTimerGood C' := by
      intro fuel
      induction fuel with
      | zero =>
          intro k C₀ hfuel _hk_pos hk_le hHeap hTimer
          have hk_eq : k = n := by omega
          subst k
          refine ⟨[], ?_⟩
          simp only [runPairs_nil]
          exact ⟨hHeap, SettledMedianTimerStrong.toGood hTimer⟩
      | succ fuel IH =>
          intro k C₀ hfuel hk_pos hk_le hHeap hTimer
          by_cases hk_eq : k = n
          · subst k
            refine ⟨[], ?_⟩
            simp only [runPairs_nil]
            exact ⟨hHeap, SettledMedianTimerStrong.toGood hTimer⟩
          · have hk_lt : k < n := by omega
            obtain ⟨parent, child, hstep⟩ :=
              heapPrefix_recruit_step
                (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
                hk_pos hk_lt C₀ hHeap hTimer
            let C₁ : Config (AgentState n) Opinion n := runPairs P C₀ [(parent, child)]
            have hHeap₁ : HeapPrefix C₁ (k + 1) := by
              simpa [C₁, P] using hstep.1
            by_cases hlast : k + 1 = n
            · refine ⟨[(parent, child)], ?_⟩
              simp only [runPairs_cons, runPairs_nil]
              exact ⟨by simpa [hlast] using hHeap₁,
                by simpa [C₁, P, hlast] using hstep.2.1⟩
            · have hk_next_lt : k + 1 < n := by omega
              have hTimer₁ : SettledMedianTimerStrong C₁ := by
                simpa [C₁, P] using hstep.2.2 hk_next_lt
              have hfuel₁ : n - (k + 1) ≤ fuel := by omega
              obtain ⟨Ltail, htail⟩ :=
                IH (k + 1) C₁ hfuel₁ (by omega) (by omega) hHeap₁ hTimer₁
              refine ⟨[(parent, child)] ++ Ltail, ?_⟩
              rw [runPairs_append]
              change
                let C' := runPairs P C₁ Ltail
                HeapPrefix C' n ∧ SettledMedianTimerGood C'
              exact htail
    obtain ⟨L, hDone⟩ :=
      grow (n - 1) 1 C (by omega) (by omega) (by omega) hHeap0 hTimer0
    refine ⟨L, ?_⟩
    obtain ⟨hHeapN, hTimerN⟩ := hDone
    have hSrank : InSrank (runPairs P C L) := HeapPrefix.to_InSrank hHeapN
    exact ⟨hSrank, Or.inl (fun μ hμ_med => hTimerN μ (hSrank.allSettled μ) hμ_med)⟩

/-- Phase 3+4 composition: all-Resetting → InSrank. -/
theorem phase34_rerank
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hRmax : 0 < Rmax) (hDmax : 0 < Dmax)
    (C : Config (AgentState n) Opinion n)
    (hDormant : IsDormantConfig C) :
    ∃ L : List (Fin n × Fin n),
      let C' := runPairs (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L
      InSrank C' ∧
      ((∀ μ : Fin n, (C' μ).1.rank.val + 1 = ceilHalf n → 2 ≤ (C' μ).1.timer) ∨
       IsConsensusConfig C') := by
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  obtain ⟨L₁, hAwake⟩ :=
    phase3a_to_awakening
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hRmax hDmax C hDormant
  let C₁ : Config (AgentState n) Opinion n := runPairs P C L₁
  obtain ⟨L₂, hSeed⟩ :=
    phase3bc_from_awakening
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 C₁ (by simpa [C₁, P] using hAwake)
  let C₂ : Config (AgentState n) Opinion n := runPairs P C₁ L₂
  obtain ⟨L₃, hRanked⟩ :=
    phase4_binary_tree
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 C₂ (by simpa [C₂, P] using hSeed)
  refine ⟨(L₁ ++ L₂) ++ L₃, ?_⟩
  rw [runPairs_append]
  change
    let C' := runPairs P (runPairs P C (L₁ ++ L₂)) L₃
    InSrank C' ∧
      ((∀ μ : Fin n, (C' μ).1.rank.val + 1 = ceilHalf n → 2 ≤ (C' μ).1.timer) ∨
       IsConsensusConfig C')
  rw [runPairs_append]
  change
    let C' := runPairs P C₂ L₃
    InSrank C' ∧
      ((∀ μ : Fin n, (C' μ).1.rank.val + 1 = ceilHalf n → 2 ≤ (C' μ).1.timer) ∨
       IsConsensusConfig C')
  simpa [P] using hRanked

/-- Scheduler-form ranking endpoint once the reset cycle has reached a
dormant configuration. -/
theorem ranking_from_dormant
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hRmax : 0 < Rmax) (hDmax : 0 < Dmax)
    (C : Config (AgentState n) Opinion n)
    (hDormant : IsDormantConfig C) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t)) := by
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  obtain ⟨L, hL⟩ :=
    phase34_rerank
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hRmax hDmax C hDormant
  exact
    exists_schedule_of_runPairs P C L
      (Goal := fun C' =>
        InSrank C' ∧
          ((∀ μ : Fin n, (C' μ).1.rank.val + 1 = ceilHalf n → 2 ≤ (C' μ).1.timer) ∨
           IsConsensusConfig C'))
      (by simpa [P] using hL)

theorem dormant_to_RankingEndpoint
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hRmax : 0 < Rmax) (hDmax : 0 < Dmax)
    (C : Config (AgentState n) Opinion n)
    (hDormant : IsDormantConfig C) :
    ∃ L : List (Fin n × Fin n),
      RankingEndpoint
        (runPairs (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L) := by
  obtain ⟨L, hL⟩ :=
    phase34_rerank
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hRmax hDmax C hDormant
  exact ⟨L, hL⟩

theorem all_resetting_pos_with_leader_to_RankingEndpoint
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hRmax : 0 < Rmax) (hDmax_n : n ≤ Dmax)
    (C : Config (AgentState n) Opinion n)
    (hAllReset : ∀ w : Fin n, (C w).1.role = .Resetting)
    (hAllPos : ∀ w : Fin n, 0 < (C w).1.resetcount)
    (hHasL : ∃ ℓ : Fin n, (C ℓ).1.leader = .L) :
    ∃ L : List (Fin n × Fin n),
      RankingEndpoint
        (runPairs (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L) := by
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have hDmax_pos : 0 < Dmax := by omega
  obtain ⟨L₁, hDormant⟩ :=
    all_resetting_pos_with_leader_to_dormant
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hDmax_n C hAllReset hAllPos hHasL
  let C₁ : Config (AgentState n) Opinion n := runPairs P C L₁
  obtain ⟨L₂, hRanked⟩ :=
    dormant_to_RankingEndpoint
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hRmax hDmax_pos C₁ (by simpa [C₁, P] using hDormant)
  refine ⟨L₁ ++ L₂, ?_⟩
  rw [runPairs_append]
  exact hRanked

theorem phase12_no_reset_to_RankingEndpoint_or_InSrank
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (hRmax : n ≤ Rmax)
    (C : Config (AgentState n) Opinion n)
    (hNoReset : ∀ w : Fin n, (C w).1.role ≠ .Resetting) :
    ∃ L : List (Fin n × Fin n),
      let C' := runPairs (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L
      InSrank C' ∨ RankingEndpoint C' := by
  classical
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  obtain ⟨L₁, h₁⟩ :=
    phase12_no_reset_to_all_resetting_pos_with_leader_or_InSrank
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hEmax hDmax hRmax C hNoReset
  let C₁ : Config (AgentState n) Opinion n := runPairs P C L₁
  rcases h₁ with hSrank | hReset
  · refine ⟨L₁, ?_⟩
    exact Or.inl hSrank
  · obtain ⟨hAllReset, hAllPos, hHasL⟩ := hReset
    have hRmax_pos : 0 < Rmax := by
      have hn_pos : 0 < n := by omega
      exact Nat.lt_of_lt_of_le hn_pos hRmax
    obtain ⟨L₂, hEndpoint⟩ :=
      all_resetting_pos_with_leader_to_RankingEndpoint
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hRmax_pos hDmax C₁
        (by simpa [C₁, P] using hAllReset)
        (by simpa [C₁, P] using hAllPos)
        (by simpa [C₁, P] using hHasL)
    refine ⟨L₁ ++ L₂, ?_⟩
    rw [runPairs_append]
    change InSrank (runPairs P C₁ L₂) ∨ RankingEndpoint (runPairs P C₁ L₂)
    exact Or.inr hEndpoint

theorem ranking_goal_of_runPairs_RankingEndpoint
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {C : Config (AgentState n) Opinion n}
    {L : List (Fin n × Fin n)}
    (hEndpoint :
      RankingEndpoint
        (runPairs (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L)) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t)) := by
  exact
    exists_schedule_of_runPairs
      (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L
      (Goal := fun C' =>
        InSrank C' ∧
          ((∀ μ : Fin n, (C' μ).1.rank.val + 1 = ceilHalf n → 2 ≤ (C' μ).1.timer) ∨
           IsConsensusConfig C'))
      hEndpoint

theorem reset_snapshot_to_RankingEndpoint
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax : n ≤ Dmax) (hRmax : n ≤ Rmax)
    (C : Config (AgentState n) Opinion n)
    (hReset :
      ∃ r : Fin n, (C r).1.role = .Resetting ∧
        n ≤ (C r).1.resetcount ∧ (C r).1.leader = .L)
    (hResetPos :
      ∀ w : Fin n, (C w).1.role = .Resetting → 0 < (C w).1.resetcount) :
    ∃ L : List (Fin n × Fin n),
      RankingEndpoint
        (runPairs (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L) := by
  classical
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have hDmax_gt_one : 1 < Dmax := by omega
  have hRmax_pos : 0 < Rmax := by
    have hn_pos : 0 < n := by omega
    exact Nat.lt_of_lt_of_le hn_pos hRmax
  obtain ⟨L₁, hAll₁, hPos₁, hLeader₁⟩ :=
    phase2_propagate_reset_with_leader_pos
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hDmax_gt_one C hReset hResetPos
  let C₁ : Config (AgentState n) Opinion n := runPairs P C L₁
  obtain ⟨L₂, hEndpoint⟩ :=
    all_resetting_pos_with_leader_to_RankingEndpoint
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hRmax_pos hDmax C₁
      (by simpa [C₁, P] using hAll₁)
      (by simpa [C₁, P] using hPos₁)
      (by simpa [C₁, P] using hLeader₁)
  refine ⟨L₁ ++ L₂, ?_⟩
  rw [runPairs_append]
  change RankingEndpoint (runPairs P C₁ L₂)
  exact hEndpoint

theorem ranking_goal_of_reset_snapshot
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax : n ≤ Dmax) (hRmax : n ≤ Rmax)
    {C : Config (AgentState n) Opinion n}
    (hReset :
      ∃ r : Fin n, (C r).1.role = .Resetting ∧
        n ≤ (C r).1.resetcount ∧ (C r).1.leader = .L)
    (hResetPos :
      ∀ w : Fin n, (C w).1.role = .Resetting → 0 < (C w).1.resetcount) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t)) := by
  obtain ⟨L, hEndpoint⟩ :=
    reset_snapshot_to_RankingEndpoint
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hDmax hRmax (C := C) hReset hResetPos
  exact
    ranking_goal_of_runPairs_RankingEndpoint
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      (C := C) (L := L) hEndpoint

theorem step_reset_snapshot_to_RankingEndpoint
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax : n ≤ Dmax) (hRmax : n ≤ Rmax)
    {C : Config (AgentState n) Opinion n} {u v : Fin n}
    (hStep :
      let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
      let C' := C.step P u v
      (C' u).1.role = .Resetting ∧ (C' u).1.resetcount = Rmax ∧
        (C' u).1.leader = .L ∧
      (C' v).1.role = .Resetting ∧ (C' v).1.resetcount = Rmax ∧
        (C' v).1.leader = .L ∧
      ∀ y : Fin n, (C' y).1.role = .Resetting →
        (C' y).1.resetcount = Rmax ∧ (C' y).1.leader = .L) :
    ∃ L : List (Fin n × Fin n),
      RankingEndpoint
        (runPairs (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C ((u, v) :: L)) := by
  classical
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  let C₁ : Config (AgentState n) Opinion n := C.step P u v
  change
    (C₁ u).1.role = .Resetting ∧ (C₁ u).1.resetcount = Rmax ∧
      (C₁ u).1.leader = .L ∧
    (C₁ v).1.role = .Resetting ∧ (C₁ v).1.resetcount = Rmax ∧
      (C₁ v).1.leader = .L ∧
    ∀ y : Fin n, (C₁ y).1.role = .Resetting →
      (C₁ y).1.resetcount = Rmax ∧ (C₁ y).1.leader = .L at hStep
  rcases hStep with ⟨hu_role, hu_rc, hu_L, _hv_role, _hv_rc, _hv_L, hSnapshot⟩
  have hReset :
      ∃ r : Fin n, (C₁ r).1.role = .Resetting ∧
        n ≤ (C₁ r).1.resetcount ∧ (C₁ r).1.leader = .L := by
    refine ⟨u, hu_role, ?_, hu_L⟩
    rw [hu_rc]
    exact hRmax
  have hResetPos :
      ∀ w : Fin n, (C₁ w).1.role = .Resetting → 0 < (C₁ w).1.resetcount := by
    intro w hw
    have hfields := hSnapshot w hw
    have hrc : (C₁ w).1.resetcount = Rmax := hfields.1
    rw [hrc]
    have hn_pos : 0 < n := by omega
    exact Nat.lt_of_lt_of_le hn_pos hRmax
  obtain ⟨L, hEndpoint⟩ :=
    reset_snapshot_to_RankingEndpoint
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hDmax hRmax C₁ hReset hResetPos
  refine ⟨L, ?_⟩
  rw [runPairs_cons]
  change RankingEndpoint (runPairs P C₁ L)
  exact hEndpoint

theorem ranking_goal_of_step_reset_snapshot
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax : n ≤ Dmax) (hRmax : n ≤ Rmax)
    {C : Config (AgentState n) Opinion n} {u v : Fin n}
    (hStep :
      let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
      let C' := C.step P u v
      (C' u).1.role = .Resetting ∧ (C' u).1.resetcount = Rmax ∧
        (C' u).1.leader = .L ∧
      (C' v).1.role = .Resetting ∧ (C' v).1.resetcount = Rmax ∧
        (C' v).1.leader = .L ∧
      ∀ y : Fin n, (C' y).1.role = .Resetting →
        (C' y).1.resetcount = Rmax ∧ (C' y).1.leader = .L) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t)) := by
  obtain ⟨L, hEndpoint⟩ :=
    step_reset_snapshot_to_RankingEndpoint
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hDmax hRmax (C := C) (u := u) (v := v) hStep
  exact
    ranking_goal_of_runPairs_RankingEndpoint
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      (C := C) (L := (u, v) :: L) hEndpoint

def BadRankingStart (C : Config (AgentState n) Opinion n) : Prop :=
  InSrank C ∧ ¬ RankingEndpoint C

theorem InSrank_misorder_step_reset_snapshot_of_not_both_settled
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    {u v : Fin n} (hMis : MisorderedPair C (u, v))
    (hnot :
      ¬ ((transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
              (C u, C v)).1.role = .Settled ∧
           (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
              (C u, C v)).2.role = .Settled)) :
    let P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
    let C' := C.step P u v
    (C' u).1.role = .Resetting ∧ (C' u).1.resetcount = Rmax ∧
      (C' u).1.leader = .L ∧
    (C' v).1.role = .Resetting ∧ (C' v).1.resetcount = Rmax ∧
      (C' v).1.leader = .L ∧
    ∀ y : Fin n, (C' y).1.role = .Resetting →
      (C' y).1.resetcount = Rmax ∧ (C' y).1.leader = .L := by
  classical
  obtain ⟨_, _, huv_rank⟩ := hMis
  have huv : u ≠ v := by
    intro h
    rw [h] at huv_rank
    exact (lt_irrefl _ huv_rank).elim
  have hsu : (C u).1.role = .Settled := hC.allSettled u
  have hsv : (C v).1.role = .Settled := hC.allSettled v
  have h_rank_ne : (C u).1.rank ≠ (C v).1.rank := ne_of_lt huv_rank
  have hRD :
      rankDeltaOSSR Rmax Emax Dmax hn ((C u).1, (C v).1) =
        ((C u).1, (C v).1) :=
    rankDeltaOSSR_satisfies_fix (C u).1 (C v).1 hsu hsv h_rank_ne
  have htr_eq :
      transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C u, C v) =
        transitionPEM_phase4 n Rmax ((C u).1, (C v).1) (C u).2 (C v).2 := by
    unfold transitionPEM transitionPEM_prePhase4
    simp [hRD, hsu, hsv, role_settled_ne_resetting]
  have hphase_not :
      ¬ ((transitionPEM_phase4 n Rmax ((C u).1, (C v).1) (C u).2 (C v).2).1.role =
            .Settled ∧
          (transitionPEM_phase4 n Rmax ((C u).1, (C v).1) (C u).2 (C v).2).2.role =
            .Settled) := by
    intro hphase
    apply hnot
    simpa [htr_eq] using hphase
  have hphase_reset :=
    transitionPEM_phase4_reset_both_of_not_both_settled
      (n := n) (Rmax := Rmax) (a := ((C u).1, (C v).1))
      (x₀ := (C u).2) (x₁ := (C v).2) hsu hsv hphase_not
  have hphase_rc :=
    phase4_resetting_resetcount
      (n := n) (Rmax := Rmax) (a := ((C u).1, (C v).1))
      (x₀ := (C u).2) (x₁ := (C v).2) hsu hsv
  have hphase_leader :=
    phase4_resetting_leader
      (n := n) (Rmax := Rmax) (a := ((C u).1, (C v).1))
      (x₀ := (C u).2) (x₁ := (C v).2) hsu hsv
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  let C' : Config (AgentState n) Opinion n := C.step P u v
  have hfst := Config.step_fst_state P C huv
  have hsnd := Config.step_snd_state P C huv huv.symm
  have hu_role : (C' u).1.role = .Resetting := by
    dsimp [C']
    rw [congrArg AgentState.role hfst]
    change (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
      (C u, C v)).1.role = .Resetting
    simpa [htr_eq] using hphase_reset.1
  have hv_role : (C' v).1.role = .Resetting := by
    dsimp [C']
    rw [congrArg AgentState.role hsnd]
    change (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
      (C u, C v)).2.role = .Resetting
    simpa [htr_eq] using hphase_reset.2
  have hu_rc : (C' u).1.resetcount = Rmax := by
    dsimp [C']
    rw [congrArg AgentState.resetcount hfst]
    change (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
      (C u, C v)).1.resetcount = Rmax
    simpa [htr_eq] using hphase_rc.1 hphase_reset.1
  have hv_rc : (C' v).1.resetcount = Rmax := by
    dsimp [C']
    rw [congrArg AgentState.resetcount hsnd]
    change (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
      (C u, C v)).2.resetcount = Rmax
    simpa [htr_eq] using hphase_rc.2 hphase_reset.2
  have hu_leader : (C' u).1.leader = .L := by
    dsimp [C']
    rw [congrArg AgentState.leader hfst]
    change (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
      (C u, C v)).1.leader = .L
    simpa [htr_eq] using hphase_leader.1 hphase_reset.1
  have hv_leader : (C' v).1.leader = .L := by
    dsimp [C']
    rw [congrArg AgentState.leader hsnd]
    change (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
      (C u, C v)).2.leader = .L
    simpa [htr_eq] using hphase_leader.2 hphase_reset.2
  refine ⟨hu_role, hu_rc, hu_leader, hv_role, hv_rc, hv_leader, ?_⟩
  intro y hy
  by_cases hyu : y = u
  · subst y
    exact ⟨hu_rc, hu_leader⟩
  · by_cases hyv : y = v
    · subst y
      exact ⟨hv_rc, hv_leader⟩
    · have hy_state : C' y = C y := by
        dsimp [C', P]
        unfold Config.step
        simp [huv, hyu, hyv]
      have hy_reset_C : (C y).1.role = .Resetting := by
        simpa [C', P, Config.step, huv, hyu, hyv] using hy
      rw [hC.allSettled y] at hy_reset_C
      cases hy_reset_C

theorem InSrank_misorder_step_to_RankingEndpoint_or_InSrank_decrease
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax : n ≤ Dmax) (hRmax : n ≤ Rmax)
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    {u v : Fin n} (hMis : MisorderedPair C (u, v)) :
    (∃ L : List (Fin n × Fin n),
      RankingEndpoint
        (runPairs (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn))
          C ((u, v) :: L))) ∨
    (InSrank
        (C.step (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) u v) ∧
      misorderedCount
        (C.step (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) u v) <
      misorderedCount C) := by
  by_cases hrole :
      (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
          (C u, C v)).1.role = .Settled ∧
      (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
          (C u, C v)).2.role = .Settled
  · exact Or.inr
      (swap_step_decreases_at_misorder_of_role_settled
        (trank := Rmax) (Rmax := Rmax)
        (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
        rankDeltaOSSR_satisfies_fix hC hMis hrole)
  · have hstep :=
      InSrank_misorder_step_reset_snapshot_of_not_both_settled
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hC hMis hrole
    obtain ⟨L, hEndpoint⟩ :=
      step_reset_snapshot_to_RankingEndpoint
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hDmax hRmax (C := C) (u := u) (v := v) hstep
    exact Or.inl ⟨L, hEndpoint⟩

theorem InSrank_reaches_RankingEndpoint_or_InSswap
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax : n ≤ Dmax) (hRmax : n ≤ Rmax)
    {C : Config (AgentState n) Opinion n} (hC : InSrank C) :
    (∃ L : List (Fin n × Fin n),
      RankingEndpoint
        (runPairs (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L)) ∨
    (∃ L : List (Fin n × Fin n),
      InSswap
        (runPairs (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L)) := by
  classical
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  let motive : ℕ → Prop := fun k =>
    ∀ C : Config (AgentState n) Opinion n,
      InSrank C →
      misorderedCount C = k →
      (∃ L : List (Fin n × Fin n), RankingEndpoint (runPairs P C L)) ∨
      (∃ L : List (Fin n × Fin n), InSswap (runPairs P C L))
  have hmain : ∀ k, motive k := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro C hC hcount
      by_cases hk0 : k = 0
      · have hzero : misorderedCount C = 0 := by
          rw [hcount, hk0]
        exact Or.inr ⟨[], by
          simpa [P] using
            (InSswap_of_InSrank_of_count_zero hC hzero)⟩
      · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
        have hpos : 0 < misorderedCount C := by
          rw [hcount]
          exact hkpos
        obtain ⟨u, v, hMis⟩ := exists_misordered_of_pos_count hpos
        have hstep :=
          InSrank_misorder_step_to_RankingEndpoint_or_InSrank_decrease
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            hn4 hDmax hRmax hC hMis
        rcases hstep with hEndpoint | hDec
        · rcases hEndpoint with ⟨L, hEndpoint⟩
          exact Or.inl ⟨(u, v) :: L, by
            simpa [P] using hEndpoint⟩
        · rcases hDec with ⟨hCstep, hlt⟩
          let Cstep : Config (AgentState n) Opinion n := C.step P u v
          have hlt_k : misorderedCount Cstep < k := by
            dsimp [Cstep, P]
            rw [← hcount]
            exact hlt
          have hrec := ih (misorderedCount Cstep) hlt_k Cstep hCstep rfl
          rcases hrec with hEndpoint | hSwap
          · rcases hEndpoint with ⟨L, hEndpoint⟩
            exact Or.inl ⟨(u, v) :: L, by
              change RankingEndpoint (runPairs P (C.step P u v) L)
              exact hEndpoint⟩
          · rcases hSwap with ⟨L, hSwap⟩
            exact Or.inr ⟨(u, v) :: L, by
              change InSswap (runPairs P (C.step P u v) L)
              exact hSwap⟩
  have h := hmain (misorderedCount C) C hC rfl
  simpa [P] using h

theorem ranking_of_no_reset_with_bad_start_handler
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (hRmax : n ≤ Rmax)
    (C : Config (AgentState n) Opinion n)
    (hNoReset : ∀ w : Fin n, (C w).1.role ≠ .Resetting)
    (hBad :
      ∀ Cbad : Config (AgentState n) Opinion n,
        BadRankingStart Cbad →
        ∃ L : List (Fin n × Fin n),
          RankingEndpoint
            (runPairs (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) Cbad L)) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t)) := by
  classical
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  obtain ⟨L₁, h₁⟩ :=
    phase12_no_reset_to_RankingEndpoint_or_InSrank
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hEmax hDmax hRmax C hNoReset
  let C₁ : Config (AgentState n) Opinion n := runPairs P C L₁
  rcases h₁ with hSrank | hEndpoint
  · by_cases hDone : RankingEndpoint C₁
    · exact
        ranking_goal_of_runPairs_RankingEndpoint
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          (C := C) (L := L₁) (by simpa [C₁, P] using hDone)
    · obtain ⟨L₂, hEndpoint₂⟩ := hBad C₁ ⟨by simpa [C₁, P] using hSrank, hDone⟩
      have hEndpoint_total :
          RankingEndpoint (runPairs P C (L₁ ++ L₂)) := by
        rw [runPairs_append]
        change RankingEndpoint (runPairs P C₁ L₂)
        exact hEndpoint₂
      exact
        ranking_goal_of_runPairs_RankingEndpoint
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          (C := C) (L := L₁ ++ L₂) hEndpoint_total
  · exact
      ranking_goal_of_runPairs_RankingEndpoint
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        (C := C) (L := L₁) (by simpa [C₁, P] using hEndpoint)

theorem BadRankingStart.not_consensus
    {C : Config (AgentState n) Opinion n}
    (hbad : BadRankingStart C) :
    ¬ IsConsensusConfig C := by
  intro hConsensus
  exact hbad.2 ⟨hbad.1, Or.inr hConsensus⟩

theorem BadRankingStart.exists_wrong_answer_of_InSswap
    {C : Config (AgentState n) Opinion n}
    (hbad : BadRankingStart C)
    (hSwap : InSswap C) :
    ∃ w : Fin n, (C w).1.answer ≠ majorityAnswer C := by
  by_contra hwrong
  push_neg at hwrong
  exact hbad.not_consensus
    { allSettled := hSwap.allSettled
      ranks_inj := hSwap.ranks_inj
      input_rank := hSwap.input_rank
      allAnswerCorrect := hwrong }

theorem InSswap.swap_condition_false
    {C : Config (AgentState n) Opinion n}
    (hSwap : InSswap C) (u v : Fin n) :
    ¬((C u).1.rank < (C v).1.rank ∧
      (C u).2 = Opinion.B ∧ (C v).2 = Opinion.A) := by
  rintro ⟨hrank, huB, hvA⟩
  have hu_not_lt : ¬ (C u).1.rank.val < nAOf C := by
    intro hu_lt
    have huA : (C u).2 = Opinion.A := (hSwap.input_rank u).mpr hu_lt
    rw [huB] at huA
    cases huA
  have hv_lt : (C v).1.rank.val < nAOf C := (hSwap.input_rank v).mp hvA
  have hlt : (C u).1.rank.val < (C v).1.rank.val := by
    simpa using hrank
  omega

theorem BadRankingStart.exists_median_timer_lt_two
    {C : Config (AgentState n) Opinion n}
    (hbad : BadRankingStart C) :
    ∃ μ : Fin n, (C μ).1.rank.val + 1 = ceilHalf n ∧ (C μ).1.timer < 2 := by
  classical
  have hnot_timer :
      ¬ ∀ μ : Fin n, (C μ).1.rank.val + 1 = ceilHalf n → 2 ≤ (C μ).1.timer := by
    intro htimer
    exact hbad.2 ⟨hbad.1, Or.inl htimer⟩
  push_neg at hnot_timer
  simpa using hnot_timer

theorem BadRankingStart.exists_median_timer_zero_or_one
    {C : Config (AgentState n) Opinion n}
    (hbad : BadRankingStart C) :
    ∃ μ : Fin n,
      (C μ).1.rank.val + 1 = ceilHalf n ∧
        ((C μ).1.timer = 0 ∨ (C μ).1.timer = 1) := by
  obtain ⟨μ, hμ, htimer⟩ := hbad.exists_median_timer_lt_two
  refine ⟨μ, hμ, ?_⟩
  omega

theorem InSrank.exists_max_rank
    {C : Config (AgentState n) Opinion n}
    (hC : InSrank C) (hn : 0 < n) :
    ∃ v : Fin n, (C v).1.rank.val + 1 = n := by
  obtain ⟨v, hv⟩ := hC.exists_at_rank hn ⟨n - 1, by omega⟩
  refine ⟨v, ?_⟩
  have hv_val := congrArg Fin.val hv
  simp at hv_val
  omega

theorem InSrank.max_rank_ne_median
    {C : Config (AgentState n) Opinion n}
    (_hC : InSrank C)
    (hn2 : 2 ≤ n)
    {μ v : Fin n}
    (hμ : (C μ).1.rank.val + 1 = ceilHalf n)
    (hv : (C v).1.rank.val + 1 = n) :
    μ ≠ v := by
  intro hμv
  rw [hμv] at hμ
  unfold ceilHalf at hμ
  omega

theorem InSrank.exists_max_rank_ne_median
    {C : Config (AgentState n) Opinion n}
    (hC : InSrank C) (hn4 : 4 ≤ n)
    {μ : Fin n}
    (hμ : (C μ).1.rank.val + 1 = ceilHalf n) :
    ∃ v : Fin n, μ ≠ v ∧ (C v).1.rank.val + 1 = n := by
  obtain ⟨v, hv⟩ := hC.exists_max_rank (by omega)
  exact ⟨v, hC.max_rank_ne_median (by omega) hμ hv, hv⟩

theorem phase12_no_reset_to_ranking_goal_or_bad_start
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (hRmax : n ≤ Rmax)
    (C : Config (AgentState n) Opinion n)
    (hNoReset : ∀ w : Fin n, (C w).1.role ≠ .Resetting) :
    (∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t))) ∨
    ∃ L : List (Fin n × Fin n),
      BadRankingStart
        (runPairs (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L) := by
  classical
  obtain ⟨L, hL⟩ :=
    phase12_no_reset_to_RankingEndpoint_or_InSrank
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hEmax hDmax hRmax C hNoReset
  rcases hL with hSrank | hEndpoint
  · by_cases hDone :
      RankingEndpoint
        (runPairs (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L)
    · exact Or.inl
        (ranking_goal_of_runPairs_RankingEndpoint
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          (C := C) (L := L) hDone)
    · exact Or.inr ⟨L, hSrank, hDone⟩
  · exact Or.inl
      (ranking_goal_of_runPairs_RankingEndpoint
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        (C := C) (L := L) hEndpoint)

theorem InSrank_timer_zero_no_swap_diff_to_RankingEndpoint
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax : n ≤ Dmax) (hRmax : n ≤ Rmax)
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (hv_no_med : (C v).1.rank.val + 1 ≠ ceilHalf n)
    (h_timer : (C μ).1.timer = 0)
    (h_no_swap : ¬((C μ).1.rank < (C v).1.rank ∧ (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A))
    (hpar : ¬ n % 2 = 0)
    (h_post_diff : opinionToAnswer (C μ).2 ≠ (C v).1.answer) :
    ∃ L : List (Fin n × Fin n),
      RankingEndpoint
        (runPairs (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L) := by
  have hstep :=
    trigger_reset_from_InSrank_timer_zero_no_swap_with_snapshot
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      (C := C) hC hμv hμ_med hv_no_med h_timer h_no_swap hpar h_post_diff
  obtain ⟨L, hEndpoint⟩ :=
    step_reset_snapshot_to_RankingEndpoint
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hDmax hRmax (C := C) (u := μ) (v := v) hstep
  exact ⟨(μ, v) :: L, hEndpoint⟩

theorem InSswap_even_lower_timer_zero_wrong_nonupper_to_RankingEndpoint
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax : n ≤ Dmax) (hRmax : n ≤ Rmax)
    {C : Config (AgentState n) Opinion n}
    (hSwap : InSswap C)
    (hpar : n % 2 = 0)
    {μ w : Fin n} (hμw : μ ≠ w)
    (hμ_lower : (C μ).1.rank.val + 1 = n / 2)
    (hw_not_upper : (C w).1.rank.val + 1 ≠ n / 2 + 1)
    (h_timer : (C μ).1.timer = 0)
    (hμ_correct : (C μ).1.answer = majorityAnswer C)
    (hw_wrong : (C w).1.answer ≠ majorityAnswer C) :
    ∃ L : List (Fin n × Fin n),
      RankingEndpoint
        (runPairs (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L) := by
  have hw_not_lower : (C w).1.rank.val + 1 ≠ n / 2 := by
    intro hw_lower
    apply hμw
    apply hSwap.ranks_inj
    apply Fin.eq_of_val_eq
    have hμ_val : (C μ).1.rank.val = n / 2 - 1 := by omega
    have hw_val : (C w).1.rank.val = n / 2 - 1 := by omega
    exact hμ_val.trans hw_val.symm
  have h_no_swap :
      ¬((C μ).1.rank < (C w).1.rank ∧
        (C μ).2 = Opinion.B ∧ (C w).2 = Opinion.A) :=
    hSwap.swap_condition_false μ w
  have hdiff : (C μ).1.answer ≠ (C w).1.answer := by
    intro hsame
    exact hw_wrong (by rw [← hsame, hμ_correct])
  have hstep :=
    trigger_reset_from_InSrank_even_lower_timer_zero_no_swap_with_snapshot
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hSwap.toInSrank hμw hpar hμ_lower hw_not_lower hw_not_upper h_timer
      h_no_swap hdiff
  obtain ⟨L, hEndpoint⟩ :=
    step_reset_snapshot_to_RankingEndpoint
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hDmax hRmax (C := C) (u := μ) (v := w) hstep
  exact ⟨(μ, w) :: L, hEndpoint⟩

theorem InSswap_even_lower_timer_one_same_then_zero_wrong_nonupper_to_RankingEndpoint
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax : n ≤ Dmax) (hRmax : n ≤ Rmax)
    {C : Config (AgentState n) Opinion n}
    (hSwap : InSswap C)
    (hpar : n % 2 = 0)
    {μ v w : Fin n} (hμv : μ ≠ v) (hμw : μ ≠ w) (hwv : w ≠ v)
    (hμ_lower : (C μ).1.rank.val + 1 = n / 2)
    (hv_max : (C v).1.rank.val + 1 = n)
    (hw_not_upper : (C w).1.rank.val + 1 ≠ n / 2 + 1)
    (h_timer : (C μ).1.timer = 1)
    (hμ_correct : (C μ).1.answer = majorityAnswer C)
    (hv_correct : (C v).1.answer = majorityAnswer C)
    (hw_wrong : (C w).1.answer ≠ majorityAnswer C) :
    ∃ L : List (Fin n × Fin n),
      RankingEndpoint
        (runPairs (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L) := by
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  let C₁ : Config (AgentState n) Opinion n := C.step P μ v
  have h_no_swap :
      ¬((C μ).1.rank < (C v).1.rank ∧
        (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A) :=
    hSwap.swap_condition_false μ v
  have h_same : (C μ).1.answer = (C v).1.answer := by
    rw [hμ_correct, hv_correct]
  obtain ⟨hμ_state, hv_state, hothers⟩ :=
    no_reset_even_lower_max_timer_one_step_state
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hSwap.toInSrank hn4 hμv hpar hμ_lower hv_max h_timer h_no_swap h_same
  have hC₁_swap_pack :=
    no_reset_even_lower_max_timer_one_step_InSswap
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hSwap hn4 hμv hpar hμ_lower hv_max h_timer h_no_swap h_same
  have hC₁_swap : InSswap C₁ := by
    simpa [C₁, P] using hC₁_swap_pack.1
  have hμ_timer₁ : (C₁ μ).1.timer = 0 := by
    simpa [C₁, P] using hC₁_swap_pack.2.1
  have hμ_lower₁ : (C₁ μ).1.rank.val + 1 = n / 2 := by
    simpa [C₁, P] using hC₁_swap_pack.2.2.2
  have hw_state₁ : C₁ w = C w := by
    simpa [C₁, P] using hothers w hμw.symm hwv
  have hmaj₁ : majorityAnswer C₁ = majorityAnswer C := by
    simpa [C₁, P] using
      (majorityAnswer_step_eq
        (trank := Rmax) (Rmax := Rmax)
        (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn) C μ v)
  have hμ_correct₁ : (C₁ μ).1.answer = majorityAnswer C₁ := by
    rw [hmaj₁]
    simpa [C₁, P] using hC₁_swap_pack.2.2.1.trans hμ_correct
  have hw_not_upper₁ : (C₁ w).1.rank.val + 1 ≠ n / 2 + 1 := by
    rw [hw_state₁]
    exact hw_not_upper
  have hw_wrong₁ : (C₁ w).1.answer ≠ majorityAnswer C₁ := by
    rw [hw_state₁, hmaj₁]
    exact hw_wrong
  obtain ⟨Ltail, hEndpoint⟩ :=
    InSswap_even_lower_timer_zero_wrong_nonupper_to_RankingEndpoint
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hDmax hRmax hC₁_swap hpar hμw hμ_lower₁ hw_not_upper₁
      hμ_timer₁ hμ_correct₁ hw_wrong₁
  refine ⟨(μ, v) :: Ltail, ?_⟩
  change RankingEndpoint (runPairs P (C.step P μ v) Ltail)
  exact hEndpoint

theorem InSswap_even_lower_timer_one_max_wrong_to_RankingEndpoint
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax : n ≤ Dmax) (hRmax : n ≤ Rmax)
    {C : Config (AgentState n) Opinion n}
    (hSwap : InSswap C)
    (hpar : n % 2 = 0)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hμ_lower : (C μ).1.rank.val + 1 = n / 2)
    (hv_max : (C v).1.rank.val + 1 = n)
    (h_timer : (C μ).1.timer = 1)
    (hμ_correct : (C μ).1.answer = majorityAnswer C)
    (hv_wrong : (C v).1.answer ≠ majorityAnswer C) :
    ∃ L : List (Fin n × Fin n),
      RankingEndpoint
        (runPairs (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L) := by
  have h_no_swap :
      ¬((C μ).1.rank < (C v).1.rank ∧
        (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A) :=
    hSwap.swap_condition_false μ v
  have hdiff : (C μ).1.answer ≠ (C v).1.answer := by
    intro hsame
    exact hv_wrong (by rw [← hsame, hμ_correct])
  have hstep :=
    trigger_reset_from_InSrank_even_lower_timer_one_max_no_swap_with_snapshot
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hSwap.toInSrank hn4 hμv hpar hμ_lower hv_max h_timer h_no_swap hdiff
  obtain ⟨L, hEndpoint⟩ :=
    step_reset_snapshot_to_RankingEndpoint
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hDmax hRmax (C := C) (u := μ) (v := v) hstep
  exact ⟨(μ, v) :: L, hEndpoint⟩

theorem InSswap_even_median_pair_inputs_agree_of_strict
    {C : Config (AgentState n) Opinion n} (hC : InSswap C)
    (hpar : n % 2 = 0) (hne : nAOf C ≠ nBOf C)
    {u v : Fin n}
    (hu_med : (C u).1.rank.val + 1 = n / 2)
    (hv_upper : (C v).1.rank.val + 1 = n / 2 + 1) :
    (C u).2 = (C v).2 := by
  have h_nA_total : nAOf C + nBOf C = n := nAOf_add_nBOf C
  have hu_rank_val : (C u).1.rank.val = n / 2 - 1 := by omega
  have hv_rank_val : (C v).1.rank.val = n / 2 := by omega
  by_cases h_nA_maj : nAOf C > n / 2
  · have hu_A : (C u).2 = Opinion.A := by
      apply (hC.input_rank u).mpr
      rw [hu_rank_val]
      omega
    have hv_A : (C v).2 = Opinion.A := by
      apply (hC.input_rank v).mpr
      rw [hv_rank_val]
      omega
    rw [hu_A, hv_A]
  · have h_nB_maj : nBOf C > n / 2 := by omega
    have h_nA_lt : nAOf C < n / 2 := by omega
    have hu_B : (C u).2 = Opinion.B := by
      rcases h_u_input : (C u).2 with _ | _
      · have h_lt := (hC.input_rank u).mp h_u_input
        rw [hu_rank_val] at h_lt
        omega
      · rfl
    have hv_B : (C v).2 = Opinion.B := by
      rcases h_v_input : (C v).2 with _ | _
      · have h_lt := (hC.input_rank v).mp h_v_input
        rw [hv_rank_val] at h_lt
        omega
      · rfl
    rw [hu_B, hv_B]

theorem InSswap_even_median_pair_inputs_disagree_of_tie
    {C : Config (AgentState n) Opinion n} (hC : InSswap C)
    (hpar : n % 2 = 0) (hTie : nAOf C = nBOf C)
    {u v : Fin n}
    (hu_med : (C u).1.rank.val + 1 = n / 2)
    (hv_upper : (C v).1.rank.val + 1 = n / 2 + 1) :
    (C u).2 ≠ (C v).2 := by
  have h_nA : nAOf C = n / 2 := by
    have hsum := nAOf_add_nBOf C
    omega
  have hu_rank_val : (C u).1.rank.val = n / 2 - 1 := by omega
  have hv_rank_val : (C v).1.rank.val = n / 2 := by omega
  have hu_A : (C u).2 = Opinion.A := by
    apply (hC.input_rank u).mpr
    rw [hu_rank_val, h_nA]
    omega
  have hv_B : (C v).2 = Opinion.B := by
    rcases h_v_input : (C v).2 with _ | _
    · have h_lt := (hC.input_rank v).mp h_v_input
      rw [hv_rank_val, h_nA] at h_lt
      omega
    · rfl
  rw [hu_A, hv_B]
  exact fun h => Opinion.noConfusion h

theorem InSswap_even_median_pair_decision_decreases
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n} (hC : InSswap C)
    {u v : Fin n} (huv : u ≠ v)
    (hpar : n % 2 = 0)
    (hu_med : (C u).1.rank.val + 1 = n / 2)
    (hv_upper : (C v).1.rank.val + 1 = n / 2 + 1)
    (hn4 : 4 ≤ n)
    (hwrong :
      (C u).1.answer ≠ majorityAnswer C ∨
        (C v).1.answer ≠ majorityAnswer C) :
    let P := protocolPEM n trank Rmax rankDelta
    InSswap (C.step P u v) ∧
      wrongAnswerCount (C.step P u v) < wrongAnswerCount C := by
  by_cases hTie : nAOf C = nBOf C
  · have hdis :=
      InSswap_even_median_pair_inputs_disagree_of_tie hC hpar hTie hu_med hv_upper
    exact
      decision_step_at_median_pair_even_tie_decreases
        hRank hC huv hpar hu_med hv_upper hdis hTie hn4 hwrong
  · have hagree :=
      InSswap_even_median_pair_inputs_agree_of_strict hC hpar hTie hu_med hv_upper
    exact
      decision_step_at_median_pair_even_decreases
        hRank hC huv hpar hu_med hv_upper hagree hTie hn4 hwrong

theorem InSswap_bad_even_to_RankingEndpoint
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax : n ≤ Dmax) (hRmax : n ≤ Rmax)
    {C : Config (AgentState n) Opinion n}
    (hbad : BadRankingStart C) (hSwap : InSswap C)
    (hpar : n % 2 = 0) :
    ∃ L : List (Fin n × Fin n),
      RankingEndpoint
        (runPairs (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L) := by
  classical
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  let motive : ℕ → Prop := fun k =>
    ∀ C : Config (AgentState n) Opinion n,
      BadRankingStart C →
      InSswap C →
      wrongAnswerCount C = k →
      ∃ L : List (Fin n × Fin n), RankingEndpoint (runPairs P C L)
  have hmain : ∀ k, motive k := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro C hbad hSwap hcount
      by_cases hk0 : k = 0
      · have hzero : wrongAnswerCount C = 0 := by
          rw [hcount, hk0]
        have hConsensus :=
          isConsensusConfig_of_InSswap_of_wrongAnswerCount_zero hSwap hzero
        exact ⟨[], by
          simp only [runPairs_nil]
          exact ⟨hSwap.toInSrank, Or.inr hConsensus⟩⟩
      · obtain ⟨μ, hμ_med, htimer⟩ := hbad.exists_median_timer_zero_or_one
        have hceil : ceilHalf n = n / 2 := by
          unfold ceilHalf
          omega
        have hμ_lower : (C μ).1.rank.val + 1 = n / 2 := by
          rwa [hceil] at hμ_med
        have h_upper_lt : n / 2 < n := by omega
        obtain ⟨ν, hν_rank⟩ :=
          hSwap.toInSrank.exists_at_rank (by omega) (⟨n / 2, h_upper_lt⟩ : Fin n)
        have hν_upper : (C ν).1.rank.val + 1 = n / 2 + 1 := by
          rw [hν_rank]
        have hμν : μ ≠ ν := by
          intro h
          subst ν
          omega
        have hdecision
            (hwrong_pair :
              (C μ).1.answer ≠ majorityAnswer C ∨
                (C ν).1.answer ≠ majorityAnswer C) :
            ∃ L : List (Fin n × Fin n), RankingEndpoint (runPairs P C L) := by
          let C₁ : Config (AgentState n) Opinion n := C.step P μ ν
          have hdec :=
            InSswap_even_median_pair_decision_decreases
              (trank := Rmax) (Rmax := Rmax)
              (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
              rankDeltaOSSR_satisfies_fix hSwap hμν hpar hμ_lower hν_upper hn4
              hwrong_pair
          have hC₁_swap : InSswap C₁ := by
            simpa [C₁, P] using hdec.1
          have hlt : wrongAnswerCount C₁ < k := by
            rw [← hcount]
            simpa [C₁, P] using hdec.2
          by_cases hDone : RankingEndpoint C₁
          · exact ⟨[(μ, ν)], by
              simp only [runPairs_cons, runPairs_nil]
              change RankingEndpoint C₁
              exact hDone⟩
          · have hbad₁ : BadRankingStart C₁ := ⟨hC₁_swap.toInSrank, hDone⟩
            obtain ⟨Ltail, htail⟩ := ih (wrongAnswerCount C₁) hlt C₁ hbad₁ hC₁_swap rfl
            exact ⟨(μ, ν) :: Ltail, by
              change RankingEndpoint (runPairs P (C.step P μ ν) Ltail)
              exact htail⟩
        by_cases hμ_wrong : (C μ).1.answer ≠ majorityAnswer C
        · exact hdecision (Or.inl hμ_wrong)
        · have hμ_correct : (C μ).1.answer = majorityAnswer C := not_not.mp hμ_wrong
          obtain ⟨w, hw_wrong⟩ := hbad.exists_wrong_answer_of_InSswap hSwap
          rcases htimer with htimer0 | htimer1
          · by_cases hw_upper : (C w).1.rank.val + 1 = n / 2 + 1
            · have hw_eq_ν : w = ν := by
                apply hSwap.ranks_inj
                apply Fin.eq_of_val_eq
                have hw_val : (C w).1.rank.val = n / 2 := by omega
                have hν_val : (C ν).1.rank.val = n / 2 := by omega
                exact hw_val.trans hν_val.symm
              subst w
              exact hdecision (Or.inr hw_wrong)
            · have hμw : μ ≠ w := by
                intro h
                subst w
                exact hw_wrong hμ_correct
              exact
                InSswap_even_lower_timer_zero_wrong_nonupper_to_RankingEndpoint
                  (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
                  hn4 hDmax hRmax hSwap hpar hμw hμ_lower hw_upper htimer0
                  hμ_correct hw_wrong
          · obtain ⟨ρ, hμρ, hρ_max⟩ :=
              hSwap.toInSrank.exists_max_rank_ne_median hn4 hμ_med
            by_cases hρ_wrong : (C ρ).1.answer ≠ majorityAnswer C
            · exact
                InSswap_even_lower_timer_one_max_wrong_to_RankingEndpoint
                  (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
                  hn4 hDmax hRmax hSwap hpar hμρ hμ_lower hρ_max htimer1
                  hμ_correct hρ_wrong
            · have hρ_correct : (C ρ).1.answer = majorityAnswer C := not_not.mp hρ_wrong
              by_cases hw_upper : (C w).1.rank.val + 1 = n / 2 + 1
              · have hw_eq_ν : w = ν := by
                  apply hSwap.ranks_inj
                  apply Fin.eq_of_val_eq
                  have hw_val : (C w).1.rank.val = n / 2 := by omega
                  have hν_val : (C ν).1.rank.val = n / 2 := by omega
                  exact hw_val.trans hν_val.symm
                subst w
                exact hdecision (Or.inr hw_wrong)
              · have hμw : μ ≠ w := by
                  intro h
                  subst w
                  exact hw_wrong hμ_correct
                have hwρ : w ≠ ρ := by
                  intro h
                  subst w
                  exact hw_wrong hρ_correct
                exact
                  InSswap_even_lower_timer_one_same_then_zero_wrong_nonupper_to_RankingEndpoint
                    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
                    hn4 hDmax hRmax hSwap hpar hμρ hμw hwρ hμ_lower hρ_max
                    hw_upper htimer1 hμ_correct hρ_correct hw_wrong
  simpa [P, motive] using hmain (wrongAnswerCount C) C hbad hSwap rfl

theorem BadRankingStart_even_to_RankingEndpoint
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax : n ≤ Dmax) (hRmax : n ≤ Rmax)
    {C : Config (AgentState n) Opinion n}
    (hbad : BadRankingStart C)
    (hpar : n % 2 = 0) :
    ∃ L : List (Fin n × Fin n),
      RankingEndpoint
        (runPairs (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L) := by
  classical
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  obtain hReach :=
    InSrank_reaches_RankingEndpoint_or_InSswap
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hDmax hRmax hbad.1
  rcases hReach with hEndpoint | hSwapReach
  · exact hEndpoint
  · obtain ⟨L₁, hSwap₁⟩ := hSwapReach
    let C₁ : Config (AgentState n) Opinion n := runPairs P C L₁
    by_cases hDone : RankingEndpoint C₁
    · exact ⟨L₁, by simpa [C₁, P] using hDone⟩
    · have hbad₁ : BadRankingStart C₁ := by
        exact ⟨by simpa [C₁, P] using hSwap₁.toInSrank, hDone⟩
      have hSwapC₁ : InSswap C₁ := by
        simpa [C₁, P] using hSwap₁
      obtain ⟨L₂, hEndpoint₂⟩ :=
        InSswap_bad_even_to_RankingEndpoint
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hn4 hDmax hRmax hbad₁ hSwapC₁ hpar
      refine ⟨L₁ ++ L₂, ?_⟩
      rw [runPairs_append]
      change RankingEndpoint (runPairs P C₁ L₂)
      exact hEndpoint₂

theorem ranking_of_no_reset_even
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (hRmax : n ≤ Rmax)
    (hpar : n % 2 = 0)
    (C : Config (AgentState n) Opinion n)
    (hNoReset : ∀ w : Fin n, (C w).1.role ≠ .Resetting) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t)) := by
  exact
    ranking_of_no_reset_with_bad_start_handler
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hEmax hDmax hRmax C hNoReset
      (fun Cbad hbad =>
        BadRankingStart_even_to_RankingEndpoint
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hn4 hDmax hRmax hbad hpar)

set_option maxHeartbeats 4000000 in
theorem transitionPEM_timer_zero_no_swap_same_trace
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (hv_no_med : (C v).1.rank.val + 1 ≠ ceilHalf n)
    (h_timer : (C μ).1.timer = 0)
    (h_no_swap : ¬((C μ).1.rank < (C v).1.rank ∧
      (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A))
    (hpar : ¬ n % 2 = 0)
    (h_post_same : opinionToAnswer (C μ).2 = (C v).1.answer) :
    transitionPEM n trank Rmax rankDelta (C μ, C v) =
      ({ (C μ).1 with answer := opinionToAnswer (C μ).2 }, (C v).1) := by
  have hμ_settled : (C μ).1.role = .Settled := hC.allSettled μ
  have hv_settled : (C v).1.role = .Settled := hC.allSettled v
  have h_rank_ne : (C μ).1.rank ≠ (C v).1.rank := by
    intro hEq
    exact hμv (hC.ranks_inj hEq)
  have hRD : rankDelta ((C μ).1, (C v).1) = ((C μ).1, (C v).1) :=
    hRank (C μ).1 (C v).1 hμ_settled hv_settled h_rank_ne
  unfold transitionPEM transitionPEM_phase4 transitionPEM_prePhase4
    phase4_swap phase4_decide phase4_propagate
  simp only [hRD, hμ_settled, hv_settled, ne_eq,
    role_settled_ne_resetting, not_true_eq_false, not_false_eq_true,
    false_and, and_false, if_false, and_self, if_true, h_no_swap, hpar,
    hμ_med, hv_no_med, h_timer]
  split_ifs with h <;> simp_all [h_timer]

theorem InSswap_bad_timer_zero_wrong_nonmedian_to_RankingEndpoint
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax : n ≤ Dmax) (hRmax : n ≤ Rmax)
    {C : Config (AgentState n) Opinion n}
    (hbad : BadRankingStart C) (hSwap : InSswap C)
    {μ w : Fin n}
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (hw_no_med : (C w).1.rank.val + 1 ≠ ceilHalf n)
    (h_timer : (C μ).1.timer = 0)
    (hpar : ¬ n % 2 = 0)
    (hw_wrong : (C w).1.answer ≠ majorityAnswer C) :
    ∃ L : List (Fin n × Fin n),
      RankingEndpoint
        (runPairs (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L) := by
  have hμw : μ ≠ w := by
    intro h
    subst w
    exact hw_no_med hμ_med
  have h_no_swap :
      ¬((C μ).1.rank < (C w).1.rank ∧
        (C μ).2 = Opinion.B ∧ (C w).2 = Opinion.A) :=
    hSwap.swap_condition_false μ w
  have h_post_diff : opinionToAnswer (C μ).2 ≠ (C w).1.answer := by
    rw [opinionToAnswer_median_eq_majorityAnswer_odd hSwap hμ_med hpar]
    exact hw_wrong.symm
  exact
    InSrank_timer_zero_no_swap_diff_to_RankingEndpoint
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hDmax hRmax hbad.1 hμw hμ_med hw_no_med h_timer
      h_no_swap hpar h_post_diff

theorem InSswap_bad_timer_zero_only_median_wrong_to_RankingEndpoint
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n)
    {C : Config (AgentState n) Opinion n}
    (hSwap : InSswap C)
    {μ : Fin n}
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (h_timer : (C μ).1.timer = 0)
    (hpar : ¬ n % 2 = 0)
    (hOnlyMedianWrong :
      ∀ w : Fin n, w ≠ μ → (C w).1.answer = majorityAnswer C) :
    ∃ L : List (Fin n × Fin n),
      RankingEndpoint
        (runPairs (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L) := by
  classical
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have hcard : 1 < Fintype.card (Fin n) := by
    rw [Fintype.card_fin]
    omega
  obtain ⟨v, hv_ne_mu⟩ := Fintype.exists_ne_of_one_lt_card hcard μ
  have hμv : μ ≠ v := fun h => hv_ne_mu h.symm
  have hv_no_med : (C v).1.rank.val + 1 ≠ ceilHalf n := by
    intro hv_med
    apply hμv
    apply hSwap.ranks_inj
    apply Fin.eq_of_val_eq
    have hμ_val : (C μ).1.rank.val = ceilHalf n - 1 := by omega
    have hv_val : (C v).1.rank.val = ceilHalf n - 1 := by omega
    exact hμ_val.trans hv_val.symm
  have h_no_swap :
      ¬((C μ).1.rank < (C v).1.rank ∧
        (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A) :=
    hSwap.swap_condition_false μ v
  have h_median_correct :
      opinionToAnswer (C μ).2 = majorityAnswer C :=
    opinionToAnswer_median_eq_majorityAnswer_odd hSwap hμ_med hpar
  have hv_correct : (C v).1.answer = majorityAnswer C :=
    hOnlyMedianWrong v hv_ne_mu
  have h_post_same : opinionToAnswer (C μ).2 = (C v).1.answer := by
    rw [h_median_correct, hv_correct]
  let C' : Config (AgentState n) Opinion n := C.step P μ v
  have htr :=
    transitionPEM_timer_zero_no_swap_same_trace
      (trank := Rmax) (Rmax := Rmax)
      (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
      (hRank := rankDeltaOSSR_satisfies_fix)
      (C := C) hSwap.toInSrank hμv hμ_med hv_no_med h_timer
      h_no_swap hpar h_post_same
  have hC'_eq : C' =
      fun w => if w = μ then ({ (C μ).1 with answer := opinionToAnswer (C μ).2 }, (C μ).2)
        else if w = v then C v
        else C w := by
    funext w
    dsimp [C', P]
    unfold Config.step
    simp only [if_neg hμv]
    change
      (if w = μ then
          ((transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).1, (C μ).2)
        else if w = v then
          ((transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).2, (C v).2)
        else C w) =
      (if w = μ then ({ (C μ).1 with answer := opinionToAnswer (C μ).2 }, (C μ).2)
        else if w = v then C v
        else C w)
    rw [htr]
  have hrank : ∀ w : Fin n, (C' w).1.rank = (C w).1.rank := by
    intro w
    have hw_state := congrFun hC'_eq w
    rw [hw_state]
    by_cases hwμ : w = μ
    · simp [hwμ]
    · by_cases hwv : w = v
      · simp [hwμ, hwv, hv_ne_mu]
      · simp [hwμ, hwv]
  have hinput : ∀ w : Fin n, (C' w).2 = (C w).2 := by
    intro w
    have hw_state := congrFun hC'_eq w
    rw [hw_state]
    by_cases hwμ : w = μ
    · simp [hwμ]
    · by_cases hwv : w = v
      · simp [hwμ, hwv, hv_ne_mu]
      · simp [hwμ, hwv]
  have hnA : nAOf C' = nAOf C := by
    simpa [C', P] using
      (nAOf_step_eq
        (trank := Rmax) (Rmax := Rmax)
        (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn) C μ v)
  have hmaj : majorityAnswer C' = majorityAnswer C := by
    simpa [C', P] using
      (majorityAnswer_step_eq
        (trank := Rmax) (Rmax := Rmax)
        (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn) C μ v)
  have hConsensus : IsConsensusConfig C' := by
    refine
      { allSettled := ?_
        ranks_inj := ?_
        input_rank := ?_
        allAnswerCorrect := ?_ }
    · intro w
      have hw_state := congrFun hC'_eq w
      rw [hw_state]
      by_cases hwμ : w = μ
      · simp [hwμ, hSwap.allSettled μ]
      · by_cases hwv : w = v
        · simp [hwμ, hwv, hv_ne_mu, hSwap.allSettled v]
        · simp [hwμ, hwv, hSwap.allSettled w]
    · intro w₁ w₂ heq
      apply hSwap.ranks_inj
      simpa [hrank w₁, hrank w₂] using heq
    · intro w
      rw [hinput w, hrank w, hnA]
      exact hSwap.input_rank w
    · intro w
      rw [hmaj]
      by_cases hwμ : w = μ
      · subst w
        have hμ_state := congrFun hC'_eq μ
        rw [hμ_state]
        simp [h_median_correct]
      · have hw_state := congrFun hC'_eq w
        rw [hw_state]
        by_cases hwv : w = v
        · subst w
          simp [hv_ne_mu, hv_correct]
        · simp [hwμ, hwv, hOnlyMedianWrong w hwμ]
  refine ⟨[(μ, v)], ?_⟩
  simp only [runPairs_cons, runPairs_nil]
  change RankingEndpoint C'
  exact ⟨⟨hConsensus.allSettled, hConsensus.ranks_inj⟩, Or.inr hConsensus⟩

theorem InSswap_bad_timer_zero_to_RankingEndpoint
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax : n ≤ Dmax) (hRmax : n ≤ Rmax)
    {C : Config (AgentState n) Opinion n}
    (hbad : BadRankingStart C) (hSwap : InSswap C)
    {μ : Fin n}
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (h_timer : (C μ).1.timer = 0)
    (hpar : ¬ n % 2 = 0) :
    ∃ L : List (Fin n × Fin n),
      RankingEndpoint
        (runPairs (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L) := by
  classical
  by_cases hOnly : ∀ w : Fin n, w ≠ μ → (C w).1.answer = majorityAnswer C
  · exact
      InSswap_bad_timer_zero_only_median_wrong_to_RankingEndpoint
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hSwap hμ_med h_timer hpar hOnly
  · push_neg at hOnly
    obtain ⟨w, hwm, hw_wrong⟩ := hOnly
    have hw_no_med : (C w).1.rank.val + 1 ≠ ceilHalf n := by
      intro hw_med
      apply hwm
      apply hSwap.ranks_inj
      apply Fin.eq_of_val_eq
      have hμ_val : (C μ).1.rank.val = ceilHalf n - 1 := by omega
      have hw_val : (C w).1.rank.val = ceilHalf n - 1 := by omega
      exact hw_val.trans hμ_val.symm
    exact
      InSswap_bad_timer_zero_wrong_nonmedian_to_RankingEndpoint
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hDmax hRmax hbad hSwap hμ_med hw_no_med h_timer hpar hw_wrong

theorem InSrank_timer_zero_swap_diff_to_RankingEndpoint
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax : n ≤ Dmax) (hRmax : n ≤ Rmax)
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (hv_no_med : (C v).1.rank.val + 1 ≠ ceilHalf n)
    (h_timer : (C μ).1.timer = 0)
    (h_swap : (C μ).1.rank < (C v).1.rank ∧ (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A)
    (hpar : ¬ n % 2 = 0)
    (h_post_diff : opinionToAnswer (C v).2 ≠ (C v).1.answer) :
    ∃ L : List (Fin n × Fin n),
      RankingEndpoint
        (runPairs (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L) := by
  have hstep :=
    trigger_reset_from_InSrank_timer_zero_swap_with_snapshot
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      (C := C) hC hμv hμ_med hv_no_med h_timer h_swap hpar h_post_diff
  obtain ⟨L, hEndpoint⟩ :=
    step_reset_snapshot_to_RankingEndpoint
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hDmax hRmax (C := C) (u := μ) (v := v) hstep
  exact ⟨(μ, v) :: L, hEndpoint⟩

theorem InSrank_timer_one_max_no_swap_diff_to_RankingEndpoint
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax : n ≤ Dmax) (hRmax : n ≤ Rmax)
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (hv_max : (C v).1.rank.val + 1 = n)
    (h_timer : (C μ).1.timer = 1)
    (h_no_swap : ¬((C μ).1.rank < (C v).1.rank ∧ (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A))
    (hpar : ¬ n % 2 = 0)
    (h_post_diff : opinionToAnswer (C μ).2 ≠ (C v).1.answer) :
    ∃ L : List (Fin n × Fin n),
      RankingEndpoint
        (runPairs (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L) := by
  have hstep :=
    trigger_reset_from_InSrank_timer_one_max_no_swap_with_snapshot
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      (C := C) hC hn4 hμv hμ_med hv_max h_timer h_no_swap hpar h_post_diff
  obtain ⟨L, hEndpoint⟩ :=
    step_reset_snapshot_to_RankingEndpoint
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hDmax hRmax (C := C) (u := μ) (v := v) hstep
  exact ⟨(μ, v) :: L, hEndpoint⟩

theorem InSrank_timer_one_max_swap_diff_to_RankingEndpoint
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax : n ≤ Dmax) (hRmax : n ≤ Rmax)
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (hv_max : (C v).1.rank.val + 1 = n)
    (h_timer : (C μ).1.timer = 1)
    (h_swap : (C μ).1.rank < (C v).1.rank ∧ (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A)
    (hpar : ¬ n % 2 = 0)
    (h_post_diff : opinionToAnswer (C v).2 ≠ (C v).1.answer) :
    ∃ L : List (Fin n × Fin n),
      RankingEndpoint
        (runPairs (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L) := by
  have hstep :=
    trigger_reset_from_InSrank_timer_one_max_swap_with_snapshot
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      (C := C) hC hn4 hμv hμ_med hv_max h_timer h_swap hpar h_post_diff
  obtain ⟨L, hEndpoint⟩ :=
    step_reset_snapshot_to_RankingEndpoint
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hDmax hRmax (C := C) (u := μ) (v := v) hstep
  exact ⟨(μ, v) :: L, hEndpoint⟩

theorem InSrank_timer_one_max_no_swap_same_then_zero_no_swap_diff_to_RankingEndpoint
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax : n ≤ Dmax) (hRmax : n ≤ Rmax)
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    {μ v w : Fin n} (hμv : μ ≠ v) (hμw : μ ≠ w) (hwv : w ≠ v)
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (hv_max : (C v).1.rank.val + 1 = n)
    (hw_no_med : (C w).1.rank.val + 1 ≠ ceilHalf n)
    (h_timer : (C μ).1.timer = 1)
    (h_no_swap_max : ¬((C μ).1.rank < (C v).1.rank ∧
      (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A))
    (h_no_swap_w : ¬((C μ).1.rank < (C w).1.rank ∧
      (C μ).2 = Opinion.B ∧ (C w).2 = Opinion.A))
    (hpar : ¬ n % 2 = 0)
    (h_post_same_max : opinionToAnswer (C μ).2 = (C v).1.answer)
    (h_post_diff_w : opinionToAnswer (C μ).2 ≠ (C w).1.answer) :
    ∃ L : List (Fin n × Fin n),
      RankingEndpoint
        (runPairs (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L) := by
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  let C₁ : Config (AgentState n) Opinion n := C.step P μ v
  have hstep :=
    no_reset_no_swap_max_timer_one_step_InSrank
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      (C := C) hC hn4 hμv hμ_med hv_max h_timer h_no_swap_max hpar h_post_same_max
  have hC₁ : InSrank C₁ := hstep.1
  have hμ_timer₁ : (C₁ μ).1.timer = 0 := hstep.2.1
  have hμ_med₁ : (C₁ μ).1.rank.val + 1 = ceilHalf n := hstep.2.2.2
  have hw_state₁ : C₁ w = C w := by
    dsimp [C₁, P]
    simp [Config.step, hμv, hμw.symm, hwv]
  have hμ_input₁ : (C₁ μ).2 = (C μ).2 := by
    dsimp [C₁, P]
    simp [Config.step, hμv]
  have hμ_rank₁ : (C₁ μ).1.rank = (C μ).1.rank := by
    have htrace :=
      no_reset_no_swap_max_timer_one_trace
        (trank := Rmax) (Rmax := Rmax)
        (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
        (hRank := rankDeltaOSSR_satisfies_fix)
        (C := C) hC hn4 hμv hμ_med hv_max h_timer h_no_swap_max hpar h_post_same_max
    have hfst := Config.step_fst_state P C hμv
    dsimp [C₁]
    rw [hfst]
    change (transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).1.rank =
      (C μ).1.rank
    rw [htrace]
  have hw_no_med₁ : (C₁ w).1.rank.val + 1 ≠ ceilHalf n := by
    rw [hw_state₁]
    exact hw_no_med
  have h_no_swap_w₁ :
      ¬((C₁ μ).1.rank < (C₁ w).1.rank ∧
        (C₁ μ).2 = Opinion.B ∧ (C₁ w).2 = Opinion.A) := by
    rintro ⟨hrank, hB, hA⟩
    exact h_no_swap_w ⟨by rwa [hμ_rank₁, hw_state₁] at hrank,
      by rwa [hμ_input₁] at hB,
      by rwa [hw_state₁] at hA⟩
  have h_post_diff_w₁ : opinionToAnswer (C₁ μ).2 ≠ (C₁ w).1.answer := by
    rw [hμ_input₁, hw_state₁]
    exact h_post_diff_w
  obtain ⟨Ltail, hEndpoint⟩ :=
    InSrank_timer_zero_no_swap_diff_to_RankingEndpoint
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hDmax hRmax hC₁ hμw hμ_med₁ hw_no_med₁ hμ_timer₁
      h_no_swap_w₁ hpar h_post_diff_w₁
  refine ⟨(μ, v) :: Ltail, ?_⟩
  change RankingEndpoint (runPairs P (C.step P μ v) Ltail)
  exact hEndpoint

theorem InSswap_bad_timer_one_only_median_wrong_to_RankingEndpoint
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n)
    {C : Config (AgentState n) Opinion n}
    (hSwap : InSswap C)
    {μ : Fin n}
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (h_timer : (C μ).1.timer = 1)
    (hpar : ¬ n % 2 = 0)
    (hOnlyMedianWrong :
      ∀ w : Fin n, w ≠ μ → (C w).1.answer = majorityAnswer C) :
    ∃ L : List (Fin n × Fin n),
      RankingEndpoint
        (runPairs (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L) := by
  classical
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  obtain ⟨v, hμv, hv_max⟩ :=
    hSwap.toInSrank.exists_max_rank_ne_median hn4 hμ_med
  have hv_ne_mu : v ≠ μ := hμv.symm
  have hv_no_med : (C v).1.rank.val + 1 ≠ ceilHalf n := by
    intro hv_med
    apply hμv
    apply hSwap.ranks_inj
    apply Fin.eq_of_val_eq
    have hμ_val : (C μ).1.rank.val = ceilHalf n - 1 := by omega
    have hv_val : (C v).1.rank.val = ceilHalf n - 1 := by omega
    exact hμ_val.trans hv_val.symm
  have h_no_swap :
      ¬((C μ).1.rank < (C v).1.rank ∧
        (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A) :=
    hSwap.swap_condition_false μ v
  have h_median_correct :
      opinionToAnswer (C μ).2 = majorityAnswer C :=
    opinionToAnswer_median_eq_majorityAnswer_odd hSwap hμ_med hpar
  have hv_correct : (C v).1.answer = majorityAnswer C :=
    hOnlyMedianWrong v hv_ne_mu
  have h_post_same : opinionToAnswer (C μ).2 = (C v).1.answer := by
    rw [h_median_correct, hv_correct]
  let C' : Config (AgentState n) Opinion n := C.step P μ v
  have htr :=
    no_reset_no_swap_max_timer_one_trace
      (trank := Rmax) (Rmax := Rmax)
      (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn)
      (hRank := rankDeltaOSSR_satisfies_fix)
      (C := C) hSwap.toInSrank hn4 hμv hμ_med hv_max h_timer
      h_no_swap hpar h_post_same
  have hC'_eq : C' =
      fun w => if w = μ then
          ({ (C μ).1 with answer := opinionToAnswer (C μ).2, timer := 0 }, (C μ).2)
        else if w = v then C v
        else C w := by
    funext w
    dsimp [C', P]
    unfold Config.step
    simp only [if_neg hμv]
    change
      (if w = μ then
          ((transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).1, (C μ).2)
        else if w = v then
          ((transitionPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn) (C μ, C v)).2, (C v).2)
        else C w) =
      (if w = μ then
          ({ (C μ).1 with answer := opinionToAnswer (C μ).2, timer := 0 }, (C μ).2)
        else if w = v then C v
        else C w)
    rw [htr]
  have hrank : ∀ w : Fin n, (C' w).1.rank = (C w).1.rank := by
    intro w
    have hw_state := congrFun hC'_eq w
    rw [hw_state]
    by_cases hwμ : w = μ
    · simp [hwμ]
    · by_cases hwv : w = v
      · simp [hwμ, hwv, hv_ne_mu]
      · simp [hwμ, hwv]
  have hinput : ∀ w : Fin n, (C' w).2 = (C w).2 := by
    intro w
    have hw_state := congrFun hC'_eq w
    rw [hw_state]
    by_cases hwμ : w = μ
    · simp [hwμ]
    · by_cases hwv : w = v
      · simp [hwμ, hwv, hv_ne_mu]
      · simp [hwμ, hwv]
  have hnA : nAOf C' = nAOf C := by
    simpa [C', P] using
      (nAOf_step_eq
        (trank := Rmax) (Rmax := Rmax)
        (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn) C μ v)
  have hmaj : majorityAnswer C' = majorityAnswer C := by
    simpa [C', P] using
      (majorityAnswer_step_eq
        (trank := Rmax) (Rmax := Rmax)
        (rankDelta := rankDeltaOSSR Rmax Emax Dmax hn) C μ v)
  have hConsensus : IsConsensusConfig C' := by
    refine
      { allSettled := ?_
        ranks_inj := ?_
        input_rank := ?_
        allAnswerCorrect := ?_ }
    · intro w
      have hw_state := congrFun hC'_eq w
      rw [hw_state]
      by_cases hwμ : w = μ
      · simp [hwμ, hSwap.allSettled μ]
      · by_cases hwv : w = v
        · simp [hwμ, hwv, hv_ne_mu, hSwap.allSettled v]
        · simp [hwμ, hwv, hSwap.allSettled w]
    · intro w₁ w₂ heq
      apply hSwap.ranks_inj
      simpa [hrank w₁, hrank w₂] using heq
    · intro w
      rw [hinput w, hrank w, hnA]
      exact hSwap.input_rank w
    · intro w
      rw [hmaj]
      by_cases hwμ : w = μ
      · subst w
        have hμ_state := congrFun hC'_eq μ
        rw [hμ_state]
        simp [h_median_correct]
      · have hw_state := congrFun hC'_eq w
        rw [hw_state]
        by_cases hwv : w = v
        · subst w
          simp [hv_ne_mu, hv_correct]
        · simp [hwμ, hwv, hOnlyMedianWrong w hwμ]
  refine ⟨[(μ, v)], ?_⟩
  simp only [runPairs_cons, runPairs_nil]
  change RankingEndpoint C'
  exact ⟨⟨hConsensus.allSettled, hConsensus.ranks_inj⟩, Or.inr hConsensus⟩

theorem InSswap_bad_timer_one_to_RankingEndpoint
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax : n ≤ Dmax) (hRmax : n ≤ Rmax)
    {C : Config (AgentState n) Opinion n}
    (hbad : BadRankingStart C) (hSwap : InSswap C)
    {μ : Fin n}
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (h_timer : (C μ).1.timer = 1)
    (hpar : ¬ n % 2 = 0) :
    ∃ L : List (Fin n × Fin n),
      RankingEndpoint
        (runPairs (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L) := by
  classical
  obtain ⟨v, hμv, hv_max⟩ :=
    hSwap.toInSrank.exists_max_rank_ne_median hn4 hμ_med
  have h_no_swap_max :
      ¬((C μ).1.rank < (C v).1.rank ∧
        (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A) :=
    hSwap.swap_condition_false μ v
  have h_median_correct :
      opinionToAnswer (C μ).2 = majorityAnswer C :=
    opinionToAnswer_median_eq_majorityAnswer_odd hSwap hμ_med hpar
  by_cases hv_wrong : (C v).1.answer ≠ majorityAnswer C
  · have h_post_diff : opinionToAnswer (C μ).2 ≠ (C v).1.answer := by
      rw [h_median_correct]
      exact hv_wrong.symm
    exact
      InSrank_timer_one_max_no_swap_diff_to_RankingEndpoint
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hDmax hRmax hbad.1 hμv hμ_med hv_max h_timer
        h_no_swap_max hpar h_post_diff
  · have hv_correct : (C v).1.answer = majorityAnswer C := by
      exact not_not.mp hv_wrong
    by_cases hOnly : ∀ w : Fin n, w ≠ μ → (C w).1.answer = majorityAnswer C
    · exact
        InSswap_bad_timer_one_only_median_wrong_to_RankingEndpoint
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hn4 hSwap hμ_med h_timer hpar hOnly
    · push_neg at hOnly
      obtain ⟨w, hwm, hw_wrong⟩ := hOnly
      have hwv : w ≠ v := by
        intro h
        subst w
        exact hw_wrong hv_correct
      have hw_no_med : (C w).1.rank.val + 1 ≠ ceilHalf n := by
        intro hw_med
        apply hwm
        apply hSwap.ranks_inj
        apply Fin.eq_of_val_eq
        have hμ_val : (C μ).1.rank.val = ceilHalf n - 1 := by omega
        have hw_val : (C w).1.rank.val = ceilHalf n - 1 := by omega
        exact hw_val.trans hμ_val.symm
      have h_no_swap_w :
          ¬((C μ).1.rank < (C w).1.rank ∧
            (C μ).2 = Opinion.B ∧ (C w).2 = Opinion.A) :=
        hSwap.swap_condition_false μ w
      have h_post_same_max : opinionToAnswer (C μ).2 = (C v).1.answer := by
        rw [h_median_correct, hv_correct]
      have h_post_diff_w : opinionToAnswer (C μ).2 ≠ (C w).1.answer := by
        rw [h_median_correct]
        exact hw_wrong.symm
      exact
        InSrank_timer_one_max_no_swap_same_then_zero_no_swap_diff_to_RankingEndpoint
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hn4 hDmax hRmax hbad.1 hμv hwm.symm hwv hμ_med hv_max hw_no_med h_timer
          h_no_swap_max h_no_swap_w hpar h_post_same_max h_post_diff_w

theorem InSswap_bad_odd_to_RankingEndpoint
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax : n ≤ Dmax) (hRmax : n ≤ Rmax)
    {C : Config (AgentState n) Opinion n}
    (hbad : BadRankingStart C) (hSwap : InSswap C)
    (hpar : ¬ n % 2 = 0) :
    ∃ L : List (Fin n × Fin n),
      RankingEndpoint
        (runPairs (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L) := by
  obtain ⟨μ, hμ_med, htimer⟩ := hbad.exists_median_timer_zero_or_one
  rcases htimer with htimer0 | htimer1
  · exact
      InSswap_bad_timer_zero_to_RankingEndpoint
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hDmax hRmax hbad hSwap hμ_med htimer0 hpar
  · exact
      InSswap_bad_timer_one_to_RankingEndpoint
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hDmax hRmax hbad hSwap hμ_med htimer1 hpar

theorem ranking_goal_of_InSswap_bad_odd
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax : n ≤ Dmax) (hRmax : n ≤ Rmax)
    {C : Config (AgentState n) Opinion n}
    (hbad : BadRankingStart C) (hSwap : InSswap C)
    (hpar : ¬ n % 2 = 0) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t)) := by
  obtain ⟨L, hEndpoint⟩ :=
    InSswap_bad_odd_to_RankingEndpoint
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hDmax hRmax hbad hSwap hpar
  exact
    ranking_goal_of_runPairs_RankingEndpoint
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      (C := C) (L := L) hEndpoint

theorem ranking_goal_of_bad_odd_count_zero
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax : n ≤ Dmax) (hRmax : n ≤ Rmax)
    {C : Config (AgentState n) Opinion n}
    (hbad : BadRankingStart C)
    (hzero : misorderedCount C = 0)
    (hpar : ¬ n % 2 = 0) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t)) := by
  exact
    ranking_goal_of_InSswap_bad_odd
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hDmax hRmax hbad
      (InSswap_of_InSrank_of_count_zero hbad.1 hzero)
      hpar

theorem BadRankingStart_odd_to_RankingEndpoint
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax : n ≤ Dmax) (hRmax : n ≤ Rmax)
    {C : Config (AgentState n) Opinion n}
    (hbad : BadRankingStart C)
    (hpar : ¬ n % 2 = 0) :
    ∃ L : List (Fin n × Fin n),
      RankingEndpoint
        (runPairs (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L) := by
  classical
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  obtain hReach :=
    InSrank_reaches_RankingEndpoint_or_InSswap
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hDmax hRmax hbad.1
  rcases hReach with hEndpoint | hSwapReach
  · exact hEndpoint
  · obtain ⟨L₁, hSwap₁⟩ := hSwapReach
    let C₁ : Config (AgentState n) Opinion n := runPairs P C L₁
    by_cases hDone : RankingEndpoint C₁
    · exact ⟨L₁, by simpa [C₁, P] using hDone⟩
    · have hbad₁ : BadRankingStart C₁ := by
        exact ⟨by simpa [C₁, P] using hSwap₁.toInSrank, hDone⟩
      have hSwapC₁ : InSswap C₁ := by
        simpa [C₁, P] using hSwap₁
      obtain ⟨L₂, hEndpoint₂⟩ :=
        InSswap_bad_odd_to_RankingEndpoint
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hn4 hDmax hRmax hbad₁ hSwapC₁ hpar
      refine ⟨L₁ ++ L₂, ?_⟩
      rw [runPairs_append]
      change RankingEndpoint (runPairs P C₁ L₂)
      exact hEndpoint₂

theorem BadRankingStart_odd_max_partner_diff_to_RankingEndpoint
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax : n ≤ Dmax) (hRmax : n ≤ Rmax)
    {C : Config (AgentState n) Opinion n} (hbad : BadRankingStart C)
    (hpar : ¬ n % 2 = 0)
    (hPartner :
      ∀ μ : Fin n,
        (C μ).1.rank.val + 1 = ceilHalf n →
        ((C μ).1.timer = 0 ∨ (C μ).1.timer = 1) →
        ∃ v : Fin n,
          μ ≠ v ∧
          (C v).1.rank.val + 1 = n ∧
          (¬((C μ).1.rank < (C v).1.rank ∧
              (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A) →
            opinionToAnswer (C μ).2 ≠ (C v).1.answer) ∧
          (((C μ).1.rank < (C v).1.rank ∧
              (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A) →
            opinionToAnswer (C v).2 ≠ (C v).1.answer)) :
    ∃ L : List (Fin n × Fin n),
      RankingEndpoint
        (runPairs (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L) := by
  obtain ⟨μ, hμ_med, htimer⟩ := hbad.exists_median_timer_zero_or_one
  obtain ⟨v, hμv, hv_max, hdiff_no_swap, hdiff_swap⟩ :=
    hPartner μ hμ_med htimer
  have hv_no_med : (C v).1.rank.val + 1 ≠ ceilHalf n := by
    unfold ceilHalf
    omega
  by_cases hswap :
      (C μ).1.rank < (C v).1.rank ∧ (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A
  · rcases htimer with htimer0 | htimer1
    · exact
        InSrank_timer_zero_swap_diff_to_RankingEndpoint
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hn4 hDmax hRmax hbad.1 hμv hμ_med hv_no_med htimer0 hswap hpar
          (hdiff_swap hswap)
    · exact
        InSrank_timer_one_max_swap_diff_to_RankingEndpoint
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hn4 hDmax hRmax hbad.1 hμv hμ_med hv_max htimer1 hswap hpar
          (hdiff_swap hswap)
  · rcases htimer with htimer0 | htimer1
    · exact
        InSrank_timer_zero_no_swap_diff_to_RankingEndpoint
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hn4 hDmax hRmax hbad.1 hμv hμ_med hv_no_med htimer0 hswap hpar
          (hdiff_no_swap hswap)
    · exact
        InSrank_timer_one_max_no_swap_diff_to_RankingEndpoint
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hn4 hDmax hRmax hbad.1 hμv hμ_med hv_max htimer1 hswap hpar
          (hdiff_no_swap hswap)

theorem ranking_of_no_reset_odd_with_bad_partner_handler
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (hRmax : n ≤ Rmax)
    (hpar : ¬ n % 2 = 0)
    (C : Config (AgentState n) Opinion n)
    (hNoReset : ∀ w : Fin n, (C w).1.role ≠ .Resetting)
    (hPartner :
      ∀ Cbad : Config (AgentState n) Opinion n,
        BadRankingStart Cbad →
        ∀ μ : Fin n,
          (Cbad μ).1.rank.val + 1 = ceilHalf n →
          ((Cbad μ).1.timer = 0 ∨ (Cbad μ).1.timer = 1) →
          ∃ v : Fin n,
            μ ≠ v ∧
            (Cbad v).1.rank.val + 1 = n ∧
            (¬((Cbad μ).1.rank < (Cbad v).1.rank ∧
                (Cbad μ).2 = Opinion.B ∧ (Cbad v).2 = Opinion.A) →
              opinionToAnswer (Cbad μ).2 ≠ (Cbad v).1.answer) ∧
            (((Cbad μ).1.rank < (Cbad v).1.rank ∧
                (Cbad μ).2 = Opinion.B ∧ (Cbad v).2 = Opinion.A) →
              opinionToAnswer (Cbad v).2 ≠ (Cbad v).1.answer)) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t)) := by
  exact
    ranking_of_no_reset_with_bad_start_handler
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hEmax hDmax hRmax C hNoReset
      (fun Cbad hbad =>
        BadRankingStart_odd_max_partner_diff_to_RankingEndpoint
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hn4 hDmax hRmax hbad hpar (hPartner Cbad hbad))

theorem ranking_of_no_reset_odd
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (hRmax : n ≤ Rmax)
    (hpar : ¬ n % 2 = 0)
    (C : Config (AgentState n) Opinion n)
    (hNoReset : ∀ w : Fin n, (C w).1.role ≠ .Resetting) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t)) := by
  exact
    ranking_of_no_reset_with_bad_start_handler
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hEmax hDmax hRmax C hNoReset
      (fun Cbad hbad =>
        BadRankingStart_odd_to_RankingEndpoint
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hn4 hDmax hRmax hbad hpar)

theorem ranking_goal_of_bad_timer_zero_no_swap_diff
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax : n ≤ Dmax) (hRmax : n ≤ Rmax)
    {C : Config (AgentState n) Opinion n} (hbad : BadRankingStart C)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (hv_no_med : (C v).1.rank.val + 1 ≠ ceilHalf n)
    (h_timer : (C μ).1.timer = 0)
    (h_no_swap : ¬((C μ).1.rank < (C v).1.rank ∧ (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A))
    (hpar : ¬ n % 2 = 0)
    (h_post_diff : opinionToAnswer (C μ).2 ≠ (C v).1.answer) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t)) := by
  obtain ⟨L, hEndpoint⟩ :=
    InSrank_timer_zero_no_swap_diff_to_RankingEndpoint
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hDmax hRmax hbad.1 hμv hμ_med hv_no_med h_timer h_no_swap hpar h_post_diff
  exact
    ranking_goal_of_runPairs_RankingEndpoint
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      (C := C) (L := L) hEndpoint

theorem ranking_goal_of_bad_timer_zero_swap_diff
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax : n ≤ Dmax) (hRmax : n ≤ Rmax)
    {C : Config (AgentState n) Opinion n} (hbad : BadRankingStart C)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (hv_no_med : (C v).1.rank.val + 1 ≠ ceilHalf n)
    (h_timer : (C μ).1.timer = 0)
    (h_swap : (C μ).1.rank < (C v).1.rank ∧ (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A)
    (hpar : ¬ n % 2 = 0)
    (h_post_diff : opinionToAnswer (C v).2 ≠ (C v).1.answer) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t)) := by
  obtain ⟨L, hEndpoint⟩ :=
    InSrank_timer_zero_swap_diff_to_RankingEndpoint
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hDmax hRmax hbad.1 hμv hμ_med hv_no_med h_timer h_swap hpar h_post_diff
  exact
    ranking_goal_of_runPairs_RankingEndpoint
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      (C := C) (L := L) hEndpoint

theorem ranking_goal_of_bad_timer_one_max_no_swap_diff
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax : n ≤ Dmax) (hRmax : n ≤ Rmax)
    {C : Config (AgentState n) Opinion n} (hbad : BadRankingStart C)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (hv_max : (C v).1.rank.val + 1 = n)
    (h_timer : (C μ).1.timer = 1)
    (h_no_swap : ¬((C μ).1.rank < (C v).1.rank ∧ (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A))
    (hpar : ¬ n % 2 = 0)
    (h_post_diff : opinionToAnswer (C μ).2 ≠ (C v).1.answer) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t)) := by
  obtain ⟨L, hEndpoint⟩ :=
    InSrank_timer_one_max_no_swap_diff_to_RankingEndpoint
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hDmax hRmax hbad.1 hμv hμ_med hv_max h_timer h_no_swap hpar h_post_diff
  exact
    ranking_goal_of_runPairs_RankingEndpoint
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      (C := C) (L := L) hEndpoint

theorem ranking_goal_of_bad_timer_one_max_no_swap_same_then_zero_no_swap_diff
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax : n ≤ Dmax) (hRmax : n ≤ Rmax)
    {C : Config (AgentState n) Opinion n} (hbad : BadRankingStart C)
    {μ v w : Fin n} (hμv : μ ≠ v) (hμw : μ ≠ w) (hwv : w ≠ v)
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (hv_max : (C v).1.rank.val + 1 = n)
    (hw_no_med : (C w).1.rank.val + 1 ≠ ceilHalf n)
    (h_timer : (C μ).1.timer = 1)
    (h_no_swap_max : ¬((C μ).1.rank < (C v).1.rank ∧
      (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A))
    (h_no_swap_w : ¬((C μ).1.rank < (C w).1.rank ∧
      (C μ).2 = Opinion.B ∧ (C w).2 = Opinion.A))
    (hpar : ¬ n % 2 = 0)
    (h_post_same_max : opinionToAnswer (C μ).2 = (C v).1.answer)
    (h_post_diff_w : opinionToAnswer (C μ).2 ≠ (C w).1.answer) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t)) := by
  obtain ⟨L, hEndpoint⟩ :=
    InSrank_timer_one_max_no_swap_same_then_zero_no_swap_diff_to_RankingEndpoint
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hDmax hRmax hbad.1 hμv hμw hwv hμ_med hv_max hw_no_med h_timer
      h_no_swap_max h_no_swap_w hpar h_post_same_max h_post_diff_w
  exact
    ranking_goal_of_runPairs_RankingEndpoint
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      (C := C) (L := L) hEndpoint

theorem ranking_goal_of_bad_timer_one_max_swap_diff
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax : n ≤ Dmax) (hRmax : n ≤ Rmax)
    {C : Config (AgentState n) Opinion n} (hbad : BadRankingStart C)
    {μ v : Fin n} (hμv : μ ≠ v)
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (hv_max : (C v).1.rank.val + 1 = n)
    (h_timer : (C μ).1.timer = 1)
    (h_swap : (C μ).1.rank < (C v).1.rank ∧ (C μ).2 = Opinion.B ∧ (C v).2 = Opinion.A)
    (hpar : ¬ n % 2 = 0)
    (h_post_diff : opinionToAnswer (C v).2 ≠ (C v).1.answer) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t)) := by
  obtain ⟨L, hEndpoint⟩ :=
    InSrank_timer_one_max_swap_diff_to_RankingEndpoint
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hDmax hRmax hbad.1 hμv hμ_med hv_max h_timer h_swap hpar h_post_diff
  exact
    ranking_goal_of_runPairs_RankingEndpoint
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      (C := C) (L := L) hEndpoint

theorem follower_clean_to_ranking_goal_or_bad_start
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (hRmax : n ≤ Rmax)
    (C : Config (AgentState n) Opinion n)
    (hClean : FollowerClean C) :
    (∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t))) ∨
    ∃ L : List (Fin n × Fin n),
      BadRankingStart
        (runPairs (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L) := by
  classical
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  obtain ⟨L₁, hNoReset₁⟩ :=
    follower_clean_to_no_reset
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 C hClean
  let C₁ : Config (AgentState n) Opinion n := runPairs P C L₁
  have hNoResetC₁ : ∀ w : Fin n, (C₁ w).1.role ≠ .Resetting := by
    simpa [C₁, P] using hNoReset₁
  obtain ⟨L₂, h₂⟩ :=
    phase12_no_reset_to_RankingEndpoint_or_InSrank
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hEmax hDmax hRmax C₁ hNoResetC₁
  rcases h₂ with hSrank | hEndpoint
  · by_cases hDone : RankingEndpoint (runPairs P C₁ L₂)
    · exact Or.inl
        (ranking_goal_of_runPairs_RankingEndpoint
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          (C := C) (L := L₁ ++ L₂)
          (by
            rw [runPairs_append]
            change RankingEndpoint (runPairs P C₁ L₂)
            exact hDone))
    · exact Or.inr ⟨L₁ ++ L₂, by
        rw [runPairs_append]
        exact ⟨hSrank, hDone⟩⟩
  · exact Or.inl
      (ranking_goal_of_runPairs_RankingEndpoint
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        (C := C) (L := L₁ ++ L₂)
        (by
          rw [runPairs_append]
          change RankingEndpoint (runPairs P C₁ L₂)
          exact hEndpoint))

theorem follower_clean_to_ranking_goal_odd
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (hRmax : n ≤ Rmax)
    (hpar : ¬ n % 2 = 0)
    (C : Config (AgentState n) Opinion n)
    (hClean : FollowerClean C) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t)) := by
  classical
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  obtain h | hbadReach :=
    follower_clean_to_ranking_goal_or_bad_start
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hEmax hDmax hRmax C hClean
  · exact h
  · obtain ⟨L₁, hbad₁⟩ := hbadReach
    let C₁ : Config (AgentState n) Opinion n := runPairs P C L₁
    have hbadC₁ : BadRankingStart C₁ := by
      simpa [C₁, P] using hbad₁
    obtain ⟨L₂, hEndpoint₂⟩ :=
      BadRankingStart_odd_to_RankingEndpoint
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hDmax hRmax hbadC₁ hpar
    have hEndpoint_total : RankingEndpoint (runPairs P C (L₁ ++ L₂)) := by
      rw [runPairs_append]
      change RankingEndpoint (runPairs P C₁ L₂)
      exact hEndpoint₂
    exact
      ranking_goal_of_runPairs_RankingEndpoint
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        (C := C) (L := L₁ ++ L₂) hEndpoint_total

theorem follower_clean_to_ranking_goal_even
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (hRmax : n ≤ Rmax)
    (hpar : n % 2 = 0)
    (C : Config (AgentState n) Opinion n)
    (hClean : FollowerClean C) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t)) := by
  classical
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  obtain h | hbadReach :=
    follower_clean_to_ranking_goal_or_bad_start
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hEmax hDmax hRmax C hClean
  · exact h
  · obtain ⟨L₁, hbad₁⟩ := hbadReach
    let C₁ : Config (AgentState n) Opinion n := runPairs P C L₁
    have hbadC₁ : BadRankingStart C₁ := by
      simpa [C₁, P] using hbad₁
    obtain ⟨L₂, hEndpoint₂⟩ :=
      BadRankingStart_even_to_RankingEndpoint
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hDmax hRmax hbadC₁ hpar
    have hEndpoint_total : RankingEndpoint (runPairs P C (L₁ ++ L₂)) := by
      rw [runPairs_append]
      change RankingEndpoint (runPairs P C₁ L₂)
      exact hEndpoint₂
    exact
      ranking_goal_of_runPairs_RankingEndpoint
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        (C := C) (L := L₁ ++ L₂) hEndpoint_total

theorem follower_dormant_or_nonresetting_to_ranking_goal_or_bad_start
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (hRmax : n ≤ Rmax)
    (C : Config (AgentState n) Opinion n)
    (hClean : FollowerDormantOrNonResetting C) :
    (∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t))) ∨
    ∃ L : List (Fin n × Fin n),
      BadRankingStart
        (runPairs (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L) := by
  classical
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  obtain ⟨L₁, hNoReset₁⟩ :=
    follower_dormant_or_nonresetting_to_no_reset
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 C hClean
  let C₁ : Config (AgentState n) Opinion n := runPairs P C L₁
  have hNoResetC₁ : ∀ w : Fin n, (C₁ w).1.role ≠ .Resetting := by
    simpa [C₁, P] using hNoReset₁
  obtain ⟨L₂, h₂⟩ :=
    phase12_no_reset_to_RankingEndpoint_or_InSrank
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hEmax hDmax hRmax C₁ hNoResetC₁
  rcases h₂ with hSrank | hEndpoint
  · by_cases hDone : RankingEndpoint (runPairs P C₁ L₂)
    · exact Or.inl
        (ranking_goal_of_runPairs_RankingEndpoint
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          (C := C) (L := L₁ ++ L₂)
          (by
            rw [runPairs_append]
            change RankingEndpoint (runPairs P C₁ L₂)
            exact hDone))
    · exact Or.inr ⟨L₁ ++ L₂, by
        rw [runPairs_append]
        exact ⟨hSrank, hDone⟩⟩
  · exact Or.inl
      (ranking_goal_of_runPairs_RankingEndpoint
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        (C := C) (L := L₁ ++ L₂)
        (by
          rw [runPairs_append]
          change RankingEndpoint (runPairs P C₁ L₂)
          exact hEndpoint))

theorem follower_dormant_or_nonresetting_to_ranking_goal_odd
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (hRmax : n ≤ Rmax)
    (hpar : ¬ n % 2 = 0)
    (C : Config (AgentState n) Opinion n)
    (hClean : FollowerDormantOrNonResetting C) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t)) := by
  classical
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  obtain h | hbadReach :=
    follower_dormant_or_nonresetting_to_ranking_goal_or_bad_start
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hEmax hDmax hRmax C hClean
  · exact h
  · obtain ⟨L₁, hbad₁⟩ := hbadReach
    let C₁ : Config (AgentState n) Opinion n := runPairs P C L₁
    have hbadC₁ : BadRankingStart C₁ := by
      simpa [C₁, P] using hbad₁
    obtain ⟨L₂, hEndpoint₂⟩ :=
      BadRankingStart_odd_to_RankingEndpoint
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hDmax hRmax hbadC₁ hpar
    have hEndpoint_total : RankingEndpoint (runPairs P C (L₁ ++ L₂)) := by
      rw [runPairs_append]
      change RankingEndpoint (runPairs P C₁ L₂)
      exact hEndpoint₂
    exact
      ranking_goal_of_runPairs_RankingEndpoint
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        (C := C) (L := L₁ ++ L₂) hEndpoint_total

theorem follower_dormant_or_nonresetting_to_ranking_goal_even
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (hRmax : n ≤ Rmax)
    (hpar : n % 2 = 0)
    (C : Config (AgentState n) Opinion n)
    (hClean : FollowerDormantOrNonResetting C) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t)) := by
  classical
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  obtain h | hbadReach :=
    follower_dormant_or_nonresetting_to_ranking_goal_or_bad_start
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hEmax hDmax hRmax C hClean
  · exact h
  · obtain ⟨L₁, hbad₁⟩ := hbadReach
    let C₁ : Config (AgentState n) Opinion n := runPairs P C L₁
    have hbadC₁ : BadRankingStart C₁ := by
      simpa [C₁, P] using hbad₁
    obtain ⟨L₂, hEndpoint₂⟩ :=
      BadRankingStart_even_to_RankingEndpoint
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hDmax hRmax hbadC₁ hpar
    have hEndpoint_total : RankingEndpoint (runPairs P C (L₁ ++ L₂)) := by
      rw [runPairs_append]
      change RankingEndpoint (runPairs P C₁ L₂)
      exact hEndpoint₂
    exact
      ranking_goal_of_runPairs_RankingEndpoint
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        (C := C) (L := L₁ ++ L₂) hEndpoint_total

theorem ranking_of_no_reset_by_parity
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (hRmax : n ≤ Rmax)
    (C : Config (AgentState n) Opinion n)
    (hNoReset : ∀ w : Fin n, (C w).1.role ≠ .Resetting) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t)) := by
  by_cases hpar : n % 2 = 0
  · exact
      ranking_of_no_reset_even
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hEmax hDmax hRmax hpar C hNoReset
  · exact
      ranking_of_no_reset_odd
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hEmax hDmax hRmax hpar C hNoReset

theorem follower_dormant_or_nonresetting_to_ranking_goal_by_parity
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (hRmax : n ≤ Rmax)
    (C : Config (AgentState n) Opinion n)
    (hClean : FollowerDormantOrNonResetting C) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t)) := by
  by_cases hpar : n % 2 = 0
  · exact
      follower_dormant_or_nonresetting_to_ranking_goal_even
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hEmax hDmax hRmax hpar C hClean
  · exact
      follower_dormant_or_nonresetting_to_ranking_goal_odd
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hEmax hDmax hRmax hpar C hClean

theorem ranking_from_all_resetting_pos_with_leader
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hRmax : 0 < Rmax) (hDmax_n : n ≤ Dmax)
    (C : Config (AgentState n) Opinion n)
    (hAllReset : ∀ w : Fin n, (C w).1.role = .Resetting)
    (hAllPos : ∀ w : Fin n, 0 < (C w).1.resetcount)
    (hHasL : ∃ ℓ : Fin n, (C ℓ).1.leader = .L) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t)) := by
  obtain ⟨L, hEndpoint⟩ :=
    all_resetting_pos_with_leader_to_RankingEndpoint
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hRmax hDmax_n C hAllReset hAllPos hHasL
  exact
    ranking_goal_of_runPairs_RankingEndpoint
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      (C := C) (L := L) hEndpoint

theorem ranking_from_known_reset_entry
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (hRmax : n ≤ Rmax)
    (C : Config (AgentState n) Opinion n)
    (hEntry :
      (∀ w : Fin n, (C w).1.role ≠ .Resetting) ∨
      FollowerDormantOrNonResetting C ∨
      ((∃ r : Fin n, (C r).1.role = .Resetting ∧
          n ≤ (C r).1.resetcount ∧ (C r).1.leader = .L) ∧
        ∀ w : Fin n, (C w).1.role = .Resetting → 0 < (C w).1.resetcount) ∨
      ((∀ w : Fin n, (C w).1.role = .Resetting) ∧
        (∀ w : Fin n, 0 < (C w).1.resetcount) ∧
        ∃ r : Fin n, (C r).1.leader = .L)) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t)) := by
  rcases hEntry with hNoReset | hEntry
  · exact
      ranking_of_no_reset_by_parity
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hEmax hDmax hRmax C hNoReset
  rcases hEntry with hClean | hSnapshot
  · exact
      follower_dormant_or_nonresetting_to_ranking_goal_by_parity
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hEmax hDmax hRmax C hClean
  rcases hSnapshot with hSnapshot | hAllResetPos
  · exact
      ranking_goal_of_reset_snapshot
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hDmax hRmax (C := C) hSnapshot.1 hSnapshot.2
  · have hRmax_pos : 0 < Rmax := by
      have hn_pos : 0 < n := by omega
      exact Nat.lt_of_lt_of_le hn_pos hRmax
    exact
      ranking_from_all_resetting_pos_with_leader
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hRmax_pos hDmax C hAllResetPos.1 hAllResetPos.2.1 hAllResetPos.2.2

theorem ranking_from_all_resetting_zero_no_leader
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (hRmax : n ≤ Rmax)
    (C : Config (AgentState n) Opinion n)
    (hAllReset : ∀ w : Fin n, (C w).1.role = .Resetting)
    (hAllZero : ∀ w : Fin n, (C w).1.resetcount = 0)
    (hNoLeader : ∀ w : Fin n, (C w).1.leader ≠ .L) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t)) := by
  have hClean : FollowerDormantOrNonResetting C := by
    intro w
    refine Or.inl ⟨hAllReset w, hAllZero w, ?_⟩
    cases hleader : (C w).1.leader with
    | L => exact False.elim ((hNoLeader w) hleader)
    | F => rfl
  exact
    follower_dormant_or_nonresetting_to_ranking_goal_by_parity
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hEmax hDmax hRmax C hClean

theorem ranking_from_all_resetting_zero_unique_leader
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax : n ≤ Dmax) (hRmax : n ≤ Rmax)
    (C : Config (AgentState n) Opinion n)
    (hAllReset : ∀ w : Fin n, (C w).1.role = .Resetting)
    (hAllZero : ∀ w : Fin n, (C w).1.resetcount = 0)
    (hUniqueLeader : ∃! ℓ : Fin n, (C ℓ).1.leader = .L) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t)) := by
  have hDormant : IsDormantConfig C := by
    refine ⟨hAllReset, hAllZero, hUniqueLeader, ?_⟩
    intro w
    cases (C w).1.leader <;> simp
  have hRmax_pos : 0 < Rmax := by
    have hn_pos : 0 < n := by omega
    exact Nat.lt_of_lt_of_le hn_pos hRmax
  have hDmax_pos : 0 < Dmax := by
    have hn_pos : 0 < n := by omega
    exact Nat.lt_of_lt_of_le hn_pos hDmax
  obtain ⟨L, hEndpoint⟩ :=
    dormant_to_RankingEndpoint
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hRmax_pos hDmax_pos C hDormant
  exact
    ranking_goal_of_runPairs_RankingEndpoint
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      (C := C) (L := L) hEndpoint

theorem ranking_from_settled_root_zero_resetting
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (hRmax : n ≤ Rmax)
    (C : Config (AgentState n) Opinion n) {ℓ : Fin n}
    (hℓ_settled : (C ℓ).1.role = .Settled)
    (hℓ_rank0 : (C ℓ).1.rank.val = 0)
    (hℓ_children : (C ℓ).1.children = 0)
    (hℓ_L : (C ℓ).1.leader = .L)
    (hResetZero : ∀ w : Fin n, (C w).1.role = .Resetting → (C w).1.resetcount = 0) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t)) := by
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  obtain ⟨L₁, hNoReset₁⟩ :=
    settled_root_zero_resetting_to_no_reset
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 C hℓ_settled hℓ_rank0 hℓ_children hℓ_L hResetZero
  let C₁ : Config (AgentState n) Opinion n := runPairs P C L₁
  have hNoResetC₁ : ∀ w : Fin n, (C₁ w).1.role ≠ .Resetting := by
    simpa [C₁, P] using hNoReset₁
  obtain ⟨γ₁, t₁, hC₁⟩ :=
    exists_schedule_of_runPairs P C L₁
      (Goal := fun C' => C' = C₁)
      (by rfl)
  obtain ⟨γ₂, t₂, hgoal₂⟩ :=
    ranking_of_no_reset_by_parity
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hEmax hDmax hRmax C₁ hNoResetC₁
  refine ⟨concatScheduler γ₁ t₁ γ₂, t₁ + t₂, ?_⟩
  rw [execution_concat]
  rw [hC₁]
  simpa [P] using hgoal₂

theorem ranking_goal_of_step_ranking_goal
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {C : Config (AgentState n) Opinion n} {u v : Fin n}
    (h :
      ∃ (γ : DetScheduler n) (t : ℕ),
        InSrank
          (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn))
            (C.step (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) u v) γ t) ∧
        ((∀ μ : Fin n,
          (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn))
            (C.step (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) u v) γ t μ).1.rank.val + 1 = ceilHalf n →
          2 ≤ (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn))
            (C.step (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) u v) γ t μ).1.timer) ∨
         IsConsensusConfig
          (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn))
            (C.step (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) u v) γ t))) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t)) := by
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  obtain ⟨γ, t, hgoal⟩ := h
  refine ⟨concatScheduler (fun _ => (u, v)) 1 γ, 1 + t, ?_⟩
  rw [execution_concat]
  simpa [P] using hgoal

set_option maxHeartbeats 128000000 in
theorem ranking_from_all_resetting_zero_with_leader
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (hRmax : n ≤ Rmax)
    (C : Config (AgentState n) Opinion n)
    (hAllReset : ∀ w : Fin n, (C w).1.role = .Resetting)
    (hAllZero : ∀ w : Fin n, (C w).1.resetcount = 0)
    (hHasLeader : ∃ ℓ : Fin n, (C ℓ).1.leader = .L) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t)) := by
  classical
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  suffices go :
      ∀ k (C₀ : Config (AgentState n) Opinion n),
        resetLeaderCount C₀ = k →
        (∀ w : Fin n, (C₀ w).1.role = .Resetting) →
        (∀ w : Fin n, (C₀ w).1.resetcount = 0) →
        (∃ ℓ : Fin n, (C₀ ℓ).1.leader = .L) →
        ∃ (γ : DetScheduler n) (t : ℕ),
          InSrank (execution P C₀ γ t) ∧
          ((∀ μ : Fin n,
            (execution P C₀ γ t μ).1.rank.val + 1 = ceilHalf n →
            2 ≤ (execution P C₀ γ t μ).1.timer) ∨
           IsConsensusConfig (execution P C₀ γ t)) by
    simpa [P] using go (resetLeaderCount C) C rfl hAllReset hAllZero hHasLeader
  intro k
  induction k using Nat.strongRecOn with
  | ind k IH =>
    intro C₀ hk hAllR hAll0 hHasL
    by_cases hUnique : ∃! ℓ : Fin n, (C₀ ℓ).1.leader = .L
    · simpa [P] using
        ranking_from_all_resetting_zero_unique_leader
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hn4 hDmax hRmax C₀ hAllR hAll0 hUnique
    · obtain ⟨ℓ, hℓ_L⟩ := hHasL
      have hOther : ∃ w : Fin n, w ≠ ℓ ∧ (C₀ w).1.leader = .L := by
        by_contra hnone
        push_neg at hnone
        apply hUnique
        refine ⟨ℓ, hℓ_L, ?_⟩
        intro y hyL
        by_contra hy_ne
        exact hnone y hy_ne hyL
      obtain ⟨w, hw_ne_ℓ, hw_L⟩ := hOther
      have hℓw : ℓ ≠ w := hw_ne_ℓ.symm
      by_cases hℓ_high : 1 < (C₀ ℓ).1.delaytimer
      · by_cases hw_high : 1 < (C₀ w).1.delaytimer
        · let C₁ : Config (AgentState n) Opinion n := C₀.step P ℓ w
          have hstep :=
            step_leader_dedup_trace
              (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
              (C := C₀) (ℓ := ℓ) (w := w) hℓw
              (hAllR ℓ) (hAll0 ℓ) (hAllR w) (hAll0 w) hℓ_L hw_L
              hℓ_high hw_high
          have hAllR₁ : ∀ x : Fin n, (C₁ x).1.role = .Resetting := by
            intro x
            by_cases hxℓ : x = ℓ
            · subst x
              exact hstep.1
            · by_cases hxw : x = w
              · subst x
                exact hstep.2.2.2.2.1
              · rw [show C₁ x = C₀ x from hstep.2.2.2.2.2.2.2.2 x hxℓ hxw]
                exact hAllR x
          have hAll0₁ : ∀ x : Fin n, (C₁ x).1.resetcount = 0 := by
            intro x
            by_cases hxℓ : x = ℓ
            · subst x
              exact hstep.2.1
            · by_cases hxw : x = w
              · subst x
                exact hstep.2.2.2.2.2.1
              · rw [show C₁ x = C₀ x from hstep.2.2.2.2.2.2.2.2 x hxℓ hxw]
                exact hAll0 x
          have hHasL₁ : ∃ x : Fin n, (C₁ x).1.leader = .L :=
            ⟨ℓ, hstep.2.2.1⟩
          have hcount_lt : resetLeaderCount C₁ < resetLeaderCount C₀ := by
            simpa [P, C₁] using
              (step_leader_dedup_resetLeaderCount_lt
                (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
                (C := C₀) (ℓ := ℓ) (w := w) hℓw
                (hAllR ℓ) (hAll0 ℓ) (hAllR w) (hAll0 w) hℓ_L hw_L
                hℓ_high hw_high)
          have hgoal₁ :=
            IH (resetLeaderCount C₁) (by omega) C₁ rfl hAllR₁ hAll0₁ hHasL₁
          exact
            ranking_goal_of_step_ranking_goal
              (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
              (C := C₀) (u := ℓ) (v := w)
              (by simpa [P, C₁] using hgoal₁)
        · have hw_low : (C₀ w).1.delaytimer ≤ 1 := by omega
          let C₁ : Config (AgentState n) Opinion n := C₀.step P w ℓ
          have hstep :=
            transitionPEM_dormant_leader_low_dt_L_partner_wakes
              (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
              hn4 (C := C₀) (ℓ := w) (w := ℓ) hw_ne_ℓ
              (hAllR w) (hAll0 w) hw_low hw_L (hAllR ℓ) (hAll0 ℓ) hℓ_L
          have hResetZero₁ :
              ∀ x : Fin n, (C₁ x).1.role = .Resetting → (C₁ x).1.resetcount = 0 := by
            intro x hx_reset
            by_cases hxw : x = w
            · subst x
              rw [hstep.1] at hx_reset
              cases hx_reset
            · by_cases hxℓ : x = ℓ
              · subst x
                rcases hstep.2.2.2.2 with hsettled | hreset
                · rw [hsettled] at hx_reset
                  cases hx_reset
                · exact hreset.2.1
              · have hx_old : C₁ x = C₀ x := by
                  dsimp [C₁, P]
                  simp [Config.step, hw_ne_ℓ, hxw, hxℓ]
                rw [hx_old] at hx_reset ⊢
                exact hAll0 x
          have hgoal₁ :=
            ranking_from_settled_root_zero_resetting
              (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
              hn4 hEmax hDmax hRmax C₁
              (ℓ := w) hstep.1 hstep.2.1 hstep.2.2.1 hstep.2.2.2.1 hResetZero₁
          exact
            ranking_goal_of_step_ranking_goal
              (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
              (C := C₀) (u := w) (v := ℓ)
              (by simpa [P, C₁] using hgoal₁)
      · have hℓ_low : (C₀ ℓ).1.delaytimer ≤ 1 := by omega
        let C₁ : Config (AgentState n) Opinion n := C₀.step P ℓ w
        have hstep :=
          transitionPEM_dormant_leader_low_dt_L_partner_wakes
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            hn4 (C := C₀) (ℓ := ℓ) (w := w) hℓw
            (hAllR ℓ) (hAll0 ℓ) hℓ_low hℓ_L (hAllR w) (hAll0 w) hw_L
        have hResetZero₁ :
            ∀ x : Fin n, (C₁ x).1.role = .Resetting → (C₁ x).1.resetcount = 0 := by
          intro x hx_reset
          by_cases hxℓ : x = ℓ
          · subst x
            rw [hstep.1] at hx_reset
            cases hx_reset
          · by_cases hxw : x = w
            · subst x
              rcases hstep.2.2.2.2 with hsettled | hreset
              · rw [hsettled] at hx_reset
                cases hx_reset
              · exact hreset.2.1
            · have hx_old : C₁ x = C₀ x := by
                dsimp [C₁, P]
                simp [Config.step, hℓw, hxℓ, hxw]
              rw [hx_old] at hx_reset ⊢
              exact hAll0 x
        have hgoal₁ :=
          ranking_from_settled_root_zero_resetting
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            hn4 hEmax hDmax hRmax C₁
            (ℓ := ℓ) hstep.1 hstep.2.1 hstep.2.2.1 hstep.2.2.2.1 hResetZero₁
        exact
          ranking_goal_of_step_ranking_goal
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            (C := C₀) (u := ℓ) (v := w)
            (by simpa [P, C₁] using hgoal₁)

theorem ranking_from_all_resetting_zero
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (hRmax : n ≤ Rmax)
    (C : Config (AgentState n) Opinion n)
    (hAllReset : ∀ w : Fin n, (C w).1.role = .Resetting)
    (hAllZero : ∀ w : Fin n, (C w).1.resetcount = 0) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t)) := by
  by_cases hHasLeader : ∃ ℓ : Fin n, (C ℓ).1.leader = .L
  · exact
      ranking_from_all_resetting_zero_with_leader
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hEmax hDmax hRmax C hAllReset hAllZero hHasLeader
  · exact
      ranking_from_all_resetting_zero_no_leader
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hEmax hDmax hRmax C hAllReset hAllZero
        (by
          intro w hwL
          exact hHasLeader ⟨w, hwL⟩)

theorem ranking_goal_of_runPairs_ranking_goal
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    {C : Config (AgentState n) Opinion n} {L : List (Fin n × Fin n)}
    (h :
      ∃ (γ : DetScheduler n) (t : ℕ),
        InSrank
          (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn))
            (runPairs (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L) γ t) ∧
        ((∀ μ : Fin n,
          (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn))
            (runPairs (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L) γ t μ).1.rank.val + 1 = ceilHalf n →
          2 ≤ (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn))
            (runPairs (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L) γ t μ).1.timer) ∨
         IsConsensusConfig
          (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn))
            (runPairs (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C L) γ t))) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t)) := by
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  obtain ⟨γ₁, t₁, hC₁⟩ :=
    exists_schedule_of_runPairs P C L
      (Goal := fun C' => C' = runPairs P C L)
      rfl
  obtain ⟨γ₂, t₂, hgoal⟩ := h
  refine ⟨concatScheduler γ₁ t₁ γ₂, t₁ + t₂, ?_⟩
  rw [execution_concat]
  rw [hC₁]
  simpa [P] using hgoal

theorem ranking_from_all_resetting_zero_leader_budget
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (hRmax : n ≤ Rmax)
    (C : Config (AgentState n) Opinion n) {ℓ : Fin n}
    (hAllReset : ∀ w : Fin n, (C w).1.role = .Resetting)
    (hℓ_L : (C ℓ).1.leader = .L)
    (hℓ_rc0 : (C ℓ).1.resetcount = 0)
    (hBudget : (positiveRcExcept C ℓ).card < (C ℓ).1.delaytimer) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t)) := by
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have hDmax_gt_one : 1 < Dmax := by omega
  obtain ⟨L₁, hAllReset₁, hAllZero₁, _hℓ_L₁⟩ :=
    drain_positive_except_anchor_to_all_zero
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hDmax_gt_one hDmax C hAllReset hℓ_L hℓ_rc0 hBudget
  let C₁ : Config (AgentState n) Opinion n := runPairs P C L₁
  have hgoal₁ :=
    ranking_from_all_resetting_zero
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hEmax hDmax hRmax C₁
      (by simpa [C₁, P] using hAllReset₁)
      (by simpa [C₁, P] using hAllZero₁)
  exact
    ranking_goal_of_runPairs_ranking_goal
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      (C := C) (L := L₁)
      (by simpa [C₁, P] using hgoal₁)

theorem ranking_from_all_resetting_pos_leader_with_second_pos
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (hRmax : n ≤ Rmax)
    (C : Config (AgentState n) Opinion n) {ℓ v : Fin n}
    (hℓv : ℓ ≠ v)
    (hAllReset : ∀ w : Fin n, (C w).1.role = .Resetting)
    (hℓ_L : (C ℓ).1.leader = .L)
    (hℓ_pos : 0 < (C ℓ).1.resetcount)
    (hv_pos : 0 < (C v).1.resetcount) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t)) := by
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have hDmax_gt_one : 1 < Dmax := by omega
  obtain ⟨L₁, hℓ_role₁, hℓ_rc₁, hℓ_L₁, hℓ_dt₁,
      hv_role₁, _hv_rc₁, _hv_F₁, hothers₁⟩ :=
    drain_pair_rc_L_any_to_LF_zero_with_u_delay
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hDmax_gt_one C hℓv (hAllReset ℓ) (hAllReset v) hℓ_pos hv_pos hℓ_L
  let C₁ : Config (AgentState n) Opinion n := runPairs P C L₁
  have hAllReset₁ : ∀ w : Fin n, (C₁ w).1.role = .Resetting := by
    intro w
    by_cases hwℓ : w = ℓ
    · subst w
      simpa [C₁, P] using hℓ_role₁
    · by_cases hwv : w = v
      · subst w
        simpa [C₁, P] using hv_role₁
      · dsimp [C₁]
        rw [hothers₁ w hwℓ hwv]
        exact hAllReset w
  have hBudget₁ : (positiveRcExcept C₁ ℓ).card < (C₁ ℓ).1.delaytimer := by
    have hdt : (C₁ ℓ).1.delaytimer = Dmax := by
      simpa [C₁, P] using hℓ_dt₁
    rw [hdt]
    exact Nat.lt_of_lt_of_le (positiveRcExcept_card_lt_n (C := C₁) (ℓ := ℓ) hn) hDmax
  have hgoal₁ :=
    ranking_from_all_resetting_zero_leader_budget
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hEmax hDmax hRmax C₁ hAllReset₁
      (by simpa [C₁, P] using hℓ_L₁)
      (by simpa [C₁, P] using hℓ_rc₁)
      hBudget₁
  exact
    ranking_goal_of_runPairs_ranking_goal
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      (C := C) (L := L₁)
      (by simpa [C₁, P] using hgoal₁)

theorem ranking_from_all_resetting_single_pos_leader_high_zero_partner
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (hRmax : n ≤ Rmax)
    (C : Config (AgentState n) Opinion n) {ℓ v : Fin n}
    (hℓv : ℓ ≠ v)
    (hAllReset : ∀ w : Fin n, (C w).1.role = .Resetting)
    (hℓ_L : (C ℓ).1.leader = .L)
    (hℓ_pos : 0 < (C ℓ).1.resetcount)
    (hv_zero : (C v).1.resetcount = 0)
    (hv_dt : 1 < (C v).1.delaytimer)
    (hOnlyPos : ∀ w : Fin n, w ≠ ℓ → (C w).1.resetcount = 0) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t)) := by
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have hDmax_pos : 0 < Dmax := by omega
  obtain ⟨L₁, hℓ_role₁, hℓ_rc₁, hℓ_L₁, hv_role₁, hv_rc₁, _hv_F₁, hothers₁⟩ :=
    drain_L_pos_any_zero_to_zero
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hDmax_pos C hℓv (hAllReset ℓ) (hAllReset v) hℓ_pos hv_zero hℓ_L hv_dt
  let C₁ : Config (AgentState n) Opinion n := runPairs P C L₁
  have hAllReset₁ : ∀ w : Fin n, (C₁ w).1.role = .Resetting := by
    intro w
    by_cases hwℓ : w = ℓ
    · subst w
      simpa [C₁, P] using hℓ_role₁
    · by_cases hwv : w = v
      · subst w
        simpa [C₁, P] using hv_role₁
      · dsimp [C₁]
        rw [hothers₁ w hwℓ hwv]
        exact hAllReset w
  have hAllZero₁ : ∀ w : Fin n, (C₁ w).1.resetcount = 0 := by
    intro w
    by_cases hwℓ : w = ℓ
    · subst w
      simpa [C₁, P] using hℓ_rc₁
    · by_cases hwv : w = v
      · subst w
        simpa [C₁, P] using hv_rc₁
      · dsimp [C₁]
        rw [hothers₁ w hwℓ hwv]
        exact hOnlyPos w hwℓ
  have hgoal₁ :=
    ranking_from_all_resetting_zero
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hEmax hDmax hRmax C₁ hAllReset₁ hAllZero₁
  exact
    ranking_goal_of_runPairs_ranking_goal
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      (C := C) (L := L₁)
      (by simpa [C₁, P] using hgoal₁)

set_option maxHeartbeats 64000000 in
theorem ranking_from_all_resetting_single_pos_leader_low_zero_partner
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (hRmax : n ≤ Rmax)
    (C : Config (AgentState n) Opinion n) {ℓ v : Fin n}
    (hℓv : ℓ ≠ v)
    (hAllReset : ∀ w : Fin n, (C w).1.role = .Resetting)
    (hℓ_L : (C ℓ).1.leader = .L)
    (hℓ_pos : 0 < (C ℓ).1.resetcount)
    (hv_zero : (C v).1.resetcount = 0)
    (hv_low : (C v).1.delaytimer ≤ 1)
    (hOnlyPos : ∀ w : Fin n, w ≠ ℓ → (C w).1.resetcount = 0) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t)) := by
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have hDmax_pos : 0 < Dmax := by omega
  by_cases hgt : 1 < (C ℓ).1.resetcount
  · have hstep :=
      step_L_pos_any_zero_gt_one
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        C hℓv (hAllReset ℓ) (hAllReset v) hgt hv_zero hℓ_L
    let C₁ : Config (AgentState n) Opinion n := C.step P ℓ v
    have hAllReset₁ : ∀ w : Fin n, (C₁ w).1.role = .Resetting := by
      intro w
      by_cases hwℓ : w = ℓ
      · subst w
        simpa [C₁, P] using hstep.1
      · by_cases hwv : w = v
        · subst w
          simpa [C₁, P] using hstep.2.1
        · dsimp [C₁]
          simp [Config.step, P, hℓv, hwℓ, hwv]
          exact hAllReset w
    have hℓ_pos₁ : 0 < (C₁ ℓ).1.resetcount := by
      have hrc : (C₁ ℓ).1.resetcount = (C ℓ).1.resetcount - 1 := by
        simpa [C₁, P] using hstep.2.2.1
      rw [hrc]
      omega
    have hv_pos₁ : 0 < (C₁ v).1.resetcount := by
      have hrc : (C₁ v).1.resetcount = (C ℓ).1.resetcount - 1 := by
        simpa [C₁, P] using hstep.2.2.2.1
      rw [hrc]
      omega
    have hgoal₁ :=
      ranking_from_all_resetting_pos_leader_with_second_pos
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hEmax hDmax hRmax C₁ hℓv hAllReset₁
        (by simpa [C₁, P] using hstep.2.2.2.2.1)
        hℓ_pos₁ hv_pos₁
    exact
      ranking_goal_of_step_ranking_goal
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        (C := C) (u := ℓ) (v := v)
        (by simpa [C₁, P] using hgoal₁)
  · have hℓ_one : (C ℓ).1.resetcount = 1 := by omega
    cases hv_leader : (C v).1.leader with
    | L =>
        have hstep :=
          step_L_pos_one_L_zero_low
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            hDmax_pos C hℓv (hAllReset ℓ) (hAllReset v) hℓ_one hv_zero
            hℓ_L hv_leader hv_low
        let C₁ : Config (AgentState n) Opinion n := C.step P ℓ v
        have hResetZero₁ :
            ∀ w : Fin n, (C₁ w).1.role = .Resetting → (C₁ w).1.resetcount = 0 := by
          intro w hw_reset
          by_cases hwℓ : w = ℓ
          · subst w
            simpa [C₁, P] using hstep.2.1
          · by_cases hwv : w = v
            · subst w
              have hv_settled : (C₁ v).1.role = .Settled := by
                simpa [C₁, P] using hstep.2.2.2.2.1
              rw [hv_settled] at hw_reset
              cases hw_reset
            · have hw_old : C₁ w = C w := by
                dsimp [C₁, P]
                simp [Config.step, hℓv, hwℓ, hwv]
              rw [hw_old] at hw_reset ⊢
              exact hOnlyPos w hwℓ
        have hgoal₁ :=
          ranking_from_settled_root_zero_resetting
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            hn4 hEmax hDmax hRmax C₁ (ℓ := v)
            (by simpa [C₁, P] using hstep.2.2.2.2.1)
            (by simpa [C₁, P] using hstep.2.2.2.2.2.1)
            (by simpa [C₁, P] using hstep.2.2.2.2.2.2.1)
            (by simpa [C₁, P] using hstep.2.2.2.2.2.2.2)
            hResetZero₁
        exact
          ranking_goal_of_step_ranking_goal
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            (C := C) (u := ℓ) (v := v)
            (by simpa [C₁, P] using hgoal₁)
    | F =>
        have hstep₁ :=
          step_L_pos_one_F_zero_low
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            hDmax_pos C hℓv (hAllReset ℓ) (hAllReset v) hℓ_one hv_zero
            hℓ_L hv_leader hv_low
        let C₁ : Config (AgentState n) Opinion n := C.step P ℓ v
        have hstep₂ :=
          transitionPEM_dormant_leader_with_unsettled_follower_wakes
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            (C := C₁) (ℓ := ℓ) (w := v) hℓv
            (by simpa [C₁, P] using hstep₁.1)
            (by simpa [C₁, P] using hstep₁.2.1)
            (by simpa [C₁, P] using hstep₁.2.2.1)
            (by simpa [C₁, P] using hstep₁.2.2.2.2.1)
            (by simpa [C₁, P] using hstep₁.2.2.2.2.2)
        let C₂ : Config (AgentState n) Opinion n := C₁.step P ℓ v
        have hResetZero₂ :
            ∀ w : Fin n, (C₂ w).1.role = .Resetting → (C₂ w).1.resetcount = 0 := by
          intro w hw_reset
          by_cases hwℓ : w = ℓ
          · subst w
            have hsettled : (C₂ ℓ).1.role = .Settled := by
              simpa [C₂, P] using hstep₂.1
            rw [hsettled] at hw_reset
            cases hw_reset
          · by_cases hwv : w = v
            · subst w
              have hun : (C₂ v).1.role = .Unsettled := by
                simpa [C₂, P] using hstep₂.2.2.2.2.1
              rw [hun] at hw_reset
              cases hw_reset
            · have hw_old₂ : C₂ w = C₁ w := by
                dsimp [C₂, P]
                simp [Config.step, hℓv, hwℓ, hwv]
              have hw_old₁ : C₁ w = C w := by
                dsimp [C₁, P]
                simp [Config.step, hℓv, hwℓ, hwv]
              rw [hw_old₂, hw_old₁] at hw_reset ⊢
              exact hOnlyPos w hwℓ
        have hgoal₂ :=
          ranking_from_settled_root_zero_resetting
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            hn4 hEmax hDmax hRmax C₂ (ℓ := ℓ)
            (by simpa [C₂, P] using hstep₂.1)
            (by
              have hrank : (C₂ ℓ).1.rank = ⟨0, hn⟩ := by
                simpa [C₂, P] using hstep₂.2.1
              rw [hrank])
            (by simpa [C₂, P] using hstep₂.2.2.1)
            (by simpa [C₂, P] using hstep₂.2.2.2.1)
            hResetZero₂
        have hgoal₁ :=
          ranking_goal_of_step_ranking_goal
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            (C := C₁) (u := ℓ) (v := v)
            (by simpa [C₂, P] using hgoal₂)
        exact
          ranking_goal_of_step_ranking_goal
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            (C := C) (u := ℓ) (v := v)
            (by simpa [C₁, P] using hgoal₁)

theorem ranking_from_all_resetting_single_pos_leader
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (hRmax : n ≤ Rmax)
    (C : Config (AgentState n) Opinion n) {ℓ v : Fin n}
    (hℓv : ℓ ≠ v)
    (hAllReset : ∀ w : Fin n, (C w).1.role = .Resetting)
    (hℓ_L : (C ℓ).1.leader = .L)
    (hℓ_pos : 0 < (C ℓ).1.resetcount)
    (hOnlyPos : ∀ w : Fin n, w ≠ ℓ → (C w).1.resetcount = 0) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t)) := by
  have hv_zero : (C v).1.resetcount = 0 := hOnlyPos v hℓv.symm
  by_cases hv_high : 1 < (C v).1.delaytimer
  · exact
      ranking_from_all_resetting_single_pos_leader_high_zero_partner
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hEmax hDmax hRmax C hℓv hAllReset hℓ_L hℓ_pos
        hv_zero hv_high hOnlyPos
  · have hv_low : (C v).1.delaytimer ≤ 1 := by omega
    exact
      ranking_from_all_resetting_single_pos_leader_low_zero_partner
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hEmax hDmax hRmax C hℓv hAllReset hℓ_L hℓ_pos
        hv_zero hv_low hOnlyPos

theorem ranking_from_all_resetting_with_positive_leader
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (hRmax : n ≤ Rmax)
    (C : Config (AgentState n) Opinion n) {ℓ : Fin n}
    (hAllReset : ∀ w : Fin n, (C w).1.role = .Resetting)
    (hℓ_L : (C ℓ).1.leader = .L)
    (hℓ_pos : 0 < (C ℓ).1.resetcount) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t)) := by
  classical
  by_cases hSecond : ∃ v : Fin n, v ≠ ℓ ∧ 0 < (C v).1.resetcount
  · obtain ⟨v, hv_ne, hv_pos⟩ := hSecond
    exact
      ranking_from_all_resetting_pos_leader_with_second_pos
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hEmax hDmax hRmax C hv_ne.symm hAllReset hℓ_L hℓ_pos hv_pos
  · push_neg at hSecond
    have hOnlyPos : ∀ w : Fin n, w ≠ ℓ → (C w).1.resetcount = 0 := by
      intro w hw
      have hle : (C w).1.resetcount ≤ 0 := hSecond w hw
      omega
    have hcard : 1 < Fintype.card (Fin n) := by
      rw [Fintype.card_fin]
      omega
    obtain ⟨v, hv_ne⟩ := Fintype.exists_ne_of_one_lt_card hcard ℓ
    exact
      ranking_from_all_resetting_single_pos_leader
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hEmax hDmax hRmax C hv_ne.symm hAllReset hℓ_L hℓ_pos hOnlyPos

theorem ranking_from_all_resetting_single_pos_follower
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (hRmax : n ≤ Rmax)
    (C : Config (AgentState n) Opinion n) {u v : Fin n}
    (huv : u ≠ v)
    (hAllReset : ∀ w : Fin n, (C w).1.role = .Resetting)
    (hAllF : ∀ w : Fin n, (C w).1.leader = .F)
    (hu_pos : 0 < (C u).1.resetcount)
    (hOnlyPos : ∀ w : Fin n, w ≠ u → (C w).1.resetcount = 0) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t)) := by
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have hDmax_pos : 0 < Dmax := by omega
  have hv_zero : (C v).1.resetcount = 0 := hOnlyPos v huv.symm
  by_cases hv_high : 1 < (C v).1.delaytimer
  · obtain ⟨L₁, hu_role₁, hu_rc₁, hu_F₁, hv_role₁, hv_rc₁, hv_F₁, hothers₁⟩ :=
      drain_F_pos_F_zero_to_zero_FF
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hDmax_pos C huv (hAllReset u) (hAllReset v) hu_pos hv_zero
        (hAllF u) (hAllF v) hv_high
    let C₁ : Config (AgentState n) Opinion n := runPairs P C L₁
    have hClean₁ : FollowerDormantOrNonResetting C₁ := by
      intro w
      by_cases hwu : w = u
      · subst w
        exact Or.inl ⟨by simpa [C₁, P] using hu_role₁,
          by simpa [C₁, P] using hu_rc₁,
          by simpa [C₁, P] using hu_F₁⟩
      · by_cases hwv : w = v
        · subst w
          exact Or.inl ⟨by simpa [C₁, P] using hv_role₁,
            by simpa [C₁, P] using hv_rc₁,
            by simpa [C₁, P] using hv_F₁⟩
        · dsimp [C₁]
          rw [hothers₁ w hwu hwv]
          exact Or.inl ⟨hAllReset w, hOnlyPos w hwu, hAllF w⟩
    have hgoal₁ :=
      follower_dormant_or_nonresetting_to_ranking_goal_by_parity
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hEmax hDmax hRmax C₁ hClean₁
    exact
      ranking_goal_of_runPairs_ranking_goal
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        (C := C) (L := L₁)
        (by simpa [C₁, P] using hgoal₁)
  · have hv_low : (C v).1.delaytimer ≤ 1 := by omega
    by_cases hu_gt : 1 < (C u).1.resetcount
    · have hstep :=
        step_F_pos_F_zero_gt_one
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          C huv (hAllReset u) (hAllReset v) hu_gt hv_zero (hAllF u) (hAllF v)
      let C₁ : Config (AgentState n) Opinion n := C.step P u v
      have hu_role₁ : (C₁ u).1.role = .Resetting := by
        simpa [C₁, P] using hstep.1
      have hv_role₁ : (C₁ v).1.role = .Resetting := by
        simpa [C₁, P] using hstep.2.1
      have hu_rc₁ : (C₁ u).1.resetcount = (C u).1.resetcount - 1 := by
        simpa [C₁, P] using hstep.2.2.1
      have hv_rc₁ : (C₁ v).1.resetcount = (C u).1.resetcount - 1 := by
        simpa [C₁, P] using hstep.2.2.2.1
      have hu_F₁ : (C₁ u).1.leader = .F := by
        simpa [C₁, P] using hstep.2.2.2.2.1
      have hv_F₁ : (C₁ v).1.leader = .F := by
        simpa [C₁, P] using hstep.2.2.2.2.2
      have hothers_step : ∀ w : Fin n, w ≠ u → w ≠ v → C₁ w = C w := by
        intro w hwu hwv
        simp [C₁, Config.step, P, huv, hwu, hwv]
      have hu_pos₁ : 0 < (C₁ u).1.resetcount := by
        rw [hu_rc₁]
        omega
      have hv_pos₁ : 0 < (C₁ v).1.resetcount := by
        rw [hv_rc₁]
        omega
      obtain ⟨Ltail, hu_role_t, hu_rc_t, hu_F_t, hv_role_t, hv_rc_t, hv_F_t, hothers_t⟩ :=
        drain_pair_rc_FF
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hDmax_pos C₁ huv hu_role₁ hv_role₁ hu_pos₁ hv_pos₁ hu_F₁ hv_F₁
      let C₂ : Config (AgentState n) Opinion n := runPairs P C₁ Ltail
      have hClean₂ : FollowerDormantOrNonResetting C₂ := by
        intro w
        by_cases hwu : w = u
        · subst w
          exact Or.inl ⟨by simpa [C₂, P] using hu_role_t,
            by simpa [C₂, P] using hu_rc_t,
            by simpa [C₂, P] using hu_F_t⟩
        · by_cases hwv : w = v
          · subst w
            exact Or.inl ⟨by simpa [C₂, P] using hv_role_t,
              by simpa [C₂, P] using hv_rc_t,
              by simpa [C₂, P] using hv_F_t⟩
          · dsimp [C₂]
            rw [hothers_t w hwu hwv, hothers_step w hwu hwv]
            exact Or.inl ⟨hAllReset w, hOnlyPos w hwu, hAllF w⟩
      have hgoal₂ :=
        follower_dormant_or_nonresetting_to_ranking_goal_by_parity
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hn4 hEmax hDmax hRmax C₂ hClean₂
      have hgoal₁ :=
        ranking_goal_of_runPairs_ranking_goal
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          (C := C₁) (L := Ltail)
          (by simpa [C₂, P] using hgoal₂)
      exact
        ranking_goal_of_step_ranking_goal
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          (C := C) (u := u) (v := v)
          (by simpa [C₁, P] using hgoal₁)
    · have hu_one : (C u).1.resetcount = 1 := by omega
      have hstep :=
        step_F_pos_one_F_zero_low
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hDmax_pos C huv (hAllReset u) (hAllReset v) hu_one hv_zero
          (hAllF u) (hAllF v) hv_low
      let C₁ : Config (AgentState n) Opinion n := C.step P u v
      have hClean₁ : FollowerDormantOrNonResetting C₁ := by
        intro w
        by_cases hwu : w = u
        · subst w
          exact Or.inl ⟨by simpa [C₁, P] using hstep.1,
            by simpa [C₁, P] using hstep.2.1,
            by simpa [C₁, P] using hstep.2.2.1⟩
        · by_cases hwv : w = v
          · subst w
            exact Or.inr (by
              intro hv_reset
              have hv_un : (C₁ v).1.role = .Unsettled := by
                simpa [C₁, P] using hstep.2.2.2.2.1
              rw [hv_un] at hv_reset
              cases hv_reset)
          · dsimp [C₁]
            simp [Config.step, P, huv, hwu, hwv]
            exact Or.inl ⟨hAllReset w, hOnlyPos w hwu, hAllF w⟩
      have hgoal₁ :=
        follower_dormant_or_nonresetting_to_ranking_goal_by_parity
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hn4 hEmax hDmax hRmax C₁ hClean₁
      exact
        ranking_goal_of_step_ranking_goal
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          (C := C) (u := u) (v := v)
          (by simpa [C₁, P] using hgoal₁)

set_option maxHeartbeats 32000000 in
theorem ranking_from_all_resetting_no_leader
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (hRmax : n ≤ Rmax)
    (C : Config (AgentState n) Opinion n)
    (hAllReset : ∀ w : Fin n, (C w).1.role = .Resetting)
    (hNoLeader : ∀ w : Fin n, (C w).1.leader ≠ .L) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t)) := by
  classical
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have hDmax_pos : 0 < Dmax := by omega
  suffices go :
      ∀ k (C₀ : Config (AgentState n) Opinion n),
        (positiveRcAgents C₀).card = k →
        (∀ w : Fin n, (C₀ w).1.role = .Resetting) →
        (∀ w : Fin n, (C₀ w).1.leader = .F) →
        ∃ (γ : DetScheduler n) (t : ℕ),
          InSrank (execution P C₀ γ t) ∧
          ((∀ μ : Fin n,
            (execution P C₀ γ t μ).1.rank.val + 1 = ceilHalf n →
            2 ≤ (execution P C₀ γ t μ).1.timer) ∨
           IsConsensusConfig (execution P C₀ γ t)) by
    have hAllF : ∀ w : Fin n, (C w).1.leader = .F := by
      intro w
      cases hleader : (C w).1.leader with
      | L => exact False.elim ((hNoLeader w) hleader)
      | F => rfl
    simpa [P] using go (positiveRcAgents C).card C rfl hAllReset hAllF
  intro k
  induction k using Nat.strongRecOn with
  | ind k IH =>
      intro C₀ hcard hAllReset₀ hAllF₀
      by_cases hcard0 : k = 0
      · have hAllZero₀ : ∀ w : Fin n, (C₀ w).1.resetcount = 0 := by
          apply positiveRcAgents_eq_zero_iff.mp
          rw [hcard, hcard0]
        exact
          ranking_from_all_resetting_zero
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            hn4 hEmax hDmax hRmax C₀ hAllReset₀ hAllZero₀
      · have hcard_pos : 0 < (positiveRcAgents C₀).card := by
          rw [hcard]
          omega
        obtain ⟨u, hu_pos⟩ :=
          positiveRcAgents_exists_of_card_pos (C := C₀) hcard_pos
        by_cases hSecond : ∃ v : Fin n, v ≠ u ∧ 0 < (C₀ v).1.resetcount
        · obtain ⟨v, hv_ne, hv_pos⟩ := hSecond
          have huv : u ≠ v := hv_ne.symm
          obtain ⟨L₁, hu_role₁, hu_rc₁, hu_F₁, hv_role₁, hv_rc₁, hv_F₁, hothers₁⟩ :=
            drain_pair_rc_FF
              (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
              hDmax_pos C₀ huv (hAllReset₀ u) (hAllReset₀ v)
              hu_pos hv_pos (hAllF₀ u) (hAllF₀ v)
          let C₁ : Config (AgentState n) Opinion n := runPairs P C₀ L₁
          have hAllReset₁ : ∀ w : Fin n, (C₁ w).1.role = .Resetting := by
            intro w
            by_cases hwu : w = u
            · subst w
              exact hu_role₁
            · by_cases hwv : w = v
              · subst w
                exact hv_role₁
              · dsimp [C₁]
                rw [hothers₁ w hwu hwv]
                exact hAllReset₀ w
          have hAllF₁ : ∀ w : Fin n, (C₁ w).1.leader = .F := by
            intro w
            by_cases hwu : w = u
            · subst w
              exact hu_F₁
            · by_cases hwv : w = v
              · subst w
                exact hv_F₁
              · dsimp [C₁]
                rw [hothers₁ w hwu hwv]
                exact hAllF₀ w
          have hsub : positiveRcAgents C₁ ⊆ (positiveRcAgents C₀).erase u := by
            intro w hw_mem
            rw [positiveRcAgents, Finset.mem_filter] at hw_mem
            have hw_pos : 0 < (C₁ w).1.resetcount := hw_mem.2
            rw [Finset.mem_erase]
            refine ⟨?_, ?_⟩
            · intro hwu
              subst w
              rw [hu_rc₁] at hw_pos
              omega
            · rw [positiveRcAgents, Finset.mem_filter]
              by_cases hwv : w = v
              · subst w
                rw [hv_rc₁] at hw_pos
                omega
              · have hwu : w ≠ u := by
                  intro hwu
                  subst w
                  rw [hu_rc₁] at hw_pos
                  omega
                have hw_old : C₁ w = C₀ w := hothers₁ w hwu hwv
                have hw_old_pos : 0 < (C₀ w).1.resetcount := by
                  rwa [hw_old] at hw_pos
                exact ⟨Finset.mem_univ w, hw_old_pos⟩
          have hu_mem_old : u ∈ positiveRcAgents C₀ := by
            rw [positiveRcAgents, Finset.mem_filter]
            exact ⟨Finset.mem_univ u, hu_pos⟩
          have hcard₁_lt : (positiveRcAgents C₁).card < k := by
            have hle := Finset.card_le_card hsub
            have herase :
                ((positiveRcAgents C₀).erase u).card =
                  (positiveRcAgents C₀).card - 1 :=
              Finset.card_erase_of_mem hu_mem_old
            rw [herase, hcard] at hle
            omega
          have hgoal₁ :=
            IH (positiveRcAgents C₁).card hcard₁_lt C₁ rfl hAllReset₁ hAllF₁
          exact
            ranking_goal_of_runPairs_ranking_goal
              (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
              (C := C₀) (L := L₁)
              (by simpa [C₁, P] using hgoal₁)
        · push_neg at hSecond
          have hOnlyPos : ∀ w : Fin n, w ≠ u → (C₀ w).1.resetcount = 0 := by
            intro w hw
            have hle : (C₀ w).1.resetcount ≤ 0 := hSecond w hw
            omega
          have hcard_fin : 1 < Fintype.card (Fin n) := by
            rw [Fintype.card_fin]
            omega
          obtain ⟨v, hv_ne_u⟩ := Fintype.exists_ne_of_one_lt_card hcard_fin u
          exact
            ranking_from_all_resetting_single_pos_follower
              (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
              hn4 hEmax hDmax hRmax C₀ hv_ne_u.symm hAllReset₀ hAllF₀
              hu_pos hOnlyPos

set_option maxHeartbeats 64000000 in
theorem ranking_from_all_resetting_zero_leader_unit_followers
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (hRmax : n ≤ Rmax)
    (C : Config (AgentState n) Opinion n) {ℓ : Fin n}
    (hAllReset : ∀ w : Fin n, (C w).1.role = .Resetting)
    (hℓ_L : (C ℓ).1.leader = .L)
    (hℓ_rc0 : (C ℓ).1.resetcount = 0)
    (hPosUnitF :
      ∀ w : Fin n, w ≠ ℓ → 0 < (C w).1.resetcount →
        (C w).1.leader = .F ∧ (C w).1.resetcount = 1) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t)) := by
  classical
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have hDmax_pos : 0 < Dmax := by omega
  have hDmax_gt_one : 1 < Dmax := by omega
  suffices go :
      ∀ k (C₀ : Config (AgentState n) Opinion n),
        (positiveRcExcept C₀ ℓ).card = k →
        (∀ w : Fin n, (C₀ w).1.role = .Resetting) →
        (C₀ ℓ).1.leader = .L →
        (C₀ ℓ).1.resetcount = 0 →
        (∀ w : Fin n, w ≠ ℓ → 0 < (C₀ w).1.resetcount →
          (C₀ w).1.leader = .F ∧ (C₀ w).1.resetcount = 1) →
        ∃ (γ : DetScheduler n) (t : ℕ),
          InSrank (execution P C₀ γ t) ∧
          ((∀ μ : Fin n,
            (execution P C₀ γ t μ).1.rank.val + 1 = ceilHalf n →
            2 ≤ (execution P C₀ γ t μ).1.timer) ∨
           IsConsensusConfig (execution P C₀ γ t)) by
    simpa [P] using
      go (positiveRcExcept C ℓ).card C rfl hAllReset hℓ_L hℓ_rc0 hPosUnitF
  intro k
  induction k using Nat.strongRecOn with
  | ind k IH =>
      intro C₀ hcard hAllReset₀ hℓ_L₀ hℓ_rc0₀ hPosUnitF₀
      by_cases hcard0 : k = 0
      · have hAllZero₀ : ∀ w : Fin n, (C₀ w).1.resetcount = 0 := by
          intro w
          by_cases hwℓ : w = ℓ
          · subst w
            exact hℓ_rc0₀
          · exact (positiveRcExcept_eq_zero_iff.mp (by rw [hcard, hcard0])) w hwℓ
        exact
          ranking_from_all_resetting_zero
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            hn4 hEmax hDmax hRmax C₀ hAllReset₀ hAllZero₀
      · by_cases hBudget : (positiveRcExcept C₀ ℓ).card < (C₀ ℓ).1.delaytimer
        · exact
            ranking_from_all_resetting_zero_leader_budget
              (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
              hn4 hEmax hDmax hRmax C₀ hAllReset₀ hℓ_L₀ hℓ_rc0₀ hBudget
        · have hcard_pos : 0 < (positiveRcExcept C₀ ℓ).card := by
            rw [hcard]
            omega
          obtain ⟨v, hv_ne_ℓ, hv_pos⟩ :=
            positiveRcExcept_exists_of_card_pos (C := C₀) (ℓ := ℓ) hcard_pos
          have hℓv : ℓ ≠ v := hv_ne_ℓ.symm
          have hv_fields := hPosUnitF₀ v hv_ne_ℓ hv_pos
          have hv_F : (C₀ v).1.leader = .F := hv_fields.1
          have hv_one : (C₀ v).1.resetcount = 1 := hv_fields.2
          by_cases hℓ_low : (C₀ ℓ).1.delaytimer ≤ 1
          · let C₁ : Config (AgentState n) Opinion n := C₀.step P ℓ v
            have hstep₁ :=
              step_L_zero_F_pos_one_low
                (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
                hDmax_pos C₀ hℓv (hAllReset₀ ℓ) (hAllReset₀ v)
                hℓ_rc0₀ hv_one hℓ_L₀ hv_F hℓ_low
            by_cases hMore : ∃ p : Fin n, p ≠ ℓ ∧ 0 < (C₁ p).1.resetcount
            · obtain ⟨p, hp_ne_ℓ, hp_pos₁⟩ := hMore
              have hp_ne_v : p ≠ v := by
                intro hpv
                subst p
                have hv_rc₁ : (C₁ v).1.resetcount = 0 := by
                  simpa [C₁, P] using hstep₁.2.2.2.2.2.1
                rw [hv_rc₁] at hp_pos₁
                omega
              have hp_old : C₁ p = C₀ p := by
                dsimp [C₁, P]
                simp [Config.step, hℓv, hp_ne_ℓ, hp_ne_v]
              have hp_pos₀ : 0 < (C₀ p).1.resetcount := by
                rwa [hp_old] at hp_pos₁
              have hp_fields := hPosUnitF₀ p hp_ne_ℓ hp_pos₀
              let C₂ : Config (AgentState n) Opinion n := C₁.step P p ℓ
              have hpℓ : p ≠ ℓ := hp_ne_ℓ
              have hstep₂ :=
                step_F_pos_one_settled_L
                  (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
                  hDmax_gt_one C₁ hpℓ
                  (by rw [hp_old]; exact hAllReset₀ p)
                  (by simpa [C₁, P] using hstep₁.1)
                  (by rw [hp_old]; exact hp_fields.2)
                  (by rw [hp_old]; exact hp_fields.1)
                  (by simpa [C₁, P] using hstep₁.2.2.2.1)
              have hAllReset₂ : ∀ w : Fin n, (C₂ w).1.role = .Resetting := by
                intro w
                by_cases hwp : w = p
                · subst w
                  simpa [C₂, P] using hstep₂.1
                · by_cases hwℓ : w = ℓ
                  · subst w
                    simpa [C₂, P] using hstep₂.2.2.2.1
                  · have hw_step₂ : C₂ w = C₁ w := by
                      dsimp [C₂, P]
                      simp [Config.step, hpℓ, hwp, hwℓ]
                    rw [hw_step₂]
                    by_cases hwv : w = v
                    · subst w
                      simpa [C₁, P] using hstep₁.2.2.2.2.1
                    · have hw_step₁ : C₁ w = C₀ w := by
                        dsimp [C₁, P]
                        simp [Config.step, hℓv, hwℓ, hwv]
                      rw [hw_step₁]
                      exact hAllReset₀ w
              have hℓ_L₂ : (C₂ ℓ).1.leader = .L := by
                simpa [C₂, P] using hstep₂.2.2.2.2.2.1
              have hℓ_rc₂ : (C₂ ℓ).1.resetcount = 0 := by
                simpa [C₂, P] using hstep₂.2.2.2.2.1
              have hℓ_dt₂ : (C₂ ℓ).1.delaytimer = Dmax - 1 := by
                simpa [C₂, P] using hstep₂.2.2.2.2.2.2
              have hBudget₂ : (positiveRcExcept C₂ ℓ).card < (C₂ ℓ).1.delaytimer := by
                have hsub : positiveRcExcept C₂ ℓ ⊆ (Finset.univ.erase ℓ).erase p := by
                  intro x hx
                  rw [positiveRcExcept, Finset.mem_filter] at hx
                  rw [Finset.mem_erase]
                  refine ⟨?_, ?_⟩
                  · intro hxp
                    subst x
                    have hp_rc₂ : (C₂ p).1.resetcount = 0 := by
                      simpa [C₂, P] using hstep₂.2.1
                    rw [hp_rc₂] at hx
                    omega
                  · rw [Finset.mem_erase]
                    exact ⟨hx.2.1, Finset.mem_univ x⟩
                have hle := Finset.card_le_card hsub
                have hp_mem : p ∈ Finset.univ.erase ℓ := by
                  rw [Finset.mem_erase]
                  exact ⟨hp_ne_ℓ, Finset.mem_univ p⟩
                have hcard_erase :
                    ((Finset.univ.erase ℓ).erase p).card = n - 2 := by
                  rw [Finset.card_erase_of_mem hp_mem]
                  rw [Finset.card_erase_of_mem (Finset.mem_univ ℓ)]
                  simpa using (Nat.sub_sub n 1 1)
                rw [hcard_erase] at hle
                rw [hℓ_dt₂]
                omega
              have hgoal₂ :=
                ranking_from_all_resetting_zero_leader_budget
                  (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
                  hn4 hEmax hDmax hRmax C₂ hAllReset₂ hℓ_L₂ hℓ_rc₂ hBudget₂
              have hgoal₁ :=
                ranking_goal_of_step_ranking_goal
                  (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
                  (C := C₁) (u := p) (v := ℓ)
                  (by simpa [C₂, P] using hgoal₂)
              exact
                ranking_goal_of_step_ranking_goal
                  (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
                  (C := C₀) (u := ℓ) (v := v)
                  (by simpa [C₁, P] using hgoal₁)
            · push_neg at hMore
              have hResetZero₁ :
                  ∀ w : Fin n, (C₁ w).1.role = .Resetting → (C₁ w).1.resetcount = 0 := by
                intro w hw_reset
                by_cases hwℓ : w = ℓ
                · subst w
                  have hsettled : (C₁ ℓ).1.role = .Settled := by
                    simpa [C₁, P] using hstep₁.1
                  rw [hsettled] at hw_reset
                  cases hw_reset
                · have hzero := hMore w hwℓ
                  omega
              have hgoal₁ :=
                ranking_from_settled_root_zero_resetting
                  (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
                  hn4 hEmax hDmax hRmax C₁
                  (ℓ := ℓ)
                  (by simpa [C₁, P] using hstep₁.1)
                  (by simpa [C₁, P] using hstep₁.2.1)
                  (by simpa [C₁, P] using hstep₁.2.2.1)
                  (by simpa [C₁, P] using hstep₁.2.2.2.1)
                  hResetZero₁
              exact
                ranking_goal_of_step_ranking_goal
                  (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
                  (C := C₀) (u := ℓ) (v := v)
                  (by simpa [C₁, P] using hgoal₁)
          · have hℓ_high : 1 < (C₀ ℓ).1.delaytimer := by omega
            have hstep₁ :=
              step_L_zero_F_pos
                (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
                hDmax_pos C₀ hℓv (hAllReset₀ ℓ) (hAllReset₀ v)
                hℓ_rc0₀ hv_pos hℓ_L₀ hv_F hℓ_high
            let C₁ : Config (AgentState n) Opinion n := C₀.step P ℓ v
            have hAllReset₁ : ∀ w : Fin n, (C₁ w).1.role = .Resetting := by
              intro w
              by_cases hwℓ : w = ℓ
              · subst w
                simpa [C₁, P] using hstep₁.1
              · by_cases hwv : w = v
                · subst w
                  simpa [C₁, P] using hstep₁.2.1
                · dsimp [C₁, P]
                  simp [Config.step, hℓv, hwℓ, hwv]
                  exact hAllReset₀ w
            have hℓ_L₁ : (C₁ ℓ).1.leader = .L := by
              simpa [C₁, P] using hstep₁.2.2.2.2.1
            have hℓ_rc₁ : (C₁ ℓ).1.resetcount = 0 := by
              have hrc : (C₁ ℓ).1.resetcount = (C₀ v).1.resetcount - 1 := by
                simpa [C₁, P] using hstep₁.2.2.1
              rw [hrc, hv_one]
            have hPosUnitF₁ :
                ∀ w : Fin n, w ≠ ℓ → 0 < (C₁ w).1.resetcount →
                  (C₁ w).1.leader = .F ∧ (C₁ w).1.resetcount = 1 := by
              intro w hw_ne hw_pos
              by_cases hwv : w = v
              · subst w
                have hv_rc₁ : (C₁ v).1.resetcount = 0 := by
                  have hrc : (C₁ v).1.resetcount = (C₀ v).1.resetcount - 1 := by
                    simpa [C₁, P] using hstep₁.2.2.2.1
                  rw [hrc, hv_one]
                rw [hv_rc₁] at hw_pos
                omega
              · have hw_old : C₁ w = C₀ w := by
                  dsimp [C₁, P]
                  simp [Config.step, hℓv, hw_ne, hwv]
                have hw_pos_old : 0 < (C₀ w).1.resetcount := by
                  rwa [hw_old] at hw_pos
                have hw_fields := hPosUnitF₀ w hw_ne hw_pos_old
                rw [hw_old]
                exact hw_fields
            have hsub : positiveRcExcept C₁ ℓ ⊆ (positiveRcExcept C₀ ℓ).erase v := by
              intro w hw_mem
              rw [positiveRcExcept, Finset.mem_filter] at hw_mem
              rw [Finset.mem_erase]
              refine ⟨?_, ?_⟩
              · intro hwv
                subst w
                have hv_rc₁ : (C₁ v).1.resetcount = 0 := by
                  have hrc : (C₁ v).1.resetcount = (C₀ v).1.resetcount - 1 := by
                    simpa [C₁, P] using hstep₁.2.2.2.1
                  rw [hrc, hv_one]
                rw [hv_rc₁] at hw_mem
                omega
              · rw [positiveRcExcept, Finset.mem_filter]
                by_cases hwv : w = v
                · subst w
                  have hv_rc₁ : (C₁ v).1.resetcount = 0 := by
                    have hrc : (C₁ v).1.resetcount = (C₀ v).1.resetcount - 1 := by
                      simpa [C₁, P] using hstep₁.2.2.2.1
                    rw [hrc, hv_one]
                  rw [hv_rc₁] at hw_mem
                  omega
                · have hw_old : C₁ w = C₀ w := by
                    dsimp [C₁, P]
                    simp [Config.step, hℓv, hw_mem.2.1, hwv]
                  have hw_pos_old : 0 < (C₀ w).1.resetcount := by
                    have hpos := hw_mem.2.2
                    rwa [hw_old] at hpos
                  exact ⟨Finset.mem_univ w, hw_mem.2.1, hw_pos_old⟩
            have hv_mem_old : v ∈ positiveRcExcept C₀ ℓ := by
              rw [positiveRcExcept, Finset.mem_filter]
              exact ⟨Finset.mem_univ v, hv_ne_ℓ, hv_pos⟩
            have hcard₁_lt : (positiveRcExcept C₁ ℓ).card < k := by
              have hle := Finset.card_le_card hsub
              have herase :
                  ((positiveRcExcept C₀ ℓ).erase v).card =
                    (positiveRcExcept C₀ ℓ).card - 1 :=
                Finset.card_erase_of_mem hv_mem_old
              rw [herase, hcard] at hle
              omega
            have hgoal₁ :=
              IH (positiveRcExcept C₁ ℓ).card hcard₁_lt C₁ rfl
                hAllReset₁ hℓ_L₁ hℓ_rc₁ hPosUnitF₁
            exact
              ranking_goal_of_step_ranking_goal
                (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
                (C := C₀) (u := ℓ) (v := v)
                (by simpa [C₁, P] using hgoal₁)

theorem ranking_from_all_resetting_zero_leader_mixed
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (hRmax : n ≤ Rmax)
    (C : Config (AgentState n) Opinion n) {ℓ : Fin n}
    (hAllReset : ∀ w : Fin n, (C w).1.role = .Resetting)
    (hℓ_L : (C ℓ).1.leader = .L)
    (hℓ_rc0 : (C ℓ).1.resetcount = 0)
    (hNoPosLeader : ∀ w : Fin n, (C w).1.leader = .L → (C w).1.resetcount = 0) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t)) := by
  classical
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  by_cases hGt : ∃ v : Fin n, v ≠ ℓ ∧ 1 < (C v).1.resetcount
  · obtain ⟨v, hv_ne_ℓ, hv_gt⟩ := hGt
    have hℓv : ℓ ≠ v := hv_ne_ℓ.symm
    have hv_F : (C v).1.leader = .F := by
      cases hv_leader : (C v).1.leader with
      | L =>
          have hv_zero := hNoPosLeader v hv_leader
          omega
      | F => rfl
    have hstep :=
      step_L_zero_F_pos_gt_one
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        C hℓv (hAllReset ℓ) (hAllReset v) hℓ_rc0 hv_gt hℓ_L hv_F
    let C₁ : Config (AgentState n) Opinion n := C.step P ℓ v
    have hAllReset₁ : ∀ w : Fin n, (C₁ w).1.role = .Resetting := by
      intro w
      by_cases hwℓ : w = ℓ
      · subst w
        simpa [C₁, P] using hstep.1
      · by_cases hwv : w = v
        · subst w
          simpa [C₁, P] using hstep.2.1
        · dsimp [C₁, P]
          simp [Config.step, hℓv, hwℓ, hwv]
          exact hAllReset w
    have hℓ_L₁ : (C₁ ℓ).1.leader = .L := by
      simpa [C₁, P] using hstep.2.2.2.2.1
    have hℓ_pos₁ : 0 < (C₁ ℓ).1.resetcount := by
      have hrc : (C₁ ℓ).1.resetcount = (C v).1.resetcount - 1 := by
        simpa [C₁, P] using hstep.2.2.1
      rw [hrc]
      omega
    have hgoal₁ :=
      ranking_from_all_resetting_with_positive_leader
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hEmax hDmax hRmax C₁ hAllReset₁ hℓ_L₁ hℓ_pos₁
    exact
      ranking_goal_of_step_ranking_goal
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        (C := C) (u := ℓ) (v := v)
        (by simpa [C₁, P] using hgoal₁)
  · have hPosUnitF :
        ∀ w : Fin n, w ≠ ℓ → 0 < (C w).1.resetcount →
          (C w).1.leader = .F ∧ (C w).1.resetcount = 1 := by
      intro w hw_ne hw_pos
      constructor
      · cases hw_leader : (C w).1.leader with
        | L =>
            have hw_zero := hNoPosLeader w hw_leader
            omega
        | F => rfl
      · have hw_not_gt : ¬ 1 < (C w).1.resetcount := by
          intro hw_gt
          exact hGt ⟨w, hw_ne, hw_gt⟩
        omega
    exact
      ranking_from_all_resetting_zero_leader_unit_followers
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hEmax hDmax hRmax C hAllReset hℓ_L hℓ_rc0 hPosUnitF

theorem ranking_from_all_resetting
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (hRmax : n ≤ Rmax)
    (C : Config (AgentState n) Opinion n)
    (hAllReset : ∀ w : Fin n, (C w).1.role = .Resetting) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t)) := by
  classical
  by_cases hHasLeader : ∃ ℓ : Fin n, (C ℓ).1.leader = .L
  · obtain ⟨ℓ, hℓ_L⟩ := hHasLeader
    by_cases hPosLeader : ∃ r : Fin n, (C r).1.leader = .L ∧ 0 < (C r).1.resetcount
    · obtain ⟨r, hr_L, hr_pos⟩ := hPosLeader
      exact
        ranking_from_all_resetting_with_positive_leader
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hn4 hEmax hDmax hRmax C hAllReset hr_L hr_pos
    · have hNoPosLeader :
          ∀ w : Fin n, (C w).1.leader = .L → (C w).1.resetcount = 0 := by
        intro w hw_L
        have hw_not_pos : ¬ 0 < (C w).1.resetcount := by
          intro hw_pos
          exact hPosLeader ⟨w, hw_L, hw_pos⟩
        omega
      exact
        ranking_from_all_resetting_zero_leader_mixed
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hn4 hEmax hDmax hRmax C hAllReset hℓ_L
          (hNoPosLeader ℓ hℓ_L) hNoPosLeader
  · have hNoLeader : ∀ w : Fin n, (C w).1.leader ≠ .L := by
      intro w hw_L
      exact hHasLeader ⟨w, hw_L⟩
    exact
      ranking_from_all_resetting_no_leader
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hEmax hDmax hRmax C hAllReset hNoLeader

theorem ranking_from_resetting_leader_budget
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (hRmax : n ≤ Rmax)
    (C : Config (AgentState n) Opinion n)
    (hReset :
      ∃ r : Fin n, (C r).1.role = .Resetting ∧
        n ≤ (C r).1.resetcount ∧ (C r).1.leader = .L) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t)) := by
  classical
  set P := protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)
  have hDmax_gt_one : 1 < Dmax := by omega
  obtain ⟨L₁, hAllReset₁, _hleader₁⟩ :=
    phase2_propagate_reset_with_leader
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hDmax_gt_one C hReset
  let C₁ : Config (AgentState n) Opinion n := runPairs P C L₁
  have hgoal₁ :=
    ranking_from_all_resetting
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      hn4 hEmax hDmax hRmax C₁
      (by simpa [C₁, P] using hAllReset₁)
  exact
    ranking_goal_of_runPairs_ranking_goal
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
      (C := C) (L := L₁)
      (by simpa [C₁, P] using hgoal₁)

theorem ranking_from_known_reset_entry_or_all_resetting_zero
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (hRmax : n ≤ Rmax)
      (C : Config (AgentState n) Opinion n)
      (hEntry :
        (∀ w : Fin n, (C w).1.role ≠ .Resetting) ∨
        FollowerDormantOrNonResetting C ∨
        ((∃ r : Fin n, (C r).1.role = .Resetting ∧
            n ≤ (C r).1.resetcount ∧ (C r).1.leader = .L) ∧
          ∀ w : Fin n, (C w).1.role = .Resetting → 0 < (C w).1.resetcount) ∨
        ((∀ w : Fin n, (C w).1.role = .Resetting) ∧
          (∀ w : Fin n, 0 < (C w).1.resetcount) ∧
          ∃ r : Fin n, (C r).1.leader = .L) ∨
        ((∀ w : Fin n, (C w).1.role = .Resetting) ∧
          ∀ w : Fin n, (C w).1.resetcount = 0) ∨
        (∀ w : Fin n, (C w).1.role = .Resetting)) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t)) := by
  rcases hEntry with hNoReset | hEntry
  · exact
      ranking_of_no_reset_by_parity
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hEmax hDmax hRmax C hNoReset
  rcases hEntry with hClean | hEntry
  · exact
      follower_dormant_or_nonresetting_to_ranking_goal_by_parity
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hEmax hDmax hRmax C hClean
  rcases hEntry with hSnapshot | hAllReset
  · exact
      ranking_goal_of_reset_snapshot
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hDmax hRmax (C := C) hSnapshot.1 hSnapshot.2
  rcases hAllReset with hAllPos | hAllReset
  · rcases hAllPos with ⟨hAllReset, hAllPos, hHasLeader⟩
    have hRmax_pos : 0 < Rmax := by
      have hn_pos : 0 < n := by omega
      exact Nat.lt_of_lt_of_le hn_pos hRmax
    exact
      ranking_from_all_resetting_pos_with_leader
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        hn4 hRmax_pos hDmax C hAllReset hAllPos hHasLeader
  · rcases hAllReset with hAllZero | hAllReset
    · rcases hAllZero with ⟨hAllReset, hAllZero⟩
      exact
        ranking_from_all_resetting_zero
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            hn4 hEmax hDmax hRmax C hAllReset hAllZero
    · exact
        ranking_from_all_resetting
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hn4 hEmax hDmax hRmax C hAllReset

theorem ranking_from_InSrank_by_parity
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n) (hDmax : n ≤ Dmax) (hRmax : n ≤ Rmax)
    (C : Config (AgentState n) Opinion n)
    (hSrank : InSrank C) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n Rmax Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) C γ t)) := by
  by_cases hDone : RankingEndpoint C
  · exact
      ranking_goal_of_runPairs_RankingEndpoint
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
        (C := C) (L := [])
        (by simpa using hDone)
  · have hbad : BadRankingStart C := ⟨hSrank, hDone⟩
    by_cases hpar : n % 2 = 0
    · obtain ⟨L, hEndpoint⟩ :=
        BadRankingStart_even_to_RankingEndpoint
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hn4 hDmax hRmax hbad hpar
      exact
        ranking_goal_of_runPairs_RankingEndpoint
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          (C := C) (L := L) hEndpoint
    · obtain ⟨L, hEndpoint⟩ :=
        BadRankingStart_odd_to_RankingEndpoint
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          hn4 hDmax hRmax hbad hpar
      exact
        ranking_goal_of_runPairs_RankingEndpoint
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          (C := C) (L := L) hEndpoint

end SSEM
