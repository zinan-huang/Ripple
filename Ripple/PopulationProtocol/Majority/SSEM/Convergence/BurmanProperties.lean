/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Abstract Burman Properties

This file defines the abstract properties that the ranking subprotocol
`rankDelta` must satisfy for the full P_EM protocol to work. These
correspond to the results from Burman et al. (PODC 2021) that Kanaya
et al. rely on.

## Structure

* `BurmanConvergence` — ranking convergence + epidemic propagation
* `ProtocolConvergence` — BurmanConvergence + timer invariant (h_inv_swap)
* `P_EM_solves_SSEM_from_single_hypothesis` — master theorem from
  `ProtocolConvergence` alone
* `P_EM_solves_SSEM_concrete_burman` — concrete instantiation with `rankDeltaOSSR`

## Timer invariant status

The swap phase does NOT need h_inv_swap (eliminated via
`swap_reaches_Sswap_from_timer_bound` in SwapFromRanking.lean). However,
the odd-n decision phase still needs h_inv_dec (timer ≥ 1 at InSswap),
derived from h_inv_swap. Future work: strengthen BurmanConvergence.epidemic
to include timer ≥ 1 at output, then derive h_inv_dec from it.
-/

import Ripple.PopulationProtocol.Majority.SSEM.Convergence.EvenNComplete
import Ripple.PopulationProtocol.Majority.SSEM.Convergence.SwapFromRanking
import Ripple.PopulationProtocol.Majority.SSEM.Protocol.RankDelta

namespace SSEM

variable {n : ℕ}

/-! ### The combined Burman hypothesis -/

/-- **BurmanConvergence**: the single bundled external assumption that
replaces `h_burman_ranking` and `BurmanRankingCorrect`.

Part 1 (`ranking`): from any initial configuration, there exists a
deterministic schedule reaching `InSrank` where the median's timer is
≥ 2. This combines ranking convergence with timer initialization.

Part 2 (`epidemic`): from any configuration where at least one agent
has the correct majority answer, there exists a deterministic schedule
reaching `InSswap` with ALL agents having the correct answer. This
captures the epidemic propagation + re-ranking + re-swapping. -/
structure BurmanConvergence
    (trank Rmax : ℕ)
    (rankDelta : AgentState n × AgentState n → AgentState n × AgentState n) : Prop where
  ranking : ∀ C₀ : Config (AgentState n) Opinion n,
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSrank (execution (protocolPEM n trank Rmax rankDelta) C₀ γ t) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n trank Rmax rankDelta) C₀ γ t μ).1.rank.val + 1 = ceilHalf n →
        2 ≤ (execution (protocolPEM n trank Rmax rankDelta) C₀ γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n trank Rmax rankDelta) C₀ γ t))
  -- NOTE: the median-timer clause is a *disjunct* with `IsConsensusConfig`,
  -- mirroring the `ranking` field above. An unconditional `1 ≤ timer@median`
  -- is FALSE: a configuration that is already `InSswap`, all-answers-correct,
  -- with `timer = 0` at the median satisfies the hypothesis but admits no
  -- recovery (`phase4_propagate` only does `timer := timer - 1`, never
  -- increases; no answer-mismatch ⇒ no reset ⇒ no re-rank ⇒ no timer
  -- re-init). Since `InSswap ∧ all-correct ⟺ IsConsensusConfig`
  -- (`InStim_iff_IsConsensusConfig`), the consensus disjunct is the honest
  -- post-condition; the timer disjunct is kept for the decision-phase
  -- consumer that still has wrong answers to fix.
  epidemic : ∀ C₀ : Config (AgentState n) Opinion n,
    (∃ w : Fin n, (C₀ w).1.answer = majorityAnswer C₀) →
    ∃ (γ : DetScheduler n) (t : ℕ),
      InSswap (execution (protocolPEM n trank Rmax rankDelta) C₀ γ t) ∧
      (∀ w : Fin n,
        (execution (protocolPEM n trank Rmax rankDelta) C₀ γ t w).1.answer = majorityAnswer C₀) ∧
      ((∀ μ : Fin n,
        (execution (protocolPEM n trank Rmax rankDelta) C₀ γ t μ).1.rank.val + 1 = ceilHalf n →
        1 ≤ (execution (protocolPEM n trank Rmax rankDelta) C₀ γ t μ).1.timer) ∨
       IsConsensusConfig (execution (protocolPEM n trank Rmax rankDelta) C₀ γ t))

/-! ### Derivation of the three hypotheses -/

theorem BurmanConvergence.h_burman_ranking
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hBC : BurmanConvergence trank Rmax rankDelta) :
    ∀ C₀ : Config (AgentState n) Opinion n,
      ∃ (γ : DetScheduler n) (t : ℕ),
        InSrank (execution (protocolPEM n trank Rmax rankDelta) C₀ γ t) := by
  intro C₀; obtain ⟨γ, t, hInSrank, _⟩ := hBC.ranking C₀; exact ⟨γ, t, hInSrank⟩

theorem BurmanConvergence.burmanRankingCorrect
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hBC : BurmanConvergence trank Rmax rankDelta) :
    BurmanRankingCorrect trank Rmax rankDelta := by
  intro C₀ hC₀
  obtain ⟨γ, t, hSwap, hAnswers, _⟩ := hBC.epidemic C₀ hC₀
  exact ⟨γ, t, hSwap, hAnswers⟩

/-! ### Master theorem -/

/-- **ProtocolConvergence**: the SINGLE external hypothesis needed for
the master theorem. Bundles `BurmanConvergence` and the timer invariant.

The timer invariant (`timer_inv`) is needed by the odd-n decision phase.
The swap phase does NOT need it (eliminated via SwapFromRanking). -/
structure ProtocolConvergence
    (trank Rmax : ℕ)
    (rankDelta : AgentState n × AgentState n → AgentState n × AgentState n) : Prop where
  burman : BurmanConvergence trank Rmax rankDelta
  timer_inv : ∀ C : Config (AgentState n) Opinion n, InSrank C →
                ∀ μ : Fin n, (C μ).1.rank.val + 1 = ceilHalf n →
                2 ≤ (C μ).1.timer

/-- **Theorem 4 from ProtocolConvergence.**

The swap phase uses `swap_reaches_Sswap_from_timer_bound` (timer ≥ 2
at the specific InSrank from ranking, not universally). The decision
phase uses h_inv_swap for the odd-n witness. -/
theorem P_EM_solves_SSEM_from_single_hypothesis
    [Inhabited (Fin n × Fin n)]
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    (hn4 : 4 ≤ n)
    (hPC : ProtocolConvergence trank Rmax rankDelta) :
    SolvesSSEM (protocolPEM n trank Rmax rankDelta) n :=
  P_EM_solves_SSEM_ultimate hRank hn4
    hPC.burman.burmanRankingCorrect
    hPC.burman.h_burman_ranking
    hPC.timer_inv

/-! ### Master theorem from BurmanConvergence alone -/

/-- Timer ≥ K preserved through Config.step when neither agent has max
rank, for any Settled pair in InSrank. Combines the misordered and
non-misordered timer preservation lemmas. -/
theorem step_preserves_timer_no_max
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n} (hC : InSrank C)
    {u v : Fin n} (huv : u ≠ v)
    (h_no_max_u : (C u).1.rank.val + 1 ≠ n)
    (h_no_max_v : (C v).1.rank.val + 1 ≠ n)
    {K : ℕ}
    (h_ge : ∀ μ : Fin n, (C μ).1.rank.val + 1 = ceilHalf n → K ≤ (C μ).1.timer) :
    ∀ μ : Fin n,
      (C.step (protocolPEM n trank Rmax rankDelta) u v μ).1.rank.val + 1 = ceilHalf n →
      K ≤ (C.step (protocolPEM n trank Rmax rankDelta) u v μ).1.timer := by
  have hsu := hC.allSettled u
  have hsv := hC.allSettled v
  by_cases hswap : (C u).1.rank < (C v).1.rank ∧ (C u).2 = Opinion.B ∧ (C v).2 = Opinion.A
  · -- Misordered: use step_at_misorder_preserves_timer_geK
    exact step_at_misorder_preserves_timer_geK
      (trank := trank) (Rmax := Rmax) hRank hC ⟨hswap.2.1, hswap.2.2, hswap.1⟩
      h_no_max_u h_no_max_v h_ge
  · -- Non-misordered: swap doesn't fire, timer preserved exactly
    have hne_rank : (C u).1.rank ≠ (C v).1.rank := fun h => huv (hC.ranks_inj h)
    have h_ns := transitionPEM_timer_of_no_max_no_swap (trank := trank) (Rmax := Rmax)
      hRank hsu hsv h_no_max_u h_no_max_v hswap hne_rank
    intro μ hμ
    by_cases hμu : μ = u
    · rw [hμu] at hμ ⊢
      have h_rk := transitionPEM_rank_of_no_swap (trank := trank) (Rmax := Rmax)
        hRank hsu hsv hswap hne_rank
      have h_fst := Config.step_fst_state (protocolPEM n trank Rmax rankDelta) C huv
      -- Timer at position u = (C u).1.timer (no swap, no decrement)
      have h_t : (C.step _ u v u).1.timer = (C u).1.timer :=
        congrArg AgentState.timer h_fst ▸ h_ns.1
      -- Rank at position u = (C u).1.rank (no swap)
      have h_r : (C.step _ u v u).1.rank = (C u).1.rank :=
        congrArg AgentState.rank h_fst ▸ h_rk.1
      rw [h_t]
      have : (C u).1.rank.val + 1 = ceilHalf n := by
        have := congrArg Fin.val h_r; omega
      exact h_ge u this
    · by_cases hμv : μ = v
      · rw [hμv] at hμ ⊢
        have h_rk := transitionPEM_rank_of_no_swap (trank := trank) (Rmax := Rmax)
          hRank hsu hsv hswap hne_rank
        have h_snd := Config.step_snd_state (protocolPEM n trank Rmax rankDelta) C huv huv.symm
        have h_t : (C.step _ u v v).1.timer = (C v).1.timer :=
          congrArg AgentState.timer h_snd ▸ h_ns.2
        have h_r : (C.step _ u v v).1.rank = (C v).1.rank :=
          congrArg AgentState.rank h_snd ▸ h_rk.2
        rw [h_t]
        have : (C v).1.rank.val + 1 = ceilHalf n := by
          have := congrArg Fin.val h_r; omega
        exact h_ge v this
      · unfold Config.step at hμ ⊢
        simp only [if_neg huv, if_neg hμu, if_neg hμv] at hμ ⊢
        exact h_ge μ hμ

/-! ### Master theorem from BurmanConvergence alone -/

/-- `BurmanConvergence` gives deterministic reachability of an
`IsConsensusConfig` endpoint from every initial configuration.  This is the
reachability fact hidden inside the qualitative `SolvesSSEM` theorem and is
the deterministic input needed by the stochastic time-bound layer. -/
theorem P_EM_consensus_reachable_from_BurmanConvergence_only
    [Inhabited (Fin n × Fin n)]
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    (hn4 : 4 ≤ n)
    (hBC : BurmanConvergence trank Rmax rankDelta) :
    ∀ C₀ : Config (AgentState n) Opinion n,
      ∃ (γ : DetScheduler n) (t : ℕ),
        IsConsensusConfig (execution (protocolPEM n trank Rmax rankDelta) C₀ γ t) := by
  set P := protocolPEM n trank Rmax rankDelta
  have hBMDT := discharge_BurmanMacroDecisionWithTimer hBC.epidemic (by omega : 0 < n)
  intro C₀
  obtain ⟨γ₁, t₁, hInSrank₁, h_timer_or_cons⟩ := hBC.ranking C₀
  obtain h_timer₁ | hCons := h_timer_or_cons
  · obtain ⟨γ₂, t₂, hInSswap₂, h_timer₂⟩ :=
    swap_reaches_Sswap_from_timer_bound_with_timer hRank hn4 hInSrank₁ h_timer₁
    -- Decision phase. `DecInv` carries `timer ≥ 1 @ median`, needed by the
    -- median-wrong single-step witnesses. The median-correct case escapes
    -- via the epidemic, which yields `IsConsensusConfig` directly (the goal),
    -- so we recurse on `wrongAnswerCount` with an early exit on consensus.
    set DecInv := fun C : Config (AgentState n) Opinion n =>
      InSswap C ∧ ∀ μ : Fin n, (C μ).1.rank.val + 1 = ceilHalf n → 1 ≤ (C μ).1.timer
      with hDecInv_def
    have hDrive : ∀ (b : ℕ) (C : Config (AgentState n) Opinion n),
        DecInv C → wrongAnswerCount C ≤ b →
        ∃ (γ : DetScheduler n) (t : ℕ), IsConsensusConfig (execution P C γ t) := by
      intro b
      induction b with
      | zero =>
        intro C ⟨hC, _⟩ hle
        have hzero : wrongAnswerCount C = 0 := Nat.le_zero.mp hle
        exact ⟨fun _ => default, 0,
          isConsensusConfig_of_InSswap_of_wrongAnswerCount_zero hC hzero⟩
      | succ b ih =>
        intro C ⟨hC, hC_timer⟩ hle
        classical
        by_cases hpos : 0 < wrongAnswerCount C
        · by_cases h_med_correct :
              ∀ μ : Fin n, (C μ).1.rank.val + 1 = ceilHalf n →
                           (C μ).1.answer = majorityAnswer C
          · -- Median correct → epidemic reaches consensus directly.
            exact hBMDT C hC hpos h_med_correct
          · -- Median wrong → non-circular single step, then recurse.
            push_neg at h_med_correct
            obtain ⟨μ, hμ_med, hμ_wrong⟩ := h_med_correct
            -- One non-circular decision step at a chosen pair, decreasing
            -- `wrongAnswerCount` and preserving `DecInv`; then recurse.
            have hStep : ∃ p : Fin n × Fin n,
                DecInv (C.step P p.1 p.2) ∧
                wrongAnswerCount (C.step P p.1 p.2) < wrongAnswerCount C := by
              by_cases hpar : n % 2 = 0
              · by_cases hTie : nAOf C = nBOf C
                · obtain ⟨u, v, huv, hu_med, hv_upper, h_disagree, h_wrong⟩ :=
                    evenCase_witness_when_median_wrong_tie hC hpar hn4 hTie ⟨μ, hμ_med, hμ_wrong⟩
                  have h_dec := decision_step_at_median_pair_even_tie_decreases
                    (trank := trank) (Rmax := Rmax) hRank hC huv hpar hu_med hv_upper h_disagree hTie hn4 h_wrong
                  have hu_no_max : (C u).1.rank.val + 1 ≠ n := by omega
                  have hv_no_max : (C v).1.rank.val + 1 ≠ n := by omega
                  exact ⟨(u, v),
                    ⟨h_dec.1,
                     step_preserves_timer_no_max hRank hC.toInSrank huv hu_no_max hv_no_max hC_timer⟩,
                    h_dec.2⟩
                · obtain ⟨u, v, huv, hu_med, hv_upper, h_agree, h_wrong⟩ :=
                    evenCase_witness_when_median_wrong hC hpar hn4 hTie ⟨μ, hμ_med, hμ_wrong⟩
                  have h_dec := decision_step_at_median_pair_even_decreases
                    (trank := trank) (Rmax := Rmax) hRank hC huv hpar hu_med hv_upper h_agree hTie hn4 h_wrong
                  have hu_no_max : (C u).1.rank.val + 1 ≠ n := by omega
                  have hv_no_max : (C v).1.rank.val + 1 ≠ n := by omega
                  exact ⟨(u, v),
                    ⟨h_dec.1,
                     step_preserves_timer_no_max hRank hC.toInSrank huv hu_no_max hv_no_max hC_timer⟩,
                    h_dec.2⟩
              · obtain ⟨μ', v, hμv, hμ'_med, hv_no_med, hv_no_max, h_rank_gt, h_timer, hμ'_wrong⟩ :=
                  oddCase_witness_when_median_wrong_with_timer hC hpar (by omega : 3 ≤ n)
                    ⟨μ, hμ_med, hμ_wrong⟩ hC_timer
                have h_step := decision_step_at_median_no_swap_odd_decreases
                  (trank := trank) (Rmax := Rmax) hRank hC hμv hpar hμ'_med hv_no_med hv_no_max h_rank_gt h_timer hμ'_wrong
                have hμ'_no_max : (C μ').1.rank.val + 1 ≠ n := by
                  unfold ceilHalf at hμ'_med; omega
                exact ⟨(μ', v),
                  ⟨h_step.1,
                   step_preserves_timer_no_max hRank hC.toInSrank hμv hμ'_no_max hv_no_max hC_timer⟩,
                  h_step.2⟩
            obtain ⟨p, hC', hdec⟩ := hStep
            have hle' : wrongAnswerCount (C.step P p.1 p.2) ≤ b := by omega
            obtain ⟨γ', t', hcons⟩ := ih (C.step P p.1 p.2) hC' hle'
            refine ⟨concatScheduler (fun _ => p) 1 γ', 1 + t', ?_⟩
            have hone : execution P C (fun _ => p) 1 = C.step P p.1 p.2 := rfl
            rw [execution_concat, hone]; exact hcons
        · push_neg at hpos
          have hzero : wrongAnswerCount C = 0 := Nat.le_zero.mp hpos
          exact ⟨fun _ => default, 0,
            isConsensusConfig_of_InSswap_of_wrongAnswerCount_zero hC hzero⟩
    set C₂ := execution P (execution P C₀ γ₁ t₁) γ₂ t₂
    obtain ⟨γ₃, t₃, hCons₃⟩ :=
      hDrive (wrongAnswerCount C₂) C₂ ⟨hInSswap₂, h_timer₂⟩ le_rfl
    exact ⟨concatScheduler (concatScheduler γ₁ t₁ γ₂) (t₁ + t₂) γ₃,
      t₁ + t₂ + t₃,
      by rw [execution_concat, execution_concat]; exact hCons₃⟩
  · exact ⟨γ₁, t₁, hCons⟩

/-- **Theorem 4 from BurmanConvergence alone** (no timer_inv). -/
theorem P_EM_solves_SSEM_from_BurmanConvergence_only
    [Inhabited (Fin n × Fin n)]
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    (hn4 : 4 ≤ n)
    (hBC : BurmanConvergence trank Rmax rankDelta) :
    SolvesSSEM (protocolPEM n trank Rmax rankDelta) n := by
  apply P_EM_solves_SSEM_of_consensus_reachable hRank
  exact P_EM_consensus_reachable_from_BurmanConvergence_only hRank hn4 hBC

/-! ### Timer_inv elimination — infrastructure complete

All pieces are in place to prove P_EM_solves_SSEM_from_BurmanConvergence_only
(master theorem from BurmanConvergence alone, no timer_inv):

  * Swap phase: swap_reaches_Sswap_from_timer_bound_with_timer
  * Decision macro-step (median correct): BurmanMacroDecisionWithTimer
  * Decision single-step timer preservation: step_preserves_timer_no_max
  * Schedule composition: reach_zero_potential_macro with DecisionInv

Remaining: compose the decision single-step theorems
(decision_step_at_median_no_swap_odd_decreases for odd n,
wrongAnswerCount_decreases_at_median_pair_even for even n)
with step_preserves_timer_no_max to get InSswap + timer ≥ 1 + count
decrease in each median-wrong case (~50 lines per parity).
-/

/-! ### Concrete instantiation with `rankDeltaOSSR` -/

/-- **Concrete Theorem 4**: P_EM with `rankDeltaOSSR` solves SSEM.
Uses rankDeltaOSSR directly (not the rankDeltaStable wrapper), enabling
collision detection for the BurmanConvergence proof. -/
theorem P_EM_solves_SSEM_concrete_burman
    [Inhabited (Fin n × Fin n)]
    {trank Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n)
    (hBC : BurmanConvergence trank Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) :
    SolvesSSEM (protocolPEM n trank Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) n :=
  P_EM_solves_SSEM_from_BurmanConvergence_only
    rankDeltaOSSR_satisfies_fix
    hn4
    hBC

end SSEM
