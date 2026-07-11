/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Timer Descent at the Median

The reset cycle of `P_EM` is gated by the median agent's `.timer` field
hitting zero.  This file develops the single-step lemma showing that
under appropriate hypotheses, an interaction at `(μ, v)` with `μ` at the
median rank and `v` at the maximum rank strictly decreases the median's
timer by 1.

Combined with `PotentialReach`, this lifts to a macro-step result: from
any `InSrank` configuration, the system reaches a state in which the
median's timer is zero (at which point the next misorder-favoured step
fires reset).

This is the first piece of the macro-step machinery (阶段 A of the
plan) preceding the reset-cycle module (`ResetCycle.lean`).
-/

import Ripple.PopulationProtocol.Majority.SSEM.Convergence.RankPreservation

namespace SSEM

variable {n : ℕ}

/-! ### medianTimer: the timer field of the median agent -/

/-- The position of the median agent in an `InSrank` configuration.  Uses
classical choice to extract the witness from `InSrank.exists_median`. -/
noncomputable def medianAgent {C : Config (AgentState n) Opinion n}
    (hC : InSrank C) (hn : 0 < n) : Fin n :=
  (hC.exists_median hn).choose

/-- The chosen median agent does sit at the median rank. -/
theorem medianAgent_rank {C : Config (AgentState n) Opinion n}
    (hC : InSrank C) (hn : 0 < n) :
    (C (medianAgent hC hn)).1.rank.val + 1 = ceilHalf n :=
  (hC.exists_median hn).choose_spec

/-- The `.timer` field of the median agent — the potential function
governing the reset cycle. -/
noncomputable def medianTimer {C : Config (AgentState n) Opinion n}
    (hC : InSrank C) (hn : 0 < n) : ℕ :=
  (C (medianAgent hC hn)).1.timer

/-! ### Timer descent at the misorder-median-pair (swap-fires, odd n) -/

/-- At a misorder pair `(μ, v)` with `μ` at the median, `v` at the
maximum rank, odd `n`, and `(C μ).1.timer ≥ 2`, the post-step
configuration's `medianTimer` is `(C μ).1.timer - 1`.

This is the single-step potential decrease: the agent that ends up at
the median rank after the step (which is the one originally at position
`μ`, after being moved to position `v` by the swap) has timer one less
than before, and the timer field is unchanged for all other agents. -/
theorem medianTimer_decreases_at_misorder_median_v_max_odd
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n} (hC : InSrank C) (hn : 0 < n)
    {μ v : Fin n} (hMis : MisorderedPair C (μ, v))
    (hpar : ¬ n % 2 = 0)
    (hμ_med : (C μ).1.rank.val + 1 = ceilHalf n)
    (hv_max : (C v).1.rank.val + 1 = n)
    (h_timer : 2 ≤ (C μ).1.timer) :
    let C' := C.step (protocolPEM n trank Rmax rankDelta) μ v
    let hC' : InSrank C' :=
      (swap_step_decreases_at_misorder_u_median_odd_v_max
         hRank hC hMis hpar hμ_med hv_max h_timer).1
    medianTimer hC' hn + 1 = (C μ).1.timer := by
  -- Use the explicit transitionPEM lemma to compute C'.
  have h_step : C.step (protocolPEM n trank Rmax rankDelta) μ v =
      fun w => if w = μ then ((C v).1, (C μ).2)
               else if w = v then
                 ({(C μ).1 with answer := opinionToAnswer (C v).2,
                                timer := (C μ).1.timer - 1}, (C v).2)
               else C w := by
    have hμv : μ ≠ v := by
      intro heq; rw [heq] at hMis; exact absurd hMis.2.2 (lt_irrefl _)
    funext w
    unfold Config.step
    simp only [if_neg hμv]
    show (if w = μ then
            ((transitionPEM n trank Rmax rankDelta (C μ, C v)).1, (C μ).2)
          else if w = v then
            ((transitionPEM n trank Rmax rankDelta (C μ, C v)).2, (C v).2)
          else C w) = _
    rw [transitionPEM_at_misordered_u_median_odd_v_max
          hRank hC hMis hpar hμ_med hv_max h_timer]
  -- The post-step InSrank uses ranks_inj from C; the median agent in C'
  -- is the position whose .rank is ceilHalf n - 1.  In C', position μ
  -- holds (C v).1 with rank n-1, position v holds (modified (C μ).1)
  -- with rank median.  So medianAgent C' = v (with timer = (C μ).1.timer - 1).
  have hvμ : v ≠ μ := fun h => by
    rw [h] at hv_max
    have hlt : (C μ).1.rank.val < (C v).1.rank.val := hMis.2.2
    rw [h] at hlt; exact absurd hlt (lt_irrefl _)
  have hC' : InSrank (C.step (protocolPEM n trank Rmax rankDelta) μ v) :=
    (swap_step_decreases_at_misorder_u_median_odd_v_max
       hRank hC hMis hpar hμ_med hv_max h_timer).1
  -- (C.step P μ v) at position v = ({(C μ).1 with ...}, (C v).2).
  have h_at_v : C.step (protocolPEM n trank Rmax rankDelta) μ v v =
      ({(C μ).1 with answer := opinionToAnswer (C v).2,
                     timer := (C μ).1.timer - 1}, (C v).2) := by
    rw [h_step]; simp [hvμ]
  -- Median agent in (C.step ...) has rank ceilHalf n - 1.
  have hv_in_C'_rank :
      (C.step (protocolPEM n trank Rmax rankDelta) μ v v).1.rank.val + 1 = ceilHalf n := by
    rw [h_at_v]; exact hμ_med
  -- Hence medianAgent of (C.step ...) = v.
  have h_median_eq : medianAgent hC' hn = v := by
    apply hC'.ranks_inj
    apply Fin.eq_of_val_eq
    have h1 := medianAgent_rank hC' hn
    have h2 := hv_in_C'_rank
    -- h1 : median_rank.val + 1 = ceilHalf n
    -- h2 : v_rank.val + 1 = ceilHalf n
    -- Hence median_rank.val = v_rank.val.
    have : (C.step (protocolPEM n trank Rmax rankDelta) μ v (medianAgent hC' hn)).1.rank.val =
           (C.step (protocolPEM n trank Rmax rankDelta) μ v v).1.rank.val := by omega
    exact this
  -- Compute medianTimer.
  have h_C'v_timer :
      (C.step (protocolPEM n trank Rmax rankDelta) μ v v).1.timer =
        (C μ).1.timer - 1 := by
    rw [h_at_v]
  show medianTimer hC' hn + 1 = (C μ).1.timer
  unfold medianTimer
  rw [h_median_eq, h_C'v_timer]
  omega

end SSEM
