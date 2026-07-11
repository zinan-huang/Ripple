/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Reachability Composition for hReach

Discharging the consensus-reachability hypothesis by chaining three
phase-reachability hypotheses:

  * `hRankPhase`     — every initial configuration eventually reaches
                       an `Srank` configuration (ranking convergence,
                       Burman et al. PODC 2021).
  * `hSwapPhase`     — every `Srank` configuration eventually reaches
                       an `Sswap` configuration (input-sorted ranks).
  * `hDecisionPhase` — every `Sswap` configuration eventually reaches
                       a consensus configuration.

The composed result is the `hReach` hypothesis assumed by
`P_EM_solves_SSEM_of_consensus_reachable`.

Each phase hypothesis is a separable subgoal: ranking is the deep
external reference (Burman et al.); swap and decision are local
protocol arguments that we will discharge by deterministic scheduler
constructions in `SwapPhase.lean` and `DecisionPhase.lean`.
-/

import Ripple.PopulationProtocol.Majority.SSEM.Convergence.Schedule
import Ripple.PopulationProtocol.Majority.SSEM.Convergence.Sets
import Ripple.PopulationProtocol.Majority.SSEM.Convergence.Theorem4

namespace SSEM

variable {n : ℕ}

/-- Composition: from per-phase reachability, derive the full
consensus-reachability hypothesis used by `P_EM_solves_SSEM_of_consensus_reachable`. -/
theorem hReach_of_phases {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRankPhase : ∀ C₀ : Config (AgentState n) Opinion n,
      ∃ (γ : DetScheduler n) (t : ℕ),
        InSrank (execution (protocolPEM n trank Rmax rankDelta) C₀ γ t))
    (hSwapPhase : ∀ C : Config (AgentState n) Opinion n, InSrank C →
      ∃ (γ : DetScheduler n) (t : ℕ),
        InSswap (execution (protocolPEM n trank Rmax rankDelta) C γ t))
    (hDecisionPhase : ∀ C : Config (AgentState n) Opinion n, InSswap C →
      ∃ (γ : DetScheduler n) (t : ℕ),
        IsConsensusConfig (execution (protocolPEM n trank Rmax rankDelta) C γ t)) :
    ∀ C₀ : Config (AgentState n) Opinion n,
      ∃ (γ : DetScheduler n) (t : ℕ),
        IsConsensusConfig (execution (protocolPEM n trank Rmax rankDelta) C₀ γ t) := by
  -- First chain Srank → Sswap.
  have h12 : ∀ C₀, ∃ γ t, InSswap (execution (protocolPEM n trank Rmax rankDelta) C₀ γ t) :=
    reachable_compose hRankPhase hSwapPhase
  -- Then chain Sswap → IsConsensusConfig.
  exact reachable_compose h12 hDecisionPhase

/-- The full unconditional theorem statement, with the three phase
reachabilities exposed as hypotheses on the parameterized ranking
subprotocol. -/
theorem P_EM_solves_SSEM_via_phases {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    (hRankPhase : ∀ C₀ : Config (AgentState n) Opinion n,
      ∃ (γ : DetScheduler n) (t : ℕ),
        InSrank (execution (protocolPEM n trank Rmax rankDelta) C₀ γ t))
    (hSwapPhase : ∀ C : Config (AgentState n) Opinion n, InSrank C →
      ∃ (γ : DetScheduler n) (t : ℕ),
        InSswap (execution (protocolPEM n trank Rmax rankDelta) C γ t))
    (hDecisionPhase : ∀ C : Config (AgentState n) Opinion n, InSswap C →
      ∃ (γ : DetScheduler n) (t : ℕ),
        IsConsensusConfig (execution (protocolPEM n trank Rmax rankDelta) C γ t)) :
    SolvesSSEM (protocolPEM n trank Rmax rankDelta) n :=
  P_EM_solves_SSEM_of_consensus_reachable hRank
    (hReach_of_phases hRankPhase hSwapPhase hDecisionPhase)

end SSEM
