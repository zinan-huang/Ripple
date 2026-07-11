/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Theorem 4 of Kanaya et al. (2025): `P_EM` Solves SSEM

We deliver the conditional theorem:

  > Assume the (parameterized) ranking subprotocol fixes Settled pairs,
  > and assume that from every initial configuration there exists a
  > scheduler under which the execution reaches a consensus configuration.
  > Then `P_EM` solves self-stabilizing exact majority.

The first hypothesis (`RankDeltaSettledFix`) is satisfied by any
well-formed ranking subprotocol after stabilization (in particular,
Burman et al.'s Optimal-Silent-SSR).  The second hypothesis is the
deep convergence claim — formalizing it requires the ranking
subprotocol's correctness theorem and a 4-phase scheduler construction;
that is the next milestone.

Once a consensus configuration is reached, our preservation lemmas
(`Convergence/Silent.lean`, `Convergence/Step.lean`) give us:
  * the configuration is output-stable, and
  * its outputs match the input majority.

Hence `SolvesSSEM` follows.
-/

import Ripple.PopulationProtocol.Majority.SSEM.Convergence.Step

namespace SSEM

variable {n : ℕ}

/-- The conditional Theorem 4: `P_EM` solves self-stabilizing exact majority,
assuming every initial configuration can be driven to a consensus
configuration by some scheduler. -/
theorem P_EM_solves_SSEM_of_consensus_reachable {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    (hReach : ∀ C₀ : Config (AgentState n) Opinion n,
      ∃ (γ : DetScheduler n) (t : ℕ),
        IsConsensusConfig (execution (protocolPEM n trank Rmax rankDelta) C₀ γ t)) :
    SolvesSSEM (protocolPEM n trank Rmax rankDelta) n := by
  intro C₀
  obtain ⟨γ, t, hCons⟩ := hReach C₀
  refine ⟨γ, t, ?_, ?_⟩
  · -- isOutputStable at the reached consensus configuration.
    exact hCons.isOutputStable hRank
  · -- ExactMajoritySafe' at the reached consensus configuration.
    -- The input multiset of the reached configuration equals C₀'s, since
    -- inputs are immutable through execution. So `ExactMajoritySafe'` of
    -- the reached config implies the same for C₀'s input counts.
    -- Note: the SolvesSSEM definition uses the agentsWithInput cards of
    -- the ENDED-AT config, which is what `exactMajoritySafe` provides.
    exact hCons.exactMajoritySafe

end SSEM
