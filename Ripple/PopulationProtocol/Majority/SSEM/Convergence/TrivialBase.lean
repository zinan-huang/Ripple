/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Trivial Base Cases for Theorem 4

If the initial configuration is already a consensus configuration, the
existence claim of `SolvesSSEM` holds with `t = 0`: zero steps suffice.
This gives a fully unconditional Theorem 4 in the special case where
"start = already consensus", and serves as the base case for the
general phase-decomposition.
-/

import Ripple.PopulationProtocol.Majority.SSEM.Convergence.Theorem4

namespace SSEM

variable {n : ℕ}

/-- If a configuration is already a consensus configuration, then `SolvesSSEM`
holds for that initial configuration: the trivial `t = 0` schedule witnesses
the existence claim. -/
theorem trivial_reach_consensus
    [Inhabited (Fin n × Fin n)]
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    {C : Config (AgentState n) Opinion n} (hC : IsConsensusConfig C) :
    ∃ (γ : DetScheduler n) (t : ℕ),
      IsConsensusConfig (execution (protocolPEM n trank Rmax rankDelta) C γ t) :=
  ⟨fun _ => default, 0, hC⟩

/-- If every initial configuration is already a consensus configuration, then
`P_EM` solves SSEM. (A degenerate but useful base case.) -/
theorem P_EM_solves_SSEM_when_all_consensus
    [Inhabited (Fin n × Fin n)]
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    (hAll : ∀ C₀ : Config (AgentState n) Opinion n, IsConsensusConfig C₀) :
    SolvesSSEM (protocolPEM n trank Rmax rankDelta) n :=
  P_EM_solves_SSEM_of_consensus_reachable hRank
    (fun C₀ => trivial_reach_consensus (hAll C₀))

end SSEM
