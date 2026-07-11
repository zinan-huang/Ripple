/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Swap-Phase Reachability via Single-Step Reduction

`hSwapPhase` reduced to a single local hypothesis: from any
`InSrank` configuration with positive misordered count, there exists
an interaction `(u, v)` such that the resulting configuration is still
`InSrank` and has strictly smaller misordered count.

This converts the global existence of a scheduler into a purely local
one-step argument, which is the natural attack point.  Discharging the
local hypothesis requires showing that — for some choice of `(u, v)` —
the propagation reset does not fire (the protocol's median-agent
timer doesn't reach 0 with answer mismatch).
-/

import Ripple.PopulationProtocol.Majority.SSEM.Convergence.PotentialReach
import Ripple.PopulationProtocol.Majority.SSEM.Convergence.SwapPhase

namespace SSEM

variable {n : ℕ}

/-- Swap-phase reachability follows from a single-step decreasing-potential
hypothesis.  Used to instantiate `hSwapPhase` in `Composition.lean`. -/
theorem swap_reaches_Sswap_of_singleStep
    [Inhabited (Fin n × Fin n)]
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hStep : ∀ C : Config (AgentState n) Opinion n,
              InSrank C → 0 < misorderedCount C →
              ∃ u v : Fin n,
                InSrank (C.step (protocolPEM n trank Rmax rankDelta) u v) ∧
                misorderedCount
                  (C.step (protocolPEM n trank Rmax rankDelta) u v)
                  < misorderedCount C) :
    ∀ C : Config (AgentState n) Opinion n, InSrank C →
      ∃ (γ : DetScheduler n) (t : ℕ),
        InSswap (execution (protocolPEM n trank Rmax rankDelta) C γ t) := by
  intro C hC
  obtain ⟨γ, t, hC_t, h0_t⟩ :=
    reach_zero_potential (P := protocolPEM n trank Rmax rankDelta)
      (Pinv := InSrank) (φ := misorderedCount) hStep C hC
  exact ⟨γ, t, InSswap_of_InSrank_of_count_zero hC_t h0_t⟩

/-- Swap-phase reachability via the **macro-step** variant: the
hypothesis can take any finite number of base steps, admitting reset
cycles or other multi-step transitions. -/
theorem swap_reaches_Sswap_of_macroStep
    [Inhabited (Fin n × Fin n)]
    {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hMacro : ∀ C : Config (AgentState n) Opinion n,
              InSrank C → 0 < misorderedCount C →
              ∃ (γ : DetScheduler n) (k : ℕ),
                InSrank (execution (protocolPEM n trank Rmax rankDelta) C γ k) ∧
                misorderedCount
                  (execution (protocolPEM n trank Rmax rankDelta) C γ k)
                  < misorderedCount C) :
    ∀ C : Config (AgentState n) Opinion n, InSrank C →
      ∃ (γ : DetScheduler n) (t : ℕ),
        InSswap (execution (protocolPEM n trank Rmax rankDelta) C γ t) := by
  intro C hC
  obtain ⟨γ, t, hC_t, h0_t⟩ :=
    reach_zero_potential_macro (P := protocolPEM n trank Rmax rankDelta)
      (Pinv := InSrank) (φ := misorderedCount) hMacro C hC
  exact ⟨γ, t, InSswap_of_InSrank_of_count_zero hC_t h0_t⟩

end SSEM
