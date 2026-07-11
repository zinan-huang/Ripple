import Ripple.PopulationProtocol.Majority.SSEM.UpperBound.Time.PolynomialBound

namespace SSEM

open scoped ENNReal

/-- Consensus is absorbing under PEMProtocolCoupled. -/
theorem PEMProtocolCoupled_consensus_absorbing
    {n Rmax Emax Dmax : ℕ} (hn0 : 0 < n)
    {C : Config (AgentState n) Opinion n}
    (hC : IsConsensusConfig C) (i j : Fin n) :
    IsConsensusConfig
      (C.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) i j) := by
  have hfix : RankDeltaSettledFix (rankDeltaOSSR Rmax Emax Dmax hn0) :=
    rankDeltaOSSR_satisfies_fix
  simpa [PEMProtocolCoupled, PEMProtocol] using step_preserves_consensus hfix hC i j

/-- From any IsBoundedConfig, E[T to consensus] < ⊤. -/
theorem PEM_consensus_bounded
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n)
    (hRmax : n ≤ Rmax) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (C : Config (AgentState n) Opinion n)
    (hBounded : IsBoundedConfig (7 * (Rmax + 4) + Emax + Dmax) C) :
    Probability.expectedHittingTime
      (PEMProtocolCoupled' n Rmax Emax Dmax hn0)
      (by omega : 2 ≤ n) C IsConsensusConfig < ⊤ :=
  bounded_config_to_consensus hn4 hn0 hRmax hEmax hDmax C hBounded

/-- End-to-end: from any initial config, expected parallel time is finite. -/
theorem PEM_expected_parallel_time_finite_init
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n)
    (hRmax : n ≤ Rmax) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (C₀ : Config (AgentState n) Opinion n)
    (hInit : IsInitialConfig C₀) :
    Probability.expectedParallelTimeToConsensus
      (PEMProtocolCoupled' n Rmax Emax Dmax hn0)
      (by omega : 2 ≤ n) C₀ < ⊤ := by
  have hBounded : IsBoundedConfig (7 * (Rmax + 4) + Emax + Dmax) C₀ := by
    intro w; have h := hInit w
    exact ⟨by omega, by omega, by omega, by omega, by omega⟩
  have hSeq := bounded_config_to_consensus hn4 hn0 hRmax hEmax hDmax C₀ hBounded
  exact ENNReal.div_lt_top (ne_of_lt hSeq) (by exact_mod_cast (show (n : ℕ) ≠ 0 by omega))

end SSEM
