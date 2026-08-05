/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.MultiFiniteHorizonConsensus
import Tri.MultiProductivePhase0Stage
import Tri.InfectionTriEntry

/-!
# Binary-Theorem-1(b) handoff for the multi-species process

Once the distinguished species beats the aggregate opposition by a gap whose
square meets the ordinary Tri threshold, the finite-horizon binary envelope
and Theorem 1(b) drive the physical multi-species chain to consensus.
-/

namespace Tri.Multi

open scoped ENNReal

variable {m n : ℕ}

/-- The proved ordinary-Tri Theorem 1(b), transferred through the binary lower
envelope to the physical multi-species chain after aggregate handoff. -/
theorem theorem1b_multi_aggregate_reaches_consensus :
    ∃ C n₀ : ℕ, ∃ c : ℝ,
      0 < C ∧ 0 < c ∧ 3 ≤ n₀ ∧
      ∀ m n gamma d : ℕ, ∀ X : Species m, ∀ h3 : 3 ≤ n,
        n₀ ≤ n →
        1 ≤ gamma →
        6 * gamma * Nat.log 2 n ≤ n →
        Reaches
          (fun q : Config m n => multiStep q h3)
          (C * gamma * n * Nat.log 2 n)
          (fun q =>
            Phase0AggregateHandoff X d q ∧
              gamma * n * Nat.log 2 n ≤ d ^ 2)
          (fun q => ConsensusOn q X)
          ((n : ℝ≥0∞)⁻¹ ^ (c * (gamma : ℝ))) := by
  rcases Tri.theorem1b_reaches_top with
    ⟨C, n₀, c, hC, hc, hn₀, htri⟩
  refine ⟨C, n₀, c, hC, hc, hn₀, ?_⟩
  intro m n gamma d X h3 hn hgamma hsize q hq
  have hcount : count q X ≤ n := by
    have hbound := (q.1 X).isLt
    unfold count
    omega
  have haggregate : HasAggregateGap q X d := by
    unfold HasAggregateGap
    exact Nat.le_of_lt hq.1
  have hbinaryGap : n + d ≤ 2 * count q X :=
    aggregateGap_to_binaryGap haggregate
  have hinitial : Tri.AssemblyInitial n gamma (count q X) := by
    refine ⟨hcount, d, hbinaryGap, ?_⟩
    simpa [Nat.mul_assoc] using hq.2
  exact
    (multiStep_consensus_failure_le_triChain
      q X h3 (C * gamma * n * Nat.log 2 n)).trans
      (htri n gamma hn hgamma hsize (count q X) hinitial)

end Tri.Multi

#print axioms Tri.Multi.theorem1b_multi_aggregate_reaches_consensus
