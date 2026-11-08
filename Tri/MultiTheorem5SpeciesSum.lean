/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.MultiProductivePhase0Ladder
import Tri.MultiTheorem1bHandoff
import Tri.HitThenReaches

/-!
# Multi-species plurality consensus

The raw phase-0 ladder first reaches either `X`-consensus or an aggregate
majority checkpoint.  In the latter branch, the binary finite-horizon envelope
and the proved ordinary-Tri Theorem 1(b) finish the computation.  The resulting
error retains the exact finite phase-0 sum; no unjustified absorption of its
species prefactor is used.
-/

namespace Tri.Multi

open scoped ENNReal

variable {m n : ℕ}

/-- The exact finite-horizon multi-species consensus theorem obtained from the
raw phase-0 ladder and the ordinary-Tri aggregate handoff. -/
theorem theorem5_multi_reaches_consensus :
    ∃ C n₀ : ℕ, ∃ c : ℝ,
      0 < C ∧ 0 < c ∧ 3 ≤ n₀ ∧
      ∀ m n gamma d : ℕ, ∀ X : Species m, ∀ h3 : 3 ≤ n,
        n₀ ≤ n →
        1 ≤ gamma →
        4 ≤ d →
        d ≤ n →
        3 * d ≤ n →
        6 ≤ gamma * Nat.log 2 n →
        6 * gamma * Nat.log 2 n ≤ n →
        m * (gamma * Nat.log 2 n) ≤ n →
        gamma * n * Nat.log 2 n ≤ d ^ 2 →
        Reaches
          (fun q : Config m n => multiStep q h3)
          (((Nat.log 2 n + 1) * phase0LadderStageHorizon m n) +
            C * gamma * n * Nat.log 2 n)
          (fun q => HasPairwiseGap q X d)
          (fun q => ConsensusOn q X)
          ((∑ j ∈ Finset.range (Nat.log 2 n + 1),
              phase0LadderStageError m n gamma
                (phase0LadderScale d n j)) +
            (n : ℝ≥0∞)⁻¹ ^ (c * (gamma : ℝ))) := by
  rcases theorem1b_multi_aggregate_reaches_consensus with
    ⟨C, n₀, c, hC, hc, hn₀, haggregate⟩
  refine ⟨C, n₀, c, hC, hc, hn₀, ?_⟩
  intro m n gamma d X h3 hn hgamma hd4 hdn hclockd
    hscale hsize hm hgapSq
  let K : Config m n → PMF (Config m n) :=
    fun q => multiStep q h3
  let T₁ : ℕ :=
    (Nat.log 2 n + 1) * phase0LadderStageHorizon m n
  let T₂ : ℕ :=
    C * gamma * n * Nat.log 2 n
  let ε₁ : ℝ≥0∞ :=
    ∑ j ∈ Finset.range (Nat.log 2 n + 1),
      phase0LadderStageError m n gamma
        (phase0LadderScale d n j)
  let ε₂ : ℝ≥0∞ :=
    (n : ℝ≥0∞)⁻¹ ^ (c * (gamma : ℝ))
  have hmPos : 0 < m := by
    have := X.isLt
    omega
  have hT₁ : 0 < T₁ := by
    dsimp only [T₁, phase0LadderStageHorizon]
    positivity
  have hT₂ : 0 < T₂ := by
    dsimp only [T₂]
    have hgammaPos : 0 < gamma := by omega
    have hnPos : 0 < n := by omega
    have hlogPos : 0 < Nat.log 2 n := by
      by_contra hzero
      have hlogZero : Nat.log 2 n = 0 :=
        Nat.eq_zero_of_not_pos hzero
      simp [hlogZero] at hscale
    positivity
  have hhit :
      ∀ q, HasPairwiseGap q X d →
        terminalFailureMass
          (iter (freeze (Phase0LadderExit X d) K) T₁ q)
          (Phase0LadderExit X d) ≤ ε₁ := by
    intro q hq
    simpa only [K, T₁, ε₁] using
      phase0Ladder_raw_exit
        h3 X d gamma hgamma hd4 hdn hclockd
        hscale hm q hq
  have hpost :
      Reaches K T₂
        (Phase0LadderExit X d)
        (fun q => ConsensusOn q X) ε₂ := by
    intro q hq
    rcases hq with hcons | hhandoff
    · have habs : K q = PMF.pure q := by
        exact multiStep_consensus q X hcons h3
      have hiter : iter K T₂ q = PMF.pure q := by
        induction T₂ with
        | zero => rfl
        | succ T ih =>
            rw [iter_succ, habs, PMF.pure_bind, ih]
      rw [hiter]
      change terminalFailureMass (PMF.pure q)
        (fun z => ConsensusOn z X) ≤ ε₂
      rw [terminalFailureMass_pure]
      simp [hcons]
    · exact
        haggregate m n gamma d X h3 hn hgamma
          hsize
          q ⟨hhandoff, hgapSq⟩
  have habs :
      ∀ q, ConsensusOn q X → K q = PMF.pure q := by
    intro q hq
    exact multiStep_consensus q X hq h3
  simpa only [K, T₁, T₂, ε₁, ε₂] using
    Reaches.comp_of_frozen_hit
      K hT₁ hT₂ hhit hpost habs

end Tri.Multi

#print axioms Tri.Multi.theorem5_multi_reaches_consensus
