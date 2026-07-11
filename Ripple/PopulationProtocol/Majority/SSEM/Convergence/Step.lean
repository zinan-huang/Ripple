/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Step / Execution preserves `IsConsensusConfig`

Lifting the pair-level invariants to the configuration level:

  * `step_preserves_consensus`: `Config.step` preserves `IsConsensusConfig`.
  * `execution_preserves_consensus`: by induction on `t`.
  * `consensus_isOutputStable`: outputs unchanged through any execution.
-/

import Ripple.PopulationProtocol.Majority.SSEM.Convergence.AnswerPreservation
import Ripple.PopulationProtocol.Majority.SSEM.Convergence.StatePreservation

namespace SSEM

variable {n : ℕ}

/-- Step preserves the input field. -/
theorem step_input_preserved {Q X Y : Type*}
    (P : Protocol Q X Y) (C : Config Q X n) (u v w : Fin n) :
    ((C.step P u v) w).2 = (C w).2 := by
  unfold Config.step
  by_cases huv : u = v
  · simp [huv]
  · simp only [if_neg huv]
    by_cases hwu : w = u
    · subst hwu; simp
    · by_cases hwv : w = v
      · subst hwv; simp [hwu]
      · simp [hwu, hwv]

/-- Project: `.role` of the new state at agent `w`. -/
private theorem step_role_eq {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (C : Config (AgentState n) Opinion n) (u v w : Fin n)
    (h1 : (transitionPEM n trank Rmax rankDelta (C u, C v)).1.role = (C u).1.role)
    (h2 : (transitionPEM n trank Rmax rankDelta (C u, C v)).2.role = (C v).1.role) :
    ((C.step (protocolPEM n trank Rmax rankDelta) u v) w).1.role = (C w).1.role := by
  unfold Config.step
  by_cases huv : u = v
  · simp [huv]
  · simp only [if_neg huv]
    by_cases hwu : w = u
    · subst hwu; simp [protocolPEM]; exact h1
    · by_cases hwv : w = v
      · subst hwv; simp [hwu, protocolPEM]; exact h2
      · simp [hwu, hwv]

private theorem step_rank_eq {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (C : Config (AgentState n) Opinion n) (u v w : Fin n)
    (h1 : (transitionPEM n trank Rmax rankDelta (C u, C v)).1.rank = (C u).1.rank)
    (h2 : (transitionPEM n trank Rmax rankDelta (C u, C v)).2.rank = (C v).1.rank) :
    ((C.step (protocolPEM n trank Rmax rankDelta) u v) w).1.rank = (C w).1.rank := by
  unfold Config.step
  by_cases huv : u = v
  · simp [huv]
  · simp only [if_neg huv]
    by_cases hwu : w = u
    · subst hwu; simp [protocolPEM]; exact h1
    · by_cases hwv : w = v
      · subst hwv; simp [hwu, protocolPEM]; exact h2
      · simp [hwu, hwv]

private theorem step_answer_eq {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (C : Config (AgentState n) Opinion n) (u v w : Fin n)
    (h1 : (transitionPEM n trank Rmax rankDelta (C u, C v)).1.answer = (C u).1.answer)
    (h2 : (transitionPEM n trank Rmax rankDelta (C u, C v)).2.answer = (C v).1.answer) :
    ((C.step (protocolPEM n trank Rmax rankDelta) u v) w).1.answer = (C w).1.answer := by
  unfold Config.step
  by_cases huv : u = v
  · simp [huv]
  · simp only [if_neg huv]
    by_cases hwu : w = u
    · subst hwu; simp [protocolPEM]; exact h1
    · by_cases hwv : w = v
      · subst hwv; simp [hwu, protocolPEM]; exact h2
      · simp [hwu, hwv]

/-- The set `agentsWithInput x` is invariant under `Config.step`. -/
theorem agentsWithInput_step_eq [DecidableEq X] {Q Y : Type*}
    (P : Protocol Q X Y) (C : Config Q X n) (u v : Fin n) (x : X) :
    (C.step P u v).agentsWithInput x = C.agentsWithInput x := by
  unfold Config.agentsWithInput
  ext w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [show (C.step P u v).inputOf w = C.inputOf w from step_input_preserved P C u v w]

/-- `nAOf` is invariant under `Config.step`. -/
theorem nAOf_step_eq {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (C : Config (AgentState n) Opinion n) (u v : Fin n) :
    nAOf (C.step (protocolPEM n trank Rmax rankDelta) u v) = nAOf C := by
  unfold nAOf
  exact congrArg Finset.card (agentsWithInput_step_eq _ C u v Opinion.A)

theorem nBOf_step_eq {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (C : Config (AgentState n) Opinion n) (u v : Fin n) :
    nBOf (C.step (protocolPEM n trank Rmax rankDelta) u v) = nBOf C := by
  unfold nBOf
  exact congrArg Finset.card (agentsWithInput_step_eq _ C u v Opinion.B)

/-- `nAOf` is invariant along an `execution` (inputs are immutable). -/
theorem nAOf_execution_eq {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (C : Config (AgentState n) Opinion n) (γ : DetScheduler n) (t : ℕ) :
    nAOf (execution (protocolPEM n trank Rmax rankDelta) C γ t) = nAOf C := by
  induction t with
  | zero => rfl
  | succ t ih =>
    show nAOf ((execution (protocolPEM n trank Rmax rankDelta) C γ t).step
        (protocolPEM n trank Rmax rankDelta) (γ t).1 (γ t).2) = _
    rw [nAOf_step_eq]; exact ih

/-- `nBOf` is invariant along an `execution` (inputs are immutable). -/
theorem nBOf_execution_eq {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (C : Config (AgentState n) Opinion n) (γ : DetScheduler n) (t : ℕ) :
    nBOf (execution (protocolPEM n trank Rmax rankDelta) C γ t) = nBOf C := by
  induction t with
  | zero => rfl
  | succ t ih =>
    show nBOf ((execution (protocolPEM n trank Rmax rankDelta) C γ t).step
        (protocolPEM n trank Rmax rankDelta) (γ t).1 (γ t).2) = _
    rw [nBOf_step_eq]; exact ih

/-- `majorityAnswer` is invariant under `Config.step`. -/
theorem majorityAnswer_step_eq {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (C : Config (AgentState n) Opinion n) (u v : Fin n) :
    majorityAnswer (C.step (protocolPEM n trank Rmax rankDelta) u v) = majorityAnswer C := by
  unfold majorityAnswer
  rw [nAOf_step_eq, nBOf_step_eq]

/-- `Config.step` preserves `IsConsensusConfig`. -/
theorem step_preserves_consensus {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n} (hC : IsConsensusConfig C) (u v : Fin n) :
    IsConsensusConfig (C.step (protocolPEM n trank Rmax rankDelta) u v) := by
  by_cases huv : u = v
  · subst huv; simp only [Config.step, if_pos rfl]; exact hC
  · -- u ≠ v → ranks differ (from InSrank bijection)
    have hne : (C u).1.rank ≠ (C v).1.rank :=
      fun h => huv (hC.ranks_inj h)
    set C' := C.step (protocolPEM n trank Rmax rankDelta) u v
    have hpair := consensus_pair_of_config hC u v
    have hAns := transitionPEM_consensus_pair_answer (trank := trank) (Rmax := Rmax) hRank hpair hne
    have hRR := transitionPEM_consensus_pair_role_rank
      (trank := trank) (Rmax := Rmax) hRank hpair hne
    -- Per-agent field equalities.
    have role_at (w : Fin n) : (C' w).1.role = (C w).1.role :=
      step_role_eq C u v w hRR.1 hRR.2.1
    have rank_at (w : Fin n) : (C' w).1.rank = (C w).1.rank :=
      step_rank_eq C u v w hRR.2.2.1 hRR.2.2.2
    have answer_at (w : Fin n) : (C' w).1.answer = (C w).1.answer :=
      step_answer_eq C u v w hAns.1 hAns.2
    have input_at (w : Fin n) : (C' w).2 = (C w).2 := step_input_preserved _ C u v w
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro w; rw [role_at w]; exact hC.allSettled w
    · intro w₁ w₂ hw
      apply hC.ranks_inj
      show (C w₁).1.rank = (C w₂).1.rank
      have h1 := rank_at w₁
      have h2 := rank_at w₂
      -- hw : (fun v => (C' v).1.rank) w₁ = (fun v => (C' v).1.rank) w₂
      -- which beta-reduces to (C' w₁).1.rank = (C' w₂).1.rank.
      have hw' : (C' w₁).1.rank = (C' w₂).1.rank := hw
      exact h1.symm.trans (hw'.trans h2)
    · intro w
      rw [input_at w, rank_at w, show nAOf C' = nAOf C from nAOf_step_eq C u v]
      exact hC.input_rank w
    · intro w
      rw [answer_at w, majorityAnswer_step_eq]
      exact hC.allAnswerCorrect w

/-- `execution` preserves `IsConsensusConfig` for any number of steps. -/
theorem execution_preserves_consensus {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n} (hC : IsConsensusConfig C)
    (γ : DetScheduler n) (t : ℕ) :
    IsConsensusConfig (execution (protocolPEM n trank Rmax rankDelta) C γ t) := by
  induction t with
  | zero => exact hC
  | succ t ih =>
    show IsConsensusConfig ((execution (protocolPEM n trank Rmax rankDelta) C γ t).step
      (protocolPEM n trank Rmax rankDelta) (γ t).1 (γ t).2)
    exact step_preserves_consensus hRank ih (γ t).1 (γ t).2

/-- `majorityAnswer` is invariant under `execution`. -/
theorem majorityAnswer_execution_eq {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (C : Config (AgentState n) Opinion n) (γ : DetScheduler n) (t : ℕ) :
    majorityAnswer (execution (protocolPEM n trank Rmax rankDelta) C γ t) = majorityAnswer C := by
  induction t with
  | zero => rfl
  | succ t ih =>
    show majorityAnswer ((execution (protocolPEM n trank Rmax rankDelta) C γ t).step
        (protocolPEM n trank Rmax rankDelta) (γ t).1 (γ t).2) = _
    rw [majorityAnswer_step_eq]; exact ih

/-- A consensus configuration is output-stable: outputs never change. -/
theorem IsConsensusConfig.isOutputStable {trank Rmax : ℕ}
    {rankDelta : AgentState n × AgentState n → AgentState n × AgentState n}
    (hRank : RankDeltaSettledFix rankDelta)
    {C : Config (AgentState n) Opinion n} (hC : IsConsensusConfig C) :
    C.isOutputStable (protocolPEM n trank Rmax rankDelta) := by
  intro γ t w
  have hC_t := execution_preserves_consensus (trank := trank) (Rmax := Rmax) hRank hC γ t
  have hAll := hC.allOutput (trank := trank) (Rmax := Rmax) (rankDelta := rankDelta)
  have hAll_t := hC_t.allOutput (trank := trank) (Rmax := Rmax) (rankDelta := rankDelta)
  rw [hAll w, hAll_t w, majorityAnswer_execution_eq]

end SSEM
