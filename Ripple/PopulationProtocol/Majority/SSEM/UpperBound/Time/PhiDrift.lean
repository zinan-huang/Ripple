import Ripple.PopulationProtocol.Majority.SSEM.Convergence.BurmanConvergenceFinal
import Ripple.PopulationProtocol.Majority.SSEM.Probability.RandomScheduler
import Mathlib.Tactic

namespace SSEM

open scoped BigOperators

/-!
Per-step `phiCount` drift obstruction.

The reservoir region `InSswap C ∧ ResAns (majorityAnswer C) C` does not imply
negative one-step drift for `phiCount`.  The four-agent configuration below is
the same local obstruction as in `PhiDescent`, but here we aggregate over all
ordered off-diagonal scheduler pairs.
-/

private def phiDriftCexState (v : Fin 4) : AgentState 4 where
  role := .Settled
  rank := v
  leader := .F
  resetcount := 0
  answer := if v.val = 1 then .phi else .outA
  timer := if v.val = 1 then 1 else 0
  children := 0
  errorcount := 0
  delaytimer := 0

private def phiDriftCex : Config (AgentState 4) Opinion 4 :=
  fun v => (phiDriftCexState v, .A)

private def phiDriftCexP : Protocol (AgentState 4) Opinion Output :=
  protocolPEM 4 1 1 (rankDeltaOSSR 1 1 1 (by norm_num : 0 < 4))

private def phiDriftOrderedPostSum : ℕ :=
  (Probability.OffDiagonalPairs 4).sum
    (fun p => phiCount (phiDriftCex.step phiDriftCexP p.1 p.2))

private def phiDriftDropPairs : Finset (Fin 4 × Fin 4) :=
  (Probability.OffDiagonalPairs 4).filter
    (fun p => phiCount (phiDriftCex.step phiDriftCexP p.1 p.2) <
      phiCount phiDriftCex)

private def phiDriftRisePairs : Finset (Fin 4 × Fin 4) :=
  (Probability.OffDiagonalPairs 4).filter
    (fun p => phiCount phiDriftCex <
      phiCount (phiDriftCex.step phiDriftCexP p.1 p.2))

private def phiDriftFlatPairs : Finset (Fin 4 × Fin 4) :=
  (Probability.OffDiagonalPairs 4).filter
    (fun p => phiCount (phiDriftCex.step phiDriftCexP p.1 p.2) =
      phiCount phiDriftCex)

private lemma phiDriftCex_nA : nAOf phiDriftCex = 4 := by
  decide

private lemma phiDriftCex_nB : nBOf phiDriftCex = 0 := by
  decide

private lemma phiDriftCex_majority : majorityAnswer phiDriftCex = .outA := by
  unfold majorityAnswer
  rw [phiDriftCex_nA, phiDriftCex_nB]
  norm_num

private lemma phiDriftCex_inSswap : InSswap phiDriftCex := by
  refine
    { toInSrank :=
        { allSettled := ?_
          ranks_inj := ?_ }
      input_rank := ?_ }
  · intro v
    rfl
  · intro v w h
    exact Fin.ext (by simpa [phiDriftCex, phiDriftCexState] using congrArg Fin.val h)
  · intro v
    rw [phiDriftCex_nA]
    simp [phiDriftCex, phiDriftCexState]

private lemma phiDriftCex_resAns :
    ResAns (majorityAnswer phiDriftCex) phiDriftCex := by
  rw [phiDriftCex_majority]
  intro w
  by_cases hw : w.val = 1
  · right
    simp [phiDriftCex, phiDriftCexState, hw]
  · left
    simp [phiDriftCex, phiDriftCexState, hw]

private lemma phiDriftCex_phiCount : phiCount phiDriftCex = 1 := by
  decide

private lemma phiDriftOrderedPostSum_eq : phiDriftOrderedPostSum = 12 := by
  decide

private lemma phiDriftDropPairs_card : phiDriftDropPairs.card = 2 := by
  decide

private lemma phiDriftRisePairs_card : phiDriftRisePairs.card = 2 := by
  decide

private lemma phiDriftFlatPairs_card : phiDriftFlatPairs.card = 8 := by
  decide

private lemma phiDriftCex_not_consensus : ¬ IsConsensusConfig phiDriftCex := by
  intro h
  have hAns := h.allAnswerCorrect (⟨1, by norm_num⟩ : Fin 4)
  rw [phiDriftCex_majority] at hAns
  norm_num [phiDriftCex, phiDriftCexState] at hAns
  cases hAns

/--
Exact obstruction to the proposed drift `≤ -1/(n(n-1))`.

Multiplying the desired inequality
`E[phiCount next] + 1/(n(n-1)) ≤ phiCount C` by `n(n-1)` gives
`ordered_post_sum + 1 ≤ n(n-1) * phiCount C`.  In this reservoir
configuration the right hand side is `12`, while the post-step ordered sum is
already `12`, so the desired strict one-pair surplus is false.
-/
theorem phiCount_drift_target_false_on_InSswap_ResAns :
    ∃ C : Config (AgentState 4) Opinion 4,
      InSswap C ∧
      ResAns (majorityAnswer C) C ∧
      0 < phiCount C ∧
      ¬ IsConsensusConfig C ∧
      ¬
        ((Probability.OffDiagonalPairs 4).sum
            (fun p => phiCount (C.step phiDriftCexP p.1 p.2)) + 1 ≤
          (4 * (4 - 1)) * phiCount C) := by
  refine ⟨phiDriftCex, phiDriftCex_inSswap, phiDriftCex_resAns, ?_, ?_, ?_⟩
  · rw [phiDriftCex_phiCount]
    norm_num
  · exact phiDriftCex_not_consensus
  · rw [show (Probability.OffDiagonalPairs 4).sum
          (fun p => phiCount (phiDriftCex.step phiDriftCexP p.1 p.2)) =
        phiDriftOrderedPostSum by rfl]
    rw [phiDriftOrderedPostSum_eq, phiDriftCex_phiCount]
    norm_num

end SSEM
