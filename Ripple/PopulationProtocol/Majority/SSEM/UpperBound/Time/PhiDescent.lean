import Ripple.PopulationProtocol.Majority.SSEM.Convergence.BurmanConvergenceFinal
import Mathlib.Tactic

namespace SSEM

/-!
This file starts with the requested all-step `phiCount` monotonicity check.
For the natural reservoir region used by the qualitative cycle,
`InSswap C ∧ ResAns (majorityAnswer C) C`, the statement is false.

The counterexample below is a four-agent `InSswap` configuration.  The
lower-median agent still has answer `.phi` and timer `1`; it interacts with
the max-rank agent.  Since this is not the even median pair, Phase 4 decision
does not resolve the lower median.  Phase 4 propagation decrements the timer
to `0`, sees `.phi ≠ .outA`, and copies `.phi` to the max-rank agent while
resetting both.  Thus `phiCount` increases from `1` to `2`.
-/

private def phiCexState (v : Fin 4) : AgentState 4 where
  role := .Settled
  rank := v
  leader := .F
  resetcount := 0
  answer := if v.val = 1 then .phi else .outA
  timer := if v.val = 1 then 1 else 0
  children := 0
  errorcount := 0
  delaytimer := 0

private def phiCex : Config (AgentState 4) Opinion 4 :=
  fun v => (phiCexState v, .A)

private def phiCexP : Protocol (AgentState 4) Opinion Output :=
  protocolPEM 4 1 1 (rankDeltaOSSR 1 1 1 (by norm_num : 0 < 4))

private def loMed4 : Fin 4 := ⟨1, by norm_num⟩
private def max4 : Fin 4 := ⟨3, by norm_num⟩

private lemma phiCex_nA : nAOf phiCex = 4 := by
  decide

private lemma phiCex_nB : nBOf phiCex = 0 := by
  decide

private lemma phiCex_majority : majorityAnswer phiCex = .outA := by
  unfold majorityAnswer
  rw [phiCex_nA, phiCex_nB]
  norm_num

private lemma phiCex_inSswap : InSswap phiCex := by
  refine
    { toInSrank :=
        { allSettled := ?_
          ranks_inj := ?_ }
      input_rank := ?_ }
  · intro v
    rfl
  · intro v w h
    exact Fin.ext (by simpa [phiCex, phiCexState] using congrArg Fin.val h)
  · intro v
    rw [phiCex_nA]
    simp [phiCex, phiCexState]

private lemma phiCex_resAns : ResAns (majorityAnswer phiCex) phiCex := by
  rw [phiCex_majority]
  intro w
  by_cases hw : w.val = 1
  · right
    simp [phiCex, phiCexState, hw]
  · left
    simp [phiCex, phiCexState, hw]

private lemma phiCex_phiCount : phiCount phiCex = 1 := by
  decide

private lemma phiCex_step_phiCount :
    phiCount (phiCex.step phiCexP loMed4 max4) = 2 := by
  decide

theorem phiCount_not_nonincreasing_on_InSswap_ResAns :
    ¬ (∀ C : Config (AgentState 4) Opinion 4,
        InSswap C ∧ ResAns (majorityAnswer C) C →
          ∀ i j : Fin 4, phiCount (C.step phiCexP i j) ≤ phiCount C) := by
  intro h
  have hle := h phiCex ⟨phiCex_inSswap, phiCex_resAns⟩ loMed4 max4
  rw [phiCex_step_phiCount, phiCex_phiCount] at hle
  omega

theorem phiCount_increases_on_phiCex_step :
    phiCount phiCex < phiCount (phiCex.step phiCexP loMed4 max4) := by
  rw [phiCex_phiCount, phiCex_step_phiCount]
  norm_num

end SSEM
