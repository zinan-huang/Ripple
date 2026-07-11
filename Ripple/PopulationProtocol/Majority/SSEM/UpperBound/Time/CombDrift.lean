import Ripple.PopulationProtocol.Majority.SSEM.Convergence.BurmanConvergenceFinal
import Ripple.PopulationProtocol.Majority.SSEM.Probability.RandomScheduler
import Mathlib.Tactic

namespace SSEM

open scoped BigOperators

/-!
Combined-potential drift obstruction.

The natural reservoir region `InSswap C ∧ ResAns (majorityAnswer C) C` is
still too weak for the requested ordered-pair net drift, even after adding
the timer sum and a settled-incompleteness term to `phiCount`.

The obstruction is a median-`.phi` configuration: the median has timer `0`,
so its `.phi` answer propagates to non-median agents in more ordered pairs
than the median-pair decision can repair it.
-/

def timerSum {n : ℕ} (C : Config (AgentState n) Opinion n) : ℕ :=
  Finset.univ.sum fun w : Fin n => (C w).1.timer

def combPotential {n : ℕ} (W2 W1 : ℕ)
    (C : Config (AgentState n) Opinion n) : ℕ :=
  W2 * phiCount C + W1 * (n - settledCount C) + timerSum C

private def combDriftCexState (v : Fin 4) : AgentState 4 where
  role := .Settled
  rank := v
  leader := .F
  resetcount := 0
  answer := if v.val = 1 then .phi else .outA
  timer := 0
  children := 0
  errorcount := 0
  delaytimer := 0

private def combDriftCex : Config (AgentState 4) Opinion 4 :=
  fun v => (combDriftCexState v, .A)

private def combDriftCexP : Protocol (AgentState 4) Opinion Output :=
  protocolPEM 4 1 1 (rankDeltaOSSR 1 1 1 (by norm_num : 0 < 4))

private def lowerMedian4 : Fin 4 := ⟨1, by norm_num⟩
private def c0 : Fin 4 := ⟨0, by norm_num⟩
private def c1 : Fin 4 := ⟨1, by norm_num⟩
private def c2 : Fin 4 := ⟨2, by norm_num⟩
private def c3 : Fin 4 := ⟨3, by norm_num⟩

private def risePairs4 : Finset (Fin 4 × Fin 4) :=
  {(c0, c1), (c1, c0), (c1, c3), (c3, c1)}

private def dropPairs4 : Finset (Fin 4 × Fin 4) :=
  {(c1, c2), (c2, c1)}

private def flatPairs4 : Finset (Fin 4 × Fin 4) :=
  {(c0, c2), (c0, c3), (c2, c0), (c2, c3), (c3, c0), (c3, c2)}

private lemma combDriftCex_nA : nAOf combDriftCex = 4 := by
  decide

private lemma combDriftCex_nB : nBOf combDriftCex = 0 := by
  decide

private lemma combDriftCex_majority : majorityAnswer combDriftCex = .outA := by
  unfold majorityAnswer
  rw [combDriftCex_nA, combDriftCex_nB]
  norm_num

private lemma combDriftCex_inSswap : InSswap combDriftCex := by
  refine
    { toInSrank :=
        { allSettled := ?_
          ranks_inj := ?_ }
      input_rank := ?_ }
  · intro v
    rfl
  · intro v w h
    exact Fin.ext (by simpa [combDriftCex, combDriftCexState] using congrArg Fin.val h)
  · intro v
    rw [combDriftCex_nA]
    simp [combDriftCex, combDriftCexState]

private lemma combDriftCex_resAns :
    ResAns (majorityAnswer combDriftCex) combDriftCex := by
  rw [combDriftCex_majority]
  intro w
  by_cases hw : w.val = 1
  · right
    simp [combDriftCex, combDriftCexState, hw]
  · left
    simp [combDriftCex, combDriftCexState, hw]

private lemma combDriftCex_phiCount : phiCount combDriftCex = 1 := by
  decide

private lemma combDriftCex_not_consensus : ¬ IsConsensusConfig combDriftCex := by
  intro h
  have hAns := h.allAnswerCorrect lowerMedian4
  rw [combDriftCex_majority] at hAns
  norm_num [combDriftCex, combDriftCexState, lowerMedian4] at hAns
  cases hAns

private lemma combDriftCex_median_phi :
    (combDriftCex lowerMedian4).1.answer = .phi := by
  rfl

private lemma combDriftCex_median_rank :
    (combDriftCex lowerMedian4).1.rank.val + 1 = ceilHalf 4 := by
  norm_num [combDriftCex, combDriftCexState, lowerMedian4, ceilHalf]

private lemma combDriftCex_combPotential (W2 W1 : ℕ) :
    combPotential W2 W1 combDriftCex = W2 := by
  have hphi : phiCount combDriftCex = 1 := by decide
  have hsettled : settledCount combDriftCex = 4 := by decide
  have htimer : timerSum combDriftCex = 0 := by decide
  unfold combPotential
  rw [hphi, hsettled, htimer]
  norm_num

private lemma combDriftCex_step01_phiCount :
    phiCount (combDriftCex.step combDriftCexP c0 c1) = 2 := by
  decide

private lemma combDriftCex_step01_settledCount :
    settledCount (combDriftCex.step combDriftCexP c0 c1) = 2 := by
  decide

private lemma combDriftCex_step01_timerSum :
    timerSum (combDriftCex.step combDriftCexP c0 c1) = 0 := by
  decide

private lemma combDriftCex_stepPot_rise
    (W2 W1 : ℕ) {i j : Fin 4}
    (hphi : phiCount (combDriftCex.step combDriftCexP i j) = 2)
    (hsettled : settledCount (combDriftCex.step combDriftCexP i j) = 2)
    (htimer : timerSum (combDriftCex.step combDriftCexP i j) = 0) :
    combPotential W2 W1 (combDriftCex.step combDriftCexP i j) =
      2 * W2 + 2 * W1 := by
  unfold combPotential
  rw [hphi, hsettled, htimer]
  omega

private lemma combDriftCex_stepPot_drop
    (W2 W1 : ℕ) {i j : Fin 4}
    (hphi : phiCount (combDriftCex.step combDriftCexP i j) = 0)
    (hsettled : settledCount (combDriftCex.step combDriftCexP i j) = 4)
    (htimer : timerSum (combDriftCex.step combDriftCexP i j) = 0) :
    combPotential W2 W1 (combDriftCex.step combDriftCexP i j) = 0 := by
  unfold combPotential
  rw [hphi, hsettled, htimer]
  norm_num

private lemma combDriftCex_stepPot_flat
    (W2 W1 : ℕ) {i j : Fin 4}
    (hphi : phiCount (combDriftCex.step combDriftCexP i j) = 1)
    (hsettled : settledCount (combDriftCex.step combDriftCexP i j) = 4)
    (htimer : timerSum (combDriftCex.step combDriftCexP i j) = 0) :
    combPotential W2 W1 (combDriftCex.step combDriftCexP i j) = W2 := by
  unfold combPotential
  rw [hphi, hsettled, htimer]
  norm_num

private lemma combDriftCex_stepPot_01 (W2 W1 : ℕ) :
    combPotential W2 W1 (combDriftCex.step combDriftCexP c0 c1) =
      2 * W2 + 2 * W1 :=
  combDriftCex_stepPot_rise W2 W1
    (by decide) (by decide) (by decide)

private lemma combDriftCex_stepPot_10 (W2 W1 : ℕ) :
    combPotential W2 W1 (combDriftCex.step combDriftCexP c1 c0) =
      2 * W2 + 2 * W1 :=
  combDriftCex_stepPot_rise W2 W1
    (by decide) (by decide) (by decide)

private lemma combDriftCex_stepPot_13 (W2 W1 : ℕ) :
    combPotential W2 W1 (combDriftCex.step combDriftCexP c1 c3) =
      2 * W2 + 2 * W1 :=
  combDriftCex_stepPot_rise W2 W1
    (by decide) (by decide) (by decide)

private lemma combDriftCex_stepPot_31 (W2 W1 : ℕ) :
    combPotential W2 W1 (combDriftCex.step combDriftCexP c3 c1) =
      2 * W2 + 2 * W1 :=
  combDriftCex_stepPot_rise W2 W1
    (by decide) (by decide) (by decide)

private lemma combDriftCex_stepPot_12 (W2 W1 : ℕ) :
    combPotential W2 W1 (combDriftCex.step combDriftCexP c1 c2) = 0 :=
  combDriftCex_stepPot_drop W2 W1
    (by decide) (by decide) (by decide)

private lemma combDriftCex_stepPot_21 (W2 W1 : ℕ) :
    combPotential W2 W1 (combDriftCex.step combDriftCexP c2 c1) = 0 :=
  combDriftCex_stepPot_drop W2 W1
    (by decide) (by decide) (by decide)

private lemma combDriftCex_stepPot_02 (W2 W1 : ℕ) :
    combPotential W2 W1 (combDriftCex.step combDriftCexP c0 c2) = W2 :=
  combDriftCex_stepPot_flat W2 W1
    (by decide) (by decide) (by decide)

private lemma combDriftCex_stepPot_03 (W2 W1 : ℕ) :
    combPotential W2 W1 (combDriftCex.step combDriftCexP c0 c3) = W2 :=
  combDriftCex_stepPot_flat W2 W1
    (by decide) (by decide) (by decide)

private lemma combDriftCex_stepPot_20 (W2 W1 : ℕ) :
    combPotential W2 W1 (combDriftCex.step combDriftCexP c2 c0) = W2 :=
  combDriftCex_stepPot_flat W2 W1
    (by decide) (by decide) (by decide)

private lemma combDriftCex_stepPot_23 (W2 W1 : ℕ) :
    combPotential W2 W1 (combDriftCex.step combDriftCexP c2 c3) = W2 :=
  combDriftCex_stepPot_flat W2 W1
    (by decide) (by decide) (by decide)

private lemma combDriftCex_stepPot_30 (W2 W1 : ℕ) :
    combPotential W2 W1 (combDriftCex.step combDriftCexP c3 c0) = W2 :=
  combDriftCex_stepPot_flat W2 W1
    (by decide) (by decide) (by decide)

private lemma combDriftCex_stepPot_32 (W2 W1 : ℕ) :
    combPotential W2 W1 (combDriftCex.step combDriftCexP c3 c2) = W2 :=
  combDriftCex_stepPot_flat W2 W1
    (by decide) (by decide) (by decide)

private lemma offDiagonalPairs4_partition :
    Probability.OffDiagonalPairs 4 =
      risePairs4 ∪ (dropPairs4 ∪ flatPairs4) := by
  decide

private lemma risePairs4_disjoint_rest :
    Disjoint risePairs4 (dropPairs4 ∪ flatPairs4) := by
  decide

private lemma dropPairs4_disjoint_flat :
    Disjoint dropPairs4 flatPairs4 := by
  decide

private lemma risePairs4_card : risePairs4.card = 4 := by
  decide

private lemma dropPairs4_card : dropPairs4.card = 2 := by
  decide

private lemma flatPairs4_card : flatPairs4.card = 6 := by
  decide

private lemma mem_risePairs4 (p : Fin 4 × Fin 4) :
    p ∈ risePairs4 ↔
      p = (c0, c1) ∨ p = (c1, c0) ∨ p = (c1, c3) ∨ p = (c3, c1) := by
  simp [risePairs4]

private lemma mem_dropPairs4 (p : Fin 4 × Fin 4) :
    p ∈ dropPairs4 ↔ p = (c1, c2) ∨ p = (c2, c1) := by
  simp [dropPairs4]

private lemma mem_flatPairs4 (p : Fin 4 × Fin 4) :
    p ∈ flatPairs4 ↔
      p = (c0, c2) ∨ p = (c0, c3) ∨ p = (c2, c0) ∨
        p = (c2, c3) ∨ p = (c3, c0) ∨ p = (c3, c2) := by
  simp [flatPairs4]

private lemma combDriftCex_risePairs4_sum (W2 W1 : ℕ) :
    risePairs4.sum (fun p => combPotential W2 W1
      (combDriftCex.step combDriftCexP p.1 p.2)) =
      4 * (2 * W2 + 2 * W1) := by
  calc
    risePairs4.sum (fun p => combPotential W2 W1
        (combDriftCex.step combDriftCexP p.1 p.2))
        = risePairs4.sum (fun _p => 2 * W2 + 2 * W1) := by
          apply Finset.sum_congr rfl
          intro p hp
          rw [mem_risePairs4] at hp
          rcases hp with rfl | rfl | rfl | rfl
          · exact combDriftCex_stepPot_01 W2 W1
          · exact combDriftCex_stepPot_10 W2 W1
          · exact combDriftCex_stepPot_13 W2 W1
          · exact combDriftCex_stepPot_31 W2 W1
    _ = 4 * (2 * W2 + 2 * W1) := by
          rw [Finset.sum_const, risePairs4_card]
          simp

private lemma combDriftCex_dropPairs4_sum (W2 W1 : ℕ) :
    dropPairs4.sum (fun p => combPotential W2 W1
      (combDriftCex.step combDriftCexP p.1 p.2)) = 0 := by
  calc
    dropPairs4.sum (fun p => combPotential W2 W1
        (combDriftCex.step combDriftCexP p.1 p.2))
        = dropPairs4.sum (fun _p => 0) := by
          apply Finset.sum_congr rfl
          intro p hp
          rw [mem_dropPairs4] at hp
          rcases hp with rfl | rfl
          · exact combDriftCex_stepPot_12 W2 W1
          · exact combDriftCex_stepPot_21 W2 W1
    _ = 0 := by simp

private lemma combDriftCex_flatPairs4_sum (W2 W1 : ℕ) :
    flatPairs4.sum (fun p => combPotential W2 W1
      (combDriftCex.step combDriftCexP p.1 p.2)) = 6 * W2 := by
  calc
    flatPairs4.sum (fun p => combPotential W2 W1
        (combDriftCex.step combDriftCexP p.1 p.2))
        = flatPairs4.sum (fun _p => W2) := by
          apply Finset.sum_congr rfl
          intro p hp
          rw [mem_flatPairs4] at hp
          rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
          · exact combDriftCex_stepPot_02 W2 W1
          · exact combDriftCex_stepPot_03 W2 W1
          · exact combDriftCex_stepPot_20 W2 W1
          · exact combDriftCex_stepPot_23 W2 W1
          · exact combDriftCex_stepPot_30 W2 W1
          · exact combDriftCex_stepPot_32 W2 W1
    _ = 6 * W2 := by
          rw [Finset.sum_const, flatPairs4_card]
          simp

private lemma combDriftCex_orderedPostSum (W2 W1 : ℕ) :
    (Probability.OffDiagonalPairs 4).sum
        (fun p => combPotential W2 W1
          (combDriftCex.step combDriftCexP p.1 p.2)) =
      14 * W2 + 8 * W1 := by
  rw [offDiagonalPairs4_partition]
  rw [Finset.sum_union risePairs4_disjoint_rest]
  rw [Finset.sum_union dropPairs4_disjoint_flat]
  rw [combDriftCex_risePairs4_sum, combDriftCex_dropPairs4_sum,
    combDriftCex_flatPairs4_sum]
  omega

/--
The requested net-count inequality is false on the natural reservoir region
`InSswap C ∧ ResAns (majorityAnswer C) C`, even for the combined potential
`W2 * phiCount + W1 * (n - settledCount) + timerSum`.

For this four-agent configuration the base potential is `W2`, while the
ordered off-diagonal post-step sum is `14*W2 + 8*W1`; the desired
`postSum + 1 ≤ 12 * base` is therefore impossible for every choice of
weights.  The obstruction is exactly the median `.phi` value:
`combDriftCex_median_phi` and `combDriftCex_median_rank`.
-/
theorem combPotential_drift_target_false_on_InSswap_ResAns
    (W2 W1 : ℕ) :
    ∃ C : Config (AgentState 4) Opinion 4,
      InSswap C ∧
      ResAns (majorityAnswer C) C ∧
      0 < phiCount C ∧
      ¬ IsConsensusConfig C ∧
      (∃ μ : Fin 4, (C μ).1.rank.val + 1 = ceilHalf 4 ∧
        (C μ).1.answer = .phi) ∧
      ¬
        ((Probability.OffDiagonalPairs 4).sum
            (fun p => combPotential W2 W1 (C.step combDriftCexP p.1 p.2)) + 1 ≤
          (4 * (4 - 1)) * combPotential W2 W1 C) := by
  refine ⟨combDriftCex, combDriftCex_inSswap, combDriftCex_resAns, ?_, ?_, ?_, ?_⟩
  · rw [combDriftCex_phiCount]
    norm_num
  · exact combDriftCex_not_consensus
  · exact ⟨lowerMedian4, combDriftCex_median_rank, combDriftCex_median_phi⟩
  · rw [combDriftCex_orderedPostSum, combDriftCex_combPotential]
    omega

end SSEM
