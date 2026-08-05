/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.MultiProductivePhase0Ladder
import Tri.MultiProductivePhase0Unconditional

/-!
# The unconditional raw phase-0 ladder

This is the dyadic phase-0 ladder with the state-dependent proper-stage error.
Its finite error sum is independent of the number of species.
-/

namespace Tri.Multi

open scoped BigOperators ENNReal

variable {m n : ℕ}

/-! ## One dyadic rung -/

/-- Uniform error of one raw phase-0 ladder rung. -/
noncomputable def phase0LadderUnconditionalStageError
    (g : ℕ) : ℝ≥0∞ :=
  (144 : ℝ≥0∞) * productiveAmplificationHeadlineError g +
    ENNReal.ofReal (Real.exp (-(g : ℝ)))

/-- One unconditional raw rung advances the dyadic ladder. -/
theorem phase0Ladder_oneStage_unconditional
    (h3 : 3 ≤ n) (X : Species m) (d g j : ℕ)
    (hgLarge : properStageHeadlineThreshold ≤ g)
    (hg6 : 6 ≤ g)
    (hd4 : 4 ≤ d) (hdn : d ≤ n)
    (hclockd : 3 * d ≤ n)
    (hm : m * g ≤ n)
    (hgapSq : g * n ≤ d ^ 2)
    (c0 : Config m n)
    (hinit : Phase0LadderGood X d n j c0) :
    terminalFailureMass
        (StagedFreezeControl.block
          (fun c => multiStep c h3)
          (phase0LadderCheckpoint X d n)
          (fun _ => phase0LadderStageHorizon m n)
          j c0)
        (Phase0LadderGood X d n (j + 1)) ≤
      phase0LadderUnconditionalStageError g := by
  let D := phase0LadderScale d n j
  have hdD : d ≤ D :=
    phase0LadderScale_ge d n hdn j
  have hDn : D ≤ n :=
    phase0LadderScale_le d n hdn j
  rcases hinit with hgap | hhandoff
  · have hstage :=
      phase0StageAt_raw_failure_headline_paper
        h3 X g d D hgLarge hg6 hd4 hdD hDn hclockd
        hm hgapSq c0 hgap
    have hmono :
        terminalFailureMass
            (iter
              (freeze (Phase0StageSuccessAt X d D)
                (fun c => multiStep c h3))
              (phase0LadderStageHorizon m n) c0)
            (Phase0LadderGood X d n (j + 1)) ≤
          terminalFailureMass
            (iter
              (freeze (Phase0StageSuccessAt X d D)
                (fun c => multiStep c h3))
              (phase0LadderStageHorizon m n) c0)
            (Phase0StageSuccessAt X d D) :=
      terminalFailureMass_mono _ _ _
        (phase0LadderCheckpoint_to_next X d n j)
    exact hmono.trans (by
      simpa [D, phase0LadderStageHorizon,
        phase0LadderUnconditionalStageError] using hstage)
  · have hcheckpoint :
        Phase0StageSuccessAt X d D c0 :=
      Or.inr hhandoff
    rw [StagedFreezeControl.block]
    change terminalFailureMass
      (iter
        (freeze (Phase0StageSuccessAt X d D)
          (fun c => multiStep c h3))
        (phase0LadderStageHorizon m n) c0)
      (Phase0LadderGood X d n (j + 1)) ≤ _
    rw [iter_freeze_of_mem c0 hcheckpoint]
    rw [terminalFailureMass_pure]
    simp [Phase0LadderGood, hhandoff]

/-! ## Composition of heterogeneous rungs

Each checkpoint quadruples the protected gap, capped at the population size.
The staged kernel freezes completed checkpoints, so a direct union bound
composes the rung estimates even though the checkpoint predicate changes.
-/

/-- The heterogeneous unconditional raw blocks compose by a union bound. -/
theorem phase0Ladder_staged_failure_unconditional
    (h3 : 3 ≤ n) (X : Species m) (d g k : ℕ)
    (hgLarge : properStageHeadlineThreshold ≤ g)
    (hg6 : 6 ≤ g)
    (hd4 : 4 ≤ d) (hdn : d ≤ n)
    (hclockd : 3 * d ≤ n)
    (hm : m * g ≤ n)
    (hgapSq : g * n ≤ d ^ 2)
    (c0 : Config m n) (hinit : HasPairwiseGap c0 X d) :
    terminalFailureMass
        (stagedIter
          (StagedFreezeControl.block
            (fun c => multiStep c h3)
            (phase0LadderCheckpoint X d n)
            (fun _ => phase0LadderStageHorizon m n))
          k c0)
        (Phase0LadderGood X d n k) ≤
      (k : ℝ≥0∞) * phase0LadderUnconditionalStageError g := by
  have hsum :=
    terminalFailureMass_stagedIter
      (K := StagedFreezeControl.block
        (fun c => multiStep c h3)
        (phase0LadderCheckpoint X d n)
        (fun _ => phase0LadderStageHorizon m n))
      (P := fun j => Phase0LadderGood X d n j)
      (ε := fun _ => phase0LadderUnconditionalStageError g)
      (m := k) (s := c0)
      (fun j _ c hc =>
        phase0Ladder_oneStage_unconditional
          h3 X d g j hgLarge hg6 hd4 hdn hclockd
          hm hgapSq c hc)
      (Or.inl hinit)
  simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using
    hsum

/-- One raw hitting process dominates the complete unconditional ladder. -/
theorem phase0Ladder_raw_failure_unconditional
    (h3 : 3 ≤ n) (X : Species m) (d g k : ℕ)
    (hgLarge : properStageHeadlineThreshold ≤ g)
    (hg6 : 6 ≤ g)
    (hd4 : 4 ≤ d) (hdn : d ≤ n)
    (hclockd : 3 * d ≤ n)
    (hm : m * g ≤ n)
    (hgapSq : g * n ≤ d ^ 2)
    (c0 : Config m n) (hinit : HasPairwiseGap c0 X d) :
    terminalFailureMass
        (iter
          (freeze (Phase0LadderGood X d n k)
            (fun c => multiStep c h3))
          (k * phase0LadderStageHorizon m n) c0)
        (Phase0LadderGood X d n k) ≤
      (k : ℝ≥0∞) * phase0LadderUnconditionalStageError g := by
  have hmPos : 1 ≤ m := by
    have := X.isLt
    omega
  have hT :
      ∀ j < k, 0 <
        (fun _ => phase0LadderStageHorizon m n) j := by
    intro j hj
    unfold phase0LadderStageHorizon
    exact Nat.mul_pos
      (Nat.mul_pos (by norm_num) (by omega))
      (by omega)
  have hcompare :=
    StagedFreezeControl.targetFreeze_failure_le_stagedFreeze
      (Phase0LadderGood X d n k)
      (fun c => multiStep c h3)
      (phase0LadderCheckpoint X d n)
      (fun _ => phase0LadderStageHorizon m n)
      k hT c0
  have hsum :
      (∑ j ∈ Finset.range k,
        (fun _ => phase0LadderStageHorizon m n) j) =
          k * phase0LadderStageHorizon m n := by
    simp
  rw [hsum] at hcompare
  exact hcompare.trans
    (phase0Ladder_staged_failure_unconditional
      h3 X d g k hgLarge hg6 hd4 hdn hclockd
      hm hgapSq c0 hinit)

/-! ## Phase-zero exit -/

/-- The full unconditional raw phase-0 ladder reaches either consensus or the
aggregate binary-handoff checkpoint. -/
theorem phase0Ladder_raw_exit_unconditional
    (h3 : 3 ≤ n) (X : Species m) (d g : ℕ)
    (hgLarge : properStageHeadlineThreshold ≤ g)
    (hg6 : 6 ≤ g)
    (hd4 : 4 ≤ d) (hdn : d ≤ n)
    (hclockd : 3 * d ≤ n)
    (hm : m * g ≤ n)
    (hgapSq : g * n ≤ d ^ 2)
    (c0 : Config m n) (hinit : HasPairwiseGap c0 X d) :
    terminalFailureMass
        (iter
          (freeze (Phase0LadderExit X d)
            (fun c => multiStep c h3))
          ((Nat.log 2 n + 1) *
            phase0LadderStageHorizon m n) c0)
        (Phase0LadderExit X d) ≤
      ((Nat.log 2 n + 1 : ℕ) : ℝ≥0∞) *
        phase0LadderUnconditionalStageError g := by
  let k := Nat.log 2 n + 1
  have hfinal :
      ∀ c, Phase0LadderGood X d n k c →
        Phase0LadderExit X d c := by
    intro c hc
    rcases hc with hgap | hhandoff
    · left
      apply pairwiseGap_population_consensus
      have hscaleFinal :
          phase0LadderScale d n k = n := by
        simpa [k] using
          phase0LadderScale_log_succ d n (by omega) hdn
      rw [hscaleFinal] at hgap
      exact hgap
    · exact Or.inr hhandoff
  have hmono :=
    targetFreeze_failure_mono_target
      (K := fun c => multiStep c h3)
      (B := Phase0LadderGood X d n k)
      (C := Phase0LadderExit X d)
      hfinal
      (k * phase0LadderStageHorizon m n) c0
  exact hmono.trans
    (phase0Ladder_raw_failure_unconditional
      h3 X d g k hgLarge hg6 hd4 hdn hclockd
      hm hgapSq c0 hinit)

end Tri.Multi

#print axioms Tri.Multi.phase0Ladder_oneStage_unconditional
#print axioms Tri.Multi.phase0Ladder_raw_failure_unconditional
#print axioms Tri.Multi.phase0Ladder_raw_exit_unconditional
