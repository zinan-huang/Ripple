/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.MultiProductivePhase0Stage
import Tri.StagedLazyHitting

/-!
# The raw phase-0 ladder

This file composes the complete raw phase-0 stage while keeping the paper's
aggregate-exit threshold fixed at the initial gap.  The pairwise-gap checkpoint
doubles between stages; heterogeneous frozen blocks are then compared with one
ordinary raw-chain hitting process.
-/

namespace Tri.Multi

open scoped ENNReal

variable {m n : ℕ}

/-- The capped dyadic pairwise-gap scale. -/
def phase0LadderScale (d n : ℕ) : ℕ → ℕ
  | 0 => d
  | j + 1 => min (2 * phase0LadderScale d n j) n

@[simp] theorem phase0LadderScale_zero
    (d n : ℕ) :
    phase0LadderScale d n 0 = d :=
  rfl

@[simp] theorem phase0LadderScale_succ
    (d n j : ℕ) :
    phase0LadderScale d n (j + 1) =
      min (2 * phase0LadderScale d n j) n :=
  rfl

/-- Every capped dyadic scale remains below the population. -/
theorem phase0LadderScale_le
    (d n : ℕ) (hdn : d ≤ n) :
    ∀ j, phase0LadderScale d n j ≤ n := by
  intro j
  induction j with
  | zero => exact hdn
  | succ j _ => exact min_le_right _ _

/-- Capping never lowers a scale that started below the population. -/
theorem phase0LadderScale_ge
    (d n : ℕ) (hdn : d ≤ n) :
    ∀ j, d ≤ phase0LadderScale d n j := by
  intro j
  induction j with
  | zero => exact le_rfl
  | succ j ih =>
      rw [phase0LadderScale_succ]
      exact le_min (by omega) hdn

/-- The next dyadic checkpoint is weaker than the internal `4D` checkpoint
reached by one complete stage. -/
theorem phase0LadderScale_succ_le_hit
    (d n j : ℕ) :
    phase0LadderScale d n (j + 1) ≤
      min (4 * phase0LadderScale d n j) n := by
  rw [phase0LadderScale_succ]
  exact min_le_min (by omega) le_rfl

/-- Closed form of the capped dyadic scale. -/
theorem phase0LadderScale_eq
    (d n j : ℕ) (hdn : d ≤ n) :
    phase0LadderScale d n j = min (2 ^ j * d) n := by
  induction j with
  | zero => simp [min_eq_left hdn]
  | succ j ih =>
      rw [phase0LadderScale_succ, ih, pow_succ]
      by_cases h : 2 ^ j * d ≤ n
      · rw [min_eq_left h]
        congr 1
        ring
      · have hn : n ≤ 2 ^ j * d := by omega
        rw [min_eq_right hn]
        have hnDouble : n ≤ 2 * n := by omega
        rw [min_eq_right hnDouble]
        have hnTarget : n ≤ 2 ^ j * 2 * d := by
          calc
            n ≤ 2 ^ j * d := hn
            _ ≤ 2 ^ j * 2 * d := by
              nlinarith [Nat.zero_le (2 ^ j * d)]
        rw [min_eq_right hnTarget]

/-- After at most `log₂ n + 1` doublings, every positive initial scale is
capped at the population. -/
theorem phase0LadderScale_log_succ
    (d n : ℕ) (hd : 1 ≤ d) (hdn : d ≤ n) :
    phase0LadderScale d n (Nat.log 2 n + 1) = n := by
  rw [phase0LadderScale_eq d n _ hdn, min_eq_right]
  have hnPow :
      n ≤ 2 ^ (Nat.log 2 n + 1) :=
    (Nat.lt_pow_succ_log_self (by norm_num) n).le
  have hmul :
      2 ^ (Nat.log 2 n + 1) ≤
        2 ^ (Nat.log 2 n + 1) * d := by
    simpa using
      Nat.mul_le_mul_left (2 ^ (Nat.log 2 n + 1)) hd
  exact hnPow.trans hmul

/-- The stage error at a current pairwise-gap scale. -/
noncomputable def phase0LadderStageError
    (m n gamma D : ℕ) : ℝ≥0∞ :=
  (144 : ℝ≥0∞) * productiveAmplificationError m n D +
    (m : ℝ≥0∞) *
      ENNReal.ofReal
        (Real.exp (-((D : ℝ) ^ 2 / (18 * (n : ℝ))))) +
    ENNReal.ofReal
      (Real.exp (-((gamma * Nat.log 2 n : ℕ) : ℝ)))

/-- At rung `j`, either the pairwise gap has reached its current scale or the
fixed aggregate phase-exit checkpoint has already been hit. -/
def Phase0LadderGood
    (X : Species m) (d n j : ℕ) (c : Config m n) : Prop :=
  HasPairwiseGap c X (phase0LadderScale d n j) ∨
    Phase0AggregateHandoff X d c

noncomputable instance phase0LadderGoodDecidable
    (X : Species m) (d n j : ℕ) :
    DecidablePred (Phase0LadderGood X d n j) :=
  Classical.decPred _

/-- The phase-0 endpoint used by the two-species handoff. -/
def Phase0LadderExit
    (X : Species m) (d : ℕ) (c : Config m n) : Prop :=
  ConsensusOn c X ∨ Phase0AggregateHandoff X d c

noncomputable instance phase0LadderExitDecidable
    (X : Species m) (d : ℕ) :
    DecidablePred (Phase0LadderExit (n := n) X d) :=
  Classical.decPred _

/-- The checkpoint frozen during rung `j`.  The anchor is intentionally
ignored: the paper's threshold depends on the fixed initial scale `d`, not on
the random state where a block begins. -/
def phase0LadderCheckpoint
    (X : Species m) (d n : ℕ) :
    ℕ → Config m n → Config m n → Prop :=
  fun j _ c =>
    Phase0StageSuccessAt X d (phase0LadderScale d n j) c

noncomputable instance phase0LadderCheckpointDecidable
    (X : Species m) (d n : ℕ) :
    ∀ j a, DecidablePred (phase0LadderCheckpoint X d n j a) := by
  intro j a
  exact Classical.decPred _

/-- A rung checkpoint supplies the next ladder postcondition. -/
theorem phase0LadderCheckpoint_to_next
    (X : Species m) (d n j : ℕ) (c : Config m n)
    (h : Phase0StageSuccessAt X d
      (phase0LadderScale d n j) c) :
    Phase0LadderGood X d n (j + 1) c := by
  rcases h with hgap | hhandoff
  · left
    exact hasPairwiseGap_of_le
      (phase0LadderScale_succ_le_hit d n j) hgap
  · exact Or.inr hhandoff

/-- The raw horizon of every phase-0 rung. -/
def phase0LadderStageHorizon (m n : ℕ) : ℕ :=
  129472 * m * n

/-- One fixed-threshold raw rung advances the dyadic ladder. -/
theorem phase0Ladder_oneStage
    (h3 : 3 ≤ n) (X : Species m) (d gamma j : ℕ)
    (_hgamma : 1 ≤ gamma)
    (hd4 : 4 ≤ d) (hdn : d ≤ n)
    (hclockd : 3 * d ≤ n)
    (hscale : 6 ≤ gamma * Nat.log 2 n)
    (hm : m * (gamma * Nat.log 2 n) ≤ n)
    (c0 : Config m n)
    (hinit : Phase0LadderGood X d n j c0) :
    terminalFailureMass
        (StagedFreezeControl.block
          (fun c => multiStep c h3)
          (phase0LadderCheckpoint X d n)
          (fun _ => phase0LadderStageHorizon m n)
          j c0)
        (Phase0LadderGood X d n (j + 1)) ≤
      phase0LadderStageError m n gamma
        (phase0LadderScale d n j) := by
  let D := phase0LadderScale d n j
  have hD4 : 4 ≤ D :=
    hd4.trans (phase0LadderScale_ge d n hdn j)
  have hDn : D ≤ n :=
    phase0LadderScale_le d n hdn j
  rcases hinit with hgap | hhandoff
  · have hstage :=
      phase0StageAt_raw_failure_lemma13
        h3 X d D gamma _hgamma hD4 hDn hclockd
        hscale hm c0 hgap
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
        phase0LadderStageError] using hstage)
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

/-- The heterogeneous frozen raw blocks compose by a union bound. -/
theorem phase0Ladder_staged_failure
    (h3 : 3 ≤ n) (X : Species m) (d gamma k : ℕ)
    (hgamma : 1 ≤ gamma)
    (hd4 : 4 ≤ d) (hdn : d ≤ n)
    (hclockd : 3 * d ≤ n)
    (hscale : 6 ≤ gamma * Nat.log 2 n)
    (hm : m * (gamma * Nat.log 2 n) ≤ n)
    (c0 : Config m n) (hinit : HasPairwiseGap c0 X d) :
    terminalFailureMass
        (stagedIter
          (StagedFreezeControl.block
            (fun c => multiStep c h3)
            (phase0LadderCheckpoint X d n)
            (fun _ => phase0LadderStageHorizon m n))
          k c0)
        (Phase0LadderGood X d n k) ≤
      ∑ j ∈ Finset.range k,
        phase0LadderStageError m n gamma
          (phase0LadderScale d n j) := by
  apply terminalFailureMass_stagedIter
  · intro j hj c hc
    exact phase0Ladder_oneStage
      h3 X d gamma j hgamma hd4 hdn hclockd
      hscale hm c hc
  · exact Or.inl hinit

/-- One raw hitting process dominates the whole adaptively paused phase-0
ladder. -/
theorem phase0Ladder_raw_failure
    (h3 : 3 ≤ n) (X : Species m) (d gamma k : ℕ)
    (hgamma : 1 ≤ gamma)
    (hd4 : 4 ≤ d) (hdn : d ≤ n)
    (hclockd : 3 * d ≤ n)
    (hscale : 6 ≤ gamma * Nat.log 2 n)
    (hm : m * (gamma * Nat.log 2 n) ≤ n)
    (c0 : Config m n) (hinit : HasPairwiseGap c0 X d) :
    terminalFailureMass
        (iter
          (freeze (Phase0LadderGood X d n k)
            (fun c => multiStep c h3))
          (k * phase0LadderStageHorizon m n) c0)
        (Phase0LadderGood X d n k) ≤
      ∑ j ∈ Finset.range k,
        phase0LadderStageError m n gamma
          (phase0LadderScale d n j) := by
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
    (phase0Ladder_staged_failure
      h3 X d gamma k hgamma hd4 hdn hclockd
      hscale hm c0 hinit)

/-- The full raw phase-0 ladder reaches either designated consensus or the
paper's fixed aggregate handoff within `log₂ n + 1` raw stages. -/
theorem phase0Ladder_raw_exit
    (h3 : 3 ≤ n) (X : Species m) (d gamma : ℕ)
    (hgamma : 1 ≤ gamma)
    (hd4 : 4 ≤ d) (hdn : d ≤ n)
    (hclockd : 3 * d ≤ n)
    (hscale : 6 ≤ gamma * Nat.log 2 n)
    (hm : m * (gamma * Nat.log 2 n) ≤ n)
    (c0 : Config m n) (hinit : HasPairwiseGap c0 X d) :
    terminalFailureMass
        (iter
          (freeze (Phase0LadderExit X d)
            (fun c => multiStep c h3))
          ((Nat.log 2 n + 1) *
            phase0LadderStageHorizon m n) c0)
        (Phase0LadderExit X d) ≤
      ∑ j ∈ Finset.range (Nat.log 2 n + 1),
        phase0LadderStageError m n gamma
          (phase0LadderScale d n j) := by
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
    (phase0Ladder_raw_failure
      h3 X d gamma k hgamma hd4 hdn hclockd
      hscale hm c0 hinit)

end Tri.Multi

#print axioms Tri.Multi.phase0Ladder_oneStage
#print axioms Tri.Multi.phase0Ladder_staged_failure
#print axioms Tri.Multi.phase0Ladder_raw_failure
#print axioms Tri.Multi.phase0Ladder_raw_exit
