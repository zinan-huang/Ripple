/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.MultiProductiveTimeChangePaper
import Tri.PaperLemma12
import Tri.HitProbMono
import Tri.SameHorizon

/-!
# One complete raw phase-0 stage

This file composes the proper-stage estimate with the physical productive
clock.  The stopping boundary distinguishes genuine success from loss of the
protected half-gap, so an early plurality failure is charged rather than
silently accepted.
-/

namespace Tri.Multi

open scoped ENNReal

variable {m n : ℕ}

/-- The binary handoff region: `X` exceeds the aggregate opposition by more
than the current phase-0 scale. -/
def Phase0AggregateHandoff
    (X : Species m) (D : ℕ) (c : Config m n) : Prop :=
  zSum c X + D < count c X

/-- A phase-0 stage succeeds either at the proper-stage checkpoint or at the
stronger aggregate handoff. -/
def Phase0StageSuccess
    (X : Species m) (D : ℕ) (c : Config m n) : Prop :=
  Lemma12HitGap X D c ∨ Phase0AggregateHandoff X D c

/-- Loss of the half-gap protected by the no-backsliding estimate. -/
def Phase0StageBad
    (X : Species m) (D : ℕ) (c : Config m n) : Prop :=
  ¬ HasPairwiseGap c X (D / 2)

/-- The counted stage stops on success or on a charged half-gap loss. -/
def Phase0StageBoundary
    (X : Species m) (D : ℕ) (c : Config m n) : Prop :=
  Phase0StageSuccess X D c ∨ Phase0StageBad X D c

/-- A phase-0 stage with a fixed phase-exit threshold `d` and a separately
growing pairwise-gap scale `D`.  The paper keeps `d` equal to the initial
square-root gap throughout phase 0. -/
def Phase0StageSuccessAt
    (X : Species m) (d D : ℕ) (c : Config m n) : Prop :=
  Lemma12HitGap X D c ∨ Phase0AggregateHandoff X d c

/-- The fixed-exit-threshold stage stops either on success or on loss of the
half-gap protected at its current scale. -/
def Phase0StageBoundaryAt
    (X : Species m) (d D : ℕ) (c : Config m n) : Prop :=
  Phase0StageSuccessAt X d D c ∨ Phase0StageBad X D c

noncomputable instance phase0AggregateHandoffDecidable
    (X : Species m) (D : ℕ) :
    DecidablePred (Phase0AggregateHandoff (n := n) X D) :=
  Classical.decPred _

noncomputable instance phase0StageSuccessDecidable
    (X : Species m) (D : ℕ) :
    DecidablePred (Phase0StageSuccess (n := n) X D) :=
  Classical.decPred _

noncomputable instance phase0StageBadDecidable
    (X : Species m) (D : ℕ) :
    DecidablePred (Phase0StageBad (n := n) X D) :=
  Classical.decPred _

noncomputable instance phase0StageBoundaryDecidable
    (X : Species m) (D : ℕ) :
    DecidablePred (Phase0StageBoundary (n := n) X D) :=
  Classical.decPred _

noncomputable instance phase0StageSuccessAtDecidable
    (X : Species m) (d D : ℕ) :
    DecidablePred (Phase0StageSuccessAt (n := n) X d D) :=
  Classical.decPred _

noncomputable instance phase0StageBoundaryAtDecidable
    (X : Species m) (d D : ℕ) :
    DecidablePred (Phase0StageBoundaryAt (n := n) X d D) :=
  Classical.decPred _

/-- The success-or-half-gap boundary contains every state where the paper's
phase-0 productive-mass floor ceases to apply. -/
theorem phase0StageBoundary_of_clockBoundary
    (X : Species m) (D : ℕ) (hD4 : 4 ≤ D) (c : Config m n)
    (hclock : PaperPhase0ConfigBoundary X D c) :
    Phase0StageBoundary X D c := by
  unfold PaperPhase0ConfigBoundary at hclock
  push Not at hclock
  by_cases hmax : IsMaxSpecies c X
  · left
    exact Or.inr (hclock hmax)
  · right
    unfold Phase0StageBad
    intro hgap
    apply hmax
    intro Z
    by_cases hZX : Z = X
    · subst Z
      exact le_rfl
    · exact Nat.le_of_lt
        (pairwiseGap_unique (by omega) hgap Z hZX)

/-- The fixed-exit-threshold stage boundary contains every state where the
paper's phase-0 productive-mass floor at threshold `d` ceases to apply. -/
theorem phase0StageBoundaryAt_of_clockBoundary
    (X : Species m) (d D : ℕ) (hD4 : 4 ≤ D) (c : Config m n)
    (hclock : PaperPhase0ConfigBoundary X d c) :
    Phase0StageBoundaryAt X d D c := by
  unfold PaperPhase0ConfigBoundary at hclock
  push Not at hclock
  by_cases hmax : IsMaxSpecies c X
  · left
    exact Or.inr (hclock hmax)
  · right
    unfold Phase0StageBad
    intro hgap
    apply hmax
    intro Z
    by_cases hZX : Z = X
    · subst Z
      exact le_rfl
    · exact Nat.le_of_lt
        (pairwiseGap_unique (by omega) hgap Z hZX)

/-- The union boundary is the sequential success-then-bad freeze. -/
theorem phase0StageBoundary_freeze
    (K : Config m n → PMF (Config m n))
    (X : Species m) (D : ℕ) :
    freeze (Phase0StageBoundary X D) K =
      freeze (Phase0StageBad X D)
        (freeze (Phase0StageSuccess X D) K) := by
  funext c
  by_cases hs : Phase0StageSuccess X D c <;>
    by_cases hb : Phase0StageBad X D c
  · rw [freeze_of_mem c (show Phase0StageBoundary X D c from Or.inl hs),
        freeze_of_mem c hb]
  · rw [freeze_of_mem c (show Phase0StageBoundary X D c from Or.inl hs),
        freeze_of_not_mem c hb, freeze_of_mem c hs]
  · rw [freeze_of_mem c (show Phase0StageBoundary X D c from Or.inr hb),
        freeze_of_mem c hb]
  · have hboundary : ¬ Phase0StageBoundary X D c := by
      intro h
      rcases h with h | h <;> contradiction
    rw [freeze_of_not_mem c hboundary, freeze_of_not_mem c hb,
        freeze_of_not_mem c hs]

/-- The fixed-exit-threshold boundary is the sequential success-then-bad
freeze. -/
theorem phase0StageBoundaryAt_freeze
    (K : Config m n → PMF (Config m n))
    (X : Species m) (d D : ℕ) :
    freeze (Phase0StageBoundaryAt X d D) K =
      freeze (Phase0StageBad X D)
        (freeze (Phase0StageSuccessAt X d D) K) := by
  funext c
  by_cases hs : Phase0StageSuccessAt X d D c <;>
    by_cases hb : Phase0StageBad X D c
  · rw [freeze_of_mem c
          (show Phase0StageBoundaryAt X d D c from Or.inl hs),
        freeze_of_mem c hb]
  · rw [freeze_of_mem c
          (show Phase0StageBoundaryAt X d D c from Or.inl hs),
        freeze_of_not_mem c hb, freeze_of_mem c hs]
  · rw [freeze_of_mem c
          (show Phase0StageBoundaryAt X d D c from Or.inr hb),
        freeze_of_mem c hb]
  · have hboundary : ¬ Phase0StageBoundaryAt X d D c := by
      intro h
      rcases h with h | h <;> contradiction
    rw [freeze_of_not_mem c hboundary, freeze_of_not_mem c hb,
        freeze_of_not_mem c hs]
/-- The productive half-gap stop is exactly a freeze on the stage bad set. -/
theorem productivePairGapStop_eq_phase0StageBad_freeze
    (h3 : 3 ≤ n) (X : Species m) (D : ℕ) :
    productivePairGapStop h3 X (D / 2) =
      freeze (Phase0StageBad X D) (productiveStep h3) := by
  funext c
  unfold productivePairGapStop freeze Phase0StageBad
  by_cases hgap : HasPairwiseGap c X (D / 2) <;> simp [hgap]

/-- The stopped half-gap failure mass is the corresponding first-hit
probability. -/
theorem productivePairGapStop_failure_eq_hitProb
    (h3 : 3 ≤ n) (X : Species m) (D T : ℕ)
    (c0 : Config m n) :
    hitProb (Phase0StageBad X D) (productiveStep h3) T c0 =
      globalPairGapFailureMass
        (iter (productivePairGapStop h3 X (D / 2)) T c0)
        X (D / 2) := by
  rw [productivePairGapStop_eq_phase0StageBad_freeze h3 X D]
  unfold hitProb globalPairGapFailureMass expect ind Phase0StageBad
  apply tsum_congr
  intro c
  by_cases hgap : HasPairwiseGap c X (D / 2) <;> simp [hgap]

/-- Under the success-or-bad stopped law, terminal bad mass is a bad hitting
probability for the success-stopped productive chain. -/
theorem phase0StageBad_mass_eq_hitProb
    (h3 : 3 ≤ n) (X : Species m) (D T : ℕ)
    (c0 : Config m n) :
    terminalFailureMass
        (iter
          (freeze (Phase0StageBoundary X D) (productiveStep h3))
          T c0)
        (fun c => ¬ Phase0StageBad X D c) =
      hitProb (Phase0StageBad X D)
        (freeze (Phase0StageSuccess X D) (productiveStep h3))
        T c0 := by
  rw [phase0StageBoundary_freeze (productiveStep h3) X D]
  unfold terminalFailureMass hitProb expect ind
  apply tsum_congr
  intro c
  by_cases hbad : Phase0StageBad X D c <;> simp [hbad]

/-- The bad terminal mass for a fixed phase-exit threshold is the bad hitting
probability for the corresponding success-stopped productive chain. -/
theorem phase0StageBad_mass_eq_hitProbAt
    (h3 : 3 ≤ n) (X : Species m) (d D T : ℕ)
    (c0 : Config m n) :
    terminalFailureMass
        (iter
          (freeze (Phase0StageBoundaryAt X d D) (productiveStep h3))
          T c0)
        (fun c => ¬ Phase0StageBad X D c) =
      hitProb (Phase0StageBad X D)
        (freeze (Phase0StageSuccessAt X d D) (productiveStep h3))
        T c0 := by
  rw [phase0StageBoundaryAt_freeze (productiveStep h3) X d D]
  unfold terminalFailureMass hitProb expect ind
  apply tsum_congr
  intro c
  by_cases hbad : Phase0StageBad X D c <;> simp [hbad]

/-- A boundary-stopped productive stage pays exactly the proper-stage hitting
error plus the half-gap no-backsliding error. -/
theorem phase0Stage_productive_failure
    (h3 : 3 ≤ n) (X : Species m) (D : ℕ)
    (hD4 : 4 ≤ D) (hDn : D ≤ n)
    (c0 : Config m n) (hinit : HasPairwiseGap c0 X D) :
    terminalFailureMass
        (iter
          (freeze (Phase0StageBoundary X D) (productiveStep h3))
          (288 * n) c0)
        (Phase0StageSuccess X D) ≤
      (144 : ℝ≥0∞) * productiveAmplificationError m n D +
        (m : ℝ≥0∞) *
          ENNReal.ofReal
            (Real.exp (-((D : ℝ) ^ 2 / (18 * (n : ℝ))))) := by
  let K : Config m n → PMF (Config m n) := productiveStep h3
  let B : Config m n → Prop := Phase0StageBoundary X D
  let A : Config m n → Prop := Phase0StageSuccess X D
  let Bad : Config m n → Prop := Phase0StageBad X D
  let p := iter (freeze B K) (288 * n) c0
  have hcover :
      terminalFailureMass p A ≤
        terminalFailureMass p (fun c => B c ∧ ¬ Bad c) := by
    apply terminalFailureMass_mono
    intro c hc
    rcases hc.1 with hsuccess | hbad
    · exact hsuccess
    · exact False.elim (hc.2 hbad)
  have hsplit :
      terminalFailureMass p (fun c => B c ∧ ¬ Bad c) ≤
        terminalFailureMass p B +
          terminalFailureMass p (fun c => ¬ Bad c) :=
    terminalFailureMass_inter_le p B (fun c => ¬ Bad c)
  have hlive :
      terminalFailureMass p B ≤
        (144 : ℝ≥0∞) * productiveAmplificationError m n D := by
    have hmono :=
      targetFreeze_failure_mono_target
        (K := K)
        (B := Lemma12HitGap X D)
        (C := B)
        (fun c hhit => Or.inl (Or.inl hhit))
        (288 * n) c0
    exact hmono.trans
      (by
        simpa [K] using
          lemma12_properStage_hitting
            h3 X D hD4 hDn c0 hinit)
  have hbad :
      terminalFailureMass p (fun c => ¬ Bad c) ≤
        (m : ℝ≥0∞) *
          ENNReal.ofReal
            (Real.exp (-((D : ℝ) ^ 2 / (18 * (n : ℝ))))) := by
    calc
      terminalFailureMass p (fun c => ¬ Bad c) =
          hitProb Bad (freeze A K) (288 * n) c0 := by
            simpa [p, K, B, A, Bad] using
              phase0StageBad_mass_eq_hitProb
                h3 X D (288 * n) c0
      _ ≤ hitProb Bad K (288 * n) c0 :=
        hitProb_freeze_le Bad A K (288 * n) c0
      _ =
          globalPairGapFailureMass
            (iter (productivePairGapStop h3 X (D / 2))
              (288 * n) c0)
            X (D / 2) := by
              simpa [K, Bad] using
                productivePairGapStop_failure_eq_hitProb
                  h3 X D (288 * n) c0
      _ ≤
          (m : ℝ≥0∞) *
            ENNReal.ofReal
              (Real.exp (-((D : ℝ) ^ 2 / (18 * (n : ℝ))))) :=
        productivePairGapStop_half_failure_exp
          h3 X D hD4 hDn (288 * n) c0 hinit
  exact hcover.trans (hsplit.trans (add_le_add hlive hbad))

/-- A productive stage with a fixed phase-exit threshold pays the same
proper-stage and no-backsliding errors as the single-scale specialization. -/
theorem phase0StageAt_productive_failure
    (h3 : 3 ≤ n) (X : Species m) (d D : ℕ)
    (hD4 : 4 ≤ D) (hDn : D ≤ n)
    (c0 : Config m n) (hinit : HasPairwiseGap c0 X D) :
    terminalFailureMass
        (iter
          (freeze (Phase0StageBoundaryAt X d D) (productiveStep h3))
          (288 * n) c0)
        (Phase0StageSuccessAt X d D) ≤
      (144 : ℝ≥0∞) * productiveAmplificationError m n D +
        (m : ℝ≥0∞) *
          ENNReal.ofReal
            (Real.exp (-((D : ℝ) ^ 2 / (18 * (n : ℝ))))) := by
  let K : Config m n → PMF (Config m n) := productiveStep h3
  let B : Config m n → Prop := Phase0StageBoundaryAt X d D
  let A : Config m n → Prop := Phase0StageSuccessAt X d D
  let Bad : Config m n → Prop := Phase0StageBad X D
  let p := iter (freeze B K) (288 * n) c0
  have hcover :
      terminalFailureMass p A ≤
        terminalFailureMass p (fun c => B c ∧ ¬ Bad c) := by
    apply terminalFailureMass_mono
    intro c hc
    rcases hc.1 with hsuccess | hbad
    · exact hsuccess
    · exact False.elim (hc.2 hbad)
  have hsplit :
      terminalFailureMass p (fun c => B c ∧ ¬ Bad c) ≤
        terminalFailureMass p B +
          terminalFailureMass p (fun c => ¬ Bad c) :=
    terminalFailureMass_inter_le p B (fun c => ¬ Bad c)
  have hlive :
      terminalFailureMass p B ≤
        (144 : ℝ≥0∞) * productiveAmplificationError m n D := by
    have hmono :=
      targetFreeze_failure_mono_target
        (K := K)
        (B := Lemma12HitGap X D)
        (C := B)
        (fun c hhit => Or.inl (Or.inl hhit))
        (288 * n) c0
    exact hmono.trans
      (by
        simpa [K] using
          lemma12_properStage_hitting
            h3 X D hD4 hDn c0 hinit)
  have hbad :
      terminalFailureMass p (fun c => ¬ Bad c) ≤
        (m : ℝ≥0∞) *
          ENNReal.ofReal
            (Real.exp (-((D : ℝ) ^ 2 / (18 * (n : ℝ))))) := by
    calc
      terminalFailureMass p (fun c => ¬ Bad c) =
          hitProb Bad (freeze A K) (288 * n) c0 := by
            simpa [p, K, B, A, Bad] using
              phase0StageBad_mass_eq_hitProbAt
                h3 X d D (288 * n) c0
      _ ≤ hitProb Bad K (288 * n) c0 :=
        hitProb_freeze_le Bad A K (288 * n) c0
      _ =
          globalPairGapFailureMass
            (iter (productivePairGapStop h3 X (D / 2))
              (288 * n) c0)
            X (D / 2) := by
              simpa [K, Bad] using
                productivePairGapStop_failure_eq_hitProb
                  h3 X D (288 * n) c0
      _ ≤
          (m : ℝ≥0∞) *
            ENNReal.ofReal
              (Real.exp (-((D : ℝ) ^ 2 / (18 * (n : ℝ))))) :=
        productivePairGapStop_half_failure_exp
          h3 X D hD4 hDn (288 * n) c0 hinit
  exact hcover.trans (hsplit.trans (add_le_add hlive hbad))

/-- One complete phase-0 stage on the physical raw chain: proper-stage
failure, half-gap loss, and productive-clock delay are all explicit. -/
theorem phase0Stage_raw_failure
    (h3 : 3 ≤ n) (X : Species m) (D L : ℕ)
    (hD4 : 4 ≤ D) (hDn : D ≤ n)
    (hclockD : 3 * D ≤ n) (h6m : 6 * m ≤ n)
    (c0 : Config m n) (hinit : HasPairwiseGap c0 X D) :
    terminalFailureMass
        (iter
          (freeze (Phase0StageSuccess X D)
            (fun c => multiStep c h3))
          (multiPaperPhase0ClockHorizon m (288 * n) L) c0)
        (Phase0StageSuccess X D) ≤
      ((144 : ℝ≥0∞) * productiveAmplificationError m n D +
        (m : ℝ≥0∞) *
          ENNReal.ofReal
            (Real.exp (-((D : ℝ) ^ 2 / (18 * (n : ℝ)))))) +
        ENNReal.ofReal (Real.exp (-(L : ℝ))) := by
  let A : Config m n → Prop := Phase0StageSuccess X D
  let B : Config m n → Prop := Phase0StageBoundary X D
  have hphysical :=
    multiStep_targetFailure_le_productiveCountdownStop
      A B h3
      (multiPaperPhase0ClockHorizon m (288 * n) L)
      (288 * n) c0
  have hcountdown :=
    productiveCountdownStop_failure_le
      A B h3
      (multiPaperPhase0ClockHorizon m (288 * n) L)
      (288 * n) c0
  have hclock :=
    paperPhase0Countdown_live_deadline_of_boundary
      B h3 X D
      (phase0StageBoundary_of_clockBoundary X D hD4)
      hclockD h6m (288 * n) L c0
  have hproductive :=
    phase0Stage_productive_failure
      h3 X D hD4 hDn c0 hinit
  exact hphysical.trans <| hcountdown.trans <|
    (add_le_add hproductive hclock)

/-- One raw stage with a fixed phase-exit threshold `d` and current
pairwise-gap scale `D`. -/
theorem phase0StageAt_raw_failure
    (h3 : 3 ≤ n) (X : Species m) (d D L : ℕ)
    (hD4 : 4 ≤ D) (hDn : D ≤ n)
    (hclockd : 3 * d ≤ n) (h6m : 6 * m ≤ n)
    (c0 : Config m n) (hinit : HasPairwiseGap c0 X D) :
    terminalFailureMass
        (iter
          (freeze (Phase0StageSuccessAt X d D)
            (fun c => multiStep c h3))
          (multiPaperPhase0ClockHorizon m (288 * n) L) c0)
        (Phase0StageSuccessAt X d D) ≤
      ((144 : ℝ≥0∞) * productiveAmplificationError m n D +
        (m : ℝ≥0∞) *
          ENNReal.ofReal
            (Real.exp (-((D : ℝ) ^ 2 / (18 * (n : ℝ)))))) +
        ENNReal.ofReal (Real.exp (-(L : ℝ))) := by
  let A : Config m n → Prop := Phase0StageSuccessAt X d D
  let B : Config m n → Prop := Phase0StageBoundaryAt X d D
  have hphysical :=
    multiStep_targetFailure_le_productiveCountdownStop
      A B h3
      (multiPaperPhase0ClockHorizon m (288 * n) L)
      (288 * n) c0
  have hcountdown :=
    productiveCountdownStop_failure_le
      A B h3
      (multiPaperPhase0ClockHorizon m (288 * n) L)
      (288 * n) c0
  have hclock :=
    paperPhase0Countdown_live_deadline_of_boundary
      B h3 X d
      (phase0StageBoundaryAt_of_clockBoundary X d D hD4)
      hclockd h6m (288 * n) L c0
  have hproductive :=
    phase0StageAt_productive_failure
      h3 X d D hD4 hDn c0 hinit
  exact hphysical.trans <| hcountdown.trans <|
    (add_le_add hproductive hclock)

/-- Paper-constant specialization of one raw phase-0 stage. -/
theorem phase0Stage_raw_failure_lemma13
    (h3 : 3 ≤ n) (X : Species m) (D gamma : ℕ)
    (_hgamma : 1 ≤ gamma)
    (hD4 : 4 ≤ D) (hDn : D ≤ n)
    (hclockD : 3 * D ≤ n)
    (hscale : 6 ≤ gamma * Nat.log 2 n)
    (hm : m * (gamma * Nat.log 2 n) ≤ n)
    (c0 : Config m n) (hinit : HasPairwiseGap c0 X D) :
    terminalFailureMass
        (iter
          (freeze (Phase0StageSuccess X D)
            (fun c => multiStep c h3))
          (129472 * m * n) c0)
        (Phase0StageSuccess X D) ≤
      ((144 : ℝ≥0∞) * productiveAmplificationError m n D +
        (m : ℝ≥0∞) *
          ENNReal.ofReal
            (Real.exp (-((D : ℝ) ^ 2 / (18 * (n : ℝ)))))) +
        ENNReal.ofReal
          (Real.exp (-((gamma * Nat.log 2 n : ℕ) : ℝ))) := by
  have hmPos : 1 ≤ m := by
    have := X.isLt
    omega
  have h6m : 6 * m ≤ n := by
    calc
      6 * m = m * 6 := by omega
      _ ≤ m * (gamma * Nat.log 2 n) :=
        Nat.mul_le_mul_left m hscale
      _ ≤ n := hm
  have hlog : gamma * Nat.log 2 n ≤ n := by
    calc
      gamma * Nat.log 2 n =
          1 * (gamma * Nat.log 2 n) := by omega
      _ ≤ m * (gamma * Nat.log 2 n) :=
        Nat.mul_le_mul_right (gamma * Nat.log 2 n) hmPos
      _ ≤ n := hm
  have hstage :=
    phase0Stage_raw_failure
      h3 X D n hD4 hDn hclockD h6m c0 hinit
  have hHorizon :
      multiPaperPhase0ClockHorizon m (288 * n) n =
        129472 * m * n := by
    simp only [multiPaperPhase0ClockHorizon, multiPhase0ClockHorizon]
    ring
  rw [hHorizon] at hstage
  exact hstage.trans <| add_le_add le_rfl <|
    ENNReal.ofReal_le_ofReal <| Real.exp_le_exp.mpr <| by
      have hlogR :
          ((gamma * Nat.log 2 n : ℕ) : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast hlog
      linarith

/-- Paper-constant specialization with the phase-exit threshold held fixed
while the current pairwise-gap scale grows. -/
theorem phase0StageAt_raw_failure_lemma13
    (h3 : 3 ≤ n) (X : Species m) (d D gamma : ℕ)
    (_hgamma : 1 ≤ gamma)
    (hD4 : 4 ≤ D) (hDn : D ≤ n)
    (hclockd : 3 * d ≤ n)
    (hscale : 6 ≤ gamma * Nat.log 2 n)
    (hm : m * (gamma * Nat.log 2 n) ≤ n)
    (c0 : Config m n) (hinit : HasPairwiseGap c0 X D) :
    terminalFailureMass
        (iter
          (freeze (Phase0StageSuccessAt X d D)
            (fun c => multiStep c h3))
          (129472 * m * n) c0)
        (Phase0StageSuccessAt X d D) ≤
      ((144 : ℝ≥0∞) * productiveAmplificationError m n D +
        (m : ℝ≥0∞) *
          ENNReal.ofReal
            (Real.exp (-((D : ℝ) ^ 2 / (18 * (n : ℝ)))))) +
        ENNReal.ofReal
          (Real.exp (-((gamma * Nat.log 2 n : ℕ) : ℝ))) := by
  have hmPos : 1 ≤ m := by
    have := X.isLt
    omega
  have h6m : 6 * m ≤ n := by
    calc
      6 * m = m * 6 := by omega
      _ ≤ m * (gamma * Nat.log 2 n) :=
        Nat.mul_le_mul_left m hscale
      _ ≤ n := hm
  have hlog : gamma * Nat.log 2 n ≤ n := by
    calc
      gamma * Nat.log 2 n =
          1 * (gamma * Nat.log 2 n) := by omega
      _ ≤ m * (gamma * Nat.log 2 n) :=
        Nat.mul_le_mul_right (gamma * Nat.log 2 n) hmPos
      _ ≤ n := hm
  have hstage :=
    phase0StageAt_raw_failure
      h3 X d D n hD4 hDn hclockd h6m c0 hinit
  have hHorizon :
      multiPaperPhase0ClockHorizon m (288 * n) n =
        129472 * m * n := by
    simp only [multiPaperPhase0ClockHorizon, multiPhase0ClockHorizon]
    ring
  rw [hHorizon] at hstage
  exact hstage.trans <| add_le_add le_rfl <|
    ENNReal.ofReal_le_ofReal <| Real.exp_le_exp.mpr <| by
      have hlogR :
          ((gamma * Nat.log 2 n : ℕ) : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast hlog
      linarith

end Tri.Multi

#print axioms Tri.Multi.phase0StageBoundary_of_clockBoundary
#print axioms Tri.Multi.productivePairGapStop_failure_eq_hitProb
#print axioms Tri.Multi.phase0Stage_productive_failure
#print axioms Tri.Multi.phase0Stage_raw_failure
#print axioms Tri.Multi.phase0Stage_raw_failure_lemma13
#print axioms Tri.Multi.phase0StageAt_raw_failure_lemma13
