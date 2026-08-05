/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.MultiProductivePhase0Stage
import Tri.MultiProductiveAmplificationUnconditional
import Tri.HitThenReaches

/-!
# Unconditional raw phase-0 stages

The old phase-0 assembly bounded loss of the protected half-gap a second time
after the proper-stage construction.  That introduced another global species
union bound.  Here the success-or-bad stopped physical chain is compared
directly with the 144-block augmented process.  A bad state already makes the
current augmented substage project to a self-loop, so its mass is charged by
the same state-dependent block error.
-/

namespace Tri.Multi

open scoped ENNReal

variable {m n : ℕ}

/-! ## Coupling the augmented and physical stopped chains

The projection is exact while the protected half-gap is live. Once that gap
is lost, the augmented process projects to a self-loop, so the bad-boundary
mass is charged inside the same amplification error rather than by a second
species union bound.
-/

/-- At a state that has lost the original protected half-gap, one augmented
amplification slot projects to a physical self-loop. -/
theorem productiveAmplificationStep_project_pure_of_stageBad
    (h3 : 3 ≤ n) (X : Species m) (Δ : ℕ) (hΔn : Δ ≤ n)
    (q : ProductiveAmplificationState m n)
    (hbad : Phase0StageBad X Δ q.config) :
    (productiveAmplificationStep h3 X Δ q).map
        ProductiveAmplificationState.toConfig =
      PMF.pure q.config := by
  classical
  unfold productiveAmplificationStep
  by_cases hfailed : q.failed = true
  · rw [if_pos hfailed]
    exact PMF.pure_map _ _
  · rw [if_neg hfailed]
    by_cases hdone : 144 ≤ q.stage
    · rw [if_pos hdone]
      exact PMF.pure_map _ _
    · rw [if_neg hdone]
      by_cases hzero : q.remaining = 0
      · rw [if_pos hzero]
        exact PMF.pure_map _ _
      · rw [if_neg hzero, PMF.map_comp]
        have hnext :
            (ProductiveAmplificationState.toConfig :
                ProductiveAmplificationState m n → Config m n) ∘
                  (productiveAmplificationNext X
                    (properAmplificationTarget Δ q.stage n) q.stage
                    (properAmplificationBlockLength n) q.stageStart
                    q.remaining :
                    Config m n × ℕ →
                      ProductiveAmplificationState m n) =
              (Prod.fst : Config m n × ℕ → Config m n) := by
          funext z
          exact productiveAmplificationNext_toConfig
            X (properAmplificationTarget Δ q.stage n) q.stage
              (properAmplificationBlockLength n) q.stageStart
              q.remaining z
        rw [hnext]
        unfold productiveInvolvingStageDeadlineStop
        rw [if_neg]
        · exact PMF.pure_map _ _
        · intro hlive
          apply hbad
          exact hasPairwiseGap_of_le
            (Nat.div_le_div_right
              (base_le_properAmplificationTarget
                Δ q.stage n hΔn))
            hlive.1

/-- The success-frozen augmented process is lazy over the physical process
stopped at success or loss of the protected half-gap. -/
theorem phase0StageBoundaryAt_amplification_isLazyProjection
    (h3 : 3 ≤ n) (X : Species m) (d Δ : ℕ) (hΔn : Δ ≤ n) :
    IsLazyProjection
      (freeze (Phase0StageBoundaryAt X d Δ) (productiveStep h3))
      (freeze
        (fun q : ProductiveAmplificationState m n =>
          Phase0StageSuccessAt X d Δ q.config)
        (productiveAmplificationStep h3 X Δ))
      ProductiveAmplificationState.toConfig := by
  classical
  intro q
  by_cases hsuccess : Phase0StageSuccessAt X d Δ q.config
  · rw [freeze_of_mem q hsuccess]
    right
    exact PMF.pure_map _ _
  · rw [freeze_of_not_mem q hsuccess]
    by_cases hboundary : Phase0StageBoundaryAt X d Δ q.config
    · have hbad : Phase0StageBad X Δ q.config := by
        rcases hboundary with hs | hb
        · exact False.elim (hsuccess hs)
        · exact hb
      right
      exact productiveAmplificationStep_project_pure_of_stageBad
        h3 X Δ hΔn q hbad
    · simpa only [ProductiveAmplificationState.toConfig,
          freeze_of_not_mem q.config hboundary] using
        productiveAmplificationStep_isLazyProjection h3 X Δ q

/-- A final amplification checkpoint is a phase-0 success state. -/
theorem productiveAmplificationReady_144_phase0StageSuccessAt
    (X : Species m) (d Δ : ℕ)
    (q : ProductiveAmplificationState m n)
    (hq : ProductiveAmplificationReady X Δ 144 q) :
    Phase0StageSuccessAt X d Δ q.config := by
  exact Or.inl
    (productiveAmplificationReady_144_pairwiseGap X Δ q hq)

/-- The final checkpoint is already absorbing for the augmented kernel. -/
theorem productiveAmplificationStep_pure_of_ready_144
    (h3 : 3 ≤ n) (X : Species m) (Δ : ℕ)
    (q : ProductiveAmplificationState m n)
    (hq : ProductiveAmplificationReady X Δ 144 q) :
    productiveAmplificationStep h3 X Δ q = PMF.pure q := by
  unfold productiveAmplificationStep
  have hfailed : q.failed ≠ true := by
    rw [hq.1]
    decide
  have hstage : q.stage = 144 := hq.2.1
  rw [if_neg hfailed, if_pos (by omega : 144 ≤ q.stage)]

/-! ## Productive-clock stage bound -/

/-- One productive phase-0 stage, stopped on success or half-gap loss, pays
only the state-dependent 144-block error. -/
theorem phase0StageAt_productive_failure_headline
    (h3 : 3 ≤ n) (X : Species m) (g d Δ : ℕ)
    (hgLarge : properStageHeadlineThreshold ≤ g)
    (hd4 : 4 ≤ d)
    (hdΔ : d ≤ Δ)
    (hΔn : Δ ≤ n)
    (hm : m * g ≤ n)
    (hscale : g * n ≤ d ^ 2)
    (c0 : Config m n) (hinit : HasPairwiseGap c0 X Δ) :
    terminalFailureMass
        (iter
          (freeze (Phase0StageBoundaryAt X d Δ) (productiveStep h3))
          (288 * n) c0)
        (Phase0StageSuccessAt X d Δ) ≤
      (144 : ℝ≥0∞) * productiveAmplificationHeadlineError g := by
  classical
  let K : Config m n → PMF (Config m n) :=
    freeze (Phase0StageBoundaryAt X d Δ) (productiveStep h3)
  let A : Config m n → Prop := Phase0StageSuccessAt X d Δ
  let L :
      ProductiveAmplificationState m n →
        PMF (ProductiveAmplificationState m n) :=
    freeze
      (fun q : ProductiveAmplificationState m n => A q.config)
      (productiveAmplificationStep h3 X Δ)
  let R : ProductiveAmplificationState m n → Prop :=
    ProductiveAmplificationReady X Δ 144
  let s0 := productiveAmplificationInitial X c0
  have hΔ4 : 4 ≤ Δ := hd4.trans hdΔ
  have hscaleΔ : g * n ≤ Δ ^ 2 :=
    hscale.trans (Nat.pow_le_pow_left hdΔ 2)
  have hs0 : ProductiveAmplificationReady X Δ 0 s0 :=
    productiveAmplificationInitial_ready X Δ c0 hΔn hinit
  have hlazy : IsLazyProjection K L
      ProductiveAmplificationState.toConfig := by
    simpa only [K, A, L] using
      phase0StageBoundaryAt_amplification_isLazyProjection
        h3 X d Δ hΔn
  have hcompare :=
    targetFreeze_failure_le_lazy_projection
      A K L ProductiveAmplificationState.toConfig
      hlazy (288 * n) s0
  have hAK : freeze A K = K := by
    simpa only [K, A] using
      freeze_comp_eq_of_subset
        (Phase0StageSuccessAt X d Δ)
        (Phase0StageBoundaryAt X d Δ)
        (productiveStep h3) (fun _ hs => Or.inl hs)
  rw [hAK] at hcompare
  have hreadySuccess :
      ∀ q, R q → A q.config := by
    intro q hq
    exact productiveAmplificationReady_144_phase0StageSuccessAt
      X d Δ q hq
  have htargetMono :=
    targetFreeze_failure_mono_target
      (K := productiveAmplificationStep h3 X Δ)
      (B := R)
      (C := fun q : ProductiveAmplificationState m n => A q.config)
      hreadySuccess (288 * n) s0
  have hfreezeR :
      freeze R (productiveAmplificationStep h3 X Δ) =
        productiveAmplificationStep h3 X Δ := by
    apply freeze_eq_of_absorbing
    intro q hq
    exact productiveAmplificationStep_pure_of_ready_144
      h3 X Δ q hq
  rw [hfreezeR] at htargetMono
  have hblocks :=
    productiveAmplificationStep_144_headline
      h3 X g Δ hgLarge hΔ4 hm hscaleΔ hΔn s0 hs0
  exact hcompare.trans <| htargetMono.trans hblocks

/-! ## Transfer to the raw-interaction clock

The productive-chain estimate is lifted to the physical clock by the
countdown coupling. Its only additional loss is the exponential probability
of seeing too few productive interactions before the chosen deadline.
-/

/-- One complete raw phase-0 stage with the state-dependent proper-stage
error and the productive-clock delay. -/
theorem phase0StageAt_raw_failure_headline
    (h3 : 3 ≤ n) (X : Species m) (g d Δ L : ℕ)
    (hgLarge : properStageHeadlineThreshold ≤ g)
    (hd4 : 4 ≤ d)
    (hdΔ : d ≤ Δ)
    (hΔn : Δ ≤ n)
    (hclockd : 3 * d ≤ n)
    (h6m : 6 * m ≤ n)
    (hm : m * g ≤ n)
    (hscale : g * n ≤ d ^ 2)
    (c0 : Config m n) (hinit : HasPairwiseGap c0 X Δ) :
    terminalFailureMass
        (iter
          (freeze (Phase0StageSuccessAt X d Δ)
            (fun c => multiStep c h3))
          (multiPaperPhase0ClockHorizon m (288 * n) L) c0)
        (Phase0StageSuccessAt X d Δ) ≤
      (144 : ℝ≥0∞) * productiveAmplificationHeadlineError g +
        ENNReal.ofReal (Real.exp (-(L : ℝ))) := by
  let A : Config m n → Prop := Phase0StageSuccessAt X d Δ
  let B : Config m n → Prop := Phase0StageBoundaryAt X d Δ
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
      (phase0StageBoundaryAt_of_clockBoundary X d Δ
        (hd4.trans hdΔ))
      hclockd h6m (288 * n) L c0
  have hproductive :=
    phase0StageAt_productive_failure_headline
      h3 X g d Δ hgLarge hd4 hdΔ hΔn hm hscale c0 hinit
  exact hphysical.trans <| hcountdown.trans <|
    add_le_add hproductive hclock

/-- Paper-clock specialization of one unconditional raw phase-0 stage. -/
theorem phase0StageAt_raw_failure_headline_paper
    (h3 : 3 ≤ n) (X : Species m) (g d Δ : ℕ)
    (hgLarge : properStageHeadlineThreshold ≤ g)
    (hg6 : 6 ≤ g)
    (hd4 : 4 ≤ d)
    (hdΔ : d ≤ Δ)
    (hΔn : Δ ≤ n)
    (hclockd : 3 * d ≤ n)
    (hm : m * g ≤ n)
    (hscale : g * n ≤ d ^ 2)
    (c0 : Config m n) (hinit : HasPairwiseGap c0 X Δ) :
    terminalFailureMass
        (iter
          (freeze (Phase0StageSuccessAt X d Δ)
            (fun c => multiStep c h3))
          (129472 * m * n) c0)
        (Phase0StageSuccessAt X d Δ) ≤
      (144 : ℝ≥0∞) * productiveAmplificationHeadlineError g +
        ENNReal.ofReal (Real.exp (-(g : ℝ))) := by
  have hmPos : 1 ≤ m := by
    have := X.isLt
    omega
  have h6m : 6 * m ≤ n := by
    calc
      6 * m = m * 6 := by omega
      _ ≤ m * g := Nat.mul_le_mul_left m hg6
      _ ≤ n := hm
  have hgn : g ≤ n := by
    calc
      g = 1 * g := by omega
      _ ≤ m * g := Nat.mul_le_mul_right g hmPos
      _ ≤ n := hm
  have hstage :=
    phase0StageAt_raw_failure_headline
      h3 X g d Δ n hgLarge hd4 hdΔ hΔn hclockd
      h6m hm hscale c0 hinit
  have hHorizon :
      multiPaperPhase0ClockHorizon m (288 * n) n =
        129472 * m * n := by
    simp only [multiPaperPhase0ClockHorizon, multiPhase0ClockHorizon]
    ring
  rw [hHorizon] at hstage
  exact hstage.trans <| add_le_add le_rfl <|
    ENNReal.ofReal_le_ofReal <| Real.exp_le_exp.mpr <| by
      have hgnR : (g : ℝ) ≤ n := by exact_mod_cast hgn
      linarith

end Tri.Multi

#print axioms Tri.Multi.phase0StageAt_productive_failure_headline
#print axioms Tri.Multi.phase0StageAt_raw_failure_headline
#print axioms Tri.Multi.phase0StageAt_raw_failure_headline_paper
