/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.MultiProductiveAmplificationLift
import Tri.MultiProductiveStateScalar

/-!
# Unconditional proper-stage amplification

The original uniform substage estimate discarded the actual gap to every
competitor and consequently paid a factor linear in the number of species.
The state-dependent estimate avoids that loss.  This file threads its
species-independent headline through all 144 proper substages.
-/

namespace Tri.Multi

open scoped ENNReal

variable {m n : ℕ}

/-! ## One-block error budget -/

/-- Species-independent error budget for one proper substage. -/
noncomputable def productiveAmplificationHeadlineError (g : ℕ) : ℝ≥0∞ :=
  (3 : ℝ≥0∞) *
    ENNReal.ofReal
      (Real.exp (-((g : ℝ) / properStageHeadlineDenominator)))

/-- The union bound over 144 proper substages is exactly 432 copies of the
common state-dependent exponential: each substage contributes three copies. -/
theorem productiveAmplificationHeadlineError_144
    (g : ℕ) :
    (144 : ℝ≥0∞) * productiveAmplificationHeadlineError g =
      (432 : ℝ≥0∞) *
        ENNReal.ofReal
          (Real.exp (-((g : ℝ) / properStageHeadlineDenominator))) := by
  unfold productiveAmplificationHeadlineError
  ring

/-! ## Lifting and composing proper substages

The state-dependent scalar estimate first advances one augmented checkpoint.
The same estimate then composes along the 144 deterministic checkpoint
indices; no new species-dependent coefficient appears in the composition.
-/

/-- Every proper substage advances one checkpoint with the
species-independent state-dependent error budget. -/
theorem productiveAmplificationStep_oneBlock_headline
    (h3 : 3 ≤ n) (X : Species m) (g Δ i : ℕ)
    (hi : i < 144)
    (hgLarge : properStageHeadlineThreshold ≤ g)
    (hΔ4 : 4 ≤ Δ)
    (hm : m * g ≤ n)
    (hscale : g * n ≤ Δ ^ 2)
    (hΔn : Δ ≤ n) :
    Reaches (productiveAmplificationStep h3 X Δ)
      (properAmplificationBlockLength n)
      (ProductiveAmplificationReady X Δ i)
      (ProductiveAmplificationReady X Δ (i + 1))
      (productiveAmplificationHeadlineError g) := by
  classical
  intro s hs
  change terminalFailureMass
      (iter (productiveAmplificationStep h3 X Δ)
        (properAmplificationBlockLength n) s)
      (ProductiveAmplificationReady X Δ (i + 1)) ≤
    productiveAmplificationHeadlineError g
  let D := properAmplificationTarget Δ i n
  let x0 := count s.config X
  have hsEq :
      s =
        productiveAmplificationBlockState X Δ i
          (properAmplificationBlockLength n) x0
          (properAmplificationBlockLength n) (s.config, 0) := by
    exact productiveAmplificationReady_eq_blockState h3 X Δ i s hs
  rw [hsEq,
    iter_productiveAmplificationStep_blockState
      h3 X Δ i x0 (properAmplificationBlockLength n) hi
      (s.config, 0)]
  have hclose :
      (productiveAmplificationBlockState X Δ i
          (properAmplificationBlockLength n) x0 0 :
          Config m n × ℕ → ProductiveAmplificationState m n) =
        productiveAmplificationFinish X
          (properAmplificationTarget Δ i n) i
          (properAmplificationBlockLength n) := by
    funext q
    exact productiveAmplificationBlockState_zero X Δ i
      (properAmplificationBlockLength n) x0 q
  rw [hclose]
  rw [terminalFailureMass_map_productiveAmplificationFinish]
  have hgap : HasPairwiseGap s.config X D := by
    exact hs.2.2.2.2.2
  have hDn : D ≤ n :=
    properAmplificationTarget_le_population Δ i n
  have hDx0 : D ≤ x0 :=
    pairwiseGap_le_count_of_le_population hDn hgap
  have hΔD : Δ ≤ D :=
    base_le_properAmplificationTarget Δ i n hΔn
  have hD4 : 4 ≤ D := hΔ4.trans hΔD
  have hstage :=
    productiveProperStage_progress_state
      h3 X D x0 hD4 hDx0 s.config rfl
  have hheadline :=
    productiveProperStageStateError_le_headline
      m n g Δ D x0 X s.config (by omega)
      hgLarge hΔ4 hm hscale hΔD hDx0 rfl hgap
  exact hstage.trans hheadline

/-- Sequential composition of the first `k ≤ 144` proper blocks with the
state-dependent headline error. -/
theorem productiveAmplificationStep_blocks_headline
    (h3 : 3 ≤ n) (X : Species m) (g Δ k : ℕ)
    (hk : k ≤ 144)
    (hgLarge : properStageHeadlineThreshold ≤ g)
    (hΔ4 : 4 ≤ Δ)
    (hm : m * g ≤ n)
    (hscale : g * n ≤ Δ ^ 2)
    (hΔn : Δ ≤ n) :
    Reaches (productiveAmplificationStep h3 X Δ)
      (k * properAmplificationBlockLength n)
      (ProductiveAmplificationReady X Δ 0)
      (ProductiveAmplificationReady X Δ k)
      ((k : ℝ≥0∞) * productiveAmplificationHeadlineError g) := by
  induction k with
  | zero =>
      simp only [zero_mul, Nat.cast_zero]
      intro s hs
      rw [tsum_eq_single s (by
        intro z hzs
        simp [iter, PMF.pure_apply, hzs])]
      simp [hs]
  | succ k ih =>
      have hk144 : k ≤ 144 := by omega
      have hklt : k < 144 := by omega
      have hprefix := ih hk144
      have hblock :=
        productiveAmplificationStep_oneBlock_headline
          h3 X g Δ k hklt hgLarge hΔ4 hm hscale hΔn
      have hcomp := hprefix.comp hblock
      simpa [Nat.succ_mul, Nat.cast_succ, add_mul] using hcomp

/-- All 144 proper blocks reach the capped quadrupling checkpoint within
`288n` productive slots. -/
theorem productiveAmplificationStep_144_headline
    (h3 : 3 ≤ n) (X : Species m) (g Δ : ℕ)
    (hgLarge : properStageHeadlineThreshold ≤ g)
    (hΔ4 : 4 ≤ Δ)
    (hm : m * g ≤ n)
    (hscale : g * n ≤ Δ ^ 2)
    (hΔn : Δ ≤ n) :
    Reaches (productiveAmplificationStep h3 X Δ)
      (288 * n)
      (ProductiveAmplificationReady X Δ 0)
      (ProductiveAmplificationReady X Δ 144)
      ((144 : ℝ≥0∞) * productiveAmplificationHeadlineError g) := by
  rw [show 288 * n =
      144 * properAmplificationBlockLength n by
    unfold properAmplificationBlockLength
    ring]
  exact productiveAmplificationStep_blocks_headline
    h3 X g Δ 144 (by omega) hgLarge hΔ4 hm hscale hΔn

/-! ## Returning to the physical productive chain -/

/-- Physical productive-chain form of the unconditional 144-block
amplification estimate. -/
theorem productiveStep_properAmplification_hitting_headline
    (h3 : 3 ≤ n) (X : Species m) (g Δ : ℕ)
    (hgLarge : properStageHeadlineThreshold ≤ g)
    (hΔ4 : 4 ≤ Δ)
    (hm : m * g ≤ n)
    (hscale : g * n ≤ Δ ^ 2)
    (hΔn : Δ ≤ n)
    (c0 : Config m n) (hinit : HasPairwiseGap c0 X Δ) :
    let A : Config m n → Prop :=
      fun c => HasPairwiseGap c X (min (4 * Δ) n)
    terminalFailureMass
        (iter (freeze A (productiveStep h3)) (288 * n) c0) A ≤
      (144 : ℝ≥0∞) * productiveAmplificationHeadlineError g := by
  classical
  dsimp only
  let A : Config m n → Prop :=
    fun c => HasPairwiseGap c X (min (4 * Δ) n)
  let s0 := productiveAmplificationInitial X c0
  have hs0 : ProductiveAmplificationReady X Δ 0 s0 :=
    productiveAmplificationInitial_ready X Δ c0 hΔn hinit
  have hlazy :=
    targetFreeze_failure_le_lazy_projection A
      (productiveStep h3) (productiveAmplificationStep h3 X Δ)
      ProductiveAmplificationState.toConfig
      (productiveAmplificationStep_isLazyProjection h3 X Δ)
      (288 * n) s0
  have hblocks :=
    productiveAmplificationStep_144_headline
      h3 X g Δ hgLarge hΔ4 hm hscale hΔn s0 hs0
  have hlift :
      terminalFailureMass
          (iter (productiveAmplificationStep h3 X Δ) (288 * n) s0)
          (fun q => A q.toConfig) ≤
        terminalFailureMass
          (iter (productiveAmplificationStep h3 X Δ) (288 * n) s0)
          (ProductiveAmplificationReady X Δ 144) := by
    apply terminalFailureMass_mono
    intro q hq
    exact productiveAmplificationReady_144_pairwiseGap X Δ q hq
  exact hlazy.trans (hlift.trans hblocks)

end Tri.Multi

#print axioms Tri.Multi.productiveAmplificationStep_oneBlock_headline
#print axioms Tri.Multi.productiveAmplificationStep_144_headline
#print axioms Tri.Multi.productiveStep_properAmplification_hitting_headline
