/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.MultiProductiveAmplification
import Tri.LazyHitting
import Tri.Compose

/-!
# A lazy physical lift for proper-stage amplification

The paper's 144 proper substages use parameters chosen from the state at the
start of each substage.  This file packages those substages into one homogeneous
augmented kernel.  Its projection is always either one productive reaction or a
self-loop, so `Tri.targetFreeze_failure_le_lazy_projection` applies.
-/

namespace Tri.Multi

open scoped ENNReal

variable {m n : ℕ}

/-- Augmented state for the 144 proper substages.  `remaining` counts physical
slots left in the current substage, while `stageStart` freezes the value of
`count X` used in that substage's parameters. -/
structure ProductiveAmplificationState (m n : ℕ) where
  config : Config m n
  stage : ℕ
  remaining : ℕ
  stageStart : ℕ
  involving : ℕ
  failed : Bool

noncomputable instance :
    DecidableEq (ProductiveAmplificationState m n) :=
  Classical.decEq _

/-- Forget the amplification bookkeeping. -/
def ProductiveAmplificationState.toConfig
    (q : ProductiveAmplificationState m n) : Config m n :=
  q.config

/-- Each proper substage receives exactly `2n` productive-reaction slots. -/
def properAmplificationBlockLength (n : ℕ) : ℕ :=
  2 * n

/-- A running augmented state inside one fixed proper substage. -/
def productiveAmplificationActive
    (i remaining x0 : ℕ) (q : Config m n × ℕ) :
    ProductiveAmplificationState m n where
  config := q.1
  stage := i
  remaining := remaining
  stageStart := x0
  involving := q.2
  failed := false

/-- Close one substage.  Only the proved capped `49/48` target counts as
success; a successful state is initialized for the next substage. -/
noncomputable def productiveAmplificationFinish
    (X : Species m) (D i H : ℕ) (q : Config m n × ℕ) :
    ProductiveAmplificationState m n := by
  classical
  exact
    if HasPairwiseGap q.1 X (properStageTarget D n) then
      { config := q.1
        stage := i + 1
        remaining := H
        stageStart := count q.1 X
        involving := 0
        failed := false }
    else
      { config := q.1
        stage := i
        remaining := 0
        stageStart := count q.1 X
        involving := q.2
        failed := true }

/-- Metadata update after one stopped substage step. -/
noncomputable def productiveAmplificationNext
    (X : Species m) (D i H x0 remaining : ℕ)
    (q : Config m n × ℕ) :
    ProductiveAmplificationState m n :=
  if remaining = 1 then
    productiveAmplificationFinish X D i H q
  else
    productiveAmplificationActive i (remaining - 1) x0 q

@[simp] theorem productiveAmplificationActive_toConfig
    (i remaining x0 : ℕ) (q : Config m n × ℕ) :
    (productiveAmplificationActive i remaining x0 q).toConfig = q.1 :=
  rfl

@[simp] theorem productiveAmplificationFinish_toConfig
    (X : Species m) (D i H : ℕ) (q : Config m n × ℕ) :
    (productiveAmplificationFinish X D i H q).toConfig = q.1 := by
  classical
  unfold productiveAmplificationFinish
  split_ifs <;> rfl

@[simp] theorem productiveAmplificationNext_toConfig
    (X : Species m) (D i H x0 remaining : ℕ)
    (q : Config m n × ℕ) :
    (productiveAmplificationNext X D i H x0 remaining q).toConfig =
      q.1 := by
  classical
  unfold productiveAmplificationNext
  split_ifs <;> simp

/-- One homogeneous slot of the 144-substage construction.  Malformed,
failed, and completed metadata states are absorbing. -/
noncomputable def productiveAmplificationStep
    (h3 : 3 ≤ n) (X : Species m) (Δ : ℕ) :
    ProductiveAmplificationState m n →
      PMF (ProductiveAmplificationState m n) := by
  classical
  exact fun q =>
    if q.failed = true then
      PMF.pure q
    else if 144 ≤ q.stage then
      PMF.pure q
    else if q.remaining = 0 then
      PMF.pure q
    else
      let D := properAmplificationTarget Δ q.stage n
      let K :=
        productiveInvolvingStageDeadlineStop h3 X
          (properStageScale q.stageStart) (D / 2)
          (properStageTarget D n)
          (properInvolvingTarget q.stageStart)
      (K (q.config, q.involving)).map
        (productiveAmplificationNext X D q.stage
          (properAmplificationBlockLength n) q.stageStart q.remaining)

/-- Every slot of the augmented construction projects either to one genuine
productive reaction or to a self-loop. -/
theorem productiveAmplificationStep_isLazyProjection
    (h3 : 3 ≤ n) (X : Species m) (Δ : ℕ) :
    IsLazyProjection (productiveStep h3)
      (productiveAmplificationStep h3 X Δ)
      ProductiveAmplificationState.toConfig := by
  classical
  intro q
  unfold productiveAmplificationStep
  by_cases hfailed : q.failed = true
  · rw [if_pos hfailed]
    right
    exact PMF.pure_map _ _
  · rw [if_neg hfailed]
    by_cases hdone : 144 ≤ q.stage
    · rw [if_pos hdone]
      right
      exact PMF.pure_map _ _
    · rw [if_neg hdone]
      by_cases hzero : q.remaining = 0
      · rw [if_pos hzero]
        right
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
        split_ifs with hlive
        · left
          exact productiveInvolvingCount_map_fst h3 X
            (q.config, q.involving)
        · right
          exact PMF.pure_map _ _

/-- The stopped kernel used during proper substage `i`. -/
noncomputable def productiveAmplificationStageKernel
    (h3 : 3 ≤ n) (X : Species m) (Δ i x0 : ℕ) :
    Config m n × ℕ → PMF (Config m n × ℕ) :=
  let D := properAmplificationTarget Δ i n
  productiveInvolvingStageDeadlineStop h3 X
    (properStageScale x0) (D / 2) (properStageTarget D n)
    (properInvolvingTarget x0)

/-- Embed a stopped-kernel state with `r` slots remaining.  At zero it is
closed by the same success/failure test used by the homogeneous lift. -/
noncomputable def productiveAmplificationBlockState
    (X : Species m) (Δ i H x0 r : ℕ) (q : Config m n × ℕ) :
    ProductiveAmplificationState m n :=
  if r = 0 then
    productiveAmplificationFinish X
      (properAmplificationTarget Δ i n) i H q
  else
    productiveAmplificationActive i r x0 q

@[simp] theorem productiveAmplificationBlockState_zero
    (X : Species m) (Δ i H x0 : ℕ) (q : Config m n × ℕ) :
    productiveAmplificationBlockState X Δ i H x0 0 q =
      productiveAmplificationFinish X
        (properAmplificationTarget Δ i n) i H q := by
  simp [productiveAmplificationBlockState]

@[simp] theorem productiveAmplificationBlockState_succ
    (X : Species m) (Δ i H x0 r : ℕ) (q : Config m n × ℕ) :
    productiveAmplificationBlockState X Δ i H x0 (r + 1) q =
      productiveAmplificationActive i (r + 1) x0 q := by
  simp [productiveAmplificationBlockState]

/-- One lifted slot on a well-formed active block commutes with the
time-dependent block embedding. -/
theorem productiveAmplificationStep_blockState_succ
    (h3 : 3 ≤ n) (X : Species m) (Δ i x0 r : ℕ)
    (hi : i < 144) (q : Config m n × ℕ) :
    productiveAmplificationStep h3 X Δ
        (productiveAmplificationBlockState X Δ i
          (properAmplificationBlockLength n) x0 (r + 1) q) =
      (productiveAmplificationStageKernel h3 X Δ i x0 q).map
        (productiveAmplificationBlockState X Δ i
          (properAmplificationBlockLength n) x0 r) := by
  classical
  rw [productiveAmplificationBlockState_succ]
  unfold productiveAmplificationStep
  simp only [productiveAmplificationActive, Bool.false_eq_true, if_false,
    not_le.mpr hi, Nat.add_eq_zero_iff, one_ne_zero, and_false,
    productiveAmplificationStageKernel]
  apply congrArg (fun f =>
    (productiveInvolvingStageDeadlineStop h3 X
      (properStageScale x0)
      (properAmplificationTarget Δ i n / 2)
      (properStageTarget (properAmplificationTarget Δ i n) n)
      (properInvolvingTarget x0) q).map f)
  funext z
  by_cases hr : r = 0
  · subst r
    simp [productiveAmplificationNext,
      productiveAmplificationBlockState]
  · simp [productiveAmplificationNext,
      productiveAmplificationBlockState, hr]

/-- Running an entire lifted block is exactly the existing stopped-kernel
iterate, followed by the deterministic success/failure closure. -/
theorem iter_productiveAmplificationStep_blockState
    (h3 : 3 ≤ n) (X : Species m) (Δ i x0 r : ℕ)
    (hi : i < 144) (q : Config m n × ℕ) :
    iter (productiveAmplificationStep h3 X Δ) r
        (productiveAmplificationBlockState X Δ i
          (properAmplificationBlockLength n) x0 r q) =
      (iter (productiveAmplificationStageKernel h3 X Δ i x0) r q).map
        (productiveAmplificationBlockState X Δ i
          (properAmplificationBlockLength n) x0 0) := by
  induction r generalizing q with
  | zero =>
      exact (PMF.pure_map _ _).symm
  | succ r ih =>
      rw [iter_succ,
        productiveAmplificationStep_blockState_succ h3 X Δ i x0 r hi q,
        PMF.bind_map]
      rw [iter_succ, PMF.map_bind]
      apply congrArg (fun f =>
        (productiveAmplificationStageKernel h3 X Δ i x0 q).bind f)
      funext a
      exact ih a

/-- Well-formed checkpoint before proper substage `i`. -/
def ProductiveAmplificationReady
    (X : Species m) (Δ i : ℕ)
    (q : ProductiveAmplificationState m n) : Prop :=
  q.failed = false ∧
    q.stage = i ∧
    q.remaining = properAmplificationBlockLength n ∧
    q.stageStart = count q.config X ∧
    q.involving = 0 ∧
    HasPairwiseGap q.config X (properAmplificationTarget Δ i n)

noncomputable instance productiveAmplificationReady_decidablePred
    (X : Species m) (Δ i : ℕ) :
    DecidablePred (ProductiveAmplificationReady (n := n) X Δ i) :=
  Classical.decPred _

noncomputable instance hasPairwiseGap_decidablePred
    (X : Species m) (d : ℕ) :
    DecidablePred (fun c : Config m n => HasPairwiseGap c X d) :=
  Classical.decPred _

/-- One uniform error budget for every proper substage. -/
noncomputable def productiveAmplificationError
    (m n Δ : ℕ) : ℝ≥0∞ :=
  ((2 * m + 1 : ℕ) : ℝ≥0∞) *
    ENNReal.ofReal
      (Real.exp (-((Δ : ℝ) ^ 2 / (82944 * (n : ℝ)))))

/-- Expanded coefficient after all 144 proper substages. -/
theorem productiveAmplificationError_144
    (m n Δ : ℕ) :
    (144 : ℝ≥0∞) * productiveAmplificationError m n Δ =
      ((288 * m + 144 : ℕ) : ℝ≥0∞) *
        ENNReal.ofReal
          (Real.exp (-((Δ : ℝ) ^ 2 / (82944 * (n : ℝ))))) := by
  unfold productiveAmplificationError
  push_cast
  ring

/-- A stronger pairwise gap implies every weaker pairwise gap. -/
theorem hasPairwiseGap_of_le
    {c : Config m n} {X : Species m} {a b : ℕ}
    (hab : a ≤ b) (hgap : HasPairwiseGap c X b) :
    HasPairwiseGap c X a := by
  intro Y hYX
  have hY := hgap Y hYX
  omega

/-- Closing substage `i` lands at checkpoint `i+1` exactly when its proved
capped target holds. -/
theorem productiveAmplificationFinish_ready_iff
    (X : Species m) (Δ i : ℕ) (q : Config m n × ℕ) :
    ProductiveAmplificationReady X Δ (i + 1)
        (productiveAmplificationFinish X
          (properAmplificationTarget Δ i n) i
          (properAmplificationBlockLength n) q) ↔
      HasPairwiseGap q.1 X
        (properStageTarget (properAmplificationTarget Δ i n) n) := by
  classical
  let D := properAmplificationTarget Δ i n
  by_cases htarget :
      HasPairwiseGap q.1 X (properStageTarget D n)
  · have hnext :
        HasPairwiseGap q.1 X
          (properAmplificationTarget Δ (i + 1) n) :=
      hasPairwiseGap_of_le
        (properAmplificationTarget_succ_le_stageTarget Δ i n)
        htarget
    simp [ProductiveAmplificationReady,
      productiveAmplificationFinish, D, htarget, hnext]
  · simp [ProductiveAmplificationReady,
      productiveAmplificationFinish, D, htarget]

/-- Failure of the next checkpoint after deterministic block closure is
exactly failure of the current substage's capped target. -/
theorem terminalFailureMass_map_productiveAmplificationFinish
    (p : PMF (Config m n × ℕ))
    (X : Species m) (Δ i : ℕ) :
    terminalFailureMass
        (p.map (productiveAmplificationFinish X
          (properAmplificationTarget Δ i n) i
          (properAmplificationBlockLength n)))
        (ProductiveAmplificationReady X Δ (i + 1)) =
      globalPairGapFailureMass (p.map Prod.fst) X
        (properStageTarget (properAmplificationTarget Δ i n) n) := by
  classical
  rw [terminalFailureMass_map,
    globalPairGapFailureMass_map_fst]
  unfold terminalFailureMass globalInvolvingPairGapFailureMass
  apply tsum_congr
  intro q
  by_cases htarget :
      HasPairwiseGap q.1 X
        (properStageTarget (properAmplificationTarget Δ i n) n)
  · have hready :
        ProductiveAmplificationReady X Δ (i + 1)
          (productiveAmplificationFinish X
            (properAmplificationTarget Δ i n) i
            (properAmplificationBlockLength n) q) :=
      (productiveAmplificationFinish_ready_iff X Δ i q).2 htarget
    simp [hready, htarget]
  · have hnotReady :
        ¬ ProductiveAmplificationReady X Δ (i + 1)
          (productiveAmplificationFinish X
            (properAmplificationTarget Δ i n) i
            (properAmplificationBlockLength n) q) := by
      intro hready
      exact htarget
        ((productiveAmplificationFinish_ready_iff X Δ i q).1 hready)
    simp [hnotReady, htarget]

/-- A checkpoint is the positive-length block embedding of its configuration
and a freshly reset involvement counter. -/
theorem productiveAmplificationReady_eq_blockState
    (h3 : 3 ≤ n) (X : Species m) (Δ i : ℕ)
    (q : ProductiveAmplificationState m n)
    (hq : ProductiveAmplificationReady X Δ i q) :
    q =
      productiveAmplificationBlockState X Δ i
        (properAmplificationBlockLength n) (count q.config X)
        (properAmplificationBlockLength n) (q.config, 0) := by
  rcases hq with ⟨hfailed, hstage, hremaining, hstart, hinvolving, -⟩
  have hH : properAmplificationBlockLength n ≠ 0 := by
    unfold properAmplificationBlockLength
    omega
  rw [show productiveAmplificationBlockState X Δ i
      (properAmplificationBlockLength n) (count q.config X)
      (properAmplificationBlockLength n) (q.config, 0) =
        productiveAmplificationActive i
          (properAmplificationBlockLength n) (count q.config X)
          (q.config, 0) by
    simp [productiveAmplificationBlockState, hH]]
  cases q
  simp_all [productiveAmplificationActive]

/-- Every proper substage advances one checkpoint with the same uniform
failure budget. -/
theorem productiveAmplificationStep_oneBlock
    (h3 : 3 ≤ n) (X : Species m) (Δ i : ℕ)
    (hi : i < 144) (hΔ4 : 4 ≤ Δ) (hΔn : Δ ≤ n) :
    Reaches (productiveAmplificationStep h3 X Δ)
      (properAmplificationBlockLength n)
      (ProductiveAmplificationReady X Δ i)
      (ProductiveAmplificationReady X Δ (i + 1))
      (productiveAmplificationError m n Δ) := by
  classical
  intro s hs
  change terminalFailureMass
      (iter (productiveAmplificationStep h3 X Δ)
        (properAmplificationBlockLength n) s)
      (ProductiveAmplificationReady X Δ (i + 1)) ≤
    productiveAmplificationError m n Δ
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
  have hD4 : 4 ≤ D := by
    exact hΔ4.trans (base_le_properAmplificationTarget Δ i n hΔn)
  have hx0n : x0 ≤ n := by
    dsimp only [x0]
    have htotal := count_add_zSum s.config X
    omega
  have hstage :=
    productiveProperStage_progress h3 X D x0 hD4 hDx0
      s.config rfl hgap
  have huniform :=
    properStage_error_le_uniform m n Δ D x0
      (by omega) hD4
      (base_le_properAmplificationTarget Δ i n hΔn)
      hDx0 hx0n
  exact hstage.trans huniform

/-- The canonical augmented start state. -/
def productiveAmplificationInitial
    (X : Species m) (c : Config m n) :
    ProductiveAmplificationState m n :=
  productiveAmplificationActive 0
    (properAmplificationBlockLength n) (count c X) (c, 0)

/-- The canonical start state is checkpoint zero. -/
theorem productiveAmplificationInitial_ready
    (X : Species m) (Δ : ℕ) (c : Config m n)
    (hΔn : Δ ≤ n) (hgap : HasPairwiseGap c X Δ) :
    ProductiveAmplificationReady X Δ 0
      (productiveAmplificationInitial X c) := by
  simp [ProductiveAmplificationReady,
    productiveAmplificationInitial, productiveAmplificationActive,
    properAmplificationTarget_zero, min_eq_left hΔn, hgap]

/-- Sequential composition of the first `k ≤ 144` homogeneous blocks. -/
theorem productiveAmplificationStep_blocks
    (h3 : 3 ≤ n) (X : Species m) (Δ k : ℕ)
    (hk : k ≤ 144) (hΔ4 : 4 ≤ Δ) (hΔn : Δ ≤ n) :
    Reaches (productiveAmplificationStep h3 X Δ)
      (k * properAmplificationBlockLength n)
      (ProductiveAmplificationReady X Δ 0)
      (ProductiveAmplificationReady X Δ k)
      ((k : ℝ≥0∞) * productiveAmplificationError m n Δ) := by
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
        productiveAmplificationStep_oneBlock
          h3 X Δ k hklt hΔ4 hΔn
      have hcomp := hprefix.comp hblock
      simpa [Nat.succ_mul, Nat.cast_succ, add_mul] using hcomp

/-- Paper-sized specialization: 144 proper blocks use `288n` productive
slots and reach the exact capped quadrupling checkpoint. -/
theorem productiveAmplificationStep_144
    (h3 : 3 ≤ n) (X : Species m) (Δ : ℕ)
    (hΔ4 : 4 ≤ Δ) (hΔn : Δ ≤ n) :
    Reaches (productiveAmplificationStep h3 X Δ)
      (288 * n)
      (ProductiveAmplificationReady X Δ 0)
      (ProductiveAmplificationReady X Δ 144)
      ((144 : ℝ≥0∞) * productiveAmplificationError m n Δ) := by
  rw [show 288 * n =
      144 * properAmplificationBlockLength n by
    unfold properAmplificationBlockLength
    ring]
  exact productiveAmplificationStep_blocks
    h3 X Δ 144 (by omega) hΔ4 hΔn

/-- The final augmented checkpoint carries the exact paper target
`min (4Δ) n`. -/
theorem productiveAmplificationReady_144_pairwiseGap
    (X : Species m) (Δ : ℕ)
    (q : ProductiveAmplificationState m n)
    (hq : ProductiveAmplificationReady X Δ 144 q) :
    HasPairwiseGap q.config X (min (4 * Δ) n) := by
  have hgap := hq.2.2.2.2.2
  rwa [properAmplificationTarget_144] at hgap

/-- **Proper-stage amplification on the physical productive chain.**

Starting from pairwise gap `Δ ≥ 4`, the original productive chain hits the
capped quadrupled gap within `288n` productive-reaction slots, except for the
144-fold uniform error. -/
theorem productiveStep_properAmplification_hitting
    (h3 : 3 ≤ n) (X : Species m) (Δ : ℕ)
    (hΔ4 : 4 ≤ Δ) (hΔn : Δ ≤ n)
    (c0 : Config m n) (hinit : HasPairwiseGap c0 X Δ) :
    let A : Config m n → Prop :=
      fun c => HasPairwiseGap c X (min (4 * Δ) n)
    terminalFailureMass
        (iter (freeze A (productiveStep h3)) (288 * n) c0) A ≤
      (144 : ℝ≥0∞) * productiveAmplificationError m n Δ := by
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
    productiveAmplificationStep_144 h3 X Δ hΔ4 hΔn s0 hs0
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

#print axioms Tri.Multi.productiveAmplificationStep_isLazyProjection
#print axioms Tri.Multi.iter_productiveAmplificationStep_blockState
#print axioms Tri.Multi.productiveAmplificationStep_oneBlock
#print axioms Tri.Multi.productiveAmplificationStep_blocks
#print axioms Tri.Multi.productiveStep_properAmplification_hitting
