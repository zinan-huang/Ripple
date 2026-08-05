/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.MultiProductiveStageSafety

/-!
# One complete proper stage

The four stopping conditions now live on one productive-event process.  A
terminal target failure is partitioned into half-gap loss (a), survival for
all `2n` productive steps (b), or reaching the involvement deadline before
global target success (c).  Global target success is completion (d).
-/

namespace Tri.Multi

open scoped BigOperators ENNReal

variable {m n : ℕ}

/-- Terminal global gap-failure mass on a configuration/counter state. -/
noncomputable def globalInvolvingPairGapFailureMass
    (p : PMF (Config m n × ℕ)) (X : Species m) (d : ℕ) : ℝ≥0∞ := by
  classical
  exact ∑' q : Config m n × ℕ,
    if ¬ HasPairwiseGap q.1 X d then p q else 0

/-- Global pair-gap failure can be evaluated before or after forgetting an
auxiliary natural-valued counter. -/
theorem globalPairGapFailureMass_map_fst
    (p : PMF (Config m n × ℕ)) (X : Species m) (d : ℕ) :
    globalPairGapFailureMass (p.map Prod.fst) X d =
      globalInvolvingPairGapFailureMass p X d := by
  classical
  let Bad : Config m n → Prop := fun c => ¬ HasPairwiseGap c X d
  calc
    globalPairGapFailureMass (p.map Prod.fst) X d =
      expect (p.map Prod.fst)
        (fun c => (if Bad c then 1 else 0 : ℝ≥0∞)) := by
      unfold globalPairGapFailureMass expect
      apply tsum_congr
      intro c
      by_cases hc : Bad c <;> simp [Bad, hc]
    _ = expect p
        (fun q => (if Bad q.1 then 1 else 0 : ℝ≥0∞)) := by
      rw [expect_map]
    _ = globalInvolvingPairGapFailureMass p X d := by
      unfold expect globalInvolvingPairGapFailureMass
      apply tsum_congr
      intro q
      by_cases hq : Bad q.1 <;> simp [Bad, hq]

/-- Exact first-of-boundaries decomposition on the common proper-stage
process. -/
theorem productiveProperStage_failure_decomposition
    (h3 : 3 ≤ n) (X : Species m)
    (D x0 T : ℕ) (c0 : Config m n)
    (hx0 : count c0 X = x0) :
    let p :=
      iter
        (productiveInvolvingStageDeadlineStop h3 X
          (properStageScale x0) (D / 2) (properStageTarget D n)
          (properInvolvingTarget x0))
        T (c0, 0)
    globalPairGapFailureMass (p.map Prod.fst)
        X (properStageTarget D n) ≤
      globalPairGapFailureMass (p.map Prod.fst) X (D / 2) +
        globalProperTargetFailureMass p X
          (properStageTarget D n) (properInvolvingTarget x0) +
        ∑' q : Config m n × ℕ,
          if ProductiveProperStageLive X (properStageScale x0) (D / 2)
              (properStageTarget D n) (properInvolvingTarget x0) q
          then p q else 0 := by
  classical
  dsimp only
  let K :=
    productiveInvolvingStageDeadlineStop h3 X
      (properStageScale x0) (D / 2) (properStageTarget D n)
      (properInvolvingTarget x0)
  let p := iter K T (c0, 0)
  have hq0 : ProductiveInvolvingCountInv X x0 (c0, 0) := by
    unfold ProductiveInvolvingCountInv
    simp [hx0]
  have hpoint : ∀ q : Config m n × ℕ,
      (if ¬ HasPairwiseGap q.1 X (properStageTarget D n)
        then p q else 0) ≤
      (if ¬ HasPairwiseGap q.1 X (D / 2) then p q else 0) +
        (if ¬ HasPairwiseGap q.1 X (properStageTarget D n) ∧
            properInvolvingTarget x0 ≤ q.2
          then p q else 0) +
        (if ProductiveProperStageLive X (properStageScale x0) (D / 2)
            (properStageTarget D n) (properInvolvingTarget x0) q
          then p q else 0) := by
    intro q
    by_cases htarget :
        ¬ HasPairwiseGap q.1 X (properStageTarget D n)
    · by_cases hpq : p q = 0
      · simp [hpq]
      · have hInv : ProductiveInvolvingCountInv X x0 q := by
          exact productiveInvolvingStageDeadlineStop_iter_inv
            h3 X x0 (properStageScale x0) (D / 2)
            (properStageTarget D n) (properInvolvingTarget x0)
            T (c0, 0) q hq0 hpq
        by_cases hhalf : HasPairwiseGap q.1 X (D / 2)
        · by_cases hk : properInvolvingTarget x0 ≤ q.2
          · simp [htarget, hhalf, hk]
          · have hklt : q.2 < properInvolvingTarget x0 := by omega
            have hbounds :=
              productiveInvolvingCountInv_bounds_before_target
                X x0 q hInv hklt
            have hlive :
                ProductiveProperStageLive X (properStageScale x0) (D / 2)
                  (properStageTarget D n) (properInvolvingTarget x0) q :=
              ⟨hhalf, hbounds.2, htarget, hklt⟩
            simp [htarget, hhalf, hk, hlive]
        · rw [if_pos htarget, if_pos hhalf]
          exact
            (le_add_right le_rfl).trans
              (le_add_right le_rfl)
    · simp [htarget]
  have hraw :
      (∑' q : Config m n × ℕ,
        if ¬ HasPairwiseGap q.1 X (properStageTarget D n)
        then p q else 0) ≤
      (∑' q : Config m n × ℕ,
        if ¬ HasPairwiseGap q.1 X (D / 2) then p q else 0) +
        (∑' q : Config m n × ℕ,
          if ¬ HasPairwiseGap q.1 X (properStageTarget D n) ∧
              properInvolvingTarget x0 ≤ q.2
          then p q else 0) +
        ∑' q : Config m n × ℕ,
          if ProductiveProperStageLive X (properStageScale x0) (D / 2)
              (properStageTarget D n) (properInvolvingTarget x0) q
          then p q else 0 := by
    calc
      (∑' q : Config m n × ℕ,
        if ¬ HasPairwiseGap q.1 X (properStageTarget D n)
        then p q else 0) ≤
          ∑' q : Config m n × ℕ,
            ((if ¬ HasPairwiseGap q.1 X (D / 2) then p q else 0) +
              (if ¬ HasPairwiseGap q.1 X (properStageTarget D n) ∧
                  properInvolvingTarget x0 ≤ q.2
                then p q else 0) +
              if ProductiveProperStageLive X (properStageScale x0) (D / 2)
                  (properStageTarget D n) (properInvolvingTarget x0) q
                then p q else 0) :=
        ENNReal.tsum_le_tsum hpoint
      _ = _ := by
        rw [ENNReal.tsum_add, ENNReal.tsum_add]
  have htargetMap :=
    globalPairGapFailureMass_map_fst p X (properStageTarget D n)
  have hhalfMap :=
    globalPairGapFailureMass_map_fst p X (D / 2)
  change globalInvolvingPairGapFailureMass p X
      (properStageTarget D n) ≤
    globalInvolvingPairGapFailureMass p X (D / 2) +
      globalProperTargetFailureMass p X
        (properStageTarget D n) (properInvolvingTarget x0) +
      _ at hraw
  rw [← htargetMap, ← hhalfMap] at hraw
  simpa only [globalProperTargetFailureMass] using hraw

/-- One full proper stage reaches the capped `49D/48` target except for the
three explicit completion errors. -/
theorem productiveProperStage_progress
    (h3 : 3 ≤ n) (X : Species m)
    (D x0 : ℕ) (hD4 : 4 ≤ D) (hDx0 : D ≤ x0)
    (c0 : Config m n) (hx0 : count c0 X = x0)
    (hinit : HasPairwiseGap c0 X D) :
    let p :=
      iter
        (productiveInvolvingStageDeadlineStop h3 X
          (properStageScale x0) (D / 2) (properStageTarget D n)
          (properInvolvingTarget x0))
        (2 * n) (c0, 0)
    globalPairGapFailureMass (p.map Prod.fst)
        X (properStageTarget D n) ≤
      (m : ℝ≥0∞) *
          ENNReal.ofReal
            (Real.exp (-((D : ℝ) ^ 2 / (18 * (n : ℝ))))) +
        (m : ℝ≥0∞) *
          ENNReal.ofReal
            (Real.exp (-((D : ℝ) ^ 2 / (82944 * (x0 : ℝ))))) +
        ENNReal.ofReal (Real.exp (-(x0 : ℝ) / 8)) := by
  classical
  dsimp only
  let p :=
    iter
      (productiveInvolvingStageDeadlineStop h3 X
        (properStageScale x0) (D / 2) (properStageTarget D n)
        (properInvolvingTarget x0))
      (2 * n) (c0, 0)
  have hx0n : x0 ≤ n := by
    rw [← hx0]
    have htotal := count_add_zSum c0 X
    omega
  have hDn : D ≤ n := hDx0.trans hx0n
  have hdecomp :=
    productiveProperStage_failure_decomposition
      h3 X D x0 (2 * n) c0 hx0
  have ha :=
    productiveProperStage_completion_a
      h3 X D x0 hD4 hDn c0 hinit
  have hc :=
    productiveInvolvingStageDeadlineStop_global_capped_exp_tail
      h3 X D x0 (2 * n) hD4 hDx0 hDn c0 hinit
  have hb :=
    productiveProperStage_completion_b
      h3 X D x0 hD4 c0 hx0
  simpa only [p] using
    hdecomp.trans (add_le_add (add_le_add ha hc) hb)

end Tri.Multi

#print axioms Tri.Multi.productiveProperStage_failure_decomposition
#print axioms Tri.Multi.productiveProperStage_progress
