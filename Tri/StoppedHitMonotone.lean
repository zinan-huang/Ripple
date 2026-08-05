/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.StoppedHitTransfer

/-!
# Monotonicity of stopped hitting failures

Enlarging the upper success set decreases failure, and increasing the initial
state decreases failure for a monotone one-step kernel between a lower bad set
and an upper good set.
-/

namespace Tri

open scoped ENNReal

variable {α : Type*}

theorem stoppedReferenceHit_mono_good
    (Bad Good More : α → Prop)
    [DecidablePred Bad] [DecidablePred Good] [DecidablePred More]
    (K : α → PMF α)
    (hGood : ∀ x, Good x → More x) :
    ∀ T x,
      stoppedReferenceHit Bad Good K T x ≤
        stoppedReferenceHit Bad More K T x := by
  intro T
  induction T with
  | zero =>
      intro x
      unfold stoppedReferenceHit ind
      by_cases hG : Good x
      · have hM := hGood x hG
        simp [hG, hM]
      · by_cases hM : More x <;> simp [hG, hM]
  | succ T ih =>
      intro x
      by_cases hM : More x
      · simp only [stoppedReferenceHit, if_pos hM]
        exact stoppedReferenceHit_le_one Bad Good K (T + 1) x
      · have hG : ¬ Good x := fun hx => hM (hGood x hx)
        by_cases hB : Bad x
        · simp [stoppedReferenceHit, hG, hM, hB]
        · simp only [stoppedReferenceHit, if_neg hG, if_neg hM, if_neg hB]
          unfold expect
          exact ENNReal.tsum_le_tsum fun y =>
            mul_le_mul_right (ih y) _

theorem stoppedBand_failure_mono_good
    (Bad Good More : α → Prop)
    [DecidablePred Bad] [DecidablePred Good] [DecidablePred More]
    (K : α → PMF α)
    (hGood : ∀ x, Good x → More x)
    (T : ℕ) (x : α) :
    terminalFailureMass
        (iter (freeze (fun y => Bad y ∨ More y) K) T x)
        More ≤
      terminalFailureMass
        (iter (freeze (fun y => Bad y ∨ Good y) K) T x)
        Good := by
  have hhit :=
    stoppedReferenceHit_mono_good Bad Good More K hGood T x
  have hsmall :=
    stoppedReferenceHit_add_terminalFailureMass Bad Good K T x
  have hlarge :=
    stoppedReferenceHit_add_terminalFailureMass Bad More K T x
  have htop :
      stoppedReferenceHit Bad Good K T x ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top
      (stoppedReferenceHit_le_one Bad Good K T x)
  apply (ENNReal.add_le_add_iff_right htop).mp
  calc
    terminalFailureMass
          (iter (freeze (fun y => Bad y ∨ More y) K) T x)
          More +
        stoppedReferenceHit Bad Good K T x ≤
      stoppedReferenceHit Bad More K T x +
        terminalFailureMass
          (iter (freeze (fun y => Bad y ∨ More y) K) T x)
          More := by
            rw [add_comm]
            gcongr
    _ = 1 := hlarge
    _ = stoppedReferenceHit Bad Good K T x +
        terminalFailureMass
          (iter (freeze (fun y => Bad y ∨ Good y) K) T x)
          Good := hsmall.symm
    _ = terminalFailureMass
          (iter (freeze (fun y => Bad y ∨ Good y) K) T x)
          Good +
        stoppedReferenceHit Bad Good K T x := add_comm _ _

/-- Enlarging the target of a target-frozen chain decreases terminal
failure. -/
theorem targetFreeze_failure_mono_good
    (Good More : α → Prop)
    [DecidablePred Good] [DecidablePred More]
    (K : α → PMF α)
    (hGood : ∀ x, Good x → More x)
    (T : ℕ) (x : α) :
    terminalFailureMass
        (iter (freeze More K) T x)
        More ≤
      terminalFailureMass
        (iter (freeze Good K) T x)
        Good := by
  have hraw :=
    stoppedBand_failure_mono_good
      (fun _ : α => False) Good More K hGood T x
  have hfreezeGood :
      freeze (fun y : α => False ∨ Good y) K =
        freeze Good K := by
    funext y
    unfold freeze
    by_cases hy : Good y
    · rw [if_pos (Or.inr hy), if_pos hy]
    · rw [if_neg (by simpa using hy), if_neg hy]
  have hfreezeMore :
      freeze (fun y : α => False ∨ More y) K =
        freeze More K := by
    funext y
    unfold freeze
    by_cases hy : More y
    · rw [if_pos (Or.inr hy), if_pos hy]
    · rw [if_neg (by simpa using hy), if_neg hy]
  rwa [hfreezeGood, hfreezeMore] at hraw

theorem stoppedBand_failure_antitone_start
    [Preorder α]
    (Bad Good : α → Prop)
    [DecidablePred Bad] [DecidablePred Good]
    (K : α → PMF α)
    (hBadLower : ∀ ⦃i j : α⦄, i ≤ j → Bad j → Bad i)
    (hGoodUpper : ∀ ⦃i j : α⦄, i ≤ j → Good i → Good j)
    (hmono : ∀ f : α → ℝ≥0∞, Monotone f →
      Monotone fun i => expect (K i) f)
    (T : ℕ) ⦃i j : α⦄ (hij : i ≤ j) :
    terminalFailureMass
        (iter (freeze (fun x => Bad x ∨ Good x) K) T j)
        Good ≤
      terminalFailureMass
        (iter (freeze (fun x => Bad x ∨ Good x) K) T i)
        Good := by
  have hhit :=
    stoppedReferenceHit_mono
      Bad Good K hBadLower hGoodUpper hmono T hij
  have hi :=
    stoppedReferenceHit_add_terminalFailureMass Bad Good K T i
  have hj :=
    stoppedReferenceHit_add_terminalFailureMass Bad Good K T j
  have htop :
      stoppedReferenceHit Bad Good K T i ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top
      (stoppedReferenceHit_le_one Bad Good K T i)
  apply (ENNReal.add_le_add_iff_right htop).mp
  calc
    terminalFailureMass
          (iter (freeze (fun x => Bad x ∨ Good x) K) T j)
          Good +
        stoppedReferenceHit Bad Good K T i ≤
      stoppedReferenceHit Bad Good K T j +
        terminalFailureMass
          (iter (freeze (fun x => Bad x ∨ Good x) K) T j)
          Good := by
            rw [add_comm]
            gcongr
    _ = 1 := hj
    _ = stoppedReferenceHit Bad Good K T i +
        terminalFailureMass
          (iter (freeze (fun x => Bad x ∨ Good x) K) T i)
          Good := hi.symm
    _ = terminalFailureMass
          (iter (freeze (fun x => Bad x ∨ Good x) K) T i)
          Good +
        stoppedReferenceHit Bad Good K T i := add_comm _ _

/-- The controlled Bellman hit value is the ordinary stopped hit value on the
joint history/state space. -/
theorem stoppedControlledHit_eq_jointReferenceHit
    {H : Type*}
    (Bad Good : α → Prop)
    [DecidablePred Bad] [DecidablePred Good]
    (K : H → α → PMF (H × α)) :
    ∀ T hist x,
      stoppedControlledHit Bad Good K T hist x =
        stoppedReferenceHit
          (fun q : H × α => Bad q.2)
          (fun q : H × α => Good q.2)
          (fun q => K q.1 q.2)
          T (hist, x) := by
  intro T
  induction T with
  | zero =>
      intro hist x
      unfold stoppedControlledHit stoppedReferenceHit ind
      rfl
  | succ T ih =>
      intro hist x
      by_cases hG : Good x
      · simp [stoppedControlledHit, stoppedReferenceHit, hG]
      · by_cases hB : Bad x
        · simp [stoppedControlledHit, stoppedReferenceHit, hG, hB]
        · simp only [stoppedControlledHit, stoppedReferenceHit,
            if_neg hG, if_neg hB]
          congr 1
          funext q
          exact ih q.1 q.2

/-- Controlled stopped hitting and terminal joint failure partition total
mass exactly. -/
theorem stoppedControlledHit_add_terminalFailureMass
    {H : Type*}
    (Bad Good : α → Prop)
    [DecidablePred Bad] [DecidablePred Good]
    (K : H → α → PMF (H × α))
    (T : ℕ) (hist : H) (x : α) :
    stoppedControlledHit Bad Good K T hist x +
        terminalFailureMass
          (iter
            (freeze
              (fun q : H × α => Bad q.2 ∨ Good q.2)
              (fun q => K q.1 q.2))
            T (hist, x))
          (fun q => Good q.2) =
      1 := by
  rw [stoppedControlledHit_eq_jointReferenceHit]
  exact stoppedReferenceHit_add_terminalFailureMass
    (fun q : H × α => Bad q.2)
    (fun q : H × α => Good q.2)
    (fun q => K q.1 q.2)
    T (hist, x)

/-- First-order domination of every history-dependent controlled step
transfers to joint stopped-band terminal failure. -/
theorem stoppedControlledBand_failure_le_reference
    {H : Type*} [Preorder α]
    (Bad Good : α → Prop)
    [DecidablePred Bad] [DecidablePred Good]
    (Kref : α → PMF α)
    (Kctl : H → α → PMF (H × α))
    (hBadLower : ∀ ⦃i j : α⦄, i ≤ j → Bad j → Bad i)
    (hGoodUpper : ∀ ⦃i j : α⦄, i ≤ j → Good i → Good j)
    (hmono : ∀ f : α → ℝ≥0∞, Monotone f →
      Monotone fun i => expect (Kref i) f)
    (hdom : ∀ hist i (f : α → ℝ≥0∞), Monotone f →
      expect (Kref i) f ≤
        expect (Kctl hist i) (fun q => f q.2))
    (T : ℕ) (hist : H) (i : α) :
    terminalFailureMass
        (iter
          (freeze
            (fun q : H × α => Bad q.2 ∨ Good q.2)
            (fun q => Kctl q.1 q.2))
          T (hist, i))
        (fun q => Good q.2) ≤
      terminalFailureMass
        (iter
          (freeze (fun x => Bad x ∨ Good x) Kref)
          T i)
        Good := by
  have hhit :=
    hitProb_ge_reference_of_kernel_stochDom
      Bad Good Kref Kctl hBadLower hGoodUpper
      hmono hdom T hist i
  have hrefPart :=
    stoppedReferenceHit_add_terminalFailureMass
      Bad Good Kref T i
  have hctlPart :=
    stoppedControlledHit_add_terminalFailureMass
      Bad Good Kctl T hist i
  have hrefTop :
      stoppedReferenceHit Bad Good Kref T i ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top
      (stoppedReferenceHit_le_one Bad Good Kref T i)
  apply (ENNReal.add_le_add_iff_right hrefTop).mp
  calc
    terminalFailureMass
          (iter
            (freeze
              (fun q : H × α => Bad q.2 ∨ Good q.2)
              (fun q => Kctl q.1 q.2))
            T (hist, i))
          (fun q => Good q.2) +
        stoppedReferenceHit Bad Good Kref T i ≤
      stoppedControlledHit Bad Good Kctl T hist i +
        terminalFailureMass
          (iter
            (freeze
              (fun q : H × α => Bad q.2 ∨ Good q.2)
              (fun q => Kctl q.1 q.2))
            T (hist, i))
          (fun q => Good q.2) := by
      rw [add_comm]
      gcongr
    _ = 1 := hctlPart
    _ = stoppedReferenceHit Bad Good Kref T i +
        terminalFailureMass
          (iter
            (freeze (fun x => Bad x ∨ Good x) Kref)
            T i)
          Good := hrefPart.symm
    _ = terminalFailureMass
          (iter
            (freeze (fun x => Bad x ∨ Good x) Kref)
            T i)
          Good +
        stoppedReferenceHit Bad Good Kref T i := add_comm _ _

end Tri

#print axioms Tri.stoppedReferenceHit_mono_good
#print axioms Tri.stoppedBand_failure_mono_good
#print axioms Tri.targetFreeze_failure_mono_good
#print axioms Tri.stoppedBand_failure_antitone_start
#print axioms Tri.stoppedControlledHit_eq_jointReferenceHit
#print axioms Tri.stoppedControlledHit_add_terminalFailureMass
#print axioms Tri.stoppedControlledBand_failure_le_reference
