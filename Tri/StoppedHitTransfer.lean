/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.BellmanDomination
import Tri.Compose
import Tri.EscapeSplit

/-!
# Generic stopped-band domination

This file transfers a live-band first-order stochastic domination statement
from stopped Bellman hit values to terminal failure mass.  It is independent
of the Byzantine model and of Paper Lemma 6.
-/

namespace Tri

open scoped ENNReal BigOperators

noncomputable section

variable {α : Type*}

/-- Live-only version of the stopped Bellman comparison.  Domination is
consulted only before either boundary has been reached. -/
theorem stoppedReferenceHit_le_of_live_stochDom
    [Preorder α]
    (Bad Good : α → Prop) [DecidablePred Bad] [DecidablePred Good]
    (Kref Kdom : α → PMF α)
    (hBadLower : ∀ ⦃i j : α⦄, i ≤ j → Bad j → Bad i)
    (hGoodUpper : ∀ ⦃i j : α⦄, i ≤ j → Good i → Good j)
    (hmono : ∀ f : α → ℝ≥0∞, Monotone f →
      Monotone fun i => expect (Kref i) f)
    (hdom : ∀ i, ¬ Bad i → ¬ Good i →
      ∀ f : α → ℝ≥0∞, Monotone f →
        expect (Kref i) f ≤ expect (Kdom i) f) :
    ∀ T i,
      stoppedReferenceHit Bad Good Kref T i ≤
        stoppedReferenceHit Bad Good Kdom T i := by
  intro T
  induction T with
  | zero =>
      intro i
      simp [stoppedReferenceHit]
  | succ T ih =>
      intro i
      by_cases hG : Good i
      · simp [stoppedReferenceHit, hG]
      · by_cases hB : Bad i
        · simp [stoppedReferenceHit, hG, hB]
        · simp only [stoppedReferenceHit, if_neg hG, if_neg hB]
          calc
            expect (Kref i) (stoppedReferenceHit Bad Good Kref T) ≤
                expect (Kdom i) (stoppedReferenceHit Bad Good Kref T) :=
              hdom i hB hG
                (stoppedReferenceHit Bad Good Kref T)
                (stoppedReferenceHit_mono Bad Good Kref
                  hBadLower hGoodUpper hmono T)
            _ ≤ expect (Kdom i)
                (stoppedReferenceHit Bad Good Kdom T) := by
              unfold expect
              exact ENNReal.tsum_le_tsum fun a =>
                mul_le_mul_left' (ih a) _

/-- The stopped hit probability and the terminal mass outside `Good` in the
`Bad ∨ Good`-frozen chain partition total mass.  If `Bad` and `Good` overlap,
`Good` wins, exactly as in `stoppedReferenceHit`. -/
theorem stoppedReferenceHit_add_terminalFailureMass
    (Bad Good : α → Prop) [DecidablePred Bad] [DecidablePred Good]
    (K : α → PMF α) :
    ∀ T i,
      stoppedReferenceHit Bad Good K T i +
          terminalFailureMass
            (iter (freeze (fun x => Bad x ∨ Good x) K) T i)
            Good =
        1 := by
  intro T
  induction T with
  | zero =>
      intro i
      unfold stoppedReferenceHit ind
      simp only [iter_zero, terminalFailureMass_pure]
      by_cases hG : Good i <;> simp [hG]
  | succ T ih =>
      intro i
      by_cases hG : Good i
      · have hstop : Bad i ∨ Good i := Or.inr hG
        have hiter :
            iter (freeze (fun x => Bad x ∨ Good x) K) (T + 1) i =
              PMF.pure i :=
          iter_targetFreeze_of_mem
            (fun x => Bad x ∨ Good x) K i hstop (T + 1)
        rw [hiter, terminalFailureMass_pure]
        simp [stoppedReferenceHit, hG]
      · by_cases hB : Bad i
        · have hstop : Bad i ∨ Good i := Or.inl hB
          have hiter :
              iter (freeze (fun x => Bad x ∨ Good x) K) (T + 1) i =
                PMF.pure i :=
            iter_targetFreeze_of_mem
              (fun x => Bad x ∨ Good x) K i hstop (T + 1)
          rw [hiter, terminalFailureMass_pure]
          simp [stoppedReferenceHit, hG, hB]
        · have hstop : ¬ (Bad i ∨ Good i) := by
            simp [hB, hG]
          rw [iter_succ, freeze_of_not_mem i hstop,
            terminalFailureMass_bind]
          simp only [stoppedReferenceHit, if_neg hG, if_neg hB]
          unfold expect
          rw [← ENNReal.tsum_add]
          calc
            (∑' a,
                (K i a * stoppedReferenceHit Bad Good K T a +
                  K i a *
                    terminalFailureMass
                      (iter (freeze (fun x => Bad x ∨ Good x) K) T a)
                      Good))
                = ∑' a,
                    K i a *
                      (stoppedReferenceHit Bad Good K T a +
                        terminalFailureMass
                          (iter (freeze (fun x => Bad x ∨ Good x) K) T a)
                          Good) := by
                apply tsum_congr
                intro a
                rw [mul_add]
            _ = ∑' a, K i a * 1 := by
                apply tsum_congr
                intro a
                rw [ih a]
            _ = 1 := by
                rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- First-order stochastic domination on the live band transfers to the
terminal failure mass of the chain stopped on both boundaries. -/
theorem stoppedBand_failure_le_of_live_stochDom
    [Preorder α]
    (Bad Good : α → Prop) [DecidablePred Bad] [DecidablePred Good]
    (Kref Kdom : α → PMF α)
    (hBadLower : ∀ ⦃i j : α⦄, i ≤ j → Bad j → Bad i)
    (hGoodUpper : ∀ ⦃i j : α⦄, i ≤ j → Good i → Good j)
    (hmono : ∀ f : α → ℝ≥0∞, Monotone f →
      Monotone fun i => expect (Kref i) f)
    (hdom : ∀ i, ¬ Bad i → ¬ Good i →
      ∀ f : α → ℝ≥0∞, Monotone f →
        expect (Kref i) f ≤ expect (Kdom i) f)
    (T : ℕ) (i : α) :
    terminalFailureMass
        (iter (freeze (fun x => Bad x ∨ Good x) Kdom) T i)
        Good ≤
      terminalFailureMass
        (iter (freeze (fun x => Bad x ∨ Good x) Kref) T i)
        Good := by
  have hhit :=
    stoppedReferenceHit_le_of_live_stochDom
      Bad Good Kref Kdom hBadLower hGoodUpper hmono hdom T i
  have hrefPart :=
    stoppedReferenceHit_add_terminalFailureMass Bad Good Kref T i
  have hdomPart :=
    stoppedReferenceHit_add_terminalFailureMass Bad Good Kdom T i
  have hrefTop : stoppedReferenceHit Bad Good Kref T i ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top
      (stoppedReferenceHit_le_one Bad Good Kref T i)
  have hsum :
      terminalFailureMass
          (iter (freeze (fun x => Bad x ∨ Good x) Kdom) T i)
          Good +
          stoppedReferenceHit Bad Good Kref T i ≤
        terminalFailureMass
          (iter (freeze (fun x => Bad x ∨ Good x) Kref) T i)
          Good +
          stoppedReferenceHit Bad Good Kref T i := by
    calc
      terminalFailureMass
            (iter (freeze (fun x => Bad x ∨ Good x) Kdom) T i)
            Good +
          stoppedReferenceHit Bad Good Kref T i =
        stoppedReferenceHit Bad Good Kref T i +
          terminalFailureMass
            (iter (freeze (fun x => Bad x ∨ Good x) Kdom) T i)
            Good := add_comm _ _
      _ ≤ stoppedReferenceHit Bad Good Kdom T i +
          terminalFailureMass
            (iter (freeze (fun x => Bad x ∨ Good x) Kdom) T i)
            Good :=
        -- add the same term on the right; `add_le_add_right` adds on the LEFT
        -- in this ordered-monoid context, so use `gcongr`.
        by gcongr
      _ = 1 := hdomPart
      _ = stoppedReferenceHit Bad Good Kref T i +
          terminalFailureMass
            (iter (freeze (fun x => Bad x ∨ Good x) Kref) T i)
            Good := hrefPart.symm
      _ = terminalFailureMass
            (iter (freeze (fun x => Bad x ∨ Good x) Kref) T i)
            Good +
          stoppedReferenceHit Bad Good Kref T i := add_comm _ _
  exact (ENNReal.add_le_add_iff_right hrefTop).mp hsum

/-- Allowing the process to continue after a lower-band exit can only help it
hit the upper target.  Equivalently, target-only failure is at most
lower-and-target-stopped failure. -/
theorem targetFailure_le_stoppedBandFailure
    (Bad Good : α → Prop) [DecidablePred Bad] [DecidablePred Good]
    (K : α → PMF α) :
    ∀ T i,
      terminalFailureMass (iter (freeze Good K) T i) Good ≤
        terminalFailureMass
          (iter (freeze (fun x => Bad x ∨ Good x) K) T i)
          Good := by
  intro T
  induction T with
  | zero =>
      intro i
      rfl
  | succ T ih =>
      intro i
      by_cases hG : Good i
      · have hstop : Bad i ∨ Good i := Or.inr hG
        have hleft :
            iter (freeze Good K) (T + 1) i = PMF.pure i :=
          iter_targetFreeze_of_mem Good K i hG (T + 1)
        have hright :
            iter (freeze (fun x => Bad x ∨ Good x) K) (T + 1) i =
              PMF.pure i :=
          iter_targetFreeze_of_mem
            (fun x => Bad x ∨ Good x) K i hstop (T + 1)
        -- both sides collapse to the same point mass; `simpa` would finish with
        -- `assumption`, but the residual goal is `x ≤ x`.
        simp only [hleft, hright]
        exact le_rfl
      · by_cases hB : Bad i
        · have hstop : Bad i ∨ Good i := Or.inl hB
          have hright :
              iter (freeze (fun x => Bad x ∨ Good x) K) (T + 1) i =
                PMF.pure i :=
            iter_targetFreeze_of_mem
              (fun x => Bad x ∨ Good x) K i hstop (T + 1)
          calc
            terminalFailureMass
                (iter (freeze Good K) (T + 1) i) Good ≤ 1 :=
              terminalFailureMass_le_one _ Good
            _ = terminalFailureMass
                (iter (freeze (fun x => Bad x ∨ Good x) K) (T + 1) i)
                Good := by
              rw [hright, terminalFailureMass_pure, if_neg hG]
        · have hstop : ¬ (Bad i ∨ Good i) := by
            simp [hB, hG]
          rw [iter_succ, iter_succ,
            freeze_of_not_mem i hG,
            freeze_of_not_mem i hstop,
            terminalFailureMass_bind, terminalFailureMass_bind]
          unfold expect
          exact ENNReal.tsum_le_tsum fun a =>
            mul_le_mul_left' (ih a) _

/-- Direct `Reaches` wrapper for a target-frozen dominated kernel. -/
theorem reaches_targetFreeze_of_live_stochDom
    [Preorder α]
    (Bad Good P : α → Prop)
    [DecidablePred Bad] [DecidablePred Good]
    (Kref Kdom : α → PMF α)
    (hBadLower : ∀ ⦃i j : α⦄, i ≤ j → Bad j → Bad i)
    (hGoodUpper : ∀ ⦃i j : α⦄, i ≤ j → Good i → Good j)
    (hmono : ∀ f : α → ℝ≥0∞, Monotone f →
      Monotone fun i => expect (Kref i) f)
    (hdom : ∀ i, ¬ Bad i → ¬ Good i →
      ∀ f : α → ℝ≥0∞, Monotone f →
        expect (Kref i) f ≤ expect (Kdom i) f)
    (T : ℕ) (ε : ℝ≥0∞)
    (href : ∀ s, P s →
      terminalFailureMass
          (iter (freeze (fun x => Bad x ∨ Good x) Kref) T s)
          Good ≤ ε) :
    Reaches (freeze Good Kdom) T P Good ε := by
  intro s hs
  change terminalFailureMass (iter (freeze Good Kdom) T s) Good ≤ ε
  exact
    (targetFailure_le_stoppedBandFailure Bad Good Kdom T s).trans
      ((stoppedBand_failure_le_of_live_stochDom
          Bad Good Kref Kdom hBadLower hGoodUpper hmono hdom T s).trans
        (href s hs))

end

end Tri
