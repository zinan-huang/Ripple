/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.ByzantineKernel

/-!
# Finite-horizon transfer for adaptive Byzantine strategies

The one-step adverse envelope is uniform over the complete past. This file
iterates such uniform potential bounds through the genuinely
history-dependent law, without claiming a law-level coupling.
-/

namespace Tri.Byzantine

open scoped ENNReal

variable {n B : ℕ}

theorem expect_adaptiveEventStep_after
    (σ : Strategy n B) (hist : History n B)
    (s : State n B) (h3 : 3 ≤ n)
    (V : State n B → ℝ≥0∞) :
    expect (adaptiveEventStep σ hist s h3)
        (fun e => V e.after) =
      expect (adaptiveStep σ hist s h3) V := by
  calc
    expect (adaptiveEventStep σ hist s h3)
        (fun e => V e.after) =
        expect
          ((adaptiveEventStep σ hist s h3).map Record.after) V :=
      (expect_map
        (adaptiveEventStep σ hist s h3) Record.after V).symm
    _ = expect (adaptiveStep σ hist s h3) V := by
      rw [adaptiveEventStep_map_after]

/-- A history-uniform one-step contraction iterates through the complete
adaptive transcript. -/
theorem controlledLaw_expect_le_pow
    (σ : Strategy n B) (h3 : 3 ≤ n)
    (V : State n B → ℝ≥0∞) (c : ℝ≥0∞)
    (hstep : ∀ hist s,
      expect (adaptiveStep σ hist s h3) V ≤ c * V s) :
    ∀ T hist s,
      expect (controlledLaw σ h3 T hist s) V ≤
        c ^ T * V s := by
  intro T
  induction T with
  | zero =>
      intro hist s
      simp [controlledLaw]
  | succ T ih =>
      intro hist s
      rw [controlledLaw, expect_bind']
      calc
        (∑' e,
            adaptiveEventStep σ hist s h3 e *
              expect
                (controlledLaw σ h3 T (e :: hist) e.after) V) ≤
          ∑' e,
            adaptiveEventStep σ hist s h3 e *
              (c ^ T * V e.after) := by
            exact ENNReal.tsum_le_tsum fun e =>
              mul_le_mul_right (ih (e :: hist) e.after) _
        _ = c ^ T *
            ∑' e,
              adaptiveEventStep σ hist s h3 e * V e.after := by
            rw [← ENNReal.tsum_mul_left]
            congr 1
            ext e
            ring
        _ = c ^ T * expect (adaptiveStep σ hist s h3) V := by
            congr 1
            change
              expect (adaptiveEventStep σ hist s h3)
                  (fun e => V e.after) =
                expect (adaptiveStep σ hist s h3) V
            exact expect_adaptiveEventStep_after σ hist s h3 V
        _ ≤ c ^ T * (c * V s) :=
          mul_le_mul_right (hstep hist s) _
        _ = c ^ (T + 1) * V s := by
          ring

/-- Any antitone `X`-potential contracting under the paper's adverse fixed
response contracts at the same rate under every history-dependent response. -/
theorem controlledLaw_antitone_expect_le_pow
    (h3 : 3 ≤ n)
    (V : ℕ → ℝ≥0∞) (hV : Antitone V)
    (c : ℝ≥0∞)
    (hworst : ∀ s : State n B,
      expect (step Control.worst s h3)
          (fun t => V (State.x t)) ≤
        c * V (State.x s)) :
    ∀ σ : Strategy n B, ∀ T hist s,
      expect (controlledLaw σ h3 T hist s)
          (fun t => V (State.x t)) ≤
        c ^ T * V (State.x s) := by
  intro σ
  apply controlledLaw_expect_le_pow σ h3
    (fun t => V (State.x t)) c
  intro hist s
  exact
    (adaptiveStep_expect_x_le_worst
      σ hist s h3 V hV).trans
        (hworst s)

theorem controlledLaw_antitone_super
    (h3 : 3 ≤ n)
    (V : ℕ → ℝ≥0∞) (hV : Antitone V)
    (hworst : ∀ s : State n B,
      expect (step Control.worst s h3)
          (fun t => V (State.x t)) ≤
        V (State.x s)) :
    ∀ σ : Strategy n B, ∀ T hist s,
      expect (controlledLaw σ h3 T hist s)
          (fun t => V (State.x t)) ≤
        V (State.x s) := by
  intro σ T hist s
  have h :=
    controlledLaw_antitone_expect_le_pow
      h3 V hV 1
      (fun q => by simpa using hworst q)
      σ T hist s
  simpa using h

end Tri.Byzantine

#print axioms Tri.Byzantine.expect_adaptiveEventStep_after
#print axioms Tri.Byzantine.controlledLaw_expect_le_pow
#print axioms Tri.Byzantine.controlledLaw_antitone_expect_le_pow
#print axioms Tri.Byzantine.controlledLaw_antitone_super
