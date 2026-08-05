/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.SameHorizon

/-!
# Finite-horizon event unions

A first hit by time `T` is contained in the union of the ordinary-chain
terminal events at times `0, ..., T`.  This elementary union bound is useful
when every fixed-time marginal has a sharper estimate than one common
maximal potential.
-/

namespace Tri

open scoped ENNReal

noncomputable section

/-- Expectation commutes with a finite sum of nonnegative functions. -/
theorem expect_finset_sum
    {α ι : Type*}
    (p : PMF α) (s : Finset ι)
    (f : ι → α → ℝ≥0∞) :
    expect p (fun z => ∑ i ∈ s, f i z) =
      ∑ i ∈ s, expect p (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [expect]
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      unfold expect at ih ⊢
      simp_rw [mul_add]
      rw [ENNReal.tsum_add, ih]

/-- The probability of a first hit by time `T` is at most the sum of the
ordinary terminal masses of the target at times `0, ..., T`. -/
theorem hitProb_le_sum_terminalEventMass
    {α : Type*}
    (B : α → Prop) [DecidablePred B]
    (K : α → PMF α) (T : ℕ) (s : α) :
    hitProb B K T s ≤
      ∑ j ∈ Finset.range (T + 1),
        terminalFailureMass
          (iter K j s) (fun z => ¬ B z) := by
  induction T generalizing s with
  | zero =>
      unfold hitProb
      rw [show iter (freeze B K) 0 s = PMF.pure s by rfl,
        expect_pure]
      rw [show Finset.range (0 + 1) = {0} by decide]
      simp [ind, terminalFailureMass_pure, iter]
  | succ T ih =>
      by_cases hs : B s
      · rw [hitProb_eq_one_of_mem B K (T + 1) s hs]
        have hzero :
            terminalFailureMass
                (iter K 0 s) (fun z => ¬ B z) =
              1 := by
          simp [iter, terminalFailureMass_pure, hs]
        calc
          (1 : ℝ≥0∞) =
              terminalFailureMass
                (iter K 0 s) (fun z => ¬ B z) := hzero.symm
          _ ≤
              ∑ j ∈ Finset.range (T + 1 + 1),
                terminalFailureMass
                  (iter K j s) (fun z => ¬ B z) := by
            apply Finset.single_le_sum
              (s := Finset.range (T + 1 + 1))
              (f := fun j =>
                terminalFailureMass
                  (iter K j s) (fun z => ¬ B z))
            · intro i hi
              exact bot_le
            · simp
      · rw [hitProb_succ_of_not B K T s hs]
        calc
          (∑' x, K s x * hitProb B K T x)
              ≤
            ∑' x, K s x *
              (∑ j ∈ Finset.range (T + 1),
                terminalFailureMass
                  (iter K j x) (fun z => ¬ B z)) := by
                exact ENNReal.tsum_le_tsum fun x =>
                  mul_le_mul_left' (ih x) _
          _ =
            expect (K s)
              (fun x =>
                ∑ j ∈ Finset.range (T + 1),
                  terminalFailureMass
                    (iter K j x) (fun z => ¬ B z)) := by
              rfl
          _ =
            ∑ j ∈ Finset.range (T + 1),
              expect (K s)
                (fun x =>
                  terminalFailureMass
                    (iter K j x) (fun z => ¬ B z)) :=
              expect_finset_sum
                (K s) (Finset.range (T + 1))
                (fun j x =>
                  terminalFailureMass
                    (iter K j x) (fun z => ¬ B z))
          _ =
            ∑ j ∈ Finset.range (T + 1),
              terminalFailureMass
                (iter K (j + 1) s) (fun z => ¬ B z) := by
              apply Finset.sum_congr rfl
              intro j hj
              rw [iter_succ, terminalFailureMass_bind]
          _ =
            ∑ j ∈ Finset.range (T + 1 + 1),
              terminalFailureMass
                (iter K j s) (fun z => ¬ B z) := by
              conv_rhs =>
                rw [Finset.sum_range_succ']
              have hzero :
                  terminalFailureMass
                      (iter K 0 s) (fun z => ¬ B z) =
                    0 := by
                simp [iter, terminalFailureMass_pure, hs]
              rw [hzero, add_zero]

end

end Tri

#print axioms Tri.expect_finset_sum
#print axioms Tri.hitProb_le_sum_terminalEventMass
