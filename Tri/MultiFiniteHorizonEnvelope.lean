/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.BinaryMonotone
import Tri.MultiBinaryEnvelope

/-!
# Finite-horizon binary envelope for the multi-species process

The exact one-step aggregate law and stochastic monotonicity of the binary
kernel combine by induction over `PMF.bind`.  Thus every increasing terminal
observable of the ordinary binary chain is dominated by the corresponding
observable of the distinguished count in the physical multi-species chain.
-/

namespace Tri.Multi

open scoped ENNReal

variable {m n : ℕ}

/-- The ordinary fixed-population binary chain is a one-step lower envelope
for the distinguished count in the physical multi-species process. -/
theorem triChain_expect_le_multiStep_count
    (c : Config m n) (X : Species m) (h3 : 3 ≤ n)
    (F : ℕ → ℝ≥0∞) (hF : Monotone F) :
    expect (Tri.triChain n (count c X)) F ≤
      expect ((multiStep c h3).map (fun d => count d X)) F := by
  have hpopulation := count_add_zSum c X
  have hcount : count c X ≤ n := by
    omega
  have hkernel :
      Tri.triChain n (count c X) =
        Tri.triStep (count c X) (zSum c X)
          (by simpa [count_add_zSum c X] using h3) := by
    unfold Tri.triChain
    rw [dif_pos ⟨h3, hcount⟩]
    congr 1
    omega
  rw [hkernel]
  exact triStep_expect_le_multiStep_count c X h3 F hF

/-- Finite-horizon stochastic domination of the ordinary binary chain by the
distinguished count in the physical multi-species chain. -/
theorem triChain_iter_expect_le_multiStep_iter_count
    (c : Config m n) (X : Species m) (h3 : 3 ≤ n)
    (T : ℕ) (F : ℕ → ℝ≥0∞) (hF : Monotone F) :
    expect (iter (Tri.triChain n) T (count c X)) F ≤
      expect (iter (fun d : Config m n => multiStep d h3) T c)
        (fun d => F (count d X)) := by
  induction T generalizing c with
  | zero =>
      simp [iter]
  | succ t ih =>
      rw [iter_succ, iter_succ, expect_bind, expect_bind]
      let G : ℕ → ℝ≥0∞ :=
        fun x => expect (iter (Tri.triChain n) t x) F
      have hG : Monotone G :=
        Tri.triChain_iter_expect_monotone n t F hF
      calc
        ∑' a, Tri.triChain n (count c X) a *
              expect (iter (Tri.triChain n) t a) F =
            expect (Tri.triChain n (count c X)) G := by
              rfl
        _ ≤ expect ((multiStep c h3).map (fun d => count d X)) G :=
          triChain_expect_le_multiStep_count c X h3 G hG
        _ = expect (multiStep c h3) (fun d => G (count d X)) := by
          rw [expect_map]
        _ ≤ ∑' d, multiStep c h3 d *
              expect
                (iter (fun q : Config m n => multiStep q h3) t d)
                (fun q => F (count q X)) := by
          unfold expect
          exact ENNReal.tsum_le_tsum fun d => by
            gcongr
            exact ih d

/-- Mapped-law form of the finite-horizon envelope. -/
theorem triChain_iter_expect_le_multiStep_iter_map_count
    (c : Config m n) (X : Species m) (h3 : 3 ≤ n)
    (T : ℕ) (F : ℕ → ℝ≥0∞) (hF : Monotone F) :
    expect (iter (Tri.triChain n) T (count c X)) F ≤
      expect
        ((iter (fun d : Config m n => multiStep d h3) T c).map
          (fun d => count d X)) F := by
  rw [expect_map]
  exact triChain_iter_expect_le_multiStep_iter_count c X h3 T F hF

/-- Indicators of upper sets are increasing. -/
theorem monotone_upperIndicator (k : ℕ) :
    Monotone (Tri.ind fun x : ℕ => k ≤ x) := by
  intro x y hxy
  unfold Tri.ind
  by_cases hx : k ≤ x
  · have hy : k ≤ y := hx.trans hxy
    simp [hx, hy]
  · simp [hx]

/-- Direct upper-tail form of the finite-horizon envelope. -/
theorem triChain_iter_upperTail_le_multiStep_iter_count
    (c : Config m n) (X : Species m) (h3 : 3 ≤ n)
    (T k : ℕ) :
    (∑' x, if k ≤ x then iter (Tri.triChain n) T (count c X) x else 0) ≤
      ∑' d, if k ≤ count d X then
        iter (fun q : Config m n => multiStep q h3) T c d else 0 := by
  simpa [expect, Tri.ind] using
    triChain_iter_expect_le_multiStep_iter_count c X h3 T
      (Tri.ind fun x : ℕ => k ≤ x) (monotone_upperIndicator k)

end Tri.Multi

#print axioms Tri.Multi.triChain_expect_le_multiStep_count
#print axioms Tri.Multi.triChain_iter_expect_le_multiStep_iter_count
#print axioms Tri.Multi.triChain_iter_expect_le_multiStep_iter_map_count
#print axioms Tri.Multi.triChain_iter_upperTail_le_multiStep_iter_count
