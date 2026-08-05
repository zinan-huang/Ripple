/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.MultiProductiveClockConstants

/-!
# Paper Lemma 13: the phase-0 raw-interaction clock

The paper separates two statements about a phase-0 stage:

* Lemma 12 bounds how many productive reactions suffice.
* Lemma 13 shows that those productive reactions occur within `Theta(m n)`
  physical interactions.

The theorem below is the second statement.  It is uniform in the initial
phase-0 configuration and gives explicit constants and failure exponent.
-/

namespace Tri.Multi

open scoped ENNReal

variable {m n : ℕ}

/-- Paper Lemma 13 with an explicit raw horizon and exponential error.

If the stage leaves its phase-0 live region, the stopped chain has completed
the stage and is not counted as a clock failure.  Otherwise, after
`129472 * m * n` physical interactions, even the larger event that the
productive counter is at most `288 * n` has mass at most
`exp (-(gamma * log₂ n))`. -/
theorem lemma13_phase0_rawDeadline
    (h3 : 3 ≤ n) (X : Species m) (D gamma : ℕ)
    (_hgamma : 1 ≤ gamma)
    (hD : 3 * D ≤ n)
    (hscale : 6 ≤ gamma * Nat.log 2 n)
    (hm : m * (gamma * Nat.log 2 n) ≤ n)
    (c0 : Config m n)
    (hmax : IsMaxSpecies c0 X)
    (hphase0 : count c0 X ≤ zSum c0 X + D) :
    (∑' q, if q.2 ≤ 288 * n ∧
          ¬ PaperPhase0ClockBoundary X D q then
        iter (multiPaperPhase0ClockStop h3 X D)
          (129472 * m * n) (c0, 0) q
      else 0) ≤
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
  have hq0 :
      ¬ PaperPhase0ClockBoundary X D (c0, 0) := by
    simp only [PaperPhase0ClockBoundary, not_not]
    exact ⟨hmax, hphase0⟩
  have hclock :=
    multiPaperPhase0ClockStop_productivity_deadline
      h3 X D hD h6m (288 * n) n (c0, 0) hq0 rfl
  have hHorizon :
      multiPaperPhase0ClockHorizon m (288 * n) n =
        129472 * m * n := by
    simp only [multiPaperPhase0ClockHorizon, multiPhase0ClockHorizon]
    ring
  rw [hHorizon] at hclock
  exact hclock.trans <| ENNReal.ofReal_le_ofReal <|
    Real.exp_le_exp.mpr <| by
      have hlogR :
          ((gamma * Nat.log 2 n : ℕ) : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast hlog
      linarith

end Tri.Multi

#print axioms Tri.Multi.lemma13_phase0_rawDeadline
