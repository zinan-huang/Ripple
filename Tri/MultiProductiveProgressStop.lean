/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.MultiProductiveProgressStep

/-!
# Stopped productive progress for a fixed competitor

The full-state process is frozen when the global half-gap invariant fails or
the fixed competitor reaches its target gap.  The relevant-event counter
remains part of the Markov state.
-/

namespace Tri.Multi

open scoped BigOperators ENNReal

variable {m n : ℕ}

/-- Productive relevant-event kernel stopped at the safety or success
boundary. -/
noncomputable def productivePairProgressStop
    (h3 : 3 ≤ n) (X Y : Species m) (d target : ℕ) :
    Config m n × ℕ → PMF (Config m n × ℕ) := by
  classical
  exact fun q =>
    if HasPairwiseGap q.1 X d ∧ pairGapNat q.1 X Y < target then
      productivePairRelevantCount h3 X Y q
    else
      PMF.pure q

/-- The joint progress potential remains a supermartingale after stopping at
the global half-gap and fixed-pair target boundaries. -/
theorem productivePairProgressStop_conserve
    (h3 : 3 ≤ n) (X Y : Species m) (hXY : X ≠ Y)
    (d target : ℕ) (hd2 : 2 ≤ d) (hdn : d ≤ n)
    (q : Config m n × ℕ) :
    expect (productivePairProgressStop h3 X Y d target q)
        (pairProgressPotential X Y
          (pairProgressTilt n d) (pairProgressFactor n d)) ≤
      pairProgressPotential X Y
        (pairProgressTilt n d) (pairProgressFactor n d) q := by
  classical
  unfold productivePairProgressStop
  split_ifs with hlive
  · exact productivePairRelevantCount_progress_conserve
      q.1 h3 X Y hXY q.2 d hd2 hdn hlive.1
  · simp only [expect_pure]
    exact le_rfl

/-- Finite-time mass that has accumulated at least `K` relevant fixed-pair
jumps without reaching `target`.  This is the rigorous four-jump replacement
for the paper's Bernoulli-success argument. -/
theorem productivePairProgressStop_relevant_tail
    (h3 : 3 ≤ n) (X Y : Species m) (hXY : X ≠ Y)
    (d target K T : ℕ) (hd2 : 2 ≤ d) (hdn : d ≤ n)
    (htarget : 1 ≤ target)
    (q0 : Config m n × ℕ) :
    (∑' q : Config m n × ℕ,
      if pairGapNat q.1 X Y < target ∧ K ≤ q.2 then
        iter (productivePairProgressStop h3 X Y d target) T q0 q
      else 0) ≤
      pairProgressPotential X Y
          (pairProgressTilt n d) (pairProgressFactor n d) q0 /
        (pairProgressTilt n d ^ (target - 1) *
          (pairProgressFactor n d)⁻¹ ^ K) := by
  let w := pairProgressTilt n d
  let φ := pairProgressFactor n d
  let V : Config m n × ℕ → ℝ≥0∞ :=
    pairProgressPotential X Y w φ
  let Bad : Config m n × ℕ → Prop := fun q =>
    pairGapNat q.1 X Y < target ∧ K ≤ q.2
  let θ : ℝ≥0∞ := w ^ (target - 1) * (φ⁻¹) ^ K
  have hn : 0 < n := by omega
  have hw1 : w ≤ 1 := by
    dsimp only [w]
    exact pairProgressTilt_le_one n d hn
  have hw0 : w ≠ 0 := by
    dsimp only [w]
    exact pairProgressTilt_ne_zero n d hn
  have hwtop : w ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top hw1
  have hφ1 : φ ≤ 1 := by
    dsimp only [φ]
    exact pairProgressFactor_le_one n d hn
  have hφ0 : φ ≠ 0 := by
    dsimp only [φ]
    exact pairProgressFactor_ne_zero n d hn
  have hφtop : φ ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top hφ1
  have hinv1 : 1 ≤ φ⁻¹ := ENNReal.one_le_inv.mpr hφ1
  have hinv0 : φ⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr hφtop
  have hinvtop : φ⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr hφ0
  have hθ0 : θ ≠ 0 := by
    dsimp only [θ]
    exact mul_ne_zero (pow_ne_zero _ hw0) (pow_ne_zero _ hinv0)
  have hθtop : θ ≠ ∞ := by
    dsimp only [θ]
    exact ENNReal.mul_ne_top
      (ENNReal.pow_ne_top hwtop) (ENNReal.pow_ne_top hinvtop)
  have hstep :
      ∀ q, expect (productivePairProgressStop h3 X Y d target q) V ≤
        V q := by
    intro q
    dsimp only [V]
    exact productivePairProgressStop_conserve
      h3 X Y hXY d target hd2 hdn q
  have hbad : ∀ q, Bad q → θ ≤ V q := by
    intro q hq
    have hgapExp : pairGapNat q.1 X Y ≤ target - 1 := by
      dsimp only [Bad] at hq
      omega
    dsimp only [θ, V, pairProgressPotential]
    exact mul_le_mul'
      (pow_le_pow_right_of_le_one' hw1 hgapExp)
      (pow_le_pow_right₀ hinv1 hq.2)
  simpa only [Bad, V, θ, w, φ] using
    Tri.stopped_bad_mass_le
      (productivePairProgressStop h3 X Y d target)
      V Bad θ hθ0 hθtop hstep hbad T q0

end Tri.Multi

#print axioms Tri.Multi.productivePairProgressStop_conserve
#print axioms Tri.Multi.productivePairProgressStop_relevant_tail
