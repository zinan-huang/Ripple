/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Phase3Feller

/-!
# Phase 3 raw-interaction completion

**This file does NOT close paper Corollary 3.**  The paper's Corollary 3 is a
*productive-clock* statement:

> *Corollary 3.* Since phase 3 starts with `y ≤ γ lg n ≤ n/6` it completes
> properly, within at most `3 γ lg n` **productive** reaction events, with
> probability at least `1 − exp(−Θ(γ lg n))`.

What is proved here is the *raw-interaction* completion of phase 3, i.e. the
composition of paper Corollary 3 with paper Lemma 5(iii) (`Θ(γ n lg n)`
interaction events), and only from the repo's **buffered** entry region
`Phase3Entry n γ`, which is `2 y ≤ γ lg n` — half of the paper's `y ≤ γ lg n`.

So `phase3_raw_completion` is:
* *stronger* than Corollary 3 in its clock (raw interactions, not productive
  events), and
* *weaker* than Corollary 3 in its start region (a factor 2 in the minority
  count).

The reconciled phase-3 development proves reachability from `Phase3Entry n γ`
to all-`X` consensus with the canonical `(n, γ)`-only error, and separately
bounds that error by the budget slice `2 · n⁻¹ ^ γ`.  The only work in this
file is rewriting that budget into the printed exponential shape
`2 exp (-(γ log n))` (the base of the logarithm only changes the constant
hidden by `Ω`).  No new probabilistic content is introduced.
-/

namespace Tri

open scoped ENNReal

/-- `n⁻¹ ^ γ` in `ℝ≥0∞` is literally `exp (-(γ log n))`. -/
theorem inv_rpow_eq_ofReal_exp_neg
    {n : ℕ} (hn : 0 < n) (γ : ℕ) :
    (n : ℝ≥0∞)⁻¹ ^ ((1 : ℝ) * (γ : ℝ)) =
      ENNReal.ofReal (Real.exp (-((γ : ℝ) * Real.log (n : ℝ)))) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hinv : (0 : ℝ) < (n : ℝ)⁻¹ := inv_pos.mpr hnR
  have hcast : (n : ℝ≥0∞)⁻¹ = ENNReal.ofReal ((n : ℝ)⁻¹) := by
    rw [ENNReal.ofReal_inv_of_pos hnR, ENNReal.ofReal_natCast]
  rw [one_mul, hcast, ENNReal.ofReal_rpow_of_pos hinv]
  congr 1
  rw [Real.rpow_def_of_pos hinv, Real.log_inv]
  congr 1
  ring

/-- **Phase-3 raw-interaction completion** (paper Corollary 3 composed with
paper Lemma 5(iii), on the buffered entry region).  From `Phase3Entry n γ`
(i.e. `2 y ≤ γ lg n`), the scaled horizon `phase3HorizonScaled 16 n γ =
16 γ n lg n` *interaction* events reach all-`X` consensus `IsXMajority n`
except with mass `2 exp (-(γ log n))`, the paper's printed `exp(-Ω(γ lg n))`.

This is NOT paper Corollary 3: that claim is on the productive clock
(`3 γ lg n` productive events) and starts from the wider region `y ≤ γ lg n`. -/
theorem phase3_raw_completion
    (n γ : ℕ) (h3 : 3 ≤ n) (hγ : 1 ≤ γ)
    (hsize : 6 * γ * Nat.log 2 n ≤ n)
    (hlog8 : 8 ≤ Nat.log 2 n) :
    Reaches (triChain n) (phase3HorizonScaled 16 n γ)
      (Phase3Entry n γ) (IsXMajority n)
      ((2 : ℝ≥0∞) *
        ENNReal.ofReal
          (Real.exp (-((γ : ℝ) * Real.log (n : ℝ))))) := by
  intro s hs
  refine le_trans (phase3_reaches_scaled_canonical n γ h3 hγ hsize s hs) ?_
  refine le_trans (canonicalPhase3Error_le_two_inverse n γ h3 hγ hsize hlog8) ?_
  rw [inv_rpow_eq_ofReal_exp_neg (by omega : 0 < n) γ]

end Tri

#print axioms Tri.inv_rpow_eq_ofReal_exp_neg
#print axioms Tri.phase3_raw_completion
