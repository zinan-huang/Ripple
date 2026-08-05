/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Lemma17PhysicalStage

/-!
# A uniform error envelope for one Lemma 17 stage

The epidemic, label, all-active-count, and direction errors are each bounded
by the slowest label exponent under explicit cross-multiplied scale
conditions.
-/

namespace Tri

open scoped ENNReal

noncomputable section

/-- The four paper-stage error terms are all bounded by the immutable-label
urn error under transparent cross-multiplied scale conditions. -/
theorem lemma17StageError_le
    (a q cStar rho r : ℕ)
    (hr : 0 < r)
    (hqa : q ≤ a)
    (hactive : 15 * q ≤ 4 * cStar * r)
    (hdirection : 3 * q * r ≤
      4 * cStar * rho ^ 2) :
    lemma17StageError a q cStar rho r ≤
      4 * lemma16UrnError q := by
  have hq0 : (0 : ℝ) ≤ (q : ℝ) := by
    positivity
  have hclockRate :
      (3 : ℝ) / 16 * (q : ℝ) ≤ (a : ℝ) := by
    have hqaR : (q : ℝ) ≤ (a : ℝ) := by
      exact_mod_cast hqa
    nlinarith
  have hactiveR :
      (15 : ℝ) * (q : ℝ) ≤
        4 * (cStar : ℝ) * (r : ℝ) := by
    exact_mod_cast hactive
  have hactiveRate :
      (3 : ℝ) / 16 * (q : ℝ) ≤
        ((cStar * r : ℕ) : ℝ) / 20 := by
    push_cast
    nlinarith
  have hrR : (0 : ℝ) < (r : ℝ) := by
    exact_mod_cast hr
  have hdirectionR :
      (3 : ℝ) * (q : ℝ) * (r : ℝ) ≤
        4 * (cStar : ℝ) * (rho : ℝ) ^ 2 := by
    exact_mod_cast hdirection
  have hdirectionRate :
      (3 : ℝ) / 16 * (q : ℝ) ≤
        ((2 * cStar * rho : ℕ) : ℝ) ^ 2 /
          (8 * ((2 * (cStar * r) : ℕ) : ℝ)) := by
    push_cast
    field_simp
    nlinarith
  have hclock :
      ENNReal.ofReal (Real.exp (-(a : ℝ))) ≤
        lemma16UrnError q := by
    unfold lemma16UrnError
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    linarith
  have hactiveErr :
      ENNReal.ofReal
          (Real.exp
            (-(((cStar * r : ℕ) : ℝ) / 20))) ≤
        lemma16UrnError q := by
    unfold lemma16UrnError
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    linarith
  have hdirectionErr :
      ENNReal.ofReal
          (Real.exp
            (-(((2 * cStar * rho : ℕ) : ℝ) ^ 2 /
              (8 *
                ((2 * (cStar * r) : ℕ) : ℝ))))) ≤
        lemma16UrnError q := by
    unfold lemma16UrnError
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    linarith
  unfold lemma17StageError
  calc
    ENNReal.ofReal (Real.exp (-(a : ℝ))) +
          lemma16UrnError q +
          ENNReal.ofReal
            (Real.exp
              (-(((cStar * r : ℕ) : ℝ) / 20))) +
          ENNReal.ofReal
            (Real.exp
              (-(((2 * cStar * rho : ℕ) : ℝ) ^ 2 /
                (8 *
                  ((2 * (cStar * r) : ℕ) : ℝ)))))
      ≤ lemma16UrnError q + lemma16UrnError q +
          lemma16UrnError q + lemma16UrnError q :=
      add_le_add
        (add_le_add
          (add_le_add hclock le_rfl)
          hactiveErr)
        hdirectionErr
    _ = 4 * lemma16UrnError q := by ring

end

end Tri

#print axioms Tri.lemma17StageError_le
