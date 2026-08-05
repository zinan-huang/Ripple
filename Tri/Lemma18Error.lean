/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Lemma17Error
import Tri.Lemma18PaperStage

/-!
# A uniform error envelope for the decisive Lemma 18 stage

The epidemic, two immutable-label, all-active-count, and guarded-direction
terms are all bounded by the same urn-scale exponential.
-/

namespace Tri

open scoped ENNReal

noncomputable section

/-- The five decisive-stage errors fit under the immutable-label urn error
when the mean and direction exponents meet their cross-multiplied budgets. -/
theorem lemma18StageError_le
    (a q cStar r D : ℕ)
    (hcStar : 0 < cStar)
    (hr : 0 < r)
    (hqa : q ≤ a)
    (hactive : 15 * q ≤ 4 * cStar * r)
    (hdirection :
      15 * q * cStar * r ≤ 49 * D ^ 2) :
    lemma18StageError q q a cStar r D ≤
      5 * lemma16UrnError q := by
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
  have hcStarR : (0 : ℝ) < (cStar : ℝ) := by
    exact_mod_cast hcStar
  have hrR : (0 : ℝ) < (r : ℝ) := by
    exact_mod_cast hr
  have hdirectionR :
      (15 : ℝ) * (q : ℝ) *
          (cStar : ℝ) * (r : ℝ) ≤
        49 * (D : ℝ) ^ 2 := by
    exact_mod_cast hdirection
  have hdirectionRate :
      (3 : ℝ) / 16 * (q : ℝ) ≤
        ((7 * D : ℕ) : ℝ) ^ 2 /
          (8 * ((10 * cStar * r : ℕ) : ℝ)) := by
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
            (-(((7 * D : ℕ) : ℝ) ^ 2 /
              (8 *
                ((10 * cStar * r : ℕ) : ℝ))))) ≤
        lemma16UrnError q := by
    unfold lemma16UrnError
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    linarith
  unfold lemma18StageError
  calc
    ENNReal.ofReal (Real.exp (-(a : ℝ))) +
          lemma16UrnError q +
          lemma16UrnError q +
          ENNReal.ofReal
            (Real.exp
              (-(((cStar * r : ℕ) : ℝ) / 20))) +
          ENNReal.ofReal
            (Real.exp
              (-(((7 * D : ℕ) : ℝ) ^ 2 /
                (8 *
                  ((10 * cStar * r : ℕ) : ℝ)))))
      ≤
        lemma16UrnError q + lemma16UrnError q +
          lemma16UrnError q + lemma16UrnError q +
          lemma16UrnError q :=
      add_le_add
        (add_le_add
          (add_le_add
            (add_le_add hclock le_rfl)
            le_rfl)
          hactiveErr)
        hdirectionErr
    _ = 5 * lemma16UrnError q := by ring

end

end Tri

#print axioms Tri.lemma18StageError_le
