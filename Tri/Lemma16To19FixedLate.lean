/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Lemma16To19FixedComplete

/-!
# Fixed late-activation clock and error parameters

The late clock is exactly twice the common exponent budget and the real error
scale is exactly three times it.  The remaining premises are the genuine
reserve, range, square, and label-scale conditions.
-/

namespace Tri

noncomputable section

/-- Exact late activation clock budget. -/
def lemma16To19FixedClockBudget
    (q : ℕ) : ℕ :=
  2 * q

/-- Exact real scale used by the final activation error. -/
def lemma16To19FixedErrorScale
    (q : ℕ) : ℝ :=
  3 * (q : ℝ)

/-- All late-stage hypotheses supplied by the exact clock and error choices. -/
structure Lemma16To19FixedLateFacts
    (n q Dlate Dlabel Mlate targetGap : ℕ) : Prop where
  hbudget :
    targetGap + Dlabel + 2 * Mlate ≤ 2 * Dlate
  hgap0 :
    0 < targetGap
  hgapn :
    targetGap < n
  hDlabel :
    0 < Dlabel
  hL :
    0 ≤ lemma16To19FixedErrorScale q
  hscale :
    lemma16To19FixedErrorScale q * (n : ℝ) ≤
      ((Dlabel : ℝ) / 2) ^ 2
  hbudgetLower :
    2 * q ≤ lemma16To19FixedClockBudget q
  hbudgetUpper :
    lemma16To19FixedClockBudget q ≤ 2 * q
  herrorL :
    3 * (q : ℝ) ≤ lemma16To19FixedErrorScale q
  hgapSq :
    q * n ≤ targetGap ^ 2
  hM :
    lemma3Quarter targetGap ≤ Mlate

/-- The exact choices discharge every formal clock and real-scale comparison. -/
theorem lemma16To19FixedLateFacts
    (n q Dlate Dlabel Mlate targetGap : ℕ)
    (hbudget :
      targetGap + Dlabel + 2 * Mlate ≤ 2 * Dlate)
    (hgap0 : 0 < targetGap)
    (hgapn : targetGap < n)
    (hDlabel : 0 < Dlabel)
    (hscale :
      lemma16To19FixedErrorScale q * (n : ℝ) ≤
        ((Dlabel : ℝ) / 2) ^ 2)
    (hgapSq :
      q * n ≤ targetGap ^ 2)
    (hM :
      lemma3Quarter targetGap ≤ Mlate) :
    Lemma16To19FixedLateFacts
      n q Dlate Dlabel Mlate targetGap :=
  { hbudget := hbudget
    hgap0 := hgap0
    hgapn := hgapn
    hDlabel := hDlabel
    hL := by
      unfold lemma16To19FixedErrorScale
      positivity
    hscale := hscale
    hbudgetLower := by
      rfl
    hbudgetUpper := by
      rfl
    herrorL := by
      rfl
    hgapSq := hgapSq
    hM := hM }

end

end Tri

#print axioms Tri.lemma16To19FixedLateFacts
