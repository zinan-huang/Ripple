/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Lemma16To19CorrectedError

/-!
# Error envelope for the fixed-landing route

The custom landing occupies the last Lemma 17 error slot.  The otherwise
unused next value of the scale family is set to the fixed target, so the
existing corrected decisive-stage error theorem applies literally.
-/

namespace Tri

open scoped ENNReal

noncomputable section

theorem lemma16To19FixedError_le_final
    (n mPred m19 q cStar targetA D r18 clockBudget
      Mlate targetGap : ℕ)
    (scale17 rho17 rStage scale19 r19 M19 :
      ℕ → ℕ)
    (L : ℝ)
    (hscaleTarget :
      scale17 (mPred + 1) = targetA)
    (hcStar : 0 < cStar)
    (hr17 : ∀ j < mPred + 1, 0 < rStage j)
    (hqa17 : ∀ j < mPred + 1, q ≤ scale17 j)
    (hactive17 :
      ∀ j < mPred + 1,
        15 * q ≤ 4 * cStar * rStage j)
    (hdirection17 :
      ∀ j < mPred + 1,
        3 * q * rStage j ≤
          4 * cStar * (rho17 j) ^ 2)
    (hr18 : 0 < r18)
    (hqa18 : q ≤ targetA)
    (hactive18 :
      15 * q ≤ 4 * cStar * r18)
    (hdirection18 :
      15 * q * cStar * r18 ≤ 49 * D ^ 2)
    (hr19 : ∀ j < m19, 0 < r19 j)
    (hqa19 : ∀ j < m19, q ≤ scale19 j)
    (hactive19 :
      ∀ j < m19,
        15 * q ≤ 4 * cStar * r19 j)
    (hdirection19 :
      ∀ j < m19,
        3 * q * cStar * r19 j ≤ (M19 j) ^ 2)
    (hq : 1 ≤ q)
    (hlog3 : 3 ≤ Nat.log 2 n)
    (hlogq : Nat.log 2 n ≤ q)
    (hbudget : 2 * q ≤ clockBudget)
    (hL : 3 * (q : ℝ) ≤ L)
    (hgap0 : 0 < targetGap)
    (hgapn : targetGap < n)
    (hgapSq : q * n ≤ targetGap ^ 2)
    (hM : lemma3Quarter targetGap ≤ Mlate)
    (hm : mPred + m19 + 2 ≤ q)
    (hqLarge : 8192 ≤ q) :
    ((3 * lemma16UrnError q +
            ∑ j ∈ Finset.range (mPred + 1),
              (lemma17StageError
                  (scale17 j) q cStar
                  (rho17 j) (rStage j) +
                lemma16UrnError q)) +
          lemma16UrnError q) +
        ((((lemma18StageError
                q q targetA cStar r18 D +
              lemma16UrnError q) +
            ∑ j ∈ Finset.range m19,
              (lemma19StageError
                  (scale19 j) q cStar
                  (r19 j) (M19 j) +
                lemma16UrnError q)) +
          lemma16UrnError q) +
        lemma19FullActivationPositiveGapUniformError
          n clockBudget Mlate targetGap L)
      ≤ infectionActivationFinalError q := by
  have h :=
    lemma16To19CorrectedError_le_final
      n (mPred + 1) m19 q cStar D r18 clockBudget
      Mlate targetGap scale17 rho17 rStage
      scale19 r19 M19 L hcStar
      hr17 hqa17 hactive17 hdirection17
      hr18 (by simpa [hscaleTarget] using hqa18)
      hactive18 hdirection18
      hr19 hqa19 hactive19 hdirection19
      hq hlog3 hlogq hbudget hL
      hgap0 hgapn hgapSq hM (by omega) hqLarge
  simpa [hscaleTarget] using h

end

end Tri

#print axioms Tri.lemma16To19FixedError_le_final
