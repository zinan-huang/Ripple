/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Lemma16To19FixedLanding
import Tri.Lemma16To19FixedHeadline

/-!
# Complete fixed-landing activation route

The semantic fixed-landing theorem is specialized to one common error
parameter and fed directly to the fixed raw-clock and final-error headline.
-/

namespace Tri

open scoped ENNReal

noncomputable section

theorem lemma16_to_19_fixed_landing_coarse_headline_complete
    (n q a16 k16 u16 nu R B rho16 cStar
      mPred DLadder kLadder uLadder rhoLanding
      F H kGap uGap rhoPrefix rhoEnd Ddec r18
      m19 Dlate Dlabel Mlate targetGapLate
      clockBudget : ℕ)
    (scale17 rho17 rStage : ℕ → ℕ)
    (scale19 targetGap19 rho19 r19 M19 : ℕ → ℕ)
    (L : ℝ)
    (h3 : 3 ≤ n)
    (hlarge :
      theorem6FixedCStarSq *
          (theorem6FixedCStarSq + 6) ≤ n)
    (hlog : Nat.log 2 n ≤ q)
    (hquarter16 : 4 * a16 ≤ n)
    (hcStar16 : 640 ≤ cStar)
    (hroot16 : a16 ^ 5 * q * n ≤ n ^ 5)
    (hqa16 : q * a16 ≤ rho16 ^ 2)
    (hqaOrder16 : q ≤ a16)
    (hrho16 : 1 ≤ rho16)
    (hnu : nu + 1 = n)
    (hk16 : k16 + 1 = a16)
    (hu16 : u16 + k16 + 1 = nu)
    (hRB : R + B = nu)
    (hmajor0 : R ≤ B)
    (hk16pos : 0 < k16)
    (hscale17_0 : scale17 0 = a16)
    (hrho17_0 : rho17 0 = rho16)
    (hcStar : 128 ≤ cStar)
    (hcTwo : 2 ≤ cStar)
    (hdouble17 :
      ∀ j < mPred,
        scale17 (j + 1) = 2 * scale17 j)
    (hroot17 :
      ∀ j < mPred,
        19 * rho17 j ≤ 14 * rho17 (j + 1))
    (ha17 :
      ∀ j < mPred, 4 ≤ scale17 j)
    (hquarter17 :
      ∀ j < mPred, 4 * scale17 j ≤ n)
    (htarget17 :
      ∀ j < mPred, 2 * scale17 j ≤ n)
    (hrho17 :
      ∀ j < mPred, 1 ≤ rho17 j)
    (hbias17 :
      ∀ j < mPred,
        38 * cStar * rho17 j ≤ scale17 j)
    (hactiveScale17 :
      ∀ j < mPred,
        76 * cStar * rStage j ≤ scale17 j)
    (hmean17 :
      ∀ j < mPred,
        (2 * scale17 j) ^ 3 ≤
          rStage j * n ^ 2)
    (hqa17 :
      ∀ j < mPred,
        q * (scale17 j + 1) ≤
          (rho17 j) ^ 2)
    (hlabelRoom17 :
      ∀ j < mPred,
        5 * (scale17 j + 1) ≤ n + 1)
    (hLadderBR :
      B + R = uLadder + kLadder + 1)
    (hLadderGap :
      R + DLadder ≤ B)
    (hkLadder : 0 < kLadder)
    (hLadderQa :
      q * (kLadder + 1) ≤ DLadder ^ 2)
    (hLadderQuarter :
      4 * (kLadder + 1) ≤ B + R + 1)
    (hLadderClock :
      ∀ j < mPred,
        scale17 j + 1 ≤ 1 + kLadder)
    (hLadderClockFinal :
      scale17 mPred + 1 ≤ 1 + kLadder)
    (haPred : 4 ≤ scale17 mPred)
    (hbelow :
      theorem6FixedCStarSq * scale17 mPred < n)
    (habove :
      n ≤ theorem6FixedCStarSq * (2 * scale17 mPred))
    (hrhoPred : 1 ≤ rho17 mPred)
    (hrootLanding :
      19 * rho17 mPred ≤ 14 * rhoLanding)
    (hbiasPred :
      38 * cStar * rho17 mPred ≤ scale17 mPred)
    (hactiveScaleLanding :
      76 * cStar * rStage mPred ≤ scale17 mPred)
    (hmeanLanding :
      (theorem6FixedCriticalScale n) ^ 3 ≤
        rStage mPred * n ^ 2)
    (hqaLanding :
      q * (scale17 mPred + 1) ≤
        (rho17 mPred) ^ 2)
    (hGapBR :
      B + R = uGap + kGap + 1)
    (hInitialGap :
      R + (F + H) ≤ B)
    (hGapShrink :
      (60 * theorem6FixedPoolMultiplier * Ddec) *
          (B + R) ≤
        H * (uGap + 1))
    (hkGap : 0 < kGap)
    (hGapQa :
      q * (kGap + 1) ≤ F ^ 2)
    (hGapQuarter :
      4 * (kGap + 1) ≤ B + R + 1)
    (hGapClock :
      theorem6FixedCriticalScale n + 1 ≤
        1 + kGap)
    (ha18 : 4 ≤ theorem6FixedCriticalScale n)
    (hquarterClock18 :
      4 * theorem6FixedCriticalScale n ≤ n)
    (hstageRoom18 :
      2 * theorem6FixedCriticalScale n + 4 ≤ n)
    (hpriorRadius :
      cStar * rhoLanding ≤ Ddec)
    (hprefixRadius :
      rhoPrefix + 1 = Ddec)
    (hendRadius :
      rhoEnd + 1 = 12 * Ddec)
    (hprefixQa :
      q * (theorem6FixedCriticalScale n + 1) ≤
        rhoPrefix ^ 2)
    (hendQa :
      q * (theorem6FixedCriticalScale n + 1) ≤
        rhoEnd ^ 2)
    (hmajorQa :
      q * (theorem6FixedCriticalScale n + 2) ≤
        (60 * theorem6FixedPoolMultiplier * Ddec) ^ 2)
    (hlabelRoom18 :
      5 * theorem6FixedCriticalScale n + 8 ≤ n)
    (hmeanActive18 :
      (2 * theorem6FixedCriticalScale n) ^ 3 ≤
        r18 * n ^ 2)
    (hguardScale :
      60 * Ddec ≤ theorem6FixedCriticalScale n)
    (hreactionScale :
      1200 * cStar * r18 ≤
        7 * theorem6FixedCriticalScale n)
    (hscale19_0 :
      scale19 0 = 2 * theorem6FixedCriticalScale n)
    (hgap19_0 :
      targetGap19 0 = 2 * Ddec)
    (hdouble19 :
      ∀ j < m19,
        scale19 (j + 1) = 2 * scale19 j)
    (ha19 :
      ∀ j < m19, 4 ≤ scale19 j)
    (hquarter19 :
      ∀ j < m19, 4 * scale19 j ≤ n)
    (htarget19 :
      ∀ j < m19, 2 * scale19 j ≤ n)
    (hmean19 :
      ∀ j < m19,
        (2 * scale19 j) ^ 3 ≤
          r19 j * n ^ 2)
    (hqa19 :
      ∀ j < m19,
        q * (scale19 j + 1) ≤
          (rho19 j) ^ 2)
    (hlabelRoom19 :
      ∀ j < m19,
        5 * (scale19 j + 1) ≤ n + 1)
    (hbudget19 :
      ∀ j < m19,
        targetGap19 (j + 1) + (rho19 j + 1) +
            2 * M19 j ≤ targetGap19 j)
    (hAfinal : 4 ≤ scale19 m19)
    (hstageRoomFinal : scale19 m19 + 4 ≤ n)
    (hquarterFinal : n ≤ 4 * scale19 m19)
    (hfinalGap :
      targetGap19 m19 = 2 * Dlate)
    (hscale19LeFinal :
      ∀ j ≤ m19,
        scale19 j ≤ scale19 m19)
    (hPostWindow :
      4 * scale19 m19 + 7 ≤
        n + 3 * theorem6FixedCriticalScale n)
    (hPostQaGlobal :
      q * (scale19 m19 + 2) ≤
        (60 * theorem6FixedPoolMultiplier * Ddec) ^ 2)
    (hbudgetLate :
      targetGapLate + Dlabel + 2 * Mlate ≤
        2 * Dlate)
    (hgapLate0 : 0 < targetGapLate)
    (hgapLaten : targetGapLate < n)
    (hDlabel : 0 < Dlabel)
    (hL : 0 ≤ L)
    (hscaleLate :
      L * (n : ℝ) ≤
        ((Dlabel : ℝ) / 2) ^ 2)
    (hscaleTarget :
      scale17 (mPred + 1) =
        theorem6FixedCriticalScale n)
    (herrorR17 :
      ∀ j < mPred + 1, 0 < rStage j)
    (herrorQa17 :
      ∀ j < mPred + 1, q ≤ scale17 j)
    (herrorActive17 :
      ∀ j < mPred + 1,
        15 * q ≤ 4 * cStar * rStage j)
    (herrorDirection17 :
      ∀ j < mPred + 1,
        3 * q * rStage j ≤
          4 * cStar * (rho17 j) ^ 2)
    (herrorR18 : 0 < r18)
    (herrorQa18 :
      q ≤ theorem6FixedCriticalScale n)
    (herrorActive18 :
      15 * q ≤ 4 * cStar * r18)
    (herrorDirection18 :
      15 * q * cStar * r18 ≤ 49 * Ddec ^ 2)
    (herrorR19 :
      ∀ j < m19, 0 < r19 j)
    (herrorQa19 :
      ∀ j < m19, q ≤ scale19 j)
    (herrorActive19 :
      ∀ j < m19,
        15 * q ≤ 4 * cStar * r19 j)
    (herrorDirection19 :
      ∀ j < m19,
        3 * q * cStar * r19 j ≤ (M19 j) ^ 2)
    (hq : 1 ≤ q)
    (hlog3 : 3 ≤ Nat.log 2 n)
    (hbudgetLower : 2 * q ≤ clockBudget)
    (hbudgetUpper : clockBudget ≤ 2 * q)
    (herrorL : 3 * (q : ℝ) ≤ L)
    (hgapSq : q * n ≤ targetGapLate ^ 2)
    (hM : lemma3Quarter targetGapLate ≤ Mlate)
    (hm : mPred + m19 + 2 ≤ q)
    (hqLarge : 8192 ≤ q)
    (s : InfectionRevealPhysicalState n)
    (hx0 : s.inactive.xIds.card = B)
    (hy0 : s.inactive.yIds.card = R) :
    terminalFailureMass
        (iter
          (freeze
            (InfectionActivationGapRangeGood
              n targetGapLate)
            (infectionStateStep n h3))
          ((2 * cStar + 8192) * q * n)
          (infectionRevealPhysicalForget s))
        (InfectionActivationGapRangeGood
          n targetGapLate)
      ≤ infectionActivationFinalError q := by
  have hclosed :=
    lemma16_to_19_fixed_landing_positive_gap_closed
      n q q q a16 k16 u16 nu R B rho16 cStar
      mPred DLadder kLadder uLadder rhoLanding
      q F H kGap uGap q q q rhoPrefix rhoEnd
      Ddec r18 q q m19 Dlate Dlabel Mlate
      targetGapLate clockBudget
      scale17 rho17 rStage
      scale19 targetGap19 rho19 r19 M19 L
      h3 hlarge hlog hquarter16 hcStar16
      hroot16 hqa16 hqaOrder16 hrho16
      hnu hk16 hu16 hRB hmajor0 hk16pos
      hscale17_0 hrho17_0 hcStar hcTwo
      hdouble17 hroot17 ha17 hquarter17
      htarget17 hrho17 hbias17 hactiveScale17
      hmean17 hqa17 hlabelRoom17
      hLadderBR hLadderGap hkLadder hLadderQa
      hLadderQuarter hLadderClock
      hLadderClockFinal haPred hbelow habove
      hrhoPred hrootLanding hbiasPred
      hactiveScaleLanding hmeanLanding hqaLanding
      hGapBR hInitialGap hGapShrink hkGap
      hGapQa hGapQuarter hGapClock
      ha18 hquarterClock18 hstageRoom18
      hpriorRadius hprefixRadius hendRadius
      hprefixQa hendQa hmajorQa hlabelRoom18
      hmeanActive18 hguardScale hreactionScale
      hscale19_0 hgap19_0 hdouble19 ha19
      hquarter19 htarget19 hmean19 hqa19
      hlabelRoom19 hbudget19 hAfinal
      hstageRoomFinal hquarterFinal hfinalGap
      hscale19LeFinal hPostWindow hPostQaGlobal
      hbudgetLate hgapLate0 hgapLaten hDlabel
      hL hscaleLate s hx0 hy0
  exact
    lemma16To19_fixed_coarse_headline_failure_le_final_of_closed
      n mPred m19 q k16 cStar
      (theorem6FixedCriticalScale n)
      (rho17 mPred) Ddec r18 clockBudget
      Mlate targetGapLate scale17 rho17 rStage
      scale19 r19 M19 L h3 s hclosed hscaleTarget
      (by omega) herrorR17 herrorQa17
      herrorActive17 herrorDirection17
      herrorR18 herrorQa18 herrorActive18
      herrorDirection18 herrorR19 herrorQa19
      herrorActive19 herrorDirection19
      hq hlog3 hlog hbudgetLower hbudgetUpper
      herrorL hgapLate0 hgapLaten hgapSq hM
      hm hqLarge

end

end Tri

#print axioms
  Tri.lemma16_to_19_fixed_landing_coarse_headline_complete
