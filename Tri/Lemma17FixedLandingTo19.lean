/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Lemma17FixedLandingTo18

/-!
# The fixed endpoint through Lemmas 18 and 19

The tight fixed endpoint has exactly the boundary type expected by the
existing corrected continuation.  A fixed pool multiplier discharges the
only endpoint-specific pool-scale obligation.
-/

namespace Tri

open scoped ENNReal

noncomputable section

theorem fixedEndpoint_then_lemma18_ladder_19_positive_gap_closed
    (n qPrefix qEnd q18Major rhoPrefix rhoEnd Ddec
      cStar rhoPrev r18
      qLadder qLadderMajor m
      Dlate Dlabel Mlate targetGapLate clockBudget : ℕ)
    (scale targetGap rhoL rL ML : ℕ → ℕ)
    (kPost uPost :
      InfectionRevealPhysicalState n → ℕ)
    (L : ℝ)
    (hn : 0 < n)
    (hlarge :
      theorem6FixedCStarSq *
          (theorem6FixedCStarSq + 6) ≤ n)
    (h3 : 3 ≤ n)
    (ha : 4 ≤ theorem6FixedCriticalScale n)
    (hquarterClock :
      4 * theorem6FixedCriticalScale n ≤ n)
    (hstageRoom :
      2 * theorem6FixedCriticalScale n + 4 ≤ n)
    (hcStar : 128 ≤ cStar)
    (hpriorRadius : cStar * rhoPrev ≤ Ddec)
    (hprefixRadius : rhoPrefix + 1 = Ddec)
    (hendRadius : rhoEnd + 1 = 12 * Ddec)
    (hprefixQa :
      qPrefix * (theorem6FixedCriticalScale n + 1) ≤
        rhoPrefix ^ 2)
    (hendQa :
      qEnd * (theorem6FixedCriticalScale n + 1) ≤
        rhoEnd ^ 2)
    (hmajorQa :
      q18Major * (theorem6FixedCriticalScale n + 2) ≤
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
    (hscale0 :
      scale 0 = 2 * theorem6FixedCriticalScale n)
    (hgap0 : targetGap 0 = 2 * Ddec)
    (hdouble :
      ∀ j < m, scale (j + 1) = 2 * scale j)
    (haL : ∀ j < m, 4 ≤ scale j)
    (hquarterL :
      ∀ j < m, 4 * scale j ≤ n)
    (htargetL :
      ∀ j < m, 2 * scale j ≤ n)
    (hmeanL :
      ∀ j < m,
        (2 * scale j) ^ 3 ≤ rL j * n ^ 2)
    (hqaL :
      ∀ j < m,
        qLadder * (scale j + 1) ≤
          (rhoL j) ^ 2)
    (hlabelRoomL :
      ∀ j < m,
        5 * (scale j + 1) ≤ n + 1)
    (hbudgetL :
      ∀ j < m,
        targetGap (j + 1) + (rhoL j + 1) +
            2 * ML j ≤ targetGap j)
    (hAfinal : 4 ≤ scale m)
    (hstageRoomFinal : scale m + 4 ≤ n)
    (hquarterFinal : n ≤ 4 * scale m)
    (hfinalGap : targetGap m = 2 * Dlate)
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
    (p : PMF (InfectionRevealPhysicalState n))
    (εBoundary εGap : ℝ≥0∞)
    (hBoundary :
      terminalFailureMass p
          (Lemma17GapBoundaryGood
            (theorem6FixedCriticalScale n)
            cStar rhoPrev)
        ≤ εBoundary)
    (hGap :
      terminalFailureMass p
          (fun z =>
            Lemma17GapBoundaryGood
                (theorem6FixedCriticalScale n)
                cStar rhoPrev z →
              z.inactive.yIds.card +
                  60 * theorem6FixedPoolMultiplier * Ddec ≤
                z.inactive.xIds.card)
        ≤ εGap)
    (hPostBR :
      ∀ z,
        Lemma18LaunchGood
            (theorem6FixedCriticalScale n)
            cStar rhoPrev
            theorem6FixedPoolMultiplier Ddec z →
          z.inactive.xIds.card +
              z.inactive.yIds.card =
            uPost z + kPost z + 1)
    (hkPost :
      ∀ z,
        Lemma18LaunchGood
            (theorem6FixedCriticalScale n)
            cStar rhoPrev
            theorem6FixedPoolMultiplier Ddec z →
          0 < kPost z)
    (hPostQa :
      ∀ z,
        Lemma18LaunchGood
            (theorem6FixedCriticalScale n)
            cStar rhoPrev
            theorem6FixedPoolMultiplier Ddec z →
          qLadderMajor * (kPost z + 1) ≤
            (60 * theorem6FixedPoolMultiplier * Ddec) ^ 2)
    (hPostQuarter :
      ∀ z,
        Lemma18LaunchGood
            (theorem6FixedCriticalScale n)
            cStar rhoPrev
            theorem6FixedPoolMultiplier Ddec z →
          4 * (kPost z + 1) ≤
            z.inactive.xIds.card +
              z.inactive.yIds.card + 1)
    (hPostClock :
      ∀ z,
        Lemma18LaunchGood
            (theorem6FixedCriticalScale n)
            cStar rhoPrev
            theorem6FixedPoolMultiplier Ddec z →
          ∀ j ≤ m,
            scale j + 1 ≤
              z.coarse.1.active + kPost z) :
    terminalFailureMass
        (p.bind
          (fun z =>
            (((lemma18FromGapBoundaryKernel
                  n h3 (theorem6FixedCriticalScale n)
                  Ddec cStar z).bind
                (fun y =>
                  stagedIter
                    (lemma19LadderKernel
                      n h3 cStar scale)
                    m y)).bind
              (lemma19FullActivationBudgetKernel
                n h3 clockBudget))))
        (Lemma19PhysicalStageRangeGood
          n targetGapLate)
      ≤
        (εBoundary + εGap) +
          ((((lemma18StageError
                qPrefix qEnd
                (theorem6FixedCriticalScale n)
                cStar r18 Ddec +
              lemma16UrnError q18Major) +
            ∑ j ∈ Finset.range m,
              (lemma19StageError
                  (scale j) qLadder cStar
                  (rL j) (ML j) +
                lemma16UrnError qLadderMajor)) +
            lemma16UrnError qLadderMajor) +
          lemma19FullActivationPositiveGapUniformError
            n clockBudget Mlate targetGapLate L) := by
  exact
    lemma17Endpoint_then_lemma18_ladder_19_positive_gap_closed
      n qPrefix qEnd q18Major rhoPrefix rhoEnd
      Ddec theorem6FixedPoolMultiplier
      (theorem6FixedCriticalScale n)
      cStar rhoPrev r18 qLadder qLadderMajor m
      Dlate Dlabel Mlate targetGapLate clockBudget
      scale targetGap rhoL rL ML kPost uPost L
      h3 ha hquarterClock hstageRoom hcStar
      hpriorRadius hprefixRadius hendRadius
      hprefixQa hendQa hmajorQa hlabelRoom18
      hmeanActive18 hguardScale hreactionScale
      hscale0 hgap0 hdouble haL hquarterL
      htargetL hmeanL hqaL hlabelRoomL hbudgetL
      hAfinal hstageRoomFinal hquarterFinal
      hfinalGap hbudgetLate hgapLate0 hgapLaten
      hDlabel hL hscaleLate p εBoundary εGap
      hBoundary hGap
      (fixedGapBoundary_pool_le_stageRemaining_mul
        n cStar rhoPrev hn hlarge)
      hPostBR hkPost hPostQa hPostQuarter hPostClock

end

end Tri

#print axioms
  Tri.fixedEndpoint_then_lemma18_ladder_19_positive_gap_closed
