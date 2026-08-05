/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Lemma16To19Corrected
import Tri.Lemma17FixedLandingTo19

/-!
# Lemmas 16--19 through the fixed final Lemma 17 landing

The ordinary dyadic Lemma 17 prefix stops at its last predecessor.  A custom
final rung lands at the least critical scale, after which the existing
Lemma 18 and positive-gap Lemma 19 continuation applies unchanged.
-/

namespace Tri

open scoped ENNReal

noncomputable section

/-- The complete semantic Lemma 16--19 chain using the fixed final
Lemma 17 landing. -/
theorem lemma16_to_19_fixed_landing_positive_gap_closed
    (n q16 qStage qLadderMajor a16 k16 u16 nu R B
      rho16 cStar mPred DLadder kLadder uLadder
      rhoLanding qGap F H kGap uGap
      qPrefix qEnd q18Major rhoPrefix rhoEnd Ddec r18
      q19 q19Major m19
      Dlate Dlabel Mlate targetGapLate clockBudget : ℕ)
    (scale17 rho17 rStage : ℕ → ℕ)
    (scale19 targetGap19 rho19 r19 M19 : ℕ → ℕ)
    (L : ℝ)
    (h3 : 3 ≤ n)
    (hlarge :
      theorem6FixedCStarSq *
          (theorem6FixedCStarSq + 6) ≤ n)
    (hlog : Nat.log 2 n ≤ q16)
    (hquarter16 : 4 * a16 ≤ n)
    (hcStar16 : 640 ≤ cStar)
    (hroot16 : a16 ^ 5 * q16 * n ≤ n ^ 5)
    (hqa16 : q16 * a16 ≤ rho16 ^ 2)
    (hqaOrder16 : q16 ≤ a16)
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
        qStage * (scale17 j + 1) ≤
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
      qLadderMajor * (kLadder + 1) ≤
        DLadder ^ 2)
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
      qStage * (scale17 mPred + 1) ≤
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
      qGap * (kGap + 1) ≤ F ^ 2)
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
        q19 * (scale19 j + 1) ≤
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
      q19Major * (scale19 m19 + 2) ≤
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
    (s : InfectionRevealPhysicalState n)
    (hx0 : s.inactive.xIds.card = B)
    (hy0 : s.inactive.yIds.card = R) :
    terminalFailureMass
        ((((lemma16PhysicalStageKernel
                n h3 k16 (cStar * q16 * n) s).bind
              (fun z =>
                stagedIter
                  (lemma17LadderKernel
                    n h3 cStar scale17 rho17)
                  mPred z)).bind
            (lemma17TargetLandingKernel
              n h3 cStar
                (theorem6FixedCriticalScale n)
                (rho17 mPred))).bind
          (fun z =>
            (((lemma18FromGapBoundaryKernel
                  n h3 (theorem6FixedCriticalScale n)
                  Ddec cStar z).bind
                (fun y =>
                  stagedIter
                    (lemma19LadderKernel
                      n h3 cStar scale19)
                    m19 y)).bind
              (lemma19FullActivationBudgetKernel
                n h3 clockBudget))))
        (Lemma19PhysicalStageRangeGood
          n targetGapLate)
      ≤
        ((3 * lemma16UrnError q16 +
            ∑ j ∈ Finset.range (mPred + 1),
              (lemma17StageError
                  (scale17 j) qStage cStar
                  (rho17 j) (rStage j) +
                lemma16UrnError qLadderMajor)) +
          lemma16UrnError qGap) +
        ((((lemma18StageError
                qPrefix qEnd
                (theorem6FixedCriticalScale n)
                cStar r18 Ddec +
              lemma16UrnError q18Major) +
            ∑ j ∈ Finset.range m19,
              (lemma19StageError
                  (scale19 j) q19 cStar
                  (r19 j) (M19 j) +
                lemma16UrnError q19Major)) +
            lemma16UrnError q19Major) +
          lemma19FullActivationPositiveGapUniformError
            n clockBudget Mlate targetGapLate L) := by
  have hcoarse := s.coarse.2
  simp only [InfectionCfg.Inv, InfectionCfg.total] at hcoarse
  have hinactive := s.hinactiveCard
  have hlabels :=
    InfectionInactiveView.xIds_card_add_yIds_card
      s.inactive
  have hstartActive : s.coarse.1.active = 1 := by
    omega
  have hanchor16 :
      s.coarse.1.active + k16 = a16 := by
    omega
  have hroom16 : a16 + 4 ≤ n := by
    omega
  have hroom17 :
      ∀ l < mPred, 2 * scale17 l + 4 ≤ n := by
    intro l hl
    have hal := ha17 l hl
    have hqtr := hquarter17 l hl
    omega
  have hroomLanding :
      theorem6FixedCriticalScale n + 4 ≤ n := by
    omega
  let p :=
    ((lemma16PhysicalStageKernel
          n h3 k16 (cStar * q16 * n) s).bind
        (fun z =>
          stagedIter
            (lemma17LadderKernel
              n h3 cStar scale17 rho17)
            mPred z)).bind
      (lemma17TargetLandingKernel
        n h3 cStar
          (theorem6FixedCriticalScale n)
          (rho17 mPred))
  have hBoundaryRaw :
      terminalFailureMass p
          (Lemma17GapBoundaryGood
            (theorem6FixedCriticalScale n)
            cStar rhoLanding)
        ≤
          (3 * lemma16UrnError q16 +
            ∑ j ∈ Finset.range mPred,
              (lemma17StageError
                  (scale17 j) qStage cStar
                  (rho17 j) (rStage j) +
                lemma16UrnError qLadderMajor)) +
            lemma16UrnError qLadderMajor +
            lemma17StageError
              (scale17 mPred) qStage cStar
              (rho17 mPred) (rStage mPred) := by
    simpa [p] using
      lemma16_then_lemma17_fixed_target_closed
        n q16 qStage qLadderMajor a16 k16 u16 nu
        R B rho16 cStar mPred DLadder kLadder
        uLadder rhoLanding (rStage mPred)
        scale17 rho17 rStage h3 hlog hquarter16
        hcStar16 hroot16 hqa16 hqaOrder16 hrho16
        hnu hk16 hu16 hRB hmajor0 hk16pos
        hscale17_0 hrho17_0 hcStar hcTwo
        hdouble17 hroot17 ha17 hquarter17
        htarget17 hrho17 hbias17 hactiveScale17
        hmean17 hqa17 hlabelRoom17 hLadderBR
        hLadderGap hkLadder hLadderQa
        hLadderQuarter hLadderClock
        hLadderClockFinal haPred hbelow habove
        hrhoPred hrootLanding hbiasPred
        hactiveScaleLanding hmeanLanding hqaLanding
        s hx0 hy0
  have hBoundary :
      terminalFailureMass p
          (Lemma17GapBoundaryGood
            (theorem6FixedCriticalScale n)
            cStar rhoLanding)
        ≤
          3 * lemma16UrnError q16 +
            ∑ j ∈ Finset.range (mPred + 1),
              (lemma17StageError
                  (scale17 j) qStage cStar
                  (rho17 j) (rStage j) +
                lemma16UrnError qLadderMajor) := by
    calc
      terminalFailureMass p
            (Lemma17GapBoundaryGood
              (theorem6FixedCriticalScale n)
              cStar rhoLanding)
          ≤
        (3 * lemma16UrnError q16 +
          ∑ j ∈ Finset.range mPred,
            (lemma17StageError
                (scale17 j) qStage cStar
                (rho17 j) (rStage j) +
              lemma16UrnError qLadderMajor)) +
          lemma16UrnError qLadderMajor +
          lemma17StageError
            (scale17 mPred) qStage cStar
            (rho17 mPred) (rStage mPred) :=
        hBoundaryRaw
      _ =
        3 * lemma16UrnError q16 +
          ∑ j ∈ Finset.range (mPred + 1),
            (lemma17StageError
                (scale17 j) qStage cStar
                (rho17 j) (rStage j) +
              lemma16UrnError qLadderMajor) := by
        rw [← lemma17FixedLandingError_sum_succ]
        ring
  have hGap :
      terminalFailureMass p
          (fun z =>
            Lemma17GapBoundaryGood
                (theorem6FixedCriticalScale n)
                cStar rhoLanding z →
              z.inactive.yIds.card +
                  60 * theorem6FixedPoolMultiplier * Ddec ≤
                z.inactive.xIds.card)
        ≤ lemma16UrnError qGap := by
    have hclock :
        theorem6FixedCriticalScale n + 1 ≤
          s.coarse.1.active + kGap := by
      rw [hstartActive]
      exact hGapClock
    simpa [p] using
      lemma16_then_lemma17_fixed_target_absolute_gap_failure
        n h3 qGap k16 a16 (cStar * q16 * n)
        cStar mPred (rho17 mPred) rhoLanding
        F H (60 * theorem6FixedPoolMultiplier * Ddec)
        kGap uGap B R scale17 rho17 s
        hroom16 hanchor16 hx0 hy0 hGapBR
        hInitialGap hGapShrink hkGap hGapQa
        hGapQuarter hroom17 hroomLanding hclock
  let kPost :
      InfectionRevealPhysicalState n → ℕ :=
    fun z => lemma19PostRemaining (scale19 m19) z
  let uPost :
      InfectionRevealPhysicalState n → ℕ :=
    fun z => lemma19PostPoolRemainder (scale19 m19) z
  have hPostSpec :
      ∀ z,
        Lemma18LaunchGood
            (theorem6FixedCriticalScale n)
            cStar rhoLanding
            theorem6FixedPoolMultiplier Ddec z →
          z.coarse.1.active + kPost z =
            scale19 m19 + 1 := by
    intro z hz
    have hactiveHi := hz.1.2.1
    have hlevel0 :
        2 * theorem6FixedCriticalScale n ≤ scale19 m19 := by
      rw [← hscale19_0]
      exact hscale19LeFinal 0 (Nat.zero_le m19)
    apply lemma19PostRemaining_spec
    dsimp only [kPost]
    omega
  have hkPost :
      ∀ z,
        Lemma18LaunchGood
            (theorem6FixedCriticalScale n)
            cStar rhoLanding
            theorem6FixedPoolMultiplier Ddec z →
          0 < kPost z := by
    intro z hz
    have hactiveHi := hz.1.2.1
    have hlevel0 :
        2 * theorem6FixedCriticalScale n ≤ scale19 m19 := by
      rw [← hscale19_0]
      exact hscale19LeFinal 0 (Nat.zero_le m19)
    have hspec := hPostSpec z hz
    omega
  have hPostQuarter :
      ∀ z,
        Lemma18LaunchGood
            (theorem6FixedCriticalScale n)
            cStar rhoLanding
            theorem6FixedPoolMultiplier Ddec z →
          4 * (kPost z + 1) ≤
            z.inactive.xIds.card +
              z.inactive.yIds.card + 1 := by
    intro z hz
    have hactiveLo := hz.1.1
    have hspec := hPostSpec z hz
    have htotal :=
      infectionReveal_active_add_inactive z
    have hlabels :=
      InfectionInactiveView.xIds_card_add_yIds_card
        z.inactive
    omega
  have hPostBR :
      ∀ z,
        Lemma18LaunchGood
            (theorem6FixedCriticalScale n)
            cStar rhoLanding
            theorem6FixedPoolMultiplier Ddec z →
          z.inactive.xIds.card +
              z.inactive.yIds.card =
            uPost z + kPost z + 1 := by
    intro z hz
    have hroom :
        kPost z + 1 ≤
          z.inactive.yIds.card +
            z.inactive.xIds.card := by
      have hqtr := hPostQuarter z hz
      omega
    have hrem :=
      lemma17PoolRemainder_spec
        (kPost z)
        z.inactive.yIds.card
        z.inactive.xIds.card hroom
    simpa [uPost, lemma19PostPoolRemainder, kPost,
      Nat.add_comm] using hrem.symm
  have hPostQa :
      ∀ z,
        Lemma18LaunchGood
            (theorem6FixedCriticalScale n)
            cStar rhoLanding
            theorem6FixedPoolMultiplier Ddec z →
          q19Major * (kPost z + 1) ≤
            (60 * theorem6FixedPoolMultiplier * Ddec) ^ 2 := by
    intro z hz
    have hspec := hPostSpec z hz
    exact
      (Nat.mul_le_mul_left q19Major
        (show kPost z + 1 ≤ scale19 m19 + 2 by
          omega)).trans hPostQaGlobal
  have hPostClock :
      ∀ z,
        Lemma18LaunchGood
            (theorem6FixedCriticalScale n)
            cStar rhoLanding
            theorem6FixedPoolMultiplier Ddec z →
          ∀ j ≤ m19,
            scale19 j + 1 ≤
              z.coarse.1.active + kPost z := by
    intro z hz j hj
    rw [hPostSpec z hz]
    exact Nat.add_le_add_right
      (hscale19LeFinal j hj) 1
  simpa [p] using
    fixedEndpoint_then_lemma18_ladder_19_positive_gap_closed
      n qPrefix qEnd q18Major rhoPrefix rhoEnd
      Ddec cStar rhoLanding r18 q19 q19Major m19
      Dlate Dlabel Mlate targetGapLate clockBudget
      scale19 targetGap19 rho19 r19 M19 kPost uPost L
      (by omega) hlarge h3 ha18 hquarterClock18
      hstageRoom18 hcStar hpriorRadius hprefixRadius
      hendRadius hprefixQa hendQa hmajorQa
      hlabelRoom18 hmeanActive18 hguardScale
      hreactionScale hscale19_0 hgap19_0 hdouble19
      ha19 hquarter19 htarget19 hmean19 hqa19
      hlabelRoom19 hbudget19 hAfinal
      hstageRoomFinal hquarterFinal hfinalGap
      hbudgetLate hgapLate0 hgapLaten hDlabel hL
      hscaleLate p
      (3 * lemma16UrnError q16 +
        ∑ j ∈ Finset.range (mPred + 1),
          (lemma17StageError
              (scale17 j) qStage cStar
              (rho17 j) (rStage j) +
            lemma16UrnError qLadderMajor))
      (lemma16UrnError qGap)
      hBoundary hGap hPostBR hkPost hPostQa
      hPostQuarter hPostClock

end

end Tri

#print axioms
  Tri.lemma16_to_19_fixed_landing_positive_gap_closed
