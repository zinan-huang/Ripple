/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Lemma17To18

/-!
# End-to-end physical composition of Lemmas 16--19

This module joins the one-active Lemma 16 stage, the Lemma 17 doubling
ladder, the decisive Lemma 18 block, and the positive-gap Lemma 19
full-activation continuation on one identity-refined physical path.
-/

namespace Tri

open scoped ENNReal

noncomputable section

/-- The complete parameterized Lemma 16--19 activation chain.  The ladder
anchor and decisive-stage inactive-gap events are both controlled by urn
potentials from the original inactive pool. -/
theorem lemma16_to_19_positive_gap_closed
    (n q16 qStage qLadderMajor a16 k16 u16 nu R B
      rho16 cStar m DLadder kLadder uLadder
      qGap F H kGap uGap
      qPrefix qEnd q18Major rhoPrefix rhoEnd D d r18
      Dlabel M targetGap clockBudget : ℕ)
    (scale rho rStage : ℕ → ℕ)
    (L : ℝ)
    (h3 : 3 ≤ n)
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
    (hscale0 : scale 0 = a16)
    (hrho0 : rho 0 = rho16)
    (hcStar : 128 ≤ cStar)
    (hcTwo : 2 ≤ cStar)
    (hdouble :
      ∀ j < m, scale (j + 1) = 2 * scale j)
    (hroot :
      ∀ j < m, 19 * rho j ≤ 14 * rho (j + 1))
    (ha :
      ∀ j < m, 4 ≤ scale j)
    (hquarter :
      ∀ j < m, 4 * scale j ≤ n)
    (htarget :
      ∀ j < m, 2 * scale j ≤ n)
    (hrho :
      ∀ j < m, 1 ≤ rho j)
    (hbias :
      ∀ j < m,
        38 * cStar * rho j ≤ scale j)
    (hactiveScale :
      ∀ j < m,
        76 * cStar * rStage j ≤ scale j)
    (hmean :
      ∀ j < m,
        (2 * scale j) ^ 3 ≤
          rStage j * n ^ 2)
    (hqa :
      ∀ j < m,
        qStage * (scale j + 1) ≤
          (rho j) ^ 2)
    (hlabelRoom :
      ∀ j < m,
        5 * (scale j + 1) ≤ n + 1)
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
      ∀ j < m,
        scale j + 1 ≤ 1 + kLadder)
    (hGapBR :
      B + R = uGap + kGap + 1)
    (hInitialGap :
      R + (F + H) ≤ B)
    (hGapShrink :
      (60 * d * D) * (B + R) ≤
        H * (uGap + 1))
    (hkGap : 0 < kGap)
    (hGapQa :
      qGap * (kGap + 1) ≤ F ^ 2)
    (hGapQuarter :
      4 * (kGap + 1) ≤ B + R + 1)
    (hGapClock :
      scale m + 1 ≤ 1 + kGap)
    (ha18 : 4 ≤ scale m)
    (hquarterClock18 :
      4 * scale m ≤ n)
    (hstageRoom18 :
      2 * scale m + 4 ≤ n)
    (hquarterLate :
      n ≤ 4 * (2 * scale m))
    (hpriorRadius :
      cStar * rho m ≤ D)
    (hprefixRadius :
      rhoPrefix + 1 = D)
    (hendRadius :
      rhoEnd + 1 = 12 * D)
    (hprefixQa :
      qPrefix * (scale m + 1) ≤
        rhoPrefix ^ 2)
    (hendQa :
      qEnd * (scale m + 1) ≤
        rhoEnd ^ 2)
    (hmajorQa :
      q18Major * (scale m + 2) ≤
        (60 * d * D) ^ 2)
    (hlabelRoom18 :
      5 * scale m + 8 ≤ n)
    (hmeanActive18 :
      (2 * scale m) ^ 3 ≤ r18 * n ^ 2)
    (hguardScale :
      60 * D ≤ scale m)
    (hreactionScale :
      1200 * cStar * r18 ≤ 7 * scale m)
    (hbudget :
      targetGap + Dlabel + 2 * M ≤ 2 * D)
    (hgap0 : 0 < targetGap)
    (hgapn : targetGap < n)
    (hDlabel : 0 < Dlabel)
    (hL : 0 ≤ L)
    (hlabelScale :
      L * (n : ℝ) ≤
        ((Dlabel : ℝ) / 2) ^ 2)
    (hPoolScale :
      ∀ z : InfectionRevealPhysicalState n,
        Lemma17GapBoundaryGood
            (scale m) cStar (rho m) z →
          z.inactive.ids.card ≤
            lemma17StageRemaining (scale m) z * d)
    (s : InfectionRevealPhysicalState n)
    (hx0 : s.inactive.xIds.card = B)
    (hy0 : s.inactive.yIds.card = R) :
    terminalFailureMass
        (((lemma16PhysicalStageKernel
              n h3 k16 (cStar * q16 * n) s).bind
            (fun z =>
              stagedIter
                (lemma17LadderKernel
                  n h3 cStar scale rho)
                m z)).bind
          (fun z =>
            (lemma18FromGapBoundaryKernel
                n h3 (scale m) D cStar z).bind
              (lemma19FullActivationBudgetKernel
                n h3 clockBudget)))
        (Lemma19PhysicalStageRangeGood n targetGap)
      ≤
        ((3 * lemma16UrnError q16 +
            ∑ j ∈ Finset.range m,
              (lemma17StageError
                  (scale j) qStage cStar
                  (rho j) (rStage j) +
                lemma16UrnError qLadderMajor)) +
          lemma16UrnError qGap) +
        ((lemma18StageError
              qPrefix qEnd (scale m) cStar r18 D +
            lemma16UrnError q18Major) +
          lemma19FullActivationPositiveGapUniformError
            n clockBudget M targetGap L) := by
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
  let p :=
    (lemma16PhysicalStageKernel
        n h3 k16 (cStar * q16 * n) s).bind
      (fun z =>
        stagedIter
          (lemma17LadderKernel
            n h3 cStar scale rho)
          m z)
  have hBoundary :
      terminalFailureMass p
          (Lemma17GapBoundaryGood
            (scale m) cStar (rho m))
        ≤
          3 * lemma16UrnError q16 +
            ∑ j ∈ Finset.range m,
              (lemma17StageError
                  (scale j) qStage cStar
                  (rho j) (rStage j) +
                lemma16UrnError qLadderMajor) := by
    simpa [p] using
      lemma16_then_lemma17_ladder_closed
        n q16 qStage qLadderMajor a16 k16 u16 nu
        R B rho16 cStar m DLadder kLadder uLadder
        scale rho rStage h3 hlog hquarter16 hcStar16
        hroot16 hqa16 hqaOrder16 hrho16 hnu hk16
        hu16 hRB hmajor0 hk16pos hscale0 hrho0
        hcStar hcTwo hdouble hroot ha hquarter htarget
        hrho hbias hactiveScale hmean hqa hlabelRoom
        hLadderBR hLadderGap hkLadder hLadderQa
        hLadderQuarter hLadderClock s hx0 hy0
  have hroom17 :
      ∀ l < m, 2 * scale l + 4 ≤ n := by
    intro l hl
    have hal := ha l hl
    have hqtr := hquarter l hl
    omega
  have hGap :
      terminalFailureMass p
          (fun z =>
            Lemma17GapBoundaryGood
                (scale m) cStar (rho m) z →
              z.inactive.yIds.card + 60 * d * D ≤
                z.inactive.xIds.card)
        ≤ lemma16UrnError qGap := by
    have hclock :
        scale m + 1 ≤
          s.coarse.1.active + kGap := by
      rw [hstartActive]
      exact hGapClock
    simpa [p] using
      lemma16_then_lemma17_absolute_gap_failure
        n h3 qGap k16 a16 (cStar * q16 * n)
        cStar m F H (60 * d * D) kGap uGap B R
        scale rho s hroom16 hanchor16 hx0 hy0
        hGapBR hInitialGap hGapShrink hkGap hGapQa
        hGapQuarter hroom17 hclock
  simpa [p] using
    lemma17Endpoint_then_lemma18_19_positive_gap_closed
      n qPrefix qEnd q18Major rhoPrefix rhoEnd D d
      (scale m) cStar (rho m) r18
      Dlabel M targetGap clockBudget L
      h3 ha18 hquarterClock18 hstageRoom18
      hquarterLate hcStar hpriorRadius
      hprefixRadius hendRadius hprefixQa hendQa
      hmajorQa hlabelRoom18 hmeanActive18
      hguardScale hreactionScale hbudget
      hgap0 hgapn hDlabel hL hlabelScale
      p
      (3 * lemma16UrnError q16 +
        ∑ j ∈ Finset.range m,
          (lemma17StageError
              (scale j) qStage cStar
              (rho j) (rStage j) +
            lemma16UrnError qLadderMajor))
      (lemma16UrnError qGap)
      hBoundary hGap hPoolScale

end

end Tri

#print axioms Tri.lemma16_to_19_positive_gap_closed
