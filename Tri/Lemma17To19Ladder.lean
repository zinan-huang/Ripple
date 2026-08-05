/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Lemma18To19Ladder

/-!
# Corrected pointwise composition from Lemma 17 through Lemma 19

The decisive Lemma 18 endpoint is still in the early activation regime.  This
module inserts the positive-gap ladder before invoking the late
full-activation kernel.  The decisive and late gap reserves are distinct.
-/

namespace Tri

open scoped ENNReal

noncomputable section

/-- A good final Lemma 17 boundary traverses the decisive stage, the missing
positive-gap ladder, and the late full-activation continuation. -/
theorem lemma18_then_ladder_then_lemma19_positive_gap_from_gapBoundary
    (n qPrefix qEnd q18Major rhoPrefix rhoEnd Ddec d
      a cStar rhoPrev r18
      qLadder qLadderMajor m kPost uPost
      Dlate Dlabel Mlate targetGapLate clockBudget : ℕ)
    (scale targetGap rhoL rL ML : ℕ → ℕ)
    (L : ℝ)
    (h3 : 3 ≤ n)
    (ha : 4 ≤ a)
    (hquarterClock : 4 * a ≤ n)
    (hstageRoom : 2 * a + 4 ≤ n)
    (hcStar : 128 ≤ cStar)
    (hpriorRadius : cStar * rhoPrev ≤ Ddec)
    (hprefixRadius : rhoPrefix + 1 = Ddec)
    (hendRadius : rhoEnd + 1 = 12 * Ddec)
    (hprefixQa :
      qPrefix * (a + 1) ≤ rhoPrefix ^ 2)
    (hendQa :
      qEnd * (a + 1) ≤ rhoEnd ^ 2)
    (hmajorQa :
      q18Major * (a + 2) ≤
        (60 * d * Ddec) ^ 2)
    (hlabelRoom18 : 5 * a + 8 ≤ n)
    (hmeanActive18 :
      (2 * a) ^ 3 ≤ r18 * n ^ 2)
    (hguardScale : 60 * Ddec ≤ a)
    (hreactionScale :
      1200 * cStar * r18 ≤ 7 * a)
    (hscale0 : scale 0 = 2 * a)
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
    (s : InfectionRevealPhysicalState n)
    (hs :
      Lemma17GapBoundaryGood
        a cStar rhoPrev s)
    (hpoolScale :
      s.inactive.ids.card ≤
        lemma17StageRemaining a s * d)
    (hpoolGap :
      s.inactive.yIds.card + 60 * d * Ddec ≤
        s.inactive.xIds.card)
    (hPostBR :
      s.inactive.xIds.card +
          s.inactive.yIds.card =
        uPost + kPost + 1)
    (hkPost : 0 < kPost)
    (hPostQa :
      qLadderMajor * (kPost + 1) ≤
        (60 * d * Ddec) ^ 2)
    (hPostQuarter :
      4 * (kPost + 1) ≤
        s.inactive.xIds.card +
          s.inactive.yIds.card + 1)
    (hPostClock :
      ∀ j ≤ m,
        scale j + 1 ≤
          s.coarse.1.active + kPost) :
    terminalFailureMass
        (((lemma18FromGapBoundaryKernel
              n h3 a Ddec cStar s).bind
            (fun z =>
              stagedIter
                (lemma19LadderKernel
                  n h3 cStar scale)
                m z)).bind
          (lemma19FullActivationBudgetKernel
            n h3 clockBudget))
        (Lemma19PhysicalStageRangeGood
          n targetGapLate)
      ≤
        (((lemma18StageError
              qPrefix qEnd a cStar r18 Ddec +
            lemma16UrnError q18Major) +
          ∑ j ∈ Finset.range m,
            (lemma19StageError
                (scale j) qLadder cStar
                (rL j) (ML j) +
              lemma16UrnError qLadderMajor)) +
          lemma16UrnError qLadderMajor) +
        lemma19FullActivationPositiveGapUniformError
          n clockBudget Mlate targetGapLate L := by
  let k18 := lemma17StageRemaining a s
  have hanchor18 :
      s.coarse.1.active + k18 = 2 * a := by
    exact
      lemma17StageRemaining_spec
        a s (by omega) hs.1 hs.2.1
  have hpre :
      terminalFailureMass
          (lemma18FromGapBoundaryKernel
            n h3 a Ddec cStar s)
          (Lemma18PhysicalEntryGood
            (2 * a) (2 * Ddec))
        ≤
          lemma18StageError
              qPrefix qEnd a cStar r18 Ddec +
            lemma16UrnError q18Major := by
    exact
      lemma18PhysicalEntry_paper_from_gapBoundary
        n qPrefix qEnd q18Major rhoPrefix rhoEnd
        Ddec d a cStar rhoPrev r18 h3 ha
        hquarterClock hstageRoom hcStar
        hpriorRadius hprefixRadius hendRadius
        hprefixQa hendQa hmajorQa hlabelRoom18
        hmeanActive18 hguardScale hreactionScale
        s hs hpoolScale hpoolGap
  let μ :=
    (lemma18FromGapBoundaryKernel
        n h3 a Ddec cStar s).bind
      (fun z =>
        stagedIter
          (lemma19LadderKernel
            n h3 cStar scale)
          m z)
  have hμ :
      terminalFailureMass μ
          (fun z =>
            Lemma19BoundaryGood
                (scale m) (targetGap m) z ∧
              z.inactive.yIds.card ≤
                z.inactive.xIds.card)
        ≤
          ((lemma18StageError
                qPrefix qEnd a cStar r18 Ddec +
              lemma16UrnError q18Major) +
            ∑ j ∈ Finset.range m,
              (lemma19StageError
                  (scale j) qLadder cStar
                  (rL j) (ML j) +
                lemma16UrnError qLadderMajor)) +
            lemma16UrnError qLadderMajor := by
    simpa [μ, k18] using
      lemma18FromGapBoundary_then_positive_gap_ladder_range_closed
        n qLadder qLadderMajor a Ddec cStar m
        (60 * d * Ddec) kPost uPost
        s.inactive.xIds.card s.inactive.yIds.card
        h3 scale targetGap rhoL rL ML hcStar
        hscale0 hgap0 hdouble haL hquarterL
        htargetL hmeanL hqaL hlabelRoomL hbudgetL
        s hstageRoom hanchor18
        (lemma18StageError
            qPrefix qEnd a cStar r18 Ddec +
          lemma16UrnError q18Major)
        hpre hPostBR hpoolGap rfl rfl hkPost
        hPostQa hPostQuarter hPostClock
  have hμLate :
      terminalFailureMass μ
          (fun z =>
            Lemma19BoundaryGood
                (scale m) (2 * Dlate) z ∧
              z.inactive.yIds.card ≤
                z.inactive.xIds.card)
        ≤
          ((lemma18StageError
                qPrefix qEnd a cStar r18 Ddec +
              lemma16UrnError q18Major) +
            ∑ j ∈ Finset.range m,
              (lemma19StageError
                  (scale j) qLadder cStar
                  (rL j) (ML j) +
                lemma16UrnError qLadderMajor)) +
            lemma16UrnError qLadderMajor := by
    simpa [hfinalGap] using hμ
  simpa [μ] using
    lemma19RangeEntry_then_full_activation_positive_gap_closed
      n (scale m) Dlate Dlabel Mlate
      targetGapLate clockBudget L h3 hAfinal
      hstageRoomFinal hquarterFinal hbudgetLate
      hgapLate0 hgapLaten hDlabel hL hscaleLate
      μ
      (((lemma18StageError
            qPrefix qEnd a cStar r18 Ddec +
          lemma16UrnError q18Major) +
        ∑ j ∈ Finset.range m,
          (lemma19StageError
              (scale j) qLadder cStar
              (rL j) (ML j) +
            lemma16UrnError qLadderMajor)) +
        lemma16UrnError qLadderMajor)
      hμLate

/-- A random final Lemma 17 endpoint continues through the corrected
decisive-stage, positive-gap-ladder, and late-activation route. -/
theorem lemma17Endpoint_then_lemma18_ladder_19_positive_gap_closed
    (n qPrefix qEnd q18Major rhoPrefix rhoEnd Ddec d
      a cStar rhoPrev r18
      qLadder qLadderMajor m
      Dlate Dlabel Mlate targetGapLate clockBudget : ℕ)
    (scale targetGap rhoL rL ML : ℕ → ℕ)
    (kPost uPost :
      InfectionRevealPhysicalState n → ℕ)
    (L : ℝ)
    (h3 : 3 ≤ n)
    (ha : 4 ≤ a)
    (hquarterClock : 4 * a ≤ n)
    (hstageRoom : 2 * a + 4 ≤ n)
    (hcStar : 128 ≤ cStar)
    (hpriorRadius : cStar * rhoPrev ≤ Ddec)
    (hprefixRadius : rhoPrefix + 1 = Ddec)
    (hendRadius : rhoEnd + 1 = 12 * Ddec)
    (hprefixQa :
      qPrefix * (a + 1) ≤ rhoPrefix ^ 2)
    (hendQa :
      qEnd * (a + 1) ≤ rhoEnd ^ 2)
    (hmajorQa :
      q18Major * (a + 2) ≤
        (60 * d * Ddec) ^ 2)
    (hlabelRoom18 : 5 * a + 8 ≤ n)
    (hmeanActive18 :
      (2 * a) ^ 3 ≤ r18 * n ^ 2)
    (hguardScale : 60 * Ddec ≤ a)
    (hreactionScale :
      1200 * cStar * r18 ≤ 7 * a)
    (hscale0 : scale 0 = 2 * a)
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
            a cStar rhoPrev)
        ≤ εBoundary)
    (hGap :
      terminalFailureMass p
          (fun z =>
            Lemma17GapBoundaryGood
                a cStar rhoPrev z →
              z.inactive.yIds.card +
                  60 * d * Ddec ≤
                z.inactive.xIds.card)
        ≤ εGap)
    (hPoolScale :
      ∀ z : InfectionRevealPhysicalState n,
        Lemma17GapBoundaryGood
            a cStar rhoPrev z →
          z.inactive.ids.card ≤
            lemma17StageRemaining a z * d)
    (hPostBR :
      ∀ z,
        Lemma18LaunchGood
            a cStar rhoPrev d Ddec z →
          z.inactive.xIds.card +
              z.inactive.yIds.card =
            uPost z + kPost z + 1)
    (hkPost :
      ∀ z,
        Lemma18LaunchGood
            a cStar rhoPrev d Ddec z →
          0 < kPost z)
    (hPostQa :
      ∀ z,
        Lemma18LaunchGood
            a cStar rhoPrev d Ddec z →
          qLadderMajor * (kPost z + 1) ≤
            (60 * d * Ddec) ^ 2)
    (hPostQuarter :
      ∀ z,
        Lemma18LaunchGood
            a cStar rhoPrev d Ddec z →
          4 * (kPost z + 1) ≤
            z.inactive.xIds.card +
              z.inactive.yIds.card + 1)
    (hPostClock :
      ∀ z,
        Lemma18LaunchGood
            a cStar rhoPrev d Ddec z →
          ∀ j ≤ m,
            scale j + 1 ≤
              z.coarse.1.active + kPost z) :
    terminalFailureMass
        (p.bind
          (fun z =>
            (((lemma18FromGapBoundaryKernel
                  n h3 a Ddec cStar z).bind
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
                qPrefix qEnd a cStar r18 Ddec +
              lemma16UrnError q18Major) +
            ∑ j ∈ Finset.range m,
              (lemma19StageError
                  (scale j) qLadder cStar
                  (rL j) (ML j) +
                lemma16UrnError qLadderMajor)) +
            lemma16UrnError qLadderMajor) +
          lemma19FullActivationPositiveGapUniformError
            n clockBudget Mlate targetGapLate L) := by
  let Launch : InfectionRevealPhysicalState n → Prop :=
    Lemma18LaunchGood a cStar rhoPrev d Ddec
  let K : InfectionRevealPhysicalState n →
      PMF (InfectionRevealPhysicalState n) :=
    fun z =>
      (((lemma18FromGapBoundaryKernel
            n h3 a Ddec cStar z).bind
          (fun y =>
            stagedIter
              (lemma19LadderKernel
                n h3 cStar scale)
              m y)).bind
        (lemma19FullActivationBudgetKernel
          n h3 clockBudget))
  have hlaunch :
      terminalFailureMass p Launch ≤
        εBoundary + εGap := by
    exact
      terminalFailureMass_lemma18LaunchGood
        a cStar rhoPrev d Ddec p εBoundary εGap
        hBoundary hGap hPoolScale
  apply
    terminalFailureMass_bind_le_add_of_support
      p K Launch
      (Lemma19PhysicalStageRangeGood
        n targetGapLate)
      (εBoundary + εGap)
      ((((lemma18StageError
            qPrefix qEnd a cStar r18 Ddec +
          lemma16UrnError q18Major) +
        ∑ j ∈ Finset.range m,
          (lemma19StageError
              (scale j) qLadder cStar
              (rL j) (ML j) +
            lemma16UrnError qLadderMajor)) +
        lemma16UrnError qLadderMajor) +
      lemma19FullActivationPositiveGapUniformError
        n clockBudget Mlate targetGapLate L)
      hlaunch
  intro z _ hz
  exact
    lemma18_then_ladder_then_lemma19_positive_gap_from_gapBoundary
      n qPrefix qEnd q18Major rhoPrefix rhoEnd
      Ddec d a cStar rhoPrev r18
      qLadder qLadderMajor m (kPost z) (uPost z)
      Dlate Dlabel Mlate targetGapLate clockBudget
      scale targetGap rhoL rL ML L h3 ha
      hquarterClock hstageRoom hcStar hpriorRadius
      hprefixRadius hendRadius hprefixQa hendQa
      hmajorQa hlabelRoom18 hmeanActive18
      hguardScale hreactionScale hscale0 hgap0
      hdouble haL hquarterL htargetL hmeanL hqaL
      hlabelRoomL hbudgetL hAfinal hstageRoomFinal
      hquarterFinal hfinalGap hbudgetLate hgapLate0
      hgapLaten hDlabel hL hscaleLate z hz.1
      hz.2.1 hz.2.2 (hPostBR z hz) (hkPost z hz)
      (hPostQa z hz) (hPostQuarter z hz)
      (hPostClock z hz)

end

end Tri

#print axioms Tri.lemma18_then_ladder_then_lemma19_positive_gap_from_gapBoundary
#print axioms Tri.lemma17Endpoint_then_lemma18_ladder_19_positive_gap_closed
