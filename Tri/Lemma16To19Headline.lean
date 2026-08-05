/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Lemma16To19Raw
import Tri.Lemma16To19Error
import Tri.Lemma16To19ErrorConditions
import Tri.Lemma19Parameters
import Tri.InfectionInitialParams

/-!
# Headline raw-clock form of the Lemma 16--19 chain

This module combines the closed stagewise estimate with its common
exponential envelope and pads the exact activation schedule to the advertised
linear raw clock.
-/

namespace Tri

open scoped ENNReal

noncomputable section

/-- Any closed stagewise Lemma 16--19 estimate with a common parameter `q`
immediately gives the final exponential estimate on the exact raw activation
clock. -/
theorem lemma16To19_coarse_clock_failure_le_final_of_closed
    (n m q cStar D r18 clockBudget M targetGap : ℕ)
    (scale rho rStage : ℕ → ℕ)
    (L : ℝ)
    (s : InfectionRevealPhysicalState n)
    (h3 : 3 ≤ n)
    (hclosed :
      terminalFailureMass
          (iter
            (freeze
              (InfectionActivationGapRangeGood n targetGap)
              (infectionStateStep n h3))
            (lemma16To19TotalClock
              n q cStar m clockBudget)
            (infectionRevealPhysicalForget s))
          (InfectionActivationGapRangeGood n targetGap)
        ≤
          ((3 * lemma16UrnError q +
                ∑ j ∈ Finset.range m,
                  (lemma17StageError
                      (scale j) q cStar
                      (rho j) (rStage j) +
                    lemma16UrnError q)) +
              lemma16UrnError q) +
            ((lemma18StageError
                  q q (scale m) cStar r18 D +
                lemma16UrnError q) +
              lemma19FullActivationPositiveGapUniformError
                n clockBudget M targetGap L))
    (hcStar : 0 < cStar)
    (hr :
      ∀ j < m, 0 < rStage j)
    (hqa :
      ∀ j < m, q ≤ scale j)
    (hactive :
      ∀ j < m,
        15 * q ≤ 4 * cStar * rStage j)
    (hdirection :
      ∀ j < m,
        3 * q * rStage j ≤
          4 * cStar * (rho j) ^ 2)
    (hr18 : 0 < r18)
    (hqa18 : q ≤ scale m)
    (hactive18 :
      15 * q ≤ 4 * cStar * r18)
    (hdirection18 :
      15 * q * cStar * r18 ≤
        49 * D ^ 2)
    (hq : 1 ≤ q)
    (hlog3 : 3 ≤ Nat.log 2 n)
    (hlogq : Nat.log 2 n ≤ q)
    (hbudget : 2 * q ≤ clockBudget)
    (hL : 3 * (q : ℝ) ≤ L)
    (hgap0 : 0 < targetGap)
    (hgapn : targetGap < n)
    (hgapSq : q * n ≤ targetGap ^ 2)
    (hM : lemma3Quarter targetGap ≤ M)
    (hm : m ≤ q)
    (hqLarge : 8192 ≤ q) :
    terminalFailureMass
        (iter
          (freeze
            (InfectionActivationGapRangeGood n targetGap)
            (infectionStateStep n h3))
          (lemma16To19TotalClock
            n q cStar m clockBudget)
          (infectionRevealPhysicalForget s))
        (InfectionActivationGapRangeGood n targetGap)
      ≤ infectionActivationFinalError q :=
  hclosed.trans
    (lemma16To19ClosedError_le_final
      n m q cStar D r18 clockBudget M targetGap
      scale rho rStage L hcStar hr hqa hactive
      hdirection hr18 hqa18 hactive18 hdirection18
      hq hlog3 hlogq hbudget hL hgap0 hgapn
      hgapSq hM hm hqLarge)

/-- The same estimate at the simple deterministic headline clock
`(2cStar + 8192) q n`, using the common-error choice
`clockBudget = 2q`. -/
theorem lemma16To19_coarse_headline_clock_failure_le_final_of_closed
    (n m q cStar D r18 clockBudget M targetGap : ℕ)
    (scale rho rStage : ℕ → ℕ)
    (L : ℝ)
    (s : InfectionRevealPhysicalState n)
    (h3 : 3 ≤ n)
    (hclosed :
      terminalFailureMass
          (iter
            (freeze
              (InfectionActivationGapRangeGood n targetGap)
              (infectionStateStep n h3))
            (lemma16To19TotalClock
              n q cStar m clockBudget)
            (infectionRevealPhysicalForget s))
          (InfectionActivationGapRangeGood n targetGap)
        ≤
          ((3 * lemma16UrnError q +
                ∑ j ∈ Finset.range m,
                  (lemma17StageError
                      (scale j) q cStar
                      (rho j) (rStage j) +
                    lemma16UrnError q)) +
              lemma16UrnError q) +
            ((lemma18StageError
                  q q (scale m) cStar r18 D +
                lemma16UrnError q) +
              lemma19FullActivationPositiveGapUniformError
                n clockBudget M targetGap L))
    (hcStar : 0 < cStar)
    (hr :
      ∀ j < m, 0 < rStage j)
    (hqa :
      ∀ j < m, q ≤ scale j)
    (hactive :
      ∀ j < m,
        15 * q ≤ 4 * cStar * rStage j)
    (hdirection :
      ∀ j < m,
        3 * q * rStage j ≤
          4 * cStar * (rho j) ^ 2)
    (hr18 : 0 < r18)
    (hqa18 : q ≤ scale m)
    (hactive18 :
      15 * q ≤ 4 * cStar * r18)
    (hdirection18 :
      15 * q * cStar * r18 ≤
        49 * D ^ 2)
    (hq : 1 ≤ q)
    (hlog3 : 3 ≤ Nat.log 2 n)
    (hlogq : Nat.log 2 n ≤ q)
    (hbudgetLower : 2 * q ≤ clockBudget)
    (hL : 3 * (q : ℝ) ≤ L)
    (hgap0 : 0 < targetGap)
    (hgapn : targetGap < n)
    (hgapSq : q * n ≤ targetGap ^ 2)
    (hM : lemma3Quarter targetGap ≤ M)
    (hm : m ≤ q)
    (hqLarge : 8192 ≤ q)
    (hmClock : m + 1 ≤ q)
    (hbudgetUpper : clockBudget ≤ 2 * q) :
    terminalFailureMass
        (iter
          (freeze
            (InfectionActivationGapRangeGood n targetGap)
            (infectionStateStep n h3))
          ((2 * cStar + 8192) * q * n)
          (infectionRevealPhysicalForget s))
        (InfectionActivationGapRangeGood n targetGap)
      ≤ infectionActivationFinalError q := by
  have hexact :=
    lemma16To19_coarse_clock_failure_le_final_of_closed
      n m q cStar D r18 clockBudget M targetGap
      scale rho rStage L s h3 hclosed hcStar hr hqa
      hactive hdirection hr18 hqa18 hactive18
      hdirection18 hq hlog3 hlogq hbudgetLower hL
      hgap0 hgapn hgapSq hM hm hqLarge
  have hclock :=
    lemma16To19TotalClock_le_two_budget
      n q cStar m clockBudget
      hq hmClock hbudgetUpper hlogq
  exact
    (terminalFailureMass_iter_freeze_antitone_of_subset
      (InfectionActivationGapRangeGood n targetGap)
      (InfectionActivationGapRangeGood n targetGap)
      (infectionStateStep n h3)
      (fun _ hz => hz)
      (lemma16To19TotalClock n q cStar m clockBudget)
      ((2 * cStar + 8192) * q * n)
      hclock
      (infectionRevealPhysicalForget s)).trans
        hexact

/-- Direct common-parameter form: the complete physical concentration chain,
raw-clock projection, error summation, and clock padding are composed in one
declaration. -/
theorem lemma16_to_19_coarse_headline_closed
    (n q a16 rho16 cStar m DLadder kLadder uLadder
      F H kGap uGap
      rhoPrefix rhoEnd D d r18 aPred
      rGap : ℕ)
    (scale rho rStage : ℕ → ℕ)
    (s : InfectionRevealPhysicalState n)
    (initial : InfectionInitialParams s a16)
    (h3 : 3 ≤ n)
    (hlog : Nat.log 2 n ≤ q)
    (hquarter16 : 4 * a16 ≤ n)
    (hcStar16 : 640 ≤ cStar)
    (hroot16 : a16 ^ 5 * q * n ≤ n ^ 5)
    (hqa16 : q * a16 ≤ rho16 ^ 2)
    (hqaOrder16 : q ≤ a16)
    (hrho16 : 1 ≤ rho16)
    (hmajor0 : initial.R ≤ initial.B)
    (hscale0 : scale 0 = a16)
    (hrho0 : rho 0 = rho16)
    (hdouble :
      ∀ j < m, scale (j + 1) = 2 * scale j)
    (hroot :
      ∀ j < m, 19 * rho j ≤ 14 * rho (j + 1))
    (ha :
      ∀ j < m, 4 ≤ scale j)
    (hquarter :
      ∀ j < m, 4 * scale j ≤ n)
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
        q * (scale j + 1) ≤
          (rho j) ^ 2)
    (hlabelRoom :
      ∀ j < m,
        5 * (scale j + 1) ≤ n + 1)
    (hLadderBR :
      initial.B + initial.R =
        uLadder + kLadder + 1)
    (hLadderGap :
      initial.R + DLadder ≤ initial.B)
    (hkLadder : 0 < kLadder)
    (hLadderQa :
      q * (kLadder + 1) ≤ DLadder ^ 2)
    (hLadderQuarter :
      4 * (kLadder + 1) ≤
        initial.B + initial.R + 1)
    (hLadderClock :
      ∀ j < m,
        scale j + 1 ≤ 1 + kLadder)
    (hGapBR :
      initial.B + initial.R =
        uGap + kGap + 1)
    (hInitialGap :
      initial.R + (F + H) ≤ initial.B)
    (hGapShrink :
      (60 * d * D) *
          (initial.B + initial.R) ≤
        H * (uGap + 1))
    (hkGap : 0 < kGap)
    (hGapQa :
      q * (kGap + 1) ≤ F ^ 2)
    (hGapQuarter :
      4 * (kGap + 1) ≤
        initial.B + initial.R + 1)
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
      q * (scale m + 1) ≤
        rhoPrefix ^ 2)
    (hendQa :
      q * (scale m + 1) ≤
        rhoEnd ^ 2)
    (hmajorQa :
      q * (scale m + 2) ≤
        (60 * d * D) ^ 2)
    (hlabelRoom18 :
      5 * scale m + 8 ≤ n)
    (hmeanActive18 :
      (2 * scale m) ^ 3 ≤ r18 * n ^ 2)
    (hguardScale :
      60 * D ≤ scale m)
    (hreactionScale :
      1200 * cStar * r18 ≤ 7 * scale m)
    (hrGap : 0 < rGap)
    (hreserve : 13 * rGap ≤ D)
    (hGapScale : q * n ≤ 16 * rGap ^ 2)
    (hGapRoom : 4 * rGap < n)
    (haPred : aPred + 1 = scale m)
    (hPoolBudget : n ≤ aPred * d)
    (hactiveErr :
      ∀ j < m,
        15 * q ≤ 4 * cStar * rStage j)
    (hactive18Err :
      15 * q ≤ 4 * cStar * r18)
    (hlog3 : 3 ≤ Nat.log 2 n)
    (hqLarge : 8192 ≤ q)
    (hmClock : m + 1 ≤ q) :
    terminalFailureMass
        (iter
          (freeze
            (InfectionActivationGapRangeGood n
              (lemma19CommonTargetGap rGap))
            (infectionStateStep n h3))
          ((2 * cStar + 8192) * q * n)
          (infectionRevealPhysicalForget s))
        (InfectionActivationGapRangeGood n
          (lemma19CommonTargetGap rGap))
      ≤ infectionActivationFinalError q := by
  have hcStar : 128 ≤ cStar := by omega
  have hcTwo : 2 ≤ cStar := by omega
  have htarget :
      ∀ j < m, 2 * scale j ≤ n := by
    intro j hj
    have := hquarter j hj
    omega
  have hbudget :=
    lemma19Common_budget D rGap hreserve
  have hgap0 :=
    lemma19Common_target_pos rGap hrGap
  have hgapn :=
    lemma19Common_target_lt_population
      n rGap hGapRoom
  have hDlabel :=
    lemma19Common_label_pos rGap hrGap
  have hL : 0 ≤ lemma19CommonRealLabelBudget q := by
    unfold lemma19CommonRealLabelBudget
    positivity
  have hlabelScale :=
    lemma19Common_label_scale n q rGap hGapScale
  have hclockBudget :=
    lemma19Common_clock_budget_eq q
  have hLlower :=
    lemma19Common_label_budget_lower q
  have hgapSq :=
    lemma19Common_gap_sq n q rGap hGapScale
  have hM :=
    lemma19Common_quarter_le_safety rGap hrGap
  have hm : m ≤ q := by omega
  have hbudgetLower :
      2 * q ≤ lemma19CommonClockBudget q := by
    rw [hclockBudget]
  have hbudgetUpper :
      lemma19CommonClockBudget q ≤ 2 * q := by
    rw [hclockBudget]
  have hk16pos : 0 < initial.k16 :=
    initial.k16_pos (by omega)
  have hPoolScale :
      ∀ z : InfectionRevealPhysicalState n,
        Lemma17GapBoundaryGood
            (scale m) cStar (rho m) z →
          z.inactive.ids.card ≤
            lemma17StageRemaining (scale m) z * d := by
    intro z hz
    exact gapBoundary_pool_le_stageRemaining_mul
      n (scale m) cStar (rho m) d aPred
      (by omega) haPred hPoolBudget z hz
  have hclosed :=
    lemma16_to_19_coarse_clock_closed
      n q q q a16 initial.k16 initial.u16
      initial.nu initial.R initial.B
      rho16 cStar m DLadder kLadder uLadder
      q F H kGap uGap
      q q q rhoPrefix rhoEnd D d r18
      (lemma19CommonLabelRadius rGap)
      (lemma19CommonSafetyBudget rGap)
      (lemma19CommonTargetGap rGap)
      (lemma19CommonClockBudget q)
      scale rho rStage
      (lemma19CommonRealLabelBudget q)
      h3 hlog hquarter16 hcStar16 hroot16 hqa16
      hqaOrder16 hrho16 initial.hnu initial.hk16
      initial.hsplit16 initial.hRB hmajor0
      hk16pos hscale0 hrho0 hcStar hcTwo hdouble
      hroot ha hquarter htarget hrho hbias hactiveScale
      hmean hqa hlabelRoom hLadderBR hLadderGap
      hkLadder hLadderQa hLadderQuarter hLadderClock
      hGapBR hInitialGap hGapShrink hkGap hGapQa
      hGapQuarter hGapClock ha18 hquarterClock18
      hstageRoom18 hquarterLate hpriorRadius
      hprefixRadius hendRadius hprefixQa hendQa hmajorQa
      hlabelRoom18 hmeanActive18 hguardScale
      hreactionScale hbudget hgap0 hgapn hDlabel hL
      hlabelScale hPoolScale s initial.hx0 initial.hy0
  have hq0 : q ≤ scale 0 := by
    rw [hscale0]
    exact hqaOrder16
  have hqaErr :
      ∀ j < m, q ≤ scale j := by
    intro j hj
    exact common_q_le_scale_of_double
      q m scale hq0 hdouble j (by omega)
  have hqa18Err : q ≤ scale m :=
    common_q_le_scale_of_double
      q m scale hq0 hdouble m le_rfl
  have hrErr :
      ∀ j < m, 0 < rStage j := by
    intro j hj
    exact stage_reaction_parameter_pos
      n (scale j) (rStage j)
      (by have := ha j hj; omega)
      (hmean j hj)
  have hr18Err : 0 < r18 :=
    stage_reaction_parameter_pos
      n (scale m) r18
      (by omega) hmeanActive18
  have hdirectionErr :
      ∀ j < m,
        3 * q * rStage j ≤
          4 * cStar * (rho j) ^ 2 := by
    intro j hj
    exact lemma17_error_direction_of_stage
      q (scale j) cStar (rho j) (rStage j)
      (by omega) (hactiveScale j hj) (hqa j hj)
  have hdirection18Err :
      15 * q * cStar * r18 ≤
        49 * D ^ 2 :=
    lemma18_error_direction_of_stage
      q (scale m) cStar r18 D rhoPrefix
      hreactionScale hprefixRadius hprefixQa
  exact
    lemma16To19_coarse_headline_clock_failure_le_final_of_closed
      n m q cStar D r18
      (lemma19CommonClockBudget q)
      (lemma19CommonSafetyBudget rGap)
      (lemma19CommonTargetGap rGap)
      scale rho rStage
      (lemma19CommonRealLabelBudget q)
      s h3 hclosed
      (by omega) hrErr hqaErr hactiveErr
      hdirectionErr hr18Err hqa18Err hactive18Err
      hdirection18Err (by omega) hlog3 hlog
      hbudgetLower hLlower hgap0 hgapn hgapSq hM
      hm hqLarge hmClock hbudgetUpper

end

end Tri

#print axioms Tri.lemma16To19_coarse_clock_failure_le_final_of_closed
#print axioms Tri.lemma16To19_coarse_headline_clock_failure_le_final_of_closed
#print axioms Tri.lemma16_to_19_coarse_headline_closed
