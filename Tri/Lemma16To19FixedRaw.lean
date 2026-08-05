/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Lemma16To19FixedClock
import Tri.Lemma16To19CorrectedRaw

/-!
# Coarse raw-clock form of the fixed-landing route

The custom landing changes one block kernel but not its horizon.  After the
fixed physical schedule has been flattened, the existing physical-to-coarse
projection and corrected linear clock envelope apply unchanged.
-/

namespace Tri

open scoped ENNReal

noncomputable section

theorem lemma16To19FixedRawClock_le_two_budget
    (n q16 cStar mPred m19 clockBudget : ℕ)
    (hq16 : 1 ≤ q16)
    (hm : mPred + m19 + 2 ≤ q16)
    (hbudget : clockBudget ≤ 2 * q16)
    (hlog : Nat.log 2 n ≤ q16) :
    lemma16To19FixedRawClock
        n q16 cStar mPred m19 clockBudget ≤
      (2 * cStar + 8192) * q16 * n := by
  rw [lemma16To19FixedRawClock_eq_corrected]
  exact
    lemma16To19CorrectedRawClock_le_two_budget
      n q16 cStar (mPred + 1) m19 clockBudget
      hq16 (by omega) hbudget hlog

theorem lemma16To19_fixed_coarse_clock_failure_le_of_schedule
    (n q16 k16 cStar mPred m19 targetA
      rhoSource D clockBudget targetGap : ℕ)
    (scale17 rho17 scale19 : ℕ → ℕ)
    (h3 : 3 ≤ n)
    (hq16 : 0 < q16)
    (hcStar : 0 < cStar)
    (s : InfectionRevealPhysicalState n)
    (ε : ℝ≥0∞)
    (hschedule :
      terminalFailureMass
          ((((lemma16PhysicalStageKernel
                    n h3 k16 (cStar * q16 * n) s).bind
                  (fun z =>
                    stagedIter
                      (lemma17LadderKernel
                        n h3 cStar scale17 rho17)
                      mPred z)).bind
                (lemma17TargetLandingKernel
                  n h3 cStar targetA rhoSource)).bind
            (fun z =>
              ((lemma18FromGapBoundaryKernel
                    n h3 targetA D cStar z).bind
                  (fun y =>
                    stagedIter
                      (lemma19LadderKernel
                        n h3 cStar scale19)
                      m19 y)).bind
                (lemma19FullActivationBudgetKernel
                  n h3 clockBudget)))
          (Lemma19PhysicalStageRangeGood n targetGap)
        ≤ ε) :
    terminalFailureMass
        (iter
          (freeze
            (InfectionActivationGapRangeGood n targetGap)
            (infectionStateStep n h3))
          (lemma16To19FixedRawClock
            n q16 cStar mPred m19 clockBudget)
          (infectionRevealPhysicalForget s))
        (InfectionActivationGapRangeGood n targetGap)
      ≤ ε := by
  rw [← infectionRevealPhysicalStep_iter_freeze_failure_eq
    n h3 targetGap
      (lemma16To19FixedRawClock
        n q16 cStar mPred m19 clockBudget) s]
  exact
    (lemma16To19_fixed_physical_clock_failure_le
      n q16 k16 cStar mPred m19 targetA
      rhoSource D clockBudget targetGap
      scale17 rho17 scale19 h3 hq16 hcStar s).trans
      hschedule

theorem lemma16To19_fixed_coarse_headline_failure_le_of_schedule
    (n q16 k16 cStar mPred m19 targetA
      rhoSource D clockBudget targetGap : ℕ)
    (scale17 rho17 scale19 : ℕ → ℕ)
    (h3 : 3 ≤ n)
    (hq16 : 1 ≤ q16)
    (hm : mPred + m19 + 2 ≤ q16)
    (hbudget : clockBudget ≤ 2 * q16)
    (hlog : Nat.log 2 n ≤ q16)
    (hcStar : 0 < cStar)
    (s : InfectionRevealPhysicalState n)
    (ε : ℝ≥0∞)
    (hschedule :
      terminalFailureMass
          ((((lemma16PhysicalStageKernel
                    n h3 k16 (cStar * q16 * n) s).bind
                  (fun z =>
                    stagedIter
                      (lemma17LadderKernel
                        n h3 cStar scale17 rho17)
                      mPred z)).bind
                (lemma17TargetLandingKernel
                  n h3 cStar targetA rhoSource)).bind
            (fun z =>
              ((lemma18FromGapBoundaryKernel
                    n h3 targetA D cStar z).bind
                  (fun y =>
                    stagedIter
                      (lemma19LadderKernel
                        n h3 cStar scale19)
                      m19 y)).bind
                (lemma19FullActivationBudgetKernel
                  n h3 clockBudget)))
          (Lemma19PhysicalStageRangeGood n targetGap)
        ≤ ε) :
    terminalFailureMass
        (iter
          (freeze
            (InfectionActivationGapRangeGood n targetGap)
            (infectionStateStep n h3))
          ((2 * cStar + 8192) * q16 * n)
          (infectionRevealPhysicalForget s))
        (InfectionActivationGapRangeGood n targetGap)
      ≤ ε := by
  have hexact :=
    lemma16To19_fixed_coarse_clock_failure_le_of_schedule
      n q16 k16 cStar mPred m19 targetA
      rhoSource D clockBudget targetGap
      scale17 rho17 scale19 h3 (by omega) hcStar
      s ε hschedule
  have hclock :=
    lemma16To19FixedRawClock_le_two_budget
      n q16 cStar mPred m19 clockBudget
      hq16 hm hbudget hlog
  exact
    (terminalFailureMass_iter_freeze_antitone_of_subset
      (InfectionActivationGapRangeGood n targetGap)
      (InfectionActivationGapRangeGood n targetGap)
      (infectionStateStep n h3)
      (fun _ hz => hz)
      (lemma16To19FixedRawClock
        n q16 cStar mPred m19 clockBudget)
      ((2 * cStar + 8192) * q16 * n)
      hclock
      (infectionRevealPhysicalForget s)).trans
        hexact

end

end Tri

#print axioms Tri.lemma16To19FixedRawClock_le_two_budget
#print axioms
  Tri.lemma16To19_fixed_coarse_clock_failure_le_of_schedule
#print axioms
  Tri.lemma16To19_fixed_coarse_headline_failure_le_of_schedule
