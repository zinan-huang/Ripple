/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Lemma16To19FixedError
import Tri.Lemma16To19FixedRaw

/-!
# Headline form of the fixed-landing route

This is the seam between a closed fixed semantic schedule and the public
coarse-chain clock and error envelopes.
-/

namespace Tri

open scoped ENNReal

noncomputable section

theorem lemma16To19_fixed_coarse_headline_failure_le_final_of_closed
    (n mPred m19 q k16 cStar targetA rhoSource D r18
      clockBudget Mlate targetGap : ℕ)
    (scale17 rho17 rStage scale19 r19 M19 :
      ℕ → ℕ)
    (L : ℝ)
    (h3 : 3 ≤ n)
    (s : InfectionRevealPhysicalState n)
    (hclosed :
      terminalFailureMass
          ((((lemma16PhysicalStageKernel
                    n h3 k16 (cStar * q * n) s).bind
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
        ≤
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
                n clockBudget Mlate targetGap L))
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
    (hbudgetLower : 2 * q ≤ clockBudget)
    (hbudgetUpper : clockBudget ≤ 2 * q)
    (hL : 3 * (q : ℝ) ≤ L)
    (hgap0 : 0 < targetGap)
    (hgapn : targetGap < n)
    (hgapSq : q * n ≤ targetGap ^ 2)
    (hM : lemma3Quarter targetGap ≤ Mlate)
    (hm : mPred + m19 + 2 ≤ q)
    (hqLarge : 8192 ≤ q) :
    terminalFailureMass
        (iter
          (freeze
            (InfectionActivationGapRangeGood n targetGap)
            (infectionStateStep n h3))
          ((2 * cStar + 8192) * q * n)
          (infectionRevealPhysicalForget s))
        (InfectionActivationGapRangeGood n targetGap)
      ≤ infectionActivationFinalError q := by
  have hraw :=
    lemma16To19_fixed_coarse_headline_failure_le_of_schedule
      n q k16 cStar mPred m19 targetA
      rhoSource D clockBudget targetGap
      scale17 rho17 scale19 h3 hq hm
      hbudgetUpper hlogq hcStar s
      (((3 * lemma16UrnError q +
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
            n clockBudget Mlate targetGap L))
      hclosed
  exact hraw.trans
    (lemma16To19FixedError_le_final
      n mPred m19 q cStar targetA D r18 clockBudget
      Mlate targetGap scale17 rho17 rStage
      scale19 r19 M19 L hscaleTarget hcStar
      hr17 hqa17 hactive17 hdirection17
      hr18 hqa18 hactive18 hdirection18
      hr19 hqa19 hactive19 hdirection19
      hq hlog3 hlogq hbudgetLower hL
      hgap0 hgapn hgapSq hM hm hqLarge)

end

end Tri

#print axioms
  Tri.lemma16To19_fixed_coarse_headline_failure_le_final_of_closed
