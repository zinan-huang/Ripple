/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Lemma18PaperStage
import Tri.Lemma17PhysicalStage
import Tri.Lemma17StagePotential
import Tri.Lemma17InactiveMajorityTail

/-!
# Physical endpoint form of Lemma 18

The counted carrier is stage-local bookkeeping.  This module projects the
fully instantiated decisive-stage theorem back to the identity-refined
physical infection state consumed by later stages.
-/

namespace Tri

open scoped ENNReal

noncomputable section

/-- The decisive physical endpoint has reached its target with positive
`X-Y` gap at least `targetGap`. -/
def Lemma18PhysicalStageGood
    {n : ℕ} (A targetGap : ℕ)
    (s : InfectionRevealPhysicalState n) : Prop :=
  A ≤ s.coarse.1.active ∧
    s.coarse.1.ay + targetGap ≤ s.coarse.1.ax

noncomputable instance lemma18PhysicalStageGoodDecidable
    {n : ℕ} (A targetGap : ℕ) :
    DecidablePred (@Lemma18PhysicalStageGood n A targetGap) :=
  Classical.decPred _

/-- The physical endpoint required by Lemma 19: the decisive active gap has
been created, and the unrevealed pool still has an `X` majority. -/
def Lemma18PhysicalEntryGood
    {n : ℕ} (A targetGap : ℕ)
    (s : InfectionRevealPhysicalState n) : Prop :=
  Lemma18PhysicalStageGood A targetGap s ∧
    s.inactive.yIds.card ≤ s.inactive.xIds.card

noncomputable instance lemma18PhysicalEntryGoodDecidable
    {n : ℕ} (A targetGap : ℕ) :
    DecidablePred (@Lemma18PhysicalEntryGood n A targetGap) :=
  Classical.decPred _

/-- A complete decisive stage preserves the initial stopped-urn potential.
Thus an initial inactive `X` advantage controls loss of the inactive majority
at the physical endpoint, including the possible one-identity overshoot. -/
theorem lemma18PhysicalStage_inactive_majority_tail
    (n : ℕ) (h3 : 3 ≤ n)
    (qMajor DMajor ell k u B R A G T : ℕ)
    (s : InfectionRevealPhysicalState n)
    (hBR : B + R = u + ell + 1)
    (hgap : R + DMajor ≤ B)
    (hx0 : s.inactive.xIds.card = B)
    (hy0 : s.inactive.yIds.card = R)
    (hell : 0 < ell)
    (hqa : qMajor * (ell + 1) ≤ DMajor ^ 2)
    (hquarter : 4 * (ell + 1) ≤ B + R + 1)
    (hstageRoom : A + 4 ≤ n)
    (hanchorActive : s.coarse.1.active + k = A)
    (hovershoot : k + 1 ≤ ell) :
    terminalFailureMass
        (lemma17PhysicalStageKernel n h3 k A G T s)
        (fun z =>
          z.inactive.yIds.card ≤ z.inactive.xIds.card)
      ≤ lemma16UrnError qMajor := by
  let Bad := Lemma16UrnWindowBad DMajor u ell B R
  let V : InfectionRevealPhysicalState n → ℝ≥0∞ :=
    fun z =>
      everHit Bad urnStopped
        (infectionInactiveCounts z.inactive)
  let μ :=
    lemma17PhysicalStageKernel n h3 k A G T s
  have hinitialTotal :
      s.coarse.1.active + (B + R) = n := by
    have htotal := infectionReveal_active_add_inactive s
    have hlabels :=
      InfectionInactiveView.xIds_card_add_yIds_card
        s.inactive
    omega
  have hmass :
      terminalFailureMass μ
          (fun z =>
            z.inactive.yIds.card ≤
              z.inactive.xIds.card)
        ≤ expect μ V := by
    unfold terminalFailureMass expect
    exact ENNReal.tsum_le_tsum fun z => by
      by_cases hzμ : μ z = 0
      · simp [hzμ]
      · by_cases hmajor :
          z.inactive.yIds.card ≤
            z.inactive.xIds.card
        · simp [hmajor]
        · have hfail :
              z.inactive.xIds.card <
                z.inactive.yIds.card :=
            Nat.lt_of_not_ge hmajor
          have hupper :
              z.coarse.1.active ≤ A + 1 :=
            lemma17PhysicalStageKernel_active_le
              n h3 k A G T s z hanchorActive
              (by simpa [μ] using hzμ)
          have htotal :=
            infectionReveal_active_add_inactive z
          have hlabels :=
            InfectionInactiveView.xIds_card_add_yIds_card
              z.inactive
          have hclock :
              u + 1 ≤
                z.inactive.xIds.card +
                  z.inactive.yIds.card := by
            omega
          have hurn :=
            lemma17_remaining_majority_fail_implies_urnWindowBad
              DMajor u ell B R
              z.inactive.xIds.card
              z.inactive.yIds.card
              hBR hgap hclock hfail hell
          have hV : V z = 1 :=
            everHit_eq_one_of_mem
              Bad urnStopped
              (infectionInactiveCounts z.inactive) hurn
          rw [hV]
          simp [hmajor]
  have hpotential :
      expect μ V ≤ V s := by
    exact
      expect_lemma17PhysicalStageKernel_urnEverHit_le
        n h3 k A G T s hstageRoom hanchorActive Bad
  have hcounts :
      infectionInactiveCounts s.inactive = (B, R) := by
    simp [infectionInactiveCounts, hx0, hy0]
  calc
    terminalFailureMass μ
          (fun z =>
            z.inactive.yIds.card ≤
              z.inactive.xIds.card)
        ≤ expect μ V := hmass
    _ ≤ V s := hpotential
    _ =
        everHit Bad urnStopped (B, R) := by
          simpa [V] using
            congrArg (everHit Bad urnStopped) hcounts
    _ ≤ lemma16UrnError qMajor := by
      unfold everHit
      exact
        lemma17_urn_window_tail_pool
          qMajor DMajor (ell + 1) ell u
          (B + R) B R hqa rfl hBR.symm rfl
          hquarter hell

/-- Project any counted decisive-stage estimate to its physical endpoint. -/
theorem lemma18PhysicalStage_of_counted
    (n : ℕ) (h3 : 3 ≤ n)
    (k A G targetGap T : ℕ)
    (s : InfectionRevealPhysicalState n)
    (ε : ℝ≥0∞)
    (h :
      terminalFailureMass
          (iter (lemma17CountedPathStep n h3 k A G) T
            (lemma17CountedPathInitial s))
          (Lemma18StageGood A targetGap)
        ≤ ε) :
    terminalFailureMass
        (lemma17PhysicalStageKernel
          n h3 k A G T s)
        (Lemma18PhysicalStageGood A targetGap)
      ≤ ε := by
  unfold lemma17PhysicalStageKernel
  rw [terminalFailureMass_map]
  simpa [Lemma18PhysicalStageGood,
    Lemma18StageGood] using h

/-- Combine the decisive active-gap estimate and the inactive-majority
estimate on the same physical endpoint. -/
theorem lemma18PhysicalEntry_of_stage_and_majority
    (n : ℕ) (h3 : 3 ≤ n)
    (k A G targetGap T : ℕ)
    (s : InfectionRevealPhysicalState n)
    (εStage εMajor : ℝ≥0∞)
    (hstage :
      terminalFailureMass
          (lemma17PhysicalStageKernel
            n h3 k A G T s)
          (Lemma18PhysicalStageGood A targetGap)
        ≤ εStage)
    (hmajor :
      terminalFailureMass
          (lemma17PhysicalStageKernel
            n h3 k A G T s)
          (fun z =>
            z.inactive.yIds.card ≤
              z.inactive.xIds.card)
        ≤ εMajor) :
    terminalFailureMass
        (lemma17PhysicalStageKernel
          n h3 k A G T s)
        (Lemma18PhysicalEntryGood A targetGap)
      ≤ εStage + εMajor := by
  have hinter :=
    terminalFailureMass_inter_le
      (lemma17PhysicalStageKernel
        n h3 k A G T s)
      (Lemma18PhysicalStageGood A targetGap)
      (fun z =>
        z.inactive.yIds.card ≤ z.inactive.xIds.card)
  have heq :
      terminalFailureMass
          (lemma17PhysicalStageKernel
            n h3 k A G T s)
          (Lemma18PhysicalEntryGood A targetGap)
        =
          terminalFailureMass
              (lemma17PhysicalStageKernel
                n h3 k A G T s)
              (fun z =>
                Lemma18PhysicalStageGood A targetGap z ∧
                  z.inactive.yIds.card ≤
                    z.inactive.xIds.card) := by
    unfold terminalFailureMass
    apply tsum_congr
    intro z
    by_cases hz :
        Lemma18PhysicalEntryGood A targetGap z
    · have hboth :
          Lemma18PhysicalStageGood A targetGap z ∧
            z.inactive.yIds.card ≤
              z.inactive.xIds.card := by
        simpa [Lemma18PhysicalEntryGood] using hz
      rw [if_pos hz, if_pos hboth]
    · have hnot :
          ¬ (Lemma18PhysicalStageGood A targetGap z ∧
            z.inactive.yIds.card ≤
              z.inactive.xIds.card) := by
        simpa [Lemma18PhysicalEntryGood] using hz
      rw [if_neg hz, if_neg hnot]
  rw [heq]
  exact hinter.trans (add_le_add hstage hmajor)

/-- Physical endpoint statement of the fully instantiated paper stage. -/
theorem lemma18PhysicalStage_paper
    (n qPrefix qEnd rhoPrefix rhoEnd D d
      a k u nu R B A cStar r : ℕ)
    (h3 : 3 ≤ n)
    (ha : 4 ≤ a)
    (hquarterClock : 4 * a ≤ n)
    (hAeq : A = 2 * a)
    (hAle : A ≤ n)
    (hcStar : 128 ≤ cStar)
    (hprefixRadius : rhoPrefix + 1 = D)
    (hendRadius : rhoEnd + 1 = 12 * D)
    (hprefixQa :
      qPrefix * (k + 1) ≤ rhoPrefix ^ 2)
    (hendQa :
      qEnd * (k + 1) ≤ rhoEnd ^ 2)
    (huk : u + k + 1 = nu)
    (hRB : R + B = nu)
    (hquarterPool : 4 * (k + 1) ≤ nu + 1)
    (hpoolScale : nu ≤ k * d)
    (hpoolGap : R + 60 * d * D ≤ B)
    (hmeanActive : A ^ 3 ≤ r * n ^ 2)
    (hguardScale : 60 * D ≤ a)
    (hreactionScale : 1200 * cStar * r ≤ 7 * a)
    (s : InfectionRevealPhysicalState n)
    (hstartActive : a ≤ s.coarse.1.active)
    (hanchorActive : s.coarse.1.active + k = A)
    (hprior :
      s.coarse.1.ay ≤ s.coarse.1.ax + 14 * D)
    (hx0 : s.inactive.xIds.card = B)
    (hy0 : s.inactive.yIds.card = R)
    (hk0 : 0 < k) :
    terminalFailureMass
        (lemma17PhysicalStageKernel
          n h3 k A (30 * D) (cStar * n) s)
        (Lemma18PhysicalStageGood A (2 * D))
      ≤
        lemma18StageError
          qPrefix qEnd a cStar r D := by
  apply
    lemma18PhysicalStage_of_counted
      n h3 k A (30 * D) (2 * D)
      (cStar * n) s
      (lemma18StageError
        qPrefix qEnd a cStar r D)
  exact
    lemma18CountedPath_paper
      n qPrefix qEnd rhoPrefix rhoEnd D d
      a k u nu R B A cStar r h3 ha
      hquarterClock hAeq hAle hcStar
      hprefixRadius hendRadius hprefixQa hendQa
      huk hRB hquarterPool hpoolScale hpoolGap
      hmeanActive hguardScale hreactionScale s
      hstartActive hanchorActive hprior hx0 hy0 hk0

/-- Fully instantiated Lemma 18 endpoint prepared for Lemma 19.  The extra
urn window charges the possible loss of the unrevealed `X` majority, with one
slot reserved for the physical two-activation overshoot. -/
theorem lemma18PhysicalEntry_paper
    (n qPrefix qEnd qMajor rhoPrefix rhoEnd D d
      a k u nu uMajor R B A cStar r : ℕ)
    (h3 : 3 ≤ n)
    (ha : 4 ≤ a)
    (hquarterClock : 4 * a ≤ n)
    (hAeq : A = 2 * a)
    (hstageRoom : A + 4 ≤ n)
    (hcStar : 128 ≤ cStar)
    (hprefixRadius : rhoPrefix + 1 = D)
    (hendRadius : rhoEnd + 1 = 12 * D)
    (hprefixQa :
      qPrefix * (k + 1) ≤ rhoPrefix ^ 2)
    (hendQa :
      qEnd * (k + 1) ≤ rhoEnd ^ 2)
    (hmajorQa :
      qMajor * ((k + 1) + 1) ≤
        (60 * d * D) ^ 2)
    (huk : u + k + 1 = nu)
    (hmajorWindow :
      uMajor + (k + 1) + 1 = nu)
    (hRB : R + B = nu)
    (hquarterPool : 4 * (k + 1) ≤ nu + 1)
    (hmajorQuarter :
      4 * ((k + 1) + 1) ≤ nu + 1)
    (hpoolScale : nu ≤ k * d)
    (hpoolGap : R + 60 * d * D ≤ B)
    (hmeanActive : A ^ 3 ≤ r * n ^ 2)
    (hguardScale : 60 * D ≤ a)
    (hreactionScale : 1200 * cStar * r ≤ 7 * a)
    (s : InfectionRevealPhysicalState n)
    (hstartActive : a ≤ s.coarse.1.active)
    (hanchorActive : s.coarse.1.active + k = A)
    (hprior :
      s.coarse.1.ay ≤ s.coarse.1.ax + 14 * D)
    (hx0 : s.inactive.xIds.card = B)
    (hy0 : s.inactive.yIds.card = R)
    (hk0 : 0 < k) :
    terminalFailureMass
        (lemma17PhysicalStageKernel
          n h3 k A (30 * D) (cStar * n) s)
        (Lemma18PhysicalEntryGood A (2 * D))
      ≤
        lemma18StageError
            qPrefix qEnd a cStar r D +
          lemma16UrnError qMajor := by
  apply
    lemma18PhysicalEntry_of_stage_and_majority
      n h3 k A (30 * D) (2 * D)
      (cStar * n) s
      (lemma18StageError
        qPrefix qEnd a cStar r D)
      (lemma16UrnError qMajor)
  · exact
      lemma18PhysicalStage_paper
        n qPrefix qEnd rhoPrefix rhoEnd D d
        a k u nu R B A cStar r h3 ha
        hquarterClock hAeq
        (by omega) hcStar
        hprefixRadius hendRadius hprefixQa hendQa
        huk hRB hquarterPool hpoolScale hpoolGap
        hmeanActive hguardScale hreactionScale s
        hstartActive hanchorActive hprior hx0 hy0 hk0
  · apply
      lemma18PhysicalStage_inactive_majority_tail
        n h3 qMajor (60 * d * D)
        (k + 1) k uMajor B R A (30 * D)
        (cStar * n) s
    · omega
    · exact hpoolGap
    · exact hx0
    · exact hy0
    · omega
    · exact hmajorQa
    · omega
    · exact hstageRoom
    · exact hanchorActive
    · rfl

end

end Tri

#print axioms Tri.lemma18PhysicalStage_of_counted
#print axioms Tri.lemma18PhysicalStage_inactive_majority_tail
#print axioms Tri.lemma18PhysicalEntry_of_stage_and_majority
#print axioms Tri.lemma18PhysicalStage_paper
#print axioms Tri.lemma18PhysicalEntry_paper
