/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.InfectionInitialParams
import Tri.Lemma17FixedPrefixFacts
import Tri.Lemma16To19FixedPost
import Tri.Lemma18FixedParameters
import Tri.Lemma16To19FixedLate

/-!
# Simultaneous application of the fixed activation certificates

This module fixes every family and every dependent parameter supplied by the
initial, prefix, decisive, post-critical, and late-stage certificates.  The
remaining function arguments are the genuine initial-majority and gap-bridge
conditions, together with the initial fifth-root condition.
-/

namespace Tri

noncomputable section

/-- Apply the complete route simultaneously to all five fixed certificates.

The ladder uses the last ordinary Lemma 17 scale and radius.  The gap stage
uses the fixed critical scale.  Their positivity, square, room, and clock
conditions are discharged here; only their additive complements and genuine
gap inequalities remain.
-/
noncomputable def
    lemma16_to_19_fixed_landing_coarse_headline_complete_of_fixedFacts
    {n γ cStar a rho Dlate R19 Dlabel Mlate targetGap : ℕ}
    {hn : 0 < n}
    {hcStar : 0 < cStar}
    {ha : 0 < a}
    {s : InfectionRevealPhysicalState n}
    (I : InfectionInitialParams s a)
    (ha2 : 2 ≤ a)
    (hlarge :
      theorem6FixedCStarSq *
          (theorem6FixedCStarSq + 6) ≤ n)
    (hγ : 2 ≤ γ)
    (hcStar16 : 640 ≤ cStar)
    (hqLarge : 8192 ≤ theorem6Q n γ)
    (P : Lemma17FixedPrefixFacts
      n (theorem6Q n γ) cStar a rho hn hcStar ha)
    (O : Lemma16To19FixedPostFacts
      n (theorem6Q n γ) cStar Dlate R19)
    (E : Lemma18FixedParameterFacts
      n (theorem6Q n γ) cStar
      (lemma19FixedDdec theorem6FixedPostStages
        Dlate cStar R19)
      (lemma17FixedLandingRho rho
        (lemma17FixedStageCount n a ha))
      hn hcStar)
    (T : Lemma16To19FixedLateFacts
      n (theorem6Q n γ) Dlate Dlabel Mlate targetGap) :=
  lemma16_to_19_fixed_landing_coarse_headline_complete
    (n := n)
    (q := theorem6Q n γ)
    (a16 := a)
    (k16 := I.k16)
    (u16 := I.u16)
    (nu := I.nu)
    (R := I.R)
    (B := I.B)
    (rho16 := rho)
    (cStar := cStar)
    (mPred := lemma17FixedStageCount n a ha)
    (DLadder :=
      lemma17FixedRho rho
        (lemma17FixedStageCount n a ha))
    (kLadder :=
      lemma17FixedScaleWithLanding a
        (lemma17FixedStageCount n a ha)
        (theorem6FixedCriticalScale n)
        (lemma17FixedStageCount n a ha))
    (rhoLanding :=
      lemma17FixedLandingRho rho
        (lemma17FixedStageCount n a ha))
    (kGap := theorem6FixedCriticalScale n)
    (rhoPrefix :=
      lemma18FixedPrefixRadius
        (lemma19FixedDdec theorem6FixedPostStages
          Dlate cStar R19))
    (rhoEnd :=
      lemma18FixedEndRadius
        (lemma19FixedDdec theorem6FixedPostStages
          Dlate cStar R19))
    (Ddec :=
      lemma19FixedDdec theorem6FixedPostStages
        Dlate cStar R19)
    (r18 :=
      lemma18FixedReaction n (theorem6Q n γ)
        cStar hn hcStar)
    (m19 := theorem6FixedPostStages)
    (Dlate := Dlate)
    (Dlabel := Dlabel)
    (Mlate := Mlate)
    (targetGapLate := targetGap)
    (clockBudget :=
      lemma16To19FixedClockBudget (theorem6Q n γ))
    (scale17 :=
      lemma17FixedScaleWithLanding a
        (lemma17FixedStageCount n a ha)
        (theorem6FixedCriticalScale n))
    (rho17 := lemma17FixedRho rho)
    (rStage :=
      lemma17FixedReactionFamily
        n (theorem6Q n γ) cStar a hn hcStar)
    (scale19 :=
      theorem6FixedPostScale
        (theorem6FixedCriticalScale n))
    (targetGap19 :=
      lemma19FixedTargetGap theorem6FixedPostStages
        Dlate cStar R19)
    (rho19 := lemma19FixedRho R19)
    (r19 :=
      lemma19FixedReaction
        (theorem6FixedPostScale
          (theorem6FixedCriticalScale n)))
    (M19 := lemma19FixedSafety cStar R19)
    (L :=
      lemma16To19FixedErrorScale (theorem6Q n γ))
    (h3 := by
      rw [theorem6FixedCStar_sq] at hlarge
      omega)
    (hlarge := hlarge)
    (hlog := by
      unfold theorem6Q
      nlinarith)
    (hquarter16 := by
      have hmono :=
        lemma17FixedScale_mono a 0
          (lemma17FixedStageCount n a ha) (Nat.zero_le _)
      have hbelow := P.hbelow
      rw [lemma17FixedScaleWithLanding_of_le _ _ _ _
          le_rfl,
        theorem6FixedCStar_sq] at hbelow
      simp only [lemma17FixedScale_zero] at hmono
      omega)
    (hcStar16 := hcStar16)
    (hqa16 :=
      (Nat.mul_le_mul_left (theorem6Q n γ)
        (by omega : a ≤ a + 1)).trans P.hrootBase)
    (hqaOrder16 := P.hqBase)
    (hrho16 := P.hrhoBase)
    (hnu := I.hnu)
    (hk16 := I.hk16)
    (hu16 := I.hsplit16)
    (hRB := I.hRB)
    (hk16pos := I.k16_pos ha2)
    (hscale17_0 := P.hscale0)
    (hrho17_0 := P.hrho0)
    (hcStar := by omega)
    (hcTwo := by omega)
    (hdouble17 := P.hdouble)
    (hroot17 := P.hgrowth)
    (ha17 := P.hscaleLower)
    (hquarter17 := P.hquarter)
    (htarget17 := P.htarget)
    (hrho17 := P.hrho)
    (hbias17 := P.hbias)
    (hactiveScale17 := P.hactiveScale)
    (hmean17 := P.hmean)
    (hqa17 := P.hqa)
    (hlabelRoom17 := P.hlabelRoom)
    (hkLadder := by
      have hscale := P.hscalePredLower
      omega)
    (hLadderQa := P.hqaLanding)
    (hLadderQuarter := by
      have hbelow := P.hbelow
      rw [theorem6FixedCStar_sq] at hbelow
      have hscale := P.hscalePredLower
      have hnu := I.hnu
      have hRB := I.hRB
      omega)
    (hLadderClock := by
      intro j hj
      rw [lemma17FixedScaleWithLanding_of_le _ _ _ _
          (by omega)]
      have hmono :=
        lemma17FixedScale_mono a j
          (lemma17FixedStageCount n a ha) (by omega)
      rw [lemma17FixedScaleWithLanding_of_le _ _ _ _
          le_rfl]
      omega)
    (hLadderClockFinal := by omega)
    (haPred := P.hscalePredLower)
    (hbelow := P.hbelow)
    (habove := P.habove)
    (hrhoPred := P.hrhoPred)
    (hrootLanding := P.hlandingGrowth)
    (hbiasPred := P.hbiasPred)
    (hactiveScaleLanding := P.hactiveScaleLanding)
    (hmeanLanding := P.hmeanLanding)
    (hqaLanding := P.hqaLanding)
    (hkGap := by
      have hscale := E.ha
      omega)
    (hGapQuarter := by
      have hpost := O.hquarter 0 (by
        norm_num [theorem6FixedPostStages])
      rw [O.hscale0] at hpost
      have hscale := E.ha
      have hnu := I.hnu
      have hRB := I.hRB
      calc
        4 * (theorem6FixedCriticalScale n + 1) ≤ n := by
          omega
        _ = I.B + I.R + 1 := by omega)
    (hGapClock := by
      omega)
    (ha18 := E.ha)
    (hquarterClock18 := E.hquarter)
    (hstageRoom18 := E.hstageRoom)
    (hpriorRadius := E.hpriorRadius)
    (hprefixRadius := E.hprefixRadius)
    (hendRadius := E.hendRadius)
    (hprefixQa := E.hprefixQa)
    (hendQa := E.hendQa)
    (hmajorQa := E.hmajorQa)
    (hlabelRoom18 := E.hlabelRoom)
    (hmeanActive18 := E.hmean)
    (hguardScale := E.hguardScale)
    (hreactionScale := E.hreactionScale)
    (hscale19_0 := O.hscale0)
    (hgap19_0 := O.hgap0)
    (hdouble19 := O.hdouble)
    (ha19 := O.ha)
    (hquarter19 := O.hquarter)
    (htarget19 := O.htarget)
    (hmean19 := O.hmean)
    (hqa19 := O.hqa)
    (hlabelRoom19 := O.hlabelRoom)
    (hbudget19 := O.hbudget)
    (hAfinal := O.hfinalScale)
    (hstageRoomFinal := O.hstageRoomFinal)
    (hquarterFinal := O.hquarterFinal)
    (hfinalGap := O.hfinalGap)
    (hscale19LeFinal := O.hscaleLeFinal)
    (hPostWindow := O.hPostWindow)
    (hPostQaGlobal :=
      lemma19FixedPostQaGlobal
        n (theorem6Q n γ) Dlate cStar R19
        O.hPostQaGlobal)
    (hbudgetLate := T.hbudget)
    (hgapLate0 := T.hgap0)
    (hgapLaten := T.hgapn)
    (hDlabel := T.hDlabel)
    (hL := T.hL)
    (hscaleLate := T.hscale)
    (hscaleTarget := P.hscaleTarget)
    (herrorR17 := P.herrorR)
    (herrorQa17 := P.herrorQa)
    (herrorActive17 := P.herrorActive)
    (herrorDirection17 := P.herrorDirection)
    (herrorR18 := E.herror.hr)
    (herrorQa18 := E.herror.hqa)
    (herrorActive18 := E.herror.hactive)
    (herrorDirection18 := E.herror.hdirection)
    (herrorR19 := O.herrorR)
    (herrorQa19 := O.herrorQa)
    (herrorActive19 := O.herrorActive)
    (herrorDirection19 := O.herrorDirection)
    (hq := by omega)
    (hlog3 := by
      have hpost :=
        theorem6FixedPostStages_add_two_le_log n hlarge
      norm_num [theorem6FixedPostStages] at hpost
      omega)
    (hbudgetLower := T.hbudgetLower)
    (hbudgetUpper := T.hbudgetUpper)
    (herrorL := T.herrorL)
    (hgapSq := T.hgapSq)
    (hM := T.hM)
    (hm := by
      have hmono :=
        lemma17FixedScale_mono a 0
          (lemma17FixedStageCount n a ha) (Nat.zero_le _)
      have hbase : theorem6FixedCStarSq * a < n := by
        have hbelow := P.hbelow
        rw [lemma17FixedScaleWithLanding_of_le _ _ _ _
            le_rfl] at hbelow
        simp only [lemma17FixedScale_zero] at hmono
        exact
          (Nat.mul_le_mul_left theorem6FixedCStarSq
            hmono).trans_lt hbelow
      exact
        lemma17FixedStageCount_add_post_le_theorem6Q
          n γ a ha hbase hγ
          (theorem6FixedPostStages_add_two_le_log n hlarge))
    (hqLarge := hqLarge)
    (s := s)
    (hx0 := I.hx0)
    (hy0 := I.hy0)

end

end Tri

#print axioms
  Tri.lemma16_to_19_fixed_landing_coarse_headline_complete_of_fixedFacts
