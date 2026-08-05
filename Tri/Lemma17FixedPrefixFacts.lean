/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Lemma17FixedSchedule

/-!
# Complete fixed Lemma 17 prefix certificate

This package forwards the dyadic scale, radius, and least-reaction choices
through the custom fixed landing slot.  Its only indexed scalar premise is
the explicit integral reaction interval fit.
-/

namespace Tri

noncomputable section

/-- All ordinary-prefix, custom-source, and error-envelope hypotheses supplied
by the fixed Lemma 17 choices. -/
structure Lemma17FixedPrefixFacts
    (n q cStar a rho : ℕ)
    (hn : 0 < n)
    (hcStar : 0 < cStar)
    (ha : 0 < a) : Prop where
  hqBase :
    q ≤ a
  hrhoBase :
    1 ≤ rho
  hrootBase :
    q * (a + 1) ≤ rho ^ 2
  hscale0 :
    lemma17FixedScaleWithLanding a
        (lemma17FixedStageCount n a ha)
        (theorem6FixedCriticalScale n) 0 =
      a
  hrho0 :
    lemma17FixedRho rho 0 = rho
  hdouble :
    ∀ j < lemma17FixedStageCount n a ha,
      lemma17FixedScaleWithLanding a
          (lemma17FixedStageCount n a ha)
          (theorem6FixedCriticalScale n) (j + 1) =
        2 * lemma17FixedScaleWithLanding a
          (lemma17FixedStageCount n a ha)
          (theorem6FixedCriticalScale n) j
  hgrowth :
    ∀ j < lemma17FixedStageCount n a ha,
      19 * lemma17FixedRho rho j ≤
        14 * lemma17FixedRho rho (j + 1)
  hscaleLower :
    ∀ j < lemma17FixedStageCount n a ha,
      4 ≤ lemma17FixedScaleWithLanding a
        (lemma17FixedStageCount n a ha)
        (theorem6FixedCriticalScale n) j
  hquarter :
    ∀ j < lemma17FixedStageCount n a ha,
      4 * lemma17FixedScaleWithLanding a
          (lemma17FixedStageCount n a ha)
          (theorem6FixedCriticalScale n) j ≤
        n
  htarget :
    ∀ j < lemma17FixedStageCount n a ha,
      2 * lemma17FixedScaleWithLanding a
          (lemma17FixedStageCount n a ha)
          (theorem6FixedCriticalScale n) j ≤
        n
  hrho :
    ∀ j < lemma17FixedStageCount n a ha,
      1 ≤ lemma17FixedRho rho j
  hbias :
    ∀ j < lemma17FixedStageCount n a ha,
      38 * cStar * lemma17FixedRho rho j ≤
        lemma17FixedScaleWithLanding a
          (lemma17FixedStageCount n a ha)
          (theorem6FixedCriticalScale n) j
  hactiveScale :
    ∀ j < lemma17FixedStageCount n a ha,
      76 * cStar *
          lemma17FixedReactionFamily
            n q cStar a hn hcStar j ≤
        lemma17FixedScaleWithLanding a
          (lemma17FixedStageCount n a ha)
          (theorem6FixedCriticalScale n) j
  hmean :
    ∀ j < lemma17FixedStageCount n a ha,
      (2 * lemma17FixedScaleWithLanding a
          (lemma17FixedStageCount n a ha)
          (theorem6FixedCriticalScale n) j) ^ 3 ≤
        lemma17FixedReactionFamily
            n q cStar a hn hcStar j *
          n ^ 2
  hqa :
    ∀ j < lemma17FixedStageCount n a ha,
      q * (lemma17FixedScaleWithLanding a
            (lemma17FixedStageCount n a ha)
            (theorem6FixedCriticalScale n) j + 1) ≤
        (lemma17FixedRho rho j) ^ 2
  hlabelRoom :
    ∀ j < lemma17FixedStageCount n a ha,
      5 * (lemma17FixedScaleWithLanding a
              (lemma17FixedStageCount n a ha)
              (theorem6FixedCriticalScale n) j + 1) ≤
        n + 1
  hscalePredLower :
    4 ≤ lemma17FixedScaleWithLanding a
      (lemma17FixedStageCount n a ha)
      (theorem6FixedCriticalScale n)
      (lemma17FixedStageCount n a ha)
  hbelow :
    theorem6FixedCStarSq *
        lemma17FixedScaleWithLanding a
          (lemma17FixedStageCount n a ha)
          (theorem6FixedCriticalScale n)
          (lemma17FixedStageCount n a ha) <
      n
  habove :
    n ≤ theorem6FixedCStarSq *
      (2 * lemma17FixedScaleWithLanding a
        (lemma17FixedStageCount n a ha)
        (theorem6FixedCriticalScale n)
        (lemma17FixedStageCount n a ha))
  hrhoPred :
    1 ≤ lemma17FixedRho rho
      (lemma17FixedStageCount n a ha)
  hlandingGrowth :
    19 * lemma17FixedRho rho
        (lemma17FixedStageCount n a ha) ≤
      14 * lemma17FixedLandingRho rho
        (lemma17FixedStageCount n a ha)
  hbiasPred :
    38 * cStar * lemma17FixedRho rho
        (lemma17FixedStageCount n a ha) ≤
      lemma17FixedScaleWithLanding a
        (lemma17FixedStageCount n a ha)
        (theorem6FixedCriticalScale n)
        (lemma17FixedStageCount n a ha)
  hactiveScaleLanding :
    76 * cStar *
        lemma17FixedReactionFamily
          n q cStar a hn hcStar
          (lemma17FixedStageCount n a ha) ≤
      lemma17FixedScaleWithLanding a
        (lemma17FixedStageCount n a ha)
        (theorem6FixedCriticalScale n)
        (lemma17FixedStageCount n a ha)
  hmeanLanding :
    (theorem6FixedCriticalScale n) ^ 3 ≤
      lemma17FixedReactionFamily
          n q cStar a hn hcStar
          (lemma17FixedStageCount n a ha) *
        n ^ 2
  hqaLanding :
    q * (lemma17FixedScaleWithLanding a
          (lemma17FixedStageCount n a ha)
          (theorem6FixedCriticalScale n)
          (lemma17FixedStageCount n a ha) + 1) ≤
      (lemma17FixedRho rho
        (lemma17FixedStageCount n a ha)) ^ 2
  hscaleTarget :
    lemma17FixedScaleWithLanding a
        (lemma17FixedStageCount n a ha)
        (theorem6FixedCriticalScale n)
        (lemma17FixedStageCount n a ha + 1) =
      theorem6FixedCriticalScale n
  herrorR :
    ∀ j < lemma17FixedStageCount n a ha + 1,
      0 <
        lemma17FixedReactionFamily
          n q cStar a hn hcStar j
  herrorQa :
    ∀ j < lemma17FixedStageCount n a ha + 1,
      q ≤ lemma17FixedScaleWithLanding a
        (lemma17FixedStageCount n a ha)
        (theorem6FixedCriticalScale n) j
  herrorActive :
    ∀ j < lemma17FixedStageCount n a ha + 1,
      15 * q ≤
        4 * cStar *
          lemma17FixedReactionFamily
            n q cStar a hn hcStar j
  herrorDirection :
    ∀ j < lemma17FixedStageCount n a ha + 1,
      3 * q *
          lemma17FixedReactionFamily
            n q cStar a hn hcStar j ≤
        4 * cStar * (lemma17FixedRho rho j) ^ 2

/-- The fixed prefix certificate follows from scalar base radius conditions,
the strict initial bracket, and the exact integral reaction fit. -/
theorem lemma17FixedPrefixFacts
    (n q cStar a rho : ℕ)
    (hn : 0 < n)
    (hcStar : 0 < cStar)
    (ha4 : 4 ≤ a)
    (hbase : theorem6FixedCStarSq * a < n)
    (hq0 : q ≤ a)
    (hrho : 23 ≤ rho)
    (hbias : 38 * cStar * rho ≤ a)
    (hroot : q * (a + 1) ≤ rho ^ 2)
    (hfit :
      ∀ j ≤ lemma17FixedStageCount n a (by omega),
        76 * cStar *
            lemma17FixedReactionLower n q cStar
              (lemma17FixedScale a j) ≤
          lemma17FixedScale a j) :
    Lemma17FixedPrefixFacts
      n q cStar a rho hn hcStar (by omega) := by
  let ha : 0 < a := by omega
  let m := lemma17FixedStageCount n a ha
  have S :=
    lemma17FixedScaleRoomFacts
      n a ha hbase ha4
  have R :=
    lemma17FixedRadiusFacts
      q a cStar rho m hrho hbias hroot
  have A :=
    lemma17FixedReactionFacts_of_fit
      n q cStar a rho m hn hcStar hq0 (by omega) hroot
      (by
        intro j hj
        exact hfit j (by simpa [ha, m] using hj))
  have W :=
    lemma17FixedLandingFacts n
      (lemma17FixedScale a m) S.hbelow S.habove
  refine
    { hqBase := hq0
      hrhoBase := by omega
      hrootBase := hroot
      hscale0 := by
        simpa [ha, m] using
          lemma17FixedScaleWithLanding_zero
            a m (theorem6FixedCriticalScale n)
      hrho0 := R.hrho0
      hdouble := ?_
      hgrowth := ?_
      hscaleLower := ?_
      hquarter := ?_
      htarget := ?_
      hrho := ?_
      hbias := ?_
      hactiveScale := ?_
      hmean := ?_
      hqa := ?_
      hlabelRoom := ?_
      hscalePredLower := ?_
      hbelow := ?_
      habove := ?_
      hrhoPred := ?_
      hlandingGrowth := R.hlandingGrowth
      hbiasPred := ?_
      hactiveScaleLanding := ?_
      hmeanLanding := ?_
      hqaLanding := ?_
      hscaleTarget := by
        simpa [ha, m] using
          lemma17FixedScaleWithLanding_target
            a m (theorem6FixedCriticalScale n)
      herrorR := ?_
      herrorQa := ?_
      herrorActive := ?_
      herrorDirection := ?_ }
  · intro j hj
    simpa [ha, m] using
      lemma17FixedScaleWithLanding_succ
        a m (theorem6FixedCriticalScale n) j
        (by simpa [m] using hj)
  · intro j hj
    exact R.hgrowth j (by simpa [m] using hj)
  · intro j hj
    rw [lemma17FixedScaleWithLanding_of_le _ _ _ _
      (by omega)]
    exact S.hscaleLower j (by omega)
  · intro j hj
    rw [lemma17FixedScaleWithLanding_of_le _ _ _ _
      (by omega)]
    exact S.hquarter j (by omega)
  · intro j hj
    rw [lemma17FixedScaleWithLanding_of_le _ _ _ _
      (by omega)]
    exact S.htarget j (by omega)
  · intro j hj
    exact R.hpositive j (by omega)
  · intro j hj
    rw [lemma17FixedScaleWithLanding_of_le _ _ _ _
      (by omega)]
    exact R.hbias j (by omega)
  · intro j hj
    rw [lemma17FixedScaleWithLanding_of_le _ _ _ _
      (by omega)]
    exact A.hupper j (by omega)
  · intro j hj
    rw [lemma17FixedScaleWithLanding_of_le _ _ _ _
      (by omega)]
    exact A.hmean j (by omega)
  · intro j hj
    rw [lemma17FixedScaleWithLanding_of_le _ _ _ _
      (by omega)]
    exact R.hroot j (by omega)
  · intro j hj
    rw [lemma17FixedScaleWithLanding_of_le _ _ _ _
      (by omega)]
    exact S.hlabelRoom j (by omega)
  · simpa [ha, m,
      lemma17FixedScaleWithLanding_of_le] using
        S.hscaleLower m le_rfl
  · simpa [ha, m,
      lemma17FixedScaleWithLanding_of_le] using
        S.hbelow
  · simpa [ha, m,
      lemma17FixedScaleWithLanding_of_le] using
        S.habove
  · exact R.hpositive m le_rfl
  · simpa [ha, m,
      lemma17FixedScaleWithLanding_of_le] using
        R.hbias m le_rfl
  · simpa [ha, m,
      lemma17FixedScaleWithLanding_of_le] using
        A.hupper m le_rfl
  · have hpow :
        (theorem6FixedCriticalScale n) ^ 3 ≤
          (2 * lemma17FixedScale a m) ^ 3 :=
      Nat.pow_le_pow_left W.htargetUpper 3
    exact hpow.trans (A.hmean m le_rfl)
  · simpa [ha, m,
      lemma17FixedScaleWithLanding_of_le] using
        R.hroot m le_rfl
  · intro j hj
    exact A.hpositive j (by omega)
  · intro j hj
    rw [lemma17FixedScaleWithLanding_of_le _ _ _ _
      (by omega)]
    exact A.hqscale j (by omega)
  · intro j hj
    exact A.hactive j (by omega)
  · intro j hj
    exact A.hdirection j (by omega)

end

end Tri

#print axioms Tri.lemma17FixedPrefixFacts
