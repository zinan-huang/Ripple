/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Lemma17LandingSchedule

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
structure Lemma17PrefixFacts
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
    lemma17ScaleWithLanding a
        (lemma17StageCount n a ha)
        (theorem6CriticalScale n) 0 =
      a
  hrho0 :
    lemma17Rho rho 0 = rho
  hdouble :
    ∀ j < lemma17StageCount n a ha,
      lemma17ScaleWithLanding a
          (lemma17StageCount n a ha)
          (theorem6CriticalScale n) (j + 1) =
        2 * lemma17ScaleWithLanding a
          (lemma17StageCount n a ha)
          (theorem6CriticalScale n) j
  hgrowth :
    ∀ j < lemma17StageCount n a ha,
      19 * lemma17Rho rho j ≤
        14 * lemma17Rho rho (j + 1)
  hscaleLower :
    ∀ j < lemma17StageCount n a ha,
      4 ≤ lemma17ScaleWithLanding a
        (lemma17StageCount n a ha)
        (theorem6CriticalScale n) j
  hquarter :
    ∀ j < lemma17StageCount n a ha,
      4 * lemma17ScaleWithLanding a
          (lemma17StageCount n a ha)
          (theorem6CriticalScale n) j ≤
        n
  htarget :
    ∀ j < lemma17StageCount n a ha,
      2 * lemma17ScaleWithLanding a
          (lemma17StageCount n a ha)
          (theorem6CriticalScale n) j ≤
        n
  hrho :
    ∀ j < lemma17StageCount n a ha,
      1 ≤ lemma17Rho rho j
  hbias :
    ∀ j < lemma17StageCount n a ha,
      38 * cStar * lemma17Rho rho j ≤
        lemma17ScaleWithLanding a
          (lemma17StageCount n a ha)
          (theorem6CriticalScale n) j
  hactiveScale :
    ∀ j < lemma17StageCount n a ha,
      76 * cStar *
          lemma17ReactionFamily
            n q cStar a hn hcStar j ≤
        lemma17ScaleWithLanding a
          (lemma17StageCount n a ha)
          (theorem6CriticalScale n) j
  hmean :
    ∀ j < lemma17StageCount n a ha,
      (2 * lemma17ScaleWithLanding a
          (lemma17StageCount n a ha)
          (theorem6CriticalScale n) j) ^ 3 ≤
        lemma17ReactionFamily
            n q cStar a hn hcStar j *
          n ^ 2
  hqa :
    ∀ j < lemma17StageCount n a ha,
      q * (lemma17ScaleWithLanding a
            (lemma17StageCount n a ha)
            (theorem6CriticalScale n) j + 1) ≤
        (lemma17Rho rho j) ^ 2
  hlabelRoom :
    ∀ j < lemma17StageCount n a ha,
      5 * (lemma17ScaleWithLanding a
              (lemma17StageCount n a ha)
              (theorem6CriticalScale n) j + 1) ≤
        n + 1
  hscalePredLower :
    4 ≤ lemma17ScaleWithLanding a
      (lemma17StageCount n a ha)
      (theorem6CriticalScale n)
      (lemma17StageCount n a ha)
  hbelow :
    theorem6CStarSq *
        lemma17ScaleWithLanding a
          (lemma17StageCount n a ha)
          (theorem6CriticalScale n)
          (lemma17StageCount n a ha) <
      n
  habove :
    n ≤ theorem6CStarSq *
      (2 * lemma17ScaleWithLanding a
        (lemma17StageCount n a ha)
        (theorem6CriticalScale n)
        (lemma17StageCount n a ha))
  hrhoPred :
    1 ≤ lemma17Rho rho
      (lemma17StageCount n a ha)
  hlandingGrowth :
    19 * lemma17Rho rho
        (lemma17StageCount n a ha) ≤
      14 * lemma17LandingRho rho
        (lemma17StageCount n a ha)
  hbiasPred :
    38 * cStar * lemma17Rho rho
        (lemma17StageCount n a ha) ≤
      lemma17ScaleWithLanding a
        (lemma17StageCount n a ha)
        (theorem6CriticalScale n)
        (lemma17StageCount n a ha)
  hactiveScaleLanding :
    76 * cStar *
        lemma17ReactionFamily
          n q cStar a hn hcStar
          (lemma17StageCount n a ha) ≤
      lemma17ScaleWithLanding a
        (lemma17StageCount n a ha)
        (theorem6CriticalScale n)
        (lemma17StageCount n a ha)
  hmeanLanding :
    (theorem6CriticalScale n) ^ 3 ≤
      lemma17ReactionFamily
          n q cStar a hn hcStar
          (lemma17StageCount n a ha) *
        n ^ 2
  hqaLanding :
    q * (lemma17ScaleWithLanding a
          (lemma17StageCount n a ha)
          (theorem6CriticalScale n)
          (lemma17StageCount n a ha) + 1) ≤
      (lemma17Rho rho
        (lemma17StageCount n a ha)) ^ 2
  hscaleTarget :
    lemma17ScaleWithLanding a
        (lemma17StageCount n a ha)
        (theorem6CriticalScale n)
        (lemma17StageCount n a ha + 1) =
      theorem6CriticalScale n
  herrorR :
    ∀ j < lemma17StageCount n a ha + 1,
      0 <
        lemma17ReactionFamily
          n q cStar a hn hcStar j
  herrorQa :
    ∀ j < lemma17StageCount n a ha + 1,
      q ≤ lemma17ScaleWithLanding a
        (lemma17StageCount n a ha)
        (theorem6CriticalScale n) j
  herrorActive :
    ∀ j < lemma17StageCount n a ha + 1,
      15 * q ≤
        4 * cStar *
          lemma17ReactionFamily
            n q cStar a hn hcStar j
  herrorDirection :
    ∀ j < lemma17StageCount n a ha + 1,
      3 * q *
          lemma17ReactionFamily
            n q cStar a hn hcStar j ≤
        4 * cStar * (lemma17Rho rho j) ^ 2

/-- The fixed prefix certificate follows from scalar base radius conditions,
the strict initial bracket, and the exact integral reaction fit. -/
theorem lemma17PrefixFacts
    (n q cStar a rho : ℕ)
    (hn : 0 < n)
    (hcStar : 0 < cStar)
    (ha4 : 4 ≤ a)
    (hbase : theorem6CStarSq * a < n)
    (hq0 : q ≤ a)
    (hrho : 23 ≤ rho)
    (hbias : 38 * cStar * rho ≤ a)
    (hroot : q * (a + 1) ≤ rho ^ 2)
    (hfit :
      ∀ j ≤ lemma17StageCount n a (by omega),
        76 * cStar *
            lemma17ReactionLower n q cStar
              (lemma17Scale a j) ≤
          lemma17Scale a j) :
    Lemma17PrefixFacts
      n q cStar a rho hn hcStar (by omega) := by
  let ha : 0 < a := by omega
  let m := lemma17StageCount n a ha
  have S :=
    lemma17ScaleRoomFacts
      n a ha hbase ha4
  have R :=
    lemma17RadiusFacts
      q a cStar rho m hrho hbias hroot
  have A :=
    lemma17ReactionFacts_of_fit
      n q cStar a rho m hn hcStar hq0 (by omega) hroot
      (by
        intro j hj
        exact hfit j (by simpa [ha, m] using hj))
  have W :=
    lemma17LandingFacts n
      (lemma17Scale a m) S.hbelow S.habove
  refine
    { hqBase := hq0
      hrhoBase := by omega
      hrootBase := hroot
      hscale0 := by
        simpa [ha, m] using
          lemma17ScaleWithLanding_zero
            a m (theorem6CriticalScale n)
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
          lemma17ScaleWithLanding_target
            a m (theorem6CriticalScale n)
      herrorR := ?_
      herrorQa := ?_
      herrorActive := ?_
      herrorDirection := ?_ }
  · intro j hj
    simpa [ha, m] using
      lemma17ScaleWithLanding_succ
        a m (theorem6CriticalScale n) j
        (by simpa [m] using hj)
  · intro j hj
    exact R.hgrowth j (by simpa [m] using hj)
  · intro j hj
    rw [lemma17ScaleWithLanding_of_le _ _ _ _
      (by omega)]
    exact S.hscaleLower j (by omega)
  · intro j hj
    rw [lemma17ScaleWithLanding_of_le _ _ _ _
      (by omega)]
    exact S.hquarter j (by omega)
  · intro j hj
    rw [lemma17ScaleWithLanding_of_le _ _ _ _
      (by omega)]
    exact S.htarget j (by omega)
  · intro j hj
    exact R.hpositive j (by omega)
  · intro j hj
    rw [lemma17ScaleWithLanding_of_le _ _ _ _
      (by omega)]
    exact R.hbias j (by omega)
  · intro j hj
    rw [lemma17ScaleWithLanding_of_le _ _ _ _
      (by omega)]
    exact A.hupper j (by omega)
  · intro j hj
    rw [lemma17ScaleWithLanding_of_le _ _ _ _
      (by omega)]
    exact A.hmean j (by omega)
  · intro j hj
    rw [lemma17ScaleWithLanding_of_le _ _ _ _
      (by omega)]
    exact R.hroot j (by omega)
  · intro j hj
    rw [lemma17ScaleWithLanding_of_le _ _ _ _
      (by omega)]
    exact S.hlabelRoom j (by omega)
  · simpa [ha, m,
      lemma17ScaleWithLanding_of_le] using
        S.hscaleLower m le_rfl
  · simpa [ha, m,
      lemma17ScaleWithLanding_of_le] using
        S.hbelow
  · simpa [ha, m,
      lemma17ScaleWithLanding_of_le] using
        S.habove
  · exact R.hpositive m le_rfl
  · simpa [ha, m,
      lemma17ScaleWithLanding_of_le] using
        R.hbias m le_rfl
  · simpa [ha, m,
      lemma17ScaleWithLanding_of_le] using
        A.hupper m le_rfl
  · have hpow :
        (theorem6CriticalScale n) ^ 3 ≤
          (2 * lemma17Scale a m) ^ 3 :=
      Nat.pow_le_pow_left W.htargetUpper 3
    exact hpow.trans (A.hmean m le_rfl)
  · simpa [ha, m,
      lemma17ScaleWithLanding_of_le] using
        R.hroot m le_rfl
  · intro j hj
    exact A.hpositive j (by omega)
  · intro j hj
    rw [lemma17ScaleWithLanding_of_le _ _ _ _
      (by omega)]
    exact A.hqscale j (by omega)
  · intro j hj
    exact A.hactive j (by omega)
  · intro j hj
    exact A.hdirection j (by omega)

end

end Tri

#print axioms Tri.lemma17PrefixFacts
