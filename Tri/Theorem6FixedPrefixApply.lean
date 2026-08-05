/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Theorem6FixedPrefix
import Tri.Lemma16To19FixedBridge

/-!
# Apply the concrete Theorem 6 prefix

The initial activation scale is the quotient by the binary fifth-root upper
bound, and the initial label radius is its positive upper square root.  The
initial-scale certificate discharges the fifth-power premise of the complete
activation route.
-/

namespace Tri

noncomputable section

/-- Apply the fixed activation route to the concrete initial scale, radius,
and prefix certificate. -/
noncomputable def
    lemma16_to_19_fixed_landing_coarse_headline_complete_of_theorem6Prefix
    {n γ cStar Dlate R19 Dlabel Mlate targetGap : ℕ}
    {hn : 0 < n}
    {hcStar : 0 < cStar}
    {s : InfectionRevealPhysicalState n}
    (I : InfectionInitialParams s
      (theorem6InitialScale n γ))
    (hN : 0 < theorem6Q n γ * n)
    (hlarge :
      theorem6FixedCStarSq *
          (theorem6FixedCStarSq + 6) ≤ n)
    (hγ : 2 ≤ γ)
    (hcStar16 : 640 ≤ cStar)
    (hqLarge : 8192 ≤ theorem6Q n γ)
    (S : Theorem6InitialScaleFacts n γ)
    (hbias :
      38 * cStar *
          theorem6InitialRadius
            (theorem6Q n γ)
            (theorem6InitialScale n γ) ≤
        theorem6InitialScale n γ)
    (hfit :
      ∀ j ≤ lemma17FixedStageCount n
          (theorem6InitialScale n γ) S.hpositive,
        76 * cStar *
            lemma17FixedReactionLower n
              (theorem6Q n γ) cStar
              (lemma17FixedScale
                (theorem6InitialScale n γ) j) ≤
          lemma17FixedScale
            (theorem6InitialScale n γ) j)
    (O : Lemma16To19FixedPostFacts
      n (theorem6Q n γ) cStar Dlate R19)
    (E : Lemma18FixedParameterFacts
      n (theorem6Q n γ) cStar
      (lemma19FixedDdec theorem6FixedPostStages
        Dlate cStar R19)
      (lemma17FixedLandingRho
        (theorem6InitialRadius
          (theorem6Q n γ)
          (theorem6InitialScale n γ))
        (lemma17FixedStageCount n
          (theorem6InitialScale n γ) S.hpositive))
      hn hcStar)
    (T : Lemma16To19FixedLateFacts
      n (theorem6Q n γ) Dlate Dlabel Mlate targetGap) :=
  fun F H hmajor0 hLadderGap hInitialGap
      hGapShrink hGapQa =>
    lemma16_to_19_fixed_landing_coarse_headline_complete_of_bridge
      (hn := hn)
      (hcStar := hcStar)
      (ha := S.hpositive)
      I (by
        have hfour := S.hfour
        omega)
      hlarge hγ hcStar16 hqLarge
      (theorem6FixedPrefixFacts
        n γ cStar hN hcStar S hqLarge hbias hfit)
      O E T F H S.hroot hmajor0 hLadderGap
      hInitialGap hGapShrink hGapQa

end

end Tri

#print axioms
  Tri.lemma16_to_19_fixed_landing_coarse_headline_complete_of_theorem6Prefix
