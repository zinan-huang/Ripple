/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Theorem6FixedPostLateApply
import Tri.Lemma18FixedExplicit

/-!
# Apply the explicit decisive-stage certificate

This is the fully assembled fixed activation route up to the remaining
initial-majority and gap-bridge inequalities.
-/

namespace Tri

noncomputable section

/-- Apply the concrete prefix, decisive, post-critical, and late certificates
with one shared terminal radius. -/
noncomputable def
    lemma16_to_19_fixed_landing_coarse_headline_complete_of_decisive
    {n γ cStar R : ℕ}
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
    (hRlt : R < n)
    (hSq : theorem6Q n γ * n ≤ R ^ 2)
    (hLanding :
      lemma17FixedLandingRho
          (theorem6InitialRadius
            (theorem6Q n γ)
            (theorem6InitialScale n γ))
          (lemma17FixedStageCount n
            (theorem6InitialScale n γ) S.hpositive) ≤
        R)
    (hguard :
      60 *
          lemma19FixedDdec theorem6FixedPostStages
            (4 * R) cStar R ≤
        theorem6FixedCriticalScale n)
    (hfit18 :
      1200 * cStar *
          lemma17FixedReactionLower n
            (theorem6Q n γ) cStar
            (theorem6FixedCriticalScale n) ≤
        7 * theorem6FixedCriticalScale n) :=
  fun F H hmajor0 hLadderGap hInitialGap
      hGapShrink hGapQa =>
    lemma16_to_19_fixed_landing_coarse_headline_complete_of_postLate
      I hN hlarge hγ hcStar16 hqLarge S hbias hfit
      (lemma18FixedParameterFacts_explicit
        n γ cStar
        (theorem6InitialScale n γ)
        (theorem6InitialRadius
          (theorem6Q n γ)
          (theorem6InitialScale n γ))
        R hn hcStar S.hpositive hlarge hLanding
        hSq hguard hfit18)
      hRlt hSq F H hmajor0 hLadderGap
      hInitialGap hGapShrink hGapQa

end

end Tri

#print axioms
  Tri.lemma16_to_19_fixed_landing_coarse_headline_complete_of_decisive
