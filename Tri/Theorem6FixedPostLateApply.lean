/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Theorem6FixedPrefixApply
import Tri.Lemma16To19FixedPostExplicit
import Tri.Lemma16To19FixedLateExplicit

/-!
# Apply the explicit post-critical and late certificates

The same terminal radius supplies the post-critical radii, the late target
gap and safety radius, and both fourfold late reserves.
-/

namespace Tri

noncomputable section

/-- Apply the concrete prefix route to the explicit post-critical and late
certificates. -/
noncomputable def
    lemma16_to_19_fixed_landing_coarse_headline_complete_of_postLate
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
    (E : Lemma18FixedParameterFacts
      n (theorem6Q n γ) cStar
      (lemma19FixedDdec theorem6FixedPostStages
        (4 * R) cStar R)
      (lemma17FixedLandingRho
        (theorem6InitialRadius
          (theorem6Q n γ)
          (theorem6InitialScale n γ))
        (lemma17FixedStageCount n
          (theorem6InitialScale n γ) S.hpositive))
      hn hcStar)
    (hRlt : R < n)
    (hSq : theorem6Q n γ * n ≤ R ^ 2) :=
  fun F H hmajor0 hLadderGap hInitialGap
      hGapShrink hGapQa =>
    lemma16_to_19_fixed_landing_coarse_headline_complete_of_theorem6Prefix
      I hN hlarge hγ hcStar16 hqLarge S hbias hfit
      (lemma16To19FixedPostFacts_explicit
        n γ cStar
        (theorem6InitialScale n γ)
        (theorem6InitialRadius
          (theorem6Q n γ)
          (theorem6InitialScale n γ))
        R hn
        (le_trans (by norm_num : 2 ≤ 640) hcStar16)
        S.hpositive hlarge
        (theorem6FixedPrefixFacts
          n γ cStar hN hcStar S hqLarge hbias hfit)
        hSq)
      E
      (lemma16To19FixedLateFacts_explicit
        n (theorem6Q n γ) R hN hRlt hSq)
      F H hmajor0 hLadderGap hInitialGap
      hGapShrink hGapQa

end

end Tri

#print axioms
  Tri.lemma16_to_19_fixed_landing_coarse_headline_complete_of_postLate
