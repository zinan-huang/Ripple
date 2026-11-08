/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Theorem6PostLateApply
import Tri.Lemma18Explicit

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
    lemma16_to_19_critical_landing_coarse_linear_clock_complete_of_decisive
    {n γ cStar R : ℕ}
    {hn : 0 < n}
    {hcStar : 0 < cStar}
    {s : InfectionRevealPhysicalState n}
    (I : InfectionInitialParams s
      (theorem6InitialScale n γ))
    (hN : 0 < theorem6Q n γ * n)
    (hlarge :
      theorem6CStarSq *
          (theorem6CStarSq + 6) ≤ n)
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
      ∀ j ≤ lemma17StageCount n
          (theorem6InitialScale n γ) S.hpositive,
        76 * cStar *
            lemma17ReactionLower n
              (theorem6Q n γ) cStar
              (lemma17Scale
                (theorem6InitialScale n γ) j) ≤
          lemma17Scale
            (theorem6InitialScale n γ) j)
    (hRlt : R < n)
    (hSq : theorem6Q n γ * n ≤ R ^ 2)
    (hLanding :
      lemma17LandingRho
          (theorem6InitialRadius
            (theorem6Q n γ)
            (theorem6InitialScale n γ))
          (lemma17StageCount n
            (theorem6InitialScale n γ) S.hpositive) ≤
        R)
    (hguard :
      60 *
          lemma19Ddec theorem6PostStages
            (4 * R) cStar R ≤
        theorem6CriticalScale n)
    (hfit18 :
      1200 * cStar *
          lemma17ReactionLower n
            (theorem6Q n γ) cStar
            (theorem6CriticalScale n) ≤
        7 * theorem6CriticalScale n) :=
  fun F H hmajor0 hLadderGap hInitialGap
      hGapShrink hGapQa =>
    lemma16_to_19_critical_landing_coarse_linear_clock_complete_of_postLate
      I hN hlarge hγ hcStar16 hqLarge S hbias hfit
      (lemma18ParameterFacts_explicit
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
  Tri.lemma16_to_19_critical_landing_coarse_linear_clock_complete_of_decisive
