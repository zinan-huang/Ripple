/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Lemma18FixedParameters
import Tri.Lemma16To19FixedPost

/-!
# Explicit decisive-stage certificate

The decisive reserve is the one induced by the fixed seventeen-stage
post-critical ladder with a fourfold late reserve.  A single terminal square
bound pays both decisive radius squares; only landing containment, guard room,
and the reaction interval remain genuine scalar premises.
-/

namespace Tri

noncomputable section

/-- The fixed post-critical reserve is positive and contains its terminal
radius below its additive predecessor. -/
theorem lemma18FixedTerminalRadius_le_prefix
    (cStar R : ℕ) :
    R ≤
      lemma18FixedPrefixRadius
        (lemma19FixedDdec theorem6FixedPostStages
          (4 * R) cStar R) := by
  let D :=
    lemma19FixedDdec theorem6FixedPostStages
      (4 * R) cStar R
  have hD : 0 < D := by
    dsimp [D, lemma19FixedDdec,
      theorem6FixedPostStages, lemma19FixedHalfDrop]
    omega
  have hR :
      R + 1 ≤ D := by
    dsimp [D, lemma19FixedDdec,
      theorem6FixedPostStages, lemma19FixedHalfDrop]
    omega
  have hpred :=
    lemma18FixedPrefixRadius_add_one D hD
  change R ≤ lemma18FixedPrefixRadius D
  omega

/-- The fixed decisive reserve dominates the landing radius whenever the
terminal post radius does. -/
theorem lemma18FixedLanding_le_reserve
    (cStar rhoLanding R : ℕ)
    (hLanding : rhoLanding ≤ R) :
    cStar * rhoLanding ≤
      lemma19FixedDdec theorem6FixedPostStages
        (4 * R) cStar R := by
  have hmul :
      cStar * rhoLanding ≤ cStar * R :=
    Nat.mul_le_mul_left cStar hLanding
  calc
    cStar * rhoLanding ≤ cStar * R := hmul
    _ ≤
        lemma19FixedDdec theorem6FixedPostStages
          (4 * R) cStar R := by
      simp only [lemma19FixedDdec,
        theorem6FixedPostStages, lemma19FixedHalfDrop]
      nlinarith

/-- Construct the decisive-stage certificate from the global terminal square
and the three genuine interval/containment conditions. -/
theorem lemma18FixedParameterFacts_explicit
    (n γ cStar a rho R : ℕ)
    (hn : 0 < n)
    (hcStar : 0 < cStar)
    (ha : 0 < a)
    (hlarge :
      theorem6FixedCStarSq *
          (theorem6FixedCStarSq + 6) ≤ n)
    (hLanding :
      lemma17FixedLandingRho rho
          (lemma17FixedStageCount n a ha) ≤
        R)
    (hSq : theorem6Q n γ * n ≤ R ^ 2)
    (hguard :
      60 *
          lemma19FixedDdec theorem6FixedPostStages
            (4 * R) cStar R ≤
        theorem6FixedCriticalScale n)
    (hfit :
      1200 * cStar *
          lemma17FixedReactionLower n
            (theorem6Q n γ) cStar
            (theorem6FixedCriticalScale n) ≤
        7 * theorem6FixedCriticalScale n) :
    Lemma18FixedParameterFacts
      n (theorem6Q n γ) cStar
      (lemma19FixedDdec theorem6FixedPostStages
        (4 * R) cStar R)
      (lemma17FixedLandingRho rho
        (lemma17FixedStageCount n a ha))
      hn hcStar := by
  let D :=
    lemma19FixedDdec theorem6FixedPostStages
      (4 * R) cStar R
  obtain ⟨e, W⟩ :=
    lemma19FixedWindowFacts_of_large n hn hlarge
  have hpostQuarter :=
    W.hquarter 0 (by
      norm_num [theorem6FixedPostStages])
  have hpostScale :=
    W.ha 0 (by
      norm_num [theorem6FixedPostStages])
  rw [W.hscale0] at hpostQuarter hpostScale
  have hcriticalOne :
      theorem6FixedCriticalScale n + 1 ≤ n := by
    omega
  have hcriticalTwo :
      theorem6FixedCriticalScale n + 2 ≤ n := by
    omega
  have hD : 0 < D := by
    dsimp [D, lemma19FixedDdec,
      theorem6FixedPostStages, lemma19FixedHalfDrop]
    omega
  have hprefixQa :
      theorem6Q n γ *
          (theorem6FixedCriticalScale n + 1) ≤
        lemma18FixedPrefixRadius D ^ 2 := by
    calc
      theorem6Q n γ *
            (theorem6FixedCriticalScale n + 1)
          ≤ theorem6Q n γ * n :=
        Nat.mul_le_mul_left (theorem6Q n γ)
          hcriticalOne
      _ ≤ R ^ 2 := hSq
      _ ≤ lemma18FixedPrefixRadius D ^ 2 :=
        Nat.pow_le_pow_left
          (by
            dsimp [D]
            exact
              lemma18FixedTerminalRadius_le_prefix
                cStar R)
          2
  have hmajorQa :
      theorem6Q n γ *
          (theorem6FixedCriticalScale n + 2) ≤
        (60 * theorem6FixedPoolMultiplier * D) ^ 2 := by
    calc
      theorem6Q n γ *
            (theorem6FixedCriticalScale n + 2)
          ≤ theorem6Q n γ * n :=
        Nat.mul_le_mul_left (theorem6Q n γ)
          hcriticalTwo
      _ ≤ R ^ 2 := hSq
      _ ≤ (60 * theorem6FixedPoolMultiplier * D) ^ 2 :=
        Nat.pow_le_pow_left
          (by
            dsimp [D]
            exact
              lemma19FixedRadius_le_global
                (4 * R) cStar R)
          2
  exact
    lemma18FixedParameterFacts
      n (theorem6Q n γ) cStar D
      (lemma17FixedLandingRho rho
        (lemma17FixedStageCount n a ha))
      hn hcStar hlarge hD
      (by
        dsimp [D]
        exact lemma18FixedLanding_le_reserve
          cStar
          (lemma17FixedLandingRho rho
            (lemma17FixedStageCount n a ha))
          R hLanding)
      hprefixQa hmajorQa
      (by simpa [D] using hguard)
      hfit

end

end Tri

#print axioms Tri.lemma18FixedTerminalRadius_le_prefix
#print axioms Tri.lemma18FixedLanding_le_reserve
#print axioms Tri.lemma18FixedParameterFacts_explicit
