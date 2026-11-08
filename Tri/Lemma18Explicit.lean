/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Lemma18Parameters
import Tri.Lemma16To19PostParameters

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
theorem lemma18TerminalRadius_le_prefix
    (cStar R : ℕ) :
    R ≤
      lemma18PrefixRadius
        (lemma19Ddec theorem6PostStages
          (4 * R) cStar R) := by
  let D :=
    lemma19Ddec theorem6PostStages
      (4 * R) cStar R
  have hD : 0 < D := by
    dsimp [D, lemma19Ddec,
      theorem6PostStages, lemma19HalfDrop]
    omega
  have hR :
      R + 1 ≤ D := by
    dsimp [D, lemma19Ddec,
      theorem6PostStages, lemma19HalfDrop]
    omega
  have hpred :=
    lemma18PrefixRadius_add_one D hD
  change R ≤ lemma18PrefixRadius D
  omega

/-- The fixed decisive reserve dominates the landing radius whenever the
terminal post radius does. -/
theorem lemma18Landing_le_reserve
    (cStar rhoLanding R : ℕ)
    (hLanding : rhoLanding ≤ R) :
    cStar * rhoLanding ≤
      lemma19Ddec theorem6PostStages
        (4 * R) cStar R := by
  have hmul :
      cStar * rhoLanding ≤ cStar * R :=
    Nat.mul_le_mul_left cStar hLanding
  calc
    cStar * rhoLanding ≤ cStar * R := hmul
    _ ≤
        lemma19Ddec theorem6PostStages
          (4 * R) cStar R := by
      simp only [lemma19Ddec,
        theorem6PostStages, lemma19HalfDrop]
      nlinarith

/-- Construct the decisive-stage certificate from the global terminal square
and the three genuine interval/containment conditions. -/
theorem lemma18ParameterFacts_explicit
    (n γ cStar a rho R : ℕ)
    (hn : 0 < n)
    (hcStar : 0 < cStar)
    (ha : 0 < a)
    (hlarge :
      theorem6CStarSq *
          (theorem6CStarSq + 6) ≤ n)
    (hLanding :
      lemma17LandingRho rho
          (lemma17StageCount n a ha) ≤
        R)
    (hSq : theorem6Q n γ * n ≤ R ^ 2)
    (hguard :
      60 *
          lemma19Ddec theorem6PostStages
            (4 * R) cStar R ≤
        theorem6CriticalScale n)
    (hfit :
      1200 * cStar *
          lemma17ReactionLower n
            (theorem6Q n γ) cStar
            (theorem6CriticalScale n) ≤
        7 * theorem6CriticalScale n) :
    Lemma18ParameterFacts
      n (theorem6Q n γ) cStar
      (lemma19Ddec theorem6PostStages
        (4 * R) cStar R)
      (lemma17LandingRho rho
        (lemma17StageCount n a ha))
      hn hcStar := by
  let D :=
    lemma19Ddec theorem6PostStages
      (4 * R) cStar R
  obtain ⟨e, W⟩ :=
    lemma19WindowFacts_of_large n hn hlarge
  have hpostQuarter :=
    W.hquarter 0 (by
      norm_num [theorem6PostStages])
  have hpostScale :=
    W.ha 0 (by
      norm_num [theorem6PostStages])
  rw [W.hscale0] at hpostQuarter hpostScale
  have hcriticalOne :
      theorem6CriticalScale n + 1 ≤ n := by
    omega
  have hcriticalTwo :
      theorem6CriticalScale n + 2 ≤ n := by
    omega
  have hD : 0 < D := by
    dsimp [D, lemma19Ddec,
      theorem6PostStages, lemma19HalfDrop]
    omega
  have hprefixQa :
      theorem6Q n γ *
          (theorem6CriticalScale n + 1) ≤
        lemma18PrefixRadius D ^ 2 := by
    calc
      theorem6Q n γ *
            (theorem6CriticalScale n + 1)
          ≤ theorem6Q n γ * n :=
        Nat.mul_le_mul_left (theorem6Q n γ)
          hcriticalOne
      _ ≤ R ^ 2 := hSq
      _ ≤ lemma18PrefixRadius D ^ 2 :=
        Nat.pow_le_pow_left
          (by
            dsimp [D]
            exact
              lemma18TerminalRadius_le_prefix
                cStar R)
          2
  have hmajorQa :
      theorem6Q n γ *
          (theorem6CriticalScale n + 2) ≤
        (60 * theorem6PoolMultiplier * D) ^ 2 := by
    calc
      theorem6Q n γ *
            (theorem6CriticalScale n + 2)
          ≤ theorem6Q n γ * n :=
        Nat.mul_le_mul_left (theorem6Q n γ)
          hcriticalTwo
      _ ≤ R ^ 2 := hSq
      _ ≤ (60 * theorem6PoolMultiplier * D) ^ 2 :=
        Nat.pow_le_pow_left
          (by
            dsimp [D]
            exact
              lemma19Radius_le_global
                (4 * R) cStar R)
          2
  exact
    lemma18ParameterFacts
      n (theorem6Q n γ) cStar D
      (lemma17LandingRho rho
        (lemma17StageCount n a ha))
      hn hcStar hlarge hD
      (by
        dsimp [D]
        exact lemma18Landing_le_reserve
          cStar
          (lemma17LandingRho rho
            (lemma17StageCount n a ha))
          R hLanding)
      hprefixQa hmajorQa
      (by simpa [D] using hguard)
      hfit

end

end Tri

#print axioms Tri.lemma18TerminalRadius_le_prefix
#print axioms Tri.lemma18Landing_le_reserve
#print axioms Tri.lemma18ParameterFacts_explicit
