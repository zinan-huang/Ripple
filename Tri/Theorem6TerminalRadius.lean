/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Lemma18Explicit
import Tri.Theorem6InitialRadius

/-!
# Canonical terminal radius for Theorem 6

The maximum of the fixed landing radius and a positive upper square root of
the global variance volume discharges both terminal-radius obligations.  The
decisive guard then puts this radius strictly below the population.
-/

namespace Tri

noncomputable section

/-- Least simple radius dominating both the fixed landing radius and the
global square-root radius. -/
def theorem6CanonicalTerminalRadius
    (n q landingRho : ℕ) : ℕ :=
  max landingRho (Nat.sqrt (q * n) + 1)

/-- The canonical radius specialized to the fixed Theorem 6 prefix. -/
def theorem6TerminalRadius
    (n γ : ℕ)
    (ha : 0 < theorem6InitialScale n γ) : ℕ :=
  theorem6CanonicalTerminalRadius n
    (theorem6Q n γ)
    (lemma17LandingRho
      (theorem6InitialRadius
        (theorem6Q n γ)
        (theorem6InitialScale n γ))
      (lemma17StageCount n
        (theorem6InitialScale n γ) ha))

theorem theorem6CanonicalTerminalRadius_landing
    (n q landingRho : ℕ) :
    landingRho ≤
      theorem6CanonicalTerminalRadius n q landingRho :=
  Nat.le_max_left _ _

theorem theorem6CanonicalTerminalRadius_sq
    (n q landingRho : ℕ) :
    q * n ≤
      theorem6CanonicalTerminalRadius n q landingRho ^ 2 := by
  have hroot :
      q * n ≤ (Nat.sqrt (q * n) + 1) ^ 2 :=
    Nat.le_of_lt (by
      simpa using Nat.lt_succ_sqrt' (q * n))
  exact hroot.trans
    (Nat.pow_le_pow_left
      (Nat.le_max_right landingRho
        (Nat.sqrt (q * n) + 1)) 2)

theorem theorem6TerminalRadius_landing
    (n γ : ℕ)
    (ha : 0 < theorem6InitialScale n γ) :
    lemma17LandingRho
        (theorem6InitialRadius
          (theorem6Q n γ)
          (theorem6InitialScale n γ))
        (lemma17StageCount n
          (theorem6InitialScale n γ) ha) ≤
      theorem6TerminalRadius n γ ha :=
  theorem6CanonicalTerminalRadius_landing _ _ _

theorem theorem6TerminalRadius_sq
    (n γ : ℕ)
    (ha : 0 < theorem6InitialScale n γ) :
    theorem6Q n γ * n ≤
      theorem6TerminalRadius n γ ha ^ 2 :=
  theorem6CanonicalTerminalRadius_sq _ _ _

/-- Once the decisive reserve fits below the critical scale, the canonical
terminal radius is automatically smaller than the population. -/
theorem theorem6CanonicalTerminalRadius_lt_of_guard
    {n q cStar landingRho : ℕ}
    (hn : 0 < n)
    (hlarge :
      theorem6CStarSq *
          (theorem6CStarSq + 6) ≤ n)
    (hguard :
      60 *
          lemma19Ddec theorem6PostStages
            (4 * theorem6CanonicalTerminalRadius
              n q landingRho)
            cStar
            (theorem6CanonicalTerminalRadius
              n q landingRho) ≤
        theorem6CriticalScale n) :
    theorem6CanonicalTerminalRadius n q landingRho < n := by
  let R :=
    theorem6CanonicalTerminalRadius n q landingRho
  let D :=
    lemma19Ddec theorem6PostStages
      (4 * R) cStar R
  have hRD : 4 * R ≤ D := by
    dsimp [D, lemma19Ddec,
      theorem6PostStages, lemma19HalfDrop]
    omega
  obtain ⟨e, W⟩ :=
    lemma19WindowFacts_of_large n hn hlarge
  have hquarter :=
    W.hquarter 0 (by
      norm_num [theorem6PostStages])
  have hscale :=
    W.hscale0
  have hcritical :
      theorem6CriticalScale n ≤ n := by
    rw [hscale] at hquarter
    omega
  change 60 * D ≤ theorem6CriticalScale n at hguard
  omega

theorem theorem6TerminalRadius_lt_of_guard
    {n γ cStar : ℕ}
    (ha : 0 < theorem6InitialScale n γ)
    (hn : 0 < n)
    (hlarge :
      theorem6CStarSq *
          (theorem6CStarSq + 6) ≤ n)
    (hguard :
      60 *
          lemma19Ddec theorem6PostStages
            (4 * theorem6TerminalRadius n γ ha)
            cStar
            (theorem6TerminalRadius n γ ha) ≤
        theorem6CriticalScale n) :
    theorem6TerminalRadius n γ ha < n := by
  exact
    theorem6CanonicalTerminalRadius_lt_of_guard
      hn hlarge (by
        simpa [theorem6TerminalRadius] using hguard)

end

end Tri

#print axioms
  Tri.theorem6CanonicalTerminalRadius_landing
#print axioms Tri.theorem6CanonicalTerminalRadius_sq
#print axioms Tri.theorem6TerminalRadius_landing
#print axioms Tri.theorem6TerminalRadius_sq
#print axioms
  Tri.theorem6CanonicalTerminalRadius_lt_of_guard
#print axioms
  Tri.theorem6TerminalRadius_lt_of_guard
