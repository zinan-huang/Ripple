/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Lemma17FixedReaction
import Tri.Lemma17FixedLandingTo18
import Tri.Lemma18FixedErrorFacts
import Tri.Lemma19FixedWindow

/-!
# Fixed decisive-stage parameters

The prefix and endpoint radii are additive predecessors of the decisive
reserve.  The decisive reaction parameter reuses the least integral choice
from the Lemma 17 family at the fixed critical scale.
-/

namespace Tri

noncomputable section

/-- Prefix reveal radius immediately below the decisive reserve. -/
def lemma18FixedPrefixRadius
    (D : ℕ) : ℕ :=
  D.pred

/-- Endpoint reveal radius immediately below twelve decisive reserves. -/
def lemma18FixedEndRadius
    (D : ℕ) : ℕ :=
  (12 * D).pred

/-- Least decisive reaction parameter satisfying the semantic and active
error lower bounds. -/
noncomputable def lemma18FixedReaction
    (n q cStar : ℕ)
    (hn : 0 < n)
    (hcStar : 0 < cStar) : ℕ :=
  lemma17FixedReaction n q cStar
    (theorem6FixedCriticalScale n) hn hcStar

theorem lemma18FixedPrefixRadius_add_one
    (D : ℕ) (hD : 0 < D) :
    lemma18FixedPrefixRadius D + 1 = D := by
  simpa [lemma18FixedPrefixRadius,
    Nat.succ_eq_add_one] using
      Nat.succ_pred_eq_of_pos hD

theorem lemma18FixedEndRadius_add_one
    (D : ℕ) (hD : 0 < D) :
    lemma18FixedEndRadius D + 1 = 12 * D := by
  have h12D : 0 < 12 * D := by
    positivity
  simpa [lemma18FixedEndRadius,
    Nat.succ_eq_add_one] using
      Nat.succ_pred_eq_of_pos h12D

/-- The endpoint radius dominates the prefix radius. -/
theorem lemma18FixedPrefixRadius_le_end
    (D : ℕ) :
    lemma18FixedPrefixRadius D ≤
      lemma18FixedEndRadius D := by
  apply Nat.pred_le_pred
  omega

/-- Every prefix square bound also holds at the endpoint radius. -/
theorem lemma18FixedEndRadius_sq
    (q a D : ℕ)
    (hprefix :
      q * (a + 1) ≤
        lemma18FixedPrefixRadius D ^ 2) :
    q * (a + 1) ≤
      lemma18FixedEndRadius D ^ 2 :=
  hprefix.trans
    (Nat.pow_le_pow_left
      (lemma18FixedPrefixRadius_le_end D) 2)

/-- Complete fixed hypotheses at the decisive Lemma 18 stage. -/
structure Lemma18FixedParameterFacts
    (n q cStar D rhoLanding : ℕ)
    (hn : 0 < n)
    (hcStar : 0 < cStar) : Prop where
  ha :
    4 ≤ theorem6FixedCriticalScale n
  hquarter :
    4 * theorem6FixedCriticalScale n ≤ n
  hstageRoom :
    2 * theorem6FixedCriticalScale n + 4 ≤ n
  hpriorRadius :
    cStar * rhoLanding ≤ D
  hprefixRadius :
    lemma18FixedPrefixRadius D + 1 = D
  hendRadius :
    lemma18FixedEndRadius D + 1 = 12 * D
  hprefixQa :
    q * (theorem6FixedCriticalScale n + 1) ≤
      lemma18FixedPrefixRadius D ^ 2
  hendQa :
    q * (theorem6FixedCriticalScale n + 1) ≤
      lemma18FixedEndRadius D ^ 2
  hmajorQa :
    q * (theorem6FixedCriticalScale n + 2) ≤
      (60 * theorem6FixedPoolMultiplier * D) ^ 2
  hlabelRoom :
    5 * theorem6FixedCriticalScale n + 8 ≤ n
  hmean :
    (2 * theorem6FixedCriticalScale n) ^ 3 ≤
      lemma18FixedReaction n q cStar hn hcStar *
        n ^ 2
  hguardScale :
    60 * D ≤ theorem6FixedCriticalScale n
  hreactionScale :
    1200 * cStar *
        lemma18FixedReaction n q cStar hn hcStar ≤
      7 * theorem6FixedCriticalScale n
  herror :
    Lemma18FixedErrorFacts q
      (theorem6FixedCriticalScale n) cStar
      (lemma18FixedReaction n q cStar hn hcStar) D

/-- The fixed large-population window, one prefix square, and one exact
reaction interval fit supply all decisive-stage fields. -/
theorem lemma18FixedParameterFacts
    (n q cStar D rhoLanding : ℕ)
    (hn : 0 < n)
    (hcStar : 0 < cStar)
    (hlarge :
      theorem6FixedCStarSq *
          (theorem6FixedCStarSq + 6) ≤ n)
    (hD : 0 < D)
    (hpriorRadius :
      cStar * rhoLanding ≤ D)
    (hprefixQa :
      q * (theorem6FixedCriticalScale n + 1) ≤
        lemma18FixedPrefixRadius D ^ 2)
    (hmajorQa :
      q * (theorem6FixedCriticalScale n + 2) ≤
        (60 * theorem6FixedPoolMultiplier * D) ^ 2)
    (hguardScale :
      60 * D ≤ theorem6FixedCriticalScale n)
    (hfit :
      1200 * cStar *
          lemma17FixedReactionLower n q cStar
            (theorem6FixedCriticalScale n) ≤
        7 * theorem6FixedCriticalScale n) :
    Lemma18FixedParameterFacts
      n q cStar D rhoLanding hn hcStar := by
  obtain ⟨e, W⟩ :=
    lemma19FixedWindowFacts_of_large n hn hlarge
  have hscaleLarge :
      theorem6FixedCStarSq + 6 ≤
        theorem6FixedCriticalScale n :=
    theorem6FixedCriticalScale_lower n
      (theorem6FixedCStarSq + 6) hlarge
  have ha :
      4 ≤ theorem6FixedCriticalScale n := by
    rw [theorem6FixedCStar_sq] at hscaleLarge
    omega
  have hpostQuarter :=
    W.hquarter 0 (by
      norm_num [theorem6FixedPostStages])
  rw [W.hscale0] at hpostQuarter
  have hquarter :
      4 * theorem6FixedCriticalScale n ≤ n := by
    omega
  have hstageRoom :
      2 * theorem6FixedCriticalScale n + 4 ≤ n := by
    omega
  have hlabelRoom :
      5 * theorem6FixedCriticalScale n + 8 ≤ n := by
    omega
  have hspec :=
    lemma17FixedReaction_spec n q cStar
      (theorem6FixedCriticalScale n) hn hcStar
  have hreactionScale :
      1200 * cStar *
          lemma18FixedReaction n q cStar hn hcStar ≤
        7 * theorem6FixedCriticalScale n := by
    unfold lemma18FixedReaction
    exact
      (Nat.mul_le_mul_left (1200 * cStar)
        (lemma17FixedReaction_le_lower n q cStar
          (theorem6FixedCriticalScale n)
          hn hcStar)).trans hfit
  have hprefixRadius :=
    lemma18FixedPrefixRadius_add_one D hD
  have herror :=
    lemma18FixedErrorFacts
      n q (theorem6FixedCriticalScale n)
      cStar
      (lemma18FixedReaction n q cStar hn hcStar)
      D (lemma18FixedPrefixRadius D)
      ha hspec.2.1 hspec.2.2 hguardScale
      hreactionScale hprefixRadius hprefixQa
  exact
    { ha := ha
      hquarter := hquarter
      hstageRoom := hstageRoom
      hpriorRadius := hpriorRadius
      hprefixRadius := hprefixRadius
      hendRadius :=
        lemma18FixedEndRadius_add_one D hD
      hprefixQa := hprefixQa
      hendQa :=
        lemma18FixedEndRadius_sq q
          (theorem6FixedCriticalScale n) D hprefixQa
      hmajorQa := hmajorQa
      hlabelRoom := hlabelRoom
      hmean := hspec.2.1
      hguardScale := hguardScale
      hreactionScale := hreactionScale
      herror := herror }

end

end Tri

#print axioms Tri.lemma18FixedPrefixRadius_add_one
#print axioms Tri.lemma18FixedEndRadius_add_one
#print axioms Tri.lemma18FixedPrefixRadius_le_end
#print axioms Tri.lemma18FixedEndRadius_sq
#print axioms Tri.lemma18FixedParameterFacts
