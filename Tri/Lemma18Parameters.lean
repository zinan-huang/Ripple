/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Lemma17Reaction
import Tri.Lemma17CriticalLandingTo18
import Tri.Lemma18ErrorFacts
import Tri.Lemma19PostWindow

/-!
# Fixed decisive-stage parameters

The prefix and endpoint radii are additive predecessors of the decisive
reserve.  The decisive reaction parameter reuses the least integral choice
from the Lemma 17 family at the fixed critical scale.
-/

namespace Tri

noncomputable section

/-- Prefix reveal radius immediately below the decisive reserve. -/
def lemma18PrefixRadius
    (D : ℕ) : ℕ :=
  D.pred

/-- Endpoint reveal radius immediately below twelve decisive reserves. -/
def lemma18EndRadius
    (D : ℕ) : ℕ :=
  (12 * D).pred

/-- Least decisive reaction parameter satisfying the semantic and active
error lower bounds. -/
noncomputable def lemma18Reaction
    (n q cStar : ℕ)
    (hn : 0 < n)
    (hcStar : 0 < cStar) : ℕ :=
  lemma17Reaction n q cStar
    (theorem6CriticalScale n) hn hcStar

theorem lemma18PrefixRadius_add_one
    (D : ℕ) (hD : 0 < D) :
    lemma18PrefixRadius D + 1 = D := by
  simpa [lemma18PrefixRadius,
    Nat.succ_eq_add_one] using
      Nat.succ_pred_eq_of_pos hD

theorem lemma18EndRadius_add_one
    (D : ℕ) (hD : 0 < D) :
    lemma18EndRadius D + 1 = 12 * D := by
  have h12D : 0 < 12 * D := by
    positivity
  simpa [lemma18EndRadius,
    Nat.succ_eq_add_one] using
      Nat.succ_pred_eq_of_pos h12D

/-- The endpoint radius dominates the prefix radius. -/
theorem lemma18PrefixRadius_le_end
    (D : ℕ) :
    lemma18PrefixRadius D ≤
      lemma18EndRadius D := by
  apply Nat.pred_le_pred
  omega

/-- Every prefix square bound also holds at the endpoint radius. -/
theorem lemma18EndRadius_sq
    (q a D : ℕ)
    (hprefix :
      q * (a + 1) ≤
        lemma18PrefixRadius D ^ 2) :
    q * (a + 1) ≤
      lemma18EndRadius D ^ 2 :=
  hprefix.trans
    (Nat.pow_le_pow_left
      (lemma18PrefixRadius_le_end D) 2)

/-- Complete fixed hypotheses at the decisive Lemma 18 stage. -/
structure Lemma18ParameterFacts
    (n q cStar D rhoLanding : ℕ)
    (hn : 0 < n)
    (hcStar : 0 < cStar) : Prop where
  ha :
    4 ≤ theorem6CriticalScale n
  hquarter :
    4 * theorem6CriticalScale n ≤ n
  hstageRoom :
    2 * theorem6CriticalScale n + 4 ≤ n
  hpriorRadius :
    cStar * rhoLanding ≤ D
  hprefixRadius :
    lemma18PrefixRadius D + 1 = D
  hendRadius :
    lemma18EndRadius D + 1 = 12 * D
  hprefixQa :
    q * (theorem6CriticalScale n + 1) ≤
      lemma18PrefixRadius D ^ 2
  hendQa :
    q * (theorem6CriticalScale n + 1) ≤
      lemma18EndRadius D ^ 2
  hmajorQa :
    q * (theorem6CriticalScale n + 2) ≤
      (60 * theorem6PoolMultiplier * D) ^ 2
  hlabelRoom :
    5 * theorem6CriticalScale n + 8 ≤ n
  hmean :
    (2 * theorem6CriticalScale n) ^ 3 ≤
      lemma18Reaction n q cStar hn hcStar *
        n ^ 2
  hguardScale :
    60 * D ≤ theorem6CriticalScale n
  hreactionScale :
    1200 * cStar *
        lemma18Reaction n q cStar hn hcStar ≤
      7 * theorem6CriticalScale n
  herror :
    Lemma18ErrorFacts q
      (theorem6CriticalScale n) cStar
      (lemma18Reaction n q cStar hn hcStar) D

/-- The fixed large-population window, one prefix square, and one exact
reaction interval fit supply all decisive-stage fields. -/
theorem lemma18ParameterFacts
    (n q cStar D rhoLanding : ℕ)
    (hn : 0 < n)
    (hcStar : 0 < cStar)
    (hlarge :
      theorem6CStarSq *
          (theorem6CStarSq + 6) ≤ n)
    (hD : 0 < D)
    (hpriorRadius :
      cStar * rhoLanding ≤ D)
    (hprefixQa :
      q * (theorem6CriticalScale n + 1) ≤
        lemma18PrefixRadius D ^ 2)
    (hmajorQa :
      q * (theorem6CriticalScale n + 2) ≤
        (60 * theorem6PoolMultiplier * D) ^ 2)
    (hguardScale :
      60 * D ≤ theorem6CriticalScale n)
    (hfit :
      1200 * cStar *
          lemma17ReactionLower n q cStar
            (theorem6CriticalScale n) ≤
        7 * theorem6CriticalScale n) :
    Lemma18ParameterFacts
      n q cStar D rhoLanding hn hcStar := by
  obtain ⟨e, W⟩ :=
    lemma19WindowFacts_of_large n hn hlarge
  have hscaleLarge :
      theorem6CStarSq + 6 ≤
        theorem6CriticalScale n :=
    theorem6CriticalScale_lower n
      (theorem6CStarSq + 6) hlarge
  have ha :
      4 ≤ theorem6CriticalScale n := by
    rw [theorem6CStar_sq] at hscaleLarge
    omega
  have hpostQuarter :=
    W.hquarter 0 (by
      norm_num [theorem6PostStages])
  rw [W.hscale0] at hpostQuarter
  have hquarter :
      4 * theorem6CriticalScale n ≤ n := by
    omega
  have hstageRoom :
      2 * theorem6CriticalScale n + 4 ≤ n := by
    omega
  have hlabelRoom :
      5 * theorem6CriticalScale n + 8 ≤ n := by
    omega
  have hspec :=
    lemma17Reaction_spec n q cStar
      (theorem6CriticalScale n) hn hcStar
  have hreactionScale :
      1200 * cStar *
          lemma18Reaction n q cStar hn hcStar ≤
        7 * theorem6CriticalScale n := by
    unfold lemma18Reaction
    exact
      (Nat.mul_le_mul_left (1200 * cStar)
        (lemma17Reaction_le_lower n q cStar
          (theorem6CriticalScale n)
          hn hcStar)).trans hfit
  have hprefixRadius :=
    lemma18PrefixRadius_add_one D hD
  have herror :=
    lemma18ErrorFacts
      n q (theorem6CriticalScale n)
      cStar
      (lemma18Reaction n q cStar hn hcStar)
      D (lemma18PrefixRadius D)
      ha hspec.2.1 hspec.2.2 hguardScale
      hreactionScale hprefixRadius hprefixQa
  exact
    { ha := ha
      hquarter := hquarter
      hstageRoom := hstageRoom
      hpriorRadius := hpriorRadius
      hprefixRadius := hprefixRadius
      hendRadius :=
        lemma18EndRadius_add_one D hD
      hprefixQa := hprefixQa
      hendQa :=
        lemma18EndRadius_sq q
          (theorem6CriticalScale n) D hprefixQa
      hmajorQa := hmajorQa
      hlabelRoom := hlabelRoom
      hmean := hspec.2.1
      hguardScale := hguardScale
      hreactionScale := hreactionScale
      herror := herror }

end

end Tri

#print axioms Tri.lemma18PrefixRadius_add_one
#print axioms Tri.lemma18EndRadius_add_one
#print axioms Tri.lemma18PrefixRadius_le_end
#print axioms Tri.lemma18EndRadius_sq
#print axioms Tri.lemma18ParameterFacts
