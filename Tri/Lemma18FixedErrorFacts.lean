/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Lemma16To19ErrorConditions

/-!
# Derived decisive-stage error facts

The physical mean, guard-scale, and prefix-radius assumptions already imply
three of the four hypotheses used by the uniform Lemma 18 error envelope.
-/

namespace Tri

noncomputable section

/-- The prefix square-radius and decisive guard imply that the common error
parameter is no larger than the decisive active scale. -/
theorem lemma18_q_le_scale_of_prefix
    (q a D rhoPrefix : ℕ)
    (hguardScale : 60 * D ≤ a)
    (hprefixRadius : rhoPrefix + 1 = D)
    (hprefixQa :
      q * (a + 1) ≤ rhoPrefix ^ 2) :
    q ≤ a := by
  have hrhoD : rhoPrefix ≤ D := by omega
  have hDa : D ≤ a := by omega
  have hrhoA : rhoPrefix ≤ a :=
    hrhoD.trans hDa
  have hsquare :
      rhoPrefix ^ 2 ≤ a ^ 2 :=
    Nat.pow_le_pow_left hrhoA 2
  by_contra hqa
  have haq : a + 1 ≤ q := by omega
  have hlower :
      (a + 1) ^ 2 ≤ q * (a + 1) := by
    simpa [pow_two] using
      Nat.mul_le_mul_right (a + 1) haq
  have hbad :
      (a + 1) ^ 2 ≤ a ^ 2 :=
    hlower.trans (hprefixQa.trans hsquare)
  nlinarith

/-- Error-envelope hypotheses derived at the decisive fixed landing. -/
structure Lemma18FixedErrorFacts
    (q a cStar r D : ℕ) : Prop where
  hr : 0 < r
  hqa : q ≤ a
  hactive : 15 * q ≤ 4 * cStar * r
  hdirection :
    15 * q * cStar * r ≤ 49 * D ^ 2

/-- Only the active-error lower bound remains independent of the semantic
decisive-stage assumptions. -/
theorem lemma18FixedErrorFacts
    (n q a cStar r D rhoPrefix : ℕ)
    (ha : 4 ≤ a)
    (hmean : (2 * a) ^ 3 ≤ r * n ^ 2)
    (hactive : 15 * q ≤ 4 * cStar * r)
    (hguardScale : 60 * D ≤ a)
    (hreactionScale :
      1200 * cStar * r ≤ 7 * a)
    (hprefixRadius : rhoPrefix + 1 = D)
    (hprefixQa :
      q * (a + 1) ≤ rhoPrefix ^ 2) :
    Lemma18FixedErrorFacts q a cStar r D :=
  { hr :=
      stage_reaction_parameter_pos n a r
        (by omega) hmean
    hqa :=
      lemma18_q_le_scale_of_prefix q a D rhoPrefix
        hguardScale hprefixRadius hprefixQa
    hactive := hactive
    hdirection :=
      lemma18_error_direction_of_stage
        q a cStar r D rhoPrefix
        hreactionScale hprefixRadius hprefixQa }

end

end Tri

#print axioms Tri.lemma18_q_le_scale_of_prefix
#print axioms Tri.lemma18FixedErrorFacts
