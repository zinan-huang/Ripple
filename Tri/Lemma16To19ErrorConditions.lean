/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Lemma16To19Error
import Tri.Lemma17Ladder

/-!
# Derived error conditions for the activation ladder

Several hypotheses needed only to put the stage errors on a common
exponential scale already follow from the physical stage assumptions.  This
file records those implications so that the headline theorem need not ask for
them twice.
-/

namespace Tri

noncomputable section

/-- A scale satisfying the exact doubling recurrence has the expected closed
form through the terminal rung. -/
theorem scale_eq_two_pow_mul_of_double
    (scale : ℕ → ℕ) (m j : ℕ)
    (hdouble :
      ∀ i < m, scale (i + 1) = 2 * scale i)
    (hj : j ≤ m) :
    scale j = 2 ^ j * scale 0 := by
  induction j with
  | zero =>
      simp
  | succ j ih =>
      have hjm : j < m := by omega
      rw [hdouble j hjm, ih (by omega), pow_succ]
      ring

/-- A lower bound at the first rung propagates through exact doubling. -/
theorem common_q_le_scale_of_double
    (q m : ℕ) (scale : ℕ → ℕ)
    (hq0 : q ≤ scale 0)
    (hdouble :
      ∀ i < m, scale (i + 1) = 2 * scale i)
    (j : ℕ) (hj : j ≤ m) :
    q ≤ scale j := by
  rw [scale_eq_two_pow_mul_of_double
    scale m j hdouble hj]
  have hpow : 1 ≤ 2 ^ j :=
    one_le_pow₀ (by norm_num : (1 : ℕ) ≤ 2)
  exact hq0.trans
    (by
      simpa [mul_comm] using
        Nat.mul_le_mul_right (scale 0) hpow)

/-- A positive stage scale and the physical mean lower bound force the
reaction-count parameter to be positive. -/
theorem stage_reaction_parameter_pos
    (n a r : ℕ)
    (ha : 0 < a)
    (hmean :
      (2 * a) ^ 3 ≤ r * n ^ 2) :
    0 < r := by
  by_contra hr
  have hr0 : r = 0 := Nat.eq_zero_of_not_pos hr
  have hleft : 0 < (2 * a) ^ 3 := by
    positivity
  rw [hr0, zero_mul] at hmean
  omega

/-- The direction-rate condition used by the exponential envelope follows
from the physical upper bound on `r` and the existing label-radius bound. -/
theorem lemma17_error_direction_of_stage
    (q a cStar rho r : ℕ)
    (hcStar : 1 ≤ cStar)
    (hactiveScale :
      76 * cStar * r ≤ a)
    (hqa :
      q * (a + 1) ≤ rho ^ 2) :
    3 * q * r ≤ 4 * cStar * rho ^ 2 := by
  have hthree : 3 * r ≤ a := by
    calc
      3 * r ≤ (76 * cStar) * r :=
        Nat.mul_le_mul_right r (by omega)
      _ = 76 * cStar * r := by ring
      _ ≤ a := hactiveScale
  calc
    3 * q * r = q * (3 * r) := by ring
    _ ≤ q * a := Nat.mul_le_mul_left q hthree
    _ ≤ q * (a + 1) :=
      Nat.mul_le_mul_left q (by omega)
    _ ≤ rho ^ 2 := hqa
    _ ≤ 4 * cStar * rho ^ 2 := by
      simpa [mul_assoc] using
        Nat.le_mul_of_pos_left
          (rho ^ 2) (by omega : 0 < 4 * cStar)

/-- A simple multiplicative pool budget discharges the endpoint-dependent
Lemma 18 launch condition.  The predecessor of the terminal scale is carried
as an additive witness. -/
theorem gapBoundary_pool_le_stageRemaining_mul
    (n a cStar rho d aPred : ℕ)
    (ha : 1 ≤ a)
    (haPred : aPred + 1 = a)
    (hpool : n ≤ aPred * d)
    (z : InfectionRevealPhysicalState n)
    (hz : Lemma17GapBoundaryGood a cStar rho z) :
    z.inactive.ids.card ≤
      lemma17StageRemaining a z * d := by
  obtain ⟨hlo, hhi, _hgap⟩ := hz
  have hremaining :=
    lemma17StageRemaining_spec
      a z ha hlo hhi
  have hpredRemaining :
      aPred ≤ lemma17StageRemaining a z := by
    omega
  have htotal :=
    infectionReveal_active_add_inactive z
  calc
    z.inactive.ids.card ≤ n := by omega
    _ ≤ aPred * d := hpool
    _ ≤ lemma17StageRemaining a z * d :=
      Nat.mul_le_mul_right d hpredRemaining

/-- The decisive-stage direction exponent is already implied by the physical
reaction upper scale and the prefix-label radius budget. -/
theorem lemma18_error_direction_of_stage
    (q a cStar r D rhoPrefix : ℕ)
    (hreactionScale :
      1200 * cStar * r ≤ 7 * a)
    (hprefixRadius : rhoPrefix + 1 = D)
    (hprefixQa :
      q * (a + 1) ≤ rhoPrefix ^ 2) :
    15 * q * cStar * r ≤ 49 * D ^ 2 := by
  have hreactionWeak :
      15 * cStar * r ≤ 7 * a := by
    calc
      15 * cStar * r = 15 * (cStar * r) := by ring
      _ ≤ 1200 * (cStar * r) :=
        Nat.mul_le_mul_right
          (cStar * r) (by norm_num)
      _ = 1200 * cStar * r := by ring
      _ ≤ 7 * a := hreactionScale
  have hrhoD : rhoPrefix ≤ D := by omega
  have hsquare :
      rhoPrefix ^ 2 ≤ D ^ 2 :=
    Nat.pow_le_pow_left hrhoD 2
  calc
    15 * q * cStar * r =
        q * (15 * cStar * r) := by ring
    _ ≤ q * (7 * a) :=
      Nat.mul_le_mul_left q hreactionWeak
    _ = 7 * (q * a) := by ring
    _ ≤ 7 * (q * (a + 1)) :=
      Nat.mul_le_mul_left 7
        (Nat.mul_le_mul_left q (by omega))
    _ ≤ 7 * rhoPrefix ^ 2 :=
      Nat.mul_le_mul_left 7 hprefixQa
    _ ≤ 7 * D ^ 2 :=
      Nat.mul_le_mul_left 7 hsquare
    _ ≤ 49 * D ^ 2 := by
      exact Nat.mul_le_mul_right
        (D ^ 2) (by norm_num)

end

end Tri

#print axioms Tri.scale_eq_two_pow_mul_of_double
#print axioms Tri.common_q_le_scale_of_double
#print axioms Tri.stage_reaction_parameter_pos
#print axioms Tri.lemma17_error_direction_of_stage
#print axioms Tri.gapBoundary_pool_le_stageRemaining_mul
#print axioms Tri.lemma18_error_direction_of_stage
