/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.MultiPairGap

/-!
# Third-party pair-gap reaction masses

For tracked species `X,Y` and a third species `Z`, favorable pair-gap reactions
are `X` winning against `Z` and `Z` winning against `Y`. The reverse two
directions are adverse. If `X` is at least as populous as both `Y` and `Z`,
the combined favorable numerator is at least the adverse numerator.
-/

namespace Tri.Multi

open scoped ENNReal

variable {m n : ℕ}

def thirdPartyUpWeight
    (c : Config m n) (X Y Z : Species m) : ℕ :=
  directedFireWeight c X Z + directedFireWeight c Z Y

def thirdPartyDownWeight
    (c : Config m n) (X Y Z : Species m) : ℕ :=
  directedFireWeight c Z X + directedFireWeight c Y Z

theorem thirdParty_weight_bias_arith
    (x y z : ℕ) (hy : y ≤ x) (hz : z ≤ x) :
    Nat.choose z 2 * x + Nat.choose y 2 * z ≤
      Nat.choose x 2 * z + Nat.choose z 2 * y := by
  cases x with
  | zero =>
      have hy0 : y = 0 := by omega
      have hz0 : z = 0 := by omega
      subst y
      subst z
      simp
  | succ x =>
      cases y with
      | zero =>
          cases z with
          | zero => simp
          | succ z =>
              have hx := two_mul_choose_two_succ x
              have hz' := two_mul_choose_two_succ z
              have hdouble :
                  2 * (Nat.choose (z + 1) 2 * (x + 1) +
                      Nat.choose 0 2 * (z + 1)) ≤
                    2 * (Nat.choose (x + 1) 2 * (z + 1) +
                      Nat.choose (z + 1) 2 * 0) := by
                calc
                  2 * (Nat.choose (z + 1) 2 * (x + 1) +
                      Nat.choose 0 2 * (z + 1)) =
                      (2 * Nat.choose (z + 1) 2) * (x + 1) +
                        (2 * Nat.choose 0 2) * (z + 1) := by ring
                  _ = (z + 1) * z * (x + 1) := by
                    rw [hz']
                    norm_num [Nat.choose_zero_succ]
                  _ = ((z + 1) * (x + 1)) * z := by ring
                  _ ≤ ((z + 1) * (x + 1)) * x :=
                    Nat.mul_le_mul_left _ (by omega)
                  _ = (x + 1) * x * (z + 1) := by ring
                  _ = (2 * Nat.choose (x + 1) 2) * (z + 1) +
                      (2 * Nat.choose (z + 1) 2) * 0 := by
                    rw [hx]
                    simp
                  _ = 2 * (Nat.choose (x + 1) 2 * (z + 1) +
                      Nat.choose (z + 1) 2 * 0) := by ring
              exact Nat.le_of_mul_le_mul_left hdouble (by norm_num)
      | succ y =>
          cases z with
          | zero => simp
          | succ z =>
              have hx := two_mul_choose_two_succ x
              have hy' := two_mul_choose_two_succ y
              have hz' := two_mul_choose_two_succ z
              have hyx : y ≤ x := by omega
              have hzx : z ≤ x := by omega
              have hzsum : z ≤ x + y + 1 := by omega
              have hidInt :
                  ((((x + 1) * x * (z + 1) +
                      (z + 1) * z * (y + 1) : ℕ) : ℤ)) =
                    (((z + 1) * z * (x + 1) +
                      (y + 1) * y * (z + 1) : ℕ) : ℤ) +
                    (((z + 1) * (x - y) *
                      (x + y + 1 - z) : ℕ) : ℤ) := by
                push_cast
                rw [Int.natCast_sub hyx, Int.natCast_sub hzsum]
                push_cast
                ring
              have hid :
                  (x + 1) * x * (z + 1) +
                      (z + 1) * z * (y + 1) =
                    ((z + 1) * z * (x + 1) +
                      (y + 1) * y * (z + 1)) +
                    (z + 1) * (x - y) *
                      (x + y + 1 - z) := by
                exact_mod_cast hidInt
              have hdouble :
                  2 * (Nat.choose (z + 1) 2 * (x + 1) +
                      Nat.choose (y + 1) 2 * (z + 1)) ≤
                    2 * (Nat.choose (x + 1) 2 * (z + 1) +
                      Nat.choose (z + 1) 2 * (y + 1)) := by
                calc
                  2 * (Nat.choose (z + 1) 2 * (x + 1) +
                      Nat.choose (y + 1) 2 * (z + 1)) =
                      (2 * Nat.choose (z + 1) 2) * (x + 1) +
                        (2 * Nat.choose (y + 1) 2) * (z + 1) := by ring
                  _ = (z + 1) * z * (x + 1) +
                      (y + 1) * y * (z + 1) := by rw [hz', hy']
                  _ ≤ (x + 1) * x * (z + 1) +
                      (z + 1) * z * (y + 1) := by
                    rw [hid]
                    omega
                  _ = (2 * Nat.choose (x + 1) 2) * (z + 1) +
                      (2 * Nat.choose (z + 1) 2) * (y + 1) := by
                    rw [hx, hz']
                  _ = 2 * (Nat.choose (x + 1) 2 * (z + 1) +
                      Nat.choose (z + 1) 2 * (y + 1)) := by ring
              exact Nat.le_of_mul_le_mul_left hdouble (by norm_num)

theorem thirdPartyDownWeight_le_upWeight
    (c : Config m n) (X Y Z : Species m)
    (hY : count c Y ≤ count c X)
    (hZ : count c Z ≤ count c X) :
    thirdPartyDownWeight c X Y Z ≤
      thirdPartyUpWeight c X Y Z := by
  unfold thirdPartyDownWeight thirdPartyUpWeight directedFireWeight
  exact thirdParty_weight_bias_arith
    (count c X) (count c Y) (count c Z) hY hZ

noncomputable def thirdPartyUpMass
    (c : Config m n) (h3 : 3 ≤ n)
    (X Y Z : Species m) : ℝ≥0∞ :=
  directedFireMass c h3 X Z + directedFireMass c h3 Z Y

noncomputable def thirdPartyDownMass
    (c : Config m n) (h3 : 3 ≤ n)
    (X Y Z : Species m) : ℝ≥0∞ :=
  directedFireMass c h3 Z X + directedFireMass c h3 Y Z

theorem thirdPartyUpMass_eq
    (c : Config m n) (h3 : 3 ≤ n)
    (X Y Z : Species m)
    (hXZ : X ≠ Z) (hZY : Z ≠ Y) :
    thirdPartyUpMass c h3 X Y Z =
      (thirdPartyUpWeight c X Y Z : ℝ≥0∞) /
        (Nat.choose n 3 : ℝ≥0∞) := by
  unfold thirdPartyUpMass thirdPartyUpWeight
  rw [directedFireMass_eq c h3 X Z hXZ,
    directedFireMass_eq c h3 Z Y hZY]
  push_cast
  rw [ENNReal.add_div]

theorem thirdPartyDownMass_eq
    (c : Config m n) (h3 : 3 ≤ n)
    (X Y Z : Species m)
    (hZX : Z ≠ X) (hYZ : Y ≠ Z) :
    thirdPartyDownMass c h3 X Y Z =
      (thirdPartyDownWeight c X Y Z : ℝ≥0∞) /
        (Nat.choose n 3 : ℝ≥0∞) := by
  unfold thirdPartyDownMass thirdPartyDownWeight
  rw [directedFireMass_eq c h3 Z X hZX,
    directedFireMass_eq c h3 Y Z hYZ]
  push_cast
  rw [ENNReal.add_div]

theorem thirdPartyDownMass_le_upMass
    (c : Config m n) (h3 : 3 ≤ n)
    (X Y Z : Species m)
    (hXZ : X ≠ Z) (hYZ : Y ≠ Z)
    (hY : count c Y ≤ count c X)
    (hZ : count c Z ≤ count c X) :
    thirdPartyDownMass c h3 X Y Z ≤
      thirdPartyUpMass c h3 X Y Z := by
  rw [thirdPartyDownMass_eq c h3 X Y Z
      (Ne.symm hXZ) hYZ,
    thirdPartyUpMass_eq c h3 X Y Z hXZ (by
      exact fun h => hYZ h.symm)]
  apply ENNReal.div_le_div_right
  exact_mod_cast thirdPartyDownWeight_le_upWeight c X Y Z hY hZ

end Tri.Multi

#print axioms Tri.Multi.thirdParty_weight_bias_arith
#print axioms Tri.Multi.thirdPartyDownWeight_le_upWeight
#print axioms Tri.Multi.thirdPartyDownMass_le_upMass
