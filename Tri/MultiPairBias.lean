/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.MultiThirdParty

/-!
# Aggregate fixed-pair reaction bias

Fix a distinguished species `X` and a competitor `Y`. Direct `X/Y` firings
change `count X - count Y` by two, while firings involving a third species
change it by one. If `X` is at least as populous as every species, the total
favorable reaction weight, counted with these jump magnitudes, is at least the
total adverse weight.
-/

namespace Tri.Multi

open scoped BigOperators ENNReal

variable {m n : ℕ}

/-- The larger coordinate wins a direct two-species firing with at least the
raw weight of the reverse firing. -/
theorem reverse_directedFireWeight_le
    (c : Config m n) (X Y : Species m)
    (hY : count c Y ≤ count c X) :
    directedFireWeight c Y X ≤ directedFireWeight c X Y := by
  unfold directedFireWeight
  cases hX : count c X with
  | zero =>
      have hY0 : count c Y = 0 := by omega
      simp [hY0]
  | succ x =>
      cases hYc : count c Y with
      | zero => simp
      | succ y =>
          have hyx : y ≤ x := by omega
          have hx := two_mul_choose_two_succ x
          have hy := two_mul_choose_two_succ y
          have hdouble :
              2 * (Nat.choose (y + 1) 2 * (x + 1)) ≤
                2 * (Nat.choose (x + 1) 2 * (y + 1)) := by
            calc
              2 * (Nat.choose (y + 1) 2 * (x + 1)) =
                  (2 * Nat.choose (y + 1) 2) * (x + 1) := by ring
              _ = (y + 1) * y * (x + 1) := by rw [hy]
              _ = ((x + 1) * (y + 1)) * y := by ring
              _ ≤ ((x + 1) * (y + 1)) * x :=
                Nat.mul_le_mul_left _ hyx
              _ = (x + 1) * x * (y + 1) := by ring
              _ = (2 * Nat.choose (x + 1) 2) * (y + 1) := by
                rw [hx]
              _ = 2 * (Nat.choose (x + 1) 2 * (y + 1)) := by ring
          simpa [hX, hYc] using
            Nat.le_of_mul_le_mul_left hdouble (by norm_num)

/-- `X` is currently a (not necessarily unique) most populous species. -/
def IsMaxSpecies (c : Config m n) (X : Species m) : Prop :=
  ∀ Z, count c Z ≤ count c X

/-- Third species included in the fixed-pair drift sum. -/
def thirdSpecies (X Y : Species m) : Finset (Species m) :=
  (Finset.univ.erase X).erase Y

/-- Favorable raw reaction weight for the signed pair gap. Direct `X/Y`
firings are doubled because their gap jump has magnitude two. -/
def pairGapUpDriftWeight
    (c : Config m n) (X Y : Species m) : ℕ :=
  2 * directedFireWeight c X Y +
    ∑ Z ∈ thirdSpecies X Y, thirdPartyUpWeight c X Y Z

/-- Adverse raw reaction weight for the signed pair gap, with direct firings
again counted twice. -/
def pairGapDownDriftWeight
    (c : Config m n) (X Y : Species m) : ℕ :=
  2 * directedFireWeight c Y X +
    ∑ Z ∈ thirdSpecies X Y, thirdPartyDownWeight c X Y Z

/-- Exact nonnegative linear drift of every fixed pair gap while `X` is a
global maximum. -/
theorem pairGapDownDriftWeight_le_up
    (c : Config m n) (X Y : Species m)
    (hmax : IsMaxSpecies c X) :
    pairGapDownDriftWeight c X Y ≤
      pairGapUpDriftWeight c X Y := by
  unfold pairGapDownDriftWeight pairGapUpDriftWeight
  apply Nat.add_le_add
  · exact Nat.mul_le_mul_left 2
      (reverse_directedFireWeight_le c X Y (hmax Y))
  · apply Finset.sum_le_sum
    intro Z _hZ
    exact thirdPartyDownWeight_le_upWeight c X Y Z
      (hmax Y) (hmax Z)

/-- Favorable PMF mass weighted by the magnitude of the pair-gap jump. -/
noncomputable def pairGapUpDriftMass
    (c : Config m n) (h3 : 3 ≤ n)
    (X Y : Species m) : ℝ≥0∞ :=
  2 * directedFireMass c h3 X Y +
    ∑ Z ∈ thirdSpecies X Y, thirdPartyUpMass c h3 X Y Z

/-- Adverse PMF mass weighted by the magnitude of the pair-gap jump. -/
noncomputable def pairGapDownDriftMass
    (c : Config m n) (h3 : 3 ≤ n)
    (X Y : Species m) : ℝ≥0∞ :=
  2 * directedFireMass c h3 Y X +
    ∑ Z ∈ thirdSpecies X Y, thirdPartyDownMass c h3 X Y Z

/-- The exact weighted PMF drift is nonnegative. This is the probability-level
form consumed by a later stopped pair-gap supermartingale. -/
theorem pairGapDownDriftMass_le_up
    (c : Config m n) (h3 : 3 ≤ n)
    (X Y : Species m) (hXY : X ≠ Y)
    (hmax : IsMaxSpecies c X) :
    pairGapDownDriftMass c h3 X Y ≤
      pairGapUpDriftMass c h3 X Y := by
  unfold pairGapDownDriftMass pairGapUpDriftMass
  apply add_le_add
  · gcongr
    rw [directedFireMass_eq c h3 Y X (Ne.symm hXY),
      directedFireMass_eq c h3 X Y hXY]
    apply ENNReal.div_le_div_right
    exact_mod_cast reverse_directedFireWeight_le c X Y (hmax Y)
  · apply Finset.sum_le_sum
    intro Z hZ
    have hZX : Z ≠ X := by
      have := (Finset.mem_erase.mp (Finset.mem_erase.mp hZ).2).1
      exact this
    have hZY : Z ≠ Y := (Finset.mem_erase.mp hZ).1
    exact thirdPartyDownMass_le_upMass c h3 X Y Z
      (Ne.symm hZX) (Ne.symm hZY) (hmax Y) (hmax Z)

end Tri.Multi

#print axioms Tri.Multi.reverse_directedFireWeight_le
#print axioms Tri.Multi.pairGapDownDriftWeight_le_up
#print axioms Tri.Multi.pairGapDownDriftMass_le_up
