/-
Ripple.BoundedUniversality.HenonSelector.Henon
--------------------------
The Arai-Ishii normalization of the Hénon map
  f_{a,b}(x,y) = (x² - a - b·y, x)
specialized to (a,b) = (9, 1).

References:
  - Arai-Ishii, "On parameter loci of the Hénon family",
    arXiv:1501.01368, Theorem 2.12 (Quasi-Trichotomy).
  - Devaney-Nitecki 1979, "Shift automorphisms in the Hénon mapping",
    Comm. Math. Phys. 67(2): horseshoe for a > 2(1+|b|)².

For (a,b) = (9,1): 2(1+1)² = 8 < 9, in the horseshoe regime.
-/

import Mathlib

namespace Ripple.BoundedUniversality.HenonSelector

abbrev Point2 := ℝ × ℝ

def IsAlgPoint (z : Point2) : Prop :=
  IsAlgebraic ℚ z.1 ∧ IsAlgebraic ℚ z.2

def henon (a b : ℝ) (p : Point2) : Point2 :=
  (p.1 ^ 2 - a - b * p.2, p.1)

noncomputable def henonInv (a b : ℝ) (p : Point2) : Point2 :=
  (p.2, (p.2 ^ 2 - a - p.1) / b)

theorem henonInv_henon (a b : ℝ) (hb : b ≠ 0) (p : Point2) :
    henonInv a b (henon a b p) = p := by
  unfold henon henonInv
  ext <;> simp <;> field_simp <;> ring

theorem henon_henonInv (a b : ℝ) (hb : b ≠ 0) (p : Point2) :
    henon a b (henonInv a b p) = p := by
  unfold henon henonInv
  ext <;> simp <;> field_simp <;> ring

def henon91 : Point2 → Point2 := henon 9 1

noncomputable def henon91Inv : Point2 → Point2 := henonInv 9 1

theorem henon91Inv_henon91 (p : Point2) : henon91Inv (henon91 p) = p :=
  henonInv_henon 9 1 (by norm_num) p

theorem henon91_henon91Inv (p : Point2) : henon91 (henon91Inv p) = p :=
  henon_henonInv 9 1 (by norm_num) p

theorem henon91_in_horseshoe_regime : (9 : ℝ) > 2 * (1 + |(1 : ℝ)|) ^ 2 := by
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 1)]
  norm_num

def IsHenonPeriodic (z : Point2) : Prop :=
  ∃ k : ℕ, 0 < k ∧ Nat.iterate henon91 k z = z

end Ripple.BoundedUniversality.HenonSelector
