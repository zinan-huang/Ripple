/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.HeavyBDirection

/-!
# Heavy-B productive mass floor

The productive weight `x*y + x*b + y*b` is the total weight of the three
non-inert compositions. Within a live band where `x ≥ 1`, the productive
weight is at least `y`, giving a productive probability floor that feeds
the raw→productive clock conversion.
-/

namespace Tri

open scoped ENNReal

/-- Productive weight of a Heavy-B state. -/
def heavyProductiveWeight (x y b : ℕ) : ℕ :=
  x * y + x * b + y * b

/-- On a live state with `x ≥ 1`, the productive weight is at least `y`. -/
theorem heavyProductiveWeight_ge_y {x y : ℕ} (b : ℕ) (hx : 1 ≤ x) :
    y ≤ heavyProductiveWeight x y b := by
  unfold heavyProductiveWeight; nlinarith

/-- Level-only productive floor for Heavy-B, in subtraction-free witness form. -/
theorem heavyProductiveWeight_level_floor (n x y b d c : ℕ)
    (hinv : x + y + 2 * b = n)
    (hgap : n + d = 2 * (x + b))
    (hco : (x + b) + c = n) :
    d * c ≤ heavyProductiveWeight x y b := by
  have hd : d ≤ x := by omega
  have hc : c = y + b := by omega
  calc
    d * c ≤ x * c := Nat.mul_le_mul_right c hd
    _ = x * (y + b) := by rw [hc]
    _ ≤ heavyProductiveWeight x y b := by
      unfold heavyProductiveWeight
      nlinarith

/-- The productive probability is the productive weight over `C(m,2)`. -/
theorem heavyProductive_mass {n : ℕ} (hn : 3 ≤ n) (s : HeavyState n)
    (h : 2 ≤ heavyEntities s) :
    dbPairPMF s.1.x s.1.y s.1.b h .xy +
        dbPairPMF s.1.x s.1.y s.1.b h .xb +
        dbPairPMF s.1.x s.1.y s.1.b h .yb =
      ((heavyProductiveWeight s.1.x s.1.y s.1.b : ℕ) : ℝ≥0∞) /
        ((Nat.choose (heavyEntities s) 2 : ℕ) : ℝ≥0∞) := by
  simp only [dbPairPMF_apply, PairComp.weight, heavyEntities]
  rw [ENNReal.div_add_div_same, ENNReal.div_add_div_same]
  congr 1
  push_cast
  unfold heavyProductiveWeight
  push_cast
  ring

/-- Within a live band (`x ≥ 1`), the productive mass is at least
`y / C(n,2)`, since productive weight ≥ y and C(m,2) ≤ C(n,2). -/
theorem heavyProductive_mass_ge {n : ℕ} (hn : 3 ≤ n) (s : HeavyState n)
    (hx : 1 ≤ s.1.x) :
    ((s.1.y : ℕ) : ℝ≥0∞) / ((Nat.choose n 2 : ℕ) : ℝ≥0∞) ≤
      dbPairPMF s.1.x s.1.y s.1.b (heavy_two_entities hn s) .xy +
        dbPairPMF s.1.x s.1.y s.1.b (heavy_two_entities hn s) .xb +
        dbPairPMF s.1.x s.1.y s.1.b (heavy_two_entities hn s) .yb := by
  rw [heavyProductive_mass hn s]
  have hprod : s.1.y ≤ heavyProductiveWeight s.1.x s.1.y s.1.b :=
    heavyProductiveWeight_ge_y s.1.b hx
  have hent : heavyEntities s ≤ n := by
    have := s.2; simp only [BiCfg.HeavyInv, heavyEntities] at this ⊢; omega
  have hC : Nat.choose (heavyEntities s) 2 ≤ Nat.choose n 2 :=
    Nat.choose_le_choose 2 hent
  gcongr

/-- Level-only productive mass floor for Heavy-B, over the ambient denominator. -/
theorem heavyProductive_mass_level_ge {n : ℕ} (hn : 3 ≤ n) (s : HeavyState n)
    (d c : ℕ)
    (hgap : n + d = 2 * BiCfg.heavyLevel s.1)
    (hco : BiCfg.heavyLevel s.1 + c = n) :
    ((d * c : ℕ) : ℝ≥0∞) / ((Nat.choose n 2 : ℕ) : ℝ≥0∞) ≤
      dbPairPMF s.1.x s.1.y s.1.b (heavy_two_entities hn s) .xy +
        dbPairPMF s.1.x s.1.y s.1.b (heavy_two_entities hn s) .xb +
        dbPairPMF s.1.x s.1.y s.1.b (heavy_two_entities hn s) .yb := by
  rw [heavyProductive_mass hn s]
  have hprod : d * c ≤ heavyProductiveWeight s.1.x s.1.y s.1.b := by
    exact heavyProductiveWeight_level_floor n s.1.x s.1.y s.1.b d c s.2 (by
      simpa [BiCfg.heavyLevel] using hgap) (by
      simpa [BiCfg.heavyLevel] using hco)
  have hent : heavyEntities s ≤ n := by
    have := s.2; simp only [BiCfg.HeavyInv, heavyEntities] at this ⊢; omega
  have hC : Nat.choose (heavyEntities s) 2 ≤ Nat.choose n 2 :=
    Nat.choose_le_choose 2 hent
  gcongr

end Tri

#print axioms Tri.heavyProductiveWeight_ge_y
#print axioms Tri.heavyProductiveWeight_level_floor
#print axioms Tri.heavyProductive_mass
#print axioms Tri.heavyProductive_mass_ge
#print axioms Tri.heavyProductive_mass_level_ge
