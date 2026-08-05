/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Kernel

/-!
# Pair interaction distribution for bi-molecular CRNs

A bi-molecular interaction draws an unordered pair uniformly from the current
population. `PairKind` records its species composition, and `PairKind.weight`
counts the pairs of each composition.
-/

namespace Tri

open scoped ENNReal

/-- The three possible compositions of an unordered pair drawn from species
`X` and `Y`. -/
inductive PairKind
  | xx
  | xy
  | yy
  deriving DecidableEq, Fintype, Repr

namespace PairKind

/-- The number of unordered pairs of each composition in a mixture with `x`
molecules of `X` and `y` molecules of `Y`. -/
def weight (x y : ℕ) : PairKind → ℕ
  | .xx => Nat.choose x 2
  | .xy => x * y
  | .yy => Nat.choose y 2

end PairKind

/-- The three pair-composition counts sum to the total number of unordered
pairs. -/
theorem pair_two_split (x y : ℕ) :
    Nat.choose (x + y) 2 = Nat.choose x 2 + x * y + Nat.choose y 2 := by
  rw [Nat.add_choose_eq]
  rw [show (2 : ℕ) = 1 + 1 from rfl, Finset.Nat.antidiagonal_succ]
  simp [Finset.Nat.antidiagonal_succ, Nat.choose_one_right, Nat.choose_zero_right,
    Finset.sum_insert]
  ring

/-- The pair weights sum to the total number of unordered pairs `C(x+y,2)`;
this is the normalisation identity for `pairPMF`. -/
theorem pair_sum_weight (x y : ℕ) :
    (∑ k : PairKind, PairKind.weight x y k) = Nat.choose (x + y) 2 := by
  rw [show (Finset.univ : Finset PairKind) = {PairKind.xx, PairKind.xy, PairKind.yy} from rfl]
  simp [PairKind.weight, pair_two_split]
  omega

/-- The distribution of the composition of a uniformly drawn unordered pair, in
a mixture of `x` molecules of `X` and `y` of `Y` with `2 ≤ x + y`.  Mirrors
`interactionPMF` one degree lower. -/
noncomputable def pairPMF (x y : ℕ) (h : 2 ≤ x + y) : PMF PairKind :=
  PMF.ofFintype
    (fun k => (PairKind.weight x y k : ℝ≥0∞) / (Nat.choose (x + y) 2 : ℝ≥0∞))
    (by
      have hpos : 0 < Nat.choose (x + y) 2 := Nat.choose_pos h
      have hne : ((Nat.choose (x + y) 2 : ℕ) : ℝ≥0∞) ≠ 0 := by
        simpa using (Nat.cast_ne_zero (R := ℝ≥0∞)).mpr hpos.ne'
      have htop : ((Nat.choose (x + y) 2 : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
      simp only [div_eq_mul_inv, ← Finset.sum_mul]
      rw [show ∑ k : PairKind, ((PairKind.weight x y k : ℕ) : ℝ≥0∞)
            = ((∑ k : PairKind, PairKind.weight x y k : ℕ) : ℝ≥0∞) by push_cast; rfl]
      rw [pair_sum_weight, ← div_eq_mul_inv]
      exact ENNReal.div_self hne htop)

@[simp] theorem pairPMF_apply (x y : ℕ) (h : 2 ≤ x + y) (k : PairKind) :
    pairPMF x y h k = (PairKind.weight x y k : ℝ≥0∞) / (Nat.choose (x + y) 2 : ℝ≥0∞) :=
  rfl

/-- **Three-species pair split.**  For the Double-B / Single-B systems (species
`X`, `Y`, `B` with `x + y + b` molecules) an unordered pair has one of six
compositions; their counts sum to `C(x+y+b,2)`.  This is the normalisation for
the bi-molecular step kernel and follows from `pair_two_split` applied twice. -/
theorem three_pair_split (x y b : ℕ) :
    Nat.choose (x + y + b) 2 =
      Nat.choose x 2 + Nat.choose y 2 + Nat.choose b 2 + x * y + x * b + y * b := by
  rw [pair_two_split (x + y) b, pair_two_split x y]
  ring

end Tri
