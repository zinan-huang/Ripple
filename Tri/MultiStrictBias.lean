/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.MultiPairBias
import Tri.FiveJumpMGF

/-!
# Strict fixed-pair odds under a global plurality gap

Nonnegative linear drift is not enough for the five-jump geometric potential:
the direct size-two adverse jump must pay two powers of the common base.  Under
a pairwise gap `d`, the subtraction-free common base

`4 n² / (4 n² + d²)`

does exactly this.  Direct `X/Y` reactions satisfy the squared-base inequality;
each third-party contribution satisfies the one-power inequality, provided
`X` beats both other species by `d`.
-/

namespace Tri.Multi

open scoped BigOperators ENNReal

variable {m n : ℕ}

noncomputable def pairGapBase (n d : ℕ) : ℝ≥0∞ :=
  (4 * n ^ 2 : ℕ) / (4 * n ^ 2 + d ^ 2 : ℕ)

theorem pairGapBase_le_one (n d : ℕ) (hn : 0 < n) :
    pairGapBase n d ≤ 1 := by
  unfold pairGapBase
  have hden0 : ((4 * n ^ 2 + d ^ 2 : ℕ) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (by positivity : 4 * n ^ 2 + d ^ 2 ≠ 0)
  have hdenTop : ((4 * n ^ 2 + d ^ 2 : ℕ) : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  calc
    ((4 * n ^ 2 : ℕ) : ℝ≥0∞) /
          ((4 * n ^ 2 + d ^ 2 : ℕ) : ℝ≥0∞) ≤
        ((4 * n ^ 2 + d ^ 2 : ℕ) : ℝ≥0∞) /
          ((4 * n ^ 2 + d ^ 2 : ℕ) : ℝ≥0∞) := by
      exact ENNReal.div_le_div_right
        (by exact_mod_cast (Nat.le_add_right (4 * n ^ 2) (d ^ 2))) _
    _ = 1 := ENNReal.div_self hden0 hdenTop

theorem pairGapBase_ne_zero (n d : ℕ) (hn : 0 < n) :
    pairGapBase n d ≠ 0 := by
  unfold pairGapBase
  simp only [ne_eq, ENNReal.div_eq_zero_iff, not_or]
  exact ⟨by
    simp only [Nat.cast_eq_zero]
    positivity, ENNReal.natCast_ne_top _⟩

private theorem direct_square_ratio_real
    (N d X : ℝ) (hN : 0 ≤ N) (hd : 0 ≤ d)
    (hdN : d ≤ N) (hdX : d ≤ X) (hXN : X ≤ N) :
    (4 * N ^ 2 + d ^ 2) ^ 2 * (X - d) ≤
      (4 * N ^ 2) ^ 2 * X := by
  have hxd : 0 ≤ X - d := sub_nonneg.mpr hdX
  have hprod :
      d * (8 * N ^ 2 + d ^ 2) * (X - d) ≤ 9 * N ^ 4 := by
    calc
      d * (8 * N ^ 2 + d ^ 2) * (X - d) ≤
          N * (8 * N ^ 2 + N ^ 2) * N := by
        gcongr <;> nlinarith [sq_nonneg N, sq_nonneg d]
      _ = 9 * N ^ 4 := by ring
  have hnonneg :
      0 ≤ d *
        (16 * N ^ 4 - d * (8 * N ^ 2 + d ^ 2) * (X - d)) := by
    apply mul_nonneg hd
    nlinarith [sq_nonneg (N ^ 2)]
  nlinarith

/-- The direct adverse size-two jump pays two powers of the common base, in
division-free natural arithmetic. -/
theorem directWeight_square_cross
    (N d x y : ℕ) (hxN : x ≤ N) (hgap : y + d ≤ x) :
    (4 * N ^ 2 + d ^ 2) ^ 2 * (Nat.choose y 2 * x) ≤
      (4 * N ^ 2) ^ 2 * (Nat.choose x 2 * y) := by
  by_cases hy : y = 0
  · simp [hy]
  have hN : 0 < N := by omega
  have hx : 0 < x := by omega
  have hdN : d ≤ N := by omega
  have hdX : d ≤ x - 1 := by omega
  have hXN : x - 1 ≤ N := by omega
  have hratioReal :=
    direct_square_ratio_real
      (N : ℝ) (d : ℝ) ((x - 1 : ℕ) : ℝ)
      (by positivity) (by positivity)
      (by exact_mod_cast hdN)
      (by exact_mod_cast hdX)
      (by exact_mod_cast hXN)
  have hratio :
      (4 * N ^ 2 + d ^ 2) ^ 2 * (y - 1) ≤
        (4 * N ^ 2) ^ 2 * (x - 1) := by
    calc
      (4 * N ^ 2 + d ^ 2) ^ 2 * (y - 1) ≤
          (4 * N ^ 2 + d ^ 2) ^ 2 * ((x - 1) - d) := by
        exact Nat.mul_le_mul_left _ (by omega)
      _ ≤ (4 * N ^ 2) ^ 2 * (x - 1) := by
        exact_mod_cast hratioReal
  have htwoY : 2 * Nat.choose y 2 = y * (y - 1) :=
    two_mul_choose_two y
  have htwoX : 2 * Nat.choose x 2 = x * (x - 1) :=
    two_mul_choose_two x
  have hscaled :
      2 * ((4 * N ^ 2 + d ^ 2) ^ 2 * (Nat.choose y 2 * x)) ≤
        2 * ((4 * N ^ 2) ^ 2 * (Nat.choose x 2 * y)) := by
    calc
      2 * ((4 * N ^ 2 + d ^ 2) ^ 2 * (Nat.choose y 2 * x)) =
          (4 * N ^ 2 + d ^ 2) ^ 2 * x *
            (2 * Nat.choose y 2) := by ring
      _ = (4 * N ^ 2 + d ^ 2) ^ 2 * x *
            (y * (y - 1)) := by rw [htwoY]
      _ = x * y * ((4 * N ^ 2 + d ^ 2) ^ 2 * (y - 1)) := by
        ring
      _ ≤ x * y * ((4 * N ^ 2) ^ 2 * (x - 1)) :=
        Nat.mul_le_mul_left (x * y) hratio
      _ = (4 * N ^ 2) ^ 2 * y * (x * (x - 1)) := by ring
      _ = (4 * N ^ 2) ^ 2 * y * (2 * Nat.choose x 2) := by
        rw [htwoX]
      _ = 2 * ((4 * N ^ 2) ^ 2 * (Nat.choose x 2 * y)) := by
        ring
  omega

/-- Exact doubled difference between favorable and adverse third-party raw
weights. -/
theorem thirdParty_doubled_gap_identity
    (x y z : ℕ) (hy : y ≤ x) (hz : z ≤ x) :
    2 * (Nat.choose x 2 * z + Nat.choose z 2 * y) =
      2 * (Nat.choose z 2 * x + Nat.choose y 2 * z) +
        z * (x - y) * (x + y - z) := by
  have htwoX : 2 * Nat.choose x 2 = x * (x - 1) :=
    two_mul_choose_two x
  have htwoY : 2 * Nat.choose y 2 = y * (y - 1) :=
    two_mul_choose_two y
  have htwoZ : 2 * Nat.choose z 2 = z * (z - 1) :=
    two_mul_choose_two z
  have hzsum : z ≤ x + y := by omega
  have hchooseInt (a : ℕ) :
      (2 : ℤ) * (Nat.choose a 2 : ℤ) =
        (a : ℤ) * ((a : ℤ) - 1) := by
    rw [show (2 : ℤ) * (Nat.choose a 2 : ℤ) =
        ((2 * Nat.choose a 2 : ℕ) : ℤ) by
      push_cast
      ring, two_mul_choose_two]
    push_cast
    cases a <;> simp
  have hidInt :
      (((2 * (Nat.choose x 2 * z + Nat.choose z 2 * y) : ℕ) : ℤ)) =
        (((2 * (Nat.choose z 2 * x + Nat.choose y 2 * z) +
          z * (x - y) * (x + y - z) : ℕ) : ℤ)) := by
    push_cast
    rw [show (2 : ℤ) *
          ((Nat.choose x 2 : ℤ) * z + (Nat.choose z 2 : ℤ) * y) =
        ((2 : ℤ) * (Nat.choose x 2 : ℤ)) * z +
          ((2 : ℤ) * (Nat.choose z 2 : ℤ)) * y by ring,
      show (2 : ℤ) *
          ((Nat.choose z 2 : ℤ) * x + (Nat.choose y 2 : ℤ) * z) =
        ((2 : ℤ) * (Nat.choose z 2 : ℤ)) * x +
          ((2 : ℤ) * (Nat.choose y 2 : ℤ)) * z by ring,
      hchooseInt x, hchooseInt z, hchooseInt y,
      Int.natCast_sub hy, Int.natCast_sub hzsum]
    push_cast
    ring
  exact_mod_cast hidInt

/-- Every third-party adverse size-one jump pays one power of the common base,
again without division. -/
theorem thirdPartyWeight_cross
    (N d x y z : ℕ)
    (hxN : x ≤ N) (hyN : y ≤ N) (hzN : z ≤ N)
    (hgapY : y + d ≤ x) (hgapZ : z + d ≤ x) :
    (4 * N ^ 2 + d ^ 2) *
        (Nat.choose z 2 * x + Nat.choose y 2 * z) ≤
      (4 * N ^ 2) *
        (Nat.choose x 2 * z + Nat.choose z 2 * y) := by
  let D := Nat.choose z 2 * x + Nat.choose y 2 * z
  let U := Nat.choose x 2 * z + Nat.choose z 2 * y
  let G := z * (x - y) * (x + y - z)
  have hyx : y ≤ x := by omega
  have hzx : z ≤ x := by omega
  have hgapIdentity : 2 * U = 2 * D + G := by
    dsimp only [U, D, G]
    exact thirdParty_doubled_gap_identity x y z hyx hzx
  have hD :
      2 * D ≤ 2 * z * N ^ 2 := by
    dsimp only [D]
    rw [show 2 * (Nat.choose z 2 * x + Nat.choose y 2 * z) =
        (2 * Nat.choose z 2) * x +
          (2 * Nat.choose y 2) * z by ring,
      two_mul_choose_two, two_mul_choose_two]
    calc
      z * (z - 1) * x + y * (y - 1) * z ≤
          z * N * N + N * N * z := by
        apply Nat.add_le_add
        · gcongr <;> omega
        · gcongr <;> omega
      _ = 2 * z * N ^ 2 := by ring
  have hG : z * d ^ 2 ≤ G := by
    dsimp only [G]
    have hxy : d ≤ x - y := by omega
    have hxz : d ≤ x + y - z := by omega
    simpa [pow_two, Nat.mul_assoc] using
      Nat.mul_le_mul_left z (Nat.mul_le_mul hxy hxz)
  have hcore : d ^ 2 * D ≤ 4 * N ^ 2 * (U - D) := by
    have htwiceGap : 2 * (U - D) = G := by omega
    have hleft : 2 * (d ^ 2 * D) ≤
        2 * z * N ^ 2 * d ^ 2 := by
      calc
        2 * (d ^ 2 * D) = d ^ 2 * (2 * D) := by ring
        _ ≤ d ^ 2 * (2 * z * N ^ 2) :=
          Nat.mul_le_mul_left _ hD
        _ = 2 * z * N ^ 2 * d ^ 2 := by ring
    have hright :
        2 * z * N ^ 2 * d ^ 2 ≤
          2 * (4 * N ^ 2 * (U - D)) := by
      calc
        2 * z * N ^ 2 * d ^ 2 ≤
            4 * N ^ 2 * (z * d ^ 2) := by
          ring_nf
          gcongr
          norm_num
        _ ≤ 4 * N ^ 2 * G :=
          Nat.mul_le_mul_left _ hG
        _ = 2 * (4 * N ^ 2 * (U - D)) := by
          rw [← htwiceGap]
          ring
    omega
  calc
    (4 * N ^ 2 + d ^ 2) * D =
        4 * N ^ 2 * D + d ^ 2 * D := by ring
    _ ≤ 4 * N ^ 2 * D + 4 * N ^ 2 * (U - D) :=
      Nat.add_le_add_left hcore _
    _ = 4 * N ^ 2 * U := by
      have hDU : D ≤ U := by omega
      rw [← Nat.mul_add, Nat.add_sub_of_le hDU]

/-- Direct physical PMF mass inequality with the squared common base. -/
theorem reverse_directedFireMass_le_base_sq
    (c : Config m n) (h3 : 3 ≤ n)
    (X Y : Species m) (hXY : X ≠ Y)
    (d : ℕ) (hgap : count c Y + d ≤ count c X) :
    directedFireMass c h3 Y X ≤
      directedFireMass c h3 X Y * pairGapBase n d ^ 2 := by
  rw [directedFireMass_eq c h3 Y X (Ne.symm hXY),
    directedFireMass_eq c h3 X Y hXY]
  apply div_le_div_mul_right
  unfold pairGapBase
  rw [show
      (((4 * n ^ 2 : ℕ) : ℝ≥0∞) /
        ((4 * n ^ 2 + d ^ 2 : ℕ) : ℝ≥0∞)) ^ 2 =
        (((4 * n ^ 2 : ℕ) : ℝ≥0∞) ^ 2) /
          (((4 * n ^ 2 + d ^ 2 : ℕ) : ℝ≥0∞) ^ 2) by
      simp only [div_eq_mul_inv, mul_pow, ← ENNReal.inv_pow],
    ← mul_div_assoc]
  have hden0 :
      (((4 * n ^ 2 + d ^ 2 : ℕ) : ℝ≥0∞) ^ 2) ≠ 0 := by
    apply pow_ne_zero
    exact_mod_cast (by
      have : 0 < n := by omega
      positivity : 4 * n ^ 2 + d ^ 2 ≠ 0)
  have hdenTop :
      (((4 * n ^ 2 + d ^ 2 : ℕ) : ℝ≥0∞) ^ 2) ≠ ⊤ := by
    finiteness
  rw [ENNReal.le_div_iff_mul_le
    (Or.inl hden0) (Or.inl hdenTop)]
  have hXn : count c X ≤ n :=
    Nat.le_of_lt_succ (c.1 X).isLt
  exact_mod_cast (by
    simpa [directedFireWeight, mul_comm, mul_left_comm, mul_assoc] using
      directWeight_square_cross n d (count c X) (count c Y)
        hXn hgap)

/-- One third species' physical adverse mass pays one common-base power. -/
theorem thirdPartyDownMass_le_upMass_mul_base
    (c : Config m n) (h3 : 3 ≤ n)
    (X Y Z : Species m)
    (hXZ : X ≠ Z) (hYZ : Y ≠ Z)
    (d : ℕ)
    (hgapY : count c Y + d ≤ count c X)
    (hgapZ : count c Z + d ≤ count c X) :
    thirdPartyDownMass c h3 X Y Z ≤
      thirdPartyUpMass c h3 X Y Z * pairGapBase n d := by
  rw [thirdPartyDownMass_eq c h3 X Y Z
      (Ne.symm hXZ) hYZ,
    thirdPartyUpMass_eq c h3 X Y Z hXZ (by
      exact fun h => hYZ h.symm)]
  apply div_le_div_mul_right
  unfold pairGapBase
  have hden0 :
      (((4 * n ^ 2 + d ^ 2 : ℕ) : ℝ≥0∞)) ≠ 0 := by
    exact_mod_cast (by
      have : 0 < n := by omega
      positivity : 4 * n ^ 2 + d ^ 2 ≠ 0)
  have hdenTop :
      (((4 * n ^ 2 + d ^ 2 : ℕ) : ℝ≥0∞)) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  rw [← mul_div_assoc]
  rw [ENNReal.le_div_iff_mul_le
    (Or.inl hden0) (Or.inl hdenTop)]
  have hXn : count c X ≤ n :=
    Nat.le_of_lt_succ (c.1 X).isLt
  have hYn : count c Y ≤ n :=
    Nat.le_of_lt_succ (c.1 Y).isLt
  have hZn : count c Z ≤ n :=
    Nat.le_of_lt_succ (c.1 Z).isLt
  exact_mod_cast (by
    simpa [thirdPartyDownWeight, thirdPartyUpWeight,
      directedFireWeight, mul_comm, mul_left_comm, mul_assoc] using
      thirdPartyWeight_cross n d
        (count c X) (count c Y) (count c Z)
        hXn hYn hZn hgapY hgapZ)

/-- Aggregate strict one-jump odds over all third species. -/
theorem thirdPartyDownMass_sum_le_up_mul_base
    (c : Config m n) (h3 : 3 ≤ n)
    (X Y : Species m) (hXY : X ≠ Y)
    (d : ℕ) (hgap : HasPairwiseGap c X d) :
    (∑ Z ∈ thirdSpecies X Y,
        thirdPartyDownMass c h3 X Y Z) ≤
      (∑ Z ∈ thirdSpecies X Y,
        thirdPartyUpMass c h3 X Y Z) * pairGapBase n d := by
  calc
    (∑ Z ∈ thirdSpecies X Y,
        thirdPartyDownMass c h3 X Y Z) ≤
      ∑ Z ∈ thirdSpecies X Y,
        thirdPartyUpMass c h3 X Y Z * pairGapBase n d := by
      apply Finset.sum_le_sum
      intro Z hZ
      have hZX : Z ≠ X :=
        (Finset.mem_erase.mp (Finset.mem_erase.mp hZ).2).1
      have hZY : Z ≠ Y := (Finset.mem_erase.mp hZ).1
      exact thirdPartyDownMass_le_upMass_mul_base
        c h3 X Y Z (Ne.symm hZX) (Ne.symm hZY) d
        (hgap Y (Ne.symm hXY)) (hgap Z hZX)
    _ = (∑ Z ∈ thirdSpecies X Y,
        thirdPartyUpMass c h3 X Y Z) * pairGapBase n d := by
      rw [Finset.sum_mul]

end Tri.Multi

#print axioms Tri.Multi.directWeight_square_cross
#print axioms Tri.Multi.thirdParty_doubled_gap_identity
#print axioms Tri.Multi.thirdPartyWeight_cross
#print axioms Tri.Multi.reverse_directedFireMass_le_base_sq
#print axioms Tri.Multi.thirdPartyDownMass_sum_le_up_mul_base
