/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.MultiProductivePair

/-!
# Linear-gap odds for multi-species Tri

The proper-stage no-backsliding exponent requires a geometric base whose
distance from one is linear, rather than quadratic, in the protected gap.
The key third-party identity already contains this strength: under global
gap `d`, `(x-y) * (x+y-z) ≥ d*x`.  Retaining that product proves the common
base `2n/(2n+d)` for both one-unit and two-unit adverse jumps.
-/

namespace Tri.Multi

open scoped BigOperators ENNReal

variable {m n : ℕ}

/-- Common geometric base with linear gap slack. -/
noncomputable def pairGapLinearBase (n d : ℕ) : ℝ≥0∞ :=
  (2 * n : ℕ) / (2 * n + d : ℕ)

theorem pairGapLinearBase_le_one
    (n d : ℕ) (hn : 0 < n) :
    pairGapLinearBase n d ≤ 1 := by
  unfold pairGapLinearBase
  have hden0 : (((2 * n + d : ℕ) : ℝ≥0∞)) ≠ 0 := by
    exact_mod_cast (by omega : 2 * n + d ≠ 0)
  have hdenTop : (((2 * n + d : ℕ) : ℝ≥0∞)) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  calc
    ((2 * n : ℕ) : ℝ≥0∞) / ((2 * n + d : ℕ) : ℝ≥0∞) ≤
        ((2 * n + d : ℕ) : ℝ≥0∞) /
          ((2 * n + d : ℕ) : ℝ≥0∞) := by
      exact ENNReal.div_le_div_right (by exact_mod_cast (by omega)) _
    _ = 1 := ENNReal.div_self hden0 hdenTop

theorem pairGapLinearBase_ne_zero
    (n d : ℕ) (hn : 0 < n) :
    pairGapLinearBase n d ≠ 0 := by
  unfold pairGapLinearBase
  simp only [ne_eq, ENNReal.div_eq_zero_iff, not_or]
  exact ⟨by exact_mod_cast (by omega : 2 * n ≠ 0),
    ENNReal.natCast_ne_top _⟩

private theorem direct_linear_square_ratio_real
    (N d X : ℝ) (hN : 0 ≤ N) (hd : 0 ≤ d)
    (hXN : X ≤ N) :
    (2 * N + d) ^ 2 * (X - d) ≤
      (2 * N) ^ 2 * X := by
  have hcoef : 0 ≤ 4 * N + d := by positivity
  have hcore : (4 * N + d) * X ≤ (2 * N + d) ^ 2 := by
    calc
      (4 * N + d) * X ≤ (4 * N + d) * N :=
        mul_le_mul_of_nonneg_left hXN hcoef
      _ ≤ (2 * N + d) ^ 2 := by nlinarith
  have hnonneg :
      0 ≤ d * ((2 * N + d) ^ 2 - (4 * N + d) * X) :=
    mul_nonneg hd (sub_nonneg.mpr hcore)
  nlinarith

/-- A direct adverse size-two jump pays two powers of the linear base. -/
theorem directWeight_linear_square_cross
    (N d x y : ℕ) (hxN : x ≤ N) (hgap : y + d ≤ x) :
    (2 * N + d) ^ 2 * (Nat.choose y 2 * x) ≤
      (2 * N) ^ 2 * (Nat.choose x 2 * y) := by
  by_cases hy : y = 0
  · simp [hy]
  have hN : 0 < N := by omega
  have hx : 0 < x := by omega
  have hdN : d ≤ N := by omega
  have hdX : d ≤ x - 1 := by omega
  have hXN : x - 1 ≤ N := by omega
  have hratioReal :=
    direct_linear_square_ratio_real
      (N : ℝ) (d : ℝ) ((x - 1 : ℕ) : ℝ)
      (by positivity) (by positivity)
      (by exact_mod_cast hXN)
  have hratio :
      (2 * N + d) ^ 2 * (y - 1) ≤
        (2 * N) ^ 2 * (x - 1) := by
    calc
      (2 * N + d) ^ 2 * (y - 1) ≤
          (2 * N + d) ^ 2 * ((x - 1) - d) := by
        exact Nat.mul_le_mul_left _ (by omega)
      _ ≤ (2 * N) ^ 2 * (x - 1) := by
        exact_mod_cast hratioReal
  have htwoY : 2 * Nat.choose y 2 = y * (y - 1) :=
    two_mul_choose_two y
  have htwoX : 2 * Nat.choose x 2 = x * (x - 1) :=
    two_mul_choose_two x
  have hscaled :
      2 * ((2 * N + d) ^ 2 * (Nat.choose y 2 * x)) ≤
        2 * ((2 * N) ^ 2 * (Nat.choose x 2 * y)) := by
    calc
      2 * ((2 * N + d) ^ 2 * (Nat.choose y 2 * x)) =
          (2 * N + d) ^ 2 * x * (2 * Nat.choose y 2) := by ring
      _ = (2 * N + d) ^ 2 * x * (y * (y - 1)) := by rw [htwoY]
      _ = x * y * ((2 * N + d) ^ 2 * (y - 1)) := by ring
      _ ≤ x * y * ((2 * N) ^ 2 * (x - 1)) :=
        Nat.mul_le_mul_left (x * y) hratio
      _ = (2 * N) ^ 2 * y * (x * (x - 1)) := by ring
      _ = (2 * N) ^ 2 * y * (2 * Nat.choose x 2) := by rw [htwoX]
      _ = 2 * ((2 * N) ^ 2 * (Nat.choose x 2 * y)) := by ring
  omega

/-- The product in the exact third-party drift identity retains one full
factor of the plurality count. -/
theorem gap_mul_count_le_thirdParty_gap_product
    (d x y z : ℕ) (hgapY : y + d ≤ x) (hgapZ : z + d ≤ x) :
    d * x ≤ (x - y) * (x + y - z) := by
  have hyx : y ≤ x := by omega
  have hzx : z ≤ x := by omega
  have hzxy : z ≤ x + y := by omega
  by_cases hzy : z ≤ y
  · exact Nat.mul_le_mul (by omega) (by omega)
  · have hyz : y ≤ z := by omega
    have hidInt :
        (((x - y) * (x + y - z) : ℕ) : ℤ) =
          (((x - z) * x + (z - y) * y : ℕ) : ℤ) := by
      push_cast
      rw [Int.natCast_sub hyx, Int.natCast_sub hzxy,
        Int.natCast_sub hzx, Int.natCast_sub hyz]
      push_cast
      ring
    have hid :
        (x - y) * (x + y - z) =
          (x - z) * x + (z - y) * y := by
      exact_mod_cast hidInt
    calc
      d * x ≤ (x - z) * x := Nat.mul_le_mul_right x (by omega)
      _ ≤ (x - z) * x + (z - y) * y := Nat.le_add_right _ _
      _ = (x - y) * (x + y - z) := hid.symm

/-- A third-party adverse size-one jump pays one power of the linear base. -/
theorem thirdPartyWeight_linear_cross
    (N d x y z : ℕ)
    (hxN : x ≤ N) (hgapY : y + d ≤ x) (hgapZ : z + d ≤ x) :
    (2 * N + d) *
        (Nat.choose z 2 * x + Nat.choose y 2 * z) ≤
      (2 * N) *
        (Nat.choose x 2 * z + Nat.choose z 2 * y) := by
  let D := Nat.choose z 2 * x + Nat.choose y 2 * z
  let U := Nat.choose x 2 * z + Nat.choose z 2 * y
  let G := z * (x - y) * (x + y - z)
  have hyx : y ≤ x := by omega
  have hzx : z ≤ x := by omega
  have hgapIdentity : 2 * U = 2 * D + G := by
    dsimp only [U, D, G]
    exact thirdParty_doubled_gap_identity x y z hyx hzx
  have hD : D ≤ z * x ^ 2 := by
    have htwo :
        2 * D ≤ 2 * (z * x ^ 2) := by
      dsimp only [D]
      rw [show 2 * (Nat.choose z 2 * x + Nat.choose y 2 * z) =
          (2 * Nat.choose z 2) * x +
            (2 * Nat.choose y 2) * z by ring,
        two_mul_choose_two, two_mul_choose_two]
      calc
        z * (z - 1) * x + y * (y - 1) * z ≤
            z * x * x + x * x * z := by
          apply Nat.add_le_add <;> gcongr <;> omega
        _ = 2 * (z * x ^ 2) := by ring
    omega
  have hG : z * d * x ≤ G := by
    dsimp only [G]
    simpa [Nat.mul_assoc] using
      Nat.mul_le_mul_left z
        (gap_mul_count_le_thirdParty_gap_product d x y z hgapY hgapZ)
  have hcore : d * D ≤ 2 * N * (U - D) := by
    have htwiceGap : 2 * (U - D) = G := by omega
    calc
      d * D ≤ d * (z * x ^ 2) := Nat.mul_le_mul_left d hD
      _ = z * d * x * x := by ring
      _ ≤ z * d * x * N := Nat.mul_le_mul_left (z * d * x) hxN
      _ ≤ G * N := Nat.mul_le_mul_right N hG
      _ = 2 * N * (U - D) := by rw [← htwiceGap]; ring
  calc
    (2 * N + d) * D = 2 * N * D + d * D := by ring
    _ ≤ 2 * N * D + 2 * N * (U - D) :=
      Nat.add_le_add_left hcore _
    _ = 2 * N * U := by
      have hDU : D ≤ U := by omega
      rw [← Nat.mul_add, Nat.add_sub_of_le hDU]

/-- Direct physical mass inequality at the stronger linear base. -/
theorem reverse_directedFireMass_le_linearBase_sq
    (c : Config m n) (h3 : 3 ≤ n)
    (X Y : Species m) (hXY : X ≠ Y)
    (d : ℕ) (hgap : count c Y + d ≤ count c X) :
    directedFireMass c h3 Y X ≤
      directedFireMass c h3 X Y * pairGapLinearBase n d ^ 2 := by
  rw [directedFireMass_eq c h3 Y X (Ne.symm hXY),
    directedFireMass_eq c h3 X Y hXY]
  apply div_le_div_mul_right
  unfold pairGapLinearBase
  rw [show
      (((2 * n : ℕ) : ℝ≥0∞) /
        ((2 * n + d : ℕ) : ℝ≥0∞)) ^ 2 =
        (((2 * n : ℕ) : ℝ≥0∞) ^ 2) /
          (((2 * n + d : ℕ) : ℝ≥0∞) ^ 2) by
      simp only [div_eq_mul_inv, mul_pow, ← ENNReal.inv_pow],
    ← mul_div_assoc]
  have hden0 : ((((2 * n + d : ℕ) : ℝ≥0∞) ^ 2)) ≠ 0 := by
    apply pow_ne_zero
    exact_mod_cast (by omega : 2 * n + d ≠ 0)
  have hdenTop : ((((2 * n + d : ℕ) : ℝ≥0∞) ^ 2)) ≠ ⊤ := by
    finiteness
  rw [ENNReal.le_div_iff_mul_le
    (Or.inl hden0) (Or.inl hdenTop)]
  have hXn : count c X ≤ n :=
    Nat.le_of_lt_succ (c.1 X).isLt
  exact_mod_cast (by
    simpa [directedFireWeight, mul_comm, mul_left_comm, mul_assoc] using
      directWeight_linear_square_cross
        n d (count c X) (count c Y) hXn hgap)

/-- One third species' adverse mass pays the stronger linear base. -/
theorem thirdPartyDownMass_le_upMass_mul_linearBase
    (c : Config m n) (h3 : 3 ≤ n)
    (X Y Z : Species m)
    (hXZ : X ≠ Z) (hYZ : Y ≠ Z)
    (d : ℕ)
    (hgapY : count c Y + d ≤ count c X)
    (hgapZ : count c Z + d ≤ count c X) :
    thirdPartyDownMass c h3 X Y Z ≤
      thirdPartyUpMass c h3 X Y Z * pairGapLinearBase n d := by
  rw [thirdPartyDownMass_eq c h3 X Y Z (Ne.symm hXZ) hYZ,
    thirdPartyUpMass_eq c h3 X Y Z hXZ (fun h => hYZ h.symm)]
  apply div_le_div_mul_right
  unfold pairGapLinearBase
  have hden0 : (((2 * n + d : ℕ) : ℝ≥0∞)) ≠ 0 := by
    exact_mod_cast (by omega : 2 * n + d ≠ 0)
  have hdenTop : (((2 * n + d : ℕ) : ℝ≥0∞)) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  rw [← mul_div_assoc]
  rw [ENNReal.le_div_iff_mul_le
    (Or.inl hden0) (Or.inl hdenTop)]
  have hXn : count c X ≤ n :=
    Nat.le_of_lt_succ (c.1 X).isLt
  exact_mod_cast (by
    simpa [thirdPartyDownWeight, thirdPartyUpWeight,
      directedFireWeight, mul_comm, mul_left_comm, mul_assoc] using
      thirdPartyWeight_linear_cross
        n d (count c X) (count c Y) (count c Z)
        hXn hgapY hgapZ)

/-- Aggregate strict one-jump odds at the stronger linear base. -/
theorem thirdPartyDownMass_sum_le_up_mul_linearBase
    (c : Config m n) (h3 : 3 ≤ n)
    (X Y : Species m) (hXY : X ≠ Y)
    (d : ℕ) (hgap : HasPairwiseGap c X d) :
    (∑ Z ∈ thirdSpecies X Y,
        thirdPartyDownMass c h3 X Y Z) ≤
      (∑ Z ∈ thirdSpecies X Y,
        thirdPartyUpMass c h3 X Y Z) * pairGapLinearBase n d := by
  calc
    (∑ Z ∈ thirdSpecies X Y,
        thirdPartyDownMass c h3 X Y Z) ≤
      ∑ Z ∈ thirdSpecies X Y,
        thirdPartyUpMass c h3 X Y Z * pairGapLinearBase n d := by
      apply Finset.sum_le_sum
      intro Z hZ
      have hZX : Z ≠ X :=
        (Finset.mem_erase.mp (Finset.mem_erase.mp hZ).2).1
      have hZY : Z ≠ Y := (Finset.mem_erase.mp hZ).1
      exact thirdPartyDownMass_le_upMass_mul_linearBase
        c h3 X Y Z (Ne.symm hZX) (Ne.symm hZY) d
        (hgap Y (Ne.symm hXY)) (hgap Z hZX)
    _ = (∑ Z ∈ thirdSpecies X Y,
        thirdPartyUpMass c h3 X Y Z) * pairGapLinearBase n d := by
      rw [Finset.sum_mul]

/-- The five physical jump masses satisfy the MGF inequality at the linear
base. -/
theorem pairDeltaMass_five_linear_mgf
    (c : Config m n) (h3 : 3 ≤ n)
    (X Y : Species m) (hXY : X ≠ Y)
    (d : ℕ) (hgap : HasPairwiseGap c X d) :
    pairDeltaMass c h3 X Y (-2) +
        pairDeltaMass c h3 X Y (-1) * pairGapLinearBase n d +
        pairDeltaMass c h3 X Y 0 * pairGapLinearBase n d ^ 2 +
        pairDeltaMass c h3 X Y 1 * pairGapLinearBase n d ^ 3 +
        pairDeltaMass c h3 X Y 2 * pairGapLinearBase n d ^ 4 ≤
      pairGapLinearBase n d ^ 2 := by
  apply five_jump_mgf_core
  · exact pairDeltaMass_five_sum c h3 X Y
  · exact pairGapLinearBase_le_one n d (by omega)
  · rw [pairDeltaMass_neg_one_eq_thirdPartyDownMass_sum
        c h3 X Y hXY,
      pairDeltaMass_one_eq_thirdPartyUpMass_sum
        c h3 X Y hXY]
    exact thirdPartyDownMass_sum_le_up_mul_linearBase
      c h3 X Y hXY d hgap
  · rw [pairDeltaMass_neg_two_eq_directedFireMass
        c h3 X Y hXY,
      pairDeltaMass_two_eq_directedFireMass
        c h3 X Y hXY]
    exact reverse_directedFireMass_le_linearBase_sq
      c h3 X Y hXY d (hgap Y (Ne.symm hXY))

/-- Physical one-step pair-gap supermartingale at the linear base. -/
theorem multiStep_pairGapLinearPotential_conserve
    (c : Config m n) (h3 : 3 ≤ n)
    (X Y : Species m) (hXY : X ≠ Y)
    (d : ℕ) (hd2 : 2 ≤ d)
    (hgap : HasPairwiseGap c X d) :
    expect (multiStep c h3)
        (pairGapPotential (pairGapLinearBase n d) X Y) ≤
      pairGapPotential (pairGapLinearBase n d) X Y c := by
  have hXYgap := hgap Y (Ne.symm hXY)
  have hg2 : 2 ≤ pairGapNat c X Y := by
    unfold pairGapNat
    omega
  rw [expect_multiStep_pairGapPotential
    c h3 X Y (pairGapLinearBase n d) hg2]
  unfold pairGapPotential
  exact five_jump_geometric_of_core hg2
    (pairDeltaMass_five_linear_mgf c h3 X Y hXY d hgap)

/-- Productive-event pair-gap supermartingale at the linear base. -/
theorem productiveStep_pairGapLinearPotential_conserve
    (c : Config m n) (h3 : 3 ≤ n)
    (X Y : Species m) (hXY : X ≠ Y)
    (d : ℕ) (hd2 : 2 ≤ d)
    (hgap : HasPairwiseGap c X d) :
    expect (productiveStep h3 c)
        (pairGapPotential (pairGapLinearBase n d) X Y) ≤
      pairGapPotential (pairGapLinearBase n d) X Y c :=
  productiveStep_conserve_of_multiStep_conserve c h3 _
    (ENNReal.pow_ne_top
      (ne_top_of_le_ne_top ENNReal.one_ne_top
        (pairGapLinearBase_le_one n d (by omega)))) <|
      multiStep_pairGapLinearPotential_conserve
        c h3 X Y hXY d hd2 hgap

/-- The existing globally stopped productive kernel also conserves the
stronger linear-base potential. -/
theorem productivePairGapStop_pair_linear_conserve
    (h3 : 3 ≤ n) (X Y : Species m) (hXY : X ≠ Y)
    (d : ℕ) (hd2 : 2 ≤ d)
    (c : Config m n) :
    expect (productivePairGapStop h3 X d c)
        (pairGapPotential (pairGapLinearBase n d) X Y) ≤
      pairGapPotential (pairGapLinearBase n d) X Y c := by
  classical
  unfold productivePairGapStop
  split_ifs with hgap
  · exact productiveStep_pairGapLinearPotential_conserve
      c h3 X Y hXY d hd2 hgap
  · simp only [expect_pure]
    exact le_rfl

/-- Fixed-competitor backsliding mass at the stronger linear base. -/
theorem productivePairGapStop_pair_failure_linear_le
    (h3 : 3 ≤ n) (X Y : Species m) (hXY : X ≠ Y)
    (d : ℕ) (hd2 : 2 ≤ d)
    (T : ℕ) (c0 : Config m n) :
    (∑' c : Config m n,
      if pairGapNat c X Y < d then
        iter (productivePairGapStop h3 X d) T c0 c
      else 0) ≤
      pairGapLinearBase n d ^ pairGapNat c0 X Y /
        pairGapLinearBase n d ^ (d - 1) := by
  let u := pairGapLinearBase n d
  let V : Config m n → ℝ≥0∞ := pairGapPotential u X Y
  let Bad : Config m n → Prop := fun c => pairGapNat c X Y < d
  have hu1 : u ≤ 1 :=
    pairGapLinearBase_le_one n d (by omega)
  have hu0 : u ≠ 0 :=
    pairGapLinearBase_ne_zero n d (by omega)
  have hutop : u ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top hu1
  have htheta0 : u ^ (d - 1) ≠ 0 :=
    pow_ne_zero _ hu0
  have hthetaTop : u ^ (d - 1) ≠ ⊤ :=
    ENNReal.pow_ne_top hutop
  have hstep :
      ∀ c, expect (productivePairGapStop h3 X d c) V ≤ V c := by
    intro c
    exact productivePairGapStop_pair_linear_conserve
      h3 X Y hXY d hd2 c
  have hbad :
      ∀ c, Bad c → u ^ (d - 1) ≤ V c := by
    intro c hc
    unfold Bad at hc
    unfold V pairGapPotential
    apply pow_le_pow_right_of_le_one' hu1
    omega
  simpa only [Bad, V, u, pairGapPotential] using
    stopped_bad_mass_le
      (productivePairGapStop h3 X d) V Bad
      (u ^ (d - 1)) htheta0 hthetaTop
      hstep hbad T c0

/-- Global productive-time no-backsliding at the stronger linear base. -/
theorem productivePairGapStop_global_failure_linear_le
    (h3 : 3 ≤ n) (X : Species m)
    (d : ℕ) (hd2 : 2 ≤ d)
    (T : ℕ) (c0 : Config m n) :
    globalPairGapFailureMass
        (iter (productivePairGapStop h3 X d) T c0) X d ≤
      ∑ Y ∈ Finset.univ.erase X,
        pairGapLinearBase n d ^ pairGapNat c0 X Y /
          pairGapLinearBase n d ^ (d - 1) := by
  calc
    globalPairGapFailureMass
        (iter (productivePairGapStop h3 X d) T c0) X d ≤
      ∑ Y ∈ Finset.univ.erase X,
        ∑' c : Config m n,
          if pairGapNat c X Y < d then
            iter (productivePairGapStop h3 X d) T c0 c
          else 0 :=
      globalPairGapFailureMass_le_pair_sum
        (iter (productivePairGapStop h3 X d) T c0) X d (by omega)
    _ ≤ ∑ Y ∈ Finset.univ.erase X,
        pairGapLinearBase n d ^ pairGapNat c0 X Y /
          pairGapLinearBase n d ^ (d - 1) := by
      apply Finset.sum_le_sum
      intro Y hY
      have hYX : Y ≠ X := (Finset.mem_erase.mp hY).1
      exact productivePairGapStop_pair_failure_linear_le
        h3 X Y (Ne.symm hYX) d hd2 T c0

/-- A buffered initial gap gives one common linear-base failure power. -/
theorem productivePairGapStop_global_failure_linear_le_of_buffer
    (h3 : 3 ≤ n) (X : Species m)
    (d b : ℕ) (hd2 : 2 ≤ d)
    (T : ℕ) (c0 : Config m n)
    (hinit : HasPairwiseGap c0 X (d + b)) :
    globalPairGapFailureMass
        (iter (productivePairGapStop h3 X d) T c0) X d ≤
      (m : ℝ≥0∞) * pairGapLinearBase n d ^ (b + 1) := by
  let u := pairGapLinearBase n d
  have hu1 : u ≤ 1 :=
    pairGapLinearBase_le_one n d (by omega)
  have hu0 : u ≠ 0 :=
    pairGapLinearBase_ne_zero n d (by omega)
  have hutop : u ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top hu1
  have htheta0 : u ^ (d - 1) ≠ 0 :=
    pow_ne_zero _ hu0
  have hthetaTop : u ^ (d - 1) ≠ ⊤ :=
    ENNReal.pow_ne_top hutop
  calc
    globalPairGapFailureMass
        (iter (productivePairGapStop h3 X d) T c0) X d ≤
      ∑ Y ∈ Finset.univ.erase X,
        u ^ pairGapNat c0 X Y / u ^ (d - 1) := by
      simpa only [u] using
        productivePairGapStop_global_failure_linear_le
          h3 X d hd2 T c0
    _ ≤ ∑ Y ∈ Finset.univ.erase X, u ^ (b + 1) := by
      apply Finset.sum_le_sum
      intro Y hY
      have hYX : Y ≠ X := (Finset.mem_erase.mp hY).1
      have hgap := hinit Y hYX
      have hnat : d + b ≤ pairGapNat c0 X Y := by
        unfold pairGapNat
        omega
      have hpow :
          u ^ pairGapNat c0 X Y ≤ u ^ (d + b) :=
        pow_le_pow_right_of_le_one' hu1 hnat
      calc
        u ^ pairGapNat c0 X Y / u ^ (d - 1) ≤
            u ^ (d + b) / u ^ (d - 1) :=
          ENNReal.div_le_div_right hpow _
        _ = u ^ (b + 1) := by
          rw [show d + b = (d - 1) + (b + 1) by omega,
            pow_add, mul_comm, mul_div_assoc,
            ENNReal.div_self htheta0 hthetaTop, mul_one]
    _ = ((Finset.univ.erase X).card : ℝ≥0∞) * u ^ (b + 1) := by
      simp
    _ ≤ (m : ℝ≥0∞) * u ^ (b + 1) := by
      gcongr
      simp

/-- Exact exponential envelope for the linear pair-gap base. -/
theorem pairGapLinearBase_pow_le_exp
    (n d k : ℕ) (hn : 0 < n) :
    pairGapLinearBase n d ^ k ≤
      ENNReal.ofReal
        (Real.exp (-((k : ℝ) * (d : ℝ) /
          (2 * (n : ℝ) + (d : ℝ))))) := by
  unfold pairGapLinearBase
  apply ratio_pow_le_ofReal_exp
  · positivity
  · omega
  · push_cast
    ring_nf
    exact le_rfl

/-- Gaussian-scale global no-backsliding in productive-event time. -/
theorem productivePairGapStop_global_failure_linear_exp
    (h3 : 3 ≤ n) (X : Species m)
    (d b : ℕ) (hd2 : 2 ≤ d)
    (T : ℕ) (c0 : Config m n)
    (hinit : HasPairwiseGap c0 X (d + b)) :
    globalPairGapFailureMass
        (iter (productivePairGapStop h3 X d) T c0) X d ≤
      (m : ℝ≥0∞) *
        ENNReal.ofReal
          (Real.exp (-(((b + 1 : ℕ) : ℝ) * (d : ℝ) /
            (2 * (n : ℝ) + (d : ℝ))))) := by
  calc
    globalPairGapFailureMass
        (iter (productivePairGapStop h3 X d) T c0) X d ≤
      (m : ℝ≥0∞) * pairGapLinearBase n d ^ (b + 1) :=
        productivePairGapStop_global_failure_linear_le_of_buffer
          h3 X d b hd2 T c0 hinit
    _ ≤ (m : ℝ≥0∞) *
        ENNReal.ofReal
          (Real.exp (-(((b + 1 : ℕ) : ℝ) * (d : ℝ) /
            (2 * (n : ℝ) + (d : ℝ))))) :=
      mul_le_mul_right
        (pairGapLinearBase_pow_le_exp n d (b + 1) (by omega)) _

/-- Paper-shaped no-backsliding: from global gap `D`, failure of the protected
half-gap has an exact quadratic-scale exponential bound. -/
theorem productivePairGapStop_half_failure_exp
    (h3 : 3 ≤ n) (X : Species m)
    (D : ℕ) (hD4 : 4 ≤ D) (hDn : D ≤ n)
    (T : ℕ) (c0 : Config m n)
    (hinit : HasPairwiseGap c0 X D) :
    globalPairGapFailureMass
        (iter (productivePairGapStop h3 X (D / 2)) T c0) X (D / 2) ≤
      (m : ℝ≥0∞) *
        ENNReal.ofReal
          (Real.exp (-((D : ℝ) ^ 2 / (18 * (n : ℝ))))) := by
  let d := D / 2
  let b := D - d
  have hd2 : 2 ≤ d := by
    dsimp only [d]
    omega
  have hdb : d + b = D := by
    dsimp only [d, b]
    omega
  have hbase :=
    productivePairGapStop_global_failure_linear_exp
      h3 X d b hd2 T c0 (by simpa [hdb] using hinit)
  have hdNat : D ≤ 3 * d := by
    dsimp only [d]
    omega
  have hbNat : D ≤ 2 * (b + 1) := by
    dsimp only [b, d]
    omega
  have hdenNat : 2 * n + d ≤ 3 * n := by
    dsimp only [d]
    omega
  have hnumNat : D ^ 2 ≤ 6 * (b + 1) * d := by
    have hmul := Nat.mul_le_mul hbNat hdNat
    calc
      D ^ 2 = D * D := by ring
      _ ≤ 2 * (b + 1) * (3 * d) := hmul
      _ = 6 * (b + 1) * d := by ring
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hdenR : (2 : ℝ) * n + d ≤ 3 * n := by
    exact_mod_cast hdenNat
  have hnumR :
      (D : ℝ) ^ 2 ≤ 6 * (b + 1 : ℕ) * d := by
    exact_mod_cast hnumNat
  have hscalar :
      (D : ℝ) ^ 2 / (18 * (n : ℝ)) ≤
        ((b + 1 : ℕ) : ℝ) * (d : ℝ) /
          (2 * (n : ℝ) + (d : ℝ)) := by
    calc
      (D : ℝ) ^ 2 / (18 * (n : ℝ)) ≤
          (6 * ((b + 1 : ℕ) : ℝ) * (d : ℝ)) /
            (18 * (n : ℝ)) := by
        gcongr
      _ = ((b + 1 : ℕ) : ℝ) * (d : ℝ) /
            (3 * (n : ℝ)) := by
        field_simp
        ring
      _ ≤ ((b + 1 : ℕ) : ℝ) * (d : ℝ) /
            (2 * (n : ℝ) + (d : ℝ)) := by
        apply div_le_div_of_nonneg_left
        · positivity
        · positivity
        · exact hdenR
  exact hbase.trans <| by
    gcongr

/-- Probability mass of ever leaving the protected global pairwise-gap region,
expressed as the supremum of its finite stopped-chain failure masses. -/
noncomputable def productivePairGapEverFailure
    (h3 : 3 ≤ n) (X : Species m) (d : ℕ)
    (c0 : Config m n) : ℝ≥0∞ :=
  ⨆ T : ℕ,
    globalPairGapFailureMass
      (iter (productivePairGapStop h3 X d) T c0) X d

/-- Unbounded-horizon form of the productive-time half-gap estimate.  The
finite-horizon bound is uniform in `T`, so taking the supremum costs no
additional error. -/
theorem productivePairGapEver_half_failure_exp
    (h3 : 3 ≤ n) (X : Species m)
    (D : ℕ) (hD4 : 4 ≤ D) (hDn : D ≤ n)
    (c0 : Config m n)
    (hinit : HasPairwiseGap c0 X D) :
    productivePairGapEverFailure h3 X (D / 2) c0 ≤
      (m : ℝ≥0∞) *
        ENNReal.ofReal
          (Real.exp (-((D : ℝ) ^ 2 / (18 * (n : ℝ))))) := by
  unfold productivePairGapEverFailure
  exact iSup_le fun T =>
    productivePairGapStop_half_failure_exp
      h3 X D hD4 hDn T c0 hinit

end Tri.Multi

#print axioms Tri.Multi.directWeight_linear_square_cross
#print axioms Tri.Multi.gap_mul_count_le_thirdParty_gap_product
#print axioms Tri.Multi.thirdPartyWeight_linear_cross
#print axioms Tri.Multi.reverse_directedFireMass_le_linearBase_sq
#print axioms Tri.Multi.thirdPartyDownMass_le_upMass_mul_linearBase
#print axioms Tri.Multi.pairDeltaMass_five_linear_mgf
#print axioms Tri.Multi.productiveStep_pairGapLinearPotential_conserve
#print axioms Tri.Multi.productivePairGapStop_pair_failure_linear_le
#print axioms Tri.Multi.productivePairGapStop_global_failure_linear_le_of_buffer
#print axioms Tri.Multi.productivePairGapStop_global_failure_linear_exp
#print axioms Tri.Multi.productivePairGapStop_half_failure_exp
#print axioms Tri.Multi.productivePairGapEver_half_failure_exp
