-- Ripple/Kurtz/StrongApprox/DyadicChainEstimate.lean
import Mathlib

/-!
# Deterministic estimates along one dyadic ancestor chain

This file has no dependency on the Gaussian or Poisson tree implementation.
A later adapter supplies the sequences and the K12 one-step identities.
-/

noncomputable section

open Real Finset
open scoped BigOperators

namespace Ripple.Kurtz.StrongApprox.DyadicChainEstimate

/-! ## Numerical constants -/

def inverseSqrtTwo : ℝ := 1 / Real.sqrt 2

def profileRatio : ℝ := 3 / 4

private theorem sqrtTwo_pos : 0 < Real.sqrt (2 : ℝ) :=
  Real.sqrt_pos.2 (by norm_num)

private theorem inverseSqrtTwo_nonneg : 0 ≤ inverseSqrtTwo := by
  unfold inverseSqrtTwo
  positivity

private theorem profileRatio_nonneg : 0 ≤ profileRatio := by
  norm_num [profileRatio]

private theorem profileRatio_le_one : profileRatio ≤ 1 := by
  norm_num [profileRatio]

private theorem inverseSqrtTwo_le_profileRatio :
    inverseSqrtTwo ≤ profileRatio := by
  have hs0 : 0 ≤ Real.sqrt (2 : ℝ) := Real.sqrt_nonneg _
  have hs2 : (Real.sqrt (2 : ℝ)) ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  have hfour : (4 : ℝ) ≤ 3 * Real.sqrt 2 := by
    by_contra h
    have hlt : 3 * Real.sqrt 2 < 4 := lt_of_not_ge h
    have hsq : (3 * Real.sqrt 2) ^ 2 < (4 : ℝ) ^ 2 :=
      (sq_lt_sq₀ (mul_nonneg (by norm_num) hs0) (by norm_num)).2 hlt
    nlinarith
  unfold inverseSqrtTwo profileRatio
  apply (div_le_iff₀ sqrtTwo_pos).2
  nlinarith

private theorem inverseSqrtTwo_le_one : inverseSqrtTwo ≤ 1 :=
  inverseSqrtTwo_le_profileRatio.trans profileRatio_le_one

/-! ## K14: the standardized Gaussian ancestor chain -/

structure GaussianAncestorChain (K : ℕ) where
  root : ℝ
  split : ℕ → ℝ
  standardized : ℕ → ℝ
  direction : ℕ → ℝ
  standardized_zero : standardized 0 = root
  direction_pm : ∀ j, j < K → direction j = 1 ∨ direction j = -1
  standardized_succ : ∀ j, j < K →
    standardized (j + 1) =
      (standardized j + direction j * split j) / Real.sqrt 2

/-- Quadratic noise used by K15 and K18. -/
def quadraticNoise {K : ℕ} (C : GaussianAncestorChain K) : ℝ :=
  C.root ^ 2 + ∑ j ∈ Finset.range K, C.split j ^ 2

private theorem standardized_step_sq
    {K : ℕ} (C : GaussianAncestorChain K) (j : ℕ) (hj : j < K) :
    C.standardized (j + 1) ^ 2 ≤
      (3 / 4 : ℝ) * C.standardized j ^ 2 +
        (3 / 2 : ℝ) * C.split j ^ 2 := by
  have hs2 : (Real.sqrt (2 : ℝ)) ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  rcases C.direction_pm j hj with hs | hs
  · rw [C.standardized_succ j hj, hs]
    simp only [one_mul]
    rw [div_pow, hs2]
    nlinarith [sq_nonneg (C.standardized j - 2 * C.split j)]
  · rw [C.standardized_succ j hj, hs]
    simp only [neg_mul, one_mul]
    rw [div_pow, hs2]
    nlinarith [sq_nonneg (C.standardized j + 2 * C.split j)]

/-- A Lyapunov form of K14.  The extra endpoint term makes the induction
one-line and gives constant `6` after it is discarded. -/
theorem standardized_energy_invariant
    {K : ℕ} (C : GaussianAncestorChain K) :
    ∀ n, n ≤ K →
      (∑ j ∈ Finset.range n, C.standardized j ^ 2) +
          4 * C.standardized n ^ 2 ≤
        4 * C.root ^ 2 +
          6 * ∑ j ∈ Finset.range n, C.split j ^ 2 := by
  intro n
  induction n with
  | zero =>
      intro _
      simp [C.standardized_zero]
  | succ n ih =>
      intro hn
      have hnK : n < K := by omega
      have hprev := ih (by omega)
      have hstep := standardized_step_sq C n hnK
      simp only [Finset.sum_range_succ]
      nlinarith

/-- Stronger form of the requested K14 square estimate. -/
theorem standardized_energy_le_six
    {K : ℕ} (C : GaussianAncestorChain K) :
    ∑ j ∈ Finset.range K, C.standardized j ^ 2 ≤
      6 * quadraticNoise C := by
  have h := standardized_energy_invariant C K le_rfl
  have hend : 0 ≤ 4 * C.standardized K ^ 2 := by positivity
  unfold quadraticNoise
  nlinarith

/-- The literal requested constant. -/
theorem standardized_energy_le_twelve
    {K : ℕ} (C : GaussianAncestorChain K) :
    ∑ j ∈ Finset.range K, C.standardized j ^ 2 ≤
      12 * quadraticNoise C := by
  have h := standardized_energy_le_six C
  have hq : 0 ≤ quadraticNoise C := by
    unfold quadraticNoise
    positivity
  nlinarith

private theorem standardized_abs_step
    {K : ℕ} (C : GaussianAncestorChain K) (j : ℕ) (hj : j < K) :
    |C.standardized (j + 1)| ≤
      inverseSqrtTwo * (|C.standardized j| + |C.split j|) := by
  have hsabs : |C.direction j| = 1 := by
    rcases C.direction_pm j hj with hs | hs <;> simp [hs]
  rw [C.standardized_succ j hj, abs_div, abs_of_pos sqrtTwo_pos]
  calc
    |C.standardized j + C.direction j * C.split j| / Real.sqrt 2
        ≤ (|C.standardized j| + |C.direction j * C.split j|) /
            Real.sqrt 2 := by
          gcongr
          exact abs_add_le _ _
    _ = inverseSqrtTwo * (|C.standardized j| + |C.split j|) := by
      rw [abs_mul, hsabs, one_mul]
      simp [inverseSqrtTwo, div_eq_mul_inv, mul_comm]

/-- Explicit absolute-value unrolling of the standardized recursion. -/
def ancestorHistory {K : ℕ} (C : GaussianAncestorChain K) (j : ℕ) : ℝ :=
  inverseSqrtTwo ^ j * |C.root| +
    ∑ b ∈ Finset.range j,
      inverseSqrtTwo ^ (j - b) * |C.split b|

private theorem ancestorHistory_succ
    {K : ℕ} (C : GaussianAncestorChain K) (j : ℕ) :
    inverseSqrtTwo * (ancestorHistory C j + |C.split j|) =
      ancestorHistory C (j + 1) := by
  have hsum :
      inverseSqrtTwo *
          (∑ b ∈ Finset.range j,
            inverseSqrtTwo ^ (j - b) * |C.split b|) =
        ∑ b ∈ Finset.range j,
          inverseSqrtTwo ^ ((j + 1) - b) * |C.split b| := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    have hb' : b < j := Finset.mem_range.mp hb
    rw [show (j + 1) - b = (j - b) + 1 by omega, pow_succ]
    ring
  unfold ancestorHistory
  rw [Finset.sum_range_succ, pow_succ, ← hsum]
  simp only [Nat.add_sub_cancel_left, pow_one]
  ring

/-- Pointwise convolution estimate for `Z'_j`. -/
theorem standardized_abs_le_history
    {K : ℕ} (C : GaussianAncestorChain K) :
    ∀ j, j ≤ K → |C.standardized j| ≤ ancestorHistory C j := by
  intro j
  induction j with
  | zero =>
      intro _
      simp [ancestorHistory, C.standardized_zero]
  | succ j ih =>
      intro hj
      have hjK : j < K := by omega
      calc
        |C.standardized (j + 1)| ≤
            inverseSqrtTwo * (|C.standardized j| + |C.split j|) :=
          standardized_abs_step C j hjK
        _ ≤ inverseSqrtTwo * (ancestorHistory C j + |C.split j|) := by
          have := ih (by omega)
          exact mul_le_mul_of_nonneg_left (by linarith) inverseSqrtTwo_nonneg
        _ = ancestorHistory C (j + 1) := ancestorHistory_succ C j

/-! ## Explicit convolution weights -/

/-- Coefficient of the root normal in a weighted sum of `|Z'_j|`. -/
def rootConvolution (K : ℕ) (w : ℕ → ℝ) : ℝ :=
  ∑ j ∈ Finset.range K, w j * inverseSqrtTwo ^ j

/-- Coefficient of split normal `Z_b`. -/
def splitConvolution (K : ℕ) (w : ℕ → ℝ) (b : ℕ) : ℝ :=
  ∑ j ∈ Finset.range K,
    if b < j then w j * inverseSqrtTwo ^ (j - b) else 0

/-- Root plus split convolution, in scalar notation. -/
def weightedNoise
    (K : ℕ) (w : ℕ → ℝ) (root : ℝ) (z : ℕ → ℝ) : ℝ :=
  rootConvolution K w * |root| +
    ∑ b ∈ Finset.range K, splitConvolution K w b * |z b|

/-- The same coefficients as a single `Fin (K+1)` vector. -/
def convolutionWeight (K : ℕ) (w : ℕ → ℝ) : Fin (K + 1) → ℝ :=
  Fin.cases (rootConvolution K w)
    (fun b : Fin K => splitConvolution K w b.val)

/-- The augmented normal vector `(Z_*, Z_0, ..., Z_{K-1})`. -/
def augmentedNoise (K : ℕ) (root : ℝ) (z : ℕ → ℝ) : Fin (K + 1) → ℝ :=
  Fin.cases root (fun b : Fin K => z b.val)

private theorem sum_range_indicator_lt
    {A : Type*} [AddCommMonoid A]
    (K j : ℕ) (hj : j ≤ K) (f : ℕ → A) :
    (∑ b ∈ Finset.range K, if b < j then f b else 0) =
      ∑ b ∈ Finset.range j, f b := by
  classical
  have hfilter :
      (Finset.range K).filter (fun b => b < j) = Finset.range j := by
    ext b
    simp
    omega
  rw [← Finset.sum_filter, hfilter]

private theorem triangular_convolution_identity
    (K : ℕ) (w z : ℕ → ℝ) :
    (∑ j ∈ Finset.range K,
      w j *
        (∑ b ∈ Finset.range j,
          inverseSqrtTwo ^ (j - b) * |z b|)) =
      ∑ b ∈ Finset.range K, splitConvolution K w b * |z b| := by
  classical
  calc
    (∑ j ∈ Finset.range K,
      w j *
        (∑ b ∈ Finset.range j,
          inverseSqrtTwo ^ (j - b) * |z b|)) =
        ∑ j ∈ Finset.range K,
          ∑ b ∈ Finset.range K,
            if b < j then
              w j * inverseSqrtTwo ^ (j - b) * |z b|
            else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjK : j ≤ K := (Finset.mem_range.mp hj).le
      rw [Finset.mul_sum]
      have h := sum_range_indicator_lt K j hjK
        (fun b => w j * inverseSqrtTwo ^ (j - b) * |z b|)
      simpa only [mul_assoc] using h.symm
    _ = ∑ b ∈ Finset.range K,
          ∑ j ∈ Finset.range K,
            if b < j then
              w j * inverseSqrtTwo ^ (j - b) * |z b|
            else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ b ∈ Finset.range K, splitConvolution K w b * |z b| := by
      apply Finset.sum_congr rfl
      intro b _
      unfold splitConvolution
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      split_ifs <;> ring

private theorem weighted_history_identity
    {K : ℕ} (C : GaussianAncestorChain K) (w : ℕ → ℝ) :
    (∑ j ∈ Finset.range K, w j * ancestorHistory C j) =
      weightedNoise K w C.root C.split := by
  unfold ancestorHistory weightedNoise rootConvolution
  simp only [mul_add]
  rw [Finset.sum_add_distrib]
  have hroot :
      (∑ j ∈ Finset.range K,
        w j * (inverseSqrtTwo ^ j * |C.root|)) =
        (∑ j ∈ Finset.range K, w j * inverseSqrtTwo ^ j) * |C.root| := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hroot, triangular_convolution_identity K w C.split]

/-- K14 weighted convolution estimate. -/
theorem weighted_standardized_abs_le
    {K : ℕ} (C : GaussianAncestorChain K)
    (w : ℕ → ℝ) (hw : ∀ j, j < K → 0 ≤ w j) :
    (∑ j ∈ Finset.range K, w j * |C.standardized j|) ≤
      weightedNoise K w C.root C.split := by
  calc
    (∑ j ∈ Finset.range K, w j * |C.standardized j|) ≤
        ∑ j ∈ Finset.range K, w j * ancestorHistory C j := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left
        (standardized_abs_le_history C j (Finset.mem_range.mp hj).le)
        (hw j (Finset.mem_range.mp hj))
    _ = weightedNoise K w C.root C.split :=
      weighted_history_identity C w

/-- Vector form of the weighted K14 estimate. -/
theorem weighted_standardized_abs_le_fin
    {K : ℕ} (C : GaussianAncestorChain K)
    (w : ℕ → ℝ) (hw : ∀ j, j < K → 0 ≤ w j) :
    (∑ j ∈ Finset.range K, w j * |C.standardized j|) ≤
      ∑ i : Fin (K + 1),
        convolutionWeight K w i * |augmentedNoise K C.root C.split i| := by
  rw [Fin.sum_univ_succ]
  have h2 : ∑ i : Fin K, convolutionWeight K w i.succ *
        |augmentedNoise K C.root C.split i.succ| =
      ∑ b ∈ Finset.range K, splitConvolution K w b * |C.split b| := by
    simp only [convolutionWeight, augmentedNoise, Fin.cases_succ]
    exact Fin.sum_univ_eq_sum_range
      (fun b => splitConvolution K w b * |C.split b|) K
  rw [h2]
  simpa [convolutionWeight, augmentedNoise, weightedNoise] using
    weighted_standardized_abs_le C w hw

/-! ## Coefficient mass estimates -/

private theorem rootConvolution_nonneg
    (K : ℕ) (w : ℕ → ℝ) (hw : ∀ j, j < K → 0 ≤ w j) :
    0 ≤ rootConvolution K w := by
  unfold rootConvolution
  exact Finset.sum_nonneg fun j hj =>
    mul_nonneg (hw j (Finset.mem_range.mp hj))
      (pow_nonneg inverseSqrtTwo_nonneg _)

private theorem splitConvolution_nonneg
    (K : ℕ) (w : ℕ → ℝ) (hw : ∀ j, j < K → 0 ≤ w j)
    (b : ℕ) :
    0 ≤ splitConvolution K w b := by
  unfold splitConvolution
  apply Finset.sum_nonneg
  intro j hj
  split_ifs
  · exact mul_nonneg (hw j (Finset.mem_range.mp hj))
      (pow_nonneg inverseSqrtTwo_nonneg _)
  · exact le_rfl

private theorem rootConvolution_le_sum
    (K : ℕ) (w : ℕ → ℝ) (hw : ∀ j, j < K → 0 ≤ w j) :
    rootConvolution K w ≤ ∑ j ∈ Finset.range K, w j := by
  unfold rootConvolution
  apply Finset.sum_le_sum
  intro j hj
  have hp : inverseSqrtTwo ^ j ≤ 1 :=
    pow_le_one₀ inverseSqrtTwo_nonneg inverseSqrtTwo_le_one
  nlinarith [hw j (Finset.mem_range.mp hj)]

private theorem splitConvolution_le_sum
    (K : ℕ) (w : ℕ → ℝ) (hw : ∀ j, j < K → 0 ≤ w j)
    (b : ℕ) :
    splitConvolution K w b ≤ ∑ j ∈ Finset.range K, w j := by
  unfold splitConvolution
  apply Finset.sum_le_sum
  intro j hj
  split_ifs
  · have hp : inverseSqrtTwo ^ (j - b) ≤ 1 :=
      pow_le_one₀ inverseSqrtTwo_nonneg inverseSqrtTwo_le_one
    nlinarith [hw j (Finset.mem_range.mp hj)]
  · exact (hw j (Finset.mem_range.mp hj))

private def backwardDecay (j : ℕ) : ℝ :=
  ∑ b ∈ Finset.range j, inverseSqrtTwo ^ (j - b)

private theorem backwardDecay_succ (j : ℕ) :
    backwardDecay (j + 1) =
      inverseSqrtTwo * backwardDecay j + inverseSqrtTwo := by
  have hsum :
      (∑ b ∈ Finset.range j,
        inverseSqrtTwo ^ ((j + 1) - b)) =
        inverseSqrtTwo *
          ∑ b ∈ Finset.range j, inverseSqrtTwo ^ (j - b) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    have hb' : b < j := Finset.mem_range.mp hb
    rw [show (j + 1) - b = (j - b) + 1 by omega, pow_succ]
    ring
  unfold backwardDecay
  rw [Finset.sum_range_succ, hsum]
  simp

private theorem backwardDecay_le_three (j : ℕ) : backwardDecay j ≤ 3 := by
  induction j with
  | zero => simp [backwardDecay]
  | succ j ih =>
      rw [backwardDecay_succ]
      have hmul := mul_le_mul_of_nonneg_left ih inverseSqrtTwo_nonneg
      have hpr := inverseSqrtTwo_le_profileRatio
      unfold profileRatio at hpr
      linarith

private theorem sum_splitConvolution_le_three
    (K : ℕ) (w : ℕ → ℝ) (hw : ∀ j, j < K → 0 ≤ w j) :
    (∑ b ∈ Finset.range K, splitConvolution K w b) ≤
      3 * ∑ j ∈ Finset.range K, w j := by
  classical
  calc
    (∑ b ∈ Finset.range K, splitConvolution K w b) =
        ∑ j ∈ Finset.range K, w j * backwardDecay j := by
      unfold splitConvolution
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      have hjK : j ≤ K := (Finset.mem_range.mp hj).le
      have hind := sum_range_indicator_lt K j hjK
        (fun b => inverseSqrtTwo ^ (j - b))
      unfold backwardDecay
      rw [← hind]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      split_ifs <;> ring
    _ ≤ ∑ j ∈ Finset.range K, w j * 3 := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left (backwardDecay_le_three j)
        (hw j (Finset.mem_range.mp hj))
    _ = 3 * ∑ j ∈ Finset.range K, w j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring

/-- Sum of all augmented coefficients. -/
def convolutionMass (K : ℕ) (w : ℕ → ℝ) : ℝ :=
  rootConvolution K w +
    ∑ b ∈ Finset.range K, splitConvolution K w b

/-- Sum of squares of all augmented coefficients. -/
def convolutionSquareMass (K : ℕ) (w : ℕ → ℝ) : ℝ :=
  (rootConvolution K w) ^ 2 +
    ∑ b ∈ Finset.range K, (splitConvolution K w b) ^ 2

theorem convolutionMass_le
    (K : ℕ) (w : ℕ → ℝ) (hw : ∀ j, j < K → 0 ≤ w j) :
    convolutionMass K w ≤ 4 * ∑ j ∈ Finset.range K, w j := by
  unfold convolutionMass
  have hr := rootConvolution_le_sum K w hw
  have hs := sum_splitConvolution_le_three K w hw
  linarith

theorem convolutionSquareMass_le
    (K : ℕ) (w : ℕ → ℝ)
    (hw : ∀ j, j < K → 0 ≤ w j)
    (hsum : (∑ j ∈ Finset.range K, w j) ≤ 4) :
    convolutionSquareMass K w ≤ 64 := by
  have hr0 := rootConvolution_nonneg K w hw
  have hr4 := (rootConvolution_le_sum K w hw).trans hsum
  have hrsq : (rootConvolution K w) ^ 2 ≤
      4 * rootConvolution K w := by nlinarith
  have hssq :
      (∑ b ∈ Finset.range K, (splitConvolution K w b) ^ 2) ≤
        4 * ∑ b ∈ Finset.range K, splitConvolution K w b := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro b _
    have hb0 := splitConvolution_nonneg K w hw b
    have hb4 := (splitConvolution_le_sum K w hw b).trans hsum
    nlinarith
  have hmass := convolutionMass_le K w hw
  unfold convolutionSquareMass convolutionMass at *
  nlinarith

theorem sum_convolutionWeight
    (K : ℕ) (w : ℕ → ℝ) :
    (∑ i : Fin (K + 1), convolutionWeight K w i) =
      convolutionMass K w := by
  rw [Fin.sum_univ_succ]
  have h2 : ∑ i : Fin K, convolutionWeight K w i.succ =
      ∑ b ∈ Finset.range K, splitConvolution K w b := by
    simp only [convolutionWeight, Fin.cases_succ]
    exact Fin.sum_univ_eq_sum_range (fun b => splitConvolution K w b) K
  rw [h2]
  rfl

theorem sum_sq_convolutionWeight
    (K : ℕ) (w : ℕ → ℝ) :
    (∑ i : Fin (K + 1), (convolutionWeight K w i) ^ 2) =
      convolutionSquareMass K w := by
  rw [Fin.sum_univ_succ]
  have h2 : ∑ i : Fin K, (convolutionWeight K w i.succ) ^ 2 =
      ∑ b ∈ Finset.range K, (splitConvolution K w b) ^ 2 := by
    simp only [convolutionWeight, Fin.cases_succ]
    exact Fin.sum_univ_eq_sum_range (fun b => (splitConvolution K w b) ^ 2) K
  rw [h2]
  rfl

/-! ## Dyadic coarse/fine cut and the K15 weights -/

/-- Level `j` has length `2^(K-j)`.  Only `j < K` is used by the bridge. -/
def dyadicLength (K j : ℕ) : ℝ := (2 : ℝ) ^ (K - j)

private theorem dyadicLength_pos (K j : ℕ) : 0 < dyadicLength K j := by
  unfold dyadicLength
  positivity

private theorem dyadicLength_succ_horizon (K j : ℕ) :
    dyadicLength (K + 1) (j + 1) = dyadicLength K j := by
  simp [dyadicLength]

private theorem dyadicLength_le_root (K j : ℕ) :
    dyadicLength K j ≤ dyadicLength K 0 := by
  unfold dyadicLength
  apply pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
  exact Nat.sub_le K j

private theorem dyadicLength_succ
    (K j : ℕ) (hj : j < K) :
    dyadicLength K (j + 1) = dyadicLength K j / 2 := by
  unfold dyadicLength
  rw [show K - j = (K - (j + 1)) + 1 by omega, pow_succ]
  ring

/-- First fine level.  If no level `j < K` is fine, this is `K`; if the root
is fine, this is zero. -/
def dyadicFineStart : ℕ → ℝ → ℕ
  | 0, _ => 0
  | K + 1, L =>
      if dyadicLength (K + 1) 0 < L then 0
      else dyadicFineStart K L + 1

private theorem dyadicFineStart_le (K : ℕ) (L : ℝ) :
    dyadicFineStart K L ≤ K := by
  induction K with
  | zero => simp [dyadicFineStart]
  | succ K ih =>
      simp only [dyadicFineStart]
      split_ifs
      · omega
      · omega

private theorem coarse_before_fineStart :
    ∀ K L j, j < K → j < dyadicFineStart K L →
      L ≤ dyadicLength K j
  | 0, _L, j, hj, _ => by omega
  | K + 1, L, j, hj, hbefore => by
      by_cases hroot : dyadicLength (K + 1) 0 < L
      · simp [dyadicFineStart, hroot] at hbefore
      · rw [dyadicFineStart, if_neg hroot] at hbefore
        cases j with
        | zero => exact le_of_not_gt hroot
        | succ j =>
            have hjK : j < K := by omega
            have hjBefore : j < dyadicFineStart K L := by omega
            simpa only [dyadicLength_succ_horizon] using
              coarse_before_fineStart K L j hjK hjBefore

private theorem fine_after_fineStart :
    ∀ K L j, j < K → dyadicFineStart K L ≤ j →
      dyadicLength K j < L
  | 0, _L, j, hj, _ => by omega
  | K + 1, L, j, hj, hafter => by
      by_cases hroot : dyadicLength (K + 1) 0 < L
      · cases j with
        | zero => exact hroot
        | succ j =>
            exact (dyadicLength_le_root (K + 1) (j + 1)).trans_lt hroot
      · rw [dyadicFineStart, if_neg hroot] at hafter
        cases j with
        | zero => omega
        | succ j =>
            have hjK : j < K := by omega
            have hjAfter : dyadicFineStart K L ≤ j := by omega
            simpa only [dyadicLength_succ_horizon] using
              fine_after_fineStart K L j hjK hjAfter

private theorem sqrt_dyadicLength_succ_le
    (K j : ℕ) (hj : j < K) :
    Real.sqrt (dyadicLength K (j + 1)) ≤
      profileRatio * Real.sqrt (dyadicLength K j) := by
  rw [dyadicLength_succ K j hj,
    Real.sqrt_div (le_of_lt (dyadicLength_pos K j))]
  calc
    Real.sqrt (dyadicLength K j) / Real.sqrt 2 =
        inverseSqrtTwo * Real.sqrt (dyadicLength K j) := by
      simp [inverseSqrtTwo, div_eq_mul_inv, mul_comm]
    _ ≤ profileRatio * Real.sqrt (dyadicLength K j) :=
      mul_le_mul_of_nonneg_right inverseSqrtTwo_le_profileRatio
        (Real.sqrt_nonneg _)

private theorem sqrt_dyadicLength_pair_le
    (K i j : ℕ) (hij : i ≤ j) (hjK : j ≤ K) :
    Real.sqrt (dyadicLength K j) ≤
      Real.sqrt (dyadicLength K i) * profileRatio ^ (j - i) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
  revert hjK
  clear hij
  induction d with
  | zero =>
      intro _
      simp
  | succ d ih =>
      intro hK
      have hprevK : i + d ≤ K := by omega
      have hstep := sqrt_dyadicLength_succ_le K (i + d) (by omega)
      have hprev := ih hprevK
      rw [Nat.add_sub_cancel_left] at hprev
      calc
        Real.sqrt (dyadicLength K (i + (d + 1))) =
            Real.sqrt (dyadicLength K ((i + d) + 1)) := by congr 2 <;> omega
        _ ≤ profileRatio * Real.sqrt (dyadicLength K (i + d)) := hstep
        _ ≤ profileRatio *
            (Real.sqrt (dyadicLength K i) * profileRatio ^ d) := by
          exact mul_le_mul_of_nonneg_left hprev profileRatio_nonneg
        _ = Real.sqrt (dyadicLength K i) *
            profileRatio ^ ((i + (d + 1)) - i) := by
          rw [show (i + (d + 1)) - i = d + 1 by omega, pow_succ]
          ring

/-- Geometric profile which dominates normalized square-root lengths after
the first fine level. -/
def suffixProfile (J j : ℕ) : ℝ :=
  if J ≤ j then profileRatio ^ (j - J) else 0

private theorem suffixProfile_nonneg (J j : ℕ) : 0 ≤ suffixProfile J j := by
  unfold suffixProfile
  split_ifs
  · exact pow_nonneg profileRatio_nonneg _
  · exact le_rfl

private theorem profile_geom_sum (N : ℕ) :
    (∑ d ∈ Finset.range N, profileRatio ^ d) =
      4 * (1 - profileRatio ^ N) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      unfold profileRatio
      ring

private theorem profile_geom_sum_le_four (N : ℕ) :
    (∑ d ∈ Finset.range N, profileRatio ^ d) ≤ 4 := by
  rw [profile_geom_sum]
  have hp : 0 ≤ profileRatio ^ N := pow_nonneg profileRatio_nonneg _
  nlinarith

private theorem suffixProfile_sum_eq_geom
    (J K : ℕ) (hJK : J ≤ K) :
    (∑ j ∈ Finset.range K, suffixProfile J j) =
      ∑ d ∈ Finset.range (K - J), profileRatio ^ d := by
  induction K generalizing J with
  | zero =>
      have hJ : J = 0 := by omega
      subst J
      simp [suffixProfile]
  | succ K ih =>
      by_cases hJ : J ≤ K
      · rw [Finset.sum_range_succ, ih J hJ]
        have hsub : K + 1 - J = (K - J) + 1 := by omega
        rw [hsub, Finset.sum_range_succ]
        simp [suffixProfile, hJ]
      · have hEq : J = K + 1 := by omega
        subst J
        rw [Nat.sub_self, Finset.sum_range_zero]
        apply Finset.sum_eq_zero
        intro x hx
        have := Finset.mem_range.mp hx
        unfold suffixProfile
        rw [if_neg (by omega)]

/-- Actual profile used by K15. -/
def fineProfile (K : ℕ) (L : ℝ) (j : ℕ) : ℝ :=
  suffixProfile (dyadicFineStart K L) j

private theorem fineProfile_nonneg (K : ℕ) (L : ℝ) (j : ℕ) :
    0 ≤ fineProfile K L j :=
  suffixProfile_nonneg _ _

private theorem fineProfile_sum_le_four (K : ℕ) (L : ℝ) :
    (∑ j ∈ Finset.range K, fineProfile K L j) ≤ 4 := by
  unfold fineProfile
  rw [suffixProfile_sum_eq_geom _ _ (dyadicFineStart_le K L)]
  exact profile_geom_sum_le_four _

private theorem fine_length_profile_bound
    (K : ℕ) {L : ℝ} (hL : 0 ≤ L)
    (j : ℕ) (hj : j < K)
    (hfine : dyadicLength K j < L) :
    Real.sqrt (dyadicLength K j) ≤
      Real.sqrt L * fineProfile K L j := by
  have hstart : dyadicFineStart K L ≤ j := by
    by_contra h
    have hbefore : j < dyadicFineStart K L := by omega
    exact (not_lt_of_ge
      (coarse_before_fineStart K L j hj hbefore)) hfine
  have hstartK : dyadicFineStart K L < K := by omega
  have hfirst := fine_after_fineStart K L
    (dyadicFineStart K L) hstartK le_rfl
  have hpair := sqrt_dyadicLength_pair_le K
    (dyadicFineStart K L) j hstart hj.le
  have hsqrt :
      Real.sqrt (dyadicLength K (dyadicFineStart K L)) ≤ Real.sqrt L :=
    Real.sqrt_le_sqrt hfirst.le
  unfold fineProfile suffixProfile
  rw [if_pos hstart]
  exact hpair.trans
    (mul_le_mul_of_nonneg_right hsqrt
      (pow_nonneg profileRatio_nonneg _))

/-- K15 coefficient vector. -/
def kmtWeight (K : ℕ) (L : ℝ) : Fin (K + 1) → ℝ :=
  convolutionWeight K (fineProfile K L)

/-- Weighted augmented normal term consumed by K18. -/
def kmtLinearTerm
    {K : ℕ} (C : GaussianAncestorChain K) (L : ℝ) : ℝ :=
  ∑ i : Fin (K + 1), kmtWeight K L i *
    |augmentedNoise K C.root C.split i|

private theorem kmtWeight_nonneg
    (K : ℕ) (L : ℝ) (i : Fin (K + 1)) :
    0 ≤ kmtWeight K L i := by
  cases i using Fin.cases with
  | zero =>
      exact rootConvolution_nonneg K (fineProfile K L)
        (fun j _ => fineProfile_nonneg K L j)
  | succ i =>
      exact splitConvolution_nonneg K (fineProfile K L)
        (fun j _ => fineProfile_nonneg K L j) i.val

/-- Explicit coefficient mass bound. -/
theorem kmtWeight_sum_le_sixteen (K : ℕ) (L : ℝ) :
    (∑ i : Fin (K + 1), kmtWeight K L i) ≤ 16 := by
  rw [show (∑ i : Fin (K + 1), kmtWeight K L i) =
      convolutionMass K (fineProfile K L) by
    exact sum_convolutionWeight K (fineProfile K L)]
  have hm := convolutionMass_le K (fineProfile K L)
    (fun j _ => fineProfile_nonneg K L j)
  have hp := fineProfile_sum_le_four K L
  nlinarith

/-- Explicit squared coefficient mass bound. -/
theorem kmtWeight_sq_sum_le_sixtyFour (K : ℕ) (L : ℝ) :
    (∑ i : Fin (K + 1), (kmtWeight K L i) ^ 2) ≤ 64 := by
  rw [show (∑ i : Fin (K + 1), (kmtWeight K L i) ^ 2) =
      convolutionSquareMass K (fineProfile K L) by
    exact sum_sq_convolutionWeight K (fineProfile K L)]
  exact convolutionSquareMass_le K (fineProfile K L)
    (fun j _ => fineProfile_nonneg K L j)
    (fineProfile_sum_le_four K L)

private theorem kmtLinearTerm_nonneg
    {K : ℕ} (C : GaussianAncestorChain K) (L : ℝ) :
    0 ≤ kmtLinearTerm C L := by
  unfold kmtLinearTerm
  exact Finset.sum_nonneg fun i _ =>
    mul_nonneg (kmtWeight_nonneg K L i) (abs_nonneg _)

/-- Fine-level endpoint term before convolution. -/
def fineEndpointTerm
    {K : ℕ} (C : GaussianAncestorChain K) (L : ℝ) : ℝ :=
  ∑ j ∈ Finset.range K,
    if dyadicLength K j < L then
      Real.sqrt (dyadicLength K j) * |C.standardized j|
    else 0

private theorem fineEndpointTerm_le
    {K : ℕ} (C : GaussianAncestorChain K)
    {L : ℝ} (hL : 0 ≤ L) :
    fineEndpointTerm C L ≤ Real.sqrt L * kmtLinearTerm C L := by
  have hpoint :
      fineEndpointTerm C L ≤
        Real.sqrt L *
          (∑ j ∈ Finset.range K,
            fineProfile K L j * |C.standardized j|) := by
    unfold fineEndpointTerm
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    by_cases hfine : dyadicLength K j < L
    · rw [if_pos hfine]
      have hlen := fine_length_profile_bound K hL j
        (Finset.mem_range.mp hj) hfine
      have h := mul_le_mul_of_nonneg_right hlen
        (abs_nonneg (C.standardized j))
      rw [mul_assoc] at h
      exact h
    · rw [if_neg hfine]
      exact mul_nonneg (Real.sqrt_nonneg _)
        (mul_nonneg (fineProfile_nonneg K L j) (abs_nonneg _))
  have hweighted := weighted_standardized_abs_le C
    (fineProfile K L) (fun j _ => fineProfile_nonneg K L j)
  have hrepr :
      weightedNoise K (fineProfile K L) C.root C.split =
        kmtLinearTerm C L := by
    unfold kmtLinearTerm kmtWeight
    rw [Fin.sum_univ_succ]
    have h2 : ∑ i : Fin K, convolutionWeight K (fineProfile K L) i.succ *
          |augmentedNoise K C.root C.split i.succ| =
        ∑ b ∈ Finset.range K,
          splitConvolution K (fineProfile K L) b * |C.split b| := by
      simp only [convolutionWeight, augmentedNoise, Fin.cases_succ]
      exact Fin.sum_univ_eq_sum_range
        (fun b => splitConvolution K (fineProfile K L) b * |C.split b|) K
    rw [h2]
    rfl
  rw [hrepr] at hweighted
  exact hpoint.trans
    (mul_le_mul_of_nonneg_left hweighted (Real.sqrt_nonneg L))

/-! ## K15 bridge data and absorption -/

structure DyadicBridgeChain (K : ℕ) extends GaussianAncestorChain K where
  parentCount : ℕ → ℝ
  quantileError : ℕ → ℝ
  correction : ℕ → ℝ
  discrepancy : ℕ → ℝ
  branchDirection : ℕ → ℝ
  branchDirection_pm : ∀ j, j < K →
    branchDirection j = 1 ∨ branchDirection j = -1
  discrepancy_succ : ∀ j, j < K →
    discrepancy (j + 1) =
      discrepancy j / 2 + branchDirection j * correction j
  top_error_bound : |discrepancy 0| ≤ 1 + 2 * root ^ 2
  quantile_error_bound : ∀ j, j < K →
    |quantileError j| ≤ 1 + split j ^ 2
  correction_bound : ∀ j, j < K →
    |correction j| ≤
      |quantileError j| +
        (|Real.sqrt (parentCount j) - Real.sqrt (dyadicLength K j)| / 2) *
          |split j|
  sqrt_difference_linear : ∀ j, j < K →
    |Real.sqrt (parentCount j) - Real.sqrt (dyadicLength K j)| ≤
      |discrepancy j| / Real.sqrt (dyadicLength K j) +
        |standardized j|
  sqrt_difference_holder : ∀ j, j < K →
    |Real.sqrt (parentCount j) - Real.sqrt (dyadicLength K j)| ≤
      Real.sqrt |discrepancy j| +
        Real.sqrt (Real.sqrt (dyadicLength K j)) *
          Real.sqrt |standardized j|

/-- K13 path quantity. -/
def pathBudget {K : ℕ} (B : DyadicBridgeChain K) : ℝ :=
  |B.discrepancy 0| +
    ∑ j ∈ Finset.range K, |B.correction j|

/-- Maximum discrepancy over `0,...,K`. -/
def chainErrorMaximum {K : ℕ} (B : DyadicBridgeChain K) : ℝ :=
  (Finset.range (K + 1)).sup' ⟨0, by simp⟩
    (fun j => |B.discrepancy j|)

private theorem discrepancy_abs_step
    {K : ℕ} (B : DyadicBridgeChain K) (j : ℕ) (hj : j < K) :
    |B.discrepancy (j + 1)| ≤
      |B.discrepancy j| / 2 + |B.correction j| := by
  have hsabs : |B.branchDirection j| = 1 := by
    rcases B.branchDirection_pm j hj with hs | hs <;> simp [hs]
  rw [B.discrepancy_succ j hj]
  calc
    |B.discrepancy j / 2 + B.branchDirection j * B.correction j| ≤
        |B.discrepancy j / 2| +
          |B.branchDirection j * B.correction j| := abs_add_le _ _
    _ = |B.discrepancy j| / 2 + |B.correction j| := by
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2),
        abs_mul, hsabs, one_mul]

/-- Error-chain Lyapunov inequality. -/
theorem discrepancy_budget_invariant
    {K : ℕ} (B : DyadicBridgeChain K) :
    ∀ n, n ≤ K →
      (∑ j ∈ Finset.range n, |B.discrepancy j|) +
          2 * |B.discrepancy n| ≤
        2 * (|B.discrepancy 0| +
          ∑ j ∈ Finset.range n, |B.correction j|) := by
  intro n
  induction n with
  | zero =>
      intro _
      simp
  | succ n ih =>
      intro hn
      have hnK : n < K := by omega
      have hprev := ih (by omega)
      have hstep := discrepancy_abs_step B n hnK
      simp only [Finset.sum_range_succ]
      nlinarith

private theorem discrepancy_sum_le_pathBudget
    {K : ℕ} (B : DyadicBridgeChain K) :
    (∑ j ∈ Finset.range K, |B.discrepancy j|) ≤
      2 * pathBudget B := by
  have h := discrepancy_budget_invariant B K le_rfl
  have hend : 0 ≤ 2 * |B.discrepancy K| := by positivity
  unfold pathBudget
  nlinarith

private theorem discrepancy_abs_le_pathBudget
    {K : ℕ} (B : DyadicBridgeChain K)
    (j : ℕ) (hj : j ≤ K) :
    |B.discrepancy j| ≤ pathBudget B := by
  have h := discrepancy_budget_invariant B j hj
  have hpartial :
      (∑ b ∈ Finset.range j, |B.correction b|) ≤
        ∑ b ∈ Finset.range K, |B.correction b| :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_subset_range.mpr hj)
      (fun _ _ _ => abs_nonneg _)
  have hsum : 0 ≤ ∑ b ∈ Finset.range j, |B.discrepancy b| :=
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  unfold pathBudget
  nlinarith

private theorem chainErrorMaximum_le_pathBudget
    {K : ℕ} (B : DyadicBridgeChain K) :
    chainErrorMaximum B ≤ pathBudget B := by
  unfold chainErrorMaximum
  refine Finset.sup'_le _ _ ?_
  intro j hj
  have hjK : j ≤ K := by
    have := Finset.mem_range.mp hj
    omega
  exact discrepancy_abs_le_pathBudget B j hjK

private theorem coarse_cross_term
    {L ell D z u delta : ℝ}
    (hL : 0 < L) (hell : L ≤ ell) (hellpos : 0 < ell)
    (hz : |z| ≤ Real.sqrt L / 4)
    (hdelta : |delta| ≤ |D| / Real.sqrt ell + |u|) :
    |delta| / 2 * |z| ≤
      |D| / 8 + (z ^ 2 + u ^ 2) / 4 := by
  have hsqrtpos : 0 < Real.sqrt ell := Real.sqrt_pos.2 hellpos
  have hsqrt : Real.sqrt L ≤ Real.sqrt ell := Real.sqrt_le_sqrt hell
  have hzell : |z| ≤ Real.sqrt ell / 4 :=
    hz.trans (div_le_div_of_nonneg_right hsqrt (by norm_num))
  have hratio : |z| / (2 * Real.sqrt ell) ≤ 1 / 8 := by
    apply (div_le_iff₀ (mul_pos (by norm_num) hsqrtpos)).2
    nlinarith
  have hDterm :
      |D| * (|z| / (2 * Real.sqrt ell)) ≤ |D| * (1 / 8) :=
    mul_le_mul_of_nonneg_left hratio (abs_nonneg D)
  have hprod : |u| * |z| / 2 ≤ (z ^ 2 + u ^ 2) / 4 := by
    have hzsq : |z| ^ 2 = z ^ 2 := sq_abs z
    have husq : |u| ^ 2 = u ^ 2 := sq_abs u
    nlinarith [sq_nonneg (|z| - |u|)]
  have hmul := mul_le_mul_of_nonneg_right hdelta
    (div_nonneg (abs_nonneg z) (by norm_num : (0 : ℝ) ≤ 2))
  calc
    |delta| / 2 * |z| ≤
        (|D| / Real.sqrt ell + |u|) / 2 * |z| := by
      nlinarith
    _ = |D| * (|z| / (2 * Real.sqrt ell)) + |u| * |z| / 2 := by
      field_simp [ne_of_gt hsqrtpos]
    _ ≤ |D| / 8 + (z ^ 2 + u ^ 2) / 4 := by
      nlinarith

private theorem fine_cross_term
    {ell D z u delta : ℝ}
    (hell : 0 ≤ ell)
    (hdelta : |delta| ≤
      Real.sqrt |D| +
        Real.sqrt (Real.sqrt ell) * Real.sqrt |u|) :
    |delta| / 2 * |z| ≤
      |D| / 8 + z ^ 2 + Real.sqrt ell * |u| / 8 := by
  let A := Real.sqrt |D|
  let C := Real.sqrt (Real.sqrt ell) * Real.sqrt |u|
  have hA : A ^ 2 = |D| := by
    dsimp [A]
    exact Real.sq_sqrt (abs_nonneg D)
  have hC : C ^ 2 = Real.sqrt ell * |u| := by
    dsimp [C]
    rw [mul_pow,
      Real.sq_sqrt (Real.sqrt_nonneg ell),
      Real.sq_sqrt (abs_nonneg u)]
  have hzsq : |z| ^ 2 = z ^ 2 := sq_abs z
  have hfirst : A * |z| / 2 ≤ |D| / 8 + z ^ 2 / 2 := by
    nlinarith [sq_nonneg (A / 2 - |z|)]
  have hsecond : C * |z| / 2 ≤ z ^ 2 / 2 + Real.sqrt ell * |u| / 8 := by
    nlinarith [sq_nonneg (C / 2 - |z|)]
  have hmul := mul_le_mul_of_nonneg_right hdelta
    (div_nonneg (abs_nonneg z) (by norm_num : (0 : ℝ) ≤ 2))
  nlinarith

private theorem correction_step_bound
    {K : ℕ} (B : DyadicBridgeChain K)
    {L : ℝ} (hL : 1 ≤ L)
    (hcoarse : ∀ j, j < K → L ≤ dyadicLength K j →
      |B.split j| ≤ Real.sqrt L / 4)
    (j : ℕ) (hj : j < K) :
    |B.correction j| ≤
      1 + 2 * B.split j ^ 2 + B.standardized j ^ 2 +
        |B.discrepancy j| / 8 +
        (if dyadicLength K j < L then
          Real.sqrt (dyadicLength K j) * |B.standardized j| / 8
        else 0) := by
  let delta := Real.sqrt (B.parentCount j) -
    Real.sqrt (dyadicLength K j)
  have heps := B.quantile_error_bound j hj
  have hcorr := B.correction_bound j hj
  by_cases hfine : dyadicLength K j < L
  · have hcross := fine_cross_term
      (ell := dyadicLength K j)
      (D := B.discrepancy j) (z := B.split j)
      (u := B.standardized j) (delta := delta)
      (le_of_lt (dyadicLength_pos K j))
      (B.sqrt_difference_holder j hj)
    rw [if_pos hfine]
    dsimp [delta] at hcross
    nlinarith [sq_nonneg (B.standardized j)]
  · have hcoarseZ := hcoarse j hj (le_of_not_gt hfine)
    have hcross := coarse_cross_term
      (L := L) (ell := dyadicLength K j)
      (D := B.discrepancy j) (z := B.split j)
      (u := B.standardized j) (delta := delta)
      (by linarith) (le_of_not_gt hfine) (dyadicLength_pos K j)
      hcoarseZ (B.sqrt_difference_linear j hj)
    rw [if_neg hfine]
    dsimp [delta] at hcross
    nlinarith [sq_nonneg (B.split j), sq_nonneg (B.standardized j)]

private theorem correction_sum_bound
    {K : ℕ} (B : DyadicBridgeChain K)
    {L : ℝ} (hL : 1 ≤ L)
    (hcoarse : ∀ j, j < K → L ≤ dyadicLength K j →
      |B.split j| ≤ Real.sqrt L / 4) :
    (∑ j ∈ Finset.range K, |B.correction j|) ≤
      (K : ℝ) +
        2 * ∑ j ∈ Finset.range K, B.split j ^ 2 +
        ∑ j ∈ Finset.range K, B.standardized j ^ 2 +
        (1 / 8 : ℝ) *
          ∑ j ∈ Finset.range K, |B.discrepancy j| +
        (1 / 8 : ℝ) * fineEndpointTerm B.toGaussianAncestorChain L := by
  have hsum :
      (∑ j ∈ Finset.range K, |B.correction j|) ≤
        ∑ j ∈ Finset.range K,
          (1 + 2 * B.split j ^ 2 + B.standardized j ^ 2 +
            |B.discrepancy j| / 8 +
            (if dyadicLength K j < L then
              Real.sqrt (dyadicLength K j) * |B.standardized j| / 8
            else 0)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact correction_step_bound B hL hcoarse j (Finset.mem_range.mp hj)
  calc
    (∑ j ∈ Finset.range K, |B.correction j|) ≤ _ := hsum
    _ = ∑ j ∈ Finset.range K,
          (1 + 2 * B.split j ^ 2 + B.standardized j ^ 2 +
            (1 / 8 : ℝ) * |B.discrepancy j| +
            (1 / 8 : ℝ) *
              (if dyadicLength K j < L then
                Real.sqrt (dyadicLength K j) * |B.standardized j|
              else 0)) := by
      apply Finset.sum_congr rfl
      intro j _
      split_ifs <;> ring
    _ = (K : ℝ) +
        2 * ∑ j ∈ Finset.range K, B.split j ^ 2 +
        ∑ j ∈ Finset.range K, B.standardized j ^ 2 +
        (1 / 8 : ℝ) *
          ∑ j ∈ Finset.range K, |B.discrepancy j| +
        (1 / 8 : ℝ) * fineEndpointTerm B.toGaussianAncestorChain L := by
      unfold fineEndpointTerm
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp

/-- Sharp absorbed K15 bound. -/
theorem pathBudget_le_sharp
    {K : ℕ} (B : DyadicBridgeChain K)
    {L : ℝ} (hL : 1 ≤ L)
    (hcoarse : ∀ j, j < K → L ≤ dyadicLength K j →
      |B.split j| ≤ Real.sqrt L / 4) :
    pathBudget B ≤
      (4 / 3 : ℝ) * (K + 1) +
        (32 / 3 : ℝ) * quadraticNoise B.toGaussianAncestorChain +
        (1 / 6 : ℝ) * Real.sqrt L *
          kmtLinearTerm B.toGaussianAncestorChain L := by
  have hcorr := correction_sum_bound B hL hcoarse
  have hdisc := discrepancy_sum_le_pathBudget B
  have htop := B.top_error_bound
  have hgauss := standardized_energy_le_six B.toGaussianAncestorChain
  have hfine := fineEndpointTerm_le B.toGaussianAncestorChain
    (L := L) (by linarith)
  have hlin := kmtLinearTerm_nonneg B.toGaussianAncestorChain L
  have hsqrt : 0 ≤ Real.sqrt L := Real.sqrt_nonneg _
  have hquad : 0 ≤ quadraticNoise B.toGaussianAncestorChain := by
    unfold quadraticNoise
    positivity
  unfold pathBudget quadraticNoise at *
  nlinarith

/-- Integer-coefficient envelope used by K18. -/
theorem pathBudget_le_envelope
    {K : ℕ} (B : DyadicBridgeChain K)
    {L : ℝ} (hL : 1 ≤ L)
    (hcoarse : ∀ j, j < K → L ≤ dyadicLength K j →
      |B.split j| ≤ Real.sqrt L / 4) :
    pathBudget B ≤
      2 * (K + 1 : ℝ) +
        11 * quadraticNoise B.toGaussianAncestorChain +
        Real.sqrt L * kmtLinearTerm B.toGaussianAncestorChain L := by
  have hsharp := pathBudget_le_sharp B hL hcoarse
  have hquad : 0 ≤ quadraticNoise B.toGaussianAncestorChain := by
    unfold quadraticNoise
    positivity
  have hlin := kmtLinearTerm_nonneg B.toGaussianAncestorChain L
  have hsqrt : 0 ≤ Real.sqrt L := Real.sqrt_nonneg _
  nlinarith

/-- Combined K15 statement: both the K13 path quantity and every chain error
obey the same x-dependent deterministic envelope. -/
theorem maximum_and_pathBudget_le
    {K : ℕ} (B : DyadicBridgeChain K)
    {L : ℝ} (hL : 1 ≤ L)
    (hcoarse : ∀ j, j < K → L ≤ dyadicLength K j →
      |B.split j| ≤ Real.sqrt L / 4) :
    max (chainErrorMaximum B) (pathBudget B) ≤
      2 * (K + 1 : ℝ) +
        11 * quadraticNoise B.toGaussianAncestorChain +
        Real.sqrt L * kmtLinearTerm B.toGaussianAncestorChain L := by
  rw [max_le_iff]
  have hpath := pathBudget_le_envelope B hL hcoarse
  exact ⟨chainErrorMaximum_le_pathBudget B |>.trans hpath, hpath⟩

/-!
THEOREM LIST
* `standardized_energy_invariant`
* `standardized_energy_le_six`, `standardized_energy_le_twelve`
* `standardized_abs_le_history`
* `weighted_standardized_abs_le`, `weighted_standardized_abs_le_fin`
* `convolutionMass_le`, `convolutionSquareMass_le`
* `kmtWeight_sum_le_sixteen`, `kmtWeight_sq_sum_le_sixtyFour`
* `discrepancy_budget_invariant`
* `pathBudget_le_sharp`, `pathBudget_le_envelope`
* `maximum_and_pathBudget_le`

CLOSES
* K14 square estimate, with constant `6` and hence the requested `12`.
* K14 weighted convolution estimate with explicit root and split coefficients.
* A threshold-dependent coarse/fine cut valid also when every level is fine or
  no level is fine.
* Explicit K15/K18 weights on the augmented normal vector, with
  `sum v ≤ 16` and `sum v^2 ≤ 64`.
* The `|D|/8` absorption, the K13 path budget, and the maximum chain error in
  one x-dependent deterministic envelope.

UNFINISHED
* No mathematical item is intentionally omitted.
* The later adapter must instantiate `DyadicBridgeChain` from K12 and the
  spatial tree chain; this file deliberately imports neither.
END
-/

end Ripple.Kurtz.StrongApprox.DyadicChainEstimate

end
