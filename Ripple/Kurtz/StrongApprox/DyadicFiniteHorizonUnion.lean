-- Ripple/Kurtz/StrongApprox/DyadicFiniteHorizonUnion.lean
import Mathlib

/-!
# K17: finite-horizon union assembly for the dyadic KMT estimate

This file is deliberately independent of the Gaussian-tree implementation.
It takes the coarse-node failure estimate and the fixed-point K16 estimate as
hypotheses, and performs only the finite union and numerical absorption.

For `n = 2^K`, `kmtHorizonLog K` is literally `log (2*n)`.
The shift is `u = 2048 * log (2*n) + x`.  The resulting constants are

* `C = 2094`,
* `a = 6`,
* `b = 9 / 16384`.
-/

noncomputable section

open MeasureTheory Set Finset
open scoped BigOperators ENNReal

namespace Ripple.Kurtz.StrongApprox.DyadicFiniteHorizonUnion

variable {Ω : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The finite horizon `n = 2^K`. -/
def dyadicHorizon (K : ℕ) : ℕ := 2 ^ K

/-- `log (2*n)` when `n = 2^K`. -/
def kmtHorizonLog (K : ℕ) : ℝ :=
  Real.log ((2 : ℝ) ^ (K + 1))

/-- The coarse Gaussian cutoff used by H1 and H2. -/
def kmtCoarseScale (K : ℕ) (x : ℝ) : ℝ :=
  128 * (kmtHorizonLog K + x)

/-- K17's deterministic shift inside the fixed-point tail. -/
def kmtUnionShift (K : ℕ) (x : ℝ) : ℝ :=
  2048 * kmtHorizonLog K + x

/-- The threshold appearing in the K16 fixed-point estimate. -/
def kmtPointThreshold (K : ℕ) (u : ℝ) : ℝ :=
  (68 / 3 : ℝ) * (((K + 1 : ℕ) : ℝ)) + u

/-- Maximum of the errors at the integer times `0, ..., 2^K`. -/
def kmtHorizonMaximum
    (K : ℕ) (E : ℕ → Ω → ℝ) (ω : Ω) : ℝ :=
  (Finset.univ : Finset (Fin (dyadicHorizon K + 1))).sup'
    ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
    (fun t => E t.val ω)

/-- The logarithm used in the theorem is exactly `log (2 * 2^K)`. -/
theorem kmtHorizonLog_eq_log_two_mul_horizon (K : ℕ) :
    kmtHorizonLog K =
      Real.log (2 * (dyadicHorizon K : ℝ)) := by
  unfold kmtHorizonLog
  congr 1
  simp [dyadicHorizon, pow_succ, mul_comm]

private theorem kmtHorizonLog_eq_generation (K : ℕ) :
    kmtHorizonLog K =
      (((K + 1 : ℕ) : ℝ)) * Real.log 2 := by
  unfold kmtHorizonLog
  rw [Real.log_pow]

private theorem exp_kmtHorizonLog (K : ℕ) :
    Real.exp (kmtHorizonLog K) =
      (2 : ℝ) ^ (K + 1) := by
  unfold kmtHorizonLog
  rw [Real.exp_log (pow_pos (by norm_num) _)]

private theorem kmtHorizonLog_pos (K : ℕ) :
    0 < kmtHorizonLog K := by
  rw [kmtHorizonLog_eq_generation]
  exact mul_pos (by positivity) (Real.log_pos (by norm_num))

/-- Positivity of the advertised absolute constants `C`, `a`, and `b`. -/
theorem finiteHorizonKMT_constants_pos :
    (0 : ℝ) < 2094 ∧
      (0 : ℝ) < 6 ∧
        (0 : ℝ) < 9 / 16384 := by
  norm_num

private theorem generation_cast_le_two_kmtHorizonLog (K : ℕ) :
    (((K + 1 : ℕ) : ℝ)) ≤ 2 * kmtHorizonLog K := by
  have hhalf : (1 / 2 : ℝ) ≤ Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hk : 0 ≤ (((K + 1 : ℕ) : ℝ)) := by positivity
  have hmul :
      (((K + 1 : ℕ) : ℝ)) * (1 / 2 : ℝ) ≤
        (((K + 1 : ℕ) : ℝ)) * Real.log 2 :=
    mul_le_mul_of_nonneg_left hhalf hk
  rw [kmtHorizonLog_eq_generation]
  nlinarith

private theorem horizon_card_cast_le_exp (K : ℕ) :
    ((dyadicHorizon K + 1 : ℕ) : ℝ) ≤
      Real.exp (kmtHorizonLog K) := by
  have hn : 1 ≤ dyadicHorizon K := by
    unfold dyadicHorizon
    exact one_le_pow₀ (by norm_num)
  have hnat :
      dyadicHorizon K + 1 ≤ 2 * dyadicHorizon K := by
    omega
  calc
    ((dyadicHorizon K + 1 : ℕ) : ℝ) ≤
        ((2 * dyadicHorizon K : ℕ) : ℝ) := by
      exact_mod_cast hnat
    _ = (2 : ℝ) ^ (K + 1) := by
      simp [dyadicHorizon, pow_succ, mul_comm]
    _ = Real.exp (kmtHorizonLog K) :=
      (exp_kmtHorizonLog K).symm

private theorem kmtUnionShift_nonneg
    (K : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ kmtUnionShift K x := by
  unfold kmtUnionShift
  nlinarith [kmtHorizonLog_pos K]

private theorem point_threshold_shift_le
    (K : ℕ) (x : ℝ) :
    kmtPointThreshold K (kmtUnionShift K x) ≤
      2094 * kmtHorizonLog K + x := by
  have hgeneration := generation_cast_le_two_kmtHorizonLog K
  have hlog := (kmtHorizonLog_pos K).le
  unfold kmtPointThreshold kmtUnionShift
  nlinarith

/-- The exact square identity behind the quadratic K17 absorption. -/
private theorem shifted_square_ratio
    {ell x : ℝ} (hsum : 0 < ell + x) :
    4095 * ell + x ≤
      (2048 * ell + x) ^ 2 / (ell + x) := by
  apply (le_div_iff₀ hsum).2
  nlinarith [sq_nonneg (2047 * ell)]

private theorem coarse_exponent_le
    (K : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    kmtHorizonLog K +
        -(kmtCoarseScale K x / 32) ≤
      -((9 / 16384 : ℝ) * x) := by
  have hlog := (kmtHorizonLog_pos K).le
  unfold kmtCoarseScale
  nlinarith

private theorem linear_exponent_le
    (K : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    kmtHorizonLog K +
        -(3 * kmtUnionShift K x / 512) ≤
      -((9 / 16384 : ℝ) * x) := by
  have hlog := (kmtHorizonLog_pos K).le
  unfold kmtUnionShift
  nlinarith

private theorem quadratic_exponent_ge
    (K : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    2 * kmtHorizonLog K + (9 / 16384 : ℝ) * x ≤
      9 * kmtUnionShift K x ^ 2 /
        (128 * kmtCoarseScale K x) := by
  let ell := kmtHorizonLog K
  have hell : 0 < ell := by
    dsimp [ell]
    exact kmtHorizonLog_pos K
  have hsum : 0 < ell + x := by linarith
  have hratio :
      4095 * ell + x ≤
        (2048 * ell + x) ^ 2 / (ell + x) :=
    shifted_square_ratio hsum
  have hcoefficient :
      2 * ell + (9 / 16384 : ℝ) * x ≤
        (9 / 16384 : ℝ) * (4095 * ell + x) := by
    nlinarith [hell.le]
  have hscaled :
      (9 / 16384 : ℝ) * (4095 * ell + x) ≤
        (9 / 16384 : ℝ) *
          ((2048 * ell + x) ^ 2 / (ell + x)) :=
    mul_le_mul_of_nonneg_left hratio (by norm_num)
  change
    2 * ell + (9 / 16384 : ℝ) * x ≤
      9 * (2048 * ell + x) ^ 2 /
        (128 * (128 * (ell + x)))
  calc
    2 * ell + (9 / 16384 : ℝ) * x ≤
        (9 / 16384 : ℝ) * (4095 * ell + x) :=
      hcoefficient
    _ ≤ (9 / 16384 : ℝ) *
        ((2048 * ell + x) ^ 2 / (ell + x)) :=
      hscaled
    _ = 9 * (2048 * ell + x) ^ 2 /
        (128 * (128 * (ell + x))) := by
      field_simp [hsum.ne']
      <;> ring

private theorem measureReal_iUnion_fintype_le
    {ι : Type*} [Fintype ι] (A : ι → Set Ω) :
    μ.real (⋃ i, A i) ≤ ∑ i, μ.real (A i) := by
  classical
  change
    (μ (⋃ i, A i)).toReal ≤
      ∑ i, (μ (A i)).toReal
  have hmeasure :
      μ (⋃ i, A i) ≤ ∑ i, μ (A i) :=
    measure_iUnion_fintype_le μ A
  have hsum_ne_top : (∑ i, μ (A i)) ≠ ⊤ := by
    rw [ENNReal.sum_ne_top]
    intro i _hi
    exact measure_ne_top μ (A i)
  have hreal := ENNReal.toReal_mono hsum_ne_top hmeasure
  rw [ENNReal.toReal_sum
    (fun i _hi => measure_ne_top μ (A i))] at hreal
  exact hreal

/-- K17 finite-horizon assembly.

`hcoarse` is H1.  `hpoint` is precisely the per-time H2 statement supplied
by `DyadicFixedChainTails` after the later adapter identifies its error
variable.  No independence or measurability information is needed here.
-/
theorem finiteHorizonKMT_union_tail
    (K : ℕ)
    (E : ℕ → Ω → ℝ)
    (bad : ℝ → Set Ω)
    (hcoarse :
      ∀ x : ℝ, 0 ≤ x →
        μ.real (bad x) ≤
          4 * (dyadicHorizon K : ℝ) *
            Real.exp (-(kmtCoarseScale K x / 32)))
    (hpoint :
      ∀ t : ℕ, t ≤ dyadicHorizon K →
      ∀ x u : ℝ, 0 ≤ x → 0 ≤ u →
        μ.real
            ({ω | kmtPointThreshold K u < E t ω} \ bad x) ≤
          Real.exp (-(3 * u / 512)) +
            (2 : ℝ) ^ (K + 1) *
              Real.exp
                (-(9 * u ^ 2 /
                  (128 * kmtCoarseScale K x))))
    {x : ℝ} (hx : 0 ≤ x) :
    μ.real
        {ω |
          2094 * kmtHorizonLog K + x <
            kmtHorizonMaximum K E ω} ≤
      6 * Real.exp (-((9 / 16384 : ℝ) * x)) := by
  classical
  let A : Fin (dyadicHorizon K + 1) → Set Ω := fun t =>
    {ω |
      kmtPointThreshold K (kmtUnionShift K x) <
        E t.val ω} \ bad x

  have hsubset :
      {ω |
        2094 * kmtHorizonLog K + x <
          kmtHorizonMaximum K E ω} ⊆
        bad x ∪ ⋃ t, A t := by
    intro ω hω
    rw [Set.mem_setOf_eq] at hω
    unfold kmtHorizonMaximum at hω
    rw [Finset.lt_sup'_iff] at hω
    rcases hω with ⟨t, _ht, ht⟩
    have hpointExceed :
        kmtPointThreshold K (kmtUnionShift K x) <
          E t.val ω :=
      lt_of_le_of_lt (point_threshold_shift_le K x) ht
    by_cases hb : ω ∈ bad x
    · exact Or.inl hb
    · refine Or.inr (Set.mem_iUnion.2 ⟨t, ?_⟩)
      simpa [A] using (And.intro hpointExceed hb)

  have hpointEach (t : Fin (dyadicHorizon K + 1)) :
      μ.real (A t) ≤
        Real.exp (-(3 * kmtUnionShift K x / 512)) +
          (2 : ℝ) ^ (K + 1) *
            Real.exp
              (-(9 * kmtUnionShift K x ^ 2 /
                (128 * kmtCoarseScale K x))) := by
    simpa [A] using
      hpoint t.val (Nat.lt_succ_iff.mp t.isLt)
        x (kmtUnionShift K x) hx
        (kmtUnionShift_nonneg K hx)

  have hcard :
      ((dyadicHorizon K + 1 : ℕ) : ℝ) ≤
        Real.exp (kmtHorizonLog K) :=
    horizon_card_cast_le_exp K

  have hnexp :
      (dyadicHorizon K : ℝ) ≤
        Real.exp (kmtHorizonLog K) := by
    have hsucc :
        (dyadicHorizon K : ℝ) ≤
          ((dyadicHorizon K + 1 : ℕ) : ℝ) := by
      exact_mod_cast (Nat.le_succ (dyadicHorizon K))
    exact hsucc.trans hcard

  have hbadFinal :
      μ.real (bad x) ≤
        4 * Real.exp (-((9 / 16384 : ℝ) * x)) := by
    calc
      μ.real (bad x) ≤
          4 * (dyadicHorizon K : ℝ) *
            Real.exp (-(kmtCoarseScale K x / 32)) :=
        hcoarse x hx
      _ ≤ 4 * Real.exp (kmtHorizonLog K) *
          Real.exp (-(kmtCoarseScale K x / 32)) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hnexp (by norm_num))
          (Real.exp_nonneg _)
      _ = 4 * Real.exp
          (kmtHorizonLog K +
            -(kmtCoarseScale K x / 32)) := by
        rw [Real.exp_add]
        ring
      _ ≤ 4 * Real.exp
          (-((9 / 16384 : ℝ) * x)) := by
        exact mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (coarse_exponent_le K hx))
          (by norm_num)

  have hlinear :
      ((dyadicHorizon K + 1 : ℕ) : ℝ) *
          Real.exp (-(3 * kmtUnionShift K x / 512)) ≤
        Real.exp (-((9 / 16384 : ℝ) * x)) := by
    calc
      ((dyadicHorizon K + 1 : ℕ) : ℝ) *
          Real.exp (-(3 * kmtUnionShift K x / 512)) ≤
        Real.exp (kmtHorizonLog K) *
          Real.exp (-(3 * kmtUnionShift K x / 512)) :=
        mul_le_mul_of_nonneg_right hcard (Real.exp_nonneg _)
      _ = Real.exp
          (kmtHorizonLog K +
            -(3 * kmtUnionShift K x / 512)) := by
        rw [Real.exp_add]
      _ ≤ Real.exp (-((9 / 16384 : ℝ) * x)) :=
        Real.exp_le_exp.mpr (linear_exponent_le K hx)

  have hquadratic :
      ((dyadicHorizon K + 1 : ℕ) : ℝ) *
          ((2 : ℝ) ^ (K + 1) *
            Real.exp
              (-(9 * kmtUnionShift K x ^ 2 /
                (128 * kmtCoarseScale K x)))) ≤
        Real.exp (-((9 / 16384 : ℝ) * x)) := by
    rw [← exp_kmtHorizonLog K]
    calc
      ((dyadicHorizon K + 1 : ℕ) : ℝ) *
          (Real.exp (kmtHorizonLog K) *
            Real.exp
              (-(9 * kmtUnionShift K x ^ 2 /
                (128 * kmtCoarseScale K x)))) ≤
        Real.exp (kmtHorizonLog K) *
          (Real.exp (kmtHorizonLog K) *
            Real.exp
              (-(9 * kmtUnionShift K x ^ 2 /
                (128 * kmtCoarseScale K x)))) := by
        exact mul_le_mul_of_nonneg_right hcard
          (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))
      _ = Real.exp
          (kmtHorizonLog K + kmtHorizonLog K) *
            Real.exp
              (-(9 * kmtUnionShift K x ^ 2 /
                (128 * kmtCoarseScale K x))) := by
        rw [Real.exp_add]
        ring
      _ = Real.exp
          ((kmtHorizonLog K + kmtHorizonLog K) +
            -(9 * kmtUnionShift K x ^ 2 /
              (128 * kmtCoarseScale K x))) := by
        rw [Real.exp_add (kmtHorizonLog K + kmtHorizonLog K)]
      _ ≤ Real.exp (-((9 / 16384 : ℝ) * x)) := by
        apply Real.exp_le_exp.mpr
        have hq := quadratic_exponent_ge K hx
        linarith

  have hpointUnionRaw :
      μ.real (⋃ t, A t) ≤
        ((dyadicHorizon K + 1 : ℕ) : ℝ) *
          (Real.exp (-(3 * kmtUnionShift K x / 512)) +
            (2 : ℝ) ^ (K + 1) *
              Real.exp
                (-(9 * kmtUnionShift K x ^ 2 /
                  (128 * kmtCoarseScale K x)))) := by
    calc
      μ.real (⋃ t, A t) ≤ ∑ t, μ.real (A t) :=
        measureReal_iUnion_fintype_le (μ := μ) A
      _ ≤ ∑ _t,
          (Real.exp (-(3 * kmtUnionShift K x / 512)) +
            (2 : ℝ) ^ (K + 1) *
              Real.exp
                (-(9 * kmtUnionShift K x ^ 2 /
                  (128 * kmtCoarseScale K x)))) :=
        Finset.sum_le_sum fun t _ht => hpointEach t
      _ = ((dyadicHorizon K + 1 : ℕ) : ℝ) *
          (Real.exp (-(3 * kmtUnionShift K x / 512)) +
            (2 : ℝ) ^ (K + 1) *
              Real.exp
                (-(9 * kmtUnionShift K x ^ 2 /
                  (128 * kmtCoarseScale K x)))) := by
        simp [nsmul_eq_mul]
        ring

  have hpointUnion :
      μ.real (⋃ t, A t) ≤
        2 * Real.exp (-((9 / 16384 : ℝ) * x)) := by
    calc
      μ.real (⋃ t, A t) ≤
          ((dyadicHorizon K + 1 : ℕ) : ℝ) *
            (Real.exp (-(3 * kmtUnionShift K x / 512)) +
              (2 : ℝ) ^ (K + 1) *
                Real.exp
                  (-(9 * kmtUnionShift K x ^ 2 /
                    (128 * kmtCoarseScale K x)))) :=
        hpointUnionRaw
      _ = ((dyadicHorizon K + 1 : ℕ) : ℝ) *
            Real.exp (-(3 * kmtUnionShift K x / 512)) +
          ((dyadicHorizon K + 1 : ℕ) : ℝ) *
            ((2 : ℝ) ^ (K + 1) *
              Real.exp
                (-(9 * kmtUnionShift K x ^ 2 /
                  (128 * kmtCoarseScale K x)))) := by
        ring
      _ ≤ Real.exp (-((9 / 16384 : ℝ) * x)) +
          Real.exp (-((9 / 16384 : ℝ) * x)) :=
        add_le_add hlinear hquadratic
      _ = 2 * Real.exp (-((9 / 16384 : ℝ) * x)) := by
        ring

  calc
    μ.real
        {ω |
          2094 * kmtHorizonLog K + x <
            kmtHorizonMaximum K E ω} ≤
      μ.real (bad x ∪ ⋃ t, A t) :=
        measureReal_mono hsubset
    _ ≤ μ.real (bad x) + μ.real (⋃ t, A t) :=
      measureReal_union_le _ _
    _ ≤ 4 * Real.exp (-((9 / 16384 : ℝ) * x)) +
        2 * Real.exp (-((9 / 16384 : ℝ) * x)) :=
      add_le_add hbadFinal hpointUnion
    _ = 6 * Real.exp (-((9 / 16384 : ℝ) * x)) := by
      ring

/-!
THEOREM LIST
* `kmtHorizonLog_eq_log_two_mul_horizon`
* `finiteHorizonKMT_constants_pos`
* `finiteHorizonKMT_union_tail`

CLOSES
* K17 union assembly from H1 and the per-time H2 hypothesis.
* The maximum is over every integer time `0 ≤ t ≤ 2^K`.
* Explicit constants: `C = 2094`, `a = 6`, `b = 9 / 16384`.
* The `n+1` and `2^(K+1)` prefactors are absorbed uniformly, including
  `K = 0` and `x = 0`.

UNFINISHED
* Nothing inside the requested K17 assembly.
* Deriving H1 from Gaussian coarse-node tails is intentionally absent, as
  requested; it is the next round.
* Wiring the concrete KMT error process into `E` and the concrete coarse event
  into `bad` is also outside this abstract assembly.
END
-/

end Ripple.Kurtz.StrongApprox.DyadicFiniteHorizonUnion

end
