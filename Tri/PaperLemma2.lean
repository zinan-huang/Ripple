/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Tri.Hoeffding
import Tri.InfectionActiveCount
import Tri.Progress

/-!
# Paper Lemma 2: multiplicative Chernoff bounds

This file gives an explicit independent-Bernoulli count chain and proves the
two multiplicative tail bounds printed as Lemma 2 of the paper.
-/

namespace Tri

open scoped ENNReal NNReal

/-- One independent Bernoulli trial, accumulated in a natural-valued counter. -/
noncomputable def iidBernoulliCountStep
    (p : ℝ≥0) (hp : p ≤ 1) (c : ℕ) : PMF ℕ :=
  (PMF.bernoulli p hp).map fun success =>
    if success then c + 1 else c

theorem iidBernoulliCountStep_decomp
    (p : ℝ≥0) (hp : p ≤ 1) (c : ℕ) (w : ℝ≥0∞) :
    expect (iidBernoulliCountStep p hp c) (fun z => w ^ z) =
      ((1 - p : ℝ≥0) : ℝ≥0∞) * w ^ c +
        (p : ℝ≥0∞) * w ^ (c + 1) := by
  rw [iidBernoulliCountStep, expect_map]
  unfold expect
  rw [tsum_fintype]
  simp [PMF.bernoulli_apply]
  ring

theorem iidBernoulliCountStep_factor
    (p : ℝ≥0) (hp : p ≤ 1) (w : ℝ≥0∞) :
    ∀ c,
      expect (iidBernoulliCountStep p hp c) (fun z => w ^ z) =
        (((1 - p : ℝ≥0) : ℝ≥0∞) + (p : ℝ≥0∞) * w) * w ^ c := by
  intro c
  rw [iidBernoulliCountStep_decomp, pow_succ]
  ring

/-- Raw lower-tail moment bound for `N` independent Bernoulli trials. -/
theorem iidBernoulli_lower_tail_raw
    (p : ℝ≥0) (hp : p ≤ 1) (w : ℝ≥0∞)
    (hw1 : w ≤ 1) (hw0 : w ≠ 0) (N k : ℕ) :
    (∑' z : ℕ,
        (if z ≤ k then iter (iidBernoulliCountStep p hp) N 0 z else 0))
      ≤
        (((1 - p : ℝ≥0) : ℝ≥0∞) + (p : ℝ≥0∞) * w) ^ N /
          w ^ k := by
  simpa using
    count_tail_bernoulli
      (iidBernoulliCountStep p hp) id w (p : ℝ≥0∞)
      ((1 - p : ℝ≥0) : ℝ≥0∞) hw1 hw0
      (fun c => (iidBernoulliCountStep_factor p hp w c).le) N k 0

/-- Raw upper-tail moment bound for `N` independent Bernoulli trials. -/
theorem iidBernoulli_upper_tail_raw
    (p : ℝ≥0) (hp : p ≤ 1) (w : ℝ≥0∞)
    (hw1 : 1 ≤ w) (hwt : w ≠ ⊤) (N k : ℕ) :
    (∑' z : ℕ,
        (if k ≤ z then iter (iidBernoulliCountStep p hp) N 0 z else 0))
      ≤
        (((1 - p : ℝ≥0) : ℝ≥0∞) + (p : ℝ≥0∞) * w) ^ N /
          w ^ k := by
  simpa using
    count_upper_tail_bernoulli
      (iidBernoulliCountStep p hp) id w (p : ℝ≥0∞)
      ((1 - p : ℝ≥0) : ℝ≥0∞) hw1 hwt
      (fun c => (iidBernoulliCountStep_factor p hp w c).le) N k 0

/-- The elementary Bernoulli exponential-moment bound
`1 - p + p * exp t ≤ exp (p * (exp t - 1))`. -/
theorem bernoulli_mgf_le_exp
    {p p' t : ℝ} (hsum : p + p' = 1) :
    p' + p * Real.exp t ≤
      Real.exp (p * (Real.exp t - 1)) := by
  calc
    p' + p * Real.exp t =
        p * (Real.exp t - 1) + 1 := by
          linarith
    _ ≤ Real.exp (p * (Real.exp t - 1)) :=
      Real.add_one_le_exp _

/-- The second-order upper bound on the negative exponential used by the
multiplicative lower-tail optimization. -/
theorem exp_neg_le_one_sub_add_half_sq
    {x : ℝ} (hx : 0 ≤ x) :
    Real.exp (-x) ≤ 1 - x + x ^ 2 / 2 := by
  have hq : 0 < 1 + x + x ^ 2 / 2 := by positivity
  rw [Real.exp_neg]
  calc
    (Real.exp x)⁻¹ ≤ (1 + x + x ^ 2 / 2)⁻¹ :=
      inv_anti₀ hq (Real.quadratic_le_exp_of_nonneg hx)
    _ ≤ 1 - x + x ^ 2 / 2 := by
      rw [inv_le_iff_one_le_mul₀ hq]
      nlinarith [sq_nonneg (x ^ 2)]

/-- The optimized real lower-tail Bernoulli moment.  The cutoff hypothesis is
the integer form of `k ≤ (1 - delta) * mu`, where `mu = N * p`. -/
theorem bernoulli_multiplicative_lower_optimized
    {p p' delta : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hsum : p + p' = 1)
    (hdelta0 : 0 ≤ delta) (_hdelta1 : delta ≤ 1)
    (N k : ℕ)
    (hk :
      (k : ℝ) ≤
        (1 - delta) * ((N : ℝ) * p)) :
    (p' + p * Real.exp (-delta)) ^ N *
        Real.exp (delta * (k : ℝ)) ≤
      Real.exp
        (-(delta ^ 2 * ((N : ℝ) * p)) / 2) := by
  have hp'0 : 0 ≤ p' := by linarith
  have hbase : 0 ≤ p' + p * Real.exp (-delta) :=
    add_nonneg hp'0 (mul_nonneg hp0 (Real.exp_nonneg _))
  have hmgf :
      p' + p * Real.exp (-delta) ≤
        Real.exp (p * (Real.exp (-delta) - 1)) :=
    bernoulli_mgf_le_exp hsum
  have hpow := pow_le_pow_left₀ hbase hmgf N
  have hTaylor :=
    exp_neg_le_one_sub_add_half_sq hdelta0
  have hNp : 0 ≤ (N : ℝ) * p :=
    mul_nonneg (by positivity) hp0
  have hmoment :
      ((N : ℝ) * p) * (Real.exp (-delta) - 1) ≤
        ((N : ℝ) * p) * (-delta + delta ^ 2 / 2) := by
    apply mul_le_mul_of_nonneg_left _ hNp
    linarith
  have hcut :
      delta * (k : ℝ) ≤
        delta * ((1 - delta) * ((N : ℝ) * p)) :=
    mul_le_mul_of_nonneg_left hk hdelta0
  calc
    (p' + p * Real.exp (-delta)) ^ N *
          Real.exp (delta * (k : ℝ)) ≤
        Real.exp (p * (Real.exp (-delta) - 1)) ^ N *
          Real.exp (delta * (k : ℝ)) :=
      mul_le_mul_of_nonneg_right hpow (Real.exp_nonneg _)
    _ = Real.exp
        ((N : ℝ) * (p * (Real.exp (-delta) - 1)) +
          delta * (k : ℝ)) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
    _ ≤ Real.exp
        (-(delta ^ 2 * ((N : ℝ) * p)) / 2) := by
      apply Real.exp_le_exp.mpr
      nlinarith

/-- Division form of `bernoulli_multiplicative_lower_optimized`, matching the
raw `ℝ≥0∞` Markov bound. -/
theorem bernoulli_multiplicative_lower_ratio
    {p p' delta : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hsum : p + p' = 1)
    (hdelta0 : 0 ≤ delta) (hdelta1 : delta ≤ 1)
    (N k : ℕ)
    (hk :
      (k : ℝ) ≤
        (1 - delta) * ((N : ℝ) * p)) :
    (p' + p * Real.exp (-delta)) ^ N /
        Real.exp (-delta) ^ k ≤
      Real.exp
        (-(delta ^ 2 * ((N : ℝ) * p)) / 2) := by
  have hrewrite :
      (p' + p * Real.exp (-delta)) ^ N /
          Real.exp (-delta) ^ k =
        (p' + p * Real.exp (-delta)) ^ N *
          Real.exp (delta * (k : ℝ)) := by
    rw [div_eq_mul_inv, ← Real.exp_nat_mul, ← Real.exp_neg]
    congr 2
    ring
  rw [hrewrite]
  exact bernoulli_multiplicative_lower_optimized
    hp0 hp1 hsum hdelta0 hdelta1 N k hk

/-- Paper Lemma 2(a), in an exact iid count-chain form.

`k` is an integer cutoff below `(1 - delta) * mu`; hence this bounds every
integer outcome in the paper event `S_N ≤ (1 - delta) * mu`. -/
theorem lemma2_lower_tail
    (p : ℝ≥0) (hp : p ≤ 1)
    (delta : ℝ) (hdelta0 : 0 ≤ delta) (hdelta1 : delta ≤ 1)
    (N k : ℕ)
    (hk :
      (k : ℝ) ≤
        (1 - delta) * ((N : ℝ) * (p : ℝ))) :
    (∑' z : ℕ,
        (if z ≤ k then
          iter (iidBernoulliCountStep p hp) N 0 z
        else 0)) ≤
      ENNReal.ofReal
        (Real.exp
          (-(delta ^ 2 * ((N : ℝ) * (p : ℝ))) / 2)) := by
  let w : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-delta))
  have hw1 : w ≤ 1 := by
    dsimp only [w]
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal <|
      (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hdelta0))
  have hw0 : w ≠ 0 := by
    dsimp only [w]
    exact ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)
  refine
    (iidBernoulli_lower_tail_raw p hp w hw1 hw0 N k).trans ?_
  have hp0R : 0 ≤ (p : ℝ) := p.2
  have hp1R : (p : ℝ) ≤ 1 := by exact_mod_cast hp
  have hp'0R : 0 ≤ ((1 - p : ℝ≥0) : ℝ) :=
    (1 - p : ℝ≥0).2
  have hsumR :
      (p : ℝ) + ((1 - p : ℝ≥0) : ℝ) = 1 := by
    rw [NNReal.coe_sub hp]
    exact add_tsub_cancel_of_le hp
  have hbase :
      (((1 - p : ℝ≥0) : ℝ≥0∞) + (p : ℝ≥0∞) * w) =
        ENNReal.ofReal
          (((1 - p : ℝ≥0) : ℝ) +
            (p : ℝ) * Real.exp (-delta)) := by
    dsimp only [w]
    rw [ENNReal.coe_nnreal_eq, ENNReal.coe_nnreal_eq,
      ← ENNReal.ofReal_mul hp0R,
      ← ENNReal.ofReal_add hp'0R
        (mul_nonneg hp0R (Real.exp_nonneg _))]
  rw [hbase,
    ← ENNReal.ofReal_pow
      (add_nonneg hp'0R
        (mul_nonneg hp0R (Real.exp_nonneg _))),
    ← ENNReal.ofReal_pow (Real.exp_nonneg _),
    ← ENNReal.ofReal_div_of_pos (pow_pos (Real.exp_pos _) k)]
  exact ENNReal.ofReal_le_ofReal <|
    bernoulli_multiplicative_lower_ratio
      hp0R hp1R hsumR hdelta0 hdelta1 N k hk

/-- The scalar inequality behind the printed upper-tail constant `1 / 3`. -/
theorem delta_sq_div_three_le_one_add_mul_log_sub
    {delta : ℝ} (hdelta0 : 0 ≤ delta) (hdelta1 : delta ≤ 1) :
    delta ^ 2 / 3 ≤
      (1 + delta) * Real.log (1 + delta) - delta := by
  have hden : 0 < delta + 2 := by linarith
  have hlog :
      2 * delta / (delta + 2) ≤ Real.log (1 + delta) :=
    Real.le_log_one_add_of_nonneg hdelta0
  have hone : 0 ≤ 1 + delta := by linarith
  have hscaled :
      (1 + delta) * (2 * delta / (delta + 2)) ≤
        (1 + delta) * Real.log (1 + delta) :=
    mul_le_mul_of_nonneg_left hlog hone
  have hrat :
      delta ^ 2 / 3 ≤ delta ^ 2 / (delta + 2) := by
    rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 3) hden]
    nlinarith [sq_nonneg delta]
  have hid :
      (1 + delta) * (2 * delta / (delta + 2)) - delta =
        delta ^ 2 / (delta + 2) := by
    field_simp
    ring
  rw [← hid] at hrat
  linarith

/-- The optimized real upper-tail Bernoulli moment, in the division form
consumed by the raw Markov bound. -/
theorem bernoulli_multiplicative_upper_ratio
    {p p' delta : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hsum : p + p' = 1)
    (hdelta0 : 0 ≤ delta) (hdelta1 : delta ≤ 1)
    (N k : ℕ)
    (hk :
      (1 + delta) * ((N : ℝ) * p) ≤ (k : ℝ)) :
    (p' + p * Real.exp (Real.log (1 + delta))) ^ N /
        Real.exp (Real.log (1 + delta)) ^ k ≤
      Real.exp
        (-(delta ^ 2 * ((N : ℝ) * p)) / 3) := by
  let t : ℝ := Real.log (1 + delta)
  have honePos : 0 < 1 + delta := by linarith
  have ht0 : 0 ≤ t := by
    dsimp only [t]
    exact Real.log_nonneg (by linarith)
  have hexplog : Real.exp t = 1 + delta := by
    dsimp only [t]
    exact Real.exp_log honePos
  have hp'0 : 0 ≤ p' := by linarith
  have hbase : 0 ≤ p' + p * Real.exp t :=
    add_nonneg hp'0 (mul_nonneg hp0 (Real.exp_nonneg _))
  have hmgf :
      p' + p * Real.exp t ≤
        Real.exp (p * (Real.exp t - 1)) :=
    bernoulli_mgf_le_exp hsum
  have hpow := pow_le_pow_left₀ hbase hmgf N
  have hrewrite :
      (p' + p * Real.exp t) ^ N / Real.exp t ^ k =
        (p' + p * Real.exp t) ^ N *
          Real.exp (-(t * (k : ℝ))) := by
    rw [div_eq_mul_inv, ← Real.exp_nat_mul, ← Real.exp_neg]
    congr 2
    ring
  have hNp : 0 ≤ (N : ℝ) * p :=
    mul_nonneg (by positivity) hp0
  have hcut :
      t * ((1 + delta) * ((N : ℝ) * p)) ≤
        t * (k : ℝ) :=
    mul_le_mul_of_nonneg_left hk ht0
  have hconstant :=
    delta_sq_div_three_le_one_add_mul_log_sub
      hdelta0 hdelta1
  have hconstantScaled :
      ((N : ℝ) * p) * (delta ^ 2 / 3) ≤
        ((N : ℝ) * p) *
          ((1 + delta) * t - delta) := by
    apply mul_le_mul_of_nonneg_left _ hNp
    simpa only [t] using hconstant
  change
    (p' + p * Real.exp t) ^ N / Real.exp t ^ k ≤ _
  rw [hrewrite]
  calc
    (p' + p * Real.exp t) ^ N *
          Real.exp (-(t * (k : ℝ))) ≤
        Real.exp (p * (Real.exp t - 1)) ^ N *
          Real.exp (-(t * (k : ℝ))) :=
      mul_le_mul_of_nonneg_right hpow (Real.exp_nonneg _)
    _ = Real.exp
        ((N : ℝ) * (p * (Real.exp t - 1)) -
          t * (k : ℝ)) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
    _ ≤ Real.exp
        (-(delta ^ 2 * ((N : ℝ) * p)) / 3) := by
      apply Real.exp_le_exp.mpr
      rw [hexplog]
      nlinarith

/-- Paper Lemma 2(b), in an exact iid count-chain form.

`k` is an integer cutoff above `(1 + delta) * mu`; taking the natural ceiling
of that real threshold gives the paper event exactly. -/
theorem lemma2_upper_tail
    (p : ℝ≥0) (hp : p ≤ 1)
    (delta : ℝ) (hdelta0 : 0 ≤ delta) (hdelta1 : delta ≤ 1)
    (N k : ℕ)
    (hk :
      (1 + delta) * ((N : ℝ) * (p : ℝ)) ≤ (k : ℝ)) :
    (∑' z : ℕ,
        (if k ≤ z then
          iter (iidBernoulliCountStep p hp) N 0 z
        else 0)) ≤
      ENNReal.ofReal
        (Real.exp
          (-(delta ^ 2 * ((N : ℝ) * (p : ℝ))) / 3)) := by
  let t : ℝ := Real.log (1 + delta)
  let w : ℝ≥0∞ := ENNReal.ofReal (Real.exp t)
  have honePos : 0 < 1 + delta := by linarith
  have hexplog : Real.exp t = 1 + delta := by
    dsimp only [t]
    exact Real.exp_log honePos
  have hw1 : 1 ≤ w := by
    dsimp only [w]
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal <| by
      rw [hexplog]
      linarith
  have hwt : w ≠ ⊤ := by
    dsimp only [w]
    exact ENNReal.ofReal_ne_top
  refine
    (iidBernoulli_upper_tail_raw p hp w hw1 hwt N k).trans ?_
  have hp0R : 0 ≤ (p : ℝ) := p.2
  have hp1R : (p : ℝ) ≤ 1 := by exact_mod_cast hp
  have hp'0R : 0 ≤ ((1 - p : ℝ≥0) : ℝ) :=
    (1 - p : ℝ≥0).2
  have hsumR :
      (p : ℝ) + ((1 - p : ℝ≥0) : ℝ) = 1 := by
    rw [NNReal.coe_sub hp]
    exact add_tsub_cancel_of_le hp
  have hbase :
      (((1 - p : ℝ≥0) : ℝ≥0∞) + (p : ℝ≥0∞) * w) =
        ENNReal.ofReal
          (((1 - p : ℝ≥0) : ℝ) +
            (p : ℝ) * Real.exp t) := by
    dsimp only [w]
    rw [ENNReal.coe_nnreal_eq, ENNReal.coe_nnreal_eq,
      ← ENNReal.ofReal_mul hp0R,
      ← ENNReal.ofReal_add hp'0R
        (mul_nonneg hp0R (Real.exp_nonneg _))]
  rw [hbase,
    ← ENNReal.ofReal_pow
      (add_nonneg hp'0R
        (mul_nonneg hp0R (Real.exp_nonneg _))),
    ← ENNReal.ofReal_pow (Real.exp_nonneg _),
    ← ENNReal.ofReal_div_of_pos (pow_pos (Real.exp_pos _) k)]
  exact ENNReal.ofReal_le_ofReal <|
    bernoulli_multiplicative_upper_ratio
      hp0R hp1R hsumR hdelta0 hdelta1 N k hk

/-- Paper Lemma 2(a) with the printed real threshold and mean `mu = N p`. -/
theorem lemma2_lower_tail_paper
    (p : ℝ≥0) (hp : p ≤ 1)
    (delta : ℝ) (hdelta0 : 0 ≤ delta) (hdelta1 : delta ≤ 1)
    (N : ℕ) :
    (∑' z : ℕ,
        (if (z : ℝ) ≤
            (1 - delta) * ((N : ℝ) * (p : ℝ)) then
          iter (iidBernoulliCountStep p hp) N 0 z
        else 0)) ≤
      ENNReal.ofReal
        (Real.exp
          (-(delta ^ 2 * ((N : ℝ) * (p : ℝ))) / 2)) := by
  have hthreshold :
      0 ≤ (1 - delta) * ((N : ℝ) * (p : ℝ)) :=
    mul_nonneg (sub_nonneg.mpr hdelta1)
      (mul_nonneg (by positivity) p.2)
  simpa only [Nat.le_floor_iff hthreshold] using
    lemma2_lower_tail p hp delta hdelta0 hdelta1 N
      ⌊(1 - delta) * ((N : ℝ) * (p : ℝ))⌋₊
      (Nat.floor_le hthreshold)

/-- Paper Lemma 2(b) with the printed real threshold and mean `mu = N p`. -/
theorem lemma2_upper_tail_paper
    (p : ℝ≥0) (hp : p ≤ 1)
    (delta : ℝ) (hdelta0 : 0 ≤ delta) (hdelta1 : delta ≤ 1)
    (N : ℕ) :
    (∑' z : ℕ,
        (if (1 + delta) * ((N : ℝ) * (p : ℝ)) ≤
            (z : ℝ) then
          iter (iidBernoulliCountStep p hp) N 0 z
        else 0)) ≤
      ENNReal.ofReal
        (Real.exp
          (-(delta ^ 2 * ((N : ℝ) * (p : ℝ))) / 3)) := by
  simpa only [Nat.ceil_le] using
    lemma2_upper_tail p hp delta hdelta0 hdelta1 N
      ⌈(1 + delta) * ((N : ℝ) * (p : ℝ))⌉₊
      (Nat.le_ceil _)

end Tri

#print axioms Tri.lemma2_lower_tail_paper
#print axioms Tri.lemma2_upper_tail_paper
