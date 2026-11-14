/-
  Ripple.Kurtz.StrongApprox.PoissonLocalization — (L): the Poisson quantile of `Φ(z)` is within one
  integer of the signed-root inverse

  With `F k = P(Pois(λ) ≤ k) = poisCdf (k+1) λ` and `q = natQuantile F (Φ z)`:
  `(PI)` at the integers `q−1` and `q+1` gives `a_{q−1}(λ) < z ≤ a_{q+1}(λ)`, where
  `a_k(λ) = poisSignedRoot k λ = sgn(k−λ)√(2 I_k(λ))`.  The endpoint `k = 0` of `(PI)` is supplied
  by the Gaussian Chernoff bound `Φ(−u) ≤ e^{−u²/2}`.
-/

import Mathlib
import Ripple.Kurtz.StrongApprox.PoissonIntersection
import Ripple.Kurtz.StrongApprox.QuantileCoupling

namespace Ripple.Kurtz.StrongApprox

open MeasureTheory ProbabilityTheory Set Finset

/-- Gaussian Chernoff bound for the lower tail: `Φ(−u) ≤ exp(−u²/2)` for `u ≥ 0`. -/
theorem stdNormalCdf_neg_le_exp {u : ℝ} (hu : 0 ≤ u) :
    stdNormalCdf (-u) ≤ Real.exp (-(u ^ 2) / 2) := by
  have h := measure_le_le_exp_mul_mgf (μ := gaussianReal 0 1) (X := id) (t := -u) (-u)
    (by linarith) (by simpa using integrable_exp_mul_gaussianReal (μ := 0) (v := 1) (-u))
  rw [mgf_id_gaussianReal] at h
  have hset : {ω : ℝ | id ω ≤ -u} = Iic (-u) := by ext x; simp
  rw [hset] at h
  rw [stdNormalCdf_eq_real, measureReal_def]
  refine h.trans (le_of_eq ?_)
  simp only [NNReal.coe_one]
  rw [← Real.exp_add]
  congr 1
  ring

theorem poisRate_zero (l : ℝ) : poisRate 0 l = l := by simp [poisRate]

theorem poisSignedRoot_zero {l : ℝ} (hl : 0 < l) :
    poisSignedRoot 0 l = -Real.sqrt (2 * l) := by
  rw [poisSignedRoot_of_gt 0 (by simpa using hl), poisRate_zero]

theorem poisCdf_one (l : ℝ) : poisCdf 1 l = Real.exp (-l) := by
  simp [poisCdf, poisTerm]

/-- Upper half of (PI) for every `k ≥ 0` (the case `k = 0` by the Chernoff bound). -/
theorem stdNormalCdf_poisSignedRoot_le_poisCdf_all (k : ℕ) {l : ℝ} (hl : 0 < l) :
    stdNormalCdf (poisSignedRoot k l) ≤ poisCdf (k + 1) l := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [poisSignedRoot_zero hl, poisCdf_one]
    refine (stdNormalCdf_neg_le_exp (Real.sqrt_nonneg _)).trans (le_of_eq ?_)
    rw [Real.sq_sqrt (by linarith)]
    congr 1; ring
  · exact stdNormalCdf_poisSignedRoot_le_poisCdf k hk hl

/-- Lower half of (PI) for every `k ≥ 0`. -/
theorem poisCdf_le_stdNormalCdf_poisSignedRoot_all (k : ℕ) {l : ℝ} (hl : 0 < l) :
    poisCdf k l ≤ stdNormalCdf (poisSignedRoot k l) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp only [poisCdf, Finset.range_zero, Finset.sum_empty]
    exact (stdNormalCdf_pos _).le
  · exact poisCdf_le_stdNormalCdf_poisSignedRoot k hk hl

/-- The Poisson(λ) cdf on `ℕ`: `poisF l k = P(Pois(λ) ≤ k)`. -/
noncomputable def poisF (l : ℝ) (k : ℕ) : ℝ := poisCdf (k + 1) l

theorem poisCdf_succ (k : ℕ) (l : ℝ) : poisCdf (k + 1) l = poisCdf k l + poisTerm k l := by
  simp [poisCdf, Finset.sum_range_succ]

theorem poisF_monotone {l : ℝ} (hl : 0 ≤ l) : Monotone (poisF l) := by
  apply monotone_nat_of_le_succ
  intro k
  unfold poisF
  rw [poisCdf_succ (k + 1)]
  linarith [poisTerm_nonneg (k + 1) hl]

theorem poisCdf_nonneg (k : ℕ) {l : ℝ} (hl : 0 ≤ l) : 0 ≤ poisCdf k l :=
  Finset.sum_nonneg fun j _ => poisTerm_nonneg j hl

theorem poisCdf_le_one (k : ℕ) {l : ℝ} (hl : 0 ≤ l) : poisCdf k l ≤ 1 := by
  have h := Real.sum_le_exp_of_nonneg hl k
  have : poisCdf k l = Real.exp (-l) * ∑ j ∈ Finset.range k, l ^ j / (j.factorial : ℝ) := by
    unfold poisCdf poisTerm
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _; ring
  rw [this]
  calc Real.exp (-l) * ∑ j ∈ Finset.range k, l ^ j / (j.factorial : ℝ)
      ≤ Real.exp (-l) * Real.exp l := mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_add]; simp

theorem poisF_nonneg {l : ℝ} (hl : 0 ≤ l) (k : ℕ) : 0 ≤ poisF l k := poisCdf_nonneg _ hl
theorem poisF_le_one {l : ℝ} (hl : 0 ≤ l) (k : ℕ) : poisF l k ≤ 1 := poisCdf_le_one _ hl

/-- Some level of the Poisson cdf reaches `Φ(z)`: via `(PI)` at a large `k`. -/
theorem exists_poisF_ge {l : ℝ} (hl : 0 < l) (z : ℝ) : ∃ k, stdNormalCdf z ≤ poisF l k := by
  obtain ⟨k, hk⟩ := exists_nat_ge (max (8 * l) (z ^ 2 / 2 + 1))
  have hk8 : 8 * l ≤ k := (le_max_left _ _).trans hk
  have hkz : z ^ 2 / 2 + 1 ≤ k := (le_max_right _ _).trans hk
  have hkpos : (0 : ℝ) < k := by linarith
  have hlk : l ≤ k := by linarith
  refine ⟨k, ?_⟩
  have hI : (k : ℝ) ≤ poisRate k l := by
    -- `I = l − k + k (log k − log l)` and `log k − log l = log (k/l) ≥ log 8 ≥ 2`
    have h8 : Real.log 8 ≤ Real.log k - Real.log l := by
      rw [← Real.log_div hkpos.ne' hl.ne']
      apply Real.log_le_log (by norm_num)
      rw [le_div_iff₀ hl]; linarith
    have hlog8 : (2 : ℝ) ≤ Real.log 8 := by
      have : (8 : ℝ) = 2 ^ 3 := by norm_num
      rw [this, Real.log_pow]
      have := Real.log_two_gt_d9
      push_cast
      linarith
    unfold poisRate
    nlinarith
  have hz : z ≤ poisSignedRoot k l := by
    rw [poisSignedRoot_of_lt k (by linarith : l < k)]
    apply le_trans (le_abs_self z)
    rw [← Real.sqrt_sq_eq_abs]
    apply Real.sqrt_le_sqrt
    linarith
  calc stdNormalCdf z ≤ stdNormalCdf (poisSignedRoot k l) := stdNormalCdf_monotone hz
    _ ≤ poisF l k := stdNormalCdf_poisSignedRoot_le_poisCdf_all k hl

/-- **(L)**: if `q = natQuantile (poisF λ) (Φ z)` then `a_{q−1}(λ) < z` (when `q ≥ 1`) and
`z ≤ a_{q+1}(λ)`. -/
theorem poisson_quantile_localization {l z : ℝ} (hl : 0 < l) {q : ℕ}
    (hq : natQuantile (poisF l) (stdNormalCdf z) = q) :
    (1 ≤ q → poisSignedRoot (q - 1) l < z) ∧ z ≤ poisSignedRoot (q + 1) l := by
  have hchar := (natQuantile_eq_iff (poisF_monotone hl.le) (exists_poisF_ge hl z)
    (stdNormalCdf_pos z) q).mp hq
  obtain ⟨h1, h2⟩ := hchar
  simp only [tail_succ] at h1
  have hΦq : stdNormalCdf z ≤ poisF l q := by linarith
  constructor
  · intro hq1
    obtain ⟨j, rfl⟩ : ∃ j, q = j + 1 := ⟨q - 1, by omega⟩
    simp only [tail_succ] at h2
    have hlt : poisF l j < stdNormalCdf z := by linarith
    have : stdNormalCdf (poisSignedRoot j l) < stdNormalCdf z :=
      lt_of_le_of_lt (stdNormalCdf_poisSignedRoot_le_poisCdf_all j hl)
        (by unfold poisF at hlt; exact hlt)
    simpa using stdNormalCdf_strictMono.lt_iff_lt.mp this
  · have : stdNormalCdf z ≤ stdNormalCdf (poisSignedRoot (q + 1) l) :=
      hΦq.trans (poisCdf_le_stdNormalCdf_poisSignedRoot_all (q + 1) hl)
    exact stdNormalCdf_strictMono.le_iff_le.mp this

end Ripple.Kurtz.StrongApprox
