/-
  Ripple.Kurtz.StrongApprox.BinomialTail — Chernoff bound for the symmetric binomial tail

  Mathematics: first half of the large-deviation step (N1-large).

  `binPMF m j = C(m,j)/2^m`, `binTail m k = Σ_{k ≤ j ≤ m} binPMF m j = P(Bin(m,½) ≥ k)`.
  Chernoff: `binTail m k ≤ exp(−θ(k − m/2) + mθ²/8)` for `θ ≥ 0`, hence with the standardized
  deviation `y = (2k − m)/√m ≥ 0`: `binTail m k ≤ exp(−y²/2)`.
-/

import Mathlib

namespace Ripple.Kurtz.StrongApprox

open Finset

/-- Symmetric binomial point mass `C(m,j)/2^m`. -/
noncomputable def binPMF (m j : ℕ) : ℝ := (m.choose j : ℝ) / 2 ^ m

/-- Upper tail `P(Bin(m,½) ≥ k) = Σ_{k ≤ j ≤ m} C(m,j)/2^m`. -/
noncomputable def binTail (m k : ℕ) : ℝ := ∑ j ∈ Finset.Ico k (m + 1), binPMF m j

theorem binPMF_nonneg (m j : ℕ) : 0 ≤ binPMF m j := by
  unfold binPMF; positivity

theorem binTail_nonneg (m k : ℕ) : 0 ≤ binTail m k :=
  Finset.sum_nonneg fun j _ => binPMF_nonneg m j

/-- Exponential moment of the binomial coefficients: `Σ_j C(m,j) e^{θ j} = (1 + e^θ)^m`. -/
theorem sum_choose_mul_exp (m : ℕ) (θ : ℝ) :
    ∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) * Real.exp (θ * j) = (1 + Real.exp θ) ^ m := by
  have h := add_pow (Real.exp θ) 1 m
  rw [add_comm (Real.exp θ) 1] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro j _
  rw [one_pow, mul_one, ← Real.exp_nat_mul, mul_comm (j : ℝ) θ]
  ring

/-- `(1 + e^θ)/2 ≤ exp(θ/2 + θ²/8)`. -/
theorem one_add_exp_div_two_le (θ : ℝ) :
    (1 + Real.exp θ) / 2 ≤ Real.exp (θ / 2 + θ ^ 2 / 8) := by
  have hcosh : Real.cosh (θ / 2) ≤ Real.exp ((θ / 2) ^ 2 / 2) := Real.cosh_le_exp_half_sq _
  have hid : (1 + Real.exp θ) / 2 = Real.exp (θ / 2) * Real.cosh (θ / 2) := by
    rw [Real.cosh_eq]
    have : Real.exp θ = Real.exp (θ / 2) * Real.exp (θ / 2) := by
      rw [← Real.exp_add]; ring_nf
    have h2 : Real.exp (θ / 2) * Real.exp (-(θ / 2)) = 1 := by
      rw [← Real.exp_add]; simp
    nlinarith [h2, this]
  rw [hid]
  calc Real.exp (θ / 2) * Real.cosh (θ / 2)
      ≤ Real.exp (θ / 2) * Real.exp ((θ / 2) ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left hcosh (Real.exp_pos _).le
    _ = Real.exp (θ / 2 + θ ^ 2 / 8) := by rw [← Real.exp_add]; ring_nf

/-- Chernoff bound for the symmetric binomial upper tail. -/
theorem binTail_le_exp (m k : ℕ) {θ : ℝ} (hθ : 0 ≤ θ) :
    binTail m k ≤ Real.exp (-θ * (k - m / 2) + m * θ ^ 2 / 8) := by
  have h1 : binTail m k ≤ ∑ j ∈ Finset.Ico k (m + 1), binPMF m j * Real.exp (θ * (j - k)) := by
    apply Finset.sum_le_sum
    intro j hj
    have hjk : (k : ℝ) ≤ j := by exact_mod_cast (Finset.mem_Ico.mp hj).1
    have : 1 ≤ Real.exp (θ * (j - k)) := by
      rw [Real.one_le_exp_iff]; exact mul_nonneg hθ (by linarith)
    exact le_mul_of_one_le_right (binPMF_nonneg m j) this
  have h2 : ∑ j ∈ Finset.Ico k (m + 1), binPMF m j * Real.exp (θ * (j - k)) ≤
      ∑ j ∈ Finset.range (m + 1), binPMF m j * Real.exp (θ * (j - k)) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro j hj
      rw [Finset.mem_range]; exact (Finset.mem_Ico.mp hj).2
    · intro j _ _
      exact mul_nonneg (binPMF_nonneg m j) (Real.exp_pos _).le
  have h3 : ∑ j ∈ Finset.range (m + 1), binPMF m j * Real.exp (θ * (j - k)) =
      Real.exp (-θ * k) * ((1 + Real.exp θ) / 2) ^ m := by
    rw [div_pow, ← sum_choose_mul_exp m θ, Finset.sum_div, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    unfold binPMF
    have : Real.exp (θ * (j - k)) = Real.exp (θ * j) * Real.exp (-θ * k) := by
      rw [← Real.exp_add]; ring_nf
    rw [this]; ring
  have h4 : ((1 + Real.exp θ) / 2) ^ m ≤ Real.exp (θ / 2 + θ ^ 2 / 8) ^ m :=
    pow_le_pow_left₀ (by positivity) (one_add_exp_div_two_le θ) m
  calc binTail m k ≤ Real.exp (-θ * k) * ((1 + Real.exp θ) / 2) ^ m := by
        rw [← h3]; exact h1.trans h2
    _ ≤ Real.exp (-θ * k) * Real.exp (θ / 2 + θ ^ 2 / 8) ^ m :=
        mul_le_mul_of_nonneg_left h4 (Real.exp_pos _).le
    _ = Real.exp (-θ * (k - m / 2) + m * θ ^ 2 / 8) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]; ring_nf

/-- Chernoff at the optimal parameter: for `k ≥ m/2`, `P(Bin(m,½) ≥ k) ≤ exp(−(2k − m)²/(2m))`,
i.e. `exp(−y²/2)` with `y = (2k − m)/√m`. -/
theorem binTail_le_exp_neg_sq {m k : ℕ} (hm : 0 < m) (hk : (m : ℝ) / 2 ≤ k) :
    binTail m k ≤ Real.exp (-((2 * k - m : ℝ) ^ 2 / (2 * m))) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hθ : 0 ≤ (4 * k - 2 * m : ℝ) / m := by
    apply div_nonneg _ hmR.le; linarith
  refine (binTail_le_exp m k hθ).trans (le_of_eq ?_)
  congr 1
  field_simp
  ring

end Ripple.Kurtz.StrongApprox
