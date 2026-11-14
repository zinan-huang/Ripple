/-
  Ripple.Kurtz.StrongApprox.BinomialCdfDeriv — the binomial cdf as a function of `p`

  Mathematics: first ingredient of the Serov–Zubkov signed-root intersection.

  `binTermP m j p = C(m,j) p^j (1−p)^{m−j}`, `binCdf m k p = Σ_{j<k} binTermP m j p =
  P(Bin(m,p) ≤ k−1)`.  The finite sum telescopes under differentiation:
  `d/dp P(Bin(n+1,p) ≤ k) = −(n+1) C(n,k) p^k (1−p)^{n−k}`.  Values at `p = 0, 1`, the total mass,
  and the complement identity `P(Bin(m,p) ≤ k) + P(Bin(m,1−p) ≤ m−k−1) = 1`.
-/

import Mathlib

namespace Ripple.Kurtz.StrongApprox

open Finset

/-- Binomial point mass `C(m,j) p^j (1−p)^{m−j}` as a function of `p`. -/
noncomputable def binTermP (m j : ℕ) (p : ℝ) : ℝ := (m.choose j : ℝ) * p ^ j * (1 - p) ^ (m - j)

/-- `P(Bin(m,p) ≤ k − 1) = Σ_{j < k} binTermP m j p`. -/
noncomputable def binCdf (m k : ℕ) (p : ℝ) : ℝ := ∑ j ∈ Finset.range k, binTermP m j p

theorem binTermP_nonneg (m j : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : 0 ≤ binTermP m j p := by
  unfold binTermP
  have : 0 ≤ 1 - p := by linarith
  positivity

theorem binCdf_nonneg (m k : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : 0 ≤ binCdf m k p :=
  Finset.sum_nonneg fun j _ => binTermP_nonneg m j hp0 hp1

theorem continuous_binTermP (m j : ℕ) : Continuous (binTermP m j) := by
  unfold binTermP; fun_prop

theorem continuous_binCdf (m k : ℕ) : Continuous (binCdf m k) := by
  unfold binCdf
  exact continuous_finset_sum _ fun j _ => continuous_binTermP m j

theorem binCdf_succ (m k : ℕ) (p : ℝ) : binCdf m (k + 1) p = binCdf m k p + binTermP m k p := by
  simp [binCdf, Finset.sum_range_succ]

theorem binCdf_mono (m : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : Monotone (fun k => binCdf m k p) := by
  apply monotone_nat_of_le_succ
  intro k
  rw [binCdf_succ]
  linarith [binTermP_nonneg m k hp0 hp1]

/-! ### Derivatives -/

theorem hasDerivAt_binTermP_zero (n : ℕ) (p : ℝ) :
    HasDerivAt (binTermP (n + 1) 0) (-(((n + 1 : ℕ) : ℝ) * binTermP n 0 p)) p := by
  have h2 : HasDerivAt (fun x : ℝ => 1 - x) (-1) p := (hasDerivAt_id p).const_sub 1
  have h := (hasDerivAt_pow (n + 1) (1 - p)).comp p h2
  have hfun : binTermP (n + 1) 0 = fun x : ℝ => (1 - x) ^ (n + 1) := by
    funext x; simp [binTermP]
  rw [hfun]
  refine h.congr_deriv ?_
  simp [binTermP]

theorem hasDerivAt_binTermP_succ (n j : ℕ) (p : ℝ) :
    HasDerivAt (binTermP (n + 1) (j + 1))
      (((n + 1 : ℕ) : ℝ) * (binTermP n j p - binTermP n (j + 1) p)) p := by
  have h2 : HasDerivAt (fun x : ℝ => 1 - x) (-1) p := (hasDerivAt_id p).const_sub 1
  have hpow : HasDerivAt (fun x : ℝ => (1 - x) ^ (n - j))
      (((n - j : ℕ) : ℝ) * (1 - p) ^ (n - j - 1) * (-1)) p :=
    (hasDerivAt_pow (n - j) (1 - p)).comp p h2
  have h := ((hasDerivAt_pow (j + 1) p).mul hpow).const_mul ((n + 1).choose (j + 1) : ℝ)
  have hfun : binTermP (n + 1) (j + 1) =
      fun x : ℝ => ((n + 1).choose (j + 1) : ℝ) * (x ^ (j + 1) * (1 - x) ^ (n - j)) := by
    funext x
    simp only [binTermP, Nat.add_sub_add_right]
    ring
  rw [hfun]
  refine h.congr_deriv ?_
  -- binomial-coefficient identities, cast to `ℝ`
  have h1 : ((n + 1 : ℕ) : ℝ) * (n.choose j : ℝ) = ((n + 1).choose (j + 1) : ℝ) * ((j + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_mul_choose_eq n j
  have h2' : (n.choose (j + 1) : ℝ) * ((j + 1 : ℕ) : ℝ) = (n.choose j : ℝ) * ((n - j : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_succ_right_eq n j
  have hj1 : ((j + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have h3 : ((n + 1).choose (j + 1) : ℝ) * ((n - j : ℕ) : ℝ) =
      ((n + 1 : ℕ) : ℝ) * (n.choose (j + 1) : ℝ) := by
    apply mul_right_cancel₀ hj1
    linear_combination (-(((n - j : ℕ) : ℝ))) * h1 - ((n + 1 : ℕ) : ℝ) * h2'
  simp only [binTermP, Nat.add_sub_cancel, Nat.sub_sub]
  push_cast at h1 h3 ⊢
  linear_combination (-(p ^ j * (1 - p) ^ (n - j))) * h1 -
    (p ^ (j + 1) * (1 - p) ^ (n - (j + 1))) * h3

/-- `d/dp P(Bin(n+1,p) ≤ k) = −(n+1) C(n,k) p^k (1−p)^{n−k}` (for `k > n` both sides vanish). -/
theorem hasDerivAt_binCdf (n k : ℕ) (p : ℝ) :
    HasDerivAt (binCdf (n + 1) (k + 1)) (-(((n + 1 : ℕ) : ℝ) * binTermP n k p)) p := by
  induction k with
  | zero =>
    have : binCdf (n + 1) 1 = binTermP (n + 1) 0 := by funext x; simp [binCdf]
    rw [this]
    exact hasDerivAt_binTermP_zero n p
  | succ k ih =>
    have hfun : binCdf (n + 1) (k + 2) = fun x => binCdf (n + 1) (k + 1) x + binTermP (n + 1) (k + 1) x := by
      funext x; simp [binCdf, Finset.sum_range_succ]
    rw [hfun]
    have := ih.add (hasDerivAt_binTermP_succ n k p)
    refine this.congr_deriv ?_
    ring

/-! ### Values at the ends -/

theorem binTermP_zero_left (m : ℕ) : binTermP m 0 0 = 1 := by simp [binTermP]

theorem binTermP_succ_left (m j : ℕ) : binTermP m (j + 1) 0 = 0 := by simp [binTermP]

theorem binTermP_right (m j : ℕ) (hj : j < m) : binTermP m j 1 = 0 := by
  unfold binTermP
  have : 0 < m - j := by omega
  rw [sub_self, zero_pow this.ne']
  ring

/-- `P(Bin(m,0) ≤ k−1) = 1` for `k ≥ 1`. -/
theorem binCdf_zero_left (m k : ℕ) (hk : 1 ≤ k) : binCdf m k 0 = 1 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  unfold binCdf
  rw [Finset.sum_range_succ']
  rw [binTermP_zero_left]
  simp [binTermP_succ_left]

/-- `P(Bin(m,1) ≤ k−1) = 0` for `k ≤ m`. -/
theorem binCdf_right (m k : ℕ) (hk : k ≤ m) : binCdf m k 1 = 0 := by
  unfold binCdf
  apply Finset.sum_eq_zero
  intro j hj
  rw [Finset.mem_range] at hj
  exact binTermP_right m j (by omega)

/-! ### Total mass and the complement identity -/

/-- `Σ_{j ≤ m} C(m,j) p^j (1−p)^{m−j} = 1`. -/
theorem binCdf_total (m : ℕ) (p : ℝ) : binCdf m (m + 1) p = 1 := by
  unfold binCdf
  calc ∑ j ∈ Finset.range (m + 1), binTermP m j p
      = ∑ j ∈ Finset.range (m + 1), p ^ j * (1 - p) ^ (m - j) * (m.choose j : ℝ) :=
        Finset.sum_congr rfl (fun j _ => by unfold binTermP; ring)
    _ = (p + (1 - p)) ^ m := (add_pow p (1 - p) m).symm
    _ = 1 := by rw [add_sub_cancel, one_pow]

theorem binTermP_reflect (m i : ℕ) (hi : i ≤ m) (p : ℝ) :
    binTermP m (m - i) p = binTermP m i (1 - p) := by
  unfold binTermP
  rw [Nat.choose_symm hi, Nat.sub_sub_self hi, sub_sub_cancel]
  ring

/-- `P(Bin(m,p) ≤ k) + P(Bin(m,1−p) ≤ m−k−1) = 1` for `k ≤ m`. -/
theorem binCdf_add_binCdf_compl (m k : ℕ) (hk : k ≤ m) (p : ℝ) :
    binCdf m (k + 1) p + binCdf m (m - k) (1 - p) = 1 := by
  have hsplit : binCdf m (m + 1) p =
      binCdf m (k + 1) p + ∑ j ∈ Finset.Ico (k + 1) (m + 1), binTermP m j p := by
    unfold binCdf
    rw [Finset.sum_range_add_sum_Ico _ (show k + 1 ≤ m + 1 by omega)]
  have hrest : ∑ j ∈ Finset.Ico (k + 1) (m + 1), binTermP m j p = binCdf m (m - k) (1 - p) := by
    rw [Finset.sum_Ico_eq_sum_range]
    have hlen : m + 1 - (k + 1) = m - k := by omega
    rw [hlen]
    unfold binCdf
    refine (Finset.sum_range_reflect (fun i => binTermP m (k + 1 + i) p) (m - k)).symm.trans ?_
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    show binTermP m (k + 1 + (m - k - 1 - i)) p = _
    rw [← binTermP_reflect m i (by omega)]
    congr 1
    omega
  rw [← hrest, ← hsplit, binCdf_total]

end Ripple.Kurtz.StrongApprox
