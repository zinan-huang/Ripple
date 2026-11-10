import Ripple.Number.Modular.R5Data
import Ripple.Number.Modular.ModularPoly41

/-!
# `T₀` is the only root of `Ψ₂₉(X, X)` in `[1.1·10¹⁰, ∞)`

From the kernel check `r5Check_eq_true`: `Ψ₂₉(a + h, a + h) = (h − b) · D(h)` with
`D(h) = Σ d_k h^k`, all `d_k ≤ 0`, `d_0 < 0`, so `D(h) < 0` for `h ≥ 0`
(`psi29_diag_eq_T0`).
-/

namespace Ripple.Number.Modular

open Finset

theorem factN_eq (n : ℕ) : factN n = n.factorial := by
  induction n with
  | zero => rfl
  | succ n ih => simp [factN, Nat.factorial, ih]

theorem chooseN_eq (n k : ℕ) : chooseN n k = n.choose k := by
  unfold chooseN
  split_ifs with h
  · rw [factN_eq, factN_eq, factN_eq, Nat.choose_eq_factorial_div_factorial h]
  · rw [Nat.choose_eq_zero_of_lt (by omega)]

theorem pow_shift (x a : ℂ) {n : ℕ} (hn : n ≤ 60) :
    x ^ n = ∑ k ∈ range 61, ((n.choose k : ℕ) : ℂ) * a ^ (n - k) * (x - a) ^ k := by
  have hsub : range (n + 1) ⊆ range 61 := range_subset_range.mpr (by omega)
  calc x ^ n = ∑ k ∈ range (n + 1), (x - a) ^ k * a ^ (n - k) * (n.choose k : ℂ) := by
        rw [← add_pow, sub_add_cancel]
    _ = ∑ k ∈ range 61, (x - a) ^ k * a ^ (n - k) * (n.choose k : ℂ) := by
        refine sum_subset hsub fun k _ hk => ?_
        rw [mem_range, not_lt] at hk
        simp [Nat.choose_eq_zero_of_lt (show n < k by omega)]
    _ = _ := sum_congr rfl fun k _ => by ring

/-- The shifted diagonal of a sparse bivariate polynomial of total degree at most `60`. -/
theorem evalDiag_shift (terms : List SparseBivarTerm)
    (hdeg : ∀ t ∈ terms, t.xPow + t.yPow ≤ 60) (x : ℂ) (a : ℤ) :
    evalSparseBivarC terms x x = ∑ k ∈ range 61,
      (((terms.map fun t => t.coeff * (chooseN (t.xPow + t.yPow) k : ℤ) *
        a ^ (t.xPow + t.yPow - k)).sum : ℤ) : ℂ) * (x - a) ^ k := by
  induction terms with
  | nil => simp [evalSparseBivarC]
  | cons t ts ih =>
    rw [evalSparseBivarC, ih (fun s hs => hdeg s (List.mem_cons_of_mem _ hs))]
    simp only [List.map_cons, List.sum_cons, Int.cast_add, add_mul, sum_add_distrib]
    congr 1
    have hx : (t.coeff : ℂ) * x ^ t.xPow * x ^ t.yPow = t.coeff * x ^ (t.xPow + t.yPow) := by
      ring
    rw [hx, pow_shift x (a : ℂ) (hdeg t List.mem_cons_self), mul_sum]
    refine sum_congr rfl fun k _ => ?_
    push_cast [chooseN_eq]
    ring

theorem r5Delta_getD {k : ℕ} (hk : k < 61) : r5DeltaL.getD k 0 = r5Delta k := by
  simp [r5DeltaL, List.getD_eq_getElem?_getD, hk]

theorem r5Cof_nonpos (k : ℕ) : r5Cof.getD k 0 ≤ 0 := by
  have hc := r5Check_eq_true
  simp only [r5Check, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hc
  rw [List.getD_eq_getElem?_getD]
  cases h : r5Cof[k]? with
  | none => simp
  | some v => exact hc.1.2 v (List.mem_of_getElem? h)

theorem r5Cof_zero_neg : r5Cof.getD 0 0 < 0 := by
  have hc := r5Check_eq_true
  simp only [r5Check, Bool.and_eq_true, decide_eq_true_eq] at hc
  exact hc.2

theorem r5Cof_getD_60 : r5Cof.getD 60 0 = 0 := by
  have hc := r5Check_eq_true
  simp only [r5Check, Bool.and_eq_true, beq_iff_eq] at hc
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [hc.1.1.1]; omega)]
  rfl

theorem r5Delta_eq {k : ℕ} (hk : k < 61) :
    r5Delta k = (if k = 0 then 0 else r5Cof.getD (k - 1) 0) - r5B * r5Cof.getD k 0 := by
  have hc := r5Check_eq_true
  simp only [r5Check, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at hc
  rw [← r5Delta_getD hk]
  exact hc.1.1.2 k hk

theorem factor_generic (d : ℕ → ℂ) (B h : ℂ) (h60 : d 60 = 0) :
    ∑ k ∈ range 61, ((if k = 0 then 0 else d (k - 1)) - B * d k) * h ^ k =
      (h - B) * ∑ k ∈ range 60, d k * h ^ k := by
  have e1 : ∑ k ∈ range 61, (if k = 0 then 0 else d (k - 1)) * h ^ k =
      h * ∑ k ∈ range 60, d k * h ^ k := by
    rw [sum_range_succ', mul_sum]
    simp only [Nat.add_one_ne_zero, ↓reduceIte, add_tsub_cancel_right, zero_mul, add_zero]
    exact sum_congr rfl fun k _ => by ring
  have e2 : ∑ k ∈ range 61, d k * h ^ k = ∑ k ∈ range 60, d k * h ^ k := by
    rw [sum_range_succ, h60, zero_mul, add_zero]
  have e3 : ∑ k ∈ range 61, ((if k = 0 then 0 else d (k - 1)) - B * d k) * h ^ k =
      ∑ k ∈ range 61, (if k = 0 then 0 else d (k - 1)) * h ^ k -
        B * ∑ k ∈ range 61, d k * h ^ k := by
    rw [mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun k _ => by ring
  rw [e3, e1, e2]
  ring

/-- `Σ δ_k h^k = (h − b) Σ_{k<60} d_k h^k`. -/
theorem r5_factor (h : ℂ) :
    ∑ k ∈ range 61, (r5Delta k : ℂ) * h ^ k =
      (h - r5B) * ∑ k ∈ range 60, (r5Cof.getD k 0 : ℂ) * h ^ k := by
  have e : ∑ k ∈ range 61, (r5Delta k : ℂ) * h ^ k =
      ∑ k ∈ range 61, ((if k = 0 then 0 else (r5Cof.getD (k - 1) 0 : ℂ)) -
        (r5B : ℂ) * (r5Cof.getD k 0 : ℂ)) * h ^ k := by
    refine sum_congr rfl fun k hk => ?_
    rw [r5Delta_eq (mem_range.mp hk)]
    split_ifs <;> push_cast <;> ring
  rw [e]
  refine factor_generic (fun k => (r5Cof.getD k 0 : ℂ)) _ h ?_
  change (r5Cof.getD 60 0 : ℂ) = 0
  rw [r5Cof_getD_60, Int.cast_zero]

theorem r5_cof_neg {s : ℝ} (hs : 0 ≤ s) :
    ∑ k ∈ range 60, (r5Cof.getD k 0 : ℝ) * s ^ k < 0 := by
  rw [sum_range_succ']
  have h1 : ∑ k ∈ range 59, (r5Cof.getD (k + 1) 0 : ℝ) * s ^ (k + 1) ≤ 0 :=
    sum_nonpos fun k _ => mul_nonpos_of_nonpos_of_nonneg (by exact_mod_cast r5Cof_nonpos _)
      (pow_nonneg hs _)
  have h2 : (r5Cof.getD 0 0 : ℝ) < 0 := by exact_mod_cast r5Cof_zero_neg
  simp only [pow_zero, mul_one]
  linarith

/-- **R5, algebraic half.** A real root `x ≥ 1.1·10¹⁰` of `Ψ₂₉(X, X)` is `T₀ = 256·99⁴ − 104`. -/
theorem psi29_diag_eq_T0 {r : ℝ} (hr : (11000000000 : ℝ) ≤ r)
    (h : evalSparseBivarC psi29SparseTerms (r : ℂ) (r : ℂ) = 0) :
    r = 256 * 99 ^ 4 - 104 := by
  have hdeg : ∀ t ∈ psi29SparseTerms, t.xPow + t.yPow ≤ 60 := by
    have := psi29SparseTerms_diag_le_60
    simpa [List.all_eq_true] using this
  rw [evalDiag_shift _ hdeg _ r5A] at h
  change ∑ k ∈ range 61, (r5Delta k : ℂ) * ((r : ℂ) - (r5A : ℂ)) ^ k = 0 at h
  rw [r5_factor] at h
  have hA : (r5A : ℝ) = 11000000000 := by norm_num [r5A]
  have hneg := r5_cof_neg (s := r - r5A) (by rw [hA]; linarith)
  have hD : ∑ k ∈ range 60, (r5Cof.getD k 0 : ℂ) * ((r : ℂ) - (r5A : ℂ)) ^ k ≠ 0 := by
    have : ∑ k ∈ range 60, (r5Cof.getD k 0 : ℂ) * ((r : ℂ) - (r5A : ℂ)) ^ k =
        ((∑ k ∈ range 60, (r5Cof.getD k 0 : ℝ) * (r - r5A) ^ k : ℝ) : ℂ) := by
      rw [Complex.ofReal_sum]
      refine sum_congr rfl fun k _ => ?_
      push_cast
      ring
    rw [this]
    exact_mod_cast hneg.ne
  have h1 := (mul_eq_zero.mp h).resolve_right hD
  have h2 : (r : ℂ) = (r5A : ℂ) + (r5B : ℂ) := by linear_combination h1
  have h3 : r = (r5A : ℝ) + (r5B : ℝ) := by exact_mod_cast h2
  rw [h3]
  norm_num [r5A, r5B, r5T0]

end Ripple.Number.Modular
