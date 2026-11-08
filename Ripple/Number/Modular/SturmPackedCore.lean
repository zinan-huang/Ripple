import Ripple.Number.Modular.ModularPolynomialQExpansion
import Ripple.Number.Modular.ModularPoly41
import Ripple.Number.Modular.SturmPackedNat
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.ZMod.Basic

/-!
# Kronecker packing of truncated integer power series

For a commutative ring `R` and `x : R` with `x ^ N = 0`, evaluating the degree `< N` truncation
of an integer power series at `x` is a ring homomorphism `PowerSeries ℤ →+* R` (`packHom`).
With `R = ZMod (2 ^ (s * N))` and `x = 2 ^ s`, a truncated series becomes one natural number with
`N` slots of `s` bits, and every ring operation on truncated series becomes one big-integer
operation. If the true coefficients are below `2 ^ s` in absolute value, a packed value `0`
forces every coefficient to vanish (`coeff_eq_zero_of_packEval_eq_zero`).
-/

namespace Ripple.Number.Modular

open Finset

section Pack

variable {R : Type*} [CommRing R]

/-- Evaluate the degree `< N` truncation of an integer power series at `x`. -/
noncomputable def packEval (x : R) (N : ℕ) (f : PowerSeries ℤ) : R :=
  (PowerSeries.trunc N f).eval₂ (Int.castRingHom R) x

theorem packEval_eq_sum (x : R) (N : ℕ) (f : PowerSeries ℤ) :
    packEval x N f = ∑ n ∈ range N, ((PowerSeries.coeff n f : ℤ) : R) * x ^ n := by
  rw [packEval, PowerSeries.eval₂_trunc_eq_sum_range]
  rfl

theorem pow_eq_zero_of_le_of_pow_eq_zero {x : R} {N i : ℕ} (hx : x ^ N = 0) (hi : N ≤ i) :
    x ^ i = 0 := by
  rw [← Nat.add_sub_cancel' hi, pow_add, hx, zero_mul]

theorem packEval_eq_sum_of_le {x : R} {N : ℕ} (hx : x ^ N = 0) (f : PowerSeries ℤ) {K : ℕ}
    (hK : N ≤ K) :
    packEval x N f = ∑ n ∈ range K, ((PowerSeries.coeff n f : ℤ) : R) * x ^ n := by
  have h0 : ∑ n ∈ Ico N K, ((PowerSeries.coeff n f : ℤ) : R) * x ^ n = 0 :=
    Finset.sum_eq_zero fun n hn => by
      rw [pow_eq_zero_of_le_of_pow_eq_zero hx (mem_Ico.mp hn).1, mul_zero]
  rw [packEval_eq_sum, ← Finset.sum_range_add_sum_Ico _ hK, h0, add_zero]

theorem packEval_congr {x : R} {N : ℕ} {f g : PowerSeries ℤ}
    (h : ∀ n < N, PowerSeries.coeff n f = PowerSeries.coeff n g) :
    packEval x N f = packEval x N g := by
  rw [packEval_eq_sum, packEval_eq_sum]
  exact sum_congr rfl fun n hn => by rw [h n (mem_range.mp hn)]

theorem eval₂_trunc_coe_of_pow_eq_zero {x : R} {N : ℕ} (hx : x ^ N = 0) (p : Polynomial ℤ) :
    (PowerSeries.trunc N (p : PowerSeries ℤ)).eval₂ (Int.castRingHom R) x =
      p.eval₂ (Int.castRingHom R) x := by
  have h := packEval_eq_sum_of_le hx (p : PowerSeries ℤ) (le_max_left N (p.natDegree + 1))
  rw [packEval] at h
  rw [h, Polynomial.eval₂_eq_sum_range' _
    (show p.natDegree < max N (p.natDegree + 1) by omega)]
  refine sum_congr rfl fun n _ => ?_
  rw [Polynomial.coeff_coe]
  rfl

/-- Truncated evaluation at a nilpotent `x` with `x ^ N = 0`, as a ring homomorphism. -/
noncomputable def packHom (x : R) (N : ℕ) (hx : x ^ N = 0) : PowerSeries ℤ →+* R where
  toFun := packEval x N
  map_zero' := by simp [packEval_eq_sum]
  map_add' f g := by
    simp only [packEval_eq_sum, map_add, Int.cast_add, add_mul, Finset.sum_add_distrib]
  map_one' := by
    rcases N with _ | N
    · rw [pow_zero] at hx
      haveI : Subsingleton R := subsingleton_of_zero_eq_one hx.symm
      exact Subsingleton.elim _ _
    · rw [packEval_eq_sum, Finset.sum_range_succ']
      simp [PowerSeries.coeff_one]
  map_mul' f g := by
    change (PowerSeries.trunc N (f * g)).eval₂ (Int.castRingHom R) x =
      (PowerSeries.trunc N f).eval₂ (Int.castRingHom R) x *
        (PowerSeries.trunc N g).eval₂ (Int.castRingHom R) x
    rw [← PowerSeries.trunc_trunc_mul_trunc, ← Polynomial.coe_mul,
      eval₂_trunc_coe_of_pow_eq_zero hx, Polynomial.eval₂_mul]

@[simp] theorem packHom_apply (x : R) (N : ℕ) (hx : x ^ N = 0) (f : PowerSeries ℤ) :
    packHom x N hx f = packEval x N f := rfl

/-- Substituting `q ↦ q ^ 41` corresponds to packing at `x ^ 41` with `K ≥ N / 41` slots. -/
theorem packEval_qPullback41Z {x : R} {N K : ℕ} (hx : x ^ N = 0) (hK : N ≤ 41 * K)
    (f : PowerSeries ℤ) :
    packEval x N (qPullback41Z f) = packEval (x ^ 41) K f := by
  rw [packEval_eq_sum_of_le hx _ hK, packEval_eq_sum]
  clear hK
  induction K with
  | zero => simp
  | succ K ih =>
    rw [show 41 * (K + 1) = 41 * K + 41 by ring, Finset.sum_range_add, ih,
      Finset.sum_range_succ _ K]
    congr 1
    rw [Finset.sum_eq_single 0]
    · rw [add_zero, coeff_qPullback41Z, if_pos (dvd_mul_right 41 K),
        Nat.mul_div_cancel_left K (by norm_num : 0 < 41), ← pow_mul]
    · intro i hi hi0
      have hnd : ¬ 41 ∣ 41 * K + i := by
        rw [Nat.dvd_add_right (dvd_mul_right 41 K)]
        exact fun h => hi0 (Nat.eq_zero_of_dvd_of_lt h (mem_range.mp hi))
      rw [coeff_qPullback41Z, if_neg hnd, Int.cast_zero, zero_mul]
    · intro h
      exact absurd (mem_range.mpr (by norm_num)) h

/-- Packed `E₄³`. -/
theorem packEval_E4ZSeries_cube {y : R} {N : ℕ} (hy : y ^ N = 0) :
    packEval y N (E4ZSeries ^ 3) = packEval y N E4ZSeries ^ 3 := by
  rw [← packHom_apply y N hy, map_pow, packHom_apply]

end Pack

/-! ### Balanced digits -/

theorem eq_zero_of_two_pow_dvd_packed {s : ℕ} :
    ∀ (N : ℕ) (c : ℕ → ℤ), (∀ n < N, |c n| < 2 ^ s) →
      ((2 : ℤ) ^ (s * N)) ∣ ∑ n ∈ range N, c n * 2 ^ (s * n) → ∀ n < N, c n = 0
  | 0, _, _, _ => fun n hn => absurd hn (Nat.not_lt_zero _)
  | N + 1, c, hc, hdvd => by
    have hsplit : ∑ n ∈ range (N + 1), c n * 2 ^ (s * n) =
        c 0 + 2 ^ s * ∑ n ∈ range N, c (n + 1) * 2 ^ (s * n) := by
      rw [Finset.sum_range_succ', Finset.mul_sum, add_comm]
      simp only [mul_zero, pow_zero, mul_one]
      congr 1
      refine sum_congr rfl fun n _ => ?_
      rw [mul_add, mul_one, pow_add]
      ring
    rw [hsplit] at hdvd
    have hs : (2 : ℤ) ^ s ∣ (2 : ℤ) ^ (s * (N + 1)) :=
      pow_dvd_pow 2 (Nat.le_mul_of_pos_right s (Nat.succ_pos N))
    have hc0 : c 0 = 0 := by
      have h1 : (2 : ℤ) ^ s ∣ c 0 := by
        have := dvd_sub (hs.trans hdvd) (dvd_mul_right ((2 : ℤ) ^ s)
          (∑ n ∈ range N, c (n + 1) * 2 ^ (s * n)))
        rwa [add_sub_cancel_right] at this
      exact Int.eq_zero_of_abs_lt_dvd h1 (hc 0 (Nat.succ_pos N))
    rw [hc0, zero_add, show s * (N + 1) = s + s * N by ring, pow_add] at hdvd
    have htail := (mul_dvd_mul_iff_left (pow_ne_zero s (by norm_num : (2 : ℤ) ≠ 0))).mp hdvd
    have ih := eq_zero_of_two_pow_dvd_packed N (fun n => c (n + 1))
      (fun n hn => hc (n + 1) (by omega)) htail
    intro n hn
    rcases n with _ | n
    · exact hc0
    · exact ih n (by omega)

/-- If the packed value of a series in `ZMod (2 ^ (s * N))` at `x = 2 ^ s` vanishes and its first
`N` coefficients are below `2 ^ s` in absolute value, those coefficients vanish. -/
theorem coeff_eq_zero_of_packEval_eq_zero {s N M : ℕ} (hM : M = 2 ^ (s * N))
    {f : PowerSeries ℤ}
    (hbound : ∀ n < N, |PowerSeries.coeff n f| < 2 ^ s)
    (hzero : packEval ((2 : ZMod M) ^ s) N f = 0) :
    ∀ n < N, PowerSeries.coeff n f = 0 := by
  subst hM
  rw [packEval_eq_sum] at hzero
  have hcast : (((∑ n ∈ range N, PowerSeries.coeff n f * 2 ^ (s * n) : ℤ)) :
      ZMod (2 ^ (s * N))) = 0 := by
    rw [← hzero]
    push_cast
    refine sum_congr rfl fun n _ => ?_
    ring
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hcast
  push_cast at hcast
  exact eq_zero_of_two_pow_dvd_packed N (fun n => PowerSeries.coeff n f) hbound hcast

/-- Scaled form with one spare slot: if `1728 ^ 84` times the packed value in
`ZMod (2 ^ (s * N'))`, `N' = N + 1`, vanishes, `504 ≤ s`, and the first `N` coefficients are below
`2 ^ s` in absolute value, those coefficients vanish. -/
theorem coeff_eq_zero_of_scaled_packEval_eq_zero {s N N' M : ℕ} (hM : M = 2 ^ (s * N'))
    (hN : N' = N + 1) (hs : 504 ≤ s) {f : PowerSeries ℤ}
    (hbound : ∀ n < N, |PowerSeries.coeff n f| < 2 ^ s)
    (hzero : (1728 : ZMod M) ^ 84 * packEval ((2 : ZMod M) ^ s) N' f = 0) :
    ∀ n < N, PowerSeries.coeff n f = 0 := by
  subst hN
  subst hM
  rw [packEval_eq_sum] at hzero
  have hcast : ((((1728 : ℤ) ^ 84 *
      ∑ n ∈ range (N + 1), PowerSeries.coeff n f * 2 ^ (s * n) : ℤ)) :
      ZMod (2 ^ (s * (N + 1)))) = 0 := by
    rw [← hzero, Int.cast_mul, Int.cast_pow, Int.cast_sum, Int.cast_ofNat]
    congr 1
    refine sum_congr rfl fun n _ => ?_
    push_cast
    ring
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd, Nat.cast_pow, Nat.cast_ofNat,
    show (1728 : ℤ) ^ 84 = 2 ^ 504 * 27 ^ 84 by
      rw [show (1728 : ℤ) = 2 ^ 6 * 27 by norm_num, mul_pow, ← pow_mul],
    mul_assoc] at hcast
  have hle : 504 + s * N ≤ s * (N + 1) := by
    rw [mul_add, mul_one, add_comm (s * N)]
    exact Nat.add_le_add_right hs _
  have h1 : (2 : ℤ) ^ 504 * 2 ^ (s * N) ∣
      2 ^ 504 * (27 ^ 84 * ∑ n ∈ range (N + 1), PowerSeries.coeff n f * 2 ^ (s * n)) := by
    have h0 : (2 : ℤ) ^ 504 * 2 ^ (s * N) ∣ 2 ^ (s * (N + 1)) := by
      rw [← pow_add]
      exact pow_dvd_pow 2 hle
    exact h0.trans hcast
  have h2 := (mul_dvd_mul_iff_left (pow_ne_zero 504 (by norm_num : (2 : ℤ) ≠ 0))).mp h1
  have hcop : IsCoprime ((2 : ℤ) ^ (s * N)) ((27 : ℤ) ^ 84) :=
    IsCoprime.pow ⟨-13, 1, by norm_num⟩
  have h3 := hcop.dvd_of_dvd_mul_left h2
  rw [Finset.sum_range_succ] at h3
  have h4 : (2 : ℤ) ^ (s * N) ∣ ∑ n ∈ range N, PowerSeries.coeff n f * 2 ^ (s * n) := by
    have := dvd_sub h3 (dvd_mul_left ((2 : ℤ) ^ (s * N)) (PowerSeries.coeff N f))
    rwa [add_sub_cancel_right] at this
  exact eq_zero_of_two_pow_dvd_packed N (fun n => PowerSeries.coeff n f) hbound h4

/-! ### Evaluation helpers that the kernel runs -/

theorem treeSum_eq (f : ℕ → ℕ) : ∀ (fuel lo len : ℕ), len ≤ 2 ^ fuel →
    treeSum f fuel lo len = ∑ i ∈ range len, f (lo + i)
  | 0, lo, len, h => by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (by simpa using h) with rfl | rfl <;>
      simp [treeSum]
  | k + 1, lo, len, h => by
    by_cases h1 : len ≤ 1
    · rw [treeSum, if_pos h1]
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h1 with rfl | rfl <;> simp
    · have h' : len ≤ 2 ^ k * 2 := by rw [← pow_succ]; exact h
      rw [treeSum, if_neg h1, treeSum_eq f k lo (len / 2) (by omega),
        treeSum_eq f k (lo + len / 2) (len - len / 2) (by omega)]
      conv_rhs => rw [show len = len / 2 + (len - len / 2) by omega, Finset.sum_range_add]
      simp only [add_assoc]

theorem geomF_eq (w : ℕ) : ∀ (fuel K : ℕ), K < 2 ^ fuel →
    geomF w fuel K = ∑ k ∈ range K, (2 ^ w) ^ (k + 1)
  | 0, K, h => by
    have hK : K = 0 := by simpa using h
    subst hK
    simp [geomF]
  | f + 1, K, h => by
    have hh : K / 2 < 2 ^ f := by rw [pow_succ] at h; omega
    have hsplit : ∑ k ∈ range (2 * (K / 2)), (2 ^ w) ^ (k + 1) =
        ∑ k ∈ range (K / 2), (2 ^ w) ^ (k + 1) +
          (∑ k ∈ range (K / 2), (2 ^ w) ^ (k + 1)) * 2 ^ (w * (K / 2)) := by
      rw [two_mul, Finset.sum_range_add, Finset.sum_mul]
      congr 1
      refine sum_congr rfl fun k _ => ?_
      simp only [← pow_mul, ← pow_add]
      congr 1
      ring
    simp only [geomF]
    rw [geomF_eq w f (K / 2) hh]
    split_ifs with hpar
    · conv_rhs => rw [show K = 2 * (K / 2) by omega]
      rw [hsplit, Nat.shiftLeft_eq]
    · conv_rhs => rw [show K = 2 * (K / 2) + 1 by omega, Finset.sum_range_succ, hsplit]
      simp only [Nat.shiftLeft_eq, one_mul]
      rw [← pow_mul, show 2 * (K / 2) + 1 = K by omega]

/-- Lambert form of `Σ_{m<n} σₖ(m) y^m`. -/
theorem sum_sigma_mul_pow (j y n : ℕ) :
    ∑ m ∈ range n, ArithmeticFunction.sigma j m * y ^ m =
      ∑ d ∈ range n, d ^ j * ∑ k ∈ range ((n - 1) / d), y ^ (d * (k + 1)) := by
  simp only [ArithmeticFunction.sigma_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_nbij' (fun p => ⟨p.2, p.1 / p.2 - 1⟩) (fun p => ⟨p.1 * (p.2 + 1), p.1⟩)
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨m, d⟩ h
    simp only [Finset.mem_sigma, mem_range, Nat.mem_divisors] at h ⊢
    obtain ⟨hm, ⟨k, rfl⟩, hm0⟩ := h
    have hd : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; simp at hm0)
    have hk : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at hm0)
    refine ⟨lt_of_le_of_lt (Nat.le_mul_of_pos_right d hk) hm, ?_⟩
    rw [Nat.mul_div_cancel_left k hd]
    have hkd : k * d ≤ n - 1 := by
      have : d * k ≤ n - 1 := Nat.le_sub_one_of_lt hm
      rwa [mul_comm] at this
    have : k ≤ (n - 1) / d := (Nat.le_div_iff_mul_le hd).2 hkd
    omega
  · rintro ⟨d, k⟩ h
    simp only [Finset.mem_sigma, mem_range, Nat.mem_divisors] at h ⊢
    obtain ⟨hd, hk⟩ := h
    have hd0 : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; simp at hk)
    have hk' : k + 1 ≤ (n - 1) / d := hk
    rw [Nat.le_div_iff_mul_le hd0, mul_comm] at hk'
    exact ⟨lt_of_le_of_lt hk' (Nat.sub_lt (by omega) Nat.one_pos),
      dvd_mul_right d (k + 1), Nat.mul_ne_zero hd0.ne' (Nat.succ_ne_zero k)⟩
  · rintro ⟨m, d⟩ h
    simp only [Finset.mem_sigma, mem_range, Nat.mem_divisors] at h
    obtain ⟨hm, ⟨k, rfl⟩, hm0⟩ := h
    have hd : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; simp at hm0)
    have hk : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at hm0)
    simp [Nat.mul_div_cancel_left k hd, Nat.sub_add_cancel hk]
  · rintro ⟨d, k⟩ h
    simp only [Finset.mem_sigma, mem_range] at h
    have hd0 : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; simp at h)
    simp [Nat.mul_div_cancel_left (k + 1) hd0]
  · rintro ⟨m, d⟩ h
    simp only [Finset.mem_sigma, mem_range, Nat.mem_divisors] at h
    obtain ⟨hm, ⟨k, rfl⟩, hm0⟩ := h
    have hd : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; simp at hm0)
    have hk : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at hm0)
    simp [Nat.mul_div_cancel_left k hd, Nat.sub_add_cancel hk]

theorem geomC_eq (a K : ℕ) (h : 0 < a ∨ K = 0) :
    geomC a K = ∑ k ∈ range K, (2 ^ a) ^ (k + 1) := by
  rcases h with ha | rfl
  · have hX : 2 ≤ 2 ^ a :=
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
    rw [geomC, pow_mul, ← Nat.geomSum_eq hX K, Finset.mul_sum]
    refine sum_congr rfl fun k _ => ?_
    ring
  · simp [geomC]

theorem sigmaPack_eq (j w : ℕ) {n : ℕ} (hw : 0 < w) (hfuel : n ≤ 4096) :
    sigmaPack j w n = ∑ m ∈ range n, ArithmeticFunction.sigma j m * 2 ^ (w * m) := by
  have hF : ∀ d ∈ range n, d ^ j * geomC (w * d) ((n - 1) / d) =
      d ^ j * ∑ k ∈ range ((n - 1) / d), (2 ^ w) ^ (d * (k + 1)) := by
    intro d _
    have h : 0 < w * d ∨ (n - 1) / d = 0 := by
      rcases Nat.eq_zero_or_pos d with rfl | hd
      · right
        simp
      · left
        positivity
    rw [geomC_eq (w * d) ((n - 1) / d) h]
    congr 1
    refine sum_congr rfl fun k _ => ?_
    rw [← pow_mul, ← pow_mul, mul_assoc]
  unfold sigmaPack
  rw [treeSum_eq _ 12 0 n (by norm_num; omega)]
  simp only [zero_add]
  rw [sum_congr rfl hF, ← sum_sigma_mul_pow]
  refine sum_congr rfl fun m _ => ?_
  rw [← pow_mul]

/-- `σⱼ(m) ≤ m^(j+1)`. -/
theorem sigma_le_pow_succ_aux (j m : ℕ) : ArithmeticFunction.sigma j m ≤ m ^ (j + 1) := by
  rw [ArithmeticFunction.sigma_apply, pow_succ']
  refine (sum_le_sum fun d hd => Nat.pow_le_pow_left (Nat.divisor_le hd) j).trans ?_
  rw [sum_const, smul_eq_mul]
  exact Nat.mul_le_mul_right _ (Nat.card_divisors_le_self m)

theorem sigma3_lt {m : ℕ} (hm : m ≤ 3529) :
    1 + 240 * ArithmeticFunction.sigma 3 m < 2 ^ 64 := by
  have h1 := (sigma_le_pow_succ_aux 3 m).trans (Nat.pow_le_pow_left hm 4)
  generalize ArithmeticFunction.sigma 3 m = t at h1 ⊢
  norm_num at h1 ⊢
  omega

theorem sigma5_lt {m : ℕ} (hm : m ≤ 3529) : ArithmeticFunction.sigma 5 m < 2 ^ 72 :=
  lt_of_le_of_lt ((sigma_le_pow_succ_aux 5 m).trans (Nat.pow_le_pow_left hm 6)) (by norm_num)

/-- The `m`-th coefficient of `E₄` as a natural number. -/
def e4Digit (m : ℕ) : ℕ := (if m = 0 then 1 else 0) + 240 * ArithmeticFunction.sigma 3 m

theorem e4Digit_lt {m : ℕ} (hm : m ≤ 3529) : e4Digit m < 2 ^ 64 := by
  have h := sigma3_lt hm
  unfold e4Digit
  generalize ArithmeticFunction.sigma 3 m = t at h ⊢
  generalize (2 : ℕ) ^ 64 = B at h ⊢
  split_ifs <;> omega

theorem e4Digit_cast (m : ℕ) : (e4Digit m : ℤ) = E4CoeffZ m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [e4Digit, E4CoeffZ]
  · simp [e4Digit, E4CoeffZ, hm.ne']

theorem e4Pack_eq_sum {w n : ℕ} (hw : 0 < w) (hn : 0 < n) (hfuel : n ≤ 4096) :
    e4Pack w n = ∑ m ∈ range n, e4Digit m * 2 ^ (w * m) := by
  have hite : ∑ m ∈ range n, (if m = 0 then 1 else 0) * 2 ^ (w * m) = 1 := by
    rw [Finset.sum_eq_single 0 (fun b _ hb => by rw [if_neg hb, zero_mul])
      (fun h => absurd (mem_range.mpr hn) h)]
    simp
  simp only [e4Digit, add_mul, Finset.sum_add_distrib, hite, e4Pack, sigmaPack_eq 3 w hw hfuel,
    Finset.mul_sum, mul_assoc]

theorem two_pow_pow_eq_zero {M s N : ℕ} (hM : M = 2 ^ (s * N)) :
    ((2 : ZMod M) ^ s) ^ N = 0 := by
  subst hM
  rw [← pow_mul]
  exact_mod_cast ZMod.natCast_self (2 ^ (s * N))

/-! ### Masked natural-number arithmetic modulo `2 ^ k`

The kernel evaluates these with GMP-backed `Nat` operations; `m` is the mask `2 ^ k - 1`. -/

section MaskCast

variable {k m M : ℕ}

theorem cast_land_mask (hM : M = 2 ^ k) (hm : m = M - 1) (a : ℕ) :
    ((a &&& m : ℕ) : ZMod M) = a := by
  subst hm
  subst hM
  rw [Nat.and_two_pow_sub_one_eq_mod, ZMod.natCast_mod]

theorem cast_mulM (hM : M = 2 ^ k) (hm : m = M - 1) (a b : ℕ) :
    ((mulM m a b : ℕ) : ZMod M) = a * b := by
  rw [mulM, cast_land_mask hM hm, Nat.cast_mul]

theorem cast_addM (hM : M = 2 ^ k) (hm : m = M - 1) (a b : ℕ) :
    ((addM m a b : ℕ) : ZMod M) = a + b := by
  rw [addM, cast_land_mask hM hm, Nat.cast_add]

theorem cast_mask_succ (hM : M = 2 ^ k) (hm : m = M - 1) : ((m + 1 : ℕ) : ZMod M) = 0 := by
  subst hm
  subst hM
  rw [Nat.sub_add_cancel Nat.one_le_two_pow, ZMod.natCast_self]

theorem cast_subM (hM : M = 2 ^ k) (hm : m = M - 1) (a b : ℕ) :
    ((subM m a b : ℕ) : ZMod M) = a - b := by
  have hle : b &&& m ≤ m + 1 := Nat.and_le_right.trans (Nat.le_succ m)
  rw [subM, cast_land_mask hM hm, Nat.cast_add, Nat.cast_sub hle, cast_land_mask hM hm,
    cast_mask_succ hM hm]
  ring

end MaskCast

/-! ### Sparse bivariate evaluation from power tables -/

theorem cast_powTab_getD {k m M : ℕ} (hM : M = 2 ^ k) (hm : m = M - 1) (a : ℕ) :
    ∀ (cur len i : ℕ), i < len →
    (((powTab m a cur len).getD i 0 : ℕ) : ZMod M) = cur * (a : ZMod M) ^ i
  | _, 0, _, h => absurd h (Nat.not_lt_zero _)
  | cur, len + 1, 0, _ => by simp [powTab]
  | cur, len + 1, i + 1, h => by
    rw [powTab, List.getD_cons_succ, cast_powTab_getD hM hm a _ len i (by omega), cast_mulM hM hm]
    ring

theorem getD_map_range (f : ℕ → ℕ) {n y : ℕ} (hy : y < n) :
    ((List.range n).map f).getD y 0 = f y := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hy]
  rfl


/-! ### Spreading narrow slots to wide slots -/

theorem spread_eq (w s v : ℕ) : ∀ (fuel lo len : ℕ), len ≤ 2 ^ fuel →
    spread w s v fuel lo len =
      ∑ i ∈ range len, (v >>> (w * (lo + i))) % 2 ^ w * 2 ^ (s * i)
  | 0, lo, len, h => by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (by simpa using h) with rfl | rfl <;>
      simp [spread]
  | k + 1, lo, len, h => by
    by_cases h1 : len ≤ 1
    · rw [spread, if_pos h1]
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h1 with rfl | rfl <;> simp
    · have h' : len ≤ 2 ^ k * 2 := by rw [← pow_succ]; exact h
      rw [spread, if_neg h1, spread_eq w s v k lo (len / 2) (by omega),
        spread_eq w s v k (lo + len / 2) (len - len / 2) (by omega), Nat.shiftLeft_eq,
        Finset.sum_mul]
      conv_rhs => rw [show len = len / 2 + (len - len / 2) by omega, Finset.sum_range_add]
      congr 1
      refine sum_congr rfl fun i _ => ?_
      rw [add_assoc lo]
      ring

theorem sum_digits_split (w : ℕ) (d : ℕ → ℕ) (n : ℕ) :
    ∑ m ∈ range (n + 1), d m * 2 ^ (w * m) =
      d 0 + 2 ^ w * ∑ m ∈ range n, d (m + 1) * 2 ^ (w * m) := by
  rw [Finset.sum_range_succ', Finset.mul_sum, add_comm]
  simp only [mul_zero, pow_zero, mul_one]
  congr 1
  refine sum_congr rfl fun m _ => ?_
  rw [mul_add, mul_one, pow_add]
  ring

/-- Slot `j` of a packing with `w`-bit digits. -/
theorem digit_of_sum (w : ℕ) :
    ∀ (j n : ℕ) (d : ℕ → ℕ), (∀ m < n, d m < 2 ^ w) → j < n →
    (∑ m ∈ range n, d m * 2 ^ (w * m)) >>> (w * j) % 2 ^ w = d j
  | _, 0, _, _, hj => absurd hj (Nat.not_lt_zero _)
  | 0, n + 1, d, hd, _ => by
    rw [sum_digits_split, mul_zero, Nat.shiftRight_zero, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt (hd 0 (Nat.succ_pos n))]
  | j + 1, n + 1, d, hd, hj => by
    rw [sum_digits_split, Nat.shiftRight_eq_div_pow, show w * (j + 1) = w + w * j by ring,
      pow_add, ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ (Nat.two_pow_pos w),
      Nat.div_eq_of_lt (hd 0 (Nat.succ_pos n)), zero_add, ← Nat.shiftRight_eq_div_pow]
    exact digit_of_sum w j n (fun m => d (m + 1)) (fun m hm => hd (m + 1) (by omega))
      (by omega)

theorem spread_of_digits (w s fuel n : ℕ) (d : ℕ → ℕ) (hd : ∀ m < n, d m < 2 ^ w)
    (hn : n ≤ 2 ^ fuel) :
    spread w s (∑ m ∈ range n, d m * 2 ^ (w * m)) fuel 0 n =
      ∑ m ∈ range n, d m * 2 ^ (s * m) := by
  rw [spread_eq w s _ fuel 0 n hn]
  refine sum_congr rfl fun m hm => ?_
  rw [zero_add, digit_of_sum w m n d hd (mem_range.mp hm)]

/-- `E₄` packed in `72`-bit slots, spread to `s`-bit slots. -/
theorem spread_e4Pack (s fuel n : ℕ) (hn : 0 < n) (hn' : n ≤ 3530) (hfuel : n ≤ 2 ^ fuel) :
    spread 72 s (e4Pack 72 n) fuel 0 n = ∑ m ∈ range n, e4Digit m * 2 ^ (s * m) := by
  rw [e4Pack_eq_sum (by norm_num) hn (by omega)]
  exact spread_of_digits 72 s fuel n e4Digit
    (fun m hm => (e4Digit_lt (by omega)).trans_le
      (Nat.pow_le_pow_right (by norm_num) (by norm_num)))
    hfuel

/-- `Σ σ₅(m) qᵐ` packed in `72`-bit slots, spread to `s`-bit slots. -/
theorem spread_sigmaPack5 (s fuel n : ℕ) (hn' : n ≤ 3530) (hfuel : n ≤ 2 ^ fuel) :
    spread 72 s (sigmaPack 5 72 n) fuel 0 n =
      ∑ m ∈ range n, ArithmeticFunction.sigma 5 m * 2 ^ (s * m) := by
  rw [sigmaPack_eq 5 72 (by norm_num) (by omega)]
  exact spread_of_digits 72 s fuel n _ (fun m hm => sigma5_lt (by omega)) hfuel

/-! ### Homogeneity and the two-accumulator inner sum -/

theorem evalSparseBivarCleared_smul {R : Type*} [CommRing R] (k a b c d : R) :
    ∀ terms : List SparseBivarTerm, (∀ t ∈ terms, t.xPow ≤ 42 ∧ t.yPow ≤ 42) →
      evalSparseBivarCleared terms 42 42 (k * a) (k * b) (k * c) (k * d) =
        k ^ 84 * evalSparseBivarCleared terms 42 42 a b c d
  | [], _ => by simp [evalSparseBivarCleared]
  | t :: ts, h => by
    obtain ⟨hx, hy⟩ := h t (by simp)
    rw [evalSparseBivarCleared, evalSparseBivarCleared,
      evalSparseBivarCleared_smul k a b c d ts (fun u hu => h u (by simp [hu])), mul_add]
    congr 1
    have e : k ^ 84 = k ^ t.xPow * k ^ (42 - t.xPow) * k ^ t.yPow * k ^ (42 - t.yPow) := by
      rw [← pow_add, ← pow_add, ← pow_add]
      congr 1
      omega
    rw [e, mul_pow, mul_pow, mul_pow, mul_pow]
    ring

theorem cast_innerPN_aux {M : ℕ} (R : List ℕ) (key idx : SparseBivarTerm → ℕ) (x : ℕ) :
    ∀ (terms : List SparseBivarTerm) (p q : ℕ),
      ((terms.foldl (fun acc t => if key t = x ∧ 0 ≤ t.coeff then
          acc + t.coeff.toNat * R.getD (idx t) 0 else acc) p : ℕ) : ZMod M) -
        ((terms.foldl (fun acc t => if key t = x ∧ t.coeff < 0 then
          acc + t.coeff.natAbs * R.getD (idx t) 0 else acc) q : ℕ) : ZMod M) =
        (p : ZMod M) - q + (terms.map fun t => if key t = x then
          (t.coeff : ZMod M) * ((R.getD (idx t) 0 : ℕ) : ZMod M) else 0).sum
  | [], p, q => by simp
  | t :: ts, p, q => by
    simp only [List.foldl_cons]
    rw [cast_innerPN_aux R key idx x ts, List.map_cons, List.sum_cons]
    by_cases hx : key t = x
    · by_cases hc : 0 ≤ t.coeff
      · rw [if_pos ⟨hx, hc⟩, if_neg (fun h => absurd h.2 (not_lt.mpr hc)), if_pos hx]
        have e : ((t.coeff.toNat : ℕ) : ZMod M) = (t.coeff : ZMod M) := by
          rw [← Int.cast_natCast, Int.toNat_of_nonneg hc]
        rw [Nat.cast_add, Nat.cast_mul, e]
        ring
      · rw [if_neg (fun h => hc h.2), if_pos ⟨hx, lt_of_not_ge hc⟩, if_pos hx]
        have e : ((t.coeff.natAbs : ℕ) : ZMod M) = -(t.coeff : ZMod M) := by
          rw [← Int.cast_natCast, Int.natCast_natAbs, abs_of_neg (lt_of_not_ge hc),
            Int.cast_neg]
        rw [Nat.cast_add, Nat.cast_mul, e]
        ring
    · rw [if_neg (fun h => hx h.1), if_neg (fun h => hx h.1), if_neg hx]
      ring

theorem cast_innerPN {k m M : ℕ} (hM : M = 2 ^ k) (hm : m = M - 1) (R : List ℕ)
    (key idx : SparseBivarTerm → ℕ) (x : ℕ) (terms : List SparseBivarTerm) :
    ((innerPN m R key idx x terms : ℕ) : ZMod M) =
      (terms.map fun t => if key t = x then
        (t.coeff : ZMod M) * ((R.getD (idx t) 0 : ℕ) : ZMod M) else 0).sum := by
  rw [innerPN, cast_subM hM hm, cast_innerPN_aux, Nat.cast_zero, sub_zero, zero_add]

theorem length_addAt (f : ℕ × ℕ → ℕ × ℕ) :
    ∀ (n : ℕ) (bs : List (ℕ × ℕ)), (addAt f n bs).length = bs.length
  | _, [] => by simp [addAt]
  | 0, b :: bs => rfl
  | n + 1, b :: bs => by rw [addAt, List.length_cons, List.length_cons, length_addAt f n bs]

theorem getD_addAt (f : ℕ × ℕ → ℕ × ℕ) :
    ∀ (n : ℕ) (bs : List (ℕ × ℕ)) (i : ℕ), (addAt f n bs).getD i (0, 0) =
      if i = n ∧ i < bs.length then f (bs.getD i (0, 0)) else bs.getD i (0, 0)
  | _, [], i => by simp [addAt]
  | 0, b :: bs, 0 => by simp [addAt]
  | 0, b :: bs, i + 1 => by simp [addAt]
  | n + 1, b :: bs, 0 => by simp [addAt]
  | n + 1, b :: bs, i + 1 => by
    simp only [addAt, List.getD_cons_succ, List.length_cons]
    rw [getD_addAt f n bs i]
    by_cases h : i = n ∧ i < bs.length
    · obtain ⟨h1, h2⟩ := h
      rw [if_pos ⟨h1, h2⟩, if_pos ⟨by omega, by omega⟩]
    · rw [if_neg h, if_neg (fun ⟨h1, h2⟩ => h ⟨by omega, by omega⟩)]

theorem getD_replicate_zero : ∀ (n y : ℕ),
    (List.replicate n ((0 : ℕ), (0 : ℕ))).getD y (0, 0) = (0, 0)
  | 0, y => by simp
  | n + 1, 0 => by simp [List.replicate_succ]
  | n + 1, y + 1 => by rw [List.replicate_succ, List.getD_cons_succ]; exact getD_replicate_zero n y

/-- The value `pos - neg` of bucket `y`. -/
def bucketVal (M : ℕ) (bs : List (ℕ × ℕ)) (y : ℕ) : ZMod M :=
  ((bs.getD y (0, 0)).1 : ZMod M) - ((bs.getD y (0, 0)).2 : ZMod M)

theorem cast_addSigned {M : ℕ} (c : ℤ) (v : ℕ) (p : ℕ × ℕ) :
    ((addSigned c v p).1 : ZMod M) - ((addSigned c v p).2 : ZMod M) =
      ((p.1 : ZMod M) - p.2) + (c : ZMod M) * v := by
  unfold addSigned
  by_cases hc : 0 ≤ c
  · rw [if_pos hc]
    have e : ((c.toNat : ℕ) : ZMod M) = (c : ZMod M) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hc]
    simp only [Nat.cast_add, Nat.cast_mul, e]
    ring
  · rw [if_neg hc]
    have e : ((c.natAbs : ℕ) : ZMod M) = -(c : ZMod M) := by
      rw [← Int.cast_natCast, Int.natCast_natAbs, abs_of_neg (lt_of_not_ge hc), Int.cast_neg]
    simp only [Nat.cast_add, Nat.cast_mul, e]
    ring

theorem bucketVal_foldl {M : ℕ} (R : List ℕ) (n : ℕ) :
    ∀ (terms : List SparseBivarTerm) (st : ℕ × ℕ × List (ℕ × ℕ)),
      st.2.1 = R.getD st.1 0 → st.2.2.length = n → (∀ t ∈ terms, t.yPow < n) → ∀ y,
      bucketVal M (terms.foldl (bucketStep R) st).2.2 y = bucketVal M st.2.2 y +
        (terms.map fun t => if t.yPow = y then
          (t.coeff : ZMod M) * ((R.getD t.xPow 0 : ℕ) : ZMod M) else 0).sum
  | [], st, _, _, _, y => by simp
  | t :: ts, st, hv, hlen, hy, y => by
    have hv' : (if t.xPow = st.1 then st.2.1 else R.getD t.xPow 0) = R.getD t.xPow 0 := by
      split_ifs with h
      · rw [hv, h]
      · rfl
    rw [List.foldl_cons, bucketVal_foldl R n ts (bucketStep R st t)
      (by simp only [bucketStep]; exact hv')
      (by simp only [bucketStep]; rw [length_addAt, hlen])
      (fun t' ht' => hy t' (List.mem_cons_of_mem _ ht')) y, List.map_cons, List.sum_cons]
    simp only [bucketStep, hv']
    rw [← add_assoc]
    congr 1
    unfold bucketVal
    rw [getD_addAt]
    by_cases hty : t.yPow = y
    · rw [if_pos ⟨hty.symm, by rw [hlen, ← hty]; exact hy t (List.mem_cons_self ..)⟩, if_pos hty,
        cast_addSigned]
    · rw [if_neg (fun h => hty h.1.symm), if_neg hty, add_zero]

theorem cast_bucketPN {k m M : ℕ} (hM : M = 2 ^ k) (hm : m = M - 1) (R : List ℕ) (n : ℕ)
    (terms : List SparseBivarTerm) (hy : ∀ t ∈ terms, t.yPow < n) (y : ℕ) :
    ((subM m ((bucketPN R n terms).getD y (0, 0)).1 ((bucketPN R n terms).getD y (0, 0)).2 : ℕ) :
        ZMod M) =
      (terms.map fun t => if t.yPow = y then
        (t.coeff : ZMod M) * ((R.getD t.xPow 0 : ℕ) : ZMod M) else 0).sum := by
  have h := bucketVal_foldl (M := M) R n terms (0, R.getD 0 0, List.replicate n (0, 0)) rfl
    (by simp) hy y
  have h0 : bucketVal M (List.replicate n ((0 : ℕ), (0 : ℕ))) y = 0 := by
    rw [bucketVal, getD_replicate_zero]
    simp
  rw [h0, zero_add] at h
  rw [cast_subM hM hm, ← h]
  rfl

/-! ### Biased digits, Horner sums, grouping by `y` -/

theorem digits_sum_lt (w : ℕ) : ∀ (n : ℕ) (d : ℕ → ℕ), (∀ m < n, d m < 2 ^ w) →
    ∑ m ∈ range n, d m * 2 ^ (w * m) < 2 ^ (w * n)
  | 0, _, _ => by simp
  | n + 1, d, hd => by
    rw [Finset.sum_range_succ]
    have ih := digits_sum_lt w n d (fun m hm => hd m (by omega))
    have hn := hd n (by omega)
    calc ∑ m ∈ range n, d m * 2 ^ (w * m) + d n * 2 ^ (w * n)
        < 2 ^ (w * n) + d n * 2 ^ (w * n) := Nat.add_lt_add_right ih _
      _ = (d n + 1) * 2 ^ (w * n) := by ring
      _ ≤ 2 ^ w * 2 ^ (w * n) := Nat.mul_le_mul_right _ hn
      _ = 2 ^ (w * (n + 1)) := by
        rw [← pow_add]
        congr 1
        ring

theorem biased_digit_lt {w : ℕ} (hw : 0 < w) {c : ℤ} (hc : |c| < 2 ^ (w - 1)) :
    (c + 2 ^ (w - 1)).toNat < 2 ^ w := by
  have hP : (2 : ℕ) ^ w = 2 * 2 ^ (w - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have h2 : (2 : ℤ) ^ (w - 1) = ((2 ^ (w - 1) : ℕ) : ℤ) := by
    rw [Nat.cast_pow, Nat.cast_ofNat]
  have h := abs_lt.mp hc
  rw [hP]
  rw [h2] at h ⊢
  generalize (2 ^ (w - 1) : ℕ) = P at h ⊢
  omega

/-- A packed series whose first `n` coefficients lie in `(-2^(w-1), 2^(w-1))`: adding the bias
`2^(w-1)` to every slot and reducing gives the true coefficients plus the bias as digits. -/
theorem biased_digits {w n M : ℕ} (hM : M = 2 ^ (w * n)) (hw : 0 < w) (f : PowerSeries ℤ)
    (hf : ∀ m < n, |PowerSeries.coeff m f| < 2 ^ (w - 1)) (V : ℕ)
    (hV : (V : ZMod M) = packEval ((2 : ZMod M) ^ w) n f) :
    (V + 2 ^ (w - 1) * ∑ m ∈ range n, 2 ^ (w * m)) % M =
      ∑ m ∈ range n, (PowerSeries.coeff m f + 2 ^ (w - 1)).toNat * 2 ^ (w * m) := by
  have hd : ∀ m < n, (PowerSeries.coeff m f + 2 ^ (w - 1)).toNat < 2 ^ w :=
    fun m hm => biased_digit_lt hw (hf m hm)
  have hR : ∑ m ∈ range n, (PowerSeries.coeff m f + 2 ^ (w - 1)).toNat * 2 ^ (w * m) < M := by
    rw [hM]
    exact digits_sum_lt w n _ hd
  have hterm : ∀ m ∈ range n,
      ((((PowerSeries.coeff m f + 2 ^ (w - 1)).toNat * 2 ^ (w * m) : ℕ)) : ZMod M) =
        ((PowerSeries.coeff m f : ℤ) : ZMod M) * ((2 : ZMod M) ^ w) ^ m +
          2 ^ (w - 1) * 2 ^ (w * m) := by
    intro m hm
    have h0 : 0 ≤ PowerSeries.coeff m f + 2 ^ (w - 1) := by
      have := abs_lt.mp (hf m (mem_range.mp hm))
      linarith
    rw [Nat.cast_mul, ← Int.cast_natCast (PowerSeries.coeff m f + 2 ^ (w - 1)).toNat,
      Int.toNat_of_nonneg h0]
    push_cast
    ring
  have hcast :
      ((∑ m ∈ range n, (PowerSeries.coeff m f + 2 ^ (w - 1)).toNat * 2 ^ (w * m) : ℕ) :
        ZMod M) = ((V + 2 ^ (w - 1) * ∑ m ∈ range n, 2 ^ (w * m) : ℕ) : ZMod M) := by
    rw [Nat.cast_sum, sum_congr rfl hterm, Finset.sum_add_distrib, ← packEval_eq_sum, ← hV,
      ← Finset.mul_sum]
    norm_num
  have := (ZMod.natCast_eq_natCast_iff' _ _ M).mp hcast.symm
  rwa [Nat.mod_eq_of_lt hR] at this

theorem one_add_geomF (w fuel K : ℕ) (hK : K < 2 ^ fuel) :
    1 + geomF w fuel K = ∑ m ∈ range (K + 1), 2 ^ (w * m) := by
  rw [geomF_eq w fuel K hK, Finset.sum_range_succ']
  simp only [mul_zero, pow_zero, ← pow_mul]
  ring

theorem cast_negM {k m M : ℕ} (hM : M = 2 ^ k) (hm : m = M - 1) (b : ℕ) :
    ((negM m b : ℕ) : ZMod M) = -b := by
  have hle : b &&& m ≤ m + 1 := Nat.and_le_right.trans (Nat.le_succ m)
  rw [negM, Nat.cast_sub hle, cast_land_mask hM hm, cast_mask_succ hM hm, zero_sub]

theorem cast_hornerM {k m M : ℕ} (hM : M = 2 ^ k) (hm : m = M - 1) (c : ℕ) (S D : ℕ → ℕ) :
    ∀ n : ℕ, ((hornerM m c S D n : ℕ) : ZMod M) =
      ∑ j ∈ range n, (S j : ZMod M) * (D j : ZMod M) * (c : ZMod M) ^ (n - 1 - j)
  | 0 => by simp [hornerM]
  | n + 1 => by
    rw [hornerM, cast_addM hM hm, cast_mulM hM hm, cast_mulM hM hm,
      cast_hornerM hM hm c S D n, Finset.sum_range_succ, Finset.mul_sum]
    have h1 : ∀ j ∈ range n,
        (c : ZMod M) * ((S j : ZMod M) * (D j : ZMod M) * (c : ZMod M) ^ (n - 1 - j)) =
          (S j : ZMod M) * (D j : ZMod M) * (c : ZMod M) ^ (n + 1 - 1 - j) := by
      intro j hj
      rw [show n + 1 - 1 - j = (n - 1 - j) + 1 by have := mem_range.mp hj; omega, pow_succ]
      ring
    rw [sum_congr rfl h1, show n + 1 - 1 - n = 0 by omega, pow_zero, mul_one]
    exact add_comm _ _

/-- Grouping a cleared sparse evaluation by the `y`-degree. -/
theorem evalSparseBivarCleared_eq_grouped_y {R : Type*} [CommRing R] (a b c d : R) :
    ∀ terms : List SparseBivarTerm, (∀ t ∈ terms, t.yPow ≤ 42) →
      evalSparseBivarCleared terms 42 42 a b c d =
        ∑ y ∈ range 43, c ^ y * d ^ (42 - y) *
          (terms.map fun t => if t.yPow = y then
            (t.coeff : R) * (a ^ t.xPow * b ^ (42 - t.xPow)) else 0).sum
  | [], _ => by simp [evalSparseBivarCleared]
  | t :: ts, h => by
    rw [evalSparseBivarCleared, evalSparseBivarCleared_eq_grouped_y a b c d ts
      (fun u hu => h u (by simp [hu]))]
    simp only [List.map_cons, List.sum_cons, mul_add, Finset.sum_add_distrib]
    congr 1
    simp only [mul_ite, mul_zero]
    rw [Finset.sum_ite_eq (range 43) t.yPow, if_pos (mem_range.mpr (by
      have := h t (by simp); omega))]
    ring

theorem abs_list_sum_map_le {α : Type*} (g : α → ℤ) (G : α → ℕ) :
    ∀ l : List α, (∀ a ∈ l, |g a| ≤ G a) → |(l.map g).sum| ≤ ((l.map G).sum : ℤ)
  | [], _ => by simp
  | a :: l, h => by
    rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, Nat.cast_add]
    exact (abs_add_le _ _).trans (add_le_add (h a (by simp))
      (abs_list_sum_map_le g G l (fun b hb => h b (by simp [hb]))))

/-! ### Spreading by one product and one mask

`spread` builds `2 log₂ n` full-width numbers. When the target slots are far apart
(`c (n + 1) + 2 ≤ a`), one product `U · Σ_j 2^(a j)` puts slot `k` of `U` at bit `(a + c) k`,
with the other partial products confined to bits that a block mask removes. -/

theorem land_blockMask {W c : ℕ} (hcW : c ≤ W) (P : ℕ) : ∀ n : ℕ,
    P &&& ∑ k ∈ range n, (2 ^ c - 1) * 2 ^ (W * k) =
      ∑ k ∈ range n, P / 2 ^ (W * k) % 2 ^ c * 2 ^ (W * k)
  | 0 => by simp
  | n + 1 => by
    have hcW' : 2 ^ c ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) hcW
    have hM : ∑ k ∈ range n, (2 ^ c - 1) * 2 ^ (W * k) < 2 ^ (W * n) :=
      digits_sum_lt W n _ (fun k _ => lt_of_lt_of_le (Nat.sub_lt (Nat.two_pow_pos c) one_pos) hcW')
    have hR : ∑ k ∈ range n, P / 2 ^ (W * k) % 2 ^ c * 2 ^ (W * k) < 2 ^ (W * n) :=
      digits_sum_lt W n _ (fun k _ => lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos c)) hcW')
    rw [sum_range_succ, sum_range_succ, add_comm _ ((2 ^ c - 1) * 2 ^ (W * n)),
      add_comm _ (P / 2 ^ (W * n) % 2 ^ c * 2 ^ (W * n)), mul_comm (2 ^ c - 1),
      mul_comm (P / 2 ^ (W * n) % 2 ^ c)]
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_and, Nat.testBit_two_pow_mul_add _ hM, Nat.testBit_two_pow_mul_add _ hR]
    split_ifs with hj
    · rw [← Nat.testBit_and, land_blockMask hcW P n]
    · rw [Nat.testBit_two_pow_sub_one, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow,
        Nat.sub_add_cancel (not_lt.mp hj)]
      exact Bool.and_comm _ _

theorem sum_range_split_digit (c n k : ℕ) (hk : k < n) (d : ℕ → ℕ) :
    ∑ m ∈ range n, d m * 2 ^ (c * m) =
      ∑ m ∈ range k, d m * 2 ^ (c * m) +
        2 ^ (c * k) * (d k + 2 ^ c * ∑ i ∈ range (n - k - 1), d (k + 1 + i) * 2 ^ (c * i)) := by
  conv_lhs => rw [show n = (k + 1) + (n - k - 1) by omega, Finset.sum_range_add,
    Finset.sum_range_succ]
  rw [add_assoc]
  congr 1
  rw [mul_add, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · ring
  · refine sum_congr rfl fun i _ => ?_
    ring

theorem geom_mul_le {e a : ℕ} (hea : e + 2 ≤ a) : ∀ k : ℕ,
    2 ^ (e + 1) * ∑ j ∈ range k, 2 ^ (a * j) ≤ 2 ^ (a * k)
  | 0 => by simp
  | k + 1 => by
    have ih := geom_mul_le hea k
    have h1 : 2 ^ (e + 1) + 1 ≤ 2 ^ a :=
      calc 2 ^ (e + 1) + 1 ≤ 2 ^ (e + 1) + 2 ^ (e + 1) :=
            Nat.add_le_add_left Nat.one_le_two_pow _
        _ = 2 ^ (e + 2) := by ring
        _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) hea
    calc 2 ^ (e + 1) * ∑ j ∈ range (k + 1), 2 ^ (a * j)
        = 2 ^ (e + 1) * ∑ j ∈ range k, 2 ^ (a * j) + 2 ^ (e + 1) * 2 ^ (a * k) := by
          rw [sum_range_succ, mul_add]
      _ ≤ 2 ^ (a * k) + 2 ^ (e + 1) * 2 ^ (a * k) := Nat.add_le_add_right ih _
      _ = (2 ^ (e + 1) + 1) * 2 ^ (a * k) := by ring
      _ ≤ 2 ^ a * 2 ^ (a * k) := Nat.mul_le_mul_right _ h1
      _ = 2 ^ (a * (k + 1)) := by rw [← pow_add]; congr 1; ring

/-- Slot `k` of `U · Σ_j 2^(a j)` at bit `(a + c) k` is digit `k` of `U`. -/
theorem comb_block_digit {a c n : ℕ} (hac : c * (n + 1) + 2 ≤ a) (d : ℕ → ℕ)
    (hd : ∀ m < n, d m < 2 ^ c) {k : ℕ} (hk : k < n) :
    (∑ m ∈ range n, d m * 2 ^ (c * m)) * (∑ j ∈ range n, 2 ^ (a * j)) /
      2 ^ ((a + c) * k) % 2 ^ c = d k := by
  have hU := sum_range_split_digit c n k hk d
  have hG : ∑ j ∈ range n, 2 ^ (a * j) = ∑ j ∈ range k, 2 ^ (a * j) +
      2 ^ (a * k) * (1 + 2 ^ a * ∑ i ∈ range (n - k - 1), 2 ^ (a * i)) := by
    simpa using sum_range_split_digit a n k hk (fun _ => 1)
  have hUlt : ∑ m ∈ range n, d m * 2 ^ (c * m) < 2 ^ (c * n) := digits_sum_lt c n d hd
  have hUlo : ∑ m ∈ range k, d m * 2 ^ (c * m) < 2 ^ (c * k) :=
    digits_sum_lt c k d (fun m hm => hd m (by omega))
  have hcn : c * (k + 1) ≤ c * n := Nat.mul_le_mul_left c hk
  have hcn1 : c * (n + 1) = c * n + c := by ring
  have hGlo := geom_mul_le (e := c * n) (a := a) (by omega) k
  set U := ∑ m ∈ range n, d m * 2 ^ (c * m)
  set Ulo := ∑ m ∈ range k, d m * 2 ^ (c * m)
  set Uhi := ∑ i ∈ range (n - k - 1), d (k + 1 + i) * 2 ^ (c * i)
  set Glo := ∑ j ∈ range k, 2 ^ (a * j)
  set Ghi := ∑ i ∈ range (n - k - 1), 2 ^ (a * i)
  have hle : (a + c) * k + c ≤ a * k + a := by
    have : (a + c) * k + c = a * k + c * (k + 1) := by ring
    omega
  obtain ⟨Z, hZ⟩ := pow_dvd_pow 2 hle
  have hprod : U * (Glo + 2 ^ (a * k) * (1 + 2 ^ a * Ghi)) =
      (U * Glo + 2 ^ (a * k) * Ulo) +
        2 ^ ((a + c) * k) * (d k + 2 ^ c * (Uhi + Z * (U * Ghi))) := by
    have e1 : 2 ^ (a * k) * 2 ^ a = 2 ^ ((a + c) * k + c) * Z := by rw [← pow_add, hZ]
    calc U * (Glo + 2 ^ (a * k) * (1 + 2 ^ a * Ghi))
        = U * Glo + 2 ^ (a * k) * U + (2 ^ (a * k) * 2 ^ a) * (U * Ghi) := by ring
      _ = U * Glo + 2 ^ (a * k) * U + 2 ^ ((a + c) * k + c) * Z * (U * Ghi) := by rw [e1]
      _ = (U * Glo + 2 ^ (a * k) * Ulo) +
            2 ^ ((a + c) * k) * (d k + 2 ^ c * (Uhi + Z * (U * Ghi))) := by
          rw [hU]
          ring
  have hlow : U * Glo + 2 ^ (a * k) * Ulo < 2 ^ ((a + c) * k) := by
    have h1 : U * Glo ≤ 2 ^ (c * n) * Glo := Nat.mul_le_mul_right _ hUlt.le
    have h2 : 2 ^ (c * n + 1) * Glo = 2 * (2 ^ (c * n) * Glo) := by ring
    have h3 : 2 ^ (a * k) * (Ulo + 1) ≤ 2 ^ (a * k) * 2 ^ (c * k) := Nat.mul_le_mul_left _ hUlo
    have h4 : (2 : ℕ) ^ ((a + c) * k) = 2 ^ (a * k) * 2 ^ (c * k) := by
      rw [← pow_add]; congr 1; ring
    have h5 : 0 < 2 ^ (a * k) := Nat.two_pow_pos _
    rw [h4]
    rw [mul_add, mul_one] at h3
    omega
  rw [hG, hprod, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hlow, zero_add,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hd k hk)]

theorem combSpread_eq {a c n : ℕ} (hn : 0 < n) (hn' : n ≤ 128) (hac : c * (n + 1) + 2 ≤ a)
    (d : ℕ → ℕ) (hd : ∀ m < n, d m < 2 ^ c) :
    combSpread a c n (∑ m ∈ range n, d m * 2 ^ (c * m)) =
      ∑ k ∈ range n, d k * 2 ^ ((a + c) * k) := by
  have hK : n - 1 < 2 ^ 7 := by norm_num; omega
  have hmask : (2 ^ c - 1) * ∑ k ∈ range n, 2 ^ ((a + c) * k) =
      ∑ k ∈ range n, (2 ^ c - 1) * 2 ^ ((a + c) * k) := Finset.mul_sum _ _ _
  rw [combSpread, one_add_geomF a 7 (n - 1) hK, one_add_geomF (a + c) 7 (n - 1) hK,
    Nat.sub_add_cancel (by omega : 1 ≤ n), hmask, land_blockMask (W := a + c) (c := c) (by omega)]
  refine sum_congr rfl fun k hk => ?_
  rw [comb_block_digit hac d hd (mem_range.mp hk)]

end Ripple.Number.Modular
