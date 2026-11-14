-- Ripple/Kurtz/StrongApprox/DyadicCoverBudget.lean
import Ripple.Kurtz.StrongApprox.BrownianEntropyComparison

/-!
# Deterministic budget for the dyadic cover of the clock horizon

The Brownian modulus is available on dyadic horizons `2^j`
(`DyadicBrownianOn`).  For the comparison of Kurtz 1978 (Lemma 3.2, p. 231,
used in Theorem 3.3(a), p. 232) all clocks lie in `[0, N D]`, and one chooses
`j` with `N D ≤ 2^j < 2 N D`.  This file proves the elementary estimates that
make the resulting coefficient independent of `N`: the logarithm of the
covering horizon and the entropy parameter at level `j` cost only multiples of
`log N`, which is exactly the factor `log N / N` in (3.20); it also defines the
explicit coefficient `dyadicCoverBeta`, proves it nonnegative, and closes the
final algebra after the perturbed comparison.
-/

noncomputable section

namespace Ripple.Kurtz.StrongApprox

open Set

/-- The entropy parameter at a dyadic covering horizon. -/
def dyadicCoverEntropy (A : ℝ) (j : ℕ) : ℝ :=
  2 + A + ((j : ℝ) + 1) * Real.log 2

/-- The affine Brownian budget retains the actual covering horizon. -/
def dyadicCoverAffineBudget (H A : ℝ) (j : ℕ) : ℝ :=
  Real.log H + dyadicCoverEntropy A j + 1

/-- Deterministic coefficient controlling the logarithm of the horizon. -/
def dyadicCoverLogFactor (D : ℝ) : ℝ :=
  1 + Real.log (2 * D) / Real.log 2

/-- Deterministic additive cost of the dyadic entropy cover. -/
def dyadicCoverOffset (D : ℝ) : ℝ :=
  2 * Real.log D + 3 * Real.log 2 + 3

private theorem real_succ_le_two_pow (n : ℕ) :
    (n : ℝ) + 1 ≤ (2 : ℝ) ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [pow_succ]
      push_cast
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      nlinarith

/-- Every positive macroscopic horizon has a dyadic cover with less than
factor two overhead.  The parameter `N` may already be a natural-number cast. -/
theorem exists_dyadic_cover {N D : ℝ} (hN : 2 ≤ N) (hD : 1 ≤ D) :
    ∃ j : ℕ, N * D ≤ (2 : ℝ) ^ j ∧ (2 : ℝ) ^ j < 2 * N * D := by
  have hNnonneg : 0 ≤ N := by linarith
  have hND : 2 ≤ N * D := by
    calc
      2 ≤ N := hN
      _ = N * 1 := by ring
      _ ≤ N * D := mul_le_mul_of_nonneg_left hD hNnonneg
  have hex : ∃ j : ℕ, N * D ≤ (2 : ℝ) ^ j := by
    obtain ⟨n, hn⟩ := exists_nat_gt (N * D)
    exact ⟨n, by linarith [real_succ_le_two_pow n]⟩
  let j := Nat.find hex
  have hj : N * D ≤ (2 : ℝ) ^ j := Nat.find_spec hex
  have hjne : j ≠ 0 := by
    intro hz
    rw [hz] at hj
    norm_num at hj
    linarith
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hjne
  have hklt : k < Nat.find hex := by change k < j; omega
  have hpre : (2 : ℝ) ^ k < N * D :=
    lt_of_not_ge (Nat.find_min hex hklt)
  refine ⟨j, hj, ?_⟩
  rw [hk, pow_succ]
  nlinarith

/-- Natural-number form of the dyadic cover. -/
theorem exists_dyadic_cover_nat {N : ℕ} {D : ℝ}
    (hN : 2 ≤ N) (hD : 1 ≤ D) :
    ∃ j : ℕ, (N : ℝ) * D ≤ (2 : ℝ) ^ j ∧
      (2 : ℝ) ^ j < 2 * (N : ℝ) * D := by
  exact exists_dyadic_cover (by exact_mod_cast hN) hD

/-- A covering horizon has logarithmic overhead bounded independently of `N`. -/
theorem dyadicCover_log_le {N D H : ℝ}
    (hN : 2 ≤ N) (hD : 1 ≤ D)
    (hlo : N * D ≤ H) (hhi : H < 2 * N * D) :
    Real.log H ≤ Real.log N + Real.log D + Real.log 2 := by
  have hNp : 0 < N := by linarith
  have hDp : 0 < D := by linarith
  have hHp : 0 < H := (mul_pos hNp hDp).trans_le hlo
  have hlog := Real.log_le_log hHp hhi.le
  rw [Real.log_mul (mul_ne_zero (by norm_num) hNp.ne') hDp.ne',
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hNp.ne'] at hlog
  linarith

/-- The level penalty costs one additional logarithm of `N`. -/
theorem dyadicCover_entropy_le {N D A : ℝ} {j : ℕ}
    (hN : 2 ≤ N) (hD : 1 ≤ D)
    (hlo : N * D ≤ (2 : ℝ) ^ j)
    (hhi : (2 : ℝ) ^ j < 2 * N * D) :
    dyadicCoverEntropy A j ≤
      A + Real.log N + Real.log D + 2 * Real.log 2 + 2 := by
  have hlog := dyadicCover_log_le hN hD hlo hhi
  rw [Real.log_pow] at hlog
  unfold dyadicCoverEntropy
  linarith

/-- The raw affine budget has two logarithms of `N` and one random additive
parameter. -/
theorem dyadicCover_affineBudget_le {N D A : ℝ} {j : ℕ}
    (hN : 2 ≤ N) (hD : 1 ≤ D)
    (hlo : N * D ≤ (2 : ℝ) ^ j)
    (hhi : (2 : ℝ) ^ j < 2 * N * D) :
    dyadicCoverAffineBudget ((2 : ℝ) ^ j) A j ≤
      2 * Real.log N + A + dyadicCoverOffset D := by
  have hlog := dyadicCover_log_le hN hD hlo hhi
  have ha := dyadicCover_entropy_le (A := A) hN hD hlo hhi
  unfold dyadicCoverAffineBudget dyadicCoverOffset
  linarith

/-- Positivity and both inputs required by the affine entropy lemma. -/
theorem dyadicCover_affineBudget_admissible {N D A : ℝ} {j : ℕ}
    (hN : 2 ≤ N) (hD : 1 ≤ D) (hA : 0 ≤ A)
    (hlo : N * D ≤ (2 : ℝ) ^ j) :
    2 ≤ dyadicCoverEntropy A j ∧
    1 ≤ dyadicCoverAffineBudget ((2 : ℝ) ^ j) A j ∧
    Real.log ((2 : ℝ) ^ j) + dyadicCoverEntropy A j ≤
      dyadicCoverAffineBudget ((2 : ℝ) ^ j) A j ∧
    Real.log N + dyadicCoverEntropy A j ≤
      dyadicCoverAffineBudget ((2 : ℝ) ^ j) A j := by
  have hNp : 0 < N := by linarith
  have hNH : N ≤ (2 : ℝ) ^ j := by
    calc
      N = N * 1 := by ring
      _ ≤ N * D := mul_le_mul_of_nonneg_left hD hNp.le
      _ ≤ (2 : ℝ) ^ j := hlo
  have hHone : 1 ≤ (2 : ℝ) ^ j := by linarith
  have hlogH : 0 ≤ Real.log ((2 : ℝ) ^ j) := Real.log_nonneg hHone
  have hlogNH := Real.log_le_log hNp hNH
  have hlogtwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have ha : 2 ≤ dyadicCoverEntropy A j := by
    unfold dyadicCoverEntropy
    have hprod : 0 ≤ ((j : ℝ) + 1) * Real.log 2 := by positivity
    linarith
  unfold dyadicCoverAffineBudget
  exact ⟨ha, by linarith, by linarith, by linarith⟩

/-- Convert an additive horizon cost to a multiple of `log N`. -/
theorem dyadicCover_log_factor_bound {N D H : ℝ}
    (hN : 2 ≤ N) (hD : 1 ≤ D)
    (hlo : N * D ≤ H) (hhi : H < 2 * N * D) :
    Real.log H ≤ dyadicCoverLogFactor D * Real.log N := by
  have hlog := dyadicCover_log_le hN hD hlo hhi
  have hDp : 0 < D := by linarith
  have hL : 0 ≤ Real.log (2 * D) := Real.log_nonneg (by linarith)
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogN : Real.log 2 ≤ Real.log N :=
    Real.log_le_log (by norm_num) hN
  have hratio : Real.log (2 * D) ≤
      (Real.log (2 * D) / Real.log 2) * Real.log N := by
    rw [div_mul_eq_mul_div, le_div_iff₀ htwo]
    exact mul_le_mul_of_nonneg_left hlogN hL
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hDp.ne'] at hratio
  unfold dyadicCoverLogFactor
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hDp.ne']
  nlinarith

/-- The KMT contribution on the covering horizon is logarithmic in `N`. -/
theorem dyadicCover_remainder_le {N D H K : ℝ}
    (hN : 2 ≤ N) (hD : 1 ≤ D) (hK : 0 ≤ K)
    (hlo : N * D ≤ H) (hhi : H < 2 * N * D) :
    K * Real.log H ≤ dyadicCoverLogFactor D * K * Real.log N := by
  have h := mul_le_mul_of_nonneg_left
    (dyadicCover_log_factor_bound hN hD hlo hhi) hK
  simpa only [mul_assoc, mul_left_comm, mul_comm] using h

/-- The affine forcing also has a common logarithmic coefficient. -/
theorem dyadicCover_affineBudget_factor_bound {N D A : ℝ} {j : ℕ}
    (hN : 2 ≤ N) (hD : 1 ≤ D) (hA : 0 ≤ A)
    (hlo : N * D ≤ (2 : ℝ) ^ j)
    (hhi : (2 : ℝ) ^ j < 2 * N * D) :
    dyadicCoverAffineBudget ((2 : ℝ) ^ j) A j ≤
      (2 + (A + dyadicCoverOffset D) / Real.log 2) * Real.log N := by
  have hraw := dyadicCover_affineBudget_le (A := A) hN hD hlo hhi
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogN : Real.log 2 ≤ Real.log N :=
    Real.log_le_log (by norm_num) hN
  have hB : 0 ≤ A + dyadicCoverOffset D := by
    unfold dyadicCoverOffset
    have hlogD := Real.log_nonneg hD
    positivity
  have hratio : A + dyadicCoverOffset D ≤
      ((A + dyadicCoverOffset D) / Real.log 2) * Real.log N := by
    rw [div_mul_eq_mul_div, le_div_iff₀ htwo]
    exact mul_le_mul_of_nonneg_left hlogN hB
  nlinarith

/-- Explicit coefficient independent of the population size. -/
def dyadicCoverBeta (S K A D Gamma E M T : ℝ) : ℝ :=
  Real.exp (257 * M * E * T) *
    (S * dyadicCoverLogFactor D * K +
      1024 * S * (2 + (A + dyadicCoverOffset D) / Real.log 2) +
      257 * Gamma * E * T / Real.log 2)

/-- Nonnegativity of the common coefficient; no sign restriction on `M` is
needed for this algebraic assertion. -/
theorem dyadicCoverBeta_nonneg {S K A D Gamma E M T : ℝ}
    (hS : 0 ≤ S) (hK : 0 ≤ K) (hA : 0 ≤ A) (hD : 1 ≤ D)
    (hGamma : 0 ≤ Gamma) (hE : 0 ≤ E) (hT : 0 ≤ T) :
    0 ≤ dyadicCoverBeta S K A D Gamma E M T := by
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogD : 0 ≤ Real.log D := Real.log_nonneg hD
  have hlogDouble : 0 ≤ Real.log (2 * D) :=
    Real.log_nonneg (by linarith)
  unfold dyadicCoverBeta dyadicCoverLogFactor dyadicCoverOffset
  positivity

/-- Deterministic final algebra after the perturbed diffusion comparison. -/
theorem dyadicCover_comparison_le_beta
    {N D A K S Gamma E M T u : ℝ} {j : ℕ}
    (hN : 2 ≤ N) (hD : 1 ≤ D) (hA : 0 ≤ A)
    (hK : 0 ≤ K) (hS : 0 ≤ S) (hGamma : 0 ≤ Gamma)
    (hE : 0 ≤ E) (hT : 0 ≤ T)
    (hlo : N * D ≤ (2 : ℝ) ^ j)
    (hhi : (2 : ℝ) ^ j < 2 * N * D)
    (hu : u ≤ Real.exp (257 * M * E * T) *
      (S * (K * Real.log ((2 : ℝ) ^ j)) +
        1024 * S * dyadicCoverAffineBudget ((2 : ℝ) ^ j) A j +
        257 * Gamma * E * T) / N) :
    u ≤ dyadicCoverBeta S K A D Gamma E M T * Real.log N / N := by
  have hNp : 0 < N := by linarith
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogN : Real.log 2 ≤ Real.log N :=
    Real.log_le_log (by norm_num) hN
  have hR := mul_le_mul_of_nonneg_left
    (dyadicCover_remainder_le hN hD hK hlo hhi) hS
  have hq := mul_le_mul_of_nonneg_left
    (dyadicCover_affineBudget_factor_bound hN hD hA hlo hhi)
    (show 0 ≤ 1024 * S by positivity)
  have hG : 257 * Gamma * E * T ≤
      (257 * Gamma * E * T / Real.log 2) * Real.log N := by
    rw [div_mul_eq_mul_div, le_div_iff₀ htwo]
    exact mul_le_mul_of_nonneg_left hlogN (by positivity)
  have hfront : S * (K * Real.log ((2 : ℝ) ^ j)) +
      1024 * S * dyadicCoverAffineBudget ((2 : ℝ) ^ j) A j +
      257 * Gamma * E * T ≤
      (S * dyadicCoverLogFactor D * K +
        1024 * S * (2 + (A + dyadicCoverOffset D) / Real.log 2) +
        257 * Gamma * E * T / Real.log 2) * Real.log N := by
    calc
      _ ≤ S * (dyadicCoverLogFactor D * K * Real.log N) +
          1024 * S *
            ((2 + (A + dyadicCoverOffset D) / Real.log 2) * Real.log N) +
          (257 * Gamma * E * T / Real.log 2) * Real.log N :=
        add_le_add (add_le_add hR hq) hG
      _ = _ := by ring
  refine hu.trans ?_
  unfold dyadicCoverBeta
  calc
    _ ≤ Real.exp (257 * M * E * T) *
        ((S * dyadicCoverLogFactor D * K +
          1024 * S * (2 + (A + dyadicCoverOffset D) / Real.log 2) +
          257 * Gamma * E * T / Real.log 2) * Real.log N) / N :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hfront (Real.exp_nonneg _)) hNp.le
    _ = _ := by ring

/-- Public entropy-to-affine adapter at the actual covering horizon. -/
theorem brownianEntropyBound_le_cover_affine
    {H N a q h : ℝ} (hH : 0 < H) (hN : 2 ≤ N)
    (ha : 2 ≤ a) (hq : 1 ≤ q)
    (hqH : Real.log H + a ≤ q) (hqN : Real.log N + a ≤ q)
    (hh : h ∈ Icc (0 : ℝ) H) :
    brownianEntropyBound H a h ≤ 1024 * q + 256 * h := by
  have hNp : 0 < N := by linarith
  have haNonneg : 0 ≤ a := by linarith
  have hlogN : (1 / 2 : ℝ) < Real.log N := by
    have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hN
    linarith [Real.log_two_gt_d9]
  have hsqrt := Real.sqrt_nonneg (h * (Real.log (H / h) + a))
  have hshape : brownianEntropyBound H a h ≤
      512 * Real.sqrt (h * (Real.log (H / h) + a)) +
        512 * (Real.log N + a) := by
    unfold brownianEntropyBound brownianEntropyConstant brownianEntropyCore
    split_ifs <;> nlinarith
  have haff := brownian_modulus_shape_le_affine
    (H := H) (N := N) (C := 512) (tail := a) (q := q) (h := h)
    hH hNp (by norm_num) haNonneg hq hqH hqN hh.1 hh.2
  exact hshape.trans (haff.trans (le_of_eq (by ring)))


end Ripple.Kurtz.StrongApprox

end
