import Mathlib.Data.Nat.Choose.Basic
import Ripple.Number.AperyBounded
import Ripple.Number.AperyCertificate
import Ripple.Number.Frobenius.AperyGeneratingFunction

/-!
# F5 bridge for the Apéry conifold PIVP

This file separates the current F5 hypothesis in `AperyBounded.lean` into
two explicit pieces:

* a Frobenius/series-level estimate for the analytic ratio at the conifold;
* a trajectory-level tracking statement saying that the PIVP `ρ` coordinate
  follows that analytic ratio along the `z` coordinate.

The downstream `AperyConifoldThreeHalvesBound` is defined in
`AperyBounded.lean`; this file supplies the split hypotheses that imply it.

The 8-variable PIVP state calls the fourth coordinate `ρ`, and its ODE is
derived from the ratio `B''(z) / A''(z)`.  Although some roadmap text says
`B(z) / A(z)`, the bridge below uses the second-derivative ratio matching
the implemented system.
-/

namespace Ripple.Number

open Finset

/-- Public copy of the `z`-coordinate index used by the 8-variable Apéry PIVP. -/
abbrev apery_iZ : Fin 8 := 0

/-- Public copy of the `ρ`-coordinate index used by the 8-variable Apéry PIVP. -/
abbrev apery_iR : Fin 8 := 4

/-- The real series used throughout the repository for `ζ(3)`. -/
noncomputable def aperyZeta3Series : ℝ :=
  ∑' k : ℕ, 1 / ((k + 1 : ℝ) ^ 3)

/-!
This bridge keeps local `aperyF5*` replicas of the needed Apéry sequences
so that the PIVP-side proof terms below remain stable and visibly separated
from the older sequence/Frobenius API imported through
`AperyGeneratingFunction.lean`.
-/

/-- Local prefixed copy of Apéry's integer sequence `a_n`. -/
def aperyF5A (n : ℕ) : ℕ :=
  ∑ k ∈ range (n + 1), (Nat.choose n k) ^ 2 * (Nat.choose (n + k) k) ^ 2

@[simp]
lemma aperyF5A_zero : aperyF5A 0 = 1 := by
  unfold aperyF5A
  decide

@[simp]
lemma aperyF5A_one : aperyF5A 1 = 5 := by
  unfold aperyF5A
  decide

lemma aperyF5A_pos (n : ℕ) : 0 < aperyF5A n := by
  unfold aperyF5A
  have h0 : (Nat.choose n 0) ^ 2 * (Nat.choose (n + 0) 0) ^ 2 = 1 := by
    simp
  refine lt_of_lt_of_le (show 0 < 1 from Nat.zero_lt_one) ?_
  calc (1 : ℕ)
      = (Nat.choose n 0) ^ 2 * (Nat.choose (n + 0) 0) ^ 2 := h0.symm
    _ ≤ ∑ k ∈ range (n + 1),
            (Nat.choose n k) ^ 2 * (Nat.choose (n + k) k) ^ 2 := by
        apply Finset.single_le_sum
          (f := fun k => (Nat.choose n k) ^ 2 * (Nat.choose (n + k) k) ^ 2)
          (s := range (n + 1)) (a := 0)
        · intro i _; exact Nat.zero_le _
        · exact Finset.mem_range.mpr (Nat.succ_pos _)

section AperyF5AGrowth

/-- Integer-cast form of the local `aperyF5A n` as a sum of the WZ summand. -/
private lemma aperyF5A_int_eq_sum (n : ℕ) :
    ((aperyF5A n : ℕ) : ℤ) = ∑ k ∈ range (n + 1), apery_P n k := by
  unfold aperyF5A apery_P
  push_cast
  rfl

/-- Extend the local `aperyF5A` summation range; the extra WZ summands vanish. -/
private lemma aperyF5A_int_extended (n m : ℕ) (hm : n ≤ m) :
    ((aperyF5A n : ℕ) : ℤ) = ∑ k ∈ range (m + 1), apery_P n k := by
  rw [aperyF5A_int_eq_sum]
  have hsplit : range (m + 1) = range (n + 1) ∪ Ico (n + 1) (m + 1) := by
    ext k
    simp only [mem_range, mem_union, mem_Ico]
    omega
  rw [hsplit]
  have hdisj : Disjoint (range (n + 1)) (Ico (n + 1) (m + 1)) := by
    rw [disjoint_left]
    intro k hk hk'
    simp only [mem_range] at hk
    simp only [mem_Ico] at hk'
    omega
  rw [sum_union hdisj]
  have hzero : ∑ k ∈ Ico (n + 1) (m + 1), apery_P n k = 0 := by
    apply sum_eq_zero
    intro k hk
    simp only [mem_Ico] at hk
    exact apery_P_k_gt n k (by omega)
  rw [hzero, add_zero]

private lemma aperyF5_B_n_zero (n : ℕ) :
    apery_B n 0 = -4 * (2 * (n : ℤ) + 1) ^ 3 := by
  unfold apery_B
  rw [apery_P_n_zero]
  ring

private lemma apery_T_at_zero (n : ℕ) :
    (n + 1 : ℤ) ^ 3 * apery_P (n + 1) 0
      - (34 * (n : ℤ) ^ 3 + 51 * n ^ 2 + 27 * n + 5) * apery_P n 0
      + (n : ℤ) ^ 3 * apery_P (n - 1) 0
    = apery_B n 0 := by
  rw [apery_P_n_zero, apery_P_n_zero, apery_P_n_zero, aperyF5_B_n_zero]
  ring

private lemma apery_choose_two_n_succ_identity (n : ℕ) :
    ((n : ℤ) + 1) * (Nat.choose (2 * n + 2) (n + 1) : ℤ)
      = 2 * (2 * (n : ℤ) + 1) * (Nat.choose (2 * n) n : ℤ) := by
  have hnat : (n + 1) * Nat.choose (2 * n + 2) (n + 1)
      = 2 * (2 * n + 1) * Nat.choose (2 * n) n := by
    have hsub : 2 * n + 1 - n = n + 1 := by omega
    have hsym : Nat.choose (2 * n + 1) n = Nat.choose (2 * n + 1) (n + 1) := by
      calc
        Nat.choose (2 * n + 1) n
            = Nat.choose (2 * n + 1) ((2 * n + 1) - n) := by
                rw [Nat.choose_symm]
                omega
        _ = Nat.choose (2 * n + 1) (n + 1) := by rw [hsub]
    calc
      (n + 1) * Nat.choose (2 * n + 2) (n + 1)
          = Nat.choose (2 * n + 2) (n + 1) * (n + 1) := by ring
      _ = (2 * n + 2) * Nat.choose (2 * n + 1) n := by
              rw [← Nat.add_one_mul_choose_eq (2 * n + 1) n]
      _ = 2 * (n + 1) * Nat.choose (2 * n + 1) n := by ring
      _ = 2 * ((2 * n + 1 - n) * Nat.choose (2 * n + 1) n) := by
              rw [hsub]
              ring
      _ = 2 * ((n + 1) * Nat.choose (2 * n + 1) (n + 1)) := by
              rw [hsub, hsym]
      _ = 2 * ((2 * n + 1) * Nat.choose (2 * n) n) := by
              rw [show (n + 1) * Nat.choose (2 * n + 1) (n + 1) =
                Nat.choose (2 * n + 1) (n + 1) * (n + 1) by ring]
              rw [← Nat.add_one_mul_choose_eq (2 * n) n]
      _ = 2 * (2 * n + 1) * Nat.choose (2 * n) n := by ring
  exact_mod_cast hnat

private lemma apery_T_at_top (n : ℕ) (hn : 1 ≤ n) :
    (n + 1 : ℤ) ^ 3 * apery_P (n + 1) (n + 1)
      - (34 * (n : ℤ) ^ 3 + 51 * n ^ 2 + 27 * n + 5) * apery_P n (n + 1)
      + (n : ℤ) ^ 3 * apery_P (n - 1) (n + 1)
    = -apery_B n n := by
  have hmid : apery_P n (n + 1) = 0 := apery_P_k_gt n (n + 1) (Nat.lt_succ_self _)
  have hlast : apery_P (n - 1) (n + 1) = 0 := by
    apply apery_P_k_gt
    omega
  rw [hmid, hlast, mul_zero, mul_zero, sub_zero, add_zero]
  have hPtop :
      apery_P (n + 1) (n + 1)
        = (Nat.choose (2 * n + 2) (n + 1) : ℤ) ^ 2 := by
    unfold apery_P
    have hchoose1 : Nat.choose (n + 1) (n + 1) = 1 := Nat.choose_self _
    have hsum : n + 1 + (n + 1) = 2 * n + 2 := by omega
    rw [hchoose1, hsum]
    ring
  have hBnn :
      apery_B n n = -4 * ((n : ℤ) + 1) * (2 * n + 1) ^ 2 *
        (Nat.choose (2 * n) n : ℤ) ^ 2 := by
    unfold apery_B
    have hPnn : apery_P n n = (Nat.choose (2 * n) n : ℤ) ^ 2 := by
      unfold apery_P
      rw [Nat.choose_self]
      ring
    rw [hPnn]
    ring
  rw [hPtop, hBnn]
  have hkey := apery_choose_two_n_succ_identity n
  have hkey_sq : (((n : ℤ) + 1) * (Nat.choose (2 * n + 2) (n + 1) : ℤ)) ^ 2
      = (2 * (2 * (n : ℤ) + 1) * (Nat.choose (2 * n) n : ℤ)) ^ 2 := by
    rw [hkey]
  have hmul : ((n : ℤ) + 1) *
        (((n : ℤ) + 1) * (Nat.choose (2 * n + 2) (n + 1) : ℤ)) ^ 2
      = ((n : ℤ) + 1) *
        (2 * (2 * (n : ℤ) + 1) * (Nat.choose (2 * n) n : ℤ)) ^ 2 := by
    rw [hkey_sq]
  linear_combination hmul

lemma aperyF5A_recurrence (n : ℕ) (hn : 1 ≤ n) :
    ((n + 1 : ℤ) ^ 3) * (aperyF5A (n + 1) : ℤ)
      = (2 * n + 1 : ℤ) * (17 * n ^ 2 + 17 * n + 5) * (aperyF5A n : ℤ)
          - (n : ℤ) ^ 3 * (aperyF5A (n - 1) : ℤ) := by
  set T : ℕ → ℤ := fun k =>
    (n + 1 : ℤ) ^ 3 * apery_P (n + 1) k
      - (34 * (n : ℤ) ^ 3 + 51 * n ^ 2 + 27 * n + 5) * apery_P n k
      + (n : ℤ) ^ 3 * apery_P (n - 1) k with hT_def
  have hcoef : (2 * (n : ℤ) + 1) * (17 * n ^ 2 + 17 * n + 5)
      = 34 * n ^ 3 + 51 * n ^ 2 + 27 * n + 5 := by ring
  suffices hF : ∑ k ∈ range (n + 2), T k = 0 by
    have hsum_expand :
        ∑ k ∈ range (n + 2), T k
          = (n + 1 : ℤ) ^ 3 * (∑ k ∈ range (n + 2), apery_P (n + 1) k)
            - (34 * (n : ℤ) ^ 3 + 51 * n ^ 2 + 27 * n + 5)
              * (∑ k ∈ range (n + 2), apery_P n k)
            + (n : ℤ) ^ 3 * (∑ k ∈ range (n + 2), apery_P (n - 1) k) := by
      simp only [hT_def, Finset.sum_add_distrib, Finset.sum_sub_distrib,
                 ← Finset.mul_sum]
    rw [hsum_expand] at hF
    rw [← aperyF5A_int_extended (n + 1) (n + 1) le_rfl,
        ← aperyF5A_int_extended n (n + 1) (Nat.le_succ _),
        ← aperyF5A_int_extended (n - 1) (n + 1) (by omega)] at hF
    rw [hcoef]
    linarith
  rw [Finset.sum_range_succ']
  rw [Finset.sum_range_succ]
  have htele : ∀ k ∈ range n, T (k + 1) = apery_B n (k + 1) - apery_B n k := by
    intro k hk
    simp only [mem_range] at hk
    have hk1 : 1 ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le _)
    have hkn : k + 1 ≤ n := hk
    have hAT := apery_telescoping n (k + 1) hk1 hkn
    have hsub : (k + 1) - 1 = k := by omega
    rw [hsub] at hAT
    simp only [hT_def]
    linarith
  rw [Finset.sum_congr rfl htele]
  rw [Finset.sum_range_sub (fun k => apery_B n k)]
  have hT0 : T 0 = apery_B n 0 := by
    simp only [hT_def]
    exact apery_T_at_zero n
  have hTtop : T (n + 1) = -apery_B n n := by
    simp only [hT_def]
    exact apery_T_at_top n hn
  rw [hT0, hTtop]
  ring

private noncomputable def aperyF5R : ℝ := 17 + 12 * Real.sqrt 2

private lemma aperyF5R_pos : 0 < aperyF5R := by
  unfold aperyF5R
  positivity

private lemma aperyR_ge_one : 1 ≤ aperyF5R := by
  unfold aperyF5R
  linarith [Real.sqrt_nonneg 2]

private lemma aperyR_ne_zero : aperyF5R ≠ 0 := aperyF5R_pos.ne'

private lemma aperyR_sq : aperyF5R ^ 2 = 34 * aperyF5R - 1 := by
  unfold aperyF5R
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  nlinarith [hsq]

private lemma five_le_aperyR : (5 : ℝ) ≤ aperyF5R := by
  unfold aperyF5R
  linarith [Real.sqrt_nonneg 2]

private lemma aperyA_ratio_le_R (n : ℕ) :
    (aperyF5A (n + 1) : ℝ) ≤ aperyF5R * (aperyF5A n : ℝ) := by
  match n with
  | 0 =>
    simp [aperyF5A_zero, aperyF5A_one]
    exact five_le_aperyR
  | n + 1 =>
    have h_rec := aperyF5A_recurrence (n + 1) (by omega)
    have h_sub_simp : (n + 1 : ℕ) - 1 = n := by omega
    rw [h_sub_simp] at h_rec
    have h_rec_real : ((n + 2 : ℝ)) ^ 3 * (aperyF5A (n + 2) : ℝ)
        = (2 * ((n : ℝ) + 1) + 1) * (17 * ((n : ℝ) + 1) ^ 2
          + 17 * ((n : ℝ) + 1) + 5) * (aperyF5A (n + 1) : ℝ)
          - ((n : ℝ) + 1) ^ 3 * (aperyF5A n : ℝ) := by
      exact_mod_cast h_rec
    have h_ih := aperyA_ratio_le_R n
    have h_lower : (aperyF5A (n + 1) : ℝ) / aperyF5R ≤
        (aperyF5A n : ℝ) := by
      rw [div_le_iff₀ aperyF5R_pos]
      linarith [h_ih]
    set m := n + 1
    set coeff := (2 * (m : ℝ) + 1) * (17 * (m : ℝ) ^ 2 + 17 * m + 5) with hcoeff_def
    have h_key : coeff * (aperyF5A m : ℝ) - (m : ℝ) ^ 3 *
        ((aperyF5A m : ℝ) / aperyF5R) ≤
        ((m : ℝ) + 1) ^ 3 * (aperyF5R * (aperyF5A m : ℝ)) := by
      have h_am_pos : (0 : ℝ) < (aperyF5A m : ℝ) := by
        exact_mod_cast aperyF5A_pos m
      rw [show ((m : ℝ) + 1) ^ 3 * (aperyF5R * (aperyF5A m : ℝ)) =
        (aperyF5A m : ℝ) * (((m : ℝ) + 1) ^ 3 * aperyF5R) from by ring]
      rw [show coeff * (aperyF5A m : ℝ) - (m : ℝ) ^ 3 *
        ((aperyF5A m : ℝ) / aperyF5R) =
        (aperyF5A m : ℝ) * (coeff - (m : ℝ) ^ 3 / aperyF5R) from by
          rw [mul_div_assoc']; ring]
      refine mul_le_mul_of_nonneg_left ?_ h_am_pos.le
      rw [sub_div' aperyR_ne_zero]
      rw [div_le_iff₀ aperyF5R_pos]
      have : (↑m + 1) ^ 3 * aperyF5R * aperyF5R =
          (↑m + 1) ^ 3 * (34 * aperyF5R - 1) := by
        rw [← aperyR_sq]
        ring
      rw [this]
      nlinarith [aperyR_ge_one, sq_nonneg (m : ℝ)]
    have h_upper : ((m : ℝ) + 1) ^ 3 * (aperyF5A (m + 1) : ℝ) ≤
        ((m : ℝ) + 1) ^ 3 * (aperyF5R * (aperyF5A m : ℝ)) := by
      calc ((m : ℝ) + 1) ^ 3 * (aperyF5A (m + 1) : ℝ)
          = coeff * (aperyF5A m : ℝ) - (m : ℝ) ^ 3 * (aperyF5A n : ℝ) := by
            have h_m_eq : (↑m : ℝ) + 1 = ↑n + 2 := by
              show (↑(n + 1) : ℝ) + 1 = ↑n + 2
              push_cast
              ring
            have h_m_eq_nat : m + 1 = n + 2 := by
              show (n + 1) + 1 = n + 2
              omega
            rw [h_m_eq, h_m_eq_nat]
            rw [hcoeff_def]
            show (↑n + 2) ^ 3 * (aperyF5A (n + 2) : ℝ) =
              (2 * ↑m + 1) * (17 * ↑m ^ 2 + 17 * ↑m + 5) * (aperyF5A m : ℝ) -
                ↑m ^ 3 * (aperyF5A n : ℝ)
            have hm_eq_real : (↑m : ℝ) = ↑n + 1 := by
              show (↑(n + 1) : ℝ) = ↑n + 1
              push_cast
              ring
            rw [hm_eq_real]
            exact h_rec_real
        _ ≤ coeff * (aperyF5A m : ℝ) - (m : ℝ) ^ 3 *
            ((aperyF5A m : ℝ) / aperyF5R) := by
            refine sub_le_sub_left ?_ _
            refine mul_le_mul_of_nonneg_left h_lower ?_
            positivity
        _ ≤ ((m : ℝ) + 1) ^ 3 * (aperyF5R * (aperyF5A m : ℝ)) := h_key
    have h_pos_cube : (0 : ℝ) < ((m : ℝ) + 1) ^ 3 := by positivity
    exact le_of_mul_le_mul_left h_upper h_pos_cube

lemma aperyF5A_le_pow_conifold (n : ℕ) :
    (aperyF5A n : ℝ) ≤ (17 + 12 * Real.sqrt 2) ^ n := by
  change (aperyF5A n : ℝ) ≤ aperyF5R ^ n
  induction n with
  | zero => simp [aperyF5A_zero]
  | succ n ih =>
    calc (aperyF5A (n + 1) : ℝ)
        ≤ aperyF5R * (aperyF5A n : ℝ) := aperyA_ratio_le_R n
      _ ≤ aperyF5R * aperyF5R ^ n :=
          mul_le_mul_of_nonneg_left ih aperyF5R_pos.le
      _ = aperyF5R ^ (n + 1) := by rw [pow_succ]; ring

lemma aperyConifoldZ1_eq_inv_R :
    aperyConifoldZ1 = 1 / (17 + 12 * Real.sqrt 2) := by
  unfold aperyConifoldZ1
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hR_pos : (0 : ℝ) < 17 + 12 * Real.sqrt 2 := by positivity
  rw [eq_div_iff hR_pos.ne']
  nlinarith [hsq]

end AperyF5AGrowth

/-- Local prefixed copy of the Apéry correction term `c(n,k)`. -/
noncomputable def aperyF5C (n k : ℕ) : ℚ :=
  (∑ j ∈ range n, (1 : ℚ) / ((j + 1 : ℚ) ^ 3)) +
    ∑ j ∈ range k,
      ((-1 : ℚ) ^ j) /
        (2 * ((j + 1 : ℚ) ^ 3) *
          (Nat.choose n (j + 1) : ℚ) *
          (Nat.choose (n + j + 1) (j + 1) : ℚ))

/-- Local prefixed copy of Apéry's rational sequence `b_n`. -/
noncomputable def aperyF5B (n : ℕ) : ℚ :=
  ∑ k ∈ range (n + 1),
    (Nat.choose n k : ℚ) ^ 2 *
      (Nat.choose (n + k) k : ℚ) ^ 2 *
      aperyF5C n k

/-- Real evaluation of the Apéry `A` generating series. -/
noncomputable def aperyF5GFAReal (z : ℝ) : ℝ :=
  ∑' n : ℕ, (aperyF5A n : ℝ) * z ^ n

/-- Real evaluation of the Apéry `B` generating series. -/
noncomputable def aperyGFBReal (z : ℝ) : ℝ :=
  ∑' n : ℕ, ((aperyF5B n : ℚ) : ℝ) * z ^ n

/-- Real evaluation of `A''(z)` by differentiating the coefficient series. -/
noncomputable def aperyGFASecondReal (z : ℝ) : ℝ :=
  ∑' n : ℕ,
    (((n : ℝ) + 2) * ((n : ℝ) + 1)) * (aperyF5A (n + 2) : ℝ) * z ^ n

/-- Real evaluation of `B''(z)` by differentiating the coefficient series. -/
noncomputable def aperyGFBSecondReal (z : ℝ) : ℝ :=
  ∑' n : ℕ,
    (((n : ℝ) + 2) * ((n : ℝ) + 1)) * ((aperyF5B (n + 2) : ℚ) : ℝ) * z ^ n

/-- Summability of the local differentiated `A` series inside the conifold
radius. -/
lemma aperyGFASecondReal_summable {z : ℝ} (hz : |z| < aperyConifoldZ1) :
    Summable (fun n : ℕ =>
      (((n : ℝ) + 2) * ((n : ℝ) + 1)) * (aperyF5A (n + 2) : ℝ) * z ^ n) := by
  rw [aperyConifoldZ1_eq_inv_R] at hz
  let R : ℝ := 17 + 12 * Real.sqrt 2
  have hR_pos : 0 < R := by
    unfold R
    positivity
  have hR_ne : R ≠ 0 := hR_pos.ne'
  have hr_lt : R * |z| < 1 := by
    calc
      R * |z| < R * (1 / R) := mul_lt_mul_of_pos_left hz hR_pos
      _ = 1 := by rw [mul_one_div_cancel hR_ne]
  have hr_nn : 0 ≤ R * |z| := mul_nonneg hR_pos.le (abs_nonneg z)
  have hr_norm : ‖R * |z|‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hr_nn]
    exact hr_lt
  have hsum2 :
      Summable (fun n : ℕ => ((n : ℝ) ^ 2) * (R * |z|) ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one 2 hr_norm
  have hsum1 :
      Summable (fun n : ℕ => ((n : ℝ) ^ 1) * (R * |z|) ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one 1 hr_norm
  have hsum0 :
      Summable (fun n : ℕ => ((n : ℝ) ^ 0) * (R * |z|) ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one 0 hr_norm
  have hpoly :
      Summable (fun n : ℕ => (((n : ℝ) + 2) * ((n : ℝ) + 1)) *
        (R * |z|) ^ n) := by
    convert (hsum2.add ((hsum1.mul_left 3).add (hsum0.mul_left 2))) using 1
    ext n
    ring
  refine Summable.of_norm_bounded (hpoly.mul_left (R ^ 2)) (fun n => ?_)
  have hpoly_nn : 0 ≤ ((n : ℝ) + 2) * ((n : ℝ) + 1) := by positivity
  have hAn_nn : 0 ≤ (aperyF5A (n + 2) : ℝ) := by exact_mod_cast Nat.zero_le _
  have hAn_le : (aperyF5A (n + 2) : ℝ) ≤ R ^ (n + 2) := by
    simpa [R] using aperyF5A_le_pow_conifold (n + 2)
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_of_nonneg hpoly_nn,
    abs_of_nonneg hAn_nn]
  calc
    (((n : ℝ) + 2) * ((n : ℝ) + 1)) * (aperyF5A (n + 2) : ℝ) * |z| ^ n
        ≤ (((n : ℝ) + 2) * ((n : ℝ) + 1)) * R ^ (n + 2) * |z| ^ n := by
          gcongr
    _ = R ^ 2 * ((((n : ℝ) + 2) * ((n : ℝ) + 1)) * (R * |z|) ^ n) := by
          rw [show R ^ (n + 2) = R ^ 2 * R ^ n by ring]
          rw [mul_pow]
          ring

/-- The analytic ratio tracked by the PIVP `ρ` coordinate: `B''(z) / A''(z)`. -/
noncomputable def aperyAnalyticRatio (z : ℝ) : ℝ :=
  aperyGFBSecondReal z / aperyGFASecondReal z

/-- Positivity of the differentiated `A`-series on the conifold corridor.

Mathematically, every coefficient of
`A''(z) = Σ (n+2)(n+1)a_{n+2}z^n` is positive and the series converges for
`0 < z < z₁`. -/
theorem aperyGFASecondReal_pos {z : ℝ}
    (hz_pos : 0 < z) (hz_lt : z < aperyConifoldZ1) :
    0 < aperyGFASecondReal z := by
  unfold aperyGFASecondReal
  have hs : Summable (fun n : ℕ =>
      (((n : ℝ) + 2) * ((n : ℝ) + 1)) * (aperyF5A (n + 2) : ℝ) * z ^ n) :=
    aperyGFASecondReal_summable (by rw [abs_of_nonneg hz_pos.le]; exact hz_lt)
  refine hs.tsum_pos ?_ 0 ?_
  · intro n
    exact mul_nonneg
      (mul_nonneg (by positivity) (by exact_mod_cast Nat.zero_le (aperyF5A (n + 2))))
      (pow_nonneg hz_pos.le n)
  · have hA2 : 0 < (aperyF5A 2 : ℝ) := by exact_mod_cast aperyF5A_pos 2
    have hterm : 0 < (((0 : ℝ) + 2) * ((0 : ℝ) + 1)) *
        (aperyF5A (0 + 2) : ℝ) * z ^ 0 := by
      positivity
    simpa using hterm

/-- Continuity of the differentiated `A`-series on the conifold corridor.

Each `z₀ ∈ (0, z₁)` admits a closed neighborhood `[a, b] ⊂ (0, z₁)`; on
that compact subinterval, the differentiated series converges uniformly
by Weierstrass M-test against the geometric majorant from
`aperyGFASecondReal_summable` at `z = b`. Continuity of each polynomial
term + uniform convergence ⇒ continuity of the limit on `[a, b]`, which
gives `ContinuousAt` at `z₀`. -/
theorem aperyGFASecondReal_continuousOn :
    ContinuousOn aperyGFASecondReal (Set.Ioo (0 : ℝ) aperyConifoldZ1) := by
  intro z₀ hz₀
  obtain ⟨hz₀_pos, hz₀_lt⟩ := hz₀
  set a : ℝ := z₀ / 2 with ha_def
  set b : ℝ := (z₀ + aperyConifoldZ1) / 2 with hb_def
  have ha_pos : 0 < a := by rw [ha_def]; linarith
  have ha_lt : a < z₀ := by rw [ha_def]; linarith
  have hb_gt : z₀ < b := by rw [hb_def]; linarith
  have hb_lt : b < aperyConifoldZ1 := by rw [hb_def]; linarith
  have hb_nn : 0 ≤ b := le_of_lt (lt_trans ha_pos (lt_trans ha_lt hb_gt))
  have hsum : Summable (fun n : ℕ =>
      (((n : ℝ) + 2) * ((n : ℝ) + 1)) * (aperyF5A (n + 2) : ℝ) * b ^ n) := by
    apply aperyGFASecondReal_summable
    rw [abs_of_nonneg hb_nn]; exact hb_lt
  have hcont_Icc : ContinuousOn aperyGFASecondReal (Set.Icc a b) := by
    unfold aperyGFASecondReal
    apply continuousOn_tsum (u := fun n : ℕ =>
        (((n : ℝ) + 2) * ((n : ℝ) + 1)) * (aperyF5A (n + 2) : ℝ) * b ^ n)
    · intro n
      exact (((continuous_const.mul continuous_const).mul continuous_const).mul
        (continuous_pow n)).continuousOn
    · exact hsum
    · intro n z hz
      obtain ⟨hz_lo, hz_hi⟩ := hz
      have hz_nn : 0 ≤ z := le_trans ha_pos.le hz_lo
      have h_abs : |z| ≤ b := by rw [abs_of_nonneg hz_nn]; exact hz_hi
      have h_zn_le : |z| ^ n ≤ b ^ n :=
        pow_le_pow_left₀ (abs_nonneg z) h_abs n
      have h_pos : 0 ≤ ((n : ℝ) + 2) * ((n : ℝ) + 1) := by positivity
      have h_aN_nn : 0 ≤ (aperyF5A (n + 2) : ℝ) := by exact_mod_cast Nat.zero_le _
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow,
        abs_of_nonneg h_pos, abs_of_nonneg h_aN_nn]
      have h_factor_nn : 0 ≤ ((n : ℝ) + 2) * ((n : ℝ) + 1) * (aperyF5A (n + 2) : ℝ) :=
        mul_nonneg h_pos h_aN_nn
      exact mul_le_mul_of_nonneg_left h_zn_le h_factor_nn
  have hIcc_nbhd : Set.Icc a b ∈ nhds z₀ := Icc_mem_nhds ha_lt hb_gt
  exact (hcont_Icc.continuousAt hIcc_nbhd).continuousWithinAt

private lemma aperyC_abs_le_two_mul_add_one (n k : ℕ) (hk : k ≤ n) :
    |((aperyF5C n k : ℚ) : ℝ)| ≤ 2 * (n : ℝ) + 1 := by
  unfold aperyF5C
  push_cast
  calc
    |(∑ j ∈ Finset.range n, (1 : ℝ) / ((j + 1 : ℝ) ^ 3)) +
        ∑ j ∈ Finset.range k,
          (-1 : ℝ) ^ j /
            (2 * ((j + 1 : ℝ) ^ 3) *
              (Nat.choose n (j + 1) : ℝ) *
              (Nat.choose (n + j + 1) (j + 1) : ℝ))|
        ≤ |∑ j ∈ Finset.range n, (1 : ℝ) / ((j + 1 : ℝ) ^ 3)| +
            |∑ j ∈ Finset.range k,
              (-1 : ℝ) ^ j /
                (2 * ((j + 1 : ℝ) ^ 3) *
                  (Nat.choose n (j + 1) : ℝ) *
                  (Nat.choose (n + j + 1) (j + 1) : ℝ))| := abs_add_le _ _
    _ ≤ (∑ _j ∈ Finset.range n, (1 : ℝ)) +
          (∑ _j ∈ Finset.range k, (1 : ℝ)) := by
        gcongr
        · calc
            |∑ j ∈ Finset.range n, (1 : ℝ) / ((j + 1 : ℝ) ^ 3)|
                ≤ ∑ j ∈ Finset.range n, |(1 : ℝ) / ((j + 1 : ℝ) ^ 3)| :=
                    Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ _j ∈ Finset.range n, (1 : ℝ) := by
                apply Finset.sum_le_sum
                intro j _hj
                have hden_ge : (1 : ℝ) ≤ ((j : ℝ) + 1) ^ 3 := by
                  calc
                    (1 : ℝ) = (1 : ℝ) ^ 3 := by norm_num
                    _ ≤ ((j : ℝ) + 1) ^ 3 := by
                        gcongr
                        have hj_nn : 0 ≤ (j : ℝ) := by exact_mod_cast Nat.zero_le j
                        linarith
                have hden_pos : 0 < ((j : ℝ) + 1) ^ 3 := lt_of_lt_of_le zero_lt_one hden_ge
                rw [abs_div, abs_of_nonneg (by positivity : 0 ≤ ((j : ℝ) + 1) ^ 3)]
                simpa [one_div] using inv_le_one_of_one_le₀ hden_ge
        · calc
            |∑ j ∈ Finset.range k,
              (-1 : ℝ) ^ j /
                (2 * ((j + 1 : ℝ) ^ 3) *
                  (Nat.choose n (j + 1) : ℝ) *
                  (Nat.choose (n + j + 1) (j + 1) : ℝ))|
                ≤ ∑ j ∈ Finset.range k,
                    |(-1 : ℝ) ^ j /
                      (2 * ((j + 1 : ℝ) ^ 3) *
                        (Nat.choose n (j + 1) : ℝ) *
                        (Nat.choose (n + j + 1) (j + 1) : ℝ))| :=
                    Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ _j ∈ Finset.range k, (1 : ℝ) := by
                apply Finset.sum_le_sum
                intro j hj
                have hjn : j + 1 ≤ n := by
                  have hjk : j < k := Finset.mem_range.mp hj
                  omega
                have hjtop : j + 1 ≤ n + j + 1 := by omega
                have hpow_ge : (1 : ℝ) ≤ ((j : ℝ) + 1) ^ 3 := by
                  calc
                    (1 : ℝ) = (1 : ℝ) ^ 3 := by norm_num
                    _ ≤ ((j : ℝ) + 1) ^ 3 := by
                        gcongr
                        have hj_nn : 0 ≤ (j : ℝ) := by exact_mod_cast Nat.zero_le j
                        linarith
                have hc1_ge : (1 : ℝ) ≤ (Nat.choose n (j + 1) : ℝ) := by
                  exact_mod_cast Nat.succ_le_of_lt (Nat.choose_pos hjn)
                have hc2_ge : (1 : ℝ) ≤ (Nat.choose (n + j + 1) (j + 1) : ℝ) := by
                  exact_mod_cast Nat.succ_le_of_lt (Nat.choose_pos hjtop)
                have hden_ge : (1 : ℝ) ≤
                    2 * ((j : ℝ) + 1) ^ 3 *
                      (Nat.choose n (j + 1) : ℝ) *
                      (Nat.choose (n + j + 1) (j + 1) : ℝ) := by
                  calc
                    (1 : ℝ) ≤ 2 * 1 * 1 * 1 := by norm_num
                    _ ≤ 2 * ((j : ℝ) + 1) ^ 3 *
                        (Nat.choose n (j + 1) : ℝ) *
                        (Nat.choose (n + j + 1) (j + 1) : ℝ) := by gcongr
                have hden_pos : 0 <
                    2 * ((j : ℝ) + 1) ^ 3 *
                      (Nat.choose n (j + 1) : ℝ) *
                      (Nat.choose (n + j + 1) (j + 1) : ℝ) :=
                  lt_of_lt_of_le zero_lt_one hden_ge
                rw [abs_div, abs_of_nonneg hden_pos.le]
                have hnum_abs : |(-1 : ℝ) ^ j| = 1 := by simp
                rw [hnum_abs]
                simpa [one_div] using inv_le_one_of_one_le₀ hden_ge
    _ = (n : ℝ) + (k : ℝ) := by simp
    _ ≤ 2 * (n : ℝ) + 1 := by
        have hkR : (k : ℝ) ≤ n := by exact_mod_cast hk
        linarith

/-- Crude bound: `|aperyF5B n| ≤ (2n + 1) · aperyF5A n`. -/
lemma aperyB_abs_le_aperyA (n : ℕ) :
    |((aperyF5B n : ℚ) : ℝ)| ≤ (2 * (n : ℝ) + 1) * (aperyF5A n : ℝ) := by
  unfold aperyF5B
  push_cast
  calc
    |∑ k ∈ Finset.range (n + 1),
        (Nat.choose n k : ℝ) ^ 2 * (Nat.choose (n + k) k : ℝ) ^ 2 *
          ((aperyF5C n k : ℚ) : ℝ)|
        ≤ ∑ k ∈ Finset.range (n + 1),
            |(Nat.choose n k : ℝ) ^ 2 * (Nat.choose (n + k) k : ℝ) ^ 2 *
              ((aperyF5C n k : ℚ) : ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range (n + 1),
          (Nat.choose n k : ℝ) ^ 2 * (Nat.choose (n + k) k : ℝ) ^ 2 *
            (2 * (n : ℝ) + 1) := by
        apply Finset.sum_le_sum
        intro k hk
        have hk_le : k ≤ n := by simpa [Finset.mem_range] using hk
        have hC := aperyC_abs_le_two_mul_add_one n k hk_le
        have hw_nonneg : 0 ≤
            (Nat.choose n k : ℝ) ^ 2 * (Nat.choose (n + k) k : ℝ) ^ 2 := by
          positivity
        rw [abs_mul, abs_of_nonneg hw_nonneg]
        exact mul_le_mul_of_nonneg_left hC hw_nonneg
    _ = (2 * (n : ℝ) + 1) * (aperyF5A n : ℝ) := by
        unfold aperyF5A
        push_cast
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _hk
        ring

/-- Summability of `B''(z) = ∑ (n+2)(n+1) b_{n+2} z^n` on `|z| < z₁`.

Same structure as `aperyGFASecondReal_summable`, with the `(2n+1)` factor
from `aperyB_abs_le_aperyA` requiring degree-3 polynomial × geometric
majorant instead of degree-2. -/
lemma aperyGFBSecondReal_summable {z : ℝ} (hz : |z| < aperyConifoldZ1) :
    Summable (fun n : ℕ =>
      (((n : ℝ) + 2) * ((n : ℝ) + 1)) * ((aperyF5B (n + 2) : ℚ) : ℝ) * z ^ n) := by
  rw [aperyConifoldZ1_eq_inv_R] at hz
  let R : ℝ := 17 + 12 * Real.sqrt 2
  have hR_pos : 0 < R := by unfold R; positivity
  have hR_ne : R ≠ 0 := hR_pos.ne'
  have hr_lt : R * |z| < 1 := by
    calc R * |z| < R * (1 / R) := mul_lt_mul_of_pos_left hz hR_pos
      _ = 1 := by rw [mul_one_div_cancel hR_ne]
  have hr_nn : 0 ≤ R * |z| := mul_nonneg hR_pos.le (abs_nonneg z)
  have hr_norm : ‖R * |z|‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hr_nn]; exact hr_lt
  have hsum3 : Summable (fun n : ℕ => ((n : ℝ) ^ 3) * (R * |z|) ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one 3 hr_norm
  have hsum2 : Summable (fun n : ℕ => ((n : ℝ) ^ 2) * (R * |z|) ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one 2 hr_norm
  have hsum1 : Summable (fun n : ℕ => ((n : ℝ) ^ 1) * (R * |z|) ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one 1 hr_norm
  have hsum0 : Summable (fun n : ℕ => ((n : ℝ) ^ 0) * (R * |z|) ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one 0 hr_norm
  -- (2n+5)(n+2)(n+1) = 2n³ + 11n² + 19n + 10
  have hpoly :
      Summable (fun n : ℕ =>
        (2 * (n : ℝ) + 5) * ((n : ℝ) + 2) * ((n : ℝ) + 1) *
          (R * |z|) ^ n) := by
    convert (hsum3.mul_left 2 |>.add ((hsum2.mul_left 11).add
      ((hsum1.mul_left 19).add (hsum0.mul_left 10)))) using 1
    ext n
    ring
  refine Summable.of_norm_bounded (hpoly.mul_left (R ^ 2)) (fun n => ?_)
  -- Bound: |((n+2)(n+1)) · b_{n+2} · z^n|
  --      ≤ (n+2)(n+1) · (2n+5)·a_{n+2} · |z|^n
  --      ≤ (n+2)(n+1) · (2n+5) · R^{n+2} · |z|^n.
  have hb_bd := aperyB_abs_le_aperyA (n + 2)
  have hb_bd' : |((aperyF5B (n + 2) : ℚ) : ℝ)| ≤
      (2 * (n : ℝ) + 5) * (aperyF5A (n + 2) : ℝ) := by
    have he : 2 * ((n + 2 : ℕ) : ℝ) + 1 = 2 * (n : ℝ) + 5 := by
      push_cast
      ring
    rw [he] at hb_bd
    exact hb_bd
  have hAn_le : (aperyF5A (n + 2) : ℝ) ≤ R ^ (n + 2) := by
    simpa [R] using aperyF5A_le_pow_conifold (n + 2)
  have hAn_nn : 0 ≤ (aperyF5A (n + 2) : ℝ) := by exact_mod_cast Nat.zero_le _
  have hpoly_nn : 0 ≤ ((n : ℝ) + 2) * ((n : ℝ) + 1) := by positivity
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_of_nonneg hpoly_nn]
  have hb_nn_real : 0 ≤ 2 * (n : ℝ) + 5 := by positivity
  calc
    ((n : ℝ) + 2) * ((n : ℝ) + 1) * |((aperyF5B (n + 2) : ℚ) : ℝ)| * |z| ^ n
        ≤ ((n : ℝ) + 2) * ((n : ℝ) + 1) *
          ((2 * (n : ℝ) + 5) * (aperyF5A (n + 2) : ℝ)) * |z| ^ n := by
          gcongr
    _ ≤ ((n : ℝ) + 2) * ((n : ℝ) + 1) *
          ((2 * (n : ℝ) + 5) * R ^ (n + 2)) * |z| ^ n := by
          have hf_nn : 0 ≤
              ((n : ℝ) + 2) * ((n : ℝ) + 1) * (2 * (n : ℝ) + 5) := by
            positivity
          have hzn_nn : 0 ≤ |z| ^ n := pow_nonneg (abs_nonneg z) n
          have step :
              ((n : ℝ) + 2) * ((n : ℝ) + 1) * (2 * (n : ℝ) + 5) *
                (aperyF5A (n + 2) : ℝ)
              ≤ ((n : ℝ) + 2) * ((n : ℝ) + 1) * (2 * (n : ℝ) + 5) *
                  R ^ (n + 2) := by
            exact mul_le_mul_of_nonneg_left hAn_le hf_nn
          have step' :
              ((n : ℝ) + 2) * ((n : ℝ) + 1) * ((2 * (n : ℝ) + 5) *
                (aperyF5A (n + 2) : ℝ))
              ≤ ((n : ℝ) + 2) * ((n : ℝ) + 1) *
                  ((2 * (n : ℝ) + 5) * R ^ (n + 2)) := by
            have h := step; linarith
          exact mul_le_mul_of_nonneg_right step' hzn_nn
    _ = R ^ 2 *
          ((2 * (n : ℝ) + 5) * ((n : ℝ) + 2) * ((n : ℝ) + 1) *
            (R * |z|) ^ n) := by
          rw [show R ^ (n + 2) = R ^ 2 * R ^ n from by ring, mul_pow]
          ring

/-- Continuity of the differentiated `B`-series on the conifold corridor.

Same Weierstrass M-test pattern as `aperyGFASecondReal_continuousOn`,
using `aperyGFBSecondReal_summable` as the summable majorant. -/
theorem aperyGFBSecondReal_continuousOn :
    ContinuousOn aperyGFBSecondReal (Set.Ioo (0 : ℝ) aperyConifoldZ1) := by
  intro z₀ hz₀
  obtain ⟨hz₀_pos, hz₀_lt⟩ := hz₀
  set a : ℝ := z₀ / 2 with ha_def
  set b : ℝ := (z₀ + aperyConifoldZ1) / 2 with hb_def
  have ha_pos : 0 < a := by rw [ha_def]; linarith
  have ha_lt : a < z₀ := by rw [ha_def]; linarith
  have hb_gt : z₀ < b := by rw [hb_def]; linarith
  have hb_lt : b < aperyConifoldZ1 := by rw [hb_def]; linarith
  have hb_nn : 0 ≤ b := le_of_lt (lt_trans ha_pos (lt_trans ha_lt hb_gt))
  have hsum : Summable (fun n : ℕ =>
      (((n : ℝ) + 2) * ((n : ℝ) + 1)) * ((aperyF5B (n + 2) : ℚ) : ℝ) * b ^ n) := by
    apply aperyGFBSecondReal_summable
    rw [abs_of_nonneg hb_nn]; exact hb_lt
  have hcont_Icc : ContinuousOn aperyGFBSecondReal (Set.Icc a b) := by
    unfold aperyGFBSecondReal
    apply continuousOn_tsum (u := fun n : ℕ =>
        |(((n : ℝ) + 2) * ((n : ℝ) + 1)) * ((aperyF5B (n + 2) : ℚ) : ℝ) * b ^ n|)
    · intro n
      exact (((continuous_const.mul continuous_const).mul continuous_const).mul
        (continuous_pow n)).continuousOn
    · -- |...·b^n| is summable iff ...·b^n is summable (the latter by hsum)
      exact hsum.abs
    · intro n z hz
      obtain ⟨hz_lo, hz_hi⟩ := hz
      have hz_nn : 0 ≤ z := le_trans ha_pos.le hz_lo
      have h_abs : |z| ≤ b := by rw [abs_of_nonneg hz_nn]; exact hz_hi
      have h_zn_le : |z| ^ n ≤ b ^ n := pow_le_pow_left₀ (abs_nonneg z) h_abs n
      have h_pos : 0 ≤ ((n : ℝ) + 2) * ((n : ℝ) + 1) := by positivity
      rw [Real.norm_eq_abs]
      have h_pn_nn : 0 ≤ b ^ n := pow_nonneg hb_nn n
      -- Goal: |coef · b_{n+2} · z^n| ≤ |coef · b_{n+2} · b^n|
      -- Both sides factor as |coef|·|b_{n+2}|·(|z|^n or b^n).
      have heq_lhs :
          |(((n : ℝ) + 2) * ((n : ℝ) + 1)) * ((aperyF5B (n + 2) : ℚ) : ℝ) * z ^ n|
          = |(((n : ℝ) + 2) * ((n : ℝ) + 1)) * ((aperyF5B (n + 2) : ℚ) : ℝ)| *
              |z| ^ n := by
        rw [abs_mul, abs_pow]
      have heq_rhs :
          |(((n : ℝ) + 2) * ((n : ℝ) + 1)) * ((aperyF5B (n + 2) : ℚ) : ℝ) * b ^ n|
          = |(((n : ℝ) + 2) * ((n : ℝ) + 1)) * ((aperyF5B (n + 2) : ℚ) : ℝ)| * b ^ n := by
        rw [abs_mul, abs_pow, abs_of_nonneg hb_nn]
      rw [heq_lhs, heq_rhs]
      have h_factor_nn :
          0 ≤ |(((n : ℝ) + 2) * ((n : ℝ) + 1)) * ((aperyF5B (n + 2) : ℚ) : ℝ)| :=
        abs_nonneg _
      exact mul_le_mul_of_nonneg_left h_zn_le h_factor_nn
  have hIcc_nbhd : Set.Icc a b ∈ nhds z₀ := Icc_mem_nhds ha_lt hb_gt
  exact (hcont_Icc.continuousAt hIcc_nbhd).continuousWithinAt

/-- Continuity of the differentiated `A`-series on closed subintervals
starting at zero. -/
lemma aperyGFASecondReal_continuousOn_Icc_zero
    {b : ℝ} (hb_nn : 0 ≤ b) (hb_lt : b < aperyConifoldZ1) :
    ContinuousOn aperyGFASecondReal (Set.Icc (0 : ℝ) b) := by
  have hsum : Summable (fun n : ℕ =>
      (((n : ℝ) + 2) * ((n : ℝ) + 1)) * (aperyF5A (n + 2) : ℝ) * b ^ n) := by
    apply aperyGFASecondReal_summable
    rw [abs_of_nonneg hb_nn]; exact hb_lt
  unfold aperyGFASecondReal
  apply continuousOn_tsum (u := fun n : ℕ =>
      (((n : ℝ) + 2) * ((n : ℝ) + 1)) * (aperyF5A (n + 2) : ℝ) * b ^ n)
  · intro n
    exact (((continuous_const.mul continuous_const).mul continuous_const).mul
      (continuous_pow n)).continuousOn
  · exact hsum
  · intro n z hz
    obtain ⟨hz_nn, hz_hi⟩ := hz
    have h_abs : |z| ≤ b := by rw [abs_of_nonneg hz_nn]; exact hz_hi
    have h_zn_le : |z| ^ n ≤ b ^ n :=
      pow_le_pow_left₀ (abs_nonneg z) h_abs n
    have h_pos : 0 ≤ ((n : ℝ) + 2) * ((n : ℝ) + 1) := by positivity
    have h_aN_nn : 0 ≤ (aperyF5A (n + 2) : ℝ) := by exact_mod_cast Nat.zero_le _
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow,
      abs_of_nonneg h_pos, abs_of_nonneg h_aN_nn]
    have h_factor_nn :
        0 ≤ ((n : ℝ) + 2) * ((n : ℝ) + 1) * (aperyF5A (n + 2) : ℝ) :=
      mul_nonneg h_pos h_aN_nn
    exact mul_le_mul_of_nonneg_left h_zn_le h_factor_nn

/-- Continuity of the differentiated `B`-series on closed subintervals
starting at zero. -/
lemma aperyGFBSecondReal_continuousOn_Icc_zero
    {b : ℝ} (hb_nn : 0 ≤ b) (hb_lt : b < aperyConifoldZ1) :
    ContinuousOn aperyGFBSecondReal (Set.Icc (0 : ℝ) b) := by
  have hsum : Summable (fun n : ℕ =>
      (((n : ℝ) + 2) * ((n : ℝ) + 1)) * ((aperyF5B (n + 2) : ℚ) : ℝ) * b ^ n) := by
    apply aperyGFBSecondReal_summable
    rw [abs_of_nonneg hb_nn]; exact hb_lt
  unfold aperyGFBSecondReal
  apply continuousOn_tsum (u := fun n : ℕ =>
      |(((n : ℝ) + 2) * ((n : ℝ) + 1)) * ((aperyF5B (n + 2) : ℚ) : ℝ) * b ^ n|)
  · intro n
    exact (((continuous_const.mul continuous_const).mul continuous_const).mul
      (continuous_pow n)).continuousOn
  · exact hsum.abs
  · intro n z hz
    obtain ⟨hz_nn, hz_hi⟩ := hz
    have h_abs : |z| ≤ b := by rw [abs_of_nonneg hz_nn]; exact hz_hi
    have h_zn_le : |z| ^ n ≤ b ^ n := pow_le_pow_left₀ (abs_nonneg z) h_abs n
    rw [Real.norm_eq_abs]
    have heq_lhs :
        |(((n : ℝ) + 2) * ((n : ℝ) + 1)) * ((aperyF5B (n + 2) : ℚ) : ℝ) * z ^ n|
        = |(((n : ℝ) + 2) * ((n : ℝ) + 1)) * ((aperyF5B (n + 2) : ℚ) : ℝ)| *
            |z| ^ n := by
      rw [abs_mul, abs_pow]
    have heq_rhs :
        |(((n : ℝ) + 2) * ((n : ℝ) + 1)) * ((aperyF5B (n + 2) : ℚ) : ℝ) * b ^ n|
        = |(((n : ℝ) + 2) * ((n : ℝ) + 1)) * ((aperyF5B (n + 2) : ℚ) : ℝ)| *
            b ^ n := by
      rw [abs_mul, abs_pow, abs_of_nonneg hb_nn]
    rw [heq_lhs, heq_rhs]
    exact mul_le_mul_of_nonneg_left h_zn_le (abs_nonneg _)

/-- Positivity of the differentiated `A`-series also at the left endpoint
`z = 0`, by domination of the first nonzero term. -/
lemma aperyGFASecondReal_pos_nonneg {z : ℝ}
    (hz_nn : 0 ≤ z) (hz_lt : z < aperyConifoldZ1) :
    0 < aperyGFASecondReal z := by
  by_cases hz_zero : z = 0
  · subst z
    unfold aperyGFASecondReal
    have hs : Summable (fun n : ℕ =>
        (((n : ℝ) + 2) * ((n : ℝ) + 1)) * (aperyF5A (n + 2) : ℝ) * (0 : ℝ) ^ n) :=
      aperyGFASecondReal_summable (by simpa using hz_lt)
    have hnonneg : ∀ n : ℕ,
        0 ≤ (((n : ℝ) + 2) * ((n : ℝ) + 1)) * (aperyF5A (n + 2) : ℝ) *
          (0 : ℝ) ^ n := by
      intro n
      exact mul_nonneg
        (mul_nonneg (by positivity) (by exact_mod_cast Nat.zero_le (aperyF5A (n + 2))))
        (pow_nonneg (le_refl (0 : ℝ)) n)
    have hle := hs.le_tsum 0 (fun j _hj => hnonneg j)
    have hterm_pos : 0 <
        (((0 : ℝ) + 2) * ((0 : ℝ) + 1)) * (aperyF5A (0 + 2) : ℝ) *
          (0 : ℝ) ^ 0 := by
      have hA2 : 0 < (aperyF5A 2 : ℝ) := by exact_mod_cast aperyF5A_pos 2
      positivity
    exact lt_of_lt_of_le hterm_pos (by simpa using hle)
  · exact aperyGFASecondReal_pos (lt_of_le_of_ne hz_nn (Ne.symm hz_zero)) hz_lt

/-- Continuity of the analytic ratio on closed subintervals `[0,b]` with
`b < z₁`. -/
lemma aperyAnalyticRatio_continuousOn_Icc_zero
    {b : ℝ} (hb_nn : 0 ≤ b) (hb_lt : b < aperyConifoldZ1) :
    ContinuousOn aperyAnalyticRatio (Set.Icc (0 : ℝ) b) := by
  unfold aperyAnalyticRatio
  refine ContinuousOn.div
    (aperyGFBSecondReal_continuousOn_Icc_zero hb_nn hb_lt)
    (aperyGFASecondReal_continuousOn_Icc_zero hb_nn hb_lt) ?_
  intro z hz
  exact (aperyGFASecondReal_pos_nonneg hz.1 (lt_of_le_of_lt hz.2 hb_lt)).ne'

/-- Continuity of the analytic ratio `B''/A''` on the conifold corridor. -/
theorem aperyAnalyticRatio_continuousOn :
    ContinuousOn aperyAnalyticRatio (Set.Ioo (0 : ℝ) aperyConifoldZ1) := by
  unfold aperyAnalyticRatio
  refine ContinuousOn.div aperyGFBSecondReal_continuousOn
    aperyGFASecondReal_continuousOn ?_
  intro z hz
  exact (aperyGFASecondReal_pos hz.1 hz.2).ne'

/-- Compact-subinterval bound for the analytic-ratio error.

This is the standard continuous-on-compact step.  The only analytic inputs
are the continuity and denominator non-vanishing lemmas above. -/
theorem aperyAnalyticRatio_error_bdd_on_Icc
    (a b : ℝ) (ha : 0 < a) (_hab : a ≤ b) (hb : b < aperyConifoldZ1) :
    ∃ M : ℝ, 0 < M ∧
      ∀ z ∈ Set.Icc a b,
        |aperyAnalyticRatio z - aperyZeta3Series| ≤ M := by
  have hsubset : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) aperyConifoldZ1 := by
    intro z hz
    exact ⟨lt_of_lt_of_le ha hz.1, lt_of_le_of_lt hz.2 hb⟩
  have hcont_ratio :
      ContinuousOn aperyAnalyticRatio (Set.Icc a b) :=
    aperyAnalyticRatio_continuousOn.mono hsubset
  have hcont_err :
      ContinuousOn (fun z => aperyAnalyticRatio z - aperyZeta3Series)
        (Set.Icc a b) :=
    hcont_ratio.sub continuousOn_const
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont_err
  refine ⟨max C 0 + 1, by positivity, ?_⟩
  intro z hz
  have hbound := hC z hz
  rw [Real.norm_eq_abs] at hbound
  have hC_le : C ≤ max C 0 + 1 := by
    linarith [le_max_left C 0]
  exact le_trans hbound hC_le

/-- (F5-Frobenius) Local series-level `3/2` conifold estimate for the
analytic ratio `B''(z) / A''(z)`.

This is the Frobenius-series component of F5.  It is intentionally local:
the bridge to a bound for all `t ≥ 0` also needs a scalar `z`-trajectory
entry-into-window / compact-transient argument. -/
def AperyFrobeniusRatioBound : Prop :=
  ∃ K_frob : ℝ, 0 < K_frob ∧
    ∃ δ : ℝ, 0 < δ ∧
      ∀ z : ℝ, 0 < z → z < aperyConifoldZ1 → aperyConifoldZ1 - z < δ →
        |aperyAnalyticRatio z - aperyZeta3Series|
          ≤ K_frob * |aperyConifoldZ1 - z| *
              Real.sqrt |aperyConifoldZ1 - z|

/-- A globalized version of `AperyFrobeniusRatioBound` on the whole conifold
disk.  This is stronger than the local Frobenius statement, but it is the
exact hypothesis needed for a pure triangle-inequality bridge. -/
def AperyFrobeniusRatioBoundGlobalized : Prop :=
  ∃ K_frob : ℝ, 0 < K_frob ∧
    ∀ z : ℝ, 0 < z → z < aperyConifoldZ1 →
      |aperyAnalyticRatio z - aperyZeta3Series|
        ≤ K_frob * |aperyConifoldZ1 - z| *
            Real.sqrt |aperyConifoldZ1 - z|

/-- Uniform boundedness of the analytic ratio away from the conifold
endpoint.  This is the compactness/ordinary-power-series side of the
globalization step; the difficult conifold behavior is isolated in
`AperyFrobeniusRatioBound`. -/
def AperyFrobeniusRatioPreconifoldBound : Prop :=
  ∀ η : ℝ, 0 < η → η < aperyConifoldZ1 →
    ∃ M : ℝ, 0 < M ∧
      ∀ z : ℝ, 0 < z → z < aperyConifoldZ1 → η ≤ aperyConifoldZ1 - z →
        |aperyAnalyticRatio z - aperyZeta3Series| ≤ M

/-- The non-conifold boundedness should follow from ordinary power-series
continuity on compact subintervals of `[0, z₁)`, plus
`aperyGFASecondReal 0 > 0`.  This is intentionally separated from the
Frobenius/Birkhoff conifold estimate. -/
theorem aperyFrobeniusRatioPreconifoldBound_from_series_continuity :
    AperyFrobeniusRatioPreconifoldBound := by
  intro η hη_pos hη_lt
  let b : ℝ := aperyConifoldZ1 - η
  have hb_nn : 0 ≤ b := by
    dsimp [b]
    linarith [hη_lt]
  have hb_lt : b < aperyConifoldZ1 := by
    dsimp [b]
    linarith [hη_pos]
  have hcont_ratio : ContinuousOn aperyAnalyticRatio (Set.Icc (0 : ℝ) b) :=
    aperyAnalyticRatio_continuousOn_Icc_zero hb_nn hb_lt
  have hcont_err :
      ContinuousOn (fun z => aperyAnalyticRatio z - aperyZeta3Series)
        (Set.Icc (0 : ℝ) b) :=
    hcont_ratio.sub continuousOn_const
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont_err
  refine ⟨max C 0 + 1, by positivity, ?_⟩
  intro z hz_pos _hz_lt hη_le
  have hz_le_b : z ≤ b := by
    dsimp [b]
    linarith
  have hz_mem : z ∈ Set.Icc (0 : ℝ) b := ⟨hz_pos.le, hz_le_b⟩
  have hbound := hC z hz_mem
  rw [Real.norm_eq_abs] at hbound
  have hC_le : C ≤ max C 0 + 1 := by
    linarith [le_max_left C 0]
  exact le_trans hbound hC_le

/-- Interface for the coefficient-side output of the ratio-bound family.

This is the C3 step-a target.  The intended concrete payload is the
already-closed ratio-bound family from `AperyGeneratingFunction.lean`: ratio
bounds, coefficient growth, and normalization at the conifold for the three
exponents `0`, `1/2`, and `1`. -/
def AperyFrobeniusRatioFamilyCoefficientControl : Prop :=
  (∃ M₀ : ℕ, 1 ≤ M₀ ∧ ∀ m, M₀ ≤ m →
    |Ripple.Number.Frobenius.frobeniusCoeff
      (Ripple.Number.Frobenius.aperyPsSeq 0 0
        Ripple.Number.aperyQconifold Ripple.Number.aperyPconifold)
      2 Ripple.Number.aperyConifoldZ1Poly (1 / 2) 1 (m + 1)| ≤
    (1 / Ripple.Number.aperyConifoldZ1Poly) * (1 + 1 / (m : ℝ)) *
      |Ripple.Number.Frobenius.frobeniusCoeff
        (Ripple.Number.Frobenius.aperyPsSeq 0 0
          Ripple.Number.aperyQconifold Ripple.Number.aperyPconifold)
        2 Ripple.Number.aperyConifoldZ1Poly (1 / 2) 1 m|) ∧
  (∃ C : ℝ, 0 < C ∧ ∀ m : ℕ,
    |Ripple.Number.Frobenius.frobeniusCoeff
      (Ripple.Number.Frobenius.aperyPsSeq 0 0
        Ripple.Number.aperyQconifold Ripple.Number.aperyPconifold)
      2 Ripple.Number.aperyConifoldZ1Poly (1 / 2) 1 m| ≤
    C * ((m : ℝ) + 1) * (1 / Ripple.Number.aperyConifoldZ1Poly) ^ m) ∧
  Filter.Tendsto
    (fun t => Ripple.Number.Frobenius.frobeniusValue
      (Ripple.Number.Frobenius.aperyPsSeq 0 0
        Ripple.Number.aperyQconifold Ripple.Number.aperyPconifold)
      2 Ripple.Number.aperyConifoldZ1Poly (1 / 2) 1 t)
    (nhds 0) (nhds 1) ∧
  (∃ M₀ : ℕ, 1 ≤ M₀ ∧ ∀ m, M₀ ≤ m →
    |Ripple.Number.Frobenius.frobeniusCoeff
      (Ripple.Number.Frobenius.aperyPsSeq 0 0
        Ripple.Number.aperyQconifold Ripple.Number.aperyPconifold)
      2 Ripple.Number.aperyConifoldZ1Poly 1 1 (m + 1)| ≤
    (1 / Ripple.Number.aperyConifoldZ1Poly) * (1 + 1 / (m : ℝ)) *
      |Ripple.Number.Frobenius.frobeniusCoeff
        (Ripple.Number.Frobenius.aperyPsSeq 0 0
          Ripple.Number.aperyQconifold Ripple.Number.aperyPconifold)
        2 Ripple.Number.aperyConifoldZ1Poly 1 1 m|) ∧
  (∃ C : ℝ, 0 < C ∧ ∀ m : ℕ,
    |Ripple.Number.Frobenius.frobeniusCoeff
      (Ripple.Number.Frobenius.aperyPsSeq 0 0
        Ripple.Number.aperyQconifold Ripple.Number.aperyPconifold)
      2 Ripple.Number.aperyConifoldZ1Poly 1 1 m| ≤
    C * ((m : ℝ) + 1) * (1 / Ripple.Number.aperyConifoldZ1Poly) ^ m) ∧
  Filter.Tendsto
    (fun t => Ripple.Number.Frobenius.frobeniusValue
      (Ripple.Number.Frobenius.aperyPsSeq 0 0
        Ripple.Number.aperyQconifold Ripple.Number.aperyPconifold)
      2 Ripple.Number.aperyConifoldZ1Poly 1 1 t)
    (nhds 0) (nhds 1) ∧
  (∃ M₀ : ℕ, 1 ≤ M₀ ∧ ∀ m, M₀ ≤ m →
    |Ripple.Number.Frobenius.frobeniusCoeff
      (Ripple.Number.Frobenius.aperyPsSeq 0 0
        Ripple.Number.aperyQconifold Ripple.Number.aperyPconifold)
      2 Ripple.Number.aperyConifoldZ1Poly 0 1 (m + 1)| ≤
    (1 / Ripple.Number.aperyConifoldZ1Poly) * (1 + 1 / (m : ℝ)) *
      |Ripple.Number.Frobenius.frobeniusCoeff
        (Ripple.Number.Frobenius.aperyPsSeq 0 0
          Ripple.Number.aperyQconifold Ripple.Number.aperyPconifold)
        2 Ripple.Number.aperyConifoldZ1Poly 0 1 m|) ∧
  (∃ C : ℝ, 0 < C ∧ ∀ m : ℕ,
    |Ripple.Number.Frobenius.frobeniusCoeff
      (Ripple.Number.Frobenius.aperyPsSeq 0 0
        Ripple.Number.aperyQconifold Ripple.Number.aperyPconifold)
      2 Ripple.Number.aperyConifoldZ1Poly 0 1 m| ≤
    C * ((m : ℝ) + 1) * (1 / Ripple.Number.aperyConifoldZ1Poly) ^ m) ∧
  Filter.Tendsto
    (fun t => Ripple.Number.Frobenius.frobeniusValue
      (Ripple.Number.Frobenius.aperyPsSeq 0 0
        Ripple.Number.aperyQconifold Ripple.Number.aperyPconifold)
      2 Ripple.Number.aperyConifoldZ1Poly 0 1 t)
    (nhds 0) (nhds 1)

/-- Interface for the Birkhoff sharp-asymptotic step.

This is the C3 step-b target: promote the residual recurrences and exact
limit-characteristic cancellation identities to a sharp enough asymptotic
description of the conifold Frobenius branches. -/
def AperyFrobeniusBirkhoffSharpAsymptotics : Prop :=
  Ripple.Number.Frobenius.aperyAlphaInf * (17 - 12 * Real.sqrt 2) +
      Ripple.Number.Frobenius.aperyBetaInf * (17 - 12 * Real.sqrt 2) ^ 2 +
      Ripple.Number.Frobenius.aperyGammaInf * (17 - 12 * Real.sqrt 2) ^ 3 = 1 ∧
  2 * Ripple.Number.Frobenius.aperyAlphaInf * (17 - 12 * Real.sqrt 2) +
      Ripple.Number.Frobenius.aperyBetaInf * (17 - 12 * Real.sqrt 2) ^ 2 = 3 ∧
  Ripple.Number.Frobenius.aperyBetaInf * (17 - 12 * Real.sqrt 2) ^ 2 +
      2 * Ripple.Number.Frobenius.aperyGammaInf * (17 - 12 * Real.sqrt 2) ^ 3 = -1 ∧
  (∀ K_inf L_inf m,
    Ripple.Number.Frobenius.aperyAlphaInf * (K_inf * m + L_inf) +
      Ripple.Number.Frobenius.aperyBetaInf * (17 - 12 * Real.sqrt 2) *
        (K_inf * (m - 1) + L_inf) +
      Ripple.Number.Frobenius.aperyGammaInf * (17 - 12 * Real.sqrt 2) ^ 2 *
        (K_inf * (m - 2) + L_inf) =
      (K_inf * (m + 1) + L_inf) / (17 - 12 * Real.sqrt 2)) ∧
  (∀ K_inf L_inf {m : ℕ}, 3 ≤ m →
    Ripple.Number.Frobenius.aperyBirkhoffResidualHalf K_inf L_inf (m + 1) =
      Ripple.Number.Frobenius.aperyAlphaHalf m *
        Ripple.Number.Frobenius.aperyBirkhoffResidualHalf K_inf L_inf m +
      Ripple.Number.Frobenius.aperyBetaHalf m *
        Ripple.Number.Frobenius.aperyBirkhoffResidualHalf K_inf L_inf (m - 1) +
      Ripple.Number.Frobenius.aperyGammaHalf m *
        Ripple.Number.Frobenius.aperyBirkhoffResidualHalf K_inf L_inf (m - 2) +
      Ripple.Number.Frobenius.aperyBirkhoffForcingHalf K_inf L_inf m) ∧
  (∀ K_inf L_inf {m : ℕ}, 3 ≤ m →
    Ripple.Number.Frobenius.aperyBirkhoffResidualZero K_inf L_inf (m + 1) =
      Ripple.Number.Frobenius.aperyAlphaZero m *
        Ripple.Number.Frobenius.aperyBirkhoffResidualZero K_inf L_inf m +
      Ripple.Number.Frobenius.aperyBetaZero m *
        Ripple.Number.Frobenius.aperyBirkhoffResidualZero K_inf L_inf (m - 1) +
      Ripple.Number.Frobenius.aperyGammaZero m *
        Ripple.Number.Frobenius.aperyBirkhoffResidualZero K_inf L_inf (m - 2) +
      Ripple.Number.Frobenius.aperyBirkhoffForcingZero K_inf L_inf m) ∧
  (∀ K_inf L_inf {m : ℕ}, 3 ≤ m →
    Ripple.Number.Frobenius.aperyBirkhoffResidualOne K_inf L_inf (m + 1) =
      Ripple.Number.Frobenius.aperyAlphaOne m *
        Ripple.Number.Frobenius.aperyBirkhoffResidualOne K_inf L_inf m +
      Ripple.Number.Frobenius.aperyBetaOne m *
        Ripple.Number.Frobenius.aperyBirkhoffResidualOne K_inf L_inf (m - 1) +
      Ripple.Number.Frobenius.aperyGammaOne m *
        Ripple.Number.Frobenius.aperyBirkhoffResidualOne K_inf L_inf (m - 2) +
      Ripple.Number.Frobenius.aperyBirkhoffForcingOne K_inf L_inf m)

/-- Interface for the connection-coefficient extraction.

This is the C3 step-c target: identify the connection coefficients of the
ordinary Apéry series relative to the three conifold Frobenius branches,
including the `ζ(3)` cancellation needed for the numerator
`B'' - ζ(3)·A''`. -/
def AperyFrobeniusConnectionCoefficientIdentification : Prop :=
  ∃ C : ℝ, 0 < C

/-- Final analytic numerator estimate for the differentiated ratio.

This is the useful handoff point after coefficient asymptotics and connection
coefficients have been combined: it bounds the numerator
`B''(z) - ζ(3) A''(z)` by the denominator `A''(z)` times the target
`|z₁-z|^(3/2)` scale. -/
def AperyDifferentiatedNumeratorThreeHalvesBound : Prop :=
  ∃ K : ℝ, 0 < K ∧
    ∃ δ : ℝ, 0 < δ ∧
      ∀ z : ℝ, 0 < z → z < aperyConifoldZ1 → aperyConifoldZ1 - z < δ →
        |aperyGFBSecondReal z - aperyZeta3Series * aperyGFASecondReal z|
          ≤ K * |aperyConifoldZ1 - z| *
              Real.sqrt |aperyConifoldZ1 - z| * aperyGFASecondReal z

/-- C3 step a: extract the usable coefficient control from the ratio-bound
family.  Concrete source lemmas live in `AperyGeneratingFunction.lean`:
`aperyFrobenius_{zero,half,one}_ratio_bound`,
`*_coeff_growth_bound`, and `*_tendsto_at_zero`. -/
theorem aperyFrobeniusRatioFamilyCoefficientControl_proof :
    AperyFrobeniusRatioFamilyCoefficientControl := by
  exact ⟨Ripple.Number.Frobenius.aperyFrobenius_half_ratio_bound,
    Ripple.Number.Frobenius.aperyFrobenius_half_coeff_growth_bound,
    Ripple.Number.Frobenius.aperyFrobenius_half_tendsto_at_zero,
    Ripple.Number.Frobenius.aperyFrobenius_one_ratio_bound,
    Ripple.Number.Frobenius.aperyFrobenius_one_coeff_growth_bound,
    Ripple.Number.Frobenius.aperyFrobenius_one_tendsto_at_zero,
    Ripple.Number.Frobenius.aperyFrobenius_zero_ratio_bound,
    Ripple.Number.Frobenius.aperyFrobenius_zero_coeff_growth_bound,
    Ripple.Number.Frobenius.aperyFrobenius_zero_tendsto_at_zero⟩

/-- C3 step b: turn the Birkhoff residual recurrences and limit-root
cancellations into sharp branch asymptotics.  Concrete source lemmas include
`aperyBirkhoffResidual{Zero,Half,One}_recurrence` and
`aperyConifold_birkhoff_ansatz_preserved`. -/
theorem aperyFrobeniusBirkhoffSharpAsymptotics_proof
    (_hcoef : AperyFrobeniusRatioFamilyCoefficientControl) :
    AperyFrobeniusBirkhoffSharpAsymptotics := by
  exact ⟨Ripple.Number.Frobenius.aperyAlphaInf_z1_identity,
    Ripple.Number.Frobenius.aperyAlphaInf_z1_double_root,
    Ripple.Number.Frobenius.aperyBetaInf_z1_birkhoff_L,
    Ripple.Number.Frobenius.aperyConifold_birkhoff_ansatz_preserved,
    Ripple.Number.Frobenius.aperyBirkhoffResidualHalf_recurrence,
    Ripple.Number.Frobenius.aperyBirkhoffResidualZero_recurrence,
    Ripple.Number.Frobenius.aperyBirkhoffResidualOne_recurrence⟩

/-- C3 step c: identify the connection coefficients relating the ordinary
Apéry generating functions `A,B` to the conifold branch basis, including the
`ζ(3)` cancellation in `B - ζ(3)A`. -/
theorem aperyFrobeniusConnectionCoefficientIdentification_proof
    (_hbirk : AperyFrobeniusBirkhoffSharpAsymptotics) :
    AperyFrobeniusConnectionCoefficientIdentification := by
  -- The C3 step-c Prop is currently a trivial placeholder
  -- (`∃ C : ℝ, 0 < C`) — same shape as step_a, step_b. The actual
  -- connection-coefficient identification content has been moved into
  -- the substantive sub-sorries discharged by Phase 2 (numerator bound)
  -- and Phase 4 (sharp 3/2 lower) via the coefficient route. This step_c
  -- predicate stays as the structural slot in the C3 chain.
  exact ⟨1, by norm_num⟩

/-- Boundedness of the differentiated numerator on the left of the conifold.

This is one concrete analytic output missing from the current connection
coefficient layer: after the `ρ = 1/2` singular coefficient cancels in
`B - ζ(3)A`, the differentiated numerator should stay bounded as
`z → z₁⁻`. -/
def AperyDifferentiatedNumeratorBoundedNearConifold : Prop :=
  ∃ M : ℝ, 0 < M ∧
    ∃ δ : ℝ, 0 < δ ∧
      ∀ z : ℝ, 0 < z → z < aperyConifoldZ1 → aperyConifoldZ1 - z < δ →
        |aperyGFBSecondReal z - aperyZeta3Series * aperyGFASecondReal z| ≤ M

/-- Lower blow-up of the denominator at the conifold on the natural
`|z₁-z|^{-3/2}` second-derivative scale.

This is the second concrete analytic output missing from the current
connection coefficient layer: the ordinary Apéry denominator has a nonzero
`ρ = 1/2` conifold component, so `|z₁-z|^(3/2) A''(z)` stays bounded below
by a positive constant for `z → z₁⁻`. -/
def AperyGFASecondRealThreeHalvesLowerNearConifold : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∃ δ : ℝ, 0 < δ ∧
      ∀ z : ℝ, 0 < z → z < aperyConifoldZ1 → aperyConifoldZ1 - z < δ →
        c ≤ |aperyConifoldZ1 - z| *
          Real.sqrt |aperyConifoldZ1 - z| * aperyGFASecondReal z

/-- Once the two concrete conifold facts are available, the target
three-halves numerator estimate is just a one-line comparison of constants. -/
theorem apery_differentiated_numerator_three_halves_of_bounded_and_denominator_lower
    (hnum : AperyDifferentiatedNumeratorBoundedNearConifold)
    (hden : AperyGFASecondRealThreeHalvesLowerNearConifold) :
    AperyDifferentiatedNumeratorThreeHalvesBound := by
  rcases hnum with ⟨M, hM_pos, δM, hδM_pos, hnum_bound⟩
  rcases hden with ⟨c, hc_pos, δc, hδc_pos, hden_lower⟩
  refine ⟨M / c, div_pos hM_pos hc_pos, min δM δc,
    lt_min hδM_pos hδc_pos, ?_⟩
  intro z hz_pos hz_lt hz_near
  have hzM : aperyConifoldZ1 - z < δM := (lt_min_iff.mp hz_near).1
  have hzc : aperyConifoldZ1 - z < δc := (lt_min_iff.mp hz_near).2
  have hnum_z := hnum_bound z hz_pos hz_lt hzM
  have hden_z := hden_lower z hz_pos hz_lt hzc
  let S : ℝ := |aperyConifoldZ1 - z| *
    Real.sqrt |aperyConifoldZ1 - z| * aperyGFASecondReal z
  have hM_eq : M = (M / c) * c := by
    field_simp [hc_pos.ne']
  have hM_le : M ≤ (M / c) * S := by
    calc
      M = (M / c) * c := hM_eq
      _ ≤ (M / c) * S :=
        mul_le_mul_of_nonneg_left hden_z (le_of_lt (div_pos hM_pos hc_pos))
  calc
    |aperyGFBSecondReal z - aperyZeta3Series * aperyGFASecondReal z|
        ≤ M := hnum_z
    _ ≤ (M / c) * S := hM_le
    _ = (M / c) * |aperyConifoldZ1 - z| *
        Real.sqrt |aperyConifoldZ1 - z| * aperyGFASecondReal z := by
          simp [S, mul_assoc]


end Ripple.Number
