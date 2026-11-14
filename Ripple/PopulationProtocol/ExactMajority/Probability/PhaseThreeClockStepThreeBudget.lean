-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockStepThreeBudget.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockRows

/-!
# An allocation matching the compiled virtual-core row split

The four clock-process rows in PhaseThreeClockRows.RowTails (activation,
passage, shape, cap) receive 7/(2*n^5). The Main-credit and complete contact
rows receive 5/(2*n^5). The shares sum to the compiled 6/n^5 core budget.

The separate paper activation-allowance error 2/n^5 is not added to this
row table: rowFailure already intersects AsyncEntry, whose deadline and
advanced profile are part of that event. This statement does not replace
a proof of any RowTails field. In particular, the activation row also asks
for activation_before_twenty and the passage row for fine_raw_local.

These are numerical lemmas only. No probabilistic row, hcore, or
asynchronous_clock_estimate is asserted.
-/

noncomputable section

open scoped ENNReal

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockStepThreeBudget

def stepThreeError (n : ℕ) : ℝ :=
  1 / (n : ℝ) ^ 8 + 1 / (n : ℝ) ^ 8 +
    2 / (n : ℝ) ^ 10 + 3 / (n : ℝ) ^ 5

def remainingCoreError (n : ℕ) : ℝ :=
  1 / (n : ℝ) ^ 29 + (1 / (n : ℝ) ^ 6 + 1 / (n : ℝ) ^ 21)

def stepThreeShare (n : ℕ) : ℝ := 7 / (2 * (n : ℝ) ^ 5)

def remainingCoreShare (n : ℕ) : ℝ := 5 / (2 * (n : ℝ) ^ 5)

theorem reciprocal_power_shift_le {n b : ℕ} (hb : 1 ≤ b) (hbn : b ≤ n)
    (k : ℕ) :
    (1 : ℝ) / (n : ℝ) ^ (5 + k) ≤
      (1 / (b : ℝ) ^ k) * (1 / (n : ℝ) ^ 5) := by
  have hbR : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hbnR : (b : ℝ) ≤ n := by exact_mod_cast hbn
  have hbp : (0 : ℝ) < b := by linarith
  have hnp : (0 : ℝ) < n := by linarith
  have hp : (b : ℝ) ^ k ≤ (n : ℝ) ^ k :=
    pow_le_pow_left₀ hbp.le hbnR k
  have hinv : (1 : ℝ) / (n : ℝ) ^ k ≤ 1 / (b : ℝ) ^ k :=
    one_div_le_one_div_of_le (by positivity) hp
  calc
    (1 : ℝ) / (n : ℝ) ^ (5 + k) =
        (1 / (n : ℝ) ^ k) * (1 / (n : ℝ) ^ 5) := by
      rw [pow_add]
      field_simp [ne_of_gt hnp]
      <;> ring
    _ ≤ (1 / (b : ℝ) ^ k) * (1 / (n : ℝ) ^ 5) :=
      mul_le_mul_of_nonneg_right hinv (by positivity)

theorem stepThreeError_nonneg (n : ℕ) : 0 ≤ stepThreeError n := by
  unfold stepThreeError
  positivity

theorem remainingCoreError_nonneg (n : ℕ) : 0 ≤ remainingCoreError n := by
  unfold remainingCoreError
  positivity

theorem stepThreeShare_nonneg (n : ℕ) : 0 ≤ stepThreeShare n := by
  unfold stepThreeShare
  positivity

theorem remainingCoreShare_nonneg (n : ℕ) : 0 ≤ remainingCoreShare n := by
  unfold remainingCoreShare
  positivity

/-- The four clock-process rows fit in 3.5/n^5 for n at least four. -/
theorem stepThreeError_le_share {n : ℕ} (hn : 4 ≤ n) :
    stepThreeError n ≤ stepThreeShare n := by
  have hheight := reciprocal_power_shift_le (n := n) (b := 4) (by norm_num) hn 3
  have hfront := reciprocal_power_shift_le (n := n) (b := 4) (by norm_num) hn 5
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat] at hheight hfront
  have hnonneg : (0 : ℝ) ≤ 1 / (n : ℝ) ^ 5 := by positivity
  have hshare : stepThreeShare n = (7 / 2 : ℝ) * (1 / (n : ℝ) ^ 5) := by
    unfold stepThreeShare
    ring
  have herr : stepThreeError n =
      3 * (1 / (n : ℝ) ^ 5) + 2 * (1 / (n : ℝ) ^ 8) +
        2 * (1 / (n : ℝ) ^ 10) := by
    unfold stepThreeError
    ring
  rw [hshare, herr]
  norm_num at hheight hfront
  simp only [one_div] at hnonneg ⊢
  linarith

/-- The Main and complete contact rows fit in the remaining allocated share. -/
theorem remainingCoreError_le_share {n : ℕ} (hn : 4 ≤ n) :
    remainingCoreError n ≤ remainingCoreShare n := by
  have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hnp : (0 : ℝ) < n := by linarith
  have hnOne : (1 : ℝ) ≤ n := by linarith
  have hlarge : (1 : ℝ) / (n : ℝ) ^ 29 ≤ 1 / (n : ℝ) ^ 6 :=
    one_div_le_one_div_of_le (by positivity)
      (pow_le_pow_right₀ hnOne (by norm_num : 6 ≤ 29))
  have hcontact : (1 : ℝ) / (n : ℝ) ^ 21 ≤ 1 / (n : ℝ) ^ 6 :=
    one_div_le_one_div_of_le (by positivity)
      (pow_le_pow_right₀ hnOne (by norm_num : 6 ≤ 21))
  have hsmall := reciprocal_power_shift_le (n := n) (b := 4) (by norm_num) hn 1
  norm_num only [Nat.reduceAdd, pow_one, Nat.cast_ofNat] at hsmall
  have hnonneg : (0 : ℝ) ≤ 1 / (n : ℝ) ^ 5 := by positivity
  have hshare : remainingCoreShare n = (5 / 2 : ℝ) * (1 / (n : ℝ) ^ 5) := by
    unfold remainingCoreShare
    ring
  rw [hshare]
  unfold remainingCoreError
  linarith

theorem shares_sum (n : ℕ) :
    stepThreeShare n + remainingCoreShare n = 6 / (n : ℝ) ^ 5 := by
  unfold stepThreeShare remainingCoreShare
  ring

theorem stepThreeError_le_share_ennreal {n : ℕ} (hn : 4 ≤ n) :
    ENNReal.ofReal (1 / (n : ℝ) ^ 8) +
      ENNReal.ofReal (1 / (n : ℝ) ^ 8) +
      ENNReal.ofReal (2 / (n : ℝ) ^ 10) +
      ENNReal.ofReal (3 / (n : ℝ) ^ 5) ≤
        ENNReal.ofReal (stepThreeShare n) := by
  have heq :
      ENNReal.ofReal (stepThreeError n) =
        ENNReal.ofReal (1 / (n : ℝ) ^ 8) +
          ENNReal.ofReal (1 / (n : ℝ) ^ 8) +
          ENNReal.ofReal (2 / (n : ℝ) ^ 10) +
          ENNReal.ofReal (3 / (n : ℝ) ^ 5) := by
    unfold stepThreeError
    repeat rw [ENNReal.ofReal_add (by positivity) (by positivity)]
  rw [← heq]
  exact ENNReal.ofReal_le_ofReal (stepThreeError_le_share hn)

theorem remainingCoreError_le_share_ennreal {n : ℕ} (hn : 4 ≤ n) :
    ENNReal.ofReal (1 / (n : ℝ) ^ 29) +
      ENNReal.ofReal (1 / (n : ℝ) ^ 6 + 1 / (n : ℝ) ^ 21) ≤
        ENNReal.ofReal (remainingCoreShare n) := by
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal (remainingCoreError_le_share hn)

/-- The expression on the left is exactly the six coefficients in
PhaseThreeClockRows.RowTails, with its right-associated row grouping. -/
theorem row_table_eq (n : ℕ) :
    ENNReal.ofReal (1 / (n : ℝ) ^ 8) + (ENNReal.ofReal (1 / (n : ℝ) ^ 8) +
      (ENNReal.ofReal (2 / (n : ℝ) ^ 10) + (ENNReal.ofReal (1 / (n : ℝ) ^ 29) +
      (ENNReal.ofReal (3 / (n : ℝ) ^ 5) +
      ENNReal.ofReal (1 / (n : ℝ) ^ 6 + 1 / (n : ℝ) ^ 21))))) =
      ENNReal.ofReal (stepThreeError n) + ENNReal.ofReal (remainingCoreError n) := by
  unfold stepThreeError remainingCoreError
  repeat rw [ENNReal.ofReal_add (by positivity) (by positivity)]
  ac_rfl

theorem virtual_core_table_le_six {n : ℕ} (hn : 4 ≤ n) :
    ENNReal.ofReal (stepThreeError n) +
      ENNReal.ofReal (remainingCoreError n) ≤
        ENNReal.ofReal (6 / (n : ℝ) ^ 5) := by
  rw [← ENNReal.ofReal_add (stepThreeError_nonneg n) (remainingCoreError_nonneg n)]
  apply ENNReal.ofReal_le_ofReal
  calc
    stepThreeError n + remainingCoreError n ≤
        stepThreeShare n + remainingCoreShare n :=
      add_le_add (stepThreeError_le_share hn) (remainingCoreError_le_share hn)
    _ = _ := shares_sum n

/-- The compiled six-row budget follows from this explicit allocation. -/
theorem row_table_le_six {n : ℕ} (hn : 4 ≤ n) :
    ENNReal.ofReal (1 / (n : ℝ) ^ 8) + (ENNReal.ofReal (1 / (n : ℝ) ^ 8) +
      (ENNReal.ofReal (2 / (n : ℝ) ^ 10) + (ENNReal.ofReal (1 / (n : ℝ) ^ 29) +
      (ENNReal.ofReal (3 / (n : ℝ) ^ 5) +
      ENNReal.ofReal (1 / (n : ℝ) ^ 6 + 1 / (n : ℝ) ^ 21))))) ≤
      ENNReal.ofReal (6 / (n : ℝ) ^ 5) := by
  rw [row_table_eq n]
  exact virtual_core_table_le_six hn

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockStepThreeBudget

end
