/-
  Ripple.LPP.QuadraticToSynPP

  A coefficient-level bridge from conservative quadratic transfer fields to
  syntactic population-protocol balance equations.
-/

import Ripple.LPP.Syntactic

namespace Ripple

namespace QuadField

variable {n : ℕ}

/-- The identity interaction contributes one copy of each input state. -/
def identityCoeff (r i j : Fin n) : ℚ :=
  (if r = i then 1 else 0) + if r = j then 1 else 0

/-- Negative coefficients may only consume one of the two input states. -/
def TransferCompatible (F : QuadField n) : Prop :=
  ∀ r i j, r ≠ i → r ≠ j → 0 ≤ F.coeff r i j

/-- A finite rational bound for every coefficient of `F`. -/
def coeffL1 (F : QuadField n) : ℚ :=
  ∑ p : Fin n × Fin n × Fin n, |F.coeff p.1 p.2.1 p.2.2|

/-- Positive normalization used to turn transfer rates into probabilities. -/
def normalization (F : QuadField n) : ℚ :=
  1 / (F.coeffL1 + 1)

theorem coeffL1_nonneg (F : QuadField n) : 0 ≤ F.coeffL1 := by
  unfold coeffL1
  positivity

theorem coeff_abs_le_coeffL1 (F : QuadField n) (r i j : Fin n) :
    |F.coeff r i j| ≤ F.coeffL1 := by
  unfold coeffL1
  exact Finset.single_le_sum (fun p _ => abs_nonneg (F.coeff p.1 p.2.1 p.2.2))
    (Finset.mem_univ (r, i, j))

theorem normalization_pos (F : QuadField n) : 0 < F.normalization := by
  unfold normalization
  exact div_pos (by norm_num) (by linarith [F.coeffL1_nonneg])

/-- Normalize a conservative transfer-compatible quadratic field into a
`SynPPBalance`. Identity probability fills the unused part of every ordered
input pair. -/
noncomputable def toSynPPBalance (F : QuadField n) (hF : F.TransferCompatible) :
    SynPPBalance n where
  coeff := fun r i j => identityCoeff r i j + F.normalization * F.coeff r i j
  coeff_nonneg := by
    intro r i j
    by_cases hri : r = i
    · have habs := F.coeff_abs_le_coeffL1 r i j
      have hden : 0 < F.coeffL1 + 1 := by linarith [F.coeffL1_nonneg]
      have hlower : -(1 : ℚ) < F.normalization * F.coeff r i j := by
        have hc : -F.coeffL1 ≤ F.coeff r i j :=
          (neg_le_neg habs).trans (neg_abs_le _)
        rw [normalization, one_div, inv_mul_eq_div]
        rw [lt_div_iff₀ hden]
        linarith
      subst r
      have hid : (1 : ℚ) ≤ identityCoeff i i j := by
        unfold identityCoeff
        simp
        split_ifs <;> norm_num
      linarith
    · by_cases hrj : r = j
      · have habs := F.coeff_abs_le_coeffL1 r i j
        have hden : 0 < F.coeffL1 + 1 := by linarith [F.coeffL1_nonneg]
        have hlower : -(1 : ℚ) < F.normalization * F.coeff r i j := by
          have hc : -F.coeffL1 ≤ F.coeff r i j :=
            (neg_le_neg habs).trans (neg_abs_le _)
          rw [normalization, one_div, inv_mul_eq_div]
          rw [lt_div_iff₀ hden]
          linarith
        subst r
        have hid : identityCoeff j i j = (1 : ℚ) := by
          simp [identityCoeff, hri]
        rw [hid]
        linarith
      · simp only [identityCoeff, hri, hrj, if_false, zero_add]
        exact mul_nonneg (le_of_lt F.normalization_pos) (hF r i j hri hrj)
  sum_coeff := by
    intro i j
    simp only [identityCoeff, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [F.sum_zero i j]
    simp only [mul_zero, add_zero]
    norm_num

theorem toSynPPBalance_quadCoeff (F : QuadField n) (hF : F.TransferCompatible)
    (r i j : Fin n) :
    (F.toSynPPBalance hF).quadCoeff r i j = F.normalization * F.coeff r i j := by
  change (identityCoeff r i j + F.normalization * F.coeff r i j) -
      (if i = r then 1 else 0) - (if j = r then 1 else 0) =
    F.normalization * F.coeff r i j
  unfold identityCoeff
  by_cases hir : i = r
  · subst i
    by_cases hjr : j = r
    · subst j; simp; ring
    · have hrj : r ≠ j := Ne.symm hjr
      simp [hjr, hrj]
  · have hri : r ≠ i := Ne.symm hir
    by_cases hjr : j = r
    · subst j; simp [hir, hri]
    · have hrj : r ≠ j := Ne.symm hjr
      simp [hir, hri, hjr, hrj]

/-- The normalized PP field is exactly a positive constant dilation of the
input quadratic field. -/
theorem toSynPPBalance_toField (F : QuadField n) (hF : F.TransferCompatible) :
    (F.toSynPPBalance hF).toField = fun x r => F.normalization * F.toField x r := by
  rw [← (F.toSynPPBalance hF).toQuadField_toField]
  funext x r
  simp only [QuadField.toField, SynPPBalance.toQuadField,
    F.toSynPPBalance_quadCoeff hF]
  simp_rw [Rat.cast_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

end QuadField

end Ripple
