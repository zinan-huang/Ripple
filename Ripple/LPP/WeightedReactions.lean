/-
  Ripple.LPP.WeightedReactions

  Finite rational 2-in/2-out reaction families as conservative quadratic
  coefficient tensors.  This is the coefficient language used by the
  symmetric Stage-3 transfer lift.
-/

import Ripple.LPP.QuadraticToSynPP

namespace Ripple

/-- A finite family of rationally weighted ordered 2-in/2-out reactions. -/
structure WeightedReactions (n m : ℕ) where
  in1 : Fin m → Fin n
  in2 : Fin m → Fin n
  out1 : Fin m → Fin n
  out2 : Fin m → Fin n
  rate : Fin m → ℚ
  rate_nonneg : ∀ a, 0 ≤ rate a

namespace WeightedReactions

variable {n m : ℕ} (R : WeightedReactions n m)

/-- Net stoichiometric coefficient of state `r` in reaction `a`. -/
def delta (a : Fin m) (r : Fin n) : ℚ :=
  (if r = R.out1 a then 1 else 0) + (if r = R.out2 a then 1 else 0) -
    (if r = R.in1 a then 1 else 0) - (if r = R.in2 a then 1 else 0)

theorem sum_delta (a : Fin m) : ∑ r, R.delta a r = 0 := by
  simp [delta, Finset.sum_add_distrib, Finset.sum_sub_distrib]

/-- Full-balance coefficient tensor induced by the weighted reactions. -/
def coeff (r i j : Fin n) : ℚ :=
  ∑ a, if R.in1 a = i ∧ R.in2 a = j then R.rate a * R.delta a r else 0

theorem sum_coeff_zero (i j : Fin n) : ∑ r, R.coeff r i j = 0 := by
  simp only [coeff]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro a _
  by_cases h : R.in1 a = i ∧ R.in2 a = j
  · simp [h, ← Finset.mul_sum, R.sum_delta]
  · simp [h]

/-- The conservative quadratic field represented by `R`. -/
def toQuadField : QuadField n where
  coeff := R.coeff
  sum_zero := R.sum_coeff_zero

theorem toQuadField_transferCompatible : R.toQuadField.TransferCompatible := by
  intro r i j hri hrj
  simp only [toQuadField, coeff]
  apply Finset.sum_nonneg
  intro a _
  by_cases h : R.in1 a = i ∧ R.in2 a = j
  · rw [if_pos h]
    rcases h with ⟨hi, hj⟩
    have hr1 : r ≠ R.in1 a := by simpa [hi] using hri
    have hr2 : r ≠ R.in2 a := by simpa [hj] using hrj
    unfold delta
    simp only [hr1, hr2, if_false, sub_zero]
    exact mul_nonneg (R.rate_nonneg a) (by positivity)
  · rw [if_neg h]

/-- Every reaction consumes two distinct states. -/
def InputsDistinct : Prop := ∀ a, R.in1 a ≠ R.in2 a

/-- Every reaction with nonzero weight consumes two distinct states.
Zero-weight padding reactions are ignored by the induced coefficient tensor. -/
def ActiveInputsDistinct : Prop := ∀ a, R.rate a ≠ 0 → R.in1 a ≠ R.in2 a

theorem inputsDistinct_active (hR : R.InputsDistinct) : R.ActiveInputsDistinct :=
  fun a _ => hR a

/-- Input-distinct reactions have no coefficient on a diagonal input pair. -/
theorem coeff_diag_eq_zero (hR : R.InputsDistinct) (r i : Fin n) :
    R.coeff r i i = 0 := by
  unfold coeff
  apply Finset.sum_eq_zero
  intro a _
  have hnot : ¬ (R.in1 a = i ∧ R.in2 a = i) := by
    rintro ⟨h1, h2⟩
    exact hR a (h1.trans h2.symm)
  simp [hnot]

/-- Diagonal coefficients also vanish when only active reactions have
distinct inputs. This form supports rectangular zero-rate enumeration. -/
theorem coeff_diag_eq_zero_of_active (hR : R.ActiveInputsDistinct) (r i : Fin n) :
    R.coeff r i i = 0 := by
  unfold coeff
  apply Finset.sum_eq_zero
  intro a _
  by_cases hpair : R.in1 a = i ∧ R.in2 a = i
  · have hr0 : R.rate a = 0 := by
      by_contra hr
      exact hR a hr (hpair.1.trans hpair.2.symm)
    simp [hpair, hr0]
  · simp [hpair]

/-- The direct mass-action field of the weighted reaction family. -/
noncomputable def toField (x : Fin n → ℝ) (r : Fin n) : ℝ :=
  ∑ a, (R.rate a : ℝ) * x (R.in1 a) * x (R.in2 a) * (R.delta a r : ℝ)

/-- Every coordinate of the finite mass-action field is continuous. -/
theorem toField_continuous (r : Fin n) :
    Continuous (fun x : Fin n → ℝ ↦ R.toField x r) := by
  unfold toField
  apply continuous_finset_sum
  intro a _
  exact (((continuous_const.mul (continuous_apply (R.in1 a))).mul
    (continuous_apply (R.in2 a))).mul continuous_const)

set_option maxHeartbeats 800000 in
theorem toQuadField_toField : R.toQuadField.toField = R.toField := by
  funext x r
  simp only [QuadField.toField, toQuadField, coeff, toField]
  push_cast
  simp_rw [Finset.sum_mul]
  let f : Fin n → Fin n → Fin m → ℝ := fun i j a =>
    ((if R.in1 a = i ∧ R.in2 a = j
      then R.rate a * R.delta a r else 0 : ℚ) : ℝ) * x i * x j
  have hreorder : (∑ i, ∑ j, ∑ a, f i j a) = ∑ a, ∑ i, ∑ j, f i j a := by
    calc
      (∑ i, ∑ j, ∑ a, f i j a) = ∑ i, ∑ a, ∑ j, f i j a := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
      _ = ∑ a, ∑ i, ∑ j, f i j a := by rw [Finset.sum_comm]
  rw [show (∑ i, ∑ j, ∑ a,
      ((if R.in1 a = i ∧ R.in2 a = j
        then R.rate a * R.delta a r else 0 : ℚ) : ℝ) * x i * x j) =
      ∑ i, ∑ j, ∑ a, f i j a from rfl, hreorder]
  apply Finset.sum_congr rfl
  intro a _
  simp only [f]
  calc
    (∑ i, ∑ j,
        ((if R.in1 a = i ∧ R.in2 a = j
          then R.rate a * R.delta a r else 0 : ℚ) : ℝ) * x i * x j) =
        ∑ i, if R.in1 a = i then
          ((R.rate a * R.delta a r : ℚ) : ℝ) * x i * x (R.in2 a) else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : R.in1 a = i
      · subst i
        rw [Finset.sum_eq_single (R.in2 a)]
        · simp
        · intro j _ hj
          simp [Ne.symm hj]
        · simp
      · simp [hi]
    _ = ((R.rate a * R.delta a r : ℚ) : ℝ) *
          x (R.in1 a) * x (R.in2 a) := by simp
    _ = (R.rate a : ℝ) * x (R.in1 a) * x (R.in2 a) *
          (R.delta a r : ℝ) := by
      push_cast
      ring

/-- The normalized syntactic PP generated by the weighted reactions. -/
noncomputable def toSynPPBalance : SynPPBalance n :=
  R.toQuadField.toSynPPBalance R.toQuadField_transferCompatible

theorem toSynPPBalance_toField :
    R.toSynPPBalance.toField =
      fun x r => R.toQuadField.normalization * R.toField x r := by
  rw [toSynPPBalance, R.toQuadField.toSynPPBalance_toField]
  rw [R.toQuadField_toField]

end WeightedReactions

end Ripple
