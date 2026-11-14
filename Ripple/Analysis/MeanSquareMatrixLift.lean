import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd

/-! Deterministic finite matrices acting on vectors in any real normed space. -/
noncomputable section
open scoped BigOperators Topology

namespace Ripple.Analysis.MeanSquareVolterra

variable {d : ℕ} {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- The ordinary finite matrix action with real scalar multiplication in `H`. -/
def matrixLift (A : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) :
    (Fin d → H) →L[ℝ] (Fin d → H) :=
  ∑ i, ∑ j, (A (Pi.single j 1) i) •
    ((ContinuousLinearMap.single ℝ (fun _ : Fin d => H) i).comp
      (ContinuousLinearMap.proj j))

@[simp] theorem matrixLift_apply (A : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ))
    (x : Fin d → H) (i : Fin d) :
    matrixLift A x i = ∑ j, (A (Pi.single j 1) i) • x j := by
  classical
  simp [matrixLift, Pi.single_apply]

 theorem matrix_apply (A : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ))
    (x : Fin d → ℝ) (i : Fin d) :
    A x i = ∑ j, A (Pi.single j 1) i * x j := by
  have hx : (∑ j, x j • Pi.single j (1 : ℝ)) = x := by
    ext j
    simp [Pi.single_apply]
  calc
    _ = A (∑ j, x j • Pi.single j 1) i := by rw [hx]
    _ = _ := by simp [mul_comm]

/-- The lifted matrix varies continuously with its real entries. -/
theorem continuous_matrixLift {S : Type*} [TopologicalSpace S]
    {A : S → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)} (hA : Continuous A) :
    Continuous (fun s => matrixLift (H := H) (A s)) := by
  unfold matrixLift
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro j _
  exact (((continuous_apply i).comp (hA.clm_apply continuous_const)).smul continuous_const)

/-- A dimension-times-operator-norm bound is sufficient for Volterra uniqueness. -/
theorem norm_matrixLift_le (A : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) :
    ‖matrixLift (H := H) A‖ ≤ (d : ℝ) * ‖A‖ := by
  classical
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))
  intro x
  apply (pi_norm_le_iff_of_nonneg
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)) (norm_nonneg _))).2
  intro i
  rw [matrixLift_apply]
  have hentry (j : Fin d) : ‖A (Pi.single j (1 : ℝ)) i‖ ≤ ‖A‖ := by
    have hsingle : ‖(Pi.single j (1 : ℝ) : Fin d → ℝ)‖ ≤ 1 := by
      apply (pi_norm_le_iff_of_nonneg zero_le_one).2
      intro k
      simp only [Pi.single_apply]
      split_ifs <;> norm_num
    exact (norm_le_pi_norm _ i).trans
      (((A.le_opNorm _).trans (mul_le_mul_of_nonneg_left hsingle (norm_nonneg _))).trans
        (by rw [mul_one]))
  calc
    _ ≤ ∑ j, ‖(A (Pi.single j 1) i) • x j‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin d, ‖A‖ * ‖x‖ := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_smul]
      exact mul_le_mul (hentry j) (norm_le_pi_norm x j) (norm_nonneg _) (norm_nonneg _)
    _ = ((d : ℝ) * ‖A‖) * ‖x‖ := by simp [mul_assoc]

end Ripple.Analysis.MeanSquareVolterra
