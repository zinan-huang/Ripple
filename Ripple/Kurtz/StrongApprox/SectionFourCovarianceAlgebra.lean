import Ripple.Kurtz.StrongApprox.FundamentalMatrixBounds
import Mathlib.Data.Matrix.Mul
import Mathlib.Probability.Moments.Covariance

/-!
# The covariance integrand in channel and matrix coordinates

The finite coordinate spaces carry the sup norm internally. Their Euclidean
pairing is consequently written explicitly as `dotProduct`. This avoids
silently changing the inner product in the paper's covariance identity.
-/

noncomputable section
open scoped BigOperators

namespace Ripple.Kurtz.StrongApprox

variable {m d : ℕ}

/-- The diffusion covariance matrix, formed from the original rate and jump
vectors at the specified state. -/
def sectionFourSigma (f : Fin m → (Fin d → ℝ) → ℝ)
    (v : Fin m → Fin d → ℝ) (x : Fin d → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j => ∑ l, f l x * v l i * v l j

theorem sectionFourSigma_mulVec
    (f : Fin m → (Fin d → ℝ) → ℝ) (v : Fin m → Fin d → ℝ)
    (x z : Fin d → ℝ) :
    (sectionFourSigma f v x).mulVec z =
      ∑ l, (f l x * dotProduct (v l) z) • v l := by
  ext i
  simp only [Matrix.mulVec, dotProduct, sectionFourSigma, Finset.sum_mul,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem dotProduct_transpose_mulVec
    (P : Matrix (Fin d) (Fin d) ℝ) (x y : Fin d → ℝ) :
    dotProduct x (P.transpose.mulVec y) = dotProduct y (P.mulVec x) := by
  simp only [dotProduct, Matrix.mulVec, Matrix.transpose_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The matrix integrand equals the sum over matching noise channels. -/
theorem sectionFourSigma_propagated_pairing
    (f : Fin m → (Fin d → ℝ) → ℝ) (v : Fin m → Fin d → ℝ)
    (x a b : Fin d → ℝ) (P Q : Matrix (Fin d) (Fin d) ℝ) :
    dotProduct a ((P * sectionFourSigma f v x * Q.transpose).mulVec b) =
      ∑ l, f l x * dotProduct a (P.mulVec (v l)) *
        dotProduct b (Q.mulVec (v l)) := by
  have hsum (c : Fin m → ℝ) :
      P.mulVec (∑ l, c l • v l) = ∑ l, c l • P.mulVec (v l) := by
    ext i
    simp only [Matrix.mulVec, dotProduct_sum, Finset.sum_apply,
      dotProduct_smul, Pi.smul_apply]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    sectionFourSigma_mulVec, hsum, dotProduct_sum]
  simp only [dotProduct_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro l _
  rw [dotProduct_transpose_mulVec]
  ring

/-- Square-root coefficients produce the original rate in the quadratic form. -/
theorem sqrt_pairing_product (r c e : ℝ) (hr : 0 ≤ r) :
    (Real.sqrt r * c) * (Real.sqrt r * e) = r * c * e := by
  calc
    _ = (Real.sqrt r) ^ 2 * c * e := by ring
    _ = _ := by rw [Real.sq_sqrt hr]

theorem sectionFourSigma_propagated_entry
    (f : Fin m → (Fin d → ℝ) → ℝ) (v : Fin m → Fin d → ℝ)
    (x : Fin d → ℝ) (P Q : Matrix (Fin d) (Fin d) ℝ) (i j : Fin d) :
    (P * sectionFourSigma f v x * Q.transpose) i j =
      ∑ l, f l x * (P.mulVec (v l)) i * (Q.mulVec (v l)) j := by
  have h := sectionFourSigma_propagated_pairing f v x
    (Pi.single i 1) (Pi.single j 1) P Q
  simp only [single_dotProduct, one_mul, Matrix.mulVec_single_one] at h
  exact h

/-- Relate the bundled evolution to the original columnwise matrix. -/
theorem fundamentalCLM_eq_mulVec
    (A : ℝ → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) (T t s : ℝ) (x : Fin d → ℝ) :
    VolterraGaussian.fundamentalCLM A T t s x =
      (VolterraGaussian.fundamentalMatrix A T t s).mulVec x := by
  ext i
  simp only [VolterraGaussian.fundamentalCLM_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem weighted_entries_eq_pairing
    (a b : Fin d → ℝ) (R : Matrix (Fin d) (Fin d) ℝ) :
    (∑ i, ∑ j, a i * b j * R i j) = dotProduct a (R.mulVec b) := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Pairing covariance is a finite sum of coordinate covariances. -/
theorem covariance_dotProduct
    {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsFiniteMeasure μ]
    {X Y : Ω → Fin d → ℝ}
    (hX : ∀ i, MeasureTheory.MemLp (fun ω => X ω i) 2 μ)
    (hY : ∀ j, MeasureTheory.MemLp (fun ω => Y ω j) 2 μ)
    (a b : Fin d → ℝ) :
    ProbabilityTheory.covariance (fun ω => dotProduct a (X ω))
      (fun ω => dotProduct b (Y ω)) μ =
      ∑ i, ∑ j, a i * b j *
        ProbabilityTheory.covariance (fun ω => X ω i) (fun ω => Y ω j) μ := by
  classical
  simp only [dotProduct]
  rw [ProbabilityTheory.covariance_fun_sum_fun_sum
    (fun i => (hX i).const_mul (a i)) (fun j => (hY j).const_mul (b j))]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [ProbabilityTheory.covariance_const_mul_left, ProbabilityTheory.covariance_const_mul_right]
  ring

end Ripple.Kurtz.StrongApprox
