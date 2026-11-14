import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.CharacteristicFunction

/-!
# Gaussian laws from moment-generating functions

The scalar theorem identifies a real law from its MGF.  The finite-family
results use the scalar theorem on every deterministic linear combination and
then characteristic-function uniqueness on the finite product.
-/

noncomputable section

namespace Ripple.Probability

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

/-- A real random variable whose MGF is that of `N(0,q)` has that law. -/
theorem map_eq_gaussianReal_of_mgf
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Y : Ω → ℝ} {q : ℝ}
    (hY : AEMeasurable Y P) (hq : 0 ≤ q)
    (hInt : ∀ t : ℝ, Integrable (fun ω => Real.exp (t * Y ω)) P)
    (hMGF : ∀ t : ℝ,
      ∫ ω, Real.exp (t * Y ω) ∂P = Real.exp (t ^ 2 * q / 2)) :
    P.map Y = gaussianReal 0 ⟨q, hq⟩ := by
  let variance : ℝ≥0 := ⟨q, hq⟩
  have hmgf : mgf Y P = mgf id (gaussianReal 0 variance) := by
    funext t
    rw [mgf_id_gaussianReal]
    change (∫ ω, Real.exp (t * Y ω) ∂P) =
      Real.exp ((0 : ℝ) * t + (variance : ℝ) * t ^ 2 / 2)
    rw [hMGF t]
    congr 1
    change t ^ 2 * q / 2 = 0 * t + q * t ^ 2 / 2
    ring
  have hset : integrableExpSet Y P = Set.univ := by
    ext t
    simp only [integrableExpSet, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact hInt t
  have hOn := eqOn_complexMGF_of_mgf
    (X := Y) (Y := id) (μ := P) (μ' := gaussianReal 0 variance) hmgf
  have hComplex :
      complexMGF Y P = complexMGF id (gaussianReal 0 variance) := by
    funext z
    apply hOn
    simp [hset]
  simpa [variance] using
    (Measure.ext_of_complexMGF_eq hY aemeasurable_id hComplex)

/-- `HasLaw` wrapper for `map_eq_gaussianReal_of_mgf`. -/
theorem hasLaw_gaussianReal_of_mgf
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Y : Ω → ℝ} {q : ℝ}
    (hY : AEMeasurable Y P) (hq : 0 ≤ q)
    (hInt : ∀ t : ℝ, Integrable (fun ω => Real.exp (t * Y ω)) P)
    (hMGF : ∀ t : ℝ,
      ∫ ω, Real.exp (t * Y ω) ∂P = Real.exp (t ^ 2 * q / 2)) :
    HasLaw Y (gaussianReal 0 ⟨q, hq⟩) P :=
  ⟨hY, map_eq_gaussianReal_of_mgf hY hq hInt hMGF⟩

/-- The variance of a deterministic linear combination of diagonal Gaussian
coordinates. -/
def diagonalVariance {ι : Type*} [Fintype ι]
    (q : ι → ℝ) (hq : ∀ i, 0 ≤ q i) (c : ι → ℝ) : ℝ≥0 :=
  ⟨∑ i, c i ^ 2 * q i,
    Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg (c i)) (hq i)⟩

@[simp]
theorem coe_diagonalVariance {ι : Type*} [Fintype ι]
    (q : ι → ℝ) (hq : ∀ i, 0 ≤ q i) (c : ι → ℝ) :
    (diagonalVariance q hq c : ℝ) = ∑ i, c i ^ 2 * q i := rfl

private theorem real_clm_apply_eq_apply_one_mul
    (A : ℝ →L[ℝ] ℝ) (x : ℝ) : A x = A 1 * x := by
  calc
    A x = A (x • (1 : ℝ)) := by simp [smul_eq_mul]
    _ = x • A 1 := by rw [map_smul]
    _ = A 1 * x := by simp [smul_eq_mul, mul_comm]

section FiniteFamily

variable {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]
  (Y : ι → Ω → ℝ) (q : ι → ℝ)
  (hY : ∀ i, AEMeasurable (Y i) P)
  (hq : ∀ i, 0 ≤ q i)
  (hInt : ∀ t : ι → ℝ,
    Integrable (fun ω => Real.exp (∑ i, t i * Y i ω)) P)
  (hMGF : ∀ t : ι → ℝ,
    ∫ ω, Real.exp (∑ i, t i * Y i ω) ∂P =
      ∏ i, Real.exp (t i ^ 2 * q i / 2))

include hY hq hInt hMGF

/-- Cramér–Wold step: every deterministic linear combination is centered
Gaussian with the diagonal variance. -/
theorem map_weightedSum_eq_gaussianReal_of_joint_mgf (c : ι → ℝ) :
    P.map (fun ω => ∑ i, c i * Y i ω) =
      gaussianReal 0 (diagonalVariance q hq c) := by
  have hMeas : AEMeasurable (fun ω => ∑ i, c i * Y i ω) P := by
    simpa only [Finset.sum_fn] using Finset.aemeasurable_sum (μ := P) Finset.univ
      (fun i _ => (hY i).const_mul (c i))
  have hIntOne (s : ℝ) :
      Integrable (fun ω => Real.exp (s * ∑ i, c i * Y i ω)) P := by
    simpa only [Finset.mul_sum, mul_assoc] using
      hInt (fun i => s * c i)
  have hMGFOne (s : ℝ) :
      ∫ ω, Real.exp (s * ∑ i, c i * Y i ω) ∂P =
        Real.exp (s ^ 2 * (diagonalVariance q hq c : ℝ) / 2) := by
    calc
      (∫ ω, Real.exp (s * ∑ i, c i * Y i ω) ∂P) =
          ∏ i, Real.exp ((s * c i) ^ 2 * q i / 2) := by
        simpa only [Finset.mul_sum, mul_assoc] using
          hMGF (fun i => s * c i)
      _ = Real.exp (∑ i, (s * c i) ^ 2 * q i / 2) := by
        rw [← Real.exp_sum]
      _ = Real.exp (s ^ 2 * (diagonalVariance q hq c : ℝ) / 2) := by
        congr 1
        change (∑ i, (s * c i) ^ 2 * q i / 2) =
          s ^ 2 * (∑ i, c i ^ 2 * q i) / 2
        calc
          (∑ i, (s * c i) ^ 2 * q i / 2) =
              ∑ i, (s ^ 2 / 2) * (c i ^ 2 * q i) := by
            apply Finset.sum_congr rfl
            intro i _
            ring
          _ = (s ^ 2 / 2) * ∑ i, c i ^ 2 * q i := by
            rw [← Finset.mul_sum]
          _ = s ^ 2 * (∑ i, c i ^ 2 * q i) / 2 := by ring
  unfold diagonalVariance
  refine map_eq_gaussianReal_of_mgf hMeas
    (Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg (c i)) (hq i))
    hIntOne ?_
  intro s
  simpa [diagonalVariance] using hMGFOne s

/-- The complete finite-dimensional law is the product of the centered
Gaussian coordinate laws. -/
theorem map_fun_eq_pi_gaussianReal_of_joint_mgf :
    P.map (fun ω i => Y i ω) =
      Measure.pi (fun i => gaussianReal 0 ⟨q i, hq i⟩) := by
  classical
  have hYvec : AEMeasurable (fun ω i => Y i ω) P :=
    aemeasurable_pi_iff.2 hY
  apply (charFunDual_eq_pi_iff
    (E := fun _ : ι => ℝ)
    (μ := fun i => gaussianReal 0 ⟨q i, hq i⟩)
    (ν := P.map (fun ω i => Y i ω))).mp
  intro L
  let c : ι → ℝ := fun i =>
    (L.comp (ContinuousLinearMap.single ℝ (fun _ : ι => ℝ) i)) 1
  have hLApply (x : ι → ℝ) : L x = ∑ i, c i * x i := by
    calc
      L x = ∑ i,
          (L.comp (ContinuousLinearMap.single ℝ (fun _ : ι => ℝ) i)) (x i) := by
        simp [← map_sum, LinearMap.sum_single_apply]
      _ = ∑ i, c i * x i := by
        apply Finset.sum_congr rfl
        intro i _
        simpa [c] using real_clm_apply_eq_apply_one_mul
          (L.comp (ContinuousLinearMap.single ℝ (fun _ : ι => ℝ) i)) (x i)
  have hfun :
      L ∘ (fun ω i => Y i ω) = fun ω => ∑ i, c i * Y i ω := by
    funext ω
    exact hLApply (fun i => Y i ω)
  have hWeighted := map_weightedSum_eq_gaussianReal_of_joint_mgf
    (P := P) Y q hY hq hInt hMGF c
  have hsource :
      charFunDual (P.map (fun ω i => Y i ω)) L =
        Complex.exp ((-(∑ i, c i ^ 2 * q i) / 2 : ℝ) : ℂ) := by
    rw [charFunDual_eq_charFun_map_one,
      AEMeasurable.map_map_of_aemeasurable (by fun_prop) hYvec]
    change charFun (P.map (L ∘ (fun ω i => Y i ω))) 1 = _
    rw [hfun, hWeighted, charFun_gaussianReal]
    congr 1
    simp only [coe_diagonalVariance]
    push_cast
    ring
  have hfactor (i : ι) :
      charFunDual (gaussianReal 0 ⟨q i, hq i⟩)
          (L.comp (ContinuousLinearMap.single ℝ (fun _ : ι => ℝ) i)) =
        Complex.exp ((-(c i ^ 2 * q i) / 2 : ℝ) : ℂ) := by
    have hA (x : ℝ) :
        (L.comp (ContinuousLinearMap.single ℝ (fun _ : ι => ℝ) i)) x =
          c i * x := by
      simpa [c] using real_clm_apply_eq_apply_one_mul
        (L.comp (ContinuousLinearMap.single ℝ (fun _ : ι => ℝ) i)) x
    rw [charFunDual_apply]
    simp_rw [hA]
    change (∫ x, Complex.exp ((c i * x : ℝ) * Complex.I)
      ∂gaussianReal 0 ⟨q i, hq i⟩) = _
    simp_rw [Complex.ofReal_mul]
    rw [← charFun_apply_real, charFun_gaussianReal]
    congr 1
    push_cast
    ring_nf
    rfl
  calc
    charFunDual (P.map (fun ω i => Y i ω)) L =
        Complex.exp ((-(∑ i, c i ^ 2 * q i) / 2 : ℝ) : ℂ) := hsource
    _ = ∏ i, Complex.exp ((-(c i ^ 2 * q i) / 2 : ℝ) : ℂ) := by
      rw [← Complex.exp_sum]
      congr 1
      push_cast
      simp only [neg_div]
      rw [Finset.sum_div, ← Finset.sum_neg_distrib]
    _ = ∏ i, charFunDual (gaussianReal 0 ⟨q i, hq i⟩)
        (L.comp (ContinuousLinearMap.single ℝ (fun _ : ι => ℝ) i)) := by
      apply Finset.prod_congr rfl
      intro i _
      exact (hfactor i).symm

/-- A coordinate marginal of the joint MGF is the corresponding centered
Gaussian law. -/
theorem map_eq_gaussianReal_of_joint_mgf (i : ι) :
    P.map (Y i) = gaussianReal 0 ⟨q i, hq i⟩ := by
  classical
  have hYvec : AEMeasurable (fun ω j => Y j ω) P :=
    aemeasurable_pi_iff.2 hY
  have hJoint := map_fun_eq_pi_gaussianReal_of_joint_mgf
    (P := P) Y q hY hq hInt hMGF
  calc
    P.map (Y i) =
        (P.map (fun ω j => Y j ω)).map (fun x => x i) := by
      rw [AEMeasurable.map_map_of_aemeasurable (measurable_pi_apply i).aemeasurable hYvec]
      rfl
    _ = (Measure.pi (fun j => gaussianReal 0 ⟨q j, hq j⟩)).map
        (fun x => x i) := by rw [hJoint]
    _ = gaussianReal 0 ⟨q i, hq i⟩ :=
      (measurePreserving_eval (fun j => gaussianReal 0 ⟨q j, hq j⟩) i).map_eq

/-- The finite joint-MGF identity gives both the Gaussian marginal laws and
mutual independence. -/
theorem gaussian_marginals_and_iIndepFun_of_joint_mgf :
    (∀ i, P.map (Y i) = gaussianReal 0 ⟨q i, hq i⟩) ∧
      iIndepFun Y P := by
  have hJoint := map_fun_eq_pi_gaussianReal_of_joint_mgf
    (P := P) Y q hY hq hInt hMGF
  have hMarginal : ∀ i, P.map (Y i) = gaussianReal 0 ⟨q i, hq i⟩ :=
    map_eq_gaussianReal_of_joint_mgf (P := P) Y q hY hq hInt hMGF
  refine ⟨hMarginal, (iIndepFun_iff_map_fun_eq_pi_map hY).2 ?_⟩
  simpa only [hMarginal] using hJoint

/-- Independence-only wrapper for the finite-family theorem. -/
theorem iIndepFun_of_joint_mgf : iIndepFun Y P :=
  (gaussian_marginals_and_iIndepFun_of_joint_mgf
    (P := P) Y q hY hq hInt hMGF).2

end FiniteFamily

end Ripple.Probability

end
