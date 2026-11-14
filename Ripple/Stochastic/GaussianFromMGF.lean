/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Mathlib

/-!
# Independent Gaussian laws from exponential moments

Scalar moment-generating-function uniqueness identifies every real linear
combination. The characteristic function of the resulting diagonal Gaussian
then factors, proving independence of the finite family.

The scalar uniqueness proof and the characteristic-function argument are
adapted from Raphael Coelho's MathFin exponential characterization of Brownian
motion. Only Mathlib is imported; no stochastic-process assumptions are used.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal RealInnerProductSpace

namespace Ripple.Stochastic

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  [IsProbabilityMeasure P]

/-- Exponential moments of a centered Gaussian determine its scalar law,
including the zero-variance case. -/
theorem map_eq_gaussianReal_of_gaussian_mgf {Y : Ω → ℝ} {q : ℝ≥0}
    (hY : AEMeasurable Y P)
    (hmgf : ∀ a : ℝ, ∫ ω, Real.exp (a * Y ω) ∂P =
      Real.exp ((q : ℝ) * a ^ 2 / 2)) :
    P.map Y = gaussianReal 0 q := by
  have heq : mgf Y P = mgf id (gaussianReal 0 q) := by
    rw [mgf_id_gaussianReal]
    funext a
    show ∫ ω, Real.exp (a * Y ω) ∂P =
      Real.exp (0 * a + (q : ℝ) * a ^ 2 / 2)
    rw [hmgf a, zero_mul, zero_add]
  have hIESgauss : integrableExpSet id (gaussianReal 0 q) = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro a
    exact integrable_exp_mul_gaussianReal a
  have hIES : integrableExpSet Y P = Set.univ := by
    rw [integrableExpSet_eq_of_mgf heq, hIESgauss]
  have hset : {z : ℂ | z.re ∈ interior (integrableExpSet Y P)} = Set.univ := by
    rw [hIES, interior_univ]
    ext z
    simp
  have hcomplexeq : complexMGF Y P = complexMGF id (gaussianReal 0 q) := by
    funext z
    exact eqOn_complexMGF_of_mgf heq (hset ▸ Set.mem_univ z)
  have hmap := Measure.ext_of_complexMGF_eq (μ := P) (μ' := gaussianReal 0 q)
    hY aemeasurable_id hcomplexeq
  rwa [Measure.map_id] at hmap

/-- The scalar exponential-moment criterion packaged as `HasLaw`. -/
theorem hasLaw_gaussianReal_of_gaussian_mgf {Y : Ω → ℝ} {q : ℝ≥0}
    (hY : AEMeasurable Y P)
    (hmgf : ∀ a : ℝ, ∫ ω, Real.exp (a * Y ω) ∂P =
      Real.exp ((q : ℝ) * a ^ 2 / 2)) :
    HasLaw Y (gaussianReal 0 q) P where
  aemeasurable := hY
  map_eq := map_eq_gaussianReal_of_gaussian_mgf hY hmgf

section FiniteFamily

variable {κ : Type*} [Fintype κ] {Y : κ → Ω → ℝ} {q : κ → ℝ≥0}

/-- The joint MGF identifies the law of every scalar linear combination. -/
theorem map_linearCombination_eq_gaussianReal_of_mgf
    (hY : ∀ i, Measurable (Y i))
    (hmgf : ∀ θ : κ → ℝ,
      ∫ ω, Real.exp (∑ i, θ i * Y i ω) ∂P =
        Real.exp (∑ i, θ i ^ 2 * (q i : ℝ) / 2))
    (c : κ → ℝ) {v : ℝ≥0}
    (hv : (v : ℝ) = ∑ i, c i ^ 2 * (q i : ℝ)) :
    P.map (fun ω => ∑ i, c i * Y i ω) = gaussianReal 0 v := by
  have hlin : Measurable (fun ω => ∑ i, c i * Y i ω) :=
    Finset.measurable_sum _ (fun i _ => (hY i).const_mul (c i))
  apply map_eq_gaussianReal_of_gaussian_mgf hlin.aemeasurable
  intro r
  have hfun : (fun ω => Real.exp (r * ∑ i, c i * Y i ω)) =
      (fun ω => Real.exp (∑ i, (r * c i) * Y i ω)) := by
    funext ω
    simp only [Finset.mul_sum, mul_assoc]
  rw [hfun, hmgf, hv, Finset.sum_mul, Finset.sum_div]
  exact congrArg Real.exp (Finset.sum_congr rfl (fun i _ => by ring))

/-- Each coordinate has the Gaussian law prescribed by the diagonal MGF. -/
theorem hasLaw_coordinate_of_gaussian_joint_mgf
    (hY : ∀ i, Measurable (Y i))
    (hmgf : ∀ θ : κ → ℝ,
      ∫ ω, Real.exp (∑ i, θ i * Y i ω) ∂P =
        Real.exp (∑ i, θ i ^ 2 * (q i : ℝ) / 2))
    (k : κ) : HasLaw (Y k) (gaussianReal 0 (q k)) P := by
  classical
  apply hasLaw_gaussianReal_of_gaussian_mgf (hY k).aemeasurable
  intro r
  have hlin : ∀ ω, (∑ i, (if i = k then r else 0) * Y i ω) = r * Y k ω := by
    intro ω
    simp [ite_mul]
  have hvar : (∑ i, (if i = k then r else 0) ^ 2 * (q i : ℝ) / 2) =
      r ^ 2 * (q k : ℝ) / 2 := by
    calc
      _ = ∑ i, if i = k then r ^ 2 * (q i : ℝ) / 2 else 0 := by
            refine Finset.sum_congr rfl (fun i _ => ?_)
            by_cases hi : i = k <;> simp [hi]
      _ = _ := by simp
  have hm := hmgf (fun i => if i = k then r else 0)
  simp_rw [hlin] at hm
  rw [hvar] at hm
  simpa [mul_comm] using hm

/-- A diagonal Gaussian joint MGF forces independence of the finite family. -/
theorem iIndepFun_of_gaussian_joint_mgf
    (hY : ∀ i, Measurable (Y i))
    (hmgf : ∀ θ : κ → ℝ,
      ∫ ω, Real.exp (∑ i, θ i * Y i ω) ∂P =
        Real.exp (∑ i, θ i ^ 2 * (q i : ℝ) / 2)) :
    iIndepFun Y P := by
  classical
  refine (iIndepFun_iff_charFun_pi (fun i => (hY i).aemeasurable)).mpr fun w => ?_
  have hvar : 0 ≤ ∑ i, w i ^ 2 * (q i : ℝ) :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (sq_nonneg _) (q i).coe_nonneg)
  let v : ℝ≥0 := ⟨∑ i, w i ^ 2 * (q i : ℝ), hvar⟩
  have hv : (v : ℝ) = ∑ i, w i ^ 2 * (q i : ℝ) := rfl
  have hlin : Measurable (fun ω => ∑ i, w i * Y i ω) :=
    Finset.measurable_sum _ (fun i _ => (hY i).const_mul (w i))
  have hvec : Measurable (fun ω => WithLp.toLp 2 (fun i : κ => Y i ω)) :=
    (WithLp.measurable_toLp 2 _).comp
      (measurable_pi_iff.2 hY : Measurable (fun ω (i : κ) => Y i ω))
  have hmarg (i : κ) : charFun (P.map (Y i)) (w i) =
      Complex.exp (((-(w i ^ 2 * (q i : ℝ)) / 2) : ℝ) : ℂ) := by
    rw [(hasLaw_coordinate_of_gaussian_joint_mgf hY hmgf i).map_eq,
      charFun_gaussianReal]
    congr 1
    push_cast
    ring
  have hsum : (∑ i, -(w i ^ 2 * (q i : ℝ)) / 2) = -(v : ℝ) / 2 := by
    rw [hv, ← Finset.sum_neg_distrib, Finset.sum_div]
  calc
    charFun (P.map (fun ω => WithLp.toLp 2 (fun i : κ => Y i ω))) w
        = charFun (P.map (fun ω => ∑ i, w i * Y i ω)) 1 := by
            rw [charFun_apply, charFun_apply_real,
              integral_map hvec.aemeasurable (by fun_prop),
              integral_map hlin.aemeasurable (by fun_prop)]
            refine integral_congr_ae (Filter.Eventually.of_forall (fun ω => ?_))
            have hinner : ⟪WithLp.toLp 2 (fun i : κ => Y i ω), w⟫ =
                ∑ i, w i * Y i ω := by
              rw [PiLp.inner_apply]
              refine Finset.sum_congr rfl (fun i _ => ?_)
              simp only [RCLike.inner_apply, conj_trivial]
            simp only [hinner, Complex.ofReal_one, one_mul]
    _ = Complex.exp (((-(v : ℝ) / 2) : ℝ) : ℂ) := by
          rw [map_linearCombination_eq_gaussianReal_of_mgf hY hmgf _ hv,
            charFun_gaussianReal]
          congr 1
          push_cast
          ring
    _ = ∏ i, charFun (P.map (Y i)) (w i) := by
          rw [Finset.prod_congr rfl (fun i _ => hmarg i), ← Complex.exp_sum,
            ← Complex.ofReal_sum, hsum]

/-- The finite-family exponential-moment criterion gives both independence and
all coordinate laws without any martingale or Brownian hypotheses. -/
theorem independent_gaussian_family_of_mgf
    (hY : ∀ i, Measurable (Y i))
    (hmgf : ∀ θ : κ → ℝ,
      ∫ ω, Real.exp (∑ i, θ i * Y i ω) ∂P =
        Real.exp (∑ i, θ i ^ 2 * (q i : ℝ) / 2)) :
    iIndepFun Y P ∧ ∀ i, HasLaw (Y i) (gaussianReal 0 (q i)) P :=
  ⟨iIndepFun_of_gaussian_joint_mgf hY hmgf,
    hasLaw_coordinate_of_gaussian_joint_mgf hY hmgf⟩

end FiniteFamily

end Ripple.Stochastic
