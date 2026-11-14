import Ripple.Stochastic.GaussianExponentialStep

/-!
# The joint Gaussian exponential step for several channels

The whole increment vector is independent of the past. Its coordinates are
independent centered Gaussians. Coefficients may depend jointly on all past
channels; independence of the stochastic integrals is never asserted.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace Ripple.Stochastic.GaussianChannelExponential
open GaussianExponentialStep

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Finite products of independent integrable variables are integrable. -/
theorem integrable_prod_of_independent {ι : Type*} (G : ι → Ω → ℝ)
    (hG : ∀ i, Measurable (G i)) (hint : ∀ i, Integrable (G i) P)
    (hind : iIndepFun G P) (s : Finset ι) :
    Integrable (fun ω => ∏ i ∈ s, G i ω) P := by
  classical
  induction s using Finset.cons_induction with
  | empty => simpa using (integrable_const (1 : ℝ) : Integrable (fun _ : Ω => (1 : ℝ)) P)
  | cons i s hi ih =>
    have ih' : Integrable (∏ j ∈ s, G j) P := by
      have h : (∏ j ∈ s, G j) = fun ω => ∏ j ∈ s, G j ω := by
        funext ω
        exact Finset.prod_apply ω s G
      rw [h]
      exact ih
    have h := (hind.indepFun_finsetProd_of_notMem hG hi).symm.integrable_mul (hint i) ih'
    refine h.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp [Finset.prod_apply, Finset.prod_insert hi]

/-- The compensated vector MGF factors coordinatewise and has expectation one. -/
theorem gaussian_product_normalized {d : ℕ} (X : Fin d → Ω → ℝ)
    (hX : ∀ j, Measurable (X j)) (v : Fin d → ℝ≥0)
    (hLaw : ∀ j, HasLaw (X j) (gaussianReal 0 (v j)) P)
    (hind : iIndepFun X P) (a : Fin d → ℝ) :
    Integrable (fun ω => ∏ j, gaussianFactor (a j) (v j) (X j ω)) P ∧
    (∫ ω, ∏ j, gaussianFactor (a j) (v j) (X j ω) ∂P) = 1 := by
  let G : Fin d → Ω → ℝ := fun j ω => gaussianFactor (a j) (v j) (X j ω)
  have hG : ∀ j, Measurable (G j) := fun j =>
    (measurable_gaussianFactor (a j) (v j)).comp (hX j)
  have hi : iIndepFun G P := hind.comp
    (fun j => gaussianFactor (a j) (v j)) (fun j => measurable_gaussianFactor (a j) (v j))
  constructor
  · exact integrable_prod_of_independent G hG
      (fun j => (gaussianFactor_hasLaw (hX j) (hLaw j) (a j)).1) hi Finset.univ
  · rw [hi.integral_fun_prod_eq_prod_integral (fun j => (hG j).aestronglyMeasurable)]
    exact Finset.prod_eq_one (fun j _ => (gaussianFactor_hasLaw (hX j) (hLaw j) (a j)).2)

/-- A finite-valued random vector coefficient has the joint conditional MGF.
The entire increment vector, rather than each coordinate separately, is required
independent of the past sigma algebra. -/
theorem selected_gaussian_vector_step {m : MeasurableSpace Ω}
    (hm : m ≤ mΩ) {d k : ℕ}
    (A : Ω → Fin k) (hA : Measurable[m] A) (c : Fin k → Fin d → ℝ)
    (U : Ω → ℝ) (hU : StronglyMeasurable[m] U) (hUint : Integrable U P)
    (X : Fin d → Ω → ℝ) (hX : ∀ j, Measurable[mΩ] (X j)) (v : Fin d → ℝ≥0)
    (hLaw : ∀ j, HasLaw (X j) (gaussianReal 0 (v j)) P)
    (hind : iIndepFun X P)
    (hpast : Indep (MeasurableSpace.comap (fun ω j => X j ω) inferInstance) m P) :
    Integrable (fun ω => U ω * ∏ j, gaussianFactor (c (A ω) j) (v j) (X j ω)) P ∧
      P[fun ω => U ω * ∏ j, gaussianFactor (c (A ω) j) (v j) (X j ω) | m] =ᵐ[P] U := by
  apply selected_mul_condExp hm A hA U hU hUint
    (fun i ω => ∏ j, gaussianFactor (c i j) (v j) (X j ω))
  · intro i
    exact Finset.measurable_prod _
      (fun j _ => (measurable_gaussianFactor (c i j) (v j)).comp (hX j))
  · exact fun i => (gaussian_product_normalized (mΩ := mΩ) X hX v hLaw hind (c i)).1
  · exact fun i => (gaussian_product_normalized (mΩ := mΩ) X hX v hLaw hind (c i)).2
  · intro i
    apply indep_of_indep_of_le_left hpast
    have hf : Measurable (fun x : Fin d → ℝ => ∏ j, gaussianFactor (c i j) (v j) (x j)) := by
      unfold gaussianFactor
      fun_prop
    have hXm : Measurable[MeasurableSpace.comap (fun ω j => X j ω) inferInstance]
        (fun ω j => X j ω) := fun s hs => ⟨s, hs, rfl⟩
    exact (hf.comp hXm).comap_le

/-- The channel compensation is the sum of the channel bracket increments. -/
theorem gaussian_product_eq_exp_sum {d : ℕ} (a x : Fin d → ℝ) (v : Fin d → ℝ≥0) :
    (∏ j, gaussianFactor (a j) (v j) (x j)) =
      Real.exp ((∑ j, a j * x j) - (∑ j, (a j) ^ 2 * (v j : ℝ)) / 2) := by
  simp only [gaussianFactor]
  rw [← Real.exp_sum]
  congr 1
  rw [Finset.sum_div, ← Finset.sum_sub_distrib]

end Ripple.Stochastic.GaussianChannelExponential
