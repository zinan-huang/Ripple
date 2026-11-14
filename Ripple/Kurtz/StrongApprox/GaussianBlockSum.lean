/-
  Ripple.Kurtz.StrongApprox.GaussianBlockSum — an iid standard normal sequence, the law of a
  block sum, and the Gaussian inputs of the exponential maximal inequality.
-/

import Mathlib

namespace Ripple.Kurtz.StrongApprox

open MeasureTheory ProbabilityTheory Set Finset

/-! ### The iid standard normal sequence -/

/-- The law of an iid sequence of standard normals on `ℕ → ℝ`. -/
noncomputable def gaussSeq : Measure (ℕ → ℝ) :=
  Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1)

instance : IsProbabilityMeasure gaussSeq := by
  unfold gaussSeq; infer_instance

theorem iIndepFun_gaussSeq : iIndepFun (fun m (x : ℕ → ℝ) => x m) gaussSeq := by
  have := iIndepFun_infinitePi (P := fun _ : ℕ => gaussianReal 0 1)
    (X := fun _ : ℕ => (id : ℝ → ℝ)) (fun _ => measurable_id)
  exact this

theorem gaussSeq_map_eval (m : ℕ) : gaussSeq.map (fun x => x m) = gaussianReal 0 1 :=
  Measure.infinitePi_map_eval _ m

theorem measurable_gaussSum (L : ℕ) : Measurable (fun x : ℕ → ℝ => ∑ m ∈ range L, x m) :=
  Finset.measurable_sum _ (fun m _ => measurable_pi_apply m)

/-- `Σ_{m<L} x m ~ N(0, L)`. -/
theorem gaussSeq_map_sum (L : ℕ) :
    gaussSeq.map (fun x => ∑ m ∈ range L, x m) = gaussianReal 0 L := by
  induction L with
  | zero =>
    simp only [range_zero, sum_empty, Nat.cast_zero]
    rw [Measure.map_const, measure_univ, one_smul, gaussianReal_zero_var]
  | succ L ih =>
    have hind : IndepFun (∑ m ∈ range L, fun x : ℕ → ℝ => x m) (fun x : ℕ → ℝ => x L) gaussSeq :=
      iIndepFun_gaussSeq.indepFun_finset_sum_of_notMem (fun m => measurable_pi_apply m)
        (by simp)
    have hsum : (fun x : ℕ → ℝ => ∑ m ∈ range (L + 1), x m) =
        (∑ m ∈ range L, fun x : ℕ → ℝ => x m) + fun x => x L := by
      funext x; simp [sum_range_succ]
    have hmeas : Measurable (∑ m ∈ range L, fun x : ℕ → ℝ => x m) := by
      have e : (∑ m ∈ range L, fun x : ℕ → ℝ => x m) = fun x => ∑ m ∈ range L, x m := by
        funext x; simp
      rw [e]; exact measurable_gaussSum L
    rw [hsum, IndepFun.map_add_eq_map_conv_map hmeas (measurable_pi_apply L) hind]
    have h1 : gaussSeq.map (∑ m ∈ range L, fun x : ℕ → ℝ => x m) = gaussianReal 0 L := by
      rw [← ih]; congr 1; funext x; simp
    rw [h1, gaussSeq_map_eval, gaussianReal_conv_gaussianReal, add_zero]
    congr 1
    push_cast
    ring

/-- `Σ_{m<L} x m / √L ~ N(0,1)` for `L ≥ 1`. -/
theorem gaussSeq_map_sum_div_sqrt {L : ℕ} (hL : 0 < L) :
    gaussSeq.map (fun x => (∑ m ∈ range L, x m) / Real.sqrt L) = gaussianReal 0 1 := by
  have hcomp : (fun x : ℕ → ℝ => (∑ m ∈ range L, x m) / Real.sqrt L) =
      (fun y : ℝ => (Real.sqrt L)⁻¹ * y) ∘ (fun x => ∑ m ∈ range L, x m) := by
    funext x; simp [div_eq_inv_mul]
  rw [hcomp, ← Measure.map_map (by fun_prop) (measurable_gaussSum L), gaussSeq_map_sum,
    gaussianReal_map_const_mul]
  have hLpos : (0:ℝ) < L := by exact_mod_cast hL
  congr 1
  · simp
  · apply NNReal.coe_injective
    simp only [NNReal.coe_mul, NNReal.coe_mk, NNReal.coe_natCast, NNReal.coe_one]
    rw [inv_pow, Real.sq_sqrt hLpos.le, inv_mul_cancel₀ hLpos.ne']

/-! ### Gaussian inputs of the maximal inequalities -/

section Gaussian

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Z : Ω → ℝ}

theorem mgf_of_gaussian (hlaw : P.map Z = gaussianReal 0 1) (θ : ℝ) :
    mgf Z P θ = Real.exp (θ ^ 2 / 2) := by
  rw [mgf_gaussianReal hlaw]; simp

theorem integrable_exp_mul_of_gaussian (hZ : Measurable Z) (hlaw : P.map Z = gaussianReal 0 1)
    (θ : ℝ) : Integrable (fun ω => Real.exp (θ * Z ω)) P := by
  have h := integrable_exp_mul_gaussianReal (μ := 0) (v := 1) θ
  rw [← hlaw] at h
  exact h.comp_measurable hZ

theorem integrable_pow_of_gaussian (hZ : Measurable Z) (hlaw : P.map Z = gaussianReal 0 1)
    (n : ℕ) : Integrable (fun ω => Z ω ^ n) P := by
  have h : Integrable (fun x : ℝ => x ^ n) (gaussianReal 0 1) := by
    have := integrable_pow_of_mem_interior_integrableExpSet
      (X := id) (μ := gaussianReal 0 1) (by rw [integrableExpSet_id_gaussianReal]; simp) n
    simpa using this
  rw [← hlaw] at h
  exact h.comp_measurable hZ

theorem integrable_of_gaussian (hZ : Measurable Z) (hlaw : P.map Z = gaussianReal 0 1) :
    Integrable Z P := by
  simpa using integrable_pow_of_gaussian hZ hlaw 1

theorem integral_of_gaussian (hZ : Measurable Z) (hlaw : P.map Z = gaussianReal 0 1) :
    ∫ ω, Z ω ∂P = 0 := by
  have := integral_map (μ := P) (φ := Z) hZ.aemeasurable (f := fun x : ℝ => x)
    measurable_id.aestronglyMeasurable
  rw [hlaw, integral_id_gaussianReal] at this
  exact this.symm

theorem memLp_two_of_gaussian [IsProbabilityMeasure P] (hZ : Measurable Z)
    (hlaw : P.map Z = gaussianReal 0 1) : MemLp Z 2 P :=
  (memLp_two_iff_integrable_sq hZ.aestronglyMeasurable).mpr (integrable_pow_of_gaussian hZ hlaw 2)

/-- The reflected variable is again standard normal. -/
theorem map_neg_of_gaussian (hZ : Measurable Z) (hlaw : P.map Z = gaussianReal 0 1) :
    P.map (fun ω => -Z ω) = gaussianReal 0 1 := by
  rw [show (fun ω => -Z ω) = (fun x : ℝ => -x) ∘ Z from rfl,
    ← Measure.map_map measurable_neg hZ, hlaw, gaussianReal_map_neg, neg_zero]

end Gaussian

end Ripple.Kurtz.StrongApprox
