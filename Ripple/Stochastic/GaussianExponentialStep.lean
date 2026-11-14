import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Tactic

/-!
# Gaussian exponential steps with finite-valued predictable coefficients

The coefficient is allowed to depend on all past observations. Independence is
between the new increment and the entire past sigma algebra. Integrability of
products is proved by splitting into the finitely many coefficient values.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal

namespace Ripple.Stochastic.GaussianExponentialStep

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  [IsProbabilityMeasure P]

/-- The normalized exponential of a centered Gaussian variable. -/
noncomputable def gaussianFactor (a : ℝ) (v : ℝ≥0) (x : ℝ) : ℝ :=
  Real.exp (a * x - a ^ 2 * (v : ℝ) / 2)

/-- Gaussian normalization, including the zero-variance case. -/
theorem gaussianFactor_integral (a : ℝ) (v : ℝ≥0) :
    ∫ x, gaussianFactor a v x ∂gaussianReal 0 v = 1 := by
  have heq : gaussianFactor a v = fun x =>
      Real.exp (-(a ^ 2 * (v : ℝ) / 2)) * Real.exp (a * x) := by
    funext x
    rw [gaussianFactor, ← Real.exp_add]
    congr 1
    ring
  rw [heq, integral_const_mul]
  have hmgf := congr_fun (mgf_id_gaussianReal (μ := 0) (v := v)) a
  change Real.exp (-(a ^ 2 * (v : ℝ) / 2)) * mgf id (gaussianReal 0 v) a = 1
  rw [hmgf, ← Real.exp_add]
  convert Real.exp_zero using 1 <;> congr 1 <;> ring

/-- Integrability is obtained from the Gaussian MGF, before any use of a
conditional expectation or a martingale identity. -/
theorem gaussianFactor_integrable (a : ℝ) (v : ℝ≥0) :
    Integrable (gaussianFactor a v) (gaussianReal 0 v) := by
  convert (integrable_exp_mul_gaussianReal (μ := 0) (v := v) a).const_mul
    (Real.exp (-(a ^ 2 * (v : ℝ) / 2))) using 1
  funext x
  rw [gaussianFactor, ← Real.exp_add]
  congr 1
  ring

/-- The normalized Gaussian factor is a measurable function of the increment. -/
theorem measurable_gaussianFactor (a : ℝ) (v : ℝ≥0) : Measurable (gaussianFactor a v) := by
  unfold gaussianFactor
  fun_prop

/-- Transport the normalized Gaussian factor along a Gaussian random variable. -/
theorem gaussianFactor_hasLaw {X : Ω → ℝ} {v : ℝ≥0}
    (hX : Measurable X) (hLaw : HasLaw X (gaussianReal 0 v) P) (a : ℝ) :
    Integrable (fun ω => gaussianFactor a v (X ω)) P ∧
      (∫ ω, gaussianFactor a v (X ω) ∂P) = 1 := by
  constructor
  · have hint : Integrable (gaussianFactor a v) (P.map X) := by
      rw [hLaw.map_eq]
      exact gaussianFactor_integrable a v
    exact hint.comp_measurable hX
  · have h := hLaw.integral_comp (f := gaussianFactor a v)
      (gaussianFactor_integrable a v).aestronglyMeasurable
    simpa only [Function.comp_apply, gaussianFactor_integral] using h

/-- A finite choice partitions a weighted step into independent products. -/
theorem selected_mul_eq_sum {d : ℕ} (A : Ω → Fin d)
    (U : Ω → ℝ) (G : Fin d → Ω → ℝ) :
    (fun ω => U ω * G (A ω) ω) =
      ∑ i : Fin d, (fun ω => ({ω | A ω = i}.indicator U) ω * G i ω) := by
  classical
  funext ω
  rw [Finset.sum_apply, Finset.sum_eq_single (A ω)]
  · simp [Set.indicator_apply]
  · intro b _ hb
    simp [Set.indicator_apply, Ne.symm hb]
  · simp

/-- One random finite-choice step preserves the conditional mean of any
integrable past-measurable weight, and produces an integrable product. -/
theorem selected_mul_condExp {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {d : ℕ} (A : Ω → Fin d) (hA : Measurable[m] A)
    (U : Ω → ℝ) (hU : StronglyMeasurable[m] U) (hUint : Integrable U P)
    (G : Fin d → Ω → ℝ) (hG : ∀ i, Measurable[mΩ] (G i))
    (hGint : ∀ i, Integrable (G i) P)
    (hGmean : ∀ i, (∫ ω, G i ω ∂P) = 1)
    (hind : ∀ i, Indep (MeasurableSpace.comap (G i) (borel ℝ)) m P) :
    Integrable (fun ω => U ω * G (A ω) ω) P ∧
      P[fun ω => U ω * G (A ω) ω | m] =ᵐ[P] U := by
  classical
  let V : Fin d → Ω → ℝ := fun i => {ω | A ω = i}.indicator U
  have hset : ∀ i, MeasurableSet[m] {ω | A ω = i} :=
    fun i => hA (measurableSet_singleton i)
  have hV : ∀ i, StronglyMeasurable[m] (V i) :=
    fun i => hU.indicator (hset i)
  have hVind : ∀ i, IndepFun (V i) (G i) P := by
    intro i
    apply (IndepFun_iff_Indep _ _ _).mpr
    exact (indep_of_indep_of_le_right (hind i)
      (measurable_iff_comap_le.mp (hV i).measurable)).symm
  have hVint : ∀ i, Integrable (V i) P :=
    fun i => hUint.indicator (hm _ (hset i))
  have hprod : ∀ i, Integrable (fun ω => V i ω * G i ω) P :=
    fun i => (hVind i).integrable_mul (hVint i) (hGint i)
  have hcondG : ∀ i, P[G i | m] =ᵐ[P] fun _ => (1 : ℝ) := by
    intro i
    have hGm : Measurable[MeasurableSpace.comap (G i) (borel ℝ)] (G i) :=
      fun s hs => ⟨s, hs, rfl⟩
    have h := condExp_indep_eq (hG i).comap_le hm hGm.stronglyMeasurable (hind i)
    simpa only [hGmean i] using h
  have hcond : ∀ i, P[fun ω => V i ω * G i ω | m] =ᵐ[P] V i := by
    intro i
    have h := condExp_mul_of_stronglyMeasurable_left (hV i) (hprod i) (hGint i)
    filter_upwards [h, hcondG i] with ω hω hGω
    simpa only [Pi.mul_apply, hGω, mul_one] using hω
  have hsum : (∑ i : Fin d, V i) = U := by
    funext ω
    simp [V, Finset.sum_apply, Set.indicator_apply]
  rw [selected_mul_eq_sum A U G]
  constructor
  · exact integrable_finsetSum' _ (fun i _ => hprod i)
  · refine (condExp_finsetSum (fun i (_ : i ∈ (Finset.univ : Finset (Fin d))) =>
      hprod i) (m := m)).trans ?_
    have h2 : (∑ i ∈ Finset.univ, P[fun ω => V i ω * G i ω | m]) =ᵐ[P]
        ∑ i ∈ Finset.univ, V i :=
      eventuallyEq_sum (fun i _ => hcond i)
    rw [hsum] at h2
    exact h2

/-- Gaussian specialization of the finite-choice step. The coefficient may be
random and may inspect any information in `m`. -/
theorem gaussian_selected_step {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {d : ℕ} (A : Ω → Fin d) (hA : Measurable[m] A) (c : Fin d → ℝ)
    (U : Ω → ℝ) (hU : StronglyMeasurable[m] U) (hUint : Integrable U P)
    {X : Ω → ℝ} {v : ℝ≥0} (hX : Measurable[mΩ] X)
    (hLaw : HasLaw X (gaussianReal 0 v) P)
    (hind : Indep (MeasurableSpace.comap X (borel ℝ)) m P) :
    Integrable (fun ω => U ω * gaussianFactor (c (A ω)) v (X ω)) P ∧
      P[fun ω => U ω * gaussianFactor (c (A ω)) v (X ω) | m] =ᵐ[P] U := by
  apply selected_mul_condExp hm A hA U hU hUint
    (fun i ω => gaussianFactor (c i) v (X ω))
  · intro i
    exact (measurable_gaussianFactor (c i) v).comp hX
  · exact fun i => (gaussianFactor_hasLaw hX hLaw (c i)).1
  · exact fun i => (gaussianFactor_hasLaw hX hLaw (c i)).2
  · intro i
    apply indep_of_indep_of_le_left hind
    have hXm : Measurable[MeasurableSpace.comap X (borel ℝ)] X :=
      fun s hs => ⟨s, hs, rfl⟩
    exact ((measurable_gaussianFactor (c i) v).comp hXm).comap_le

/-- Logarithm of the finite-step exponential, with its actual accumulated
quadratic compensator. -/
noncomputable def discreteLog {d : ℕ} (A : ℕ → Ω → Fin d)
    (c : ℕ → Fin d → ℝ) (X : ℕ → Ω → ℝ) (v : ℕ → ℝ≥0) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range n, (c k (A k ω) * X k ω - (c k (A k ω)) ^ 2 * (v k : ℝ) / 2)

/-- A discrete stochastic exponential with finite-valued predictable
coefficients is a martingale. No exponential moment or conditional MGF
identity is carried as a premise. -/
theorem discrete_exponential_martingale {d : ℕ}
    (F : Filtration ℕ mΩ) (A : ℕ → Ω → Fin d) (c : ℕ → Fin d → ℝ)
    (X : ℕ → Ω → ℝ) (v : ℕ → ℝ≥0)
    (hA : ∀ n, Measurable[F n] (A n))
    (hX : ∀ n, Measurable[F (n + 1)] (X n))
    (hLaw : ∀ n, HasLaw (X n) (gaussianReal 0 (v n)) P)
    (hind : ∀ n, Indep (MeasurableSpace.comap (X n) (borel ℝ)) (F n) P) :
    Martingale (fun n ω => Real.exp (discreteLog A c X v n ω)) F P := by
  let Z : ℕ → Ω → ℝ := fun n ω => Real.exp (discreteLog A c X v n ω)
  have hsucc : ∀ n, Z (n + 1) = fun ω =>
      Z n ω * gaussianFactor (c n (A n ω)) (v n) (X n ω) := by
    intro n
    funext ω
    simp only [Z, discreteLog, Finset.sum_range_succ, gaussianFactor]
    rw [Real.exp_add]
  have hadapt : StronglyAdapted F Z := by
    intro n
    apply Real.continuous_exp.comp_stronglyMeasurable
    apply Finset.stronglyMeasurable_fun_sum
    intro k hk
    have hkn : k < n := Finset.mem_range.mp hk
    have hc : Measurable[F n] (fun ω => c k (A k ω)) :=
      (measurable_of_finite (c k)).comp ((hA k).mono (F.mono hkn.le) le_rfl)
    have hx : Measurable[F n] (X k) := (hX k).mono (F.mono hkn) le_rfl
    exact ((hc.mul hx).sub ((hc.pow_const 2).mul_const _ |>.div_const 2)).stronglyMeasurable
  have hint : ∀ n, Integrable (Z n) P := by
    intro n
    induction n with
    | zero => simpa [Z, discreteLog] using (integrable_const (1 : ℝ) : Integrable (fun _ : Ω => (1 : ℝ)) P)
    | succ n hn =>
      rw [hsucc]
      exact (gaussian_selected_step (F.le n) (A n) (hA n) (c n)
        (Z n) (hadapt n) hn ((hX n).mono (F.le _) le_rfl) (hLaw n) (hind n)).1
  apply martingale_nat hadapt hint
  intro n
  rw [hsucc]
  exact (gaussian_selected_step (F.le n) (A n) (hA n) (c n)
    (Z n) (hadapt n) (hint n) ((hX n).mono (F.le _) le_rfl)
    (hLaw n) (hind n)).2.symm

end Ripple.Stochastic.GaussianExponentialStep
