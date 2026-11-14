import Ripple.Stochastic.KnightTerminalMGF
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.Ring

/-!
# Random terminal brackets and independent completion

A bounded bracket need not have a deterministic terminal value. The terminal
normalized exponential still has mean one. An independent auxiliary process
whose conditional exponential moment fills the missing variance then produces
the deterministic Gaussian moment on the product space. Product integrability
is a conclusion, obtained from the nonnegative section integrals.
-/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace Ripple.Stochastic.Knight

variable {Ω Ω₀ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω₀]
  {P : Measure Ω} {P₀ : Measure Ω₀}
  [IsProbabilityMeasure P] [IsProbabilityMeasure P₀]

/-- A bounded random terminal bracket preserves normalization. In particular,
no independence between the integral and its terminal bracket is required. -/
theorem terminal_normalized_exponential_random_bracket
    (Y Q : ℕ → Ω → ℝ) (L R : Ω → ℝ) (q a : ℝ)
    (hY : ∀ n, AEStronglyMeasurable (Y n) P)
    (hQ : ∀ n, AEStronglyMeasurable (Q n) P)
    (hbound : ∀ n, ∀ᵐ ω ∂P, Q n ω ≤ q)
    (hint : ∀ b n, Integrable
      (fun ω => Real.exp (b * Y n ω - b ^ 2 * Q n ω / 2)) P)
    (hmean : ∀ b n,
      (∫ ω, Real.exp (b * Y n ω - b ^ 2 * Q n ω / 2) ∂P) = 1)
    (hYlim : ∀ᵐ ω ∂P, Tendsto (fun n => Y n ω) atTop (𝓝 (L ω)))
    (hQlim : ∀ᵐ ω ∂P, Tendsto (fun n => Q n ω) atTop (𝓝 (R ω))) :
    Integrable (fun ω => Real.exp (a * L ω - a ^ 2 * R ω / 2)) P ∧
      (∫ ω, Real.exp (a * L ω - a ^ 2 * R ω / 2) ∂P) = 1 := by
  let Z := fun n ω => Real.exp (a * Y n ω - a ^ 2 * Q n ω / 2)
  have hsquare : ∀ n, Integrable (fun ω => (Z n ω) ^ 2) P ∧
      (∫ ω, (Z n ω) ^ 2 ∂P) ≤ Real.exp (a ^ 2 * q) := by
    intro n
    exact ExponentialMartingaleLimit.exponential_sq_bound (Y n) (Q n) a q
      (hY n) (hQ n) (hbound n) (hint (2 * a) n) (hmean (2 * a) n)
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun n => Z n ω) atTop
      (𝓝 (Real.exp (a * L ω - a ^ 2 * R ω / 2))) := by
    filter_upwards [hYlim, hQlim] with ω hy hq
    exact Real.continuous_exp.continuousAt.tendsto.comp
      ((hy.const_mul a).sub ((hq.const_mul (a ^ 2)).div_const 2))
  obtain ⟨hi, ht⟩ := KnightTerminalMGF.integral_limit_of_sq_bound
    (fun n => hint a n) (fun n => (hsquare n).1) (fun n => (hsquare n).2) hlim
  refine ⟨hi, tendsto_nhds_unique ht ?_⟩
  simpa only [Z, hmean] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))

/-- Conditional Gaussian completion. For each original sample, the auxiliary
exponential has the missing variance `q-R`. Fubini and terminal normalization
give the full moment, including integrability on the product space. -/
theorem product_mgf_of_terminal_normalization
    (L R : Ω → ℝ) (V : Ω × Ω₀ → ℝ) (q a : ℝ)
    (hL : Measurable L) (hV : Measurable V)
    (hbaseInt : Integrable (fun ω => Real.exp (a * L ω - a ^ 2 * R ω / 2)) P)
    (hbaseMean : (∫ ω, Real.exp (a * L ω - a ^ 2 * R ω / 2) ∂P) = 1)
    (hauxInt : ∀ ω, Integrable (fun z => Real.exp (a * V (ω, z))) P₀)
    (hauxMean : ∀ ω, (∫ z, Real.exp (a * V (ω, z)) ∂P₀) =
      Real.exp (a ^ 2 * (q - R ω) / 2)) :
    Integrable (fun p => Real.exp (a * (L p.1 + V p))) (P.prod P₀) ∧
      (∫ p, Real.exp (a * (L p.1 + V p)) ∂P.prod P₀) =
        Real.exp (a ^ 2 * q / 2) := by
  let E := fun p : Ω × Ω₀ => Real.exp (a * (L p.1 + V p))
  let C := Real.exp (a ^ 2 * q / 2)
  let Z := fun ω => Real.exp (a * L ω - a ^ 2 * R ω / 2)
  have heq (ω : Ω) (z : Ω₀) :
      E (ω, z) = Real.exp (a * L ω) * Real.exp (a * V (ω, z)) := by
    dsimp [E]
    rw [mul_add, Real.exp_add]
  have hsection (ω : Ω) : Integrable (fun z => E (ω, z)) P₀ := by
    simp_rw [heq]
    exact (hauxInt ω).const_mul _
  have hinner (ω : Ω) : (∫ z, E (ω, z) ∂P₀) = C * Z ω := by
    simp_rw [heq]
    rw [integral_const_mul, hauxMean, ← Real.exp_add]
    dsimp [C, Z]
    rw [← Real.exp_add]
    congr 1
    ring
  have hnorm (ω : Ω) : (∫ z, ‖E (ω, z)‖ ∂P₀) = C * Z ω := by
    calc
      _ = ∫ z, E (ω, z) ∂P₀ := integral_congr_ae (ae_of_all _ fun z =>
        Real.norm_of_nonneg (Real.exp_pos _).le)
      _ = _ := hinner ω
  have hmeas : Measurable E :=
    Real.continuous_exp.measurable.comp
      (((hL.comp measurable_fst).add hV).const_mul a)
  have hi : Integrable E (P.prod P₀) := by
    apply (integrable_prod_iff hmeas.aestronglyMeasurable).2
    refine ⟨ae_of_all _ hsection, ?_⟩
    simp_rw [hnorm]
    exact hbaseInt.const_mul C
  refine ⟨hi, ?_⟩
  change (∫ p, E p ∂P.prod P₀) = C
  rw [integral_prod _ hi]
  simp_rw [hinner]
  rw [integral_const_mul]
  change C * (∫ ω, Real.exp (a * L ω - a ^ 2 * R ω / 2) ∂P) = C
  rw [hbaseMean, mul_one]

end Ripple.Stochastic.Knight
