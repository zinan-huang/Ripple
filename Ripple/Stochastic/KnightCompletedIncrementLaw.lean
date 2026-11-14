import Ripple.Stochastic.KnightCompletionGrid
import Ripple.Stochastic.KnightRandomBracketMGF
import Ripple.Stochastic.KnightBrownianLaw
import Ripple.Stochastic.KnightStepIntegral
import Ripple.Stochastic.KnightTerminalValue
import Ripple.Stochastic.CompletedKnightReconstruction

/-!
# Rectangular laws for completed inverse-clock paths

Safe stopped sums converge even above finite terminal clocks. Their brackets
converge to clipped terminal brackets. Auxiliary increments fill exactly the
remaining variance on the product space. The stochastic normalization inputs
are explicit: this module supplies the completion argument, not the bounded
predictable exponential producer.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology BigOperators

namespace Ripple.Stochastic.Knight
open Ripple.Analysis Ripple.ProbabilityTheory

variable {ι κ Ω Ω₀ : Type} [Fintype κ]

def originalGridSum (g : IntervalGrid ι κ) (θ : κ → ℝ)
    (M : ι → ℝ≥0 → Ω → ℝ) (A : ι → ℝ≥0 → Ω → ℝ≥0)
    (L : ι → Ω → ℝ) (ω : Ω) : ℝ :=
  ∑ j, θ j *
    (terminalOriginalPath (fun t => M (g.channel j) t ω)
        (fun t => A (g.channel j) t ω) (L (g.channel j) ω) (g.upper j) -
      terminalOriginalPath (fun t => M (g.channel j) t ω)
        (fun t => A (g.channel j) t ω) (L (g.channel j) ω) (g.lower j))

theorem cappedStepSum_tendsto_originalGridSum
    (g : IntervalGrid ι κ) (θ : κ → ℝ)
    (M : ι → ℝ≥0 → Ω → ℝ) (A : ι → ℝ≥0 → Ω → ℝ≥0)
    (L : ι → Ω → ℝ) (ω : Ω)
    (hlim : ∀ i, terminalClock (fun t => A i t ω) ≠ ⊤ →
      Tendsto (fun t => M i t ω) atTop (𝓝 (L i ω))) :
    Tendsto (fun t => cappedStepSum g θ M A t ω) atTop
      (𝓝 (originalGridSum g θ M A L ω)) := by
  apply tendsto_finset_sum
  intro j _
  exact ((clockStoppedPath_tendsto_terminalOriginalPath (hlim (g.channel j))
    (g.upper j)).sub
    (clockStoppedPath_tendsto_terminalOriginalPath (hlim (g.channel j))
      (g.lower j))).const_mul (θ j)

theorem stepBracket_tendsto_terminalGridBracket
    (g : IntervalGrid ι κ) (θ : κ → ℝ)
    (A : ι → ℝ≥0 → Ω → ℝ≥0) (ω : Ω)
    (hm : ∀ i, Monotone (fun t => A i t ω)) :
    Tendsto (fun t => stepBracket g θ A t ω) atTop
      (𝓝 (terminalGridBracket g θ (fun i => terminalClock (fun t => A i t ω)))) := by
  apply tendsto_finset_sum
  intro j _
  exact (((NNReal.continuous_coe.tendsto _).comp
    (min_clock_tendsto_terminalClip (hm _) (g.upper j))).sub
    ((NNReal.continuous_coe.tendsto _).comp
      (min_clock_tendsto_terminalClip (hm _) (g.lower j)))).const_mul (θ j ^ 2)

variable [MeasurableSpace Ω] [MeasurableSpace Ω₀]
  {P : Measure Ω} {P₀ : Measure Ω₀}
  [IsProbabilityMeasure P] [IsProbabilityMeasure P₀]

/-- The terminal original contribution has a normalized exponential of mean
one. Both terminal limits are produced from the actual safe stopped sums. -/
theorem capped_step_terminal_normalization
    (g : IntervalGrid ι κ) (θ : κ → ℝ)
    (M : ι → ℝ≥0 → Ω → ℝ) (A : ι → ℝ≥0 → Ω → ℝ≥0) (L : ι → Ω → ℝ)
    (hm : ∀ᵐ ω ∂P, ∀ i, Monotone (fun t => A i t ω))
    (hlim : ∀ᵐ ω ∂P, ∀ i, terminalClock (fun t => A i t ω) ≠ ⊤ →
      Tendsto (fun t => M i t ω) atTop (𝓝 (L i ω)))
    (hY : ∀ n : ℕ, AEStronglyMeasurable (cappedStepSum g θ M A n) P)
    (hQ : ∀ n : ℕ, AEStronglyMeasurable (stepBracket g θ A n) P)
    (hint : ∀ a (n : ℕ), Integrable (fun ω => Real.exp
      (a * cappedStepSum g θ M A n ω - a ^ 2 * stepBracket g θ A n ω / 2)) P)
    (hmean : ∀ a (n : ℕ), (∫ ω, Real.exp
      (a * cappedStepSum g θ M A n ω - a ^ 2 * stepBracket g θ A n ω / 2) ∂P) = 1) :
    Integrable (fun ω => Real.exp (originalGridSum g θ M A L ω -
      terminalGridBracket g θ (fun i => terminalClock (fun t => A i t ω)) / 2)) P ∧
    (∫ ω, Real.exp (originalGridSum g θ M A L ω -
      terminalGridBracket g θ (fun i => terminalClock (fun t => A i t ω)) / 2) ∂P) = 1 := by
  have hYL : ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => cappedStepSum g θ M A n ω) atTop
      (𝓝 (originalGridSum g θ M A L ω)) := by
    filter_upwards [hlim] with ω hω
    exact (cappedStepSum_tendsto_originalGridSum g θ M A L ω hω).comp tendsto_nnreal_natCast
  have hQL : ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => stepBracket g θ A n ω) atTop
      (𝓝 (terminalGridBracket g θ (fun i => terminalClock (fun t => A i t ω)))) := by
    filter_upwards [hm] with ω hω
    exact (stepBracket_tendsto_terminalGridBracket g θ A ω hω).comp tendsto_nnreal_natCast
  simpa only [one_mul, one_pow] using terminal_normalized_exponential_random_bracket
      (fun n : ℕ => cappedStepSum g θ M A n) (fun n : ℕ => stepBracket g θ A n)
      (originalGridSum g θ M A L)
      (fun ω => terminalGridBracket g θ (fun i => terminalClock (fun t => A i t ω)))
      (gridVariance g θ) 1 hY hQ
      (fun n => ae_of_all _ fun ω => stepBracket_le_gridVariance g θ A n ω)
      hint hmean hYL hQL

/-- Exact rectangular MGF of the completed paths. Original-clock and auxiliary
terms may each have random variances; their sum has the deterministic grid
variance. The auxiliary grid is formed after fixing the original sample. -/
theorem completed_grid_mgf
    (g : IntervalGrid ι κ) (θ : κ → ℝ)
    (M : ι → ℝ≥0 → Ω → ℝ) (A : ι → ℝ≥0 → Ω → ℝ≥0) (L : ι → Ω → ℝ)
    (W : ι → ℝ≥0 → Ω₀ → ℝ)
    (hW : HasRectangularGaussianIncrements W P₀)
    (hWzero : ∀ i z, W i 0 z = 0)
    (hWjoint : ∀ i, Measurable (Function.uncurry (W i)))
    (hterminal : ∀ i, Measurable (fun ω => terminalClock (fun t => A i t ω)))
    (hO : ∀ i u, Measurable (fun ω =>
      terminalOriginalPath (fun t => M i t ω) (fun t => A i t ω) (L i ω) u))
    (hnorm : Integrable (fun ω => Real.exp (originalGridSum g θ M A L ω -
        terminalGridBracket g θ (fun i => terminalClock (fun t => A i t ω)) / 2)) P ∧
      (∫ ω, Real.exp (originalGridSum g θ M A L ω -
        terminalGridBracket g θ (fun i => terminalClock (fun t => A i t ω)) / 2) ∂P) = 1) :
    Integrable (fun p => Real.exp (∑ j, θ j *
      (completedKnightTimeChange M A L W (g.channel j) (g.upper j) p -
        completedKnightTimeChange M A L W (g.channel j) (g.lower j) p))) (P.prod P₀) ∧
    (∫ p, Real.exp (∑ j, θ j *
      (completedKnightTimeChange M A L W (g.channel j) (g.upper j) p -
        completedKnightTimeChange M A L W (g.channel j) (g.lower j) p)) ∂P.prod P₀) =
      Real.exp (gridVariance g θ / 2) := by
  classical
  let c := fun (ω : Ω) i => terminalClock (fun t => A i t ω)
  let V := fun p : Ω × Ω₀ => ∑ j, θ j *
    (W (g.channel j) (terminalResidual (c p.1 (g.channel j)) (g.upper j)) p.2 -
      W (g.channel j) (terminalResidual (c p.1 (g.channel j)) (g.lower j)) p.2)
  have hres (i : ι) (u : ℝ≥0) : Measurable (fun ω => terminalResidual (c ω i) u) := by
    unfold terminalResidual terminalClip
    exact measurable_const.sub (Measurable.ite
      (measurableSet_eq_fun (hterminal i) measurable_const)
      measurable_const (measurable_const.min (hterminal i).ennreal_toNNReal))
  have hVm : Measurable V := by
    apply Finset.measurable_sum
    intro j _
    exact (((hWjoint _).comp (((hres _ _).comp measurable_fst).prodMk measurable_snd)).sub
      ((hWjoint _).comp (((hres _ _).comp measurable_fst).prodMk measurable_snd))).const_mul _
  have hOm : Measurable (originalGridSum g θ M A L) := by
    apply Finset.measurable_sum
    intro j _
    exact ((hO _ _).sub (hO _ _)).const_mul _
  have haux (ω : Ω) : Integrable (fun z => Real.exp (V (ω, z))) P₀ ∧
      (∫ z, Real.exp (V (ω, z)) ∂P₀) =
        Real.exp ((gridVariance g θ - terminalGridBracket g θ (c ω)) / 2) := by
    let gr := g.residual (c ω)
    have h := independent_gaussian_weighted_mgf
      (fun j z => W (gr.channel j) (gr.upper j) z - W (gr.channel j) (gr.lower j) z)
      (fun j => ((hWjoint _).comp (measurable_const.prodMk measurable_id)).sub
        ((hWjoint _).comp (measurable_const.prodMk measurable_id)))
      (fun j => gr.upper j - gr.lower j) (hW κ gr).2 (hW κ gr).1 θ
    have hv : (∑ j, θ j ^ 2 * ((gr.upper j - gr.lower j : ℝ≥0) : ℝ)) =
        gridVariance g θ - terminalGridBracket g θ (c ω) := by
      have hd : ∀ j, ((gr.upper j - gr.lower j : ℝ≥0) : ℝ) =
          (gr.upper j : ℝ) - (gr.lower j : ℝ) := fun j => NNReal.coe_sub (gr.ordered j)
      simp_rw [hd]
      have heq := terminalGridBracket_add_residual g θ (c ω)
      change gridVariance gr θ = _
      linarith
    simpa only [hv] using h
  have hprod := product_mgf_of_terminal_normalization
    (originalGridSum g θ M A L) (fun ω => terminalGridBracket g θ (c ω)) V
    (gridVariance g θ) 1 hOm hVm
    (by simpa only [one_mul, one_pow] using hnorm.1)
    (by simpa only [one_mul, one_pow] using hnorm.2)
    (fun ω => by simpa only [one_mul] using (haux ω).1)
    (fun ω => by simpa only [one_mul, one_pow] using (haux ω).2)
  have hsplit (p : Ω × Ω₀) :
      (∑ j, θ j * (completedKnightTimeChange M A L W (g.channel j) (g.upper j) p -
        completedKnightTimeChange M A L W (g.channel j) (g.lower j) p)) =
        originalGridSum g θ M A L p.1 + V p := by
    unfold originalGridSum V
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    unfold completedKnightTimeChange
    rw [completedTimeChangePath_split _ _ _ _ (hWzero _ p.2),
      completedTimeChangePath_split _ _ _ _ (hWzero _ p.2)]
    ring
  simpa only [one_mul, one_pow, ← hsplit] using hprod

end Ripple.Stochastic.Knight
