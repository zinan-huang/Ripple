import Ripple.Stochastic.KnightCompletedIncrementLaw
import Ripple.Stochastic.KnightTimeChangeContinuity

/-!
# Completed Knight paths from normalized stopped exponentials

The completion takes place on one product extension. A single auxiliary
Brownian family suffices; no independence between different population sizes
is requested or asserted. The remaining stochastic inputs are normalization
of safe stopped sums, fibre constancy, and finite-clock convergence.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology BigOperators

namespace Ripple.Stochastic.Knight
open Ripple.Analysis Ripple.ProbabilityTheory

variable {ι Ω Ω₀ : Type} [Fintype ι]
  [MeasurableSpace Ω] [MeasurableSpace Ω₀]
  {P : Measure Ω} {P₀ : Measure Ω₀}
  [IsProbabilityMeasure P] [IsProbabilityMeasure P₀]

/-- Measurability of the completed process is derived from measurable original
inverse evaluations, terminal clocks, and joint auxiliary evaluation. -/
theorem measurable_completedKnightTimeChange
    (M : ι → ℝ≥0 → Ω → ℝ) (A : ι → ℝ≥0 → Ω → ℝ≥0) (L : ι → Ω → ℝ)
    (W : ι → ℝ≥0 → Ω₀ → ℝ)
    (hWzero : ∀ i z, W i 0 z = 0)
    (hWjoint : ∀ i, Measurable (Function.uncurry (W i)))
    (hterminal : ∀ i, Measurable (fun ω => terminalClock (fun t => A i t ω)))
    (hO : ∀ i u, Measurable (fun ω =>
      terminalOriginalPath (fun t => M i t ω) (fun t => A i t ω) (L i ω) u))
    (i : ι) (u : ℝ≥0) : Measurable (completedKnightTimeChange M A L W i u) := by
  classical
  have hres : Measurable (fun ω => terminalResidual (terminalClock (fun t => A i t ω)) u) := by
    unfold terminalResidual terminalClip
    exact measurable_const.sub (Measurable.ite
      (measurableSet_eq_fun (hterminal i) measurable_const)
      measurable_const (measurable_const.min (hterminal i).ennreal_toNNReal))
  have heq : completedKnightTimeChange M A L W i u = fun p : Ω × Ω₀ =>
      terminalOriginalPath (fun t => M i t p.1) (fun t => A i t p.1) (L i p.1) u +
        W i (terminalResidual (terminalClock (fun t => A i t p.1)) u) p.2 := by
    funext p
    exact completedTimeChangePath_split _ _ _ _ (hWzero i p.2) u
  rw [heq]
  exact ((hO i u).comp measurable_fst).add
    ((hWjoint i).comp ((hres.comp measurable_fst).prodMk measurable_snd))

/-- Completion supplies every rectangular increment law from normalized
original terminal exponentials. This includes all finite/infinite patterns
of the channel terminal clocks on the same original probability space. -/
theorem completed_rectangular_gaussian
    (M : ι → ℝ≥0 → Ω → ℝ) (A : ι → ℝ≥0 → Ω → ℝ≥0) (L : ι → Ω → ℝ)
    (W : ι → ℝ≥0 → Ω₀ → ℝ)
    (hW : HasRectangularGaussianIncrements W P₀)
    (hWzero : ∀ i z, W i 0 z = 0)
    (hWjoint : ∀ i, Measurable (Function.uncurry (W i)))
    (hterminal : ∀ i, Measurable (fun ω => terminalClock (fun t => A i t ω)))
    (hO : ∀ i u, Measurable (fun ω =>
      terminalOriginalPath (fun t => M i t ω) (fun t => A i t ω) (L i ω) u))
    (hnorm : ∀ (κ : Type) [Fintype κ] (g : IntervalGrid ι κ) (θ : κ → ℝ),
      Integrable (fun ω => Real.exp (originalGridSum g θ M A L ω -
        terminalGridBracket g θ (fun i => terminalClock (fun t => A i t ω)) / 2)) P ∧
      (∫ ω, Real.exp (originalGridSum g θ M A L ω -
        terminalGridBracket g θ (fun i => terminalClock (fun t => A i t ω)) / 2) ∂P) = 1) :
    HasRectangularGaussianIncrements (completedKnightTimeChange M A L W) (P.prod P₀) := by
  intro κ _ g
  apply independent_gaussian_family_of_mgf
    (fun j => (measurable_completedKnightTimeChange M A L W hWzero hWjoint hterminal hO
      (g.channel j) (g.upper j)).sub
      (measurable_completedKnightTimeChange M A L W hWzero hWjoint hterminal hO
        (g.channel j) (g.lower j)))
  intro θ
  have h := (completed_grid_mgf g θ M A L W hW hWzero hWjoint hterminal hO
    (hnorm κ g θ)).2
  have hdiff : ∀ j, ((g.upper j - g.lower j : ℝ≥0) : ℝ) =
      (g.upper j : ℝ) - (g.lower j : ℝ) := fun j => NNReal.coe_sub (g.ordered j)
  simp_rw [hdiff]
  simpa only [gridVariance, Finset.sum_div] using h

/-- Completed Brownian law, continuity, and all-time reconstruction on the
product extension. The original paths in the reconstruction are explicitly
lifted through `Prod.fst`. Terminal normalization is the remaining exponential
producer input, rather than a Brownian law or independence premise for β. -/
theorem completed_knight_of_terminal_normalization
    (M : ι → ℝ≥0 → Ω → ℝ) (A : ι → ℝ≥0 → Ω → ℝ≥0) (L : ι → Ω → ℝ)
    (W : ι → ℝ≥0 → Ω₀ → ℝ)
    (hW : ∀ i, IsPreBrownian (W i) P₀)
    (hWind : iIndepFun (fun i z t => W i t z) P₀)
    (hWzero : ∀ i z, W i 0 z = 0)
    (hWjoint : ∀ i, Measurable (Function.uncurry (W i)))
    (hWcont : ∀ i, ∀ᵐ z ∂P₀, Continuous (fun t => W i t z))
    (hc : ∀ i, ∀ᵐ ω ∂P, Continuous (fun t => A i t ω))
    (hm : ∀ i, ∀ᵐ ω ∂P, Monotone (fun t => A i t ω))
    (hz : ∀ i, ∀ᵐ ω ∂P, A i 0 ω = 0)
    (hMc : ∀ i, ∀ᵐ ω ∂P, Continuous (fun t => M i t ω))
    (hMz : ∀ i, ∀ᵐ ω ∂P, M i 0 ω = 0)
    (hflat : ∀ i, ∀ᵐ ω ∂P, ConstantOnClockFibres (fun t => A i t ω) (fun t => M i t ω))
    (hlim : ∀ i, ∀ᵐ ω ∂P, terminalClock (fun t => A i t ω) ≠ ⊤ →
      Tendsto (fun t => M i t ω) atTop (𝓝 (L i ω)))
    (hterminal : ∀ i, Measurable (fun ω => terminalClock (fun t => A i t ω)))
    (hO : ∀ i u, Measurable (fun ω =>
      terminalOriginalPath (fun t => M i t ω) (fun t => A i t ω) (L i ω) u))
    (hnorm : ∀ (κ : Type) [Fintype κ] (g : IntervalGrid ι κ) (θ : κ → ℝ),
      Integrable (fun ω => Real.exp (originalGridSum g θ M A L ω -
        terminalGridBracket g θ (fun i => terminalClock (fun t => A i t ω)) / 2)) P ∧
      (∫ ω, Real.exp (originalGridSum g θ M A L ω -
        terminalGridBracket g θ (fun i => terminalClock (fun t => A i t ω)) / 2) ∂P) = 1) :
    (∀ i u, Measurable (completedKnightTimeChange M A L W i u)) ∧
    (∀ i, IsPreBrownian (completedKnightTimeChange M A L W i) (P.prod P₀)) ∧
    (∀ i, ∀ᵐ p ∂P.prod P₀, Continuous (fun u => completedKnightTimeChange M A L W i u p)) ∧
    iIndepFun (fun i p u => completedKnightTimeChange M A L W i u p) (P.prod P₀) ∧
    (∀ᵐ p ∂P.prod P₀, ∀ i t,
      M i t p.1 = completedKnightTimeChange M A L W i (A i t p.1) p) := by
  have hmeas := measurable_completedKnightTimeChange M A L W hWzero hWjoint hterminal hO
  have hrect := completed_rectangular_gaussian M A L W
    (rectangular_of_brownian_family hW hWind) hWzero hWjoint hterminal hO hnorm
  have hreconstruct := completedKnightTimeChange_comp M A L W hc hm hz hflat hlim
    (fun i => ae_of_all P₀ (hWzero i))
  have hf : MeasurePreserving (Prod.fst : Ω × Ω₀ → Ω) (P.prod P₀) P :=
    measurePreserving_fst (μ := P) (ν := P₀)
  have hs : MeasurePreserving (Prod.snd : Ω × Ω₀ → Ω₀) (P.prod P₀) P₀ :=
    measurePreserving_snd (μ := P) (ν := P₀)
  have hzero : ∀ i, ∀ᵐ p ∂P.prod P₀, completedKnightTimeChange M A L W i 0 p = 0 := by
    intro i
    filter_upwards [hreconstruct, hf.quasiMeasurePreserving.ae (hz i),
      hf.quasiMeasurePreserving.ae (hMz i)] with p hr ha hmz
    simpa only [ha, hmz] using hr i 0
  obtain ⟨hB, hind⟩ := brownian_family_of_rectangular hrect hmeas hzero
  refine ⟨hmeas, hB, ?_, hind, hreconstruct.mono (fun p hp i t => (hp i t).symm)⟩
  intro i
  filter_upwards [hf.quasiMeasurePreserving.ae (hc i), hf.quasiMeasurePreserving.ae (hm i),
    hf.quasiMeasurePreserving.ae (hz i), hf.quasiMeasurePreserving.ae (hMc i),
    hf.quasiMeasurePreserving.ae (hflat i), hf.quasiMeasurePreserving.ae (hlim i),
    hs.quasiMeasurePreserving.ae (hWcont i)] with p hcω hmω hzω hMω hfω hlω hWω
  exact continuous_completedTimeChangePath hcω hmω hzω hMω hfω hlω hWω (hWzero i p.2)

end Ripple.Stochastic.Knight
