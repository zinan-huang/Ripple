import Ripple.Stochastic.KnightStepGrid
import Ripple.Stochastic.KnightStoppedClock
import Ripple.Stochastic.GaussianChannelExponential

/-!
# Splitting a completed rectangular grid at terminal clocks

The original contribution at an unreachable clock level is the terminal path
value. It is never evaluation of an infinite inverse through `toNNReal`.
Clipped and residual interval lengths add to the original interval length;
the same identity therefore holds for their weighted variances.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology BigOperators

namespace Ripple.Stochastic.Knight
open Ripple.Analysis Ripple.ProbabilityTheory

/-- The part of an internal time supplied by the original path. -/
def terminalClip (c : ℝ≥0∞) (u : ℝ≥0) : ℝ≥0 :=
  if c = ⊤ then u else min u c.toNNReal

/-- Time supplied by the auxiliary process. Infinite original clocks need no
auxiliary time. -/
def terminalResidual (c : ℝ≥0∞) (u : ℝ≥0) : ℝ≥0 := u - terminalClip c u

theorem terminalClip_le (c : ℝ≥0∞) (u : ℝ≥0) : terminalClip c u ≤ u := by
  unfold terminalClip
  split_ifs <;> simp

theorem terminalClip_add_residual (c : ℝ≥0∞) (u : ℝ≥0) :
    terminalClip c u + terminalResidual c u = u :=
  add_tsub_cancel_of_le (terminalClip_le c u)

theorem terminalClip_mono (c : ℝ≥0∞) : Monotone (terminalClip c) := by
  intro u v huv
  unfold terminalClip
  split_ifs
  · exact huv
  · exact min_le_min_right _ huv

theorem terminalResidual_mono (c : ℝ≥0∞) : Monotone (terminalResidual c) := by
  intro u v huv
  by_cases hc : c = ⊤
  · simp [terminalResidual, terminalClip, hc]
  · have key : ∀ u c : ℝ≥0, u - min u c = u - c := by
      intro u c
      rcases le_total u c with h | h
      · simp [min_eq_left h, tsub_eq_zero_of_le h]
      · simp [min_eq_right h]
    simp only [terminalResidual, terminalClip, if_neg hc, key]
    exact tsub_le_tsub_right huv _

theorem terminalClip_of_lt {c : ℝ≥0∞} {u : ℝ≥0} (hu : (u : ℝ≥0∞) < c) :
    terminalClip c u = u := by
  by_cases hc : c = ⊤
  · simp [terminalClip, hc]
  · have hul : u ≤ c.toNNReal := by
      rw [← ENNReal.coe_toNNReal hc] at hu
      exact_mod_cast hu.le
    simp [terminalClip, hc, min_eq_left hul]

theorem terminalClip_of_le {c : ℝ≥0∞} {u : ℝ≥0} (hu : c ≤ (u : ℝ≥0∞)) :
    terminalClip c u = c.toNNReal := by
  have hc : c ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hu
  have hcu : c.toNNReal ≤ u := by
    rw [← ENNReal.coe_toNNReal hc] at hu
    exact_mod_cast hu
  simp [terminalClip, hc, min_eq_right hcu]

theorem coe_terminalClip_le (c : ℝ≥0∞) (u : ℝ≥0) :
    (terminalClip c u : ℝ≥0∞) ≤ c := by
  by_cases hc : c = ⊤
  · simp [hc]
  · rw [terminalClip, if_neg hc, ← ENNReal.coe_toNNReal hc]
    exact_mod_cast min_le_right u c.toNNReal

/-- Clipping the increasing clock commutes with its terminal limit, whether
the terminal clock is finite or infinite. The proof uses the defining
supremum, so no finite terminal-clock convergence is assumed. -/
theorem min_clock_tendsto_terminalClip {A : ℝ≥0 → ℝ≥0}
    (hm : Monotone A) (u : ℝ≥0) :
    Tendsto (fun t => min (A t) u) atTop (𝓝 (terminalClip (terminalClock A) u)) := by
  have hbound (t : ℝ≥0) : min (A t) u ≤ terminalClip (terminalClock A) u := by
    by_cases hc : terminalClock A = ⊤
    · simpa [terminalClip, hc] using min_le_right (A t) u
    · have ht : A t ≤ (terminalClock A).toNNReal := by
        have hh := le_iSup (fun s : ℝ≥0 => (A s : ℝ≥0∞)) t
        change (A t : ℝ≥0∞) ≤ terminalClock A at hh
        rw [← ENNReal.coe_toNNReal hc] at hh
        exact_mod_cast hh
      simpa [terminalClip, hc, min_comm] using min_le_min_right u ht
  apply tendsto_order.2
  constructor
  · intro a ha
    have hau : a < u := ha.trans_le (terminalClip_le _ _)
    have hac : (a : ℝ≥0∞) < terminalClock A :=
      (show (a : ℝ≥0∞) < (terminalClip (terminalClock A) u : ℝ≥0∞) by
        exact_mod_cast ha).trans_le (coe_terminalClip_le _ _)
    obtain ⟨s, hs⟩ := lt_iSup_iff.mp hac
    have has : a < A s := by exact_mod_cast hs
    filter_upwards [eventually_ge_atTop s] with t ht
    exact lt_min (has.trans_le (hm ht)) hau
  · intro b hb
    exact Eventually.of_forall fun t => (hbound t).trans_lt hb

/-- The original term in the completed path, including unreachable levels. -/
def terminalOriginalPath (M : ℝ≥0 → ℝ) (A : ℝ≥0 → ℝ≥0) (L : ℝ) (u : ℝ≥0) : ℝ :=
  if (u : ℝ≥0∞) < terminalClock A then rawTimeChangePath M A u else L

theorem completedTimeChangePath_split
    (M : ℝ≥0 → ℝ) (A : ℝ≥0 → ℝ≥0) (L : ℝ) (W : ℝ≥0 → ℝ)
    (hW : W 0 = 0) (u : ℝ≥0) :
    completedTimeChangePath M A L W u = terminalOriginalPath M A L u +
      W (terminalResidual (terminalClock A) u) := by
  by_cases hu : (u : ℝ≥0∞) < terminalClock A
  · simp [completedTimeChangePath, terminalOriginalPath, hu, terminalResidual,
      terminalClip_of_lt hu, hW]
  · simp [completedTimeChangePath, terminalOriginalPath, hu, terminalResidual,
      terminalClip_of_le (le_of_not_gt hu)]

/-- Safe inverse stopping converges to the original part of the completed
path, including levels at and above a finite terminal clock. -/
theorem clockStoppedPath_tendsto_terminalOriginalPath
    {M : ℝ≥0 → ℝ} {A : ℝ≥0 → ℝ≥0} {L : ℝ}
    (hlim : terminalClock A ≠ ⊤ → Tendsto M atTop (𝓝 L)) (u : ℝ≥0) :
    Tendsto (clockStoppedPath M A u) atTop (𝓝 (terminalOriginalPath M A L u)) := by
  by_cases hu : (u : ℝ≥0∞) < terminalClock A
  · have hfinite : clockInverse A u ≠ ⊤ := clockInverse_ne_top_of_lt_terminal hu
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (clockInverse A u).toNNReal] with t ht
    simp [clockStoppedPath, clockStoppedTime, hfinite, min_eq_right ht,
      terminalOriginalPath, hu, rawTimeChangePath]
  · have hle := le_of_not_gt hu
    rw [clockStoppedPath_eq_of_terminal_le hle]
    simpa [terminalOriginalPath, hu] using
      hlim (ne_top_of_le_ne_top ENNReal.coe_ne_top hle)

variable {ι κ : Type*} [Fintype κ]

/-- Removing the original part of each internal interval preserves its order
and disjointness within every channel, even with random channelwise seams. -/
def IntervalGrid.residual (g : IntervalGrid ι κ) (c : ι → ℝ≥0∞) : IntervalGrid ι κ where
  channel := g.channel
  lower := fun j => terminalResidual (c (g.channel j)) (g.lower j)
  upper := fun j => terminalResidual (c (g.channel j)) (g.upper j)
  ordered := fun j => terminalResidual_mono _ (g.ordered j)
  separated := by
    intro j k hjk heq
    rcases g.separated j k hjk heq with h | h
    · exact Or.inl (by simpa only [heq] using terminalResidual_mono (c (g.channel k)) h)
    · exact Or.inr (by simpa only [heq] using terminalResidual_mono (c (g.channel k)) h)

/-- Random variance supplied by the original stopped integral. -/
def terminalGridBracket (g : IntervalGrid ι κ) (θ : κ → ℝ) (c : ι → ℝ≥0∞) : ℝ :=
  ∑ j, θ j ^ 2 * ((terminalClip (c (g.channel j)) (g.upper j) : ℝ) -
    (terminalClip (c (g.channel j)) (g.lower j) : ℝ))

theorem terminalGridBracket_add_residual (g : IntervalGrid ι κ) (θ : κ → ℝ)
    (c : ι → ℝ≥0∞) :
    terminalGridBracket g θ c + gridVariance (g.residual c) θ = gridVariance g θ := by
  unfold terminalGridBracket gridVariance
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have hu := congrArg (fun x : ℝ≥0 => (x : ℝ))
    (terminalClip_add_residual (c (g.channel j)) (g.upper j))
  have hl := congrArg (fun x : ℝ≥0 => (x : ℝ))
    (terminalClip_add_residual (c (g.channel j)) (g.lower j))
  simp only [NNReal.coe_add] at hu hl
  change θ j ^ 2 * _ + θ j ^ 2 *
    ((terminalResidual (c (g.channel j)) (g.upper j) : ℝ) -
      (terminalResidual (c (g.channel j)) (g.lower j) : ℝ)) = _
  rw [← mul_add]
  congr 1
  linarith

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- The exponential moment of an arbitrary finite weighted independent
centered Gaussian vector, with integrability proved before integration. -/
theorem independent_gaussian_weighted_mgf
    (X : κ → Ω → ℝ) (hX : ∀ j, Measurable (X j)) (v : κ → ℝ≥0)
    (hLaw : ∀ j, HasLaw (X j) (gaussianReal 0 (v j)) P)
    (hind : iIndepFun X P) (θ : κ → ℝ) :
    Integrable (fun ω => Real.exp (∑ j, θ j * X j ω)) P ∧
      (∫ ω, Real.exp (∑ j, θ j * X j ω) ∂P) =
        Real.exp ((∑ j, θ j ^ 2 * (v j : ℝ)) / 2) := by
  let G := fun j ω => Real.exp (θ j * X j ω)
  have hG : ∀ j, Measurable (G j) := fun j => ((hX j).const_mul (θ j)).exp
  have hgi : ∀ j, Integrable (G j) P := fun j => by
    have h1 : Integrable (fun x : ℝ => Real.exp (θ j * x)) (P.map (X j)) := by
      rw [(hLaw j).map_eq]
      exact integrable_exp_mul_gaussianReal (θ j)
    exact h1.comp_aemeasurable (hLaw j).aemeasurable
  have hgd : iIndepFun G P := hind.comp
    (fun j x => Real.exp (θ j * x)) (fun _ => by fun_prop)
  have hprod (ω : Ω) : Real.exp (∑ j, θ j * X j ω) = ∏ j, G j ω :=
    Real.exp_sum _ _
  simp_rw [hprod]
  refine ⟨GaussianChannelExponential.integrable_prod_of_independent G hG hgi hgd
    Finset.univ, ?_⟩
  rw [hgd.integral_fun_prod_eq_prod_integral (fun j => (hG j).aestronglyMeasurable)]
  have hm (j : κ) : (∫ ω, G j ω ∂P) = Real.exp (θ j ^ 2 * (v j : ℝ) / 2) := by
    have h := mgf_gaussianReal (hLaw j).map_eq (θ j)
    simpa only [mgf, G, zero_mul, zero_add, mul_comm (v j : ℝ)] using h
  simp_rw [hm]
  rw [← Real.exp_sum, Finset.sum_div]

end Ripple.Stochastic.Knight
