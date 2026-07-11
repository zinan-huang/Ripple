/-
  Ripple.Kurtz.JumpBracket — Predictable Quadratic Variation for PLPP Martingales

  Computes the algebraic bracket bound for density-dependent CTMCs.
  The key result: the per-coordinate predictable QV satisfies

    ⟨M_i⟩_T ≤ (J_∞² · Λ_max · |α| · T) / N

  and the trace bound (sum over coordinates):

    Σ_i ⟨M_i⟩_T ≤ (J₂² · Λ_max · |α| · T) / N

  These are pure algebra — no measure theory needed.
  The counting-process-compensator → bracket-formula implication is
  deferred (3-8 weeks of probability infrastructure).
-/

import Ripple.Kurtz.JumpModel
import Mathlib.MeasureTheory.Measure.MeasureSpace

namespace Ripple.Kurtz

open Finset MeasureTheory

/-- Martingale data for a density-dependent CTMC with N agents.
    Associates a density process Z, coordinate martingales M,
    and their predictable brackets with a DensityJumpModel. -/
structure DensityMartingaleData
    (Ω ι α : Type*) [MeasurableSpace Ω]
    [Fintype ι] [Fintype α] where
  μ : Measure Ω
  N : ℕ
  Z : ℝ → Ω → ι → ℝ
  M : ι → ℝ → Ω → ℝ
  bracket : ι → ℝ → Ω → ℝ
  model : DensityJumpModel ι α
  hN : 0 < N
  bracket_formula : ∀ᵐ ω ∂μ, ∀ i t, 0 ≤ t →
    bracket i t ω ≤ (1 / (N : ℝ)) *
      ∑ a : α, (model.gamma a i) ^ 2 *
        (model.LambdaMax * t)

/-- Per-coordinate bracket bound. -/
theorem coordinate_bracket_bound
    {Ω ι α : Type*} [MeasurableSpace Ω]
    [Fintype ι] [Fintype α]
    (data : DensityMartingaleData Ω ι α) :
    ∀ᵐ ω ∂data.μ, ∀ i T, 0 ≤ T →
      data.bracket i T ω ≤
        data.model.J ^ 2 * data.model.LambdaMax *
          (Fintype.card α : ℝ) * T / (data.N : ℝ) := by
  filter_upwards [data.bracket_formula] with ω hbracket
  intro i T hT
  have hNpos : (0 : ℝ) < (data.N : ℝ) := by
    exact_mod_cast data.hN
  have hNnonneg : 0 ≤ (1 / (data.N : ℝ)) := by
    positivity
  have hLambdaT : 0 ≤ data.model.LambdaMax * T :=
    mul_nonneg data.model.LambdaMax_nonneg hT
  have hsum :
      (∑ a : α, (data.model.gamma a i) ^ 2 *
        (data.model.LambdaMax * T)) ≤
        ∑ a : α, data.model.J ^ 2 * (data.model.LambdaMax * T) := by
    refine Finset.sum_le_sum fun a _ => ?_
    have hgamma_sq : (data.model.gamma a i) ^ 2 ≤ data.model.J ^ 2 := by
      rw [sq_le_sq]
      simpa [abs_of_nonneg data.model.J_nonneg] using data.model.gamma_linf_le a i
    exact mul_le_mul_of_nonneg_right hgamma_sq hLambdaT
  have hsum_const :
      (∑ a : α, data.model.J ^ 2 * (data.model.LambdaMax * T)) =
        (Fintype.card α : ℝ) *
          (data.model.J ^ 2 * (data.model.LambdaMax * T)) := by
    simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  calc
    data.bracket i T ω ≤
        (1 / (data.N : ℝ)) *
          ∑ a : α, (data.model.gamma a i) ^ 2 *
            (data.model.LambdaMax * T) := hbracket i T hT
    _ ≤ (1 / (data.N : ℝ)) *
        ((Fintype.card α : ℝ) *
          (data.model.J ^ 2 * (data.model.LambdaMax * T))) := by
      exact mul_le_mul_of_nonneg_left (hsum.trans_eq hsum_const) hNnonneg
    _ = data.model.J ^ 2 * data.model.LambdaMax *
          (Fintype.card α : ℝ) * T / (data.N : ℝ) := by
      ring_nf

/-- Trace bracket bound (sum over all coordinates). -/
noncomputable def traceBracket
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (bracket : ι → ℝ → Ω → ℝ) (T : ℝ) (ω : Ω) : ℝ :=
  ∑ i, bracket i T ω

theorem trace_bracket_bound
    {Ω ι α : Type*} [MeasurableSpace Ω]
    [Fintype ι] [Fintype α]
    (data : DensityMartingaleData Ω ι α) :
    ∀ᵐ ω ∂data.μ, ∀ T, 0 ≤ T →
      traceBracket data.bracket T ω ≤
        data.model.J ^ 2 * data.model.LambdaMax *
          (Fintype.card α : ℝ) * (Fintype.card ι : ℝ) * T /
            (data.N : ℝ) := by
  filter_upwards [coordinate_bracket_bound data] with ω hcoord
  intro T hT
  unfold traceBracket
  calc
    (∑ i, data.bracket i T ω) ≤
        ∑ i : ι, data.model.J ^ 2 * data.model.LambdaMax *
          (Fintype.card α : ℝ) * T / (data.N : ℝ) := by
      exact Finset.sum_le_sum fun i _ => hcoord i T hT
    _ = data.model.J ^ 2 * data.model.LambdaMax *
          (Fintype.card α : ℝ) * (Fintype.card ι : ℝ) * T /
            (data.N : ℝ) := by
      simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring_nf

end Ripple.Kurtz
