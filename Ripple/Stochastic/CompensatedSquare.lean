/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic

/-!
# A compensated-square criterion from conditional increment moments

For adapted square-integrable `M` and adapted integrable `Q`, zero conditional first
increment moments and the conditional identity `E[(ΔM)² | F_s] = E[ΔQ | F_s]`
imply that `M² - Q` is a martingale. The first identity kills the mixed term by
pulling out the past factor. No stochastic integral or bracket is constructed here.
-/

open MeasureTheory Filter

namespace Ripple.Stochastic.CompensatedSquare

variable {ι Ω : Type*} [Preorder ι] [mΩ : MeasurableSpace Ω]
variable {μ : Measure Ω} [IsFiniteMeasure μ] {F : Filtration ι mΩ}
variable {M Q : ι → Ω → ℝ}

/-- Conditional first and second increment identities imply the compensated-square martingale.
The second moment is conditional on the same past sigma-algebra as the first moment;
an unconditional Itô isometry does not supply this premise. -/
theorem martingale_sq_sub_of_conditional_increment_moments
    (hM : StronglyAdapted F M) (hQ : StronglyAdapted F Q)
    (hMmem : ∀ t, MemLp (M t) 2 μ) (hQint : ∀ t, Integrable (Q t) μ)
    (hfirst : ∀ s t, s ≤ t →
      μ[(fun ω => M t ω - M s ω) | F s] =ᵐ[μ] 0)
    (hsecond : ∀ s t, s ≤ t →
      μ[(fun ω => (M t ω - M s ω) ^ 2) | F s] =ᵐ[μ]
        μ[(fun ω => Q t ω - Q s ω) | F s]) :
    Martingale (fun t ω => (M t ω) ^ 2 - Q t ω) F μ := by
  let C : ι → Ω → ℝ := fun t ω => (M t ω) ^ 2 - Q t ω
  have hadapt : StronglyAdapted F C := fun t => ((hM t).pow 2).sub (hQ t)
  have hint : ∀ t, Integrable (C t) μ := fun t =>
    (hMmem t).integrable_sq.sub (hQint t)
  refine ⟨hadapt, fun s t hst => ?_⟩
  let d : Ω → ℝ := fun ω => M t ω - M s ω
  let v : Ω → ℝ := fun ω => d ω ^ 2 - (Q t ω - Q s ω)
  let c : Ω → ℝ := fun ω => M s ω * d ω
  have hd : MemLp d 2 μ := (hMmem t).sub (hMmem s)
  have hdint : Integrable d μ := hd.integrable (by norm_num)
  have hvint : Integrable v μ := hd.integrable_sq.sub ((hQint t).sub (hQint s))
  have hcint : Integrable c μ := (hMmem s).integrable_mul hd
  have hvzero : μ[v | F s] =ᵐ[μ] 0 := by
    have hsplit := condExp_sub hd.integrable_sq ((hQint t).sub (hQint s)) (F s)
    filter_upwards [hsplit, hsecond s t hst] with ω hs hsecondω
    change (μ[v | F s]) ω = 0
    change (μ[v | F s]) ω =
      (μ[(fun ω => d ω ^ 2) | F s]) ω -
        (μ[(fun ω => Q t ω - Q s ω) | F s]) ω at hs
    rw [hs]
    exact sub_eq_zero.mpr hsecondω
  have hczero : μ[c | F s] =ᵐ[μ] 0 := by
    have hpull : μ[c | F s] =ᵐ[μ]
        fun ω => M s ω * (μ[d | F s]) ω :=
      condExp_mul_of_stronglyMeasurable_left (hM s) hcint hdint
    filter_upwards [hpull, hfirst s t hst] with ω hp hf
    change (μ[c | F s]) ω = 0
    change (μ[d | F s]) ω = 0 at hf
    rw [hp, hf, mul_zero]
  have hexpand : C t - C s = (v + c) + c := by
    funext ω
    dsimp [C, v, c, d]
    ring
  have hzero : μ[C t - C s | F s] =ᵐ[μ] 0 := by
    rw [hexpand]
    filter_upwards [condExp_add (hvint.add hcint) hcint (F s),
      condExp_add hvint hcint (F s), hvzero, hczero] with ω ha hb hv hc
    change (μ[(v + c) + c | F s]) ω = 0
    change (μ[(v + c) + c | F s]) ω =
      (μ[v + c | F s]) ω + (μ[c | F s]) ω at ha
    change (μ[v + c | F s]) ω =
      (μ[v | F s]) ω + (μ[c | F s]) ω at hb
    change (μ[v | F s]) ω = 0 at hv
    change (μ[c | F s]) ω = 0 at hc
    rw [ha, hb, hv, hc, add_zero, add_zero]
  have hsplit := condExp_sub (hint t) (hint s) (F s)
  have hself : μ[C s | F s] = C s :=
    condExp_of_stronglyMeasurable (F.le s) (hadapt s) (hint s)
  filter_upwards [hsplit, hzero] with ω hs hz
  change (μ[C t | F s]) ω = C s ω
  change (μ[C t - C s | F s]) ω =
    (μ[C t | F s]) ω - (μ[C s | F s]) ω at hs
  rw [hself] at hs
  change (μ[C t - C s | F s]) ω = 0 at hz
  linarith

end Ripple.Stochastic.CompensatedSquare
