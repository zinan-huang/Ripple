/-
Ripple.BoundedUniversality.GPAC.TimeChangeConstruct
--------------------------------
Construction of the time change s(τ) = ∫₀ᵗ ρ(u) du where
ρ(u) = 1/(1+f̄(u)^N) is the surrogate speed function.

Properties:
- s(0) = 0
- s'(τ) = ρ(τ) > 0 (strictly increasing)
- s continuous
- s(τ) → ∞ when the original ODE exists for all time

This is the remaining piece connecting surrogateCompileOneVar
to bounded_surrogate_compilation via the Ripple ODE bridge.
-/

import Ripple.BoundedUniversality.GPAC.TimeChange
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace Ripple.BoundedUniversality.GPAC

open MeasureTheory

/-- The time change defined as an interval integral of the speed function.
ρ(τ) > 0 ensures s is strictly increasing. -/
noncomputable def timeChangeIntegral (ρ : ℝ → ℝ) (τ : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..τ, ρ u

/-- The time change satisfies s(0) = 0. -/
theorem timeChangeIntegral_zero (ρ : ℝ → ℝ) :
    timeChangeIntegral ρ 0 = 0 := by
  simp [timeChangeIntegral, intervalIntegral.integral_same]

/-- If ρ is continuous and positive, s is strictly increasing. -/
theorem timeChangeIntegral_strictMono
    (ρ : ℝ → ℝ) (hρ_cont : Continuous ρ) (hρ_pos : ∀ t, 0 < ρ t) :
    StrictMono (timeChangeIntegral ρ) := by
  intro a b hab
  have hsplit : timeChangeIntegral ρ b = timeChangeIntegral ρ a + ∫ u in a..b, ρ u := by
    unfold timeChangeIntegral
    have hii1 : IntervalIntegrable ρ volume 0 a := hρ_cont.intervalIntegrable 0 a
    have hii2 : IntervalIntegrable ρ volume a b := hρ_cont.intervalIntegrable a b
    simpa [add_comm, add_left_comm, add_assoc] using
      (intervalIntegral.integral_add_adjacent_intervals hii1 hii2).symm
  have hpos : 0 < ∫ u in a..b, ρ u :=
    intervalIntegral.intervalIntegral_pos_of_pos
      (hρ_cont.intervalIntegrable a b) hρ_pos hab
  linarith

/-- If ρ ≥ c > 0 for some constant c, then s(τ) ≥ c·τ → ∞. -/
theorem timeChangeIntegral_tendsto
    (ρ : ℝ → ℝ) (hρ_cont : Continuous ρ)
    (c : ℝ) (hc : 0 < c) (hρ_lb : ∀ t, c ≤ ρ t) :
    Filter.Tendsto (timeChangeIntegral ρ) Filter.atTop Filter.atTop := by
  have hlower : ∀ τ : ℝ, 0 ≤ τ → c * τ ≤ timeChangeIntegral ρ τ := by
    intro τ hτ
    have h_const_int : IntervalIntegrable (fun _ : ℝ => c) volume 0 τ :=
      continuous_const.intervalIntegrable 0 τ
    have hρ_int : IntervalIntegrable ρ volume 0 τ :=
      hρ_cont.intervalIntegrable 0 τ
    have hle_int : (∫ u in (0 : ℝ)..τ, c) ≤ ∫ u in (0 : ℝ)..τ, ρ u :=
      intervalIntegral.integral_mono_on hτ h_const_int hρ_int (fun u _ => hρ_lb u)
    have hconst : (∫ _u in (0 : ℝ)..τ, c) = c * τ := by
      rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_comm]
    simpa [timeChangeIntegral, hconst] using hle_int
  refine Filter.tendsto_atTop_mono' Filter.atTop ?_
    (Filter.Tendsto.const_mul_atTop hc Filter.tendsto_id)
  exact (Filter.eventually_ge_atTop (0 : ℝ)).mono fun τ hτ => hlower τ hτ

/-- If ρ is continuous, s has HasDerivAt s (ρ τ) τ (FTC). -/
theorem timeChangeIntegral_hasDerivAt
    (ρ : ℝ → ℝ) (hρ_cont : Continuous ρ) (τ : ℝ) :
    HasDerivAt (timeChangeIntegral ρ) (ρ τ) τ := by
  unfold timeChangeIntegral
  exact (hρ_cont.integral_hasStrictDerivAt (a := 0) (b := τ)).hasDerivAt

/-- Tail-surjectivity from continuous + strictly increasing + Tendsto. -/
theorem tailSurj_of_strictMono_tendsto
    {s : ℝ → ℝ} (hs_cont : Continuous s) (hs_mono : StrictMono s)
    (hs_zero : s 0 = 0) (hs_tendsto : Filter.Tendsto s Filter.atTop Filter.atTop) :
    ∀ T' : ℝ, ∃ T : ℝ, ∀ t ≥ T, ∃ τ ≥ T', s τ = t := by
  have _ : StrictMono s := hs_mono
  have _ : s 0 = 0 := hs_zero
  intro T'
  refine ⟨s T', ?_⟩
  intro t ht
  obtain ⟨R0, hR0⟩ := (Filter.tendsto_atTop_atTop.mp hs_tendsto) t
  let R : ℝ := max T' R0
  have hT'R : T' ≤ R := le_max_left T' R0
  have hR0R : R0 ≤ R := le_max_right T' R0
  have ht_le_sR : t ≤ s R := hR0 R hR0R
  have hmem : t ∈ Set.Icc (s T') (s R) := ⟨ht, ht_le_sR⟩
  have himage : t ∈ s '' Set.Icc T' R :=
    intermediate_value_Icc hT'R hs_cont.continuousOn hmem
  rcases himage with ⟨τ, hτ, hτeq⟩
  exact ⟨τ, hτ.1, hτeq⟩

end Ripple.BoundedUniversality.GPAC
