/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# ClockWindowFields

Field values for the C0 clock-window route-A reducer.

This file discharges the scalar field of
`ClockDriftCardWindow.Phase0CardAffineScalar` and assembles the
`Slot0HtailAssembly.Phase0ClockZeroPrefixTail` through the landed route-A reducer.

Boundary:

The remaining protocol-heavy value is the all-phase pair summand bound
`ClockDriftCardWindow.AllPhaseClockPairBound`.  It is the 11-phase deterministic
case split over `Transition`; this file keeps it as a single explicit argument
instead of burying an unexported proof.  The transition facts needed for that proof
are exactly the ones in `Protocol/Transition.lean`:

* `phaseInit` resets clock counters on counter-reset phase entries;
* `advancePhase` only changes `phase`;
* `stdCounterSubroutine` either decrements an existing clock or advances through
  `phaseInit`;
* Phase-0 Rule 4 creates one fresh full-counter clock and one reserve.

No `sorry` / `admit` / `axiom` / `native_decide`.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockDriftCardWindow

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal Real

namespace ClockWindowFields

open ClockDriftCardWindow
open Phase0PrefixTailDischarge
open Slot0HtailAssembly
open Phase0Window
open RoleSplitConcentration

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-! ## Scalar arithmetic -/

/-- `ENNReal.ofReal` commutes with powers on nonnegative reals (inline, since
`ENNReal.ofReal_pow` is not available in this Mathlib). -/
theorem ofReal_pow_eq {p : ℝ} (hp : 0 ≤ p) :
    ∀ m : ℕ, ENNReal.ofReal (p ^ m) = ENNReal.ofReal p ^ m
  | 0 => by simp
  | (m + 1) => by
      rw [pow_succ, pow_succ, ENNReal.ofReal_mul (pow_nonneg hp m),
        ofReal_pow_eq hp m]

/-- The real base used by `phase0AffineA`. -/
noncomputable def phase0AffineAReal (n : ℕ) : ℝ :=
  1 + 2 * (Real.exp 1 - 1) / (n : ℝ)

/-- Nonnegativity of the real affine base. -/
theorem phase0AffineAReal_nonneg (n : ℕ) :
    0 ≤ phase0AffineAReal n := by
  unfold phase0AffineAReal
  have he : 0 ≤ Real.exp 1 - 1 := by
    linarith [Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)]
  have hn : 0 ≤ (n : ℝ) := by positivity
  have hterm : 0 ≤ 2 * (Real.exp 1 - 1) / (n : ℝ) :=
    div_nonneg (mul_nonneg (by norm_num) he) hn
  linarith

/-- The affine base is at least one. -/
theorem one_le_phase0AffineAReal (n : ℕ) :
    1 ≤ phase0AffineAReal n := by
  unfold phase0AffineAReal
  have he : 0 ≤ Real.exp 1 - 1 := by
    linarith [Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)]
  have hn : 0 ≤ (n : ℝ) := by positivity
  have hterm : 0 ≤ 2 * (Real.exp 1 - 1) / (n : ℝ) :=
    div_nonneg (mul_nonneg (by norm_num) he) hn
  linarith

/-- `phase0AffineA n = ofReal (phase0AffineAReal n)`. -/
theorem phase0AffineA_eq_ofReal (n : ℕ) :
    phase0AffineA n = ENNReal.ofReal (phase0AffineAReal n) := by
  rfl

/-- `phase0AffineB L = ofReal(exp(-50(L+1)))`, with the harmless `1 *` removed. -/
theorem phase0AffineB_eq_ofReal (L : ℕ) :
    phase0AffineB L =
      ENNReal.ofReal (Real.exp (-(50 * (L + 1) : ℕ))) := by
  simp [phase0AffineB]

/-- The clock-zero budget as an `ofReal`. -/
theorem phase0ClockZeroBudget_eq_ofReal (L : ℕ) :
    phase0ClockZeroBudget L =
      ENNReal.ofReal (Real.exp (-(45 * (L + 1) : ℕ))) := by
  rfl

/--
Sharp real geometric bound:
`∑_{i<τ} a^i ≤ n * a^τ` for `a = 1 + 2(e-1)/n`.

The proof avoids the naive `τ*a^τ` loss.  Inductively,
`sum_{i<t+1} a^i ≤ n*a^t + a^t = (n+1)*a^t ≤ n*a*a^t`,
using `1 ≤ n*(a-1)`, which follows from `1 ≤ 2(e-1)`.
-/
theorem geom_sum_phase0AffineAReal_le
    (n τ : ℕ) (hn : 1 ≤ n) :
    (∑ i ∈ Finset.range τ, (phase0AffineAReal n) ^ i)
      ≤ (n : ℝ) * (phase0AffineAReal n) ^ τ := by
  classical
  set a := phase0AffineAReal n with ha
  have ha1 : 1 ≤ a := by
    rw [ha]
    exact one_le_phase0AffineAReal n
  have ha0 : 0 ≤ a := le_trans (by norm_num : (0 : ℝ) ≤ 1) ha1
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hcoef : 1 ≤ (n : ℝ) * (a - 1) := by
    rw [ha]
    unfold phase0AffineAReal
    have he_lb : (1 : ℝ) ≤ 2 * (Real.exp 1 - 1) := by
      have h : (2 : ℝ) ≤ Real.exp 1 := by
        have := Real.add_one_le_exp (1 : ℝ)
        nlinarith
      nlinarith
    calc
      (1 : ℝ) ≤ 2 * (Real.exp 1 - 1) := he_lb
      _ = (n : ℝ) * (2 * (Real.exp 1 - 1) / (n : ℝ)) := by
            field_simp [ne_of_gt hnpos]
      _ = (n : ℝ) * (1 + 2 * (Real.exp 1 - 1) / (n : ℝ) - 1) := by
            ring
  induction τ with
  | zero =>
      simp [hnpos.le]
  | succ τ ih =>
      rw [Finset.sum_range_succ]
      calc
        (∑ i ∈ Finset.range τ, a ^ i) + a ^ τ
            ≤ (n : ℝ) * a ^ τ + a ^ τ := by
              gcongr
        _ = ((n : ℝ) + 1) * a ^ τ := by ring
        _ ≤ ((n : ℝ) * a) * a ^ τ := by
              gcongr
              have hstep : (n : ℝ) + 1 ≤ (n : ℝ) * a := by
                have hexp : (n : ℝ) * (a - 1) = (n : ℝ) * a - (n : ℝ) := by ring
                linarith [hcoef, hexp]
              exact hstep
        _ = (n : ℝ) * a ^ (τ + 1) := by
              rw [pow_succ]
              ring

/--
ENNReal version of the sharp geometric bound.
-/
theorem geom_sum_phase0AffineA_le
    (n τ : ℕ) (hn : 1 ≤ n) :
    (∑ i ∈ Finset.range τ, phase0AffineA n ^ i)
      ≤ (n : ℝ≥0∞) * phase0AffineA n ^ τ := by
  classical
  have ha0 : 0 ≤ phase0AffineAReal n := phase0AffineAReal_nonneg n
  have hL :
      (∑ i ∈ Finset.range τ, phase0AffineA n ^ i)
        = ENNReal.ofReal (∑ i ∈ Finset.range τ, (phase0AffineAReal n) ^ i) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => pow_nonneg ha0 i)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [phase0AffineA_eq_ofReal, ofReal_pow_eq ha0 i]
  have hR :
      (n : ℝ≥0∞) * phase0AffineA n ^ τ
        = ENNReal.ofReal ((n : ℝ) * (phase0AffineAReal n) ^ τ) := by
    rw [phase0AffineA_eq_ofReal, ← ofReal_pow_eq ha0 τ,
        ← ENNReal.ofReal_natCast n,
        ← ENNReal.ofReal_mul (by positivity : 0 ≤ (n : ℝ))]
  rw [hL, hR]
  exact ENNReal.ofReal_le_ofReal
    (geom_sum_phase0AffineAReal_le n τ hn)

/--
The scalar clock-window prefix bound.

Hypotheses:
* `1 ≤ n`;
* `t ≤ n*(L+1)`;
* `log n ≤ L+1`.

The proof uses the sharp geometric bound above and the landed
`Phase0Window.phase0_numerics_real`.
-/
theorem phase0_cardAffine_hscalar
    {n t : ℕ}
    (hn : 1 ≤ n)
    (ht : t ≤ n * (L + 1))
    (hlog : Real.log (n : ℝ) ≤ (L + 1 : ℕ)) :
    ∀ c₀,
      RoleSplitConcentration.Phase0Initial (L := L) (K := K) n c₀ →
      ∀ τ ∈ Finset.range t,
        (phase0AffineA n ^ τ *
            Phase0Window.clockCounterPotential (L := L) (K := K) 1 c₀
          + phase0AffineB L *
              ∑ i ∈ Finset.range τ, phase0AffineA n ^ i)
          / (1 : ℝ≥0∞)
        ≤ Slot0HtailAssembly.phase0ClockZeroBudget L := by
  intro c₀ hinit τ hτmem
  have hΦ0 :
      Phase0Window.clockCounterPotential (L := L) (K := K) 1 c₀ = 0 :=
    ClockDriftCardWindow.clockCounterPotential_eq_zero_of_phase0Initial
      (L := L) (K := K) hinit

  have hτle : τ ≤ n * (L + 1) := by
    exact le_trans (Nat.le_of_lt (Finset.mem_range.mp hτmem)) ht

  have hgeom :
      (∑ i ∈ Finset.range τ, phase0AffineA n ^ i)
        ≤ (n : ℝ≥0∞) * phase0AffineA n ^ τ :=
    geom_sum_phase0AffineA_le n τ hn

  have hnclock :
      phase0AffineA n ^ τ * ((n : ℝ≥0∞) * phase0AffineB L)
        ≤ phase0ClockZeroBudget L := by
    rw [phase0AffineA_eq_ofReal, phase0AffineB_eq_ofReal,
        phase0ClockZeroBudget_eq_ofReal]
    have ha0 : 0 ≤ phase0AffineAReal n := phase0AffineAReal_nonneg n
    have hpow :
        (ENNReal.ofReal (phase0AffineAReal n)) ^ τ
          = ENNReal.ofReal ((phase0AffineAReal n) ^ τ) :=
      (ofReal_pow_eq ha0 τ).symm
    rw [hpow]
    rw [show (n : ℝ≥0∞) = ENNReal.ofReal (n : ℝ) from by
      rw [ENNReal.ofReal_natCast]]
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (n : ℝ))]
    rw [← ENNReal.ofReal_mul (by positivity :
      0 ≤ (phase0AffineAReal n) ^ τ)]
    apply ENNReal.ofReal_le_ofReal
    simpa [phase0AffineAReal] using
      Phase0Window.phase0_numerics_real n L τ hn hlog hτle

  calc
    (phase0AffineA n ^ τ *
        Phase0Window.clockCounterPotential (L := L) (K := K) 1 c₀
      + phase0AffineB L *
          ∑ i ∈ Finset.range τ, phase0AffineA n ^ i)
      / (1 : ℝ≥0∞)
        = phase0AffineB L *
            ∑ i ∈ Finset.range τ, phase0AffineA n ^ i := by
          rw [hΦ0, mul_zero, zero_add, div_one]
    _ ≤ phase0AffineB L * ((n : ℝ≥0∞) * phase0AffineA n ^ τ) := by
          gcongr
    _ = phase0AffineA n ^ τ * ((n : ℝ≥0∞) * phase0AffineB L) := by
          ring
    _ ≤ phase0ClockZeroBudget L := hnclock

/--
Closed value of `Phase0CardAffineScalar`.
-/
def phase0CardAffineScalar_value
    {n t : ℕ}
    (hn : 1 ≤ n)
    (ht : t ≤ n * (L + 1))
    (hlog : Real.log (n : ℝ) ≤ (L + 1 : ℕ)) :
    ClockDriftCardWindow.Phase0CardAffineScalar (L := L) (K := K) n t where
  hscalar := phase0_cardAffine_hscalar
    (L := L) (K := K) hn ht hlog

/--
Assembled Phase-0 clock-zero prefix tail from:

* the all-phase per-pair deterministic protocol bound;
* the closed scalar value above.
-/
theorem phase0ClockZeroPrefixTail_closed
    {n t : ℕ}
    (hn : 1 ≤ n)
    (ht : t ≤ n * (L + 1))
    (hlog : Real.log (n : ℝ) ≤ (L + 1 : ℕ))
    (A : ClockDriftCardWindow.AllPhaseClockPairBound (L := L) (K := K)) :
    Slot0HtailAssembly.Phase0ClockZeroPrefixTail (L := L) (K := K) n t :=
  ClockDriftCardWindow.phase0ClockZeroPrefixTail_of_cardWindow
    (L := L) (K := K)
    A
    (phase0CardAffineScalar_value (L := L) (K := K) hn ht hlog)

#print axioms geom_sum_phase0AffineAReal_le
#print axioms geom_sum_phase0AffineA_le
#print axioms phase0_cardAffine_hscalar
#print axioms phase0CardAffineScalar_value
#print axioms phase0ClockZeroPrefixTail_closed

end ClockWindowFields

end ExactMajority
