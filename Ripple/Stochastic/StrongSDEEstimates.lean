import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

/-!
# Deterministic estimates for the finite-channel Brownian Picard map

These statements concern normed spaces and deterministic integrals.
The Picard estimates consume explicitly named bounds. Their intended process space has
norm `(E sup_{s ≤ h} ‖X s‖²)^(1/2)`. Its construction, completeness, continuous adapted
representatives, and stochastic integration are separate obligations. No existence claim
is made here.
-/

noncomputable section

open Set MeasureTheory
open scoped Interval BigOperators

namespace Ripple.Stochastic.StrongSDE

section NormBounds

variable {E : Type*} [NormedAddCommGroup E]

/-- The two-term estimate does not require an inner product. -/
theorem norm_add_sq_le (a b : E) :
    ‖a + b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have h := norm_add_le a b
  have ha := norm_nonneg a
  have hb := norm_nonneg b
  have hab := norm_nonneg (a + b)
  have hs : ‖a + b‖ * ‖a + b‖ ≤ (‖a‖ + ‖b‖) * (‖a‖ + ‖b‖) :=
    mul_le_mul h h hab (add_nonneg ha hb)
  nlinarith [sq_nonneg (‖a‖ - ‖b‖)]

/-- The three-term bound used for the value of the Picard map. -/
theorem norm_add_add_sq_le (a b c : E) :
    ‖a + b + c‖ ^ 2 ≤ 3 * ‖a‖ ^ 2 + 3 * ‖b‖ ^ 2 + 3 * ‖c‖ ^ 2 := by
  have h : ‖a + b + c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ :=
    (norm_add_le (a + b) c).trans (add_le_add (norm_add_le a b) le_rfl)
  have hs := mul_le_mul h h (norm_nonneg (a + b + c))
    (add_nonneg (add_nonneg (norm_nonneg a) (norm_nonneg b)) (norm_nonneg c))
  nlinarith [sq_nonneg (‖a‖ - ‖b‖), sq_nonneg (‖a‖ - ‖c‖),
    sq_nonneg (‖b‖ - ‖c‖)]

end NormBounds

section Drift

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Uniform deterministic integral estimate. The norm bound is enough for this
inequality; continuity is needed separately when constructing the integral path. -/
theorem norm_intervalIntegral_le (b : ℝ → E) {t C : ℝ} (ht : 0 ≤ t)
    (hbound : ∀ s ∈ Icc 0 t, ‖b s‖ ≤ C) :
    ‖∫ s in (0 : ℝ)..t, b s‖ ≤ t * C := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := t) (C := C) (f := b) (fun s hs => by
      rw [uIoc_of_le ht] at hs
      exact hbound s ⟨hs.1.le, hs.2⟩)
  simpa [abs_of_nonneg ht, mul_comm] using h

/-- Continuity of the paths and drift produces interval integrability, which is
used to move subtraction inside the integral. The drift's global Lipschitz
estimate and the uniform path difference supply the bound on the integrand. -/
theorem drift_integral_difference_le (F : E → E) (x y : ℝ → E)
    (hF : Continuous F) (hx : Continuous x) (hy : Continuous y)
    {t L R : ℝ} (ht : 0 ≤ t) (hL : 0 ≤ L)
    (driftLipschitz : ∀ u v, ‖F u - F v‖ ≤ L * ‖u - v‖)
    (pathDifferenceBound : ∀ s ∈ Icc 0 t, ‖x s - y s‖ ≤ R) :
    ‖(∫ s in (0 : ℝ)..t, F (x s)) - (∫ s in (0 : ℝ)..t, F (y s))‖ ≤
      t * L * R := by
  rw [← intervalIntegral.integral_sub
    (show IntervalIntegrable (fun s => F (x s)) MeasureTheory.volume 0 t from
      (hF.comp hx).intervalIntegrable 0 t)
    (show IntervalIntegrable (fun s => F (y s)) MeasureTheory.volume 0 t from
      (hF.comp hy).intervalIntegrable 0 t)]
  have h := norm_intervalIntegral_le (fun s => F (x s) - F (y s)) ht
    (C := L * R) (fun s hs =>
      (driftLipschitz (x s) (y s)).trans
        (mul_le_mul_of_nonneg_left (pathDifferenceBound s hs) hL))
  simpa [mul_assoc] using h

end Drift

section Channels

variable {ι E V : Type*} [NormedAddCommGroup E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Finite-channel energy. The scalar coefficient estimates are produced by the
assumed global Lipschitz bounds for the square roots of the channel rates. -/
theorem finite_channel_difference_energy (channels : Finset ι) (ell : ι → V)
    (g : ι → E → ℝ) (L : ι → ℝ)
    (lipschitzConstant_nonneg : ∀ i ∈ channels, 0 ≤ L i)
    (channelLipschitz : ∀ i ∈ channels, ∀ x y,
      ‖g i x - g i y‖ ≤ L i * ‖x - y‖) (x y : E) :
    (∑ i ∈ channels, ‖(g i x - g i y) • ell i‖ ^ 2) ≤
      (∑ i ∈ channels, ‖ell i‖ ^ 2 * L i ^ 2) * ‖x - y‖ ^ 2 := by
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  have h := channelLipschitz i hi x y
  have hs : ‖g i x - g i y‖ ^ 2 ≤ (L i * ‖x - y‖) ^ 2 := by
    simpa only [pow_two] using
      (mul_le_mul h h (norm_nonneg _) (mul_nonneg
        (lipschitzConstant_nonneg i hi) (norm_nonneg _)))
  calc
    ‖(g i x - g i y) • ell i‖ ^ 2 =
        ‖g i x - g i y‖ ^ 2 * ‖ell i‖ ^ 2 := by rw [norm_smul]; ring
    _ ≤ (L i * ‖x - y‖) ^ 2 * ‖ell i‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hs (sq_nonneg _)
    _ = (‖ell i‖ ^ 2 * L i ^ 2) * ‖x - y‖ ^ 2 := by ring

/-- Bounded coefficients give the corresponding finite-channel value bound. -/
theorem finite_channel_energy (channels : Finset ι) (ell : ι → V)
    (g : ι → E → ℝ) (B : ι → ℝ)
    (bound_nonneg : ∀ i ∈ channels, 0 ≤ B i)
    (channelBound : ∀ i ∈ channels, ∀ x, ‖g i x‖ ≤ B i) (x : E) :
    (∑ i ∈ channels, ‖g i x • ell i‖ ^ 2) ≤
      ∑ i ∈ channels, ‖ell i‖ ^ 2 * B i ^ 2 := by
  apply Finset.sum_le_sum
  intro i hi
  have h := channelBound i hi x
  have hs : ‖g i x‖ ^ 2 ≤ B i ^ 2 := by
    simpa only [pow_two] using mul_le_mul h h (norm_nonneg _) (bound_nonneg i hi)
  calc
    ‖g i x • ell i‖ ^ 2 = ‖g i x‖ ^ 2 * ‖ell i‖ ^ 2 := by rw [norm_smul]; ring
    _ ≤ B i ^ 2 * ‖ell i‖ ^ 2 := mul_le_mul_of_nonneg_right hs (sq_nonneg _)
    _ = ‖ell i‖ ^ 2 * B i ^ 2 := by ring

/-- A scale in `[0,1]` cannot increase any squared channel norm. In the SDE
application this is applied with the scale `N^(-1/2)` after proving its bounds. -/
theorem scaled_norm_sq_le (v : V) {r : ℝ} (hr : 0 ≤ r) (hrOne : r ≤ 1) :
    ‖r • v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
  have hn : ‖r • v‖ ≤ ‖v‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr]
    simpa using mul_le_mul_of_nonneg_right hrOne (norm_nonneg v)
  simpa only [pow_two] using mul_le_mul hn hn (norm_nonneg _) (norm_nonneg _)

end Channels

/-- Every positive integer uses a diffusion scale between zero and one. -/
theorem inverse_sqrt_nat_bounds {N : ℕ} (hN : 1 ≤ N) :
    0 ≤ (Real.sqrt (N : ℝ))⁻¹ ∧ (Real.sqrt (N : ℝ))⁻¹ ≤ 1 := by
  have hn : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hs : 1 ≤ Real.sqrt (N : ℝ) := by
    nlinarith [Real.sq_sqrt (show 0 ≤ (N : ℝ) by positivity),
      Real.sqrt_nonneg (N : ℝ)]
  refine ⟨inv_nonneg.mpr (Real.sqrt_nonneg _), ?_⟩
  simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hs

section Picard

variable {S : Type*} [NormedAddCommGroup S]

/-- Algebraic Picard map; `S` is intended to be the complete space of continuous
adapted processes with the square-integrable path supremum norm. -/
def picardStep (initial : S) (drift noise : S → S) (x : S) : S :=
  initial + drift x + noise x

/-- Conditional difference estimate, uniform in the channel scale when the
noise hypothesis is uniform. Deterministic integration and the coefficient
Lipschitz bound produce `driftDifferenceBound`. Finite-channel Itô isometry,
Doob's L² maximal inequality, and the channel energy estimate must produce
`doobNoiseDifferenceBound`. This theorem does not construct those operators. -/
theorem picardStep_difference_sq_le (initial : S) (drift noise : S → S)
    (h LF LSsq : ℝ)
    (driftDifferenceBound : ∀ x y,
      ‖drift x - drift y‖ ^ 2 ≤ h ^ 2 * LF ^ 2 * ‖x - y‖ ^ 2)
    (doobNoiseDifferenceBound : ∀ x y,
      ‖noise x - noise y‖ ^ 2 ≤ 4 * h * LSsq * ‖x - y‖ ^ 2)
    (x y : S) :
    ‖picardStep initial drift noise x - picardStep initial drift noise y‖ ^ 2 ≤
      (2 * h ^ 2 * LF ^ 2 + 8 * h * LSsq) * ‖x - y‖ ^ 2 := by
  have heq : picardStep initial drift noise x - picardStep initial drift noise y =
      (drift x - drift y) + (noise x - noise y) := by
    simp only [picardStep]
    abel
  rw [heq]
  have hn := norm_add_sq_le (drift x - drift y) (noise x - noise y)
  have hd := driftDifferenceBound x y
  have hs := doobNoiseDifferenceBound x y
  nlinarith

/-- Conditional map bound. Bounded drift and deterministic integration produce
`driftValueBound`; bounded channel coefficients, Itô isometry, and Doob's L²
maximal inequality produce `doobNoiseValueBound`. -/
theorem picardStep_sq_le (initial : S) (drift noise : S → S)
    (h BF BSsq : ℝ)
    (driftValueBound : ∀ x, ‖drift x‖ ^ 2 ≤ h ^ 2 * BF ^ 2)
    (doobNoiseValueBound : ∀ x, ‖noise x‖ ^ 2 ≤ 4 * h * BSsq)
    (x : S) :
    ‖picardStep initial drift noise x‖ ^ 2 ≤
      3 * ‖initial‖ ^ 2 + 3 * h ^ 2 * BF ^ 2 + 12 * h * BSsq := by
  have hn := norm_add_add_sq_le initial (drift x) (noise x)
  have hd := driftValueBound x
  have hs := doobNoiseValueBound x
  dsimp [picardStep]
  nlinarith

end Picard

end Ripple.Stochastic.StrongSDE
