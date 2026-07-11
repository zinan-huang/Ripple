/-
Kernel-power Azuma-Hoeffding tail for a bounded-difference supermartingale.

This is the genuine unblock for Lemma 6.10 of Doty et al. The naive `exp(s·Φ)`
is NOT a supermartingale (Jensen the wrong way). The correct object is the
**Azuma exponential supermartingale** `Ψ_t = exp(s·Φ − (s²c²/2)·t)`, whose
multiplicative drift `r = 1` lets us reuse the geometric-drift kernel tail.

Everything is PURE PROBABILITY infra: any measurable space `α`, any Markov
kernel `K : Kernel α α`, any real potential `Φ : α → ℝ`. No protocol dependency.

## Structure

* `stepMGF_bound` — the per-step conditional MGF bound, genuinely derived from
  Mathlib's Hoeffding's lemma (`hasSubgaussianMGF_of_mem_Icc`):
  if `Φ y − Φ x ∈ [−c, c]` a.e. `∂(K x)` and the conditional mean drifts down
  (`∫ Φ y ∂(K x) ≤ Φ x`), then for `0 ≤ s`,
  `∫ exp(s·(Φ y − Φ x)) ∂(K x) ≤ exp(c²·s²/2)`.

* `expSupermartingale_drift` — repackages `stepMGF_bound` as a multiplicative
  `r = exp(c²s²/2)` drift for `Ψ = ofReal ∘ exp(s·Φ)`, i.e. the exact hypothesis
  shape of `geometric_drift_tail_kernel`.

* `azuma_exp_tail` — the exponential-form kernel tail
  `(K^t) x {y | θ ≤ exp(s·Φ y)} ≤ exp(s·Φ x + (s²c²/2)·t) / θ`.

* `azuma_tail` — the additive upper Azuma tail, after optimizing `s = λ/(t c²)`:
  `(K^t) x {y | Φ x + λ ≤ Φ y} ≤ exp(−λ²/(2·t·c²))`.

Reference: Doty et al., Lemma 6.10; Azuma–Hoeffding inequality.
Mathlib: `ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc` (Hoeffding's lemma).
-/

import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Kernel.Defs
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Supermartingale

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real

namespace ExactMajority

variable {α : Type*} [MeasurableSpace α]

/-! ## Per-step conditional MGF bound from Hoeffding's lemma -/

/-- **Per-step conditional MGF bound** (genuinely derived from Hoeffding's
lemma, NOT assumed).

Let `K : Kernel α α` be a Markov kernel, `Φ : α → ℝ` a measurable potential,
`c ≥ 0`, and fix a state `x`. Suppose:
* (bounded difference) `Φ y − Φ x ∈ [−c, c]` for a.e. `y ∂(K x)`;
* (downward drift) `∫ y, Φ y ∂(K x) ≤ Φ x`.
Then for every `s ≥ 0`,
`∫ y, exp(s·(Φ y − Φ x)) ∂(K x) ≤ exp(c² · s² / 2)`.

This is the conditional analogue of the independent-sum sub-Gaussian estimate.
The `(b−a)² / 4 = (2c)² / 4 = c²` proxy is exactly Hoeffding's variance proxy
for a `[−c, c]`-bounded variable, and the downward drift kills the
mean-shift factor `exp(s·(E[Φ] − Φ x)) ≤ 1`. -/
theorem stepMGF_bound
    (K : Kernel α α) [IsMarkovKernel K]
    (Φ : α → ℝ) (hΦ : Measurable Φ)
    (c : ℝ) (hc : 0 ≤ c) (x : α)
    (hdiff : ∀ᵐ y ∂(K x), |Φ y - Φ x| ≤ c)
    (hdrift : ∫ y, Φ y ∂(K x) ≤ Φ x)
    {s : ℝ} (hs : 0 ≤ s) :
    ∫ y, Real.exp (s * (Φ y - Φ x)) ∂(K x) ≤ Real.exp (c ^ 2 * s ^ 2 / 2) := by
  haveI : IsProbabilityMeasure (K x) := IsMarkovKernel.isProbabilityMeasure x
  -- The random variable on `(K x)`.
  set Y : α → ℝ := fun y => Φ y
  have hY : AEMeasurable Y (K x) := hΦ.aemeasurable
  -- Bounded difference rephrased as membership in `Icc (Φ x - c) (Φ x + c)`.
  have hb : ∀ᵐ y ∂(K x), Y y ∈ Set.Icc (Φ x - c) (Φ x + c) := by
    filter_upwards [hdiff] with y hy
    rw [abs_le] at hy
    exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
  -- Hoeffding's lemma: `Y - E[Y]` is sub-Gaussian with proxy `((b-a)/2)² = c²`.
  have hsubG :
      HasSubgaussianMGF (fun y => Y y - (K x)[Y])
        ((‖(Φ x + c) - (Φ x - c)‖₊ / 2) ^ 2) (K x) :=
    hasSubgaussianMGF_of_mem_Icc hY hb
  -- The proxy, cast to ℝ, equals `c²`.
  have hproxy : (((‖(Φ x + c) - (Φ x - c)‖₊ / 2) ^ 2 : ℝ≥0) : ℝ) = c ^ 2 := by
    have hcoe : ‖(Φ x + c) - (Φ x - c)‖ = 2 * c := by
      rw [Real.norm_eq_abs, show (Φ x + c) - (Φ x - c) = 2 * c by ring]
      exact abs_of_nonneg (by linarith)
    push_cast
    rw [hcoe]
    ring
  -- The MGF bound at parameter `s`.
  have hmgf : mgf (fun y => Y y - (K x)[Y]) (K x) s
      ≤ Real.exp (c ^ 2 * s ^ 2 / 2) := by
    have h := hsubG.mgf_le s
    rw [hproxy] at h
    exact h
  -- Unfold the centered MGF as an integral.
  have hmgf_int :
      mgf (fun y => Y y - (K x)[Y]) (K x) s
        = ∫ y, Real.exp (s * (Y y - (K x)[Y])) ∂(K x) := by
    rfl
  -- Mean shift: `exp(s·(E[Y] − Φ x)) ≤ 1` from drift + `s ≥ 0`.
  have hmean : (K x)[Y] ≤ Φ x := hdrift
  have hshift : Real.exp (s * ((K x)[Y] - Φ x)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : (K x)[Y] - Φ x ≤ 0 := by linarith
    exact mul_nonpos_of_nonneg_of_nonpos hs this
  -- Relate `exp(s·(Φ y − Φ x))` to the centered exponential.
  have hsplit : ∀ y, Real.exp (s * (Φ y - Φ x))
      = Real.exp (s * ((K x)[Y] - Φ x)) * Real.exp (s * (Y y - (K x)[Y])) := by
    intro y
    rw [← Real.exp_add]
    congr 1
    simp only [Y]
    ring
  -- Integrability of the centered exponential.
  have hint : Integrable (fun y => Real.exp (s * (Y y - (K x)[Y]))) (K x) := by
    have := hsubG.integrable_exp_mul s
    simpa using this
  calc
    ∫ y, Real.exp (s * (Φ y - Φ x)) ∂(K x)
        = ∫ y, Real.exp (s * ((K x)[Y] - Φ x))
            * Real.exp (s * (Y y - (K x)[Y])) ∂(K x) := by
          simp_rw [hsplit]
    _ = Real.exp (s * ((K x)[Y] - Φ x))
            * ∫ y, Real.exp (s * (Y y - (K x)[Y])) ∂(K x) := by
          rw [integral_const_mul]
    _ ≤ 1 * ∫ y, Real.exp (s * (Y y - (K x)[Y])) ∂(K x) := by
          apply mul_le_mul_of_nonneg_right hshift
          apply integral_nonneg
          intro y
          positivity
    _ = mgf (fun y => Y y - (K x)[Y]) (K x) s := by
          rw [one_mul, hmgf_int]
    _ ≤ Real.exp (c ^ 2 * s ^ 2 / 2) := hmgf

/-! ## The exponential supermartingale drift -/

/-- The exp-potential `Ψ y = ofReal (exp (s·Φ y))` satisfies the multiplicative
drift `∫⁻ Ψ ∂(K x) ≤ exp(c²s²/2) · Ψ x`. This is the `geometric_drift_tail_kernel`
hypothesis (with `r = ofReal (exp(c²s²/2))`, NOT `r = 1`; absorbing the `r^t`
factor reconstitutes the Azuma exponential supermartingale `Ψ_t`). -/
theorem expSupermartingale_drift
    (K : Kernel α α) [IsMarkovKernel K]
    (Φ : α → ℝ) (hΦ : Measurable Φ)
    (c : ℝ) (hc : 0 ≤ c)
    (hdiff : ∀ x, ∀ᵐ y ∂(K x), |Φ y - Φ x| ≤ c)
    (hdrift : ∀ x, ∫ y, Φ y ∂(K x) ≤ Φ x)
    {s : ℝ} (hs : 0 ≤ s) :
    ∀ x, ∫⁻ y, ENNReal.ofReal (Real.exp (s * Φ y)) ∂(K x)
        ≤ ENNReal.ofReal (Real.exp (c ^ 2 * s ^ 2 / 2))
          * ENNReal.ofReal (Real.exp (s * Φ x)) := by
  intro x
  haveI : IsProbabilityMeasure (K x) := IsMarkovKernel.isProbabilityMeasure x
  -- Integrability of `y ↦ exp(s·Φ y)` on `K x` (centered exponential is integrable).
  have hstep := stepMGF_bound K Φ hΦ c hc x (hdiff x) (hdrift x) hs
  -- `exp(s·Φ y) = exp(s·Φ x) · exp(s·(Φ y − Φ x))`.
  have hsplit : ∀ y, Real.exp (s * Φ y)
      = Real.exp (s * Φ x) * Real.exp (s * (Φ y - Φ x)) := by
    intro y
    rw [← Real.exp_add]; congr 1; ring
  -- Integrability of the difference-exponential.
  have hint_diff : Integrable (fun y => Real.exp (s * (Φ y - Φ x))) (K x) := by
    have hsg := hasSubgaussianMGF_of_mem_Icc (μ := K x) (X := fun y => Φ y)
      (a := Φ x - c) (b := Φ x + c) hΦ.aemeasurable
      (by
        filter_upwards [hdiff x] with y hy
        rw [abs_le] at hy
        exact ⟨by linarith [hy.1], by linarith [hy.2]⟩)
    -- `exp(s·(Φ y − Φ x))` differs from `exp(s·(Φ y − m))` by a constant factor.
    have h1 : Integrable (fun y => Real.exp (s * ((fun y => Φ y) y - (K x)[fun z => Φ z]))) (K x) :=
      hsg.integrable_exp_mul s
    have hconst : ∀ y, Real.exp (s * (Φ y - Φ x))
        = Real.exp (s * ((K x)[fun z => Φ z] - Φ x))
          * Real.exp (s * (Φ y - (K x)[fun z => Φ z])) := by
      intro y; rw [← Real.exp_add]; congr 1; ring
    simp_rw [hconst]
    exact h1.const_mul _
  have hint : Integrable (fun y => Real.exp (s * Φ y)) (K x) := by
    have : (fun y => Real.exp (s * Φ y))
        = (fun y => Real.exp (s * Φ x) * Real.exp (s * (Φ y - Φ x))) := by
      funext y; exact hsplit y
    rw [this]
    exact hint_diff.const_mul _
  calc
    ∫⁻ y, ENNReal.ofReal (Real.exp (s * Φ y)) ∂(K x)
        = ENNReal.ofReal (∫ y, Real.exp (s * Φ y) ∂(K x)) := by
          rw [ofReal_integral_eq_lintegral_ofReal hint
            (Filter.Eventually.of_forall (fun y => (Real.exp_pos _).le))]
    _ = ENNReal.ofReal (∫ y, Real.exp (s * Φ x)
          * Real.exp (s * (Φ y - Φ x)) ∂(K x)) := by
          congr 1; apply integral_congr_ae
          exact Filter.Eventually.of_forall (fun y => hsplit y)
    _ = ENNReal.ofReal (Real.exp (s * Φ x)
          * ∫ y, Real.exp (s * (Φ y - Φ x)) ∂(K x)) := by
          rw [integral_const_mul]
    _ ≤ ENNReal.ofReal (Real.exp (s * Φ x)
          * Real.exp (c ^ 2 * s ^ 2 / 2)) := by
          apply ENNReal.ofReal_le_ofReal
          apply mul_le_mul_of_nonneg_left hstep (Real.exp_pos _).le
    _ = ENNReal.ofReal (Real.exp (c ^ 2 * s ^ 2 / 2))
          * ENNReal.ofReal (Real.exp (s * Φ x)) := by
          rw [mul_comm (Real.exp (s * Φ x)),
            ENNReal.ofReal_mul (Real.exp_pos _).le]

/-! ## Exponential-form Azuma tail -/

/-- **Azuma exponential-form kernel tail.**

Under downward drift and bounded per-step difference `c ≥ 0`, for every `s ≥ 0`
and finite non-zero threshold `θ`,
`(K^t) x {y | θ ≤ exp(s·Φ y)} ≤ exp(s·Φ x + (s²c²/2)·t) / θ`.

This is `geometric_drift_tail` applied to the Azuma exponential supermartingale
`Ψ = ofReal ∘ exp(s·Φ)` with multiplicative rate `r = exp(c²s²/2)`. -/
theorem azuma_exp_tail
    (K : Kernel α α) [IsMarkovKernel K]
    (Φ : α → ℝ) (hΦ : Measurable Φ)
    (c : ℝ) (hc : 0 ≤ c)
    (hdiff : ∀ x, ∀ᵐ y ∂(K x), |Φ y - Φ x| ≤ c)
    (hdrift : ∀ x, ∫ y, Φ y ∂(K x) ≤ Φ x)
    {s : ℝ} (hs : 0 ≤ s)
    (t : ℕ) (x : α) {θ : ℝ} (hθ : 0 < θ) :
    (K ^ t) x {y | θ ≤ Real.exp (s * Φ y)}
      ≤ ENNReal.ofReal (Real.exp (s * Φ x + s ^ 2 * c ^ 2 / 2 * t)) / ENNReal.ofReal θ := by
  set Ψ : α → ℝ≥0∞ := fun y => ENNReal.ofReal (Real.exp (s * Φ y)) with hΨ
  have hΨ_meas : Measurable Ψ :=
    (Real.measurable_exp.comp ((measurable_const).mul hΦ)).ennreal_ofReal
  set r : ℝ≥0∞ := ENNReal.ofReal (Real.exp (c ^ 2 * s ^ 2 / 2)) with hr
  have hdrift_Ψ : ∀ y, ∫⁻ z, Ψ z ∂(K y) ≤ r * Ψ y :=
    expSupermartingale_drift K Φ hΦ c hc hdiff hdrift hs
  -- The threshold sets coincide: `{θ ≤ exp(s Φ y)} = {ofReal θ ≤ Ψ y}`.
  have hset : {y | θ ≤ Real.exp (s * Φ y)} = {y | ENNReal.ofReal θ ≤ Ψ y} := by
    ext y
    simp only [Set.mem_setOf_eq, hΨ]
    rw [ENNReal.ofReal_le_ofReal_iff (Real.exp_pos _).le]
  rw [hset]
  have hθ0 : ENNReal.ofReal θ ≠ 0 := by
    simp [ENNReal.ofReal_eq_zero, not_le, hθ]
  have hθtop : ENNReal.ofReal θ ≠ ∞ := ENNReal.ofReal_ne_top
  have htail := geometric_drift_tail K Ψ hΨ_meas r hdrift_Ψ t x (ENNReal.ofReal θ) hθ0 hθtop
  -- Rewrite `r^t * Ψ x` into the claimed exponential numerator.
  have hrt : r ^ t * Ψ x
      = ENNReal.ofReal (Real.exp (s * Φ x + s ^ 2 * c ^ 2 / 2 * t)) := by
    rw [hr, hΨ, ← ENNReal.ofReal_pow (Real.exp_pos _).le,
      ← ENNReal.ofReal_mul (by positivity), ← Real.exp_nat_mul, ← Real.exp_add]
    congr 2
    ring
  rw [hrt] at htail
  exact htail

/-! ## Additive Azuma-Hoeffding tail -/

/-- **Additive Azuma-Hoeffding kernel tail.**

Let `K : Kernel α α` be a Markov kernel and `Φ : α → ℝ` a measurable potential
satisfying the supermartingale drift `∫ Φ ∂(K x) ≤ Φ x` and the bounded per-step
difference `|Φ y − Φ x| ≤ c` (a.e. `∂(K x)`) with `c > 0`. Then for every
deviation `λ > 0` and step count `t ≥ 1`,
`(K^t) x {y | Φ x + λ ≤ Φ y} ≤ exp(−λ² / (2 t c²))`.

Obtained from `azuma_exp_tail` at the optimal `s = λ / (t c²)`. -/
theorem azuma_tail
    (K : Kernel α α) [IsMarkovKernel K]
    (Φ : α → ℝ) (hΦ : Measurable Φ)
    (c : ℝ) (hc : 0 < c)
    (hdiff : ∀ x, ∀ᵐ y ∂(K x), |Φ y - Φ x| ≤ c)
    (hdrift : ∀ x, ∫ y, Φ y ∂(K x) ≤ Φ x)
    (t : ℕ) (ht : 1 ≤ t) (x : α) {lam : ℝ} (hlam : 0 < lam) :
    (K ^ t) x {y | Φ x + lam ≤ Φ y}
      ≤ ENNReal.ofReal (Real.exp (-(lam ^ 2) / (2 * t * c ^ 2))) := by
  -- Optimal sub-Gaussian parameter.
  set s : ℝ := lam / (t * c ^ 2) with hsdef
  have htpos : (0 : ℝ) < t := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one ht
  have hc2 : (0 : ℝ) < c ^ 2 := by positivity
  have htc2 : (0 : ℝ) < t * c ^ 2 := by positivity
  have hs : 0 ≤ s := by rw [hsdef]; positivity
  -- Threshold making the exp-event coincide with the additive event.
  set θ : ℝ := Real.exp (s * (Φ x + lam)) with hθdef
  have hθpos : 0 < θ := Real.exp_pos _
  -- Apply the exponential tail.
  have hexp := azuma_exp_tail K Φ hΦ c hc.le hdiff hdrift hs t x hθpos
  -- The event `{θ ≤ exp(s Φ y)}` equals `{Φ x + λ ≤ Φ y}` since `s ≥ 0`.
  have hset : {y | θ ≤ Real.exp (s * Φ y)} = {y | Φ x + lam ≤ Φ y} := by
    ext y
    simp only [Set.mem_setOf_eq, hθdef]
    rw [Real.exp_le_exp]
    constructor
    · intro h
      -- s could be 0 only if lam = 0; here lam > 0 ⟹ s > 0.
      have hspos : 0 < s := by rw [hsdef]; positivity
      exact le_of_mul_le_mul_left h hspos
    · intro h
      have hspos : 0 < s := by rw [hsdef]; positivity
      exact mul_le_mul_of_nonneg_left h hspos.le
  rw [hset] at hexp
  -- Bound the RHS `ofReal(exp(...))/ofReal(θ)` by `ofReal(exp(−λ²/(2 t c²)))`.
  refine hexp.trans ?_
  rw [ENNReal.div_le_iff_le_mul (Or.inl (by simp [ENNReal.ofReal_eq_zero, not_le, hθpos]))
    (Or.inl ENNReal.ofReal_ne_top), hθdef,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  apply ENNReal.ofReal_le_ofReal
  rw [Real.exp_le_exp]
  -- The exponent inequality, with `s = lam/(t c²)`, is an equality.
  rw [hsdef]
  field_simp
  ring_nf
  -- Goal is now a polynomial inequality (equality) in lam, t, c.
  nlinarith [sq_nonneg lam, htc2, hc2, htpos, mul_pos htpos hc2]

end ExactMajority
