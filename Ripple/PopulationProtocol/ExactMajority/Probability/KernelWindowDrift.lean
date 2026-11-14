import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseConvergenceWeak
import Ripple.PopulationProtocol.ExactMajority.Probability.GatedGeometricDrift

/-!
# KernelWindowDrift — the Kernel-parametric WEAK window-drift builder (Doty et al. §6)

`WindowConcentration.windowDrift_PhaseConvergence` is `Protocol`-parametric and returns the
STRONG `PhaseConvergence P.transitionKernel`; it cannot be instantiated at an arbitrary
`Kernel (Option Config) (Option Config)` (the killed-minute kernel), nor does the killed
minute have a deterministic `Post`-absorption.  This file provides the Kernel-parametric WEAK
copy: same Markov-tail body, but `Protocol → Kernel` and `PhaseConvergence → PhaseConvergenceW`.

## Design note (documented deviation from the blueprint §3 skeleton)

The blueprint §3 sketch keeps an absorbing-window hypothesis `hQ_abs` and derives the
multi-step decay via an a.e.-invariance of `Q` along the trajectory (the
`Protocol.ae_of_stepDistOrSelf_support_preserved` analogue).  For a general `Kernel`, "the
support of a measure" is not a first-class notion in Mathlib (`Measure.support` does not
exist), so porting that a.e. step verbatim is awkward.

We instead require the strictly cleaner **UNCONDITIONAL one-step drift**
`∀ x, ∫⁻ Φ ∂(K x) ≤ r · Φ x` — which is EXACTLY what the killed-minute kernel satisfies (its
drift is unconditional: at the cemetery and off-gate the integral is `0`, on-gate it is the
real drift).  This removes `Q`/`hQ_abs` entirely and reuses the already-proven
`GatedDrift.lintegral_stepIndexed_decay` (constant potential family) for the decay.  Consumers
discharge the unconditional drift as their `killed_*_drift` lemma.
-/

namespace Ripple.PopulationProtocol.ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace KernelWindowDrift

variable {Ω : Type*} [MeasurableSpace Ω] [DiscreteMeasurableSpace Ω]

/-- **Unconditional multi-step decay.**  If a measurable potential `Φ` contracts at rate `r`
at EVERY state (`∫⁻ Φ ∂(K x) ≤ r · Φ x` for all `x`), then the `t`-step expectation contracts
geometrically: `∫⁻ Φ d(Kᵗ x₀) ≤ rᵗ · Φ x₀`.  Port of `WindowConcentration.lintegral_decay_on_absorbing`
to a `Kernel`, with the absorbing window replaced by the unconditional hypothesis. -/
theorem kernel_lintegral_decay {K : Kernel Ω Ω} [IsMarkovKernel K]
    (Φ : Ω → ℝ≥0∞) (hΦ : Measurable Φ) (r : ℝ≥0∞)
    (hdrift : ∀ x, ∫⁻ y, Φ y ∂(K x) ≤ r * Φ x)
    (t : ℕ) (x₀ : Ω) :
    ∫⁻ y, Φ y ∂((K ^ t) x₀) ≤ r ^ t * Φ x₀ := by
  induction t generalizing x₀ with
  | zero =>
    simp only [pow_zero, one_mul]
    change ∫⁻ y, Φ y ∂(Kernel.id x₀) ≤ Φ x₀
    rw [Kernel.id_apply, lintegral_dirac' x₀ hΦ]
  | succ t ih =>
    change ∫⁻ y, Φ y ∂(((K ^ t) ∘ₖ K) x₀) ≤ r ^ (t + 1) * Φ x₀
    rw [Kernel.lintegral_comp _ _ x₀ hΦ]
    calc ∫⁻ b, ∫⁻ y, Φ y ∂((K ^ t) b) ∂(K x₀)
        ≤ ∫⁻ b, r ^ t * Φ b ∂(K x₀) := lintegral_mono (fun b => ih b)
      _ = r ^ t * ∫⁻ b, Φ b ∂(K x₀) := lintegral_const_mul _ hΦ
      _ ≤ r ^ t * (r * Φ x₀) := by gcongr; exact hdrift x₀
      _ = r ^ (t + 1) * Φ x₀ := by rw [pow_succ, mul_assoc]

/-- **Kernel Markov tail at threshold `θ`.**  Under the unconditional drift, the probability
that `θ ≤ Φ` after `t` steps is at most `rᵗ · Φ x₀ / θ`.  Port of
`WindowConcentration.measure_ge_thresh_on_absorbing`. -/
theorem kernel_measure_ge_thresh {K : Kernel Ω Ω} [IsMarkovKernel K]
    (Φ : Ω → ℝ≥0∞) (hΦ : Measurable Φ) (r : ℝ≥0∞)
    (hdrift : ∀ x, ∫⁻ y, Φ y ∂(K x) ≤ r * Φ x)
    (t : ℕ) (x₀ : Ω) (θ : ℝ≥0∞) (hθ : θ ≠ 0) (hθ_top : θ ≠ ⊤) :
    (K ^ t) x₀ {y | θ ≤ Φ y} ≤ r ^ t * Φ x₀ / θ := by
  have hmarkov := mul_meas_ge_le_lintegral₀ (μ := (K ^ t) x₀) hΦ.aemeasurable θ
  have hdecay := kernel_lintegral_decay Φ hΦ r hdrift t x₀
  have hchain : θ * (K ^ t) x₀ {y | θ ≤ Φ y} ≤ r ^ t * Φ x₀ := le_trans hmarkov hdecay
  rw [ENNReal.le_div_iff_mul_le (Or.inl hθ) (Or.inl hθ_top), mul_comm]
  exact hchain

/-- **Kernel weak window-drift tail.**  The "unfinished" region `{¬Post}` lies in `{θ ≤ Φ}`
(failing `Post` forces `Φ ≥ θ`), so the threshold Markov tail bounds the failure probability.
Port of `WindowConcentration.windowDrift_tail`. -/
theorem kernel_windowDrift_tail {K : Kernel Ω Ω} [IsMarkovKernel K]
    (Φ : Ω → ℝ≥0∞) (hΦ : Measurable Φ) (r : ℝ≥0∞)
    (hdrift : ∀ x, ∫⁻ y, Φ y ∂(K x) ≤ r * Φ x)
    (Post : Ω → Prop)
    (θ : ℝ≥0∞) (hθ : θ ≠ 0) (hθ_top : θ ≠ ⊤)
    (hlink : ∀ x, ¬ Post x → θ ≤ Φ x)
    (t : ℕ) (x₀ : Ω) :
    (K ^ t) x₀ {y | ¬ Post y} ≤ r ^ t * Φ x₀ / θ := by
  have hsubset : {y : Ω | ¬ Post y} ⊆ {y | θ ≤ Φ y} := fun y hy => hlink y hy
  calc (K ^ t) x₀ {y | ¬ Post y}
      ≤ (K ^ t) x₀ {y | θ ≤ Φ y} := measure_mono hsubset
    _ ≤ r ^ t * Φ x₀ / θ := kernel_measure_ge_thresh Φ hΦ r hdrift t x₀ θ hθ hθ_top

/-- **The keystone — the Kernel-parametric WEAK concentration builder.**  Turns an
unconditional one-step drift contraction into a `PhaseConvergenceW K`.  Port of
`WindowConcentration.windowDrift_PhaseConvergence`, dropping the deterministic
`post_absorbing` field (the weak structure has none) and the absorbing window.

* `hdrift` — UNCONDITIONAL per-step contraction `∫ Φ dK(x) ≤ r · Φ x` at every `x`;
* `hlink` — failing `Post` forces `Φ ≥ θ`;
* `hPre_bound` — `Pre` bounds the initial potential by `Φ₀`;
* `hε` — the geometric tail fits under `ε`: `rᵗ · Φ₀ / θ ≤ ε`. -/
noncomputable def kernelWindowDrift_PhaseConvergenceW {K : Kernel Ω Ω} [IsMarkovKernel K]
    (Φ : Ω → ℝ≥0∞) (hΦ : Measurable Φ) (r : ℝ≥0∞)
    (hdrift : ∀ x, ∫⁻ y, Φ y ∂(K x) ≤ r * Φ x)
    (Pre Post : Ω → Prop)
    (θ : ℝ≥0∞) (hθ : θ ≠ 0) (hθ_top : θ ≠ ⊤)
    (hlink : ∀ x, ¬ Post x → θ ≤ Φ x)
    (Φ₀ : ℝ≥0∞) (hPre_bound : ∀ x, Pre x → Φ x ≤ Φ₀)
    (t : ℕ) (ε : ℝ≥0)
    (hε : r ^ t * Φ₀ / θ ≤ (ε : ℝ≥0∞)) :
    PhaseConvergenceW K where
  Pre := Pre
  Post := Post
  t := t
  ε := ε
  convergence := by
    intro x₀ hPre₀
    calc (K ^ t) x₀ {y | ¬ Post y}
        ≤ r ^ t * Φ x₀ / θ :=
          kernel_windowDrift_tail Φ hΦ r hdrift Post θ hθ hθ_top hlink t x₀
      _ ≤ r ^ t * Φ₀ / θ := by
          gcongr
          exact hPre_bound x₀ hPre₀
      _ ≤ (ε : ℝ≥0∞) := hε

end KernelWindowDrift

end Ripple.PopulationProtocol.ExactMajority
