/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `ReachableClockTail` — the REACHABILITY-CONDITIONED clock depletion tail.

The single-term tool `ClockDepletionCoupling.mgf_depletion_tail_uniform` produces the clock
per-`τ` depletion mass `(K^H) c₀ {count sc ≤ N − R}` but only by consuming the UNIVERSAL caps

  `hcard : ∀ c, 2 ≤ c.card → c.card = n`   and   `hcap : ∀ c, c.count sc ≤ m`,

both of which are FALSE over all configs (`FaithfulDischargeTierA.hcard_not_universal` /
`hcap_not_universal`, refutation-checked).  The HONEST caps hold only on the reachable-from-`c₀`
domain (`card_eq_on_reachable`, `clockCount_eq_on_reachable_qmix`).

This file generalizes the depletion tail to the REACHABLE domain.  The chain started at `c₀`
stays reachable (`Protocol.ae_reachable_transitionKernel_pow` / one-step support reachability),
so the MGF supermartingale only needs the per-step decrement rate `q = 2m/n` ON the configs the
chain visits — i.e. reachable configs, where `card = n` and `count sc ≤ m` HOLD.  We therefore
build a reachability-conditioned multiplicative-decay engine and feed it the reachable caps.

## What is PROVEN here

* `lintegral_geometric_decay_reachable` — the generic multiplicative-decay engine
  (`PopProtoCommon.lintegral_geometric_decay`) with the drift restricted to the reachable-from-`c₀`
  domain.  Proof: the same induction, but `lintegral_mono` is replaced by `lintegral_mono_ae`,
  feeding on the one-step ae-reachability of the support of `K x` (composed with `Reachable c₀ x`),
  and the drift is consumed only at the reachable `x`.
* `geometric_drift_tail_reachable` — Markov's inequality on top of the reachable decay.
* `expPot_drift_reachable` — the clock MGF drift `∫⁻ Φ_s dK(c) ≤ Q·Φ_s(c)` consumed only on
  reachable `c`, from the per-step decrement bound restricted to reachable configs.
* `mgf_depletion_tail_reachable` — the headline: same conclusion as `mgf_depletion_tail_uniform`
  but with `hcard`/`hcap` replaced by the REACHABLE forms
  `hcard_reach : ∀ c, Reachable c₀ c → card c = n` and `hcap_reach : ∀ c, Reachable c₀ c → count sc ≤ m`
  (plus the universal `hsmall`, a TRUE universal).
* `clock_perτ_tail_reachable` — instantiates the reachable caps along the forward trajectory:
  for every `τ`, the term `(K^τ) c₀ {count sc ≤ N − R}` is bounded by the reachable MGF tail.

## ANTI-TRAP compliance

NO `InvClosed` of a phase window.  The reachable cap is TRUE (`card_eq_on_reachable` proven); the
universal cap is FALSE (NOT used — only the reachable-restricted `hcard_reach`/`hcap_reach`).  The
drift is consumed on the reachable trajectory, not all configs.  The `Q^H / e^{sR}` decay is from
`e^{sR}` (`Q ≥ 1`, no contraction) — the Chernoff window.  Refutation guard: the reachable caps are
exactly the honest domain restriction; carrying them as bare universals would be the refuted false
universal.  Non-vacuity: for `s > 0`, `R ≥ 1`, `H·q·(e^{2s}−1) < s·R` the tail `< 1`.

## Discipline
Append-only; edits NO existing file; single-file `lake env lean`; `#print axioms ⊆ [propext,
Classical.choice, Quot.sound]`; no `sorry`/`admit`/`axiom`/`native_decide`.
-/
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockDepletionCoupling
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.FaithfulDischargeTierA

namespace ExactMajority
namespace ReachableClockTail

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Real
open Protocol ClockDepletionCoupling

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-! ## Part 1 — the REACHABILITY-CONDITIONED multiplicative-decay engine.

`PopProtoCommon.lintegral_geometric_decay` needs `hdrift : ∀ x` UNIVERSALLY.  We weaken it to the
reachable-from-`c₀` domain.  The chain started at any reachable `x` stays reachable (one-step
support reachability, transitively composed), so the inductive step only ever consumes the drift
on reachable configs — the `lintegral_mono` becomes a `lintegral_mono_ae` over the ae-reachable
support of `K x`. -/

/-- **Reachable-conditioned geometric decay.**  If the multiplicative drift
`∫⁻ Φ dK(x) ≤ r·Φ(x)` holds for every config reachable from `c₀`, then for every `x` reachable
from `c₀` (in particular `x = c₀`), the `t`-step integral satisfies `∫⁻ Φ d(K^t)(x) ≤ r^t·Φ(x)`.
The drift is consumed ONLY on reachable configs (the honest domain), via the ae-reachability of the
chain (`stepDistOrSelf_support_reachable` composed with `Reachable c₀ x`). -/
theorem lintegral_geometric_decay_reachable (P : Protocol Λ)
    (Φ : Config Λ → ℝ≥0∞) (hΦ : Measurable Φ) (r : ℝ≥0∞) (c₀ : Config Λ)
    (hdrift : ∀ x : Config Λ, P.Reachable c₀ x →
      ∫⁻ y, Φ y ∂(P.transitionKernel x) ≤ r * Φ x)
    (t : ℕ) (x : Config Λ) (hx : P.Reachable c₀ x) :
    ∫⁻ y, Φ y ∂((P.transitionKernel ^ t) x) ≤ r ^ t * Φ x := by
  classical
  induction t generalizing x with
  | zero =>
    simp only [pow_zero, one_mul]
    change ∫⁻ y, Φ y ∂(Kernel.id x) ≤ Φ x
    rw [Kernel.id_apply, lintegral_dirac' x hΦ]
  | succ t ih =>
    change ∫⁻ y, Φ y ∂(((P.transitionKernel ^ t) ∘ₖ P.transitionKernel) x)
      ≤ r ^ (t + 1) * Φ x
    rw [Kernel.lintegral_comp _ P.transitionKernel x hΦ]
    -- The inner integrand `∫⁻ Φ d(K^t b)` is bounded by `r^t·Φ b` for ae `b` (reachable from c₀).
    have hae : ∀ᵐ b ∂(P.transitionKernel x),
        ∫⁻ y, Φ y ∂((P.transitionKernel ^ t) b) ≤ r ^ t * Φ b := by
      have hreach : ∀ᵐ b ∂(P.transitionKernel x), P.Reachable c₀ b := by
        have : (P.transitionKernel x) = (P.stepDistOrSelf x).toMeasure := rfl
        rw [this]
        apply ClockDepletionCoupling.ae_of_pmf_support
        intro b hb
        exact Relation.ReflTransGen.trans hx (stepDistOrSelf_support_reachable P x b hb)
      filter_upwards [hreach] with b hb
      exact ih b hb
    calc ∫⁻ b, ∫⁻ y, Φ y ∂((P.transitionKernel ^ t) b) ∂(P.transitionKernel x)
        ≤ ∫⁻ b, r ^ t * Φ b ∂(P.transitionKernel x) := lintegral_mono_ae hae
      _ = r ^ t * ∫⁻ b, Φ b ∂(P.transitionKernel x) := lintegral_const_mul _ hΦ
      _ ≤ r ^ t * (r * Φ x) := by gcongr; exact hdrift x hx
      _ = r ^ (t + 1) * Φ x := by rw [pow_succ, mul_assoc]

/-- **Reachable-conditioned geometric-drift tail (division form).**  Markov's inequality on top of
the reachable decay: under the reachable-domain drift, the super-level set `{θ ≤ Φ}` after `t`
steps from a reachable `x` is bounded by `r^t·Φ(x)/θ`. -/
theorem geometric_drift_tail_reachable (P : Protocol Λ)
    (Φ : Config Λ → ℝ≥0∞) (hΦ : Measurable Φ) (r : ℝ≥0∞) (c₀ : Config Λ)
    (hdrift : ∀ x : Config Λ, P.Reachable c₀ x →
      ∫⁻ y, Φ y ∂(P.transitionKernel x) ≤ r * Φ x)
    (t : ℕ) (x : Config Λ) (hx : P.Reachable c₀ x)
    (θ : ℝ≥0∞) (hθ0 : θ ≠ 0) (hθ_top : θ ≠ ∞) :
    (P.transitionKernel ^ t) x {y | θ ≤ Φ y} ≤ r ^ t * Φ x / θ := by
  have hmarkov := mul_meas_ge_le_lintegral₀
    (μ := (P.transitionKernel ^ t) x) hΦ.aemeasurable (ε := θ)
  have hdecay := lintegral_geometric_decay_reachable P Φ hΦ r c₀ hdrift t x hx
  -- θ · μ{θ ≤ Φ} ≤ ∫⁻ Φ ≤ r^t·Φ x ; divide by θ.
  have hθμ : θ * (P.transitionKernel ^ t) x {y | θ ≤ Φ y} ≤ r ^ t * Φ x :=
    le_trans hmarkov hdecay
  calc (P.transitionKernel ^ t) x {y | θ ≤ Φ y}
      = (θ⁻¹ * θ) * (P.transitionKernel ^ t) x {y | θ ≤ Φ y} := by
        rw [ENNReal.inv_mul_cancel hθ0 hθ_top, one_mul]
    _ = θ⁻¹ * (θ * (P.transitionKernel ^ t) x {y | θ ≤ Φ y}) := by rw [mul_assoc]
    _ ≤ θ⁻¹ * (r ^ t * Φ x) := by gcongr
    _ = r ^ t * Φ x * θ⁻¹ := by rw [mul_comm]
    _ = r ^ t * Φ x / θ := rfl

/-! ## Part 2 — the clock MGF drift at a SINGLE config (the honest scoping).

`ClockDepletionCoupling.expPot_drift` is stated with a universal per-step decrement bound
`hqbound : ∀ c, ... ≤ q`, but its proof body only ever applies `hqbound` at the SINGLE config it is
called at.  We cannot honestly hand it a universal built from a reachable-only bound (that would be
the refuted false universal).  So we re-derive the drift at a SINGLE FIXED config `c` directly,
with the hypothesis scoped to that `c` — the honest content of `expPot_drift`.  Then the
reachable-domain drift is the immediate instance at each reachable `c`.  The proof replicates the
`expPot_drift` argument (bounded-decrement `count_drop_le_two_support` + the per-step decrement mass
at `c`). -/

/-- **Single-config clock MGF drift.**  For `s ≥ 0` and the per-step decrement bound at the FIXED
config `c` only, the clock exponential potential satisfies the multiplicative drift
`∫⁻ Φ_s dK(c) ≤ (1 + q·(e^{2s}−1))·Φ_s(c)`.  This is `expPot_drift` with its hypothesis correctly
scoped to the single config (its proof uses `hqbound` only at this `c`). -/
theorem expPot_drift_single (P : Protocol Λ) (sc : Λ) (s : ℝ) (hs : 0 ≤ s) (N : ℕ)
    (q : ℝ≥0∞) (c : Config Λ)
    (hqc : (P.stepDistOrSelf c).toMeasure {c' : Config Λ | c'.count sc < c.count sc} ≤ q) :
    ∫⁻ c', expPot sc s N c' ∂(P.transitionKernel c)
      ≤ (1 + q * ENNReal.ofReal (Real.exp (2 * s) - 1)) * expPot sc s N c := by
  classical
  have hμmeas : (P.transitionKernel c) = (P.stepDistOrSelf c).toMeasure := rfl
  set S : Set (Config Λ) := {c' : Config Λ | c'.count sc < c.count sc} with hS
  have hSmeas : MeasurableSet S := MeasurableSet.of_discrete
  set A : ℝ := Real.exp (s * ((N : ℝ) - c.count sc)) with hA
  have hApos : 0 < A := Real.exp_pos _
  set E2 : ℝ := Real.exp (2 * s) - 1 with hE2
  have hE2nn : 0 ≤ E2 := by
    rw [hE2]; nlinarith [Real.add_one_le_exp (2 * s), Real.exp_pos (2 * s), hs]
  have hae : ∀ᵐ c' ∂(P.transitionKernel c),
      expPot sc s N c'
        ≤ ENNReal.ofReal A * (1 + S.indicator (fun _ => ENNReal.ofReal E2) c') := by
    rw [hμmeas]
    apply ClockDepletionCoupling.ae_of_pmf_support
    intro c' hc'
    have hdrop2 := count_drop_le_two_support P c sc c' hc'
    have hreal : Real.exp (s * ((N : ℝ) - c'.count sc))
        ≤ A * (1 + (if (c'.count sc < c.count sc) then E2 else 0)) := by
      by_cases h : c'.count sc < c.count sc
      · simp only [h, if_true]
        rw [hA, hE2, mul_add, mul_one, mul_sub_one,
          show A * Real.exp (2 * s) = Real.exp (s * ((N : ℝ) - c.count sc) + 2 * s) by
            rw [hA, ← Real.exp_add]]
        rw [show Real.exp (s * ((N : ℝ) - c.count sc))
              + (Real.exp (s * ((N : ℝ) - c.count sc) + 2 * s)
                - Real.exp (s * ((N : ℝ) - c.count sc)))
            = Real.exp (s * ((N : ℝ) - c.count sc) + 2 * s) by ring,
          Real.exp_le_exp]
        have hcc : (c.count sc : ℝ) ≤ (c'.count sc : ℝ) + 2 := by exact_mod_cast hdrop2
        nlinarith [hcc, hs,
          mul_nonneg hs (by linarith [hcc] : (0:ℝ) ≤ (c'.count sc : ℝ) + 2 - c.count sc)]
      · simp only [h, if_false, add_zero, mul_one]
        rw [hA, Real.exp_le_exp]
        push Not at h
        have hcc : (c.count sc : ℝ) ≤ (c'.count sc : ℝ) := by exact_mod_cast h
        rw [mul_sub, mul_sub]
        have hkey : s * (c.count sc : ℝ) ≤ s * (c'.count sc : ℝ) :=
          mul_le_mul_of_nonneg_left hcc hs
        linarith [hkey]
    unfold expPot
    calc ENNReal.ofReal (Real.exp (s * ((N : ℝ) - c'.count sc)))
        ≤ ENNReal.ofReal (A * (1 + (if (c'.count sc < c.count sc) then E2 else 0))) :=
          ENNReal.ofReal_le_ofReal hreal
      _ = ENNReal.ofReal A * (1 + S.indicator (fun _ => ENNReal.ofReal E2) c') := by
          rw [ENNReal.ofReal_mul hApos.le]
          congr 1
          by_cases h : c' ∈ S
          · rw [Set.indicator_of_mem h]
            have : c'.count sc < c.count sc := h
            simp only [this, if_true]
            rw [ENNReal.ofReal_add (by norm_num) hE2nn, ENNReal.ofReal_one]
          · rw [Set.indicator_of_notMem h]
            have : ¬ c'.count sc < c.count sc := h
            simp only [this, if_false, add_zero, ENNReal.ofReal_one]
  calc ∫⁻ c', expPot sc s N c' ∂(P.transitionKernel c)
      ≤ ∫⁻ c',
          ENNReal.ofReal A * (1 + S.indicator (fun _ => ENNReal.ofReal E2) c')
            ∂(P.transitionKernel c) := lintegral_mono_ae hae
    _ = ENNReal.ofReal A *
          ∫⁻ c', (1 + S.indicator (fun _ => ENNReal.ofReal E2) c')
            ∂(P.transitionKernel c) := by
          rw [lintegral_const_mul _ (by measurability)]
    _ = ENNReal.ofReal A * (1 + ENNReal.ofReal E2 * (P.transitionKernel c) S) := by
          congr 1
          rw [lintegral_add_left measurable_const, lintegral_const,
            lintegral_indicator_const hSmeas, measure_univ, mul_one, mul_comm]
    _ ≤ ENNReal.ofReal A * (1 + ENNReal.ofReal E2 * q) := by
          gcongr; rw [hμmeas]; exact hqc
    _ = (1 + q * ENNReal.ofReal E2) * expPot sc s N c := by
          unfold expPot
          rw [hA, mul_comm (ENNReal.ofReal E2) q,
            mul_comm (ENNReal.ofReal (Real.exp (s * ((N : ℝ) - c.count sc)))) _]

/-- **Reachable-domain clock MGF drift.**  For `s ≥ 0` and a per-step decrement bound `q` holding
on every config reachable from `c₀`, the clock potential satisfies the multiplicative drift at
every reachable `c`.  Immediate instance of `expPot_drift_single` at the reachable `c`. -/
theorem expPot_drift_reachable (P : Protocol Λ) (sc : Λ) (s : ℝ) (hs : 0 ≤ s) (N : ℕ)
    (q : ℝ≥0∞) (c₀ : Config Λ)
    (hqbound_reach : ∀ c : Config Λ, P.Reachable c₀ c →
      (P.stepDistOrSelf c).toMeasure {c' : Config Λ | c'.count sc < c.count sc} ≤ q)
    (c : Config Λ) (hc : P.Reachable c₀ c) :
    ∫⁻ c', expPot sc s N c' ∂(P.transitionKernel c)
      ≤ (1 + q * ENNReal.ofReal (Real.exp (2 * s) - 1)) * expPot sc s N c :=
  expPot_drift_single P sc s hs N q c (hqbound_reach c hc)

/-! ## Part 3 — the REACHABILITY-CONDITIONED depletion tail (the headline).

We now bound the per-`τ` depletion mass `(K^H) c₀ {count sc ≤ N − R}` using ONLY the reachable
caps.  The reachable per-step decrement rate is `q = 2m/n` (from `decrement_step_prob_le` plus the
reachable `card = n`, `count sc ≤ m`); `expPot_drift_reachable` supplies the drift on the
trajectory, and `geometric_drift_tail_reachable` iterates it.  The start `c₀` is reachable from
itself (`Reachable.refl`), so the tail holds at `c₀`. -/

/-- **Reachable per-step decrement bound `q = 2m/n`.**  On every config reachable from `c₀` the
population size is `n` (`hcard_reach`) and the clock count is `≤ m` (`hcap_reach`), and small
configs cannot decrement (`hsmall`, a TRUE universal).  Hence `decrement_step_prob_le`'s
config-dependent `2·count(sc)/card` becomes the uniform `2·m/n` on the reachable domain. -/
theorem reachable_decrement_bound (P : Protocol Λ) (sc : Λ) (n m : ℕ) (c₀ : Config Λ)
    (hcard_reach : ∀ c : Config Λ, P.Reachable c₀ c → 2 ≤ c.card → c.card = n)
    (hsmall : ∀ c : Config Λ, ¬ (2 ≤ c.card) →
      (P.stepDistOrSelf c).toMeasure {c' : Config Λ | c'.count sc < c.count sc} = 0)
    (hcap_reach : ∀ c : Config Λ, P.Reachable c₀ c → c.count sc ≤ m)
    (c : Config Λ) (hc : P.Reachable c₀ c) :
    (P.stepDistOrSelf c).toMeasure {c' : Config Λ | c'.count sc < c.count sc}
      ≤ 2 * (m : ℝ≥0∞) / (n : ℝ≥0∞) := by
  by_cases hcc : 2 ≤ c.card
  · have h := decrement_step_prob_le P c hcc sc
    rw [hcard_reach c hc hcc] at h
    refine h.trans ?_
    have : (c.count sc : ℝ≥0∞) ≤ (m : ℝ≥0∞) := by exact_mod_cast hcap_reach c hc
    gcongr
  · rw [hsmall c hcc]; exact bot_le

/-- **Reachability-conditioned depletion tail (the headline — replaces the FALSE universal caps).**
Same conclusion as `ClockDepletionCoupling.mgf_depletion_tail_uniform`, but the universal caps
`hcard : ∀ c, ...` / `hcap : ∀ c, count sc ≤ m` are replaced by the HONEST reachable-restricted
forms `hcard_reach`/`hcap_reach` (TRUE — `FaithfulDischargeTierA.card_eq_on_reachable` etc.; the
bare universals are FALSE, refutation-checked).  The chain from `c₀` stays reachable, so the MGF
drift only needs the rate `q = 2m/n` along the trajectory.  After `H` steps the kernel mass of
`{count sc ≤ N − R}` is bounded by `(1 + (2m/n)·(e^{2s}−1))^H · expPot sc s N c₀ / e^{s·R}`. -/
theorem mgf_depletion_tail_reachable (P : Protocol Λ) (sc : Λ) (s : ℝ) (hs : 0 < s)
    (N R n m : ℕ) (c₀ : Config Λ)
    (hcard_reach : ∀ c : Config Λ, P.Reachable c₀ c → 2 ≤ c.card → c.card = n)
    (hsmall : ∀ c : Config Λ, ¬ (2 ≤ c.card) →
      (P.stepDistOrSelf c).toMeasure {c' : Config Λ | c'.count sc < c.count sc} = 0)
    (hcap_reach : ∀ c : Config Λ, P.Reachable c₀ c → c.count sc ≤ m)
    (H : ℕ) :
    (P.transitionKernel ^ H) c₀ {c : Config Λ | (c.count sc : ℝ) ≤ (N : ℝ) - R}
      ≤ (1 + (2 * (m : ℝ≥0∞) / (n : ℝ≥0∞)) * ENNReal.ofReal (Real.exp (2 * s) - 1)) ^ H
          * expPot sc s N c₀ / ENNReal.ofReal (Real.exp (s * R)) := by
  classical
  set q : ℝ≥0∞ := 2 * (m : ℝ≥0∞) / (n : ℝ≥0∞) with hq
  set r : ℝ≥0∞ := 1 + q * ENNReal.ofReal (Real.exp (2 * s) - 1) with hr
  set θ : ℝ≥0∞ := ENNReal.ofReal (Real.exp (s * R)) with hθ
  have hθ0 : θ ≠ 0 := by
    rw [hθ]; simp [ENNReal.ofReal_eq_zero, not_le, Real.exp_pos]
  have hθtop : θ ≠ ∞ := by rw [hθ]; exact ENNReal.ofReal_ne_top
  -- The depletion set is contained in the super-level set `{θ ≤ Φ_s}`.
  have hsubset :
      {c : Config Λ | (c.count sc : ℝ) ≤ (N : ℝ) - R}
        ⊆ {c : Config Λ | θ ≤ expPot sc s N c} := by
    intro c hc
    simp only [Set.mem_setOf_eq] at hc ⊢
    rw [hθ]
    unfold expPot
    apply ENNReal.ofReal_le_ofReal
    rw [Real.exp_le_exp]
    have hRle : (R : ℝ) ≤ (N : ℝ) - c.count sc := by linarith [hc]
    nlinarith [hRle, hs.le, mul_le_mul_of_nonneg_left hRle hs.le]
  -- The reachable-domain drift (rate `q = 2m/n` on reachable configs).
  have hdrift : ∀ x : Config Λ, P.Reachable c₀ x →
      ∫⁻ y, expPot sc s N y ∂(P.transitionKernel x) ≤ r * expPot sc s N x := by
    intro x hx
    exact expPot_drift_reachable P sc s hs.le N q c₀
      (reachable_decrement_bound P sc n m c₀ hcard_reach hsmall hcap_reach) x hx
  calc (P.transitionKernel ^ H) c₀ {c : Config Λ | (c.count sc : ℝ) ≤ (N : ℝ) - R}
      ≤ (P.transitionKernel ^ H) c₀ {c : Config Λ | θ ≤ expPot sc s N c} :=
        measure_mono hsubset
    _ ≤ r ^ H * expPot sc s N c₀ / θ :=
        geometric_drift_tail_reachable P (expPot sc s N) (expPot_measurable sc s N) r c₀
          hdrift H c₀ Relation.ReflTransGen.refl θ hθ0 hθtop

/-! ## Part 4 — the per-`τ` forward-trajectory tail (instantiating the reachable caps).

For the clock per-`τ` prefix `∑_{τ<T} (K^τ) c₀ {count sc ≤ N − R}`, each term `(K^τ) c₀ {…}` is
exactly the headline `mgf_depletion_tail_reachable` at horizon `H := τ`.  So the SAME reachable
caps bound every forward-trajectory term uniformly: each `≤ (the MGF tail)`.  Feeding this to
`ClockStructGateDischarge.clock_prefix_fit` closes the clock per-`τ` input — the contracting slots
become regime-CLOSED modulo only the regime arithmetic on the MGF tail (the `η_clock ≤ 1/(3n²)`
fit, of the same `Q^τ/e^{sR}` shape as `struct_floor_fit`). -/

/-- **Per-`τ` clock depletion mass, uniform over the forward trajectory.**  For every `τ` (in
particular every `τ < T`), the term `(K^τ) c₀ {count sc ≤ N − R}` is bounded by the reachable MGF
tail at horizon `τ` — using ONLY the reachable caps.  This is exactly the per-`τ` input
`ClockStructGateDischarge.clock_prefix_fit` consumes (with `ε` the MGF-tail upper bound, once the
`Q^τ` factor is bounded by the regime horizon). -/
theorem clock_perτ_tail_reachable (P : Protocol Λ) (sc : Λ) (s : ℝ) (hs : 0 < s)
    (N R n m : ℕ) (c₀ : Config Λ)
    (hcard_reach : ∀ c : Config Λ, P.Reachable c₀ c → 2 ≤ c.card → c.card = n)
    (hsmall : ∀ c : Config Λ, ¬ (2 ≤ c.card) →
      (P.stepDistOrSelf c).toMeasure {c' : Config Λ | c'.count sc < c.count sc} = 0)
    (hcap_reach : ∀ c : Config Λ, P.Reachable c₀ c → c.count sc ≤ m)
    (τ : ℕ) :
    (P.transitionKernel ^ τ) c₀ {c : Config Λ | (c.count sc : ℝ) ≤ (N : ℝ) - R}
      ≤ (1 + (2 * (m : ℝ≥0∞) / (n : ℝ≥0∞)) * ENNReal.ofReal (Real.exp (2 * s) - 1)) ^ τ
          * expPot sc s N c₀ / ENNReal.ofReal (Real.exp (s * R)) :=
  mgf_depletion_tail_reachable P sc s hs N R n m c₀ hcard_reach hsmall hcap_reach τ

/-- **Uniform per-`τ` clock bound (the `clock_prefix_fit`-ready input).**  For `Q ≥ 1` the MGF tail
`Q^τ · Φ(c₀) / e^{sR}` grows with `τ`, so `Q^T · Φ(c₀) / e^{sR}` dominates every `τ ≤ T` term.
Hence every forward-trajectory term `(K^τ) c₀ {count sc ≤ N − R}` (for `τ ≤ T`) is bounded by the
single `ε := Q^T · Φ(c₀) / e^{sR}` — exactly the uniform per-`τ` input
`ClockStructGateDischarge.clock_prefix_fit` consumes.  This closes the clock per-`τ` hypothesis
`hClockPerτ` from the reachable caps; the residual `T·ε ≤ 1/(3n²)` fit is the SAME `Q^T/e^{sR}`
regime arithmetic as `ClockStructGateDischarge.struct_floor_fit` (PROVEN there). -/
theorem clock_perτ_uniform_reachable (P : Protocol Λ) (sc : Λ) (s : ℝ) (hs : 0 < s)
    (N R n m : ℕ) (c₀ : Config Λ)
    (hcard_reach : ∀ c : Config Λ, P.Reachable c₀ c → 2 ≤ c.card → c.card = n)
    (hsmall : ∀ c : Config Λ, ¬ (2 ≤ c.card) →
      (P.stepDistOrSelf c).toMeasure {c' : Config Λ | c'.count sc < c.count sc} = 0)
    (hcap_reach : ∀ c : Config Λ, P.Reachable c₀ c → c.count sc ≤ m)
    (T τ : ℕ) (hτ : τ ≤ T) :
    (P.transitionKernel ^ τ) c₀ {c : Config Λ | (c.count sc : ℝ) ≤ (N : ℝ) - R}
      ≤ (1 + (2 * (m : ℝ≥0∞) / (n : ℝ≥0∞)) * ENNReal.ofReal (Real.exp (2 * s) - 1)) ^ T
          * expPot sc s N c₀ / ENNReal.ofReal (Real.exp (s * R)) := by
  set Q : ℝ≥0∞ := 1 + (2 * (m : ℝ≥0∞) / (n : ℝ≥0∞)) * ENNReal.ofReal (Real.exp (2 * s) - 1) with hQdef
  have hQ1 : (1 : ℝ≥0∞) ≤ Q := by rw [hQdef]; exact le_add_right (le_refl 1)
  -- The per-`τ` tail bound (reachable), then monotone `Q^τ ≤ Q^T`.
  refine le_trans
    (clock_perτ_tail_reachable P sc s hs N R n m c₀ hcard_reach hsmall hcap_reach τ) ?_
  rw [ENNReal.div_le_iff (by simp [ENNReal.ofReal_eq_zero, not_le, Real.exp_pos])
    (ENNReal.ofReal_ne_top), ENNReal.div_mul_cancel
    (by simp [ENNReal.ofReal_eq_zero, not_le, Real.exp_pos]) (ENNReal.ofReal_ne_top)]
  gcongr

/-! ## Part 5 — non-vacuity guard + audit.

The reachable caps are the HONEST domain restriction.  Carrying them as bare universals would be
the refuted false universal (`FaithfulDischargeTierA.hcap_not_universal`).  The tail is non-vacuous:
for `s > 0`, `R ≥ 1`, `H·q·(e^{2s}−1) < s·R` the factor `(1 + q·(e^{2s}−1))^H / e^{s·R} < 1`. -/

/-- The reachable caps are NOT the refuted universal: the universal count cap is false, so the
honest route REQUIRES the reachable restriction `mgf_depletion_tail_reachable` consumes.  (Stated at
the genuine `AgentState L K` state space where the depletion tail is instantiated.) -/
theorem reachable_cap_is_honest {L K : ℕ} (sc : AgentState L K) (m : ℕ) :
    ¬ (∀ c : Config (AgentState L K), c.count sc ≤ m) :=
  FaithfulDischargeTierA.hcap_not_universal sc m

#print axioms lintegral_geometric_decay_reachable
#print axioms geometric_drift_tail_reachable
#print axioms expPot_drift_single
#print axioms expPot_drift_reachable
#print axioms reachable_decrement_bound
#print axioms mgf_depletion_tail_reachable
#print axioms clock_perτ_tail_reachable
#print axioms clock_perτ_uniform_reachable
#print axioms reachable_cap_is_honest

end ReachableClockTail
end ExactMajority
