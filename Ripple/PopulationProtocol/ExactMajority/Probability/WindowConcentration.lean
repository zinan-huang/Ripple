/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Avenue F — the GENERAL trajectory-level concentration FRAMEWORK

This file extracts, from Avenue S1's ad-hoc single-window construction
(`ConstantDensityEpidemic.lean`), the **general, reusable builder** that turns a
per-step potential-drift bound on an absorbing window into a kernel-level
`PhaseConvergence`.  It is the common prerequisite that unblocks the remaining
phases, the multi-level front, S3, and the clock re-composition: with this
builder in hand each remaining piece collapses to "define a potential `Φ` +
prove one-step contraction on its window", and the multi-step tail + the
`PhaseConvergence` wrapping (consumed by A1's `compose_n_phases`) come for free.

## The recurring gap (A0 / B / S1 / S2b)

Every piece of the §6 campaign hits the SAME wall: a drift / advance bound that
holds only on an *absorbing* window `Q` (a one-step-support-closed set containing
the start) must be lifted to a kernel-level multi-step concentration statement
that A1 can consume.  `JansonHitting.MilestonePhase.toPhaseConvergence` does this
only for the unit-coverage milestone engine with the rate hardwired (`λ = 2`);
S1 did it *ad hoc* for one constant-density window via
`lintegral_decay_on_absorbing` + `measure_ge_one_on_absorbing`.  Avenue F lifts
that S1 primitive out of the constant-density specifics into an abstract builder
allowing an arbitrary potential `Φ`, absorbing predicate `Q`, contraction rate
`r`, postcondition `Post`, and threshold `θ`.

## What is built (0 sorry / 0 axiom / no native_decide)

* `lintegral_decay_on_absorbing` — the abstract `Pre`-conditioned multiplicative
  drift decay (re-proven here, lifting S1's; **S1 is not edited**), reusing
  `Protocol.ae_of_stepDistOrSelf_support_preserved`;
* `measure_ge_thresh_on_absorbing` — abstract `Pre`-conditioned Markov tail at an
  arbitrary threshold `θ` (generalizing S1's `measure_ge_one_on_absorbing`, which
  is the `θ = 1` case);
* `windowDrift_tail` — the kernel-level multi-step tail
  `(Kᵗ) c₀ {¬Post} ≤ rᵗ · Φ(c₀) / θ` from a one-step contraction on `Q`;
* `windowDrift_PhaseConvergence` — **the keystone**: packages `windowDrift_tail`
  into a `PhaseConvergence P.transitionKernel`, with the supplied `ε`;
* `windowGrowth_PhaseConvergence` — the DUAL "growth-suppression" form (S2b's
  direction: a front quantity stays small).  As documented below it is the same
  lemma instantiated with `Φ = exp(s · value)`: choosing the potential covers
  both the "deficit shrinks" (S1) and "value stays bounded" (S2b) directions, so
  the dual is a thin convenience wrapper, not a separate proof.
* `s1_via_framework` — the sanity instantiation that reproduces S1's
  `constantDensity_epidemic_O1_parallel` THROUGH the general builder (S1 itself
  is untouched).

Reference: S1 = `ConstantDensityEpidemic.lean`; consumer = A1's
`compose_n_phases` / `PhaseConvergence`.
-/

import Ripple.PopulationProtocol.ExactMajority.Probability.ConstantDensityEpidemic
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseConvergence

namespace Ripple.PopulationProtocol.ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real BigOperators

namespace WindowConcentration

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-! ## The abstract `Pre`-conditioned multiplicative-drift decay.

This is `ConstantDensityEpidemic.lintegral_decay_on_absorbing` lifted verbatim
into the framework namespace.  It is already abstract in `Φ`, `Q`, `r`, so the
"lift" is exactly a re-proof (NOT an edit of S1): S1 then becomes one
instantiation through `windowDrift_PhaseConvergence`.  The proof threads the a.e.
invariance of the absorbing predicate `Q` along the trajectory via
`Protocol.ae_of_stepDistOrSelf_support_preserved`. -/

/-- **`Pre`-conditioned geometric decay (lintegral form), abstract.**  If a
measurable potential `Φ` contracts at rate `r` on every configuration satisfying
the *one-step-support-closed* predicate `Q`, then starting from any `c₀` with
`Q c₀` the `t`-step expectation contracts geometrically:
`∫ Φ d(Kᵗ)(c₀) ≤ rᵗ · Φ(c₀)`. -/
theorem lintegral_decay_on_absorbing (P : Protocol Λ)
    (Φ : Config Λ → ℝ≥0∞) (hΦ : Measurable Φ)
    (Q : Config Λ → Prop)
    (hQ_abs : ∀ c c', Q c → c' ∈ (P.stepDistOrSelf c).support → Q c')
    (r : ℝ≥0∞)
    (hdrift : ∀ c, Q c → ∫⁻ c', Φ c' ∂(P.transitionKernel c) ≤ r * Φ c)
    (t : ℕ) (c₀ : Config Λ) (hQ0 : Q c₀) :
    ∫⁻ c', Φ c' ∂((P.transitionKernel ^ t) c₀) ≤ r ^ t * Φ c₀ := by
  induction t generalizing c₀ with
  | zero =>
    simp only [pow_zero, one_mul]
    change ∫⁻ c', Φ c' ∂(Kernel.id c₀) ≤ Φ c₀
    rw [Kernel.id_apply, lintegral_dirac' c₀ hΦ]
  | succ t ih =>
    change ∫⁻ c', Φ c' ∂(((P.transitionKernel ^ t) ∘ₖ P.transitionKernel) c₀)
      ≤ r ^ (t + 1) * Φ c₀
    rw [Kernel.lintegral_comp _ _ c₀ hΦ]
    have hae : ∀ᵐ b ∂(P.transitionKernel c₀),
        ∫⁻ c', Φ c' ∂((P.transitionKernel ^ t) b) ≤ r ^ t * Φ b := by
      have hsupp_ae : ∀ᵐ b ∂(P.transitionKernel c₀), Q b := by
        have h1 := Protocol.ae_of_stepDistOrSelf_support_preserved P Q hQ_abs c₀ hQ0 1
        simpa [pow_one] using h1
      filter_upwards [hsupp_ae] with b hb
      exact ih b hb
    calc ∫⁻ b, ∫⁻ c', Φ c' ∂((P.transitionKernel ^ t) b) ∂(P.transitionKernel c₀)
        ≤ ∫⁻ b, r ^ t * Φ b ∂(P.transitionKernel c₀) := lintegral_mono_ae hae
      _ = r ^ t * ∫⁻ b, Φ b ∂(P.transitionKernel c₀) := lintegral_const_mul _ hΦ
      _ ≤ r ^ t * (r * Φ c₀) := by gcongr; exact hdrift c₀ hQ0
      _ = r ^ (t + 1) * Φ c₀ := by rw [pow_succ, mul_assoc]

/-! ## The abstract `Pre`-conditioned Markov tail at threshold `θ`.

S1's `measure_ge_one_on_absorbing` is the `θ = 1` case of this.  The general
threshold form is what lets a window potential whose "unfinished" region is
`{θ ≤ Φ}` (rather than `{1 ≤ Φ}`) feed the builder directly. -/

/-- **`Pre`-conditioned Markov tail at threshold `θ`.**  Under the hypotheses of
`lintegral_decay_on_absorbing`, for `θ ≠ 0` the probability that `θ ≤ Φ` after
`t` steps is at most `rᵗ · Φ(c₀) / θ`. -/
theorem measure_ge_thresh_on_absorbing (P : Protocol Λ)
    (Φ : Config Λ → ℝ≥0∞) (hΦ : Measurable Φ)
    (Q : Config Λ → Prop)
    (hQ_abs : ∀ c c', Q c → c' ∈ (P.stepDistOrSelf c).support → Q c')
    (r : ℝ≥0∞)
    (hdrift : ∀ c, Q c → ∫⁻ c', Φ c' ∂(P.transitionKernel c) ≤ r * Φ c)
    (t : ℕ) (c₀ : Config Λ) (hQ0 : Q c₀)
    (θ : ℝ≥0∞) (hθ : θ ≠ 0) (hθ_top : θ ≠ ⊤) :
    (P.transitionKernel ^ t) c₀ {c | θ ≤ Φ c} ≤ r ^ t * Φ c₀ / θ := by
  -- Markov's inequality at level θ: θ · μ{θ ≤ Φ} ≤ ∫ Φ ≤ rᵗ · Φ(c₀).
  have hmarkov := mul_meas_ge_le_lintegral₀ (μ := (P.transitionKernel ^ t) c₀)
    hΦ.aemeasurable θ
  have hdecay := lintegral_decay_on_absorbing P Φ hΦ Q hQ_abs r hdrift t c₀ hQ0
  have hchain : θ * (P.transitionKernel ^ t) c₀ {c | θ ≤ Φ c} ≤ r ^ t * Φ c₀ :=
    le_trans hmarkov hdecay
  -- divide both sides by θ:  a ≤ b/θ ↔ a*θ ≤ b
  rw [ENNReal.le_div_iff_mul_le (Or.inl hθ) (Or.inl hθ_top), mul_comm]
  exact hchain

/-! ## The kernel-level multi-step tail.

The "unfinished" region `{¬Post}` is contained in `{θ ≤ Φ}` (failing the goal
forces the potential above threshold), so the threshold Markov tail yields the
clean multi-step bound `(Kᵗ) c₀ {¬Post} ≤ rᵗ · Φ(c₀) / θ`. -/

/-- **Window-drift multi-step tail.**  Given the abstract one-step contraction on
the absorbing window `Q`, plus a measurable threshold link `¬Post c → θ ≤ Φ c`,
the probability of *not* having reached `Post` after `t` steps is bounded by the
geometric tail `rᵗ · Φ(c₀) / θ`. -/
theorem windowDrift_tail (P : Protocol Λ)
    (Φ : Config Λ → ℝ≥0∞) (hΦ : Measurable Φ)
    (Q : Config Λ → Prop)
    (hQ_abs : ∀ c c', Q c → c' ∈ (P.stepDistOrSelf c).support → Q c')
    (r : ℝ≥0∞)
    (hdrift : ∀ c, Q c → ∫⁻ c', Φ c' ∂(P.transitionKernel c) ≤ r * Φ c)
    (Post : Config Λ → Prop)
    (θ : ℝ≥0∞) (hθ : θ ≠ 0) (hθ_top : θ ≠ ⊤)
    (hlink : ∀ c, ¬ Post c → θ ≤ Φ c)
    (t : ℕ) (c₀ : Config Λ) (hQ0 : Q c₀) :
    (P.transitionKernel ^ t) c₀ {c | ¬ Post c} ≤ r ^ t * Φ c₀ / θ := by
  have hsubset : {c : Config Λ | ¬ Post c} ⊆ {c | θ ≤ Φ c} := fun c hc => hlink c hc
  calc (P.transitionKernel ^ t) c₀ {c | ¬ Post c}
      ≤ (P.transitionKernel ^ t) c₀ {c | θ ≤ Φ c} := measure_mono hsubset
    _ ≤ r ^ t * Φ c₀ / θ :=
        measure_ge_thresh_on_absorbing P Φ hΦ Q hQ_abs r hdrift t c₀ hQ0 θ hθ hθ_top

/-! ## The keystone: `windowDrift_PhaseConvergence`.

Packages everything into a `PhaseConvergence` that A1's `compose_n_phases`
consumes.  The caller supplies:
* a potential `Φ`, an absorbing window `Q`, a per-step contraction rate `r` on
  `Q`, a postcondition `Post` (with its kernel-absorbing proof) and a threshold
  `θ` with the link `¬Post → θ ≤ Φ`;
* the budget `t` and a target failure probability `ε : ℝ≥0` together with the
  single arithmetic check that the geometric tail at *every* admissible start
  fits under `ε`.

`Pre` is parameterised: it must imply `Q` (start lies in the window) and bound
the initial potential, `Φ(c₀) ≤ Φ₀`, so the uniform tail
`rᵗ · Φ₀ / θ ≤ ε` discharges all starts at once. -/

/-- **The general trajectory-level concentration builder.**  Turns a one-step
drift contraction on an absorbing window into a kernel-level `PhaseConvergence`.

* `hPost_abs` — `Post` is one-step-support closed (hence kernel-absorbing);
* `hdrift` — per-step contraction `∫ Φ dK(c) ≤ r · Φ(c)` on the window `Q`;
* `hlink` — failing `Post` forces `Φ ≥ θ`;
* `hPre_Q` — `Pre` lies inside the window;
* `hPre_bound` — `Pre` bounds the initial potential by `Φ₀`;
* `hε` — the geometric tail fits under `ε`: `rᵗ · Φ₀ / θ ≤ ε`. -/
noncomputable def windowDrift_PhaseConvergence (P : Protocol Λ)
    (Φ : Config Λ → ℝ≥0∞) (hΦ : Measurable Φ)
    (Q : Config Λ → Prop)
    (hQ_abs : ∀ c c', Q c → c' ∈ (P.stepDistOrSelf c).support → Q c')
    (r : ℝ≥0∞)
    (hdrift : ∀ c, Q c → ∫⁻ c', Φ c' ∂(P.transitionKernel c) ≤ r * Φ c)
    (Pre Post : Config Λ → Prop)
    (hPost_abs : ∀ c c', Post c → c' ∈ (P.stepDistOrSelf c).support → Post c')
    (θ : ℝ≥0∞) (hθ : θ ≠ 0) (hθ_top : θ ≠ ⊤)
    (hlink : ∀ c, ¬ Post c → θ ≤ Φ c)
    (hPre_Q : ∀ c, Pre c → Q c)
    (Φ₀ : ℝ≥0∞) (hPre_bound : ∀ c, Pre c → Φ c ≤ Φ₀)
    (t : ℕ) (ε : ℝ≥0)
    (hε : r ^ t * Φ₀ / θ ≤ (ε : ℝ≥0∞)) :
    PhaseConvergence P.transitionKernel where
  Pre := Pre
  Post := Post
  t := t
  ε := ε
  post_absorbing := by
    intro c hc
    change (P.stepDistOrSelf c).toMeasure {c' | Post c'} = 1
    rw [(P.stepDistOrSelf c).toMeasure_apply_eq_one_iff
      (DiscreteMeasurableSpace.forall_measurableSet _)]
    intro c' hc'
    exact hPost_abs c c' hc hc'
  convergence := by
    intro c₀ hPre₀
    have hQ0 : Q c₀ := hPre_Q c₀ hPre₀
    calc (P.transitionKernel ^ t) c₀ {c | ¬ Post c}
        ≤ r ^ t * Φ c₀ / θ :=
          windowDrift_tail P Φ hΦ Q hQ_abs r hdrift Post θ hθ hθ_top hlink t c₀ hQ0
      _ ≤ r ^ t * Φ₀ / θ := by
          gcongr
          exact hPre_bound c₀ hPre₀
      _ ≤ (ε : ℝ≥0∞) := hε

/-! ## The dual growth-suppression form (S2b's direction).

S2b needs the *opposite* sign: a front quantity `V : Config → ℝ` must stay
SMALL.  This is the same builder with the standard exponential change of
potential `Φ(c) = exp(s · V(c))` (`s > 0`).  "The front grew past `b`" is
`{b ≤ V}`, which equals `{exp(s·b) ≤ Φ}`, i.e. the threshold link with
`θ = exp(s·b)`; one-step *suppression* of `V` is exactly one-step contraction of
`Φ`.  So the dual is `windowDrift_PhaseConvergence` instantiated at this `Φ` and
`θ`; we expose it as a named wrapper rather than a separate proof. -/

/-- **The dual growth-suppression builder.**  A front value `V : Config → ℝ`
that contracts in the exponential potential `Φ = exp(s·V)` on an absorbing window
gives a `PhaseConvergence` for the goal `Post := V < b` (front stays below `b`),
with threshold `θ = exp(s·b)`.  This is `windowDrift_PhaseConvergence` with
`Φ = exp(s·V)`; choosing the potential covers both the S1 "deficit shrinks" and
the S2b "value stays bounded" directions, so this is a thin convenience wrapper,
not a separate proof. -/
noncomputable def windowGrowth_PhaseConvergence (P : Protocol Λ)
    (V : Config Λ → ℝ) (s : ℝ) (hs : 0 < s)
    (Q : Config Λ → Prop)
    (hQ_abs : ∀ c c', Q c → c' ∈ (P.stepDistOrSelf c).support → Q c')
    (r : ℝ≥0∞)
    (hdrift : ∀ c, Q c →
      ∫⁻ c', ENNReal.ofReal (Real.exp (s * V c')) ∂(P.transitionKernel c)
        ≤ r * ENNReal.ofReal (Real.exp (s * V c)))
    (Pre : Config Λ → Prop) (b : ℝ)
    (hPost_abs : ∀ c c', V c < b → c' ∈ (P.stepDistOrSelf c).support → V c' < b)
    (hPre_Q : ∀ c, Pre c → Q c)
    (V₀ : ℝ) (hPre_bound : ∀ c, Pre c → V c ≤ V₀)
    (t : ℕ) (ε : ℝ≥0)
    (hε : r ^ t * ENNReal.ofReal (Real.exp (s * V₀)) / ENNReal.ofReal (Real.exp (s * b))
        ≤ (ε : ℝ≥0∞)) :
    PhaseConvergence P.transitionKernel :=
  windowDrift_PhaseConvergence P
    (fun c => ENNReal.ofReal (Real.exp (s * V c)))
    (fun _ _ => DiscreteMeasurableSpace.forall_measurableSet _)
    Q hQ_abs r hdrift
    Pre (fun c => V c < b)
    hPost_abs
    (ENNReal.ofReal (Real.exp (s * b)))
    (by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact Real.exp_pos _)
    ENNReal.ofReal_ne_top
    (by
      intro c hc
      rw [not_lt] at hc
      apply ENNReal.ofReal_le_ofReal
      exact Real.exp_le_exp.mpr (by nlinarith [hs, hc]))
    hPre_Q
    (ENNReal.ofReal (Real.exp (s * V₀)))
    (by
      intro c hc
      apply ENNReal.ofReal_le_ofReal
      exact Real.exp_le_exp.mpr (by nlinarith [hs, hPre_bound c hc]))
    t ε hε

/-! ## Sanity check: S1 reproduced through the framework.

We re-derive S1's `constantDensity_epidemic_O1_parallel` THROUGH
`windowDrift_PhaseConvergence`, confirming the general builder reproduces the
proven S1 result.  S1 itself is untouched; this is a separate instantiation.

The instantiation:
* potential `Φ = ConstantDensity.windowPot n (log 2)` (S1's window potential);
* window `Q = ConstantDensity.floorInv n` (absorbing, S1's `floorInvariant_absorbing`);
* rate `r = ofReal (199/200)` (S1's constant-density contraction rate);
* contraction `hdrift = ConstantDensity.windowPot_drift_floorInv` (S1's drift);
* `Post = ConstantDensity.Crossed n`, threshold `θ = 1`
  (S1's `not_crossed_imp_pot_ge_one` gives the `¬Post → 1 ≤ Φ` link);
* `Pre c := card = n ∧ informed = lo n`, initial potential `Φ₀ = 2^{hi-lo}`.

The resulting `convergence` field reproduces exactly S1's kernel-level bound. -/

open ConstantDensity Phase2Time

/-- S1's constant-density crossing, REBUILT through the general framework.
The `Pre` is "start at the lower boundary" (`card = n`, `informed = lo n`); the
`Post` is "crossed" (`hi n ≤ informed`); `t` and `ε` are the caller's budget. -/
noncomputable def s1_via_framework (n : ℕ) (hn : 20 ≤ n)
    (t : ℕ) (ε : ℝ≥0)
    (hε : ENNReal.ofReal ((199 / 200 : ℝ)) ^ t *
            ENNReal.ofReal (Real.exp (Real.log 2 * ((hi n : ℝ) - (lo n : ℝ)))) / 1
          ≤ (ε : ℝ≥0∞)) :
    PhaseConvergence epidemicProto.transitionKernel := by
  have hs : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  -- the constant-density rate r = ofReal(1 - (1/100)(1 - e^{-log2})) = ofReal(199/200)
  have he : Real.exp (-Real.log 2) = 1 / 2 := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ) < 2)]; norm_num
  have hrate : (1 : ℝ) - (1 / 100) * (1 - Real.exp (-Real.log 2)) = 199 / 200 := by
    rw [he]; norm_num
  refine windowDrift_PhaseConvergence epidemicProto
    (windowPot n (Real.log 2)) (windowPot_measurable n (Real.log 2))
    (floorInv n) (floorInvariant_absorbing n)
    (ENNReal.ofReal (1 - (1 / 100) * (1 - Real.exp (-Real.log 2))))
    (windowPot_drift_floorInv n (Real.log 2) hs hn)
    (fun c => c.card = n ∧ informed c = lo n)   -- Pre
    (Crossed n)                                  -- Post
    ?_                                           -- hPost_abs
    1 one_ne_zero ENNReal.one_ne_top             -- θ = 1
    ?_                                           -- hlink
    ?_                                           -- hPre_Q
    (ENNReal.ofReal (Real.exp (Real.log 2 * ((hi n : ℝ) - (lo n : ℝ)))))  -- Φ₀
    ?_                                           -- hPre_bound
    t ε ?_                                       -- hε
  · -- Post = Crossed is one-step-support closed (informed non-decreasing)
    intro c c' hcr hsupp
    exact informed_ge_monotone (hi n) c c' hcr hsupp
  · -- ¬Crossed → 1 ≤ Φ
    intro c hc
    exact not_crossed_imp_pot_ge_one n (Real.log 2) hs hn c hc
  · -- Pre → floorInv
    intro c ⟨hcard, hinf⟩
    exact ⟨hcard, by rw [hinf]⟩
  · -- Pre → Φ ≤ Φ₀  (at the lower boundary Φ = ofReal(exp(log2·(hi-lo))) = Φ₀)
    intro c ⟨hcard, hinf⟩
    have hΦc : windowPot n (Real.log 2) c
        = ENNReal.ofReal (Real.exp (Real.log 2 * ((hi n : ℝ) - (lo n : ℝ)))) := by
      unfold windowPot
      rw [if_neg (by rw [hinf]; have := lo_lt_hi n hn; omega)]
      rw [clampInf_eq_of_floor n c (by rw [hinf])]
      congr 2
      have : min (informed c) (hi n) = lo n := by
        rw [hinf]; have := lo_lt_hi n hn; omega
      rw [this]
    rw [hΦc]
  · -- the ε arithmetic: rewrite the rate to 199/200 and forward hε
    rw [hrate] at *
    exact hε

/-- **Sanity verdict.**  The framework genuinely reproduces S1's proven headline
bound: the `convergence` field of the framework-built phase, instantiated at
S1's parameters, yields exactly S1's `constantDensity_epidemic_O1_parallel`
kernel-level bound `(Kᵗ) c₀ {informed < hi} ≤ (199/200)ᵗ · 2^{hi−lo}`.  This is
derived purely through `s1_via_framework` (S1's own proof is untouched). -/
theorem informed_lt_hi_tail_via_framework (n : ℕ) (hn : 20 ≤ n)
    (c₀ : Config Bool) (hcard : c₀.card = n) (hinf : informed c₀ = lo n) (t : ℕ) :
    (epidemicProto.transitionKernel ^ t) c₀ {c | informed c < hi n} ≤
      ENNReal.ofReal (((199 : ℝ) / 200) ^ t * (2 : ℝ) ^ (hi n - lo n)) := by
  -- Build the framework phase with ε equal to S1's RHS, then read off `convergence`.
  set εR : ℝ := ((199 : ℝ) / 200) ^ t * (2 : ℝ) ^ (hi n - lo n) with hεR
  have hεR_nonneg : 0 ≤ εR := by positivity
  -- The framework ε-hypothesis: tail ≤ ofReal εR  (= ε as ℝ≥0).
  have hε : ENNReal.ofReal ((199 / 200 : ℝ)) ^ t *
            ENNReal.ofReal (Real.exp (Real.log 2 * ((hi n : ℝ) - (lo n : ℝ)))) / 1
          ≤ (εR.toNNReal : ℝ≥0∞) := by
    rw [div_one, ENNReal.ofNNReal_toNNReal εR, ← ENNReal.ofReal_pow (by norm_num)]
    -- exp(log2·(hi−lo)) = 2^{hi−lo}
    have hpot : Real.exp (Real.log 2 * ((hi n : ℝ) - (lo n : ℝ))) = (2 : ℝ) ^ (hi n - lo n) := by
      have hcast : ((hi n : ℝ) - (lo n : ℝ)) = ((hi n - lo n : ℕ) : ℝ) := by
        rw [Nat.cast_sub (by have := lo_lt_hi n hn; omega)]
      rw [hcast, mul_comm, Real.exp_nat_mul, Real.exp_log (by norm_num : (0:ℝ) < 2)]
    rw [hpot, hεR, ENNReal.ofReal_mul (by positivity)]
  -- Instantiate the phase and read off its convergence at c₀.
  have hconv := (s1_via_framework n hn t εR.toNNReal hε).convergence c₀ ⟨hcard, hinf⟩
  -- The phase's `Post` is defeq to `Crossed n`, so `{¬Post} = {informed < hi}`.
  have hev : {c : Config Bool | ¬ (s1_via_framework n hn t εR.toNNReal hε).Post c}
      = {c : Config Bool | informed c < hi n} := by
    apply Set.ext; intro c
    change ¬ Crossed n c ↔ informed c < hi n
    simp only [Crossed, not_le]
  rw [hev] at hconv
  -- ε = ↑εR.toNNReal = ofReal εR.
  calc (epidemicProto.transitionKernel ^ t) c₀ {c | informed c < hi n}
      ≤ (εR.toNNReal : ℝ≥0∞) := hconv
    _ = ENNReal.ofReal εR := ENNReal.ofNNReal_toNNReal εR

end WindowConcentration

end Ripple.PopulationProtocol.ExactMajority
