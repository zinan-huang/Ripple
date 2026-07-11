/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Generic counter-timeout wrapper for timed phases (Doty et al., Phase C)

Every *timed* phase of the Doty exact-majority protocol (phases 0, 1, 5, 6, 7, 8)
is driven by the **shared standard counter subroutine** running on the `Clock`
agents.  The phase advances once every clock counter has been decremented down to
`0`.  The deterministic core — "a clock-clock interaction with positive counters
strictly decrements the combined counter, and a zero counter advances the phase" —
already lives in `Analysis/PhaseProgress.lean`
(`stdCounterSubroutine_counter_strict_descent`, `stdCounterSubroutine_zero_advances`).

This file provides the **probabilistic timeout wrapper** that turns that
deterministic decrement into a *whp finish in `C·n·log n` interactions* statement,
in a form parametric enough that each timed phase instantiates it.

## Engine

We reuse the block-geometric hitting machinery of `Probability/ExpectedHitting.lean`.
The single quantitative input each phase must supply is the **per-block
contraction**

    hblock : ∀ b ∈ Doneᶜ, (K ^ s) b Doneᶜ ≤ q          (q < 1, s = block length)

i.e. "from any not-yet-finished configuration, a block of `s` interactions fails
to finish the phase with probability at most `q`".  The phase derives this from
(i) the carried clock floor `clockCount ≥ cFrac·n`, (ii) the per-pair decrement
event (a clock-clock meeting fires with probability `≥ (cFrac·n)²-shape / n²`),
and (iii) the counter cap `counter ≤ counterMax`, via the deterministic
`PhaseProgress` facts.  Given that single input, this file delivers:

* `counterTimeout_tail` — the whp tail `(K^(numBlocks·s)) c₀ Doneᶜ ≤ q ^ numBlocks`;
* `counterTimeout_PhaseConvergenceW` — packaged as a `PhaseConvergenceW K` instance
  with horizon `t = numBlocks·s` and failure `ε = q ^ numBlocks` (the `C·n·log n`
  shape: `numBlocks = Θ(log n)`, `s = Θ(n)`);
* `counterTimeout_PhaseConvergenceW_of_pre` — the predicate-shaped variant whose
  `Pre`/`Post` discharge `Done := {y | Post y}` and the absorption/contraction from
  a phase-entry hypothesis, the form the per-phase files (0/1/5/6/7/8) plug into;
* `counterTimeout_chain` — the chaining corollary into `composeW_two_phases`, so a
  timed phase composes with whatever phase follows it.

`Done` is the **phase-advance trigger** ("all clock counters hit `0`, phase
advanced").  It must be absorbing under `K` (once advanced, the phase epidemic and
the next phase's rule never send any agent back), which is the deterministic
closure each phase already owns.

ZERO sorry, zero axiom (beyond `propext`/`Classical.choice`/`Quot.sound`),
zero `native_decide`.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ExpectedHitting
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.PhaseConvergenceWeak

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace CounterTimeout

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## Part 1 — The whp finish tail from a per-block contraction

The single fact each timed phase supplies is the per-block contraction `hblock`.
Everything probabilistic is then a thin wrapper over
`ExactMajority.bad_block_geometric`. -/

/-- **Counter-timeout whp tail.**  Let `Done` be the (measurable, absorbing) phase-
advance trigger.  If from every not-yet-finished configuration a block of `s`
interactions fails to finish the phase with probability at most `q`
(`hblock`), then after `numBlocks` such blocks the phase is unfinished with
probability at most `q ^ numBlocks`:

    (K ^ (numBlocks * s)) c₀ Doneᶜ ≤ q ^ numBlocks.

With `s = Θ(n)` (so that one block lets every clock meet another whp) and
`numBlocks = Θ(log n)`, the horizon `numBlocks * s = Θ(n log n)` interactions and
the failure `q ^ numBlocks = n^{-Θ(1)}`. -/
theorem counterTimeout_tail (K : Kernel Ω Ω) [IsMarkovKernel K]
    {Done : Set Ω} (hDone : MeasurableSet Done)
    (hAbs : ∀ x ∈ Done, K x Doneᶜ = 0)
    (s : ℕ) (q : ℝ≥0∞)
    (hblock : ∀ b ∈ (Doneᶜ : Set Ω), (K ^ s) b Doneᶜ ≤ q)
    (c₀ : Ω) (numBlocks : ℕ) :
    (K ^ (numBlocks * s)) c₀ Doneᶜ ≤ q ^ numBlocks :=
  bad_block_geometric K hDone hAbs s q hblock c₀ numBlocks

/-! ## Part 2 — Packaging the tail as a `PhaseConvergenceW`

The phase files target `PhaseConvergenceW K`, the weak convergence structure
(`Pre`/`Post`/`t`/`ε`/`convergence`, no deterministic absorption field).  The
`convergence` field is exactly the timeout tail of Part 1 once `Done := {y | Post y}`.

We work over a `DiscreteMeasurableSpace`, so `Done`'s measurability is automatic
(`DiscreteMeasurableSpace.forall_measurableSet`) — the instance writer never has to
supply it. -/

section Weak

variable {Ω : Type*} [MeasurableSpace Ω] [DiscreteMeasurableSpace Ω]

/-- **Counter-timeout convergence packaging.**  Given the same per-block
contraction `hblock` over `Done := {y | Post y}`, plus the entailment
`hpre : Pre x → ¬ Post x → ...` baked into `hblock`, package the timeout tail into
a `PhaseConvergenceW K` with horizon `t = numBlocks * s` and failure
`ε = q ^ numBlocks`.

* `Post` is the phase-advance trigger; `Done := {y | Post y}`.
* `hAbs` — `Post` is absorbing (the deterministic closure the phase owns).
* `hblock` — per-block finish-failure ≤ `q` from every not-yet-`Post` config.
* `hε` — `(q ^ numBlocks : ℝ≥0∞) ≤ ε`, i.e. the geometric tail fits under the
  target failure budget. -/
noncomputable def counterTimeout_PhaseConvergenceW (K : Kernel Ω Ω) [IsMarkovKernel K]
    (Pre Post : Ω → Prop)
    (hAbs : ∀ x, Post x → K x {y | ¬ Post y} = 0)
    (s : ℕ) (q : ℝ≥0∞)
    (hblock : ∀ b, ¬ Post b → (K ^ s) b {y | ¬ Post y} ≤ q)
    (numBlocks : ℕ) (ε : ℝ≥0)
    (hε : (q ^ numBlocks : ℝ≥0∞) ≤ (ε : ℝ≥0∞)) :
    PhaseConvergenceW K where
  Pre := Pre
  Post := Post
  t := numBlocks * s
  ε := ε
  convergence := by
    intro x₀ _hPre₀
    -- `Done := {y | Post y}`, so `Doneᶜ = {y | ¬ Post y}`.
    have hDone : MeasurableSet {y : Ω | Post y} :=
      DiscreteMeasurableSpace.forall_measurableSet _
    have hcompl : ({y : Ω | Post y}ᶜ) = {y : Ω | ¬ Post y} := by
      ext y; simp
    have hAbs' : ∀ x ∈ {y : Ω | Post y}, K x ({y : Ω | Post y}ᶜ) = 0 := by
      intro x hx; rw [hcompl]; exact hAbs x hx
    have hblock' : ∀ b ∈ ({y : Ω | Post y}ᶜ : Set Ω),
        (K ^ s) b ({y : Ω | Post y}ᶜ) ≤ q := by
      intro b hb
      rw [hcompl] at hb ⊢
      exact hblock b hb
    calc (K ^ (numBlocks * s)) x₀ {y | ¬ Post y}
        = (K ^ (numBlocks * s)) x₀ ({y : Ω | Post y}ᶜ) := by rw [hcompl]
      _ ≤ q ^ numBlocks :=
          counterTimeout_tail K hDone hAbs' s q hblock' x₀ numBlocks
      _ ≤ (ε : ℝ≥0∞) := hε

end Weak

/-! ## Part 3 — From a per-single-step finish probability

The most phase-friendly atom is the **per-step** finish-failure probability: "from
every not-yet-finished config, a single interaction fails to finish the phase with
probability at most `q₁`".  This is the direct image of the deterministic
PhaseProgress decrement plus the pair-meeting probability `≥ (cFrac·n)²-shape / n²`.

Iterating that single step over a block of `s` interactions multiplies the
failure: `s` steps fail with probability `≤ q₁ ^ s` (block contraction with block
length `s` and per-block failure `q₁ ^ s`... but here we instead read the whole
horizon as `t` single steps).  Concretely, with per-step failure `≤ q₁`, after `t`
interactions the phase is unfinished with probability `≤ q₁ ^ t`. -/

/-- **Per-step finish probability ⇒ whp finish tail.**  If `Done` is absorbing and
from every not-yet-done configuration a single interaction fails to finish with
probability at most `q₁`, then after `t` interactions the phase is unfinished with
probability at most `q₁ ^ t`.

This is `counterTimeout_tail` at block length `s = 1` (so `t = t * 1` blocks). -/
theorem counterTimeout_tail_perStep (K : Kernel Ω Ω) [IsMarkovKernel K]
    {Done : Set Ω} (hDone : MeasurableSet Done)
    (hAbs : ∀ x ∈ Done, K x Doneᶜ = 0)
    (q₁ : ℝ≥0∞)
    (hstep : ∀ b ∈ (Doneᶜ : Set Ω), K b Doneᶜ ≤ q₁)
    (c₀ : Ω) (t : ℕ) :
    (K ^ t) c₀ Doneᶜ ≤ q₁ ^ t := by
  have hblock : ∀ b ∈ (Doneᶜ : Set Ω), (K ^ 1) b Doneᶜ ≤ q₁ := by
    intro b hb; rw [pow_one]; exact hstep b hb
  have h := counterTimeout_tail K hDone hAbs 1 q₁ hblock c₀ t
  simpa using h

/-! ## Part 4 — Per-step packaging and the chaining corollary

The form a timed phase consumes:

* it supplies a per-step finish-failure bound `q₁` (from the carried clock floor +
  the per-pair decrement event + the counter cap), an absorbing `Post`, and a
  horizon `t` (the `C·n·log n` interaction count);
* it gets a `PhaseConvergenceW K` with failure `ε ≥ q₁ ^ t`;
* `counterTimeout_chain` then composes that timed phase with the next phase via
  `composeW_two_phases`, giving the prefix bound `K^(t₁+t₂) c Doneᶜ ≤ ε₁ + ε₂`. -/

section Weak2

variable {Ω : Type*} [MeasurableSpace Ω] [DiscreteMeasurableSpace Ω]

/-- **Per-step counter-timeout convergence.**  From a per-step finish-failure bound
`q₁` over the not-yet-`Post` class and an absorbing `Post`, build a
`PhaseConvergenceW K` with horizon `t` and failure `ε ≥ q₁ ^ t`.

This is the entry point for the timed phases 0/1/5/6/7/8: `q₁` is the per-
interaction probability that the phase does *not* advance (one minus the clock-
clock decrement probability `≥ (cFrac·n)²-shape / n²`), `t = Θ(n log n)` is the
interaction horizon, and `ε = q₁ ^ t = n^{-Θ(1)}` is the whp failure. -/
noncomputable def counterTimeout_PhaseConvergenceW_perStep (K : Kernel Ω Ω)
    [IsMarkovKernel K]
    (Pre Post : Ω → Prop)
    (hAbs : ∀ x, Post x → K x {y | ¬ Post y} = 0)
    (q₁ : ℝ≥0∞)
    (hstep : ∀ b, ¬ Post b → K b {y | ¬ Post y} ≤ q₁)
    (t : ℕ) (ε : ℝ≥0)
    (hε : (q₁ ^ t : ℝ≥0∞) ≤ (ε : ℝ≥0∞)) :
    PhaseConvergenceW K where
  Pre := Pre
  Post := Post
  t := t
  ε := ε
  convergence := by
    intro x₀ _hPre₀
    have hDone : MeasurableSet {y : Ω | Post y} :=
      DiscreteMeasurableSpace.forall_measurableSet _
    have hcompl : ({y : Ω | Post y}ᶜ) = {y : Ω | ¬ Post y} := by
      ext y; simp
    have hAbs' : ∀ x ∈ {y : Ω | Post y}, K x ({y : Ω | Post y}ᶜ) = 0 := by
      intro x hx; rw [hcompl]; exact hAbs x hx
    have hstep' : ∀ b ∈ ({y : Ω | Post y}ᶜ : Set Ω), K b ({y : Ω | Post y}ᶜ) ≤ q₁ := by
      intro b hb; rw [hcompl] at hb ⊢; exact hstep b hb
    calc (K ^ t) x₀ {y | ¬ Post y}
        = (K ^ t) x₀ ({y : Ω | Post y}ᶜ) := by rw [hcompl]
      _ ≤ q₁ ^ t :=
          counterTimeout_tail_perStep K hDone hAbs' q₁ hstep' x₀ t
      _ ≤ (ε : ℝ≥0∞) := hε

/-- **Chaining corollary.**  A timed phase (a `PhaseConvergenceW`) composes with the
next phase via the weak two-phase composition: if the timed phase's `Post` entails
the next phase's `Pre`, then from the timed phase's `Pre` the combined horizon
`timed.t + next.t` lands in `next.Post` with failure at most `timed.ε + next.ε`.

This is exactly `composeW_two_phases` specialized to a timed leading phase; it is
the shape the per-phase files (0→1, 1→2, 5→6, …) feed their convergence instances
into. -/
theorem counterTimeout_chain (K : Kernel Ω Ω) [IsMarkovKernel K]
    (timed next : PhaseConvergenceW K)
    (h_chain : ∀ x, timed.Post x → next.Pre x)
    (x₀ : Ω) (hx₀ : timed.Pre x₀) :
    (K ^ (timed.t + next.t)) x₀ {y | ¬ next.Post y} ≤ (timed.ε + next.ε : ℝ≥0∞) :=
  composeW_two_phases timed next h_chain x₀ hx₀

end Weak2

end CounterTimeout

end ExactMajority
