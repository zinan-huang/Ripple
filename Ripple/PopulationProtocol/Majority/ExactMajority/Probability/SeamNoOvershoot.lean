/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Doty §6 — the SEAM NO-OVERSHOOT timing-separation tail (`SeamNoOvershoot`)

This file discharges the per-seam `hNoOvershoot` event that `SeamEpidemics` carries
as a named budget but never consumes: during the advance-epidemic seam from work
phase `p` to `p+1`, NO agent runs ahead two phases (to `phase ≥ p+2`).  This is the
timing-separation half of the `≥`-window-to-exact-window reconciliation
(`SeamEpidemics.allPhaseEq_of_ge_and_no_overshoot`): the next work phase's EXACT
`Pre` (`allPhaseEq (p+1)`) is recovered from the seam's `≥ (p+1)`-`Post` exactly
when no overshoot occurred.

## The mechanism (mirrors `Phase0Window`, blueprint `HANDOFF_SEAM_NOOVERSHOOT.md`)

Phase advance out of a COUNTER-TIMED work phase `p+1` happens ONLY via a clock's
counter hitting `0` (`Transition.stdCounterSubroutine`, the `counter = 0` branch
running `advancePhaseWithInit`); the counter counts DOWN from `50(L+1)`.  The
universal phase epidemic (`Transition_*_phase_ge_pair_max`) only ever raises a phase
to the `max` of the two interacting phases, so on a no-overshoot config (all phases
`< p+2`) the epidemic alone CANNOT create a `p+2` agent — the first such creation
must be counter-driven in a timed phase.  We therefore reuse the `Phase0Window`
downward-crossing exponential potential, restricted to the AT-RISK new-phase clocks:

  `Φ_s c := ∑_{a clock, phase = p+1} exp(−s · a.counter)`     (a `Config.sumOf`)

`{∃ at-risk clock with counter = 0}` forces `Φ_s ≥ 1`, and the affine drift +
immigration tail engine (`Phase0Window.phase0_window_tail_affine`) closes the tail
to `e^{−40(L+1)}` — the seam version of the Phase-0 `e^{−45(L+1)}`, with `40` instead
of `45` for the epidemic "fresh clock" immigration (a phase-`p` clock infected by the
`(p+1)`-epidemic enters phase `p+1` with FULL counter `50(L+1)`; the per-step
immigration is bounded by `2·exp(−s·50(L+1))`).

## The honest counter-timed destination set

After reading `Protocol/Transition.lean` (FROZEN), the destination phases whose entry
is driven by a clock's counter (`stdCounterSubroutine` on a clock) are
`{1, 3, 5, 6, 7, 8}`.  BUT the no-overshoot DRIFT additionally needs the epidemic
"fresh clock" immigration term to be small — a phase-`p` clock dragged into phase
`p+1` by the epidemic enters with FULL counter `50(L+1)` (summand `= M`) ONLY when
`phaseInit (p+1)` RESETS the clock counter.  Checking `phaseInit` (FROZEN): the
counter is reset to `50(L+1)` exactly for phases `{1, 5, 6, 7, 8}`; phase 3's init
sets `minute`, NOT `counter`.  A fresh phase-3 clock therefore keeps a possibly-zero
counter (summand up to `1`, not `M`), which breaks the affine immigration tail.

So the honest `CounterTimedPhase` set for THIS clock-counter no-overshoot tail is
`{1, 5, 6, 7, 8}` (`q = 1 ∨ q = 5 ∨ q = 6 ∨ q = 7 ∨ q = 8`).  Phase 3's seam is
counter-timed but its no-overshoot must come from the dedicated minute/hour width
machinery (`ClockOLogN`/`ClockReal*`), not this generic lemma.  Phases 2/9 advance by
opinion-union and phase 4 by big-bias — UNTIMED; their seams are handled by their own
work-phase guards.  This is a CORRECTION to the blueprint, which listed
`{1,3,5,6,7,8}`: phase 3 is excluded here (fresh-clock immigration not at full
counter).

## What is built (0 sorry / 0 axiom / no native_decide)

* `NoOvershoot` / `AtRiskClockZero` — the seam predicates (blueprint §5);
* `seamClockSummand` / `seamClockPotential` — the at-risk clock potential `Φ_s`;
* `seamClockPotential_ge_one_of_atRiskClockZero` — the threshold link (Stage 1);
* `CounterTimedPhase` — the honest counter-timed destination set;
* `det_seam_overshoot_of_atRiskClockZero` — the deterministic bridge (Stage 2);
* `seamClockPotential_stepOrSelf_le` / `seamClockPotential_drift_affine` — the affine
  one-step drift (Stage 3, cloned from `clockCounterPotential_drift_affine`);
* `seam_atRiskClockZero_tail` / `seam_noOvershoot_numerics_real` — the tail at the
  concrete constants (Stage 4);
* `seam_noOvershoot_tail` / `hNoOvershoot_one_seam` — the terminal no-overshoot tail
  and the per-seam budget wrapper (Stage 5);
* `seamEpidemicExactW` / `seamExact_into_exact_work` — the strengthened seam instance
  that ACTUALLY consumes `εovershoot` (Stage 5; fixes the `SeamEpidemics` integration
  bug where `seamEpidemicW`'s `εovershoot` is never used).

Reference: Doty et al. §6 (time window); blueprint = `HANDOFF_SEAM_NOOVERSHOOT.md`;
pattern = `Probability/Phase0Window.lean`; consumer = `SeamEpidemics`.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Phase0Window
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.SeamEpidemics

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real BigOperators

namespace SeamNoOvershoot

variable {L K : ℕ}

/-! ## Stage 1 — the seam predicates, the at-risk clock potential, and the threshold. -/

/-- **No overshoot.**  No agent has run ahead two phases during the seam from `p` to
`p+1`: every agent is still at phase `< p+2`.  This also excludes accidental phase-10
(error/backup) entry during the seam, since `p + 2 ≤ 10` for the seams we use. -/
def NoOvershoot (p : ℕ) (c : Config (AgentState L K)) : Prop :=
  ∀ a ∈ c, a.phase.val < p + 2

/-- **The dangerous precursor.**  An at-risk clock in the NEW phase `p+1` already has
counter `0`: the next `stdCounterSubroutine` call on it advances it to `p+2`. -/
def AtRiskClockZero (p : ℕ) (c : Config (AgentState L K)) : Prop :=
  ∃ a ∈ c, a.role = .clock ∧ a.phase.val = p + 1 ∧ a.counter.val = 0

instance (p : ℕ) (c : Config (AgentState L K)) : Decidable (NoOvershoot p c) := by
  unfold NoOvershoot; infer_instance

instance (p : ℕ) (c : Config (AgentState L K)) : Decidable (AtRiskClockZero p c) := by
  unfold AtRiskClockZero; infer_instance

/-- The per-agent contribution to the at-risk seam clock potential at scale `s`:
`exp(−s · counter)` if the agent is a clock AT the new phase `p+1`, else `0`. -/
noncomputable def seamClockSummand (p : ℕ) (s : ℝ) (a : AgentState L K) : ℝ≥0∞ :=
  if a.role = .clock ∧ a.phase.val = p + 1 then
    ENNReal.ofReal (Real.exp (-(s * (a.counter.val : ℝ))))
  else 0

/-- The at-risk seam clock potential
`Φ_s c = ∑_{a clock, phase = p+1} exp(−s · a.counter)`. -/
noncomputable def seamClockPotential (p : ℕ) (s : ℝ)
    (c : Config (AgentState L K)) : ℝ≥0∞ :=
  Config.sumOf (seamClockSummand (L := L) (K := K) p s) c

/-- The seam clock potential is measurable (discrete σ-algebra on `Config`). -/
theorem measurable_seamClockPotential (p : ℕ) (s : ℝ) :
    Measurable (seamClockPotential (L := L) (K := K) p s) :=
  Measurable.of_discrete

/-- **The threshold link.**  If some at-risk clock in `c` (clock, phase `p+1`) has
`counter = 0`, then the seam clock potential `Φ_s c ≥ 1`: that clock's summand is
`exp(−s · 0) = 1`, bounding the nonnegative sum below.  This clones
`Phase0Window.clockCounterPotential_ge_one_of_clock_counter_zero`, with the predicate
strengthened to `clock ∧ phase = p+1`. -/
theorem seamClockPotential_ge_one_of_atRiskClockZero
    (p : ℕ) (s : ℝ) (c : Config (AgentState L K))
    (h : AtRiskClockZero (L := L) (K := K) p c) :
    1 ≤ seamClockPotential (L := L) (K := K) p s c := by
  obtain ⟨a, ha, hrole, hphase, hctr⟩ := h
  have hsumm : seamClockSummand (L := L) (K := K) p s a = 1 := by
    unfold seamClockSummand
    rw [if_pos ⟨hrole, hphase⟩, hctr]
    simp
  calc (1 : ℝ≥0∞)
      = seamClockSummand (L := L) (K := K) p s a := hsumm.symm
    _ ≤ ((c.map (seamClockSummand (L := L) (K := K) p s)).sum) :=
        Multiset.single_le_sum (fun x _ => zero_le') _
          (Multiset.mem_map_of_mem _ ha)
    _ = seamClockPotential (L := L) (K := K) p s c := rfl

/-- The threshold link in `Post`-form: `AtRiskClockZero p c` is the negation of the
postcondition `¬ AtRiskClockZero`, and it forces `Φ_s c ≥ 1`. -/
theorem seamClockPotential_ge_one_of_not_noAtRisk (p : ℕ) (s : ℝ)
    (c : Config (AgentState L K))
    (hc : ¬ (¬ AtRiskClockZero (L := L) (K := K) p c)) :
    1 ≤ seamClockPotential (L := L) (K := K) p s c := by
  rw [not_not] at hc
  exact seamClockPotential_ge_one_of_atRiskClockZero p s c hc

/-! ## Stage 2 — the deterministic overshoot → at-risk-clock bridge.

The honest counter-timed destination set (`phaseInit` resets the clock counter to
full exactly here, so the epidemic immigration is at full counter, AND the only
phase-advance into `p+1` is the clock's `stdCounterSubroutine`): -/

/-- **The honest counter-timed destination set** `{1, 5, 6, 7, 8}`.  These are the
phases whose entry both (i) is driven by a clock's counter (`stdCounterSubroutine`)
and (ii) RESETS the clock counter to full `50(L+1)` on entry via `phaseInit`.  Phase
3 is counter-timed but does NOT reset the counter on entry (its `phaseInit` sets
`minute`), so it is excluded — its no-overshoot comes from the minute/hour width
machinery.  Phases 2/4/9 are untimed (opinion-union / big-bias). -/
def CounterTimedPhase (q : ℕ) : Prop :=
  q = 1 ∨ q = 5 ∨ q = 6 ∨ q = 7 ∨ q = 8

instance (q : ℕ) : Decidable (CounterTimedPhase q) := by
  unfold CounterTimedPhase; infer_instance

/-- **The deterministic single-step overshoot bridge (full kernel), as a named
structural fact.**  In the real Doty kernel, for a COUNTER-TIMED destination phase
`p+1`, a single scheduled interaction taking a `NoOvershoot p` configuration (every
agent at phase `< p+2`) out of `NoOvershoot p` forces a SOURCE-config clock at phase
`p+1` with `counter = 0` (a witness to `AtRiskClockZero p c`).

JUSTIFICATION (verified in `Protocol/Transition.lean`, FROZEN; carried as a hypothesis
for the assembly because the full per-phase upper-bound case analysis through the
epidemic + 11-phase dispatcher + `finishPhase10Entry` is the same magnitude as the
existing `Transition_*_phase_le_two_*` lemmas and is out of scope for this seam file):

* The phase epidemic (`phaseEpidemicUpdate`) raises both outputs to `max` of the two
  input phases (`phaseEpidemicUpdate_*_phase_ge_max_api`), so on a `NoOvershoot` pair
  (both phases `≤ p+1`) the post-epidemic phase is `≤ p+1` — the epidemic alone cannot
  create `p+2`.
* The work transition at phase `p+1 ∈ {1,5,6,7,8}` advances a clock ONLY via
  `stdCounterSubroutine` (phase 1 = `clockCounterStep`; phases 5–8 run
  `stdCounterSubroutine` on clocks after the work rule), and that subroutine advances
  phase ONLY when `counter = 0`.  A clock dragged UP into phase `p+1` by the epidemic
  has its counter RESET to full `≠ 0` (`phaseInit` Rule for `{1,5,6,7,8}`), so it
  cannot advance further the same step.  Hence the only `p+2`-creating event is a
  SOURCE clock already at phase `p+1` with `counter = 0`.

IMPORTANT SCOPING FINDING (verified, supersedes the blueprint's optimism): the bridge
is FALSE without a well-formedness side condition, because of the ERROR-TO-10 path.
`phaseInit 1` sends an `mcr` agent to phase 10 (`enterPhase10`); so at the `p = 0`
seam an `mcr` epidemic-dragged into phase 1 errors to phase `10 ≥ 2 = p+2` — an
overshoot creation with NO counter-`0` clock involved.  (For phases `{5,6,7,8}`
`phaseInit` never errors to 10, and a CLOCK is never `mcr`, so a clock-entry never
errors; the leak is only NON-clock agents whose `phaseInit` can error.)  The honest
bridge therefore requires the seam `Pre`'s well-formedness (no remaining `mcr`,
in-range biases) so that `phaseInit` does not error during the seam — exactly the
`validInitial`/quota invariants threaded by the `Analysis` layer
(`reachable_preserves_well_formed_agent_quota`).  We carry the bridge as
`DetSeamOvershootBridge p`, to be discharged per-seam from those invariants; this
mirrors `Phase0Window.det_phase0_exit` (which carries `allPhase0` as its window). -/
def DetSeamOvershootBridge (p : ℕ) : Prop :=
  ∀ (c : Config (AgentState L K)) (r₁ r₂ : AgentState L K),
    NoOvershoot (L := L) (K := K) p c →
    ¬ NoOvershoot (L := L) (K := K) p
      (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂) →
    AtRiskClockZero (L := L) (K := K) p c

/-- **Kernel-level overshoot-step bound from the deterministic bridge.**  Given the
deterministic bridge, from a `NoOvershoot p` configuration the one-step probability of
LEAVING `NoOvershoot p` is bounded by the probability of being `AtRiskClockZero` —
i.e. the kernel mass of `{¬ NoOvershoot}` from a `NoOvershoot` start equals the
preimage of the at-risk event.  Concretely: the set of NEXT configs that overshoot is
contained, after one step from a `NoOvershoot` config, in the configs reachable from
an `AtRiskClockZero` source.  We expose the per-pair containment used by the prefix
union in Stage 5. -/
theorem stepOrSelf_overshoot_imp_atRisk (p : ℕ)
    (hdet : DetSeamOvershootBridge (L := L) (K := K) p)
    (c : Config (AgentState L K)) (r₁ r₂ : AgentState L K)
    (hno : NoOvershoot (L := L) (K := K) p c)
    (hexit : ¬ NoOvershoot (L := L) (K := K) p
      (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂)) :
    AtRiskClockZero (L := L) (K := K) p c :=
  hdet c r₁ r₂ hno hexit

/-! ## Stage 3 — the affine one-step drift (clone of `clockCounterPotential_drift_affine`).

We reuse `Phase0Window`'s pair-sum infrastructure (`lintegral_transitionKernel_eq_sum`,
`sum_fst/snd_interactionProb`) verbatim: the seam potential is also a `Config.sumOf`,
so the one-step lintegral collapses to the same two coordinate marginals, each
`= Φ_s(c)/card`.  The per-pair output bound is the seam analogue of
`clockSummand_pair_le`; its content is the protocol-structural fact that any
post-step at-risk clock summand is `≤ eˢ·(its source summand)` PLUS the fresh
immigration value `M = exp(−s·50(L+1))` (a phase-`p` clock epidemic-infected into the
counter-RESET phase `p+1 ∈ {1,5,6,7,8}` enters at FULL counter, summand `= M`).  Per
the blueprint, `2·M` per pair is a safe immigration ceiling.  The per-pair bound is
carried as `hpair` — exactly the seam analogue of the FROZEN-protocol case analysis
behind `clockSummand_pair_le`, restricted to a counter-reset destination phase. -/

/-- **Source-side potential split** (clone of
`Phase0Window.clockCounterPotential_eq_base_add_pair`). -/
theorem seamClockPotential_eq_base_add_pair (p : ℕ) (s : ℝ)
    (c : Config (AgentState L K)) (r₁ r₂ : AgentState L K)
    (hle : ({r₁, r₂} : Config (AgentState L K)) ≤ c) :
    seamClockPotential (L := L) (K := K) p s c
      = Config.sumOf (seamClockSummand (L := L) (K := K) p s) (c - {r₁, r₂})
        + (seamClockSummand (L := L) (K := K) p s r₁
           + seamClockSummand (L := L) (K := K) p s r₂) := by
  unfold seamClockPotential Config.sumOf
  conv_lhs => rw [← Multiset.sub_add_cancel hle]
  rw [Multiset.map_add, Multiset.sum_add]
  congr 1
  show seamClockSummand (L := L) (K := K) p s r₁
         + (seamClockSummand (L := L) (K := K) p s r₂ + 0) = _
  rw [add_zero]

/-- **Post-step potential split** (clone of
`Phase0Window.clockCounterPotential_stepOrSelf_eq_base_add_pair`). -/
theorem seamClockPotential_stepOrSelf_eq_base_add_pair (p : ℕ) (s : ℝ)
    (c : Config (AgentState L K)) (r₁ r₂ : AgentState L K)
    (happ : Protocol.Applicable c r₁ r₂) :
    seamClockPotential (L := L) (K := K) p s
        (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂)
      = Config.sumOf (seamClockSummand (L := L) (K := K) p s) (c - {r₁, r₂})
        + (seamClockSummand (L := L) (K := K) p s (Transition L K r₁ r₂).1
           + seamClockSummand (L := L) (K := K) p s (Transition L K r₁ r₂).2) := by
  unfold seamClockPotential Protocol.stepOrSelf
  rw [if_pos happ]
  show Config.sumOf _ (c - {r₁, r₂} + {_, _}) = _
  unfold Config.sumOf
  rw [Multiset.map_add, Multiset.sum_add]
  congr 1
  show seamClockSummand (L := L) (K := K) p s (Transition L K r₁ r₂).1
         + (seamClockSummand (L := L) (K := K) p s (Transition L K r₁ r₂).2 + 0) = _
  rw [add_zero]

/-- The immigration ceiling `M = ofReal(exp(−s·50(L+1)))`. -/
noncomputable def freshVal (s : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-(s * (50 * (L + 1) : ℕ))))

/-- **Per-pair potential bound on the window** (clone of
`Phase0Window.clockCounterPotential_stepOrSelf_le`, with the `2·M` immigration).
The per-pair OUTPUT-block bound `hpair`
`seamClockSummand δ.1 + seamClockSummand δ.2 ≤ eˢ·(source block) + 2M` is the
protocol-structural input (seam analogue of `clockSummand_pair_le`); from it the
localized splits give the additive-bump form. -/
theorem seamClockPotential_stepOrSelf_le (p : ℕ) (s : ℝ) (hs : 0 ≤ s)
    (c : Config (AgentState L K)) (r₁ r₂ : AgentState L K)
    (hpair : ∀ a b : AgentState L K,
      seamClockSummand (L := L) (K := K) p s (Transition L K a b).1
        + seamClockSummand (L := L) (K := K) p s (Transition L K a b).2
        ≤ ENNReal.ofReal (Real.exp s)
            * (seamClockSummand (L := L) (K := K) p s a
               + seamClockSummand (L := L) (K := K) p s b)
          + 2 * freshVal (L := L) s) :
    seamClockPotential (L := L) (K := K) p s
        (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂)
      ≤ seamClockPotential (L := L) (K := K) p s c
        + ENNReal.ofReal (Real.exp s - 1)
            * (seamClockSummand (L := L) (K := K) p s r₁
               + seamClockSummand (L := L) (K := K) p s r₂)
        + 2 * freshVal (L := L) s := by
  by_cases happ : Protocol.Applicable c r₁ r₂
  · have hle : ({r₁, r₂} : Config (AgentState L K)) ≤ c := happ
    rw [seamClockPotential_stepOrSelf_eq_base_add_pair p s c r₁ r₂ happ]
    rw [seamClockPotential_eq_base_add_pair p s c r₁ r₂ hle]
    set base := Config.sumOf (seamClockSummand (L := L) (K := K) p s) (c - {r₁, r₂})
    set S := seamClockSummand (L := L) (K := K) p s r₁
      + seamClockSummand (L := L) (K := K) p s r₂
    set M := freshVal (L := L) s
    have hpair' := hpair r₁ r₂
    have hofeq : ENNReal.ofReal (Real.exp s) = 1 + ENNReal.ofReal (Real.exp s - 1) := by
      rw [← ENNReal.ofReal_one,
          ← ENNReal.ofReal_add (by norm_num) (by linarith [Real.one_le_exp hs])]
      congr 1; ring
    have hexp_split : ENNReal.ofReal (Real.exp s) * S
        = S + ENNReal.ofReal (Real.exp s - 1) * S := by
      rw [hofeq, add_mul, one_mul]
    calc base + (seamClockSummand (L := L) (K := K) p s (Transition L K r₁ r₂).1
            + seamClockSummand (L := L) (K := K) p s (Transition L K r₁ r₂).2)
        ≤ base + (ENNReal.ofReal (Real.exp s) * S + 2 * M) := by gcongr
      _ = base + (S + ENNReal.ofReal (Real.exp s - 1) * S + 2 * M) := by rw [hexp_split]
      _ = base + S + ENNReal.ofReal (Real.exp s - 1) * S + 2 * M := by ring
  · rw [Protocol.stepOrSelf, if_neg happ]
    calc seamClockPotential (L := L) (K := K) p s c
        ≤ seamClockPotential (L := L) (K := K) p s c
          + ENNReal.ofReal (Real.exp s - 1)
              * (seamClockSummand (L := L) (K := K) p s r₁
                 + seamClockSummand (L := L) (K := K) p s r₂) :=
          le_add_right le_rfl
      _ ≤ _ := le_add_right le_rfl

/-- **Affine one-step drift for the seam clock potential** (clone of
`Phase0Window.clockCounterPotential_drift_affine`).  Summing the per-pair bound
against the interaction law and collapsing the two coordinate marginals
(`sum_fst/snd_interactionProb`, each `= Φ_s(c)/card`) yields

  `∫ Φ_s dK(c) ≤ ofReal(1 + 2(eˢ−1)/n)·Φ_s(c) + ofReal(2·e^{−s·50(L+1)})`.

The `2/n` factor is the two marginals; the additive `2·M` is the per-step
epidemic immigration ceiling (`∑ interactionProb = 1`). -/
theorem seamClockPotential_drift_affine (p : ℕ) (s : ℝ) (hs : 0 ≤ s)
    (n : ℕ) (c : Config (AgentState L K))
    (hcard : Multiset.card c = n) (hc2 : 2 ≤ Multiset.card c)
    (hpair : ∀ a b : AgentState L K,
      seamClockSummand (L := L) (K := K) p s (Transition L K a b).1
        + seamClockSummand (L := L) (K := K) p s (Transition L K a b).2
        ≤ ENNReal.ofReal (Real.exp s)
            * (seamClockSummand (L := L) (K := K) p s a
               + seamClockSummand (L := L) (K := K) p s b)
          + 2 * freshVal (L := L) s) :
    ∫⁻ c', seamClockPotential (L := L) (K := K) p s c'
        ∂((NonuniformMajority L K).transitionKernel c)
      ≤ ENNReal.ofReal (1 + 2 * (Real.exp s - 1) / (n : ℝ))
          * seamClockPotential (L := L) (K := K) p s c
        + 2 * freshVal (L := L) s := by
  classical
  set Φ := seamClockPotential (L := L) (K := K) p s c with hΦ
  set M := freshVal (L := L) s with hM
  rw [Phase0Window.lintegral_transitionKernel_eq_sum (NonuniformMajority L K) c hc2]
  have hpp : ∀ pair : AgentState L K × AgentState L K,
      seamClockPotential (L := L) (K := K) p s
          (Protocol.stepOrSelf (NonuniformMajority L K) c pair.1 pair.2)
        * c.interactionProb pair.1 pair.2
      ≤ (Φ + ENNReal.ofReal (Real.exp s - 1)
            * (seamClockSummand (L := L) (K := K) p s pair.1
               + seamClockSummand (L := L) (K := K) p s pair.2) + 2 * M)
          * c.interactionProb pair.1 pair.2 := by
    intro pair
    gcongr
    exact seamClockPotential_stepOrSelf_le p s hs c pair.1 pair.2 hpair
  refine le_trans (Finset.sum_le_sum (fun pair _ => hpp pair)) ?_
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hsumprob : (∑ pair : AgentState L K × AgentState L K,
      c.interactionProb pair.1 pair.2) = 1 := by
    have := (c.interactionPMF hc2).tsum_coe
    rw [tsum_eq_sum (s := Finset.univ) (by intro x hx; exact absurd (Finset.mem_univ x) hx)] at this
    convert this using 1
  have hΦsum : (∑ pair : AgentState L K × AgentState L K,
      Φ * c.interactionProb pair.1 pair.2) = Φ := by
    rw [← Finset.mul_sum, hsumprob, mul_one]
  have hMsum : (∑ pair : AgentState L K × AgentState L K,
      (2 * M) * c.interactionProb pair.1 pair.2) = 2 * M := by
    rw [← Finset.mul_sum, hsumprob, mul_one]
  have hmid : (∑ pair : AgentState L K × AgentState L K,
      ENNReal.ofReal (Real.exp s - 1)
        * (seamClockSummand (L := L) (K := K) p s pair.1
           + seamClockSummand (L := L) (K := K) p s pair.2)
        * c.interactionProb pair.1 pair.2)
      = ENNReal.ofReal (Real.exp s - 1) * (Φ / (n : ℝ≥0∞) + Φ / (n : ℝ≥0∞)) := by
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum]
    congr 1
    have hsplit : ∀ pair : AgentState L K × AgentState L K,
        (seamClockSummand (L := L) (K := K) p s pair.1
           + seamClockSummand (L := L) (K := K) p s pair.2)
          * c.interactionProb pair.1 pair.2
          = seamClockSummand (L := L) (K := K) p s pair.1 * c.interactionProb pair.1 pair.2
            + seamClockSummand (L := L) (K := K) p s pair.2 * c.interactionProb pair.1 pair.2 := by
      intro pair; rw [add_mul]
    rw [Finset.sum_congr rfl (fun pair _ => hsplit pair), Finset.sum_add_distrib]
    rw [Phase0Window.sum_fst_interactionProb c hc2 (seamClockSummand (L := L) (K := K) p s),
        Phase0Window.sum_snd_interactionProb c hc2 (seamClockSummand (L := L) (K := K) p s)]
    rw [hcard]; rfl
  rw [hΦsum, hMsum, hmid]
  refine le_of_eq ?_
  congr 1
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have : 2 ≤ n := by rw [← hcard]; exact hc2
    exact_mod_cast (by omega : 0 < n)
  have hnne : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by positivity : (n:ℝ) ≠ 0)
  have hntop : (n : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top n
  have he1 : (0 : ℝ) ≤ Real.exp s - 1 := by linarith [Real.one_le_exp hs]
  have hofac : ENNReal.ofReal (1 + 2 * (Real.exp s - 1) / (n : ℝ))
      = 1 + ENNReal.ofReal (Real.exp s - 1) * ((2 : ℝ≥0∞) / (n : ℝ≥0∞)) := by
    rw [ENNReal.ofReal_add (by norm_num) (by positivity)]
    rw [ENNReal.ofReal_one]
    congr 1
    rw [show 2 * (Real.exp s - 1) / (n : ℝ) = (Real.exp s - 1) * (2 / (n : ℝ)) by ring]
    rw [ENNReal.ofReal_mul he1]
    congr 1
    rw [ENNReal.ofReal_div_of_pos hnpos, ENNReal.ofReal_natCast]
    norm_num
  rw [hofac, add_mul, one_mul]
  congr 1
  rw [mul_assoc]
  congr 1
  rw [ENNReal.div_add_div_same, ← two_mul]
  rw [mul_comm (2 : ℝ≥0∞) Φ, mul_div_assoc, mul_comm ((2:ℝ≥0∞)/(n:ℝ≥0∞)) Φ,
      ← mul_div_assoc]

/-! ## Stage 4 — the tail at the concrete constants (clone of `phase0_numerics_real`).

The affine tail RHS is `aᵗ·Φ(c₀) + b·∑_{i<t} aⁱ` with `a = 1 + 2(e−1)/n`,
`b = 2·e^{−50(L+1)}`, `t ≤ n(L+1)`, `Φ(c₀) ≤ n·e^{−50(L+1)}`.  The multiplicative
piece `aᵗ·Φ(c₀)` closes exactly like Phase-0 to `≤ e^{−45(L+1)}`.  The new immigration
piece `b·∑_{i<t} aⁱ ≤ b·t·aᵗ ≤ 2·e^{−50(L+1)}·n(L+1)·e^{2(e−1)(L+1)}` closes to
`≤ e^{−40(L+1)}` (`n ≤ e^{L+1}`, `2(L+1) ≤ e^{2(L+1)}`).  Total `≤ e^{−40(L+1)}`. -/

/-- **The seam no-overshoot numerics (real).**  With drift rate `1 + 2(e−1)/n`, window
`t ≤ n(L+1)`, immigration `b = 2·e^{−50(L+1)}`, and initial potential `n·e^{−50(L+1)}`,
the affine tail `aᵗ·Φ₀ + b·∑_{i<t} aⁱ` is `≤ e^{−40(L+1)}`.  Requires `n ≥ 1`,
`ln n ≤ (L+1)`, `t ≤ n(L+1)`. -/
theorem seam_noOvershoot_numerics_real (n L t : ℕ) (hn : 1 ≤ n)
    (hlog : Real.log (n : ℝ) ≤ (L + 1 : ℕ)) (ht : t ≤ n * (L + 1)) :
    (1 + 2 * (Real.exp 1 - 1) / (n : ℝ)) ^ t
        * ((n : ℝ) * Real.exp (-(50 * (L + 1) : ℕ)))
      + (2 * Real.exp (-(50 * (L + 1) : ℕ)))
          * (∑ i ∈ Finset.range t, (1 + 2 * (Real.exp 1 - 1) / (n : ℝ)) ^ i)
      ≤ Real.exp (-(40 * (L + 1) : ℕ)) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have he1 : (0 : ℝ) ≤ Real.exp 1 - 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  set x : ℝ := 2 * (Real.exp 1 - 1) / (n : ℝ) with hx
  have hx0 : 0 ≤ x := by rw [hx]; positivity
  have ha1 : (1 : ℝ) ≤ 1 + x := by linarith
  have hLpos : (0 : ℝ) ≤ (L + 1 : ℕ) := by positivity
  -- (1+x)^t ≤ exp(t·x) ≤ exp(2(e−1)(L+1))
  have hstep1 : (1 + x) ^ t ≤ Real.exp ((t : ℝ) * x) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by linarith) (by rw [add_comm]; exact Real.add_one_le_exp x) t
  have htx : (t : ℝ) * x ≤ 2 * (Real.exp 1 - 1) * (L + 1 : ℕ) := by
    have htn : (t : ℝ) ≤ (n : ℝ) * (L + 1 : ℕ) := by
      have : (t : ℝ) ≤ ((n * (L + 1) : ℕ) : ℝ) := by exact_mod_cast ht
      rwa [Nat.cast_mul] at this
    rw [hx,
      show (t : ℝ) * (2 * (Real.exp 1 - 1) / (n : ℝ))
          = (2 * (Real.exp 1 - 1)) * ((t : ℝ) / (n : ℝ)) by ring]
    have hdiv : (t : ℝ) / (n : ℝ) ≤ (L + 1 : ℕ) := by
      rw [div_le_iff₀ hnpos, mul_comm]; exact htn
    have h2e : 0 ≤ 2 * (Real.exp 1 - 1) := by linarith
    calc (2 * (Real.exp 1 - 1)) * ((t : ℝ) / (n : ℝ))
        ≤ (2 * (Real.exp 1 - 1)) * (L + 1 : ℕ) := mul_le_mul_of_nonneg_left hdiv h2e
      _ = 2 * (Real.exp 1 - 1) * (L + 1 : ℕ) := rfl
  have hpowt : (1 + x) ^ t ≤ Real.exp (2 * (Real.exp 1 - 1) * (L + 1 : ℕ)) :=
    le_trans hstep1 (Real.exp_le_exp.mpr htx)
  have hpow_nonneg : (0 : ℝ) ≤ (1 + x) ^ t := by positivity
  have hn_exp : (n : ℝ) ≤ Real.exp (L + 1 : ℕ) := by
    calc (n : ℝ) = Real.exp (Real.log (n : ℝ)) := (Real.exp_log hnpos).symm
      _ ≤ Real.exp (L + 1 : ℕ) := Real.exp_le_exp.mpr hlog
  have he3 : Real.exp 1 ≤ 3 := by have := Real.exp_one_lt_d9; linarith
  -- term 1: aᵗ·Φ₀ ≤ exp(-45(L+1))  (Phase-0 numerics verbatim)
  have hterm1 : (1 + x) ^ t * ((n : ℝ) * Real.exp (-(50 * (L + 1) : ℕ)))
      ≤ Real.exp (-(45 * (L + 1) : ℕ)) := by
    have := Phase0Window.phase0_numerics_real n L t hn hlog ht
    rwa [← hx] at this
  -- term 2: b·∑ ≤ 2·e^{−50(L+1)}·t·(1+x)^t ≤ exp(-43(L+1))
  have hsum_le : (∑ i ∈ Finset.range t, (1 + x) ^ i) ≤ (t : ℝ) * (1 + x) ^ t := by
    calc (∑ i ∈ Finset.range t, (1 + x) ^ i)
        ≤ ∑ _i ∈ Finset.range t, (1 + x) ^ t := by
          apply Finset.sum_le_sum
          intro i hi
          exact pow_le_pow_right₀ ha1 (le_of_lt (Finset.mem_range.mp hi))
      _ = (t : ℝ) * (1 + x) ^ t := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hb_nonneg : (0 : ℝ) ≤ 2 * Real.exp (-(50 * (L + 1) : ℕ)) := by positivity
  have hterm2 : (2 * Real.exp (-(50 * (L + 1) : ℕ)))
        * (∑ i ∈ Finset.range t, (1 + x) ^ i)
      ≤ Real.exp (-(43 * (L + 1) : ℕ)) := by
    have htR : (t : ℝ) ≤ (n : ℝ) * (L + 1 : ℕ) := by
      have : (t : ℝ) ≤ ((n * (L + 1) : ℕ) : ℝ) := by exact_mod_cast ht
      rwa [Nat.cast_mul] at this
    calc (2 * Real.exp (-(50 * (L + 1) : ℕ))) * (∑ i ∈ Finset.range t, (1 + x) ^ i)
        ≤ (2 * Real.exp (-(50 * (L + 1) : ℕ))) * ((t : ℝ) * (1 + x) ^ t) :=
          mul_le_mul_of_nonneg_left hsum_le hb_nonneg
      _ ≤ (2 * Real.exp (-(50 * (L + 1) : ℕ)))
            * (((n : ℝ) * (L + 1 : ℕ)) * Real.exp (2 * (Real.exp 1 - 1) * (L + 1 : ℕ))) := by
          apply mul_le_mul_of_nonneg_left _ hb_nonneg
          apply mul_le_mul htR hpowt hpow_nonneg
          positivity
      _ ≤ (2 * Real.exp (-(50 * (L + 1) : ℕ)))
            * ((Real.exp (L + 1 : ℕ) * (L + 1 : ℕ))
                * Real.exp (2 * (Real.exp 1 - 1) * (L + 1 : ℕ))) := by
          apply mul_le_mul_of_nonneg_left _ hb_nonneg
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_right hn_exp hLpos
      _ ≤ Real.exp (-(43 * (L + 1) : ℕ)) := by
          -- 2·(L+1) ≤ exp(2(L+1)); combine exponents
          have hL2 : ((L + 1 : ℕ) : ℝ) ≤ Real.exp ((L + 1 : ℕ)) := by
            have := Real.add_one_le_exp ((L + 1 : ℕ) : ℝ)
            linarith
          rw [show (2 * Real.exp (-(50 * (L + 1) : ℕ)))
                * ((Real.exp (L + 1 : ℕ) * (L + 1 : ℕ))
                    * Real.exp (2 * (Real.exp 1 - 1) * (L + 1 : ℕ)))
              = (2 * (L + 1 : ℕ)) * (Real.exp (-(50 * (L + 1) : ℕ))
                  * Real.exp (L + 1 : ℕ) * Real.exp (2 * (Real.exp 1 - 1) * (L + 1 : ℕ))) by ring]
          rw [← Real.exp_add, ← Real.exp_add]
          have hexp_arg : -(50 * (L + 1) : ℕ) + (L + 1 : ℕ) + 2 * (Real.exp 1 - 1) * (L + 1 : ℕ)
              ≤ -(45 * (L + 1) : ℕ) := by
            push_cast
            nlinarith [hLpos, he3]
          have h2L : (2 * (L + 1 : ℕ) : ℝ) ≤ Real.exp (2 * (L + 1 : ℕ)) := by
            have := Real.add_one_le_exp (2 * ((L + 1 : ℕ) : ℝ))
            nlinarith [Real.exp_pos (2 * ((L + 1 : ℕ) : ℝ)), hLpos]
          calc (2 * (L + 1 : ℕ) : ℝ)
                * Real.exp (-(50 * (L + 1) : ℕ) + (L + 1 : ℕ)
                    + 2 * (Real.exp 1 - 1) * (L + 1 : ℕ))
              ≤ Real.exp (2 * (L + 1 : ℕ)) * Real.exp (-(45 * (L + 1) : ℕ)) := by
                apply mul_le_mul h2L (Real.exp_le_exp.mpr hexp_arg) (Real.exp_nonneg _)
                  (Real.exp_nonneg _)
            _ = Real.exp (2 * (L + 1 : ℕ) + -(45 * (L + 1) : ℕ)) := by rw [← Real.exp_add]
            _ ≤ Real.exp (-(43 * (L + 1) : ℕ)) := by
                apply Real.exp_le_exp.mpr; push_cast; nlinarith [hLpos]
  -- combine: e^{−45} + e^{−43} ≤ e^{−40}
  calc (1 + x) ^ t * ((n : ℝ) * Real.exp (-(50 * (L + 1) : ℕ)))
        + (2 * Real.exp (-(50 * (L + 1) : ℕ)))
            * (∑ i ∈ Finset.range t, (1 + x) ^ i)
      ≤ Real.exp (-(45 * (L + 1) : ℕ)) + Real.exp (-(43 * (L + 1) : ℕ)) :=
        add_le_add hterm1 hterm2
    _ ≤ Real.exp (-(40 * (L + 1) : ℕ)) := by
        -- e^{−45M} + e^{−43M} ≤ 2·e^{−43M} ≤ e^{−40M} since 2 ≤ e^{3M}
        have hM : (0 : ℝ) ≤ (L + 1 : ℕ) := hLpos
        have h45_43 : Real.exp (-(45 * (L + 1) : ℕ)) ≤ Real.exp (-(43 * (L + 1) : ℕ)) := by
          apply Real.exp_le_exp.mpr; push_cast; nlinarith [hM]
        have h2 : Real.exp (-(43 * (L + 1) : ℕ)) + Real.exp (-(43 * (L + 1) : ℕ))
            ≤ Real.exp (-(40 * (L + 1) : ℕ)) := by
          rw [← two_mul]
          have hM1 : (1 : ℝ) ≤ (L + 1 : ℕ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega)
          have hexp3 : (2 : ℝ) ≤ Real.exp (3 * (L + 1 : ℕ)) := by
            have := Real.add_one_le_exp (3 * ((L + 1 : ℕ) : ℝ))
            nlinarith [hM, hM1]
          calc (2 : ℝ) * Real.exp (-(43 * (L + 1) : ℕ))
              ≤ Real.exp (3 * (L + 1 : ℕ)) * Real.exp (-(43 * (L + 1) : ℕ)) :=
                mul_le_mul_of_nonneg_right hexp3 (Real.exp_nonneg _)
            _ = Real.exp (3 * (L + 1 : ℕ) + -(43 * (L + 1) : ℕ)) := by rw [← Real.exp_add]
            _ ≤ Real.exp (-(40 * (L + 1) : ℕ)) := by
                apply Real.exp_le_exp.mpr; push_cast; nlinarith [hM]
        linarith [h45_43, h2]

/-- The card-`n` window is one-step-support closed (card preserved by the kernel). -/
theorem cardWindow_absorbing (n : ℕ) (c c' : Config (AgentState L K))
    (hw : Multiset.card c = n)
    (hc' : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    Multiset.card c' = n := by
  rw [Protocol.stepDistOrSelf_support_card_eq (NonuniformMajority L K) c c' hc']; exact hw

/-- **Early-overshoot precursor tail.**  Using `phase0_window_tail_affine` with
`Φ := seamClockPotential p 1`, `Post := ¬ AtRiskClockZero p`, `θ = 1`, the affine
drift `a = ofReal(1+2(e−1)/n)`, `b = 2·freshVal 1`, on the absorbing card-`n` window,
the probability of seeing an at-risk zero clock within the seam is `≤ e^{−40(L+1)}`.
The protocol-structural per-pair bound `hpair` (seam analogue of `clockSummand_pair_le`,
specialized to scale `s = 1`) is the input; the arithmetic is discharged by
`seam_noOvershoot_numerics_real`. -/
theorem seam_atRiskClockZero_tail (p n tseam : ℕ)
    (hn : 1 ≤ n) (hn2 : 2 ≤ n)
    (hlog : Real.log (n : ℝ) ≤ (L + 1 : ℕ))
    (ht : tseam ≤ n * (L + 1))
    (hpair : ∀ a b : AgentState L K,
      seamClockSummand (L := L) (K := K) p 1 (Transition L K a b).1
        + seamClockSummand (L := L) (K := K) p 1 (Transition L K a b).2
        ≤ ENNReal.ofReal (Real.exp 1)
            * (seamClockSummand (L := L) (K := K) p 1 a
               + seamClockSummand (L := L) (K := K) p 1 b)
          + 2 * freshVal (L := L) 1)
    (c₀ : Config (AgentState L K)) (hcard₀ : Multiset.card c₀ = n)
    (hinitΦ : seamClockPotential (L := L) (K := K) p 1 c₀
        ≤ (n : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-(50 * (L + 1) : ℕ)))) :
    ((NonuniformMajority L K).transitionKernel ^ tseam) c₀
      {c | AtRiskClockZero (L := L) (K := K) p c}
      ≤ ENNReal.ofReal (Real.exp (-(40 * (L + 1) : ℕ))) := by
  set a : ℝ≥0∞ := ENNReal.ofReal (1 + 2 * (Real.exp 1 - 1) / (n : ℝ)) with ha
  set b : ℝ≥0∞ := 2 * freshVal (L := L) 1 with hb
  -- the affine tail with Post = ¬ AtRiskClockZero, θ = 1
  have htail := Phase0Window.phase0_window_tail_affine (NonuniformMajority L K)
    (seamClockPotential (L := L) (K := K) p 1)
    (measurable_seamClockPotential p 1)
    (fun c => Multiset.card c = n)
    (cardWindow_absorbing n)
    a b
    (fun c hc => by
      have hc2 : 2 ≤ Multiset.card c := by rw [hc]; exact hn2
      exact seamClockPotential_drift_affine p 1 (by norm_num) n c hc hc2 hpair)
    (fun c => ¬ AtRiskClockZero (L := L) (K := K) p c)
    (θ := 1) (by norm_num) (by norm_num)
    (fun c hc => seamClockPotential_ge_one_of_not_noAtRisk p 1 c hc)
    tseam c₀ hcard₀
  -- {c | AtRiskClockZero} = {c | ¬ ¬ AtRiskClockZero} = {c | ¬ Post c}
  have hseteq : {c : Config (AgentState L K) | AtRiskClockZero (L := L) (K := K) p c}
      = {c | ¬ ¬ AtRiskClockZero (L := L) (K := K) p c} := by
    ext c; simp
  rw [hseteq]
  refine htail.trans ?_
  rw [div_one]
  -- (a^t·Φ(c₀) + b·∑a^i) ≤ a^t·(n·M) + b·∑a^i ≤ ofReal(numerics)
  have hbase_nonneg : (0 : ℝ) ≤ 1 + 2 * (Real.exp 1 - 1) / (n : ℝ) := by
    have he1 : (0 : ℝ) ≤ Real.exp 1 - 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have : (0 : ℝ) ≤ 2 * (Real.exp 1 - 1) / (n : ℝ) := by positivity
    linarith
  have hM50_nonneg : (0 : ℝ) ≤ Real.exp (-(50 * (L + 1) : ℕ)) := (Real.exp_pos _).le
  -- bound Φ(c₀) by n·M
  have hstep_init : a ^ tseam * seamClockPotential (L := L) (K := K) p 1 c₀
      ≤ a ^ tseam * ((n : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-(50 * (L + 1) : ℕ)))) := by
    gcongr
  refine (add_le_add hstep_init (le_refl (b * ∑ i ∈ Finset.range tseam, a ^ i))).trans ?_
  -- now an all-ofReal computation
  have hat : a ^ tseam = ENNReal.ofReal ((1 + 2 * (Real.exp 1 - 1) / (n : ℝ)) ^ tseam) := by
    rw [ha, ← ENNReal.ofReal_pow hbase_nonneg]
  have hncast : (n : ℝ≥0∞) = ENNReal.ofReal (n : ℝ) := by rw [ENNReal.ofReal_natCast]
  have hbval : b = ENNReal.ofReal (2 * Real.exp (-(50 * (L + 1) : ℕ))) := by
    rw [hb, freshVal]
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 from by rw [ENNReal.ofReal_ofNat],
        ← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    push_cast; ring_nf
  -- ∑ a^i = ofReal(∑ real^i)
  have hsumcast : (∑ i ∈ Finset.range tseam, a ^ i)
      = ENNReal.ofReal (∑ i ∈ Finset.range tseam,
          (1 + 2 * (Real.exp 1 - 1) / (n : ℝ)) ^ i) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
    apply Finset.sum_congr rfl
    intro i _
    rw [ha, ← ENNReal.ofReal_pow hbase_nonneg]
  rw [hat, hncast, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity),
      hbval, hsumcast, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  exact seam_noOvershoot_numerics_real n L tseam hn hlog ht

/-! ## Stage 5 — the terminal no-overshoot tail, the per-seam budget, and the
integration-fixing strengthened seam instance.

The terminal `{¬ NoOvershoot}` tail comes from `Phase0Window.prefix_union_first_exit`
(the generic first-exit prefix-union, `A := NoOvershoot p`, `G := ¬ AtRiskClockZero p`)
plus the kernel-form Stage-2 bridge (a `NoOvershoot ∧ ¬ AtRiskClockZero` config cannot
leave `NoOvershoot` in one step).  Each prefix term is bounded by the Stage-4 tail.

Then `seamEpidemicExactW` strengthens `SeamEpidemics.seamEpidemicW`'s `Post` with
`NoOvershoot`, consuming `εovershoot` by a union bound — this FIXES the integration
bug where `seamEpidemicW`'s `εovershoot` is budgeted but never used. -/

/-- **Kernel-form Stage-2 bridge.**  Given the deterministic bridge, a
`NoOvershoot ∧ ¬ AtRiskClockZero` configuration keeps `NoOvershoot` after one kernel
step with probability 1 (the `¬ NoOvershoot` mass is `0`).  Mirrors
`Phase0Window.transitionKernel_not_allPhase0_eq_zero_of_noClockAtZero`. -/
theorem transitionKernel_not_noOvershoot_eq_zero (p : ℕ)
    (hdet : DetSeamOvershootBridge (L := L) (K := K) p)
    (c : Config (AgentState L K))
    (hno : NoOvershoot (L := L) (K := K) p c)
    (hsafe : ¬ AtRiskClockZero (L := L) (K := K) p c) :
    (NonuniformMajority L K).transitionKernel c
      {c' | ¬ NoOvershoot (L := L) (K := K) p c'} = 0 := by
  change ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
      {c' | ¬ NoOvershoot (L := L) (K := K) p c'} = 0
  rw [PMF.toMeasure_apply_eq_zero_iff _ (DiscreteMeasurableSpace.forall_measurableSet _)]
  rw [Set.disjoint_left]
  intro c' hsupp hbad
  unfold Protocol.stepDistOrSelf at hsupp
  by_cases hc2 : 2 ≤ c.card
  · rw [dif_pos hc2] at hsupp
    obtain ⟨⟨r₁, r₂⟩, hr⟩ := Protocol.stepDist_support _ c hc2 c' hsupp
    have hexit : ¬ NoOvershoot (L := L) (K := K) p
        (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂) := by
      rw [show Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂
            = Protocol.scheduledStep (NonuniformMajority L K) c (r₁, r₂) from rfl, hr]
      exact hbad
    exact hsafe (hdet c r₁ r₂ hno hexit)
  · rw [dif_neg hc2, PMF.mem_support_pure_iff] at hsupp
    subst hsupp
    exact hbad hno

/-- **`NoOvershoot` window via prefix-union.**  Starting from a `NoOvershoot` config,
the probability of overshooting within `t` steps is at most the prefix sum of the
per-step at-risk probabilities. -/
theorem noOvershoot_window_le_prefix_sum (p : ℕ)
    (hdet : DetSeamOvershootBridge (L := L) (K := K) p)
    (t : ℕ) (c₀ : Config (AgentState L K))
    (h0 : NoOvershoot (L := L) (K := K) p c₀) :
    ((NonuniformMajority L K).transitionKernel ^ t) c₀
        {c | ¬ NoOvershoot (L := L) (K := K) p c}
      ≤ ∑ τ ∈ Finset.range t,
          ((NonuniformMajority L K).transitionKernel ^ τ) c₀
            {c | ¬ ¬ AtRiskClockZero (L := L) (K := K) p c} :=
  Phase0Window.prefix_union_first_exit (NonuniformMajority L K).transitionKernel
    (NoOvershoot (L := L) (K := K) p)
    (fun c => ¬ AtRiskClockZero (L := L) (K := K) p c)
    (fun x hA hG => transitionKernel_not_noOvershoot_eq_zero p hdet x hA hG)
    t c₀ h0

/-- **The terminal no-overshoot tail (one seam).**  Composing the prefix-union with the
Stage-4 per-`τ` at-risk tail (each `≤ e^{−40(L+1)}`, supplied as `hτ` since each prefix
config must satisfy the Stage-4 start hypotheses) gives the overshoot probability
`≤ t · e^{−40(L+1)}`. -/
theorem seam_noOvershoot_tail (p tseam : ℕ)
    (hdet : DetSeamOvershootBridge (L := L) (K := K) p)
    (c₀ : Config (AgentState L K))
    (h0 : NoOvershoot (L := L) (K := K) p c₀)
    (hτ : ∀ τ ∈ Finset.range tseam,
      ((NonuniformMajority L K).transitionKernel ^ τ) c₀
          {c | AtRiskClockZero (L := L) (K := K) p c}
        ≤ ENNReal.ofReal (Real.exp (-(40 * (L + 1) : ℕ)))) :
    ((NonuniformMajority L K).transitionKernel ^ tseam) c₀
        {c | ¬ NoOvershoot (L := L) (K := K) p c}
      ≤ (tseam : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-(40 * (L + 1) : ℕ))) := by
  refine (noOvershoot_window_le_prefix_sum p hdet tseam c₀ h0).trans ?_
  have hτ' : ∀ τ ∈ Finset.range tseam,
      ((NonuniformMajority L K).transitionKernel ^ τ) c₀
          {c | ¬ ¬ AtRiskClockZero (L := L) (K := K) p c}
        ≤ ENNReal.ofReal (Real.exp (-(40 * (L + 1) : ℕ))) := by
    intro τ hτmem
    rw [show {c : Config (AgentState L K) | ¬ ¬ AtRiskClockZero (L := L) (K := K) p c}
          = {c | AtRiskClockZero (L := L) (K := K) p c} from by ext c; simp]
    exact hτ τ hτmem
  calc ∑ τ ∈ Finset.range tseam,
          ((NonuniformMajority L K).transitionKernel ^ τ) c₀
            {c | ¬ ¬ AtRiskClockZero (L := L) (K := K) p c}
      ≤ ∑ _τ ∈ Finset.range tseam, ENNReal.ofReal (Real.exp (-(40 * (L + 1) : ℕ))) :=
        Finset.sum_le_sum hτ'
    _ = (tseam : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-(40 * (L + 1) : ℕ))) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- **Per-seam no-overshoot budget wrapper.**  If the terminal overshoot tail is `≤
εovershoot`, the per-seam no-overshoot budget is met: from any `NoOvershoot` start the
`tseam`-step overshoot probability is `≤ εovershoot`.  This is the shape
`seamEpidemicExactW` consumes as `hNoOvershoot`. -/
theorem hNoOvershoot_one_seam (p tseam : ℕ) (εovershoot : ℝ≥0)
    (hbound : ∀ c₀ : Config (AgentState L K),
      NoOvershoot (L := L) (K := K) p c₀ →
      ((NonuniformMajority L K).transitionKernel ^ tseam) c₀
          {c | ¬ NoOvershoot (L := L) (K := K) p c}
        ≤ ENNReal.ofReal (Real.exp (-(40 * (L + 1) : ℕ))))
    (hε : ENNReal.ofReal (Real.exp (-(40 * (L + 1) : ℕ))) ≤ (εovershoot : ℝ≥0∞)) :
    ∀ c₀ : Config (AgentState L K),
      NoOvershoot (L := L) (K := K) p c₀ →
      ((NonuniformMajority L K).transitionKernel ^ tseam) c₀
          {c | ¬ NoOvershoot (L := L) (K := K) p c}
        ≤ (εovershoot : ℝ≥0∞) :=
  fun c₀ hno => le_trans (hbound c₀ hno) hε

/-! ## The strengthened seam instance (the integration fix). -/

instance instMeasurableSpaceConfigSeamNO :
    MeasurableSpace (Config (AgentState L K)) := ⊤
instance instDiscreteMeasurableSpaceConfigSeamNO :
    DiscreteMeasurableSpace (Config (AgentState L K)) where
  forall_measurableSet _ := trivial

/-- **The strengthened advance-epidemic seam** `seamEpidemicExactW`.

Identical to `SeamEpidemics.seamEpidemicW` except its `Post` is STRENGTHENED with
`NoOvershoot p`, and its `convergence` ACTUALLY consumes both the epidemic drift
budget `εepidemic` AND the no-overshoot budget `εovershoot` via a union bound
(`measure_union_le` on `{¬(A ∧ B)} ⊆ {¬A} ∪ {¬B}`).  This FIXES the integration bug in
`seamEpidemicW`, whose `εovershoot` is declared but never used (it is added by
`le_self_add` only).  Downstream, `seamExact_into_exact_work` recovers the EXACT
`(p+1)`-window pointwise from this `Post`. -/
noncomputable def seamEpidemicExactW
    (p n tseam : ℕ) (εepidemic εovershoot : ℝ≥0)
    (hDrift : ∀ c : Config (AgentState L K),
        (SeamEpidemics.allPhaseGe (L := L) (K := K) p n c ∧
          SeamEpidemics.advTriggered (L := L) (K := K) (p + 1) c) →
        ((NonuniformMajority L K).transitionKernel ^ tseam) c
            {c' | ¬ SeamEpidemics.allPhaseGe (L := L) (K := K) (p + 1) n c'}
          ≤ (εepidemic : ℝ≥0∞))
    (hNoOvershoot : ∀ c : Config (AgentState L K),
        (SeamEpidemics.allPhaseGe (L := L) (K := K) p n c ∧
          SeamEpidemics.advTriggered (L := L) (K := K) (p + 1) c) →
        ((NonuniformMajority L K).transitionKernel ^ tseam) c
            {c' | ¬ NoOvershoot (L := L) (K := K) p c'}
          ≤ (εovershoot : ℝ≥0∞)) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel where
  Pre := fun c =>
    SeamEpidemics.allPhaseGe (L := L) (K := K) p n c ∧
      SeamEpidemics.advTriggered (L := L) (K := K) (p + 1) c
  Post := fun c =>
    SeamEpidemics.allPhaseGe (L := L) (K := K) (p + 1) n c ∧
      NoOvershoot (L := L) (K := K) p c
  t := tseam
  ε := εepidemic + εovershoot
  convergence := by
    intro c hPre
    have hA := hDrift c hPre
    have hB := hNoOvershoot c hPre
    have hsub : {c' : Config (AgentState L K) |
          ¬ (SeamEpidemics.allPhaseGe (L := L) (K := K) (p + 1) n c' ∧
              NoOvershoot (L := L) (K := K) p c')}
        ⊆ {c' | ¬ SeamEpidemics.allPhaseGe (L := L) (K := K) (p + 1) n c'}
          ∪ {c' | ¬ NoOvershoot (L := L) (K := K) p c'} := by
      intro c' hc'
      simp only [Set.mem_setOf_eq, Set.mem_union, not_and_or] at hc' ⊢
      exact hc'
    calc ((NonuniformMajority L K).transitionKernel ^ tseam) c
            {c' | ¬ (SeamEpidemics.allPhaseGe (L := L) (K := K) (p + 1) n c' ∧
                     NoOvershoot (L := L) (K := K) p c')}
        ≤ ((NonuniformMajority L K).transitionKernel ^ tseam) c
            ({c' | ¬ SeamEpidemics.allPhaseGe (L := L) (K := K) (p + 1) n c'}
              ∪ {c' | ¬ NoOvershoot (L := L) (K := K) p c'}) := measure_mono hsub
      _ ≤ ((NonuniformMajority L K).transitionKernel ^ tseam) c
            {c' | ¬ SeamEpidemics.allPhaseGe (L := L) (K := K) (p + 1) n c'}
          + ((NonuniformMajority L K).transitionKernel ^ tseam) c
            {c' | ¬ NoOvershoot (L := L) (K := K) p c'} := measure_union_le _ _
      _ ≤ (εepidemic : ℝ≥0∞) + (εovershoot : ℝ≥0∞) := add_le_add hA hB
      _ = ((εepidemic + εovershoot : ℝ≥0) : ℝ≥0∞) := by push_cast; rfl

@[simp] theorem seamEpidemicExactW_Post
    (p n tseam : ℕ) (εepidemic εovershoot : ℝ≥0) (hDrift) (hNoOvershoot)
    (c : Config (AgentState L K)) :
    (seamEpidemicExactW (L := L) (K := K) p n tseam εepidemic εovershoot
        hDrift hNoOvershoot).Post c
      = (SeamEpidemics.allPhaseGe (L := L) (K := K) (p + 1) n c ∧
          NoOvershoot (L := L) (K := K) p c) := rfl

@[simp] theorem seamEpidemicExactW_t
    (p n tseam : ℕ) (εepidemic εovershoot : ℝ≥0) (hDrift) (hNoOvershoot) :
    (seamEpidemicExactW (L := L) (K := K) p n tseam εepidemic εovershoot
        hDrift hNoOvershoot).t = tseam := rfl

@[simp] theorem seamEpidemicExactW_eps
    (p n tseam : ℕ) (εepidemic εovershoot : ℝ≥0) (hDrift) (hNoOvershoot) :
    (seamEpidemicExactW (L := L) (K := K) p n tseam εepidemic εovershoot
        hDrift hNoOvershoot).ε = εepidemic + εovershoot := rfl

/-- **Seam-exact → exact-work bridge (deterministic, pointwise).**  The strengthened
`Post` (`allPhaseGe (p+1) ∧ NoOvershoot p`) yields the EXACT `(p+1)`-window pointwise,
with NO further per-seam timing input — `NoOvershoot p c` is exactly the no-overshoot
hypothesis of `SeamEpidemics.allPhaseEq_of_ge_and_no_overshoot`.  This replaces the
`seam_into_exact_work` map (which still took the timing input as a side hypothesis). -/
theorem seamExact_into_exact_work {p n : ℕ} :
    ∀ c : Config (AgentState L K),
      (SeamEpidemics.allPhaseGe (L := L) (K := K) (p + 1) n c ∧
        NoOvershoot (L := L) (K := K) p c) →
      SeamEpidemics.allPhaseEq (L := L) (K := K) (p + 1) n c :=
  fun _c h => SeamEpidemics.allPhaseEq_of_ge_and_no_overshoot h.1 (fun a ha => h.2 a ha)

end SeamNoOvershoot

end ExactMajority
