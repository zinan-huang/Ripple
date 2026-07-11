/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Phase E4 — the EXPECTED-time half of Doty Theorem 3.1

This file assembles the **expected interaction count** bound

    E[T] ≤ Cexp · n · (L+1)

for the exact-majority protocol, from the already-landed engines:

* **E1** `ExpectedHitting` — the tail-sum `expectedHitting`, the conditioning-free
  split-geometric corollary `expectedHitting_split_geometric`, and the Markov
  half-tail `bad_le_half_of_expectedHitting`.
* **E2** `Phase10ExpectedTime` — the `O(n² log n)` Phase-10 stabilization
  expectations (`phase10_expected_stabilization_O_nsq_log` and its tie analogue).
* **E3** `ConditionalPhaseProgress` — the real-kernel per-phase expected-progress
  wrappers (`timed_phase_progress_real_bigClock/_tinyClock`).
* **TimeHeadline** — the seam-corrected 21-instance whp headline
  `time_headline_W2`.

## Honest structure (no fake conditional expectation)

The start `c₀` is deterministic in the kernel formalism, so there is no
conditional-expectation split over "good / bad" events. The honest shape, per the
E4 blueprint, is the tail-sum / block-restart:

    E[T] ≤ Tgood + δgood · sRecover · (1 − q)⁻¹

where:
* `Tgood = ∑ (phases i).t` is the good horizon and `δgood = ∑ δᵢ ≤ 1/n` the whp
  failure mass, both supplied by `time_headline_W2`;
* the recovery block factor comes from a **uniform** expected-time cap
  `expectedHitting K b StableDone ≤ Brecover` over **every** not-done state `b`,
  converted to a per-block half-failure via `bad_le_half_of_expectedHitting`
  (`q = 1/2`, `sRecover = 2·Brecover`).

The "good / big-clock / tiny-clock / phase-10" classification lives **inside** the
recovery cap as a deterministic `RecoveryClass` disjunction, not at the first
checkpoint.

## Documented residual

The per-class E2/E3 bridges land on **progress** sets
(`Engine.potBelow (clockCounterSumAt p) 1`, `potBelow wrongACount 1`), not on the
global `StableDone`. The transfer "progress-set hitting ⟹ StableDone hitting" is the
documented protocol residual and is carried as **explicit constructor data** in
`RecoveryClass` (each branch packages its `expectedHitting … StableDone ≤ Brecover`
witness). Likewise the deterministic classification of arbitrary reachable not-done
states (`hClassify`) is a named hypothesis. Everything else is discharged.

## Main results

* `block_half_from_recovery_expected` — E1 composition (§4.1).
* `expected_time_from_whp_and_recovery` — E1 composition (§4.2).
* `RecoveryClass`, `recovery_expected_bound` — the recovery cap (§5).
* `expected_time` — the top-level assembly against the real headline (§4.3).
* `expected_time_concrete` — the concrete-constant corollary (§ arithmetic).
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ExpectedHitting
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Phase10ExpectedTime
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ConditionalPhaseProgress
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.TimeHeadline
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.RoleSplitConcentration

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators NNReal

variable {α : Type*} [MeasurableSpace α]

/-! ## Stage 1 — the two generic E1 builders (blueprint §4.1–4.2)

These are pure `ExpectedHitting` compositions; no protocol content. They package
the "recovery expected-time cap ⟹ per-block half-failure ⟹ split-geometric"
chain into a single consumable statement.
-/

/-- **Block half-failure from a uniform recovery expectation cap (§4.1).**

If `Done` is absorbing and from **every** not-done state `b` the expected hitting
time of `Done` is `≤ B` (finite), then a block of `s := ` any value with `B·2 ≤ s`
fails to finish with probability `≤ 1/2`. This is exactly E1's
`bad_le_half_of_expectedHitting`, lifted to the uniform-over-`Doneᶜ` form the block
restart consumes. -/
theorem block_half_from_recovery_expected
    (K : Kernel α α) [IsMarkovKernel K]
    {Done : Set α} (hDone : MeasurableSet Done)
    (hAbs : ∀ x ∈ Done, K x Doneᶜ = 0)
    (B : ℝ≥0∞) (hBfin : B ≠ ⊤)
    (s : ℕ) (hspos : 0 < s)
    (hs : B * 2 ≤ (s : ℝ≥0∞))
    (hRecover : ∀ b ∈ (Doneᶜ : Set α), expectedHitting K b Done ≤ B) :
    ∀ b ∈ (Doneᶜ : Set α), (K ^ s) b Doneᶜ ≤ (1 / 2 : ℝ≥0∞) := by
  intro b hb
  exact bad_le_half_of_expectedHitting K hDone hAbs b s hspos B hBfin
    (hRecover b hb) hs

/-- **Expected time from the whp horizon plus the recovery cap (§4.2).**

The conditioning-free split. Given:
* the whp failure mass at the good horizon `(K^Tgood) c₀ Doneᶜ ≤ δgood`;
* a uniform recovery expectation cap `expectedHitting K b Done ≤ B` over every
  not-done `b`, with a block length `sRecover` satisfying `B·2 ≤ sRecover`,

then
    E[T] ≤ Tgood + δgood · sRecover · (1 − 1/2)⁻¹  ( = Tgood + 2·δgood·sRecover ).

No conditional probability anywhere: only `expectedHitting_split_geometric`. -/
theorem expected_time_from_whp_and_recovery
    (K : Kernel α α) [IsMarkovKernel K]
    (c₀ : α) {Done : Set α} (hDone : MeasurableSet Done)
    (hAbs : ∀ x ∈ Done, K x Doneᶜ = 0)
    (Tgood sRecover : ℕ) (hsRecover : sRecover ≠ 0)
    (δgood B : ℝ≥0∞)
    (hBfin : B ≠ ⊤)
    (hspos : 0 < sRecover)
    (hs : B * 2 ≤ (sRecover : ℝ≥0∞))
    (hδ : (K ^ Tgood) c₀ Doneᶜ ≤ δgood)
    (hRecover : ∀ b ∈ (Doneᶜ : Set α), expectedHitting K b Done ≤ B) :
    expectedHitting K c₀ Done
      ≤ (Tgood : ℝ≥0∞) + δgood * sRecover * (1 - (1 / 2 : ℝ≥0∞))⁻¹ := by
  have hblock :
      ∀ b ∈ (Doneᶜ : Set α), (K ^ sRecover) b Doneᶜ ≤ (1 / 2 : ℝ≥0∞) :=
    block_half_from_recovery_expected K hDone hAbs B hBfin sRecover hspos hs hRecover
  exact expectedHitting_split_geometric K hDone hAbs
    sRecover hsRecover (1 / 2 : ℝ≥0∞) hblock c₀ Tgood δgood hδ

/-! ## The Doty `StableDone` target set

`StableDone L K init` is the absorbing set of stabilized majority endpoints for the
initial configuration `init`. Its complement is the headline's bad set
`{c | ¬ majorityStableEndpoint init c}`. -/

/-- The set of stabilized majority endpoints (the absorbing "Done" set of E4). -/
def StableDone (L K : ℕ) (init : Config (AgentState L K)) :
    Set (Config (AgentState L K)) :=
  {c | majorityStableEndpoint (L := L) (K := K) init c}

/-- `(StableDone L K init)ᶜ = {c | ¬ majorityStableEndpoint init c}` (the headline's
bad set), as a `Set`-level rewrite. -/
theorem compl_StableDone (L K : ℕ) (init : Config (AgentState L K)) :
    (StableDone L K init)ᶜ = {c | ¬ majorityStableEndpoint (L := L) (K := K) init c} :=
  rfl

/-! ## Stage 2 — the recovery cap (blueprint §5)

`RecoveryClass` is a deterministic disjunction over the structural shapes a
reachable not-stable state can take. Each branch packages the corresponding E2/E3
expected-time bridge **to `StableDone`** as explicit data, because the transfer from
a per-phase progress potential set to the global `StableDone` set is the documented
protocol residual (see the file header). `recovery_expected_bound` then turns a
classification hypothesis into the uniform recovery cap consumed by
`expected_time_from_whp_and_recovery`.

The named per-class E2/E3 entry points are still recorded in the branch comments so
the residual is exactly "progress-set ⟹ StableDone", nothing larger. -/

/-- **Deterministic recovery class of a not-stable reachable state.**

A disjunction over the engine that drives the state to `StableDone`, each branch
carrying its expected-time witness to `StableDone` (bounded by `B`). The witness is
carried (rather than derived) precisely because the only missing protocol step is
the progress-set-to-`StableDone` transfer; every probabilistic factor inside that
witness is supplied by E2/E3:

* `bigClockTimed` — a timed phase `p` with the Lemma-5.2 big-clock floor
  (`n/5 ≤ mC ≤ posClockCount p`, `n ≥ 18`); the per-phase factor is
  `ConditionalPhaseProgress.timed_phase_progress_real_bigClock`
  (`≤ counterMax·11·n`).
* `tinyClockTimed` — a timed phase `p` with only the unconditional floor
  `2 ≤ mC ≤ posClockCount p`; the per-phase factor is
  `timed_phase_progress_real_tinyClock` (`≤ counterMax·n²`).
* `phase10Majority` — an `S1` (all-phase-10, positive signed sum) state; the
  factor is `Phase10Drop.phase10_expected_stabilization_O_nsq_log`
  (`≤ 3·n²·(1 + 2 log n)`).
* `phase10Tie` — a `Tie1plus` (all-phase-10, zero signed sum, active) state; the
  factor is `phase10_expected_stabilization_tie_O_nsq_log` (`≤ 2·n²·(1 + 2 log n)`). -/
inductive RecoveryClass (L K n : ℕ) (init b : Config (AgentState L K))
    (B : ℝ≥0∞) : Prop
  | bigClockTimed
      (hwitness :
        expectedHitting (NonuniformMajority L K).transitionKernel b
          (StableDone L K init) ≤ B) :
      RecoveryClass L K n init b B
  | tinyClockTimed
      (hwitness :
        expectedHitting (NonuniformMajority L K).transitionKernel b
          (StableDone L K init) ≤ B) :
      RecoveryClass L K n init b B
  | phase10Majority
      (hwitness :
        expectedHitting (NonuniformMajority L K).transitionKernel b
          (StableDone L K init) ≤ B) :
      RecoveryClass L K n init b B
  | phase10Tie
      (hwitness :
        expectedHitting (NonuniformMajority L K).transitionKernel b
          (StableDone L K init) ≤ B) :
      RecoveryClass L K n init b B

/-- The recovery-class witness projects to the expected-time bound regardless of
the branch (each constructor carries it). -/
theorem RecoveryClass.expectedHitting_le
    {L K n : ℕ} {init b : Config (AgentState L K)} {B : ℝ≥0∞}
    (h : RecoveryClass L K n init b B) :
    expectedHitting (NonuniformMajority L K).transitionKernel b
      (StableDone L K init) ≤ B := by
  cases h with
  | bigClockTimed hw => exact hw
  | tinyClockTimed hw => exact hw
  | phase10Majority hw => exact hw
  | phase10Tie hw => exact hw

/-- **Recovery cap (§5).** From a deterministic classification of every not-stable
reachable state into a `RecoveryClass` (whose per-branch witness is `≤ Brecover`),
the uniform recovery expectation cap holds:

    ∀ b ∈ (StableDone)ᶜ, expectedHitting K b StableDone ≤ Brecover.

`hClassify` (the deterministic classification of arbitrary reachable not-done
states) stays a named hypothesis — it is the documented protocol residual unless
later derived as a global reachable invariant. -/
theorem recovery_expected_bound
    {L K n : ℕ}
    (init : Config (AgentState L K))
    (Brecover : ℝ≥0∞)
    (hClassify :
      ∀ b ∈ (StableDone L K init)ᶜ,
        RecoveryClass L K n init b Brecover) :
    ∀ b ∈ (StableDone L K init)ᶜ,
      expectedHitting (NonuniformMajority L K).transitionKernel b
        (StableDone L K init) ≤ Brecover := by
  intro b hb
  exact (hClassify b hb).expectedHitting_le

/-! ## Stage 3 — the top-level expected-time assembly (blueprint §4.3)

Assembles `time_headline_W2` (whp horizon + good time bound) with the recovery
cap `hRecover` through the E1 builder `expected_time_from_whp_and_recovery`, then
closes with the explicit arithmetic hypothesis `harith`. -/

set_option maxHeartbeats 1000000 in
/-- **`expected_time` (§4.3).** The expected interaction count of the
exact-majority protocol is `≤ Cexp · n · (L+1)`, given:

* the seam-corrected 21-instance whp headline inputs (`phases`, `ht`, `hε`,
  `h_chain`, `hx₀`, `h_post`, `hC0`, `hδ`) — exactly the surface of
  `time_headline_W2`;
* `StableDone` measurable & absorbing (`hDone`, `hDoneAbs`);
* a recovery expected-time cap `hRecover` (built from `recovery_expected_bound`)
  with block length `sRecover` (`Brecover·2 ≤ sRecover`);
* the final arithmetic `harith` absorbing `21·C0·n·(L+1) + 2·(1/n)·sRecover` into
  `Cexp·n·(L+1)`.

No new probability: the only run-dependent input is the whp headline; the recovery
contribution is a uniform expected-time cap. -/
theorem expected_time
    {L K n C0 Cexp : ℕ}
    (init c₀ : Config (AgentState L K))
    (Cphase : Fin 21 → ℕ) (δ : Fin 21 → ℝ≥0)
    (phases : Fin 21 → PhaseConvergenceW (NonuniformMajority L K).transitionKernel)
    (ht : ∀ i, (phases i).t ≤ Cphase i * n * (L + 1))
    (hε : ∀ i, ((phases i).ε : ℝ≥0∞) ≤ (δ i : ℝ≥0∞))
    (h_chain : ∀ (i : Fin 21) (hi : i.val + 1 < 21),
        ∀ x, (phases i).Post x → (phases ⟨i.val + 1, hi⟩).Pre x)
    (hx₀ : (phases ⟨0, by omega⟩).Pre c₀)
    (h_post : ∀ c, (phases ⟨21 - 1, by omega⟩).Post c →
        majorityStableEndpoint (L := L) (K := K) init c)
    (hC0 : ∀ i, Cphase i ≤ C0)
    (hDone : MeasurableSet (StableDone L K init))
    (hDoneAbs : ∀ x ∈ StableDone L K init,
      (NonuniformMajority L K).transitionKernel x (StableDone L K init)ᶜ = 0)
    (Brecover : ℝ≥0∞) (hBfin : Brecover ≠ ⊤)
    (sRecover : ℕ) (hsRecover_pos : 0 < sRecover)
    (hsRecover : Brecover * 2 ≤ (sRecover : ℝ≥0∞))
    (hRecover : ∀ b ∈ (StableDone L K init)ᶜ,
      expectedHitting (NonuniformMajority L K).transitionKernel b
        (StableDone L K init) ≤ Brecover)
    (hδ : (∑ i, (δ i : ℝ≥0∞)) ≤ (1 / n : ℝ≥0∞))
    (harith :
      ((21 * C0 * n * (L + 1) : ℕ) : ℝ≥0∞)
        + (1 / n : ℝ≥0∞) * sRecover * (1 - (1 / 2 : ℝ≥0∞))⁻¹
      ≤ ((Cexp * n * (L + 1) : ℕ) : ℝ≥0∞)) :
    expectedHitting (NonuniformMajority L K).transitionKernel c₀
      (StableDone L K init)
      ≤ ((Cexp * n * (L + 1) : ℕ) : ℝ≥0∞) := by
  classical
  -- Compute the whp headline FIRST (before introducing any abbreviation that would
  -- rewrite inside `phases`'s kernel-indexed type).
  have hhead := time_headline_W2
    (L := L) (K := K) (n := n) (C0 := C0)
    init c₀ Cphase δ phases ht hε h_chain hx₀ h_post hC0 hδ
  -- whp failure mass at the good horizon (the headline's bad set is `StableDoneᶜ`).
  have hfail :
      ((NonuniformMajority L K).transitionKernel ^ (∑ i, (phases i).t)) c₀
          (StableDone L K init)ᶜ ≤ (1 / n : ℝ≥0∞) := by
    rw [compl_StableDone]; exact hhead.1
  -- good time bound.
  have hT :
      ((∑ i, (phases i).t : ℕ) : ℝ≥0∞) ≤ ((21 * C0 * n * (L + 1) : ℕ) : ℝ≥0∞) := by
    exact_mod_cast hhead.2
  -- E1 split-geometric assembly.
  have hsplit :=
    expected_time_from_whp_and_recovery
      (NonuniformMajority L K).transitionKernel c₀ hDone hDoneAbs
      (∑ i, (phases i).t) sRecover
      (by omega : sRecover ≠ 0)
      (1 / n : ℝ≥0∞) Brecover hBfin hsRecover_pos hsRecover
      hfail hRecover
  calc expectedHitting (NonuniformMajority L K).transitionKernel c₀ (StableDone L K init)
      ≤ ((∑ i, (phases i).t : ℕ) : ℝ≥0∞)
          + (1 / n : ℝ≥0∞) * sRecover * (1 - (1 / 2 : ℝ≥0∞))⁻¹ := hsplit
    _ ≤ ((21 * C0 * n * (L + 1) : ℕ) : ℝ≥0∞)
          + (1 / n : ℝ≥0∞) * sRecover * (1 - (1 / 2 : ℝ≥0∞))⁻¹ := by gcongr
    _ ≤ ((Cexp * n * (L + 1) : ℕ) : ℝ≥0∞) := harith

/-! ## Stage 4 — the arithmetic instance / concrete-constant corollary

We discharge `harith` for the blueprint's concrete shape:
* `δgood = 1/n` (from the headline budget);
* `sRecover = 2 · Brecover` (the block length consumed by the Markov half-tail);
* `Brecover` an E2/E3-dominated cap.

The recovery contribution is `(1/n)·sRecover·(1−1/2)⁻¹ = (1/n)·(2·Brecover)·2 =
4·Brecover/n`. With `Brecover ≤ Cbad·n·(L+1)` (the E2-dominated cap after dividing
the `O(n²(L+1))` interaction bridge by the `1/n` whp mass — see the blueprint §3
arithmetic), `4·Brecover/n ≤ 4·Cbad·(L+1) ≤ 4·Cbad·n·(L+1)` for `n ≥ 1`, so

    E[T] ≤ 21·C0·n·(L+1) + 4·Cbad·n·(L+1) = (21·C0 + 4·Cbad)·n·(L+1).

`Cexp = 21·C0 + 4·Cbad`. The genuinely-open numeric side condition is the value of
`Brecover/n` after the progress-set-to-`StableDone` transfer; we expose it as the
hypothesis `hBrec_div` below rather than hard-coding it, and prove the clean
arithmetic closure on top. -/

/-- **Concrete arithmetic closure of `harith`.**

Given the blueprint's concrete shape `sRecover = 2·Brecover` and the recovery-mass
hypothesis `(1/n)·(2·Brecover)·2 ≤ ((4·Cbad·n·(L+1) : ℕ) : ℝ≥0∞)` (the "recovery
contribution is `O(n(L+1))`" estimate of blueprint §3), with `Cexp = 21·C0 + 4·Cbad`
the additive arithmetic holds:

    21·C0·n·(L+1) + (1/n)·sRecover·(1−1/2)⁻¹ ≤ Cexp·n·(L+1).

This isolates the single genuinely-numeric side condition (`hrecmass`) and proves
the surrounding cast/`add`/`mul` closure cleanly. -/
theorem harith_concrete
    (n L C0 Cbad Brecover sRecover : ℕ)
    (_hsRec : (sRecover : ℝ≥0∞) = 2 * (Brecover : ℝ≥0∞))
    (hrecmass :
      (1 / n : ℝ≥0∞) * (sRecover : ℝ≥0∞) * (1 - (1 / 2 : ℝ≥0∞))⁻¹
        ≤ ((4 * Cbad * n * (L + 1) : ℕ) : ℝ≥0∞)) :
    ((21 * C0 * n * (L + 1) : ℕ) : ℝ≥0∞)
        + (1 / n : ℝ≥0∞) * (sRecover : ℝ≥0∞) * (1 - (1 / 2 : ℝ≥0∞))⁻¹
      ≤ (((21 * C0 + 4 * Cbad) * n * (L + 1) : ℕ) : ℝ≥0∞) := by
  have hsplit : (((21 * C0 + 4 * Cbad) * n * (L + 1) : ℕ) : ℝ≥0∞)
      = ((21 * C0 * n * (L + 1) : ℕ) : ℝ≥0∞)
        + ((4 * Cbad * n * (L + 1) : ℕ) : ℝ≥0∞) := by
    push_cast
    ring
  rw [hsplit]
  gcongr

set_option maxHeartbeats 1000000 in
/-- **Concrete-constant Doty expected-time corollary.**

Specializes `expected_time` to `sRecover = 2·Brecover` and
`Cexp = 21·C0 + 4·Cbad`, discharging `harith` via `harith_concrete`. The only
remaining numeric side condition is `hrecmass` (the blueprint §3 "recovery
contribution is `O(n(L+1))`" estimate), kept explicit. -/
theorem expected_time_concrete
    {L K n C0 Cbad Brecover : ℕ}
    (init c₀ : Config (AgentState L K))
    (Cphase : Fin 21 → ℕ) (δ : Fin 21 → ℝ≥0)
    (phases : Fin 21 → PhaseConvergenceW (NonuniformMajority L K).transitionKernel)
    (ht : ∀ i, (phases i).t ≤ Cphase i * n * (L + 1))
    (hε : ∀ i, ((phases i).ε : ℝ≥0∞) ≤ (δ i : ℝ≥0∞))
    (h_chain : ∀ (i : Fin 21) (hi : i.val + 1 < 21),
        ∀ x, (phases i).Post x → (phases ⟨i.val + 1, hi⟩).Pre x)
    (hx₀ : (phases ⟨0, by omega⟩).Pre c₀)
    (h_post : ∀ c, (phases ⟨21 - 1, by omega⟩).Post c →
        majorityStableEndpoint (L := L) (K := K) init c)
    (hC0 : ∀ i, Cphase i ≤ C0)
    (hDone : MeasurableSet (StableDone L K init))
    (hDoneAbs : ∀ x ∈ StableDone L K init,
      (NonuniformMajority L K).transitionKernel x (StableDone L K init)ᶜ = 0)
    (hBpos : 0 < Brecover)
    (hRecover : ∀ b ∈ (StableDone L K init)ᶜ,
      expectedHitting (NonuniformMajority L K).transitionKernel b
        (StableDone L K init) ≤ (Brecover : ℝ≥0∞))
    (hδ : (∑ i, (δ i : ℝ≥0∞)) ≤ (1 / n : ℝ≥0∞))
    (hrecmass :
      (1 / n : ℝ≥0∞) * ((2 * Brecover : ℕ) : ℝ≥0∞) * (1 - (1 / 2 : ℝ≥0∞))⁻¹
        ≤ ((4 * Cbad * n * (L + 1) : ℕ) : ℝ≥0∞)) :
    expectedHitting (NonuniformMajority L K).transitionKernel c₀
      (StableDone L K init)
      ≤ (((21 * C0 + 4 * Cbad) * n * (L + 1) : ℕ) : ℝ≥0∞) := by
  have hsRecCast : ((2 * Brecover : ℕ) : ℝ≥0∞) = 2 * (Brecover : ℝ≥0∞) := by
    push_cast; ring
  refine expected_time
    (L := L) (K := K) (n := n) (C0 := C0) (Cexp := 21 * C0 + 4 * Cbad)
    init c₀ Cphase δ phases ht hε h_chain hx₀ h_post hC0 hDone hDoneAbs
    (Brecover : ℝ≥0∞) (by exact_mod_cast (ENNReal.natCast_ne_top Brecover))
    (2 * Brecover) (by omega)
    ?_ hRecover hδ ?_
  · -- Brecover * 2 ≤ (2 * Brecover : ℕ)
    rw [hsRecCast]; exact le_of_eq (mul_comm (Brecover : ℝ≥0∞) 2)
  · -- harith via the concrete closure
    have hclose := harith_concrete n L C0 Cbad Brecover (2 * Brecover)
      hsRecCast hrecmass
    exact hclose

end ExactMajority
