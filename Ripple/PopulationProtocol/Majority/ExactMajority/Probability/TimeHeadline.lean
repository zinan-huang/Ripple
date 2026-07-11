/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Phase D-3 — the eleven-phase composition headline (`time_headline_W`)

This file delivers the **Phase-D composition headline** of the Doty et al. exact-majority
time campaign: the single theorem that composes the eleven timed phase instances on the
real `(NonuniformMajority L K).transitionKernel` into a with-high-probability stabilization
bound in `O(log n)` parallel time, UNCONDITIONAL beyond the named-input surface.

It is the WEAK-structure (`PhaseConvergenceW`, no absorption field) analogue of
`TimeComposition.time_headline`.  The campaign's Phase-B rewire retired the strong
structure's `post_absorbing` field (it forced the FALSE `habs_mix` on the faithful clock
minutes); every real phase instance is therefore a `PhaseConvergenceW`, and the strong
Phase-2/9 instance lifts via `PhaseConvergence.toW`.  The composition is `composeW_n_phases`
over the `Fin 11` family with the chained budgets `∑ ε_i` and horizon `∑ t_i`.

## The eleven instances (the family this headline is parameterised over)

Each lives on `(NonuniformMajority L K).transitionKernel`, with `Pre`/`Post` (verified in
each instance file):

| i  | instance file                              | `Pre`                                   | `Post`                                  |
|----|--------------------------------------------|-----------------------------------------|-----------------------------------------|
| 0  | `RoleSplitConcentration` (3-stage)         | role-split start (`stage1.Pre`)          | `RoleSplitStage2Good` (`roleMCR=0 ∧ crCount≤1`) |
| 1  | `Phase1Convergence.phase1Convergence`      | `Phase1AllMain n ∧ extremeU ≤ M₀`        | `Phase1AllMain n ∧ NoExtreme`           |
| 2  | `Phase2Convergence.phase2Convergence.toW`  | `Qwin U v n`                             | `Qwin U v n ∧ oFinished U n`            |
| 3  | `HourComposition.phase3Convergence`        | `{c = c₀}` (clock-entry config)          | `HourComplete n mC` (the hour closed)   |
| 4  | `Phase4Convergence.phase4Convergence`      | `StableTie4 ∨ Qwin4 n` (tie / non-tie)   | `StableTie4 ∨ advFinished n`            |
| 5  | `Phase5Convergence.phase5Convergence`      | `Phase5AllWin n ∧ unsampledReserveU ≤ M₀`| `Phase5AllWin n ∧ ReserveSampleGood i K₀`|
| 6  | `Phase6Convergence.phase6Convergence'`     | `Phase6Win n ∧ highMass l ≤ M₀`          | `Phase6Win n ∧ highMass l = 0`          |
| 7  | `Phase7Convergence.phase7Convergence''`    | `Inv7Sum n ∧ classMassN σ ≤ M₀`          | `Inv7Sum n ∧ classMassN σ = 0`          |
| 8  | `Phase8Convergence.phase8Convergence`      | `Phase8AllMain n ∧ minorityU σ ≤ M₀`     | `Phase8AllMain n ∧ minorityU σ = 0`     |
| 9  | `Phase2Convergence.phase2Convergence.toW`  | `Qwin U' v' n` (the second opinion union)| `Qwin U' v' n ∧ oFinished U' n`        |
| 10 | `Phase10Convergence.phase10Convergence`    | `S1 n ∨ Tie1plus n`                      | `Phase10Post` (unanimous output)        |

The stabilize-early branches thread as disjuncts (the paper's structure): Phase 2's
consensus and Phase 4's tie are carried as `∨`-disjuncts in `Pre`/`Post` (mirrored from
`Phase4Convergence.phase4Convergence`).  The composition's FINAL `Post` flows, via `h_post`,
into `Analysis.StableEndpoints.majorityStableEndpoint` — which is itself the disjunction
`phase2Consensus ∨ phase4Tie ∨ phase9Consensus ∨ phase10MajorityWitness` (stabilized at
2 ∨ at 4 ∨ at 9 ∨ reached 10's unanimity).

## The surviving-input inventory (THE honest Phase-D deliverable)

The headline is `UNCONDITIONAL` beyond exactly the following named feeders, all carried as
hypotheses (no smuggled axiom, no `sorry`, no `native_decide`):

1. **The eleven phase instances** `phases : Fin 11 → PhaseConvergenceW K` — each already a
   proven `PhaseConvergenceW` in its file (the per-phase `convergence` tails are discharged
   there, modulo the per-phase carried drains listed next).
2. **The chain maps** `h_chain : Post_i ⟹ Pre_{i+1}` — the eleven→ten deterministic
   structural bridges (phase-advance facts + the carried structural floors: Phase 0's role
   counts → 1's window, Theorem-6.2 structure from Phase 3 → 4/5/6, `ReserveSampleGood`
   from 5 → 6, etc.).  Documented as a named input: each bridge is a deterministic-reachable
   `Analysis/` invariant; supplying them all is the honest Phase-D surface.
3. **The start** `hx₀ : (phases 0).Pre c₀` — the validInitial → role-split-entry condition.
4. **The closing map** `h_post : Post_10 ⟹ majorityStableEndpoint init` — the deterministic
   stable-endpoint reading of the last phase's unanimity.
5. **The per-phase carried drains** (folded into the instances, hence into `phases`): the
   `q`/`hstep` drain rates for phases 0/1/5/6/7/8 (the `OneSidedCancel` engine's per-step
   rectangle floors, the `[45]`/Lemma-7.x quantitative atoms); Phase 3's `hside` (the
   τ-uniform `Sgood(T)ᶜ ≤ sideEps` side budget, the §6 nine named feeders, width slice
   concrete via `εWAt`); Phase 5's `hConc` sampled-class concentration; the Lemma-5.2 clock
   floor `hfloor`.  These are the consolidated B-12/B-13/D-1/D-2 residuals, threaded but not
   re-opened.
6. **The scaling** `ht : t_i ≤ Cphase_i · n · (L+1)` (each phase is `O(log n)`-parallel) and
   `hδ : ∑ δ_i ≤ 1/n` (the union budget is whp).

The conclusion: from `(phases 0).Pre c₀`, within `T = ∑ t_i ≤ 11·C0·n·(L+1) = O(n log n)`
interactions (`O(L+1) = O(log n)` parallel time), the run reaches `majorityStableEndpoint`
with failure probability `≤ 1/n`.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.PhaseConvergenceWeak
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.NonuniformMarkovChain
import Ripple.PopulationProtocol.Majority.ExactMajority.Analysis.StableEndpoints

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

/-- The last phase index `10 : Fin 11`.  Matches the `⟨m - 1, _⟩` last-phase index
`composeW_n_phases` produces at `m = 11`. -/
private def lastPhaseW : Fin 11 := ⟨11 - 1, by omega⟩

/-! ## Arithmetic facts (independent of per-phase content) -/

/-- **Total-time arithmetic.**  If every phase takes at most `Cphase i · n · (L+1)`
interactions, the total interaction count is at most `(∑ Cphase) · n · (L+1)`. -/
theorem total_time_le_W
    {m : ℕ} {n L : ℕ} (t Cphase : Fin m → ℕ)
    (ht : ∀ i, t i ≤ Cphase i * n * (L + 1)) :
    (∑ i, t i) ≤ (∑ i, Cphase i) * n * (L + 1) := by
  calc (∑ i, t i)
      ≤ ∑ i, Cphase i * n * (L + 1) := Finset.sum_le_sum (fun i _ => ht i)
    _ = (∑ i, Cphase i) * n * (L + 1) := by
        simp [Finset.sum_mul]

/-- **Total-error arithmetic.**  Union-bound total error `≤ ∑ δ`. -/
theorem total_error_le_W
    {m : ℕ} (ε δ : Fin m → ℝ≥0)
    (hε : ∀ i, (ε i : ℝ≥0∞) ≤ (δ i : ℝ≥0∞)) :
    (∑ i, (ε i : ℝ≥0∞)) ≤ ∑ i, (δ i : ℝ≥0∞) :=
  Finset.sum_le_sum (fun i _ => hε i)

/-! ## The compose-all-phases contract (weak structure) -/

/-- **Doty time composition (weak-structure assembly contract).**

Given eleven `PhaseConvergenceW` instances for the `NonuniformMajority L K` transition
kernel, with per-phase time/error bounds, the chaining hypothesis `h_chain` (phase `i`'s
`Post` implies phase `i+1`'s `Pre`), the start hypothesis `hx₀`, and the closing map
`h_post` (the last phase's `Post` implies `majorityStableEndpoint init`), the composed chain
reaches `majorityStableEndpoint init` within `T := ∑ (phases i).t` interactions with failure
probability at most `∑ (phases i).ε`, and moreover `T ≤ (∑ Cphase)·n·(L+1)` and
`∑ (phases i).ε ≤ ∑ δ`.

This is purely the assembly arithmetic over `composeW_n_phases`; it uses no per-phase
content beyond each instance's `convergence` field. -/
theorem time_composition_W
    {L K n : ℕ}
    (init c₀ : Config (AgentState L K))
    (Cphase : Fin 11 → ℕ) (δ : Fin 11 → ℝ≥0)
    (phases : Fin 11 → PhaseConvergenceW (NonuniformMajority L K).transitionKernel)
    (ht : ∀ i, (phases i).t ≤ Cphase i * n * (L + 1))
    (hε : ∀ i, ((phases i).ε : ℝ≥0∞) ≤ (δ i : ℝ≥0∞))
    (h_chain : ∀ (i : Fin 11) (hi : i.val + 1 < 11),
        ∀ x, (phases i).Post x → (phases ⟨i.val + 1, hi⟩).Pre x)
    (hx₀ : (phases ⟨0, by omega⟩).Pre c₀)
    (h_post : ∀ c, (phases lastPhaseW).Post c →
        majorityStableEndpoint (L := L) (K := K) init c) :
    ((NonuniformMajority L K).transitionKernel ^ (∑ i, (phases i).t)) c₀
        {c | ¬ majorityStableEndpoint (L := L) (K := K) init c}
      ≤ (∑ i, ((phases i).ε : ℝ≥0∞))
    ∧ (∑ i, (phases i).t) ≤ (∑ i, Cphase i) * n * (L + 1)
    ∧ (∑ i, ((phases i).ε : ℝ≥0∞)) ≤ ∑ i, (δ i : ℝ≥0∞) := by
  refine ⟨?_, ?_, ?_⟩
  · have h_compose :=
      composeW_n_phases (K := (NonuniformMajority L K).transitionKernel)
        (m := 11) (by omega) phases h_chain c₀ hx₀
    have h_subset :
        {c | ¬ majorityStableEndpoint (L := L) (K := K) init c}
          ⊆ {c | ¬ (phases ⟨11 - 1, by omega⟩).Post c} := by
      intro c hc
      simp only [Set.mem_setOf_eq] at hc ⊢
      intro hPost
      exact hc (h_post c hPost)
    calc ((NonuniformMajority L K).transitionKernel ^ (∑ i, (phases i).t)) c₀
            {c | ¬ majorityStableEndpoint (L := L) (K := K) init c}
        ≤ ((NonuniformMajority L K).transitionKernel ^ (∑ i, (phases i).t)) c₀
            {c | ¬ (phases ⟨11 - 1, by omega⟩).Post c} := measure_mono h_subset
      _ ≤ (∑ i, ((phases i).ε : ℝ≥0∞)) := h_compose
  · exact total_time_le_W (fun i => (phases i).t) Cphase ht
  · exact total_error_le_W (fun i => (phases i).ε) δ hε

/-! ## Headline corollary: O(log n)-parallel whp stabilization (weak structure)

The Phase-D deliverable.  See the file header for the complete surviving-input inventory.
-/

/-- **`time_headline_W` — the eleven-phase composition headline (UNCONDITIONAL beyond
the named-input surface).**

Specialising the constants: if every per-phase constant satisfies `Cphase i ≤ C0` and the
total error budget is `∑ δ ≤ 1/n`, then the composed eleven-phase weak chain reaches
`majorityStableEndpoint init` within `T ≤ 11·C0·n·(L+1)` interactions with failure
probability at most `1/n`.

`T ≤ 11·C0·n·(L+1)` means `O(n·(L+1)) = O(n log n)` interactions, i.e. `O(L+1) = O(log n)`
parallel time; failure `≤ 1/n` is the with-high-probability guarantee.  The final `Post` is
`majorityStableEndpoint = phase2Consensus ∨ phase4Tie ∨ phase9Consensus ∨
phase10MajorityWitness` (stabilized at 2 ∨ at 4 ∨ at 9 ∨ reached 10's unanimity), the
stabilize-early branches threaded as disjuncts per the paper's structure.

**Surviving inputs** (all named hypotheses; zero axiom beyond
`[propext, Classical.choice, Quot.sound]`, zero `sorry`, zero `native_decide`):
the eleven `PhaseConvergenceW` instances `phases` (each proven in its file, carrying its own
per-phase drains — the `q`/`hstep` rates for 0/1/5/6/7/8, Phase 3's `hside` τ-uniform side
budget, Phase 5's `hConc`, the Lemma-5.2 clock floor); the chain maps `h_chain`
(`Post_i ⟹ Pre_{i+1}`, the deterministic structural bridges); the start `hx₀`; the closing
map `h_post` (`Post_10 ⟹ majorityStableEndpoint`); the scaling `ht`/`hC0`/`hδ`.  This is the
honest single-theorem statement of the campaign's Phase-D goal. -/
theorem time_headline_W
    {L K n C0 : ℕ}
    (init c₀ : Config (AgentState L K))
    (Cphase : Fin 11 → ℕ) (δ : Fin 11 → ℝ≥0)
    (phases : Fin 11 → PhaseConvergenceW (NonuniformMajority L K).transitionKernel)
    (ht : ∀ i, (phases i).t ≤ Cphase i * n * (L + 1))
    (hε : ∀ i, ((phases i).ε : ℝ≥0∞) ≤ (δ i : ℝ≥0∞))
    (h_chain : ∀ (i : Fin 11) (hi : i.val + 1 < 11),
        ∀ x, (phases i).Post x → (phases ⟨i.val + 1, hi⟩).Pre x)
    (hx₀ : (phases ⟨0, by omega⟩).Pre c₀)
    (h_post : ∀ c, (phases lastPhaseW).Post c →
        majorityStableEndpoint (L := L) (K := K) init c)
    (hC0 : ∀ i, Cphase i ≤ C0)
    (hδ : (∑ i, (δ i : ℝ≥0∞)) ≤ (1 / n : ℝ≥0∞)) :
    ((NonuniformMajority L K).transitionKernel ^ (∑ i, (phases i).t)) c₀
        {c | ¬ majorityStableEndpoint (L := L) (K := K) init c}
      ≤ (1 / n : ℝ≥0∞)
    ∧ (∑ i, (phases i).t) ≤ 11 * C0 * n * (L + 1) := by
  obtain ⟨h_bound, h_time, h_err⟩ :=
    time_composition_W init c₀ Cphase δ phases ht hε h_chain hx₀ h_post
  refine ⟨?_, ?_⟩
  · calc ((NonuniformMajority L K).transitionKernel ^ (∑ i, (phases i).t)) c₀
            {c | ¬ majorityStableEndpoint (L := L) (K := K) init c}
        ≤ (∑ i, ((phases i).ε : ℝ≥0∞)) := h_bound
      _ ≤ ∑ i, (δ i : ℝ≥0∞) := h_err
      _ ≤ (1 / n : ℝ≥0∞) := hδ
  · calc (∑ i, (phases i).t)
        ≤ (∑ i, Cphase i) * n * (L + 1) := h_time
      _ ≤ (11 * C0) * n * (L + 1) := by
          have hsum : (∑ i, Cphase i) ≤ 11 * C0 := by
            calc (∑ i : Fin 11, Cphase i)
                ≤ ∑ _i : Fin 11, C0 := Finset.sum_le_sum (fun i _ => hC0 i)
              _ = 11 * C0 := by simp [Finset.sum_const, Finset.card_univ, mul_comm]
          gcongr
      _ = 11 * C0 * n * (L + 1) := by ring

/-! ## Phase D-4 — the SEAM-CORRECTED 21-instance composition (`time_headline_W2`)

`ChainBridges` PROVED the ten `h_chain` bridges above are NOT pointwise implications: every
phase window pins agents to a single distinct `phase.val`, so `Post_i ∧ Pre_{i+1}` is
contradictory on any populated config (the bridge is the `advancePhase` epidemic, a genuine
TRANSITION, not a predicate implication).  The `h_chain` hypothesis of
`time_composition_W` is therefore satisfiable only vacuously (the empty config) — the
headline above is honest about carrying it as a named input, but the input cannot be
discharged against the real instances.

`SeamEpidemics.seamEpidemicW` repairs this by interposing, between each pair of work phases, a
SEAM phase that realises the inter-phase advance epidemic.  The corrected chain is the
21-instance interleave `[work₀, seam₀, work₁, seam₁, …, seam₉, work₁₀]`, on which the bridges
ARE now genuine pointwise implications:

* `work_i.Post ⟹ seam_i.Pre` : the work phase's `Post` carries the advance trigger
  (`advTriggered (p+1)` — at least one agent has advanced; this is the trigger-form tail that
  the work `Post` must expose, noted per work phase) and the `≥ p`-window; `seam_i.Pre` is
  exactly `allPhaseGe p n ∧ advTriggered (p+1)`.  TRUE pointwise.
* `seam_i.Post ⟹ work_{i+1}.Pre` : the seam's `Post` is the `≥ (p+1)`-window
  `allPhaseGe (p+1) n`; for `≥`-window work `Pre`s this is the identity, for exact-pin work
  `Pre`s it is recovered via `SeamEpidemics.allPhaseEq_of_ge_and_no_overshoot` under the named
  per-seam timing input `hNoOvershoot` (no agent overshot to `≥ p+2`).  TRUE pointwise modulo
  the named overshoot feeder (folded into the seam's `εovershoot`).

The composition is the SAME `composeW_n_phases`, now over `Fin 21`.  The budget is the
21-term sum `∑ (11 work + 10 seam) ε`; the horizon is `∑ (11 work + 10 seam) t`.

This contract theorem is the pure assembly arithmetic over the 21-instance family; the
seam instances and their trigger/overshoot feeders are supplied as `phases`/`h_chain` exactly
as the work instances and their drains are.  See `SeamEpidemics` for the generic seam and the
exact shapes of the two named gaps (`hDrift`, `hNoOvershoot`).
-/

/-- The last phase index `20 : Fin 21` (the final WORK phase `work₁₀` in the interleave). -/
private def lastPhaseW2 : Fin 21 := ⟨21 - 1, by omega⟩

/-- **Doty time composition — seam-corrected 21-instance assembly contract.**

Identical assembly to `time_composition_W`, now over the 21-instance interleave
`[work₀, seam₀, …, seam₉, work₁₀]`.  The `h_chain` hypothesis here is genuinely satisfiable
pointwise (the seams carry the advance epidemic; the work↔seam bridges are TRUE on populated
configs, unlike the work↔work bridges refuted in `ChainBridges`). -/
theorem time_composition_W2
    {L K n : ℕ}
    (init c₀ : Config (AgentState L K))
    (Cphase : Fin 21 → ℕ) (δ : Fin 21 → ℝ≥0)
    (phases : Fin 21 → PhaseConvergenceW (NonuniformMajority L K).transitionKernel)
    (ht : ∀ i, (phases i).t ≤ Cphase i * n * (L + 1))
    (hε : ∀ i, ((phases i).ε : ℝ≥0∞) ≤ (δ i : ℝ≥0∞))
    (h_chain : ∀ (i : Fin 21) (hi : i.val + 1 < 21),
        ∀ x, (phases i).Post x → (phases ⟨i.val + 1, hi⟩).Pre x)
    (hx₀ : (phases ⟨0, by omega⟩).Pre c₀)
    (h_post : ∀ c, (phases lastPhaseW2).Post c →
        majorityStableEndpoint (L := L) (K := K) init c) :
    ((NonuniformMajority L K).transitionKernel ^ (∑ i, (phases i).t)) c₀
        {c | ¬ majorityStableEndpoint (L := L) (K := K) init c}
      ≤ (∑ i, ((phases i).ε : ℝ≥0∞))
    ∧ (∑ i, (phases i).t) ≤ (∑ i, Cphase i) * n * (L + 1)
    ∧ (∑ i, ((phases i).ε : ℝ≥0∞)) ≤ ∑ i, (δ i : ℝ≥0∞) := by
  refine ⟨?_, ?_, ?_⟩
  · have h_compose :=
      composeW_n_phases (K := (NonuniformMajority L K).transitionKernel)
        (m := 21) (by omega) phases h_chain c₀ hx₀
    have h_subset :
        {c | ¬ majorityStableEndpoint (L := L) (K := K) init c}
          ⊆ {c | ¬ (phases ⟨21 - 1, by omega⟩).Post c} := by
      intro c hc
      simp only [Set.mem_setOf_eq] at hc ⊢
      intro hPost
      exact hc (h_post c hPost)
    calc ((NonuniformMajority L K).transitionKernel ^ (∑ i, (phases i).t)) c₀
            {c | ¬ majorityStableEndpoint (L := L) (K := K) init c}
        ≤ ((NonuniformMajority L K).transitionKernel ^ (∑ i, (phases i).t)) c₀
            {c | ¬ (phases ⟨21 - 1, by omega⟩).Post c} := measure_mono h_subset
      _ ≤ (∑ i, ((phases i).ε : ℝ≥0∞)) := h_compose
  · exact total_time_le_W (fun i => (phases i).t) Cphase ht
  · exact total_error_le_W (fun i => (phases i).ε) δ hε

/-- **`time_headline_W2` — the SEAM-CORRECTED eleven-work + ten-seam composition headline
(UNCONDITIONAL beyond the named-input surface).**

The Phase-D-4 deliverable.  Replaces the work↔work `h_chain` of `time_headline_W` (refuted
pointwise in `ChainBridges`) by the 21-instance interleave whose bridges ARE genuine pointwise
implications.  If every per-phase constant satisfies `Cphase i ≤ C0` and the 21-term error
budget is `∑ δ ≤ 1/n`, the composed chain reaches `majorityStableEndpoint init` within
`T ≤ 21·C0·n·(L+1)` interactions with failure probability `≤ 1/n`.

`T ≤ 21·C0·n·(L+1) = O(n log n)` interactions (`O(L+1) = O(log n)` parallel time); failure
`≤ 1/n` is whp.  The interleave constant doubles `11 → 21` but the asymptotics are unchanged
(each seam is one `O(n·(L+1))` advance epidemic, same order as a work phase).

**Surviving inputs** (all named hypotheses; zero axiom beyond
`[propext, Classical.choice, Quot.sound]`, zero `sorry`, zero `native_decide`):
the 11 WORK `PhaseConvergenceW` instances (each proven in its file with its own drains, plus —
where the work `Post` does not already expose it — the advance-trigger strengthening
`advTriggered (p+1)`, noted per work phase); the 10 SEAM instances
`SeamEpidemics.seamEpidemicW` (each carrying its two named feeders `hDrift` = generic-`p`
advance-epidemic drift and `εovershoot`/`hNoOvershoot` = per-seam timing separation); the
21-term chain maps `h_chain` (work↔seam, TRUE pointwise per `SeamEpidemics`); the start `hx₀`;
the closing map `h_post`; the scaling `ht`/`hC0`/`hδ`.  This is the honest seam-corrected
single-theorem statement of the campaign's Phase-D goal. -/
theorem time_headline_W2
    {L K n C0 : ℕ}
    (init c₀ : Config (AgentState L K))
    (Cphase : Fin 21 → ℕ) (δ : Fin 21 → ℝ≥0)
    (phases : Fin 21 → PhaseConvergenceW (NonuniformMajority L K).transitionKernel)
    (ht : ∀ i, (phases i).t ≤ Cphase i * n * (L + 1))
    (hε : ∀ i, ((phases i).ε : ℝ≥0∞) ≤ (δ i : ℝ≥0∞))
    (h_chain : ∀ (i : Fin 21) (hi : i.val + 1 < 21),
        ∀ x, (phases i).Post x → (phases ⟨i.val + 1, hi⟩).Pre x)
    (hx₀ : (phases ⟨0, by omega⟩).Pre c₀)
    (h_post : ∀ c, (phases lastPhaseW2).Post c →
        majorityStableEndpoint (L := L) (K := K) init c)
    (hC0 : ∀ i, Cphase i ≤ C0)
    (hδ : (∑ i, (δ i : ℝ≥0∞)) ≤ (1 / n : ℝ≥0∞)) :
    ((NonuniformMajority L K).transitionKernel ^ (∑ i, (phases i).t)) c₀
        {c | ¬ majorityStableEndpoint (L := L) (K := K) init c}
      ≤ (1 / n : ℝ≥0∞)
    ∧ (∑ i, (phases i).t) ≤ 21 * C0 * n * (L + 1) := by
  obtain ⟨h_bound, h_time, h_err⟩ :=
    time_composition_W2 init c₀ Cphase δ phases ht hε h_chain hx₀ h_post
  refine ⟨?_, ?_⟩
  · calc ((NonuniformMajority L K).transitionKernel ^ (∑ i, (phases i).t)) c₀
            {c | ¬ majorityStableEndpoint (L := L) (K := K) init c}
        ≤ (∑ i, ((phases i).ε : ℝ≥0∞)) := h_bound
      _ ≤ ∑ i, (δ i : ℝ≥0∞) := h_err
      _ ≤ (1 / n : ℝ≥0∞) := hδ
  · calc (∑ i, (phases i).t)
        ≤ (∑ i, Cphase i) * n * (L + 1) := h_time
      _ ≤ (21 * C0) * n * (L + 1) := by
          have hsum : (∑ i, Cphase i) ≤ 21 * C0 := by
            calc (∑ i : Fin 21, Cphase i)
                ≤ ∑ _i : Fin 21, C0 := Finset.sum_le_sum (fun i _ => hC0 i)
              _ = 21 * C0 := by simp [Finset.sum_const, Finset.card_univ, mul_comm]
          gcongr
      _ = 21 * C0 * n * (L + 1) := by ring

/-! ## Phase D-4d — `hDrift(p)` DISCHARGED: the seam consumption form (append-only note)

`time_headline_W2` consumes its ten seam instances POLYMORPHICALLY, through the abstract
`phases : Fin 21 → PhaseConvergenceW …` array — it does not itself carry `hDrift` as a separate
hypothesis.  Phase D-4 left the seam slot fillable only by `SeamEpidemics.seamEpidemicW`, which
carries an UNDISCHARGED `hDrift` feeder (the generic-`p` advance-epidemic convergence bound).

Phase D-4d **discharges that feeder**.  `SeamEpidemics.seam_drift` proves the exact `hDrift`
shape by cloning the Phase-4 non-tie epidemic at an arbitrary phase parameter `p` (informed =
`phase ≥ p+1`, count `geCount (p+1)`, spread by the public phase-`max` lemmas
`Transition_{left,right}_phase_ge_pair_max`, genuine drift rate
`r = 1 − ((n−1)/(n(n−1)))·(1 − e^{−s})` via `windowDrift_PhaseConvergence`).  The packaged seam
`SeamEpidemics.seamEpidemicW_calibrated p n t hn s hs εepidemic εovershoot hε` then has the SAME
`Pre`/`Post`/`t`/`ε` profile (`@[simp]` projection lemmas
`seamEpidemicW_calibrated_{Pre,Post,t,eps}`) as `seamEpidemicW` but with NO undischarged `hDrift`
— its only quantitative input is the explicit geometric-tail check `hε` (the Phase-4-shape
`r^t · exp(s·(n−1)) ≤ εepidemic`), exactly mirroring `Phase4Convergence.phase4Convergence`'s `hε`.

**Consumption form.**  A caller assembling the 21-instance `phases` array now plugs
`SeamEpidemics.seamEpidemicW_calibrated pᵢ n tᵢ hn s hs εᵢ εovᵢ hεᵢ` into each of the ten seam
slots.  The headline's `ht`/`hε`/`h_chain` obligations on those slots read off the calibrated
seam's projections (`t = tᵢ`, `ε = εᵢ + εovᵢ`, `Pre = allPhaseGe pᵢ n ∧ advTriggered (pᵢ+1)`,
`Post = allPhaseGe (pᵢ+1) n`); the work↔seam bridges `h_chain` use
`SeamEpidemics.{exact_work_into_seam, ge_work_into_seam, seam_into_exact_work}` exactly as before.
**Result:** `hDrift` LEAVES the surviving-input list of `time_headline_W2`.  The remaining
seam-side named input is `hNoOvershoot` (per-seam timing separation, folded into `εovershoot`),
still carried; `εepidemic` is now a derived quantity bounded by `hε`, not an unconstrained gap.

The headline signature is unchanged (it was already polymorphic over `phases`); this note records
the consumption form so the assembly does not silently reopen the discharged feeder. -/

end ExactMajority
