# DOCTRINE — Fill Theorem31.time_bound (the 1 sorry)

## Goal

`Theorem31.time_bound` (Theorem31.lean): clean-signature Theorem 3.1 time bound.
Fill the sorry by instantiating all parameters of
`Theorem31.theorem_3_1_unconditional_final` from
`Regime + validInitial + card`.

Terminal condition: `lake build Theorem31` green, 0 sorry, clean 3.

## Constraint

Must go through `theorem_3_1_unconditional_final` (TerminalAssemblyR).
The FaithfulWorkSeamCore / Assembly' path is BLOCKED (false hNoOvershoot).

## Avenue (a): field-by-field instantiation via ConcreteInstantiation

Grind the 7 sorry in ConcreteInstantiation.lean, then assemble into
Theorem31.time_bound. Attack order:

| # | piece | difficulty |
|---|-------|-----------|
| 1 | SlotInputsConcrete (non-Phase3 slots) | MEDIUM |
| 2 | Phase3Package | HARD |
| 3 | Seam params (seamT, εovershoot) | EASY |
| 4 | SeamEntryFromWorkPost (10 per-seam) | HARD |
| 5 | TerminalReachableOvershootResidual | MEDIUM |
| 6 | TerminalSeamTieResidual | MEDIUM |
| 7 | Per-phase ht/hε bounds | MEDIUM |

## Avenue (b): direct TerminalAssemblyR construction

Skip ConcreteAProducerInputs. Build TerminalAssemblyR + terminalWork
directly from the Phase convergence files. Fewer layers but more manual.

## Discovered structural gap: Slot 4 hPostEq

`TerminalSeamTieResidual.hPostEq` requires `∀ c, work[k].Post c → allPhaseEq (seamP k) n c`.
For k=4, `work[4].Post = Phase4Post = card n ∧ (StableTie4 ∨ advFinished n)`.
The `advFinished` branch means all agents phase ≥ 5, NOT allPhaseEq 4 or 5.

Neither `seamP 4 = 4` nor `seamP 4 = 5` makes hPostEq provable for both branches.

For REACHABLE configs, `Q4 + advFinished` implies `allPhaseEq 5` (Phase4Transition
max output = 5). But `hPostEq` is blanket `∀ c` without reachability restriction.

Fix options:
(A) Add `Reachable c₀ c` to hPostEq (like hPreEq already has) — requires modifying
    TerminalSeamTieResidual + terminalAssembly + exactIfReset consumer
(B) Strengthen Phase4Post to carry `∀ a ∈ c, a.phase.val ≤ 5` explicitly
(C) Split Phase 4 into tie/non-tie sub-slots

This is a CODE CHANGE, not a wiring fix. Pick one and implement.

## Tools

ChatGPT family1/2/3, Codex subagents, uisai2 remote builds.

## Discovered: Slot 0 Phase 0 model mismatch

The current `uniformRoleSplitMilestoneInstance` models Phase 0 as a pure
MCR+MCR coalescent (Janson milestone, O(n²) interactions). But the paper's
Phase 0 (Lemma 5.1/5.2) uses ONE-SIDED conversion reactions that give
O(n log n) interactions = O(log n) parallel time.

Fix: replace the milestone model with the paper's Lemma 5.1 population-split
analysis. This is not a wiring fix — it's a different probability proof.

## Overshoot tail: existing machinery found

SeamPairAdapter.lean has:
- seam_atRiskClockZero_tail_honest (tseam ≤ n(L+1), target exp(-40(L+1)))
- seam_atRiskClockZero_tail_honest_wide (tseam ≤ 12n(L+1), target exp(-5(L+1)))
- seam_noOvershoot_tail_honest (wraps into full tail)

CounterResetDest (p+1) = {1,6,7,8} means honest tail only for seams 0,5,6,7.
Other seams need different arguments or the generic SeamNoOvershoot path.
