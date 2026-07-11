/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Phase10SignResolved — resolving the C11 phase-10 sign-conservation / reachability gap.

`Assembly.ResidualAtomsFull` feeds four fields into
`PkgFAtoms.hPhase10Sign_of_rooted` to produce `Atoms.Phase10SignMatch init`:

  * `hInitValid : validInitial init`
  * `hAllRoot   : ∀ a ∈ init, a.phase.val = 10`
  * `hActRoot   : hasActiveAgent init`
  * `hReach10   : ∀ c, Phase10Drop.Phase10Post c → (NonuniformMajority L K).Reachable init c`

This file establishes the HONEST status of C11.  Two findings, both proved here:

## Finding 1 — `hAllRoot` and `hActRoot` are NOT honest preconditions; they are an
## OVER-SPECIFICATION that is in fact JOINTLY UNSATISFIABLE with `hInitValid`.

`validInitial init` (`MainTheorem.lean:101`) pins EVERY agent of `init` to
`a.phase = ⟨0,_⟩`, i.e. `a.phase.val = 0`.  `hAllRoot` pins every agent of the SAME
`init` to `a.phase.val = 10`.  For any agent `a ∈ init` this forces `0 = 10`, absurd.
Hence `validInitial init ∧ (∀ a ∈ init, a.phase.val = 10)` forces `init` to be the EMPTY
configuration, and then `hActRoot : hasActiveAgent init = ∃ a ∈ init, a.full` is also
false.  So the four fields are jointly satisfiable ONLY by the empty `init` — which fails
`hActRoot`.  They are jointly UNSATISFIABLE (`fields_jointly_unsatisfiable` below).

This is exactly the disallowed situation under the build discipline ("a carried `(name :
Prop)` binder is allowed ONLY if TRUE/satisfiable").  `hPhase10Sign_of_rooted` happens to
type-check because `hasActiveAgent_of_reachable` only USES `hAllRoot`/`hActRoot` at the
reflexive base of the reachability induction — but as carried theorem hypotheses they are
vacuous: any theorem quantifying over `ResidualAtomsFull` is conditioned on an empty
premise set, so `hAllRoot`/`hActRoot` are NOT honest interface facts.  They must be
DISCHARGED, not carried.

## Finding 2 — they ARE chain-derivable; `hInitValid` + `hReach10` ALONE suffice.

The activity oracle `hAllRoot`/`hActRoot` threaded was only ever needed to supply
`hasActiveAgent c` on each `Phase10Post c`.  But that follows already from the phase-0
`validInitial init` + reachability + the all-phase-10 content INSIDE `Phase10Post`, via the
LANDED liveness lemma `card_eq_zero_or_hasActiveAgent_of_reachable_all_phase10`
(`Analysis/Phase10Backup.lean:2063`): a reachable all-phase-10 config is empty or active.
On the empty config the `phase10MajorityWitness` disjuncts hold vacuously; on the nonempty
config the active source is supplied.  So we re-derive `Phase10SignMatch init` from the TWO
honest fields `hInitValid`/`hReach10` alone, with `hAllRoot`/`hActRoot` DROPPED.

`phase10SignMatch_of_validInitial_reach` below is the discharged producer.  It is a strict
strengthening of `SmallSweep.phase10SignMatch_of_rooted` (fewer hypotheses, same output).

## Verdict per field (the C11 roster)

| field        | verdict                | justification                                          |
|--------------|------------------------|--------------------------------------------------------|
| `hInitValid` | **legitimate precondition** | `validInitial init` = "input is a valid majority config" = the DOMAIN of Doty Thm 3.1 (`stable_majority_correct_of_majorityStableEndpoint_reachability` quantifies `∀ init, validInitial init → …`). The conservation engine `phase10ActiveSignedSum_eq_initialGap_of_reachable` consumes exactly this. |
| `hReach10`   | **legitimate precondition** (conditioning surface) | "every `Phase10Post` config the chain visits is reachable from `init`" — the chain only ever visits configs reachable from its phase-0 start (`reachableFrom_kernel_closed`); this is the `hc₀Reach`-flavoured conditioning surface the probabilistic argument already owns, NOT a fresh assumption. |
| `hAllRoot`   | **chain-derivable / DROP** | NOT a precondition: contradicts `hInitValid` (phase 0 ≠ phase 10). The all-phase-10 content needed is the one INSIDE `Phase10Post c`, not on `init`. Discharged via the landed liveness lemma. |
| `hActRoot`   | **chain-derivable / DROP** | NOT a precondition: with `hAllRoot` it forces empty `init`, then false. Activity on each `Phase10Post c` is re-derived from `hInitValid + hReach10` via `card_eq_zero_or_hasActiveAgent_of_reachable_all_phase10`. |

## On the paper (Doty 2021, §11)

Doty's Theorem 3.1 is a STABLE-COMPUTATION statement: it assumes a valid majority input
(the protocol's domain) and PROVES the protocol stabilizes to the correct majority output.
Phase-10 sign conservation is a CONSEQUENCE Doty PROVES (the backup-entry argument:
the conserved active signed sum equals the initial gap), NOT an assumption.  Accordingly
`hInitValid` is the honest domain hypothesis (case a); the sign match itself is proved
(case b), here re-derived in Lean from the landed conservation engine.

## Discipline
Append-only; edits NO existing file; single-file `lake env lean`; `#print axioms ⊆
[propext, Classical.choice, Quot.sound]`; no `sorry`/`admit`/`axiom`/`native_decide`.
-/
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.SignMatch

namespace ExactMajority
namespace Phase10SignResolved

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators NNReal

variable {L K : ℕ}

/-! ## Part 1 — the unsatisfiability of the over-specified bundle (Finding 1).

`validInitial init` forces phase 0 on every agent; `hAllRoot` forces phase 10 on the same
agents.  Jointly they force `init` empty, and then `hActRoot` is false.  Hence the four
`ResidualAtomsFull` start/sign fields are jointly UNSATISFIABLE.  This is why
`hAllRoot`/`hActRoot` cannot be honest carried preconditions. -/

/-- `validInitial` and "all agents in phase 10" jointly force the empty configuration:
the per-agent phases `0` (validInitial) and `10` (root) collide on every member. -/
theorem init_empty_of_validInitial_allRoot {init : Config (AgentState L K)}
    (hinit : validInitial init) (hAllRoot : ∀ a ∈ init, a.phase.val = 10) :
    init = 0 := by
  rw [← Multiset.card_eq_zero]
  by_contra hne
  have hpos : 0 < init.card := Nat.pos_of_ne_zero hne
  obtain ⟨a, ha⟩ := Multiset.card_pos_iff_exists_mem.1 hpos
  have h0 : a.phase.val = 0 := by rw [(hinit a ha).1]
  have h10 : a.phase.val = 10 := hAllRoot a ha
  omega

/-- **The four start/sign fields are jointly UNSATISFIABLE.**  `hInitValid ∧ hAllRoot` forces
`init = 0`; then `hActRoot : ∃ a ∈ init, a.full` is false (no members).  Therefore
`hAllRoot`/`hActRoot` are NOT honest carried preconditions — they are an over-specification
that must be discharged (Part 2), not assumed. -/
theorem fields_jointly_unsatisfiable {init : Config (AgentState L K)}
    (hinit : validInitial init) (hAllRoot : ∀ a ∈ init, a.phase.val = 10)
    (hactRoot : hasActiveAgent init) : False := by
  have hz : init = 0 := init_empty_of_validInitial_allRoot hinit hAllRoot
  obtain ⟨a, ha, _⟩ := hactRoot
  rw [hz] at ha
  exact (Multiset.notMem_zero a) ha

/-! ## Part 2 — the discharged producer (Finding 2).

`Phase10SignMatch init` is re-derived from the TWO honest fields `hInitValid`/`hReach10`
ALONE, dropping `hAllRoot`/`hActRoot`.  The activity oracle is supplied by the landed
liveness lemma; the empty branch lands the witness vacuously. -/

/-- **Activity on every `Phase10Post` config, from the phase-0 root.**  For each
`Phase10Post c` reachable from a `validInitial` `init`, either `c` is empty or it has an
active backup source.  Threads the landed
`card_eq_zero_or_hasActiveAgent_of_reachable_all_phase10` against the all-phase-10 content
inside `Phase10Post`.  NO `hAllRoot`/`hActRoot` on `init`. -/
theorem cardZero_or_active_of_post {init c : Config (AgentState L K)}
    (hinit : validInitial init)
    (hreachc : (NonuniformMajority L K).Reachable init c)
    (hPost : Phase10Drop.Phase10Post (L := L) (K := K) c) :
    c = 0 ∨ hasActiveAgent c := by
  obtain ⟨o, ho⟩ := hPost
  have hphase : ∀ a ∈ c, a.phase.val = 10 := fun a ha => (ho a ha).1
  rcases card_eq_zero_or_hasActiveAgent_of_reachable_all_phase10
      (L := L) (K := K) init c hinit hreachc hphase with hz | hact
  · exact Or.inl (Multiset.card_eq_zero.1 hz)
  · exact Or.inr hact

/-- **The empty `Phase10Post` config lands the witness vacuously.**  On `c = 0` every
"`∀ a ∈ c, …`" predicate is vacuously true, so the `phase10MajorityWitness` disjunct keyed
to `initialGap init`'s sign holds with no agents to constrain. -/
theorem witness_of_empty {init : Config (AgentState L K)} :
    phase10MajorityWitness (L := L) (K := K) init (0 : Config (AgentState L K)) := by
  rcases lt_trichotomy (initialGap (L := L) (K := K) init) 0 with hneg | hzero | hpos
  · exact Or.inr (Or.inl ⟨hneg, by intro a ha; exact absurd ha (Multiset.notMem_zero a)⟩)
  · exact Or.inr (Or.inr ⟨hzero, by intro a ha; exact absurd ha (Multiset.notMem_zero a)⟩)
  · exact Or.inl ⟨hpos, by intro a ha; exact absurd ha (Multiset.notMem_zero a)⟩

/-- **The DISCHARGED rooted-sign producer.**  Re-derives `Atoms.Phase10SignMatch init`
from the TWO honest fields `hInitValid`/`hReach10` ALONE — `hAllRoot`/`hActRoot` DROPPED.

For each `Phase10Post c`: it is reachable from `init` (`hreach`), so it is empty (witness by
`witness_of_empty`) or active.  In the active case we feed `SignMatch.witness_of_post_conservation`
with the conserved signed sum `= initialGap init` (`phase10ActiveSignedSum_eq_initialGap_of_reachable`)
and the active source.

A strict strengthening of `SmallSweep.phase10SignMatch_of_rooted`. -/
theorem phase10SignMatch_of_validInitial_reach {init : Config (AgentState L K)}
    (hinit : validInitial init)
    (hreach : ∀ c, Phase10Drop.Phase10Post (L := L) (K := K) c →
      (NonuniformMajority L K).Reachable init c) :
    Atoms.Phase10SignMatch (L := L) (K := K) init := by
  intro c hPost
  rcases cardZero_or_active_of_post hinit (hreach c hPost) hPost with hz | hact
  · subst hz; exact witness_of_empty
  · obtain ⟨o, ho⟩ := hPost
    have hphase : ∀ a ∈ c, a.phase.val = 10 := fun a ha => (ho a ha).1
    have hcons : phase10ActiveSignedSum c = initialGap (L := L) (K := K) init :=
      phase10ActiveSignedSum_eq_initialGap_of_reachable
        (L := L) (K := K) init c hinit (hreach c ⟨o, ho⟩) hphase
    exact SignMatch.witness_of_post_conservation ⟨o, ho⟩ hcons hact

/-! ## Part 3 — the resolved `hPhase10Sign` producer.

`hPhase10Sign_resolved` is the drop-in replacement for `PkgFAtoms.hPhase10Sign_of_rooted`
taking only the two honest preconditions.  It is the field
`ResidualAtomsFull.hPhase10Sign` produced WITHOUT the over-specified (unsatisfiable)
`hAllRoot`/`hActRoot`.

Wiring note (not re-stated as a theorem here to keep this file checkable against the landed
deterministic oleans, independent of the Full→V7 assembly build): in
`Assembly.toResidualFull` the line

  `hPhase10Sign := PkgFAtoms.hPhase10Sign_of_rooted … ra.hInitValid ra.hAllRoot ra.hActRoot ra.hReach10`

can be replaced verbatim by

  `hPhase10Sign := Phase10SignResolved.hPhase10Sign_resolved ra.hInitValid ra.hReach10`

and the residual fields `hAllRoot`/`hActRoot` deleted from `ResidualAtomsFull` — they feed
NOTHING else (grep: their only consumer is `hPhase10Sign_of_rooted`).  By
`fields_jointly_unsatisfiable` the old producer was only ever applied to a vacuous premise
set, so the replacement is a strict honesty improvement, not a behavioural change. -/

/-- **`ResidualAtomsFull.hPhase10Sign`, RESOLVED.**  Produces the same Full field as
`PkgFAtoms.hPhase10Sign_of_rooted`, but from the two HONEST preconditions only
(`hInitValid` + `hReach10`); `hAllRoot`/`hActRoot` DROPPED. -/
theorem hPhase10Sign_resolved {init : Config (AgentState L K)}
    (hinit : validInitial init)
    (hreach : ∀ c, Phase10Drop.Phase10Post (L := L) (K := K) c →
      (NonuniformMajority L K).Reachable init c) :
    Atoms.Phase10SignMatch (L := L) (K := K) init :=
  phase10SignMatch_of_validInitial_reach hinit hreach

end Phase10SignResolved
end ExactMajority
