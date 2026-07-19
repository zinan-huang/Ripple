/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# FaithfulCoreDischarge — discharging the `FaithfulCore` residual fields.

This append-only file edits NO existing file.  It discharges the two FaithfulCore fields the
prompt flags as the clean, finishable wins, and PRECISELY ISOLATES the genuinely-remaining
probabilistic content into a smaller, refutation-clean residual core.

## What is discharged here (the honest accounting)

### Field `hcard : Multiset.card c₀ = n` — DISCHARGED by DEFINITION.
`n` is the population size of the start.  We fold `n := Multiset.card c₀`, so `hcard` is `rfl`.
Trivial; no probability.

### Field `hReach10 : ∀ c, Phase10Post c → Reachable c₀ c` — REMOVED (false universal) and
replaced by the TRUE chain-restricted form, used only a.e. on the chain.

The literal universal is FALSE: an ad-hoc `Phase10Post` config need NOT be reachable from `c₀`.
But it enters the headline ONLY through the final measure bound, where the bad set
`{c | ¬ majorityStableEndpoint c₀ c}` is integrated against `(K^T) c₀`.  By
`nonuniformTransitionKernel_pow_eq_zero_of_forall_not_reachable`, the chain a.e. visits only
configs reachable from `c₀`, so the part of the bad set that is NOT reachable contributes ZERO.
On the reachable part, the closing sign-match map needs reachability of `c` — which, since
`init := c₀`, is EXACTLY the hypothesis we already have (`Reachable c₀ c`).  So the TRUE
chain-restricted reachability `∀ c, Reachable c₀ c → Phase10Post c → Reachable c₀ c` is
`fun _ h _ => h` — DISCHARGED to a tautology — and the headline is reproved WITHOUT ever
asserting the false universal.  This is the prompt's "show the field is only used a.e. on the
chain" route, made concrete: the reachable-vs-not split, with the not-reachable part = 0.

### The reduced residual core `FaithfulWorkSeamCore` — the PRECISELY-ISOLATED remainder.

Everything else FaithfulCore carries — the 11 work instances, the window-shape ties, the slot-0/
slot-10 bridges, the §10 seam-entry concentration scalars, the seed events — is the genuine
remaining paper-probability content (NOT discharged here; see the isolation note at the bottom).
We bundle it WITHOUT `hReach10` and WITHOUT `hcard` (both discharged above) into
`FaithfulWorkSeamCore`, and build the headline from it.

## ANTI-TRAP compliance
NO false universal carried (`hReach10` is REMOVED, replaced by the chain-restricted tautology).
NO `InvClosed`.  NO bare-universal floor.  The reachable split is the PROVEN
`nonuniformTransitionKernel_pow_eq_zero_of_forall_not_reachable`.  The remaining work/seam content
is carried in `FaithfulWorkSeamCore`, every field refutation-checked TRUE-shaped (inherited
verbatim from `FaithfulCore`'s already-isolated fields).

## Discipline
Append-only; edits NO existing file; single-file `lake env lean`; `#print axioms ⊆ [propext,
Classical.choice, Quot.sound]`; no `sorry`/`admit`/`axiom`/`native_decide`.
-/
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.FaithfulWitness

namespace ExactMajority
namespace FaithfulCoreDischarge

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators NNReal

variable {L K : ℕ}

/-! ## Part 1 — the chain-restricted reachability tautology (the honest `hReach10` route).

`hReach10` enters the headline ONLY through the final measure bound.  Restricted to the chain
(configs reachable from `c₀`), with `init := c₀`, it is a tautology. -/

/-- **The TRUE chain-restricted reachability — a tautology.**  Restricting `hReach10`'s universal
to configs already reachable from `c₀` (which, by the a.e.-reachability of the chain, is the ONLY
part of the bad set with positive measure) makes it `Reachable c₀ c → Phase10Post c →
Reachable c₀ c`, discharged by the first hypothesis.  This is the honest replacement for the false
literal universal. -/
theorem reach10_chain_restricted (c₀ : Config (AgentState L K)) :
    ∀ c, (NonuniformMajority L K).Reachable c₀ c →
      Phase10Drop.Phase10Post (L := L) (K := K) c →
      (NonuniformMajority L K).Reachable c₀ c :=
  fun _ hreach _ => hreach

/-! ## Part 2 — the chain-restricted bad-set bound.

The composition delivers `(K^T) c₀ {¬ (phases 20).Post} ≤ ∑ ε`.  We lift it to the
`majorityStableEndpoint` bad set WITHOUT the false universal, by splitting the bad set into its
reachable and non-reachable parts: the non-reachable part has measure ZERO
(`nonuniformTransitionKernel_pow_eq_zero_of_forall_not_reachable`), and on the reachable part the
closing map needs only the chain-restricted reachability tautology. -/

/-- **The single-config majority witness, from reachability of THAT config alone.**  This is the
body of `Phase10SignResolved.phase10SignMatch_of_validInitial_reach` SPECIALIZED to one config `c`:
it needs reachability of `c` ONLY (not the false universal over all `Phase10Post` configs).  For a
reachable `Phase10Post c` it is empty (vacuous witness) or active (conserved gap-sign), so it lands
the `phase10MajorityWitness init c` disjunct.  This is exactly why the universal `hReach10` is NOT
needed: the producer's work is pointwise, and the only configs with positive measure are reachable. -/
theorem majorityWitness_of_reachable_post {init c : Config (AgentState L K)}
    (hinit : validInitial init)
    (hreach : (NonuniformMajority L K).Reachable init c)
    (hPost : Phase10Drop.Phase10Post (L := L) (K := K) c) :
    phase10MajorityWitness (L := L) (K := K) init c := by
  rcases Phase10SignResolved.cardZero_or_active_of_post hinit hreach hPost with hz | hact
  · subst hz; exact Phase10SignResolved.witness_of_empty
  · obtain ⟨o, ho⟩ := hPost
    have hphase : ∀ a ∈ c, a.phase.val = 10 := fun a ha => (ho a ha).1
    have hcons : phase10ActiveSignedSum c
        = initialGap (L := L) (K := K) init :=
      phase10ActiveSignedSum_eq_initialGap_of_reachable
        (L := L) (K := K) init c hinit (hreach) hphase
    exact SignMatch.witness_of_post_conservation ⟨o, ho⟩ hcons hact

/-- **The closing map, RELATIVIZED to the chain.**  Every REACHABLE final-`Post` config is a
`majorityStableEndpoint c₀` — built WITHOUT the false universal `hReach10`, using only the
reachability of the config at hand (the prompt's "used only a.e. on the chain" route).  `init := c₀`
makes the supplied reachability `Reachable c₀ c` discharge the producer's per-config reachability. -/
theorem hpost_on_reachable {n C0 : ℕ}
    (ra : Capstone.ResidualAtomsFaithful (L := L) (K := K) n C0)
    (hinit : validInitial ra.init)
    (hceq : ra.c₀ = ra.init)
    (hSlot10Post : ∀ c, (ra.work ⟨10, by omega⟩).Post c →
      Phase10Drop.Phase10Post (L := L) (K := K) c) :
    ∀ c, (NonuniformMajority L K).Reachable ra.c₀ c →
      (Capstone.phases ra ⟨21 - 1, by omega⟩).Post c →
      majorityStableEndpoint (L := L) (K := K) ra.init c := by
  intro c hreach hPost
  have hP10 : Phase10Drop.Phase10Post (L := L) (K := K) c :=
    Capstone.slot20_post ra hSlot10Post hPost
  have hreach' : (NonuniformMajority L K).Reachable ra.init c := hceq ▸ hreach
  exact Or.inr (Or.inr (Or.inr (majorityWitness_of_reachable_post hinit hreach' hP10)))

/-! ## Part 3 — `FaithfulWorkSeamCore`: the PRECISELY-ISOLATED residual (NO `hReach10`, NO `hcard`).

This is `FaithfulCore` with the two discharged fields REMOVED.  It carries the genuine remaining
paper-probability content — the 11 work instances, the window/slot bridges, and the §10 seam-entry
concentration scalars — and NOTHING false.  We assemble it as a `Assembly'` (the work/seam
content) plus the slot-0 / slot-10 bridges + the `validInitial` domain, and prove the headline. -/

/-- **`FaithfulWorkSeamCore` — the residual after the two clean discharges.**  Bundles the
work/seam assembly (`Assembly'`, carrying the 11 work instances + the §10 seam concentration
glue), the slot-0 entry bridge (`hStart`), the slot-10→`Phase10Post` bridge, and the `validInitial`
domain hypothesis.  This is EXACTLY `FaithfulCore` minus `hReach10` (the false universal, discharged
via the chain-restriction in Part 2) and minus `hcard` (folded to `n := card c₀`). -/
structure FaithfulWorkSeamCore (n : ℕ) (c₀ : Config (AgentState L K)) where
  asm : SeedTrigWiring.Assembly' (L := L) (K := K) n
  hStart : (asm.work ⟨0, by omega⟩).Pre c₀
  hSlot10Post : ∀ c, (asm.work ⟨10, by omega⟩).Post c →
    Phase10Drop.Phase10Post (L := L) (K := K) c
  hValid : validInitial c₀

set_option maxHeartbeats 2000000 in
/-- **The chain-restricted closing map for a bare `Assembly'` (`init := c₀`).**  Every
config reachable from `c₀` whose final-phase `Post` holds is a `majorityStableEndpoint c₀` — built
from the per-config reachability ONLY (no false universal). -/
theorem hpost_on_reachable_asm {n : ℕ}
    (asm : SeedTrigWiring.Assembly' (L := L) (K := K) n)
    (c₀ : Config (AgentState L K)) (hValid : validInitial c₀)
    (hSlot10Post : ∀ c, (asm.work ⟨10, by omega⟩).Post c →
      Phase10Drop.Phase10Post (L := L) (K := K) c) :
    ∀ c, (NonuniformMajority L K).Reachable c₀ c →
      (SeedTrigWiring.phases' asm ⟨21 - 1, by omega⟩).Post c →
      majorityStableEndpoint (L := L) (K := K) c₀ c := by
  intro c hreach hPost
  -- reduce `phases' asm 20 .Post c` to `asm.work ⟨10⟩ .Post c` (slot 20 is `work₁₀`).
  have hP10 : Phase10Drop.Phase10Post (L := L) (K := K) c := by
    have heq : (SeedTrigWiring.phases' asm ⟨21 - 1, by omega⟩).Post c
        = (asm.work ⟨10, by omega⟩).Post c := by
      rw [SeedTrigWiring.phases'_even _ _ (by rfl)]
      show (asm.work (ConcreteAssembly.workIdx ⟨21 - 1, by omega⟩)).Post c
          = (asm.work ⟨10, by omega⟩).Post c
      rw [show ConcreteAssembly.workIdx ⟨21 - 1, by omega⟩ = (⟨10, by omega⟩ : Fin 11) from by
        apply Fin.ext; norm_num [ConcreteAssembly.workIdx]]
    exact hSlot10Post c (heq ▸ hPost)
  exact Or.inr (Or.inr (Or.inr (majorityWitness_of_reachable_post hValid hreach hP10)))

/-! ## Part 4 — the chain-restricted error bound.

The composition delivers `(K^T) c₀ {¬ (phases 20).Post} ≤ ∑ ε`.  We lift it to the
`majorityStableEndpoint c₀` bad set WITHOUT the false universal, by the subset
`{¬ maj} ⊆ {¬ (phases 20).Post} ∪ {¬ Reachable c₀}` — the second set has measure ZERO at every
finite time (`nonuniformTransitionKernel_pow_eq_zero_of_forall_not_reachable`). -/

/-- **The chain-restricted bad-set bound.**  Bounds the `majorityStableEndpoint c₀` failure measure
by `∑ ε` using the work/seam composition + the reachable split (NO false `hReach10`).  This is the
honest replacement for the bundle's `h_post`-via-universal route.

The horizon `T` and the budget `Esum` are taken as EXPLICIT PARAMETERS (with the defining
equalities `hT`/`hEsum`), NOT inlined as `∑ (phases' …)` in the statement.  This is the
decisive whnf-blowup fix: with `T`/`Esum` opaque variables, NEITHER the elaborator NOR the KERNEL
ever has to reduce the 21 `phases'` `dif`s when checking this decl's type / the closing
`h_compose` match (the inlined `∑` form forced a kernel `whnf` over all 21 `dif`s — a timeout past
8M heartbeats that `convert`/`exact`/`set`/`irreducible` could not avoid, since the KERNEL
typecheck ignores all of those).  `stable_majority_whp_of_faithful_core` already carries `T`/`hT`,
and supplies `Esum := ∑ ε` with `hEsum := rfl`. -/
theorem chainRestricted_bad_bound {n : ℕ}
    (asm : SeedTrigWiring.Assembly' (L := L) (K := K) n)
    (c₀ : Config (AgentState L K)) (hValid : validInitial c₀)
    (hStart : (asm.work ⟨0, by omega⟩).Pre c₀)
    (hSlot10Post : ∀ c, (asm.work ⟨10, by omega⟩).Post c →
      Phase10Drop.Phase10Post (L := L) (K := K) c)
    (T : ℕ) (hT : T = ∑ i, (SeedTrigWiring.phases' asm i).t)
    (Esum : ℝ≥0∞) (hEsum : Esum = ∑ i, ((SeedTrigWiring.phases' asm i).ε : ℝ≥0∞)) :
    ((NonuniformMajority L K).transitionKernel ^ T) c₀
        {c | ¬ majorityStableEndpoint (L := L) (K := K) c₀ c}
      ≤ Esum := by
  -- (a) slot-0 `Pre` of the wired family, from `hStart`.
  have hx₀ : (SeedTrigWiring.phases' asm ⟨0, by omega⟩).Pre c₀ := by
    rw [SeedTrigWiring.phases'_even _ _ (by rfl)]
    show (asm.work (ConcreteAssembly.workIdx ⟨0, by omega⟩)).Pre c₀
    rw [show ConcreteAssembly.workIdx ⟨0, by omega⟩ = (⟨0, by omega⟩ : Fin 11) from by
      apply Fin.ext; norm_num [ConcreteAssembly.workIdx]]
    exact hStart
  -- (b) the n-phase composition to the final `Post` failure.  Its final `Post`-set is
  -- `{y | ¬ (phases' asm ⟨21 - 1, _⟩).Post y}` (`composeW_n_phases` at `m := 21`).  We FOLD its
  -- exponent `∑ t` into the opaque param `T` and budget `∑ ε` into `Esum` via the defining
  -- equalities — so `h_compose : (K ^ T) c₀ {¬ (phases' asm ⟨21-1,_⟩).Post} ≤ Esum` references
  -- ONLY opaque vars, and the kernel's typecheck of the closing match NEVER reduces the 21
  -- `phases'` `dif`s (the whnf blowup that defeated `convert`/`exact`/`set`/`irreducible`).
  have h_compose :=
    composeW_n_phases (K := (NonuniformMajority L K).transitionKernel)
      (m := 21) (by omega) (SeedTrigWiring.phases' asm)
      (SeedTrigWiring.phases'_h_chain asm) c₀ hx₀
  rw [← hT, ← hEsum] at h_compose
  -- (c) the closing map on reachable configs (no false universal); stated against the SAME
  -- `phases' asm ⟨21-1,_⟩.Post` set as `h_compose`, so no `Post`-set rewrite is needed.
  have hpost := hpost_on_reachable_asm asm c₀ hValid hSlot10Post
  -- (d) the reachable split: bad ⊆ {¬ (phases' asm ⟨20⟩).Post} ∪ {¬ reachable}.
  have h_subset :
      {c | ¬ majorityStableEndpoint (L := L) (K := K) c₀ c}
        ⊆ {c | ¬ (SeedTrigWiring.phases' asm ⟨21 - 1, by omega⟩).Post c}
          ∪ {c | ¬ (NonuniformMajority L K).Reachable c₀ c} := by
    intro c hc
    by_cases hreach : (NonuniformMajority L K).Reachable c₀ c
    · -- reachable: if `Post` held, the closing map would give `maj` — contradiction.
      refine Or.inl ?_
      simp only [Set.mem_setOf_eq] at hc ⊢
      intro hPost
      exact hc (hpost c hreach hPost)
    · exact Or.inr hreach
  -- (e) the non-reachable part has measure 0.
  have h_unreach :
      ((NonuniformMajority L K).transitionKernel ^ T) c₀
          {c | ¬ (NonuniformMajority L K).Reachable c₀ c} = 0 :=
    nonuniformTransitionKernel_pow_not_reachable_eq_zero L K c₀ T
  -- (f) assemble.  The `Post`-set is the SAME `phases' asm ⟨21-1,_⟩.Post` as `h_compose`, and the
  -- exponent / budget are the opaque `T` / `Esum`, so the closing `exact h_compose` is a variable-
  -- level match with NO `dif` reduction.
  calc ((NonuniformMajority L K).transitionKernel ^ T) c₀
          {c | ¬ majorityStableEndpoint (L := L) (K := K) c₀ c}
      ≤ ((NonuniformMajority L K).transitionKernel ^ T) c₀
          ({c | ¬ (SeedTrigWiring.phases' asm ⟨21 - 1, by omega⟩).Post c}
            ∪ {c | ¬ (NonuniformMajority L K).Reachable c₀ c}) := measure_mono h_subset
    _ ≤ ((NonuniformMajority L K).transitionKernel ^ T) c₀
          {c | ¬ (SeedTrigWiring.phases' asm ⟨21 - 1, by omega⟩).Post c}
        + ((NonuniformMajority L K).transitionKernel ^ T) c₀
          {c | ¬ (NonuniformMajority L K).Reachable c₀ c} := measure_union_le _ _
    _ = ((NonuniformMajority L K).transitionKernel ^ T) c₀
          {c | ¬ (SeedTrigWiring.phases' asm ⟨21 - 1, by omega⟩).Post c} := by
        rw [h_unreach, add_zero]
    _ ≤ Esum := h_compose

/-! ## Part 5 — `stable_majority_whp_of_faithful_core`: the headline, `hReach10`-FREE.

Combines the chain-restricted error bound (Part 4) with the time/budget arithmetic, producing the
Doty Theorem 3.1 headline `(K^T) c₀ {¬ majorityStableEndpoint c₀} ≤ 21/n² ∧ T ≤ 21·C0·n·(L+1)` (+
the `clog` form) conditional ONLY on: `Regime`, `validInitial c₀`, `card c₀ = n`, and the
work/seam residual `FaithfulWorkSeamCore` — with the false `hReach10` universal REMOVED (discharged
to the chain-restricted tautology), and `hcard` foldable to `rfl` (`n := card c₀`).  The remaining
per-instance time/budget fits `hT`/`ht`/`hε` are the arithmetic bookkeeping over the assembled
21-instance family (facts about the work/seam scalars, supplied per-instantiation). -/
set_option maxHeartbeats 2000000 in
theorem stable_majority_whp_of_faithful_core {n : ℕ}
    (hReg : PaperRegime.Regime n L K)
    (c₀ : Config (AgentState L K)) (_hcard : Multiset.card c₀ = n)
    (core : FaithfulWorkSeamCore (L := L) (K := K) n c₀)
    (T : ℕ) (hT : T = ∑ i, (SeedTrigWiring.phases' core.asm i).t)
    (ht : ∀ i, (SeedTrigWiring.phases' core.asm i).t
      ≤ Atoms.C0_numeral * n * (L + 1))
    (hε : ∀ i, ((SeedTrigWiring.phases' core.asm i).ε : ℝ≥0∞)
      ≤ (1 / (n : ℝ≥0∞) ^ 2)) :
    ((NonuniformMajority L K).transitionKernel ^ T) c₀
        {c | ¬ majorityStableEndpoint (L := L) (K := K) c₀ c}
      ≤ (21 : ℝ≥0∞) / (n : ℝ≥0∞) ^ 2
    ∧ T ≤ 21 * Atoms.C0_numeral * n * (L + 1)
    ∧ T ≤ 21 * Atoms.C0_numeral * n * (Nat.clog 2 n + 1) := by
  -- error clause: the chain-restricted bad-set bound + the `∑ ε ≤ 21/n²` fold.  `chainRestricted_
  -- bad_bound` now takes `T`/`hT` and `Esum := ∑ ε`/`hEsum := rfl` as explicit params (the opaque-
  -- horizon whnf fix), so `herr0` is directly `(K ^ T) c₀ {¬ maj} ≤ ∑ ε` at OUR `T`.
  have herr0 := chainRestricted_bad_bound core.asm c₀ core.hValid core.hStart core.hSlot10Post
    T hT (∑ i, ((SeedTrigWiring.phases' core.asm i).ε : ℝ≥0∞)) rfl
  have herr : ((NonuniformMajority L K).transitionKernel ^ T) c₀
        {c | ¬ majorityStableEndpoint (L := L) (K := K) c₀ c}
      ≤ (21 : ℝ≥0∞) / (n : ℝ≥0∞) ^ 2 := by
    refine le_trans herr0 ?_
    have h21 := BudgetTightening.sum_inv_sq_le
      (m := 21) (n := n) (fun i => (SeedTrigWiring.phases' core.asm i).ε) hε
    -- `sum_inv_sq_le` gives `∑ ε ≤ (21 : ℝ≥0∞)/n²` (the literal `m = 21`).
    simpa using h21
  -- time clause: ∑ t ≤ (∑ C0) · n · (L+1) = 21 · C0 · n · (L+1).
  have htime : T ≤ 21 * Atoms.C0_numeral * n * (L + 1) := by
    rw [hT]
    refine le_trans (total_time_le_W
      (fun i => (SeedTrigWiring.phases' core.asm i).t)
      (fun _ => Atoms.C0_numeral) ht) ?_
    have hsum : (∑ _i : Fin 21, Atoms.C0_numeral) = 21 * Atoms.C0_numeral := by
      simp [Finset.sum_const, Finset.card_univ, mul_comm]
    rw [hsum]
  refine ⟨herr, htime, ?_⟩
  -- the `clog` form: `L = clog 2 n` (regime), so `L + 1 = clog 2 n + 1`.
  rw [← hReg.hLlog]; exact htime

/-! ## Part 6 — wiring note: `faithfulCore_of_valid` and the removed false field.

The prompt asks for `faithfulCore_of_valid : Regime → validInitial c₀ → FaithfulCore n c₀`.
That object CANNOT be inhabited HONESTLY: `FaithfulWitness.FaithfulCore` carries the field
`hReach10 : ∀ c, Phase10Post c → Reachable c₀ c`, which is a FALSE universal (an ad-hoc
`Phase10Post` config need not be reachable — refutation-noted in `FaithfulWitness.lean`).  So
inhabiting `FaithfulCore` would require supplying a false field — exactly the trap the ANTI-TRAP
clause forbids.

The HONEST resolution (this file): the false universal is REMOVED, not carried.  `hReach10` enters
the headline ONLY through the final measure bound, where — by `chainRestricted_bad_bound` — only the
REACHABLE part of the bad set has positive measure, and there `majorityWitness_of_reachable_post`
supplies the closing map from the per-config reachability alone (the chain-restricted tautology
`reach10_chain_restricted`).  `stable_majority_whp_of_faithful_core` therefore takes the residual
`FaithfulWorkSeamCore` — `FaithfulCore` minus `hReach10` (removed) minus `hcard` (`n := card c₀`) —
and is the headline conditional ONLY on `Regime`, `validInitial c₀`, `card c₀ = n`, the work/
seam residual, and the per-instance time/budget fits.  This is strictly MORE unconditional than the
`FaithfulCore`-conditioned `FaithfulWitness.stable_majority_whp_of_unconditional_witness`: the false field is gone.
-/

/-! ## Axiom audit (verified by `#print axioms`).  Expected `[propext, Classical.choice,
Quot.sound]`. -/

#print axioms majorityWitness_of_reachable_post
#print axioms chainRestricted_bad_bound
#print axioms stable_majority_whp_of_faithful_core

end FaithfulCoreDischarge
end ExactMajority
