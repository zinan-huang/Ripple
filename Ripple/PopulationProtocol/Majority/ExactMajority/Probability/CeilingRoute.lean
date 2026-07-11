/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Ceiling route — the honest fix for audit finding F5

Audit F5 (independent adversarial audit, `/tmp/opus_audit_report.md`):

> `WindowReconciliation.BiasedMainIndexLeHour` (the PER-AGENT form: every biased Main's index
> `≤ its OWN hour`) is NOT step-preserved by the frozen `phase3CancelSplit`.  The split writes the
> biased partner's index to `i+1` while gating only the OTHER agent's hour (`s2.hour > i`).
> Counterexample: `t2.hour = i`, `s2.hour = i+1`.  Before the step `t2` satisfies `i ≤ t2.hour = i`;
> after the split `t2.bias = dyadic sgn (i+1)` with `i+1 > t2.hour = i`, so the per-agent predicate
> FAILS on `t2`.  The cited per-step lemma `DoublingEdges.phase3CancelSplit_preserves_top_edge`
> preserves only the GLOBAL ceiling (`index ≤ top ∧ hour ≤ top`), not the per-agent form; the prose
> lemma `biasedMainIndexLeHour_of_split_guard_step` named in the reconciliation does not exist.

## Verdict: the audit is RIGHT.

We read the FROZEN split branch exactly (`Protocol/Transition.lean:590-598`):

```
  | .zero, .dyadic sgn i =>
      if _h_gt : s2.hour.val > i.val then
        ({ s2 with bias := .dyadic sgn ⟨i.val + 1, _⟩ },     -- OUTPUT .1  (was the .zero agent)
         { t2 with bias := .dyadic sgn ⟨i.val + 1, _⟩ })      -- OUTPUT .2  (was the biased agent)
      else (s2, t2)
```

The gate is `s2.hour.val > i.val` — the UNBIASED agent's hour.  BOTH outputs are `{ _ with bias := … }`,
i.e. only `bias` is rewritten; NEITHER output's `hour` is touched (the cancel branches DO write
`hour := i`, lowering it, but the split/raise branch does not).  So the biased partner `t2` becomes
`dyadic sgn (i+1)` while keeping its own hour `t2.hour`.  If `t2.hour.val = i` and `s2.hour.val = i+1`,
the input config satisfies the per-agent predicate (`t2`: `i ≤ t2.hour = i`; `s2`: unbiased, vacuous)
but the output `t2'` has index `i+1 > t2.hour = i`.  The per-agent predicate is BROKEN by one step.
`biasedMainIndexLeHour_not_step_preserved` below proves exactly this against the frozen rule.

## The corrected route: carry the GLOBAL ceiling directly.

The downstream consumer (`DoublingEdges.phase6_to_phase7_of_doubling_edges`) only ever needs
`DoublingEdges.AllBiasedMainBelow (l+2) c` — the GLOBAL ceiling `index ≤ top`.  That global form IS
genuinely step-preserved: `DoublingEdges.phase3CancelSplit_preserves_top_edge` proves, exhaustively
over the frozen branches, that `(index ≤ top ∧ hour ≤ top)` on the inputs gives `index ≤ top` on the
outputs (the raise `i → i+1` fires only under `hour > i`, so `i+1 ≤ hour ≤ top`).  This is the honest
inductive quantity; the "induct over the chain" provenance is SOUND for it.

This file therefore:

* records the counterexample as a machine-checked theorem (`biasedMainIndexLeHour_not_step_preserved`);
* re-exports the SOUND per-pair preservation of the global ceiling
  (`allBiasedMainBelow_pair_preserved` — straight from `phase3CancelSplit_preserves_top_edge`);
* supplies the CORRECTED Phase6→7 surface (`phase6To7_surface_ceilingRoute`) carrying the global
  ceiling `AllBiasedMainBelow (l+2)` DIRECTLY, dropping the broken per-agent `BiasedMainIndexLeHour`
  from the carried set — the consumer is fed the genuinely-preserved predicate.

NEW file; no existing file is edited; no sorry/admit/axiom/native_decide.
-/
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.WindowReconciliation

namespace ExactMajority

open scoped BigOperators ENNReal

namespace CeilingRoute

variable {L K : ℕ}

open DoublingEdges WindowReconciliation

/-! ## Part 1 — the counterexample: `BiasedMainIndexLeHour` is NOT step-preserved (F5 verdict).

We formalise the audit's counterexample against the FROZEN `phase3CancelSplit`.  From an arbitrary
base Main state we build a split-firing pair `(s2, t2)` such that:

* `s2` is the unbiased agent with `hour = 1` (so the gate `s2.hour.val = 1 > 0 = i.val` fires);
* `t2` is the biased partner at index `0` with its OWN hour `= 0` (so `0 ≤ 0`, the per-agent
  predicate holds on the input);
* the split output `t2'` is `dyadic sgn 1` with `hour` still `0` — the per-agent predicate FAILS on
  the output (`1 > 0`).

The witness needs `1 ≤ L` so the index `1 : Fin (L+1)` exists. -/

/-- **F5 counterexample (the audit is RIGHT).**  For any `1 ≤ L`, there is a `phase3CancelSplit`-firing
input pair `(s2, t2)` whose biased member satisfies the per-agent invariant `index ≤ own hour` on the
INPUT, yet the split OUTPUT `.2` (the biased partner) violates it: its exponent index `> its own hour`.
So the per-agent `BiasedMainIndexLeHour` is not preserved by one frozen split step — exactly the audit's
`t2.hour = i, s2.hour = i+1` configuration at `i = 0`.

Read off the frozen rule: the gate is the UNBIASED agent's hour (`s2.hour.val > i.val`), but the RAISED
index is written to the biased partner whose own hour is left untouched. -/
theorem biasedMainIndexLeHour_not_step_preserved (hL : 1 ≤ L) (base : AgentState L K) :
    ∃ s2 t2 : AgentState L K,
      -- input: the biased member `t2` satisfies `index ≤ own hour`
      (∀ (s : Sign) (i : Fin (L + 1)), t2.bias = Bias.dyadic s i → i.val ≤ t2.hour.val) ∧
      -- the split FIRES (frozen Rule-4 split branch on `(.zero, dyadic …)`)
      s2.bias = Bias.zero ∧
      (∃ (s : Sign) (i : Fin (L + 1)), t2.bias = Bias.dyadic s i ∧ s2.hour.val > i.val) ∧
      -- output: the biased partner `.2` now violates `index ≤ own hour`
      (∃ (s : Sign) (i : Fin (L + 1)),
        (phase3CancelSplit L K s2 t2).2.bias = Bias.dyadic s i ∧
          i.val > (phase3CancelSplit L K s2 t2).2.hour.val) := by
  -- index 0 and 1 live in `Fin (L+1)` since `L ≥ 1`.
  have h0 : (0 : ℕ) < L + 1 := by omega
  have h1 : (1 : ℕ) < L + 1 := by omega
  -- the two Fin witnesses and the two agent states, factored out so the anonymous-constructor
  -- `⟨_, _⟩` for `Fin` does not collide with the outer `refine ⟨…⟩`.
  let i0 : Fin (L + 1) := ⟨0, h0⟩
  let i1 : Fin (L + 1) := ⟨1, h1⟩
  -- s2 : unbiased Main, hour = 1  (the gate `s2.hour.val = 1 > 0` fires)
  let s2 : AgentState L K := { base with role := Role.main, bias := Bias.zero, hour := i1 }
  -- t2 : biased Main at index 0, OWN hour = 0  (input per-agent predicate holds: `0 ≤ 0`)
  let t2 : AgentState L K :=
    { base with role := Role.main, bias := Bias.dyadic Sign.pos i0, hour := i0 }
  refine ⟨s2, t2, ?_, ?_, ?_, ?_⟩
  · -- input per-agent predicate on `t2`: `bias = dyadic pos 0`, hour 0, and `0 ≤ 0`.
    intro s i hb
    -- the only matching bias is `dyadic pos 0`; hence `i.val = 0 ≤ 0 = hour.val`.
    simp only [t2] at hb
    injection hb with _ hidx
    have : i.val = (0 : ℕ) := by rw [← hidx]
    simp only [t2, i0]
    omega
  · rfl
  · exact ⟨Sign.pos, i0, rfl, by simp [s2, i0, i1]⟩
  · -- evaluate the frozen split on `(.zero, dyadic pos 0)` with gate `1 > 0` true.
    refine ⟨Sign.pos, i1, ?_, ?_⟩
    · simp only [phase3CancelSplit, s2, t2]
      -- gate `s2.hour.val = 1 > 0` holds → the raise branch fires, output .2 bias = dyadic pos (0+1).
      rw [dif_pos (by simp [i0, i1])]
    · -- output .2 hour is `t2.hour = i0 = 0` (unchanged by the `{ _ with bias := … }` rewrite),
      -- raised index is `i1 = 1`, so `1 > 0`.
      simp only [phase3CancelSplit, s2, t2]
      rw [dif_pos (by simp [i0, i1])]
      simp only [i0, i1]
      omega

/-! ## Part 2 — the SOUND route: the GLOBAL ceiling is step-preserved.

`DoublingEdges.AllBiasedMainBelow top c` (`index ≤ top`, GLOBAL) is the genuinely inductive quantity.
Its per-pair preservation is exactly `DoublingEdges.phase3CancelSplit_preserves_top_edge`.  We re-state
it here in the local idiom (the "engine" of the corrected route) so the corrected surface's provenance
is the SOUND per-step fact, not the broken per-agent one. -/

/-- **The SOUND per-pair preservation (re-export of the global-ceiling step lemma).**  If both inputs of
`phase3CancelSplit` are bias-bounded `≤ top` and have `hour ≤ top`, both outputs are bias-bounded
`≤ top`.  This is `DoublingEdges.phase3CancelSplit_preserves_top_edge` — proven exhaustively over the
frozen branches.  Unlike the per-agent `index ≤ own hour`, THIS quantity (the global `top` ceiling) is
step-preserved, because the raise `i → i+1` fires only under `hour > i`, so `i+1 ≤ hour ≤ top`. -/
theorem allBiasedMainBelow_pair_preserved {top : ℕ} (s2 t2 : AgentState L K)
    (hsb : ∀ (ss : Sign) (i : Fin (L + 1)), s2.bias = Bias.dyadic ss i → i.val ≤ top)
    (htb : ∀ (ss : Sign) (i : Fin (L + 1)), t2.bias = Bias.dyadic ss i → i.val ≤ top)
    (hsh : s2.hour.val ≤ top) (hth : t2.hour.val ≤ top) :
    (∀ (ss : Sign) (i : Fin (L + 1)),
        (phase3CancelSplit L K s2 t2).1.bias = Bias.dyadic ss i → i.val ≤ top) ∧
    (∀ (ss : Sign) (i : Fin (L + 1)),
        (phase3CancelSplit L K s2 t2).2.bias = Bias.dyadic ss i → i.val ≤ top) :=
  DoublingEdges.phase3CancelSplit_preserves_top_edge (L := L) (K := K) s2 t2 hsb htb hsh hth

/-! ## Part 3 — the CORRECTED Phase6→7 surface.

`WindowReconciliation.phase6To7_surface_reconciled` carried the broken per-agent `BiasedMainIndexLeHour`
(plus `MainHourBelow`) and bridged to the global ceiling.  Since the per-agent predicate is NOT
step-preserved (Part 1), we DROP it and carry the global ceiling `AllBiasedMainBelow (l+2)` DIRECTLY —
the genuinely step-preserved quantity (Part 2).  Everything else is the landed
`DoublingEdges.phase6_to_phase7_of_doubling_edges`. -/

/-- **The corrected reconciled Phase6→7 surface (PROVEN).**  Carries the GLOBAL ceiling
`DoublingEdges.AllBiasedMainBelow (l+2) c` directly — the step-preserved quantity — instead of the
broken per-agent `BiasedMainIndexLeHour` + `MainHourBelow` pair of `phase6To7_surface_reconciled`.  This
is the honest F5 route: the carried positional invariant is the one that survives the frozen split step.

(The earlier `WindowReconciliation.phase6To7_surface_reconciled` is still TRUE — its proven bridge
`index ≤ hour ≤ top ⟹ index ≤ top` is correct — but its `hIdx` input has no sound reachability
discharge, so this is the route a consumer should use.) -/
theorem phase6To7_surface_ceilingRoute {l n E : ℕ} {σ : Sign} {c : Config (AgentState L K)}
    (hl : 1 ≤ l)
    (hSeed : MinorityFloorGap.AllBiasedMainAbove (L := L) (K := K) (l + 1) c)
    (hA : MarginLedgers.MainConfinementProfile (L := L) (K := K) σ n c)
    (h6 : Phase6Convergence.Phase6Win (L := L) (K := K) n c)
    (hCeil : DoublingEdges.AllBiasedMainBelow (L := L) (K := K) (l + 2) c)
    (hCo : DoublingEdges.PredecessorLevelsCoPopulated (L := L) (K := K) σ E l c)
    (hE : (E : ℝ) ≤ (4 : ℝ) * (n : ℝ) / 15) :
    EliminatorMargins.Phase6To7Structure (L := L) (K := K) σ E c :=
  DoublingEdges.phase6_to_phase7_of_doubling_edges hl hSeed hA h6 hCeil hCo hE

/-- **The corrected route still SUBSUMES the old per-agent surface (bridge retained, soundly fed).**
If a consumer genuinely has the two clock snapshots `BiasedMainIndexLeHour` + `MainHourBelow (l+2)`
on the SAME config `c` (as a snapshot, not via the broken step-induction), the proven bridge
`WindowReconciliation.allBiasedMainBelow_of_indexLeHour_of_hourCeiling` still produces the global
ceiling — and we feed THAT into the corrected surface.  So no expressive power is lost; only the unsound
"induct the per-agent form over the chain" provenance is removed. -/
theorem phase6To7_surface_ceilingRoute_ofSnapshots {l n E : ℕ} {σ : Sign}
    {c : Config (AgentState L K)}
    (hl : 1 ≤ l)
    (hSeed : MinorityFloorGap.AllBiasedMainAbove (L := L) (K := K) (l + 1) c)
    (hA : MarginLedgers.MainConfinementProfile (L := L) (K := K) σ n c)
    (h6 : Phase6Convergence.Phase6Win (L := L) (K := K) n c)
    (hIdx : WindowReconciliation.BiasedMainIndexLeHour (L := L) (K := K) c)
    (hHour : WindowReconciliation.MainHourBelow (L := L) (K := K) (l + 2) c)
    (hCo : DoublingEdges.PredecessorLevelsCoPopulated (L := L) (K := K) σ E l c)
    (hE : (E : ℝ) ≤ (4 : ℝ) * (n : ℝ) / 15) :
    EliminatorMargins.Phase6To7Structure (L := L) (K := K) σ E c :=
  phase6To7_surface_ceilingRoute hl hSeed hA h6
    (WindowReconciliation.allBiasedMainBelow_of_indexLeHour_of_hourCeiling hIdx hHour) hCo hE

end CeilingRoute

end ExactMajority
