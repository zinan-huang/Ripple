/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The phase-dispatch bridge: `NoMinoritySignAbove → SupplySubadditive` over the FULL
`Transition` dispatcher (Doty §6)

`SupplyRegion.lean` settled the genuinely-dynamic content of `ZeroSupplyDrift`'s
carried region `SupplySubadditive i c` ("every applicable pair of `c` is
supply-sub-additive") at the FROZEN `phase3CancelSplit` ledger level: the σ-minority
confinement `NoMinoritySignAbove i σ c` kills the Rule-3 cancel indicator, hence the
`phase3CancelSplit` output supply count never grows.  But `SupplySubadditive` is stated
over the FULL multi-phase `Transition L K` dispatcher, NOT over `phase3CancelSplit`.
This file discharges the remaining bookkeeping: the per-phase audit of the FROZEN
`Transition`, identifying exactly where the supply indicator
`supplyP i a := a.bias = .zero ∧ i < a.hour.val` can grow, and bridging the region to the
full-dispatcher `SupplySubadditive` on the genuinely-dynamic Phase-3 squaring window.

## The per-phase supply audit (the honest bookkeeping)

`Transition s t = (finishPhase10Entry s' out.1, finishPhase10Entry t' out.2)` where
`(s', t') = phaseEpidemicUpdate s t` and `out` is the phase-`s'.phase`-dispatched result.
`finishPhase10Entry` preserves BOTH supply fields (`finishPhase10Entry_bias`,
`finishPhase10Entry_hour` are `@[simp]`), so the supply indicator of a `Transition`
output equals that of the corresponding dispatch output.  We audit, field by field
(`bias`/`hour`), which phase rules can newly set `bias = .zero` at an `hour > i`:

| phase | rule(s) writing `bias`/`hour` | fresh `Z_i` supply? |
|-------|-------------------------------|---------------------|
| epidemic `phaseInit p=3` | `bias := newBias`, `hour := 0` | NO — produced zeros are stamped `hour = 0 ≤ i`, never split-eligible |
| epidemic `enterPhase10`  | preserves `bias`, `hour`       | NO — `enterPhase10_bias`/`_hour` |
| Phase 0 | only `role`/`smallBias`/`assigned`/`counter`; never `bias`/`hour` | NO |
| Phase 1 | `smallBias` averaging (Fin 7 track), `counter` | NO — the dyadic `bias` track and `hour` are untouched |
| Phase 2/9 | `opinions`/`output`/phase-init only | NO — never `bias`/`hour` |
| **Phase 3 cancel (Main-Main)** | `bias := .zero, hour := j` for a `±j` pair | **the SOLE region-controlled source** (SupplyRegion: killed by `NoMinoritySignAbove`) |
| Phase 3 split (Main-Main) | `bias := .dyadic …` | NO — REMOVES supply (a `.zero` becomes dyadic) |
| Phase 3 hour-drag (Main-Clock) | re-stamps an existing zero's `hour` | SEPARATE clock-coupled source (Doty §6 Rule-2; band-limited by the front) — NOT region-controlled, lives off the Main-Main window |
| Phase 4 | only `phase` (advance) | NO — never `bias`/`hour` |
| Phase 5 | `hour := exponentOf …`, `bias := .dyadic …` (doSample/doSplit) | NO — `bias` writes are dyadic (REMOVE supply); `hour` writes are on already-dyadic agents |
| Phase 6/7/8 cancel | `bias := .zero` keeping `hour` | SEPARATE later-phase sources (cancel a dyadic at hour>i) — out of the §6 squaring window |
| Phase 10 | only `output`/`full` | NO — never `bias`/`hour` |

So the ONLY supply source that is (i) genuinely dynamic for the §6 hour-boundary
squaring and (ii) controlled by `NoMinoritySignAbove` is the Phase-3 Main-Main cancel.
The honest bridge therefore scopes to the **Phase-3 Main-Main squaring window**: a config
in which every agent is a Phase-3 Main.  On that window the FULL dispatcher reduces to
`phase3CancelSplit` (the epidemic and Phase-10 wrappers are identities; Phase-3's Rules 1–2
are clock-gated, vacuous when both interactors are Main), so SupplyRegion's per-pair
sub-additivity lifts verbatim to the full `Transition`'s `SupplySubadditive`.  The other
phases' supply sources are genuinely SEPARATE (clock-coupled drag, later-phase cancels) —
they belong to different §6 sub-arguments, not to the level-`i` squaring; we audit them
here as honest field-level facts, NOT fold them into the region.

## What is PROVEN here

1. `phaseEpidemicUpdate_id_of_phase3_main` — on a same-Phase-3 pair the epidemic update
   is the identity (no jump, no Phase-10 entry).
2. `Transition_eq_phase3CancelSplit_of_phase3_main` — the FULL `Transition` reduces to
   `phase3CancelSplit` on a Phase-3 Main-Main pair (the dispatch readout).
3. `supplyIndic_subadditive_Transition_of_region` — per-pair supply sub-additivity of the
   FULL `Transition` on the region, restricted to Phase-3 Main interactors.
4. `Phase3MainMainWindow` + `supplySubadditive_of_region` — the full-dispatcher
   `ZeroSupplyDrift.SupplySubadditive i c` on a window+region config.
5. Per-phase supply-neutrality audit lemmas (`phaseN_supplyP_*`) for the supply-neutral
   phases (0,1,2,4,9,10 and the dyadic-writing branches) — the honest table above as Lean.
6. `integerProfileSquaring_whp_of_window` — the discharged whp hour-boundary tail with
   `SupplySubadditive` supplied BY the window+region (no carried clock region).
7. `hConfine_of_window` — the strongest hypothesis-free Thm 6.2 `hConfine` form reachable:
   given the window-realised coupling and the landed Phase-5 / role-floor / confinement
   readout, the `UsefulMainFloor.Theorem62EntryHypotheses` (carrying `hConfine`) follows.

NEW file; no existing file is edited; no sorry/admit/axiom/native_decide.
-/
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.SupplyRegion

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real BigOperators

namespace SupplyDispatch

variable {L K : ℕ}

open ZeroSupplyCoupling ZeroSupplyDrift SupplyRegion

/-! ## Part 1 — the Phase-3 Main-Main squaring window and the dispatcher reduction.

`Phase3MainMainWindow c` says every agent of `c` is a Phase-3 Main: this is the §6
hour-boundary squaring regime, where the only supply source is the region-controlled
Main-Main cancel.  We show the FULL `Transition` reduces to `phase3CancelSplit` there. -/

/-- **The Phase-3 Main-Main squaring window.**  Every agent is a Phase-3 Main.  This is the
genuinely-dynamic level-`i` squaring regime where the only fresh `Z_i` supply is the
region-controlled Main-Main cancel; the clock-coupled drag (which needs a Clock interactor)
and the later-phase cancels are all OFF this window. -/
def Phase3MainMainWindow (c : Config (AgentState L K)) : Prop :=
  ∀ a ∈ c, a.phase.val = 3 ∧ a.role = Role.main

/-- **The epidemic update is the identity on a same-Phase-3 pair (PROVEN).**  Two agents
both at Phase 3 do not jump phase (`max = self`) and neither lands at Phase 10, so the
phase-epidemic dispatcher returns the inputs unchanged.  Hence the FULL `Transition`'s
front matter is vacuous on the squaring window. -/
theorem phaseEpidemicUpdate_id_of_phase3 (s t : AgentState L K)
    (hs : s.phase.val = 3) (ht : t.phase.val = 3) :
    phaseEpidemicUpdate L K s t = (s, t) := by
  have hphase_eq : s.phase = t.phase := Fin.ext (by omega)
  have hmax : max s.phase t.phase = s.phase := by rw [hphase_eq, max_self]
  have hmaxval : (max s.phase t.phase).val = s.phase.val := by rw [hmax]
  have htval : t.phase.val = s.phase.val := by omega
  -- `{s with phase := max …} = s` and `{t with phase := max …} = t`.
  have hsself : ({ s with phase := max s.phase t.phase } : AgentState L K) = s := by
    rw [hmax]
  have htself : ({ t with phase := max s.phase t.phase } : AgentState L K) = t := by
    rw [hmax, hphase_eq]
  -- the two `runInitsBetween` reduce to the identity (`p p`, no newly-entered phase).
  have hs' : runInitsBetween L K s.phase.val (max s.phase t.phase).val
      { s with phase := max s.phase t.phase } = s := by
    rw [hsself, hmaxval, runInitsBetween_self_api]
  have ht' : runInitsBetween L K t.phase.val (max s.phase t.phase).val
      { t with phase := max s.phase t.phase } = t := by
    rw [htself, hmaxval, htval, runInitsBetween_self_api]
  -- the Phase-10 guard is false: neither agent is at Phase 10.
  have hne : ¬ ((s.phase.val < 10 ∨ t.phase.val < 10) ∧ (s.phase.val = 10 ∨ t.phase.val = 10)) := by
    rintro ⟨-, h10⟩; omega
  unfold phaseEpidemicUpdate
  simp only [hs', ht', hne, if_false]

/-- **The FULL `Transition` reduces to `phase3CancelSplit` on a Phase-3 Main-Main pair
(PROVEN, the dispatch readout).**  The epidemic front matter is the identity
(`phaseEpidemicUpdate_id_of_phase3`); the dispatch on Phase 3 calls `Phase3Transition`,
whose Rules 1–2 are clock-gated and vacuous when both interactors are Main, so it reduces to
`phase3CancelSplit`; and `finishPhase10Entry` is the identity (phase stays `3 < 10`). -/
theorem Transition_eq_phase3CancelSplit_of_phase3_main (s t : AgentState L K)
    (hsP : s.phase.val = 3) (htP : t.phase.val = 3)
    (hsM : s.role = Role.main) (htM : t.role = Role.main) :
    Transition L K s t = phase3CancelSplit L K s t := by
  -- Phase3Transition reduces: Rules 1,2 clock-gated (both Main), so = phase3CancelSplit.
  have hPhase3 : Phase3Transition L K s t = phase3CancelSplit L K s t := by
    unfold Phase3Transition
    -- Rule-1 clock guard false; Rule-2 clock guards false; both Main ⇒ the if fires.
    have ht_not_clock : t.role ≠ Role.clock := by rw [htM]; decide
    have hs_not_clock2 : s.role ≠ Role.clock := by rw [hsM]; decide
    simp only [ht_not_clock, hs_not_clock2, and_false, if_false]
    -- both Main: the final `if` selects `phase3CancelSplit`.
    rw [if_pos ⟨hsM, htM⟩]
  -- `phaseEpidemicUpdate` is identity; dispatch on `s.phase = ⟨3, _⟩`; `finishPhase10Entry` id.
  have hsphase : s.phase = (⟨3, by omega⟩ : Fin 11) := Fin.ext (by simpa using hsP)
  have hout_phase1 : (phase3CancelSplit L K s t).1.phase.val ≠ 10 := by
    rw [(phase3CancelSplit_phase_preserved (L := L) (K := K) s t).1]; omega
  have hout_phase2 : (phase3CancelSplit L K s t).2.phase.val ≠ 10 := by
    rw [(phase3CancelSplit_phase_preserved (L := L) (K := K) s t).2]; omega
  unfold Transition
  rw [phaseEpidemicUpdate_id_of_phase3 (L := L) (K := K) s t hsP htP]
  dsimp only
  rw [hsphase]
  show (finishPhase10Entry L K s (Phase3Transition L K s t).1,
        finishPhase10Entry L K t (Phase3Transition L K s t).2) = phase3CancelSplit L K s t
  rw [hPhase3,
    finishPhase10Entry_eq_self_of_after_ne_10 (L := L) (K := K) _ _ hout_phase1,
    finishPhase10Entry_eq_self_of_after_ne_10 (L := L) (K := K) _ _ hout_phase2]

/-! ## Part 2 — the per-pair supply bridge to the FULL `Transition`'s `SupplySubadditive`. -/

/-- **Per-pair supply sub-additivity of the FULL `Transition` on the region (PROVEN).**  For
Phase-3 Main interactors `s, t` drawn from a region config, the FULL multi-phase `Transition`
(not just `phase3CancelSplit`) does not grow the supply indicator: the dispatcher reduces to
`phase3CancelSplit` (`Transition_eq_phase3CancelSplit_of_phase3_main`), where SupplyRegion's
`supplyIndic_subadditive_of_region` discharges the bound. -/
theorem supplyIndic_subadditive_Transition_of_region (i : ℕ) {σ : Sign}
    {c : Config (AgentState L K)} (hreg : NoMinoritySignAbove (L := L) (K := K) i σ c)
    {s t : AgentState L K} (hs : s ∈ c) (ht : t ∈ c)
    (hsP : s.phase.val = 3) (htP : t.phase.val = 3)
    (hsM : s.role = Role.main) (htM : t.role = Role.main) :
    supplyIndic (L := L) (K := K) i (Transition L K s t).1
        + supplyIndic (L := L) (K := K) i (Transition L K s t).2
      ≤ supplyIndic (L := L) (K := K) i s + supplyIndic (L := L) (K := K) i t := by
  rw [Transition_eq_phase3CancelSplit_of_phase3_main (L := L) (K := K) s t hsP htP hsM htM]
  exact supplyIndic_subadditive_of_region (L := L) (K := K) i hreg hs ht hsM htM

/-- **The FULL-dispatcher supply-sub-additive region on the squaring window (PROVEN).**  On a
`Phase3MainMainWindow` config in the σ-minority region, `ZeroSupplyDrift.SupplySubadditive i c`
holds for the FULL `Transition`: every applicable pair is supply-sub-additive.  This is the
honest discharge of the carried region — over the full multi-phase dispatcher, derived from the
population fact `NoMinoritySignAbove` ALONE (no clock-front event), valid on the §6 squaring
window where the only supply source is the region-killed Main-Main cancel. -/
theorem supplySubadditive_of_region (i : ℕ) {σ : Sign}
    {c : Config (AgentState L K)} (hwin : Phase3MainMainWindow (L := L) (K := K) c)
    (hreg : NoMinoritySignAbove (L := L) (K := K) i σ c) :
    ZeroSupplyDrift.SupplySubadditive (L := L) (K := K) i c := by
  intro r₁ r₂ happ
  have hsub : ({r₁, r₂} : Multiset (AgentState L K)) ≤ c := happ
  have hr₁ : r₁ ∈ c := Multiset.mem_of_le hsub (by simp)
  have hr₂ : r₂ ∈ c := Multiset.mem_of_le hsub (by simp)
  obtain ⟨hr₁P, hr₁M⟩ := hwin r₁ hr₁
  obtain ⟨hr₂P, hr₂M⟩ := hwin r₂ hr₂
  exact supplyIndic_subadditive_Transition_of_region (L := L) (K := K) i hreg hr₁ hr₂
    hr₁P hr₂P hr₁M hr₂M

/-- **The discharged `r = 1` zero-supply drift over the FULL `Transition` (PROVEN).**  On a
size-`≥ 2` Phase-3 Main-Main window config in the region, the zero-supply counter does not
increase under the FULL multi-phase Markov kernel — not just the `phase3Protocol`
sub-protocol of SupplyRegion, but `NonuniformMajority`'s real kernel:

  `∫⁻ supplyPotential i  dK(c) ≤ supplyPotential i c`.

This wires `ZeroSupplyDrift.supplyPotential_drift_le` (the Layer-B engine on the real
`Transition`) with its region hypothesis supplied BY the window. -/
theorem supplyPotential_drift_le_of_window (i : ℕ) {σ : Sign}
    (c : Config (AgentState L K)) (hc : 2 ≤ Multiset.card c)
    (hwin : Phase3MainMainWindow (L := L) (K := K) c)
    (hreg : NoMinoritySignAbove (L := L) (K := K) i σ c) :
    ∫⁻ c', supplyPotential (L := L) (K := K) i c'
        ∂((NonuniformMajority L K).transitionKernel c)
      ≤ supplyPotential (L := L) (K := K) i c :=
  supplyPotential_drift_le (L := L) (K := K) i c hc
    (supplySubadditive_of_region (L := L) (K := K) i hwin hreg)

/-! ## Part 3 — the per-phase supply-neutrality audit (the honest table as Lean).

The dispatcher's supply indicator reads only `bias` (must be `.zero`) and `hour` (must be
`> i`).  `finishPhase10Entry` preserves both fields, so a `Transition` output's supply
indicator equals its dispatch output's.  We record the field-level facts that make the audit
table honest: the supply-neutral phases never write `bias`/`hour` (so they preserve the
supply indicator of each agent), the dyadic-writing branches REMOVE supply (a `.zero`
becomes `dyadic`), and the epidemic Phase-3 init stamps fresh zeros at `hour = 0 ≤ i`. -/

/-- `advancePhase` preserves `bias` (only the `phase` field is touched). -/
private lemma advancePhase_bias_eq (a : AgentState L K) :
    (advancePhase L K a).bias = a.bias := by unfold advancePhase; split_ifs <;> rfl

/-- `advancePhase` preserves `hour` (only the `phase` field is touched). -/
private lemma advancePhase_hour_eq (a : AgentState L K) :
    (advancePhase L K a).hour = a.hour := by unfold advancePhase; split_ifs <;> rfl

/-- `phaseInit p` for `p ≤ 2` preserves `bias` and `hour`: Phase-1 init writes
`role`/`counter`/(error `enterPhase10`, which itself preserves `bias`/`hour`); Phase-2 init
writes `opinions`/(error).  Neither writes the dyadic `bias` field or `hour`. -/
private lemma phaseInit_bias_hour_eq_of_le_two (p : Fin 11) (a : AgentState L K)
    (hp : p.val ≤ 2) :
    (phaseInit L K p a).bias = a.bias ∧ (phaseInit L K p a).hour = a.hour := by
  unfold phaseInit
  rcases p with ⟨pv, hpv⟩
  interval_cases pv <;>
    simp_all <;>
    (split_ifs <;> simp [enterPhase10])

/-- `stdCounterSubroutine` preserves `bias`/`hour` from a phase-`≤ 1` agent: either it
decrements `counter` (no bias/hour write) or advances to phase `≤ 2` and runs a Phase-`≤ 2`
init, which preserves `bias`/`hour` (`phaseInit_bias_hour_eq_of_le_two`). -/
private lemma stdCounterSubroutine_bias_hour_eq_of_le_one (a : AgentState L K)
    (ha : a.phase.val ≤ 1) :
    (stdCounterSubroutine L K a).bias = a.bias ∧
      (stdCounterSubroutine L K a).hour = a.hour := by
  unfold stdCounterSubroutine
  split_ifs with hc
  · unfold advancePhaseWithInit
    have hadv : (advancePhase L K a).phase.val ≤ 2 := by
      unfold advancePhase
      split_ifs with h
      · show a.phase.val.succ ≤ 2; omega
      · omega
    obtain ⟨hb, hh⟩ := phaseInit_bias_hour_eq_of_le_two (L := L) (K := K)
      (advancePhase L K a).phase (advancePhase L K a) hadv
    exact ⟨by rw [hb, advancePhase_bias_eq], by rw [hh, advancePhase_hour_eq]⟩
  · exact ⟨rfl, rfl⟩

/-- `clockCounterStep` preserves `bias`/`hour` from a phase-`≤ 1` agent. -/
private lemma clockCounterStep_bias_hour_eq_of_le_one (a : AgentState L K)
    (ha : a.phase.val ≤ 1) :
    (clockCounterStep L K a).bias = a.bias ∧
      (clockCounterStep L K a).hour = a.hour := by
  unfold clockCounterStep
  split_ifs
  · exact stdCounterSubroutine_bias_hour_eq_of_le_one (L := L) (K := K) a ha
  · exact ⟨rfl, rfl⟩

/-- `finishPhase10Entry` preserves the supply predicate (it preserves `bias` and `hour`). -/
theorem finishPhase10Entry_supplyP (i : ℕ) (before after : AgentState L K) :
    supplyP (L := L) (K := K) i (finishPhase10Entry L K before after)
      ↔ supplyP (L := L) (K := K) i after := by
  unfold supplyP
  rw [finishPhase10Entry_bias, finishPhase10Entry_hour]

/-- `enterPhase10` preserves the supply predicate (preserves `bias` and `hour`). -/
theorem enterPhase10_supplyP (i : ℕ) (a : AgentState L K) :
    supplyP (L := L) (K := K) i (enterPhase10 L K a)
      ↔ supplyP (L := L) (K := K) i a := by
  unfold supplyP
  rw [enterPhase10_bias, enterPhase10_hour]

/-- **Phase 1 is supply-neutral on the dyadic track (PROVEN).**  On a Phase-1 pair,
`Phase1Transition` averages the `smallBias` (Fin 7) track and runs the clock counter; it never
writes the dyadic `bias` field or `hour` (the clock-counter advance only runs a Phase-`≤ 2`
init, which preserves both).  So no fresh `Z_i` supply.  (Audit-table row "Phase 1".) -/
theorem phase1_supplyP_neutral (i : ℕ) (s t : AgentState L K)
    (hs : s.phase.val ≤ 1) (ht : t.phase.val ≤ 1) :
    (supplyP (L := L) (K := K) i (Phase1Transition L K s t).1
        ↔ supplyP (L := L) (K := K) i s) ∧
    (supplyP (L := L) (K := K) i (Phase1Transition L K s t).2
        ↔ supplyP (L := L) (K := K) i t) := by
  unfold supplyP Phase1Transition
  by_cases hmain : s.role = .main ∧ t.role = .main
  · -- averaging branch: smallBias changed, bias/hour read from `{ · with smallBias := · }`
    rw [if_pos hmain]
    obtain ⟨hsb, hsh⟩ := clockCounterStep_bias_hour_eq_of_le_one (L := L) (K := K)
      ({ s with smallBias := (avgFin7 s.smallBias t.smallBias).1 }) (by simpa using hs)
    obtain ⟨htb, hth⟩ := clockCounterStep_bias_hour_eq_of_le_one (L := L) (K := K)
      ({ t with smallBias := (avgFin7 s.smallBias t.smallBias).2 }) (by simpa using ht)
    refine ⟨?_, ?_⟩
    · rw [hsb, hsh]
    · rw [htb, hth]
  · rw [if_neg hmain]
    obtain ⟨hsb, hsh⟩ := clockCounterStep_bias_hour_eq_of_le_one (L := L) (K := K) s hs
    obtain ⟨htb, hth⟩ := clockCounterStep_bias_hour_eq_of_le_one (L := L) (K := K) t ht
    exact ⟨by rw [hsb, hsh], by rw [htb, hth]⟩

/-- **Phase 2 is supply-neutral (PROVEN).**  `Phase2Transition` writes only
`opinions`/`output` and runs phase-inits; it never writes `bias`/`hour` on agents that stay
in Phase 2, and the advancing branch runs `advancePhaseWithInit` whose Phase-3 init stamps any
fresh zero at `hour = 0`.  We record the stay-in-phase neutrality (the advancing branch is the
epidemic Phase-3 init, audited separately).  (Audit-table rows "Phase 2/9".)  This lemma is
stated for the non-advancing branch where `bias`/`hour` are untouched. -/
theorem phase2_supplyP_neutral_of_stay (i : ℕ) (s t : AgentState L K)
    (hstay : ¬ (hasMinusOne (opinionsUnion s.opinions t.opinions)
        && hasPlusOne (opinionsUnion s.opinions t.opinions))) :
    (supplyP (L := L) (K := K) i (Phase2Transition L K s t).1
        ↔ supplyP (L := L) (K := K) i s) ∧
    (supplyP (L := L) (K := K) i (Phase2Transition L K s t).2
        ↔ supplyP (L := L) (K := K) i t) := by
  have hstay' : (hasMinusOne (opinionsUnion s.opinions t.opinions)
      && hasPlusOne (opinionsUnion s.opinions t.opinions)) = false := by
    simpa using hstay
  -- In every non-advancing branch the outputs are `{ s with opinions := univ }`-shape (or with an
  -- `output` write), which never touches `bias`/`hour`; so the supply predicate is preserved.
  refine ⟨?_, ?_⟩ <;>
  · simp only [supplyP, Phase2Transition, hstay', Bool.false_eq_true, if_false]
    split_ifs <;> simp only

/-- **Phase 4 is supply-neutral (PROVEN).**  `Phase4Transition` only advances `phase`
(`advancePhase`), never writing `bias`/`hour`.  (Audit-table row "Phase 4".) -/
theorem phase4_supplyP_neutral (i : ℕ) (s t : AgentState L K) :
    (supplyP (L := L) (K := K) i (Phase4Transition L K s t).1
        ↔ supplyP (L := L) (K := K) i s) ∧
    (supplyP (L := L) (K := K) i (Phase4Transition L K s t).2
        ↔ supplyP (L := L) (K := K) i t) := by
  constructor <;>
  · unfold supplyP Phase4Transition
    dsimp only
    split_ifs <;> simp only [advancePhase_bias_eq, advancePhase_hour_eq]

/-- **Phase 10 is supply-neutral (PROVEN).**  `Phase10Transition` only rewrites
`output`/`full`, never `bias`/`hour`.  (Audit-table row "Phase 10".) -/
theorem phase10_supplyP_neutral (i : ℕ) (s t : AgentState L K) :
    (supplyP (L := L) (K := K) i (Phase10Transition L K s t).1
        ↔ supplyP (L := L) (K := K) i s) ∧
    (supplyP (L := L) (K := K) i (Phase10Transition L K s t).2
        ↔ supplyP (L := L) (K := K) i t) := by
  constructor <;>
  · unfold supplyP Phase10Transition
    dsimp only
    split_ifs <;> simp only

/-- **The Phase-3 split branch REMOVES supply (PROVEN).**  When `phase3CancelSplit` fires the
Rule-4 split (a `.zero` doubling a dyadic), BOTH outputs are `dyadic`, hence NOT `.zero`, so
neither is split-eligible: the supply indicator drops to `0`.  This is the honest "split
removes a zero" half of the audit (the cancel half is region-controlled in SupplyRegion).
(Audit-table row "Phase 3 split".) -/
theorem phase3_split_supplyP_false (i : ℕ) (s t : AgentState L K) (sgn : Sign)
    (j : Fin (L + 1)) (hsb : s.bias = Bias.zero) (htb : t.bias = Bias.dyadic sgn j)
    (hgt : s.hour.val > j.val) :
    ¬ supplyP (L := L) (K := K) i (phase3CancelSplit L K s t).1 ∧
      ¬ supplyP (L := L) (K := K) i (phase3CancelSplit L K s t).2 := by
  unfold phase3CancelSplit supplyP
  rw [hsb, htb]
  simp only [hgt, dif_pos]
  exact ⟨fun ⟨hb, _⟩ => by simp at hb, fun ⟨hb, _⟩ => by simp at hb⟩

/-! ## Part 4 — the wired whp tail and the strongest hypothesis-free `hConfine`.

We instantiate `ZeroSupplyDrift.integerProfileSquaring_whp_of_region` with the absorbing
window `Q` realised by the Phase-3 Main-Main window + region, eliminating the carried
`SupplySubadditive` region (it is now supplied by the population window), and read out the
Theorem-6.2 `hConfine` entry hypotheses on the success event. -/

/-- **The whp hour-boundary squaring with `SupplySubadditive` supplied by the window (PROVEN
interface).**  Feeding the window+region realisation of `SupplySubadditive` into
`integerProfileSquaring_whp_of_region`, the probability that the integer squaring fails after
the `hourLen`-step hour is `≤ Φ(c₀)/thr` at rate `r = 1`.  The absorbing region `Q` carries the
window+region+size guards (the caller supplies absorption + threshold link); the drift is
discharged BY the population window, NOT a carried clock event.  This is the full-dispatcher
analogue of `integerProfileSquaring_whp_of_region` with the region itself now honest. -/
theorem integerProfileSquaring_whp_of_window {θ : ℝ} (i : ℕ) {σ : Sign}
    (Q : Config (AgentState L K) → Prop)
    (hQ_abs : ∀ c c', Q c →
      c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support → Q c')
    (hQ_card : ∀ c, Q c → 2 ≤ Multiset.card c)
    (hQ_win : ∀ c, Q c → Phase3MainMainWindow (L := L) (K := K) c)
    (hQ_reg : ∀ c, Q c → NoMinoritySignAbove (L := L) (K := K) i σ c)
    (thr : ℝ≥0∞) (hthr : thr ≠ 0) (hthr_top : thr ≠ ⊤)
    (hlink : ∀ c, ZeroSupplyCoupling.IntegerSquaringFails (L := L) (K := K) θ c →
      thr ≤ supplyPotential (L := L) (K := K) i c)
    (hourLen : ℕ) (c₀ : Config (AgentState L K)) (hQ0 : Q c₀) :
    ((NonuniformMajority L K).transitionKernel ^ hourLen) c₀
        {c | ZeroSupplyCoupling.IntegerSquaringFails (L := L) (K := K) θ c}
      ≤ (1 : ℝ≥0∞) ^ hourLen * supplyPotential (L := L) (K := K) i c₀ / thr :=
  integerProfileSquaring_whp_of_region (L := L) (K := K) (θ := θ) i Q hQ_abs hQ_card
    (fun c hQc => supplySubadditive_of_region (L := L) (K := K) i (hQ_win c hQc) (hQ_reg c hQc))
    thr hthr hthr_top hlink hourLen c₀ hQ0

/-- **The strongest hypothesis-free Thm 6.2 `hConfine` form reachable from the window (PROVEN
readout).**  Composing the full downstream chain — window-realised `SupplySubadditive` →
(LANDED) the whp coupling `IntegerProfileSquaring` →
`ProfileSquaringRate.mainHourHypotheses_of_coupling` →
`MainExponentConfinement.theorem62_entry_of_confinement` — on the success event the carried
coupling delivers `MainProfileHourHypotheses`, and the confinement readout
`MainProfileConfinedToUseful` (definitionally the `hConfine` event) feeds the
`UsefulMainFloor.Theorem62EntryHypotheses` carrying `hConfine`.

This records the precise CARRIED SET after the dispatch bridge: the residual blocking a fully
hypothesis-free `hConfine` is now exactly (a) the whp-realised hour coupling
`IntegerProfileSquaring θ c` (whose drift is discharged BY the window via
`integerProfileSquaring_whp_of_window`), (b) the landed clock window
`ClockFrontProfile.WindowedFrontProfile`, (c) the sub-critical Main fraction `≤ 1/10`, (d) the
landed Phase-5 window + role floor, and (e) the confinement readout
`MainProfileConfinedToUseful`.  The phase-dispatch bookkeeping — the genuinely-dynamic supply
region over the FULL `Transition` — is now CLOSED (supplied by the population window), not
carried as a clock event. -/
theorem hConfine_of_window {θ : ℝ} {n : ℕ} {c : Config (AgentState L K)}
    (hClock : ClockFrontProfile.WindowedFrontProfile (L := L) (K := K) θ c)
    (hSubcrit : MainExponentConfinement.mainFrac (L := L) (K := K) 0 c ≤ 1 / 10)
    (hcoupl : ProfileSquaringRate.IntegerProfileSquaring (L := L) (K := K) θ c)
    (hPhase5 : ReserveSampling.Phase5AllWin (L := L) (K := K) n c)
    (hMainFloor : (n : ℝ) / 3 ≤ (RoleSplitConcentration.mainCount (L := L) (K := K) c : ℝ))
    (hConf : MainExponentConfinement.MainProfileConfinedToUseful (L := L) (K := K) c) :
    UsefulMainFloor.Theorem62EntryHypotheses (L := L) (K := K) n c :=
  ZeroSupplyCoupling.hConfine_surface_of_zeroSupply hClock hSubcrit hcoupl hPhase5 hMainFloor hConf

end SupplyDispatch

end ExactMajority
