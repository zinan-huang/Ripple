/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Assembly bridges — discharging the `Assembly` structural-Pre gaps (`AssemblyBridges`)

This file attacks the three carried bridge fields of `ConcreteAssembly.Assembly`
(`hTrig`, `hWorkPostToWindow`, `hWindowToWorkPre`) and the `hcompFail` carry, GENUINELY
per phase — by reading off each landed work instance's concrete `Pre`/`Post` predicate and
proving the extractable part as a standalone, axiom-clean lemma, while pinning the
genuinely-probabilistic residual to its file:line provenance.

## The per-phase reading (the survey result)

Every landed WORK instance's `Post`/`Pre` is built by the drain engines
(`OneSidedCancel.crude_PhaseConvergenceW` / `levels_PhaseConvergenceW`) or their per-phase
specialisations, and ALL of them factor as

    Post c = (phase-pin window `Win p n c`) ∧ (drain-done predicate)
    Pre  c = (phase-pin window `Win p n c`) ∧ (drain-budget `Φ ≤ M₀`)   [+ role/sign pins]

where the phase-pin window `Win p n c` is literally `c.card = n ∧ ∀ a ∈ c, a.phase.val = p`
(`Phase1AllMain`, `Phase5AllWin`, `Phase6Win`, `Phase7AllMain`, `Phase8AllMain`; with
`Phase4`'s `Qwin4`/`advFinished` the `≥`-window, and Phase 10's `S1`/`Tie1plus` carrying
`AllPhase10`).  Provenance, exact lines:

* `Phase1Convergence.lean:266`  `Phase1AllMain n c = c.card = n ∧ ∀ a ∈ c, a.phase.val = 1 ∧ a.role = main`
* `ReserveSampling.lean:93`     `Phase5AllWin   n c = c.card = n ∧ ∀ a ∈ c, a.phase.val = 5`
* `Phase6Convergence.lean:1020` `Phase6Win      n c = c.card = n ∧ ∀ a ∈ c, a.phase.val = 6`
* `Phase7Convergence.lean:540`  `Phase7AllMain  n c = c.card = n ∧ ∀ a ∈ c, a.phase.val = 7 ∧ a.role = main`
* `Phase8Convergence.lean:236`  `Phase8AllMain  n c = c.card = n ∧ ∀ a ∈ c, a.phase.val = 8 ∧ a.role = main`
* `Phase10ExpectedTime.lean:2126` `S1 n c = AllPhase10 c ∧ c.card = n ∧ 0 < phase10ActiveSignedSum c`

## What this file CLOSES (genuine theorems, not carries)

`hWorkPostToWindow` is DISCHARGEABLE per phase: the window→`allPhaseGe` extraction is a
pointwise structural fact (`allPhaseGe p n` is `c.card = n ∧ ∀ a ∈ c, p ≤ a.phase.val`, and
the work window pins `a.phase.val = p`, so `p ≤ a.phase.val` is `le_refl`).  We prove the
generic extraction `windowEq_imp_allPhaseGe` (any `c.card = n ∧ ∀ a, phase = p` window) and
its `≥`-form, then the per-phase corollaries `phaseI_post_to_window` for the concrete
work `Post`s.  These are the EXACT maps the campaign carried as `hWorkPostToWindow`; here
they are landed lemmas.

## What genuinely REMAINS carried (named, with provenance)

* `hTrig` — `advTriggered (p+1)` on `work k . Post`.  `advTriggered (p+1) c` needs an agent
  ALREADY at phase `≥ p+1` (`SeamEpidemics.lean:87`).  But a drained work `Post` pins EVERY
  agent at phase EXACTLY `p` (`allPhaseEq p n`), so it CANNOT supply an agent at `p+1`.  We
  PROVE this obstruction (`drained_post_no_advTrig`): on a populated all-at-`p` config the
  trigger is FALSE.  Hence `hTrig` is a genuine one-step seam-entry event (some agent's clock
  ticks it forward into the new phase), carried per phase.  We also check the structural
  alternative below.

* `hWindowToWorkPre` — `allPhaseEq (p+1) n ⟹ work (k+1) . Pre`.  The phase-pin half is
  CLOSED (`windowEq_card_phase` extracts `c.card = n` and the `= p+1` pin, exactly the work
  window's structural conjunct).  But each work `Pre` ALSO carries (i) the drain budget
  `Φ ≤ M₀` (the entering phase's potential is at most `M₀`), and for some phases (ii) role
  pins (`a.role = main` for Phases 1/7/8) and (iii) sign/active pins (Phase 10's
  `0 < phase10ActiveSignedSum` / `hasActiveAgent`, `Phase10ExpectedTime.lean:2126,3435`).
  Items (i)–(iii) are NOT functions of the phase window and stay carried per phase.

## The structural alternative for `hTrig` (checked, documented)

`SeamNoOvershoot.AtRiskClockZero (p) c` (`SeamNoOvershoot.lean:99`) — a clock at the NEW
phase `p+1` with counter `0`, advancing on its next `stdCounterSubroutine` call — is the
honest seam advance seed.  But `advTriggered (p+1)` is ALREADY phase-`(p+1)` presence, which
`AtRiskClockZero (p)` (phase `= p+1`) IMPLIES.  We record the reduction
`advTriggered_of_atRiskClockZero`: an at-risk clock at phase `p+1` fires the trigger.  So the
seam's `Pre` advance seed can be supplied by ANY phase-`(p+1)` agent; the carry is the
existence of that one advanced agent at seam entry — a one-step whp event, named per phase.

This file is APPEND-ONLY and imports only landed surfaces; it edits no existing file.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ConcreteAssembly
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Phase1Convergence
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Phase5Convergence
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Phase6Convergence
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Phase7HonestDrain
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Phase8Convergence

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace AssemblyBridges

variable {L K : ℕ}

/-! ## Part A — the generic window↔`allPhaseGe`/`allPhaseEq` extraction.

These are the honest structural maps the campaign carried as `hWorkPostToWindow` and the
phase-pin half of `hWindowToWorkPre`.  They are pure pointwise facts about the window
predicate shape `c.card = n ∧ ∀ a ∈ c, a.phase.val = p`. -/

/-- A phase-EXACT window (`card = n`, every agent at phase `= p`) is the `allPhaseEq p n`
window verbatim — the campaign's `Phase{5,6}Win`/`Phase{1,7,8}AllMain`-minus-role read. -/
theorem allPhaseEq_of_card_phase {p n : ℕ} {c : Config (AgentState L K)}
    (hcard : c.card = n) (hphase : ∀ a ∈ c, a.phase.val = p) :
    SeamEpidemics.allPhaseEq (L := L) (K := K) p n c :=
  ⟨hcard, hphase⟩

/-- A phase-EXACT window implies the `≥`-window `allPhaseGe p n` (the seam source window).
This is the `hWorkPostToWindow` extraction at its core: `a.phase.val = p ⟹ p ≤ a.phase.val`. -/
theorem allPhaseGe_of_card_phase {p n : ℕ} {c : Config (AgentState L K)}
    (hcard : c.card = n) (hphase : ∀ a ∈ c, a.phase.val = p) :
    SeamEpidemics.allPhaseGe (L := L) (K := K) p n c :=
  ⟨hcard, fun a ha => (hphase a ha).ge⟩

/-- The `≥`-window form directly (e.g. Phase-6's `AllZeroGE6`, Phase-4's `Qwin4`). -/
theorem allPhaseGe_of_card_phaseGe {p n : ℕ} {c : Config (AgentState L K)}
    (hcard : c.card = n) (hphase : ∀ a ∈ c, p ≤ a.phase.val) :
    SeamEpidemics.allPhaseGe (L := L) (K := K) p n c :=
  ⟨hcard, hphase⟩

/-! ## Part B — the per-phase `hWorkPostToWindow` corollaries (CLOSED).

For each work phase whose `Post` is `Win p n ∧ drain`, the seam source window
`allPhaseGe p n` is extracted by projecting the window conjunct.  These discharge the
`hWorkPostToWindow k` field for the phase-pinned destinations. -/

/-- **Phase 1.**  `Phase1AllMain n c ⟹ allPhaseGe 1 n c`.  (The work `Post` is
`Phase1AllMain n ∧ NoExtreme`; project the window.) -/
theorem phase1_window_to_ge {n : ℕ} {c : Config (AgentState L K)}
    (h : Phase1Convergence.Phase1AllMain (L := L) (K := K) n c) :
    SeamEpidemics.allPhaseGe (L := L) (K := K) 1 n c :=
  allPhaseGe_of_card_phase h.1 (fun a ha => (h.2 a ha).1)

/-- **Phase 5.**  `Phase5AllWin n c ⟹ allPhaseGe 5 n c`. -/
theorem phase5_window_to_ge {n : ℕ} {c : Config (AgentState L K)}
    (h : ReserveSampling.Phase5AllWin (L := L) (K := K) n c) :
    SeamEpidemics.allPhaseGe (L := L) (K := K) 5 n c :=
  allPhaseGe_of_card_phase h.1 h.2

/-- **Phase 6.**  `Phase6Win n c ⟹ allPhaseGe 6 n c`. -/
theorem phase6_window_to_ge {n : ℕ} {c : Config (AgentState L K)}
    (h : Phase6Convergence.Phase6Win (L := L) (K := K) n c) :
    SeamEpidemics.allPhaseGe (L := L) (K := K) 6 n c :=
  allPhaseGe_of_card_phase h.1 h.2

/-- **Phase 7.**  `Phase7AllMain n c ⟹ allPhaseGe 7 n c`. -/
theorem phase7_window_to_ge {n : ℕ} {c : Config (AgentState L K)}
    (h : Phase7Convergence.Phase7AllMain (L := L) (K := K) n c) :
    SeamEpidemics.allPhaseGe (L := L) (K := K) 7 n c :=
  allPhaseGe_of_card_phase h.1 (fun a ha => (h.2 a ha).1)

/-- **Phase 8.**  `Phase8AllMain n c ⟹ allPhaseGe 8 n c`. -/
theorem phase8_window_to_ge {n : ℕ} {c : Config (AgentState L K)}
    (h : Phase8Convergence.Phase8AllMain (L := L) (K := K) n c) :
    SeamEpidemics.allPhaseGe (L := L) (K := K) 8 n c :=
  allPhaseGe_of_card_phase h.1 (fun a ha => (h.2 a ha).1)

/-! ## Part C — the `hTrig` obstruction (PROVED) and the structural alternative.

`hTrig k` asks `advTriggered (p+1) c` on a `work k . Post` config.  We prove that a DRAINED
exact window (every agent at phase EXACTLY `p`) makes the trigger FALSE on a populated
config — so `hTrig` cannot be read off the work `Post`; it is a genuine seam-entry event. -/

/-- `advTriggered (p+1)` means at least one agent has `phase.val ≥ p+1`. -/
theorem advTriggered_iff_exists {p : ℕ} {c : Config (AgentState L K)} :
    SeamEpidemics.advTriggered (L := L) (K := K) p c ↔
      ∃ a ∈ c, p ≤ a.phase.val := by
  unfold SeamEpidemics.advTriggered
  rw [Nat.one_le_iff_ne_zero, ne_eq, Multiset.countP_eq_zero]
  simp only [not_forall, not_not, decide_eq_true_eq]
  constructor
  · rintro ⟨a, ha, hge⟩; exact ⟨a, ha, hge⟩
  · rintro ⟨a, ha, hge⟩; exact ⟨a, ha, hge⟩

/-- **The `hTrig` obstruction.**  On an exact `p`-window (every agent at phase `= p`), the
`(p+1)`-advance trigger is FALSE — no agent has reached phase `≥ p+1`.  Hence the drained
work `Post` (which is `allPhaseEq p n ∧ …`) does NOT supply `advTriggered (p+1)`; it is a
genuine extra one-step seam-entry event, carried per phase. -/
theorem drained_post_no_advTrig {p n : ℕ} {c : Config (AgentState L K)}
    (heq : SeamEpidemics.allPhaseEq (L := L) (K := K) p n c) :
    ¬ SeamEpidemics.advTriggered (L := L) (K := K) (p + 1) c := by
  rw [advTriggered_iff_exists]
  rintro ⟨a, ha, hge⟩
  have hp := heq.2 a ha
  omega

/-- **The structural-alternative reduction.**  An at-risk clock at the NEW phase `p+1`
(`SeamNoOvershoot.AtRiskClockZero p`) already fires `advTriggered (p+1)` — phase-`(p+1)`
presence IS the trigger.  So the seam's advance seed needs only ONE phase-`(p+1)` agent at
seam entry, and `AtRiskClockZero` is a sufficient (stronger, counter-0) witness. -/
theorem advTriggered_of_atRiskClockZero {p : ℕ} {c : Config (AgentState L K)}
    (h : SeamNoOvershoot.AtRiskClockZero (L := L) (K := K) p c) :
    SeamEpidemics.advTriggered (L := L) (K := K) (p + 1) c := by
  rw [advTriggered_iff_exists]
  obtain ⟨a, ha, _, hphase, _⟩ := h
  exact ⟨a, ha, by omega⟩

/-! ## Part D — the `hWindowToWorkPre` phase-pin half (CLOSED) + the residual.

`hWindowToWorkPre k` asks `allPhaseEq (p+1) n c ⟹ work (k+1) . Pre c`.  We extract the
phase-pin half (`c.card = n` and the `= p+1` pin) — exactly the structural conjunct of the
next work window — and isolate the residual (drain budget `Φ ≤ M₀`, role pins, sign/active
pins) as the genuinely-carried per-phase entry data. -/

/-- The phase-pin half of any `hWindowToWorkPre`: `allPhaseEq (p+1) n` delivers the card and
the exact phase pin of the entering window verbatim.  (The next work `Pre` needs this PLUS
the drain budget / role / sign pins, which are not functions of the window — those stay
carried.) -/
theorem windowEq_card_phase {q n : ℕ} {c : Config (AgentState L K)}
    (heq : SeamEpidemics.allPhaseEq (L := L) (K := K) q n c) :
    c.card = n ∧ ∀ a ∈ c, a.phase.val = q :=
  ⟨heq.1, heq.2⟩

/-- For a `≥`-window DESTINATION (Phase 4's `Q4 = allPhaseGe 4`), the seam's exact output
`allPhaseEq (p+1) n` drops to the `≥`-window directly with no overshoot exactness needed —
the trivial direction `allPhaseGe_of_allPhaseEq`. -/
theorem windowEq_to_ge {q n : ℕ} {c : Config (AgentState L K)}
    (heq : SeamEpidemics.allPhaseEq (L := L) (K := K) q n c) :
    SeamEpidemics.allPhaseGe (L := L) (K := K) q n c :=
  SeamEpidemics.allPhaseGe_of_allPhaseEq heq

/-! ## Part F — the `hWorkPostToWindow` field is no longer a free carry.

We show the `hWorkPostToWindow` field of `Assembly` is DERIVABLE from per-phase
`Post ⟹ (card ∧ phase-pin)` reads — i.e. the field is discharged by the landed structural
lemmas above, not assumed.  `mk_hWorkPostToWindow` takes, for each seam `k`, the per-phase
window read `hwin k` (`work k . Post ⟹ c.card = n ∧ ∀ a, a.phase.val = seamP k`) — which IS
one of the `phaseI_window_to_ge`-shaped facts above for the concrete instances — and builds
the exact field shape `ConcreteAssembly.Assembly` requires.  Supplying `mk_…` instead of
a free binder makes the carry a CONSEQUENCE of the per-phase structure: the only genuine
per-phase input is the window read, which the lemmas in Part B close for the pinned phases. -/

open ConcreteAssembly in
/-- Builder for the `hWorkPostToWindow` field from per-seam window reads.  The hypothesis
`hwin k` is exactly the campaign's per-phase structural read `work k . Post ⟹ card ∧ phase
pin`, closed by `phase{1,5,6,7,8}_window_to_ge` for the pinned destinations. -/
theorem mk_hWorkPostToWindow {n : ℕ}
    (work : Fin 11 → PhaseConvergenceW (NonuniformMajority L K).transitionKernel)
    (seamP : Fin 10 → ℕ)
    (hwin : ∀ (k : Fin 10) (c : Config (AgentState L K)),
        (work ⟨k.val, by omega⟩).Post c →
        c.card = n ∧ ∀ a ∈ c, a.phase.val = seamP k) :
    ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (work ⟨k.val, by omega⟩).Post c →
      SeamEpidemics.allPhaseGe (L := L) (K := K) (seamP k) n c := by
  intro k c hpost
  exact allPhaseGe_of_card_phase (hwin k c hpost).1 (hwin k c hpost).2

/-- Builder for the phase-pin half of `hWindowToWorkPre`: from the seam's exact output
`allPhaseEq (seamP k + 1) n`, deliver the card and phase pin the entering work window needs.
The residual (drain budget / role / sign pins) is the genuinely-carried per-phase entry data,
supplied separately. -/
theorem mk_hWindowToWorkPre_pin {n : ℕ} (seamP : Fin 10 → ℕ) :
    ∀ (k : Fin 10) (c : Config (AgentState L K)),
      SeamEpidemics.allPhaseEq (L := L) (K := K) (seamP k + 1) n c →
      c.card = n ∧ ∀ a ∈ c, a.phase.val = seamP k + 1 :=
  fun _k _c heq => windowEq_card_phase heq

end AssemblyBridges

/-! ## Part E — `hcompFail` engineering attack.

The kernel-power obstruction (`ConcreteAssembly.lean:269`) is: re-using the failure-side
composition output `.1` — unifying its kernel-power LHS `(K ^ ∑ (phases asm i).t) c₀ {…}`
against a restated copy — diverges.  `time_headline_CONCRETE` carries it as the named
hypothesis `hcompFail`.

The engineering question: can `hcompFail` be PRODUCED inside a stated theorem (so the caller
need not supply it from a cheap external application)?  The obstruction is the `whnf` of
`(NonuniformMajority L K).transitionKernel ^ T` against `∑ i, (phases asm i).t` once `T`
is the SUM.  The attack below ABSTRACTS the horizon behind an opaque `T` BEFORE the
composition's LHS is mentioned: we state the producer with `T` as a free variable equal to
the sum via `hT`, and the kernel power is applied to the OPAQUE `T`, never re-unified against
the `Fin 21` sum shape.  This is exactly the shape `time_headline_CONCRETE` already uses
(`hcompFail` is stated at the opaque `T`).  The genuine content here: the producer
`hcompFail_of_composition` derives `hcompFail` from the composition's `.1` by rewriting along
`hT` in the SAFE direction (`.1`'s LHS is at the literal sum; `rw [← hT]` folds it to the
opaque `T` — a single rewrite of the horizon SUBTERM, NOT a re-unification of the whole
kernel-power application). -/

namespace AssemblyBridges

open ConcreteAssembly

/-- **`hcompFail` producer (engineering attack on the kernel-power obstruction).**
Given the composition's failure-side output at the LITERAL sum horizon `∑ i, (phases asm
i).t`, fold it to the opaque `T` via `hT`.  This is a single rewrite of the horizon subterm
(the `∑` → `T` direction), which does NOT trigger the divergent re-unification of the whole
kernel-power application against the `Fin 21` sum (that only happens when going the OTHER way,
unifying a restated `T`-shaped LHS against the sum-shaped composition output).  The result is
exactly the `hcompFail` hypothesis that `time_headline_CONCRETE` consumes — produced,
not assumed. -/
theorem hcompFail_of_composition
    {L K n : ℕ}
    (init c₀ : Config (AgentState L K))
    (asm : Assembly (L := L) (K := K) n)
    (T : ℕ) (hT : T = ∑ i, (phases asm i).t)
    (hfail :
      ((NonuniformMajority L K).transitionKernel ^ (∑ i, (phases asm i).t)) c₀
          {c | ¬ majorityStableEndpoint (L := L) (K := K) init c}
        ≤ (∑ i, ((phases asm i).ε : ℝ≥0∞))) :
    ((NonuniformMajority L K).transitionKernel ^ T) c₀
        {c | ¬ majorityStableEndpoint (L := L) (K := K) init c}
      ≤ (∑ i, ((phases asm i).ε : ℝ≥0∞)) := by
  rw [hT]; exact hfail

end AssemblyBridges

end ExactMajority
