/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Phase0RoleSplitDischarge — discharging `work⟨0⟩` of the faithful cascade.

`work⟨0⟩` of the faithful cascade
(`Capstone.theorem_3_1_faithful`) is the phase-0 ROLE-SPLIT
survival, assembled by `EndpointWiring.roleSplitW_of_two_stage` (the landed
three-stage Chapman–Kolmogorov composer
`RoleSplitConcentration.phase0_roleSplit_whp_two_stage`).  Its three stage
`PhaseConvergenceW` instances + two chain links are the PARAMETERS that carry the
deep §5 role-split concentration (Doty Lemma 5.1 population-splitting Chernoff +
Lemma 5.2 Janson hitting-time).  Discharging `work⟨0⟩` = SUPPLYING those three
stages.  This file builds them off the landed machinery, isolating the single
irreducible probabilistic residual precisely.

## What of the three stages is LANDED vs carried

  * **Stage 2** (`crCount` R4-diagonal drain) — the εfloor is structurally
    ABSENT.  On the gate `noMCRShell n = {card = n ∧ roleMCRCount = 0}` no rule
    produces an `RoleMCR` (`Transition_roleMCRCount_noMCR_pair`), so the gate is
    genuinely ABSORBING and the killed-kernel escape mass is identically zero
    (`RoleSplitConcentration.noMCRShell_killedEscape_eq_zero`).  Hence Stage 2 has
    NO floor obligation; its only carried datum is the Janson hitting-time tail of
    its `crCount` milestone family.  This is the strictly-lighter stage.

  * **Stages 1 + 1.5** (`mcrCount` drain to `0`) — the genuine Lemma-5.1 Chernoff
    `εfloor`.  The full structural side is LANDED: `phase0_stage1_whp_final` bounds
    the real `t`-step bad mass `¬ roleSplitGoodMile` by the Janson tail PLUS the
    floor-escape union budget `t·q + ∑_{τ<t} P(assignableCount < a₀ at τ)`.  The
    per-step gate-escape rate `q` and the `floorGateᶜ`-prefix mass are the
    irreducible Lemma-5.1 floor-concentration content — the in-house
    `exp(−s·assignableCount)` real-kernel drift the campaign isolated as NOT
    assemblable from the deterministic count atoms (R4 drains the assignable pool
    concurrently with `mcrCount > 0`; see the doctrine in `RoleSplitConcentration`,
    lines 3513–3553).  We carry it as the satisfiable, refutation-checked bundle
    `Stage1FloorResidual` and PROVE the stage-1 `PhaseConvergenceW` from it.

## What this file delivers

  * `Stage1FloorResidual` — the precise carried bundle for the `mcrCount`-drain
    stage: the floor-Chernoff `(q, lam, t)` plus the headline-budget bound that the
    Janson tail and the escape prefix together sit below a named `ε`.  Proven
    SATISFIABLE (`stage1FloorResidual_satisfiable`) so the downstream
    `PhaseConvergenceW` is NOT a vacuous conditional.
  * `stage1W_of_residual` — the Stage-1 `PhaseConvergenceW`, built from
    `phase0_stage1_whp_final` + `Stage1FloorResidual`.  `Pre = Phase0Initial ∧
    c₀ ∈ floorGate`, `Post = roleSplitGoodMile`, with the carried budget as `ε`.
  * `roleSplitWork0` — `work⟨0⟩`, assembled via `roleSplitW_of_two_stage` from the
    three supplied stages and the two chain links.  `Post = stage2.Post`.

## ANTI-TRAP compliance (the six caught patterns)

  * NO `InvClosed` of a phase window: the floor enters as the killed-kernel ADDITIVE
    escape budget (`real_bad_le_janson_add_escape`), never as a deterministic
    `inv_closed`.  Stage 2's gate is absorbing — escape `≡ 0`, not an inv-window.
  * Role-assignment count is monotone-INCREASING → milestone fine, progress is a
    per-step LOWER bound (the `floorRate` rate of `roleSplitKernelMilestone`).
  * NO bare-universal floor: the floor holds on the floor-GATE
    (`a₀ ≤ assignableCount`), NOT `∀ c`; the residual `q`/prefix are quantified over
    the gate, carried as hypotheses.
  * NO non-contracting drain: every stage's `convergence` is the genuine Janson
    contraction.
  * Every carried residual REFUTATION-CHECKED satisfiable
    (`stage1FloorResidual_satisfiable`, `roleSplitGood_does_not_pin_floor`).

This file is APPEND-ONLY and edits NO existing file.  Single-file `lake env lean`.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.EndpointWiring
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.RoleSplitConcentration
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Phase0Window
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.PhaseConvergenceWeak
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.JansonHitting
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Phase15ClockTailDepletion
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ReachableClockTail
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockCounterDepthCover

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal Real

namespace Phase0RoleSplitDischarge

variable {L K : ℕ}

/-- The cemetery extension carries the discrete (`⊤`) measurable space (matches
`GatedDrift.instOptionMSnow` / `RoleSplitConcentration.instOptionMSrsc`, supplied here
so the `KernelMilestone (killK_now …)` accessors `meanTime`/`pMin` typecheck in this
file). -/
local instance instOptionMSp0d {α : Type*} : MeasurableSpace (Option α) := ⊤
local instance instOptionDMSp0d {α : Type*} : DiscreteMeasurableSpace (Option α) :=
  ⟨fun _ => trivial⟩

/-- The `τ`-fold monoid power of a Markov kernel is a Markov kernel (induction over
`pow_succ` + the `∘ₖ` Markov instance).  Needed so `((K^τ) c₀)` is a probability
measure (`prob_le_one`). -/
instance isMarkovKernel_pow {α : Type*} [MeasurableSpace α]
    (κ : Kernel α α) [IsMarkovKernel κ] (τ : ℕ) : IsMarkovKernel (κ ^ τ) := by
  induction τ with
  | zero =>
      rw [pow_zero]
      show IsMarkovKernel (Kernel.id : Kernel α α)
      infer_instance
  | succ m ih =>
      rw [pow_succ]
      haveI := ih
      show IsMarkovKernel ((κ ^ m) ∘ₖ κ)
      infer_instance

/-! ## Part 1 — the Stage-1 (`mcrCount`-drain) floor residual (Doty Lemma 5.1 Chernoff).

The structural side of Stage 1 is the LANDED headline
`RoleSplitConcentration.phase0_stage1_whp_final`: from a `Phase0Initial` start in
the floor gate, the real `t`-step mass on `¬ roleSplitGoodMile` is at most

  Janson tail  +  ( t·q  +  ∑_{τ<t} P(c₀ leaves floorGate at τ) ).

The Janson tail is `exp(−pMin·meanTime·(lam−1−log lam))` with the floor-driven
`pMin·meanTime = Θ(log n)` (`roleSplitKernelMilestone_pMin_meanTime`).  The two
genuinely-probabilistic numbers — the per-step gate-escape rate `q` and the
`floorGateᶜ`-prefix mass — are the irreducible Lemma-5.1 floor content.

`Stage1FloorResidual` packages EXACTLY the inputs `phase0_stage1_whp_final`
consumes plus the budget bound that pins the whole RHS below a named `ε`.  It is a
TRUE residual (carries the deep paper Chernoff), refutation-checked satisfiable
below, NOT a false universal. -/

/-- **The Stage-1 floor residual (Doty Lemma 5.1 Chernoff content).**  The bundle
of genuinely-probabilistic data the landed `phase0_stage1_whp_final` headline
consumes, for a fixed start `c₀` and population/floor parameters:

  * `lam ≥ 1`, the Janson tilt; `t`, the horizon `≥ lam·meanTime`;
  * `q`, the per-step gate-escape rate, with the gate-Lipschitz hypothesis `hstep`;
  * `hbudget`, the budget bound: the Janson tail + the escape union budget
    `t·q + ∑_{τ<t} P(leave floorGate at τ)` together sit below `ε`.

This is the precise irreducible Lemma-5.1 floor-concentration content the campaign
isolated (the in-house `exp(−s·assignableCount)` drift — see
`RoleSplitConcentration` lines 3513–3553); carried as a hypothesis bundle, NOT
faked. -/
structure Stage1FloorResidual (n a₀ : ℕ) (hn2 : 2 ≤ n) (ha1 : 1 ≤ a₀)
    (ha_le : a₀ ≤ n - 1) (c₀ : Config (AgentState L K)) (ε : ℝ≥0) where
  /-- The Janson tilt. -/
  lam : ℝ
  /-- The horizon. -/
  t : ℕ
  /-- The per-step gate-escape rate. -/
  q : ℝ≥0∞
  /-- `lam ≥ 1` (Janson admissibility). -/
  hlam : 1 ≤ lam
  /-- The horizon clears `lam · meanTime`. -/
  ht : lam *
      (RoleSplitConcentration.roleSplitKernelMilestone
        (L := L) (K := K) n a₀ hn2 ha1 ha_le).meanTime ≤ (t : ℝ)
  /-- The gate-Lipschitz hypothesis: from every gated state in `floorGate`, the
  one-step gate-exit probability is `≤ q` (the floor-breach rate). -/
  hstep : ∀ x ∈ RoleSplitConcentration.floorGate (L := L) (K := K) n a₀,
      x ∈ RoleSplitConcentration.floorGate (L := L) (K := K) n a₀ →
      (NonuniformMajority L K).transitionKernel x
        (RoleSplitConcentration.floorGate (L := L) (K := K) n a₀)ᶜ ≤ q
  /-- The start lies in the floor gate. -/
  hc₀ : c₀ ∈ RoleSplitConcentration.floorGate (L := L) (K := K) n a₀
  /-- **The budget bound** — the whole `phase0_stage1_whp_final` RHS (Janson tail +
  escape union budget) sits below `ε`.  This is where the Chernoff `O(1/n²)`
  accounting is consumed. -/
  hbudget :
    ENNReal.ofReal (Real.exp
        (-(RoleSplitConcentration.roleSplitKernelMilestone
            (L := L) (K := K) n a₀ hn2 ha1 ha_le).pMin *
          (RoleSplitConcentration.roleSplitKernelMilestone
            (L := L) (K := K) n a₀ hn2 ha1 ha_le).meanTime *
          (lam - 1 - Real.log lam))) +
      ((t : ℝ≥0∞) * q +
        ∑ τ ∈ Finset.range t,
          ((NonuniformMajority L K).transitionKernel ^ τ) c₀
            (RoleSplitConcentration.floorGate (L := L) (K := K) n a₀)ᶜ)
      ≤ (ε : ℝ≥0∞)

/-! ## Part 2 — refutation check: the residual is SATISFIABLE (not a vacuous premise).

`#print axioms` cannot detect an unsatisfiable hypothesis bundle (a conditional
theorem with a false premise is mechanically green but vacuous).  We exhibit a
concrete inhabitant of `Stage1FloorResidual` over a non-degenerate domain to
certify the carried residual is TRUE content, not a hidden `False`. -/

/-- **Refutation check: `Stage1FloorResidual` is satisfiable (for some budget `ε`).**
For ANY start `c₀` in the floor gate, taking the escape rate `q := 1` (the trivial
finite upper bound), a sufficiently long horizon `t := ⌈meanTime⌉₊`, and `lam := 1`,
the headline RHS is a FIXED FINITE `ℝ≥0∞` value `R < ⊤` (the Janson `ofReal` tail is
finite, `t·q = t·1` is finite, and the `t`-term prefix sum of probability masses is
finite).  Choosing `ε := R.toNNReal` makes `hbudget` the equality `R ≤ R`, so the
bundle is inhabited.  This certifies the downstream `PhaseConvergenceW` is NOT a
vacuous conditional: the carried premise is consistent over the floor-gate domain.

(The QUANTITATIVE `O(1/n²)` budget — `ε = n^{-2}`-shape — is the genuine Lemma-5.1
Chernoff CONTENT; that is what is carried.  Here we only refute vacuity: the bundle
type is inhabited, so no `False` is smuggled into the premise.) -/
theorem stage1FloorResidual_satisfiable
    (n a₀ : ℕ) (hn2 : 2 ≤ n) (ha1 : 1 ≤ a₀) (ha_le : a₀ ≤ n - 1)
    (c₀ : Config (AgentState L K))
    (hc₀ : c₀ ∈ RoleSplitConcentration.floorGate (L := L) (K := K) n a₀) :
    ∃ ε : ℝ≥0,
      Nonempty (Stage1FloorResidual (L := L) (K := K) n a₀ hn2 ha1 ha_le c₀ ε) := by
  classical
  set mt := (RoleSplitConcentration.roleSplitKernelMilestone
    (L := L) (K := K) n a₀ hn2 ha1 ha_le).meanTime with hmt
  set pm := (RoleSplitConcentration.roleSplitKernelMilestone
    (L := L) (K := K) n a₀ hn2 ha1 ha_le).pMin with hpm
  -- the headline RHS at `lam = 1`, `q = 1`, `t = ⌈mt⌉₊`.
  set t₀ := ⌈mt⌉₊ with ht₀
  set R : ℝ≥0∞ :=
      ENNReal.ofReal (Real.exp (-pm * mt * ((1 : ℝ) - 1 - Real.log 1))) +
        ((t₀ : ℝ≥0∞) * 1 +
          ∑ τ ∈ Finset.range t₀,
            ((NonuniformMajority L K).transitionKernel ^ τ) c₀
              (RoleSplitConcentration.floorGate (L := L) (K := K) n a₀)ᶜ) with hR
  -- R is finite: a finite `ofReal` + a finite product + a finite sum of `≤ 1` masses.
  have hR_lt_top : R < ⊤ := by
    rw [hR]
    refine ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top, ?_⟩
    refine ENNReal.add_lt_top.mpr ⟨?_, ?_⟩
    · exact ENNReal.mul_lt_top (by exact_mod_cast (ENNReal.natCast_lt_top t₀)) ENNReal.one_lt_top
    · -- finite sum of probability masses, each `≤ 1` (Markov kernel power).
      refine (ENNReal.sum_lt_top).mpr ?_
      intro τ _
      exact lt_of_le_of_lt prob_le_one ENNReal.one_lt_top
  refine ⟨R.toNNReal, ⟨{
    lam := 1
    t := t₀
    q := 1
    hlam := le_refl 1
    ht := ?_
    hstep := ?_
    hc₀ := hc₀
    hbudget := ?_ }⟩⟩
  · -- `1 · mt ≤ ⌈mt⌉₊`.
    rw [one_mul]; simpa [ht₀] using Nat.le_ceil mt
  · -- the floor-breach rate `q := 1` is the trivial Markov upper bound.
    intro x _ _; exact prob_le_one
  · -- the RHS at these values is exactly `R` (folded by `set`), and
    -- `R ≤ (R.toNNReal : ℝ≥0∞) = R`.
    rw [ENNReal.coe_toNNReal hR_lt_top.ne]

/-! ## Part 3 — the Stage-1 `PhaseConvergenceW`, built from the residual.

`stage1W_of_residual` packages `phase0_stage1_whp_final` as a `PhaseConvergenceW`:
`Pre c = Phase0Initial n c ∧ c ∈ floorGate n a₀`, `Post = roleSplitGoodMile n hn2`,
`t = w.t`, `ε = ε`.  The `convergence` field is exactly the landed headline applied
through the carried `Stage1FloorResidual` budget. -/

/-- **`stage1W_of_residual` — the Stage-1 (`mcrCount`-drain) `PhaseConvergenceW`.**
Built from the landed `RoleSplitConcentration.phase0_stage1_whp_final` and the
carried, refutation-checked `Stage1FloorResidual w`.  The `Pre` couples the
`Phase0Initial` all-`RoleMCR` start with floor-gate membership (both consumed by the
headline); the `Post` is `roleSplitGoodMile` (`mcrCount ≤ 1`); the `ε` is the carried
floor-Chernoff budget. -/
noncomputable def stage1W_of_residual
    (n a₀ : ℕ) (hn2 : 2 ≤ n) (ha1 : 1 ≤ a₀) (ha_le : a₀ ≤ n - 1)
    (ε : ℝ≥0)
    (w : ∀ c₀, RoleSplitConcentration.Phase0Initial (L := L) (K := K) n c₀ →
        c₀ ∈ RoleSplitConcentration.floorGate (L := L) (K := K) n a₀ →
        Stage1FloorResidual (L := L) (K := K) n a₀ hn2 ha1 ha_le c₀ ε)
    (tt : ℕ)
    (htt : ∀ c₀ (hinit : RoleSplitConcentration.Phase0Initial (L := L) (K := K) n c₀)
        (hg : c₀ ∈ RoleSplitConcentration.floorGate (L := L) (K := K) n a₀),
        (w c₀ hinit hg).t = tt) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel where
  Pre c := RoleSplitConcentration.Phase0Initial (L := L) (K := K) n c ∧
    c ∈ RoleSplitConcentration.floorGate (L := L) (K := K) n a₀
  Post c := RoleSplitConcentration.roleSplitGoodMile (L := L) (K := K) n hn2 c
  t := tt
  ε := ε
  convergence := by
    rintro c₀ ⟨hinit, hg⟩
    set hw := w c₀ hinit hg with hwdef
    have hheadline := RoleSplitConcentration.phase0_stage1_whp_final
      (L := L) (K := K) n a₀ hn2 ha1 ha_le hw.q hw.hstep hinit hg hw.lam hw.hlam
      hw.t hw.ht
    -- rewrite the GOAL horizon `tt` back to `hw.t` (`hw.t = (w c₀ hinit hg).t = tt`),
    -- so the landed headline + the carried budget chain directly.
    have hteq : hw.t = tt := by rw [hwdef]; exact htt c₀ hinit hg
    rw [← hteq]
    exact le_trans hheadline hw.hbudget

@[simp] theorem stage1W_of_residual_Post
    (n a₀ : ℕ) (hn2 : 2 ≤ n) (ha1 : 1 ≤ a₀) (ha_le : a₀ ≤ n - 1)
    (ε : ℝ≥0)
    (w : ∀ c₀, RoleSplitConcentration.Phase0Initial (L := L) (K := K) n c₀ →
        c₀ ∈ RoleSplitConcentration.floorGate (L := L) (K := K) n a₀ →
        Stage1FloorResidual (L := L) (K := K) n a₀ hn2 ha1 ha_le c₀ ε)
    (tt : ℕ)
    (htt : ∀ c₀ (hinit : RoleSplitConcentration.Phase0Initial (L := L) (K := K) n c₀)
        (hg : c₀ ∈ RoleSplitConcentration.floorGate (L := L) (K := K) n a₀),
        (w c₀ hinit hg).t = tt) :
    (stage1W_of_residual (L := L) (K := K) n a₀ hn2 ha1 ha_le ε w tt htt).Post =
      fun c => RoleSplitConcentration.roleSplitGoodMile (L := L) (K := K) n hn2 c := rfl

/-! ## Part 3.5 — Stage 1.5, the terminal `RoleMCR` drain as a timed gate.

This is the Stage-1.5 structural core: the last `RoleMCR` is killed by the same
floor-driven one-sided interaction used in Stage 1, but only on the timed gate

```lean
floorGate n a₀ ∩ {c | roleMCRCount c ≤ 1}.
```

The gate is deliberately NOT claimed to be a global invariant.  Exiting it is
charged to the killed-kernel escape prefix.  In the intended Doty framing that
escape prefix is where the phase-0 clock/no-advance event and the maintained
floor event are unioned.
-/

/-- Stage-1.5 gate: the Stage-1 floor gate plus the Stage-1 endpoint fact
`roleMCRCount ≤ 1`.  Alive states of the killed chain satisfy exactly the
hypotheses needed for the last-particle conversion rate; leaving the gate is
an additive timed-event escape, not an invariant violation to be ignored. -/
def stage15Gate (n a₀ : ℕ) : Set (Config (AgentState L K)) :=
  {c | c ∈ RoleSplitConcentration.floorGate (L := L) (K := K) n a₀ ∧
    Phase0Window.allPhase0 (L := L) (K := K) c ∧
    RoleSplitConcentration.roleMCRCount (L := L) (K := K) c ≤ 1}

theorem stage15Gate_floorGate {n a₀ : ℕ} {c : Config (AgentState L K)}
    (hc : c ∈ stage15Gate (L := L) (K := K) n a₀) :
    c ∈ RoleSplitConcentration.floorGate (L := L) (K := K) n a₀ := hc.1

theorem stage15Gate_allPhase0 {n a₀ : ℕ} {c : Config (AgentState L K)}
    (hc : c ∈ stage15Gate (L := L) (K := K) n a₀) :
    Phase0Window.allPhase0 (L := L) (K := K) c := hc.2.1

theorem stage15Gate_card {n a₀ : ℕ} {c : Config (AgentState L K)}
    (hc : c ∈ stage15Gate (L := L) (K := K) n a₀) : Multiset.card c = n :=
  RoleSplitConcentration.floorGate_card (L := L) (K := K)
    (stage15Gate_floorGate (L := L) (K := K) hc)

theorem stage15Gate_floor {n a₀ : ℕ} {c : Config (AgentState L K)}
    (hc : c ∈ stage15Gate (L := L) (K := K) n a₀) :
    a₀ ≤ RoleSplitConcentration.assignableCount (L := L) (K := K) c :=
  RoleSplitConcentration.floorGate_floor (L := L) (K := K)
    (stage15Gate_floorGate (L := L) (K := K) hc)

theorem stage15Gate_phase0 {n a₀ : ℕ} {c : Config (AgentState L K)}
    (hc : c ∈ stage15Gate (L := L) (K := K) n a₀) :
    ∀ a ∈ c, a.role = .mcr → a.phase.val = 0 :=
  RoleSplitConcentration.floorGate_phase0 (L := L) (K := K)
    (stage15Gate_floorGate (L := L) (K := K) hc)

theorem stage15Gate_roleMCR_le_one {n a₀ : ℕ} {c : Config (AgentState L K)}
    (hc : c ∈ stage15Gate (L := L) (K := K) n a₀) :
    RoleSplitConcentration.roleMCRCount (L := L) (K := K) c ≤ 1 := hc.2.2

/-- A terminal Stage-1.5 state that is still in the timed gate has exactly the
Stage-2 CR-drain shell facts: fixed card, no `RoleMCR`, and every `RoleCR`
remains at phase 0. -/
theorem stage15Gate_terminal_stage2ShellFacts {n a₀ : ℕ}
    {c : Config (AgentState L K)}
    (hc : c ∈ stage15Gate (L := L) (K := K) n a₀)
    (hmcr0 : RoleSplitConcentration.roleMCRCount (L := L) (K := K) c = 0) :
    Multiset.card c = n ∧
      RoleSplitConcentration.roleMCRCount (L := L) (K := K) c = 0 ∧
      ∀ a ∈ c, a.role = .cr → a.phase.val = 0 := by
  refine ⟨stage15Gate_card (L := L) (K := K) hc, hmcr0, ?_⟩
  intro a ha _
  have hphase := stage15Gate_allPhase0 (L := L) (K := K) hc a ha
  simpa using congrArg Fin.val hphase

/-- Deterministic Stage-1 → Stage-1.5 entry bridge, with the timed side
conditions exposed: if the floor gate and the phase-0 window still hold at a
Stage-1 endpoint, then `roleSplitGoodMile` supplies the `roleMCRCount ≤ 1`
conjunct of `stage15Gate`. -/
theorem stage15Gate_of_roleSplitGoodMile {n a₀ : ℕ} (hn2 : 2 ≤ n)
    {c : Config (AgentState L K)}
    (hfloor : c ∈ RoleSplitConcentration.floorGate (L := L) (K := K) n a₀)
    (hall : Phase0Window.allPhase0 (L := L) (K := K) c)
    (hgood : RoleSplitConcentration.roleSplitGoodMile (L := L) (K := K) n hn2 c) :
    c ∈ stage15Gate (L := L) (K := K) n a₀ := by
  refine ⟨hfloor, hall, ?_⟩
  exact RoleSplitConcentration.roleMCRCount_le_one_of_roleSplitGoodMile
    (L := L) (K := K) hn2
    (RoleSplitConcentration.floorGate_card (L := L) (K := K) hfloor)
    (RoleSplitConcentration.floorGate_phase0 (L := L) (K := K) hfloor)
    hgood

/-! ### Stage-1.5 clock/no-advance bridge

`stage15Gate` is the killed milestone gate.  The one-step leak hypothesis of
`real_bad_le_janson_add_escape` is sharper if its side set `S` also requires
`noClockAtZero`: on `stage15Gate ∧ noClockAtZero`, the phase-0 window is preserved
for one step, and `roleMCRCount ≤ 1` is support-preserved.  Thus the only one-step
escape still needing a quantitative `q` is the genuine floor escape.  The
probability of falling out of this side set along the real trajectory is then paid
by the clock-counter survival prefix below. -/

/-- Side set for Stage 1.5: the timed gate plus the per-step no-advance guard. -/
def stage15NoAdvanceSet (n a₀ : ℕ) : Set (Config (AgentState L K)) :=
  {c | c ∈ stage15Gate (L := L) (K := K) n a₀ ∧
    Phase0Window.noClockAtZero (L := L) (K := K) c}

theorem stage15NoAdvanceSet_stage15Gate {n a₀ : ℕ} {c : Config (AgentState L K)}
    (hc : c ∈ stage15NoAdvanceSet (L := L) (K := K) n a₀) :
    c ∈ stage15Gate (L := L) (K := K) n a₀ := hc.1

theorem stage15NoAdvanceSet_noClockAtZero {n a₀ : ℕ} {c : Config (AgentState L K)}
    (hc : c ∈ stage15NoAdvanceSet (L := L) (K := K) n a₀) :
    Phase0Window.noClockAtZero (L := L) (K := K) c := hc.2

/-- `¬ noClockAtZero` is the same clock-counter failure as `¬ ClockPos`, in the
subset direction needed to consume the landed clock-tail depletion adapters. -/
theorem noClockAtZero_compl_subset_clockPos_compl :
    {c : Config (AgentState L K) |
        ¬ Phase0Window.noClockAtZero (L := L) (K := K) c}
      ⊆
    {c : Config (AgentState L K) |
        ¬ Phase6LeakZero.ClockPos (L := L) (K := K) c} := by
  intro c hbad hpos
  unfold Phase0Window.noClockAtZero at hbad
  push Not at hbad
  obtain ⟨a, ha, hrole, hzero⟩ := hbad
  have hpositive := hpos a ha hrole
  omega

theorem noClockAtZero_fail_mass_le_clockPos_fail_mass
    (H : ℕ) (c₀ : Config (AgentState L K)) :
    ((NonuniformMajority L K).transitionKernel ^ H) c₀
        {c : Config (AgentState L K) |
          ¬ Phase0Window.noClockAtZero (L := L) (K := K) c}
      ≤
    ((NonuniformMajority L K).transitionKernel ^ H) c₀
        {c : Config (AgentState L K) |
          ¬ Phase6LeakZero.ClockPos (L := L) (K := K) c} :=
  measure_mono (noClockAtZero_compl_subset_clockPos_compl (L := L) (K := K))

/-- The potential-threshold form of the same guard breach, re-exported here so
the Stage-1.5 timing bridge visibly uses the phase-0 clock-threshold atom. -/
theorem noClockAtZero_compl_subset_clockCounterPotential_ge_one (s : ℝ) :
    {c : Config (AgentState L K) |
        ¬ Phase0Window.noClockAtZero (L := L) (K := K) c}
      ⊆
    {c : Config (AgentState L K) |
        (1 : ℝ≥0∞) ≤ Phase0Window.clockCounterPotential (L := L) (K := K) s c} := by
  intro c hc
  exact Phase0Window.clockCounterPotential_ge_one_of_not_noClockAtZero
    (L := L) (K := K) s c hc

/-- Phase-0 one-horizon clock-zero bound from the unrestricted clock survival
adapter (`Nphase = 0`).  This is the phase-0 form of the counter-depletion route:
`survival_union_bound` + per-clock MGF depletion tails + the caller's deterministic
`WinN 0 n` breach cover. -/
theorem phase0_noClockAtZero_fail_mass_le_clock_survival
    {ι : Type*}
    (n H R N0 m : ℕ)
    (c₀ : Config (AgentState L K))
    (Clocks : Finset ι) (species : ι → AgentState L K)
    (s : ℝ) (hs : 0 < s)
    (p_tail : ℝ≥0∞)
    (hcover :
      {c : Config (AgentState L K) |
          ¬ CounterSurvivalConc.WinN (L := L) (K := K) 0 n c}
        ⊆ ⋃ j ∈ Clocks,
          {c : Config (AgentState L K) |
            Phase6ClockTailDepletion.DepletedCount
              (L := L) (K := K) (species j) N0 R c})
    (hcard :
      ∀ c : Config (AgentState L K), 2 ≤ c.card → c.card = n)
    (hsmall :
      ∀ j, j ∈ Clocks →
        ∀ c : Config (AgentState L K), ¬ (2 ≤ c.card) →
          ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
            {c' : Config (AgentState L K) |
              c'.count (species j) < c.count (species j)} = 0)
    (hcap :
      ∀ j, j ∈ Clocks →
        ∀ c : Config (AgentState L K), c.count (species j) ≤ m)
    (htail :
      ∀ j, j ∈ Clocks →
        Phase6ClockTailDepletion.mgfDepletionTailBound
          (L := L) (K := K)
          (species j) s N0 R n m H c₀ ≤ p_tail) :
    ((NonuniformMajority L K).transitionKernel ^ H) c₀
        {c : Config (AgentState L K) |
          ¬ Phase0Window.noClockAtZero (L := L) (K := K) c}
      ≤ (Clocks.card : ℕ) • p_tail := by
  exact
    (noClockAtZero_fail_mass_le_clockPos_fail_mass
      (L := L) (K := K) H c₀).trans
      (Phase15ClockTailDepletion.clockPos_fail_mass_le_mgf_clock_union_unrestricted
        (L := L) (K := K)
        0 n H R N0 m
        c₀ Clocks species s hs p_tail
        hcover hcard hsmall hcap htail)

/-- Phase-0 prefix clock-zero bound over the drain horizon, using the existing
unrestricted `WinN`/MGF clock-depletion machinery at `Nphase = 0`. -/
theorem phase0_noClockAtZero_prefix_sum_range_le_clock_survival
    {ι : Type*}
    (n T R N0 m : ℕ)
    (c₀ : Config (AgentState L K))
    (Clocks : Finset ι) (species : ι → AgentState L K)
    (s : ℝ) (hs : 0 < s)
    (p_tail : ℝ≥0∞)
    (hcover :
      {c : Config (AgentState L K) |
          ¬ CounterSurvivalConc.WinN (L := L) (K := K) 0 n c}
        ⊆ ⋃ j ∈ Clocks,
          {c : Config (AgentState L K) |
            Phase6ClockTailDepletion.DepletedCount
              (L := L) (K := K) (species j) N0 R c})
    (hcard :
      ∀ c : Config (AgentState L K), 2 ≤ c.card → c.card = n)
    (hsmall :
      ∀ j, j ∈ Clocks →
        ∀ c : Config (AgentState L K), ¬ (2 ≤ c.card) →
          ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
            {c' : Config (AgentState L K) |
              c'.count (species j) < c.count (species j)} = 0)
    (hcap :
      ∀ j, j ∈ Clocks →
        ∀ c : Config (AgentState L K), c.count (species j) ≤ m)
    (htail :
      ∀ H, H ∈ Finset.range T →
        ∀ j, j ∈ Clocks →
          Phase6ClockTailDepletion.mgfDepletionTailBound
            (L := L) (K := K)
            (species j) s N0 R n m H c₀ ≤ p_tail) :
    (∑ H ∈ Finset.range T,
        ((NonuniformMajority L K).transitionKernel ^ H) c₀
          {c : Config (AgentState L K) |
            ¬ Phase0Window.noClockAtZero (L := L) (K := K) c})
      ≤ T • ((Clocks.card : ℕ) • p_tail) := by
  classical
  calc
    (∑ H ∈ Finset.range T,
        ((NonuniformMajority L K).transitionKernel ^ H) c₀
          {c : Config (AgentState L K) |
            ¬ Phase0Window.noClockAtZero (L := L) (K := K) c})
        ≤ ∑ H ∈ Finset.range T, ((Clocks.card : ℕ) • p_tail) := by
          apply Finset.sum_le_sum
          intro H hH
          exact
            phase0_noClockAtZero_fail_mass_le_clock_survival
              (L := L) (K := K)
              n H R N0 m
              c₀ Clocks species s hs p_tail
              hcover hcard hsmall hcap
              (fun j hj => htail H hH j hj)
    _ = T • ((Clocks.card : ℕ) • p_tail) := by
          rw [Finset.sum_const, Finset.card_range]

/-- The named no-advance endpoint bridge: starting in `allPhase0`, the chance of
having left phase 0 by horizon `T` is bounded by the phase-0 clock-depletion
survival prefix.  The `allPhase0` chaining is exactly
`transitionKernel_not_allPhase0_eq_zero_of_noClockAtZero` packaged in
`allPhase0_window_le_prefix_sum`. -/
theorem phase0_allPhase0_noadvance_le_clock_survival
    {ι : Type*}
    (n T R N0 m : ℕ)
    (c₀ : Config (AgentState L K))
    (h0 : Phase0Window.allPhase0 (L := L) (K := K) c₀)
    (Clocks : Finset ι) (species : ι → AgentState L K)
    (s : ℝ) (hs : 0 < s)
    (p_tail : ℝ≥0∞)
    (hcover :
      {c : Config (AgentState L K) |
          ¬ CounterSurvivalConc.WinN (L := L) (K := K) 0 n c}
        ⊆ ⋃ j ∈ Clocks,
          {c : Config (AgentState L K) |
            Phase6ClockTailDepletion.DepletedCount
              (L := L) (K := K) (species j) N0 R c})
    (hcard :
      ∀ c : Config (AgentState L K), 2 ≤ c.card → c.card = n)
    (hsmall :
      ∀ j, j ∈ Clocks →
        ∀ c : Config (AgentState L K), ¬ (2 ≤ c.card) →
          ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
            {c' : Config (AgentState L K) |
              c'.count (species j) < c.count (species j)} = 0)
    (hcap :
      ∀ j, j ∈ Clocks →
        ∀ c : Config (AgentState L K), c.count (species j) ≤ m)
    (htail :
      ∀ H, H ∈ Finset.range T →
        ∀ j, j ∈ Clocks →
          Phase6ClockTailDepletion.mgfDepletionTailBound
            (L := L) (K := K)
            (species j) s N0 R n m H c₀ ≤ p_tail) :
    ((NonuniformMajority L K).transitionKernel ^ T) c₀
        {c : Config (AgentState L K) |
          ¬ Phase0Window.allPhase0 (L := L) (K := K) c}
      ≤ T • ((Clocks.card : ℕ) • p_tail) :=
  (Phase0Window.allPhase0_window_le_prefix_sum
    (L := L) (K := K) T c₀ h0).trans
    (phase0_noClockAtZero_prefix_sum_range_le_clock_survival
      (L := L) (K := K)
      n T R N0 m c₀ Clocks species s hs p_tail
      hcover hcard hsmall hcap htail)

/-- Prefix version of the all-phase-0 chaining.  A bad all-phase-0 prefix is paid
by a triangular clock-zero prefix. -/
theorem allPhase0_prefix_sum_le_noClockAtZero_prefix_sum
    (T : ℕ) (c₀ : Config (AgentState L K))
    (h0 : Phase0Window.allPhase0 (L := L) (K := K) c₀) :
    (∑ τ ∈ Finset.range T,
        ((NonuniformMajority L K).transitionKernel ^ τ) c₀
          {c : Config (AgentState L K) |
            ¬ Phase0Window.allPhase0 (L := L) (K := K) c})
      ≤ T •
        (∑ σ ∈ Finset.range T,
          ((NonuniformMajority L K).transitionKernel ^ σ) c₀
            {c : Config (AgentState L K) |
              ¬ Phase0Window.noClockAtZero (L := L) (K := K) c}) := by
  classical
  calc
    (∑ τ ∈ Finset.range T,
        ((NonuniformMajority L K).transitionKernel ^ τ) c₀
          {c : Config (AgentState L K) |
            ¬ Phase0Window.allPhase0 (L := L) (K := K) c})
        ≤ ∑ τ ∈ Finset.range T,
            (∑ σ ∈ Finset.range T,
              ((NonuniformMajority L K).transitionKernel ^ σ) c₀
                {c : Config (AgentState L K) |
                  ¬ Phase0Window.noClockAtZero (L := L) (K := K) c}) := by
          apply Finset.sum_le_sum
          intro τ hτ
          refine (Phase0Window.allPhase0_window_le_prefix_sum
            (L := L) (K := K) τ c₀ h0).trans ?_
          exact Finset.sum_le_sum_of_subset
            (Finset.range_mono (Nat.le_of_lt (Finset.mem_range.mp hτ)))
    _ = T •
        (∑ σ ∈ Finset.range T,
          ((NonuniformMajority L K).transitionKernel ^ σ) c₀
            {c : Config (AgentState L K) |
              ¬ Phase0Window.noClockAtZero (L := L) (K := K) c}) := by
          rw [Finset.sum_const, Finset.card_range]

/-- Prefix no-advance bound in the shape consumed by Stage-1.5 side-set escape:
the all-phase-0 bad prefix is bounded by the clock-survival prefix, with the
expected triangular factor from the first-exit union. -/
theorem phase0_allPhase0_prefix_sum_le_clock_survival
    {ι : Type*}
    (n T R N0 m : ℕ)
    (c₀ : Config (AgentState L K))
    (h0 : Phase0Window.allPhase0 (L := L) (K := K) c₀)
    (Clocks : Finset ι) (species : ι → AgentState L K)
    (s : ℝ) (hs : 0 < s)
    (p_tail : ℝ≥0∞)
    (hcover :
      {c : Config (AgentState L K) |
          ¬ CounterSurvivalConc.WinN (L := L) (K := K) 0 n c}
        ⊆ ⋃ j ∈ Clocks,
          {c : Config (AgentState L K) |
            Phase6ClockTailDepletion.DepletedCount
              (L := L) (K := K) (species j) N0 R c})
    (hcard :
      ∀ c : Config (AgentState L K), 2 ≤ c.card → c.card = n)
    (hsmall :
      ∀ j, j ∈ Clocks →
        ∀ c : Config (AgentState L K), ¬ (2 ≤ c.card) →
          ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
            {c' : Config (AgentState L K) |
              c'.count (species j) < c.count (species j)} = 0)
    (hcap :
      ∀ j, j ∈ Clocks →
        ∀ c : Config (AgentState L K), c.count (species j) ≤ m)
    (htail :
      ∀ H, H ∈ Finset.range T →
        ∀ j, j ∈ Clocks →
          Phase6ClockTailDepletion.mgfDepletionTailBound
            (L := L) (K := K)
            (species j) s N0 R n m H c₀ ≤ p_tail) :
    (∑ τ ∈ Finset.range T,
        ((NonuniformMajority L K).transitionKernel ^ τ) c₀
          {c : Config (AgentState L K) |
            ¬ Phase0Window.allPhase0 (L := L) (K := K) c})
      ≤ T • (T • ((Clocks.card : ℕ) • p_tail)) :=
  (allPhase0_prefix_sum_le_noClockAtZero_prefix_sum
    (L := L) (K := K) T c₀ h0).trans
    (nsmul_le_nsmul_right
      (phase0_noClockAtZero_prefix_sum_range_le_clock_survival
        (L := L) (K := K)
        n T R N0 m c₀ Clocks species s hs p_tail
        hcover hcard hsmall hcap htail) T)

theorem roleMCRCount_le_one_support_preserved
    (c c' : Config (AgentState L K))
    (hle : RoleSplitConcentration.roleMCRCount (L := L) (K := K) c ≤ 1)
    (hsupp : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    RoleSplitConcentration.roleMCRCount (L := L) (K := K) c' ≤ 1 := by
  have hstep := mcrCount_step_le (L := L) (K := K) c c' hsupp
  rw [RoleSplitConcentration.roleMCRCount_eq_mcrCount (L := L) (K := K) c] at hle
  rw [RoleSplitConcentration.roleMCRCount_eq_mcrCount (L := L) (K := K) c']
  exact hstep.trans hle

theorem roleMCRCount_le_one_pow_compl_eq_zero
    (c₀ : Config (AgentState L K))
    (hle : RoleSplitConcentration.roleMCRCount (L := L) (K := K) c₀ ≤ 1)
    (t : ℕ) :
    ((NonuniformMajority L K).transitionKernel ^ t) c₀
        {c : Config (AgentState L K) |
          ¬ RoleSplitConcentration.roleMCRCount (L := L) (K := K) c ≤ 1} = 0 :=
  Protocol.transitionKernel_pow_not_pred_eq_zero_of_stepDistOrSelf_support_preserved
    (NonuniformMajority L K)
    (fun c : Config (AgentState L K) =>
      RoleSplitConcentration.roleMCRCount (L := L) (K := K) c ≤ 1)
    (fun c c' hQ hsupp =>
      roleMCRCount_le_one_support_preserved (L := L) (K := K) c c' hQ hsupp)
    c₀ hle t

theorem stage15Gate_compl_subset_floor_allPhase0_mcrLeOne {n a₀ : ℕ} :
    (stage15Gate (L := L) (K := K) n a₀)ᶜ
      ⊆
    (RoleSplitConcentration.floorGate (L := L) (K := K) n a₀)ᶜ ∪
      ({c : Config (AgentState L K) |
        ¬ Phase0Window.allPhase0 (L := L) (K := K) c} ∪
      {c : Config (AgentState L K) |
        ¬ RoleSplitConcentration.roleMCRCount (L := L) (K := K) c ≤ 1}) := by
  intro c hc
  by_cases hfloor : c ∈ RoleSplitConcentration.floorGate (L := L) (K := K) n a₀
  · by_cases hall : Phase0Window.allPhase0 (L := L) (K := K) c
    · right
      right
      intro hmcr
      exact hc ⟨hfloor, hall, hmcr⟩
    · right
      left
      exact hall
  · left
    exact hfloor

theorem stage15NoAdvanceSet_compl_subset
    {n a₀ : ℕ} :
    (stage15NoAdvanceSet (L := L) (K := K) n a₀)ᶜ
      ⊆
    (RoleSplitConcentration.floorGate (L := L) (K := K) n a₀)ᶜ ∪
      ({c : Config (AgentState L K) |
        ¬ Phase0Window.allPhase0 (L := L) (K := K) c} ∪
      ({c : Config (AgentState L K) |
        ¬ RoleSplitConcentration.roleMCRCount (L := L) (K := K) c ≤ 1} ∪
      {c : Config (AgentState L K) |
        ¬ Phase0Window.noClockAtZero (L := L) (K := K) c})) := by
  intro c hc
  by_cases hfloor : c ∈ RoleSplitConcentration.floorGate (L := L) (K := K) n a₀
  · by_cases hall : Phase0Window.allPhase0 (L := L) (K := K) c
    · by_cases hmcr :
        RoleSplitConcentration.roleMCRCount (L := L) (K := K) c ≤ 1
      · right
        right
        right
        intro hno
        exact hc ⟨⟨hfloor, hall, hmcr⟩, hno⟩
      · right
        right
        left
        exact hmcr
    · right
      left
      exact hall
  · left
    exact hfloor

/-- From a Stage-1.5 gate state whose clocks are still away from zero, one-step
escape from `stage15Gate` is no larger than the floor-gate escape.  The
`allPhase0` component has zero one-step leak by the phase-0 window bridge, and
`roleMCRCount ≤ 1` is support-preserved. -/
theorem stage15Gate_escape_le_floor_of_noClockAtZero {n a₀ : ℕ}
    (x : Config (AgentState L K))
    (hx : x ∈ stage15Gate (L := L) (K := K) n a₀)
    (hno : Phase0Window.noClockAtZero (L := L) (K := K) x) :
    (NonuniformMajority L K).transitionKernel x
        (stage15Gate (L := L) (K := K) n a₀)ᶜ
      ≤
    (NonuniformMajority L K).transitionKernel x
        (RoleSplitConcentration.floorGate (L := L) (K := K) n a₀)ᶜ := by
  classical
  have hall0 :
      (NonuniformMajority L K).transitionKernel x
        {c : Config (AgentState L K) |
          ¬ Phase0Window.allPhase0 (L := L) (K := K) c} = 0 :=
    Phase0Window.transitionKernel_not_allPhase0_eq_zero_of_noClockAtZero
      (L := L) (K := K) x
      (stage15Gate_allPhase0 (L := L) (K := K) hx) hno
  have hmcr0 :
      (NonuniformMajority L K).transitionKernel x
        {c : Config (AgentState L K) |
          ¬ RoleSplitConcentration.roleMCRCount (L := L) (K := K) c ≤ 1} = 0 := by
    have hpow := roleMCRCount_le_one_pow_compl_eq_zero
      (L := L) (K := K) x
      (stage15Gate_roleMCR_le_one (L := L) (K := K) hx) 1
    simpa [pow_one] using hpow
  calc
    (NonuniformMajority L K).transitionKernel x
        (stage15Gate (L := L) (K := K) n a₀)ᶜ
      ≤ (NonuniformMajority L K).transitionKernel x
          ((RoleSplitConcentration.floorGate (L := L) (K := K) n a₀)ᶜ ∪
            ({c : Config (AgentState L K) |
              ¬ Phase0Window.allPhase0 (L := L) (K := K) c} ∪
            {c : Config (AgentState L K) |
              ¬ RoleSplitConcentration.roleMCRCount (L := L) (K := K) c ≤ 1})) :=
        measure_mono (stage15Gate_compl_subset_floor_allPhase0_mcrLeOne
          (L := L) (K := K) (n := n) (a₀ := a₀))
    _ ≤ (NonuniformMajority L K).transitionKernel x
          (RoleSplitConcentration.floorGate (L := L) (K := K) n a₀)ᶜ +
        (NonuniformMajority L K).transitionKernel x
          ({c : Config (AgentState L K) |
            ¬ Phase0Window.allPhase0 (L := L) (K := K) c} ∪
          {c : Config (AgentState L K) |
            ¬ RoleSplitConcentration.roleMCRCount (L := L) (K := K) c ≤ 1}) :=
        measure_union_le _ _
    _ ≤ (NonuniformMajority L K).transitionKernel x
          (RoleSplitConcentration.floorGate (L := L) (K := K) n a₀)ᶜ +
        ((NonuniformMajority L K).transitionKernel x
          {c : Config (AgentState L K) |
            ¬ Phase0Window.allPhase0 (L := L) (K := K) c} +
        (NonuniformMajority L K).transitionKernel x
          {c : Config (AgentState L K) |
            ¬ RoleSplitConcentration.roleMCRCount (L := L) (K := K) c ≤ 1}) := by
          gcongr
          exact measure_union_le _ _
    _ = (NonuniformMajority L K).transitionKernel x
          (RoleSplitConcentration.floorGate (L := L) (K := K) n a₀)ᶜ := by
          rw [hall0, hmcr0]
          simp

theorem stage15Gate_hstep_of_floor_noadvance {n a₀ : ℕ} {q : ℝ≥0∞}
    (hfloor :
      ∀ x ∈ RoleSplitConcentration.floorGate (L := L) (K := K) n a₀,
        x ∈ stage15NoAdvanceSet (L := L) (K := K) n a₀ →
          (NonuniformMajority L K).transitionKernel x
            (RoleSplitConcentration.floorGate (L := L) (K := K) n a₀)ᶜ ≤ q) :
    ∀ x ∈ stage15Gate (L := L) (K := K) n a₀,
      x ∈ stage15NoAdvanceSet (L := L) (K := K) n a₀ →
        (NonuniformMajority L K).transitionKernel x
          (stage15Gate (L := L) (K := K) n a₀)ᶜ ≤ q := by
  intro x hx hxS
  exact (stage15Gate_escape_le_floor_of_noClockAtZero
    (L := L) (K := K) x hx
    (stage15NoAdvanceSet_noClockAtZero (L := L) (K := K) hxS)).trans
    (hfloor x (stage15Gate_floorGate (L := L) (K := K) hx) hxS)

/-- Prefix escape from `stage15NoAdvanceSet` splits into the genuine floor-prefix
term plus the clock/no-advance prefix.  The `roleMCRCount≤1` conjunct contributes
zero mass along all powers from a Stage-1 endpoint. -/
theorem stage15NoAdvanceSet_escape_prefix_le_floor_allPhase0_noClock
    (n a₀ T : ℕ) (c₀ : Config (AgentState L K))
    (hmcr : RoleSplitConcentration.roleMCRCount (L := L) (K := K) c₀ ≤ 1) :
    (∑ τ ∈ Finset.range T,
        ((NonuniformMajority L K).transitionKernel ^ τ) c₀
          (stage15NoAdvanceSet (L := L) (K := K) n a₀)ᶜ)
      ≤
    (∑ τ ∈ Finset.range T,
        ((NonuniformMajority L K).transitionKernel ^ τ) c₀
          (RoleSplitConcentration.floorGate (L := L) (K := K) n a₀)ᶜ) +
      (∑ τ ∈ Finset.range T,
        ((NonuniformMajority L K).transitionKernel ^ τ) c₀
          {c : Config (AgentState L K) |
            ¬ Phase0Window.allPhase0 (L := L) (K := K) c}) +
      (∑ τ ∈ Finset.range T,
        ((NonuniformMajority L K).transitionKernel ^ τ) c₀
          {c : Config (AgentState L K) |
            ¬ Phase0Window.noClockAtZero (L := L) (K := K) c}) := by
  classical
  calc
    (∑ τ ∈ Finset.range T,
        ((NonuniformMajority L K).transitionKernel ^ τ) c₀
          (stage15NoAdvanceSet (L := L) (K := K) n a₀)ᶜ)
      ≤ ∑ τ ∈ Finset.range T,
          (((NonuniformMajority L K).transitionKernel ^ τ) c₀
            (RoleSplitConcentration.floorGate (L := L) (K := K) n a₀)ᶜ +
          (((NonuniformMajority L K).transitionKernel ^ τ) c₀
            {c : Config (AgentState L K) |
              ¬ Phase0Window.allPhase0 (L := L) (K := K) c} +
          ((NonuniformMajority L K).transitionKernel ^ τ) c₀
            {c : Config (AgentState L K) |
              ¬ Phase0Window.noClockAtZero (L := L) (K := K) c})) := by
        apply Finset.sum_le_sum
        intro τ _
        have hmcr0 := roleMCRCount_le_one_pow_compl_eq_zero
          (L := L) (K := K) c₀ hmcr τ
        calc
          ((NonuniformMajority L K).transitionKernel ^ τ) c₀
              (stage15NoAdvanceSet (L := L) (K := K) n a₀)ᶜ
            ≤ ((NonuniformMajority L K).transitionKernel ^ τ) c₀
                ((RoleSplitConcentration.floorGate (L := L) (K := K) n a₀)ᶜ ∪
                  ({c : Config (AgentState L K) |
                    ¬ Phase0Window.allPhase0 (L := L) (K := K) c} ∪
                  ({c : Config (AgentState L K) |
                    ¬ RoleSplitConcentration.roleMCRCount (L := L) (K := K) c ≤ 1} ∪
                  {c : Config (AgentState L K) |
                    ¬ Phase0Window.noClockAtZero (L := L) (K := K) c}))) :=
              measure_mono (stage15NoAdvanceSet_compl_subset
                (L := L) (K := K) (n := n) (a₀ := a₀))
          _ ≤ ((NonuniformMajority L K).transitionKernel ^ τ) c₀
                (RoleSplitConcentration.floorGate (L := L) (K := K) n a₀)ᶜ +
              ((NonuniformMajority L K).transitionKernel ^ τ) c₀
                ({c : Config (AgentState L K) |
                  ¬ Phase0Window.allPhase0 (L := L) (K := K) c} ∪
                ({c : Config (AgentState L K) |
                  ¬ RoleSplitConcentration.roleMCRCount (L := L) (K := K) c ≤ 1} ∪
                {c : Config (AgentState L K) |
                  ¬ Phase0Window.noClockAtZero (L := L) (K := K) c})) :=
              measure_union_le _ _
          _ ≤ ((NonuniformMajority L K).transitionKernel ^ τ) c₀
                (RoleSplitConcentration.floorGate (L := L) (K := K) n a₀)ᶜ +
              (((NonuniformMajority L K).transitionKernel ^ τ) c₀
                {c : Config (AgentState L K) |
                  ¬ Phase0Window.allPhase0 (L := L) (K := K) c} +
              (((NonuniformMajority L K).transitionKernel ^ τ) c₀
                {c : Config (AgentState L K) |
                  ¬ RoleSplitConcentration.roleMCRCount (L := L) (K := K) c ≤ 1} +
              ((NonuniformMajority L K).transitionKernel ^ τ) c₀
                {c : Config (AgentState L K) |
                  ¬ Phase0Window.noClockAtZero (L := L) (K := K) c})) := by
              have hMN :
                  ((NonuniformMajority L K).transitionKernel ^ τ) c₀
                    ({c : Config (AgentState L K) |
                      ¬ RoleSplitConcentration.roleMCRCount (L := L) (K := K) c ≤ 1} ∪
                    {c : Config (AgentState L K) |
                      ¬ Phase0Window.noClockAtZero (L := L) (K := K) c})
                    ≤
                  ((NonuniformMajority L K).transitionKernel ^ τ) c₀
                    {c : Config (AgentState L K) |
                      ¬ RoleSplitConcentration.roleMCRCount (L := L) (K := K) c ≤ 1} +
                  ((NonuniformMajority L K).transitionKernel ^ τ) c₀
                    {c : Config (AgentState L K) |
                      ¬ Phase0Window.noClockAtZero (L := L) (K := K) c} :=
                measure_union_le _ _
              have hAMN :
                  ((NonuniformMajority L K).transitionKernel ^ τ) c₀
                    ({c : Config (AgentState L K) |
                      ¬ Phase0Window.allPhase0 (L := L) (K := K) c} ∪
                    ({c : Config (AgentState L K) |
                      ¬ RoleSplitConcentration.roleMCRCount (L := L) (K := K) c ≤ 1} ∪
                    {c : Config (AgentState L K) |
                      ¬ Phase0Window.noClockAtZero (L := L) (K := K) c}))
                    ≤
                  ((NonuniformMajority L K).transitionKernel ^ τ) c₀
                    {c : Config (AgentState L K) |
                      ¬ Phase0Window.allPhase0 (L := L) (K := K) c} +
                  (((NonuniformMajority L K).transitionKernel ^ τ) c₀
                    {c : Config (AgentState L K) |
                      ¬ RoleSplitConcentration.roleMCRCount (L := L) (K := K) c ≤ 1} +
                  ((NonuniformMajority L K).transitionKernel ^ τ) c₀
                    {c : Config (AgentState L K) |
                      ¬ Phase0Window.noClockAtZero (L := L) (K := K) c}) := by
                calc
                  ((NonuniformMajority L K).transitionKernel ^ τ) c₀
                    ({c : Config (AgentState L K) |
                      ¬ Phase0Window.allPhase0 (L := L) (K := K) c} ∪
                    ({c : Config (AgentState L K) |
                      ¬ RoleSplitConcentration.roleMCRCount (L := L) (K := K) c ≤ 1} ∪
                    {c : Config (AgentState L K) |
                      ¬ Phase0Window.noClockAtZero (L := L) (K := K) c}))
                    ≤
                  ((NonuniformMajority L K).transitionKernel ^ τ) c₀
                    {c : Config (AgentState L K) |
                      ¬ Phase0Window.allPhase0 (L := L) (K := K) c} +
                  ((NonuniformMajority L K).transitionKernel ^ τ) c₀
                    ({c : Config (AgentState L K) |
                      ¬ RoleSplitConcentration.roleMCRCount (L := L) (K := K) c ≤ 1} ∪
                    {c : Config (AgentState L K) |
                      ¬ Phase0Window.noClockAtZero (L := L) (K := K) c}) :=
                    measure_union_le _ _
                  _ ≤
                  ((NonuniformMajority L K).transitionKernel ^ τ) c₀
                    {c : Config (AgentState L K) |
                      ¬ Phase0Window.allPhase0 (L := L) (K := K) c} +
                  (((NonuniformMajority L K).transitionKernel ^ τ) c₀
                    {c : Config (AgentState L K) |
                      ¬ RoleSplitConcentration.roleMCRCount (L := L) (K := K) c ≤ 1} +
                  ((NonuniformMajority L K).transitionKernel ^ τ) c₀
                    {c : Config (AgentState L K) |
                      ¬ Phase0Window.noClockAtZero (L := L) (K := K) c}) :=
                    add_le_add_right hMN _
              exact add_le_add_right hAMN _
          _ = ((NonuniformMajority L K).transitionKernel ^ τ) c₀
                (RoleSplitConcentration.floorGate (L := L) (K := K) n a₀)ᶜ +
              (((NonuniformMajority L K).transitionKernel ^ τ) c₀
                {c : Config (AgentState L K) |
                  ¬ Phase0Window.allPhase0 (L := L) (K := K) c} +
              (0 +
              ((NonuniformMajority L K).transitionKernel ^ τ) c₀
                {c : Config (AgentState L K) |
                  ¬ Phase0Window.noClockAtZero (L := L) (K := K) c})) := by
              rw [hmcr0]
          _ = ((NonuniformMajority L K).transitionKernel ^ τ) c₀
                (RoleSplitConcentration.floorGate (L := L) (K := K) n a₀)ᶜ +
              (((NonuniformMajority L K).transitionKernel ^ τ) c₀
                {c : Config (AgentState L K) |
                  ¬ Phase0Window.allPhase0 (L := L) (K := K) c} +
              ((NonuniformMajority L K).transitionKernel ^ τ) c₀
                {c : Config (AgentState L K) |
                  ¬ Phase0Window.noClockAtZero (L := L) (K := K) c}) := by
              simp
    _ =
        (∑ τ ∈ Finset.range T,
          ((NonuniformMajority L K).transitionKernel ^ τ) c₀
            (RoleSplitConcentration.floorGate (L := L) (K := K) n a₀)ᶜ) +
        (∑ τ ∈ Finset.range T,
          ((NonuniformMajority L K).transitionKernel ^ τ) c₀
            {c : Config (AgentState L K) |
              ¬ Phase0Window.allPhase0 (L := L) (K := K) c}) +
        (∑ τ ∈ Finset.range T,
          ((NonuniformMajority L K).transitionKernel ^ τ) c₀
            {c : Config (AgentState L K) |
              ¬ Phase0Window.noClockAtZero (L := L) (K := K) c}) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
        abel

theorem stage15NoAdvanceSet_escape_prefix_le_floor_clock_survival
    {ι : Type*}
    (n a₀ T R N0 m : ℕ)
    (c₀ : Config (AgentState L K))
    (h0 : Phase0Window.allPhase0 (L := L) (K := K) c₀)
    (hmcr : RoleSplitConcentration.roleMCRCount (L := L) (K := K) c₀ ≤ 1)
    (Clocks : Finset ι) (species : ι → AgentState L K)
    (s : ℝ) (hs : 0 < s)
    (p_tail ε_floor : ℝ≥0∞)
    (hfloor :
      (∑ τ ∈ Finset.range T,
        ((NonuniformMajority L K).transitionKernel ^ τ) c₀
          (RoleSplitConcentration.floorGate (L := L) (K := K) n a₀)ᶜ)
        ≤ ε_floor)
    (hcover :
      {c : Config (AgentState L K) |
          ¬ CounterSurvivalConc.WinN (L := L) (K := K) 0 n c}
        ⊆ ⋃ j ∈ Clocks,
          {c : Config (AgentState L K) |
            Phase6ClockTailDepletion.DepletedCount
              (L := L) (K := K) (species j) N0 R c})
    (hcard :
      ∀ c : Config (AgentState L K), 2 ≤ c.card → c.card = n)
    (hsmall :
      ∀ j, j ∈ Clocks →
        ∀ c : Config (AgentState L K), ¬ (2 ≤ c.card) →
          ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
            {c' : Config (AgentState L K) |
              c'.count (species j) < c.count (species j)} = 0)
    (hcap :
      ∀ j, j ∈ Clocks →
        ∀ c : Config (AgentState L K), c.count (species j) ≤ m)
    (htail :
      ∀ H, H ∈ Finset.range T →
        ∀ j, j ∈ Clocks →
          Phase6ClockTailDepletion.mgfDepletionTailBound
            (L := L) (K := K)
            (species j) s N0 R n m H c₀ ≤ p_tail) :
    (∑ τ ∈ Finset.range T,
        ((NonuniformMajority L K).transitionKernel ^ τ) c₀
          (stage15NoAdvanceSet (L := L) (K := K) n a₀)ᶜ)
      ≤ ε_floor +
        (T • (T • ((Clocks.card : ℕ) • p_tail)) +
          T • ((Clocks.card : ℕ) • p_tail)) := by
  have hsplit := stage15NoAdvanceSet_escape_prefix_le_floor_allPhase0_noClock
    (L := L) (K := K) n a₀ T c₀ hmcr
  have hall := phase0_allPhase0_prefix_sum_le_clock_survival
    (L := L) (K := K)
    n T R N0 m c₀ h0 Clocks species s hs p_tail
    hcover hcard hsmall hcap htail
  have hno := phase0_noClockAtZero_prefix_sum_range_le_clock_survival
    (L := L) (K := K)
    n T R N0 m c₀ Clocks species s hs p_tail
    hcover hcard hsmall hcap htail
  calc
    (∑ τ ∈ Finset.range T,
        ((NonuniformMajority L K).transitionKernel ^ τ) c₀
          (stage15NoAdvanceSet (L := L) (K := K) n a₀)ᶜ)
      ≤
        (∑ τ ∈ Finset.range T,
          ((NonuniformMajority L K).transitionKernel ^ τ) c₀
            (RoleSplitConcentration.floorGate (L := L) (K := K) n a₀)ᶜ) +
        (∑ τ ∈ Finset.range T,
          ((NonuniformMajority L K).transitionKernel ^ τ) c₀
            {c : Config (AgentState L K) |
              ¬ Phase0Window.allPhase0 (L := L) (K := K) c}) +
        (∑ τ ∈ Finset.range T,
          ((NonuniformMajority L K).transitionKernel ^ τ) c₀
            {c : Config (AgentState L K) |
              ¬ Phase0Window.noClockAtZero (L := L) (K := K) c}) := hsplit
    _ ≤ ε_floor +
        (T • (T • ((Clocks.card : ℕ) • p_tail)) +
          T • ((Clocks.card : ℕ) • p_tail)) := by
        calc
          (∑ τ ∈ Finset.range T,
            ((NonuniformMajority L K).transitionKernel ^ τ) c₀
              (RoleSplitConcentration.floorGate (L := L) (K := K) n a₀)ᶜ) +
            (∑ τ ∈ Finset.range T,
              ((NonuniformMajority L K).transitionKernel ^ τ) c₀
                {c : Config (AgentState L K) |
                  ¬ Phase0Window.allPhase0 (L := L) (K := K) c}) +
            (∑ τ ∈ Finset.range T,
              ((NonuniformMajority L K).transitionKernel ^ τ) c₀
                {c : Config (AgentState L K) |
                  ¬ Phase0Window.noClockAtZero (L := L) (K := K) c})
              ≤ ε_floor + T • (T • ((Clocks.card : ℕ) • p_tail)) +
                  T • ((Clocks.card : ℕ) • p_tail) :=
                add_le_add (add_le_add hfloor hall) hno
          _ = ε_floor +
              (T • (T • ((Clocks.card : ℕ) • p_tail)) +
                T • ((Clocks.card : ℕ) • p_tail)) := by
                ac_rfl

/-- Terminal Stage-1.5 milestone on the killed state space.  The cemetery is
terminal by convention; an alive state is terminal exactly when no `RoleMCR`
remains. -/
def stage15Terminal : Option (Config (AgentState L K)) → Prop
  | none => True
  | some c => RoleSplitConcentration.roleMCRCount (L := L) (K := K) c = 0

/-- At a gated nonterminal Stage-1.5 state, the real kernel has at least
`floorRate n a₀ 1` mass on terminal successors; off-gate successors are mapped
to the cemetery and also count as terminal in the killed chain. -/
theorem stage15Terminal_progress_mass {n a₀ : ℕ} (hn2 : 2 ≤ n)
    (c : Config (AgentState L K)) (hc : c ∈ stage15Gate (L := L) (K := K) n a₀)
    (h_not : ¬ stage15Terminal (L := L) (K := K) (some c)) :
    (GatedDrift.killK_now (NonuniformMajority L K).transitionKernel
        (stage15Gate (L := L) (K := K) n a₀) (some c))
        {o | stage15Terminal (L := L) (K := K) o} ≥
      ENNReal.ofReal (RoleSplitConcentration.floorRate n a₀ 1) := by
  classical
  have hrole_eq_one :
      RoleSplitConcentration.roleMCRCount (L := L) (K := K) c = 1 := by
    have hne : RoleSplitConcentration.roleMCRCount (L := L) (K := K) c ≠ 0 := by
      intro h0
      exact h_not h0
    have hle := stage15Gate_roleMCR_le_one (L := L) (K := K) hc
    omega
  have hmcr_eq_one : ExactMajority.mcrCount (L := L) (K := K) c = 1 := by
    rw [← RoleSplitConcentration.roleMCRCount_eq_mcrCount (L := L) (K := K) c]
    exact hrole_eq_one
  rw [GatedDrift.killK_now_some_gated
        (K := (NonuniformMajority L K).transitionKernel)
        (G := stage15Gate (L := L) (K := K) n a₀) c hc,
      Measure.map_apply (GatedDrift.gateMap_measurable _)
        (DiscreteMeasurableSpace.forall_measurableSet _)]
  have hbridge := RoleSplitConcentration.phase0_mcrCount_decrease_prob_floor
    (L := L) (K := K) c n a₀
    (stage15Gate_card (L := L) (K := K) hc) hn2
    (stage15Gate_phase0 (L := L) (K := K) hc)
    (stage15Gate_floor (L := L) (K := K) hc)
  have hrate : RoleSplitConcentration.floorRate n a₀ 1 =
      (((ExactMajority.mcrCount (L := L) (K := K) c * a₀ : ℕ) : ℝ) /
        ((n : ℝ) * ((n : ℝ) - 1))) := by
    unfold RoleSplitConcentration.floorRate
    rw [hmcr_eq_one]
  rw [hrate]
  have hsub : {c' : Config (AgentState L K) |
        ExactMajority.mcrCount (L := L) (K := K) c' <
          ExactMajority.mcrCount (L := L) (K := K) c} ⊆
      (GatedDrift.gateMap (stage15Gate (L := L) (K := K) n a₀)) ⁻¹'
        {o | stage15Terminal (L := L) (K := K) o} := by
    intro c' hc'
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    unfold GatedDrift.gateMap
    by_cases hc'G : c' ∈ stage15Gate (L := L) (K := K) n a₀
    · rw [if_pos hc'G]
      change RoleSplitConcentration.roleMCRCount (L := L) (K := K) c' = 0
      have hmcr0 : ExactMajority.mcrCount (L := L) (K := K) c' = 0 := by
        have hc'_lt : ExactMajority.mcrCount (L := L) (K := K) c' <
            ExactMajority.mcrCount (L := L) (K := K) c := hc'
        rw [hmcr_eq_one] at hc'_lt
        omega
      rw [RoleSplitConcentration.roleMCRCount_eq_mcrCount (L := L) (K := K) c']
      exact hmcr0
    · rw [if_neg hc'G]
      exact trivial
  calc ENNReal.ofReal
        (((ExactMajority.mcrCount (L := L) (K := K) c * a₀ : ℕ) : ℝ) /
          ((n : ℝ) * ((n : ℝ) - 1)))
      ≤ ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
          {c' | ExactMajority.mcrCount (L := L) (K := K) c' <
            ExactMajority.mcrCount (L := L) (K := K) c} := hbridge
    _ ≤ ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
          ((GatedDrift.gateMap (stage15Gate (L := L) (K := K) n a₀)) ⁻¹'
            {o | stage15Terminal (L := L) (K := K) o}) :=
        measure_mono hsub

/-- Terminal milestone monotonicity for the Stage-1.5 killed kernel.  Once the
alive source has no `RoleMCR`, real reachable successors have no `RoleMCR`;
cemetery successors are terminal by definition. -/
theorem stage15Terminal_monotone {n a₀ : ℕ}
    (o o' : Option (Config (AgentState L K)))
    (hmono : stage15Terminal (L := L) (K := K) o)
    (hsupp : 0 < GatedDrift.killK_now (NonuniformMajority L K).transitionKernel
      (stage15Gate (L := L) (K := K) n a₀) o {o'}) :
    stage15Terminal (L := L) (K := K) o' := by
  classical
  rcases o' with _ | c'
  · exact trivial
  · have hc'G : c' ∈ stage15Gate (L := L) (K := K) n a₀ :=
      GatedDrift.alive_support_gate
        (K := (NonuniformMajority L K).transitionKernel)
        (G := stage15Gate (L := L) (K := K) n a₀) o c' hsupp
    rcases o with _ | c
    · rw [GatedDrift.killK_now_none,
        Measure.dirac_apply' _ (DiscreteMeasurableSpace.forall_measurableSet _),
        Set.indicator_of_notMem (by simp :
          (none : Option (Config (AgentState L K))) ∉
            ({some c'} : Set (Option (Config (AgentState L K)))))] at hsupp
      exact absurd hsupp (lt_irrefl 0)
    · have hmcr0 : RoleSplitConcentration.roleMCRCount (L := L) (K := K) c = 0 := hmono
      by_cases hcG : c ∈ stage15Gate (L := L) (K := K) n a₀
      · rw [GatedDrift.killK_now_some_gated
              (K := (NonuniformMajority L K).transitionKernel)
              (G := stage15Gate (L := L) (K := K) n a₀) c hcG,
            Measure.map_apply (GatedDrift.gateMap_measurable _)
              (DiscreteMeasurableSpace.forall_measurableSet _)] at hsupp
        have hpre :
            (GatedDrift.gateMap (stage15Gate (L := L) (K := K) n a₀)) ⁻¹'
              {(some c' : Option (Config (AgentState L K)))} = {c'} := by
          ext y
          simp only [Set.mem_preimage, Set.mem_singleton_iff]
          unfold GatedDrift.gateMap
          by_cases hyG : y ∈ stage15Gate (L := L) (K := K) n a₀
          · rw [if_pos hyG]
            exact ⟨fun h => Option.some.inj h, fun h => by rw [h]⟩
          · rw [if_neg hyG]
            exact ⟨fun h => absurd h (by simp), fun h => absurd (h ▸ hc'G) hyG⟩
        rw [hpre] at hsupp
        have hsupp' : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support :=
          RoleSplitConcentration.mem_support_of_pos_toMeasure (L := L) (K := K) hsupp
        have hreach :=
          Protocol.stepDistOrSelf_support_reachable (NonuniformMajority L K) c c' hsupp'
        exact RoleSplitConcentration.roleMCRCount_zero_of_reachable
          (L := L) (K := K) hreach hmcr0
      · rw [GatedDrift.killK_now_ungated c hcG,
          Measure.dirac_apply' _ (DiscreteMeasurableSpace.forall_measurableSet _),
          Set.indicator_of_notMem (by simp :
            (none : Option (Config (AgentState L K))) ∉
              ({some c'} : Set (Option (Config (AgentState L K)))))] at hsupp
        exact absurd hsupp (lt_irrefl 0)

/-- Global progress for the one-milestone Stage-1.5 killed kernel. -/
theorem stage15Terminal_progress {n a₀ : ℕ} (hn2 : 2 ≤ n) (ha_le : a₀ ≤ n - 1)
    (i : Fin 1) (o : Option (Config (AgentState L K)))
    (_h_prev : ∀ j : Fin 1, j < i → stage15Terminal (L := L) (K := K) o)
    (h_not : ¬ stage15Terminal (L := L) (K := K) o) :
    GatedDrift.killK_now (NonuniformMajority L K).transitionKernel
        (stage15Gate (L := L) (K := K) n a₀) o
        {o' | stage15Terminal (L := L) (K := K) o'} ≥
      ENNReal.ofReal (RoleSplitConcentration.floorRate n a₀ 1) := by
  classical
  have hfloorRate_le_one : RoleSplitConcentration.floorRate n a₀ 1 ≤ 1 :=
    RoleSplitConcentration.floorRate_le_one (n := n) (a₀ := a₀) (M := 1) hn2 (by omega) ha_le
  rcases o with _ | c
  · exact absurd (trivial : stage15Terminal (L := L) (K := K)
      (none : Option (Config (AgentState L K)))) h_not
  · by_cases hcG : c ∈ stage15Gate (L := L) (K := K) n a₀
    · exact stage15Terminal_progress_mass (L := L) (K := K) hn2 c hcG h_not
    · rw [GatedDrift.killK_now_ungated c hcG, Measure.dirac_apply' _
        (DiscreteMeasurableSpace.forall_measurableSet _),
        Set.indicator_of_mem (show (none : Option (Config (AgentState L K))) ∈
          {o' | stage15Terminal (L := L) (K := K) o'} from trivial)]
      calc ENNReal.ofReal (RoleSplitConcentration.floorRate n a₀ 1) ≤ ENNReal.ofReal 1 :=
            ENNReal.ofReal_le_ofReal hfloorRate_le_one
        _ = 1 := ENNReal.ofReal_one

/-- The concrete Stage-1.5 terminal milestone witness.  It has one milestone:
`roleMCRCount = 0`, with success probability `floorRate n a₀ 1`. -/
noncomputable def stage15KernelMilestone (n a₀ : ℕ) (hn2 : 2 ≤ n)
    (ha1 : 1 ≤ a₀) (ha_le : a₀ ≤ n - 1) :
    RoleSplitConcentration.KernelMilestone
      (GatedDrift.killK_now (NonuniformMajority L K).transitionKernel
        (stage15Gate (L := L) (K := K) n a₀)) where
  k := 1
  milestone _ := stage15Terminal (L := L) (K := K)
  p _ := RoleSplitConcentration.floorRate n a₀ 1
  hp_pos _ := RoleSplitConcentration.floorRate_pos
    (n := n) (a₀ := a₀) (M := 1) hn2 (by omega) ha1
  hp_le_one _ := RoleSplitConcentration.floorRate_le_one
    (n := n) (a₀ := a₀) (M := 1) hn2 (by omega) ha_le
  milestone_monotone _ o o' hmono hsupp :=
    stage15Terminal_monotone (L := L) (K := K) (n := n) (a₀ := a₀) o o' hmono hsupp
  progress i o h_prev h_not :=
    stage15Terminal_progress (L := L) (K := K) hn2 ha_le i o h_prev h_not

/-- `Post` of the one-milestone witness is exactly `roleMCRCount = 0` on alive states. -/
theorem stage15KernelMilestone_post_sound (n a₀ : ℕ) (hn2 : 2 ≤ n)
    (ha1 : 1 ≤ a₀) (ha_le : a₀ ≤ n - 1) (y : Config (AgentState L K)) :
    (stage15KernelMilestone (L := L) (K := K) n a₀ hn2 ha1 ha_le).Post (some y) →
      RoleSplitConcentration.roleMCRCount (L := L) (K := K) y = 0 := by
  intro hPost
  exact hPost ⟨0, by simp [stage15KernelMilestone]⟩

/-- The nonterminal Stage-1.5 precondition for the one-milestone witness. -/
theorem stage15KernelMilestone_hPre_of_not_terminal (n a₀ : ℕ) (hn2 : 2 ≤ n)
    (ha1 : 1 ≤ a₀) (ha_le : a₀ ≤ n - 1) {c₀ : Config (AgentState L K)}
    (hnot : RoleSplitConcentration.roleMCRCount (L := L) (K := K) c₀ ≠ 0) :
    ∀ i : Fin (stage15KernelMilestone (L := L) (K := K) n a₀ hn2 ha1 ha_le).k,
      ¬ (stage15KernelMilestone (L := L) (K := K) n a₀ hn2 ha1 ha_le).milestone i (some c₀) := by
  intro i hi
  exact hnot hi

/-- The Stage-1.5 timed residual: terminal Janson tail plus the killed-gate escape
prefix.  The escape is the honest place for `E_noadvance` and floor-maintenance
budgets; no phase window is treated as an invariant here. -/
structure Stage15TimedResidual (n a₀ : ℕ) (hn2 : 2 ≤ n) (ha1 : 1 ≤ a₀)
    (ha_le : a₀ ≤ n - 1) (c₀ : Config (AgentState L K)) (ε : ℝ≥0) where
  lam : ℝ
  t : ℕ
  q : ℝ≥0∞
  hlam : 1 ≤ lam
  ht : lam *
      (stage15KernelMilestone (L := L) (K := K) n a₀ hn2 ha1 ha_le).meanTime ≤ (t : ℝ)
  hstep : ∀ x ∈ stage15Gate (L := L) (K := K) n a₀,
      x ∈ stage15Gate (L := L) (K := K) n a₀ →
      (NonuniformMajority L K).transitionKernel x
        (stage15Gate (L := L) (K := K) n a₀)ᶜ ≤ q
  hc₀ : c₀ ∈ stage15Gate (L := L) (K := K) n a₀
  hbudget :
    ENNReal.ofReal (Real.exp
        (-(stage15KernelMilestone (L := L) (K := K) n a₀ hn2 ha1 ha_le).pMin *
          (stage15KernelMilestone (L := L) (K := K) n a₀ hn2 ha1 ha_le).meanTime *
          (lam - 1 - Real.log lam))) +
      ((t : ℝ≥0∞) * q +
        ∑ τ ∈ Finset.range t,
          ((NonuniformMajority L K).transitionKernel ^ τ) c₀
            (stage15Gate (L := L) (K := K) n a₀)ᶜ)
      ≤ (ε : ℝ≥0∞)

/-- Refutation check: the Stage-1.5 residual is inhabited for a finite budget from
any start in the timed gate.  Quantitative `O(1/n²)` still requires the real
clock/floor tail input; this only rules out a vacuous premise. -/
theorem stage15TimedResidual_satisfiable
    (n a₀ : ℕ) (hn2 : 2 ≤ n) (ha1 : 1 ≤ a₀) (ha_le : a₀ ≤ n - 1)
    (c₀ : Config (AgentState L K))
    (hc₀ : c₀ ∈ stage15Gate (L := L) (K := K) n a₀) :
    ∃ ε : ℝ≥0,
      Nonempty (Stage15TimedResidual (L := L) (K := K) n a₀ hn2 ha1 ha_le c₀ ε) := by
  classical
  set mt := (stage15KernelMilestone (L := L) (K := K) n a₀ hn2 ha1 ha_le).meanTime with hmt
  set pm := (stage15KernelMilestone (L := L) (K := K) n a₀ hn2 ha1 ha_le).pMin with hpm
  set t₀ := ⌈mt⌉₊ with ht₀
  set R : ℝ≥0∞ :=
      ENNReal.ofReal (Real.exp (-pm * mt * ((1 : ℝ) - 1 - Real.log 1))) +
        ((t₀ : ℝ≥0∞) * 1 +
          ∑ τ ∈ Finset.range t₀,
            ((NonuniformMajority L K).transitionKernel ^ τ) c₀
              (stage15Gate (L := L) (K := K) n a₀)ᶜ) with hR
  have hR_lt_top : R < ⊤ := by
    rw [hR]
    refine ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top, ?_⟩
    refine ENNReal.add_lt_top.mpr ⟨?_, ?_⟩
    · exact ENNReal.mul_lt_top (by exact_mod_cast (ENNReal.natCast_lt_top t₀)) ENNReal.one_lt_top
    · refine (ENNReal.sum_lt_top).mpr ?_
      intro τ _
      exact lt_of_le_of_lt prob_le_one ENNReal.one_lt_top
  refine ⟨R.toNNReal, ⟨{
    lam := 1
    t := t₀
    q := 1
    hlam := le_refl 1
    ht := ?_
    hstep := ?_
    hc₀ := hc₀
    hbudget := ?_ }⟩⟩
  · rw [one_mul]
    simpa [ht₀] using Nat.le_ceil mt
  · intro x _ _
    exact prob_le_one
  · rw [ENNReal.coe_toNNReal hR_lt_top.ne]

/-- Stage-1.5 residual with the no-advance side set wired into the killed-kernel
escape engine.  The killed gate is still `stage15Gate`, but the one-step leak
hypothesis is only required on `stage15NoAdvanceSet`; there it reduces to the
floor-gate leak by `stage15Gate_hstep_of_floor_noadvance`.  The prefix term is
therefore exactly where the clock-survival/no-advance budget is consumed. -/
structure Stage15NoAdvanceResidual (n a₀ : ℕ) (hn2 : 2 ≤ n) (ha1 : 1 ≤ a₀)
    (ha_le : a₀ ≤ n - 1) (c₀ : Config (AgentState L K)) (ε : ℝ≥0) where
  lam : ℝ
  t : ℕ
  q : ℝ≥0∞
  hlam : 1 ≤ lam
  ht : lam *
      (stage15KernelMilestone (L := L) (K := K) n a₀ hn2 ha1 ha_le).meanTime ≤ (t : ℝ)
  hfloorStep :
    ∀ x ∈ RoleSplitConcentration.floorGate (L := L) (K := K) n a₀,
      x ∈ stage15NoAdvanceSet (L := L) (K := K) n a₀ →
        (NonuniformMajority L K).transitionKernel x
          (RoleSplitConcentration.floorGate (L := L) (K := K) n a₀)ᶜ ≤ q
  hc₀ : c₀ ∈ stage15Gate (L := L) (K := K) n a₀
  hbudget :
    ENNReal.ofReal (Real.exp
        (-(stage15KernelMilestone (L := L) (K := K) n a₀ hn2 ha1 ha_le).pMin *
          (stage15KernelMilestone (L := L) (K := K) n a₀ hn2 ha1 ha_le).meanTime *
          (lam - 1 - Real.log lam))) +
      ((t : ℝ≥0∞) * q +
        ∑ τ ∈ Finset.range t,
          ((NonuniformMajority L K).transitionKernel ^ τ) c₀
            (stage15NoAdvanceSet (L := L) (K := K) n a₀)ᶜ)
      ≤ (ε : ℝ≥0∞)

/-- Constructor for the no-advance Stage-1.5 residual from a maintained floor
prefix and the phase-0 unrestricted clock-survival bridge. -/
noncomputable def stage15NoAdvanceResidual_of_floor_clock_survival
    {ι : Type*}
    (n a₀ : ℕ) (hn2 : 2 ≤ n) (ha1 : 1 ≤ a₀) (ha_le : a₀ ≤ n - 1)
    (c₀ : Config (AgentState L K)) (ε : ℝ≥0)
    (lam : ℝ) (t : ℕ) (q : ℝ≥0∞)
    (hlam : 1 ≤ lam)
    (ht : lam *
      (stage15KernelMilestone (L := L) (K := K) n a₀ hn2 ha1 ha_le).meanTime ≤ (t : ℝ))
    (hfloorStep :
      ∀ x ∈ RoleSplitConcentration.floorGate (L := L) (K := K) n a₀,
        x ∈ stage15NoAdvanceSet (L := L) (K := K) n a₀ →
          (NonuniformMajority L K).transitionKernel x
            (RoleSplitConcentration.floorGate (L := L) (K := K) n a₀)ᶜ ≤ q)
    (hc₀ : c₀ ∈ stage15Gate (L := L) (K := K) n a₀)
    (R N0 m : ℕ)
    (Clocks : Finset ι) (species : ι → AgentState L K)
    (s : ℝ) (hs : 0 < s)
    (p_tail ε_floor : ℝ≥0∞)
    (hfloor :
      (∑ τ ∈ Finset.range t,
        ((NonuniformMajority L K).transitionKernel ^ τ) c₀
          (RoleSplitConcentration.floorGate (L := L) (K := K) n a₀)ᶜ)
        ≤ ε_floor)
    (hcover :
      {c : Config (AgentState L K) |
          ¬ CounterSurvivalConc.WinN (L := L) (K := K) 0 n c}
        ⊆ ⋃ j ∈ Clocks,
          {c : Config (AgentState L K) |
            Phase6ClockTailDepletion.DepletedCount
              (L := L) (K := K) (species j) N0 R c})
    (hcard :
      ∀ c : Config (AgentState L K), 2 ≤ c.card → c.card = n)
    (hsmall :
      ∀ j, j ∈ Clocks →
        ∀ c : Config (AgentState L K), ¬ (2 ≤ c.card) →
          ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
            {c' : Config (AgentState L K) |
              c'.count (species j) < c.count (species j)} = 0)
    (hcap :
      ∀ j, j ∈ Clocks →
        ∀ c : Config (AgentState L K), c.count (species j) ≤ m)
    (htail :
      ∀ H, H ∈ Finset.range t →
        ∀ j, j ∈ Clocks →
          Phase6ClockTailDepletion.mgfDepletionTailBound
            (L := L) (K := K)
            (species j) s N0 R n m H c₀ ≤ p_tail)
    (hbudget :
      ENNReal.ofReal (Real.exp
          (-(stage15KernelMilestone (L := L) (K := K) n a₀ hn2 ha1 ha_le).pMin *
            (stage15KernelMilestone (L := L) (K := K) n a₀ hn2 ha1 ha_le).meanTime *
            (lam - 1 - Real.log lam))) +
        ((t : ℝ≥0∞) * q +
          (ε_floor +
            (t • (t • ((Clocks.card : ℕ) • p_tail)) +
              t • ((Clocks.card : ℕ) • p_tail))))
        ≤ (ε : ℝ≥0∞)) :
    Stage15NoAdvanceResidual (L := L) (K := K) n a₀ hn2 ha1 ha_le c₀ ε := by
  refine {
    lam := lam
    t := t
    q := q
    hlam := hlam
    ht := ht
    hfloorStep := hfloorStep
    hc₀ := hc₀
    hbudget := ?_ }
  have hprefix := stage15NoAdvanceSet_escape_prefix_le_floor_clock_survival
    (L := L) (K := K)
    n a₀ t R N0 m c₀
    (stage15Gate_allPhase0 (L := L) (K := K) hc₀)
    (stage15Gate_roleMCR_le_one (L := L) (K := K) hc₀)
    Clocks species s hs p_tail ε_floor hfloor
    hcover hcard hsmall hcap htail
  calc
    ENNReal.ofReal (Real.exp
        (-(stage15KernelMilestone (L := L) (K := K) n a₀ hn2 ha1 ha_le).pMin *
          (stage15KernelMilestone (L := L) (K := K) n a₀ hn2 ha1 ha_le).meanTime *
          (lam - 1 - Real.log lam))) +
      ((t : ℝ≥0∞) * q +
        ∑ τ ∈ Finset.range t,
          ((NonuniformMajority L K).transitionKernel ^ τ) c₀
            (stage15NoAdvanceSet (L := L) (K := K) n a₀)ᶜ)
      ≤
    ENNReal.ofReal (Real.exp
        (-(stage15KernelMilestone (L := L) (K := K) n a₀ hn2 ha1 ha_le).pMin *
          (stage15KernelMilestone (L := L) (K := K) n a₀ hn2 ha1 ha_le).meanTime *
          (lam - 1 - Real.log lam))) +
      ((t : ℝ≥0∞) * q +
        (ε_floor +
          (t • (t • ((Clocks.card : ℕ) • p_tail)) +
            t • ((Clocks.card : ℕ) • p_tail)))) := by
        gcongr
    _ ≤ (ε : ℝ≥0∞) := hbudget

/-! ### Reachable replacement for the Stage-1.5 clock/no-advance bridge

The legacy constructor above is retained for audit history, but its `hcard` and
`hcap` inputs are global-universal facts and are refutation-checked false below.
The declarations in this section are the load-bearing replacement: the MGF tail
is instantiated through `ReachableClockTail.mgf_depletion_tail_reachable`, so the
cardinality and per-species count caps are required only on configurations
reachable from the current Stage-1.5 start.
-/

/-- Per-clock depletion input for `survival_union_bound`, with the `hcard`/`hcap`
caps scoped to the reachable-from-`c₀` domain. -/
theorem hdec_of_mgf_depletion_tail_reachable
    {ι : Type*}
    (Clocks : Finset ι) (species : ι → AgentState L K)
    (s : ℝ) (hs : 0 < s)
    (N0 R n m H : ℕ) (c₀ : Config (AgentState L K))
    (p_tail : ℝ≥0∞)
    (hcard_reach :
      ∀ c : Config (AgentState L K),
        (NonuniformMajority L K).Reachable c₀ c → 2 ≤ c.card → c.card = n)
    (hsmall :
      ∀ j, j ∈ Clocks →
        ∀ c : Config (AgentState L K), ¬ (2 ≤ c.card) →
          ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
            {c' : Config (AgentState L K) |
              c'.count (species j) < c.count (species j)} = 0)
    (hcap_reach :
      ∀ j, j ∈ Clocks →
        ∀ c : Config (AgentState L K),
          (NonuniformMajority L K).Reachable c₀ c → c.count (species j) ≤ m)
    (htail :
      ∀ j, j ∈ Clocks →
        Phase6ClockTailDepletion.mgfDepletionTailBound
          (L := L) (K := K)
          (species j) s N0 R n m H c₀ ≤ p_tail) :
    ∀ j ∈ Clocks,
      ((NonuniformMajority L K).transitionKernel ^ H) c₀
        {c : Config (AgentState L K) |
          Phase6ClockTailDepletion.DepletedCount
            (L := L) (K := K) (species j) N0 R c}
        ≤ p_tail := by
  intro j hj
  calc
    ((NonuniformMajority L K).transitionKernel ^ H) c₀
        {c : Config (AgentState L K) |
          Phase6ClockTailDepletion.DepletedCount
            (L := L) (K := K) (species j) N0 R c}
        ≤ Phase6ClockTailDepletion.mgfDepletionTailBound
            (L := L) (K := K) (species j) s N0 R n m H c₀ := by
          simpa [Phase6ClockTailDepletion.DepletedCount,
            Phase6ClockTailDepletion.mgfDepletionTailBound] using
            (ReachableClockTail.mgf_depletion_tail_reachable
              (P := NonuniformMajority L K)
              (sc := species j)
              (s := s) hs
              N0 R n m c₀
              hcard_reach
              (hsmall j hj)
              (hcap_reach j hj)
              H)
    _ ≤ p_tail := htail j hj

/-- Reachable-support version of `ClockCounterSurvival.survival_union_bound`.
The chain started at `c₀` gives zero mass to unreachable configs, so the
deterministic cover only has to hold on `Reachable c₀ c ∧ Bad c`. -/
theorem survival_union_bound_reachable
    {ι : Type*} (N n H : ℕ)
    (c₀ : Config (AgentState L K))
    (Clocks : Finset ι) (Depleted : ι → Config (AgentState L K) → Prop)
    (p_tail : ℝ≥0∞)
    (hcover :
      {c : Config (AgentState L K) |
          (NonuniformMajority L K).Reachable c₀ c ∧
            ¬ CounterSurvivalConc.WinN (L := L) (K := K) N n c}
        ⊆ ⋃ j ∈ Clocks, {c | Depleted j c})
    (hdec : ∀ j ∈ Clocks,
      ((NonuniformMajority L K).transitionKernel ^ H) c₀ {c | Depleted j c} ≤ p_tail) :
    ((NonuniformMajority L K).transitionKernel ^ H) c₀
        {c : Config (AgentState L K) |
          ¬ CounterSurvivalConc.WinN (L := L) (K := K) N n c}
      ≤ (Clocks.card : ℕ) • p_tail := by
  classical
  let μ := ((NonuniformMajority L K).transitionKernel ^ H) c₀
  let Bad : Set (Config (AgentState L K)) :=
    {c | ¬ CounterSurvivalConc.WinN (L := L) (K := K) N n c}
  let ReachBad : Set (Config (AgentState L K)) :=
    {c | (NonuniformMajority L K).Reachable c₀ c ∧
      ¬ CounterSurvivalConc.WinN (L := L) (K := K) N n c}
  let NotReach : Set (Config (AgentState L K)) :=
    {c | ¬ (NonuniformMajority L K).Reachable c₀ c}
  have hbad_sub : Bad ⊆ ReachBad ∪ NotReach := by
    intro c hc
    by_cases hreach : (NonuniformMajority L K).Reachable c₀ c
    · left
      exact ⟨hreach, hc⟩
    · right
      exact hreach
  have hnotReach0 : μ NotReach = 0 := by
    simpa [μ, NotReach] using
      (Protocol.transitionKernel_pow_not_reachable_eq_zero
        (NonuniformMajority L K) c₀ H)
  calc μ Bad
      ≤ μ (ReachBad ∪ NotReach) := measure_mono hbad_sub
    _ ≤ μ ReachBad + μ NotReach := measure_union_le _ _
    _ = μ ReachBad := by rw [hnotReach0]; simp
    _ ≤ μ (⋃ j ∈ Clocks, {c | Depleted j c}) := measure_mono hcover
    _ ≤ ∑ j ∈ Clocks, μ {c | Depleted j c} := measure_biUnion_finset_le _ _
    _ ≤ ∑ _j ∈ Clocks, p_tail := Finset.sum_le_sum hdec
    _ = (Clocks.card : ℕ) • p_tail := by
        rw [Finset.sum_const]

/-- If the original global `WinN` cover is available, the reachable-scoped cover
follows by forgetting the reachability conjunct.  This is the only valid
drop-in from the old interface; it does not manufacture the global cover. -/
theorem reachable_hcover_of_global_hcover
    {ι : Type*} (n N0 R : ℕ)
    (c₀ : Config (AgentState L K))
    (Clocks : Finset ι) (species : ι → AgentState L K)
    (hcover :
      {c : Config (AgentState L K) |
          ¬ CounterSurvivalConc.WinN (L := L) (K := K) 0 n c}
        ⊆ ⋃ j ∈ Clocks,
          {c : Config (AgentState L K) |
            Phase6ClockTailDepletion.DepletedCount
              (L := L) (K := K) (species j) N0 R c}) :
    {c : Config (AgentState L K) |
        (NonuniformMajority L K).Reachable c₀ c ∧
          ¬ CounterSurvivalConc.WinN (L := L) (K := K) 0 n c}
      ⊆ ⋃ j ∈ Clocks,
        {c : Config (AgentState L K) |
          Phase6ClockTailDepletion.DepletedCount
            (L := L) (K := K) (species j) N0 R c} := by
  intro c hc
  exact hcover hc.2

/-- Generic `WinN` failure bound from reachable-scoped per-clock depletion tails. -/
theorem winN_fail_mass_le_mgf_clock_union_reachable
    {ι : Type*}
    (Nphase n H R N0 m : ℕ)
    (c₀ : Config (AgentState L K))
    (Clocks : Finset ι) (species : ι → AgentState L K)
    (s : ℝ) (hs : 0 < s)
    (p_tail : ℝ≥0∞)
    (hcover :
      {c : Config (AgentState L K) |
          (NonuniformMajority L K).Reachable c₀ c ∧
            ¬ CounterSurvivalConc.WinN (L := L) (K := K) Nphase n c}
        ⊆ ⋃ j ∈ Clocks,
          {c : Config (AgentState L K) |
            Phase6ClockTailDepletion.DepletedCount
              (L := L) (K := K) (species j) N0 R c})
    (hcard_reach :
      ∀ c : Config (AgentState L K),
        (NonuniformMajority L K).Reachable c₀ c → 2 ≤ c.card → c.card = n)
    (hsmall :
      ∀ j, j ∈ Clocks →
        ∀ c : Config (AgentState L K), ¬ (2 ≤ c.card) →
          ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
            {c' : Config (AgentState L K) |
              c'.count (species j) < c.count (species j)} = 0)
    (hcap_reach :
      ∀ j, j ∈ Clocks →
        ∀ c : Config (AgentState L K),
          (NonuniformMajority L K).Reachable c₀ c → c.count (species j) ≤ m)
    (htail :
      ∀ j, j ∈ Clocks →
        Phase6ClockTailDepletion.mgfDepletionTailBound
          (L := L) (K := K)
          (species j) s N0 R n m H c₀ ≤ p_tail) :
    ((NonuniformMajority L K).transitionKernel ^ H) c₀
        {c : Config (AgentState L K) |
          ¬ CounterSurvivalConc.WinN (L := L) (K := K) Nphase n c}
      ≤ (Clocks.card : ℕ) • p_tail := by
  classical
  exact
    survival_union_bound_reachable
      (L := L) (K := K)
      Nphase n H c₀
      Clocks
      (fun j c =>
        Phase6ClockTailDepletion.DepletedCount
          (L := L) (K := K) (species j) N0 R c)
      p_tail
      hcover
      (hdec_of_mgf_depletion_tail_reachable
        (L := L) (K := K)
        Clocks species s hs N0 R n m H c₀ p_tail
        hcard_reach hsmall hcap_reach htail)

/-- Generic `ClockPos` failure bound from the reachable-scoped `WinN` adapter. -/
theorem clockPos_fail_mass_le_mgf_clock_union_reachable
    {ι : Type*}
    (Nphase n H R N0 m : ℕ)
    (c₀ : Config (AgentState L K))
    (Clocks : Finset ι) (species : ι → AgentState L K)
    (s : ℝ) (hs : 0 < s)
    (p_tail : ℝ≥0∞)
    (hcover :
      {c : Config (AgentState L K) |
          (NonuniformMajority L K).Reachable c₀ c ∧
            ¬ CounterSurvivalConc.WinN (L := L) (K := K) Nphase n c}
        ⊆ ⋃ j ∈ Clocks,
          {c : Config (AgentState L K) |
            Phase6ClockTailDepletion.DepletedCount
              (L := L) (K := K) (species j) N0 R c})
    (hcard_reach :
      ∀ c : Config (AgentState L K),
        (NonuniformMajority L K).Reachable c₀ c → 2 ≤ c.card → c.card = n)
    (hsmall :
      ∀ j, j ∈ Clocks →
        ∀ c : Config (AgentState L K), ¬ (2 ≤ c.card) →
          ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
            {c' : Config (AgentState L K) |
              c'.count (species j) < c.count (species j)} = 0)
    (hcap_reach :
      ∀ j, j ∈ Clocks →
        ∀ c : Config (AgentState L K),
          (NonuniformMajority L K).Reachable c₀ c → c.count (species j) ≤ m)
    (htail :
      ∀ j, j ∈ Clocks →
        Phase6ClockTailDepletion.mgfDepletionTailBound
          (L := L) (K := K)
          (species j) s N0 R n m H c₀ ≤ p_tail) :
    ((NonuniformMajority L K).transitionKernel ^ H) c₀
        {c : Config (AgentState L K) |
          ¬ Phase6LeakZero.ClockPos (L := L) (K := K) c}
      ≤ (Clocks.card : ℕ) • p_tail := by
  calc
    ((NonuniformMajority L K).transitionKernel ^ H) c₀
        {c : Config (AgentState L K) |
          ¬ Phase6LeakZero.ClockPos (L := L) (K := K) c}
        ≤
      ((NonuniformMajority L K).transitionKernel ^ H) c₀
        {c : Config (AgentState L K) |
          ¬ CounterSurvivalConc.WinN (L := L) (K := K) Nphase n c} :=
        Phase6ClockTailDepletion.clockPos_fail_mass_le_winN_fail_mass
          (L := L) (K := K) Nphase n H c₀
    _ ≤ (Clocks.card : ℕ) • p_tail :=
        winN_fail_mass_le_mgf_clock_union_reachable
          (L := L) (K := K)
          Nphase n H R N0 m
          c₀ Clocks species s hs p_tail
          hcover hcard_reach hsmall hcap_reach htail

/-- Phase-0 one-horizon clock-zero bound through the reachable clock-tail
interface, at `Nphase = 0`. -/
theorem phase0_noClockAtZero_fail_mass_le_clock_survival_reachable
    {ι : Type*}
    (n H R N0 m : ℕ)
    (c₀ : Config (AgentState L K))
    (Clocks : Finset ι) (species : ι → AgentState L K)
    (s : ℝ) (hs : 0 < s)
    (p_tail : ℝ≥0∞)
    (hcover :
      {c : Config (AgentState L K) |
          (NonuniformMajority L K).Reachable c₀ c ∧
            ¬ CounterSurvivalConc.WinN (L := L) (K := K) 0 n c}
        ⊆ ⋃ j ∈ Clocks,
          {c : Config (AgentState L K) |
            Phase6ClockTailDepletion.DepletedCount
              (L := L) (K := K) (species j) N0 R c})
    (hcard_reach :
      ∀ c : Config (AgentState L K),
        (NonuniformMajority L K).Reachable c₀ c → 2 ≤ c.card → c.card = n)
    (hsmall :
      ∀ j, j ∈ Clocks →
        ∀ c : Config (AgentState L K), ¬ (2 ≤ c.card) →
          ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
            {c' : Config (AgentState L K) |
              c'.count (species j) < c.count (species j)} = 0)
    (hcap_reach :
      ∀ j, j ∈ Clocks →
        ∀ c : Config (AgentState L K),
          (NonuniformMajority L K).Reachable c₀ c → c.count (species j) ≤ m)
    (htail :
      ∀ j, j ∈ Clocks →
        Phase6ClockTailDepletion.mgfDepletionTailBound
          (L := L) (K := K)
          (species j) s N0 R n m H c₀ ≤ p_tail) :
    ((NonuniformMajority L K).transitionKernel ^ H) c₀
        {c : Config (AgentState L K) |
          ¬ Phase0Window.noClockAtZero (L := L) (K := K) c}
      ≤ (Clocks.card : ℕ) • p_tail :=
  (noClockAtZero_fail_mass_le_clockPos_fail_mass
      (L := L) (K := K) H c₀).trans
    (clockPos_fail_mass_le_mgf_clock_union_reachable
      (L := L) (K := K)
      0 n H R N0 m
      c₀ Clocks species s hs p_tail
      hcover hcard_reach hsmall hcap_reach htail)

/-- Phase-0 prefix clock-zero bound over the drain horizon through the reachable
clock-tail interface. -/
theorem phase0_noClockAtZero_prefix_sum_range_le_clock_survival_reachable
    {ι : Type*}
    (n T R N0 m : ℕ)
    (c₀ : Config (AgentState L K))
    (Clocks : Finset ι) (species : ι → AgentState L K)
    (s : ℝ) (hs : 0 < s)
    (p_tail : ℝ≥0∞)
    (hcover :
      {c : Config (AgentState L K) |
          (NonuniformMajority L K).Reachable c₀ c ∧
            ¬ CounterSurvivalConc.WinN (L := L) (K := K) 0 n c}
        ⊆ ⋃ j ∈ Clocks,
          {c : Config (AgentState L K) |
            Phase6ClockTailDepletion.DepletedCount
              (L := L) (K := K) (species j) N0 R c})
    (hcard_reach :
      ∀ c : Config (AgentState L K),
        (NonuniformMajority L K).Reachable c₀ c → 2 ≤ c.card → c.card = n)
    (hsmall :
      ∀ j, j ∈ Clocks →
        ∀ c : Config (AgentState L K), ¬ (2 ≤ c.card) →
          ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
            {c' : Config (AgentState L K) |
              c'.count (species j) < c.count (species j)} = 0)
    (hcap_reach :
      ∀ j, j ∈ Clocks →
        ∀ c : Config (AgentState L K),
          (NonuniformMajority L K).Reachable c₀ c → c.count (species j) ≤ m)
    (htail :
      ∀ H, H ∈ Finset.range T →
        ∀ j, j ∈ Clocks →
          Phase6ClockTailDepletion.mgfDepletionTailBound
            (L := L) (K := K)
            (species j) s N0 R n m H c₀ ≤ p_tail) :
    (∑ H ∈ Finset.range T,
        ((NonuniformMajority L K).transitionKernel ^ H) c₀
          {c : Config (AgentState L K) |
            ¬ Phase0Window.noClockAtZero (L := L) (K := K) c})
      ≤ T • ((Clocks.card : ℕ) • p_tail) := by
  classical
  calc
    (∑ H ∈ Finset.range T,
        ((NonuniformMajority L K).transitionKernel ^ H) c₀
          {c : Config (AgentState L K) |
            ¬ Phase0Window.noClockAtZero (L := L) (K := K) c})
        ≤ ∑ H ∈ Finset.range T, ((Clocks.card : ℕ) • p_tail) := by
          apply Finset.sum_le_sum
          intro H hH
          exact
            phase0_noClockAtZero_fail_mass_le_clock_survival_reachable
              (L := L) (K := K)
              n H R N0 m
              c₀ Clocks species s hs p_tail
              hcover hcard_reach hsmall hcap_reach
              (fun j hj => htail H hH j hj)
    _ = T • ((Clocks.card : ℕ) • p_tail) := by
          rw [Finset.sum_const, Finset.card_range]

/-- Endpoint no-advance bridge using reachable-scoped clock depletion. -/
theorem phase0_allPhase0_noadvance_le_clock_survival_reachable
    {ι : Type*}
    (n T R N0 m : ℕ)
    (c₀ : Config (AgentState L K))
    (h0 : Phase0Window.allPhase0 (L := L) (K := K) c₀)
    (Clocks : Finset ι) (species : ι → AgentState L K)
    (s : ℝ) (hs : 0 < s)
    (p_tail : ℝ≥0∞)
    (hcover :
      {c : Config (AgentState L K) |
          (NonuniformMajority L K).Reachable c₀ c ∧
            ¬ CounterSurvivalConc.WinN (L := L) (K := K) 0 n c}
        ⊆ ⋃ j ∈ Clocks,
          {c : Config (AgentState L K) |
            Phase6ClockTailDepletion.DepletedCount
              (L := L) (K := K) (species j) N0 R c})
    (hcard_reach :
      ∀ c : Config (AgentState L K),
        (NonuniformMajority L K).Reachable c₀ c → 2 ≤ c.card → c.card = n)
    (hsmall :
      ∀ j, j ∈ Clocks →
        ∀ c : Config (AgentState L K), ¬ (2 ≤ c.card) →
          ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
            {c' : Config (AgentState L K) |
              c'.count (species j) < c.count (species j)} = 0)
    (hcap_reach :
      ∀ j, j ∈ Clocks →
        ∀ c : Config (AgentState L K),
          (NonuniformMajority L K).Reachable c₀ c → c.count (species j) ≤ m)
    (htail :
      ∀ H, H ∈ Finset.range T →
        ∀ j, j ∈ Clocks →
          Phase6ClockTailDepletion.mgfDepletionTailBound
            (L := L) (K := K)
            (species j) s N0 R n m H c₀ ≤ p_tail) :
    ((NonuniformMajority L K).transitionKernel ^ T) c₀
        {c : Config (AgentState L K) |
          ¬ Phase0Window.allPhase0 (L := L) (K := K) c}
      ≤ T • ((Clocks.card : ℕ) • p_tail) :=
  (Phase0Window.allPhase0_window_le_prefix_sum
    (L := L) (K := K) T c₀ h0).trans
    (phase0_noClockAtZero_prefix_sum_range_le_clock_survival_reachable
      (L := L) (K := K)
      n T R N0 m c₀ Clocks species s hs p_tail
      hcover hcard_reach hsmall hcap_reach htail)

/-- Prefix no-advance bound in the shape consumed by Stage-1.5 side-set escape,
with all clock-tail inputs reachable-scoped. -/
theorem phase0_allPhase0_prefix_sum_le_clock_survival_reachable
    {ι : Type*}
    (n T R N0 m : ℕ)
    (c₀ : Config (AgentState L K))
    (h0 : Phase0Window.allPhase0 (L := L) (K := K) c₀)
    (Clocks : Finset ι) (species : ι → AgentState L K)
    (s : ℝ) (hs : 0 < s)
    (p_tail : ℝ≥0∞)
    (hcover :
      {c : Config (AgentState L K) |
          (NonuniformMajority L K).Reachable c₀ c ∧
            ¬ CounterSurvivalConc.WinN (L := L) (K := K) 0 n c}
        ⊆ ⋃ j ∈ Clocks,
          {c : Config (AgentState L K) |
            Phase6ClockTailDepletion.DepletedCount
              (L := L) (K := K) (species j) N0 R c})
    (hcard_reach :
      ∀ c : Config (AgentState L K),
        (NonuniformMajority L K).Reachable c₀ c → 2 ≤ c.card → c.card = n)
    (hsmall :
      ∀ j, j ∈ Clocks →
        ∀ c : Config (AgentState L K), ¬ (2 ≤ c.card) →
          ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
            {c' : Config (AgentState L K) |
              c'.count (species j) < c.count (species j)} = 0)
    (hcap_reach :
      ∀ j, j ∈ Clocks →
        ∀ c : Config (AgentState L K),
          (NonuniformMajority L K).Reachable c₀ c → c.count (species j) ≤ m)
    (htail :
      ∀ H, H ∈ Finset.range T →
        ∀ j, j ∈ Clocks →
          Phase6ClockTailDepletion.mgfDepletionTailBound
            (L := L) (K := K)
            (species j) s N0 R n m H c₀ ≤ p_tail) :
    (∑ τ ∈ Finset.range T,
        ((NonuniformMajority L K).transitionKernel ^ τ) c₀
          {c : Config (AgentState L K) |
            ¬ Phase0Window.allPhase0 (L := L) (K := K) c})
      ≤ T • (T • ((Clocks.card : ℕ) • p_tail)) :=
  (allPhase0_prefix_sum_le_noClockAtZero_prefix_sum
    (L := L) (K := K) T c₀ h0).trans
    (nsmul_le_nsmul_right
      (phase0_noClockAtZero_prefix_sum_range_le_clock_survival_reachable
        (L := L) (K := K)
        n T R N0 m c₀ Clocks species s hs p_tail
        hcover hcard_reach hsmall hcap_reach htail) T)

/-- Stage-1.5 side-set escape prefix, using reachable-scoped no-advance inputs
instead of the false global clock-survival inputs. -/
theorem stage15NoAdvanceSet_escape_prefix_le_floor_clock_survival_reachable
    {ι : Type*}
    (n a₀ T R N0 m : ℕ)
    (c₀ : Config (AgentState L K))
    (h0 : Phase0Window.allPhase0 (L := L) (K := K) c₀)
    (hmcr : RoleSplitConcentration.roleMCRCount (L := L) (K := K) c₀ ≤ 1)
    (Clocks : Finset ι) (species : ι → AgentState L K)
    (s : ℝ) (hs : 0 < s)
    (p_tail ε_floor : ℝ≥0∞)
    (hfloor :
      (∑ τ ∈ Finset.range T,
        ((NonuniformMajority L K).transitionKernel ^ τ) c₀
          (RoleSplitConcentration.floorGate (L := L) (K := K) n a₀)ᶜ)
        ≤ ε_floor)
    (hcover :
      {c : Config (AgentState L K) |
          (NonuniformMajority L K).Reachable c₀ c ∧
            ¬ CounterSurvivalConc.WinN (L := L) (K := K) 0 n c}
        ⊆ ⋃ j ∈ Clocks,
          {c : Config (AgentState L K) |
            Phase6ClockTailDepletion.DepletedCount
              (L := L) (K := K) (species j) N0 R c})
    (hcard_reach :
      ∀ c : Config (AgentState L K),
        (NonuniformMajority L K).Reachable c₀ c → 2 ≤ c.card → c.card = n)
    (hsmall :
      ∀ j, j ∈ Clocks →
        ∀ c : Config (AgentState L K), ¬ (2 ≤ c.card) →
          ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
            {c' : Config (AgentState L K) |
              c'.count (species j) < c.count (species j)} = 0)
    (hcap_reach :
      ∀ j, j ∈ Clocks →
        ∀ c : Config (AgentState L K),
          (NonuniformMajority L K).Reachable c₀ c → c.count (species j) ≤ m)
    (htail :
      ∀ H, H ∈ Finset.range T →
        ∀ j, j ∈ Clocks →
          Phase6ClockTailDepletion.mgfDepletionTailBound
            (L := L) (K := K)
            (species j) s N0 R n m H c₀ ≤ p_tail) :
    (∑ τ ∈ Finset.range T,
        ((NonuniformMajority L K).transitionKernel ^ τ) c₀
          (stage15NoAdvanceSet (L := L) (K := K) n a₀)ᶜ)
      ≤ ε_floor +
        (T • (T • ((Clocks.card : ℕ) • p_tail)) +
          T • ((Clocks.card : ℕ) • p_tail)) := by
  have hsplit := stage15NoAdvanceSet_escape_prefix_le_floor_allPhase0_noClock
    (L := L) (K := K) n a₀ T c₀ hmcr
  have hall := phase0_allPhase0_prefix_sum_le_clock_survival_reachable
    (L := L) (K := K)
    n T R N0 m c₀ h0 Clocks species s hs p_tail
    hcover hcard_reach hsmall hcap_reach htail
  have hno := phase0_noClockAtZero_prefix_sum_range_le_clock_survival_reachable
    (L := L) (K := K)
    n T R N0 m c₀ Clocks species s hs p_tail
    hcover hcard_reach hsmall hcap_reach htail
  calc
    (∑ τ ∈ Finset.range T,
        ((NonuniformMajority L K).transitionKernel ^ τ) c₀
          (stage15NoAdvanceSet (L := L) (K := K) n a₀)ᶜ)
      ≤
        (∑ τ ∈ Finset.range T,
          ((NonuniformMajority L K).transitionKernel ^ τ) c₀
            (RoleSplitConcentration.floorGate (L := L) (K := K) n a₀)ᶜ) +
        (∑ τ ∈ Finset.range T,
          ((NonuniformMajority L K).transitionKernel ^ τ) c₀
            {c : Config (AgentState L K) |
              ¬ Phase0Window.allPhase0 (L := L) (K := K) c}) +
        (∑ τ ∈ Finset.range T,
          ((NonuniformMajority L K).transitionKernel ^ τ) c₀
            {c : Config (AgentState L K) |
              ¬ Phase0Window.noClockAtZero (L := L) (K := K) c}) := hsplit
    _ ≤ ε_floor +
        (T • (T • ((Clocks.card : ℕ) • p_tail)) +
          T • ((Clocks.card : ℕ) • p_tail)) := by
        calc
          (∑ τ ∈ Finset.range T,
            ((NonuniformMajority L K).transitionKernel ^ τ) c₀
              (RoleSplitConcentration.floorGate (L := L) (K := K) n a₀)ᶜ) +
            (∑ τ ∈ Finset.range T,
              ((NonuniformMajority L K).transitionKernel ^ τ) c₀
                {c : Config (AgentState L K) |
                  ¬ Phase0Window.allPhase0 (L := L) (K := K) c}) +
            (∑ τ ∈ Finset.range T,
              ((NonuniformMajority L K).transitionKernel ^ τ) c₀
                {c : Config (AgentState L K) |
                  ¬ Phase0Window.noClockAtZero (L := L) (K := K) c})
              ≤ ε_floor + T • (T • ((Clocks.card : ℕ) • p_tail)) +
                  T • ((Clocks.card : ℕ) • p_tail) :=
                add_le_add (add_le_add hfloor hall) hno
          _ = ε_floor +
              (T • (T • ((Clocks.card : ℕ) • p_tail)) +
                T • ((Clocks.card : ℕ) • p_tail)) := by
                ac_rfl

/-- Constructor for the no-advance Stage-1.5 residual from reachable-scoped
clock-survival inputs. -/
noncomputable def stage15NoAdvanceResidual_of_floor_clock_survival_reachable
    {ι : Type*}
    (n a₀ : ℕ) (hn2 : 2 ≤ n) (ha1 : 1 ≤ a₀) (ha_le : a₀ ≤ n - 1)
    (c₀ : Config (AgentState L K)) (ε : ℝ≥0)
    (lam : ℝ) (t : ℕ) (q : ℝ≥0∞)
    (hlam : 1 ≤ lam)
    (ht : lam *
      (stage15KernelMilestone (L := L) (K := K) n a₀ hn2 ha1 ha_le).meanTime ≤ (t : ℝ))
    (hfloorStep :
      ∀ x ∈ RoleSplitConcentration.floorGate (L := L) (K := K) n a₀,
        x ∈ stage15NoAdvanceSet (L := L) (K := K) n a₀ →
          (NonuniformMajority L K).transitionKernel x
            (RoleSplitConcentration.floorGate (L := L) (K := K) n a₀)ᶜ ≤ q)
    (hc₀ : c₀ ∈ stage15Gate (L := L) (K := K) n a₀)
    (R N0 m : ℕ)
    (Clocks : Finset ι) (species : ι → AgentState L K)
    (s : ℝ) (hs : 0 < s)
    (p_tail ε_floor : ℝ≥0∞)
    (hfloor :
      (∑ τ ∈ Finset.range t,
        ((NonuniformMajority L K).transitionKernel ^ τ) c₀
          (RoleSplitConcentration.floorGate (L := L) (K := K) n a₀)ᶜ)
        ≤ ε_floor)
    (hcover :
      {c : Config (AgentState L K) |
          (NonuniformMajority L K).Reachable c₀ c ∧
            ¬ CounterSurvivalConc.WinN (L := L) (K := K) 0 n c}
        ⊆ ⋃ j ∈ Clocks,
          {c : Config (AgentState L K) |
            Phase6ClockTailDepletion.DepletedCount
              (L := L) (K := K) (species j) N0 R c})
    (hcard_reach :
      ∀ c : Config (AgentState L K),
        (NonuniformMajority L K).Reachable c₀ c → 2 ≤ c.card → c.card = n)
    (hsmall :
      ∀ j, j ∈ Clocks →
        ∀ c : Config (AgentState L K), ¬ (2 ≤ c.card) →
          ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
            {c' : Config (AgentState L K) |
              c'.count (species j) < c.count (species j)} = 0)
    (hcap_reach :
      ∀ j, j ∈ Clocks →
        ∀ c : Config (AgentState L K),
          (NonuniformMajority L K).Reachable c₀ c → c.count (species j) ≤ m)
    (htail :
      ∀ H, H ∈ Finset.range t →
        ∀ j, j ∈ Clocks →
          Phase6ClockTailDepletion.mgfDepletionTailBound
            (L := L) (K := K)
            (species j) s N0 R n m H c₀ ≤ p_tail)
    (hbudget :
      ENNReal.ofReal (Real.exp
          (-(stage15KernelMilestone (L := L) (K := K) n a₀ hn2 ha1 ha_le).pMin *
            (stage15KernelMilestone (L := L) (K := K) n a₀ hn2 ha1 ha_le).meanTime *
            (lam - 1 - Real.log lam))) +
        ((t : ℝ≥0∞) * q +
          (ε_floor +
            (t • (t • ((Clocks.card : ℕ) • p_tail)) +
              t • ((Clocks.card : ℕ) • p_tail))))
        ≤ (ε : ℝ≥0∞)) :
    Stage15NoAdvanceResidual (L := L) (K := K) n a₀ hn2 ha1 ha_le c₀ ε := by
  refine {
    lam := lam
    t := t
    q := q
    hlam := hlam
    ht := ht
    hfloorStep := hfloorStep
    hc₀ := hc₀
    hbudget := ?_ }
  have hprefix := stage15NoAdvanceSet_escape_prefix_le_floor_clock_survival_reachable
    (L := L) (K := K)
    n a₀ t R N0 m c₀
    (stage15Gate_allPhase0 (L := L) (K := K) hc₀)
    (stage15Gate_roleMCR_le_one (L := L) (K := K) hc₀)
    Clocks species s hs p_tail ε_floor hfloor
    hcover hcard_reach hsmall hcap_reach htail
  calc
    ENNReal.ofReal (Real.exp
        (-(stage15KernelMilestone (L := L) (K := K) n a₀ hn2 ha1 ha_le).pMin *
          (stage15KernelMilestone (L := L) (K := K) n a₀ hn2 ha1 ha_le).meanTime *
          (lam - 1 - Real.log lam))) +
      ((t : ℝ≥0∞) * q +
        ∑ τ ∈ Finset.range t,
          ((NonuniformMajority L K).transitionKernel ^ τ) c₀
            (stage15NoAdvanceSet (L := L) (K := K) n a₀)ᶜ)
      ≤
    ENNReal.ofReal (Real.exp
        (-(stage15KernelMilestone (L := L) (K := K) n a₀ hn2 ha1 ha_le).pMin *
          (stage15KernelMilestone (L := L) (K := K) n a₀ hn2 ha1 ha_le).meanTime *
          (lam - 1 - Real.log lam))) +
      ((t : ℝ≥0∞) * q +
        (ε_floor +
          (t • (t • ((Clocks.card : ℕ) • p_tail)) +
            t • ((Clocks.card : ℕ) • p_tail)))) := by
        gcongr
    _ ≤ (ε : ℝ≥0∞) := hbudget

/-- `Phase0Initial` supplies the reachable card cap used by the reachable
clock-tail interface. -/
theorem phase0Initial_hcard_reach
    (n : ℕ) {c₀ : Config (AgentState L K)}
    (hinit : RoleSplitConcentration.Phase0Initial (L := L) (K := K) n c₀) :
    ∀ c : Config (AgentState L K),
      (NonuniformMajority L K).Reachable c₀ c → 2 ≤ c.card → c.card = n := by
  intro c hreach _
  exact FaithfulDischargeTierA.card_eq_on_reachable n c₀ c hreach hinit.1

/-- A conservative reachable per-species cap from `Phase0Initial`: on the
reachable trajectory every single-state count is at most the conserved population
size `n`.  Sharper role-count caps can replace this in numeric calibrations, but
this proves the reachable cap interface is satisfiable from the real card
invariant. -/
theorem phase0Initial_hcap_reach_card
    (n : ℕ) {c₀ : Config (AgentState L K)}
    (hinit : RoleSplitConcentration.Phase0Initial (L := L) (K := K) n c₀)
    (sc : AgentState L K) :
    ∀ c : Config (AgentState L K),
      (NonuniformMajority L K).Reachable c₀ c → c.count sc ≤ n := by
  intro c hreach
  have hcard := FaithfulDischargeTierA.card_eq_on_reachable n c₀ c hreach hinit.1
  rw [← hcard]
  exact Multiset.count_le_card sc c

/-- A Stage-1.5 gate start supplies the reachable card invariant used by the
reachable clock-tail interface.  This is the per-Stage-1.5 form: after the CK
composition moves into the Stage-1.5 start, `stage15Gate` pins `card = n`, and
reachability conserves that card. -/
theorem stage15Gate_hcard_reach
    {n a₀ : ℕ} {c₀ : Config (AgentState L K)}
    (hc₀ : c₀ ∈ stage15Gate (L := L) (K := K) n a₀) :
    ∀ c : Config (AgentState L K),
      (NonuniformMajority L K).Reachable c₀ c → 2 ≤ c.card → c.card = n := by
  intro c hreach _
  exact FaithfulDischargeTierA.card_eq_on_reachable n c₀ c hreach
    (stage15Gate_card (L := L) (K := K) hc₀)

/-- Conservative reachable per-species cap from a Stage-1.5 gate start.  It is
only a satisfiable fallback (`m = n`); quantitative callers should use the
sharper role-count reachable cap through
`stage15NoAdvanceResidual_of_stage15Gate_clock_cap_reachable`. -/
theorem stage15Gate_hcap_reach_card
    {n a₀ : ℕ} {c₀ : Config (AgentState L K)}
    (hc₀ : c₀ ∈ stage15Gate (L := L) (K := K) n a₀)
    (sc : AgentState L K) :
    ∀ c : Config (AgentState L K),
      (NonuniformMajority L K).Reachable c₀ c → c.count sc ≤ n := by
  intro c hreach
  have hcard := FaithfulDischargeTierA.card_eq_on_reachable n c₀ c hreach
    (stage15Gate_card (L := L) (K := K) hc₀)
  rw [← hcard]
  exact Multiset.count_le_card sc c

/-- Family form of the conservative Stage-1.5 reachable per-species cap.  This
is the exact `∀ j ∈ Clocks` producer for the `m = n` constructor. -/
theorem stage15Gate_hcap_reach_card_family
    {ι : Type*} {n a₀ : ℕ} {c₀ : Config (AgentState L K)}
    (Clocks : Finset ι) (species : ι → AgentState L K)
    (hc₀ : c₀ ∈ stage15Gate (L := L) (K := K) n a₀) :
    ∀ j, j ∈ Clocks →
      ∀ c : Config (AgentState L K),
        (NonuniformMajority L K).Reachable c₀ c → c.count (species j) ≤ n := by
  intro j _hj
  exact stage15Gate_hcap_reach_card (L := L) (K := K) hc₀ (species j)

/-- Constructor for the no-advance Stage-1.5 residual from a Stage-1.5 gate start
and a reachable-scoped per-species cap.  This removes the refuted global
`hcard` and `hsmall` inputs from the call site: `card = n` comes from
`stage15Gate`, while `hsmall` is the true small-config self-loop theorem.  The
remaining cap is explicitly reachable-scoped, so it can be supplied by the
genuine role-count window rather than by a false universal. -/
noncomputable def stage15NoAdvanceResidual_of_stage15Gate_clock_cap_reachable
    {ι : Type*}
    (n a₀ : ℕ) (hn2 : 2 ≤ n) (ha1 : 1 ≤ a₀) (ha_le : a₀ ≤ n - 1)
    (c₀ : Config (AgentState L K)) (ε : ℝ≥0)
    (lam : ℝ) (t : ℕ) (q : ℝ≥0∞)
    (hlam : 1 ≤ lam)
    (ht : lam *
      (stage15KernelMilestone (L := L) (K := K) n a₀ hn2 ha1 ha_le).meanTime ≤ (t : ℝ))
    (hfloorStep :
      ∀ x ∈ RoleSplitConcentration.floorGate (L := L) (K := K) n a₀,
        x ∈ stage15NoAdvanceSet (L := L) (K := K) n a₀ →
          (NonuniformMajority L K).transitionKernel x
            (RoleSplitConcentration.floorGate (L := L) (K := K) n a₀)ᶜ ≤ q)
    (hc₀ : c₀ ∈ stage15Gate (L := L) (K := K) n a₀)
    (R N0 m : ℕ)
    (Clocks : Finset ι) (species : ι → AgentState L K)
    (s : ℝ) (hs : 0 < s)
    (p_tail ε_floor : ℝ≥0∞)
    (hfloor :
      (∑ τ ∈ Finset.range t,
        ((NonuniformMajority L K).transitionKernel ^ τ) c₀
          (RoleSplitConcentration.floorGate (L := L) (K := K) n a₀)ᶜ)
        ≤ ε_floor)
    (hcover :
      {c : Config (AgentState L K) |
          (NonuniformMajority L K).Reachable c₀ c ∧
            ¬ CounterSurvivalConc.WinN (L := L) (K := K) 0 n c}
        ⊆ ⋃ j ∈ Clocks,
          {c : Config (AgentState L K) |
            Phase6ClockTailDepletion.DepletedCount
              (L := L) (K := K) (species j) N0 R c})
    (hcap_reach :
      ∀ j, j ∈ Clocks →
        ∀ c : Config (AgentState L K),
          (NonuniformMajority L K).Reachable c₀ c → c.count (species j) ≤ m)
    (htail :
      ∀ H, H ∈ Finset.range t →
        ∀ j, j ∈ Clocks →
          Phase6ClockTailDepletion.mgfDepletionTailBound
            (L := L) (K := K)
            (species j) s N0 R n m H c₀ ≤ p_tail)
    (hbudget :
      ENNReal.ofReal (Real.exp
          (-(stage15KernelMilestone (L := L) (K := K) n a₀ hn2 ha1 ha_le).pMin *
            (stage15KernelMilestone (L := L) (K := K) n a₀ hn2 ha1 ha_le).meanTime *
            (lam - 1 - Real.log lam))) +
        ((t : ℝ≥0∞) * q +
          (ε_floor +
            (t • (t • ((Clocks.card : ℕ) • p_tail)) +
              t • ((Clocks.card : ℕ) • p_tail))))
        ≤ (ε : ℝ≥0∞)) :
    Stage15NoAdvanceResidual (L := L) (K := K) n a₀ hn2 ha1 ha_le c₀ ε :=
  stage15NoAdvanceResidual_of_floor_clock_survival_reachable
    (L := L) (K := K)
    n a₀ hn2 ha1 ha_le c₀ ε lam t q hlam ht hfloorStep hc₀
    R N0 m Clocks species s hs p_tail ε_floor hfloor hcover
    (stage15Gate_hcard_reach (L := L) (K := K) hc₀)
    (fun j _hj => FaithfulDischargeTierA.hsmall_self_loop (L := L) (K := K) (species j))
    hcap_reach htail hbudget

/-- One-horizon phase-0 clock-zero bound through the aggregate counter-depth
cover.  This is the phase-0 mirror of the repaired Phase-6 shape: the
deterministic cover is the TRUE singleton aggregate
`ClockCounterDepthCover.counterDepth_hcover`, and the probabilistic input is the
aggregate `CounterDepthDepleted` tail.  No per-species `DepletedCount` cover is
used. -/
theorem phase0_noClockAtZero_fail_mass_le_aggregate_depth
    (n H R : ℕ)
    (c₀ : Config (AgentState L K))
    (s : ℝ) (p_depth : ℝ≥0∞)
    (hdepth :
      ((NonuniformMajority L K).transitionKernel ^ H) c₀
        {c : Config (AgentState L K) |
          ClockCounterDepthCover.CounterDepthDepleted
            (L := L) (K := K) n 0 R s c}
        ≤ p_depth) :
    ((NonuniformMajority L K).transitionKernel ^ H) c₀
        {c : Config (AgentState L K) |
          ¬ Phase0Window.noClockAtZero (L := L) (K := K) c}
      ≤ p_depth := by
  have hdepthCover :
      {c : Config (AgentState L K) |
          ¬ CounterSurvivalConc.WinN (L := L) (K := K) 0 n c}
        ⊆
      {c : Config (AgentState L K) |
          ClockCounterDepthCover.CounterDepthDepleted
            (L := L) (K := K) n 0 R s c} := by
    intro c hc
    have h :=
      ClockCounterDepthCover.counterDepth_hcover
        (L := L) (K := K) n 0 R s hc
    simpa [ClockCounterDepthCover.DepthClocks,
      ClockCounterDepthCover.DepthDepleted] using h
  calc
    ((NonuniformMajority L K).transitionKernel ^ H) c₀
        {c : Config (AgentState L K) |
          ¬ Phase0Window.noClockAtZero (L := L) (K := K) c}
        ≤
      ((NonuniformMajority L K).transitionKernel ^ H) c₀
        {c : Config (AgentState L K) |
          ¬ Phase6LeakZero.ClockPos (L := L) (K := K) c} :=
        noClockAtZero_fail_mass_le_clockPos_fail_mass
          (L := L) (K := K) H c₀
    _ ≤
      ((NonuniformMajority L K).transitionKernel ^ H) c₀
        {c : Config (AgentState L K) |
          ¬ CounterSurvivalConc.WinN (L := L) (K := K) 0 n c} :=
        Phase6ClockTailDepletion.clockPos_fail_mass_le_winN_fail_mass
          (L := L) (K := K) 0 n H c₀
    _ ≤
      ((NonuniformMajority L K).transitionKernel ^ H) c₀
        {c : Config (AgentState L K) |
          ClockCounterDepthCover.CounterDepthDepleted
            (L := L) (K := K) n 0 R s c} :=
        measure_mono hdepthCover
    _ ≤ p_depth := hdepth

/-- Prefix phase-0 clock-zero bound through the aggregate counter-depth tail. -/
theorem phase0_noClockAtZero_prefix_sum_range_le_aggregate_depth
    (n T R : ℕ)
    (c₀ : Config (AgentState L K))
    (s : ℝ) (p_depth : ℝ≥0∞)
    (hdepth :
      ∀ H, H ∈ Finset.range T →
        ((NonuniformMajority L K).transitionKernel ^ H) c₀
          {c : Config (AgentState L K) |
            ClockCounterDepthCover.CounterDepthDepleted
              (L := L) (K := K) n 0 R s c}
          ≤ p_depth) :
    (∑ H ∈ Finset.range T,
        ((NonuniformMajority L K).transitionKernel ^ H) c₀
          {c : Config (AgentState L K) |
            ¬ Phase0Window.noClockAtZero (L := L) (K := K) c})
      ≤ T • p_depth := by
  classical
  calc
    (∑ H ∈ Finset.range T,
        ((NonuniformMajority L K).transitionKernel ^ H) c₀
          {c : Config (AgentState L K) |
            ¬ Phase0Window.noClockAtZero (L := L) (K := K) c})
        ≤ ∑ _H ∈ Finset.range T, p_depth := by
          exact Finset.sum_le_sum (fun H hH =>
            phase0_noClockAtZero_fail_mass_le_aggregate_depth
              (L := L) (K := K) n H R c₀ s p_depth (hdepth H hH))
    _ = T • p_depth := by
          rw [Finset.sum_const, Finset.card_range]

/-- Endpoint all-phase-0 no-advance bound from the aggregate counter-depth tail. -/
theorem phase0_allPhase0_noadvance_le_aggregate_depth
    (n T R : ℕ)
    (c₀ : Config (AgentState L K))
    (h0 : Phase0Window.allPhase0 (L := L) (K := K) c₀)
    (s : ℝ) (p_depth : ℝ≥0∞)
    (hdepth :
      ∀ H, H ∈ Finset.range T →
        ((NonuniformMajority L K).transitionKernel ^ H) c₀
          {c : Config (AgentState L K) |
            ClockCounterDepthCover.CounterDepthDepleted
              (L := L) (K := K) n 0 R s c}
          ≤ p_depth) :
    ((NonuniformMajority L K).transitionKernel ^ T) c₀
        {c : Config (AgentState L K) |
          ¬ Phase0Window.allPhase0 (L := L) (K := K) c}
      ≤ T • p_depth :=
  (Phase0Window.allPhase0_window_le_prefix_sum
    (L := L) (K := K) T c₀ h0).trans
    (phase0_noClockAtZero_prefix_sum_range_le_aggregate_depth
      (L := L) (K := K) n T R c₀ s p_depth hdepth)

/-- Prefix all-phase-0 no-advance bound from the aggregate counter-depth tail. -/
theorem phase0_allPhase0_prefix_sum_le_aggregate_depth
    (n T R : ℕ)
    (c₀ : Config (AgentState L K))
    (h0 : Phase0Window.allPhase0 (L := L) (K := K) c₀)
    (s : ℝ) (p_depth : ℝ≥0∞)
    (hdepth :
      ∀ H, H ∈ Finset.range T →
        ((NonuniformMajority L K).transitionKernel ^ H) c₀
          {c : Config (AgentState L K) |
            ClockCounterDepthCover.CounterDepthDepleted
              (L := L) (K := K) n 0 R s c}
          ≤ p_depth) :
    (∑ τ ∈ Finset.range T,
        ((NonuniformMajority L K).transitionKernel ^ τ) c₀
          {c : Config (AgentState L K) |
            ¬ Phase0Window.allPhase0 (L := L) (K := K) c})
      ≤ T • (T • p_depth) :=
  (allPhase0_prefix_sum_le_noClockAtZero_prefix_sum
    (L := L) (K := K) T c₀ h0).trans
    (nsmul_le_nsmul_right
      (phase0_noClockAtZero_prefix_sum_range_le_aggregate_depth
        (L := L) (K := K) n T R c₀ s p_depth hdepth) T)

/-- Stage-1.5 side-set escape prefix using the TRUE aggregate counter-depth
cover/tail.  The clock contribution has no per-species `Clocks/species` union:
the clock-zero and all-phase-0 leaks are paid by the singleton aggregate
`CounterDepthDepleted` tail. -/
theorem stage15NoAdvanceSet_escape_prefix_le_floor_aggregate_depth
    (n a₀ T R : ℕ)
    (c₀ : Config (AgentState L K))
    (h0 : Phase0Window.allPhase0 (L := L) (K := K) c₀)
    (hmcr : RoleSplitConcentration.roleMCRCount (L := L) (K := K) c₀ ≤ 1)
    (s : ℝ)
    (p_depth ε_floor : ℝ≥0∞)
    (hfloor :
      (∑ τ ∈ Finset.range T,
        ((NonuniformMajority L K).transitionKernel ^ τ) c₀
          (RoleSplitConcentration.floorGate (L := L) (K := K) n a₀)ᶜ)
        ≤ ε_floor)
    (hdepth :
      ∀ H, H ∈ Finset.range T →
        ((NonuniformMajority L K).transitionKernel ^ H) c₀
          {c : Config (AgentState L K) |
            ClockCounterDepthCover.CounterDepthDepleted
              (L := L) (K := K) n 0 R s c}
          ≤ p_depth) :
    (∑ τ ∈ Finset.range T,
        ((NonuniformMajority L K).transitionKernel ^ τ) c₀
          (stage15NoAdvanceSet (L := L) (K := K) n a₀)ᶜ)
      ≤ ε_floor + (T • (T • p_depth) + T • p_depth) := by
  have hsplit := stage15NoAdvanceSet_escape_prefix_le_floor_allPhase0_noClock
    (L := L) (K := K) n a₀ T c₀ hmcr
  have hall := phase0_allPhase0_prefix_sum_le_aggregate_depth
    (L := L) (K := K) n T R c₀ h0 s p_depth hdepth
  have hno := phase0_noClockAtZero_prefix_sum_range_le_aggregate_depth
    (L := L) (K := K) n T R c₀ s p_depth hdepth
  calc
    (∑ τ ∈ Finset.range T,
        ((NonuniformMajority L K).transitionKernel ^ τ) c₀
          (stage15NoAdvanceSet (L := L) (K := K) n a₀)ᶜ)
      ≤
        (∑ τ ∈ Finset.range T,
          ((NonuniformMajority L K).transitionKernel ^ τ) c₀
            (RoleSplitConcentration.floorGate (L := L) (K := K) n a₀)ᶜ) +
        (∑ τ ∈ Finset.range T,
          ((NonuniformMajority L K).transitionKernel ^ τ) c₀
            {c : Config (AgentState L K) |
              ¬ Phase0Window.allPhase0 (L := L) (K := K) c}) +
        (∑ τ ∈ Finset.range T,
          ((NonuniformMajority L K).transitionKernel ^ τ) c₀
            {c : Config (AgentState L K) |
              ¬ Phase0Window.noClockAtZero (L := L) (K := K) c}) := hsplit
    _ ≤ ε_floor + T • (T • p_depth) + T • p_depth :=
        add_le_add (add_le_add hfloor hall) hno
    _ = ε_floor + (T • (T • p_depth) + T • p_depth) := by
        ac_rfl

/-- Constructor for the no-advance Stage-1.5 residual from the aggregate
counter-depth clock-tail. -/
noncomputable def stage15NoAdvanceResidual_of_floor_aggregate_depth
    (n a₀ : ℕ) (hn2 : 2 ≤ n) (ha1 : 1 ≤ a₀) (ha_le : a₀ ≤ n - 1)
    (c₀ : Config (AgentState L K)) (ε : ℝ≥0)
    (lam : ℝ) (t : ℕ) (q : ℝ≥0∞)
    (hlam : 1 ≤ lam)
    (ht : lam *
      (stage15KernelMilestone (L := L) (K := K) n a₀ hn2 ha1 ha_le).meanTime ≤ (t : ℝ))
    (hfloorStep :
      ∀ x ∈ RoleSplitConcentration.floorGate (L := L) (K := K) n a₀,
        x ∈ stage15NoAdvanceSet (L := L) (K := K) n a₀ →
          (NonuniformMajority L K).transitionKernel x
            (RoleSplitConcentration.floorGate (L := L) (K := K) n a₀)ᶜ ≤ q)
    (hc₀ : c₀ ∈ stage15Gate (L := L) (K := K) n a₀)
    (R : ℕ) (s : ℝ)
    (p_depth ε_floor : ℝ≥0∞)
    (hfloor :
      (∑ τ ∈ Finset.range t,
        ((NonuniformMajority L K).transitionKernel ^ τ) c₀
          (RoleSplitConcentration.floorGate (L := L) (K := K) n a₀)ᶜ)
        ≤ ε_floor)
    (hdepth :
      ∀ H, H ∈ Finset.range t →
        ((NonuniformMajority L K).transitionKernel ^ H) c₀
          {c : Config (AgentState L K) |
            ClockCounterDepthCover.CounterDepthDepleted
              (L := L) (K := K) n 0 R s c}
          ≤ p_depth)
    (hbudget :
      ENNReal.ofReal (Real.exp
          (-(stage15KernelMilestone (L := L) (K := K) n a₀ hn2 ha1 ha_le).pMin *
            (stage15KernelMilestone (L := L) (K := K) n a₀ hn2 ha1 ha_le).meanTime *
            (lam - 1 - Real.log lam))) +
        ((t : ℝ≥0∞) * q +
          (ε_floor + (t • (t • p_depth) + t • p_depth)))
        ≤ (ε : ℝ≥0∞)) :
    Stage15NoAdvanceResidual (L := L) (K := K) n a₀ hn2 ha1 ha_le c₀ ε := by
  refine {
    lam := lam
    t := t
    q := q
    hlam := hlam
    ht := ht
    hfloorStep := hfloorStep
    hc₀ := hc₀
    hbudget := ?_ }
  have hprefix := stage15NoAdvanceSet_escape_prefix_le_floor_aggregate_depth
    (L := L) (K := K)
    n a₀ t R c₀
    (stage15Gate_allPhase0 (L := L) (K := K) hc₀)
    (stage15Gate_roleMCR_le_one (L := L) (K := K) hc₀)
    s p_depth ε_floor hfloor hdepth
  calc
    ENNReal.ofReal (Real.exp
        (-(stage15KernelMilestone (L := L) (K := K) n a₀ hn2 ha1 ha_le).pMin *
          (stage15KernelMilestone (L := L) (K := K) n a₀ hn2 ha1 ha_le).meanTime *
          (lam - 1 - Real.log lam))) +
      ((t : ℝ≥0∞) * q +
        ∑ τ ∈ Finset.range t,
          ((NonuniformMajority L K).transitionKernel ^ τ) c₀
            (stage15NoAdvanceSet (L := L) (K := K) n a₀)ᶜ)
      ≤
    ENNReal.ofReal (Real.exp
        (-(stage15KernelMilestone (L := L) (K := K) n a₀ hn2 ha1 ha_le).pMin *
          (stage15KernelMilestone (L := L) (K := K) n a₀ hn2 ha1 ha_le).meanTime *
          (lam - 1 - Real.log lam))) +
      ((t : ℝ≥0∞) * q +
        (ε_floor + (t • (t • p_depth) + t • p_depth))) := by
        gcongr
    _ ≤ (ε : ℝ≥0∞) := hbudget

/-- Conservative satisfiable Stage-1.5 aggregate-clock constructor.
The old implementation of this name consumed a reachable-scoped per-species
cover.  That is still the false shape for the `WinN` breach.  This version
consumes only the aggregate `CounterDepthDepleted` tail, with the deterministic
cover supplied by `ClockCounterDepthCover.counterDepth_hcover`. -/
noncomputable def stage15NoAdvanceResidual_of_stage15Gate_card_cap_reachable
    (n a₀ : ℕ) (hn2 : 2 ≤ n) (ha1 : 1 ≤ a₀) (ha_le : a₀ ≤ n - 1)
    (c₀ : Config (AgentState L K)) (ε : ℝ≥0)
    (lam : ℝ) (t : ℕ) (q : ℝ≥0∞)
    (hlam : 1 ≤ lam)
    (ht : lam *
      (stage15KernelMilestone (L := L) (K := K) n a₀ hn2 ha1 ha_le).meanTime ≤ (t : ℝ))
    (hfloorStep :
      ∀ x ∈ RoleSplitConcentration.floorGate (L := L) (K := K) n a₀,
        x ∈ stage15NoAdvanceSet (L := L) (K := K) n a₀ →
          (NonuniformMajority L K).transitionKernel x
            (RoleSplitConcentration.floorGate (L := L) (K := K) n a₀)ᶜ ≤ q)
    (hc₀ : c₀ ∈ stage15Gate (L := L) (K := K) n a₀)
    (R : ℕ) (s : ℝ)
    (p_depth ε_floor : ℝ≥0∞)
    (hfloor :
      (∑ τ ∈ Finset.range t,
        ((NonuniformMajority L K).transitionKernel ^ τ) c₀
          (RoleSplitConcentration.floorGate (L := L) (K := K) n a₀)ᶜ)
        ≤ ε_floor)
    (hdepth :
      ∀ H, H ∈ Finset.range t →
        ((NonuniformMajority L K).transitionKernel ^ H) c₀
          {c : Config (AgentState L K) |
            ClockCounterDepthCover.CounterDepthDepleted
              (L := L) (K := K) n 0 R s c}
          ≤ p_depth)
    (hbudget :
      ENNReal.ofReal (Real.exp
          (-(stage15KernelMilestone (L := L) (K := K) n a₀ hn2 ha1 ha_le).pMin *
            (stage15KernelMilestone (L := L) (K := K) n a₀ hn2 ha1 ha_le).meanTime *
            (lam - 1 - Real.log lam))) +
        ((t : ℝ≥0∞) * q +
          (ε_floor + (t • (t • p_depth) + t • p_depth)))
        ≤ (ε : ℝ≥0∞)) :
    Stage15NoAdvanceResidual (L := L) (K := K) n a₀ hn2 ha1 ha_le c₀ ε :=
  stage15NoAdvanceResidual_of_floor_aggregate_depth
    (L := L) (K := K)
    n a₀ hn2 ha1 ha_le c₀ ε lam t q hlam ht hfloorStep hc₀
    R s p_depth ε_floor hfloor hdepth hbudget

/-- Stage-1.5 `PhaseConvergenceW`: from the timed gate, the last `RoleMCR`
disappears with the supplied terminal-drain plus escape budget.  If the start
already has no `RoleMCR`, the absorbing `noMCRShell` proof gives zero bad mass. -/
noncomputable def stage15W_of_timedResidual
    (n a₀ : ℕ) (hn2 : 2 ≤ n) (ha1 : 1 ≤ a₀) (ha_le : a₀ ≤ n - 1)
    (ε : ℝ≥0)
    (w : ∀ c₀, c₀ ∈ stage15Gate (L := L) (K := K) n a₀ →
        Stage15TimedResidual (L := L) (K := K) n a₀ hn2 ha1 ha_le c₀ ε)
    (tt : ℕ)
    (htt : ∀ c₀ (hg : c₀ ∈ stage15Gate (L := L) (K := K) n a₀),
        (w c₀ hg).t = tt) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel where
  Pre c := c ∈ stage15Gate (L := L) (K := K) n a₀
  Post c := RoleSplitConcentration.roleMCRCount (L := L) (K := K) c = 0
  t := tt
  ε := ε
  convergence := by
    intro c₀ hg
    by_cases hmcr0 : RoleSplitConcentration.roleMCRCount (L := L) (K := K) c₀ = 0
    · have hno : c₀ ∈ RoleSplitConcentration.noMCRShell (L := L) (K := K) n :=
        ⟨stage15Gate_card (L := L) (K := K) hg, hmcr0⟩
      have hzero := RoleSplitConcentration.noMCRShell_pow_compl_eq_zero
        (L := L) (K := K) c₀ hno tt
      have hsub :
          {y : Config (AgentState L K) |
            ¬ RoleSplitConcentration.roleMCRCount (L := L) (K := K) y = 0}
            ⊆ (RoleSplitConcentration.noMCRShell (L := L) (K := K) n)ᶜ := by
        intro y hy hyno
        exact hy (RoleSplitConcentration.noMCRShell_mcr0 (L := L) (K := K) hyno)
      calc ((NonuniformMajority L K).transitionKernel ^ tt) c₀
            {y | ¬ RoleSplitConcentration.roleMCRCount (L := L) (K := K) y = 0}
          ≤ ((NonuniformMajority L K).transitionKernel ^ tt) c₀
              (RoleSplitConcentration.noMCRShell (L := L) (K := K) n)ᶜ := measure_mono hsub
        _ = 0 := hzero
        _ ≤ (ε : ℝ≥0∞) := zero_le'
    · set hw := w c₀ hg with hwdef
      have hheadline := RoleSplitConcentration.real_bad_le_janson_add_escape
        (K := (NonuniformMajority L K).transitionKernel)
        (G := stage15Gate (L := L) (K := K) n a₀)
        (S := stage15Gate (L := L) (K := K) n a₀)
        (good := fun y =>
          RoleSplitConcentration.roleMCRCount (L := L) (K := K) y = 0)
        (q := hw.q)
        (stage15KernelMilestone (L := L) (K := K) n a₀ hn2 ha1 ha_le)
        (NonuniformMajority L K)
        (stage15KernelMilestone_post_sound (L := L) (K := K) n a₀ hn2 ha1 ha_le)
        hw.hstep c₀ hw.hc₀
        (stage15KernelMilestone_hPre_of_not_terminal
          (L := L) (K := K) n a₀ hn2 ha1 ha_le hmcr0)
        hw.lam hw.hlam hw.t hw.ht
      have hteq : hw.t = tt := by rw [hwdef]; exact htt c₀ hg
      rw [← hteq]
      exact le_trans hheadline hw.hbudget

@[simp] theorem stage15W_of_timedResidual_Post
    (n a₀ : ℕ) (hn2 : 2 ≤ n) (ha1 : 1 ≤ a₀) (ha_le : a₀ ≤ n - 1)
    (ε : ℝ≥0)
    (w : ∀ c₀, c₀ ∈ stage15Gate (L := L) (K := K) n a₀ →
        Stage15TimedResidual (L := L) (K := K) n a₀ hn2 ha1 ha_le c₀ ε)
    (tt : ℕ)
    (htt : ∀ c₀ (hg : c₀ ∈ stage15Gate (L := L) (K := K) n a₀),
        (w c₀ hg).t = tt) :
    (stage15W_of_timedResidual (L := L) (K := K) n a₀ hn2 ha1 ha_le ε w tt htt).Post =
      fun c => RoleSplitConcentration.roleMCRCount (L := L) (K := K) c = 0 := rfl

/-- Stage-1.5 `PhaseConvergenceW` with the no-advance side set wired in.  The
killed milestone runs on `stage15Gate`; the escape side set is
`stage15NoAdvanceSet`, whose prefix is discharged by the clock-survival bridge. -/
noncomputable def stage15W_of_noAdvanceResidual
    (n a₀ : ℕ) (hn2 : 2 ≤ n) (ha1 : 1 ≤ a₀) (ha_le : a₀ ≤ n - 1)
    (ε : ℝ≥0)
    (w : ∀ c₀, c₀ ∈ stage15Gate (L := L) (K := K) n a₀ →
        Stage15NoAdvanceResidual (L := L) (K := K) n a₀ hn2 ha1 ha_le c₀ ε)
    (tt : ℕ)
    (htt : ∀ c₀ (hg : c₀ ∈ stage15Gate (L := L) (K := K) n a₀),
        (w c₀ hg).t = tt) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel where
  Pre c := c ∈ stage15Gate (L := L) (K := K) n a₀
  Post c := RoleSplitConcentration.roleMCRCount (L := L) (K := K) c = 0
  t := tt
  ε := ε
  convergence := by
    intro c₀ hg
    by_cases hmcr0 : RoleSplitConcentration.roleMCRCount (L := L) (K := K) c₀ = 0
    · have hno : c₀ ∈ RoleSplitConcentration.noMCRShell (L := L) (K := K) n :=
        ⟨stage15Gate_card (L := L) (K := K) hg, hmcr0⟩
      have hzero := RoleSplitConcentration.noMCRShell_pow_compl_eq_zero
        (L := L) (K := K) c₀ hno tt
      have hsub :
          {y : Config (AgentState L K) |
            ¬ RoleSplitConcentration.roleMCRCount (L := L) (K := K) y = 0}
            ⊆ (RoleSplitConcentration.noMCRShell (L := L) (K := K) n)ᶜ := by
        intro y hy hyno
        exact hy (RoleSplitConcentration.noMCRShell_mcr0 (L := L) (K := K) hyno)
      calc ((NonuniformMajority L K).transitionKernel ^ tt) c₀
            {y | ¬ RoleSplitConcentration.roleMCRCount (L := L) (K := K) y = 0}
          ≤ ((NonuniformMajority L K).transitionKernel ^ tt) c₀
              (RoleSplitConcentration.noMCRShell (L := L) (K := K) n)ᶜ := measure_mono hsub
        _ = 0 := hzero
        _ ≤ (ε : ℝ≥0∞) := zero_le'
    · set hw := w c₀ hg with hwdef
      have hheadline := RoleSplitConcentration.real_bad_le_janson_add_escape
        (K := (NonuniformMajority L K).transitionKernel)
        (G := stage15Gate (L := L) (K := K) n a₀)
        (S := stage15NoAdvanceSet (L := L) (K := K) n a₀)
        (good := fun y =>
          RoleSplitConcentration.roleMCRCount (L := L) (K := K) y = 0)
        (q := hw.q)
        (stage15KernelMilestone (L := L) (K := K) n a₀ hn2 ha1 ha_le)
        (NonuniformMajority L K)
        (stage15KernelMilestone_post_sound (L := L) (K := K) n a₀ hn2 ha1 ha_le)
        (stage15Gate_hstep_of_floor_noadvance (L := L) (K := K) hw.hfloorStep)
        c₀ hw.hc₀
        (stage15KernelMilestone_hPre_of_not_terminal
          (L := L) (K := K) n a₀ hn2 ha1 ha_le hmcr0)
        hw.lam hw.hlam hw.t hw.ht
      have hteq : hw.t = tt := by rw [hwdef]; exact htt c₀ hg
      rw [← hteq]
      exact le_trans hheadline hw.hbudget

@[simp] theorem stage15W_of_noAdvanceResidual_Post
    (n a₀ : ℕ) (hn2 : 2 ≤ n) (ha1 : 1 ≤ a₀) (ha_le : a₀ ≤ n - 1)
    (ε : ℝ≥0)
    (w : ∀ c₀, c₀ ∈ stage15Gate (L := L) (K := K) n a₀ →
        Stage15NoAdvanceResidual (L := L) (K := K) n a₀ hn2 ha1 ha_le c₀ ε)
    (tt : ℕ)
    (htt : ∀ c₀ (hg : c₀ ∈ stage15Gate (L := L) (K := K) n a₀),
        (w c₀ hg).t = tt) :
    (stage15W_of_noAdvanceResidual (L := L) (K := K)
      n a₀ hn2 ha1 ha_le ε w tt htt).Post =
      fun c => RoleSplitConcentration.roleMCRCount (L := L) (K := K) c = 0 := rfl

/-! ### Strong Stage-1.5 endpoint for the Stage-2 CR drain

The plain Stage-1.5 instance above exposes only `roleMCRCount = 0`.  The
Stage-2 CR-drain instance needs the stronger shell
`noMCRCRPhase0Shell`: fixed cardinality, no MCR, and all residual CR agents
still in phase 0.  Since the killed Stage-1.5 chain keeps alive states inside
`stage15Gate`, the same one-milestone proof can expose the stronger endpoint
without changing the residual budget. -/

/-- Strong terminal predicate for Stage-1.5.  Cemetery is terminal; an alive
state is terminal only when it is still in `stage15Gate` and has no `RoleMCR`. -/
def stage15StrongTerminal (n a₀ : ℕ) : Option (Config (AgentState L K)) → Prop
  | none => True
  | some c =>
      c ∈ stage15Gate (L := L) (K := K) n a₀ ∧
        RoleSplitConcentration.roleMCRCount (L := L) (K := K) c = 0

theorem stage15Terminal_of_stage15StrongTerminal {n a₀ : ℕ}
    {o : Option (Config (AgentState L K))}
    (ho : stage15StrongTerminal (L := L) (K := K) n a₀ o) :
    stage15Terminal (L := L) (K := K) o := by
  cases o with
  | none => exact trivial
  | some c => exact ho.2

theorem stage15StrongTerminal_monotone {n a₀ : ℕ}
    (o o' : Option (Config (AgentState L K)))
    (hmono : stage15StrongTerminal (L := L) (K := K) n a₀ o)
    (hsupp : 0 < GatedDrift.killK_now (NonuniformMajority L K).transitionKernel
      (stage15Gate (L := L) (K := K) n a₀) o {o'}) :
    stage15StrongTerminal (L := L) (K := K) n a₀ o' := by
  classical
  rcases o' with _ | c'
  · exact trivial
  · have hc'G : c' ∈ stage15Gate (L := L) (K := K) n a₀ :=
      GatedDrift.alive_support_gate
        (K := (NonuniformMajority L K).transitionKernel)
        (G := stage15Gate (L := L) (K := K) n a₀) o c' hsupp
    have hterm' :=
      stage15Terminal_monotone (L := L) (K := K) (n := n) (a₀ := a₀)
        o (some c')
        (stage15Terminal_of_stage15StrongTerminal (L := L) (K := K) hmono)
        hsupp
    exact ⟨hc'G, hterm'⟩

/-- At a gated nonterminal Stage-1.5 state, the real kernel has at least
`floorRate n a₀ 1` mass on strong-terminal successors. -/
theorem stage15StrongTerminal_progress_mass {n a₀ : ℕ} (hn2 : 2 ≤ n)
    (c : Config (AgentState L K)) (hc : c ∈ stage15Gate (L := L) (K := K) n a₀)
    (h_not : ¬ stage15StrongTerminal (L := L) (K := K) n a₀ (some c)) :
    (GatedDrift.killK_now (NonuniformMajority L K).transitionKernel
        (stage15Gate (L := L) (K := K) n a₀) (some c))
        {o | stage15StrongTerminal (L := L) (K := K) n a₀ o} ≥
      ENNReal.ofReal (RoleSplitConcentration.floorRate n a₀ 1) := by
  classical
  have hrole_eq_one :
      RoleSplitConcentration.roleMCRCount (L := L) (K := K) c = 1 := by
    have hne : RoleSplitConcentration.roleMCRCount (L := L) (K := K) c ≠ 0 := by
      intro h0
      exact h_not ⟨hc, h0⟩
    have hle := stage15Gate_roleMCR_le_one (L := L) (K := K) hc
    omega
  have hmcr_eq_one : ExactMajority.mcrCount (L := L) (K := K) c = 1 := by
    rw [← RoleSplitConcentration.roleMCRCount_eq_mcrCount (L := L) (K := K) c]
    exact hrole_eq_one
  rw [GatedDrift.killK_now_some_gated
        (K := (NonuniformMajority L K).transitionKernel)
        (G := stage15Gate (L := L) (K := K) n a₀) c hc,
      Measure.map_apply (GatedDrift.gateMap_measurable _)
        (DiscreteMeasurableSpace.forall_measurableSet _)]
  have hbridge := RoleSplitConcentration.phase0_mcrCount_decrease_prob_floor
    (L := L) (K := K) c n a₀
    (stage15Gate_card (L := L) (K := K) hc) hn2
    (stage15Gate_phase0 (L := L) (K := K) hc)
    (stage15Gate_floor (L := L) (K := K) hc)
  have hrate : RoleSplitConcentration.floorRate n a₀ 1 =
      (((ExactMajority.mcrCount (L := L) (K := K) c * a₀ : ℕ) : ℝ) /
        ((n : ℝ) * ((n : ℝ) - 1))) := by
    unfold RoleSplitConcentration.floorRate
    rw [hmcr_eq_one]
  rw [hrate]
  have hsub : {c' : Config (AgentState L K) |
        ExactMajority.mcrCount (L := L) (K := K) c' <
          ExactMajority.mcrCount (L := L) (K := K) c} ⊆
      (GatedDrift.gateMap (stage15Gate (L := L) (K := K) n a₀)) ⁻¹'
        {o | stage15StrongTerminal (L := L) (K := K) n a₀ o} := by
    intro c' hc'
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    unfold GatedDrift.gateMap
    by_cases hc'G : c' ∈ stage15Gate (L := L) (K := K) n a₀
    · rw [if_pos hc'G]
      change c' ∈ stage15Gate (L := L) (K := K) n a₀ ∧
        RoleSplitConcentration.roleMCRCount (L := L) (K := K) c' = 0
      refine ⟨hc'G, ?_⟩
      have hmcr0 : ExactMajority.mcrCount (L := L) (K := K) c' = 0 := by
        have hc'_lt : ExactMajority.mcrCount (L := L) (K := K) c' <
            ExactMajority.mcrCount (L := L) (K := K) c := hc'
        rw [hmcr_eq_one] at hc'_lt
        omega
      rw [RoleSplitConcentration.roleMCRCount_eq_mcrCount (L := L) (K := K) c']
      exact hmcr0
    · rw [if_neg hc'G]
      exact trivial
  calc ENNReal.ofReal
        (((ExactMajority.mcrCount (L := L) (K := K) c * a₀ : ℕ) : ℝ) /
          ((n : ℝ) * ((n : ℝ) - 1)))
      ≤ ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
          {c' | ExactMajority.mcrCount (L := L) (K := K) c' <
            ExactMajority.mcrCount (L := L) (K := K) c} := hbridge
    _ ≤ ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
          ((GatedDrift.gateMap (stage15Gate (L := L) (K := K) n a₀)) ⁻¹'
            {o | stage15StrongTerminal (L := L) (K := K) n a₀ o}) :=
        measure_mono hsub

theorem stage15StrongTerminal_progress {n a₀ : ℕ} (hn2 : 2 ≤ n)
    (ha_le : a₀ ≤ n - 1)
    (i : Fin 1) (o : Option (Config (AgentState L K)))
    (_h_prev : ∀ j : Fin 1, j < i →
      stage15StrongTerminal (L := L) (K := K) n a₀ o)
    (h_not : ¬ stage15StrongTerminal (L := L) (K := K) n a₀ o) :
    GatedDrift.killK_now (NonuniformMajority L K).transitionKernel
        (stage15Gate (L := L) (K := K) n a₀) o
        {o' | stage15StrongTerminal (L := L) (K := K) n a₀ o'} ≥
      ENNReal.ofReal (RoleSplitConcentration.floorRate n a₀ 1) := by
  classical
  have hfloorRate_le_one : RoleSplitConcentration.floorRate n a₀ 1 ≤ 1 :=
    RoleSplitConcentration.floorRate_le_one (n := n) (a₀ := a₀) (M := 1) hn2 (by omega) ha_le
  rcases o with _ | c
  · exact absurd (trivial : stage15StrongTerminal (L := L) (K := K) n a₀
      (none : Option (Config (AgentState L K)))) h_not
  · by_cases hcG : c ∈ stage15Gate (L := L) (K := K) n a₀
    · exact stage15StrongTerminal_progress_mass (L := L) (K := K) hn2 c hcG h_not
    · rw [GatedDrift.killK_now_ungated c hcG, Measure.dirac_apply' _
        (DiscreteMeasurableSpace.forall_measurableSet _),
        Set.indicator_of_mem (show (none : Option (Config (AgentState L K))) ∈
          {o' | stage15StrongTerminal (L := L) (K := K) n a₀ o'} from trivial)]
      calc ENNReal.ofReal (RoleSplitConcentration.floorRate n a₀ 1) ≤ ENNReal.ofReal 1 :=
            ENNReal.ofReal_le_ofReal hfloorRate_le_one
        _ = 1 := ENNReal.ofReal_one

/-- The strong one-milestone Stage-1.5 witness.  It has the same rate and timing
as `stage15KernelMilestone`, but its alive postcondition remembers the
`stage15Gate` facts needed to enter Stage 2. -/
noncomputable def stage15StrongKernelMilestone (n a₀ : ℕ) (hn2 : 2 ≤ n)
    (ha1 : 1 ≤ a₀) (ha_le : a₀ ≤ n - 1) :
    RoleSplitConcentration.KernelMilestone
      (GatedDrift.killK_now (NonuniformMajority L K).transitionKernel
        (stage15Gate (L := L) (K := K) n a₀)) where
  k := 1
  milestone _ := stage15StrongTerminal (L := L) (K := K) n a₀
  p _ := RoleSplitConcentration.floorRate n a₀ 1
  hp_pos _ := RoleSplitConcentration.floorRate_pos
    (n := n) (a₀ := a₀) (M := 1) hn2 (by omega) ha1
  hp_le_one _ := RoleSplitConcentration.floorRate_le_one
    (n := n) (a₀ := a₀) (M := 1) hn2 (by omega) ha_le
  milestone_monotone _ o o' hmono hsupp :=
    stage15StrongTerminal_monotone (L := L) (K := K) (n := n) (a₀ := a₀)
      o o' hmono hsupp
  progress i o h_prev h_not :=
    stage15StrongTerminal_progress (L := L) (K := K) hn2 ha_le i o h_prev h_not

theorem stage15StrongKernelMilestone_post_sound (n a₀ : ℕ) (hn2 : 2 ≤ n)
    (ha1 : 1 ≤ a₀) (ha_le : a₀ ≤ n - 1) (y : Config (AgentState L K)) :
    (stage15StrongKernelMilestone (L := L) (K := K) n a₀ hn2 ha1 ha_le).Post
        (some y) →
      y ∈ RoleSplitConcentration.noMCRCRPhase0Shell (L := L) (K := K) n := by
  intro hPost
  have hstrong :
      stage15StrongTerminal (L := L) (K := K) n a₀ (some y) :=
    hPost ⟨0, by simp [stage15StrongKernelMilestone]⟩
  exact stage15Gate_terminal_stage2ShellFacts (L := L) (K := K)
    hstrong.1 hstrong.2

theorem stage15StrongKernelMilestone_hPre_of_not_stage2Shell
    (n a₀ : ℕ) (hn2 : 2 ≤ n) (ha1 : 1 ≤ a₀) (ha_le : a₀ ≤ n - 1)
    {c₀ : Config (AgentState L K)}
    (_hg : c₀ ∈ stage15Gate (L := L) (K := K) n a₀)
    (hnot : ¬ c₀ ∈ RoleSplitConcentration.noMCRCRPhase0Shell (L := L) (K := K) n) :
    ∀ i : Fin (stage15StrongKernelMilestone
        (L := L) (K := K) n a₀ hn2 ha1 ha_le).k,
      ¬ (stage15StrongKernelMilestone
        (L := L) (K := K) n a₀ hn2 ha1 ha_le).milestone i (some c₀) := by
  intro i hi
  exact hnot (stage15Gate_terminal_stage2ShellFacts (L := L) (K := K) hi.1 hi.2)

/-- Strong Stage-1.5 `PhaseConvergenceW`: from `stage15Gate`, the chain reaches
the Stage-2 CR-drain shell with the same no-advance residual budget. -/
noncomputable def stage15W_to_stage2Shell_of_noAdvanceResidual
    (n a₀ : ℕ) (hn2 : 2 ≤ n) (ha1 : 1 ≤ a₀) (ha_le : a₀ ≤ n - 1)
    (ε : ℝ≥0)
    (w : ∀ c₀, c₀ ∈ stage15Gate (L := L) (K := K) n a₀ →
        Stage15NoAdvanceResidual (L := L) (K := K) n a₀ hn2 ha1 ha_le c₀ ε)
    (tt : ℕ)
    (htt : ∀ c₀ (hg : c₀ ∈ stage15Gate (L := L) (K := K) n a₀),
        (w c₀ hg).t = tt) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel where
  Pre c := c ∈ stage15Gate (L := L) (K := K) n a₀
  Post c := c ∈ RoleSplitConcentration.noMCRCRPhase0Shell (L := L) (K := K) n
  t := tt
  ε := ε
  convergence := by
    intro c₀ hg
    by_cases hshell : c₀ ∈ RoleSplitConcentration.noMCRCRPhase0Shell (L := L) (K := K) n
    · have hzero := RoleSplitConcentration.noMCRCRPhase0Shell_pow_compl_eq_zero
        (L := L) (K := K) c₀ hshell tt
      change ((NonuniformMajority L K).transitionKernel ^ tt) c₀
        (RoleSplitConcentration.noMCRCRPhase0Shell (L := L) (K := K) n)ᶜ ≤
          (ε : ℝ≥0∞)
      rw [hzero]
      exact zero_le'
    · set hw := w c₀ hg with hwdef
      have htStrong : hw.lam *
          (stage15StrongKernelMilestone (L := L) (K := K) n a₀ hn2 ha1 ha_le).meanTime ≤
          (hw.t : ℝ) := by
        simpa [stage15StrongKernelMilestone, stage15KernelMilestone] using hw.ht
      have hheadline := RoleSplitConcentration.real_bad_le_janson_add_escape
        (K := (NonuniformMajority L K).transitionKernel)
        (G := stage15Gate (L := L) (K := K) n a₀)
        (S := stage15NoAdvanceSet (L := L) (K := K) n a₀)
        (good := fun y =>
          y ∈ RoleSplitConcentration.noMCRCRPhase0Shell (L := L) (K := K) n)
        (q := hw.q)
        (stage15StrongKernelMilestone (L := L) (K := K) n a₀ hn2 ha1 ha_le)
        (NonuniformMajority L K)
        (stage15StrongKernelMilestone_post_sound
          (L := L) (K := K) n a₀ hn2 ha1 ha_le)
        (stage15Gate_hstep_of_floor_noadvance (L := L) (K := K) hw.hfloorStep)
        c₀ hw.hc₀
        (stage15StrongKernelMilestone_hPre_of_not_stage2Shell
          (L := L) (K := K) n a₀ hn2 ha1 ha_le hg hshell)
        hw.lam hw.hlam hw.t htStrong
      have hteq : hw.t = tt := by rw [hwdef]; exact htt c₀ hg
      rw [← hteq]
      exact le_trans hheadline (by
        simpa [stage15StrongKernelMilestone, stage15KernelMilestone] using hw.hbudget)

@[simp] theorem stage15W_to_stage2Shell_of_noAdvanceResidual_Post
    (n a₀ : ℕ) (hn2 : 2 ≤ n) (ha1 : 1 ≤ a₀) (ha_le : a₀ ≤ n - 1)
    (ε : ℝ≥0)
    (w : ∀ c₀, c₀ ∈ stage15Gate (L := L) (K := K) n a₀ →
        Stage15NoAdvanceResidual (L := L) (K := K) n a₀ hn2 ha1 ha_le c₀ ε)
    (tt : ℕ)
    (htt : ∀ c₀ (hg : c₀ ∈ stage15Gate (L := L) (K := K) n a₀),
        (w c₀ hg).t = tt) :
    (stage15W_to_stage2Shell_of_noAdvanceResidual (L := L) (K := K)
      n a₀ hn2 ha1 ha_le ε w tt htt).Post =
      fun c => c ∈ RoleSplitConcentration.noMCRCRPhase0Shell (L := L) (K := K) n := rfl

/-! ## Part 4 — `work⟨0⟩`, assembled via the landed three-stage CK composer.

Given the three supplied stage `PhaseConvergenceW` instances and the two chain links,
`EndpointWiring.roleSplitW_of_two_stage` packages the landed three-phase
Chapman–Kolmogorov composer `RoleSplitConcentration.phase0_roleSplit_whp_two_stage`
as a single `PhaseConvergenceW` — this IS `work⟨0⟩` (`Post = stage2.Post`,
`Pre = stage1.Pre`, `ε = ε₁ + ε₁·₅ + ε₂`).  Discharging `work⟨0⟩` is exactly
supplying these three stages; `stage1W_of_residual` is the recipe for stage 1 (and,
mutatis mutandis with the absorbing `noMCRShell` gate where the floor escape is
provably `0`, for stages 1.5 and 2). -/

/-- **`roleSplitWork0` — the discharged `work⟨0⟩`.**  The phase-0 role-split survival
`PhaseConvergenceW`, assembled from the three supplied stage instances and the two
chain links via the landed `roleSplitW_of_two_stage`.  `Post = stage2.Post` (the
role-split-good milestone / `RoleSplitStage2Good`-feeding postcondition),
`Pre = stage1.Pre`, budget `ε₁ + ε₁·₅ + ε₂`. -/
noncomputable def roleSplitWork0
    (stage1 stage15 stage2 :
      PhaseConvergenceW (NonuniformMajority L K).transitionKernel)
    (h_chain1 : ∀ x, stage1.Post x → stage15.Pre x)
    (h_chain2 : ∀ x, stage15.Post x → stage2.Pre x) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  EndpointWiring.roleSplitW_of_two_stage stage1 stage15 stage2 h_chain1 h_chain2

@[simp] theorem roleSplitWork0_Post
    (stage1 stage15 stage2 :
      PhaseConvergenceW (NonuniformMajority L K).transitionKernel)
    (h1 : ∀ x, stage1.Post x → stage15.Pre x)
    (h2 : ∀ x, stage15.Post x → stage2.Pre x) :
    (roleSplitWork0 stage1 stage15 stage2 h1 h2).Post = stage2.Post := rfl

@[simp] theorem roleSplitWork0_Pre
    (stage1 stage15 stage2 :
      PhaseConvergenceW (NonuniformMajority L K).transitionKernel)
    (h1 : ∀ x, stage1.Post x → stage15.Pre x)
    (h2 : ∀ x, stage15.Post x → stage2.Pre x) :
    (roleSplitWork0 stage1 stage15 stage2 h1 h2).Pre = stage1.Pre := rfl

/-! ## Part 5 — Stage 2 (`crCount` R4-drain): the εfloor is provably ZERO.

The structural advance of Stage 2 over Stages 1/1.5: on the gate
`noMCRShell n = {card = n ∧ roleMCRCount = 0}` NO rule produces an `RoleMCR`
(`Transition_roleMCRCount_noMCR_pair`), so the gate is genuinely ABSORBING and the
killed-kernel escape mass is identically ZERO
(`RoleSplitConcentration.noMCRShell_killedEscape_eq_zero`).  We re-export that
zero-escape fact here as the certificate that Stage 2 carries NO floor residual — its
only datum is the Janson hitting-time tail of the `crCount` milestone family. -/

/-- **Stage-2 zero-escape certificate (re-export).**  For any `c₀` in `noMCRShell n`
and any horizon `M`, the killed-kernel escape (cemetery) mass is `0`: the no-MCR gate
is absorbing, so the floor `εfloor` of Stage 2 is identically zero.  This is the
honest reason Stage 2 carries no Chernoff residual (unlike Stages 1/1.5). -/
theorem stage2_killedEscape_eq_zero {n : ℕ}
    (c₀ : Config (AgentState L K))
    (hc₀ : c₀ ∈ RoleSplitConcentration.noMCRShell (L := L) (K := K) n) (M : ℕ) :
    (GatedDrift.killK_now (NonuniformMajority L K).transitionKernel
        (RoleSplitConcentration.noMCRShell (L := L) (K := K) n) ^ M) (some c₀)
        {(none : Option (Config (AgentState L K)))} = 0 :=
  RoleSplitConcentration.noMCRShell_killedEscape_eq_zero (L := L) (K := K) c₀ hc₀ M

/-! ## Part 6 — refutation check: `RoleSplitGood` does NOT pin the floor.

The carried floor residual is genuine, not derivable from the role-split Post: a
`RoleSplitGood` config constrains only role COUNTS, carrying no information about the
`assignableCount` floor on the trajectory.  (This mirrors the anti-trap discipline:
the floor is not a bare-universal fact about role-good configs.)  We record the
structural witness that `RoleSplitGood` and the floor are independent: `RoleSplitGood`
is a property of role counts, the floor `a₀ ≤ assignableCount` is a property of the
transient pool — there is no implication. -/

/-- **Refutation: the floor is independent of `RoleSplitGood`.**  `RoleSplitGood`'s
defining conjuncts mention only `roleMCRCount`, `mainCount`, `clockCount`,
`reserveCount` — never `assignableCount`.  Hence no role-good fact forces the floor;
the floor residual is genuinely carried, not a hidden consequence of the Post.  We
witness this by the trivial observation that `RoleSplitGood` unfolds to a statement
with no `assignableCount` occurrence (so it cannot bound it). -/
theorem roleSplitGood_does_not_pin_floor
    {η : ℝ} {n : ℕ} {c : Config (AgentState L K)} :
    RoleSplitConcentration.RoleSplitGood (L := L) (K := K) η n c ↔
      (RoleSplitConcentration.roleMCRCount (L := L) (K := K) c = 0 ∧
        ((1 - η) * (n : ℝ) / 2 ≤ (RoleSplitConcentration.mainCount (L := L) (K := K) c : ℝ)) ∧
        ((RoleSplitConcentration.mainCount (L := L) (K := K) c : ℝ) ≤ (1 + η) * (n : ℝ) / 2) ∧
        ((1 - η) * (n : ℝ) / 4 ≤ (RoleSplitConcentration.clockCount (L := L) (K := K) c : ℝ)) ∧
        ((1 - η) * (n : ℝ) / 4 ≤ (RoleSplitConcentration.reserveCount (L := L) (K := K) c : ℝ))) :=
  Iff.rfl

/-! ## Part 7 — refutation guard for the old clock-survival regime inputs.

The current Stage-1.5 clock-survival constructor above still exposes the legacy
`Phase15ClockTailDepletion` interface.  Its `hcard` and `hcap` parameters are
universals over all configurations.  Those are not consequences of a phase-0
start; they are false statements globally.  The honest replacement has to use a
reachable/support-local clock-tail interface (`ClockTailNoSync` /
`ReachableClockTail`) instead of manufacturing these inputs from `Phase0Initial`.
-/

/-- The old `hcard` input to `stage15NoAdvanceResidual_of_floor_clock_survival`
is a false global statement: arbitrary configurations do not all have card `n`. -/
theorem stage15_clock_survival_hcard_not_universal
    (a : AgentState L K) (n : ℕ) (hn : n ≠ 3) :
    ¬ (∀ c : Config (AgentState L K), 2 ≤ c.card → c.card = n) := by
  intro hcard
  have hcard3 : (Multiset.replicate 3 a : Config (AgentState L K)).card = 3 := by
    simp
  have hbad := hcard (Multiset.replicate 3 a) (by rw [hcard3]; norm_num)
  rw [hcard3] at hbad
  exact hn hbad.symm

/-- The old per-clock `hcap` input is also false globally whenever the clock
index set is nonempty: a configuration can contain `m+1` copies of that state. -/
theorem stage15_clock_survival_hcap_not_universal
    {ι : Type*} (Clocks : Finset ι) (species : ι → AgentState L K)
    (m : ℕ) (j : ι) (hj : j ∈ Clocks) :
    ¬ (∀ j, j ∈ Clocks →
        ∀ c : Config (AgentState L K), c.count (species j) ≤ m) := by
  intro hcap
  have hbad := hcap j hj (Multiset.replicate (m + 1) (species j))
  rw [Config.count, Multiset.count_replicate_self] at hbad
  omega

/-! ## Axiom audit (verified by `#print axioms`). -/

#print axioms stage1FloorResidual_satisfiable
#print axioms stage1W_of_residual
#print axioms stage15Gate_terminal_stage2ShellFacts
#print axioms stage15Gate_of_roleSplitGoodMile
#print axioms noClockAtZero_compl_subset_clockPos_compl
#print axioms noClockAtZero_compl_subset_clockCounterPotential_ge_one
#print axioms phase0_noClockAtZero_fail_mass_le_clock_survival
#print axioms phase0_noClockAtZero_prefix_sum_range_le_clock_survival
#print axioms phase0_allPhase0_noadvance_le_clock_survival
#print axioms phase0_allPhase0_prefix_sum_le_clock_survival
#print axioms stage15Gate_hstep_of_floor_noadvance
#print axioms stage15NoAdvanceSet_escape_prefix_le_floor_clock_survival
#print axioms stage15Terminal_progress_mass
#print axioms stage15KernelMilestone
#print axioms stage15TimedResidual_satisfiable
#print axioms stage15W_of_timedResidual
#print axioms stage15NoAdvanceResidual_of_floor_clock_survival
#print axioms hdec_of_mgf_depletion_tail_reachable
#print axioms survival_union_bound_reachable
#print axioms reachable_hcover_of_global_hcover
#print axioms winN_fail_mass_le_mgf_clock_union_reachable
#print axioms clockPos_fail_mass_le_mgf_clock_union_reachable
#print axioms phase0_noClockAtZero_fail_mass_le_clock_survival_reachable
#print axioms phase0_noClockAtZero_prefix_sum_range_le_clock_survival_reachable
#print axioms phase0_allPhase0_noadvance_le_clock_survival_reachable
#print axioms phase0_allPhase0_prefix_sum_le_clock_survival_reachable
#print axioms stage15NoAdvanceSet_escape_prefix_le_floor_clock_survival_reachable
#print axioms stage15NoAdvanceResidual_of_floor_clock_survival_reachable
#print axioms ClockCounterDepthCover.counterDepth_hcover
#print axioms phase0_noClockAtZero_fail_mass_le_aggregate_depth
#print axioms phase0_noClockAtZero_prefix_sum_range_le_aggregate_depth
#print axioms phase0_allPhase0_noadvance_le_aggregate_depth
#print axioms phase0_allPhase0_prefix_sum_le_aggregate_depth
#print axioms stage15NoAdvanceSet_escape_prefix_le_floor_aggregate_depth
#print axioms stage15NoAdvanceResidual_of_floor_aggregate_depth
#print axioms phase0Initial_hcard_reach
#print axioms phase0Initial_hcap_reach_card
#print axioms stage15Gate_hcard_reach
#print axioms stage15Gate_hcap_reach_card
#print axioms stage15Gate_hcap_reach_card_family
#print axioms stage15NoAdvanceResidual_of_stage15Gate_clock_cap_reachable
#print axioms stage15NoAdvanceResidual_of_stage15Gate_card_cap_reachable
#print axioms stage15W_of_noAdvanceResidual
#print axioms stage15StrongKernelMilestone
#print axioms stage15W_to_stage2Shell_of_noAdvanceResidual
#print axioms roleSplitWork0
#print axioms roleSplitWork0_Post
#print axioms roleSplitWork0_Pre
#print axioms stage2_killedEscape_eq_zero
#print axioms roleSplitGood_does_not_pin_floor
#print axioms stage15_clock_survival_hcard_not_universal
#print axioms stage15_clock_survival_hcap_not_universal
#print axioms isMarkovKernel_pow

end Phase0RoleSplitDischarge
end ExactMajority
