/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Phase D-4 — the inter-phase advance-epidemic seams (`SeamEpidemics`)

`ChainBridges` PROVED that the ten `h_chain` bridges `Post_i ⟹ Pre_{i+1}` of
`TimeHeadline.time_headline_W` are **NOT** pointwise implications: every phase-window
predicate pins all agents to a single, distinct `phase.val`, so a populated config can never
simultaneously satisfy `Post_i` (all at `phase.val = i`) and `Pre_{i+1}` (all at `phase.val =
i+1`).  The bridge is the paper's inter-phase TRANSITION — the `advancePhase` EPIDEMIC — not a
predicate implication on a fixed `x`.

This file builds the honest reconciliation: a **seam phase** between each pair of work phases,
itself a `PhaseConvergenceW` whose `Pre` is the *trigger-form* tail of `work_i.Post` (some agent
already advanced) and whose `Post` is the next work phase's `≥`-window entry condition (all
agents advanced).  The mechanics are the protocol's universal phase epidemic: on EVERY
interaction both outputs take `max` of the two input phases (the public lemmas
`Invariants.Transition_left/right_phase_ge_pair_max`).  The Phase-4 instance
`Phase4Convergence.phase4Convergence` is EXACTLY this epidemic at `p = 4`
(`advancedU`-count drift, rate `m(n−m)/(n(n−1))`); the seam generalises it to a parameter `p`.

## The generic seam (the largest closed subset, delivered here)

`seamEpidemicW p n εepidemic εovershoot hDrift` : `PhaseConvergenceW K` with

* `Pre  c := c.card = n ∧ (∀ a ∈ c, p ≤ a.phase.val) ∧ 1 ≤ #{a ∈ c | p+1 ≤ a.phase.val}`
  — the trigger has fired (some agent is already at phase `≥ p+1`).
* `Post c := c.card = n ∧ (∀ a ∈ c, p+1 ≤ a.phase.val)` — the `≥`-window for the next phase.
* `t := tseam`, `ε := εepidemic + εovershoot`.
* `convergence` — threaded through TWO named feeders, mirroring the campaign's honest
  per-phase-drain pattern (no `sorry`, no smuggled `axiom`, no `native_decide`):
  - `hDrift` : the generic-`p` advance-epidemic convergence bound
        `(K^tseam) c {¬ allPhaseGe (p+1) n} ≤ εepidemic`
    — the parameter-`p` clone of `phase4AdvancedDrift` (drift count = `#{phase ≥ p+1}`,
    rate `m(n−m)/(n(n−1))`, spread by `Transition_*_phase_ge_pair_max`).  Discharging it =
    instantiating the Phase-4 OneSidedCancel engine at abstract `p` (the named GAP).
  - `εovershoot` budget : folded additively; the per-seam overshoot input
    `hNoOvershoot` (below) is what bounds `#{phase ≥ p+2} ≥ 1` at the seam end.

## The `≥`/exact-window reconciliation (`allPhaseEq` ⟺ `allPhaseGe (p+1) ∧ ¬ overshoot`)

A work phase whose `Pre` pins agents to an EXACT phase (`a.phase.val = p+1`) is recovered from
the seam's `≥`-`Post` by `allPhaseEq_of_ge_and_no_overshoot`: `(∀ a, p+1 ≤ phase) ∧
(∀ a, phase < p+2) ⟹ (∀ a, phase = p+1)`.  The "no overshoot" half — no agent has run ahead to
`phase ≥ p+2` during the seam — is the timing-separation event, named per seam as
`hNoOvershoot` and bounded (NOT discharged here) by the Phase0Window counter machinery (a
counter cannot finish too early).

## What is delivered vs. named-gap

DELIVERED (0-sorry, axiom-clean): the generic `seamEpidemicW` instance; the `≥`/exact-window
reconciliation lemma; the trigger/window helper lemmas; the corrected 21-instance composition
skeleton lives in `TimeHeadline` (`time_headline_W2`).
NAMED GAPS (carried as hypotheses, exact shapes recorded in the docstrings):
`hDrift` (generic-`p` epidemic drift), `hNoOvershoot` (per-seam timing separation).
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.PhaseConvergenceWeak
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.NonuniformMarkovChain
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.WindowConcentration
import Ripple.PopulationProtocol.Majority.ExactMajority.Analysis.Invariants

namespace ExactMajority
namespace SeamEpidemics

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-! ## The generic phase windows and the advance trigger -/

/-- The `≥`-window at phase `p`: fixed size `n`, every agent at phase `≥ p`.  This is the
parameter-`p` generalisation of `Phase4Convergence.Q4` (which is `allPhaseGe 4 n`). -/
def allPhaseGe (p n : ℕ) (c : Config (AgentState L K)) : Prop :=
  c.card = n ∧ ∀ a ∈ c, p ≤ a.phase.val

/-- The exact window at phase `p`: fixed size `n`, every agent at phase exactly `= p`.  This is
the shape the EXACT-pinning work `Pre`s carry (`Phase1AllMain`, `Q2`, `Phase6Win`, …). -/
def allPhaseEq (p n : ℕ) (c : Config (AgentState L K)) : Prop :=
  c.card = n ∧ ∀ a ∈ c, a.phase.val = p

/-- The advance trigger: at least one agent has already reached phase `≥ p`. -/
def advTriggered (p : ℕ) (c : Config (AgentState L K)) : Prop :=
  1 ≤ Multiset.countP (fun a => decide (p ≤ a.phase.val)) c

instance (p n : ℕ) (c : Config (AgentState L K)) : Decidable (allPhaseGe p n c) := by
  unfold allPhaseGe; infer_instance

instance (p n : ℕ) (c : Config (AgentState L K)) : Decidable (allPhaseEq p n c) := by
  unfold allPhaseEq; infer_instance

instance (p : ℕ) (c : Config (AgentState L K)) : Decidable (advTriggered p c) := by
  unfold advTriggered; infer_instance

/-! ## The `≥`/exact reconciliation -/

/-- **The honest `≥`-to-exact reconciliation.**  At the seam's end the population is in the
`≥ (p+1)`-window; the next work phase's EXACT `Pre` (`allPhaseEq (p+1)`) is recovered IFF no
agent has overshot to phase `≥ p+2`.  The "no overshoot" half is the named per-seam timing
event `hNoOvershoot`. -/
theorem allPhaseEq_of_ge_and_no_overshoot
    {p n : ℕ} {c : Config (AgentState L K)}
    (hge : allPhaseGe (L := L) (K := K) (p + 1) n c)
    (hno : ∀ a ∈ c, a.phase.val < p + 2) :
    allPhaseEq (L := L) (K := K) (p + 1) n c := by
  obtain ⟨hcard, hge'⟩ := hge
  refine ⟨hcard, ?_⟩
  intro a ha
  have h1 := hge' a ha
  have h2 := hno a ha
  omega

/-- Conversely, the exact window at `p+1` IS the `≥`-window at `p+1` (the trivial direction,
used when chaining a seam INTO an exact-pin work phase that we then keep as `≥`). -/
theorem allPhaseGe_of_allPhaseEq
    {p n : ℕ} {c : Config (AgentState L K)}
    (heq : allPhaseEq (L := L) (K := K) p n c) :
    allPhaseGe (L := L) (K := K) p n c := by
  obtain ⟨hcard, heq'⟩ := heq
  exact ⟨hcard, fun a ha => (heq' a ha).ge⟩

/-! ## The generic seam epidemic instance -/

/-- **The generic phase-advance epidemic seam** `seamEpidemicW`.

`Pre` = `≥ p`-window with the advance trigger fired (some agent at `≥ p+1`); `Post` =
`≥ (p+1)`-window.  The mechanics are the universal phase epidemic
(`Invariants.Transition_*_phase_ge_pair_max`): each interaction lifts both outputs to the
`max` of the two input phases, so the leading `≥ p+1` agent spreads phase `p+1` to the whole
population — the `advancedU`-count drift at abstract `p` (the Phase-4 instance is `p = 4`).

The `convergence` is threaded through the NAMED drift feeder `hDrift` (exact shape: the
generic-`p` epidemic convergence bound on the next `≥`-window), with the overshoot budget
`εovershoot` folded additively.  This is the campaign's honest per-phase-drain pattern: the
quantitative epidemic atom is supplied as a hypothesis, not re-opened here. -/
noncomputable def seamEpidemicW
    (p n tseam : ℕ) (εepidemic εovershoot : ℝ≥0)
    (hDrift : ∀ c : Config (AgentState L K),
        (allPhaseGe (L := L) (K := K) p n c ∧ advTriggered (L := L) (K := K) (p + 1) c) →
        ((NonuniformMajority L K).transitionKernel ^ tseam) c
            {c' | ¬ allPhaseGe (L := L) (K := K) (p + 1) n c'}
          ≤ (εepidemic : ℝ≥0∞)) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel where
  Pre := fun c =>
    allPhaseGe (L := L) (K := K) p n c ∧ advTriggered (L := L) (K := K) (p + 1) c
  Post := fun c => allPhaseGe (L := L) (K := K) (p + 1) n c
  t := tseam
  ε := εepidemic + εovershoot
  convergence := by
    intro c hPre
    calc ((NonuniformMajority L K).transitionKernel ^ tseam) c
            {c' | ¬ allPhaseGe (L := L) (K := K) (p + 1) n c'}
        ≤ (εepidemic : ℝ≥0∞) := hDrift c hPre
      _ ≤ ((εepidemic : ℝ≥0∞) + (εovershoot : ℝ≥0∞)) := le_self_add
      _ = ((εepidemic + εovershoot : ℝ≥0) : ℝ≥0∞) := by push_cast; rfl

@[simp] theorem seamEpidemicW_Pre
    (p n tseam : ℕ) (εepidemic εovershoot : ℝ≥0) (hDrift) (c : Config (AgentState L K)) :
    (seamEpidemicW (L := L) (K := K) p n tseam εepidemic εovershoot hDrift).Pre c
      = (allPhaseGe (L := L) (K := K) p n c ∧ advTriggered (L := L) (K := K) (p + 1) c) := rfl

@[simp] theorem seamEpidemicW_Post
    (p n tseam : ℕ) (εepidemic εovershoot : ℝ≥0) (hDrift) (c : Config (AgentState L K)) :
    (seamEpidemicW (L := L) (K := K) p n tseam εepidemic εovershoot hDrift).Post c
      = allPhaseGe (L := L) (K := K) (p + 1) n c := rfl

@[simp] theorem seamEpidemicW_t
    (p n tseam : ℕ) (εepidemic εovershoot : ℝ≥0) (hDrift) :
    (seamEpidemicW (L := L) (K := K) p n tseam εepidemic εovershoot hDrift).t = tseam := rfl

@[simp] theorem seamEpidemicW_eps
    (p n tseam : ℕ) (εepidemic εovershoot : ℝ≥0) (hDrift) :
    (seamEpidemicW (L := L) (K := K) p n tseam εepidemic εovershoot hDrift).ε
      = εepidemic + εovershoot := rfl

/-! ## The two per-seam bridge directions (work ↔ seam), as generic pointwise implications

These are the bridges `composeW_n_phases` consumes in the 21-instance interleave.  They are
GENUINE pointwise implications on populated configs — the phase-clash that refuted the
work↔work bridges (`ChainBridges`) does NOT arise, because the seam's `Pre`/`Post` are
`≥`-windows, not exact-pins.  Both are stated against the generic `allPhaseEq`/`allPhaseGe`
shapes; every concrete work window (`Phase1AllMain`, `Q2`, `Phase6Win`, `Phase5AllWin`, …)
reduces to `allPhaseEq i n ∧ (extra structural component)` and feeds these by projection. -/

/-- **Seam → exact-work bridge.**  The seam's `Post` (the `≥ (p+1)`-window) implies an
EXACT-pin work `Pre` (`allPhaseEq (p+1)`) under the named per-seam timing input `hno`
(no agent overshot to `≥ p+2`).  This is the reconciliation `≥` ⟹ `=` of
`allPhaseEq_of_ge_and_no_overshoot`, packaged as the bridge map.  The `≥`-window work phases
(only Phase 4 = `Q4 = allPhaseGe 4`) take `hge` directly with no overshoot input. -/
theorem seam_into_exact_work
    {p n : ℕ} (hno : ∀ c : Config (AgentState L K),
        allPhaseGe (L := L) (K := K) (p + 1) n c → ∀ a ∈ c, a.phase.val < p + 2) :
    ∀ c, allPhaseGe (L := L) (K := K) (p + 1) n c →
      allPhaseEq (L := L) (K := K) (p + 1) n c :=
  fun c hge => allPhaseEq_of_ge_and_no_overshoot hge (hno c hge)

/-- **Exact-work → seam bridge.**  An exact-pin work `Post` (all agents at phase `= p`) does
NOT by itself fire the advance trigger (`advTriggered (p+1)` requires some agent already at
`≥ p+1`); the trigger is the per-work-phase strengthening the campaign carries as a named
input.  Given the work `Post` `allPhaseEq p n` AND the trigger `advTriggered (p+1)`, the
seam's `Pre` (`allPhaseGe p n ∧ advTriggered (p+1)`) follows pointwise. -/
theorem exact_work_into_seam
    {p n : ℕ} (c : Config (AgentState L K))
    (hwork : allPhaseEq (L := L) (K := K) p n c)
    (htrig : advTriggered (L := L) (K := K) (p + 1) c) :
    allPhaseGe (L := L) (K := K) p n c ∧ advTriggered (L := L) (K := K) (p + 1) c :=
  ⟨allPhaseGe_of_allPhaseEq hwork, htrig⟩

/-- **`≥`-work → seam bridge.**  When the work `Post` is already a `≥`-window
(`allPhaseGe p n`, e.g. Phase 4's `Q4`), the seam `Pre` follows from it plus the trigger with
no `≥`-to-`=` step. -/
theorem ge_work_into_seam
    {p n : ℕ} (c : Config (AgentState L K))
    (hwork : allPhaseGe (L := L) (K := K) p n c)
    (htrig : advTriggered (L := L) (K := K) (p + 1) c) :
    allPhaseGe (L := L) (K := K) p n c ∧ advTriggered (L := L) (K := K) (p + 1) c :=
  ⟨hwork, htrig⟩

/-! ## The generic advance-epidemic ENGINE at abstract threshold `q = p+1`

This section discharges `hDrift(p)` — the first named D-4 gap — by cloning the
`Phase4Convergence` non-tie epidemic at an arbitrary phase parameter.  The
Phase-4 instance is `p = 4` (informed = `phase ≥ 5`); here informed is
`phase ≥ p+1` and the seam window is `allPhaseGe p n` (every agent at phase
`≥ p`).  The mechanics are the universal phase-`max` epidemic
(`Invariants.Transition_{left,right}_phase_ge_pair_max`).  All proofs mirror
`Phase4Convergence`'s Parts C–H verbatim with `advancedP` replaced by `geP q`. -/

instance instMeasurableSpaceAgentStateSeam : MeasurableSpace (AgentState L K) := ⊤
instance instDiscreteMeasurableSpaceAgentStateSeam :
    DiscreteMeasurableSpace (AgentState L K) where
  forall_measurableSet _ := trivial

/-- An agent is *informed at threshold `q`* if its phase is `≥ q`. -/
def geP (q : ℕ) (a : AgentState L K) : Prop := q ≤ a.phase.val

instance (q : ℕ) (a : AgentState L K) : Decidable (geP q a) := by
  unfold geP; infer_instance

/-- The informed-agent count at threshold `q` (phase `≥ q`). -/
def geCount (q : ℕ) (c : Config (AgentState L K)) : ℕ :=
  Multiset.countP (fun a => geP q a) c

/-- A *susceptible* agent in the seam window (phase exactly `p`, i.e. `≥ p` but
not `≥ p+1`). -/
def susP (p : ℕ) (a : AgentState L K) : Prop := a.phase.val = p

instance (p : ℕ) (a : AgentState L K) : Decidable (susP p a) := by
  unfold susP; infer_instance

private theorem mem_of_applicable_left_seam {c : Config (AgentState L K)}
    {r₁ r₂ : AgentState L K} (happ : Protocol.Applicable c r₁ r₂) : r₁ ∈ c :=
  Multiset.mem_of_le (happ : ({r₁, r₂} : Multiset _) ≤ c) (by simp)

private theorem mem_of_applicable_right_seam {c : Config (AgentState L K)}
    {r₁ r₂ : AgentState L K} (happ : Protocol.Applicable c r₁ r₂) : r₂ ∈ c :=
  Multiset.mem_of_le (happ : ({r₁, r₂} : Multiset _) ≤ c) (by simp)

private theorem applicable_of_mem_distinct_seam {c : Config (AgentState L K)}
    {x y : AgentState L K} (hx : x ∈ c) (hy : y ∈ c) (hxy : x ≠ y) :
    Protocol.Applicable c x y := by
  refine Multiset.le_iff_count.mpr ?_
  intro a
  rw [show ({x, y} : Multiset (AgentState L K)) = x ::ₘ y ::ₘ 0 from rfl,
      Multiset.count_cons, Multiset.count_cons, Multiset.count_zero]
  have hxc : 1 ≤ Multiset.count x c := Multiset.one_le_count_iff_mem.mpr hx
  have hyc : 1 ≤ Multiset.count y c := Multiset.one_le_count_iff_mem.mpr hy
  by_cases hax : a = x
  · subst hax
    have hay : ¬ a = y := fun h => hxy (h ▸ rfl)
    rw [if_pos rfl, if_neg hay]; omega
  · by_cases hay : a = y
    · subst hay; rw [if_neg hax, if_pos rfl]; omega
    · rw [if_neg hax, if_neg hay]; omega

/-- `countP (geP q)` over a two-element pair. -/
theorem countP_geP_pair (q : ℕ) (x y : AgentState L K) :
    Multiset.countP (fun a => geP q a) ({x, y} : Multiset (AgentState L K))
      = (if geP q x then 1 else 0) + (if geP q y then 1 else 0) := by
  rw [show ({x, y} : Multiset (AgentState L K)) = x ::ₘ y ::ₘ 0 from rfl]
  rw [Multiset.countP_cons, Multiset.countP_cons, Multiset.countP_zero]
  ring

/-- **Per-pair informed-count monotonicity.**  Phase only rises under
`Transition`, and `geP q` is upward-closed in phase, so the informed count of the
produced pair is at least that of the consumed pair. -/
theorem geP_pair_mono (q : ℕ) (s t : AgentState L K) :
    Multiset.countP (fun a => geP q a) ({s, t} : Multiset (AgentState L K))
      ≤ Multiset.countP (fun a => geP q a)
          ({(Transition L K s t).1, (Transition L K s t).2}
            : Multiset (AgentState L K)) := by
  have hmono := Transition_phase_monotone (L := L) (K := K) s t
  simp only [] at hmono
  obtain ⟨hsm, htm⟩ := hmono
  rw [countP_geP_pair, countP_geP_pair]
  have hs' : geP q s → geP q (Transition L K s t).1 := fun h => le_trans h hsm
  have ht' : geP q t → geP q (Transition L K s t).2 := fun h => le_trans h htm
  by_cases hsa : geP q s
  · by_cases hta : geP q t
    · rw [if_pos hsa, if_pos hta, if_pos (hs' hsa), if_pos (ht' hta)]
    · rw [if_pos hsa, if_neg hta, if_pos (hs' hsa)]; split_ifs <;> omega
  · by_cases hta : geP q t
    · rw [if_neg hsa, if_pos hta, if_pos (ht' hta)]; split_ifs <;> omega
    · rw [if_neg hsa, if_neg hta]; omega

/-- **Per-pair advance.**  A mixed pair — one informed (`phase ≥ q`), one in the
seam window (`phase ≥ p`, with `p+1 = q`) but not informed — produces two informed
agents, since both `Transition` outputs have phase `≥ max(s,t) ≥ q`. -/
theorem geP_pair_advances (p : ℕ) (s t : AgentState L K)
    (_hsp : p ≤ s.phase.val) (_htp : p ≤ t.phase.val)
    (hmixed : (geP (L := L) (K := K) (p + 1) s ∧ ¬ geP (L := L) (K := K) (p + 1) t) ∨
              (¬ geP (L := L) (K := K) (p + 1) s ∧ geP (L := L) (K := K) (p + 1) t)) :
    Multiset.countP (fun a => geP (p + 1) a) ({s, t} : Multiset (AgentState L K)) + 1
      ≤ Multiset.countP (fun a => geP (p + 1) a)
          ({(Transition L K s t).1, (Transition L K s t).2}
            : Multiset (AgentState L K)) := by
  have hmaxq : p + 1 ≤ max s.phase.val t.phase.val := by
    rcases hmixed with ⟨hsa, _⟩ | ⟨_, hta⟩
    · exact le_trans hsa (le_max_left _ _)
    · exact le_trans hta (le_max_right _ _)
  have hout1 : geP (L := L) (K := K) (p + 1) (Transition L K s t).1 :=
    le_trans hmaxq (Transition_left_phase_ge_pair_max (L := L) (K := K) s t)
  have hout2 : geP (L := L) (K := K) (p + 1) (Transition L K s t).2 :=
    le_trans hmaxq (Transition_right_phase_ge_pair_max (L := L) (K := K) s t)
  rw [countP_geP_pair, countP_geP_pair, if_pos hout1, if_pos hout2]
  rcases hmixed with ⟨hsa, hta⟩ | ⟨hsa, hta⟩
  · rw [if_pos hsa, if_neg hta]
  · rw [if_neg hsa, if_pos hta]

/-- `geCount q` is non-decreasing under any chosen-pair update. -/
theorem geCount_stepOrSelf_ge (q : ℕ) (c : Config (AgentState L K))
    (r₁ r₂ : AgentState L K) :
    geCount (L := L) (K := K) q c
      ≤ geCount (L := L) (K := K) q
          (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂) := by
  by_cases happ : Protocol.Applicable c r₁ r₂
  · have hsub : ({r₁, r₂} : Multiset (AgentState L K)) ≤ c := happ
    have hc' : Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂
        = c - {r₁, r₂} + {(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2} := by
      unfold Protocol.stepOrSelf; rw [if_pos happ]; rfl
    unfold geCount
    rw [hc', Multiset.countP_add, Multiset.countP_sub hsub]
    have hpair_le : Multiset.countP (fun a => geP q a)
        ({r₁, r₂} : Multiset (AgentState L K))
          ≤ Multiset.countP (fun a => geP q a) c := Multiset.countP_le_of_le _ hsub
    have hmono := geP_pair_mono (L := L) (K := K) q r₁ r₂
    omega
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]

/-- `geCount q` is preserved-or-raised on the one-step kernel support. -/
theorem geCount_ge_monotone (q m : ℕ) (c c' : Config (AgentState L K))
    (h : m ≤ geCount (L := L) (K := K) q c)
    (hc' : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    m ≤ geCount (L := L) (K := K) q c' := by
  by_cases hc : 2 ≤ c.card
  · rw [show (NonuniformMajority L K).stepDistOrSelf c = (NonuniformMajority L K).stepDist c hc by
        unfold Protocol.stepDistOrSelf; rw [dif_pos hc]] at hc'
    obtain ⟨⟨r₁, r₂⟩, hr⟩ := Protocol.stepDist_support (NonuniformMajority L K) c hc c' hc'
    rw [← hr]
    exact le_trans h (geCount_stepOrSelf_ge q c r₁ r₂)
  · rw [show (NonuniformMajority L K).stepDistOrSelf c = PMF.pure c by
        unfold Protocol.stepDistOrSelf; rw [dif_neg hc]] at hc'
    rw [PMF.mem_support_pure_iff] at hc'
    subst hc'; exact h

/-- A scheduled (informed, susceptible) pair raises the GLOBAL informed count
`geCount (p+1)` by one. -/
theorem geCount_stepOrSelf_advance (p : ℕ) (c : Config (AgentState L K))
    (s t : AgentState L K) (happ : Protocol.Applicable c s t)
    (hsp : p ≤ s.phase.val) (htp : p ≤ t.phase.val)
    (hmixed : (geP (L := L) (K := K) (p + 1) s ∧ ¬ geP (L := L) (K := K) (p + 1) t) ∨
              (¬ geP (L := L) (K := K) (p + 1) s ∧ geP (L := L) (K := K) (p + 1) t)) :
    geCount (L := L) (K := K) (p + 1) c + 1
      ≤ geCount (L := L) (K := K) (p + 1)
          (Protocol.stepOrSelf (NonuniformMajority L K) c s t) := by
  have hsub : ({s, t} : Multiset (AgentState L K)) ≤ c := happ
  have hc' : Protocol.stepOrSelf (NonuniformMajority L K) c s t
      = c - {s, t} + {(Transition L K s t).1, (Transition L K s t).2} := by
    unfold Protocol.stepOrSelf; rw [if_pos happ]; rfl
  unfold geCount
  rw [hc', Multiset.countP_add, Multiset.countP_sub hsub]
  have hpair_le : Multiset.countP (fun a => geP (p + 1) a) ({s, t} : Multiset (AgentState L K))
      ≤ Multiset.countP (fun a => geP (p + 1) a) c := Multiset.countP_le_of_le _ hsub
  have hadv := geP_pair_advances (L := L) (K := K) p s t hsp htp hmixed
  omega

/-- **The generic rectangle → advance-probability bound.**  Mirrors
`Phase4Convergence.advanced_advance_prob_of_rect` with `geCount (p+1)` as the
advancing quantity. -/
theorem advance_prob_of_rect (p n : ℕ) (hn : 2 ≤ n)
    (c : Config (AgentState L K)) (hcardn : c.card = n)
    (R : Finset (AgentState L K × AgentState L K)) (N : ℕ)
    (hadv : ∀ pr ∈ R, 1 ≤ c.count pr.1 → 1 ≤ c.count pr.2 →
      (pr.1 = pr.2 → 2 ≤ c.count pr.1) →
      geCount (L := L) (K := K) (p + 1) c + 1
        ≤ geCount (L := L) (K := K) (p + 1)
            (Protocol.stepOrSelf (NonuniformMajority L K) c pr.1 pr.2))
    (hcount : (N : ℕ) ≤ ∑ pr ∈ R, c.interactionCount pr.1 pr.2) :
    ENNReal.ofReal ((N : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) ≤
      ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
        {c' | geCount (L := L) (K := K) (p + 1) c + 1
                ≤ geCount (L := L) (K := K) (p + 1) c'} := by
  set j := geCount (L := L) (K := K) (p + 1) c with hjdef
  have hcard2 : 2 ≤ c.card := by rw [hcardn]; omega
  have hmeas : MeasurableSet {c' : Config (AgentState L K) | j + 1 ≤ geCount (p + 1) c'} :=
    DiscreteMeasurableSpace.forall_measurableSet _
  set S : Finset (AgentState L K × AgentState L K) :=
    R.filter (fun pr => 1 ≤ c.count pr.1 ∧ 1 ≤ c.count pr.2 ∧
      (pr.1 = pr.2 → 2 ≤ c.count pr.1)) with hS
  have hsub : (↑S : Set (AgentState L K × AgentState L K)) ⊆
      (Protocol.scheduledStep (NonuniformMajority L K) c) ⁻¹'
        {c' | j + 1 ≤ geCount (p + 1) c'} := by
    intro pr hp
    simp only [Finset.coe_filter, Set.mem_setOf_eq, hS] at hp
    obtain ⟨hpc, hp1, hp2, hp3⟩ := hp
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Protocol.scheduledStep]
    exact hadv pr hpc hp1 hp2 hp3
  have hstepDist : (NonuniformMajority L K).stepDistOrSelf c
      = (NonuniformMajority L K).stepDist c hcard2 := by
    unfold Protocol.stepDistOrSelf; rw [dif_pos hcard2]
  have hbase : ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
        {c' | j + 1 ≤ geCount (p + 1) c'}
      = (c.interactionPMF hcard2).toMeasure
          ((Protocol.scheduledStep (NonuniformMajority L K) c) ⁻¹'
            {c' | j + 1 ≤ geCount (p + 1) c'}) := by
    rw [hstepDist]; unfold Protocol.stepDist
    rw [PMF.toMeasure_map_apply _ _ _ (Measurable.of_discrete) hmeas]
  rw [hbase]
  have hmono : (c.interactionPMF hcard2).toMeasure (↑S : Set _)
      ≤ (c.interactionPMF hcard2).toMeasure
          ((Protocol.scheduledStep (NonuniformMajority L K) c) ⁻¹'
            {c' | j + 1 ≤ geCount (p + 1) c'}) :=
    measure_mono hsub
  refine le_trans ?_ hmono
  have hSmeasure : (c.interactionPMF hcard2).toMeasure (↑S : Set _)
      = ∑ pr ∈ S, c.interactionProb pr.1 pr.2 := by
    rw [PMF.toMeasure_apply_finset]; rfl
  have hSsum : ∑ pr ∈ S, c.interactionProb pr.1 pr.2
      = ∑ pr ∈ R, c.interactionProb pr.1 pr.2 := by
    rw [hS]
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro pr hpc hpnot
    rw [Finset.mem_filter] at hpnot
    push Not at hpnot
    have hexcl := hpnot hpc
    have hzero : c.interactionCount pr.1 pr.2 = 0 := by
      unfold Config.interactionCount
      by_cases h1 : 1 ≤ c.count pr.1
      · by_cases h2 : 1 ≤ c.count pr.2
        · obtain ⟨hpe, hlt⟩ := hexcl h1 h2
          rw [if_pos hpe]
          have hc1 : c.count pr.1 = 1 := by omega
          rw [hc1]
        · have hz2 : c.count pr.2 = 0 := by omega
          by_cases hpe : pr.1 = pr.2
          · rw [if_pos hpe]; rw [hpe, hz2, Nat.zero_mul]
          · rw [if_neg hpe, hz2, Nat.mul_zero]
      · have hz1 : c.count pr.1 = 0 := by omega
        by_cases hpe : pr.1 = pr.2
        · rw [if_pos hpe, hz1, Nat.zero_mul]
        · rw [if_neg hpe, hz1, Nat.zero_mul]
    unfold Config.interactionProb; rw [hzero]; simp
  rw [hSmeasure, hSsum]
  have heqterm : ∀ pr : AgentState L K × AgentState L K,
      c.interactionProb pr.1 pr.2
        = (↑(c.interactionCount pr.1 pr.2) : ℝ≥0∞) * (↑c.totalPairs)⁻¹ := by
    intro pr; unfold Config.interactionProb; rw [div_eq_mul_inv]
  rw [Finset.sum_congr rfl (fun pr _ => heqterm pr), ← Finset.sum_mul, ← Nat.cast_sum]
  set M := ∑ pr ∈ R, c.interactionCount pr.1 pr.2 with hM
  have htp : c.totalPairs = n * (n - 1) := by rw [Config.totalPairs, hcardn]
  rw [htp, ← div_eq_mul_inv]
  have hden_pos : (0 : ℝ) < ((n * (n - 1) : ℕ) : ℝ) := by
    have : 0 < n * (n - 1) := Nat.mul_pos (by omega) (by omega)
    exact_mod_cast this
  have hdenR : ((n * (n - 1) : ℕ) : ℝ) = (n : ℝ) * ((n : ℝ) - 1) := by
    rw [Nat.cast_mul, Nat.cast_sub (by omega)]; push_cast; ring
  have hstep1 : ENNReal.ofReal ((N : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)))
      ≤ ENNReal.ofReal (((M : ℕ) : ℝ) / ((n * (n - 1) : ℕ) : ℝ)) := by
    apply ENNReal.ofReal_le_ofReal
    rw [hdenR]
    have hNM : (N : ℝ) ≤ (M : ℝ) := by exact_mod_cast hcount
    have hposden : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := by rw [← hdenR]; exact hden_pos
    gcongr
  refine le_trans hstep1 ?_
  rw [← ENNReal.ofReal_natCast M, ← ENNReal.ofReal_natCast (n * (n - 1)),
      ← ENNReal.ofReal_div_of_pos hden_pos]

/-! ## The informed×susceptible rectangle on the seam window `allPhaseGe p n`. -/

/-- For two state-finsets `A`, `B` of pairwise-distinct states, the
`interactionCount` mass of `A ×ˢ B` is `(∑_A count)·(∑_B count)`. -/
theorem sum_interactionCount_cross_disjoint_seam
    (c : Config (AgentState L K)) (A B : Finset (AgentState L K))
    (hdisj : ∀ a ∈ A, ∀ b ∈ B, a ≠ b) :
    (∑ pr ∈ A ×ˢ B, c.interactionCount pr.1 pr.2)
      = (∑ a ∈ A, c.count a) * (∑ b ∈ B, c.count b) := by
  rw [Finset.sum_product, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  unfold Config.interactionCount
  rw [if_neg (hdisj a ha b hb)]

/-- `∑ count` over the informed STATES equals `geCount q c`. -/
theorem sum_count_geP (q : ℕ) (c : Config (AgentState L K)) :
    (∑ a ∈ Finset.univ.filter (fun a : AgentState L K => geP q a), c.count a)
      = geCount (L := L) (K := K) q c := by
  have hcard : (Multiset.filter (fun a : AgentState L K => geP q a) c).card
      = geCount (L := L) (K := K) q c := by
    unfold geCount; rw [Multiset.countP_eq_card_filter]
  rw [← hcard]
  have hcount_eq : ∀ a ∈ Finset.univ.filter (fun a : AgentState L K => geP q a),
      c.count a
        = Multiset.count a (Multiset.filter (fun a : AgentState L K => geP q a) c) := by
    intro a ha
    rw [Finset.mem_filter] at ha
    rw [Config.count, Multiset.count_filter, if_pos ha.2]
  rw [Finset.sum_congr rfl hcount_eq, Multiset.sum_count_eq_card]
  intro a ha
  rw [Multiset.mem_filter] at ha
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha.2⟩

/-- `∑ count` over the susceptible STATES equals `countP (susP p) c`. -/
theorem sum_count_susP (p : ℕ) (c : Config (AgentState L K)) :
    (∑ a ∈ Finset.univ.filter (fun a : AgentState L K => susP p a), c.count a)
      = Multiset.countP (fun a => susP p a) c := by
  have hcard : (Multiset.filter (fun a : AgentState L K => susP p a) c).card
      = Multiset.countP (fun a => susP p a) c := by
    rw [Multiset.countP_eq_card_filter]
  rw [← hcard]
  have hcount_eq : ∀ a ∈ Finset.univ.filter (fun a : AgentState L K => susP p a),
      c.count a
        = Multiset.count a (Multiset.filter (fun a : AgentState L K => susP p a) c) := by
    intro a ha
    rw [Finset.mem_filter] at ha
    rw [Config.count, Multiset.count_filter, if_pos ha.2]
  rw [Finset.sum_congr rfl hcount_eq, Multiset.sum_count_eq_card]
  intro a ha
  rw [Multiset.mem_filter] at ha
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha.2⟩

/-- On the window `allPhaseGe p n`, every agent is informed (`phase ≥ p+1`) XOR
susceptible (`phase = p`), so `geCount (p+1) + #susP = n`.  Hence the susceptible
count is `n − geCount (p+1)`. -/
theorem susP_count_eq (p n : ℕ) (c : Config (AgentState L K))
    (hw : allPhaseGe (L := L) (K := K) p n c) :
    Multiset.countP (fun a => susP p a) c = n - geCount (L := L) (K := K) (p + 1) c := by
  unfold geCount
  have hsplit : Multiset.countP (fun a => geP (p + 1) a) c
      + Multiset.countP (fun a => susP p a) c = c.card := by
    rw [Multiset.countP_eq_card_filter, Multiset.countP_eq_card_filter, ← Multiset.card_add]
    congr 1
    refine Multiset.ext.mpr ?_
    intro a
    rw [Multiset.count_add, Multiset.count_filter, Multiset.count_filter]
    by_cases hmem : a ∈ c
    · have hpp := hw.2 a hmem
      by_cases hge : geP (L := L) (K := K) (p + 1) a
      · have hnsus : ¬ susP (L := L) (K := K) p a := by
          simp only [geP, susP] at hge ⊢; omega
        rw [if_pos hge, if_neg hnsus]; omega
      · have hsus : susP (L := L) (K := K) p a := by
          simp only [geP, susP] at hge ⊢; omega
        rw [if_neg hge, if_pos hsus]; omega
    · have h0 : Multiset.count a c = 0 := Multiset.count_eq_zero.mpr hmem
      rw [h0]; simp
  rw [hw.1] at hsplit
  omega

/-- The informed×susceptible rectangle `interactionCount` mass is `m·(n−m)`,
`m = geCount (p+1) c` (cross pairs distinct: informed `phase ≥ p+1`, susceptible
`phase = p`). -/
theorem sum_interactionCount_syncRect_seam (p n : ℕ) (c : Config (AgentState L K))
    (hw : allPhaseGe (L := L) (K := K) p n c) :
    (∑ pr ∈ (Finset.univ.filter (fun a : AgentState L K => geP (p + 1) a)) ×ˢ
        (Finset.univ.filter (fun a : AgentState L K => susP p a)),
        c.interactionCount pr.1 pr.2)
      = geCount (L := L) (K := K) (p + 1) c
          * (n - geCount (L := L) (K := K) (p + 1) c) := by
  rw [sum_interactionCount_cross_disjoint_seam c _ _ ?_, sum_count_geP,
      sum_count_susP, susP_count_eq p n c hw]
  intro a ha b hb
  rw [Finset.mem_filter] at ha hb
  intro hab
  have haA : geP (L := L) (K := K) (p + 1) a := ha.2
  have hbS : susP (L := L) (K := K) p b := hb.2
  rw [hab] at haA
  simp only [geP, susP] at haA hbS; omega

/-- **The SYNC informed-advance probability (DERIVED).**  On `allPhaseGe p n` with
`n ≥ 2`, one step raises `geCount (p+1)` by `≥ 1` with probability
`≥ m·(n−m)/(n(n−1))`, `m = geCount (p+1) c`. -/
theorem ge_advance_prob (p n : ℕ) (hn : 2 ≤ n)
    (c : Config (AgentState L K)) (hw : allPhaseGe (L := L) (K := K) p n c) :
    ENNReal.ofReal
        (((geCount (L := L) (K := K) (p + 1) c
            * (n - geCount (L := L) (K := K) (p + 1) c) : ℕ) : ℝ)
          / ((n : ℝ) * ((n : ℝ) - 1))) ≤
      ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
        {c' | geCount (L := L) (K := K) (p + 1) c + 1
                ≤ geCount (L := L) (K := K) (p + 1) c'} := by
  set R := (Finset.univ.filter (fun a : AgentState L K => geP (p + 1) a)) ×ˢ
    (Finset.univ.filter (fun a : AgentState L K => susP p a)) with hR
  set m := geCount (L := L) (K := K) (p + 1) c with hmdef
  have hcount : m * (n - m) ≤ ∑ pr ∈ R, c.interactionCount pr.1 pr.2 := by
    rw [hR, sum_interactionCount_syncRect_seam p n c hw]
  refine advance_prob_of_rect p n hn c hw.1 R (m * (n - m)) ?_ hcount
  · rintro ⟨a, b⟩ hp h1 h2 _hsame
    rw [hR, Finset.mem_product, Finset.mem_filter, Finset.mem_filter] at hp
    obtain ⟨⟨_, haA⟩, ⟨_, hbS⟩⟩ := hp
    have haadv : geP (L := L) (K := K) (p + 1) a := haA
    have hbsus : susP (L := L) (K := K) p b := hbS
    have hap : p ≤ a.phase.val := by simp only [geP] at haadv; omega
    have hbp : p ≤ b.phase.val := by simp only [susP] at hbsus; omega
    have hbnadv : ¬ geP (L := L) (K := K) (p + 1) b := by
      simp only [geP, susP] at hbsus ⊢; omega
    have hamem : a ∈ c := Multiset.one_le_count_iff_mem.mp h1
    have hbmem : b ∈ c := Multiset.one_le_count_iff_mem.mp h2
    have hab : a ≠ b := by intro h; rw [h] at haadv; exact hbnadv haadv
    have happ : Protocol.Applicable c a b := applicable_of_mem_distinct_seam hamem hbmem hab
    exact geCount_stepOrSelf_advance p c a b happ hap hbp (Or.inl ⟨haadv, hbnadv⟩)

/-! ## The window `allPhaseGe p n` is one-step closed; the deficit potential. -/

/-- `allPhaseGe p n` is preserved by a single chosen-pair update (phase only
rises, card preserved). -/
theorem allPhaseGe_stepOrSelf (p n : ℕ) (c : Config (AgentState L K))
    (hw : allPhaseGe (L := L) (K := K) p n c) (r₁ r₂ : AgentState L K) :
    allPhaseGe (L := L) (K := K) p n
      (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂) := by
  by_cases happ : Protocol.Applicable c r₁ r₂
  · have hmem1 := mem_of_applicable_left_seam happ
    have hmem2 := mem_of_applicable_right_seam happ
    have h1p := hw.2 r₁ hmem1
    have h2p := hw.2 r₂ hmem2
    have hc' : Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂
        = c - {r₁, r₂} + {(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2} := by
      unfold Protocol.stepOrSelf; rw [if_pos happ]; rfl
    have hmono := Transition_phase_monotone (L := L) (K := K) r₁ r₂
    simp only [] at hmono
    obtain ⟨hsm, htm⟩ := hmono
    refine ⟨?_, ?_⟩
    · have hcard := Protocol.reachable_card_eq
        (Protocol.reachable_stepOrSelf (P := NonuniformMajority L K) c r₁ r₂)
      rw [hcard]; exact hw.1
    · intro a ha
      rw [hc'] at ha
      rcases Multiset.mem_add.mp ha with hold | hnew
      · exact hw.2 a (Multiset.mem_of_le (Multiset.sub_le_self _ _) hold)
      · rw [show ({(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2}
              : Multiset (AgentState L K))
            = (Transition L K r₁ r₂).1 ::ₘ (Transition L K r₁ r₂).2 ::ₘ 0 from rfl] at hnew
        simp only [Multiset.mem_cons, Multiset.notMem_zero, or_false] at hnew
        rcases hnew with h | h
        · subst h; exact le_trans h1p hsm
        · subst h; exact le_trans h2p htm
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]; exact hw

/-- `allPhaseGe p n` is one-step-support closed. -/
theorem allPhaseGe_absorbing (p n : ℕ) (c c' : Config (AgentState L K))
    (hw : allPhaseGe (L := L) (K := K) p n c)
    (hc' : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    allPhaseGe (L := L) (K := K) p n c' := by
  by_cases hc : 2 ≤ c.card
  · rw [show (NonuniformMajority L K).stepDistOrSelf c = (NonuniformMajority L K).stepDist c hc by
        unfold Protocol.stepDistOrSelf; rw [dif_pos hc]] at hc'
    obtain ⟨⟨r₁, r₂⟩, hr⟩ := Protocol.stepDist_support (NonuniformMajority L K) c hc c' hc'
    rw [← hr]
    exact allPhaseGe_stepOrSelf p n c hw r₁ r₂
  · rw [show (NonuniformMajority L K).stepDistOrSelf c = PMF.pure c by
        unfold Protocol.stepDistOrSelf; rw [dif_neg hc]] at hc'
    rw [PMF.mem_support_pure_iff] at hc'
    subst hc'; exact hw

/-- "Finished": all `n` agents are informed (`phase ≥ p+1`). -/
def geFinished (p n : ℕ) (c : Config (AgentState L K)) : Prop :=
  n ≤ geCount (L := L) (K := K) (p + 1) c

instance (p n : ℕ) (c : Config (AgentState L K)) : Decidable (geFinished p n c) := by
  unfold geFinished; infer_instance

/-- On the card-`n` window, "finished" (`geCount (p+1) ≥ n`) coincides with the
seam `Post` `allPhaseGe (p+1) n`.  This is the bridge from the count engine to the
`hDrift` target set. -/
theorem allPhaseGe_succ_iff_geFinished (p n : ℕ) (c : Config (AgentState L K))
    (hcard : c.card = n) :
    allPhaseGe (L := L) (K := K) (p + 1) n c ↔ geFinished (L := L) (K := K) p n c := by
  unfold geFinished geCount
  constructor
  · rintro ⟨hc, hge⟩
    rw [Multiset.countP_eq_card_filter]
    rw [show Multiset.filter (fun a => geP (L := L) (K := K) (p + 1) a) c = c from ?_]
    · rw [hc]
    · refine Multiset.filter_eq_self.mpr ?_
      intro a ha; exact hge a ha
  · intro hfin
    refine ⟨hcard, ?_⟩
    intro a ha
    -- countP ≥ n = card forces every agent informed
    by_contra hcon
    have hlt : Multiset.countP (fun a => geP (L := L) (K := K) (p + 1) a) c < c.card := by
      have hle : Multiset.countP (fun a => geP (L := L) (K := K) (p + 1) a) c ≤ c.card :=
        Multiset.countP_le_card _ _
      rcases lt_or_eq_of_le hle with h | h
      · exact h
      · exfalso
        have hall : ∀ b ∈ c, geP (L := L) (K := K) (p + 1) b := by
          rw [Multiset.countP_eq_card_filter] at h
          have hfeq : Multiset.filter (fun b => geP (L := L) (K := K) (p + 1) b) c = c :=
            Multiset.eq_of_le_of_card_le (Multiset.filter_le _ _) (le_of_eq h.symm)
          intro b hb
          have : b ∈ Multiset.filter (fun b => geP (L := L) (K := K) (p + 1) b) c := by
            rw [hfeq]; exact hb
          exact (Multiset.mem_filter.mp this).2
        exact hcon (by simpa [geP] using hall a ha)
    rw [hcard] at hlt; omega

/-- The clamped informed count `min (geCount (p+1) c) n`. -/
def gClamp (p n : ℕ) (c : Config (AgentState L K)) : ℕ :=
  min (geCount (L := L) (K := K) (p + 1) c) n

theorem geFinished_absorbing (p n : ℕ) (c c' : Config (AgentState L K))
    (hfin : geFinished (L := L) (K := K) p n c)
    (hc' : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    geFinished (L := L) (K := K) p n c' := by
  unfold geFinished at hfin ⊢
  exact geCount_ge_monotone (p + 1) n c c' hfin hc'

/-- The exponential-window deficit potential at threshold `p+1`: `0` when
finished, else `ofReal(exp(s·(n − gClamp)))`. -/
noncomputable def gDeficitPot (p n : ℕ) (s : ℝ) (c : Config (AgentState L K)) : ℝ≥0∞ :=
  if geFinished (L := L) (K := K) p n c then 0
  else ENNReal.ofReal (Real.exp (s * ((n : ℝ) - (gClamp (L := L) (K := K) p n c : ℝ))))

theorem gDeficitPot_measurable (p n : ℕ) (s : ℝ) :
    Measurable (gDeficitPot p n s (L := L) (K := K)) :=
  Measurable.of_discrete

theorem gDeficitPot_eq_of_lt (p n : ℕ) (s : ℝ) (c : Config (AgentState L K))
    (hlt : geCount (L := L) (K := K) (p + 1) c < n) :
    gDeficitPot p n s c
      = ENNReal.ofReal
          (Real.exp (s * ((n : ℝ) - (geCount (L := L) (K := K) (p + 1) c : ℝ)))) := by
  unfold gDeficitPot geFinished gClamp
  rw [if_neg (by omega)]
  congr 2
  rw [min_eq_left (le_of_lt hlt)]

theorem not_finished_imp_gDeficitPot_ge_one (p n : ℕ) (s : ℝ) (hs : 0 < s)
    (c : Config (AgentState L K)) (hc : ¬ geFinished (L := L) (K := K) p n c) :
    (1 : ℝ≥0∞) ≤ gDeficitPot p n s c := by
  have hlt : geCount (L := L) (K := K) (p + 1) c < n := by unfold geFinished at hc; omega
  rw [gDeficitPot_eq_of_lt p n s c hlt]
  rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm]
  apply ENNReal.ofReal_le_ofReal
  rw [show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]
  apply Real.exp_le_exp.mpr
  have hdef : (1 : ℝ) ≤ (n : ℝ) - (geCount (L := L) (K := K) (p + 1) c : ℝ) := by
    have : (geCount (L := L) (K := K) (p + 1) c : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hlt
    linarith
  nlinarith [hs, hdef]

/-- Pointwise one-step bound on the deficit potential, using the PROVEN
monotonicity `geCount_ge_monotone`. -/
theorem gDeficitPot_pointwise_bound (p n : ℕ) (s : ℝ) (hs : 0 < s)
    (c : Config (AgentState L K)) (m : ℕ)
    (_hm : geCount (L := L) (K := K) (p + 1) c = m) (_hm_hi : m < n)
    (c' : Config (AgentState L K)) (hmono : m ≤ geCount (L := L) (K := K) (p + 1) c') :
    gDeficitPot p n s c' ≤
      (if m + 1 ≤ geCount (L := L) (K := K) (p + 1) c' then
        ENNReal.ofReal (Real.exp (s * ((n : ℝ) - (m : ℝ) - 1)))
      else
        ENNReal.ofReal (Real.exp (s * ((n : ℝ) - (m : ℝ))))) := by
  unfold gDeficitPot geFinished gClamp
  by_cases hfin : n ≤ geCount (L := L) (K := K) (p + 1) c'
  · rw [if_pos hfin]; split_ifs <;> exact bot_le
  · rw [if_neg hfin]
    rw [not_le] at hfin
    by_cases hadv : m + 1 ≤ geCount (L := L) (K := K) (p + 1) c'
    · rw [if_pos hadv]
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      rw [min_eq_left (le_of_lt hfin)]
      have : (m : ℝ) + 1 ≤ (geCount (L := L) (K := K) (p + 1) c' : ℝ) := by exact_mod_cast hadv
      nlinarith [hs, this]
    · rw [if_neg hadv]
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      rw [min_eq_left (le_of_lt hfin)]
      have hle : (m : ℝ) ≤ (geCount (L := L) (K := K) (p + 1) c' : ℝ) := by exact_mod_cast hmono
      nlinarith [hs, hle]

/-! ## The genuine one-step informed-count drift. -/

/-- The PROVEN advance-fraction floor: for `1 ≤ m ≤ n−1`, `n − 1 ≤ m·(n−m)`. -/
theorem advance_floor_seam (n m : ℕ) (h1 : 1 ≤ m) (hlt : m < n) : n - 1 ≤ m * (n - m) := by
  obtain ⟨k, hk⟩ : ∃ k, n = m + k ∧ 1 ≤ k := ⟨n - m, by omega, by omega⟩
  obtain ⟨hnk, hk1⟩ := hk
  subst hnk
  rw [Nat.add_sub_cancel_left]
  obtain ⟨a, rfl⟩ : ∃ a, m = a + 1 := ⟨m - 1, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, k = b + 1 := ⟨k - 1, by omega⟩
  have : (a + 1) * (b + 1) = a * b + a + b + 1 := by ring
  omega

/-- **The genuine generic-`p` advance-count drift.**  On the seam window
`allPhaseGe p n` with `n ≥ 2`, in the unfinished regime (`geCount (p+1) < n`), the
deficit potential contracts at the GENUINE rate
`r = 1 − ((n−1)/(n(n−1)))·(1 − e^{−s})`.  This is the abstract-`p` clone of
`Phase4Convergence.phase4AdvancedDrift`. -/
theorem phaseAdvanceDrift (p n : ℕ) (hn : 2 ≤ n) (s : ℝ) (hs : 0 < s)
    (c : Config (AgentState L K)) (hQ : allPhaseGe (L := L) (K := K) p n c)
    (hlo : 1 ≤ geCount (L := L) (K := K) (p + 1) c)
    (hnc : geCount (L := L) (K := K) (p + 1) c < n) :
    ∫⁻ c', gDeficitPot p n s c' ∂((NonuniformMajority L K).transitionKernel c) ≤
      ENNReal.ofReal (1 - (((n - 1 : ℕ) : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) * (1 - Real.exp (-s)))
        * gDeficitPot p n s c := by
  set m := geCount (L := L) (K := K) (p + 1) c with hm
  have hΦc : gDeficitPot p n s c
      = ENNReal.ofReal (Real.exp (s * ((n : ℝ) - (m : ℝ)))) :=
    gDeficitPot_eq_of_lt p n s c hnc
  set A := {c' : Config (AgentState L K) | m + 1 ≤ geCount (L := L) (K := K) (p + 1) c'}
    with hA_def
  have hA_meas : MeasurableSet A := DiscreteMeasurableSpace.forall_measurableSet _
  set pR : ℝ := (((n - 1 : ℕ)) : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) with hpR
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hden_pos : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
  have hfloorN : n - 1 ≤ m * (n - m) := advance_floor_seam n m hlo hnc
  have hmRle : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast le_of_lt hnc
  have hnmR : ((n - m : ℕ) : ℝ) = (n : ℝ) - (m : ℝ) := by rw [Nat.cast_sub (le_of_lt hnc)]
  have hrec_le : ((m * (n - m) : ℕ) : ℝ) ≤ (n : ℝ) * ((n : ℝ) - 1) := by
    rw [Nat.cast_mul, hnmR]
    nlinarith [sq_nonneg ((n : ℝ) - 2 * (m : ℝ)), hmRle, hnR,
      mul_nonneg (by linarith : (0:ℝ) ≤ (m:ℝ)) (by linarith : (0:ℝ) ≤ (n:ℝ) - (m:ℝ))]
  have hfloorR : (((n - 1 : ℕ)) : ℝ) ≤ ((m * (n - m) : ℕ) : ℝ) := by exact_mod_cast hfloorN
  have hnum_le : (((n - 1 : ℕ)) : ℝ) ≤ (n : ℝ) * ((n : ℝ) - 1) := le_trans hfloorR hrec_le
  have hpR_nonneg : 0 ≤ pR := by rw [hpR]; exact div_nonneg (Nat.cast_nonneg _) (le_of_lt hden_pos)
  have hpR_le_one : pR ≤ 1 := by rw [hpR, div_le_one hden_pos]; exact hnum_le
  set E0 : ℝ := Real.exp (s * ((n : ℝ) - (m : ℝ))) with hE0
  set E1 : ℝ := Real.exp (s * ((n : ℝ) - (m : ℝ) - 1)) with hE1
  have hE0_pos : 0 < E0 := Real.exp_pos _
  have hE1_pos : 0 < E1 := Real.exp_pos _
  have hE1_eq : E1 = E0 * Real.exp (-s) := by rw [hE0, hE1, ← Real.exp_add]; congr 1; ring
  have hstep : ENNReal.ofReal pR ≤
      ((NonuniformMajority L K).stepDistOrSelf c).toMeasure A := by
    have hadv := ge_advance_prob p n hn c hQ
    rw [← hm] at hadv
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) hadv
    rw [hpR]
    apply (div_le_div_iff_of_pos_right hden_pos).mpr
    exact hfloorR
  change ∫⁻ c', gDeficitPot p n s c'
    ∂((NonuniformMajority L K).stepDistOrSelf c).toMeasure ≤ _
  calc ∫⁻ c', gDeficitPot p n s c'
        ∂((NonuniformMajority L K).stepDistOrSelf c).toMeasure
      ≤ ∫⁻ c', (if m + 1 ≤ geCount (L := L) (K := K) (p + 1) c' then ENNReal.ofReal E1
          else ENNReal.ofReal E0) ∂((NonuniformMajority L K).stepDistOrSelf c).toMeasure := by
        apply lintegral_mono_ae
        rw [ae_iff, PMF.toMeasure_apply_eq_zero_iff _
          (DiscreteMeasurableSpace.forall_measurableSet _)]
        rw [Set.disjoint_left]
        intro x hsupp hbad
        apply hbad
        have hmono_x : m ≤ geCount (L := L) (K := K) (p + 1) x :=
          geCount_ge_monotone (p + 1) m c x (le_of_eq hm.symm) hsupp
        exact gDeficitPot_pointwise_bound p n s hs c m hm.symm hnc x hmono_x
    _ = (∫⁻ c' in A, ENNReal.ofReal E1 ∂((NonuniformMajority L K).stepDistOrSelf c).toMeasure) +
        (∫⁻ c' in Aᶜ, ENNReal.ofReal E0 ∂((NonuniformMajority L K).stepDistOrSelf c).toMeasure) := by
        rw [← lintegral_add_compl _ hA_meas]
        congr 1
        · apply lintegral_congr_ae
          filter_upwards [ae_restrict_mem hA_meas] with c' hc'
          simp only [Set.mem_setOf_eq, hA_def] at hc'
          simp [hc']
        · apply lintegral_congr_ae
          filter_upwards [ae_restrict_mem hA_meas.compl] with c' hc'
          simp only [Set.mem_compl_iff, Set.mem_setOf_eq, hA_def] at hc'
          simp [hc']
    _ = ENNReal.ofReal E1 * ((NonuniformMajority L K).stepDistOrSelf c).toMeasure A +
        ENNReal.ofReal E0 * ((NonuniformMajority L K).stepDistOrSelf c).toMeasure Aᶜ := by
        rw [lintegral_const, Measure.restrict_apply_univ,
            lintegral_const, Measure.restrict_apply_univ]
    _ ≤ ENNReal.ofReal (1 - pR * (1 - Real.exp (-s))) * gDeficitPot p n s c := by
        rw [hΦc]
        set q := ((NonuniformMajority L K).stepDistOrSelf c).toMeasure A with hq_def
        set qc := ((NonuniformMajority L K).stepDistOrSelf c).toMeasure Aᶜ with hqc_def
        haveI : IsProbabilityMeasure ((NonuniformMajority L K).stepDistOrSelf c).toMeasure :=
          PMF.toMeasure.isProbabilityMeasure _
        have hq_ge : ENNReal.ofReal pR ≤ q := hstep
        have hq_le_one : q ≤ 1 := by
          calc q ≤ ((NonuniformMajority L K).stepDistOrSelf c).toMeasure Set.univ :=
                measure_mono (Set.subset_univ _)
            _ = 1 := measure_univ
        have hq_ne_top : q ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hq_le_one
        have hqc_eq : qc = 1 - q := by
          have h_compl := measure_compl hA_meas hq_ne_top
          rw [show ((NonuniformMajority L K).stepDistOrSelf c).toMeasure Set.univ = 1
            from measure_univ] at h_compl
          exact h_compl
        set qr := q.toReal with hqr_def
        have hqr_nonneg : 0 ≤ qr := ENNReal.toReal_nonneg
        have hqr_le_one : qr ≤ 1 := by
          have := ENNReal.toReal_mono ENNReal.one_ne_top hq_le_one
          rwa [ENNReal.toReal_one] at this
        have hq_ofReal : q = ENNReal.ofReal qr := (ENNReal.ofReal_toReal hq_ne_top).symm
        have hp_le_qr : pR ≤ qr := by
          have h1 : ENNReal.ofReal pR ≤ ENNReal.ofReal qr := by rw [← hq_ofReal]; exact hq_ge
          exact (ENNReal.ofReal_le_ofReal_iff hqr_nonneg).mp h1
        have h1mqr_nonneg : 0 ≤ 1 - qr := by linarith
        have hqc_ofReal : qc = ENNReal.ofReal (1 - qr) := by
          rw [hqc_eq, hq_ofReal,
              show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm,
              ← ENNReal.ofReal_sub 1 hqr_nonneg]
        have lhs_eq : ENNReal.ofReal E1 * q + ENNReal.ofReal E0 * qc =
            ENNReal.ofReal (E1 * qr + E0 * (1 - qr)) := by
          rw [hq_ofReal, hqc_ofReal,
              ← ENNReal.ofReal_mul hE1_pos.le, ← ENNReal.ofReal_mul hE0_pos.le,
              ← ENNReal.ofReal_add (mul_nonneg hE1_pos.le hqr_nonneg)
                (mul_nonneg hE0_pos.le h1mqr_nonneg)]
        have hexp_le_one : Real.exp (-s) ≤ 1 := by
          rw [show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]
          exact Real.exp_le_exp.mpr (by linarith)
        have rhs_eq : ENNReal.ofReal (1 - pR * (1 - Real.exp (-s))) * ENNReal.ofReal E0 =
            ENNReal.ofReal ((1 - pR * (1 - Real.exp (-s))) * E0) := by
          rw [← ENNReal.ofReal_mul]
          have : (1 : ℝ) - pR * (1 - Real.exp (-s)) ≥ 0 := by
            have h0 : (0 : ℝ) ≤ 1 - Real.exp (-s) := by linarith
            nlinarith [hpR_nonneg, hpR_le_one, h0]
          linarith
        rw [lhs_eq, rhs_eq]
        apply ENNReal.ofReal_le_ofReal
        have hfactor : E1 * qr + E0 * (1 - qr) = E0 * (1 - qr * (1 - Real.exp (-s))) := by
          rw [hE1_eq]; ring
        rw [hfactor]
        have hrhs : (1 - pR * (1 - Real.exp (-s))) * E0
            = E0 * (1 - pR * (1 - Real.exp (-s))) := by ring
        rw [hrhs]
        apply mul_le_mul_of_nonneg_left _ hE0_pos.le
        have h1me : (0 : ℝ) ≤ 1 - Real.exp (-s) := by linarith
        nlinarith [mul_le_mul_of_nonneg_right hp_le_qr h1me]

/-! ## Part F — the seam tail: wrap the drift into `windowDrift_PhaseConvergence`
and discharge `hDrift`. -/

/-- On the seam `Pre` (at least one informed agent), the deficit potential is at
most `ofReal(exp(s·(n−1)))`. -/
theorem gDeficitPot_le_pre (p n : ℕ) (s : ℝ) (hs : 0 < s)
    (c : Config (AgentState L K)) (hlo : 1 ≤ geCount (L := L) (K := K) (p + 1) c) :
    gDeficitPot p n s c ≤ ENNReal.ofReal (Real.exp (s * ((n : ℝ) - 1))) := by
  unfold gDeficitPot gClamp
  by_cases hfin : geFinished (L := L) (K := K) p n c
  · rw [if_pos hfin]; exact bot_le
  · rw [if_neg hfin]
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have hmin : (min (geCount (L := L) (K := K) (p + 1) c) n : ℕ)
        = geCount (L := L) (K := K) (p + 1) c := by
      unfold geFinished at hfin; omega
    rw [hmin]
    have h1 : (1 : ℝ) ≤ (geCount (L := L) (K := K) (p + 1) c : ℝ) := by exact_mod_cast hlo
    nlinarith [hs, h1]

/-- The seam drift window: the seam `≥ p`-window plus at least one informed agent
(`1 ≤ geCount (p+1)`, the epidemic seed). -/
def Qwin (p n : ℕ) (c : Config (AgentState L K)) : Prop :=
  allPhaseGe (L := L) (K := K) p n c ∧ 1 ≤ geCount (L := L) (K := K) (p + 1) c

instance (p n : ℕ) (c : Config (AgentState L K)) : Decidable (Qwin p n c) := by
  unfold Qwin; infer_instance

theorem Qwin_absorbing (p n : ℕ) (c c' : Config (AgentState L K)) (hw : Qwin p n c)
    (hc' : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    Qwin p n c' :=
  ⟨allPhaseGe_absorbing p n c c' hw.1 hc', geCount_ge_monotone (p + 1) 1 c c' hw.2 hc'⟩

/-- The window-guarded deficit potential: `⊤` off `Qwin`, else `gDeficitPot`. -/
noncomputable def gPotW (p n : ℕ) (s : ℝ) (c : Config (AgentState L K)) : ℝ≥0∞ :=
  if Qwin p n c then gDeficitPot p n s c else ⊤

theorem gPotW_measurable (p n : ℕ) (s : ℝ) :
    Measurable (gPotW p n s (L := L) (K := K)) :=
  Measurable.of_discrete

theorem gPotW_eq_on_window (p n : ℕ) (s : ℝ) (c : Config (AgentState L K))
    (hw : Qwin p n c) : gPotW p n s c = gDeficitPot p n s c := by
  unfold gPotW; rw [if_pos hw]

/-- **The seam advance-epidemic `PhaseConvergence`** (`Post = geFinished`).  Built
by wrapping `phaseAdvanceDrift` into `windowDrift_PhaseConvergence`, exactly as
`phase4NonTieConvergence` wraps `phase4AdvancedDrift`. -/
noncomputable def seamGeConvergence (p n : ℕ) (hn : 2 ≤ n) (s : ℝ) (hs : 0 < s)
    (t : ℕ) (ε : ℝ≥0)
    (hε : ENNReal.ofReal
            (1 - (((n - 1 : ℕ) : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) * (1 - Real.exp (-s))) ^ t *
            ENNReal.ofReal (Real.exp (s * ((n : ℝ) - 1))) / 1
          ≤ (ε : ℝ≥0∞)) :
    PhaseConvergence (NonuniformMajority L K).transitionKernel := by
  refine WindowConcentration.windowDrift_PhaseConvergence (NonuniformMajority L K)
    (gPotW p n s) (gPotW_measurable p n s)
    (fun c => Qwin p n c)
    (Qwin_absorbing p n)
    (ENNReal.ofReal
      (1 - (((n - 1 : ℕ) : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) * (1 - Real.exp (-s))))
    ?_
    (fun c => Qwin p n c)
    (fun c => Qwin p n c ∧ geFinished (L := L) (K := K) p n c)
    ?_
    1 one_ne_zero ENNReal.one_ne_top
    ?_
    (fun c h => h)
    (ENNReal.ofReal (Real.exp (s * ((n : ℝ) - 1))))
    ?_
    t ε hε
  · -- hdrift
    intro c hQw
    obtain ⟨hQ, hlo⟩ := hQw
    rw [gPotW_eq_on_window p n s c ⟨hQ, hlo⟩]
    have hint_eq : ∫⁻ c', gPotW p n s c'
          ∂((NonuniformMajority L K).transitionKernel c)
        = ∫⁻ c', gDeficitPot p n s c'
          ∂((NonuniformMajority L K).transitionKernel c) := by
      apply lintegral_congr_ae
      change ∀ᵐ c' ∂((NonuniformMajority L K).stepDistOrSelf c).toMeasure,
        gPotW p n s c' = gDeficitPot p n s c'
      rw [ae_iff, PMF.toMeasure_apply_eq_zero_iff _
        (DiscreteMeasurableSpace.forall_measurableSet _)]
      rw [Set.disjoint_left]
      intro x hsupp hbad
      apply hbad
      exact gPotW_eq_on_window p n s x (Qwin_absorbing p n c x ⟨hQ, hlo⟩ hsupp)
    rw [hint_eq]
    by_cases hfin : geFinished (L := L) (K := K) p n c
    · have hΦc0 : gDeficitPot p n s c = 0 := by unfold gDeficitPot; rw [if_pos hfin]
      rw [hΦc0, mul_zero, nonpos_iff_eq_zero]
      change ∫⁻ c', gDeficitPot p n s c'
          ∂((NonuniformMajority L K).stepDistOrSelf c).toMeasure = 0
      rw [lintegral_eq_zero_iff (gDeficitPot_measurable p n s)]
      rw [Filter.eventuallyEq_iff_exists_mem]
      refine ⟨((NonuniformMajority L K).stepDistOrSelf c).support, ?_, ?_⟩
      · rw [mem_ae_iff, PMF.toMeasure_apply_eq_zero_iff _
          (DiscreteMeasurableSpace.forall_measurableSet _)]
        rw [Set.disjoint_left]; intro x hsupp hx
        exact hx (PMF.mem_support_iff _ _ |>.mp hsupp)
      · intro c' hc'
        have hfin' : geFinished (L := L) (K := K) p n c' :=
          geFinished_absorbing p n c c' hfin hc'
        change gDeficitPot p n s c' = 0
        unfold gDeficitPot; rw [if_pos hfin']
    · have hnc : geCount (L := L) (K := K) (p + 1) c < n := by unfold geFinished at hfin; omega
      exact phaseAdvanceDrift p n hn s hs c hQ hlo hnc
  · -- hPost_abs
    rintro c c' ⟨hQw, hfin⟩ hc'
    exact ⟨Qwin_absorbing p n c c' hQw hc',
      geFinished_absorbing p n c c' hfin hc'⟩
  · -- hlink
    intro c hnp
    unfold gPotW
    by_cases hQw : Qwin p n c
    · rw [if_pos hQw]
      have hnf : ¬ geFinished (L := L) (K := K) p n c := fun hfin => hnp ⟨hQw, hfin⟩
      exact not_finished_imp_gDeficitPot_ge_one p n s hs c hnf
    · rw [if_neg hQw]; exact le_top
  · -- hPre_bound
    intro c hPre
    rw [gPotW_eq_on_window p n s c hPre]
    exact gDeficitPot_le_pre p n s hs c hPre.2

/-- `advTriggered (p+1)` matches `1 ≤ geCount (p+1)` (the `countP` predicates agree:
`decide (p+1 ≤ phase) = true` ↔ `p+1 ≤ phase`). -/
theorem advTriggered_iff_geCount (p : ℕ) (c : Config (AgentState L K)) :
    advTriggered (L := L) (K := K) (p + 1) c
      ↔ 1 ≤ geCount (L := L) (K := K) (p + 1) c := by
  have hcount : Multiset.countP (fun a => decide (p + 1 ≤ a.phase.val)) c
      = Multiset.countP (fun a => geP (L := L) (K := K) (p + 1) a) c := by
    apply Multiset.countP_congr rfl
    intro a _
    simp only [geP, decide_eq_true_eq]
  unfold advTriggered geCount
  rw [hcount]

/-- **The discharged `hDrift(p)`.**  From a seam `Pre` (`allPhaseGe p n ∧
advTriggered (p+1)`), after `t` interactions the next `≥`-window `allPhaseGe (p+1)
n` fails with probability at most the genuine epidemic tail
`r^t · exp(s·(n−1))`, `r = 1 − ((n−1)/(n(n−1)))·(1 − e^{−s})`.  This is exactly the
hypothesis the generic `seamEpidemicW` carries — discharged here by the abstract-`p`
clone of the Phase-4 epidemic. -/
theorem seam_drift (p n : ℕ) (hn : 2 ≤ n) (s : ℝ) (hs : 0 < s) (t : ℕ) (ε : ℝ≥0)
    (hε : ENNReal.ofReal
            (1 - (((n - 1 : ℕ) : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) * (1 - Real.exp (-s))) ^ t *
            ENNReal.ofReal (Real.exp (s * ((n : ℝ) - 1))) / 1
          ≤ (ε : ℝ≥0∞))
    (c : Config (AgentState L K))
    (hPre : allPhaseGe (L := L) (K := K) p n c ∧ advTriggered (L := L) (K := K) (p + 1) c) :
    ((NonuniformMajority L K).transitionKernel ^ t) c
        {c' | ¬ allPhaseGe (L := L) (K := K) (p + 1) n c'}
      ≤ (ε : ℝ≥0∞) := by
  set NT := seamGeConvergence (L := L) (K := K) p n hn s hs t ε hε with hNT
  -- Pre of NT is `Qwin p n`; our hPre gives it via advTriggered ↔ geCount.
  have hQwin : Qwin (L := L) (K := K) p n c :=
    ⟨hPre.1, (advTriggered_iff_geCount p c).mp hPre.2⟩
  have hNTpre : NT.Pre c := hQwin
  have hNTconv := NT.convergence c hNTpre
  -- NT.Post c' = Qwin p n c' ∧ geFinished p n c'; show {¬allPhaseGe(p+1)} ⊆ {¬Post}.
  have hsub : {c' : Config (AgentState L K)
        | ¬ allPhaseGe (L := L) (K := K) (p + 1) n c'}
      ⊆ {c' | ¬ NT.Post c'} := by
    intro c' hc'
    simp only [Set.mem_setOf_eq] at hc' ⊢
    intro hPost
    have hPostU : Qwin (L := L) (K := K) p n c' ∧ geFinished (L := L) (K := K) p n c' := hPost
    obtain ⟨hQw', hfin'⟩ := hPostU
    have hcard' : c'.card = n := hQw'.1.1
    exact hc' ((allPhaseGe_succ_iff_geFinished p n c' hcard').mpr hfin')
  calc ((NonuniformMajority L K).transitionKernel ^ t) c
          {c' | ¬ allPhaseGe (L := L) (K := K) (p + 1) n c'}
      ≤ ((NonuniformMajority L K).transitionKernel ^ t) c {c' | ¬ NT.Post c'} :=
        measure_mono hsub
    _ ≤ (ε : ℝ≥0∞) := hNTconv

/-- **The calibrated generic seam.**  `seamEpidemicW` with its `hDrift` field
DISCHARGED at the genuine Phase-4-shape tail.  `Pre` = seam `≥ p`-window + trigger;
`Post` = `≥ (p+1)`-window; `t`, `εepidemic`, the overshoot budget `εovershoot`, and
the explicit tail check `hε` are the calibration inputs, mirroring Phase 4's `hε`.
This is the seam ready to plug into the 21-instance composition with NO undischarged
`hDrift` hypothesis. -/
noncomputable def seamEpidemicW_calibrated
    (p n t : ℕ) (hn : 2 ≤ n) (s : ℝ) (hs : 0 < s) (εepidemic εovershoot : ℝ≥0)
    (hε : ENNReal.ofReal
            (1 - (((n - 1 : ℕ) : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) * (1 - Real.exp (-s))) ^ t *
            ENNReal.ofReal (Real.exp (s * ((n : ℝ) - 1))) / 1
          ≤ (εepidemic : ℝ≥0∞)) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  seamEpidemicW (L := L) (K := K) p n t εepidemic εovershoot
    (fun c hPre => seam_drift p n hn s hs t εepidemic hε c hPre)

@[simp] theorem seamEpidemicW_calibrated_Pre
    (p n t : ℕ) (hn : 2 ≤ n) (s : ℝ) (hs : 0 < s) (εepidemic εovershoot : ℝ≥0) (hε)
    (c : Config (AgentState L K)) :
    (seamEpidemicW_calibrated (L := L) (K := K) p n t hn s hs εepidemic εovershoot hε).Pre c
      = (allPhaseGe (L := L) (K := K) p n c ∧ advTriggered (L := L) (K := K) (p + 1) c) := rfl

@[simp] theorem seamEpidemicW_calibrated_Post
    (p n t : ℕ) (hn : 2 ≤ n) (s : ℝ) (hs : 0 < s) (εepidemic εovershoot : ℝ≥0) (hε)
    (c : Config (AgentState L K)) :
    (seamEpidemicW_calibrated (L := L) (K := K) p n t hn s hs εepidemic εovershoot hε).Post c
      = allPhaseGe (L := L) (K := K) (p + 1) n c := rfl

@[simp] theorem seamEpidemicW_calibrated_t
    (p n t : ℕ) (hn : 2 ≤ n) (s : ℝ) (hs : 0 < s) (εepidemic εovershoot : ℝ≥0) (hε) :
    (seamEpidemicW_calibrated (L := L) (K := K) p n t hn s hs εepidemic εovershoot hε).t = t := rfl

@[simp] theorem seamEpidemicW_calibrated_eps
    (p n t : ℕ) (hn : 2 ≤ n) (s : ℝ) (hs : 0 < s) (εepidemic εovershoot : ℝ≥0) (hε) :
    (seamEpidemicW_calibrated (L := L) (K := K) p n t hn s hs εepidemic εovershoot hε).ε
      = εepidemic + εovershoot := rfl

end SeamEpidemics
end ExactMajority
