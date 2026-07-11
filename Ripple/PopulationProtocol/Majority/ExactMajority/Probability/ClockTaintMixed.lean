/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# ClockTaintMixed — the clock-filtered early-drip ghost on the marked kernel (§6 brick 3, STAGE 3)

This file builds the MIXED-protocol clock-filtered taint count on the EXISTING marked-agent kernel
`EarlyDripMarked.markedK` (NO new ghost kernel — Hole-3 fix from the doctrine, ROUND 5/6).  In the
real mixed protocol Main and Reserve agents coexist with Clocks, so `AllClockP3` (every agent is a
phase-3 clock) is FALSE.  The early-drip ghost rate `tainted_rise_prob_le` is stated under
`AllClockP3`; here we provide the CLOCK-FILTERED variant whose bad event is restricted to the
clock-role agents, towards a hypothesis weakened to `ClockP3` (only the clock-role agents pinned to
phase 3, Main/Reserve unconstrained — `ClockFrontMixed.ClockP3`).

## What is proven (axiom-clean)

* `clockTaintedCount T mc` — Doty's `d_{≥T+1}` restricted to the clock role (clock ∧ minute ≥ T+1 ∧
  tainted).
* `clockTaintedCount_le_taintedCount` — clock-filtered ≤ all tainted (`countP` monotonicity).
* `clockTaintedCount_le_rBeyond_succ_erase` — tainted clocks beyond `T` ≤ all clocks beyond `T`
  (= `rBeyond (T+1) ∘ eraseConfig`), an elementary `countP`/erase identity.
* `clockTaintedCount_le_aboveCount`, `clockTaintedCount_le_clockBeyondCount` — supporting structural
  inequalities.

## STAGE-3 KEY adapter — the precise remaining obligation

The KEY adapter `clockTainted_rise_prob_le` (a MIXED variant of `tainted_rise_prob_le` that drops
`AllClockP3` for `ClockP3`) is stated as `clockTainted_rise_subset_obligation` together with the
EXACT blocking step documented at its declaration.  The blocker is identified PRECISELY below: the
existing `EarlyDripMarked.tainted_rise_subset` applies `AllClockP3` to BOTH sampled pair members
(`EarlyDripMarked.lean` lines 1304-1305) to invoke `ClimbTail.transition_p3_minute_le_succ_max`,
which needs BOTH pair members to be phase-3 *clocks*.  Under the weakened `ClockP3` a sampled pair
may contain a Main/Reserve agent, and the Main×Clock / Main×Main transition is only an identity on
the clock when the Main agent is *unbiased and at phase 3* (`HourCoupling.phase3_drag_left/right`,
which require `hs_bias = .zero`).  `ClockP3` does NOT constrain Main agents, so the
clock-locality of the taint rise is not available from `ClockP3` alone; the honest weakened
hypothesis additionally
needs the unbiased-phase-3 Main facts (or the prefix-FrontSync gate that supplies them).  This is
recorded as the explicit obligation rather than faked.

Reference: Doty et al. (arXiv:2106.10201v2) lines 1807-1819; `DOCTRINE_THM69_CA.md` ROUND 5 (Hole 1,
Hole 3) and ROUND 6 (family2: the clock-filtered taint, the `tainted_rise_prob_le` `AllClockP3`
caveat).
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.EarlyDripMarked
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockFrontMixed

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace ClockTaintMixed

open ClockRealKernel EarlyDripMarked

variable {L K : ℕ}

/-! ## Part 0 — local `countP`/sum helpers (Mathlib has no global `countP` monotonicity; the
`sum_count_filter_eq_countP` of `EarlyDripMarked` is `private`). -/

/-- **Pointwise `countP` monotonicity** on the elements of the multiset: if `p a → q a` for every
`a ∈ s`, then `countP p s ≤ countP q s`.  (Mathlib only ships `countP_mono_left` for the LIST/ARRAY
APIs; for `Multiset` we reprove it by induction.) -/
private theorem countP_mono_mem {α : Type*} (s : Multiset α) (p q : α → Prop)
    [DecidablePred p] [DecidablePred q] (h : ∀ a ∈ s, p a → q a) :
    Multiset.countP p s ≤ Multiset.countP q s := by
  classical
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
      rw [Multiset.countP_cons, Multiset.countP_cons]
      have ih' := ih (fun x hx => h x (Multiset.mem_cons_of_mem hx))
      by_cases hp : p a
      · have hq : q a := h a (Multiset.mem_cons_self a s) hp
        simp only [hp, hq, if_true]
        omega
      · simp only [hp, if_false, Nat.add_zero]
        have : (if q a then 1 else 0) ≥ 0 := Nat.zero_le _
        omega

/-- The indicator-sum form of `countP` over the universal finite type (a local copy of
`EarlyDripMarked.sum_count_filter_eq_countP`, which is `private`). -/
private theorem sum_count_filter_eq_countP (p : MarkedAgent L K → Prop) [DecidablePred p]
    (c : Config (MarkedAgent L K)) :
    (∑ m ∈ Finset.univ.filter p, c.count m) = Multiset.countP p c := by
  classical
  calc (∑ m ∈ Finset.univ.filter p, c.count m)
      = ∑ m : MarkedAgent L K, if p m then c.count m else 0 :=
        Finset.sum_filter _ _
    _ = ∑ m : MarkedAgent L K, (c.filter p).count m := by
        apply Finset.sum_congr rfl
        intro m _
        show _ = Multiset.count m (c.filter p)
        rw [Multiset.count_filter]
        rfl
    _ = (c.filter p).card :=
        Multiset.sum_count_eq_card (fun a _ => Finset.mem_univ a)
    _ = Multiset.countP p c := (Multiset.countP_eq_card_filter _ _).symm

/-! ## Part 1 — the clock-filtered tainted count (Doty's `d_{≥T+1}` restricted to clocks). -/

/-- **The clock-filtered tainted count.**  Doty's `d_{≥T+1}` restricted to the CLOCK role: agents
that are clocks, sit above minute `T`, and carry the taint mark.  In the mixed protocol only these
clock-role marks matter for the front-shape (the front is a clock-minute statistic), so this is the
ghost count that the mixed early-drip analysis tracks (vs `taintedCount`, which also counts any
Main/Reserve marks). -/
def clockTaintedCount (T : ℕ) (mc : Config (MarkedAgent L K)) : ℕ :=
  Multiset.countP
    (fun m : MarkedAgent L K => m.1.role = .clock ∧ T + 1 ≤ m.1.minute.val ∧ m.2 = true) mc

/-! ## Part 2 — the elementary structural inequalities (`countP` monotonicity + erase identity). -/

/-- **Clock-filtered ≤ all tainted.**  Every clock-filtered tainted agent is tainted, so the
clock-filtered count is at most the full taint count (`countP` monotonicity). -/
theorem clockTaintedCount_le_taintedCount (T : ℕ) (mc : Config (MarkedAgent L K)) :
    clockTaintedCount (L := L) (K := K) T mc ≤ taintedCount (L := L) (K := K) mc := by
  classical
  unfold clockTaintedCount taintedCount
  apply countP_mono_mem
  intro m _ hm
  exact hm.2.2

/-- **Clock-filtered ≤ clocks above `T`.**  Every clock-filtered tainted agent is a clock above `T`
(dropping the taint condition), so the clock-filtered count is at most the count of clocks above `T`
inside the marked configuration. -/
theorem clockTaintedCount_le_clockBeyondCount (T : ℕ) (mc : Config (MarkedAgent L K)) :
    clockTaintedCount (L := L) (K := K) T mc ≤
      Multiset.countP
        (fun m : MarkedAgent L K => m.1.role = .clock ∧ T + 1 ≤ m.1.minute.val) mc := by
  classical
  unfold clockTaintedCount
  apply countP_mono_mem
  intro m _ hm
  exact ⟨hm.1, hm.2.1⟩

/-- **Clock-filtered ≤ above `T`.**  Dropping the role and taint conditions, the clock-filtered count
is at most `aboveCount T` (the raw count of agents above minute `T`). -/
theorem clockTaintedCount_le_aboveCount (T : ℕ) (mc : Config (MarkedAgent L K)) :
    clockTaintedCount (L := L) (K := K) T mc ≤ aboveCount (L := L) (K := K) T mc := by
  classical
  unfold clockTaintedCount aboveCount
  apply countP_mono_mem
  intro m _ hm
  exact hm.2.1

/-- **The clocks-above-`T` count of a marked config equals `rBeyond (T+1)` of its erasure.**  The
clock-beyond predicate on the erased config (`clockBeyondP (T+1) = role .clock ∧ T+1 ≤ minute`) counts
exactly the clock-role agents above `T` in the marked config, since erasure (`Multiset.map Prod.fst`)
only forgets the marks and `clockBeyondP` depends solely on the agent state. -/
theorem clockBeyondCount_eq_rBeyond_succ_erase (T : ℕ) (mc : Config (MarkedAgent L K)) :
    Multiset.countP
        (fun m : MarkedAgent L K => m.1.role = .clock ∧ T + 1 ≤ m.1.minute.val) mc
      = rBeyond (L := L) (K := K) (T + 1) (eraseConfig (L := L) (K := K) mc) := by
  classical
  unfold rBeyond eraseConfig clockBeyondP
  rw [Multiset.countP_map, ← Multiset.countP_eq_card_filter]
  rfl

/-- **Tainted clocks beyond `T` ≤ all clocks beyond `T` (= `rBeyond (T+1) ∘ erase`).**  The key
structural cap: the clock-filtered taint count is dominated by the real-chain front statistic
`rBeyond (T+1)` of the erased configuration.  This is the deterministic bridge that lets the ghost
count be compared to the real front fraction. -/
theorem clockTaintedCount_le_rBeyond_succ_erase (T : ℕ) (mc : Config (MarkedAgent L K)) :
    clockTaintedCount (L := L) (K := K) T mc ≤
      rBeyond (L := L) (K := K) (T + 1) (eraseConfig (L := L) (K := K) mc) := by
  rw [← clockBeyondCount_eq_rBeyond_succ_erase (L := L) (K := K) T mc]
  exact clockTaintedCount_le_clockBeyondCount (L := L) (K := K) T mc

/-! ## Part 3 — the MIXED KEY adapter: the precise remaining obligation.

The mixed clock-filtered ghost rate `clockTainted_rise_prob_le` would weaken `AllClockP3` to
`ClockFrontMixed.ClockP3` while bounding `P[clockTaintedCount rises]`.  We isolate the EXACT
remaining obligation as a `Prop`-level statement (`ClockTaintedRiseSubset`) together with the
precise blocking analysis.

### Why the existing proof does NOT weaken to `ClockP3` (the precise blocker)

`tainted_rise_prob_le` is `measure_mono (tainted_rise_subset hw)` followed by purely combinatorial
`interactionPMF` block bounds.  ALL of the `AllClockP3` usage is inside
`EarlyDripMarked.tainted_rise_subset`, at exactly two applications:

  `have h1cp := hw pr.1.1 (Multiset.mem_map_of_mem Prod.fst hmem1)`   -- EarlyDripMarked.lean:1304
  `have h2cp := hw pr.2.1 (Multiset.mem_map_of_mem Prod.fst hmem2)`   -- EarlyDripMarked.lean:1305

i.e. `hw` is consumed to learn that BOTH members of the SAMPLED pair `pr` are phase-3 clocks, which
feeds `ClimbTail.transition_p3_minute_le_succ_max` (the per-pair cap "outputs ≤ max(inputs)+1") used
to force the gated drip-seed structure.

Under the weakened `ClockP3` a sampled pair may contain a Main/Reserve agent.  A Main×Clock or
Main×Main interaction leaves a clock-role agent's minute UNCHANGED only when the Main agent is
UNBIASED and at phase 3 (`HourCoupling.phase3_drag_left` / `phase3_drag_right`, both of which carry
the hypothesis `hs_bias = .zero` and a phase-3 context).  `ClockP3` constrains ONLY the clock-role
agents; it says nothing about Main bias/phase.  Hence `ClockP3` ALONE does not give the clock-locality
of the clock-filtered taint rise, and the honest mixed hypothesis additionally needs the unbiased
phase-3 Main facts (supplied in the real campaign by the prefix-FrontSync / Phase-3 gate).

We therefore state the remaining obligation precisely (no `sorry`/`axiom`): the clock-filtered rise
subset under `ClockP3` PLUS the auxiliary clock-locality of the step.  The provable part — the
reduction of the probability bound to this subset — is recorded for the eventual discharge.
-/

/-- **The clock-filtered taint-rise subset (the remaining obligation).**  The statement that, under
the mixed `ClockP3` window (and whatever auxiliary unbiased-phase-3 Main facts the real gate
supplies, abstracted here as the predicate `Aux`), the event that one marked step raises the
clock-filtered taint count is contained in the two scheduler events (a same-minute-`T` clock pair or
a pair containing a tainted clock).  This is the MIXED analogue of
`EarlyDripMarked.tainted_rise_subset`; its discharge is the STAGE-3 KEY adapter's genuine remaining
content (see the module docstring for the precise blocking analysis). -/
def ClockTaintedRiseSubset (T θn : ℕ) (Aux : Config (MarkedAgent L K) → Prop) : Prop :=
  ∀ mc : Config (MarkedAgent L K),
    ClockFrontMixed.ClockP3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc) →
    Aux mc →
      (markedStep (L := L) (K := K) T θn mc) ⁻¹'
          {mc' | clockTaintedCount (L := L) (K := K) T mc
            < clockTaintedCount (L := L) (K := K) T mc'} ⊆
        {pr : MarkedAgent L K × MarkedAgent L K |
            pr.1.1.minute.val = T ∧ pr.2.1.minute.val = T} ∪
          {pr : MarkedAgent L K × MarkedAgent L K | pr.1.2 = true ∨ pr.2.2 = true}

/-- **The KEY adapter, modulo the remaining obligation (the provable reduction).**  GIVEN the
clock-filtered rise subset `ClockTaintedRiseSubset` (the genuine remaining content, whose blocker is
documented above), the clock-filtered ghost rate

  `P[clockTaintedCount rises] ≤ (count@T / n)² + 2·taintedCount/n`

follows by EXACTLY the same `interactionPMF` block bounds as `tainted_rise_prob_le` — the part that
does NOT use `AllClockP3`.  Thus the ONLY obstruction to the mixed bound is the rise-subset
obligation; the probabilistic envelope transfers unchanged.  (The `2·taintedCount/n` epidemic term is
kept at the FULL `taintedCount` since `clockTaintedCount ≤ taintedCount`, which only loosens the
bound.) -/
theorem clockTainted_rise_prob_le_of_subset
    (T θn : ℕ) (Aux : Config (MarkedAgent L K) → Prop)
    (hsub : ClockTaintedRiseSubset (L := L) (K := K) T θn Aux)
    (mc : Config (MarkedAgent L K)) (h : 2 ≤ mc.card)
    (hP3 : ClockFrontMixed.ClockP3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc))
    (haux : Aux mc) :
    markedK (L := L) (K := K) T θn mc
        {mc' | clockTaintedCount (L := L) (K := K) T mc
          < clockTaintedCount (L := L) (K := K) T mc'} ≤
      ENNReal.ofReal
        (((Multiset.countP (fun m : MarkedAgent L K => m.1.minute.val = T) mc : ℝ)
          / (mc.card : ℝ)) ^ 2)
      + ENNReal.ofReal
          (2 * ((taintedCount (L := L) (K := K) mc : ℝ) / (mc.card : ℝ))) := by
  classical
  rw [markedK_apply_pair (L := L) (K := K) T θn mc h _
    (DiscreteMeasurableSpace.forall_measurableSet _)]
  refine le_trans (measure_mono (hsub mc hP3 haux)) ?_
  refine le_trans (measure_union_le _ _) ?_
  set ST : Finset (MarkedAgent L K) :=
    Finset.univ.filter (fun m : MarkedAgent L K => m.1.minute.val = T) with hST
  set SM : Finset (MarkedAgent L K) :=
    Finset.univ.filter (fun m : MarkedAgent L K => m.2 = true) with hSM
  have hXT : (∑ m ∈ ST, mc.count m)
      = Multiset.countP (fun m : MarkedAgent L K => m.1.minute.val = T) mc := by
    rw [hST]
    exact sum_count_filter_eq_countP _ mc
  have hXM : (∑ m ∈ SM, mc.count m) = taintedCount (L := L) (K := K) mc := by
    rw [hSM]
    exact sum_count_filter_eq_countP _ mc
  have hbound1 : (mc.interactionPMF h).toMeasure
      {pr : MarkedAgent L K × MarkedAgent L K |
        pr.1.1.minute.val = T ∧ pr.2.1.minute.val = T} ≤
      ENNReal.ofReal
        (((Multiset.countP (fun m : MarkedAgent L K => m.1.minute.val = T) mc : ℝ)
          / (mc.card : ℝ)) ^ 2) := by
    have hset : {pr : MarkedAgent L K × MarkedAgent L K |
        pr.1.1.minute.val = T ∧ pr.2.1.minute.val = T}
        = {pr : MarkedAgent L K × MarkedAgent L K | pr.1 ∈ ST ∧ pr.2 ∈ ST} := by
      ext pr
      simp [hST]
    rw [hset, ← hXT]
    exact pair_block_prob_le_sq (L := L) (K := K) mc h ST
  have hbound2 : (mc.interactionPMF h).toMeasure
      {pr : MarkedAgent L K × MarkedAgent L K | pr.1.2 = true ∨ pr.2.2 = true} ≤
      ENNReal.ofReal
        (2 * ((taintedCount (L := L) (K := K) mc : ℝ) / (mc.card : ℝ))) := by
    have hsub2 : {pr : MarkedAgent L K × MarkedAgent L K | pr.1.2 = true ∨ pr.2.2 = true}
        ⊆ {pr : MarkedAgent L K × MarkedAgent L K | pr.1 ∈ SM}
          ∪ {pr : MarkedAgent L K × MarkedAgent L K | pr.2 ∈ SM} := by
      rintro pr (hp | hp)
      · exact Or.inl (by simp [hSM, hp])
      · exact Or.inr (by simp [hSM, hp])
    refine le_trans (measure_mono hsub2) (le_trans (measure_union_le _ _) ?_)
    have h1 := fst_block_prob_le (L := L) (K := K) mc h SM
    have h2 := snd_block_prob_le (L := L) (K := K) mc h SM
    rw [hXM] at h1 h2
    refine le_trans (add_le_add h1 h2) ?_
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    ring_nf
    exact le_refl _
  exact add_le_add hbound1 hbound2

end ClockTaintMixed

end ExactMajority
