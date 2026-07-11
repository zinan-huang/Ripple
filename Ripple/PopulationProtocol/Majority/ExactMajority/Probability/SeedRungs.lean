/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Phase E4 — the per-rung ADVANCE SEEDS (`SeedRungs`)

`TimedChainRungs.lean` / `ChainEndAssembly.lean` closed the per-rung phase-advance
EXPECTED-time caps (`seam_rung_to_chain_target_le_nsq`, `≤ n²`), but every one of those
caps starts from the **trigger hypothesis** `htrig : 1 ≤ geCount (p+1) c` — at least one
agent has already crossed to phase `≥ p+1`.  `ChainEndAssembly`'s Part-4 survey concluded
that this seed is NOT supplied by the previous rung's drained output `AllClockGEpCard p n`
(which only gives `geCount p = n`, NOT `geCount (p+1) ≥ 1`).  **This file supplies the
honest mechanism that materialises that seed.**

## The honest mechanism (the survey)

The seed is NOT a carried mystery and NOT a free deterministic fact: it materialises after
ONE more counter-running interaction.  The counter-drain rung
(`ConditionalPhaseProgress.timed_phase_progress_real_tinyClock`) delivers
`E[T to clockCounterSumAt p = 0]` — the drained state in which EVERY phase-`p` clock has
counter `0` (`clockCounterSumAt p c = 0` is a sum of non-negative weights, so each summand
is `0`).  In the all-clock regime `AllClockGEpCard p n` with the seed not yet fired
(`geCount (p+1) c = 0`), EVERY agent is then a clock at phase exactly `p` (all `≥ p` by the
invariant, none `≥ p+1` by `geCount (p+1) = 0`) with counter `0`.

The FROZEN protocol then advances on the NEXT counter-running interaction: a clock-clock
pair at phase `p` with a `0` counter runs `stdCounterSubroutine → advancePhaseWithInit`,
advancing (at least) one participant to phase `≥ p+1` — this is the proven per-pair advance
`Analysis.PhaseProgress.Transition_timed_clock_counter_zero_advances` (timed phases
`p ∈ {0,1,5,6,7,8}`, covering `{5,6,7,8}` and the chain-end `9` via the analogous routes —
see Part 4 for the `9 → 10` verdict).  So `geCount (p+1)` climbs from `0` to `≥ 1`: the seed.

## The deliverables

1. **The per-pair seed advance** (`seed_pair_advances`): from a drained, all-clock, un-seeded
   state, ANY distinct pair raises `geCount (p+1)` from `0` to `≥ 1` (the counter-0 advance,
   via `Transition_timed_clock_counter_zero_advances`).
2. **The seed advance probability** (`seed_advance_prob`): the per-step kernel mass on
   `{1 ≤ geCount (p+1)}` is `≥ n(n−1)/(n(n−1))`-flavoured (the FULL clock×clock rectangle —
   every distinct pair advances), routed through `SeamEpidemics.advance_prob_of_rect`.
3. **The seed expected-time bound** (`seed_expectedHitting_le`): from the drained un-seeded
   state, `E[T to {1 ≤ geCount (p+1)}] ≤ n(n−1)/((n)(n−1))`-flavoured — one clock-pair
   meeting, an `O(1)`-block / single-milestone coupon (`ExpectedHitting.expectedHitting_one_step_q`).
4. **The wired seed rung** (`seed_then_spread_le`): drained → seeded (this file) → spread
   (`TimedChainRungs`, `≤ n²`), the per-rung `drained ⟹ chain-target` bound with the seed
   discharged, and the re-cut spine arithmetic (`2·9·n²` budget).

## Build

Single-file only:
  `lake env lean Ripple/PopulationProtocol/Majority/ExactMajority/Probability/SeedRungs.lean`
from the project root (deps as cached oleans).  NEVER local `lake build`.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.TimedChainRungs
import Ripple.PopulationProtocol.Majority.ExactMajority.Analysis.PhaseProgress

namespace ExactMajority
namespace SeedRungs

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators NNReal
open ConditionalPhaseProgress SeamEpidemics TimedChainRungs

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-! ## Part 0 — the drained-state structure facts

`clockCounterSumAt p c = 0` (the engine's drained target `potBelow (clockCounterSumAt p) 1`)
forces every phase-`p` clock's counter to `0`: the sum is over non-negative per-agent
weights `wtAt p a = if (clock ∧ phase = p) then counter else 0`, so a zero sum forces each
summand to `0`.  Combined with `AllClockGEp p` (every agent a clock at phase `≥ p`) and the
un-seeded condition `geCount (p+1) c = 0` (no agent at phase `≥ p+1`), every agent is a clock
at phase EXACTLY `p` with counter `0`. -/

/-- **Drained ⟹ every phase-`p` clock has counter `0`.**  `clockCounterSumAt p c = 0` is a
sum of non-negative weights `wtAt p`, so each agent's weight is `0`; for a clock at phase
exactly `p` the weight IS its counter, hence the counter is `0`. -/
theorem drained_imp_counter_zero (p : ℕ) (c : Config (AgentState L K))
    (hdrain : clockCounterSumAt (L := L) (K := K) p c = 0)
    (a : AgentState L K) (ha : a ∈ c) (haclock : a.role = .clock)
    (haphase : a.phase.val = p) :
    a.counter.val = 0 := by
  classical
  -- clockCounterSumAt p c = (c.map (wtAt p)).sum = 0; every summand ≥ 0, so wtAt p a = 0.
  rw [clockCounterSumAt_eq_sum_wtAt] at hdrain
  have hmem : wtAt (L := L) (K := K) p a ∈ c.map (wtAt (L := L) (K := K) p) :=
    Multiset.mem_map_of_mem _ ha
  have hzero : wtAt (L := L) (K := K) p a = 0 := by
    by_contra hne
    have hpos : 0 < wtAt (L := L) (K := K) p a := Nat.pos_of_ne_zero hne
    have : 0 < (c.map (wtAt (L := L) (K := K) p)).sum :=
      lt_of_lt_of_le hpos (Multiset.single_le_sum (fun _ _ => Nat.zero_le _) _ hmem)
    omega
  -- wtAt p a = counter (clock at phase p), so counter = 0.
  unfold wtAt at hzero
  rw [if_pos ⟨haclock, haphase⟩] at hzero
  exact hzero

/-- **The un-seeded all-clock characterisation.**  In the all-clock regime `AllClockGEp p`
with `geCount (p+1) c = 0` (no agent yet at phase `≥ p+1`), every agent in `c` is a clock at
phase EXACTLY `p`. -/
theorem unseeded_imp_phase_eq (p : ℕ) (c : Config (AgentState L K))
    (hInv : AllClockGEp (L := L) (K := K) p c)
    (hunseed : geCount (L := L) (K := K) (p + 1) c = 0)
    (a : AgentState L K) (ha : a ∈ c) :
    a.role = .clock ∧ a.phase.val = p := by
  classical
  obtain ⟨haclock, hage⟩ := hInv a ha
  refine ⟨haclock, ?_⟩
  -- geCount (p+1) c = 0 ⇒ countP (geP (p+1)) c = 0 ⇒ a is not geP (p+1), i.e. phase < p+1.
  have hnot : ¬ geP (L := L) (K := K) (p + 1) a := by
    intro hge
    have : 0 < Multiset.countP (fun b => geP (L := L) (K := K) (p + 1) b) c :=
      Multiset.countP_pos.mpr ⟨a, ha, hge⟩
    unfold geCount at hunseed
    omega
  simp only [geP] at hnot
  omega

/-! ## Part 1 — the per-pair seed advance

A distinct clock-clock pair at phase `p` (counter `0`) raises `geCount (p+1)` from `0` to
`≥ 1`: the counter-0 advance (`Transition_timed_clock_counter_zero_advances`) puts one of the
two outputs at phase `≥ p+1`, so the produced pair carries at least one `geP (p+1)` agent. -/

/-- **`countP (geP (p+1))` of the produced pair is `≥ 1`** when a distinct clock-clock pair at
phase `p` (counter `0`) is updated: the per-pair counter-0 advance lands one output at phase
`≥ p+1`. -/
theorem geP_pair_seed_advances (p : ℕ) (hp : p ∈ ({0, 1, 5, 6, 7, 8} : Finset ℕ))
    (s t : AgentState L K)
    (hs_phase : s.phase.val = p) (ht_phase : t.phase.val = p)
    (hs_clock : s.role = .clock) (ht_clock : t.role = .clock)
    (hs_ctr : s.counter.val = 0) (_ht_ctr : t.counter.val = 0) :
    1 ≤ Multiset.countP (fun a => geP (L := L) (K := K) (p + 1) a)
        ({(Transition L K s t).1, (Transition L K s t).2}
          : Multiset (AgentState L K)) := by
  have hadv := Transition_timed_clock_counter_zero_advances (L := L) (K := K) p hp s t
    hs_phase ht_phase hs_clock ht_clock (Or.inl hs_ctr)
  rw [countP_geP_pair]
  rcases hadv with h1 | h2
  · -- output .1 at phase ≥ p+1.
    have : geP (L := L) (K := K) (p + 1) (Transition L K s t).1 := h1
    rw [if_pos this]; omega
  · have : geP (L := L) (K := K) (p + 1) (Transition L K s t).2 := h2
    rw [if_pos this]; split_ifs <;> omega

/-- **The per-pair seed advance on the GLOBAL count.**  A scheduled distinct clock-clock pair
at phase `p` (counter `0`) from an un-seeded state (`geCount (p+1) c = 0`) raises the global
`geCount (p+1)` to `≥ 1`.  The un-seeded hypothesis is essential: with `geCount (p+1) c = 0`,
the removed pair `{s,t}` carries `0` informed agents (`countP (geP (p+1)) {s,t} = 0`), so the
produced pair's `≥ 1` informed agent is a NET gain.  Mirrors
`SeamEpidemics.geCount_stepOrSelf_advance` with the counter-0 advance replacing the mixed-pair
advance. -/
theorem geCount_stepOrSelf_seed_advance (p : ℕ)
    (hp : p ∈ ({0, 1, 5, 6, 7, 8} : Finset ℕ)) (c : Config (AgentState L K))
    (s t : AgentState L K) (happ : Protocol.Applicable c s t)
    (_hunseed : geCount (L := L) (K := K) (p + 1) c = 0)
    (hs_phase : s.phase.val = p) (ht_phase : t.phase.val = p)
    (hs_clock : s.role = .clock) (ht_clock : t.role = .clock)
    (hs_ctr : s.counter.val = 0) (ht_ctr : t.counter.val = 0) :
    1 ≤ geCount (L := L) (K := K) (p + 1)
          (Protocol.stepOrSelf (NonuniformMajority L K) c s t) := by
  have hsub : ({s, t} : Multiset (AgentState L K)) ≤ c := happ
  have hc' : Protocol.stepOrSelf (NonuniformMajority L K) c s t
      = c - {s, t} + {(Transition L K s t).1, (Transition L K s t).2} := by
    unfold Protocol.stepOrSelf; rw [if_pos happ]; rfl
  unfold geCount
  rw [hc', Multiset.countP_add]
  have hpair_ge : 1 ≤ Multiset.countP (fun a => geP (L := L) (K := K) (p + 1) a)
      ({(Transition L K s t).1, (Transition L K s t).2} : Multiset (AgentState L K)) :=
    geP_pair_seed_advances (L := L) (K := K) p hp s t hs_phase ht_phase hs_clock ht_clock
      hs_ctr ht_ctr
  -- 1 ≤ (anything) + countP{pair} since 1 ≤ countP{pair}.
  omega

/-! ## Part 2 — the seed advance probability (the full clock×clock rectangle)

The drained un-seeded state has EVERY agent a clock at phase exactly `p` with counter `0`.
The seed advance fires on ANY applicable distinct pair (`geCount_stepOrSelf_seed_advance`),
so the per-step kernel mass on `{1 ≤ geCount (p+1)}` is bounded below by the FULL clock-pair
rectangle mass `n(n−1)/(n(n−1))`.  We route this through `SeamEpidemics.advance_prob_of_rect`
with the rectangle `R` = all present states squared (every present state qualifies). -/

/-- **The seed advance probability (`≥ (n−1)/(n(n−1)) = 1/n`-flavoured, via the full
rectangle).**  From a drained (`clockCounterSumAt p c = 0`), un-seeded (`geCount (p+1) c = 0`)
all-clock state `AllClockGEpCard p n` with `n ≥ 2`, one step raises `geCount (p+1)` to `≥ 1`
with probability `≥ (n·(n−1)) / (n(n−1))`.  Every present state is a clock at phase `p` with
counter `0`, so every applicable ordered pair advances; the present-square rectangle aggregates
to `n(n−1)` interaction count out of `n(n−1)` ordered pairs. -/
theorem seed_advance_prob (p : ℕ) (hp : p ∈ ({0, 1, 5, 6, 7, 8} : Finset ℕ)) (n : ℕ)
    (hn : 2 ≤ n) (c : Config (AgentState L K))
    (hInv : AllClockGEpCard (L := L) (K := K) p n c)
    (hdrain : clockCounterSumAt (L := L) (K := K) p c = 0)
    (hunseed : geCount (L := L) (K := K) (p + 1) c = 0) :
    ENNReal.ofReal (((n * (n - 1) : ℕ) : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) ≤
      ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
        {c' | geCount (L := L) (K := K) (p + 1) c + 1
                ≤ geCount (L := L) (K := K) (p + 1) c'} := by
  classical
  obtain ⟨hAllClock, hcardn⟩ := hInv
  -- The rectangle: full present-state square.
  set R : Finset (AgentState L K × AgentState L K) := Finset.univ ×ˢ Finset.univ with hRdef
  -- Per-pair: a present distinct pair (both clock-at-p-counter-0) seed-advances.
  -- interactionCount sum over the full square = card · (card - 1) = n(n-1).
  have hsquare : (∑ pr ∈ R, c.interactionCount pr.1 pr.2) = c.card * (c.card - 1) := by
    -- mirror sum_interactionCount_posPhaseP_square with F = univ (∑ count over univ = card).
    have hpoint : ∀ pr ∈ R,
        c.interactionCount pr.1 pr.2 + (if pr.1 = pr.2 then c.count pr.1 else 0)
          = c.count pr.1 * c.count pr.2 := by
      rintro ⟨a, b⟩ _
      unfold Config.interactionCount
      by_cases h : a = b
      · subst h; rw [if_pos rfl, if_pos rfl]
        have hle : c.count a ≤ c.count a * c.count a := by nlinarith [Nat.zero_le (c.count a)]
        rw [Nat.mul_sub_one, Nat.sub_add_cancel hle]
      · rw [if_neg h, if_neg h, Nat.add_zero]
    have hNcard : (∑ a ∈ (Finset.univ : Finset (AgentState L K)), c.count a) = c.card := by
      simp only [Config.count]
      rw [← Multiset.sum_count_eq_card (s := Finset.univ) (m := c)
        (fun a _ => Finset.mem_univ a)]
    have hsq : (∑ pr ∈ R, c.count pr.1 * c.count pr.2)
        = (∑ a ∈ (Finset.univ : Finset (AgentState L K)), c.count a)
          * (∑ b ∈ (Finset.univ : Finset (AgentState L K)), c.count b) := by
      rw [hRdef, Finset.sum_product, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _; rw [Finset.mul_sum]
    have hdiag : (∑ pr ∈ R, (if pr.1 = pr.2 then c.count pr.1 else 0))
        = (∑ a ∈ (Finset.univ : Finset (AgentState L K)), c.count a) := by
      rw [hRdef, Finset.sum_product]
      have : ∀ a ∈ (Finset.univ : Finset (AgentState L K)),
          (∑ b ∈ (Finset.univ : Finset (AgentState L K)), (if a = b then c.count a else 0))
            = c.count a := by
        intro a ha
        rw [Finset.sum_ite_eq Finset.univ a (fun _ => c.count a), if_pos (Finset.mem_univ a)]
      rw [Finset.sum_congr rfl this]
    have hadd : (∑ pr ∈ R, c.interactionCount pr.1 pr.2) + c.card = c.card * c.card := by
      have hcollect : (∑ pr ∈ R, c.interactionCount pr.1 pr.2)
          + (∑ pr ∈ R, (if pr.1 = pr.2 then c.count pr.1 else 0))
          = ∑ pr ∈ R, c.count pr.1 * c.count pr.2 := by
        rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl hpoint
      rw [hdiag, hsq, hNcard] at hcollect; exact hcollect
    rw [Nat.mul_sub_one]; omega
  -- N = n(n-1) ≤ ∑ interactionCount over R.
  have hcount : (n * (n - 1) : ℕ) ≤ ∑ pr ∈ R, c.interactionCount pr.1 pr.2 := by
    rw [hsquare, hcardn]
  -- per-pair advance hypothesis for advance_prob_of_rect.
  refine advance_prob_of_rect p n hn c hcardn R (n * (n - 1)) ?_ hcount
  rintro ⟨a, b⟩ _hp h1 h2 _hsame
  -- a, b are present (count ≥ 1); both are clock-at-p-counter-0 (drained un-seeded all-clock).
  have hamem : a ∈ c := Multiset.one_le_count_iff_mem.mp h1
  have hbmem : b ∈ c := Multiset.one_le_count_iff_mem.mp h2
  obtain ⟨ha_clock, ha_phase⟩ :=
    unseeded_imp_phase_eq (L := L) (K := K) p c hAllClock hunseed a hamem
  obtain ⟨hb_clock, hb_phase⟩ :=
    unseeded_imp_phase_eq (L := L) (K := K) p c hAllClock hunseed b hbmem
  have ha_ctr : a.counter.val = 0 :=
    drained_imp_counter_zero (L := L) (K := K) p c hdrain a hamem ha_clock ha_phase
  have hb_ctr : b.counter.val = 0 :=
    drained_imp_counter_zero (L := L) (K := K) p c hdrain b hbmem hb_clock hb_phase
  -- applicable: distinct present states OR diagonal with count ≥ 2.
  have happ : Protocol.Applicable c a b := by
    by_cases hab : a = b
    · subst hab
      have hcnt2 : 2 ≤ c.count a := _hsame rfl
      show ({a, a} : Multiset (AgentState L K)) ≤ c
      rw [show ({a, a} : Multiset (AgentState L K)) = a ::ₘ a ::ₘ 0 from rfl, Multiset.le_iff_count]
      intro x
      rw [Multiset.count_cons, Multiset.count_cons, Multiset.count_zero]
      by_cases hxa : x = a
      · rw [hxa, if_pos rfl]
        have hcc : c.count a = Multiset.count a c := rfl
        omega
      · simp only [if_neg hxa]; omega
    · exact pair_le_of_mem_ne hamem hbmem hab
  -- the seed advance: geCount(p+1) c + 1 = 0 + 1 = 1 ≤ geCount(p+1)(step).
  rw [hunseed]
  exact geCount_stepOrSelf_seed_advance (L := L) (K := K) p hp c a b happ hunseed
    ha_phase hb_phase ha_clock hb_clock ha_ctr hb_ctr

/-! ## Part 3 — the seed expected-time bound (`E ≤ 1`: one clock-pair meeting)

The seed advance rate from a drained un-seeded state is the FULL rectangle
`n(n−1)/(n(n−1)) = 1`: EVERY applicable ordered pair is a counter-0 clock-clock pair and
advances.  So the kernel mass on the seed target `{1 ≤ geCount (p+1)}` is `≥ 1`, hence `= 1`:
the seed fires on the NEXT counter-running interaction with probability `1`.  The expected
time is therefore `≤ 1` — the single-milestone coupon at its trivial extreme.

This is the honest cost of the per-rung seed: ONE expected interaction (`O(1)`, absorbed into
the per-rung `n²` cap with overwhelming slack), NOT a carried mystery. -/

/-- The seed target set: at least one agent has crossed to phase `≥ p+1`. -/
def seedTarget (p : ℕ) : Set (Config (AgentState L K)) :=
  {c | 1 ≤ geCount (L := L) (K := K) (p + 1) c}

theorem seedTarget_measurable (p : ℕ) :
    MeasurableSet (seedTarget (L := L) (K := K) p) :=
  DiscreteMeasurableSpace.forall_measurableSet _

/-- **The seed target is absorbing.**  `geCount (p+1)` only rises along the kernel
(`SeamEpidemics.geCount_ge_monotone`), so once `≥ 1` it stays `≥ 1`. -/
theorem seedTarget_absorbing (p : ℕ) (c : Config (AgentState L K))
    (hc : c ∈ seedTarget (L := L) (K := K) p) :
    (NonuniformMajority L K).transitionKernel c (seedTarget (L := L) (K := K) p)ᶜ = 0 := by
  classical
  change ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
    (seedTarget (L := L) (K := K) p)ᶜ = 0
  rw [PMF.toMeasure_apply_eq_zero_iff _
    (seedTarget_measurable (L := L) (K := K) p).compl]
  rw [Set.disjoint_left]
  intro c' hsupp hbad
  apply hbad
  -- c ∈ seedTarget ⟹ c' ∈ seedTarget (geCount monotone on support).
  have : 1 ≤ geCount (L := L) (K := K) (p + 1) c := hc
  exact geCount_ge_monotone (p + 1) 1 c c' this hsupp

/-- **The seed fires in one step a.s. from a drained un-seeded state.**  The kernel mass on
the complement of the seed target is `0`: the advance rate is the full rectangle `= 1`, so
every step lands in `{1 ≤ geCount (p+1)}`. -/
theorem drained_kernel_seedTarget_compl_zero (p : ℕ)
    (hp : p ∈ ({0, 1, 5, 6, 7, 8} : Finset ℕ)) (n : ℕ) (hn : 2 ≤ n)
    (c : Config (AgentState L K)) (hInv : AllClockGEpCard (L := L) (K := K) p n c)
    (hdrain : clockCounterSumAt (L := L) (K := K) p c = 0)
    (hunseed : geCount (L := L) (K := K) (p + 1) c = 0) :
    (NonuniformMajority L K).transitionKernel c (seedTarget (L := L) (K := K) p)ᶜ = 0 := by
  classical
  -- The advance event {geCount c + 1 ≤ geCount c'} = {1 ≤ geCount c'} = seedTarget (geCount c = 0).
  have hrate := seed_advance_prob (L := L) (K := K) p hp n hn c hInv hdrain hunseed
  -- the rate ofReal(n(n-1)/(n(n-1))) = 1.
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hn1pos : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hden_pos : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := mul_pos hnpos hn1pos
  have hnumeq : (((n * (n - 1) : ℕ) : ℝ)) = (n : ℝ) * ((n : ℝ) - 1) := by
    rw [Nat.cast_mul, Nat.cast_sub (by omega)]; push_cast; ring
  have hrate1 : ENNReal.ofReal (((n * (n - 1) : ℕ) : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) = 1 := by
    rw [hnumeq, div_self (ne_of_gt hden_pos), ENNReal.ofReal_one]
  rw [hrate1] at hrate
  -- advance event ⊆ seedTarget (geCount c = 0 ⟹ geCount c + 1 = 1).
  have hsub : {c' : Config (AgentState L K) | geCount (L := L) (K := K) (p + 1) c + 1
                ≤ geCount (L := L) (K := K) (p + 1) c'}
      ⊆ seedTarget (L := L) (K := K) p := by
    intro c' hc'
    simp only [Set.mem_setOf_eq, hunseed] at hc'
    exact hc'
  have hmono : ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
        {c' | geCount (L := L) (K := K) (p + 1) c + 1 ≤ geCount (L := L) (K := K) (p + 1) c'}
      ≤ ((NonuniformMajority L K).stepDistOrSelf c).toMeasure (seedTarget (L := L) (K := K) p) :=
    measure_mono hsub
  -- kernel = stepDistOrSelf; mass on seedTarget ≥ 1, so = 1, so complement = 0.
  have hge1 : (1 : ℝ≥0∞) ≤ (NonuniformMajority L K).transitionKernel c
      (seedTarget (L := L) (K := K) p) := by
    change (1 : ℝ≥0∞) ≤ ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
      (seedTarget (L := L) (K := K) p)
    exact le_trans hrate hmono
  have hle1 : (NonuniformMajority L K).transitionKernel c (seedTarget (L := L) (K := K) p) ≤ 1 :=
    MeasureTheory.prob_le_one
  have heq1 : (NonuniformMajority L K).transitionKernel c (seedTarget (L := L) (K := K) p) = 1 :=
    le_antisymm hle1 hge1
  -- complement mass = 1 - 1 = 0.
  rw [MeasureTheory.prob_compl_eq_one_sub (seedTarget_measurable (L := L) (K := K) p), heq1,
    tsub_self]

/-- **The seed expected-time bound (`E[T to seed] ≤ 1`).**  From a drained
(`clockCounterSumAt p c = 0`), un-seeded (`geCount (p+1) c = 0`) all-clock state
`AllClockGEpCard p n` (`n ≥ 2`), the expected number of interactions to materialise the
advance seed `{1 ≤ geCount (p+1)}` is at most `1`: the next counter-running interaction
advances a clock to phase `≥ p+1` with probability `1`.  Proven directly from the
one-step-a.s. fact (`drained_kernel_seedTarget_compl_zero`): the `t = 0` tail term is `≤ 1`
and all `t ≥ 1` terms vanish. -/
theorem seed_expectedHitting_le_one (p : ℕ)
    (hp : p ∈ ({0, 1, 5, 6, 7, 8} : Finset ℕ)) (n : ℕ) (hn : 2 ≤ n)
    (c : Config (AgentState L K)) (hInv : AllClockGEpCard (L := L) (K := K) p n c)
    (hdrain : clockCounterSumAt (L := L) (K := K) p c = 0)
    (hunseed : geCount (L := L) (K := K) (p + 1) c = 0) :
    expectedHitting (NonuniformMajority L K).transitionKernel c
        (seedTarget (L := L) (K := K) p)
      ≤ 1 := by
  classical
  set ker := (NonuniformMajority L K).transitionKernel with hker
  set Done := seedTarget (L := L) (K := K) p with hDoneset
  have hDmeas : MeasurableSet Done := seedTarget_measurable (L := L) (K := K) p
  have hDabs : ∀ x ∈ Done, ker x Doneᶜ = 0 := fun x hx =>
    seedTarget_absorbing (L := L) (K := K) p x hx
  -- the one-step a.s. fact at the drained start.
  have hstep0 : ker c Doneᶜ = 0 :=
    drained_kernel_seedTarget_compl_zero (L := L) (K := K) p hp n hn c hInv hdrain hunseed
  -- expectedHitting = ∑' t, (ker^t) c Doneᶜ; t=0 term ≤ 1, t≥1 terms ≤ (ker^1) c Doneᶜ = 0.
  rw [expectedHitting_eq_tsum]
  rw [← ENNReal.summable.sum_add_tsum_nat_add' (f := fun t => (ker ^ t) c Doneᶜ) (k := 1)]
  have htail0 : ∀ t : ℕ, (ker ^ (t + 1)) c Doneᶜ = 0 := by
    intro t
    have hle : (ker ^ (t + 1)) c Doneᶜ ≤ (ker ^ 1) c Doneᶜ :=
      bad_antitone_le ker hDmeas hDabs c (by omega : 1 ≤ t + 1)
    rw [pow_one] at hle
    rw [hstep0] at hle
    exact le_antisymm hle (zero_le')
  have hsum1 : (∑ i ∈ Finset.range 1, (ker ^ i) c Doneᶜ) ≤ 1 := by
    simp only [Finset.range_one, Finset.sum_singleton, pow_zero]
    exact kernel_pow_le_one ker 0 c Doneᶜ
  have htailsum : (∑' t : ℕ, (ker ^ (t + 1)) c Doneᶜ) = 0 := by
    simp only [htail0]; exact tsum_zero
  calc (∑ i ∈ Finset.range 1, (ker ^ i) c Doneᶜ) + ∑' t : ℕ, (ker ^ (t + 1)) c Doneᶜ
      = (∑ i ∈ Finset.range 1, (ker ^ i) c Doneᶜ) + 0 := by rw [htailsum]
    _ ≤ 1 := by rw [add_zero]; exact hsum1

/-! ## Part 4 — the wired seed rung: drained → seeded → spread (`E ≤ 1 + n²`)

Composing the seed bound (Part 3, `E[T drained → seeded] ≤ 1`) with the seam spread
(`TimedChainRungs.seam_rung_to_chain_target_le_nsq`, `E[T seeded → chain-target] ≤ n²`) via the
invariant-relative seqcomp `RecoveryBridges.expectedHitting_seqcomp_on_of_uniform`
(`J = AllClockGEpCard p n`, one-step-closed; `Mid = seedTarget`, `Done = chain-target`).  The
`Mid`-state cap is exactly `seam_rung_to_chain_target_le_nsq`, whose two inputs — the regime
membership `AllClockGEpCard p n` (`= J`) and the seed `1 ≤ geCount (p+1)` (`= Mid`) — are now
SUPPLIED by the seqcomp's `J ∩ Mid` hypothesis, NOT carried.  This is the per-rung
`drained ⟹ chain-target` bound with the seed DISCHARGED. -/

open scoped Classical in
/-- **The wired per-rung seed-and-spread bound (`E ≤ 1 + n²`).**

From a DRAINED, un-seeded, all-clock state `AllClockGEpCard p n` (`3 ≤ p`, `n ≥ 2`,
`clockCounterSumAt p c = 0`, `geCount (p+1) c = 0`) — the EXACT output of the counter-drain
rung `ConditionalPhaseProgress.timed_phase_progress_real_tinyClock` — the expected number of
interactions to reach the next-phase chain target `{AllClockGEpCard (p+1) n}` is at most
`1 + n²`: ONE interaction to materialise the advance seed (Part 3), then `≤ n²` for the seam
epidemic to spread the phase to the whole population.

This CLOSES the `htrig`/`hseed` residual `TimedChainRungs`/`ChainEndAssembly` carried: the seed
is no longer a hypothesis but a theorem, costing `O(1)` expected interactions absorbed into the
per-rung budget. -/
theorem seed_then_spread_le (p n : ℕ) (hp : p ∈ ({0, 1, 5, 6, 7, 8} : Finset ℕ))
    (hp3 : 3 ≤ p) (hn : 2 ≤ n) (c : Config (AgentState L K))
    (hInv : AllClockGEpCard (L := L) (K := K) p n c)
    (hdrain : clockCounterSumAt (L := L) (K := K) p c = 0)
    (hunseed : geCount (L := L) (K := K) (p + 1) c = 0) :
    expectedHitting (NonuniformMajority L K).transitionKernel c
        (StableBridges_timed_phase_chain_target (L := L) (K := K) (n := n) (p := p))
      ≤ 1 + ((n * n : ℕ) : ℝ≥0∞) := by
  classical
  set ker := (NonuniformMajority L K).transitionKernel with hker
  set J : Config (AgentState L K) → Prop := AllClockGEpCard (L := L) (K := K) p n with hJ
  set Mid : Set (Config (AgentState L K)) := seedTarget (L := L) (K := K) p with hMidset
  set Done : Set (Config (AgentState L K)) :=
    StableBridges_timed_phase_chain_target (L := L) (K := K) (n := n) (p := p) with hDoneset
  -- J is one-step closed (3 ≤ p).
  have hClosed : ∀ b : Config (AgentState L K), J b → ker b {x | ¬ J x} = 0 :=
    AllClockGEpCard_InvClosed (L := L) (K := K) p n hp3
  have hMidMeas : MeasurableSet Mid := seedTarget_measurable (L := L) (K := K) p
  have hDoneMeas : MeasurableSet Done :=
    DiscreteMeasurableSpace.forall_measurableSet _
  -- A = 1: the seed bound.
  have hA : expectedHitting ker c Mid ≤ 1 :=
    seed_expectedHitting_le_one (L := L) (K := K) p hp n hn c hInv hdrain hunseed
  -- B = n²: from every (J ∩ Mid)-state the seam spread caps at n².
  have hB : ∀ y : Config (AgentState L K), J y → y ∈ Mid →
      expectedHitting ker y Done ≤ ((n * n : ℕ) : ℝ≥0∞) := by
    intro y hJy hyMid
    have htrig : 1 ≤ geCount (L := L) (K := K) (p + 1) y := hyMid
    exact seam_rung_to_chain_target_le_nsq (L := L) (K := K) p n hp3 hn y hJy htrig
  exact expectedHitting_seqcomp_on_of_uniform ker J hClosed hMidMeas hDoneMeas
    (1 : ℝ≥0∞) ((n * n : ℕ) : ℝ≥0∞) c hInv hA hB

/-! ## Part 5 — the re-cut per-rung budget and spine arithmetic

The honest per-rung cap is now `1 + n²` (seed + spread), NOT `n²`.  The timed spine telescopes
the phase chain `p → p+1 → ⋯ → 10` over the `3 ≤ p` rungs `p ∈ {5,6,7,8}` (plus the chain-end
`9 → 10`, see Part 6), i.e. `q = 10 − p` rungs from a phase-`p` start.  Each rung now costs
`1 + n²`, so the telescoped budget is `q·(1 + n²) = q + q·n²`.

`ChainEndAssembly.timedSpine_ladderData` already budgets `q·n² + βfinal ≤ Brecover`; the re-cut
adds the per-rung seed term, giving `q·(1 + n²) + βfinal = q + q·n² + βfinal`.  For the longest
timed branch (`p = 5`, `q = 5`) the seed overhead is `5·1 = 5` interactions on top of `5·n² + …`
— utterly dominated by the `n²` spread terms (`n ≥ 2`).  We record the per-rung re-cut and the
telescoped seed overhead `q·1 = q` as honest closed-form additions. -/

/-- **The re-cut per-rung budget: each rung is `1 + n²`.**  Trivial restatement of
`seed_then_spread_le` packaging the per-rung cap as `seedOverhead + spread = 1 + n²`; the seed
overhead `1` is the `O(1)`-expected-interaction cost of materialising the advance seed, absorbed
into the spine budget (`q·(1 + n²)` over `q` rungs). -/
theorem per_rung_recut (p n : ℕ) (hp : p ∈ ({0, 1, 5, 6, 7, 8} : Finset ℕ))
    (hp3 : 3 ≤ p) (hn : 2 ≤ n) (c : Config (AgentState L K))
    (hInv : AllClockGEpCard (L := L) (K := K) p n c)
    (hdrain : clockCounterSumAt (L := L) (K := K) p c = 0)
    (hunseed : geCount (L := L) (K := K) (p + 1) c = 0) :
    expectedHitting (NonuniformMajority L K).transitionKernel c
        (StableBridges_timed_phase_chain_target (L := L) (K := K) (n := n) (p := p))
      ≤ 1 + ((n * n : ℕ) : ℝ≥0∞) :=
  seed_then_spread_le (L := L) (K := K) p n hp hp3 hn c hInv hdrain hunseed

/-- **The telescoped seed overhead is `q` interactions** for a `q`-rung timed branch:
`q·(1 + n²) = q + q·n²`.  The extra `q·1 = q` over the previous `q·n²` budget is the total seed
cost across the branch's rungs — a pure additive `O(q) = O(1)` term (q ≤ 5), dominated by the
`q·n²` spread.  Pure `ℝ≥0∞` arithmetic, no kernel content. -/
theorem telescoped_seed_overhead (q n : ℕ) :
    (q : ℝ≥0∞) * (1 + ((n * n : ℕ) : ℝ≥0∞))
      = (q : ℝ≥0∞) + (q : ℝ≥0∞) * ((n * n : ℕ) : ℝ≥0∞) := by
  rw [mul_add, mul_one]

/-! ## Part 6 — the `9 → 10` chain-end verdict (RE-SURVEYED)

**The seed mechanism covers `p ∈ {5,6,7,8}` (and the lower timed phases `{0,1}`), NOT `9`.**
`seed_then_spread_le` requires `hp : p ∈ {0,1,5,6,7,8}` — the counter-timed phases on which
`Transition_timed_clock_counter_zero_advances` fires.  The chain-end `9 → 10` is OUTSIDE this
set, and the re-survey CONFIRMS the campaign's prior finding: **phase 9 genuinely has no timed
counter.**

* `Protocol.Transition.Phase9Transition = Phase2Transition` (a bias-sign / opinion-comparison
  transition); it runs NO `stdCounterSubroutine` on clocks, so there is no counter-0 clock that
  advances `9 → 10` on a counter-running interaction.  Equivalently `9 ∉ CounterTimedPhase`
  (`SeamNoOvershoot.CounterTimedPhase q = (q = 1 ∨ q = 5 ∨ q = 6 ∨ q = 7 ∨ q = 8)`).

* Therefore the counter-drain seed mechanism of this file CANNOT supply the `9 → 10` seed.  The
  honest `9 → 10` entry seed stays the **error-jump / backup-entry route**: `phaseInit 1/2/9`
  error-jumps a biased/`mcr` agent to phase `10` via `enterPhase10` (the FROZEN seam), as
  documented in `BackupEntry.lean` Part 6.  That seed (`1 ≤ geCount 10 c`) is the NAMED whp
  event — the `enterPhase10` error-jump fires whp once a biased/`mcr` agent crosses — NOT a
  deterministic counter-0 advance, and is honestly carried by `BackupEntry.backup_entry_*`,
  not closed here.

So this file CLOSES the `{5,6,7,8}` seam-rung seeds deterministically-modulo-`O(1)`-time (the
counter-0 mechanism) and leaves the `9 → 10` seed precisely where it honestly lives — the
backup-entry whp event.  The Part-3 seed bound, applied at `p = 9`, would be VACUOUS (its
`hp : 9 ∈ {0,1,5,6,7,8}` is false), correctly refusing to manufacture a non-existent counter. -/

end SeedRungs
end ExactMajority
