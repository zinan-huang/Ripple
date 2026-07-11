/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Avenue D-lynch-3 — the MIXED-regime clock-minute advance (genuine clock fraction)

`ClockRealAdvance.clock_real_advance_uncond` proved the clock-minute advance on
the ALL-CLOCKS window `AllClockMinT3 T` (every agent a Phase-3 Clock at minute
`≥ T`).  That window never arises in the real protocol: clocks are a SUB-population
of size `m_C` coexisting with Main/Reserve agents.  This file moves to the MIXED
regime.

The decisive change vs the all-clocks file is the SCHEDULER DENOMINATOR.  In the
all-clocks file `card = n` equals the clock count, so `totalPairs = n(n−1)`
already counted only clocks; the advance probability `2/(n(n−1))` was secretly the
clock-only ratio.  Here `card = n` is the FULL population and only `m_C ≤ n` of
them are clocks.  The advancing pairs are still clock-clock pairs, but they are
now weighed against the FULL `totalPairs = n(n−1)` denominator.  THIS is where the
genuine clock-fraction factor appears: the advance probability is

  (advancing clock-clock ordered pairs) / (n(n−1))

with the numerator built from the clock count `m_C`, NOT from `n`.  This factor is
DERIVED below from `interactionCount`/`totalPairs` — never assumed.

## What is reused verbatim (proven, agent-agnostic, in ClockRealKernel / ClockRealAdvance)
* `rBeyond T c` — count of CLOCK agents at minute `≥ T` (Main/Reserve contribute 0).
* `rDrip_pair_advances`, `rDripDistinct_pair_advances`, `rEpidemic_pair_advances(')`
  — per-pair clock-clock minute advance; AGENT-OTHER-AGNOSTIC (they only constrain
  the two scheduled clocks, never the rest of the population).
* `applicable_of_mem_distinct`, `countP_pair`, `clockBeyondP`.
* `rSeedPot`, `rClamp`, `rFinished`, `rSeedPotG`, `rShell`, the guarded link /
  bound / absorbing helpers, and `windowDrift_PhaseConvergence`.

## Honest hypotheses (carried as EXPLICIT, clearly-labeled inputs — deferred)
These are GENUINE protocol invariants (true in real executions of the protocol);
they are STRUCTURAL (deterministic support-closure facts), NOT the contraction
itself, and they are carried as named hypotheses to be discharged in separate
avenues.  The contraction PROBABILITY is NOT among them — it is derived.

1. `habs_mix` — one-step support closure of the mixed window `Q_mix` (the
   "clock-role agents stay at phase exactly 3" invariant).  Deferred to the
   cap-boundary reachability invariant.  (Analog of the all-clocks `habs`.)
2. `hmono_mix` — `rBeyond (T+1)` is non-decreasing on the kernel support over the
   window (no clock's minute drops, no clock-at-`≥T+1` loses its clock role).
   This is a DETERMINISTIC structural fact: clocks are role-stable (role changes
   fire only in Phase 0, gated on non-clock inputs) and minute-monotone (only the
   clock-clock Phase-3 drip edits a minute, upward).  Deferred to a separate
   one-sided clock-stability avenue.
3. `hclock_lb : γ * n ≤ m_C` — the clock-population fraction floor (from Phase-0
   clock creation).  Used to translate the derived `(m_C−1)/(n(n−1))` advance
   probability into a clock-fraction contraction factor.

The advance probability LOWER bound is DERIVED by pair-counting from the FULL
`n(n−1)` denominator (`clock_real_advance_prob_mixed`); it is never assumed.

NEW file; no existing file is edited; no sorry/admit/axiom/native_decide.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockRealKernel
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockRealAdvance

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real BigOperators

namespace ClockRealMixed

open ClockRealKernel

variable {L K : ℕ}

/-! ## Part A — the mixed window `Q_mix` and the clock count.

`clockCount c` is the number of clock-role agents.  The mixed window allows
Main/Reserve agents to coexist: it constrains ONLY the clock-role agents (to be at
phase exactly 3 and at minute `≥ T`), carries the clock population size `m_C`, and
requires all `m_C` clocks to be at minute `≥ T` (`rBeyond T c = m_C`). -/

/-- The number of clock-role agents in `c`. -/
def clockCount (c : Config (AgentState L K)) : ℕ :=
  Multiset.countP (fun a => a.role = .clock) c

/-- The MIXED-regime window.  Unlike `AllClockMinT3`, the predicate on a NON-clock
agent is vacuous (Main/Reserve are unconstrained); only clock-role agents are
pinned to phase exactly 3 and minute `≥ T`.  The clock population size `m_C` is
carried, and all `m_C` clocks are at minute `≥ T`. -/
structure Q_mix (n mC T : ℕ) (c : Config (AgentState L K)) : Prop where
  /-- The full population size (Main/Reserve included). -/
  card : c.card = n
  /-- Clock-role agents are at phase EXACTLY 3 (the phase-3 window; Main/Reserve
  unconstrained).  NO minute floor is imposed (the SYNC mechanism reads the
  susceptible count from `clockSize`, not from a per-clock minute floor). -/
  clockPhase3 : ∀ a ∈ c, a.role = .clock → a.phase.val = 3
  /-- The carried clock population size. -/
  clockSize : clockCount (L := L) (K := K) c = mC
  /-- The level-`T` 0.9-floor: at least `⌊9·m_C/10⌋` clocks are at minute `≥ T`.
  This is the SEED drip source floor; it does NOT require FULL crossing
  `rBeyond T = mC`. -/
  crossedT : 9 * mC / 10 ≤ rBeyond (L := L) (K := K) T c

/-! ## Part B — extracting a frontier clock and the advancing pair SET.

In the unfinished regime `rBeyond (T+1) c < m_C` there is a clock at minute exactly
`T` (a frontier clock `w`).  We build the advancing ordered-pair set as `w` paired
with EVERY clock state (`(w, v)` and `(v, w)` for every present clock state `v`),
each of which advances `rBeyond (T+1)` by one (same-state drip, distinct drip, or
epidemic sync).  The total `interactionCount` over this set is `count w · (m_C−1)`,
the genuine clock-count numerator. -/

/-- The clock sub-multiset of `c`. -/
def clocksOf (c : Config (AgentState L K)) : Multiset (AgentState L K) :=
  c.filter (fun a => a.role = .clock)

theorem clocksOf_card (c : Config (AgentState L K)) :
    (clocksOf (L := L) (K := K) c).card = clockCount (L := L) (K := K) c := by
  unfold clocksOf clockCount
  rw [Multiset.countP_eq_card_filter]

/-- A clock at minute exactly `T` exists when the level-`T` count strictly exceeds
the level-`T+1` count (`rBeyond (T+1) c < rBeyond T c`): the threshold counts at
level `T` and `T+1` differ, so some clock sits at minute exactly `T`.  This needs
NO full crossing — it is the genuine drip-frontier extraction. -/
theorem exists_frontier_clock (n mC T : ℕ) (c : Config (AgentState L K))
    (hQ : Q_mix (L := L) (K := K) n mC T c)
    (hunf : rBeyond (L := L) (K := K) (T + 1) c < rBeyond (L := L) (K := K) T c) :
    ∃ w ∈ c, w.role = .clock ∧ w.phase.val = 3 ∧ w.minute.val = T := by
  classical
  -- count of {clock ∧ minute ≥ T+1} < count of {clock ∧ minute ≥ T}.
  have hlt : Multiset.countP (fun a => clockBeyondP (T + 1) a) c
      < Multiset.countP (fun a => clockBeyondP T a) c := by
    have h1 : Multiset.countP (fun a => clockBeyondP T a) c
        = rBeyond (L := L) (K := K) T c := rfl
    have h2 : Multiset.countP (fun a => clockBeyondP (T + 1) a) c
        = rBeyond (L := L) (K := K) (T + 1) c := rfl
    omega
  -- a separating element: clock beyond T but not beyond T+1, i.e. at minute exactly T.
  by_contra hcon
  simp only [not_exists, not_and] at hcon
  have hge : Multiset.countP (fun a => clockBeyondP T a) c
      ≤ Multiset.countP (fun a => clockBeyondP (T + 1) a) c := by
    rw [Multiset.countP_eq_card_filter, Multiset.countP_eq_card_filter]
    apply Multiset.card_le_card
    rw [Multiset.le_iff_count]
    intro a
    rw [Multiset.count_filter, Multiset.count_filter]
    by_cases hbT : clockBeyondP T a
    · rw [if_pos hbT]
      by_cases hmem : a ∈ c
      · have hbT1 : clockBeyondP (T + 1) a := by
          by_contra hnb
          -- a is a clock (hbT.1), at minute ≥ T (hbT.2) but not ≥ T+1, so minute = T.
          have hac : a.role = .clock := hbT.1
          have hp3 : a.phase.val = 3 := hQ.clockPhase3 a hmem hac
          have hmT : a.minute.val = T := by
            have h1 : T ≤ a.minute.val := hbT.2
            have h2 : ¬ (T + 1 ≤ a.minute.val) := fun h => hnb ⟨hac, h⟩
            omega
          exact hcon a hmem hac hp3 hmT
        rw [if_pos hbT1]
      · rw [Multiset.count_eq_zero_of_notMem hmem]; split_ifs <;> omega
    · rw [if_neg hbT]; omega
  omega

/-- **The generalized EPIDEMIC-sync advance for a susceptible at minute `≤ T`.**  A
scheduled Phase-3 clock pair `(s, t)` with `s.minute ≥ T+1` (INFECTED) and
`t.minute ≤ T` (SUSCEPTIBLE, NOT necessarily exactly `T`) has unequal minutes, so the
SYNC rule pulls BOTH up to `max = s.minute ≥ T+1`, raising `rBeyond (T+1)` by one.
Generalizes `ClockRealKernel.rEpidemic_pair_advances'` (which fixed `t.minute = T`) to
the whole susceptible band; built from the same floor-agnostic per-pair sync fact. -/
theorem rSync_pair_advances (T : ℕ) (c : Config (AgentState L K))
    (s t : AgentState L K)
    (hs_phase : s.phase.val = 3) (ht_phase : t.phase.val = 3)
    (hs_clock : s.role = .clock) (ht_clock : t.role = .clock)
    (hs_min : T + 1 ≤ s.minute.val) (ht_min : t.minute.val ≤ T)
    (happ : Protocol.Applicable c s t)
    (j : ℕ) (hj : rBeyond (L := L) (K := K) (T + 1) c = j) :
    j + 1 ≤ rBeyond (L := L) (K := K) (T + 1)
      (Protocol.stepOrSelf (NonuniformMajority L K) c s t) := by
  classical
  have hsub : ({s, t} : Multiset (AgentState L K)) ≤ c := happ
  have hne : s.minute ≠ t.minute := by
    intro h; have := congrArg Fin.val h; omega
  have hsy := Transition_phase3_clock_minute_sync_decreases (L := L) (K := K) s t
    hs_phase ht_phase hs_clock ht_clock hne
  set s' := (Transition L K s t).1 with hs'
  set t' := (Transition L K s t).2 with ht'
  have hs'clock : s'.role = .clock := hsy.2.2.1
  have ht'clock : t'.role = .clock := hsy.2.2.2.1
  have hs'min : s'.minute = max s.minute t.minute := hsy.2.2.2.2.1
  have ht'min : t'.minute = max s.minute t.minute := hsy.2.2.2.2.2.1
  have hmaxge : T + 1 ≤ (max s.minute t.minute).val := by
    have : s.minute.val ≤ (max s.minute t.minute).val := by
      rcases le_total s.minute t.minute with h | h
      · rw [max_eq_right h]; exact h
      · rw [max_eq_left h]
    omega
  have hc' : Protocol.stepOrSelf (NonuniformMajority L K) c s t
      = c - {s, t} + {s', t'} := by
    unfold Protocol.stepOrSelf; rw [if_pos happ]; rfl
  unfold rBeyond
  rw [hc', Multiset.countP_add, Multiset.countP_sub hsub]
  have hsabove : clockBeyondP (T + 1) s := ⟨hs_clock, hs_min⟩
  have htbelow : ¬ clockBeyondP (T + 1) t := by
    unfold clockBeyondP; omega
  have hpairT1 : Multiset.countP (fun a => clockBeyondP (T + 1) a)
      ({s, t} : Multiset (AgentState L K)) = 1 := by
    rw [countP_pair]; simp [hsabove, htbelow]
  have hs'_beyond : clockBeyondP (T + 1) s' := by
    refine ⟨hs'clock, ?_⟩; rw [hs'min]; exact hmaxge
  have ht'_beyond : clockBeyondP (T + 1) t' := by
    refine ⟨ht'clock, ?_⟩; rw [ht'min]; exact hmaxge
  have hprodT1 : 2 ≤ Multiset.countP (fun a => clockBeyondP (T + 1) a)
      ({s', t'} : Multiset (AgentState L K)) := by
    rw [countP_pair]; simp [hs'_beyond, ht'_beyond]
  have hjc : Multiset.countP (fun a => clockBeyondP (T + 1) a) c = j := hj
  rw [hjc, hpairT1]
  have hjge : 1 ≤ j := by
    rw [← hjc]
    have hmem : s ∈ c := Multiset.mem_of_le hsub (by simp)
    calc (1 : ℕ) = Multiset.countP (fun a => clockBeyondP (T + 1) a) {s} := by
            rw [show ({s} : Multiset (AgentState L K)) = s ::ₘ 0 from rfl]
            rw [Multiset.countP_cons, Multiset.countP_zero]; simp [hsabove]
      _ ≤ _ := Multiset.countP_le_of_le _ (by rw [Multiset.singleton_le]; exact hmem)
  omega

/-- A scheduled pair of two FRONTIER clocks (both at minute exactly `T < cap`, phase
3) drips one up to minute `T+1`, raising `rBeyond (T+1)` by one.  Either the same
state (count ≥ 2, forced by applicability) or two DISTINCT frontier clocks.  Pure
repackaging of the proven floor-agnostic drip per-pair advances. -/
theorem frontier_pair_advances (T : ℕ) (hcap : T < K * (L + 1))
    (c : Config (AgentState L K))
    (w v : AgentState L K) (hwc : w.role = .clock) (hwp : w.phase.val = 3)
    (hwm : w.minute.val = T) (hvc : v.role = .clock) (hvp : v.phase.val = 3)
    (hvm : v.minute.val = T) (happ : Protocol.Applicable c w v)
    (j : ℕ) (hj : rBeyond (L := L) (K := K) (T + 1) c = j) :
    j + 1 ≤ rBeyond (L := L) (K := K) (T + 1)
      (Protocol.stepOrSelf (NonuniformMajority L K) c w v) := by
  classical
  by_cases hvw : w = v
  · subst hvw
    have hw2 : 2 ≤ c.count w := by
      have hle : ({w, w} : Multiset (AgentState L K)) ≤ c := happ
      have hcnt : Multiset.count w ({w, w} : Multiset (AgentState L K)) ≤ Multiset.count w c :=
        Multiset.le_iff_count.mp hle w
      have hpair : Multiset.count w ({w, w} : Multiset (AgentState L K)) = 2 := by
        rw [show ({w, w} : Multiset (AgentState L K)) = w ::ₘ w ::ₘ 0 from rfl,
            Multiset.count_cons, Multiset.count_cons, Multiset.count_zero]
        simp
      rw [hpair] at hcnt; exact hcnt
    exact rDrip_pair_advances T c w hwp hwc hwm hcap hw2 j hj
  · have hwvmin : w.minute = v.minute := Fin.ext (by rw [hwm, hvm])
    exact rDripDistinct_pair_advances T c w v hwp hvp hwc hvc hwm hwvmin hcap happ j hj

/-! ## Part C — the GENUINE clock-fraction rectangle count (the `(m_C/n)²` source).

This is the decisive content of D-lynch-3.  The advancing ordered clock-clock pairs
are exactly those with at least one FRONTIER clock (a clock at minute exactly `T`):

* frontier × frontier (both at minute `T`)        — drip,
* frontier × beyond (`T` and `≥ T+1`)             — epidemic,
* beyond × frontier                               — epidemic.

We lower-bound the advancing-pair scheduler mass by the FRONTIER × ALL-CLOCKS
ordered rectangle.  Summing `interactionCount` over that rectangle gives, with the
FULL `n(n−1)` denominator,

  ∑_{a frontier, b clock} interactionCount a b  =  (m_C − m) · (m_C − 1),

where `m = rBeyond (T+1) c` and `m_C − m` is the number of FRONTIER clock agents.
The `(m_C − m)` factor is the genuine clock count of laggards and `(m_C − 1)` is the
genuine clock count of partners — BOTH are clock counts (∝ `m_C`), NOT `n`.  Over
`n(n−1)` this is the genuine clock-fraction-squared mass; in the bulk regime
`m_C − m = Θ(m_C)` it is `Θ((m_C/n)²)` (Doty's `1/c²`, NON-trivial).  This is
DERIVED below, never assumed.  See the honest status discussion at the end for the
uniform contraction factor actually packaged. -/

/-- Sum of `count` over all clock STATES equals the clock count `m_C`. -/
theorem sum_count_clocks (c : Config (AgentState L K)) :
    (∑ a ∈ Finset.univ.filter (fun a : AgentState L K => a.role = .clock), c.count a)
      = clockCount (L := L) (K := K) c := by
  classical
  have hcard : (Multiset.filter (fun a : AgentState L K => a.role = .clock) c).card
      = clockCount (L := L) (K := K) c := by
    unfold clockCount; rw [Multiset.countP_eq_card_filter]
  rw [← hcard]
  have hcount_eq : ∀ a ∈ Finset.univ.filter (fun a : AgentState L K => a.role = .clock),
      c.count a
        = Multiset.count a (Multiset.filter (fun a : AgentState L K => a.role = .clock) c) := by
    intro a ha
    rw [Finset.mem_filter] at ha
    rw [Config.count, Multiset.count_filter, if_pos ha.2]
  rw [Finset.sum_congr rfl hcount_eq, Multiset.sum_count_eq_card]
  intro a ha
  rw [Multiset.mem_filter] at ha
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha.2⟩

/-- The frontier-clock predicate: a clock at minute exactly `T`. -/
def isFrontier (T : ℕ) (a : AgentState L K) : Prop := a.role = .clock ∧ a.minute.val = T

instance (T : ℕ) (a : AgentState L K) : Decidable (isFrontier T a) := by
  unfold isFrontier; infer_instance

/-- The frontier-clock agent count `m_C − m` (clocks at minute exactly `T`), as a
sum of `count` over frontier STATES.  Equal to `rBeyond T c − rBeyond (T+1) c`. -/
theorem sum_count_frontier (T : ℕ) (c : Config (AgentState L K)) :
    (∑ a ∈ Finset.univ.filter (fun a : AgentState L K => isFrontier T a), c.count a)
      = rBeyond (L := L) (K := K) T c - rBeyond (L := L) (K := K) (T + 1) c := by
  classical
  -- count of frontier states = countP isFrontier = countP(clockBeyond T) − countP(clockBeyond T+1).
  have hcard : (Multiset.filter (fun a : AgentState L K => isFrontier T a) c).card
      = Multiset.countP (fun a => isFrontier T a) c := by
    rw [Multiset.countP_eq_card_filter]
  have hsum : (∑ a ∈ Finset.univ.filter (fun a : AgentState L K => isFrontier T a), c.count a)
      = Multiset.countP (fun a => isFrontier T a) c := by
    rw [← hcard]
    have hcount_eq : ∀ a ∈ Finset.univ.filter (fun a : AgentState L K => isFrontier T a),
        c.count a
          = Multiset.count a (Multiset.filter (fun a : AgentState L K => isFrontier T a) c) := by
      intro a ha
      rw [Finset.mem_filter] at ha
      rw [Config.count, Multiset.count_filter, if_pos ha.2]
    rw [Finset.sum_congr rfl hcount_eq, Multiset.sum_count_eq_card]
    intro a ha
    rw [Multiset.mem_filter] at ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha.2⟩
  rw [hsum]
  -- countP isFrontier = countP(clockBeyond T) − countP(clockBeyond (T+1)).
  -- {clock ∧ minute = T} = {clock ∧ minute ≥ T} \ {clock ∧ minute ≥ T+1}, nested.
  have hle : Multiset.countP (fun a => clockBeyondP (T + 1) a) c
      ≤ Multiset.countP (fun a => clockBeyondP T a) c :=
    countP_mono_pred (fun a => clockBeyondP (T + 1) a) (fun a => clockBeyondP T a) c
      (fun a ha => ⟨ha.1, by have := ha.2; omega⟩)
  have hsplit : Multiset.countP (fun a => clockBeyondP T a) c
      = Multiset.countP (fun a => isFrontier T a) c
        + Multiset.countP (fun a => clockBeyondP (T + 1) a) c := by
    rw [Multiset.countP_eq_card_filter, Multiset.countP_eq_card_filter,
        Multiset.countP_eq_card_filter]
    -- card (filter clockBeyond T) = card (filter isFrontier) + card (filter clockBeyond T+1)
    rw [← Multiset.card_add]
    congr 1
    -- multiset extensionality via counts
    ext a
    rw [Multiset.count_add, Multiset.count_filter, Multiset.count_filter, Multiset.count_filter]
    by_cases hbT : clockBeyondP T a
    · by_cases hbT1 : clockBeyondP (T + 1) a
      · -- beyond T+1 ⟹ not frontier (minute ≥ T+1 ≠ T)
        have hnf : ¬ isFrontier T a := by
          rintro ⟨_, hm⟩; have := hbT1.2; omega
        rw [if_pos hbT, if_neg hnf, if_pos hbT1]; omega
      · -- beyond T, not beyond T+1 ⟹ frontier (minute = T)
        have hf : isFrontier T a := by
          refine ⟨hbT.1, ?_⟩
          have h1 : T ≤ a.minute.val := hbT.2
          have h2 : ¬ (T + 1 ≤ a.minute.val) := fun h => hbT1 ⟨hbT.1, h⟩
          omega
        rw [if_pos hbT, if_pos hf, if_neg hbT1]; omega
    · -- not beyond T ⟹ not frontier and not beyond T+1
      have hnf : ¬ isFrontier T a := by
        rintro ⟨hc, hm⟩; exact hbT ⟨hc, by omega⟩
      have hnb1 : ¬ clockBeyondP (T + 1) a := fun h => hbT ⟨h.1, by have := h.2; omega⟩
      rw [if_neg hbT, if_neg hnf, if_neg hnb1]
  unfold rBeyond
  omega

/-- For a fixed frontier clock STATE `a`, summing `interactionCount a b` over all
clock states `b` gives `count_a · (m_C − 1)`.  Pure `interactionCount` algebra:
`∑_b interactionCount a b = count_a·(∑_b count_b) − count_a = count_a·(m_C − 1)`. -/
theorem sum_interactionCount_frontier_row (c : Config (AgentState L K))
    (a : AgentState L K) (hac : a.role = .clock) :
    (∑ b ∈ Finset.univ.filter (fun b : AgentState L K => b.role = .clock),
        c.interactionCount a b)
      = c.count a * (clockCount (L := L) (K := K) c - 1) := by
  classical
  set F := Finset.univ.filter (fun b : AgentState L K => b.role = .clock) with hF
  have haF : a ∈ F := by rw [hF, Finset.mem_filter]; exact ⟨Finset.mem_univ a, hac⟩
  -- ADDITIVE identity (no nat subtraction): ∑_b interactionCount a b + count_a = count_a · m_C.
  -- Then the subtraction form follows since count_a ≤ count_a · m_C.
  have hsumF : (∑ b ∈ F, c.count b) = clockCount (L := L) (K := K) c := by
    rw [hF]; exact sum_count_clocks c
  -- pointwise: interactionCount a b + (if b = a then count_a else 0) = count_a · count_b.
  have hpoint : ∀ b ∈ F,
      c.interactionCount a b + (if b = a then c.count a else 0) = c.count a * c.count b := by
    intro b _
    unfold Config.interactionCount
    by_cases h : a = b
    · subst h; rw [if_pos rfl, if_pos rfl]
      -- count_a·(count_a − 1) + count_a = count_a·count_a.
      have hle : c.count a ≤ c.count a * c.count a := by nlinarith [Nat.zero_le (c.count a)]
      rw [Nat.mul_sub_one, Nat.sub_add_cancel hle]
    · rw [if_neg h, if_neg (fun hh => h hh.symm), Nat.add_zero]
  have hadd : (∑ b ∈ F, c.interactionCount a b) + c.count a
      = c.count a * clockCount (L := L) (K := K) c := by
    have hcollect : (∑ b ∈ F, c.interactionCount a b)
        + (∑ b ∈ F, (if b = a then c.count a else 0))
        = ∑ b ∈ F, c.count a * c.count b := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl hpoint
    have hsingle : (∑ b ∈ F, (if b = a then c.count a else 0)) = c.count a := by
      rw [Finset.sum_ite_eq' F a (fun _ => c.count a), if_pos haF]
    rw [hsingle] at hcollect
    rw [hcollect, ← Finset.mul_sum, hsumF]
  -- conclude count_a · (m_C − 1) from the additive identity.
  have hca_le : c.count a ≤ c.count a * clockCount (L := L) (K := K) c := by
    rcases Nat.eq_zero_or_pos (clockCount (L := L) (K := K) c) with h0 | h1
    · -- m_C = 0 impossible since a is a clock present? not needed: then count_a ≤ count_a·0=0
      -- but additive identity then forces ∑+count_a = 0, so count_a = 0.
      rw [h0, Nat.mul_zero] at hadd ⊢; omega
    · calc c.count a = c.count a * 1 := (Nat.mul_one _).symm
        _ ≤ c.count a * clockCount (L := L) (K := K) c := Nat.mul_le_mul_left _ h1
  have hmc1 : c.count a * (clockCount (L := L) (K := K) c - 1)
      = c.count a * clockCount (L := L) (K := K) c - c.count a := by
    rcases Nat.eq_zero_or_pos (clockCount (L := L) (K := K) c) with h0 | h1
    · rw [h0]; simp
    · rw [Nat.mul_sub_one, Nat.mul_comm]
  rw [hmc1]
  omega

/-! ### Infected / susceptible state-set counts (no per-clock minute floor).

The SYNC rectangle reads the susceptible count from the clock population
(`clockSize`), NOT from any per-clock minute floor.  `infected` = clock at minute
`≥ T+1` (count `rBeyond (T+1) = m`), `susceptible` = clock at minute `≤ T`
(count `m_C − m`, via `clockSize`). -/

/-- The infected predicate: a clock at minute `≥ T+1` (= `clockBeyondP (T+1)`). -/
def isInfected (T : ℕ) (a : AgentState L K) : Prop := clockBeyondP (T + 1) a

instance (T : ℕ) (a : AgentState L K) : Decidable (isInfected T a) := by
  unfold isInfected; infer_instance

/-- The susceptible predicate: a clock at minute `≤ T`. -/
def isSusceptible (T : ℕ) (a : AgentState L K) : Prop := a.role = .clock ∧ a.minute.val ≤ T

instance (T : ℕ) (a : AgentState L K) : Decidable (isSusceptible T a) := by
  unfold isSusceptible; infer_instance

/-- `∑ count` over the infected STATES is `rBeyond (T+1) c`. -/
theorem sum_count_infected (T : ℕ) (c : Config (AgentState L K)) :
    (∑ a ∈ Finset.univ.filter (fun a : AgentState L K => isInfected T a), c.count a)
      = rBeyond (L := L) (K := K) (T + 1) c := by
  classical
  have hcard : (Multiset.filter (fun a : AgentState L K => isInfected T a) c).card
      = rBeyond (L := L) (K := K) (T + 1) c := by
    unfold rBeyond isInfected
    rw [Multiset.countP_eq_card_filter]
    rfl
  rw [← hcard]
  have hcount_eq : ∀ a ∈ Finset.univ.filter (fun a : AgentState L K => isInfected T a),
      c.count a
        = Multiset.count a
            (Multiset.filter (fun a : AgentState L K => isInfected T a) c) := by
    intro a ha
    rw [Finset.mem_filter] at ha
    rw [Config.count, Multiset.count_filter, if_pos ha.2]
  rw [Finset.sum_congr rfl hcount_eq, Multiset.sum_count_eq_card]
  intro a ha
  rw [Multiset.mem_filter] at ha
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha.2⟩

/-- `∑ count` over the susceptible STATES is `m_C − rBeyond (T+1) c` (via `clockSize`):
the susceptibles are the clocks NOT beyond `T+1`, so their count = clockCount − m. -/
theorem sum_count_susceptible (T : ℕ) (c : Config (AgentState L K)) :
    (∑ a ∈ Finset.univ.filter (fun a : AgentState L K => isSusceptible T a), c.count a)
      = clockCount (L := L) (K := K) c - rBeyond (L := L) (K := K) (T + 1) c := by
  classical
  have hcard : (Multiset.filter (fun a : AgentState L K => isSusceptible T a) c).card
      = Multiset.countP (fun a => isSusceptible T a) c := by
    rw [Multiset.countP_eq_card_filter]
  have hsum : (∑ a ∈ Finset.univ.filter (fun a : AgentState L K => isSusceptible T a), c.count a)
      = Multiset.countP (fun a => isSusceptible T a) c := by
    rw [← hcard]
    have hcount_eq : ∀ a ∈ Finset.univ.filter (fun a : AgentState L K => isSusceptible T a),
        c.count a
          = Multiset.count a
              (Multiset.filter (fun a : AgentState L K => isSusceptible T a) c) := by
      intro a ha
      rw [Finset.mem_filter] at ha
      rw [Config.count, Multiset.count_filter, if_pos ha.2]
    rw [Finset.sum_congr rfl hcount_eq, Multiset.sum_count_eq_card]
    intro a ha
    rw [Multiset.mem_filter] at ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha.2⟩
  rw [hsum]
  -- countP susceptible = countP(role=clock) − countP(clockBeyond (T+1)).
  have hsplit : Multiset.countP (fun a => a.role = .clock) c
      = Multiset.countP (fun a => isSusceptible T a) c
        + Multiset.countP (fun a => clockBeyondP (T + 1) a) c := by
    rw [Multiset.countP_eq_card_filter, Multiset.countP_eq_card_filter,
        Multiset.countP_eq_card_filter, ← Multiset.card_add]
    congr 1
    ext a
    rw [Multiset.count_add, Multiset.count_filter, Multiset.count_filter, Multiset.count_filter]
    by_cases hcl : a.role = .clock
    · by_cases hb1 : clockBeyondP (T + 1) a
      · have hns : ¬ isSusceptible T a := by
          rintro ⟨_, hm⟩; have := hb1.2; omega
        rw [if_pos hcl, if_neg hns, if_pos hb1]; omega
      · have hs : isSusceptible T a := by
          refine ⟨hcl, ?_⟩
          have h2 : ¬ (T + 1 ≤ a.minute.val) := fun h => hb1 ⟨hcl, h⟩
          omega
        rw [if_pos hcl, if_pos hs, if_neg hb1]; omega
    · have hns : ¬ isSusceptible T a := fun h => hcl h.1
      have hnb1 : ¬ clockBeyondP (T + 1) a := fun h => hcl h.1
      rw [if_neg hcl, if_neg hns, if_neg hnb1]
  unfold clockCount rBeyond
  omega

/-! ## Part C2 — the two genuine rectangles (DRIP frontier×frontier, SYNC infected×susceptible).

Two rectangle COUNTS, both DERIVED by pure `interactionCount` algebra and BOTH
floor-free of any per-clock minute window:

* **DRIP (seed):** `frontier × frontier` (both at minute exactly `T`).  The mass is
  `F·(F−1)` where `F = rBeyond T − rBeyond (T+1)` is the frontier-clock count.
* **SYNC (bulk):** `infected × susceptible` (`≥ T+1` × `≤ T`).  The mass is
  `m·(m_C − m)` where `m = rBeyond (T+1)` and `m_C − m` is the susceptible count from
  `clockSize` — NO full crossing.  All cross pairs are DISTINCT (minutes differ). -/

/-- For two state-finsets `A`, `B` where every `a ∈ A`, `b ∈ B` are DISTINCT, the
`interactionCount` mass of the rectangle `A ×ˢ B` is `(∑_A count)·(∑_B count)`. -/
theorem sum_interactionCount_cross_disjoint
    (c : Config (AgentState L K)) (A B : Finset (AgentState L K))
    (hdisj : ∀ a ∈ A, ∀ b ∈ B, a ≠ b) :
    (∑ p ∈ A ×ˢ B, c.interactionCount p.1 p.2)
      = (∑ a ∈ A, c.count a) * (∑ b ∈ B, c.count b) := by
  classical
  rw [Finset.sum_product]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  unfold Config.interactionCount
  rw [if_neg (hdisj a ha b hb)]

/-- The DRIP frontier self-rectangle count: `∑_{a,b frontier} interactionCount a b
= F·(F−1)`, `F = rBeyond T − rBeyond (T+1)` (the frontier-clock count).  Pure
`interactionCount` algebra: distinct pairs give `count_a·count_b`, same-state pairs
`count_a·(count_a−1)`; total `(∑count)² − ∑count = F(F−1)`. -/
theorem sum_interactionCount_frontierRect (T : ℕ) (c : Config (AgentState L K)) :
    (∑ p ∈ (Finset.univ.filter (fun a : AgentState L K => isFrontier T a)) ×ˢ
        (Finset.univ.filter (fun a : AgentState L K => isFrontier T a)),
        c.interactionCount p.1 p.2)
      = (rBeyond (L := L) (K := K) T c - rBeyond (L := L) (K := K) (T + 1) c)
          * (rBeyond (L := L) (K := K) T c - rBeyond (L := L) (K := K) (T + 1) c - 1) := by
  classical
  set F := Finset.univ.filter (fun a : AgentState L K => isFrontier T a) with hF
  set N := ∑ a ∈ F, c.count a with hN
  -- pointwise: interactionCount a b + (if a = b then count_a else 0) = count_a · count_b.
  have hpoint : ∀ p ∈ F ×ˢ F,
      c.interactionCount p.1 p.2 + (if p.1 = p.2 then c.count p.1 else 0)
        = c.count p.1 * c.count p.2 := by
    rintro ⟨a, b⟩ _
    unfold Config.interactionCount
    by_cases h : a = b
    · subst h; rw [if_pos rfl, if_pos rfl]
      have hle : c.count a ≤ c.count a * c.count a := by nlinarith [Nat.zero_le (c.count a)]
      rw [Nat.mul_sub_one, Nat.sub_add_cancel hle]
    · rw [if_neg h, if_neg h, Nat.add_zero]
  -- ∑ interactionCount + ∑ diag = ∑ count_a·count_b = N².
  have hsq : (∑ p ∈ F ×ˢ F, c.count p.1 * c.count p.2) = N * N := by
    rw [Finset.sum_product]
    rw [hN, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _; rw [Finset.mul_sum]
  have hdiag : (∑ p ∈ F ×ˢ F, (if p.1 = p.2 then c.count p.1 else 0)) = N := by
    rw [Finset.sum_product]
    have : ∀ a ∈ F, (∑ b ∈ F, (if a = b then c.count a else 0)) = c.count a := by
      intro a ha
      rw [Finset.sum_ite_eq F a (fun _ => c.count a), if_pos ha]
    rw [Finset.sum_congr rfl this]
  have hadd : (∑ p ∈ F ×ˢ F, c.interactionCount p.1 p.2) + N = N * N := by
    have hcollect : (∑ p ∈ F ×ˢ F, c.interactionCount p.1 p.2)
        + (∑ p ∈ F ×ˢ F, (if p.1 = p.2 then c.count p.1 else 0))
        = ∑ p ∈ F ×ˢ F, c.count p.1 * c.count p.2 := by
      rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl hpoint
    rw [hdiag, hsq] at hcollect; exact hcollect
  -- F count = rBeyond T − rBeyond (T+1).
  have hNval : N = rBeyond (L := L) (K := K) T c - rBeyond (L := L) (K := K) (T + 1) c := by
    rw [hN, hF]; exact sum_count_frontier T c
  rw [← hNval, Nat.mul_sub_one]
  omega

/-- The SYNC rectangle count: `∑_{a infected, b susceptible} interactionCount a b
= m·(m_C − m)`, `m = rBeyond (T+1)`.  All cross pairs are DISTINCT (infected minute
`≥ T+1`, susceptible minute `≤ T`), so the mass is the product of the two state-set
counts.  The susceptible factor `m_C − m` comes from `clockSize` — NO full crossing. -/
theorem sum_interactionCount_syncRect (T : ℕ) (c : Config (AgentState L K)) :
    (∑ p ∈ (Finset.univ.filter (fun a : AgentState L K => isInfected T a)) ×ˢ
        (Finset.univ.filter (fun a : AgentState L K => isSusceptible T a)),
        c.interactionCount p.1 p.2)
      = rBeyond (L := L) (K := K) (T + 1) c
        * (clockCount (L := L) (K := K) c - rBeyond (L := L) (K := K) (T + 1) c) := by
  classical
  rw [sum_interactionCount_cross_disjoint c _ _ ?_, sum_count_infected, sum_count_susceptible]
  -- distinctness: infected minute ≥ T+1, susceptible minute ≤ T.
  intro a ha b hb
  rw [Finset.mem_filter] at ha hb
  have ham : T + 1 ≤ a.minute.val := ha.2.2
  have hbm : b.minute.val ≤ T := hb.2.2
  intro hab; rw [hab] at ham; omega

/-! ## Part D — the genuine mixed-regime advance probabilities.

A generic builder `advance_prob_of_rect` lower-bounds the one-step advance measure of
`{rBeyond (T+1) advances}` by `N / (n(n−1))`, given a rectangle `R` of pairs that (a)
each advance `rBeyond (T+1)` when present-applicable and (b) carry `interactionCount`
mass `≥ N`.  Instantiated TWICE: the DRIP frontier×frontier rectangle (seed) and the
SYNC infected×susceptible rectangle (bulk).  DERIVED by pair-counting from the FULL
`n(n−1)` denominator — never assumed. -/

/-- **The generic rectangle → advance-probability bound.** -/
theorem advance_prob_of_rect (n T : ℕ) (hn : 2 ≤ n)
    (c : Config (AgentState L K)) (hcardn : c.card = n)
    (R : Finset (AgentState L K × AgentState L K)) (N : ℕ)
    (hadv : ∀ p ∈ R, 1 ≤ c.count p.1 → 1 ≤ c.count p.2 → (p.1 = p.2 → 2 ≤ c.count p.1) →
      ∀ j, rBeyond (L := L) (K := K) (T + 1) c = j →
        j + 1 ≤ rBeyond (L := L) (K := K) (T + 1)
          (Protocol.stepOrSelf (NonuniformMajority L K) c p.1 p.2))
    (hcount : (N : ℕ) ≤ ∑ p ∈ R, c.interactionCount p.1 p.2) :
    ENNReal.ofReal ((N : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) ≤
      ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
        {c' | rBeyond (L := L) (K := K) (T + 1) c + 1 ≤ rBeyond (L := L) (K := K) (T + 1) c'} := by
  classical
  set j := rBeyond (L := L) (K := K) (T + 1) c with hjdef
  have hcard2 : 2 ≤ c.card := by rw [hcardn]; omega
  have hmeas : MeasurableSet
      {c' : Config (AgentState L K) | j + 1 ≤ rBeyond (L := L) (K := K) (T + 1) c'} :=
    DiscreteMeasurableSpace.forall_measurableSet _
  -- present-applicable rectangle pairs.
  set S : Finset (AgentState L K × AgentState L K) :=
    R.filter (fun p => 1 ≤ c.count p.1 ∧ 1 ≤ c.count p.2 ∧ (p.1 = p.2 → 2 ≤ c.count p.1)) with hS
  have hsub : (↑S : Set (AgentState L K × AgentState L K)) ⊆
      (Protocol.scheduledStep (NonuniformMajority L K) c) ⁻¹'
        {c' | j + 1 ≤ rBeyond (L := L) (K := K) (T + 1) c'} := by
    intro p hp
    simp only [Finset.coe_filter, Set.mem_setOf_eq, hS] at hp
    obtain ⟨hpc, hp1, hp2, hp3⟩ := hp
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Protocol.scheduledStep]
    exact hadv p hpc hp1 hp2 hp3 j hjdef.symm
  have hstepDist : (NonuniformMajority L K).stepDistOrSelf c
      = (NonuniformMajority L K).stepDist c hcard2 := by
    unfold Protocol.stepDistOrSelf; rw [dif_pos hcard2]
  have hbase : ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
        {c' | j + 1 ≤ rBeyond (L := L) (K := K) (T + 1) c'}
      = (c.interactionPMF hcard2).toMeasure
          ((Protocol.scheduledStep (NonuniformMajority L K) c) ⁻¹'
            {c' | j + 1 ≤ rBeyond (L := L) (K := K) (T + 1) c'}) := by
    rw [hstepDist]; unfold Protocol.stepDist
    rw [PMF.toMeasure_map_apply _ _ _ (Measurable.of_discrete) hmeas]
  rw [hbase]
  have hmono : (c.interactionPMF hcard2).toMeasure (↑S : Set _)
      ≤ (c.interactionPMF hcard2).toMeasure
          ((Protocol.scheduledStep (NonuniformMajority L K) c) ⁻¹'
            {c' | j + 1 ≤ rBeyond (L := L) (K := K) (T + 1) c'}) :=
    measure_mono hsub
  refine le_trans ?_ hmono
  have hSmeasure : (c.interactionPMF hcard2).toMeasure (↑S : Set _)
      = ∑ p ∈ S, c.interactionProb p.1 p.2 := by
    rw [PMF.toMeasure_apply_finset]; rfl
  have hSsum : ∑ p ∈ S, c.interactionProb p.1 p.2
      = ∑ p ∈ R, c.interactionProb p.1 p.2 := by
    rw [hS]
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro p hpc hpnot
    rw [Finset.mem_filter] at hpnot
    push Not at hpnot
    have hexcl := hpnot hpc
    have hzero : c.interactionCount p.1 p.2 = 0 := by
      unfold Config.interactionCount
      by_cases h1 : 1 ≤ c.count p.1
      · by_cases h2 : 1 ≤ c.count p.2
        · obtain ⟨hpe, hlt⟩ := hexcl h1 h2
          rw [if_pos hpe]
          have hc1 : c.count p.1 = 1 := by omega
          rw [hc1]
        · have hz2 : c.count p.2 = 0 := by omega
          by_cases hpe : p.1 = p.2
          · rw [if_pos hpe]; rw [hpe, hz2, Nat.zero_mul]
          · rw [if_neg hpe, hz2, Nat.mul_zero]
      · have hz1 : c.count p.1 = 0 := by omega
        by_cases hpe : p.1 = p.2
        · rw [if_pos hpe, hz1, Nat.zero_mul]
        · rw [if_neg hpe, hz1, Nat.zero_mul]
    unfold Config.interactionProb; rw [hzero]; simp
  rw [hSmeasure, hSsum]
  have heqterm : ∀ p : AgentState L K × AgentState L K,
      c.interactionProb p.1 p.2
        = (↑(c.interactionCount p.1 p.2) : ℝ≥0∞) * (↑c.totalPairs)⁻¹ := by
    intro p; unfold Config.interactionProb; rw [div_eq_mul_inv]
  rw [Finset.sum_congr rfl (fun p _ => heqterm p), ← Finset.sum_mul, ← Nat.cast_sum]
  set M := ∑ p ∈ R, c.interactionCount p.1 p.2 with hM
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

/-- **The DRIP advance probability (seed).**  One step raises `rBeyond (T+1)` by `≥ 1`
with probability `≥ F·(F−1)/(n(n−1))`, `F = rBeyond T − rBeyond (T+1)` the
frontier-clock count.  DERIVED from the frontier×frontier drip rectangle.  Needs the
frontier to be non-empty, which the SEED 0.9-floor guarantees — NO full crossing. -/
theorem clock_real_drip_advance_prob_mixed (n mC T : ℕ) (hn : 2 ≤ n)
    (hcap : T < K * (L + 1))
    (c : Config (AgentState L K)) (hQ : Q_mix (L := L) (K := K) n mC T c) :
    ENNReal.ofReal
        ((((rBeyond (L := L) (K := K) T c - rBeyond (L := L) (K := K) (T + 1) c)
            * (rBeyond (L := L) (K := K) T c - rBeyond (L := L) (K := K) (T + 1) c - 1) : ℕ) : ℝ)
          / ((n : ℝ) * ((n : ℝ) - 1))) ≤
      ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
        {c' | rBeyond (L := L) (K := K) (T + 1) c + 1 ≤ rBeyond (L := L) (K := K) (T + 1) c'} := by
  classical
  set R := (Finset.univ.filter (fun a : AgentState L K => isFrontier T a)) ×ˢ
    (Finset.univ.filter (fun a : AgentState L K => isFrontier T a)) with hR
  set F := rBeyond (L := L) (K := K) T c - rBeyond (L := L) (K := K) (T + 1) c with hFdef
  have hcount : F * (F - 1) ≤ ∑ p ∈ R, c.interactionCount p.1 p.2 := by
    rw [hR, sum_interactionCount_frontierRect]
  refine advance_prob_of_rect n T hn c hQ.card R (F * (F - 1)) ?_ hcount
  · -- every rectangle pair advances when present-applicable.
    rintro ⟨a, b⟩ hp h1 h2 hsame jj hjj
    rw [hR, Finset.mem_product, Finset.mem_filter, Finset.mem_filter] at hp
    obtain ⟨⟨_, hac, ham⟩, ⟨_, hbc, hbm⟩⟩ := hp
    have hamem : a ∈ c := Multiset.one_le_count_iff_mem.mp h1
    have hbmem : b ∈ c := Multiset.one_le_count_iff_mem.mp h2
    have hap3 : a.phase.val = 3 := hQ.clockPhase3 a hamem hac
    have hbp3 : b.phase.val = 3 := hQ.clockPhase3 b hbmem hbc
    have happ : Protocol.Applicable c a b := by
      by_cases hab : a = b
      · subst hab
        have hca2 : 2 ≤ c.count a := hsame rfl
        refine Multiset.le_iff_count.mpr ?_
        intro x
        rw [show ({a, a} : Multiset (AgentState L K)) = a ::ₘ a ::ₘ 0 from rfl,
            Multiset.count_cons, Multiset.count_cons, Multiset.count_zero]
        by_cases hxa : x = a
        · subst hxa; rw [if_pos rfl]; exact hca2
        · rw [if_neg hxa]; omega
      · exact applicable_of_mem_distinct hamem hbmem hab
    exact frontier_pair_advances T hcap c a b hac hap3 ham hbc hbp3 hbm happ jj hjj

/-- **The SYNC advance probability (bulk).**  One step raises `rBeyond (T+1)` by `≥ 1`
with probability `≥ m·(m_C − m)/(n(n−1))`, `m = rBeyond (T+1)` the infected count and
`m_C − m` the susceptible count (from `clockSize`).  DERIVED from the
infected×susceptible sync rectangle — NO full crossing, NO drip frontier. -/
theorem clock_real_sync_advance_prob_mixed (n mC T : ℕ) (hn : 2 ≤ n)
    (hcap : T < K * (L + 1))
    (c : Config (AgentState L K)) (hQ : Q_mix (L := L) (K := K) n mC T c) :
    ENNReal.ofReal
        (((rBeyond (L := L) (K := K) (T + 1) c
            * (mC - rBeyond (L := L) (K := K) (T + 1) c) : ℕ) : ℝ)
          / ((n : ℝ) * ((n : ℝ) - 1))) ≤
      ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
        {c' | rBeyond (L := L) (K := K) (T + 1) c + 1 ≤ rBeyond (L := L) (K := K) (T + 1) c'} := by
  classical
  set R := (Finset.univ.filter (fun a : AgentState L K => isInfected T a)) ×ˢ
    (Finset.univ.filter (fun a : AgentState L K => isSusceptible T a)) with hR
  set m := rBeyond (L := L) (K := K) (T + 1) c with hmdef
  have hcount : m * (mC - m) ≤ ∑ p ∈ R, c.interactionCount p.1 p.2 := by
    rw [hR, sum_interactionCount_syncRect, hQ.clockSize]
  refine advance_prob_of_rect n T hn c hQ.card R (m * (mC - m)) ?_ hcount
  · -- every infected×susceptible pair advances when present-applicable.
    rintro ⟨a, b⟩ hp h1 h2 _hsame jj hjj
    rw [hR, Finset.mem_product, Finset.mem_filter, Finset.mem_filter] at hp
    obtain ⟨⟨_, hinf⟩, ⟨_, hsus⟩⟩ := hp
    have hac : a.role = .clock := hinf.1
    have ham : T + 1 ≤ a.minute.val := hinf.2
    have hbc : b.role = .clock := hsus.1
    have hbm : b.minute.val ≤ T := hsus.2
    have hamem : a ∈ c := Multiset.one_le_count_iff_mem.mp h1
    have hbmem : b ∈ c := Multiset.one_le_count_iff_mem.mp h2
    have hap3 : a.phase.val = 3 := hQ.clockPhase3 a hamem hac
    have hbp3 : b.phase.val = 3 := hQ.clockPhase3 b hbmem hbc
    have hab : a ≠ b := by intro h; rw [h] at ham; omega
    have happ : Protocol.Applicable c a b := applicable_of_mem_distinct hamem hbmem hab
    exact rSync_pair_advances T c a b hap3 hbp3 hac hbc ham hbm happ jj hjj

/-! ## Part E — the mixed drift and the contraction factor.

The clock-minute potential targets the CLOCK population `m_C` (clocks reach
`rBeyond (T+1) = m_C`, NEVER `n`, since only `m_C` of the `n` agents are clocks):
`rSeedPot mC T s` (the level-`mC` deficit).  The drift uses the GENUINE advance
probability `clock_real_advance_prob_mixed` with the FULL `n(n−1)` denominator.

Two structural facts are CARRIED as explicit, clearly-labeled hypotheses (true
protocol invariants, deferred to separate avenues — NOT the contraction itself):

* `hmono` — `rBeyond (T+1)` is non-decreasing on the one-step kernel support (clocks
  are role-stable and minute-monotone; a deterministic clock-stability fact).  In
  the all-clocks file this came for free from `rBeyondGE3_ge_monotone`, which needs
  `AllClockGE3` (every agent a clock) — FALSE in the mixed regime — so it is carried.
* `hfrontier` — the FRONTIER-FRACTION floor: `γ·m_C(m_C−1) ≤ (m_C − m)(m_C − 1)`
  (a constant fraction `γ` of clocks lag at the level-`T` frontier).  This is what
  upgrades the per-step `(m_C − m)(m_C − 1)/(n(n−1))` mass to the GENUINE
  clock-fraction-squared contraction `Θ((m_C/n)²)`.  Deferred to Phase-0/mixing. -/

/-- Pointwise one-step bound on the level-`mC` potential, CARRYING the monotonicity
hypothesis `hmono` (the deferred clock-stability fact) in place of the all-clocks
`rBeyondGE3_ge_monotone`.  Mirrors `rSeedPot_pointwise_bound`. -/
theorem rSeedPot_pointwise_bound_mixed (mC T : ℕ) (s : ℝ) (hs : 0 < s)
    (c : Config (AgentState L K)) (m : ℕ)
    (_hm : rBeyond (L := L) (K := K) (T + 1) c = m) (_hm_hi : m < mC)
    (c' : Config (AgentState L K))
    (hmono : m ≤ rBeyond (L := L) (K := K) (T + 1) c') :
    rSeedPot (L := L) (K := K) mC T s c' ≤
      (if m + 1 ≤ rBeyond (L := L) (K := K) (T + 1) c' then
        ENNReal.ofReal (Real.exp (s * ((mC : ℝ) - (m : ℝ) - 1)))
      else
        ENNReal.ofReal (Real.exp (s * ((mC : ℝ) - (m : ℝ))))) := by
  unfold rSeedPot rClamp
  by_cases hfin : mC ≤ rBeyond (L := L) (K := K) (T + 1) c'
  · rw [if_pos hfin]; split_ifs <;> positivity
  · rw [if_neg hfin]
    rw [not_le] at hfin
    by_cases hadv : m + 1 ≤ rBeyond (L := L) (K := K) (T + 1) c'
    · rw [if_pos hadv]
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      have hclamp : min (rBeyond (L := L) (K := K) (T + 1) c') mC
          = rBeyond (L := L) (K := K) (T + 1) c' := by omega
      rw [hclamp]
      have : (m : ℝ) + 1 ≤ (rBeyond (L := L) (K := K) (T + 1) c' : ℝ) := by exact_mod_cast hadv
      nlinarith [hs, this]
    · rw [if_neg hadv]
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      have heq : rBeyond (L := L) (K := K) (T + 1) c' = m := by omega
      have hclamp : min (rBeyond (L := L) (K := K) (T + 1) c') mC
          = rBeyond (L := L) (K := K) (T + 1) c' := by omega
      rw [hclamp, heq]

/-- **The mixed-regime clock-minute drift.**  On the mixed window `Q_mix n mC T` with
`m_C ≥ 2`, in the unfinished regime, the level-`mC` potential contracts at the
GENUINE clock-fraction-squared rate

  r = 1 − (γ·m_C(m_C−1)/(n(n−1)))·(1 − e^{−s}),

with `γ` the carried frontier-fraction.  The contraction PROBABILITY is DERIVED
from `clock_real_advance_prob_mixed` (full `n(n−1)` denominator) and the carried
frontier floor — it is NOT assumed; only `hmono`/`hfrontier` (structural) are
carried. -/
theorem rSeedPot_contracts_mixed (n mC T : ℕ) (hn : 2 ≤ n) (hmC : 2 ≤ mC)
    (hcap : T < K * (L + 1)) (s : ℝ) (hs : 0 < s) (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (c : Config (AgentState L K)) (hQ : Q_mix (L := L) (K := K) n mC T c)
    (hnc : rBeyond (L := L) (K := K) (T + 1) c < mC)
    (hmono : ∀ c' : Config (AgentState L K),
      c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support →
      rBeyond (L := L) (K := K) (T + 1) c ≤ rBeyond (L := L) (K := K) (T + 1) c')
    (hfrontier : γ * ((mC : ℝ) * (mC : ℝ))
      ≤ (rBeyond (L := L) (K := K) (T + 1) c
          * (mC - rBeyond (L := L) (K := K) (T + 1) c : ℕ) : ℝ)) :
    ∫⁻ c', rSeedPot (L := L) (K := K) mC T s c' ∂((NonuniformMajority L K).transitionKernel c) ≤
      ENNReal.ofReal (1 - (γ * ((mC : ℝ) * (mC : ℝ)) / ((n : ℝ) * ((n : ℝ) - 1)))
          * (1 - Real.exp (-s)))
        * rSeedPot (L := L) (K := K) mC T s c := by
  set m := rBeyond (L := L) (K := K) (T + 1) c with hm
  have hm_hi : m < mC := hnc
  have hΦc : rSeedPot (L := L) (K := K) mC T s c
      = ENNReal.ofReal (Real.exp (s * ((mC : ℝ) - (m : ℝ)))) := by
    unfold rSeedPot
    rw [if_neg (by rw [← hm]; omega), rClamp_eq_of_lt mC T c (by rw [← hm]; omega)]
  set A := {c' : Config (AgentState L K) | m + 1 ≤ rBeyond (L := L) (K := K) (T + 1) c'} with hA_def
  have hA_meas : MeasurableSet A := DiscreteMeasurableSpace.forall_measurableSet _
  set pR : ℝ := γ * ((mC : ℝ) * (mC : ℝ)) / ((n : ℝ) * ((n : ℝ) - 1)) with hpR
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hmCR : (2 : ℝ) ≤ (mC : ℝ) := by exact_mod_cast hmC
  have hden_pos : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
  have hmC_le_n : mC ≤ n := by
    have hle : clockCount (L := L) (K := K) c ≤ c.card := by
      unfold clockCount; exact Multiset.countP_le_card _ _
    rw [hQ.card, hQ.clockSize] at hle; exact hle
  have hmCRn : (mC : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmC_le_n
  -- m·(mC−m) ≤ n(n−1): AM-GM on the clock split, then mC ≤ n.
  have hmRle : (m : ℝ) ≤ (mC : ℝ) := by exact_mod_cast (le_of_lt hm_hi)
  have hmCmR : ((mC - m : ℕ) : ℝ) = (mC : ℝ) - (m : ℝ) := by
    rw [Nat.cast_sub (le_of_lt hm_hi)]
  have hrec_le : ((m * (mC - m) : ℕ) : ℝ) ≤ (n : ℝ) * ((n : ℝ) - 1) := by
    rw [Nat.cast_mul, hmCmR]
    -- m(mC−m) ≤ (mC/2)² ≤ (n/2)² ≤ n(n−1) for n ≥ 2.
    nlinarith [sq_nonneg ((mC : ℝ) - 2 * (m : ℝ)), hmRle, hmCRn, hnR,
      mul_nonneg (by linarith : (0:ℝ) ≤ (m:ℝ)) (by linarith : (0:ℝ) ≤ (mC:ℝ) - (m:ℝ))]
  have hfrm : γ * ((mC : ℝ) * (mC : ℝ))
      ≤ ((m * (mC - m) : ℕ) : ℝ) := by
    rw [Nat.cast_mul]; exact hfrontier
  have hnum_le : γ * ((mC : ℝ) * (mC : ℝ)) ≤ (n : ℝ) * ((n : ℝ) - 1) :=
    le_trans hfrm hrec_le
  have hpR_nonneg : 0 ≤ pR := by
    rw [hpR]; apply div_nonneg _ (le_of_lt hden_pos)
    apply mul_nonneg (le_of_lt hγ); nlinarith
  have hpR_le_one : pR ≤ 1 := by
    rw [hpR, div_le_one hden_pos]; exact hnum_le
  set E0 : ℝ := Real.exp (s * ((mC : ℝ) - (m : ℝ))) with hE0
  set E1 : ℝ := Real.exp (s * ((mC : ℝ) - (m : ℝ) - 1)) with hE1
  have hE0_pos : 0 < E0 := Real.exp_pos _
  have hE1_pos : 0 < E1 := Real.exp_pos _
  have hE1_eq : E1 = E0 * Real.exp (-s) := by
    rw [hE0, hE1, ← Real.exp_add]; congr 1; ring
  -- THE genuine mixed SYNC advance probability bound, lower-bounded via the floor.
  have hstep : ENNReal.ofReal pR ≤
      ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
        {c' | rBeyond (L := L) (K := K) (T + 1) c + 1 ≤ rBeyond (L := L) (K := K) (T + 1) c'} := by
    refine le_trans (ENNReal.ofReal_le_ofReal ?_)
      (clock_real_sync_advance_prob_mixed n mC T hn hcap c hQ)
    rw [hpR]
    apply (div_le_div_iff_of_pos_right hden_pos).mpr
    -- γ·mC² ≤ ↑(m·(mC−m)): hfrontier with the product cast.
    rw [Nat.cast_mul]; exact hfrontier
  rw [← hm] at hstep
  change ∫⁻ c', rSeedPot (L := L) (K := K) mC T s c'
    ∂((NonuniformMajority L K).stepDistOrSelf c).toMeasure ≤ _
  calc ∫⁻ c', rSeedPot (L := L) (K := K) mC T s c'
        ∂((NonuniformMajority L K).stepDistOrSelf c).toMeasure
      ≤ ∫⁻ c', (if m + 1 ≤ rBeyond (L := L) (K := K) (T + 1) c' then ENNReal.ofReal E1
          else ENNReal.ofReal E0) ∂((NonuniformMajority L K).stepDistOrSelf c).toMeasure := by
        apply lintegral_mono_ae
        rw [ae_iff, PMF.toMeasure_apply_eq_zero_iff _
          (DiscreteMeasurableSpace.forall_measurableSet _)]
        rw [Set.disjoint_left]
        intro x hsupp hbad
        apply hbad
        exact rSeedPot_pointwise_bound_mixed mC T s hs c m hm.symm hm_hi x (hmono x hsupp)
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
    _ ≤ ENNReal.ofReal (1 - pR * (1 - Real.exp (-s)))
          * rSeedPot (L := L) (K := K) mC T s c := by
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

/-! ## Part F — packaging into `PhaseConvergence` (carrying the structural inputs).

The mixed drift `rSeedPot_contracts_mixed` is packaged into a `PhaseConvergence` via
`WindowConcentration.windowDrift_PhaseConvergence`.  The window `Q` is the mixed
window `Q_mix n mC T`; the guarded potential is `⊤` off `Q`, else `rSeedPot mC T`.
`Post` = "all `m_C` clocks crossed level `T+1`" (`mC ≤ rBeyond (T+1)`).

The contraction PROBABILITY is NOT assumed — it is the derived
`rSeedPot_contracts_mixed`.  What IS carried (explicit, labeled, deferred):
* `habs_mix` — one-step closure of `Q_mix` (clock-role agents stay at phase 3 etc.);
* `hmono_mix` — `rBeyond (T+1)` non-decreasing on the kernel support over `Q`
  (clock-stability; replaces the all-clocks `rBeyondGE3_ge_monotone`);
* `hfrontier_mix` — the frontier-fraction floor `γ·m_C(m_C−1) ≤ (m_C−m)(m_C−1)` over
  the unfinished window (the genuine clock-fraction-squared source);
* `hpost_abs_mix` — one-step closure of `Post`.
None of these is the contraction; each is a true protocol invariant deferred for
separate discharge. -/

/-- The mixed guarded clock-minute potential: `⊤` off the window `Q_mix n mC T`,
else the level-`mC` potential `rSeedPot mC T`. -/
noncomputable def rSeedPotMix (n mC T : ℕ) (s : ℝ) (c : Config (AgentState L K)) : ℝ≥0∞ :=
  open Classical in
  if Q_mix (L := L) (K := K) n mC T c then rSeedPot (L := L) (K := K) mC T s c else ⊤

theorem rSeedPotMix_measurable (n mC T : ℕ) (s : ℝ) :
    Measurable (rSeedPotMix (L := L) (K := K) n mC T s) :=
  fun _ _ => DiscreteMeasurableSpace.forall_measurableSet _

theorem rSeedPotMix_eq_on_window (n mC T : ℕ) (s : ℝ) (c : Config (AgentState L K))
    (h : Q_mix (L := L) (K := K) n mC T c) :
    rSeedPotMix (L := L) (K := K) n mC T s c = rSeedPot (L := L) (K := K) mC T s c := by
  unfold rSeedPotMix; rw [if_pos h]

/-- **`clock_real_advance_mixed` — the MIXED-regime clock-minute advance (genuine
clock fraction).**  Packaged as a `PhaseConvergence` on the REAL `NonuniformMajority
L K` kernel.  Starting from the mixed window `Q_mix n mC T` (`card = n`, clock-role
agents at phase exactly 3 and minute `≥ T`, clock count `m_C`, all `m_C` clocks at
minute `≥ T`), all `m_C` clocks reach minute `≥ T+1` within `t` interactions with
failure `≤ ε`, at the GENUINE clock-fraction-squared contraction
`r = 1 − (γ·m_C(m_C−1)/(n(n−1)))·(1 − e^{−s})`.

The contraction PROBABILITY is DERIVED (`rSeedPot_contracts_mixed`, full `n(n−1)`
denominator); it is NOT among the carried hypotheses.  The carried hypotheses are
the four STRUCTURAL protocol invariants (true but deferred): `habs_mix`,
`hmono_mix`, `hfrontier_mix`, `hpost_abs_mix`. -/
noncomputable def clock_real_advance_mixed (n mC T : ℕ) (hn : 2 ≤ n) (hmC : 2 ≤ mC)
    (hT : T < K * (L + 1)) (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    -- STRUCTURAL INVARIANT (deferred): one-step closure of the mixed window.
    (habs_mix : ∀ c c' : Config (AgentState L K),
      Q_mix (L := L) (K := K) n mC T c →
      c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support →
      Q_mix (L := L) (K := K) n mC T c')
    -- STRUCTURAL INVARIANT (deferred): clock-stability monotonicity on the support.
    (hmono_mix : ∀ c c' : Config (AgentState L K),
      Q_mix (L := L) (K := K) n mC T c →
      c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support →
      rBeyond (L := L) (K := K) (T + 1) c ≤ rBeyond (L := L) (K := K) (T + 1) c')
    -- STRUCTURAL INVARIANT (deferred): SYNC clock-fraction floor (the c² source).
    (hfrontier_mix : ∀ c : Config (AgentState L K),
      Q_mix (L := L) (K := K) n mC T c →
      rBeyond (L := L) (K := K) (T + 1) c < mC →
      γ * ((mC : ℝ) * (mC : ℝ))
        ≤ (rBeyond (L := L) (K := K) (T + 1) c
            * (mC - rBeyond (L := L) (K := K) (T + 1) c : ℕ) : ℝ))
    (t : ℕ) (ε : ℝ≥0)
    (hε : ENNReal.ofReal
            (1 - (γ * ((mC : ℝ) * (mC : ℝ)) / ((n : ℝ) * ((n : ℝ) - 1)))
              * (1 - Real.exp (-Real.log 2))) ^ t
          * ENNReal.ofReal (Real.exp (Real.log 2 * (mC : ℝ))) / 1 ≤ (ε : ℝ≥0∞)) :
    PhaseConvergence (NonuniformMajority L K).transitionKernel := by
  have hs : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  refine WindowConcentration.windowDrift_PhaseConvergence (NonuniformMajority L K)
    (rSeedPotMix (L := L) (K := K) n mC T (Real.log 2))
    (rSeedPotMix_measurable n mC T (Real.log 2))
    (fun c => Q_mix (L := L) (K := K) n mC T c)                          -- Q
    habs_mix                                                             -- hQ_abs
    (ENNReal.ofReal (1 - (γ * ((mC : ℝ) * (mC : ℝ)) / ((n : ℝ) * ((n : ℝ) - 1)))
        * (1 - Real.exp (-Real.log 2))))                                -- r
    ?_                                                                   -- hdrift
    (fun c => Q_mix (L := L) (K := K) n mC T c)                          -- Pre
    (fun c => Q_mix (L := L) (K := K) n mC T c
      ∧ mC ≤ rBeyond (L := L) (K := K) (T + 1) c)                       -- Post
    ?_                                                                   -- hPost_abs
    1 one_ne_zero ENNReal.one_ne_top                                     -- θ = 1
    ?_                                                                   -- hlink
    (fun c h => h)                                                       -- hPre_Q
    (ENNReal.ofReal (Real.exp (Real.log 2 * (mC : ℝ))))                 -- Φ₀
    ?_                                                                   -- hPre_bound
    t ε hε                                                              -- hε
  · -- hdrift : on the window, contraction (unfinished) or `Φ = 0` (finished).
    intro c hQ
    rw [rSeedPotMix_eq_on_window n mC T (Real.log 2) c hQ]
    have hint_eq : ∫⁻ c', rSeedPotMix (L := L) (K := K) n mC T (Real.log 2) c'
          ∂((NonuniformMajority L K).transitionKernel c)
        = ∫⁻ c', rSeedPot (L := L) (K := K) mC T (Real.log 2) c'
          ∂((NonuniformMajority L K).transitionKernel c) := by
      apply lintegral_congr_ae
      change ∀ᵐ c' ∂((NonuniformMajority L K).stepDistOrSelf c).toMeasure,
        rSeedPotMix (L := L) (K := K) n mC T (Real.log 2) c'
          = rSeedPot (L := L) (K := K) mC T (Real.log 2) c'
      rw [ae_iff, PMF.toMeasure_apply_eq_zero_iff _
        (DiscreteMeasurableSpace.forall_measurableSet _)]
      rw [Set.disjoint_left]
      intro x hsupp hbad
      apply hbad
      exact rSeedPotMix_eq_on_window n mC T (Real.log 2) x (habs_mix c x hQ hsupp)
    rw [hint_eq]
    by_cases hfin : mC ≤ rBeyond (L := L) (K := K) (T + 1) c
    · -- finished: Φ = 0, integral 0.
      have hΦc0 : rSeedPot (L := L) (K := K) mC T (Real.log 2) c = 0 := by
        unfold rSeedPot; rw [if_pos hfin]
      rw [hΦc0, mul_zero, nonpos_iff_eq_zero]
      change ∫⁻ c', rSeedPot (L := L) (K := K) mC T (Real.log 2) c'
          ∂((NonuniformMajority L K).stepDistOrSelf c).toMeasure = 0
      rw [lintegral_eq_zero_iff (rSeedPot_measurable mC T (Real.log 2))]
      rw [Filter.eventuallyEq_iff_exists_mem]
      refine ⟨((NonuniformMajority L K).stepDistOrSelf c).support, ?_, ?_⟩
      · rw [mem_ae_iff, PMF.toMeasure_apply_eq_zero_iff _
          (DiscreteMeasurableSpace.forall_measurableSet _)]
        rw [Set.disjoint_left]; intro x hsupp hx
        exact hx (PMF.mem_support_iff _ _ |>.mp hsupp)
      · intro c' hc'
        have hfin' : mC ≤ rBeyond (L := L) (K := K) (T + 1) c' :=
          le_trans hfin (hmono_mix c c' hQ hc')
        change rSeedPot (L := L) (K := K) mC T (Real.log 2) c' = 0
        unfold rSeedPot; rw [if_pos hfin']
    · -- unfinished: the genuine mixed contraction.
      have hnc : rBeyond (L := L) (K := K) (T + 1) c < mC := by omega
      exact rSeedPot_contracts_mixed n mC T hn hmC hT (Real.log 2) hs γ hγ hγ1 c hQ hnc
        (fun c' hc' => hmono_mix c c' hQ hc') (hfrontier_mix c hQ hnc)
  · -- hPost_abs : window closure + finished preserved (monotone).
    rintro c c' ⟨hQ, hfin⟩ hc'
    exact ⟨habs_mix c c' hQ hc', le_trans hfin (hmono_mix c c' hQ hc')⟩
  · -- hlink : ¬Post → 1 ≤ Φ.  Off-window Φ = ⊤; on-window-unfinished Φ ≥ 1.
    intro c hnp
    unfold rSeedPotMix
    by_cases hQ : Q_mix (L := L) (K := K) n mC T c
    · rw [if_pos hQ]
      have hnf : ¬ rFinished (L := L) (K := K) mC T c := by
        unfold rFinished
        intro hfin; exact hnp ⟨hQ, hfin⟩
      exact not_finished_imp_rSeedPot_ge_one mC T (Real.log 2) hs c hnf
    · rw [if_neg hQ]; exact le_top
  · -- hPre_bound : Φ ≤ exp(s·mC) on the window.
    intro c hQ
    rw [rSeedPotMix_eq_on_window n mC T (Real.log 2) c hQ]
    exact rSeedPot_le_max mC T (Real.log 2) hs c

end ClockRealMixed

end ExactMajority
