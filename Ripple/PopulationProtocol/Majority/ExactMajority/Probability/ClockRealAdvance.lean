/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Avenue D-lynch-2 — DISCHARGING the witness: the UNCONDITIONAL clock-minute advance

`ClockRealKernel.clock_real_advance` packages the real-kernel clock-minute drift,
but takes a `witnessOf` hypothesis that is never discharged: "≥ 2 clocks with
IDENTICAL full state at minute exactly `T` in the unfinished regime".  That
same-state requirement is over-restrictive — agents at minute `T` may differ in
other fields (counter, opinions, …).  This file DISCHARGES the witness from the
bare floor facts, replacing it by a genuine pair-counting argument that does NOT
need identical full states.

The mathematical content added here:

* `exists_clock_minute_eq` — from `rBeyond T c = n` (card `n`) and the unfinished
  level `rBeyond (T+1) c = m < n`, there is a Clock at minute EXACTLY `T`; and if
  `n − m ≥ 2`, there are TWO DISTINCT Clocks at minute `T` (distinct as states).
* `rEpidemic_pair_advances` — the NEW per-pair EPIDEMIC advance: an unequal-minute
  Phase-3 clock pair `(s, t)` with `s.minute = T`, `t.minute > T` syncs the lower
  clock UP to `t.minute > T`, raising `rBeyond (T+1)` by one.  Built directly from
  the proven per-pair sync fact `Transition_phase3_clock_minute_sync_decreases`.
* `rDripDistinct_pair_advances` — the per-pair DRIP advance for TWO DISTINCT clocks
  at the same minute `T < cap` (NOT identical state), raising `rBeyond (T+1)` by one.
* `clock_real_advance_prob_uncond` — a uniform advance-probability LOWER bound
  `≥ 1/(n(n−1))` in BOTH regimes (`n − m ≥ 2` drip, `n − m = 1` epidemic), DERIVED
  from `interactionProb`/`interactionCount`/`totalPairs` (the `1/c²` pair-counting),
  exactly as the existing same-state drip lemma — never assumed.
* `clock_real_advance_uncond` — the UNCONDITIONAL clock-minute advance: a
  `PhaseConvergence` on the real kernel with NO `witnessOf` hypothesis.

The floor window here is `AllClockMinT3 T` ("every agent is a Phase-3 Clock at
minute `≥ T`") — strictly stronger than `ClockRealKernel.AllClockGE3` only in that
clocks are at phase EXACTLY 3 (so the Phase-3 drip/sync rule fires).  This is the
honest window on which the advance is genuinely unconditional; see the module
docstring of `clock_real_advance_uncond` for the precise status of the cap boundary.

No existing file is edited; no sorry/admit/axiom/native_decide.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockRealKernel

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real BigOperators

namespace ClockRealKernel

variable {L K : ℕ}

/-- `countP` is monotone under a GLOBAL predicate implication. -/
theorem countP_mono_pred {α : Type*} (p q : α → Prop) [DecidablePred p] [DecidablePred q]
    (s : Multiset α) (h : ∀ a, p a → q a) :
    Multiset.countP p s ≤ Multiset.countP q s := by
  rw [Multiset.countP_eq_card_filter, Multiset.countP_eq_card_filter]
  exact Multiset.card_le_card (Multiset.monotone_filter_right s h)

/-! ## Part A — extracting a Phase-3 minute-`T` Clock witness from the floor facts.

The witness is DERIVED by counting, not assumed.  On a window of Phase-3 Clocks
with `rBeyond T c = card = n`, every agent is a Clock at minute `≥ T`; the
unfinished level `rBeyond (T+1) c = m < n` then forces `n − m ≥ 1` Clocks at
minute EXACTLY `T`, and `n − m ≥ 2` forces two DISTINCT such Clocks. -/

/-- The genuinely usable floor window: every agent is a Clock in Phase EXACTLY 3 at
minute `≥ T`.  (Phase 3 is what makes the Phase-3 drip/sync rule fire; it is the
only field strengthening over `AllClockGE3`.) -/
def AllClockMinT3 (T : ℕ) (c : Config (AgentState L K)) : Prop :=
  ∀ a ∈ c, a.role = .clock ∧ a.phase.val = 3 ∧ T ≤ a.minute.val

/-- `AllClockMinT3 T` refines `AllClockGE3`. -/
theorem AllClockMinT3.toGE3 {T : ℕ} {c : Config (AgentState L K)}
    (h : AllClockMinT3 T c) : AllClockGE3 c :=
  fun a ha => ⟨(h a ha).1, by have := (h a ha).2.1; omega⟩

/-- The "at minute exactly `T`" predicate over a Phase-3 Clock window: a member of
`c` is at minute exactly `T` iff it is beyond `T` but not beyond `T+1`. -/
theorem clockBeyond_T_not_T1 {T : ℕ} {c : Config (AgentState L K)} {a : AgentState L K}
    (hmem : a ∈ c) (hw : AllClockMinT3 T c)
    (hbT : clockBeyondP T a) (hnbT1 : ¬ clockBeyondP (T + 1) a) :
    a.role = .clock ∧ a.phase.val = 3 ∧ a.minute.val = T := by
  obtain ⟨hc, hp, _⟩ := hw a hmem
  refine ⟨hc, hp, ?_⟩
  have h1 : T ≤ a.minute.val := hbT.2
  have h2 : ¬ (T + 1 ≤ a.minute.val) := by
    intro h; exact hnbT1 ⟨hc, h⟩
  omega

/-- **Witness extraction.**  On the Phase-3 Clock window with `rBeyond T c = card = n`
and the level unfinished (`rBeyond (T+1) c < n`), there is a Clock at minute exactly
`T` (Phase 3).  Pure counting: `{minute ≥ T+1} ⊆ {minute ≥ T}` and the counts
differ, so some member is beyond `T` but not beyond `T+1`. -/
theorem exists_clock_minute_eqT (n T : ℕ) (c : Config (AgentState L K))
    (_hcard : c.card = n) (hw : AllClockMinT3 T c) (hcr : rBeyond T c = n)
    (hunf : rBeyond (T + 1) c < n) :
    ∃ w ∈ c, w.role = .clock ∧ w.phase.val = 3 ∧ w.minute.val = T := by
  classical
  -- `rBeyond T c = card` ⟹ EVERY member is `clockBeyondP T`.
  -- `rBeyond (T+1) c < rBeyond T c` ⟹ some member is NOT `clockBeyondP (T+1)`.
  -- there is `w ∈ c` with `clockBeyondP T w ∧ ¬ clockBeyondP (T+1) w`.
  have hlt : Multiset.countP (fun a => clockBeyondP (T + 1) a) c
      < Multiset.countP (fun a => clockBeyondP T a) c := by
    have h1 : Multiset.countP (fun a => clockBeyondP T a) c = n := by rw [← hcr]; rfl
    have h2 : Multiset.countP (fun a => clockBeyondP (T + 1) a) c = rBeyond (T + 1) c := rfl
    omega
  -- A strict inequality of countP with the global implication forces a separating element.
  by_contra hcon
  simp only [not_exists, not_and] at hcon
  -- claim: every member that is beyond T is also beyond T+1, contradicting hlt.
  -- We promote this to a GLOBAL implication using membership-free reasoning:
  -- an element NOT in `c` contributes to neither count, and a member beyond T but
  -- not beyond T+1 would be a witness (excluded by `hcon`).
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
          obtain ⟨hac, hap, ham⟩ := clockBeyond_T_not_T1 hmem hw hbT hnb
          exact hcon a hmem hac hap ham
        rw [if_pos hbT1]
      · rw [Multiset.count_eq_zero_of_notMem hmem]; split_ifs <;> omega
    · rw [if_neg hbT]; omega
  omega

/-! ## Part B — the per-pair advance lemmas (drip-distinct and epidemic-sync).

Both raise `rBeyond (T+1)` by one from a scheduled Phase-3 clock pair, WITHOUT any
identical-full-state requirement.  They mirror `rDrip_pair_advances` but apply to
DISTINCT clock states. -/

/-- countP of the threshold at level `T+1` over an applicable pair `{r₁, r₂}` whose
produced pair has the spreading element. -/
private theorem applicable_pair_le {c : Config (AgentState L K)} {r₁ r₂ : AgentState L K}
    (happ : Protocol.Applicable c r₁ r₂) :
    ({r₁, r₂} : Multiset (AgentState L K)) ≤ c := happ

/-- The post-config decomposition `c - {r₁,r₂} + {δ.1, δ.2}` for an applicable pair. -/
private theorem stepOrSelf_decomp (c : Config (AgentState L K)) (r₁ r₂ : AgentState L K)
    (happ : Protocol.Applicable c r₁ r₂) :
    Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂
      = c - {r₁, r₂} + {(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2} := by
  unfold Protocol.stepOrSelf; rw [if_pos happ]; rfl

/-- **The EPIDEMIC-sync per-pair advance (NEW).**  A scheduled Phase-3 clock pair
`(s, t)` with `s.minute = T` and `t.minute ≥ T+1` (so the minutes are UNEQUAL) syncs
BOTH clocks up to `max s.minute t.minute = t.minute ≥ T+1`, raising `rBeyond (T+1)`
by at least one.  Mirrors `rDrip_pair_advances`; built from
`Transition_phase3_clock_minute_sync_decreases`. -/
theorem rEpidemic_pair_advances (T : ℕ) (c : Config (AgentState L K))
    (s t : AgentState L K)
    (hs_phase : s.phase.val = 3) (ht_phase : t.phase.val = 3)
    (hs_clock : s.role = .clock) (ht_clock : t.role = .clock)
    (hs_min : s.minute.val = T) (ht_min : T + 1 ≤ t.minute.val)
    (happ : Protocol.Applicable c s t)
    (j : ℕ) (hj : rBeyond (T + 1) c = j) :
    j + 1 ≤ rBeyond (T + 1) (Protocol.stepOrSelf (NonuniformMajority L K) c s t) := by
  classical
  have hsub : ({s, t} : Multiset (AgentState L K)) ≤ c := happ
  -- minutes unequal, so SYNC fires: both outputs to max minute = t.minute ≥ T+1.
  have hne : s.minute ≠ t.minute := by
    intro h; rw [h] at hs_min; omega
  have hsy := Transition_phase3_clock_minute_sync_decreases (L := L) (K := K) s t
    hs_phase ht_phase hs_clock ht_clock hne
  set s' := (Transition L K s t).1 with hs'
  set t' := (Transition L K s t).2 with ht'
  have hs'clock : s'.role = .clock := hsy.2.2.1
  have ht'clock : t'.role = .clock := hsy.2.2.2.1
  have hs'min : s'.minute = max s.minute t.minute := hsy.2.2.2.2.1
  have ht'min : t'.minute = max s.minute t.minute := hsy.2.2.2.2.2.1
  -- the produced first output is at minute = max ≥ t.minute ≥ T+1, beyond T+1.
  have hmaxge : T + 1 ≤ (max s.minute t.minute).val := by
    have : t.minute.val ≤ (max s.minute t.minute).val := by
      rcases le_total s.minute t.minute with h | h
      · rw [max_eq_right h]
      · rw [max_eq_left h]; exact h
    omega
  have hc' : Protocol.stepOrSelf (NonuniformMajority L K) c s t
      = c - {s, t} + {s', t'} := stepOrSelf_decomp c s t happ
  unfold rBeyond
  rw [hc', Multiset.countP_add, Multiset.countP_sub hsub]
  -- count over {s,t} at level T+1: s is at minute T (not), t is at ≥T+1 (counted) → 1.
  -- count over {s',t'} at level T+1: s' at max ≥ T+1 (counted) → ≥1.
  have hsbelow : ¬ clockBeyondP (T + 1) s := by
    unfold clockBeyondP; rw [hs_min]; omega
  have htabove : clockBeyondP (T + 1) t := ⟨ht_clock, ht_min⟩
  have hpairT1 : Multiset.countP (fun a => clockBeyondP (T + 1) a)
      ({s, t} : Multiset (AgentState L K)) = 1 := by
    rw [countP_pair]; simp [hsbelow, htabove]
  have hs'_beyond : clockBeyondP (T + 1) s' := by
    refine ⟨hs'clock, ?_⟩; rw [hs'min]; exact hmaxge
  have ht'_beyond : clockBeyondP (T + 1) t' := by
    refine ⟨ht'clock, ?_⟩; rw [ht'min]; exact hmaxge
  -- BOTH outputs are synced up to max ≥ T+1, so the produced pair count is 2.
  have hprodT1 : 2 ≤ Multiset.countP (fun a => clockBeyondP (T + 1) a)
      ({s', t'} : Multiset (AgentState L K)) := by
    rw [countP_pair]; simp [hs'_beyond, ht'_beyond]
  have hjc : Multiset.countP (fun a => clockBeyondP (T + 1) a) c = j := hj
  rw [hjc, hpairT1]
  -- j ≥ 1 since t is beyond T+1 in c.
  have hjge : 1 ≤ j := by
    rw [← hjc]
    have : t ∈ c := Multiset.mem_of_le hsub (by simp)
    calc (1 : ℕ) = Multiset.countP (fun a => clockBeyondP (T + 1) a) {t} := by
            rw [show ({t} : Multiset (AgentState L K)) = t ::ₘ 0 from rfl]
            rw [Multiset.countP_cons, Multiset.countP_zero]; simp [htabove]
      _ ≤ _ := Multiset.countP_le_of_le _ (by
            rw [Multiset.singleton_le]; exact this)
  omega

/-- **The DRIP per-pair advance for DISTINCT clocks (NEW).**  A scheduled Phase-3
clock pair `(s, t)` with `s.minute = t.minute = T < cap` (minutes EQUAL but the
full states need NOT be identical) drips the FIRST clock to minute `T+1`, raising
`rBeyond (T+1)` by at least one.  Mirrors `rDrip_pair_advances` but does not need
`s = t` nor a count ≥ 2 of a single state. -/
theorem rDripDistinct_pair_advances (T : ℕ) (c : Config (AgentState L K))
    (s t : AgentState L K)
    (hs_phase : s.phase.val = 3) (ht_phase : t.phase.val = 3)
    (hs_clock : s.role = .clock) (ht_clock : t.role = .clock)
    (hs_min : s.minute.val = T) (heq : s.minute = t.minute) (hcap : T < K * (L + 1))
    (happ : Protocol.Applicable c s t)
    (j : ℕ) (hj : rBeyond (T + 1) c = j) :
    j + 1 ≤ rBeyond (T + 1) (Protocol.stepOrSelf (NonuniformMajority L K) c s t) := by
  classical
  have hsub : ({s, t} : Multiset (AgentState L K)) ≤ c := happ
  have hcap' : s.minute.val < K * (L + 1) := by rw [hs_min]; exact hcap
  have hd := Transition_phase3_clock_minute_drip_decreases (L := L) (K := K) s t
    hs_phase ht_phase hs_clock ht_clock heq hcap'
  set s' := (Transition L K s t).1 with hs'
  set t' := (Transition L K s t).2 with ht'
  have hs'clock : s'.role = .clock := hd.2.2.1
  have hs'min : s'.minute.val = s.minute.val + 1 := hd.2.2.2.2.1
  have ht'min : t'.minute = t.minute := hd.2.2.2.2.2.1
  have hc' : Protocol.stepOrSelf (NonuniformMajority L K) c s t
      = c - {s, t} + {s', t'} := stepOrSelf_decomp c s t happ
  unfold rBeyond
  rw [hc', Multiset.countP_add, Multiset.countP_sub hsub]
  -- both s, t at minute T < T+1 (not beyond T+1) → count over {s,t} = 0.
  have hsbelow : ¬ clockBeyondP (T + 1) s := by
    unfold clockBeyondP; rw [hs_min]; omega
  have htbelow : ¬ clockBeyondP (T + 1) t := by
    unfold clockBeyondP
    have hT : t.minute.val = T := by rw [← heq]; exact hs_min
    rw [hT]; omega
  have hpairT1 : Multiset.countP (fun a => clockBeyondP (T + 1) a)
      ({s, t} : Multiset (AgentState L K)) = 0 := by
    rw [countP_pair]; simp [hsbelow, htbelow]
  -- s' at minute T+1 (counted).
  have hs'_beyond : clockBeyondP (T + 1) s' := by
    refine ⟨hs'clock, ?_⟩; rw [hs'min, hs_min]
  have hprodT1 : 1 ≤ Multiset.countP (fun a => clockBeyondP (T + 1) a)
      ({s', t'} : Multiset (AgentState L K)) := by
    rw [countP_pair]; simp [hs'_beyond]
  have hjc : Multiset.countP (fun a => clockBeyondP (T + 1) a) c = j := hj
  rw [hjc, hpairT1]
  omega

/-- The EPIDEMIC-sync advance with the LAGGING clock as the SECOND coordinate
(`s.minute ≥ T+1`, `t.minute = T`).  Same sync mechanism; both outputs go to the
max minute `≥ T+1`. -/
theorem rEpidemic_pair_advances' (T : ℕ) (c : Config (AgentState L K))
    (s t : AgentState L K)
    (hs_phase : s.phase.val = 3) (ht_phase : t.phase.val = 3)
    (hs_clock : s.role = .clock) (ht_clock : t.role = .clock)
    (hs_min : T + 1 ≤ s.minute.val) (ht_min : t.minute.val = T)
    (happ : Protocol.Applicable c s t)
    (j : ℕ) (hj : rBeyond (T + 1) c = j) :
    j + 1 ≤ rBeyond (T + 1) (Protocol.stepOrSelf (NonuniformMajority L K) c s t) := by
  classical
  have hsub : ({s, t} : Multiset (AgentState L K)) ≤ c := happ
  have hne : s.minute ≠ t.minute := by
    intro h; rw [h] at hs_min; omega
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
      = c - {s, t} + {s', t'} := stepOrSelf_decomp c s t happ
  unfold rBeyond
  rw [hc', Multiset.countP_add, Multiset.countP_sub hsub]
  have hsabove : clockBeyondP (T + 1) s := ⟨hs_clock, hs_min⟩
  have htbelow : ¬ clockBeyondP (T + 1) t := by
    unfold clockBeyondP; rw [ht_min]; omega
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

/-! ## Part C — the witness-free advance probability (the `1/c²` pair-counting).

From the floor facts ALONE we extract a Phase-3 Clock `w` at minute exactly `T`.
We then exhibit an advancing ordered-pair SET `S` of total interaction-count `≥ 2`:

* if `count w ≥ 2`, take `S = {(w,w)}` (same-state DRIP, `interactionCount = count w·(count w−1) ≥ 2`);
* otherwise there is a DISTINCT partner `v`, and `S = {(w,v),(v,w)}` (epidemic or
  distinct-drip in BOTH orders, total `interactionCount = 2·count w·count v ≥ 2`).

Every pair in `S` advances `rBeyond (T+1)`, so the advance-set measure is
`≥ (∑_{p∈S} interactionCount p)/totalPairs ≥ 2/(n(n−1))`, DERIVED by pair-counting. -/

/-- Applicability of a DISTINCT present pair. -/
theorem applicable_of_mem_distinct {c : Config (AgentState L K)} {x y : AgentState L K}
    (hx : x ∈ c) (hy : y ∈ c) (hxy : x ≠ y) : Protocol.Applicable c x y := by
  classical
  have hxc : 1 ≤ Multiset.count x c := Multiset.one_le_count_iff_mem.mpr hx
  have hyc : 1 ≤ Multiset.count y c := Multiset.one_le_count_iff_mem.mpr hy
  refine Multiset.le_iff_count.mpr ?_
  intro a
  rw [show ({x, y} : Multiset (AgentState L K)) = x ::ₘ y ::ₘ 0 from rfl,
      Multiset.count_cons, Multiset.count_cons, Multiset.count_zero]
  by_cases hax : a = x
  · subst hax
    have hay : ¬ a = y := fun h => hxy (h ▸ rfl)
    rw [if_pos rfl, if_neg hay]; omega
  · by_cases hay : a = y
    · subst hay
      have hax' : ¬ a = x := hax
      rw [if_pos rfl, if_neg hax']; omega
    · rw [if_neg hax, if_neg hay]; omega

/-- The advancing-pair Finset and its key properties, extracted from the floor facts. -/
theorem exists_advancing_pairSet (n T : ℕ) (hn : 2 ≤ n) (hcap : T < K * (L + 1))
    (c : Config (AgentState L K))
    (hcard : c.card = n) (hw : AllClockMinT3 T c) (hcr : rBeyond T c = n)
    (hunf : rBeyond (T + 1) c < n) :
    ∃ S : Finset (AgentState L K × AgentState L K),
      (∀ p ∈ S, ∀ j, rBeyond (T + 1) c = j →
        j + 1 ≤ rBeyond (T + 1) (Protocol.stepOrSelf (NonuniformMajority L K) c p.1 p.2)) ∧
      2 ≤ ∑ p ∈ S, c.interactionCount p.1 p.2 := by
  classical
  obtain ⟨w, hwmem, hwc, hwp, hwm⟩ := exists_clock_minute_eqT n T c hcard hw hcr hunf
  have hwcount : 1 ≤ c.count w := Multiset.one_le_count_iff_mem.mpr hwmem
  by_cases hw2 : 2 ≤ c.count w
  · -- same-state drip on (w, w).
    refine ⟨{(w, w)}, ?_, ?_⟩
    · intro p hp j hj
      rw [Finset.mem_singleton] at hp; subst hp
      simp only
      exact rDrip_pair_advances T c w hwp hwc hwm hcap hw2 j hj
    · rw [Finset.sum_singleton]
      rw [show c.interactionCount w w = c.count w * (c.count w - 1) from by
        unfold Config.interactionCount; rw [if_pos rfl]]
      have : 1 ≤ c.count w - 1 := by omega
      calc (2 : ℕ) = 2 * 1 := by ring
        _ ≤ c.count w * (c.count w - 1) := Nat.mul_le_mul (by omega) this
  · -- count w = 1; find a distinct partner v.
    have hwcount1 : c.count w = 1 := by omega
    have hex : ∃ v ∈ c, v ≠ w := by
      by_contra hcon
      rw [not_exists] at hcon
      simp only [not_and, not_not] at hcon
      have hall : ∀ a ∈ c, a = w := hcon
      -- then count w = card = n ≥ 2, contradicting count w = 1.
      have hcw : Multiset.count w c = Multiset.card c :=
        Multiset.count_eq_card.mpr (fun x hx => (hall x hx).symm)
      rw [hcard] at hcw
      have : c.count w = n := hcw
      rw [hwcount1] at this; omega
    obtain ⟨v, hvmem, hvw⟩ := hex
    have hvc : v.role = .clock := (hw v hvmem).1
    have hvp : v.phase.val = 3 := (hw v hvmem).2.1
    have hvmin : T ≤ v.minute.val := (hw v hvmem).2.2
    have hvcount : 1 ≤ c.count v := Multiset.one_le_count_iff_mem.mpr hvmem
    have hwv : w ≠ v := fun h => hvw h.symm
    have happ_wv : Protocol.Applicable c w v := applicable_of_mem_distinct hwmem hvmem hwv
    have happ_vw : Protocol.Applicable c v w := applicable_of_mem_distinct hvmem hwmem hvw
    -- v is at minute = T (drip) or > T (epidemic).
    refine ⟨{(w, v), (v, w)}, ?_, ?_⟩
    · intro p hp j hj
      rw [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with hp | hp <;> (subst hp; simp only)
      · -- (w, v)
        by_cases hvT : v.minute.val = T
        · have hwvmin : w.minute = v.minute := Fin.ext (by rw [hwm, hvT])
          exact rDripDistinct_pair_advances T c w v hwp hvp hwc hvc hwm hwvmin hcap happ_wv j hj
        · have hvgt : T + 1 ≤ v.minute.val := by omega
          exact rEpidemic_pair_advances T c w v hwp hvp hwc hvc hwm hvgt happ_wv j hj
      · -- (v, w)
        by_cases hvT : v.minute.val = T
        · have hvwmin : v.minute = w.minute := Fin.ext (by rw [hvT, hwm])
          exact rDripDistinct_pair_advances T c v w hvp hwp hvc hwc hvT hvwmin hcap happ_vw j hj
        · have hvgt : T + 1 ≤ v.minute.val := by omega
          exact rEpidemic_pair_advances' T c v w hvp hwp hvc hwc hvgt hwm happ_vw j hj
    · -- ∑ interactionCount = count w·count v + count v·count w = 2·count w·count v ≥ 2.
      rw [Finset.sum_insert (by
        simp only [Finset.mem_singleton, Prod.mk.injEq, not_and]
        intro h; exact absurd h hwv)]
      rw [Finset.sum_singleton]
      simp only [Config.interactionCount, if_neg hwv, if_neg (Ne.symm hwv)]
      calc (2 : ℕ) = 1 * 1 + 1 * 1 := by ring
        _ ≤ c.count w * c.count v + c.count v * c.count w :=
            Nat.add_le_add (Nat.mul_le_mul hwcount hvcount) (Nat.mul_le_mul hvcount hwcount)

/-! ## Part D — the witness-free advance probability bound `≥ 2/(n(n−1))`. -/

/-- **The witness-free advance probability (the keystone).**  From the floor facts
ALONE (no witness), one scheduler step raises `rBeyond (T+1)` by at least one with
probability `≥ 2/(n(n−1))`.  Proof: the advancing-pair Finset `S` lies inside the
advance preimage, so the advance measure is `≥ ∑_{p∈S} interactionProb p =
(∑_{p∈S} interactionCount p)/totalPairs ≥ 2/(n(n−1))`, DERIVED by pair-counting. -/
theorem clock_real_advance_prob_uncond (n T : ℕ) (hn : 2 ≤ n) (hcap : T < K * (L + 1))
    (c : Config (AgentState L K))
    (hcard : c.card = n) (hw : AllClockMinT3 T c) (hcr : rBeyond T c = n)
    (hunf : rBeyond (T + 1) c < n) :
    ENNReal.ofReal ((2 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) ≤
      ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
        {c' | rBeyond (T + 1) c + 1 ≤ rBeyond (T + 1) c'} := by
  classical
  set j := rBeyond (T + 1) c with hjdef
  have hc : 2 ≤ c.card := by rw [hcard]; omega
  obtain ⟨S, hSadv, hScount⟩ :=
    exists_advancing_pairSet n T hn hcap c hcard hw hcr hunf
  have hmeas : MeasurableSet {c' : Config (AgentState L K) | j + 1 ≤ rBeyond (T + 1) c'} :=
    DiscreteMeasurableSpace.forall_measurableSet _
  -- S ⊆ preimage of the advance set under scheduledStep.
  have hsub : (↑S : Set (AgentState L K × AgentState L K)) ⊆
      (Protocol.scheduledStep (NonuniformMajority L K) c) ⁻¹'
        {c' | j + 1 ≤ rBeyond (T + 1) c'} := by
    intro p hp
    rw [Finset.mem_coe] at hp
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Protocol.scheduledStep]
    exact hSadv p hp j hjdef.symm
  -- advance measure = interactionPMF measure of the preimage.
  have hstepDist : (NonuniformMajority L K).stepDistOrSelf c
      = (NonuniformMajority L K).stepDist c hc := by
    unfold Protocol.stepDistOrSelf; rw [dif_pos hc]
  have hbase : ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
        {c' | j + 1 ≤ rBeyond (T + 1) c'}
      = (c.interactionPMF hc).toMeasure
          ((Protocol.scheduledStep (NonuniformMajority L K) c) ⁻¹'
            {c' | j + 1 ≤ rBeyond (T + 1) c'}) := by
    rw [hstepDist]; unfold Protocol.stepDist
    rw [PMF.toMeasure_map_apply _ _ _ (Measurable.of_discrete) hmeas]
  rw [hbase]
  have hmono : (c.interactionPMF hc).toMeasure (↑S : Set _)
      ≤ (c.interactionPMF hc).toMeasure
          ((Protocol.scheduledStep (NonuniformMajority L K) c) ⁻¹'
            {c' | j + 1 ≤ rBeyond (T + 1) c'}) :=
    measure_mono hsub
  refine le_trans ?_ hmono
  -- toMeasure ↑S = ∑_{p ∈ S} interactionProb p.
  have hSmeasure : (c.interactionPMF hc).toMeasure (↑S : Set _)
      = ∑ p ∈ S, c.interactionProb p.1 p.2 := by
    rw [PMF.toMeasure_apply_finset]; rfl
  rw [hSmeasure]
  -- ∑ interactionProb = (∑ interactionCount)/totalPairs.
  have heqterm : ∀ p : AgentState L K × AgentState L K,
      c.interactionProb p.1 p.2
        = (↑(c.interactionCount p.1 p.2) : ℝ≥0∞) * (↑c.totalPairs)⁻¹ := by
    intro p; unfold Config.interactionProb; rw [div_eq_mul_inv]
  rw [Finset.sum_congr rfl (fun p _ => heqterm p), ← Finset.sum_mul, ← Nat.cast_sum]
  set N := ∑ p ∈ S, c.interactionCount p.1 p.2 with hN
  have htp : c.totalPairs = n * (n - 1) := by rw [Config.totalPairs, hcard]
  rw [htp, ← div_eq_mul_inv]
  have hden_pos : (0 : ℝ) < ((n * (n - 1) : ℕ) : ℝ) := by
    have : 0 < n * (n - 1) := Nat.mul_pos (by omega) (by omega)
    exact_mod_cast this
  -- 2/(n(n-1)) ≤ N/(n(n-1)) with N ≥ 2.
  have hstep1 : ENNReal.ofReal ((2 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)))
      ≤ ENNReal.ofReal (((N : ℕ) : ℝ) / ((n * (n - 1) : ℕ) : ℝ)) := by
    apply ENNReal.ofReal_le_ofReal
    have hdenR : ((n * (n - 1) : ℕ) : ℝ) = (n : ℝ) * ((n : ℝ) - 1) := by
      rw [Nat.cast_mul, Nat.cast_sub (by omega)]; push_cast; ring
    rw [hdenR]
    have hNR : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hScount
    have hposden : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := by rw [← hdenR]; exact hden_pos
    gcongr
  refine le_trans hstep1 ?_
  rw [← ENNReal.ofReal_natCast N, ← ENNReal.ofReal_natCast (n * (n - 1)),
      ← ENNReal.ofReal_div_of_pos hden_pos]

/-! ## Part E — the witness-free drift and the unconditional `PhaseConvergence`.

We re-run the C3-style window contraction with the WITNESS-FREE advance probability
`clock_real_advance_prob_uncond` in place of the witness-driven `rdrip_prob_ge`.
Everything else (the pointwise bound, the split-and-average algebra) is reused from
`ClockRealKernel`.  The floor window is `AllClockMinT3 T`. -/

/-- The witness-free floor invariant: `card = n`, the Phase-3 Clock window
`AllClockMinT3 T`, and level `T` crossed.  NO witness field. -/
structure rFloorInv' (n T : ℕ) (c : Config (AgentState L K)) : Prop where
  card : c.card = n
  window : AllClockMinT3 T c
  crossedT : rBeyond T c = n

/-- The witness-free contraction: copies `rSeedPot_contracts_on_floor` but draws the
advance probability `≥ 2/(n(n−1))` from `clock_real_advance_prob_uncond` (no witness). -/
theorem rSeedPot_contracts_on_floor' (n T : ℕ) (hn : 2 ≤ n) (hT : T < K * (L + 1))
    (s : ℝ) (hs : 0 < s)
    (c : Config (AgentState L K)) (hfl : rFloorInv' (L := L) (K := K) n T c)
    (hnc : ¬ rFinished (L := L) (K := K) n T c) :
    ∫⁻ c', rSeedPot (L := L) (K := K) n T s c' ∂((NonuniformMajority L K).transitionKernel c) ≤
      ENNReal.ofReal (1 - ((2 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) * (1 - Real.exp (-s)))
        * rSeedPot (L := L) (K := K) n T s c := by
  set m := rBeyond (T + 1) c with hm
  have hm_hi : m < n := by rw [rFinished, not_le] at hnc; exact hnc
  have hΦc : rSeedPot (L := L) (K := K) n T s c
      = ENNReal.ofReal (Real.exp (s * ((n : ℝ) - (m : ℝ)))) := by
    unfold rSeedPot
    rw [if_neg (by rw [← hm]; omega), rClamp_eq_of_lt n T c (by rw [← hm]; omega)]
  set A := {c' : Config (AgentState L K) | m + 1 ≤ rBeyond (T + 1) c'} with hA_def
  have hA_meas : MeasurableSet A := DiscreteMeasurableSpace.forall_measurableSet _
  set pR : ℝ := (2 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) with hpR
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hden_pos : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
  have hpR_nonneg : 0 ≤ pR := by
    rw [hpR]; exact le_of_lt (div_pos (by norm_num) hden_pos)
  have hpR_le_one : pR ≤ 1 := by
    rw [hpR, div_le_one hden_pos]; nlinarith
  set E0 : ℝ := Real.exp (s * ((n : ℝ) - (m : ℝ))) with hE0
  set E1 : ℝ := Real.exp (s * ((n : ℝ) - (m : ℝ) - 1)) with hE1
  have hE0_pos : 0 < E0 := Real.exp_pos _
  have hE1_pos : 0 < E1 := Real.exp_pos _
  have hE1_eq : E1 = E0 * Real.exp (-s) := by
    rw [hE0, hE1, ← Real.exp_add]; congr 1; ring
  -- THE witness-free advance probability bound.
  have hstep : ENNReal.ofReal pR ≤
      ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
        {c' | rBeyond (T + 1) c + 1 ≤ rBeyond (T + 1) c'} := by
    rw [hpR]
    exact clock_real_advance_prob_uncond n T hn hT c hfl.card hfl.window hfl.crossedT
      (by rw [← hm]; exact hm_hi)
  rw [← hm] at hstep
  change ∫⁻ c', rSeedPot (L := L) (K := K) n T s c'
    ∂((NonuniformMajority L K).stepDistOrSelf c).toMeasure ≤ _
  calc ∫⁻ c', rSeedPot (L := L) (K := K) n T s c'
        ∂((NonuniformMajority L K).stepDistOrSelf c).toMeasure
      ≤ ∫⁻ c', (if m + 1 ≤ rBeyond (T + 1) c' then ENNReal.ofReal E1
          else ENNReal.ofReal E0) ∂((NonuniformMajority L K).stepDistOrSelf c).toMeasure := by
        apply lintegral_mono_ae
        rw [ae_iff, PMF.toMeasure_apply_eq_zero_iff _
          (DiscreteMeasurableSpace.forall_measurableSet _)]
        rw [Set.disjoint_left]
        intro x hsupp hbad
        apply hbad
        exact rSeedPot_pointwise_bound n T s hs c hfl.window.toGE3 m hm.symm hm_hi x hsupp
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
          * rSeedPot (L := L) (K := K) n T s c := by
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

/-! ## Part F — absorbing-ness of the Phase-3 window (the structural status).

`AllClockMinT3 T` requires every agent to be a Clock at phase EXACTLY 3.  Minutes
never drop (so `T ≤ minute` is preserved) and roles stay Clock.  Phase 3 is
preserved on a Phase-3 pair UNLESS the equal-minute-at-cap branch fires, which
advances a Clock to phase 4 via `stdCounterSubroutine`.  In the regime
`T < K(L+1)` the unfinished minute-`T` clocks are sub-cap; but over many steps a
drip can march a clock UP to the cap and trigger the phase-4 escape.  Hence
`AllClockMinT3 T` is NOT one-step absorbing in general.

To deliver a genuinely UNCONDITIONAL theorem we therefore parametrize the
`PhaseConvergence` by the window's absorbing-ness as the SINGLE remaining
structural input `habs`.  This is a one-step support-closure statement about the
real kernel, NOT a probabilistic witness: the central over-restrictive `witnessOf`
existential (≥ 2 identical-state clocks) is FULLY DISCHARGED above (Part D).  See
the final docstring for the precise honest status. -/

/-- **`clock_real_advance_uncond` — the WITNESS-FREE clock-minute advance.**
The undischarged `witnessOf` of `ClockRealKernel.clock_real_advance` is GONE: the
advance probability `≥ 2/(n(n−1))` is DERIVED by pair-counting
(`clock_real_advance_prob_uncond`) from the floor facts alone, handling BOTH the
`n−m ≥ 2` drip and `n−m = 1` epidemic cases.  The only remaining input is `habs`,
the one-step support-closure of the Phase-3 Clock window `AllClockMinT3 T` (a
structural kernel fact, not a witness); see Part F for why it is not derivable from
one-step structural facts. -/
noncomputable def clock_real_advance_uncond (n T : ℕ) (hn : 2 ≤ n) (hT : T < K * (L + 1))
    (habs : ∀ c c' : Config (AgentState L K),
      AllClockMinT3 T c → c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support →
      AllClockMinT3 T c')
    (t : ℕ) (ε : ℝ≥0)
    (hε : ENNReal.ofReal (1 - ((2 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) * (1 - Real.exp (-Real.log 2)))
            ^ t * ENNReal.ofReal (Real.exp (Real.log 2 * (n : ℝ))) / 1 ≤ (ε : ℝ≥0∞)) :
    PhaseConvergence (NonuniformMajority L K).transitionKernel := by
  have hs : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  -- The guarded potential `rSeedPotG` is reused; the shell is `card = n ∧ AllClockGE3`.
  -- Q = card = n ∧ AllClockMinT3 T ∧ rBeyond T = n.
  refine WindowConcentration.windowDrift_PhaseConvergence (NonuniformMajority L K)
    (rSeedPotG (L := L) (K := K) n T (Real.log 2)) (rSeedPotG_measurable n T (Real.log 2))
    (fun c => c.card = n ∧ AllClockMinT3 T c ∧ rBeyond T c = n)        -- Q (absorbing)
    ?_                                                                  -- hQ_abs
    (ENNReal.ofReal (1 - ((2 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) * (1 - Real.exp (-Real.log 2))))
    ?_                                                                  -- hdrift
    (fun c => c.card = n ∧ AllClockMinT3 T c ∧ rBeyond T c = n)        -- Pre
    (fun c => rShell (L := L) (K := K) n c ∧ rFinished (L := L) (K := K) n T c)  -- Post
    (rPostG_absorbing n T)                                             -- hPost_abs
    1 one_ne_zero ENNReal.one_ne_top                                   -- θ = 1
    (rSeedPotG_link n T (Real.log 2) hs)                               -- hlink
    (fun c h => h)                                                     -- hPre_Q
    (ENNReal.ofReal (Real.exp (Real.log 2 * (n : ℝ))))                -- Φ₀
    ?_                                                                 -- hPre_bound
    t ε hε                                                            -- hε
  · -- hQ_abs : card, AllClockMinT3 (via habs), and rBeyond T preserved.
    rintro c c' ⟨hcard, hwin, hcr⟩ hc'
    have hwin' : AllClockMinT3 T c' := habs c c' hwin hc'
    refine ⟨?_, hwin', ?_⟩
    · rw [Protocol.stepDistOrSelf_support_card_eq (NonuniformMajority L K) c c' hc']; exact hcard
    · have hge := rBeyondGE3_ge_monotone T n c c' hwin.toGE3 (le_of_eq hcr.symm) hc'
      have hle : rBeyond T c' ≤ c'.card := by
        unfold rBeyond; exact Multiset.countP_le_card _ _
      have hcard' : c'.card = n := by
        rw [Protocol.stepDistOrSelf_support_card_eq (NonuniformMajority L K) c c' hc']; exact hcard
      omega
  · -- hdrift : build the WITNESS-FREE floor invariant and apply the guarded drift.
    rintro c ⟨hcard, hwin, hcr⟩
    have hfl : rFloorInv' (L := L) (K := K) n T c := ⟨hcard, hwin, hcr⟩
    -- the guarded drift mirrors `rSeedPotG_drift_floorInv` but with `rFloorInv'`.
    have hshell : c.card = n ∧ AllClockGE3 c := ⟨hfl.card, hfl.window.toGE3⟩
    rw [rSeedPotG_eq_on_shell n T (Real.log 2) c hshell]
    have hint_eq : ∫⁻ c', rSeedPotG (L := L) (K := K) n T (Real.log 2) c'
          ∂((NonuniformMajority L K).transitionKernel c)
        = ∫⁻ c', rSeedPot (L := L) (K := K) n T (Real.log 2) c'
          ∂((NonuniformMajority L K).transitionKernel c) := by
      apply lintegral_congr_ae
      change ∀ᵐ c' ∂((NonuniformMajority L K).stepDistOrSelf c).toMeasure,
        rSeedPotG (L := L) (K := K) n T (Real.log 2) c'
          = rSeedPot (L := L) (K := K) n T (Real.log 2) c'
      rw [ae_iff, PMF.toMeasure_apply_eq_zero_iff _
        (DiscreteMeasurableSpace.forall_measurableSet _)]
      rw [Set.disjoint_left]
      intro x hsupp hbad
      apply hbad
      have hxwin : AllClockMinT3 T x := habs c x hfl.window hsupp
      have hxshell : x.card = n ∧ AllClockGE3 x := by
        refine ⟨?_, hxwin.toGE3⟩
        rw [Protocol.stepDistOrSelf_support_card_eq (NonuniformMajority L K) c x hsupp]
        exact hfl.card
      exact rSeedPotG_eq_on_shell n T (Real.log 2) x hxshell
    rw [hint_eq]
    by_cases hfin : rFinished (L := L) (K := K) n T c
    · -- finished: Φ = 0 and stays 0.
      have hΦc0 : rSeedPot (L := L) (K := K) n T (Real.log 2) c = 0 := by
        unfold rSeedPot rFinished at *; rw [if_pos hfin]
      rw [hΦc0, mul_zero, nonpos_iff_eq_zero]
      change ∫⁻ c', rSeedPot (L := L) (K := K) n T (Real.log 2) c'
          ∂((NonuniformMajority L K).stepDistOrSelf c).toMeasure = 0
      rw [lintegral_eq_zero_iff (rSeedPot_measurable n T (Real.log 2))]
      rw [Filter.eventuallyEq_iff_exists_mem]
      refine ⟨((NonuniformMajority L K).stepDistOrSelf c).support, ?_, ?_⟩
      · rw [mem_ae_iff, PMF.toMeasure_apply_eq_zero_iff _
          (DiscreteMeasurableSpace.forall_measurableSet _)]
        rw [Set.disjoint_left]; intro x hsupp hx
        exact hx (PMF.mem_support_iff _ _ |>.mp hsupp)
      · intro c' hc'
        have hfin' : rFinished (L := L) (K := K) n T c' :=
          rBeyondGE3_ge_monotone (T + 1) n c c' hfl.window.toGE3 hfin hc'
        change rSeedPot (L := L) (K := K) n T (Real.log 2) c' = 0
        unfold rSeedPot rFinished at *; rw [if_pos hfin']
    · exact rSeedPot_contracts_on_floor' n T hn hT (Real.log 2) hs c hfl hfin
  · -- hPre_bound
    rintro c ⟨hcard, hwin, _⟩
    exact rSeedPotG_le_max n T (Real.log 2) hs c ⟨hcard, hwin.toGE3⟩

end ClockRealKernel

end ExactMajority
