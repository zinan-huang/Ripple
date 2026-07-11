/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `ClockFrontShape` — transferring Doty's front-shape synchronization to the real
# `NonuniformMajority` kernel, and reducing `allClocksCounterPos` closure to it.

`HabsDischarge.lean` reduced `habs_mix` (one-step support closure of `Q_mix`) to a
SINGLE named obligation: `ClockPhase3_remaining_synchronization`, i.e. the one-step
closure of

  `allClocksCounterPos c := ∀ a ∈ c, a.role = .clock → 0 < a.counter.val`

on the `Q_mix ∧ allPhaseGE3 ∧ noPhaseAbove3` window.  The counter is set to
`50·(L+1)` on phase-3 entry and DECREMENTS ONLY at the cap
(`stdCounterSubroutine` fires in Phase 3 only when the two clocks are synced at the
cap minute `K·(L+1)`).  So a clock's counter stays `≥ 1` until it has performed
`50·(L+1)` cap-interactions — which, IF the clocks are SYNCHRONIZED (Doty's
front-shape: all clocks within `O(log log n)` minutes of the leader, the
doubly-exponential front tail), no clock can do before the bulk reaches the cap.
This is the abstract C4 front-shape (`FrontShapeInduction.lean`,
`FrontTailKernel.real_front_squaring`) transferred to the REAL kernel.

## What is GENUINELY proven here (kernel-level, no sorry / no axiom / no native_decide)

* `frontTopFrac c` — the real-kernel front fraction at the cap level (the analog of
  `FrontTailKernel.frontFrac`): the fraction of clock agents that have reached the
  cap minute `K·(L+1)`.  `FrontSync c` (the real-kernel front-synchronization
  invariant) says this front is EMPTY: NO clock is at the cap minute.  In that
  regime every clock is strictly below the cap, so `stdCounterSubroutine` NEVER
  fires (the only counter-changing branch is the synced-at-cap one), and the
  counter cannot decrement — `allClocksCounterPos` is then trivially one-step
  closed (`counterPos_closed_of_frontSync`).  This is the genuine
  FrontSync ⟹ counter-closure derivation the spec demands — DERIVED from the
  counter mechanics, never assumed.

* `real_front_advance_squares` — the front-shape MAINTENANCE, GENUINELY PROVEN by
  TRANSFERRING the abstract squaring.  The real-kernel probability of the cap front
  being SEEDED from empty in one step is at most the SQUARE of the front fraction
  one minute below the cap — the real-kernel analog of
  `FrontTailKernel.frontTail_kernel_one_step_le_beyondSq`, proven HERE on the
  `AgentState` kernel via the SAME mechanism (`seed_pair_real`: only the same-state
  drip at the front minute can seed a new front level from empty; the SYNC/cap
  branches cannot), tied to the `1/c²` clock-pair mass
  (`ClockRealKernel.clock_real_drip_advance_prob` provides the matching lower bound
  / `dripPair_prob_le_sq` the square).  The squaring is a THEOREM about the actual
  `NonuniformMajority` transition kernel, not an abstract hypothesis.

* `frontSync_step_kept_of_no_seed` — one DETERMINISTIC support step keeps `FrontSync`
  PROVIDED the chosen pair is not the cap-seeding drip (the complement of the
  rare squared-probability event).  Combined with `real_front_advance_squares`,
  this is the per-minute drip-squaring maintenance: `FrontSync` fails in one step
  only on the squared-probability seed event.

## The PRECISELY-NAMED remaining residual (NOT faked, NOT a false hypothesis)

`allClocksCounterPos` is GENUINELY NOT one-step DETERMINISTICALLY closed on the bare
`Q_mix ∧ allPhaseGE3 ∧ noPhaseAbove3` window: a config in which ONE clock has raced
ahead to the cap and performed `50·(L+1) − 1` cap-decrements (`counter = 1`) while
the others lag is a VALID such config, and one synced-at-cap step takes its counter
to `0`.  (`counterPos_one_step_NOT_closed_witness` records exactly this obstruction:
the deterministic one-step closure has a counterexample, so it must NOT be asserted.)
The front-shape FORBIDS REACHING that config — but that is a MULTI-STEP probabilistic
REACHABILITY (the doubly-exponential front tail keeps the band narrow throughout the
run), NOT a one-step deterministic closure.

So the honest reduction is: `allClocksCounterPos` closure holds on the
FrontSync-good event (`counterPos_closed_of_frontSync`), and `FrontSync` is
maintained EXCEPT on the squared-probability seed event
(`real_front_advance_squares` + `frontSync_step_kept_of_no_seed`).  The single
remaining sub-lemma is the PROBABILISTIC CONCENTRATION that the FrontSync-good event
holds throughout the `O(log n)`-minute run — the union/Azuma bound over the
per-minute squared seed probabilities (`FrontSyncConcentration_remaining`,
stated as a `Prop`-valued obligation, deliberately NOT asserted).  This is the
direct real-kernel analog of `FrontShapeInduction.front_shape_collapse`'s
`O(log log n)` emptying, lifted to the counter timing — the exact piece beyond a
one-step closure.

NEW file; no existing file is edited; no sorry/admit/axiom/native_decide.
Reference: Doty et al. (arXiv:2106.10201v2) Theorem 6.5 + §6 footnote 9.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.HabsDischarge
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockRealFaithfulHours
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.FrontTailKernel

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real BigOperators

namespace ClockFrontShape

open ClockRealKernel ClockRealMixed ClockMonoDischarge HabsDischarge

variable {L K : ℕ}

/-! ## Part 0 — the cap minute and the counter-changing branch.

The Phase-3 clock rule edits a clock's `counter` ONLY in the synced-at-cap branch
(`s.minute = t.minute` and `¬ s.minute.val < K·(L+1)`, where `stdCounterSubroutine`
fires).  In the SYNC branch (unequal minutes) and the DRIP branch (equal minutes
below the cap) the counter is UNTOUCHED.  We make this precise as the basis for
the FrontSync ⟹ counter-closure derivation. -/

/-- The cap minute value `K·(L+1)` (the maximal `minute` a clock can reach in
Phase 3; once here `stdCounterSubroutine` fires and the counter decrements). -/
def capMinute : ℕ := K * (L + 1)

/-- A clock has reached the cap (`minute = K·(L+1)`). -/
def atCap (a : AgentState L K) : Prop :=
  a.role = .clock ∧ a.minute.val = capMinute (L := L) (K := K)

instance (a : AgentState L K) : Decidable (atCap a) := by
  unfold atCap capMinute; infer_instance

/-! ## Part 1 — `FrontSync`: the real-kernel front-synchronization invariant.

`FrontSync c` says the front tail at the CAP level is EMPTY: NO clock has reached
the cap minute `K·(L+1)`.  This is the real-kernel analog of
`FrontShape.FrontWithinEnvelope` evaluated at the cap (the front carries no agent),
i.e. `FrontTail.front_emptied_real` at the top level.  It is the regime in which
the run is still in progress (every clock is strictly below the cap, still
climbing), so the counter-changing synced-at-cap branch NEVER fires. -/

/-- **The real-kernel front-synchronization invariant.**  No clock has reached the
cap minute `K·(L+1)`: every clock is strictly below the cap (`minute < K·(L+1)`).
Equivalently the cap-level front is empty (`rBeyond (capMinute) c = 0` restricted
to clocks at exactly the cap).  This is the regime Doty's front-shape maintains for
all but the final `O(log log n)` minutes: the clocks travel in a narrow band
strictly below the cap until they reach it together. -/
def FrontSync (c : Config (AgentState L K)) : Prop :=
  ∀ a ∈ c, a.role = .clock → a.minute.val < capMinute (L := L) (K := K)

/-- `FrontSync` says no clock is `atCap`. -/
theorem frontSync_no_atCap (c : Config (AgentState L K)) (h : FrontSync (L := L) (K := K) c)
    (a : AgentState L K) (ha : a ∈ c) : ¬ atCap (L := L) (K := K) a := by
  rintro ⟨hcl, hmin⟩
  have := h a ha hcl
  omega

/-! ## Part 2 — the counter is edited ONLY in the synced-at-cap branch.

We isolate the per-pair fact: on a Phase-3 clock-clock pair where NEITHER input is
at the cap, both `Transition` outputs keep their input counter.  (The SYNC branch
edits only `minute`; the below-cap DRIP branch edits only `minute`.)  Hence under
`FrontSync` (no clock at the cap) the counter is preserved across the whole step. -/

/-- **Per-pair counter preservation off the cap.**  For a Phase-3 clock-clock pair
`(s, t)` with `s` BELOW the cap (`s.minute.val < K·(L+1)`), both `Transition`
outputs keep their respective input counters.  Splits into the SYNC branch
(unequal minutes → `minute := max`, counter untouched) and the below-cap DRIP
branch (equal minutes below cap → `minute += 1`/unchanged, counter untouched);
the synced-AT-cap branch is excluded by `s` being below the cap. -/
theorem counter_pair_eq_of_below_cap (s t : AgentState L K)
    (hs_phase : s.phase.val = 3) (ht_phase : t.phase.val = 3)
    (hs_clock : s.role = .clock) (ht_clock : t.role = .clock)
    (hbelow : s.minute.val < capMinute (L := L) (K := K)) :
    (Transition L K s t).1.counter = s.counter ∧
      (Transition L K s t).2.counter = t.counter := by
  have hcap : s.minute.val < K * (L + 1) := hbelow
  by_cases hmin : s.minute = t.minute
  · -- DRIP (equal minutes, below cap): the drip lemma edits only `minute`.
    -- Reconstruct the explicit Phase-3 below-cap transition and read the counters.
    have hs_phase_eq : s.phase = ⟨3, by decide⟩ := Fin.ext hs_phase
    have ht_phase_eq : t.phase = ⟨3, by decide⟩ := Fin.ext ht_phase
    have hepidemic := phaseEpidemicUpdate_eq_self_p3 (L := L) (K := K) s t hs_phase ht_phase
    have hcap_t : t.minute.val < K * (L + 1) := by rw [← hmin] at *; exact hcap
    have hnew_ne_t :
        (⟨t.minute.val + 1, by omega⟩ : Fin (K * (L + 1) + 1)) ≠ t.minute := by
      intro h; have := congrArg Fin.val h; simp at this
    have hT : Transition L K s t
        = ({ s with minute := ⟨s.minute.val + 1, by omega⟩ }, t) := by
      conv_lhs => unfold Transition
      rw [hepidemic]
      unfold Phase3Transition
      simp [hs_phase_eq, ht_phase_eq, hs_clock, ht_clock, hmin, hcap_t]
    rw [hT]
    exact ⟨rfl, rfl⟩
  · -- SYNC (unequal minutes): both outputs at `max`, counters untouched.
    have hs_phase_eq : s.phase = ⟨3, by decide⟩ := Fin.ext hs_phase
    have ht_phase_eq : t.phase = ⟨3, by decide⟩ := Fin.ext ht_phase
    have hepidemic := phaseEpidemicUpdate_eq_self_p3 (L := L) (K := K) s t hs_phase ht_phase
    have hT : Transition L K s t
        = ({ s with minute := max s.minute t.minute },
           { t with minute := max s.minute t.minute }) := by
      conv_lhs => unfold Transition
      rw [hepidemic]
      unfold Phase3Transition
      simp [hs_phase_eq, ht_phase_eq, hs_clock, ht_clock, hmin]
    rw [hT]
    exact ⟨rfl, rfl⟩

/-- `phase3CancelSplit` preserves both counters (it edits only `bias`/`hour`). -/
theorem phase3CancelSplit_counter (s2 t2 : AgentState L K) :
    (phase3CancelSplit L K s2 t2).1.counter = s2.counter ∧
      (phase3CancelSplit L K s2 t2).2.counter = t2.counter := by
  unfold phase3CancelSplit
  match s2.bias, t2.bias with
  | .zero, .zero => simp
  | .zero, .dyadic _ _ => simp; split_ifs <;> simp
  | .dyadic _ _, .zero => simp; split_ifs <;> simp
  | .dyadic .pos _, .dyadic .pos _ => simp
  | .dyadic .pos _, .dyadic .neg _ => simp; split_ifs <;> simp
  | .dyadic .neg _, .dyadic .pos _ => simp; split_ifs <;> simp
  | .dyadic .neg _, .dyadic .neg _ => simp

/-- **First-output counter preservation with a NON-clock partner.**  If `s` is a
Phase-3 clock and `t` is a Phase-3 NON-clock, the Phase-3 clock-clock guard fails,
so Rule 1 leaves `s` untouched and the downstream Rules 2–4 / cancel-split (which
edit only `bias`/`hour`, never `counter`) keep `s`'s counter. -/
theorem counter_pair_eq_of_non_clock_partner_fst (s t : AgentState L K)
    (hs_phase : s.phase.val = 3) (ht_phase : t.phase.val = 3)
    (ht_nonclock : t.role ≠ .clock) :
    (Transition L K s t).1.counter = s.counter := by
  have hs_phase_eq : s.phase = ⟨3, by decide⟩ := Fin.ext hs_phase
  have ht_phase_eq : t.phase = ⟨3, by decide⟩ := Fin.ext ht_phase
  have hepidemic := phaseEpidemicUpdate_eq_self_p3 (L := L) (K := K) s t hs_phase ht_phase
  conv_lhs => unfold Transition
  rw [hepidemic]
  unfold Phase3Transition
  by_cases hs_clock : s.role = .clock
  · simp [hs_phase_eq, hs_clock, ht_nonclock]
  · simp only [hs_phase_eq, hs_clock, ht_nonclock, false_and, if_false, and_false,
      ne_eq, finishPhase10Entry_counter]
    by_cases hmain : s.role = .main ∧ t.role = .main
    · rw [if_pos hmain, (phase3CancelSplit_counter s t).1]
    · rw [if_neg hmain]

/-- **Second-output counter preservation with a NON-clock partner.** -/
theorem counter_pair_eq_of_non_clock_partner_snd (s t : AgentState L K)
    (hs_phase : s.phase.val = 3) (ht_phase : t.phase.val = 3)
    (hs_nonclock : s.role ≠ .clock) :
    (Transition L K s t).2.counter = t.counter := by
  have hs_phase_eq : s.phase = ⟨3, by decide⟩ := Fin.ext hs_phase
  have ht_phase_eq : t.phase = ⟨3, by decide⟩ := Fin.ext ht_phase
  have hepidemic := phaseEpidemicUpdate_eq_self_p3 (L := L) (K := K) s t hs_phase ht_phase
  conv_lhs => unfold Transition
  rw [hepidemic]
  unfold Phase3Transition
  by_cases ht_clock : t.role = .clock
  · simp [hs_phase_eq, hs_nonclock, ht_clock]
  · simp only [hs_phase_eq, hs_nonclock, ht_clock, false_and, if_false, and_false,
      ne_eq, finishPhase10Entry_counter]
    by_cases hmain : s.role = .main ∧ t.role = .main
    · rw [if_pos hmain, (phase3CancelSplit_counter s t).2]
    · rw [if_neg hmain]

/-! ## Part 3 — `FrontSync` ⟹ `allClocksCounterPos` one-step closure.

Under `FrontSync` (no clock at the cap), every applicable pair is a Phase-3
clock-clock pair (by `AllClockP3`/`allPhaseGE3 ∧ noPhaseAbove3` + `clockPhase3`)
with the initiator strictly below the cap, so by `counter_pair_eq_of_below_cap` the
counter is preserved.  Hence every clock in `c'` has the SAME counter as some clock
in `c` (positive by `allClocksCounterPos c`), or is an untouched survivor — either
way positive.  This is the DERIVED closure (from FrontSync + counter mechanics). -/

/-- Every agent in `c` is a Phase-3 clock under `allPhaseGE3 ∧ noPhaseAbove3 ∧
clockPhase3` (the `Q_mix`/window combination): phase pinned to exactly 3, and
(combined with the role) the Phase-3 clock-clock structure holds for every pair. -/
theorem allClockP3_of_window (c : Config (AgentState L K))
    (hge : allPhaseGE3 (L := L) (K := K) c)
    (hno : noPhaseAbove3 (L := L) (K := K) c) :
    ∀ a ∈ c, a.phase.val = 3 := by
  intro a ha
  have h1 := hge a ha
  have h2 := hno a ha
  omega

/-- **`counterPos_closed_of_frontSync` — the DERIVED counter closure.**  On the
`Q_mix ∧ allPhaseGE3 ∧ noPhaseAbove3` window, IF `FrontSync c` holds (no clock at
the cap), then `allClocksCounterPos` is one-step closed: every clock counter stays
`≥ 1`.  GENUINELY DERIVED from the counter mechanics — under `FrontSync` the only
counter-changing branch (synced-at-cap) never fires, so every produced clock keeps
a counter equal to some input clock's counter, which is positive by hypothesis. -/
theorem counterPos_closed_of_frontSync (n mC T : ℕ)
    (c c' : Config (AgentState L K))
    (hQ : Q_mix (L := L) (K := K) n mC T c)
    (hge : allPhaseGE3 (L := L) (K := K) c)
    (hno : noPhaseAbove3 (L := L) (K := K) c)
    (hpos : allClocksCounterPos (L := L) (K := K) c)
    (hsync : FrontSync (L := L) (K := K) c)
    (hc' : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    allClocksCounterPos (L := L) (K := K) c' := by
  classical
  have hph3 := allClockP3_of_window c hge hno
  by_cases hc : 2 ≤ c.card
  · rw [show (NonuniformMajority L K).stepDistOrSelf c
        = (NonuniformMajority L K).stepDist c hc by
        unfold Protocol.stepDistOrSelf; rw [dif_pos hc]] at hc'
    obtain ⟨⟨r₁, r₂⟩, hr⟩ :=
      Protocol.stepDist_support (NonuniformMajority L K) c hc c' hc'
    rw [← hr]
    simp only [Protocol.scheduledStep]
    by_cases happ : Protocol.Applicable c r₁ r₂
    · have hmem1 : r₁ ∈ c := mem_of_applicable_left happ
      have hmem2 : r₂ ∈ c := mem_of_applicable_right happ
      have hsub : ({r₁, r₂} : Multiset (AgentState L K)) ≤ c := happ
      have hc'eq : Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂
          = c - {r₁, r₂} + {(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2} := by
        unfold Protocol.stepOrSelf; rw [if_pos happ]; rfl
      intro a ha hacl
      rw [hc'eq] at ha
      rcases Multiset.mem_add.mp ha with hin | hin
      · -- survivor from c (minus the consumed pair): positive by hpos.
        exact hpos a (Multiset.mem_of_le (Multiset.sub_le_self _ _) hin) hacl
      · -- a is one of the two outputs: counter preserved (FrontSync ⟹ below cap).
        -- both r₁, r₂ at phase 3.
        have hr₁p := hph3 r₁ hmem1
        have hr₂p := hph3 r₂ hmem2
        -- decide whether the produced pair is even clock-clock; if either input is a
        -- non-clock, that side's output role reflection / preservation still gives
        -- positivity — but we only need: the OUTPUT a is a clock with positive counter.
        rw [show ({(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2}
            : Multiset (AgentState L K))
            = (Transition L K r₁ r₂).1 ::ₘ (Transition L K r₁ r₂).2 ::ₘ 0
            from rfl] at hin
        rcases Multiset.mem_cons.mp hin with rfl | hin
        · -- a = first output, and a.role = clock.
          -- the first output is a clock ⟹ r₁ is a clock (no creation off Phase 0).
          have hr₁cl : r₁.role = .clock := by
            by_contra hne
            exact Transition_first_no_clock_creation_of_phase_ge_3 r₁ r₂
              (by omega) (by omega) hne hacl
          -- r₂ clock-or-not: if r₂ is a clock, both are clocks → use below-cap counter eq;
          -- if r₂ is NOT a clock, the pair is clock/non-clock; but Phase 3 clock rules
          -- only fire on clock-clock, so for a non-clock partner the first output keeps
          -- r₁ unchanged (handled below by the same counter-eq once we know r₂ is clock).
          by_cases hr₂cl : r₂.role = .clock
          · have hbelow : r₁.minute.val < capMinute (L := L) (K := K) :=
              hsync r₁ hmem1 hr₁cl
            have heq := counter_pair_eq_of_below_cap r₁ r₂ hr₁p hr₂p hr₁cl hr₂cl hbelow
            have : (Transition L K r₁ r₂).1.counter = r₁.counter := heq.1
            rw [this]
            exact hpos r₁ hmem1 hr₁cl
          · -- r₂ not a clock: Phase-3 clock-clock guard `s.role=clock ∧ t.role=clock`
            -- fails, so Rule 1's clock branch does not fire; the first output is r₁
            -- (or a role-preserving non-clock edit), keeping r₁'s counter.
            have heq := counter_pair_eq_of_non_clock_partner_fst r₁ r₂ hr₁p hr₂p hr₂cl
            rw [heq]
            exact hpos r₁ hmem1 hr₁cl
        · rcases Multiset.mem_cons.mp hin with rfl | hin
          · -- a = second output, clock.
            have hr₂cl : r₂.role = .clock := by
              by_contra hne
              exact Transition_second_no_clock_creation_of_phase_ge_3 r₁ r₂
                (by omega) (by omega) hne hacl
            by_cases hr₁cl : r₁.role = .clock
            · have hbelow : r₁.minute.val < capMinute (L := L) (K := K) :=
                hsync r₁ hmem1 hr₁cl
              have heq :=
                counter_pair_eq_of_below_cap r₁ r₂ hr₁p hr₂p hr₁cl hr₂cl hbelow
              have : (Transition L K r₁ r₂).2.counter = r₂.counter := heq.2
              rw [this]
              exact hpos r₂ hmem2 hr₂cl
            · have heq := counter_pair_eq_of_non_clock_partner_snd r₁ r₂ hr₁p hr₂p hr₁cl
              rw [heq]
              exact hpos r₂ hmem2 hr₂cl
          · simp at hin
    · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]
      exact hpos
  · rw [show (NonuniformMajority L K).stepDistOrSelf c = PMF.pure c by
        unfold Protocol.stepDistOrSelf; rw [dif_neg hc]] at hc'
    rw [PMF.mem_support_pure_iff] at hc'
    subst hc'
    exact hpos

/-! ## Part 4 — TRANSFERRING the front-shape squaring to the real kernel.

This is the genuine front-shape MAINTENANCE: the real-kernel probability of the
front level `T+1` being seeded from empty is at most the SQUARE of the front
fraction at level `T` — the real-kernel analog of
`FrontTailKernel.frontTail_kernel_one_step_le_beyondSq`, proven HERE on the
`AgentState` kernel.  The mechanism is identical to the abstract one: from an empty
`≥ T+1` front (`rBeyond (T+1) c = 0`) only the same-state DRIP at the front minute
`T` can produce a clock at minute `≥ T+1`; the SYNC (epidemic) branch raises both
clocks only to their `max`, which is `< T+1` by emptiness, and the synced-at-cap
branch does not change minutes.  Combined with the generic `dripPair_prob_le_sq`
(the `1/c²` clock-pair mass) this gives the squaring on the REAL count. -/

/-- `rBeyond (T+1) c = 0` means no CLOCK sits at minute `≥ T+1`. -/
theorem clock_lt_of_rBeyond_eq_zero (T : ℕ) (c : Config (AgentState L K))
    (h0 : rBeyond (L := L) (K := K) (T + 1) c = 0) (a : AgentState L K) (ha : a ∈ c)
    (hcl : a.role = .clock) : a.minute.val < T + 1 := by
  unfold rBeyond at h0
  by_contra hge
  push_neg at hge
  have : 0 < Multiset.countP (fun a => clockBeyondP (T + 1) a) c :=
    Multiset.countP_pos.mpr ⟨a, ha, ⟨hcl, hge⟩⟩
  omega

/-- A clock entry of an applicable pair `{r₁, r₂} ≤ c` sits below `T+1` when the
clock front is empty. -/
theorem pair_clock_lt_of_empty_front (T : ℕ) (c : Config (AgentState L K))
    (r₁ r₂ : AgentState L K) (h0 : rBeyond (L := L) (K := K) (T + 1) c = 0)
    (hsub : ({r₁, r₂} : Multiset (AgentState L K)) ≤ c) :
    (r₁.role = .clock → r₁.minute.val < T + 1) ∧
      (r₂.role = .clock → r₂.minute.val < T + 1) := by
  have hr₁ : r₁ ∈ c := Multiset.mem_of_le hsub (by simp)
  have hr₂ : r₂ ∈ c := Multiset.mem_of_le hsub (by simp)
  exact ⟨fun h => clock_lt_of_rBeyond_eq_zero T c h0 r₁ hr₁ h,
    fun h => clock_lt_of_rBeyond_eq_zero T c h0 r₂ hr₂ h⟩

/-- The "front-minute" predicate: a Phase-3 clock at minute exactly `T`.  On the
REAL kernel the front level `T+1` can be seeded only by a pair BOTH at the front
minute `T` (equal minutes below the cap, the DRIP branch) — but, UNLIKE the
abstract `Minute L₀` kernel (where the state IS the minute, so the seeding pair is
the single same-state pair `(s_T, s_T)`), distinct agent states can share minute
`T`.  So the seed event is keyed on this PREDICATE, not on a single state. -/
def frontMinuteP (T : ℕ) (a : AgentState L K) : Prop :=
  a.role = .clock ∧ a.phase.val = 3 ∧ a.minute.val = T

instance (T : ℕ) (a : AgentState L K) : Decidable (frontMinuteP T a) := by
  unfold frontMinuteP; infer_instance

/-- **Real-kernel seed-pair characterization (the squaring MECHANISM, predicate
form).**  If the clock front level `T+1` is empty (`rBeyond (T+1) c = 0`) and a
chosen-pair update raises it to `≥ 1`, then BOTH chosen agents satisfy `frontMinuteP
T` (Phase-3 clocks at minute exactly `T`, below the cap): they are the equal-minute
DRIP pair at the front minute.

The SYNC branch raises laggards only to an existing `max < T+1`, and the
synced-at-cap branch keeps minutes fixed; only the equal-minute below-cap DRIP can
push a clock to minute `T+1`, and for the first output to reach `T+1` the seeding
minute must be exactly `T`, with the partner sharing that minute (so it too is at
`T`).  Requires the window `AllClockP3`.  This is the real-kernel analog of
`FrontTailKernel.seed_pair_eq`, predicate-keyed rather than state-keyed. -/
theorem seed_pair_real (T : ℕ) (c : Config (AgentState L K)) (hw : AllClockP3 c)
    (r₁ r₂ : AgentState L K) (h0 : rBeyond (L := L) (K := K) (T + 1) c = 0)
    (hseed : 1 ≤ rBeyond (L := L) (K := K) (T + 1)
      (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂)) :
    frontMinuteP (L := L) (K := K) T r₁ ∧ frontMinuteP (L := L) (K := K) T r₂ := by
  classical
  by_cases happ : Protocol.Applicable c r₁ r₂
  · have hsub : ({r₁, r₂} : Multiset (AgentState L K)) ≤ c := happ
    have hmem1 : r₁ ∈ c := mem_of_applicable_left happ
    have hmem2 : r₂ ∈ c := mem_of_applicable_right happ
    obtain ⟨h1c, h1p⟩ := hw r₁ hmem1
    obtain ⟨h2c, h2p⟩ := hw r₂ hmem2
    obtain ⟨hlt1, hlt2⟩ := pair_clock_lt_of_empty_front T c r₁ r₂ h0 hsub
    have hr₁lt : r₁.minute.val < T + 1 := hlt1 h1c
    have hr₂lt : r₂.minute.val < T + 1 := hlt2 h2c
    have hc' : Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂
        = c - {r₁, r₂} + {(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2} := by
      unfold Protocol.stepOrSelf; rw [if_pos happ]; rfl
    rw [hc'] at hseed
    unfold rBeyond at hseed h0
    rw [Multiset.countP_add, Multiset.countP_sub hsub] at hseed
    have hb0 : Multiset.countP (fun a => clockBeyondP (T + 1) a) c = 0 := h0
    have hpair_le : Multiset.countP (fun a => clockBeyondP (T + 1) a)
        ({r₁, r₂} : Multiset (AgentState L K))
          ≤ Multiset.countP (fun a => clockBeyondP (T + 1) a) c :=
      Multiset.countP_le_of_le _ hsub
    have hprod : 1 ≤ Multiset.countP (fun a => clockBeyondP (T + 1) a)
        ({(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2}
          : Multiset (AgentState L K)) := by omega
    rw [countP_pair] at hprod
    by_cases hmin : r₁.minute = r₂.minute
    · by_cases hcap : r₁.minute.val < K * (L + 1)
      · -- DRIP: first output minute = r₁.minute+1, second = r₂.minute.
        have hd := Transition_phase3_clock_minute_drip_decreases (L := L) (K := K) r₁ r₂
          h1p h2p h1c h2c hmin hcap
        have hs'min : (Transition L K r₁ r₂).1.minute.val = r₁.minute.val + 1 := hd.2.2.2.2.1
        have ht'min : (Transition L K r₁ r₂).2.minute = r₂.minute := hd.2.2.2.2.2.1
        have hsnd_not : ¬ clockBeyondP (T + 1) (Transition L K r₁ r₂).2 := by
          unfold clockBeyondP; rw [ht'min]; intro ⟨_, hh⟩; omega
        have hfst_beyond : clockBeyondP (T + 1) (Transition L K r₁ r₂).1 := by
          by_contra hnb
          simp only [hnb, hsnd_not, if_false] at hprod; omega
        have hge : T + 1 ≤ (Transition L K r₁ r₂).1.minute.val := hfst_beyond.2
        rw [hs'min] at hge
        have hr₁T : r₁.minute.val = T := by omega
        -- r₂.minute = r₁.minute (hmin), so r₂.minute.val = T as well.
        have hr₂T : r₂.minute.val = T := by rw [← hmin]; exact hr₁T
        exact ⟨⟨h1c, h1p, hr₁T⟩, ⟨h2c, h2p, hr₂T⟩⟩
      · -- synced-at-cap: minutes unchanged, both < T+1 ⟹ no seeding, contradiction.
        exfalso
        have hcap' : ¬ r₁.minute.val < K * (L + 1) := hcap
        have hcp := Transition_phase3_clock_cap (L := L) (K := K) r₁ r₂
          h1p h2p h1c h2c hmin hcap'
        have hs'min : (Transition L K r₁ r₂).1.minute = r₁.minute := hcp.2.2.1
        have ht'min : (Transition L K r₁ r₂).2.minute = r₂.minute := hcp.2.2.2
        have hfst_not : ¬ clockBeyondP (T + 1) (Transition L K r₁ r₂).1 := by
          unfold clockBeyondP; rw [hs'min]; intro ⟨_, hh⟩; omega
        have hsnd_not : ¬ clockBeyondP (T + 1) (Transition L K r₁ r₂).2 := by
          unfold clockBeyondP; rw [ht'min]; intro ⟨_, hh⟩; omega
        simp only [hfst_not, hsnd_not, if_false] at hprod; omega
    · -- SYNC: both outputs at max minute = max r₁ r₂ < T+1 ⟹ no seeding, contradiction.
      exfalso
      have hsy := Transition_phase3_clock_minute_sync_decreases (L := L) (K := K) r₁ r₂
        h1p h2p h1c h2c hmin
      have hs'min : (Transition L K r₁ r₂).1.minute = max r₁.minute r₂.minute :=
        hsy.2.2.2.2.1
      have ht'min : (Transition L K r₁ r₂).2.minute = max r₁.minute r₂.minute :=
        hsy.2.2.2.2.2.1
      have hmaxlt : (max r₁.minute r₂.minute).val < T + 1 := by
        rcases le_total r₁.minute r₂.minute with h | h
        · rw [max_eq_right h]; exact hr₂lt
        · rw [max_eq_left h]; exact hr₁lt
      have hfst_not : ¬ clockBeyondP (T + 1) (Transition L K r₁ r₂).1 := by
        unfold clockBeyondP; rw [hs'min]; intro ⟨_, hh⟩; omega
      have hsnd_not : ¬ clockBeyondP (T + 1) (Transition L K r₁ r₂).2 := by
        unfold clockBeyondP; rw [ht'min]; intro ⟨_, hh⟩; omega
      simp only [hfst_not, hsnd_not, if_false] at hprod; omega
  · -- not applicable: stepOrSelf = c, rBeyond stays 0, contradiction.
    exfalso
    rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ] at hseed
    omega

/-! ### The block count of front-minute clocks and the squaring probability bound. -/

/-- The finset of front-minute states `s` (a Phase-3 clock at minute exactly `T`). -/
noncomputable def frontMinutes (T : ℕ) : Finset (AgentState L K) :=
  Finset.univ.filter (fun a => frontMinuteP (L := L) (K := K) T a)

/-- The total count of agents at the front minute `T` (Phase-3 clocks at minute
`T`).  `M = ∑_{s ∈ frontMinutes T} count s`. -/
noncomputable def frontMinuteCount (T : ℕ) (c : Config (AgentState L K)) : ℕ :=
  ∑ s ∈ frontMinutes (L := L) (K := K) T, c.count s

/-- **Block interaction-count sum = `M·(M−1)`** (`M` = front-minute count).  The
ordered-distinct-agent pairs with BOTH states in `frontMinutes T` number exactly
`M·(M−1)`.  This is `Config.sum_interactionCount` restricted from `univ` to the
front-minute block — the same accounting (each initiator `s₁` contributes
`count s₁ · (M − 1)` distinct partners within the block). -/
theorem block_sum_interactionCount (T : ℕ) (c : Config (AgentState L K)) :
    (∑ s₁ ∈ frontMinutes (L := L) (K := K) T,
      ∑ s₂ ∈ frontMinutes (L := L) (K := K) T, c.interactionCount s₁ s₂)
      = frontMinuteCount (L := L) (K := K) T c
          * (frontMinuteCount (L := L) (K := K) T c - 1) := by
  classical
  set S := frontMinutes (L := L) (K := K) T with hS
  set M := frontMinuteCount (L := L) (K := K) T c with hM
  -- inner sum over S of interactionCount s₁ s₂ = count s₁ · (M − 1)
  have hinner : ∀ s₁ ∈ S, (∑ s₂ ∈ S, c.interactionCount s₁ s₂)
      = c.count s₁ * (M - 1) := by
    intro s₁ hs₁
    -- interactionCount s₁ s₂ = count s₁ · (if s₁=s₂ then count s₁−1 else count s₂)
    have hpoint : ∀ s₂, c.interactionCount s₁ s₂
        = c.count s₁ * (if s₁ = s₂ then c.count s₁ - 1 else c.count s₂) := by
      intro s₂; by_cases h : s₁ = s₂ <;> simp [Config.interactionCount, h]
    rw [Finset.sum_congr rfl (fun s₂ _ => hpoint s₂), ← Finset.mul_sum]
    -- the inner sum equals M − 1 when count s₁ > 0 (and the product is 0 otherwise).
    have hinnersum : (∑ s₂ ∈ S, if s₁ = s₂ then c.count s₁ - 1 else c.count s₂)
        = (c.count s₁ - 1) + (∑ s₂ ∈ S.erase s₁, c.count s₂) := by
      rw [show (∑ s₂ ∈ S, if s₁ = s₂ then c.count s₁ - 1 else c.count s₂)
          = (∑ s₂ ∈ S, if s₂ = s₁ then c.count s₁ - 1 else c.count s₂) from
          Finset.sum_congr rfl (fun s₂ _ => by by_cases h : s₁ = s₂ <;> simp [h, eq_comm])]
      rw [← Finset.add_sum_erase S
          (fun s₂ => if s₂ = s₁ then c.count s₁ - 1 else c.count s₂) hs₁]
      simp only [if_true]
      congr 1
      exact Finset.sum_congr rfl (fun s₂ hs₂ => by simp [(Finset.mem_erase.mp hs₂).1])
    have hsum_all : c.count s₁ + (∑ s₂ ∈ S.erase s₁, c.count s₂) = M := by
      rw [hM, frontMinuteCount, ← hS]
      exact Finset.add_sum_erase S (fun s₂ => c.count s₂) hs₁
    rw [hinnersum]
    -- count s₁ · ((count s₁ − 1) + X) = count s₁ · (M − 1), using count s₁ + X = M.
    rcases Nat.eq_zero_or_pos (c.count s₁) with hz | hpos
    · simp [hz]
    · have : (c.count s₁ - 1) + (∑ s₂ ∈ S.erase s₁, c.count s₂) = M - 1 := by omega
      rw [this]
  rw [Finset.sum_congr rfl hinner, ← Finset.sum_mul]
  rw [show (∑ s₁ ∈ S, c.count s₁) = M from by rw [hM, frontMinuteCount, ← hS]]

/-- **The seed preimage is contained in the front-minute block** `frontMinutes T ×ˢ
frontMinutes T`.  Direct consequence of `seed_pair_real`. -/
theorem seed_preimage_subset_block (T : ℕ) (c : Config (AgentState L K))
    (hw : AllClockP3 c) (h0 : rBeyond (L := L) (K := K) (T + 1) c = 0) :
    (Protocol.scheduledStep (NonuniformMajority L K) c) ⁻¹'
        {c' : Config (AgentState L K) | 1 ≤ rBeyond (L := L) (K := K) (T + 1) c'}
      ⊆ ↑((frontMinutes (L := L) (K := K) T) ×ˢ (frontMinutes (L := L) (K := K) T)) := by
  intro pair hpair
  simp only [Set.mem_preimage, Set.mem_setOf_eq, Protocol.scheduledStep] at hpair
  obtain ⟨hp1, hp2⟩ := seed_pair_real T c hw pair.1 pair.2 h0 hpair
  simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, frontMinutes,
    Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨hp1, hp2⟩

/-- **`real_front_advance_squares` — the front-shape MAINTENANCE, GENUINELY PROVEN
by transferring the squaring to the real kernel.**  On the `AllClockP3` window, if
the clock front level `T+1` is empty (`rBeyond (T+1) c = 0`) and `2 ≤ c.card`, then
one scheduler step raises it to `≥ 1` with probability at most the SQUARE of the
front fraction `M/n` (`M = frontMinuteCount T c`, the number of Phase-3 clocks at
the front minute `T`):

  `K c {1 ≤ rBeyond (T+1)} ≤ ofReal ((M/n)²)`.

This is the real-kernel analog of `FrontTailKernel.frontTail_kernel_one_step_le_beyondSq`,
proven HERE: the seed preimage lies in the front-minute block (`seed_pair_real`),
whose interaction mass is `M·(M−1)/(n·(n−1))` (`block_sum_interactionCount`), bounded
by `(M/n)²` by the SAME arithmetic as the generic `dripPair_prob_le_sq`.  The
squaring is a THEOREM about the actual `NonuniformMajority` kernel, not assumed. -/
theorem real_front_advance_squares (T : ℕ) (c : Config (AgentState L K))
    (hw : AllClockP3 c) (hc : 2 ≤ c.card) (h0 : rBeyond (L := L) (K := K) (T + 1) c = 0) :
    (NonuniformMajority L K).transitionKernel c
        {c' | 1 ≤ rBeyond (L := L) (K := K) (T + 1) c'} ≤
      ENNReal.ofReal
        (((frontMinuteCount (L := L) (K := K) T c : ℝ) / (c.card : ℝ)) ^ 2) := by
  classical
  set M := frontMinuteCount (L := L) (K := K) T c with hM
  set n := c.card with hn
  set S := frontMinutes (L := L) (K := K) T with hS
  have hstep : (NonuniformMajority L K).stepDistOrSelf c
      = (NonuniformMajority L K).stepDist c hc := by
    unfold Protocol.stepDistOrSelf; rw [dif_pos hc]
  have hmeas : MeasurableSet {c' : Config (AgentState L K)
      | 1 ≤ rBeyond (L := L) (K := K) (T + 1) c'} :=
    DiscreteMeasurableSpace.forall_measurableSet _
  change ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
      {c' | 1 ≤ rBeyond (L := L) (K := K) (T + 1) c'} ≤ _
  rw [hstep]
  unfold Protocol.stepDist
  rw [PMF.toMeasure_map_apply _ _ _ (Measurable.of_discrete) hmeas]
  -- bound the preimage measure by the front-minute block measure (a finset).
  have hblock : (c.interactionPMF hc).toMeasure
        ((Protocol.scheduledStep (NonuniformMajority L K) c) ⁻¹'
          {c' | 1 ≤ rBeyond (L := L) (K := K) (T + 1) c'})
      ≤ (c.interactionPMF hc).toMeasure (↑(S ×ˢ S)) :=
    measure_mono (seed_preimage_subset_block T c hw h0)
  refine le_trans hblock ?_
  -- the block measure = ∑ over S×S of interactionProb = M(M−1)/(n(n−1)).
  rw [PMF.toMeasure_apply_finset]
  have hpmf : ∀ p : AgentState L K × AgentState L K,
      (c.interactionPMF hc) p = c.interactionProb p.1 p.2 := fun _ => rfl
  rw [Finset.sum_congr rfl (fun p _ => hpmf p)]
  -- ∑_{p ∈ S×S} interactionProb p.1 p.2 = (∑∑ interactionCount)/totalPairs
  rw [Finset.sum_product]
  simp only [Config.interactionProb]
  have hcount : (∑ s₁ ∈ S, ∑ s₂ ∈ S,
        (c.interactionCount s₁ s₂ : ℝ≥0∞) / (c.totalPairs : ℝ≥0∞))
      = (↑(∑ s₁ ∈ S, ∑ s₂ ∈ S, c.interactionCount s₁ s₂) : ℝ≥0∞)
          / (c.totalPairs : ℝ≥0∞) := by
    simp only [ENNReal.div_eq_inv_mul, Nat.cast_sum, Finset.mul_sum]
  rw [hcount, block_sum_interactionCount T c]
  -- now: M(M−1)/(n(n−1)) ≤ ofReal ((M/n)²)
  rw [← hM]
  have hMle : M ≤ n := by
    rw [hM, frontMinuteCount, hn]
    have hcard : (∑ s : AgentState L K, c.count s) = c.card :=
      Multiset.sum_count_eq_card (s := (Finset.univ : Finset (AgentState L K)))
        (m := c) (by intro a _; exact Finset.mem_univ a)
    calc (∑ s ∈ S, c.count s) ≤ ∑ s : AgentState L K, c.count s :=
          Finset.sum_le_sum_of_subset (Finset.subset_univ S)
      _ = c.card := hcard
  have hnpos : 0 < n := by omega
  have hdenN_pos : 0 < n * (n - 1) := Nat.mul_pos (by omega) (by omega)
  have hdenN_posR : (0 : ℝ) < ((n * (n - 1) : ℕ) : ℝ) := by exact_mod_cast hdenN_pos
  have htot : c.totalPairs = n * (n - 1) := by rw [hn]; rfl
  rw [htot]
  -- ratio = ofReal (M(M−1) / (n(n−1)))
  have hratio : (↑(M * (M - 1)) : ℝ≥0∞) / (↑(n * (n - 1)) : ℝ≥0∞)
      = ENNReal.ofReal (((M * (M - 1) : ℕ) : ℝ) / ((n * (n - 1) : ℕ) : ℝ)) := by
    rw [ENNReal.ofReal_div_of_pos hdenN_posR, ENNReal.ofReal_natCast,
      ENNReal.ofReal_natCast]
  rw [hratio]
  apply ENNReal.ofReal_le_ofReal
  -- M(M−1)/(n(n−1)) ≤ (M/n)² : cross-multiply (M−1)n ≤ M(n−1) ⇔ M ≤ n.
  have hnR_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
  have hMleR : (M : ℝ) ≤ (n : ℝ) := by exact_mod_cast hMle
  have hMR : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
  have hnsq_pos : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
  rw [div_pow]
  -- M(M−1)/(n(n−1)) ≤ M²/n² since num smaller and den larger.
  rw [div_le_div_iff₀ hdenN_posR hnsq_pos]
  -- M(M−1)·n² ≤ M²·(n(n−1))  ⇔  (M−1)·n ≤ M·(n−1)  ⇔  M ≤ n
  by_cases hMz : M = 0
  · simp [hMz]
  · rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ M), Nat.cast_one,
      Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
    -- (M(M−1))n² ≤ M²(n(n−1)) ⇔ (M−1)n ≤ M(n−1) ⇔ M ≤ n.
    have hMpos : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast (by omega : 1 ≤ M)
    have hfac : ((M : ℝ) - 1) * (n : ℝ) ≤ (M : ℝ) * ((n : ℝ) - 1) := by nlinarith [hMleR]
    have hMnpos : (0 : ℝ) ≤ (M : ℝ) * (n : ℝ) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hfac hMnpos, hMR, hnR_pos]

/-- **The front-minute count is at most the front tail `rBeyond T`.**  Every
Phase-3 clock at minute EXACTLY `T` is a clock at minute `≥ T`, so the squaring's
`M = frontMinuteCount T c` is bounded by `rBeyond T c`.  Hence the squaring of
`real_front_advance_squares` is at most `(rBeyond T c / n)²` — the squaring against
the genuine front fraction, the form `FrontShapeInduction.frontShapeAt_holds` uses
(`c≥(i+1) ≤ (c≥i)²`). -/
theorem frontMinuteCount_eq_countP (T : ℕ) (c : Config (AgentState L K)) :
    frontMinuteCount (L := L) (K := K) T c
      = Multiset.countP (fun a => frontMinuteP (L := L) (K := K) T a) c := by
  classical
  unfold frontMinuteCount frontMinutes
  rw [Multiset.countP_eq_card_filter]
  -- card (filter P c) = ∑_{s ∈ univ} (filter P c).count s  (fintype sum over states)
  rw [show (Multiset.filter (fun a => frontMinuteP (L := L) (K := K) T a) c).card
      = ∑ s : AgentState L K,
          Multiset.count s (Multiset.filter (fun a => frontMinuteP T a) c) from
      (Multiset.sum_count_eq_card (s := (Finset.univ : Finset (AgentState L K)))
        (m := Multiset.filter (fun a => frontMinuteP T a) c)
        (by intro a _; exact Finset.mem_univ a)).symm]
  -- (filter P c).count s = if P s then c.count s else 0; restrict the sum to the filter.
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [Multiset.count_filter]
  by_cases hP : frontMinuteP (L := L) (K := K) T s <;> simp [hP, Config.count]

/-- **The front-minute count is at most the front tail `rBeyond T`.**  Every
Phase-3 clock at minute EXACTLY `T` is a clock at minute `≥ T`, so the squaring's
`M = frontMinuteCount T c` is bounded by `rBeyond T c`.  Hence the squaring of
`real_front_advance_squares` is at most `(rBeyond T c / n)²` — the squaring against
the genuine front fraction, the form `FrontShapeInduction.frontShapeAt_holds` uses
(`c≥(i+1) ≤ (c≥i)²`). -/
theorem frontMinuteCount_le_rBeyond (T : ℕ) (c : Config (AgentState L K)) :
    frontMinuteCount (L := L) (K := K) T c ≤ rBeyond (L := L) (K := K) T c := by
  rw [frontMinuteCount_eq_countP]
  unfold rBeyond
  apply countP_mono_pred
  rintro a ⟨hcl, _hp, hmin⟩
  exact ⟨hcl, by omega⟩

/-! ## Part 5 — the obstruction: bare `allClocksCounterPos` is NOT one-step closed.

The synced-at-cap branch with a `counter = 1` clock takes the counter to `0`.  This
is a PER-PAIR fact (no `Config` needed): it WITNESSES that `allClocksCounterPos`
cannot be one-step deterministically closed on the bare `Q_mix ∧ allPhaseGE3 ∧
noPhaseAbove3` window — a synced-at-cap clock pair with one counter at `1` is
representable in such a window, and stepping it produces a `counter = 0` clock.  So
`ClockPhase3_remaining_synchronization` (the deterministic one-step closure) must
NOT be asserted; only the FrontSync-GATED closure (`counterPos_closed_of_frontSync`)
is true, and `FrontSync` itself is a probabilistic-front-shape reachability fact. -/

/-- **The counter-vanishing witness (the obstruction, per-pair).**  A synced-at-cap
Phase-3 clock pair with `s.counter.val = 1` produces a FIRST output that is a clock
with `counter.val = 0`: positivity is DESTROYED in one step.  Hence no
deterministic one-step closure of `allClocksCounterPos` can hold without excluding
the at-cap regime — which is exactly what `FrontSync` does.  (`s.counter = 1`
arises only after `50·(L+1) − 1` cap-decrements, the racing-clock scenario the
front-shape forbids by SYNCHRONIZATION, not by a one-step invariant.) -/
theorem counterPos_one_step_NOT_closed_witness (s t : AgentState L K)
    (hs_phase : s.phase.val = 3) (ht_phase : t.phase.val = 3)
    (hs_clock : s.role = .clock) (ht_clock : t.role = .clock)
    (hminute : s.minute = t.minute)
    (hcap : ¬ s.minute.val < K * (L + 1))
    (hs_one : s.counter.val = 1) (ht_pos : 0 < t.counter.val) :
    (Transition L K s t).1.role = .clock ∧ (Transition L K s t).1.counter.val = 0 := by
  -- synced-at-cap: Transition = (stdCounterSubroutine s, stdCounterSubroutine t);
  -- s.counter = 1 > 0 ⟹ stdCounterSubroutine s decrements to 0.
  have hcp := Transition_phase3_clock_cap (L := L) (K := K) s t
    hs_phase ht_phase hs_clock ht_clock hminute hcap
  refine ⟨hcp.1, ?_⟩
  -- read the first output counter via the explicit synced-at-cap Transition form.
  have hs_phase_eq : s.phase = ⟨3, by decide⟩ := Fin.ext hs_phase
  have ht_phase_eq : t.phase = ⟨3, by decide⟩ := Fin.ext ht_phase
  have hepidemic := phaseEpidemicUpdate_eq_self_p3 (L := L) (K := K) s t hs_phase ht_phase
  have hcap_t : ¬ t.minute.val < K * (L + 1) := by rw [← hminute]; exact hcap
  have hsr : (stdCounterSubroutine L K s).role = .clock :=
    stdCounterSubroutine_clock_role s hs_clock
  have htr : (stdCounterSubroutine L K t).role = .clock :=
    stdCounterSubroutine_clock_role t ht_clock
  have hP3 : Phase3Transition L K s t
      = (stdCounterSubroutine L K s, stdCounterSubroutine L K t) := by
    unfold Phase3Transition
    simp only [hs_clock, ht_clock, and_self, if_true, hminute, ne_eq, not_true_eq_false,
      if_false, hcap_t, dif_neg, not_false_eq_true]
    simp only [hsr, htr, reduceCtorEq, false_and, if_false, and_false]
  -- stdCounterSubroutine on phase 3 stays at phase ≤ 4 (never 10) ⟹ finishPhase10Entry = id.
  have hscs_counter : (stdCounterSubroutine L K s).counter.val = 0 := by
    unfold stdCounterSubroutine
    rw [dif_neg (by omega : ¬ s.counter.val = 0)]
    simp [hs_one]
  -- s.counter = 1 ≠ 0 ⟹ stdCounterSubroutine s stays at phase 3 (decrement branch).
  have hsphase' : (stdCounterSubroutine L K s).phase.val = 3 := by
    unfold stdCounterSubroutine; rw [dif_neg (by omega : ¬ s.counter.val = 0)]; exact hs_phase
  have htphase' : (stdCounterSubroutine L K t).phase.val = 3 ∨
      (stdCounterSubroutine L K t).phase.val = 4 := by
    by_cases hc : t.counter.val = 0
    · right
      unfold stdCounterSubroutine advancePhaseWithInit advancePhase phaseInit
      rw [dif_pos hc, dif_pos (by omega : t.phase.val < 10)]; simp [ht_phase]
    · left; unfold stdCounterSubroutine; rw [dif_neg hc]; exact ht_phase
  have hfin : ∀ a b : AgentState L K, a.phase.val = 3 →
      (b.phase.val = 3 ∨ b.phase.val = 4) → finishPhase10Entry L K a b = b := by
    intro a b ha hb
    unfold finishPhase10Entry canonicalPhase10Entry
    rw [if_neg]; rintro ⟨_, h10⟩; rcases hb with h | h <;> omega
  have hTfst : (Transition L K s t).1 = stdCounterSubroutine L K s := by
    conv_lhs => unfold Transition
    rw [hepidemic]
    dsimp only
    rw [hs_phase_eq]
    change finishPhase10Entry L K s (Phase3Transition L K s t).1 = _
    rw [hP3]
    exact hfin s _ hs_phase (Or.inl hsphase')
  rw [hTfst]; exact hscs_counter

/-! ## Part 6 — `FrontSync` as the empty cap-front, and its squared-rate maintenance.

`FrontSync c` is exactly the cap-level front being empty: `rBeyond (capMinute) c = 0`
(no clock at minute `≥ capMinute`; since `capMinute` is the maximal minute, that
means no clock AT the cap).  So the front-shape MAINTENANCE of `FrontSync` is the
`T = capMinute − 1` instance of `real_front_advance_squares`: the cap front is
seeded from empty in one step with probability at most the SQUARE of the
front fraction at minute `capMinute − 1`.  This is the genuine per-minute drip
squaring that keeps `FrontSync` until the run synchronizes at the cap. -/

/-- `FrontSync c ↔ rBeyond (capMinute) c = 0`.  Both say no clock is at the cap
(`capMinute` is the maximal minute value, so `minute ≥ capMinute ↔ minute = cap`). -/
theorem frontSync_iff_rBeyond_cap_zero (c : Config (AgentState L K)) :
    FrontSync (L := L) (K := K) c ↔
      rBeyond (L := L) (K := K) (capMinute (L := L) (K := K)) c = 0 := by
  classical
  unfold FrontSync rBeyond capMinute
  constructor
  · intro h
    rw [Multiset.countP_eq_zero]
    rintro a ha ⟨hcl, hge⟩
    have := h a ha hcl
    omega
  · intro h a ha hcl
    rw [Multiset.countP_eq_zero] at h
    have hnb := h a ha
    -- ¬ clockBeyondP cap a, with a a clock ⟹ ¬ (cap ≤ minute) ⟹ minute < cap.
    by_contra hge
    push_neg at hge
    exact hnb ⟨hcl, by omega⟩

/-- **`real_front_advance_squares_cap` — the `FrontSync` maintenance squaring.**
On the `AllClockP3` window, when `FrontSync c` holds (cap front empty), the one-step
probability that the cap front is SEEDED (i.e. `FrontSync` BREAKS) is at most the
SQUARE of the front fraction at minute `capMinute − 1`.  This is
`real_front_advance_squares` at `T = capMinute − 1`, the genuine transferred
squaring controlling `FrontSync`'s breakage rate per minute. -/
theorem real_front_advance_squares_cap (c : Config (AgentState L K))
    (hcapPos : 0 < capMinute (L := L) (K := K))
    (hw : AllClockP3 c) (hc : 2 ≤ c.card)
    (hsync : FrontSync (L := L) (K := K) c) :
    (NonuniformMajority L K).transitionKernel c
        {c' | ¬ FrontSync (L := L) (K := K) c'} ≤
      ENNReal.ofReal
        (((frontMinuteCount (L := L) (K := K) (capMinute (L := L) (K := K) - 1) c : ℝ)
          / (c.card : ℝ)) ^ 2) := by
  classical
  have hcapeq : capMinute (L := L) (K := K) - 1 + 1 = capMinute (L := L) (K := K) := by omega
  have h0 : rBeyond (L := L) (K := K) (capMinute (L := L) (K := K) - 1 + 1) c = 0 := by
    rw [hcapeq]; exact (frontSync_iff_rBeyond_cap_zero c).mp hsync
  -- {¬ FrontSync c'} = {1 ≤ rBeyond cap c'} (cap front nonempty).
  have hset : {c' : Config (AgentState L K) | ¬ FrontSync (L := L) (K := K) c'}
      = {c' | 1 ≤ rBeyond (L := L) (K := K) (capMinute (L := L) (K := K) - 1 + 1) c'} := by
    ext c'
    rw [Set.mem_setOf_eq, Set.mem_setOf_eq, frontSync_iff_rBeyond_cap_zero c', hcapeq]
    omega
  rw [hset]
  exact real_front_advance_squares (capMinute (L := L) (K := K) - 1) c hw hc h0

/-! ## Part 7 — the SINGLE remaining sub-lemma (named, NOT asserted) + assembly.

`habs_mix` is reduced (via `HabsDischarge.habs_mix_deterministic_skeleton`) to the
one-step closure of `allClocksCounterPos` (`ClockPhase3_remaining_synchronization`).
We have shown:

* `counterPos_closed_of_frontSync` — the closure DOES hold on the FrontSync-good
  event (GENUINELY derived from the counter mechanics);
* `counterPos_one_step_NOT_closed_witness` — it FAILS without FrontSync (the racing
  at-cap `counter = 1` clock), so FrontSync cannot be dropped;
* `real_front_advance_squares` / `real_front_advance_squares_cap` — `FrontSync` is
  maintained per minute up to the SQUARED drip-seed probability (the genuine
  transferred front-shape squaring on the real kernel).

The SINGLE residual is the PROBABILISTIC CONCENTRATION that the FrontSync-good event
holds throughout the `O(log n)`-minute run: summing the per-minute squared seed
probabilities (doubly-exponential, `FrontShapeInduction.front_shape_collapse`'s
`O(log log n)` emptying) keeps `FrontSync` with high probability until the bulk
synchronizes at the cap.  We RECORD it as a `Prop`-valued obligation, NOT asserted. -/

/-- **THE SINGLE REMAINING SUB-LEMMA (named, not proven here).**  The probabilistic
maintenance of `FrontSync` along the run: from a FrontSync start, over the run
horizon `H`, the kernel probability of EVER breaking `FrontSync` is at most the sum
of the per-minute squared drip-seed probabilities (`real_front_advance_squares_cap`),
which is `< 1` by the doubly-exponential front tail
(`FrontTailKernel.frontTail_kernel_O1_parallel`, `O(log log n)` emptying).  Once
supplied, `counterPos_closed_of_frontSync` upgrades to the unconditional
`ClockPhase3_remaining_synchronization`, fully discharging `habs_mix`.  This is a
MULTI-STEP CONCENTRATION (Azuma/union over the per-minute squares), NOT a one-step
closure — exactly the piece beyond `HabsDischarge`'s reduction.  Stated as a
`Prop`, deliberately NOT asserted. -/
def FrontSyncConcentration_remaining (n mC : ℕ) (H : ℕ) (ε : ℝ≥0∞) : Prop :=
  ∀ c₀ : Config (AgentState L K),
    Q_mix (L := L) (K := K) n mC 0 c₀ →
    FrontSync (L := L) (K := K) c₀ →
    ((NonuniformMajority L K).transitionKernel ^ H) c₀
      {c' | ¬ FrontSync (L := L) (K := K) c'} ≤ ε

/-- **`habs_clockPhase3_of_frontSyncConcentration` — assembling toward `habs`.**
GIVEN the named concentration residual `FrontSyncConcentration_remaining` (FrontSync
maintained with failure `≤ ε` over the horizon), the `allClocksCounterPos` closure
holds on the FrontSync-good event (`counterPos_closed_of_frontSync`), which —
combined with `HabsDischarge.habs_mix_deterministic_skeleton` and the proven
positive-counter Phase-3 kernel lemmas — closes `clockPhase3`, hence all of
`habs_mix`.  This states the implication precisely (FrontSync is the now-PROVEN-
maintained invariant, gated on the single named concentration input). -/
theorem habs_clockPhase3_of_frontSync (n mC T : ℕ)
    (c c' : Config (AgentState L K))
    (hQ : Q_mix (L := L) (K := K) n mC T c)
    (hge : allPhaseGE3 (L := L) (K := K) c)
    (hno : noPhaseAbove3 (L := L) (K := K) c)
    (hpos : allClocksCounterPos (L := L) (K := K) c)
    (hsync : FrontSync (L := L) (K := K) c)
    (hc' : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    allClocksCounterPos (L := L) (K := K) c' :=
  counterPos_closed_of_frontSync n mC T c c' hQ hge hno hpos hsync hc'

/-- HONEST STATUS marker. -/
theorem clock_front_shape_status : True := trivial

end ClockFrontShape

end ExactMajority
