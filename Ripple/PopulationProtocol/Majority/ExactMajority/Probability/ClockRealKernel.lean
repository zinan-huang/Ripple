/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Avenue D-lynch — the clock-minute advance drift ON THE REAL kernel

This file is the LINCHPIN of the Doty et al. §6 time-half campaign.  C3/C4/C5
proved the speedup on the ABSTRACT `clockProto`, whose carrier is `Fin (L₀+1)`.
The REAL protocol's clock is the `AgentState.minute` field inside
`NonuniformMajority L K`.  D-lynch builds the clock-minute advance DIRECTLY on
the real kernel — the FAITHFUL link, NOT an assumed lumpability/time-change (the
"C2 lesson").

We transplant C3's `seedPot_contracts_on_floor` to the real kernel:

* `rBeyond T c` — the count of *clock* agents whose minute is at or beyond a
  fixed level `T`; the real-kernel analog of `ClockTime.beyond`.  The threshold
  predicate `role = clock ∧ T ≤ minute` is the "spreading opinion".
* The window `AllClockP3` = "every agent is a Clock in Phase 3" makes every
  applicable ordered pair a Phase-3 clock-clock interaction, so the proven
  per-pair descent lemmas (`Transition_phase3_clock_minute_{sync,drip}_decreases`)
  apply to EVERY pair.  We prove `rBeyond T` is non-decreasing on the kernel
  support over this window (`rBeyond_ge_monotone`), handling ALL THREE Phase-3
  clock-clock branches (sync / drip-below-cap / synced-at-cap counter advance):
  every branch keeps both agents Clocks and never lowers a minute.
* `rDrip_pair_advances` / `clock_real_drip_advance_prob` — the single same-state
  drip pair `(s_T, s_T)` at minute exactly `T` raises `rBeyond (T+1)` by one,
  with scheduler probability `m·(m−1)/(card·(card−1))` (`m = count s_T`).  This
  is where Doty's `1/c²` (clock-fraction squared) appears NATURALLY by
  pair-counting; it is DERIVED, never assumed.
* `rSeedPot_contracts_on_floor` — the genuine drift `∫Φ dK(c) ≤ r·Φ(c)` on the
  real kernel, mirroring C3's structure.
* `clock_real_advance` — packages the drift into a
  `PhaseConvergence (NonuniformMajority L K).transitionKernel` via Avenue F's
  `windowDrift_PhaseConvergence`.

NEW file; no existing file is edited; no sorry/admit/axiom/native_decide.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Analysis.PhaseProgress
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.WindowConcentration
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.NonuniformMarkovChain

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real BigOperators

namespace ClockRealKernel

variable {L K : ℕ}

/-- Discrete measurable space on agent states (needed for the scheduler PMF over
ordered pairs, exactly as `Config`'s `⊤` instance). -/
noncomputable instance instMeasurableSpaceAgentState :
    MeasurableSpace (AgentState L K) := ⊤

instance instDiscreteMeasurableSpaceAgentState :
    DiscreteMeasurableSpace (AgentState L K) where
  forall_measurableSet _ := trivial

/-! ## Part 0 — the Phase-3 epidemic identity (own copy, public deps only).

The proven per-pair lemmas in `PhaseProgress` use a `private` epidemic-identity
helper.  We re-prove it here from the PUBLIC `runInitsBetween_self_api`, so the
synced-at-cap branch can be unfolded without touching `PhaseProgress`. -/

theorem phaseEpidemicUpdate_eq_self_p3 (s t : AgentState L K)
    (hs : s.phase.val = 3) (ht : t.phase.val = 3) :
    phaseEpidemicUpdate L K s t = (s, t) := by
  have hs_eq : s.phase = ⟨3, by decide⟩ := Fin.ext hs
  have ht_eq : t.phase = ⟨3, by decide⟩ := Fin.ext ht
  unfold phaseEpidemicUpdate
  rw [hs_eq, ht_eq, max_self]
  simp only [runInitsBetween_self_api]
  cases s
  cases t
  simp_all

/-! ## Part 1 — the per-pair clock behaviour on the Phase-3 window.

On a Phase-3 clock-clock pair, BOTH transition outputs are Clocks and NEITHER
minute drops below the smaller of the two inputs.  We split the three Phase-3
clock-clock branches: sync (unequal minutes), drip (equal, below the cap), and
the synced-at-cap counter advance (equal, at the cap).  Branches 1,2 reuse the
proven public descent lemmas; branch 3 is unfolded here. -/

/-- The synced-at-cap branch: two Clocks in Phase 3 at the SAME minute equal to
the cap.  Both outputs stay Clocks and keep minute = the cap (`stdCounterSubroutine`
does not touch `minute`, and the 3→4 phase advance's Init does not reset it). -/
theorem Transition_phase3_clock_cap
    (s t : AgentState L K)
    (hs_phase : s.phase.val = 3) (ht_phase : t.phase.val = 3)
    (hs_clock : s.role = .clock) (ht_clock : t.role = .clock)
    (hminute : s.minute = t.minute)
    (hcap : ¬ s.minute.val < K * (L + 1)) :
    (Transition L K s t).1.role = .clock ∧
      (Transition L K s t).2.role = .clock ∧
      (Transition L K s t).1.minute = s.minute ∧
      (Transition L K s t).2.minute = t.minute := by
  have hs_phase_eq : s.phase = ⟨3, by decide⟩ := Fin.ext hs_phase
  have ht_phase_eq : t.phase = ⟨3, by decide⟩ := Fin.ext ht_phase
  have hepidemic := phaseEpidemicUpdate_eq_self_p3 (L := L) (K := K) s t hs_phase ht_phase
  have hcap_t : ¬ t.minute.val < K * (L + 1) := by
    simpa [hminute] using hcap
  -- the synced-at-cap Phase-3 transition outputs are the two counter-subroutine
  -- results (Rules 2/3/4 do not fire: both outputs remain Clocks).
  have hPhase3 :
      Phase3Transition L K s t =
        (stdCounterSubroutine L K s, stdCounterSubroutine L K t) := by
    unfold Phase3Transition
    have hsr : (stdCounterSubroutine L K s).role = .clock :=
      stdCounterSubroutine_clock_role s hs_clock
    have htr : (stdCounterSubroutine L K t).role = .clock :=
      stdCounterSubroutine_clock_role t ht_clock
    simp only [hs_clock, ht_clock, and_self, if_true, hminute, ne_eq, not_true_eq_false,
      if_false, hcap_t, dif_neg, not_false_eq_true]
    simp only [hsr, htr, reduceCtorEq, false_and, if_false, and_false]
  -- the counter subroutine never touches `minute`; from Phase 3 it advances to
  -- Phase 4 whose Init also leaves `minute` untouched.
  have hmin : ∀ a : AgentState L K, a.phase.val = 3 →
      (stdCounterSubroutine L K a).minute = a.minute := by
    intro a ha
    unfold stdCounterSubroutine
    by_cases hc : a.counter.val = 0
    · rw [dif_pos hc]
      unfold advancePhaseWithInit advancePhase
      rw [dif_pos (by omega : a.phase.val < 10)]
      -- advanced phase is 4; phaseInit p=4 only sets `output`, leaving `minute`.
      set b : AgentState L K :=
        { a with phase := ⟨a.phase.val.succ, by have := a.phase.2; omega⟩ } with hb
      have hbph : b.phase.val = 4 := by rw [hb]; simp [ha]
      have hbmin : b.minute = a.minute := by rw [hb]
      show (phaseInit L K b.phase b).minute = a.minute
      unfold phaseInit
      rw [dif_neg (by omega : ¬ b.phase.val = 1),
          dif_neg (by omega : ¬ b.phase.val = 2),
          dif_neg (by omega : ¬ b.phase.val = 3),
          dif_pos hbph]
    · rw [dif_neg hc]
  have hrole : ∀ a : AgentState L K, a.role = .clock →
      (stdCounterSubroutine L K a).role = .clock :=
    fun a ha => stdCounterSubroutine_clock_role a ha
  -- phase of stdCounterSubroutine output ∈ {3, 4} (never 10), so finishPhase10Entry is identity.
  have hsphase' : (stdCounterSubroutine L K s).phase.val = 3 ∨
      (stdCounterSubroutine L K s).phase.val = 4 := by
    by_cases hc : s.counter.val = 0
    · right
      unfold stdCounterSubroutine advancePhaseWithInit advancePhase phaseInit
      rw [dif_pos hc, dif_pos (by omega : s.phase.val < 10)]
      simp [hs_phase]
    · left; unfold stdCounterSubroutine; rw [dif_neg hc]; exact hs_phase
  have htphase' : (stdCounterSubroutine L K t).phase.val = 3 ∨
      (stdCounterSubroutine L K t).phase.val = 4 := by
    by_cases hc : t.counter.val = 0
    · right
      unfold stdCounterSubroutine advancePhaseWithInit advancePhase phaseInit
      rw [dif_pos hc, dif_pos (by omega : t.phase.val < 10)]
      simp [ht_phase]
    · left; unfold stdCounterSubroutine; rw [dif_neg hc]; exact ht_phase
  have hfin : ∀ (a b : AgentState L K), a.phase.val = 3 →
      (b.phase.val = 3 ∨ b.phase.val = 4) → finishPhase10Entry L K a b = b := by
    intro a b ha hb
    unfold finishPhase10Entry canonicalPhase10Entry
    rw [if_neg]
    rintro ⟨_, h10⟩
    rcases hb with h | h <;> omega
  have hT : Transition L K s t = (stdCounterSubroutine L K s, stdCounterSubroutine L K t) := by
    conv_lhs => unfold Transition
    rw [hepidemic]
    dsimp only []
    rw [hs_phase_eq]
    show (finishPhase10Entry L K s (Phase3Transition L K s t).1,
          finishPhase10Entry L K t (Phase3Transition L K s t).2) = _
    rw [hPhase3]
    rw [hfin s _ hs_phase hsphase', hfin t _ ht_phase htphase']
  rw [hT]
  exact ⟨hrole s hs_clock, hrole t ht_clock, hmin s hs_phase, hmin t ht_phase⟩

/-! ## Part 2 — the `rBeyond T` count and its per-pair monotonicity.

`rBeyond T c` counts Clock agents whose minute is at or beyond `T`.  On the
all-Clock-Phase-3 window every applicable pair is a Phase-3 clock-clock pair, and
in every one of the three branches both outputs are Clocks with no minute lowered,
so the per-pair count of `{role = clock ∧ T ≤ minute}` never decreases.  This is
the real-kernel transport of `ClockTime.beyond_pair_mono`. -/

/-- The threshold predicate: a Clock agent at minute `≥ T`. -/
def clockBeyondP (T : ℕ) (a : AgentState L K) : Prop := a.role = .clock ∧ T ≤ a.minute.val

instance (T : ℕ) (a : AgentState L K) : Decidable (clockBeyondP T a) := by
  unfold clockBeyondP; infer_instance

/-- The count of Clock agents at minute `≥ T` (real-kernel analog of `beyond`). -/
def rBeyond (T : ℕ) (c : Config (AgentState L K)) : ℕ :=
  Multiset.countP (fun a => clockBeyondP T a) c

/-- The window: every agent in `c` is a Clock in Phase 3. -/
def AllClockP3 (c : Config (AgentState L K)) : Prop :=
  ∀ a ∈ c, a.role = .clock ∧ a.phase.val = 3

/-- `countP` of the threshold predicate over a two-element pair. -/
theorem countP_pair (T : ℕ) (x y : AgentState L K) :
    Multiset.countP (fun a => clockBeyondP T a) ({x, y} : Multiset (AgentState L K))
      = (if clockBeyondP T x then 1 else 0) + (if clockBeyondP T y then 1 else 0) := by
  rw [show ({x, y} : Multiset (AgentState L K)) = x ::ₘ y ::ₘ 0 from rfl]
  rw [Multiset.countP_cons, Multiset.countP_cons, Multiset.countP_zero]
  ring

/-- **The per-pair monotonicity of `rBeyond T`** on a Phase-3 clock-clock pair.
In every branch (sync / drip / synced-at-cap) both `Transition` outputs are
Clocks and no minute is lowered, so the threshold count over the produced pair is
at least the count over the consumed pair.  This is the genuine combinatorial
core that lifts the proven per-pair descent lemmas to the count level. -/
theorem rBeyond_pair_mono (T : ℕ) (s t : AgentState L K)
    (hs_phase : s.phase.val = 3) (ht_phase : t.phase.val = 3)
    (hs_clock : s.role = .clock) (ht_clock : t.role = .clock) :
    Multiset.countP (fun a => clockBeyondP T a) ({s, t} : Multiset (AgentState L K))
      ≤ Multiset.countP (fun a => clockBeyondP T a)
          ({(Transition L K s t).1, (Transition L K s t).2}
            : Multiset (AgentState L K)) := by
  set s' := (Transition L K s t).1 with hs'
  set t' := (Transition L K s t).2 with ht'
  rw [countP_pair, countP_pair]
  by_cases hmin : s.minute = t.minute
  · by_cases hcap : s.minute.val < K * (L + 1)
    · -- DRIP: s' minute = s.minute + 1, t' minute = t.minute, both Clocks.
      have hd := Transition_phase3_clock_minute_drip_decreases (L := L) (K := K) s t
        hs_phase ht_phase hs_clock ht_clock hmin hcap
      have hs'role : s'.role = .clock := hd.2.2.1
      have ht'role : t'.role = .clock := hd.2.2.2.1
      have hs'min : s'.minute.val = s.minute.val + 1 := hd.2.2.2.2.1
      have ht'min : t'.minute = t.minute := hd.2.2.2.2.2.1
      have key : ∀ x x' : AgentState L K, x'.role = .clock → x'.minute.val ≥ x.minute.val →
          x.role = .clock →
          (if clockBeyondP T x then (1:ℕ) else 0) ≤ (if clockBeyondP T x' then 1 else 0) := by
        intro x x' hx'r hx'm hxr
        unfold clockBeyondP
        simp only [hx'r, hxr, true_and]
        split_ifs <;> omega
      have h1 := key s s' hs'role (by omega) hs_clock
      have h2 := key t t' ht'role (by rw [ht'min]) ht_clock
      omega
    · -- synced-at-cap: both minutes unchanged, both Clocks.
      have hcap' : ¬ s.minute.val < K * (L + 1) := hcap
      have hc := Transition_phase3_clock_cap (L := L) (K := K) s t
        hs_phase ht_phase hs_clock ht_clock hmin hcap'
      have hs'role : s'.role = .clock := hc.1
      have ht'role : t'.role = .clock := hc.2.1
      have hs'min : s'.minute = s.minute := hc.2.2.1
      have ht'min : t'.minute = t.minute := hc.2.2.2
      have e1 : (if clockBeyondP T s then (1:ℕ) else 0) = if clockBeyondP T s' then 1 else 0 := by
        unfold clockBeyondP; simp only [hs'role, hs'min, hs_clock]
      have e2 : (if clockBeyondP T t then (1:ℕ) else 0) = if clockBeyondP T t' then 1 else 0 := by
        unfold clockBeyondP; simp only [ht'role, ht'min, ht_clock]
      omega
  · -- SYNC: both outputs at max minute, both Clocks.
    have hsy := Transition_phase3_clock_minute_sync_decreases (L := L) (K := K) s t
      hs_phase ht_phase hs_clock ht_clock hmin
    have hs'role : s'.role = .clock := hsy.2.2.1
    have ht'role : t'.role = .clock := hsy.2.2.2.1
    have hs'min : s'.minute = max s.minute t.minute := hsy.2.2.2.2.1
    have ht'min : t'.minute = max s.minute t.minute := hsy.2.2.2.2.2.1
    have hmax1 : s.minute.val ≤ (max s.minute t.minute).val := by
      rcases le_total s.minute t.minute with h | h
      · rw [max_eq_right h]; exact h
      · rw [max_eq_left h]
    have hmax2 : t.minute.val ≤ (max s.minute t.minute).val := by
      rcases le_total s.minute t.minute with h | h
      · rw [max_eq_right h]
      · rw [max_eq_left h]; exact h
    have key : ∀ x x' : AgentState L K, x'.role = .clock → x'.minute.val ≥ x.minute.val →
        x.role = .clock →
        (if clockBeyondP T x then (1:ℕ) else 0) ≤ (if clockBeyondP T x' then 1 else 0) := by
      intro x x' hx'r hx'm hxr
      unfold clockBeyondP
      simp only [hx'r, hxr, true_and]
      split_ifs <;> omega
    have h1 := key s s' hs'role (by rw [hs'min]; exact hmax1) hs_clock
    have h2 := key t t' ht'role (by rw [ht'min]; exact hmax2) ht_clock
    omega

/-! ## Part 3 — `rBeyond T` is non-decreasing on the kernel support over the window. -/

/-- Membership in an applicable pair implies membership in `c`. -/
theorem mem_of_applicable_left {c : Config (AgentState L K)} {r₁ r₂ : AgentState L K}
    (happ : Protocol.Applicable c r₁ r₂) : r₁ ∈ c := by
  have hle : ({r₁, r₂} : Multiset (AgentState L K)) ≤ c := happ
  exact Multiset.mem_of_le hle (by simp)

theorem mem_of_applicable_right {c : Config (AgentState L K)} {r₁ r₂ : AgentState L K}
    (happ : Protocol.Applicable c r₁ r₂) : r₂ ∈ c := by
  have hle : ({r₁, r₂} : Multiset (AgentState L K)) ≤ c := happ
  exact Multiset.mem_of_le hle (by simp)

/-- `rBeyond T` is non-decreasing under any chosen-pair update, given the window
`AllClockP3` (so the chosen pair, if applicable, is a Phase-3 clock-clock pair). -/
theorem rBeyond_stepOrSelf_ge (T : ℕ) (c : Config (AgentState L K))
    (hw : AllClockP3 c) (r₁ r₂ : AgentState L K) :
    rBeyond T c ≤ rBeyond T (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂) := by
  classical
  by_cases happ : Protocol.Applicable c r₁ r₂
  · have hmem1 := mem_of_applicable_left happ
    have hmem2 := mem_of_applicable_right happ
    obtain ⟨h1c, h1p⟩ := hw r₁ hmem1
    obtain ⟨h2c, h2p⟩ := hw r₂ hmem2
    have hsub : ({r₁, r₂} : Multiset (AgentState L K)) ≤ c := happ
    -- stepOrSelf = c - {r₁,r₂} + {δ.1, δ.2}
    have hc' : Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂
        = c - {r₁, r₂} + {(NonuniformMajority L K).δ r₁ r₂ |>.1,
            (NonuniformMajority L K).δ r₁ r₂ |>.2} := by
      unfold Protocol.stepOrSelf; rw [if_pos happ]
    have hδ : (NonuniformMajority L K).δ r₁ r₂ = Transition L K r₁ r₂ := rfl
    unfold rBeyond
    rw [hc']
    rw [Multiset.countP_add, Multiset.countP_sub hsub]
    have hpair_le : Multiset.countP (fun a => clockBeyondP T a)
        ({r₁, r₂} : Multiset (AgentState L K))
          ≤ Multiset.countP (fun a => clockBeyondP T a) c := Multiset.countP_le_of_le _ hsub
    have hmono := rBeyond_pair_mono T r₁ r₂ h1p h2p h1c h2c
    rw [hδ]
    omega
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]

/-- `rBeyond T` is preserved-or-raised on the one-step kernel support, over the
window `AllClockP3` (the real-kernel `milestone_monotone`). -/
theorem rBeyond_ge_monotone (T m : ℕ) (c c' : Config (AgentState L K))
    (hw : AllClockP3 c) (h : m ≤ rBeyond T c)
    (hc' : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    m ≤ rBeyond T c' := by
  classical
  by_cases hc : 2 ≤ c.card
  · rw [show (NonuniformMajority L K).stepDistOrSelf c = (NonuniformMajority L K).stepDist c hc by
        unfold Protocol.stepDistOrSelf; rw [dif_pos hc]] at hc'
    obtain ⟨⟨r₁, r₂⟩, hr⟩ := Protocol.stepDist_support (NonuniformMajority L K) c hc c' hc'
    rw [← hr]
    exact le_trans h (rBeyond_stepOrSelf_ge T c hw r₁ r₂)
  · rw [show (NonuniformMajority L K).stepDistOrSelf c = PMF.pure c by
        unfold Protocol.stepDistOrSelf; rw [dif_neg hc]] at hc'
    rw [PMF.mem_support_pure_iff] at hc'
    subst hc'; exact h

/-! ## Part 4 — the drip advance probability (the keystone; the `1/c²` source).

A scheduled same-state pair `(w, w)`, where `w` is a Clock in Phase 3 at minute
exactly `T` (with `T < cap`) and at least two copies sit in `c`, drips one copy up
to minute `T+1`, raising `rBeyond (T+1)` by one.  The scheduler selects this
ordered pair with probability `m·(m−1)/(card·(card−1))`, `m = count w` — the
single same-state pair's mass.  This `m·(m−1)/(card·(card−1))` ratio is EXACTLY
where Doty's `1/c²` (c = clock fraction) is DERIVED by pair-counting; it is not
assumed.  Mirrors `ClockFaithful.clock_drip_seed_advance_prob`. -/

/-- A scheduled same-state drip pair `(w, w)` with `w` a Phase-3 Clock at minute
exactly `T < cap` raises `rBeyond (T+1)` by at least one. -/
theorem rDrip_pair_advances (T : ℕ) (c : Config (AgentState L K)) (w : AgentState L K)
    (hw_phase : w.phase.val = 3) (hw_clock : w.role = .clock)
    (hw_min : w.minute.val = T) (hcap : T < K * (L + 1))
    (hcount : 2 ≤ c.count w) (j : ℕ) (hj : rBeyond (T + 1) c = j) :
    j + 1 ≤ rBeyond (T + 1) (Protocol.stepOrSelf (NonuniformMajority L K) c w w) := by
  classical
  -- applicability of the same-state pair {w, w}.
  have hpaircount : ∀ x : AgentState L K,
      Multiset.count x ({w, w} : Multiset (AgentState L K))
        = (if x = w then 2 else 0) := by
    intro x
    rw [show ({w, w} : Multiset (AgentState L K)) = w ::ₘ w ::ₘ 0 from rfl]
    rw [Multiset.count_cons, Multiset.count_cons, Multiset.count_zero]
    by_cases hx : x = w <;> simp [hx]
  have happ : Protocol.Applicable c w w := by
    refine Multiset.le_iff_count.mpr ?_
    intro x
    rw [hpaircount x]
    have hcx : Multiset.count w c = c.count w := rfl
    by_cases hx : x = w
    · subst hx; rw [if_pos rfl, hcx]; omega
    · rw [if_neg hx]; omega
  have hsub : ({w, w} : Multiset (AgentState L K)) ≤ c := happ
  -- Transition w w is the same-minute drip below cap.
  have hmin_eq : w.minute = w.minute := rfl
  have hcap' : w.minute.val < K * (L + 1) := by rw [hw_min]; exact hcap
  have hd := Transition_phase3_clock_minute_drip_decreases (L := L) (K := K) w w
    hw_phase hw_phase hw_clock hw_clock hmin_eq hcap'
  set w1 := (Transition L K w w).1 with hw1
  set w2 := (Transition L K w w).2 with hw2
  have hw1_clock : w1.role = .clock := hd.2.2.1
  have hw2_clock : w2.role = .clock := hd.2.2.2.1
  have hw1_min : w1.minute.val = w.minute.val + 1 := hd.2.2.2.2.1
  have hw2_min : w2.minute = w.minute := hd.2.2.2.2.2.1
  -- stepOrSelf = c - {w,w} + {w1, w2}
  have hc' : Protocol.stepOrSelf (NonuniformMajority L K) c w w
      = c - {w, w} + {w1, w2} := by
    unfold Protocol.stepOrSelf
    rw [if_pos happ]
    rfl
  unfold rBeyond
  rw [hc', Multiset.countP_add, Multiset.countP_sub hsub]
  -- count over {w, w} at level T+1 is 0 (w sits at minute T < T+1).
  have hwbelow : ¬ clockBeyondP (T + 1) w := by
    unfold clockBeyondP; rw [hw_min]; omega
  have hpairT1 : Multiset.countP (fun a => clockBeyondP (T + 1) a)
      ({w, w} : Multiset (AgentState L K)) = 0 := by
    rw [countP_pair]; simp [hwbelow]
  -- count over {w1, w2}: w1 at minute T+1 (counted), w2 at minute T (not).
  have hw1_beyond : clockBeyondP (T + 1) w1 := by
    unfold clockBeyondP; exact ⟨hw1_clock, by rw [hw1_min, hw_min]⟩
  have hprodT1 : 1 ≤ Multiset.countP (fun a => clockBeyondP (T + 1) a)
      ({w1, w2} : Multiset (AgentState L K)) := by
    rw [countP_pair]; simp [hw1_beyond]
  -- count over c at level T+1 is j.
  have hjc : Multiset.countP (fun a => clockBeyondP (T + 1) a) c = j := hj
  rw [hjc, hpairT1]
  omega

/-- **The real-kernel drip advance probability (the keystone, a LOWER bound).**
For a Phase-3 Clock `w` at minute exactly `T < cap` with `2 ≤ count w` and
`2 ≤ card`, one scheduler step raises `rBeyond (T+1)` to `≥ j+1` with probability
at least `m·(m−1)/(card·(card−1))`, `m = count w`.  This single same-state pair's
mass is precisely Doty's `1/c²` clock-pair fraction, DERIVED by pair-counting (it
equals `interactionProb w w`), not assumed. -/
theorem clock_real_drip_advance_prob (T : ℕ) (c : Config (AgentState L K))
    (w : AgentState L K) (hw_phase : w.phase.val = 3) (hw_clock : w.role = .clock)
    (hw_min : w.minute.val = T) (hcap : T < K * (L + 1))
    (hc : 2 ≤ c.card) (j : ℕ) (hj : rBeyond (T + 1) c = j)
    (hcount : 2 ≤ c.count w) :
    ((NonuniformMajority L K).stepDistOrSelf c).toMeasure {c' | j + 1 ≤ rBeyond (T + 1) c'} ≥
      ENNReal.ofReal ((c.count w * (c.count w - 1) : ℝ) /
        (c.card * (c.card - 1) : ℝ)) := by
  classical
  set m := c.count w with hm
  set n := c.card with hn
  have hstepDist : (NonuniformMajority L K).stepDistOrSelf c
      = (NonuniformMajority L K).stepDist c hc := by
    unfold Protocol.stepDistOrSelf; rw [dif_pos hc]
  have hmeas : MeasurableSet {c' : Config (AgentState L K) | j + 1 ≤ rBeyond (T + 1) c'} :=
    DiscreteMeasurableSpace.forall_measurableSet _
  -- the singleton pair (w, w) is contained in the advance preimage.
  have hsub : ({(w, w)} : Set (AgentState L K × AgentState L K)) ⊆
      (Protocol.scheduledStep (NonuniformMajority L K) c) ⁻¹'
        {c' | j + 1 ≤ rBeyond (T + 1) c'} := by
    intro p hp
    rw [Set.mem_singleton_iff] at hp
    subst hp
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Protocol.scheduledStep]
    exact rDrip_pair_advances T c w hw_phase hw_clock hw_min hcap hcount j hj
  have hbase : ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
        {c' | j + 1 ≤ rBeyond (T + 1) c'}
      = (c.interactionPMF hc).toMeasure
          ((Protocol.scheduledStep (NonuniformMajority L K) c) ⁻¹'
            {c' | j + 1 ≤ rBeyond (T + 1) c'}) := by
    rw [hstepDist]
    unfold Protocol.stepDist
    rw [PMF.toMeasure_map_apply _ _ _ (Measurable.of_discrete) hmeas]
  rw [hbase]
  have hmono : (c.interactionPMF hc).toMeasure ({(w, w)} : Set _)
      ≤ (c.interactionPMF hc).toMeasure
          ((Protocol.scheduledStep (NonuniformMajority L K) c) ⁻¹'
            {c' | j + 1 ≤ rBeyond (T + 1) c'}) :=
    measure_mono hsub
  refine le_trans ?_ hmono
  have hsingle : (c.interactionPMF hc).toMeasure ({(w, w)} : Set _)
      = c.interactionProb w w := by
    rw [PMF.toMeasure_apply_singleton _ _ (DiscreteMeasurableSpace.forall_measurableSet _)]
    rfl
  rw [hsingle]
  have hIP : c.interactionProb w w
      = (↑(m * (m - 1)) : ℝ≥0∞) / (↑(n * (n - 1)) : ℝ≥0∞) := by
    unfold Config.interactionProb Config.interactionCount Config.totalPairs
    rw [if_pos rfl]
  rw [hIP]
  have hdenN_pos : 0 < n * (n - 1) := Nat.mul_pos (by omega) (by omega)
  have hdenN_posR : (0 : ℝ) < ((n * (n - 1) : ℕ) : ℝ) := by exact_mod_cast hdenN_pos
  have hratio : (↑(m * (m - 1)) : ℝ≥0∞) / (↑(n * (n - 1)) : ℝ≥0∞)
      = ENNReal.ofReal (((m * (m - 1) : ℕ) : ℝ) / ((n * (n - 1) : ℕ) : ℝ)) := by
    rw [ENNReal.ofReal_div_of_pos hdenN_posR, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
  rw [hratio]
  apply ENNReal.ofReal_le_ofReal
  have hmle : m ≤ n := by rw [hm, hn]; exact Multiset.count_le_card w c
  have hm1 : 1 ≤ m := by omega
  have hn1 : 1 ≤ n := by omega
  have hnumL : ((m * (m - 1) : ℕ) : ℝ) = (m : ℝ) * ((m : ℝ) - 1) := by
    rw [Nat.cast_mul, Nat.cast_sub hm1, Nat.cast_one]
  have hdenL : ((n * (n - 1) : ℕ) : ℝ) = (n : ℝ) * ((n : ℝ) - 1) := by
    rw [Nat.cast_mul, Nat.cast_sub hn1, Nat.cast_one]
  rw [hnumL, hdenL]

/-! ## Part 5 — the genuinely absorbing window: `AllClock` (every agent a Clock).

The faithful absorbing window is "every agent is a Clock".  A clock-clock pair
keeps BOTH outputs Clocks in EVERY phase, and never lowers a `minute`: in Phases
4–8 a clock-clock pair reduces to `stdCounterSubroutine` (the Main/Reserve update
branches do not fire), in Phase 9 it only edits `opinions`/`output`, in Phase 3 it
drips/syncs/counts (minutes only rise), and in Phase 10 it edits only the backup
fields.  Crucially, `phaseInit` resets `minute` ONLY when entering Phase 3
(`p = 3`); since clocks in this window sit at phase `≥ 3` and phases only advance,
that reset never fires.  Hence `rBeyond T` (count of Clocks at minute `≥ T`) is
non-decreasing on the kernel support over `AllClock`, and `AllClock` is absorbing. -/

/-- `phaseInit` at any phase `p ≠ 3` preserves a Clock's `minute`. -/
theorem phaseInit_minute_eq_of_ne_three (p : Fin 11) (a : AgentState L K)
    (hp : p.val ≠ 3) : (phaseInit L K p a).minute = a.minute := by
  unfold phaseInit
  by_cases h1 : p.val = 1
  · rw [dif_pos h1]
    split_ifs <;> simp [enterPhase10]
  · rw [dif_neg h1]
    by_cases h2 : p.val = 2
    · rw [dif_pos h2]
      simp only []
      split_ifs <;> simp [enterPhase10]
    · rw [dif_neg h2, dif_neg hp]
      by_cases h4 : p.val = 4
      · rw [dif_pos h4]
      · rw [dif_neg h4]
        by_cases h5 : p.val = 5
        · rw [dif_pos h5]; split_ifs <;> simp
        · rw [dif_neg h5]
          by_cases h6 : p.val = 6
          · rw [dif_pos h6]; split_ifs <;> simp
          · rw [dif_neg h6]
            by_cases h7 : p.val = 7
            · rw [dif_pos h7]; split_ifs <;> simp
            · rw [dif_neg h7]
              by_cases h8 : p.val = 8
              · rw [dif_pos h8]
              · rw [dif_neg h8]
                by_cases h9 : p.val = 9
                · rw [dif_pos h9]
                  simp only []
                  split_ifs
                  all_goals first | rfl | simp [enterPhase10]
                · rw [dif_neg h9]
                  by_cases h10 : p.val = 10
                  · rw [dif_pos h10]; simp [enterPhase10]
                  · rw [dif_neg h10]

/-- `phaseInit` preserves a Clock's role at any phase. -/
theorem phaseInit_clock (p : Fin 11) (a : AgentState L K) (ha : a.role = .clock) :
    (phaseInit L K p a).role = .clock := by
  exact phaseInit_clock_role_eq (L := L) (K := K) p a ha

/-- `runInitsBetween` with `3 ≤ oldP` preserves a Clock's role and `minute`: the
phases initialized lie in `(oldP, newP]`, all `≥ 4 ≠ 3`, so the `minute`-resetting
Phase-3 init never runs. -/
theorem runInitsBetween_clock_minute (oldP newP : ℕ) (hold : 3 ≤ oldP)
    (a : AgentState L K) (ha : a.role = .clock) :
    (runInitsBetween L K oldP newP a).role = .clock ∧
      (runInitsBetween L K oldP newP a).minute = a.minute := by
  unfold runInitsBetween
  set lst := (List.range 11).filter (fun k => oldP < k ∧ k ≤ newP) with hlst
  have hmem : ∀ k ∈ lst, 3 < k := by
    intro k hk
    rw [hlst, List.mem_filter] at hk
    have hk2 : oldP < k ∧ k ≤ newP := by
      have := hk.2; simpa using this
    omega
  clear_value lst
  -- prove the fold preserves "role = clock ∧ minute = a₀.minute" by list induction,
  -- carrying the membership constraint so each step's phase ≠ 3.
  suffices H : ∀ (l : List ℕ), (∀ k ∈ l, 3 < k) → ∀ b : AgentState L K, b.role = .clock →
      (l.foldl (fun acc k => if h : k < 11 then phaseInit L K ⟨k, h⟩ acc else acc) b).role
          = .clock ∧
      (l.foldl (fun acc k => if h : k < 11 then phaseInit L K ⟨k, h⟩ acc else acc) b).minute
          = b.minute by
    exact H lst hmem a ha
  intro l
  induction l with
  | nil => intro _ b hb; exact ⟨hb, rfl⟩
  | cons k ks ih =>
    intro hmemk b hb
    simp only [List.foldl_cons]
    by_cases hk : k < 11
    · rw [dif_pos hk]
      have hk3 : (⟨k, hk⟩ : Fin 11).val ≠ 3 := by
        show k ≠ 3
        have := hmemk k (List.mem_cons_self); omega
      have hrole : (phaseInit L K ⟨k, hk⟩ b).role = .clock := phaseInit_clock _ b hb
      have hmin : (phaseInit L K ⟨k, hk⟩ b).minute = b.minute :=
        phaseInit_minute_eq_of_ne_three ⟨k, hk⟩ b hk3
      have hih := ih (fun j hj => hmemk j (List.mem_cons_of_mem k hj))
        (phaseInit L K ⟨k, hk⟩ b) hrole
      exact ⟨hih.1, hih.2.trans hmin⟩
    · rw [dif_neg hk]
      exact ih (fun j hj => hmemk j (List.mem_cons_of_mem k hj)) b hb

/-- `stdCounterSubroutine` on a Clock at phase `≥ 3` keeps it a Clock and keeps
its `minute`: the counter decrement leaves both untouched, and the `3 → 4` (or
higher) phase advance's Init never resets `minute` (only `p = 3` Init does). -/
theorem stdCounterSubroutine_clock_minute (a : AgentState L K)
    (ha : a.role = .clock) (hp : 3 ≤ a.phase.val) :
    (stdCounterSubroutine L K a).role = .clock ∧
      (stdCounterSubroutine L K a).minute = a.minute := by
  refine ⟨stdCounterSubroutine_clock_role a ha, ?_⟩
  unfold stdCounterSubroutine
  by_cases hc : a.counter.val = 0
  · rw [dif_pos hc]
    unfold advancePhaseWithInit advancePhase
    by_cases h10 : a.phase.val < 10
    · rw [dif_pos h10]
      set b : AgentState L K :=
        { a with phase := ⟨a.phase.val.succ, by have := a.phase.2; omega⟩ } with hb
      have hbp3 : b.phase.val ≠ 3 := by rw [hb]; simp; omega
      have hbmin : b.minute = a.minute := by rw [hb]
      rw [phaseInit_minute_eq_of_ne_three b.phase b hbp3, hbmin]
    · rw [dif_neg h10]
      -- phase = 10; phaseInit at phase 10 keeps minute (enterPhase10).
      rw [phaseInit_minute_eq_of_ne_three a.phase a (by omega)]
  · rw [dif_neg hc]

/-- `runInitsBetween` is phase-non-decreasing (own copy from public
`phaseInit_phase_nondec`). -/
theorem runInitsBetween_phase_nondec_pub (oldP newP : ℕ) (a : AgentState L K) :
    a.phase.val ≤ (runInitsBetween L K oldP newP a).phase.val := by
  unfold runInitsBetween
  set lst := (List.range 11).filter (fun k => oldP < k ∧ k ≤ newP) with hlst
  clear_value lst
  suffices H : ∀ (l : List ℕ) (b : AgentState L K),
      b.phase.val ≤
        (l.foldl (fun acc k => if h : k < 11 then phaseInit L K ⟨k, h⟩ acc else acc) b).phase.val by
    exact H lst a
  intro l
  induction l with
  | nil => intro b; exact le_refl _
  | cons k ks ih =>
    intro b
    simp only [List.foldl_cons]
    by_cases hk : k < 11
    · rw [dif_pos hk]
      exact le_trans (phaseInit_phase_nondec L K ⟨k, hk⟩ b) (ih _)
    · rw [dif_neg hk]; exact ih b

/-! ### Per-phase clock-clock helpers (Phases 4–10): role + minute preserved.

For a clock-clock pair, Phases 4–10 never read `minute` and reduce to
`stdCounterSubroutine`/identity/output-edits, all role/`minute`-safe. -/

theorem Phase4_clock_pair (s t : AgentState L K)
    (hs : s.role = .clock) (ht : t.role = .clock) (hps : 3 ≤ s.phase.val) (hpt : 3 ≤ t.phase.val) :
    (Phase4Transition L K s t).1.role = .clock ∧ (Phase4Transition L K s t).2.role = .clock ∧
      s.minute = (Phase4Transition L K s t).1.minute ∧
      t.minute = (Phase4Transition L K s t).2.minute := by
  have hrole : ∀ a : AgentState L K, a.role = .clock → (advancePhase L K a).role = .clock := by
    intro a ha; unfold advancePhase; split_ifs <;> simp [ha]
  have hmins : ∀ a : AgentState L K, (advancePhase L K a).minute = a.minute := by
    intro a; unfold advancePhase; split_ifs <;> rfl
  unfold Phase4Transition
  dsimp only
  split_ifs
  · exact ⟨hrole s hs, hrole t ht, (hmins s).symm, (hmins t).symm⟩
  · exact ⟨hs, ht, rfl, rfl⟩

/-- Phases 5–8 share the shape `(if s1.role = clock then stdCounter s1 else s1, …)`
with `s1 = s` on a Clock; the produced pair is `(stdCounter s, stdCounter t)`. -/
theorem stdCounterPair_clock (s t : AgentState L K)
    (hs : s.role = .clock) (ht : t.role = .clock) (hps : 3 ≤ s.phase.val) (hpt : 3 ≤ t.phase.val) :
    (stdCounterSubroutine L K s).role = .clock ∧ (stdCounterSubroutine L K t).role = .clock ∧
      s.minute = (stdCounterSubroutine L K s).minute ∧
      t.minute = (stdCounterSubroutine L K t).minute := by
  have h1 := stdCounterSubroutine_clock_minute s hs hps
  have h2 := stdCounterSubroutine_clock_minute t ht hpt
  exact ⟨h1.1, h2.1, h1.2.symm, h2.2.symm⟩

theorem Phase5_clock_pair (s t : AgentState L K)
    (hs : s.role = .clock) (ht : t.role = .clock) (hps : 3 ≤ s.phase.val) (hpt : 3 ≤ t.phase.val) :
    (Phase5Transition L K s t).1.role = .clock ∧ (Phase5Transition L K s t).2.role = .clock ∧
      s.minute = (Phase5Transition L K s t).1.minute ∧
      t.minute = (Phase5Transition L K s t).2.minute := by
  unfold Phase5Transition
  simp only [hs, ht, reduceCtorEq, false_and, and_false, if_false, if_true]
  exact stdCounterPair_clock s t hs ht hps hpt

theorem Phase6_clock_pair (s t : AgentState L K)
    (hs : s.role = .clock) (ht : t.role = .clock) (hps : 3 ≤ s.phase.val) (hpt : 3 ≤ t.phase.val) :
    (Phase6Transition L K s t).1.role = .clock ∧ (Phase6Transition L K s t).2.role = .clock ∧
      s.minute = (Phase6Transition L K s t).1.minute ∧
      t.minute = (Phase6Transition L K s t).2.minute := by
  unfold Phase6Transition
  simp only [hs, ht, reduceCtorEq, false_and, and_false, if_false, if_true]
  exact stdCounterPair_clock s t hs ht hps hpt

theorem Phase7_clock_pair (s t : AgentState L K)
    (hs : s.role = .clock) (ht : t.role = .clock) (hps : 3 ≤ s.phase.val) (hpt : 3 ≤ t.phase.val) :
    (Phase7Transition L K s t).1.role = .clock ∧ (Phase7Transition L K s t).2.role = .clock ∧
      s.minute = (Phase7Transition L K s t).1.minute ∧
      t.minute = (Phase7Transition L K s t).2.minute := by
  unfold Phase7Transition
  simp only [hs, ht, reduceCtorEq, false_and, and_false, if_false, if_true]
  exact stdCounterPair_clock s t hs ht hps hpt

theorem Phase8_clock_pair (s t : AgentState L K)
    (hs : s.role = .clock) (ht : t.role = .clock) (hps : 3 ≤ s.phase.val) (hpt : 3 ≤ t.phase.val) :
    (Phase8Transition L K s t).1.role = .clock ∧ (Phase8Transition L K s t).2.role = .clock ∧
      s.minute = (Phase8Transition L K s t).1.minute ∧
      t.minute = (Phase8Transition L K s t).2.minute := by
  unfold Phase8Transition
  simp only [hs, ht, reduceCtorEq, false_and, and_false, if_false, if_true]
  exact stdCounterPair_clock s t hs ht hps hpt

/-- `advancePhaseWithInit` on a Clock at phase `≥ 3` preserves role and `minute`. -/
theorem advancePhaseWithInit_clock_minute (a : AgentState L K) (ha : a.role = .clock)
    (hp : 3 ≤ a.phase.val) :
    (advancePhaseWithInit L K a).role = .clock ∧
      (advancePhaseWithInit L K a).minute = a.minute := by
  refine ⟨advancePhaseWithInit_clock_role_eq (L := L) (K := K) a ha, ?_⟩
  unfold advancePhaseWithInit advancePhase
  by_cases h10 : a.phase.val < 10
  · rw [dif_pos h10]
    set b : AgentState L K := { a with phase := ⟨a.phase.val.succ, by have := a.phase.2; omega⟩ }
      with hb
    have hbp3 : b.phase.val ≠ 3 := by
      show a.phase.val.succ ≠ 3; omega
    have hbmin : b.minute = a.minute := by rw [hb]
    rw [phaseInit_minute_eq_of_ne_three b.phase b hbp3, hbmin]
  · rw [dif_neg h10]
    rw [phaseInit_minute_eq_of_ne_three a.phase a (by omega)]

theorem Phase9_clock_pair (s t : AgentState L K)
    (hs : s.role = .clock) (ht : t.role = .clock) (hps : 3 ≤ s.phase.val) (hpt : 3 ≤ t.phase.val) :
    (Phase9Transition L K s t).1.role = .clock ∧ (Phase9Transition L K s t).2.role = .clock ∧
      s.minute = (Phase9Transition L K s t).1.minute ∧
      t.minute = (Phase9Transition L K s t).2.minute := by
  -- the advancing branch acts on the opinion-updated agents, still Clocks at phase ≥ 3.
  have hadvs := advancePhaseWithInit_clock_minute ({ s with opinions := opinionsUnion s.opinions t.opinions }) hs hps
  have hadvt := advancePhaseWithInit_clock_minute ({ t with opinions := opinionsUnion s.opinions t.opinions }) ht hpt
  unfold Phase9Transition Phase2Transition
  dsimp only
  split_ifs <;>
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
    first
    | exact hadvs.1 | exact hadvt.1 | exact hadvs.2.symm | exact hadvt.2.symm
    | (simp only []; exact hs) | (simp only []; exact ht)
    | simp [hs] | simp [ht] | rfl | simp

theorem Phase10_clock_pair (s t : AgentState L K)
    (hs : s.role = .clock) (ht : t.role = .clock) :
    (Phase10Transition L K s t).1.role = .clock ∧ (Phase10Transition L K s t).2.role = .clock ∧
      s.minute = (Phase10Transition L K s t).1.minute ∧
      t.minute = (Phase10Transition L K s t).2.minute := by
  unfold Phase10Transition
  simp only []
  split_ifs <;> exact ⟨by simp [hs], by simp [ht], by simp, by simp⟩

/-- Phase 3 clock-clock: both outputs Clocks, minutes non-decreasing.  Reuses the
proven full-`Transition` descent lemmas: at phase 3 the epidemic stage is identity
and `finishPhase10Entry` is identity on the Phase-3 outputs (phase ∈ {3,4}), so
the `Transition` facts transfer to `Phase3Transition`. -/
theorem Phase3_clock_pair (s t : AgentState L K)
    (hs_clock : s.role = .clock) (ht_clock : t.role = .clock)
    (hs_phase : s.phase.val = 3) (ht_phase : t.phase.val = 3) :
    (Phase3Transition L K s t).1.role = .clock ∧
      (Phase3Transition L K s t).2.role = .clock ∧
      s.minute.val ≤ (Phase3Transition L K s t).1.minute.val ∧
      t.minute.val ≤ (Phase3Transition L K s t).2.minute.val := by
  have hsc := stdCounterSubroutine_clock_minute s hs_clock (by omega)
  have htc := stdCounterSubroutine_clock_minute t ht_clock (by omega)
  by_cases hmin : s.minute = t.minute
  · by_cases hcap : s.minute.val < K * (L + 1)
    · -- drip: (s ↦ minute+1, t ↦ t), both Clocks; Rules 2/3/4 inert.
      have hcap_t : t.minute.val < K * (L + 1) := by simpa [hmin] using hcap
      have hP3 : Phase3Transition L K s t =
          ({ s with minute := ⟨s.minute.val + 1, by omega⟩ }, t) := by
        unfold Phase3Transition
        simp only [hs_clock, ht_clock, and_self, if_true, hmin, ne_eq, not_true_eq_false,
          if_false, hcap, hcap_t, ↓reduceDIte, reduceCtorEq, false_and, and_false, true_and,
          if_false]
      rw [hP3]
      exact ⟨by simp [hs_clock], by simp [ht_clock], by simp, by simp [hmin]⟩
    · -- synced-at-cap → (stdCounter s, stdCounter t).
      have hcap_t : ¬ t.minute.val < K * (L + 1) := by simpa [hmin] using hcap
      have hP3 : Phase3Transition L K s t =
          (stdCounterSubroutine L K s, stdCounterSubroutine L K t) := by
        unfold Phase3Transition
        simp only [hs_clock, ht_clock, and_self, if_true, hmin, ne_eq, not_true_eq_false,
          if_false, hcap, hcap_t, dif_neg, not_false_eq_true]
        simp only [hsc.1, htc.1, reduceCtorEq, false_and, if_false, and_false]
      rw [hP3]
      exact ⟨hsc.1, htc.1, by rw [hsc.2], by rw [htc.2]⟩
  · -- sync → (max, max), both Clocks; Rules 2/3/4 inert.
    have hmax_s : s.minute.val ≤ (max s.minute t.minute).val := by
      rcases le_total s.minute t.minute with h | h
      · rw [max_eq_right h]; exact h
      · rw [max_eq_left h]
    have hmax_t : t.minute.val ≤ (max s.minute t.minute).val := by
      rcases le_total s.minute t.minute with h | h
      · rw [max_eq_right h]
      · rw [max_eq_left h]; exact h
    have hP3 : Phase3Transition L K s t =
        ({ s with minute := max s.minute t.minute }, { t with minute := max s.minute t.minute }) := by
      unfold Phase3Transition
      simp only [hs_clock, ht_clock, and_self, if_true, if_neg hmin, ne_eq, hmin,
        not_false_eq_true, reduceCtorEq, false_and, and_false, if_false]
    rw [hP3]
    exact ⟨by simp [hs_clock], by simp [ht_clock], by simpa using hmax_s, by simpa using hmax_t⟩
/-- `phaseEpidemicUpdate` on a clock-clock pair both at phase `≥ 3` keeps both
outputs Clocks, preserves both `minute`s, and keeps both phases `≥ 3`.  Covers
both branches: the normal drag (`runInitsBetween`, Phase-3 init never runs from
phase `≥ 3`) and the Phase-10 entry branch (`enterPhase10`, role/minute-safe). -/
theorem phaseEpidemicUpdate_clock (s t : AgentState L K)
    (hs_clock : s.role = .clock) (ht_clock : t.role = .clock)
    (hs_phase : 3 ≤ s.phase.val) (ht_phase : 3 ≤ t.phase.val) :
    (phaseEpidemicUpdate L K s t).1.role = .clock ∧
      (phaseEpidemicUpdate L K s t).2.role = .clock ∧
      (phaseEpidemicUpdate L K s t).1.minute = s.minute ∧
      (phaseEpidemicUpdate L K s t).2.minute = t.minute ∧
      3 ≤ (phaseEpidemicUpdate L K s t).1.phase.val ∧
      3 ≤ (phaseEpidemicUpdate L K s t).2.phase.val := by
  set p := max s.phase t.phase with hp
  have hp_ge3 : 3 ≤ p.val := by
    rw [hp]; rcases le_total s.phase t.phase with h | h
    · rw [max_eq_right h]; exact ht_phase
    · rw [max_eq_left h]; exact hs_phase
  have hsdrag := runInitsBetween_clock_minute (L := L) (K := K) s.phase.val p.val hs_phase
    ({ s with phase := p }) hs_clock
  have htdrag := runInitsBetween_clock_minute (L := L) (K := K) t.phase.val p.val ht_phase
    ({ t with phase := p }) ht_clock
  have hsph : 3 ≤ (runInitsBetween L K s.phase.val p.val { s with phase := p }).phase.val := by
    calc 3 ≤ p.val := hp_ge3
      _ = ({ s with phase := p } : AgentState L K).phase.val := rfl
      _ ≤ _ := runInitsBetween_phase_nondec_pub s.phase.val p.val { s with phase := p }
  have htph : 3 ≤ (runInitsBetween L K t.phase.val p.val { t with phase := p }).phase.val := by
    calc 3 ≤ p.val := hp_ge3
      _ = ({ t with phase := p } : AgentState L K).phase.val := rfl
      _ ≤ _ := runInitsBetween_phase_nondec_pub t.phase.val p.val { t with phase := p }
  unfold phaseEpidemicUpdate
  simp only [← hp]
  by_cases hbr : (s.phase.val < 10 ∨ t.phase.val < 10) ∧
      ((runInitsBetween L K s.phase.val p.val { s with phase := p }).phase.val = 10 ∨
       (runInitsBetween L K t.phase.val p.val { t with phase := p }).phase.val = 10)
  · rw [if_pos hbr]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [phase10EpidemicEntry] <;>
      split_ifs <;>
      simp_all [enterPhase10, hsdrag.1, htdrag.1, hsdrag.2, htdrag.2]
  · rw [if_neg hbr]
    exact ⟨hsdrag.1, htdrag.1, hsdrag.2, htdrag.2, hsph, htph⟩

/-! ## The master clock-pair behaviour: both outputs stay Clocks, minutes never drop. -/

/-- **Master per-pair lemma.**  For a clock-clock pair both at phase `≥ 3`,
`Transition` keeps BOTH outputs Clocks and never lowers either `minute`.  This is
the genuine combinatorial fact (across ALL phases 3–10) making the window
`AllClock` absorbing and `rBeyond` monotone.  Proof: the epidemic drag keeps both
Clocks at the common max phase `≥ 3` (Phase-3 init never runs, so `minute` is
kept), the dispatched per-phase rule on a clock-clock pair reduces to
`stdCounterSubroutine`/identity (Phases 4–8,10) / opinions edit (Phase 9) /
drip-sync-count (Phase 3), all role/`minute`-safe, and `finishPhase10Entry`
(= `canonicalPhase10Entry`) touches only the backup fields via `enterPhase10`. -/
theorem Transition_clock_pair (s t : AgentState L K)
    (hs_clock : s.role = .clock) (ht_clock : t.role = .clock)
    (hs_phase : 3 ≤ s.phase.val) (ht_phase : 3 ≤ t.phase.val) :
    (Transition L K s t).1.role = .clock ∧
      (Transition L K s t).2.role = .clock ∧
      s.minute.val ≤ (Transition L K s t).1.minute.val ∧
      t.minute.val ≤ (Transition L K s t).2.minute.val := by
  classical
  -- Stage A: the epidemic stage keeps both Clocks, preserves minutes, phases ≥ 3.
  have hepi := phaseEpidemicUpdate_clock s t hs_clock ht_clock hs_phase ht_phase
  set s' := (phaseEpidemicUpdate L K s t).1 with hs'
  set t' := (phaseEpidemicUpdate L K s t).2 with ht'
  have hs'clock : s'.role = .clock := hepi.1
  have ht'clock : t'.role = .clock := hepi.2.1
  have hs'min : s'.minute = s.minute := hepi.2.2.1
  have ht'min : t'.minute = t.minute := hepi.2.2.2.1
  have hs'phase : 3 ≤ s'.phase.val := hepi.2.2.2.2.1
  have ht'phase : 3 ≤ t'.phase.val := hepi.2.2.2.2.2
  -- Stage B: the dispatched per-phase rule on a clock-clock pair keeps role + minute.
  set out := match s'.phase with
    | ⟨0, _⟩ => Phase0Transition L K s' t'
    | ⟨1, _⟩ => Phase1Transition L K s' t'
    | ⟨2, _⟩ => Phase2Transition L K s' t'
    | ⟨3, _⟩ => Phase3Transition L K s' t'
    | ⟨4, _⟩ => Phase4Transition L K s' t'
    | ⟨5, _⟩ => Phase5Transition L K s' t'
    | ⟨6, _⟩ => Phase6Transition L K s' t'
    | ⟨7, _⟩ => Phase7Transition L K s' t'
    | ⟨8, _⟩ => Phase8Transition L K s' t'
    | ⟨9, _⟩ => Phase9Transition L K s' t'
    | ⟨10, _⟩ => Phase10Transition L K s' t'
    | _ => (s', t') with hout
  -- when dispatch fires Phase 3 (s'.phase = 3), both s,t were at phase 3 with empty
  -- drag, so s' = s, t' = t are both at phase 3.
  -- when dispatch fires Phase 3 (s'.phase = 3), both inputs were at phase 3 and the
  -- epidemic stage is the identity, so t'.phase = 3 too.
  have hphase3_both : s'.phase.val = 3 → t'.phase.val = 3 := by
    intro h3
    -- the epidemic drags both to max phase ≥ each input; s'.phase ≥ max s.phase t.phase.
    have hge : (max s.phase t.phase).val ≤ s'.phase.val := by
      rw [hs']
      unfold phaseEpidemicUpdate
      by_cases hbr : (s.phase.val < 10 ∨ t.phase.val < 10) ∧
          ((runInitsBetween L K s.phase.val (max s.phase t.phase).val
              { s with phase := max s.phase t.phase }).phase.val = 10 ∨
           (runInitsBetween L K t.phase.val (max s.phase t.phase).val
              { t with phase := max s.phase t.phase }).phase.val = 10)
      · -- phase-10 entry branch: each component is either enterPhase10 (phase = 10)
        -- or the dragged result (phase ≥ max via nondec); s'.phase ≥ max either way.
        simp only [if_pos hbr]
        have hmaxlt : (max s.phase t.phase).val ≤ 10 := by
          have := (max s.phase t.phase).isLt; omega
        have hnondec := runInitsBetween_phase_nondec_pub s.phase.val (max s.phase t.phase).val
          ({ s with phase := max s.phase t.phase } : AgentState L K)
        have hbase : ({ s with phase := max s.phase t.phase } : AgentState L K).phase.val
            = (max s.phase t.phase).val := rfl
        unfold phase10EpidemicEntry
        split_ifs with h
        · show (max s.phase t.phase).val ≤ (enterPhase10 L K _).phase.val
          rw [show (enterPhase10 L K (runInitsBetween L K s.phase.val (max s.phase t.phase).val
            { s with phase := max s.phase t.phase })).phase.val = 10 from by
            simp [enterPhase10, phase10]]
          omega
        · show (max s.phase t.phase).val ≤ _
          rw [← hbase]; exact hnondec
      · simp only [if_neg hbr]
        calc (max s.phase t.phase).val
            = ({ s with phase := max s.phase t.phase } : AgentState L K).phase.val := rfl
          _ ≤ _ := runInitsBetween_phase_nondec_pub s.phase.val (max s.phase t.phase).val _
    have hmax3 : (max s.phase t.phase).val ≤ 3 := by omega
    have hsle : s.phase.val ≤ (max s.phase t.phase).val := by
      exact_mod_cast (le_max_left s.phase t.phase : s.phase ≤ max s.phase t.phase)
    have htle : t.phase.val ≤ (max s.phase t.phase).val := by
      exact_mod_cast (le_max_right s.phase t.phase : t.phase ≤ max s.phase t.phase)
    have hsp3 : s.phase.val = 3 := by omega
    have htp3 : t.phase.val = 3 := by omega
    have hepi_id : phaseEpidemicUpdate L K s t = (s, t) :=
      phaseEpidemicUpdate_eq_self_p3 s t hsp3 htp3
    rw [ht']; rw [hepi_id]; exact htp3
  have hdispatch : out.1.role = .clock ∧ out.2.role = .clock ∧
      s'.minute.val ≤ out.1.minute.val ∧ t'.minute.val ≤ out.2.minute.val := by
    rw [hout]
    rcases hpv : s'.phase with ⟨pv, hpvlt⟩
    have hpv3 : 3 ≤ pv := by have := hs'phase; rw [hpv] at this; exact this
    -- reduce the match by the concrete phase value.
    interval_cases pv
    · -- 3
      have ht'3 := hphase3_both (by rw [hpv])
      have h := Phase3_clock_pair s' t' hs'clock ht'clock (by rw [hpv]) ht'3
      simpa [hpv] using h
    · -- 4
      have h := Phase4_clock_pair s' t' hs'clock ht'clock hs'phase ht'phase
      refine ⟨by simpa [hpv] using h.1, by simpa [hpv] using h.2.1, ?_, ?_⟩
      · simp only [hpv]; rw [← h.2.2.1]
      · simp only [hpv]; rw [← h.2.2.2]
    · -- 5
      have h := Phase5_clock_pair s' t' hs'clock ht'clock hs'phase ht'phase
      refine ⟨by simpa [hpv] using h.1, by simpa [hpv] using h.2.1, ?_, ?_⟩
      · simp only [hpv]; rw [← h.2.2.1]
      · simp only [hpv]; rw [← h.2.2.2]
    · -- 6
      have h := Phase6_clock_pair s' t' hs'clock ht'clock hs'phase ht'phase
      refine ⟨by simpa [hpv] using h.1, by simpa [hpv] using h.2.1, ?_, ?_⟩
      · simp only [hpv]; rw [← h.2.2.1]
      · simp only [hpv]; rw [← h.2.2.2]
    · -- 7
      have h := Phase7_clock_pair s' t' hs'clock ht'clock hs'phase ht'phase
      refine ⟨by simpa [hpv] using h.1, by simpa [hpv] using h.2.1, ?_, ?_⟩
      · simp only [hpv]; rw [← h.2.2.1]
      · simp only [hpv]; rw [← h.2.2.2]
    · -- 8
      have h := Phase8_clock_pair s' t' hs'clock ht'clock hs'phase ht'phase
      refine ⟨by simpa [hpv] using h.1, by simpa [hpv] using h.2.1, ?_, ?_⟩
      · simp only [hpv]; rw [← h.2.2.1]
      · simp only [hpv]; rw [← h.2.2.2]
    · -- 9
      have h := Phase9_clock_pair s' t' hs'clock ht'clock hs'phase ht'phase
      refine ⟨by simpa [hpv] using h.1, by simpa [hpv] using h.2.1, ?_, ?_⟩
      · simp only [hpv]; rw [← h.2.2.1]
      · simp only [hpv]; rw [← h.2.2.2]
    · -- 10
      have h := Phase10_clock_pair s' t' hs'clock ht'clock
      refine ⟨by simpa [hpv] using h.1, by simpa [hpv] using h.2.1, ?_, ?_⟩
      · simp only [hpv]; rw [← h.2.2.1]
      · simp only [hpv]; rw [← h.2.2.2]
  -- finishPhase10Entry (= canonicalPhase10Entry) only ever applies enterPhase10,
  -- which preserves role and minute.
  -- the full Transition is (finishPhase10Entry s' out.1, finishPhase10Entry t' out.2).
  have hTeq : Transition L K s t =
      (finishPhase10Entry L K s' out.1, finishPhase10Entry L K t' out.2) := by
    conv_lhs => unfold Transition
    rfl
  rw [hTeq]
  have hfin_role : ∀ before after : AgentState L K, after.role = .clock →
      (finishPhase10Entry L K before after).role = .clock := by
    intro before after h
    unfold finishPhase10Entry canonicalPhase10Entry
    split_ifs <;> simp [enterPhase10, h]
  have hfin_min : ∀ before after : AgentState L K,
      (finishPhase10Entry L K before after).minute = after.minute := by
    intro before after
    unfold finishPhase10Entry canonicalPhase10Entry
    split_ifs <;> simp [enterPhase10]
  refine ⟨hfin_role _ _ hdispatch.1, hfin_role _ _ hdispatch.2.1, ?_, ?_⟩
  · rw [hfin_min, ← hs'min]; exact hdispatch.2.2.1
  · rw [hfin_min, ← ht'min]; exact hdispatch.2.2.2

/-! ## Part 6 — the genuinely absorbing window and the global `rBeyond` monotonicity.

The window `AllClockGE3 c` = "every agent is a Clock at phase ≥ 3" is one-step
support closed (`AllClockGE3_absorbing`): a clock-clock pair keeps both outputs
Clocks at phase ≥ 3 (`Transition_clock_pair` + phase-non-decrease).  On this window
`rBeyond T` (count of Clocks at minute ≥ T) is non-decreasing on the kernel support
(`rBeyondGE3_ge_monotone`). -/

/-- The genuinely absorbing window: every agent is a Clock at phase `≥ 3`. -/
def AllClockGE3 (c : Config (AgentState L K)) : Prop :=
  ∀ a ∈ c, a.role = .clock ∧ 3 ≤ a.phase.val

/-- `Transition` keeps both outputs at phase `≥ 3` for a clock-clock pair at phase
`≥ 3` (phases never decrease). -/
theorem Transition_clock_pair_phase (s t : AgentState L K)
    (hs_clock : s.role = .clock) (ht_clock : t.role = .clock)
    (hs_phase : 3 ≤ s.phase.val) (ht_phase : 3 ≤ t.phase.val) :
    3 ≤ (Transition L K s t).1.phase.val ∧ 3 ≤ (Transition L K s t).2.phase.val := by
  have hepi := phaseEpidemicUpdate_clock s t hs_clock ht_clock hs_phase ht_phase
  have hle := phaseEpidemicUpdate_phase_le_Transition_phase (L := L) (K := K) s t
  exact ⟨le_trans hepi.2.2.2.2.1 hle.1, le_trans hepi.2.2.2.2.2 hle.2⟩

/-- The per-pair statement specialized to the count-monotonicity over `AllClockGE3`:
each branch keeps both outputs Clocks with minutes non-decreasing, so the threshold
count over the produced pair is at least that over the consumed pair. -/
theorem rBeyondGE3_pair_mono (T : ℕ) (s t : AgentState L K)
    (hs_clock : s.role = .clock) (ht_clock : t.role = .clock)
    (hs_phase : 3 ≤ s.phase.val) (ht_phase : 3 ≤ t.phase.val) :
    Multiset.countP (fun a => clockBeyondP T a) ({s, t} : Multiset (AgentState L K))
      ≤ Multiset.countP (fun a => clockBeyondP T a)
          ({(Transition L K s t).1, (Transition L K s t).2}
            : Multiset (AgentState L K)) := by
  have htr := Transition_clock_pair s t hs_clock ht_clock hs_phase ht_phase
  rw [countP_pair, countP_pair]
  have key : ∀ x x' : AgentState L K, x'.role = .clock → x.minute.val ≤ x'.minute.val →
      x.role = .clock →
      (if clockBeyondP T x then (1:ℕ) else 0) ≤ (if clockBeyondP T x' then 1 else 0) := by
    intro x x' hx'r hx'm hxr
    unfold clockBeyondP
    simp only [hx'r, hxr, true_and]
    split_ifs <;> omega
  have h1 := key s _ htr.1 htr.2.2.1 hs_clock
  have h2 := key t _ htr.2.1 htr.2.2.2 ht_clock
  omega

/-- `rBeyond T` is non-decreasing under any chosen-pair update, on `AllClockGE3`. -/
theorem rBeyondGE3_stepOrSelf_ge (T : ℕ) (c : Config (AgentState L K))
    (hw : AllClockGE3 c) (r₁ r₂ : AgentState L K) :
    rBeyond T c ≤ rBeyond T (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂) := by
  classical
  by_cases happ : Protocol.Applicable c r₁ r₂
  · obtain ⟨h1c, h1p⟩ := hw r₁ (mem_of_applicable_left happ)
    obtain ⟨h2c, h2p⟩ := hw r₂ (mem_of_applicable_right happ)
    have hsub : ({r₁, r₂} : Multiset (AgentState L K)) ≤ c := happ
    have hc' : Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂
        = c - {r₁, r₂} + {(NonuniformMajority L K).δ r₁ r₂ |>.1,
            (NonuniformMajority L K).δ r₁ r₂ |>.2} := by
      unfold Protocol.stepOrSelf; rw [if_pos happ]
    have hδ : (NonuniformMajority L K).δ r₁ r₂ = Transition L K r₁ r₂ := rfl
    unfold rBeyond
    rw [hc', Multiset.countP_add, Multiset.countP_sub hsub]
    have hpair_le : Multiset.countP (fun a => clockBeyondP T a)
        ({r₁, r₂} : Multiset (AgentState L K))
          ≤ Multiset.countP (fun a => clockBeyondP T a) c := Multiset.countP_le_of_le _ hsub
    have hmono := rBeyondGE3_pair_mono T r₁ r₂ h1c h2c h1p h2p
    rw [hδ]
    omega
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]

/-- `AllClockGE3` is one-step support closed (absorbing). -/
theorem AllClockGE3_absorbing (c c' : Config (AgentState L K))
    (hw : AllClockGE3 c) (hc' : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    AllClockGE3 c' := by
  classical
  by_cases hc : 2 ≤ c.card
  · rw [show (NonuniformMajority L K).stepDistOrSelf c = (NonuniformMajority L K).stepDist c hc by
        unfold Protocol.stepDistOrSelf; rw [dif_pos hc]] at hc'
    obtain ⟨⟨r₁, r₂⟩, hr⟩ := Protocol.stepDist_support (NonuniformMajority L K) c hc c' hc'
    subst hr
    by_cases happ : Protocol.Applicable c r₁ r₂
    · obtain ⟨h1c, h1p⟩ := hw r₁ (mem_of_applicable_left happ)
      obtain ⟨h2c, h2p⟩ := hw r₂ (mem_of_applicable_right happ)
      have hsub : ({r₁, r₂} : Multiset (AgentState L K)) ≤ c := happ
      have htr := Transition_clock_pair r₁ r₂ h1c h2c h1p h2p
      have htp := Transition_clock_pair_phase r₁ r₂ h1c h2c h1p h2p
      intro a ha
      -- a is in c - {r₁,r₂} (so in c, a clock at phase ≥ 3) or one of the two outputs.
      have hsc : Protocol.scheduledStep (NonuniformMajority L K) c (r₁, r₂)
          = c - {r₁, r₂} + {(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2} := by
        unfold Protocol.scheduledStep Protocol.stepOrSelf
        rw [if_pos happ]; rfl
      rw [hsc] at ha
      rw [Multiset.mem_add] at ha
      rcases ha with ha | ha
      · exact hw a (Multiset.mem_of_le (Multiset.sub_le_self _ _) ha)
      · rw [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at ha
        rcases ha with rfl | rfl
        · exact ⟨htr.1, htp.1⟩
        · exact ⟨htr.2.1, htp.2⟩
    · -- not applicable: scheduledStep is the identity.
      rw [Protocol.scheduledStep, Protocol.stepOrSelf_eq_self_of_not_applicable happ]
      exact hw
  · rw [show (NonuniformMajority L K).stepDistOrSelf c = PMF.pure c by
        unfold Protocol.stepDistOrSelf; rw [dif_neg hc]] at hc'
    rw [PMF.mem_support_pure_iff] at hc'
    subst hc'; exact hw

/-- `rBeyond T` is preserved-or-raised on the one-step kernel support, over the
genuinely absorbing window `AllClockGE3`. -/
theorem rBeyondGE3_ge_monotone (T m : ℕ) (c c' : Config (AgentState L K))
    (hw : AllClockGE3 c) (h : m ≤ rBeyond T c)
    (hc' : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    m ≤ rBeyond T c' := by
  classical
  by_cases hc : 2 ≤ c.card
  · rw [show (NonuniformMajority L K).stepDistOrSelf c = (NonuniformMajority L K).stepDist c hc by
        unfold Protocol.stepDistOrSelf; rw [dif_pos hc]] at hc'
    obtain ⟨⟨r₁, r₂⟩, hr⟩ := Protocol.stepDist_support (NonuniformMajority L K) c hc c' hc'
    rw [← hr]
    exact le_trans h (rBeyondGE3_stepOrSelf_ge T c hw r₁ r₂)
  · rw [show (NonuniformMajority L K).stepDistOrSelf c = PMF.pure c by
        unfold Protocol.stepDistOrSelf; rw [dif_neg hc]] at hc'
    rw [PMF.mem_support_pure_iff] at hc'
    subst hc'; exact h

/-! ## Part 7 — the clock-minute potential, the drift, and `clock_real_advance`.

We transplant C3's `seedPot_contracts_on_floor` to the real kernel.  The potential
`rSeedPot` drives `rBeyond (T+1)` (the count of Clocks at minute `≥ T+1`) up to the
full population `n`; `Post` is "all `n` Clocks reached minute `≥ T+1`".  The drift
factor `r = 1 − p·(1−e^{−s})`, where the advance probability `p = m·(m−1)/(n·(n−1))`
is the single same-state drip pair's scheduler mass — Doty's `1/c²` clock-pair
fraction, DERIVED by pair-counting in `clock_real_drip_advance_prob`, never assumed. -/

/-- The clamped "reached `T+1`" count, capped at `n`. -/
def rClamp (n T : ℕ) (c : Config (AgentState L K)) : ℕ := min (rBeyond (T + 1) c) n

/-- The "level `T+1` finished" predicate: all `n` agents reached minute `≥ T+1`. -/
def rFinished (n T : ℕ) (c : Config (AgentState L K)) : Prop := n ≤ rBeyond (T + 1) c

/-- The clock-minute window potential (exponential of the deficit `n − rClamp`). -/
noncomputable def rSeedPot (n T : ℕ) (s : ℝ) (c : Config (AgentState L K)) : ℝ≥0∞ :=
  if n ≤ rBeyond (T + 1) c then 0
  else ENNReal.ofReal (Real.exp (s * ((n : ℝ) - (rClamp n T c : ℝ))))

theorem rSeedPot_measurable (n T : ℕ) (s : ℝ) :
    Measurable (rSeedPot (L := L) (K := K) n T s) :=
  fun _ _ => DiscreteMeasurableSpace.forall_measurableSet _

theorem rClamp_eq_of_lt (n T : ℕ) (c : Config (AgentState L K))
    (h : rBeyond (T + 1) c < n) : rClamp (L := L) (K := K) n T c = rBeyond (T + 1) c := by
  unfold rClamp; omega

/-- The clock-minute floor invariant: `card = n`, the window `AllClockGE3`, level `T`
crossed (all `n` Clocks at minute `≥ T`), and a witnessing Phase-3 Clock state `w`
at minute exactly `T < cap` of which there are `≥ 2` copies whenever the level is
unfinished.  The witness is what makes the drip advance fire; it is TRUE in the real
dynamics (Clocks at minute `< cap` are at Phase 3 and there are `n − rBeyond(T+1)`
of them at minute exactly `T`). -/
structure rFloorInv (n T : ℕ) (c : Config (AgentState L K)) : Prop where
  card : c.card = n
  window : AllClockGE3 c
  crossedT : rBeyond T c = n
  witness : ¬ rFinished (L := L) (K := K) n T c →
    ∃ w : AgentState L K, w.phase.val = 3 ∧ w.role = .clock ∧ w.minute.val = T ∧
      2 ≤ c.count w

/-- Pointwise one-step bound on the clock-minute potential, mirroring C3's
`seedPot_pointwise_bound`, using `rBeyondGE3_ge_monotone` for support monotonicity. -/
theorem rSeedPot_pointwise_bound (n T : ℕ) (s : ℝ) (hs : 0 < s)
    (c : Config (AgentState L K)) (hw : AllClockGE3 c) (m : ℕ)
    (hm : rBeyond (T + 1) c = m) (hm_hi : m < n)
    (c' : Config (AgentState L K))
    (hsupp : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    rSeedPot (L := L) (K := K) n T s c' ≤
      (if m + 1 ≤ rBeyond (T + 1) c' then
        ENNReal.ofReal (Real.exp (s * ((n : ℝ) - (m : ℝ) - 1)))
      else
        ENNReal.ofReal (Real.exp (s * ((n : ℝ) - (m : ℝ))))) := by
  have hmono : m ≤ rBeyond (T + 1) c' :=
    rBeyondGE3_ge_monotone (T + 1) m c c' hw (by rw [hm]) hsupp
  unfold rSeedPot rClamp
  by_cases hfin : n ≤ rBeyond (T + 1) c'
  · rw [if_pos hfin]; split_ifs <;> positivity
  · rw [if_neg hfin]
    rw [not_le] at hfin
    by_cases hadv : m + 1 ≤ rBeyond (T + 1) c'
    · rw [if_pos hadv]
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      have hclamp : min (rBeyond (T + 1) c') n = rBeyond (T + 1) c' := by omega
      rw [hclamp]
      have : (m : ℝ) + 1 ≤ (rBeyond (T + 1) c' : ℝ) := by exact_mod_cast hadv
      nlinarith [hs, this]
    · rw [if_neg hadv]
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      have heq : rBeyond (T + 1) c' = m := by omega
      have hclamp : min (rBeyond (T + 1) c') n = rBeyond (T + 1) c' := by omega
      rw [hclamp, heq]

/-- The drip-advance probability is at least `p := 2/(n·(n−1))` in the unfinished
regime, derived from the witness Clock (`2 ≤ count w`) via
`clock_real_drip_advance_prob` and `m·(m−1) ≥ 2` for `m ≥ 2`. -/
theorem rdrip_prob_ge (n T : ℕ) (hn : 2 ≤ n) (hT : T < K * (L + 1))
    (c : Config (AgentState L K)) (hfl : rFloorInv (L := L) (K := K) n T c)
    (hnc : ¬ rFinished (L := L) (K := K) n T c) :
    ENNReal.ofReal ((2 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) ≤
      ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
        {c' | rBeyond (T + 1) c + 1 ≤ rBeyond (T + 1) c'} := by
  obtain ⟨w, hw3, hwc, hwm, hwcount⟩ := hfl.witness hnc
  have hcard2 : 2 ≤ c.card := by rw [hfl.card]; omega
  have hstep := clock_real_drip_advance_prob T c w hw3 hwc hwm hT hcard2 (rBeyond (T + 1) c)
    rfl hwcount
  have hcardn : c.card = n := hfl.card
  rw [hcardn] at hstep
  refine le_trans ?_ hstep
  apply ENNReal.ofReal_le_ofReal
  set m := c.count w with hm
  have hmle : m ≤ n := by rw [hm, ← hfl.card]; exact Multiset.count_le_card w c
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hden_pos : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
  have hnum : (2 : ℝ) ≤ (m : ℝ) * ((m : ℝ) - 1) := by
    have hm2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hwcount
    nlinarith
  -- 2/(n(n-1)) ≤ (m(m-1))/(n(n-1)) since 2 ≤ m(m-1) and the denominator is positive.
  gcongr

/-- **The clock-minute drift on the REAL kernel (THE HARD CORE).**  On the floor
invariant (`card = n`, window `AllClockGE3`, level `T` crossed) the clock-minute
potential contracts at rate `r = 1 − p·(1−e^{−s})` with `p = 2/(n·(n−1))`.  The `p`
factor is the single drip pair's scheduler mass, DERIVED by pair-counting in
`clock_real_drip_advance_prob` (the `1/c²` source), NOT assumed.  Structure mirrors
C3's `seedPot_contracts_on_floor`. -/
theorem rSeedPot_contracts_on_floor (n T : ℕ) (hn : 2 ≤ n) (hT : T < K * (L + 1))
    (s : ℝ) (hs : 0 < s)
    (c : Config (AgentState L K)) (hfl : rFloorInv (L := L) (K := K) n T c)
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
  have hstep := rdrip_prob_ge n T hn hT c hfl hnc
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
        exact rSeedPot_pointwise_bound n T s hs c hfl.window m hm.symm hm_hi x hsupp
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
        have hq_ge : ENNReal.ofReal pR ≤ q := by
          rw [hpR]; exact hstep
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

/-! ## Part 8 — packaging the drift into `PhaseConvergence`.

We card/window-guard the potential (`⊤` off the floor shell `card = n ∧ AllClockGE3`)
so the threshold link `¬Post → 1 ≤ Φ` holds globally (off-shell `Φ = ⊤ ≥ 1`,
on-shell-unfinished `Φ = rSeedPot ≥ 1`), exactly as C3's `seedPotG`. -/

/-- The shell predicate carried through `Post`. -/
def rShell (n : ℕ) (c : Config (AgentState L K)) : Prop := c.card = n ∧ AllClockGE3 c

/-- The guarded clock-minute potential: `⊤` off the shell, else `rSeedPot`. -/
noncomputable def rSeedPotG (n T : ℕ) (s : ℝ) (c : Config (AgentState L K)) : ℝ≥0∞ :=
  open Classical in
  if c.card = n ∧ AllClockGE3 c then rSeedPot (L := L) (K := K) n T s c else ⊤

theorem rSeedPotG_measurable (n T : ℕ) (s : ℝ) :
    Measurable (rSeedPotG (L := L) (K := K) n T s) :=
  fun _ _ => DiscreteMeasurableSpace.forall_measurableSet _

theorem rSeedPotG_eq_on_shell (n T : ℕ) (s : ℝ) (c : Config (AgentState L K))
    (h : c.card = n ∧ AllClockGE3 c) :
    rSeedPotG (L := L) (K := K) n T s c = rSeedPot (L := L) (K := K) n T s c := by
  unfold rSeedPotG; rw [if_pos h]

/-- `rFinished` is one-step support closed: `rBeyond (T+1)` is non-decreasing on
`AllClockGE3`, so once `n ≤ rBeyond (T+1)` it stays so.  Together with `card = n`
and the absorbing window this is the kernel-absorbing `Post`. -/
theorem rFinished_absorbing (n T : ℕ)
    (c c' : Config (AgentState L K))
    (h : c.card = n ∧ AllClockGE3 c ∧ rFinished (L := L) (K := K) n T c)
    (hc' : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    c'.card = n ∧ AllClockGE3 c' ∧ rFinished (L := L) (K := K) n T c' := by
  obtain ⟨hcard, hw, hfin⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [Protocol.stepDistOrSelf_support_card_eq (NonuniformMajority L K) c c' hc']; exact hcard
  · exact AllClockGE3_absorbing c c' hw hc'
  · exact rBeyondGE3_ge_monotone (T + 1) n c c' hw hfin hc'

/-- The clock-minute drift holds on the WHOLE floor invariant (finished or not):
on finished configs `Φ = 0` and `rFinished` is preserved.  This is the `hdrift`
that `windowDrift_PhaseConvergence` consumes. -/
theorem rSeedPot_drift_floorInv (n T : ℕ) (hn : 2 ≤ n) (hT : T < K * (L + 1))
    (s : ℝ) (hs : 0 < s)
    (c : Config (AgentState L K)) (hfl : rFloorInv (L := L) (K := K) n T c) :
    ∫⁻ c', rSeedPot (L := L) (K := K) n T s c' ∂((NonuniformMajority L K).transitionKernel c) ≤
      ENNReal.ofReal (1 - ((2 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) * (1 - Real.exp (-s)))
        * rSeedPot (L := L) (K := K) n T s c := by
  by_cases hfin : rFinished (L := L) (K := K) n T c
  · have hΦc0 : rSeedPot (L := L) (K := K) n T s c = 0 := by
      unfold rSeedPot rFinished at *; rw [if_pos hfin]
    rw [hΦc0, mul_zero, nonpos_iff_eq_zero]
    change ∫⁻ c', rSeedPot (L := L) (K := K) n T s c'
        ∂((NonuniformMajority L K).stepDistOrSelf c).toMeasure = 0
    rw [lintegral_eq_zero_iff (rSeedPot_measurable n T s)]
    rw [Filter.eventuallyEq_iff_exists_mem]
    refine ⟨((NonuniformMajority L K).stepDistOrSelf c).support, ?_, ?_⟩
    · rw [mem_ae_iff, PMF.toMeasure_apply_eq_zero_iff _
        (DiscreteMeasurableSpace.forall_measurableSet _)]
      rw [Set.disjoint_left]; intro x hsupp hx
      exact hx (PMF.mem_support_iff _ _ |>.mp hsupp)
    · intro c' hc'
      have hfin' : rFinished (L := L) (K := K) n T c' :=
        rBeyondGE3_ge_monotone (T + 1) n c c' hfl.window hfin hc'
      show rSeedPot (L := L) (K := K) n T s c' = 0
      unfold rSeedPot rFinished at *; rw [if_pos hfin']
  · exact rSeedPot_contracts_on_floor n T hn hT s hs c hfl hfin

/-- On `{¬rFinished}` the clock-minute potential is `≥ 1`. -/
theorem not_finished_imp_rSeedPot_ge_one (n T : ℕ) (s : ℝ) (hs : 0 < s)
    (c : Config (AgentState L K)) (hnc : ¬ rFinished (L := L) (K := K) n T c) :
    1 ≤ rSeedPot (L := L) (K := K) n T s c := by
  unfold rFinished at hnc; rw [not_le] at hnc
  unfold rSeedPot rClamp
  rw [if_neg (by omega)]
  rw [← ENNReal.ofReal_one]
  apply ENNReal.ofReal_le_ofReal
  rw [show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]
  apply Real.exp_le_exp.mpr
  have hclamp_lt : min (rBeyond (T + 1) c) n ≤ n - 1 := by omega
  have h1 : ((min (rBeyond (T + 1) c) n : ℕ) : ℝ) ≤ (n : ℝ) - 1 := by
    have h1' : ((min (rBeyond (T + 1) c) n : ℕ) : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by
      exact_mod_cast hclamp_lt
    have h2 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    linarith
  have hdef : (1 : ℝ) ≤ (n : ℝ) - ((min (rBeyond (T + 1) c) n : ℕ) : ℝ) := by linarith
  nlinarith [hs, hdef]

/-- The clock-minute potential is bounded by `exp(s·n)` on the floor invariant. -/
theorem rSeedPot_le_max (n T : ℕ) (s : ℝ) (hs : 0 < s)
    (c : Config (AgentState L K)) :
    rSeedPot (L := L) (K := K) n T s c ≤ ENNReal.ofReal (Real.exp (s * (n : ℝ))) := by
  unfold rSeedPot rClamp
  by_cases hfin : n ≤ rBeyond (T + 1) c
  · rw [if_pos hfin]; positivity
  · rw [if_neg hfin]
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have hge0 : (0 : ℝ) ≤ ((min (rBeyond (T + 1) c) n : ℕ) : ℝ) := Nat.cast_nonneg _
    nlinarith [hs, hge0]

/-- Guarded drift on the floor invariant: integrate `rSeedPotG`; on the support the
shell holds (absorbing), so `rSeedPotG = rSeedPot` a.e. and the drift transfers. -/
theorem rSeedPotG_drift_floorInv (n T : ℕ) (hn : 2 ≤ n) (hT : T < K * (L + 1))
    (s : ℝ) (hs : 0 < s)
    (c : Config (AgentState L K)) (hfl : rFloorInv (L := L) (K := K) n T c) :
    ∫⁻ c', rSeedPotG (L := L) (K := K) n T s c' ∂((NonuniformMajority L K).transitionKernel c) ≤
      ENNReal.ofReal (1 - ((2 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) * (1 - Real.exp (-s)))
        * rSeedPotG (L := L) (K := K) n T s c := by
  have hshell : c.card = n ∧ AllClockGE3 c := ⟨hfl.card, hfl.window⟩
  rw [rSeedPotG_eq_on_shell n T s c hshell]
  have hint_eq : ∫⁻ c', rSeedPotG (L := L) (K := K) n T s c'
        ∂((NonuniformMajority L K).transitionKernel c)
      = ∫⁻ c', rSeedPot (L := L) (K := K) n T s c'
        ∂((NonuniformMajority L K).transitionKernel c) := by
    apply lintegral_congr_ae
    change ∀ᵐ c' ∂((NonuniformMajority L K).stepDistOrSelf c).toMeasure,
      rSeedPotG (L := L) (K := K) n T s c' = rSeedPot (L := L) (K := K) n T s c'
    rw [ae_iff, PMF.toMeasure_apply_eq_zero_iff _
      (DiscreteMeasurableSpace.forall_measurableSet _)]
    rw [Set.disjoint_left]
    intro x hsupp hbad
    apply hbad
    have hxshell : x.card = n ∧ AllClockGE3 x := by
      refine ⟨?_, AllClockGE3_absorbing c x hfl.window hsupp⟩
      rw [Protocol.stepDistOrSelf_support_card_eq (NonuniformMajority L K) c x hsupp]; exact hfl.card
    exact rSeedPotG_eq_on_shell n T s x hxshell
  rw [hint_eq]
  exact rSeedPot_drift_floorInv n T hn hT s hs c hfl

/-- Guarded threshold link: `¬(rShell ∧ rFinished) → 1 ≤ rSeedPotG`. -/
theorem rSeedPotG_link (n T : ℕ) (s : ℝ) (hs : 0 < s)
    (c : Config (AgentState L K))
    (hnc : ¬ (rShell (L := L) (K := K) n c ∧ rFinished (L := L) (K := K) n T c)) :
    1 ≤ rSeedPotG (L := L) (K := K) n T s c := by
  unfold rSeedPotG
  by_cases hshell : c.card = n ∧ AllClockGE3 c
  · rw [if_pos hshell]
    have hnf : ¬ rFinished (L := L) (K := K) n T c := fun h => hnc ⟨hshell, h⟩
    exact not_finished_imp_rSeedPot_ge_one n T s hs c hnf
  · rw [if_neg hshell]; exact le_top

/-- Guarded `Post` (`rShell ∧ rFinished`) is one-step support closed. -/
theorem rPostG_absorbing (n T : ℕ) (c c' : Config (AgentState L K))
    (h : rShell (L := L) (K := K) n c ∧ rFinished (L := L) (K := K) n T c)
    (hc' : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    rShell (L := L) (K := K) n c' ∧ rFinished (L := L) (K := K) n T c' := by
  obtain ⟨⟨hcard, hw⟩, hfin⟩ := h
  refine ⟨⟨?_, AllClockGE3_absorbing c c' hw hc'⟩, ?_⟩
  · rw [Protocol.stepDistOrSelf_support_card_eq (NonuniformMajority L K) c c' hc']; exact hcard
  · exact rBeyondGE3_ge_monotone (T + 1) n c c' hw hfin hc'

/-- Guarded potential bounded by `exp(s·n)` on the shell. -/
theorem rSeedPotG_le_max (n T : ℕ) (s : ℝ) (hs : 0 < s)
    (c : Config (AgentState L K)) (hshell : c.card = n ∧ AllClockGE3 c) :
    rSeedPotG (L := L) (K := K) n T s c ≤ ENNReal.ofReal (Real.exp (s * (n : ℝ))) := by
  rw [rSeedPotG_eq_on_shell n T s c hshell]
  exact rSeedPot_le_max n T s hs c

/-- **`clock_real_advance` — the LINCHPIN.**  The clock-minute advance for level
`T+1` packaged as a `PhaseConvergence` on the REAL `NonuniformMajority L K` kernel.
Starting from the floor invariant (`card = n`, all Clocks at phase ≥ 3 and minute
≥ T), all `n` Clocks reach minute `≥ T+1` within `t` interactions with failure `≤ ε`,
provided the geometric tail `r^t · exp(log2·n) ≤ ε` at `s = log 2`, where
`r = 1 − (2/(n(n−1)))·(1−1/2) = 1 − 1/(n(n−1))`.  The `2/(n(n−1))` advance factor is
Doty's `1/c²` clock-pair fraction, DERIVED by pair-counting (the single drip pair's
scheduler mass), NEVER assumed. -/
noncomputable def clock_real_advance (n T : ℕ) (hn : 2 ≤ n) (hT : T < K * (L + 1))
    (witnessOf : ∀ c : Config (AgentState L K),
      c.card = n → AllClockGE3 c → rBeyond T c = n →
      ¬ rFinished (L := L) (K := K) n T c →
      ∃ w : AgentState L K, w.phase.val = 3 ∧ w.role = .clock ∧ w.minute.val = T ∧
        2 ≤ c.count w)
    (t : ℕ) (ε : ℝ≥0)
    (hε : ENNReal.ofReal (1 - ((2 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) * (1 - Real.exp (-Real.log 2)))
            ^ t * ENNReal.ofReal (Real.exp (Real.log 2 * (n : ℝ))) / 1 ≤ (ε : ℝ≥0∞)) :
    PhaseConvergence (NonuniformMajority L K).transitionKernel := by
  have hs : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  refine WindowConcentration.windowDrift_PhaseConvergence (NonuniformMajority L K)
    (rSeedPotG (L := L) (K := K) n T (Real.log 2)) (rSeedPotG_measurable n T (Real.log 2))
    (fun c => c.card = n ∧ AllClockGE3 c ∧ rBeyond T c = n)        -- Q (absorbing)
    ?_                                                              -- hQ_abs
    (ENNReal.ofReal (1 - ((2 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) * (1 - Real.exp (-Real.log 2))))
    ?_                                                              -- hdrift
    (fun c => c.card = n ∧ AllClockGE3 c ∧ rBeyond T c = n)        -- Pre
    (fun c => rShell (L := L) (K := K) n c ∧ rFinished (L := L) (K := K) n T c)  -- Post
    (rPostG_absorbing n T)                                         -- hPost_abs
    1 one_ne_zero ENNReal.one_ne_top                               -- θ = 1
    (rSeedPotG_link n T (Real.log 2) hs)                           -- hlink
    (fun c h => h)                                                 -- hPre_Q
    (ENNReal.ofReal (Real.exp (Real.log 2 * (n : ℝ))))            -- Φ₀
    ?_                                                             -- hPre_bound
    t ε hε                                                        -- hε
  · -- hQ_abs
    rintro c c' ⟨hcard, hw, hcr⟩ hc'
    refine ⟨?_, AllClockGE3_absorbing c c' hw hc', ?_⟩
    · rw [Protocol.stepDistOrSelf_support_card_eq (NonuniformMajority L K) c c' hc']; exact hcard
    · have hge := rBeyondGE3_ge_monotone T n c c' hw (le_of_eq hcr.symm) hc'
      have hle : rBeyond T c' ≤ c'.card := by
        unfold rBeyond; exact Multiset.countP_le_card _ _
      have hcard' : c'.card = n := by
        rw [Protocol.stepDistOrSelf_support_card_eq (NonuniformMajority L K) c c' hc']; exact hcard
      omega
  · -- hdrift: build the floor invariant (with witness) and apply the guarded drift.
    rintro c ⟨hcard, hw, hcr⟩
    have hfl : rFloorInv (L := L) (K := K) n T c :=
      { card := hcard, window := hw, crossedT := hcr,
        witness := fun hnf => witnessOf c hcard hw hcr hnf }
    exact rSeedPotG_drift_floorInv n T hn hT (Real.log 2) hs c hfl
  · -- hPre_bound
    rintro c ⟨hcard, hw, _⟩
    exact rSeedPotG_le_max n T (Real.log 2) hs c ⟨hcard, hw⟩

end ClockRealKernel

end ExactMajority
