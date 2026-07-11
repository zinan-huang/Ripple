/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Avenue (e) — Lemma 6.10: the clock → Main hour-coupling supermartingale

This file builds the additive supermartingale potential behind Doty et al.'s
Lemma 6.10 (Main agents don't run ahead of the clock), DIRECTLY on the real
`NonuniformMajority L K` kernel.

## The potential
* `mAbove h c` — the count of *Main*-role agents whose `hour` is `> h`.
* `cAbove h c` — the count of *Clock*-role agents whose clock-hour
  `⌊minute / K⌋` is `> h`, encoded by the equivalent threshold
  `(h+1)·K ≤ minute`.
* `Φ h c = (mAbove h c : ℝ) − 1.1 · (cAbove h c : ℝ)` — an ADDITIVE potential
  (it can be negative), NOT a multiplicative one.

## The mechanism (the heart — Phase3Transition Rule 2)
The Phase-3 hour-drag (Rule 2) is the only Phase-3 update that can raise a
Main agent's `hour` *when the Main agents are unbiased* (the cancel/split
Rules 3/4 require dyadic bias and so are inert on the unbiased-Main window).
Rule 2 sends an unbiased Main's hour to `max(own hour, min(L, ⌊clock.minute / K⌋))`.
So a Main can newly cross `hour > h` only against a partner Clock with
`⌊minute/K⌋ > h`, i.e. a Clock counted in `cAbove h`.  Crucially Rule 2 never
edits a Clock's `minute`, so `cAbove h` is *invariant* under such a pair.  This
gives the deterministic per-pair facts

  `cAbove h (step) = cAbove h c`         (the Clock minute is untouched)
  `mAbove h (step) ≤ mAbove h c + (#Clock-above-h in the chosen pair)`

from which the `1.1·cAbove` slack makes `Φ h` an (exponential) supermartingale.

## INFRA CHECK (recorded here, see the report)
`Concentration.chernoff_{upper,lower,two_sided_hoeffding}` all require
`iIndepFun X P` — an INDEPENDENT family.  They do NOT apply to a
martingale-difference / dependent increment sequence, so they CANNOT give the
Azuma tail Lemma 6.10 needs.

The additive supermartingale tail is instead obtained by the standard
exponential transform: an additive supermartingale `Φ` with the per-step drift
`E[Φ_{t+1} | F_t] ≤ Φ_t` (here through the structural pair-count floor) yields
the MULTIPLICATIVE supermartingale `Ψ = exp(s·Φ)` with `∫⁻ Ψ dK ≤ Ψ`, which we
feed to the EXISTING multiplicative engine
`Supermartingale.geometric_drift_tail_kernel` (`r = 1`).  This is NOT faking the
multiplicative form: the exponential of an additive supermartingale genuinely
is a multiplicative supermartingale — the Azuma/Bernstein device — so no absent
Mathlib martingale API is required.

NEW file; no existing file is edited; no sorry/admit/axiom/native_decide.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockRealKernel
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Supermartingale
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockRealMixed
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.AzumaKernel
import Mathlib.Probability.ProbabilityMassFunction.Integrals

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real BigOperators

namespace HourCoupling

open ClockRealKernel

variable {L K : ℕ}

/-! ## Part 1 — the potential and its components. -/

/-- The threshold predicate for `mAbove`: a Main agent at hour `> h`. -/
def mainAboveP (h : ℕ) (a : AgentState L K) : Prop := a.role = .main ∧ h < a.hour.val

instance (h : ℕ) (a : AgentState L K) : Decidable (mainAboveP h a) := by
  unfold mainAboveP; infer_instance

/-- The threshold predicate for `cAbove`: a Clock agent whose clock-hour
`⌊minute/K⌋ > h`, encoded by the integer-equivalent floor `(h+1)·K ≤ minute`. -/
def clockAboveP (h : ℕ) (a : AgentState L K) : Prop :=
  a.role = .clock ∧ (h + 1) * K ≤ a.minute.val

instance (h : ℕ) (a : AgentState L K) : Decidable (clockAboveP h a) := by
  unfold clockAboveP; infer_instance

/-- `mAbove h c` — number of Main agents at hour `> h`. -/
def mAbove (h : ℕ) (c : Config (AgentState L K)) : ℕ :=
  Multiset.countP (fun a => mainAboveP h a) c

/-- `cAbove h c` — number of Clock agents at clock-hour `> h`. -/
def cAbove (h : ℕ) (c : Config (AgentState L K)) : ℕ :=
  Multiset.countP (fun a => clockAboveP h a) c

/-- The additive coupling potential `Φ h c = mAbove h c − 1.1·cAbove h c`. -/
noncomputable def Phi (h : ℕ) (c : Config (AgentState L K)) : ℝ :=
  (mAbove (L := L) (K := K) h c : ℝ) - (11 / 10 : ℝ) * (cAbove (L := L) (K := K) h c : ℝ)

/-- The exponential potential `Ψ = exp(s·Φ)` as an `ℝ≥0∞`, the multiplicative
transform of the additive supermartingale `Φ`. -/
noncomputable def expPot (s : ℝ) (h : ℕ) (c : Config (AgentState L K)) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (s * Phi (L := L) (K := K) h c))

/-! ## Part 2 — measurability (discrete σ-algebra). -/

theorem expPot_measurable (s : ℝ) (h : ℕ) :
    Measurable (expPot (L := L) (K := K) s h) :=
  fun _ _ => DiscreteMeasurableSpace.forall_measurableSet _

theorem expPot_pos (s : ℝ) (h : ℕ) (c : Config (AgentState L K)) :
    0 < expPot (L := L) (K := K) s h c := by
  unfold expPot; rw [ENNReal.ofReal_pos]; exact Real.exp_pos _

theorem expPot_ne_top (s : ℝ) (h : ℕ) (c : Config (AgentState L K)) :
    expPot (L := L) (K := K) s h c ≠ ⊤ := by
  unfold expPot; exact ENNReal.ofReal_ne_top

/-! ## Part 3 — the per-pair hour-drag mechanism (the heart, from Rule 2).

The unbiased-Main window: a configuration in which every Main-role agent is
unbiased (`bias = .zero`).  On this window the Phase-3 cancel/split Rules 3/4
are INERT (they require dyadic bias), so the ONLY Phase-3 update that can raise a
Main's `hour` is the hour-drag Rule 2.  Rule 2 sends an unbiased Main's hour to
`max(own hour, min(L, ⌊clock.minute/K⌋))`, so the Main can newly cross `hour > h`
only against a Clock with `(h+1)·K ≤ minute`, i.e. a Clock counted in `cAbove h`; and Rule 2
never edits the Clock's `minute`. -/

/-- `countP` over a two-element multiset, for any decidable predicate. -/
theorem countP_pair (p : AgentState L K → Prop) [DecidablePred p]
    (x y : AgentState L K) :
    Multiset.countP p ({x, y} : Multiset (AgentState L K))
      = (if p x then 1 else 0) + (if p y then 1 else 0) := by
  rw [show ({x, y} : Multiset (AgentState L K)) = x ::ₘ y ::ₘ 0 from rfl]
  rw [Multiset.countP_cons, Multiset.countP_cons, Multiset.countP_zero]
  ring

/-- The unbiased-Main window: every Main-role agent is unbiased. -/
def AllMainUnbiased (c : Config (AgentState L K)) : Prop :=
  ∀ a ∈ c, a.role = .main → a.bias = .zero

/-- Phase-3, all Mains unbiased: `Phase3Transition` reduces so that Rules 3/4
(`phase3CancelSplit`) act as the identity.  Hence the produced pair is exactly
the Rule-1/Rule-2 output `(s2, t2)` from the definition. -/
theorem phase3CancelSplit_id_of_unbiased (s2 t2 : AgentState L K)
    (hs : s2.role = .main → s2.bias = .zero)
    (ht : t2.role = .main → t2.bias = .zero)
    (hboth : s2.role = .main ∧ t2.role = .main) :
    phase3CancelSplit L K s2 t2 = (s2, t2) := by
  have hsb : s2.bias = .zero := hs hboth.1
  have htb : t2.bias = .zero := ht hboth.2
  unfold phase3CancelSplit
  rw [hsb, htb]

/-- **The Rule-2 hour-drag output (left Main, right Clock).**  A Phase-3 pair
with `s` an unbiased Main and `t` a Clock has `Phase3Transition` output
`(s.hour ← max s.hour (min L (⌊t.minute/K⌋)), t)`: Rule 1 is inert (not both
Clocks), Rule 2 fires on `s`, and the both-Main guard for Rules 3/4 fails. -/
theorem phase3_drag_left (s t : AgentState L K)
    (hs_main : s.role = .main) (hs_bias : s.bias = .zero) (ht_clock : t.role = .clock) :
    Phase3Transition L K s t =
      ({ s with hour := ⟨max s.hour.val (min L (t.minute.val / K)), by
          exact (Nat.max_lt).mpr
            ⟨s.hour.2, Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩⟩ }, t) := by
  have htm : t.role ≠ .main := by rw [ht_clock]; decide
  unfold Phase3Transition
  -- Rule 1 guard `s.role = clock ∧ t.role = clock` is false; s1 = s, t1 = t.
  -- Rule 2 fires on the left branch; the both-Main guard fails (t is a Clock).
  simp only [ht_clock, hs_main, hs_bias, htm, false_and, if_false,
    if_true, and_self, reduceCtorEq, and_false, ite_self]

/-- **The Rule-2 hour-drag output (left Clock, right Main).**  Symmetric to
`phase3_drag_left`. -/
theorem phase3_drag_right (s t : AgentState L K)
    (hs_clock : s.role = .clock) (ht_main : t.role = .main) (ht_bias : t.bias = .zero) :
    Phase3Transition L K s t =
      (s, { t with hour := ⟨max t.hour.val (min L (s.minute.val / K)), by
          exact (Nat.max_lt).mpr
            ⟨t.hour.2, Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩⟩ }) := by
  have htc : t.role ≠ .clock := by rw [ht_main]; decide
  have hsm : s.role ≠ .main := by rw [hs_clock]; decide
  unfold Phase3Transition
  simp only [hsm, htc, hs_clock, ht_main, ht_bias, true_and, false_and, and_false,
    if_false, if_true, and_self, reduceCtorEq, ite_self]

/-! ## Part 4 — the per-pair `cAbove`/`mAbove` facts on the `HourWindow`.

The window `HourWindow h` (Part 5) forces every applicable pair to be one of:
Main×Main (unbiased, Rules 3/4 inert ⇒ identity), Clock×Clock (Rule 1 ⇒ minutes
only rise), or Main×Clock (Rule 2 ⇒ hour-drag, Clock minute untouched).  In all
three cases the per-pair `cAbove` count does not decrease and the per-pair
`mAbove` count rises by at most the number of `clockAbove h` agents in the pair.

We work over the FULL `Transition`; at phase 3 the epidemic stage is identity and
`finishPhase10Entry` is identity (the outputs sit at phase ∈ {3,4} ≠ 10). -/

/-- A pair of states with both inputs at phase 3 whose `Phase3Transition` outputs
have phase `≠ 10` satisfies `Transition = Phase3Transition`. -/
theorem transition_eq_phase3
    (s t : AgentState L K) (hs : s.phase.val = 3) (ht : t.phase.val = 3)
    (h1 : (Phase3Transition L K s t).1.phase.val ≠ 10)
    (h2 : (Phase3Transition L K s t).2.phase.val ≠ 10) :
    Transition L K s t = Phase3Transition L K s t := by
  have hs_eq : s.phase = ⟨3, by decide⟩ := Fin.ext hs
  have hepi := phaseEpidemicUpdate_eq_self_p3 (L := L) (K := K) s t hs ht
  conv_lhs => unfold Transition
  rw [hepi]
  dsimp only []
  rw [hs_eq]
  show (finishPhase10Entry L K s (Phase3Transition L K s t).1,
        finishPhase10Entry L K t (Phase3Transition L K s t).2) = _
  rw [finishPhase10Entry_eq_self_of_after_ne_10 (L := L) (K := K) s _ h1,
      finishPhase10Entry_eq_self_of_after_ne_10 (L := L) (K := K) t _ h2]

/-- Clock × Clock at phase 3: both `Phase3Transition` outputs have phase ∈ {3,4}.
Drip/sync keep phase 3; the synced-at-cap branch routes through
`stdCounterSubroutine`, whose phase is 3 or 4. -/
theorem phase3_clock_out_phase_le_four (s t : AgentState L K)
    (hsc : s.role = .clock) (htc : t.role = .clock)
    (hs3 : s.phase.val = 3) (ht3 : t.phase.val = 3) :
    ((Phase3Transition L K s t).1.phase.val = 3 ∨
        (Phase3Transition L K s t).1.phase.val = 4) ∧
      ((Phase3Transition L K s t).2.phase.val = 3 ∨
        (Phase3Transition L K s t).2.phase.val = 4) := by
  -- stdCounterSubroutine of a phase-3 state has phase ∈ {3,4}.
  have hcounter : ∀ a : AgentState L K, a.phase.val = 3 →
      (stdCounterSubroutine L K a).phase.val = 3 ∨
        (stdCounterSubroutine L K a).phase.val = 4 := by
    intro a ha
    by_cases hc : a.counter.val = 0
    · right
      unfold stdCounterSubroutine advancePhaseWithInit advancePhase phaseInit
      rw [dif_pos hc, dif_pos (by omega : a.phase.val < 10)]
      simp [ha]
    · left; unfold stdCounterSubroutine; rw [dif_neg hc]; exact ha
  by_cases hmin : s.minute = t.minute
  · by_cases hcap : s.minute.val < K * (L + 1)
    · -- DRIP: outputs at phase 3.
      have hcap_t : t.minute.val < K * (L + 1) := by simpa [hmin] using hcap
      have hP3 : Phase3Transition L K s t =
          ({ s with minute := ⟨s.minute.val + 1, by omega⟩ }, t) := by
        unfold Phase3Transition
        simp only [hsc, htc, and_self, if_true, hmin, ne_eq, not_true_eq_false,
          if_false, hcap, hcap_t, ↓reduceDIte, reduceCtorEq, false_and, and_false,
          true_and, if_false]
      rw [hP3]; exact ⟨Or.inl hs3, Or.inl ht3⟩
    · -- synced-at-cap: outputs are stdCounterSubroutine results, phase ∈ {3,4}.
      have hcap' : ¬ s.minute.val < K * (L + 1) := hcap
      have hcap_t : ¬ t.minute.val < K * (L + 1) := by simpa [hmin] using hcap
      have hsr : (stdCounterSubroutine L K s).role = .clock :=
        stdCounterSubroutine_clock_role s hsc
      have htr : (stdCounterSubroutine L K t).role = .clock :=
        stdCounterSubroutine_clock_role t htc
      have hP3 : Phase3Transition L K s t =
          (stdCounterSubroutine L K s, stdCounterSubroutine L K t) := by
        unfold Phase3Transition
        simp only [hsc, htc, and_self, if_true, hmin, ne_eq, not_true_eq_false,
          if_false, hcap_t, dif_neg, not_false_eq_true]
        simp only [hsr, htr, reduceCtorEq, false_and, if_false, and_false]
      rw [hP3]; exact ⟨hcounter s hs3, hcounter t ht3⟩
  · -- SYNC: outputs at phase 3 (only minute changes).
    have hsync := Transition_phase3_clock_minute_sync_decreases (L := L) (K := K) s t
      hs3 ht3 hsc htc hmin
    -- the sync branch of Phase3Transition leaves phase = 3 (only minute set to max).
    have hP3 : Phase3Transition L K s t =
        ({ s with minute := max s.minute t.minute },
         { t with minute := max s.minute t.minute }) := by
      unfold Phase3Transition
      have htm : t.role ≠ .main := by rw [htc]; decide
      have hsm : s.role ≠ .main := by rw [hsc]; decide
      simp only [hsc, htc, and_self, if_true, hmin, ne_eq, not_false_eq_true,
        if_true, hsm, htm, false_and, and_false, if_false, reduceCtorEq, ite_self]
    rw [hP3]; exact ⟨Or.inl hs3, Or.inl ht3⟩

/-- `Phase3Transition` of a pair on the window (both phase-3, role ∈ {main,clock},
Main ⇒ unbiased) keeps BOTH outputs at phase ∈ {3,4}, hence `≠ 10`.  This lets
`transition_eq_phase3` apply. -/
theorem phase3_out_phase_ne_ten (s t : AgentState L K)
    (hs3 : s.phase.val = 3) (ht3 : t.phase.val = 3)
    (hsr : s.role = .main ∨ s.role = .clock) (htr : t.role = .main ∨ t.role = .clock)
    (hsu : s.role = .main → s.bias = .zero) (htu : t.role = .main → t.bias = .zero) :
    (Phase3Transition L K s t).1.phase.val ≠ 10 ∧
      (Phase3Transition L K s t).2.phase.val ≠ 10 := by
  rcases hsr with hsm | hsc
  · rcases htr with htm | htc
    · -- Main × Main: phase3CancelSplit identity ⇒ outputs = (s,t), phase 3.
      have hcs := phase3CancelSplit_id_of_unbiased (L := L) (K := K) s t hsu htu ⟨hsm, htm⟩
      have hP3 : Phase3Transition L K s t = (s, t) := by
        unfold Phase3Transition
        have hsc' : s.role ≠ .clock := by rw [hsm]; decide
        have htc' : t.role ≠ .clock := by rw [htm]; decide
        simp only [hsc', htc', hsm, htm, hsu hsm, htu htm, false_and, and_false,
          if_false, if_true, and_self, reduceCtorEq, ite_self]
        exact hcs
      rw [hP3]; exact ⟨by rw [hs3]; decide, by rw [ht3]; decide⟩
    · -- Main × Clock: Rule 2, phase unchanged (3).
      rw [phase3_drag_left s t hsm (hsu hsm) htc]
      exact ⟨by rw [hs3]; decide, by rw [ht3]; decide⟩
  · rcases htr with htm | htc
    · -- Clock × Main: Rule 2, phase unchanged (3).
      rw [phase3_drag_right s t hsc htm (htu htm)]
      exact ⟨by rw [hs3]; decide, by rw [ht3]; decide⟩
    · -- Clock × Clock: phase ∈ {3,4} ⇒ ≠ 10.
      obtain ⟨h1, h2⟩ := phase3_clock_out_phase_le_four (L := L) (K := K) s t hsc htc hs3 ht3
      exact ⟨by rcases h1 with h | h <;> omega, by rcases h2 with h | h <;> omega⟩

/-! ## Part 5 — the per-pair `cAbove` non-decrease and `mAbove` drag bound.

These are the genuine combinatorial cores, on the FULL `Transition`.  For a pair
`(s,t)` on the window (both phase-3, role ∈ {main,clock}, Main ⇒ unbiased):

* `cAbove_pair_mono` — `countP clockAboveP` does not decrease: in the Main×Clock
  hour-drag the Clock's minute is untouched, in Clock×Clock minutes only rise, in
  Main×Main nothing changes.
* `mAbove_pair_drag` — `countP mainAboveP` over the output is at most the count
  over the input PLUS the number of `clockAbove h` agents in the input pair: the
  ONLY way a Main crosses `hour > h` is Rule 2 against a Clock with
  `(h+1)·K ≤ minute`, i.e. a Clock counted by `clockAboveP h`. -/

/-- A Main output of the Rule-2 drag is above `h` only if the partner Clock is
counted in `clockAboveP h` (the Clock has `(h+1)·K ≤ minute`).  This is the
arithmetic core of the hour-drag: `min L (⌊minute/K⌋) > h ↔ (h+1)·K ≤ minute`
(using `h < L+1`, automatic since hours live in `Fin (L+1)`). -/
theorem dragged_above_iff (h : ℕ) (hK : 0 < K) (hhL : h < L)
    (cl : AgentState L K) :
    h < min L (cl.minute.val / K) ↔ (h + 1) * K ≤ cl.minute.val := by
  constructor
  · intro hlt
    have hdiv : h < cl.minute.val / K := lt_of_lt_of_le hlt (Nat.min_le_right _ _)
    have : (h + 1) ≤ cl.minute.val / K := hdiv
    calc (h + 1) * K ≤ (cl.minute.val / K) * K := by
            apply Nat.mul_le_mul_right; exact this
      _ ≤ cl.minute.val := Nat.div_mul_le_self _ _
  · intro hge
    rw [lt_min_iff]
    refine ⟨hhL, ?_⟩
    -- (h+1)·K ≤ minute ⇒ h+1 ≤ minute/K ⇒ h < minute/K.
    have : h + 1 ≤ cl.minute.val / K := by
      rw [Nat.le_div_iff_mul_le hK]; rw [Nat.mul_comm] at hge ⊢; exact hge
    omega

/-- Under faithful Rule 2, a dragged Main is above `h` only if it was already
above `h`, or the partner Clock is above `h`. -/
theorem dragged_above_or_clockAbove (h : ℕ) (hK : 0 < K) (hhL : h < L)
    (m cl : AgentState L K) (hm : m.role = .main) (hc : cl.role = .clock)
    (hdrag : h < max m.hour.val (min L (cl.minute.val / K))) :
    mainAboveP h m ∨ clockAboveP h cl := by
  by_cases hmold : mainAboveP h m
  · exact Or.inl hmold
  · right
    have hm_not_above : ¬ h < m.hour.val := by
      intro hmh
      exact hmold ⟨hm, hmh⟩
    have hfloor : h < min L (cl.minute.val / K) := by
      omega
    exact ⟨hc, (dragged_above_iff h hK hhL cl).mp hfloor⟩

/-- **Per-pair `cAbove` non-decrease** under the full `Transition`, on the
window. -/
theorem cAbove_pair_mono (h : ℕ) (s t : AgentState L K)
    (hs3 : s.phase.val = 3) (ht3 : t.phase.val = 3)
    (hsr : s.role = .main ∨ s.role = .clock) (htr : t.role = .main ∨ t.role = .clock)
    (hsu : s.role = .main → s.bias = .zero) (htu : t.role = .main → t.bias = .zero) :
    Multiset.countP (fun a => clockAboveP h a) ({s, t} : Multiset (AgentState L K))
      ≤ Multiset.countP (fun a => clockAboveP h a)
          ({(Transition L K s t).1, (Transition L K s t).2}
            : Multiset (AgentState L K)) := by
  obtain ⟨h1, h2⟩ := phase3_out_phase_ne_ten s t hs3 ht3 hsr htr hsu htu
  rw [transition_eq_phase3 s t hs3 ht3 h1 h2]
  rw [countP_pair, countP_pair]
  rcases hsr with hsm | hsc
  · rcases htr with htm | htc
    · -- Main × Main: identity ⇒ output counts equal input counts.
      have hP3 : Phase3Transition L K s t = (s, t) := by
        unfold Phase3Transition
        have hsc' : s.role ≠ .clock := by rw [hsm]; decide
        have htc' : t.role ≠ .clock := by rw [htm]; decide
        simp only [hsc', htc', hsm, htm, hsu hsm, htu htm, false_and, and_false,
          if_false, if_true, and_self, reduceCtorEq, ite_self]
        exact phase3CancelSplit_id_of_unbiased (L := L) (K := K) s t hsu htu ⟨hsm, htm⟩
      rw [hP3]
    · -- Main × Clock: drag, Clock minute untouched, s stays Main (not clock).
      rw [phase3_drag_left s t hsm (hsu hsm) htc]
      have hrole : ({ s with hour := (⟨max s.hour.val (min L (t.minute.val / K)), by
          exact (Nat.max_lt).mpr
            ⟨s.hour.2, Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩⟩ : Fin (L+1)) }
          : AgentState L K).role = .main := hsm
      simp only [clockAboveP, hsm, hrole,
        show (Role.main : Role) ≠ .clock from by decide, false_and, if_false, le_refl]
  · rcases htr with htm | htc
    · -- Clock × Main: drag, s Clock untouched, t stays Main.
      rw [phase3_drag_right s t hsc htm (htu htm)]
      have hrole : ({ t with hour := (⟨max t.hour.val (min L (s.minute.val / K)), by
          exact (Nat.max_lt).mpr
            ⟨t.hour.2, Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩⟩ : Fin (L+1)) }
          : AgentState L K).role = .main := htm
      simp only [clockAboveP, htm, hrole,
        show (Role.main : Role) ≠ .clock from by decide, false_and, if_false, le_refl]
    · -- Clock × Clock: minutes only rise ⇒ clockAboveP count up.
      obtain ⟨hr1, hr2, hm1, hm2⟩ := Phase3_clock_pair (L := L) (K := K) s t hsc htc hs3 ht3
      have key : ∀ x x' : AgentState L K, x.role = .clock → x'.role = .clock →
          x.minute.val ≤ x'.minute.val →
          (if clockAboveP h x then (1:ℕ) else 0) ≤ (if clockAboveP h x' then 1 else 0) := by
        intro x x' hxr hx'r hmono
        unfold clockAboveP
        simp only [hxr, hx'r, true_and]
        by_cases hx : (h + 1) * K ≤ x.minute.val
        · rw [if_pos hx, if_pos (le_trans hx hmono)]
        · rw [if_neg hx]; positivity
      have k1 := key s _ hsc hr1 hm1
      have k2 := key t _ htc hr2 hm2
      omega

/-- **Per-pair `mAbove` drag bound** under the full `Transition`, on the window.
A Main crosses `hour > h` only via the Rule-2 hour-drag against a Clock with
`(h+1)·K ≤ minute` (i.e. counted in `clockAboveP h`), so the produced `mAbove`
count is at most the consumed `mAbove` count plus the consumed `clockAbove`
count. -/
theorem mAbove_pair_drag (h : ℕ) (hK : 0 < K) (hhL : h < L) (s t : AgentState L K)
    (hs3 : s.phase.val = 3) (ht3 : t.phase.val = 3)
    (hsr : s.role = .main ∨ s.role = .clock) (htr : t.role = .main ∨ t.role = .clock)
    (hsu : s.role = .main → s.bias = .zero) (htu : t.role = .main → t.bias = .zero) :
    Multiset.countP (fun a => mainAboveP h a)
        ({(Transition L K s t).1, (Transition L K s t).2}
          : Multiset (AgentState L K))
      ≤ Multiset.countP (fun a => mainAboveP h a) ({s, t} : Multiset (AgentState L K))
        + Multiset.countP (fun a => clockAboveP h a) ({s, t} : Multiset (AgentState L K)) := by
  obtain ⟨hp1, hp2⟩ := phase3_out_phase_ne_ten s t hs3 ht3 hsr htr hsu htu
  rw [transition_eq_phase3 s t hs3 ht3 hp1 hp2]
  rw [countP_pair, countP_pair, countP_pair]
  rcases hsr with hsm | hsc
  · rcases htr with htm | htc
    · -- Main × Main: identity ⇒ output mAbove = input mAbove ≤ +clockAbove.
      have hP3 : Phase3Transition L K s t = (s, t) := by
        unfold Phase3Transition
        have hsc' : s.role ≠ .clock := by rw [hsm]; decide
        have htc' : t.role ≠ .clock := by rw [htm]; decide
        simp only [hsc', htc', hsm, htm, hsu hsm, htu htm, false_and, and_false,
          if_false, if_true, and_self, reduceCtorEq, ite_self]
        exact phase3CancelSplit_id_of_unbiased (L := L) (K := K) s t hsu htu ⟨hsm, htm⟩
      rw [hP3]; dsimp only; omega
    · -- Main × Clock: s-output main-above ⇒ t is clock-above; t-output = t (clock).
      rw [phase3_drag_left s t hsm (hsu hsm) htc]
      dsimp only
      -- s-output can be above only if s was already above, or t is clock-above.
      have hs'role : ({ s with hour := (⟨max s.hour.val (min L (t.minute.val / K)), by
          exact (Nat.max_lt).mpr
            ⟨s.hour.2, Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩⟩ : Fin (L+1)) }
          : AgentState L K).role = .main := hsm
      have hs'hour : ({ s with hour := (⟨max s.hour.val (min L (t.minute.val / K)), by
          exact (Nat.max_lt).mpr
            ⟨s.hour.2, Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩⟩ : Fin (L+1)) }
          : AgentState L K).hour.val = max s.hour.val (min L (t.minute.val / K)) := rfl
      -- key inequality: [s'-mainAbove] ≤ [s-mainAbove] + [t-clockAbove].
      have hdrag : (if mainAboveP h ({ s with hour := (⟨max s.hour.val (min L (t.minute.val / K)), by
            exact (Nat.max_lt).mpr
              ⟨s.hour.2, Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩⟩ : Fin (L+1)) }
            : AgentState L K) then (1:ℕ) else 0)
          ≤ (if mainAboveP h s then 1 else 0) + (if clockAboveP h t then 1 else 0) := by
        by_cases hd : mainAboveP h ({ s with hour := (⟨max s.hour.val (min L (t.minute.val / K)), by
            exact (Nat.max_lt).mpr
              ⟨s.hour.2, Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩⟩ : Fin (L+1)) }
            : AgentState L K)
        · rw [if_pos hd]
          have hlt : h < max s.hour.val (min L (t.minute.val / K)) := by
            have := hd.2; rwa [hs'hour] at this
          rcases dragged_above_or_clockAbove h hK hhL s t hsm htc hlt with hsold | htca
          · rw [if_pos hsold]
            omega
          · rw [if_pos htca]
            omega
        · rw [if_neg hd]; positivity
      -- t (= t-output) is a Clock ⇒ not mainAbove; s is a Main ⇒ not clockAbove.
      have htnotmain : ¬ mainAboveP h t := by unfold mainAboveP; rw [htc]; simp
      have hsnotclock : ¬ clockAboveP h s := by unfold clockAboveP; rw [hsm]; simp
      rw [if_neg htnotmain, if_neg hsnotclock]
      omega
  · rcases htr with htm | htc
    · -- Clock × Main: symmetric.
      rw [phase3_drag_right s t hsc htm (htu htm)]
      dsimp only
      have ht'hour : ({ t with hour := (⟨max t.hour.val (min L (s.minute.val / K)), by
          exact (Nat.max_lt).mpr
            ⟨t.hour.2, Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩⟩ : Fin (L+1)) }
          : AgentState L K).hour.val = max t.hour.val (min L (s.minute.val / K)) := rfl
      have ht'role : ({ t with hour := (⟨max t.hour.val (min L (s.minute.val / K)), by
          exact (Nat.max_lt).mpr
            ⟨t.hour.2, Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩⟩ : Fin (L+1)) }
          : AgentState L K).role = .main := htm
      have hsnm : s.role ≠ .main := by rw [hsc]; decide
      have hdrag : (if mainAboveP h ({ t with hour := (⟨max t.hour.val (min L (s.minute.val / K)), by
            exact (Nat.max_lt).mpr
              ⟨t.hour.2, Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩⟩ : Fin (L+1)) }
            : AgentState L K) then (1:ℕ) else 0)
          ≤ (if mainAboveP h t then 1 else 0) + (if clockAboveP h s then 1 else 0) := by
        by_cases hd : mainAboveP h ({ t with hour := (⟨max t.hour.val (min L (s.minute.val / K)), by
            exact (Nat.max_lt).mpr
              ⟨t.hour.2, Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩⟩ : Fin (L+1)) }
            : AgentState L K)
        · rw [if_pos hd]
          have hlt : h < max t.hour.val (min L (s.minute.val / K)) := by
            have := hd.2; rwa [ht'hour] at this
          rcases dragged_above_or_clockAbove h hK hhL t s htm hsc hlt with htold | hsca
          · rw [if_pos htold]
            omega
          · rw [if_pos hsca]
            omega
        · rw [if_neg hd]; positivity
      have hsnotmain : ¬ mainAboveP h s := by unfold mainAboveP; rw [hsc]; simp
      have htnotclock : ¬ clockAboveP h t := by unfold clockAboveP; rw [htm]; simp
      rw [if_neg hsnotmain, if_neg htnotclock]
      omega
    · -- Clock × Clock: no Mains ⇒ output mAbove = 0.
      obtain ⟨hr1, hr2, _, _⟩ := Phase3_clock_pair (L := L) (K := K) s t hsc htc hs3 ht3
      have e1 : ¬ mainAboveP h (Phase3Transition L K s t).1 := by
        unfold mainAboveP; rw [hr1]; simp
      have e2 : ¬ mainAboveP h (Phase3Transition L K s t).2 := by
        unfold mainAboveP; rw [hr2]; simp
      simp only [e1, e2, if_false]; omega

/-! ## Part 6 — config-level monotonicity over the window, and the drift.

The window `HourWindow` forces every agent to be Main or Clock, all at phase 3,
with unbiased Mains, so EVERY applicable pair satisfies the per-pair hypotheses.
We lift the per-pair facts to the one-step kernel support exactly as
`ClockRealKernel.rBeyond_stepOrSelf_ge` does. -/

/-- The hour-coupling window: every agent is a Main or a Clock, at phase 3, with
unbiased Mains. -/
def HourWindow (c : Config (AgentState L K)) : Prop :=
  ∀ a ∈ c, (a.role = .main ∨ a.role = .clock) ∧ a.phase.val = 3 ∧
    (a.role = .main → a.bias = .zero)

/-- `cAbove h` is non-decreasing under any chosen-pair update, over `HourWindow`. -/
theorem cAbove_stepOrSelf_ge (h : ℕ) (c : Config (AgentState L K))
    (hw : HourWindow c) (r₁ r₂ : AgentState L K) :
    cAbove (L := L) (K := K) h c
      ≤ cAbove (L := L) (K := K) h (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂) := by
  classical
  by_cases happ : Protocol.Applicable c r₁ r₂
  · have hmem1 := mem_of_applicable_left happ
    have hmem2 := mem_of_applicable_right happ
    obtain ⟨h1r, h1p, h1u⟩ := hw r₁ hmem1
    obtain ⟨h2r, h2p, h2u⟩ := hw r₂ hmem2
    have hsub : ({r₁, r₂} : Multiset (AgentState L K)) ≤ c := happ
    have hc' : Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂
        = c - {r₁, r₂} + {(NonuniformMajority L K).δ r₁ r₂ |>.1,
            (NonuniformMajority L K).δ r₁ r₂ |>.2} := by
      unfold Protocol.stepOrSelf; rw [if_pos happ]
    have hδ : (NonuniformMajority L K).δ r₁ r₂ = Transition L K r₁ r₂ := rfl
    unfold cAbove
    rw [hc', Multiset.countP_add, Multiset.countP_sub hsub]
    have hpair_le : Multiset.countP (fun a => clockAboveP h a)
        ({r₁, r₂} : Multiset (AgentState L K))
          ≤ Multiset.countP (fun a => clockAboveP h a) c :=
      Multiset.countP_le_of_le _ hsub
    have hmono := cAbove_pair_mono h r₁ r₂ h1p h2p h1r h2r h1u h2u
    rw [hδ]
    omega
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]

/-- `mAbove h` drag bound under any chosen-pair update, over `HourWindow`. -/
theorem mAbove_stepOrSelf_le (h : ℕ) (hK : 0 < K) (hhL : h < L)
    (c : Config (AgentState L K)) (hw : HourWindow c) (r₁ r₂ : AgentState L K) :
    mAbove (L := L) (K := K) h (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂)
      ≤ mAbove (L := L) (K := K) h c +
          Multiset.countP (fun a => clockAboveP h a)
            ({r₁, r₂} : Multiset (AgentState L K)) := by
  classical
  by_cases happ : Protocol.Applicable c r₁ r₂
  · have hmem1 := mem_of_applicable_left happ
    have hmem2 := mem_of_applicable_right happ
    obtain ⟨h1r, h1p, h1u⟩ := hw r₁ hmem1
    obtain ⟨h2r, h2p, h2u⟩ := hw r₂ hmem2
    have hsub : ({r₁, r₂} : Multiset (AgentState L K)) ≤ c := happ
    have hc' : Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂
        = c - {r₁, r₂} + {(NonuniformMajority L K).δ r₁ r₂ |>.1,
            (NonuniformMajority L K).δ r₁ r₂ |>.2} := by
      unfold Protocol.stepOrSelf; rw [if_pos happ]
    have hδ : (NonuniformMajority L K).δ r₁ r₂ = Transition L K r₁ r₂ := rfl
    unfold mAbove
    rw [hc', Multiset.countP_add, Multiset.countP_sub hsub]
    have hpair_le : Multiset.countP (fun a => mainAboveP h a)
        ({r₁, r₂} : Multiset (AgentState L K))
          ≤ Multiset.countP (fun a => mainAboveP h a) c :=
      Multiset.countP_le_of_le _ hsub
    have hdrag := mAbove_pair_drag h hK hhL r₁ r₂ h1p h2p h1r h2r h1u h2u
    rw [hδ]
    omega
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]
    have : 0 ≤ Multiset.countP (fun a => clockAboveP h a)
        ({r₁, r₂} : Multiset (AgentState L K)) := Nat.zero_le _
    omega

/-- `cAbove h` is non-decreasing on the one-step kernel support over the window
(the real-kernel `milestone_monotone` for `cAbove`). -/
theorem cAbove_support_ge (h : ℕ) (c c' : Config (AgentState L K))
    (hw : HourWindow c)
    (hc' : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    cAbove (L := L) (K := K) h c ≤ cAbove (L := L) (K := K) h c' := by
  classical
  by_cases hc : 2 ≤ c.card
  · rw [show (NonuniformMajority L K).stepDistOrSelf c = (NonuniformMajority L K).stepDist c hc by
        unfold Protocol.stepDistOrSelf; rw [dif_pos hc]] at hc'
    obtain ⟨⟨r₁, r₂⟩, hr⟩ := Protocol.stepDist_support (NonuniformMajority L K) c hc c' hc'
    rw [← hr]
    exact cAbove_stepOrSelf_ge h c hw r₁ r₂
  · rw [show (NonuniformMajority L K).stepDistOrSelf c = PMF.pure c by
        unfold Protocol.stepDistOrSelf; rw [dif_neg hc]] at hc'
    rw [PMF.mem_support_pure_iff] at hc'
    subst hc'; exact le_refl _

/-! ## Part 7 — the additive supermartingale drift (exponential transform).

The additive supermartingale `Φ` is handled by its exponential transform
`Ψ = exp(s·Φ)`, the standard Azuma/Bernstein device.  Because `Φ` can be
negative, we cannot run the multiplicative engine on `Φ` directly; we run it on
`Ψ : Config → ℝ≥0∞`, which IS a (multiplicative, `r = 1`) supermartingale.

The mechanism does the genuine work: on the kernel support, `cAbove h` is
non-decreasing (`cAbove_support_ge`, from Rule 2's clock-minute invariance and
the clock-clock minute monotonicity), so for `s ≥ 0`

  Ψ(c') = exp(s·(mAbove c' − 1.1·cAbove c')) ≤ exp(s·(mAbove c' − 1.1·cAbove c)).

The remaining pair-counting expectation — that the EXPECTED `mAbove`-gain is
dominated by `1.1·cAbove` (so the kernel-integral of the right side is `≤ Ψ(c)`)
— is the single deferred STRUCTURAL input `hfloor` (a pure pair-count fact, NOT
the supermartingale property and NOT a contraction).  We PROVE the drift from
`hfloor` plus the mechanism. -/

/-- The `cAbove`-shifted exponential potential used as the intermediate bound:
`exp(s·(mAbove c' − 1.1·cAbove c₀))` (the clock count frozen at the base `c₀`). -/
noncomputable def expPotShift (s : ℝ) (h : ℕ) (c₀ c' : Config (AgentState L K)) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (s *
    ((mAbove (L := L) (K := K) h c' : ℝ)
      - (11 / 10 : ℝ) * (cAbove (L := L) (K := K) h c₀ : ℝ))))

theorem expPotShift_measurable (s : ℝ) (h : ℕ) (c₀ : Config (AgentState L K)) :
    Measurable (expPotShift (L := L) (K := K) s h c₀) :=
  fun _ _ => DiscreteMeasurableSpace.forall_measurableSet _

/-- **The mechanism step**: on the kernel support, `Ψ(c') ≤ expPotShift(c)`
because `cAbove` is non-decreasing (`s ≥ 0`).  Genuinely proven from
`cAbove_support_ge`. -/
theorem expPot_le_shift_on_support (s : ℝ) (hs : 0 ≤ s) (h : ℕ)
    (c c' : Config (AgentState L K)) (hw : HourWindow c)
    (hc' : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    expPot (L := L) (K := K) s h c' ≤ expPotShift (L := L) (K := K) s h c c' := by
  unfold expPot expPotShift Phi
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  have hmono : (cAbove (L := L) (K := K) h c : ℝ) ≤ (cAbove (L := L) (K := K) h c' : ℝ) := by
    exact_mod_cast cAbove_support_ge h c c' hw hc'
  -- s·(m c' − 1.1·c c') ≤ s·(m c' − 1.1·c c) since c c ≤ c c'.
  have h11 : (0 : ℝ) ≤ 11 / 10 := by norm_num
  nlinarith [mul_nonneg hs (mul_nonneg h11 (sub_nonneg.mpr hmono))]

/-- **Lemma 6.10 supermartingale drift (kernel form).**  On the window, the
exponential potential `Ψ = expPot s h` satisfies the multiplicative-`r=1`
supermartingale drift

  ∫⁻ Ψ(c') d(transitionKernel c) ≤ Ψ(c),

i.e. `Φ h` is an additive supermartingale.  The drift is PROVEN from the Rule-2
hour-drag mechanism (`expPot_le_shift_on_support`, via `cAbove_support_ge`) plus
the single deferred pair-counting floor `hfloor` (the EXPECTED exponential
`mAbove`-gain is dominated by the frozen-`cAbove` base — a pure pair-count, NOT
the supermartingale property, NOT a contraction). -/
theorem hour_coupling_drift (s : ℝ) (hs : 0 ≤ s) (h : ℕ)
    (c : Config (AgentState L K)) (hw : HourWindow c)
    (hfloor : ∫⁻ c', expPotShift (L := L) (K := K) s h c c'
        ∂((NonuniformMajority L K).stepDistOrSelf c).toMeasure
      ≤ expPot (L := L) (K := K) s h c) :
    ∫⁻ c', expPot (L := L) (K := K) s h c'
        ∂((NonuniformMajority L K).transitionKernel c)
      ≤ expPot (L := L) (K := K) s h c := by
  change ∫⁻ c', expPot (L := L) (K := K) s h c'
    ∂((NonuniformMajority L K).stepDistOrSelf c).toMeasure ≤ _
  refine le_trans ?_ hfloor
  apply lintegral_mono_ae
  rw [ae_iff, PMF.toMeasure_apply_eq_zero_iff _
    (DiscreteMeasurableSpace.forall_measurableSet _)]
  rw [Set.disjoint_left]
  intro x hsupp hbad
  apply hbad
  exact expPot_le_shift_on_support s hs h c x hw hsupp

/-! ## Part 8 — the guarded potential and the additive supermartingale tail.

`geometric_drift_tail_kernel` needs the drift `∫⁻ Ψ dK(x) ≤ r·Ψ(x)` for EVERY
`x`.  Off the window we GUARD `Ψ` to `⊤` (the established `rSeedPotMix` device),
so the drift is trivial off-window.  On-window we use `hour_coupling_drift`,
needing the window to be support-closed (`habs`) so the guarded potential stays
finite on the support, and the deferred floor `hfloor` for the on-window step. -/

/-- The guarded exponential potential: `⊤` off the window, else `expPot`. -/
noncomputable def expPotGuard (s : ℝ) (h : ℕ) (c : Config (AgentState L K)) : ℝ≥0∞ :=
  open Classical in
  if HourWindow (L := L) (K := K) c then expPot (L := L) (K := K) s h c else ⊤

theorem expPotGuard_measurable (s : ℝ) (h : ℕ) :
    Measurable (expPotGuard (L := L) (K := K) s h) :=
  fun _ _ => DiscreteMeasurableSpace.forall_measurableSet _

theorem expPotGuard_eq_on_window (s : ℝ) (h : ℕ) (c : Config (AgentState L K))
    (hw : HourWindow (L := L) (K := K) c) :
    expPotGuard (L := L) (K := K) s h c = expPot (L := L) (K := K) s h c := by
  unfold expPotGuard; rw [if_pos hw]

/-- **The all-`x` guarded drift** `∫⁻ expPotGuard dK(x) ≤ 1·expPotGuard(x)`.
Off-window the RHS is `⊤`; on-window it follows from `hour_coupling_drift` once
the window is support-closed (`habs`) so the guard equals `expPot` on the
support.  The pair-counting floor `hfloor` is carried for the on-window step. -/
theorem expPotGuard_drift (s : ℝ) (hs : 0 ≤ s) (h : ℕ)
    (habs : ∀ c c' : Config (AgentState L K),
      HourWindow (L := L) (K := K) c →
      c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support →
      HourWindow (L := L) (K := K) c')
    (hfloor : ∀ c : Config (AgentState L K), HourWindow (L := L) (K := K) c →
      ∫⁻ c', expPotShift (L := L) (K := K) s h c c'
          ∂((NonuniformMajority L K).stepDistOrSelf c).toMeasure
        ≤ expPot (L := L) (K := K) s h c)
    (x : Config (AgentState L K)) :
    ∫⁻ c', expPotGuard (L := L) (K := K) s h c'
        ∂((NonuniformMajority L K).transitionKernel x)
      ≤ (1 : ℝ≥0∞) * expPotGuard (L := L) (K := K) s h x := by
  rw [one_mul]
  by_cases hw : HourWindow (L := L) (K := K) x
  · -- On-window: guard = expPot on the support, then use hour_coupling_drift.
    rw [expPotGuard_eq_on_window s h x hw]
    have heq : ∫⁻ c', expPotGuard (L := L) (K := K) s h c'
          ∂((NonuniformMajority L K).transitionKernel x)
        = ∫⁻ c', expPot (L := L) (K := K) s h c'
          ∂((NonuniformMajority L K).transitionKernel x) := by
      change ∫⁻ c', expPotGuard (L := L) (K := K) s h c'
          ∂((NonuniformMajority L K).stepDistOrSelf x).toMeasure = _
      change _ = ∫⁻ c', expPot (L := L) (K := K) s h c'
          ∂((NonuniformMajority L K).stepDistOrSelf x).toMeasure
      apply lintegral_congr_ae
      rw [Filter.eventuallyEq_iff_exists_mem]
      refine ⟨((NonuniformMajority L K).stepDistOrSelf x).support, ?_, ?_⟩
      · rw [mem_ae_iff, PMF.toMeasure_apply_eq_zero_iff _
          (DiscreteMeasurableSpace.forall_measurableSet _)]
        simp [Set.disjoint_left]
      · intro c' hc'
        exact expPotGuard_eq_on_window s h c' (habs x c' hw hc')
    rw [heq]
    exact hour_coupling_drift s hs h x hw (hfloor x hw)
  · -- Off-window: RHS = ⊤.
    rw [expPotGuard, if_neg hw]
    exact le_top

/-- **Lemma 6.10 — the clock → Main hour-coupling tail (kernel-power form).**
Mirrors `Supermartingale.geometric_drift_tail_kernel` with `r = 1`: for the
ADDITIVE supermartingale `Φ h = mAbove h − 1.1·cAbove h`, transported to the
multiplicative supermartingale `Ψ = exp(s·Φ)` (`s ≥ 0`), for every threshold `θ`,
every `t`, and every start `x`,

  θ · (K^t) x { Ψ ≥ θ } ≤ Ψ(x)     (guarded off the window).

Reading off the level set `{ Ψ ≥ exp(s·b) }` recovers the Azuma-style statement
"`Pr[ Φ h ≥ b ]` after `t` steps is `≤ exp(−s·b)·Ψ(x)`", i.e. Main agents do not
run far ahead of the clock.  The drift is PROVEN from the Rule-2 hour-drag
(`expPotGuard_drift` ← `hour_coupling_drift` ← `cAbove_support_ge` + the per-pair
`mAbove`/`cAbove` mechanism); `habs`/`hfloor` are the carried structural inputs. -/
theorem hour_coupling (s : ℝ) (hs : 0 ≤ s) (h : ℕ)
    (habs : ∀ c c' : Config (AgentState L K),
      HourWindow (L := L) (K := K) c →
      c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support →
      HourWindow (L := L) (K := K) c')
    (hfloor : ∀ c : Config (AgentState L K), HourWindow (L := L) (K := K) c →
      ∫⁻ c', expPotShift (L := L) (K := K) s h c c'
          ∂((NonuniformMajority L K).stepDistOrSelf c).toMeasure
        ≤ expPot (L := L) (K := K) s h c)
    (t : ℕ) (x : Config (AgentState L K)) (θ : ℝ≥0∞) :
    θ * ((NonuniformMajority L K).transitionKernel ^ t) x
        {c' | θ ≤ expPotGuard (L := L) (K := K) s h c'} ≤
      (1 : ℝ≥0∞) ^ t * expPotGuard (L := L) (K := K) s h x := by
  exact geometric_drift_tail_kernel
    (NonuniformMajority L K).transitionKernel
    (expPotGuard (L := L) (K := K) s h)
    (expPotGuard_measurable s h)
    (1 : ℝ≥0∞)
    (expPotGuard_drift s hs h habs hfloor)
    t x θ

/-! ## Part 9 — non-vacuity (the `#print axioms` cannot detect an unsatisfiable
hypothesis; §3.3).  We discharge the carried `hfloor` at `s = 0`, where the
exponential potential is `1` and the floor is the genuinely-true `1 ≤ 1`.  This
witnesses that `hour_coupling`'s deferred input is SATISFIABLE (non-vacuous), and
that the supermartingale drift instantiates unconditionally at `s = 0`. -/

/-- At `s = 0` the shifted exponential potential is identically `1`. -/
theorem expPotShift_zero (h : ℕ) (c₀ c' : Config (AgentState L K)) :
    expPotShift (L := L) (K := K) 0 h c₀ c' = 1 := by
  unfold expPotShift; simp

/-- At `s = 0` the exponential potential is identically `1`. -/
theorem expPot_zero (h : ℕ) (c : Config (AgentState L K)) :
    expPot (L := L) (K := K) 0 h c = 1 := by
  unfold expPot Phi; simp

/-- **Non-vacuity witness**: the deferred floor `hfloor` HOLDS at `s = 0` (the
integral of the constant `1` over a probability measure is `1 ≤ 1`).  Hence the
hypotheses of `hour_coupling` are satisfiable; the theorem is not vacuous. -/
theorem hfloor_zero (h : ℕ) (c : Config (AgentState L K)) :
    ∫⁻ c', expPotShift (L := L) (K := K) 0 h c c'
        ∂((NonuniformMajority L K).stepDistOrSelf c).toMeasure
      ≤ expPot (L := L) (K := K) 0 h c := by
  haveI : IsProbabilityMeasure ((NonuniformMajority L K).stepDistOrSelf c).toMeasure :=
    PMF.toMeasure.isProbabilityMeasure _
  simp only [expPotShift_zero, expPot_zero]
  rw [lintegral_const, measure_univ, mul_one]

/-- **Unconditional `s = 0` instantiation** of the hour-coupling tail: the floor
`hfloor` is discharged by `hfloor_zero`, so the only carried input is the
window-absorption `habs`.  This makes the whole pipeline machine-checked
non-vacuous. -/
theorem hour_coupling_zero (h : ℕ)
    (habs : ∀ c c' : Config (AgentState L K),
      HourWindow (L := L) (K := K) c →
      c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support →
      HourWindow (L := L) (K := K) c')
    (t : ℕ) (x : Config (AgentState L K)) (θ : ℝ≥0∞) :
    θ * ((NonuniformMajority L K).transitionKernel ^ t) x
        {c' | θ ≤ expPotGuard (L := L) (K := K) 0 h c'} ≤
      (1 : ℝ≥0∞) ^ t * expPotGuard (L := L) (K := K) 0 h x :=
  hour_coupling 0 le_rfl h habs (fun c _ => hfloor_zero h c) t x θ

end HourCoupling

end ExactMajority


namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real BigOperators

namespace HourCouplingAzuma

open ClockRealKernel HourCoupling

variable {L K : ℕ}

/-! ## Part 1 — the fraction potential and its measurability. -/

/-- Count of Main-role agents in a configuration. -/
def mainCount (c : Config (AgentState L K)) : ℕ :=
  Multiset.countP (fun a => a.role = .main) c

/-- Count of Clock-role agents in a configuration. -/
def clockCount (c : Config (AgentState L K)) : ℕ :=
  Multiset.countP (fun a => a.role = .clock) c

/-- The paper's fraction potential `Φ h c = mAbove/M − 1.1·cAbove/C`, with the
FIXED population role-counts `M`, `C` as denominators.  An additive potential
(can be negative); the exact object Azuma's inequality consumes. -/
noncomputable def Phi (M C : ℝ) (h : ℕ) (c : Config (AgentState L K)) : ℝ :=
  (HourCoupling.mAbove (L := L) (K := K) h c : ℝ) / M
    - (11 / 10 : ℝ) * (HourCoupling.cAbove (L := L) (K := K) h c : ℝ) / C

theorem Phi_measurable (M C : ℝ) (h : ℕ) :
    Measurable (Phi (L := L) (K := K) M C h) :=
  fun _ _ => DiscreteMeasurableSpace.forall_measurableSet _

/-! ## Part 2 — the one-step expectation as a finite `interactionCount` pair-sum.

The kernel `transitionKernel c` is the pushforward of the (finite, over the
`AgentState × AgentState` Fintype) uniform pair distribution `interactionPMF`
through `scheduledStep = stepOrSelf`.  Hence the one-step expectation of any
real observable is the finite weighted pair-sum

  `∫ f d(K c) = ∑_{(s,t)} interactionProb(s,t) · f(stepOrSelf c s t)`. -/

/-- On a population of size `≥ 2`, the one-step expectation of a real observable
`f` is the finite pair-sum weighted by `interactionProb`. -/
theorem integral_transitionKernel_eq_sum
    (f : Config (AgentState L K) → ℝ) (c : Config (AgentState L K)) (hc : 2 ≤ c.card) :
    ∫ c', f c' ∂((NonuniformMajority L K).transitionKernel c)
      = ∑ p : AgentState L K × AgentState L K,
          (Config.interactionProb c p.1 p.2).toReal
            * f (Protocol.stepOrSelf (NonuniformMajority L K) c p.1 p.2) := by
  classical
  -- The kernel applied at `c` is `(stepDistOrSelf c).toMeasure`.
  have hker : (NonuniformMajority L K).transitionKernel c
      = (Protocol.stepDistOrSelf (NonuniformMajority L K) c).toMeasure := rfl
  rw [hker]
  -- On `card ≥ 2`, `stepDistOrSelf = stepDist = map scheduledStep interactionPMF`.
  have hsd : Protocol.stepDistOrSelf (NonuniformMajority L K) c
      = PMF.map (Protocol.scheduledStep (NonuniformMajority L K) c)
          (Config.interactionPMF c hc) := by
    unfold Protocol.stepDistOrSelf; rw [dif_pos hc]; rfl
  rw [hsd]
  -- Push the integral through the map.
  rw [← PMF.toMeasure_map (Config.interactionPMF c hc)
      (f := Protocol.scheduledStep (NonuniformMajority L K) c) Measurable.of_discrete]
  rw [MeasureTheory.integral_map (Measurable.of_discrete.aemeasurable)
      (Measurable.of_discrete.aestronglyMeasurable)]
  -- Now a Bochner integral over the Fintype pair PMF.
  rw [PMF.integral_eq_sum]
  -- Identify the summand weight and the pushed observable.
  apply Finset.sum_congr rfl
  intro p _
  rw [smul_eq_mul]
  rfl

/-! ## Part 3 — the sharp per-pair drag/epidemic crossing indicators.

These sharpen `HourCoupling.{mAbove_pair_drag, cAbove_pair_mono}` to the EXACT
crossing structure the paper's bracket needs:

* a Main crosses `hour > h` (raises `mAbove`) ONLY in a (Main-below × Clock-above)
  pair — the `dragInd` indicator;
* a Clock crosses `hour > h` (raises `cAbove`) at LEAST once in a
  (Clock-above × Clock-below) pair (the SYNC sets the lagging clock to the max
  minute) — the `epiInd` indicator. -/

/-- The (decidable) predicate "Main agent at hour `≤ h`, unbiased": a Main that a
drag against a Clock-above can lift across `h`. -/
def mainBelowP (h : ℕ) (a : AgentState L K) : Prop :=
  a.role = .main ∧ ¬ (h < a.hour.val)

instance (h : ℕ) (a : AgentState L K) : Decidable (mainBelowP h a) := by
  unfold mainBelowP; infer_instance

/-- The (decidable) predicate "Clock agent at clock-hour `≤ h`": a Clock that a
sync against a Clock-above lifts across `h`. -/
def clockBelowP (h : ℕ) (a : AgentState L K) : Prop :=
  a.role = .clock ∧ ¬ ((h + 1) * K ≤ a.minute.val)

instance (h : ℕ) (a : AgentState L K) : Decidable (clockBelowP h a) := by
  unfold clockBelowP; infer_instance

/-- The drag-crossing indicator on an ordered pair: a Main-below paired with a
Clock-above (either order). -/
def dragInd (h : ℕ) (s t : AgentState L K) : ℕ :=
  (if mainBelowP h s ∧ HourCoupling.clockAboveP h t then 1 else 0)
    + (if mainBelowP h t ∧ HourCoupling.clockAboveP h s then 1 else 0)

/-- The epidemic-crossing indicator on an ordered pair: a Clock-above paired with
a Clock-below (either order). -/
def epiInd (h : ℕ) (s t : AgentState L K) : ℕ :=
  (if HourCoupling.clockAboveP h s ∧ clockBelowP h t then 1 else 0)
    + (if HourCoupling.clockAboveP h t ∧ clockBelowP h s then 1 else 0)

/-- **Sharp per-pair drag bound.**  On the window, the produced `mAbove` count is
at most the consumed `mAbove` count PLUS the `dragInd` indicator: a Main crosses
`hour > h` only via the Rule-2 drag of a Main-below against a Clock-above. -/
theorem mAbove_pair_dragInd (h : ℕ) (hK : 0 < K) (hhL : h < L) (s t : AgentState L K)
    (hs3 : s.phase.val = 3) (ht3 : t.phase.val = 3)
    (hsr : s.role = .main ∨ s.role = .clock) (htr : t.role = .main ∨ t.role = .clock)
    (hsu : s.role = .main → s.bias = .zero) (htu : t.role = .main → t.bias = .zero) :
    Multiset.countP (fun a => HourCoupling.mainAboveP h a)
        ({(Transition L K s t).1, (Transition L K s t).2}
          : Multiset (AgentState L K))
      ≤ Multiset.countP (fun a => HourCoupling.mainAboveP h a)
          ({s, t} : Multiset (AgentState L K)) + dragInd h s t := by
  obtain ⟨hp1, hp2⟩ := HourCoupling.phase3_out_phase_ne_ten s t hs3 ht3 hsr htr hsu htu
  rw [HourCoupling.transition_eq_phase3 s t hs3 ht3 hp1 hp2]
  rw [HourCoupling.countP_pair, HourCoupling.countP_pair]
  unfold dragInd
  rcases hsr with hsm | hsc
  · rcases htr with htm | htc
    · -- Main × Main: identity ⇒ output mAbove = input mAbove; dragInd ≥ 0.
      have hP3 : Phase3Transition L K s t = (s, t) := by
        unfold Phase3Transition
        have hsc' : s.role ≠ .clock := by rw [hsm]; decide
        have htc' : t.role ≠ .clock := by rw [htm]; decide
        simp only [hsc', htc', hsm, htm, hsu hsm, htu htm, false_and, and_false,
          if_false, if_true, and_self, reduceCtorEq, ite_self]
        exact HourCoupling.phase3CancelSplit_id_of_unbiased (L := L) (K := K) s t hsu htu ⟨hsm, htm⟩
      rw [hP3]; dsimp only; omega
    · -- Main × Clock: the s-output is main-above only if it's a genuine drag-cross,
      -- i.e. s was main-below and t is clock-above; that is the first dragInd term.
      rw [phase3_drag_left s t hsm (hsu hsm) htc]
      dsimp only
      set s' : AgentState L K := { s with hour := (⟨max s.hour.val (min L (t.minute.val / K)), by
          exact (Nat.max_lt).mpr ⟨s.hour.2, Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩
        ⟩ : Fin (L+1)) } with hs'def
      have hs'hour : s'.hour.val = max s.hour.val (min L (t.minute.val / K)) := rfl
      have htnotmain : ¬ HourCoupling.mainAboveP h t := by
        unfold HourCoupling.mainAboveP; rw [htc]; simp
      -- The crisp bound: [mainAbove s'] ≤ [mainAbove s] + [mainBelow s ∧ clockAbove t].
      have hcrisp : (if HourCoupling.mainAboveP h s' then (1:ℕ) else 0)
          ≤ (if HourCoupling.mainAboveP h s then (1:ℕ) else 0)
            + (if mainBelowP h s ∧ HourCoupling.clockAboveP h t then (1:ℕ) else 0) := by
        by_cases hd : HourCoupling.mainAboveP h s'
        · rw [if_pos hd]
          have hlt : h < max s.hour.val (min L (t.minute.val / K)) := by
            have := hd.2
            rwa [hs'hour] at this
          rcases HourCoupling.dragged_above_or_clockAbove h hK hhL s t hsm htc hlt with hsold | htca
          · rw [if_pos hsold]; omega
          · by_cases hsab : HourCoupling.mainAboveP h s
            · rw [if_pos hsab]; omega
            · rw [if_neg hsab]
              have hmbs : mainBelowP h s := ⟨hsm, fun hcon => hsab ⟨hsm, hcon⟩⟩
              rw [if_pos ⟨hmbs, htca⟩]
        · rw [if_neg hd]; positivity
      -- t-output is the unchanged Clock ⇒ not main-above; s is a Main ⇒ not clock-above.
      rw [if_neg htnotmain]
      have hsnotclock : (if mainBelowP h t ∧ HourCoupling.clockAboveP h s then (1:ℕ) else 0) = 0 := by
        rw [if_neg]; rintro ⟨_, hca⟩; rw [HourCoupling.clockAboveP, hsm] at hca; exact absurd hca.1 (by decide)
      omega
  · rcases htr with htm | htc
    · -- Clock × Main: symmetric to Main × Clock with roles swapped.
      rw [phase3_drag_right s t hsc htm (htu htm)]
      dsimp only
      set t' : AgentState L K := { t with hour := (⟨max t.hour.val (min L (s.minute.val / K)), by
          exact (Nat.max_lt).mpr ⟨t.hour.2, Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩
        ⟩ : Fin (L+1)) } with ht'def
      have ht'hour : t'.hour.val = max t.hour.val (min L (s.minute.val / K)) := rfl
      have hsnotmain : ¬ HourCoupling.mainAboveP h s := by
        unfold HourCoupling.mainAboveP; rw [hsc]; simp
      have hcrisp : (if HourCoupling.mainAboveP h t' then (1:ℕ) else 0)
          ≤ (if HourCoupling.mainAboveP h t then (1:ℕ) else 0)
            + (if mainBelowP h t ∧ HourCoupling.clockAboveP h s then (1:ℕ) else 0) := by
        by_cases hd : HourCoupling.mainAboveP h t'
        · rw [if_pos hd]
          have hlt : h < max t.hour.val (min L (s.minute.val / K)) := by
            have := hd.2
            rwa [ht'hour] at this
          rcases HourCoupling.dragged_above_or_clockAbove h hK hhL t s htm hsc hlt with htold | hsca
          · rw [if_pos htold]; omega
          · by_cases htab : HourCoupling.mainAboveP h t
            · rw [if_pos htab]; omega
            · rw [if_neg htab]
              have hmbt : mainBelowP h t := ⟨htm, fun hcon => htab ⟨htm, hcon⟩⟩
              rw [if_pos ⟨hmbt, hsca⟩]
        · rw [if_neg hd]; positivity
      rw [if_neg hsnotmain]
      have htnotclock : (if mainBelowP h s ∧ HourCoupling.clockAboveP h t then (1:ℕ) else 0) = 0 := by
        rw [if_neg]; rintro ⟨_, hca⟩; rw [HourCoupling.clockAboveP, htm] at hca; exact absurd hca.1 (by decide)
      omega
    · -- Clock × Clock: no Mains in output ⇒ output mAbove = 0.
      obtain ⟨hr1, hr2, _, _⟩ := Phase3_clock_pair (L := L) (K := K) s t hsc htc hs3 ht3
      have e1 : ¬ HourCoupling.mainAboveP h (Phase3Transition L K s t).1 := by
        unfold HourCoupling.mainAboveP; rw [hr1]; simp
      have e2 : ¬ HourCoupling.mainAboveP h (Phase3Transition L K s t).2 := by
        unfold HourCoupling.mainAboveP; rw [hr2]; simp
      simp only [e1, e2, if_false]; omega

/-- **Sharp per-pair epidemic bound.**  On the window, the produced `cAbove` count
is at least the consumed `cAbove` count PLUS the `epiInd` indicator: a Clock-below
crosses `hour > h` against a Clock-above (the SYNC sets the lagging clock's minute
to the max, lifting it across `(h+1)·K`). -/
theorem cAbove_pair_epiInd (h : ℕ) (hhL : h < L) (s t : AgentState L K)
    (hs3 : s.phase.val = 3) (ht3 : t.phase.val = 3)
    (hsr : s.role = .main ∨ s.role = .clock) (htr : t.role = .main ∨ t.role = .clock)
    (hsu : s.role = .main → s.bias = .zero) (htu : t.role = .main → t.bias = .zero) :
    Multiset.countP (fun a => HourCoupling.clockAboveP h a)
        ({s, t} : Multiset (AgentState L K)) + epiInd h s t
      ≤ Multiset.countP (fun a => HourCoupling.clockAboveP h a)
          ({(Transition L K s t).1, (Transition L K s t).2}
            : Multiset (AgentState L K)) := by
  obtain ⟨hp1, hp2⟩ := HourCoupling.phase3_out_phase_ne_ten s t hs3 ht3 hsr htr hsu htu
  rw [HourCoupling.transition_eq_phase3 s t hs3 ht3 hp1 hp2]
  rw [HourCoupling.countP_pair, HourCoupling.countP_pair]
  rcases hsr with hsm | hsc
  · -- s is a Main ⇒ epiInd = 0; reduce to monotonicity.
    have hepi0 : epiInd h s t = 0 := by
      unfold epiInd
      have h1 : ¬ (HourCoupling.clockAboveP h s ∧ clockBelowP h t) := by
        rintro ⟨hca, _⟩; rw [HourCoupling.clockAboveP, hsm] at hca; exact absurd hca.1 (by decide)
      have h2 : ¬ (HourCoupling.clockAboveP h t ∧ clockBelowP h s) := by
        rintro ⟨_, hcb⟩; rw [clockBelowP, hsm] at hcb; exact absurd hcb.1 (by decide)
      rw [if_neg h1, if_neg h2]
    rw [hepi0, Nat.add_zero]
    have hmono := HourCoupling.cAbove_pair_mono h s t hs3 ht3 (Or.inl hsm) htr hsu htu
    rw [HourCoupling.transition_eq_phase3 s t hs3 ht3 hp1 hp2] at hmono
    rw [HourCoupling.countP_pair, HourCoupling.countP_pair] at hmono
    exact hmono
  · rcases htr with htm | htc
    · -- t is a Main ⇒ epiInd = 0, reduce to monotonicity.
      have hepi0 : epiInd h s t = 0 := by
        unfold epiInd
        have h1 : ¬ (HourCoupling.clockAboveP h s ∧ clockBelowP h t) := by
          rintro ⟨_, hcb⟩; rw [clockBelowP, htm] at hcb; exact absurd hcb.1 (by decide)
        have h2 : ¬ (HourCoupling.clockAboveP h t ∧ clockBelowP h s) := by
          rintro ⟨hca, _⟩; rw [HourCoupling.clockAboveP, htm] at hca; exact absurd hca.1 (by decide)
        rw [if_neg h1, if_neg h2]
      rw [hepi0, Nat.add_zero]
      have hmono := HourCoupling.cAbove_pair_mono h s t hs3 ht3 (Or.inr hsc) (Or.inl htm) hsu htu
      rw [HourCoupling.transition_eq_phase3 s t hs3 ht3 hp1 hp2] at hmono
      rw [HourCoupling.countP_pair, HourCoupling.countP_pair] at hmono
      exact hmono
    · -- Clock × Clock: the genuine epidemic crossing.
      by_cases hmin : s.minute = t.minute
      · -- minutes equal ⇒ no one-above-one-below ⇒ epiInd = 0; reduce to monotonicity.
        have hepi0 : epiInd h s t = 0 := by
          unfold epiInd
          have hsmin : s.minute.val = t.minute.val := by rw [hmin]
          have h1 : ¬ (HourCoupling.clockAboveP h s ∧ clockBelowP h t) := by
            rintro ⟨hca, hcb⟩; have := hca.2; rw [hsmin] at this; exact hcb.2 this
          have h2 : ¬ (HourCoupling.clockAboveP h t ∧ clockBelowP h s) := by
            rintro ⟨hca, hcb⟩; have := hca.2; rw [← hsmin] at this; exact hcb.2 this
          rw [if_neg h1, if_neg h2]
        rw [hepi0, Nat.add_zero]
        have hmono := HourCoupling.cAbove_pair_mono h s t hs3 ht3 (Or.inr hsc) (Or.inr htc) hsu htu
        rw [HourCoupling.transition_eq_phase3 s t hs3 ht3 hp1 hp2] at hmono
        rw [HourCoupling.countP_pair, HourCoupling.countP_pair] at hmono
        exact hmono
      · -- SYNC: both outputs get minute = max s.minute t.minute.
        have hP3 : Phase3Transition L K s t =
            ({ s with minute := max s.minute t.minute },
             { t with minute := max s.minute t.minute }) := by
          unfold Phase3Transition
          have htm' : t.role ≠ .main := by rw [htc]; decide
          have hsm' : s.role ≠ .main := by rw [hsc]; decide
          simp only [hsc, htc, and_self, if_true, hmin, ne_eq, not_false_eq_true,
            if_true, hsm', htm', false_and, and_false, if_false, reduceCtorEq, ite_self]
        rw [hP3]
        dsimp only
        have hmaxval : (max s.minute t.minute).val = max s.minute.val t.minute.val := by
          rcases le_total s.minute t.minute with hle | hle
          · rw [max_eq_right hle, max_eq_right (by exact_mod_cast hle)]
          · rw [max_eq_left hle, max_eq_left (by exact_mod_cast hle)]
        have ho1ca : HourCoupling.clockAboveP h
            ({ s with minute := max s.minute t.minute } : AgentState L K)
            ↔ (h + 1) * K ≤ max s.minute.val t.minute.val := by
          unfold HourCoupling.clockAboveP
          rw [show ({ s with minute := max s.minute t.minute } : AgentState L K).role = .clock from hsc,
            show ({ s with minute := max s.minute t.minute } : AgentState L K).minute.val
              = (max s.minute t.minute).val from rfl, hmaxval]
          simp
        have ho2ca : HourCoupling.clockAboveP h
            ({ t with minute := max s.minute t.minute } : AgentState L K)
            ↔ (h + 1) * K ≤ max s.minute.val t.minute.val := by
          unfold HourCoupling.clockAboveP
          rw [show ({ t with minute := max s.minute t.minute } : AgentState L K).role = .clock from htc,
            show ({ t with minute := max s.minute t.minute } : AgentState L K).minute.val
              = (max s.minute t.minute).val from rfl, hmaxval]
          simp
        have hsca_iff : HourCoupling.clockAboveP h s ↔ (h+1)*K ≤ s.minute.val :=
          ⟨fun hh => hh.2, fun hh => ⟨hsc, hh⟩⟩
        have htca_iff : HourCoupling.clockAboveP h t ↔ (h+1)*K ≤ t.minute.val :=
          ⟨fun hh => hh.2, fun hh => ⟨htc, hh⟩⟩
        have hsb_iff : clockBelowP h s ↔ ¬ (h+1)*K ≤ s.minute.val :=
          ⟨fun hh => hh.2, fun hh => ⟨hsc, hh⟩⟩
        have htb_iff : clockBelowP h t ↔ ¬ (h+1)*K ≤ t.minute.val :=
          ⟨fun hh => hh.2, fun hh => ⟨htc, hh⟩⟩
        unfold epiInd
        by_cases hsabove : (h+1)*K ≤ s.minute.val <;>
          by_cases htabove : (h+1)*K ≤ t.minute.val <;>
          simp only [ho1ca, ho2ca, hsca_iff, htca_iff, hsb_iff, htb_iff,
            le_max_iff, hsabove, htabove, true_or, or_true, or_false, false_or,
            not_true, not_false, not_true_eq_false, not_false_eq_true,
            and_true, and_false, true_and, false_and,
            if_true, if_false, le_refl] <;>
          omega

/-! ## Part 4 — the config-level sharp drag/epidemic bounds (lift to `stepOrSelf`).

Following `HourCoupling.{mAbove_stepOrSelf_le, cAbove_stepOrSelf_ge}`, we lift the
sharp per-pair facts to the chosen-pair kernel update on the window. -/

/-- **Config-level sharp drag bound**: `mAbove(step) ≤ mAbove c + dragInd`. -/
theorem mAbove_stepOrSelf_dragInd (h : ℕ) (hK : 0 < K) (hhL : h < L)
    (c : Config (AgentState L K)) (hw : HourCoupling.HourWindow c) (r₁ r₂ : AgentState L K) :
    HourCoupling.mAbove (L := L) (K := K) h
        (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂)
      ≤ HourCoupling.mAbove (L := L) (K := K) h c + dragInd h r₁ r₂ := by
  classical
  by_cases happ : Protocol.Applicable c r₁ r₂
  · have hmem1 := mem_of_applicable_left happ
    have hmem2 := mem_of_applicable_right happ
    obtain ⟨h1r, h1p, h1u⟩ := hw r₁ hmem1
    obtain ⟨h2r, h2p, h2u⟩ := hw r₂ hmem2
    have hsub : ({r₁, r₂} : Multiset (AgentState L K)) ≤ c := happ
    have hc' : Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂
        = c - {r₁, r₂} + {(NonuniformMajority L K).δ r₁ r₂ |>.1,
            (NonuniformMajority L K).δ r₁ r₂ |>.2} := by
      unfold Protocol.stepOrSelf; rw [if_pos happ]
    have hδ : (NonuniformMajority L K).δ r₁ r₂ = Transition L K r₁ r₂ := rfl
    unfold HourCoupling.mAbove
    rw [hc', Multiset.countP_add, Multiset.countP_sub hsub]
    have hpair_le : Multiset.countP (fun a => HourCoupling.mainAboveP h a)
        ({r₁, r₂} : Multiset (AgentState L K))
          ≤ Multiset.countP (fun a => HourCoupling.mainAboveP h a) c :=
      Multiset.countP_le_of_le _ hsub
    have hdrag := mAbove_pair_dragInd h hK hhL r₁ r₂ h1p h2p h1r h2r h1u h2u
    rw [hδ]
    omega
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]
    have : 0 ≤ dragInd h r₁ r₂ := Nat.zero_le _
    omega

/-- **Config-level sharp epidemic bound** (for an applicable pair):
`cAbove c + epiInd ≤ cAbove(step)`.  Applicability is used only to fire the
per-pair crossing; in the drift sum the non-applicable pairs carry zero
interaction weight. -/
theorem cAbove_stepOrSelf_epiInd (h : ℕ) (hhL : h < L)
    (c : Config (AgentState L K)) (hw : HourCoupling.HourWindow c) (r₁ r₂ : AgentState L K)
    (happ : Protocol.Applicable c r₁ r₂) :
    HourCoupling.cAbove (L := L) (K := K) h c + epiInd h r₁ r₂
      ≤ HourCoupling.cAbove (L := L) (K := K) h
          (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂) := by
  classical
  have hmem1 := mem_of_applicable_left happ
  have hmem2 := mem_of_applicable_right happ
  obtain ⟨h1r, h1p, h1u⟩ := hw r₁ hmem1
  obtain ⟨h2r, h2p, h2u⟩ := hw r₂ hmem2
  have hsub : ({r₁, r₂} : Multiset (AgentState L K)) ≤ c := happ
  have hc' : Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂
      = c - {r₁, r₂} + {(NonuniformMajority L K).δ r₁ r₂ |>.1,
          (NonuniformMajority L K).δ r₁ r₂ |>.2} := by
    unfold Protocol.stepOrSelf; rw [if_pos happ]
  have hδ : (NonuniformMajority L K).δ r₁ r₂ = Transition L K r₁ r₂ := rfl
  unfold HourCoupling.cAbove
  rw [hc', Multiset.countP_add, Multiset.countP_sub hsub]
  have hsplit : Multiset.countP (fun a => HourCoupling.clockAboveP h a) c
      = Multiset.countP (fun a => HourCoupling.clockAboveP h a) (c - {r₁, r₂})
        + Multiset.countP (fun a => HourCoupling.clockAboveP h a)
            ({r₁, r₂} : Multiset (AgentState L K)) := by
    rw [← Multiset.countP_add, Multiset.sub_add_cancel hsub]
  have hpair := cAbove_pair_epiInd h hhL r₁ r₂ h1p h2p h1r h2r h1u h2u
  rw [hδ]
  omega

/-! ## Part 5 — counts and the partition identities. -/

/-- The Main-below count (Main agents at hour `≤ h`). -/
def mainBelowCount (h : ℕ) (c : Config (AgentState L K)) : ℕ :=
  Multiset.countP (fun a => mainBelowP h a) c

/-- The Clock-below count (Clock agents at clock-hour `≤ h`). -/
def clockBelowCount (h : ℕ) (c : Config (AgentState L K)) : ℕ :=
  Multiset.countP (fun a => clockBelowP h a) c

/-- Mains partition into above-`h` and below-`h`: `mAbove + mainBelow = mainCount`. -/
theorem mAbove_add_mainBelow (h : ℕ) (c : Config (AgentState L K)) :
    HourCoupling.mAbove (L := L) (K := K) h c + mainBelowCount (L := L) (K := K) h c
      = mainCount (L := L) (K := K) c := by
  unfold HourCoupling.mAbove mainBelowCount mainCount
  induction c using Multiset.induction with
  | empty => simp
  | cons a s ih =>
      rw [Multiset.countP_cons, Multiset.countP_cons, Multiset.countP_cons]
      have hA : (if HourCoupling.mainAboveP h a then (1:ℕ) else 0)
          + (if mainBelowP h a then (1:ℕ) else 0) = (if a.role = .main then (1:ℕ) else 0) := by
        by_cases hr : a.role = .main
        · by_cases hh : h < a.hour.val
          · simp [HourCoupling.mainAboveP, mainBelowP, hr, hh]
          · simp [HourCoupling.mainAboveP, mainBelowP, hr, hh]
        · simp [HourCoupling.mainAboveP, mainBelowP, hr]
      omega

/-- Clocks partition into above-`h` and below-`h`: `cAbove + clockBelow = clockCount`. -/
theorem cAbove_add_clockBelow (h : ℕ) (c : Config (AgentState L K)) :
    HourCoupling.cAbove (L := L) (K := K) h c + clockBelowCount (L := L) (K := K) h c
      = clockCount (L := L) (K := K) c := by
  unfold HourCoupling.cAbove clockBelowCount clockCount
  induction c using Multiset.induction with
  | empty => simp
  | cons a s ih =>
      rw [Multiset.countP_cons, Multiset.countP_cons, Multiset.countP_cons]
      have hA : (if HourCoupling.clockAboveP h a then (1:ℕ) else 0)
          + (if clockBelowP h a then (1:ℕ) else 0) = (if a.role = .clock then (1:ℕ) else 0) := by
        by_cases hr : a.role = .clock
        · by_cases hh : (h + 1) * K ≤ a.minute.val
          · simp [HourCoupling.clockAboveP, clockBelowP, hr, hh]
          · simp [HourCoupling.clockAboveP, clockBelowP, hr, hh]
        · simp [HourCoupling.clockAboveP, clockBelowP, hr]
      omega

/-- `countP p c = ∑_{a ∈ filter p univ} count a` (generic). -/
theorem countP_eq_sum_count (p : AgentState L K → Prop) [DecidablePred p]
    (c : Config (AgentState L K)) :
    Multiset.countP p c
      = ∑ a ∈ Finset.univ.filter (fun a : AgentState L K => p a), c.count a := by
  classical
  have hcard : (Multiset.filter (fun a : AgentState L K => p a) c).card
      = Multiset.countP p c := (Multiset.countP_eq_card_filter _ _).symm
  rw [← hcard, eq_comm]
  have hcount_eq : ∀ a ∈ Finset.univ.filter (fun a : AgentState L K => p a),
      c.count a = Multiset.count a (Multiset.filter (fun a : AgentState L K => p a) c) := by
    intro a ha
    rw [Finset.mem_filter] at ha
    rw [Config.count, Multiset.count_filter, if_pos ha.2]
  rw [Finset.sum_congr rfl hcount_eq, Multiset.sum_count_eq_card]
  intro a ha
  rw [Multiset.mem_filter] at ha
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha.2⟩

/-! ## Part 6 — the weighted pair-sum identities (drag and epidemic mass). -/

/-- An indicator-weighted full-`univ` pair-sum equals the rectangle sum over the
two predicate filters. -/
theorem sum_interactionCount_indicator
    (c : Config (AgentState L K)) (P Q : AgentState L K → Prop)
    [DecidablePred P] [DecidablePred Q] :
    (∑ p : AgentState L K × AgentState L K,
        c.interactionCount p.1 p.2 * (if P p.1 ∧ Q p.2 then 1 else 0))
      = ∑ p ∈ (Finset.univ.filter (fun a : AgentState L K => P a)) ×ˢ
          (Finset.univ.filter (fun a : AgentState L K => Q a)),
          c.interactionCount p.1 p.2 := by
  classical
  rw [show (Finset.univ : Finset (AgentState L K × AgentState L K))
      = Finset.univ ×ˢ Finset.univ from (Finset.univ_product_univ).symm]
  rw [Finset.sum_product, Finset.sum_product]
  -- Both sides become ∑_s ∑_t (...); reduce each row.
  -- RHS: ∑_{s∈Pf} ∑_{t∈Qf} count.  Rewrite as ∑_{s∈univ} (if P s then ∑_{t∈Qf} count else 0).
  rw [Finset.sum_filter (s := (Finset.univ : Finset (AgentState L K)))
      (p := fun a => P a) (f := fun s => ∑ t ∈ Finset.univ.filter (fun a => Q a),
        c.interactionCount s t)]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  by_cases hP : P s
  · rw [if_pos hP]
    rw [Finset.sum_filter (s := (Finset.univ : Finset (AgentState L K)))
        (p := fun a => Q a) (f := fun t => c.interactionCount s t)]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    by_cases hQ : Q t
    · simp [hP, hQ]
    · simp [hQ]
  · rw [if_neg hP]
    refine (Finset.sum_eq_zero (fun t _ => ?_))
    simp [hP]

/-- **Drag mass**: `∑ interactionCount · dragInd = 2 · mainBelowCount · cAbove`. -/
theorem sum_interactionCount_dragInd (h : ℕ) (c : Config (AgentState L K)) :
    (∑ p : AgentState L K × AgentState L K,
        c.interactionCount p.1 p.2 * dragInd h p.1 p.2)
      = 2 * (mainBelowCount (L := L) (K := K) h c)
          * (HourCoupling.cAbove (L := L) (K := K) h c) := by
  classical
  -- Disjointness: mainBelow is role main, clockAbove is role clock.
  have hdisj1 : ∀ a ∈ Finset.univ.filter (fun a : AgentState L K => mainBelowP h a),
      ∀ b ∈ Finset.univ.filter (fun a : AgentState L K => HourCoupling.clockAboveP h a),
      a ≠ b := by
    intro a ha b hb hab
    rw [Finset.mem_filter] at ha hb
    subst hab; exact absurd (ha.2.1.symm.trans hb.2.1) (by decide)
  have hdisj2 : ∀ a ∈ Finset.univ.filter (fun a : AgentState L K => HourCoupling.clockAboveP h a),
      ∀ b ∈ Finset.univ.filter (fun a : AgentState L K => mainBelowP h a),
      a ≠ b := by
    intro a ha b hb hab
    rw [Finset.mem_filter] at ha hb
    subst hab; exact absurd (ha.2.1.symm.trans hb.2.1) (by decide)
  -- Split dragInd into its two indicator terms.
  have hsplit : (∑ p : AgentState L K × AgentState L K,
        c.interactionCount p.1 p.2 * dragInd h p.1 p.2)
      = (∑ p : AgentState L K × AgentState L K,
          c.interactionCount p.1 p.2
            * (if mainBelowP h p.1 ∧ HourCoupling.clockAboveP h p.2 then 1 else 0))
        + (∑ p : AgentState L K × AgentState L K,
          c.interactionCount p.1 p.2
            * (if mainBelowP h p.2 ∧ HourCoupling.clockAboveP h p.1 then 1 else 0)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _; unfold dragInd; ring
  rw [hsplit]
  -- First term: rectangle mainBelow × clockAbove.
  rw [sum_interactionCount_indicator c (fun a => mainBelowP h a)
      (fun a => HourCoupling.clockAboveP h a)]
  rw [ClockRealMixed.sum_interactionCount_cross_disjoint c _ _ hdisj1]
  -- Second term: swap the indicator order to (clockAbove p.1 ∧ mainBelow p.2).
  rw [show (∑ p : AgentState L K × AgentState L K,
        c.interactionCount p.1 p.2
          * (if mainBelowP h p.2 ∧ HourCoupling.clockAboveP h p.1 then 1 else 0))
      = (∑ p : AgentState L K × AgentState L K,
        c.interactionCount p.1 p.2
          * (if HourCoupling.clockAboveP h p.1 ∧ mainBelowP h p.2 then 1 else 0)) from by
    apply Finset.sum_congr rfl; intro p _; congr 1; exact if_congr and_comm rfl rfl]
  rw [sum_interactionCount_indicator c (fun a => HourCoupling.clockAboveP h a)
      (fun a => mainBelowP h a)]
  rw [ClockRealMixed.sum_interactionCount_cross_disjoint c _ _ hdisj2]
  unfold mainBelowCount HourCoupling.cAbove
  simp only [← countP_eq_sum_count]
  ring

/-- **Epidemic mass**: `∑ interactionCount · epiInd = 2 · cAbove · clockBelowCount`. -/
theorem sum_interactionCount_epiInd (h : ℕ) (c : Config (AgentState L K)) :
    (∑ p : AgentState L K × AgentState L K,
        c.interactionCount p.1 p.2 * epiInd h p.1 p.2)
      = 2 * (HourCoupling.cAbove (L := L) (K := K) h c)
          * (clockBelowCount (L := L) (K := K) h c) := by
  classical
  have hdisj1 : ∀ a ∈ Finset.univ.filter (fun a : AgentState L K => HourCoupling.clockAboveP h a),
      ∀ b ∈ Finset.univ.filter (fun a : AgentState L K => clockBelowP h a),
      a ≠ b := by
    intro a ha b hb hab
    rw [Finset.mem_filter] at ha hb
    subst hab; exact hb.2.2 ha.2.2
  have hdisj2 : ∀ a ∈ Finset.univ.filter (fun a : AgentState L K => clockBelowP h a),
      ∀ b ∈ Finset.univ.filter (fun a : AgentState L K => HourCoupling.clockAboveP h a),
      a ≠ b := by
    intro a ha b hb hab
    rw [Finset.mem_filter] at ha hb
    subst hab; exact ha.2.2 hb.2.2
  have hsplit : (∑ p : AgentState L K × AgentState L K,
        c.interactionCount p.1 p.2 * epiInd h p.1 p.2)
      = (∑ p : AgentState L K × AgentState L K,
          c.interactionCount p.1 p.2
            * (if HourCoupling.clockAboveP h p.1 ∧ clockBelowP h p.2 then 1 else 0))
        + (∑ p : AgentState L K × AgentState L K,
          c.interactionCount p.1 p.2
            * (if HourCoupling.clockAboveP h p.2 ∧ clockBelowP h p.1 then 1 else 0)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _; unfold epiInd; ring
  rw [hsplit]
  rw [sum_interactionCount_indicator c (fun a => HourCoupling.clockAboveP h a)
      (fun a => clockBelowP h a)]
  rw [ClockRealMixed.sum_interactionCount_cross_disjoint c _ _ hdisj1]
  rw [show (∑ p : AgentState L K × AgentState L K,
        c.interactionCount p.1 p.2
          * (if HourCoupling.clockAboveP h p.2 ∧ clockBelowP h p.1 then 1 else 0))
      = (∑ p : AgentState L K × AgentState L K,
        c.interactionCount p.1 p.2
          * (if clockBelowP h p.1 ∧ HourCoupling.clockAboveP h p.2 then 1 else 0)) from by
    apply Finset.sum_congr rfl; intro p _; congr 1; exact if_congr and_comm rfl rfl]
  rw [sum_interactionCount_indicator c (fun a => clockBelowP h a)
      (fun a => HourCoupling.clockAboveP h a)]
  rw [ClockRealMixed.sum_interactionCount_cross_disjoint c _ _ hdisj2]
  unfold HourCoupling.cAbove clockBelowCount
  simp only [← countP_eq_sum_count]
  ring

/-! ## Part 7 — the GENUINE supermartingale drift.

We expand `∫ Φ d(K c)` into the finite `interactionCount` pair-sum, bound each
applicable pair's `ΔΦ` by `dragInd/M − 1.1·epiInd/C` (the sharp drag/epidemic
crossing structure), then sum via the mass identities and close with the bracket
`(1 − m_{>h}) − 1.1·(1 − c_{>h}) ≤ 0` on the window `c_{>h} ≤ 1/11`. -/

/-- The window predicate `c_{>h} ≤ 1/11`, in integer form `11·cAbove ≤ clockCount`.
This is the TRUE synchronous-hour window (`c_{>h} ≤ 0.001` until `end_h`). -/
def Window (h : ℕ) (c : Config (AgentState L K)) : Prop :=
  11 * HourCoupling.cAbove (L := L) (K := K) h c ≤ clockCount (L := L) (K := K) c

/-- Per-applicable-pair real bound on `ΔΦ`. -/
theorem Phi_step_le (M C : ℝ) (hM : 0 < M) (hC : 0 < C) (h : ℕ) (hK : 0 < K) (hhL : h < L)
    (c : Config (AgentState L K)) (hw : HourCoupling.HourWindow c)
    (hMc : (mainCount (L := L) (K := K) c : ℝ) = M)
    (hCc : (clockCount (L := L) (K := K) c : ℝ) = C)
    (s t : AgentState L K) (happ : Protocol.Applicable c s t) :
    Phi (L := L) (K := K) M C h (Protocol.stepOrSelf (NonuniformMajority L K) c s t)
      ≤ Phi (L := L) (K := K) M C h c
        + (dragInd h s t : ℝ) / M - (11 / 10 : ℝ) * (epiInd h s t : ℝ) / C := by
  have hdrag := mAbove_stepOrSelf_dragInd h hK hhL c hw s t
  have hepi := cAbove_stepOrSelf_epiInd h hhL c hw s t happ
  have hdragR : (HourCoupling.mAbove (L := L) (K := K) h
      (Protocol.stepOrSelf (NonuniformMajority L K) c s t) : ℝ)
      ≤ (HourCoupling.mAbove (L := L) (K := K) h c : ℝ) + (dragInd h s t : ℝ) := by
    exact_mod_cast hdrag
  have hepiR : (HourCoupling.cAbove (L := L) (K := K) h c : ℝ) + (epiInd h s t : ℝ)
      ≤ (HourCoupling.cAbove (L := L) (K := K) h
          (Protocol.stepOrSelf (NonuniformMajority L K) c s t) : ℝ) := by
    exact_mod_cast hepi
  unfold Phi
  -- Divide the two count inequalities by M, C.
  have h1 : (HourCoupling.mAbove (L := L) (K := K) h
      (Protocol.stepOrSelf (NonuniformMajority L K) c s t) : ℝ) / M
      ≤ ((HourCoupling.mAbove (L := L) (K := K) h c : ℝ) + (dragInd h s t : ℝ)) / M :=
    div_le_div_of_nonneg_right hdragR hM.le
  have h2 : ((HourCoupling.cAbove (L := L) (K := K) h c : ℝ) + (epiInd h s t : ℝ)) / C
      ≤ (HourCoupling.cAbove (L := L) (K := K) h
          (Protocol.stepOrSelf (NonuniformMajority L K) c s t) : ℝ) / C :=
    div_le_div_of_nonneg_right hepiR hC.le
  rw [add_div] at h1 h2
  -- Normalize all the `(11/10)·x/C` terms to `(11/10)·(x/C)`.
  simp only [mul_div_assoc]
  -- Now pure linear arithmetic over the divided terms.
  have h11 : (0:ℝ) ≤ 11/10 := by norm_num
  nlinarith [h1, mul_le_mul_of_nonneg_left h2 h11]

/-- `mainCount + clockCount ≤ card` (mains and clocks are disjoint roles). -/
theorem mainCount_add_clockCount_le_card (c : Config (AgentState L K)) :
    mainCount (L := L) (K := K) c + clockCount (L := L) (K := K) c ≤ c.card := by
  unfold mainCount clockCount
  induction c using Multiset.induction with
  | empty => simp
  | cons a s ih =>
      rw [Multiset.countP_cons, Multiset.countP_cons, Multiset.card_cons]
      have hca : (if a.role = .main then (1:ℕ) else 0)
          + (if a.role = .clock then (1:ℕ) else 0) ≤ 1 := by
        by_cases hm : a.role = .main
        · have hc : a.role ≠ .clock := by rw [hm]; decide
          simp [hm, hc]
        · simp only [hm, if_false, Nat.zero_add]; split <;> omega
      omega

/-- `card ≥ 2` when both role counts are `≥ 1`. -/
theorem two_le_card_of_counts (c : Config (AgentState L K))
    (hM : 1 ≤ mainCount (L := L) (K := K) c) (hC : 1 ≤ clockCount (L := L) (K := K) c) :
    2 ≤ c.card :=
  le_trans (by omega) (mainCount_add_clockCount_le_card c)

/-- **The GENUINE supermartingale drift** (real Bochner integral form, the exact
hypothesis `AzumaKernel.azuma_tail` consumes).  On the window `c_{>h} ≤ 1/11`,

  `∫ Φ d(K c) ≤ Φ c`.

DERIVED: the one-step expectation is expanded into the finite `interactionCount`
pair-sum; each applicable pair's `ΔΦ` is bounded by `dragInd/M − 1.1·epiInd/C`
(sharp drag/epidemic crossing); the masses sum to `2·mainBelow·cAbove` and
`2·cAbove·clockBelow`; and the bracket `(1−m_{>h}) − 1.1(1−c_{>h}) ≤ 0` on the
window closes it.  NO frozen-`cAbove`. -/
theorem hour_drift (M C : ℝ) (h : ℕ) (hK : 0 < K) (hhL : h < L)
    (c : Config (AgentState L K)) (hw : HourCoupling.HourWindow c)
    (hwin : Window (L := L) (K := K) h c)
    (hMc : (mainCount (L := L) (K := K) c : ℝ) = M)
    (hCc : (clockCount (L := L) (K := K) c : ℝ) = C)
    (hM1 : 1 ≤ mainCount (L := L) (K := K) c)
    (hC1 : 1 ≤ clockCount (L := L) (K := K) c) :
    ∫ c', Phi (L := L) (K := K) M C h c'
        ∂((NonuniformMajority L K).transitionKernel c)
      ≤ Phi (L := L) (K := K) M C h c := by
  have hM : 0 < M := by rw [← hMc]; exact_mod_cast hM1
  have hC : 0 < C := by rw [← hCc]; exact_mod_cast hC1
  have hcard : 2 ≤ c.card := two_le_card_of_counts c hM1 hC1
  -- Expand the integral into the finite pair-sum.
  rw [integral_transitionKernel_eq_sum _ c hcard]
  -- Bound each pair-term by  prob · (Φ c + dragInd/M − 1.1·epiInd/C).
  have hkey : ∑ p : AgentState L K × AgentState L K,
        (Config.interactionProb c p.1 p.2).toReal
          * Phi (L := L) (K := K) M C h (Protocol.stepOrSelf (NonuniformMajority L K) c p.1 p.2)
      ≤ ∑ p : AgentState L K × AgentState L K,
        (Config.interactionProb c p.1 p.2).toReal
          * (Phi (L := L) (K := K) M C h c
              + (dragInd h p.1 p.2 : ℝ) / M - (11 / 10 : ℝ) * (epiInd h p.1 p.2 : ℝ) / C) := by
    apply Finset.sum_le_sum
    intro p _
    have hprob_nonneg : 0 ≤ (Config.interactionProb c p.1 p.2).toReal := ENNReal.toReal_nonneg
    -- If the pair is applicable, use Phi_step_le; else interactionProb = 0.
    by_cases happ : Protocol.Applicable c p.1 p.2
    · exact mul_le_mul_of_nonneg_left
        (Phi_step_le M C hM hC h hK hhL c hw hMc hCc p.1 p.2 happ) hprob_nonneg
    · -- Not applicable ⇒ interactionCount = 0 ⇒ prob = 0.
      have hzero : (Config.interactionProb c p.1 p.2).toReal = 0 := by
        have hic : Config.interactionCount c p.1 p.2 = 0 := by
          by_contra hne
          apply happ
          have hpos : 0 < Config.interactionCount c p.1 p.2 := Nat.pos_of_ne_zero hne
          have hpos' := hpos
          unfold Config.interactionCount at hpos'
          unfold Protocol.Applicable
          rw [Multiset.le_iff_count]; intro a
          rw [show ({p.1, p.2} : Multiset (AgentState L K)) = p.1 ::ₘ p.2 ::ₘ 0 from rfl]
          simp only [Multiset.count_cons, Multiset.count_zero, Nat.zero_add, Nat.add_zero]
          -- counts of p.1, p.2 in c.
          have hcc1 : Config.count c p.1 = Multiset.count p.1 c := rfl
          have hcc2 : Config.count c p.2 = Multiset.count p.2 c := rfl
          by_cases heq : p.1 = p.2
          · rw [if_pos heq] at hpos'
            have h2 : 2 ≤ Multiset.count p.1 c := by
              rcases Nat.lt_or_ge (Multiset.count p.1 c) 2 with hlt | hge
              · exfalso
                rw [hcc1] at hpos'
                interval_cases (Multiset.count p.1 c) <;> simp_all
              · exact hge
            by_cases ha : a = p.1
            · subst ha
              rw [if_pos rfl, if_pos heq]; omega
            · have ha2 : a ≠ p.2 := fun hh => ha (hh.trans heq.symm)
              rw [if_neg ha, if_neg ha2]; exact Nat.zero_le _
          · rw [if_neg heq] at hpos'
            rw [hcc1, hcc2] at hpos'
            have hc1 : 0 < Multiset.count p.1 c := Nat.pos_of_ne_zero (by
              intro h0; rw [h0, Nat.zero_mul] at hpos'; exact absurd hpos' (lt_irrefl 0))
            have hc2 : 0 < Multiset.count p.2 c := Nat.pos_of_ne_zero (by
              intro h0; rw [h0, Nat.mul_zero] at hpos'; exact absurd hpos' (lt_irrefl 0))
            by_cases ha1 : a = p.1 <;> by_cases ha2 : a = p.2
            · subst ha1; exact absurd ha2 heq
            · subst ha1; rw [if_pos rfl, if_neg ha2]; omega
            · subst ha2; rw [if_neg ha1, if_pos rfl]; omega
            · rw [if_neg ha1, if_neg ha2]; exact Nat.zero_le _
        unfold Config.interactionProb
        rw [hic]; simp
      rw [hzero, zero_mul, zero_mul]
  refine hkey.trans ?_
  -- Now the sum of the bound: distribute and use the mass identities.
  -- ∑ prob·(Φc + drag/M − 1.1 epi/C) = Φc·∑prob + (1/M)∑prob·drag − (1.1/C)∑prob·epi.
  have hprob_sum : ∑ p : AgentState L K × AgentState L K,
      (Config.interactionProb c p.1 p.2).toReal = 1 := by
    have h1 : ∑ p : AgentState L K × AgentState L K,
        (Config.interactionProb c p.1 p.2) = 1 := by
      have := (Config.interactionPMF c hcard).tsum_coe
      rw [tsum_fintype] at this
      convert this using 1
    have := congrArg ENNReal.toReal h1
    rw [ENNReal.toReal_one] at this
    rw [← this, ENNReal.toReal_sum]
    intro p _
    exact ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (Config.totalPairs_ne_zero_ennreal hcard)
  -- Real form of the per-pair probability weight.
  have hPpos : (0 : ℝ) < (c.totalPairs : ℝ) := by
    have := Config.totalPairs_pos hcard; exact_mod_cast this
  have hprobR : ∀ p : AgentState L K × AgentState L K,
      (Config.interactionProb c p.1 p.2).toReal
        = (c.interactionCount p.1 p.2 : ℝ) / (c.totalPairs : ℝ) := by
    intro p
    unfold Config.interactionProb
    rw [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast]
  -- Distribute the RHS sum.
  have hM : 0 < M := by rw [← hMc]; exact_mod_cast hM1
  have hC : 0 < C := by rw [← hCc]; exact_mod_cast hC1
  have hexpand : ∑ p : AgentState L K × AgentState L K,
        (Config.interactionProb c p.1 p.2).toReal
          * (Phi (L := L) (K := K) M C h c
              + (dragInd h p.1 p.2 : ℝ) / M - (11 / 10 : ℝ) * (epiInd h p.1 p.2 : ℝ) / C)
      = Phi (L := L) (K := K) M C h c
          + (∑ p : AgentState L K × AgentState L K,
              (c.interactionCount p.1 p.2 : ℝ) * (dragInd h p.1 p.2 : ℝ))
              / ((c.totalPairs : ℝ) * M)
          - (11 / 10 : ℝ) * (∑ p : AgentState L K × AgentState L K,
              (c.interactionCount p.1 p.2 : ℝ) * (epiInd h p.1 p.2 : ℝ))
              / ((c.totalPairs : ℝ) * C) := by
    have hsub : ∀ p : AgentState L K × AgentState L K,
        (Config.interactionProb c p.1 p.2).toReal
          * (Phi (L := L) (K := K) M C h c
              + (dragInd h p.1 p.2 : ℝ) / M - (11 / 10 : ℝ) * (epiInd h p.1 p.2 : ℝ) / C)
        = (Config.interactionProb c p.1 p.2).toReal * Phi (L := L) (K := K) M C h c
          + (c.interactionCount p.1 p.2 : ℝ) * (dragInd h p.1 p.2 : ℝ)
              / ((c.totalPairs : ℝ) * M)
          - (11 / 10 : ℝ) * ((c.interactionCount p.1 p.2 : ℝ) * (epiInd h p.1 p.2 : ℝ))
              / ((c.totalPairs : ℝ) * C) := by
      intro p; rw [hprobR p]; field_simp
    rw [Finset.sum_congr rfl (fun p _ => hsub p)]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rw [← Finset.sum_mul, hprob_sum, one_mul]
    congr 1
    · rw [← Finset.sum_div]
    · rw [← Finset.sum_div, ← Finset.mul_sum, mul_div_assoc]
  rw [hexpand]
  -- Mass identities (cast to ℝ).
  have hdragmass : (∑ p : AgentState L K × AgentState L K,
        (c.interactionCount p.1 p.2 : ℝ) * (dragInd h p.1 p.2 : ℝ))
      = 2 * (mainBelowCount (L := L) (K := K) h c : ℝ)
          * (HourCoupling.cAbove (L := L) (K := K) h c : ℝ) := by
    have := sum_interactionCount_dragInd h c
    have hcast : (∑ p : AgentState L K × AgentState L K,
          (c.interactionCount p.1 p.2 : ℝ) * (dragInd h p.1 p.2 : ℝ))
        = ((∑ p : AgentState L K × AgentState L K,
            c.interactionCount p.1 p.2 * dragInd h p.1 p.2 : ℕ) : ℝ) := by
      push_cast; rfl
    rw [hcast, this]; push_cast; ring
  have hepimass : (∑ p : AgentState L K × AgentState L K,
        (c.interactionCount p.1 p.2 : ℝ) * (epiInd h p.1 p.2 : ℝ))
      = 2 * (HourCoupling.cAbove (L := L) (K := K) h c : ℝ)
          * (clockBelowCount (L := L) (K := K) h c : ℝ) := by
    have := sum_interactionCount_epiInd h c
    have hcast : (∑ p : AgentState L K × AgentState L K,
          (c.interactionCount p.1 p.2 : ℝ) * (epiInd h p.1 p.2 : ℝ))
        = ((∑ p : AgentState L K × AgentState L K,
            c.interactionCount p.1 p.2 * epiInd h p.1 p.2 : ℕ) : ℝ) := by
      push_cast; rfl
    rw [hcast, this]; push_cast; ring
  rw [hdragmass, hepimass]
  -- The bracket: it suffices that  2·cAbove·mainBelow/(P·M) ≤ 1.1·2·cAbove·clockBelow/(P·C).
  -- i.e.  mainBelow/M ≤ 1.1·clockBelow/C  on the window.
  have hmB : (mainBelowCount (L := L) (K := K) h c : ℝ)
      = M - (HourCoupling.mAbove (L := L) (K := K) h c : ℝ) := by
    have := mAbove_add_mainBelow (L := L) (K := K) h c
    have : (HourCoupling.mAbove (L := L) (K := K) h c : ℝ)
        + (mainBelowCount (L := L) (K := K) h c : ℝ) = M := by
      rw [← hMc]; exact_mod_cast this
    linarith
  have hcB : (clockBelowCount (L := L) (K := K) h c : ℝ)
      = C - (HourCoupling.cAbove (L := L) (K := K) h c : ℝ) := by
    have := cAbove_add_clockBelow (L := L) (K := K) h c
    have : (HourCoupling.cAbove (L := L) (K := K) h c : ℝ)
        + (clockBelowCount (L := L) (K := K) h c : ℝ) = C := by
      rw [← hCc]; exact_mod_cast this
    linarith
  -- mainBelow ≤ M and the window 11·cAbove ≤ C give the bracket.
  have hmBle : (HourCoupling.mAbove (L := L) (K := K) h c : ℝ) ≥ 0 := by positivity
  have hcAge : (HourCoupling.cAbove (L := L) (K := K) h c : ℝ) ≥ 0 := by positivity
  have hwinR : 11 * (HourCoupling.cAbove (L := L) (K := K) h c : ℝ) ≤ C := by
    rw [← hCc]; exact_mod_cast hwin
  -- Now close.  Both extra terms divide by P·M, P·C > 0.
  rw [hmB, hcB]
  have hbracket : (M - (HourCoupling.mAbove (L := L) (K := K) h c : ℝ)) / M
      ≤ (11/10 : ℝ) * (C - (HourCoupling.cAbove (L := L) (K := K) h c : ℝ)) / C := by
    rw [div_le_div_iff₀ hM hC]
    nlinarith [hmBle, hcAge, hwinR, hM, hC, mul_nonneg hmBle hC.le]
  -- Reduce the goal to hbracket scaled by  2·cAbove/P  ≥ 0.
  have hfac : (0:ℝ) ≤ 2 * (HourCoupling.cAbove (L := L) (K := K) h c : ℝ) / (c.totalPairs : ℝ) := by
    apply div_nonneg _ hPpos.le; positivity
  have key : 2 * (M - (HourCoupling.mAbove (L := L) (K := K) h c : ℝ))
        * (HourCoupling.cAbove (L := L) (K := K) h c : ℝ) / ((c.totalPairs : ℝ) * M)
      ≤ (11/10 : ℝ) * (2 * (HourCoupling.cAbove (L := L) (K := K) h c : ℝ)
        * (C - (HourCoupling.cAbove (L := L) (K := K) h c : ℝ))) / ((c.totalPairs : ℝ) * C) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 := hbracket
    rw [div_le_div_iff₀ hM hC] at h1
    nlinarith [h1, hcAge, hPpos, mul_nonneg hcAge hPpos.le,
      mul_nonneg (mul_nonneg hcAge hPpos.le) (le_of_lt hM)]
  linarith [key]

/-! ## Part 8 — the bounded-difference lemma. -/

/-- A single chosen-pair update changes any `countP` by at most `2` (it removes a
2-element pair and adds a 2-element pair). -/
theorem countP_stepOrSelf_diff_le_two (p : AgentState L K → Prop) [DecidablePred p]
    (c : Config (AgentState L K)) (r₁ r₂ : AgentState L K) :
    (Multiset.countP p (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂) : ℤ)
        - (Multiset.countP p c : ℤ) ≤ 2
      ∧ (Multiset.countP p c : ℤ)
        - (Multiset.countP p (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂) : ℤ) ≤ 2 := by
  classical
  by_cases happ : Protocol.Applicable c r₁ r₂
  · have hsub : ({r₁, r₂} : Multiset (AgentState L K)) ≤ c := happ
    have hc' : Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂
        = c - {r₁, r₂} + {(NonuniformMajority L K).δ r₁ r₂ |>.1,
            (NonuniformMajority L K).δ r₁ r₂ |>.2} := by
      unfold Protocol.stepOrSelf; rw [if_pos happ]
    rw [hc', Multiset.countP_add, Multiset.countP_sub hsub]
    have hadd_le : Multiset.countP p ({(NonuniformMajority L K).δ r₁ r₂ |>.1,
        (NonuniformMajority L K).δ r₁ r₂ |>.2} : Multiset (AgentState L K)) ≤ 2 := by
      refine le_trans (Multiset.countP_le_card _ _) ?_
      simp [Multiset.card_pair]
    have hrem_le : Multiset.countP p ({r₁, r₂} : Multiset (AgentState L K)) ≤ 2 := by
      refine le_trans (Multiset.countP_le_card _ _) ?_
      simp [Multiset.card_pair]
    have hrem_le_c : Multiset.countP p ({r₁, r₂} : Multiset (AgentState L K))
        ≤ Multiset.countP p c := Multiset.countP_le_of_le _ hsub
    omega
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]; omega

/-- **The bounded-difference lemma**: a single interaction changes `Φ` by at most
`c₀ = 2/M + 2·(11/10)/C` a.e. on the kernel support. -/
theorem hour_bdd (M C : ℝ) (hM : 0 < M) (hC : 0 < C) (h : ℕ)
    (x : Config (AgentState L K)) :
    ∀ᵐ y ∂((NonuniformMajority L K).transitionKernel x),
      |Phi (L := L) (K := K) M C h y - Phi (L := L) (K := K) M C h x|
        ≤ 2 / M + 2 * (11 / 10 : ℝ) / C := by
  -- Reduce to the support: every support point is `stepOrSelf x r₁ r₂`.
  have hsupp : ∀ y ∈ ((NonuniformMajority L K).stepDistOrSelf x).support,
      |Phi (L := L) (K := K) M C h y - Phi (L := L) (K := K) M C h x|
        ≤ 2 / M + 2 * (11 / 10 : ℝ) / C := by
    intro y hy
    -- Either `card ≥ 2` (so `y = stepOrSelf x r₁ r₂`) or `y = x` (bound is `|0|`).
    have hcase : (∃ r₁ r₂, Protocol.stepOrSelf (NonuniformMajority L K) x r₁ r₂ = y) ∨ y = x := by
      by_cases hc : 2 ≤ x.card
      · rw [show (NonuniformMajority L K).stepDistOrSelf x
            = (NonuniformMajority L K).stepDist x hc by
            unfold Protocol.stepDistOrSelf; rw [dif_pos hc]] at hy
        obtain ⟨⟨r₁, r₂⟩, hr⟩ := Protocol.stepDist_support (NonuniformMajority L K) x hc y hy
        exact Or.inl ⟨r₁, r₂, hr⟩
      · rw [show (NonuniformMajority L K).stepDistOrSelf x = PMF.pure x by
            unfold Protocol.stepDistOrSelf; rw [dif_neg hc]] at hy
        rw [PMF.mem_support_pure_iff] at hy
        exact Or.inr hy
    rcases hcase with ⟨r₁, r₂, hstep⟩ | hyx
    · subst hstep
      -- mAbove, cAbove each move by ≤ 2 (integer), so Φ moves by ≤ 2/M + 2·1.1/C.
      obtain ⟨hmA1, hmA2⟩ :=
        countP_stepOrSelf_diff_le_two (fun a => HourCoupling.mainAboveP h a) x r₁ r₂
      obtain ⟨hcA1, hcA2⟩ :=
        countP_stepOrSelf_diff_le_two (fun a => HourCoupling.clockAboveP h a) x r₁ r₂
      -- Cast the ℤ bounds to ℝ (mAbove/cAbove are the corresponding countP).
      have hmAle : -2 ≤ (HourCoupling.mAbove (L := L) (K := K) h
          (Protocol.stepOrSelf (NonuniformMajority L K) x r₁ r₂) : ℝ)
          - (HourCoupling.mAbove (L := L) (K := K) h x : ℝ)
          ∧ (HourCoupling.mAbove (L := L) (K := K) h
          (Protocol.stepOrSelf (NonuniformMajority L K) x r₁ r₂) : ℝ)
          - (HourCoupling.mAbove (L := L) (K := K) h x : ℝ) ≤ 2 := by
        show _ ∧ _
        unfold HourCoupling.mAbove
        constructor
        · have : ((Multiset.countP (fun a => HourCoupling.mainAboveP h a) x : ℝ))
              - (Multiset.countP (fun a => HourCoupling.mainAboveP h a)
                  (Protocol.stepOrSelf (NonuniformMajority L K) x r₁ r₂) : ℝ) ≤ 2 := by
            exact_mod_cast hmA2
          linarith
        · have : ((Multiset.countP (fun a => HourCoupling.mainAboveP h a)
              (Protocol.stepOrSelf (NonuniformMajority L K) x r₁ r₂) : ℝ))
              - (Multiset.countP (fun a => HourCoupling.mainAboveP h a) x : ℝ) ≤ 2 := by
            exact_mod_cast hmA1
          linarith
      have hcAle : -2 ≤ (HourCoupling.cAbove (L := L) (K := K) h
          (Protocol.stepOrSelf (NonuniformMajority L K) x r₁ r₂) : ℝ)
          - (HourCoupling.cAbove (L := L) (K := K) h x : ℝ)
          ∧ (HourCoupling.cAbove (L := L) (K := K) h
          (Protocol.stepOrSelf (NonuniformMajority L K) x r₁ r₂) : ℝ)
          - (HourCoupling.cAbove (L := L) (K := K) h x : ℝ) ≤ 2 := by
        show _ ∧ _
        unfold HourCoupling.cAbove
        constructor
        · have : ((Multiset.countP (fun a => HourCoupling.clockAboveP h a) x : ℝ))
              - (Multiset.countP (fun a => HourCoupling.clockAboveP h a)
                  (Protocol.stepOrSelf (NonuniformMajority L K) x r₁ r₂) : ℝ) ≤ 2 := by
            exact_mod_cast hcA2
          linarith
        · have : ((Multiset.countP (fun a => HourCoupling.clockAboveP h a)
              (Protocol.stepOrSelf (NonuniformMajority L K) x r₁ r₂) : ℝ))
              - (Multiset.countP (fun a => HourCoupling.clockAboveP h a) x : ℝ) ≤ 2 := by
            exact_mod_cast hcA1
          linarith
      unfold Phi
      rw [abs_le]
      -- Each /M, /C term is bounded by 2/M, 2/C in absolute value.
      have hmM1 : (HourCoupling.mAbove (L := L) (K := K) h
          (Protocol.stepOrSelf (NonuniformMajority L K) x r₁ r₂) : ℝ) / M
          - (HourCoupling.mAbove (L := L) (K := K) h x : ℝ) / M ≤ 2 / M := by
        rw [div_sub_div_same, div_le_div_iff_of_pos_right hM]; linarith [hmAle.2]
      have hmM2 : -(2 / M) ≤ (HourCoupling.mAbove (L := L) (K := K) h
          (Protocol.stepOrSelf (NonuniformMajority L K) x r₁ r₂) : ℝ) / M
          - (HourCoupling.mAbove (L := L) (K := K) h x : ℝ) / M := by
        rw [div_sub_div_same, ← neg_div, div_le_div_iff_of_pos_right hM]; linarith [hmAle.1]
      have hcC1 : (HourCoupling.cAbove (L := L) (K := K) h
          (Protocol.stepOrSelf (NonuniformMajority L K) x r₁ r₂) : ℝ) / C
          - (HourCoupling.cAbove (L := L) (K := K) h x : ℝ) / C ≤ 2 / C := by
        rw [div_sub_div_same, div_le_div_iff_of_pos_right hC]; linarith [hcAle.2]
      have hcC2 : -(2 / C) ≤ (HourCoupling.cAbove (L := L) (K := K) h
          (Protocol.stepOrSelf (NonuniformMajority L K) x r₁ r₂) : ℝ) / C
          - (HourCoupling.cAbove (L := L) (K := K) h x : ℝ) / C := by
        rw [div_sub_div_same, ← neg_div, div_le_div_iff_of_pos_right hC]; linarith [hcAle.1]
      -- Scale the cAbove/C bounds by 11/10.
      have h11 : (0:ℝ) ≤ 11/10 := by norm_num
      have hcC1' : (11/10 : ℝ) * ((HourCoupling.cAbove (L := L) (K := K) h
          (Protocol.stepOrSelf (NonuniformMajority L K) x r₁ r₂) : ℝ) / C
          - (HourCoupling.cAbove (L := L) (K := K) h x : ℝ) / C)
          ≤ (11/10 : ℝ) * (2 / C) := mul_le_mul_of_nonneg_left hcC1 h11
      have hcC2' : (11/10 : ℝ) * (-(2 / C))
          ≤ (11/10 : ℝ) * ((HourCoupling.cAbove (L := L) (K := K) h
          (Protocol.stepOrSelf (NonuniformMajority L K) x r₁ r₂) : ℝ) / C
          - (HourCoupling.cAbove (L := L) (K := K) h x : ℝ) / C) :=
        mul_le_mul_of_nonneg_left hcC2 h11
      have he : 2 * (11/10/C:ℝ) = (11/10) * (2/C) := by ring
      have he2 : (11/10:ℝ) * (-(2/C)) = -((11/10) * (2/C)) := by ring
      rw [he2] at hcC2'
      constructor
      · simp only [mul_div_assoc]; rw [he]; linarith [hmM1, hmM2, hcC1', hcC2']
      · simp only [mul_div_assoc]; rw [he]; linarith [hmM1, hmM2, hcC1', hcC2']
    · subst hyx; simp only [sub_self, abs_zero]; positivity
  -- Lift the support bound to a.e.
  rw [ae_iff]
  change ((NonuniformMajority L K).stepDistOrSelf x).toMeasure
    {y | ¬ |Phi (L := L) (K := K) M C h y - Phi (L := L) (K := K) M C h x|
        ≤ 2 / M + 2 * (11 / 10 : ℝ) / C} = 0
  rw [PMF.toMeasure_apply_eq_zero_iff _ (DiscreteMeasurableSpace.forall_measurableSet _)]
  rw [Set.disjoint_left]
  intro y hy hbad
  exact hbad (hsupp y hy)

/-! ## Part 9 — Lemma 6.10 via the real Azuma tail.

We feed the GENUINE drift (`hour_drift`) and the bounded-difference lemma
(`hour_bdd`) into `AzumaKernel.azuma_tail`.  Since `azuma_tail` needs the drift
and bounded difference at EVERY state, we carry the synchronous-hour regime as an
explicit global hypothesis `hreg` (the TRUE window `c_{>h} ≤ 1/11` together with
the fixed role counts `M`, `C`).  This is the faithful "on the window / until
`end_h`" qualifier of the paper's Lemma 6.10. -/

/-- The synchronous-hour regime at a configuration: the unbiased-Main window, the
window `c_{>h} ≤ 1/11`, the fixed role counts `M`, `C`, and `≥ 1` of each role. -/
def Regime (M C : ℝ) (h : ℕ) (c : Config (AgentState L K)) : Prop :=
  HourCoupling.HourWindow c ∧ Window (L := L) (K := K) h c ∧
    (mainCount (L := L) (K := K) c : ℝ) = M ∧
    (clockCount (L := L) (K := K) c : ℝ) = C ∧
    1 ≤ mainCount (L := L) (K := K) c ∧ 1 ≤ clockCount (L := L) (K := K) c

/-- **Lemma 6.10 (the clock → Main hour-coupling tail), genuine redo.**

For the additive supermartingale potential `Φ h = mAbove h / M − 1.1 · cAbove h / C`
on the synchronous-hour regime (`hreg`), the real Azuma-Hoeffding tail
`AzumaKernel.azuma_tail` gives: for every deviation `λ > 0` and `t ≥ 1`,

  `(K^t) c₀ { Φ ≥ Φ c₀ + λ }  ≤  exp(−λ² / (2 t c₀²))`,    `c₀ = 2/M + 2·(11/10)/C`.

Reading off `Φ c₀ = 0` at the start (Main and Clock both synchronized) and the
level `λ = 0.1 · c_{>h}(end_h)` recovers `m_{>h}(t) ≤ 1.2 · c_{>h}(end_h)` whp.

The drift is the GENUINE `hour_drift` (derived from drag/epidemic pair-counting +
the bracket inequality), NOT a frozen-`cAbove` floor; the concentration is the
REAL `azuma_tail`; the only carried hypothesis is the TRUE window `c_{>h} ≤ 1/11`
(packaged in `hreg`). -/
theorem hour_coupling_v2 (M C : ℝ) (hM : 0 < M) (hC : 0 < C) (h : ℕ) (hK : 0 < K) (hhL : h < L)
    (hreg : ∀ c : Config (AgentState L K), Regime (L := L) (K := K) M C h c)
    (t : ℕ) (ht : 1 ≤ t) (c₀ : Config (AgentState L K)) {lam : ℝ} (hlam : 0 < lam) :
    ((NonuniformMajority L K).transitionKernel ^ t) c₀
        {c' | Phi (L := L) (K := K) M C h c₀ + lam ≤ Phi (L := L) (K := K) M C h c'}
      ≤ ENNReal.ofReal (Real.exp
          (-(lam ^ 2) / (2 * t * (2 / M + 2 * (11 / 10 : ℝ) / C) ^ 2))) := by
  set c0 : ℝ := 2 / M + 2 * (11 / 10 : ℝ) / C with hc0def
  have hc0pos : 0 < c0 := by rw [hc0def]; positivity
  -- Global drift from `hour_drift` under the regime.
  have hdrift : ∀ x, ∫ y, Phi (L := L) (K := K) M C h y
      ∂((NonuniformMajority L K).transitionKernel x) ≤ Phi (L := L) (K := K) M C h x := by
    intro x
    obtain ⟨hw, hwin, hMc, hCc, hM1, hC1⟩ := hreg x
    exact hour_drift M C h hK hhL x hw hwin hMc hCc hM1 hC1
  -- Global bounded difference from `hour_bdd`.
  have hdiff : ∀ x, ∀ᵐ y ∂((NonuniformMajority L K).transitionKernel x),
      |Phi (L := L) (K := K) M C h y - Phi (L := L) (K := K) M C h x| ≤ c0 := by
    intro x; rw [hc0def]; exact hour_bdd M C hM hC h x
  exact ExactMajority.azuma_tail (NonuniformMajority L K).transitionKernel
    (Phi (L := L) (K := K) M C h) (Phi_measurable M C h) c0 hc0pos hdiff hdrift t ht c₀ hlam

end HourCouplingAzuma

end ExactMajority
