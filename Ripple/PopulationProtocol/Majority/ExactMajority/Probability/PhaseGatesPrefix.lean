/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `PhaseGatesPrefix` — the deterministic phase-gate induction along a FrontSync prefix.

This file supplies the CLEAN deterministic piece of the §6 honest C-A route
(`DOCTRINE_THM69_CA.md`, ROUND 6 — `phaseGates_of_prefix_frontSync`).  It is NOT a
probability theorem: it assembles three ALREADY-PROVEN one-step support closures into
a path (prefix) induction.

The three one-step closures, on the `Q_mix ∧ allPhaseGE3 ∧ noPhaseAbove3` window with
`FrontSync` (no clock at the cap):

* `HabsDischarge.allPhaseGE3_closed`            — `allPhaseGE3` is one-step closed
  (unconditional: phase is non-decreasing on every kernel support step);
* `noPhaseAbove3_closed_of_frontSync` (NEW here) — `noPhaseAbove3` is one-step closed
  UNDER `FrontSync`: at phase exactly 3 (= `allPhaseGE3 ∧ noPhaseAbove3`), the only
  phase-advancing branch is `stdCounterSubroutine` firing at the cap, which `FrontSync`
  excludes — so no output exceeds phase 3;
* `ClockFrontShape.counterPos_closed_of_frontSync` — `allClocksCounterPos` is one-step
  closed UNDER `FrontSync` (the synced-at-cap counter-decrement never fires).

`phaseGates_of_prefix_frontSync` then inducts over a support path whose every prefix
config is `FrontSync`, concluding the four phase gates at the prefix end.  This is the
deterministic discharge of `HabsDischarge.ClockPhase3_remaining_synchronization` along a
synchronized trajectory — the probabilistic content (that `FrontSync` HOLDS throughout)
is the SEPARATE front-shape concentration, not touched here.

NEW file; no existing file is edited; no sorry/admit/axiom/native_decide.
Reference: Doty et al. (arXiv:2106.10201v2) Theorem 6.5 + §6 footnote 9.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockFrontShape

namespace ExactMajority

namespace PhaseGatesPrefix

open HabsDischarge ClockFrontShape ClockRealKernel ClockRealMixed

variable {L K : ℕ}

/-! ## Part 1 — the NEW one-step closure `noPhaseAbove3_closed_of_frontSync`.

At phase exactly 3 (`allPhaseGE3 ∧ noPhaseAbove3` pin every agent to `phase.val = 3`),
`FrontSync` keeps every clock strictly below the cap minute `K·(L+1)`.  In the per-pair
`Transition`, the phase epidemic is the identity on two equal phases, and the dispatched
`Phase3Transition` advances phase ONLY via `stdCounterSubroutine`, which fires only in the
synced-AT-cap branch (guarded by `¬ s.minute.val < K·(L+1)`).  `FrontSync` excludes that
branch, so both `Transition` outputs keep `phase.val = 3 ≤ 3`. -/

/-- The phase epidemic is the identity on a pair both at phase exactly 3 (the `max` is
their common phase, the inits between equal phases are empty, and the phase-10 entry
guard fails). -/
theorem phaseEpidemicUpdate_eq_self_of_both_phase3 (s t : AgentState L K)
    (hs : s.phase.val = 3) (ht : t.phase.val = 3) :
    phaseEpidemicUpdate L K s t = (s, t) := by
  have hpeq : s.phase = t.phase := by
    apply Fin.ext; omega
  have hmax : max s.phase t.phase = s.phase := by
    rw [hpeq, max_self]
  have hsself : ({ s with phase := s.phase } : AgentState L K) = s := rfl
  have htself : ({ t with phase := s.phase } : AgentState L K) = t := by
    rw [hpeq]
  have hrunS : runInitsBetween L K s.phase.val (max s.phase t.phase).val
        ({ s with phase := max s.phase t.phase } : AgentState L K) = s := by
    rw [hmax, runInitsBetween_self_api]
  have hrunT : runInitsBetween L K t.phase.val (max s.phase t.phase).val
        ({ t with phase := max s.phase t.phase } : AgentState L K) = t := by
    rw [hmax, show t.phase.val = s.phase.val from by omega, runInitsBetween_self_api]
    exact htself
  unfold phaseEpidemicUpdate
  simp only [hrunS, hrunT]
  rw [if_neg (by omega)]

/-- **Per-pair phase upper bound under `FrontSync`.**  For a pair both at phase exactly 3,
with the FIRST agent strictly below the cap whenever it is a clock (`FrontSync` at the
pair level), both `Transition` outputs are at phase `≤ 3`.  The only phase-advancing branch
(`stdCounterSubroutine` at the cap) is excluded: in the clock-clock case it is guarded by
`s.minute.val < K·(L+1)` (`s` below cap), and in the non-clock-clock case `Phase3Transition`
leaves both phases at the Rule-1 result, which equals the (unchanged) input phase. -/
theorem Transition_phase_le_3_of_pair (s t : AgentState L K)
    (hs : s.phase.val = 3) (ht : t.phase.val = 3)
    (hbelow : s.role = .clock → s.minute.val < capMinute (L := L) (K := K)) :
    (Transition L K s t).1.phase.val ≤ 3 ∧ (Transition L K s t).2.phase.val ≤ 3 := by
  -- Reduce the full `Transition` to `Phase3Transition` on the (unchanged) inputs.
  have hepi := phaseEpidemicUpdate_eq_self_of_both_phase3 s t hs ht
  have hphase3 : s.phase = (⟨3, by omega⟩ : Fin 11) := by apply Fin.ext; simpa using hs
  -- The Rule-1 left result `s1`.
  set s1 : AgentState L K :=
    (if s.role = .clock ∧ t.role = .clock then
      if s.minute ≠ t.minute then { s with minute := max s.minute t.minute }
      else if h_max : s.minute.val < K * (L + 1) then
        { s with minute := ⟨s.minute.val + 1, by omega⟩ }
      else stdCounterSubroutine L K s
    else s) with hs1def
  set t1 : AgentState L K :=
    (if s.role = .clock ∧ t.role = .clock then
      if s.minute ≠ t.minute then { t with minute := max s.minute t.minute }
      else if h_max : s.minute.val < K * (L + 1) then t
      else stdCounterSubroutine L K t
    else t) with ht1def
  -- Rule-1 results stay at phase 3 (the at-cap `stdCounterSubroutine` branch is excluded).
  have hcap : capMinute (L := L) (K := K) = K * (L + 1) := rfl
  have hs1_phase : s1.phase.val = 3 := by
    rw [hs1def]
    by_cases hcc : s.role = .clock ∧ t.role = .clock
    · rw [if_pos hcc]
      by_cases hne : s.minute ≠ t.minute
      · rw [if_pos hne]; simpa using hs
      · rw [if_neg hne]
        have hlt : s.minute.val < K * (L + 1) := by
          have := hbelow hcc.1; rw [hcap] at this; exact this
        rw [dif_pos hlt]; simpa using hs
    · rw [if_neg hcc]; exact hs
  have ht1_phase : t1.phase.val = 3 := by
    rw [ht1def]
    by_cases hcc : s.role = .clock ∧ t.role = .clock
    · rw [if_pos hcc]
      by_cases hne : s.minute ≠ t.minute
      · rw [if_pos hne]; simpa using ht
      · rw [if_neg hne]
        have hlt : s.minute.val < K * (L + 1) := by
          have := hbelow hcc.1; rw [hcap] at this; exact this
        rw [dif_pos hlt]; simpa using ht
    · rw [if_neg hcc]; exact ht
  -- `Phase3Transition` output phases equal the Rule-1 phases.
  have hL := (Phase3Transition_left_output_eq_rule1 (L := L) (K := K) s t s1 hs1def).2
  have hR := (Phase3Transition_right_output_eq_rule1 (L := L) (K := K) s t t1 ht1def).2
  -- Wire `Transition` = `Phase3Transition` (epidemic self; finishPhase10Entry preserves phase).
  have hTrans : Transition L K s t
      = (finishPhase10Entry L K s (Phase3Transition L K s t).1,
         finishPhase10Entry L K t (Phase3Transition L K s t).2) := by
    unfold Transition
    rw [hepi]
    simp only [hphase3]
  refine ⟨?_, ?_⟩
  · rw [hTrans]
    simp only [finishPhase10Entry_phase_val]
    rw [congrArg Fin.val hL, hs1_phase]
  · rw [hTrans]
    simp only [finishPhase10Entry_phase_val]
    rw [congrArg Fin.val hR, ht1_phase]

/-- **`noPhaseAbove3_closed_of_frontSync` — the NEW one-step closure.**  On the
`allPhaseGE3 ∧ noPhaseAbove3` window (every agent at phase exactly 3), `FrontSync` (no clock
at the cap) makes `noPhaseAbove3` one-step closed: every produced agent is at phase `≤ 3`.
Mirrors `HabsDischarge.allPhaseGE3_closed`'s support-step structure, using the per-pair phase
upper bound `Transition_phase_le_3_of_pair` (the at-cap `stdCounterSubroutine` advance is
excluded by `FrontSync`). -/
theorem noPhaseAbove3_closed_of_frontSync (c c' : Config (AgentState L K))
    (hge : allPhaseGE3 (L := L) (K := K) c)
    (hno : noPhaseAbove3 (L := L) (K := K) c)
    (hsync : FrontSync (L := L) (K := K) c)
    (hc' : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    noPhaseAbove3 (L := L) (K := K) c' := by
  classical
  by_cases hc : 2 ≤ c.card
  · rw [show (NonuniformMajority L K).stepDistOrSelf c
        = (NonuniformMajority L K).stepDist c hc by
        unfold Protocol.stepDistOrSelf; rw [dif_pos hc]] at hc'
    obtain ⟨⟨r₁, r₂⟩, hr⟩ := Protocol.stepDist_support (NonuniformMajority L K) c hc c' hc'
    rw [← hr]
    simp only [Protocol.scheduledStep]
    by_cases happ : Protocol.Applicable c r₁ r₂
    · have hmem1 : r₁ ∈ c := mem_of_applicable_left happ
      have hmem2 : r₂ ∈ c := mem_of_applicable_right happ
      -- both inputs are at phase EXACTLY 3.
      have h1eq : r₁.phase.val = 3 := le_antisymm (hno r₁ hmem1) (hge r₁ hmem1)
      have h2eq : r₂.phase.val = 3 := le_antisymm (hno r₂ hmem2) (hge r₂ hmem2)
      -- `FrontSync`: `r₁` is below the cap if it is a clock.
      have hbelow : r₁.role = .clock → r₁.minute.val < capMinute (L := L) (K := K) :=
        fun hcl => hsync r₁ hmem1 hcl
      have hpair := Transition_phase_le_3_of_pair r₁ r₂ h1eq h2eq hbelow
      have hsub : ({r₁, r₂} : Multiset (AgentState L K)) ≤ c := happ
      have hc'eq : Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂
          = c - {r₁, r₂} + {(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2} := by
        unfold Protocol.stepOrSelf; rw [if_pos happ]; rfl
      intro a ha
      rw [hc'eq] at ha
      rcases Multiset.mem_add.mp ha with hin | hin
      · -- survivor from `c`: still phase ≤ 3.
        exact hno a (Multiset.mem_of_le (Multiset.sub_le_self _ _) hin)
      · rw [show ({(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2}
            : Multiset (AgentState L K))
            = (Transition L K r₁ r₂).1 ::ₘ (Transition L K r₁ r₂).2 ::ₘ 0 from rfl] at hin
        rcases Multiset.mem_cons.mp hin with rfl | hin
        · exact hpair.1
        · rcases Multiset.mem_cons.mp hin with rfl | hin
          · exact hpair.2
          · simp at hin
    · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]; exact hno
  · rw [show (NonuniformMajority L K).stepDistOrSelf c = PMF.pure c by
        unfold Protocol.stepDistOrSelf; rw [dif_neg hc]] at hc'
    rw [PMF.mem_support_pure_iff] at hc'
    subst hc'
    exact hno

/-! ## Part 2 — the prefix induction `phaseGates_of_prefix_frontSync`.

A support path is `path : ℕ → Config` with each successor in the previous config's kernel
support (`SupportPath`).  Given a synchronized phase-3 start (`allPhaseGE3 ∧ noPhaseAbove3 ∧
allClocksCounterPos` at `path 0`, plus `Q_mix` along the prefix — only used to instantiate
`counterPos_closed_of_frontSync`'s unused `Q_mix` slot), and `FrontSync` on every prefix
config, the four phase gates hold at the prefix end. -/

/-- A support path: every successor lies in the predecessor's one-step kernel support. -/
def SupportPath (path : ℕ → Config (AgentState L K)) : Prop :=
  ∀ t, path (t + 1) ∈ ((NonuniformMajority L K).stepDistOrSelf (path t)).support

/-- **`phaseGates_of_prefix_frontSync` — the deterministic prefix induction.**

Along a support path whose every prefix config (`path t`, `t ≤ τ`) is `FrontSync`, the three
gates `allPhaseGE3`, `noPhaseAbove3`, `allClocksCounterPos` are maintained from the
synchronized start to `path τ`, and additionally every one-step successor of `path τ` is
`noPhaseAbove3`.  `Q_mix` is carried along the prefix only to fill the (unused) `Q_mix`
slot of `counterPos_closed_of_frontSync`. -/
theorem phaseGates_of_prefix_frontSync
    {n mC T : ℕ} (path : ℕ → Config (AgentState L K)) (hpath : SupportPath path)
    (τ : ℕ)
    (hge0 : allPhaseGE3 (L := L) (K := K) (path 0))
    (hno0 : noPhaseAbove3 (L := L) (K := K) (path 0))
    (hpos0 : allClocksCounterPos (L := L) (K := K) (path 0))
    (hQ : ∀ t, t ≤ τ → Q_mix (L := L) (K := K) n mC T (path t))
    (hprefix : ∀ t, t ≤ τ → FrontSync (L := L) (K := K) (path t)) :
    allPhaseGE3 (L := L) (K := K) (path τ) ∧
      noPhaseAbove3 (L := L) (K := K) (path τ) ∧
      allClocksCounterPos (L := L) (K := K) (path τ) ∧
      (∀ c' ∈ ((NonuniformMajority L K).stepDistOrSelf (path τ)).support,
        noPhaseAbove3 (L := L) (K := K) c') := by
  -- The three running gates along the prefix, proven by induction on `τ`.
  have hgates : ∀ s, s ≤ τ →
      allPhaseGE3 (L := L) (K := K) (path s) ∧
        noPhaseAbove3 (L := L) (K := K) (path s) ∧
        allClocksCounterPos (L := L) (K := K) (path s) := by
    intro s
    induction s with
    | zero => intro _; exact ⟨hge0, hno0, hpos0⟩
    | succ k IH =>
      intro hk
      have hkτ : k ≤ τ := Nat.le_of_succ_le hk
      obtain ⟨hge, hno, hpos⟩ := IH hkτ
      have hsync : FrontSync (L := L) (K := K) (path k) := hprefix k hkτ
      have hstep : path (k + 1) ∈ ((NonuniformMajority L K).stepDistOrSelf (path k)).support :=
        hpath k
      refine ⟨?_, ?_, ?_⟩
      · exact allPhaseGE3_closed (path k) (path (k + 1)) hge hstep
      · exact noPhaseAbove3_closed_of_frontSync (path k) (path (k + 1)) hge hno hsync hstep
      · exact counterPos_closed_of_frontSync n mC T (path k) (path (k + 1))
          (hQ k hkτ) hge hno hpos hsync hstep
  obtain ⟨hgeτ, hnoτ, hposτ⟩ := hgates τ (le_refl τ)
  refine ⟨hgeτ, hnoτ, hposτ, ?_⟩
  -- The successor-`noPhaseAbove3` slot: `FrontSync` at `path τ` closes `noPhaseAbove3`.
  intro c' hc'
  exact noPhaseAbove3_closed_of_frontSync (path τ) c' hgeτ hnoτ (hprefix τ (le_refl τ)) hc'

end PhaseGatesPrefix

end ExactMajority
