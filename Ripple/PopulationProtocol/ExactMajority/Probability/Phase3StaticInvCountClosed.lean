import Ripple.PopulationProtocol.ExactMajority.Probability.HourCoupling
import Ripple.PopulationProtocol.ExactMajority.Probability.ClockRealKernel
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseGatesPrefix
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase3LeafTail

/-!
# Slot-3 static invariant — the COUNT-conservation step closure (the true part)

`StaticInvStepClosed` (the `hstatic_stepClosed` residual) is FALSE unconditionally because it carries
`HourCoupling.HourWindow`'s "phase EXACTLY 3", which is not one-step closed (a phase-3 clock at the cap
advances to phase 4; `HabsDischarge` documents this needs `Q_mix ∧ noPhaseAbove3 ∧ allClocksCounterPos`).

But the **count part** of `StaticInv` (`mainCount = M ∧ clockCount = C`) IS genuinely one-step closed on
the `HourWindow`, because on the window every applicable pair is Main×Main (unbiased ⇒ `phase3CancelSplit`
identity), Main×Clock / Clock×Main (Rule-2 hour-drag, role untouched), or Clock×Clock (Rule-1, role stays
clock even when the phase advances).  So **no role is created or destroyed**, hence every role count is
conserved.  This file proves that count-conservation; the phase/HourWindow guard is supplied separately
from the GoodClock good-hour (clocks below cap before the finish cut).

Key fact: `transition_role_eq_of_window_pair` — on a window pair, the `Transition` preserves both agents'
roles POINTWISE (NOT a global phase≥3 fact, which is false: Phase 6 turns Reserve→Main).
-/

namespace Ripple.PopulationProtocol.ExactMajority
namespace Phase3StaticInvCountClosed

open HourCoupling HourCouplingAzuma Phase3Assembly.LeafTail

variable {L K : ℕ}

/-- **Pointwise role preservation on a window pair.**  For a Phase-3 pair where each agent is
Main-or-Clock and each Main is unbiased (the `HourCoupling.HourWindow` per-agent fact), the protocol
`Transition` leaves both agents' roles unchanged.  Mirrors the case split of
`HourCoupling.phase3_out_phase_ne_ten`. -/
theorem transition_role_eq_of_window_pair (s t : AgentState L K)
    (hs3 : s.phase.val = 3) (ht3 : t.phase.val = 3)
    (hsr : s.role = .main ∨ s.role = .clock) (htr : t.role = .main ∨ t.role = .clock)
    (hsu : s.role = .main → s.bias = .zero) (htu : t.role = .main → t.bias = .zero) :
    (Transition L K s t).1.role = s.role ∧ (Transition L K s t).2.role = t.role := by
  have hne := HourCoupling.phase3_out_phase_ne_ten (L := L) (K := K) s t hs3 ht3 hsr htr hsu htu
  rw [HourCoupling.transition_eq_phase3 (L := L) (K := K) s t hs3 ht3 hne.1 hne.2]
  rcases hsr with hsm | hsc
  · rcases htr with htm | htc
    · -- Main × Main: Phase3Transition = (s, t).
      have hP3 : Phase3Transition L K s t = (s, t) := by
        have hcs := phase3CancelSplit_id_of_unbiased (L := L) (K := K) s t hsu htu ⟨hsm, htm⟩
        unfold Phase3Transition
        have hsc' : s.role ≠ .clock := by rw [hsm]; decide
        have htc' : t.role ≠ .clock := by rw [htm]; decide
        simp only [hsc', htc', hsm, htm, hsu hsm, htu htm, false_and, and_false,
          if_false, if_true, and_self, reduceCtorEq, ite_self]
        exact hcs
      rw [hP3]; exact ⟨rfl, rfl⟩
    · -- Main × Clock: Rule-2 drag, only `hour` changes.
      rw [phase3_drag_left (L := L) (K := K) s t hsm (hsu hsm) htc]; exact ⟨rfl, rfl⟩
  · rcases htr with htm | htc
    · -- Clock × Main: symmetric drag.
      rw [phase3_drag_right (L := L) (K := K) s t hsc htm (htu htm)]; exact ⟨rfl, rfl⟩
    · -- Clock × Clock: Rule-1; role stays clock (even when phase advances to 4).
      exact ⟨(Phase3Transition_preserves_clock_role (L := L) (K := K) s t hsc).trans hsc.symm,
        (Phase3Transition_second_preserves_clock_role (L := L) (K := K) s t htc).trans htc.symm⟩

/-- `countP (role = X)` of the transition output pair equals that of the input pair, on the window. -/
theorem roleCount_pair_eq_of_window (X : Role) (s t : AgentState L K)
    (hs3 : s.phase.val = 3) (ht3 : t.phase.val = 3)
    (hsr : s.role = .main ∨ s.role = .clock) (htr : t.role = .main ∨ t.role = .clock)
    (hsu : s.role = .main → s.bias = .zero) (htu : t.role = .main → t.bias = .zero) :
    Multiset.countP (fun a => a.role = X)
        ({(Transition L K s t).1, (Transition L K s t).2} : Multiset (AgentState L K))
      = Multiset.countP (fun a => a.role = X)
        ({s, t} : Multiset (AgentState L K)) := by
  classical
  rw [HourCoupling.countP_pair, HourCoupling.countP_pair]
  obtain ⟨h1, h2⟩ := transition_role_eq_of_window_pair (L := L) (K := K) s t hs3 ht3 hsr htr hsu htu
  rw [h1, h2]

/-- **Generic config-level role-count conservation under one `StepRel`, on the window.**
Lifts the per-pair `roleCount_pair_eq_of_window` to the whole config (mirrors the
`Multiset.countP_add`/`countP_sub`/`countP_le_of_le` + omega pattern of `clockCount_stepRel`). -/
theorem roleCount_stepRel_of_window (X : Role) {c c' : Config (AgentState L K)}
    (hw : HourCoupling.HourWindow (L := L) (K := K) c)
    (h : (NonuniformMajority L K).StepRel c c') :
    Multiset.countP (fun a => a.role = X) c' = Multiset.countP (fun a => a.role = X) c := by
  classical
  obtain ⟨r₁, r₂, happ, hc'⟩ := h
  have hc'T : c' = c - {r₁, r₂} +
      {(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2} := by
    simpa [NonuniformMajority] using hc'
  have hmem1 : r₁ ∈ c := ClockRealKernel.mem_of_applicable_left happ
  have hmem2 : r₂ ∈ c := ClockRealKernel.mem_of_applicable_right happ
  have hsub : ({r₁, r₂} : Multiset (AgentState L K)) ≤ c := happ
  rw [hc'T, Multiset.countP_add, Multiset.countP_sub hsub]
  rw [roleCount_pair_eq_of_window (L := L) (K := K) X r₁ r₂
        (hw r₁ hmem1).2.1 (hw r₂ hmem2).2.1
        (hw r₁ hmem1).1 (hw r₂ hmem2).1
        (hw r₁ hmem1).2.2 (hw r₂ hmem2).2.2]
  have hle : Multiset.countP (fun a => a.role = X) ({r₁, r₂} : Multiset (AgentState L K))
      ≤ Multiset.countP (fun a => a.role = X) c := Multiset.countP_le_of_le _ hsub
  omega

/-- `mainCount` is conserved by one `StepRel` on the window. -/
theorem mainCount_stepRel_of_window {c c' : Config (AgentState L K)}
    (hw : HourCoupling.HourWindow (L := L) (K := K) c)
    (h : (NonuniformMajority L K).StepRel c c') :
    HourCouplingAzuma.mainCount (L := L) (K := K) c'
      = HourCouplingAzuma.mainCount (L := L) (K := K) c := by
  unfold HourCouplingAzuma.mainCount
  exact roleCount_stepRel_of_window (L := L) (K := K) Role.main hw h

/-- `clockCount` is conserved by one `StepRel` on the window. -/
theorem clockCount_stepRel_of_window {c c' : Config (AgentState L K)}
    (hw : HourCoupling.HourWindow (L := L) (K := K) c)
    (h : (NonuniformMajority L K).StepRel c c') :
    HourCouplingAzuma.clockCount (L := L) (K := K) c'
      = HourCouplingAzuma.clockCount (L := L) (K := K) c := by
  unfold HourCouplingAzuma.clockCount
  exact roleCount_stepRel_of_window (L := L) (K := K) Role.clock hw h

/-! ## Support-level lifting + the GoodClock-guarded static step (the phase-3 half) -/

/-- One support step is either the identity or a genuine `StepRel`. -/
theorem step_support_eq_or_stepRel {c c' : Config (AgentState L K)}
    (hsupp : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    c' = c ∨ (NonuniformMajority L K).StepRel c c' := by
  classical
  by_cases hc : 2 ≤ c.card
  · rw [show (NonuniformMajority L K).stepDistOrSelf c
        = (NonuniformMajority L K).stepDist c hc by
        unfold Protocol.stepDistOrSelf; rw [dif_pos hc]] at hsupp
    obtain ⟨⟨r₁, r₂⟩, hr⟩ := Protocol.stepDist_support (NonuniformMajority L K) c hc c' hsupp
    rw [← hr]
    simp only [Protocol.scheduledStep]
    by_cases happ : Protocol.Applicable c r₁ r₂
    · exact Or.inr (Protocol.stepRel_stepOrSelf_of_applicable (P := NonuniformMajority L K) happ)
    · exact Or.inl (Protocol.stepOrSelf_eq_self_of_not_applicable (P := NonuniformMajority L K) happ)
  · left
    rw [show (NonuniformMajority L K).stepDistOrSelf c = PMF.pure c by
        unfold Protocol.stepDistOrSelf; rw [dif_neg hc]] at hsupp
    simpa using hsupp

theorem mainCount_stepSupport_of_window {c c' : Config (AgentState L K)}
    (hw : HourCoupling.HourWindow (L := L) (K := K) c)
    (hsupp : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    HourCouplingAzuma.mainCount (L := L) (K := K) c'
      = HourCouplingAzuma.mainCount (L := L) (K := K) c := by
  rcases step_support_eq_or_stepRel hsupp with h | h
  · rw [h]
  · exact mainCount_stepRel_of_window hw h

theorem clockCount_stepSupport_of_window {c c' : Config (AgentState L K)}
    (hw : HourCoupling.HourWindow (L := L) (K := K) c)
    (hsupp : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    HourCouplingAzuma.clockCount (L := L) (K := K) c'
      = HourCouplingAzuma.clockCount (L := L) (K := K) c := by
  rcases step_support_eq_or_stepRel hsupp with h | h
  · rw [h]
  · exact clockCount_stepRel_of_window hw h

/-- Output mains of a window pair are unbiased (mirrors `transition_role_eq_of_window_pair`). -/
theorem transition_pair_main_unbiased (s t : AgentState L K)
    (hs3 : s.phase.val = 3) (ht3 : t.phase.val = 3)
    (hsr : s.role = .main ∨ s.role = .clock) (htr : t.role = .main ∨ t.role = .clock)
    (hsu : s.role = .main → s.bias = .zero) (htu : t.role = .main → t.bias = .zero) :
    ((Transition L K s t).1.role = .main → (Transition L K s t).1.bias = .zero) ∧
      ((Transition L K s t).2.role = .main → (Transition L K s t).2.bias = .zero) := by
  have hne := HourCoupling.phase3_out_phase_ne_ten (L := L) (K := K) s t hs3 ht3 hsr htr hsu htu
  rw [HourCoupling.transition_eq_phase3 (L := L) (K := K) s t hs3 ht3 hne.1 hne.2]
  rcases hsr with hsm | hsc
  · rcases htr with htm | htc
    · -- Main × Main: Phase3Transition = (s, t).
      have hP3 : Phase3Transition L K s t = (s, t) := by
        have hcs := phase3CancelSplit_id_of_unbiased (L := L) (K := K) s t hsu htu ⟨hsm, htm⟩
        unfold Phase3Transition
        have hsc' : s.role ≠ .clock := by rw [hsm]; decide
        have htc' : t.role ≠ .clock := by rw [htm]; decide
        simp only [hsc', htc', hsm, htm, hsu hsm, htu htm, false_and, and_false,
          if_false, if_true, and_self, reduceCtorEq, ite_self]
        exact hcs
      rw [hP3]; exact ⟨fun _ => hsu hsm, fun _ => htu htm⟩
    · -- Main × Clock: drag, only hour changes; bias unchanged.
      rw [phase3_drag_left (L := L) (K := K) s t hsm (hsu hsm) htc]
      exact ⟨fun _ => hsu hsm, fun hm => absurd hm (by rw [htc]; decide)⟩
  · rcases htr with htm | htc
    · rw [phase3_drag_right (L := L) (K := K) s t hsc htm (htu htm)]
      exact ⟨fun hm => absurd hm (by rw [hsc]; decide), fun _ => htu htm⟩
    · -- Clock × Clock: outputs stay clock, so the "is main" hypothesis is impossible.
      refine ⟨fun hm => ?_, fun hm => ?_⟩
      · rw [Phase3Transition_preserves_clock_role (L := L) (K := K) s t hsc] at hm
        exact absurd hm (by decide)
      · rw [Phase3Transition_second_preserves_clock_role (L := L) (K := K) s t htc] at hm
        exact absurd hm (by decide)

/-- Generic "∀ a ∈ c', P a" lift through one `StepRel` on the window, given P on `c` and on the
output pair. -/
theorem forall_mem_stepRel_of_window (P : AgentState L K → Prop)
    {c c' : Config (AgentState L K)}
    (hPc : ∀ a ∈ c, P a)
    (hPpair : ∀ r₁ r₂ : AgentState L K, r₁ ∈ c → r₂ ∈ c →
      P (Transition L K r₁ r₂).1 ∧ P (Transition L K r₁ r₂).2)
    (h : (NonuniformMajority L K).StepRel c c') :
    ∀ a ∈ c', P a := by
  classical
  obtain ⟨r₁, r₂, happ, hc'⟩ := h
  have hc'T : c' = c - {r₁, r₂} +
      {(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2} := by
    simpa [NonuniformMajority] using hc'
  have hmem1 : r₁ ∈ c := ClockRealKernel.mem_of_applicable_left happ
  have hmem2 : r₂ ∈ c := ClockRealKernel.mem_of_applicable_right happ
  intro a ha
  rw [hc'T] at ha
  rcases Multiset.mem_add.1 ha with hsub | hpair
  · exact hPc a (Multiset.mem_of_le tsub_le_self hsub)
  · obtain ⟨hp1, hp2⟩ := hPpair r₁ r₂ hmem1 hmem2
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hpair
    rcases hpair with rfl | rfl
    · exact hp1
    · exact hp2

theorem roles_main_or_clock_stepSupport_of_window {c c' : Config (AgentState L K)}
    (hw : HourCoupling.HourWindow (L := L) (K := K) c)
    (hsupp : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    ∀ a ∈ c', a.role = Role.main ∨ a.role = Role.clock := by
  rcases step_support_eq_or_stepRel hsupp with h | h
  · rw [h]; exact fun a ha => (hw a ha).1
  · refine forall_mem_stepRel_of_window (fun a => a.role = .main ∨ a.role = .clock)
      (fun a ha => (hw a ha).1) (fun r₁ r₂ hr₁ hr₂ => ?_) h
    obtain ⟨h1, h2⟩ := transition_role_eq_of_window_pair (L := L) (K := K) r₁ r₂
      (hw r₁ hr₁).2.1 (hw r₂ hr₂).2.1 (hw r₁ hr₁).1 (hw r₂ hr₂).1 (hw r₁ hr₁).2.2 (hw r₂ hr₂).2.2
    simp only [h1, h2]; exact ⟨(hw r₁ hr₁).1, (hw r₂ hr₂).1⟩

theorem mains_unbiased_stepSupport_of_window {c c' : Config (AgentState L K)}
    (hw : HourCoupling.HourWindow (L := L) (K := K) c)
    (hsupp : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    ∀ a ∈ c', a.role = Role.main → a.bias = Bias.zero := by
  rcases step_support_eq_or_stepRel hsupp with h | h
  · rw [h]; exact fun a ha => (hw a ha).2.2
  · refine forall_mem_stepRel_of_window (fun a => a.role = .main → a.bias = .zero)
      (fun a ha => (hw a ha).2.2) (fun r₁ r₂ hr₁ hr₂ => ?_) h
    exact transition_pair_main_unbiased (L := L) (K := K) r₁ r₂
      (hw r₁ hr₁).2.1 (hw r₂ hr₂).2.1 (hw r₁ hr₁).1 (hw r₂ hr₂).1 (hw r₁ hr₁).2.2 (hw r₂ hr₂).2.2

/-- **The GoodClock-guarded static step.**  `StaticInv` is NOT one-step closed (phase-exactly-3 fails
at the clock cap), but it IS closed under the guard `FrontSync` (no clock at the cap rules out the only
phase-advancing branch).  Count/role/bias parts are unconditionally window-closed (proved above);
phase∈{≥3,≤3} closes via `allPhaseGE3_closed` + `noPhaseAbove3_closed_of_frontSync`. -/
theorem staticInv_step_of_frontSync {D : Phase3Core.Phase3ModeDomain L} {C : ℝ}
    {c c' : Config (AgentState L K)}
    (hs : StaticInv (L := L) (K := K) D C c)
    (hfront : ClockFrontShape.FrontSync (L := L) (K := K) c)
    (hsupp : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    StaticInv (L := L) (K := K) D C c' := by
  have hw : HourCoupling.HourWindow (L := L) (K := K) c := hs.1
  have hge : MixedWindowClosure.allPhaseGE3 (L := L) (K := K) c :=
    fun a ha => le_of_eq (hw a ha).2.1.symm
  have hno : MixedWindowClosure.noPhaseAbove3 (L := L) (K := K) c :=
    fun a ha => le_of_eq (hw a ha).2.1
  have hge' : MixedWindowClosure.allPhaseGE3 (L := L) (K := K) c' :=
    MixedWindowClosure.allPhaseGE3_closed c c' hge hsupp
  have hno' : MixedWindowClosure.noPhaseAbove3 (L := L) (K := K) c' :=
    PhaseGatesPrefix.noPhaseAbove3_closed_of_frontSync c c' hge hno hfront hsupp
  have hmain := mainCount_stepSupport_of_window (L := L) (K := K) hw hsupp
  have hclock := clockCount_stepSupport_of_window (L := L) (K := K) hw hsupp
  have hw' : HourCoupling.HourWindow (L := L) (K := K) c' := by
    intro a ha
    exact ⟨roles_main_or_clock_stepSupport_of_window (L := L) (K := K) hw hsupp a ha,
      le_antisymm (hno' a ha) (hge' a ha),
      mains_unbiased_stepSupport_of_window (L := L) (K := K) hw hsupp a ha⟩
  exact ⟨hw', by rw [hmain]; exact hs.2.1, by rw [hclock]; exact hs.2.2.1,
    by rw [hmain]; exact hs.2.2.2.1, by rw [hclock]; exact hs.2.2.2.2⟩

/-- **Finite stopped-prefix induction.**  If the trace follows the kernel support, starts at a
`StaticInv` entry, and is `FrontSync` on the whole prefix `[0, t)`, then `StaticInv` holds at time `t`. -/
theorem staticInv_at_time_of_frontSync_prefix {D : Phase3Core.Phase3ModeDomain L} {C : ℝ}
    {entry : Config (AgentState L K)} {tr : ℕ → Config (AgentState L K)}
    (hstart : tr 0 = entry)
    (hpath : PhaseGatesPrefix.SupportPath (L := L) (K := K) tr)
    (hentry : StaticInv (L := L) (K := K) D C entry)
    (t : ℕ)
    (hfront : ∀ τ, τ < t → ClockFrontShape.FrontSync (L := L) (K := K) (tr τ)) :
    StaticInv (L := L) (K := K) D C (tr t) := by
  induction t with
  | zero => simpa [hstart] using hentry
  | succ t ih =>
      have hs_t : StaticInv (L := L) (K := K) D C (tr t) :=
        ih (fun τ hτ => hfront τ (by omega))
      exact staticInv_step_of_frontSync (L := L) (K := K) hs_t
        (hfront t (by omega)) (hpath t)

end Phase3StaticInvCountClosed
end Ripple.PopulationProtocol.ExactMajority
