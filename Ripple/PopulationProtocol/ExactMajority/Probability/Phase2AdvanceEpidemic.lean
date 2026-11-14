/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Phase-2 opposite-sign advance epidemic

The strict Phase-2 consensus branches are ordinary one-sign epidemics.  The
remaining branch starts with both signs present, but with every individual
opinion still single-sign.  A positive/negative encounter advances both
selected agents to Phase 3.  Both sign tails below are measured under the same
real protocol kernel and use one common target-stopped rank.  A separate
target-stopped kernel freezes the exact first-entry payload for the pathwise
bridge.

The real-kernel fixed-time post `allPhaseGe 2 /\ some phase >= 3` is deliberately
kept separate from the first-crossing shell.  The former is absorbing but may
later contain phases 4--10; only the stopped kernel retains the exact first
Phase-3 entry state.
-/

import Ripple.PopulationProtocol.ExactMajority.Analysis.PhaseProgress
import Ripple.PopulationProtocol.ExactMajority.Probability.CancelClockConcentration
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase5Convergence
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase3Pre3
import Ripple.PopulationProtocol.ExactMajority.Probability.AdvanceEpidemics
import Ripple.PopulationProtocol.ExactMajority.Probability.AdvanceOvershootSource
import Ripple.PopulationProtocol.ExactMajority.Probability.TightEpidemicWork

namespace Ripple.PopulationProtocol.ExactMajority
namespace Phase2AdvanceEpidemic

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal Real

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-! ## Opinion algebra and the genuine active shell -/

/-- An opinion carries the selected strict sign. -/
def carries (sigma : Sign) (a : AgentState L K) : Prop :=
  match sigma with
  | .pos => hasPlusOne a.opinions = true
  | .neg => hasMinusOne a.opinions = true

instance (sigma : Sign) (a : AgentState L K) : Decidable (carries sigma a) := by
  unfold carries
  split <;> infer_instance

/-- Number of agents carrying one selected sign. -/
noncomputable def signCount (sigma : Sign)
    (c : Config (AgentState L K)) : ℕ :=
  Multiset.countP (carries sigma) c

/-- All agents are in Phase 2 and every individual opinion is single-sign. -/
def Phase2SingleShell (n : ℕ) (c : Config (AgentState L K)) : Prop :=
  c.card = n ∧
    ∀ a ∈ c, a.phase.val = 2 ∧
      Phase2Convergence.singleSign a.opinions

/-- The active four-way branch: both signs have a live source, but no individual
agent carries both signs. -/
def Active2Core (n : ℕ) (c : Config (AgentState L K)) : Prop :=
  Phase2SingleShell n c ∧
    1 ≤ signCount Sign.pos c ∧
    1 ≤ signCount Sign.neg c

/-- Concrete provenance needed by the Phase-1-to-2 producer.  The probabilistic
core itself only consumes `Active2Core`; this strengthening additionally rules
out every initializer error and the unreachable empty opinion code. -/
def Active2Concrete (n : ℕ) (c : Config (AgentState L K)) : Prop :=
  Active2Core n c ∧
    AdvanceNoOvershoot.Wf c ∧
    ∀ a ∈ c, a.opinions.val ≠ 0

/-- Failure of `singleSign` is exactly the conflicting-sign condition. -/
theorem not_singleSign_iff_conflicting (o : Fin 8) :
    ¬ Phase2Convergence.singleSign o ↔
      hasMinusOne o = true ∧ hasPlusOne o = true := by
  simp [Phase2Convergence.singleSign]

/-- Opinion union either remains single-sign or exposes both signs.  This is a
dichotomy, not an unconditional closure theorem. -/
theorem union_singleSign_or_conflicting (u v : Fin 8) :
    Phase2Convergence.singleSign (opinionsUnion u v) ∨
      (hasMinusOne (opinionsUnion u v) = true ∧
        hasPlusOne (opinionsUnion u v) = true) := by
  by_cases h : Phase2Convergence.singleSign (opinionsUnion u v)
  · exact Or.inl h
  · exact Or.inr ((not_singleSign_iff_conflicting _).mp h)

/-- Union preserves a selected sign from the left input. -/
theorem carries_union_left (sigma : Sign) (u v : Fin 8)
    (h : match sigma with
      | .pos => hasPlusOne u = true
      | .neg => hasMinusOne u = true) :
    match sigma with
    | .pos => hasPlusOne (opinionsUnion u v) = true
    | .neg => hasMinusOne (opinionsUnion u v) = true := by
  cases sigma <;> fin_cases u <;> fin_cases v <;>
    simp [opinionsUnion, hasPlusOne, hasMinusOne] at h ⊢

/-- Union preserves a selected sign from the right input. -/
theorem carries_union_right (sigma : Sign) (u v : Fin 8)
    (h : match sigma with
      | .pos => hasPlusOne v = true
      | .neg => hasMinusOne v = true) :
    match sigma with
    | .pos => hasPlusOne (opinionsUnion u v) = true
    | .neg => hasMinusOne (opinionsUnion u v) = true := by
  cases sigma <;> fin_cases u <;> fin_cases v <;>
    simp [opinionsUnion, hasPlusOne, hasMinusOne] at h ⊢

/-- A nonempty opinion remains nonempty after union. -/
theorem opinionsUnion_ne_zero_of_left {u v : Fin 8} (hu : u.val ≠ 0) :
    (opinionsUnion u v).val ≠ 0 := by
  fin_cases u <;> fin_cases v <;>
    simp [opinionsUnion] at hu ⊢

/-- Same-phase Phase-2 interactions do not run a phase initializer. -/
private theorem phaseEpidemicUpdate_eq_self_of_phase2
    (s t : AgentState L K) (hs : s.phase.val = 2) (ht : t.phase.val = 2) :
    phaseEpidemicUpdate L K s t = (s, t) := by
  have hs_eq : s.phase = ⟨2, by decide⟩ := Fin.ext hs
  have ht_eq : t.phase = ⟨2, by decide⟩ := Fin.ext ht
  unfold phaseEpidemicUpdate
  rw [hs_eq, ht_eq, max_self]
  simp only [runInitsBetween_self]
  cases s
  cases t
  simp_all

/-- Exact local Phase-2 dichotomy.  On the nonconflicting branch the selected
pair stays in Phase 2 with the common union opinion; on the conflicting branch
both outputs are exactly in Phase 3. -/
theorem Transition_phase2_singleSign_or_advance
    (s t : AgentState L K)
    (hs2 : s.phase.val = 2) (ht2 : t.phase.val = 2) :
    let u := opinionsUnion s.opinions t.opinions
    let s' := (Transition L K s t).1
    let t' := (Transition L K s t).2
    (Phase2Convergence.singleSign u ∧
        s'.phase.val = 2 ∧ t'.phase.val = 2 ∧
        s'.opinions = u ∧ t'.opinions = u) ∨
      (hasMinusOne u = true ∧ hasPlusOne u = true ∧
        s'.phase.val = 3 ∧ t'.phase.val = 3) := by
  dsimp only
  rcases union_singleSign_or_conflicting s.opinions t.opinions with hsingle | hconf
  · left
    have hs_phase : s.phase = ⟨2, by decide⟩ := Fin.ext hs2
    have ht_phase : t.phase = ⟨2, by decide⟩ := Fin.ext ht2
    have hepi := phaseEpidemicUpdate_eq_self_of_phase2
      (L := L) (K := K) s t hs2 ht2
    have hstay := Phase2Convergence.not_both_signs_of_singleSign hsingle
    have hTrans : Transition L K s t =
        (finishPhase10Entry L K s (Phase2Transition L K s t).1,
          finishPhase10Entry L K t (Phase2Transition L K s t).2) := by
      unfold Transition
      rw [hepi]
      simp only [hs_phase]
    have hlocal :
        (Phase2Transition L K s t).1.phase = s.phase ∧
          (Phase2Transition L K s t).1.opinions =
            opinionsUnion s.opinions t.opinions ∧
          (Phase2Transition L K s t).2.phase = t.phase ∧
          (Phase2Transition L K s t).2.opinions =
            opinionsUnion s.opinions t.opinions := by
      unfold Phase2Transition
      rw [if_neg (by simp [hstay])]
      split_ifs <;> simp_all
    have hs_ne : (Phase2Transition L K s t).1.phase.val ≠ 10 := by
      rw [hlocal.1, hs2]
      omega
    have ht_ne : (Phase2Transition L K s t).2.phase.val ≠ 10 := by
      rw [hlocal.2.2.1, ht2]
      omega
    have hs_finish :
        finishPhase10Entry L K s (Phase2Transition L K s t).1 =
          (Phase2Transition L K s t).1 :=
      finishPhase10Entry_eq_self_of_after_ne_10
        (L := L) (K := K) s _ hs_ne
    have ht_finish :
        finishPhase10Entry L K t (Phase2Transition L K s t).2 =
          (Phase2Transition L K s t).2 :=
      finishPhase10Entry_eq_self_of_after_ne_10
        (L := L) (K := K) t _ ht_ne
    refine ⟨hsingle, ?_, ?_, ?_, ?_⟩
    · rw [hTrans, hs_finish, hlocal.1, hs2]
    · rw [hTrans, ht_finish, hlocal.2.2.1, ht2]
    · rw [hTrans, hs_finish]
      exact hlocal.2.1
    · rw [hTrans, ht_finish]
      exact hlocal.2.2.2
  · right
    have hadv := Transition_phase2_advances_of_union_has_opposite_signs
      (L := L) (K := K) s t hs2 ht2 hconf.1 hconf.2
    exact ⟨hconf.1, hconf.2, hadv.1, hadv.2⟩

/-- Per-sign reading of the exact local dichotomy.  A nonadvancing pair copies
the selected sign to both outputs whenever either input carried it. -/
theorem Transition_phase2_sign_pair_or_advance
    (sigma : Sign) (s t : AgentState L K)
    (hs2 : s.phase.val = 2) (ht2 : t.phase.val = 2) :
    let s' := (Transition L K s t).1
    let t' := (Transition L K s t).2
    (s'.phase.val = 2 ∧ Phase2Convergence.singleSign s'.opinions ∧
        t'.phase.val = 2 ∧ Phase2Convergence.singleSign t'.opinions ∧
        (carries sigma s ∨ carries sigma t →
          carries sigma s' ∧ carries sigma t')) ∨
      (s'.phase.val = 3 ∧ t'.phase.val = 3) := by
  dsimp only
  rcases Transition_phase2_singleSign_or_advance
      (L := L) (K := K) s t hs2 ht2 with hkeep | hadv
  · left
    refine ⟨hkeep.2.1, ?_, hkeep.2.2.1, ?_, ?_⟩
    · simpa [hkeep.2.2.2.1] using hkeep.1
    · simpa [hkeep.2.2.2.2] using hkeep.1
    · intro hsource
      cases sigma with
      | pos =>
          have hu : hasPlusOne (opinionsUnion s.opinions t.opinions) = true :=
            hsource.elim
              (carries_union_left Sign.pos s.opinions t.opinions)
              (carries_union_right Sign.pos s.opinions t.opinions)
          simpa [carries, hkeep.2.2.2.1, hkeep.2.2.2.2] using And.intro hu hu
      | neg =>
          have hu : hasMinusOne (opinionsUnion s.opinions t.opinions) = true :=
            hsource.elim
              (carries_union_left Sign.neg s.opinions t.opinions)
              (carries_union_right Sign.neg s.opinions t.opinions)
          simpa [carries, hkeep.2.2.2.1, hkeep.2.2.2.2] using And.intro hu hu
  · exact Or.inr ⟨hadv.2.2.1, hadv.2.2.2⟩

/-! ## Exact Phase-3 first-entry payload -/

/-- Advancing a Phase-2 agent with the destination initializer produces
exactly the pointwise Phase-3 entry payload. -/
theorem Phase3EntryAgent_advancePhaseWithInit_of_phase2
    (a : AgentState L K) (ha : a.phase.val = 2) :
    Phase3Pre3.Phase3EntryAgent
      (advancePhaseWithInit L K a) := by
  have hphase : a.phase = ⟨2, by decide⟩ := Fin.ext ha
  rcases a with
    ⟨input, output, phase, role, assigned, bias, smallBias,
      hour, minute, full, opinions, counter⟩
  simp only at hphase
  subst phase
  cases role <;>
    simp [Phase3Pre3.Phase3EntryAgent,
      Phase3Pre3.phase3BiasOfSmallBias,
      advancePhaseWithInit, advancePhase, phaseInit]

/-- On the conflicting branch, the local Phase-2 rule produces two exact
Phase-3 initializer payloads. -/
theorem Phase2Transition_advance_entry_agents
    (s t : AgentState L K)
    (hs2 : s.phase.val = 2) (ht2 : t.phase.val = 2)
    (hminus : hasMinusOne (opinionsUnion s.opinions t.opinions) = true)
    (hplus : hasPlusOne (opinionsUnion s.opinions t.opinions) = true) :
    Phase3Pre3.Phase3EntryAgent (Phase2Transition L K s t).1 ∧
      Phase3Pre3.Phase3EntryAgent (Phase2Transition L K s t).2 := by
  have hsEntry := Phase3EntryAgent_advancePhaseWithInit_of_phase2
    (L := L) (K := K)
    ({s with opinions := opinionsUnion s.opinions t.opinions}) (by simpa using hs2)
  have htEntry := Phase3EntryAgent_advancePhaseWithInit_of_phase2
    (L := L) (K := K)
    ({t with opinions := opinionsUnion s.opinions t.opinions}) (by simpa using ht2)
  simpa [Phase2Transition, hminus, hplus] using And.intro hsEntry htEntry

/-- Full-dispatcher form of the exact Phase-3 initializer payload theorem. -/
theorem Transition_phase2_advance_entry_agents
    (s t : AgentState L K)
    (hs2 : s.phase.val = 2) (ht2 : t.phase.val = 2)
    (hminus : hasMinusOne (opinionsUnion s.opinions t.opinions) = true)
    (hplus : hasPlusOne (opinionsUnion s.opinions t.opinions) = true) :
    Phase3Pre3.Phase3EntryAgent (Transition L K s t).1 ∧
      Phase3Pre3.Phase3EntryAgent (Transition L K s t).2 := by
  have hs_phase : s.phase = ⟨2, by decide⟩ := Fin.ext hs2
  have hepi := phaseEpidemicUpdate_eq_self_of_phase2
    (L := L) (K := K) s t hs2 ht2
  have hlocal := Phase2Transition_advance_entry_agents
    (L := L) (K := K) s t hs2 ht2 hminus hplus
  have hTrans : Transition L K s t =
      (finishPhase10Entry L K s (Phase2Transition L K s t).1,
        finishPhase10Entry L K t (Phase2Transition L K s t).2) := by
    unfold Transition
    rw [hepi]
    simp only [hs_phase]
  have hs_ne : (Phase2Transition L K s t).1.phase.val ≠ 10 := by
    have := hlocal.1.1
    omega
  have ht_ne : (Phase2Transition L K s t).2.phase.val ≠ 10 := by
    have := hlocal.2.1
    omega
  have hs_finish :
      finishPhase10Entry L K s (Phase2Transition L K s t).1 =
        (Phase2Transition L K s t).1 :=
    finishPhase10Entry_eq_self_of_after_ne_10
      (L := L) (K := K) s _ hs_ne
  have ht_finish :
      finishPhase10Entry L K t (Phase2Transition L K s t).2 =
        (Phase2Transition L K s t).2 :=
    finishPhase10Entry_eq_self_of_after_ne_10
      (L := L) (K := K) t _ ht_ne
  rw [hTrans, hs_finish, ht_finish]
  exact hlocal

/-- Exact shell at the first Phase-2-to-3 crossing: unchanged agents remain in
Phase 2, and every newly advanced agent carries the Phase-3 initializer
payload. -/
def Phase23FirstEntry (n : ℕ) (c : Config (AgentState L K)) : Prop :=
  c.card = n ∧
    (∀ a ∈ c, a.phase.val = 2 ∨
      Phase3Pre3.Phase3EntryAgent a) ∧
    ∃ a ∈ c, Phase3Pre3.Phase3EntryAgent a

noncomputable instance (n : ℕ) (c : Config (AgentState L K)) :
    Decidable (Phase23FirstEntry n c) := by
  unfold Phase23FirstEntry
  infer_instance

/-- A conflicting applicable pair creates the exact first-entry shell. -/
theorem Phase23FirstEntry_stepOrSelf_of_conflicting_pair
    (n : ℕ) (c : Config (AgentState L K))
    (hShell : Phase2SingleShell n c) (s t : AgentState L K)
    (happ : Protocol.Applicable c s t)
    (hminus : hasMinusOne (opinionsUnion s.opinions t.opinions) = true)
    (hplus : hasPlusOne (opinionsUnion s.opinions t.opinions) = true) :
    Phase23FirstEntry n
      (Protocol.stepOrSelf (NonuniformMajority L K) c s t) := by
  classical
  have hs_mem : s ∈ c := Multiset.mem_of_le happ (by simp)
  have ht_mem : t ∈ c := Multiset.mem_of_le happ (by simp)
  have hentry := Transition_phase2_advance_entry_agents s t
    (hShell.2 s hs_mem).1 (hShell.2 t ht_mem).1 hminus hplus
  have hc' :
      Protocol.stepOrSelf (NonuniformMajority L K) c s t =
        c - {s, t} + {(Transition L K s t).1, (Transition L K s t).2} := by
    unfold Protocol.stepOrSelf
    rw [if_pos happ]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [Protocol.stepOrSelf_card_eq]
    exact hShell.1
  · intro a ha
    rw [hc'] at ha
    have ha' :
        a = (Transition L K s t).1 ∨ a ∈ c - {s, t} ∨
          a = (Transition L K s t).2 := by
      simpa using ha
    rcases ha' with rfl | haold | rfl
    · exact Or.inr hentry.1
    · exact Or.inl (hShell.2 a
        (Multiset.mem_of_le (Multiset.sub_le_self c {s, t}) haold)).1
    · exact Or.inr hentry.2
  · refine ⟨(Transition L K s t).1, ?_, hentry.1⟩
    rw [hc']
    simp

/-! ## Common first-advance stopped kernel -/

/-- Absorbing real-kernel marker that the execution has crossed Phase 2. -/
def AdvancedPast2 (n : ℕ) (c : Config (AgentState L K)) : Prop :=
  AdvanceEpidemics.SeededAdvanceWin (L := L) (K := K) 2 n c

instance (n : ℕ) (c : Config (AgentState L K)) :
    Decidable (AdvancedPast2 (L := L) (K := K) n c) := by
  unfold AdvancedPast2
  infer_instance

/-- Boolean-valued counter used only to instantiate the generic target-stopped
kernel. -/
def advanceBit (n : ℕ) (c : Config (AgentState L K)) : ℕ :=
  if AdvancedPast2 n c then 1 else 0

/-- Auxiliary target-stopped kernel for the exact first-entry shell.  It agrees
with the real protocol before the first advance and self-loops afterwards.  The
sign milestone phases below run on the real protocol kernel, not on this one. -/
noncomputable abbrev advanceStopK (n : ℕ) :
    Kernel (Config (AgentState L K)) (Config (AgentState L K)) :=
  CancelClockConcentration.stoppedKernel
    (NonuniformMajority L K).transitionKernel
    (advanceBit (L := L) (K := K) n) 1

/-- Before the target, the common stopped kernel is literally the real kernel. -/
theorem advanceStopK_eq_real_of_not_advanced
    (n : ℕ) (c : Config (AgentState L K))
    (h : ¬ AdvancedPast2 n c) :
    advanceStopK (L := L) (K := K) n c =
      (NonuniformMajority L K).transitionKernel c := by
  unfold advanceStopK CancelClockConcentration.stoppedKernel
  rw [Kernel.piecewise_apply]
  simp [CancelClockConcentration.activeSet, advanceBit, h]

/-- At the target, the common stopped kernel is the identity kernel. -/
theorem advanceStopK_eq_id_of_advanced
    (n : ℕ) (c : Config (AgentState L K))
    (h : AdvancedPast2 n c) :
    advanceStopK (L := L) (K := K) n c = Kernel.id c := by
  unfold advanceStopK CancelClockConcentration.stoppedKernel
  rw [Kernel.piecewise_apply]
  simp [CancelClockConcentration.activeSet, advanceBit, h]

/-- The shared stopped rank: every first advance jumps both sign processes to
their common terminal level `n`. -/
noncomputable def stoppedSignCount (sigma : Sign) (n : ℕ)
    (c : Config (AgentState L K)) : ℕ :=
  if AdvancedPast2 n c then n else signCount sigma c

/-- Per-sign invariant used by the two concurrent milestone processes. -/
def SignRunInv (sigma : Sign) (n : ℕ)
    (c : Config (AgentState L K)) : Prop :=
  AdvancedPast2 n c ∨
    (Phase2SingleShell n c ∧ 1 ≤ signCount sigma c)

/-- A concrete active start supplies both per-sign invariants. -/
theorem signRunInv_of_active (sigma : Sign) (n : ℕ)
    (c : Config (AgentState L K)) (h : Active2Core n c) :
    SignRunInv sigma n c := by
  right
  refine ⟨h.1, ?_⟩
  cases sigma
  · exact h.2.1
  · exact h.2.2

/-- The real target marker is support-closed. -/
theorem AdvancedPast2_of_real_support
    (n : ℕ) (c c' : Config (AgentState L K))
    (h : AdvancedPast2 n c)
    (hsupp : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    AdvancedPast2 n c' := by
  exact AdvanceEpidemics.SeededAdvanceWin_absorbing
    (L := L) (K := K) 2 n c c' h hsupp

/-- From an already advanced state, the real protocol assigns zero mass to the
not-yet-advanced region. -/
theorem real_not_advanced_eq_zero_of_advanced
    (n : ℕ) (c : Config (AgentState L K))
    (h : AdvancedPast2 n c) :
    (NonuniformMajority L K).transitionKernel c
        {c' | ¬ AdvancedPast2 n c'} = 0 := by
  change ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
      {c' | ¬ AdvancedPast2 n c'} = 0
  rw [PMF.toMeasure_apply_eq_zero_iff
    (p := (NonuniformMajority L K).stepDistOrSelf c)
    (DiscreteMeasurableSpace.forall_measurableSet _)]
  rw [Set.disjoint_left]
  intro c' hsupp hnot
  exact hnot (AdvancedPast2_of_real_support n c c' h hsupp)

/-- At every finite time, the stopped and real chains have exactly the same
restriction to the not-yet-advanced region.  This is stronger than equality of
their non-hitting probabilities and is the quantitative bridge from the real
Janson tail to the first-entry stopped chain. -/
theorem advanceStopK_pow_restrict_not_advanced_eq_real
    (n t : ℕ) (c : Config (AgentState L K)) :
    ((advanceStopK (L := L) (K := K) n ^ t) c).restrict
        {c' | ¬ AdvancedPast2 n c'} =
      (((NonuniformMajority L K).transitionKernel ^ t) c).restrict
        {c' | ¬ AdvancedPast2 n c'} := by
  let U : Set (Config (AgentState L K)) :=
    {c' | ¬ AdvancedPast2 n c'}
  have hU : MeasurableSet U :=
    DiscreteMeasurableSpace.forall_measurableSet _
  change ((advanceStopK (L := L) (K := K) n ^ t) c).restrict U =
    (((NonuniformMajority L K).transitionKernel ^ t) c).restrict U
  induction t with
  | zero => rfl
  | succ t ih =>
      apply Measure.ext
      intro S hS
      rw [Measure.restrict_apply hS, Measure.restrict_apply hS]
      have hSU : MeasurableSet (S ∩ U) := hS.inter hU
      rw [Kernel.pow_succ_apply_eq_lintegral _ t c hSU,
        Kernel.pow_succ_apply_eq_lintegral _ t c hSU]
      have hkernel : ∀ x : Config (AgentState L K),
          advanceStopK (L := L) (K := K) n x (S ∩ U) =
            (NonuniformMajority L K).transitionKernel x (S ∩ U) := by
        intro x
        by_cases hx : x ∈ U
        · have hnot : ¬ AdvancedPast2 n x := by
            simpa [U] using hx
          rw [advanceStopK_eq_real_of_not_advanced n x hnot]
        · have hadv : AdvancedPast2 n x := by
            simpa [U] using hx
          calc
            advanceStopK (L := L) (K := K) n x (S ∩ U) = 0 := by
              rw [advanceStopK_eq_id_of_advanced n x hadv,
                Kernel.id_apply, Measure.dirac_apply' x hSU]
              simp [hx]
            _ = (NonuniformMajority L K).transitionKernel x (S ∩ U) :=
              (measure_mono_null Set.inter_subset_right
                (real_not_advanced_eq_zero_of_advanced n x hadv)).symm
      let f : Config (AgentState L K) → ℝ≥0∞ := fun x =>
        (NonuniformMajority L K).transitionKernel x (S ∩ U)
      have hf_zero : ∀ x : Config (AgentState L K), x ∉ U → f x = 0 := by
        intro x hx
        have hadv : AdvancedPast2 n x := by
          simpa [U] using hx
        exact measure_mono_null Set.inter_subset_right
          (real_not_advanced_eq_zero_of_advanced n x hadv)
      have hindicator : ∀ x : Config (AgentState L K),
          U.indicator f x = f x := by
        intro x
        by_cases hx : x ∈ U
        · simp [hx]
        · simp [hx, hf_zero x hx]
      calc
        ∫⁻ x, advanceStopK (L := L) (K := K) n x (S ∩ U)
            ∂((advanceStopK (L := L) (K := K) n ^ t) c) =
            ∫⁻ x, f x ∂((advanceStopK (L := L) (K := K) n ^ t) c) :=
          lintegral_congr hkernel
        _ = ∫⁻ x, U.indicator f x
              ∂((advanceStopK (L := L) (K := K) n ^ t) c) :=
          lintegral_congr (fun x => (hindicator x).symm)
        _ = ∫⁻ x, f x ∂(((advanceStopK
              (L := L) (K := K) n ^ t) c).restrict U) :=
          lintegral_indicator hU f
        _ = ∫⁻ x, f x ∂((((NonuniformMajority L K).transitionKernel ^ t) c).restrict U) := by
          rw [ih]
        _ = ∫⁻ x, U.indicator f x
              ∂(((NonuniformMajority L K).transitionKernel ^ t) c) :=
          (lintegral_indicator hU f).symm
        _ = ∫⁻ x, f x
              ∂(((NonuniformMajority L K).transitionKernel ^ t) c) :=
          lintegral_congr hindicator

/-- Consequently, the real and stopped laws have the same probability of not
having advanced by any fixed finite time. -/
theorem advanceStopK_pow_not_advanced_eq_real
    (n t : ℕ) (c : Config (AgentState L K)) :
    (advanceStopK (L := L) (K := K) n ^ t) c
        {c' | ¬ AdvancedPast2 n c'} =
      ((NonuniformMajority L K).transitionKernel ^ t) c
        {c' | ¬ AdvancedPast2 n c'} := by
  have h := congrArg
    (fun μ : Measure (Config (AgentState L K)) =>
      μ {c' | ¬ AdvancedPast2 n c'})
    (advanceStopK_pow_restrict_not_advanced_eq_real
      (L := L) (K := K) n t c)
  simpa only [Measure.restrict_apply_self] using h

/-! ## Deterministic and support closure -/

/-- Once the common target has been reached, every scheduled pair preserves
it. -/
theorem AdvancedPast2_stepOrSelf
    (n : ℕ) (c : Config (AgentState L K))
    (h : AdvancedPast2 n c) (s t : AgentState L K) :
    AdvancedPast2 n
      (Protocol.stepOrSelf (NonuniformMajority L K) c s t) := by
  unfold AdvancedPast2 at h ⊢
  exact ⟨
    AdvanceEpidemics.allPhaseGe_stepOrSelf 2 n c h.1 s t,
    le_trans h.2 (AdvanceEpidemics.geCount_stepOrSelf_ge 3 c s t)⟩

/-- An applicable pair whose two dispatcher outputs are in Phase 3 creates the
common target from the Phase-2 shell. -/
theorem AdvancedPast2_stepOrSelf_of_phase3_pair
    (n : ℕ) (c : Config (AgentState L K))
    (hShell : Phase2SingleShell n c) (s t : AgentState L K)
    (happ : Protocol.Applicable c s t)
    (hs3 : (Transition L K s t).1.phase.val = 3)
    (ht3 : (Transition L K s t).2.phase.val = 3) :
    AdvancedPast2 n
      (Protocol.stepOrSelf (NonuniformMajority L K) c s t) := by
  classical
  have hc' :
      Protocol.stepOrSelf (NonuniformMajority L K) c s t =
        c - {s, t} + {(Transition L K s t).1, (Transition L K s t).2} := by
    unfold Protocol.stepOrSelf
    rw [if_pos happ]
    rfl
  unfold AdvancedPast2 AdvanceEpidemics.SeededAdvanceWin
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · rw [Protocol.stepOrSelf_card_eq]
      exact hShell.1
    · intro a ha
      rw [hc'] at ha
      have ha' :
          a = (Transition L K s t).1 ∨ a ∈ c - {s, t} ∨
            a = (Transition L K s t).2 := by
        simpa using ha
      rcases ha' with rfl | haold | rfl
      · omega
      · have hac : a ∈ c :=
          Multiset.mem_of_le (Multiset.sub_le_self c {s, t}) haold
        exact (hShell.2 a hac).1.ge
      · omega
  · unfold AdvanceEpidemics.geCount
    have hmem :
        (Transition L K s t).1 ∈
          Protocol.stepOrSelf (NonuniformMajority L K) c s t := by
      rw [hc']
      simp
    have hge :
        AdvanceEpidemics.geP 3 (Transition L K s t).1 := by
      unfold AdvanceEpidemics.geP
      omega
    exact Multiset.countP_pos_of_mem hmem hge

/-- One scheduled pair either preserves the exact Phase-2 single-sign shell or
creates the common first-advance target. -/
theorem Phase2SingleShell_stepOrSelf_or_advanced
    (n : ℕ) (c : Config (AgentState L K))
    (hShell : Phase2SingleShell n c) (s t : AgentState L K) :
    Phase2SingleShell n
        (Protocol.stepOrSelf (NonuniformMajority L K) c s t) ∨
      AdvancedPast2 n
        (Protocol.stepOrSelf (NonuniformMajority L K) c s t) := by
  classical
  by_cases happ : Protocol.Applicable c s t
  · have hs_mem : s ∈ c := Multiset.mem_of_le happ (by simp)
    have ht_mem : t ∈ c := Multiset.mem_of_le happ (by simp)
    have hs := hShell.2 s hs_mem
    have ht := hShell.2 t ht_mem
    rcases Transition_phase2_singleSign_or_advance
        (L := L) (K := K) s t hs.1 ht.1 with hkeep | hadv
    · left
      have hc' :
          Protocol.stepOrSelf (NonuniformMajority L K) c s t =
            c - {s, t} + {(Transition L K s t).1, (Transition L K s t).2} := by
        unfold Protocol.stepOrSelf
        rw [if_pos happ]
        rfl
      refine ⟨?_, ?_⟩
      · rw [Protocol.stepOrSelf_card_eq]
        exact hShell.1
      · intro a ha
        rw [hc'] at ha
        have ha' :
            a = (Transition L K s t).1 ∨ a ∈ c - {s, t} ∨
              a = (Transition L K s t).2 := by
          simpa using ha
        rcases ha' with rfl | haold | rfl
        · exact ⟨hkeep.2.1, by simpa [hkeep.2.2.2.1] using hkeep.1⟩
        · exact hShell.2 a
            (Multiset.mem_of_le (Multiset.sub_le_self c {s, t}) haold)
        · exact ⟨hkeep.2.2.1, by simpa [hkeep.2.2.2.2] using hkeep.1⟩
    · right
      exact AdvancedPast2_stepOrSelf_of_phase3_pair n c hShell s t happ
        hadv.2.2.1 hadv.2.2.2
  · left
    rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]
    exact hShell

/-- A pure Phase-2 shell has not yet reached the common advance target. -/
theorem not_AdvancedPast2_of_Phase2SingleShell
    (n : ℕ) (c : Config (AgentState L K))
    (hShell : Phase2SingleShell n c) :
    ¬ AdvancedPast2 n c := by
  intro hadv
  have hzero : AdvanceEpidemics.geCount (L := L) (K := K) 3 c = 0 := by
    unfold AdvanceEpidemics.geCount
    rw [Multiset.countP_eq_zero]
    intro a ha
    unfold AdvanceEpidemics.geP
    have ha2 := (hShell.2 a ha).1
    omega
  unfold AdvancedPast2 AdvanceEpidemics.SeededAdvanceWin at hadv
  change _ ∧ 1 ≤ AdvanceEpidemics.geCount (L := L) (K := K) 3 c at hadv
  omega

/-- Before the first advance, a selected sign count is monotone; a conflicting
pair is recorded by the alternative target conclusion. -/
theorem signCount_stepOrSelf_le_or_advanced
    (sigma : Sign) (n : ℕ) (c : Config (AgentState L K))
    (hShell : Phase2SingleShell n c) (s t : AgentState L K) :
    AdvancedPast2 n
        (Protocol.stepOrSelf (NonuniformMajority L K) c s t) ∨
      signCount sigma c ≤ signCount sigma
        (Protocol.stepOrSelf (NonuniformMajority L K) c s t) := by
  classical
  by_cases happ : Protocol.Applicable c s t
  · have hs_mem : s ∈ c := Multiset.mem_of_le happ (by simp)
    have ht_mem : t ∈ c := Multiset.mem_of_le happ (by simp)
    have hpair := Transition_phase2_sign_pair_or_advance sigma s t
      (hShell.2 s hs_mem).1 (hShell.2 t ht_mem).1
    rcases hpair with hkeep | hadv
    · right
      have hc' :
          Protocol.stepOrSelf (NonuniformMajority L K) c s t =
            c - {s, t} + {(Transition L K s t).1, (Transition L K s t).2} := by
        unfold Protocol.stepOrSelf
        rw [if_pos happ]
        rfl
      have hsub : ({s, t} : Multiset (AgentState L K)) ≤ c := happ
      have hpair_le :
          Multiset.countP (carries sigma) {s, t} ≤
            Multiset.countP (carries sigma) c :=
        Multiset.countP_le_of_le (carries sigma) hsub
      unfold signCount
      rw [hc', Multiset.countP_add, Multiset.countP_sub hsub]
      rw [show ({s, t} : Multiset (AgentState L K)) = s ::ₘ t ::ₘ 0 from rfl,
        show ({(Transition L K s t).1, (Transition L K s t).2} :
          Multiset (AgentState L K)) =
            (Transition L K s t).1 ::ₘ (Transition L K s t).2 ::ₘ 0 from rfl]
      rw [Multiset.countP_cons, Multiset.countP_cons, Multiset.countP_zero,
        Multiset.countP_cons, Multiset.countP_cons, Multiset.countP_zero]
      by_cases hsC : carries sigma s <;> by_cases htC : carries sigma t
      · have hout := hkeep.2.2.2.2 (Or.inl hsC)
        simp [hsC, htC, hout.1, hout.2] at hpair_le ⊢
        omega
      · have hout := hkeep.2.2.2.2 (Or.inl hsC)
        simp [hsC, htC, hout.1, hout.2] at hpair_le ⊢
        omega
      · have hout := hkeep.2.2.2.2 (Or.inr htC)
        simp [hsC, htC, hout.1, hout.2] at hpair_le ⊢
        omega
      · simp [hsC, htC]
    · left
      exact AdvancedPast2_stepOrSelf_of_phase3_pair n c hShell s t happ
        hadv.1 hadv.2
  · right
    rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]

/-- A selected sign count is bounded by the population size. -/
theorem signCount_le_card (sigma : Sign)
    (c : Config (AgentState L K)) :
    signCount sigma c ≤ c.card := by
  unfold signCount
  exact Multiset.countP_le_card _ _

/-- A witnessed noncarrier makes the selected sign count strictly smaller
than the population size. -/
theorem signCount_lt_card_of_mem_not_carries
    (sigma : Sign) (c : Config (AgentState L K))
    (a : AgentState L K) (ha : a ∈ c) (hna : ¬ carries sigma a) :
    signCount sigma c < c.card := by
  have hle := signCount_le_card sigma c
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact hlt
  · exfalso
    have hall : ∀ b ∈ c, carries sigma b := by
      have heq' : Multiset.countP (carries sigma) c = c.card := by
        simpa [signCount] using heq
      exact Multiset.countP_eq_card.mp heq'
    exact hna (hall a ha)

/-- The common stopped rank is monotone under every scheduled pair while its
per-sign invariant holds. -/
theorem stoppedSignCount_stepOrSelf_le
    (sigma : Sign) (n : ℕ) (c : Config (AgentState L K))
    (hInv : SignRunInv sigma n c) (s t : AgentState L K) :
    stoppedSignCount sigma n c ≤ stoppedSignCount sigma n
      (Protocol.stepOrSelf (NonuniformMajority L K) c s t) := by
  rcases hInv with hadv | hactive
  · have hadv' := AdvancedPast2_stepOrSelf n c hadv s t
    simp [stoppedSignCount, hadv, hadv']
  · have hnot := not_AdvancedPast2_of_Phase2SingleShell n c hactive.1
    have hcount_le : signCount sigma c ≤ n := by
      rw [← hactive.1.1]
      exact signCount_le_card sigma c
    rcases signCount_stepOrSelf_le_or_advanced sigma n c hactive.1 s t with
        hadv' | hmono
    · simp [stoppedSignCount, hnot, hadv', hcount_le]
    · by_cases hadv' : AdvancedPast2 n
          (Protocol.stepOrSelf (NonuniformMajority L K) c s t)
      · simp [stoppedSignCount, hnot, hadv', hcount_le]
      · simpa [stoppedSignCount, hnot, hadv'] using hmono

/-- A selected carrier/noncarrier interaction raises the common stopped rank
by one.  If the pair is conflicting this is the terminal jump to `n`; otherwise
ordinary opinion union creates one additional carrier. -/
theorem stoppedSignCount_stepOrSelf_advance
    (sigma : Sign) (n : ℕ) (c : Config (AgentState L K))
    (hShell : Phase2SingleShell n c) (s t : AgentState L K)
    (happ : Protocol.Applicable c s t)
    (hsCarrier : carries sigma s) (htCarrier : ¬ carries sigma t) :
    stoppedSignCount sigma n c + 1 ≤ stoppedSignCount sigma n
      (Protocol.stepOrSelf (NonuniformMajority L K) c s t) := by
  classical
  have hs_mem : s ∈ c := Multiset.mem_of_le happ (by simp)
  have ht_mem : t ∈ c := Multiset.mem_of_le happ (by simp)
  have hnot := not_AdvancedPast2_of_Phase2SingleShell n c hShell
  have hlt : signCount sigma c < n := by
    rw [← hShell.1]
    exact signCount_lt_card_of_mem_not_carries sigma c t ht_mem htCarrier
  have hpair := Transition_phase2_sign_pair_or_advance sigma s t
    (hShell.2 s hs_mem).1 (hShell.2 t ht_mem).1
  rcases hpair with hkeep | hadvPair
  · by_cases hadv' : AdvancedPast2 n
        (Protocol.stepOrSelf (NonuniformMajority L K) c s t)
    · simp [stoppedSignCount, hnot, hadv']
      omega
    · have hcur : stoppedSignCount sigma n c = signCount sigma c := by
        simp [stoppedSignCount, hnot]
      have hnext : stoppedSignCount sigma n
          (Protocol.stepOrSelf (NonuniformMajority L K) c s t) =
            signCount sigma
              (Protocol.stepOrSelf (NonuniformMajority L K) c s t) := by
        simp [stoppedSignCount, hadv']
      rw [hcur, hnext]
      have hout := hkeep.2.2.2.2 (Or.inl hsCarrier)
      have hsub : ({s, t} : Multiset (AgentState L K)) ≤ c := happ
      have hc' :
          Protocol.stepOrSelf (NonuniformMajority L K) c s t =
            c - {s, t} + {(Transition L K s t).1, (Transition L K s t).2} := by
        unfold Protocol.stepOrSelf
        rw [if_pos happ]
        rfl
      unfold signCount
      rw [hc', Multiset.countP_add, Multiset.countP_sub hsub]
      have hpair_le :
          Multiset.countP (carries sigma) {s, t} ≤
            Multiset.countP (carries sigma) c :=
        Multiset.countP_le_of_le (carries sigma) hsub
      have hold : Multiset.countP (carries sigma) {s, t} = 1 := by
        rw [show ({s, t} : Multiset (AgentState L K)) = s ::ₘ t ::ₘ 0 from rfl,
          Multiset.countP_cons, Multiset.countP_cons, Multiset.countP_zero]
        simp [hsCarrier, htCarrier]
      have hnew :
          Multiset.countP (carries sigma)
              {(Transition L K s t).1, (Transition L K s t).2} = 2 := by
        rw [show ({(Transition L K s t).1, (Transition L K s t).2} :
            Multiset (AgentState L K)) =
              (Transition L K s t).1 ::ₘ (Transition L K s t).2 ::ₘ 0 from rfl,
          Multiset.countP_cons, Multiset.countP_cons, Multiset.countP_zero]
        simp [hout.1, hout.2]
      rw [hold] at hpair_le ⊢
      rw [hnew]
      omega
  · have hadv' := AdvancedPast2_stepOrSelf_of_phase3_pair n c hShell s t happ
      hadvPair.1 hadvPair.2
    simp [stoppedSignCount, hnot, hadv']
    omega

/-- The per-sign real-kernel invariant is preserved by every scheduled pair. -/
theorem SignRunInv_stepOrSelf
    (sigma : Sign) (n : ℕ) (c : Config (AgentState L K))
    (hInv : SignRunInv sigma n c) (s t : AgentState L K) :
    SignRunInv sigma n
      (Protocol.stepOrSelf (NonuniformMajority L K) c s t) := by
  rcases hInv with hadv | hactive
  · exact Or.inl (AdvancedPast2_stepOrSelf n c hadv s t)
  · rcases signCount_stepOrSelf_le_or_advanced sigma n c hactive.1 s t with
      hadv | hmono
    · exact Or.inl hadv
    · rcases Phase2SingleShell_stepOrSelf_or_advanced n c hactive.1 s t with
        hShell | hadv
      · exact Or.inr ⟨hShell, le_trans hactive.2 hmono⟩
      · exact Or.inl hadv

/-- Closure of the per-sign invariant under one protocol relation step. -/
theorem SignRunInv_stepRel
    (sigma : Sign) (n : ℕ) {c c' : Config (AgentState L K)}
    (hInv : SignRunInv sigma n c)
    (hstep : (NonuniformMajority L K).StepRel c c') :
    SignRunInv sigma n c' := by
  rcases hstep with ⟨s, t, happ, hc'⟩
  dsimp at hc'
  have heq :
      Protocol.stepOrSelf (NonuniformMajority L K) c s t = c' := by
    unfold Protocol.stepOrSelf
    rw [if_pos happ]
    exact hc'.symm
  rw [← heq]
  exact SignRunInv_stepOrSelf sigma n c hInv s t

/-- Closure of the per-sign invariant along every finite execution. -/
theorem SignRunInv_reachable
    (sigma : Sign) (n : ℕ) {c c' : Config (AgentState L K)}
    (hInv : SignRunInv sigma n c)
    (hreach : (NonuniformMajority L K).Reachable c c') :
    SignRunInv sigma n c' := by
  induction hreach with
  | refl => exact hInv
  | tail _ hstep ih => exact SignRunInv_stepRel sigma n ih hstep

/-- Scheduler-support closure of the per-sign invariant. -/
theorem SignRunInv_of_stepDistOrSelf_support
    (sigma : Sign) (n : ℕ) (c c' : Config (AgentState L K))
    (hInv : SignRunInv sigma n c)
    (hsupp : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    SignRunInv sigma n c' :=
  SignRunInv_reachable sigma n hInv
    (Protocol.stepDistOrSelf_support_reachable
      (NonuniformMajority L K) c c' hsupp)

/-- Stopped-rank monotonicity under one protocol relation step. -/
theorem stoppedSignCount_stepRel_le
    (sigma : Sign) (n : ℕ) {c c' : Config (AgentState L K)}
    (hInv : SignRunInv sigma n c)
    (hstep : (NonuniformMajority L K).StepRel c c') :
    stoppedSignCount sigma n c ≤ stoppedSignCount sigma n c' := by
  rcases hstep with ⟨s, t, happ, hc'⟩
  dsimp at hc'
  have heq :
      Protocol.stepOrSelf (NonuniformMajority L K) c s t = c' := by
    unfold Protocol.stepOrSelf
    rw [if_pos happ]
    exact hc'.symm
  rw [← heq]
  exact stoppedSignCount_stepOrSelf_le sigma n c hInv s t

/-- Stopped-rank monotonicity along every finite execution. -/
theorem stoppedSignCount_reachable_le
    (sigma : Sign) (n : ℕ) {c c' : Config (AgentState L K)}
    (hInv : SignRunInv sigma n c)
    (hreach : (NonuniformMajority L K).Reachable c c') :
    stoppedSignCount sigma n c ≤ stoppedSignCount sigma n c' := by
  induction hreach with
  | refl => exact le_rfl
  | @tail b d hprefix hstep ih =>
      exact le_trans ih
        (stoppedSignCount_stepRel_le sigma n
          (SignRunInv_reachable sigma n hInv hprefix) hstep)

/-- Scheduler-support form of stopped-rank monotonicity. -/
theorem stoppedSignCount_of_stepDistOrSelf_support_le
    (sigma : Sign) (n : ℕ) (c c' : Config (AgentState L K))
    (hInv : SignRunInv sigma n c)
    (hsupp : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    stoppedSignCount sigma n c ≤ stoppedSignCount sigma n c' :=
  stoppedSignCount_reachable_le sigma n hInv
    (Protocol.stepDistOrSelf_support_reachable
      (NonuniformMajority L K) c c' hsupp)

/-! ## The two sign rectangles and one-step progress -/

/-- States carrying one selected sign. -/
noncomputable def signStates (sigma : Sign) : Finset (AgentState L K) :=
  Finset.univ.filter (carries sigma)

/-- States not carrying the selected sign. -/
noncomputable def nonsignStates (sigma : Sign) : Finset (AgentState L K) :=
  Finset.univ.filter (fun a => ¬ carries sigma a)

theorem signStates_nonsignStates_disjoint
    (sigma : Sign) (a : AgentState L K) (ha : a ∈ signStates sigma)
    (b : AgentState L K) (hb : b ∈ nonsignStates sigma) : a ≠ b := by
  simp only [signStates, nonsignStates, Finset.mem_filter] at ha hb
  intro hab
  subst b
  exact hb.2 ha.2

private theorem sum_count_filter_eq_countP
    (p : AgentState L K → Prop) [DecidablePred p]
    (c : Config (AgentState L K)) :
    (∑ a ∈ Finset.univ.filter p, c.count a) = Multiset.countP p c := by
  classical
  calc
    (∑ a ∈ Finset.univ.filter p, c.count a)
        = ∑ a : AgentState L K, if p a then c.count a else 0 :=
          Finset.sum_filter _ _
    _ = ∑ a : AgentState L K, (c.filter p).count a := by
      refine Finset.sum_congr rfl (fun a _ => ?_)
      show _ = Multiset.count a (c.filter p)
      rw [Multiset.count_filter]
      rfl
    _ = (c.filter p).card :=
      Multiset.sum_count_eq_card (fun a _ => Finset.mem_univ a)
    _ = Multiset.countP p c := (Multiset.countP_eq_card_filter _ _).symm

private theorem signCount_add_nonsignCount
    (sigma : Sign) (c : Config (AgentState L K)) :
    signCount sigma c +
        Multiset.countP (fun a : AgentState L K => ¬ carries sigma a) c =
      c.card := by
  classical
  induction c using Multiset.induction_on with
  | empty => simp [signCount]
  | @cons a c ih =>
      unfold signCount at ih ⊢
      rw [Multiset.countP_cons, Multiset.countP_cons, Multiset.card_cons]
      by_cases h : carries sigma a <;> simp [h] at ih ⊢ <;> omega

/-- Exact scheduler weight of the selected-sign/non-sign rectangle. -/
theorem sum_interactionCount_signRect
    (sigma : Sign) (c : Config (AgentState L K)) :
    (∑ p ∈ signStates (L := L) (K := K) sigma ×ˢ
        nonsignStates (L := L) (K := K) sigma,
        c.interactionCount p.1 p.2) =
      signCount sigma c * (c.card - signCount sigma c) := by
  classical
  rw [Phase5Convergence.sum_interactionCount_cross_disjoint5 c _ _
      (signStates_nonsignStates_disjoint sigma),
    signStates, nonsignStates,
    sum_count_filter_eq_countP, sum_count_filter_eq_countP]
  have hsplit := signCount_add_nonsignCount sigma c
  have hle := signCount_le_card sigma c
  have hnon :
      Multiset.countP (fun a : AgentState L K => ¬ carries sigma a) c =
        c.card - signCount sigma c := by
    omega
  rw [hnon]
  rfl

/-- Genuine one-step progress rate for either selected sign, measured against
the common stopped rank.  Conflicting pairs count as successful terminal
jumps, so the ordinary rumor rectangle remains a valid lower bound. -/
theorem sign_advance_prob
    (sigma : Sign) (n : ℕ) (hn : 2 ≤ n)
    (c : Config (AgentState L K)) (hShell : Phase2SingleShell n c) :
    ENNReal.ofReal
        (((signCount sigma c * (n - signCount sigma c) : ℕ) : ℝ) /
          ((n : ℝ) * ((n : ℝ) - 1))) ≤
      ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
        {c' | stoppedSignCount sigma n c + 1 ≤
          stoppedSignCount sigma n c'} := by
  classical
  set R := signStates (L := L) (K := K) sigma ×ˢ
    nonsignStates (L := L) (K := K) sigma with hR
  refine Phase5Convergence.rise_prob_of_rect5
    (stoppedSignCount (L := L) (K := K) sigma n) n hn c hShell.1 R
      (signCount sigma c * (n - signCount sigma c)) ?_ ?_
  · rintro ⟨s, t⟩ hp hsCount htCount _hsame
    rw [hR, Finset.mem_product, signStates, nonsignStates,
      Finset.mem_filter, Finset.mem_filter] at hp
    obtain ⟨⟨_, hsCarrier⟩, ⟨_, htCarrier⟩⟩ := hp
    have hs_mem : s ∈ c := Multiset.one_le_count_iff_mem.mp hsCount
    have ht_mem : t ∈ c := Multiset.one_le_count_iff_mem.mp htCount
    have hne : s ≠ t := by
      intro hst
      subst t
      exact htCarrier hsCarrier
    have happ : Protocol.Applicable c s t :=
      Phase5Convergence.applicable_of_mem_distinct5 hs_mem ht_mem hne
    exact stoppedSignCount_stepOrSelf_advance sigma n c hShell s t happ
      hsCarrier htCarrier
  · rw [hR, sum_interactionCount_signRect, hShell.1]

/-! ## Per-sign milestones on the common real kernel -/

/-- A selected-sign milestone, guarded by the real-kernel invariant. -/
def signMilestone (sigma : Sign) (n i : ℕ)
    (c : Config (AgentState L K)) : Prop :=
  SignRunInv sigma n c ∧ i + 2 ≤ stoppedSignCount sigma n c

/-- The shared stopped rank never exceeds `n` on its invariant. -/
theorem stoppedSignCount_le_of_inv
    (sigma : Sign) (n : ℕ) (c : Config (AgentState L K))
    (hInv : SignRunInv sigma n c) :
    stoppedSignCount sigma n c ≤ n := by
  rcases hInv with hadv | hactive
  · simp [stoppedSignCount, hadv]
  · have hnot := not_AdvancedPast2_of_Phase2SingleShell n c hactive.1
    rw [show stoppedSignCount sigma n c = signCount sigma c by
      simp [stoppedSignCount, hnot]]
    rw [← hactive.1.1]
    exact signCount_le_card sigma c

/-- Canonical rumor-rate milestones for one selected sign.  Both instances
use the same protocol kernel and the same target-stopped rank. -/
noncomputable def signMilestonePhase
    (sigma : Sign) (n : ℕ) (hn : 2 ≤ n) :
    RoleSplitConcentration.MilestonePhaseOn
      (L := L) (K := K) (NonuniformMajority L K) where
  k := n - 1
  milestone i c := signMilestone (L := L) (K := K) sigma n i.val c
  p i := Phase2Time.epP n i.val
  hp_pos i := Phase2Time.epP_pos hn (by have := i.isLt; omega)
  hp_le_one i := Phase2Time.epP_le_one hn (by have := i.isLt; omega)
  milestone_monotone := by
    intro i c c' h hsupp
    exact ⟨
      SignRunInv_of_stepDistOrSelf_support sigma n c c' h.1 hsupp,
      le_trans h.2
        (stoppedSignCount_of_stepDistOrSelf_support_le
          sigma n c c' h.1 hsupp)⟩
  Inv := SignRunInv sigma n
  inv_closed := by
    intro c hInv
    change ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
      {c' | ¬ SignRunInv sigma n c'} = 0
    rw [PMF.toMeasure_apply_eq_zero_iff
      (p := (NonuniformMajority L K).stepDistOrSelf c)
      (DiscreteMeasurableSpace.forall_measurableSet _)]
    rw [Set.disjoint_left]
    intro c' hsupp hbad
    exact hbad (SignRunInv_of_stepDistOrSelf_support sigma n c c' hInv hsupp)
  progress_on := by
    intro i c hInv hprev hcur
    have hnot : ¬ AdvancedPast2 n c := by
      intro hadv
      apply hcur
      refine ⟨hInv, ?_⟩
      simp [stoppedSignCount, hadv]
      have := i.isLt
      omega
    have hactive : Phase2SingleShell n c ∧ 1 ≤ signCount sigma c := by
      rcases hInv with hadv | hactive
      · exact (hnot hadv).elim
      · exact hactive
    have hstop : stoppedSignCount sigma n c = signCount sigma c := by
      simp [stoppedSignCount, hnot]
    have hcount_eq : signCount sigma c = i.val + 1 := by
      have hlt : signCount sigma c < i.val + 2 := by
        exact Nat.lt_of_not_ge (fun hge => hcur ⟨hInv, by simpa [hstop] using hge⟩)
      have hge : i.val + 1 ≤ signCount sigma c := by
        by_cases hi0 : i.val = 0
        · rw [hi0]
          exact hactive.2
        · have hprev' := hprev ⟨i.val - 1, by omega⟩ (by
            exact Fin.mk_lt_mk.mpr (by omega))
          have hprev_cov :
              (i.val - 1) + 2 ≤ stoppedSignCount sigma n c := hprev'.2
          rw [hstop] at hprev_cov
          omega
      omega
    have hbound := sign_advance_prob sigma n hn c hactive.1
    have heq :
        ((((signCount sigma c * (n - signCount sigma c) : ℕ) : ℝ) /
          ((n : ℝ) * ((n : ℝ) - 1)))) = Phase2Time.epP n i.val := by
      rw [hcount_eq]
      unfold Phase2Time.epP
      have hi1_le : i.val + 1 ≤ n := by
        have := i.isLt
        omega
      rw [Nat.cast_mul, Nat.cast_sub hi1_le, Nat.cast_add, Nat.cast_one]
    rw [heq] at hbound
    set A := {c' : Config (AgentState L K) |
      i.val + 2 ≤ stoppedSignCount sigma n c'}
    set M := {c' : Config (AgentState L K) |
      signMilestone (L := L) (K := K) sigma n i.val c'}
    have hA_le_M :
        ((NonuniformMajority L K).stepDistOrSelf c).toMeasure A ≤
          ((NonuniformMajority L K).stepDistOrSelf c).toMeasure M := by
      have hsub :
          A ⊆ M ∪ {c' : Config (AgentState L K) | ¬ SignRunInv sigma n c'} := by
        intro x hx
        by_cases hxInv : SignRunInv sigma n x
        · left
          exact ⟨hxInv, hx⟩
        · right
          exact hxInv
      have hclosed :
          ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
            {c' : Config (AgentState L K) | ¬ SignRunInv sigma n c'} = 0 := by
        rw [PMF.toMeasure_apply_eq_zero_iff
          (p := (NonuniformMajority L K).stepDistOrSelf c)
          (DiscreteMeasurableSpace.forall_measurableSet _)]
        rw [Set.disjoint_left]
        intro c' hsupp hbad
        exact hbad
          (SignRunInv_of_stepDistOrSelf_support sigma n c c' hInv hsupp)
      calc
        ((NonuniformMajority L K).stepDistOrSelf c).toMeasure A
            ≤ ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
                (M ∪ {c' : Config (AgentState L K) | ¬ SignRunInv sigma n c'}) :=
              measure_mono hsub
        _ ≤ ((NonuniformMajority L K).stepDistOrSelf c).toMeasure M +
              ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
                {c' : Config (AgentState L K) | ¬ SignRunInv sigma n c'} :=
              measure_union_le M _
        _ = ((NonuniformMajority L K).stepDistOrSelf c).toMeasure M := by
              rw [hclosed, add_zero]
    have hboundA : ENNReal.ofReal (Phase2Time.epP n i.val) ≤
        ((NonuniformMajority L K).stepDistOrSelf c).toMeasure A := by
      simpa [A, hstop, hcount_eq, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hbound
    exact le_trans hboundA hA_le_M

theorem signMilestone_pMin_eq_epidemic
    (sigma : Sign) (n : ℕ) (hn : 2 ≤ n) :
    (signMilestonePhase (L := L) (K := K) sigma n hn).pMin =
      (Phase2Time.epidemicMilestonePhase n hn).pMin := rfl

theorem signMilestone_meanTime_eq_epidemic
    (sigma : Sign) (n : ℕ) (hn : 2 ≤ n) :
    (signMilestonePhase (L := L) (K := K) sigma n hn).meanTime =
      (Phase2Time.epidemicMilestonePhase n hn).meanTime := rfl

/-- Reaching every milestone for one sign gives its invariant and terminal
stopped rank. -/
theorem signMilestone_post_imp_inv_and_stopped_eq
    (sigma : Sign) (n : ℕ) (hn : 2 ≤ n)
    (c : Config (AgentState L K))
    (hPost :
      (signMilestonePhase (L := L) (K := K) sigma n hn).Post c) :
    SignRunInv sigma n c ∧ stoppedSignCount sigma n c = n := by
  let i : Fin ((signMilestonePhase
      (L := L) (K := K) sigma n hn).k) :=
    ⟨n - 2, by
      change n - 2 < n - 1
      omega⟩
  have hi := hPost i
  change signMilestone (L := L) (K := K) sigma n i.val c at hi
  have hival : i.val = n - 2 := rfl
  rw [hival] at hi
  have hge : n ≤ stoppedSignCount sigma n c := by
    have := hi.2
    omega
  exact ⟨hi.1, le_antisymm (stoppedSignCount_le_of_inv sigma n c hi.1) hge⟩

/-- If both selected-sign milestone phases finish on the same state, the common
first-advance target has been reached. -/
theorem dual_signMilestone_post_imp_advanced
    (n : ℕ) (hn : 2 ≤ n) (c : Config (AgentState L K))
    (hpos :
      (signMilestonePhase (L := L) (K := K) Sign.pos n hn).Post c)
    (hneg :
      (signMilestonePhase (L := L) (K := K) Sign.neg n hn).Post c) :
    AdvancedPast2 n c := by
  have hp := signMilestone_post_imp_inv_and_stopped_eq Sign.pos n hn c hpos
  have hm := signMilestone_post_imp_inv_and_stopped_eq Sign.neg n hn c hneg
  by_contra hnot
  have hpactive : Phase2SingleShell n c ∧ 1 ≤ signCount Sign.pos c :=
    hp.1.resolve_left hnot
  have hmactive : Phase2SingleShell n c ∧ 1 ≤ signCount Sign.neg c :=
    hm.1.resolve_left hnot
  have hpcount : signCount Sign.pos c = n := by
    simpa [stoppedSignCount, hnot] using hp.2
  have hmcount : signCount Sign.neg c = n := by
    simpa [stoppedSignCount, hnot] using hm.2
  have hpEqCard : Multiset.countP (carries Sign.pos) c = c.card := by
    unfold signCount at hpcount
    rw [hpactive.1.1]
    exact hpcount
  have hmEqCard : Multiset.countP (carries Sign.neg) c = c.card := by
    unfold signCount at hmcount
    rw [hmactive.1.1]
    exact hmcount
  have hallPos : ∀ a ∈ c, carries Sign.pos a :=
    Multiset.countP_eq_card.mp hpEqCard
  have hallNeg : ∀ a ∈ c, carries Sign.neg a :=
    Multiset.countP_eq_card.mp hmEqCard
  have hcardPos : 0 < c.card := by
    rw [hpactive.1.1]
    omega
  obtain ⟨a, ha⟩ := Multiset.card_pos_iff_exists_mem.mp hcardPos
  have hsingle := (hpactive.1.2 a ha).2
  exact hsingle (by
    simpa [carries] using And.intro (hallNeg a ha) (hallPos a ha))

/-! ## Same-measure dual Janson tail -/

/-- One selected sign reaches all of its milestones with the canonical
half-inverse-square budget. -/
theorem signMilestone_tail_le_tightBudget
    (sigma : Sign) (n : ℕ) (hn : 2 ≤ n)
    (c : Config (AgentState L K)) (hInv : SignRunInv sigma n c) :
    ((NonuniformMajority L K).transitionKernel ^
        TightEpidemicWork.epiHorizonTight n hn) c
        {c' | ¬ (signMilestonePhase
          (L := L) (K := K) sigma n hn).Post c'} ≤
      ((TightEpidemicWork.tightBudget n : ℝ≥0) : ℝ≥0∞) := by
  set mp := signMilestonePhase (L := L) (K := K) sigma n hn with hmp
  have ht :
      (6 : ℝ) * mp.meanTime ≤
        (TightEpidemicWork.epiHorizonTight n hn : ℝ) := by
    rw [hmp]
    unfold TightEpidemicWork.epiHorizonTight
    exact Nat.le_ceil _
  have hj := mp.milestone_hitting_time_bound_on_partial c (by
      rw [hmp]
      exact hInv) 6 (by norm_num)
    (TightEpidemicWork.epiHorizonTight n hn) ht
  have hexp :=
    TightEpidemicWork.epidemic_janson_exp_le_half_inv_sq
      (L := L) (K := K) mp n hn
      (by rw [hmp]; exact signMilestone_pMin_eq_epidemic sigma n hn)
      (by rw [hmp]; exact signMilestone_meanTime_eq_epidemic sigma n hn)
  have htail :
      ((NonuniformMajority L K).transitionKernel ^
          TightEpidemicWork.epiHorizonTight n hn) c
          {c' | ¬ mp.Post c'} ≤
        ENNReal.ofReal (1 / (2 * (n : ℝ) ^ 2)) :=
    le_trans hj (ENNReal.ofReal_le_ofReal hexp)
  calc
    ((NonuniformMajority L K).transitionKernel ^
        TightEpidemicWork.epiHorizonTight n hn) c
        {c' | ¬ (signMilestonePhase
          (L := L) (K := K) sigma n hn).Post c'}
        ≤ ENNReal.ofReal (1 / (2 * (n : ℝ) ^ 2)) := htail
    _ = ((TightEpidemicWork.tightBudget n : ℝ≥0) : ℝ≥0∞) := by
      rw [TightEpidemicWork.tightBudget,
        ← ENNReal.ofReal_coe_nnreal, Real.coe_toNNReal]
      positivity

/-- The two half-budgets used by the positive/negative union bound. -/
noncomputable def advanceTailBudget (n : ℕ) : ℝ≥0 :=
  TightEpidemicWork.tightBudget n +
    TightEpidemicWork.tightBudget n

/-- The two half-budgets add to at most the advertised inverse-square budget. -/
theorem advanceTailBudget_le_inv_sq (n : ℕ) (hn : 2 ≤ n) :
    advanceTailBudget n ≤ Real.toNNReal (1 / (n : ℝ) ^ 2) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hhalf : 0 ≤ (1 / (2 * (n : ℝ) ^ 2) : ℝ) := by positivity
  have hfull : 0 ≤ (1 / ((n : ℝ) ^ 2) : ℝ) := by positivity
  rw [← NNReal.coe_le_coe]
  simp only [advanceTailBudget, TightEpidemicWork.tightBudget, NNReal.coe_add]
  rw [Real.coe_toNNReal _ hhalf, Real.coe_toNNReal _ hfull]
  field_simp
  norm_num

/-- Both sign failures are measured under the same real-kernel law.  A state
which is not advanced must fail at least one sign milestone postcondition, so a
single union bound gives the first-advance tail. -/
theorem advancedPast2_tail_le_advanceTailBudget
    (n : ℕ) (hn : 2 ≤ n) (c : Config (AgentState L K))
    (hActive : Active2Core n c) :
    ((NonuniformMajority L K).transitionKernel ^
        TightEpidemicWork.epiHorizonTight n hn) c
        {c' | ¬ AdvancedPast2 n c'} ≤
      ((advanceTailBudget n : ℝ≥0) : ℝ≥0∞) := by
  let μ := ((NonuniformMajority L K).transitionKernel ^
    TightEpidemicWork.epiHorizonTight n hn) c
  let Bpos := {c' : Config (AgentState L K) |
    ¬ (signMilestonePhase
      (L := L) (K := K) Sign.pos n hn).Post c'}
  let Bneg := {c' : Config (AgentState L K) |
    ¬ (signMilestonePhase
      (L := L) (K := K) Sign.neg n hn).Post c'}
  have hsub : {c' : Config (AgentState L K) | ¬ AdvancedPast2 n c'} ⊆
      Bpos ∪ Bneg := by
    intro c' hbad
    by_cases hp :
        (signMilestonePhase
          (L := L) (K := K) Sign.pos n hn).Post c'
    · right
      intro hm
      exact hbad (dual_signMilestone_post_imp_advanced n hn c' hp hm)
    · left
      exact hp
  have hpTail := signMilestone_tail_le_tightBudget
    Sign.pos n hn c (signRunInv_of_active Sign.pos n c hActive)
  have hmTail := signMilestone_tail_le_tightBudget
    Sign.neg n hn c (signRunInv_of_active Sign.neg n c hActive)
  calc
    μ {c' | ¬ AdvancedPast2 n c'}
        ≤ μ (Bpos ∪ Bneg) := measure_mono hsub
    _ ≤ μ Bpos + μ Bneg := measure_union_le Bpos Bneg
    _ ≤ ((TightEpidemicWork.tightBudget n : ℝ≥0) : ℝ≥0∞) +
          ((TightEpidemicWork.tightBudget n : ℝ≥0) : ℝ≥0∞) := by
      exact add_le_add (by simpa [μ, Bpos] using hpTail)
        (by simpa [μ, Bneg] using hmTail)
    _ = ((advanceTailBudget n : ℝ≥0) : ℝ≥0∞) := by
      simp [advanceTailBudget]

/-- Public four-way-advance convergence package. -/
noncomputable def phase2AdvanceConvergence
    (n : ℕ) (hn : 2 ≤ n) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel where
  Pre := Active2Core n
  Post := AdvancedPast2 n
  t := TightEpidemicWork.epiHorizonTight n hn
  ε := advanceTailBudget n
  convergence := by
    intro c hPre
    exact advancedPast2_tail_le_advanceTailBudget n hn c hPre

/-! ## First-crossing support bridge -/

/-- If a chosen-pair successor of the pure Phase-2 shell reaches the common
target, it is necessarily the exact Phase-3 first-entry shell. -/
theorem Phase23FirstEntry_of_stepOrSelf_advanced
    (n : ℕ) (c : Config (AgentState L K))
    (hShell : Phase2SingleShell n c) (s t : AgentState L K)
    (hadv : AdvancedPast2 n
      (Protocol.stepOrSelf (NonuniformMajority L K) c s t)) :
    Phase23FirstEntry n
      (Protocol.stepOrSelf (NonuniformMajority L K) c s t) := by
  classical
  by_cases happ : Protocol.Applicable c s t
  · have hs_mem : s ∈ c := Multiset.mem_of_le happ (by simp)
    have ht_mem : t ∈ c := Multiset.mem_of_le happ (by simp)
    rcases Transition_phase2_singleSign_or_advance
        (L := L) (K := K) s t
        (hShell.2 s hs_mem).1 (hShell.2 t ht_mem).1 with hkeep | hconf
    · exfalso
      apply not_AdvancedPast2_of_Phase2SingleShell n
        (Protocol.stepOrSelf (NonuniformMajority L K) c s t) _ hadv
      have hc' :
          Protocol.stepOrSelf (NonuniformMajority L K) c s t =
            c - {s, t} + {(Transition L K s t).1, (Transition L K s t).2} := by
        unfold Protocol.stepOrSelf
        rw [if_pos happ]
        rfl
      refine ⟨?_, ?_⟩
      · rw [Protocol.stepOrSelf_card_eq]
        exact hShell.1
      · intro a ha
        rw [hc'] at ha
        have ha' :
            a = (Transition L K s t).1 ∨ a ∈ c - {s, t} ∨
              a = (Transition L K s t).2 := by
          simpa using ha
        rcases ha' with rfl | haold | rfl
        · exact ⟨hkeep.2.1, by simpa [hkeep.2.2.2.1] using hkeep.1⟩
        · exact hShell.2 a
            (Multiset.mem_of_le (Multiset.sub_le_self c {s, t}) haold)
        · exact ⟨hkeep.2.2.1, by simpa [hkeep.2.2.2.2] using hkeep.1⟩
    · exact Phase23FirstEntry_stepOrSelf_of_conflicting_pair n c hShell s t happ
        hconf.1 hconf.2.1
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ] at hadv ⊢
    exact (not_AdvancedPast2_of_Phase2SingleShell n c hShell hadv).elim

/-- Real one-step scheduler support cannot enter the target anywhere except
through the exact Phase-3 first-entry shell. -/
theorem Phase23FirstEntry_of_real_support
    (n : ℕ) (c c' : Config (AgentState L K))
    (hShell : Phase2SingleShell n c)
    (hsupp : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support)
    (hadv : AdvancedPast2 n c') :
    Phase23FirstEntry n c' := by
  unfold Protocol.stepDistOrSelf at hsupp
  by_cases hc2 : 2 ≤ c.card
  · rw [dif_pos hc2] at hsupp
    obtain ⟨⟨s, t⟩, hstep⟩ :=
      Protocol.stepDist_support (NonuniformMajority L K) c hc2 c' hsupp
    rw [show Protocol.scheduledStep (NonuniformMajority L K) c (s, t) =
        Protocol.stepOrSelf (NonuniformMajority L K) c s t from rfl] at hstep
    rw [← hstep] at hadv ⊢
    exact Phase23FirstEntry_of_stepOrSelf_advanced n c hShell s t hadv
  · rw [dif_neg hc2, PMF.mem_support_pure_iff] at hsupp
    subst c'
    exact (not_AdvancedPast2_of_Phase2SingleShell n c hShell hadv).elim

/-- One-step first-entry support theorem for the common stopped kernel.  From
the Phase-2 shell, its mass on an advanced state without the exact initializer
payload is zero. -/
theorem advanceStopK_first_entry_support
    (n : ℕ) (c : Config (AgentState L K))
    (hShell : Phase2SingleShell n c) :
    advanceStopK (L := L) (K := K) n c
        {c' | AdvancedPast2 n c' ∧ ¬ Phase23FirstEntry n c'} = 0 := by
  have hnot := not_AdvancedPast2_of_Phase2SingleShell n c hShell
  rw [advanceStopK_eq_real_of_not_advanced n c hnot]
  change ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
      {c' | AdvancedPast2 n c' ∧ ¬ Phase23FirstEntry n c'} = 0
  rw [PMF.toMeasure_apply_eq_zero_iff
    (p := (NonuniformMajority L K).stepDistOrSelf c)
    (DiscreteMeasurableSpace.forall_measurableSet _)]
  rw [Set.disjoint_left]
  intro c' hsupp hbad
  exact hbad.2 (Phase23FirstEntry_of_real_support n c c' hShell hsupp hbad.1)

/-- A real-kernel support successor which has not advanced remains in the pure
Phase-2 shell. -/
theorem Phase2SingleShell_of_real_support_not_advanced
    (n : ℕ) (c c' : Config (AgentState L K))
    (hShell : Phase2SingleShell n c)
    (hsupp : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support)
    (hnot : ¬ AdvancedPast2 n c') :
    Phase2SingleShell n c' := by
  unfold Protocol.stepDistOrSelf at hsupp
  by_cases hc2 : 2 ≤ c.card
  · rw [dif_pos hc2] at hsupp
    obtain ⟨⟨s, t⟩, hstep⟩ :=
      Protocol.stepDist_support (NonuniformMajority L K) c hc2 c' hsupp
    rw [show Protocol.scheduledStep (NonuniformMajority L K) c (s, t) =
        Protocol.stepOrSelf (NonuniformMajority L K) c s t from rfl] at hstep
    rw [← hstep] at hnot ⊢
    rcases Phase2SingleShell_stepOrSelf_or_advanced n c hShell s t with
        hShell' | hadv
    · exact hShell'
    · exact (hnot hadv).elim
  · rw [dif_neg hc2, PMF.mem_support_pure_iff] at hsupp
    subst c'
    exact hShell

/-- The exact first-entry shell itself satisfies the common advance target. -/
theorem AdvancedPast2_of_Phase23FirstEntry
    (n : ℕ) (c : Config (AgentState L K))
    (hFirst : Phase23FirstEntry n c) :
    AdvancedPast2 n c := by
  unfold AdvancedPast2 AdvanceEpidemics.SeededAdvanceWin
  refine ⟨?_, ?_⟩
  · refine ⟨hFirst.1, ?_⟩
    intro a ha
    rcases hFirst.2.1 a ha with ha2 | ha3
    · omega
    · have := ha3.1
      omega
  · rcases hFirst.2.2 with ⟨a, ha, haEntry⟩
    unfold AdvanceEpidemics.geCount
    apply Multiset.countP_pos_of_mem ha
    unfold AdvanceEpidemics.geP
    exact haEntry.1.ge

/-- The stopped-chain safety predicate: it is either still in the pure Phase-2
shell or frozen at the exact first-entry payload. -/
def StoppedSafe (n : ℕ) (c : Config (AgentState L K)) : Prop :=
  Phase2SingleShell n c ∨ Phase23FirstEntry n c

/-- One stopped-kernel step preserves the pathwise safety predicate with
probability one. -/
theorem advanceStopK_safe_one_step
    (n : ℕ) (c : Config (AgentState L K))
    (hSafe : StoppedSafe n c) :
    advanceStopK (L := L) (K := K) n c {c' | ¬ StoppedSafe n c'} = 0 := by
  rcases hSafe with hShell | hFirst
  · have hnot := not_AdvancedPast2_of_Phase2SingleShell n c hShell
    rw [advanceStopK_eq_real_of_not_advanced n c hnot]
    change ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
      {c' | ¬ StoppedSafe n c'} = 0
    rw [PMF.toMeasure_apply_eq_zero_iff
      (p := (NonuniformMajority L K).stepDistOrSelf c)
      (DiscreteMeasurableSpace.forall_measurableSet _)]
    rw [Set.disjoint_left]
    intro c' hsupp hbad
    apply hbad
    by_cases hadv : AdvancedPast2 n c'
    · exact Or.inr (Phase23FirstEntry_of_real_support n c c' hShell hsupp hadv)
    · exact Or.inl
        (Phase2SingleShell_of_real_support_not_advanced n c c' hShell hsupp hadv)
  · have hadv := AdvancedPast2_of_Phase23FirstEntry n c hFirst
    rw [advanceStopK_eq_id_of_advanced n c hadv, Kernel.id_apply]
    simp [StoppedSafe, hFirst]

/-- The stopped chain remains pathwise safe at every finite time. -/
theorem advanceStopK_ae_safe
    (n t : ℕ) (c : Config (AgentState L K))
    (hSafe : StoppedSafe n c) :
    ∀ᵐ c' ∂((advanceStopK (L := L) (K := K) n ^ t) c),
      StoppedSafe n c' := by
  induction t with
  | zero =>
      simp only [pow_zero]
      change ∀ᵐ c' ∂(Kernel.id c), StoppedSafe n c'
      rw [Kernel.id_apply, MeasureTheory.ae_dirac_iff
        (DiscreteMeasurableSpace.forall_measurableSet _)]
      exact hSafe
  | succ t ih =>
      rw [MeasureTheory.ae_iff]
      have hbad_meas : MeasurableSet
          {c' : Config (AgentState L K) | ¬ StoppedSafe n c'} :=
        DiscreteMeasurableSpace.forall_measurableSet _
      rw [Kernel.pow_succ_apply_eq_lintegral _ _ _ hbad_meas,
        MeasureTheory.lintegral_eq_zero_iff
          (Kernel.measurable_coe _ hbad_meas)]
      filter_upwards [ih] with c' hc'
      exact advanceStopK_safe_one_step n c' hc'

/-- At every finite stopped time, any advanced state has exactly the Phase-3
first-entry payload. -/
theorem advanceStopK_pow_first_entry_support
    (n t : ℕ) (c : Config (AgentState L K))
    (hShell : Phase2SingleShell n c) :
    (advanceStopK (L := L) (K := K) n ^ t) c
        {c' | AdvancedPast2 n c' ∧ ¬ Phase23FirstEntry n c'} = 0 := by
  have hae := advanceStopK_ae_safe n t c (Or.inl hShell)
  have hzero :
      (advanceStopK (L := L) (K := K) n ^ t) c
        {c' | ¬ StoppedSafe n c'} = 0 := by
    rwa [MeasureTheory.ae_iff] at hae
  refine measure_mono_null ?_ hzero
  intro c' hbad hsafe
  rcases hsafe with hShell' | hFirst
  · exact (not_AdvancedPast2_of_Phase2SingleShell n c' hShell' hbad.1).elim
  · exact hbad.2 hFirst

/-! ## Quantitative stopped-chain first-entry bridge -/

/-- At the same tight epidemic horizon as the real-kernel advance theorem, the
stopped chain is outside the exact Phase-3 first-entry shell with probability at
most the dual-sign budget.  The only extra mass that could distinguish
`not first entry` from `not advanced` is `advanced ∧ not first entry`, and
`advanceStopK_pow_first_entry_support` proves that mass is zero. -/
theorem advanceStopK_first_entry_tail_le_advanceTailBudget
    (n : ℕ) (hn : 2 ≤ n) (c : Config (AgentState L K))
    (hActive : Active2Core n c) :
    (advanceStopK (L := L) (K := K) n ^
        TightEpidemicWork.epiHorizonTight n hn) c
        {c' | ¬ Phase23FirstEntry n c'} ≤
      ((advanceTailBudget n : ℝ≥0) : ℝ≥0∞) := by
  let t := TightEpidemicWork.epiHorizonTight n hn
  let U : Set (Config (AgentState L K)) :=
    {c' | ¬ AdvancedPast2 n c'}
  let E : Set (Config (AgentState L K)) :=
    {c' | AdvancedPast2 n c' ∧ ¬ Phase23FirstEntry n c'}
  let B : Set (Config (AgentState L K)) :=
    {c' | ¬ Phase23FirstEntry n c'}
  let μ := (advanceStopK (L := L) (K := K) n ^ t) c
  have hsub : B ⊆ U ∪ E := by
    intro c' hnotFirst
    by_cases hadv : AdvancedPast2 n c'
    · exact Or.inr ⟨hadv, hnotFirst⟩
    · exact Or.inl hadv
  have hEzero : μ E = 0 := by
    dsimp [μ, E, t]
    exact advanceStopK_pow_first_entry_support n
      (TightEpidemicWork.epiHorizonTight n hn) c hActive.1
  have hUeq :
      μ U =
        ((NonuniformMajority L K).transitionKernel ^ t) c U := by
    dsimp [μ, U, t]
    exact advanceStopK_pow_not_advanced_eq_real n
      (TightEpidemicWork.epiHorizonTight n hn) c
  have hreal := advancedPast2_tail_le_advanceTailBudget n hn c hActive
  change μ B ≤ ((advanceTailBudget n : ℝ≥0) : ℝ≥0∞)
  calc
    μ B ≤ μ (U ∪ E) := measure_mono hsub
    _ ≤ μ U + μ E := measure_union_le U E
    _ = μ U := by rw [hEzero, add_zero]
    _ = ((NonuniformMajority L K).transitionKernel ^ t) c U := hUeq
    _ ≤ ((advanceTailBudget n : ℝ≥0) : ℝ≥0∞) := by
      simpa [t, U] using hreal

/-- Direct convergence package for the quantitative Continue3 first-entry
shell.  Its kernel is the genuine first-advance stopped kernel; its precondition
is still only the active Phase-2 core and therefore does not manufacture the
upstream Phase-1-to-2 producer. -/
noncomputable def phase2AdvanceFirstEntryStoppedConvergence
    (n : ℕ) (hn : 2 ≤ n) :
    PhaseConvergenceW (advanceStopK (L := L) (K := K) n) where
  Pre := Active2Core n
  Post := Phase23FirstEntry n
  t := TightEpidemicWork.epiHorizonTight n hn
  ε := advanceTailBudget n
  convergence := by
    intro c hPre
    exact advanceStopK_first_entry_tail_le_advanceTailBudget n hn c hPre

#print axioms not_singleSign_iff_conflicting
#print axioms union_singleSign_or_conflicting
#print axioms carries_union_left
#print axioms carries_union_right
#print axioms opinionsUnion_ne_zero_of_left
#print axioms Transition_phase2_singleSign_or_advance
#print axioms Transition_phase2_sign_pair_or_advance
#print axioms Phase3EntryAgent_advancePhaseWithInit_of_phase2
#print axioms Phase2Transition_advance_entry_agents
#print axioms Transition_phase2_advance_entry_agents
#print axioms Phase23FirstEntry_stepOrSelf_of_conflicting_pair
#print axioms advanceStopK_eq_real_of_not_advanced
#print axioms advanceStopK_eq_id_of_advanced
#print axioms real_not_advanced_eq_zero_of_advanced
#print axioms advanceStopK_pow_restrict_not_advanced_eq_real
#print axioms advanceStopK_pow_not_advanced_eq_real
#print axioms signRunInv_of_active
#print axioms AdvancedPast2_of_real_support
#print axioms AdvancedPast2_stepOrSelf
#print axioms AdvancedPast2_stepOrSelf_of_phase3_pair
#print axioms Phase2SingleShell_stepOrSelf_or_advanced
#print axioms signCount_stepOrSelf_le_or_advanced
#print axioms signCount_le_card
#print axioms signCount_lt_card_of_mem_not_carries
#print axioms stoppedSignCount_stepOrSelf_le
#print axioms stoppedSignCount_stepOrSelf_advance
#print axioms SignRunInv_stepOrSelf
#print axioms SignRunInv_stepRel
#print axioms SignRunInv_reachable
#print axioms SignRunInv_of_stepDistOrSelf_support
#print axioms stoppedSignCount_stepRel_le
#print axioms stoppedSignCount_reachable_le
#print axioms stoppedSignCount_of_stepDistOrSelf_support_le
#print axioms signStates_nonsignStates_disjoint
#print axioms sum_interactionCount_signRect
#print axioms sign_advance_prob
#print axioms stoppedSignCount_le_of_inv
#print axioms signMilestonePhase
#print axioms signMilestone_pMin_eq_epidemic
#print axioms signMilestone_meanTime_eq_epidemic
#print axioms signMilestone_post_imp_inv_and_stopped_eq
#print axioms dual_signMilestone_post_imp_advanced
#print axioms signMilestone_tail_le_tightBudget
#print axioms advanceTailBudget_le_inv_sq
#print axioms advancedPast2_tail_le_advanceTailBudget
#print axioms phase2AdvanceConvergence
#print axioms not_AdvancedPast2_of_Phase2SingleShell
#print axioms Phase23FirstEntry_of_stepOrSelf_advanced
#print axioms Phase23FirstEntry_of_real_support
#print axioms advanceStopK_first_entry_support
#print axioms Phase2SingleShell_of_real_support_not_advanced
#print axioms AdvancedPast2_of_Phase23FirstEntry
#print axioms advanceStopK_safe_one_step
#print axioms advanceStopK_ae_safe
#print axioms advanceStopK_pow_first_entry_support
#print axioms advanceStopK_first_entry_tail_le_advanceTailBudget
#print axioms phase2AdvanceFirstEntryStoppedConvergence

end Phase2AdvanceEpidemic
end Ripple.PopulationProtocol.ExactMajority
