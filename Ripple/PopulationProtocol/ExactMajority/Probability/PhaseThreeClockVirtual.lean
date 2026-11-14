import Ripple.PopulationProtocol.ExactMajority.Probability.PairLogAuxiliary
import Ripple.PopulationProtocol.ExactMajority.Probability.StageEventSpec

/-!
# The virtual Phase-3 clock continuation (Doty et al. plan node N12, step 1)

PHASE3 §2.2: the virtual process executes the actual wrapper (phase epidemic,
initializers, Phase-1/2 rules, all Phase-3 minute and Main rules) and differs from
the protocol only at an equal-cap Clock pair in which both endpoints are in Phase 3:
there it keeps Phase 3 and replaces each counter `k` by `max (k - 1) 0`.

It is realized as an auxiliary process on the recorded pair log
(`PairLogAuxiliary.auxLabels`), so the labels drawn at every step are those of the
actual protocol and only the states they act on may differ.

Main results:
* `virtualRule_eq_transition`: the virtual rule agrees with the protocol rule on
  every pair that is not an actual counter exit.
* `transition_phase_ge_four_of_exit`: an actual counter exit moves one endpoint to
  a phase at least four.
* `virtualLabels_eq_labelsAt_of_phases_lt_four`: through any time at which all actual
  phases are below four, the virtual and actual labelled processes coincide.
* `virtualLabels_eq_labelsAt_before_seed`: strictly before the genuine first Phase-4
  seed they coincide; in particular the pretransition states (and hence the
  eligibility indicators of `StageEventSpec.eligibleContact`) of the exiting
  interaction agree.
* `virtualRule_phase_three_of_capCounterPair`: the virtual rule never leaves Phase 3
  at a cap pair (saturated counters).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockVirtual

open TimeTheorem PairLog PairLogAuxiliary

variable {L K : ℕ}

/-! ## The virtual pair rule -/

/-- Saturated counter decrement `k ↦ max (k - 1) 0`; no phase advance, no initializer. -/
def saturatedCounterStep (a : AgentState L K) : AgentState L K :=
  { a with counter := ⟨a.counter.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) a.counter.isLt⟩ }

@[simp] theorem saturatedCounterStep_phase (a : AgentState L K) :
    (saturatedCounterStep a).phase = a.phase := rfl

@[simp] theorem saturatedCounterStep_role (a : AgentState L K) :
    (saturatedCounterStep a).role = a.role := rfl

@[simp] theorem saturatedCounterStep_minute (a : AgentState L K) :
    (saturatedCounterStep a).minute = a.minute := rfl

@[simp] theorem saturatedCounterStep_counter (a : AgentState L K) :
    (saturatedCounterStep a).counter.val = a.counter.val - 1 := rfl

/-- After the wrapper's phase epidemic, both endpoints are Phase-3 Clocks with equal
minutes at the cap: the actual rule runs the counter subroutine on both. -/
def CapCounterPair (s t : AgentState L K) : Prop :=
  (phaseEpidemicUpdate L K s t).1.phase.val = 3 ∧
  (phaseEpidemicUpdate L K s t).2.phase.val = 3 ∧
  (phaseEpidemicUpdate L K s t).1.role = .clock ∧
  (phaseEpidemicUpdate L K s t).2.role = .clock ∧
  (phaseEpidemicUpdate L K s t).1.minute = (phaseEpidemicUpdate L K s t).2.minute ∧
  (phaseEpidemicUpdate L K s t).1.minute.val = K * (L + 1)

instance (s t : AgentState L K) : Decidable (CapCounterPair s t) := by
  unfold CapCounterPair
  infer_instance

/-- A cap counter pair in which some endpoint has counter zero: the actual rule
advances that endpoint out of Phase 3. -/
def CounterExitPair (s t : AgentState L K) : Prop :=
  CapCounterPair s t ∧
    ((phaseEpidemicUpdate L K s t).1.counter.val = 0 ∨
      (phaseEpidemicUpdate L K s t).2.counter.val = 0)

/-- The virtual rule: the protocol wrapper, except that a cap counter pair keeps
Phase 3 with saturated counters. -/
def virtualRule : PairRule L K := fun s t =>
  if CapCounterPair s t then
    (saturatedCounterStep (phaseEpidemicUpdate L K s t).1,
      saturatedCounterStep (phaseEpidemicUpdate L K s t).2)
  else Transition L K s t

/-! ## Protocol facts at a cap pair -/

theorem stdCounterSubroutine_of_ne_zero (a : AgentState L K) (h : a.counter.val ≠ 0) :
    stdCounterSubroutine L K a = saturatedCounterStep a := by
  unfold stdCounterSubroutine saturatedCounterStep
  rw [dif_neg h]

theorem stdCounterSubroutine_phase_ge_four (a : AgentState L K)
    (h3 : a.phase.val = 3) (h0 : a.counter.val = 0) :
    4 ≤ (stdCounterSubroutine L K a).phase.val := by
  unfold stdCounterSubroutine
  rw [dif_pos h0]
  unfold advancePhaseWithInit
  refine le_trans ?_ (phaseInit_phase_nondec L K _ _)
  unfold advancePhase
  rw [dif_pos (by omega)]
  change 4 ≤ a.phase.val.succ
  omega

/-- The Phase-3 rule at an equal-cap Clock pair is the counter subroutine on both
endpoints: the Main rules do not fire. -/
theorem phase3Transition_cap (s t : AgentState L K)
    (hsr : s.role = .clock) (htr : t.role = .clock)
    (hmin : s.minute = t.minute) (hcap : s.minute.val = K * (L + 1)) :
    Phase3Transition L K s t = (stdCounterSubroutine L K s, stdCounterSubroutine L K t) := by
  have hnot : ¬ s.minute.val < K * (L + 1) := by omega
  have hnot' : ¬ t.minute.val < K * (L + 1) := by rw [← hmin]; exact hnot
  have hs1 : (stdCounterSubroutine L K s).role = .clock :=
    stdCounterSubroutine_clock_role_eq L K s hsr
  have ht1 : (stdCounterSubroutine L K t).role = .clock :=
    stdCounterSubroutine_clock_role_eq L K t htr
  simp only [Phase3Transition, hsr, htr, and_self, if_true, hmin, ne_eq, not_true_eq_false,
    if_false, hnot', dif_neg, not_false_eq_true, hs1, ht1]
  simp [hs1, ht1]

/-- The wrapper at a cap counter pair. -/
theorem transition_of_capCounterPair (s t : AgentState L K) (h : CapCounterPair s t) :
    Transition L K s t =
      (finishPhase10Entry L K (phaseEpidemicUpdate L K s t).1
          (stdCounterSubroutine L K (phaseEpidemicUpdate L K s t).1),
        finishPhase10Entry L K (phaseEpidemicUpdate L K s t).2
          (stdCounterSubroutine L K (phaseEpidemicUpdate L K s t).2)) := by
  obtain ⟨h3, h3', hsr, htr, hmin, hcap⟩ := h
  unfold Transition
  generalize hd : phaseEpidemicUpdate L K s t = d at *
  obtain ⟨s', t'⟩ := d
  simp only at h3 h3' hsr htr hmin hcap ⊢
  have hph : s'.phase = ⟨3, by omega⟩ := Fin.ext h3
  rw [hph]
  simp only []
  rw [phase3Transition_cap s' t' hsr htr hmin hcap]

/-- The virtual rule agrees with the protocol rule on every pair that is not an actual
counter exit. -/
theorem virtualRule_eq_transition (s t : AgentState L K) (h : ¬ CounterExitPair s t) :
    virtualRule s t = Transition L K s t := by
  unfold virtualRule
  split_ifs with hcap
  · have hc1 : (phaseEpidemicUpdate L K s t).1.counter.val ≠ 0 :=
      fun h0 => h ⟨hcap, Or.inl h0⟩
    have hc2 : (phaseEpidemicUpdate L K s t).2.counter.val ≠ 0 :=
      fun h0 => h ⟨hcap, Or.inr h0⟩
    have hp1 : (saturatedCounterStep (phaseEpidemicUpdate L K s t).1).phase.val ≠ 10 := by
      change (phaseEpidemicUpdate L K s t).1.phase.val ≠ 10
      have := hcap.1
      omega
    have hp2 : (saturatedCounterStep (phaseEpidemicUpdate L K s t).2).phase.val ≠ 10 := by
      change (phaseEpidemicUpdate L K s t).2.phase.val ≠ 10
      have := hcap.2.1
      omega
    rw [transition_of_capCounterPair s t hcap, stdCounterSubroutine_of_ne_zero _ hc1,
      stdCounterSubroutine_of_ne_zero _ hc2,
      finishPhase10Entry_eq_self_of_after_ne_10 L K _ _ hp1,
      finishPhase10Entry_eq_self_of_after_ne_10 L K _ _ hp2]
  · rfl

/-- An actual counter exit moves one endpoint to a phase at least four. -/
theorem transition_phase_ge_four_of_exit (s t : AgentState L K) (h : CounterExitPair s t) :
    4 ≤ (Transition L K s t).1.phase.val ∨ 4 ≤ (Transition L K s t).2.phase.val := by
  obtain ⟨hcap, hz⟩ := h
  rw [transition_of_capCounterPair s t hcap]
  simp only [finishPhase10Entry_phase_val]
  rcases hz with h0 | h0
  · exact Or.inl (stdCounterSubroutine_phase_ge_four _ hcap.1 h0)
  · exact Or.inr (stdCounterSubroutine_phase_ge_four _ hcap.2.1 h0)

/-- Saturated counters: at a cap counter pair the virtual rule keeps both endpoints
in Phase 3 with their roles and minutes. -/
theorem virtualRule_phase_three_of_capCounterPair (s t : AgentState L K)
    (h : CapCounterPair s t) :
    (virtualRule s t).1.phase.val = 3 ∧ (virtualRule s t).2.phase.val = 3 ∧
    (virtualRule s t).1.role = .clock ∧ (virtualRule s t).2.role = .clock ∧
    (virtualRule s t).1.minute.val = K * (L + 1) ∧
    (virtualRule s t).2.minute.val = K * (L + 1) := by
  obtain ⟨h3, h3', hsr, htr, hmin, hcap⟩ := h
  have hv : virtualRule s t =
      (saturatedCounterStep (phaseEpidemicUpdate L K s t).1,
        saturatedCounterStep (phaseEpidemicUpdate L K s t).2) := by
    unfold virtualRule
    rw [if_pos ⟨h3, h3', hsr, htr, hmin, hcap⟩]
  rw [hv]
  refine ⟨h3, h3', hsr, htr, hcap, ?_⟩
  change (phaseEpidemicUpdate L K s t).2.minute.val = K * (L + 1)
  rw [← hmin]
  exact hcap

/-! ## Agreement with the actual labelled process -/

/-- Agreement through `T` when the rule agrees with the protocol on every pair actually
drawn before `T`. This refines `auxLabels_eq_labelsAt_of_agree`, whose agreement set
is a property of the whole labelling. -/
theorem auxLabels_eq_labelsAt_of_drawn_agree (init : Cfg L K) (F : PairRule L K)
    (ω : Ω L K) (T : ℕ)
    (h : ∀ t < T, ∀ i j : Fin init.card, drawLabels init ω (t + 1) = some (i, j) →
      F (labelsAt init ω t i) (labelsAt init ω t j) =
        (NonuniformMajority L K).δ (labelsAt init ω t i) (labelsAt init ω t j)) :
    ∀ t ≤ T, auxLabels init F ω t = labelsAt init ω t := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
      intro ht
      rw [auxLabels_succ, labelsAt_succ_eq_auxStep, ih (by omega)]
      cases hd : drawLabels init ω (t + 1) with
      | none => rfl
      | some ij =>
          obtain ⟨i, j⟩ := ij
          simp only [auxStep, ruleUpdate]
          rw [h t (by omega) i j hd]

/-- The virtual labelled process along the recorded pair log. -/
def virtualLabels (init : Cfg L K) (ω : Ω L K) (t : ℕ) : Fin init.card → AgentState L K :=
  auxLabels init virtualRule ω t

/-- The virtual configuration at time `t`. -/
def virtualCfg (init : Cfg L K) (ω : Ω L K) (t : ℕ) : Cfg L K :=
  auxCfg init virtualRule ω t

theorem virtualLabels_zero (init : Cfg L K) (ω : Ω L K) :
    virtualLabels init ω 0 = labelsAt init ω 0 := rfl

theorem virtualLabels_succ (init : Cfg L K) (ω : Ω L K) (t : ℕ) :
    virtualLabels init ω (t + 1) =
      auxStep virtualRule (virtualLabels init ω t) (drawLabels init ω (t + 1)) := rfl

theorem measurable_virtualLabels (init : Cfg L K) (t : ℕ) :
    Measurable[pairLogFiltration L K t] (fun ω => virtualLabels init ω t) :=
  measurable_auxLabels init virtualRule t

theorem labelsAt_mem_trace (init : Cfg L K) (ω : Ω L K) (t : ℕ) (i : Fin init.card) :
    labelsAt init ω t i ∈ trace init ω t := by
  rw [← labelsAt_config]
  exact Multiset.mem_map.mpr ⟨i, Finset.mem_univ_val i, rfl⟩

/-- Through any time at which every actual phase is below four, the virtual and actual
labelled processes coincide. -/
theorem virtualLabels_eq_labelsAt_of_phases_lt_four (init : Cfg L K) (ω : Ω L K) (T : ℕ)
    (h : ∀ u ≤ T, ∀ i : Fin init.card, (labelsAt init ω u i).phase.val < 4) :
    ∀ t ≤ T, virtualLabels init ω t = labelsAt init ω t := by
  apply auxLabels_eq_labelsAt_of_drawn_agree
  intro t ht i j hd
  apply virtualRule_eq_transition
  intro hexit
  obtain ⟨-, hi, hj, -⟩ := labelsAt_selected_transition init ω t i j hd
  rcases transition_phase_ge_four_of_exit _ _ hexit with h4 | h4
  · have hlt := h (t + 1) (by omega) i
    rw [hi] at hlt
    change (Transition L K _ _).1.phase.val < 4 at hlt
    omega
  · have hlt := h (t + 1) (by omega) j
    rw [hj] at hlt
    change (Transition L K _ _).2.phase.val < 4 at hlt
    omega

/-- Strictly before the genuine first Phase-4 seed, the virtual and actual labelled
processes coincide. At the seed time `ρ` itself the pretransition states (time
`ρ - 1`) agree, so the eligibility indicators of the exiting interaction agree. -/
theorem virtualLabels_eq_labelsAt_before_seed (init : Cfg L K) (ω : Ω L K) {ρ : ℕ}
    (hρ : firstPhaseSeed init 4 ρ ω) :
    ∀ t < ρ, virtualLabels init ω t = labelsAt init ω t := by
  intro t ht
  refine virtualLabels_eq_labelsAt_of_phases_lt_four init ω t ?_ t le_rfl
  intro u hu i
  exact hρ.2 u (by omega) _ (labelsAt_mem_trace init ω u i)

theorem virtualCfg_eq_trace_before_seed (init : Cfg L K) (ω : Ω L K) {ρ : ℕ}
    (hρ : firstPhaseSeed init 4 ρ ω) :
    ∀ t < ρ, virtualCfg init ω t = trace init ω t := by
  intro t ht
  change labelCfg (virtualLabels init ω t) = trace init ω t
  rw [virtualLabels_eq_labelsAt_before_seed init ω hρ t ht]
  exact labelsAt_config init ω t

/-- Event transfer before the first Phase-4 seed: any event about the virtual path
through `T` coincides, on the event that all phases are below four through `T`, with
the same event about the actual path. -/
theorem virtual_event_eq_actual_event (init : Cfg L K) (T : ℕ)
    (P : ((t : Finset.Iic T) → Fin init.card → AgentState L K) → Prop) :
    {ω | (∀ u ≤ T, ∀ i : Fin init.card, (labelsAt init ω u i).phase.val < 4) ∧
        P (fun t => virtualLabels init ω t.val)} =
      {ω | (∀ u ≤ T, ∀ i : Fin init.card, (labelsAt init ω u i).phase.val < 4) ∧
        P (fun t => labelsAt init ω t.val)} := by
  ext ω
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨hG, hP⟩
    refine ⟨hG, ?_⟩
    have hpath : (fun t : Finset.Iic T => virtualLabels init ω t.val) =
        (fun t => labelsAt init ω t.val) := by
      funext t
      exact virtualLabels_eq_labelsAt_of_phases_lt_four init ω T hG t.val
        (Finset.mem_Iic.mp t.property)
    rwa [hpath] at hP
  · rintro ⟨hG, hP⟩
    refine ⟨hG, ?_⟩
    have hpath : (fun t : Finset.Iic T => virtualLabels init ω t.val) =
        (fun t => labelsAt init ω t.val) := by
      funext t
      exact virtualLabels_eq_labelsAt_of_phases_lt_four init ω T hG t.val
        (Finset.mem_Iic.mp t.property)
    rwa [hpath]

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockVirtual

end
