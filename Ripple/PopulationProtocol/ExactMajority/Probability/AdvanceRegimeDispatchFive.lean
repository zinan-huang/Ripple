-- Ripple/PopulationProtocol/ExactMajority/Probability/AdvanceRegimeDispatchFive.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.AdvanceResetPairBound
import Ripple.PopulationProtocol.ExactMajority.Probability.AdvanceOvershootSource
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockMainActivation

/-!
# `AdvanceRegimeDispatch 5`, proved for all `L`, `K`

The proof follows the dispatcher of `Transition`.  Write `e`, `f` for the two
epidemic outputs and `D` for the phase-specific output on `(e, f)`.

* `e` and `f` always carry the same phase `N` (`epidemic_phases_eq`).
* `Transition.i = finishPhase10Entry _ D.i`, which keeps role and phase.
* A Phase-6 clock output cannot come from `N ≤ 4` (each of those branches
  raises the phase by at most one, or enters the error phase 10) nor from
  `N ≥ 7` (branches never lower the phase).
* For `N = 5` and `N = 6` the output is a clock only if its input was a clock
  (`phaseFive*Reflect`, `phaseSix*Reflect`: the only role writes there are the
  reserve split to Main and nothing else).

No `Wf` hypothesis and no enumeration of states is used.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real BigOperators

namespace Ripple.PopulationProtocol.ExactMajority

namespace AdvanceNoOvershoot

variable {L K : ℕ}

/-! ## Phase-raising bounds without well-formedness -/

theorem advancePhaseWithInit_phase_le_succ_or_ten (a : AgentState L K) :
    (advancePhaseWithInit L K a).phase.val ≤ a.phase.val + 1 ∨
      (advancePhaseWithInit L K a).phase.val = 10 := by
  have hadv := advancePhase_phase_le_succ (L := L) (K := K) a
  unfold advancePhaseWithInit
  dsimp only
  rcases phaseInit_phase_eq_or_ten (L := L) (K := K)
      (advancePhase L K a).phase (advancePhase L K a) with h | h
  · left
    omega
  · right
    exact h

theorem phaseOneLeft_le (a b : AgentState L K) :
    (Phase1Transition L K a b).1.phase.val ≤ a.phase.val + 1 ∨
      (Phase1Transition L K a b).1.phase.val = 10 := by
  by_cases hmain : a.role = .main ∧ b.role = .main
  · left
    obtain ⟨ha, hb⟩ := hmain
    have hval : (Phase1Transition L K a b).1.phase.val = a.phase.val := by
      simp [Phase1Transition, ha, hb, clockCounterStep]
    omega
  · have hval : (Phase1Transition L K a b).1 = clockCounterStep L K a := by
      unfold Phase1Transition
      rw [if_neg hmain]
    rw [hval]
    exact PhaseThreeClockMainActivation.clockCounterStep_phase_le_succ a

theorem phaseOneRight_le (a b : AgentState L K) :
    (Phase1Transition L K a b).2.phase.val ≤ b.phase.val + 1 ∨
      (Phase1Transition L K a b).2.phase.val = 10 := by
  by_cases hmain : a.role = .main ∧ b.role = .main
  · left
    obtain ⟨ha, hb⟩ := hmain
    have hval : (Phase1Transition L K a b).2.phase.val = b.phase.val := by
      simp [Phase1Transition, ha, hb, clockCounterStep]
    omega
  · have hval : (Phase1Transition L K a b).2 = clockCounterStep L K b := by
      unfold Phase1Transition
      rw [if_neg hmain]
    rw [hval]
    exact PhaseThreeClockMainActivation.clockCounterStep_phase_le_succ b

theorem phaseTwoLeft_le (a b : AgentState L K) :
    (Phase2Transition L K a b).1.phase.val ≤ a.phase.val + 1 ∨
      (Phase2Transition L K a b).1.phase.val = 10 := by
  unfold Phase2Transition
  dsimp only
  split_ifs
  · exact advancePhaseWithInit_phase_le_succ_or_ten _
  all_goals (left; exact Nat.le_succ _)

theorem phaseTwoRight_le (a b : AgentState L K) :
    (Phase2Transition L K a b).2.phase.val ≤ b.phase.val + 1 ∨
      (Phase2Transition L K a b).2.phase.val = 10 := by
  unfold Phase2Transition
  dsimp only
  split_ifs
  · exact advancePhaseWithInit_phase_le_succ_or_ten _
  all_goals (left; exact Nat.le_succ _)

theorem phaseFourLeft_le (a b : AgentState L K) :
    (Phase4Transition L K a b).1.phase.val ≤ a.phase.val + 1 ∨
      (Phase4Transition L K a b).1.phase.val = 10 := by
  unfold Phase4Transition
  dsimp
  split_ifs
  · exact advancePhaseWithInit_phase_le_succ_or_ten a
  · left; exact Nat.le_succ _

theorem phaseFourRight_le (a b : AgentState L K) :
    (Phase4Transition L K a b).2.phase.val ≤ b.phase.val + 1 ∨
      (Phase4Transition L K a b).2.phase.val = 10 := by
  unfold Phase4Transition
  dsimp
  split_ifs
  · exact advancePhaseWithInit_phase_le_succ_or_ten b
  · left; exact Nat.le_succ _

theorem phaseThreeRight_le (a b : AgentState L K) :
    (Phase3Transition L K a b).2.phase.val ≤ b.phase.val + 1 ∨
      (Phase3Transition L K a b).2.phase.val = 10 := by
  set t1 : AgentState L K :=
    (if a.role = .clock ∧ b.role = .clock then
      if a.minute ≠ b.minute then { b with minute := max a.minute b.minute }
      else if _h : a.minute.val < K * (L + 1) then b
      else stdCounterSubroutine L K b
    else b) with ht1def
  have hphaseeq : (Phase3Transition L K a b).2.phase = t1.phase :=
    (Phase3Transition_right_output_eq_rule1 (L := L) (K := K) a b t1 ht1def).2
  have hval : (Phase3Transition L K a b).2.phase.val = t1.phase.val := by
    rw [hphaseeq]
  rw [hval, ht1def]
  split_ifs with hcl hmin hlt
  · left; exact Nat.le_succ _
  · left; exact Nat.le_succ _
  · exact PhaseThreeClockMainActivation.stdCounterSubroutine_phase_le_succ b
  · left; exact Nat.le_succ _

theorem phaseThreeLeft_le (a b : AgentState L K) :
    (Phase3Transition L K a b).1.phase.val ≤ a.phase.val + 1 ∨
      (Phase3Transition L K a b).1.phase.val = 10 := by
  set s1 : AgentState L K :=
    (if a.role = .clock ∧ b.role = .clock then
      if a.minute ≠ b.minute then { a with minute := max a.minute b.minute }
      else if _h : a.minute.val < K * (L + 1) then
        { a with minute := ⟨a.minute.val + 1, by omega⟩ }
      else stdCounterSubroutine L K a
    else a) with hs1def
  have hphaseeq : (Phase3Transition L K a b).1.phase = s1.phase :=
    (Phase3Transition_left_output_eq_rule1 (L := L) (K := K) a b s1 hs1def).2
  have hval : (Phase3Transition L K a b).1.phase.val = s1.phase.val := by
    rw [hphaseeq]
  rw [hval, hs1def]
  split_ifs with hcl hmin hlt
  · left; exact Nat.le_succ _
  · left; exact Nat.le_succ _
  · exact PhaseThreeClockMainActivation.stdCounterSubroutine_phase_le_succ a
  · left; exact Nat.le_succ _


/-! ## The two epidemic outputs carry the same phase -/

theorem epidemic_phases_eq (s t : AgentState L K) :
    (phaseEpidemicUpdate L K s t).1.phase.val =
      (phaseEpidemicUpdate L K s t).2.phase.val := by
  unfold phaseEpidemicUpdate
  dsimp only
  have hps : s.phase.val ≤ (max s.phase t.phase).val := by
    exact_mod_cast (le_max_left s.phase t.phase)
  have hpt : t.phase.val ≤ (max s.phase t.phase).val := by
    exact_mod_cast (le_max_right s.phase t.phase)
  have hp10 : (max s.phase t.phase).val ≤ 10 := by
    have := (max s.phase t.phase).isLt
    omega
  have hs' : (runInitsBetween L K s.phase.val (max s.phase t.phase).val
        { s with phase := max s.phase t.phase }).phase.val =
        (max s.phase t.phase).val ∨
      (runInitsBetween L K s.phase.val (max s.phase t.phase).val
        { s with phase := max s.phase t.phase }).phase.val = 10 := by
    rcases runInitsBetween_phase_eq_or_ten (L := L) (K := K) s.phase.val
      (max s.phase t.phase).val { s with phase := max s.phase t.phase } with h | h
    · exact Or.inl h
    · exact Or.inr h
  have ht' : (runInitsBetween L K t.phase.val (max s.phase t.phase).val
        { t with phase := max s.phase t.phase }).phase.val =
        (max s.phase t.phase).val ∨
      (runInitsBetween L K t.phase.val (max s.phase t.phase).val
        { t with phase := max s.phase t.phase }).phase.val = 10 := by
    rcases runInitsBetween_phase_eq_or_ten (L := L) (K := K) t.phase.val
      (max s.phase t.phase).val { t with phase := max s.phase t.phase } with h | h
    · exact Or.inl h
    · exact Or.inr h
  set p := max s.phase t.phase with hp
  set s' := runInitsBetween L K s.phase.val p.val { s with phase := p } with hs'def
  set t' := runInitsBetween L K t.phase.val p.val { t with phase := p } with ht'def
  split_ifs with hcond
  · simp only [phase10EpidemicEntry]
    split_ifs with h1 h2 h2
    all_goals first
      | omega
      | (simp [enterPhase10, phase10] <;> omega)
      | simp [enterPhase10, phase10]
  · simp only
    omega

/-! ## The dispatcher output -/

/-- The phase-specific output of `Transition`, as a standalone definition. -/
def dispatchOut (L K : ℕ) (e f : AgentState L K) :
    AgentState L K × AgentState L K :=
  match e.phase with
  | ⟨0, _⟩ => Phase0Transition L K e f
  | ⟨1, _⟩ => Phase1Transition L K e f
  | ⟨2, _⟩ => Phase2Transition L K e f
  | ⟨3, _⟩ => Phase3Transition L K e f
  | ⟨4, _⟩ => Phase4Transition L K e f
  | ⟨5, _⟩ => Phase5Transition L K e f
  | ⟨6, _⟩ => Phase6Transition L K e f
  | ⟨7, _⟩ => Phase7Transition L K e f
  | ⟨8, _⟩ => Phase8Transition L K e f
  | ⟨9, _⟩ => Phase9Transition L K e f
  | ⟨10, _⟩ => Phase10Transition L K e f
  | _ => (e, f)

theorem transition_eq_dispatch (a b : AgentState L K) :
    Transition L K a b =
      (finishPhase10Entry L K (phaseEpidemicUpdate L K a b).1
          (dispatchOut L K (phaseEpidemicUpdate L K a b).1
            (phaseEpidemicUpdate L K a b).2).1,
        finishPhase10Entry L K (phaseEpidemicUpdate L K a b).2
          (dispatchOut L K (phaseEpidemicUpdate L K a b).1
            (phaseEpidemicUpdate L K a b).2).2) := rfl

/-! ## Clock reflection for the Phase-5 and Phase-6 branches -/

theorem stdGuardReflect (a : AgentState L K)
    (h : (if a.role = .clock then stdCounterSubroutine L K a else a).role = .clock) :
    a.role = .clock := by
  split_ifs at h with hh
  · exact hh
  · exact h

theorem doSplitFstReflect (r m : AgentState L K)
    (h : (doSplit L K r m).1.role = .clock) : r.role = .clock := by
  unfold doSplit at h
  match hm : m.bias with
  | Bias.zero => simpa [hm] using h
  | Bias.dyadic sgn j => simp only [hm] at h; split_ifs at h <;> simp_all

theorem phaseFiveFirstReflect (s t : AgentState L K)
    (h : (Phase5Transition L K s t).1.role = .clock) : s.role = .clock := by
  unfold Phase5Transition at h; dsimp only at h
  set s1 := (if s.role = .reserve ∧ t.role = .main ∧ (t.bias ≠ Bias.zero) then
      (if s.hour.val = L then ({ s with hour := exponentOf L t.bias }, t) else (s, t)).1
    else if t.role = .reserve ∧ s.role = .main ∧ (s.bias ≠ Bias.zero) then
      (if t.hour.val = L then ({ t with hour := exponentOf L s.bias }, s) else (t, s)).2
    else s) with hs1
  have hs1cl : s1.role = .clock := stdGuardReflect s1 (by simpa [hs1] using h)
  rw [hs1] at hs1cl
  split_ifs at hs1cl with h1 hh1 h2 hh2
  · exact absurd (by simpa using hs1cl : s.role = Role.clock) (by rw [h1.1]; simp)
  · exact absurd (by simpa using hs1cl : s.role = Role.clock) (by rw [h1.1]; simp)
  · exact absurd (by simpa using hs1cl : s.role = Role.clock) (by rw [h2.2.1]; simp)
  · exact absurd (by simpa using hs1cl : s.role = Role.clock) (by rw [h2.2.1]; simp)
  · exact hs1cl

theorem phaseFiveSecondReflect (s t : AgentState L K)
    (h : (Phase5Transition L K s t).2.role = .clock) : t.role = .clock := by
  unfold Phase5Transition at h; dsimp only at h
  set t1 := (if s.role = .reserve ∧ t.role = .main ∧ (t.bias ≠ Bias.zero) then
      (if s.hour.val = L then ({ s with hour := exponentOf L t.bias }, t) else (s, t)).2
    else if t.role = .reserve ∧ s.role = .main ∧ (s.bias ≠ Bias.zero) then
      (if t.hour.val = L then ({ t with hour := exponentOf L s.bias }, s) else (t, s)).1
    else t) with ht1
  have ht1cl : t1.role = .clock := stdGuardReflect t1 (by simpa [ht1] using h)
  rw [ht1] at ht1cl
  split_ifs at ht1cl with h1 hh1 h2 hh2
  · exact absurd (by simpa using ht1cl : t.role = Role.clock) (by rw [h1.2.1]; simp)
  · exact absurd (by simpa using ht1cl : t.role = Role.clock) (by rw [h1.2.1]; simp)
  · exact absurd (by simpa using ht1cl : t.role = Role.clock) (by rw [h2.1]; simp)
  · exact absurd (by simpa using ht1cl : t.role = Role.clock) (by rw [h2.1]; simp)
  · exact ht1cl

theorem phaseSixFirstReflect (s t : AgentState L K)
    (h : (Phase6Transition L K s t).1.role = .clock) : s.role = .clock := by
  unfold Phase6Transition at h
  set s1 := (if s.role = .reserve ∧ t.role = .main ∧ (t.bias ≠ Bias.zero) then (doSplit L K s t).1
    else if t.role = .reserve ∧ s.role = .main ∧ (s.bias ≠ Bias.zero) then (doSplit L K t s).2
    else s) with hs1
  have hs1cl : s1.role = .clock := stdGuardReflect s1 (by simpa [hs1] using h)
  rw [hs1] at hs1cl
  split_ifs at hs1cl with h1 h2
  · exact (by rw [doSplitFstReflect s t hs1cl] at h1; exact absurd h1.1 (by simp))
  · rw [doSplit_role_snd] at hs1cl; rw [hs1cl] at h2; exact absurd h2.2.1 (by simp)
  · exact hs1cl

theorem phaseSixSecondReflect (s t : AgentState L K)
    (h : (Phase6Transition L K s t).2.role = .clock) : t.role = .clock := by
  unfold Phase6Transition at h
  set t1 := (if s.role = .reserve ∧ t.role = .main ∧ (t.bias ≠ Bias.zero) then (doSplit L K s t).2
    else if t.role = .reserve ∧ s.role = .main ∧ (s.bias ≠ Bias.zero) then (doSplit L K t s).1
    else t) with ht1
  have ht1cl : t1.role = .clock := stdGuardReflect t1 (by simpa [ht1] using h)
  rw [ht1] at ht1cl
  split_ifs at ht1cl with h1 h2
  · rw [doSplit_role_snd] at ht1cl; rw [ht1cl] at h1; exact absurd h1.2.1 (by simp)
  · exact (by rw [doSplitFstReflect t s ht1cl] at h2; exact absurd h2.1 (by simp))
  · exact ht1cl

/-! ## One lemma per dispatch branch -/

/-- A Phase-6 clock in the first dispatched output comes from a clock at
phase 5 or 6 (the only branches `N = 5, 6` can produce it; `N ≤ 4` and
`N ≥ 7` are impossible). -/
theorem dispatch_first_six (e f : AgentState L K)
    (h6 : (dispatchOut L K e f).1.phase.val = 6)
    (hc : (dispatchOut L K e f).1.role = .clock) :
    e.role = .clock ∧ (e.phase.val = 5 ∨ e.phase.val = 6) := by
  unfold dispatchOut at h6 hc
  rcases hpv : e.phase with ⟨pv, hlt⟩
  have he : e.phase.val = pv := by rw [hpv]
  simp only [hpv] at h6 hc
  interval_cases pv
  · have := Phase0Transition_left_phase_le_succ_of_phase0 e f he
    simp only at h6
    omega
  · simp only at h6
    rcases phaseOneLeft_le e f with h | h <;> omega
  · simp only at h6
    rcases phaseTwoLeft_le e f with h | h <;> omega
  · simp only at h6
    rcases phaseThreeLeft_le e f with h | h <;> omega
  · simp only at h6
    rcases phaseFourLeft_le e f with h | h <;> omega
  · simp only at hc
    exact ⟨phaseFiveFirstReflect e f hc, Or.inl rfl⟩
  · simp only at hc
    exact ⟨phaseSixFirstReflect e f hc, Or.inr rfl⟩
  · simp only at h6
    have := (Phase7Transition_phase_nondec L K e f).1
    omega
  · simp only at h6
    have := (Phase8Transition_phase_nondec L K e f).1
    omega
  · simp only at h6
    have := (Phase9Transition_phase_nondec L K e f).1
    omega
  · simp only at h6
    have := (Phase10Transition_phase_nondec L K e f).1
    omega

/-- Second-output version; `f` has the same phase as `e`. -/
theorem dispatch_second_six (e f : AgentState L K)
    (hef : e.phase.val = f.phase.val)
    (h6 : (dispatchOut L K e f).2.phase.val = 6)
    (hc : (dispatchOut L K e f).2.role = .clock) :
    f.role = .clock ∧ (e.phase.val = 5 ∨ e.phase.val = 6) := by
  unfold dispatchOut at h6 hc
  rcases hpv : e.phase with ⟨pv, hlt⟩
  have he : e.phase.val = pv := by rw [hpv]
  have hf : f.phase.val = pv := by omega
  simp only [hpv] at h6 hc
  interval_cases pv
  · have := Phase0Transition_right_phase_le_succ_of_phase0 e f hf
    simp only at h6
    omega
  · simp only at h6
    rcases phaseOneRight_le e f with h | h <;> omega
  · simp only at h6
    rcases phaseTwoRight_le e f with h | h <;> omega
  · simp only at h6
    rcases phaseThreeRight_le e f with h | h <;> omega
  · simp only at h6
    rcases phaseFourRight_le e f with h | h <;> omega
  · simp only at hc
    exact ⟨phaseFiveSecondReflect e f hc, Or.inl rfl⟩
  · simp only at hc
    exact ⟨phaseSixSecondReflect e f hc, Or.inr rfl⟩
  · simp only at h6
    have := (Phase7Transition_phase_nondec L K e f).2
    omega
  · simp only at h6
    have := (Phase8Transition_phase_nondec L K e f).2
    omega
  · simp only at h6
    have := (Phase9Transition_phase_nondec L K e f).2
    omega
  · simp only at h6
    have := (Phase10Transition_phase_nondec L K e f).2
    omega

/-- **`AdvanceRegimeDispatch 5` holds for every `L`, `K`.** -/
theorem advanceRegimeDispatch_five :
    AdvanceRegimeDispatch (L := L) (K := K) 5 := by
  intro a b
  have hef := epidemic_phases_eq a b
  have hT := transition_eq_dispatch a b
  have hT1r : (Transition L K a b).1.role =
      (dispatchOut L K (phaseEpidemicUpdate L K a b).1
        (phaseEpidemicUpdate L K a b).2).1.role := by
    rw [hT]
    exact finishPhase10Entry_role_eq L K _ _
  have hT1p : (Transition L K a b).1.phase.val =
      (dispatchOut L K (phaseEpidemicUpdate L K a b).1
        (phaseEpidemicUpdate L K a b).2).1.phase.val := by
    rw [hT]
    exact finishPhase10Entry_phase_val L K _ _
  have hT2r : (Transition L K a b).2.role =
      (dispatchOut L K (phaseEpidemicUpdate L K a b).1
        (phaseEpidemicUpdate L K a b).2).2.role := by
    rw [hT]
    exact finishPhase10Entry_role_eq L K _ _
  have hT2p : (Transition L K a b).2.phase.val =
      (dispatchOut L K (phaseEpidemicUpdate L K a b).1
        (phaseEpidemicUpdate L K a b).2).2.phase.val := by
    rw [hT]
    exact finishPhase10Entry_phase_val L K _ _
  constructor
  · by_cases hcl : (Transition L K a b).1.role = .clock ∧
        (Transition L K a b).1.phase.val = 5 + 1
    · have h6 : (dispatchOut L K (phaseEpidemicUpdate L K a b).1
          (phaseEpidemicUpdate L K a b).2).1.phase.val = 6 := by
        have := hcl.2
        omega
      have hc : (dispatchOut L K (phaseEpidemicUpdate L K a b).1
          (phaseEpidemicUpdate L K a b).2).1.role = .clock := by
        rw [← hT1r]
        exact hcl.1
      obtain ⟨hr, hph⟩ := dispatch_first_six _ _ h6 hc
      rcases hph with h5 | h6'
      · exact Or.inr (Or.inl ⟨hr, h5⟩)
      · exact Or.inl ⟨hr, by omega⟩
    · exact Or.inr (Or.inr hcl)
  · by_cases hcl : (Transition L K a b).2.role = .clock ∧
        (Transition L K a b).2.phase.val = 5 + 1
    · have h6 : (dispatchOut L K (phaseEpidemicUpdate L K a b).1
          (phaseEpidemicUpdate L K a b).2).2.phase.val = 6 := by
        have := hcl.2
        omega
      have hc : (dispatchOut L K (phaseEpidemicUpdate L K a b).1
          (phaseEpidemicUpdate L K a b).2).2.role = .clock := by
        rw [← hT2r]
        exact hcl.1
      obtain ⟨hr, hph⟩ := dispatch_second_six _ _ hef h6 hc
      rcases hph with h5 | h6'
      · exact Or.inr (Or.inl ⟨h5, hr, by omega⟩)
      · exact Or.inl ⟨by omega, by omega, hr⟩
    · exact Or.inr (Or.inr hcl)

/-! ## The consumers at `p = 5` with `hdisp` discharged -/

theorem counterResetDestSix : CounterResetDest 6 := by
  simp [CounterResetDest]

/-- `advanceClockSummand_Transition_pair_le` at `p = 5`: the two-sided pair
ceiling, with the regime dispatch discharged. -/
theorem advanceClockSummandPairLeFive (s : ℝ) (hs : 0 ≤ s) (a b : AgentState L K) :
    advanceClockSummand (L := L) (K := K) 5 s (Transition L K a b).1
      + advanceClockSummand (L := L) (K := K) 5 s (Transition L K a b).2
      ≤ ENNReal.ofReal (Real.exp s)
          * (advanceClockSummand (L := L) (K := K) 5 s a
             + advanceClockSummand (L := L) (K := K) 5 s b)
        + 2 * (ENNReal.ofReal (Real.exp s) * freshVal (L := L) s) :=
  advanceClockSummand_Transition_pair_le 5 counterResetDestSix s hs
    advanceRegimeDispatch_five a b

/-- `advanceClockPotential_drift_affine_of_resetDest` at `p = 5`, `hdisp` discharged. -/
theorem advanceClockPotentialDriftAffineFive (s : ℝ) (hs : 0 ≤ s)
    (n : ℕ) (c : Config (AgentState L K))
    (hcard : Multiset.card c = n) (hc2 : 2 ≤ Multiset.card c) :
    ∫⁻ c', advanceClockPotential (L := L) (K := K) 5 s c'
        ∂((NonuniformMajority L K).transitionKernel c)
      ≤ ENNReal.ofReal (1 + 2 * (Real.exp s - 1) / (n : ℝ))
          * advanceClockPotential (L := L) (K := K) 5 s c
        + 2 * (ENNReal.ofReal (Real.exp s) * freshVal (L := L) s) :=
  advanceClockPotential_drift_affine_of_resetDest 5 counterResetDestSix s hs
    advanceRegimeDispatch_five n c hcard hc2

end AdvanceNoOvershoot

end Ripple.PopulationProtocol.ExactMajority

end
