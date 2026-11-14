import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockAssembly
import Ripple.PopulationProtocol.ExactMajority.Probability.ThresholdEpidemic

/-!
# The exit and spread rows of the clock producer (N12, step 6)

PHASE3 P15 has two rows: the first Phase-4 seed occurs within `logWindow n 400` of
the all-cap time (equation (65)), and the phase threshold then spreads to every agent
(the coupon-collector half-epidemics). The second row is the N08 producer
`ThresholdEpidemic.threshold_spread_sharp_tail`; this file discharges it, with the
deadline arithmetic (66) and the monotonicity of the threshold along the actual trace.
The first row is isolated as the named event `ExitDeadlineAt`.

`asynchronous_clock_estimate_of_global_inputs` is the N12 headline from the global
form of the remaining inputs: the virtual-core tail (steps 3–4) and the exit-deadline
tail (P15 (65)), with the explicit N08 spread error added to the budget.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockExit

open TimeTheorem PairLog StageEventSpec PhaseThreeClockCore PhaseThreeClockTransfer
  PhaseThreeClockProducer PhaseThreeClockAssembly

variable {n : ℕ} (init : InputCfg n)

/-! ## The threshold is absorbing along the actual trace -/

theorem allGE_trace_succ (ω : InputLog n) (q t : ℕ) (h : allGE q (trace init ω t)) :
    allGE q (trace init ω (t + 1)) := by
  intro a ha
  rw [← labelsAt_config] at ha
  obtain ⟨k, -, hk⟩ := Multiset.mem_map.mp ha
  rw [← hk]
  have hprev : ∀ i, q ≤ (labelsAt init ω t i).phase.val :=
    fun i => h _ (PhaseThreeClockVirtual.labelsAt_mem_trace init ω t i)
  cases hd : drawLabels init ω (t + 1) with
  | none =>
      have hstep := PairLogAuxiliary.labelsAt_succ_eq_auxStep init ω t
      rw [hd] at hstep
      rw [hstep]
      exact hprev k
  | some ij =>
      obtain ⟨i, j⟩ := ij
      obtain ⟨-, -, -, hother⟩ := labelsAt_selected_transition init ω t i j hd
      by_cases hki : k = i
      · subst hki
        exact (ThresholdEpidemic.selected_labels_threshold_infection init ω t q k j hd
          (Or.inl (hprev k))).1
      by_cases hkj : k = j
      · subst hkj
        exact (ThresholdEpidemic.selected_labels_threshold_infection init ω t q i k hd
          (Or.inr (hprev k))).2
      rw [hother k hki hkj]
      exact hprev k

theorem allGE_trace_mono (ω : InputLog n) (q : ℕ) {t t' : ℕ} (htt : t ≤ t')
    (h : allGE q (trace init ω t)) : allGE q (trace init ω t') := by
  induction t', htt using Nat.le_induction with
  | base => exact h
  | succ t' _ ih => exact allGE_trace_succ init ω q t' ih

/-! ## The deadline arithmetic (66) -/

theorem logWindow_le_real (hn : 1 ≤ n) (c : ℕ) :
    (logWindow n c : ℝ) ≤ (c : ℝ) * (n : ℝ) * Real.log (n : ℝ) + 1 := by
  unfold logWindow
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  exact (Nat.ceil_lt_add_one (by positivity)).le

theorem logWindow_ge_real (c : ℕ) :
    (c : ℝ) * (n : ℝ) * Real.log (n : ℝ) ≤ (logWindow n c : ℝ) := by
  unfold logWindow
  exact Nat.le_ceil _

/-- PHASE3 (66): the activation allowance, the all-cap deadline, the exit allowance and
a spread window of at most `3000 n ln n` fit before the final horizon. -/
theorem exit_deadline_arith (hn : 2 ≤ n) (u : ℕ) (hu : u ≤ 3000) :
    2 * logWindow n 6 + logWindow n 16000 + logWindow n 400 + logWindow n u ≤
      logWindow n 20000 := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log (n : ℝ) := by
    have := Real.log_two_gt_d9
    have h2 : Real.log 2 ≤ Real.log (n : ℝ) := Real.log_le_log (by norm_num) hnR
    linarith
  have hx : (1 : ℝ) ≤ (n : ℝ) * Real.log (n : ℝ) := by nlinarith
  have huR : (u : ℝ) ≤ 3000 := by exact_mod_cast hu
  have h6 := logWindow_le_real (n := n) hn1 6
  have h16000 := logWindow_le_real (n := n) hn1 16000
  have h400 := logWindow_le_real (n := n) hn1 400
  have hu' := logWindow_le_real (n := n) hn1 u
  have h20000 : (20000 : ℝ) * (n : ℝ) * Real.log (n : ℝ) ≤ (logWindow n 20000 : ℝ) :=
    logWindow_ge_real 20000
  have hux : (u : ℝ) * (n : ℝ) * Real.log (n : ℝ) ≤ 3000 * (n : ℝ) * Real.log (n : ℝ) := by
    have hpos : 0 ≤ (n : ℝ) * Real.log (n : ℝ) := by linarith
    have := mul_le_mul_of_nonneg_right huR hpos
    linarith [this]
  have hcast : ((2 * logWindow n 6 + logWindow n 16000 + logWindow n 400 + logWindow n u : ℕ) : ℝ) ≤
      (logWindow n 20000 : ℝ) := by
    push_cast at h6 h16000 h400 hu' h20000 ⊢
    linarith [h6, h16000, h400, hu', h20000, hux, hx]
  exact_mod_cast hcast

/-! ## The two P15 rows as named events -/

/-- P15 (65): the genuine first Phase-4 seed occurs by `cap + logWindow n 400` for every
virtual cap witness of the entry at `s`. -/
def ExitDeadlineAt (s : ℕ) (ω : InputLog n) : Prop :=
  ∃ ρ : ℕ, firstPhaseSeed init 4 ρ ω ∧
    ∀ T (w : ClockTimes init), T ≤ earlyHorizon n → AsyncEntry init ω s T →
      VirtualClockCore init ω s T w → ρ ≤ w.cap + logWindow n 400

/-- P15 (spread): from the genuine first Phase-4 seed the threshold spreads within
`logWindow n u`. This is the complement of the N08 event. -/
def SpreadGood (u : ℕ) (ω : InputLog n) : Prop :=
  ∀ ρ : ℕ, firstPhaseSeed init 4 ρ ω → allGE 4 (trace init ω (ρ + logWindow n u))

theorem exitGoodAt_of (hn : 2 ≤ n) {u : ℕ} (hu : u ≤ 3000) {s : ℕ} {ω : InputLog n}
    (hv : VirtualGoodAt init s ω) (hd : ExitDeadlineAt init s ω) (hsp : SpreadGood init u ω) :
    ExitGoodAt init s ω := by
  obtain ⟨T, w, hT, hentry, hcore⟩ := hv
  obtain ⟨ρ, hexit, hafter⟩ := hd
  have hρ := hafter T w hT hentry hcore
  have hcap := hcore.cap_from_activation
  have hTd := hentry.deadline
  have harith := exit_deadline_arith hn u hu
  have hdead : ρ + logWindow n u ≤ s + logWindow n 20000 := by
    unfold activationHorizon at hTd
    omega
  refine ⟨ρ, hexit, by omega, ?_, hafter⟩
  exact allGE_trace_mono init ω 4 hdead (hsp ρ hexit)

/-- The N08 producer in the form of `SpreadGood`. -/
theorem spread_tail (hinput : ThresholdEpidemic.GoodInput n init) (u : ℕ) (hu : 1 ≤ u) :
    law init {ω | ¬ SpreadGood init u ω} ≤
      ENNReal.ofReal (Real.exp 3 * Real.rpow (n : ℝ) (1 - (u : ℝ))) := by
  have h := ThresholdEpidemic.threshold_spread_sharp_tail init hinput ⟨4, by norm_num⟩
    (by norm_num) u hu
  refine le_trans (measure_mono ?_) h
  intro ω hω
  simp only [Set.mem_setOf_eq, SpreadGood, not_forall] at hω
  obtain ⟨ρ, hexit, hbad⟩ := hω
  exact ⟨ρ, hexit, hbad⟩

/-! ## The headline from the global inputs -/

/-- The remaining producer inputs in global form: the virtual-core tail of steps 3–4
and the exit-deadline tail of P15 (65). -/
structure ClockProducerInputsGlobal (ε₁ ε₂ : ℝ≥0∞) : Prop where
  virtual_core_tail : law init {ω | ∃ s : ℕ, seedTime init 3 ω = (s : WithTop ℕ) ∧
      SeedProfile n init (trace init ω s) ∧
      (∃ T, T ≤ earlyHorizon n ∧ AsyncEntry init ω s T) ∧ ¬ VirtualGoodAt init s ω} ≤ ε₁
  exit_deadline_tail : law init {ω | ∃ s : ℕ, seedTime init 3 ω = (s : WithTop ℕ) ∧
      VirtualGoodAt init s ω ∧ ¬ ExitDeadlineAt init s ω} ≤ ε₂

theorem clockFailureAt_subset_global {u : ℕ} (hn : 2 ≤ n) (hu : u ≤ 3000) :
    clockFailureAt init ⊆
      {ω | ∃ s : ℕ, seedTime init 3 ω = (s : WithTop ℕ) ∧
        SeedProfile n init (trace init ω s) ∧
        (∃ T, T ≤ earlyHorizon n ∧ AsyncEntry init ω s T) ∧ ¬ VirtualGoodAt init s ω} ∪
      ({ω | ∃ s : ℕ, seedTime init 3 ω = (s : WithTop ℕ) ∧
        VirtualGoodAt init s ω ∧ ¬ ExitDeadlineAt init s ω} ∪
      {ω | ¬ SpreadGood init u ω}) := by
  rintro ω ⟨s, hs, hsp, hbad⟩
  by_cases hv : VirtualGoodAt init s ω
  · by_cases hd : ExitDeadlineAt init s ω
    · by_cases hspr : SpreadGood init u ω
      · exfalso
        exact hbad.2 (reviewedClockGood_of_good init (by omega) hv (exitGoodAt_of init hn hu hv hd hspr))
      · exact Or.inr (Or.inr hspr)
    · exact Or.inr (Or.inl ⟨s, hs, hv, hd⟩)
  · exact Or.inl ⟨s, hs, hsp, hbad.1, hv⟩

/-- The N12 headline from the global inputs and the §11 budget, with the N08 spread
error `e^3 n^{1-u}` discharged. -/
theorem asynchronous_clock_estimate_of_global_inputs
    (hinput : ThresholdEpidemic.GoodInput n init) {ε₁ ε₂ : ℝ≥0∞}
    (h : ClockProducerInputsGlobal init ε₁ ε₂) (u : ℕ) (hu : 1 ≤ u) (hu' : u ≤ 3000)
    (hbudget : ε₁ + (ε₂ + ENNReal.ofReal (Real.exp 3 * Real.rpow (n : ℝ) (1 - (u : ℝ)))) ≤
      ENNReal.ofReal (8 / (n : ℝ) ^ 5)) :
    law init (phaseClockFailure (reviewedStageEvents n init)) ≤
      ENNReal.ofReal (8 / (n : ℝ) ^ 5) := by
  have h40 : 40 ≤ n := (time_population_bounds hinput.1).2
  calc law init (phaseClockFailure (reviewedStageEvents n init))
      ≤ law init (clockFailureAt init) := measure_mono (phaseClockFailure_subset init)
    _ ≤ law init _ := measure_mono (clockFailureAt_subset_global init (u := u) (by omega) hu')
    _ ≤ law init _ + law init (_ ∪ _) := measure_union_le _ _
    _ ≤ law init _ + (law init _ + law init _) :=
        add_le_add le_rfl (measure_union_le _ _)
    _ ≤ ε₁ + (ε₂ + ENNReal.ofReal (Real.exp 3 * Real.rpow (n : ℝ) (1 - (u : ℝ)))) :=
        add_le_add h.virtual_core_tail (add_le_add h.exit_deadline_tail (spread_tail init hinput u hu))
    _ ≤ ENNReal.ofReal (8 / (n : ℝ) ^ 5) := hbudget

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockExit

end
