/-
Partial N11a development.

It supplies the entry interface, deterministic prefix invariants,
pair-log one-step estimates, the Phase-1 epidemic tail, and scalar budgets.
The complete phase_zero_entry_estimate producer is still unfinished.
-/

import Ripple.PopulationProtocol.ExactMajority.Probability.ThresholdEpidemic
import Ripple.PopulationProtocol.ExactMajority.Probability.StageEventSpec
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase0InitialFresh
import Ripple.PopulationProtocol.ExactMajority.Probability.RoleSplitFreeTargetFloor
import Ripple.PopulationProtocol.ExactMajority.Analysis.Invariants
import Mathlib.Tactic.Linarith

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped BigOperators ENNReal NNReal MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.PhaseZeroEntry

open TimeTheorem

/-! ## Exact entry interface and deterministic mass consequences -/

/-- The genuine first time when every agent has phase at least one. -/
def IsFirstAllPhaseOne {n : ℕ} (init : InputCfg n)
    (ω : InputLog n) (s : ℕ) : Prop :=
  StageEventSpec.firstHit
    (StageEventSpec.allGE (n := n) 1) (trace init ω) s

/-- Integer small-bias mass restricted to Main agents. -/
def mainSmallBiasSum {L K : ℕ} (c : Cfg L K) : ℤ :=
  (c.map (fun a =>
    if a.role = .main then AgentState.smallBiasInt a else 0)).sum

/-- The configuration conclusions of the Phase-0 theorem.
The existing RoleSplitGood conclusion is derived by role_good below. -/
structure PhaseOneEntryProfile {n : ℕ} (init : InputCfg n)
    (ω : InputLog n) (s : ℕ) : Prop where
  all_one :
    ∀ a ∈ trace init ω s, a.phase.val = 1
  final_roles :
    StageEventSpec.finalRoles (n := n) (trace init ω s)
  main_lower :
    (99 / 200 : ℝ) * (n : ℝ) ≤
      (RoleSplitConcentration.mainCount (trace init ω s) : ℝ)
  main_upper :
    (RoleSplitConcentration.mainCount (trace init ω s) : ℝ) ≤
      (101 / 200 : ℝ) * (n : ℝ)
  clock_lower :
    (97 / 400 : ℝ) * (n : ℝ) ≤
      (RoleSplitConcentration.clockCount (trace init ω s) : ℝ)
  reserve_lower :
    (97 / 400 : ℝ) * (n : ℝ) ≤
      (RoleSplitConcentration.reserveCount (trace init ω s) : ℝ)
  clock_counter :
    ∀ a ∈ trace init ω s, a.role = .clock →
      30 * PhaseThreeModel.Numeric.clockHours n ≤ a.counter.val
  nonmain_zero :
    ∀ a ∈ trace init ω s, a.role ≠ .main →
      a.smallBias.val = 3
  main_mass :
    mainSmallBiasSum (trace init ω s) = initialGap init

theorem first_all_phase_one_unique {n : ℕ} {init : InputCfg n}
    {ω : InputLog n} {s t : ℕ}
    (hs : IsFirstAllPhaseOne init ω s)
    (ht : IsFirstAllPhaseOne init ω t) :
    s = t := by
  apply Nat.le_antisymm
  · by_contra hle
    exact hs.2 t (Nat.lt_of_not_ge hle) ht.1
  · by_contra hle
    exact ht.2 s (Nat.lt_of_not_ge hle) hs.1

theorem first_all_phase_one_exists_le {n : ℕ} (init : InputCfg n)
    (ω : InputLog n) (T : ℕ)
    (hT : StageEventSpec.allGE (n := n) 1 (trace init ω T)) :
    ∃ s ≤ T, IsFirstAllPhaseOne init ω s := by
  classical
  have hex :
      ∃ s, StageEventSpec.allGE (n := n) 1 (trace init ω s) :=
    ⟨T, hT⟩
  refine ⟨Nat.find hex, Nat.find_min' hex hT, ?_⟩
  exact ⟨Nat.find_spec hex, fun u hu => Nat.find_min hex hu⟩

/-- The first-entry event is measurable in the complete pair-log past. -/
theorem first_all_phase_one_measurableSet {n : ℕ}
    (init : InputCfg n) (s : ℕ) :
    MeasurableSet[
      PairLog.pairLogFiltration
        (PhaseThreeModel.Numeric.hourIndex n) 256 s]
      {ω | IsFirstAllPhaseOne init ω s} := by
  have hnow :
      MeasurableSet[
        PairLog.pairLogFiltration
          (PhaseThreeModel.Numeric.hourIndex n) 256 s]
        {ω | StageEventSpec.allGE (n := n) 1 (trace init ω s)} :=
    (show MeasurableSet
        {c : InputCfg n | StageEventSpec.allGE (n := n) 1 c} from
      (Set.to_countable _).measurableSet).preimage
        (PairLog.measurable_trace_at init s)
  have hpast (u : ℕ) :
      MeasurableSet[
        PairLog.pairLogFiltration
          (PhaseThreeModel.Numeric.hourIndex n) 256 s]
        {ω | u < s →
          ¬ StageEventSpec.allGE (n := n) 1 (trace init ω u)} := by
    by_cases hu : u < s
    · simpa only [hu, true_implies] using
        (show MeasurableSet
            {c : InputCfg n |
              ¬ StageEventSpec.allGE (n := n) 1 c} from
          (Set.to_countable _).measurableSet).preimage
            (PairLog.measurable_trace_at_of_le init hu.le)
    · simp only [hu, false_implies, Set.setOf_true]
      exact MeasurableSet.univ
  have heq :
      {ω | IsFirstAllPhaseOne init ω s} =
        {ω | StageEventSpec.allGE (n := n) 1 (trace init ω s)} ∩
          ⋂ u : ℕ, {ω | u < s →
            ¬ StageEventSpec.allGE (n := n) 1 (trace init ω u)} := by
    ext ω
    simp only [IsFirstAllPhaseOne, StageEventSpec.firstHit,
      Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [heq]
  exact hnow.inter (MeasurableSet.iInter hpast)

/-- Every reconstructed log follows protocol reachability, including
logs outside the support of the probability law. -/
theorem phase_zero_trace_reachable {n : ℕ}
    (init : InputCfg n) (ω : InputLog n) (s : ℕ) :
    (NonuniformMajority
      (PhaseThreeModel.Numeric.hourIndex n) 256).Reachable
      init (trace init ω s) := by
  simpa only [trace_zero] using
    (trace_reachable init ω (s := 0) (t := s) (Nat.zero_le s))

theorem phase_one_trace_final_roles {n : ℕ}
    (init : InputCfg n) (hinput : ThresholdEpidemic.GoodInput n init)
    (ω : InputLog n) (s : ℕ)
    (hone : ∀ a ∈ trace init ω s, a.phase.val = 1) :
    StageEventSpec.finalRoles (n := n) (trace init ω s) := by
  have hpartition :=
    post_phase_zero_role_partition init (trace init ω s)
      hinput.2.1 (phase_zero_trace_reachable init ω s)
      (fun a ha => by rw [hone a ha])
  clear hinput
  intro a ha
  rcases hpartition a ha with hm | hr | hc | hten
  · exact Or.inl hm
  · exact Or.inr (Or.inr hr)
  · exact Or.inr (Or.inl hc)
  · have hphase := hone a ha
    omega

/-- PHASE02 section 2.8: the compiled integer accumulator invariant. -/
theorem phase_zero_trace_small_mass {n : ℕ}
    (init : InputCfg n) (hinput : ThresholdEpidemic.GoodInput n init)
    (ω : InputLog n) (s : ℕ) :
    smallBiasSum (trace init ω s) = initialGap init :=
  reachable_smallBiasSum_eq_initialGap_all_phases
    init (trace init ω s) hinput.2.1
    (phase_zero_trace_reachable init ω s)

theorem phase_one_trace_nonmain_zero {n : ℕ}
    (init : InputCfg n) (hinput : ThresholdEpidemic.GoodInput n init)
    (ω : InputLog n) (s : ℕ)
    (hroles : StageEventSpec.finalRoles (n := n) (trace init ω s)) :
    ∀ a ∈ trace init ω s, a.role ≠ .main →
      a.smallBias.val = 3 := by
  have hzero :=
    reachable_nonMain_smallBias_zero
      init (trace init ω s) hinput.2.1
      (phase_zero_trace_reachable init ω s)
  intro a ha hnotmain
  rcases hroles a ha with hm | hc | hr
  · exact False.elim (hnotmain hm)
  · exact hzero a ha (Or.inr hc)
  · exact hzero a ha (Or.inl hr)

theorem mainSmallBiasSum_eq_smallBiasSum {L K : ℕ}
    (c : Cfg L K)
    (hzero : ∀ a ∈ c, a.role ≠ .main → a.smallBias.val = 3) :
    mainSmallBiasSum c = smallBiasSum c := by
  revert hzero
  induction c using Multiset.induction_on with
  | empty =>
      intro hzero
      simp [mainSmallBiasSum, smallBiasSum]
  | cons a c ih =>
      intro hzero
      have htail :
          ∀ x ∈ c, x.role ≠ .main → x.smallBias.val = 3 :=
        fun x hx => hzero x (Multiset.mem_cons_of_mem hx)
      have hi := ih htail
      by_cases hm : a.role = .main
      · simpa [mainSmallBiasSum, smallBiasSum, hm] using
          congrArg (fun z : ℤ => AgentState.smallBiasInt a + z) hi
      · have hb : AgentState.smallBiasInt a = 0 := by
          unfold AgentState.smallBiasInt
          rw [hzero a (Multiset.mem_cons_self a c) hm]
          norm_num
        simpa [mainSmallBiasSum, smallBiasSum, hm, hb] using hi

theorem phase_one_trace_main_mass {n : ℕ}
    (init : InputCfg n) (hinput : ThresholdEpidemic.GoodInput n init)
    (ω : InputLog n) (s : ℕ)
    (hroles : StageEventSpec.finalRoles (n := n) (trace init ω s)) :
    mainSmallBiasSum (trace init ω s) = initialGap init := by
  calc
    mainSmallBiasSum (trace init ω s) =
        smallBiasSum (trace init ω s) :=
      mainSmallBiasSum_eq_smallBiasSum _
        (phase_one_trace_nonmain_zero init hinput ω s hroles)
    _ = initialGap init :=
      phase_zero_trace_small_mass init hinput ω s

/-- Equation (8) implies the existing RoleSplitGood interface. -/
theorem PhaseOneEntryProfile.role_good {n : ℕ}
    {init : InputCfg n} {ω : InputLog n} {s : ℕ}
    (h : PhaseOneEntryProfile init ω s) :
    RoleSplitConcentration.RoleSplitGood
      (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
      (1 / 25 : ℝ) n (trace init ω s) := by
  have hmcr :
      RoleSplitConcentration.roleMCRCount (trace init ω s) = 0 := by
    unfold RoleSplitConcentration.roleMCRCount
    apply Multiset.countP_eq_zero.mpr
    intro a ha
    rcases h.final_roles a ha with hm | hc | hr
    · simp [hm]
    · simp [hc]
    · simp [hr]
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  refine ⟨hmcr, ?_, ?_, ?_, ?_⟩
  · linarith only [h.main_lower, hn]
  · linarith only [h.main_upper, hn]
  · linarith only [h.clock_lower, hn]
  · linarith only [h.reserve_lower, hn]

theorem PhaseOneEntryProfile.nonmain_smallBiasInt_eq_zero {n : ℕ}
    {init : InputCfg n} {ω : InputLog n} {s : ℕ}
    (h : PhaseOneEntryProfile init ω s) :
    ∀ a ∈ trace init ω s, a.role ≠ .main →
      AgentState.smallBiasInt a = 0 := by
  intro a ha hm
  unfold AgentState.smallBiasInt
  rw [h.nonmain_zero a ha hm]
  norm_num

/-- Deterministic assembly from the phase, count, and counter bounds.
This is not the probability producer. -/
theorem phase_one_entry_profile_of_bounds {n : ℕ}
    (init : InputCfg n) (hinput : ThresholdEpidemic.GoodInput n init)
    (ω : InputLog n) (s : ℕ)
    (hone : ∀ a ∈ trace init ω s, a.phase.val = 1)
    (hmainlo :
      (99 / 200 : ℝ) * (n : ℝ) ≤
        (RoleSplitConcentration.mainCount (trace init ω s) : ℝ))
    (hmainhi :
      (RoleSplitConcentration.mainCount (trace init ω s) : ℝ) ≤
        (101 / 200 : ℝ) * (n : ℝ))
    (hclock :
      (97 / 400 : ℝ) * (n : ℝ) ≤
        (RoleSplitConcentration.clockCount (trace init ω s) : ℝ))
    (hreserve :
      (97 / 400 : ℝ) * (n : ℝ) ≤
        (RoleSplitConcentration.reserveCount (trace init ω s) : ℝ))
    (hcounter :
      ∀ a ∈ trace init ω s, a.role = .clock →
        30 * PhaseThreeModel.Numeric.clockHours n ≤ a.counter.val) :
    PhaseOneEntryProfile init ω s := by
  have hroles := phase_one_trace_final_roles init hinput ω s hone
  exact
    { all_one := hone
      final_roles := hroles
      main_lower := hmainlo
      main_upper := hmainhi
      clock_lower := hclock
      reserve_lower := hreserve
      clock_counter := hcounter
      nonmain_zero := phase_one_trace_nonmain_zero init hinput ω s hroles
      main_mass := phase_one_trace_main_mass init hinput ω s hroles }

/-- The complete profile at a fixed time is measurable in that past. -/
theorem phase_one_entry_profile_measurableSet {n : ℕ}
    (init : InputCfg n) (s : ℕ) :
    MeasurableSet[
      PairLog.pairLogFiltration
        (PhaseThreeModel.Numeric.hourIndex n) 256 s]
      {ω | PhaseOneEntryProfile init ω s} := by
  let P : InputCfg n → Prop := fun c =>
    (∀ a ∈ c, a.phase.val = 1) ∧
    StageEventSpec.finalRoles (n := n) c ∧
    (99 / 200 : ℝ) * (n : ℝ) ≤
      (RoleSplitConcentration.mainCount c : ℝ) ∧
    (RoleSplitConcentration.mainCount c : ℝ) ≤
      (101 / 200 : ℝ) * (n : ℝ) ∧
    (97 / 400 : ℝ) * (n : ℝ) ≤
      (RoleSplitConcentration.clockCount c : ℝ) ∧
    (97 / 400 : ℝ) * (n : ℝ) ≤
      (RoleSplitConcentration.reserveCount c : ℝ) ∧
    (∀ a ∈ c, a.role = .clock →
      30 * PhaseThreeModel.Numeric.clockHours n ≤ a.counter.val) ∧
    (∀ a ∈ c, a.role ≠ .main → a.smallBias.val = 3) ∧
    mainSmallBiasSum c = initialGap init
  have hP : MeasurableSet {c : InputCfg n | P c} :=
    (Set.to_countable _).measurableSet
  have heq :
      {ω | PhaseOneEntryProfile init ω s} =
        (fun ω => trace init ω s) ⁻¹' {c : InputCfg n | P c} := by
    ext ω
    change PhaseOneEntryProfile init ω s ↔ P (trace init ω s)
    constructor
    · intro h
      exact
        ⟨h.all_one, h.final_roles, h.main_lower, h.main_upper,
          h.clock_lower, h.reserve_lower, h.clock_counter,
          h.nonmain_zero, h.main_mass⟩
    · rintro ⟨hone, hroles, hmainlo, hmainhi, hclock, hreserve,
        hcounter, hzero, hmass⟩
      exact
        { all_one := hone
          final_roles := hroles
          main_lower := hmainlo
          main_upper := hmainhi
          clock_lower := hclock
          reserve_lower := hreserve
          clock_counter := hcounter
          nonmain_zero := hzero
          main_mass := hmass }
  rw [heq]
  exact hP.preimage (PairLog.measurable_trace_at init s)

theorem first_all_phase_one_measurableSet_ambient {n : ℕ}
    (init : InputCfg n) (s : ℕ) :
    MeasurableSet {ω | IsFirstAllPhaseOne init ω s} :=
  (PairLog.pairLogFiltration
    (PhaseThreeModel.Numeric.hourIndex n) 256).le s _
      (first_all_phase_one_measurableSet init s)

theorem phase_one_entry_profile_measurableSet_ambient {n : ℕ}
    (init : InputCfg n) (s : ℕ) :
    MeasurableSet {ω | PhaseOneEntryProfile init ω s} :=
  (PairLog.pairLogFiltration
    (PhaseThreeModel.Numeric.hourIndex n) 256).le s _
      (phase_one_entry_profile_measurableSet init s)

theorem phase_zero_entry_success_measurableSet {n : ℕ}
    (init : InputCfg n) (T : ℕ) :
    MeasurableSet
      {ω | ∃ s ≤ T,
        IsFirstAllPhaseOne init ω s ∧ PhaseOneEntryProfile init ω s} := by
  have hterm (s : ℕ) :
      MeasurableSet
        {ω | s ≤ T ∧
          IsFirstAllPhaseOne init ω s ∧
            PhaseOneEntryProfile init ω s} := by
    by_cases hs : s ≤ T
    · simpa only [hs, true_and] using
        (first_all_phase_one_measurableSet_ambient init s).inter
          (phase_one_entry_profile_measurableSet_ambient init s)
    · simp only [hs, false_and, Set.setOf_false]
      exact MeasurableSet.empty
  have heq :
      {ω | ∃ s ≤ T,
        IsFirstAllPhaseOne init ω s ∧ PhaseOneEntryProfile init ω s} =
        ⋃ s : ℕ, {ω | s ≤ T ∧
          IsFirstAllPhaseOne init ω s ∧
            PhaseOneEntryProfile init ω s} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
  rw [heq]
  exact MeasurableSet.iUnion hterm

theorem phase_zero_entry_failure_measurableSet {n : ℕ}
    (init : InputCfg n) (T : ℕ) :
    MeasurableSet
      {ω | ¬ ∃ s ≤ T,
        IsFirstAllPhaseOne init ω s ∧ PhaseOneEntryProfile init ω s} :=
  (phase_zero_entry_success_measurableSet init T).compl

/-! ## Scalar calibration and genuine-first-seed spread -/

private theorem phase_zero_population_at {e n : ℕ}
    (he : 24 ≤ e) (hn : 5 * 2 ^ e ≤ n) :
    2 ^ 24 ≤ n := by
  calc
    2 ^ 24 ≤ 2 ^ e :=
      Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) he
    _ = 1 * 2 ^ e := by simp
    _ ≤ 5 * 2 ^ e :=
      Nat.mul_le_mul_right (2 ^ e) (by decide : 1 ≤ 5)
    _ ≤ n := hn

/-- The threshold is used by monotonicity at a variable exponent.
No evaluation of the enormous outer power occurs. -/
theorem phase_zero_population_lower {n : ℕ}
    (hn : timePopulationThreshold ≤ n) :
    2 ^ 24 ≤ n := by
  obtain ⟨hnpos, hlog⟩ := ScalarTails.time_population_scalar_bounds hn
  have hlt : ((2 : ℝ) ^ 24) < (n : ℝ) := by
    have hl : Real.log ((2 : ℝ) ^ 24) < Real.log (n : ℝ) := by
      rw [Real.log_pow]
      push_cast
      linarith [Real.log_two_lt_d9]
    exact (Real.log_lt_log_iff (by positivity) hnpos).1 hl
  exact_mod_cast hlt.le

theorem phase_one_spread_scalar {x : ℝ} (hx : 40 ≤ x) :
    Real.exp 3 * Real.rpow x (-6) ≤ 1 / x ^ 4 := by
  have hxp : 0 < x := by linarith only [hx]
  have hsquare : (40 : ℝ) ^ 2 ≤ x ^ 2 := by
    have hprod : 0 ≤ (x - 40) * (x + 40) :=
      mul_nonneg (sub_nonneg.mpr hx) (by linarith only [hx])
    nlinarith only [hprod]
  have hnum : Real.exp 3 ≤ x ^ 2 :=
    TimeTheorem.time_exp_three_lt.le.trans
      (by nlinarith only [hsquare])
  calc
    Real.exp 3 * Real.rpow x (-6) = Real.exp 3 / x ^ 6 := by
      rw [show Real.rpow x (-6) = x ^ (-(6 : ℝ)) from rfl,
        Real.rpow_neg hxp.le, Real.rpow_ofNat, div_eq_mul_inv]
    _ ≤ x ^ 2 / x ^ 6 :=
      div_le_div_of_nonneg_right hnum (by positivity)
    _ = 1 / x ^ 4 := by
      field_simp [hxp.ne'] <;> ring

/-- PHASE02 section 2.7: N08, specialized to Phase 1 and seven
logarithmic time units. The bound is under the original pair-log law. -/
theorem phase_one_spread_tail {n : ℕ} (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init) :
    law init
      {ω | ∃ s : ℕ, firstPhaseSeed init 1 s ω ∧
        ¬ (∀ a ∈ trace init ω (s + logWindow n 7),
          1 ≤ a.phase.val)} ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 4) := by
  have hn : 40 ≤ n := (time_population_bounds hinput.1).2
  have hnR : (40 : ℝ) ≤ n := by exact_mod_cast hn
  have htail := ThresholdEpidemic.threshold_spread_sharp_tail
    init hinput (⟨1, by decide⟩ : Fin 11) (by decide) 7 (by decide)
  clear hinput
  change
    law init
      {ω | ∃ s : ℕ, firstPhaseSeed init 1 s ω ∧
        ¬ (∀ a ∈ trace init ω (s + logWindow n 7),
          1 ≤ a.phase.val)} ≤
      ENNReal.ofReal
        (Real.exp 3 * Real.rpow (n : ℝ) (1 - (7 : ℝ)))
    at htail
  rw [show (1 : ℝ) - 7 = -6 by norm_num] at htail
  exact htail.trans
    (ENNReal.ofReal_le_ofReal (phase_one_spread_scalar hnR))

/-- The same epidemic estimate supplies a genuine first all-threshold-one
time, rather than an arbitrarily chosen successful endpoint. -/
theorem phase_one_spread_first_entry_tail {n : ℕ}
    (init : InputCfg n) (hinput : ThresholdEpidemic.GoodInput n init) :
    law init
      {ω | ∃ S : ℕ, firstPhaseSeed init 1 S ω ∧
        ¬ ∃ s ≤ S + logWindow n 7, IsFirstAllPhaseOne init ω s} ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 4) := by
  calc
    law init
        {ω | ∃ S : ℕ, firstPhaseSeed init 1 S ω ∧
          ¬ ∃ s ≤ S + logWindow n 7, IsFirstAllPhaseOne init ω s} ≤
      law init
        {ω | ∃ S : ℕ, firstPhaseSeed init 1 S ω ∧
          ¬ (∀ a ∈ trace init ω (S + logWindow n 7),
            1 ≤ a.phase.val)} := by
        apply measure_mono
        rintro ω ⟨S, hseed, hnot⟩
        refine ⟨S, hseed, ?_⟩
        intro hall
        exact hnot
          (first_all_phase_one_exists_le init ω (S + logWindow n 7) hall)
    _ ≤ ENNReal.ofReal (1 / (n : ℝ) ^ 4) :=
      phase_one_spread_tail init hinput

/-- The scalar role-work allowance used by the stopped timer estimate. -/
theorem phase_zero_role_horizon_le {n : ℕ}
    (hpop : timePopulationThreshold ≤ n) :
    ((241 * n + logWindow n 20 : ℕ) : ℝ) ≤
      40 * (n : ℝ) * Real.log (n : ℝ) := by
  have hnlarge := (time_population_bounds hpop).2
  have hloglarge := (ScalarTails.time_population_scalar_bounds hpop).2
  clear hpop
  have hnR : (1 : ℝ) ≤ n := by
    exact_mod_cast (show 1 ≤ n by omega)
  have hlogzero : 0 ≤ Real.log (n : ℝ) := by
    linarith only [hloglarge]
  have hmul : (100 : ℝ) * n ≤ (n : ℝ) * Real.log (n : ℝ) := by
    calc
      (100 : ℝ) * n = (n : ℝ) * 100 := mul_comm _ _
      _ ≤ (n : ℝ) * Real.log (n : ℝ) :=
        mul_le_mul_of_nonneg_left hloglarge (Nat.cast_nonneg n)
  have hceil : (logWindow n 20 : ℝ) <
      20 * (n : ℝ) * Real.log (n : ℝ) + 1 := by
    change (Nat.ceil ((20 : ℝ) * (n : ℝ) * Real.log (n : ℝ)) : ℝ) < _
    exact Nat.ceil_lt_add_one (by positivity)
  push_cast
  nlinarith only [hnR, hmul, hceil]

/-- PHASE02 section 2.7: the rounded role, first-seed and spread windows
fit into 348nH, hence into the requested 350nH. -/
theorem phase_zero_horizon_le {n : ℕ}
    (hpop : timePopulationThreshold ≤ n) :
    241 * n + logWindow n 20 +
      300 * n * PhaseThreeModel.Numeric.clockHours n +
      logWindow n 7 ≤
      348 * n * PhaseThreeModel.Numeric.clockHours n := by
  obtain ⟨hnlarge, _, hlog, hlogH, _, _⟩ :=
    time_hour_calibration hpop
  obtain ⟨_, hloglarge⟩ := ScalarTails.time_population_scalar_bounds hpop
  clear hpop
  have hnR : (1 : ℝ) ≤ n := by
    exact_mod_cast (show 1 ≤ n by omega)
  have hlogzero : 0 ≤ Real.log (n : ℝ) := by linarith only [hlog]
  have hHlarge :
      (100 : ℝ) ≤ PhaseThreeModel.Numeric.clockHours n :=
    hloglarge.trans hlogH
  have hlogmul :
      (n : ℝ) * Real.log (n : ℝ) ≤
        (n : ℝ) * PhaseThreeModel.Numeric.clockHours n :=
    mul_le_mul_of_nonneg_left hlogH (Nat.cast_nonneg n)
  have hHmul :
      (100 : ℝ) * n ≤
        (n : ℝ) * PhaseThreeModel.Numeric.clockHours n := by
    calc
      (100 : ℝ) * n = (n : ℝ) * 100 := mul_comm _ _
      _ ≤ (n : ℝ) * PhaseThreeModel.Numeric.clockHours n :=
        mul_le_mul_of_nonneg_left hHlarge (Nat.cast_nonneg n)
  have hroleCeil : (logWindow n 20 : ℝ) <
      20 * (n : ℝ) * Real.log (n : ℝ) + 1 := by
    change (Nat.ceil ((20 : ℝ) * (n : ℝ) * Real.log (n : ℝ)) : ℝ) < _
    exact Nat.ceil_lt_add_one (by positivity)
  have hspreadCeil : (logWindow n 7 : ℝ) <
      7 * (n : ℝ) * Real.log (n : ℝ) + 1 := by
    change (Nat.ceil ((7 : ℝ) * (n : ℝ) * Real.log (n : ℝ)) : ℝ) < _
    exact Nat.ceil_lt_add_one (by positivity)
  have hreal :
      (241 : ℝ) * n + (logWindow n 20 : ℝ) +
        300 * (n : ℝ) * PhaseThreeModel.Numeric.clockHours n +
        (logWindow n 7 : ℝ) ≤
      348 * (n : ℝ) * PhaseThreeModel.Numeric.clockHours n := by
    nlinarith only [hnR, hHmul, hlogmul, hroleCeil, hspreadCeil]
  exact_mod_cast hreal

theorem phase_zero_entry_horizon_le {n : ℕ}
    (hpop : timePopulationThreshold ≤ n) :
    241 * n + logWindow n 20 +
      300 * n * PhaseThreeModel.Numeric.clockHours n +
      logWindow n 7 ≤
      350 * n * PhaseThreeModel.Numeric.clockHours n := by
  exact (phase_zero_horizon_le hpop).trans
    (Nat.mul_le_mul_right _
      (Nat.mul_le_mul_right n (by decide : 348 ≤ 350)))

theorem phase_zero_error_budget_le {x : ℝ} (hx : 40 ≤ x) :
    7 / x ^ 3 + 1 / x ^ 20 + 2 / x ^ 4 ≤ 8 / x ^ 3 := by
  have hxp : 0 < x := by linarith only [hx]
  have hpow : x ^ 4 ≤ x ^ 20 :=
    pow_le_pow_right₀
      (by linarith only [hx]) (by norm_num : 4 ≤ 20)
  have hsmall : 1 / x ^ 20 ≤ 1 / x ^ 4 := by
    rw [div_le_div_iff₀ (pow_pos hxp 20) (pow_pos hxp 4)]
    simpa only [one_mul] using hpow
  have hrest : 3 / x ^ 4 ≤ 1 / x ^ 3 := by
    rw [div_le_div_iff₀ (pow_pos hxp 4) (pow_pos hxp 3)]
    calc
      3 * x ^ 3 ≤ x * x ^ 3 :=
        mul_le_mul_of_nonneg_right
          (by linarith only [hx]) (pow_nonneg hxp.le 3)
      _ = 1 * x ^ 4 := by ring
  calc
    7 / x ^ 3 + 1 / x ^ 20 + 2 / x ^ 4 ≤
        7 / x ^ 3 + 1 / x ^ 4 + 2 / x ^ 4 :=
      add_le_add (add_le_add le_rfl hsmall) le_rfl
    _ = 7 / x ^ 3 + 3 / x ^ 4 := by ring
    _ ≤ 7 / x ^ 3 + 1 / x ^ 3 := add_le_add le_rfl hrest
    _ = 8 / x ^ 3 := by ring

theorem phase_zero_error_budget_ennreal {x : ℝ} (hx : 40 ≤ x) :
    ENNReal.ofReal (7 / x ^ 3) + ENNReal.ofReal (1 / x ^ 20) +
      ENNReal.ofReal (2 / x ^ 4) ≤ ENNReal.ofReal (8 / x ^ 3) := by
  have hxp : 0 < x := by linarith only [hx]
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal (phase_zero_error_budget_le hx)

/-! ## Phase-0 role ledgers on the actual pair-log trace -/

open RoleSplitConcentration PhaseThreeModel.OccurrenceScheduler

section RoleLedgers

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-- The contribution of one agent to the true free-target pool. -/
private def phaseZeroFreshWeight {L K : ℕ} (a : AgentState L K) : ℕ :=
  if freeTargetPred (L := L) (K := K) a then 1 else 0

/-- An MCR--MCR interaction creates exactly two free targets. -/
def phaseZeroFreshGain {L K : ℕ} (s t : AgentState L K) : ℕ :=
  if s.role = .mcr ∧ t.role = .mcr then 2 else 0
private lemma phaseZeroPhaseInit_assigned (p : Fin 11) (a : AgentState L K) :
    (phaseInit L K p a).assigned = a.assigned := by
  fin_cases p
  · unfold phaseInit; simp
  · unfold phaseInit; simp; split_ifs <;> simp [enterPhase10_assigned]
  · unfold phaseInit; simp
    by_cases h : a.smallBias.val ≤ 1 ∨ a.smallBias.val ≥ 5
    · simp [h, enterPhase10_assigned]
    · simp [h]
  · unfold phaseInit; simp; split <;> simp
  · unfold phaseInit; simp
  · unfold phaseInit; simp; split_ifs <;> simp
  · unfold phaseInit; simp; split_ifs <;> simp
  · unfold phaseInit; simp; split_ifs <;> simp
  · unfold phaseInit; simp
  · unfold phaseInit; simp <;> split_ifs <;> simp
  · unfold phaseInit; simp [enterPhase10_assigned]

/-- `stdCounterSubroutine` preserves the `assigned` flag (neither `advancePhase`,
`phaseInit`, nor `enterPhase10` ever writes `assigned`). -/
private lemma phaseZeroStdCounter_assigned (a : AgentState L K) :
    (stdCounterSubroutine L K a).assigned = a.assigned := by
  unfold stdCounterSubroutine
  split
  · -- advancePhaseWithInit = phaseInit (advancePhase a).phase (advancePhase a)
    unfold advancePhaseWithInit
    rw [phaseZeroPhaseInit_assigned]
    unfold advancePhase
    split <;> rfl
  · rfl

/-- The Standard Counter Subroutine keeps a `Clock` agent a `Clock` (local copy
of the private TopSplitDrift lemma). -/
private lemma phaseZeroStdCounter_clock_role (a : AgentState L K)
    (ha : a.role = .clock) :
    (stdCounterSubroutine L K a).role = .clock := by
  unfold stdCounterSubroutine
  split
  · exact advancePhaseWithInit_clock_role_eq L K a ha
  · exact ha


private theorem phaseZeroFreshWeight_stdCounter
    (a : AgentState L K) (ha : a.role = .clock) :
    phaseZeroFreshWeight (stdCounterSubroutine L K a) =
      phaseZeroFreshWeight a := by
  simp only [phaseZeroFreshWeight, freeTargetPred,
    phaseZeroStdCounter_clock_role a ha,
    phaseZeroStdCounter_assigned a, ha]

theorem phaseZero_freeTargetCount_add
    (c d : Config (AgentState L K)) :
    freeTargetCount (L := L) (K := K) (c + d) =
      freeTargetCount (L := L) (K := K) c +
        freeTargetCount (L := L) (K := K) d := by
  simp only [freeTargetCount, Multiset.countP_add]

private theorem phaseZero_freeTargetCount_pair
    (s t : AgentState L K) :
    freeTargetCount (L := L) (K := K)
        ({s, t} : Config (AgentState L K)) =
      phaseZeroFreshWeight s + phaseZeroFreshWeight t := by
  unfold freeTargetCount phaseZeroFreshWeight
  rw [show ({s, t} : Config (AgentState L K)) = s ::ₘ t ::ₘ 0 from rfl,
    Multiset.countP_cons, Multiset.countP_cons, Multiset.countP_zero]
  by_cases hs : freeTargetPred (L := L) (K := K) s <;>
    by_cases ht : freeTargetPred (L := L) (K := K) t <;>
      simp [hs, ht]

-- This finite check splits 5 * 5 * 2 * 2 role/assigned combinations.
-- The scoped allowance avoids imposing any global elaboration budget.
set_option maxHeartbeats 800000 in
/-- PHASE02 section 2.1: the actual Phase-0 rules increase the correct
free-target pool by two on MCR--MCR and preserve it otherwise. -/
theorem phaseZero_freeTarget_pair_balance
    (s t : AgentState L K)
    (hs : NotAssignedMcr (L := L) (K := K) s)
    (ht : NotAssignedMcr (L := L) (K := K) t) :
    freeTargetCount (L := L) (K := K)
        ({(Phase0Transition L K s t).1,
          (Phase0Transition L K s t).2} :
          Config (AgentState L K)) =
      freeTargetCount (L := L) (K := K)
          ({s, t} : Config (AgentState L K)) +
        phaseZeroFreshGain s t := by
  rw [phaseZero_freeTargetCount_pair, phaseZero_freeTargetCount_pair]
  by_cases hcc : s.role = .clock ∧ t.role = .clock
  · obtain ⟨hsc, htc⟩ := hcc
    have hstep :
        Phase0Transition L K s t =
          (stdCounterSubroutine L K s,
            stdCounterSubroutine L K t) := by
      unfold Phase0Transition
      simp only [hsc, htc, reduceCtorEq, and_self,
        and_true, true_and, and_false, false_and,
        if_true, if_false, ite_true, ite_false]
    rw [hstep, phaseZeroFreshWeight_stdCounter s hsc,
      phaseZeroFreshWeight_stdCounter t htc]
    simp [phaseZeroFreshGain, hsc, htc]
  · unfold NotAssignedMcr at hs ht
    rcases s with
      ⟨si, so, sp, sr, sa, sb, ssb, sh, sm, sf, sop, sc⟩
    rcases t with
      ⟨ti, tO, tp, tr, ta, tb, tsb, th, tm, tf, top, tc⟩
    cases sr <;> cases tr <;> cases sa <;> cases ta <;>
      first
      | (exfalso; exact hcc ⟨rfl, rfl⟩)
      | (exact False.elim (hs ⟨rfl, rfl⟩))
      | (exact False.elim (ht ⟨rfl, rfl⟩))
      | (simp only [Phase0Transition, phaseZeroFreshWeight,
          freeTargetPred, phaseZeroFreshGain,
          reduceCtorEq, ne_eq, and_true, and_false,
          true_and, false_and, and_self, if_true, if_false,
          ite_true, ite_false, not_true_eq_false,
          not_false_eq_true, Bool.not_true, Bool.not_false,
          Bool.true_eq_false, Bool.false_eq_true] <;> norm_num)

/-- Monotonicity for an actual Phase-0 step, including self-loops
caused by an inapplicable pair. -/
theorem phaseZero_freeTarget_stepOrSelf
    (c : Config (AgentState L K)) (s t : AgentState L K)
    (hall : Phase0Window.allPhase0 (L := L) (K := K) c)
    (hfresh : NoAssignedMcrConfig (L := L) (K := K) c) :
    freeTargetCount (L := L) (K := K) c ≤
      freeTargetCount (L := L) (K := K)
        (Protocol.stepOrSelf (NonuniformMajority L K) c s t) := by
  by_cases happ : Protocol.Applicable c s t
  · have hle : ({s, t} : Config (AgentState L K)) ≤ c := happ
    have hsmem : s ∈ c := Multiset.mem_of_le hle (by simp)
    have htmem : t ∈ c := Multiset.mem_of_le hle (by simp)
    have hsphase : s.phase.val = 0 :=
      congrArg Fin.val (hall s hsmem)
    have htphase : t.phase.val = 0 :=
      congrArg Fin.val (hall t htmem)
    have hroles :=
      Transition_roles_eq_phase0_of_both_phase0
        (L := L) (K := K) s t hsphase htphase
    have hassigned :=
      Transition_assigned_eq_phase0_of_both_phase0
        (L := L) (K := K) s t hsphase htphase
    have hcounts :
        freeTargetCount (L := L) (K := K)
            ({(Transition L K s t).1, (Transition L K s t).2} :
              Config (AgentState L K)) =
          freeTargetCount (L := L) (K := K)
            ({(Phase0Transition L K s t).1,
              (Phase0Transition L K s t).2} :
              Config (AgentState L K)) := by
      rw [phaseZero_freeTargetCount_pair, phaseZero_freeTargetCount_pair]
      simp only [phaseZeroFreshWeight, freeTargetPred,
        hroles.1, hroles.2, hassigned.1, hassigned.2]
      all_goals congr!
    have hbalance :=
      phaseZero_freeTarget_pair_balance s t
        (hfresh s hsmem) (hfresh t htmem)
    have hpair :
        freeTargetCount (L := L) (K := K)
            ({s, t} : Config (AgentState L K)) ≤
          freeTargetCount (L := L) (K := K)
            ({(Transition L K s t).1, (Transition L K s t).2} :
              Config (AgentState L K)) := by
      rw [hcounts, hbalance]
      exact Nat.le_add_right _ _
    have hrestore :
        freeTargetCount (L := L) (K := K) (c - {s, t}) +
            freeTargetCount (L := L) (K := K)
              ({s, t} : Config (AgentState L K)) =
          freeTargetCount (L := L) (K := K) c := by
      rw [← phaseZero_freeTargetCount_add]
      exact congrArg
        (fun d : Config (AgentState L K) =>
          freeTargetCount (L := L) (K := K) d)
        (Multiset.sub_add_cancel hle)
    have hstep :
        Protocol.stepOrSelf (NonuniformMajority L K) c s t =
          c - {s, t} +
            {(Transition L K s t).1, (Transition L K s t).2} := by
      unfold Protocol.stepOrSelf
      rw [if_pos happ]
      rfl
    rw [hstep, phaseZero_freeTargetCount_add, ← hrestore]
    exact Nat.add_le_add_left hpair _
  · rw [Protocol.stepOrSelf, if_neg happ]

theorem phaseZero_noAssigned_applyDraw
    (c : Cfg L K) (o : Draw L K)
    (hall : Phase0Window.allPhase0 (L := L) (K := K) c)
    (hfresh : NoAssignedMcrConfig (L := L) (K := K) c) :
    NoAssignedMcrConfig (L := L) (K := K) (applyDraw c o) := by
  cases o with
  | none => exact hfresh
  | some p =>
      exact NoAssignedMcrConfig_stepOrSelf
        c (occurrenceStatePair p).1 (occurrenceStatePair p).2
        hall hfresh

theorem phaseZero_freeTarget_applyDraw
    (c : Cfg L K) (o : Draw L K)
    (hall : Phase0Window.allPhase0 (L := L) (K := K) c)
    (hfresh : NoAssignedMcrConfig (L := L) (K := K) c) :
    freeTargetCount (L := L) (K := K) c ≤
      freeTargetCount (L := L) (K := K) (applyDraw c o) := by
  cases o with
  | none => exact le_rfl
  | some p =>
      exact phaseZero_freeTarget_stepOrSelf
        c (occurrenceStatePair p).1 (occurrenceStatePair p).2
        hall hfresh

/-- Freshness propagation through the complete Phase-0 prefix. -/
theorem phaseZero_noAssigned_trace_prefix
    {n : ℕ} (init : Cfg L K) (ω : Ω L K) (T : ℕ)
    (hinit : Phase0InitialFresh (L := L) (K := K) n init)
    (hall : ∀ t < T,
      Phase0Window.allPhase0 (L := L) (K := K) (trace init ω t)) :
    ∀ t ≤ T,
      NoAssignedMcrConfig (L := L) (K := K) (trace init ω t) := by
  intro t
  induction t with
  | zero =>
      intro _
      simpa only [trace_zero] using
        noAssignedMcrConfig_of_phase0InitialFresh
          (L := L) (K := K) hinit
  | succ t ih =>
      intro ht
      rw [trace_succ]
      exact phaseZero_noAssigned_applyDraw
        (trace init ω t) (ω (t + 1))
        (hall t (by omega)) (ih (by omega))

/-- PHASE02 section 2.1 on the actual pair-log trace. -/
theorem phaseZero_freeTarget_trace_step
    {n : ℕ} (init : Cfg L K) (ω : Ω L K) (T : ℕ)
    (hinit : Phase0InitialFresh (L := L) (K := K) n init)
    (hall : ∀ t < T,
      Phase0Window.allPhase0 (L := L) (K := K) (trace init ω t))
    (t : ℕ) (ht : t < T) :
    freeTargetCount (L := L) (K := K) (trace init ω t) ≤
      freeTargetCount (L := L) (K := K) (trace init ω (t + 1)) := by
  rw [trace_succ]
  exact phaseZero_freeTarget_applyDraw
    (trace init ω t) (ω (t + 1)) (hall t ht)
    (phaseZero_noAssigned_trace_prefix init ω T hinit hall t ht.le)

/-- The assigned-balance ledger also transports through the recorded draw. -/
theorem phaseZero_ledger_applyDraw
    (c : Cfg L K) (o : Draw L K)
    (hall : Phase0Window.allPhase0 (L := L) (K := K) c)
    (hfresh : NoAssignedMcrConfig (L := L) (K := K) c)
    (hledger : LedgerInv (L := L) (K := K) c) :
    LedgerInv (L := L) (K := K) (applyDraw c o) := by
  cases o with
  | none => exact hledger
  | some p =>
      exact LedgerInv_stepOrSelf
        c (occurrenceStatePair p).1 (occurrenceStatePair p).2
        hall hfresh hledger

theorem phaseZero_ledger_trace_prefix
    {n : ℕ} (init : Cfg L K) (ω : Ω L K) (T : ℕ)
    (hinit : Phase0InitialFresh (L := L) (K := K) n init)
    (hall : ∀ t < T,
      Phase0Window.allPhase0 (L := L) (K := K) (trace init ω t)) :
    ∀ t ≤ T, LedgerInv (L := L) (K := K) (trace init ω t) := by
  intro t
  induction t with
  | zero =>
      intro _
      simpa only [trace_zero] using
        (LedgerInv_init (L := L) (K := K) hinit.1)
  | succ t ih =>
      intro ht
      rw [trace_succ]
      have htT : t < T := by omega
      exact phaseZero_ledger_applyDraw
        (trace init ω t) (ω (t + 1))
        (hall t htT)
        (phaseZero_noAssigned_trace_prefix init ω T hinit hall t htT.le)
        (ih htT.le)

/-- The genuine first seed supplies the Phase-0 prefix needed above. -/
theorem phaseZero_allPhaseZero_before_seed
    (init : Cfg L K) (ω : Ω L K) (S : ℕ)
    (hseed : firstPhaseSeed init 1 S ω) :
    ∀ t < S, Phase0Window.allPhase0 (trace init ω t) := by
  intro t ht a ha
  apply Fin.ext
  exact Nat.lt_one_iff.mp (hseed.2 t ht a ha)

theorem phaseZero_freeTarget_until_seed
    {n : ℕ} (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init)
    (ω : InputLog n) (S : ℕ)
    (hseed : firstPhaseSeed init 1 S ω)
    (t : ℕ) (ht : t < S) :
    freeTargetCount (trace init ω t) ≤
      freeTargetCount (trace init ω (t + 1)) := by
  have hinit :=
    phase0InitialFresh_of_validInitial n init hinput.2.1 hinput.2.2
  exact phaseZero_freeTarget_trace_step init ω S hinit
    (phaseZero_allPhaseZero_before_seed init ω S hseed) t ht

/-- A fresh side agent contributes minus one to freeDiff; every other
agent's contribution is at least minus its side-membership indicator. -/
theorem phaseZero_freeDiff_add_side_nonneg
    (c : Config (AgentState L K)) :
    0 ≤ freeDiff (L := L) (K := K) c +
      (crCount (L := L) (K := K) c : ℤ) +
      (clockCount (L := L) (K := K) c : ℤ) +
      (reserveCount (L := L) (K := K) c : ℤ) := by
  unfold freeDiff Config.sumOf crCount clockCount reserveCount freeW
  induction c using Multiset.induction with
  | empty => simp
  | cons a c ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons,
        Multiset.countP_cons]
      cases hrole : a.role <;> cases hassigned : a.assigned <;>
        simp only [hrole, hassigned, reduceCtorEq, ne_eq,
          and_true, and_false, true_and, false_and,
          or_true, or_false, false_or, true_or,
          not_true_eq_false, not_false_eq_true,
          Bool.true_eq_false, Bool.false_eq_true,
          if_true, if_false, ite_true, ite_false,
          Nat.cast_add, Nat.cast_one, Nat.cast_zero] <;>
        omega

/-- The free Main-minus-side imbalance is bounded above by Main count. -/
theorem phaseZero_main_sub_freeDiff_nonneg
    (c : Config (AgentState L K)) :
    0 ≤ (mainCount (L := L) (K := K) c : ℤ) -
      freeDiff (L := L) (K := K) c := by
  unfold mainCount freeDiff Config.sumOf freeW
  induction c using Multiset.induction with
  | empty => simp
  | cons a c ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons,
        Multiset.countP_cons]
      cases hrole : a.role <;> cases hassigned : a.assigned <;>
        simp only [hrole, hassigned, reduceCtorEq, ne_eq,
          and_true, and_false, true_and, false_and,
          or_true, or_false, false_or, true_or,
          not_true_eq_false, not_false_eq_true,
          Bool.true_eq_false, Bool.false_eq_true,
          if_true, if_false, ite_true, ite_false,
          Nat.cast_add, Nat.cast_one, Nat.cast_zero] <;>
        omega

/-- PHASE02 equation (11), valid even while MCR agents remain. -/
theorem phaseZero_side_le_two_main
    (c : Config (AgentState L K))
    (hledger : LedgerInv (L := L) (K := K) c) :
    topCRMass (L := L) (K := K) c ≤
      2 * mainCount (L := L) (K := K) c := by
  have hfree := phaseZero_freeDiff_add_side_nonneg c
  unfold LedgerInv at hledger
  rw [topSplitXZ_eq_counts] at hledger
  have hside :
      (crCount (L := L) (K := K) c : ℤ) +
          (clockCount (L := L) (K := K) c : ℤ) +
          (reserveCount (L := L) (K := K) c : ℤ) ≤
        2 * (mainCount (L := L) (K := K) c : ℤ) := by
    omega
  unfold topCRMass
  exact_mod_cast hside

theorem phaseZero_main_le_two_side
    (c : Config (AgentState L K))
    (hledger : LedgerInv (L := L) (K := K) c) :
    mainCount (L := L) (K := K) c ≤
      2 * topCRMass (L := L) (K := K) c := by
  have hfree := phaseZero_main_sub_freeDiff_nonneg c
  unfold LedgerInv at hledger
  rw [topSplitXZ_eq_counts] at hledger
  have hmain :
      (mainCount (L := L) (K := K) c : ℤ) ≤
        2 * ((crCount (L := L) (K := K) c : ℤ) +
          (clockCount (L := L) (K := K) c : ℤ) +
          (reserveCount (L := L) (K := K) c : ℤ)) := by
    omega
  unfold topCRMass
  exact_mod_cast hmain

theorem phaseZero_clock_third_of_ledger_balance
    (c : Config (AgentState L K))
    (hledger : LedgerInv (L := L) (K := K) c)
    (hbalance : ClockReserveBalanced (L := L) (K := K) c) :
    3 * clockCount (L := L) (K := K) c ≤ c.card := by
  have hside := phaseZero_side_le_two_main c hledger
  have hconservation := roleCount_conservation (L := L) (K := K) c
  unfold topCRMass at hside
  unfold ClockReserveBalanced at hbalance
  omega

private theorem phaseZero_clockCount_add
    (c d : Config (AgentState L K)) :
    clockCount (L := L) (K := K) (c + d) =
      clockCount (L := L) (K := K) c +
        clockCount (L := L) (K := K) d := by
  simp only [clockCount, Multiset.countP_add]

private theorem phaseZero_reserveCount_add
    (c d : Config (AgentState L K)) :
    reserveCount (L := L) (K := K) (c + d) =
      reserveCount (L := L) (K := K) c +
        reserveCount (L := L) (K := K) d := by
  simp only [reserveCount, Multiset.countP_add]

theorem phaseZero_clockReserve_initial
    {n : ℕ} {c : Config (AgentState L K)}
    (hinit : Phase0Initial (L := L) (K := K) n c) :
    ClockReserveBalanced (L := L) (K := K) c := by
  have hclock : clockCount (L := L) (K := K) c = 0 := by
    unfold clockCount
    rw [Multiset.countP_eq_zero]
    intro a ha
    rw [(hinit.2 a ha).2]
    simp
  have hreserve : reserveCount (L := L) (K := K) c = 0 := by
    unfold reserveCount
    rw [Multiset.countP_eq_zero]
    intro a ha
    rw [(hinit.2 a ha).2]
    simp
  unfold ClockReserveBalanced
  rw [hclock, hreserve]

/-- Clock/Reserve balance through the actual dispatcher. -/
theorem phaseZero_clockReserve_stepOrSelf
    (c : Config (AgentState L K)) (s t : AgentState L K)
    (hall : Phase0Window.allPhase0 (L := L) (K := K) c)
    (hbalance : ClockReserveBalanced (L := L) (K := K) c) :
    ClockReserveBalanced (L := L) (K := K)
      (Protocol.stepOrSelf (NonuniformMajority L K) c s t) := by
  by_cases happ : Protocol.Applicable c s t
  · have hle : ({s, t} : Config (AgentState L K)) ≤ c := happ
    have hsmem : s ∈ c := Multiset.mem_of_le hle (by simp)
    have htmem : t ∈ c := Multiset.mem_of_le hle (by simp)
    have hsphase : s.phase.val = 0 :=
      congrArg Fin.val (hall s hsmem)
    have htphase : t.phase.val = 0 :=
      congrArg Fin.val (hall t htmem)
    have hroles :=
      Transition_roles_eq_phase0_of_both_phase0
        (L := L) (K := K) s t hsphase htphase
    have hpair :
        clockCount (L := L) (K := K)
            ({(Transition L K s t).1, (Transition L K s t).2} :
              Config (AgentState L K)) +
            reserveCount (L := L) (K := K)
              ({s, t} : Config (AgentState L K)) =
          reserveCount (L := L) (K := K)
            ({(Transition L K s t).1, (Transition L K s t).2} :
              Config (AgentState L K)) +
            clockCount (L := L) (K := K)
              ({s, t} : Config (AgentState L K)) := by
      simpa only [clockCount_pair', reserveCount_pair',
        hroles.1, hroles.2] using
        (Phase0Transition_clock_reserve_balance_pair
          (L := L) (K := K) s t)
    have hclockRestore :
        clockCount (L := L) (K := K) (c - {s, t}) +
            clockCount (L := L) (K := K)
              ({s, t} : Config (AgentState L K)) =
          clockCount (L := L) (K := K) c := by
      rw [← phaseZero_clockCount_add]
      exact congrArg
        (fun d : Config (AgentState L K) =>
          clockCount (L := L) (K := K) d)
        (Multiset.sub_add_cancel hle)
    have hreserveRestore :
        reserveCount (L := L) (K := K) (c - {s, t}) +
            reserveCount (L := L) (K := K)
              ({s, t} : Config (AgentState L K)) =
          reserveCount (L := L) (K := K) c := by
      rw [← phaseZero_reserveCount_add]
      exact congrArg
        (fun d : Config (AgentState L K) =>
          reserveCount (L := L) (K := K) d)
        (Multiset.sub_add_cancel hle)
    have hstep :
        Protocol.stepOrSelf (NonuniformMajority L K) c s t =
          c - {s, t} +
            {(Transition L K s t).1, (Transition L K s t).2} := by
      unfold Protocol.stepOrSelf
      rw [if_pos happ]
      rfl
    unfold ClockReserveBalanced at hbalance ⊢
    rw [hstep, phaseZero_clockCount_add, phaseZero_reserveCount_add]
    omega
  · rw [Protocol.stepOrSelf, if_neg happ]
    exact hbalance

theorem phaseZero_clockReserve_applyDraw
    (c : Cfg L K) (o : Draw L K)
    (hall : Phase0Window.allPhase0 (L := L) (K := K) c)
    (hbalance : ClockReserveBalanced (L := L) (K := K) c) :
    ClockReserveBalanced (L := L) (K := K) (applyDraw c o) := by
  cases o with
  | none => exact hbalance
  | some p =>
      exact phaseZero_clockReserve_stepOrSelf
        c (occurrenceStatePair p).1 (occurrenceStatePair p).2
        hall hbalance

theorem phaseZero_clockReserve_trace_prefix
    {n : ℕ} (init : Cfg L K) (ω : Ω L K) (T : ℕ)
    (hinit : Phase0InitialFresh (L := L) (K := K) n init)
    (hall : ∀ t < T,
      Phase0Window.allPhase0 (L := L) (K := K) (trace init ω t)) :
    ∀ t ≤ T,
      ClockReserveBalanced (L := L) (K := K) (trace init ω t) := by
  intro t
  induction t with
  | zero =>
      intro _
      simpa only [trace_zero] using
        (phaseZero_clockReserve_initial (L := L) (K := K) hinit.1)
  | succ t ih =>
      intro ht
      rw [trace_succ]
      exact phaseZero_clockReserve_applyDraw
        (trace init ω t) (ω (t + 1))
        (hall t (by omega)) (ih (by omega))

/-- PHASE02 equation (12) on the actual pair-log trace, with no
role-success assumption or future conditioning. -/
theorem phaseZero_clock_third_trace_prefix
    {n : ℕ} (init : Cfg L K) (ω : Ω L K) (T : ℕ)
    (hinit : Phase0InitialFresh (L := L) (K := K) n init)
    (hall : ∀ t < T,
      Phase0Window.allPhase0 (L := L) (K := K) (trace init ω t)) :
    ∀ t ≤ T,
      3 * clockCount (L := L) (K := K) (trace init ω t) ≤ n := by
  intro t ht
  have hledger := phaseZero_ledger_trace_prefix init ω T hinit hall t ht
  have hbalance :=
    phaseZero_clockReserve_trace_prefix init ω T hinit hall t ht
  have hcap :=
    phaseZero_clock_third_of_ledger_balance
      (trace init ω t) hledger hbalance
  have hcard : (trace init ω t).card = n := by
    calc
      (trace init ω t).card = (trace init ω 0).card :=
        Protocol.reachable_card_eq
          (trace_reachable init ω (s := 0) (t := t) (Nat.zero_le t))
      _ = n := by simpa only [trace_zero] using hinit.1.1
  simpa only [hcard] using hcap

theorem phaseZero_clock_third_until_seed
    {n : ℕ} (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init)
    (ω : InputLog n) (S : ℕ)
    (hseed : firstPhaseSeed init 1 S ω) :
    ∀ t ≤ S, 3 * clockCount (trace init ω t) ≤ n := by
  have hinit :=
    phase0InitialFresh_of_validInitial n init hinput.2.1 hinput.2.2
  exact phaseZero_clock_third_trace_prefix init ω S hinit
    (phaseZero_allPhaseZero_before_seed init ω S hseed)

end RoleLedgers

/-! ## Conditional next-draw estimates on the pair-log law -/

section PairLogEstimates

open PairLog

attribute [local instance] Classical.propDecidable

theorem pair_log_conditional_next_mass
    {L K : ℕ} (init : Cfg L K) (t : ℕ)
    (A : ((i : Finset.Iic t) → Draw L K) → Draw L K → Prop)
    (q : ((i : Finset.Iic t) → Draw L K) → ℝ≥0∞)
    (hmass : ∀ p,
      (drawLaw (prefixCfg init t p)).toMeasure {d | A p d} = q p) :
    (law init)[fun ω =>
      if A (frestrictLe t ω) (ω (t + 1)) then (1 : ℝ) else 0
      | pairLogFiltration L K t] =ᵐ[law init]
      (fun ω => (q (frestrictLe t ω)).toReal) := by
  classical
  let κ := fun s => pairKernel init s
  let f : Ω L K → ℝ := fun ω =>
    if A (frestrictLe t ω) (ω (t + 1)) then 1 else 0
  have hA :
      MeasurableSet {z : ((i : Finset.Iic t) → Draw L K) × Draw L K |
        A z.1 z.2} :=
    (Set.to_countable _).measurableSet
  have hpair :
      Measurable (fun ω : Ω L K =>
        (frestrictLe (π := fun _ : ℕ => Draw L K) t ω, ω (t + 1))) :=
    (measurable_frestrictLe (X := fun _ : ℕ => Draw L K) t).prodMk
      (measurable_pi_apply (t + 1))
  have hEvent :
      MeasurableSet {ω : Ω L K | A (frestrictLe t ω) (ω (t + 1))} :=
    hA.preimage hpair
  have hfm : Measurable f :=
    Measurable.ite hEvent measurable_const measurable_const
  have hfi : Integrable f (law init) :=
    (integrable_const (1 : ℝ)).mono' hfm.aestronglyMeasurable
      (ae_of_all _ fun ω => by
        dsimp [f]
        split_ifs <;> norm_num)
  have hlaw : law init =
      Kernel.traj (X := fun _ => Draw L K) (fun s => pairKernel init s) 0 (fun _ => none) :=
    (Kernel.traj_apply _ _).symm
  have hce :
      (law init)[f | pairLogFiltration L K t] =ᵐ[law init]
        (fun ω => ∫ y, f y ∂Kernel.traj (X := fun _ => Draw L K) κ t (frestrictLe t ω)) := by
    rw [hlaw] at hfi ⊢
    rw [show (pairLogFiltration L K t : MeasurableSpace (Ω L K)) =
      Filtration.piLE (X := fun _ : ℕ => Draw L K) t from rfl]
    exact Kernel.condExp_traj (X := fun _ => Draw L K)
      (κ := fun s => pairKernel init s) (a := 0) (b := t)
      (x₀ := fun _ => none) (Nat.zero_le t) hfi
  have hlocal (p : (i : Finset.Iic t) → Draw L K) :
      (∫ d, (if A p d then (1 : ℝ) else 0) ∂pairKernel init t p) =
        (q p).toReal := by
    have hp : MeasurableSet {d : Draw L K | A p d} :=
      (Set.to_countable _).measurableSet
    calc
      (∫ d, (if A p d then (1 : ℝ) else 0) ∂pairKernel init t p) =
          (pairKernel init t p).real {d | A p d} := by
        simpa only [Set.indicator, Pi.one_apply, Set.mem_setOf_eq] using
          (integral_indicator_one (μ := pairKernel init t p) hp)
      _ = (q p).toReal := by
        change ((drawLaw (prefixCfg init t p)).toMeasure {d | A p d}).toReal = _
        rw [hmass p]
  have htraj (p : (i : Finset.Iic t) → Draw L K) :
      (∫ y, f y ∂Kernel.traj (X := fun _ => Draw L K) κ t p) = (q p).toReal := by
    have hfreeze :
        (fun y : Ω L K =>
          f (Function.updateFinset y (Finset.Iic t) p)) =
        (fun y => if A p (y (t + 1)) then (1 : ℝ) else 0) := by
      funext y
      dsimp [f]
      rw [frestrictLe_updateFinset]
      simp [Function.updateFinset, Finset.mem_Iic, Nat.not_succ_le_self]
    have hmap :
        Measure.map (fun y : Ω L K => y (t + 1)) (Kernel.traj (X := fun _ => Draw L K) κ t p) =
          pairKernel init t p := by
      change (Kernel.traj (X := fun _ => Draw L K) κ t p).map
        (fun y : Ω L K => y (t + 1)) = κ t p
      rw [← Kernel.map_apply _ (measurable_pi_apply (t + 1)),
        Kernel.map_traj_succ_self]
    have hnext :
        Measurable (fun d : Draw L K =>
          if A p d then (1 : ℝ) else 0) :=
      Measurable.ite (Set.to_countable _).measurableSet
        measurable_const measurable_const
    calc
      (∫ y, f y ∂Kernel.traj (X := fun _ => Draw L K) κ t p) =
          ∫ y, f (Function.updateFinset y (Finset.Iic t) p)
            ∂Kernel.traj (X := fun _ => Draw L K) κ t p :=
        Kernel.integral_traj (X := fun _ => Draw L K) (κ := κ) p hfm.aestronglyMeasurable
      _ = ∫ y : Ω L K, (if A p (y (t + 1)) then (1 : ℝ) else 0)
          ∂Kernel.traj (X := fun _ => Draw L K) κ t p := by rw [hfreeze]
      _ = ∫ d, (if A p d then (1 : ℝ) else 0)
          ∂pairKernel init t p := by
        rw [← hmap]
        exact (integral_map (μ := Kernel.traj (X := fun _ => Draw L K) κ t p)
          (f := fun d : Draw L K => if A p d then (1 : ℝ) else 0)
          (measurable_pi_apply (t + 1)).aemeasurable
          hnext.aestronglyMeasurable).symm
      _ = (q p).toReal := hlocal p
  filter_upwards [hce] with ω hω
  exact hω.trans (htraj (frestrictLe t ω))

/-- Exact next-draw mass for both orientations of encounters between a
persistent label and a finite partner set excluding that label. -/
theorem selected_label_partner_mass {L K n : ℕ}
    (f : Fin n → AgentState L K) (hn : 2 ≤ n)
    (i : Fin n) (J : Finset (Fin n)) (hi : i ∉ J) :
    (drawLaw (PairLog.labelCfg f)).toMeasure
        {d | ∃ j ∈ J,
          PairLog.selectLabels f d = some (i, j) ∨
          PairLog.selectLabels f d = some (j, i)} =
      ((2 * J.card : ℕ) : ℝ≥0∞) *
        ((n * (n - 1) : ℕ) : ℝ≥0∞)⁻¹ := by
  classical
  let μ := (drawLaw (PairLog.labelCfg f)).toMeasure
  let r : ℝ≥0∞ := ((n * (n - 1) : ℕ) : ℝ≥0∞)⁻¹
  let A (j : Fin n) : Set (Draw L K) :=
    {d | PairLog.selectLabels f d = some (i, j)}
  let B (j : Fin n) : Set (Draw L K) :=
    {d | PairLog.selectLabels f d = some (j, i)}
  have hAm (j : Fin n) : MeasurableSet (A j) :=
    (Set.to_countable _).measurableSet
  have hBm (j : Fin n) : MeasurableSet (B j) :=
    (Set.to_countable _).measurableSet
  have hleft (j : Fin n) (hj : j ∈ J) : μ (A j) = r := by
    have hij : i ≠ j := by
      intro h
      apply hi
      simpa only [h] using hj
    calc
      μ (A j) =
          ((drawLaw (PairLog.labelCfg f)).map
            (PairLog.selectLabels f)) (some (i, j)) :=
        PairLog.drawLaw_event_eq_map
          (PairLog.labelCfg f) (PairLog.selectLabels f) (some (i, j))
      _ = r := PairLog.selectLabels_drawLaw f hn i j hij
  have hright (j : Fin n) (hj : j ∈ J) : μ (B j) = r := by
    have hji : j ≠ i := by
      intro h
      apply hi
      simpa only [h] using hj
    calc
      μ (B j) =
          ((drawLaw (PairLog.labelCfg f)).map
            (PairLog.selectLabels f)) (some (j, i)) :=
        PairLog.drawLaw_event_eq_map
          (PairLog.labelCfg f) (PairLog.selectLabels f) (some (j, i))
      _ = r := PairLog.selectLabels_drawLaw f hn j i hji
  have hdA : Set.PairwiseDisjoint (↑J : Set (Fin n)) A := by
    intro j _ k _ hjk
    apply Set.disjoint_left.mpr
    intro d hdj hdk
    dsimp only [A, Set.mem_setOf_eq] at hdj hdk
    apply hjk
    exact congrArg Prod.snd (Option.some.inj (hdj.symm.trans hdk))
  have hdB : Set.PairwiseDisjoint (↑J : Set (Fin n)) B := by
    intro j _ k _ hjk
    apply Set.disjoint_left.mpr
    intro d hdj hdk
    dsimp only [B, Set.mem_setOf_eq] at hdj hdk
    apply hjk
    exact congrArg Prod.fst (Option.some.inj (hdj.symm.trans hdk))
  have hleftSum :
      (∑ j ∈ J, μ (A j)) = (J.card : ℝ≥0∞) * r := by
    calc
      (∑ j ∈ J, μ (A j)) = ∑ _j ∈ J, r :=
        Finset.sum_congr rfl hleft
      _ = (J.card : ℝ≥0∞) * r := by
        simp only [Finset.sum_const, nsmul_eq_mul]
  have hrightSum :
      (∑ j ∈ J, μ (B j)) = (J.card : ℝ≥0∞) * r := by
    calc
      (∑ j ∈ J, μ (B j)) = ∑ _j ∈ J, r :=
        Finset.sum_congr rfl hright
      _ = (J.card : ℝ≥0∞) * r := by
        simp only [Finset.sum_const, nsmul_eq_mul]
  have hAU :
      μ (⋃ j ∈ J, A j) = (J.card : ℝ≥0∞) * r :=
    (measure_biUnion_finset (μ := μ) hdA
      (fun j _ => hAm j)).trans hleftSum
  have hBU :
      μ (⋃ j ∈ J, B j) = (J.card : ℝ≥0∞) * r :=
    (measure_biUnion_finset (μ := μ) hdB
      (fun j _ => hBm j)).trans hrightSum
  have hAB : Disjoint (⋃ j ∈ J, A j) (⋃ j ∈ J, B j) := by
    apply Set.disjoint_left.mpr
    intro d hdA hdB
    obtain ⟨j, hdA⟩ := Set.mem_iUnion.mp hdA
    obtain ⟨_, hdA⟩ := Set.mem_iUnion.mp hdA
    obtain ⟨k, hdB⟩ := Set.mem_iUnion.mp hdB
    obtain ⟨hk, hdB⟩ := Set.mem_iUnion.mp hdB
    dsimp only [A, Set.mem_setOf_eq] at hdA
    dsimp only [B, Set.mem_setOf_eq] at hdB
    have hki : k = i :=
      (congrArg Prod.fst
        (Option.some.inj (hdA.symm.trans hdB))).symm
    apply hi
    simpa only [hki] using hk
  have hEvent :
      {d : Draw L K | ∃ j ∈ J,
        PairLog.selectLabels f d = some (i, j) ∨
        PairLog.selectLabels f d = some (j, i)} =
      (⋃ j ∈ J, A j) ∪ (⋃ j ∈ J, B j) := by
    ext d
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_iUnion, A, B]
    constructor
    · rintro ⟨j, hj, h | h⟩
      · exact Or.inl ⟨j, hj, h⟩
      · exact Or.inr ⟨j, hj, h⟩
    · rintro (⟨j, hj, h⟩ | ⟨j, hj, h⟩)
      · exact ⟨j, hj, Or.inl h⟩
      · exact ⟨j, hj, Or.inr h⟩
  calc
    (drawLaw (PairLog.labelCfg f)).toMeasure
        {d | ∃ j ∈ J,
          PairLog.selectLabels f d = some (i, j) ∨
          PairLog.selectLabels f d = some (j, i)} =
        μ ((⋃ j ∈ J, A j) ∪ (⋃ j ∈ J, B j)) :=
      congrArg μ hEvent
    _ = μ (⋃ j ∈ J, A j) + μ (⋃ j ∈ J, B j) :=
      measure_union hAB ((Set.to_countable _).measurableSet)
    _ = (J.card : ℝ≥0∞) * r + (J.card : ℝ≥0∞) * r := by
      rw [hAU, hBU]
    _ = ((2 * J.card : ℕ) : ℝ≥0∞) *
        ((n * (n - 1) : ℕ) : ℝ≥0∞)⁻¹ := by
      change
        (J.card : ℝ≥0∞) * r + (J.card : ℝ≥0∞) * r =
          ((2 * J.card : ℕ) : ℝ≥0∞) * r
      simp only [Nat.cast_mul, Nat.cast_ofNat]
      ring

/-- A fixed persistent label participates with conditional probability
exactly 2/n, given the entire recorded pair-log past. -/
theorem selected_label_participation_conditional_probability
    {L K : ℕ} (init : Cfg L K) (hc : 2 ≤ init.card)
    (i : Fin init.card) (t : ℕ) :
    (law init)[fun ω =>
      if ∃ j : Fin init.card, j ≠ i ∧
          (PairLog.drawLabels init ω (t + 1) = some (i, j) ∨
           PairLog.drawLabels init ω (t + 1) = some (j, i))
      then (1 : ℝ) else 0
      | PairLog.pairLogFiltration L K t] =ᵐ[law init]
        (fun _ => 2 / (init.card : ℝ)) := by
  classical
  let J : Finset (Fin init.card) := Finset.univ.erase i
  let A :
      ((k : Finset.Iic t) → Draw L K) → Draw L K → Prop :=
    fun p d =>
      ∃ j : Fin init.card, j ≠ i ∧
        (PairLog.selectLabels (PairLog.prefixLabels init t p) d =
            some (i, j) ∨
         PairLog.selectLabels (PairLog.prefixLabels init t p) d =
            some (j, i))
  let q : ℝ≥0∞ :=
    ((2 * (init.card - 1) : ℕ) : ℝ≥0∞) *
      ((init.card * (init.card - 1) : ℕ) : ℝ≥0∞)⁻¹
  have hiJ : i ∉ J := by simp [J]
  have hJcard : J.card = init.card - 1 := by simp [J]
  have hmass (p : (k : Finset.Iic t) → Draw L K) :
      (drawLaw (prefixCfg init t p)).toMeasure {d | A p d} = q := by
    have hm := selected_label_partner_mass
      (PairLog.prefixLabels init t p) hc i J hiJ
    rw [hJcard, PairLog.prefixLabels_config init t p] at hm
    simpa only [A, q, J, Finset.mem_erase,
      Finset.mem_univ, and_true] using hm
  have h := PairLog.pairLog_condExp_indicator_of_next_mass
    init t A q hmass
  have hq : q.toReal = 2 / (init.card : ℝ) := by
    have hnpos : 0 < (init.card : ℝ) := by
      exact_mod_cast (show 0 < init.card by omega)
    have hnlarge : (2 : ℝ) ≤ init.card := by exact_mod_cast hc
    have hnsub : (init.card : ℝ) - 1 ≠ 0 := by
      linarith only [hnlarge]
    dsimp only [q]
    rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
      ENNReal.toReal_natCast]
    push_cast [Nat.cast_sub (show 1 ≤ init.card by omega)]
    first
      | (field_simp [hnpos.ne', hnsub]; ring)
      | field_simp [hnpos.ne', hnsub]
  rw [hq] at h
  refine
    (condExp_congr_ae (μ := law init)
      (m := PairLog.pairLogFiltration L K t) ?_).trans h
  apply Filter.Eventually.of_forall
  intro ω
  have hEvent :
      (∃ j : Fin init.card, j ≠ i ∧
        (PairLog.drawLabels init ω (t + 1) = some (i, j) ∨
         PairLog.drawLabels init ω (t + 1) = some (j, i))) ↔
      A (frestrictLe t ω) (ω (t + 1)) := by
    rfl
  by_cases hA : A (frestrictLe t ω) (ω (t + 1))
  · simp only [if_pos (hEvent.mpr hA), if_pos hA]
  · have hnot :
        ¬ (∃ j : Fin init.card, j ≠ i ∧
          (PairLog.drawLabels init ω (t + 1) = some (i, j) ∨
           PairLog.drawLabels init ω (t + 1) = some (j, i))) :=
      fun hj => hA (hEvent.mp hj)
    simp only [if_neg hnot, if_neg hA]

/-- The actual one-step CR-death rate from section 2.5, pulled back to
the pair-log past. The rate is zero outside the all-phase-zero region.
No assertion is made here about the future CR-drain duration. -/
theorem phase_zero_cr_conditional_decrease
    {L K : ℕ} (init : Cfg L K) (hc : 2 ≤ init.card) (t : ℕ) :
    (fun ω =>
      if Phase0Window.allPhase0 (trace init ω t) then
        (((RoleSplitConcentration.crCount (trace init ω t) *
          (RoleSplitConcentration.crCount (trace init ω t) - 1) : ℕ) : ℝ) /
          ((init.card : ℝ) * ((init.card : ℝ) - 1)))
      else 0) ≤ᵐ[law init]
      (law init)[fun ω =>
        if RoleSplitConcentration.crCount (trace init ω (t + 1)) <
          RoleSplitConcentration.crCount (trace init ω t)
        then (1 : ℝ) else 0 | pairLogFiltration L K t] := by
  classical
  let A : ((i : Finset.Iic t) → Draw L K) → Draw L K → Prop :=
    fun p d =>
      RoleSplitConcentration.crCount (applyDraw (prefixCfg init t p) d) <
        RoleSplitConcentration.crCount (prefixCfg init t p)
  let mass : ((i : Finset.Iic t) → Draw L K) → ℝ≥0∞ :=
    fun p => (drawLaw (prefixCfg init t p)).toMeasure {d | A p d}
  let rate : ((i : Finset.Iic t) → Draw L K) → ℝ := fun p =>
    if Phase0Window.allPhase0 (prefixCfg init t p) then
      (((RoleSplitConcentration.crCount (prefixCfg init t p) *
          (RoleSplitConcentration.crCount (prefixCfg init t p) - 1) : ℕ) : ℝ) /
        ((init.card : ℝ) * ((init.card : ℝ) - 1)))
    else 0
  have hden : (0 : ℝ) < (init.card : ℝ) * ((init.card : ℝ) - 1) := by
    have hcR : (2 : ℝ) ≤ init.card := by exact_mod_cast hc
    nlinarith only [hcR]
  have hnonneg : ∀ p, 0 ≤ rate p := by
    intro p
    dsimp only [rate]
    split_ifs
    · exact div_nonneg (Nat.cast_nonneg _) hden.le
    · exact le_rfl
  have hbound : ∀ p, ENNReal.ofReal (rate p) ≤ mass p := by
    intro p
    by_cases hp : Phase0Window.allPhase0 (prefixCfg init t p)
    · have hcard : (prefixCfg init t p).card = init.card := by
        rw [← PairLog.prefixLabels_config init t p]
        exact PairLog.labelCfg_card _
      have hm : Measurable (applyDraw (prefixCfg init t p)) := by
        intro B hB
        exact (Set.to_countable _).measurableSet
      have hB : MeasurableSet
          {c : Cfg L K |
            RoleSplitConcentration.crCount c <
              RoleSplitConcentration.crCount (prefixCfg init t p)} :=
        (Set.to_countable _).measurableSet
      have hproject :
          mass p =
            (NonuniformMajority L K).transitionKernel
              (prefixCfg init t p)
              {c | RoleSplitConcentration.crCount c <
                RoleSplitConcentration.crCount (prefixCfg init t p)} := by
        rw [← PairLog.drawLaw_map_toMeasure (prefixCfg init t p),
          Measure.map_apply hm hB]
        rfl
      have hrate :=
        RoleSplitConcentration.phase0_crCount_decrease_prob
          (prefixCfg init t p) init.card hcard hc
          (fun a ha _ => congrArg Fin.val (hp a ha))
      rw [hproject]
      simpa only [rate, if_pos hp] using hrate
    · simp only [rate, if_neg hp, ENNReal.ofReal_zero]
      exact bot_le
  have hce :=
    pair_log_conditional_next_mass init t A mass (fun _ => rfl)
  have hfun :
      (fun ω : Ω L K =>
        @ite ℝ (A (frestrictLe t ω) (ω (t + 1))) (Classical.propDecidable _) 1 0) =
      (fun ω : Ω L K =>
        if RoleSplitConcentration.crCount (trace init ω (t + 1)) <
          RoleSplitConcentration.crCount (trace init ω t)
        then (1 : ℝ) else 0) := by
    funext ω
    have hevent :
        A (frestrictLe t ω) (ω (t + 1)) ↔
          RoleSplitConcentration.crCount (trace init ω (t + 1)) <
            RoleSplitConcentration.crCount (trace init ω t) := by
      rfl
    by_cases h : A (frestrictLe t ω) (ω (t + 1))
    · rw [if_pos h, if_pos (hevent.mp h)]
    · rw [if_neg h, if_neg (fun h' => h (hevent.mpr h'))]
  have hce' :
      (law init)[fun ω =>
        if RoleSplitConcentration.crCount (trace init ω (t + 1)) <
          RoleSplitConcentration.crCount (trace init ω t)
        then (1 : ℝ) else 0 | pairLogFiltration L K t] =ᵐ[law init]
        (fun ω => (mass (frestrictLe t ω)).toReal) := by
    rw [← hfun]
    exact hce
  filter_upwards [hce'] with ω hω
  rw [hω]
  have h :=
    ENNReal.toReal_mono
      (show mass (frestrictLe t ω) ≠ ⊤ from measure_ne_top _ _)
      (hbound (frestrictLe t ω))
  simpa only [ENNReal.toReal_ofReal (hnonneg (frestrictLe t ω)),
    rate, trace] using h

end PairLogEstimates

end Ripple.PopulationProtocol.ExactMajority.PhaseZeroEntry
