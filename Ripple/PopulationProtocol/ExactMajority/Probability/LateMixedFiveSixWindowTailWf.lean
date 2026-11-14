-- Ripple/PopulationProtocol/ExactMajority/Probability/LateMixedFiveSixWindowTailWf.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.LateMixedFiveSixWindowFirstExitWf
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseTwoThresholds
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseZeroTwoCalibration
import Ripple.PopulationProtocol.ExactMajority.Probability.AdvanceResetPairBound

/-!
# N18 row four: reachable-Wf original-law mixed Phase-5/6 window tail

This is the mixed-window tail with the false global deterministic bridge removed.
The timer first-exit argument now runs inside the reachable restricted window
from `LateMixedFiveSixWindowFirstExitWf`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder Set
open scoped ENNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.LateMixedFiveSixWindowTailWf

open TimeTheorem PairLog
open PhaseOneDrain PhaseOneDrainStopping
open LateSamplingCompletion LateMixedFuel LateF6OriginalLaw
open LateMixedFiveSixWindow
open LateMixedFiveSixWindowFirstExitWf
open PhaseTwoThresholds
open AdvanceNoOvershoot

variable {L K m n : ℕ}

/-- Exact state information consumed by the wide Phase-6 timer tail at the
genuine first Phase-6 seed.  The fields are unchanged from the earlier version. -/
structure PhaseSixTimerSeed (n : ℕ) (c : InputCfg n) : Prop where
  population : c.card = n
  no_overshoot :
    NoOvershoot
      (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256) 5 c
  potential :
    advanceClockPotential
        (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256) 5 1 c ≤
      (n : ℝ≥0∞) * ENNReal.ofReal
        (Real.exp
          (-(50 * (PhaseThreeModel.Numeric.hourIndex n + 1) : ℕ)))

/-- Completion-to-first-6 receipt.  The fields are unchanged from the earlier version. -/
structure PhaseSixSeedReceipt
    (init : InputCfg n) (ω : InputLog n) (u s : ℕ) : Prop where
  time : firstSixStart init ω = (s : WithTop ℕ)
  order : u ≤ s
  timer_seed : PhaseSixTimerSeed n (trace init ω s)

/-- Phase-5 timer producer interface.  The fields are unchanged from the earlier version,
so its waiting consumer only needs to switch the imported module. -/
structure PhaseSixSeedProducer
    (init : InputCfg n) (seedFailure : Set (InputLog n)) : Prop where
  tail :
    law init seedFailure ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 5)
  produce : ∀ (ω : InputLog n) (u : ℕ),
    completionTime init n ω = (u : WithTop ℕ) →
    ω ∉ seedFailure →
    ∃ s, PhaseSixSeedReceipt init ω u s

/-- The first-six receipt exposes the actual threshold-6 seed. -/
theorem PhaseSixSeedReceipt.trigger
    {init : InputCfg n} {ω : InputLog n} {u s : ℕ}
    (h : PhaseSixSeedReceipt init ω u s) :
    StageEventSpec.someGE (n := n) 6 (trace init ω s) := by
  have hfirst :=
    (exitTime_eq_iff_firstHit init
      (StageEventSpec.someGE (n := n) 6) ω s).mp
      (by simpa only [firstSixStart] using h.time)
  exact hfirst.1

/-- Endpoint timer failure, restricted to the lower-phase invariant needed by
the genuine first-exit bridge.  This restriction has no extra probabilistic
cost on paths produced after sampling completion. -/
def phaseSixTimerFailure (init : InputCfg n) : Set (InputLog n) :=
  {ω | ∃ s : ℕ,
    firstSixStart init ω = (s : WithTop ℕ) ∧
      PhaseSixTimerSeed n (trace init ω s) ∧
      (∀ a ∈ trace init ω s, 2 ≤ a.phase.val) ∧
      ¬ NoOvershoot
        (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256) 5
        (trace init ω (s + StageEventSpec.activationHorizon n))}

@[simp] theorem mem_phaseSixTimerFailure_iff
    (init : InputCfg n) (ω : InputLog n) :
    ω ∈ phaseSixTimerFailure init ↔
      ∃ s : ℕ,
        firstSixStart init ω = (s : WithTop ℕ) ∧
        PhaseSixTimerSeed n (trace init ω s) ∧
        (∀ a ∈ trace init ω s, 2 ≤ a.phase.val) ∧
        ¬ NoOvershoot
          (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256) 5
          (trace init ω (s + StageEventSpec.activationHorizon n)) :=
  Iff.rfl

/-- Threshold-6 epidemic failure at the same genuine first-six stopping time. -/
def phaseSixSpreadFailure (init : InputCfg n) : Set (InputLog n) :=
  thresholdFailureAt init n 6 (StageEventSpec.activationHorizon n)
    (firstSixStart init)

/-- The restricted timer failure is measurable. -/
theorem phaseSixTimerFailure_measurable (init : InputCfg n) :
    MeasurableSet (phaseSixTimerFailure init) := by
  have heq : phaseSixTimerFailure init =
      ⋃ s : ℕ,
        {ω | firstSixStart init ω = (s : WithTop ℕ)} ∩
          ({ω | PhaseSixTimerSeed n (trace init ω s)} ∩
            ({ω | ∀ a ∈ trace init ω s, 2 ≤ a.phase.val} ∩
              {ω | ¬ NoOvershoot
                (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256) 5
                (trace init ω
                  (s + StageEventSpec.activationHorizon n))})) := by
    ext ω
    simp only [phaseSixTimerFailure, Set.mem_setOf_eq,
      Set.mem_iUnion, Set.mem_inter_iff]
  rw [heq]
  apply MeasurableSet.iUnion
  intro s
  have htime : MeasurableSet
      {ω | firstSixStart init ω = (s : WithTop ℕ)} :=
    (pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256).le s _
      ((firstSixStart_past init) s)
  have hseed : MeasurableSet
      {ω | PhaseSixTimerSeed n (trace init ω s)} :=
    (show MeasurableSet {c : InputCfg n | PhaseSixTimerSeed n c} from
      (Set.to_countable _).measurableSet).preimage
        ((measurable_pi_apply s).comp (measurable_trace init))
  have hlower : MeasurableSet
      {ω | ∀ a ∈ trace init ω s, 2 ≤ a.phase.val} :=
    (show MeasurableSet {c : InputCfg n |
        ∀ a ∈ c, 2 ≤ a.phase.val} from
      (Set.to_countable _).measurableSet).preimage
        ((measurable_pi_apply s).comp (measurable_trace init))
  have hbad : MeasurableSet
      {ω | ¬ NoOvershoot
        (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256) 5
        (trace init ω (s + StageEventSpec.activationHorizon n))} :=
    (show MeasurableSet {c : InputCfg n |
        ¬ NoOvershoot
          (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256) 5 c} from
      (Set.to_countable _).measurableSet).preimage
        ((measurable_pi_apply
          (s + StageEventSpec.activationHorizon n)).comp
            (measurable_trace init))
  exact htime.inter (hseed.inter (hlower.inter hbad))

/-- The concrete prefix-union factor is at most `9 n⁻³`.
The scoped heartbeat allowance is only for the real-exponential, rational-power,
and ENNReal normalization in this calculation. -/
theorem activation_timer_budget_le
    (hn : timePopulationThreshold ≤ n) :
    (StageEventSpec.activationHorizon n : ℝ≥0∞) *
        ENNReal.ofReal
          (Real.exp
            (-(5 * PhaseThreeModel.Numeric.clockHours n : ℕ))) ≤
      ENNReal.ofReal (9 / (n : ℝ) ^ 3) := by
  obtain ⟨hnpos, _⟩ := ScalarTails.time_population_scalar_bounds hn
  have hnforty : 40 ≤ n := (time_population_bounds hn).2
  have hNnat :=
    PhaseZeroTwoCalibration.activationHorizon_le_nine_hours n hnforty
  have hNreal :
      (StageEventSpec.activationHorizon n : ℝ) ≤
        9 * (n : ℝ) *
          (PhaseThreeModel.Numeric.clockHours n : ℝ) := by
    exact_mod_cast hNnat
  have hHlog :
      Real.log (n : ℝ) ≤
        (PhaseThreeModel.Numeric.clockHours n : ℝ) := by
    have h := PhaseZeroTwoCalibration.log_add_one_le_clockHours n
    linarith
  have hHexp :
      (PhaseThreeModel.Numeric.clockHours n : ℝ) *
          Real.exp (-(PhaseThreeModel.Numeric.clockHours n : ℝ)) ≤ 1 := by
    have hlin :
        (PhaseThreeModel.Numeric.clockHours n : ℝ) ≤
          Real.exp (PhaseThreeModel.Numeric.clockHours n : ℝ) := by
      have h := Real.add_one_le_exp
        (PhaseThreeModel.Numeric.clockHours n : ℝ)
      linarith
    calc
      (PhaseThreeModel.Numeric.clockHours n : ℝ) *
          Real.exp (-(PhaseThreeModel.Numeric.clockHours n : ℝ)) ≤
        Real.exp (PhaseThreeModel.Numeric.clockHours n : ℝ) *
          Real.exp (-(PhaseThreeModel.Numeric.clockHours n : ℝ)) :=
        mul_le_mul_of_nonneg_right hlin (Real.exp_nonneg _)
      _ = 1 := by
        rw [← Real.exp_add]
        simp
  have hfour :
      Real.exp
          (-(4 * (PhaseThreeModel.Numeric.clockHours n : ℝ))) ≤
        1 / (n : ℝ) ^ 4 := by
    have hneg :
        -(4 * (PhaseThreeModel.Numeric.clockHours n : ℝ)) ≤
          -(4 * Real.log (n : ℝ)) := by
      nlinarith only [hHlog]
    calc
      Real.exp
          (-(4 * (PhaseThreeModel.Numeric.clockHours n : ℝ))) ≤
        Real.exp (-(4 * Real.log (n : ℝ))) :=
          Real.exp_le_exp.mpr hneg
      _ = (n : ℝ) ^ (-(4 : ℝ)) := by
        rw [Real.rpow_def_of_pos hnpos]
        congr 1
        ring
      _ = 1 / (n : ℝ) ^ 4 := by
        rw [Real.rpow_neg hnpos.le (4 : ℝ),
          show (n : ℝ) ^ (4 : ℝ) = (n : ℝ) ^ (4 : ℕ) by
            exact_mod_cast Real.rpow_natCast (n : ℝ) 4]
        simp only [div_eq_mul_inv, one_mul]
  have hsplit :
      Real.exp
          (-(5 * PhaseThreeModel.Numeric.clockHours n : ℕ)) =
        Real.exp (-(PhaseThreeModel.Numeric.clockHours n : ℝ)) *
          Real.exp
            (-(4 * (PhaseThreeModel.Numeric.clockHours n : ℝ))) := by
    rw [← Real.exp_add]
    congr 1
    push_cast
    ring
  have hreal :
      (StageEventSpec.activationHorizon n : ℝ) *
          Real.exp
            (-(5 * PhaseThreeModel.Numeric.clockHours n : ℕ)) ≤
        9 / (n : ℝ) ^ 3 := by
    calc
      (StageEventSpec.activationHorizon n : ℝ) *
          Real.exp
            (-(5 * PhaseThreeModel.Numeric.clockHours n : ℕ)) ≤
        (9 * (n : ℝ) *
          (PhaseThreeModel.Numeric.clockHours n : ℝ)) *
            Real.exp
              (-(5 * PhaseThreeModel.Numeric.clockHours n : ℕ)) :=
        mul_le_mul_of_nonneg_right hNreal (Real.exp_nonneg _)
      _ = 9 * (n : ℝ) *
          ((PhaseThreeModel.Numeric.clockHours n : ℝ) *
            Real.exp (-(PhaseThreeModel.Numeric.clockHours n : ℝ))) *
          Real.exp
            (-(4 * (PhaseThreeModel.Numeric.clockHours n : ℝ))) := by
        rw [hsplit]
        ring
      _ ≤ 9 * (n : ℝ) * 1 *
          Real.exp
            (-(4 * (PhaseThreeModel.Numeric.clockHours n : ℝ))) := by
        gcongr
      _ ≤ 9 * (n : ℝ) * 1 * (1 / (n : ℝ) ^ 4) := by
        gcongr
      _ = 9 / (n : ℝ) ^ 3 := by
        field_simp [ne_of_gt hnpos]
  rw [show (StageEventSpec.activationHorizon n : ℝ≥0∞) =
      ENNReal.ofReal (StageEventSpec.activationHorizon n : ℝ) by
        rw [ENNReal.ofReal_natCast],
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  exact ENNReal.ofReal_le_ofReal hreal

/-- Fixed-start Phase-6 timer tail over the epidemic horizon.  Reachability and
the phase lower bound replace the false global bridge. -/
theorem phaseSix_timer_kernel_tail
    (init : InputCfg n)
    (hn : timePopulationThreshold ≤ n)
    (hvalid : validInitial init)
    (hdisp : AdvanceRegimeDispatch
      (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256) 5)
    (c : InputCfg n)
    (hreach :
      (NonuniformMajority (PhaseThreeModel.Numeric.hourIndex n) 256).Reachable
        init c)
    (hlower : ∀ a ∈ c, 2 ≤ a.phase.val)
    (hseed : PhaseSixTimerSeed n c) :
    ((NonuniformMajority
        (PhaseThreeModel.Numeric.hourIndex n) 256).transitionKernel ^
          StageEventSpec.activationHorizon n) c
      {d | ¬ NoOvershoot
        (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256) 5 d} ≤
      ENNReal.ofReal (9 / (n : ℝ) ^ 3) := by
  have hnforty : 40 ≤ n := (time_population_bounds hn).2
  have hn1 : 1 ≤ n := by omega
  have hn2 : 2 ≤ n := by omega
  obtain ⟨_, _hnlog⟩ := ScalarTails.time_population_scalar_bounds hn
  have hlog :
      Real.log (n : ℝ) ≤
        (PhaseThreeModel.Numeric.hourIndex n + 1 : ℕ) := by
    have h := PhaseZeroTwoCalibration.log_add_one_le_clockHours n
    simpa only [PhaseThreeModel.Numeric.clockHours] using (by linarith :
      Real.log (n : ℝ) ≤
        (PhaseThreeModel.Numeric.clockHours n : ℝ))
  have hbigReal :
      (42 : ℝ) ≤ PhaseThreeModel.Numeric.clockHours n := by
    have h := PhaseZeroTwoCalibration.log_add_one_le_clockHours n
    linarith
  have hbigHours : 42 ≤ PhaseThreeModel.Numeric.clockHours n := by
    exact_mod_cast hbigReal
  have hbig : 42 ≤ PhaseThreeModel.Numeric.hourIndex n + 1 := by
    simpa only [PhaseThreeModel.Numeric.clockHours] using hbigHours
  have hfit :
      StageEventSpec.activationHorizon n ≤
        12 * n * (PhaseThreeModel.Numeric.hourIndex n + 1) := by
    calc
      StageEventSpec.activationHorizon n ≤
          9 * n * PhaseThreeModel.Numeric.clockHours n :=
        PhaseZeroTwoCalibration.activationHorizon_le_nine_hours n hnforty
      _ ≤ 12 * n * (PhaseThreeModel.Numeric.hourIndex n + 1) := by
        simp only [PhaseThreeModel.Numeric.clockHours]
        exact Nat.mul_le_mul_right _ (by omega)
  have hreset : CounterResetDest 6 := by
    simp [CounterResetDest]
  have hprefix :=
    noOvershoot_window_le_prefix_sum_wf
      (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
      init hvalid 5 (by norm_num) hreset
      (StageEventSpec.activationHorizon n) c
      hreach hlower hseed.no_overshoot
  have hset :
      {d : InputCfg n | ¬ ¬ AtRiskClockZero
        (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256) 5 d} =
      {d | AtRiskClockZero
        (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256) 5 d} := by
    ext d
    simp
  rw [hset] at hprefix
  refine hprefix.trans ?_
  have hterm : ∀ τ ∈ Finset.range (StageEventSpec.activationHorizon n),
      ((NonuniformMajority
          (PhaseThreeModel.Numeric.hourIndex n) 256).transitionKernel ^ τ) c
        {d | AtRiskClockZero
          (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256) 5 d} ≤
        ENNReal.ofReal
          (Real.exp
            (-(5 * PhaseThreeModel.Numeric.clockHours n : ℕ))) := by
    intro τ hτ
    have hτfit :
        τ ≤ 12 * n * (PhaseThreeModel.Numeric.hourIndex n + 1) :=
      (Nat.le_of_lt (Finset.mem_range.mp hτ)).trans hfit
    simpa only [PhaseThreeModel.Numeric.clockHours] using
      (advance_atRiskClockZero_tail_of_resetDest_wide
        (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
        5 n τ hreset hdisp hn1 hn2 hlog hbig hτfit c
        hseed.population hseed.potential)
  calc
    ∑ τ ∈ Finset.range (StageEventSpec.activationHorizon n),
        ((NonuniformMajority
          (PhaseThreeModel.Numeric.hourIndex n) 256).transitionKernel ^ τ) c
          {d | AtRiskClockZero
            (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256) 5 d} ≤
      ∑ _τ ∈ Finset.range (StageEventSpec.activationHorizon n),
        ENNReal.ofReal
          (Real.exp
            (-(5 * PhaseThreeModel.Numeric.clockHours n : ℕ))) :=
      Finset.sum_le_sum hterm
    _ = (StageEventSpec.activationHorizon n : ℝ≥0∞) *
        ENNReal.ofReal
          (Real.exp
            (-(5 * PhaseThreeModel.Numeric.clockHours n : ℕ))) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ ENNReal.ofReal (9 / (n : ℝ) ^ 3) :=
      activation_timer_budget_le hn

/-- Original-law timer tail, spliced at the genuine first-six time. -/
theorem law_phaseSixTimerFailure_tail
    (init : InputCfg n)
    (hn : timePopulationThreshold ≤ n)
    (hvalid : validInitial init)
    (hdisp : AdvanceRegimeDispatch
      (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256) 5) :
    law init (phaseSixTimerFailure init) ≤
      ENNReal.ofReal (9 / (n : ℝ) ^ 3) := by
  let ε : ℝ≥0∞ := ENNReal.ofReal (9 / (n : ℝ) ^ 3)
  refine genuine_seed_splice (law init) (firstSixStart init)
    (phaseSixTimerFailure init) ε
    (phaseSixTimerFailure_measurable init)
    (fun s =>
      (pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256).le s _
        ((firstSixStart_past init) s)) ?_ ?_
  · intro ω hω
    rw [mem_phaseSixTimerFailure_iff] at hω
    rcases hω with ⟨s, hs, _, _, _⟩
    rw [hs]
    exact WithTop.coe_ne_top
  · intro s
    have hσs := (firstSixStart_past init) s
    rw [pairLogFiltration_eq_comap] at hσs
    obtain ⟨Aσ, _, hAσ⟩ := hσs
    let A : Set ((k : Finset.Iic s) →
        Draw (PhaseThreeModel.Numeric.hourIndex n) 256) :=
      {p | p ∈ Aσ ∧
        PhaseSixTimerSeed n (prefixCfg init s p) ∧
          ∀ a ∈ prefixCfg init s p, 2 ≤ a.phase.val}
    have hmem (ω : InputLog n) :
        frestrictLe (π := fun _ : ℕ =>
          Draw (PhaseThreeModel.Numeric.hourIndex n) 256) s ω ∈ Aσ ↔
          firstSixStart init ω = (s : WithTop ℕ) := by
      change ω ∈ (frestrictLe (π := fun _ : ℕ =>
        Draw (PhaseThreeModel.Numeric.hourIndex n) 256) s) ⁻¹' Aσ ↔
        ω ∈ {ω | firstSixStart init ω = (s : WithTop ℕ)}
      rw [hAσ]
    have htail := recorded_prefix_endpoint_bound init s
      (StageEventSpec.activationHorizon n) A
      {c | ¬ NoOvershoot
        (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256) 5 c} ε
      (fun p hp =>
        phaseSix_timer_kernel_tail init hn hvalid hdisp
          (prefixCfg init s p)
          (prefixCfg_reachable init s p)
          hp.2.2 hp.2.1)
    calc
      law init (phaseSixTimerFailure init ∩
          {ω | firstSixStart init ω = (s : WithTop ℕ)}) ≤
        law init
          {ω |
            frestrictLe (π := fun _ : ℕ =>
              Draw (PhaseThreeModel.Numeric.hourIndex n) 256) s ω ∈ A ∧
            ¬ NoOvershoot
              (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256) 5
              (trace init ω
                (s + StageEventSpec.activationHorizon n))} := by
        apply measure_mono
        rintro ω ⟨hfailure, hs⟩
        rw [mem_phaseSixTimerFailure_iff] at hfailure
        rcases hfailure with ⟨r, hr, hseed, hlower, hbad⟩
        have hrs : r = s := WithTop.coe_injective (hr.symm.trans hs)
        subst r
        change PhaseSixTimerSeed n
          (prefixCfg init s
            (frestrictLe (π := fun _ : ℕ =>
              Draw (PhaseThreeModel.Numeric.hourIndex n) 256) s ω)) at hseed
        change ∀ a ∈
          prefixCfg init s
            (frestrictLe (π := fun _ : ℕ =>
              Draw (PhaseThreeModel.Numeric.hourIndex n) 256) s ω),
            2 ≤ a.phase.val at hlower
        exact ⟨⟨(hmem ω).mpr hs, hseed, hlower⟩, hbad⟩
      _ ≤ ε * law init
          {ω |
            frestrictLe (π := fun _ : ℕ =>
              Draw (PhaseThreeModel.Numeric.hourIndex n) 256) s ω ∈ A} :=
        htail
      _ ≤ ε * law init
          {ω | firstSixStart init ω = (s : WithTop ℕ)} :=
        mul_le_mul_left'
          (measure_mono fun ω hω => (hmem ω).mp hω.1) ε

/-- The threshold-6 epidemic uses the same first-six stopping time and costs
`2 n⁻⁵`. -/
theorem law_phaseSixSpreadFailure_tail
    (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init) :
    law init (phaseSixSpreadFailure init) ≤
      ENNReal.ofReal (2 / (n : ℝ) ^ 5) := by
  have hn2 : 2 ≤ n := by
    have hnforty : 40 ≤ n := (time_population_bounds hinput.1).2
    omega
  exact
    (threshold_spread_at_past_time init hn2 6 (by omega)
      (StageEventSpec.activationHorizon n) (firstSixStart init)
      (firstSixStart_past init)).trans
        (activation_thresholdBudget_le hn2)

/-! ## Deterministic conversion of endpoint successes into the mixed race -/

private theorem stepLabels_phase_le
    (f : Fin m → AgentState L K) (d : Draw L K) (x : Fin m) :
    (f x).phase.val ≤ (stepLabels f d x).phase.val := by
  classical
  cases hsel : selectLabels f d with
  | none =>
      simp [stepLabels, hsel]
  | some pair =>
      rcases pair with ⟨i, j⟩
      have hij := selectLabels_distinct f d i j hsel
      simp only [stepLabels, hsel]
      by_cases hxi : x = i
      · subst x
        have hupd : updateLabels f i j i =
            ((NonuniformMajority L K).δ (f i) (f j)).1 := by
          unfold updateLabels
          rw [Function.update_of_ne hij, Function.update_self]
        rw [hupd]
        exact (Transition_phase_monotone
          (L := L) (K := K) (f i) (f j)).1
      · by_cases hxj : x = j
        · subst x
          have hupd : updateLabels f i j j =
              ((NonuniformMajority L K).δ (f i) (f j)).2 := by
            unfold updateLabels
            rw [Function.update_self]
          rw [hupd]
          exact (Transition_phase_monotone
            (L := L) (K := K) (f i) (f j)).2
        · simp [updateLabels, hxi, hxj]

private theorem labelsAt_phase_mono
    (init : Config (AgentState L K)) (ω : Ω L K) {r t : ℕ}
    (hrt : r ≤ t) (i : Fin init.card) :
    (labelsAt init ω r i).phase.val ≤
      (labelsAt init ω t i).phase.val := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hrt
  clear hrt
  induction d with
  | zero => simp
  | succ d ih =>
      have hstep :
          (labelsAt init ω (r + d) i).phase.val ≤
            (labelsAt init ω (r + d + 1) i).phase.val := by
        rw [labelsAt_succ]
        exact stepLabels_phase_le
          (labelsAt init ω (r + d)) (ω (r + d + 1)) i
      simpa [Nat.add_assoc] using ih.trans hstep

private theorem label_mem_trace
    (init : Config (AgentState L K)) (ω : Ω L K)
    (t : ℕ) (i : Fin init.card) :
    labelsAt init ω t i ∈ trace init ω t := by
  rw [← labelsAt_config]
  exact Multiset.mem_map.mpr ⟨i, by simp, rfl⟩

private theorem exists_label_of_mem
    (init : Config (AgentState L K)) (ω : Ω L K) (t : ℕ)
    {a : AgentState L K} (ha : a ∈ trace init ω t) :
    ∃ i : Fin init.card, labelsAt init ω t i = a := by
  rw [← labelsAt_config] at ha
  rcases Multiset.mem_map.mp ha with ⟨i, _, hi⟩
  exact ⟨i, hi⟩

/-- An all-Phase-6 endpoint with no overshoot proves the exact mixed-window
race. -/
theorem mixedWindowCondition_of_seed_endpoint
    (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init)
    (ω : InputLog n) (u s : ℕ)
    (hcompletion : completionTime init n ω = (u : WithTop ℕ))
    (hseed : PhaseSixSeedReceipt init ω u s)
    (hall : ∀ a ∈
      trace init ω (s + StageEventSpec.activationHorizon n),
        6 ≤ a.phase.val)
    (hno : NoOvershoot
      (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256) 5
      (trace init ω (s + StageEventSpec.activationHorizon n))) :
    MixedWindowCondition init ω u := by
  have huFirst :=
    (exitTime_eq_iff_firstHit init (SamplingComplete n) ω u).mp
      (by simpa only [completionTime] using hcompletion)
  have huComplete := huFirst.1
  have hstart :
      LateMixedFuelLedger.MixedFiveSixWin n (trace init ω u) := by
    refine ⟨huComplete.population, ?_⟩
    intro a ha
    exact Or.inl (huComplete.phase_five a ha)
  have hendSix :
      allPhaseSix
        (trace init ω (s + StageEventSpec.activationHorizon n)) := by
    intro a ha
    have hlo := hall a ha
    have hhi := hno a ha
    omega
  have hhomoLe :
      homogeneousSixStart init ω ≤
        ((s + StageEventSpec.activationHorizon n : ℕ) : WithTop ℕ) := by
    simpa only [homogeneousSixStart] using
      (TraceDrain.exitTime_le_iff init allPhaseSix ω
        (s + StageEventSpec.activationHorizon n)).2
          ⟨s + StageEventSpec.activationHorizon n, le_rfl, hendSix⟩
  have hhomoFinite : homogeneousSixStart init ω ≠ ⊤ :=
    ne_top_of_le_ne_top
      (show ((s + StageEventSpec.activationHorizon n : ℕ) : WithTop ℕ) ≠ ⊤ from
        WithTop.coe_ne_top) hhomoLe
  obtain ⟨v, hv⟩ := WithTop.ne_top_iff_exists.mp hhomoFinite
  have hvTime : homogeneousSixStart init ω = (v : WithTop ℕ) := hv.symm
  have hvFirst :=
    (exitTime_eq_iff_firstHit init allPhaseSix ω v).mp
      (by simpa only [homogeneousSixStart] using hvTime)
  have huv : u ≤ v := by
    by_contra hnot
    have hvu : v < u := Nat.lt_of_not_ge hnot
    have hreach := trace_reachable init ω hvu.le
    have hlower :=
      phase_lower_reachable
        (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
        6 (trace init ω v) (trace init ω u) hreach
        (fun a ha => (hvFirst.1 a ha).ge)
    have hpos : 0 < (trace init ω u).card := by
      rw [huComplete.population]
      have hnforty : 40 ≤ n := (time_population_bounds hinput.1).2
      omega
    obtain ⟨a, ha⟩ := Multiset.card_pos_iff_exists_mem.mp hpos
    have hlo := hlower a ha
    have hfive := huComplete.phase_five a ha
    omega
  have hseven :
      ((s + StageEventSpec.activationHorizon n : ℕ) : WithTop ℕ) <
        firstPhaseSevenStart init ω := by
    by_contra hnot
    have hsevenLe : firstPhaseSevenStart init ω ≤
        ((s + StageEventSpec.activationHorizon n : ℕ) : WithTop ℕ) :=
      le_of_not_gt hnot
    have hsevenFinite : firstPhaseSevenStart init ω ≠ ⊤ :=
      ne_top_of_le_ne_top
        (show ((s + StageEventSpec.activationHorizon n : ℕ) : WithTop ℕ) ≠ ⊤ from
          WithTop.coe_ne_top) hsevenLe
    obtain ⟨w, hw⟩ := WithTop.ne_top_iff_exists.mp hsevenFinite
    have hwFirst := (firstPhaseSevenStart_eq_iff init ω w).mp hw.symm
    rcases hwFirst.1 with ⟨a, ha, hphase⟩
    obtain ⟨i, hi⟩ := exists_label_of_mem init ω w ha
    have hweTop : (w : WithTop ℕ) ≤
        ((s + StageEventSpec.activationHorizon n : ℕ) : WithTop ℕ) :=
      hw.trans_le hsevenLe
    have hwe : w ≤ s + StageEventSpec.activationHorizon n :=
      WithTop.coe_le_coe.mp hweTop
    have hmono := labelsAt_phase_mono init ω hwe i
    have hpast : 7 ≤ (labelsAt init ω w i).phase.val := by
      rw [hi]
      exact hphase
    have hend :
        (labelsAt init ω
          (s + StageEventSpec.activationHorizon n) i).phase.val < 7 :=
      hno _ (label_mem_trace init ω
        (s + StageEventSpec.activationHorizon n) i)
    omega
  have huHomo :
      (u : WithTop ℕ) ≤ homogeneousSixStart init ω := by
    rw [hvTime]
    exact WithTop.coe_le_coe.mpr huv
  have hvEnd : (v : WithTop ℕ) ≤
      ((s + StageEventSpec.activationHorizon n : ℕ) : WithTop ℕ) := by
    simpa only [hvTime] using hhomoLe
  have hhomoSeven :
      homogeneousSixStart init ω < firstPhaseSevenStart init ω := by
    rw [hvTime]
    exact hvEnd.trans_lt hseven
  exact ⟨hstart, huHomo, hhomoSeven⟩

/-- Every mixed-window failure is charged to one of the three original-law
failure sets. -/
theorem mixedFailure_subset_failures
    (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init)
    (seedFailure : Set (InputLog n))
    (hseedProducer : PhaseSixSeedProducer init seedFailure) :
    mixedFailure init ⊆
      (seedFailure ∪ phaseSixSpreadFailure init) ∪
        phaseSixTimerFailure init := by
  intro ω hbad
  by_cases hseedBad : ω ∈ seedFailure
  · exact Or.inl (Or.inl hseedBad)
  by_cases hspreadBad : ω ∈ phaseSixSpreadFailure init
  · exact Or.inl (Or.inr hspreadBad)
  by_cases htimerBad : ω ∈ phaseSixTimerFailure init
  · exact Or.inr htimerBad
  exfalso
  rw [mem_mixedFailure_iff] at hbad
  rcases hbad with ⟨u, hu, hcondition⟩
  rcases hseedProducer.produce ω u hu hseedBad with ⟨s, hseed⟩
  have huFirst :=
    (exitTime_eq_iff_firstHit init (SamplingComplete n) ω u).mp
      (by simpa only [completionTime] using hu)
  have huComplete := huFirst.1
  have hlowerAtCompletion :
      ∀ a ∈ trace init ω u, 5 ≤ a.phase.val := by
    intro a ha
    have hfive := huComplete.phase_five a ha
    omega
  have hlowerFive :=
    phase_lower_reachable
      (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
      5 (trace init ω u) (trace init ω s)
      (trace_reachable init ω hseed.order) hlowerAtCompletion
  have hlowerSeed :
      ∀ a ∈ trace init ω s, 2 ≤ a.phase.val := by
    intro a ha
    have h := hlowerFive a ha
    omega
  have hall : ∀ a ∈
      trace init ω (s + StageEventSpec.activationHorizon n),
        6 ≤ a.phase.val := by
    by_contra hnot
    apply hspreadBad
    exact ⟨s, hseed.time, hseed.timer_seed.population,
      hseed.trigger, hnot⟩
  have hno : NoOvershoot
      (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256) 5
      (trace init ω (s + StageEventSpec.activationHorizon n)) := by
    by_contra hnot
    apply htimerBad
    rw [mem_phaseSixTimerFailure_iff]
    exact ⟨s, hseed.time, hseed.timer_seed, hlowerSeed, hnot⟩
  exact hcondition
    (mixedWindowCondition_of_seed_endpoint
      init hinput ω u s hu hseed hall hno)

/-- The three explicit charges fit below `n⁻²`. -/
theorem mixed_window_budget_le_inverse_square
    (hn : 40 ≤ n) :
    (ENNReal.ofReal (1 / (n : ℝ) ^ 5) +
        ENNReal.ofReal (2 / (n : ℝ) ^ 5)) +
      ENNReal.ofReal (9 / (n : ℝ) ^ 3) ≤
        ENNReal.ofReal (1 / (n : ℝ) ^ 2) := by
  have hnR : (40 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hx2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((n : ℝ) - 1)]
  have hcoef : (31 : ℝ) ≤ (n : ℝ) - 9 := by linarith
  have hmul :
      31 * (n : ℝ) ^ 2 ≤ ((n : ℝ) - 9) * (n : ℝ) ^ 2 :=
    mul_le_mul_of_nonneg_right hcoef (sq_nonneg (n : ℝ))
  have hpoly :
      3 + 9 * (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 3 := by
    have hthree : (3 : ℝ) ≤ 31 * (n : ℝ) ^ 2 := by
      nlinarith only [hx2]
    nlinarith only [hmul, hthree]
  have hreal :
      1 / (n : ℝ) ^ 5 + 2 / (n : ℝ) ^ 5 +
          9 / (n : ℝ) ^ 3 ≤
        1 / (n : ℝ) ^ 2 := by
    field_simp [ne_of_gt hnpos]
    nlinarith only [hpoly]
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal hreal

/-- Raw original-law accounting before the final numerical compression. -/
theorem law_mixedFailure_raw_tail
    (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init)
    (seedFailure : Set (InputLog n))
    (hseedProducer : PhaseSixSeedProducer init seedFailure)
    (hdisp : AdvanceRegimeDispatch
      (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256) 5) :
    law init (mixedFailure init) ≤
      (ENNReal.ofReal (1 / (n : ℝ) ^ 5) +
        ENNReal.ofReal (2 / (n : ℝ) ^ 5)) +
          ENNReal.ofReal (9 / (n : ℝ) ^ 3) := by
  have hspread := law_phaseSixSpreadFailure_tail init hinput
  have htimer := law_phaseSixTimerFailure_tail
    init hinput.1 hinput.2.1 hdisp
  calc
    law init (mixedFailure init) ≤
        law init ((seedFailure ∪ phaseSixSpreadFailure init) ∪
          phaseSixTimerFailure init) :=
      measure_mono
        (mixedFailure_subset_failures init hinput seedFailure hseedProducer)
    _ ≤ law init (seedFailure ∪ phaseSixSpreadFailure init) +
          law init (phaseSixTimerFailure init) :=
      measure_union_le _ _
    _ ≤ (law init seedFailure + law init (phaseSixSpreadFailure init)) +
          law init (phaseSixTimerFailure init) :=
      add_le_add (measure_union_le _ _) le_rfl
    _ ≤ (ENNReal.ofReal (1 / (n : ℝ) ^ 5) +
          ENNReal.ofReal (2 / (n : ℝ) ^ 5)) +
        ENNReal.ofReal (9 / (n : ℝ) ^ 3) :=
      add_le_add (add_le_add hseedProducer.tail hspread) htimer

/-- Original-law inverse-square tail for `mixedFailure`. -/
theorem law_mixedFailure_inverse_square
    (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init)
    (seedFailure : Set (InputLog n))
    (hseedProducer : PhaseSixSeedProducer init seedFailure)
    (hdisp : AdvanceRegimeDispatch
      (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256) 5) :
    law init (mixedFailure init) ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 2) := by
  have hnforty : 40 ≤ n := (time_population_bounds hinput.1).2
  exact (law_mixedFailure_raw_tail init hinput seedFailure
    hseedProducer hdisp).trans
      (mixed_window_budget_le_inverse_square hnforty)

/-!
THEOREM LIST
* `PhaseSixSeedReceipt.trigger`
* `mem_phaseSixTimerFailure_iff`
* `phaseSixTimerFailure_measurable`
* `activation_timer_budget_le`
* `phaseSix_timer_kernel_tail`
* `law_phaseSixTimerFailure_tail`
* `law_phaseSixSpreadFailure_tail`
* `mixedWindowCondition_of_seed_endpoint`
* `mixedFailure_subset_failures`
* `mixed_window_budget_le_inverse_square`
* `law_mixedFailure_raw_tail`
* `law_mixedFailure_inverse_square`

CLOSES
* The four tail theorems without any
  `OvershootForcesZeroClock 5` hypothesis.
* The genuine-stopping-time timer tail under the original law, using
  `validInitial init` and the reachable per-configuration bridge.
* The threshold-6 epidemic tail and the final inverse-square mixed-window
  estimate without conditioning on completion or survival.
* Compatibility of the three public seed structures with the waiting producer.

EXPLICIT INPUTS
* `PhaseSixSeedProducer`, unchanged from the earlier version.
* `AdvanceRegimeDispatch 5`, still explicit.
* `validInitial init`: explicit on the standalone timer tail and supplied by
  `ThresholdEpidemic.GoodInput` in the composed mixed-failure theorems.

UNFINISHED
* Construct `PhaseSixSeedProducer` from the compiled Phase-5 upper timer and
  the role/Clock existence receipt.
* Discharge `AdvanceRegimeDispatch 5` by the Phase-6 transition case split.
END
-/

end Ripple.PopulationProtocol.ExactMajority.LateMixedFiveSixWindowTailWf

end
