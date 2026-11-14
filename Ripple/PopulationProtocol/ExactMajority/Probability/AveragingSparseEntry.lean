import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingEventInterface
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseTwoSparseProducer
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseZeroTwoEntryClosed

/-!
# Safe sparse seeds on the original law

The closed entry producers are reused here. On the actual averaging failure
event, the deterministic strong branch is absent. The remaining branch has a
drained Phase-1 boundary outside the already proved Phase-0 and drain errors.
The actual clock history supplies AsyncEntry, so its sparse strengthening does
not require a new outcome or activation probability estimate.

The final bound is precisely the first term in the N13 error split. It does not
assert the local averaging estimate or the N13 headline.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Ripple.PopulationProtocol.ExactMajority.AveragingSparseEntry

open TimeTheorem PairLog StageEventSpec
open PhaseZeroEntry PhaseOneDrainStopping PhaseTwoDrainedSafety
open AveragingEventInterface

variable {n : ℕ}

def SafeSeedState (init c : InputCfg n) : Prop :=
  SeedProfile n init c ∧ sparse c ∧ AllSmallSafe c

def SafeSparseSeed (init : InputCfg n) (ω : InputLog n) (s : ℕ) : Prop :=
  firstPhaseSeed init 3 s ω ∧ SafeSeedState init (trace init ω s)

def safeSparseEntry (init : InputCfg n) : Set (InputLog n) :=
  {ω | ∃ s : ℕ, SafeSparseSeed init ω s}

/-- The safe seed predicate is measurable at the genuine seed time. -/
theorem safeSparseSeed_past (init : InputCfg n) (s : ℕ) :
    MeasurableSet[pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256 s]
      {ω | SafeSparseSeed init ω s} := by
  exact (firstPhaseSeed_measurableSet init 3 s).inter
    ((show MeasurableSet {c : InputCfg n | SafeSeedState init c} from
      (Set.to_countable _).measurableSet).preimage (measurable_trace_at init s))

/-- Safety at the genuine seed persists on every later actual draw. -/
theorem safeSparseSeed_small_safe_future
    (init : InputCfg n) (ω : InputLog n) (s u : ℕ)
    (hseed : SafeSparseSeed init ω s) (hsu : s ≤ u) :
    AllSmallSafe (trace init ω u) := by
  exact small_safe_reachable _ _ (TimeTheorem.trace_reachable init ω hsu)
    (fun a ha => (hseed.2.1.phase_range a ha).1) hseed.2.2.2

/-- A witness in the safe-entry event belongs to the same genuine seed as
any supplied AsyncEntry on that execution. -/
theorem safeSeedState_at_entry {init : InputCfg n} {ω : InputLog n}
    {S T : ℕ} (hentry : AsyncEntry init ω S T)
    (hgood : ω ∈ safeSparseEntry init) :
    SafeSeedState init (trace init ω S) := by
  obtain ⟨s, hs⟩ := hgood
  have heq : s = S :=
    PhaseThreeClockProducer.firstPhaseSeed_unique init 3 ω
      hs.1 hentry.first_phase_seed
  simpa only [heq] using hs.2

/-- An all-Phase-1 configuration must precede a genuine Phase-3 threshold
hit. This uses phase monotonicity, not an inference from stable outputs. -/
theorem all_one_time_lt_seed (init : InputCfg n) (ω : InputLog n)
    (s S : ℕ)
    (hone : ∀ a ∈ trace init ω s, a.phase.val = 1)
    (hfirst : firstHit (someGE (n := n) 3) (trace init ω) S) :
    s < S := by
  by_contra hnot
  have hSs : S ≤ s := by omega
  have hupper := phase_upper_reachable 1
    (trace init ω S) (trace init ω s)
    (TimeTheorem.trace_reachable init ω hSs)
    (fun a ha => (hone a ha).le)
  obtain ⟨a, ha, hphase⟩ := hfirst.1
  have hcap := hupper a ha
  omega

/-- The Main count used by the averaging readout is the same count as at
the retained Phase-1 entry profile. -/
theorem mainCount_at_seed (init : InputCfg n) (ω : InputLog n)
    (s S T : ℕ) (hprofile : PhaseOneEntryProfile init ω s)
    (hentry : AsyncEntry init ω S T) :
    timeMainCount (trace init ω S) =
      RoleSplitConcentration.mainCount (trace init ω s) := by
  classical
  have hsS : s ≤ S :=
    (all_one_time_lt_seed init ω s S hprofile.all_one hentry.seed_first).le
  have hwindow : ∀ u, s ≤ u → u ≤ S → ∀ a ∈ trace init ω u,
      1 ≤ a.phase.val ∧ a.phase.val ≤ 3 := by
    intro u hsu huS a ha
    have hlo := phase_lower_reachable 1
      (trace init ω s) (trace init ω u)
      (TimeTheorem.trace_reachable init ω hsu)
      (fun b hb => (hprofile.all_one b hb).symm.le)
    have hhi := phase_upper_reachable 3
      (trace init ω u) (trace init ω S)
      (TimeTheorem.trace_reachable init ω huS)
      (fun b hb => (hentry.seed_profile.phase_range b hb).2)
    exact ⟨hlo a ha, hhi a ha⟩
  have hbefore : ∀ u, s ≤ u → u < S → ∀ a ∈ trace init ω u,
      a.phase.val ≤ 2 := by
    intro u _ huS a ha
    have hlt : a.phase.val < 3 := Nat.lt_of_not_ge
      (fun hp => hentry.seed_first.2 u huS ⟨a, ha, hp⟩)
    omega
  have hcounts := PhaseTwoSeedProfile.mixed_role_count_trace .main
    init ω s S hsS hwindow hbefore
  simpa only [timeMainCount, RoleSplitConcentration.mainCount,
    countP_classical] using hcounts

/-- The existing sparse-entry and safety theorems give all seed premises,
including safety of pending Phase-1 agents. -/
theorem safeSparseSeed_of_drained_clockHistory
    (init : InputCfg n) (ω : InputLog n) (d S T ρ : ℕ)
    (hready : PhaseOneReadyProfile init (trace init ω d))
    (hdS : d ≤ S) {w : ClockTimes init}
    (hclock : ClockHistory init ω S T ρ w) :
    SafeSparseSeed init ω S := by
  have hsparse := PhaseTwoSparse.sparse_async_entry_of_drained
    init ω d S T hready hdS hclock.entry
  exact ⟨hclock.entry.first_phase_seed, hclock.entry.seed_profile,
    hsparse.2 S le_rfl hclock.entry.order,
    readyProfile_small_safe_future init ω d S hready hdS⟩

/-- The only upstream exceptions needed inside the actual averaging
failure event are the existing Phase-0 and weak-drain exceptions. -/
theorem averaging_sparse_failure_cover
    (init : InputCfg n) (hinput : ThresholdEpidemic.GoodInput n init) :
    phaseAveragingFailure (reviewedStageEvents n init) \ safeSparseEntry init ⊆
      PhaseZeroTwoEntry.phaseZeroFailure init ∪ firstDrainedWindowFailure init := by
  classical
  intro ω hbad
  by_cases hzero : ω ∈ PhaseZeroTwoEntry.phaseZeroFailure init
  · exact Or.inl hzero
  by_cases hdrain : ω ∈ firstDrainedWindowFailure init
  · exact Or.inr hdrain
  exfalso
  have hphaseZero : ∃ s ≤ 350 * n * PhaseThreeModel.Numeric.clockHours n,
      IsFirstAllPhaseOne init ω s ∧ PhaseOneEntryProfile init ω s := by
    by_contra hnone
    exact hzero hnone
  obtain ⟨s, _, hfirst, hprofile⟩ := hphaseZero
  obtain ⟨S, T, ρ, hT, _, hclockGood⟩ := hbad.1.1
  obtain ⟨w, hclock⟩ := hclockGood
  have hnforty : 40 ≤ n := (time_population_bounds hinput.1).2
  have hsmall := averagingFailure_small_gap
    (by omega : 0 < n) hbad.1 hT hclock
  have hmain := mainCount_at_seed init ω s S T hprofile hclock.entry
  have hweak : 40 * (initialGap init).natAbs ≤
      RoleSplitConcentration.mainCount (trace init ω s) := by
    change 40 * gapMagnitude init ≤ _
    rw [← hmain]
    exact hsmall.le
  obtain ⟨d, hd⟩ := exists_drainedPrefix_of_not_failure
    init hinput ω s hfirst hprofile hweak hdrain
  have hready := hd.ready_profile hinput
  have hdS : d ≤ S :=
    (all_one_time_lt_seed init ω d S hready.all_one hclock.entry.seed_first).le
  exact hbad.2 ⟨S,
    safeSparseSeed_of_drained_clockHistory init ω d S T ρ hready hdS hclock⟩

theorem sparse_entry_error_budget {n : ℕ} (hn : 8 ≤ n) :
    ENNReal.ofReal (8 / (n : ℝ) ^ 3) + 1 / (n : ℝ≥0∞) ^ 2 ≤
      ENNReal.ofReal (2 / (n : ℝ) ^ 2) := by
  have hnR : (8 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hdrop : 8 / (n : ℝ) ^ 3 ≤ 1 / (n : ℝ) ^ 2 := by
    apply (div_le_div_iff₀ (pow_pos hnpos 3) (pow_pos hnpos 2)).2
    calc
      8 * (n : ℝ) ^ 2 ≤ (n : ℝ) * (n : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right hnR (sq_nonneg (n : ℝ))
      _ = 1 * (n : ℝ) ^ 3 := by ring
  have hcast : 1 / (n : ℝ≥0∞) ^ 2 =
      ENNReal.ofReal (1 / (n : ℝ) ^ 2) := by
    rw [ENNReal.ofReal_div_of_pos (pow_pos hnpos 2), ENNReal.ofReal_one,
      ENNReal.ofReal_pow (Nat.cast_nonneg n), ENNReal.ofReal_natCast]
  rw [hcast, ← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  calc
    8 / (n : ℝ) ^ 3 + 1 / (n : ℝ) ^ 2 ≤
        1 / (n : ℝ) ^ 2 + 1 / (n : ℝ) ^ 2 := add_le_add hdrop le_rfl
    _ = 2 / (n : ℝ) ^ 2 := by ring

/-- The safe sparse-entry charge in N13, on the original pair-log law.
There is no N12 error charge: the event is already inside clockBy. -/
theorem averaging_sparse_entry_exception
    (init : InputCfg n) (hinput : ThresholdEpidemic.GoodInput n init) :
    law init
        (phaseAveragingFailure (reviewedStageEvents n init) \ safeSparseEntry init) ≤
      ENNReal.ofReal (2 / (n : ℝ) ^ 2) := by
  have hnforty : 40 ≤ n := (time_population_bounds hinput.1).2
  have hzero : law init (PhaseZeroTwoEntry.phaseZeroFailure init) ≤
      ENNReal.ofReal (8 / (n : ℝ) ^ 3) :=
    PhaseZeroEntryProducer.phase_zero_entry_estimate init hinput
  have hdrain := firstDrainedWindowFailure_le init hinput
  calc
    law init
        (phaseAveragingFailure (reviewedStageEvents n init) \ safeSparseEntry init) ≤
      law init (PhaseZeroTwoEntry.phaseZeroFailure init ∪
        firstDrainedWindowFailure init) :=
      measure_mono (averaging_sparse_failure_cover init hinput)
    _ ≤ law init (PhaseZeroTwoEntry.phaseZeroFailure init) +
        law init (firstDrainedWindowFailure init) :=
      measure_union_le _ _
    _ ≤ ENNReal.ofReal (8 / (n : ℝ) ^ 3) + 1 / (n : ℝ≥0∞) ^ 2 :=
      add_le_add hzero hdrain
    _ ≤ ENNReal.ofReal (2 / (n : ℝ) ^ 2) :=
      sparse_entry_error_budget (by omega)

end Ripple.PopulationProtocol.ExactMajority.AveragingSparseEntry

end
