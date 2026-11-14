-- Ripple/PopulationProtocol/ExactMajority/Probability/LateTwoLevelWarmup.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingTerminalDebtDeadlines
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingHourStops

/-!
# The lower-hour debt at the penultimate two-level window

The paper's Y_< is the compiled debtX at k = ell + 1, and its Y is
debtY at that same k. The paper's majority process X is a different
quantity. This file keeps those names separate.

The warmup has length ceil(5 n^2/C), threshold .018 M, and error exp(-M/500).
Every bound is under the original law and retains its observed live gates.
The canonical start is a genuine stopping time, defined without clock success.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal

namespace Ripple.PopulationProtocol.ExactMajority.LateStrengthening

open PhaseThreeClockProducer

open TimeTheorem PairLog PhaseOneDrain StageEventSpec
open AveragingMixedAlgebra AveragingMixedLedgers AveragingDebtService
open AveragingPotentialService AveragingTerminalDebt AveragingTerminalDebtTails
open AveragingStoppedDebt AveragingTerminalDebtDeadlines AveragingHourStops

variable {L n : ℕ}

def lowerHourDebt (σ : Sign) (ell : ℕ) (c : Cfg L 256) : ℚ :=
  debtX σ (ell + 1) c

def twoLevelDebt (σ : Sign) (ell : ℕ) (c : Cfg L 256) : ℚ :=
  debtY σ (ell + 1) c

theorem lowerHourDebt_nonneg (σ : Sign) (ell : ℕ) (c : Cfg L 256) :
    0 ≤ lowerHourDebt σ ell c := by
  have hd : 0 ≤ minorityDebt σ (ell + 1) c :=
    mul_nonneg (by positivity) (minorityMass_nonneg σ c)
  change 0 ≤ debtX σ (ell + 1) c
  rw [debtX_eq]
  positivity

theorem twoLevelDebt_nonneg (σ : Sign) (ell : ℕ) (c : Cfg L 256) :
    0 ≤ twoLevelDebt σ ell c := by
  have hd : 0 ≤ minorityDebt σ (ell + 1) c :=
    mul_nonneg (by positivity) (minorityMass_nonneg σ c)
  change 0 ≤ debtY σ (ell + 1) c
  rw [debtY_eq]
  positivity

theorem twoLevelDebt_sub_lowerHourDebt
    (σ : Sign) (ell : ℕ) (c : Cfg L 256) :
    twoLevelDebt σ ell c - lowerHourDebt σ ell c =
      (exactZeroCount (ell + 1) c : ℚ) :=
  debtY_sub_debtX σ (ell + 1) c

theorem lowerHourDebt_trace_le (σ : Sign) (ell : ℕ)
    (init : Cfg L 256) (ω : Ω L 256) {s t : ℕ} (hst : s ≤ t)
    (hdom : ∀ u, s ≤ u → u ≤ t → PotentialDomain (trace init ω u)) :
    lowerHourDebt σ ell (trace init ω t) ≤
      lowerHourDebt σ ell (trace init ω s) :=
  debtX_trace_le σ (ell + 1) init ω s t hst
    (fun u hsu hut a ha => (hdom u hsu hut a ha).range)
    (fun u hsu hut a ha => (hdom u hsu hut a ha).safe)
    (fun u hsu hut a ha => (hdom u hsu hut a ha).small_carrier)

theorem twoLevelDebt_trace_le (σ : Sign) (ell : ℕ)
    (init : Cfg L 256) (ω : Ω L 256) {s t : ℕ} (hst : s ≤ t)
    (hdom : ∀ u, s ≤ u → u ≤ t → PotentialDomain (trace init ω u)) :
    twoLevelDebt σ ell (trace init ω t) ≤
      twoLevelDebt σ ell (trace init ω s) :=
  debtY_trace_le σ (ell + 1) init ω s t hst
    (fun u hsu hut a ha => (hdom u hsu hut a ha).range)
    (fun u hsu hut a ha => (hdom u hsu hut a ha).safe)
    (fun u hsu hut a ha => (hdom u hsu hut a ha).small_carrier)

/-- The floor used by J is dominated by the actual exact-hour-zero count. -/
theorem twoLevelDebt_floor_excess_le_zero (σ : Sign) (ell M : ℕ)
    (c : Cfg L 256)
    (hlower : lowerHourDebt σ ell c ≤ (9 / 500 : ℚ) * M) :
    Nat.floor (twoLevelDebt σ ell c) - Nat.ceil ((9 / 500 : ℚ) * M) ≤
      exactZeroCount (ell + 1) c := by
  have hf : (Nat.floor (twoLevelDebt σ ell c) : ℚ) ≤ twoLevelDebt σ ell c :=
    Nat.floor_le (twoLevelDebt_nonneg σ ell c)
  have hb : (9 / 500 : ℚ) * M ≤ (Nat.ceil ((9 / 500 : ℚ) * M) : ℚ) :=
    Nat.le_ceil _
  have he := twoLevelDebt_sub_lowerHourDebt σ ell c
  have hn : Nat.floor (twoLevelDebt σ ell c) ≤
      Nat.ceil ((9 / 500 : ℚ) * M) + exactZeroCount (ell + 1) c := by
    have hr : (Nat.floor (twoLevelDebt σ ell c) : ℚ) ≤
        (Nat.ceil ((9 / 500 : ℚ) * M) : ℚ) + exactZeroCount (ell + 1) c := by
      linarith only [hf, hb, he, hlower]
    exact_mod_cast hr
  omega

open Classical in
structure TwoLevelWarmupGate (σ : Sign) (ell n C M : ℕ)
    (c : Cfg L 256) : Prop where
  population : c.card = n
  domain : PotentialDomain c
  main_count : RoleSplitConcentration.mainCount c = M
  minority : minorityDebt σ (ell + 1) c ≤ (1 / 125 : ℚ) * M
  clocks : warmClockCount C ≤ c.countP (ClockServiceSource (ell + 1))

theorem TwoLevelWarmupGate.xGate {σ : Sign} {ell n C M : ℕ}
    {c : Cfg L 256} (hc : TwoLevelWarmupGate σ ell n C M c) :
    XGate σ (ell + 1) ((1 / 125 : ℚ) * M) n (warmClockCount C) c :=
  ⟨hc.population, hc.domain, hc.minority, hc.clocks⟩

/-- These are current-state gates; no future success is a conditioning event. -/
def twoLevelWarmupFailure (init : Cfg L 256) (s : ℕ)
    (σ : Sign) (ell n C M : ℕ) : Set (Ω L 256) :=
  {ω | (∀ u, u ≤ clockWarmup n C →
      TwoLevelWarmupGate σ ell n C M (trace init ω (s + u))) ∧
    (9 / 500 : ℚ) * M <
      lowerHourDebt σ ell (trace init ω (s + clockWarmup n C))}

theorem twoLevelWarmup_failure_subset (init : Cfg L 256) (s : ℕ)
    (σ : Sign) (ell n C M : ℕ) :
    twoLevelWarmupFailure init s σ ell n C M ⊆
      thresholdFailure init s (debtX σ (ell + 1)) (2 * ((1 / 125 : ℚ) * M))
        (XGate σ (ell + 1) ((1 / 125 : ℚ) * M) n (warmClockCount C))
        M (1 / 500) (clockWarmup n C) := by
  rintro ω ⟨hwindow, hbad⟩
  have hstart := hwindow 0 (Nat.zero_le _)
  simp only [Nat.add_zero] at hstart
  refine ⟨⟨?_, fun u hu => (hwindow u hu).xGate⟩, ?_⟩
  · simpa only [hstart.main_count] using
      x_initial_ceiling_le_mainCount σ (ell + 1) ((1 / 125 : ℚ) * M)
        (trace init ω s) hstart.minority
  · change (9 / 500 : ℚ) * M <
      debtX σ (ell + 1) (trace init ω (s + clockWarmup n C)) at hbad
    linarith only [hbad]

theorem twoLevelWarmup_tail_from (init : Cfg L 256) (s : ℕ)
    (B : Set ((i : Finset.Iic s) → Draw L 256))
    (σ : Sign) (ell : ℕ) (hell : ell + 1 ≤ L)
    (n C M : ℕ) (hn : 2 ≤ n) (hC : 0 < C) (hroles : C + M ≤ n) :
    law init {ω | frestrictLe (π := fun _ : ℕ => Draw L 256) s ω ∈ B ∧
        ω ∈ twoLevelWarmupFailure init s σ ell n C M} ≤
      ENNReal.ofReal (Real.exp (-(M : ℝ) / 500)) *
        law init {ω | frestrictLe (π := fun _ : ℕ => Draw L 256) s ω ∈ B} := by
  refine (measure_mono ?_).trans
    (debtX_warmup_tail_from init s B σ (ell + 1) hell
      ((1 / 125 : ℚ) * M) n C M hn hC hroles)
  rintro ω ⟨hp, hf⟩
  exact ⟨hp, twoLevelWarmup_failure_subset init s σ ell n C M hf⟩

theorem twoLevelWarmup_tail_at_pastTime (init : Cfg L 256)
    (τ : Ω L 256 → WithTop ℕ) (hτ : PairLogPastTime τ)
    (σ : Sign) (ell : ℕ) (hell : ell + 1 ≤ L)
    (n C M : ℕ) (hn : 2 ≤ n) (hC : 0 < C) (hroles : C + M ≤ n) :
    law init {ω | ∃ s : ℕ, τ ω = (s : WithTop ℕ) ∧
        ω ∈ twoLevelWarmupFailure init s σ ell n C M} ≤
      ENNReal.ofReal (Real.exp (-(M : ℝ) / 500)) := by
  refine (measure_mono ?_).trans
    (debtX_warmup_tail_at_pastTime init τ hτ σ (ell + 1) hell
      ((1 / 125 : ℚ) * M) n C M hn hC hroles)
  rintro ω ⟨s, hs, hf⟩
  exact ⟨s, hs, twoLevelWarmup_failure_subset init s σ ell n C M hf⟩

theorem twoLevelWarmup_tail_at_hourStart (init : InputCfg n)
    (seed : InputLog n → WithTop ℕ) (hseed : PairLogPastTime seed)
    (σ : Sign) (ell : ℕ) (hell : ell + 1 ≤ PhaseThreeModel.Numeric.hourIndex n)
    (C M : ℕ) (hn : 2 ≤ n) (hC : 0 < C) (hroles : C + M ≤ n) :
    law init {ω | ∃ s : ℕ,
        hourStart init seed (ell + 1) ω = (s : WithTop ℕ) ∧
        ω ∈ twoLevelWarmupFailure init s σ ell n C M} ≤
      ENNReal.ofReal (Real.exp (-(M : ℝ) / 500)) :=
  twoLevelWarmup_tail_at_pastTime init (hourStart init seed (ell + 1))
    (hourStart_pastTime init seed hseed (ell + 1)) σ ell hell
    n C M hn hC hroles

theorem twoLevelWarmup_tail_at_phaseThreeSeed (init : InputCfg n)
    (σ : Sign) (ell : ℕ) (hell : ell + 1 ≤ PhaseThreeModel.Numeric.hourIndex n)
    (C M : ℕ) (hn : 2 ≤ n) (hC : 0 < C) (hroles : C + M ≤ n) :
    law init {ω | ∃ s : ℕ,
        hourStart init (seedTime init 3) (ell + 1) ω = (s : WithTop ℕ) ∧
        ω ∈ twoLevelWarmupFailure init s σ ell n C M} ≤
      ENNReal.ofReal (Real.exp (-(M : ℝ) / 500)) :=
  twoLevelWarmup_tail_at_hourStart init (seedTime init 3) (seedTime_pastTime init 3)
    σ ell hell C M hn hC hroles

/-- A successful clock witness identifies the already-defined stopping time.
It is only intersected with the failure event in this statement. -/
theorem twoLevelWarmup_tail_on_clockHistory (init : InputCfg n)
    (σ : Sign) (ell : ℕ) (hell : ell + 1 ≤ PhaseThreeModel.Numeric.hourIndex n)
    (C M : ℕ) (hn : 2 ≤ n) (hC : 0 < C) (hroles : C + M ≤ n) :
    law init {ω | ∃ (S T ρ : ℕ) (w : ClockTimes init),
        ClockHistory init ω S T ρ w ∧
        ω ∈ twoLevelWarmupFailure init (w.start (ell + 1)) σ ell n C M} ≤
      ENNReal.ofReal (Real.exp (-(M : ℝ) / 500)) := by
  refine (measure_mono ?_).trans
    (twoLevelWarmup_tail_at_phaseThreeSeed init σ ell hell C M hn hC hroles)
  rintro ω ⟨S, T, ρ, w, hc, hf⟩
  exact ⟨w.start (ell + 1), hourStart_phaseThreeSeed_clockHistory hc (ell + 1) hell, hf⟩

open Classical in
theorem twoLevelWarmupGate_of_clockHistory
    {init : InputCfg n} {ω : InputLog n} {S T ρ v : ℕ}
    {w : ClockTimes init} (hc : ClockHistory init ω S T ρ w)
    (σ : Sign) (ell M : ℕ)
    (hell : ell + 1 ≤ PhaseThreeModel.Numeric.hourIndex n)
    (hSv : S ≤ v) (hvρ : v < ρ)
    (hstart : w.start (ell + 1) ≤ v) (hfinish : v ≤ w.finish (ell + 1))
    (hpop : (trace init ω v).card = n)
    (hdom : PotentialDomain (trace init ω v))
    (hmain : RoleSplitConcentration.mainCount (trace init ω v) = M)
    (hminor : minorityDebt σ (ell + 1) (trace init ω v) ≤ (1 / 125 : ℚ) * M) :
    TwoLevelWarmupGate σ ell n (clockCount (trace init ω S)) M (trace init ω v) :=
  ⟨hpop, hdom, hmain, hminor,
    clockFloor_of_clockHistory hc hSv hvρ (ell + 1) hell hstart hfinish⟩

theorem lowerHourDebt_after_warmup (init : Cfg L 256) (ω : Ω L 256)
    (σ : Sign) (ell n C M s t : ℕ)
    (hst : s + clockWarmup n C ≤ t)
    (hdom : ∀ u, s + clockWarmup n C ≤ u → u ≤ t →
      PotentialDomain (trace init ω u))
    (hwarm : lowerHourDebt σ ell (trace init ω (s + clockWarmup n C)) ≤
      (9 / 500 : ℚ) * M) :
    lowerHourDebt σ ell (trace init ω t) ≤ (9 / 500 : ℚ) * M :=
  (lowerHourDebt_trace_le σ ell init ω hst hdom).trans hwarm

end Ripple.PopulationProtocol.ExactMajority.LateStrengthening

end
