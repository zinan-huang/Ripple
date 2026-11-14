-- Ripple/PopulationProtocol/ExactMajority/Probability/LateSeedNearTestFailure.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.LateSeedReceiptProducerTail
import Ripple.PopulationProtocol.ExactMajority.Probability.LateTwoLevelBlock
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingGlobalFailureSplice

/-!
# Original-law terminal near-test failures for the N16 receipt

There are two stopped tests between successful N13 hours and the retained-credit
receipt.

* `AveragingGlobalFailureSplice.globalTerminalFailure` is the N13 terminal
  `ell + 2` X/Y drain.  Its complement supplies the protected-credit,
  minority, and potential part of `SmallReadout`.
* `globalNearLevelFailure` is the N16 `ell + 1` two-level block.  Its complement
  is intended to supply the mixed barrier used by
  `receipt_near_credit_at_first_exit`.

Their union is the `nearTestFailure` branch intended for the later deterministic
cover of `lateSamplingSeedProducerSafeFailure`.  The old-index cutoff is not
included here.  Every random seed, selected level, count pair, and block start
is selected from a measurable past.  The future successful receipt is never a
conditioning event.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.LateStrengthening

open PhaseThreeClockProducer
open TimeTheorem PairLog PhaseOneDrain StageEventSpec
open AveragingSparseEntry AveragingEventInterface
open AveragingDominantLevelSplice AveragingGlobalFailureSplice
open AveragingObservedHourTails AveragingNumerics AveragingHourStops

variable {n : ℕ}

/-- The selected strict-small-gap level is usable by the N16 near block.
The tie schedule is deliberately excluded. -/
def nearLevelScheduleAdmissible (n : ℕ) (p : ℕ × ℕ) : Prop :=
  5 ≤ p.1 ∧ p.1 + 2 ≤ PhaseThreeModel.Numeric.hourIndex n

/-- The N16 two-level block at a fixed genuine seed and fixed level, with the
clock and Main counts read at that seed.  The start is the independently
defined pair-log stopping time `hourStart ... (ell + 1)`. -/
def observedTwoLevelBlockFailure
    (init : InputCfg n) (S : ℕ)
    (j : Fin (PhaseThreeModel.Numeric.hourIndex n + 1)) :
    Set (InputLog n) :=
  {ω | ∃ s : ℕ,
    hourStart init (seedTime init 3) (j.val + 1) ω =
        (s : WithTop ℕ) ∧
      ω ∈ twoLevelBlockFailure init s (selectedSign init) j n
        (seedCounts init S ω).1 (seedCounts init S ω).2}

open Classical in
/-- Seed-measurable selected-level version of the N16 two-level block. -/
def scheduledNearLevelFailure
    (init : InputCfg n) (S : ℕ) (p : ℕ × ℕ) : Set (InputLog n) :=
  if h : nearLevelScheduleAdmissible n p then
    observedTwoLevelBlockFailure init S
      ⟨p.1, by
        have := h.2
        omega⟩
  else ∅

/-- The selected N16 near-level failure, spliced over the genuine Phase-3 seed. -/
def globalNearLevelFailure (init : InputCfg n) : Set (InputLog n) :=
  ⋃ S, seedPiece init S ∩
    {ω | ω ∈ scheduledNearLevelFailure init S
      (selectedSchedule init (trace init ω S))}

/-- The named original-law family supplied as `nearTestFailure` to
`late_sampling_seed_receipt_safe_estimate`.

The `globalTerminalFailure` branch covers failure of the terminal package that
precedes the protected `.9616` credit.  The `globalNearLevelFailure` branch
covers failure of the N16 warmup/nonlinear-service block that should establish

`twoLevelBarrier M (mixedShallowPositiveNat σ ell c)
  (debtY σ (ell + 1) c) ≤ twoLevelTarget M`.

The later `hcover`, not this definition, relates these stopped test failures to
the future absence of `LateSamplingSeedReceipt`. -/
def nearTestFailure (init : InputCfg n) : Set (InputLog n) :=
  globalTerminalFailure init ∪ globalNearLevelFailure init

/-- Membership rewrite for the named near-test family. -/
theorem mem_nearTestFailure_iff
    (init : InputCfg n) (ω : InputLog n) :
    ω ∈ nearTestFailure init ↔
      ω ∈ globalTerminalFailure init ∨
        ∃ S : ℕ,
          S ≤ earlyHorizon n ∧
          SafeSparseSeed init ω S ∧
          ω ∈ scheduledNearLevelFailure init S
            (selectedSchedule init (trace init ω S)) := by
  simp only [nearTestFailure, globalNearLevelFailure, Set.mem_union,
    Set.mem_iUnion, Set.mem_inter_iff, seedPiece, Set.mem_setOf_eq]
  tauto

private theorem seedCounts_main_upper_near
    (init : InputCfg n) (S : ℕ) (ω : InputLog n)
    (hp : SeedProfile n init (trace init ω S)) :
    25 * (seedCounts init S ω).2 ≤ 13 * n := by
  have hm := hp.role_good.2.2.1
  change (RoleSplitConcentration.mainCount (trace init ω S) : ℝ) ≤
    (1 + (1 / 25 : ℝ)) * (n : ℝ) / 2 at hm
  have hmEq :
      RoleSplitConcentration.mainCount (trace init ω S) =
        timeMainCount (trace init ω S) := by
    simp only [RoleSplitConcentration.mainCount, timeMainCount,
      AveragingEventInterface.countP_classical]
  rw [hmEq] at hm
  have h :
      (25 : ℝ) * (timeMainCount (trace init ω S) : ℝ) ≤
        13 * (n : ℝ) := by
    linarith
  exact_mod_cast h

private theorem weighted_near_fibres
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (E : Set Ω) (τ : Ω → WithTop ℕ)
    (P B : ℕ → Set Ω) (ε : ℝ≥0∞)
    (hP : ∀ s, MeasurableSet (P s))
    (hsub : ∀ s, P s ⊆ E ∩ {ω | τ ω = (s : WithTop ℕ)})
    (ht : ∀ s, μ (P s ∩ B s) ≤ ε * μ (P s)) :
    μ (⋃ s, P s ∩ B s) ≤ ε * μ E := by
  have hd : Pairwise fun s t => Disjoint (P s) (P t) := by
    intro s t hst
    apply Set.disjoint_left.mpr
    intro ω hs ht'
    exact hst (WithTop.coe_injective
      ((hsub s hs).2.symm.trans (hsub t ht').2))
  have hu : (⋃ s, P s) ⊆ E := by
    rintro ω hω
    obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hω
    exact (hsub s hs).1
  calc
    μ (⋃ s, P s ∩ B s) ≤ ∑' s, μ (P s ∩ B s) :=
      measure_iUnion_le _
    _ ≤ ∑' s, ε * μ (P s) := ENNReal.tsum_le_tsum ht
    _ = ε * μ (⋃ s, P s) := by
      rw [ENNReal.tsum_mul_left, ← measure_iUnion hd hP]
    _ ≤ ε * μ E := mul_le_mul_left' (measure_mono hu) ε

/-- Prefix-weighted calibrated form of `twoLevelBlock_tail_from`.
The measurable event `E` is observed at the physical block start `s`; it is
retained as a multiplicative factor through the warmup/service decomposition. -/
theorem two_level_block_prefix_tail_calibrated
    (init : InputCfg n) (s : ℕ)
    (E : Set (InputLog n))
    (hE : MeasurableSet[pairLogFiltration
      (PhaseThreeModel.Numeric.hourIndex n) 256 s] E)
    (σ : Sign)
    (j : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (hj : 1 ≤ j.val)
    (hk : j.val + 1 ≤ PhaseThreeModel.Numeric.hourIndex n)
    (C M : ℕ)
    (hn : timePopulationThreshold ≤ n)
    (hC : 0 < C)
    (hroles : C + M ≤ n)
    (hlower : 12 * n ≤ 25 * M)
    (hupper : 25 * M ≤ 13 * n) :
    law init (E ∩ twoLevelBlockFailure init s σ j n C M) ≤
      ENNReal.ofReal (2 / (n : ℝ) ^ 20) * law init E := by
  have hE' := hE
  rw [pairLogFiltration_eq_comap] at hE'
  obtain ⟨A, _, hA⟩ := hE'
  have hp :
      {ω | frestrictLe (π := fun _ : ℕ =>
        Draw (PhaseThreeModel.Numeric.hourIndex n) 256) s ω ∈ A} = E := hA
  have hnthree : 3 ≤ n := by
    have := (time_population_bounds hn).2
    omega
  have hM : 0 < M := by omega
  have ht := twoLevelBlock_tail_from init s A σ j hj hk n C M
    hnthree hC hM hroles hupper
  have hbound := ht.trans
    (mul_le_mul_right'
      (twoLevelBlock_error_le_inverse_power hn hlower)
      (law init {ω | frestrictLe (π := fun _ : ℕ =>
        Draw (PhaseThreeModel.Numeric.hourIndex n) 256) s ω ∈ A}))
  change law init
      ({ω | frestrictLe (π := fun _ : ℕ =>
          Draw (PhaseThreeModel.Numeric.hourIndex n) 256) s ω ∈ A} ∩
        twoLevelBlockFailure init s σ j n C M) ≤
    ENNReal.ofReal (2 / (n : ℝ) ^ 20) *
      law init {ω | frestrictLe (π := fun _ : ℕ =>
        Draw (PhaseThreeModel.Numeric.hourIndex n) 256) s ω ∈ A} at hbound
  simpa only [hp] using hbound

/-- Fixed genuine seed and level, but random block start and seed-observed
clock/Main counts.  The start fibres are disjoint, and each count fibre is
measurable at that start. -/
theorem observed_two_level_block_failure_tail
    (init : InputCfg n)
    (hn : timePopulationThreshold ≤ n)
    (S : ℕ)
    (j : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (hj : 1 ≤ j.val)
    (hk : j.val + 1 ≤ PhaseThreeModel.Numeric.hourIndex n)
    (E : Set (InputLog n))
    (hE : MeasurableSet[pairLogFiltration
      (PhaseThreeModel.Numeric.hourIndex n) 256 S] E)
    (hseed : ∀ ω ∈ E, SafeSparseSeed init ω S) :
    law init (E ∩ observedTwoLevelBlockFailure init S j) ≤
      ENNReal.ofReal (2 / (n : ℝ) ^ 20) * law init E := by
  let τ := hourStart init (seedTime init 3) (j.val + 1)
  let P : ℕ → Set (InputLog n) := fun s =>
    E ∩ {ω | τ ω = (s : WithTop ℕ)}
  let B : ℕ → Set (InputLog n) := fun s =>
    {ω | ω ∈ twoLevelBlockFailure init s (selectedSign init) j n
      (seedCounts init S ω).1 (seedCounts init S ω).2}
  have hτ := hourStart_phaseThreeSeed_pastTime init (j.val + 1)
  have hnpos : 0 < n := by
    have := (time_population_bounds hn).2
    omega
  have hPempty (s : ℕ) (hSs : ¬ S ≤ s) : P s = ∅ := by
    ext ω
    simp only [P, Set.mem_inter_iff, Set.mem_setOf_eq,
      Set.mem_empty_iff_false, iff_false]
    rintro ⟨hωE, hs⟩
    have hseedTime : seedTime init 3 ω = (S : WithTop ℕ) :=
      (seedTime_eq_iff init 3 ω S).2 (hseed ω hωE).1
    have hs' :
        hourStart init (seedTime init 3) (j.val + 1) ω =
          (s : WithTop ℕ) := by
      simpa only [τ] using hs
    have hstart := hourStart_le_iff_of_seed init (seedTime init 3)
      (j.val + 1) ω S s hseedTime
    obtain ⟨v, hv, _⟩ := hstart.mp hs'.le
    exact hSs (hv.1.trans hv.2)
  have hPm (s : ℕ) :
      MeasurableSet[pairLogFiltration
        (PhaseThreeModel.Numeric.hourIndex n) 256 s] (P s) := by
    by_cases hSs : S ≤ s
    · exact (((pairLogFiltration _ _).mono hSs _ hE).inter (hτ s))
    · rw [hPempty s hSs]
      exact MeasurableSpace.measurableSet_empty _
  have hlocal (s : ℕ) :
      law init (P s ∩ B s) ≤
        ENNReal.ofReal (2 / (n : ℝ) ^ 20) * law init (P s) := by
    by_cases hSs : S ≤ s
    · dsimp only [B]
      apply seedCounts_prefix_bound init S s hSs (P s) (hPm s) hnpos
        (fun ω hω => (hseed ω hω.1).2.1)
        (fun p => twoLevelBlockFailure init s (selectedSign init) j n p.1 p.2)
        (ENNReal.ofReal (2 / (n : ℝ) ^ 20))
      intro p hC hmain hroles
      let F := P s ∩ {ω | seedCounts init S ω = p}
      change law init
          (F ∩ twoLevelBlockFailure init s (selectedSign init) j n p.1 p.2) ≤
        ENNReal.ofReal (2 / (n : ℝ) ^ 20) * law init F
      have hFm :
          MeasurableSet[pairLogFiltration
            (PhaseThreeModel.Numeric.hourIndex n) 256 s] F :=
        (hPm s).inter (seedCounts_fibre_measurable init S s hSs p)
      by_cases hnonempty : F.Nonempty
      · obtain ⟨ω, hω⟩ := hnonempty
        have hprofile : SeedProfile n init (trace init ω S) :=
          (hseed ω hω.1.1).2.1
        have hupper := seedCounts_main_upper_near init S ω hprofile
        have hpEq : seedCounts init S ω = p := hω.2
        rw [hpEq] at hupper
        exact two_level_block_prefix_tail_calibrated init s F hFm
          (selectedSign init) j hj hk p.1 p.2 hn hC hroles hmain hupper
      · have hF0 : F = ∅ := Set.not_nonempty_iff_eq_empty.mp hnonempty
        rw [hF0]
        simp
    · rw [hPempty s hSs]
      simp
  have hsplice := weighted_near_fibres (law init) E τ P B
    (ENNReal.ofReal (2 / (n : ℝ) ^ 20))
    (fun s => (pairLogFiltration _ _).le s _ (hPm s))
    (fun s ω hω => ⟨hω.1, hω.2⟩) hlocal
  have he :
      E ∩ observedTwoLevelBlockFailure init S j =
        ⋃ s, P s ∩ B s := by
    ext ω
    simp only [observedTwoLevelBlockFailure, P, B, τ,
      Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨hωE, s, hs, hb⟩
      exact ⟨s, ⟨⟨hωE, hs⟩, hb⟩⟩
    · rintro ⟨s, ⟨⟨hωE, hs⟩, hb⟩⟩
      exact ⟨hωE, s, hs, hb⟩
  rw [he]
  exact hsplice

/-- Fixed genuine seed, with the strict-small-gap level selected from that
seed prefix.  Observable partitioning introduces no factor for the level. -/
theorem fixed_seed_selected_near_level_tail
    (init : InputCfg n)
    (hn : timePopulationThreshold ≤ n)
    (S : ℕ) :
    law init (seedPiece init S ∩
      {ω | ω ∈ scheduledNearLevelFailure init S
        (selectedSchedule init (trace init ω S))}) ≤
      ENNReal.ofReal (2 / (n : ℝ) ^ 20) * law init (seedPiece init S) := by
  let f : InputLog n → ℕ × ℕ :=
    fun ω => selectedSchedule init (trace init ω S)
  let B : ℕ × ℕ → Set (InputLog n) := scheduledNearLevelFailure init S
  apply observable_partition_bound (law init) (seedPiece init S)
    ((pairLogFiltration _ _).le S _ (seedPiece_measurable init S)) f
    (fun p => (pairLogFiltration _ _).le S _
      (selectedSchedule_fibre_measurable init S p)) B
    (ENNReal.ofReal (2 / (n : ℝ) ^ 20))
  intro p
  by_cases hp : nearLevelScheduleAdmissible n p
  · have hp1 : 5 ≤ p.1 := hp.1
    have hp2 : p.1 + 2 ≤ PhaseThreeModel.Numeric.hourIndex n := hp.2
    let E := seedPiece init S ∩ {ω | f ω = p}
    have hE :
        MeasurableSet[pairLogFiltration
          (PhaseThreeModel.Numeric.hourIndex n) 256 S] E :=
      (seedPiece_measurable init S).inter
        (selectedSchedule_fibre_measurable init S p)
    have hs : ∀ ω ∈ E, SafeSparseSeed init ω S := by
      intro ω hω
      exact hω.1.2
    let j : Fin (PhaseThreeModel.Numeric.hourIndex n + 1) :=
      ⟨p.1, by
        have := hp.2
        omega⟩
    have ht := observed_two_level_block_failure_tail init hn S j
      (by dsimp only [j]; omega)
      (by dsimp only [j]; omega) E hE hs
    simpa [E, f, B, scheduledNearLevelFailure, hp, j] using ht
  · simp [B, scheduledNearLevelFailure, hp]

/-- Global N16 near-level tail.  Genuine seed fibres are disjoint, so possible
seed times do not contribute a union factor. -/
theorem global_near_level_failure_tail
    (init : InputCfg n)
    (hn : timePopulationThreshold ≤ n) :
    law init (globalNearLevelFailure init) ≤
      ENNReal.ofReal (2 / (n : ℝ) ^ 20) := by
  let P : ℕ → Set (InputLog n) := seedPiece init
  let B : ℕ → Set (InputLog n) := fun S =>
    {ω | ω ∈ scheduledNearLevelFailure init S
      (selectedSchedule init (trace init ω S))}
  have ht := weighted_near_fibres (law init) Set.univ (seedTime init 3)
    P B (ENNReal.ofReal (2 / (n : ℝ) ^ 20))
    (fun S => (pairLogFiltration _ _).le S _ (seedPiece_measurable init S))
    (fun S ω hω => ⟨Set.mem_univ ω,
      (seedTime_eq_iff init 3 ω S).2 hω.2.1⟩)
    (fun S => fixed_seed_selected_near_level_tail init hn S)
  simpa only [globalNearLevelFailure, P, B, measure_univ, mul_one] using ht

private theorem twice_hour_error_eq (n : ℕ) :
    2 * hourError n = ENNReal.ofReal (2 / (n : ℝ) ^ 20) := by
  unfold hourError
  rw [show (2 : ℝ) / (n : ℝ) ^ 20 =
      2 * (1 / (n : ℝ) ^ 20) by ring,
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
    ENNReal.ofReal_ofNat]

/-- Before the final numerical compression, the combined family costs only
`4 / n^20`. -/
theorem near_test_failure_raw_estimate
    (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init) :
    law init (nearTestFailure init) ≤
      ENNReal.ofReal (4 / (n : ℝ) ^ 20) := by
  have hterminal :
      law init (globalTerminalFailure init) ≤
        ENNReal.ofReal (2 / (n : ℝ) ^ 20) := by
    calc
      law init (globalTerminalFailure init) ≤ 2 * hourError n :=
        global_terminal_failure_tail init hinput.2.1 hinput.2.2 hinput.1
      _ = ENNReal.ofReal (2 / (n : ℝ) ^ 20) :=
        twice_hour_error_eq n
  have hnear := global_near_level_failure_tail init hinput.1
  change law init
    (globalTerminalFailure init ∪ globalNearLevelFailure init) ≤ _
  calc
    law init (globalTerminalFailure init ∪ globalNearLevelFailure init) ≤
        law init (globalTerminalFailure init) +
          law init (globalNearLevelFailure init) :=
      measure_union_le _ _
    _ ≤ ENNReal.ofReal (2 / (n : ℝ) ^ 20) +
        ENNReal.ofReal (2 / (n : ℝ) ^ 20) :=
      add_le_add hterminal hnear
    _ = ENNReal.ofReal (4 / (n : ℝ) ^ 20) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

/-- The raw `4 / n^20` charge lies in the `1 / n^4` slot reserved by
`late_sampling_seed_receipt_safe_estimate`. -/
theorem near_test_failure_budget {n : ℕ}
    (hn : timePopulationThreshold ≤ n) :
    ENNReal.ofReal (4 / (n : ℝ) ^ 20) ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 4) := by
  apply ENNReal.ofReal_le_ofReal
  obtain ⟨-, hnpos, hlog, hclock, -, -⟩ := time_hour_calibration hn
  have hcoefficient :
      (4 : ℝ) ≤
        10 * (PhaseThreeModel.Numeric.clockHours n : ℝ) := by
    nlinarith only [hlog, hclock]
  calc
    (4 : ℝ) / (n : ℝ) ^ 20 ≤
        10 * (PhaseThreeModel.Numeric.clockHours n : ℝ) /
          (n : ℝ) ^ 20 :=
      div_le_div_of_nonneg_right hcoefficient (pow_pos hnpos 20).le
    _ ≤ 1 / (n : ℝ) ^ 4 := hour_test_union_scalar hn

/-- The requested unconditional `hnear` estimate. -/
theorem near_test_failure_estimate
    (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init) :
    law init (nearTestFailure init) ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 4) :=
  (near_test_failure_raw_estimate init hinput).trans
    (near_test_failure_budget hinput.1)

end Ripple.PopulationProtocol.ExactMajority.LateStrengthening

end
