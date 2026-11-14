-- Ripple/PopulationProtocol/ExactMajority/Probability/LateSeedReceiptCoverData.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.LateSeedReceiptTestInstantiation
import Ripple.PopulationProtocol.ExactMajority.Probability.LateSeedOldIndexFailure

/-!
# Deterministic data for the N16 receipt cover

The successful N13 hour induction is used only deterministically here.  Its
first-failed-hour families were already charged under the original law in
`protectedTestFailure` and `nearTestFailure`.

The old-index selector fibre is adapted at the early potential checkpoint.  It
contains the genuine safe seed, the selected strict-small-gap level, successful
completed tests before the current early checkpoint, and the current potential
cap.  It does not contain the current terminal endpoint failure and does not
contain `successfulHistory`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.LateStrengthening

open PhaseThreeClockProducer
open TimeTheorem PairLog PhaseOneDrain StageEventSpec
open AveragingSparseEntry AveragingEventInterface
open AveragingDominantLevelSplice AveragingGlobalFailureSplice
open AveragingHourEvents AveragingHourPrefix AveragingHourStops
open AveragingHourGateAssembly AveragingHourSchedule
open AveragingTerminalPackages AveragingTerminalDebtDeadlines
open AveragingCreditClockBridge AveragingCheckpointReadout
open AveragingIntegerPotential AveragingMixedLedgers AveragingMixedAlgebra
open AveragingLiveProduct AveragingTerminalDebt
open AveragingPendingCredit AveragingPendingCreditTransitions
open AveragingCreditCount AveragingCreditTransitions
open AveragingOldHourGate AveragingCanonicalBlocks AveragingRandomOldBlocks
open AveragingObservedHourTails AveragingNumerics AveragingSeededDelay
open AveragingWorkCounter AveragingObservedBlocks AveragingOldBlocks
open AveragingWorkBudget LateSamplingSeedReceipt
open AveragingHourInvariant AveragingClockBlocks AveragingCancellationAlgebra

variable {n : ℕ}

/-- The three terminal checkpoint bounds consumed by
`lateSamplingSeedReceipt_of_checkpoint_data`. -/
structure ReceiptTerminalCheckpointData
    (init : InputCfg n) (ω : InputLog n) (S : ℕ)
    (w : ClockTimes init) (ell : ℕ) (σ : Sign) : Prop where
  protected_credit :
    (601 / 625 : ℚ) *
        (timeMainCount (trace init ω S) : ℚ) ≤
      totalCredit σ ell (ell + 2) (trace init ω w.cap)
  minority :
    250 * (2 : ℚ) ^ ell *
        sideMass (oppositeSign σ) (trace init ω w.cap) ≤
      timeMainCount (trace init ω S)
  potential :
    (1000 : ℚ) * augmentedPhi ell (trace init ω w.cap) ≤
      timeMainCount (trace init ω S)

/-- The exact mixed checkpoint used by the retained near-level alternative. -/
structure ReceiptNearCheckpointData
    (init : InputCfg n) (ω : InputLog n)
    (S T ρ ell : ℕ) (σ : Sign) (checkpoint : ℕ) : Prop where
  seed_le : S ≤ checkpoint
  before_exit : checkpoint < ρ
  barrier :
    twoLevelBarrier (timeMainCount (trace init ω S))
        (mixedShallowPositiveNat σ ell (trace init ω checkpoint))
        (debtY σ (ell + 1) (trace init ω checkpoint)) ≤
      twoLevelTarget (timeMainCount (trace init ω S))
  exception_bound :
    (exceptionCount (ell + 1) (trace init ω checkpoint) : ℚ) ≤
      (3 / 1250 : ℚ) * timeMainCount (trace init ω S)
  potential_bound :
    augmentedPhi ell (trace init ω checkpoint) ≤
      (1 / 1000 : ℚ) * timeMainCount (trace init ω S)

private theorem cover_history_data
    {init : InputCfg n} {ω : InputLog n} {S T ρ u v : ℕ}
    {w : ClockTimes init} (hvalid : validInitial init)
    (hseed : SafeSparseSeed init ω S)
    (H : ClockHistory init ω S T ρ w) (hu : S ≤ u) (huv : u ≤ v)
    (hvρ : v < ρ) :
    (∀ q, u ≤ q → q ≤ v → ∀ a ∈ trace init ω q,
      1 ≤ a.phase.val ∧ a.phase.val ≤ 3) ∧
    (∀ q, u ≤ q → q ≤ v → ∀ a ∈ trace init ω q,
      a.smallBias.val ∈ ({2, 3, 4} : Finset ℕ)) ∧
    (∀ q, u ≤ q → q ≤ v → ∀ a ∈ trace init ω q,
      a.role ≠ .main → a.smallBias.val = 3) := by
  refine ⟨?_, ?_, ?_⟩
  · intro q huq hqv
    exact H.phase_range q (hu.trans huq) (hqv.trans_lt hvρ)
  · intro q huq hqv a ha
    exact (potentialDomain_of_safeSparseSeed_clockHistory hvalid hseed H
      (hu.trans huq) (hqv.trans_lt hvρ) a ha).safe
  · intro q huq hqv a ha hm
    exact (potentialDomain_of_safeSparseSeed_clockHistory hvalid hseed H
      (hu.trans huq) (hqv.trans_lt hvρ) a ha).small_carrier hm

private theorem cover_signed_mass_of_winning
    {init : InputCfg n} (hvalid : validInitial init)
    {ω : InputLog n} {S T ρ v : ℕ} {w : ClockTimes init}
    (H : ClockHistory init ω S T ρ w)
    (hSv : S ≤ v) (hvρ : v < ρ) (σ : Sign)
    (hw : winningSign init σ) :
    prePhase4MassSum (trace init ω v) =
      if σ = .pos then (gapMagnitude init : ℚ)
      else -(gapMagnitude init : ℚ) := by
  have hm := trace_mixedSigned_eq_initialGap init hvalid ω v
    (fun a ha => by
      have := (H.phase_range v hSv hvρ a ha).2
      omega)
  cases σ with
  | pos =>
      have hp : 0 < initialGap init := hw
      rw [if_pos rfl, hm]
      have heq :
          (initialGap init : ℤ) = ((initialGap init).natAbs : ℤ) := by
        omega
      unfold gapMagnitude
      first
        | exact_mod_cast heq
        | simpa using congrArg (fun z : ℤ => (z : ℚ)) heq
  | neg =>
      have hn : initialGap init < 0 := hw
      rw [if_neg (by decide : Sign.neg ≠ Sign.pos), hm]
      have heq :
          (initialGap init : ℤ) = -((initialGap init).natAbs : ℤ) := by
        omega
      unfold gapMagnitude
      first
        | exact_mod_cast heq
        | simpa using congrArg (fun z : ℤ => (z : ℚ)) heq

private theorem cover_seed_clock_main_le_card (c : InputCfg n) :
    clockCount c + timeMainCount c ≤ Multiset.card c := by
  classical
  unfold clockCount timeMainCount
  induction c using Multiset.induction_on with
  | empty => simp
  | cons a c ih =>
      rw [Multiset.countP_cons, Multiset.countP_cons, Multiset.card_cons]
      by_cases hc : a.role = Role.clock
      · have hm : a.role ≠ Role.main := by rw [hc]; decide
        (simp [hc, hm] at ih ⊢) <;> omega
      · by_cases hm : a.role = Role.main
        · (simp [hc, hm] at ih ⊢) <;> omega
        · (simp [hc, hm] at ih ⊢) <;> omega

private theorem cover_terminal_window_before_finish
    {init : InputCfg n} {ω : InputLog n} {S T ρ ell : ℕ}
    {w : ClockTimes init} (H : ClockHistory init ω S T ρ w)
    (hn : timePopulationThreshold ≤ n)
    (hell : ell + 2 ≤ PhaseThreeModel.Numeric.hourIndex n) :
    let C := clockCount (trace init ω S)
    let M := timeMainCount (trace init ω S)
    w.start (ell + 2) + (clockWarmup n C + majorityWork n M) <
      w.finish (ell + 2) := by
  intro C M
  have hST := clockHistory_seed_lt_exit H
  have hd := H.density S le_rfl (lt_of_le_of_lt hST.1 hST.2)
  have hnpos : 0 < n := by
    have := (time_population_bounds hn).2
    omega
  have hC : 0 < C := by dsimp [C]; omega
  have hM : 0 < M := by dsimp [M]; omega
  have hcard : (trace init ω S).card = n :=
    H.entry.seed_profile.card_eq
  have hCM : C + M ≤ n := by
    have hbound := cover_seed_clock_main_le_card (trace init ω S)
    dsimp [C, M]
    omega
  have hCcard : C ≤ n := by omega
  have hratio : 12 * C ≤ 7 * M := by
    dsimp [C, M] at hd ⊢
    omega
  have hfit := terminal_work_fits_window n C M
    (w.finish (ell + 2) - w.start (ell + 2))
    (by omega) hC hM hCcard hratio (H.raw_width (ell + 2) hell)
  omega

private theorem cover_phi_le_of_nat {h : ℕ} {c d : InputCfg n}
    (hm : augmentedPhiNat h c ≤ augmentedPhiNat h d) :
    augmentedPhi h c ≤ augmentedPhi h d := by
  have hcast := (Nat.cast_le (α := ℚ)).mpr hm
  rwa [augmentedPhiNat_cast, augmentedPhiNat_cast] at hcast

private theorem cover_augmentedPhiNat_zero_of_initialized
    (c : InputCfg n) (hphase : ∀ a ∈ c, 3 ≤ a.phase.val) :
    augmentedPhiNat 0 c = 0 := by
  induction c using Multiset.induction_on with
  | empty => simp [augmentedPhiNat]
  | cons a c ih =>
      have ha := hphase a (Multiset.mem_cons_self a c)
      have htail := ih (fun b hb => hphase b (Multiset.mem_cons_of_mem hb))
      have hhead : augmentedAgentPhiNat 0 a = 0 := by
        unfold augmentedAgentPhiNat
        rw [if_neg (by omega)]
        cases hb : a.bias <;> simp [activeAgentPhiNat, hb]
      simp only [augmentedPhiNat, Multiset.map_cons, Multiset.sum_cons,
        hhead, zero_add]
      exact htail

/-- Successful selected hours either supply all three cap bounds or expose the
already charged N13 terminal failure. -/
theorem receipt_terminal_checkpoint_data_or_failure
    {init : InputCfg n} (hvalid : validInitial init)
    (hn : timePopulationThreshold ≤ n)
    {ω : InputLog n} {S T ρ ell : ℕ} {w : ClockTimes init} {σ : Sign}
    (hseed : SafeSparseSeed init ω S)
    (H : ClockHistory init ω S T ρ w)
    (hwinning : winningSign init σ)
    (hscale : DominantScale init (trace init ω S) ell)
    (hno : ω ∉ hourFailure
      (hourSuccess init (seedTime init 3) ell σ) ell) :
    ReceiptTerminalCheckpointData init ω S w ell σ ∨
      ω ∈ terminalFailure init (w.start (ell + 2)) σ ell
        ((2 / 125 : ℚ) * timeMainCount (trace init ω S)) n
        (clockCount (trace init ω S))
        (timeMainCount (trace init ω S)) := by
  have hellone : 1 ≤ ell := by have := hscale.1; omega
  let C := clockCount (trace init ω S)
  let M := timeMainCount (trace init ω S)
  let W := warmCheckpoint w C ell
  let P := potentialCheckpoint w C M ell
  let V := workCheckpoint w C M ell
  let s := w.start (ell + 2)
  let q := s + (clockWarmup n C + majorityWork n M)
  have hsucc := success_of_not_hourFailure
    (hourSuccess init (seedTime init 3) ell σ) hno hellone le_rfl
  have hsTime : seedTime init 3 ω = (S : WithTop ℕ) :=
    (seedTime_eq_iff init 3 ω S).2 hseed.1
  have hchecks := hourChecks_of_success H (seedTime init 3) hsTime σ
    hellone (by have := hscale.2.1; omega) le_rfl hsucc
  rcases hchecks with ⟨_, _, hphi, _, hminor⟩
  have hminorV :
      (2 : ℚ) ^ ell * sideMass (oppositeSign σ) (trace init ω V) ≤
        (1 / 250 : ℚ) * M := by
    simpa only [minorityTarget,
      show ell + 4 ≠ ell by omega,
      show ell + 3 ≠ ell by omega,
      show ell + 2 ≠ ell by omega,
      show ell + 1 ≠ ell by omega,
      if_false, if_pos rfl] using hminor (by omega)
  have hwork : workCheckpoint w C M ell < w.start (ell + 1) := by
    have h := work_before_next H
      (by exact_mod_cast (time_hour_calibration hn).2.1)
      (h := ell + 1) (by omega)
      (by have := hscale.2.1; omega)
    simpa using h
  have hmono := clockHistory_start_mono H
    (by exact_mod_cast (time_hour_calibration hn).2.1)
    (ell + 1) (ell + 2) (by omega) hscale.2.1
  have hbudget : clockWarmup n C + potentialTrials n M ≤ rawWork n M C := by
    unfold clockWarmup potentialTrials rawWork
    omega
  have hPbefore : P ≤ s := by
    dsimp only [P, V, s, potentialCheckpoint, workCheckpoint,
      warmCheckpoint] at hwork hbudget ⊢
    omega
  have hVbefore : V ≤ s := by
    dsimp only [V, s, workCheckpoint] at hwork ⊢
    omega
  have hfinish := cover_terminal_window_before_finish H hn hscale.2.1
  have hqfinish : q < w.finish (ell + 2) := by
    simpa only [q, s, C, M] using hfinish
  have hSq : S ≤ q :=
    (H.start_positive (ell + 2) (by omega) hscale.2.1).1.trans
      (by dsimp [q, s]; omega)
  have hqρ : q < ρ := hqfinish.trans
    ((H.hour_before_cap (ell + 2) hscale.2.1).2.trans_lt
      (lt_of_le_of_lt (Nat.le_add_right _ _) H.protected_settling))
  have hsq : s ≤ q := Nat.le_add_right _ _
  have hgate : ∀ u, u ≤ clockWarmup n C + majorityWork n M →
      TerminalGate σ ell ((2 / 125 : ℚ) * M) n C M
        (trace init ω (s + u)) := by
    intro u hu
    let v := s + u
    have hsv : s ≤ v := by dsimp [v]; omega
    have hvq : v ≤ q := by dsimp [v, q]; omega
    have hSv : S ≤ v :=
      (H.start_positive (ell + 2) (by omega) hscale.2.1).1.trans hsv
    have hvρ : v < ρ := hvq.trans_lt hqρ
    have hdom := potentialDomain_of_safeSparseSeed_clockHistory
      hvalid hseed H hSv hvρ
    have hminorMono := sideMass_le_of_clockHistory (oppositeSign σ)
      hvalid hseed H
      (by
        dsimp [V, workCheckpoint]
        exact (H.start_positive ell hellone
          (by have := hscale.2.1; omega)).1.trans (by omega))
      (hVbefore.trans hsv) hvρ
    have hminorDebt : minorityDebt σ (ell + 2) (trace init ω v) ≤
        (2 / 125 : ℚ) * M := by
      have hm : ∀ (τ : Sign) (c : InputCfg n),
          minorityMass τ c = sideMass (oppositeSign τ) c := by
        intro τ c
        cases τ <;> rfl
      have hnonneg : (0 : ℚ) ≤ (2 : ℚ) ^ ell := by positivity
      have hscaled := mul_le_mul_of_nonneg_left hminorMono hnonneg
      have hpow : (2 : ℚ) ^ (ell + 2) = 4 * (2 : ℚ) ^ ell := by ring
      unfold minorityDebt
      rw [hm, hpow]
      linarith only [hscaled, hminorV]
    have hphiV : augmentedPhi ell (trace init ω v) ≤
        (1 / 1000 : ℚ) * M := by
      have hm := potential_trace_le_of_domain ell hellone init ω P v
        (hPbefore.trans hsv)
        (fun z hPz hzv => potentialDomain_of_safeSparseSeed_clockHistory
          hvalid hseed H
          ((H.start_positive ell hellone
            (by have := hscale.2.1; omega)).1.trans (by
              dsimp only [P, potentialCheckpoint, warmCheckpoint] at hPz
              omega))
          (hzv.trans_lt hvρ))
      have hphi' : 1000 * augmentedPhi ell (trace init ω P) ≤ (M : ℚ) :=
        hphi
      linarith only [cover_phi_le_of_nat hm, hphi']
    have hclock := clockFloor_of_clockHistory H hSv hvρ (ell + 2)
      hscale.2.1 hsv (hvq.trans hqfinish.le)
    have hmain : RoleSplitConcentration.mainCount (trace init ω v) = M := by
      dsimp [M]
      convert H.main_count v hSv hvρ using 1 <;>
        simp only [RoleSplitConcentration.mainCount, timeMainCount]
    have hsigned := cover_signed_mass_of_winning hvalid H hSv hvρ σ hwinning
    have hy := yGate_with_canonical_partners σ ell
      (debtX σ (ell + 2) (trace init ω v)) (gapMagnitude init)
      n M (trace init ω v)
      (population_of_clockHistory H v) hdom le_rfl (by omega)
      hmain hsigned (by
        have hs : (2 : ℚ) * M ≤
            5 * (2 : ℚ) ^ ell * gapMagnitude init := by
          exact_mod_cast hscale.2.2.1
        nlinarith only [hs]) hphiV
    exact ⟨population_of_clockHistory H v, hdom, hmain,
      hminorDebt, hclock, hy.partners⟩
  by_cases hbad : ω ∈ terminalFailure init s σ ell
      ((2 / 125 : ℚ) * M) n C M
  · exact Or.inr (by simpa only [s, C, M] using hbad)
  · have hY : debtY σ (ell + 2) (trace init ω q) ≤
        (7 / 200 : ℚ) * M := by
      by_contra hlarge
      apply hbad
      exact ⟨hgate, lt_of_not_ge hlarge⟩
    have hphiQ : augmentedPhi ell (trace init ω q) ≤
        (1 / 1000 : ℚ) * M := by
      have hm := potential_trace_le_of_domain ell hellone init ω P q
        (hPbefore.trans (by dsimp [q, s]; omega))
        (fun z hPz hzq => potentialDomain_of_safeSparseSeed_clockHistory
          hvalid hseed H
          ((H.start_positive ell hellone
            (by have := hscale.2.1; omega)).1.trans (by
              dsimp only [P, potentialCheckpoint, warmCheckpoint] at hPz
              omega))
          (hzq.trans_lt hqρ))
      have hphi' : 1000 * augmentedPhi ell (trace init ω P) ≤ (M : ℚ) :=
        hphi
      linarith only [cover_phi_le_of_nat hm, hphi']
    have hcreditQ := initial_mixed_credit_clockHistory H hSq hqρ σ ell
      hscale.2.1 hqfinish.le hY hphiQ
    have hqcap : q ≤ w.cap :=
      hqfinish.le.trans (H.hour_before_cap (ell + 2) hscale.2.1).2
    have hcapρ : w.cap < ρ :=
      lt_of_le_of_lt (Nat.le_add_right _ _) H.protected_settling
    have hdata := cover_history_data hvalid hseed H hSq hqcap hcapρ
    have hcreditMixed := hcreditQ.trans
      (mixedTotalCredit_trace_mono σ ell (ell + 2) (by omega)
        init ω q w.cap hqcap hdata.1 hdata.2.1 hdata.2.2)
    have hphaseCap : ∀ a ∈ trace init ω w.cap, 3 ≤ a.phase.val :=
      fun a ha => (H.all_three w.cap H.all_before_cap hcapρ a ha).ge
    have hcredit : (601 / 625 : ℚ) * M ≤
        totalCredit σ ell (ell + 2) (trace init ω w.cap) := by
      rw [← mixedTotalCredit_eq_totalCredit σ ell (ell + 2)
        (trace init ω w.cap) hphaseCap]
      exact hcreditMixed
    have hminorCap : 250 * (2 : ℚ) ^ ell *
        sideMass (oppositeSign σ) (trace init ω w.cap) ≤ M := by
      have hm := sideMass_le_of_clockHistory (oppositeSign σ)
        hvalid hseed H
        (by
          dsimp [V, workCheckpoint]
          exact (H.start_positive ell hellone
            (by have := hscale.2.1; omega)).1.trans (by omega))
        ((hVbefore.trans hsq).trans hqcap) hcapρ
      have hscaled := mul_le_mul_of_nonneg_left hm
        (show (0 : ℚ) ≤ 250 * (2 : ℚ) ^ ell by positivity)
      nlinarith only [hscaled, hminorV]
    have hphiCap : (1000 : ℚ) * augmentedPhi ell
        (trace init ω w.cap) ≤ M := by
      have hm := potential_trace_le_of_domain ell hellone init ω P w.cap
        ((hPbefore.trans hsq).trans hqcap)
        (fun z hPz hzcap => potentialDomain_of_safeSparseSeed_clockHistory
          hvalid hseed H
          ((H.start_positive ell hellone
            (by have := hscale.2.1; omega)).1.trans (by
              dsimp only [P, potentialCheckpoint, warmCheckpoint] at hPz
              omega))
          (hzcap.trans_lt hcapρ))
      have hphi' : 1000 * augmentedPhi ell (trace init ω P) ≤ (M : ℚ) :=
        hphi
      linarith only [cover_phi_le_of_nat hm, hphi']
    exact Or.inl ⟨by simpa only [M] using hcredit,
      by simpa only [M] using hminorCap,
      by simpa only [M] using hphiCap⟩

/-- Successful selected hours either supply the mixed `ell + 1` barrier data or
expose the already charged N16 two-level block failure. -/
theorem receipt_near_checkpoint_data_or_failure
    {init : InputCfg n} (hvalid : validInitial init)
    (hn : timePopulationThreshold ≤ n)
    {ω : InputLog n} {S T ρ ell : ℕ} {w : ClockTimes init} {σ : Sign}
    (hseed : SafeSparseSeed init ω S)
    (H : ClockHistory init ω S T ρ w)
    (hscale : DominantScale init (trace init ω S) ell)
    (hno : ω ∉ hourFailure
      (hourSuccess init (seedTime init 3) ell σ) ell) :
    let j : Fin (PhaseThreeModel.Numeric.hourIndex n + 1) :=
      ⟨ell, by have := hscale.2.1; omega⟩
    (∃ c : ℕ, ReceiptNearCheckpointData init ω S T ρ ell σ c) ∨
      ω ∈ twoLevelBlockFailure init (w.start (ell + 1)) σ j n
        (clockCount (trace init ω S))
        (timeMainCount (trace init ω S)) := by
  let j : Fin (PhaseThreeModel.Numeric.hourIndex n + 1) :=
    ⟨ell, by have := hscale.2.1; omega⟩
  change (∃ c : ℕ, ReceiptNearCheckpointData init ω S T ρ ell σ c) ∨
    ω ∈ twoLevelBlockFailure init (w.start (ell + 1)) σ j n
      (clockCount (trace init ω S))
      (timeMainCount (trace init ω S))
  have hsc1 : 5 ≤ ell := hscale.1
  have hsc2 : ell + 2 ≤ PhaseThreeModel.Numeric.hourIndex n := hscale.2.1
  have hellone : 1 ≤ ell := by omega
  let C := clockCount (trace init ω S)
  let M := timeMainCount (trace init ω S)
  let P := potentialCheckpoint w C M ell
  let V := workCheckpoint w C M ell
  let a := w.start (ell + 1)
  let b := a + clockWarmup n C + twoLevelTrials n M
  have hsTime : seedTime init 3 ω = (S : WithTop ℕ) :=
    (seedTime_eq_iff init 3 ω S).2 hseed.1
  have hsucc := success_of_not_hourFailure
    (hourSuccess init (seedTime init 3) ell σ) hno hellone le_rfl
  have hchecks := hourChecks_of_success H (seedTime init 3) hsTime σ
    hellone (by have := hscale.2.1; omega) le_rfl hsucc
  rcases hchecks with ⟨_, _, hphi, _, hminor⟩
  have hminorV :
      (2 : ℚ) ^ ell * sideMass (oppositeSign σ) (trace init ω V) ≤
        (1 / 250 : ℚ) * M := by
    simpa only [minorityTarget,
      show ell + 4 ≠ ell by omega,
      show ell + 3 ≠ ell by omega,
      show ell + 2 ≠ ell by omega,
      show ell + 1 ≠ ell by omega,
      if_false, if_pos rfl] using hminor (by omega)
  have hnpos : 0 < n := by exact_mod_cast (time_hour_calibration hn).2.1
  have hwork : V < a := by
    simpa only [V, a] using
      (work_before_next H hnpos (h := ell + 1) (by omega)
        (by have := hscale.2.1; omega))
  have hPbefore : P ≤ a := by
    have hbud : clockWarmup n C + potentialTrials n M ≤ rawWork n M C := by
      unfold clockWarmup potentialTrials rawWork
      omega
    dsimp only [P, V, a, potentialCheckpoint, warmCheckpoint,
      workCheckpoint] at hwork hbud ⊢
    omega
  have hVbefore : V ≤ a := hwork.le
  have hbfinish : b < w.finish (ell + 1) := by
    simpa only [b, a, C, M, Nat.add_assoc] using
      (two_level_work_fits_clock_history H hn (ell + 1) (by omega))
  have hcapρ : w.cap < ρ :=
    lt_of_le_of_lt (Nat.le_add_right _ _) H.protected_settling
  have hbρ : b < ρ := hbfinish.trans
    ((H.hour_before_cap (ell + 1) (by omega)).2.trans_lt hcapρ)
  have hwindow : ∀ u, u ≤ clockWarmup n C + twoLevelTrials n M →
      TwoLevelWarmupGate σ ell n C M (trace init ω (a + u)) := by
    intro u hu
    let v := a + u
    have hav : a ≤ v := by dsimp [v]; omega
    have hvb : v ≤ b := by dsimp [v, b]; omega
    have hSv : S ≤ v :=
      (H.start_positive (ell + 1) (by omega) (by omega)).1.trans hav
    have hvρ : v < ρ := hvb.trans_lt hbρ
    have hdom := potentialDomain_of_safeSparseSeed_clockHistory
      hvalid hseed H hSv hvρ
    have hminorMono := sideMass_le_of_clockHistory (oppositeSign σ)
      hvalid hseed H
      (by
        dsimp [V, workCheckpoint]
        exact (H.start_positive ell hellone (by omega)).1.trans (by omega))
      (hVbefore.trans hav) hvρ
    have hminorDebt : minorityDebt σ (ell + 1) (trace init ω v) ≤
        (1 / 125 : ℚ) * M := by
      have hm : ∀ (τ : Sign) (c : InputCfg n),
          minorityMass τ c = sideMass (oppositeSign τ) c := by
        intro τ c
        cases τ <;> rfl
      have hnonneg : (0 : ℚ) ≤ (2 : ℚ) ^ ell := by positivity
      have hscaled := mul_le_mul_of_nonneg_left hminorMono hnonneg
      have hpow : (2 : ℚ) ^ (ell + 1) = 2 * (2 : ℚ) ^ ell := by ring
      unfold minorityDebt
      rw [hm, hpow]
      linarith only [hscaled, hminorV]
    have hclock := clockFloor_of_clockHistory H hSv hvρ (ell + 1)
      (by omega) hav (hvb.trans hbfinish.le)
    have hmain : RoleSplitConcentration.mainCount (trace init ω v) = M := by
      dsimp [M]
      convert H.main_count v hSv hvρ using 1 <;>
        simp only [RoleSplitConcentration.mainCount, timeMainCount]
    exact ⟨population_of_clockHistory H v, hdom, hmain,
      hminorDebt, hclock⟩
  have hpotential : ∀ u, u ≤ twoLevelTrials n M →
      augmentedPhi ell
          (trace init ω (a + clockWarmup n C + u)) ≤
        (1 / 1000 : ℚ) * M := by
    intro u hu
    let v := a + clockWarmup n C + u
    have hPv : P ≤ v := by dsimp [v]; omega
    have hvb : v ≤ b := by dsimp [v, b]; omega
    have hvρ : v < ρ := hvb.trans_lt hbρ
    have hm := potential_trace_le_of_domain ell hellone init ω P v hPv
      (fun z hPz hzv => potentialDomain_of_safeSparseSeed_clockHistory
        hvalid hseed H
        ((H.start_positive ell hellone (by omega)).1.trans (by
          dsimp only [P, potentialCheckpoint, warmCheckpoint] at hPz
          omega))
        (hzv.trans_lt hvρ))
    have hphi' : 1000 * augmentedPhi ell (trace init ω P) ≤ (M : ℚ) :=
      hphi
    linarith only [cover_phi_le_of_nat hm, hphi']
  by_cases hbad : twoLevelTarget M <
      twoLevelIndex σ ell M (trace init ω b)
  · apply Or.inr
    change
      (∀ u, u ≤ clockWarmup n C + twoLevelTrials n M →
        TwoLevelWarmupGate σ ell n C M (trace init ω (a + u))) ∧
      (∀ u, u ≤ twoLevelTrials n M →
        augmentedPhi ell (trace init ω (a + clockWarmup n C + u)) ≤
          (1 / 1000 : ℚ) * M) ∧
      twoLevelTarget M < twoLevelIndex σ ell M (trace init ω b)
    exact ⟨hwindow, hpotential, hbad⟩
  · apply Or.inl
    refine ⟨b, ?_⟩
    refine
      { seed_le := (H.start_positive (ell + 1) (by omega) (by omega)).1.trans
          (by dsimp [b, a]; omega)
        before_exit := hbρ
        barrier := ?_
        exception_bound := ?_
        potential_bound := ?_ }
    · simpa only [twoLevelIndex, twoLevelDebt, M] using le_of_not_gt hbad
    · simpa only [M] using
        (exceptionCount_bound_clockHistory H
          ((H.start_positive (ell + 1) (by omega) (by omega)).1.trans
            (by dsimp [b, a]; omega))
          hbρ (ell + 1) (by omega) hbfinish.le)
    · simpa only [b] using hpotential (twoLevelTrials n M) le_rfl

/-- A countable case records only fixed natural parameters.  The proof fields
ensure every selector projection satisfies the old-index interface. -/
abbrev ReceiptOldCase (n : ℕ) :=
  {z : ℕ × ℕ × ℕ //
    terminalCutoff n < z.2.1 ∧
      z.2.1 + 2 ≤ PhaseThreeModel.Numeric.hourIndex n ∧
      z.1 ≤ z.2.2}

/-- Adapted prefix data for one terminal old-index candidate.  The current
`endpointBlocksFailure` is deliberately absent. -/
def receiptOldCaseEvent (init : InputCfg n)
    (i : ReceiptOldCase n) : Set (InputLog n) :=
  {ω |
    SafeSparseSeed init ω i.val.1 ∧
    selectedSchedule init (trace init ω i.val.1) =
      (i.val.2.1, i.val.2.1) ∧
    hourPotentialEnd init (seedTime init 3)
        (i.val.2.1 - terminalCutoff n) ω =
      (i.val.2.2 : WithTop ℕ) ∧
    ω ∈ earlierSuccessBy init (seedTime init 3)
      i.val.2.1 (selectedSign init)
      (i.val.2.1 - terminalCutoff n - 1) i.val.2.2 ∧
    1000 * augmentedPhiNat (i.val.2.1 - terminalCutoff n)
        (trace init ω i.val.2.2) ≤
      timeMainCount (trace init ω i.val.1)}

theorem receiptOldCaseEvent_measurable
    (init : InputCfg n) (i : ReceiptOldCase n) :
    MeasurableSet[pairLogFiltration
      (PhaseThreeModel.Numeric.hourIndex n) 256 i.val.2.2]
      (receiptOldCaseEvent init i) := by
  let S := i.val.1
  let ell := i.val.2.1
  let s := i.val.2.2
  let r := ell - terminalCutoff n
  have hSs : S ≤ s := i.property.2.2
  have hsafe : MeasurableSet[pairLogFiltration
      (PhaseThreeModel.Numeric.hourIndex n) 256 s]
      {ω | SafeSparseSeed init ω S} :=
    (pairLogFiltration _ _).mono hSs _ (safeSparseSeed_past init S)
  have hschedule : MeasurableSet[pairLogFiltration
      (PhaseThreeModel.Numeric.hourIndex n) 256 s]
      {ω | selectedSchedule init (trace init ω S) = (ell, ell)} :=
    (pairLogFiltration _ _).mono hSs _
      (selectedSchedule_fibre_measurable init S (ell, ell))
  have hstop : MeasurableSet[pairLogFiltration
      (PhaseThreeModel.Numeric.hourIndex n) 256 s]
      {ω | hourPotentialEnd init (seedTime init 3) r ω =
        (s : WithTop ℕ)} :=
    hourPotentialEnd_pastTime init (seedTime init 3)
      (seedTime_pastTime init 3) r s
  have hearlier : MeasurableSet[pairLogFiltration
      (PhaseThreeModel.Numeric.hourIndex n) 256 s]
      (earlierSuccessBy init (seedTime init 3) ell
        (selectedSign init) (r - 1) s) :=
    earlierSuccessBy_past init (seedTime init 3)
      (seedTime_pastTime init 3) ell (selectedSign init) (r - 1) s
  have hcap : MeasurableSet[pairLogFiltration
      (PhaseThreeModel.Numeric.hourIndex n) 256 s]
      {ω | 1000 * augmentedPhiNat r (trace init ω s) ≤
        timeMainCount (trace init ω S)} := by
    have hm : MeasurableSet
        {z : InputCfg n × InputCfg n |
          1000 * augmentedPhiNat r z.2 ≤ timeMainCount z.1} :=
      (Set.to_countable _).measurableSet
    exact hm.preimage
      ((measurable_trace_at_of_le init hSs).prodMk
        (measurable_trace_at init s))
  have heq : receiptOldCaseEvent init i =
      {ω | SafeSparseSeed init ω S} ∩
        ({ω | selectedSchedule init (trace init ω S) = (ell, ell)} ∩
          ({ω | hourPotentialEnd init (seedTime init 3) r ω =
              (s : WithTop ℕ)} ∩
            (earlierSuccessBy init (seedTime init 3) ell
                (selectedSign init) (r - 1) s ∩
              {ω | 1000 * augmentedPhiNat r (trace init ω s) ≤
                timeMainCount (trace init ω S)}))) := by
    ext ω
    simp [receiptOldCaseEvent, S, ell, s, r]
  rw [heq]
  exact hsafe.inter (hschedule.inter (hstop.inter (hearlier.inter hcap)))

theorem receiptOldCaseEvent_unique
    (init : InputCfg n) {ω : InputLog n}
    {i k : ReceiptOldCase n}
    (hi : ω ∈ receiptOldCaseEvent init i)
    (hk : ω ∈ receiptOldCaseEvent init k) : i = k := by
  have hseedI := (seedTime_eq_iff init 3 ω i.val.1).2 hi.1.1
  have hseedK := (seedTime_eq_iff init 3 ω k.val.1).2 hk.1.1
  have hS : i.val.1 = k.val.1 :=
    WithTop.coe_injective (hseedI.symm.trans hseedK)
  have hschedules :
      (i.val.2.1, i.val.2.1) = (k.val.2.1, k.val.2.1) := by
    calc
      (i.val.2.1, i.val.2.1) =
          selectedSchedule init (trace init ω i.val.1) := hi.2.1.symm
      _ = selectedSchedule init (trace init ω k.val.1) := by rw [hS]
      _ = (k.val.2.1, k.val.2.1) := hk.2.1
  have hell : i.val.2.1 = k.val.2.1 := (Prod.mk.inj hschedules).1
  have hstarts : (i.val.2.2 : WithTop ℕ) = (k.val.2.2 : WithTop ℕ) := by
    calc
      (i.val.2.2 : WithTop ℕ) =
          hourPotentialEnd init (seedTime init 3)
            (i.val.2.1 - terminalCutoff n) ω := hi.2.2.1.symm
      _ = hourPotentialEnd init (seedTime init 3)
            (k.val.2.1 - terminalCutoff n) ω := by rw [hell]
      _ = (k.val.2.2 : WithTop ℕ) := hk.2.2.1
  have hs : i.val.2.2 = k.val.2.2 := WithTop.coe_injective hstarts
  apply Subtype.ext
  apply Prod.ext
  · exact hS
  · apply Prod.ext
    · exact hell
    · exact hs

open Classical in
/-- The unique adapted candidate selected by the observed prefix. -/
noncomputable def receiptOldFirstCase
    (init : InputCfg n) (ω : InputLog n) : Option (ReceiptOldCase n) :=
  if h : ∃ i, ω ∈ receiptOldCaseEvent init i then
    some (Classical.choose h)
  else none

theorem receiptOldFirstCase_eq_some_iff
    (init : InputCfg n) (i : ReceiptOldCase n) (ω : InputLog n) :
    receiptOldFirstCase init ω = some i ↔
      ω ∈ receiptOldCaseEvent init i := by
  classical
  unfold receiptOldFirstCase
  by_cases h : ∃ k, ω ∈ receiptOldCaseEvent init k
  · rw [dif_pos h]
    constructor
    · intro heq
      have hchoice : Classical.choose h = i := Option.some.inj heq
      simpa only [hchoice] using Classical.choose_spec h
    · intro hi
      have hchoice := receiptOldCaseEvent_unique init
        (Classical.choose_spec h) hi
      rw [hchoice]
  · rw [dif_neg h]
    constructor
    · intro heq
      exact (Option.some_ne_none _ heq.symm).elim
    · intro hi
      exact (h ⟨i, hi⟩).elim

/-- The concrete selector used by the deterministic cover. -/
noncomputable def receiptOldBlockSelector
    (init : InputCfg n) :
    TerminalOldBlockSelector init (ReceiptOldCase n) where
  firstCase := receiptOldFirstCase init
  seedStart := fun i => i.val.1
  blockStart := fun i => i.val.2.2
  terminalLevel := fun i => i.val.2.1
  adapted := by
    intro i
    have heq :
        {ω | receiptOldFirstCase init ω = some i} =
          receiptOldCaseEvent init i := by
      ext ω
      exact receiptOldFirstCase_eq_some_iff init i ω
    rw [heq]
    exact receiptOldCaseEvent_measurable init i
  seed_le_start := fun i => i.property.2.2
  terminal_ready := fun i => i.property.1
  safe_seed := by
    intro i ω hi
    exact ((receiptOldFirstCase_eq_some_iff init i ω).1 hi).1

/-- On the complement of the concrete old-index family, the terminal old
potential is zero at the cap checkpoint.  The proof uses
`preceding_of_success`, `PrecedingHours`, `canonical_old_workLive`, and
`canonical_terminal_old_blocks_complete`. -/
theorem receipt_old_checkpoint_zero_of_not_failure
    (init : InputCfg n) (hvalid : validInitial init)
    (hn : timePopulationThreshold ≤ n)
    {ω : InputLog n} {S T ρ ell : ℕ} {w : ClockTimes init}
    (hseed : SafeSparseSeed init ω S)
    (H : ClockHistory init ω S T ρ w)
    (hscale : DominantScale init (trace init ω S) ell)
    (hschedule : selectedSchedule init (trace init ω S) = (ell, ell))
    (hno : ω ∉ hourFailure
      (hourSuccess init (seedTime init 3) ell (selectedSign init)) ell)
    (hnot : ω ∉ oldIndexFailure (receiptOldBlockSelector init)) :
    augmentedPhiNat (ell - terminalCutoff n) (trace init ω w.cap) = 0 := by
  have hsc1 : 5 ≤ ell := hscale.1
  have hsc2 : ell + 2 ≤ PhaseThreeModel.Numeric.hourIndex n := hscale.2.1
  let seed := seedTime init 3
  let σ := selectedSign init
  let C := clockCount (trace init ω S)
  let M := timeMainCount (trace init ω S)
  have hsTime : seed ω = (S : WithTop ℕ) := by
    simpa only [seed] using (seedTime_eq_iff init 3 ω S).2 hseed.1
  have hall (j : ℕ) (hj : 1 ≤ j) (hjell : j ≤ ell) :
      hourSuccess init seed ell σ j ω := by
    apply success_of_not_hourFailure
      (hourSuccess init seed ell σ) (by simpa only [seed, σ] using hno)
      hj hjell
  have hpast : PrecedingHours init ω S w ell ell :=
    (preceding_of_success H seed hsTime (by omega) le_rfl σ
      (fun j hj hjlt => hall j hj hjlt.le)).1
  have hcapρ : w.cap < ρ :=
    lt_of_le_of_lt (Nat.le_add_right _ _) H.protected_settling
  by_cases hcut : ell ≤ terminalCutoff n
  · have hphase : ∀ a ∈ trace init ω w.cap, 3 ≤ a.phase.val :=
      fun a ha => (H.all_three w.cap H.all_before_cap hcapρ a ha).ge
    have hz := cover_augmentedPhiNat_zero_of_initialized
      (trace init ω w.cap) hphase
    simpa only [Nat.sub_eq_zero_of_le hcut] using hz
  · let q := terminalCutoff n
    let r := ell - q
    let P := potentialCheckpoint w C M r
    let W := warmCheckpoint w C ell
    have hq : 7 ≤ q := by
      simpa only [q] using terminalCutoff_ge_seven hn
    have hr : 1 ≤ r := by dsimp [r, q]; omega
    have heq : r + q = ell := by dsimp [r, q]; omega
    have hrlt : r < ell := by omega
    have hnpos : 0 < n := by exact_mod_cast (population_log_lower hn).1
    have hSP : S ≤ P := by
      have horder := checkpoint_order H hnpos r hr (by omega)
      dsimp only [P, potentialCheckpoint, warmCheckpoint, C, M]
      omega
    have hcapQ := hpast.potential r hr hrlt
    have hcapNat : 1000 * augmentedPhiNat r (trace init ω P) ≤ M := by
      have hcast :
          (1000 : ℚ) *
              (augmentedPhiNat r (trace init ω P) : ℚ) ≤
            (M : ℚ) := by
        rw [augmentedPhiNat_cast]
        exact hcapQ
      exact_mod_cast hcast
    have hcap : augmentedPhiNat r (trace init ω P) ≤ M / 1000 := by
      omega
    have hcompleted :
        ∀ j, j < r - 1 → ∀ k : Fin 5, ∃ u : ℕ,
          checkTime init seed (j + 1) k ω = (u : WithTop ℕ) ∧ u ≤ P := by
      intro j hj k
      obtain ⟨u, hu, hule⟩ :=
        checkpoints_before_next H hnpos seed hsTime (r - 1)
          (by omega) j hj k
      have hr1 : r - 1 + 1 = r := by omega
      rw [hr1] at hule
      refine ⟨u, hu, hule.trans ?_⟩
      dsimp only [P, potentialCheckpoint, warmCheckpoint, C, M]
      omega
    have hearlier :
        ω ∈ earlierSuccessBy init seed ell σ (r - 1) P := by
      unfold earlierSuccessBy
      apply (previousHoursBy_iff_of_completed init seed
        (checkTime init seed) (checkTest ell σ) ω (r - 1) P
        hcompleted).2
      intro j hj
      exact hall (j + 1) (by omega) (by omega)
    let i : ReceiptOldCase n :=
      ⟨(S, ell, P), not_le.mp hcut, hscale.2.1, hSP⟩
    have hicase : ω ∈ receiptOldCaseEvent init i := by
      refine ⟨hseed, ?_, ?_, ?_, ?_⟩
      · simpa only [i] using hschedule
      · simpa only [i, r, P, C, M, seed] using
          (hourPotentialEnd_clockHistory H seed r hsTime (by omega))
      · simpa only [i, r, P, seed, σ] using hearlier
      · simpa only [i, r, P, M] using hcapNat
    have hfirst : receiptOldFirstCase init ω = some i :=
      (receiptOldFirstCase_eq_some_iff init i ω).2 hicase
    have hwarm : ∀ j : Fin (q - 6),
        changingZeroFuel (r + 1 + j.val)
          (trace init ω (warmCheckpoint w C (r + 1 + j.val))) ≤
            (101 / 500 : ℚ) * M := by
      intro j
      have hp := hpast.warm (r + 1 + j.val) (by omega) (by omega)
      rw [old_block_previous_early (ell := ell) (h := ell)
        (j := r + 1 + j.val) (by omega) (by omega) le_rfl] at hp
      norm_num at hp
      exact hp
    have hPW : P ≤ W := by
      simpa only [P, W, C, M, heq] using
        potential_checkpoint_le_later_warm H hnpos r (r + q) hr
          (by omega) (by omega)
    have hsum : P + (W - P) = W := by omega
    have hworkLive :
        WorkLive init P r (ENNReal.ofReal (oldWorkRate n M)) Set.univ
          (M / 1000)
          (blockWork P (oldWorkTrials n M)
            (oldBlockStarts init seed r q)) (W - P) ω := by
      simpa [P, W, C, M, heq] using
        (canonical_old_workLive hvalid hseed H hn seed hsTime
          r q (M / 1000) hr hq (by omega) hcap hwarm)
    have hcomplete :
        BlocksComplete P (oldWorkTrials n M)
          (oldBlockStarts init seed r q) (W - P) ω := by
      simpa [P, W, C, M, q, heq] using
        (canonical_terminal_old_blocks_complete H hn seed hsTime r
          (by dsimp only [r, q]; omega))
    by_contra hzero
    have hzero' : augmentedPhiNat r (trace init ω w.cap) ≠ 0 := hzero
    have hpositiveCap :
        1 ≤ augmentedPhiNat r (trace init ω w.cap) := by
      omega
    have horder := checkpoint_order H hnpos ell (by omega) (by omega)
    have hWcap : W ≤ w.cap := by
      have hhour := H.hour_before_cap ell (by omega)
      dsimp only [W, warmCheckpoint, C] at horder ⊢
      omega
    have hSW : S ≤ W := by
      dsimp only [W, warmCheckpoint, C]
      exact (H.start_positive ell (by omega) (by omega)).1.trans (by omega)
    have hmono := potential_trace_le_of_domain r hr init ω W w.cap hWcap
      (fun v hWv hvcap =>
        potentialDomain_of_safeSparseSeed_clockHistory hvalid hseed H
          (hSW.trans hWv) (lt_of_le_of_lt hvcap hcapρ))
    have hpositiveW : 1 ≤ augmentedPhiNat r (trace init ω W) := by
      omega
    have hterminal :
        ω ∈ observedTerminalOldFailure init S P r
          (oldBlockStarts init seed r q)
          (hourWarmStart init seed ell) := by
      change ω ∈ endpointBlocksFailure init P r
        (ENNReal.ofReal (oldWorkRate n M)) Set.univ
        (M / 1000) (oldWorkTrials n M)
        (oldBlockStarts init seed r q)
        (hourWarmStart init seed ell)
      refine ⟨W - P, ?_, hworkLive, hcomplete, ?_⟩
      · rw [hsum]
        simpa only [W, C] using
          (hourWarmStart_clockHistory H seed ell hsTime (by omega))
      · simpa only [hsum] using hpositiveW
    have hcaseFailure :
        ω ∈ terminalOldFailureAt (receiptOldBlockSelector init) i := by
      simpa [terminalOldFailureAt, receiptOldBlockSelector, i, seed,
        r, q, P] using hterminal
    have holdmem :
        ω ∈ oldIndexFailure (receiptOldBlockSelector init) :=
      (mem_oldIndexFailure_iff (receiptOldBlockSelector init) ω).2
        ⟨i, hfirst, hcaseFailure⟩
    exact (hnot holdmem).elim

end Ripple.PopulationProtocol.ExactMajority.LateStrengthening

end
