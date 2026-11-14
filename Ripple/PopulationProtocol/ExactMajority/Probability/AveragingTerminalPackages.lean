-- Ripple/PopulationProtocol/ExactMajority/Probability/AveragingTerminalPackages.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingDominantLevelSplice
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingCheckpointReadout
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingProtectedCap
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingWorkBudget

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.AveragingTerminalPackages

open PhaseThreeClockProducer

open TimeTheorem PairLog PhaseOneDrain StageEventSpec
open AveragingSparseEntry AveragingEventInterface
open AveragingDominantLevelSplice AveragingHourEvents AveragingHourPrefix
open AveragingHourStops AveragingHourInvariant AveragingHourSchedule
open AveragingOldHourGate AveragingHourGateAssembly
open AveragingTerminalDebt AveragingTerminalDebtDeadlines
open AveragingCreditClockBridge AveragingCheckpointReadout
open AveragingPendingCredit AveragingPendingCreditTransitions
open AveragingProtectedCap AveragingWorkBudget AveragingMixedLedgers
open AveragingIntegerPotential AveragingHourFailureCover AveragingSeededDelay
open AveragingMixedAlgebra AveragingCreditCount AveragingLiveProduct AveragingClockBlocks
open AveragingPendingCredit AveragingNumerics AveragingCancellationAlgebra AveragingCreditTransitions
open AveragingFuelFloor AveragingPotentialDrift

variable {n : ℕ}

/-- Canonical cap hit, built before assuming a successful clock history. -/
def CapReached (init : InputCfg n) (S t : ℕ) (ω : InputLog n) : Prop :=
  frontCount init ω S t (clockTop n) = clockCount (trace init ω S)

open Classical in
def capSignal (init : InputCfg n) (seed : InputLog n → WithTop ℕ)
    (t : ℕ) (ω : InputLog n) : ℕ :=
  if ∃ S, S ≤ t ∧ seed ω = (S : WithTop ℕ) ∧ CapReached init S t ω
  then 1 else 0

def capTime (init : InputCfg n) (seed : InputLog n → WithTop ℕ) :
    InputLog n → WithTop ℕ :=
  hittingAfter (capSignal init seed) ({1} : Set ℕ) 0

theorem capSignal_adapted (init : InputCfg n)
    (seed : InputLog n → WithTop ℕ) (hseed : PairLogPastTime seed) :
    Adapted (pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256)
      (capSignal init seed) := by
  classical
  intro t
  have hm : MeasurableSet[pairLogFiltration
      (PhaseThreeModel.Numeric.hourIndex n) 256 t]
      {ω | ∃ S, S ≤ t ∧ seed ω = (S : WithTop ℕ) ∧
        CapReached init S t ω} := by
    rw [show {ω | ∃ S, S ≤ t ∧ seed ω = (S : WithTop ℕ) ∧
          CapReached init S t ω} =
        ⋃ S, {ω | S ≤ t ∧ seed ω = (S : WithTop ℕ) ∧
          CapReached init S t ω} by ext ω; simp]
    refine MeasurableSet.iUnion fun S => ?_
    by_cases hSt : S ≤ t
    · have hs := (pairLogFiltration _ _).mono hSt _ (hseed S)
      have hf := measurable_frontCount_at init hSt (clockTop n)
      have hc := (measurable_of_countable
        (fun c : InputCfg n => clockCount c)).comp
          (measurable_trace_at_of_le init hSt)
      have heq : MeasurableSet
          {p : ℕ × ℕ | p.1 = p.2} := (Set.to_countable _).measurableSet
      simpa only [hSt, true_and, CapReached] using
        hs.inter (heq.preimage (hf.prodMk hc))
    · simp [hSt]
  exact Measurable.ite hm measurable_const measurable_const

theorem capTime_past (init : InputCfg n)
    (seed : InputLog n → WithTop ℕ) (hseed : PairLogPastTime seed) :
    PairLogPastTime (capTime init seed) := by
  intro t
  exact ((capSignal_adapted init seed hseed).isStoppingTime_hittingAfter
    (measurableSet_singleton 1)).measurableSet_eq_of_countable t

theorem capTime_eq_clockHistory
    {init : InputCfg n} {ω : InputLog n} {S T ρ : ℕ}
    {w : ClockTimes init} (h : ClockHistory init ω S T ρ w)
    (seed : InputLog n → WithTop ℕ) (hs : seed ω = (S : WithTop ℕ)) :
    capTime init seed ω = (w.cap : WithTop ℕ) := by
  apply le_antisymm
  · change hittingAfter (capSignal init seed) ({1} : Set ℕ) 0 ω ≤ _
    apply (hittingAfter_le_iff).2
    refine ⟨w.cap, ⟨Nat.zero_le _, le_rfl⟩, ?_⟩
    simp only [capSignal, Set.mem_singleton_iff]
    rw [if_pos]
    exact ⟨S, h.cap_first.1, hs, h.cap_first.2.1⟩
  · by_contra hnot
    have hlt : capTime init seed ω < (w.cap : WithTop ℕ) := lt_of_not_ge hnot
    change hittingAfter (capSignal init seed) ({1} : Set ℕ) 0 ω < _ at hlt
    obtain ⟨v, hv, hmem⟩ := hittingAfter_lt_iff.mp hlt
    simp only [Set.mem_singleton_iff] at hmem
    have hit : ∃ R, R ≤ v ∧ seed ω = (R : WithTop ℕ) ∧
        CapReached init R v ω := by
      by_contra hne
      unfold capSignal at hmem
      rw [if_neg hne] at hmem
      exact absurd hmem (by norm_num)
    obtain ⟨R, hRv, hR, hreach⟩ := hit
    have hRS : R = S := WithTop.coe_injective (hR.symm.trans hs)
    subst R
    exact h.cap_first.2.2 v hRv hv.2 hreach

theorem hourChecks_of_success
    {init : InputCfg n} {ω : InputLog n} {S T ρ ell h : ℕ}
    {w : ClockTimes init} (H : ClockHistory init ω S T ρ w)
    (seed : InputLog n → WithTop ℕ) (hseed : seed ω = (S : WithTop ℕ))
    (σ : Sign) (hh : 1 ≤ h) (hL : h ≤ PhaseThreeModel.Numeric.hourIndex n)
    (hle : h ≤ ell)
    (hsuccess : hourSuccess init seed ell σ h ω) :
    CurrentHourChecks σ init ω S w ell h := by
  let C := clockCount (trace init ω S)
  let M := timeMainCount (trace init ω S)
  let W := warmCheckpoint w C h
  let P := potentialCheckpoint w C M h
  let V := workCheckpoint w C M h
  have hw := hourWarmStart_clockHistory H seed h hseed hL
  have hp := hourPotentialEnd_clockHistory H seed h hseed hL
  have hv := hourWorkEnd_clock H seed hseed h hL
  have key := fun (i : Fin 5) (u : ℕ)
      (hu : checkTime init seed h i ω = (u : WithTop ℕ)) =>
    observed_value init seed (checkTime init seed h i) (checkTest ell σ h i)
      ω S u hseed hu (hsuccess i)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have := key ⟨0, by decide⟩ W (by simpa [checkTime] using hw)
    simpa [checkTest] using this
  · have := key ⟨1, by decide⟩ W (by simpa [checkTime] using hw)
    simpa [checkTest] using this
  · have := key ⟨2, by decide⟩ P (by simpa [checkTime] using hp)
    simpa [checkTest] using this
  · have := key ⟨3, by decide⟩ V (by simpa [checkTime] using hv)
    simpa [checkTest] using this
  · intro h4
    have := key ⟨4, by decide⟩ V (by simpa [checkTime] using hv)
    simpa [checkTest, h4, hle] using this

theorem success_of_not_hourFailure
    {Ω : Type*} (good : ℕ → Ω → Prop) {ω : Ω} {N h : ℕ}
    (hnot : ω ∉ hourFailure good N) (hh : 1 ≤ h) (hN : h ≤ N) :
    good h ω := by
  by_contra hbad
  apply hnot
  exact ⟨h - 1, by omega, by simpa only [Nat.sub_add_cancel hh]⟩

private theorem history_data
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

private theorem signed_mass_of_winning
    {init : InputCfg n} (hvalid : validInitial init) {ω : InputLog n} {S T ρ v : ℕ}
    {w : ClockTimes init} (H : ClockHistory init ω S T ρ w)
    (hSv : S ≤ v) (hvρ : v < ρ) (σ : Sign)
    (hw : winningSign init σ) :
    prePhase4MassSum (trace init ω v) =
      if σ = .pos then (gapMagnitude init : ℚ) else -(gapMagnitude init : ℚ) := by
  have hm := trace_mixedSigned_eq_initialGap init hvalid ω v
    (fun a ha => by have := (H.phase_range v hSv hvρ a ha).2; omega)
  cases σ with
  | pos =>
      have hp : 0 < initialGap init := hw
      rw [if_pos rfl, hm]
      have h2 : (initialGap init : ℤ) = ((initialGap init).natAbs : ℤ) := by omega
      unfold gapMagnitude
      first
        | exact_mod_cast h2
        | simpa using congrArg (fun z : ℤ => (z : ℚ)) h2
  | neg =>
      have hn : initialGap init < 0 := hw
      rw [if_neg (by decide : Sign.neg ≠ Sign.pos), hm]
      have h2 : (initialGap init : ℤ) = -((initialGap init).natAbs : ℤ) := by omega
      unfold gapMagnitude
      first
        | exact_mod_cast h2
        | simpa using congrArg (fun z : ℤ => (z : ℚ)) h2

private theorem seed_clock_main_le_card (c : InputCfg n) :
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

private theorem terminal_window_before_finish
    {init : InputCfg n} {ω : InputLog n} {S T ρ ell : ℕ}
    {w : ClockTimes init} (H : ClockHistory init ω S T ρ w)
    (hn : timePopulationThreshold ≤ n)
    (hell : ell + 2 ≤ PhaseThreeModel.Numeric.hourIndex n) :
    let C := clockCount (trace init ω S)
    let M := timeMainCount (trace init ω S);
      w.start (ell + 2) + (clockWarmup n C + majorityWork n M) <
      w.finish (ell + 2) := by
  intro C M
  have hST := clockHistory_seed_lt_exit H
  have hd := H.density S le_rfl (lt_of_le_of_lt hST.1 hST.2)
  have hnpos : 0 < n := by have := (time_population_bounds hn).2; omega
  have hC : 0 < C := by dsimp [C]; omega
  have hM : 0 < M := by dsimp [M]; omega
  have hcard : (trace init ω S).card = n := by
    exact H.entry.seed_profile.card_eq
  have hCM : C + M ≤ n := by
    have h2 := seed_clock_main_le_card (trace init ω S)
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

private theorem phi_le_of_nat {h : ℕ} {c d : InputCfg n}
    (hm : augmentedPhiNat h c ≤ augmentedPhiNat h d) :
    augmentedPhi h c ≤ augmentedPhi h d := by
  have := (Nat.cast_le (α := ℚ)).mpr hm
  rwa [augmentedPhiNat_cast, augmentedPhiNat_cast] at this

/-- The successful hour induction either already gives the literal small-gap
 readout or produces the exact `terminalFailure` charged later. -/
theorem small_readout_or_terminalFailure
    {init : InputCfg n} (hvalid : validInitial init)
    (hn : timePopulationThreshold ≤ n)
    {ω : InputLog n} {S T ρ ell : ℕ} {w : ClockTimes init}
    (hseed : SafeSparseSeed init ω S)
    (H : ClockHistory init ω S T ρ w)
    (hgap : 0 < gapMagnitude init)
    (hsmall : 40 * gapMagnitude init < timeMainCount (trace init ω S))
    (hscale : DominantScale init (trace init ω S) ell)
    (hno : ω ∉ hourFailure
      (hourSuccess init (seedTime init 3) ell (selectedSign init)) ell) :
    SmallReadout init (timeMainCount (trace init ω S)) ell
        (selectedSign init) (trace init ω ρ) ∨
      ω ∈ terminalFailure init (w.start (ell + 2)) (selectedSign init) ell
        ((2 / 125 : ℚ) * timeMainCount (trace init ω S)) n
        (clockCount (trace init ω S)) (timeMainCount (trace init ω S)) := by
  have hell1 : 1 ≤ ell := by have := hscale.1; omega
  let σ := selectedSign init
  let C := clockCount (trace init ω S)
  let M := timeMainCount (trace init ω S)
  let W := warmCheckpoint w C ell
  let P := potentialCheckpoint w C M ell
  let V := workCheckpoint w C M ell
  let s := w.start (ell + 2)
  let q := s + (clockWarmup n C + majorityWork n M)
  have hsucc := success_of_not_hourFailure
    (hourSuccess init (seedTime init 3) ell σ) hno (by have := hell1; omega) le_rfl
  have hsTime : seedTime init 3 ω = (S : WithTop ℕ) :=
    (seedTime_eq_iff init 3 ω S).2 hseed.1
  have hc := hourChecks_of_success H (seedTime init 3) hsTime σ
    (by have := hell1; omega) (by have := hscale.2.1; omega) le_rfl hsucc
  rcases hc with ⟨hfuel, _, hphi, _, hminor⟩
  have hminorV :
      (2 : ℚ) ^ ell * sideMass (oppositeSign σ) (trace init ω V) ≤
        (1 / 250 : ℚ) * M := by
    simpa only [minorityTarget, show ell + 4 ≠ ell by omega,
      show ell + 3 ≠ ell by omega, show ell + 2 ≠ ell by omega,
      show ell + 1 ≠ ell by omega, if_false, if_pos rfl] using
        hminor (by omega)
  have hwork : workCheckpoint w C M ell < w.start (ell + 1) := by
    have := work_before_next H (by exact_mod_cast (time_hour_calibration hn).2.1)
      (h := ell + 1) (by omega) (by have := hscale.2.1; omega)
    simpa using this
  have hmono := clockHistory_start_mono H
    (by exact_mod_cast (time_hour_calibration hn).2.1)
    (ell + 1) (ell + 2) (by omega) hscale.2.1
  have hbud : clockWarmup n C + potentialTrials n M ≤ rawWork n M C := by
    unfold clockWarmup potentialTrials rawWork
    omega
  have hPbefore : P ≤ s := by
    dsimp only [P, V, s, potentialCheckpoint, workCheckpoint, warmCheckpoint] at hwork hbud ⊢
    omega
  have hVbefore : V ≤ s := by
    dsimp only [V, s, workCheckpoint] at hwork ⊢
    omega
  have hfinish := terminal_window_before_finish H hn hscale.2.1
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
      hvalid hseed H (by
        dsimp [V, workCheckpoint]
        exact (H.start_positive ell hell1 (by have := hscale.2.1; omega)).1.trans (by omega))
      (hVbefore.trans hsv) hvρ
    have hminorDebt : minorityDebt σ (ell + 2) (trace init ω v) ≤
        (2 / 125 : ℚ) * M := by
      have hmm : ∀ (τ : Sign) (c : InputCfg n),
          minorityMass τ c = sideMass (oppositeSign τ) c := by
        intro τ c
        cases τ <;> rfl
      have h2 : (0 : ℚ) ≤ (2 : ℚ) ^ ell := by positivity
      have h3 := mul_le_mul_of_nonneg_left hminorMono h2
      have e : (2 : ℚ) ^ (ell + 2) = 4 * (2 : ℚ) ^ ell := by ring
      unfold minorityDebt
      rw [hmm, e]
      have hV : (2 : ℚ) ^ ell * sideMass (oppositeSign σ) (trace init ω V) ≤
          (1 / 250 : ℚ) * M := hminorV
      linarith only [h3, hV]
    have hphiV : augmentedPhi ell (trace init ω v) ≤ (1 / 1000 : ℚ) * M := by
      have hm := potential_trace_le_of_domain ell hell1 init ω P v (hPbefore.trans hsv)
        (fun z hPz hzv => potentialDomain_of_safeSparseSeed_clockHistory
          hvalid hseed H
          ((H.start_positive ell hell1 (by have := hscale.2.1; omega)).1.trans (by
            dsimp only [P, potentialCheckpoint, warmCheckpoint] at hPz; omega))
          (hzv.trans_lt hvρ))
      have hphi' : 1000 * augmentedPhi ell (trace init ω P) ≤ (M : ℚ) := hphi
      linarith only [phi_le_of_nat hm, hphi']
    have hclock := clockFloor_of_clockHistory H hSv hvρ (ell + 2)
      hscale.2.1 hsv (hvq.trans hqfinish.le)
    have hmain : RoleSplitConcentration.mainCount (trace init ω v) = M := by
      dsimp [M]
      convert H.main_count v hSv hvρ using 1 <;>
        simp only [RoleSplitConcentration.mainCount, timeMainCount]
    have hsigned := signed_mass_of_winning hvalid H hSv hvρ σ
      (selectedSign_winning init hgap)
    have hy := yGate_with_canonical_partners σ ell
      (debtX σ (ell + 2) (trace init ω v)) (gapMagnitude init)
      n M (trace init ω v)
      (population_of_clockHistory H v) hdom le_rfl (by omega)
      hmain hsigned (by
        have hs : (2 : ℚ) * M ≤ 5 * (2 : ℚ) ^ ell * gapMagnitude init := by
          exact_mod_cast hscale.2.2.1
        nlinarith only [hs]) hphiV
    exact ⟨population_of_clockHistory H v, hdom, hmain,
      hminorDebt, hclock, hy.partners⟩
  by_cases hbad : ω ∈ terminalFailure init s σ ell
      ((2 / 125 : ℚ) * M) n C M
  · exact Or.inr hbad
  · have hY : debtY σ (ell + 2) (trace init ω q) ≤ (7 / 200 : ℚ) * M := by
      by_contra hlarge
      apply hbad
      exact ⟨hgate, lt_of_not_ge hlarge⟩
    have hphiQ : augmentedPhi ell (trace init ω q) ≤ (1 / 1000 : ℚ) * M := by
      have hm := potential_trace_le_of_domain ell hell1 init ω P q
        (hPbefore.trans (by dsimp [q, s]; omega))
        (fun z hPz hzq => potentialDomain_of_safeSparseSeed_clockHistory
          hvalid hseed H
          ((H.start_positive ell hell1 (by have := hscale.2.1; omega)).1.trans (by
            dsimp only [P, potentialCheckpoint, warmCheckpoint] at hPz; omega))
          (hzq.trans_lt hqρ))
      have hphi' : 1000 * augmentedPhi ell (trace init ω P) ≤ (M : ℚ) := hphi
      linarith only [phi_le_of_nat hm, hphi']
    have hcreditQ := initial_mixed_credit_clockHistory H hSq hqρ σ ell
      hscale.2.1 hqfinish.le hY hphiQ
    have hqcap : q ≤ w.cap :=
      hqfinish.le.trans (H.hour_before_cap (ell + 2) hscale.2.1).2
    have hcapρ : w.cap < ρ :=
      lt_of_le_of_lt (Nat.le_add_right _ _) H.protected_settling
    have hdata := history_data hvalid hseed H hSq hqcap hcapρ
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
      have hm := sideMass_le_of_clockHistory (oppositeSign σ) hvalid hseed H
        (by
          dsimp [V, workCheckpoint]
          exact (H.start_positive ell hell1 (by have := hscale.2.1; omega)).1.trans (by omega))
        ((hVbefore.trans hsq).trans hqcap) hcapρ
      have hs := mul_le_mul_of_nonneg_left hm
        (show (0 : ℚ) ≤ 250 * (2 : ℚ) ^ ell by positivity)
      nlinarith only [hs, hminorV]
    have hphiCap : (1000 : ℚ) * augmentedPhi ell
        (trace init ω w.cap) ≤ M := by
      have hm := potential_trace_le_of_domain ell hell1 init ω P w.cap
        ((hPbefore.trans hsq).trans hqcap)
        (fun z hPz hzcap => potentialDomain_of_safeSparseSeed_clockHistory
          hvalid hseed H
          ((H.start_positive ell hell1 (by have := hscale.2.1; omega)).1.trans (by
            dsimp only [P, potentialCheckpoint, warmCheckpoint] at hPz; omega))
          (hzcap.trans_lt hcapρ))
      have hphi' : 1000 * augmentedPhi ell (trace init ω P) ≤ (M : ℚ) := hphi
      linarith only [phi_le_of_nat hm, hphi']
    exact Or.inl (smallReadout_at_first_exit_of_checkpoint hvalid H
      H.all_before_cap hcapρ rfl (selectedSign_winning init hgap) hgap hsmall
      hscale.1 hscale.2.1 hscale.2.2.1 hscale.2.2.2
      hcredit hminorCap hphiCap)

private theorem exceptionCount_top_eq_zero
    (c : Cfg (PhaseThreeModel.Numeric.hourIndex n) 256) :
    exceptionCount (PhaseThreeModel.Numeric.hourIndex n) c = 0 := by
  classical
  induction c using Multiset.induction_on with
  | empty => simp [exceptionCount]
  | cons a c ih =>
      have hw : exceptionWeight (PhaseThreeModel.Numeric.hourIndex n) a = 0 := by
        unfold exceptionWeight
        by_cases hmain : a.role = .main ∧ ¬ a.phase.val < 3
        · rw [if_pos hmain]
          cases hb : a.bias with
          | zero =>
              simp only [hb]
              exact if_neg (by have := a.hour.isLt; omega)
          | dyadic σ j =>
              simp only [hb]
              exact if_neg (by have := j.isLt; omega)
        · rw [if_neg hmain]
      unfold exceptionCount at ih ⊢
      rw [Multiset.map_cons, Multiset.sum_cons, hw, zero_add]
      exact ih

/-- Hour `L` produces both the cap potential and the persistent ready-zero
 floor required by `tie_readout_failure_on_protected_cap`. -/
theorem tie_cap_package
    {init : InputCfg n} (hvalid : validInitial init)
    (hn : timePopulationThreshold ≤ n)
    {ω : InputLog n} {S T ρ : ℕ} {w : ClockTimes init}
    (hseed : SafeSparseSeed init ω S)
    (H : ClockHistory init ω S T ρ w)
    (hgap : initialGap init = 0)
    (hno : ω ∉ hourFailure
      (hourSuccess init (seedTime init 3)
        (PhaseThreeModel.Numeric.hourIndex n + 5) (selectedSign init))
      (PhaseThreeModel.Numeric.hourIndex n)) :
    let M := timeMainCount (trace init ω S);
      capTime init (seedTime init 3) ω = (w.cap : WithTop ℕ) ∧
      1000 * augmentedPhiNat (PhaseThreeModel.Numeric.hourIndex n)
        (trace init ω w.cap) ≤ M ∧
      (∀ v, w.cap ≤ v → v < w.cap + logWindow n 16 →
        CapGate n M (PhaseThreeModel.Numeric.hourIndex n) (trace init ω v)) := by
  let L := PhaseThreeModel.Numeric.hourIndex n
  let ell := L + 5
  let C := clockCount (trace init ω S)
  let M := timeMainCount (trace init ω S)
  let W := warmCheckpoint w C L
  let P := potentialCheckpoint w C M L
  have hL : 1 ≤ L := cap_index_pos hn
  have hsTime : seedTime init 3 ω = (S : WithTop ℕ) :=
    (seedTime_eq_iff init 3 ω S).2 hseed.1
  have hsucc := success_of_not_hourFailure
    (hourSuccess init (seedTime init 3) ell (selectedSign init)) hno hL le_rfl
  have hc := hourChecks_of_success H (seedTime init 3) hsTime
    (selectedSign init) hL le_rfl (by omega) hsucc
  rcases hc with ⟨hfuel, _, hphi, _, _⟩
  have hcapEq := capTime_eq_clockHistory H (seedTime init 3) hsTime
  have hcapρ : w.cap < ρ :=
    lt_of_le_of_lt (Nat.le_add_right _ _) H.protected_settling
  have hn0 : 0 < n := by exact_mod_cast (time_hour_calibration hn).2.1
  have hord : w.start L + clockWarmup n C + potentialTrials n M < w.finish L :=
    (checkpoint_order H hn0 L hL le_rfl).2.1
  have hfc := (H.hour_before_cap L le_rfl).2
  have hPcap : P ≤ w.cap := by
    dsimp only [P, potentialCheckpoint, warmCheckpoint]
    omega
  have hphiCapQ : (1000 : ℚ) * augmentedPhi L (trace init ω w.cap) ≤ M := by
    have hm := potential_trace_le_of_domain L hL init ω P w.cap hPcap
      (fun z hPz hzcap => potentialDomain_of_safeSparseSeed_clockHistory
        hvalid hseed H
        ((H.start_positive L hL le_rfl).1.trans (by
          dsimp only [P, potentialCheckpoint, warmCheckpoint] at hPz; omega))
        (hzcap.trans_lt hcapρ))
    have hphi' : 1000 * augmentedPhi L (trace init ω P) ≤ (M : ℚ) := hphi
    linarith only [phi_le_of_nat hm, hphi']
  have hphaseCap : ∀ a ∈ trace init ω w.cap, 3 ≤ a.phase.val :=
    fun a ha => (H.all_three w.cap H.all_before_cap hcapρ a ha).ge
  have hnatcast : (augmentedPhiNat L (trace init ω w.cap) : ℚ) =
      augmentedPhi L (trace init ω w.cap) :=
    augmentedPhiNat_cast L (trace init ω w.cap)
  have hphiNat : 1000 * augmentedPhiNat L (trace init ω w.cap) ≤ M := by
    have h' : (1000 : ℚ) * (augmentedPhiNat L (trace init ω w.cap) : ℚ) ≤ M := by
      rw [hnatcast]; exact hphiCapQ
    exact_mod_cast h'
  refine ⟨hcapEq, hphiNat, ?_⟩
  intro v hcapv hv
  have hSv : S ≤ v :=
    (H.cap_first.1.trans hcapv)
  have hvρ : v < ρ := hv.trans_le H.protected_settling.le
  have hdom := potentialDomain_of_safeSparseSeed_clockHistory
    hvalid hseed H hSv hvρ
  have hWv : W ≤ v := by
    dsimp only [W, warmCheckpoint]
    omega
  have hfuelV := fuel_trace_le_of_domain L init ω W v hWv
    (fun z hWz hzv => potentialDomain_of_safeSparseSeed_clockHistory
      hvalid hseed H
      ((H.start_positive L hL le_rfl).1.trans (by
        dsimp only [W, warmCheckpoint] at hWz; omega))
      (hzv.trans_lt hvρ))
  have hfuelBound : changingZeroFuel L (trace init ω v) ≤ (101 / 500 : ℚ) * M := by
    dsimp [W, ell, L, M] at hfuel
    rw [totalPrevious_early hL (by omega)] at hfuel
    norm_num at hfuel
    exact hfuelV.trans hfuel
  have hmain : RoleSplitConcentration.mainCount (trace init ω v) = M := by
    dsimp [M]
    convert H.main_count v hSv hvρ using 1 <;>
      simp only [RoleSplitConcentration.mainCount, timeMainCount]
  have hfloor := mainCount_le_fuel_zero_exception L (trace init ω v)
  rw [hmain, exceptionCount_top_eq_zero (trace init ω v)] at hfloor
  have hready := exactZeroCount_le_readyZeroCount L L le_rfl (trace init ω v) hdom
  have hreadyQ : (77 / 100 : ℝ) * M ≤
      (readyZeroCount L (trace init ω v) : ℝ) := by
    have hfq : changingZeroFuel L (trace init ω v) ≤ (101 / 500 : ℚ) * M := hfuelBound
    have hq : (399 / 500 : ℚ) * M ≤ exactZeroCount L (trace init ω v) := by
      push_cast at hfloor
      linarith only [hfloor, hfq]
    have hr : (399 / 500 : ℝ) * M ≤
        (exactZeroCount L (trace init ω v) : ℝ) := by
      have h2 := (Rat.cast_le (K := ℝ)).mpr hq
      push_cast at h2
      exact h2
    have hcast : (exactZeroCount L (trace init ω v) : ℝ) ≤
        readyZeroCount L (trace init ω v) := by exact_mod_cast hready
    have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg _
    linarith only [hr, hcast, hM0]
  exact ⟨population_of_clockHistory H v, hdom, hreadyQ⟩

end Ripple.PopulationProtocol.ExactMajority.AveragingTerminalPackages

end
