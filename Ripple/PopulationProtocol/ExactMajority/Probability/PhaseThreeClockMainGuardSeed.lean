-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockMainGuardSeed.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockMainProcessDrift
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockMainExponent
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockRegime
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockHourOccupancyRow
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockPassageOrderRows

/-!
# Guarded initialization of the killed Main process

The genuine first Phase-3 seed is recognized by the pfx recursion.  Before the
first positive Clock front at level `256 (h+1)`, the process is waiting, the Main
ledger is zero, and the Clock front is zero.  At the first positive front, the unit
front law gives front exactly one and the process enters its live state.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockMainGuardSeed

open TimeTheorem PairLog PairLogAuxiliary StageEventSpec
  PhaseThreeClockProducer PhaseThreeClockSeedTails PhaseThreeClockVirtual
  PhaseThreeClockGatedLaw PhaseThreeClockEmbeddingBridge
  PhaseThreeClockMainLedger PhaseThreeClockMainPath
  PhaseThreeClockMainProcess PhaseThreeClockMainProcessIncrement
  PhaseThreeClockMainProcessDrift PhaseThreeClockMainPairCounts
  PhaseThreeClockMainTerminal PhaseThreeClockRawLocalRow PhaseThreeClockCore
  PhaseThreeClockActivationSeed PhaseThreeClockHourOccupancyRow
  PhaseThreeClockPassageOrderRows PhaseThreeClockRegime
open PhaseThreeModel.Numeric

variable {n : ℕ} (init : InputCfg n)

/-! ## The exact seed carried by the pfx process -/

def guardedMainSeedData (ω : InputLog n) (S : ℕ) : MainSeedData init :=
  { time := S
    labels := virtualLabels init ω S
    cfg := trace init ω S }

theorem guardedMainSeed_admissible
    (hn : populationThreshold ≤ n) {ω : InputLog n} {S T : ℕ}
    (hentry : AsyncEntry init ω S T) :
    MainSeedAdmissible init (guardedMainSeedData init ω S) := by
  have hseed : ω ∈ seedPrefix init S :=
    ⟨(seedTime_eq_iff init 3 ω S).2 hentry.first_phase_seed,
      hentry.seed_profile⟩
  have hdensity := seed_density init ω hentry
  have hpower := power_le_of_threshold hn
  have hsmall : (50000 : ℝ) ≤ (1000 : ℝ) ^ 2 := by norm_num
  have hmono : (1000 : ℝ) ^ 2 ≤ (1000 : ℝ) ^ 100 :=
    pow_le_pow_right₀ (by norm_num) (by norm_num)
  have hnReal : (50000 : ℝ) ≤ (n : ℝ) := hsmall.trans (hmono.trans hpower)
  have hnLarge : 50000 ≤ n := by exact_mod_cast hnReal
  have hclockLarge : 2000 ≤ clockCount (trace init ω S) := by
    omega
  refine
    { cfg_eq := ?_
      profile := hentry.seed_profile
      card_eq := seedPrefix_card_eq init ω S hseed
      main_lower := hdensity.1
      main_upper := hdensity.2.1
      clock_lower := hdensity.2.2.1
      clock_upper := hdensity.2.2.2.1
      clock_large := hclockLarge }
  change virtualCfg init ω S = trace init ω S
  exact virtualCfg_eq_trace_at_seedPrefix init ω S hseed

noncomputable def guardedMainSeed
    (ω : InputLog n) (S T : ℕ) (hn : populationThreshold ≤ n)
    (hentry : AsyncEntry init ω S T) : MainSeed init :=
  ⟨guardedMainSeedData init ω S,
    guardedMainSeed_admissible init hn hentry⟩

@[simp] theorem guardedMainSeed_time
    (ω : InputLog n) (S T : ℕ) (hn : populationThreshold ≤ n)
    (hentry : AsyncEntry init ω S T) :
    (guardedMainSeed init ω S T hn hentry).1.time = S := rfl

@[simp] theorem guardedMainSeed_labels
    (ω : InputLog n) (S T : ℕ) (hn : populationThreshold ≤ n)
    (hentry : AsyncEntry init ω S T) :
    (guardedMainSeed init ω S T hn hentry).1.labels =
      virtualLabels init ω S := rfl

@[simp] theorem guardedMainSeed_cfg
    (ω : InputLog n) (S T : ℕ) (hn : populationThreshold ≤ n)
    (hentry : AsyncEntry init ω S T) :
    (guardedMainSeed init ω S T hn hentry).1.cfg = trace init ω S := rfl

@[simp] theorem guardedMainSeedM_eq
    (ω : InputLog n) (S T : ℕ) (hn : populationThreshold ≤ n)
    (hentry : AsyncEntry init ω S T) :
    mainSeedM init (guardedMainSeed init ω S T hn hentry) =
      timeMainCount (trace init ω S) := rfl

@[simp] theorem guardedMainSeedC_eq
    (ω : InputLog n) (S T : ℕ) (hn : populationThreshold ≤ n)
    (hentry : AsyncEntry init ω S T) :
    mainSeedC init (guardedMainSeed init ω S T hn hentry) =
      clockCount (trace init ω S) := rfl

theorem main_logWindow_pos (seed : MainSeed init) :
    0 < logWindow n 30 := by
  unfold logWindow
  apply Nat.ceil_pos.mpr
  have hnTwo := mainSeed_two_le_population init seed
  have hnReal : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos hnReal
  positivity

/-! ## Seed state -/

theorem guardedMainWaitingCondition_at_seed
    (hn : populationThreshold ≤ n) {ω : InputLog n} {S T h : ℕ}
    (hentry : AsyncEntry init ω S T) :
    MainWaitingCondition init h
      (guardedMainSeed init ω S T hn hentry)
      (virtualLabels init ω S) := by
  have hseed : ω ∈ seedPrefix init S :=
    ⟨(seedTime_eq_iff init 3 ω S).2 hentry.first_phase_seed,
      hentry.seed_profile⟩
  have hsums := sums_zero_of_mainFieldsLe init h (virtualLabels init ω S)
    (mainFieldsLe_seed init ω hentry h)
  refine
    { environment :=
        virtualLabels_clockEnvironment_of_asyncEntry init ω S T hentry S le_rfl
      roles := ?_
      front_zero := ?_
      vertical_zero := hsums.1
      hour_zero := hsums.2 }
  · intro i
    rfl
  · exact current_positive_front_zero_at_seed init ω S (mainLevel h) hseed
      (mainLevel_pos h)

theorem noExactPhaseThree_before_seed
    {ω : InputLog n} {S T t : ℕ} (hentry : AsyncEntry init ω S T)
    (ht : t < S) : ¬ HasExactPhaseThree (trace init ω t) := by
  rintro ⟨a, ha, hphase⟩
  have hlt := hentry.first_phase_seed.2 t ht a ha
  omega

theorem mainProcessState_before_seed
    {ω : InputLog n} {S T h t : ℕ} (hentry : AsyncEntry init ω S T)
    (ht : t < S) :
    mainProcessState init h t ω = .dormant := by
  revert ht
  induction t with
  | zero =>
      intro ht
      have hno := noExactPhaseThree_before_seed init hentry ht
      unfold mainProcessState
      simp only [mainPrefixState]
      classical
      simp only [mainMakeSeedState]
      rw [if_neg (by simpa only [trace] using hno)]
  | succ t ih =>
      intro ht
      have hprev : t < S := by omega
      have hno := noExactPhaseThree_before_seed init hentry ht
      rw [mainProcessState_succ, ih hprev]
      simp only [mainProcessStep]
      classical
      simp only [mainMakeSeedState]
      rw [if_neg (by simpa only [trace] using hno)]

theorem mainProcessState_at_seed
    (hn : populationThreshold ≤ n) {ω : InputLog n} {S T h : ℕ}
    (hentry : AsyncEntry init ω S T) :
    ∃ data : MainWaiting init h,
      mainProcessState init h S ω = .waiting data ∧
      data.seed = guardedMainSeed init ω S T hn hentry ∧
      data.lab = virtualLabels init ω S := by
  let raw := guardedMainSeedData init ω S
  have hadmissible : MainSeedAdmissible init raw := by
    simpa only [raw] using guardedMainSeed_admissible init hn hentry
  let seed : MainSeed init := ⟨raw, hadmissible⟩
  have hseedEq : seed = guardedMainSeed init ω S T hn hentry := by
    apply Subtype.ext
    rfl
  have hvalid : MainWaitingCondition init h seed (virtualLabels init ω S) := by
    simpa only [hseedEq] using guardedMainWaitingCondition_at_seed init hn hentry
  let data : MainWaiting init h :=
    { seed := seed
      lab := virtualLabels init ω S
      valid := hvalid }
  have hphase : HasExactPhaseThree (trace init ω S) := by
    obtain ⟨a, ha, hp⟩ := hentry.first_phase_seed.1
    exact ⟨a, ha, hp⟩
  have hmake :
      mainMakeSeedState init h S (virtualLabels init ω S) (trace init ω S) =
        .waiting data := by
    classical
    simp only [mainMakeSeedState]
    rw [if_pos hphase]
    change (if admissible : MainSeedAdmissible init raw then
      (let candidate : MainSeed init := ⟨raw, admissible⟩
       if waiting : MainWaitingCondition init h candidate
          (virtualLabels init ω S) then
         MainProcessState.waiting
           { seed := candidate
             lab := virtualLabels init ω S
             valid := waiting }
       else MainProcessState.killed 0)
      else MainProcessState.killed 0) = .waiting data
    rw [dif_pos hadmissible]
    change (if waiting : MainWaitingCondition init h seed
        (virtualLabels init ω S) then
      MainProcessState.waiting
        { seed := seed
          lab := virtualLabels init ω S
          valid := waiting }
      else MainProcessState.killed 0) = .waiting data
    rw [dif_pos hvalid]
  refine ⟨data, ?_, hseedEq, rfl⟩
  cases S with
  | zero =>
      unfold mainProcessState
      simp only [mainPrefixState]
      simpa only [trace] using hmake
  | succ S =>
      rw [mainProcessState_succ,
        mainProcessState_before_seed init hentry (Nat.lt_succ_self S)]
      simpa only [mainProcessStep, trace] using hmake

/-! ## Before the first positive front -/

theorem currentFront_zero_before_first
    {ω : InputLog n} {S T h σ u : ℕ}
    (hentry : AsyncEntry init ω S T)
    (hfirst : firstAfter
      (fun v => 1 ≤ frontCountL init (virtualLabels init ω S)
        (virtualLabels init ω v) (mainLevel h)) S σ)
    (hSu : S ≤ u) (huσ : u < σ) :
    frontCount (virtualLabels init ω u) (mainLevel h) = 0 := by
  have hrow :
      frontCountL init (virtualLabels init ω S)
        (virtualLabels init ω u) (mainLevel h) = 0 := by
    have hnot : ¬ 1 ≤ frontCountL init (virtualLabels init ω S)
        (virtualLabels init ω u) (mainLevel h) :=
      fun hhit => hfirst.2.2 u hSu huσ hhit
    omega
  simpa only [core_front_eq_current_of_asyncEntry init ω S T u
    (mainLevel h) (by
      exact ⟨(seedTime_eq_iff init 3 ω S).2 hentry.first_phase_seed,
        hentry.seed_profile⟩) hentry hSu] using hrow

theorem noHighClock_before_first
    {ω : InputLog n} {S T h σ u : ℕ}
    (hentry : AsyncEntry init ω S T)
    (hfirst : firstAfter
      (fun v => 1 ≤ frontCountL init (virtualLabels init ω S)
        (virtualLabels init ω v) (mainLevel h)) S σ)
    (hSu : S ≤ u) (huσ : u < σ) :
    NoHighClock init h (virtualLabels init ω u) := by
  intro i hclock hactive
  by_contra hminute
  have hi : i ∈ aboveSet (virtualLabels init ω u) (mainLevel h) := by
    simp only [aboveSet, Finset.mem_filter, Finset.mem_univ, true_and,
      hclock, effMinute, if_pos hactive]
    unfold mainLevel at hminute ⊢
    omega
  have hpos : 0 < frontCount (virtualLabels init ω u) (mainLevel h) :=
    Finset.card_pos.mpr ⟨i, hi⟩
  rw [currentFront_zero_before_first init hentry hfirst hSu huσ] at hpos
  omega

theorem mainFields_before_first
    {ω : InputLog n} {S T h σ u : ℕ}
    (hentry : AsyncEntry init ω S T)
    (hfirst : firstAfter
      (fun v => 1 ≤ frontCountL init (virtualLabels init ω S)
        (virtualLabels init ω v) (mainLevel h)) S σ)
    (hSu : S ≤ u) (huσ : u ≤ σ) :
    ∀ i, MainFieldsLe h (virtualLabels init ω u i) := by
  exact mainFieldsLe_of_noHighClock init ω hentry h σ hfirst.1
    (mainFieldsLe_seed init ω hentry h)
    (fun t hSt ht => noHighClock_before_first init hentry hfirst hSt ht)
    u hSu huσ

theorem mainSums_zero_at_first
    {ω : InputLog n} {S T h σ : ℕ}
    (hentry : AsyncEntry init ω S T)
    (hfirst : firstAfter
      (fun v => 1 ≤ frontCountL init (virtualLabels init ω S)
        (virtualLabels init ω v) (mainLevel h)) S σ) :
    vSum init h (virtualLabels init ω σ) = 0 ∧
      hSum init h (virtualLabels init ω σ) = 0 :=
  sums_zero_of_mainFieldsLe init h (virtualLabels init ω σ)
    (mainFields_before_first init hentry hfirst hfirst.1 le_rfl)

theorem guardedMainWaitingCondition_before_first
    (hn : populationThreshold ≤ n) {ω : InputLog n} {S T h σ u : ℕ}
    (hentry : AsyncEntry init ω S T)
    (hfirst : firstAfter
      (fun v => 1 ≤ frontCountL init (virtualLabels init ω S)
        (virtualLabels init ω v) (mainLevel h)) S σ)
    (hSu : S ≤ u) (huσ : u < σ) :
    MainWaitingCondition init h
      (guardedMainSeed init ω S T hn hentry)
      (virtualLabels init ω u) := by
  have hsums := sums_zero_of_mainFieldsLe init h (virtualLabels init ω u)
    (mainFields_before_first init hentry hfirst hSu huσ.le)
  refine
    { environment :=
        virtualLabels_clockEnvironment_of_asyncEntry init ω S T hentry u hSu
      roles := ?_
      front_zero := currentFront_zero_before_first init hentry hfirst hSu huσ
      vertical_zero := hsums.1
      hour_zero := hsums.2 }
  intro i
  change (virtualLabels init ω u i).role =
    (virtualLabels init ω S i).role
  have hu := virtualLabels_roles_fixed_of_asyncEntry init ω S T hentry u hSu i
  have hS := virtualLabels_roles_fixed_of_asyncEntry init ω S T hentry S le_rfl i
  exact hu.trans hS.symm

theorem mainProcessState_waiting_before_first
    (hn : populationThreshold ≤ n) {ω : InputLog n} {S T h σ u : ℕ}
    (hentry : AsyncEntry init ω S T)
    (hfirst : firstAfter
      (fun v => 1 ≤ frontCountL init (virtualLabels init ω S)
        (virtualLabels init ω v) (mainLevel h)) S σ)
    (hSu : S ≤ u) (huσ : u < σ) :
    ∃ data : MainWaiting init h,
      mainProcessState init h u ω = .waiting data ∧
      data.seed = guardedMainSeed init ω S T hn hentry ∧
      data.lab = virtualLabels init ω u := by
  induction u, hSu using Nat.le_induction with
  | base =>
      obtain ⟨data, hstate, hseed, hlab⟩ :=
        mainProcessState_at_seed init hn hentry
      exact ⟨data, hstate, hseed, hlab⟩
  | succ u hSu ih =>
      have huσ : u < σ := by omega
      obtain ⟨data, hstate, hseed, hlab⟩ := ih huσ
      have hzero := currentFront_zero_before_first init hentry hfirst
        (by omega : S ≤ u + 1) (by omega : u + 1 < σ)
      have hvalid := guardedMainWaitingCondition_before_first init hn hentry hfirst
        (by omega : S ≤ u + 1) (by omega : u + 1 < σ)
      have hvalidData : MainWaitingCondition init h data.seed
          (virtualLabels init ω (u + 1)) := by
        simpa only [hseed] using hvalid
      let next : MainWaiting init h :=
        { seed := data.seed
          lab := virtualLabels init ω (u + 1)
          valid := hvalidData }
      refine ⟨next, ?_, hseed, rfl⟩
      rw [mainProcessState_succ, hstate]
      simp only [mainProcessStep]
      have hfront : mainWaitingFront init h (virtualLabels init ω (u + 1)) = 0 := by
        simpa only [mainWaitingFront] using hzero
      classical
      unfold mainWaitingStep
      dsimp only
      rw [if_pos hfront, dif_pos hvalidData]

/-! ## Unit first hit and live start -/

theorem firstThreshold_front_eq
    {ω : InputLog n} {S T ell b v : ℕ}
    (hentry : AsyncEntry init ω S T)
    (hell : 1 ≤ ell) (hcap : ell ≤ clockTop n) (hb : 1 ≤ b)
    (hfirst : firstAfter
      (fun t => b ≤ frontCountL init (virtualLabels init ω S)
        (virtualLabels init ω t) ell) S v) :
    frontCountL init (virtualLabels init ω S)
      (virtualLabels init ω v) ell = b := by
  have hseed : ω ∈ seedPrefix init S :=
    ⟨(seedTime_eq_iff init 3 ω S).2 hentry.first_phase_seed,
      hentry.seed_profile⟩
  have hSv0 : S ≤ v := hfirst.1
  have hSv : S < v := by
    by_contra hnot
    have heq : v = S := by omega
    have hzero := core_positive_front_zero_at_seed init ω S T ell hseed hentry hell
    have hhit := hfirst.2.1
    rw [heq, hzero] at hhit
    omega
  have hpred : S ≤ v - 1 := by omega
  have hsucc : v - 1 + 1 = v := by omega
  have hbelow :
      frontCountL init (virtualLabels init ω S)
        (virtualLabels init ω (v - 1)) ell < b := by
    by_contra hnot
    exact hfirst.2.2 (v - 1) hpred (by omega) (by omega)
  have hstep := core_front_step_bounds_of_asyncEntry init ω S T ell (v - 1)
    hseed hentry hell hcap hpred
  have hupper :
      frontCountL init (virtualLabels init ω S)
        (virtualLabels init ω v) ell ≤ b := by
    rw [← hsucc]
    omega
  exact Nat.le_antisymm hupper hfirst.2.1

theorem firstPositive_currentFront_eq_one
    {ω : InputLog n} {S T h σ : ℕ}
    (hentry : AsyncEntry init ω S T) (hh : h ≤ hourIndex n)
    (hfirst : firstAfter
      (fun v => 1 ≤ frontCountL init (virtualLabels init ω S)
        (virtualLabels init ω v) (mainLevel h)) S σ) :
    frontCount (virtualLabels init ω σ) (mainLevel h) = 1 := by
  have hseed : ω ∈ seedPrefix init S :=
    ⟨(seedTime_eq_iff init 3 ω S).2 hentry.first_phase_seed,
      hentry.seed_profile⟩
  have hrow := firstThreshold_front_eq init hentry (mainLevel_pos h)
    (mainLevel_le_clockCap hh) (by norm_num) hfirst
  simpa only [core_front_eq_current_of_asyncEntry init ω S T σ
    (mainLevel h) hseed hentry hfirst.1] using hrow

theorem guardedMainAcceptedCondition
    (hn : populationThreshold ≤ n) {ω : InputLog n} {S T h σ u : ℕ}
    (hentry : AsyncEntry init ω S T)
    (hfirst : firstAfter
      (fun v => 1 ≤ frontCountL init (virtualLabels init ω S)
        (virtualLabels init ω v) (mainLevel h)) S σ)
    (hσu : σ ≤ u) :
    MainAcceptedCondition init h
      (guardedMainSeed init ω S T hn hentry)
      (virtualLabels init ω u)
      (credit init ω h σ u)
      (frontCount (virtualLabels init ω u) (mainLevel h)) := by
  have hzero := mainSums_zero_at_first init hentry hfirst
  have hsums := sums_le_of_credit init ω hentry h σ u hfirst.1 hσu
  refine
    { environment :=
        virtualLabels_clockEnvironment_of_asyncEntry init ω S T hentry u
          (hfirst.1.trans hσu)
      roles := ?_
      front_eq := rfl
      vertical_le := ?_
      hour_le := ?_ }
  · intro i
    change (virtualLabels init ω u i).role =
      (virtualLabels init ω S i).role
    have hu := virtualLabels_roles_fixed_of_asyncEntry init ω S T hentry u
      (hfirst.1.trans hσu) i
    have hS := virtualLabels_roles_fixed_of_asyncEntry init ω S T hentry S le_rfl i
    exact hu.trans hS.symm
  · rw [hzero.1, zero_add] at hsums
    exact hsums.1
  · rw [hzero.2, zero_add] at hsums
    exact hsums.2

theorem guardedMainStartCondition
    (hn : populationThreshold ≤ n) {ω : InputLog n} {S T h σ : ℕ}
    (hentry : AsyncEntry init ω S T) (hh : h ≤ hourIndex n)
    (hfirst : firstAfter
      (fun v => 1 ≤ frontCountL init (virtualLabels init ω S)
        (virtualLabels init ω v) (mainLevel h)) S σ) :
    MainStartCondition init h
      (guardedMainSeed init ω S T hn hentry)
      (virtualLabels init ω σ) 1
      (mainStartValue init (guardedMainSeed init ω S T hn hentry) 1) := by
  let seed := guardedMainSeed init ω S T hn hentry
  have hfront := firstPositive_currentFront_eq_one init hentry hh hfirst
  have haccepted := guardedMainAcceptedCondition init hn hentry hfirst
    (show σ ≤ σ from le_rfl)
  have haccepted' : MainAcceptedCondition init h seed
      (virtualLabels init ω σ) 0 1 := by
    simpa only [seed, credit_self, hfront] using haccepted
  have hM := mainSeed_main_pos init seed
  have hC := seed.2.clock_large
  refine
    { front_one := rfl
      live :=
        { accepted := haccepted'
          credit_small := by
            have hM' := mainSeed_main_pos init (guardedMainSeed init ω S T hn hentry)
            omega
          front_small := by
            have hC' := (guardedMainSeed init ω S T hn hentry).2.clock_large
            unfold smallThreshold mainSeedC
            omega
          age_small := main_logWindow_pos init seed
          value_eq := rfl } }

theorem mainProcessState_at_firstPositive
    (hn : populationThreshold ≤ n) {ω : InputLog n} {S T h σ : ℕ}
    (hentry : AsyncEntry init ω S T) (hh : h ≤ hourIndex n)
    (hfirst : firstAfter
      (fun v => 1 ≤ frontCountL init (virtualLabels init ω S)
        (virtualLabels init ω v) (mainLevel h)) S σ) :
    ∃ data : MainLive init h,
      mainProcessState init h σ ω = .live data ∧
      data.seed = guardedMainSeed init ω S T hn hentry ∧
      data.age = 0 ∧ data.credit = 0 ∧ data.front = 1 ∧
      data.value = mainLiveValue init
        (guardedMainSeed init ω S T hn hentry) 0 0 1 := by
  have hfront := firstPositive_currentFront_eq_one init hentry hh hfirst
  have hseed : ω ∈ seedPrefix init S :=
    ⟨(seedTime_eq_iff init 3 ω S).2 hentry.first_phase_seed,
      hentry.seed_profile⟩
  have hseedZero := current_positive_front_zero_at_seed init ω S
    (mainLevel h) hseed (mainLevel_pos h)
  have hSσ0 : S ≤ σ := hfirst.1
  have hSσ : S < σ := by
    by_contra hnot
    have heq : σ = S := by omega
    rw [heq, hseedZero] at hfront
    omega
  have hpred : S ≤ σ - 1 := by omega
  have hpredlt : σ - 1 < σ := by omega
  obtain ⟨waiting, hstate, hseedEq, hlab⟩ :=
    mainProcessState_waiting_before_first init hn hentry hfirst hpred hpredlt
  have hsucc : σ - 1 + 1 = σ := by omega
  have hstart := guardedMainStartCondition init hn hentry hh hfirst
  have hstartData : MainStartCondition init h waiting.seed
      (virtualLabels init ω σ) 1
      (mainStartValue init waiting.seed 1) := by
    simpa only [hseedEq] using hstart
  let live : MainLive init h :=
    { seed := waiting.seed
      lab := virtualLabels init ω σ
      age := 0
      credit := 0
      front := 1
      value := mainStartValue init waiting.seed 1
      valid := hstartData.live }
  have htransition :
      mainWaitingStep init h waiting (virtualLabels init ω σ) = .live live := by
    classical
    unfold mainWaitingStep
    dsimp only
    have hwf : mainWaitingFront init h (virtualLabels init ω σ) = 1 := by
      simpa only [mainWaitingFront] using hfront
    simp only [hwf, one_ne_zero, if_false]
    rw [dif_pos hstartData]
  refine ⟨live, ?_, hseedEq, rfl, rfl, rfl, ?_⟩
  have hsuccState := mainProcessState_succ init h (σ - 1) ω
  rw [hsucc] at hsuccState
  rw [hsuccState, hstate]
  simpa only [mainProcessStep] using htransition
  dsimp only [live]
  unfold mainStartValue
  rw [hseedEq]

theorem mainProcessY_zero (h : ℕ) (ω : InputLog n) :
    mainProcessY init h 0 ω = 0 := by
  unfold mainProcessY mainProcessState
  simp only [mainPrefixState]
  exact mainMakeSeedState_value_zero init h 0
    (auxPrefix init virtualRule 0 (frestrictLe 0 ω))
    (prefixCfg init 0 (frestrictLe 0 ω))

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockMainGuardSeed

end
