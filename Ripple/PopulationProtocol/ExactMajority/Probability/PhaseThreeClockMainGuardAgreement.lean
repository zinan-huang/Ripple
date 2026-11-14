-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockMainGuardAgreement.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockMainGuardSeed
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockHourGeometry

/-!
# Guarded agreement through the first credit barrier

The pfx process agrees with the path credit and the current Clock front before the
first credit barrier.  The accepted candidate at that first barrier is stored in a
`stopped` state.  The first-small and age barriers cannot stop the process earlier on
the guarded passage window.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockMainGuardAgreement

open TimeTheorem PairLog PairLogAuxiliary StageEventSpec
  PhaseThreeClockProducer PhaseThreeClockSeedTails PhaseThreeClockVirtual
  PhaseThreeClockGatedLaw PhaseThreeClockGatedLevelOne
  PhaseThreeClockEmbeddingBridge PhaseThreeClockMainPath
  PhaseThreeClockMainProcess PhaseThreeClockMainProcessIncrement
  PhaseThreeClockMainProcessDrift PhaseThreeClockMainPairCounts
  PhaseThreeClockMainGuardSeed PhaseThreeClockRawLocalRow
  PhaseThreeClockHourOccupancyRow PhaseThreeClockPassageOrderRows
  PhaseThreeClockHourGeometry PhaseThreeClockCore
open PhaseThreeModel.Numeric

variable {n : ℕ} (init : InputCfg n)

structure MainCreditFirst (ω : InputLog n) (h σ : ℕ)
    (seed : MainSeed init) (τ : ℕ) : Prop where
  lower : σ ≤ τ
  hit : 3 * mainSeedM init seed ≤ 2500 * credit init ω h σ τ
  before : ∀ u, σ ≤ u → u < τ →
    2500 * credit init ω h σ u < 3 * mainSeedM init seed

structure MainLiveAgreement (ω : InputLog n) (h σ u : ℕ)
    (seed : MainSeed init) (data : MainLive init h) : Prop where
  seed_eq : data.seed = seed
  age_eq : data.age = u - σ
  credit_eq : data.credit = credit init ω h σ u
  front_eq : data.front =
    frontCount (virtualLabels init ω u) (mainLevel h)
  value_eq : data.value = mainLiveValue init seed (u - σ)
    (credit init ω h σ u)
    (frontCount (virtualLabels init ω u) (mainLevel h))

/-! ## Endpoint arithmetic -/

theorem smallThreshold_pos (seed : MainSeed init) :
    1 ≤ smallThreshold (mainSeedC init seed) := by
  have hlarge := seed.2.clock_large
  unfold smallThreshold mainSeedC
  omega

theorem smallThreshold_le_bulkThreshold (C : ℕ) :
    smallThreshold C ≤ bulkThreshold C := by
  have hdiv : C / 1000 ≤ C / 10 :=
    Nat.div_le_div_left (by norm_num : 10 ≤ 1000) (by norm_num : 0 < 10)
  have hcast : ((C / 10 : ℕ) : ℝ) ≤ (C : ℝ) / 10 := Nat.cast_div_le
  have hceil : (C : ℝ) / 10 ≤ (Nat.ceil ((C : ℝ) / 10) : ℝ) := Nat.le_ceil _
  have hnat : C / 10 ≤ Nat.ceil ((C : ℝ) / 10) := by
    exact_mod_cast hcast.trans hceil
  exact hdiv.trans hnat

theorem guardedFinish_le_bulk
    {ω : InputLog n} {S h finish bulk : ℕ}
    (hfinish : firstAfter
      (fun v => smallThreshold (clockCount (virtualCfg init ω S)) ≤
        frontCountL init (virtualLabels init ω S)
          (virtualLabels init ω v) (mainLevel h)) S finish)
    (hbulk : firstAfter
      (fun v => bulkThreshold (clockCount (virtualCfg init ω S)) ≤
        frontCountL init (virtualLabels init ω S)
          (virtualLabels init ω v) (mainLevel h)) S bulk) :
    finish ≤ bulk :=
  firstAfter_le_of_holds hfinish hbulk.1
    ((smallThreshold_le_bulkThreshold (clockCount (virtualCfg init ω S))).trans
      hbulk.2.1)

theorem guardedFirst_le_finish
    {ω : InputLog n} {S h σ finish : ℕ}
    (hpositive : 1 ≤ smallThreshold (clockCount (virtualCfg init ω S)))
    (hfirst : firstAfter
      (fun v => 1 ≤ frontCountL init (virtualLabels init ω S)
        (virtualLabels init ω v) (mainLevel h)) S σ)
    (hfinish : firstAfter
      (fun v => smallThreshold (clockCount (virtualCfg init ω S)) ≤
        frontCountL init (virtualLabels init ω S)
          (virtualLabels init ω v) (mainLevel h)) S finish) :
    σ ≤ finish :=
  firstAfter_le_of_holds hfirst hfinish.1
    (hpositive.trans hfinish.2.1)

theorem guardedAge_le_window
    {σ finish bulk u : ℕ} (hu : u ≤ finish) (hfb : finish ≤ bulk)
    (hlocal : bulk - σ ≤ logWindow n 30) :
    u - σ ≤ logWindow n 30 := by
  omega

/-! ## Candidate atoms agree with the path observables -/

theorem mainPairCredit_eq_stepCredit
    {ω : InputLog n} {h t : ℕ} (data : MainLive init h)
    (hlab : data.lab = virtualLabels init ω t) :
    mainPairCredit init h data.lab (drawLabels init ω (t + 1)) =
      stepCredit init ω h t := by
  cases hd : drawLabels init ω (t + 1) with
  | none => simp [mainPairCredit, stepCredit, hd]
  | some pair =>
      rcases pair with ⟨i, j⟩
      simp [mainPairCredit, stepCredit, hd, hlab]

theorem mainNextCredit_eq_guardedCredit
    {ω : InputLog n} {h σ t : ℕ} (data : MainLive init h)
    (hσt : σ ≤ t) (hlab : data.lab = virtualLabels init ω t)
    (hcredit : data.credit = credit init ω h σ t) :
    mainNextCredit init data (drawLabels init ω (t + 1)) =
      credit init ω h σ (t + 1) := by
  unfold mainNextCredit
  rw [hcredit, mainPairCredit_eq_stepCredit init data hlab,
    credit_succ init ω h σ t hσt]

theorem mainNextFront_eq_guardedFront
    {ω : InputLog n} {S T h t : ℕ} (hentry : AsyncEntry init ω S T)
    (hh : h ≤ hourIndex n) (hSt : S ≤ t) (data : MainLive init h)
    (hlab : data.lab = virtualLabels init ω t)
    (hfront : data.front = frontCount (virtualLabels init ω t) (mainLevel h)) :
    mainNextFront init data (drawLabels init ω (t + 1)) =
      frontCount (virtualLabels init ω (t + 1)) (mainLevel h) := by
  cases hd : drawLabels init ω (t + 1) with
  | none =>
      unfold mainNextFront
      rw [hfront]
      simp only [mainPairRaising, hd]
      rw [frontCount_virtualLabels_succ_of_none init ω t hd]
      try rfl
  | some pair =>
      rcases pair with ⟨i, j⟩
      unfold mainNextFront
      rw [hfront, hlab]
      rw [frontCount_virtualLabels_succ_of_asyncEntry init ω S T hentry t hSt
        i j hd (mainLevel h) (mainLevel_pos h) (mainLevel_le_clockCap hh)]
      simp only [mainPairRaising, hd]

/-! ## Live agreement -/

theorem mainProcessState_live_before_credit
    (hn : populationThreshold ≤ n)
    {ω : InputLog n} {S T h σ finish bulk τ u : ℕ}
    (hentry : AsyncEntry init ω S T) (hh : h ≤ hourIndex n)
    (hfirst : firstAfter
      (fun v => 1 ≤ frontCountL init (virtualLabels init ω S)
        (virtualLabels init ω v) (mainLevel h)) S σ)
    (hfinish : firstAfter
      (fun v => smallThreshold (clockCount (virtualCfg init ω S)) ≤
        frontCountL init (virtualLabels init ω S)
          (virtualLabels init ω v) (mainLevel h)) S finish)
    (hbulk : firstAfter
      (fun v => bulkThreshold (clockCount (virtualCfg init ω S)) ≤
        frontCountL init (virtualLabels init ω S)
          (virtualLabels init ω v) (mainLevel h)) S bulk)
    (hlocal : bulk - σ ≤ logWindow n 30)
    (hτ : MainCreditFirst init ω h σ
      (guardedMainSeed init ω S T hn hentry) τ)
    (hτfinish : τ ≤ finish) (hσu : σ ≤ u) (huτ : u < τ) :
    ∃ data : MainLive init h,
      mainProcessState init h u ω = .live data ∧
      MainLiveAgreement init ω h σ u
        (guardedMainSeed init ω S T hn hentry) data := by
  induction u, hσu using Nat.le_induction with
  | base =>
      obtain ⟨data, hstate, hseed, hage, hcredit, hfront, hvalue⟩ :=
        mainProcessState_at_firstPositive init hn hentry hh hfirst
      refine ⟨data, hstate, ?_⟩
      refine
        { seed_eq := hseed
          age_eq := by simpa only [Nat.sub_self] using hage
          credit_eq := by simpa only [credit_self] using hcredit
          front_eq := by
            rw [hfront]
            exact (firstPositive_currentFront_eq_one init hentry hh hfirst).symm
          value_eq := ?_ }
      simpa only [Nat.sub_self, credit_self,
        firstPositive_currentFront_eq_one init hentry hh hfirst] using hvalue
  | succ u hσu ih =>
      have hSσ : S ≤ σ := hfirst.1
      have huτ : u < τ := by omega
      obtain ⟨data, hstate, hagree⟩ := ih huτ
      have hlab := mainProcessState_lab init h u ω
      rw [hstate] at hlab
      change data.lab = virtualLabels init ω u at hlab
      have hcreditNext := mainNextCredit_eq_guardedCredit init data hσu hlab
        hagree.credit_eq
      have hfrontNext := mainNextFront_eq_guardedFront init hentry hh
        (hfirst.1.trans hσu) data hlab hagree.front_eq
      have hacceptedGlobal := guardedMainAcceptedCondition init hn hentry hfirst
        (show σ ≤ u + 1 by omega)
      have haccepted : MainAcceptedCondition init h data.seed
          (virtualLabels init ω (u + 1))
          (mainNextCredit init data (drawLabels init ω (u + 1)))
          (mainNextFront init data (drawLabels init ω (u + 1))) := by
        rw [hagree.seed_eq, hcreditNext, hfrontNext]
        exact hacceptedGlobal
      have hcreditSmall :
          2500 * credit init ω h σ (u + 1) <
            3 * mainSeedM init
              (guardedMainSeed init ω S T hn hentry) :=
        hτ.before (u + 1) (by omega) (by omega)
      have hrowSmall :
          frontCountL init (virtualLabels init ω S)
            (virtualLabels init ω (u + 1)) (mainLevel h) <
              smallThreshold (clockCount (virtualCfg init ω S)) := by
        by_contra hnot
        exact hfinish.2.2 (u + 1) (by omega) (by omega) (by omega)
      have hseedPrefix : ω ∈ seedPrefix init S :=
        ⟨(seedTime_eq_iff init 3 ω S).2 hentry.first_phase_seed,
          hentry.seed_profile⟩
      have hfrontSmall :
          frontCount (virtualLabels init ω (u + 1)) (mainLevel h) <
            smallThreshold
              (mainSeedC init (guardedMainSeed init ω S T hn hentry)) := by
        have hcur :
            frontCount (virtualLabels init ω (u + 1)) (mainLevel h) <
              smallThreshold (clockCount (virtualCfg init ω S)) := by
          simpa only [core_front_eq_current_of_asyncEntry init ω S T (u + 1)
            (mainLevel h) hseedPrefix hentry (by omega)] using hrowSmall
        rw [guardedMainSeedC_eq]
        simpa only [virtualCfg_eq_trace_at_seedPrefix init ω S hseedPrefix] using hcur
      have hfinishBulk := guardedFinish_le_bulk init hfinish hbulk
      have hageNext : mainNextAge init data = u + 1 - σ := by
        unfold mainNextAge
        rw [hagree.age_eq]
        omega
      have hageSmall : u + 1 - σ < logWindow n 30 := by
        have huFinish : u + 1 < finish := by omega
        omega
      have hnotStop : ¬ mainStop init data.seed
          (mainNextAge init data)
          (mainNextCredit init data (drawLabels init ω (u + 1)))
          (mainNextFront init data (drawLabels init ω (u + 1))) := by
        rw [hagree.seed_eq, hageNext, hcreditNext, hfrontNext]
        intro hstop
        rcases hstop with hbad | hbad | hbad
        · omega
        · omega
        · omega
      have hcreditSmallData :
          2500 * mainNextCredit init data (drawLabels init ω (u + 1)) <
            3 * mainSeedM init data.seed := by
        rw [hagree.seed_eq, hcreditNext]
        exact hcreditSmall
      have hfrontSmallData :
          mainNextFront init data (drawLabels init ω (u + 1)) <
            smallThreshold (mainSeedC init data.seed) := by
        rw [hagree.seed_eq, hfrontNext]
        exact hfrontSmall
      have hageSmallData : mainNextAge init data < logWindow n 30 := by
        rw [hageNext]
        exact hageSmall
      let next : MainLive init h :=
        { seed := data.seed
          lab := virtualLabels init ω (u + 1)
          age := mainNextAge init data
          credit := mainNextCredit init data (drawLabels init ω (u + 1))
          front := mainNextFront init data (drawLabels init ω (u + 1))
          value := mainNextValue init data (drawLabels init ω (u + 1))
          valid :=
            { accepted := haccepted
              credit_small := hcreditSmallData
              front_small := hfrontSmallData
              age_small := hageSmallData
              value_eq := rfl } }
      have htransition :
          mainProcessState init h (u + 1) ω = .live next := by
        rw [mainProcessState_succ, hstate]
        simp only [mainProcessStep]
        classical
        unfold mainLiveStep
        dsimp only
        rw [dif_pos haccepted, dif_neg hnotStop]
      refine ⟨next, htransition, ?_⟩
      refine
        { seed_eq := hagree.seed_eq
          age_eq := ?_
          credit_eq := ?_
          front_eq := ?_
          value_eq := ?_ }
      · dsimp only [next]
        exact hageNext
      · dsimp only [next]
        exact hcreditNext
      · dsimp only [next]
        exact hfrontNext
      · dsimp only [next]
        unfold mainNextValue
        rw [hagree.seed_eq, hageNext, hcreditNext, hfrontNext]

/-! ## The retained first barrier and subsequent freeze -/

theorem mainProcessState_stopped_at_credit
    (hn : populationThreshold ≤ n)
    {ω : InputLog n} {S T h σ finish bulk τ : ℕ}
    (hentry : AsyncEntry init ω S T) (hh : h ≤ hourIndex n)
    (hfirst : firstAfter
      (fun v => 1 ≤ frontCountL init (virtualLabels init ω S)
        (virtualLabels init ω v) (mainLevel h)) S σ)
    (hfinish : firstAfter
      (fun v => smallThreshold (clockCount (virtualCfg init ω S)) ≤
        frontCountL init (virtualLabels init ω S)
          (virtualLabels init ω v) (mainLevel h)) S finish)
    (hbulk : firstAfter
      (fun v => bulkThreshold (clockCount (virtualCfg init ω S)) ≤
        frontCountL init (virtualLabels init ω S)
          (virtualLabels init ω v) (mainLevel h)) S bulk)
    (hlocal : bulk - σ ≤ logWindow n 30)
    (hτ : MainCreditFirst init ω h σ
      (guardedMainSeed init ω S T hn hentry) τ)
    (hτfinish : τ ≤ finish) :
    mainProcessState init h τ ω =
      .stopped (mainLiveValue init
        (guardedMainSeed init ω S T hn hentry) (τ - σ)
        (credit init ω h σ τ)
        (frontCount (virtualLabels init ω τ) (mainLevel h))) := by
  have hστ : σ < τ := by
    by_contra hnot
    have hlow := hτ.lower
    have heq : τ = σ := by omega
    have hhit := hτ.hit
    rw [heq, credit_self] at hhit
    have hM := mainSeed_main_pos init
      (guardedMainSeed init ω S T hn hentry)
    omega
  have hpred : σ ≤ τ - 1 := by omega
  have hpredlt : τ - 1 < τ := by omega
  obtain ⟨data, hstate, hagree⟩ :=
    mainProcessState_live_before_credit init hn hentry hh hfirst hfinish hbulk
      hlocal hτ hτfinish hpred hpredlt
  have hlab := mainProcessState_lab init h (τ - 1) ω
  rw [hstate] at hlab
  change data.lab = virtualLabels init ω (τ - 1) at hlab
  have hsucc : τ - 1 + 1 = τ := by omega
  have hcreditNext := mainNextCredit_eq_guardedCredit init data hpred hlab
    hagree.credit_eq
  have hfrontNext := mainNextFront_eq_guardedFront init hentry hh
    (hfirst.1.trans hpred) data hlab hagree.front_eq
  have hacceptedGlobal := guardedMainAcceptedCondition init hn hentry hfirst
    hτ.lower
  have haccepted : MainAcceptedCondition init h data.seed
      (virtualLabels init ω τ)
      (mainNextCredit init data (drawLabels init ω τ))
      (mainNextFront init data (drawLabels init ω τ)) := by
    rw [hsucc] at hcreditNext hfrontNext
    rw [hagree.seed_eq, hcreditNext, hfrontNext]
    exact hacceptedGlobal
  have hageNext : mainNextAge init data = τ - σ := by
    unfold mainNextAge
    rw [hagree.age_eq]
    omega
  have hstop : mainStop init data.seed
      (mainNextAge init data)
      (mainNextCredit init data (drawLabels init ω τ))
      (mainNextFront init data (drawLabels init ω τ)) := by
    apply Or.inl
    rw [hsucc] at hcreditNext
    rw [hagree.seed_eq, hcreditNext]
    exact hτ.hit
  have hsuccState := mainProcessState_succ init h (τ - 1) ω
  rw [hsucc] at hsuccState
  rw [hsuccState, hstate]
  simp only [mainProcessStep]
  classical
  unfold mainLiveStep
  dsimp only
  rw [dif_pos haccepted, dif_pos hstop]
  unfold mainNextValue
  rw [hsucc] at hcreditNext hfrontNext
  rw [hagree.seed_eq, hageNext, hcreditNext, hfrontNext]

theorem mainProcessState_stopped_mono
    (h : ℕ) (ω : InputLog n) {u v : ℕ} {value : ℝ}
    (hstate : mainProcessState init h u ω = .stopped value)
    (huv : u ≤ v) :
    mainProcessState init h v ω = .stopped value := by
  induction v, huv using Nat.le_induction with
  | base => exact hstate
  | succ v huv ih =>
      rw [mainProcessState_succ, ih]
      rfl

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockMainGuardAgreement

end
