-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockMainBarrier.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockMainGuardAgreement
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockMainDiscount
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockMainHourReduction

/-!
# The guarded Main failure forces the retained terminal barrier

A row violation cannot occur before the first positive high Clock, because both Main
ledger sums are then zero.  At and after that first positive time, the path ledger
bounds both row observables by the accumulated credit.  The first credit barrier is
therefore no later than the violating time and no later than `finish h`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockMainBarrier

open TimeTheorem PairLog StageEventSpec PhaseThreeClockProducer
  PhaseThreeClockSeedTails PhaseThreeClockVirtual PhaseThreeClockCore
  PhaseThreeClockRows PhaseThreeClockRowsGuarded
  PhaseThreeClockMainLedger PhaseThreeClockMainPath
  PhaseThreeClockMainAlgebra PhaseThreeClockMainTerminal
  PhaseThreeClockMainProcess PhaseThreeClockMainProcessIncrement
  PhaseThreeClockMainGuardSeed PhaseThreeClockMainGuardAgreement
  PhaseThreeClockMainPairCounts
  PhaseThreeClockMainHourReduction PhaseThreeClockRawLocalRow
  PhaseThreeClockHourOccupancyRow PhaseThreeClockHourGeometry
open PhaseThreeModel.Numeric

variable {n : ℕ} (init : InputCfg n)

/-- Rewrite lemma for the large set-builder failure event. -/
theorem mem_guardedMainHourFailure_iff
    (h : ℕ) (ω : InputLog n) :
    ω ∈ guardedMainHourFailure init h ↔
      ∃ S T : ℕ,
        seedTime init 3 ω = (S : WithTop ℕ) ∧
        T ≤ earlyHorizon n ∧
        AsyncEntry init ω S T ∧
        guardMain init ω S T ∧
        h ≤ hourIndex n ∧
        MainHourViolation init h S ω :=
  Iff.rfl

/-- Either Main-row inequality forces a credit-barrier witness after the first
positive high Clock and no later than `finish h`. -/
theorem mainHourViolation_credit_witness
    {ω : InputLog n} {S T h σ : ℕ}
    (hentry : AsyncEntry init ω S T)
    (hfirst : firstAfter
      (fun v => 1 ≤ frontCountL init (virtualLabels init ω S)
        (virtualLabels init ω v) (mainLevel h)) S σ)
    (hbad : MainHourViolation init h S ω) :
    ∃ v, σ ≤ v ∧ v ≤ (virtualTimes init ω S).finish h ∧
      3 * timeMainCount (virtualCfg init ω S) ≤
        2500 * credit init ω h σ v := by
  have hzero := mainSums_zero_at_first init hentry hfirst
  rcases hbad with hbad | hbad
  · obtain ⟨v, hSv, hvFinish, hstrict⟩ := hbad
    have hσv : σ ≤ v := by
      by_contra hnot
      have hfields := mainFields_before_first init hentry hfirst hSv (by omega)
      have hsums := sums_zero_of_mainFieldsLe init h (virtualLabels init ω v) hfields
      have heq := highHourMainsL_eq_hSum init ω hentry h v hSv
      rw [heq, hsums.2] at hstrict
      omega
    have hsums := sums_le_of_credit init ω hentry h σ v hfirst.1 hσv
    have hhour :
        highHourMainsL init (virtualLabels init ω S)
            (virtualLabels init ω v) h ≤ credit init ω h σ v := by
      rw [highHourMainsL_eq_hSum init ω hentry h v hSv]
      rw [hzero.2, zero_add] at hsums
      exact hsums.2
    have hdeep :
        highHourZeroMainsL init (virtualLabels init ω S)
              (virtualLabels init ω v) h +
            deepBiasedMainsL init (virtualLabels init ω S)
              (virtualLabels init ω v) h ≤ 2 * credit init ω h σ v := by
      exact (highHourZero_add_deep_le_vSum init ω hentry h v hSv).trans
        (by rw [hzero.1, zero_add] at hsums; exact hsums.1)
    exact ⟨v, hσv, hvFinish,
      (row_failure_forces_credit hhour hdeep (Or.inl hstrict)).le⟩
  · obtain ⟨v, hSv, hvFinish, hstrict⟩ := hbad
    have hσv : σ ≤ v := by
      by_contra hnot
      have hfields := mainFields_before_first init hentry hfirst hSv (by omega)
      have hsums := sums_zero_of_mainFieldsLe init h (virtualLabels init ω v) hfields
      have hle := highHourZero_add_deep_le_vSum init ω hentry h v hSv
      rw [hsums.1] at hle
      omega
    have hsums := sums_le_of_credit init ω hentry h σ v hfirst.1 hσv
    have hhour :
        highHourMainsL init (virtualLabels init ω S)
            (virtualLabels init ω v) h ≤ credit init ω h σ v := by
      rw [highHourMainsL_eq_hSum init ω hentry h v hSv]
      rw [hzero.2, zero_add] at hsums
      exact hsums.2
    have hdeep :
        highHourZeroMainsL init (virtualLabels init ω S)
              (virtualLabels init ω v) h +
            deepBiasedMainsL init (virtualLabels init ω S)
              (virtualLabels init ω v) h ≤ 2 * credit init ω h σ v := by
      exact (highHourZero_add_deep_le_vSum init ω hentry h v hSv).trans
        (by rw [hzero.1, zero_add] at hsums; exact hsums.1)
    exact ⟨v, hσv, hvFinish,
      (row_failure_forces_credit hhour hdeep (Or.inr hstrict)).le⟩

/-- Item 4, in exactly the `barrier` field shape. -/
theorem guardedMainHourFailure_subset_barrier
    (hn : populationThreshold ≤ n) (h : Fin (clockHours n)) :
    guardedMainHourFailure init h.val ⊆
      {ω | mainBarrierRise n ≤
        mainProcessY init h.val (mainTerminalHorizon n) ω -
          mainProcessY init h.val 0 ω} := by
  intro ω hω
  rw [mem_guardedMainHourFailure_iff init h.val ω] at hω
  obtain ⟨S, T, hseedTime, hT, hentry, hguard, hh, hbad⟩ := hω
  simp only [Set.mem_setOf_eq]
  have hseed : ω ∈ seedPrefix init S := ⟨hseedTime, hentry.seed_profile⟩
  let ell := mainLevel h.val
  let w := virtualTimes init ω S
  let sigma := w.first ell
  let finish := w.finish h.val
  let bulk := w.bulk ell
  let seed := guardedMainSeed init ω S T hn hentry
  have hell : 1 ≤ ell := by dsimp only [ell]; exact mainLevel_pos h.val
  have hellCap : ell ≤ clockTop n := by
    dsimp only [ell]
    exact mainLevel_le_clockCap hh
  have hpass : passageRow init ω S T := hguard.2.1
  have hcapRow : capRow init ω S T := hguard.2.2.2
  have hfirst : firstAfter
      (fun v => 1 ≤ frontCountL init (virtualLabels init ω S)
        (virtualLabels init ω v) ell) S sigma := by
    dsimp only [sigma, w]
    exact hpass.level_first ell hell hellCap
  have hfinish : firstAfter
      (fun v => smallThreshold (clockCount (virtualCfg init ω S)) ≤
        frontCountL init (virtualLabels init ω S)
          (virtualLabels init ω v) ell) S finish := by
    dsimp only [finish, w, ell]
    exact hpass.finish_first h.val hh
  have hbulk : firstAfter
      (fun v => bulkThreshold (clockCount (virtualCfg init ω S)) ≤
        frontCountL init (virtualLabels init ω S)
          (virtualLabels init ω v) ell) S bulk := by
    dsimp only [bulk, w]
    exact hpass.level_bulk ell hell hellCap
  have hlocal : bulk - sigma ≤ logWindow n 30 := by
    dsimp only [bulk, sigma, w]
    exact hpass.raw_local ell hell hellCap
  have hcreditWitness := mainHourViolation_credit_witness init hentry
    (by simpa only [ell, sigma, w] using hfirst) hbad
  have hMseed : mainSeedM init seed = timeMainCount (virtualCfg init ω S) := by
    dsimp only [seed]
    rw [guardedMainSeedM_eq,
      virtualCfg_eq_trace_at_seedPrefix init ω S hseed]
  have hCseed : mainSeedC init seed = clockCount (virtualCfg init ω S) := by
    dsimp only [seed]
    rw [guardedMainSeedC_eq,
      virtualCfg_eq_trace_at_seedPrefix init ω S hseed]
  have hex : ∃ v, sigma ≤ v ∧ v ≤ finish ∧
      3 * mainSeedM init seed ≤ 2500 * credit init ω h.val sigma v := by
    obtain ⟨v, hσv, hv, hcredit⟩ := hcreditWitness
    exact ⟨v, hσv, hv, by simpa only [hMseed] using hcredit⟩
  let tau := Nat.find hex
  have htauSpec := Nat.find_spec hex
  have htauFirst : MainCreditFirst init ω h.val sigma seed tau := by
    refine
      { lower := htauSpec.1
        hit := htauSpec.2.2
        before := ?_ }
    intro u hσu hu
    by_contra hnot
    have hbarrier :
        3 * mainSeedM init seed ≤ 2500 * credit init ω h.val sigma u := by
      omega
    have hmin := Nat.find_min' hex ⟨hσu, by omega, hbarrier⟩
    omega
  have hfinishBulk := guardedFinish_le_bulk init hfinish hbulk
  have hpositive : 1 ≤ smallThreshold (clockCount (virtualCfg init ω S)) := by
    rw [← hCseed]
    exact smallThreshold_pos init seed
  have hsigmaFinish := guardedFirst_le_finish init hpositive hfirst hfinish
  have hfinishRow := firstThreshold_front_eq init hentry hell hellCap hpositive hfinish
  have hfinishCurrent :
      PhaseThreeClockGatedLaw.frontCount (virtualLabels init ω finish) ell =
        smallThreshold (clockCount (virtualCfg init ω S)) := by
    simpa only [core_front_eq_current_of_asyncEntry init ω S T finish ell
      hseed hentry hfinish.1] using hfinishRow
  have hfrontMonoRow := core_front_mono_of_asyncEntry init ω S T ell tau finish
    hseed hentry hell hellCap (hfirst.1.trans htauSpec.1) htauSpec.2.1
  have hfrontMono :
      PhaseThreeClockGatedLaw.frontCount (virtualLabels init ω tau) ell ≤
        PhaseThreeClockGatedLaw.frontCount (virtualLabels init ω finish) ell := by
    simpa only [core_front_eq_current_of_asyncEntry init ω S T tau ell
      hseed hentry (hfirst.1.trans htauSpec.1),
      core_front_eq_current_of_asyncEntry init ω S T finish ell
        hseed hentry hfinish.1] using hfrontMonoRow
  have hsparseNat :
      1000 * PhaseThreeClockGatedLaw.frontCount (virtualLabels init ω tau) ell ≤
        mainSeedC init seed := by
    rw [hCseed]
    calc
      1000 * PhaseThreeClockGatedLaw.frontCount (virtualLabels init ω tau) ell ≤
          1000 * PhaseThreeClockGatedLaw.frontCount (virtualLabels init ω finish) ell :=
        Nat.mul_le_mul_left 1000 hfrontMono
      _ = 1000 * smallThreshold (clockCount (virtualCfg init ω S)) := by
        rw [hfinishCurrent]
      _ ≤ clockCount (virtualCfg init ω S) :=
        smallThreshold_rounding _
  have hage : tau - sigma ≤ logWindow n 30 :=
    guardedAge_le_window (n := n) htauSpec.2.1 hfinishBulk hlocal
  have hstopped : mainProcessState init h.val tau ω =
      .stopped (mainLiveValue init seed (tau - sigma)
        (credit init ω h.val sigma tau)
        (PhaseThreeClockGatedLaw.frontCount (virtualLabels init ω tau) ell)) := by
    dsimp only [seed]
    exact mainProcessState_stopped_at_credit init hn hentry hh
      (by simpa only [ell, sigma, w] using hfirst)
      (by simpa only [ell, finish, w] using hfinish)
      (by simpa only [ell, bulk, w] using hbulk)
      hlocal (by simpa only [seed] using htauFirst) htauSpec.2.1
  have hfinishCap : finish ≤ w.cap := by
    dsimp only [finish]
    exact (hpass.hour_before_cap h.val hh).2
  have hcapDeadline : w.cap ≤ S + logWindow n 20000 := hcapRow.cap_deadline
  have hSearly : S ≤ earlyHorizon n := hentry.order.trans hT
  have htauHorizon : tau ≤ mainTerminalHorizon n := by
    unfold mainTerminalHorizon
    omega
  have hterminal := mainProcessState_stopped_mono init h.val ω hstopped htauHorizon
  have hMpos := mainSeed_main_real_pos init seed
  have hCpos := mainSeed_clock_real_pos init seed
  have hcreditReal :
      (3 : ℝ) * mainSeedM init seed ≤
        2500 * (credit init ω h.val sigma tau : ℝ) := by
    exact_mod_cast htauSpec.2.2
  have hsparseReal :
      (1000 : ℝ) * PhaseThreeClockGatedLaw.frontCount (virtualLabels init ω tau) ell ≤
        mainSeedC init seed := by
    exact_mod_cast hsparseNat
  have hpotential := barrier_potential_lower hMpos hCpos hcreditReal hsparseReal
  have hdiscount := main_discount_calibration hn seed hage
  have hdiscountNonneg := (mainDiscount_bounds init seed (tau - sigma)).1
  have hvalue : mainBarrierRise n ≤
      mainLiveValue init seed (tau - sigma)
        (credit init ω h.val sigma tau)
        (PhaseThreeClockGatedLaw.frontCount (virtualLabels init ω tau) ell) := by
    calc
      mainBarrierRise n ≤ mainDiscount init seed (tau - sigma) / 10000 := hdiscount
      _ = mainDiscount init seed (tau - sigma) * (1 / 10000 : ℝ) := by ring
      _ ≤ mainDiscount init seed (tau - sigma) *
          mainPotential init seed (credit init ω h.val sigma tau)
            (PhaseThreeClockGatedLaw.frontCount (virtualLabels init ω tau) ell) :=
        mul_le_mul_of_nonneg_left hpotential hdiscountNonneg
      _ = _ := rfl
  have hzero := mainProcessY_zero init h.val ω
  rw [hzero, sub_zero]
  unfold mainProcessY
  rw [hterminal]
  exact hvalue

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockMainBarrier

end
