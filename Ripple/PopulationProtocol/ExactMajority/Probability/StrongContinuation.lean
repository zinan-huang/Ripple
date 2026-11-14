-- Ripple/PopulationProtocol/ExactMajority/Probability/StrongContinuation.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.StrongContinuationComposition
import Ripple.PopulationProtocol.ExactMajority.Probability.StrongPhaseFour
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseNineContinuation

/-!
The strong continuation, including M = 40d.  The current readout already
supplies the useful input gap and a genuine Phase-4 seed.  Hence neither
of the unfinished N12/N13 producer estimates is a premise here.

The four actual upper timers use the stronger available 40nH allowance
with error n^-5.  The resulting schedule has coefficient 1142 before
ceiling corrections and is contained in the requested 1800 window.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.StrongContinuation

open TimeTheorem PairLog TraceDrain StageEventSpec PhaseOneDrain
  PhaseOneDrainStopping StrongContinuationTimer StrongContinuationComposition

variable {n : ℕ}

def smallError (n : ℕ) : ℝ≥0∞ := ENNReal.ofReal (1 / (n : ℝ) ^ 5)

def continuationHorizon (n : ℕ) : ℕ :=
  6 * activationHorizon n + 2 * logWindow n 3 +
    4 * PhaseOneTimer.timerHorizon n + logWindow n 12 +
      StrongGapBackup.backupHorizon n

theorem sixth_error_le (hn : 2 ≤ n) :
    ENNReal.ofReal (1 / (n : ℝ) ^ 6) ≤ smallError n := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : (0 : ℝ) < n := by linarith
  apply ENNReal.ofReal_le_ofReal
  exact one_div_le_one_div_of_le (by positivity)
    (pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ n) (by decide : 5 ≤ 6))

theorem double_error :
    ENNReal.ofReal (2 / (n : ℝ) ^ 5) = 2 * smallError n := by
  unfold smallError
  rw [show (2 : ℝ) / (n : ℝ) ^ 5 = 2 * (1 / (n : ℝ) ^ 5) by ring,
    ENNReal.ofReal_mul (by norm_num)]
  norm_num

theorem seven_error :
    ENNReal.ofReal (7 / (n : ℝ) ^ 5) = 7 * smallError n := by
  unfold smallError
  rw [show (7 : ℝ) / (n : ℝ) ^ 5 = 7 * (1 / (n : ℝ) ^ 5) by ring,
    ENNReal.ofReal_mul (by norm_num)]
  norm_num

theorem continuation_error_le (hn : 40 ≤ n) :
    24 * smallError n + ENNReal.ofReal (5 / (n : ℝ) ^ 3) ≤
      ENNReal.ofReal (6 / (n : ℝ) ^ 3) := by
  have hnR : (40 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : (0 : ℝ) < n := by linarith
  have hsq : (24 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have hm := mul_le_mul_of_nonneg_right hsq (pow_nonneg hp.le 3)
  have hratio : (24 : ℝ) / (n : ℝ) ^ 5 ≤ 1 / (n : ℝ) ^ 3 :=
    (div_le_div_iff₀ (pow_pos hp 5) (pow_pos hp 3)).2 (by nlinarith only [hm])
  have he :
      24 * smallError n + ENNReal.ofReal (5 / (n : ℝ) ^ 3) =
        ENNReal.ofReal (24 / (n : ℝ) ^ 5 + 5 / (n : ℝ) ^ 3) := by
    unfold smallError
    rw [ENNReal.ofReal_add (by positivity) (by positivity),
      show (24 : ℝ) / (n : ℝ) ^ 5 = 24 * (1 / (n : ℝ) ^ 5) by ring,
      ENNReal.ofReal_mul (by norm_num)]
    norm_num
  rw [he]
  apply ENNReal.ofReal_le_ofReal
  have e6 : (6 : ℝ) / (n : ℝ) ^ 3 = 5 / (n : ℝ) ^ 3 + 1 / (n : ℝ) ^ 3 := by ring
  linarith only [hratio, e6]

theorem continuation_horizon_le (hn : timePopulationThreshold ≤ n) :
    continuationHorizon n ≤ logWindow n 1800 := by
  obtain ⟨hnlarge, hp, hlog, -, hH, -⟩ := time_hour_calibration hn
  clear hn
  have hnR : (40 : ℝ) ≤ n := by exact_mod_cast hnlarge
  have hlognonneg : 0 ≤ Real.log (n : ℝ) := by linarith
  have hHtwo : (PhaseThreeModel.Numeric.clockHours n : ℝ) ≤
      2 * Real.log (n : ℝ) := by linarith
  have hHmul := mul_le_mul_of_nonneg_left hHtwo
    (show 0 ≤ (160 : ℝ) * n by positivity)
  have hprod := mul_le_mul_of_nonneg_left hlog hp.le
  have hceil (c : ℕ) :
      (logWindow n c : ℝ) ≤ (c : ℝ) * (n : ℝ) * Real.log (n : ℝ) + 1 := by
    unfold logWindow
    exact (Nat.ceil_lt_add_one (by positivity)).le
  have htarget : (1800 : ℝ) * (n : ℝ) * Real.log (n : ℝ) ≤
      (logWindow n 1800 : ℝ) := Nat.le_ceil _
  have hreal : (continuationHorizon n : ℝ) ≤ (logWindow n 1800 : ℝ) := by
    unfold continuationHorizon StrongGapBackup.backupHorizon
      StrongGapBackup.threeStageHorizon activationHorizon PhaseOneTimer.timerHorizon
    push_cast
    have hc := hceil 6
    have hd := hceil 3
    have he := hceil 12
    have hf := hceil 240
    norm_num only [Nat.cast_ofNat] at hc hd he hf
    nlinarith only [hc, hd, he, hf, hHmul, hprod, hnR, htarget]
  exact_mod_cast hreal

theorem prefix_phase_four (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init) :
    PrefixEstimate init (StableOrAll init 4) (StableOrSeed init 5)
      (logWindow n 3) (smallError n) := by
  have hnlarge : 40 ≤ n := (time_population_bounds hinput.1).2
  have hn : 2 ≤ n := (by decide : 2 ≤ 40).trans hnlarge
  have hlow : 11 ≤ init.card := by rw [hinput.2.2]; exact (by decide : 11 ≤ 40).trans hnlarge
  have hsize : init.card ≤ 2 ^ PhaseThreeModel.Numeric.hourIndex n := by
    rw [hinput.2.2]
    exact Nat.le_pow_clog (by decide : 1 < (2 : ℕ)) n
  intro s A hA
  let B : Set ((k : Finset.Iic s) → Draw (PhaseThreeModel.Numeric.hourIndex n) 256) :=
    {a | a ∈ A ∧ ∀ b ∈ prefixCfg init s a, 4 ≤ b.phase.val}
  have hb : ∀ a ∈ B, UniformRecovery.phaseWorkInv 4 n init (prefixCfg init s a) := by
    intro a ha
    exact ⟨prefix_reachable init s a, (prefix_card init s a).trans hinput.2.2, ha.2⟩
  have ht := (StrongPhaseFour.phase_four_prefix_calibrated init hinput.2.1 hlow hsize
    n hn s B hb).trans (mul_le_mul_right' (sixth_error_le hn) _)
  have hmass :
      law init {ω | frestrictLe (π := fun _ : ℕ => Draw _ _) s ω ∈ B} ≤
        law init {ω | frestrictLe (π := fun _ : ℕ => Draw _ _) s ω ∈ A} :=
    measure_mono fun ω hω => hω.1
  apply (measure_mono ?_).trans (ht.trans (mul_le_mul_left' hmass _))
  rintro ω ⟨ha, hbad⟩
  have hs : trace init ω s ∉ StableDone _ _ init := by
    intro hd
    exact hbad (Or.inl (stable_persists init ω s _ (Nat.le_add_right _ _) hd))
  refine ⟨⟨ha, (hA _ ha).resolve_left hs⟩, ?_⟩
  rintro (hd | ⟨a, ha', hp⟩)
  · exact hbad (Or.inl hd)
  · exact hbad (Or.inr ⟨a, ha', Nat.succ_le_of_lt hp⟩)

theorem prefix_timed_rung (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init)
    (p : ℕ) (hp : TimedPhase p) :
    PrefixEstimate init (StableOrAll init p) (StableOrAll init (p + 1))
      (PhaseOneTimer.timerHorizon n + activationHorizon n)
      (3 * smallError n) := by
  have hn : 2 ≤ n := (by decide : 2 ≤ 40).trans (time_population_bounds hinput.1).2
  have ht := prefix_estimate_trans init
    (StableOrAll init p) (StableOrSeed init (p + 1)) (StableOrAll init (p + 1))
    (PhaseOneTimer.timerHorizon n) (activationHorizon n)
    (smallError n) (ENNReal.ofReal (2 / (n : ℝ) ^ 5))
    (prefix_timed init hinput.2.1 hn hinput.2.2 p hp)
    (prefix_threshold init hn hinput.2.2 (p + 1) (Nat.succ_pos p))
  have he : smallError n + ENNReal.ofReal (2 / (n : ℝ) ^ 5) = 3 * smallError n := by
    rw [double_error]
    ring
  simpa only [he] using ht

theorem prefix_four_timers (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init) :
    PrefixEstimate init (StableOrAll init 5) (StableOrAll init 9)
      (4 * (PhaseOneTimer.timerHorizon n + activationHorizon n))
      (12 * smallError n) := by
  let D := PhaseOneTimer.timerHorizon n + activationHorizon n
  let e := smallError n
  have hfirst : PrefixEstimate init (StableOrAll init 5) (StableOrAll init 6) D (3 * e) :=
    prefix_timed_rung init hinput 5 (by simp [TimedPhase])
  have hsecond : PrefixEstimate init (StableOrAll init 6) (StableOrAll init 7) D (3 * e) :=
    prefix_timed_rung init hinput 6 (by simp [TimedPhase])
  have hthird : PrefixEstimate init (StableOrAll init 7) (StableOrAll init 8) D (3 * e) :=
    prefix_timed_rung init hinput 7 (by simp [TimedPhase])
  have hfourth : PrefixEstimate init (StableOrAll init 8) (StableOrAll init 9) D (3 * e) :=
    prefix_timed_rung init hinput 8 (by simp [TimedPhase])
  have htwo := prefix_estimate_trans init _ _ _ D D (3 * e) (3 * e) hfirst hsecond
  have hthree := prefix_estimate_trans init _ _ _ (D + D) D (3 * e + 3 * e)
    (3 * e) htwo hthird
  have hfour := prefix_estimate_trans init _ _ _ ((D + D) + D) D
    ((3 * e + 3 * e) + 3 * e) (3 * e) hthree hfourth
  have hN : ((D + D) + D) + D = 4 * D := by ring
  have he : ((3 * e + 3 * e) + 3 * e) + 3 * e = 12 * e := by ring
  simpa only [hN, he] using hfour

theorem prefix_phase_nine (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init) :
    PrefixEstimate init (StableOrAll init 9) (StableOrSeed init 10)
      (logWindow n 12 + logWindow n 3) (7 * smallError n) := by
  intro s A hA
  let B : Set ((k : Finset.Iic s) → Draw (PhaseThreeModel.Numeric.hourIndex n) 256) :=
    {a | a ∈ A ∧ UniformRecovery.PurePhase 9 (prefixCfg init s a)}
  have hb : ∀ a ∈ B, (prefixCfg init s a).card = n ∧
      UniformRecovery.PurePhase 9 (prefixCfg init s a) :=
    fun a ha => ⟨(prefix_card init s a).trans hinput.2.2, ha.2⟩
  have ht := PhaseNineContinuation.phase_nine_prefix_tail init hinput s B hb
  simp only [Nat.add_assoc] at ht
  rw [seven_error] at ht
  have hmass :
      law init {ω | frestrictLe (π := fun _ : ℕ => Draw _ _) s ω ∈ B} ≤
        law init {ω | frestrictLe (π := fun _ : ℕ => Draw _ _) s ω ∈ A} :=
    measure_mono fun ω hω => hω.1
  apply (measure_mono ?_).trans (ht.trans (mul_le_mul_left' hmass _))
  rintro ω ⟨ha, hbad⟩
  have hs : trace init ω s ∉ StableDone _ _ init := by
    intro hd
    exact hbad (Or.inl (stable_persists init ω s _ (Nat.le_add_right _ _) hd))
  have hlo := (hA _ ha).resolve_left hs
  have hhi : ∀ a ∈ trace init ω s, a.phase.val ≤ 9 := by
    intro a ha'
    by_contra hh
    have hseed : ∃ b ∈ trace init ω s, 10 ≤ b.phase.val :=
      ⟨a, ha', Nat.succ_le_of_lt (Nat.lt_of_not_ge hh)⟩
    exact hbad (Or.inr (seed_persists init ω 10 s _ (by decide)
      (Nat.le_add_right _ _) hseed))
  exact ⟨⟨ha, fun a ha' => le_antisymm (hhi a ha') (hlo a ha')⟩, hbad⟩

/-- The homogeneous backup snapshot also has the pre-existing recovery
guarantee for the verdict of the original input.  Readiness is derived from
actual reachability, including the neutral active source in a tie.  The
sharper signed backup tail below supplies the logarithmic-time estimate. -/
theorem backup_prefix_expected_recovery (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init)
    (s : ℕ)
    (a : (k : Finset.Iic s) → Draw (PhaseThreeModel.Numeric.hourIndex n) 256)
    (hAll : Phase10Drop.AllPhase10 (prefixCfg init s a)) :
    expectedHitting (NonuniformMajority _ _).transitionKernel
      (prefixCfg init s a) (StableDone _ _ init) ≤
        UniformRecovery.phaseTenDrainBudget n := by
  have hn : 2 ≤ n := (by decide : 2 ≤ 40).trans
    (time_population_bounds hinput.1).2
  have hr := prefix_reachable init s a
  have hc : (prefixCfg init s a).card = n :=
    (prefix_card init s a).trans hinput.2.2
  exact Recovery10ToStable.phase10Ready_reachable_expectedHitting_stableDone_le
    n hn init (prefixCfg init s a) hinput.2.1 hr
    (UniformRecovery.reachable_allPhaseTen_ready n hn init
      (prefixCfg init s a) hinput.2.1 hr hc hAll)

theorem strong_prefix_estimate (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init)
    (hstrong : n ≤ 120 * gapMagnitude init) :
    PrefixEstimate init (StableOrSeed init 4)
      (fun c => c ∈ StableDone (PhaseThreeModel.Numeric.hourIndex n) 256 init)
      (continuationHorizon n) (ENNReal.ofReal (6 / (n : ℝ) ^ 3)) := by
  have hnlarge : 40 ≤ n := (time_population_bounds hinput.1).2
  have hn : 2 ≤ n := (by decide : 2 ≤ 40).trans hnlarge
  let a := activationHorizon n
  let b := logWindow n 3
  let d := PhaseOneTimer.timerHorizon n + a
  let e := smallError n
  have hspread : PrefixEstimate init (StableOrSeed init 4) (StableOrAll init 4)
      a (2 * e) := by
    simpa only [double_error] using prefix_threshold init hn hinput.2.2 4 (by decide)
  have hwork := prefix_estimate_trans init _ _ _ a b (2 * e) e
    hspread (prefix_phase_four init hinput)
  have hspreadNext : PrefixEstimate init (StableOrSeed init 5) (StableOrAll init 5)
      a (2 * e) := by
    simpa only [double_error] using prefix_threshold init hn hinput.2.2 5 (by decide)
  have hfive := prefix_estimate_trans init _ _ _ (a + b) a (2 * e + e) (2 * e)
    hwork hspreadNext
  have hnine := prefix_estimate_trans init _ _ _ ((a + b) + a) (4 * d)
    ((2 * e + e) + 2 * e) (12 * e) hfive (prefix_four_timers init hinput)
  have hten := prefix_estimate_trans init _ _ _ (((a + b) + a) + 4 * d)
    (logWindow n 12 + b) (((2 * e + e) + 2 * e) + 12 * e) (7 * e)
    hnine (prefix_phase_nine init hinput)
  have hdone := prefix_estimate_trans init _ _ _
    ((((a + b) + a) + 4 * d) + (logWindow n 12 + b))
    (StrongGapBackup.backupHorizon n)
    ((((2 * e + e) + 2 * e) + 12 * e) + 7 * e)
    (ENNReal.ofReal (5 / (n : ℝ) ^ 3)) hten
    (prefix_backup init hinput.2.1 hn hinput.2.2 hstrong)
  have hN :
      ((((a + b) + a) + 4 * d) + (logWindow n 12 + b)) +
        StrongGapBackup.backupHorizon n = continuationHorizon n := by
    dsimp only [a, b, d, continuationHorizon]
    ring
  have he :
      ((((2 * e + e) + 2 * e) + 12 * e) + 7 * e) +
        ENNReal.ofReal (5 / (n : ℝ) ^ 3) =
      24 * smallError n + ENNReal.ofReal (5 / (n : ℝ) ^ 3) := by
    dsimp only [e]
    ring
  rw [hN, he] at hdone
  exact prefix_estimate_mono init _ _ _ _ _ _ _ hdone
    (fun _ h => h) (fun _ h => h) (continuation_error_le hnlarge)

def firstFour (init : InputCfg n) : InputLog n → WithTop ℕ :=
  TraceDrain.exitTime init (someGE (n := n) 4)

theorem firstFour_past (init : InputCfg n) :
    PairLogPastTime (firstFour init) :=
  exitTime_pairLogPastTime init (someGE (n := n) 4)

theorem firstFour_isStoppingTime (init : InputCfg n) :
    IsStoppingTime (pairLogFiltration _ _) (firstFour init) :=
  TraceDrain.exitTime_isStoppingTime init (someGE (n := n) 4)

theorem firstFour_of_seed (init : InputCfg n) (ω : InputLog n) (s : ℕ)
    (hs : firstPhaseSeed init 4 s ω) :
    firstFour init ω = (s : WithTop ℕ) := by
  apply (exitTime_eq_iff_firstHit init (someGE (n := n) 4) ω s).2
  refine ⟨?_, ?_⟩
  · obtain ⟨a, ha, hp⟩ := hs.1
    exact ⟨a, ha, hp.ge⟩
  · intro u hu
    rintro ⟨a, ha, hphase⟩
    have := hs.2 u hu a ha
    omega

theorem strong_readout_of_history (init : InputCfg n) (ω : InputLog n) (S T ρ : ℕ)
    (hh : successfulHistory (reviewedStageEvents n init) ω S T ρ)
    (hgap : 0 < gapMagnitude init)
    (hstrong : timeMainCount (trace init ω S) ≤ 40 * gapMagnitude init) :
    StrongReadout init (timeMainCount (trace init ω S)) (trace init ω ρ) := by
  have ha : averageReadout init (timeMainCount (trace init ω S)) (trace init ω ρ) := hh.2.2.2
  rcases ha with htie | hsmall | hlarge
  · have hg : gapMagnitude init = 0 := by simp [gapMagnitude, htie.1]
    omega
  · obtain ⟨ell, σ, hs⟩ := hsmall
    have := hs.strictGap
    omega
  · exact hlarge

/-- N15, including equality in the strong branch.  All local estimates were
established on genuine observed prefixes under the original law. -/
theorem strong_continuation_estimate (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init) :
    law init (strongGapLateFailure (reviewedStageEvents n init)) ≤
      ENNReal.ofReal (6 / (n : ℝ) ^ 3) := by
  classical
  by_cases hstrong : n ≤ 120 * gapMagnitude init
  · have ht := prefix_estimate_at_past_time init (StableOrSeed init 4)
      (fun c => c ∈ StableDone (PhaseThreeModel.Numeric.hourIndex n) 256 init)
      (continuationHorizon n) (ENNReal.ofReal (6 / (n : ℝ) ^ 3))
      (strong_prefix_estimate init hinput hstrong) (firstFour init) (firstFour_past init)
    apply (measure_mono ?_).trans ht
    rintro ω ⟨S, T, ρ, hh, hg, hM, hu, hbad⟩
    have hseed := (reviewedStageEvents n init).clock_seed hh.2.2.1
    refine ⟨ρ, firstFour_of_seed init ω ρ hseed, ?_, ?_⟩
    · obtain ⟨a, ha, hp⟩ := hseed.1
      exact Or.inr ⟨a, ha, hp.ge⟩
    · intro hdone
      apply hbad
      refine ⟨ρ + continuationHorizon n, ?_, hdone⟩
      gcongr
      exact continuation_horizon_le hinput.1
  · have he : strongGapLateFailure (reviewedStageEvents n init) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro ω ⟨S, T, ρ, hh, hg, hM, hu, hbad⟩
      exact hstrong (strong_readout_of_history init ω S T ρ hh hg hM).usefulGap
    rw [he, measure_empty]
    exact zero_le

end Ripple.PopulationProtocol.ExactMajority.StrongContinuation

end
