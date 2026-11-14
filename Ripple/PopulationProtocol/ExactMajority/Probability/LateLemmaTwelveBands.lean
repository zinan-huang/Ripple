-- Ripple/PopulationProtocol/ExactMajority/Probability/LateLemmaTwelveBands.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.LateLemmaTwelveSingleBand
import Ripple.PopulationProtocol.ExactMajority.Probability.LateLemmaElevenAssembly
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeAveragingStops
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingSeededDelay
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase7BandTransition

/-!
# Lemma 12: the three Phase-7 bands

Imported from `LateLemmaTwelveSingleBand`:

* `SingleBandReady`;
* `phaseSevenSingleBandFailureAt` and its measurability theorem;
* `phaseSevenSingleBandDrift`;
* `phaseSevenSingleBandScalar` and `phaseSevenSingleBandBudget`.

The random-time lift below does not substitute a random time into the
unconditional single-band theorem.  It invokes the prefix-weighted splice already
available, `PhaseThreeAveragingStops.potential_drift_tail_at_pastTime`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder Set
open scoped ENNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.LateLemmaTwelveBands

open TimeTheorem PairLog TraceDrain StageEventSpec
open PhaseOneDrain PhaseOneDrainStopping
open Phase7BandDefs Phase7BandTransition
open LateBiasedResourceCreditPhaseSeven
open LateBiasedResourceCreditPath
open LateMixedFiveSixWindow
open LateTimerUpperOriginalLaw
open LateLemmaElevenFiniteTimes
open LateLemmaTwelveSingleBand

variable {L K n M : ℕ}

/-! ## The prefix-weighted random-start lift -/

/-- The single-band stopped failure, now started at a genuine pair-log past time. -/
def phaseSevenSingleBandFailureAtPast
    (init : Cfg L K) (n M : ℕ) (sigma : Sign)
    (ell j : Fin (L + 1))
    (start : Ω L K → WithTop ℕ) : Set (Ω L K) :=
  {omega | ∃ s : ℕ, start omega = (s : WithTop ℕ) ∧
    omega ∈ phaseSevenSingleBandFailureAt init n M sigma ell j s}

/-- The random-start event is a countable union of measurable time fibres
intersected with the measurable single-band fixed-time event. -/
theorem measurableSet_phaseSevenSingleBandFailureAtPast
    (init : Cfg L K) (n M : ℕ) (sigma : Sign)
    (ell j : Fin (L + 1))
    (start : Ω L K → WithTop ℕ)
    (hstart : PairLogPastTime start) :
    MeasurableSet
      (phaseSevenSingleBandFailureAtPast
        init n M sigma ell j start) := by
  have heq :
      phaseSevenSingleBandFailureAtPast init n M sigma ell j start =
        ⋃ s : ℕ,
          {omega | start omega = (s : WithTop ℕ)} ∩
            phaseSevenSingleBandFailureAt init n M sigma ell j s := by
    ext omega
    simp [phaseSevenSingleBandFailureAtPast]
  rw [heq]
  apply MeasurableSet.iUnion
  intro s
  exact
    ((pairLogFiltration L K).le s _ (hstart s)).inter
      (measurableSet_phaseSevenSingleBandFailureAt
        init n M sigma ell j s)

/-- **Stopping-time splice for one band.**  This is the prefix-weighted local
estimate, not an application of the unconditional fixed-`s` theorem at a
random argument. -/
theorem law_phaseSevenSingleBandFailureAtPast
    (init : Cfg L K)
    (hn : 2 ≤ n) (hM : 12 * n ≤ 25 * M)
    (sigma : Sign) (ell j : Fin (L + 1))
    (hjl : ell.val ≤ j.val) (hjtop : j.val < ell.val + 3)
    (start : Ω L K → WithTop ℕ)
    (hstart : PairLogPastTime start) :
    law init
        (phaseSevenSingleBandFailureAtPast
          init n M sigma ell j start) ≤
      phaseSevenSingleBandBudget n := by
  have htail :
      law init
          (PhaseThreeAveragingStops.driftFailureAt init start
            (fun c => bandCountN (L := L) (K := K) sigma j c)
            (fun c => SingleBandReady n M sigma ell j c)
            (phaseSevenBandHorizon n) n) ≤
        (1 - phaseSevenBandRate n) ^ phaseSevenBandHorizon n * n := by
    exact
      PhaseThreeAveragingStops.potential_drift_tail_at_pastTime
        init start hstart
        (fun c => bandCountN (L := L) (K := K) sigma j c)
        (fun c => SingleBandReady n M sigma ell j c)
        (phaseSevenBandRate n)
        (phaseSevenSingleBandDrift
          (L := L) (K := K) hn hM sigma ell j hjl hjtop)
        (phaseSevenBandHorizon n) n
  calc
    law init
        (phaseSevenSingleBandFailureAtPast
          init n M sigma ell j start) ≤
      law init
        (PhaseThreeAveragingStops.driftFailureAt init start
          (fun c => bandCountN (L := L) (K := K) sigma j c)
          (fun c => SingleBandReady n M sigma ell j c)
          (phaseSevenBandHorizon n) n) := by
      apply measure_mono
      intro omega homega
      change ∃ s : ℕ, start omega = (s : WithTop ℕ) ∧
        omega ∈ phaseSevenSingleBandFailureAt
          init n M sigma ell j s at homega
      rcases homega with ⟨s, hs, hfixed⟩
      change
        SingleBandReady n M sigma ell j (trace init omega s) ∧
          (∀ u, s ≤ u → u < s + phaseSevenBandHorizon n →
            SingleBandReady n M sigma ell j (trace init omega u)) ∧
          1 ≤ bandCountN (L := L) (K := K) sigma j
            (trace init omega (s + phaseSevenBandHorizon n)) at hfixed
      rcases hfixed with ⟨hready, halive, hpositive⟩
      refine ⟨s, hs, ?_, halive, hpositive⟩
      exact
        (bandCountN_le_card (L := L) (K := K) sigma j
          (trace init omega s)).trans_eq
            hready.consumer.genuine.1
    _ ≤ (1 - phaseSevenBandRate n) ^ phaseSevenBandHorizon n * n :=
      htail
    _ ≤ phaseSevenSingleBandBudget n :=
      phaseSevenSingleBandScalar n hn

/-! ## The three deterministic offsets from the random homogeneous time -/

/-- The second exact band. -/
def middleBand (ell : Fin (L + 1)) (hell : ell.val + 2 ≤ L) :
    Fin (L + 1) :=
  ⟨ell.val + 1, by omega⟩

/-- The third exact band. -/
def upperBand (ell : Fin (L + 1)) (hell : ell.val + 2 ≤ L) :
    Fin (L + 1) :=
  ⟨ell.val + 2, by omega⟩

/-- Start slot `slot` exactly `slot * H` interactions after the homogeneous
Phase-7 time.  `seededDelay` is used with the same seed and start time. -/
noncomputable def phaseSevenBandSchedule
    (init : InputCfg n) (slot : ℕ) : InputLog n → WithTop ℕ :=
  AveragingSeededDelay.seededDelay init
    (homogeneousLatePhaseStart init 7)
    (homogeneousLatePhaseStart init 7)
    (fun _ => slot * phaseSevenBandHorizon n)

/-- Every deterministic offset schedule is a genuine pair-log past time. -/
theorem phaseSevenBandSchedule_pastTime
    (init : InputCfg n) (slot : ℕ) :
    PairLogPastTime (phaseSevenBandSchedule init slot) := by
  exact
    AveragingSeededDelay.seededDelay_pastTime init
      (homogeneousLatePhaseStart init 7)
      (homogeneousLatePhaseStart init 7)
      (homogeneousLatePhaseStart_past init 7)
      (homogeneousLatePhaseStart_past init 7)
      (fun _ => slot * phaseSevenBandHorizon n)

/-- Evaluation of a schedule on a finite homogeneous-time fibre. -/
theorem phaseSevenBandSchedule_eq
    (init : InputCfg n) (slot : ℕ) (omega : InputLog n)
    (homogeneous : ℕ)
    (hhomogeneous :
      homogeneousLatePhaseStart init 7 omega =
        (homogeneous : WithTop ℕ)) :
    phaseSevenBandSchedule init slot omega =
      ((homogeneous + slot * phaseSevenBandHorizon n : ℕ) : WithTop ℕ) := by
  simpa [phaseSevenBandSchedule] using
    (AveragingSeededDelay.seededDelay_eq_of_eq init
      (homogeneousLatePhaseStart init 7)
      (homogeneousLatePhaseStart init 7)
      (fun _ => slot * phaseSevenBandHorizon n)
      omega homogeneous homogeneous
      hhomogeneous hhomogeneous le_rfl)

/-- The named three-band failure set for one fixed Lemma-11 witness branch. -/
def phaseSevenBandsFailure
    (init : InputCfg n) (M : ℕ) (sigma : Sign)
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n) :
    Set (InputLog n) :=
  phaseSevenSingleBandFailureAtPast
      init n M sigma ell ell
      (phaseSevenBandSchedule init 0) ∪
    (phaseSevenSingleBandFailureAtPast
        init n M sigma ell (middleBand ell hell)
        (phaseSevenBandSchedule init 1) ∪
      phaseSevenSingleBandFailureAtPast
        init n M sigma ell (upperBand ell hell)
        (phaseSevenBandSchedule init 2))

/-- Exact three-band charge `3 * n^(-3.64256)`. -/
noncomputable def phaseSevenBandsBudget (n : ℕ) : ℝ≥0∞ :=
  3 * phaseSevenSingleBandBudget n

/-- Measurability of the named three-band union. -/
theorem measurableSet_phaseSevenBandsFailure
    (init : InputCfg n) (M : ℕ) (sigma : Sign)
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n) :
    MeasurableSet (phaseSevenBandsFailure init M sigma ell hell) := by
  unfold phaseSevenBandsFailure
  exact
    (measurableSet_phaseSevenSingleBandFailureAtPast
      init n M sigma ell ell
      (phaseSevenBandSchedule init 0)
      (phaseSevenBandSchedule_pastTime init 0)).union
      ((measurableSet_phaseSevenSingleBandFailureAtPast
        init n M sigma ell (middleBand ell hell)
        (phaseSevenBandSchedule init 1)
        (phaseSevenBandSchedule_pastTime init 1)).union
        (measurableSet_phaseSevenSingleBandFailureAtPast
          init n M sigma ell (upperBand ell hell)
          (phaseSevenBandSchedule init 2)
          (phaseSevenBandSchedule_pastTime init 2)))

/-- **Three-band union bound.**  There is no start-time counting factor. -/
theorem law_phaseSevenBandsFailure
    (init : InputCfg n)
    (hn : 2 ≤ n) (hM : 12 * n ≤ 25 * M)
    (sigma : Sign)
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n) :
    law init (phaseSevenBandsFailure init M sigma ell hell) ≤
      phaseSevenBandsBudget n := by
  have hbase :
      law init
          (phaseSevenSingleBandFailureAtPast
            init n M sigma ell ell
            (phaseSevenBandSchedule init 0)) ≤
        phaseSevenSingleBandBudget n :=
    law_phaseSevenSingleBandFailureAtPast
      (n := n) (M := M) init hn hM sigma ell ell le_rfl
      (by omega) (phaseSevenBandSchedule init 0)
      (phaseSevenBandSchedule_pastTime init 0)
  have hmiddle :
      law init
          (phaseSevenSingleBandFailureAtPast
            init n M sigma ell (middleBand ell hell)
            (phaseSevenBandSchedule init 1)) ≤
        phaseSevenSingleBandBudget n :=
    law_phaseSevenSingleBandFailureAtPast
      (n := n) (M := M) init hn hM sigma ell
      (middleBand ell hell)
      (by simp [middleBand])
      (by simp [middleBand])
      (phaseSevenBandSchedule init 1)
      (phaseSevenBandSchedule_pastTime init 1)
  have hupper :
      law init
          (phaseSevenSingleBandFailureAtPast
            init n M sigma ell (upperBand ell hell)
            (phaseSevenBandSchedule init 2)) ≤
        phaseSevenSingleBandBudget n :=
    law_phaseSevenSingleBandFailureAtPast
      (n := n) (M := M) init hn hM sigma ell
      (upperBand ell hell)
      (by simp [upperBand])
      (by simp [upperBand])
      (phaseSevenBandSchedule init 2)
      (phaseSevenBandSchedule_pastTime init 2)
  unfold phaseSevenBandsFailure phaseSevenBandsBudget
  calc
    law init
        (phaseSevenSingleBandFailureAtPast
            init n M sigma ell ell
            (phaseSevenBandSchedule init 0) ∪
          (phaseSevenSingleBandFailureAtPast
              init n M sigma ell (middleBand ell hell)
              (phaseSevenBandSchedule init 1) ∪
            phaseSevenSingleBandFailureAtPast
              init n M sigma ell (upperBand ell hell)
              (phaseSevenBandSchedule init 2))) ≤
      law init
          (phaseSevenSingleBandFailureAtPast
            init n M sigma ell ell
            (phaseSevenBandSchedule init 0)) +
        law init
          (phaseSevenSingleBandFailureAtPast
              init n M sigma ell (middleBand ell hell)
              (phaseSevenBandSchedule init 1) ∪
            phaseSevenSingleBandFailureAtPast
              init n M sigma ell (upperBand ell hell)
              (phaseSevenBandSchedule init 2)) :=
      measure_union_le _ _
    _ ≤ phaseSevenSingleBandBudget n +
        (law init
            (phaseSevenSingleBandFailureAtPast
              init n M sigma ell (middleBand ell hell)
              (phaseSevenBandSchedule init 1)) +
          law init
            (phaseSevenSingleBandFailureAtPast
              init n M sigma ell (upperBand ell hell)
              (phaseSevenBandSchedule init 2))) :=
      add_le_add hbase (measure_union_le _ _)
    _ ≤ phaseSevenSingleBandBudget n +
        (phaseSevenSingleBandBudget n +
          phaseSevenSingleBandBudget n) :=
      add_le_add le_rfl (add_le_add hmiddle hupper)
    _ = 3 * phaseSevenSingleBandBudget n := by ring

/-! ## Deterministic pathwise sequencing on a Lemma-11 receipt -/

/-- Lemma 10's no-shallow conclusion clears the cumulative prefix below
`ell`, for either minority sign. -/
private theorem bandClear_of_noShallow
    (sigma : Sign) (ell : Fin (L + 1))
    (c : Config (AgentState L K))
    (h : NoShallowMain ell c) :
    BandClear (L := L) (K := K) sigma ell.val c := by
  classical
  intro j hj
  unfold bandCountN
  apply Finset.sum_eq_zero
  intro a ha
  simp only [Phase7Convergence.minorityAt7, Finset.mem_filter] at ha
  obtain ⟨_, hmain, hbias⟩ := ha
  by_contra hcount
  have hacount : 1 ≤ c.count a :=
    Nat.one_le_iff_ne_zero.mpr hcount
  have hac : a ∈ c :=
    Multiset.one_le_count_iff_mem.mp hacount
  have hhigh : Phase6Convergence.highSt (L := L) (K := K) ell.val a :=
    Phase6Convergence.highSt_of
      (L := L) (K := K) ell.val a sigma j hmain hbias hj
  exact h a hac hhigh

/-- Appending the zero current band to an already-cleared lower prefix. -/
private theorem bandClear_succ_of_count_eq_zero
    (sigma : Sign) (j : Fin (L + 1))
    (c : Config (AgentState L K))
    (hclear : BandClear (L := L) (K := K) sigma j.val c)
    (hzero : bandCountN (L := L) (K := K) sigma j c = 0) :
    BandClear (L := L) (K := K) sigma (j.val + 1) c := by
  intro k hk
  by_cases hkj : k.val < j.val
  · exact hclear k hkj
  · have hval : k.val = j.val := by omega
    have hEq : k = j := Fin.ext hval
    subst k
    exact hzero

/-- One actual draw preserves a cleared prefix in a genuine Phase-7 state. -/
private theorem bandClear_applyDraw
    (sigma : Sign) (m population : ℕ)
    (c : Config (AgentState L K))
    (hwin : PhaseOnlyWindows.Phase7Win
      (L := L) (K := K) population c)
    (hclear : BandClear (L := L) (K := K) sigma m c)
    (draw : Draw L K) :
    BandClear (L := L) (K := K) sigma m (applyDraw c draw) := by
  cases draw with
  | none => exact hclear
  | some pair =>
      change BandClear (L := L) (K := K) sigma m
        (Protocol.stepOrSelf (NonuniformMajority L K)
          c pair.1.1 pair.2.1)
      exact bandClear_stepOrSelf sigma m population c
        hwin hclear pair.1.1 pair.2.1

/-- Pathwise persistence of a cleared prefix over a genuine Phase-7 interval. -/
private theorem bandClear_trace
    (init : Cfg L K) (omega : Ω L K)
    (sigma : Sign) (m population s t : ℕ)
    (hst : s ≤ t)
    (hclear : BandClear (L := L) (K := K) sigma m
      (trace init omega s))
    (hwin : ∀ u, s ≤ u → u < t →
      PhaseOnlyWindows.Phase7Win (L := L) (K := K) population
        (trace init omega u)) :
    BandClear (L := L) (K := K) sigma m
      (trace init omega t) := by
  induction t, hst using Nat.le_induction with
  | base => exact hclear
  | succ t hst ih =>
      have hprev := ih fun u hsu hut =>
        hwin u hsu (by omega)
      rw [TimeTheorem.trace_succ]
      exact bandClear_applyDraw sigma m population
        (trace init omega t)
        (hwin t hst (Nat.lt_succ_self t))
        hprev (omega (t + 1))

/-- Complement of a fixed-start failure, together with its ready/alive facts,
forces zero exact-band count at the block endpoint. -/
private theorem singleBand_zero_of_not_failure
    (init : Cfg L K) (n M : ℕ) (sigma : Sign)
    (ell j : Fin (L + 1)) (omega : Ω L K) (s : ℕ)
    (hready : SingleBandReady n M sigma ell j
      (trace init omega s))
    (halive : ∀ u, s ≤ u → u < s + phaseSevenBandHorizon n →
      SingleBandReady n M sigma ell j (trace init omega u))
    (hgood : omega ∉
      phaseSevenSingleBandFailureAt init n M sigma ell j s) :
    bandCountN (L := L) (K := K) sigma j
      (trace init omega (s + phaseSevenBandHorizon n)) = 0 := by
  by_contra hne
  apply hgood
  exact ⟨hready, halive, Nat.one_le_iff_ne_zero.mpr hne⟩

private theorem trace_card_eq_population
    {init : InputCfg n} {omega : InputLog n}
    (hcard : init.card = n) (t : ℕ) :
    (trace init omega t).card = n := by
  have hreach :
      (NonuniformMajority
        (PhaseThreeModel.Numeric.hourIndex n) 256).Reachable
        init (trace init omega t) := by
    simpa only [TimeTheorem.trace_zero] using
      (TimeTheorem.trace_reachable init omega
        (s := 0) (t := t) (Nat.zero_le t))
  exact (Protocol.reachable_card_eq hreach).trans hcard

/-- The first Phase-7 threshold hit is no later than the finite homogeneous
Phase-7 time. -/
private theorem firstSeven_le_homogeneous
    {init : InputCfg n} {omega : InputLog n}
    {completed seven homogeneous eight M R : ℕ}
    {ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1)}
    {hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n}
    {sigma tau : Sign}
    (hpath : LemmaElevenPathReceipt (M := M) (R := R)
      init omega completed seven eight ell hell sigma tau)
    (height : EightSeedReceipt init omega seven homogeneous eight) :
    seven ≤ homogeneous := by
  have hpure :
      allPhaseExactly 7 (trace init omega homogeneous) :=
    ((homogeneousLatePhaseStart_eq_iff
      init 7 homogeneous omega).mp height.homogeneous_time).1
  have hcard : (trace init omega homogeneous).card = n :=
    trace_card_eq_population hpath.good_input.2.2 homogeneous
  have hpositive : 0 < (trace init omega homogeneous).card := by
    rw [hcard]
    have hnlarge := (time_population_bounds hpath.good_input.1).2
    omega
  obtain ⟨a, ha⟩ :=
    Multiset.card_pos_iff_exists_mem.mp hpositive
  have hsome : someGE (n := n) 7
      (trace init omega homogeneous) :=
    ⟨a, ha, by rw [hpure a ha]⟩
  have hle :
      firstPhaseSevenStart init omega ≤
        (homogeneous : WithTop ℕ) := by
    simpa only [firstPhaseSevenStart] using
      (TraceDrain.exitTime_le_iff init
        (someGE (n := n) 7) omega homogeneous).2
        ⟨homogeneous, le_rfl, hsome⟩
  rw [hpath.seven_time] at hle
  exact WithTop.coe_le_coe.mp hle

/-- Between the homogeneous Phase-7 time and the strict first-Phase-8 seed,
the actual trace is a genuine Phase-7 trace. -/
private theorem phaseSevenWin_before_firstEight
    {init : InputCfg n} {omega : InputLog n}
    {completed seven homogeneous eight M R t : ℕ}
    {ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1)}
    {hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n}
    {sigma tau : Sign}
    (hpath : LemmaElevenPathReceipt (M := M) (R := R)
      init omega completed seven eight ell hell sigma tau)
    (height : EightSeedReceipt init omega seven homogeneous eight)
    (hhomogeneous : homogeneous ≤ t) (htEight : t < eight) :
    PhaseOnlyWindows.Phase7Win
      (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
      n (trace init omega t) := by
  have hpure :
      allPhaseExactly 7 (trace init omega homogeneous) :=
    ((homogeneousLatePhaseStart_eq_iff
      init 7 homogeneous omega).mp height.homogeneous_time).1
  have hreach :=
    TimeTheorem.trace_reachable init omega hhomogeneous
  have hlower :=
    PhaseOneDrainStopping.phase_lower_reachable
      (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
      7 (trace init omega homogeneous) (trace init omega t)
      hreach (fun a ha => by rw [hpure a ha])
  refine ⟨trace_card_eq_population hpath.good_input.2.2 t, ?_⟩
  intro a ha
  have hlo : 7 ≤ a.phase.val := hlower a ha
  have hhi : a.phase.val < 8 :=
    height.eight_seed.2 t htEight a ha
  omega

/-- The Lemma-11 receipt supplies the exact consumer used by `LateLemmaTwelveSingleBand` at every
strictly pre-8 time after homogeneity. -/
private theorem phaseSevenBandConsumer_at
    {init : InputCfg n} {omega : InputLog n}
    {completed seven homogeneous eight M R t : ℕ}
    {ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1)}
    {hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n}
    {sigma tau : Sign}
    (hpath : LemmaElevenPathReceipt (M := M) (R := R)
      init omega completed seven eight ell hell sigma tau)
    (height : EightSeedReceipt init omega seven homogeneous eight)
    (hhomogeneous : homogeneous ≤ t) (htEight : t < eight) :
    PhaseSevenBandConsumer n M sigma ell (trace init omega t) := by
  have hsevenHomogeneous :=
    firstSeven_le_homogeneous hpath height
  have hsevenT : seven ≤ t :=
    hsevenHomogeneous.trans hhomogeneous
  exact
    { genuine :=
        phaseSevenWin_before_firstEight
          hpath height hhomogeneous htEight
      simple_scaled :=
        hpath.simple_at (hpath.order.1.trans hsevenT) htEight.le
      ledger := hpath.fuelLedger_at hsevenT htEight.le }

/-- The initial lower prefix remains clear at every such receipt time. -/
private theorem baseBandClear_at
    {init : InputCfg n} {omega : InputLog n}
    {completed seven homogeneous eight M R t : ℕ}
    {ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1)}
    {hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n}
    {sigma tau : Sign}
    (hpath : LemmaElevenPathReceipt (M := M) (R := R)
      init omega completed seven eight ell hell sigma tau)
    (height : EightSeedReceipt init omega seven homogeneous eight)
    (hhomogeneous : homogeneous ≤ t) (htEight : t < eight) :
    BandClear
      (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
      sigma ell.val (trace init omega t) := by
  have hsevenHomogeneous :=
    firstSeven_le_homogeneous hpath height
  have hsevenT : seven ≤ t :=
    hsevenHomogeneous.trans hhomogeneous
  exact bandClear_of_noShallow sigma ell (trace init omega t)
    (hpath.noShallow_at hsevenT htEight.le)

/-- **Lemma-11 receipt route outside the three-band event.**  The timer
comparison is deliberately a premise of this file.  Strictness is necessary:
at the first Phase-8 seed the configuration need not be a genuine Phase-7
configuration. -/
theorem phaseSevenBands_empty_of_receipts
    {init : InputCfg n} {omega : InputLog n}
    {completed seven homogeneous eight M R : ℕ}
    {ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1)}
    {hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n}
    {sigma tau : Sign}
    (hpath : LemmaElevenPathReceipt (M := M) (R := R)
      init omega completed seven eight ell hell sigma tau)
    (height : EightSeedReceipt init omega seven homogeneous eight)
    (hdeadline :
      homogeneous + 3 * phaseSevenBandHorizon n < eight)
    (hgood : omega ∉ phaseSevenBandsFailure
      init M sigma ell hell) :
    PhaseOnlyWindows.Phase7Win
        (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
        n (trace init omega
          (homogeneous + 3 * phaseSevenBandHorizon n)) ∧
      bandCountN
          (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
          sigma ell
          (trace init omega
            (homogeneous + 3 * phaseSevenBandHorizon n)) = 0 ∧
      bandCountN
          (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
          sigma (middleBand ell hell)
          (trace init omega
            (homogeneous + 3 * phaseSevenBandHorizon n)) = 0 ∧
      bandCountN
          (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
          sigma (upperBand ell hell)
          (trace init omega
            (homogeneous + 3 * phaseSevenBandHorizon n)) = 0 := by
  let H := phaseSevenBandHorizon n
  let firstEnd := homogeneous + H
  let secondEnd := firstEnd + H
  let finalEnd := secondEnd + H

  have hfinalEight : finalEnd < eight := by
    dsimp [finalEnd, secondEnd, firstEnd, H]
    omega
  have hhomFinal : homogeneous ≤ finalEnd := by
    dsimp [finalEnd, secondEnd, firstEnd, H]
    omega
  have hfirstFinal : firstEnd ≤ finalEnd := by
    dsimp [finalEnd, secondEnd, firstEnd, H]
    omega
  have hsecondFinal : secondEnd ≤ finalEnd := by
    dsimp [finalEnd, secondEnd, H]
    omega
  have hhomFirst : homogeneous ≤ firstEnd := by
    dsimp [firstEnd, H]
    omega
  have hhomSecond : homogeneous ≤ secondEnd :=
    hhomFirst.trans (by
      dsimp [secondEnd, H]
      omega)
  have hhomEight : homogeneous < eight :=
    lt_of_le_of_lt hhomFinal hfinalEight
  have hfirstEight : firstEnd < eight :=
    lt_of_le_of_lt hfirstFinal hfinalEight
  have hsecondEight : secondEnd < eight :=
    lt_of_le_of_lt hsecondFinal hfinalEight

  have hgoodUnion :
      omega ∉
        phaseSevenSingleBandFailureAtPast
            init n M sigma ell ell
            (phaseSevenBandSchedule init 0) ∪
          (phaseSevenSingleBandFailureAtPast
              init n M sigma ell (middleBand ell hell)
              (phaseSevenBandSchedule init 1) ∪
            phaseSevenSingleBandFailureAtPast
              init n M sigma ell (upperBand ell hell)
              (phaseSevenBandSchedule init 2)) := by
    simpa only [phaseSevenBandsFailure] using hgood
  have hgoodBase :
      omega ∉ phaseSevenSingleBandFailureAtPast
        init n M sigma ell ell
        (phaseSevenBandSchedule init 0) := by
    intro hbad
    exact hgoodUnion (Or.inl hbad)
  have hgoodMiddle :
      omega ∉ phaseSevenSingleBandFailureAtPast
        init n M sigma ell (middleBand ell hell)
        (phaseSevenBandSchedule init 1) := by
    intro hbad
    exact hgoodUnion (Or.inr (Or.inl hbad))
  have hgoodUpper :
      omega ∉ phaseSevenSingleBandFailureAtPast
        init n M sigma ell (upperBand ell hell)
        (phaseSevenBandSchedule init 2) := by
    intro hbad
    exact hgoodUnion (Or.inr (Or.inr hbad))

  have hscheduleBase :
      phaseSevenBandSchedule init 0 omega =
        (homogeneous : WithTop ℕ) := by
    simpa using
      (phaseSevenBandSchedule_eq init 0 omega homogeneous
        height.homogeneous_time)
  have hscheduleMiddle :
      phaseSevenBandSchedule init 1 omega =
        (firstEnd : WithTop ℕ) := by
    calc
      phaseSevenBandSchedule init 1 omega =
          ((homogeneous + 1 * phaseSevenBandHorizon n : ℕ) :
            WithTop ℕ) :=
        phaseSevenBandSchedule_eq init 1 omega homogeneous
          height.homogeneous_time
      _ = (firstEnd : WithTop ℕ) := by
        congr 1
        dsimp [firstEnd, H]
        omega
  have hscheduleUpper :
      phaseSevenBandSchedule init 2 omega =
        (secondEnd : WithTop ℕ) := by
    calc
      phaseSevenBandSchedule init 2 omega =
          ((homogeneous + 2 * phaseSevenBandHorizon n : ℕ) :
            WithTop ℕ) :=
        phaseSevenBandSchedule_eq init 2 omega homogeneous
          height.homogeneous_time
      _ = (secondEnd : WithTop ℕ) := by
        congr 1
        dsimp [secondEnd, firstEnd, H]
        omega

  have hnotBaseFixed :
      omega ∉ phaseSevenSingleBandFailureAt
        init n M sigma ell ell homogeneous := by
    intro hbad
    apply hgoodBase
    exact ⟨homogeneous, hscheduleBase, hbad⟩
  have hnotMiddleFixed :
      omega ∉ phaseSevenSingleBandFailureAt
        init n M sigma ell (middleBand ell hell) firstEnd := by
    intro hbad
    apply hgoodMiddle
    exact ⟨firstEnd, hscheduleMiddle, hbad⟩
  have hnotUpperFixed :
      omega ∉ phaseSevenSingleBandFailureAt
        init n M sigma ell (upperBand ell hell) secondEnd := by
    intro hbad
    apply hgoodUpper
    exact ⟨secondEnd, hscheduleUpper, hbad⟩

  have hreadyBase :
      SingleBandReady n M sigma ell ell
        (trace init omega homogeneous) :=
    { consumer :=
        phaseSevenBandConsumer_at hpath height le_rfl hhomEight
      lower_clear :=
        baseBandClear_at hpath height le_rfl hhomEight }
  have haliveBase :
      ∀ u, homogeneous ≤ u → u < homogeneous + phaseSevenBandHorizon n →
        SingleBandReady n M sigma ell ell
          (trace init omega u) := by
    intro u hhomU huFirst
    have huEight : u < eight :=
      huFirst.trans hfirstEight
    exact
      { consumer :=
          phaseSevenBandConsumer_at hpath height hhomU huEight
        lower_clear :=
          baseBandClear_at hpath height hhomU huEight }
  have hzeroBase :
      bandCountN
          (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
          sigma ell (trace init omega firstEnd) = 0 := by
    have hz :=
      singleBand_zero_of_not_failure
        init n M sigma ell ell omega homogeneous
        hreadyBase haliveBase hnotBaseFixed
    simpa [firstEnd, H] using hz
  have hbaseClearFirst :
      BandClear
        (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
        sigma ell.val (trace init omega firstEnd) :=
    baseBandClear_at hpath height hhomFirst hfirstEight
  have hclearMiddleAtFirst :
      BandClear
        (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
        sigma (middleBand ell hell).val
        (trace init omega firstEnd) := by
    simpa [middleBand] using
      (bandClear_succ_of_count_eq_zero sigma ell
        (trace init omega firstEnd) hbaseClearFirst hzeroBase)

  have hreadyMiddle :
      SingleBandReady n M sigma ell (middleBand ell hell)
        (trace init omega firstEnd) :=
    { consumer :=
        phaseSevenBandConsumer_at hpath height hhomFirst hfirstEight
      lower_clear := hclearMiddleAtFirst }
  have haliveMiddle :
      ∀ u, firstEnd ≤ u → u < firstEnd + phaseSevenBandHorizon n →
        SingleBandReady n M sigma ell (middleBand ell hell)
          (trace init omega u) := by
    intro u hfirstU huSecond
    have hhomU : homogeneous ≤ u := hhomFirst.trans hfirstU
    have huEight : u < eight := huSecond.trans hsecondEight
    have hclearU :
        BandClear
          (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
          sigma (middleBand ell hell).val
          (trace init omega u) :=
      bandClear_trace init omega sigma (middleBand ell hell).val n
        firstEnd u hfirstU hclearMiddleAtFirst (by
          intro v hfirstV hvu
          exact phaseSevenWin_before_firstEight hpath height
            (hhomFirst.trans hfirstV)
            (hvu.trans (huSecond.trans hsecondEight)))
    exact
      { consumer :=
          phaseSevenBandConsumer_at hpath height hhomU huEight
        lower_clear := hclearU }
  have hzeroMiddle :
      bandCountN
          (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
          sigma (middleBand ell hell)
          (trace init omega secondEnd) = 0 := by
    have hz :=
      singleBand_zero_of_not_failure
        init n M sigma ell (middleBand ell hell) omega firstEnd
        hreadyMiddle haliveMiddle hnotMiddleFixed
    simpa [secondEnd, H] using hz
  have hclearMiddleAtSecond :
      BandClear
        (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
        sigma (middleBand ell hell).val
        (trace init omega secondEnd) :=
    bandClear_trace init omega sigma (middleBand ell hell).val n
      firstEnd secondEnd (by
        dsimp [secondEnd, H]
        omega) hclearMiddleAtFirst (by
          intro v hfirstV hvSecond
          exact phaseSevenWin_before_firstEight hpath height
            (hhomFirst.trans hfirstV)
            (hvSecond.trans hsecondEight))
  have hclearUpperAtSecond :
      BandClear
        (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
        sigma (upperBand ell hell).val
        (trace init omega secondEnd) := by
    simpa [middleBand, upperBand] using
      (bandClear_succ_of_count_eq_zero sigma
        (middleBand ell hell) (trace init omega secondEnd)
        hclearMiddleAtSecond hzeroMiddle)

  have hreadyUpper :
      SingleBandReady n M sigma ell (upperBand ell hell)
        (trace init omega secondEnd) :=
    { consumer :=
        phaseSevenBandConsumer_at hpath height hhomSecond hsecondEight
      lower_clear := hclearUpperAtSecond }
  have haliveUpper :
      ∀ u, secondEnd ≤ u → u < secondEnd + phaseSevenBandHorizon n →
        SingleBandReady n M sigma ell (upperBand ell hell)
          (trace init omega u) := by
    intro u hsecondU huFinal
    have hhomU : homogeneous ≤ u := hhomSecond.trans hsecondU
    have huEight : u < eight := huFinal.trans hfinalEight
    have hclearU :
        BandClear
          (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
          sigma (upperBand ell hell).val
          (trace init omega u) :=
      bandClear_trace init omega sigma (upperBand ell hell).val n
        secondEnd u hsecondU hclearUpperAtSecond (by
          intro v hsecondV hvu
          exact phaseSevenWin_before_firstEight hpath height
            (hhomSecond.trans hsecondV)
            (hvu.trans (huFinal.trans hfinalEight)))
    exact
      { consumer :=
          phaseSevenBandConsumer_at hpath height hhomU huEight
        lower_clear := hclearU }
  have hzeroUpper :
      bandCountN
          (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
          sigma (upperBand ell hell)
          (trace init omega finalEnd) = 0 := by
    have hz :=
      singleBand_zero_of_not_failure
        init n M sigma ell (upperBand ell hell) omega secondEnd
        hreadyUpper haliveUpper hnotUpperFixed
    simpa [finalEnd, H] using hz
  have hclearUpperAtFinal :
      BandClear
        (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
        sigma (upperBand ell hell).val
        (trace init omega finalEnd) :=
    bandClear_trace init omega sigma (upperBand ell hell).val n
      secondEnd finalEnd (by
        dsimp [finalEnd, H]
        omega) hclearUpperAtSecond (by
          intro v hsecondV hvFinal
          exact phaseSevenWin_before_firstEight hpath height
            (hhomSecond.trans hsecondV)
            (hvFinal.trans hfinalEight))
  have hfullClear :
      BandClear
        (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
        sigma ((upperBand ell hell).val + 1)
        (trace init omega finalEnd) :=
    bandClear_succ_of_count_eq_zero sigma (upperBand ell hell)
      (trace init omega finalEnd) hclearUpperAtFinal hzeroUpper
  have hfinalWin :
      PhaseOnlyWindows.Phase7Win
        (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
        n (trace init omega finalEnd) :=
    phaseSevenWin_before_firstEight
      hpath height hhomFinal hfinalEight
  have hfinalEq :
      finalEnd = homogeneous + 3 * phaseSevenBandHorizon n := by
    dsimp [finalEnd, secondEnd, firstEnd, H]
    omega

  rw [← hfinalEq]
  refine ⟨hfinalWin, ?_, ?_, ?_⟩
  · exact hfullClear ell (by simp [upperBand])
  · exact hfullClear (middleBand ell hell)
      (by simp [middleBand, upperBand])
  · exact hfullClear (upperBand ell hell)
      (by simp [upperBand])

/-!
THEOREM LIST
* `phaseSevenSingleBandFailureAtPast`
* `measurableSet_phaseSevenSingleBandFailureAtPast`
* `law_phaseSevenSingleBandFailureAtPast`
* `middleBand`, `upperBand`
* `phaseSevenBandSchedule`
* `phaseSevenBandSchedule_pastTime`
* `phaseSevenBandSchedule_eq`
* `phaseSevenBandsFailure`, `phaseSevenBandsBudget`
* `measurableSet_phaseSevenBandsFailure`
* `law_phaseSevenBandsFailure`
* `phaseSevenBands_empty_of_receipts`

CLOSES ITEM 1
* Uses the genuine past-time splice already in the library:
  `PhaseThreeAveragingStops.potential_drift_tail_at_pastTime`.
* Uses deterministic block endpoints after the random homogeneous Phase-7
  time.  `bandClear_stepOrSelf` and `bandClear_trace` prove that an early-cleared
  prefix stays clear while waiting for the next endpoint.

CLOSES ITEM 2
* Defines the measurable fixed-witness event `phaseSevenBandsFailure`.
* Proves
  `law init (phaseSevenBandsFailure ...) ≤ 3 * phaseSevenSingleBandBudget n`,
  i.e. exactly `3 n^(-3.64256)`.
* Outside that event, a `LemmaElevenPathReceipt` plus its synchronized
  `EightSeedReceipt` clears `ell`, `ell+1`, and `ell+2` at
  `seven' + 3 ceil(6 n ln n)`.

CARRIED PREMISES AND PRODUCERS
* `hn : 2 ≤ n`: follows from `GoodInput` via `time_population_bounds`.
* `hM : 12*n ≤ 25*M`: `StrongSeedDensity.mains_lower` in the strong seed
  receipt used by the Lemma-11 assembly.  The current public
  `LemmaElevenPathReceipt` does not retain this field, so the caller must retain
  it alongside the receipt witnesses.
* `hpath`: `LateLemmaElevenAssembly.exists_lemmaElevenPathReceipt_of_smallHistory`.
* `height`: `LateLemmaElevenFiniteTimes.exists_eightSeed_of_finiteSeven`, kept
  internally by `LateLemmaElevenAfterSeven.exists_eightSeed_and_afterSeven`;
  the current public path receipt discards it, so it is stated explicitly.
* No hypothesis quantifies over all logs or arbitrary configurations.

UNFINISHED
* The timer comparison
  `homogeneous + 3 * phaseSevenBandHorizon n < eight` is intentionally left as
  the single open premise.
* Packaging `hM` and `height` into the public Lemma-11 return tuple is an
  interface convenience, not a new mathematical estimate.
END
-/

end Ripple.PopulationProtocol.ExactMajority.LateLemmaTwelveBands

end
