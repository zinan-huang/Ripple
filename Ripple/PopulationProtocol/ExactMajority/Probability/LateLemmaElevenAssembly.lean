-- Ripple/PopulationProtocol/ExactMajority/Probability/LateLemmaElevenAssembly.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.LateLemmaElevenAfterSeven

/-!
# Lemma 11: charged failure union, synchronized receipt, and all-time bounds

Declarations used from
`LateLemmaElevenFiniteTimes.lean`:

* `phaseSixUpperTimerFailure`, `phaseSevenHomogeneousFailure`,
  `phaseSevenUpperTimerFailure`;
* their measurable-set and unconditional-law theorems;
* `SevenFiniteReceipt`, `EightSeedReceipt`;
* `exists_lemmaElevenEntry_and_finiteSeven` and
  `exists_eightSeed_of_finiteSeven`.

Declarations used from
`LateLemmaElevenAfterSeven.lean`:

* `phaseSixSevenCreditReachable_afterSeven`;
* `exists_eightSeed_and_afterSeven`.

Declarations used here:

* `lemmaElevenEntry_of_completed_receipts`;
* `lemmaElevenBeforeSeven_of_strongReceipt`;
* `exists_completedFuelLedger_of_smallHistory`;
* the selected-level Phase-6 drain adapters
  `correctedCompatibleFuelReceipt_of_strong`,
  `phaseSixPaperStart_of_correctedReceipt`,
  `producedN16LevelEvent_of_receipts`,
  `not_downstreamFailures_of_producedLevel`, and
  `phaseSixPaperDrainReceipt_of_start`;
* `no_shallow_main_at_firstPhaseSeven_of_receipt`;
* `LemmaElevenPathReceipt.credit_at`, `.simple_at`, and
  `majorityBlock_scaled_806_of_simple`.

The auxiliary call to `LateLemmaElevenFiniteTimes` is used only to identify the unique finite first
Phase-7 time and its exact seed.  Entry, before-seven transport, and the
selected drain are rebuilt from one single completed-snapshot receipt, so
`completed`, `ell`, `sigma`, `tau`, `M`, and `R` are definitionally the same
witnesses in the final `LemmaElevenPathReceipt`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder Set
open scoped ENNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.LateLemmaElevenAssembly

open TimeTheorem PairLog StageEventSpec
open LateF6OriginalLaw
open LateStrengthening
open LateMixedFuel LateMixedFiveSixWindow
open LateSamplingCompletion LateSamplingSeedReceipt
open LateSamplingStrongSeedReceipt
open LateSamplingStrongReceiptProducer
open LatePhaseSixDrainSelectedLevel
open LatePhaseSixDrainPaperNumerics
open LatePhaseSixDrainPaperTimeline
open LateBiasedResourceCredit
open LateBiasedResourceCreditPhaseSeven
open LateBiasedResourceCreditPath
open LateLemmaElevenEntry
open LateLemmaElevenBeforeSeven
open LateLemmaElevenFiniteTimes
open LateLemmaElevenAfterSeven
open Phase7MajorityBlockLedger

variable {n : ℕ}

/-! ## The exact producer union and its measurable charged hull -/

/-- Literal union of the four producer failures.  The Phase-7 spread failure
is already the first summand of `phaseSevenHomogeneousFailure`, so it must not
be added a second time. -/
def lemmaElevenProducerFailure
    (init : InputCfg n) : Set (InputLog n) :=
  smallGapPhaseSixDrainFailure init ∪
    (phaseSixUpperTimerFailure init ∪
      (phaseSevenHomogeneousFailure init ∪
        phaseSevenUpperTimerFailure init))

/-- Measurable charged version of the exact producer union.  The hull adds no
probability: `measure_toMeasurable` gives literal equality under `law init`. -/
noncomputable def lemmaElevenFailure
    (init : InputCfg n) : Set (InputLog n) :=
  toMeasurable (law init) (lemmaElevenProducerFailure init)

/-- Explicit total charge: the complete small-gap Phase-6 charge, two
upper-timer `n⁻⁵` charges, and the Phase-7 spread plus guarded lower-timer
charge. -/
noncomputable def lemmaElevenFailureCharge (n : ℕ) : ℝ≥0∞ :=
  smallGapPhaseSixDrainCharge n +
    (ENNReal.ofReal (1 / (n : ℝ) ^ 5) +
      ((ENNReal.ofReal
          (Real.exp 3 * Real.rpow (n : ℝ) (1 - (3 : ℝ))) +
        ENNReal.ofReal
          (Real.rpow (n : ℝ) (-(103 / 50 : ℝ)))) +
        ENNReal.ofReal (1 / (n : ℝ) ^ 5)))

theorem measurableSet_lemmaElevenFailure
    (init : InputCfg n) :
    MeasurableSet (lemmaElevenFailure init) := by
  unfold lemmaElevenFailure
  exact measurableSet_toMeasurable _ _

theorem lemmaElevenProducerFailure_subset_failure
    (init : InputCfg n) :
    lemmaElevenProducerFailure init ⊆ lemmaElevenFailure init := by
  unfold lemmaElevenFailure
  exact subset_toMeasurable _ _

theorem law_lemmaElevenFailure_eq_producerFailure
    (init : InputCfg n) :
    law init (lemmaElevenFailure init) =
      law init (lemmaElevenProducerFailure init) := by
  unfold lemmaElevenFailure
  exact measure_toMeasurable _

theorem law_lemmaElevenProducerFailure
    (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init) :
    law init (lemmaElevenProducerFailure init) ≤
      lemmaElevenFailureCharge n := by
  unfold lemmaElevenProducerFailure
  calc
    law init
        (smallGapPhaseSixDrainFailure init ∪
          (phaseSixUpperTimerFailure init ∪
            (phaseSevenHomogeneousFailure init ∪
              phaseSevenUpperTimerFailure init))) ≤
      law init (smallGapPhaseSixDrainFailure init) +
        law init
          (phaseSixUpperTimerFailure init ∪
            (phaseSevenHomogeneousFailure init ∪
              phaseSevenUpperTimerFailure init)) :=
      measure_union_le _ _
    _ ≤ lemmaElevenFailureCharge n := by
      unfold lemmaElevenFailureCharge
      refine add_le_add
        (law_smallGapPhaseSixDrainFailure init hinput) ?_
      calc
        law init
            (phaseSixUpperTimerFailure init ∪
              (phaseSevenHomogeneousFailure init ∪
                phaseSevenUpperTimerFailure init)) ≤
          law init (phaseSixUpperTimerFailure init) +
            law init
              (phaseSevenHomogeneousFailure init ∪
                phaseSevenUpperTimerFailure init) :=
          measure_union_le _ _
        _ ≤ ENNReal.ofReal (1 / (n : ℝ) ^ 5) +
            (law init (phaseSevenHomogeneousFailure init) +
              law init (phaseSevenUpperTimerFailure init)) :=
          add_le_add
            (law_phaseSixUpperTimerFailure init hinput)
            (measure_union_le _ _)
        _ ≤ ENNReal.ofReal (1 / (n : ℝ) ^ 5) +
            ((ENNReal.ofReal
                (Real.exp 3 * Real.rpow (n : ℝ) (1 - (3 : ℝ))) +
              ENNReal.ofReal
                (Real.rpow (n : ℝ) (-(103 / 50 : ℝ)))) +
              ENNReal.ofReal (1 / (n : ℝ) ^ 5)) :=
          add_le_add le_rfl
            (add_le_add
              (law_phaseSevenHomogeneousFailure init hinput)
              (law_phaseSevenUpperTimerFailure init hinput))

theorem law_lemmaElevenFailure
    (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init) :
    law init (lemmaElevenFailure init) ≤
      lemmaElevenFailureCharge n := by
  rw [law_lemmaElevenFailure_eq_producerFailure]
  exact law_lemmaElevenProducerFailure init hinput

/-! ## One synchronized construction -/

/-- Core constructor under the literal four-producer union. -/
theorem exists_lemmaElevenPathReceipt_of_not_producerFailure
    {init : InputCfg n}
    (hinput : ThresholdEpidemic.GoodInput n init)
    {omega : InputLog n}
    (hsmall : omega ∈ smallHistory init)
    (hgood : omega ∉ lemmaElevenProducerFailure init) :
    ∃ completed seven eight : ℕ,
      ∃ ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1),
      ∃ hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n,
      ∃ sigma tau : Sign, ∃ M R : ℕ,
        LemmaElevenPathReceipt (M := M) (R := R)
          init omega completed seven eight ell hell sigma tau := by
  have hselected :
      omega ∉ smallGapPhaseSixDrainFailure init := by
    intro hbad
    exact hgood (Or.inl hbad)
  have hphaseSixUpper :
      omega ∉ phaseSixUpperTimerFailure init := by
    intro hbad
    exact hgood (Or.inr (Or.inl hbad))
  have hphaseSevenHomogeneous :
      omega ∉ phaseSevenHomogeneousFailure init := by
    intro hbad
    exact hgood (Or.inr (Or.inr (Or.inl hbad)))
  have hphaseSevenUpper :
      omega ∉ phaseSevenUpperTimerFailure init := by
    intro hbad
    exact hgood (Or.inr (Or.inr (Or.inr hbad)))

  have hnotSnapshot :
      omega ∉ smallRowTwoSnapshotProductionFailure init := by
    intro hbad
    exact hselected (Or.inl hbad)
  have hnotMixed : omega ∉ mixedFailure init := by
    intro hbad
    exact hselected (Or.inr (Or.inl hbad))
  have hnotSeed :
      omega ∉ LateMixedFiveSixWindowTailWf.phaseSixSeedFailure init := by
    intro hbad
    exact hselected (Or.inr (Or.inr (Or.inl hbad)))
  have hnotSelected :
      omega ∉ anySelectedProducedLevelPhaseSixFailure init := by
    intro hbad
    exact hselected (Or.inr (Or.inr (Or.inr hbad)))

  obtain ⟨seed, allThree, four, ell, hell, tau, five, completed,
      _history, hseed, hstrong, _ledger⟩ :=
    exists_completedFuelLedger_of_smallHistory
      hinput hsmall hnotSnapshot
  obtain ⟨sixHomogeneous, hmixed⟩ :=
    mixedFiveSixPrefix_of_not_mixedFailure
      hnotMixed hstrong.completion

  have hentry :
      LemmaElevenEntry
        (M := timeMainCount (trace init omega seed))
        (R := StageEventSpec.reserveCount (trace init omega seed))
        ell hell (oppositeSign tau) tau
        (trace init omega completed) :=
    lemmaElevenEntry_of_completed_receipts
      (M := timeMainCount (trace init omega seed))
      (C := StageEventSpec.clockCount (trace init omega seed))
      (R := StageEventSpec.reserveCount (trace init omega seed))
      hinput ell hell tau hseed hstrong hnotSnapshot

  /- `LateLemmaElevenFiniteTimes` supplies the unique finite first-seven time and exact seed.  Its
  auxiliary entry witnesses are discarded; all payload witnesses below remain
  those from `hstrong`. -/
  obtain ⟨seedOther, allThreeOther, fourOther, ellOther, hellOther,
      sigmaOther, tauOther, fiveOther, completedOther, homogeneousOther,
      seven, mainOther, reserveOther, signOther, mainEqOther,
      reserveEqOther, entryOther, sevenOther⟩ :=
    exists_lemmaElevenEntry_and_finiteSeven
      hinput hsmall hselected hphaseSixUpper

  have hallThreeSeven : allThree < seven := by
    have hh := sevenOther.all_three_lt
    rw [hstrong.completion.observed_path.all_start] at hh
    exact WithTop.coe_lt_coe.mp hh
  have hcompletedSeven : completed ≤ seven := by
    by_contra hbad
    have hsevenCompleted : seven ≤ completed := by omega
    obtain ⟨a, ha, hphase⟩ := sevenOther.seven_seed.1
    have hupper :=
      hstrong.completion.observed_path.before_six
        seven hallThreeSeven.le hsevenCompleted a ha
    omega

  have hseven :
      SevenFiniteReceipt init omega completed sixHomogeneous seven :=
    { mixed := hmixed
      seven_time := sevenOther.seven_time
      seven_seed := sevenOther.seven_seed
      completed_le := hcompletedSeven
      all_three_lt := sevenOther.all_three_lt }

  have hbefore :
      ∀ t, completed ≤ t → t ≤ seven →
        PhaseFiveSixCreditReachable init n
          (trace init omega completed) (trace init omega t) :=
    lemmaElevenBeforeSeven_of_strongReceipt
      hstrong hmixed hseven.seven_time

  /- Rebuild the Phase-6 drain at the very same `ell` carried by `hentry`. -/
  have hnlarge : 2 ≤ n := by
    have hlarge := (time_population_bounds hinput.1).2
    omega
  obtain ⟨seedSix, hSix⟩ :=
    LateMixedFiveSixWindowTailWf.phaseSixSeedReceipt_of_not_failure
      hnlarge init omega completed
      hstrong.completion.completed_at hnotSeed
  have hcompatible :=
    correctedCompatibleFuelReceipt_of_strong
      hinput.1 ell hell tau hstrong hseed hmixed
  have hstart :=
    phaseSixPaperStart_of_correctedReceipt hcompatible hSix
  have hlevel : omega ∈ producedN16LevelEvent init ell :=
    producedN16LevelEvent_of_receipts ell tau hstrong hseed
  obtain ⟨hnotSpread, hnotTimer, hnotDrain⟩ :=
    not_downstreamFailures_of_producedLevel
      init ell hell hlevel hnotSelected
  obtain ⟨endpoint, hreceipt⟩ :=
    phaseSixPaperDrainReceipt_of_start
      init hinput ell hell hstart hnotSpread hnotTimer hnotDrain
  have hnoShallow :
      NoShallowMain ell (trace init omega seven) := by
    simpa only [NoShallowMain] using
      (no_shallow_main_at_firstPhaseSeven_of_receipt
        hreceipt hseven.seven_time)

  obtain ⟨sevenHomogeneous, eight, height, hafter⟩ :=
    exists_eightSeed_and_afterSeven
      hinput hseven hphaseSevenHomogeneous hphaseSevenUpper

  refine ⟨completed, seven, eight, ell, hell,
    oppositeSign tau, tau,
    timeMainCount (trace init omega seed),
    StageEventSpec.reserveCount (trace init omega seed), ?_⟩
  exact
    { good_input := hinput
      small_history := hsmall
      selected_good := hselected
      order := ⟨hcompletedSeven, height.seven_le_eight⟩
      seven_time := hseven.seven_time
      eight_seed := height.eight_seed
      entry := hentry
      before_seven := hbefore
      no_shallow_seven := hnoShallow
      after_seven := hafter }

/-- Public constructor under the measurable charged event. -/
theorem exists_lemmaElevenPathReceipt_of_smallHistory
    {init : InputCfg n}
    (hinput : ThresholdEpidemic.GoodInput n init)
    {omega : InputLog n}
    (hsmall : omega ∈ smallHistory init)
    (hgood : omega ∉ lemmaElevenFailure init) :
    ∃ completed seven eight : ℕ,
      ∃ ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1),
      ∃ hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n,
      ∃ sigma tau : Sign, ∃ M R : ℕ,
        LemmaElevenPathReceipt (M := M) (R := R)
          init omega completed seven eight ell hell sigma tau := by
  apply exists_lemmaElevenPathReceipt_of_not_producerFailure
    hinput hsmall
  intro hbad
  exact hgood
    (lemmaElevenProducerFailure_subset_failure init hbad)

/-! ## Lemma 11 all-time conclusion -/

/-- From completion through the first Phase-8 seed, equation (49) has the
scaled `.544 M` floor and equation (52) has the literal scaled block-count
floor `.806 M`. -/
theorem lemmaEleven_bounds_of_smallHistory
    {init : InputCfg n}
    (hinput : ThresholdEpidemic.GoodInput n init)
    {omega : InputLog n}
    (hsmall : omega ∈ smallHistory init)
    (hgood : omega ∉ lemmaElevenFailure init) :
    ∃ completed eight : ℕ,
      ∃ ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1),
      ∃ hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n,
      ∃ sigma tau : Sign, ∃ M R : ℕ,
        completed ≤ eight ∧
          ∀ t, completed ≤ t → t ≤ eight →
            (544 : ℤ) * (M : ℤ) ≤
                1000 * lateBiasedResourceCredit sigma ell hell
                  (trace init omega t) ∧
              806 * M ≤
                1000 * majorityBlockCount sigma ell.val
                  (trace init omega t) := by
  obtain ⟨completed, seven, eight, ell, hell, sigma, tau, M, R,
      hpath⟩ :=
    exists_lemmaElevenPathReceipt_of_smallHistory
      hinput hsmall hgood
  refine ⟨completed, eight, ell, hell, sigma, tau, M, R,
    hpath.order.1.trans hpath.order.2, ?_⟩
  intro t hcompleted htEight
  refine ⟨hpath.credit_at hcompleted htEight, ?_⟩
  exact majorityBlock_scaled_806_of_simple
    sigma ell M (trace init omega t)
    (hpath.simple_at hcompleted htEight)

/-!
THEOREM LIST
* `lemmaElevenProducerFailure`
* `lemmaElevenFailure`, `lemmaElevenFailureCharge`
* `measurableSet_lemmaElevenFailure`
* `lemmaElevenProducerFailure_subset_failure`
* `law_lemmaElevenFailure_eq_producerFailure`
* `law_lemmaElevenProducerFailure`, `law_lemmaElevenFailure`
* `exists_lemmaElevenPathReceipt_of_not_producerFailure`
* `exists_lemmaElevenPathReceipt_of_smallHistory`
* `lemmaEleven_bounds_of_smallHistory`

CLOSES
* Item 1, corrected interface: the exact four-producer union is retained
  literally, and its measurable equal-law hull is the public charged event.
  There is no fifth stochastic summand.
* Item 2: one synchronized `LemmaElevenPathReceipt`; entry, before-seven,
  selected drain, and after-seven use the same literal witnesses.
* Item 3: `.544 M` for `J` and the scaled `.806 M` majority-block count at
  every time from the completed snapshot through the exact first Phase-8 seed.

CARRIED PREMISES AND PRODUCERS
* `hinput : GoodInput n init` and `hsmall : omega ∈ smallHistory init` are the
  two caller inputs.
* Complement of `smallGapPhaseSixDrainFailure` produces the completed row-two
  receipt, mixed 5/6 prefix, Phase-6 seed receipt, and selected-level drain.
* Complement of `phaseSixUpperTimerFailure` produces a finite exact first
  Phase-7 seed through `LateLemmaElevenFiniteTimes`.
* Complement of `phaseSevenHomogeneousFailure` produces threshold-7 spread and
  guarded lower-timer protection; complement of
  `phaseSevenUpperTimerFailure` produces the finite exact first Phase-8 seed.
* `LateLemmaElevenAfterSeven` turns the two finite receipts into the source-guarded after-seven
  route.  No premise ranges over all logs or arbitrary configurations.

UNFINISHED
* No mathematical item in Lemma 11 is intentionally omitted.
* The exact raw union is not separately asserted measurable because the library does not export measurability for the complete nested Phase-6 producer
  hierarchy; `toMeasurable` is an equal-law, stronger-complement repair rather
  than a new probabilistic assumption.
END
-/

end Ripple.PopulationProtocol.ExactMajority.LateLemmaElevenAssembly

end
