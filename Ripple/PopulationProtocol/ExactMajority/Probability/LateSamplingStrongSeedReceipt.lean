import Ripple.PopulationProtocol.ExactMajority.Probability.LateSamplingFuelFeasibilityAudit

/-!
# Strong role-density receipt from the asynchronous seed to sampling completion

The old `LateFrozenPoolOriginalLaw.SeedDensity` stores only a Main lower bound,
a Reserve upper bound, and `M + R ≤ n`.  The actual asynchronous seed has the
strictly stronger paper role split.  This file transports that split along the
actual label trace to the genuine first Phase-4 hit and to the endpoint of an
existing `LateSamplingCompletion.CompletionReceipt`.

There is no probability or conditioning argument in this file.  Every theorem
is deterministic once the genuine `AsyncEntry` and `CompletionReceipt` witnesses
are supplied.
-/

noncomputable section

namespace Ripple.PopulationProtocol.ExactMajority.LateSamplingStrongSeedReceipt

open TimeTheorem PairLog StageEventSpec
open LateF6OriginalLaw LateSamplingCompletion

variable {n : ℕ}

/-- The complete role-density data retained from `RoleSplitGood (1 / 25)`.
The Clock count is kept because it is what converts the Main lower bound into
the legacy Reserve upper bound. -/
structure StrongSeedDensity (n M C R : ℕ) : Prop where
  total_eq : M + C + R = n
  mains_lower : 12 * n ≤ 25 * M
  mains_upper : 25 * M ≤ 13 * n
  clocks_lower : 6 * n ≤ 25 * C
  clocks_upper : 25 * C ≤ 7 * n
  reserves_lower : 6 * n ≤ 25 * R

/-- The omitted legacy Reserve upper bound follows from the total and the
Main/Clock lower bounds. -/
theorem StrongSeedDensity.reserves_upper
    {n M C R : ℕ} (h : StrongSeedDensity n M C R) :
    25 * R ≤ 7 * n := by
  have htotal := h.total_eq
  have hmain := h.mains_lower
  have hclock := h.clocks_lower
  omega

/-- Forgetting the Clock population leaves at most the whole population. -/
theorem StrongSeedDensity.main_reserve_total_le
    {n M C R : ℕ} (h : StrongSeedDensity n M C R) :
    M + R ≤ n := by
  have htotal := h.total_eq
  omega

/-- Drop-in adapter for every existing row-two theorem that still asks for the
weak `LateFrozenPoolOriginalLaw.SeedDensity`. -/
theorem StrongSeedDensity.toWeakSeedDensity
    {n M C R : ℕ} (h : StrongSeedDensity n M C R) :
    LateFrozenPoolOriginalLaw.SeedDensity n M R :=
  { mains_lower := h.mains_lower
    reserves_upper := StrongSeedDensity.reserves_upper h
    total_le := StrongSeedDensity.main_reserve_total_le h }

/-- The two bounds missing from the old record, together with its Main lower
bound, in the exact form used by the corrected fuel arithmetic. -/
theorem StrongSeedDensity.paperBounds
    {n M C R : ℕ} (h : StrongSeedDensity n M C R) :
    12 * n ≤ 25 * M ∧
      25 * M ≤ 13 * n ∧
      6 * n ≤ 25 * R :=
  ⟨h.mains_lower, h.mains_upper, h.reserves_lower⟩

/-- The genuine asynchronous seed supplies the complete strong record. -/
theorem strongSeedDensity_of_asyncEntry
    {init : InputCfg n} {omega : InputLog n} {seed allThree : ℕ}
    (hentry : AsyncEntry init omega seed allThree) :
    StrongSeedDensity n
      (timeMainCount (trace init omega seed))
      (StageEventSpec.clockCount (trace init omega seed))
      (StageEventSpec.reserveCount (trace init omega seed)) := by
  have hdensity := PhaseThreeClockRegime.seed_density init omega hentry
  have htotal :=
    PhaseThreeClockRegime.role_counts_add_eq_card
      (trace init omega seed) hentry.seed_profile.final_roles
  rw [hentry.seed_profile.card_eq] at htotal
  exact
    { total_eq := htotal
      mains_lower := hdensity.1
      mains_upper := hdensity.2.1
      clocks_lower := hdensity.2.2.1
      clocks_upper := hdensity.2.2.2.1
      reserves_lower := hdensity.2.2.2.2 }

/-- The population parameter of an actual `AsyncEntry` is the cardinality of
its initial configuration. -/
theorem inputCard_eq_of_asyncEntry
    {init : InputCfg n} {omega : InputLog n} {seed allThree : ℕ}
    (hentry : AsyncEntry init omega seed allThree) :
    init.card = n := by
  have hreach :
      (NonuniformMajority
        (PhaseThreeModel.Numeric.hourIndex n) 256).Reachable
        init (trace init omega seed) := by
    simpa only [TimeTheorem.trace_zero] using
      (TimeTheorem.trace_reachable init omega
        (s := 0) (t := seed) (Nat.zero_le seed))
  have hcard : (trace init omega seed).card = init.card :=
    Protocol.reachable_card_eq hreach
  exact hcard.symm.trans hentry.seed_profile.card_eq

/-- Main labels and the trace configuration count the same role class. -/
theorem labelMainCount_eq_trace
    (init : InputCfg n) (omega : InputLog n) (t : ℕ) :
    LateF6Hazards.mainCount (labelsAt init omega t) =
      timeMainCount (trace init omega t) := by
  classical
  unfold LateF6Hazards.mainCount timeMainCount
  rw [show trace init omega t = labelCfg (labelsAt init omega t) from
    (PairLog.labelsAt_config init omega t).symm,
    PhaseThreeClockRegime.countP_role_labelCfg]
  congr 1
  ext i
  simp [LateF6Hazards.mem_pool, LateF6Hazards.Main]

/-- Reserve labels and the trace configuration count the same role class. -/
theorem labelReserveCount_eq_trace
    (init : InputCfg n) (omega : InputLog n) (t : ℕ) :
    LateF6Hazards.reserveCount (labelsAt init omega t) =
      StageEventSpec.reserveCount (trace init omega t) := by
  classical
  unfold LateF6Hazards.reserveCount LateF6Hazards.trackedCount StageEventSpec.reserveCount
  rw [show trace init omega t = labelCfg (labelsAt init omega t) from
    (PairLog.labelsAt_config init omega t).symm,
    PhaseThreeClockRegime.countP_role_labelCfg]
  congr 1
  ext i
  simp [LateF6Hazards.mem_pool, LateF6Hazards.reserveRole]

/-- `AsyncEntry.all_first` and `Prefix.all_start` are two descriptions of the
same genuine first all-Phase-3 hit. -/
theorem asyncAllThree_eq_pathAllThree
    {init : InputCfg n} {omega : InputLog n}
    {seed entryAll allThree four completed : ℕ}
    (hentry : AsyncEntry init omega seed entryAll)
    (hpath : LateF6OriginalLaw.Prefix
      init omega allThree four completed) :
    entryAll = allThree := by
  have hall :
      StageEventSpec.firstHit
        (StageEventSpec.allGE (n := n) 3)
        (trace init omega) allThree := by
    exact
      (PhaseOneDrainStopping.exitTime_eq_iff_firstHit
        init (StageEventSpec.allGE (n := n) 3)
        omega allThree).mp
        (by
          simpa only [LateF6OriginalLaw.allThreeStart] using
            hpath.all_start)
  exact PhaseThreeClockRows.firstHit_unique hentry.all_first hall

/-- Main label count is constant from all-three to every observed endpoint. -/
theorem mainCount_eq_at_allThree
    {init : InputCfg n} {omega : InputLog n}
    {allThree four completed v : ℕ}
    (hpath : LateF6OriginalLaw.Prefix
      init omega allThree four completed)
    (hallv : allThree ≤ v) (hvcompleted : v ≤ completed) :
    LateF6Hazards.mainCount (labelsAt init omega v) =
      LateF6Hazards.mainCount (labelsAt init omega allThree) := by
  apply congrArg Finset.card
  ext i
  simp only [LateF6Hazards.mem_pool, LateF6Hazards.Main]
  rw [hpath.role_between allThree v le_rfl hallv hvcompleted i]

/-- Reserve label count is constant from all-three to every observed endpoint. -/
theorem reserveCount_eq_at_allThree
    {init : InputCfg n} {omega : InputLog n}
    {allThree four completed v : ℕ}
    (hpath : LateF6OriginalLaw.Prefix
      init omega allThree four completed)
    (hallv : allThree ≤ v) (hvcompleted : v ≤ completed) :
    LateF6Hazards.reserveCount (labelsAt init omega v) =
      LateF6Hazards.reserveCount (labelsAt init omega allThree) := by
  apply congrArg Finset.card
  ext i
  simp only [LateF6Hazards.mem_pool, LateF6Hazards.reserveRole]
  rw [hpath.role_between allThree v le_rfl hallv hvcompleted i]

/-- One compact pathwise receipt.  It retains the genuine entry and completion
witnesses, the three seed/all-three counts, and the Main/Reserve label counts at
the first-four and completed snapshots. -/
structure StrongSeedReceipt
    (init : InputCfg n) (omega : InputLog n)
    (seed allThree four five completed M C R : ℕ)
    (Snapshot : InputCfg n → Prop) : Prop where
  entry : AsyncEntry init omega seed allThree
  completion : LateSamplingCompletion.CompletionReceipt
    init omega allThree four five completed Snapshot
  population : init.card = n
  seed_main : timeMainCount (trace init omega seed) = M
  seed_clock : StageEventSpec.clockCount (trace init omega seed) = C
  seed_reserve : StageEventSpec.reserveCount (trace init omega seed) = R
  all_three_main : timeMainCount (trace init omega allThree) = M
  all_three_clock : StageEventSpec.clockCount
    (trace init omega allThree) = C
  all_three_reserve : StageEventSpec.reserveCount
    (trace init omega allThree) = R
  first_four_main : LateF6Hazards.mainCount
    (labelsAt init omega four) = M
  first_four_reserve : LateF6Hazards.reserveCount
    (labelsAt init omega four) = R
  completed_main : LateF6Hazards.mainCount
    (labelsAt init omega completed) = M
  completed_reserve : LateF6Hazards.reserveCount
    (labelsAt init omega completed) = R
  density : StrongSeedDensity n M C R

/-- Main constructor with named counts.  The first-hit equality is proved,
not assumed. -/
theorem strongSeedReceipt_of_asyncEntry_completion
    {init : InputCfg n} {omega : InputLog n}
    {seed entryAll allThree four five completed M C R : ℕ}
    {Snapshot : InputCfg n → Prop}
    (hentry : AsyncEntry init omega seed entryAll)
    (hcompletion : LateSamplingCompletion.CompletionReceipt
      init omega allThree four five completed Snapshot)
    (hmain : timeMainCount (trace init omega seed) = M)
    (hclock : StageEventSpec.clockCount (trace init omega seed) = C)
    (hreserve : StageEventSpec.reserveCount (trace init omega seed) = R) :
    StrongSeedReceipt init omega seed allThree four five completed
      M C R Snapshot := by
  have hsame :=
    asyncAllThree_eq_pathAllThree hentry hcompletion.observed_path
  subst entryAll
  have hmainAll :
      timeMainCount (trace init omega allThree) = M :=
    (hentry.main_count allThree hentry.order le_rfl).trans hmain
  have hclockAll :
      StageEventSpec.clockCount (trace init omega allThree) = C :=
    (hentry.clock_count allThree hentry.order le_rfl).trans hclock
  have hreserveAll :
      StageEventSpec.reserveCount (trace init omega allThree) = R :=
    (hentry.reserve_count allThree hentry.order le_rfl).trans hreserve
  have hmainAtAll :
      LateF6Hazards.mainCount (labelsAt init omega allThree) = M :=
    (labelMainCount_eq_trace init omega allThree).trans hmainAll
  have hreserveAtAll :
      LateF6Hazards.reserveCount (labelsAt init omega allThree) = R :=
    (labelReserveCount_eq_trace init omega allThree).trans hreserveAll
  have hmainFour :
      LateF6Hazards.mainCount (labelsAt init omega four) = M :=
    (mainCount_eq_at_allThree
      (v := four) hcompletion.observed_path
      hcompletion.observed_path.start_order
      hcompletion.observed_path.observed).trans hmainAtAll
  have hreserveFour :
      LateF6Hazards.reserveCount (labelsAt init omega four) = R :=
    (reserveCount_eq_at_allThree
      (v := four) hcompletion.observed_path
      hcompletion.observed_path.start_order
      hcompletion.observed_path.observed).trans hreserveAtAll
  have hmainCompleted :
      LateF6Hazards.mainCount (labelsAt init omega completed) = M :=
    (mainCount_eq_at_allThree
      (v := completed) hcompletion.observed_path
      (hcompletion.observed_path.start_order.trans
        hcompletion.observed_path.observed)
      le_rfl).trans hmainAtAll
  have hreserveCompleted :
      LateF6Hazards.reserveCount (labelsAt init omega completed) = R :=
    (reserveCount_eq_at_allThree
      (v := completed) hcompletion.observed_path
      (hcompletion.observed_path.start_order.trans
        hcompletion.observed_path.observed)
      le_rfl).trans hreserveAtAll
  have hdensity : StrongSeedDensity n M C R := by
    simpa only [hmain, hclock, hreserve] using
      (strongSeedDensity_of_asyncEntry hentry)
  exact
    { entry := hentry
      completion := hcompletion
      population := inputCard_eq_of_asyncEntry hentry
      seed_main := hmain
      seed_clock := hclock
      seed_reserve := hreserve
      all_three_main := hmainAll
      all_three_clock := hclockAll
      all_three_reserve := hreserveAll
      first_four_main := hmainFour
      first_four_reserve := hreserveFour
      completed_main := hmainCompleted
      completed_reserve := hreserveCompleted
      density := hdensity }

/-- Canonical constructor, with the seed counts chosen definitionally. -/
theorem strongSeedReceipt_of_asyncEntry_completion_counts
    {init : InputCfg n} {omega : InputLog n}
    {seed entryAll allThree four five completed : ℕ}
    {Snapshot : InputCfg n → Prop}
    (hentry : AsyncEntry init omega seed entryAll)
    (hcompletion : LateSamplingCompletion.CompletionReceipt
      init omega allThree four five completed Snapshot) :
    StrongSeedReceipt init omega seed allThree four five completed
      (timeMainCount (trace init omega seed))
      (StageEventSpec.clockCount (trace init omega seed))
      (StageEventSpec.reserveCount (trace init omega seed))
      Snapshot := by
  exact strongSeedReceipt_of_asyncEntry_completion
    hentry hcompletion rfl rfl rfl

/-- Explicit wrapper for the already charged completion failure set.  The
`completionBase` hypothesis is exactly the still-separate producer input; this
theorem performs no conditioning and introduces no new exceptional event. -/
theorem exists_strongSeedReceipt_of_completionBase
    {init : InputCfg n} {omega : InputLog n}
    {seed entryAll : ℕ} {Snapshot : InputCfg n → Prop}
    (hentry : AsyncEntry init omega seed entryAll)
    (completionBase :
      ∀ omega',
        omega' ∉ LateSamplingCompletion.completionFailure init n →
        ∃ allThree four five completed,
          LateSamplingCompletion.CompletionReceipt
            init omega' allThree four five completed Snapshot)
    (hnot : omega ∉ LateSamplingCompletion.completionFailure init n) :
    ∃ allThree four five completed,
      StrongSeedReceipt init omega seed allThree four five completed
        (timeMainCount (trace init omega seed))
        (StageEventSpec.clockCount (trace init omega seed))
        (StageEventSpec.reserveCount (trace init omega seed))
        Snapshot := by
  obtain ⟨allThree, four, five, completed, hcompletion⟩ :=
    completionBase omega hnot
  exact ⟨allThree, four, five, completed,
    strongSeedReceipt_of_asyncEntry_completion_counts
      hentry hcompletion⟩

/-- Strong density written with the actual first-four label counts. -/
theorem StrongSeedReceipt.firstFourStrongDensity
    {init : InputCfg n} {omega : InputLog n}
    {seed allThree four five completed M C R : ℕ}
    {Snapshot : InputCfg n → Prop}
    (h : StrongSeedReceipt init omega seed allThree four five completed
      M C R Snapshot) :
    StrongSeedDensity n
      (LateF6Hazards.mainCount (labelsAt init omega four)) C
      (LateF6Hazards.reserveCount (labelsAt init omega four)) := by
  simpa only [h.first_four_main, h.first_four_reserve] using h.density

/-- Strong density written with the actual completed label counts. -/
theorem StrongSeedReceipt.completedStrongDensity
    {init : InputCfg n} {omega : InputLog n}
    {seed allThree four five completed M C R : ℕ}
    {Snapshot : InputCfg n → Prop}
    (h : StrongSeedReceipt init omega seed allThree four five completed
      M C R Snapshot) :
    StrongSeedDensity n
      (LateF6Hazards.mainCount (labelsAt init omega completed)) C
      (LateF6Hazards.reserveCount (labelsAt init omega completed)) := by
  simpa only [h.completed_main, h.completed_reserve] using h.density

/-- Legacy row-two input at the genuine first-four stopping line. -/
theorem StrongSeedReceipt.rowTwoSeedDensity
    {init : InputCfg n} {omega : InputLog n}
    {seed allThree four five completed M C R : ℕ}
    {Snapshot : InputCfg n → Prop}
    (h : StrongSeedReceipt init omega seed allThree four five completed
      M C R Snapshot) :
    LateFrozenPoolOriginalLaw.SeedDensity init.card
      (LateF6Hazards.mainCount (labelsAt init omega four))
      (LateF6Hazards.reserveCount (labelsAt init omega four)) := by
  have hdensity := StrongSeedReceipt.firstFourStrongDensity h
  have hweak := StrongSeedDensity.toWeakSeedDensity hdensity
  simpa only [h.population] using hweak

/-- The same legacy interface at the completed snapshot, for consumers whose
finite family is packaged at completion rather than first-four. -/
theorem StrongSeedReceipt.completedSeedDensity
    {init : InputCfg n} {omega : InputLog n}
    {seed allThree four five completed M C R : ℕ}
    {Snapshot : InputCfg n → Prop}
    (h : StrongSeedReceipt init omega seed allThree four five completed
      M C R Snapshot) :
    LateFrozenPoolOriginalLaw.SeedDensity init.card
      (LateF6Hazards.mainCount (labelsAt init omega completed))
      (LateF6Hazards.reserveCount (labelsAt init omega completed)) := by
  have hdensity := StrongSeedReceipt.completedStrongDensity h
  have hweak := StrongSeedDensity.toWeakSeedDensity hdensity
  simpa only [h.population] using hweak

/-- The complete Main/Reserve paper bounds at first-four. -/
theorem StrongSeedReceipt.firstFourPaperBounds
    {init : InputCfg n} {omega : InputLog n}
    {seed allThree four five completed M C R : ℕ}
    {Snapshot : InputCfg n → Prop}
    (h : StrongSeedReceipt init omega seed allThree four five completed
      M C R Snapshot) :
    12 * n ≤ 25 * LateF6Hazards.mainCount (labelsAt init omega four) ∧
      25 * LateF6Hazards.mainCount (labelsAt init omega four) ≤ 13 * n ∧
      6 * n ≤ 25 * LateF6Hazards.reserveCount
        (labelsAt init omega four) :=
  StrongSeedDensity.paperBounds
    (StrongSeedReceipt.firstFourStrongDensity h)

/-- The complete Main/Reserve paper bounds at the actual completed snapshot. -/
theorem StrongSeedReceipt.completedPaperBounds
    {init : InputCfg n} {omega : InputLog n}
    {seed allThree four five completed M C R : ℕ}
    {Snapshot : InputCfg n → Prop}
    (h : StrongSeedReceipt init omega seed allThree four five completed
      M C R Snapshot) :
    12 * n ≤ 25 * LateF6Hazards.mainCount
        (labelsAt init omega completed) ∧
      25 * LateF6Hazards.mainCount
        (labelsAt init omega completed) ≤ 13 * n ∧
      6 * n ≤ 25 * LateF6Hazards.reserveCount
        (labelsAt init omega completed) :=
  StrongSeedDensity.paperBounds
    (StrongSeedReceipt.completedStrongDensity h)

/-- Exactly the two missing inequalities requested by the corrected fuel
certificate at the completed snapshot. -/
theorem StrongSeedReceipt.correctedFuelBounds
    {init : InputCfg n} {omega : InputLog n}
    {seed allThree four five completed M C R : ℕ}
    {Snapshot : InputCfg n → Prop}
    (h : StrongSeedReceipt init omega seed allThree four five completed
      M C R Snapshot) :
    25 * LateF6Hazards.mainCount (labelsAt init omega completed) ≤ 13 * n ∧
      6 * n ≤ 25 * LateF6Hazards.reserveCount
        (labelsAt init omega completed) := by
  have hdensity := StrongSeedReceipt.completedStrongDensity h
  exact ⟨hdensity.mains_upper, hdensity.reserves_lower⟩

/-!
THEOREM LIST
* `StrongSeedDensity.reserves_upper`
* `StrongSeedDensity.main_reserve_total_le`
* `StrongSeedDensity.toWeakSeedDensity`
* `StrongSeedDensity.paperBounds`
* `strongSeedDensity_of_asyncEntry`
* `inputCard_eq_of_asyncEntry`
* `labelMainCount_eq_trace`
* `labelReserveCount_eq_trace`
* `asyncAllThree_eq_pathAllThree`
* `mainCount_eq_at_allThree`
* `reserveCount_eq_at_allThree`
* `strongSeedReceipt_of_asyncEntry_completion`
* `strongSeedReceipt_of_asyncEntry_completion_counts`
* `exists_strongSeedReceipt_of_completionBase`
* `StrongSeedReceipt.firstFourStrongDensity`
* `StrongSeedReceipt.completedStrongDensity`
* `StrongSeedReceipt.rowTwoSeedDensity`
* `StrongSeedReceipt.completedSeedDensity`
* `StrongSeedReceipt.firstFourPaperBounds`
* `StrongSeedReceipt.completedPaperBounds`
* `StrongSeedReceipt.correctedFuelBounds`

CLOSES
* Retaining `25 M ≤ 13 n` and `6 n ≤ 25 R` rather than
  weakening immediately to the old `SeedDensity`.
* Deterministic transport from the genuine asynchronous seed, through the
  unique genuine all-three hit, to the actual first-four and completed label
  snapshots.
* A literal drop-in old-`SeedDensity` adapter for the row-two finite family.
* A literal completed-snapshot pair of inequalities for the corrected
  branch-indexed fuel certificate.
* No new failure set and no conditional probability law.

UNFINISHED
* Constructing the `completionBase` producer remains the existing row-3 input;
  `LateSamplingRowTwoConsumer.CompletionProducer.base` has exactly this role.
* The repaired row-two four-inequality class cover, including its threshold
  accepted counter and sentinel boundary, remains a separate item.
* The corrected fuel branch selector and sharp adjacent-union arithmetic remain
  later items.  This receipt supplies their missing role bounds only.
END
-/

end Ripple.PopulationProtocol.ExactMajority.LateSamplingStrongSeedReceipt

end
