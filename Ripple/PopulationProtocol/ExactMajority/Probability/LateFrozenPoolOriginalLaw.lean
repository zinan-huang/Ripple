-- Ripple/PopulationProtocol/ExactMajority/Probability/LateFrozenPoolOriginalLaw.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.LateFrozenPoolTail
import Ripple.PopulationProtocol.ExactMajority.Probability.LateSamplingEarlyRoles
import Ripple.PopulationProtocol.ExactMajority.Probability.LateSamplingSplice

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal

namespace Ripple.PopulationProtocol.ExactMajority.LateFrozenPoolOriginalLaw

open TimeTheorem PairLog LateF6Acceptance LateF6Hazards
open AveragingRecordedExpectation LateSamplingCalibration LateSamplingSplice
open LateSamplingFirstHit LateSamplingClassGates LateFrozenPoolTail
open LateSamplingEarlyRoles

variable {L K : ℕ}

structure SeedDensity (n M R : ℕ) : Prop where
  mains_lower : 12 * n ≤ 25 * M
  reserves_upper : 25 * R ≤ 7 * n
  total_le : M + R ≤ n

def testEvent (init : Cfg L K) (s M R : ℕ)
    (C : Fin 3 → Bias L → Prop) : ClassTestIndex M → Set (Ω L K)
  | none => EarlyRoleEvent init s M R (Nat.ceil ((init.card : ℝ) / 1000000))
  | some (i, A, k) =>
      if Nat.ceil ((init.card : ℝ) / 1000000) ≤ k.val then
        frozenFailure init s M A.val k.val (C i) (1 / 40000)
      else ∅

def prerequisiteEvent (init : Cfg L K) (s M R : ℕ)
    (C : Fin 3 → Bias L → Prop) : Set (Ω L K) :=
  ⋃ i, testEvent init s M R C i

theorem testEvent_measurable (init : Cfg L K) (s M R : ℕ)
    (C : Fin 3 → Bias L → Prop) (i : ClassTestIndex M) :
    MeasurableSet (testEvent init s M R C i) := by
  classical
  cases i with
  | none => exact earlyRoleEvent_measurable init s M R _
  | some z =>
      rcases z with ⟨i, A, k⟩
      unfold testEvent
      dsimp only
      split_ifs
      · exact frozenFailure_measurable init s M A.val k.val (C i) _
      · exact MeasurableSpace.measurableSet_empty _

theorem prerequisiteEvent_measurable (init : Cfg L K) (s M R : ℕ)
    (C : Fin 3 → Bias L → Prop) :
    MeasurableSet (prerequisiteEvent init s M R C) :=
  MeasurableSet.iUnion (testEvent_measurable init s M R C)

/-- The zero freeze-count slot is empty here. A later accepted-trial producer
can occupy that slot without changing the planned finite index or prefactor. -/
theorem recorded_prerequisites_tail (init : Cfg L K) (s M R : ℕ)
    (hd : SeedDensity init.card M R)
    (hlog : (1000000000000 : ℝ) < Real.log (init.card : ℝ))
    (C : Fin 3 → Bias L → Prop)
    (p : (i : Finset.Iic s) → Draw L K) :
    recordedFuture init s p (prerequisiteEvent init s M R C) ≤
      ENNReal.ofReal ((3 * ((M : ℝ) + 1) ^ 2 + 1) *
        Real.exp (-(init.card : ℝ) / 800000000000000)) := by
  have hlarge := logarithm_population_lower hlog
  have hn : 2 ≤ init.card := by omega
  have hM : 0 < M := by have h := hd.mains_lower; omega
  apply class_test_union_bound (recordedFuture init s p) init.card M
    (testEvent init s M R C)
  intro i
  cases i with
  | none =>
      exact recorded_early_role_tail init s M R hd.mains_lower
        hd.reserves_upper hd.total_le hlog p
  | some z =>
      rcases z with ⟨i, A, k⟩
      unfold testEvent
      dsimp only
      split_ifs with hk
      · exact frozen_test_tail init hn init.card s M A.val k.val hM
          (by omega) (by omega) hk (C i) p
      · rw [measure_empty]
        exact zero_le

/-- All non-Clock roles are the original roles throughout the observed prefix. -/
theorem prefix_main_count {n : ℕ} {init : InputCfg n} {ω : InputLog n}
    {a s T : ℕ} (h : LateF6OriginalLaw.Prefix init ω a s T)
    {u : ℕ} (hsu : s ≤ u) (huT : u ≤ T) :
    mainCount (labelsAt init ω u) = mainCount (labelsAt init ω s) := by
  apply congrArg Finset.card
  ext i
  simp only [mem_pool, Main]
  rw [h.role_between s u h.start_order hsu huT i]

theorem prefix_reserve_count {n : ℕ} {init : InputCfg n} {ω : InputLog n}
    {a s T : ℕ} (h : LateF6OriginalLaw.Prefix init ω a s T)
    {u : ℕ} (hsu : s ≤ u) (huT : u ≤ T) :
    LateF6Hazards.reserveCount (labelsAt init ω u) =
      LateF6Hazards.reserveCount (labelsAt init ω s) := by
  apply congrArg Finset.card
  ext i
  simp only [mem_pool, reserveRole]
  rw [h.role_between s u h.start_order hsu huT i]

variable {n : ℕ}

abbrev InputPrefix (n s : ℕ) :=
  RecordedPrefix (PhaseThreeModel.Numeric.hourIndex n) 256 s

abbrev ClassChoice (n : ℕ) :=
  (s : ℕ) → InputPrefix n s → Fin 3 →
    Bias (PhaseThreeModel.Numeric.hourIndex n) → Prop

def selectedMains (init : InputCfg n) (s : ℕ) (p : InputPrefix n s) : ℕ :=
  mainCount (prefixLabels init s p)

def selectedReserves (init : InputCfg n) (s : ℕ) (p : InputPrefix n s) : ℕ :=
  LateF6Hazards.reserveCount (prefixLabels init s p)

def seedPrefixes (init : InputCfg n) (s : ℕ) : Set (InputPrefix n s) :=
  {p | SeedDensity init.card (selectedMains init s p) (selectedReserves init s p)}

def selectedPrerequisites (init : InputCfg n) (C : ClassChoice n) (s : ℕ)
    (p : InputPrefix n s) : Set (InputLog n) :=
  prerequisiteEvent init s (selectedMains init s p) (selectedReserves init s p) (C s p)

/-- The finite-prefix choice may retain the original Main count, terminal
level and winning sign. The choice cannot inspect any future draw. -/
def originalPrerequisiteFailure (init : InputCfg n) (C : ClassChoice n) :
    Set (InputLog n) :=
  {ω | ∃ s : ℕ, LateF6OriginalLaw.firstFourStart init ω = (s : WithTop ℕ) ∧
    ω ∈ selectedFailure s (seedPrefixes init s) (selectedPrerequisites init C s)}

/-- Original-law prerequisite tail from the genuine first threshold-4 time.
The recorded local estimate retains the full review prefactor, and prefix
selection adds no factor for the seed time or any observed parameter. -/
theorem law_prerequisites_tail (init : InputCfg n) (hcard : init.card = n)
    (hn : timePopulationThreshold ≤ n) (C : ClassChoice n) :
    law init (originalPrerequisiteFailure init C) ≤
      ENNReal.ofReal (13 * (n : ℝ) ^ 2 *
        Real.exp (-(n : ℝ) / 800000000000000)) := by
  have hlog : (1000000000000 : ℝ) < Real.log (init.card : ℝ) := by
    simpa only [hcard] using time_threshold_logarithm hn
  apply law_stopping_selected_bound init (LateF6OriginalLaw.firstFourStart init)
    (LateF6OriginalLaw.firstFourStart_past init)
    (seedPrefixes init) (selectedPrerequisites init C)
    (fun s p => prerequisiteEvent_measurable init s _ _ (C s p))
  intro s p hp
  have hd : SeedDensity init.card (selectedMains init s p)
      (selectedReserves init s p) := hp
  have hM : selectedMains init s p ≤ init.card := by
    have h := hd.total_le
    omega
  have hlocal := recorded_prerequisites_tail init s _ _ hd hlog (C s p) p
  have hpoly := (sampling_finite_factor hM hlog).1
  have hbound := hlocal.trans (ENNReal.ofReal_le_ofReal hpoly)
  simpa only [hcard] using hbound

theorem law_prerequisites_inverse_power (init : InputCfg n) (hcard : init.card = n)
    (hn : timePopulationThreshold ≤ n) (C : ClassChoice n) :
    law init (originalPrerequisiteFailure init C) ≤
      ENNReal.ofReal (Real.rpow (n : ℝ) (-190)) := by
  have hpoly := (sampling_finite_factor (M := n) le_rfl
    (time_threshold_logarithm hn)).2
  exact (law_prerequisites_tail init hcard hn C).trans
    (ENNReal.ofReal_le_ofReal hpoly.le)

/-- Every observed frozen-pool violation is one of the deterministic tests,
even if its global floor is selected only at the later observation. -/
theorem prefix_frozen_failure_mem {init : InputCfg n} {ω : InputLog n}
    {a s T A : ℕ} (h : LateF6OriginalLaw.Prefix init ω a s T)
    (C : ClassChoice n) (i : Fin 3)
    (hd : SeedDensity init.card (mainCount (labelsAt init ω s))
      (LateF6Hazards.reserveCount (labelsAt init ω s)))
    (hA : A ≤ mainCount (labelsAt init ω s))
    (hfloor : ∀ u, s ≤ u → u ≤ T →
      A ≤ classCount (C s (frestrictLe s ω) i) (labelsAt init ω u))
    (hk : Nat.ceil ((init.card : ℝ) / 1000000) ≤ frozenCount (labelsAt init ω T))
    (hbad : ¬ FrozenFloor (C s (frestrictLe s ω) i) A
      (mainCount (labelsAt init ω s)) (1 / 40000) (labelsAt init ω T)) :
    ω ∈ originalPrerequisiteFailure init C := by
  classical
  let M := mainCount (labelsAt init ω s)
  let k := frozenCount (labelsAt init ω T)
  have hmain := prefix_main_count h h.observed le_rfl
  have hkM : k ≤ M := (frozen_le_main _).trans_eq hmain
  let j : ClassTestIndex M :=
    some (i, ⟨A, by omega⟩, ⟨k, by omega⟩)
  have hzero := prefix_start_counts_zero h
  have hbzero := (prefix_start_bad_counts_zero h (C s (frestrictLe s ω) i) ∅).1
  have hmember : ω ∈ prerequisiteEvent init s M
      (LateF6Hazards.reserveCount (labelsAt init ω s)) (C s (frestrictLe s ω)) := by
    apply Set.mem_iUnion.mpr
    refine ⟨j, ?_⟩
    change ω ∈ if Nat.ceil ((init.card : ℝ) / 1000000) ≤ k then
      frozenFailure init s M A k (C s (frestrictLe s ω) i) (1 / 40000) else ∅
    rw [if_pos hk]
    refine ⟨hzero.1, hbzero, T, h.observed, ?_, rfl, hbad⟩
    intro u hsu huT
    refine ⟨?_, prefix_main_count h hsu huT, hfloor u hsu huT⟩
    intro z
    exact h.window u (h.start_order.trans hsu) huT _
      (label_mem_trace init ω u z)
  exact ⟨s, h.four_start, hd, hmember⟩

theorem prefix_early_failure_mem {init : InputCfg n} {ω : InputLog n}
    {a s T : ℕ} (h : LateF6OriginalLaw.Prefix init ω a s T)
    (C : ClassChoice n)
    (hd : SeedDensity init.card (mainCount (labelsAt init ω s))
      (LateF6Hazards.reserveCount (labelsAt init ω s)))
    (hmain : frozenCount (labelsAt init ω T) <
      Nat.ceil ((init.card : ℝ) / 1000000))
    (hreserve : Nat.ceil ((init.card : ℝ) / 1000000) ≤
      reserveFrozenCount (labelsAt init ω T)) :
    ω ∈ originalPrerequisiteFailure init C := by
  have hzero := prefix_start_counts_zero h
  have hmember : ω ∈ prerequisiteEvent init s
      (mainCount (labelsAt init ω s)) (LateF6Hazards.reserveCount (labelsAt init ω s))
      (C s (frestrictLe s ω)) := by
    apply Set.mem_iUnion.mpr
    refine ⟨none, hzero.2.2.1, hzero.2.2.2, T, h.observed, ?_, hmain, hreserve⟩
    intro u hsu huT
    refine ⟨?_, prefix_main_count h hsu huT.le, prefix_reserve_count h hsu huT.le⟩
    intro z
    exact h.window u (h.start_order.trans hsu) huT.le _
      (label_mem_trace init ω u z)
  exact ⟨s, h.four_start, hd, hmember⟩

end Ripple.PopulationProtocol.ExactMajority.LateFrozenPoolOriginalLaw

end
