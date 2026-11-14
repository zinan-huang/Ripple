-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockBulkFamily.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockObservedPassageSplice
import Mathlib.Order.Interval.Finset.Nat

/-!
# The all-level bulk-passage failure budget

Every start is observed on its own finite stopping-time fibres. Current
positive-front and Clock-density facts are required on those fibres;
neither a future environment event nor future success enters the prefix.

A family of Q such starts has failure at most Q m^(-9) times the prefix
probability. If Q is at most the population this becomes m^(-8).
The final specialization uses the existing Numeric.clockCap definition
and the cap bound in Numeric.numeric_calibration_core.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockBulkFamily

open TimeTheorem PairLog PhaseThreeClockObservedPassageSplice

variable {L : ℕ}

/-- A finite union with a uniform local coefficient. Measurability of the
individual failures is unnecessary for this outer-measure upper bound. -/
theorem finite_union_prefix_bound
    {Ω : Type*} {mΩ : MeasurableSpace Ω} (μ : Measure Ω)
    (E : Set Ω) (B : ℕ → Set Ω) (I : Finset ℕ) (r : ℝ≥0∞)
    (hlocal : ∀ ℓ ∈ I, μ (E ∩ B ℓ) ≤ r) :
    μ (E ∩ ⋃ ℓ ∈ I, B ℓ) ≤ (I.card : ℝ≥0∞) * r := by
  classical
  revert hlocal
  induction I using Finset.induction_on with
  | empty =>
      intro hlocal
      simp
  | @insert ℓ I hnot ih =>
      intro hlocal
      have hhere := hlocal ℓ (Finset.mem_insert_self ℓ I)
      have hrest := ih (fun k hk => hlocal k (Finset.mem_insert_of_mem hk))
      have hset : (⋃ k ∈ insert ℓ I, B k) = B ℓ ∪ ⋃ k ∈ I, B k := by
        ext ω
        simp
      rw [hset, Set.inter_union_distrib_left]
      calc
        μ ((E ∩ B ℓ) ∪ (E ∩ ⋃ k ∈ I, B k)) ≤
            μ (E ∩ B ℓ) + μ (E ∩ ⋃ k ∈ I, B k) := measure_union_le _ _
        _ ≤ r + (I.card : ℝ≥0∞) * r := add_le_add hhere hrest
        _ = ((insert ℓ I).card : ℝ≥0∞) * r := by
          rw [Finset.card_insert_of_notMem hnot, Nat.cast_add, Nat.cast_one]
          ring

def bulkFamilyFailure (init : Cfg L 256) (I : Finset ℕ)
    (T : ℕ → Ω L 256 → WithTop ℕ) : Set (Ω L 256) :=
  ⋃ ℓ ∈ I, observedBulkFailure init ℓ (T ℓ)

/-- Each single-level failure, with its observed prefix, is measurable in
the ambient original-law sigma algebra. Its fibres are observed at their
individual deadlines by bulk_failure_fibre_measurable. -/
theorem observed_bulk_prefix_measurable (init : Cfg L 256) (ℓ : ℕ)
    (T : Ω L 256 → WithTop ℕ) (E : Set (Ω L 256))
    (hprefix : ∀ s : ℕ, MeasurableSet[pairLogFiltration L 256 s]
      (E ∩ {ω | T ω = (s : WithTop ℕ)})) :
    MeasurableSet (E ∩ observedBulkFailure init ℓ T) := by
  have heq : E ∩ observedBulkFailure init ℓ T =
      ⋃ s : ℕ, (E ∩ {ω | T ω = (s : WithTop ℕ)}) ∩
        randomCountPassageFailure init ℓ s
          (PhaseThreeModel.Numeric.firstHitHorizon init.card) := by
    ext ω
    constructor
    · rintro ⟨he, s, hs, hb⟩
      exact Set.mem_iUnion.mpr ⟨s, ⟨he, hs⟩, hb⟩
    · intro hω
      obtain ⟨s, ⟨he, hs⟩, hb⟩ := Set.mem_iUnion.mp hω
      exact ⟨he, s, hs, hb⟩
  rw [heq]
  refine MeasurableSet.iUnion fun s => ?_
  exact ((pairLogFiltration L 256).le
    (s + PhaseThreeModel.Numeric.firstHitHorizon init.card)) _
      (bulk_failure_fibre_measurable init ℓ T E s (hprefix s))

theorem bulk_family_prefix_measurable (init : Cfg L 256)
    (I : Finset ℕ) (T : ℕ → Ω L 256 → WithTop ℕ) (E : Set (Ω L 256))
    (hprefix : ∀ ℓ ∈ I, ∀ s : ℕ, MeasurableSet[pairLogFiltration L 256 s]
      (E ∩ {ω | T ℓ ω = (s : WithTop ℕ)})) :
    MeasurableSet (E ∩ bulkFamilyFailure init I T) := by
  have heq : E ∩ bulkFamilyFailure init I T =
      ⋃ ℓ ∈ I, E ∩ observedBulkFailure init ℓ (T ℓ) := by
    ext ω
    constructor
    · rintro ⟨he, hb⟩
      obtain ⟨ℓ, hℓ⟩ := Set.mem_iUnion.mp hb
      obtain ⟨hmem, hfail⟩ := Set.mem_iUnion.mp hℓ
      exact Set.mem_iUnion.mpr ⟨ℓ, Set.mem_iUnion.mpr ⟨hmem, he, hfail⟩⟩
    · intro hω
      obtain ⟨ℓ, hℓ⟩ := Set.mem_iUnion.mp hω
      obtain ⟨hmem, he, hfail⟩ := Set.mem_iUnion.mp hℓ
      exact ⟨he, Set.mem_iUnion.mpr
        ⟨ℓ, Set.mem_iUnion.mpr ⟨hmem, hfail⟩⟩⟩
  rw [heq]
  refine MeasurableSet.iUnion fun ℓ => MeasurableSet.iUnion fun hℓ => ?_
  exact observed_bulk_prefix_measurable init ℓ (T ℓ) E (hprefix ℓ hℓ)

/-- The exact finite-family P3a budget on a common observed prefix. -/
theorem bulk_family_prefix_tail (init : Cfg L 256)
    (hm : 20 ≤ init.card) (I : Finset ℕ)
    (hlevels : ∀ ℓ ∈ I, 1 ≤ ℓ ∧ ℓ ≤ 256 * (L + 1))
    (T : ℕ → Ω L 256 → WithTop ℕ) (E : Set (Ω L 256))
    (hprefix : ∀ ℓ ∈ I, ∀ s : ℕ, MeasurableSet[pairLogFiltration L 256 s]
      (E ∩ {ω | T ℓ ω = (s : WithTop ℕ)}))
    (hstart : ∀ ℓ ∈ I, ∀ s : ℕ, ∀ ω ∈ E, T ℓ ω = (s : WithTop ℕ) →
      DensePositiveStart init ℓ ω s) :
    law init (E ∩ bulkFamilyFailure init I T) ≤
      (I.card : ℝ≥0∞) * ENNReal.ofReal (1 / (init.card : ℝ) ^ 9) * law init E := by
  have hbound := finite_union_prefix_bound (law init) E
    (fun ℓ => observedBulkFailure init ℓ (T ℓ)) I
    (ENNReal.ofReal (1 / (init.card : ℝ) ^ 9) * law init E)
    (fun ℓ hℓ => bulk_observed_passage_tail init hm ℓ
      (hlevels ℓ hℓ).1 (hlevels ℓ hℓ).2 (T ℓ) E
      (hprefix ℓ hℓ) (hstart ℓ hℓ))
  simpa only [bulkFamilyFailure, mul_assoc] using hbound

theorem family_coefficient_calibration (m q : ℕ)
    (hm : 1 ≤ m) (hq : q ≤ m) :
    (q : ℝ≥0∞) * ENNReal.ofReal (1 / (m : ℝ) ^ 9) ≤
      ENNReal.ofReal (1 / (m : ℝ) ^ 8) := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by
    exact_mod_cast (by omega : 0 < m)
  have hqE : (q : ℝ≥0∞) ≤ (m : ℝ≥0∞) := by exact_mod_cast hq
  have hprod : (m : ℝ) * (1 / (m : ℝ) ^ 9) = 1 / (m : ℝ) ^ 8 := by
    field_simp [ne_of_gt hmpos]
    <;> ring
  calc
    (q : ℝ≥0∞) * ENNReal.ofReal (1 / (m : ℝ) ^ 9) ≤
        (m : ℝ≥0∞) * ENNReal.ofReal (1 / (m : ℝ) ^ 9) :=
      mul_le_mul_right' hqE _
    _ = ENNReal.ofReal ((m : ℝ) * (1 / (m : ℝ) ^ 9)) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
    _ = _ := congrArg ENNReal.ofReal hprod

theorem bulk_family_prefix_calibrated (init : Cfg L 256)
    (hm : 20 ≤ init.card) (I : Finset ℕ)
    (hlevels : ∀ ℓ ∈ I, 1 ≤ ℓ ∧ ℓ ≤ 256 * (L + 1))
    (hI : I.card ≤ init.card)
    (T : ℕ → Ω L 256 → WithTop ℕ) (E : Set (Ω L 256))
    (hprefix : ∀ ℓ ∈ I, ∀ s : ℕ, MeasurableSet[pairLogFiltration L 256 s]
      (E ∩ {ω | T ℓ ω = (s : WithTop ℕ)}))
    (hstart : ∀ ℓ ∈ I, ∀ s : ℕ, ∀ ω ∈ E, T ℓ ω = (s : WithTop ℕ) →
      DensePositiveStart init ℓ ω s) :
    law init (E ∩ bulkFamilyFailure init I T) ≤
      ENNReal.ofReal (1 / (init.card : ℝ) ^ 8) * law init E := by
  apply (bulk_family_prefix_tail init hm I hlevels T E hprefix hstart).trans
  exact mul_le_mul_right'
    (family_coefficient_calibration init.card I.card (by omega) hI) _

/-- This is the actual existing numerical cap, specialized in the
calibration core to the admissible auxiliary value C = m. -/
theorem numeric_clockCap_le_population (m : ℕ)
    (hm : PhaseThreeModel.Numeric.populationThreshold ≤ m) :
    PhaseThreeModel.Numeric.clockCap m ≤ m := by
  have hdensity : (6 / 25 : ℝ) * (m : ℝ) ≤ (m : ℝ) := by
    have hmnonneg : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    nlinarith
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hcap, _, _⟩ :=
    PhaseThreeModel.Numeric.numeric_calibration_core
      (n := m) (C := m) hm hdensity le_rfl
  exact hcap

/-- All levels 1 through Numeric.clockCap n. The population equality is
explicit because InputCfg n fixes the state-space parameter, not its
multiset cardinality. No shape or level-birth conclusion is assumed here;
the observed start facts are precisely the displayed hypotheses. -/
theorem numeric_bulk_family_prefix_tail {n : ℕ} (init : InputCfg n)
    (hm : 20 ≤ init.card) (hcard : init.card = n)
    (hn : PhaseThreeModel.Numeric.populationThreshold ≤ n)
    (T : ℕ → InputLog n → WithTop ℕ) (E : Set (InputLog n))
    (hprefix : ∀ ℓ ∈ Finset.Icc 1 (PhaseThreeModel.Numeric.clockCap n),
      ∀ s : ℕ, MeasurableSet[pairLogFiltration _ _ s]
        (E ∩ {ω | T ℓ ω = (s : WithTop ℕ)}))
    (hstart : ∀ ℓ ∈ Finset.Icc 1 (PhaseThreeModel.Numeric.clockCap n),
      ∀ s : ℕ, ∀ ω ∈ E, T ℓ ω = (s : WithTop ℕ) →
        DensePositiveStart init ℓ ω s) :
    law init (E ∩ bulkFamilyFailure init
      (Finset.Icc 1 (PhaseThreeModel.Numeric.clockCap n)) T) ≤
      ENNReal.ofReal (1 / (init.card : ℝ) ^ 8) * law init E := by
  apply bulk_family_prefix_calibrated init hm
    (Finset.Icc 1 (PhaseThreeModel.Numeric.clockCap n)) ?_ ?_ T E hprefix hstart
  · intro ℓ hℓ
    obtain ⟨hlow, hhigh⟩ := Finset.mem_Icc.mp hℓ
    exact ⟨hlow, by
      simpa only [PhaseThreeModel.Numeric.clockCap, PhaseThreeModel.Numeric.clockHours]
        using hhigh⟩
  · rw [Nat.card_Icc, Nat.add_sub_cancel, hcard]
    exact numeric_clockCap_le_population n hn

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockBulkFamily

end
