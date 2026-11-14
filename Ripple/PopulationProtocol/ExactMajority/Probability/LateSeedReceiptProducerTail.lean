-- Ripple/PopulationProtocol/ExactMajority/Probability/LateSeedReceiptProducerTail.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.LateSeedReceiptProducer
import Ripple.PopulationProtocol.ExactMajority.Probability.LateSeedSparseEntry

/-!
# Original-law N16 receipt producer tail

The successful-history predicate remains inside the measured event.  The first-seed
safety event and all test tails are charged under the original law; no future-success
conditioning is introduced.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.LateStrengthening

open TimeTheorem StageEventSpec
open AveragingSparseEntry LateSamplingSeedReceipt

variable {n : ℕ}

/-- Failure of the retained-credit receipt at the genuine first Phase-4 seed. -/
def lateSamplingSeedProducerFailure (init : InputCfg n) : Set (InputLog n) :=
  {ω | ∃ S T ρ : ℕ,
    successfulHistory (reviewedStageEvents n init) ω S T ρ ∧
    0 < gapMagnitude init ∧
    40 * gapMagnitude init < timeMainCount (trace init ω S) ∧
    ¬ ∃ ell σ,
      LateSamplingSeedReceipt init
        (timeMainCount (trace init ω S)) ell σ
        (trace init ω ρ)}

/-- The same failure with safety asserted at the exact genuine Phase-3 seed.
`SafeSparseSeed init ω S` is a prefix event at `S`. -/
def lateSamplingSeedProducerSafeFailure
    (init : InputCfg n) : Set (InputLog n) :=
  {ω | ∃ S T ρ : ℕ,
    successfulHistory (reviewedStageEvents n init) ω S T ρ ∧
    0 < gapMagnitude init ∧
    40 * gapMagnitude init < timeMainCount (trace init ω S) ∧
    SafeSparseSeed init ω S ∧
    ¬ ∃ ell σ,
      LateSamplingSeedReceipt init
        (timeMainCount (trace init ω S)) ell σ
        (trace init ω ρ)}

/-- Rewrite lemma for the unconditioned receipt failure event. -/
theorem mem_lateSamplingSeedProducerFailure_iff
    (init : InputCfg n) (ω : InputLog n) :
    ω ∈ lateSamplingSeedProducerFailure init ↔
      ∃ S T ρ : ℕ,
        successfulHistory (reviewedStageEvents n init) ω S T ρ ∧
        0 < gapMagnitude init ∧
        40 * gapMagnitude init < timeMainCount (trace init ω S) ∧
        ¬ ∃ ell σ,
          LateSamplingSeedReceipt init
            (timeMainCount (trace init ω S)) ell σ
            (trace init ω ρ) :=
  Iff.rfl

/-- Rewrite lemma for the exact-seed prefix form. -/
theorem mem_lateSamplingSeedProducerSafeFailure_iff
    (init : InputCfg n) (ω : InputLog n) :
    ω ∈ lateSamplingSeedProducerSafeFailure init ↔
      ∃ S T ρ : ℕ,
        successfulHistory (reviewedStageEvents n init) ω S T ρ ∧
        0 < gapMagnitude init ∧
        40 * gapMagnitude init < timeMainCount (trace init ω S) ∧
        SafeSparseSeed init ω S ∧
        ¬ ∃ ell σ,
          LateSamplingSeedReceipt init
            (timeMainCount (trace init ω S)) ell σ
            (trace init ω ρ) :=
  Iff.rfl

theorem lateSamplingSeedProducerFailure_subset_smallHistory
    (init : InputCfg n) :
    lateSamplingSeedProducerFailure init ⊆ smallHistory init := by
  intro ω hω
  rw [mem_lateSamplingSeedProducerFailure_iff init ω] at hω
  obtain ⟨S, T, ρ, hhistory, hnonzero, hgap, _⟩ := hω
  exact ⟨S, T, ρ, hhistory, hnonzero, hgap⟩

/-- Intersecting with the existential sparse-entry event selects the same genuine
seed `S`; it does not introduce a later substitute seed. -/
theorem lateSamplingSeedProducerSafeFailure_eq
    (init : InputCfg n) :
    lateSamplingSeedProducerSafeFailure init =
      lateSamplingSeedProducerFailure init ∩ safeSparseEntry init := by
  ext ω
  rw [mem_lateSamplingSeedProducerSafeFailure_iff init ω,
    Set.mem_inter_iff,
    mem_lateSamplingSeedProducerFailure_iff init ω]
  constructor
  · rintro ⟨S, T, ρ, hhistory, hnonzero, hgap, hsafe, hbad⟩
    exact
      ⟨⟨S, T, ρ, hhistory, hnonzero, hgap, hbad⟩,
        ⟨S, hsafe⟩⟩
  · rintro ⟨⟨S, T, ρ, hhistory, hnonzero, hgap, hbad⟩, hsafe⟩
    exact
      ⟨S, T, ρ, hhistory, hnonzero, hgap,
        safeSparseSeed_at_successfulHistory hhistory hsafe, hbad⟩

/-- The safe-seed producer charge.  The three supplied sets are the prefix-spliced
failures selected by the later global induction. -/
theorem late_sampling_seed_receipt_safe_estimate
    (init : InputCfg n)
    (protectedTestFailure nearTestFailure oldIndexFailure : Set (InputLog n))
    (hcover :
      lateSamplingSeedProducerSafeFailure init ⊆
        protectedTestFailure ∪ (nearTestFailure ∪ oldIndexFailure))
    (hprotected :
      law init protectedTestFailure ≤
        ENNReal.ofReal (1 / (n : ℝ) ^ 4))
    (hnear :
      law init nearTestFailure ≤
        ENNReal.ofReal (1 / (n : ℝ) ^ 4))
    (hold :
      law init oldIndexFailure ≤
        ENNReal.ofReal
          (Real.rpow (n : ℝ) (-(207 / 100 : ℝ)))) :
    law init (lateSamplingSeedProducerSafeFailure init) ≤
      ENNReal.ofReal
        (2 / (n : ℝ) ^ 4 +
          Real.rpow (n : ℝ) (-(207 / 100 : ℝ))) := by
  have hx : 0 ≤ 1 / (n : ℝ) ^ 4 := by positivity
  have hz :
      0 ≤ Real.rpow (n : ℝ) (-(207 / 100 : ℝ)) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  calc
    law init (lateSamplingSeedProducerSafeFailure init) ≤
        law init (protectedTestFailure ∪
          (nearTestFailure ∪ oldIndexFailure)) :=
      measure_mono hcover
    _ ≤ law init protectedTestFailure +
        law init (nearTestFailure ∪ oldIndexFailure) :=
      measure_union_le _ _
    _ ≤ law init protectedTestFailure +
        (law init nearTestFailure + law init oldIndexFailure) :=
      add_le_add le_rfl (measure_union_le _ _)
    _ ≤ ENNReal.ofReal (1 / (n : ℝ) ^ 4) +
        (ENNReal.ofReal (1 / (n : ℝ) ^ 4) +
          ENNReal.ofReal
            (Real.rpow (n : ℝ) (-(207 / 100 : ℝ)))) :=
      add_le_add hprotected (add_le_add hnear hold)
    _ = ENNReal.ofReal
        (2 / (n : ℝ) ^ 4 +
          Real.rpow (n : ℝ) (-(207 / 100 : ℝ))) := by
      have hinner := (ENNReal.ofReal_add hx hz).symm
      have houter :=
        (ENNReal.ofReal_add hx (add_nonneg hx hz)).symm
      rw [hinner, houter]
      congr 1
      ring

/-- Item 1: the receipt-valued N16 producer in the original-law form consumed
by N18 row 2.  The successful history remains an intersection in the measured
set, and `ρ` is its genuine first Phase-4 seed. -/
theorem late_sampling_seed_receipt_estimate
    (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init)
    (protectedTestFailure nearTestFailure oldIndexFailure : Set (InputLog n))
    (hcover :
      lateSamplingSeedProducerSafeFailure init ⊆
        protectedTestFailure ∪ (nearTestFailure ∪ oldIndexFailure))
    (hprotected :
      law init protectedTestFailure ≤
        ENNReal.ofReal (1 / (n : ℝ) ^ 4))
    (hnear :
      law init nearTestFailure ≤
        ENNReal.ofReal (1 / (n : ℝ) ^ 4))
    (hold :
      law init oldIndexFailure ≤
        ENNReal.ofReal
          (Real.rpow (n : ℝ) (-(207 / 100 : ℝ)))) :
    law init
      {ω | ∃ S T ρ : ℕ,
        successfulHistory (reviewedStageEvents n init) ω S T ρ ∧
        0 < gapMagnitude init ∧
        40 * gapMagnitude init < timeMainCount (trace init ω S) ∧
        ¬ ∃ ell σ,
          LateSamplingSeedReceipt init
            (timeMainCount (trace init ω S)) ell σ
            (trace init ω ρ)} ≤
      ENNReal.ofReal
        (2 / (n : ℝ) ^ 2 + 2 / (n : ℝ) ^ 4 +
          Real.rpow (n : ℝ) (-(207 / 100 : ℝ))) := by
  have hsparse :
      law init
          (lateSamplingSeedProducerFailure init \
            safeSparseEntry init) ≤
        ENNReal.ofReal (2 / (n : ℝ) ^ 2) := by
    have hsub :
        lateSamplingSeedProducerFailure init \
            safeSparseEntry init ⊆
          smallHistory init \ safeSparseEntry init := by
      rintro ω ⟨hfailure, hsafe⟩
      exact
        ⟨lateSamplingSeedProducerFailure_subset_smallHistory
            init hfailure,
          hsafe⟩
    exact (measure_mono hsub).trans
      (smallHistory_sparse_entry_exception init hinput)
  have hsafe :=
    late_sampling_seed_receipt_safe_estimate init
      protectedTestFailure nearTestFailure oldIndexFailure
      hcover hprotected hnear hold
  have hsplit :
      lateSamplingSeedProducerFailure init ⊆
        (lateSamplingSeedProducerFailure init \
          safeSparseEntry init) ∪
        lateSamplingSeedProducerSafeFailure init := by
    intro ω hfailure
    by_cases hseed : ω ∈ safeSparseEntry init
    · apply Or.inr
      rw [lateSamplingSeedProducerSafeFailure_eq init]
      exact ⟨hfailure, hseed⟩
    · exact Or.inl ⟨hfailure, hseed⟩
  have ha : 0 ≤ 2 / (n : ℝ) ^ 2 := by positivity
  have hb :
      0 ≤ 2 / (n : ℝ) ^ 4 +
        Real.rpow (n : ℝ) (-(207 / 100 : ℝ)) :=
    add_nonneg (by positivity) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  change law init (lateSamplingSeedProducerFailure init) ≤ _
  calc
    law init (lateSamplingSeedProducerFailure init) ≤
        law init
          ((lateSamplingSeedProducerFailure init \
              safeSparseEntry init) ∪
            lateSamplingSeedProducerSafeFailure init) :=
      measure_mono hsplit
    _ ≤ law init
          (lateSamplingSeedProducerFailure init \
            safeSparseEntry init) +
        law init (lateSamplingSeedProducerSafeFailure init) :=
      measure_union_le _ _
    _ ≤ ENNReal.ofReal (2 / (n : ℝ) ^ 2) +
        ENNReal.ofReal
          (2 / (n : ℝ) ^ 4 +
            Real.rpow (n : ℝ) (-(207 / 100 : ℝ))) :=
      add_le_add hsparse hsafe
    _ = ENNReal.ofReal
        (2 / (n : ℝ) ^ 2 +
          (2 / (n : ℝ) ^ 4 +
            Real.rpow (n : ℝ) (-(207 / 100 : ℝ)))) :=
      (ENNReal.ofReal_add ha hb).symm
    _ = ENNReal.ofReal
        (2 / (n : ℝ) ^ 2 + 2 / (n : ℝ) ^ 4 +
          Real.rpow (n : ℝ) (-(207 / 100 : ℝ))) := by
      congr 1
      ring

end Ripple.PopulationProtocol.ExactMajority.LateStrengthening

end
