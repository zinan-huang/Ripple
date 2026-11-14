-- Ripple/PopulationProtocol/ExactMajority/Probability/AveragingObservedBlocks.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingWorkCounter
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeAveragingStops
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Ordered random work blocks on the actual trace

The raw-time work bit is constructed from a finite family of pair-log stopping
times. Completion and ordering are joint-event conditions, never a change of
probability law. The cardinality argument counts all N interactions in each
of B disjoint blocks; the work-counter potential then supplies B*N
multiplicative contractions.

Instantiating these stopping times with the clock's hour work starts and
proving their completion before the current warmup is not asserted here.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.AveragingObservedBlocks

open TimeTheorem PairLog PhaseOneDrain AveragingIntegerPotential AveragingWorkCounter

variable {L B : ℕ}

open Classical in
def blockWork (s N : ℕ) (σ : Fin B → Ω L 256 → WithTop ℕ)
    (t : ℕ) (ω : Ω L 256) : Bool :=
  if ∃ j : Fin B, ∃ r : ℕ, σ j ω = (r : WithTop ℕ) ∧
      s ≤ r ∧ r ≤ s + t ∧ s + t < r + N
  then true else false

theorem blockWork_eq_true (s N : ℕ) (σ : Fin B → Ω L 256 → WithTop ℕ)
    (t : ℕ) (ω : Ω L 256) :
    blockWork s N σ t ω = true ↔
      ∃ j : Fin B, ∃ r : ℕ, σ j ω = (r : WithTop ℕ) ∧
        s ≤ r ∧ r ≤ s + t ∧ s + t < r + N := by
  classical
  by_cases he : ∃ j : Fin B, ∃ r : ℕ, σ j ω = (r : WithTop ℕ) ∧
      s ≤ r ∧ r ≤ s + t ∧ s + t < r + N
  · simp only [blockWork, if_pos he, true_iff]
    exact he
  · simp only [blockWork, if_neg he, Bool.false_eq_true, false_iff]
    exact he

theorem measurable_blockWork (s N : ℕ) (σ : Fin B → Ω L 256 → WithTop ℕ)
    (hσ : ∀ j, PairLogPastTime (σ j)) (t : ℕ) :
    Measurable[pairLogFiltration L 256 (s + t)] (blockWork s N σ t) := by
  classical
  have hevent : MeasurableSet[pairLogFiltration L 256 (s + t)]
      {ω | ∃ j : Fin B, ∃ r : ℕ, σ j ω = (r : WithTop ℕ) ∧
        s ≤ r ∧ r ≤ s + t ∧ s + t < r + N} := by
    simp only [Set.setOf_exists]
    refine MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun r => ?_
    by_cases hr : s ≤ r ∧ r ≤ s + t ∧ s + t < r + N
    · have hf := (pairLogFiltration L 256).mono hr.2.1 _ (hσ j r)
      simpa only [hr.1, hr.2.1, hr.2.2, and_true] using hf
    · have hempty :
          {ω | σ j ω = (r : WithTop ℕ) ∧
            s ≤ r ∧ r ≤ s + t ∧ s + t < r + N} = (∅ : Set (Ω L 256)) := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false]
        constructor
        · intro hω
          exact hr hω.2
        · intro hfalse
          exact False.elim hfalse
      rw [hempty]
      exact @MeasurableSet.empty _ (pairLogFiltration L 256 (s + t))
  exact Measurable.ite hevent measurable_const measurable_const

def BlocksComplete (s N : ℕ) (σ : Fin B → Ω L 256 → WithTop ℕ)
    (T : ℕ) (ω : Ω L 256) : Prop :=
  ∃ r : Fin B → ℕ,
    (∀ j, σ j ω = (r j : WithTop ℕ) ∧ s ≤ r j ∧ r j + N ≤ s + T) ∧
    (∀ i j, i < j → r i + N ≤ r j)

theorem workCount_eq_card_marked (work : ℕ → Ω L 256 → Bool)
    (T : ℕ) (ω : Ω L 256) :
    workCount work T ω = Fintype.card {u : Fin T // work u.val ω = true} := by
  classical
  rw [workCount, Finset.sum_range, Fintype.card_subtype]
  simp only [Finset.sum_boole, Nat.cast_id]

/-- Each completed ordered block contributes all N distinct raw interactions. -/
theorem blocks_complete_work_count (s N : ℕ)
    (σ : Fin B → Ω L 256 → WithTop ℕ) (T : ℕ) (ω : Ω L 256)
    (hcomplete : BlocksComplete s N σ T ω) :
    B * N ≤ workCount (blockWork s N σ) T ω := by
  classical
  obtain ⟨r, hr, horder⟩ := hcomplete
  let f : Fin B × Fin N → {u : Fin T // blockWork s N σ u.val ω = true} :=
    fun p =>
      ⟨⟨r p.1 - s + p.2.val, by
          have hs := (hr p.1).2.1
          have he := (hr p.1).2.2
          have hk := p.2.isLt
          omega⟩,
        (blockWork_eq_true s N σ _ ω).2
          ⟨p.1, r p.1, (hr p.1).1, (hr p.1).2.1,
            by
              have hs := (hr p.1).2.1
              show r p.1 ≤ s + (r p.1 - s + p.2.val)
              omega,
            by
              have hs := (hr p.1).2.1
              have hk := p.2.isLt
              show s + (r p.1 - s + p.2.val) < r p.1 + N
              omega⟩⟩
  have hf : Function.Injective f := by
    intro p q heq
    have hv : r p.1 - s + p.2.val = r q.1 - s + q.2.val :=
      congrArg (fun x : {u : Fin T // blockWork s N σ u.val ω = true} => x.val.val) heq
    have hj : p.1 = q.1 := by
      rcases lt_trichotomy p.1 q.1 with hlt | he | hgt
      · have hsep := horder p.1 q.1 hlt
        have hpstart := (hr p.1).2.1
        have hqstart := (hr q.1).2.1
        have hpN := p.2.isLt
        have hqN := q.2.isLt
        omega
      · exact he
      · have hsep := horder q.1 p.1 hgt
        have hpstart := (hr p.1).2.1
        have hqstart := (hr q.1).2.1
        have hpN := p.2.isLt
        have hqN := q.2.isLt
        omega
    apply Prod.ext hj
    apply Fin.ext
    have he : r p.1 = r q.1 := congrArg r hj
    omega
  have hc := Fintype.card_le_of_injective f hf
  rw [workCount_eq_card_marked]
  simpa only [Fintype.card_prod, Fintype.card_fin] using hc

/-- The actual fixed potential contracts across all completed random blocks.
The future block-completion event is intersected with the bad event under
the original law; it is never used as a conditional probability space. -/
theorem observed_blocks_extinction_tail (init : Cfg L 256) (s h : ℕ)
    (hh : 1 ≤ h) (ρ : ℝ≥0∞) (hρ : ρ < 1)
    (A : Set ((i : Finset.Iic s) → Draw L 256)) (Ψ N : ℕ)
    (σ : Fin B → Ω L 256 → WithTop ℕ) (hσ : ∀ j, PairLogPastTime (σ j))
    (T : ℕ) :
    law init {ω | WorkLive init s h ρ A Ψ (blockWork s N σ) T ω ∧
        BlocksComplete s N σ T ω ∧
        1 ≤ augmentedPhiNat h (trace init ω (s + T))} ≤
      (1 - ρ) ^ (B * N) * Ψ *
        law init {ω | frestrictLe (π := fun _ : ℕ => Draw L 256) s ω ∈ A} := by
  refine (measure_mono ?_).trans
    (work_count_extinction_tail init s h hh ρ hρ A Ψ (blockWork s N σ)
      (measurable_blockWork s N σ hσ) T (B * N))
  rintro ω ⟨hlive, hcomplete, hpositive⟩
  exact ⟨hlive, blocks_complete_work_count s N σ T ω hcomplete, hpositive⟩

end Ripple.PopulationProtocol.ExactMajority.AveragingObservedBlocks

end
