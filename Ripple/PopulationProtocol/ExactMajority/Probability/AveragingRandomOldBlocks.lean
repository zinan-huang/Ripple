-- Ripple/PopulationProtocol/ExactMajority/Probability/AveragingRandomOldBlocks.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingFrozenWork
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingOldBlocks

/-!
# Old-index extinction between two genuinely observed random times

The work blocks and the endpoint are pair-log stopping times. The compensated
potential is frozen at the endpoint before Markov's inequality is used.
The earlier start is then spliced over disjoint recorded-prefix fibres.

The actual clock's hour-start/checkpoint definitions and their agreement with
ClockHistory witnesses remain separate deterministic obligations.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal

namespace Ripple.PopulationProtocol.ExactMajority.AveragingRandomOldBlocks

open TimeTheorem PairLog PhaseOneDrain AveragingIntegerPotential
open AveragingWorkCounter AveragingObservedBlocks AveragingFrozenWork
open AveragingOldBlocks AveragingNumerics

variable {L B : ℕ}

def endpointBlocksFailure (init : Cfg L 256) (s h : ℕ) (ρ : ℝ≥0∞)
    (A : Set ((i : Finset.Iic s) → Draw L 256)) (Ψ N : ℕ)
    (σ : Fin B → Ω L 256 → WithTop ℕ) (τ : Ω L 256 → WithTop ℕ) :
    Set (Ω L 256) :=
  {ω | ∃ u : ℕ, τ ω = ((s + u : ℕ) : WithTop ℕ) ∧
    WorkLive init s h ρ A Ψ (blockWork s N σ) u ω ∧
    BlocksComplete s N σ u ω ∧ 1 ≤ augmentedPhiNat h (trace init ω (s + u))}

theorem random_endpoint_blocks_tail (init : Cfg L 256) (s h : ℕ)
    (hh : 1 ≤ h) (ρ : ℝ≥0∞) (hρ : ρ < 1)
    (A : Set ((i : Finset.Iic s) → Draw L 256)) (Ψ N : ℕ)
    (σ : Fin B → Ω L 256 → WithTop ℕ) (hσ : ∀ j, PairLogPastTime (σ j))
    (τ : Ω L 256 → WithTop ℕ) (hτ : PairLogPastTime τ) :
    law init (endpointBlocksFailure init s h ρ A Ψ N σ τ) ≤
      (1 - ρ) ^ (B * N) * Ψ *
        law init {ω | frestrictLe (π := fun _ : ℕ => Draw L 256) s ω ∈ A} := by
  refine (measure_mono ?_).trans
    (random_endpoint_work_tail init s h hh ρ hρ A Ψ (blockWork s N σ)
      (measurable_blockWork s N σ hσ) τ hτ (B * N))
  rintro ω ⟨u, htime, hlive, hcomplete, hpositive⟩
  exact ⟨u, htime, hlive, blocks_complete_work_count s N σ u ω hcomplete, hpositive⟩

def randomBlocksFailure (init : Cfg L 256)
    (start finish : Ω L 256 → WithTop ℕ) (h : ℕ) (ρ : ℝ≥0∞) (Ψ N : ℕ)
    (σ : Fin B → Ω L 256 → WithTop ℕ) : Set (Ω L 256) :=
  {ω | ∃ s u : ℕ, start ω = (s : WithTop ℕ) ∧
    finish ω = ((s + u : ℕ) : WithTop ℕ) ∧
    WorkLive init s h ρ Set.univ Ψ (blockWork s N σ) u ω ∧
    BlocksComplete s N σ u ω ∧ 1 ≤ augmentedPhiNat h (trace init ω (s + u))}

/-- Both the earlier checkpoint and the current endpoint are random observed
times. There is no multiplicity factor for either set of possible times. -/
theorem random_blocks_tail (init : Cfg L 256)
    (start finish : Ω L 256 → WithTop ℕ)
    (hstart : PairLogPastTime start) (hfinish : PairLogPastTime finish)
    (h : ℕ) (hh : 1 ≤ h) (ρ : ℝ≥0∞) (hρ : ρ < 1) (Ψ N : ℕ)
    (σ : Fin B → Ω L 256 → WithTop ℕ) (hσ : ∀ j, PairLogPastTime (σ j)) :
    law init (randomBlocksFailure init start finish h ρ Ψ N σ) ≤
      (1 - ρ) ^ (B * N) * Ψ := by
  refine PhaseThreeClockProducer.splice_of_local (law init) start
    (randomBlocksFailure init start finish h ρ Ψ N σ)
    ((1 - ρ) ^ (B * N) * Ψ)
    (fun s => (pairLogFiltration L 256).le s _ (hstart s)) ?_ ?_
  · rintro ω ⟨s, u, hs, _⟩
    rw [hs]
    exact WithTop.coe_ne_top
  · intro s
    have hs := hstart s
    rw [pairLogFiltration_eq_comap] at hs
    obtain ⟨A, -, hA⟩ := hs
    have hmem (ω : Ω L 256) :
        frestrictLe (π := fun _ : ℕ => Draw L 256) s ω ∈ A ↔
          start ω = (s : WithTop ℕ) := by
      change ω ∈ frestrictLe (π := fun _ : ℕ => Draw L 256) s ⁻¹' A ↔
        ω ∈ {ω | start ω = (s : WithTop ℕ)}
      rw [hA]
    calc
      law init (randomBlocksFailure init start finish h ρ Ψ N σ ∩
          {ω | start ω = (s : WithTop ℕ)}) ≤
          law init (endpointBlocksFailure init s h ρ A Ψ N σ finish) := by
            apply measure_mono
            rintro ω ⟨⟨r, u, hr, hf, hlive, hcomplete, hpositive⟩, hs⟩
            have hrs : r = s := WithTop.coe_injective (hr.symm.trans hs)
            subst r
            refine ⟨u, hf, ?_, hcomplete, hpositive⟩
            exact ⟨(hmem ω).mpr hs, hlive.2⟩
      _ ≤ ((1 - ρ) ^ (B * N) * Ψ) *
          law init {ω | frestrictLe (π := fun _ : ℕ => Draw L 256) s ω ∈ A} :=
        random_endpoint_blocks_tail init s h hh ρ hρ A Ψ N σ hσ finish hfinish
      _ = ((1 - ρ) ^ (B * N) * Ψ) *
          law init {ω | start ω = (s : WithTop ℕ)} := by
        rw [show {ω | frestrictLe (π := fun _ : ℕ => Draw L 256) s ω ∈ A} =
          {ω | start ω = (s : WithTop ℕ)} from Set.ext hmem]

theorem old_blocks_tail_at_random_endpoint
    (n M : ℕ) (hn : timePopulationThreshold ≤ n) (hMpos : 0 < M) (hMle : M ≤ n)
    (init : Cfg L 256) (s h : ℕ) (hh : 1 ≤ h)
    (A : Set ((i : Finset.Iic s) → Draw L 256)) (Ψ : ℕ)
    (hΨ : (Ψ : ℝ) ≤ (1 / 1000 : ℝ) * n)
    (σ : Fin (oldCutoff n - 6) → Ω L 256 → WithTop ℕ)
    (hσ : ∀ j, PairLogPastTime (σ j))
    (τ : Ω L 256 → WithTop ℕ) (hτ : PairLogPastTime τ) :
    law init (endpointBlocksFailure init s h
        (ENNReal.ofReal (oldWorkRate n M)) A Ψ (oldWorkTrials n M) σ τ) ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 20) *
        law init {ω | frestrictLe (π := fun _ : ℕ => Draw L 256) s ω ∈ A} := by
  have hnp : 0 < n := by exact_mod_cast (population_log_lower hn).1
  refine (random_endpoint_blocks_tail init s h hh
    (ENNReal.ofReal (oldWorkRate n M))
    (ENNReal.ofReal_lt_one.mpr (oldWorkRate_lt_one n M (by omega) hMle))
    A Ψ (oldWorkTrials n M) σ hσ τ hτ).trans ?_
  exact mul_le_mul_right' (old_blocks_constant n M Ψ hn hMpos hMle hΨ) _

/-- The calibrated old-index tail with random earlier checkpoint, random
work-block starts, and random current warmup endpoint. -/
theorem old_blocks_tail_between_pastTimes
    (n M : ℕ) (hn : timePopulationThreshold ≤ n) (hMpos : 0 < M) (hMle : M ≤ n)
    (init : Cfg L 256) (start finish : Ω L 256 → WithTop ℕ)
    (hstart : PairLogPastTime start) (hfinish : PairLogPastTime finish)
    (h : ℕ) (hh : 1 ≤ h) (Ψ : ℕ)
    (hΨ : (Ψ : ℝ) ≤ (1 / 1000 : ℝ) * n)
    (σ : Fin (oldCutoff n - 6) → Ω L 256 → WithTop ℕ)
    (hσ : ∀ j, PairLogPastTime (σ j)) :
    law init (randomBlocksFailure init start finish h
        (ENNReal.ofReal (oldWorkRate n M)) Ψ (oldWorkTrials n M) σ) ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 20) := by
  have hnp : 0 < n := by exact_mod_cast (population_log_lower hn).1
  exact (random_blocks_tail init start finish hstart hfinish h hh
    (ENNReal.ofReal (oldWorkRate n M))
    (ENNReal.ofReal_lt_one.mpr (oldWorkRate_lt_one n M (by omega) hMle))
    Ψ (oldWorkTrials n M) σ hσ).trans
      (old_blocks_constant n M Ψ hn hMpos hMle hΨ)

end Ripple.PopulationProtocol.ExactMajority.AveragingRandomOldBlocks

end
