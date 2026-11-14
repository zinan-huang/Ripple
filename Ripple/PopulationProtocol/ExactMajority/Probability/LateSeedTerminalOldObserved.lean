-- Ripple/PopulationProtocol/ExactMajority/Probability/LateSeedTerminalOldObserved.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.LateSeedOldIndexTail
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingObservedHourTails
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingSparseEntry

/-!
# Observed terminal old-index tails

This is the terminal-cutoff analogue of the N13 observed old-block wrapper.
The prefix event is measurable at the fixed observed block start.  The random
Main count is then partitioned by `seedCounts_prefix_bound`, under the original
law and without conditioning on future clock success.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.LateStrengthening

open TimeTheorem PairLog PhaseOneDrain StageEventSpec
open AveragingSparseEntry AveragingNumerics AveragingOldBlocks
open AveragingRandomOldBlocks AveragingObservedHourTails

variable {L n : ℕ}

/-- The terminal old-block failure with the Main count read at the selected
safe seed.  The current `WorkLive` gate, completed-block certificate, and
positive terminal potential remain inside `endpointBlocksFailure`. -/
def observedTerminalOldFailure
    (init : InputCfg n) (S s r : ℕ)
    (σ : Fin (terminalCutoff n - 6) → InputLog n → WithTop ℕ)
    (finish : InputLog n → WithTop ℕ) : Set (InputLog n) :=
  {ω |
    let M := (seedCounts init S ω).2
    ω ∈ endpointBlocksFailure init s r
      (ENNReal.ofReal (oldWorkRate n M)) Set.univ
      (M / 1000) (oldWorkTrials n M) σ finish}

/-- Prefix-local terminal old-block estimate.  This is the exact analogue of
`AveragingObservedHourTails.old_prefix_tail`, but it uses the sharper terminal
cutoff theorem and therefore retains the `n^(-207/100)` coefficient. -/
theorem terminal_old_prefix_tail
    (n M : ℕ) (hn : timePopulationThreshold ≤ n)
    (hMpos : 0 < M) (hMle : M ≤ n)
    (init : Cfg L 256) (s h : ℕ) (hh : 1 ≤ h)
    (E : Set (Ω L 256))
    (hE : MeasurableSet[pairLogFiltration L 256 s] E)
    (Ψ : ℕ) (hΨ : (Ψ : ℝ) ≤ (1 / 1000 : ℝ) * n)
    (σ : Fin (terminalCutoff n - 6) → Ω L 256 → WithTop ℕ)
    (hσ : ∀ j, PairLogPastTime (σ j))
    (τ : Ω L 256 → WithTop ℕ) (hτ : PairLogPastTime τ) :
    law init
        (E ∩ endpointBlocksFailure init s h
          (ENNReal.ofReal (oldWorkRate n M)) Set.univ Ψ
          (oldWorkTrials n M) σ τ) ≤
      ENNReal.ofReal
          (Real.rpow (n : ℝ) (-(207 / 100 : ℝ))) *
        law init E := by
  rw [pairLogFiltration_eq_comap] at hE
  obtain ⟨A, _, hA⟩ := hE
  have hp :
      {ω | frestrictLe (π := fun _ : ℕ => Draw L 256) s ω ∈ A} = E :=
    hA
  have hsub :
      E ∩ endpointBlocksFailure init s h
          (ENNReal.ofReal (oldWorkRate n M)) Set.univ Ψ
          (oldWorkTrials n M) σ τ ⊆
        endpointBlocksFailure init s h
          (ENNReal.ofReal (oldWorkRate n M)) A Ψ
          (oldWorkTrials n M) σ τ := by
    rintro ω ⟨hω, u, ht, hlive, hcomplete, hpositive⟩
    refine ⟨u, ht, ?_, hcomplete, hpositive⟩
    refine ⟨?_, hlive.2⟩
    change ω ∈
      {ω | frestrictLe (π := fun _ : ℕ => Draw L 256) s ω ∈ A}
    rw [hp]
    exact hω
  have ht :=
    terminal_old_blocks_at_random_endpoint n M hn hMpos hMle
      init s h hh A Ψ hΨ σ hσ τ hτ
  exact (measure_mono hsub).trans (by simpa only [hp] using ht)

/-- The observed terminal old-block estimate.  The safe-seed prefix controls
both random seed counts, and `seedCounts_prefix_bound` sums their disjoint
fibres without a multiplicity factor. -/
theorem observed_terminal_old_prefix_tail
    (init : InputCfg n) (hn : timePopulationThreshold ≤ n)
    (S s : ℕ) (hSs : S ≤ s) (r : ℕ) (hr : 1 ≤ r)
    (σ : Fin (terminalCutoff n - 6) → InputLog n → WithTop ℕ)
    (hσ : ∀ j, PairLogPastTime (σ j))
    (finish : InputLog n → WithTop ℕ)
    (hfinish : PairLogPastTime finish)
    (E : Set (InputLog n))
    (hE : MeasurableSet[
      pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256 s] E)
    (hseed : ∀ ω ∈ E, SeedProfile n init (trace init ω S)) :
    law init (E ∩ observedTerminalOldFailure init S s r σ finish) ≤
      ENNReal.ofReal
          (Real.rpow (n : ℝ) (-(207 / 100 : ℝ))) *
        law init E := by
  have hnlarge := (time_population_bounds hn).2
  apply seedCounts_prefix_bound init S s hSs E hE (by omega) hseed
    (fun p =>
      endpointBlocksFailure init s r
        (ENNReal.ofReal (oldWorkRate n p.2)) Set.univ
        (p.2 / 1000) (oldWorkTrials n p.2) σ finish)
    (ENNReal.ofReal
      (Real.rpow (n : ℝ) (-(207 / 100 : ℝ))))
  intro p _ hmain hroles
  have hMpos : 0 < p.2 := by omega
  have hMle : p.2 ≤ n := by omega
  have hcapN : 1000 * (p.2 / 1000) ≤ n := by omega
  have hcapR :
      (1000 : ℝ) * ((p.2 / 1000 : ℕ) : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hcapN
  exact
    terminal_old_prefix_tail n p.2 hn hMpos hMle init s r hr
      (E ∩ {ω | seedCounts init S ω = p})
      (hE.inter (seedCounts_fibre_measurable init S s hSs p))
      (p.2 / 1000) (by linarith) σ hσ finish hfinish

end Ripple.PopulationProtocol.ExactMajority.LateStrengthening

end
