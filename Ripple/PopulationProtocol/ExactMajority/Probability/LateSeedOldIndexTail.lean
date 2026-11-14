-- Ripple/PopulationProtocol/ExactMajority/Probability/LateSeedOldIndexTail.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.LateSeedReadout
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingCanonicalBlocks

/-!
# The sharper terminal old-index tail

The cutoff is floor(log n / 25), as proposed in N16.  The existing observed
block argument applies to this shorter collection of q-6 blocks and gives
n^(-207/100).  All estimates below are under the original law, and every
random start, work-block start, and endpoint is a pair-log past time.

The WorkLive predicate remains inside the failure event.  Producing that
gate and its earlier potential cap from the successful averaging induction
is a separate obligation; these statements do not condition on a future
ClockHistory, and they do not assert that bare SmallReadout supplies a gate.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal

namespace Ripple.PopulationProtocol.ExactMajority.LateStrengthening

open TimeTheorem PairLog PhaseOneDrain StageEventSpec PhaseThreeClockProducer
open AveragingNumerics AveragingOldBlocks AveragingWorkCounter AveragingObservedBlocks
open AveragingRandomOldBlocks AveragingCanonicalBlocks AveragingSeededDelay
open AveragingTerminalDebtDeadlines

variable {L n : ℕ}

/-- The public population calibration makes the terminal collection of
early-hour work blocks nonempty. -/
theorem terminalCutoff_ge_seven (hn : timePopulationThreshold ≤ n) :
    7 ≤ terminalCutoff n := by
  have hlog := (population_log_lower hn).2
  have hfloor := Nat.lt_floor_add_one (Real.log (n : ℝ) / 25)
  have hr : (7 : ℝ) ≤ (terminalCutoff n : ℝ) := by
    dsimp [terminalCutoff]
    linarith only [hfloor, hlog]
  exact_mod_cast hr

/-- This is the paper's floor-loss estimate with the constant 539 absorbed
using the already compiled lower bound log n >= 500000000. -/
theorem terminal_blocks_real_exponent (hn : timePopulationThreshold ≤ n) :
    (1 / 1000 : ℝ) * n *
        Real.exp (-77 * ((terminalCutoff n : ℝ) - 6)) ≤
      Real.rpow (n : ℝ) (-(207 / 100 : ℝ)) := by
  obtain ⟨hnpos, hlog⟩ := population_log_lower hn
  have hfloor :
      Real.log (n : ℝ) / 25 - 1 < (terminalCutoff n : ℝ) := by
    have h := Nat.lt_floor_add_one (Real.log (n : ℝ) / 25)
    dsimp [terminalCutoff]
    linarith only [h]
  have hexp :
      Real.log (n : ℝ) - 77 * ((terminalCutoff n : ℝ) - 6) ≤
        Real.log (n : ℝ) * (-(207 / 100 : ℝ)) := by
    linarith only [hfloor, hlog]
  calc
    (1 / 1000 : ℝ) * n *
        Real.exp (-77 * ((terminalCutoff n : ℝ) - 6)) ≤
        (n : ℝ) * Real.exp (-77 * ((terminalCutoff n : ℝ) - 6)) := by
      have hnonneg :
          0 ≤ (n : ℝ) * Real.exp (-77 * ((terminalCutoff n : ℝ) - 6)) :=
        mul_nonneg hnpos.le (Real.exp_nonneg _)
      nlinarith only [hnonneg]
    _ = Real.exp
        (Real.log (n : ℝ) - 77 * ((terminalCutoff n : ℝ) - 6)) := by
      rw [Real.exp_sub, Real.exp_log hnpos, div_eq_mul_inv, ← Real.exp_neg,
        neg_mul]
    _ ≤ Real.exp (Real.log (n : ℝ) * (-(207 / 100 : ℝ))) :=
      Real.exp_le_exp.mpr hexp
    _ = Real.rpow (n : ℝ) (-(207 / 100 : ℝ)) :=
      (rpow_def' hnpos _).symm

theorem terminal_blocks_natural_exponent (hn : timePopulationThreshold ≤ n) :
    (1 / 1000 : ℝ) * n *
        Real.exp (-77 * ((terminalCutoff n - 6 : ℕ) : ℝ)) ≤
      Real.rpow (n : ℝ) (-(207 / 100 : ℝ)) := by
  have hq : 6 ≤ terminalCutoff n := (by omega : 6 ≤ 7).trans
    (terminalCutoff_ge_seven hn)
  simpa only [Nat.cast_sub hq, Nat.cast_ofNat] using
    terminal_blocks_real_exponent hn

/-- Scalar conversion of the existing compensated-work bound at the new
terminal cutoff. -/
theorem terminal_blocks_constant (n M Ψ : ℕ)
    (hn : timePopulationThreshold ≤ n) (hMpos : 0 < M) (hMle : M ≤ n)
    (hΨ : (Ψ : ℝ) ≤ (1 / 1000 : ℝ) * n) :
    (1 - ENNReal.ofReal (oldWorkRate n M)) ^
        ((terminalCutoff n - 6) * oldWorkTrials n M) * Ψ ≤
      ENNReal.ofReal (Real.rpow (n : ℝ) (-(207 / 100 : ℝ))) := by
  have hnpos : 0 < n := by exact_mod_cast (population_log_lower hn).1
  have hgeom := geometric_blocks_le_exp (oldWorkRate n M)
    (oldWorkRate_nonneg n M) (oldWorkRate_lt_one n M (by omega) hMle)
    (terminalCutoff n - 6) (oldWorkTrials n M)
    (oldWorkRate_trials n M hnpos hMpos)
  have hmass :
      (Ψ : ℝ) * Real.exp (-77 * ((terminalCutoff n - 6 : ℕ) : ℝ)) ≤
        Real.rpow (n : ℝ) (-(207 / 100 : ℝ)) :=
    (mul_le_mul_of_nonneg_right hΨ (Real.exp_pos _).le).trans
      (terminal_blocks_natural_exponent hn)
  calc
    _ ≤ ENNReal.ofReal
        (Real.exp (-77 * ((terminalCutoff n - 6 : ℕ) : ℝ))) * Ψ :=
      mul_le_mul_right' hgeom _
    _ = ENNReal.ofReal
        ((Ψ : ℝ) * Real.exp (-77 * ((terminalCutoff n - 6 : ℕ) : ℝ))) := by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg Ψ), ENNReal.ofReal_natCast]
      ring
    _ ≤ _ := ENNReal.ofReal_le_ofReal hmass

/-- Prefix-local form.  The prefix event A retains its probability factor,
so disjoint genuine-prefix fibres can later be summed without a factor
counting possible seed times. -/
theorem terminal_old_blocks_at_random_endpoint
    (n M : ℕ) (hn : timePopulationThreshold ≤ n) (hMpos : 0 < M) (hMle : M ≤ n)
    (init : Cfg L 256) (s h : ℕ) (hh : 1 ≤ h)
    (A : Set ((i : Finset.Iic s) → Draw L 256)) (Ψ : ℕ)
    (hΨ : (Ψ : ℝ) ≤ (1 / 1000 : ℝ) * n)
    (σ : Fin (terminalCutoff n - 6) → Ω L 256 → WithTop ℕ)
    (hσ : ∀ j, PairLogPastTime (σ j))
    (τ : Ω L 256 → WithTop ℕ) (hτ : PairLogPastTime τ) :
    law init (endpointBlocksFailure init s h
        (ENNReal.ofReal (oldWorkRate n M)) A Ψ (oldWorkTrials n M) σ τ) ≤
      ENNReal.ofReal (Real.rpow (n : ℝ) (-(207 / 100 : ℝ))) *
        law init {ω | frestrictLe (π := fun _ : ℕ => Draw L 256) s ω ∈ A} := by
  have hnp : 0 < n := by exact_mod_cast (population_log_lower hn).1
  refine (random_endpoint_blocks_tail init s h hh
    (ENNReal.ofReal (oldWorkRate n M))
    (ENNReal.ofReal_lt_one.mpr (oldWorkRate_lt_one n M (by omega) hMle))
    A Ψ (oldWorkTrials n M) σ hσ τ hτ).trans ?_
  exact mul_le_mul_right' (terminal_blocks_constant n M Ψ hn hMpos hMle hΨ) _

/-- The local cutoff tail between two genuine pair-log past times.
The live-gate and completed-work assertions are intersections in the event. -/
theorem terminal_old_blocks_between_pastTimes
    (n M : ℕ) (hn : timePopulationThreshold ≤ n) (hMpos : 0 < M) (hMle : M ≤ n)
    (init : Cfg L 256) (start finish : Ω L 256 → WithTop ℕ)
    (hstart : PairLogPastTime start) (hfinish : PairLogPastTime finish)
    (h : ℕ) (hh : 1 ≤ h) (Ψ : ℕ)
    (hΨ : (Ψ : ℝ) ≤ (1 / 1000 : ℝ) * n)
    (σ : Fin (terminalCutoff n - 6) → Ω L 256 → WithTop ℕ)
    (hσ : ∀ j, PairLogPastTime (σ j)) :
    law init (randomBlocksFailure init start finish h
        (ENNReal.ofReal (oldWorkRate n M)) Ψ (oldWorkTrials n M) σ) ≤
      ENNReal.ofReal (Real.rpow (n : ℝ) (-(207 / 100 : ℝ))) := by
  have hnp : 0 < n := by exact_mod_cast (population_log_lower hn).1
  exact (random_blocks_tail init start finish hstart hfinish h hh
    (ENNReal.ofReal (oldWorkRate n M))
    (ENNReal.ofReal_lt_one.mpr (oldWorkRate_lt_one n M (by omega) hMle))
    Ψ (oldWorkTrials n M) σ hσ).trans
      (terminal_blocks_constant n M Ψ hn hMpos hMle hΨ)

/-- Parameters may be selected from the entire observed prefix.  The
singleton-prefix events are disjoint, so the sharp coefficient is charged
once, retaining the mass of A.  In particular there is no multiplicity
factor for the possible values of the Main count or terminal scale.

The caller supplies only past-time facts and scalar calibration premises;
the current drift gate and initial potential cap remain inside each
endpointBlocksFailure event. -/
theorem terminal_old_blocks_at_prefix_choice
    (n : ℕ) (hn : timePopulationThreshold ≤ n) (init : Cfg L 256) (s : ℕ)
    (A : Set ((i : Finset.Iic s) → Draw L 256))
    (M h Ψ : ((i : Finset.Iic s) → Draw L 256) → ℕ)
    (hMpos : ∀ p ∈ A, 0 < M p) (hMle : ∀ p ∈ A, M p ≤ n)
    (hh : ∀ p ∈ A, 1 ≤ h p)
    (hΨ : ∀ p ∈ A, (Ψ p : ℝ) ≤ (1 / 1000 : ℝ) * n)
    (σ : ((i : Finset.Iic s) → Draw L 256) →
      Fin (terminalCutoff n - 6) → Ω L 256 → WithTop ℕ)
    (hσ : ∀ p ∈ A, ∀ j, PairLogPastTime (σ p j))
    (τ : ((i : Finset.Iic s) → Draw L 256) → Ω L 256 → WithTop ℕ)
    (hτ : ∀ p ∈ A, PairLogPastTime (τ p)) :
    law init (⋃ p : A, endpointBlocksFailure init s (h p.1)
        (ENNReal.ofReal (oldWorkRate n (M p.1))) {p.1} (Ψ p.1)
        (oldWorkTrials n (M p.1)) (σ p.1) (τ p.1)) ≤
      ENNReal.ofReal (Real.rpow (n : ℝ) (-(207 / 100 : ℝ))) *
        law init {ω | frestrictLe (π := fun _ : ℕ => Draw L 256) s ω ∈ A} := by
  classical
  let ε := ENNReal.ofReal (Real.rpow (n : ℝ) (-(207 / 100 : ℝ)))
  let P : A → Set (Ω L 256) := fun p =>
    {ω | frestrictLe (π := fun _ : ℕ => Draw L 256) s ω = p.1}
  let E : A → Set (Ω L 256) := fun p =>
    endpointBlocksFailure init s (h p.1)
      (ENNReal.ofReal (oldWorkRate n (M p.1))) {p.1} (Ψ p.1)
      (oldWorkTrials n (M p.1)) (σ p.1) (τ p.1)
  have hlocal (p : A) : law init (E p) ≤ ε * law init (P p) := by
    simpa only [E, P, ε, Set.mem_singleton_iff] using
      terminal_old_blocks_at_random_endpoint n (M p.1) hn
        (hMpos p.1 p.2) (hMle p.1 p.2) init s (h p.1) (hh p.1 p.2)
        {p.1} (Ψ p.1) (hΨ p.1 p.2) (σ p.1) (hσ p.1 p.2)
        (τ p.1) (hτ p.1 p.2)
  have hmeas (p : A) : MeasurableSet (P p) := by
    exact ((Set.to_countable ({p.1} :
      Set ((i : Finset.Iic s) → Draw L 256))).measurableSet).preimage
        (measurable_frestrictLe (X := fun _ : ℕ => Draw L 256) s)
  have hdisj : Pairwise (fun p q : A => Disjoint (P p) (P q)) := by
    intro p q hpq
    apply Set.disjoint_left.mpr
    intro ω hp hq
    apply hpq
    exact Subtype.ext (hp.symm.trans hq)
  have hunion :
      (⋃ p : A, P p) =
        {ω | frestrictLe (π := fun _ : ℕ => Draw L 256) s ω ∈ A} := by
    ext ω
    constructor
    · intro hω
      obtain ⟨p, hp⟩ := Set.mem_iUnion.mp hω
      change frestrictLe (π := fun _ : ℕ => Draw L 256) s ω = p.1 at hp
      change frestrictLe (π := fun _ : ℕ => Draw L 256) s ω ∈ A
      rw [hp]
      exact p.2
    · intro hω
      refine Set.mem_iUnion.mpr ⟨⟨_, hω⟩, ?_⟩
      rfl
  have hmass :
      (∑' p : A, law init (P p)) =
        law init {ω | frestrictLe (π := fun _ : ℕ => Draw L 256) s ω ∈ A} := by
    rw [← measure_iUnion hdisj hmeas, hunion]
  change law init (⋃ p : A, E p) ≤ ε * _
  calc
    law init (⋃ p : A, E p) ≤ ∑' p : A, law init (E p) :=
      measure_iUnion_le E
    _ ≤ ∑' p : A, ε * law init (P p) :=
      ENNReal.tsum_le_tsum hlocal
    _ = ε * ∑' p : A, law init (P p) := by rw [ENNReal.tsum_mul_left]
    _ = _ := by rw [hmass]

/-- The shorter terminal collection has the same actual hour-window
alignment as the earlier N13 collection. -/
theorem canonical_terminal_old_blocks_complete
    {init : InputCfg n} {ω : InputLog n}
    {S T ρ : ℕ} {w : ClockTimes init} (H : ClockHistory init ω S T ρ w)
    (hn : timePopulationThreshold ≤ n) (seed : InputLog n → WithTop ℕ)
    (hseed : seed ω = (S : WithTop ℕ)) (r : ℕ)
    (hrq : r + terminalCutoff n ≤ PhaseThreeModel.Numeric.hourIndex n) :
    let C := clockCount (trace init ω S)
    let M := timeMainCount (trace init ω S)
    let P := w.start r + clockWarmup n C + potentialTrials n M
    let W := w.start (r + terminalCutoff n) + clockWarmup n C
    BlocksComplete P (oldWorkTrials n M)
      (oldBlockStarts init seed r (terminalCutoff n)) (W - P) ω := by
  have hnp : 0 < n := by exact_mod_cast (population_log_lower hn).1
  exact canonical_old_blocks_complete H hnp seed hseed r (terminalCutoff n)
    (terminalCutoff_ge_seven hn) hrq

/-- Canonical actual clock stopping times, with fixed local Main count and
potential cap.  Producing WorkLive from prior successful hours is not a
premise of this probability inequality: WorkLive remains in its event. -/
theorem canonical_terminal_old_blocks_tail (init : InputCfg n)
    (seed : InputLog n → WithTop ℕ) (hseed : PairLogPastTime seed)
    (r : ℕ) (hr : 1 ≤ r) (M Ψ : ℕ)
    (hn : timePopulationThreshold ≤ n) (hMpos : 0 < M) (hMle : M ≤ n)
    (hΨ : (Ψ : ℝ) ≤ (1 / 1000 : ℝ) * n) :
    law init (randomBlocksFailure init
        (hourPotentialEnd init seed r)
        (hourWarmStart init seed (r + terminalCutoff n)) r
        (ENNReal.ofReal (oldWorkRate n M)) Ψ (oldWorkTrials n M)
        (oldBlockStarts init seed r (terminalCutoff n))) ≤
      ENNReal.ofReal (Real.rpow (n : ℝ) (-(207 / 100 : ℝ))) :=
  terminal_old_blocks_between_pastTimes n M hn hMpos hMle init
    (hourPotentialEnd init seed r) (hourWarmStart init seed (r + terminalCutoff n))
    (hourPotentialEnd_pastTime init seed hseed r)
    (hourWarmStart_pastTime init seed hseed (r + terminalCutoff n))
    r hr Ψ hΨ (oldBlockStarts init seed r (terminalCutoff n))
    (fun j => oldBlockStarts_pastTime init seed hseed r (terminalCutoff n) j)

/-- In particular the seed is the actual first threshold-3 hitting time. -/
theorem canonical_terminal_old_blocks_phaseThreeSeed_tail (init : InputCfg n)
    (r : ℕ) (hr : 1 ≤ r) (M Ψ : ℕ)
    (hn : timePopulationThreshold ≤ n) (hMpos : 0 < M) (hMle : M ≤ n)
    (hΨ : (Ψ : ℝ) ≤ (1 / 1000 : ℝ) * n) :
    law init (randomBlocksFailure init
        (hourPotentialEnd init (seedTime init 3) r)
        (hourWarmStart init (seedTime init 3) (r + terminalCutoff n)) r
        (ENNReal.ofReal (oldWorkRate n M)) Ψ (oldWorkTrials n M)
        (oldBlockStarts init (seedTime init 3) r (terminalCutoff n))) ≤
      ENNReal.ofReal (Real.rpow (n : ℝ) (-(207 / 100 : ℝ))) :=
  canonical_terminal_old_blocks_tail init (seedTime init 3) (seedTime_pastTime init 3)
    r hr M Ψ hn hMpos hMle hΨ

end Ripple.PopulationProtocol.ExactMajority.LateStrengthening

end
